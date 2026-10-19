//! Namespace resolver — maps namespace imports (C# `using A.B;`) to files.
//!
//! A namespace import names no file: `A.B` may be declared in any number of
//! files, in any folder. Linking a file to every file of each namespace it
//! imports would invent dependencies (an unused `using` is common), so this
//! resolver links at type granularity instead:
//!
//!   1. Index every declared type and extension method by namespace.
//!   2. For each file, collect its visible namespaces: the namespaces it
//!      declares and their parents, the global namespace, its `using`
//!      directives, and the `global using` directives of its project.
//!   3. Each referenced name that matches a type (or extension method) in a
//!      visible namespace yields an edge to the declaring file(s).
//!
//! `using static T;` and `using Alias = T;` resolve to the file(s) declaring T.
//! Dotted references (`Domain.Order`) resolve absolutely or relative to the
//! file's namespaces. Names from outside the scan (System.*) match nothing.

use crate::core::types::{FileNode, ImportEdge, NamespaceInfo, NamespaceUsing};
use std::collections::{BTreeSet, HashMap, HashSet};

/// namespace -> member name -> declaring files.
type MemberIndex<'a> = HashMap<&'a str, HashMap<&'a str, Vec<&'a str>>>;

/// Project-wide lookup tables built once per scan.
struct NamespaceIndex<'a> {
    /// Types by namespace (nested types are keyed by their outer type).
    types: MemberIndex<'a>,
    /// Extension methods by namespace.
    ext: MemberIndex<'a>,
    /// Every declared namespace and all of its parents.
    namespaces: HashSet<String>,
    /// `global using` directives per project root.
    global_usings: HashMap<&'a str, Vec<&'a NamespaceUsing>>,
}

/// Split "A.B.C" into ("A.B", "C"); a bare name lives in the global namespace "".
fn split_last(fq: &str) -> (&str, &str) {
    fq.rsplit_once('.').unwrap_or(("", fq))
}

fn add_member<'a>(index: &mut MemberIndex<'a>, fq: &'a str, file: &'a str) {
    let (ns, name) = split_last(fq);
    let files = index.entry(ns).or_default().entry(name).or_default();
    if !files.contains(&file) {
        files.push(file);
    }
}

/// Insert `ns` and every parent namespace ("A.B.C" -> "A.B.C", "A.B", "A").
fn add_namespace_chain(set: &mut HashSet<String>, ns: &str) {
    let mut cur = ns;
    while !cur.is_empty() {
        if !set.insert(cur.to_string()) {
            break;
        }
        cur = cur.rsplit_once('.').map_or("", |(parent, _)| parent);
    }
}

fn ns_info(file: &FileNode) -> Option<&NamespaceInfo> {
    file.sa.as_ref().and_then(|sa| sa.ns.as_ref())
}

impl<'a> NamespaceIndex<'a> {
    fn build(files: &[&'a FileNode], project_map: &'a HashMap<String, String>) -> Self {
        let mut idx = NamespaceIndex {
            types: HashMap::new(),
            ext: HashMap::new(),
            namespaces: HashSet::new(),
            global_usings: HashMap::new(),
        };
        for &file in files {
            let Some(info) = ns_info(file) else { continue };
            let path = file.path.as_str();
            for fq in &info.types {
                add_member(&mut idx.types, fq, path);
            }
            for fq in &info.ext {
                add_member(&mut idx.ext, fq, path);
            }
            for ns in &info.decl {
                add_namespace_chain(&mut idx.namespaces, ns);
            }
            let project = project_map.get(&file.path).map_or("", |s| s.as_str());
            for u in info.usings.iter().filter(|u| u.is_global) {
                idx.global_usings.entry(project).or_default().push(u);
            }
        }
        idx
    }

    fn type_files(&self, fq: &str) -> Option<&Vec<&'a str>> {
        let (ns, name) = split_last(fq);
        self.types.get(ns).and_then(|m| m.get(name))
    }

    /// Files declaring `base.segs[0..k]` for the largest k >= 1 that matches.
    /// `Outer.Inner` falls back to `Outer`, `Type.Member` to `Type`. The
    /// lookup never strips into `base`, so a reference cannot match a type
    /// that merely shares its name with a namespace segment.
    fn longest_type(&self, base: &str, segs: &[&str]) -> Option<&Vec<&'a str>> {
        (1..=segs.len()).rev().find_map(|k| {
            let tail = segs[..k].join(".");
            let fq = if base.is_empty() { tail } else { format!("{base}.{tail}") };
            self.type_files(&fq)
        })
    }
}

/// Namespaces and aliases visible inside one file.
struct FileScope<'u> {
    /// Namespaces whose members are visible by simple name.
    open: Vec<String>,
    /// Namespaces enclosing the file's declarations ("" included); dotted
    /// references are also tried relative to these.
    enclosing: Vec<String>,
    /// `using Alias = Target;`
    aliases: HashMap<&'u str, &'u str>,
    /// `using static Type;` targets.
    statics: Vec<&'u str>,
}

fn file_scope<'u>(info: &'u NamespaceInfo, globals: &[&'u NamespaceUsing]) -> FileScope<'u> {
    let mut enclosing: BTreeSet<String> = BTreeSet::new();
    enclosing.insert(String::new());
    for ns in &info.decl {
        let mut cur = ns.as_str();
        while !cur.is_empty() {
            enclosing.insert(cur.to_string());
            cur = cur.rsplit_once('.').map_or("", |(parent, _)| parent);
        }
    }

    let mut open: BTreeSet<String> = enclosing.clone();
    let mut aliases = HashMap::new();
    let mut statics = Vec::new();
    for u in info.usings.iter().chain(globals.iter().copied()) {
        match (&u.alias, u.is_static) {
            (Some(alias), _) => {
                aliases.insert(alias.as_str(), u.target.as_str());
            }
            (None, true) => statics.push(u.target.as_str()),
            (None, false) => {
                open.insert(u.target.clone());
            }
        }
    }
    FileScope {
        open: open.into_iter().collect(),
        enclosing: enclosing.into_iter().collect(),
        aliases,
        statics,
    }
}

/// Resolve one file's references to the files it depends on.
fn resolve_file<'a>(info: &NamespaceInfo, scope: &FileScope<'_>, idx: &NamespaceIndex<'a>, out: &mut BTreeSet<&'a str>, attribute_suffix: &str) {
    let mut add = |files: Option<&Vec<&'a str>>| {
        if let Some(files) = files {
            out.extend(files.iter().copied());
        }
    };

    for target in &scope.statics {
        let segs: Vec<&str> = target.split('.').collect();
        add(idx.longest_type("", &segs));
    }

    for r in &info.refs {
        let (head, rest) = match r.split_once('.') {
            Some((h, t)) => (h, Some(t)),
            None => (r.as_str(), None),
        };

        // Alias: `Alias` or `Alias.Member` — substitute the target. The
        // target is either a type or a namespace, so `rest` is tried first.
        if let Some(target) = scope.aliases.get(head) {
            let rest_segs: Vec<&str> = rest.map(|r| r.split('.').collect()).unwrap_or_default();
            let found = idx.longest_type(target, &rest_segs).or_else(|| {
                let segs: Vec<&str> = target.split('.').collect();
                idx.longest_type("", &segs)
            });
            add(found);
            continue;
        }

        match rest {
            None => {
                for ns in &scope.open {
                    let types = idx.types.get(ns.as_str());
                    add(types.and_then(|m| m.get(r.as_str())));
                    if !attribute_suffix.is_empty() {
                        let attr = format!("{r}{attribute_suffix}");
                        add(types.and_then(|m| m.get(attr.as_str())));
                    }
                    add(idx.ext.get(ns.as_str()).and_then(|m| m.get(r.as_str())));
                }
            }
            Some(_) => {
                // Dotted: absolute, relative to an enclosing namespace, or
                // `Type.Member` with Type visible through an open namespace.
                let segs: Vec<&str> = r.split('.').collect();
                for base in scope.enclosing.iter().chain(scope.open.iter()) {
                    add(idx.longest_type(base, &segs));
                }
            }
        }
    }
}

/// Count how many using directives point into the scanned project.
fn using_resolves(u: &NamespaceUsing, idx: &NamespaceIndex<'_>) -> bool {
    if u.is_static || u.alias.is_some() {
        let segs: Vec<&str> = u.target.split('.').collect();
        idx.longest_type("", &segs).is_some() || idx.namespaces.contains(&u.target)
    } else {
        idx.namespaces.contains(&u.target)
    }
}

/// Resolve namespace imports for every file whose language enables them.
/// Returns file-to-file import edges (deduplicated per file, no self-edges).
pub(crate) fn resolve_namespace_imports(files: &[&FileNode], project_map: &HashMap<String, String>) -> Vec<ImportEdge> {
    let ns_files: Vec<&FileNode> = files.iter().copied().filter(|f| !f.is_dir && ns_info(f).is_some()).collect();
    if ns_files.is_empty() {
        return Vec::new();
    }
    let idx = NamespaceIndex::build(&ns_files, project_map);

    let mut edges = Vec::new();
    let (mut in_project, mut external) = (0usize, 0usize);
    for file in &ns_files {
        let Some(info) = ns_info(file) else { continue };
        let profile = crate::analysis::lang_registry::profile(&file.lang);
        let project = project_map.get(&file.path).map_or("", |s| s.as_str());
        let globals = idx.global_usings.get(project).map_or(&[][..], |v| v.as_slice());
        let scope = file_scope(info, globals);

        for u in &info.usings {
            if using_resolves(u, &idx) { in_project += 1 } else { external += 1 }
        }

        let mut targets = BTreeSet::new();
        resolve_file(info, &scope, &idx, &mut targets, &profile.semantics.namespaces.attribute_suffix);
        targets.remove(file.path.as_str());
        for t in &targets {
            crate::debug_log!("[resolve_namespaces] {} -> {}", file.path, t);
        }
        edges.extend(targets.into_iter().map(|t| ImportEdge {
            from_file: file.path.clone(),
            to_file: t.to_string(),
        }));
    }

    eprintln!(
        "[resolve_namespaces] {} files, {} namespaces, {} usings in project, {} external, {} edges",
        ns_files.len(), idx.namespaces.len(), in_project, external, edges.len()
    );
    edges
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analysis::test_helpers::make_file;
    use crate::core::types::StructuralAnalysis;

    /// A C# file with the given namespace facts.
    fn cs(path: &str, decl: &[&str], types: &[&str], usings: Vec<NamespaceUsing>, refs: &[&str]) -> FileNode {
        let strings = |xs: &[&str]| xs.iter().map(|s| s.to_string()).collect::<Vec<_>>();
        let ns = NamespaceInfo {
            decl: strings(decl),
            types: strings(types),
            ext: Vec::new(),
            usings,
            refs: strings(refs),
        };
        let sa = StructuralAnalysis {
            functions: None, cls: None, imp: None, co: None, tags: None, comment_lines: None, ns: Some(ns),
        };
        let name = path.rsplit('/').next().unwrap_or(path);
        make_file(name, path, "csharp", Some(sa))
    }

    fn using(target: &str) -> NamespaceUsing {
        NamespaceUsing { target: target.to_string(), ..Default::default() }
    }

    fn resolve(files: &[FileNode]) -> Vec<(String, String)> {
        resolve_with_projects(files, &HashMap::new())
    }

    fn resolve_with_projects(files: &[FileNode], project_map: &HashMap<String, String>) -> Vec<(String, String)> {
        let refs: Vec<&FileNode> = files.iter().collect();
        let mut edges: Vec<(String, String)> = resolve_namespace_imports(&refs, project_map)
            .into_iter()
            .map(|e| (e.from_file, e.to_file))
            .collect();
        edges.sort();
        edges
    }

    fn edge(from: &str, to: &str) -> (String, String) {
        (from.to_string(), to.to_string())
    }

    #[test]
    fn using_links_to_the_file_declaring_a_referenced_type() {
        let files = vec![
            cs("App/Handler.cs", &["Acme.App"], &["Acme.App.Handler"], vec![using("Acme.Domain")], &["Order"]),
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
            cs("Domain/Invoice.cs", &["Acme.Domain"], &["Acme.Domain.Invoice"], vec![], &[]),
        ];
        // Invoice shares the namespace but is not referenced: no edge.
        assert_eq!(resolve(&files), vec![edge("App/Handler.cs", "Domain/Order.cs")]);
    }

    #[test]
    fn unused_and_external_usings_produce_no_edges() {
        let files = vec![
            cs("App/Handler.cs", &["Acme.App"], &["Acme.App.Handler"], vec![using("Acme.Domain"), using("System")], &["Console"]),
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
        ];
        assert!(resolve(&files).is_empty());
    }

    #[test]
    fn enclosing_and_parent_namespaces_are_visible_without_using() {
        let files = vec![
            cs("App/Orders/Handler.cs", &["Acme.App.Orders"], &["Acme.App.Orders.Handler"], vec![], &["Validator", "Clock"]),
            cs("App/Orders/Validator.cs", &["Acme.App.Orders"], &["Acme.App.Orders.Validator"], vec![], &[]),
            cs("App/Clock.cs", &["Acme.App"], &["Acme.App.Clock"], vec![], &[]),
        ];
        assert_eq!(
            resolve(&files),
            vec![edge("App/Orders/Handler.cs", "App/Clock.cs"), edge("App/Orders/Handler.cs", "App/Orders/Validator.cs")]
        );
    }

    #[test]
    fn sibling_namespaces_are_not_visible_without_using() {
        let files = vec![
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &["Handler"]),
            cs("App/Handler.cs", &["Acme.App"], &["Acme.App.Handler"], vec![], &[]),
        ];
        assert!(resolve(&files).is_empty());
    }

    #[test]
    fn global_using_applies_within_its_project_only() {
        let global = NamespaceUsing { target: "Acme.Domain".into(), is_global: true, ..Default::default() };
        let files = vec![
            cs("App/GlobalUsings.cs", &[], &[], vec![global], &[]),
            cs("App/Handler.cs", &["Acme.App"], &["Acme.App.Handler"], vec![], &["Order"]),
            cs("Tool/Main.cs", &["Acme.Tool"], &["Acme.Tool.Main"], vec![], &["Order"]),
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
        ];
        let project_map: HashMap<String, String> = [
            ("App/GlobalUsings.cs", "App"),
            ("App/Handler.cs", "App"),
            ("Tool/Main.cs", "Tool"),
            ("Domain/Order.cs", "Domain"),
        ]
        .into_iter()
        .map(|(f, p)| (f.to_string(), p.to_string()))
        .collect();
        assert_eq!(resolve_with_projects(&files, &project_map), vec![edge("App/Handler.cs", "Domain/Order.cs")]);
    }

    #[test]
    fn using_static_and_alias_resolve_to_the_named_type() {
        let stat = NamespaceUsing { target: "Acme.Domain.Guard".into(), is_static: true, ..Default::default() };
        let alias = NamespaceUsing { target: "Acme.Domain.Order".into(), alias: Some("Ord".into()), ..Default::default() };
        let files = vec![
            cs("App/A.cs", &["Acme.App"], &["Acme.App.A"], vec![stat], &["NotNull"]),
            cs("App/B.cs", &["Acme.App"], &["Acme.App.B"], vec![alias], &["Ord"]),
            cs("Domain/Guard.cs", &["Acme.Domain"], &["Acme.Domain.Guard"], vec![], &[]),
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
        ];
        assert_eq!(
            resolve(&files),
            vec![edge("App/A.cs", "Domain/Guard.cs"), edge("App/B.cs", "Domain/Order.cs")]
        );
    }

    #[test]
    fn namespace_alias_resolves_dotted_members() {
        let alias = NamespaceUsing { target: "Acme.Domain".into(), alias: Some("D".into()), ..Default::default() };
        let files = vec![
            cs("App/A.cs", &["Acme.App"], &["Acme.App.A"], vec![alias], &["D.Order"]),
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
        ];
        assert_eq!(resolve(&files), vec![edge("App/A.cs", "Domain/Order.cs")]);
    }

    #[test]
    fn dotted_references_resolve_absolute_relative_and_by_outer_type() {
        let files = vec![
            cs("App/A.cs", &["Acme.App"], &["Acme.App.A"], vec![], &["Acme.Domain.Order"]),
            cs("App/B.cs", &["Acme"], &["Acme.B"], vec![], &["Domain.Invoice.Line"]),
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
            cs("Domain/Invoice.cs", &["Acme.Domain"], &["Acme.Domain.Invoice", "Acme.Domain.Invoice.Line"], vec![], &[]),
        ];
        assert_eq!(
            resolve(&files),
            vec![edge("App/A.cs", "Domain/Order.cs"), edge("App/B.cs", "Domain/Invoice.cs")]
        );
    }

    #[test]
    fn dotted_lookup_never_strips_into_the_namespace() {
        // `order.Lines` in namespace Acme.Domain must not match a class
        // named `Domain` in namespace Acme.
        let files = vec![
            cs("Domain/Handler.cs", &["Acme.Domain"], &["Acme.Domain.Handler"], vec![], &["order.Lines"]),
            cs("Domain.cs", &["Acme"], &["Acme.Domain"], vec![], &[]),
        ];
        assert!(resolve(&files).is_empty());
    }

    #[test]
    fn attribute_suffix_and_extension_methods_resolve() {
        let mut ext_file = cs("Infra/Registration.cs", &["Acme.Infra"], &["Acme.Infra.Registration"], vec![], &[]);
        if let Some(ns) = ext_file.sa.as_mut().and_then(|sa| sa.ns.as_mut()) {
            ns.ext = vec!["Acme.Infra.AddInfra".to_string()];
        }
        let files = vec![
            cs("App/Startup.cs", &["Acme.App"], &["Acme.App.Startup"], vec![using("Acme.Infra")], &["AddInfra", "Audited"]),
            cs("Infra/AuditedAttribute.cs", &["Acme.Infra"], &["Acme.Infra.AuditedAttribute"], vec![], &[]),
            ext_file,
        ];
        assert_eq!(
            resolve(&files),
            vec![edge("App/Startup.cs", "Infra/AuditedAttribute.cs"), edge("App/Startup.cs", "Infra/Registration.cs")]
        );
    }

    #[test]
    fn partial_type_parts_reach_each_other_but_never_themselves() {
        let files = vec![
            cs("Domain/Order.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &["Order"]),
            cs("Domain/Order.Rules.cs", &["Acme.Domain"], &["Acme.Domain.Order"], vec![], &[]),
            cs("App/Handler.cs", &["Acme.App"], &["Acme.App.Handler"], vec![using("Acme.Domain")], &["Order"]),
        ];
        // A consumer depends on every part of a partial type.
        assert_eq!(
            resolve(&files),
            vec![
                edge("App/Handler.cs", "Domain/Order.Rules.cs"),
                edge("App/Handler.cs", "Domain/Order.cs"),
                edge("Domain/Order.cs", "Domain/Order.Rules.cs"),
            ]
        );
    }

    #[test]
    fn files_without_namespace_info_are_ignored() {
        let files = vec![make_file("main.py", "main.py", "python", None)];
        assert!(resolve(&files).is_empty());
    }
}
