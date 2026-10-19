//! Namespace extraction — declared namespaces, types, usings and references.
//!
//! For languages where an import names a namespace (C# `using A.B;`) the
//! import text alone cannot be mapped to a file. This walker records the
//! per-file facts the namespace resolver joins across the project:
//!
//!   - namespaces declared (block-scoped and file-scoped, nested ones joined)
//!   - types declared, qualified by namespace and outer type
//!   - extension methods declared, qualified by namespace
//!   - using directives (plain, `static`, `global`, aliased)
//!   - names referenced (identifiers and dotted names), minus declaration names
//!   - member names invoked, the only names matched against extension methods
//!
//! Fully data-driven by `[semantics.namespaces]` in plugin.toml.

use crate::analysis::plugin::profile::NamespaceConfig;
use crate::core::types::{NamespaceInfo, NamespaceUsing};
use std::collections::BTreeSet;
use tree_sitter::Node;

/// Max AST depth walked. Deeper nodes are ignored (pathological input).
const MAX_DEPTH: usize = 512;

/// Walk a parsed tree and collect its namespace facts.
pub(crate) fn extract_namespace_info(root: Node<'_>, content: &[u8], cfg: &NamespaceConfig) -> NamespaceInfo {
    let mut w = Walker {
        cfg,
        content,
        decl: BTreeSet::new(),
        types: BTreeSet::new(),
        ext: BTreeSet::new(),
        usings: Vec::new(),
        refs: BTreeSet::new(),
        calls: BTreeSet::new(),
    };
    w.walk_children(root, &Scope::default(), 0);
    NamespaceInfo {
        decl: w.decl.into_iter().collect(),
        types: w.types.into_iter().collect(),
        ext: w.ext.into_iter().collect(),
        usings: w.usings,
        refs: w.refs.into_iter().collect(),
        calls: w.calls.into_iter().collect(),
    }
}

/// Lexical position while walking: enclosing namespace and enclosing type.
#[derive(Default, Clone)]
struct Scope {
    /// Fully qualified enclosing namespace ("" = global namespace).
    ns: String,
    /// Fully qualified enclosing type, if inside a type body.
    ty: Option<String>,
}

struct Walker<'a> {
    cfg: &'a NamespaceConfig,
    content: &'a [u8],
    decl: BTreeSet<String>,
    types: BTreeSet<String>,
    ext: BTreeSet<String>,
    usings: Vec<NamespaceUsing>,
    refs: BTreeSet<String>,
    calls: BTreeSet<String>,
}

fn join(prefix: &str, name: &str) -> String {
    if prefix.is_empty() { name.to_string() } else { format!("{prefix}.{name}") }
}

fn has(list: &[String], kind: &str) -> bool {
    list.iter().any(|k| k == kind)
}

/// A dotted identifier chain: `A`, `A.B.C`. Rejects calls, generics, `this.x`.
fn is_dotted_name(s: &str) -> bool {
    !s.is_empty()
        && s.split('.').all(|seg| {
            let mut chars = seg.chars();
            matches!(chars.next(), Some(c) if c.is_alphabetic() || c == '_')
                && chars.all(|c| c.is_alphanumeric() || c == '_')
        })
}

/// Strip whitespace and C#'s `@` verbatim-identifier prefix from a name.
fn clean_name(raw: &str) -> String {
    raw.chars().filter(|c| !c.is_whitespace() && *c != '@').collect()
}

impl<'a> Walker<'a> {
    fn text(&self, node: Node<'_>) -> &'a str {
        node.utf8_text(self.content).unwrap_or("")
    }

    /// Walk the children of `node`. A file-scoped namespace declaration
    /// (a declaration kind without a `body`) changes the namespace of the
    /// siblings that follow it.
    fn walk_children(&mut self, node: Node<'_>, scope: &Scope, depth: usize) {
        if depth > MAX_DEPTH {
            return;
        }
        let mut scope = scope.clone();
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if has(&self.cfg.declaration_kinds, child.kind()) && child.child_by_field_name("body").is_none() {
                let name = child.child_by_field_name("name").map(|n| clean_name(self.text(n))).unwrap_or_default();
                scope = Scope { ns: join(&scope.ns, &name), ty: None };
                self.decl.insert(scope.ns.clone());
                // Older grammars nest the following declarations inside it.
                self.walk_children(child, &scope, depth + 1);
                continue;
            }
            self.walk(child, &scope, depth + 1);
        }
    }

    fn walk(&mut self, node: Node<'_>, scope: &Scope, depth: usize) {
        if depth > MAX_DEPTH {
            return;
        }
        let kind = node.kind();
        let cfg = self.cfg;

        if has(&cfg.using_kinds, kind) {
            self.record_using(node);
            return;
        }

        if has(&cfg.declaration_kinds, kind) {
            let name = node.child_by_field_name("name").map(|n| clean_name(self.text(n))).unwrap_or_default();
            let inner = Scope { ns: join(&scope.ns, &name), ty: None };
            self.decl.insert(inner.ns.clone());
            match node.child_by_field_name("body") {
                Some(body) => self.walk_children(body, &inner, depth + 1),
                None => self.walk_children(node, &inner, depth + 1),
            }
            return;
        }

        if has(&cfg.type_declaration_kinds, kind) {
            if let Some(name_node) = node.child_by_field_name("name") {
                let name = clean_name(self.text(name_node));
                let fq = join(scope.ty.as_deref().unwrap_or(&scope.ns), &name);
                self.types.insert(fq.clone());
                let inner = Scope { ns: scope.ns.clone(), ty: Some(fq) };
                self.walk_children_except(node, name_node, &inner, depth + 1);
                return;
            }
        }

        if has(&cfg.method_kinds, kind) {
            if let Some(name_node) = node.child_by_field_name("name") {
                if self.is_extension_method(node) {
                    let name = clean_name(self.text(name_node));
                    self.ext.insert(join(&scope.ns, &name));
                }
                self.walk_children_except(node, name_node, scope, depth + 1);
                return;
            }
        }

        if has(&cfg.invocation_kinds, kind) {
            if let Some(name) = node.child_by_field_name("function").and_then(|f| self.invoked_name(f)) {
                self.calls.insert(name);
            }
        }

        if has(&cfg.qualified_kinds, kind) {
            let text = clean_name(self.text(node));
            if is_dotted_name(&text) {
                // Record the whole chain once; its inner prefixes (`A.B` of
                // `A.B.C`) are not references. Leaf identifiers still are.
                self.refs.insert(text);
                self.walk_leaves(node, depth);
                return;
            }
        } else if has(&cfg.reference_kinds, kind) {
            let text = clean_name(self.text(node));
            if !text.is_empty() {
                self.refs.insert(text);
            }
            return;
        }

        self.walk_children(node, scope, depth);
    }

    /// Record the reference leaves under a dotted name, skipping nested
    /// dotted-name nodes.
    fn walk_leaves(&mut self, node: Node<'_>, depth: usize) {
        if depth > MAX_DEPTH {
            return;
        }
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if has(&self.cfg.reference_kinds, child.kind()) {
                let text = clean_name(self.text(child));
                if !text.is_empty() {
                    self.refs.insert(text);
                }
            } else {
                self.walk_leaves(child, depth + 1);
            }
        }
    }

    /// Walk children of a declaration, skipping its own name node so a
    /// declaration does not count as a reference to itself (partial classes
    /// would otherwise link every part to every other part).
    fn walk_children_except(&mut self, node: Node<'_>, skip: Node<'_>, scope: &Scope, depth: usize) {
        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            if child.id() != skip.id() {
                self.walk(child, scope, depth + 1);
            }
        }
    }

    /// The member an invocation calls: the last segment of `a.b.Name` or
    /// `Name`, without type arguments (`Name<T>`).
    fn invoked_name(&self, function: Node<'_>) -> Option<String> {
        let target = function.child_by_field_name("name").unwrap_or(function);
        let text = clean_name(self.text(target));
        let name = text.split('<').next().unwrap_or("").rsplit('.').next().unwrap_or("").trim().to_string();
        (!name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_')).then_some(name)
    }

    /// Extension method: first parameter starts with the configured prefix (`this `).
    fn is_extension_method(&self, node: Node<'_>) -> bool {
        let prefix = &self.cfg.extension_param_prefix;
        if prefix.is_empty() {
            return false;
        }
        let params = match node.child_by_field_name("parameters") {
            Some(p) => p,
            None => return false,
        };
        let mut cursor = params.walk();
        let first = params.named_children(&mut cursor).next();
        first.is_some_and(|p| self.text(p).trim_start().starts_with(prefix.as_str()))
    }

    /// Record `[global] using [static] [Alias =] Target;`.
    fn record_using(&mut self, node: Node<'_>) {
        let mut is_static = false;
        let mut is_global = false;
        let mut target = None;
        let alias = node.child_by_field_name("name").map(|n| clean_name(self.text(n)));
        let alias_id = node.child_by_field_name("name").map(|n| n.id());

        let mut cursor = node.walk();
        for child in node.children(&mut cursor) {
            let text = self.text(child);
            if !child.is_named() {
                if text == self.cfg.static_keyword {
                    is_static = true;
                } else if text == self.cfg.global_keyword {
                    is_global = true;
                }
                continue;
            }
            if Some(child.id()) == alias_id {
                continue;
            }
            let name = clean_name(text);
            if is_dotted_name(&name) {
                target = Some(name);
            } else if !name.is_empty() && target.is_none() {
                // Generic alias target (`using L = List<int>;`): keep the outer name.
                let outer: String = name.split('<').next().unwrap_or("").to_string();
                if is_dotted_name(&outer) {
                    target = Some(outer);
                }
            }
        }

        if let Some(target) = target {
            self.usings.push(NamespaceUsing { target, alias, is_static, is_global });
        }
    }
}
