//! Tests for namespace extraction (C# `[semantics.namespaces]`).
//!
//! Dump the C# AST of the sample with:
//! cargo test csharp_namespace_ast_dump -- --ignored --nocapture

#[cfg(test)]
mod tests {
    use crate::analysis::parser::parse_bytes;
    use crate::core::types::{NamespaceInfo, NamespaceUsing};

    const SAMPLE: &str = r#"global using Acme.Shared;
using System;
using Acme.Domain.Orders;
using static Acme.Domain.Guard;
using Ord = Acme.Domain.Orders.Order;

namespace Acme.Application
{
    namespace Handlers
    {
        [Audited]
        public sealed partial class PlaceOrder : ICommandHandler<PlaceOrderCommand>
        {
            private readonly IClock _clock;

            public Ord Handle(PlaceOrderCommand cmd)
            {
                var line = new Acme.Domain.Orders.Line();
                Repo.Save(cmd.Id);
                return Order.Create(_clock.Now);
            }

            private sealed class Nested { }
        }
    }

    public static class Registration
    {
        public static IServices AddApplication(this IServices services) => services;
    }
}
"#;

    fn ns_of(code: &str) -> NamespaceInfo {
        let sa = parse_bytes(code.as_bytes(), "csharp").expect("csharp parse failed");
        sa.ns.expect("csharp profile should enable namespace extraction")
    }

    fn using(target: &str, alias: Option<&str>, is_static: bool, is_global: bool) -> NamespaceUsing {
        NamespaceUsing { target: target.to_string(), alias: alias.map(str::to_string), is_static, is_global }
    }

    #[test]
    fn csharp_declared_namespaces_nest() {
        let ns = ns_of(SAMPLE);
        assert_eq!(ns.decl, vec!["Acme.Application", "Acme.Application.Handlers"]);
    }

    #[test]
    fn csharp_types_are_qualified_by_namespace_and_outer_type() {
        let ns = ns_of(SAMPLE);
        assert_eq!(
            ns.types,
            vec![
                "Acme.Application.Handlers.PlaceOrder",
                "Acme.Application.Handlers.PlaceOrder.Nested",
                "Acme.Application.Registration",
            ]
        );
    }

    #[test]
    fn csharp_extension_methods_are_qualified_by_namespace() {
        let ns = ns_of(SAMPLE);
        assert_eq!(ns.ext, vec!["Acme.Application.AddApplication"]);
    }

    #[test]
    fn csharp_using_forms() {
        let ns = ns_of(SAMPLE);
        assert_eq!(
            ns.usings,
            vec![
                using("Acme.Shared", None, false, true),
                using("System", None, false, false),
                using("Acme.Domain.Orders", None, false, false),
                using("Acme.Domain.Guard", None, true, false),
                using("Acme.Domain.Orders.Order", Some("Ord"), false, false),
            ]
        );
    }

    #[test]
    fn csharp_references_exclude_declaration_names() {
        let ns = ns_of(SAMPLE);
        for expected in ["ICommandHandler", "PlaceOrderCommand", "IClock", "Ord", "Audited", "Order", "Repo", "IServices", "Acme.Domain.Orders.Line"] {
            assert!(ns.refs.iter().any(|r| r == expected), "missing ref {expected}: {:?}", ns.refs);
        }
        // Declaration names and using targets are not references.
        for absent in ["PlaceOrder", "Nested", "Registration", "Handle", "AddApplication", "Handlers", "Acme.Domain.Orders"] {
            assert!(!ns.refs.iter().any(|r| r == absent), "unexpected ref {absent}: {:?}", ns.refs);
        }
    }

    #[test]
    fn csharp_file_scoped_namespace_applies_to_following_declarations() {
        let ns = ns_of("namespace Acme.Domain;\n\npublic sealed record Order(int Id);\npublic enum Status { Open }\n");
        assert_eq!(ns.decl, vec!["Acme.Domain"]);
        assert_eq!(ns.types, vec!["Acme.Domain.Order", "Acme.Domain.Status"]);
    }

    #[test]
    fn csharp_global_namespace_types_are_unqualified() {
        let ns = ns_of("public class Program { static void Main() {} }\n");
        assert!(ns.decl.is_empty());
        assert_eq!(ns.types, vec!["Program"]);
    }

    #[test]
    fn csharp_base_list_feeds_inheritance() {
        let sa = parse_bytes(b"class Handler : BaseHandler, IHandler { }\n", "csharp").expect("csharp parse failed");
        let cls = sa.cls.expect("no classes");
        let bases = cls[0].b.clone().unwrap_or_default();
        assert!(bases.iter().any(|b| b == "BaseHandler"), "bases: {bases:?}");
        assert!(bases.iter().any(|b| b == "IHandler"), "bases: {bases:?}");
    }

    #[test]
    fn languages_without_namespace_config_have_no_ns_info() {
        let sa = parse_bytes(b"import os\n", "python").expect("python parse failed");
        assert!(sa.ns.is_none());
    }

    #[test]
    #[ignore]
    fn csharp_namespace_ast_dump() {
        let (grammar, _) = crate::analysis::lang_registry::get_grammar_and_query("csharp").expect("csharp grammar");
        let mut parser = tree_sitter::Parser::new();
        parser.set_language(grammar).unwrap();
        let tree = parser.parse(SAMPLE, None).unwrap();
        println!("{}", tree.root_node().to_sexp());
    }
}
