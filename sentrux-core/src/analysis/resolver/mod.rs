//! Import resolution — resolves import specifiers to file paths.
//!
//! Unified suffix-index resolver for ALL languages. No tier split.
//! JS/TS path aliases (tsconfig.json) handled via plugin-declared config.
//! Namespace-import languages (C#) resolve through `namespace` instead.

pub mod helpers;
pub mod namespace;
pub mod suffix;
