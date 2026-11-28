//! fe_kernel: R→R 関数方程式ソルバの検証核。
//!
//! 証明済みの事実 (`kernel::Fact`) はこのクレートの推論規則でしか作れない。
//! 探索部はこのクレートに依存するが、このクレートは探索部に依存しない（Cargo の依存関係で強制）。
//!
//! 以下はクレートの外から事実を偽造できないことのコンパイル時テスト（コンパイルに失敗すれば合格）。
//!
//! ```compile_fail
//! // Fact のフィールドは非公開なので、構造体リテラルで作れない
//! let f = fe_kernel::Fact { kernel: 1, idx: 0 };
//! ```
//!
//! ```compile_fail
//! // 事実の記録も外から作れない
//! let r = fe_kernel::kernel::FactRec { clause: todo!(), branch: fe_kernel::ROOT, rule: fe_kernel::Rule::Axiom };
//! ```
//!
//! ```compile_fail
//! // 検証済みの解の族も外から作れない
//! let fam = fe_kernel::Family { kernel: 1, g: fe_kernel::Poly::var(0), template: fe_kernel::Poly::var(0), params: vec![] };
//! ```
//!
//! ```compile_fail
//! // 検証済みの加法的な族も外から作れない
//! let fam = fe_kernel::AddFamily { kernel: 1, g: fe_kernel::Poly::zero(), template: fe_kernel::Poly::zero(), params: vec![], kind: fe_kernel::AddKind::Free };
//! ```
//!
//! ```compile_fail
//! // 検証済みの区分的な族も外から作れない
//! let fam = fe_kernel::PwFamily { kernel: 1, breaks: vec![], pieces: vec![] };
//! ```
//!
//! ```compile_fail
//! // 検証済みの「有理数と無理数で式を変える族」も外から作れない
//! let fam = fe_kernel::QsFamily { kernel: 1, g_rat: fe_kernel::Poly::var(0), g_irr: fe_kernel::Poly::zero() };
//! ```
//!
//! ```compile_fail
//! // 検証核が保持する事実の一覧は外から書き換えられない
//! fn tamper(k: &mut fe_kernel::Kernel) { k.facts.clear(); }
//! ```
//!
//! ```compile_fail
//! // 読み取り用の参照から節を書き換えることもできない
//! fn tamper(k: &fe_kernel::Kernel, f: fe_kernel::Fact) { let c: &mut fe_kernel::Clause = k.clause(f); }
//! ```
#![forbid(unsafe_code)]

pub mod clause;
pub mod kernel;
pub mod piecewise;
pub mod poly;
pub mod rational;

pub use clause::{Clause, Lit, Rel};
pub use kernel::{AddFamily, AddKind, BranchId, Conclusion, Fact, Family, Kernel, Rule, Split, ROOT};
pub use piecewise::{ArbFamily, ArbPiece, PwFamily};
pub use poly::{Atom, Mono, Poly, Q};
pub use rational::QsFamily;
