//! fe_solver: R→R 関数方程式ソルバの探索部・パーサ。
//! 証明済みの事実は fe_kernel の推論規則を呼ぶことでしか得られない。
#![forbid(unsafe_code)]

pub mod parse;
pub mod problems;
