//! fe_solver: R→R 関数方程式ソルバの探索部・パーサ。
//! 証明済みの事実は fe_kernel の推論規則を呼ぶことでしか得られない。
#![forbid(unsafe_code)]

pub mod engine;
pub mod matching;
pub mod order;
pub mod parse;
pub mod polyutil;
pub mod pos;
pub mod problems;
pub mod search;
pub mod solve;
