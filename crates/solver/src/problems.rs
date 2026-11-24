//! data/problems.json と data/split.json の読み込み。

use crate::parse::{parse_strict, StrictEq};
use serde_json::Value;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Set {
    /// 評価セットのうち初見セットでないもの
    Seen,
    /// 初見セット（評価セットから固定の乱数で取り分けたもの）
    Unseen,
    /// 挑戦セット（サイトで solved でないもの）
    Challenge,
}

#[derive(Clone, Debug)]
pub struct ProblemEq {
    pub display: String,
    pub left: Vec<String>,
    pub right: Vec<String>,
    pub parsed: StrictEq,
}

#[derive(Clone, Debug)]
pub struct Problem {
    pub id: String,
    pub status: String,
    pub set: Set,
    pub equations: Vec<ProblemEq>,
}

pub fn data_dir() -> PathBuf {
    if let Ok(d) = std::env::var("FE_DATA") {
        return PathBuf::from(d);
    }
    let here = Path::new(env!("CARGO_MANIFEST_DIR"));
    here.join("..").join("..").join("data")
}

pub fn load_problems() -> Result<Vec<Problem>, String> {
    let dir = data_dir();
    let read = |name: &str| -> Result<Value, String> {
        let t = std::fs::read_to_string(dir.join(name)).map_err(|e| format!("{}: {}", name, e))?;
        serde_json::from_str(&t).map_err(|e| format!("{}: {}", name, e))
    };
    let probs = read("problems.json")?;
    let split = read("split.json")?;
    let ids = |k: &str| -> Vec<String> {
        split[k].as_array().map(|a| a.iter().filter_map(|v| v.as_str().map(String::from)).collect()).unwrap_or_default()
    };
    let unseen = ids("unseen");
    let evaluation = ids("evaluation");
    let mut out = Vec::new();
    for p in probs.as_array().ok_or("problems.json が配列ではない")? {
        let id = p["id"].as_str().ok_or("id がない")?.to_string();
        let status = p["status"].as_str().unwrap_or("open").to_string();
        let set = if unseen.contains(&id) {
            Set::Unseen
        } else if evaluation.contains(&id) {
            Set::Seen
        } else {
            Set::Challenge
        };
        let mut equations = Vec::new();
        for e in p["equations"].as_array().ok_or("equations がない")? {
            let display = e["display"].as_str().ok_or("display がない")?.to_string();
            let sv = |k: &str| -> Vec<String> {
                e[k].as_array().map(|a| a.iter().filter_map(|v| v.as_str().map(String::from)).collect()).unwrap_or_default()
            };
            let parsed = parse_strict(&display).map_err(|m| format!("{}: {}: {}", id, display, m))?;
            equations.push(ProblemEq { display, left: sv("left"), right: sv("right"), parsed });
        }
        out.push(Problem { id, status, set, equations });
    }
    Ok(out)
}
