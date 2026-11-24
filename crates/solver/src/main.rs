#![forbid(unsafe_code)]
//! CLI:
//!   fe_solver solve <FE-XXXX | 方程式> [--timeout 秒] [--json] [--proof]
//!   fe_solver list [seen|unseen|challenge|all]

use fe_solver::parse::parse_general;
use fe_solver::problems::{load_problems, Set};
use fe_solver::solve::{report, solve};
use std::time::Duration;

fn json_str(s: &str) -> String {
    serde_json::Value::String(s.to_string()).to_string()
}

fn main() {
    // 探索は再帰が深くなりうるので大きなスタックのスレッドで動かす
    let h = std::thread::Builder::new().stack_size(512 << 20).spawn(real_main).expect("thread");
    let code = h.join().unwrap_or(101);
    std::process::exit(code);
}

fn real_main() -> i32 {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: fe_solver solve <FE-XXXX | equation> [--timeout SEC] [--json] [--proof] | list [set]");
        return 2;
    }
    match args[1].as_str() {
        "list" => {
            let which = args.get(2).map(|s| s.as_str()).unwrap_or("all");
            for p in load_problems().expect("data") {
                let ok = match which {
                    "seen" => p.set == Set::Seen,
                    "unseen" => p.set == Set::Unseen,
                    "challenge" => p.set == Set::Challenge,
                    _ => true,
                };
                if ok {
                    println!("{}\t{:?}\t{}", p.id, p.set, p.equations[0].display);
                }
            }
        }
        "solve" => {
            let target = args.get(2).expect("問題 ID か方程式");
            let mut timeout = 20.0;
            let mut as_json = false;
            let mut proof = false;
            let mut dump = false;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--timeout" => {
                        timeout = args[i + 1].parse().expect("秒数");
                        i += 1;
                    }
                    "--json" => as_json = true,
                    "--proof" => proof = true,
                    "--dump" => dump = true,
                    other => panic!("不明な引数 {}", other),
                }
                i += 1;
            }
            let (id, display, lhs, rhs) = if target.starts_with("FE-") {
                let p = load_problems().expect("data").into_iter().find(|p| p.id == *target).expect("問題が見つからない");
                let (l, r) = p.equations[0].parsed.sides();
                (p.id.clone(), p.equations[0].display.clone(), l, r)
            } else {
                let (l, r) = parse_general(target).expect("方程式の解析");
                ("custom".to_string(), target.clone(), l, r)
            };
            let out = solve(lhs, rhs, Duration::from_secs_f64(timeout)).expect("solve");
            if dump {
                for i in 0..out.kernel.num_facts() {
                    let f = out.kernel.fact_at(i).unwrap();
                    let r = out.kernel.fact(f);
                    let rule = format!("{:?}", r.rule());
                    let rule: String = rule.chars().take(160).collect();
                    eprintln!("#{} [b{}] {}    <- {}", i, r.branch().0, r.clause(), rule);
                }
            }
            if as_json {
                let fams: Vec<String> = out.families.iter().map(|f| json_str(&fe_render::fmt_family(f))).collect();
                let found: Vec<String> = out.found.iter().map(|f| json_str(&fe_render::fmt_family(f))).collect();
                let reasons: Vec<String> = out.reasons.iter().map(|r| json_str(r)).collect();
                let stats: Vec<String> = out.stats.iter().map(|(k, v)| format!("{}:{}", json_str(k), v)).collect();
                println!(
                    "{{\"id\":{},\"equation\":{},\"status\":{},\"families\":[{}],\"found\":[{}],\"reasons\":[{}],\"time_ms\":{},\"facts\":{},\"branches\":{},\"stats\":{{{}}}}}",
                    json_str(&id),
                    json_str(&display),
                    json_str(out.status),
                    fams.join(","),
                    found.join(","),
                    reasons.join(","),
                    out.elapsed.as_millis(),
                    out.kernel.num_facts(),
                    out.kernel.num_branches(),
                    stats.join(",")
                );
                if proof {
                    eprintln!("{}", report(&out));
                }
            } else {
                println!("{}", report(&out));
                eprintln!("time: {} ms, facts: {}", out.elapsed.as_millis(), out.kernel.num_facts());
            }
        }
        other => {
            eprintln!("unknown command {}", other);
            return 2;
        }
    }
    0
}
