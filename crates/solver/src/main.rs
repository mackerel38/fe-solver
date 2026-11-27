#![forbid(unsafe_code)]
//! CLI:
//!   fe_solver solve <FE-XXXX | 方程式> [--timeout 秒] [--json] [--proof]
//!   fe_solver list [seen|unseen|challenge|all]

use fe_solver::parse::parse_general;
use fe_solver::problems::{load_problems, Set};
use fe_solver::solve::{default_schedule, report, solve_with};
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
        "scan-choice" => {
            // 計測用: 各点で 2 つの候補を自由に選べる（病的な解が存在する）方程式を数える。証明には使わない
            let lib = fe_solver::scan::library();
            for p in load_problems().expect("data") {
                let (l, r) = p.equations[0].parsed.sides();
                let k = fe_kernel::Kernel::new(l.clone(), r.clone()).expect("kernel");
                let sols: Vec<&(String, fe_kernel::Poly)> = lib.iter().filter(|(_, g)| k.verify_solution(g).is_ok()).collect();
                let mut pairs = Vec::new();
                for i in 0..sols.len() {
                    for j in i + 1..sols.len() {
                        if fe_solver::scan::pointwise_choice_ok(&l, &r, &sols[i].1, &sols[j].1) {
                            pairs.push(format!("{{{}, {}}}", sols[i].0, sols[j].0));
                        }
                    }
                }
                let add = k.verify_additive(&fe_kernel::Poly::zero()).is_ok() || k.verify_additive(&fe_kernel::Poly::f(fe_kernel::Poly::zero())).is_ok();
                let z = fe_kernel::Poly::zero();
                let inv = fe_solver::scan::additive_ok(&l, &r, &z, 1);
                let proj = fe_solver::scan::additive_ok(&l, &r, &z, 2);
                if !pairs.is_empty() || add || inv || proj {
                    println!("{}\t{:?}\t{}\tadditive={} inv={} proj={}\t{}", p.id, p.set, p.equations[0].display, add, inv, proj, pairs.join(" "));
                }
            }
        }
        "solve" => {
            let target = args.get(2).expect("問題 ID か方程式");
            let mut timeout = 60.0;
            let mut as_json = false;
            let mut proof = false;
            let mut dump = false;
            let mut schedule = default_schedule();
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
                    "--width" => {
                        schedule = vec![(args[i + 1].parse().expect("幅"), 1.0)];
                        i += 1;
                    }
                    "--schedule" => {
                        // 例: 0.5:0.25,1:0.35,2:1
                        schedule = args[i + 1]
                            .split(',')
                            .map(|t| {
                                let (w, f) = t.split_once(':').expect("幅:割合");
                                (w.parse().expect("幅"), f.parse().expect("割合"))
                            })
                            .collect();
                        i += 1;
                    }
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
            let out = solve_with(lhs, rhs, Duration::from_secs_f64(timeout), &schedule).expect("solve");
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
                // 加法的関数を含む族を先に、それに含まれる多項式の族は省いて並べる
                let mut fams: Vec<String> = out.add_families.iter().map(|f| json_str(&fe_render::fmt_add_family(f))).collect();
                fams.extend(
                    fe_render::display_families(&out.families)
                        .into_iter()
                        .filter(|f| !out.add_families.iter().any(|a| fe_render::subsumed_by_additive(f, a)))
                        .map(|f| json_str(&fe_render::fmt_family(f))),
                );
                fams.extend(out.pw_families.iter().map(|f| json_str(&fe_render::fmt_pw(f))));
                let mut found: Vec<String> = out.add_found.iter().map(|f| json_str(&fe_render::fmt_add_family(f))).collect();
                if out.add_found.is_none() {
                    found.extend(out.arb_found.iter().map(|f| json_str(&fe_render::fmt_arb(f))));
                }
                found.extend(
                    fe_render::display_families(&out.found)
                        .into_iter()
                        .filter(|f| !out.add_found.iter().any(|a| fe_render::subsumed_by_additive(f, a)))
                        .map(|f| json_str(&fe_render::fmt_family(f))),
                );
                found.extend(out.pw_found.iter().map(|f| json_str(&fe_render::fmt_pw(f))));
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
