// Token Arbitrariness Demo
// Companion to: "is lim sin(x)/x = 1, == 1, or ~= 1?"
//
// Same program + different budget = different tokens + different result.
// Token is arbitrary.

use serde::Deserialize;
use std::fmt;


//  CONFIG — loaded from JSON
#[derive(Deserialize)]
struct Config {
    cases: Vec<Case>,
}

#[derive(Deserialize)]
struct Case {
    name: String,
    description: String,
    program: Program,
    budgets: Vec<BudgetCfg>,
}

#[derive(Deserialize)]
#[serde(tag = "type")]
enum Program {
    #[serde(rename = "collatz")]
    Collatz { start: i64 },
    #[serde(rename = "infinite")]
    Infinite { init: i64, stride: i64 },
    #[serde(rename = "concrete")]
    Concrete { init: i64, stride: i64, exit_at: usize },
    #[serde(rename = "limit")]
    Limit { scale: i64 },
}

#[derive(Deserialize)]
struct BudgetCfg {
    max_bits: u32,
    max_intervals: usize,
    max_steps: usize,
}


//  INTERVAL SET — abstract state
/// A set of values represented as sorted, non-overlapping intervals.
/// When the number of intervals exceeds capacity, the closest pair
/// is merged — introducing "phantom" values that were never observed.
/// Each merge is one token of information destruction.
#[derive(Clone)]
struct IntervalSet {
    intervals: Vec<(i64, i64)>,
    capacity: usize,
}

impl IntervalSet {
    fn new(capacity: usize) -> Self {
        Self {
            intervals: Vec::new(),
            capacity,
        }
    }

    fn contains(&self, v: i64) -> bool {
        self.intervals.iter().any(|&(lo, hi)| lo <= v && v <= hi)
    }

    /// Insert a value. Returns the number of phantom values introduced
    /// by forced merging (0 = no information loss).
    fn insert(&mut self, v: i64) -> usize {
        if self.contains(v) {
            return 0;
        }

        self.intervals.push((v, v));
        self.normalize();

        let mut phantoms = 0;
        while self.intervals.len() > self.capacity {
            phantoms += self.merge_closest();
        }
        phantoms
    }

    /// Merge overlapping or adjacent intervals (lossless).
    fn normalize(&mut self) {
        self.intervals.sort_by_key(|&(lo, _)| lo);
        let mut i = 0;
        while i + 1 < self.intervals.len() {
            if self.intervals[i].1 + 1 >= self.intervals[i + 1].0 {
                self.intervals[i].1 = self.intervals[i].1.max(self.intervals[i + 1].1);
                self.intervals.remove(i + 1);
            } else {
                i += 1;
            }
        }
    }

    /// Merge the pair with the smallest gap. Returns phantom count.
    fn merge_closest(&mut self) -> usize {
        if self.intervals.len() <= 1 {
            return 0;
        }

        let mut min_gap = i64::MAX;
        let mut idx = 0;
        for i in 0..self.intervals.len() - 1 {
            let gap = self.intervals[i + 1].0 - self.intervals[i].1 - 1;
            if gap < min_gap {
                min_gap = gap;
                idx = i;
            }
        }

        let phantoms = (self.intervals[idx + 1].0 - self.intervals[idx].1 - 1) as usize;
        self.intervals[idx].1 = self.intervals[idx + 1].1;
        self.intervals.remove(idx + 1);
        phantoms
    }

    fn memory_size(&self, bits: u32) -> usize {
        let bytes_per_num = (bits as usize + 7) / 8;
        self.intervals.len() * 2 * bytes_per_num
    }
}

impl fmt::Display for IntervalSet {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.intervals.is_empty() {
            return write!(f, "{{}}");
        }
        for (i, &(lo, hi)) in self.intervals.iter().enumerate() {
            if i > 0 {
                write!(f, " U ")?;
            }
            if lo == hi {
                write!(f, "{{{}}}", lo)?;
            } else {
                write!(f, "[{}, {}]", lo, hi)?;
            }
        }
        Ok(())
    }
}


//  BUDGET
struct Budget {
    max_bits: u32,
    max_intervals: usize,
    max_steps: usize,
}

impl Budget {
    fn max_value(&self) -> i64 {
        if self.max_bits >= 127 {
            i64::MAX
        } else {
            (1i64 << self.max_bits) - 1
        }
    }

    fn in_range(&self, v: i64) -> bool {
        v >= 0 && v <= self.max_value()
    }
}

impl fmt::Display for Budget {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "bits={}, intervals={}, steps={}",
            self.max_bits, self.max_intervals, self.max_steps
        )
    }
}


//  RESULT + TRACE
enum Outcome {
    Unknown(String),
    Infinite(String),
    Concrete { exit_count: usize, value: i64 },
    Frozen,
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Outcome::Unknown(r) => write!(f, "UNKNOWN  -- {}", r),
            Outcome::Infinite(d) => write!(f, "INFINITE -- {}", d),
            Outcome::Concrete { exit_count, value } => {
                write!(f, "CONCRETE -- exit at step {}, value = {}", exit_count, value)
            }
            Outcome::Frozen => write!(f, "FROZEN   -- L bound, not yet evaluated"),
        }
    }
}

struct Step {
    n: usize,
    value: i64,
    state: IntervalSet,
    phantoms: usize,
    total_phantoms: usize,
    merges: usize,
    memory: usize,
}

fn print_analysis(budget: &Budget, steps: &[Step], result: &Outcome) {
    println!("  Budget: {}", budget);

    let max_show = 14;
    let len = steps.len();

    for (i, s) in steps.iter().enumerate() {
        let half = max_show / 2;
        if len > max_show + 2 && i >= half && i < len - half {
            if i == half {
                println!(
                    "    ... {} steps omitted ...",
                    len - max_show
                );
            }
            continue;
        }

        let lost = if s.phantoms > 0 {
            format!("<- LOST(+{})", s.phantoms)
        } else {
            String::new()
        };

        if s.n == 0 && s.state.intervals.is_empty() {
            println!(
                "    step {:>4}: {:>8}    {{}}    mem={}B  merges={}  (frozen)",
                s.n, "—", s.memory, s.merges
            );
        } else {
            println!(
                "    step {:>4}: {:>8}    {}    mem={}B  merges={}  {}",
                s.n, s.value, s.state, s.memory, s.merges, lost
            );
        }
    }

    println!();
    println!("  Result: {}", result);
    if let Some(last) = steps.last() {
        println!(
            "  Tokens(merges): {}  |  Phantoms: {}  |  Peak memory: {}B",
            last.merges,
            last.total_phantoms,
            steps.iter().map(|s| s.memory).max().unwrap_or(0),
        );
    }
    println!();
}


//  COLLATZ
fn collatz_step(n: i64) -> i64 {
    if n % 2 == 0 {
        n / 2
    } else {
        3 * n + 1
    }
}

fn analyze_collatz(start: i64, budget: &Budget) -> (Vec<Step>, Outcome) {
    let mut trace = Vec::new();
    let mut state = IntervalSet::new(budget.max_intervals);
    let mut a = start;
    let mut merges = 0usize;
    let mut total_phantoms = 0usize;

    state.insert(a);
    trace.push(Step {
        n: 0,
        value: a,
        state: state.clone(),
        phantoms: 0,
        total_phantoms: 0,
        merges: 0,
        memory: state.memory_size(budget.max_bits),
    });

    for step in 1..=budget.max_steps {
        let next = collatz_step(a);

        if !budget.in_range(next) {
            return (
                trace,
                Outcome::Unknown(format!(
                    "overflow at step {}: {} -> {} exceeds {} bits",
                    step, a, next, budget.max_bits
                )),
            );
        }

        a = next;
        let phantoms = state.insert(a);
        if phantoms > 0 {
            merges += 1;
        }
        total_phantoms += phantoms;

        trace.push(Step {
            n: step,
            value: a,
            state: state.clone(),
            phantoms,
            total_phantoms,
            merges,
            memory: state.memory_size(budget.max_bits),
        });

        if a == 1 {
            return (trace, Outcome::Concrete { exit_count: step, value: a });
        }
    }

    (
        trace,
        Outcome::Unknown(format!("step budget ({}) exhausted", budget.max_steps)),
    )
}


//  INFINITE LOOP
fn analyze_infinite(init: i64, stride: i64, budget: &Budget) -> (Vec<Step>, Outcome) {
    let mut trace = Vec::new();
    let mut state = IntervalSet::new(budget.max_intervals);
    let mut b = init;
    let mut merges = 0usize;
    let mut total_phantoms = 0usize;

    state.insert(b);
    trace.push(Step {
        n: 0,
        value: b,
        state: state.clone(),
        phantoms: 0,
        total_phantoms: 0,
        merges: 0,
        memory: state.memory_size(budget.max_bits),
    });

    for step in 1..=budget.max_steps {
        b += stride;

        if !budget.in_range(b) {
            return (
                trace,
                Outcome::Infinite(format!(
                    "{{{}, +, {}}}, overflow at step {}",
                    init, stride, step
                )),
            );
        }

        let phantoms = state.insert(b);
        if phantoms > 0 {
            merges += 1;
        }
        total_phantoms += phantoms;

        trace.push(Step {
            n: step,
            value: b,
            state: state.clone(),
            phantoms,
            total_phantoms,
            merges,
            memory: state.memory_size(budget.max_bits),
        });
    }

    (
        trace,
        Outcome::Infinite(format!(
            "{{{}, +, {}}}, step budget ({}) exhausted",
            init, stride, budget.max_steps
        )),
    )
}


//  CONCRETE LOOP


fn analyze_concrete(
    init: i64,
    stride: i64,
    exit_at: usize,
    budget: &Budget,
) -> (Vec<Step>, Outcome) {
    let mut trace = Vec::new();
    let mut state = IntervalSet::new(budget.max_intervals);
    let mut c = init;
    let mut merges = 0usize;
    let mut total_phantoms = 0usize;

    state.insert(c);
    trace.push(Step {
        n: 0,
        value: c,
        state: state.clone(),
        phantoms: 0,
        total_phantoms: 0,
        merges: 0,
        memory: state.memory_size(budget.max_bits),
    });

    let limit = budget.max_steps.min(exit_at);
    for step in 1..=limit {
        c += stride;

        if !budget.in_range(c) {
            return (
                trace,
                Outcome::Unknown(format!("overflow at step {}", step)),
            );
        }

        let phantoms = state.insert(c);
        if phantoms > 0 {
            merges += 1;
        }
        total_phantoms += phantoms;

        trace.push(Step {
            n: step,
            value: c,
            state: state.clone(),
            phantoms,
            total_phantoms,
            merges,
            memory: state.memory_size(budget.max_bits),
        });
    }

    if limit >= exit_at {
        (trace, Outcome::Concrete { exit_count: exit_at, value: c })
    } else {
        (
            trace,
            Outcome::Unknown(format!(
                "step budget ({}) exhausted before exit ({})",
                budget.max_steps, exit_at
            )),
        )
    }
}


//  LIMIT: lim sin(x)/x as x → 0


fn analyze_limit(scale: i64, budget: &Budget) -> (Vec<Step>, Outcome) {
    let mut trace = Vec::new();
    let mut state = IntervalSet::new(budget.max_intervals);
    let target = scale; // 1.0 in fixed-point
    let mut merges = 0usize;
    let mut total_phantoms = 0usize;

    // Step 0: freeze — "let L = lim sin(x)/x". Name bound, not
    // yet evaluated. No operator applied, no capacity used.
    trace.push(Step {
        n: 0,
        value: 0, // placeholder; frozen, unevaluated
        state: state.clone(),
        phantoms: 0,
        total_phantoms: 0,
        merges: 0,
        memory: state.memory_size(budget.max_bits),
    });

    for step in 1..=budget.max_steps {
        // x = 1, 0.1, 0.01, 0.001, ...
        let x = 10f64.powi(-(step as i32 - 1));
        let sinc = x.sin() / x;
        let value = (sinc * scale as f64).round() as i64;

        if !budget.in_range(value) {
            return (
                trace,
                Outcome::Unknown(format!("overflow at step {}", step)),
            );
        }

        let phantoms = state.insert(value);
        if phantoms > 0 {
            merges += 1;
        }
        total_phantoms += phantoms;

        trace.push(Step {
            n: step,
            value,
            state: state.clone(),
            phantoms,
            total_phantoms,
            merges,
            memory: state.memory_size(budget.max_bits),
        });
    }

    let last_value = trace.last().map(|s| s.value).unwrap_or(0);
    if trace.len() == 1 {
        // Only freeze, no evaluation
        (trace, Outcome::Frozen)
    } else if last_value == target {
        let exit = trace.len() - 1;
        (
            trace,
            Outcome::Concrete {
                exit_count: exit,
                value: last_value,
            },
        )
    } else {
        (
            trace,
            Outcome::Infinite(format!(
                "converging: last = {}, target = {} (1.0)",
                last_value, target
            )),
        )
    }
}


//  MAIN


fn main() {
    let path = std::env::args().nth(1).unwrap_or_else(|| "cases.json".into());
    let file = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {}", path, e));
    let config: Config = serde_json::from_str(&file)
        .unwrap_or_else(|e| panic!("failed to parse {}: {}", path, e));

    println!("==================================================");
    println!("  Token Arbitrariness Demo");
    println!("  Same program, different budget, different tokens.");
    println!("==================================================");
    println!();

    for case in &config.cases {
        println!("--- {} ---", case.name);
        println!("  {}", case.description);
        println!();

        for b in &case.budgets {
            let budget = Budget {
                max_bits: b.max_bits,
                max_intervals: b.max_intervals,
                max_steps: b.max_steps,
            };

            let (trace, result) = match &case.program {
                Program::Collatz { start } => analyze_collatz(*start, &budget),
                Program::Infinite { init, stride } => analyze_infinite(*init, *stride, &budget),
                Program::Concrete { init, stride, exit_at } => {
                    analyze_concrete(*init, *stride, *exit_at, &budget)
                }
                Program::Limit { scale } => analyze_limit(*scale, &budget),
            };

            print_analysis(&budget, &trace, &result);
        }
    }
}
