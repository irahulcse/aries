# Aries Instrumentation Guide

## Step 1: Add Energy Profiler Module

1. Copy `energy_profiler.rs` to `planning/planners/src/`
2. Add to `planning/planners/Cargo.toml`:
```toml
[dependencies]
lazy_static = "1.4"
```

3. Add to `planning/planners/src/lib.rs`:
```rust
#[macro_use]
pub mod energy_profiler;
```

## Step 2: Instrument Main Binary

Edit `planning/planners/src/bin/planner.rs`:

```rust
// At the top
use aries_planners::energy_profiler;
use aries_planners::profile_function;

fn main() -> Result<()> {
    // ... existing code ...
    
    // PARSING
    {
        profile_function!("Parsing", "main");
        let dom = parse_pddl_domain(dom)?;
        let prob = parse_pddl_problem(prob)?;
    }
    
    // PREPROCESSING  
    {
        profile_function!("Preprocessing", "main");
        let spec = pddl_to_chronicles(&dom, &prob)?;
    }
    
    // SOLVING
    {
        profile_function!("Solving", "main");
        let result = solve(spec, ...)?;
    }
    
    // Save results before exit
    energy_profiler::save_results("energy_profile.csv");
    
    Ok(())
}
```

## Step 3: Instrument Key Functions

Add `profile_function!()` calls at the beginning of each target function.

Example for preprocessing:
```rust
pub fn preprocess(problem: &mut Problem) {
    profile_function!("Preprocessing", "preprocess");
    // ... existing code ...
}

pub fn remove_unusable_effects(problem: &mut Problem) {
    profile_function!("Preprocessing", "remove_unusable_effects");
    // ... existing code ...
}
```

## Step 4: Build and Run

```bash
cd ~/Desktop/aries
cargo build --release --bin aries-plan
aries-plan problem.hddl
cat energy_profile.csv
```

## Step 5: Analyze

```bash
python3 analyze_function_energy.py
```
