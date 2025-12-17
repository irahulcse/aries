#!/bin/bash

# Automated Aries Function-Level Instrumentation Script
# Extracts key functions and prepares them for energy profiling

set -e


ARIES_DIR="${1:-$HOME/Desktop/aries}"
OUTPUT_DIR="./aries_analysis"

echo "================================"
echo "Aries Function Analysis & Instrumentation"
echo "================================"
echo "Aries directory: $ARIES_DIR"
echo "Output directory: $OUTPUT_DIR"
echo ""

mkdir -p "$OUTPUT_DIR"/{functions,instructions,call_graphs,instrumented}

# Step 1: Extract function signatures from key modules
echo "[1/6] Extracting function signatures..."

extract_functions() {
    local file=$1
    local component=$2
    local output="$OUTPUT_DIR/functions/${component}_functions.txt"
    
    echo "Processing: $file"
    
    # Extract public functions
    grep -E "^\s*(pub\s+)?fn\s+" "$file" | \
        sed 's/^\s*//' | \
        sed 's/{.*//' | \
        awk -v comp="$component" '{print comp "," $0}' >> "$output"
}

extract_instructions(){
    local file=$1
    local component=$2
    local output="$OUTPUT_DIR/functions/${component}_instructions.txt"

    echo "Processing instructions: $file"

    # Extract lines that look like Rust instructions (excluding signatures)
    # Any line ending with ';'
    grep -E ";\s*$" "$file" \
        | sed 's/^\s*//' \
        | awk -v comp="$component" '{print comp "," $0}' >> "$output"

}

# Parse Parsing module
if [ -f "$ARIES_DIR/planning/planning/src/parsing/pddl.rs" ]; then
    extract_functions "$ARIES_DIR/planning/planning/src/parsing/pddl.rs" "Parsing"
    extract_instructions "$ARIES_DIR/planning/planning/src/parsing/pddl.rs" "Parsing"
fi

# Parse Preprocessing module
if [ -f "$ARIES_DIR/planning/planning/src/chronicles/preprocessing.rs" ]; then
    extract_functions "$ARIES_DIR/planning/planning/src/chronicles/preprocessing.rs" "Preprocessing"
    extract_instructions "$ARIES_DIR/planning/planning/src/chronicles/preprocessing.rs" "Preprocessing"
fi

# Parse Encoding/Decomposition module
if [ -f "$ARIES_DIR/planning/planners/src/encode.rs" ]; then
    extract_functions "$ARIES_DIR/planning/planners/src/encode.rs" "Decomposition"
    extract_instructions "$ARIES_DIR/planning/planners/src/encode.rs" "Decomposition"
fi

# Parse Solver modules
if [ -d "$ARIES_DIR/solver/src" ]; then
    find "$ARIES_DIR/solver/src" -name "*.rs" -type f | while read file; do
        extract_functions "$file" "Solving"
        extract_instructions "$file" "Solving"
    done
fi

echo "✓ Function signatures extracted to $OUTPUT_DIR/functions/"
echo ""

# Step 2: Analyze function calls and dependencies
echo "[2/6] Analyzing function call graph..."

cd "$ARIES_DIR/planning/planners"

# Try to build call graph
if command -v cargo-call-stack &> /dev/null; then
    cargo call-stack --bin aries-plan > "$OUTPUT_DIR/call_graphs/aries_callgraph.txt" 2>&1 || true
    echo "✓ Call graph saved to $OUTPUT_DIR/call_graphs/aries_callgraph.txt"
else
    echo "⚠ cargo-call-stack not installed. Skipping call graph generation."
    echo "  Install with: cargo install cargo-call-stack"
fi

cd - > /dev/null
echo ""

# Step 3: Identify key functions to instrument
echo "[3/6] Identifying key functions for instrumentation..."

cat > "$OUTPUT_DIR/key_functions.txt" << 'EOF'
# Key functions to instrument for energy profiling
# Format: Component,Function,Priority (1=High, 2=Medium, 3=Low)

# PARSING PHASE
Parsing,parse_pddl_domain,1
Parsing,parse_pddl_problem,1
Parsing,tokenize,2
Parsing,read_sexpr,2

# PREPROCESSING PHASE
Preprocessing,preprocess,1
Preprocessing,remove_unusable_effects,2
Preprocessing,lift_predicates_to_state_variables,2
Preprocessing,statics_as_tables,2
Preprocessing,merge_statements,2
Preprocessing,rollup_actions,2

# DECOMPOSITION PHASE
Decomposition,populate_with_task_network,1
Decomposition,gather_subtasks,2
Decomposition,instantiate_template,2
Decomposition,ensure_mutual_exclusion,3

# SOLVING PHASE
Solving,solve,1
Solving,propagate,2
Solving,unit_propagation,2
Solving,stn_propagation,2
Solving,make_decision,2
Solving,analyze_conflict,2
Solving,learn_clause,3
Solving,backtrack,3
EOF

echo "✓ Key functions listed in $OUTPUT_DIR/key_functions.txt"
echo ""

# Step 4: Generate energy profiler module
echo "[4/6] Generating energy profiler module..."

cat > "$OUTPUT_DIR/instrumented/energy_profiler.rs" << 'RUST_CODE'
//! Energy profiling module for Aries planner
//! Measures energy consumption at function level using Intel RAPL

use std::fs::File;
use std::io::{self, Read, Write};
use std::time::Instant;
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    pub static ref GLOBAL_PROFILER: Mutex<Option<EnergyProfiler>> = 
        Mutex::new(Some(EnergyProfiler::new()));
}

pub struct EnergyProfiler {
    measurements: Vec<EnergyMeasurement>,
    start_time: Instant,
    max_energy_range: u64,
}

#[derive(Clone, Debug)]
pub struct EnergyMeasurement {
    pub component: String,
    pub function: String,
    pub timestamp_ns: u128,
    pub energy_uj: u64,
    pub duration_ns: u128,
}

impl EnergyProfiler {
    pub fn new() -> Self {
        let max_range = Self::read_max_energy_range().unwrap_or(262143328850);
        Self {
            measurements: Vec::new(),
            start_time: Instant::now(),
            max_energy_range: max_range,
        }
    }
    
    fn read_max_energy_range() -> io::Result<u64> {
        let mut file = File::open("/sys/class/powercap/intel-rapl/intel-rapl:0/max_energy_range_uj")?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(contents.trim().parse().unwrap_or(262143328850))
    }
    
    fn read_rapl_energy() -> io::Result<u64> {
        let mut file = File::open("/sys/class/powercap/intel-rapl/intel-rapl:0/energy_uj")?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(contents.trim().parse().unwrap_or(0))
    }
    
    pub fn start_function(&self, component: &str, function: &str) -> FunctionGuard {
        FunctionGuard {
            component: component.to_string(),
            function: function.to_string(),
            start_energy: Self::read_rapl_energy().unwrap_or(0),
            start_time: Instant::now(),
            profiler_start: self.start_time,
            max_range: self.max_energy_range,
        }
    }
    
    pub fn record_measurement(&mut self, guard: FunctionGuard) {
        let end_energy = Self::read_rapl_energy().unwrap_or(0);
        let duration = guard.start_time.elapsed();
        
        let energy_consumed = if end_energy >= guard.start_energy {
            end_energy - guard.start_energy
        } else {
            // Handle RAPL counter overflow
            guard.max_range - guard.start_energy + end_energy
        };
        
        self.measurements.push(EnergyMeasurement {
            component: guard.component,
            function: guard.function,
            timestamp_ns: guard.profiler_start.elapsed().as_nanos(),
            energy_uj: energy_consumed,
            duration_ns: duration.as_nanos(),
        });
    }
    
    pub fn save_to_csv(&self, path: &str) -> io::Result<()> {
        let mut file = File::create(path)?;
        writeln!(file, "component,function,timestamp_ns,energy_uj,duration_ns")?;
        
        for m in &self.measurements {
            writeln!(
                file,
                "{},{},{},{},{}",
                m.component, m.function, m.timestamp_ns, m.energy_uj, m.duration_ns
            )?;
        }
        
        Ok(())
    }
    
    pub fn print_summary(&self) {
        let mut component_energy: HashMap<String, u64> = HashMap::new();
        let mut function_energy: HashMap<String, u64> = HashMap::new();
        let mut function_calls: HashMap<String, usize> = HashMap::new();
        
        for m in &self.measurements {
            *component_energy.entry(m.component.clone()).or_insert(0) += m.energy_uj;
            *function_energy.entry(m.function.clone()).or_insert(0) += m.energy_uj;
            *function_calls.entry(m.function.clone()).or_insert(0) += 1;
        }
        
        let total_energy: u64 = component_energy.values().sum();
        
        println!("\n{}", "=".repeat(80));
        println!("ENERGY PROFILING SUMMARY");
        println!("{}", "=".repeat(80));
        println!("\nTotal measurements: {}", self.measurements.len());
        println!("Total energy: {:.6} J", total_energy as f64 / 1_000_000.0);
        
        println!("\n{}", "=".repeat(80));
        println!("ENERGY BY COMPONENT");
        println!("{}", "=".repeat(80));
        let mut components: Vec<_> = component_energy.iter().collect();
        components.sort_by_key(|&(_, e)| std::cmp::Reverse(*e));
        
        println!("{:<20} {:>15} {:>15}", "Component", "Energy (J)", "Percentage");
        println!("{}", "-".repeat(80));
        for (comp, energy) in components {
            let energy_j = *energy as f64 / 1_000_000.0;
            let pct = (*energy as f64 / total_energy as f64) * 100.0;
            println!("{:<20} {:>15.6} {:>14.2}%", comp, energy_j, pct);
        }
        
        println!("\n{}", "=".repeat(80));
        println!("TOP 20 ENERGY-CONSUMING FUNCTIONS");
        println!("{}", "=".repeat(80));
        let mut functions: Vec<_> = function_energy.iter().collect();
        functions.sort_by_key(|&(_, e)| std::cmp::Reverse(*e));
        
        println!("{:<40} {:>12} {:>12} {:>12}", "Function", "Calls", "Total (J)", "Avg (J)");
        println!("{}", "-".repeat(80));
        for (func, energy) in functions.iter().take(20) {
            let energy_j = **energy as f64 / 1_000_000.0;
            let calls = function_calls.get(*func).unwrap_or(&0);
            let avg_j = energy_j / (*calls as f64);
            println!("{:<40} {:>12} {:>12.6} {:>12.6}", func, calls, energy_j, avg_j);
        }
        
        println!("\n{}", "=".repeat(80));
    }
}

pub struct FunctionGuard {
    component: String,
    function: String,
    start_energy: u64,
    start_time: Instant,
    profiler_start: Instant,
    max_range: u64,
}

impl Drop for FunctionGuard {
    fn drop(&mut self) {
        if let Ok(mut profiler) = GLOBAL_PROFILER.lock() {
            if let Some(prof) = profiler.as_mut() {
                let guard = FunctionGuard {
                    component: self.component.clone(),
                    function: self.function.clone(),
                    start_energy: self.start_energy,
                    start_time: self.start_time,
                    profiler_start: self.profiler_start,
                    max_range: self.max_range,
                };
                prof.record_measurement(guard);
            }
        }
    }
}

// Convenience macro for profiling
#[macro_export]
macro_rules! profile_function {
    ($component:expr, $function:expr) => {
        let _guard = $crate::energy_profiler::GLOBAL_PROFILER
            .lock()
            .ok()
            .and_then(|p| p.as_ref().map(|prof| prof.start_function($component, $function)));
    };
}

pub fn save_results(path: &str) {
    if let Ok(profiler) = GLOBAL_PROFILER.lock() {
        if let Some(prof) = profiler.as_ref() {
            prof.save_to_csv(path).ok();
            prof.print_summary();
        }
    }
}
RUST_CODE

echo "✓ Energy profiler module generated: $OUTPUT_DIR/instrumented/energy_profiler.rs"
echo ""

# Step 5: Generate instrumentation patches
echo "[5/6] Generating instrumentation guide..."

cat > "$OUTPUT_DIR/INSTRUMENTATION_GUIDE.md" << 'EOF'
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
EOF

echo "✓ Instrumentation guide: $OUTPUT_DIR/INSTRUMENTATION_GUIDE.md"
echo ""

# Step 6: Generate summary report
echo "[6/6] Generating analysis summary..."

cat > "$OUTPUT_DIR/ANALYSIS_SUMMARY.md" << EOF
# Aries Function-Level Analysis Summary

Generated: $(date)

## Directory Structure

\`\`\`
$OUTPUT_DIR/
├── functions/              # Extracted function signatures
├── call_graphs/            # Function call graphs
├── instrumented/           # Generated instrumentation code
│   └── energy_profiler.rs
├── key_functions.txt       # Functions to instrument
├── INSTRUMENTATION_GUIDE.md
└── ANALYSIS_SUMMARY.md     # This file
\`\`\`

## Next Steps

1. **Review key functions**: Edit \`key_functions.txt\` to prioritize functions
2. **Add profiler module**: Copy \`instrumented/energy_profiler.rs\` to Aries source
3. **Instrument code**: Follow \`INSTRUMENTATION_GUIDE.md\`
4. **Build and run**: Rebuild Aries and run on benchmarks
5. **Analyze results**: Use provided Python scripts

## Key Files to Instrument

See \`key_functions.txt\` for the complete list.

### High Priority (Component-level):
- Parsing: parse_pddl_domain, parse_pddl_problem
- Preprocessing: preprocess, remove_unusable_effects, lift_predicates
- Decomposition: populate_with_task_network
- Solving: solve, propagate, make_decision

### Medium Priority (Algorithm-level):
- Constraint propagation functions
- Search and backtracking
- Conflict analysis

### Low Priority (Helper functions):
- Individual propagators
- Data structure operations

## Measurement Considerations

- **Overhead**: Profiling adds ~10-50 microseconds per function call
- **Accuracy**: RAPL has ~1ms sampling resolution
- **Coverage**: Instrument only critical path functions first
- **Validation**: Compare total energy with external measurements

## Analysis Scripts

1. \`analyze_function_energy.py\` - Basic analysis
2. \`component_attribution_analysis.py\` - Detailed component breakdown
3. Jupyter notebook - Interactive exploration

## References

- PLANERGYM Paper: Function-level energy profiling methodology
- Intel RAPL: https://www.intel.com/rapl
- Aries Source: https://github.com/plaans/aries
EOF

echo "✓ Analysis summary: $OUTPUT_DIR/ANALYSIS_SUMMARY.md"
echo ""

echo "================================"
echo "Analysis Complete!"
echo "================================"
echo ""
echo "Output directory: $OUTPUT_DIR"
echo ""
echo "Next steps:"
echo "1. Review: $OUTPUT_DIR/key_functions.txt"
echo "2. Read: $OUTPUT_DIR/INSTRUMENTATION_GUIDE.md"
echo "3. Copy: $OUTPUT_DIR/instrumented/energy_profiler.rs to Aries"
echo "4. Instrument Aries following the guide"
echo "5. Build and run experiments"
echo ""