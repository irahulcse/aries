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