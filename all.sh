#!/bin/bash
# Get the directory where all.sh is located
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"

# Run using the python inside the venv relative to this script
sudo "$SCRIPT_DIR/.venv/bin/python3" "$SCRIPT_DIR/aries-runners/aries-runner.py" \
     --config "$SCRIPT_DIR/aries-runners/config-aries.json"