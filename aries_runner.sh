#!/bin/bash

DOMAIN_DIR="/home/rahul/Desktop/aries/benchmarks/domains/ChildSnack"

# Run all problems in the domain
for problem in $DOMAIN_DIR/*.hddl; do
    echo "====== Solving $(basename $problem) ======"
    aries-plan "$problem"
    echo ""
done