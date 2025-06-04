#!/bin/bash -e

if [ ! "$1" ]; then 
    echo "_run.sh <binary>"
    exit 1
fi
binary=$1
script_name=GetBasicBlocks

# Make projects directory if it does not exist
__projects_path="${GHIDRA_HOME}/ghidra_projects"
mkdir -p "${__projects_path}"

rm -f GetBasicBlocks_result.json

set +e
/ghidra/support/analyzeHeadless /ghidra/ghidra_projects ANewProject -readOnly \
    -postScript $script_name \
    -scriptPath "/ghidra_scripts" \
    -import $binary &> /tmp/log

if [ -f "GetBasicBlocks_result.json" ]; then
    cat "GetBasicBlocks_result.json"
else
    echo "++ ERROR:"
    cat /tmp/log
    exit 1
fi

