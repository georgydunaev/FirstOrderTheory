#!/usr/bin/env python3

import os
import subprocess

# List of Coq files to verify
coq_files = [
    "/botworkspace/FirstOrderTheory/OneFile.v",
    "/botworkspace/FirstOrderTheory/OneFileZFC.v",
    "/botworkspace/FirstOrderTheory/Isabelle.v",
    "/botworkspace/FirstOrderTheory/IsabelleAlt.v"
]

# Verify each Coq file
for file in coq_files:
    if os.path.exists(file):
        print(f"Verifying Coq file: {file}")
        result = subprocess.run(["coqc", file], capture_output=True, text=True)
        if result.returncode == 0:
            print(f"Successfully verified Coq file: {file}")
        else:
            print(f"Failed to verify Coq file: {file}")
            print(result.stderr)
    else:
        print(f"Coq file not found: {file}")
for file in coq_files:
    if os.path.exists(file):
        print(f"Found Coq file: {file}")
    else:
        print(f"Coq file not found: {file}")
