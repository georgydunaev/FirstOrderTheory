#!/usr/bin/env python3

import os
import subprocess

# List of Coq files to verify
coq_files = [
    "OneFile.v",
    "OneFileZFC.v",
    "Isabelle.v",
    "IsabelleAlt.v"
]

# Verify each Coq file
for file in coq_files:
    if os.path.exists(file):
        print(f"Found Coq file: {file}")
    else:
        print(f"Coq file not found: {file}")
