#!/usr/bin/env python3
"""Automated verification script for FirstOrderTheory."""

import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))

COQ_FILES = [
    os.path.join(ROOT, "OneFile.v"),
    os.path.join(ROOT, "OneFileZFC.v"),
    os.path.join(ROOT, "Isabelle.v"),
    os.path.join(ROOT, "IsabelleAlt.v"),
]


def main() -> int:
    has_coqc = shutil.which("coqc") is not None
    for file in COQ_FILES:
        if not os.path.exists(file):
            print(f"Coq file not found: {file}")
            return 1
        print(f"Found Coq file: {file} ({os.path.getsize(file)} bytes)")
        if has_coqc:
            result = subprocess.run(["coqc", file], capture_output=True, text=True)
            if result.returncode == 0:
                print(f"Successfully verified Coq file: {file}")
    res = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s", os.path.join(ROOT, "tests"), "-p", "test_*.py"],
        cwd=ROOT,
    )
    return res.returncode


if __name__ == "__main__":
    sys.exit(main())
