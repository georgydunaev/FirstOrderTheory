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
    os.path.join(ROOT, "OneFileIsabelle.v"),
    os.path.join(ROOT, "MembershipTests.v"),
    os.path.join(ROOT, "OneFileZFCTests.v"),
    os.path.join(ROOT, "logical_tautology.v"),
]


def main() -> int:
    has_coqc = shutil.which("coqc") is not None
    if not has_coqc:
        print("Error: coqc compiler not found in PATH")
        return 1

    failed = []
    for file in COQ_FILES:
        if not os.path.exists(file):
            print(f"Coq file not found: {file}")
            return 1
        print(f"Compiling Coq file: {os.path.basename(file)} ({os.path.getsize(file)} bytes)...")
        result = subprocess.run(
            ["coqc", "-Q", ROOT, "", file],
            capture_output=True,
            text=True,
            cwd=ROOT,
        )
        if result.returncode == 0:
            print(f"Successfully verified Coq file: {os.path.basename(file)}")
        else:
            print(f"Verification FAILED for: {os.path.basename(file)}")
            if result.stderr:
                print(result.stderr)
            failed.append(file)

    if failed:
        print(f"Error: {len(failed)} Coq file(s) failed verification.")
        return 1

    print("All Coq files compiled and verified cleanly.")
    print("Running Python test suite...")
    res = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s", os.path.join(ROOT, "tests"), "-p", "test_*.py"],
        cwd=ROOT,
    )
    return res.returncode


if __name__ == "__main__":
    sys.exit(main())
