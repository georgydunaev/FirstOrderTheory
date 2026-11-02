import os
import sys

_TESTS_DIR = os.path.dirname(os.path.abspath(__file__))
_REPO_DIR = os.path.dirname(_TESTS_DIR)
_WORKSPACE_DIR = os.path.dirname(_REPO_DIR)
for _p in (_TESTS_DIR, _REPO_DIR, _WORKSPACE_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)
