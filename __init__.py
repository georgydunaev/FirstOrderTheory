import os
import sys

_PKG_DIR = os.path.dirname(os.path.abspath(__file__))
_PARENT_DIR = os.path.dirname(_PKG_DIR)
for _p in (_PKG_DIR, _PARENT_DIR):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from main import FirstOrderTheory
from cognition import Terms, Terms_ind, FVC, FSC, FSV, Vector, term_substitution, flash_search
import cognition
import main
import OneFile
import OneFileZFC
import Isabelle
