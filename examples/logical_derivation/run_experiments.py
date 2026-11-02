# Experiment runner for the first-order-logic example.
#
# Compiles and executes logical_derivation.py and prints an EPISTEMIC-01
# verdict (explicit premise--conclusion relationship).

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))


def main() -> int:
    import logical_derivation as ld

    print(f"Predicates over D = [1, 99]:")
    print(f"  P(x) == (x even)        -> e.g. P(2)={ld.P(2)}  P(3)={ld.P(3)}")
    print(f"  Q(x) == (x > 0)         -> e.g. Q(2)={ld.Q(2)}  Q(-1) not in D")
    print(f"  R(x) == (3 divides x)   -> e.g. R(6)={ld.R(6)}  R(4)={ld.R(4)}")
    print()

    try:
        concluded, witness = ld.logical_derivation()
    except ValueError as exc:
        print(f"UNPROVABLE: {exc}")
        return 2

    if concluded:
        print(f"PROVED: (exists x, R x) via P/witness x={witness}, "
              f"R({witness})={ld.R(witness)}.")
        return 0
    else:
        print("PREMISE FALSE: no x in D satisfies P x and Q x; "
              "conclusion not dispatched.")
        return 1


if __name__ == "__main__":
    sys.exit(main())