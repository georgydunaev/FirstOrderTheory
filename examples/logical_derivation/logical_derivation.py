# Logical Derivation Example in Python
#
# Formal statement (first-order logic), over a canonical domain D:
#
#     ((forall x, P x /\ Q x  -->  R x)  /\  (exists x, P x /\ Q x))
#        -->  (exists x, R x)

P = lambda x: x % 6 == 0   # P(x): x is divisible by 6
Q = lambda x: x > 0        # Q(x): x is positive
R = lambda x: x % 3 == 0   # R(x): x is divisible by 3


def logical_derivation(p_fn=None, q_fn=None, r_fn=None, x_values=None):
    r"""Discharge ((forall x, P x /\ Q x --> R x) /\ (exists x, P x /\ Q x))
    --> (exists x, R x) over D = range(1, 100), or check existential witness over
    explicit (p_fn, q_fn, r_fn, x_values).
    """
    if p_fn is not None and q_fn is not None and r_fn is not None and x_values is not None:
        return any(p_fn(x) and q_fn(x) and r_fn(x) for x in x_values)

    domain = range(1, 100)
    for x in domain:
        if P(x) and Q(x) and not R(x):
            raise ValueError(
                f"Universal conditional violated at x={x}: "
                f"P({x}) and Q({x}) are true but R({x}) is false."
            )

    witness = next((x for x in domain if P(x) and Q(x)), None)
    if witness is None:
        return (False, None)

    assert R(witness), "Discharge failed: universal conditional not honoured."
    return (True, witness)


if __name__ == "__main__":
    concluded, witness = logical_derivation()
    if concluded:
        print(
            f"Derived (exists x, R x): witness x = {witness} "
            f"satisfies P ({P(witness)}), Q ({Q(witness)}), R ({R(witness)})."
        )
    else:
        print("No x in the domain satisfies P x and Q x; the premise is false.")
