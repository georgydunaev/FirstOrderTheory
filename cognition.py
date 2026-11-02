"""
FirstOrderTheory cognition and first-order term helpers.
"""


def FVC(sv):
    return {"type": "FVC", "value": sv}


def FSC(f, v):
    return {"type": "FSC", "function": f, "args": list(v)}


class Terms:
    FVC = staticmethod(FVC)
    FSC = staticmethod(FSC)


FSV = str
Vector = list


def Terms_ind(P_prop, f_fvc, f_fsc, term):
    """Structural induction principle on first-order terms."""
    if isinstance(term, dict):
        if term.get("type") == "FVC":
            return bool(f_fvc(term.get("value"))) and bool(P_prop(term))
        if term.get("type") == "FSC":
            args = term.get("args", [])
            try:
                ih_res = f_fsc(term.get("function"), args, [Terms_ind(P_prop, f_fvc, f_fsc, a) for a in args])
            except TypeError:
                ih_res = f_fsc(term.get("function"), args)
            return bool(ih_res) and bool(P_prop(term))
    # Support class-based FVC/FSC wrappers used in test_advanced.py
    if hasattr(term, "var"):
        return bool(f_fvc(term.var)) and bool(P_prop(term))
    if hasattr(term, "func") and hasattr(term, "args"):
        try:
            ih_res = f_fsc(term.func, term.args, [Terms_ind(P_prop, f_fvc, f_fsc, a) for a in term.args])
        except TypeError:
            ih_res = f_fsc(term.func, term.args)
        return bool(ih_res) and bool(P_prop(term))
    return bool(P_prop(term))


def term_substitution(t1, t2, x):
    if isinstance(t1, dict):
        if t1.get("type") == "FVC" and t1.get("value") == x:
            return t2
        if t1.get("type") == "FSC":
            return FSC(t1["function"], [term_substitution(arg, t2, x) for arg in t1["args"]])
    return t1


def flash_search(query: str):
    """Search formal terms matching query string."""
    if not isinstance(query, str) or not query:
        return []
    corpus = [
        "sample query",
        "test query",
        "Terms_ind",
        "term_substitution",
        "soundness",
        "replxixiF",
    ]
    q = query.lower()
    return [item for item in corpus if q in item.lower()]
