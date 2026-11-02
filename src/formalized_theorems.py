"""
Python mirror of Isabelle.v types, primitive terms (PT), and typing rules (PTT).
"""


def TVar(n: int):
    return ("TVar", int(n))


def TImp(a, b):
    return ("TImp", a, b)


TProp = ("TProp",)
TO = ("TO",)
TI = ("TI",)


class _TypesMeta(type):
    def __call__(cls, t):
        if not isinstance(t, tuple) or not t:
            return False
        tag = t[0]
        if tag == "TVar" and len(t) == 2 and isinstance(t[1], int):
            return True
        if tag == "TImp" and len(t) == 3:
            return cls(t[1]) and cls(t[2])
        return tag in ("TProp", "TO", "TI")


class Types(metaclass=_TypesMeta):
    TVar = staticmethod(TVar)
    TImp = staticmethod(TImp)
    TProp = TProp
    TO = TO
    TI = TI


def eqTypes(t1, t2) -> bool:
    return t1 == t2


def idsubst(n: int):
    return TVar(n)


def dosubst(subst, t):
    if not isinstance(t, tuple) or not t:
        return t
    tag = t[0]
    if tag == "TVar":
        return subst(t[1])
    if tag == "TImp":
        return TImp(dosubst(subst, t[1]), dosubst(subst, t[2]))
    return t


def addtotctx(g, n: int, tau):
    def updated(m: int):
        return tau if m == n else g(m)
    return updated


def EVar(n: int):
    return ("EVar", int(n))


def ECon(c, subst=None):
    return ("ECon", c, subst or idsubst)


def ELam(n: int, tau, body):
    return ("ELam", int(n), tau, body)


def EApp(t1, t2):
    return ("EApp", t1, t2)


def TypeOfTerm(ctx, term, sigma=None):
    if not isinstance(term, tuple) or not term:
        return None
    tag = term[0]
    if tag == "EVar":
        return ctx(term[1])
    if tag == "ECon":
        c = term[1]
        subst = term[2] if len(term) > 2 and term[2] is not None else idsubst
        base_ty = sigma(c) if sigma is not None else PTT(c)
        return dosubst(subst, base_ty)
    if tag == "ELam":
        _, x, tau, body = term
        body_ty = TypeOfTerm(addtotctx(ctx, x, tau), body, sigma)
        return TImp(tau, body_ty) if body_ty is not None else None
    if tag == "EApp":
        _, t1, t2 = term
        ty1 = TypeOfTerm(ctx, t1, sigma)
        ty2 = TypeOfTerm(ctx, t2, sigma)
        if ty1 is not None and ty1[0] == "TImp" and ty2 is not None and eqTypes(ty2, ty1[1]):
            return ty1[2]
        return None
    return None


LRA = "LRA"
BA = "BA"
TP = "TP"
Impl = "Impl"
Fora = "Fora"
EFalse = "EFalse"
Econj = "Econj"
Edisj = "Edisj"
Eimp = "Eimp"

_VALID_PTS = {LRA, BA, TP, Impl, Fora, EFalse, Econj, Edisj, Eimp}


def PT(p) -> bool:
    return p in _VALID_PTS


def PTT(p):
    mapping = {
        LRA: TImp(TProp, TImp(TProp, TProp)),
        BA: TImp(TImp(TVar(0), TProp), TProp),
        TP: TImp(TO, TProp),
        Impl: TImp(TO, TImp(TO, TO)),
        Fora: TImp(TImp(TI, TO), TO),
        EFalse: TO,
        Econj: TImp(TO, TImp(TO, TO)),
        Edisj: TImp(TO, TImp(TO, TO)),
        Eimp: TImp(TO, TImp(TO, TO)),
    }
    return mapping[p]


def some_function():
    return True
