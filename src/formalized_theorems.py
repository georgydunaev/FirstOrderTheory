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
