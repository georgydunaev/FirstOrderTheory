
type __ = Obj.t

type nat =
| O
| S of nat

type setVars = nat
  (* singleton inductive, whose constructor was Va *)

type terms = setVars
  (* singleton inductive, whose constructor was FVC *)

type atomFm =
| IN of terms * terms

type fm =
| Atom of atomFm
| Bot
| Conj of fm * fm
| Disj of fm * fm
| Impl of fm * fm
| Fora of setVars * fm
| Exis of setVars * fm

type pROCA =
| Ha1 of fm * fm
| Ha2 of fm * fm * fm
| Ha3 of fm * fm
| Ha4 of fm * fm
| Ha5 of fm * fm
| Ha6 of fm * fm
| Ha7 of fm * fm
| Ha8 of fm * fm * fm
| Ha9 of fm * fm
| Ha10 of fm * fm

type pRECA =
| PRO of fm * pROCA
| Ha12 of fm * terms * setVars * fm
| Ha13 of fm * terms * setVars * fm
| Hb1 of fm * fm * setVars
| Hb2 of fm * fm * setVars

type 'a inL = __

type pREPR =
| Hyp_E of fm * fm inL
| Hax_E of fm * pRECA
| MP_E of fm * fm * pREPR * pREPR
| GEN_E of fm * setVars * pREPR
