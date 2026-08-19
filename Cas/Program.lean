/-
  `eval` and `diff` as tree-calculus programs.

  Both are `Y2` fixpoints of a *dispatch* function. Dispatch is a
  `triage` that inspects the encoded expression *before* the recursor
  is applied, so eager `S` does not copy the recursor into unused
  constructor cases.

    teval ⬝ ⌜e⌝ ⬝ ⌜n⌝  →*  ⌜e(n)⌝     (only the variable `x` is bound)
    tdiff ⬝ ⌜e⌝ ⬝ ⌜x⌝  →*  ⌜∂e/∂x⌝
-/

import Cas.Bracket
import Cas.Encode
import Cas.Bin
import Cas.Expr
import Cas.Int
import Cas.Rat

namespace Cas

namespace P

open Tm

def v : String → Tm := Tm.v
def lam : String → Tm → Tm := Tm.lam
def q (t : Tree) : Tm := .embed t

def tagT (n : Nat) : Tm := q (Expr.tag n).toTree

def mk (ctor : Nat) (payload : Tm) : Tm :=
  Tm.node ◃ tagT ctor ◃ payload

def mkBin (ctor : Nat) (a b : Tm) : Tm :=
  mk ctor (Tm.node ◃ a ◃ b)

def mkAdd (a b : Tm) : Tm := mkBin 2 a b
def mkMul (a b : Tm) : Tm := mkBin 3 a b
def mkPow (a b : Tm) : Tm := mkBin 4 a b
def mkNeg (a : Tm) : Tm := mk 5 a
def mkInv (a : Tm) : Tm := mk 6 a
def mkSin (a : Tm) : Tm := mk 7 a
def mkCos (a : Tm) : Tm := mk 8 a
def mkExp (a : Tm) : Tm := mk 9 a
def mkLn  (a : Tm) : Tm := mk 10 a

def const0 : Tm := q (Expr.encode (.const 0)).toTree
def const1 : Tm := q (Expr.encode (.const 1)).toTree
def const2 : Tm := q (Expr.encode (.const 2)).toTree

/-- Magnitude of a non-negative `ofInt`; otherwise `0`. -/
def unInt (payload : Tm) : Tm :=
  Tm.triage
    Tm.node
    (lam "_" Tm.node)
    (lam "sign" (lam "mag" (
      Tm.triage
        (v "mag")
        (lam "_" Tm.node)
        (lam "_" (lam "_" Tm.node))
        (v "sign"))))
    payload

/-- `payload` is `△ a b`; run `k a b`. Otherwise `dflt`. -/
def onPair (payload dflt : Tm) (k : Tm → Tm → Tm) : Tm :=
  Tm.triage
    dflt
    (lam "_" dflt)
    (lam "a" (lam "b" (k (v "a") (v "b"))))
    payload

/-- The dispatch operator itself: `△ (△ l s) f`. -/
def dispatch (l s f : Tm) : Tm :=
  Tm.node ◃ (Tm.node ◃ l ◃ s) ◃ f

end P

/-! ### `teval`

  `dispatchEval e` is a function `λrec x. …` for the constructor of `e`.
  `Y2` then feeds that function the recursor:

    teval e x = dispatchEval e teval x
-/

private def ev (e : Tm) : Tm := P.v "rec" ◃ e ◃ P.v "x"

/-- `λrec x. 0/1` -/
private def evalK0 : Tm := P.lam "rec" (P.lam "x" (P.q trat0))

/-- A constant is an `ofInt`; lift it to a rational with denominator `1`. -/
private def evalConst (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x" (P.q tintToRat ◃ payload))

/-- The input is a binary nat bound to the variable `x`; any other
    name is stuck (not a rational). -/
private def evalVar (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (Tm.triage
      Tm.node
      (P.lam "_" (P.q tintToRat ◃ (Tm.node ◃ Tm.node ◃ P.v "x")))
      (P.lam "_" (P.lam "_" Tm.node))
      (P.q tequal ◃ payload ◃ P.q (Expr.encodeString "x").toTree)))

/-- Non-numeric constructors (`sin`, `cos`, …) and unknown names. -/
private def evalStuck : Tm := P.lam "rec" (P.lam "x" Tm.node)

private def evalAdd (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (P.onPair payload (P.q trat0) fun a b =>
      P.q (trPlus ()) ◃ ev a ◃ ev b))

private def evalMul (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (P.onPair payload (P.q trat0) fun a b =>
      P.q (trTimes ()) ◃ ev a ◃ ev b))

/-- Magnitude of an `ofInt`; `0` if the value is not a fork. -/
private def magInt (z : Tm) : Tm :=
  Tm.triage Tm.node (P.lam "_" Tm.node)
    (P.lam "_" (P.lam "mmag" (P.v "mmag"))) z

/-- Sign bit of an `ofInt`; `+` if the value is not a fork. -/
private def signInt (z : Tm) : Tm :=
  Tm.triage Tm.node (P.lam "_" Tm.node)
    (P.lam "msign" (P.lam "_" (P.v "msign"))) z

/-- `va ^ bnum` when `va` is a rational and `bnum` is an `ofInt` exponent. -/
private def evalPowInt (va bnum : Tm) : Tm :=
  Tm.triage (P.q trat0) (P.lam "_" (P.q trat0))
    (P.lam "anum" (P.lam "aden"
      (let e : Tm := magInt bnum
       let s : Tm := signInt (P.v "anum")
       let m : Tm := magInt (P.v "anum")
       let s' : Tm :=
         Tm.triage s (P.lam "_" Tm.node)
           (P.lam "_" (P.lam "_" Tm.node))
           (P.q tbEven ◃ e)
       let r : Tm :=
         Tm.node
           ◃ (Tm.node ◃ s' ◃ (P.q tbPow ◃ e ◃ m))
           ◃ (P.q tbPow ◃ e ◃ P.v "aden")
       Tm.triage r (P.lam "_" (P.q (trInv ()) ◃ r))
         (P.lam "_" (P.lam "_" (P.q trat0)))
         (signInt bnum))))
    va

/-- Integer (or reciprocal) power of a rational; non-unit denominators on
    the exponent yield `0/1`. -/
private def evalPow (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (P.onPair payload (P.q trat0) fun a b =>
      Tm.triage (P.q trat0) (P.lam "_" (P.q trat0))
        (P.lam "bnum" (P.lam "bden"
          (Tm.triage (P.q trat0) (P.lam "_" (P.q trat0))
            (P.lam "dbit" (P.lam "drest"
              (Tm.triage
                (Tm.triage (P.q trat0)
                  (P.lam "_" (evalPowInt (ev a) (P.v "bnum")))
                  (P.lam "_" (P.lam "_" (P.q trat0)))
                  (P.v "dbit"))
                (P.lam "_" (P.q trat0))
                (P.lam "_" (P.lam "_" (P.q trat0)))
                (P.v "drest"))))
            (P.v "bden"))))
        (ev b)))

private def evalNeg (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x" (P.q trNeg ◃ ev payload))

private def evalInv (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x" (P.q (trInv ()) ◃ ev payload))

/-- `rest` is the tag with the first stem peeled off (ctor ≥ 1). -/
private def evalFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    (evalVar payload)
    (P.lam "t"
      (Tm.triage
        (evalAdd payload)
        (P.lam "t"
          (Tm.triage
            (evalMul payload)
            (P.lam "t"
              (Tm.triage
                (evalPow payload)
                (P.lam "t"
                  (Tm.triage
                    (evalNeg payload)
                    (P.lam "t"
                      (Tm.triage
                        (evalInv payload)
                        (P.lam "t"
                          (Tm.triage
                            evalStuck
                            (P.lam "t"
                              (Tm.triage
                                evalStuck
                                (P.lam "t"
                                  (Tm.triage
                                    evalStuck
                                    (P.lam "t"
                                      (Tm.triage
                                        evalStuck
                                        (P.lam "_" evalStuck)
                                        (P.lam "_" (P.lam "_" evalStuck))
                                        (P.v "t")))
                                    (P.lam "_" (P.lam "_" evalStuck))
                                    (P.v "t")))
                                (P.lam "_" (P.lam "_" evalStuck))
                                (P.v "t")))
                            (P.lam "_" (P.lam "_" evalStuck))
                            (P.v "t")))
                        (P.lam "_" (P.lam "_" evalStuck))
                        (P.v "t")))
                    (P.lam "_" (P.lam "_" evalStuck))
                    (P.v "t")))
                (P.lam "_" (P.lam "_" evalStuck))
                (P.v "t")))
            (P.lam "_" (P.lam "_" evalStuck))
            (P.v "t")))
        (P.lam "_" (P.lam "_" evalStuck))
        (P.v "t")))
    (P.lam "_" (P.lam "_" evalStuck))
    rest

private def evalFork (_ : Unit := ()) : Tm :=
  P.lam "tag" (P.lam "payload"
    (Tm.triage
      (evalConst (P.v "payload"))
      (P.lam "rest" (evalFrom1 (P.v "rest") (P.v "payload")))
      (P.lam "_" (P.lam "_" evalK0))
      (P.v "tag")))

/-- Closed dispatch: leaf / stem / fork of an encoded expression.
    A function so the embedded arithmetic programs are not built at init. -/
def dispatchEval (_ : Unit := ()) : Tm :=
  P.dispatch evalK0 (P.lam "_" evalK0) (evalFork ())

/-- Built on demand so module init does not construct the 70k-node tree. -/
def teval (_ : Unit := ()) : Tree := Y2 (Tm.compile (dispatchEval ()))

/-! ### `tdiff`

  `tdiff e v = dispatchDiff e tdiff v`. Each case is `λd name. …`.
  A variable differentiates to `1` iff its encoded name equals `name`.
-/

private def dc (e : Tm) : Tm := P.v "d" ◃ e ◃ P.v "v"

/-- `λd name. ⌜0⌝` -/
private def diffK0 : Tm := P.lam "d" (P.lam "v" P.const0)

private def diffConst : Tm := P.lam "d" (P.lam "v" P.const0)

private def diffVar (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v"
    (Tm.triage P.const0 (P.lam "_" P.const1) (P.lam "_" (P.lam "_" P.const0))
      (P.q tequal ◃ payload ◃ P.v "v")))

private def diffAdd (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v"
    (P.onPair payload P.const0 fun a b =>
      P.mkAdd (dc a) (dc b)))

private def diffMul (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v"
    (P.onPair payload P.const0 fun a b =>
      P.mkAdd (P.mkMul (dc a) b) (P.mkMul a (dc b))))

private def nm1Expr : Tm :=
  P.mk 0 (Tm.node ◃ Tm.node ◃ (P.q tbPred ◃ P.v "mag"))

/-- `(u^n)' = n · u^(n-1) · u'` for a non-negative constant `n`. -/
private def diffPow (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v"
    (P.onPair payload P.const0 fun u w =>
      Tm.triage
        P.const0
        (P.lam "_" P.const0)
        (P.lam "wTag" (P.lam "wPay"
          (Tm.triage
            (Tm.triage
              P.const0
              (P.lam "_" P.const0)
              (P.lam "sgn" (P.lam "mag"
                (P.mkMul (P.mkMul w (P.mkPow u nm1Expr)) (dc u))))
              (P.v "wPay"))
            -- non-constant exponent: u^w · (w'·ln u + w·u'/u)
            (P.lam "_"
              (P.mkMul (P.mkPow u w)
                (P.mkAdd
                  (P.mkMul (dc w) (P.mkLn u))
                  (P.mkMul w (P.mkMul (dc u) (P.mkInv u))))))
            (P.lam "_" (P.lam "_" P.const0))
            (P.v "wTag"))))
        w))

private def diffNeg (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v" (P.mkNeg (dc payload)))

private def diffInv (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v"
    (P.mkNeg (P.mkMul (dc payload)
      (P.mkInv (P.mkPow payload P.const2)))))

private def diffSin (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v" (P.mkMul (P.mkCos payload) (dc payload)))

private def diffCos (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v" (P.mkNeg (P.mkMul (P.mkSin payload) (dc payload))))

private def diffExp (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v" (P.mkMul (P.mkExp payload) (dc payload)))

private def diffLn (payload : Tm) : Tm :=
  P.lam "d" (P.lam "v" (P.mkMul (dc payload) (P.mkInv payload)))

/-- Peel stems of the tag, starting at ctor 1. -/
private def diffFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    (diffVar payload)
    (P.lam "t"
      (Tm.triage
        (diffAdd payload)
        (P.lam "t"
          (Tm.triage
            (diffMul payload)
            (P.lam "t"
              (Tm.triage
                (diffPow payload)
                (P.lam "t"
                  (Tm.triage
                    (diffNeg payload)
                    (P.lam "t"
                      (Tm.triage
                        (diffInv payload)
                        (P.lam "t"
                          (Tm.triage
                            (diffSin payload)
                            (P.lam "t"
                              (Tm.triage
                                (diffCos payload)
                                (P.lam "t"
                                  (Tm.triage
                                    (diffExp payload)
                                    (P.lam "t"
                                      (Tm.triage
                                        (diffLn payload)
                                        (P.lam "_" diffK0)
                                        (P.lam "_" (P.lam "_" diffK0))
                                        (P.v "t")))
                                    (P.lam "_" (P.lam "_" diffK0))
                                    (P.v "t")))
                                (P.lam "_" (P.lam "_" diffK0))
                                (P.v "t")))
                            (P.lam "_" (P.lam "_" diffK0))
                            (P.v "t")))
                        (P.lam "_" (P.lam "_" diffK0))
                        (P.v "t")))
                    (P.lam "_" (P.lam "_" diffK0))
                    (P.v "t")))
                (P.lam "_" (P.lam "_" diffK0))
                (P.v "t")))
            (P.lam "_" (P.lam "_" diffK0))
            (P.v "t")))
        (P.lam "_" (P.lam "_" diffK0))
        (P.v "t")))
    (P.lam "_" (P.lam "_" diffK0))
    rest

private def diffFork : Tm :=
  P.lam "tag" (P.lam "payload"
    (Tm.triage
      diffConst
      (P.lam "rest" (diffFrom1 (P.v "rest") (P.v "payload")))
      (P.lam "_" (P.lam "_" diffK0))
      (P.v "tag")))

def dispatchDiff : Tm :=
  P.dispatch diffK0 (P.lam "_" diffK0) diffFork

def tdiff : Tree := Y2 (Tm.compile dispatchDiff)

end Cas
