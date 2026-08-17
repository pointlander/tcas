/-
  `eval` and `diff` as tree-calculus programs.

  Both are `Y2` fixpoints of a *dispatch* function. Dispatch is a
  `triage` that inspects the encoded expression *before* the recursor
  is applied, so eager `S` does not copy the recursor into unused
  constructor cases.

    teval ⬝ ⌜e⌝ ⬝ ⌜n⌝  →*  ⌜e(n)⌝
    tdiff ⬝ ⌜e⌝        →*  ⌜∂e/∂x⌝
-/

import Cas.Bracket
import Cas.Encode
import Cas.Expr

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

/-- `λrec x. 0` -/
private def evalK0 : Tm := P.lam "rec" (P.lam "x" Tm.node)

private def evalConst (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x" (P.unInt payload))

private def evalVar : Tm :=
  P.lam "rec" (P.lam "x" (P.v "x"))

private def evalAdd (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (P.onPair payload Tm.node fun a b =>
      P.q tplus ◃ ev a ◃ ev b))

private def evalMul (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (P.onPair payload Tm.node fun a b =>
      P.q ttimes ◃ ev a ◃ ev b))

private def evalPow (payload : Tm) : Tm :=
  P.lam "rec" (P.lam "x"
    (P.onPair payload Tm.node fun a b =>
      P.q tpow ◃ ev b ◃ ev a))

/-- `rest` is the tag with the first stem peeled off (ctor ≥ 1). -/
private def evalFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    evalVar
    (P.lam "t"
      (Tm.triage
        (evalAdd payload)
        (P.lam "t"
          (Tm.triage
            (evalMul payload)
            (P.lam "t"
              (Tm.triage
                (evalPow payload)
                (P.lam "_" evalK0)
                (P.lam "_" (P.lam "_" evalK0))
                (P.v "t")))
            (P.lam "_" (P.lam "_" evalK0))
            (P.v "t")))
        (P.lam "_" (P.lam "_" evalK0))
        (P.v "t")))
    (P.lam "_" (P.lam "_" evalK0))
    rest

private def evalFork : Tm :=
  P.lam "tag" (P.lam "payload"
    (Tm.triage
      (evalConst (P.v "payload"))
      (P.lam "rest" (evalFrom1 (P.v "rest") (P.v "payload")))
      (P.lam "_" (P.lam "_" evalK0))
      (P.v "tag")))

/-- Closed dispatch: leaf / stem / fork of an encoded expression. -/
def dispatchEval : Tm :=
  P.dispatch evalK0 (P.lam "_" evalK0) evalFork

def teval : Tree := Y2 (Tm.compile dispatchEval)

/-! ### `tdiff`

  Unary: `tdiff e = dispatchDiff e tdiff`, and each case is `λd. …`.
-/

private def dc (e : Tm) : Tm := P.v "d" ◃ e

/-- `λd. ⌜0⌝` -/
private def diffK0 : Tm := P.lam "d" P.const0

private def diffConst : Tm := P.lam "d" P.const0
private def diffVar : Tm := P.lam "d" P.const1

private def diffAdd (payload : Tm) : Tm :=
  P.lam "d"
    (P.onPair payload P.const0 fun a b =>
      P.mkAdd (dc a) (dc b))

private def diffMul (payload : Tm) : Tm :=
  P.lam "d"
    (P.onPair payload P.const0 fun a b =>
      P.mkAdd (P.mkMul (dc a) b) (P.mkMul a (dc b)))

private def nm1Expr : Tm :=
  P.mk 0 (Tm.node ◃ Tm.node ◃ (P.q tpred ◃ P.v "mag"))

/-- `(u^n)' = n · u^(n-1) · u'` for a non-negative constant `n`. -/
private def diffPow (payload : Tm) : Tm :=
  P.lam "d"
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
        w)

private def diffNeg (payload : Tm) : Tm :=
  P.lam "d" (P.mkNeg (dc payload))

private def diffInv (payload : Tm) : Tm :=
  P.lam "d"
    (P.mkNeg (P.mkMul (dc payload)
      (P.mkInv (P.mkPow payload P.const2))))

private def diffSin (payload : Tm) : Tm :=
  P.lam "d" (P.mkMul (P.mkCos payload) (dc payload))

private def diffCos (payload : Tm) : Tm :=
  P.lam "d" (P.mkNeg (P.mkMul (P.mkSin payload) (dc payload)))

private def diffExp (payload : Tm) : Tm :=
  P.lam "d" (P.mkMul (P.mkExp payload) (dc payload))

private def diffLn (payload : Tm) : Tm :=
  P.lam "d" (P.mkMul (dc payload) (P.mkInv payload))

/-- Peel stems of the tag, starting at ctor 1. -/
private def diffFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    diffVar
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
