/-
  One bottom-up distribute pass as a tree program.

  `texpand` is a `Y2` of a constructor dispatch, same shape as `tsimp`.
  Children are expanded first; then a `mul` whose side is an `add`
  becomes a sum of products, and `neg` of an `add` splits. Iterate
  then `tsimp` so `(x+1)*(x-1)` reduces to `x * x - 1`.
-/

import Cas.Program
import Cas.Algebra

namespace Cas

open P

private def sc (e : Tm) : Tm := P.v "s" ◃ e

private def iteT (cond t f : Tm) : Tm :=
  Tm.triage f (lam "_" t) (lam "_" (lam "_" f)) cond

private def isTag : Nat → Tm → Tm
  | 0, tag =>
      Tm.triage (q ttrue) (lam "_" (q tfalse)) (lam "_" (lam "_" (q tfalse))) tag
  | n + 1, tag =>
      Tm.triage (q tfalse) (lam "tg" (isTag n (v "tg")))
        (lam "_" (lam "_" (q tfalse))) tag

private def hasCtor (n : Nat) (e : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "ct" (lam "_" (isTag n (v "ct")))) e

private def pay (e : Tm) : Tm :=
  Tm.triage Tm.node (lam "_" Tm.node) (lam "_" (lam "py" (v "py"))) e

private def with2 (a b : Tm) (k : Tm → Tm → Tm) : Tm :=
  lam "lhs" (lam "rhs" (k (v "lhs") (v "rhs"))) ◃ a ◃ b

/-- `(a+b)*c → a*c + b*c`, `a*(b+c) → a*b + a*c`,
    `(-a)*b → -(a*b)`, `a*(-b) → -(a*b)`. -/
private def expandMulRules (a b : Tm) : Tm :=
  iteT (hasCtor 2 a)
    (onPair (pay a) (mkMul a b) fun a1 a2 =>
      mkAdd (mkMul a1 b) (mkMul a2 b))
    (iteT (hasCtor 2 b)
      (onPair (pay b) (mkMul a b) fun b1 b2 =>
        mkAdd (mkMul a b1) (mkMul a b2))
      (iteT (hasCtor 5 a)
        (mkNeg (mkMul (pay a) b))
        (iteT (hasCtor 5 b)
          (mkNeg (mkMul a (pay b)))
          (mkMul a b))))

/-- `-(a+b) → (-a) + (-b)`. -/
private def expandNegRules (a : Tm) : Tm :=
  iteT (hasCtor 2 a)
    (onPair (pay a) (mkNeg a) fun a1 a2 =>
      mkAdd (mkNeg a1) (mkNeg a2))
    (mkNeg a)

private def expandAdd (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    mkAdd (sc a) (sc b))

private def expandMul (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    with2 (sc a) (sc b) expandMulRules)

private def expandPow (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    mkPow (sc a) (sc b))

private def expandNeg (payload : Tm) : Tm :=
  lam "s" (expandNegRules (sc payload))

private def expandInv (payload : Tm) : Tm :=
  lam "s" (mkInv (sc payload))

private def expandSin (payload : Tm) : Tm :=
  lam "s" (mkSin (sc payload))

private def expandCos (payload : Tm) : Tm :=
  lam "s" (mkCos (sc payload))

private def expandExp (payload : Tm) : Tm :=
  lam "s" (mkExp (sc payload))

private def expandLn (payload : Tm) : Tm :=
  lam "s" (mkLn (sc payload))

private def expandK0 : Tm := lam "s" const0
private def expandConst : Tm := lam "s" (mk 0 (v "payload"))
private def expandVar : Tm := lam "s" (mk 1 (v "payload"))

private def expandFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    expandVar
    (lam "t"
      (Tm.triage
        (expandAdd payload)
        (lam "t"
          (Tm.triage
            (expandMul payload)
            (lam "t"
              (Tm.triage
                (expandPow payload)
                (lam "t"
                  (Tm.triage
                    (expandNeg payload)
                    (lam "t"
                      (Tm.triage
                        (expandInv payload)
                        (lam "t"
                          (Tm.triage
                            (expandSin payload)
                            (lam "t"
                              (Tm.triage
                                (expandCos payload)
                                (lam "t"
                                  (Tm.triage
                                    (expandExp payload)
                                    (lam "t"
                                      (Tm.triage
                                        (expandLn payload)
                                        (lam "_" expandK0)
                                        (lam "_" (lam "_" expandK0))
                                        (v "t")))
                                    (lam "_" (lam "_" expandK0))
                                    (v "t")))
                                (lam "_" (lam "_" expandK0))
                                (v "t")))
                            (lam "_" (lam "_" expandK0))
                            (v "t")))
                        (lam "_" (lam "_" expandK0))
                        (v "t")))
                    (lam "_" (lam "_" expandK0))
                    (v "t")))
                (lam "_" (lam "_" expandK0))
                (v "t")))
            (lam "_" (lam "_" expandK0))
            (v "t")))
        (lam "_" (lam "_" expandK0))
        (v "t")))
    (lam "_" (lam "_" expandK0))
    rest

private def expandFork (_ : Unit := ()) : Tm :=
  lam "tag" (lam "payload"
    (Tm.triage
      expandConst
      (lam "rest" (expandFrom1 (v "rest") (v "payload")))
      (lam "_" (lam "_" expandK0))
      (v "tag")))

def dispatchExpand (_ : Unit := ()) : Tm :=
  dispatch expandK0 (lam "_" expandK0) (expandFork ())

/-- One bottom-up distribute pass. Built on demand so module init stays small. -/
def texpand (_ : Unit := ()) : Tree := Y2 (Tm.compile (dispatchExpand ()))

/-- One bottom-up distribute pass on the `Expr` AST; the denotation of `texpand`. -/
def expandOnce : Expr → Expr
  | .add a b => .add (expandOnce a) (expandOnce b)
  | .neg a =>
      match expandOnce a with
      | .add x y => .add (.neg x) (.neg y)
      | a => .neg a
  | .mul a b =>
      let a := expandOnce a
      let b := expandOnce b
      match a, b with
      | .add x y, _ => .add (.mul x b) (.mul y b)
      | _, .add x y => .add (.mul a x) (.mul a y)
      | .neg x, _ => .neg (.mul x b)
      | _, .neg y => .neg (.mul a y)
      | _, _ => .mul a b
  | .pow a b => .pow (expandOnce a) (expandOnce b)
  | .inv a => .inv (expandOnce a)
  | .sin a => .sin (expandOnce a)
  | .cos a => .cos (expandOnce a)
  | .exp a => .exp (expandOnce a)
  | .ln a => .ln (expandOnce a)
  | e@(.const _) | e@(.var _) => e

def expandV (e : Value) : Value :=
  match Expr.decode e with
  | some expr => Expr.encode (expandOnce expr)
  | none => e

end Cas
