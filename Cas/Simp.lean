/-
  One bottom-up rewrite pass as a tree program.

  `tsimp` is a `Y2` of a constructor dispatch, same shape as `tdiff`.
  Children are simplified first; then the node is rewritten by the
  ring / field identities that `Expr.rewrite` implements. `tdiff`
  results become readable by reduction (`2 * x^1 * 1` → `2 * x`).
-/

import Cas.Program
import Cas.Algebra
import Cas.Int

namespace Cas

open P

private def sc (e : Tm) : Tm := P.v "s" ◃ e

/-- `if cond then t else f`, with `true = △ △` and `false = △`. -/
private def iteT (cond t f : Tm) : Tm :=
  Tm.triage f (lam "_" t) (lam "_" (lam "_" f)) cond

private def andT (p r : Tm) : Tm := iteT p r (q tfalse)

/-- `tag` is `n` nested stems on a leaf. -/
private def isTag : Nat → Tm → Tm
  | 0, tag =>
      Tm.triage (q ttrue) (lam "_" (q tfalse)) (lam "_" (lam "_" (q tfalse))) tag
  | n + 1, tag =>
      Tm.triage (q tfalse) (lam "tg" (isTag n (v "tg")))
        (lam "_" (lam "_" (q tfalse))) tag

/-- `e` is `△ ⟨ctor n⟩ ⟨payload⟩`. -/
private def hasCtor (n : Nat) (e : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "ct" (lam "_" (isTag n (v "ct")))) e

private def pay (e : Tm) : Tm :=
  Tm.triage Tm.node (lam "_" Tm.node) (lam "_" (lam "py" (v "py"))) e

/-- `ofInt 0 = △ △ △`. -/
private def isZeroInt (z : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "sg" (lam "mg"
      (Tm.triage
        (Tm.triage (q ttrue) (lam "_" (q tfalse))
          (lam "_" (lam "_" (q tfalse))) (v "mg"))
        (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse)))
        (v "sg"))))
    z

/-- `ofBin 1 = △ (△ △) △`. -/
private def isBin1 (m : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "bit" (lam "rest"
      (Tm.triage
        (Tm.triage (q tfalse) (lam "_" (q ttrue))
          (lam "_" (lam "_" (q tfalse))) (v "bit"))
        (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse)))
        (v "rest"))))
    m

/-- `ofInt 1 = △ △ ⌜1⌝₂`. -/
private def isOneInt (z : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "sg" (lam "mg"
      (Tm.triage (isBin1 (v "mg")) (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse))) (v "sg"))))
    z

/-- `ofInt −1 = △ (△ △) ⌜1⌝₂`. -/
private def isNegOneInt (z : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "sg" (lam "mg"
      (Tm.triage (q tfalse) (lam "_" (isBin1 (v "mg")))
        (lam "_" (lam "_" (q tfalse))) (v "sg"))))
    z

private def isConst (e : Tm) : Tm := hasCtor 0 e

private def isConst0 (e : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "ct" (lam "cp"
      (Tm.triage (isZeroInt (v "cp")) (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse))) (v "ct"))))
    e

private def isConst1 (e : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "ct" (lam "cp"
      (Tm.triage (isOneInt (v "cp")) (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse))) (v "ct"))))
    e

private def isConstNeg1 (e : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "ct" (lam "cp"
      (Tm.triage (isNegOneInt (v "cp")) (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse))) (v "ct"))))
    e

private def eqT (a b : Tm) : Tm := q tequal ◃ a ◃ b

private def with2 (a b : Tm) (k : Tm → Tm → Tm) : Tm :=
  lam "lhs" (lam "rhs" (k (v "lhs") (v "rhs"))) ◃ a ◃ b

private def simpAddRules (a b : Tm) : Tm :=
  iteT (andT (isConst a) (isConst b))
    (mk 0 (q tiPlus ◃ pay a ◃ pay b))
    (iteT (isConst0 a) b
      (iteT (isConst0 b) a
        (iteT (andT (hasCtor 5 b) (eqT a (pay b))) const0
          (iteT (andT (hasCtor 5 a) (eqT (pay a) b)) const0
            (mkAdd a b)))))

private def simpMulRules (a b : Tm) : Tm :=
  iteT (andT (isConst a) (isConst b))
    (mk 0 (q tiTimes ◃ pay a ◃ pay b))
    (iteT (andT (isConst0 a) (q ttrue)) const0
      (iteT (isConst0 b) const0
        (iteT (isConst1 a) b
          (iteT (isConst1 b) a
            (iteT (isConstNeg1 a) (mkNeg b)
              (iteT (isConstNeg1 b) (mkNeg a)
                (iteT (andT (hasCtor 6 b) (eqT a (pay b))) const1
                  (iteT (andT (hasCtor 6 a) (eqT (pay a) b)) const1
                    (mkMul a b)))))))))

private def simpPowRules (a b : Tm) : Tm :=
  iteT (isConst0 b) const1
    (iteT (isConst1 b) a
      (iteT (isConst1 a) const1
        (mkPow a b)))

private def simpNegRules (a : Tm) : Tm :=
  iteT (isConst a) (mk 0 (q tiNeg ◃ pay a))
    (iteT (hasCtor 5 a) (pay a)
      (mkNeg a))

private def simpInvRules (a : Tm) : Tm :=
  iteT (isConst1 a) const1
    (iteT (isConstNeg1 a) (q (Expr.encode (.const (-1))).toTree)
      (iteT (hasCtor 6 a) (pay a)
        (mkInv a)))

private def simpExpRules (a : Tm) : Tm :=
  iteT (isConst0 a) const1 (mkExp a)

private def simpLnRules (a : Tm) : Tm :=
  iteT (isConst1 a) const0
    (iteT (hasCtor 9 a) (pay a)
      (mkLn a))

private def simpAdd (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    with2 (sc a) (sc b) simpAddRules)

private def simpMul (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    with2 (sc a) (sc b) simpMulRules)

private def simpPow (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    with2 (sc a) (sc b) simpPowRules)

private def simpNeg (payload : Tm) : Tm :=
  lam "s" (simpNegRules (sc payload))

private def simpInv (payload : Tm) : Tm :=
  lam "s" (simpInvRules (sc payload))

private def simpSin (payload : Tm) : Tm :=
  lam "s" (mkSin (sc payload))

private def simpCos (payload : Tm) : Tm :=
  lam "s" (mkCos (sc payload))

private def simpExp (payload : Tm) : Tm :=
  lam "s" (simpExpRules (sc payload))

private def simpLn (payload : Tm) : Tm :=
  lam "s" (simpLnRules (sc payload))

private def simpK0 : Tm := lam "s" const0
private def simpConst : Tm := lam "s" (mk 0 (v "payload"))
private def simpVar : Tm := lam "s" (mk 1 (v "payload"))

private def simpFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    simpVar
    (lam "t"
      (Tm.triage
        (simpAdd payload)
        (lam "t"
          (Tm.triage
            (simpMul payload)
            (lam "t"
              (Tm.triage
                (simpPow payload)
                (lam "t"
                  (Tm.triage
                    (simpNeg payload)
                    (lam "t"
                      (Tm.triage
                        (simpInv payload)
                        (lam "t"
                          (Tm.triage
                            (simpSin payload)
                            (lam "t"
                              (Tm.triage
                                (simpCos payload)
                                (lam "t"
                                  (Tm.triage
                                    (simpExp payload)
                                    (lam "t"
                                      (Tm.triage
                                        (simpLn payload)
                                        (lam "_" simpK0)
                                        (lam "_" (lam "_" simpK0))
                                        (v "t")))
                                    (lam "_" (lam "_" simpK0))
                                    (v "t")))
                                (lam "_" (lam "_" simpK0))
                                (v "t")))
                            (lam "_" (lam "_" simpK0))
                            (v "t")))
                        (lam "_" (lam "_" simpK0))
                        (v "t")))
                    (lam "_" (lam "_" simpK0))
                    (v "t")))
                (lam "_" (lam "_" simpK0))
                (v "t")))
            (lam "_" (lam "_" simpK0))
            (v "t")))
        (lam "_" (lam "_" simpK0))
        (v "t")))
    (lam "_" (lam "_" simpK0))
    rest

private def simpFork (_ : Unit := ()) : Tm :=
  lam "tag" (lam "payload"
    (Tm.triage
      simpConst
      (lam "rest" (simpFrom1 (v "rest") (v "payload")))
      (lam "_" (lam "_" simpK0))
      (v "tag")))

def dispatchSimp (_ : Unit := ()) : Tm :=
  dispatch simpK0 (lam "_" simpK0) (simpFork ())

/-- One bottom-up rewrite pass. Built on demand so module init stays small. -/
def tsimp (_ : Unit := ()) : Tree := Y2 (Tm.compile (dispatchSimp ()))

/-- Denotation of one `tsimp` pass: `encode (rewrite (decode e))`. -/
def simpV (e : Value) : Value :=
  match Expr.decode e with
  | some expr => Expr.encode (Expr.rewrite expr)
  | none => e

end Cas
