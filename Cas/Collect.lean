/-
  Like-term collection as a tree program.

  `tcollect` is a `Y2` of a constructor dispatch, same shape as `tsimp`.
  Children are collected first; then an `add` doubles equal summands,
  cancels `a + (-a)`, adds constants, and pulls a cancel through a
  left-associated sum. `collectOnce` is the Lean denotation (full
  flatten-and-merge).
-/

import Cas.Program
import Cas.Int

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

private def isConst0 (e : Tm) : Tm :=
  Tm.triage (q tfalse) (lam "_" (q tfalse))
    (lam "ct" (lam "cp"
      (Tm.triage (isZeroInt (v "cp")) (lam "_" (q tfalse))
        (lam "_" (lam "_" (q tfalse))) (v "ct"))))
    e

private def isConst (e : Tm) : Tm := hasCtor 0 e

private def onPairAs (na nb : String) (payload dflt : Tm) (k : Tm → Tm → Tm) : Tm :=
  Tm.triage dflt (lam "_" dflt)
    (lam na (lam nb (k (v na) (v nb))))
    payload

private def andT (p r : Tm) : Tm := iteT p r (q tfalse)

private def twice (a : Tm) : Tm :=
  mkMul (mk 0 (q (Value.ofInt 2).toTree)) a

/-- Merge like terms with `tequal`; cancel `a + (-a)`; double `a + a`. -/
private def collectAddRules (a b eq : Tm) : Tm :=
  iteT (eq ◃ a ◃ b)
    (twice a)
    (iteT (andT (hasCtor 5 b) (eq ◃ a ◃ pay b))
      const0
      (iteT (andT (hasCtor 5 a) (eq ◃ pay a ◃ b))
        const0
        (iteT (andT (isConst a) (isConst b))
          (mk 0 (q tiPlus ◃ pay a ◃ pay b))
          (iteT (hasCtor 2 a)
            (onPairAs "a1" "a2" (pay a) (mkAdd a b) fun a1 a2 =>
              iteT (eq ◃ a2 ◃ b)
                (iteT (isConst0 a1) (twice a2) (mkAdd a1 (twice a2)))
                (iteT (andT (hasCtor 5 b) (eq ◃ a2 ◃ pay b))
                  a1
                  (iteT (andT (hasCtor 5 a2) (eq ◃ pay a2 ◃ b))
                    a1
                    (mkAdd a1 (mkAdd a2 b)))))
            (mkAdd a b)))))

/-! ### `tcollect` -/

private def collectAdd (payload : Tm) : Tm :=
  lam "s" (
    lam "eq" (
      onPairAs "lhs" "rhs" payload const0 fun lhs rhs =>
        collectAddRules (sc lhs) (sc rhs) (v "eq")
    ) ◃ q tequal)

private def collectMul (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    mkMul (sc a) (sc b))

private def collectPow (payload : Tm) : Tm :=
  lam "s" (onPair payload const0 fun a b =>
    mkPow (sc a) (sc b))

private def collectNeg (payload : Tm) : Tm :=
  lam "s" (mkNeg (sc payload))

private def collectInv (payload : Tm) : Tm :=
  lam "s" (mkInv (sc payload))

private def collectSin (payload : Tm) : Tm :=
  lam "s" (mkSin (sc payload))

private def collectCos (payload : Tm) : Tm :=
  lam "s" (mkCos (sc payload))

private def collectExp (payload : Tm) : Tm :=
  lam "s" (mkExp (sc payload))

private def collectLn (payload : Tm) : Tm :=
  lam "s" (mkLn (sc payload))

private def collectK0 : Tm := lam "s" const0
private def collectConst : Tm := lam "s" (mk 0 (v "payload"))
private def collectVar : Tm := lam "s" (mk 1 (v "payload"))

private def collectFrom1 (rest payload : Tm) : Tm :=
  Tm.triage
    collectVar
    (lam "t"
      (Tm.triage
        (collectAdd payload)
        (lam "t"
          (Tm.triage
            (collectMul payload)
            (lam "t"
              (Tm.triage
                (collectPow payload)
                (lam "t"
                  (Tm.triage
                    (collectNeg payload)
                    (lam "t"
                      (Tm.triage
                        (collectInv payload)
                        (lam "t"
                          (Tm.triage
                            (collectSin payload)
                            (lam "t"
                              (Tm.triage
                                (collectCos payload)
                                (lam "t"
                                  (Tm.triage
                                    (collectExp payload)
                                    (lam "t"
                                      (Tm.triage
                                        (collectLn payload)
                                        (lam "_" collectK0)
                                        (lam "_" (lam "_" collectK0))
                                        (v "t")))
                                    (lam "_" (lam "_" collectK0))
                                    (v "t")))
                                (lam "_" (lam "_" collectK0))
                                (v "t")))
                            (lam "_" (lam "_" collectK0))
                            (v "t")))
                        (lam "_" (lam "_" collectK0))
                        (v "t")))
                    (lam "_" (lam "_" collectK0))
                    (v "t")))
                (lam "_" (lam "_" collectK0))
                (v "t")))
            (lam "_" (lam "_" collectK0))
            (v "t")))
        (lam "_" (lam "_" collectK0))
        (v "t")))
    (lam "_" (lam "_" collectK0))
    rest

private def collectFork (_ : Unit := ()) : Tm :=
  lam "tag" (lam "payload"
    (Tm.triage
      collectConst
      (lam "rest" (collectFrom1 (v "rest") (v "payload")))
      (lam "_" (lam "_" collectK0))
      (v "tag")))

def dispatchCollect (_ : Unit := ()) : Tm :=
  dispatch collectK0 (lam "_" collectK0) (collectFork ())

/-- One bottom-up collect pass. Built on demand so module init stays small. -/
def tcollect (_ : Unit := ()) : Tree := Y2 (Tm.compile (dispatchCollect ()))

/-! ### Denotation -/

/-- Peel a constant coefficient, leaving the power-product (or `1`). -/
def stripMono : Expr → Int × Expr
  | .const n => (n, .const 1)
  | .neg a =>
      let (c, b) := stripMono a
      (-c, b)
  | .mul (.const n) a =>
      let (c, b) := stripMono a
      (n * c, b)
  | .mul a (.const n) =>
      let (c, b) := stripMono a
      (n * c, b)
  | a => (1, a)

def rebuildMono (c : Int) (b : Expr) : Expr :=
  if c == 0 then .const 0
  else if b == .const 1 then .const c
  else if c == 1 then b
  else if c == -1 then .neg b
  else .mul (.const c) b

def isZeroExpr : Expr → Bool
  | .const 0 => true
  | _ => false

def insertTerm (t : Expr) : Expr → Expr
  | .add h rest =>
      if isZeroExpr t then .add h rest
      else
        let (c1, b1) := stripMono t
        let (c2, b2) := stripMono h
        if b1 == b2 then
          let t' := rebuildMono (c1 + c2) b1
          if isZeroExpr t' then rest
          else if isZeroExpr rest then t'
          else .add t' rest
        else .add h (insertTerm t rest)
  | p =>
      if isZeroExpr t then p
      else if isZeroExpr p then t
      else
        let (c1, b1) := stripMono t
        let (c2, b2) := stripMono p
        if b1 == b2 then rebuildMono (c1 + c2) b1
        else .add p t

def mergePoly : Expr → Expr → Expr
  | .add h rest, p => mergePoly rest (insertTerm h p)
  | t, p => insertTerm t p

def negPoly : Expr → Expr
  | .add a b => mergePoly (negPoly b) (negPoly a)
  | t =>
      let (c, b) := stripMono t
      rebuildMono (-c) b

/-- One bottom-up collect pass on the `Expr` AST; the denotation of `tcollect`. -/
def collectOnce : Expr → Expr
  | .add a b => mergePoly (collectOnce b) (collectOnce a)
  | .neg a => negPoly (collectOnce a)
  | .mul a b => .mul (collectOnce a) (collectOnce b)
  | .pow a b => .pow (collectOnce a) (collectOnce b)
  | .inv a => .inv (collectOnce a)
  | .sin a => .sin (collectOnce a)
  | .cos a => .cos (collectOnce a)
  | .exp a => .exp (collectOnce a)
  | .ln a => .ln (collectOnce a)
  | e@(.const _) | e@(.var _) => e

def collectV (e : Value) : Value :=
  match Expr.decode e with
  | some expr => Expr.encode (collectOnce expr)
  | none => e

end Cas
