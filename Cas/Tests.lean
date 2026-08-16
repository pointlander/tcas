/-
  Compile-time checks. These run whenever the module is built.
-/

import Cas

namespace Cas.Tests

/-! ### Combinators -/

#guard (eval! (K ⬝ △ ⬝ (△ ⬝ △))).toTree == △
#guard (eval! (I ⬝ △)).toTree == △
#guard (eval! (I ⬝ (△ ⬝ △))).toTree == (△ ⬝ △)
#guard (eval! (S ⬝ K ⬝ K ⬝ △)).toTree == △
#guard (eval! (S ⬝ K ⬝ K ⬝ (△ ⬝ △))).toTree == (△ ⬝ △)

/-! ### Triage -/

#guard (eval! (triage (ofNat 1) (K ⬝ ofNat 2) (K ⬝ (K ⬝ ofNat 3)) ⬝ △)).toNat? == some 1
#guard (eval! (triage (ofNat 1) I (K ⬝ (K ⬝ ofNat 3)) ⬝ (△ ⬝ ofNat 7))).toNat? == some 7
#guard (eval! (triage (ofNat 1) I (star "u" (star "v" (.ref "u"))) ⬝ (△ ⬝ ofNat 4 ⬝ ofNat 5))).toNat?
        == some 4

/-! ### Booleans -/

#guard (eval! (tnot ⬝ tfalse)).toTree == ttrue
#guard (eval! (tnot ⬝ ttrue)).toTree == tfalse
#guard (eval! (tand ⬝ ttrue ⬝ tfalse)).toTree == tfalse
#guard (eval! (tand ⬝ ttrue ⬝ ttrue)).toTree == ttrue
#guard (eval! (tor ⬝ tfalse ⬝ ttrue)).toTree == ttrue
#guard (eval! (tor ⬝ tfalse ⬝ tfalse)).toTree == tfalse

/-! ### Nats: encode / decode / pred / succ -/

#guard (Value.ofNat 0).toNat? == some 0
#guard (Value.ofNat 5).toNat? == some 5
#guard (eval! (tpred ⬝ ofNat 0)).toNat? == some 0
#guard (eval! (tpred ⬝ ofNat 4)).toNat? == some 3
#guard (eval! (tisZero ⬝ ofNat 0)).toTree == ttrue
#guard (eval! (tisZero ⬝ ofNat 2)).toTree == tfalse
#guard (eval! (△ ⬝ ofNat 3)).toNat? == some 4

/-! ### Pairs -/

#guard (eval! (tfirst ⬝ (tpair (ofNat 2) (ofNat 5)))).toNat? == some 2
#guard (eval! (tsecond ⬝ (tpair (ofNat 2) (ofNat 5)))).toNat? == some 5

/-! ### Surface CAS -/

#guard (parseExpr? "2+3").isSome
#guard (match parseExpr? "2+3" with
        | some e => Expr.evalInt [] e == some 5
        | none => false)
#guard (match parseExpr? "2*x+1" with
        | some e => Expr.evalInt [("x", 3)] e == some 7
        | none => false)
#guard (match parseExpr? "(x+1)*(x-1)" with
        | some e =>
            let s := (Expr.normalize e).toString
            s == "x^2 - 1" || s == "x^2 + -1"
        | none => false)

#guard (Expr.diff "x" (.var "x") == .const 1)
#guard (Expr.diff "x" (.const 7) == .const 0)
#guard (Expr.dsimp "x" (Expr.pow (.var "x") (.const 2)) ==
          Expr.mul (.const 2) (.var "x") ||
        (Expr.dsimp "x" (Expr.pow (.var "x") (.const 2))).toString == "2 * x")

/-! ### Encode / decode expressions -/

private def roundTrip (e : Expr) : Bool :=
  match Expr.decode (Expr.encode e) with
  | some e' => e' == e
  | none    => false

#guard roundTrip (.const 0)
#guard roundTrip (.const (-3))
#guard roundTrip (.var "x")
#guard roundTrip (.var "foo")
#guard roundTrip (.add (.var "x") (.const 1))
#guard roundTrip (.mul (.sin (.var "x")) (.cos (.var "x")))

#guard (List.range 32).all (fun n => Expr.toNatBin? (Expr.ofNatBin n) == some n)

#guard (match parseExpr? "(x+1)*(x-1)" with
        | some e => (Expr.normalize e).toString == "x^2 - 1"
        | none => false)

/-! ### Parser of trees -/

#guard (match parseTree? "△ △" with | some t => t == K | none => false)
#guard (match parseTree? "I △" with
        | some t => (eval! t).toTree == △
        | none => false)
#guard (match parseTree? "K I △" with
        | some t => (eval! t).toTree == I
        | none => false)

end Cas.Tests
