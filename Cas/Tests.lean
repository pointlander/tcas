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

#guard (eval! (tisLeaf ⬝ △)).toTree == ttrue
#guard (eval! (tisLeaf ⬝ (△ ⬝ △))).toTree == tfalse
#guard (eval! (tisStem ⬝ (△ ⬝ △))).toTree == ttrue
#guard (eval! (tisFork ⬝ (△ ⬝ △ ⬝ △))).toTree == ttrue

#guard Value.equalV .leaf .leaf
#guard !(Value.equalV .leaf (.stem .leaf))
#guard Value.equalV (Value.ofNat 4) (Value.ofNat 4)
#guard !(Value.equalV (Value.ofNat 4) (Value.ofNat 3))
#guard (eval! (△ ⬝ ofNat 3)).toNat? == some 4

#guard plusV (Value.ofNat 2) (Value.ofNat 3) == Value.ofNat 5
#guard mulV (Value.ofNat 3) (Value.ofNat 4) == Value.ofNat 12
#guard powV (Value.ofNat 2) (Value.ofNat 5) == Value.ofNat 32

/-! ### Pairs -/

#guard (eval! (tfirst ⬝ (tpair (ofNat 2) (ofNat 5)))).toNat? == some 2
#guard (eval! (tsecond ⬝ (tpair (ofNat 2) (ofNat 5)))).toNat? == some 5

/-! ### Intensional equality -/

#guard tequal.isProgram
#guard tequal.isClosed
#guard (eval! (tequal ⬝ △ ⬝ △)).toTree == ttrue
#guard (eval! (tequal ⬝ △ ⬝ (△ ⬝ △))).toTree == tfalse
#guard (eval! (tequal ⬝ K ⬝ K)).toTree == ttrue
#guard (eval! (tequal ⬝ K ⬝ I)).toTree == tfalse
#guard (eval! (tequal ⬝ I ⬝ I)).toTree == ttrue
#guard (eval! (tequal ⬝ ofNat 5 ⬝ ofNat 5)).toTree == ttrue
#guard (eval! (tequal ⬝ ofNat 5 ⬝ ofNat 4)).toTree == tfalse
#guard (eval! (tequal ⬝ (△ ⬝ ofNat 2 ⬝ ofNat 3) ⬝ (△ ⬝ ofNat 2 ⬝ ofNat 3))).toTree
        == ttrue
#guard (eval! (tequal ⬝ (△ ⬝ ofNat 2 ⬝ ofNat 3) ⬝ (△ ⬝ ofNat 2 ⬝ ofNat 4))).toTree
        == tfalse
#guard (match kernelEqual (Value.ofNat 7) (Value.ofNat 7) with
        | some b => b == true
        | none => false)

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

/-! ### Reduction tracer -/

#guard (match contract (K ⬝ ofNat 3) (ofNat 7) with
        | some (t, .k) => t == ofNat 3
        | _ => false)
#guard (match contract I △ with
        | some (_, .s) => true
        | _ => false)
#guard (match contract tnot tfalse with
        | some (t, .triageL) => t == ttrue
        | _ => false)
#guard (match contract tpred (ofNat 4) with
        | some (_, .triageS) => true
        | _ => false)

private def traceDone (t v : Tree) : Bool :=
  match runTrace t with
  | { status := .done, final := w, .. } => w == v
  | _ => false

#guard traceDone (K ⬝ ofNat 3 ⬝ ofNat 7) (ofNat 3)
#guard traceDone (I ⬝ △) △
#guard traceDone (S ⬝ K ⬝ K ⬝ △) △
#guard traceDone (tnot ⬝ tfalse) ttrue
#guard traceDone (tpred ⬝ ofNat 4) (ofNat 3)
#guard (runTrace (K ⬝ ofNat 3 ⬝ ofNat 7)).steps.map (·.rule) == [.k]
#guard (runTrace (I ⬝ △)).steps.map (·.rule) == [.s, .k]
#guard (Tree.pretty (K ⬝ ofNat 3 ⬝ ofNat 7) == "K 3 7")
#guard (match nf (S ⬝ K ⬝ K ⬝ ofNat 5), (runTrace (S ⬝ K ⬝ K ⬝ ofNat 5)).nf? with
        | some a, some b => a == b
        | _, _ => false)

/-! ### Compiled eval / diff programs (construction only; reduction is runtime) -/

#guard (eval! (Tm.compile (Tm.lam "x" (Tm.embed I ◃ Tm.v "x")) ⬝ △)).toTree == △
#guard teval.size > 0
#guard tdiff.size > 0

/-- Runtime checks for `teval` / `tdiff`. Returns `none` on success. -/
def programSelfTest : Option String :=
  let ev (s : String) (n : Nat) : Option Nat :=
    match parseExpr? s with
    | some e => kernelEvalExpr n e
    | none   => none
  let kd (s : String) : Option String :=
    match parseExpr? s with
    | some e =>
        match kernelDiffExpr e with
        | some d => some (Expr.simplify d).toString
        | none   => some "<diverged>"
    | none => some "<parse>"
  let expect (name : String) (got want : Option String) : Option String :=
    if got == want then none else some s!"{name}: got {got}, want {want}"
  let rec firstFail : List (Option String) → Option String
    | [] => none
    | none :: rest => firstFail rest
    | some m :: _ => some m
  firstFail
    [ if ev "2" 0 == some 2 then none else some "teval 2"
    , if ev "x" 5 == some 5 then none else some "teval x @ 5"
    , if ev "x+1" 4 == some 5 then none else some "teval x+1 @ 4"
    , if ev "2*x+1" 3 == some 7 then none else some "teval 2*x+1 @ 3"
    , if ev "x^2+1" 3 == some 10 then none else some "teval x^2+1 @ 3"
    , expect "tdiff 2" (kd "2") (some "0")
    , expect "tdiff x" (kd "x") (some "1")
    , expect "tdiff x+1" (kd "x+1") (some "1")
    , expect "tdiff x^2" (kd "x^2") (some "2 * x")
    , expect "tdiff sin(x)" (kd "sin(x)") (some "cos(x)")
    , expect "tdiff cos(x)" (kd "cos(x)") (some "-sin(x)")
    , expect "tdiff exp(x)" (kd "exp(x)") (some "exp(x)")
    , expect "tdiff ln(x)" (kd "ln(x)") (some "1 / x")
    , if ev "(x+1)*(x+2)" 3 == some 20 then none else some "teval (x+1)*(x+2) @ 3"
    , let eqv := eval! tequal
      if kernelEqual eqv eqv == some true then none else some "equal equal equal"
    , if kernelEqual (eval! tequal) (eval! tnot) == some false then none
      else some "equal equal not"
    ]

end Cas.Tests
