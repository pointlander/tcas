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
#guard minusV (Value.ofNat 5) (Value.ofNat 3) == Value.ofNat 2
#guard minusV (Value.ofNat 3) (Value.ofNat 5) == Value.ofNat 0
#guard tminus.isProgram && tcmp.isProgram
#guard tiNeg.isProgram && tiPlus.isProgram
#guard tiMinus.isProgram && tiTimes.isProgram
#guard Value.toInt? (Value.ofInt 5) == some 5
#guard Value.toInt? (Value.ofInt (-3)) == some (-3)
#guard plusIntV (Value.ofInt 3) (Value.ofInt (-5)) == Value.ofInt (-2)
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

/-! ### Program size -/

#guard tsize.isProgram
#guard tsize.isClosed
#guard (eval! (tsize ⬝ △)).toNat? == some 1
#guard (eval! (tsize ⬝ K)).toNat? == some K.size
#guard (eval! (tsize ⬝ I)).toNat? == some I.size
#guard (eval! (tsize ⬝ S)).toNat? == some S.size
#guard (eval! (tsize ⬝ ofNat 5)).toNat? == some (ofNat 5).size
#guard (eval! (tsize ⬝ (△ ⬝ ofNat 2 ⬝ ofNat 3))).toNat?
        == some (△ ⬝ ofNat 2 ⬝ ofNat 3).size
#guard (match kernelSize (Value.ofNat 4) with
        | some n => n == (Value.ofNat 4).size
        | none => false)

/-! ### Binary nats -/

#guard (List.range 64).all (fun n => Value.toBin? (Value.ofBin n) == some n)
#guard succBinV (Value.ofBin 7) == Value.ofBin 8
#guard predBinV (Value.ofBin 8) == Value.ofBin 7
#guard plusBinV (Value.ofBin 13) (Value.ofBin 21) == Value.ofBin 34
#guard mulBinV (Value.ofBin 12) (Value.ofBin 13) == Value.ofBin 156
#guard powBinV (Value.ofBin 2) (Value.ofBin 8) == Value.ofBin 256
#guard tbSucc.isProgram && tbSucc.isClosed
#guard tbPred.isProgram && tbPlus.isProgram
#guard tbTimes.isProgram && tbPow.isProgram
#guard tbCmp.isProgram && tbMinus.isProgram
#guard minusBinV (Value.ofBin 5) (Value.ofBin 3) == Value.ofBin 2
#guard (tbDiv ()).isProgram && (tbMod ()).isProgram && (tbGcd ()).isProgram
#guard divBinV (Value.ofBin 10) (Value.ofBin 3) == Value.ofBin 3
#guard modBinV (Value.ofBin 10) (Value.ofBin 3) == Value.ofBin 1
#guard gcdBinV (Value.ofBin 12) (Value.ofBin 8) == Value.ofBin 4

/-! ### Rationals -/

#guard Value.toRat? (Value.ofRat 2 4) == some (1, 2)
#guard Value.toRat? (Value.ofRat (-6) 9) == some (-2, 3)
#guard Value.toRat? (Value.ofRat 0 7) == some (0, 1)
#guard Value.toRat? (Value.ofRat 5 1) == some (5, 1)
#guard plusRatV (Value.ofRat 1 2) (Value.ofRat 1 3) == Value.ofRat 5 6
#guard mulRatV (Value.ofRat 2 3) (Value.ofRat 3 4) == Value.ofRat 1 2
#guard invRatV (Value.ofRat 2 3) == Value.ofRat 3 2
#guard invRatV (Value.ofRat (-2) 3) == Value.ofRat (-3) 2
#guard (tmkRat ()).isProgram && (trPlus ()).isProgram && (trTimes ()).isProgram
#guard trNeg.isProgram && (trInv ()).isProgram && (trDiv ()).isProgram

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
#guard (teval ()).size > 0
#guard tdiff.size > 0

/-- Runtime checks for `teval` / `tdiff`. Returns `none` on success. -/
def programSelfTest (_ : Unit := ()) : Option String :=
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
    , if ev "x-1" 4 == some 3 then none else some "teval x-1 @ 4"
    , if kernelEvalInt 4 (parseExpr? "1-x" |>.getD (.const 0)) == some (-3)
      then none else some "teval 1-x @ 4"
    , if kernelEvalInt 0 (parseExpr? "-2" |>.getD (.const 0)) == some (-2)
      then none else some "teval -2"
    , if ev "2*x+1" 3 == some 7 then none else some "teval 2*x+1 @ 3"
    , if ev "x^2+1" 3 == some 10 then none else some "teval x^2+1 @ 3"
    , if kernelEvalRat 0 (parseExpr? "1/2" |>.getD (.const 0)) == some (1, 2)
      then none else some "teval 1/2"
    , if kernelEvalRat 0 (parseExpr? "1/2+1/3" |>.getD (.const 0)) == some (5, 6)
      then none else some "teval 1/2+1/3"
    , if kernelEvalRat 4 (parseExpr? "1/x" |>.getD (.const 0)) == some (1, 4)
      then none else some "teval 1/x @ 4"
    , if kernelEvalRat 3 (parseExpr? "(x-1)/(x+1)" |>.getD (.const 0)) == some (1, 2)
      then none else some "teval (x-1)/(x+1) @ 3"
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
    , match kernelSize (eval! tsize) with
      | some n =>
          if n == tsize.size then none
          else some s!"size size: got {n}, want {tsize.size}"
      | none => some "size size: diverged"
    , if kernelBinSucc (Value.ofBin 15) == some 16 then none else some "bin succ 15"
    , if kernelBinPred (Value.ofBin 16) == some 15 then none else some "bin pred 16"
    , if kernelBinPred (Value.ofBin 0) == some 0 then none else some "bin pred 0"
    , if kernelBinAdd (Value.ofBin 5) (Value.ofBin 7) == some 12 then none
      else some "bin 5+7"
    , if kernelBinAdd (Value.ofBin 13) (Value.ofBin 21) == some 34 then none
      else some "bin 13+21"
    , if kernelBinMul (Value.ofBin 6) (Value.ofBin 7) == some 42 then none
      else some "bin 6*7"
    , if kernelBinPow (Value.ofBin 2) (Value.ofBin 5) == some 32 then none
      else some "bin 2^5"
    , if kernelBinSub (Value.ofBin 10) (Value.ofBin 3) == some 7 then none
      else some "bin 10-3"
    , if kernelBinSub (Value.ofBin 3) (Value.ofBin 10) == some 0 then none
      else some "bin 3-10"
    , match kernelRAdd (Value.ofRat 1 2) (Value.ofRat 1 3) with
      | some v => if v.toRat? == some (5, 6) then none else some "rat 1/2+1/3"
      | none => some "rat 1/2+1/3: diverged"
    , match kernelRMul (Value.ofRat 2 3) (Value.ofRat 3 4) with
      | some v => if v.toRat? == some (1, 2) then none else some "rat 2/3*3/4"
      | none => some "rat 2/3*3/4: diverged"
    , match kernelRInv (Value.ofRat 2 3) with
      | some v => if v.toRat? == some (3, 2) then none else some "rat inv 2/3"
      | none => some "rat inv 2/3: diverged"
    , match kernelMinus (Value.ofNat 5) (Value.ofNat 3) with
      | some v => if v.toNat? == some 2 then none else some "minus 5 3"
      | none => some "minus 5 3: diverged"
    , match kernelIAdd (Value.ofInt 3) (Value.ofInt (-5)) with
      | some v => if v.toInt? == some (-2) then none else some "int 3+(-5)"
      | none => some "int 3+(-5): diverged"
    , match kernelISub (Value.ofInt 1) (Value.ofInt 4) with
      | some v => if v.toInt? == some (-3) then none else some "int 1-4"
      | none => some "int 1-4: diverged"
    ]

end Cas.Tests
