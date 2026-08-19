/-
  Sign-magnitude integers as tree programs.

  Encoding (`Value.ofInt`):

    +n = △ △ n     (fork leaf mag)
    -n = △ (△ △) n (fork true mag)

  Magnitude is a binary nat (`ofBin`). Zero is always `+0`.
  `minus` on nats is saturating; signed plus subtracts magnitudes
  only when they differ in sign.
-/

import Cas.Encode
import Cas.Bin

namespace Cas

/-- `+0`. -/
def tint0 : Tree := △ ⬝ △ ⬝ △

/-- Flip a sign bit: `+ ↔ −`. -/
def tflipSign : Tree :=
  triage ttrue (K ⬝ tfalse) (K ⬝ (K ⬝ tfalse))

/-- Pack `△ s m`. Binary `0` is a leaf; any fork is a nonzero magnitude. -/
def tmkInt : Tree :=
  star "s" (star "m" (
    triage tint0
      (star "_" tint0)
      (star "_" (star "_" (△ ⬝ .ref "s" ⬝ .ref "m")))
      ⬝ .ref "m"))

/-- Integer negation. -/
def tiNeg : Tree :=
  star "z" (
    triage tint0 (K ⬝ tint0)
      (star "s" (star "m" (
        tmkInt ⬝ (tflipSign ⬝ .ref "s") ⬝ .ref "m")))
      ⬝ .ref "z")

open Tm

private def q (t : Tree) : Tm := .embed t

/-- Same-sign test on two sign bits. -/
private def sameSignTm (s1 s2 : Tm) : Tm :=
  Tm.triage
    (Tm.triage (q ttrue) (lam "_" (q tfalse)) (lam "_" (lam "_" (q tfalse))) s2)
    (lam "_"
      (Tm.triage (q tfalse) (lam "_" (q ttrue)) (lam "_" (lam "_" (q tfalse))) s2))
    (lam "_" (lam "_" (q tfalse)))
    s1

/-- Signed addition of two `ofInt` values. -/
def tiPlus : Tree :=
  Tm.compile <|
    lam "a" <| lam "b" <|
      Tm.triage (q tint0) (lam "_" (q tint0))
        (lam "s1" <| lam "m1" <|
          Tm.triage (q tint0) (lam "_" (q tint0))
            (lam "s2" <| lam "m2" <|
              Tm.triage
                -- `false = △` (leaf): different signs → subtract magnitudes
                (Tm.triage
                  (q tmkInt ◃ v "s2" ◃ (q tbMinus ◃ v "m2" ◃ v "m1"))
                  (lam "_" (q tint0))
                  (lam "_" (lam "_"
                    (q tmkInt ◃ v "s1" ◃ (q tbMinus ◃ v "m1" ◃ v "m2"))))
                  (q tbCmp ◃ v "m1" ◃ v "m2"))
                -- `true = △ △` (stem): same sign → add magnitudes
                (lam "_"
                  (q tmkInt ◃ v "s1" ◃ (q tbPlus ◃ v "m1" ◃ v "m2")))
                (lam "_" (lam "_" (q tint0)))
                (sameSignTm (v "s1") (v "s2")))
            (v "b"))
        (v "a")

/-- Signed subtraction: `a − b = a + (−b)`. -/
def tiMinus : Tree :=
  star "a" (star "b" (tiPlus ⬝ .ref "a" ⬝ (tiNeg ⬝ .ref "b")))

/-- XOR of two sign bits. -/
private def xorSignTm (s1 s2 : Tm) : Tm :=
  Tm.triage
    s2
    (lam "_" (q tflipSign ◃ s2))
    (lam "_" (lam "_" s2))
    s1

/-- Signed multiplication. -/
def tiTimes : Tree :=
  Tm.compile <|
    lam "a" <| lam "b" <|
      Tm.triage (q tint0) (lam "_" (q tint0))
        (lam "s1" <| lam "m1" <|
          Tm.triage (q tint0) (lam "_" (q tint0))
            (lam "s2" <| lam "m2" <|
              q tmkInt ◃ xorSignTm (v "s1") (v "s2") ◃
                (q tbTimes ◃ v "m1" ◃ v "m2"))
            (v "b"))
        (v "a")

/-! ### Denotation -/

theorem toInt_ofInt (i : Int) : Value.toInt? (Value.ofInt i) = some i := by
  cases i with
  | ofNat n =>
      simp [Value.ofInt, Value.toInt?, Value.toBin_ofBin]
  | negSucc n =>
      simp [Value.ofInt, Value.toInt?, Value.toBin_ofBin]
      cases n <;> rfl

theorem ofInt_inj {i j : Int} (h : Value.ofInt i = Value.ofInt j) : i = j := by
  have := congrArg Value.toInt? h
  simp [toInt_ofInt] at this
  exact this

def negIntV (v : Value) : Value :=
  match v.toInt? with
  | some i => Value.ofInt (-i)
  | none => Value.ofInt 0

def plusIntV (a b : Value) : Value :=
  match a.toInt?, b.toInt? with
  | some i, some j => Value.ofInt (i + j)
  | _, _ => Value.ofInt 0

def minusIntV (a b : Value) : Value :=
  match a.toInt?, b.toInt? with
  | some i, some j => Value.ofInt (i - j)
  | _, _ => Value.ofInt 0

def mulIntV (a b : Value) : Value :=
  match a.toInt?, b.toInt? with
  | some i, some j => Value.ofInt (i * j)
  | _, _ => Value.ofInt 0

theorem plusIntV_ofInt (a b : Int) :
    plusIntV (Value.ofInt a) (Value.ofInt b) = Value.ofInt (a + b) := by
  simp [plusIntV, toInt_ofInt]

theorem minusIntV_ofInt (a b : Int) :
    minusIntV (Value.ofInt a) (Value.ofInt b) = Value.ofInt (a - b) := by
  simp [minusIntV, toInt_ofInt]

theorem mulIntV_ofInt (a b : Int) :
    mulIntV (Value.ofInt a) (Value.ofInt b) = Value.ofInt (a * b) := by
  simp [mulIntV, toInt_ofInt]

theorem negIntV_ofInt (a : Int) :
    negIntV (Value.ofInt a) = Value.ofInt (-a) := by
  simp [negIntV, toInt_ofInt]

end Cas
