/-
  Reduced rationals as tree programs.

  Encoding (`Value.ofRat p q`):

    p/q = △ ⌜p⌝ ⌜q⌝₂

  The numerator is a sign-magnitude integer (`ofInt`); the denominator
  is a positive binary nat (`ofBin`). Zero is `0/1`. Arithmetic
  programs leave fractions unreduced so `teval` can embed them;
  `tmkRat` cancels by `tbGcd` at the kernel boundary.
-/

import Cas.Encode
import Cas.Bin
import Cas.Int

namespace Cas

/-- `0/1`. -/
def trat0 : Tree := △ ⬝ tint0 ⬝ tbin1

/-- `1/1`. -/
def trat1 : Tree := △ ⬝ (△ ⬝ △ ⬝ tbin1) ⬝ tbin1

open Tm

private def q (t : Tree) : Tm := .embed t

/-- Pack `△ num den`, reducing by gcd. A zero denominator becomes `0/1`. -/
def tmkRat (_ : Unit := ()) : Tree :=
  Tm.compile <|
    lam "num" <| lam "den" <|
      let reduce : Tm :=
        let g : Tm := q (tbGcd ()) ◃ v "m" ◃ v "den"
        Tm.node
          ◃ (Tm.node ◃ v "s" ◃ (q (tbDiv ()) ◃ v "m" ◃ g))
          ◃ (q (tbDiv ()) ◃ v "den" ◃ g)
      let onMag : Tm :=
        Tm.triage (q trat0) (lam "_" (q trat0))
          (lam "_" (lam "_" reduce)) (v "m")
      let onNum : Tm :=
        Tm.triage (q trat0) (lam "_" (q trat0))
          (lam "s" (lam "m" onMag)) (v "num")
      Tm.triage (q trat0) (lam "_" (q trat0))
        (lam "_" (lam "_" onNum)) (v "den")

/-- Lift an `ofInt` to a (possibly unreduced) rational with denominator `1`. -/
def tintToRat : Tree :=
  star "z" (△ ⬝ .ref "z" ⬝ tbin1)

/-- Rational negation: flip the numerator's sign. -/
def trNeg : Tree :=
  star "r" (
    triage △ (K ⬝ △)
      (star "num" (star "den" (
        △ ⬝ (tiNeg ⬝ .ref "num") ⬝ .ref "den")))
      ⬝ .ref "r")

/-- Reciprocal. `1/0` is `0/1`. Does not reduce. -/
def trInv (_ : Unit := ()) : Tree :=
  Tm.compile <|
    lam "r" <|
      Tm.triage Tm.node (lam "_" Tm.node)
        (lam "num" <| lam "den" <|
          Tm.triage Tm.node (lam "_" Tm.node)
            (lam "s" <| lam "m" <|
              Tm.triage Tm.node (lam "_" Tm.node)
                (lam "_" (lam "_"
                  (Tm.node ◃ (Tm.node ◃ v "s" ◃ v "den") ◃ v "m")))
                (v "m"))
            (v "num"))
        (v "r")

/-- `+n` as an `ofInt`, from a binary magnitude. -/
private def tpos (m : Tm) : Tm := Tm.node ◃ Tm.node ◃ m

/-- Signed addition of two `ofRat` values. Does not reduce. -/
def trPlus (_ : Unit := ()) : Tree :=
  Tm.compile <|
    lam "a" <| lam "b" <|
      Tm.triage Tm.node (lam "_" Tm.node)
        (lam "n1" <| lam "d1" <|
          Tm.triage Tm.node (lam "_" Tm.node)
            (lam "n2" <| lam "d2" <|
              Tm.node
                ◃ (q tiPlus
                    ◃ (q tiTimes ◃ v "n1" ◃ tpos (v "d2"))
                    ◃ (q tiTimes ◃ v "n2" ◃ tpos (v "d1")))
                ◃ (q tbTimes ◃ v "d1" ◃ v "d2"))
            (v "b"))
        (v "a")

/-- Signed subtraction: `a − b = a + (−b)`. -/
def trMinus (_ : Unit := ()) : Tree :=
  star "a" (star "b" (trPlus () ⬝ .ref "a" ⬝ (trNeg ⬝ .ref "b")))

/-- Signed multiplication of two `ofRat` values. Does not reduce. -/
def trTimes (_ : Unit := ()) : Tree :=
  Tm.compile <|
    lam "a" <| lam "b" <|
      Tm.triage Tm.node (lam "_" Tm.node)
        (lam "n1" <| lam "d1" <|
          Tm.triage Tm.node (lam "_" Tm.node)
            (lam "n2" <| lam "d2" <|
              Tm.node
                ◃ (q tiTimes ◃ v "n1" ◃ v "n2")
                ◃ (q tbTimes ◃ v "d1" ◃ v "d2"))
            (v "b"))
        (v "a")

/-- Signed division: `a / b = a * (1/b)`. -/
def trDiv (_ : Unit := ()) : Tree :=
  star "a" (star "b" (trTimes () ⬝ .ref "a" ⬝ (trInv () ⬝ .ref "b")))

/-! ### Denotation -/

private theorem negOfNat_succ (n : Nat) : Int.negOfNat (n + 1) = .negSucc n := rfl

theorem toRat_ofRat (p : Int) (q : Nat) (hq : q ≠ 0)
    (hg : Nat.gcd p.natAbs q = 1) :
    Value.toRat? (Value.ofRat p q) = some (p, q) := by
  cases q with
  | zero => exact (hq rfl).elim
  | succ q =>
      have hg1 : Nat.gcd p.natAbs (q + 1) = 1 := hg
      unfold Value.ofRat
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      cases p with
      | ofNat n =>
          have hgcd : Nat.gcd n (q + 1) = 1 := by
            simpa [Int.natAbs] using hg1
          simp [hgcd, Value.toRat?, toInt_ofInt, Value.toBin_ofBin]
      | negSucc n =>
          have h1 : Nat.gcd (n + 1) (q + 1) = 1 := by
            simpa [Int.natAbs] using hg1
          simp [h1, Value.toRat?, toInt_ofInt, Value.toBin_ofBin, negOfNat_succ]

theorem toRat_ofRat_one (p : Int) :
    Value.toRat? (Value.ofRat p 1) = some (p, 1) := by
  have hg : Nat.gcd p.natAbs 1 = 1 := Nat.gcd_one_right p.natAbs
  exact toRat_ofRat p 1 (by decide) hg

def negRatV (v : Value) : Value :=
  match v.toRat? with
  | some (p, q) => Value.ofRat (-p) q
  | none => Value.ofRat 0 1

def invRatV (v : Value) : Value :=
  match v.toRat? with
  | some (0, _) => Value.ofRat 0 1
  | some (p, q) => Value.ofRat (if p < 0 then -Int.ofNat q else Int.ofNat q) p.natAbs
  | none => Value.ofRat 0 1

def plusRatV (a b : Value) : Value :=
  match a.toRat?, b.toRat? with
  | some (p, q), some (r, s) =>
      Value.ofRat (p * Int.ofNat s + r * Int.ofNat q) (q * s)
  | _, _ => Value.ofRat 0 1

def minusRatV (a b : Value) : Value :=
  match a.toRat?, b.toRat? with
  | some (p, q), some (r, s) =>
      Value.ofRat (p * Int.ofNat s - r * Int.ofNat q) (q * s)
  | _, _ => Value.ofRat 0 1

def mulRatV (a b : Value) : Value :=
  match a.toRat?, b.toRat? with
  | some (p, q), some (r, s) => Value.ofRat (p * r) (q * s)
  | _, _ => Value.ofRat 0 1

def divRatV (a b : Value) : Value :=
  mulRatV a (invRatV b)

theorem plusRatV_ofRat_one (a b : Int) :
    plusRatV (Value.ofRat a 1) (Value.ofRat b 1) = Value.ofRat (a + b) 1 := by
  simp [plusRatV, toRat_ofRat_one]

theorem mulRatV_ofRat_one (a b : Int) :
    mulRatV (Value.ofRat a 1) (Value.ofRat b 1) = Value.ofRat (a * b) 1 := by
  simp [mulRatV, toRat_ofRat_one]

theorem plusRatV_ofRat (a c : Int) (b d : Nat)
    (hb : b ≠ 0) (hd : d ≠ 0)
    (ha : Nat.gcd a.natAbs b = 1) (hc : Nat.gcd c.natAbs d = 1) :
    plusRatV (Value.ofRat a b) (Value.ofRat c d) =
      Value.ofRat (a * Int.ofNat d + c * Int.ofNat b) (b * d) := by
  simp [plusRatV, toRat_ofRat a b hb ha, toRat_ofRat c d hd hc]

theorem mulRatV_ofRat (a c : Int) (b d : Nat)
    (hb : b ≠ 0) (hd : d ≠ 0)
    (ha : Nat.gcd a.natAbs b = 1) (hc : Nat.gcd c.natAbs d = 1) :
    mulRatV (Value.ofRat a b) (Value.ofRat c d) =
      Value.ofRat (a * c) (b * d) := by
  simp [mulRatV, toRat_ofRat a b hb ha, toRat_ofRat c d hd hc]

theorem negRatV_ofRat (a : Int) (b : Nat) (hb : b ≠ 0)
    (ha : Nat.gcd a.natAbs b = 1) :
    negRatV (Value.ofRat a b) = Value.ofRat (-a) b := by
  simp [negRatV, toRat_ofRat a b hb ha]

theorem negRatV_ofRat_one (a : Int) :
    negRatV (Value.ofRat a 1) = Value.ofRat (-a) 1 :=
  negRatV_ofRat a 1 (by decide) (Nat.gcd_one_right _)

end Cas
