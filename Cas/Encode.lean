/-
  Data encodings as binary trees, after Jay / treecalcul.us.

  Bool:   false = △, true = △ △
  Nat:    0 = △, n+1 = △ n          (stems)
  Pair:   ⟨a, b⟩ = △ a b            (the node *is* pairing)
  List:   [] = △, h :: t = △ h t
  Int:    fork of a sign bit and a nat
-/

import Cas.Tree
import Cas.Reduce
import Cas.Bracket

namespace Cas

/-! ### Booleans -/

def tfalse : Tree := △
def ttrue  : Tree := △ ⬝ △

def ofBool : Bool → Tree
  | false => tfalse
  | true  => ttrue

/-- `not = triage { true, λ_. false, λ_ _. false }`
    (only `false = △` and `true = △ △` are used). -/
def tnot : Tree :=
  triage ttrue (K ⬝ tfalse) (K ⬝ (K ⬝ tfalse))

/-- `and = triage { K false, λ_. I, λ_ _. K false }`
    so `and false = K false` and `and true = I`. -/
def tand : Tree :=
  triage (K ⬝ tfalse) (K ⬝ I) (K ⬝ (K ⬝ (K ⬝ tfalse)))

/-- `or = triage { I, λ_. K true, λ_ _. K true }`
    so `or false = I` and `or true = K true`. -/
def tor : Tree :=
  triage I (K ⬝ (K ⬝ ttrue)) (K ⬝ (K ⬝ (K ⬝ ttrue)))

/-! ### Pairs and lists -/

def tpair (a b : Tree) : Tree := △ ⬝ a ⬝ b

/-- `first = triage { △, λ_. △, λu v. u }` — on a fork return the left. -/
def tfirst : Tree :=
  triage △ (K ⬝ △) (star "u" (star "v" (.ref "u")))

/-- `second = triage { △, λ_. △, λu v. v }` -/
def tsecond : Tree :=
  triage △ (K ⬝ △) (star "u" (star "v" (.ref "v")))

def tnil : Tree := △
def tcons (h t : Tree) : Tree := △ ⬝ h ⬝ t

def thead : Tree := tfirst
def ttail : Tree := tsecond

/-! ### Naturals -/

def tzero : Tree := △
def tsucc : Tree := △   -- successor is the node itself

/-- `pred = triage { 0, I, λ_ _. 0 }` -/
def tpred : Tree :=
  triage tzero I (K ⬝ (K ⬝ tzero))

/-- `isZero = triage { true, λ_. false, λ_ _. false }` -/
def tisZero : Tree :=
  triage ttrue (K ⬝ tfalse) (K ⬝ (K ⬝ tfalse))

/-! ### Generic queries (intensional) -/

/-- `isLeaf = triage { true, λ_. false, λ_ _. false }` -/
def tisLeaf : Tree :=
  triage ttrue (K ⬝ tfalse) (K ⬝ (K ⬝ tfalse))

/-- `isStem = triage { false, λ_. true, λ_ _. false }` -/
def tisStem : Tree :=
  triage tfalse (K ⬝ ttrue) (K ⬝ (K ⬝ tfalse))

/-- `isFork = triage { false, λ_. false, λ_ _. true }` -/
def tisFork : Tree :=
  triage tfalse (K ⬝ tfalse) (K ⬝ (K ⬝ ttrue))

/--
  Intensional equality of programs (Jay).

  `Y2 (λx eq. triage {leaf, stem, fork} x)` then compares the second
  argument. Dispatch on `x` happens *before* the recursor is applied,
  so eager `S` does not copy `eq` into unused constructor cases.

    leaf:  triage { true, λ_. false, λ_ _. false }
    stem:  λx₁ eq. triage { false, eq x₁, λ_ _. false }
    fork:  λx₁ x₂ eq. triage { false, λ_. false,
                               λy₁ y₂. and (eq x₁ y₁) (eq x₂ y₂) }
-/
def tequal : Tree :=
  Y2 (star "x" (
    triage
      (star "eq" (triage ttrue (K ⬝ tfalse) (K ⬝ (K ⬝ tfalse))))
      (star "x1" (star "eq" (
        triage tfalse (.ref "eq" ⬝ .ref "x1") (K ⬝ (K ⬝ tfalse)))))
      (star "x1" (star "x2" (star "eq" (
        triage tfalse (K ⬝ tfalse)
          (star "y1" (star "y2"
            (tand ⬝ (.ref "eq" ⬝ .ref "x1" ⬝ .ref "y1")
                   ⬝ (.ref "eq" ⬝ .ref "x2" ⬝ .ref "y2"))))))))
      ⬝ .ref "x"))

/-- `plus = Y2 (λm plus n. triage { n, λm₁. succ (plus m₁ n), λ_ _. n } m)` -/
def tplus : Tree :=
  Y2 (star "m" (star "plus" (star "n"
    (triage (.ref "n")
            (star "m1" (△ ⬝ (.ref "plus" ⬝ .ref "m1" ⬝ .ref "n")))
            (star "_" (star "_" (.ref "n")))
            ⬝ .ref "m"))))

@[inherit_doc tplus]
def tplusDirect : Tree := tplus

/-- `times = Y2 (λn times m. triage { 0, λn₁. plus m (times n₁ m), λ_ _. 0 } n)` -/
def ttimes : Tree :=
  Y2 (star "n" (star "times" (star "m"
    (triage △
            (star "n1" (tplus ⬝ .ref "m" ⬝ (.ref "times" ⬝ .ref "n1" ⬝ .ref "m")))
            (star "_" (star "_" △))
            ⬝ .ref "n"))))

/-- `pow = Y2 (λe pow b. triage { 1, λe₁. times b (pow e₁ b), λ_ _. 1 } e)` -/
def tpow : Tree :=
  Y2 (star "e" (star "pow" (star "b"
    (triage (△ ⬝ △)
            (star "e1" (ttimes ⬝ .ref "b" ⬝ (.ref "pow" ⬝ .ref "e1" ⬝ .ref "b")))
            (star "_" (star "_" (△ ⬝ △)))
            ⬝ .ref "e"))))

/-! ### Value-level helpers -/

namespace Value

def ofBool : Bool → Value
  | false => .leaf
  | true  => .stem .leaf

def toBool? : Value → Option Bool
  | .leaf         => some false
  | .stem .leaf   => some true
  | _             => none

def pair (a b : Value) : Value := .fork a b

def first? : Value → Option Value
  | .fork a _ => some a
  | _         => none

def second? : Value → Option Value
  | .fork _ b => some b
  | _         => none

def ofList : List Value → Value
  | []      => .leaf
  | h :: t  => .fork h (ofList t)

partial def toList? : Value → Option (List Value)
  | .leaf     => some []
  | .fork h t =>
      match toList? t with
      | some ts => some (h :: ts)
      | none    => none
  | .stem _   => none

/-- Sign-magnitude integer. Non-negative: `△ 0 n`. Negative: `△ (△ △) n`. -/
def ofInt : Int → Value
  | .ofNat n   => .fork .leaf (ofNat n)
  | .negSucc n => .fork (.stem .leaf) (ofNat (n + 1))

def toInt? : Value → Option Int
  | .fork .leaf n =>
      (toNat? n).map (fun k => Int.ofNat k)
  | .fork (.stem .leaf) n =>
      match toNat? n with
      | some 0 => some 0
      | some k => some (Int.negOfNat k)
      | none   => none
  | _ => none

/-- Structural (intensional) equality of values. The denotation of `tequal`. -/
def equalV : Value → Value → Bool
  | .leaf, .leaf         => true
  | .stem x, .stem y     => equalV x y
  | .fork a b, .fork c d => equalV a c && equalV b d
  | _, _                 => false

theorem equalV_rfl (v : Value) : equalV v v = true := by
  induction v with
  | leaf => rfl
  | stem x ih => simpa [equalV] using ih
  | fork a b iha ihb => simp [equalV, iha, ihb]

theorem equalV_eq (a b : Value) : equalV a b = true ↔ a = b := by
  induction a generalizing b with
  | leaf =>
      cases b <;> simp [equalV]
  | stem x ih =>
      cases b with
      | leaf => simp [equalV]
      | stem y =>
          simp [equalV]
          exact ih y
      | fork _ _ => simp [equalV]
  | fork a1 a2 ih1 ih2 =>
      cases b with
      | leaf => simp [equalV]
      | stem _ => simp [equalV]
      | fork b1 b2 =>
          simp [equalV, Bool.and_eq_true, ih1 b1, ih2 b2]

end Value

def encodeNat (n : Nat) : Tree := (Value.ofNat n).toTree
def encodeInt (i : Int) : Tree := (Value.ofInt i).toTree
def encodeBool (b : Bool) : Tree := (Value.ofBool b).toTree

theorem ofBool_false : Value.ofBool false = .leaf := rfl
theorem ofBool_true  : Value.ofBool true  = .stem .leaf := rfl

end Cas
