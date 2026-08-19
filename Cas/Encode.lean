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

/-- Three-way compare on unary nats: `△` = LT, `△ △` = EQ, `△ △ △` = GT. -/
def tcmp : Tree :=
  Y2 (star "m" (
    triage
      (star "cmp" (star "n" (
        triage (△ ⬝ △) (K ⬝ △) (K ⬝ (K ⬝ △)) ⬝ .ref "n")))
      (star "m1" (star "cmp" (star "n" (
        triage (△ ⬝ △ ⬝ △)
          (star "n1" (.ref "cmp" ⬝ .ref "m1" ⬝ .ref "n1"))
          (star "_" (star "_" (△ ⬝ △ ⬝ △)))
          ⬝ .ref "n"))))
      (star "_" (star "_" (star "cmp" (star "n" (△ ⬝ △)))))
      ⬝ .ref "m"))

/-- Saturating subtraction on unary nats: `minus 0 n = 0`, `minus m 0 = m`. -/
def tminus : Tree :=
  Y2 (star "m" (
    triage
      (star "minus" (star "n" △))
      (star "m1" (star "minus" (star "n" (
        triage (△ ⬝ .ref "m1")
          (star "n1" (.ref "minus" ⬝ .ref "m1" ⬝ .ref "n1"))
          (star "_" (star "_" △))
          ⬝ .ref "n"))))
      (star "_" (star "_" (star "minus" (star "n" △))))
      ⬝ .ref "m"))

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

/-- Lookup `name` in a list of pairs `△ ⟨name, val⟩ rest`. Missing → `△`. -/
def tlookup : Tree :=
  Y2 <| Tm.compile <|
    let q (t : Tree) : Tm := .embed t
    open Tm in
    lam "env" <|
      Tm.triage
        (lam "look" (lam "name" Tm.node))
        (lam "_" (lam "look" (lam "name" Tm.node)))
        (lam "pair" <| lam "rest" <| lam "look" <| lam "name" <|
          Tm.triage
            Tm.node
            (lam "_" Tm.node)
            (lam "n" <| lam "r" <|
              Tm.triage
                (v "look" ◃ v "rest" ◃ v "name")
                (lam "_" (v "r"))
                (lam "_" (lam "_" (v "look" ◃ v "rest" ◃ v "name")))
                (q tequal ◃ v "n" ◃ v "name"))
            (v "pair"))
        (v "env")

/-- `plus = Y2 (λm plus n. triage { n, λm₁. succ (plus m₁ n), λ_ _. n } m)` -/
def tplus : Tree :=
  Y2 (star "m" (star "plus" (star "n"
    (triage (.ref "n")
            (star "m1" (△ ⬝ (.ref "plus" ⬝ .ref "m1" ⬝ .ref "n")))
            (star "_" (star "_" (.ref "n")))
            ⬝ .ref "m"))))

@[inherit_doc tplus]
def tplusDirect : Tree := tplus

/--
  Size of a program (Jay).

  `Y2 (λx sz. triage {leaf, stem, fork} x)` with

    leaf:  1
    stem:  λx₁ sz. succ (sz x₁)
    fork:  λx₁ x₂ sz. succ (plus (sz x₁) (sz x₂))

  Dispatch on `x` happens before the recursor is applied.
-/
def tsize : Tree :=
  Y2 (star "x" (
    triage
      (star "sz" (△ ⬝ △))
      (star "x1" (star "sz" (△ ⬝ (.ref "sz" ⬝ .ref "x1"))))
      (star "x1" (star "x2" (star "sz" (
        △ ⬝ (tplus ⬝ (.ref "sz" ⬝ .ref "x1") ⬝ (.ref "sz" ⬝ .ref "x2"))))))
      ⬝ .ref "x"))

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

/-- Little-endian binary natural: `0 = △`, `2k = △ △ k`, `2k+1 = △ (△ △) k`.
    Canonical form has no trailing `0` bits (so `0` is a leaf, never `△ △ △`). -/
def ofBin (n : Nat) : Value :=
  if n = 0 then .leaf
  else if n % 2 = 0 then .fork .leaf (ofBin (n / 2))
  else .fork (.stem .leaf) (ofBin (n / 2))
termination_by n
decreasing_by
  all_goals
    refine Nat.div_lt_self ?_ (by decide)
    cases n with
    | zero => contradiction
    | succ _ => exact Nat.succ_pos _

def toBin? : Value → Option Nat
  | .leaf => some 0
  | .fork .leaf r => (toBin? r).map (· * 2)
  | .fork (.stem .leaf) r => (toBin? r).map (fun k => k * 2 + 1)
  | _ => none

theorem toBin_ofBin (n : Nat) : toBin? (ofBin n) = some n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      unfold ofBin
      split
      · next h0 =>
          subst h0
          simp [toBin?]
      · next h0 =>
          split
          · next hev =>
              have hlt : n / 2 < n :=
                Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
              simp [toBin?, ih (n / 2) hlt]
              have hmod : n % 2 = 0 := hev
              have := Nat.div_add_mod n 2
              simp [hmod] at this
              omega
          · next hod =>
              have hlt : n / 2 < n :=
                Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
              simp [toBin?, ih (n / 2) hlt]
              have hmod : n % 2 = 1 := by
                have : n % 2 < 2 := Nat.mod_lt n (by decide)
                omega
              have := Nat.div_add_mod n 2
              simp [hmod] at this
              omega

/-- Sign-magnitude integer. Magnitude is a binary nat (`ofBin`).
    Non-negative: `△ △ n`. Negative: `△ (△ △) n`. -/
def ofInt : Int → Value
  | .ofNat n   => .fork .leaf (ofBin n)
  | .negSucc n => .fork (.stem .leaf) (ofBin (n + 1))

def toInt? : Value → Option Int
  | .fork .leaf n =>
      (toBin? n).map (fun k => Int.ofNat k)
  | .fork (.stem .leaf) n =>
      match toBin? n with
      | some 0 => some 0
      | some k => some (Int.negOfNat k)
      | none   => none
  | _ => none

/-- Reduced rational `p/q` with `q > 0`. Stored as `△ ⌜p⌝ ⌜q⌝₂`.
    A zero denominator is mapped to `0/1`. -/
def ofRat (p : Int) (q : Nat) : Value :=
  if q = 0 then
    .fork (ofInt 0) (ofBin 1)
  else
    let g := Nat.gcd p.natAbs q
    let p' : Int :=
      match p with
      | .ofNat n   => .ofNat (n / g)
      | .negSucc n => Int.negOfNat ((n + 1) / g)
    .fork (ofInt p') (ofBin (q / g))

def toRat? : Value → Option (Int × Nat)
  | .fork num den =>
      match toInt? num, toBin? den with
      | some p, some q => if q = 0 then none else some (p, q)
      | _, _ => none
  | _ => none

def formatRat (p : Int) (q : Nat) : String :=
  if q = 1 then ToString.toString p else s!"{ToString.toString p}/{q}"

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
def encodeBin (n : Nat) : Tree := (Value.ofBin n).toTree
def encodeInt (i : Int) : Tree := (Value.ofInt i).toTree
def encodeRat (p : Int) (q : Nat) : Tree := (Value.ofRat p q).toTree
def encodeBool (b : Bool) : Tree := (Value.ofBool b).toTree

theorem ofBool_false : Value.ofBool false = .leaf := rfl
theorem ofBool_true  : Value.ofBool true  = .stem .leaf := rfl

end Cas
