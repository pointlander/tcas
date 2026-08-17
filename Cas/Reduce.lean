/-
  Small-step and evaluation semantics of triage calculus.

    (1)  △ △ y z             → y
    (2)  △ (△ x) y z         → x z (y z)
    (3a) △ (△ w x) y △       → w
    (3b) △ (△ w x) y (△ u)   → x u
    (3c) △ (△ w x) y (△ u v) → y u v

  Values are binary trees (leaf / stem / fork). Applying two values is
  the only computation step; it is confluent on overlapping-free rules.
-/

import Cas.Tree

namespace Cas

/-- Irreducible binary trees. These *are* the programs. -/
inductive Value where
  | leaf : Value
  | stem : Value → Value
  | fork : Value → Value → Value
  deriving BEq, Repr, Inhabited

namespace Value

def toTree : Value → Tree
  | .leaf     => △
  | .stem x   => △ ⬝ x.toTree
  | .fork x y => △ ⬝ x.toTree ⬝ y.toTree

def size : Value → Nat
  | .leaf     => 1
  | .stem x   => 1 + size x
  | .fork x y => 1 + size x + size y

/-- Unary natural numbers: `n` nested stems around a leaf. -/
def ofNat : Nat → Value
  | 0     => .leaf
  | n + 1 => .stem (ofNat n)

def toNat? : Value → Option Nat
  | .leaf   => some 0
  | .stem x => (toNat? x).map (· + 1)
  | .fork _ _ => none

instance : OfNat Value n where
  ofNat := ofNat n

def toString : Value → String
  | v => v.toTree.toString

instance : ToString Value := ⟨toString⟩

/--
  Apply `f` to `x` with a step budget. `none` means the budget was
  exhausted (possible divergence).
-/
def apply : Nat → Value → Value → Option Value
  | 0, _, _ => none
  | _fuel + 1, .leaf, y => some (.stem y)
  | _fuel + 1, .stem x, y => some (.fork x y)
  | _fuel + 1, .fork .leaf _y, _z =>
      -- rule 1: △ △ y z → y
      some _y
  | fuel + 1, .fork (.stem x) y, z =>
      -- rule 2: △ (△ x) y z → x z (y z)
      match apply fuel x z with
      | none => none
      | some xz =>
        match apply fuel y z with
        | none => none
        | some yz => apply fuel xz yz
  | fuel + 1, .fork (.fork w x) _y, z =>
      -- rule 3: triage on z
      match z with
      | .leaf     => some w
      | .stem u   => apply fuel x u
      | .fork u v =>
        match apply fuel _y u with
        | none => none
        | some yu => apply fuel yu v

def apply! (fuel : Nat) (f x : Value) : Value :=
  match apply fuel f x with
  | some v => v
  | none   => panic! "tree calculus: evaluation budget exhausted"

/-- Default budget large enough for the programs in this library. -/
def defaultFuel : Nat := 2_000_000

def app (f x : Value) : Option Value := apply defaultFuel f x

end Value

/-- Evaluate a closed term by reducing every application. -/
def eval : Nat → Tree → Option Value
  | _, △ => some .leaf
  | 0, .app _ _ => none
  | fuel + 1, f ⬝ a =>
      match eval fuel f, eval fuel a with
      | some fv, some av => Value.apply fuel fv av
      | _, _ => none
  | _, .ref _ => none

def eval! (t : Tree) (fuel : Nat := Value.defaultFuel) : Value :=
  match eval fuel t with
  | some v => v
  | none   => panic! "tree calculus: cannot evaluate (open term or diverged)"

def nf (t : Tree) (fuel : Nat := Value.defaultFuel) : Option Tree :=
  (eval fuel t).map Value.toTree

/-- Convert a value-encoding of a nat, or a tree that evaluates to one. -/
def evalNat (t : Tree) (fuel : Nat := Value.defaultFuel) : Option Nat :=
  match eval fuel t with
  | some v => v.toNat?
  | none   => none

/-! ### Kernel lemmas -/

theorem apply_leaf (fuel : Nat) (y : Value) :
    Value.apply (fuel + 1) .leaf y = some (.stem y) := rfl

theorem apply_stem (fuel : Nat) (x y : Value) :
    Value.apply (fuel + 1) (.stem x) y = some (.fork x y) := rfl

theorem apply_K (fuel : Nat) (y z : Value) :
    Value.apply (fuel + 1) (.fork .leaf y) z = some y := rfl

theorem apply_triage_leaf (fuel : Nat) (w x y : Value) :
    Value.apply (fuel + 1) (.fork (.fork w x) y) .leaf = some w := rfl

theorem apply_succ (n : Nat) :
    Value.ofNat (n + 1) = .stem (Value.ofNat n) := rfl

theorem toNat_ofNat (n : Nat) : (Value.ofNat n).toNat? = some n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Value.ofNat, Value.toNat?, ih]

theorem toTree_ofNat (n : Nat) : (Value.ofNat n).toTree = ofNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Value.ofNat, Value.toTree, ofNat, ih]

end Cas
