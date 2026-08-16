/-
  Tree calculus terms (triage calculus, treecalcul.us).

  Grammar:  t ::= △ | t t | x
  Application is left-associative. Closed irreducible terms are binary trees:
  a *leaf* △, a *stem* △ a, or a *fork* △ a b.
-/

namespace Cas

inductive Tree where
  | node : Tree
  | app  : Tree → Tree → Tree
  | ref  : String → Tree
  deriving BEq, Repr, Inhabited

/-- The single operator △. -/
notation "△" => Tree.node

/-- Left-associative application. -/
infixl:65 " ⬝ " => Tree.app

namespace Tree

def size : Tree → Nat
  | △      => 1
  | f ⬝ a  => size f + size a
  | .ref _ => 1

def occurs (x : String) : Tree → Bool
  | △      => false
  | f ⬝ a  => occurs x f || occurs x a
  | .ref y => x == y

def substitute (x : String) (n : Tree) : Tree → Tree
  | △      => △
  | f ⬝ a  => substitute x n f ⬝ substitute x n a
  | .ref y => if x == y then n else .ref y

/-- A *program* (value) is a closed binary tree: leaf, stem, or fork. -/
def isProgram : Tree → Bool
  | △          => true
  | △ ⬝ a      => isProgram a
  | △ ⬝ a ⬝ b  => isProgram a && isProgram b
  | _          => false

/-- Closed combination: no free variables. -/
def isClosed : Tree → Bool
  | △      => true
  | f ⬝ a  => isClosed f && isClosed a
  | .ref _ => false

/-- Pretty-print with the fewest parentheses, assuming left-associative `⬝`. -/
def toString : Tree → String
  | △      => "△"
  | .ref x => x
  | f ⬝ a  =>
    let fs := toString f
    match a with
    | _ ⬝ _ => s!"{fs} ({toString a})"
    | _     => s!"{fs} {toString a}"

instance : ToString Tree := ⟨toString⟩

/-- Right-nested applications need parens; atoms do not. -/
def needsParens : Tree → Bool
  | _ ⬝ _ => true
  | _     => false

end Tree

/-- Combinators that do not depend on abstraction. -/
def K : Tree := △ ⬝ △

/-- `S x = △ (△ x)`, so `S = λx. △ (△ x) = △ (△ (K △)) △`. -/
def S : Tree := △ ⬝ (△ ⬝ (K ⬝ △)) ⬝ △

/-- `I = S K K`. -/
def I : Tree := △ ⬝ (△ ⬝ K) ⬝ K

/-- `d x = △ (△ x)`. Then `d x y z → x z (y z)` (rule 2). -/
def d (x : Tree) : Tree := △ ⬝ (△ ⬝ x)

/-- `triage l s f = △ (△ l s) f`. Cases on a *value*:
    leaf ↦ l, stem u ↦ s u, fork u v ↦ f u v. -/
def triage (l s f : Tree) : Tree := △ ⬝ (△ ⬝ l ⬝ s) ⬝ f

/-- Unary natural: `0 = △`, `n+1 = △ n` (a stem). Successor *is* △. -/
def ofNat : Nat → Tree
  | 0     => △
  | n + 1 => △ ⬝ ofNat n

instance : OfNat Tree n where
  ofNat := ofNat n

end Cas
