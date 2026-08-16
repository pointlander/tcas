/-
  Bracket / star abstraction: compile a term with free variables into a
  combination. For triage-calculus rule 2 (`△ (△ x) y z → x z (y z)`):

    [x] (M N)  =  △ (△ [x]M) ([x]N)

  so that `([x] (M N)) P → ([x]M) P (([x]N) P)`.
-/

import Cas.Tree
import Cas.Reduce

namespace Cas

/-- Naive bracket abstraction. -/
def bracket (x : String) : Tree → Tree
  | △      => K ⬝ △
  | .ref y => if x == y then I else K ⬝ .ref y
  | f ⬝ a  => d (bracket x f) ⬝ bracket x a

/--
  Optimised abstraction (`star`). Uses the usual K / η / S cases.
  η is only an implementation of abstraction, not an equational axiom:
  tree calculus is intentionally not η-equivalent.
-/
def star (x : String) : Tree → Tree
  | △      => K ⬝ △
  | .ref y => if x == y then I else K ⬝ .ref y
  | f ⬝ a  =>
    if !(Tree.occurs x (f ⬝ a)) then
      K ⬝ (f ⬝ a)
    else
      match a with
      | .ref y =>
        if x == y then
          if Tree.occurs x f then d I ⬝ star x f
          else f
        else
          d (star x f) ⬝ (K ⬝ .ref y)
      | _ =>
        d (star x f) ⬝ star x a

notation:max "λ*" x:max ", " b:arg => star x b

/-- A tiny lambda language that compiles to trees. -/
inductive Tm where
  | v    : String → Tm
  | node : Tm
  | app  : Tm → Tm → Tm
  | lam  : String → Tm → Tm
  deriving Repr, Inhabited

namespace Tm

infixl:67 " ◃ " => Tm.app

def lamn : List String → Tm → Tm
  | [], b => b
  | x :: xs, b => .lam x (lamn xs b)

def compile : Tm → Tree
  | .v x     => .ref x
  | .node    => Tree.node
  | .app f a => compile f ⬝ compile a
  | .lam x b => star x (compile b)

/-- `triage l s f x` as a surface term. -/
def triage (l s f x : Tm) : Tm :=
  .node ◃ (.node ◃ l ◃ s) ◃ f ◃ x

end Tm

/-- First-class wait: `wait M N` is a program and `wait M N P → M N P`.

    `wait M N = S (S (K M) (K N)) I`
    `          = △ (△ (△ (△ (K M)) (K N))) I` -/
def wait (M N : Tree) : Tree :=
  △ ⬝ (△ ⬝ (△ ⬝ (△ ⬝ (K ⬝ M)) ⬝ (K ⬝ N))) ⬝ I

/-- `λx. x x` -/
def selfApply : Tree :=
  star "x" (.ref "x" ⬝ .ref "x")

/-- Call-by-value fixpoint: `Z f x → f (Z f) x`. -/
def Z (f : Tree) : Tree :=
  -- wait selfApply (λs. f (wait selfApply s))
  wait selfApply (star "s" (f ⬝ wait selfApply (.ref "s")))

/-- `swap f x y → f y x` -/
def swap (f : Tree) : Tree :=
  star "x" (star "y" (f ⬝ .ref "y" ⬝ .ref "x"))

/-- Two-argument fixpoint used by arithmetic and the kernel CAS:
    `Y2 f x → f x (Y2 f)`. -/
def Y2 (f : Tree) : Tree := Z (swap f)

end Cas
