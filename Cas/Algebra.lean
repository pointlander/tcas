/-
  Evaluation, substitution, expansion, and algebraic simplification.
-/

import Cas.Expr

namespace Cas

namespace Expr

def lookup (x : String) : Env → Option Int
  | [] => none
  | (y, v) :: rest => if x == y then some v else lookup x rest

def lookupF (x : String) : FEnv → Option Float
  | [] => none
  | (y, v) :: rest => if x == y then some v else lookupF x rest

def intPow (b : Int) (e : Nat) : Int :=
  match e with
  | 0     => 1
  | n + 1 => b * intPow b n

/-- Evaluate in `ℤ` when the expression is a closed integer combination. -/
def evalInt (env : Env) : Expr → Option Int
  | const n => some n
  | var v   => lookup v env
  | add a b =>
      match evalInt env a, evalInt env b with
      | some x, some y => some (x + y)
      | _, _ => none
  | mul a b =>
      match evalInt env a, evalInt env b with
      | some x, some y => some (x * y)
      | _, _ => none
  | pow a b =>
      match evalInt env a, evalInt env b with
      | some x, some y =>
          if y ≥ 0 then some (intPow x y.toNat) else none
      | _, _ => none
  | neg a => (evalInt env a).map (fun x => -x)
  | inv a =>
      match evalInt env a with
      | some 1  => some 1
      | some (-1) => some (-1)
      | _ => none
  | sin _ | cos _ | exp _ | ln _ => none

/-- Floating-point evaluation (used by the CLI). -/
def evalFloat (env : FEnv) : Expr → Option Float
  | const n => some (Float.ofInt n)
  | var v   => lookupF v env
  | add a b =>
      match evalFloat env a, evalFloat env b with
      | some x, some y => some (x + y)
      | _, _ => none
  | mul a b =>
      match evalFloat env a, evalFloat env b with
      | some x, some y => some (x * y)
      | _, _ => none
  | pow a b =>
      match evalFloat env a, evalFloat env b with
      | some x, some y => some (x.pow y)
      | _, _ => none
  | neg a => (evalFloat env a).map (fun x => -x)
  | inv a =>
      match evalFloat env a with
      | some x =>
          if x == 0 then none else some (1.0 / x)
      | none => none
  | sin a => (evalFloat env a).map Float.sin
  | cos a => (evalFloat env a).map Float.cos
  | exp a => (evalFloat env a).map Float.exp
  | ln a  =>
      match evalFloat env a with
      | some x => if x > 0 then some (Float.log x) else none
      | none   => none

/-- Substitute `x := v`. -/
def subst (x : String) (v : Expr) : Expr → Expr
  | const n => const n
  | var y   => if x == y then v else var y
  | add a b => add (subst x v a) (subst x v b)
  | mul a b => mul (subst x v a) (subst x v b)
  | pow a b => pow (subst x v a) (subst x v b)
  | neg a   => neg (subst x v a)
  | inv a   => inv (subst x v a)
  | sin a   => sin (subst x v a)
  | cos a   => cos (subst x v a)
  | exp a   => exp (subst x v a)
  | ln a    => ln (subst x v a)

/-! ### Local algebraic rewrite -/

/-- One bottom-up rewrite pass of the ring / field identities. -/
partial def rewrite : Expr → Expr
  | add a b =>
      let a := rewrite a
      let b := rewrite b
      match a, b with
      | const m, const n => const (m + n)
      | const 0, b       => b
      | a, const 0       => a
      | a, neg b         =>
          if a == b then const 0 else add a (neg b)
      | neg a, b         =>
          if a == b then const 0 else add (neg a) b
      | a, b             => add a b
  | mul a b =>
      let a := rewrite a
      let b := rewrite b
      match a, b with
      | const m, const n => const (m * n)
      | const 0, _       => const 0
      | _, const 0       => const 0
      | const 1, b       => b
      | a, const 1       => a
      | const (-1), b    => rewrite (neg b)
      | a, const (-1)    => rewrite (neg a)
      | a, inv b         =>
          if a == b then const 1 else mul a (inv b)
      | inv a, b         =>
          if a == b then const 1 else mul (inv a) b
      | a, b             => mul a b
  | pow a b =>
      let a := rewrite a
      let b := rewrite b
      match a, b with
      | _, const 0       => const 1
      | a, const 1       => a
      | const 1, _       => const 1
      | const m, const n =>
          if n ≥ 0 then const (intPow m n.toNat) else pow (const m) (const n)
      | a, b             => pow a b
  | neg a =>
      match rewrite a with
      | const n => const (-n)
      | neg b   => b
      | b       => neg b
  | inv a =>
      match rewrite a with
      | const 1    => const 1
      | const (-1) => const (-1)
      | inv b      => b
      | b          => inv b
  | sin a => sin (rewrite a)
  | cos a => cos (rewrite a)
  | exp a =>
      match rewrite a with
      | const 0 => const 1
      | b       => exp b
  | ln a =>
      match rewrite a with
      | const 1 => const 0
      | exp b   => b
      | b       => ln b
  | e@(const _) | e@(var _) => e

/-- Iterate `rewrite` to a fixpoint (bounded). -/
def simplify : Expr → Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | n + 1 =>
        let e' := rewrite e
        if e' == e then e else go n e'
  fun e => go (size e + 8) e

/-! ### Expansion (distribute `*` over `+`) -/

/-- Flatten a sum into a list of summands (no nested `add`/`neg` at the top). -/
def flattenAdd : Expr → List Expr
  | add a b => flattenAdd a ++ flattenAdd b
  | neg a   => (flattenAdd a).map neg
  | a       => [a]

/-- Flatten a product into a list of factors. -/
def flattenMul : Expr → List Expr
  | mul a b => flattenMul a ++ flattenMul b
  | a       => [a]

def sumList : List Expr → Expr
  | []      => const 0
  | [a]     => a
  | a :: as => add a (sumList as)

def prodList : List Expr → Expr
  | []      => const 1
  | [a]     => a
  | a :: as => mul a (prodList as)

/-- Distribute multiplication across a sum. -/
partial def expand : Expr → Expr
  | add a b => simplify (add (expand a) (expand b))
  | neg a   => simplify (neg (expand a))
  | mul a b =>
      let as := flattenAdd (expand a)
      let bs := flattenAdd (expand b)
      let terms := as.flatMap (fun x => bs.map (fun y => simplify (mul x y)))
      simplify (sumList terms)
  | pow a (const n) =>
      if n == 0 then const 1
      else if n == 1 then expand a
      else if n > 1 then
        expand (mul (expand a) (pow a (const (n - 1))))
      else
        pow (expand a) (const n)
  | pow a b => pow (expand a) (expand b)
  | inv a   => inv (expand a)
  | sin a   => sin (expand a)
  | cos a   => cos (expand a)
  | exp a   => exp (expand a)
  | ln a    => ln (expand a)
  | e@(const _) | e@(var _) => e

/-! ### Like-term collection for polynomials in `+` / `*` / `^` -/

/-- A monomial is a coefficient and a sorted list of `(var, exp)` pairs. -/
structure Mono where
  coeff : Int
  pows  : List (String × Nat)
  deriving BEq, Repr

namespace Mono

def mul : Mono → Mono → Mono
  | ⟨c₁, p₁⟩, ⟨c₂, p₂⟩ =>
      let rec merge (a b : List (String × Nat)) : List (String × Nat) :=
        match a, b with
        | [], ys => ys
        | xs, [] => xs
        | (x, e₁) :: xs, (y, e₂) :: ys =>
            if x == y then
              (x, e₁ + e₂) :: merge xs ys
            else if x < y then
              (x, e₁) :: merge xs ((y, e₂) :: ys)
            else
              (y, e₂) :: merge ((x, e₁) :: xs) ys
      ⟨c₁ * c₂, merge p₁ p₂⟩

def toExpr : Mono → Expr
  | ⟨0, _⟩ => const 0
  | ⟨c, []⟩ => const c
  | ⟨c, ps⟩ =>
      let rec varPow : List (String × Nat) → Expr
        | [] => const 1
        | (_v, 0) :: rest => varPow rest
        | (v, 1) :: rest =>
            match rest with
            | [] => var v
            | _  => Expr.mul (var v) (varPow rest)
        | (v, e) :: rest =>
            match rest with
            | [] => pow (var v) (const (Int.ofNat e))
            | _  => Expr.mul (pow (var v) (const (Int.ofNat e))) (varPow rest)
      if c == 1 then varPow ps
      else if c == -1 then neg (varPow ps)
      else Expr.mul (const c) (varPow ps)

end Mono

/-- Try to read an atom as a monomial. Returns `none` on transcendentals. -/
partial def toMono? : Expr → Option Mono
  | const n => some ⟨n, []⟩
  | var v   => some ⟨1, [(v, 1)]⟩
  | neg a   => (toMono? a).map (fun m => ⟨-m.coeff, m.pows⟩)
  | mul a b =>
      match toMono? a, toMono? b with
      | some ma, some mb => some (ma.mul mb)
      | _, _ => none
  | pow (var v) (const n) =>
      if n ≥ 0 then some ⟨1, [(v, n.toNat)]⟩ else none
  | pow a (const n) =>
      if n == 0 then some ⟨1, []⟩
      else if n == 1 then toMono? a
      else none
  | _ => none

def collectMonos (ms : List Mono) : List Mono :=
  let rec insert (m : Mono) : List Mono → List Mono
    | [] => if m.coeff == 0 then [] else [m]
    | m' :: rest =>
        if m.pows == m'.pows then
          let c := m.coeff + m'.coeff
          if c == 0 then rest else ⟨c, m.pows⟩ :: rest
        else m' :: insert m rest
  ms.foldl (fun acc m => insert m acc) []

/-- Canonicalise a polynomial (sum of monomials). Leaves other terms intact. -/
def collect : Expr → Expr :=
  fun e =>
    let bits := flattenAdd (expand e)
    let rec split (xs : List Expr) (ms : List Mono) (other : List Expr) :
        List Mono × List Expr :=
      match xs with
      | [] => (ms, other)
      | t :: ts =>
          match toMono? t with
          | some m => split ts (m :: ms) other
          | none   => split ts ms (t :: other)
    let (ms, other) := split bits [] []
    let ms := collectMonos ms.reverse
    simplify (sumList (ms.map Mono.toExpr ++ other.reverse))

/-- Full algebraic normalise: expand, collect like terms, rewrite. -/
def normalize (e : Expr) : Expr :=
  simplify (collect e)

end Expr

/-- `evalInt` of a constant fold is the constant. -/
theorem evalInt_const (env : Expr.Env) (n : Int) :
    Expr.evalInt env (.const n) = some n := rfl

theorem subst_const (x : String) (v : Expr) (n : Int) :
    Expr.subst x v (.const n) = .const n := rfl

theorem subst_same (v : Expr) (x : String) :
    Expr.subst x v (.var x) = v := by
  simp [Expr.subst]

theorem subst_other (v : Expr) {x y : String} (h : x ≠ y) :
    Expr.subst x v (.var y) = .var y := by
  simp [Expr.subst, h]

end Cas
