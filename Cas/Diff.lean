/-
  Symbolic differentiation.
-/

import Cas.Algebra

namespace Cas

namespace Expr

/-- Partial derivative with respect to `x`. -/
def diff (x : String) : Expr → Expr
  | const _ => const 0
  | var y   => if x == y then const 1 else const 0
  | add a b => add (diff x a) (diff x b)
  | mul a b => add (mul (diff x a) b) (mul a (diff x b))
  | pow a b =>
      -- d/dx (a^b) = a^b * (b' * ln a + b * a' / a)
      -- Special case: constant exponent n,  n * a^(n-1) * a'
      match b with
      | const n =>
          mul (mul (const n) (pow a (const (n - 1)))) (diff x a)
      | _ =>
          mul (pow a b)
            (add (mul (diff x b) (ln a))
                 (mul b (mul (diff x a) (inv a))))
  | neg a => neg (diff x a)
  | inv a =>
      -- d(1/a) = -a' / a²
      neg (mul (diff x a) (inv (pow a (const 2))))
  | sin a => mul (cos a) (diff x a)
  | cos a => neg (mul (sin a) (diff x a))
  | exp a => mul (exp a) (diff x a)
  | ln a  => mul (diff x a) (inv a)

def dsimp (x : String) (e : Expr) : Expr :=
  normalize (diff x e)

/-! ### Structural lemmas (the "calculus" the CAS implements) -/

theorem diff_const (x : String) (n : Int) :
    diff x (const n) = const 0 := rfl

theorem diff_var_same (x : String) :
    diff x (var x) = const 1 := by
  simp [diff]

theorem diff_var_other {x y : String} (h : x ≠ y) :
    diff x (var y) = const 0 := by
  simp [diff, h]

theorem diff_add (x : String) (a b : Expr) :
    diff x (add a b) = add (diff x a) (diff x b) := rfl

theorem diff_mul (x : String) (a b : Expr) :
    diff x (mul a b) = add (mul (diff x a) b) (mul a (diff x b)) := rfl

theorem diff_neg (x : String) (a : Expr) :
    diff x (neg a) = neg (diff x a) := rfl

theorem diff_sin (x : String) (a : Expr) :
    diff x (sin a) = mul (cos a) (diff x a) := rfl

theorem diff_cos (x : String) (a : Expr) :
    diff x (cos a) = neg (mul (sin a) (diff x a)) := rfl

theorem diff_exp (x : String) (a : Expr) :
    diff x (exp a) = mul (exp a) (diff x a) := rfl

theorem diff_ln (x : String) (a : Expr) :
    diff x (ln a) = mul (diff x a) (inv a) := rfl

theorem diff_pow_const (x : String) (a : Expr) (n : Int) :
    diff x (pow a (const n)) =
      mul (mul (const n) (pow a (const (n - 1)))) (diff x a) := rfl

end Expr

end Cas
