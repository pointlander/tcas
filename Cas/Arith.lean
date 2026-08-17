/-
  Kernel arithmetic.

  `plusV` / `mulV` / `powV` are the denotation of the unary-nat programs
  `tplus` / `ttimes` / `tpow`. Any 2-argument function that satisfies the
  same recurrences computes `Nat` addition, multiplication and
  exponentiation. Predecessor and zero-test are proved by unfolding the
  small `triage` programs. `evalPoly` is the denotation of kernel
  evaluation on encoded nat-polynomials.
-/

import Cas.Semantics
import Cas.Encode
import Cas.Expr
import Cas.Kernel

namespace Cas

/-! ### Denotation of unary-nat arithmetic -/

/-- `plus 0 n = n`, `plus (succ m) n = succ (plus m n)`. -/
def plusV : Value → Value → Value
  | .leaf, n     => n
  | .stem m, n   => .stem (plusV m n)
  | .fork _ _, n => n

/-- `times 0 m = 0`, `times (succ n) m = plus m (times n m)`. -/
def mulV : Value → Value → Value
  | .leaf, _     => .leaf
  | .stem n, m   => plusV m (mulV n m)
  | .fork _ _, _ => .leaf

/-- `pow b 0 = 1`, `pow b (succ e) = times b (pow b e)`. -/
def powV : Value → Value → Value
  | _, .leaf     => .stem .leaf
  | b, .stem e   => mulV b (powV b e)
  | _, .fork _ _ => .stem .leaf

theorem plusV_zero (n : Value) : plusV .leaf n = n := rfl

theorem plusV_succ (m n : Value) : plusV (.stem m) n = .stem (plusV m n) := rfl

theorem mulV_zero (m : Value) : mulV .leaf m = .leaf := rfl

theorem mulV_succ (n m : Value) : mulV (.stem n) m = plusV m (mulV n m) := rfl

theorem powV_zero (b : Value) : powV b .leaf = .stem .leaf := rfl

theorem powV_succ (b e : Value) : powV b (.stem e) = mulV b (powV b e) := rfl

theorem plusV_ofNat (m n : Nat) :
    plusV (Value.ofNat m) (Value.ofNat n) = Value.ofNat (m + n) := by
  induction m with
  | zero =>
      simp [Value.ofNat, plusV, Nat.zero_add]
  | succ m ih =>
      simp [Value.ofNat, plusV, ih, Nat.succ_add]

theorem mulV_ofNat (m n : Nat) :
    mulV (Value.ofNat m) (Value.ofNat n) = Value.ofNat (m * n) := by
  induction m with
  | zero =>
      simp [Value.ofNat, mulV, Nat.zero_mul]
  | succ m ih =>
      simp [Value.ofNat, mulV, ih, plusV_ofNat, Nat.succ_mul, Nat.add_comm]

theorem powV_ofNat (b e : Nat) :
    powV (Value.ofNat b) (Value.ofNat e) = Value.ofNat (b ^ e) := by
  induction e with
  | zero =>
      simp [Value.ofNat, powV]
  | succ e ih =>
      simp [Value.ofNat, powV, ih, mulV_ofNat, Nat.pow_succ, Nat.mul_comm]

/-- Any function with the plus recurrences is addition on unary nats. -/
theorem plus_rec_unique (φ : Value → Value → Option Value)
    (h0 : ∀ n : Nat, φ .leaf (Value.ofNat n) = some (Value.ofNat n))
    (hs : ∀ m n : Nat,
      φ (.stem (Value.ofNat m)) (Value.ofNat n) =
        (φ (Value.ofNat m) (Value.ofNat n)).map .stem) :
    ∀ m n : Nat, φ (Value.ofNat m) (Value.ofNat n) = some (Value.ofNat (m + n)) := by
  intro m n
  induction m with
  | zero =>
      simpa [Value.ofNat] using h0 n
  | succ m ih =>
      simp [Value.ofNat, hs, ih, Nat.succ_add]

theorem mul_rec_unique (φ : Value → Value → Option Value)
    (h0 : ∀ n : Nat, φ .leaf (Value.ofNat n) = some .leaf)
    (hs : ∀ m n : Nat,
      φ (.stem (Value.ofNat m)) (Value.ofNat n) =
        (φ (Value.ofNat m) (Value.ofNat n)).bind
          (fun k => some (plusV (Value.ofNat n) k))) :
    ∀ m n : Nat, φ (Value.ofNat m) (Value.ofNat n) = some (Value.ofNat (m * n)) := by
  intro m n
  induction m with
  | zero =>
      simpa [Value.ofNat] using h0 n
  | succ m ih =>
      simp [Value.ofNat, hs, ih, plusV_ofNat, Nat.succ_mul, Nat.add_comm]

theorem pow_rec_unique (φ : Value → Value → Option Value)
    (h0 : ∀ b : Nat, φ (Value.ofNat b) .leaf = some (.stem .leaf))
    (hs : ∀ b e : Nat,
      φ (Value.ofNat b) (.stem (Value.ofNat e)) =
        (φ (Value.ofNat b) (Value.ofNat e)).map (fun k => mulV (Value.ofNat b) k)) :
    ∀ b e : Nat, φ (Value.ofNat b) (Value.ofNat e) = some (Value.ofNat (b ^ e)) := by
  intro b e
  induction e with
  | zero =>
      simpa [Value.ofNat] using h0 b
  | succ e ih =>
      simp [Value.ofNat, hs, ih, mulV_ofNat, Nat.pow_succ, Nat.mul_comm]

/-- If a 2-argument program satisfies the plus recurrences, it adds unary nats. -/
theorem kernelAdd_ofNat_of_rec
    (h0 : ∀ n : Nat, kernelAdd .leaf (Value.ofNat n) = some (Value.ofNat n))
    (hs : ∀ m n : Nat,
      kernelAdd (.stem (Value.ofNat m)) (Value.ofNat n) =
        (kernelAdd (Value.ofNat m) (Value.ofNat n)).map .stem) :
    ∀ m n : Nat, kernelAdd (Value.ofNat m) (Value.ofNat n) = some (Value.ofNat (m + n)) :=
  plus_rec_unique _ h0 hs

theorem kernelMul_ofNat_of_rec
    (h0 : ∀ n : Nat, kernelMul .leaf (Value.ofNat n) = some .leaf)
    (hs : ∀ m n : Nat,
      kernelMul (.stem (Value.ofNat m)) (Value.ofNat n) =
        (kernelMul (Value.ofNat m) (Value.ofNat n)).bind
          (fun k => some (plusV (Value.ofNat n) k))) :
    ∀ m n : Nat, kernelMul (Value.ofNat m) (Value.ofNat n) = some (Value.ofNat (m * n)) :=
  mul_rec_unique _ h0 hs

theorem kernelPow_ofNat_of_rec
    (h0 : ∀ b : Nat, kernelPow (Value.ofNat b) .leaf = some (.stem .leaf))
    (hs : ∀ b e : Nat,
      kernelPow (Value.ofNat b) (.stem (Value.ofNat e)) =
        (kernelPow (Value.ofNat b) (Value.ofNat e)).map
          (fun k => mulV (Value.ofNat b) k)) :
    ∀ b e : Nat, kernelPow (Value.ofNat b) (Value.ofNat e) = some (Value.ofNat (b ^ e)) :=
  pow_rec_unique _ h0 hs

/-! ### Predecessor and zero-test -/

def predVal : Value :=
  triageVal .leaf ival (.fork .leaf (.fork .leaf .leaf))

def isZeroVal : Value :=
  triageVal (.stem .leaf) (.fork .leaf .leaf) (.fork .leaf (.fork .leaf .leaf))

theorem eval_tpred : eval 16 tpred = some predVal := by
  native_decide

theorem eval_tisZero : eval 16 tisZero = some isZeroVal := by
  native_decide

private theorem fuel_ge_16 : 16 ≤ Value.defaultFuel := by
  simp [Value.defaultFuel]

theorem run1_pred_zero : run1 tpred .leaf 16 = some .leaf := by
  simp [run1, eval_tpred, predVal, triageVal, Value.apply]

theorem run1_pred_succ (n : Value) : run1 tpred (.stem n) 16 = some n := by
  simp [run1, eval_tpred, predVal, triageVal, Value.apply]
  exact apply_mono (by omega) (apply_I_val n)

theorem kernelPred_zero : kernelPred .leaf = some .leaf := by
  simp [kernelPred]
  have h := eval_mono fuel_ge_16 eval_tpred
  simp [run1, h]
  have : Value.apply 16 predVal .leaf = some .leaf := by
    simp [predVal, triageVal, Value.apply]
  exact apply_mono fuel_ge_16 this

theorem kernelPred_succ (n : Value) : kernelPred (.stem n) = some n := by
  simp [kernelPred]
  have h := eval_mono fuel_ge_16 eval_tpred
  simp [run1, h]
  have : Value.apply 16 predVal (.stem n) = some n := by
    simp [predVal, triageVal, Value.apply]
    exact apply_mono (by omega) (apply_I_val n)
  exact apply_mono fuel_ge_16 this

theorem kernelIsZero_zero : kernelIsZero .leaf = some (.stem .leaf) := by
  simp [kernelIsZero]
  have h := eval_mono fuel_ge_16 eval_tisZero
  simp [run1, h]
  have : Value.apply 16 isZeroVal .leaf = some (.stem .leaf) := by
    simp [isZeroVal, triageVal, Value.apply]
  exact apply_mono fuel_ge_16 this

theorem kernelIsZero_succ (n : Value) : kernelIsZero (.stem n) = some .leaf := by
  simp [kernelIsZero]
  have h := eval_mono fuel_ge_16 eval_tisZero
  simp [run1, h]
  have : Value.apply 16 isZeroVal (.stem n) = some .leaf := by
    simp [isZeroVal, triageVal, Value.apply]
  exact apply_mono fuel_ge_16 this

/-! ### Polynomial evaluation (spec of kernel eval) -/

inductive NatPoly : Expr → Prop where
  | const (n : Nat) : NatPoly (.const n)
  | var (x : String) : NatPoly (.var x)
  | add {a b} : NatPoly a → NatPoly b → NatPoly (.add a b)
  | mul {a b} : NatPoly a → NatPoly b → NatPoly (.mul a b)
  | pow {a b} : NatPoly a → NatPoly b → NatPoly (.pow a b)

/-- Denotational evaluation using `plusV` / `mulV` / `powV`. -/
def evalPoly (x : Value) : Value → Option Value
  | .fork tag payload =>
      match tag.toNat? with
      | some 0 =>
          match payload with
          | .fork .leaf mag => some mag
          | _ => none
      | some 1 => some x
      | some 2 =>
          match payload with
          | .fork a b =>
              match evalPoly x a, evalPoly x b with
              | some va, some vb => some (plusV va vb)
              | _, _ => none
          | _ => none
      | some 3 =>
          match payload with
          | .fork a b =>
              match evalPoly x a, evalPoly x b with
              | some va, some vb => some (mulV va vb)
              | _, _ => none
          | _ => none
      | some 4 =>
          match payload with
          | .fork a b =>
              match evalPoly x a, evalPoly x b with
              | some va, some vb => some (powV va vb)
              | _, _ => none
          | _ => none
      | _ => none
  | _ => none

theorem evalPoly_const (x : Value) (n : Nat) :
    evalPoly x (Expr.encode (.const (Int.ofNat n))) = some (Value.ofNat n) := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.ofInt, Value.toNat?]

theorem evalPoly_var (x : Value) (s : String) :
    evalPoly x (Expr.encode (.var s)) = some x := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.toNat?]

theorem evalPoly_add (x : Value) (a b : Expr) {va vb : Value}
    (ha : evalPoly x (Expr.encode a) = some va)
    (hb : evalPoly x (Expr.encode b) = some vb) :
    evalPoly x (Expr.encode (.add a b)) = some (plusV va vb) := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.toNat?, ha, hb]

theorem evalPoly_mul (x : Value) (a b : Expr) {va vb : Value}
    (ha : evalPoly x (Expr.encode a) = some va)
    (hb : evalPoly x (Expr.encode b) = some vb) :
    evalPoly x (Expr.encode (.mul a b)) = some (mulV va vb) := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.toNat?, ha, hb]

theorem evalPoly_pow (x : Value) (a b : Expr) {va vb : Value}
    (ha : evalPoly x (Expr.encode a) = some va)
    (hb : evalPoly x (Expr.encode b) = some vb) :
    evalPoly x (Expr.encode (.pow a b)) = some (powV va vb) := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.toNat?, ha, hb]

/-- `evalInt`-style evaluation of a nat-polynomial at a single input. -/
def evalNatAt (n : Nat) : Expr → Option Nat
  | .const k => if 0 ≤ k then some k.toNat else none
  | .var _ => some n
  | .add a b =>
      match evalNatAt n a, evalNatAt n b with
      | some x, some y => some (x + y)
      | _, _ => none
  | .mul a b =>
      match evalNatAt n a, evalNatAt n b with
      | some x, some y => some (x * y)
      | _, _ => none
  | .pow a b =>
      match evalNatAt n a, evalNatAt n b with
      | some x, some y => some (x ^ y)
      | _, _ => none
  | _ => none

theorem evalPoly_natPoly (e : Expr) (n : Nat) (h : NatPoly e) :
    ∃ k, evalNatAt n e = some k ∧
      evalPoly (Value.ofNat n) (Expr.encode e) = some (Value.ofNat k) := by
  induction h with
  | const k =>
      refine ⟨k, ?_, ?_⟩
      · simp [evalNatAt]
      · simpa using evalPoly_const (Value.ofNat n) k
  | var s =>
      refine ⟨n, rfl, evalPoly_var _ s⟩
  | @add a b _ _ iha ihb =>
      obtain ⟨ka, ha1, ha2⟩ := iha
      obtain ⟨kb, hb1, hb2⟩ := ihb
      refine ⟨ka + kb, ?_, ?_⟩
      · simp [evalNatAt, ha1, hb1]
      · simpa [plusV_ofNat] using evalPoly_add (Value.ofNat n) a b ha2 hb2
  | @mul a b _ _ iha ihb =>
      obtain ⟨ka, ha1, ha2⟩ := iha
      obtain ⟨kb, hb1, hb2⟩ := ihb
      refine ⟨ka * kb, ?_, ?_⟩
      · simp [evalNatAt, ha1, hb1]
      · simpa [mulV_ofNat] using evalPoly_mul (Value.ofNat n) a b ha2 hb2
  | @pow a b _ _ iha ihb =>
      obtain ⟨ka, ha1, ha2⟩ := iha
      obtain ⟨kb, hb1, hb2⟩ := ihb
      refine ⟨ka ^ kb, ?_, ?_⟩
      · simp [evalNatAt, ha1, hb1]
      · simpa [powV_ofNat] using evalPoly_pow (Value.ofNat n) a b ha2 hb2

end Cas
