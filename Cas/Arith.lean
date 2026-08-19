/-
  Kernel arithmetic.

  `plusV` / `mulV` / `powV` are the denotation of the unary-nat programs
  `tplus` / `ttimes` / `tpow`. Any 2-argument function that satisfies the
  same recurrences computes `Nat` addition, multiplication and
  exponentiation. Binary nats have the same uniqueness theorems on
  `ofBin` (`plus_bin_rec_unique` and friends in `Cas.Bin`). Predecessor
  and zero-test are proved by unfolding the small `triage` programs.
  `evalPoly` is the denotation of kernel evaluation on encoded
  nat-polynomials, using binary magnitudes. `walkEval` is the denotation
  of `teval` against a named environment; `walkDiff` is the denotation
  of `tdiff`.
-/

import Cas.Semantics
import Cas.Encode
import Cas.Bin
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

/-- Saturating subtraction: `minus 0 n = 0`, `minus m 0 = m`. -/
def minusV : Value → Value → Value
  | .leaf, _     => .leaf
  | m, .leaf     => m
  | .stem m, .stem n => minusV m n
  | .fork _ _, _ => .leaf
  | m, .fork _ _ => m

theorem minusV_zero_left (n : Value) : minusV .leaf n = .leaf := rfl

theorem minusV_zero_right (m : Value) : minusV m .leaf = m := by
  cases m <;> rfl

theorem minusV_ofNat (m n : Nat) :
    minusV (Value.ofNat m) (Value.ofNat n) = Value.ofNat (m - n) := by
  induction m generalizing n with
  | zero =>
      simp [Value.ofNat, minusV]
  | succ m ih =>
      cases n with
      | zero =>
          simp [Value.ofNat, minusV]
      | succ n =>
          simp [Value.ofNat, minusV, ih, Nat.succ_sub_succ]

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

/-- Denotational evaluation using `plusBinV` / `mulBinV` / `powBinV`. -/
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
              | some va, some vb => some (plusBinV va vb)
              | _, _ => none
          | _ => none
      | some 3 =>
          match payload with
          | .fork a b =>
              match evalPoly x a, evalPoly x b with
              | some va, some vb => some (mulBinV va vb)
              | _, _ => none
          | _ => none
      | some 4 =>
          match payload with
          | .fork a b =>
              match evalPoly x a, evalPoly x b with
              | some va, some vb => some (powBinV va vb)
              | _, _ => none
          | _ => none
      | _ => none
  | _ => none

theorem evalPoly_const (x : Value) (n : Nat) :
    evalPoly x (Expr.encode (.const (Int.ofNat n))) = some (Value.ofBin n) := by
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
    evalPoly x (Expr.encode (.add a b)) = some (plusBinV va vb) := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.toNat?, ha, hb]

theorem evalPoly_mul (x : Value) (a b : Expr) {va vb : Value}
    (ha : evalPoly x (Expr.encode a) = some va)
    (hb : evalPoly x (Expr.encode b) = some vb) :
    evalPoly x (Expr.encode (.mul a b)) = some (mulBinV va vb) := by
  unfold Expr.encode Expr.tagged
  unfold evalPoly
  simp [Expr.tag, Value.toNat?, ha, hb]

theorem evalPoly_pow (x : Value) (a b : Expr) {va vb : Value}
    (ha : evalPoly x (Expr.encode a) = some va)
    (hb : evalPoly x (Expr.encode b) = some vb) :
    evalPoly x (Expr.encode (.pow a b)) = some (powBinV va vb) := by
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
      evalPoly (Value.ofBin n) (Expr.encode e) = some (Value.ofBin k) := by
  induction h with
  | const k =>
      refine ⟨k, ?_, ?_⟩
      · simp [evalNatAt]
      · simpa using evalPoly_const (Value.ofBin n) k
  | var s =>
      refine ⟨n, rfl, evalPoly_var _ s⟩
  | @add a b _ _ iha ihb =>
      obtain ⟨ka, ha1, ha2⟩ := iha
      obtain ⟨kb, hb1, hb2⟩ := ihb
      refine ⟨ka + kb, ?_, ?_⟩
      · simp [evalNatAt, ha1, hb1]
      · simpa [plusBinV_ofBin] using evalPoly_add (Value.ofBin n) a b ha2 hb2
  | @mul a b _ _ iha ihb =>
      obtain ⟨ka, ha1, ha2⟩ := iha
      obtain ⟨kb, hb1, hb2⟩ := ihb
      refine ⟨ka * kb, ?_, ?_⟩
      · simp [evalNatAt, ha1, hb1]
      · simpa [mulBinV_ofBin] using evalPoly_mul (Value.ofBin n) a b ha2 hb2
  | @pow a b _ _ iha ihb =>
      obtain ⟨ka, ha1, ha2⟩ := iha
      obtain ⟨kb, hb1, hb2⟩ := ihb
      refine ⟨ka ^ kb, ?_, ?_⟩
      · simp [evalNatAt, ha1, hb1]
      · simpa [powBinV_ofBin] using evalPoly_pow (Value.ofBin n) a b ha2 hb2

/-! ### `walkEval` agrees with `evalInt` on integer combinations -/

theorem liftInt_ofInt (i : Int) :
    liftInt (Value.ofInt i) = Value.ofRat i 1 := by
  simp [liftInt, toInt_ofInt]

private theorem beq_false_of_ne {x y : String} (h : x ≠ y) : (x == y) = false := by
  simpa [beq_iff_eq] using h

theorem lookupEnv_encodeEnv (env : Expr.Env) (x : String) :
    lookupEnv (Expr.encodeString x) (Expr.encodeEnv env) =
      (Expr.lookup x env).map (fun n => Value.ofRat n 1) := by
  induction env with
  | nil =>
      simp [lookupEnv, Expr.encodeEnv, Expr.lookup]
  | cons kv rest ih =>
      obtain ⟨k, n⟩ := kv
      unfold Expr.encodeEnv lookupEnv
      by_cases h : x = k
      · subst h
        simp [Value.equalV_rfl, Expr.lookup]
      · have hne : Value.equalV (Expr.encodeString k) (Expr.encodeString x) = false := by
          rw [Bool.eq_false_iff, ne_eq, Value.equalV_eq]
          intro heq
          exact h (encodeString_inj heq).symm
        simp [hne, beq_false_of_ne h, Expr.lookup, ih]

theorem walkEval_const (env : Value) (n : Int) :
    walkEval env (Expr.encode (.const n)) = some (Value.ofRat n 1) := by
  simp [encode_const, Expr.tag, walkEval, liftInt_ofInt]

theorem walkEval_var (env : Expr.Env) (x : String) :
    walkEval (Expr.encodeEnv env) (Expr.encode (.var x)) =
      (Expr.lookup x env).map (fun n => Value.ofRat n 1) := by
  simp [encode_var, Expr.tag, walkEval, lookupEnv_encodeEnv]

theorem walkEval_add (env : Value) (a b : Expr) {va vb : Value}
    (ha : walkEval env (Expr.encode a) = some va)
    (hb : walkEval env (Expr.encode b) = some vb) :
    walkEval env (Expr.encode (.add a b)) = some (plusRatV va vb) := by
  simp [encode_add, Expr.tag, walkEval, ha, hb]

theorem walkEval_mul (env : Value) (a b : Expr) {va vb : Value}
    (ha : walkEval env (Expr.encode a) = some va)
    (hb : walkEval env (Expr.encode b) = some vb) :
    walkEval env (Expr.encode (.mul a b)) = some (mulRatV va vb) := by
  simp [encode_mul, Expr.tag, walkEval, ha, hb]

theorem walkEval_neg (env : Value) (a : Expr) {va : Value}
    (ha : walkEval env (Expr.encode a) = some va) :
    walkEval env (Expr.encode (.neg a)) = some (negRatV va) := by
  simp [encode_neg, Expr.tag, walkEval, ha]

/-- Integer polynomials: constants, variables, `+`, `*`, `-`. -/
inductive ZPoly : Expr → Prop where
  | const (n : Int) : ZPoly (.const n)
  | var (x : String) : ZPoly (.var x)
  | add {a b} : ZPoly a → ZPoly b → ZPoly (.add a b)
  | mul {a b} : ZPoly a → ZPoly b → ZPoly (.mul a b)
  | neg {a} : ZPoly a → ZPoly (.neg a)

theorem walkEval_zpoly (e : Expr) (env : Expr.Env) (h : ZPoly e) :
    walkEval (Expr.encodeEnv env) (Expr.encode e) =
      (Expr.evalInt env e).map (fun n => Value.ofRat n 1) := by
  induction h with
  | const n =>
      simp [walkEval_const, Expr.evalInt]
  | var x =>
      simpa [Expr.evalInt] using walkEval_var env x
  | @add a b _ _ iha ihb =>
      simp [encode_add, Expr.tag, walkEval, Expr.evalInt, iha, ihb]
      cases Expr.evalInt env a <;> cases Expr.evalInt env b
        <;> simp [plusRatV_ofRat_one]
  | @mul a b _ _ iha ihb =>
      simp [encode_mul, Expr.tag, walkEval, Expr.evalInt, iha, ihb]
      cases Expr.evalInt env a <;> cases Expr.evalInt env b
        <;> simp [mulRatV_ofRat_one]
  | @neg a _ ih =>
      simp [encode_neg, Expr.tag, walkEval, Expr.evalInt, ih]
      cases Expr.evalInt env a <;> simp [negRatV_ofRat_one]

/-! ### `walkDiff` agrees with `Expr.diff` -/

theorem walkDiff_const (var : Value) (n : Int) :
    walkDiff var (Expr.encode (.const n)) = some (Expr.encode (.const 0)) := by
  simp [encode_const, Expr.tag, walkDiff]

theorem walkDiff_var (x y : String) :
    walkDiff (Expr.encodeString x) (Expr.encode (.var y)) =
      some (Expr.encode (Expr.diff x (.var y))) := by
  simp [encode_var, Expr.tag, walkDiff]
  by_cases h : x = y
  · subst h
    simp [Value.equalV_rfl, Expr.diff]
  · have hne : Value.equalV (Expr.encodeString y) (Expr.encodeString x) = false := by
      rw [Bool.eq_false_iff, ne_eq, Value.equalV_eq]
      intro heq
      exact h (encodeString_inj heq).symm
    simp [hne, beq_false_of_ne h, Expr.diff]

theorem walkDiff_add (var : Value) (a b : Expr) {da db : Value}
    (ha : walkDiff var (Expr.encode a) = some da)
    (hb : walkDiff var (Expr.encode b) = some db) :
    walkDiff var (Expr.encode (.add a b)) =
      some (Expr.tagged 2 (.fork da db)) := by
  simp [encode_add, Expr.tag, walkDiff, ha, hb]

theorem walkDiff_mul (var : Value) (a b : Expr) {da db : Value}
    (ha : walkDiff var (Expr.encode a) = some da)
    (hb : walkDiff var (Expr.encode b) = some db) :
    walkDiff var (Expr.encode (.mul a b)) =
      some (Expr.tagged 2
        (.fork (Expr.tagged 3 (.fork da (Expr.encode b)))
               (Expr.tagged 3 (.fork (Expr.encode a) db)))) := by
  simp [encode_mul, Expr.tag, walkDiff, ha, hb]

theorem walkDiff_neg (var : Value) (a : Expr) {da : Value}
    (ha : walkDiff var (Expr.encode a) = some da) :
    walkDiff var (Expr.encode (.neg a)) = some (Expr.tagged 5 da) := by
  simp [encode_neg, Expr.tag, walkDiff, ha]

/-- Constructors on which `walkDiff` matches `Expr.diff` (no general power). -/
inductive DiffShape : Expr → Prop where
  | const (n : Int) : DiffShape (.const n)
  | var (x : String) : DiffShape (.var x)
  | add {a b} : DiffShape a → DiffShape b → DiffShape (.add a b)
  | mul {a b} : DiffShape a → DiffShape b → DiffShape (.mul a b)
  | neg {a} : DiffShape a → DiffShape (.neg a)
  | inv {a} : DiffShape a → DiffShape (.inv a)
  | sin {a} : DiffShape a → DiffShape (.sin a)
  | cos {a} : DiffShape a → DiffShape (.cos a)
  | exp {a} : DiffShape a → DiffShape (.exp a)
  | ln {a} : DiffShape a → DiffShape (.ln a)

theorem walkDiff_diff (e : Expr) (x : String) (h : DiffShape e) :
    walkDiff (Expr.encodeString x) (Expr.encode e) =
      some (Expr.encode (Expr.diff x e)) := by
  induction h with
  | const n =>
      simpa [Expr.diff] using walkDiff_const (Expr.encodeString x) n
  | var y =>
      exact walkDiff_var x y
  | @add a b _ _ iha ihb =>
      have h := walkDiff_add (Expr.encodeString x) a b iha ihb
      simpa [Expr.diff, Expr.encode, Expr.tagged] using h
  | @mul a b _ _ iha ihb =>
      have h := walkDiff_mul (Expr.encodeString x) a b iha ihb
      simpa [Expr.diff, Expr.encode, Expr.tagged] using h
  | @neg a _ ih =>
      have h := walkDiff_neg (Expr.encodeString x) a ih
      simpa [Expr.diff, Expr.encode, Expr.tagged] using h
  | @inv a _ ih =>
      simp [encode_inv, Expr.tag, Expr.tagged, Expr.diff, walkDiff, ih,
        encode_neg, encode_mul, encode_inv, encode_pow, encode_const]
  | @sin a _ ih =>
      simp [encode_sin, Expr.tag, Expr.tagged, Expr.diff, walkDiff, ih,
        encode_mul, encode_cos]
  | @cos a _ ih =>
      simp [encode_cos, Expr.tag, Expr.tagged, Expr.diff, walkDiff, ih,
        encode_neg, encode_mul, encode_sin]
  | @exp a _ ih =>
      simp [encode_exp, Expr.tag, Expr.tagged, Expr.diff, walkDiff, ih,
        encode_mul, encode_exp]
  | @ln a _ ih =>
      simp [encode_ln, Expr.tag, Expr.tagged, Expr.diff, walkDiff, ih,
        encode_mul, encode_inv]

end Cas
