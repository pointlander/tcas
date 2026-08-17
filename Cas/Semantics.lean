/-
  Operational lemmas for the fuelled evaluator: monotonicity, the five
  rules as `Applies`, and the small combinators K, I, S, triage, wait.
-/

import Cas.Tree
import Cas.Reduce
import Cas.Bracket

namespace Cas

/-! ### Fuel monotonicity -/

theorem apply_mono {n m : Nat} (hle : n ≤ m) {f x v : Value} :
    Value.apply n f x = some v → Value.apply m f x = some v := by
  induction n generalizing m f x v with
  | zero =>
      intro h
      simp [Value.apply] at h
  | succ n ih =>
      intro h
      cases m with
      | zero => cases hle
      | succ m =>
          have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
          cases f with
          | leaf =>
              simp [Value.apply] at h ⊢
              exact h
          | stem _ =>
              simp [Value.apply] at h ⊢
              exact h
          | fork f1 f2 =>
              cases f1 with
              | leaf =>
                  simp [Value.apply] at h ⊢
                  exact h
              | stem x' =>
                  simp [Value.apply] at h
                  split at h
                  · contradiction
                  · next xz hxz =>
                      split at h
                      · contradiction
                      · next yz hyz =>
                          simp [Value.apply, ih hnm hxz, ih hnm hyz, ih hnm h]
              | fork w x' =>
                  cases x with
                  | leaf =>
                      simp [Value.apply] at h ⊢
                      exact h
                  | stem u =>
                      simp [Value.apply] at h ⊢
                      exact ih hnm h
                  | fork u w' =>
                      simp [Value.apply] at h
                      split at h
                      · contradiction
                      · next yu hyu =>
                          simp [Value.apply, ih hnm hyu, ih hnm h]

theorem eval_mono {n m : Nat} (hle : n ≤ m) {t : Tree} {v : Value} :
    eval n t = some v → eval m t = some v := by
  induction n generalizing m t v with
  | zero =>
      intro h
      cases t with
      | node =>
          cases m with
          | zero => exact h
          | succ _ =>
              simp [eval] at h ⊢
              exact h
      | app _ _ => simp [eval] at h
      | ref _ => simp [eval] at h
  | succ n ih =>
      intro h
      cases t with
      | node =>
          cases m with
          | zero => cases hle
          | succ _ =>
              simp [eval] at h ⊢
              exact h
      | ref _ => simp [eval] at h
      | app f a =>
          cases m with
          | zero => cases hle
          | succ m =>
              have hnm : n ≤ m := Nat.le_of_succ_le_succ hle
              simp [eval] at h
              split at h
              · next fv av hfv hav =>
                  simp [eval, ih hnm hfv, ih hnm hav, apply_mono hnm h]
              · contradiction

/-! ### Termination relation -/

/-- `Applies f x y` means `f x` reduces to `y` with some fuel. -/
def Applies (f x y : Value) : Prop :=
  ∃ fuel, Value.apply fuel f x = some y

def Applies2 (f a b r : Value) : Prop :=
  ∃ fa, Applies f a fa ∧ Applies fa b r

def Applies3 (f a b c r : Value) : Prop :=
  ∃ fab, Applies2 f a b fab ∧ Applies fab c r

theorem applies_leaf (y : Value) : Applies .leaf y (.stem y) :=
  ⟨1, rfl⟩

theorem applies_stem (x y : Value) : Applies (.stem x) y (.fork x y) :=
  ⟨1, rfl⟩

theorem applies_K (y z : Value) : Applies (.fork .leaf y) z y :=
  ⟨1, rfl⟩

theorem applies_triage_leaf (w x y : Value) :
    Applies (.fork (.fork w x) y) .leaf w :=
  ⟨1, rfl⟩

theorem applies_triage_stem {w x y u r : Value}
    (h : Applies x u r) : Applies (.fork (.fork w x) y) (.stem u) r := by
  obtain ⟨fuel, hf⟩ := h
  exact ⟨fuel + 1, by simpa [Value.apply] using hf⟩

theorem applies_triage_fork {w x y u v yu r : Value}
    (hyu : Applies y u yu) (hur : Applies yu v r) :
    Applies (.fork (.fork w x) y) (.fork u v) r := by
  obtain ⟨f1, h1⟩ := hyu
  obtain ⟨f2, h2⟩ := hur
  refine ⟨max f1 f2 + 1, ?_⟩
  have h1' := apply_mono (Nat.le_max_left f1 f2) h1
  have h2' := apply_mono (Nat.le_max_right f1 f2) h2
  simp [Value.apply, h1', h2']

theorem applies_S {x y z xz yz r : Value}
    (hxz : Applies x z xz) (hyz : Applies y z yz) (hr : Applies xz yz r) :
    Applies (.fork (.stem x) y) z r := by
  obtain ⟨f1, h1⟩ := hxz
  obtain ⟨f2, h2⟩ := hyz
  obtain ⟨f3, h3⟩ := hr
  let F := max f1 (max f2 f3)
  refine ⟨F + 1, ?_⟩
  have hf1 : f1 ≤ F := Nat.le_max_left _ _
  have hf2 : f2 ≤ F := Nat.le_trans (Nat.le_max_left f2 f3) (Nat.le_max_right _ _)
  have hf3 : f3 ≤ F := Nat.le_trans (Nat.le_max_right f2 f3) (Nat.le_max_right _ _)
  simp [Value.apply, apply_mono hf1 h1, apply_mono hf2 h2, apply_mono hf3 h3]

/-! ### Combinators as values -/

def kval : Value := .stem .leaf

/-- `I = △ (△ K) K`. -/
def ival : Value := .fork (.stem (.stem .leaf)) (.stem .leaf)

/-- `S = △ (△ (K △)) △`. -/
def sval : Value := .fork (.stem (.fork .leaf .leaf)) .leaf

def triageVal (l s f : Value) : Value := .fork (.fork l s) f

theorem eval_K : eval 2 K = some kval := rfl

theorem eval_I : eval 8 I = some ival := by
  native_decide

theorem apply_I_val (z : Value) : Value.apply 2 ival z = some z := by
  simp [ival, Value.apply]

theorem applies_I (z : Value) : Applies ival z z :=
  ⟨2, apply_I_val z⟩

theorem applies_kval (y : Value) : Applies kval y (.fork .leaf y) :=
  applies_stem .leaf y

theorem applies_K2 (y z : Value) : Applies2 kval y z y :=
  ⟨.fork .leaf y, applies_kval y, applies_K y z⟩

/-! ### `wait` -/

/-- `wait M N` as a value: `△ (△ (△ (△ (K M)) (K N))) I`. -/
def waitVal (M N : Value) : Value :=
  .fork (.stem (.fork (.stem (.fork .leaf M)) (.fork .leaf N))) ival

private theorem apply_ival (P : Value) : Value.apply 2 ival P = some P := by
  simp [ival, Value.apply]

theorem applies_wait {M N P MN r : Value}
    (hMN : Applies M N MN) (hr : Applies MN P r) :
    Applies (waitVal M N) P r := by
  obtain ⟨f1, h1⟩ := hMN
  obtain ⟨f2, h2⟩ := hr
  refine ⟨f1 + f2 + 8, ?_⟩
  have hI : Value.apply (f1 + f2 + 7) ival P = some P :=
    apply_mono (by omega) (apply_ival P)
  have hX :
      Value.apply (f1 + f2 + 7)
        (.fork (.stem (.fork .leaf M)) (.fork .leaf N)) P = some MN := by
    have : Value.apply (f1 + 2)
        (.fork (.stem (.fork .leaf M)) (.fork .leaf N)) P = some MN := by
      simp [Value.apply]
      exact apply_mono (by omega) h1
    exact apply_mono (by omega) this
  change Value.apply (Nat.succ (f1 + f2 + 7)) (waitVal M N) P = some r
  rw [waitVal, Value.apply]
  simp [hX, hI]
  exact apply_mono (by omega) h2

/-! ### Values evaluate to themselves -/

theorem ofNat_size (n : Nat) : (Value.ofNat n).size = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Value.ofNat, Value.size, ih]
      omega

theorem size_pos (v : Value) : 0 < v.size := by
  cases v <;> simp [Value.size] <;> omega

private theorem apply_leaf_of_pos (fuel : Nat) (x : Value) (h : 0 < fuel) :
    Value.apply fuel .leaf x = some (.stem x) := by
  cases fuel with
  | zero => cases h
  | succ _ => rfl

private theorem apply_stem_of_pos (fuel : Nat) (x y : Value) (h : 0 < fuel) :
    Value.apply fuel (.stem x) y = some (.fork x y) := by
  cases fuel with
  | zero => cases h
  | succ _ => rfl

theorem eval_toTree (v : Value) :
    ∀ fuel, v.size * 2 ≤ fuel → eval fuel v.toTree = some v := by
  induction v with
  | leaf =>
      intro fuel h
      cases fuel with
      | zero => simp [Value.size] at h
      | succ _ => rfl
  | stem x ih =>
      intro fuel h
      cases fuel with
      | zero =>
          simp [Value.size] at h
          omega
      | succ fuel =>
          have hx : x.size * 2 ≤ fuel := by
            simp [Value.size] at h
            omega
          have hpos : 0 < fuel := by
            simp [Value.size] at h
            omega
          simp [Value.toTree, eval, ih fuel hx]
          exact apply_leaf_of_pos fuel x hpos
  | fork x y ihx ihy =>
      intro fuel h
      cases fuel with
      | zero =>
          simp [Value.size] at h
          omega
      | succ fuel =>
          have hx : x.size * 2 ≤ fuel := by
            simp [Value.size] at h
            omega
          have hy : y.size * 2 ≤ fuel := by
            simp [Value.size] at h
            omega
          have hxapp : eval fuel (△ ⬝ x.toTree) = some (.stem x) := by
            cases fuel with
            | zero =>
                simp [Value.size] at h
                omega
            | succ fuel' =>
                have : x.size * 2 ≤ fuel' := by
                  simp [Value.size] at h
                  omega
                have hpos : 0 < fuel' := by
                  have := size_pos x
                  omega
                simp [eval, ihx fuel' this]
                exact apply_leaf_of_pos fuel' x hpos
          have hpos : 0 < fuel := by
            simp [Value.size] at h
            omega
          simp [Value.toTree, eval, hxapp, ihy fuel hy]
          exact apply_stem_of_pos fuel x y hpos

theorem eval_ofNat (n fuel : Nat) (h : (n + 1) * 2 ≤ fuel) :
    eval fuel (Value.ofNat n).toTree = some (Value.ofNat n) := by
  have : (Value.ofNat n).size * 2 ≤ fuel := by
    rw [ofNat_size]; exact h
  exact eval_toTree (Value.ofNat n) fuel this

/-! ### Closed terms and substitution -/

def onlyFree (x : String) : Tree → Bool
  | △      => true
  | .ref y => x == y
  | f ⬝ a  => onlyFree x f && onlyFree x a

theorem substitute_not_occurs (x : String) (N M : Tree) :
    Tree.occurs x M = false → Tree.substitute x N M = M := by
  induction M with
  | node => intro _; rfl
  | ref y =>
      intro h
      simp [Tree.occurs, Tree.substitute] at h ⊢
      intro hxy
      simp [hxy] at h
  | app f a ihf iha =>
      intro h
      simp [Tree.occurs, Bool.or_eq_false_iff] at h
      simp [Tree.substitute, ihf h.1, iha h.2]

theorem occurs_onlyFree {x y : String} {M : Tree}
    (h : onlyFree x M = true) (hne : x ≠ y) : Tree.occurs y M = false := by
  induction M with
  | node => rfl
  | ref z =>
      simp [onlyFree] at h
      simp [Tree.occurs]
      have hx : x = z := by
        simpa [beq_iff_eq] using h
      intro hyz
      have hy : y = z := by
        simpa [beq_iff_eq] using hyz
      exact hne (hx.trans hy.symm)
  | app f a ihf iha =>
      simp [onlyFree, Bool.and_eq_true] at h
      simp [Tree.occurs, ihf h.1, iha h.2]

end Cas
