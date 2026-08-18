/-
  Operational star-β: if `M` mentions only `x` and `N ⇓ Nv`, then
  `star x M ⬝ N` evaluates to the same value as `substitute x N M`.
-/

import Cas.Semantics

namespace Cas

theorem evals_K : Evals K kval := ⟨2, eval_K⟩

theorem evals_I : Evals I ival := ⟨8, eval_I⟩

theorem evals_node : Evals △ .leaf := ⟨1, rfl⟩

theorem evals_K_app {M N : Tree} {Mv Nv : Value}
    (hM : Evals M Mv) (hN : Evals N Nv) :
    Evals (K ⬝ M ⬝ N) Mv :=
  evals_app (evals_app evals_K hM (applies_kval Mv)) hN (applies_K Mv Nv)

theorem evals_I_app {N : Tree} {Nv : Value} (hN : Evals N Nv) :
    Evals (I ⬝ N) Nv :=
  evals_app evals_I hN (applies_I Nv)

/-- `d A ⬝ B ⇓ fork (stem A) B`. -/
theorem evals_d_app {A B : Tree} {Av Bv : Value}
    (hA : Evals A Av) (hB : Evals B Bv) :
    Evals (d A ⬝ B) (.fork (.stem Av) Bv) := by
  obtain ⟨nA, hA⟩ := hA
  obtain ⟨nB, hB⟩ := hB
  let k := max nA nB + 1
  have hk0 : 0 < k := Nat.succ_pos _
  have hA1 : eval k A = some Av := eval_mono (by omega) hA
  have hB1 : eval (k + 2) B = some Bv := eval_mono (by omega) hB
  have hΔA : eval (k + 1) (△ ⬝ A) = some (.stem Av) := by
    rw [eval, hA1]
    have hleaf : eval k △ = some .leaf := by cases k <;> rfl
    simp [hleaf]
    exact apply_leaf_of_pos k Av hk0
  have hΔΔA : eval (k + 2) (△ ⬝ (△ ⬝ A)) = some (.stem (.stem Av)) := by
    rw [show k + 2 = Nat.succ (k + 1) from rfl, eval]
    have hleaf : eval (k + 1) △ = some .leaf := rfl
    simp [hleaf, hΔA]
    exact apply_leaf_of_pos (k + 1) (.stem Av) (Nat.succ_pos _)
  refine ⟨k + 3, ?_⟩
  rw [d, show k + 3 = Nat.succ (k + 2) from rfl, eval]
  simp [hΔΔA, hB1]
  exact apply_stem_of_pos (k + 2) (.stem Av) Bv (by omega)

private theorem onlyFree_left {x : String} {f a : Tree}
    (h : onlyFree x (f ⬝ a) = true) : onlyFree x f = true := by
  simp [onlyFree, Bool.and_eq_true] at h
  exact h.1

private theorem onlyFree_right {x : String} {f a : Tree}
    (h : onlyFree x (f ⬝ a) = true) : onlyFree x a = true := by
  simp [onlyFree, Bool.and_eq_true] at h
  exact h.2

theorem star_not_occurs (x : String) (M : Tree) (h : Tree.occurs x M = false) :
    star x M = K ⬝ M := by
  cases M with
  | node => rfl
  | ref y =>
      simp [star, Tree.occurs] at h ⊢
      intro hxy
      simp [hxy] at h
  | app _ _ =>
      simp [star, h]

theorem evals_star_node (x : String) : Evals (star x △) (.fork .leaf .leaf) := by
  simp [star]
  exact ⟨4, by native_decide⟩

/-- If the substitution evaluates, then `star x M` itself evaluates. -/
theorem evals_star (x : String) (M N : Tree) {Nv v : Value}
    (hM : onlyFree x M = true)
    (_hN : Evals N Nv)
    (hsub : Evals (Tree.substitute x N M) v) :
    ∃ sv, Evals (star x M) sv := by
  induction M generalizing v with
  | node =>
      exact ⟨.fork .leaf .leaf, evals_star_node x⟩
  | ref y =>
      simp [onlyFree] at hM
      have : x = y := by simpa [beq_iff_eq] using hM
      subst this
      simp [star]
      exact ⟨ival, evals_I⟩
  | app f a ihf iha =>
      by_cases hocc : Tree.occurs x (f ⬝ a) = true
      · have hf := onlyFree_left hM
        have ha := onlyFree_right hM
        obtain ⟨fv, av, n, hfv, hav, _⟩ := evals_app_inv (r := v) (by
          simpa [Tree.substitute] using hsub)
        obtain ⟨sf, hsf⟩ := ihf hf ⟨n, hfv⟩
        obtain ⟨sa, hsa⟩ := iha ha ⟨n, hav⟩
        refine ⟨.fork (.stem sf) sa, ?_⟩
        simpa [star, hocc] using evals_d_app hsf hsa
      · simp [star, hocc]
        have heq : Tree.substitute x N (f ⬝ a) = f ⬝ a :=
          substitute_not_occurs x N (f ⬝ a) (by simp [hocc])
        rw [heq] at hsub
        exact ⟨.fork .leaf v, evals_app evals_K hsub (applies_kval v)⟩

/-- Operational star-β. -/
theorem star_beta (x : String) (M N : Tree) {Nv v : Value}
    (hM : onlyFree x M = true)
    (hN : Evals N Nv)
    (hsub : Evals (Tree.substitute x N M) v) :
    Evals (star x M ⬝ N) v := by
  induction M generalizing v with
  | node =>
      have hv : v = .leaf := evals_det hsub evals_node
      subst hv
      simpa [star] using evals_K_app evals_node hN
  | ref y =>
      simp [onlyFree] at hM
      have : x = y := by simpa [beq_iff_eq] using hM
      subst this
      simp [star, Tree.substitute] at hsub ⊢
      have hv : v = Nv := evals_det hsub hN
      subst hv
      exact evals_I_app hN
  | app f a ihf iha =>
      by_cases hocc : Tree.occurs x (f ⬝ a) = true
      · have hf := onlyFree_left hM
        have ha := onlyFree_right hM
        obtain ⟨fv, av, n, hfv, hav, hap⟩ := evals_app_inv (r := v) (by
          simpa [Tree.substitute] using hsub)
        have hsubf : Evals (Tree.substitute x N f) fv := ⟨n, hfv⟩
        have hsuba : Evals (Tree.substitute x N a) av := ⟨n, hav⟩
        have hfN := ihf hf hsubf
        have haN := iha ha hsuba
        obtain ⟨sf, hsf⟩ := evals_star x f N hf hN hsubf
        obtain ⟨sa, hsa⟩ := evals_star x a N ha hN hsuba
        obtain ⟨sf', Nv₁, n1, hsf', hN1, hapf⟩ := evals_app_inv hfN
        obtain ⟨sa', Nv₂, n2, hsa', hN2, hapa⟩ := evals_app_inv haN
        have hsfeq : sf' = sf := evals_det ⟨n1, hsf'⟩ hsf
        have hsaeq : sa' = sa := evals_det ⟨n2, hsa'⟩ hsa
        have hNeq1 : Nv₁ = Nv := evals_det ⟨n1, hN1⟩ hN
        have hNeq2 : Nv₂ = Nv := evals_det ⟨n2, hN2⟩ hN
        have hS : Applies (.fork (.stem sf) sa) Nv v :=
          applies_S
            ⟨n1, hsfeq ▸ hNeq1 ▸ hapf⟩
            ⟨n2, hsaeq ▸ hNeq2 ▸ hapa⟩
            ⟨n, hap⟩
        have hd := evals_d_app hsf hsa
        simpa [star, hocc] using evals_app hd hN hS
      · simp [star, hocc]
        have heq : Tree.substitute x N (f ⬝ a) = f ⬝ a :=
          substitute_not_occurs x N (f ⬝ a) (by simp [hocc])
        rw [heq] at hsub
        exact evals_K_app hsub hN

/-- Convenience: star-β when `N` is already a value. -/
theorem star_beta_value (x : String) (M : Tree) (Nv v : Value)
    (hM : onlyFree x M = true)
    (hN : Evals Nv.toTree Nv)
    (hsub : Evals (Tree.substitute x Nv.toTree M) v) :
    Evals (star x M ⬝ Nv.toTree) v :=
  star_beta x M Nv.toTree hM hN hsub

end Cas
