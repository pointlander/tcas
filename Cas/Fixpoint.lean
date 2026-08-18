/-
  Operational unfolding of `wait`, `selfApply`, `swap`, `Z` and `Y2`.

  Headline: `Y2_red` — `Y2 f ⬝ x` evaluates like `f ⬝ x ⬝ (Y2 f)`.
-/

import Cas.StarBeta

namespace Cas

theorem K_isClosed : K.isClosed = true := rfl

theorem I_isClosed : I.isClosed = true := by
  simp [I, K, Tree.isClosed]

/-! ### Evaluation inversions -/

theorem evals_cons_leaf {A : Tree} {v : Value} (h : Evals (△ ⬝ A) v) :
    ∃ Av, Evals A Av ∧ v = .stem Av := by
  obtain ⟨fv, av, n, hf, ha, hap⟩ := evals_app_inv h
  have hleaf : fv = .leaf := evals_det ⟨n, hf⟩ evals_node
  subst hleaf
  cases n with
  | zero => simp [Value.apply] at hap
  | succ n =>
      simp [Value.apply] at hap
      exact ⟨av, ⟨n + 1, ha⟩, hap.symm⟩

theorem evals_cons_stem {A B : Tree} {v : Value}
    (h : Evals ((△ ⬝ A) ⬝ B) v) :
    ∃ Av Bv, Evals A Av ∧ Evals B Bv ∧ v = .fork Av Bv := by
  obtain ⟨fv, bv, n, hf, hb, hap⟩ := evals_app_inv h
  obtain ⟨Av, hA, heq⟩ := evals_cons_leaf ⟨n, hf⟩
  subst heq
  cases n with
  | zero => simp [Value.apply] at hap
  | succ n =>
      simp [Value.apply] at hap
      exact ⟨Av, bv, hA, ⟨n + 1, hb⟩, hap.symm⟩

theorem evals_K_cons {A : Tree} {v : Value} (h : Evals (K ⬝ A) v) :
    ∃ Av, Evals A Av ∧ v = .fork .leaf Av := by
  obtain ⟨kv, av, n, hk, ha, hap⟩ := evals_app_inv h
  have : kv = kval := evals_det ⟨n, hk⟩ evals_K
  subst this
  cases n with
  | zero => simp [Value.apply] at hap
  | succ n =>
      simp [kval, Value.apply] at hap
      exact ⟨av, ⟨n + 1, ha⟩, hap.symm⟩

/-! ### Closedness of `star` -/

private theorem onlyFree_left {x : String} {f a : Tree}
    (h : onlyFree x (f ⬝ a) = true) : onlyFree x f = true := by
  simp [onlyFree, Bool.and_eq_true] at h
  exact h.1

private theorem onlyFree_right {x : String} {f a : Tree}
    (h : onlyFree x (f ⬝ a) = true) : onlyFree x a = true := by
  simp [onlyFree, Bool.and_eq_true] at h
  exact h.2

theorem onlyFree_not_occurs_closed {x : String} {M : Tree}
    (h : onlyFree x M = true) (ho : Tree.occurs x M = false) :
    M.isClosed = true := by
  induction M with
  | node => rfl
  | ref y =>
      simp [onlyFree] at h
      simp [Tree.occurs] at ho
      simp [h] at ho
  | app f a ihf iha =>
      simp [onlyFree, Bool.and_eq_true] at h
      simp [Tree.occurs, Bool.or_eq_false_iff] at ho
      simp [Tree.isClosed, ihf h.1 ho.1, iha h.2 ho.2]

theorem star_isClosed (x : String) (M : Tree) (h : onlyFree x M = true) :
    (star x M).isClosed = true := by
  induction M with
  | node => simp [star, K, Tree.isClosed]
  | ref y =>
      simp [onlyFree] at h
      have : x = y := by simpa [beq_iff_eq] using h
      subst this
      simp [star, I, K, Tree.isClosed]
  | app f a ihf iha =>
      by_cases hocc : Tree.occurs x (f ⬝ a) = true
      · have hf := onlyFree_left h
        have ha := onlyFree_right h
        simp [star, hocc, d, Tree.isClosed, ihf hf, iha ha]
      · have hocc' : Tree.occurs x (f ⬝ a) = false := by simp [hocc]
        have hcl := onlyFree_not_occurs_closed h hocc'
        simp [star, hocc, K]
        simpa [Tree.isClosed] using hcl

/-! ### `wait` -/

theorem evals_KM {M : Tree} {Mv : Value} (hM : Evals M Mv) :
    Evals (K ⬝ M) (.fork .leaf Mv) :=
  evals_app evals_K hM (applies_kval Mv)

theorem evals_wait {M N : Tree} {Mv Nv : Value}
    (hM : Evals M Mv) (hN : Evals N Nv) :
    Evals (wait M N) (waitVal Mv Nv) := by
  have hKM := evals_KM hM
  have hKN := evals_KM hN
  have h1 : Evals (△ ⬝ (K ⬝ M)) (.stem (.fork .leaf Mv)) :=
    evals_app evals_node hKM (applies_leaf _)
  have h2 : Evals (△ ⬝ (△ ⬝ (K ⬝ M))) (.stem (.stem (.fork .leaf Mv))) :=
    evals_app evals_node h1 (applies_leaf _)
  have h3 : Evals (△ ⬝ (△ ⬝ (K ⬝ M)) ⬝ (K ⬝ N))
      (.fork (.stem (.fork .leaf Mv)) (.fork .leaf Nv)) :=
    evals_app h2 hKN (applies_stem _ _)
  have h4 : Evals (△ ⬝ (△ ⬝ (△ ⬝ (K ⬝ M)) ⬝ (K ⬝ N)))
      (.stem (.fork (.stem (.fork .leaf Mv)) (.fork .leaf Nv))) :=
    evals_app evals_node h3 (applies_leaf _)
  have h5 : Evals (△ ⬝ (△ ⬝ (△ ⬝ (△ ⬝ (K ⬝ M)) ⬝ (K ⬝ N))))
      (.stem (.stem (.fork (.stem (.fork .leaf Mv)) (.fork .leaf Nv)))) :=
    evals_app evals_node h4 (applies_leaf _)
  simpa [wait, waitVal] using evals_app h5 evals_I (applies_stem _ _)

theorem evals_wait_app {M N P : Tree} {Mv Nv Pv MNv r : Value}
    (hM : Evals M Mv) (hN : Evals N Nv) (hP : Evals P Pv)
    (hMN : Applies Mv Nv MNv) (hr : Applies MNv Pv r) :
    Evals (wait M N ⬝ P) r :=
  evals_app (evals_wait hM hN) hP (applies_wait hMN hr)

theorem evals_wait_inv {M N : Tree} {v : Value} (h : Evals (wait M N) v) :
    ∃ Mv Nv, Evals M Mv ∧ Evals N Nv ∧ v = waitVal Mv Nv := by
  simp only [wait] at h
  obtain ⟨w, iv, n, hw, hI, hap⟩ := evals_app_inv h
  have hiv : iv = ival := evals_det ⟨n, hI⟩ evals_I
  subst hiv
  cases n with
  | zero => simp [Value.apply] at hap
  | succ n =>
      obtain ⟨Xv, hX, hweq⟩ := evals_cons_leaf ⟨n + 1, hw⟩
      subst hweq
      simp [Value.apply] at hap
      subst hap
      obtain ⟨Yv, hY, hXeq⟩ := evals_cons_leaf hX
      subst hXeq
      obtain ⟨Zv, KNv, hZ, hKN, hYeq⟩ := evals_cons_stem hY
      subst hYeq
      obtain ⟨Nv, hN, hKNeq⟩ := evals_K_cons hKN
      subst hKNeq
      obtain ⟨KMv, hKM, hZeq⟩ := evals_cons_leaf hZ
      subst hZeq
      obtain ⟨Mv, hM, hKMeq⟩ := evals_K_cons hKM
      subst hKMeq
      exact ⟨Mv, Nv, hM, hN, rfl⟩

/-! ### `selfApply` -/

theorem selfApply_eq : selfApply = d I ⬝ I := by
  simp [selfApply, star, Tree.occurs]

theorem selfApply_isClosed : selfApply.isClosed = true := by
  simp [selfApply_eq, d, I, K, Tree.isClosed]

theorem evals_selfApply : Evals selfApply (.fork (.stem ival) ival) := by
  simp [selfApply_eq]
  exact evals_d_app evals_I evals_I

theorem evals_selfApply_app {W : Tree} {w r : Value}
    (hW : Evals W w) (hWW : Evals (W ⬝ W) r) :
    Evals (selfApply ⬝ W) r := by
  obtain ⟨w₁, w₂, n, hw1, hw2, hap⟩ := evals_app_inv hWW
  have e1 : w₁ = w := evals_det ⟨n, hw1⟩ hW
  have e2 : w₂ = w := evals_det ⟨n, hw2⟩ hW
  rw [e1, e2] at hap
  exact evals_app evals_selfApply hW
    (applies_S (applies_I w) (applies_I w) ⟨n, hap⟩)

/-! ### `swap` for a closed `f` -/

theorem star_y_swap_body (f : Tree) (hy : Tree.occurs "y" f = false) :
    star "y" (f ⬝ .ref "y" ⬝ .ref "x") =
      d (d (K ⬝ f) ⬝ I) ⬝ (K ⬝ .ref "x") := by
  have hyx : ("y" == "x") = false := by decide
  have hsf : star "y" f = K ⬝ f := star_not_occurs "y" f hy
  simp [star, Tree.occurs, hy, hyx, hsf]

theorem onlyFree_x_swap_inner (f : Tree) (h : f.isClosed = true) :
    onlyFree "x" (star "y" (f ⬝ .ref "y" ⬝ .ref "x")) = true := by
  rw [star_y_swap_body f (occurs_closed "y" h)]
  have hf : onlyFree "x" f = true := isClosed_onlyFree "x" h
  have hK : onlyFree "x" K = true := isClosed_onlyFree "x" K_isClosed
  have hI : onlyFree "x" I = true := isClosed_onlyFree "x" I_isClosed
  simp [onlyFree, d, hf, hK, hI]

theorem subst_x_swap_inner (f X : Tree) (h : f.isClosed = true) :
    Tree.substitute "x" X (star "y" (f ⬝ .ref "y" ⬝ .ref "x")) =
      d (d (K ⬝ f) ⬝ I) ⬝ (K ⬝ X) := by
  rw [star_y_swap_body f (occurs_closed "y" h)]
  have hf : Tree.occurs "x" f = false := occurs_closed "x" h
  simp [Tree.substitute, d, K, I, substitute_not_occurs "x" X f hf]

theorem swap_isClosed (f : Tree) (h : f.isClosed = true) :
    (swap f).isClosed = true := by
  simpa [swap] using star_isClosed "x" _ (onlyFree_x_swap_inner f h)

theorem evals_swap {f : Tree} {fv : Value}
    (hclosed : f.isClosed = true) (hf : Evals f fv) :
    ∃ sv, Evals (swap f) sv :=
  evals_star "x" (star "y" (f ⬝ .ref "y" ⬝ .ref "x")) △
    (onlyFree_x_swap_inner f hclosed) evals_node
    (by
      rw [subst_x_swap_inner f △ hclosed]
      exact evals_d_app (evals_d_app (evals_KM hf) evals_I)
        (evals_KM evals_node))

/-- `swap f ⬝ x ⬝ y` evaluates like `f ⬝ y ⬝ x`. -/
theorem swap_red {f x y : Tree} {fv xv yv r : Value}
    (hclosed : f.isClosed = true)
    (hf : Evals f fv) (hx : Evals x xv) (hy : Evals y yv)
    (hr : Evals (f ⬝ y ⬝ x) r) :
    Evals (swap f ⬝ x ⬝ y) r := by
  obtain ⟨fy, xv', n, hfyT, hx', hap⟩ := evals_app_inv hr
  obtain ⟨fv', yv', n2, hf', hy', hfyApp⟩ := evals_app_inv ⟨n, hfyT⟩
  have hfeq : fv' = fv := evals_det ⟨n2, hf'⟩ hf
  have hyeq : yv' = yv := evals_det ⟨n2, hy'⟩ hy
  have hxeq : xv' = xv := evals_det ⟨n, hx'⟩ hx
  rw [hfeq, hyeq] at hfyApp
  rw [hxeq] at hap
  have hswapX :
      Evals (swap f ⬝ x)
        (.fork (.stem (.fork (.stem (.fork .leaf fv)) ival)) (.fork .leaf xv)) := by
    simpa [swap] using
      star_beta "x" (star "y" (f ⬝ .ref "y" ⬝ .ref "x")) x
        (onlyFree_x_swap_inner f hclosed) hx
        (by
          rw [subst_x_swap_inner f x hclosed]
          exact evals_d_app (evals_d_app (evals_KM hf) evals_I) (evals_KM hx))
  exact evals_app hswapX hy
    (applies_S
      (applies_S (applies_K fv yv) (applies_I yv) ⟨n2, hfyApp⟩)
      (applies_K xv yv)
      ⟨n, hap⟩)

/-! ### `Z` and `Y2` -/

def zBody (f : Tree) : Tree :=
  star "s" (f ⬝ wait selfApply (.ref "s"))

theorem Z_eq (f : Tree) : Z f = wait selfApply (zBody f) := rfl

theorem onlyFree_zBody (f : Tree) (h : f.isClosed = true) :
    onlyFree "s" (f ⬝ wait selfApply (.ref "s")) = true := by
  have hf : onlyFree "s" f = true := isClosed_onlyFree "s" h
  have hSA : onlyFree "s" selfApply = true :=
    isClosed_onlyFree "s" selfApply_isClosed
  have hK : onlyFree "s" K = true := isClosed_onlyFree "s" K_isClosed
  have hI : onlyFree "s" I = true := isClosed_onlyFree "s" I_isClosed
  simp [onlyFree, wait, hf, hSA, hK, hI]

theorem subst_zBody (f B : Tree) (h : f.isClosed = true) :
    Tree.substitute "s" B (f ⬝ wait selfApply (.ref "s")) =
      f ⬝ wait selfApply B := by
  have hf : Tree.occurs "s" f = false := occurs_closed "s" h
  have hSA : Tree.occurs "s" selfApply = false :=
    occurs_closed "s" selfApply_isClosed
  have hK : Tree.occurs "s" K = false := occurs_closed "s" K_isClosed
  have hI : Tree.occurs "s" I = false := occurs_closed "s" I_isClosed
  rw [Tree.substitute, substitute_not_occurs "s" B f hf]
  simp [wait, Tree.substitute,
    substitute_not_occurs "s" B selfApply hSA,
    substitute_not_occurs "s" B K hK,
    substitute_not_occurs "s" B I hI]

theorem zBody_isClosed (f : Tree) (h : f.isClosed = true) :
    (zBody f).isClosed = true :=
  star_isClosed "s" _ (onlyFree_zBody f h)

theorem Y2_isClosed (f : Tree) (h : f.isClosed = true) :
    (Y2 f).isClosed = true := by
  have hsw := swap_isClosed f h
  have hzb := zBody_isClosed (swap f) hsw
  rw [Y2, Z_eq, wait]
  simp [Tree.isClosed, selfApply_isClosed, hzb, K, I]

/-- `Z f ⬝ x` evaluates like `f ⬝ (Z f) ⬝ x`. -/
theorem Z_red {f x : Tree} {fv xv zv r : Value}
    (hclosed : f.isClosed = true)
    (_hf : Evals f fv) (hx : Evals x xv)
    (hZ : Evals (Z f) zv)
    (hr : Evals (f ⬝ Z f ⬝ x) r) :
    Evals (Z f ⬝ x) r := by
  obtain ⟨fz, xv', n, hfz, hx', hap⟩ := evals_app_inv hr
  have hxeq : xv' = xv := evals_det ⟨n, hx'⟩ hx
  rw [hxeq] at hap
  have hZwait : Evals (wait selfApply (zBody f)) zv := by
    rwa [Z_eq] at hZ
  obtain ⟨_sav, bv, _hSA, hb, _⟩ := evals_wait_inv hZwait
  have hsub : Evals (Tree.substitute "s" (zBody f)
      (f ⬝ wait selfApply (.ref "s"))) fz := by
    rw [subst_zBody f (zBody f) hclosed, ← Z_eq]
    exact ⟨n, hfz⟩
  have hβ : Evals (zBody f ⬝ zBody f) fz :=
    star_beta "s" (f ⬝ wait selfApply (.ref "s")) (zBody f)
      (onlyFree_zBody f hclosed) hb hsub
  have hSAapp : Evals (selfApply ⬝ zBody f) fz :=
    evals_selfApply_app hb hβ
  obtain ⟨sav, bv', ns, hs1, hb1, haps⟩ := evals_app_inv hSAapp
  have hsaveq : sav = .fork (.stem ival) ival :=
    evals_det ⟨ns, hs1⟩ evals_selfApply
  have hbveq : bv' = bv := evals_det ⟨ns, hb1⟩ hb
  rw [hsaveq, hbveq] at haps
  have hZx : Evals (wait selfApply (zBody f) ⬝ x) r :=
    evals_wait_app evals_selfApply hb hx ⟨ns, haps⟩ ⟨n, hap⟩
  rwa [← Z_eq] at hZx

/-- `Y2 f ⬝ x` evaluates like `f ⬝ x ⬝ (Y2 f)`. -/
theorem Y2_red {f x : Tree} {fv xv y2v r : Value}
    (hclosed : f.isClosed = true)
    (hf : Evals f fv) (hx : Evals x xv) (hy2 : Evals (Y2 f) y2v)
    (hr : Evals (f ⬝ x ⬝ Y2 f) r) :
    Evals (Y2 f ⬝ x) r := by
  have hswapc : (swap f).isClosed = true := swap_isClosed f hclosed
  obtain ⟨sv, hsv⟩ := evals_swap hclosed hf
  have hswapX : Evals (swap f ⬝ Y2 f ⬝ x) r :=
    swap_red hclosed hf hy2 hx hr
  have hy2Z : Evals (Z (swap f)) y2v := by
    rwa [Y2] at hy2
  have hZ : Evals (Z (swap f) ⬝ x) r :=
    Z_red hswapc hsv hx hy2Z hswapX
  rwa [Y2]

end Cas
