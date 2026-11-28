import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_442_aux

open scoped BigOperators

private lemma zmod2_eq_zero_of_ne_one (x : ZMod 2) (h : x ≠ 1) : x = 0 := by
  revert x h; decide

private lemma zmod2_eq_one_of_ne_zero (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert x h; decide

private lemma main_proof (m s : ℕ) (F : Fin m → Finset ((Fin m × Fin s) → ZMod 2))
    (w : Fin m → Fin s)
    (hcover : ∀ i u, ∃ f ∈ F i, f (i, u) = 1)
    (hsep : ∀ i j, i ≠ j → ∀ f ∈ F i, f (j, w j) = 0) :
    let V := Submodule.span (ZMod 2) {f : (Fin m × Fin s) → ZMod 2 | ∃ i, f ∈ F i}
    ∃ (mark : Fin m → ((Fin m × Fin s) → ZMod 2)) (C : Finset ((Fin m × Fin s) → ZMod 2)),
      (∀ i, mark i ∈ F i) ∧
      (∀ i j, mark i (j, w j) = if i = j then 1 else 0) ∧
      C.card + m = Module.finrank (ZMod 2) V ∧
      (∀ c ∈ C, (∀ j, c (j, w j) = 0) ∧
        ∃ i, ∃ f ∈ F i, c = f - f (i, w i) • mark i) ∧
      (∀ i, ∀ f ∈ F i, f - f (i, w i) • mark i ∈ Submodule.span (ZMod 2) (C : Set ((Fin m × Fin s) → ZMod 2))) ∧
      ∀ i u, mark i (i, u) = 1 ∨ ∃ c ∈ C, c (i, u) = 1 := by
  classical
  intro V
  have hex_mark : ∀ i : Fin m, ∃ f ∈ F i, f (i, w i) = 1 := fun i => hcover i (w i)
  choose mark hmark_mem hmark_one using hex_mark
  have hmark_delta : ∀ i j : Fin m, mark i (j, w j) = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      exact hmark_one i
    · simp only [hij, ↓reduceIte]
      exact hsep i j hij (mark i) (hmark_mem i)
  let P := (Fin m × Fin s) → ZMod 2
  let G : Finset P :=
    Finset.univ.biUnion (fun i : Fin m => (F i).image (fun f => f - f (i, w i) • mark i))
  have hG_zero : ∀ g ∈ G, ∀ j : Fin m, g (j, w j) = 0 := by
    intro g hg j
    simp only [G, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hg
    rcases hg with ⟨i, f, hf, rfl⟩
    change f (j, w j) - f (i, w i) * mark i (j, w j) = 0
    rw [hmark_delta i j]
    by_cases hij : i = j
    · subst hij
      simp
    · simp only [hij, ↓reduceIte, mul_zero, sub_zero]
      exact hsep i j hij f hf
  have hG_form : ∀ g ∈ G, ∃ i, ∃ f ∈ F i, g = f - f (i, w i) • mark i := by
    intro g hg
    simp only [G, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hg
    rcases hg with ⟨i, f, hf, rfl⟩
    exact ⟨i, f, hf, rfl⟩
  let M : Submodule (ZMod 2) P := Submodule.span (ZMod 2) (Set.range mark)
  let W : Submodule (ZMod 2) P := Submodule.span (ZMod 2) (G : Set P)
  have hW_zero : ∀ v ∈ W, ∀ j : Fin m, v (j, w j) = 0 := by
    intro v hv j
    refine Submodule.span_induction (p := fun x _ => x (j, w j) = 0) ?_ ?_ ?_ ?_ hv
    · intro x hx
      exact hG_zero x (Finset.mem_coe.mp hx) j
    · rfl
    · intro x y _ _ hx hy
      change x (j, w j) + y (j, w j) = 0
      rw [hx, hy, zero_add]
    · intro c x _ hx
      change c * x (j, w j) = 0
      rw [hx, mul_zero]
  have hmark_li : LinearIndependent (ZMod 2) mark := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h0 : (∑ i : Fin m, g i • mark i) (j, w j) = 0 := by rw [hg]; rfl
    rw [Finset.sum_apply] at h0
    have hsum : (∑ i : Fin m, (g i • mark i) (j, w j)) = g j := by
      calc (∑ i : Fin m, (g i • mark i) (j, w j))
          = ∑ i : Fin m, g i * (if i = j then 1 else 0) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              change g i * mark i (j, w j) = _
              rw [hmark_delta i j]
        _ = ∑ i : Fin m, if i = j then g i else 0 := by
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hij : i = j <;> simp [hij]
        _ = g j := by simp
    rw [hsum] at h0
    exact h0
  have hM_finrank : Module.finrank (ZMod 2) M = m := by
    rw [finrank_span_eq_card hmark_li, Fintype.card_fin]
  have hMW_sup : M ⊔ W = V := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨i, hmark_mem i⟩
      · apply Submodule.span_le.mpr
        intro g hg
        rcases hG_form g (Finset.mem_coe.mp hg) with ⟨i, f, hf, rfl⟩
        exact V.sub_mem (Submodule.subset_span ⟨i, hf⟩)
          (V.smul_mem _ (Submodule.subset_span ⟨i, hmark_mem i⟩))
    · apply Submodule.span_le.mpr
      rintro f ⟨i, hf⟩
      have hdecomp : f = f (i, w i) • mark i + (f - f (i, w i) • mark i) := by abel
      rw [hdecomp]
      refine Submodule.add_mem_sup ?_ ?_
      · exact M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
      · exact Submodule.subset_span (Finset.mem_coe.mpr (by
          simp only [G, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨i, f, hf, rfl⟩))
  have hMW_inf : M ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rcases hv with ⟨hvM, hvW⟩
    let b := Module.Basis.span hmark_li
    have hv_sum : (∑ i : Fin m, b.repr ⟨v, hvM⟩ i • mark i) = v := by
      have h1 := b.sum_repr ⟨v, hvM⟩
      have h2 := congr_arg Subtype.val h1
      simpa [b] using h2
    have hcoeff : ∀ j : Fin m, b.repr ⟨v, hvM⟩ j = 0 := by
      intro j
      have h0 : v (j, w j) = 0 := hW_zero v hvW j
      rw [← hv_sum, Finset.sum_apply] at h0
      have hsum : (∑ i : Fin m, (b.repr ⟨v, hvM⟩ i • mark i) (j, w j)) = b.repr ⟨v, hvM⟩ j := by
        calc (∑ i : Fin m, (b.repr ⟨v, hvM⟩ i • mark i) (j, w j))
            = ∑ i : Fin m, b.repr ⟨v, hvM⟩ i * (if i = j then 1 else 0) := by
                refine Finset.sum_congr rfl fun i _ => ?_
                change b.repr ⟨v, hvM⟩ i * mark i (j, w j) = _
                rw [hmark_delta i j]
          _ = ∑ i : Fin m, if i = j then b.repr ⟨v, hvM⟩ i else 0 := by
                refine Finset.sum_congr rfl fun i _ => ?_
                by_cases hij : i = j <;> simp [hij]
          _ = b.repr ⟨v, hvM⟩ j := by simp
      rw [hsum] at h0
      exact h0
    rw [Submodule.mem_bot, ← hv_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [hcoeff i, zero_smul]
  have hW_finrank : Module.finrank (ZMod 2) W + m = Module.finrank (ZMod 2) V := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq M W
    rw [hMW_sup, hMW_inf, finrank_bot, add_zero, hM_finrank, add_comm] at hmod
    exact hmod.symm
  obtain ⟨S, hSG, hS_span, hS_li⟩ := exists_linearIndependent (ZMod 2) (G : Set P)
  let C : Finset P := S.toFinset
  have hC_coe : (C : Set P) = S := Set.coe_toFinset S
  have hC_sub : C ⊆ G := by
    intro c hc
    exact Finset.mem_coe.mp (hSG (Set.mem_toFinset.mp hc))
  have hC_span : Submodule.span (ZMod 2) (C : Set P) = W := by
    rw [hC_coe]
    exact hS_span
  have hC_card : C.card = Module.finrank (ZMod 2) W := by
    have h1 := finrank_span_set_eq_card (R := ZMod 2) hS_li
    rw [hS_span] at h1
    exact h1.symm
  refine ⟨mark, C, hmark_mem, hmark_delta, ?_, ?_, ?_, ?_⟩
  · rw [hC_card]
    exact hW_finrank
  · intro c hc
    have hcG : c ∈ G := hC_sub hc
    exact ⟨hG_zero c hcG, hG_form c hcG⟩
  · intro i f hf
    rw [hC_span]
    exact Submodule.subset_span (Finset.mem_coe.mpr (by
      simp only [G, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨i, f, hf, rfl⟩))
  · intro i u
    by_cases hm : mark i (i, u) = 1
    · exact Or.inl hm
    · right
      have hm0 : mark i (i, u) = 0 := zmod2_eq_zero_of_ne_one _ hm
      obtain ⟨f, hf, hfu⟩ := hcover i u
      let g : P := f - f (i, w i) • mark i
      have hg_mem : g ∈ Submodule.span (ZMod 2) (C : Set P) := by
        rw [hC_span]
        exact Submodule.subset_span (Finset.mem_coe.mpr (by
          simp only [G, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
          exact ⟨i, f, hf, rfl⟩))
      have hgu : g (i, u) = 1 := by
        change f (i, u) - f (i, w i) * mark i (i, u) = 1
        rw [hfu, hm0, mul_zero, sub_zero]
      by_contra hno
      push Not at hno
      have hall0 : ∀ c ∈ C, c (i, u) = 0 := fun c hc => zmod2_eq_zero_of_ne_one _ (hno c hc)
      have hg0 : g (i, u) = 0 := by
        refine Submodule.span_induction (p := fun x _ => x (i, u) = 0) ?_ ?_ ?_ ?_ hg_mem
        · intro c hc
          exact hall0 c (Finset.mem_coe.mp hc)
        · rfl
        · intro x y _ _ hx hy
          change x (i, u) + y (i, u) = 0
          rw [hx, hy, zero_add]
        · intro c x _ hx
          change c * x (i, u) = 0
          rw [hx, mul_zero]
      rw [hgu] at hg0
      exact one_ne_zero hg0

end PEqualNP.Outside.L_pcx_442_aux

theorem PEqualNP.Outside.L_pcx_442 :
  ∀ m s : ℕ,
  let K := ZMod 2
  let I := Fin m
  let U := Fin s
  let P := (I × U) → K
  ∀ (F : I → Finset P) (w : I → U),
    (∀ i u, ∃ f ∈ F i, f (i,u) = 1) →
    (∀ i j, i ≠ j → ∀ f ∈ F i, f (j,w j) = 0) →
    let V := Submodule.span K {f : P | ∃ i, f ∈ F i}
    ∃ (mark : I → P) (C : Finset P),
      (∀ i, mark i ∈ F i) ∧
      (∀ i j, mark i (j,w j) = if i = j then 1 else 0) ∧
      C.card + m = Module.finrank K V ∧
      (∀ c ∈ C, (∀ j, c (j,w j) = 0) ∧
        ∃ i, ∃ f ∈ F i, c = f - f (i,w i) • mark i) ∧
      (∀ i, ∀ f ∈ F i, f - f (i,w i) • mark i ∈ Submodule.span K (C : Set P)) ∧
      ∀ i u, mark i (i,u) = 1 ∨ ∃ c ∈ C, c (i,u) = 1 := by
  intro m s
  dsimp only
  intro F w hcover hsep
  exact PEqualNP.Outside.L_pcx_442_aux.main_proof m s F w hcover hsep
