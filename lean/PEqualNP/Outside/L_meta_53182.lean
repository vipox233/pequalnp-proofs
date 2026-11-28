import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53182_aux

lemma order_exists {α : Type} [DecidableEq α] (B D : Finset α) (Q : Finset α → α → Prop)
    (step : ∀ U : Finset α, B ⊆ U → U ⊆ D → U ≠ D → ∃ y ∈ D, y ∉ U ∧ Q U y) :
    ∀ (k : ℕ) (U : Finset α), B ⊆ U → U ⊆ D → (D \ U).card = k →
      ∃ w : Fin k → α, Function.Injective w ∧ (∀ i, w i ∈ D \ U) ∧
        ∀ i (S : Finset α), (∀ z, z ∈ S ↔ z ∈ U ∨ ∃ j, j < i ∧ w j = z) → Q S (w i) := by
  intro k
  induction k with
  | zero =>
    intro U _ _ _
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro U hBU hUD hcard
    have hne : U ≠ D := by
      intro h
      subst h
      simp at hcard
    obtain ⟨y, hyD, hyU, hQy⟩ := step U hBU hUD hne
    have hcard' : (D \ insert y U).card = k := by
      have h1 : D \ insert y U = (D \ U).erase y := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        tauto
      rw [h1, Finset.card_erase_of_mem (by simp [hyD, hyU]), hcard]
      rfl
    have hsub : insert y U ⊆ D := Finset.insert_subset hyD hUD
    obtain ⟨w', hinj, hmem, hQ⟩ :=
      ih (insert y U) (hBU.trans (Finset.subset_insert y U)) hsub hcard'
    refine ⟨(Fin.cons y w' : Fin (k + 1) → α), ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hinj⟩
      rintro ⟨i, hi⟩
      have := hmem i
      rw [hi] at this
      simp at this
    · intro i
      cases i using Fin.cases with
      | zero => simp [hyD, hyU]
      | succ i =>
        have := hmem i
        simp only [Fin.cons_succ]
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at this ⊢
        exact ⟨this.1, this.2.2⟩
    · intro i S hS
      cases i using Fin.cases with
      | zero =>
        have hSU : S = U := by
          ext z
          rw [hS]
          simp
        rw [hSU]
        simpa using hQy
      | succ i =>
        simp only [Fin.cons_succ]
        apply hQ i S
        intro z
        rw [hS]
        simp only [Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.succ_lt_succ_iff,
          Finset.mem_insert, Fin.succ_pos, true_and]
        constructor
        · rintro (h | h | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h.symm)
          · exact Or.inr h
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)

end PEqualNP.Outside.L_meta_53182_aux

open PEqualNP.Outside.L_meta_53182_aux in
theorem PEqualNP.Outside.L_meta_53182 : ∀ (α : Type) [DecidableEq α] (inv : α → α), Function.Involutive inv →
  ∀ (A D : Finset α), A ⊆ D → ∀ (P : Finset α → α → Prop),
  (∀ U V : Finset α, U ⊆ V → ∀ x, P U x → P V x) →
  ∀ H : Finset (Finset α),
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let pair := fun x => ({x, inv x} : Finset α)
  let eligible := (D.filter (fun x => inv x ∈ D ∧ inv x ≠ x ∧ ¬ (x ∈ A ∧ inv x ∈ A))).image pair
  let N := (D \ A).card
  (∃ w : Fin N → α, Function.Injective w ∧ Finset.univ.image w = D \ A ∧
    let prior := fun (i : Fin N) => A ∪ ((Finset.univ.filter (fun j => j < i)).image w)
    let used := Finset.univ.filter (fun i => pair (w i) ∈ H ∧ inv (w i) ∈ prior i)
    used.image (fun i => pair (w i)) = H ∧ used.card = H.card ∧
    ∀ i, i ∉ used → P (prior i) (w i)) ↔
  H ⊆ eligible ∧ ∀ U : Finset α, A ⊆ U → U ⊂ D →
    (∀ y ∈ D, P U y → y ∈ U) →
    ∃ x ∈ U, inv x ∉ U ∧ pair x ∈ H := by
  intro α _ inv hinv A D hAD P hP H pair eligible N
  have hpinv : ∀ x, pair (inv x) = pair x := by
    intro x
    ext y
    simp only [pair, Finset.mem_insert, Finset.mem_singleton, hinv x]
    tauto
  have hmp : ∀ x y, y ∈ pair x ↔ y = x ∨ y = inv x := by
    intro x y
    simp [pair]
  constructor
  · rintro ⟨w, hw, himg, h1, h2, h3⟩
    have hmemimg : ∀ z, (∃ i, w i = z) ↔ (z ∈ D ∧ z ∉ A) := by
      intro z
      have := congrArg (fun s => z ∈ s) himg
      simpa using this
    have hwm : ∀ i, w i ∈ D ∧ w i ∉ A := fun i => (hmemimg (w i)).mp ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · intro h hh
      rw [← h1] at hh
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union] at hh
      obtain ⟨i, ⟨_, hinvp⟩, rfl⟩ := hh
      simp only [eligible, Finset.mem_image, Finset.mem_filter]
      refine ⟨w i, ⟨(hwm i).1, ?_, ?_, ?_⟩, rfl⟩
      · rcases hinvp with h | ⟨j, _, hj⟩
        · exact hAD h
        · rw [← hj]
          exact (hwm j).1
      · intro heq
        rw [heq] at hinvp
        rcases hinvp with h | ⟨j, hj, hj'⟩
        · exact (hwm i).2 h
        · have := hw hj'
          rw [this] at hj
          exact lt_irrefl _ hj
      · intro h
        exact (hwm i).2 h.1
    · intro U hAU hUD hcl
      obtain ⟨d, hdD, hdU⟩ := Finset.exists_of_ssubset hUD
      have hdA : d ∉ A := fun h => hdU (hAU h)
      obtain ⟨i, hi⟩ := (hmemimg d).mpr ⟨hdD, hdA⟩
      let S := Finset.univ.filter (fun i => w i ∉ U)
      have hS : S.Nonempty := ⟨i, by simp [S, hi, hdU]⟩
      let i0 := S.min' hS
      have hi0 : w i0 ∉ U := by
        have := S.min'_mem hS
        simpa [S] using this
      have hlt : ∀ j, j < i0 → w j ∈ U := by
        intro j hj
        by_contra hjU
        have : i0 ≤ j := S.min'_le j (by simp [S, hjU])
        exact absurd hj (not_lt.mpr this)
      have h3' := h3 i0
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_image] at h3'
      by_cases hu : pair (w i0) ∈ H ∧
          (inv (w i0) ∈ A ∨ ∃ j, j < i0 ∧ w j = inv (w i0))
      · refine ⟨inv (w i0), ?_, ?_, ?_⟩
        · rcases hu.2 with h | ⟨j, hj, hj'⟩
          · exact hAU h
          · rw [← hj']
            exact hlt j hj
        · rw [hinv]
          exact hi0
        · rw [hpinv]
          exact hu.1
      · exfalso
        have hP0 := h3' (by simpa using hu)
        apply hi0
        apply hcl _ (hwm i0).1
        refine hP _ U ?_ _ hP0
        intro z hz
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and] at hz
        rcases hz with h | ⟨j, hj, rfl⟩
        · exact hAU h
        · exact hlt j hj
  · rintro ⟨hHe, hcross⟩
    have hstep : ∀ U : Finset α, A ⊆ U → U ⊆ D → U ≠ D →
        ∃ y ∈ D, y ∉ U ∧ (P U y ∨ (pair y ∈ H ∧ inv y ∈ U)) := by
      intro U hAU hUD hne
      by_cases hc : ∃ y ∈ D, y ∉ U ∧ P U y
      · obtain ⟨y, hy, hyU, hPy⟩ := hc
        exact ⟨y, hy, hyU, Or.inl hPy⟩
      · have hcl : ∀ y ∈ D, P U y → y ∈ U := by
          intro y hy hPy
          by_contra hyU
          exact hc ⟨y, hy, hyU, hPy⟩
        obtain ⟨x, hxU, hixU, hxH⟩ :=
          hcross U hAU (Finset.ssubset_iff_subset_ne.mpr ⟨hUD, hne⟩) hcl
        have hel := hHe hxH
        simp only [eligible, Finset.mem_image, Finset.mem_filter] at hel
        obtain ⟨z, ⟨hzD, hizD, _, _⟩, hz⟩ := hel
        have hixD : inv x ∈ D := by
          have : inv x ∈ pair z := by
            rw [hz, hmp]
            exact Or.inr rfl
          rw [hmp] at this
          rcases this with h | h
          · rw [h]; exact hzD
          · rw [h]; exact hizD
        refine ⟨inv x, hixD, hixU, Or.inr ⟨?_, ?_⟩⟩
        · rw [hpinv]
          exact hxH
        · rw [hinv]
          exact hxU
    have hN : (D \ A).card = N := by
      congr
      exact Subsingleton.elim _ _
    obtain ⟨w, hw, hwm, hQ⟩ :=
      order_exists A D (fun U y => P U y ∨ (pair y ∈ H ∧ inv y ∈ U)) hstep N A
        (Finset.Subset.refl A) hAD hN
    have himg0 : Finset.univ.image w = D \ A := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
        exact hwm i
      · rw [Finset.card_image_of_injective _ hw, Finset.card_univ, Fintype.card_fin]
        exact hN.le
    have hwm' : ∀ i, w i ∈ D ∧ w i ∉ A := fun i => Finset.mem_sdiff.mp (hwm i)
    have hfind : ∀ d, d ∈ D → d ∉ A → ∃ i, w i = d := by
      intro d hd hdA
      have : d ∈ Finset.univ.image w := by
        rw [himg0]
        exact Finset.mem_sdiff.mpr ⟨hd, hdA⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp this
      exact ⟨i, hi⟩
    refine ⟨w, hw, ?_, ?_⟩
    · ext z
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_sdiff]
      constructor
      · rintro ⟨i, rfl⟩
        exact hwm' i
      · rintro ⟨hz, hzA⟩
        exact hfind z hz hzA
    intro prior used
    have hpm : ∀ i z, z ∈ prior i ↔ z ∈ A ∨ ∃ j, j < i ∧ w j = z := by
      intro i z
      simp [prior]
    have hum : ∀ i, i ∈ used ↔ pair (w i) ∈ H ∧ inv (w i) ∈ prior i := by
      intro i
      simp [used]
    have hQ' : ∀ i, P (prior i) (w i) ∨ (pair (w i) ∈ H ∧ inv (w i) ∈ prior i) :=
      fun i => hQ i (prior i) (hpm i)
    have key : ∀ h, (∃ i ∈ used, pair (w i) = h) ↔ h ∈ H := by
      intro h
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ((hum i).mp hi).1
      · intro hh
        have hel := hHe hh
        simp only [eligible, Finset.mem_image, Finset.mem_filter] at hel
        obtain ⟨z, ⟨hzD, hizD, hne, hnA⟩, rfl⟩ := hel
        by_cases hzA : z ∈ A
        · have hizA : inv z ∉ A := fun h => hnA ⟨hzA, h⟩
          obtain ⟨i, hi⟩ := hfind (inv z) hizD hizA
          refine ⟨i, ?_, ?_⟩
          · rw [hum, hpm, hi, hinv, hpinv]
            exact ⟨hh, Or.inl hzA⟩
          · rw [hi, hpinv]
        · obtain ⟨i, hi⟩ := hfind z hzD hzA
          by_cases hizA : inv z ∈ A
          · refine ⟨i, ?_, ?_⟩
            · rw [hum, hpm, hi]
              exact ⟨hh, Or.inl hizA⟩
            · rw [hi]
          · obtain ⟨j, hj⟩ := hfind (inv z) hizD hizA
            have hij : i ≠ j := by
              intro h
              rw [h, hj] at hi
              exact hne hi
            rcases lt_or_gt_of_ne hij with hlt | hlt
            · refine ⟨j, ?_, ?_⟩
              · rw [hum, hpm, hj, hinv, hpinv]
                exact ⟨hh, Or.inr ⟨i, hlt, hi⟩⟩
              · rw [hj, hpinv]
            · refine ⟨i, ?_, ?_⟩
              · rw [hum, hpm, hi]
                exact ⟨hh, Or.inr ⟨j, hlt, hj⟩⟩
              · rw [hi]
    have himgH : used.image (fun i => pair (w i)) = H := by
      ext h
      rw [Finset.mem_image, key]
    refine ⟨?_, ?_, ?_⟩
    · ext h
      simp only [Finset.mem_image]
      exact key h
    · have hinj : Set.InjOn (fun i => pair (w i)) ↑used := by
        intro i hi j hj heq
        simp only [Finset.mem_coe] at hi hj
        by_contra hij
        have hwij : w i ≠ w j := fun h => hij (hw h)
        have hji : w j = inv (w i) := by
          have : w j ∈ pair (w i) := by
            have h' : pair (w i) = pair (w j) := heq
            rw [h', hmp]
            exact Or.inl rfl
          rw [hmp] at this
          rcases this with h | h
          · exact absurd h.symm hwij
          · exact h
        have hij' : w i = inv (w j) := by
          rw [hji, hinv]
        have hi2 := ((hum i).mp hi).2
        have hj2 := ((hum j).mp hj).2
        rw [hpm] at hi2 hj2
        rcases hi2 with h | ⟨k, hk, hk'⟩
        · rw [← hji] at h
          exact (hwm' j).2 h
        · rcases hj2 with h | ⟨l, hl, hl'⟩
          · rw [← hij'] at h
            exact (hwm' i).2 h
          · rw [← hji] at hk'
            rw [← hij'] at hl'
            have e1 := hw hk'
            have e2 := hw hl'
            rw [e1] at hk
            rw [e2] at hl
            exact lt_asymm hk hl
      rw [← himgH]
      exact (Finset.card_image_of_injOn hinj).symm
    · intro i hi
      rcases hQ' i with h | h
      · exact h
      · exact absurd ((hum i).mpr h) hi
