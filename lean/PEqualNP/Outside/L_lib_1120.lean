import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1120

variable {n : Nat}

theorem ext_max (H : Finset (Finset (Fin n))) (X : Finset (Fin n))
    (hX : ∀ e ∈ H, ¬e ⊆ X) :
    ∃ Y, X ⊆ Y ∧ (∀ e ∈ H, ¬e ⊆ Y) ∧ ∀ i, i ∉ Y → ¬ (∀ e ∈ H, ¬e ⊆ insert i Y) := by
  classical
  obtain ⟨Y, hY, hmax⟩ := Finset.exists_max_image
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun Y => X ⊆ Y ∧ ∀ e ∈ H, ¬e ⊆ Y))
    Finset.card ⟨X, by simp; exact hX⟩
  rw [Finset.mem_filter] at hY
  refine ⟨Y, hY.2.1, hY.2.2, fun i hi hmiss => ?_⟩
  have h1 := hmax (insert i Y) (by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hY.2.1.trans (Finset.subset_insert _ _), hmiss⟩)
  rw [Finset.card_insert_of_notMem hi] at h1
  omega

theorem pair_eq (f : Finset (Fin n)) (hf : f.card = 2) (i k : Fin n) (hi : i ∈ f) (hk : k ∈ f)
    (hne : i ≠ k) : ({i, k} : Finset (Fin n)) = f := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · exact h ▸ hi
    · exact (Finset.mem_singleton.mp h) ▸ hk
  · rw [hf, Finset.card_pair hne]

theorem graphA (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = 2) (e : Finset (Fin n))
    (Y : Finset (Fin n))
    (hY : ∀ f ∈ E.erase e, ¬f ⊆ Y)
    (hmax : ∀ i, i ∉ Y → ¬ ∀ f ∈ E.erase e, ¬f ⊆ insert i Y) (heY : e ⊆ Y) :
    (∀ i ∈ Y \ e, i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E) ∧ (∀ f ∈ E, ¬f ⊆ Y \ e) ∧
    (∀ i, (i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E) → i ∉ Y \ e →
      ¬ ∀ f ∈ E, ¬f ⊆ insert i (Y \ e)) ∧ e ∪ (Y \ e) = Y := by
  refine ⟨?_, ?_, ?_, Finset.union_sdiff_of_subset heY⟩
  · intro i hi
    rw [Finset.mem_sdiff] at hi
    refine ⟨hi.2, fun j hj hij => ?_⟩
    refine hY {i,j} (Finset.mem_erase.mpr ⟨?_, hij⟩) ?_
    · intro h
      apply hi.2
      rw [← h]
      exact Finset.mem_insert_self _ _
    · intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ hi.1
      · exact (Finset.mem_singleton.mp h) ▸ heY hj
  · intro f hf hfY
    have hne : f ≠ e := by
      intro hfe
      have hc := hE f hf
      obtain ⟨x, hx⟩ : f.Nonempty := by
        rw [← Finset.card_pos]
        omega
      exact (Finset.mem_sdiff.mp (hfY hx)).2 (hfe ▸ hx)
    exact hY f (Finset.mem_erase.mpr ⟨hne, hf⟩) (hfY.trans Finset.sdiff_subset)
  · intro i hi hiX hmiss
    have hiY : i ∉ Y := fun h => hiX (Finset.mem_sdiff.mpr ⟨h, hi.1⟩)
    apply hmax i hiY
    intro f hf hfY
    have hfE := (Finset.mem_erase.mp hf).2
    apply hmiss f hfE
    have hif : i ∈ f := by
      by_contra hif
      apply hY f hf
      intro x hx
      rcases Finset.mem_insert.mp (hfY hx) with h | h
      · exact absurd (h ▸ hx) hif
      · exact h
    intro k hk
    by_cases hki : k = i
    · rw [hki]
      exact Finset.mem_insert_self _ _
    · have hkY : k ∈ Y := by
        rcases Finset.mem_insert.mp (hfY hk) with h | h
        · exact absurd h hki
        · exact h
      refine Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hkY, fun hke => ?_⟩)
      have hp := pair_eq f (hE f hfE) i k hif hk (Ne.symm hki)
      exact hi.2 k hke (by rw [hp]; exact hfE)

theorem graphB (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = 2) (e : Finset (Fin n))
    (he : e ∈ E) (X0 : Finset (Fin n))
    (hsub : ∀ i ∈ X0, i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E)
    (hm : ∀ f ∈ E, ¬f ⊆ X0)
    (hmax : ∀ i, (i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E) → i ∉ X0 →
      ¬ ∀ f ∈ E, ¬f ⊆ insert i X0) :
    (∀ f ∈ E.erase e, ¬f ⊆ e ∪ X0) ∧
      ∀ i, i ∉ e ∪ X0 → ¬ ∀ f ∈ E.erase e, ¬f ⊆ insert i (e ∪ X0) := by
  constructor
  · intro f hf hfB
    obtain ⟨hne, hfE⟩ := Finset.mem_erase.mp hf
    have hc := hE f hfE
    have h1 : ∃ j ∈ f, j ∈ e := by
      by_contra h
      push_neg at h
      apply hm f hfE
      intro x hx
      rcases Finset.mem_union.mp (hfB hx) with h' | h'
      · exact absurd h' (h x hx)
      · exact h'
    obtain ⟨j, hjf, hje⟩ := h1
    have h2 : ∃ k ∈ f, k ∉ e := by
      by_contra h
      push_neg at h
      exact hne (Finset.eq_of_subset_of_card_le h (by rw [hc, hE e he]))
    obtain ⟨k, hkf, hke⟩ := h2
    have hkX : k ∈ X0 := by
      rcases Finset.mem_union.mp (hfB hkf) with h' | h'
      · exact absurd h' hke
      · exact h'
    have hkj : k ≠ j := fun h => hke (h ▸ hje)
    have hp := pair_eq f hc k j hkf hjf hkj
    exact (hsub k hkX).2 j hje (by rw [hp]; exact hfE)
  · intro i hi hmiss
    rw [Finset.mem_union, not_or] at hi
    by_cases ho : ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E
    · apply hmax i ⟨hi.1, ho⟩ hi.2
      intro f hfE hfi
      refine hmiss f (Finset.mem_erase.mpr ⟨?_, hfE⟩) ?_
      · intro hfe
        have hc := hE f hfE
        obtain ⟨x, hx⟩ : f.Nonempty := by
          rw [← Finset.card_pos]
          omega
        have hxe : x ∈ e := hfe ▸ hx
        rcases Finset.mem_insert.mp (hfi hx) with h' | h'
        · exact hi.1 (h' ▸ hxe)
        · exact (hsub x h').1 hxe
      · exact hfi.trans (Finset.insert_subset_insert _ Finset.subset_union_right)
    · push_neg at ho
      obtain ⟨j, hje, hij⟩ := ho
      refine hmiss {i,j} (Finset.mem_erase.mpr ⟨?_, hij⟩) ?_
      · intro h
        apply hi.1
        rw [← h]
        exact Finset.mem_insert_self _ _
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]
          exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton.mp h]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hje)

theorem suff (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = 2)
    (D : Finset (Finset (Fin n))) (hD : D ⊆ E) (Q : Finset (Finset (Fin n)))
    (H : Finset (Finset (Fin n))) (hH : H = E ∨ ∃ e ∈ D, H = E.erase e)
    (hQE : E ⊆ Q)
    (hQb : ∀ Y : Finset (Fin n), (∀ f ∈ E, ¬f ⊆ Y) → (∀ i, i ∉ Y → ¬ ∀ f ∈ E, ¬f ⊆ insert i Y) → Y ∈ Q)
    (hQo : ∀ e ∈ D, ∀ X : Finset (Fin n),
      (∀ i ∈ X, i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E) → (∀ f ∈ E, ¬f ⊆ X) →
      (∀ i, (i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E) → i ∉ X →
        ¬ ∀ f ∈ E, ¬f ⊆ insert i X) → e ∪ X ∈ Q)
    (C : Finset (Fin n) → Bool)
    [dec : ∀ X : Finset (Fin n), Decidable (∀ e ∈ H, ¬e ⊆ X)]
    (hmono : ∀ X Y : Finset (Fin n), X ⊆ Y → C X = true → C Y = true)
    (hCQ : ∀ X ∈ Q, C X = !decide (∀ e ∈ H, ¬e ⊆ X)) :
    ∀ X, C X = !decide (∀ e ∈ H, ¬e ⊆ X) := by
  intro X
  have hHE : H ⊆ E := by
    rcases hH with h | ⟨e, -, h⟩
    · rw [h]
    · rw [h]
      exact Finset.erase_subset _ _
  by_cases hX : ∀ e ∈ H, ¬e ⊆ X
  · obtain ⟨Y, hXY, hY, hYmax⟩ := ext_max H X hX
    have hYQ : Y ∈ Q := by
      by_cases hEY : ∀ e ∈ E, ¬e ⊆ Y
      · exact hQb Y hEY (fun i hi hm => hYmax i hi (fun e he => hm e (hHE he)))
      · rcases hH with h | ⟨e, heD, h⟩
        · rw [h] at hY
          exact absurd hY hEY
        · rw [h] at hY hYmax
          push_neg at hEY
          obtain ⟨e', he', he'Y⟩ := hEY
          have hee : e' = e := by
            by_contra hne
            exact hY e' (Finset.mem_erase.mpr ⟨hne, he'⟩) he'Y
          rw [hee] at he'Y
          obtain ⟨h1, h2, h3, h4⟩ := graphA E hE e Y hY hYmax he'Y
          rw [← h4]
          exact hQo e heD _ h1 h2 h3
    have hCY := hCQ Y hYQ
    rw [decide_eq_true hY] at hCY
    have hCX : C X = false := by
      by_contra h
      have h' := hmono X Y hXY (by simpa using h)
      rw [h'] at hCY
      exact absurd hCY (by decide)
    rw [decide_eq_true hX, hCX]
    rfl
  · have hX' := hX
    push_neg at hX'
    obtain ⟨e, he, heX⟩ := hX'
    have h1 := hCQ e (hQE (hHE he))
    have h2 : ¬ ∀ e' ∈ H, ¬e' ⊆ e := fun h => h e he subset_rfl
    rw [decide_eq_false h2] at h1
    have h3 := hmono e X heX h1
    rw [decide_eq_false hX, h3]
    rfl

theorem nec_edge (E : Finset (Finset (Fin n))) (hE : ∀ e ∈ E, e.card = 2)
    (fam : Finset (Finset (Finset (Fin n)))) (hsub : ∀ H ∈ fam, H ⊆ E) (hEf : E ∈ fam)
    (ord : Bool) (Q : Finset (Finset (Fin n)))
    [inst : ∀ (H : Finset (Finset (Fin n))) (X : Finset (Fin n)), Decidable (∀ e ∈ H, ¬e ⊆ X)]
    (hdet : ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ fam, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ fam, ∀ J ∈ fam, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ fam, ∀ X ∈ Q, C H X = !decide (∀ e ∈ H, ¬e ⊆ X)) →
      ∀ H ∈ fam, ∀ X, C H X = !decide (∀ e ∈ H, ¬e ⊆ X))
    (e : Finset (Fin n)) (he : e ∈ E) : e ∈ Q := by
  by_contra heQ
  have key := hdet (fun H X => !decide (∀ e ∈ H, ¬e ⊆ X) && !decide (X = e)) ?_ ?_ ?_ E hEf e
  · have h2 : ¬ ∀ e' ∈ E, ¬e' ⊆ e := fun h => h e he subset_rfl
    simp [decide_eq_false h2] at key
  · intro H hH X Y hXY hC
    by_cases hXm : ∀ e ∈ H, ¬e ⊆ X
    · simp [decide_eq_true hXm] at hC
    · have hYm : ¬ ∀ e ∈ H, ¬e ⊆ Y := fun h => hXm (fun f hf hfX => h f hf (hfX.trans hXY))
      have hXe : X ≠ e := by simpa [decide_eq_false hXm] using hC
      have hYe : Y ≠ e := by
        intro hYe
        push_neg at hXm
        obtain ⟨f, hf, hfX⟩ := hXm
        have hfe : f = e := Finset.eq_of_subset_of_card_le (hYe ▸ hfX.trans hXY)
          (by rw [hE f (hsub H hH hf), hE e he])
        exact hXe (subset_antisymm (hYe ▸ hXY) (hfe ▸ hfX))
      simp [decide_eq_false hYm, hYe]
  · intro _ H hH J hJ hHJ X hC
    by_cases hXm : ∀ e ∈ H, ¬e ⊆ X
    · simp [decide_eq_true hXm] at hC
    · have hJm : ¬ ∀ e ∈ J, ¬e ⊆ X := fun h => hXm (fun f hf => h f (hHJ hf))
      have hXe : X ≠ e := by simpa [decide_eq_false hXm] using hC
      simp [decide_eq_false hJm, hXe]
  · intro H hH X hX
    have hXe : X ≠ e := fun h => heQ (h ▸ hX)
    simp [hXe]

theorem nec_ind (fam : Finset (Finset (Finset (Fin n)))) (H0 : Finset (Finset (Fin n)))
    (hH0 : H0 ∈ fam) (ord : Bool) (Q : Finset (Finset (Fin n)))
    [inst : ∀ (H : Finset (Finset (Fin n))) (X : Finset (Fin n)), Decidable (∀ e ∈ H, ¬e ⊆ X)]
    (hdet : ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ fam, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ fam, ∀ J ∈ fam, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ fam, ∀ X ∈ Q, C H X = !decide (∀ e ∈ H, ¬e ⊆ X)) →
      ∀ H ∈ fam, ∀ X, C H X = !decide (∀ e ∈ H, ¬e ⊆ X))
    (B : Finset (Fin n)) (hm : ∀ e ∈ H0, ¬e ⊆ B)
    (hmax : ∀ i, i ∉ B → ¬ ∀ e ∈ H0, ¬e ⊆ insert i B)
    (hup : ∀ J ∈ fam, H0 ⊆ J → J ≠ H0 → ¬ ∀ e ∈ J, ¬e ⊆ B) : B ∈ Q := by
  by_contra hBQ
  have key := hdet (fun H X => !decide (∀ e ∈ H, ¬e ⊆ X) || (decide (H = H0) && decide (X = B)))
    ?_ ?_ ?_ H0 hH0 B
  · simp [decide_eq_true hm] at key
  · intro H hH X Y hXY hC
    by_cases hY : ∀ e ∈ H, ¬e ⊆ Y
    · have hX : ∀ e ∈ H, ¬e ⊆ X := fun e he h => hY e he (h.trans hXY)
      have hC' : H = H0 ∧ X = B := by simpa [decide_eq_true hX] using hC
      have hYB : Y = B := by
        by_contra hne
        obtain ⟨i, hiY, hiX⟩ : ∃ i ∈ Y, i ∉ B := by
          by_contra h
          push_neg at h
          exact hne (subset_antisymm h (hC'.2 ▸ hXY))
        apply hmax i hiX
        intro f hf hfi
        refine hY f (hC'.1 ▸ hf) (hfi.trans ?_)
        exact Finset.insert_subset hiY (hC'.2 ▸ hXY)
      simp [hC'.1, hYB]
    · simp [decide_eq_false hY]
  · intro _ H hH J hJ hHJ X hC
    by_cases hJm : ∀ e ∈ J, ¬e ⊆ X
    · have hX : ∀ e ∈ H, ¬e ⊆ X := fun f hf => hJm f (hHJ hf)
      have hC' : H = H0 ∧ X = B := by simpa [decide_eq_true hX] using hC
      have hJ0 : J = H0 := by
        by_contra hne
        exact hup J hJ (hC'.1 ▸ hHJ) hne (hC'.2 ▸ hJm)
      simp [hJ0, hC'.2]
    · simp [decide_eq_false hJm]
  · intro H hH X hX
    have hXe : X ≠ B := fun h => hBQ (h ▸ hX)
    simp [hXe]

end PEqualNP.Outside.L_lib_1120

theorem PEqualNP.Outside.L_lib_1120 : ∀ (n : Nat) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
  let sets := (Finset.univ : Finset (Finset (Fin n)))
  let miss := fun (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) => ∀ e ∈ H, ¬e ⊆ X
  let maximal := fun (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) =>
    sets.filter (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))
  let base := maximal E Finset.univ
  ∀ D : Finset (Finset (Fin n)), D ⊆ E →
  let family := insert E (D.image (fun e => E.erase e))
  let outside := fun e : Finset (Fin n) => (Finset.univ : Finset (Fin n)).filter
    (fun i => i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E)
  let bank := E ∪ base ∪ D.biUnion (fun e => (maximal E (outside e)).image (fun X => e ∪ X))
  let determines := fun (ord : Bool) (Q : Finset (Finset (Fin n))) =>
    ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X)) →
      ∀ H ∈ family, ∀ X, C H X = !decide (miss H X)
  ∀ ord Q, determines ord Q ↔ bank ⊆ Q := by
  intro n E hE sets miss maximal base D hD family outside bank determines ord Q
  have hfamsub : ∀ H ∈ family, H ⊆ E := by
    intro H hH
    rcases Finset.mem_insert.mp hH with h | h
    · rw [h]
    · obtain ⟨e, -, h⟩ := Finset.mem_image.mp h
      rw [← h]
      exact Finset.erase_subset _ _
  have hEf : E ∈ family := Finset.mem_insert_self _ _
  have hout : ∀ (e : Finset (Fin n)) (i : Fin n),
      i ∈ outside e ↔ (i ∉ e ∧ ∀ j ∈ e, ({i,j} : Finset (Fin n)) ∉ E) := by
    intro e i
    simp [outside]
  constructor
  · intro hdet B hB
    rcases Finset.mem_union.mp hB with hB | hB
    · rcases Finset.mem_union.mp hB with hB | hB
      · exact PEqualNP.Outside.L_lib_1120.nec_edge E hE family hfamsub hEf ord Q hdet B hB
      · obtain ⟨-, -, h2, h3⟩ := Finset.mem_filter.mp hB
        refine PEqualNP.Outside.L_lib_1120.nec_ind family E hEf ord Q hdet B h2
          (fun i hi => h3 i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩)) ?_
        intro J hJ hEJ hne
        exact absurd (subset_antisymm (hfamsub J hJ) hEJ) hne
    · obtain ⟨e, heD, hB⟩ := Finset.mem_biUnion.mp hB
      obtain ⟨X0, hX0, hXB⟩ := Finset.mem_image.mp hB
      obtain ⟨-, h1, h2, h3⟩ := Finset.mem_filter.mp hX0
      obtain ⟨g1, g2⟩ := PEqualNP.Outside.L_lib_1120.graphB E hE e (hD heD) X0
        (fun i hi => (hout e i).mp (h1 hi)) h2
        (fun i hi hiX => h3 i (Finset.mem_sdiff.mpr ⟨(hout e i).mpr hi, hiX⟩))
      rw [← hXB]
      refine PEqualNP.Outside.L_lib_1120.nec_ind family (E.erase e)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ heD)) ord Q hdet _ g1 g2 ?_
      intro J hJ hsubJ hne hmiss
      have heJ : e ∈ J := by
        by_contra heJ
        apply hne
        refine subset_antisymm ?_ hsubJ
        intro f hf
        exact Finset.mem_erase.mpr ⟨fun h => heJ (h ▸ hf), hfamsub J hJ hf⟩
      exact hmiss e heJ Finset.subset_union_left
  · intro hbank C hmono _ hCQ H hH X
    refine PEqualNP.Outside.L_lib_1120.suff E hE D hD Q H ?_ ?_ ?_ ?_ (C H) (hmono H hH)
      (hCQ H hH) X
    · rcases Finset.mem_insert.mp hH with h | h
      · exact Or.inl h
      · obtain ⟨e, he, h⟩ := Finset.mem_image.mp h
        exact Or.inr ⟨e, he, h.symm⟩
    · intro f hf
      exact hbank (Finset.mem_union_left _ (Finset.mem_union_left _ hf))
    · intro Y hY hmax
      exact hbank (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.subset_univ _, hY,
          fun i hi => hmax i (Finset.mem_sdiff.mp hi).2⟩)))
    · intro e heD X' h1 h2 h3
      exact hbank (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨e, heD,
        Finset.mem_image.mpr ⟨X', Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun i hi => (hout e i).mpr (h1 i hi), h2,
          fun i hi => h3 i ((hout e i).mp (Finset.mem_sdiff.mp hi).1)
            (Finset.mem_sdiff.mp hi).2⟩, rfl⟩⟩))
