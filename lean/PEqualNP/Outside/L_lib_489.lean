import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_489_aux

private theorem count_supersets (n r : Nat) (U : Finset (Fin n)) :
    (((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun S => U ⊆ S)).card =
      if U.card ≤ r then (n - U.card).choose (r - U.card) else 0 := by
  by_cases hkr : U.card ≤ r
  · simp only [hkr, ↓reduceIte]
    have hbij : (((Finset.univ : Finset (Fin n)).powersetCard r).filter (fun S => U ⊆ S)).card =
        ((Finset.univ \ U).powersetCard (r - U.card)).card := by
      refine Finset.card_bij (fun S _ => S \ U) ?_ ?_ ?_
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS ⊢
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hx ⊢
          exact hx.2
        · rw [Finset.card_sdiff_of_subset hS.2, hS.1]
      · intro S1 hS1 S2 hS2 heq
        simp only [Finset.mem_filter] at hS1 hS2
        rw [← Finset.sdiff_union_of_subset hS1.2, ← Finset.sdiff_union_of_subset hS2.2, heq]
      · intro T hT
        simp only [Finset.mem_powersetCard] at hT
        have hdisj : Disjoint T U := by
          rw [Finset.disjoint_left]
          intro x hxT hxU
          have := hT.1 hxT
          simp only [Finset.mem_sdiff] at this
          exact this.2 hxU
        refine ⟨T ∪ U, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
          refine ⟨?_, Finset.subset_union_right⟩
          rw [Finset.card_union_of_disjoint hdisj, hT.2]
          omega
        · rw [Finset.union_sdiff_cancel_right hdisj]
    rw [hbij, Finset.card_powersetCard, Finset.card_sdiff_of_subset (Finset.subset_univ U),
      Finset.card_univ, Fintype.card_fin]
  · simp only [hkr, ↓reduceIte]
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
    have hle := Finset.card_le_card hS.2
    omega

private theorem solve_489 (n r : Nat) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))) (_hr : r ≤ n) :
    let levels := (Finset.univ : Finset (Fin n)).powersetCard r
    (levels.sum (fun S => (F.filter (fun C => (C.image Prod.fst) ⊆ S)).card)) =
      F.sum (fun C => let k := (C.image Prod.fst).card
                       if k ≤ r then (n - k).choose (r - k) else 0) := by
  intro levels
  calc
    levels.sum (fun S => (F.filter (fun C => (C.image Prod.fst) ⊆ S)).card)
        = levels.sum (fun S => F.sum (fun C => if (C.image Prod.fst) ⊆ S then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro S _
            rw [Finset.card_filter]
    _ = F.sum (fun C => levels.sum (fun S => if (C.image Prod.fst) ⊆ S then 1 else 0)) :=
            Finset.sum_comm
    _ = F.sum (fun C => (levels.filter (fun S => (C.image Prod.fst) ⊆ S)).card) := by
            apply Finset.sum_congr rfl
            intro C _
            rw [Finset.card_filter]
    _ = F.sum (fun C => let k := (C.image Prod.fst).card
                         if k ≤ r then (n - k).choose (r - k) else 0) := by
            apply Finset.sum_congr rfl
            intro C _
            exact count_supersets n r (C.image Prod.fst)

end PEqualNP.Outside.L_lib_489_aux

theorem PEqualNP.Outside.L_lib_489 : ∀ (n r : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Fin n))), r ≤ n →
  let levels := (Finset.univ : Finset (Fin n)).powersetCard r
  (levels.sum (fun S => (F.filter (fun C => (C.image Prod.fst) ⊆ S)).card)) =
    F.sum (fun C => let k := (C.image Prod.fst).card
                     if k ≤ r then (n-k).choose (r-k) else 0) := by
  intro n r F hr
  exact PEqualNP.Outside.L_lib_489_aux.solve_489 n r F hr
