import PEqualNP.Defs

-- L-meta-25501: a pair with both rows kept gives two matched columns whose kept rows differ only where the
-- two paired rows differ (at most a), so at least gap deleted rows separate them; a deleted row separates
-- disjoint column pairs at most minority-many times, and pairs with a deleted row inject into deleted rows.
-- Double counting over (pair, deleted row) incidences then gives the bound.

namespace PEqualNP.Outside.L_meta_25501_aux

theorem full_pair (n m a gap : ℕ) (G : Fin n → Fin n → Bool)
    (rowPair : (Fin m × Bool) ↪ Fin n) (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n))
    (hrow : ∀ i, (Finset.univ.filter (fun col : Fin n =>
      G (rowPair (i, false)) col ≠ G (rowPair (i, true)) col)).card ≤ a)
    (hcol : ∀ b c : Fin n, b ≠ c →
      a + gap ≤ (Finset.univ.filter (fun row : Fin n => G row b ≠ G row c)).card)
    (hsym : ∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u))
    (i : Fin m) (hr : rowPair (i, false) ∈ kept) (hs : rowPair (i, true) ∈ kept) :
    gap ≤ ((Finset.univ \ kept).filter (fun w : Fin n =>
      G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
  have hne : π (rowPair (i, false)) ≠ π (rowPair (i, true)) := by
    intro h
    have := rowPair.injective (π.injective h)
    simp at this
  have h1 := hcol _ _ hne
  have hsub : Finset.univ.filter (fun w : Fin n =>
        G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true)))) ⊆
      kept.filter (fun w : Fin n =>
        G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true)))) ∪
      (Finset.univ \ kept).filter (fun w : Fin n =>
        G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true)))) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    by_cases hk : w ∈ kept
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hw⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩, hw⟩)
  have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h3 : (kept.filter (fun w : Fin n =>
        G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤
      (Finset.univ.filter (fun col : Fin n =>
        G (rowPair (i, false)) col ≠ G (rowPair (i, true)) col)).card := by
    apply Finset.card_le_card_of_injOn (fun w => π w)
    · intro w hw
      have hw' := Finset.mem_filter.mp hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rw [← hsym _ hw'.1 _ hr, ← hsym _ hw'.1 _ hs]
      exact hw'.2
    · intro x _ y _ hxy
      exact π.injective hxy
  have h4 := hrow i
  omega

theorem pair_minor (n m : ℕ) (G : Fin n → Fin n → Bool)
    (rowPair : (Fin m × Bool) ↪ Fin n) (π : Equiv.Perm (Fin n)) (S : Finset (Fin m)) (w : Fin n) :
    (S.filter (fun i : Fin m =>
      G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤
    min (Finset.univ.filter (fun onCol : Fin n => G w onCol = true)).card
        (Finset.univ.filter (fun offCol : Fin n => G w offCol = false)).card := by
  apply le_min
  · apply Finset.card_le_card_of_injOn
      (fun i => π (rowPair (i, G w (π (rowPair (i, true))))))
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      cases hb : G w (π (rowPair (i, true)))
      · rw [hb] at hi'
        simpa using hi'
      · exact hb
    · intro x _ y _ hxy
      have := rowPair.injective (π.injective hxy)
      exact (Prod.mk.inj this).1
  · apply Finset.card_le_card_of_injOn
      (fun i => π (rowPair (i, G w (π (rowPair (i, false))))))
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      cases hb : G w (π (rowPair (i, false)))
      · exact hb
      · rw [hb] at hi'
        simpa using hi'
    · intro x _ y _ hxy
      have := rowPair.injective (π.injective hxy)
      exact (Prod.mk.inj this).1

theorem open_pairs (n m : ℕ) (rowPair : (Fin m × Bool) ↪ Fin n) (kept : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin m =>
      ¬ (rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept))).card ≤
    (Finset.univ \ kept).card := by
  apply Finset.card_le_card_of_injOn (fun i => rowPair (i, decide (rowPair (i, false) ∈ kept)))
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
      Finset.mem_coe]
    by_cases h : rowPair (i, false) ∈ kept
    · simp only [h, decide_true]
      exact fun hs => hi' ⟨h, hs⟩
    · simp [h]
  · intro x _ y _ hxy
    have := rowPair.injective hxy
    exact (Prod.mk.inj this).1

theorem main (n m a gap : ℕ) (G : Fin n → Fin n → Bool)
    (rowPair : (Fin m × Bool) ↪ Fin n) (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n))
    (hrow : ∀ i, (Finset.univ.filter (fun col : Fin n =>
      G (rowPair (i, false)) col ≠ G (rowPair (i, true)) col)).card ≤ a)
    (hcol : ∀ b c : Fin n, b ≠ c →
      a + gap ≤ (Finset.univ.filter (fun row : Fin n => G row b ≠ G row c)).card)
    (hsym : ∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) :
    gap * m ≤ gap * (n - kept.card) +
      ∑ u ∈ Finset.univ \ kept,
        min (Finset.univ.filter (fun onCol : Fin n => G u onCol = true)).card
            (Finset.univ.filter (fun offCol : Fin n => G u offCol = false)).card := by
  classical
  set F := Finset.univ.filter (fun i : Fin m =>
      rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept) with hF
  set NF := Finset.univ.filter (fun i : Fin m =>
      ¬ (rowPair (i, false) ∈ kept ∧ rowPair (i, true) ∈ kept)) with hNF
  set D := Finset.univ \ kept with hD
  have hm : F.card + NF.card = m := by
    rw [hF, hNF, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have hDc : D.card = n - kept.card := by
    rw [hD, Finset.card_univ_sdiff, Fintype.card_fin]
  have hNFD : NF.card ≤ D.card := open_pairs n m rowPair kept
  have hfull : gap * F.card ≤ ∑ i ∈ F, (D.filter (fun w : Fin n =>
      G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
    calc gap * F.card = ∑ _i ∈ F, gap := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := (Finset.mem_filter.mp hi).2
        exact full_pair n m a gap G rowPair π kept hrow hcol hsym i hi'.1 hi'.2
  have hswap : ∑ i ∈ F, (D.filter (fun w : Fin n =>
      G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card =
      ∑ w ∈ D, (F.filter (fun i : Fin m =>
      G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hmin : ∑ w ∈ D, (F.filter (fun i : Fin m =>
      G w (π (rowPair (i, false))) ≠ G w (π (rowPair (i, true))))).card ≤
      ∑ w ∈ D, min (Finset.univ.filter (fun onCol : Fin n => G w onCol = true)).card
            (Finset.univ.filter (fun offCol : Fin n => G w offCol = false)).card := by
    apply Finset.sum_le_sum
    intro w _
    exact pair_minor n m G rowPair π F w
  have hgN : gap * NF.card ≤ gap * D.card := Nat.mul_le_mul_left _ hNFD
  rw [← hDc, ← hm, Nat.mul_add]
  omega

end PEqualNP.Outside.L_meta_25501_aux

open PEqualNP.Outside.L_meta_25501_aux in
theorem PEqualNP.Outside.L_meta_25501 :
    ∀ (n m a gap : ℕ) (G : Fin n → Fin n → Bool)
        (rowPair : (Fin m × Bool) ↪ Fin n)
        (π : Equiv.Perm (Fin n)) (kept : Finset (Fin n)),
      let rowDistance := fun (firstRow secondRow : Fin n) =>
        (Finset.univ.filter (fun col : Fin n => G firstRow col ≠ G secondRow col)).card
      let colDistance := fun (firstCol secondCol : Fin n) =>
        (Finset.univ.filter (fun row : Fin n => G row firstCol ≠ G row secondCol)).card
      let minority := fun (line : Fin n) =>
        min (Finset.univ.filter (fun onCol : Fin n => G line onCol = true)).card
            (Finset.univ.filter (fun offCol : Fin n => G line offCol = false)).card
      (∀ i, rowDistance (rowPair (i, false)) (rowPair (i, true)) ≤ a) →
      (∀ b c, b ≠ c → a + gap ≤ colDistance b c) →
      (∀ u ∈ kept, ∀ v ∈ kept, G u (π v) = G v (π u)) →
      gap * m ≤ gap * (n - kept.card) +
        ∑ u ∈ Finset.univ \ kept, minority u := by
  intro n m a gap G rowPair π kept rowDistance colDistance minority hrow hcol hsym
  exact main n m a gap G rowPair π kept hrow hcol hsym
