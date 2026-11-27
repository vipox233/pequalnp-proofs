import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7866_3
    (h_match : ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) (x6 : Finset (Sym2 (Fin x2))),
      (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) →
      (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) →
      2 * x6.card ≤ x2)
    (h_core : ∃ (c : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle x3 →
      (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) →
      PEqualNP.TopForm.IsLeastAO x3 x5 →
      PEqualNP.TopForm.TopForm x3 x5 →
      (PEqualNP.TopForm.junk x3 x5).Nonempty →
      x3.edgeSet.ncard + x2 ≤ x5.size + (1 : ℕ) + c * (x2 + (1 : ℕ)).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨c, hc⟩ := h_core
  refine ⟨c, ?_⟩
  intro x2 x3 x4 x5 x6 hnf hne hleast htop hjunk hx6 hdisj
  have hm : 2 * x6.card ≤ x2 := h_match x2 x3 x6 hx6 hdisj
  have hcore : x3.edgeSet.ncard + x2 ≤ x5.size + (1 : ℕ) + c * (x2 + (1 : ℕ)).sqrt :=
    hc x2 x3 x5 hnf hne hleast htop hjunk
  omega
