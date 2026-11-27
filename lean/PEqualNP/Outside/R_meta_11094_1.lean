import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_11094_1
    (h1 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.junk G C).Nonempty →
      G.edgeSet.ncard + G.edgeSet.ncard ≤ C.size + 1 + (PEqualNP.TopForm.junk G C).card)
    (h2 : ∃ K : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∃ u v : Fin n, G.Adj u v) →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.junk G C).Nonempty →
      (PEqualNP.TopForm.junk G C).card ≤ K * (n + 1).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x6 : Fin x2) (x7 : Fin x2), x3.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → x3.edgeSet.ncard + x3.edgeSet.ncard ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt := by
  obtain ⟨K, hK⟩ := h2
  refine ⟨K, ?_⟩
  intro n G inst C hedge hleast htop hjunk
  have hb : G.edgeSet.ncard + G.edgeSet.ncard ≤ C.size + 1 + (PEqualNP.TopForm.junk G C).card :=
    h1 n G C hedge hleast htop hjunk
  have hj : (PEqualNP.TopForm.junk G C).card ≤ K * (n + 1).sqrt :=
    hK n G C hedge hleast htop hjunk
  omega
