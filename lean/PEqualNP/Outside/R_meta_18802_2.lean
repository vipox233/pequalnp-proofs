import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18802_2
    (hCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Sym2 (Fin n))),
      U ⊆ G.edgeFinset →
      ∃ V : Finset (Fin n), (∀ a b : Fin n, G.Adj a b → s(a, b) ∈ U → a ∈ V ∨ b ∈ V) ∧ V.card ≤ U.card)
    (hHard : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x4).card → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → s(x12, x13) ∈ PEqualNP.TopForm.Ustar x2 x4 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro x1 x2 x3 x4 hC4 hNE hLeast hTF hU hJ
  by_cases hsmall : (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x4).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card
  · have hsub : PEqualNP.TopForm.Ustar x2 x4 ⊆ x2.edgeFinset := by
      intro e he
      exact (Finset.mem_sdiff.mp he).1
    obtain ⟨V, hcov, hcard⟩ := @hCover x1 x2 x3 (PEqualNP.TopForm.Ustar x2 x4) hsub
    refine ⟨V, ?_, ?_⟩
    · exact hcov
    · omega
  · exact @hHard x1 x2 x3 x4 hC4 hNE hLeast hTF hU hJ (by omega)
