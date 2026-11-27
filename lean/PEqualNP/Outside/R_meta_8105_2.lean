import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-8105`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_8105_2 :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g) → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) →
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) := by
  classical
  intro h1 h2 x1 x2 x3 x4
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x4.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
