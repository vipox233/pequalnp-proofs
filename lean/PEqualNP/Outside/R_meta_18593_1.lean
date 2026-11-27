import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18593_1
    (hBipCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsBipartite →
      ∃ V : Finset (Fin n), G.IsVertexCover ↑V ∧ 2 * V.card ≤ n)
    (hEdgeCover : ∀ (n : ℕ) (U : Finset (Sym2 (Fin n))),
      ∃ V : Finset (Fin n), (∀ e ∈ U, ∃ v ∈ V, v ∈ e) ∧ V.card ≤ U.card)
    (hCore : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 →
      PEqualNP.TopForm.TopForm x2 x4 →
      (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) →
      (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card →
      (1 : ℕ) ≤ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card →
      (3 : ℕ) ≤ (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card →
      (5 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card →
      (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x2 x4).card →
      (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ x19 ∈ x16, x19 ∈ x17) → (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < x16.card + (PEqualNP.TopForm.Ustar x2 x4).card) →
      (2 : ℕ) * (x4.size + (1 : ℕ)) < (2 : ℕ) * x2.edgeFinset.card + x1 →
      (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x2 x4).card →
      (∃ x17 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x18 : Fin x1) (x19 : Fin x1) (x20 : Fin x1) (x21 : Fin x1), s(x18, x19) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x20, x21) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) →
      False) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (1 : ℕ) ≤ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (5 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x2 x4).card → (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ x19 ∈ x16, x19 ∈ x17) → (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < x16.card + (PEqualNP.TopForm.Ustar x2 x4).card) → (∃ x17 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x18 : Fin x1) (x19 : Fin x1) (x20 : Fin x1) (x21 : Fin x1), s(x18, x19) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x20, x21) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) → False) := by
  intro x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hVC hJ hO hCO hD hU hUcov hJunk
  obtain ⟨V1, hV1cov, hV1card⟩ := hBipCover x1 x2 hBip
  have h1 := hVC V1 hV1cov
  obtain ⟨V2, hV2cov, hV2card⟩ := hEdgeCover x1 (PEqualNP.TopForm.Ustar x2 x4)
  have h2 := hUcov V2 hV2cov
  exact @hCore x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hVC hJ hO hCO hD hU hUcov (by omega) (by omega) hJunk
