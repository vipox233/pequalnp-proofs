import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18593_3
    (hNoCentreless :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        have J := PEqualNP.TopForm.junk x2 x4;
        have O := (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;
        have U := PEqualNP.TopForm.Ustar x2 x4;
        x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 →
        PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 →
        (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) →
        PEqualNP.TopForm.centreless x2 x4 = ∅ →
        (2 : ℕ) ≤ J.card → (1 : ℕ) ≤ O → (3 : ℕ) ≤ O → (5 : ℕ) ≤ J.card + O → (3 : ℕ) ≤ U.card →
        (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ U, ∃ x19 ∈ x16, x19 ∈ x17) → J.card + O < x16.card + U.card) →
        (∃ x17 ∈ J, ∃ (x18 x19 x20 x21 : Fin x1), s(x18, x19) ∈ U ∧ s(x20, x21) ∈ U ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) →
        False)
    (hHasCentreless :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        have J := PEqualNP.TopForm.junk x2 x4;
        have O := (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card;
        have K := (PEqualNP.TopForm.centreless x2 x4).card;
        have U := PEqualNP.TopForm.Ustar x2 x4;
        x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 →
        PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 →
        (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) →
        (PEqualNP.TopForm.centreless x2 x4).Nonempty →
        (2 : ℕ) ≤ J.card → (1 : ℕ) ≤ O → (3 : ℕ) ≤ K + O → (5 : ℕ) ≤ (2 : ℕ) * K + J.card + O → (3 : ℕ) ≤ U.card →
        (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ U, ∃ x19 ∈ x16, x19 ∈ x17) → (2 : ℕ) * K + J.card + O < x16.card + U.card) →
        (∃ x17 ∈ J, ∃ (x18 x19 x20 x21 : Fin x1), s(x18, x19) ∈ U ∧ s(x20, x21) ∈ U ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) →
        False) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∀ (x10 : Finset (Fin x1)), x2.IsVertexCover ↑x10 → x4.size + (1 : ℕ) < x2.edgeFinset.card + x10.card) → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → (1 : ℕ) ≤ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (5 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x2 x4).card → (∀ (x16 : Finset (Fin x1)), (∀ x17 ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ x19 ∈ x16, x19 ∈ x17) → (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card < x16.card + (PEqualNP.TopForm.Ustar x2 x4).card) → (∃ x17 ∈ PEqualNP.TopForm.junk x2 x4, ∃ (x18 : Fin x1) (x19 : Fin x1) (x20 : Fin x1) (x21 : Fin x1), s(x18, x19) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x20, x21) ∈ PEqualNP.TopForm.Ustar x2 x4 ∧ s(x18, x19) ≠ s(x20, x21) ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x17 (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true) → False := by
  intro x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hVC hJ hO hCO hD hU hUcov hJunk
  by_cases hc : PEqualNP.TopForm.centreless x2 x4 = ∅
  · have hCO' : (3 : ℕ) ≤ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
      rw [hc, Finset.card_empty] at hCO
      omega
    have hD' : (5 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
      rw [hc, Finset.card_empty] at hD
      omega
    have hUcov' : ∀ (x16 : Finset (Fin x1)),
        (∀ x17 ∈ PEqualNP.TopForm.Ustar x2 x4, ∃ x19 ∈ x16, x19 ∈ x17) →
        (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card <
          x16.card + (PEqualNP.TopForm.Ustar x2 x4).card := by
      intro x16 hx16
      have h := hUcov x16 hx16
      rw [hc, Finset.card_empty] at h
      omega
    exact @hNoCentreless x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hVC hc hJ hO hCO' hD' hU hUcov' hJunk
  · exact @hHasCentreless x1 x2 x3 x4 hBip hNA hC4 hLeast hTF hVC (Finset.nonempty_iff_ne_empty.mpr hc) hJ hO hCO hD hU hUcov hJunk
