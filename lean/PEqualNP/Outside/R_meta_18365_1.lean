import Mathlib.Data.Nat.BitIndices
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18365_1
    (hCentrelessZero :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x3.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 →
        (PEqualNP.TopForm.centreless x1 x3).card = (0 : ℕ) →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x9 : ℕ := (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;
        (4 : ℕ) ≤ x9 → x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card ≤ (4 : ℕ) →
        ∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x14 →
        ∀ (x16 : List ℕ), List.Pairwise (fun (x17 x18 : ℕ) => x17 &&& x18 = (0 : ℕ)) x16 →
        (∀ x18 ∈ x16, x18 ∈ x2 ∧ ∀ (x20 : Fin (11 : ℕ)), x18.testBit ↑x20 = Bool.true → x20 ∉ x14) →
        ∀ x19 ∈ x16, x19.bitIndices.length ≠ (2 : ℕ) →
        (List.map (fun (x20 : ℕ) => (x20.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x16).sum ≤ x9 - x8.card)
    (hCentrelessPos :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x3.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 →
        (1 : ℕ) ≤ (PEqualNP.TopForm.centreless x1 x3).card →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;
        (4 : ℕ) ≤ x9 → x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card ≤ (4 : ℕ) →
        ∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x14 →
        ∀ (x16 : List ℕ), List.Pairwise (fun (x17 x18 : ℕ) => x17 &&& x18 = (0 : ℕ)) x16 →
        (∀ x18 ∈ x16, x18 ∈ x2 ∧ ∀ (x20 : Fin (11 : ℕ)), x18.testBit ↑x20 = Bool.true → x20 ∉ x14) →
        ∀ x19 ∈ x16, x19.bitIndices.length ≠ (2 : ℕ) →
        (List.map (fun (x20 : ℕ) => (x20.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x16).sum ≤ x9 - x8.card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           (4 : ℕ) ≤ x9 → x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card ≤ (4 : ℕ) → ∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x14 → ∀ (x16 : List ℕ), List.Pairwise (fun (x17 x18 : ℕ) => x17 &&& x18 = (0 : ℕ)) x16 → (∀ x18 ∈ x16, x18 ∈ x2 ∧ ∀ (x20 : Fin (11 : ℕ)), x18.testBit ↑x20 = Bool.true → x20 ∉ x14) → (∃ x19 ∈ x16, x19.bitIndices.length ≠ (2 : ℕ)) → (List.map (fun (x20 : ℕ) => (x20.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x16).sum ≤ x9 - x8.card := by
  intro x1 x2 x3 hSz hL hT hJ x8 x9 h4 hU9 h9U hDiff x14 hMC x16 hPW hMem hEx
  rcases hEx with ⟨x19, hx19m, hx19ne⟩
  rcases Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless x1 x3).card with h0 | hpos
  · have hx9 : x9 = (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
      dsimp only [x9]; rw [h0, Nat.mul_zero, Nat.zero_add]
    rw [hx9] at h4 hU9 h9U hDiff ⊢
    exact hCentrelessZero x3 hSz hL hT h0 hJ h4 hU9 h9U hDiff x14 hMC x16 hPW hMem x19 hx19m hx19ne
  · exact hCentrelessPos x3 hSz hL hT hpos hJ h4 hU9 h9U hDiff x14 hMC x16 hPW hMem x19 hx19m hx19ne
