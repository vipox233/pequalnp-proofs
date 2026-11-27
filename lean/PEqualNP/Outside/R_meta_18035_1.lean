import PEqualNP.Defs
import Mathlib.Data.Nat.BitIndices

theorem PEqualNP.Outside.R_meta_18035_1
    (hGap5 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x14 : Finset (Fin (11 : ℕ))),
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;
        (x3.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x3 ∧ PEqualNP.TopForm.TopForm x1 x3 ∧ (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card ∧ x8.card ≤ x9 ∧ x9 < (2 : ℕ) * x8.card ∧ x9 - x8.card = (5 : ℕ) ∧ PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x14 ∧ x14.card ≤ (1 : ℕ)) →
          ∃ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x15 ∧ ∀ (x16 : List ℕ), List.Pairwise (fun (x17 x18 : ℕ) => x17 &&& x18 = (0 : ℕ)) x16 → (∀ x18 ∈ x16, x18 ∈ x2 ∧ ∀ x20 ∈ x15, x18.testBit ↑x20 = Bool.false) → (List.map (fun (x19 : ℕ) => (x19.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x16).sum ≤ (5 : ℕ))
    (hGap6 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x14 : Finset (Fin (11 : ℕ))),
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
        have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;
        (x3.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x3 ∧ PEqualNP.TopForm.TopForm x1 x3 ∧ (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card ∧ x8.card ≤ x9 ∧ x9 < (2 : ℕ) * x8.card ∧ x9 - x8.card = (6 : ℕ) ∧ PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x14 ∧ x14.card = (0 : ℕ)) →
          ∃ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x15 ∧ ∀ (x16 : List ℕ), List.Pairwise (fun (x17 x18 : ℕ) => x17 &&& x18 = (0 : ℕ)) x16 → (∀ x18 ∈ x16, x18 ∈ x2 ∧ ∀ x20 ∈ x15, x18.testBit ↑x20 = Bool.false) → (List.map (fun (x19 : ℕ) => (x19.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x16).sum ≤ (6 : ℕ)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → (5 : ℕ) ≤ x9 - x8.card → (∃ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x14 ∧ x14.card + (x9 - x8.card) ≤ (6 : ℕ)) → ∃ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x15 ∧ ∀ (x16 : List ℕ), List.Pairwise (fun (x17 x18 : ℕ) => x17 &&& x18 = (0 : ℕ)) x16 → (∀ x18 ∈ x16, x18 ∈ x2 ∧ ∀ x20 ∈ x15, x18.testBit ↑x20 = Bool.false) → (List.map (fun (x19 : ℕ) => (x19.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x16).sum ≤ x9 - x8.card :=
  fun x3 hSz hL hT hJ hLe hLt hLt7 hGe5 hEx =>
    Exists.elim hEx fun x14 h14 =>
      (Nat.eq_or_lt_of_le hGe5).elim
        (fun h5 => by
          have h5' := h5.symm
          have hc1 : x14.card ≤ 1 := by have h := h14.2; rw [h5'] at h; exact Nat.le_of_add_le_add_right h
          have r := hGap5 x3 x14 ⟨hSz, hL, hT, hJ, hLe, hLt, h5', h14.1, hc1⟩
          rw [h5']; exact r)
        (fun hGt5 => by
          have h6 : _ = 6 := Nat.le_antisymm (Nat.le_of_lt_succ hLt7) hGt5
          have hc0 : x14.card = 0 := by have h := h14.2; rw [h6] at h; exact Nat.eq_zero_of_le_zero (Nat.le_of_add_le_add_right h)
          have r := hGap6 x3 x14 ⟨hSz, hL, hT, hJ, hLe, hLt, h6, h14.1, hc0⟩
          rw [h6]; exact r)
