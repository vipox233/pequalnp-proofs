import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17171_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun g => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 g;
        x2.size ≤ 21 → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 →
        3 ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4, (x7 x16).card ≠ 1) →
        (∀ x17 ∈ x4, ∃ x19 : Fin 11, ∀ x20 ∈ x7 x17, x19 ∈ x20) →
        PEqualNP.TopForm.centreless x1 x2 = ∅ →
        x3.card ≤ x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun g => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 g;
        x2.size ≤ 21 → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 →
        3 ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4, (x7 x16).card ≠ 1) →
        (∀ x17 ∈ x4, ∃ x19 : Fin 11, ∀ x20 ∈ x7 x17, x19 ∈ x20) →
        0 < (PEqualNP.TopForm.centreless x1 x2).card →
        x3.card ≤ 2 * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) → (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) → (∀ x17 ∈ x4, ∃ (x19 : Fin (11 : ℕ)), ∀ x20 ∈ x7 x17, x19 ∈ x20) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  intro x1 x2 x3 x4 x5 x6 x7 hSz hLeast hTF hJ3 h35 h46 hEq hCov hNe1 hStar
  rcases Nat.eq_zero_or_pos (PEqualNP.TopForm.centreless x1 x2).card with h0 | hPos
  · have hRes := hNoCentreless x2 x3 x4 hSz hLeast hTF hJ3 h35 h46 hEq hCov hNe1 hStar (Finset.card_eq_zero.mp h0)
    rw [h0, Nat.mul_zero, Nat.zero_add]
    exact hRes
  · exact hHasCentreless x2 x3 x4 hSz hLeast hTF hJ3 h35 h46 hEq hCov hNe1 hStar hPos
