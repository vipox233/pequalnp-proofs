import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17637_1
    (hMinVC7 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (W : Finset (Fin (11 : ℕ))), (∀ (u v : Fin (11 : ℕ)), x1.Adj u v → u ∈ W ∨ v ∈ W) → (7 : ℕ) ≤ W.card)
    (hTriCoverBound :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        (∀ (W : Finset (Fin (11 : ℕ))), (∀ (u v : Fin (11 : ℕ)), x1.Adj u v → u ∈ W ∨ v ∈ W) → (7 : ℕ) ≤ W.card) →
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ x6.card →
        x3 ⊆ x5 →
        x4 ⊆ x6 →
        x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) →
        (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) →
        (∀ x17 ∈ x4, ∀ x19 ∈ x7 x17, ∀ x21 ∈ x7 x17, ¬Disjoint x19.toFinset x21.toFinset) →
        (∃ x18 ∈ x4, (x7 x18).card = (3 : ℕ) ∧ (x7 x18 = {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), s((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))})) →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ), have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2; have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2; have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7; x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) → (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) → (∀ x17 ∈ x4, ∀ x19 ∈ x7 x17, ∀ x21 ∈ x7 x17, ¬Disjoint x19.toFinset x21.toFinset) → (∃ x18 ∈ x4, x7 x18 = {s((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), s((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), s((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), s((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))} ∨ x7 x18 = {s((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), s((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), s((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))}) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  intro x1 x2 x3 x4 x5 x6 x7 hSz hLeast hTop hJunk2 hSub3 hSub4 hCard hCov hNe1 hInt hTri
  obtain ⟨j, hj, hT⟩ := hTri
  have hj3 : (x7 j).card = 3 := by
    rcases hT with h | h | h <;> rw [h] <;> decide
  exact hTriCoverBound x2 x3 x4 hMinVC7 hSz hLeast hTop hJunk2 hSub3 hSub4 hCard hCov hNe1 hInt ⟨j, hj, hj3, hT⟩

