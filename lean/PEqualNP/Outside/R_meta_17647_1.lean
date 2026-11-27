import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17647_1
    (hOverlapSum :
      ∀ (I : Finset ℕ) (F : ℕ → Finset (Sym2 (Fin (11 : ℕ)))),
        (∃ i ∈ I, ∃ j ∈ I, i ≠ j ∧ (F i ∩ F j).Nonempty) →
        (I.biUnion F).card + (1 : ℕ) ≤ I.sum (fun i => (F i).card))
    (hWithStrictSum :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (∃ x12 ∈ x6, ∃ x13 ∈ x6, x12 ≠ x13 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x12 x13 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x13 x12) → x5 ⊆ x6.biUnion (PEqualNP.TopForm.gammaE x1 x2) → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → x3 = x4.biUnion x7 → (∀ x18 ∈ x3, ∃ (x20 : ↥x4 ↪ Sym2 (Fin (11 : ℕ))), ∀ (x21 : ↥x4), x20 x21 ∈ (x7 ↑x21).erase x18) → (∃ x19 ∈ x4, ∃ x20 ∈ x4, x19 ≠ x20 ∧ (x7 x19 ∩ x7 x20).Nonempty) → x3.card + (1 : ℕ) ≤ x4.sum (fun i => (x7 i).card) → x3.card ≤ x4.card + x8) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (∃ x12 ∈ x6, ∃ x13 ∈ x6, x12 ≠ x13 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x12 x13 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x13 x12) → x5 ⊆ x6.biUnion (PEqualNP.TopForm.gammaE x1 x2) → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → x3 = x4.biUnion x7 → (∀ x18 ∈ x3, ∃ (x20 : ↥x4 ↪ Sym2 (Fin (11 : ℕ))), ∀ (x21 : ↥x4), x20 x21 ∈ (x7 ↑x21).erase x18) → (∃ x19 ∈ x4, ∃ x20 ∈ x4, x19 ≠ x20 ∧ (x7 x19 ∩ x7 x20).Nonempty) → x3.card ≤ x4.card + x8) := by
  intro x1 x2 x3 x4
  dsimp only
  intro hsize hleast htop hincomp hcov hx3 hx4 hcard hbi hhall hov
  exact hWithStrictSum x2 x3 x4 hsize hleast htop hincomp hcov hx3 hx4 hcard hbi hhall hov
    (Eq.ndrec (motive := fun s => s.card + (1 : ℕ) ≤ x4.sum (fun i => (x3 ∩ PEqualNP.TopForm.gammaE x1 x2 i).card))
      (hOverlapSum x4 (fun i => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 i) hov) hbi.symm)
