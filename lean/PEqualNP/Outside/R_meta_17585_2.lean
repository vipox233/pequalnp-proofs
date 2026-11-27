import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17585_2
    (hJunkEq2 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (PEqualNP.TopForm.junk x1 x2).card = 2 →
        x2.size ≤ 21 →
        2 * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < 2 * (PEqualNP.TopForm.Ustar x1 x2).card →
        have x8 : Fin 11 → Finset ℕ := fun v => (Finset.range x2.size).filter (fun g => v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs);
        have x9 : Fin 11 → ℕ → Prop := fun v g => ∃ w < 11 + g, ∀ y : Fin 11 → Bool, y v = false → PEqualNP.ReadTwo.wval x2 y (11 + g) = PEqualNP.ReadTwo.wval x2 y w;
        (∀ v : Fin 11, v.val < 4 → (x8 v).card = 2 ∧ ∀ g ∈ x8 v, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ v : Fin 11, v.val < 4 ∧ ∃ g ∉ x8 v, g < x2.size ∧ x9 v g)
    (hJunkGe3 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        3 ≤ (PEqualNP.TopForm.junk x1 x2).card →
        x2.size ≤ 21 →
        2 * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < 2 * (PEqualNP.TopForm.Ustar x1 x2).card →
        have x8 : Fin 11 → Finset ℕ := fun v => (Finset.range x2.size).filter (fun g => v.val ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs);
        have x9 : Fin 11 → ℕ → Prop := fun v g => ∃ w < 11 + g, ∀ y : Fin 11 → Bool, y v = false → PEqualNP.ReadTwo.wval x2 y (11 + g) = PEqualNP.ReadTwo.wval x2 y w;
        (∀ v : Fin 11, v.val < 4 → (x8 v).card = 2 ∧ ∀ g ∈ x8 v, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ v : Fin 11, v.val < 4 ∧ ∃ g ∉ x8 v, g < x2.size ∧ x9 v g) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             have x8 : Fin (11 : ℕ) → Finset ℕ := fun (x8 : Fin (11 : ℕ)) => {x9 ∈ Finset.range x2.size | ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x9).inputs};             have x9 : Fin (11 : ℕ) → ℕ → Prop := fun (x9 : Fin (11 : ℕ)) (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;             (∀ (x10 : Fin (11 : ℕ)), ↑x10 < (4 : ℕ) → (x8 x10).card = (2 : ℕ) ∧ ∀ x12 ∈ x8 x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x11 : Fin (11 : ℕ)), ↑x11 < (4 : ℕ) ∧ ∃ x12 ∉ x8 x11, x12 < x2.size ∧ x9 x11 x12) := by
  intro x1 x2 hLeast hTF hJ2
  exact Or.elim (Nat.eq_or_lt_of_le hJ2)
    (fun hEq => hJunkEq2 x2 hLeast hTF hEq.symm)
    (fun hLt => hJunkGe3 x2 hLeast hTF hLt)
