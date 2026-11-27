import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17850_2 :
    (∀ (J : Finset ℕ) (a b : ℕ),
      a ∈ J →
      b ∈ J →
      a ≠ b →
      ((J.erase a).erase b).card + (2 : ℕ) = J.card) →
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.size ≤ (21 : ℕ) →
      PEqualNP.TopForm.IsLeastAO x1 x2 →
      PEqualNP.TopForm.TopForm x1 x2 →
      have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
      have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
      have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
      ∀ x9 ∈ x7, ∀ x11 ∈ x7,
        x9 ≠ x11 →
        PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →
        have x15 : Finset ℕ := (x7.erase x9).erase x11;
        have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);
        have x17 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x15;
        (x16 x15).card ≤ x15.card →
        x8 + (3 : ℕ) ≤ x17.card →
        x17 ⊆ PEqualNP.TopForm.gammaE x1 x2 x9 ∪ PEqualNP.TopForm.gammaE x1 x2 x11 →
        x17.card ≤ x8 + (2 : ℕ) + (x15.card - (x16 x15).card)) →
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         ∀ x9 ∈ x7,           ∀ x11 ∈ x7,             x9 ≠ x11 →               PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →                 have x15 : Finset ℕ := (x7.erase x9).erase x11;                 have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);                 have x17 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x15;                 (x16 x15).card ≤ x15.card → x8 + (3 : ℕ) ≤ x17.card → x17 ⊆ PEqualNP.TopForm.gammaE x1 x2 x9 ∪ PEqualNP.TopForm.gammaE x1 x2 x11 → x17.card ≤ x8 + (x7.card - (x16 x15).card)) := by
  intro hDoubleEraseCard hNestedPairSlack x1 x2 hSz hLeast hTF x6 x7 x8 x9 hx9 x11 hx11 hne hCone x15 x16 x17 hle h3 hSub
  have hm : x15.card + (2 : ℕ) = x7.card :=
    hDoubleEraseCard x7 x9 x11 hx9 hx11 hne
  have hSubAdd : (x15.card - (x16 x15).card + (2 : ℕ)) + (x16 x15).card = x7.card :=
    (Nat.add_right_comm (x15.card - (x16 x15).card) (2 : ℕ) (x16 x15).card).trans
      ((congrArg (· + (2 : ℕ)) (Nat.sub_add_cancel hle)).trans hm)
  have hSubEq : x15.card - (x16 x15).card + (2 : ℕ) = x7.card - (x16 x15).card :=
    (Nat.add_sub_cancel (x15.card - (x16 x15).card + (2 : ℕ)) (x16 x15).card).symm.trans
      (congrArg (· - (x16 x15).card) hSubAdd)
  have hRhsEq : x8 + (2 : ℕ) + (x15.card - (x16 x15).card) = x8 + (x7.card - (x16 x15).card) :=
    (Nat.add_assoc x8 (2 : ℕ) (x15.card - (x16 x15).card)).trans
      (congrArg (x8 + ·) ((Nat.add_comm (2 : ℕ) (x15.card - (x16 x15).card)).trans hSubEq))
  exact Eq.subst (motive := fun k => x17.card ≤ k) hRhsEq
    (hNestedPairSlack x2 hSz hLeast hTF x9 hx9 x11 hx11 hne hCone hle h3 hSub)
