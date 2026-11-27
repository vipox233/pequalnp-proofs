import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17852_2
    (hThreeWayErase : ∀ (J S : Finset ℕ) (a b : ℕ), a ∈ J → b ∈ J → a ≠ b → S ⊆ (J.erase a).erase b → S.card + (((J.erase a).erase b) \ S).card + (2 : ℕ) = J.card)
    (hHallSlackBound : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2; have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2; have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card; ∀ x9 ∈ x7, ∀ x11 ∈ x7, x9 ≠ x11 → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 → have x15 : Finset ℕ := (x7.erase x9).erase x11; have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2); ∀ x17 ⊆ x15, have x19 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x17; (x15 \ x17).card + (1 : ℕ) ≤ (x19 ∩ (x15 \ x17).biUnion (PEqualNP.TopForm.gammaE x1 x2)).card → (x16 x17).card ≤ x17.card → x8 + (3 : ℕ) ≤ x19.card → x19 ⊆ (x7 \ x17).biUnion (PEqualNP.TopForm.gammaE x1 x2) → (∀ x24 ⊆ x15 \ x17, x24.Nonempty → x24.card < (x19 ∩ x24.biUnion (PEqualNP.TopForm.gammaE x1 x2)).card) → x19.card ≤ x8 + (2 : ℕ) + (x15 \ x17).card + (x17.card - (x16 x17).card)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         ∀ x9 ∈ x7,           ∀ x11 ∈ x7,             x9 ≠ x11 →               PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x11 →                 have x15 : Finset ℕ := (x7.erase x9).erase x11;                 have x16 : Finset ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x16 : Finset ℕ) => x6 ∩ x16.biUnion (PEqualNP.TopForm.gammaE x1 x2);                 ∀ x17 ⊆ x15,                   have x19 : Finset (Sym2 (Fin (11 : ℕ))) := x6 \ x16 x17;                   (x15 \ x17).Nonempty → (x16 x17).card ≤ x17.card → x8 + (3 : ℕ) ≤ x19.card → x19 ⊆ (x7 \ x17).biUnion (PEqualNP.TopForm.gammaE x1 x2) → (∀ x24 ⊆ x15 \ x17, x24.Nonempty → x24.card < (x19 ∩ x24.biUnion (PEqualNP.TopForm.gammaE x1 x2)).card) → x19.card ≤ x8 + (x7.card - (x16 x17).card) := by
  intro x1 x2 hsz hleast htop x6 x7 x8 x9 hx9 x11 hx11 hne hcone x15 x16 x17 hx17sub x19 hRemNon hle h3 hcov hHall
  have hHallGlobal : (x15 \ x17).card + (1 : ℕ) ≤ (x19 ∩ (x15 \ x17).biUnion (PEqualNP.TopForm.gammaE x1 x2)).card :=
    hHall (x15 \ x17) (Finset.Subset.refl (x15 \ x17)) hRemNon
  have hPart : x17.card + (x15 \ x17).card + (2 : ℕ) = x7.card :=
    hThreeWayErase x7 x17 x9 x11 hx9 hx11 hne hx17sub
  have hBound : x19.card ≤ x8 + (2 : ℕ) + (x15 \ x17).card + (x17.card - (x16 x17).card) :=
    hHallSlackBound x2 hsz hleast htop x9 hx9 x11 hx11 hne hcone x17 hx17sub hHallGlobal hle h3 hcov hHall
  have hSwap : (2 : ℕ) + (x15 \ x17).card + x17.card = x17.card + (x15 \ x17).card + (2 : ℕ) :=
    Eq.trans
      (Nat.add_comm ((2 : ℕ) + (x15 \ x17).card) x17.card)
      (Eq.trans
        (congrArg (fun k => x17.card + k) (Nat.add_comm (2 : ℕ) (x15 \ x17).card))
        (Nat.add_assoc x17.card (x15 \ x17).card (2 : ℕ)).symm)
  have hSum : (2 : ℕ) + (x15 \ x17).card + (x17.card - (x16 x17).card) + (x16 x17).card = x7.card :=
    Eq.trans
      (Nat.add_assoc ((2 : ℕ) + (x15 \ x17).card) (x17.card - (x16 x17).card) (x16 x17).card)
      (Eq.trans
        (congrArg (fun k => (2 : ℕ) + (x15 \ x17).card + k) (Nat.sub_add_cancel hle))
        (Eq.trans hSwap hPart))
  have hDiff : (2 : ℕ) + (x15 \ x17).card + (x17.card - (x16 x17).card) = x7.card - (x16 x17).card :=
    Eq.trans
      (Nat.add_sub_cancel ((2 : ℕ) + (x15 \ x17).card + (x17.card - (x16 x17).card)) (x16 x17).card).symm
      (congrArg (fun k => k - (x16 x17).card) hSum)
  have hRHS : x8 + (2 : ℕ) + (x15 \ x17).card + (x17.card - (x16 x17).card) = x8 + (x7.card - (x16 x17).card) :=
    Eq.trans
      (congrArg (fun k => k + (x17.card - (x16 x17).card)) (Nat.add_assoc x8 (2 : ℕ) (x15 \ x17).card))
      (Eq.trans
        (Nat.add_assoc x8 ((2 : ℕ) + (x15 \ x17).card) (x17.card - (x16 x17).card))
        (congrArg (fun k => x8 + k) hDiff))
  exact Eq.subst (motive := fun k => x19.card ≤ k) hRHS hBound
