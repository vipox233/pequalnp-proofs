import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18388_2 :
    ((∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 n C →
      C.size =
        (PEqualNP.TopForm.tops G C).card +
        (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orT G C).card +
        (PEqualNP.TopForm.orN G C).card) ∧
    (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      PEqualNP.EdgeOwnership.InCone n C i j →
      i < j)) →
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
      x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
      PEqualNP.TopForm.IsLeastAO x1 x3 →
      PEqualNP.TopForm.TopForm x1 x3 →
      PEqualNP.TopForm.junk x1 x3 = {x4, x5} →
      PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →
      have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
      have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;
      have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;
      (3 : ℕ) + x13 < (2 : ℕ) * x11.card →
      (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card →
      (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 →
        ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3,
          ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) →
      (20 : ℕ) + x12.card ≤
        (PEqualNP.TopForm.tops x1 x3 \ x12).card +
        (PEqualNP.TopForm.orT x1 x3).card +
        (PEqualNP.TopForm.lam x1 x3).card + x13) →
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;             (3 : ℕ) + x13 < (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → (22 : ℕ) ≤ x3.size := by
  intro hFourAndCone hCleanStar20 x1 x2 x3 x4 x5 hEqG hLeast hTF hJunkEq hCone x11 x12 x13 hlt1 hle2 hcov
  have hne : x4 ≠ x5 := Nat.ne_of_lt (hFourAndCone.2 (11 : ℕ) x3 x4 x5 hCone)
  have hJunkCard : (PEqualNP.TopForm.junk x1 x3).card = (2 : ℕ) :=
    Eq.trans (congrArg Finset.card hJunkEq) (Finset.card_pair hne)
  have hSz :
      x3.size =
        (PEqualNP.TopForm.tops x1 x3).card +
        (PEqualNP.TopForm.junk x1 x3).card +
        (PEqualNP.TopForm.orT x1 x3).card +
        (PEqualNP.TopForm.orN x1 x3).card :=
    @hFourAndCone.1 (11 : ℕ) x1 x2 x3 hLeast.1
  have hCardTops :
      (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.centreless x1 x3).card =
      (PEqualNP.TopForm.tops x1 x3).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hCardOrN :
      (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card +
        (PEqualNP.TopForm.lam x1 x3).card =
      (PEqualNP.TopForm.orN x1 x3).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hBound :
      (20 : ℕ) + (PEqualNP.TopForm.centreless x1 x3).card ≤
        (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.orT x1 x3).card +
        (PEqualNP.TopForm.lam x1 x3).card +
        ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
          (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) :=
    @hCleanStar20 x1 x2 x3 x4 x5 hEqG hLeast hTF hJunkEq hCone hlt1 hle2 hcov
  have h1 :
      (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card =
      (PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card +
        (PEqualNP.TopForm.centreless x1 x3).card :=
    Eq.trans
      (congrArg (fun t => t + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card)
        (Nat.two_mul (PEqualNP.TopForm.centreless x1 x3).card))
      (Nat.add_right_comm _ _ _)
  have h2 :
      (PEqualNP.TopForm.lam x1 x3).card +
        ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
          (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) =
      (PEqualNP.TopForm.centreless x1 x3).card +
        ((PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card +
          (PEqualNP.TopForm.lam x1 x3).card) +
        (PEqualNP.TopForm.centreless x1 x3).card := by
    rw [h1, ← Nat.add_assoc,
      Nat.add_left_comm (PEqualNP.TopForm.lam x1 x3).card (PEqualNP.TopForm.centreless x1 x3).card _,
      Nat.add_comm (PEqualNP.TopForm.lam x1 x3).card _]
  have h3 :
      (PEqualNP.TopForm.lam x1 x3).card +
        ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
          (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) =
      (PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.orN x1 x3).card +
        (PEqualNP.TopForm.centreless x1 x3).card := by
    rw [h2, hCardOrN]
  have h4 :
      (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.orT x1 x3).card +
        (PEqualNP.TopForm.lam x1 x3).card +
        ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
          (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) =
      ((PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
        (PEqualNP.TopForm.centreless x1 x3).card) +
        (PEqualNP.TopForm.orT x1 x3).card +
        (PEqualNP.TopForm.orN x1 x3).card +
        (PEqualNP.TopForm.centreless x1 x3).card := by
    rw [Nat.add_assoc
        ((PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
          (PEqualNP.TopForm.orT x1 x3).card)
        (PEqualNP.TopForm.lam x1 x3).card _,
      h3, ← Nat.add_assoc, ← Nat.add_assoc,
      Nat.add_assoc
        (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card
        (PEqualNP.TopForm.orT x1 x3).card
        (PEqualNP.TopForm.centreless x1 x3).card,
      Nat.add_comm (PEqualNP.TopForm.orT x1 x3).card (PEqualNP.TopForm.centreless x1 x3).card,
      ← Nat.add_assoc]
  have h5 :
      (2 : ℕ) +
        ((PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
          (PEqualNP.TopForm.orT x1 x3).card +
          (PEqualNP.TopForm.lam x1 x3).card +
          ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
            (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card)) =
      x3.size + (PEqualNP.TopForm.centreless x1 x3).card := by
    rw [h4, hCardTops, ← hJunkCard, ← Nat.add_assoc, ← Nat.add_assoc, ← Nat.add_assoc,
      Nat.add_comm (PEqualNP.TopForm.junk x1 x3).card (PEqualNP.TopForm.tops x1 x3).card,
      ← hSz]
  have h6 :
      (2 : ℕ) + ((20 : ℕ) + (PEqualNP.TopForm.centreless x1 x3).card) ≤
        (2 : ℕ) +
          ((PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
            (PEqualNP.TopForm.orT x1 x3).card +
            (PEqualNP.TopForm.lam x1 x3).card +
            ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
              (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card)) :=
    Nat.add_le_add_left hBound (2 : ℕ)
  rw [← Nat.add_assoc, h5] at h6
  exact Nat.le_of_add_le_add_right h6
