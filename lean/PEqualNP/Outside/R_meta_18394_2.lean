import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18394_2
    (hFourDisjoint :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 n C →
        C.size =
          (PEqualNP.TopForm.tops G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orT G C).card +
          (PEqualNP.TopForm.orN G C).card)
    (hStarOrBound :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;
        have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;
        (2 : ℕ) ≤ x6.card →
        (4 : ℕ) ≤ x9 →
        x8.card ≤ x9 →
        x9 < (2 : ℕ) * x8.card →
        (0 : ℕ) < x7.card →
        (0 : ℕ) < x5.card ∨ (2 : ℕ) ≤ x7.card →
        (22 : ℕ) + x5.card ≤
          (PEqualNP.TopForm.tops x1 x2 \ x5).card +
          (PEqualNP.TopForm.orT x1 x2).card +
          (PEqualNP.TopForm.lam x1 x2).card + x9) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset ℕ := PEqualNP.TopForm.centreless x1 x2;       have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;       have x7 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;       have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x9 : ℕ := (2 : ℕ) * x5.card + x6.card + x7.card;       (2 : ℕ) ≤ x6.card → (4 : ℕ) ≤ x9 → x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → (0 : ℕ) < x7.card → (0 : ℕ) < x5.card ∨ (2 : ℕ) ≤ x7.card → (22 : ℕ) ≤ x2.size := by
  intro x1 x2 hLeast hTF x5 x6 x7 x8 x9 h2 h4 hle hlt hpos hor
  have hSz :
      x2.size =
        (PEqualNP.TopForm.tops x1 x2).card +
        (PEqualNP.TopForm.junk x1 x2).card +
        (PEqualNP.TopForm.orT x1 x2).card +
        (PEqualNP.TopForm.orN x1 x2).card :=
    @hFourDisjoint (11 : ℕ) x1 inferInstance x2 hLeast.1
  have hSubTops : PEqualNP.TopForm.centreless x1 x2 ⊆ PEqualNP.TopForm.tops x1 x2 :=
    Finset.filter_subset _ _
  have hCardTops :
      (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card +
      (PEqualNP.TopForm.centreless x1 x2).card =
      (PEqualNP.TopForm.tops x1 x2).card :=
    Finset.card_sdiff_add_card_eq_card hSubTops
  have hSubOrN : PEqualNP.TopForm.lam x1 x2 ⊆ PEqualNP.TopForm.orN x1 x2 :=
    Finset.filter_subset _ _
  have hCardOrN :
      (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card +
      (PEqualNP.TopForm.lam x1 x2).card =
      (PEqualNP.TopForm.orN x1 x2).card :=
    Finset.card_sdiff_add_card_eq_card hSubOrN
  have hBound := hStarOrBound x2 hLeast hTF h2 h4 hle hlt hpos hor
  have hRearr :
      ∀ a b c k j d : ℕ,
        a + b + c + ((2 : ℕ) * k + j + d) = a + k + j + b + (d + c) + k := by
    intro a b c k j d
    calc
      a + b + c + ((2 : ℕ) * k + j + d)
          = a + b + c + (k + k + j + d) := by rw [Nat.two_mul]
      _ = a + b + (c + (k + (k + j + d))) := by
            rw [Nat.add_assoc, Nat.add_assoc k k j, Nat.add_assoc k (k + j) d]
      _ = a + (b + (k + (c + (k + j + d)))) := by
            rw [Nat.add_assoc a b, Nat.add_left_comm c k]
      _ = a + (k + (b + (c + (k + j + d)))) := by
            rw [Nat.add_left_comm b k]
      _ = (a + k) + (b + (c + (k + (j + d)))) := by
            rw [← Nat.add_assoc a k, Nat.add_assoc k j d]
      _ = (a + k) + (b + (k + (c + (j + d)))) := by
            rw [Nat.add_left_comm c k]
      _ = (a + k) + (b + (k + (j + (c + d)))) := by
            rw [Nat.add_left_comm c j]
      _ = (a + k) + (b + (j + (k + (d + c)))) := by
            rw [Nat.add_left_comm k j, Nat.add_comm c d]
      _ = (a + k) + (j + (b + (d + c + k))) := by
            rw [Nat.add_left_comm b j, Nat.add_comm k (d + c)]
      _ = a + k + j + b + (d + c) + k := by
            rw [← Nat.add_assoc (a + k) j, ← Nat.add_assoc (a + k + j) b, ← Nat.add_assoc (a + k + j + b) (d + c)]
  have hEq :
      (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card +
      (PEqualNP.TopForm.orT x1 x2).card +
      (PEqualNP.TopForm.lam x1 x2).card +
      ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card +
       (PEqualNP.TopForm.junk x1 x2).card +
       (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) =
      x2.size + (PEqualNP.TopForm.centreless x1 x2).card := by
    rw [hRearr, hCardTops, hCardOrN, ← hSz]
  exact Nat.le_of_add_le_add_right (hEq ▸ hBound)
