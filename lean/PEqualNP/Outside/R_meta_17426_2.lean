import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17426_2
    (hCase5 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
           ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
           ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
           ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x14 x16 : Finset (Fin (11 : ℕ))),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2
        have x8 : ℕ :=
          (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card +
          (PEqualNP.TopForm.junk x1 x2).card +
          (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card
        (x2.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          x8 = x7.card + (5 : ℕ) ∧ (12 : ℕ) ≤ x7.card ∧
          x14.card = (10 : ℕ) ∧ x16 ⊆ x14 ∧ x16.card = (4 : ℕ) ∧
          ∀ a ∈ x16, ∀ b ∈ x16, ¬x1.Adj a b) →
        ∃ a ∈ x14, ∃ b ∈ x14, x1.Adj a b ∧ s(a, b) ∉ x7)
    (hCase6 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
           ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
           ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
           ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x14 x16 : Finset (Fin (11 : ℕ))),
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2
        have x8 : ℕ :=
          (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card +
          (PEqualNP.TopForm.junk x1 x2).card +
          (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card
        (x2.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧
          (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
          x8 = x7.card + (6 : ℕ) ∧ (16 : ℕ) ≤ x7.card ∧
          x14.card = (11 : ℕ) ∧ x16 ⊆ x14 ∧ x16.card = (4 : ℕ) ∧
          ∀ a ∈ x16, ∀ b ∈ x16, ¬x1.Adj a b) →
        ∃ a ∈ x14, ∃ b ∈ x14, x1.Adj a b ∧ s(a, b) ∉ x7) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           ∀ (x9 : ℕ), (5 : ℕ) ≤ x9 ∧ x9 ≤ (6 : ℕ) → x8 = x7.card + x9 → x8 < (2 : ℕ) * x7.card → [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)].getD x9 (0 : ℕ) ≤ x7.card → ∀ (x14 : Finset (Fin (11 : ℕ))), x14.card = x9 + (5 : ℕ) → (∃ x16 ⊆ x14, x16.card = (4 : ℕ) ∧ ∀ x17 ∈ x16, ∀ x19 ∈ x16, ¬x1.Adj x17 x19) → ∃ x17 ∈ x14, ∃ x18 ∈ x14, x1.Adj x17 x18 ∧ s(x17, x18) ∉ x7) :=
  fun x2 hSz hL hTF hJ x9 h9 h8 _ hGet x14 h14 hEx =>
    hEx.elim fun x16 hx16 =>
      (Nat.eq_or_lt_of_le h9.2).elim
        (fun hEq6 : x9 = 6 =>
          hCase6 x2 x14 x16
            ⟨hSz, hL, hTF, hJ,
              Eq.subst (motive := fun k => _ = _ + k) hEq6 h8,
              Eq.subst (motive := fun k => [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)].getD k (0 : ℕ) ≤ _) hEq6 hGet,
              Eq.subst (motive := fun k => x14.card = k + 5) hEq6 h14,
              hx16.1, hx16.2.1, hx16.2.2⟩)
        (fun hLt6 : x9 < 6 =>
          have hEq5 : x9 = 5 := Nat.le_antisymm (Nat.le_of_lt_succ hLt6) h9.1
          hCase5 x2 x14 x16
            ⟨hSz, hL, hTF, hJ,
              Eq.subst (motive := fun k => _ = _ + k) hEq5 h8,
              Eq.subst (motive := fun k => [(1 : ℕ), (2 : ℕ), (3 : ℕ), (5 : ℕ), (8 : ℕ), (12 : ℕ), (16 : ℕ)].getD k (0 : ℕ) ≤ _) hEq5 hGet,
              Eq.subst (motive := fun k => x14.card = k + 5) hEq5 h14,
              hx16.1, hx16.2.1, hx16.2.2⟩)
