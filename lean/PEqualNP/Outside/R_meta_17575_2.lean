import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17575_2
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) (i : Fin (2 : ℕ)),
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;
        have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x8.card;
        (x2.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧
         (PEqualNP.TopForm.centreless x1 x2).Nonempty ∧
         (2 : ℕ) ≤ x6.card ∧ (2 : ℕ) ≤ x9 ∧ x9 + x6.card < x7.card ∧ x7.card ≤ (16 : ℕ) ∧
         (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x7 → ∃ g ∈ x6, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 g (PEqualNP.EdgeOwnership.pairInput u v) = Bool.true) ∧
         a ∈ x6 ∧ b ∈ x6 ∧ a < b ∧ PEqualNP.TopForm.opnd x2 b i = (11 : ℕ) + a) →
        False)
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ) (i : Fin (2 : ℕ)),
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;
        (x2.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧
         PEqualNP.TopForm.centreless x1 x2 = ∅ ∧
         (2 : ℕ) ≤ x6.card ∧ (2 : ℕ) ≤ x8.card ∧ x8.card + x6.card < x7.card ∧ x7.card ≤ (16 : ℕ) ∧
         (∀ (u v : Fin (11 : ℕ)), s(u, v) ∈ x7 → ∃ g ∈ x6, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 g (PEqualNP.EdgeOwnership.pairInput u v) = Bool.true) ∧
         a ∈ x6 ∧ b ∈ x6 ∧ a < b ∧ PEqualNP.TopForm.opnd x2 b i = (11 : ℕ) + a) →
        False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x8 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;         have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x8.card;         (2 : ℕ) ≤ x6.card → (2 : ℕ) ≤ x9 → x9 + x6.card < x7.card → x7.card ≤ (16 : ℕ) → (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x7 → ∃ x17 ∈ x6, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (∃ x15 ∈ x6, ∃ x16 ∈ x6, x15 < x16 ∧ ∃ (x17 : Fin (2 : ℕ)), PEqualNP.TopForm.opnd x2 x16 x17 = (11 : ℕ) + x15) → False) :=
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
  fun x2 hSz hLeast hTF hJ2 hX9_2 hSumLt hU16 hCov hDirect =>
    Exists.elim hDirect fun a hA =>
      Exists.elim hA.2 fun b hB =>
        Exists.elim hB.2.2 fun i hOp =>
          Or.elim (Finset.eq_empty_or_nonempty (PEqualNP.TopForm.centreless x1 x2))
            (fun hEmpty =>
              have hEq :
                  (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card =
                  (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card :=
                Eq.trans
                  (congrArg (fun k => k + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
                    (Eq.trans (congrArg (fun c => (2 : ℕ) * c) (Eq.trans (congrArg Finset.card hEmpty) Finset.card_empty)) (Nat.mul_zero (2 : ℕ))))
                  (Nat.zero_add (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
              hNoCentreless x2 a b i
                ⟨hSz, hLeast, hTF, hEmpty, hJ2,
                 Eq.mp (congrArg (fun k => (2 : ℕ) ≤ k) hEq) hX9_2,
                 Eq.mp (congrArg (fun k => k + (PEqualNP.TopForm.junk x1 x2).card < (PEqualNP.TopForm.Ustar x1 x2).card) hEq) hSumLt,
                 hU16, hCov, hA.1, hB.1, hB.2.1, hOp⟩)
            (fun hNE =>
              hHasCentreless x2 a b i
                ⟨hSz, hLeast, hTF, hNE, hJ2, hX9_2, hSumLt, hU16, hCov, hA.1, hB.1, hB.2.1, hOp⟩)
