import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17898_2
    (hCoverPigeonhole :
      ∀ (S : Finset (Sym2 (Fin (11 : ℕ)))) (T : Finset ℕ) (f : ℕ → Finset (Sym2 (Fin (11 : ℕ)))),
        (∀ e ∈ S, ∃ g ∈ T, e ∈ f g) →
        (∀ g ∈ T, (f g).card ≠ (1 : ℕ)) →
        T.card + (1 : ℕ) < S.card →
        (∃ g ∈ T, (3 : ℕ) ≤ (f g).card) ∨
        (∃ g1 ∈ T, ∃ g2 ∈ T, g1 ≠ g2 ∧ (f g1).card = (2 : ℕ) ∧ (f g2).card = (2 : ℕ)))
    (hWithRichJunk :
      let x1 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
           ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
           ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
           ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        let x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        let x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        let x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (g : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 g;
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (2 : ℕ) ≤ x6.card ∧
         x3 ⊆ x5 ∧
         x4 ⊆ x6 ∧
         x3.card + x6.card = x5.card + x4.card ∧
         (∀ g ∈ x6 \ x4, Disjoint x3 (PEqualNP.TopForm.gammaE x1 x2 g)) ∧
         (∀ e ∈ x3, ∃ g ∈ x4, e ∈ x7 g) ∧
         (∀ g ∈ x4, (x7 g).card ≠ (1 : ℕ)) ∧
         x4.card + (1 : ℕ) < x3.card ∧
         (∀ g ∈ x4, ∀ e1 ∈ x7 g, ∀ e2 ∈ x7 g, ¬Disjoint e1.toFinset e2.toFinset) ∧
         ((∃ g ∈ x4, (3 : ℕ) ≤ (x7 g).card) ∨
          (∃ g1 ∈ x4, ∃ g2 ∈ x4, g1 ≠ g2 ∧ (x7 g1).card = (2 : ℕ) ∧ (x7 g2).card = (2 : ℕ)))) →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card +
          (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x6 \ x4, Disjoint x3 (PEqualNP.TopForm.gammaE x1 x2 x15)) → (∀ x16 ∈ x3, ∃ x18 ∈ x4, x16 ∈ x7 x18) → (∀ x17 ∈ x4, (x7 x17).card ≠ (1 : ℕ)) → x4.card + (1 : ℕ) < x3.card → (∀ x19 ∈ x4, ∀ x21 ∈ x7 x19, ∀ x23 ∈ x7 x19, ¬Disjoint x21.toFinset x23.toFinset) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :=
  fun x2 x3 x4 hSz hL hTF hJ2 h35 h46 hEq hDisj hCov hNe1 hLt hInt =>
    hWithRichJunk x2 x3 x4
      ⟨hSz, hL, hTF, hJ2, h35, h46, hEq, hDisj, hCov, hNe1, hLt, hInt,
       hCoverPigeonhole x3 x4
         (fun g => x3 ∩ PEqualNP.TopForm.gammaE
           (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
             [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
              ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
              ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
              ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]) x2 g)
         hCov hNe1 hLt⟩
