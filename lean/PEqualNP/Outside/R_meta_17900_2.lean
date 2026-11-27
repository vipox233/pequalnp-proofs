import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17900_2
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ) (j : ℕ) (e1 e2 : Sym2 (Fin (11 : ℕ))),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x6 \ x4, Disjoint x3 (PEqualNP.TopForm.gammaE x1 x2 x15)) →
        (∀ x16 ∈ x3, ∃ x18 ∈ x4, x16 ∈ x7 x18) →
        (∀ x17 ∈ x4, (x7 x17).card ≠ (1 : ℕ)) →
        x4.card + (1 : ℕ) < x3.card →
        j ∈ x4 → e1 ∈ x7 j → e2 ∈ x7 j → Disjoint e1.toFinset e2.toFinset →
        PEqualNP.TopForm.centreless x1 x2 = ∅ →
        x3.card ≤ x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ) (j : ℕ) (e1 e2 : Sym2 (Fin (11 : ℕ))),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 →
        (2 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card →
        (∀ x15 ∈ x6 \ x4, Disjoint x3 (PEqualNP.TopForm.gammaE x1 x2 x15)) →
        (∀ x16 ∈ x3, ∃ x18 ∈ x4, x16 ∈ x7 x18) →
        (∀ x17 ∈ x4, (x7 x17).card ≠ (1 : ℕ)) →
        x4.card + (1 : ℕ) < x3.card →
        j ∈ x4 → e1 ∈ x7 j → e2 ∈ x7 j → Disjoint e1.toFinset e2.toFinset →
        (PEqualNP.TopForm.centreless x1 x2).Nonempty →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x6 \ x4, Disjoint x3 (PEqualNP.TopForm.gammaE x1 x2 x15)) → (∀ x16 ∈ x3, ∃ x18 ∈ x4, x16 ∈ x7 x18) → (∀ x17 ∈ x4, (x7 x17).card ≠ (1 : ℕ)) → x4.card + (1 : ℕ) < x3.card → (∃ x19 ∈ x4, ∃ x20 ∈ x7 x19, ∃ x21 ∈ x7 x19, Disjoint x20.toFinset x21.toFinset) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :=
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]
  fun x2 x3 x4 hSz hLeast hTF hJunk hSub3 hSub4 hCard hDisjOut hCov hNe1 hLt hEx =>
    Exists.elim hEx fun j hj =>
      Exists.elim hj.2 fun e1 he1 =>
        Exists.elim he1.2 fun e2 he2 =>
          Or.elim (Finset.eq_empty_or_nonempty (PEqualNP.TopForm.centreless x1 x2))
            (fun hEmpty =>
              Nat.le_trans
                (hNoCentreless x2 x3 x4 j e1 e2 hSz hLeast hTF hJunk hSub3 hSub4 hCard hDisjOut hCov hNe1 hLt hj.1 he1.1 he2.1 he2.2 hEmpty)
                (Nat.add_le_add_right (Nat.le_add_left x4.card _) _))
            (fun hNE =>
              hHasCentreless x2 x3 x4 j e1 e2 hSz hLeast hTF hJunk hSub3 hSub4 hCard hDisjOut hCov hNe1 hLt hj.1 he1.1 he2.1 he2.2 hNE)
