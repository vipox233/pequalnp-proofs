import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18906_2
    (hCentrelessAndMinCover :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.centreless G C = ∅ →
        (2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card =
          (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) ∧
        ∃ (M : Finset (Fin 11)),
          PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) M)
    (hG11WitnessRefute :
      let x1 : SimpleGraph (Fin 11) := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (M : Finset (Fin 11)),
        have U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar x1 C;
        have B : ℕ := (PEqualNP.TopForm.junk x1 C).card + (PEqualNP.TopForm.orN x1 C \ PEqualNP.TopForm.lam x1 C).card;
        (PEqualNP.TopForm.IsLeastAO x1 C ∧
         PEqualNP.TopForm.TopForm x1 C ∧
         C.size ≤ 21 ∧
         3 ≤ (PEqualNP.TopForm.junk x1 C).card ∧
         4 ≤ U.card ∧
         B < 2 * U.card ∧
         PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑U) M ∧
         M.card + B ≤ 6 + U.card ∧
         PEqualNP.TopForm.centreless x1 C = ∅ ∧
         1 ≤ (PEqualNP.TopForm.orN x1 C \ PEqualNP.TopForm.lam x1 C).card ∧
         4 ≤ B ∧
         (∀ (u v : Fin 11), s(u, v) ∈ U →
           ∃ j ∈ PEqualNP.TopForm.junk x1 C, PEqualNP.EdgeOwnership.gateVal 11 C j (PEqualNP.EdgeOwnership.pairInput u v) = true)) →
        False) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x6 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;       x2.size ≤ (21 : ℕ) → (3 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card → (4 : ℕ) ≤ x5.card → x6 < (2 : ℕ) * x5.card → (∀ (x11 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x5) x11 → x11.card + x6 ≤ (6 : ℕ) + x5.card) → PEqualNP.TopForm.centreless x1 x2 = ∅ → (1 : ℕ) ≤ (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card → (4 : ℕ) ≤ x6 → (∀ (x15 x16 : Fin (11 : ℕ)), s(x15, x16) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x18 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x18 (PEqualNP.EdgeOwnership.pairInput x15 x16) = Bool.true) → False) :=
  fun x2 hL hTF hSz hJ hU hBnd hCov hCent hOr h4 hHit =>
    let hCM := hCentrelessAndMinCover _ x2 hCent
    Exists.elim hCM.2 fun M hM =>
      hG11WitnessRefute x2 M
        ⟨hL, hTF, hSz, hJ, hU,
          Eq.subst (motive := fun z => z < _) hCM.1 hBnd,
          hM,
          Eq.subst (motive := fun z => M.card + z ≤ _) hCM.1 (hCov M hM),
          hCent, hOr,
          Eq.subst (motive := fun z => 4 ≤ z) hCM.1 h4,
          hHit⟩
