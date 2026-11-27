import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17543_2
    (hHasCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b r : ℕ),
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun j => x7 ∩ PEqualNP.TopForm.gammaE x1 x2 j;
        (x2.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧
         (PEqualNP.TopForm.centreless x1 x2).Nonempty ∧
         a ∈ x6 ∧ b ∈ x6 ∧ a < b ∧
         ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b ∧
         ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 b a ∧
         x7 ⊆ x6.biUnion x8 ∧ (3 : ℕ) ≤ x7.card ∧ r ∈ x6 ∧ (3 : ℕ) ≤ (x8 r).card) →
        x7.card ≤ x6.card + ((2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card))
    (hNoCentreless :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (a b r : ℕ),
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x8 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun j => x7 ∩ PEqualNP.TopForm.gammaE x1 x2 j;
        (x2.size ≤ (21 : ℕ) ∧ PEqualNP.TopForm.IsLeastAO x1 x2 ∧ PEqualNP.TopForm.TopForm x1 x2 ∧
         PEqualNP.TopForm.centreless x1 x2 = ∅ ∧
         a ∈ x6 ∧ b ∈ x6 ∧ a < b ∧
         ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 a b ∧
         ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 b a ∧
         x7 ⊆ x6.biUnion x8 ∧ (3 : ℕ) ≤ x7.card ∧ r ∈ x6 ∧ (3 : ℕ) ≤ (x8 r).card) →
        x7.card ≤ x6.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x8 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x8 : ℕ) => x7 ∩ PEqualNP.TopForm.gammaE x1 x2 x8;         have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         (∃ (x10 : ℕ) (x11 : ℕ), x10 ∈ x6 ∧ x11 ∈ x6 ∧ x10 ≠ x11 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x11 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x11 x10) → x7 ⊆ x6.biUnion x8 → (3 : ℕ) ≤ x7.card → (∃ x13 ∈ x6, (3 : ℕ) ≤ (x8 x13).card) → x7.card ≤ x6.card + x9) :=
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
  fun x2 hSz hLeast hTF hPair hCov hU3 hRich =>
    Exists.elim hPair fun u hPair2 =>
      Exists.elim hPair2 fun v hUV =>
        Exists.elim hRich fun r hR =>
          Or.elim (Finset.eq_empty_or_nonempty (PEqualNP.TopForm.centreless x1 x2))
            (fun hEmpty =>
              Eq.mp
                (congrArg (fun rhs => (PEqualNP.TopForm.Ustar x1 x2).card ≤ (PEqualNP.TopForm.junk x1 x2).card + rhs)
                  (Eq.symm
                    (Eq.trans
                      (congrArg (fun k => k + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card)
                        (Eq.trans (congrArg (fun c => (2 : ℕ) * c) (Eq.trans (congrArg Finset.card hEmpty) Finset.card_empty)) (Nat.mul_zero (2 : ℕ))))
                      (Nat.zero_add (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card))))
                (Or.elim (Nat.lt_or_gt_of_ne hUV.2.2.1)
                  (fun hLt =>
                    hNoCentreless x2 u v r
                      ⟨hSz, hLeast, hTF, hEmpty, hUV.1, hUV.2.1, hLt, hUV.2.2.2.1, hUV.2.2.2.2, hCov, hU3, hR.1, hR.2⟩)
                  (fun hGt =>
                    hNoCentreless x2 v u r
                      ⟨hSz, hLeast, hTF, hEmpty, hUV.2.1, hUV.1, hGt, hUV.2.2.2.2, hUV.2.2.2.1, hCov, hU3, hR.1, hR.2⟩)))
            (fun hNE =>
              Or.elim (Nat.lt_or_gt_of_ne hUV.2.2.1)
                (fun hLt =>
                  hHasCentreless x2 u v r
                    ⟨hSz, hLeast, hTF, hNE, hUV.1, hUV.2.1, hLt, hUV.2.2.2.1, hUV.2.2.2.2, hCov, hU3, hR.1, hR.2⟩)
                (fun hGt =>
                  hHasCentreless x2 v u r
                    ⟨hSz, hLeast, hTF, hNE, hUV.2.1, hUV.1, hGt, hUV.2.2.2.2, hUV.2.2.2.1, hCov, hU3, hR.1, hR.2⟩))
