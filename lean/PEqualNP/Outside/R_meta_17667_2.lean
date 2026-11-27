import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17667_2
    (hInterSub :
      ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj],
        x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),
          have x11 : ℕ → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.wmax x1 x4;
          have x12 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x4;
          have x13 : ℕ → (Fin (11 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4;
          have x14 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x14 : ℕ) => {x15 ∈ x12 x14 | ∃ x16 ∈ x11 x14, x16 ∈ x15};
          have x15 : Finset (Sym2 (Fin (11 : ℕ))) := x12 x5 ∩ x12 x6;
          have x17 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x4;
          (PEqualNP.TopForm.IsLeastAO x1 x4 ∧
            PEqualNP.TopForm.TopForm x1 x4 ∧
            x4.size < (22 : ℕ) ∧
            PEqualNP.TopForm.junk x1 x4 = {x5, x6} ∧
            (∀ (x16 : Fin (11 : ℕ) → Bool), x13 x5 x16 = Bool.true → x13 x6 x16 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x16 = Bool.true) ∧
            (x14 x5).card ≤ (7 : ℕ) ∧ (x14 x6).card ≤ (7 : ℕ) ∧ x15.card ≤ (8 : ℕ) ∧
            (∀ x19 ∈ x17, x19 ∈ x14 x5 ∨ x19 ∈ x14 x6 ∨ x19 ∈ x15) ∧
            (2 : ℕ) ≤ x17.card) →
          [(0 : ℕ), (0 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (21 : ℕ)].getD x17.card (0 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x4).card + (PEqualNP.TopForm.orN x1 x4 \ PEqualNP.TopForm.lam x1 x4).card)
    (hCommonMax :
      ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj],
        x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),
          have x11 : ℕ → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.wmax x1 x4;
          have x12 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x4;
          have x14 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x14 : ℕ) => {x15 ∈ x12 x14 | ∃ x16 ∈ x11 x14, x16 ∈ x15};
          have x17 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x4;
          (PEqualNP.TopForm.IsLeastAO x1 x4 ∧
            PEqualNP.TopForm.TopForm x1 x4 ∧
            x4.size < (22 : ℕ) ∧
            PEqualNP.TopForm.junk x1 x4 = {x5, x6} ∧
            (x11 x5 ∩ x11 x6).Nonempty ∧
            (x14 x5).card ≤ (7 : ℕ) ∧ (x14 x6).card ≤ (7 : ℕ) ∧
            (∀ x19 ∈ x17, x19 ∈ x14 x5 ∨ x19 ∈ x14 x6) ∧
            (2 : ℕ) ≤ x17.card) →
          [(0 : ℕ), (0 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (21 : ℕ)].getD x17.card (0 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x4).card + (PEqualNP.TopForm.orN x1 x4 \ PEqualNP.TopForm.lam x1 x4).card) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [DecidableRel x1.Adj],   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),       PEqualNP.TopForm.IsLeastAO x1 x4 →         PEqualNP.TopForm.TopForm x1 x4 →           x4.size < (22 : ℕ) →             PEqualNP.TopForm.junk x1 x4 = {x5, x6} →               have x11 : ℕ → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.wmax x1 x4;               have x12 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x4;               have x13 : ℕ → (Fin (11 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4;               have x14 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x14 : ℕ) => {x15 ∈ x12 x14 | ∃ x16 ∈ x11 x14, x16 ∈ x15};               have x15 : Finset (Sym2 (Fin (11 : ℕ))) := x12 x5 ∩ x12 x6;               have x16 : Prop := ∀ (x16 : Fin (11 : ℕ) → Bool), x13 x5 x16 = Bool.true → x13 x6 x16 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x16 = Bool.true;               have x17 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x4;               (x14 x5).card ≤ (7 : ℕ) ∧ (x14 x6).card ≤ (7 : ℕ) ∧ (x16 → x15.card ≤ (8 : ℕ)) ∧ (x16 ∨ (x11 x5 ∩ x11 x6).Nonempty) → (∀ x19 ∈ x17, x19 ∈ x14 x5 ∨ x19 ∈ x14 x6 ∨ x16 ∧ x19 ∈ x15) → (2 : ℕ) ≤ x17.card → [(0 : ℕ), (0 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (21 : ℕ)].getD x17.card (0 : ℕ) ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x4).card + (PEqualNP.TopForm.orN x1 x4 \ PEqualNP.TopForm.lam x1 x4).card) :=
  fun x1 _ hG x4 x5 x6 hLeast hTF hSz hJunk hA hCov hU2 =>
    Or.elim (Classical.em (∀ (f : Fin (11 : ℕ) → Bool), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x5 f = Bool.true → PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x4 x6 f = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ f = Bool.true))
      (fun h16 =>
        hInterSub x1 hG x4 x5 x6
          ⟨hLeast, hTF, hSz, hJunk, h16, hA.1, hA.2.1, hA.2.2.1 h16,
           fun e he => Or.elim (hCov e he) Or.inl (fun h2 => Or.elim h2 (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h.2))),
           hU2⟩)
      (fun hn16 =>
        hCommonMax x1 hG x4 x5 x6
          ⟨hLeast, hTF, hSz, hJunk, Or.elim hA.2.2.2 (fun h => False.elim (hn16 h)) id, hA.1, hA.2.1,
           fun e he => Or.elim (hCov e he) Or.inl (fun h2 => Or.elim h2 Or.inr (fun h => False.elim (hn16 h.1))),
           hU2⟩)
