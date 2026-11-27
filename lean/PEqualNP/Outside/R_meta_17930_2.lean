import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17930_2 :
    (∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (11 : ℕ)) (gAnd gOr : ℕ),
      PEqualNP.TopForm.IsAO2 (11 : ℕ) C →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C gAnd).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C gOr).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∀ g < C.size, ↑v ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs ↔ g = gAnd) →
      PEqualNP.TopForm.readers (11 : ℕ) C gAnd = {gOr} →
      gAnd < gOr ∧ gOr < C.size ∧
      (∃ w < (11 : ℕ) + gAnd, ∀ z : Fin (11 : ℕ) → Bool, z v = Bool.false → PEqualNP.ReadTwo.wval C z ((11 : ℕ) + gAnd) = PEqualNP.ReadTwo.wval C z w) ∧
      (∃ w < (11 : ℕ) + gOr, ∀ z : Fin (11 : ℕ) → Bool, z v = Bool.false → PEqualNP.ReadTwo.wval C z ((11 : ℕ) + gOr) = PEqualNP.ReadTwo.wval C z w)) →
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (11 : ℕ)) (x4 x5 : ℕ),
      have x6 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;
      have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
      have x8 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;
      have elimAt : Fin (11 : ℕ) → ℕ → Prop := fun v g => ∃ w < (11 : ℕ) + g, ∀ z : Fin (11 : ℕ) → Bool, z v = Bool.false → PEqualNP.ReadTwo.wval x2 z ((11 : ℕ) + g) = PEqualNP.ReadTwo.wval x2 z w;
      PEqualNP.TopForm.IsLeastAO x1 x2 →
      PEqualNP.TopForm.TopForm x1 x2 →
      (2 : ℕ) ≤ x7.card →
      x2.size ≤ (21 : ℕ) →
      (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →
      (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + x8.card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →
      ↑x3 < (4 : ℕ) →
      (x6 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      (x6 x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →
      (∀ x18 < x2.size, ↑x3 ∈ (x6 x18).inputs ↔ x18 = x4) →
      PEqualNP.TopForm.readers (11 : ℕ) x2 x4 = {x5} →
      (x4 ∈ x7 → x5 ∈ x8) →
      (∃ g < x2.size, g ≠ x4 ∧ g ≠ x5 ∧ elimAt x3 g) ∨
      (∃ (v : Fin (11 : ℕ)), ↑v < (4 : ℕ) ∧ ∃ a b c : ℕ, a < b ∧ b < c ∧ c < x2.size ∧ elimAt v a ∧ elimAt v b ∧ elimAt v c)) →
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (11 : ℕ)) (x4 x5 : ℕ),   have x6 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x2;   have x7 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x8 : Finset ℕ := PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2;   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ x7.card →         x2.size ≤ (21 : ℕ) →           (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card →             (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x7.card + x8.card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →               ↑x3 < (4 : ℕ) →                 (x6 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and →                   (x6 x5).op = PEqualNP.CircuitLowerBounds.GateOp.or →                     (∀ x18 < x2.size, ↑x3 ∈ (x6 x18).inputs ↔ x18 = x4) →                       PEqualNP.TopForm.readers (11 : ℕ) x2 x4 = {x5} →                         (x4 ∈ x7 → x5 ∈ x8) →                           ∃ (x21 : Fin (11 : ℕ)),                             ↑x21 < (4 : ℕ) ∧                               have x22 : ℕ → Prop := fun (x22 : ℕ) => ∃ x23 < (11 : ℕ) + x22, ∀ (x24 : Fin (11 : ℕ) → Bool), x24 x21 = Bool.false → PEqualNP.ReadTwo.wval x2 x24 ((11 : ℕ) + x22) = PEqualNP.ReadTwo.wval x2 x24 x23;                               ∃ (x23 : ℕ) (x24 : ℕ) (x25 : ℕ), x23 < x24 ∧ x24 < x25 ∧ x25 < x2.size ∧ x22 x23 ∧ x22 x24 ∧ x22 x25) :=
  fun h1 h2 x2 x3 x4 x5 hLeast hTF h2j hSz hU3 hStrict hx3lt hAnd hOr hUniq hReaders hImp =>
    let hPair := h1 x2 x3 x4 x5 hLeast.1 hAnd hOr hUniq hReaders
    let hChoice := h2 x2 x3 x4 x5 hLeast hTF h2j hSz hU3 hStrict hx3lt hAnd hOr hUniq hReaders hImp
    Or.elim hChoice
      (fun hLeft =>
        Exists.elim hLeft (fun g hg =>
          ⟨x3, hx3lt,
            Or.elim (lt_trichotomy g x4)
              (fun hg4 => ⟨g, x4, x5, hg4, hPair.1, hPair.2.1, hg.2.2.2, hPair.2.2.1, hPair.2.2.2⟩)
              (fun hge4 =>
                Or.elim hge4
                  (fun heq4 => False.elim (hg.2.1 heq4))
                  (fun h4g =>
                    Or.elim (lt_trichotomy g x5)
                      (fun hg5 => ⟨x4, g, x5, h4g, hg5, hPair.2.1, hPair.2.2.1, hg.2.2.2, hPair.2.2.2⟩)
                      (fun hge5 =>
                        Or.elim hge5
                          (fun heq5 => False.elim (hg.2.2.1 heq5))
                          (fun h5g => ⟨x4, x5, g, hPair.1, h5g, hg.1, hPair.2.2.1, hPair.2.2.2, hg.2.2.2⟩))))⟩))
      (fun hRight => hRight)
