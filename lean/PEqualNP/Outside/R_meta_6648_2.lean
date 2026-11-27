import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6648_2
    (hSym2Match :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit)
        (g : ℕ) (S : Finset (Sym2 (Fin n))) (e1 e2 : Sym2 (Fin n)),
        e1 ∈ S ∩ PEqualNP.TopForm.gammaE G C g →
        e2 ∈ S ∩ PEqualNP.TopForm.gammaE G C g →
        Disjoint e1.toFinset e2.toFinset →
        ∃ (u1 v1 u2 v2 : Fin n),
          s(u1, v1) ∈ S ∩ PEqualNP.TopForm.gammaE G C g ∧
          s(u2, v2) ∈ S ∩ PEqualNP.TopForm.gammaE G C g ∧
          G.Adj u1 v1 ∧ G.Adj u2 v2 ∧
          u1 ≠ u2 ∧ u1 ≠ v2 ∧ v1 ≠ u2 ∧ v1 ≠ v2 ∧
          PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u1 v1) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u2 v2) = Bool.true)
    (hExplicitMatchBound :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        (3 : ℕ) ≤ x6.card →
        x3 ⊆ x5 →
        x4 ⊆ x6 →
        (x6 \ x4).card = (x5 \ x3).card →
        x3 = x4.biUnion x7 →
        (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) →
        (∃ x17 ∈ x4, ∃ (u1 v1 u2 v2 : Fin (11 : ℕ)),
          s(u1, v1) ∈ x7 x17 ∧ s(u2, v2) ∈ x7 x17 ∧
          x1.Adj u1 v1 ∧ x1.Adj u2 v2 ∧
          u1 ≠ u2 ∧ u1 ≠ v2 ∧ v1 ≠ u2 ∧ v1 ≠ v2 ∧
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x17 (PEqualNP.EdgeOwnership.pairInput u1 v1) = Bool.true ∧
          PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x17 (PEqualNP.EdgeOwnership.pairInput u2 v2) = Bool.true) →
        x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))) (x4 : Finset ℕ),   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x7 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x7 : ℕ) => x3 ∩ PEqualNP.TopForm.gammaE x1 x2 x7;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (3 : ℕ) ≤ x6.card → x3 ⊆ x5 → x4 ⊆ x6 → x3.card + x6.card = x5.card + x4.card → (∀ x15 ∈ x3, ∃ x17 ∈ x4, x15 ∈ x7 x17) → (∀ x16 ∈ x4, (x7 x16).card ≠ (1 : ℕ)) → (∃ x17 ∈ x4, ∃ x18 ∈ x7 x17, ∃ x19 ∈ x7 x17, Disjoint x18.toFinset x19.toFinset) → x3.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x4.card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro x1 x2 x3 x4 x5 x6 x7 hSz hLeast hTF h3 hx3sub hx4sub hCardEq hCov hNe1 hDisjEx
  have h35 : (x5 \ x3).card + x3.card = x5.card := Finset.card_sdiff_add_card_eq_card hx3sub
  have h46 : (x6 \ x4).card + x4.card = x6.card := Finset.card_sdiff_add_card_eq_card hx4sub
  have h1 : x3.card + ((x6 \ x4).card + x4.card) = ((x5 \ x3).card + x3.card) + x4.card :=
    (congrArg (x3.card + ·) h46).trans (hCardEq.trans (congrArg (· + x4.card) h35.symm))
  have h2 : (x3.card + (x6 \ x4).card) + x4.card = ((x5 \ x3).card + x3.card) + x4.card :=
    (Nat.add_assoc x3.card (x6 \ x4).card x4.card).trans h1
  have h3' : x3.card + (x6 \ x4).card = (x5 \ x3).card + x3.card := Nat.add_right_cancel h2
  have h4' : (x6 \ x4).card + x3.card = (x5 \ x3).card + x3.card :=
    (Nat.add_comm (x6 \ x4).card x3.card).trans h3'
  have hSdiffEq : (x6 \ x4).card = (x5 \ x3).card := Nat.add_right_cancel h4'
  have hBiUnion : x3 = x4.biUnion x7 :=
    Finset.Subset.antisymm
      (fun e he => Finset.mem_biUnion.mpr (hCov e he))
      (Finset.biUnion_subset.mpr (fun _ _ => Finset.inter_subset_left))
  have hMatchEx :
      ∃ x17 ∈ x4, ∃ (u1 v1 u2 v2 : Fin (11 : ℕ)),
        s(u1, v1) ∈ x7 x17 ∧ s(u2, v2) ∈ x7 x17 ∧
        x1.Adj u1 v1 ∧ x1.Adj u2 v2 ∧
        u1 ≠ u2 ∧ u1 ≠ v2 ∧ v1 ≠ u2 ∧ v1 ≠ v2 ∧
        PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x17 (PEqualNP.EdgeOwnership.pairInput u1 v1) = Bool.true ∧
        PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x17 (PEqualNP.EdgeOwnership.pairInput u2 v2) = Bool.true :=
    Exists.elim hDisjEx fun g0 hg0 =>
      Exists.elim hg0.2 fun e1 he1 =>
        Exists.elim he1.2 fun e2 he2 =>
          Exists.intro g0 (And.intro hg0.1 (hSym2Match (11 : ℕ) x1 x2 g0 x3 e1 e2 he1.1 he2.1 he2.2))
  exact hExplicitMatchBound x2 x3 x4 hSz hLeast hTF h3 hx3sub hx4sub hSdiffEq hBiUnion hNe1 hMatchEx
