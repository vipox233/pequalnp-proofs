import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17810_2
    (hActiveCover :
      ∀ (J : Finset ℕ) (U S : Finset (Sym2 (Fin (11 : ℕ)))) (Γ : ℕ → Finset (Sym2 (Fin (11 : ℕ)))),
        S ⊆ U →
        (∀ g ∈ J, (S ∩ Γ g).card ≠ (1 : ℕ)) →
        (∀ e ∈ U, ∃ g ∈ J, e ∈ Γ g) →
        let A : Finset ℕ := {g ∈ J | ¬Disjoint S (Γ g)};
        let D : Finset ℕ := {g ∈ J | Disjoint S (Γ g)};
        A.card + D.card = J.card ∧
        S = A.biUnion (fun g => S ∩ Γ g) ∧
        (∀ g ∈ A, (2 : ℕ) ≤ (S ∩ Γ g).card) ∧
        (∀ g ∈ J \ A, Disjoint S (Γ g)))
    (hActiveBound :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (21 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        (2 : ℕ) ≤ x6.card →
        (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) →
        (3 : ℕ) ≤ x7.card →
        ∀ x11 ⊆ x7, ∀ A ⊆ x6,
          A.Nonempty →
          A.card + (x7 \ x11).card ≤ x6.card →
          x11 = A.biUnion (fun g => x11 ∩ PEqualNP.TopForm.gammaE x1 x2 g) →
          (∀ g ∈ A, (2 : ℕ) ≤ (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 g).card) →
          (∀ g ∈ x6 \ A, Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 g)) →
          (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) →
          x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         have x6 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;         have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         (2 : ℕ) ≤ x6.card → (∃ (x9 : ℕ) (x10 : ℕ), x9 ∈ x6 ∧ x10 ∈ x6 ∧ x9 ≠ x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x9 x10 ∧ ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 x10 x9) → (3 : ℕ) ≤ x7.card → ∀ x11 ⊆ x7, x11.Nonempty → (x7 \ x11).card ≤ {x14 ∈ x6 | Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 x14)}.card → (∀ x15 ∈ x6, (x11 ∩ PEqualNP.TopForm.gammaE x1 x2 x15).card ≠ (1 : ℕ)) → (∀ x16 ∈ x7, ∃ x18 ∈ x6, x16 ∈ PEqualNP.TopForm.gammaE x1 x2 x18) → x11.card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (x6.card - (x7 \ x11).card) + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro x1 x2 hSz hLeast hTF x6 x7 h2 hIncomp h3 x11 hx11sub hx11non hSdiffLeD hNe1 hCov7
  let A : Finset ℕ := {g ∈ x6 | ¬Disjoint x11 (PEqualNP.TopForm.gammaE x1 x2 g)}
  have hAC := hActiveCover x6 x7 x11 (PEqualNP.TopForm.gammaE x1 x2) hx11sub hNe1 hCov7
  have hAsub : A ⊆ x6 := Finset.filter_subset _ _
  have hBudget : A.card + (x7 \ x11).card ≤ x6.card :=
    Eq.subst (motive := fun k => A.card + (x7 \ x11).card ≤ k) hAC.1 (Nat.add_le_add_left hSdiffLeD A.card)
  have hAnon : A.Nonempty :=
    Exists.elim hx11non fun e he =>
      Exists.elim (Finset.mem_biUnion.mp (Eq.mp (congrArg (fun T => e ∈ T) hAC.2.1) he)) fun g hg =>
        Exists.intro g hg.1
  exact hActiveBound x2 hSz hLeast hTF h2 hIncomp h3 x11 hx11sub A hAsub hAnon hBudget hAC.2.1 hAC.2.2.1 hAC.2.2.2 hCov7
