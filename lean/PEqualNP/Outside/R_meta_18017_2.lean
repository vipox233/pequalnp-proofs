import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18017_2
    (hActiveBlockBounds :
      ∀ (U S : Finset (Sym2 (Fin (11 : ℕ)))) (J : Finset ℕ) (γ : ℕ → Finset (Sym2 (Fin (11 : ℕ)))),
        (J.card + (2 : ℕ) ≤ U.card ∧
         S ⊆ U ∧
         (U \ S).card ≤ {j ∈ J | Disjoint S (γ j)}.card ∧
         (∀ e ∈ U, ∃ j ∈ J, e ∈ γ j) ∧
         (∀ j ∈ J, (S ∩ γ j).card ≠ (1 : ℕ))) →
        have A : Finset ℕ := {j ∈ J | ¬Disjoint S (γ j)};
        (1 : ℕ) ≤ A.card ∧ A.card + (2 : ℕ) ≤ S.card ∧ (3 : ℕ) ≤ S.card ∧ ∀ j ∈ A, (2 : ℕ) ≤ (S ∩ γ j).card)
    (hWithActiveBlock :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))),
        have x4 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;
        have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x6 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x2;
        have A : Finset ℕ := {j ∈ x4 | ¬Disjoint x3 (x6 j)};
        (x2.size ≤ (21 : ℕ) ∧
         PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         (2 : ℕ) ≤ x4.card ∧
         x4.card + (2 : ℕ) ≤ x5.card ∧
         x3 ⊆ x5 ∧
         (x5 \ x3).card ≤ {x13 ∈ x4 | Disjoint x3 (x6 x13)}.card ∧
         (∀ x14 ∈ x5, ∃ x16 ∈ x4, x14 ∈ x6 x16) ∧
         (∀ x15 ∈ x4, (x3 ∩ x6 x15).card ≠ (1 : ℕ)) ∧
         (∀ x16 ⊆ x3, x16.Nonempty → (∀ x19 ∈ x4, Disjoint x16 (x6 x19) ∨ Disjoint (x3 \ x16) (x6 x19)) → {x20 ∈ x4 | ¬Disjoint x16 (x6 x20)}.card < x16.card) ∧
         (1 : ℕ) ≤ A.card ∧ A.card + (2 : ℕ) ≤ x3.card ∧ (3 : ℕ) ≤ x3.card ∧ ∀ j ∈ A, (2 : ℕ) ≤ (x3 ∩ x6 j).card) →
        x5.card ≤ x4.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Finset (Sym2 (Fin (11 : ℕ)))),   have x4 : Finset ℕ := PEqualNP.TopForm.junk x1 x2;   have x5 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;   have x6 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x2;   x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (2 : ℕ) ≤ x4.card → x4.card + (2 : ℕ) ≤ x5.card → x3 ⊆ x5 → (x5 \ x3).card ≤ {x13 ∈ x4 | Disjoint x3 (x6 x13)}.card → (∀ x14 ∈ x5, ∃ x16 ∈ x4, x14 ∈ x6 x16) → (∀ x15 ∈ x4, (x3 ∩ x6 x15).card ≠ (1 : ℕ)) → (∀ x16 ⊆ x3, x16.Nonempty → (∀ x19 ∈ x4, Disjoint x16 (x6 x19) ∨ Disjoint (x3 \ x16) (x6 x19)) → {x20 ∈ x4 | ¬Disjoint x16 (x6 x20)}.card < x16.card) → x5.card ≤ x4.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card) := by
  intro x1 x2 x3 x4 x5 x6 hSz hL hTF hJ2 hJU hSub hDiff hCov hNe1 hComp
  exact
    let hA := hActiveBlockBounds x5 x3 x4 x6 ⟨hJU, hSub, hDiff, hCov, hNe1⟩
    hWithActiveBlock x2 x3 ⟨hSz, hL, hTF, hJ2, hJU, hSub, hDiff, hCov, hNe1, hComp, hA.1, hA.2.1, hA.2.2.1, hA.2.2.2⟩
