import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18615_2
    (hZeroFalsePos :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → x3 < x2 →
        have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) =>
          PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;
        (∀ (p l : Fin (13 : ℕ)), p ∉ PEqualNP.HeptadCover.singerLines3 l →
          PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput ([p].toFinset) ([l].toFinset)) x2 = Bool.false) →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } →
        (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) →
        (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) →
        (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) →
        (63 : ℕ) ≤ x1.size)
    (hPosFalsePos :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        x2 < (26 : ℕ) + x1.size → x3 < (26 : ℕ) + x1.size → x3 < x2 →
        have sl := PEqualNP.HeptadCover.singerLines3;
        have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (w : ℕ) (S : Finset (Fin (13 : ℕ))) =>
          PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput S (PEqualNP.HeptadCover.missLines sl S)) w;
        have c : ℕ := Fintype.card { p : Fin (13 : ℕ) × Fin (13 : ℕ) // p.1 ∉ sl p.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput ([p.1].toFinset) ([p.2].toFinset)) x2 = Bool.true };
        (1 : ℕ) ≤ c → c ≤ (12 : ℕ) →
        PEqualNP.GenericRejection.RightOnIncidentPairs sl { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →
        PEqualNP.GenericRejection.RightOnIncidentPairs sl { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } →
        (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle sl x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) →
        (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle sl x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) →
        (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle sl x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) →
        (63 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x3 < x2 →             have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;             have x10 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x10 : ℕ) => {x11 : Fin (13 : ℕ) × Fin (13 : ℕ) | x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x11.1} {x11.2}) x10 = Bool.true};             (x10 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) → (63 : ℕ) ≤ x1.size) := by
  intro x1 x2 x3 hM hRB h2 h3 hlt x9 x10 h12 hR2 hR3 hQ hE1 hE2
  have hS : ∀ a : Fin (13 : ℕ), ([a].toFinset : Finset (Fin (13 : ℕ))) = {a} := fun a => by ext z; simp
  have hCardEq : Fintype.card { x11 : Fin (13 : ℕ) × Fin (13 : ℕ) // x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput ([x11.1].toFinset) ([x11.2].toFinset)) x2 = Bool.true } = (x10 x2).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext p
    simp [x10, hS]
  rcases Nat.eq_zero_or_pos (x10 x2).card with h0 | hpos
  · refine hZeroFalsePos x1 x2 x3 hM hRB h2 h3 hlt ?_ hR2 hR3 hQ hE1 hE2
    intro p l hpl
    cases hv : PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput ([p].toFinset) ([l].toFinset)) x2
    · rfl
    · exfalso
      have hmem : (p, l) ∈ x10 x2 := by
        simp only [x10, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hpl, by simpa [hS] using hv⟩
      have := Finset.card_pos.mpr ⟨(p, l), hmem⟩
      omega
  · exact hPosFalsePos x1 x2 x3 hM hRB h2 h3 hlt (hCardEq.symm ▸ hpos) (hCardEq.symm ▸ h12) hR2 hR3 hQ hE1 hE2
