import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18613_3
    (hWireInternal :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →
        PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
          { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } →
        (26 : ℕ) ≤ x2)
    (hInternalLB :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ)
        (q1 q2 : Finset (Fin (13 : ℕ))),
        have qval : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun w q =>
          PEqualNP.LowMerge.wireVal x1
            (PEqualNP.GenericRejection.incidenceInput q (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 q)) w
        have pairs : List (Fin (13 : ℕ) × Fin (13 : ℕ)) :=
          (List.finRange (13 : ℕ)).flatMap fun a => (List.finRange (13 : ℕ)).map fun b => (a, b)
        (PEqualNP.MetaComplexity.Monotone2 x1 ∧
          PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 ∧
          (26 : ℕ) ≤ x2 ∧ x2 < x3 ∧ x3 < (26 : ℕ) + x1.size ∧
          pairs.countP (fun e =>
            Decidable.decide (e.1 ∉ PEqualNP.HeptadCover.singerLines3 e.2) &&
              PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput [e.1].toFinset [e.2].toFinset) x2) ≤ (12 : ℕ) ∧
          PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
            { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } ∧
          PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3
            { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } ∧
          (∀ (q : Finset (Fin (13 : ℕ))),
            PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 q →
            qval x2 q = Bool.false ∨ qval x3 q = Bool.false) ∧
          PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 q1 ∧
          qval x2 q1 = Bool.false ∧ qval x3 q1 = Bool.true ∧
          PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 q2 ∧
          qval x3 q2 = Bool.false ∧ qval x2 q2 = Bool.true) →
        (63 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           x2 < x3 →             have x9 : ℕ → Finset (Fin (13 : ℕ)) → Bool := fun (x9 : ℕ) (x10 : Finset (Fin (13 : ℕ))) => PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput x10 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x10)) x9;             have x10 : ℕ → Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := fun (x10 : ℕ) => {x11 : Fin (13 : ℕ) × Fin (13 : ℕ) | x11.1 ∉ PEqualNP.HeptadCover.singerLines3 x11.2 ∧ PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput {x11.1} {x11.2}) x10 = Bool.true};             (x10 x2).card ≤ (12 : ℕ) → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x2 : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.GenericRejection.RightOnIncidentPairs PEqualNP.HeptadCover.singerLines3 { gates := x1.gates, output := x3 : PEqualNP.CircuitLowerBounds.Circuit } → (∀ (x14 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x14 → x9 x2 x14 = Bool.false ∨ x9 x3 x14 = Bool.false) → (∃ (x15 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x15 ∧ x9 x2 x15 = Bool.false ∧ x9 x3 x15 = Bool.true) → (∃ (x16 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x16 ∧ x9 x3 x16 = Bool.false ∧ x9 x2 x16 = Bool.true) → (63 : ℕ) ≤ x1.size) := by
  intro x1 x2 x3 hM hRB _ h3 hlt x9 x10 hcard hR2 hR3 hAll hQ1 hQ2
  have h2ge : (26 : ℕ) ≤ x2 := hWireInternal x1 x2 hM hRB hR2
  have hsing : ∀ a : Fin 13, [a].toFinset = {a} := fun a =>
    Finset.ext fun _ => List.mem_toFinset.trans (List.mem_singleton.trans Finset.mem_singleton.symm)
  let pairs : List (Fin 13 × Fin 13) :=
    (List.finRange 13).flatMap fun a => (List.finRange 13).map fun b => (a, b)
  let pred : Fin 13 × Fin 13 → Bool := fun e =>
    Decidable.decide (e.1 ∉ PEqualNP.HeptadCover.singerLines3 e.2) &&
      PEqualNP.LowMerge.wireVal x1 (PEqualNP.GenericRejection.incidenceInput [e.1].toFinset [e.2].toFinset) x2
  have hnodup : pairs.Nodup := by
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro a _
      exact (List.nodup_finRange 13).map (fun _ _ h => (Prod.mk.inj h).2)
    · exact (List.nodup_finRange 13).pairwise_of_forall_ne fun a _ b _ hab => by
        intro e he1 he2
        simp only [List.mem_map] at he1 he2
        exact hab (((he1.choose_spec.2).trans he2.choose_spec.2.symm |> Prod.mk.inj).1)
  have hcount : pairs.countP pred ≤ 12 := by
    have heq : pairs.countP pred = (x10 x2).card := by
      rw [List.countP_eq_length_filter, ← List.toFinset_card_of_nodup (hnodup.filter pred)]
      congr 1
      ext e
      simp only [List.mem_toFinset, List.mem_filter, pred, x10, Finset.mem_filter, Finset.mem_univ,
        true_and, Bool.and_eq_true, decide_eq_true_eq, hsing, pairs, List.mem_flatMap, List.mem_map,
        List.mem_finRange, true_and]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨⟨e.1, e.2, rfl⟩, h⟩
    rw [heq]
    exact hcard
  exact hQ1.elim fun q1 hq1 =>
    hQ2.elim fun q2 hq2 =>
      hInternalLB x1 x2 x3 q1 q2
        ⟨hM, hRB, h2ge, hlt, h3, hcount, hR2, hR3, hAll,
          hq1.1, hq1.2.1, hq1.2.2, hq2.1, hq2.2.1, hq2.2.2⟩
