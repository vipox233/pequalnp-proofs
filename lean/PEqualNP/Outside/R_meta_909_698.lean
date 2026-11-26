import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_909_698
    (search :
      let rows : List (Finset (Fin 10)) :=
        [{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6}, {1,3,7}, {0,3,6,7},
         {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8}, {0,3,9}, {2,5,9},
         {1,3,5,9}, {1,8,9}, {0,2,8,9}]
      ∃ C : PEqualNP.AndCount.AndCountCircuit 10, ∃ safe : Finset (Fin C.size),
        C.WellFormed ∧ C.size ≤ 6 ∧
        (∀ v : Fin 10, Multiset.card (Multiset.filter
          (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)
          (Finset.univ : Finset (Fin C.size)).val) ≤ 2) ∧
        C.outVars = ∅ ∧ C.outGates = safe ∧
        (∀ i, i ∈ safe ↔ ∀ I ∈ rows, C.gateVal I i = false) ∧
        (∀ i j, j ∈ C.leftGates i ∨ j ∈ C.rightGates i → j ∉ safe) ∧
        3 ≤ (Finset.univ \ safe).card ∧
        (∀ I ∈ rows, C.eval I = false ∧
          ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true))
    (coverage :
      let H : SimpleGraph (Fin 10) := SimpleGraph.fromRel (fun a b : Fin 10 =>
        ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
          (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ)))
      ∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ H.Adj a c) →
        (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, H.Adj a w) →
        I ∈ ([{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6}, {1,3,7}, {0,3,6,7},
          {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8}, {0,3,9}, {2,5,9},
          {1,3,5,9}, {1,8,9}, {0,2,8,9}] : List (Finset (Fin 10)))) :
    ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
      ∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧ C.size ≤ 6 ∧
        (∀ v : Fin 10, (Finset.univ.filter (fun i : Fin C.size => v ∈ C.leftVars i ∨ v ∈ C.rightVars i)).card ≤ 2) ∧
        (∀ I : Finset (Fin 10), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin 10, w ∉ I → C.eval (insert w I) = true) := by
  intro G hG
  subst G
  obtain ⟨C, _, wellFormed, sizeBound, bareBound, _, _, _, _, _, onRows⟩ := search
  exact ⟨C, wellFormed, sizeBound, bareBound, fun I independent maximal =>
    onRows I (coverage I independent maximal)⟩
