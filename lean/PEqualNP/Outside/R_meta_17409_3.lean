import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17409_3
    (hSingleOut :
      have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → List Bool → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : List Bool) =>
        have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (x3 ++ [Bool.false]) x1;
        Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true);
      have x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x2 x3 : Fin (21 : ℕ)) => [(↑x2 + (20 : ℕ)) % (21 : ℕ), ↑x2, (↑x2 + (5 : ℕ)) % (21 : ℕ), (↑x2 + (7 : ℕ)) % (21 : ℕ), (↑x2 + (17 : ℕ)) % (21 : ℕ)].contains ↑x3;
      ∀ (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Finset ℕ),
        (x4.card = (1 : ℕ) ∧
          ∀ (x5 : Fin (42 : ℕ) → Bool), x1 x3 x4 (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (21 : ℕ)) (x7 : Fin (21 : ℕ)), x2 x6 x7 = Bool.true ∧ x5 (Fin.castAdd (21 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.true) →
        ∃ (x6 : List (Finset ℕ × Finset ℕ)) (x7 : List (Finset ℕ × Finset ℕ)) (x8 : Fin (21 : ℕ) → Finset ℕ) (x9 : Finset ℕ),
          x6.length + x7.length ≤ x3.length ∧
          ∀ (x10 x11 : Fin (21 : ℕ) → Bool),
            ((x10 = fun (_ : Fin (21 : ℕ)) => Bool.false) ∨ ∃ (x12 : Fin (21 : ℕ)), x10 = fun (x13 : Fin (21 : ℕ)) => Decidable.decide (x13 = x12)) →
            x1 x7 x9 (List.ofFn fun (x13 : Fin (21 : ℕ)) => x10 x13 && x1 x6 (x8 x13) (List.ofFn x11)) = x1 x3 x4 (List.ofFn (Fin.append x10 x11)))
    (hMultiOut :
      have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → List Bool → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : List Bool) =>
        have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (x3 ++ [Bool.false]) x1;
        Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true);
      have x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x2 x3 : Fin (21 : ℕ)) => [(↑x2 + (20 : ℕ)) % (21 : ℕ), ↑x2, (↑x2 + (5 : ℕ)) % (21 : ℕ), (↑x2 + (7 : ℕ)) % (21 : ℕ), (↑x2 + (17 : ℕ)) % (21 : ℕ)].contains ↑x3;
      ∀ (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Finset ℕ),
        ((2 : ℕ) ≤ x4.card ∧
          ∀ (x5 : Fin (42 : ℕ) → Bool), x1 x3 x4 (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (21 : ℕ)) (x7 : Fin (21 : ℕ)), x2 x6 x7 = Bool.true ∧ x5 (Fin.castAdd (21 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.true) →
        ∃ (x6 : List (Finset ℕ × Finset ℕ)) (x7 : List (Finset ℕ × Finset ℕ)) (x8 : Fin (21 : ℕ) → Finset ℕ) (x9 : Finset ℕ),
          x6.length + x7.length ≤ x3.length ∧
          ∀ (x10 x11 : Fin (21 : ℕ) → Bool),
            ((x10 = fun (_ : Fin (21 : ℕ)) => Bool.false) ∨ ∃ (x12 : Fin (21 : ℕ)), x10 = fun (x13 : Fin (21 : ℕ)) => Decidable.decide (x13 = x12)) →
            x1 x7 x9 (List.ofFn fun (x13 : Fin (21 : ℕ)) => x10 x13 && x1 x6 (x8 x13) (List.ofFn x11)) = x1 x3 x4 (List.ofFn (Fin.append x10 x11))) :
    (have x1 : List (Finset ℕ × Finset ℕ) → Finset ℕ → List Bool → Bool := fun (x1 : List (Finset ℕ × Finset ℕ)) (x2 : Finset ℕ) (x3 : List Bool) =>   have x4 : List Bool := List.foldl (fun (x4 : List Bool) (x5 : Finset ℕ × Finset ℕ) => x4 ++ [Decidable.decide (∀ x6 ∈ x5.1, x4.getD x6 Bool.false = Bool.true) || Decidable.decide (∀ x6 ∈ x5.2, x4.getD x6 Bool.false = Bool.true)]) (x3 ++ [Bool.false]) x1;   Decidable.decide (∀ x5 ∈ x2, x4.getD x5 Bool.false = Bool.true); have x2 : Fin (21 : ℕ) → Fin (21 : ℕ) → Bool := fun (x2 x3 : Fin (21 : ℕ)) => [(↑x2 + (20 : ℕ)) % (21 : ℕ), ↑x2, (↑x2 + (5 : ℕ)) % (21 : ℕ), (↑x2 + (7 : ℕ)) % (21 : ℕ), (↑x2 + (17 : ℕ)) % (21 : ℕ)].contains ↑x3; ∀ (x3 : List (Finset ℕ × Finset ℕ)) (x4 : Finset ℕ), (∀ (x5 : Fin (42 : ℕ) → Bool), x1 x3 x4 (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (21 : ℕ)) (x7 : Fin (21 : ℕ)), x2 x6 x7 = Bool.true ∧ x5 (Fin.castAdd (21 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (21 : ℕ) x7) = Bool.true) → ∃ (x6 : List (Finset ℕ × Finset ℕ)) (x7 : List (Finset ℕ × Finset ℕ)) (x8 : Fin (21 : ℕ) → Finset ℕ) (x9 : Finset ℕ), x6.length + x7.length ≤ x3.length ∧ ∀ (x10 x11 : Fin (21 : ℕ) → Bool), ((x10 = fun (_ : Fin (21 : ℕ)) => Bool.false) ∨ ∃ (x12 : Fin (21 : ℕ)), x10 = fun (x13 : Fin (21 : ℕ)) => Decidable.decide (x13 = x12)) → x1 x7 x9 (List.ofFn fun (x13 : Fin (21 : ℕ)) => x10 x13 && x1 x6 (x8 x13) (List.ofFn x11)) = x1 x3 x4 (List.ofFn (Fin.append x10 x11))) :=
  fun x3 x4 hSpec =>
    let hNE : x4.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr fun hEmp =>
        Exists.elim
          ((hSpec fun _ => Bool.false).mp
            (hEmp ▸ (decide_eq_true fun _ hw => False.elim (Finset.notMem_empty _ hw))))
          fun _ hp => Exists.elim hp fun _ hl => Bool.false_ne_true hl.2.1
    Or.elim (Nat.eq_or_lt_of_le (Finset.one_le_card.mpr hNE))
      (fun hEq => hSingleOut x3 x4 ⟨hEq.symm, hSpec⟩)
      (fun hLt => hMultiOut x3 x4 ⟨hLt, hSpec⟩)
