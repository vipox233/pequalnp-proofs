import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17463_2
    (hTargetNotBasis :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (13 : ℕ))),
        ((∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ (x8 : Fin x2), x3 x8 = {x5} ∧ x4 x8 = {x6}) ∧
          (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) → (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x6 | x1 x10 x9}.card ≤ (2 : ℕ)) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x1 x10 x11}.card ≤ (2 : ℕ)) → ∃ (x11 : Fin x2), x3 x11 = x6 ∧ x4 x11 = x7)) →
        have T : Set (Fin x2) := {x11 : Fin x2 | ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x1 x12 x13 ∧ x3 x11 = {x12} ∧ x4 x11 = {x13}};
        T ≠ ∅ ∧ T ≠ Set.univ ∧ ∀ (i : Fin ((13 : ℕ) + (13 : ℕ))), T ≠ {x8 : Fin x2 | Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x3 x8)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x4 x8)) i = Bool.true})
    (hTargetInList :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (13 : ℕ))),
        have x7 : Set (Set (Fin x2)) := ({∅, Set.univ} : Set (Set (Fin x2))) ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x3 x8)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x4 x8)) x7 = Bool.true};
        ∀ (x8 : List (Set (Fin x2))),
          ((∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ (x8 : Fin x2), x3 x8 = {x5} ∧ x4 x8 = {x6}) ∧
            (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) → (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x6 | x1 x10 x9}.card ≤ (2 : ℕ)) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x1 x10 x11}.card ≤ (2 : ℕ)) → ∃ (x11 : Fin x2), x3 x11 = x6 ∧ x4 x11 = x7) ∧
            x8.length ≤ (63 : ℕ) ∧
            (∀ (x10 : Fin x8.length), x8.getD ↑x10 ∅ ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8} ∧ ∃ x11 ∈ x7 ∪ {x12 : Set (Fin x2) | x12 ∈ List.take (↑x10) x8}, ∃ x12 ∈ x7 ∪ {x13 : Set (Fin x2) | x13 ∈ List.take (↑x10) x8}, x8.getD ↑x10 ∅ = x11 ∪ x12 ∨ x8.getD ↑x10 ∅ = x11 ∩ x12) ∧
            {x11 : Fin x2 | ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x1 x12 x13 ∧ x3 x11 = {x12} ∧ x4 x11 = {x13}} ∈ x8) →
          (51 : ℕ) ≤ {x12 : Fin x8.length | ¬∃ x13 ∈ x7 ∪ {x14 : Set (Fin x2) | x14 ∈ List.take (↑x12) x8}, ∃ x14 ∈ x7 ∪ {x15 : Set (Fin x2) | x15 ∈ List.take (↑x12) x8}, x8.getD ↑x12 ∅ = x13 ∩ x14}.ncard) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (13 : ℕ))),   (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ (x8 : Fin x2), x3 x8 = {x5} ∧ x4 x8 = {x6}) →     (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) → (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x6 | x1 x10 x9}.card ≤ (2 : ℕ)) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x1 x10 x11}.card ≤ (2 : ℕ)) → ∃ (x11 : Fin x2), x3 x11 = x6 ∧ x4 x11 = x7) →       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x3 x8)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x4 x8)) x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))), x8.length ≤ (63 : ℕ) → (∀ (x10 : Fin x8.length), x8.getD ↑x10 ∅ ∉ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ List.take (↑x10) x8} ∧ ∃ x11 ∈ x7 ∪ {x12 : Set (Fin x2) | x12 ∈ List.take (↑x10) x8}, ∃ x12 ∈ x7 ∪ {x13 : Set (Fin x2) | x13 ∈ List.take (↑x10) x8}, x8.getD ↑x10 ∅ = x11 ∪ x12 ∨ x8.getD ↑x10 ∅ = x11 ∩ x12) → {x11 : Fin x2 | ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x1 x12 x13 ∧ x3 x11 = {x12} ∧ x4 x11 = {x13}} ∈ x7 ∪ {x11 : Set (Fin x2) | x11 ∈ x8} → (51 : ℕ) ≤ {x12 : Fin x8.length | ¬∃ x13 ∈ x7 ∪ {x14 : Set (Fin x2) | x14 ∈ List.take (↑x12) x8}, ∃ x14 ∈ x7 ∪ {x15 : Set (Fin x2) | x15 ∈ List.take (↑x12) x8}, x8.getD ↑x12 ∅ = x13 ∩ x14}.ncard) :=
  fun x2 x3 x4 hPos hNeg x8 hLen hStep hMem =>
    Or.elim hMem
      (fun hB =>
        let hNB := hTargetNotBasis x2 x3 x4 ⟨hPos, hNeg⟩
        False.elim
          (Or.elim hB
            (fun h01 => Or.elim h01 hNB.1 (fun hu => hNB.2.1 (Set.mem_singleton_iff.mp hu)))
            (fun hr => Exists.elim hr fun i hi => hNB.2.2 i hi.symm)))
      (fun hInL => hTargetInList x2 x3 x4 x8 ⟨hPos, hNeg, hLen, hStep, hInL⟩)
