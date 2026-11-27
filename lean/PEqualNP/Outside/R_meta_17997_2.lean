import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17997_2
    (hStarCover :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∃ (x11 : Finset (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)))),
        (∀ (x12 x13 : Fin (13 : ℕ)), ((x12, x13) ∈ x11.biUnion fun (x14 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => x14.1 ×ˢ x14.2) ↔ x1 x12 x13) ∧
        ∑ x12 ∈ x11, (x12.1.card + x12.2.card) ≤ (65 : ℕ))
    (hLenLB :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (13 : ℕ))),
        (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ (x8 : Fin x2), x3 x8 = {x5} ∧ x4 x8 = {x6}) →
        (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) → (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x6 | x1 x10 x9}.card ≤ (2 : ℕ)) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x1 x10 x11}.card ≤ (2 : ℕ)) → ∃ (x11 : Fin x2), x3 x11 = x6 ∧ x4 x11 = x7) →
        have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x3 x8)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x4 x8)) x7 = Bool.true};
        ∀ (x8 : List (Set (Fin x2))),
          (∀ (x9 : Fin x8.length),
            have x10 : Set (Set (Fin x2)) := x7 ∪ {x10 : Set (Fin x2) | x10 ∈ List.take (↑x9) x8};
            ∃ x11 ∈ x10, ∃ x12 ∈ x10, x8.getD ↑x9 ∅ = x11 ∪ x12 ∨ x8.getD ↑x9 ∅ = x11 ∩ x12) →
          {x10 : Fin x2 | ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x1 x11 x12 ∧ x3 x10 = {x11} ∧ x4 x10 = {x12}} ∈ x7 ∪ {x10 : Set (Fin x2) | x10 ∈ x8} →
          (64 : ℕ) ≤ x8.length) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (13 : ℕ))),   (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → ∃ (x8 : Fin x2), x3 x8 = {x5} ∧ x4 x8 = {x6}) →     (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x6, ∀ x10 ∈ x7, ¬x1 x8 x10) → (∀ (x9 : Fin (13 : ℕ)), {x10 ∈ x6 | x1 x10 x9}.card ≤ (2 : ℕ)) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x1 x10 x11}.card ≤ (2 : ℕ)) → ∃ (x11 : Fin x2), x3 x11 = x6 ∧ x4 x11 = x7) →       have x7 : Set (Set (Fin x2)) := {∅, Set.univ} ∪ Set.range fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => {x8 : Fin x2 | Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x3 x8)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x4 x8)) x7 = Bool.true};       ∀ (x8 : List (Set (Fin x2))),         (∀ (x9 : Fin x8.length),             have x10 : Set (Set (Fin x2)) := x7 ∪ {x10 : Set (Fin x2) | x10 ∈ List.take (↑x9) x8};             ∃ x11 ∈ x10, ∃ x12 ∈ x10, x8.getD ↑x9 ∅ = x11 ∪ x12 ∨ x8.getD ↑x9 ∅ = x11 ∩ x12) →           {x10 : Fin x2 | ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x1 x11 x12 ∧ x3 x10 = {x11} ∧ x4 x10 = {x12}} ∈ x7 ∪ {x10 : Set (Fin x2) | x10 ∈ x8} → ∃ (x11 : Finset (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)))), (∀ (x12 x13 : Fin (13 : ℕ)), ((x12, x13) ∈ x11.biUnion fun (x14 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => x14.1 ×ˢ x14.2) ↔ x1 x12 x13) ∧ ∑ x12 ∈ x11, (x12.1.card + x12.2.card) ≤ x8.length + (1 : ℕ)) :=
  fun x2 x3 x4 hPos hNeg x8 hProg hTarget =>
    Exists.elim hStarCover fun cov hCov =>
      ⟨cov, hCov.1, Nat.le_trans hCov.2 (Nat.succ_le_succ (hLenLB x2 x3 x4 hPos hNeg x8 hProg hTarget))⟩
