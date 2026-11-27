import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17781_2
    (hLenLo : ∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),
      (35 : ℕ) ≤ x1.length →
        x1.length ≤ (42 : ℕ) →
          ∃ (x4 : Fin (16 : ℕ)) (x5 : Fin (13 : ℕ)) (x6 : Fin (3 : ℕ)),
            have x7 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x7 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) (x7.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x7.2 (0 : Fin (13 : ℕ))) ∨ x8 = Fin.natAdd (13 : ℕ) x7.1);
            let x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x8 x9 : Fin (13 : ℕ)) => x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ));
            have x9 : Fin (13 : ℕ) → Bool := fun (y : Fin (13 : ℕ)) => ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x4 (0 : ℕ)).testBit ↑((y - x5) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6 (0 : Fin (13 : ℕ)));
            have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide ((∃ (x11 : Fin (13 : ℕ)), x9 x11 = Bool.true ∧ x10 = Fin.castAdd (13 : ℕ) x11) ∨ ∃ (x11 : Fin (13 : ℕ)), x10 = Fin.natAdd (13 : ℕ) x11 ∧ ∀ (x12 : Fin (13 : ℕ)), x9 x12 = Bool.true → ¬x8 x12 x11);
            ¬List.foldl (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x13 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 x13 ∨ x13 ⊆ x12.1 ∪ x12.2 ∧ x11 x12.1 ∧ x11 x12.2) (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 = ∅ ∨ ∃ (x12 : Fin (26 : ℕ)), x10 x12 = Bool.false ∧ ∀ x13 ∈ x11, x7 x13 x12 = Bool.true) x1 Finset.univ)
    (hLenHi : ∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),
      (43 : ℕ) ≤ x1.length →
        x1.length ≤ (50 : ℕ) →
          ∃ (x4 : Fin (16 : ℕ)) (x5 : Fin (13 : ℕ)) (x6 : Fin (3 : ℕ)),
            have x7 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x7 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) (x7.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x7.2 (0 : Fin (13 : ℕ))) ∨ x8 = Fin.natAdd (13 : ℕ) x7.1);
            let x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x8 x9 : Fin (13 : ℕ)) => x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ));
            have x9 : Fin (13 : ℕ) → Bool := fun (y : Fin (13 : ℕ)) => ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x4 (0 : ℕ)).testBit ↑((y - x5) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6 (0 : Fin (13 : ℕ)));
            have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide ((∃ (x11 : Fin (13 : ℕ)), x9 x11 = Bool.true ∧ x10 = Fin.castAdd (13 : ℕ) x11) ∨ ∃ (x11 : Fin (13 : ℕ)), x10 = Fin.natAdd (13 : ℕ) x11 ∧ ∀ (x12 : Fin (13 : ℕ)), x9 x12 = Bool.true → ¬x8 x12 x11);
            ¬List.foldl (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x13 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 x13 ∨ x13 ⊆ x12.1 ∪ x12.2 ∧ x11 x12.1 ∧ x11 x12.2) (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 = ∅ ∨ ∃ (x12 : Fin (26 : ℕ)), x10 x12 = Bool.false ∧ ∀ x13 ∈ x11, x7 x13 x12 = Bool.true) x1 Finset.univ) :
    (∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),   (35 : ℕ) ≤ x1.length →     x1.length ≤ (50 : ℕ) →       ∃ (x4 : Fin (16 : ℕ)) (x5 : Fin (13 : ℕ)) (x6 : Fin (3 : ℕ)),         have x7 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x7 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) (x7.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x7.2 (0 : Fin (13 : ℕ))) ∨ x8 = Fin.natAdd (13 : ℕ) x7.1);         let x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x8 x9 : Fin (13 : ℕ)) => x8 = x9 ∨ x8 = x9 + (1 : Fin (13 : ℕ)) ∨ x8 = x9 + (3 : Fin (13 : ℕ)) ∨ x8 = x9 + (9 : Fin (13 : ℕ));         have x9 : Finset (Fin (13 : ℕ)) := {x9 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x4 (0 : ℕ)).testBit ↑((x9 - x5) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6 (0 : Fin (13 : ℕ))) = Bool.true};         have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide ((∃ x11 ∈ x9, x10 = Fin.castAdd (13 : ℕ) x11) ∨ ∃ (x11 : Fin (13 : ℕ)), x10 = Fin.natAdd (13 : ℕ) x11 ∧ ∀ x12 ∈ x9, ¬x8 x12 x11);         ¬List.foldl (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x13 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 x13 ∨ x13 ⊆ x12.1 ∪ x12.2 ∧ x11 x12.1 ∧ x11 x12.2) (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 = ∅ ∨ ∃ (x12 : Fin (26 : ℕ)), x10 x12 = Bool.false ∧ ∀ x13 ∈ x11, x7 x13 x12 = Bool.true) x1 Finset.univ) := by
  intro x1 hlo hhi
  obtain ⟨x4, x5, x6, h⟩ := Or.elim (Nat.lt_or_ge x1.length (43 : ℕ))
    (fun hlt => hLenLo x1 hlo (Nat.le_of_lt_succ hlt))
    (fun hge => hLenHi x1 hge hhi)
  refine ⟨x4, x5, x6, ?_⟩
  let f : (Fin (26 : ℕ) → Bool) → Prop := fun g =>
    ¬List.foldl (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x13 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 x13 ∨ x13 ⊆ x12.1 ∪ x12.2 ∧ x11 x12.1 ∧ x11 x12.2)
      (fun (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x11 = ∅ ∨ ∃ (x12 : Fin (26 : ℕ)), g x12 = Bool.false ∧ ∀ x13 ∈ x11, Decidable.decide (x12 = Fin.castAdd (13 : ℕ) (x13.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x13.2 (0 : Fin (13 : ℕ))) ∨ x12 = Fin.natAdd (13 : ℕ) x13.1) = Bool.true)
      x1 Finset.univ
  change f _ at h
  change f _
  suffices heq : _ = _ by exact congrArg f heq ▸ h
  funext x10
  apply decide_eq_decide.mpr
  constructor <;> intro ho <;> rcases ho with ⟨a, ha1, ha2⟩ | ⟨a, ha1, ha2⟩
  · exact Or.inl ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha1⟩, ha2⟩
  · exact Or.inr ⟨a, ha1, fun b hb => ha2 b (Finset.mem_filter.mp hb).2⟩
  · exact Or.inl ⟨a, (Finset.mem_filter.mp ha1).2, ha2⟩
  · exact Or.inr ⟨a, ha1, fun b hb => ha2 b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩)⟩
