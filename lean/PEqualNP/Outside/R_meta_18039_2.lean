import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18039_2
    (hFix1 :
      have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true;
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        (∀ (x6 : Fin (26 : ℕ) → Bool), x6 (0 : Fin (26 : ℕ)) = Bool.false → x6 (13 : Fin (26 : ℕ)) = Bool.false → x6 (1 : Fin (26 : ℕ)) = Bool.false → (x2.eval (List.ofFn x6) = Bool.true ↔ x1 x6)) →
        (52 : ℕ) ≤ x2.size)
    (hFix2 :
      have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true;
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        (∀ (x6 : Fin (26 : ℕ) → Bool), x6 (0 : Fin (26 : ℕ)) = Bool.false → x6 (13 : Fin (26 : ℕ)) = Bool.false → x6 (2 : Fin (26 : ℕ)) = Bool.false → (x2.eval (List.ofFn x6) = Bool.true ↔ x1 x6)) →
        (51 : ℕ) ≤ x2.size) :
    (have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x2 → x3 = (1 : Fin (26 : ℕ)) ∨ x3 = (2 : Fin (26 : ℕ)) → (∀ (x6 : Fin (26 : ℕ) → Bool), x6 (0 : Fin (26 : ℕ)) = Bool.false → x6 (13 : Fin (26 : ℕ)) = Bool.false → x6 x3 = Bool.false → (x2.eval (List.ofFn x6) = Bool.true ↔ x1 x6)) → (if x3 = (1 : Fin (26 : ℕ)) then (52 : ℕ) else (51 : ℕ)) ≤ x2.size) := by
  intro x1 x2 x3 hM hOr hEval
  rcases hOr with rfl | rfl
  · simpa using hFix1 x2 hM hEval
  · simpa using hFix2 x2 hM hEval
