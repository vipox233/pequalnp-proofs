import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17233_3
    (hOutInBounds : ∀ (x1 x2 : Fin (14 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 ≠ x2 →
      Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min ↑x1 ↑x2 + Max.max ↑x1 ↑x2) = Bool.true →
      ¬(Min.min ↑x1 ↑x2 = (0 : ℕ) ∧ Max.max ↑x1 ↑x2 = (7 : ℕ)) →
      x3.size ≤ (26 : ℕ) →
      PEqualNP.TopForm.IsAO2 (15 : ℕ) x3 →
      (∀ x9 < x3.size, PEqualNP.TopForm.opnd x3 x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x3 x9 (1 : Fin (2 : ℕ))) →
      (∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x1 || x10 x2]) = Bool.true ↔
        ∃ (x11 x12 : Fin (7 : ℕ)), (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
          x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) →
      (15 : ℕ) ≤ x3.output ∧ x3.output < (15 : ℕ) + x3.size)
    (hOrderedInBounds : ∀ (x1 x2 : Fin (14 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      x1 < x2 →
      (15 : ℕ) ≤ x3.output ∧ x3.output < (15 : ℕ) + x3.size →
      Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * ↑x1 + ↑x2) = Bool.true →
      ¬(↑x1 = (0 : ℕ) ∧ ↑x2 = (7 : ℕ)) →
      x3.size ≤ (26 : ℕ) →
      PEqualNP.TopForm.IsAO2 (15 : ℕ) x3 →
      (∀ x9 < x3.size, PEqualNP.TopForm.opnd x3 x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x3 x9 (1 : Fin (2 : ℕ))) →
      (∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x1 || x10 x2]) = Bool.true ↔
        ∃ (x11 x12 : Fin (7 : ℕ)), (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
          x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) →
      ∃ (x11 : Bool), ((PEqualNP.ReadK.linearParts x3 (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && ((↑x1 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑x2 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [↑x1 == (0 : ℕ) || ↑x1 == (7 : ℕ) || (↑x2 == (0 : ℕ) || ↑x2 == (7 : ℕ))])).getD x3.output (Bool.false, Bool.false)).2 = Bool.true) :
    ∀ (x1 x2 : Fin (14 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), x1 ≠ x2 → Nat.testBit (365118556550 : ℕ) ((14 : ℕ) * Min.min ↑x1 ↑x2 + Max.max ↑x1 ↑x2) = Bool.true → ¬(Min.min ↑x1 ↑x2 = (0 : ℕ) ∧ Max.max ↑x1 ↑x2 = (7 : ℕ)) → x3.size ≤ (26 : ℕ) → PEqualNP.TopForm.IsAO2 (15 : ℕ) x3 → (∀ x9 < x3.size, PEqualNP.TopForm.opnd x3 x9 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x3 x9 (1 : Fin (2 : ℕ))) → (∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x1 || x10 x2]) = Bool.true ↔ ∃ (x11 : Fin (7 : ℕ)) (x12 : Fin (7 : ℕ)), (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧ x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true) → ∃ (x11 : Bool), ((PEqualNP.ReadK.linearParts x3 (fun (x12 : ℕ) => (x12 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || x12 == (14 : ℕ) && ((↑x1 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ)) || ↑x2 == if x11 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.map (fun (x12 : ℕ) => x12 == (0 : ℕ) || x12 == (7 : ℕ)) (List.range (14 : ℕ)) ++ [↑x1 == (0 : ℕ) || ↑x1 == (7 : ℕ) || (↑x2 == (0 : ℕ) || ↑x2 == (7 : ℕ))])).getD x3.output (Bool.false, Bool.false)).2 = Bool.true := by
  intro x1 x2 x3 hne hbit hnot07 hsz hAO hdist hEval
  have hob := hOutInBounds x1 x2 x3 hne hbit hnot07 hsz hAO hdist hEval
  rcases lt_or_gt_of_ne hne with h12 | h21
  · have hmn : Min.min (x1 : ℕ) (x2 : ℕ) = (x1 : ℕ) := Nat.min_eq_left (Nat.le_of_lt h12)
    have hmx : Max.max (x1 : ℕ) (x2 : ℕ) = (x2 : ℕ) := Nat.max_eq_right (Nat.le_of_lt h12)
    rw [hmn, hmx] at hbit hnot07
    exact hOrderedInBounds x1 x2 x3 h12 hob hbit hnot07 hsz hAO hdist hEval
  · have hmn : Min.min (x1 : ℕ) (x2 : ℕ) = (x2 : ℕ) := Nat.min_eq_right (Nat.le_of_lt h21)
    have hmx : Max.max (x1 : ℕ) (x2 : ℕ) = (x1 : ℕ) := Nat.max_eq_left (Nat.le_of_lt h21)
    rw [hmn, hmx] at hbit hnot07
    have hEval' : ∀ (x10 : Fin (14 : ℕ) → Bool), x3.eval (List.ofFn x10 ++ [x10 x2 || x10 x1]) = Bool.true ↔
        ∃ (x11 x12 : Fin (7 : ℕ)), (x11 = x12 ∨ x11 = x12 + (1 : Fin (7 : ℕ)) ∨ x11 = x12 + (3 : Fin (7 : ℕ))) ∧
          x10 (Fin.castAdd (7 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (7 : ℕ) x12) = Bool.true := by
      intro x10
      have hx := hEval x10
      rw [Bool.or_comm (x10 x1) (x10 x2)] at hx
      exact hx
    obtain ⟨b, hb⟩ := hOrderedInBounds x2 x1 x3 h21 hob hbit hnot07 hsz hAO hdist hEval'
    refine ⟨b, ?_⟩
    rw [Bool.or_comm (↑x1 == if b = Bool.true then (7 : ℕ) else (0 : ℕ)) (↑x2 == if b = Bool.true then (7 : ℕ) else (0 : ℕ)),
        Bool.or_comm (↑x1 == (0 : ℕ) || ↑x1 == (7 : ℕ)) (↑x2 == (0 : ℕ) || ↑x2 == (7 : ℕ))]
    exact hb
