import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17205_2
    (hCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x1 ∧
        x1.size ≤ (28 : ℕ) ∧
        x1.output < (23 : ℕ) + x1.size ∧
        ∀ (x2 : Fin (17 : ℕ) → Bool),
          x1.eval (List.ofFn x2 ++ [x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)), x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ))]) =
            ((x2 (0 : Fin (17 : ℕ)) && (x2 (6 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)))) ||
             (x2 (1 : Fin (17 : ℕ)) && (x2 (6 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (13 : Fin (17 : ℕ)))) ||
             (x2 (2 : Fin (17 : ℕ)) && (x2 (6 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (15 : Fin (17 : ℕ)) || x2 (16 : Fin (17 : ℕ)))) ||
             (x2 (3 : Fin (17 : ℕ)) && (x2 (7 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)))) ||
             (x2 (4 : Fin (17 : ℕ)) && (x2 (7 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (15 : Fin (17 : ℕ)))) ||
             (x2 (5 : Fin (17 : ℕ)) && (x2 (7 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)) || x2 (13 : Fin (17 : ℕ)) || x2 (16 : Fin (17 : ℕ))))))
    (hStarEquiv :
      ∀ (x2 : Fin (17 : ℕ) → Bool),
        ((x2 (0 : Fin (17 : ℕ)) && (x2 (6 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)))) ||
         (x2 (1 : Fin (17 : ℕ)) && (x2 (6 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (13 : Fin (17 : ℕ)))) ||
         (x2 (2 : Fin (17 : ℕ)) && (x2 (6 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (15 : Fin (17 : ℕ)) || x2 (16 : Fin (17 : ℕ)))) ||
         (x2 (3 : Fin (17 : ℕ)) && (x2 (7 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)))) ||
         (x2 (4 : Fin (17 : ℕ)) && (x2 (7 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (15 : Fin (17 : ℕ)))) ||
         (x2 (5 : Fin (17 : ℕ)) && (x2 (7 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)) || x2 (13 : Fin (17 : ℕ)) || x2 (16 : Fin (17 : ℕ))))) = Bool.true ↔
        ∃ (x3 : Fin (6 : ℕ)) (x4 : Fin (4 : ℕ)),
          x2 (Fin.ofNat (17 : ℕ) ↑x3) = Bool.true ∧
          x2 (Fin.ofNat (17 : ℕ) (if ↑x4 = (0 : ℕ) then (6 : ℕ) + ↑x3 / (3 : ℕ) else (8 : ℕ) + if ↑x3 < (3 : ℕ) then (3 : ℕ) * ↑x3 + (↑x4 - (1 : ℕ)) else (3 : ℕ) * (↑x4 - (1 : ℕ)) + (↑x3 - (3 : ℕ)))) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (28 : ℕ) ∧ x1.output < (23 : ℕ) + x1.size ∧ ∀ (x2 : Fin (17 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)), x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (6 : ℕ)) (x4 : Fin (4 : ℕ)), x2 (Fin.ofNat (17 : ℕ) ↑x3) = Bool.true ∧ x2 (Fin.ofNat (17 : ℕ) (if ↑x4 = (0 : ℕ) then (6 : ℕ) + ↑x3 / (3 : ℕ) else (8 : ℕ) + if ↑x3 < (3 : ℕ) then (3 : ℕ) * ↑x3 + (↑x4 - (1 : ℕ)) else (3 : ℕ) * (↑x4 - (1 : ℕ)) + (↑x3 - (3 : ℕ)))) = Bool.true) := by
  obtain ⟨x1, hM, hSz, hOut, hEv⟩ := hCircuit
  refine ⟨x1, hM, hSz, hOut, fun x2 => ?_⟩
  exact ⟨fun h => (hStarEquiv x2).mp ((hEv x2).symm.trans h), fun h => (hEv x2).trans ((hStarEquiv x2).mpr h)⟩
