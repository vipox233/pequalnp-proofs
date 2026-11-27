import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18415_2
    (hCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x1 ∧
        x1.size ≤ (29 : ℕ) ∧
        x1.output < (17 : ℕ) + x1.size ∧
        x2 < (17 : ℕ) + x1.size ∧
        ∀ (x3 : Fin (17 : ℕ) → Bool),
          x1.eval (List.ofFn x3) =
            ((x3 (0 : Fin (17 : ℕ)) && (x3 (6 : Fin (17 : ℕ)) || x3 (7 : Fin (17 : ℕ)) || x3 (8 : Fin (17 : ℕ)) || x3 (15 : Fin (17 : ℕ)))) ||
             (x3 (1 : Fin (17 : ℕ)) && (x3 (9 : Fin (17 : ℕ)) || x3 (10 : Fin (17 : ℕ)) || x3 (11 : Fin (17 : ℕ)) || x3 (15 : Fin (17 : ℕ)))) ||
             (x3 (2 : Fin (17 : ℕ)) && (x3 (12 : Fin (17 : ℕ)) || x3 (13 : Fin (17 : ℕ)) || x3 (14 : Fin (17 : ℕ)) || x3 (15 : Fin (17 : ℕ)))) ||
             (x3 (3 : Fin (17 : ℕ)) && (x3 (6 : Fin (17 : ℕ)) || x3 (9 : Fin (17 : ℕ)) || x3 (12 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ)))) ||
             (x3 (4 : Fin (17 : ℕ)) && (x3 (7 : Fin (17 : ℕ)) || x3 (10 : Fin (17 : ℕ)) || x3 (13 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ)))) ||
             (x3 (5 : Fin (17 : ℕ)) && (x3 (8 : Fin (17 : ℕ)) || x3 (11 : Fin (17 : ℕ)) || x3 (14 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ))))) ∧
          (x1.eval (List.ofFn x3) = Bool.false →
            (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (15 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ)))))
    (hStarEquiv :
      ∀ (x3 : Fin (17 : ℕ) → Bool),
        ((x3 (0 : Fin (17 : ℕ)) && (x3 (6 : Fin (17 : ℕ)) || x3 (7 : Fin (17 : ℕ)) || x3 (8 : Fin (17 : ℕ)) || x3 (15 : Fin (17 : ℕ)))) ||
         (x3 (1 : Fin (17 : ℕ)) && (x3 (9 : Fin (17 : ℕ)) || x3 (10 : Fin (17 : ℕ)) || x3 (11 : Fin (17 : ℕ)) || x3 (15 : Fin (17 : ℕ)))) ||
         (x3 (2 : Fin (17 : ℕ)) && (x3 (12 : Fin (17 : ℕ)) || x3 (13 : Fin (17 : ℕ)) || x3 (14 : Fin (17 : ℕ)) || x3 (15 : Fin (17 : ℕ)))) ||
         (x3 (3 : Fin (17 : ℕ)) && (x3 (6 : Fin (17 : ℕ)) || x3 (9 : Fin (17 : ℕ)) || x3 (12 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ)))) ||
         (x3 (4 : Fin (17 : ℕ)) && (x3 (7 : Fin (17 : ℕ)) || x3 (10 : Fin (17 : ℕ)) || x3 (13 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ)))) ||
         (x3 (5 : Fin (17 : ℕ)) && (x3 (8 : Fin (17 : ℕ)) || x3 (11 : Fin (17 : ℕ)) || x3 (14 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ))))) = Bool.true ↔
        ∃ (x5 : Fin (17 : ℕ)) (x6 : Fin (17 : ℕ)),
          (↑x5 < (6 : ℕ) ∧ (↑x6 = (15 : ℕ) + ↑x5 / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑x6 ∧ ↑x6 < (15 : ℕ) ∧ (if ↑x5 < (3 : ℕ) then (↑x6 - (6 : ℕ)) / (3 : ℕ) else (↑x6 - (6 : ℕ)) % (3 : ℕ)) = ↑x5 % (3 : ℕ))) ∧
          x3 x5 = Bool.true ∧ x3 x6 = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (29 : ℕ) ∧       x1.output < (17 : ℕ) + x1.size ∧         x2 < (17 : ℕ) + x1.size ∧           ∀ (x3 : Fin (17 : ℕ) → Bool),             have x4 : Fin (17 : ℕ) → Fin (17 : ℕ) → Prop := fun (x4 x5 : Fin (17 : ℕ)) => ↑x4 < (6 : ℕ) ∧ (↑x5 = (15 : ℕ) + ↑x4 / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑x5 ∧ ↑x5 < (15 : ℕ) ∧ (if ↑x4 < (3 : ℕ) then (↑x5 - (6 : ℕ)) / (3 : ℕ) else (↑x5 - (6 : ℕ)) % (3 : ℕ)) = ↑x4 % (3 : ℕ));             (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (17 : ℕ)) (x6 : Fin (17 : ℕ)), x4 x5 x6 ∧ x3 x5 = Bool.true ∧ x3 x6 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (15 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ))))) := by
  obtain ⟨x1, x2, hM, hSz, hOut, hW, hEval⟩ := hCircuit
  refine ⟨x1, x2, hM, hSz, hOut, hW, fun x3 => ?_⟩
  exact ⟨⟨fun h => (hStarEquiv x3).mp ((hEval x3).1.symm.trans h), fun h => (hEval x3).1.trans ((hStarEquiv x3).mpr h)⟩, (hEval x3).2⟩
