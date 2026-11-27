import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17858_3
    (hDiffEquiv :
      ∀ (a b : Fin (7 : ℕ)),
        ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] ↔
          (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))))
    (hCircuitDiff :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), ↑(x4 - x5) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) → ↑(x2 - x3) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] → x1.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) → x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) := by
  rcases hCircuitDiff with ⟨x1, hSz, hAO, hNd, hO1, hO2, hSound, hComp⟩
  refine ⟨x1, hSz, hAO, hNd, hO1, hO2, fun x2 hev => ?_, fun x2 x3 hne h => hComp x2 x3 hne ((hDiffEquiv x2 x3).mpr h)⟩
  rcases hSound x2 hev with ⟨x4, x5, hd, ha, hb⟩
  exact ⟨x4, x5, (hDiffEquiv x4 x5).mp hd, ha, hb⟩
