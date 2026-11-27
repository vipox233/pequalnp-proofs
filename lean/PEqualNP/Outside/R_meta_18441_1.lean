import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-18441`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_18441_1 :
    (∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2 → (17 : ℕ) ≤ x1.size + x2.size → x1.size + x2.size ≤ (18 : ℕ) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (x1.wires (List.ofFn x7) ++ [!x1.eval (List.ofFn x7)]) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (10 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (10 : ℕ) (x8 % (10 : ℕ)))) →
    (∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2 → (17 : ℕ) ≤ x1.size + x2.size → x1.size + x2.size ≤ (18 : ℕ) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (x1.wires (List.ofFn x7) ++ [!x1.eval (List.ofFn x7)]) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (10 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (10 : ℕ) (x8 % (10 : ℕ)))) →
    (∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.Monotone2 x2 → (17 : ℕ) ≤ x1.size + x2.size → x1.size + x2.size ≤ (18 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x2.eval (x1.wires (List.ofFn x7) ++ [!x1.eval (List.ofFn x7)]) = [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x8 : ℕ) => x7 (Fin.ofNat (10 : ℕ) (x8 / (10 : ℕ))) && x7 (Fin.ofNat (10 : ℕ) (x8 % (10 : ℕ)))) := by
  classical
  intro h1 h2 x1 x2
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
