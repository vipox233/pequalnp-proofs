import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-18773`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_18773_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (10 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ)))) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (10 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ)))) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (10 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ)))) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
