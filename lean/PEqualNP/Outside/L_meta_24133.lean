import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24133 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275098 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [1, 2]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.and, [1, 4]⟩,
      ⟨.or, [0, 6]⟩,
      ⟨.or, [3, 6]⟩,
      ⟨.or, [5, 7]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [0, 9]⟩,
      ⟨.or, [10, 12]⟩,
      ⟨.or, [11, 13]⟩], 14⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
