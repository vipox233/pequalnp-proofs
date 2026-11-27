import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24528 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197439 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not, [5]⟩,
      ⟨.and, [2, 4]⟩,
      ⟨.not, [4]⟩,
      ⟨.and, [3, 8]⟩,
      ⟨.or, [7, 9]⟩,
      ⟨.or, [1, 10]⟩,
      ⟨.and, [6, 11]⟩,
      ⟨.or, [0, 12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
