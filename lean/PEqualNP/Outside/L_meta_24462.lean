import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24462 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101946 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.and, [2, 6]⟩,
      ⟨.and, [1, 7]⟩,
      ⟨.or, [1, 7]⟩,
      ⟨.and, [0, 10]⟩,
      ⟨.or, [8, 11]⟩,
      ⟨.or, [9, 12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
