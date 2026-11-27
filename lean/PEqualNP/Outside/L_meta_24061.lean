import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24061 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13148 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩,
      ⟨.and, [0, 5]⟩,
      ⟨.or, [1, 2]⟩,
      ⟨.or, [0, 2]⟩,
      ⟨.or, [1, 4]⟩,
      ⟨.and, [8, 9]⟩,
      ⟨.not, [10]⟩,
      ⟨.and, [7, 11]⟩,
      ⟨.or, [6, 12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
