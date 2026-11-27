import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22491 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (408 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 3]⟩,
      ⟨.or, [6, 4]⟩,
      ⟨.or, [7, 5]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [1, 9]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.and, [0, 11]⟩,
      ⟨.or, [10, 12]⟩], 13⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
