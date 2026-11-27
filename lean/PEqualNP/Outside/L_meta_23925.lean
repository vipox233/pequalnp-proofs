import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23925 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (92 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩,
      ⟨.or, [2, 5]⟩,
      ⟨.and, [0, 6]⟩,
      ⟨.or, [0, 6]⟩,
      ⟨.not, [8]⟩,
      ⟨.or, [7, 9]⟩], 10⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
