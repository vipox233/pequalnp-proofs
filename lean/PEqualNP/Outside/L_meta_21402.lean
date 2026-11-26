import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21402 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114429 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩,
      ⟨.or, [9, 3]⟩,
      ⟨.and, [10, 5]⟩,
      ⟨.or, [0, 2]⟩,
      ⟨.or, [6, 7]⟩,
      ⟨.and, [12, 13]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [6, 8]⟩,
      ⟨.and, [15, 16]⟩,
      ⟨.or, [11, 14]⟩,
      ⟨.or, [18, 17]⟩,
      ⟨.or, [19, 4]⟩], 20⟩
  refine ⟨witness, ?_, by decide, by decide +kernel⟩
  intro gate hgate
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
