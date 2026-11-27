import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_22447 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881973 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨⟨[⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [5, 12]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [17, 18]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [20, 21]⟩], 22⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
