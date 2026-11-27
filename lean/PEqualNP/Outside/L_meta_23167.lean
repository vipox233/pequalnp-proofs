import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23167 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30460 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [15, 16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
