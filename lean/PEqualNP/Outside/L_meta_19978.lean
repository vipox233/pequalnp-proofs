import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19978
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [3, 14]⟩, ⟨GateOp.and, [13, 6]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [4, 18]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [11, 1]⟩, ⟨GateOp.or, [8, 5]⟩, ⟨GateOp.or, [15, 19]⟩, ⟨GateOp.or, [13, 7]⟩, ⟨GateOp.or, [24, 15]⟩, ⟨GateOp.or, [6, 25]⟩, ⟨GateOp.or, [24, 20]⟩, ⟨GateOp.or, [26, 4]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.or, [27, 18]⟩, ⟨GateOp.or, [17, 21]⟩, ⟨GateOp.or, [26, 22]⟩, ⟨GateOp.and, [16, 32]⟩, ⟨GateOp.and, [9, 28]⟩, ⟨GateOp.and, [23, 29]⟩, ⟨GateOp.and, [30, 31]⟩, ⟨GateOp.or, [35, 33]⟩, ⟨GateOp.or, [34, 37]⟩, ⟨GateOp.or, [38, 36]⟩], 39⟩

end PEqualNP.Outside.L_meta_19978

theorem PEqualNP.Outside.L_meta_19978 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5360062095110517900 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  refine ⟨PEqualNP.Outside.L_meta_19978.circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19978.circuit, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
