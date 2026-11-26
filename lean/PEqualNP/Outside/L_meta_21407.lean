import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21407
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def circ : Circuit := ⟨[⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.or, [0, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [4, 16]⟩, ⟨GateOp.and, [17, 18]⟩, ⟨GateOp.or, [15, 19]⟩], 20⟩
theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (241276 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel
end PEqualNP.Outside.L_meta_21407

theorem PEqualNP.Outside.L_meta_21407 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241276 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_21407.circ, PEqualNP.Outside.L_meta_21407.mono, by decide, PEqualNP.Outside.L_meta_21407.rep⟩
