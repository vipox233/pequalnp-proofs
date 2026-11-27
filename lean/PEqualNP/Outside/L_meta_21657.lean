import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21657_aux

-- The circuit; the kernel replays it on the inputs the statement asks about.
def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [12, 11]⟩], 13⟩

end PEqualNP.Outside.L_meta_21657_aux

theorem PEqualNP.Outside.L_meta_21657 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13085 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21657_aux.wit, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_21657_aux.wit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
