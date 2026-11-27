import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21756

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [3, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [6, 9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 13]⟩], 16⟩

theorem mono : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem pts : ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283486 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21756

theorem PEqualNP.Outside.L_meta_21756 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283486 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21756.C, PEqualNP.Outside.L_meta_21756.mono, by decide, PEqualNP.Outside.L_meta_21756.pts⟩
