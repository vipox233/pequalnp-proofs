import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22465

def C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [15, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [16]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 17]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [19, 18]⟩], 20⟩

theorem mono : PEqualNP.MetaComplexity.FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
theorem pts : ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18105 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22465

theorem PEqualNP.Outside.L_meta_22465 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18105 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22465.C, PEqualNP.Outside.L_meta_22465.mono, by decide, PEqualNP.Outside.L_meta_22465.pts⟩
