import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23993

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [1, 7]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩], 12⟩

theorem gatesOK : ∀ g ∈ witness.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem evalOK : ∀ i j : Fin 5, witness.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25502 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23993

theorem PEqualNP.Outside.L_meta_23993 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (25502 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_23993.witness, PEqualNP.Outside.L_meta_23993.gatesOK, PEqualNP.Outside.L_meta_23993.sizeOK, PEqualNP.Outside.L_meta_23993.evalOK⟩
