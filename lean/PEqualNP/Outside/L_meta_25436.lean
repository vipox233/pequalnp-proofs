import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25436_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 4]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 10]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [13, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [14]⟩], 15⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 10 := by decide +kernel

end PEqualNP.Outside.L_meta_25436_aux

theorem PEqualNP.Outside.L_meta_25436 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549423 : ℕ).testBit (6 * min i.val j.val + max i.val j.val))  := by
  exact ⟨PEqualNP.Outside.L_meta_25436_aux.circ, PEqualNP.Outside.L_meta_25436_aux.h_ok, PEqualNP.Outside.L_meta_25436_aux.h_sz, by decide +kernel⟩
