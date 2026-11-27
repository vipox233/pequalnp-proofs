import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23505_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [1, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 11]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 12]⟩], 13⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 8 := by decide +kernel

end PEqualNP.Outside.L_meta_23505_aux

theorem PEqualNP.Outside.L_meta_23505 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17167 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23505_aux.circ, PEqualNP.Outside.L_meta_23505_aux.h_ok, PEqualNP.Outside.L_meta_23505_aux.h_sz, by decide +kernel⟩
