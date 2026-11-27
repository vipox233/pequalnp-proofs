import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23864_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.not, [2]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [5, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [9, 10]⟩], 11⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 7 := by decide +kernel

end PEqualNP.Outside.L_meta_23864_aux

theorem PEqualNP.Outside.L_meta_23864 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4955 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23864_aux.circ, PEqualNP.Outside.L_meta_23864_aux.h_ok, PEqualNP.Outside.L_meta_23864_aux.h_sz, by decide +kernel⟩
