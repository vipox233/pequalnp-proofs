import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22198_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 3]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 6]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 8]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [7, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [13]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [11, 12]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [10, 15]⟩, ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [14, 16]⟩], 17⟩

lemma h_ok : FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma h_sz : circ.size ≤ 12 := by decide +kernel

end PEqualNP.Outside.L_meta_22198_aux

theorem PEqualNP.Outside.L_meta_22198 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17210 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_22198_aux.circ, PEqualNP.Outside.L_meta_22198_aux.h_ok, PEqualNP.Outside.L_meta_22198_aux.h_sz, by decide +kernel⟩
