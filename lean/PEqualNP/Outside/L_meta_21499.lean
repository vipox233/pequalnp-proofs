import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21499_aux
open PEqualNP.CircuitLowerBounds

private def witnessCircuit : Circuit :=
  ⟨[⟨.not, [0]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.not, [8]⟩], 9⟩

private theorem fanIn : PEqualNP.MetaComplexity.FanInTwo witnessCircuit := by
  intro g hg
  simp only [witnessCircuit, List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21499_aux

open PEqualNP.Outside.L_meta_21499_aux in
theorem PEqualNP.Outside.L_meta_21499 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (71 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨witnessCircuit,fanIn,by decide,?_⟩
  decide +kernel
