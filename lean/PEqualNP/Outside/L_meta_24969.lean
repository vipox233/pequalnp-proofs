import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24969

def circuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [3, 2]⟩,
     ⟨.or, [1, 5]⟩,
     ⟨.and, [6, 7]⟩,
     ⟨.not, [8]⟩,
     ⟨.not, [4]⟩,
     ⟨.or, [1, 0]⟩,
     ⟨.and, [10, 11]⟩,
     ⟨.or, [6, 12]⟩,
     ⟨.and, [9, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24969

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_meta_24969 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408367 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_24969.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, PEqualNP.Outside.L_meta_24969.circuit]
  · decide +kernel
