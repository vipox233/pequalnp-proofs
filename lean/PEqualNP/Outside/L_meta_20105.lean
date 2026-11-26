import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20105_aux

def circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [11, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [15, 21]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [11, 20]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [12, 23]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [7, 30]⟩, ⟨.and, [6, 22]⟩, ⟨.and, [4, 24]⟩, ⟨.and, [0, 25]⟩, ⟨.and, [2, 29]⟩, ⟨.and, [5, 27]⟩, ⟨.and, [3, 26]⟩, ⟨.and, [1, 28]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [39, 33]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 35]⟩, ⟨.or, [42, 36]⟩, ⟨.or, [43, 37]⟩, ⟨.or, [44, 38]⟩], 45⟩

end PEqualNP.Outside.L_meta_20105_aux

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_meta_20105 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6455152135695128040 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨PEqualNP.Outside.L_meta_20105_aux.circuit, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, PEqualNP.Outside.L_meta_20105_aux.circuit]
  · decide +kernel
