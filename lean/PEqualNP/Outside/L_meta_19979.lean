import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19979
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [9, 15]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [24, 18]⟩, ⟨.and, [2, 25]⟩, ⟨.or, [8, 24]⟩, ⟨.or, [13, 27]⟩, ⟨.or, [15, 28]⟩, ⟨.and, [3, 29]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [12, 31]⟩, ⟨.or, [9, 32]⟩, ⟨.or, [14, 33]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [27, 21]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [31, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [42, 26]⟩, ⟨.or, [43, 30]⟩, ⟨.or, [44, 35]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

end PEqualNP.Outside.L_meta_19979

open PEqualNP.Outside.L_meta_19979 PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19979 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
