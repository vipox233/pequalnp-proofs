import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19992
open PEqualNP.CircuitLowerBounds

def witness : Circuit := ⟨[⟨.or, [13, 14]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [21, 23]⟩, ⟨.and, [0, 25]⟩, ⟨.and, [1, 28]⟩, ⟨.and, [2, 29]⟩, ⟨.and, [3, 26]⟩, ⟨.and, [4, 27]⟩, ⟨.and, [5, 30]⟩, ⟨.and, [6, 31]⟩, ⟨.and, [7, 24]⟩, ⟨.or, [39, 32]⟩, ⟨.or, [40, 33]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 37]⟩, ⟨.or, [45, 38]⟩], 46⟩

end PEqualNP.Outside.L_meta_19992

open PEqualNP.Outside.L_meta_19992 PEqualNP.MetaComplexity in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19992 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16472541325419705030 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
