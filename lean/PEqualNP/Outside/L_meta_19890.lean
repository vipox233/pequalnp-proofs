import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19890
open PEqualNP.CircuitLowerBounds
def witness : Circuit := ⟨[⟨.or, [8, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [14, 18]⟩, ⟨.or, [11, 19]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [23, 16]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [8, 20]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [10, 19]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [30, 16]⟩, ⟨.and, [4, 31]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [13, 20]⟩, ⟨.and, [6, 35]⟩, ⟨.or, [14, 19]⟩, ⟨.and, [7, 37]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [39, 27]⟩, ⟨.or, [40, 29]⟩, ⟨.or, [41, 32]⟩, ⟨.or, [42, 34]⟩, ⟨.or, [43, 36]⟩, ⟨.or, [44, 38]⟩], 45⟩
end PEqualNP.Outside.L_meta_19890

open PEqualNP.Outside.L_meta_19890 in
theorem PEqualNP.Outside.L_meta_19890 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8280023251922031930 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
