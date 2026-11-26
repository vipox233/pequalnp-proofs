import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_20301

def witness : Circuit := ⟨[
  ⟨.or, [9, 0]⟩,
  ⟨.or, [13, 10]⟩,
  ⟨.or, [6, 11]⟩,
  ⟨.and, [17, 3]⟩,
  ⟨.or, [6, 1]⟩,
  ⟨.or, [13, 4]⟩,
  ⟨.or, [20, 5]⟩,
  ⟨.or, [8, 7]⟩,
  ⟨.or, [19, 16]⟩,
  ⟨.or, [12, 11]⟩,
  ⟨.or, [25, 15]⟩,
  ⟨.or, [24, 23]⟩,
  ⟨.and, [22, 26]⟩,
  ⟨.or, [14, 21]⟩,
  ⟨.or, [23, 15]⟩,
  ⟨.or, [29, 1]⟩,
  ⟨.or, [31, 3]⟩,
  ⟨.or, [16, 12]⟩,
  ⟨.or, [29, 33]⟩,
  ⟨.or, [10, 2]⟩,
  ⟨.or, [35, 14]⟩,
  ⟨.or, [27, 18]⟩,
  ⟨.or, [35, 30]⟩,
  ⟨.and, [32, 37]⟩,
  ⟨.or, [28, 39]⟩,
  ⟨.or, [23, 5]⟩,
  ⟨.and, [41, 36]⟩,
  ⟨.and, [38, 34]⟩,
  ⟨.or, [40, 43]⟩,
  ⟨.or, [44, 42]⟩], 45⟩

end PEqualNP.Outside.L_meta_20301

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_20301 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8572844398234278885 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let C := PEqualNP.Outside.L_meta_20301.witness
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp [C, PEqualNP.Outside.L_meta_20301.witness] at hg
    rcases hg with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> decide
  · decide +kernel
