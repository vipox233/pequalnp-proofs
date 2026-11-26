import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21161

def C : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 4]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [7, 13]⟩,
    ⟨.and, [10, 14]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.and, [12, 16]⟩,
    ⟨.or, [15, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_21161

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_21161 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40414 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  refine ⟨PEqualNP.Outside.L_meta_21161.C, ?_, ?_, ?_⟩
  · simp [PEqualNP.Outside.L_meta_21161.C, PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
