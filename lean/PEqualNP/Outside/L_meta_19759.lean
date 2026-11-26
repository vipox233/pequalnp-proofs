import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_19759

def witness : Circuit :=
  ⟨[
    ⟨.or, [8, 15]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [11, 20]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [22, 16]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.or, [28, 17]⟩,
    ⟨.or, [9, 21]⟩,
    ⟨.or, [9, 24]⟩,
    ⟨.or, [11, 25]⟩,
    ⟨.or, [32, 15]⟩,
    ⟨.or, [23, 19]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.and, [0, 27]⟩,
    ⟨.and, [1, 31]⟩,
    ⟨.and, [2, 33]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.and, [4, 26]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.and, [6, 29]⟩,
    ⟨.and, [7, 34]⟩,
    ⟨.or, [43, 42]⟩,
    ⟨.or, [44, 41]⟩,
    ⟨.or, [45, 40]⟩,
    ⟨.or, [46, 39]⟩,
    ⟨.or, [47, 38]⟩,
    ⟨.or, [48, 37]⟩,
    ⟨.or, [49, 36]⟩
  ], 50⟩

end PEqualNP.Outside.L_meta_19759

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_19759 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12498470449173941205 : ℕ).testBit (8 * u.val + v.val)) 35 := by
  let C := PEqualNP.Outside.L_meta_19759.witness
  have strict : PEqualNP.TopForm.IsAO2 16 C := by decide +kernel
  refine ⟨C, ?_, by decide +kernel, by decide +kernel⟩
  intro g hg
  exact ⟨by simpa using strict.1 g hg, (strict.2.2 g hg).le⟩
