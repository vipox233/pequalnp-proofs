import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_20020

private def witness : Circuit :=
  ⟨[
    ⟨.or, [8, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.or, [9, 17]⟩,
    ⟨.or, [16, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [12, 13]⟩,
    ⟨.or, [21, 15]⟩, ⟨.or, [16, 22]⟩, ⟨.and, [1, 23]⟩,
    ⟨.or, [10, 14]⟩, ⟨.or, [25, 22]⟩, ⟨.and, [2, 26]⟩,
    ⟨.or, [10, 13]⟩, ⟨.or, [8, 28]⟩, ⟨.or, [29, 17]⟩,
    ⟨.and, [3, 30]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [11, 32]⟩,
    ⟨.or, [33, 25]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [28, 18]⟩,
    ⟨.and, [5, 36]⟩, ⟨.or, [32, 29]⟩, ⟨.and, [6, 38]⟩,
    ⟨.or, [33, 16]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [20, 24]⟩,
    ⟨.or, [42, 27]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 35]⟩,
    ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

private theorem witnessMonotone : Monotone2 witness := by
  simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_20020

open PEqualNP.Outside.L_meta_20020 in
theorem PEqualNP.Outside.L_meta_20020 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6572913902839198155 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  exact ⟨witness, witnessMonotone, by decide, by decide +kernel⟩
