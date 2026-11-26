import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19713

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [10, 15]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [16, 17]⟩, ⟨.and, [20, 0]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [9, 22]⟩, ⟨.or, [11, 8]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [15, 23]⟩, ⟨.or, [18, 27]⟩, ⟨.and, [2, 25]⟩, ⟨.and, [6, 26]⟩, ⟨.or, [27, 11]⟩, ⟨.or, [19, 12]⟩, ⟨.or, [32, 15]⟩, ⟨.and, [28, 4]⟩, ⟨.and, [5, 29]⟩, ⟨.and, [3, 34]⟩, ⟨.or, [21, 31]⟩, ⟨.or, [37, 35]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [32, 24]⟩, ⟨.or, [36, 40]⟩, ⟨.and, [7, 41]⟩, ⟨.and, [33, 1]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [43, 45]⟩, ⟨.or, [42, 46]⟩], 47⟩

end PEqualNP.Outside.L_meta_19713

theorem PEqualNP.Outside.L_meta_19713 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5420442459739364580 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  refine ⟨PEqualNP.Outside.L_meta_19713.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19713.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
