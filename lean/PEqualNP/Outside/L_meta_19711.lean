import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19711

def wit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [20, 10]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [20, 25]⟩, ⟨.and, [26, 2]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [28, 15]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [8, 29]⟩, ⟨.and, [31, 3]⟩, ⟨.and, [19, 0]⟩, ⟨.and, [4, 30]⟩, ⟨.or, [23, 28]⟩, ⟨.and, [35, 5]⟩, ⟨.or, [15, 18]⟩, ⟨.and, [37, 6]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [36, 24]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [27, 40]⟩, ⟨.or, [42, 38]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [33, 41]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 46]⟩], 47⟩

end PEqualNP.Outside.L_meta_19711

theorem PEqualNP.Outside.L_meta_19711 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17339788871490640935 : ℕ).testBit (8 * u.val + v.val)) 32) := by
  refine ⟨PEqualNP.Outside.L_meta_19711.wit, ?_, by decide, ?_⟩
  · simp [PEqualNP.Outside.L_meta_19711.wit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
