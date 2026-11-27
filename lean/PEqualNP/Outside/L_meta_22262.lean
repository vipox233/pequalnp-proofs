import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22262

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 11]⟩,
    ⟨.or, [1, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [13, 14]⟩,
    ⟨.or, [12, 15]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [8, 9]⟩,
    ⟨.or, [17, 18]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [16, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_22262

open PEqualNP.Outside.L_meta_22262 in
theorem PEqualNP.Outside.L_meta_22262 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (836597 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]

