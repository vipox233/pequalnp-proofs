import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_21189

def witness : Circuit :=
  ⟨[⟨.or, [3, 8]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [3, 10]⟩,
    ⟨.or, [2, 5]⟩, ⟨.or, [6, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [14, 15]⟩, ⟨.or, [16, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_21189

open PEqualNP.Outside.L_meta_21189 in
theorem PEqualNP.Outside.L_meta_21189 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104218 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨witness, by simp [PEqualNP.MetaComplexity.Monotone2, witness], by decide, by decide +kernel⟩
