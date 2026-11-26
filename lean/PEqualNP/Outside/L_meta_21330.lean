import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21330_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.or, [1, 4]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.or, [0, 14]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [2, 16]⟩,
    ⟨.and, [15, 17]⟩,
    ⟨.or, [13, 18]⟩
  ], 19⟩

theorem legal : Monotone2 witness := by simp [Monotone2, witness]
end PEqualNP.Outside.L_meta_21330_aux

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_21330 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105881 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_21330_aux.witness, PEqualNP.Outside.L_meta_21330_aux.legal, by decide, by decide +kernel⟩
