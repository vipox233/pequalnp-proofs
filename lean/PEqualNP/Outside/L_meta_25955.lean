import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25955
open PEqualNP.CircuitLowerBounds

-- Wire 4 selects column zero. Rows 1 and 2 use that column, and row 0 uses its complement.
private def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.not, [4]⟩,
    ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_25955

theorem PEqualNP.Outside.L_meta_25955 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 1, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨PEqualNP.Outside.L_meta_25955.witness, ?_, by decide, by decide, ?_⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_25955.witness] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
