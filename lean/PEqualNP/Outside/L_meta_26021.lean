import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26021_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  { gates :=
      [ { op := GateOp.not, inputs := [3] }
      , { op := GateOp.or, inputs := [4, 5] }
      , { op := GateOp.or, inputs := [8, 9] } ]
    output := 10 }

end PEqualNP.Outside.L_meta_26021_aux

theorem PEqualNP.Outside.L_meta_26021 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 15, 15, 3] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨PEqualNP.Outside.L_meta_26021_aux.witness, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_26021_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp
