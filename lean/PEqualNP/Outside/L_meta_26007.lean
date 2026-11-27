import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26007_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  { gates :=
      [ { op := GateOp.or, inputs := [0, 1] }
      , { op := GateOp.or, inputs := [4, 5] }
      , { op := GateOp.or, inputs := [8, 9] }
      , { op := GateOp.and, inputs := [8, 9] }
      , { op := GateOp.not, inputs := [11] }
      , { op := GateOp.and, inputs := [10, 12] } ]
    output := 13 }

end PEqualNP.Outside.L_meta_26007_aux

theorem PEqualNP.Outside.L_meta_26007 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([12, 12, 3, 3] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨PEqualNP.Outside.L_meta_26007_aux.witness, ?_, by decide, by decide, by decide⟩
  intro g hg
  simp only [PEqualNP.Outside.L_meta_26007_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
