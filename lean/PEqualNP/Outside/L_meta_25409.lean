import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25409

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def C : Circuit :=
  { gates := [
      { op := GateOp.or, inputs := [3, 2] },
      { op := GateOp.and, inputs := [2, 4] },
      { op := GateOp.or, inputs := [5, 1] },
      { op := GateOp.or, inputs := [0, 8] },
      { op := GateOp.or, inputs := [1, 6] },
      { op := GateOp.and, inputs := [3, 9] },
      { op := GateOp.or, inputs := [7, 11] },
      { op := GateOp.not, inputs := [12] },
      { op := GateOp.or, inputs := [10, 0] },
      { op := GateOp.and, inputs := [13, 14] }
    ], output := 15 }

private theorem C_fan : FanInTwo C := by
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem C_size : C.size ≤ 10 := by
  decide

private theorem C_rep :
    ∀ i j : Fin 6,
      C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (6475191 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_25409

theorem PEqualNP.Outside.L_meta_25409 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
        ∀ i j : Fin 6,
          C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
            (6475191 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25409.C,
   PEqualNP.Outside.L_meta_25409.C_fan,
   PEqualNP.Outside.L_meta_25409.C_size,
   PEqualNP.Outside.L_meta_25409.C_rep⟩
