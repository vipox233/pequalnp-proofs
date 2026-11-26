import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22167_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (841195 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 6] }, { op := GateOp.or, inputs := [10, 3] },
      { op := GateOp.or, inputs := [10, 8] }, { op := GateOp.or, inputs := [1, 7] },
      { op := GateOp.or, inputs := [13, 11] }, { op := GateOp.or, inputs := [13, 9] },
      { op := GateOp.and, inputs := [15, 12] }, { op := GateOp.or, inputs := [16, 2] },
      { op := GateOp.or, inputs := [17, 5] }, { op := GateOp.and, inputs := [18, 14] },
      { op := GateOp.or, inputs := [19, 4] }],
    output := 20 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_22167_aux

theorem PEqualNP.Outside.L_meta_22167 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841195 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_22167_aux.upperC, PEqualNP.Outside.L_meta_22167_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_22167_aux.upper_rep⟩
