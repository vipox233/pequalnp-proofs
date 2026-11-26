import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20540_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 5 → Bool := fun (u : Fin 3) (v : Fin 5) => (16123 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 5] }, { op := GateOp.or, inputs := [1, 6] },
      { op := GateOp.and, inputs := [9, 8] }, { op := GateOp.or, inputs := [10, 2] },
      { op := GateOp.or, inputs := [11, 7] }, { op := GateOp.or, inputs := [9, 8] },
      { op := GateOp.and, inputs := [13, 12] }, { op := GateOp.or, inputs := [14, 3] },
      { op := GateOp.or, inputs := [15, 4] }],
    output := 16 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_20540_aux

theorem PEqualNP.Outside.L_meta_20540 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (16123 : ℕ).testBit (5 * u.val + v.val)) 9 := by
  exact ⟨PEqualNP.Outside.L_meta_20540_aux.upperC, PEqualNP.Outside.L_meta_20540_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_20540_aux.upper_rep⟩
