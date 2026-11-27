import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22448_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (1881975 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [10, 7] },
      { op := GateOp.or, inputs := [11, 8] }, { op := GateOp.or, inputs := [8, 9] },
      { op := GateOp.and, inputs := [13, 0] }, { op := GateOp.or, inputs := [14, 1] },
      { op := GateOp.or, inputs := [15, 5] }, { op := GateOp.and, inputs := [16, 12] },
      { op := GateOp.or, inputs := [17, 2] }, { op := GateOp.or, inputs := [18, 6] },
      { op := GateOp.or, inputs := [16, 11] }, { op := GateOp.and, inputs := [20, 19] },
      { op := GateOp.or, inputs := [21, 4] }],
    output := 22 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_22448_aux

theorem PEqualNP.Outside.L_meta_22448 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881975 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22448_aux.upperC, PEqualNP.Outside.L_meta_22448_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_22448_aux.upper_rep⟩
