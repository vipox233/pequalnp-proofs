import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21276_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (39289 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.or, inputs := [9, 6] },
      { op := GateOp.and, inputs := [0, 8] }, { op := GateOp.or, inputs := [11, 2] },
      { op := GateOp.or, inputs := [12, 4] }, { op := GateOp.or, inputs := [13, 1] },
      { op := GateOp.or, inputs := [13, 7] }, { op := GateOp.and, inputs := [15, 10] },
      { op := GateOp.or, inputs := [3, 5] }, { op := GateOp.and, inputs := [17, 14] },
      { op := GateOp.or, inputs := [18, 16] }],
    output := 19 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_21276_aux

theorem PEqualNP.Outside.L_meta_21276 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39289 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_21276_aux.upperC, PEqualNP.Outside.L_meta_21276_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_21276_aux.upper_rep⟩
