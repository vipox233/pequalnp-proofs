import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23156_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 6 → Bool := fun (u : Fin 3) (v : Fin 6) => (62969 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [9, 5] },
      { op := GateOp.or, inputs := [1, 6] }, { op := GateOp.or, inputs := [11, 10] },
      { op := GateOp.or, inputs := [11, 8] }, { op := GateOp.and, inputs := [13, 10] },
      { op := GateOp.or, inputs := [14, 2] }, { op := GateOp.or, inputs := [15, 7] },
      { op := GateOp.and, inputs := [16, 12] }, { op := GateOp.or, inputs := [17, 3] }],
    output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_23156_aux

theorem PEqualNP.Outside.L_meta_23156 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (62969 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_23156_aux.upperC, PEqualNP.Outside.L_meta_23156_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_23156_aux.upper_rep⟩
