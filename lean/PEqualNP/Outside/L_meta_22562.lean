import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22562_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (1948405 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 1] }, { op := GateOp.and, inputs := [10, 9] },
      { op := GateOp.or, inputs := [11, 4] }, { op := GateOp.or, inputs := [0, 5] },
      { op := GateOp.or, inputs := [13, 7] }, { op := GateOp.or, inputs := [2, 6] },
      { op := GateOp.or, inputs := [15, 13] }, { op := GateOp.or, inputs := [15, 1] },
      { op := GateOp.and, inputs := [17, 14] }, { op := GateOp.or, inputs := [18, 12] },
      { op := GateOp.or, inputs := [3, 8] }, { op := GateOp.and, inputs := [20, 16] },
      { op := GateOp.or, inputs := [21, 19] }],
    output := 22 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_22562_aux

theorem PEqualNP.Outside.L_meta_22562 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948405 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22562_aux.upperC, PEqualNP.Outside.L_meta_22562_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_22562_aux.upper_rep⟩
