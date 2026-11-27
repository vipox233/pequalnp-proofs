import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23158_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 3 → Fin 6 → Bool := fun (u : Fin 3) (v : Fin 6) => (64764 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 3] }, { op := GateOp.or, inputs := [9, 4] },
      { op := GateOp.or, inputs := [1, 5] }, { op := GateOp.or, inputs := [11, 6] },
      { op := GateOp.and, inputs := [12, 10] }, { op := GateOp.or, inputs := [13, 2] },
      { op := GateOp.or, inputs := [14, 7] }, { op := GateOp.or, inputs := [15, 8] },
      { op := GateOp.or, inputs := [12, 10] }, { op := GateOp.and, inputs := [17, 16] }],
    output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_23158_aux

theorem PEqualNP.Outside.L_meta_23158 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (64764 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_23158_aux.upperC, PEqualNP.Outside.L_meta_23158_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_23158_aux.upper_rep⟩
