import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22029_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 6 → Bool := fun (u : Fin 4) (v : Fin 6) => (815931 : ℕ).testBit (6 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 6] }, { op := GateOp.or, inputs := [10, 3] },
      { op := GateOp.or, inputs := [1, 4] }, { op := GateOp.or, inputs := [12, 5] },
      { op := GateOp.or, inputs := [13, 10] }, { op := GateOp.or, inputs := [13, 8] },
      { op := GateOp.or, inputs := [15, 9] }, { op := GateOp.and, inputs := [16, 11] },
      { op := GateOp.or, inputs := [17, 2] }, { op := GateOp.or, inputs := [18, 7] },
      { op := GateOp.and, inputs := [19, 14] }],
    output := 20 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_22029_aux

theorem PEqualNP.Outside.L_meta_22029 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815931 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_22029_aux.upperC, PEqualNP.Outside.L_meta_22029_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_22029_aux.upper_rep⟩
