import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21130_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (36284 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 4] }, { op := GateOp.or, inputs := [9, 1] },
      { op := GateOp.or, inputs := [10, 5] }, { op := GateOp.or, inputs := [1, 3] },
      { op := GateOp.or, inputs := [12, 8] }, { op := GateOp.and, inputs := [13, 9] },
      { op := GateOp.or, inputs := [14, 2] }, { op := GateOp.or, inputs := [15, 6] },
      { op := GateOp.or, inputs := [16, 7] }, { op := GateOp.and, inputs := [17, 11] }],
    output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_21130_aux

theorem PEqualNP.Outside.L_meta_21130 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36284 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21130_aux.upperC, PEqualNP.Outside.L_meta_21130_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_21130_aux.upper_rep⟩
