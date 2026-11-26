import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21104_aux

-- Credit: live-set search copied from the merged file L_meta_5469.lean (all-true case: L_meta_5475.lean), constants replaced by auto/fam_rep.py.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def A : Fin 4 → Fin 5 → Bool := fun (u : Fin 4) (v : Fin 5) => (34263 : ℕ).testBit (5 * u.val + v.val)

def upperC : Circuit :=
  { gates := [{ op := GateOp.or, inputs := [0, 2] }, { op := GateOp.or, inputs := [9, 3] },
      { op := GateOp.and, inputs := [10, 4] }, { op := GateOp.or, inputs := [5, 6] },
      { op := GateOp.or, inputs := [12, 7] }, { op := GateOp.and, inputs := [13, 1] },
      { op := GateOp.or, inputs := [14, 11] }, { op := GateOp.or, inputs := [12, 8] },
      { op := GateOp.and, inputs := [16, 0] }, { op := GateOp.or, inputs := [17, 15] }],
    output := 18 }

theorem upper_mono : Monotone2 upperC := by
  intro g hg
  simp only [upperC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem upper_rep : PEqualNP.Represents.Represents A upperC := by
  decide +kernel

end PEqualNP.Outside.L_meta_21104_aux

theorem PEqualNP.Outside.L_meta_21104 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (34263 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21104_aux.upperC, PEqualNP.Outside.L_meta_21104_aux.upper_mono, by decide, PEqualNP.Outside.L_meta_21104_aux.upper_rep⟩
