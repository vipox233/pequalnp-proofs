import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22435

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := { gates := [⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [10, 4]⟩, ⟨GateOp.and, [2, 16]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.and, [3, 18]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [20, 17]⟩, ⟨GateOp.or, [21, 19]⟩], output := 22 }

theorem mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
  simp [PEqualNP.MetaComplexity.Monotone2, C0]

end PEqualNP.Outside.L_meta_22435

theorem PEqualNP.Outside.L_meta_22435 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881450 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22435.C0, PEqualNP.Outside.L_meta_22435.mono, by decide, by decide⟩
