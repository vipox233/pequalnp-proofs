import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20021

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first eight gates pair row i with column p(i), where
-- p = [0, 1, 7, 3, 2, 5, 6, 4]. The paired matrix is symmetric.
-- In these coordinates gates 24–26 cover the four edges between
-- {2,4} and {3,5}, and gates 27–29 cover the triangle on {0,6,7}.
-- The remaining terms cover the two loops, the two edges from 1 to
-- {3,4}, and the two edges joining these groups.
def witness : Circuit :=
  ⟨[⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.or, [2, 15]⟩, ⟨GateOp.or, [3, 11]⟩,
    ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.or, [5, 13]⟩,
    ⟨GateOp.or, [6, 14]⟩, ⟨GateOp.or, [7, 12]⟩,
    ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.or, [19, 21]⟩,
    ⟨GateOp.and, [24, 25]⟩,
    ⟨GateOp.or, [22, 23]⟩, ⟨GateOp.and, [16, 27]⟩,
    ⟨GateOp.and, [22, 23]⟩, ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [19, 20]⟩, ⟨GateOp.and, [17, 31]⟩,
    ⟨GateOp.and, [23, 17]⟩, ⟨GateOp.and, [22, 18]⟩,
    ⟨GateOp.and, [5, 13]⟩,
    ⟨GateOp.or, [26, 28]⟩, ⟨GateOp.or, [29, 30]⟩,
    ⟨GateOp.or, [32, 33]⟩, ⟨GateOp.or, [34, 35]⟩,
    ⟨GateOp.or, [36, 37]⟩, ⟨GateOp.or, [38, 39]⟩,
    ⟨GateOp.or, [40, 41]⟩], 42⟩

theorem witness_mono : Monotone2 witness := by
  simp [Monotone2, witness]

end PEqualNP.Outside.L_meta_20021

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_20021 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4868853174714768465 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨L_meta_20021.witness, L_meta_20021.witness_mono, by decide, ?_⟩
  decide
