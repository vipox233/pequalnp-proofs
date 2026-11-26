import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19768_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def okGate : Gate → Bool
  | ⟨.and, l⟩ => decide (l.length ≤ 2)
  | ⟨.or, l⟩ => decide (l.length ≤ 2)
  | _ => false

theorem okGate_spec (g : Gate) (h : okGate g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, l⟩
  cases op <;> simp_all [okGate]

def circ : Circuit := ⟨[⟨.or, [8, 10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [2, 27]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [29, 19]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [32, 19]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [35, 18]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [40, 20]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [43, 28]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem circ_ok : circ.gates.all okGate = true := by decide

end PEqualNP.Outside.L_meta_19768_aux

open PEqualNP.Outside.L_meta_19768_aux in
theorem PEqualNP.Outside.L_meta_19768 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5748802764708593400 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨circ, fun g hg => okGate_spec g (List.all_eq_true.mp circ_ok g hg), by decide, by decide +kernel⟩
