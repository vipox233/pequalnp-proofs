import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19724_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def okGate : Gate → Bool
  | ⟨.and, l⟩ => decide (l.length ≤ 2)
  | ⟨.or, l⟩ => decide (l.length ≤ 2)
  | _ => false

theorem okGate_spec (g : Gate) (h : okGate g = true) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, l⟩
  cases op <;> simp_all [okGate]

def circ : Circuit := ⟨[⟨.or, [8, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [23, 16]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [26, 13]⟩, ⟨.or, [27, 15]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [32, 17]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [16, 18]⟩, ⟨.and, [5, 35]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [6, 37]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 29]⟩, ⟨.or, [42, 31]⟩, ⟨.or, [43, 34]⟩, ⟨.or, [44, 36]⟩, ⟨.or, [45, 38]⟩, ⟨.or, [46, 40]⟩], 47⟩

theorem circ_ok : circ.gates.all okGate = true := by decide

end PEqualNP.Outside.L_meta_19724_aux

open PEqualNP.Outside.L_meta_19724_aux in
theorem PEqualNP.Outside.L_meta_19724 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨circ, fun g hg => okGate_spec g (List.all_eq_true.mp circ_ok g hg), by decide, by decide +kernel⟩
