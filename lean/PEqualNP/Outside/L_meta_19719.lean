import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19719

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 64 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.and, [0, 17]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [9, 19]⟩, ⟨GateOp.and, [1, 20]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [2, 22]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [8, 24]⟩, ⟨GateOp.and, [3, 25]⟩, ⟨GateOp.or, [10, 19]⟩, ⟨GateOp.and, [4, 27]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [29, 12]⟩, ⟨GateOp.and, [5, 30]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [13, 32]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [29, 15]⟩, ⟨GateOp.and, [7, 35]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.or, [37, 23]⟩, ⟨GateOp.or, [38, 26]⟩, ⟨GateOp.or, [39, 28]⟩, ⟨GateOp.or, [40, 31]⟩, ⟨GateOp.or, [41, 34]⟩, ⟨GateOp.or, [42, 36]⟩], 43⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def shapeB (C : Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : Circuit} (h : shapeB C = true) : Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem fits : Monotone2 circ := shapeB_sound (by decide)

theorem small : circ.size ≤ 28 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19719

theorem PEqualNP.Outside.L_meta_19719 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_19719.circ, PEqualNP.Outside.L_meta_19719.fits, PEqualNP.Outside.L_meta_19719.small, PEqualNP.Outside.L_meta_19719.right⟩
