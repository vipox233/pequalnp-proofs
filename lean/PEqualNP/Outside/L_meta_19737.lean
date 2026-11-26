import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19737

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 64 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [16, 13]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.and, [0, 18]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [11, 20]⟩, ⟨GateOp.or, [13, 21]⟩, ⟨GateOp.and, [1, 22]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [24, 20]⟩, ⟨GateOp.and, [2, 25]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [9, 27]⟩, ⟨GateOp.or, [8, 28]⟩, ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [12, 31]⟩, ⟨GateOp.or, [10, 32]⟩, ⟨GateOp.and, [4, 33]⟩, ⟨GateOp.or, [14, 32]⟩, ⟨GateOp.and, [5, 35]⟩, ⟨GateOp.or, [24, 15]⟩, ⟨GateOp.or, [10, 37]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [10, 21]⟩, ⟨GateOp.and, [7, 40]⟩, ⟨GateOp.or, [19, 23]⟩, ⟨GateOp.or, [42, 26]⟩, ⟨GateOp.or, [43, 30]⟩, ⟨GateOp.or, [44, 34]⟩, ⟨GateOp.or, [45, 36]⟩, ⟨GateOp.or, [46, 39]⟩, ⟨GateOp.or, [47, 41]⟩], 48⟩

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

theorem small : circ.size ≤ 33 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_19737

theorem PEqualNP.Outside.L_meta_19737 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19737.circ, PEqualNP.Outside.L_meta_19737.fits, PEqualNP.Outside.L_meta_19737.small, PEqualNP.Outside.L_meta_19737.right⟩
