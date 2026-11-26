import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20706

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 25 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.or, [15, 16]⟩], 17⟩

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

theorem small : circ.size ≤ 8 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 5 => (30510080 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20706

theorem PEqualNP.Outside.L_meta_20706 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (30510080 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  exact ⟨PEqualNP.Outside.L_meta_20706.circ, PEqualNP.Outside.L_meta_20706.fits, PEqualNP.Outside.L_meta_20706.small, PEqualNP.Outside.L_meta_20706.right⟩
