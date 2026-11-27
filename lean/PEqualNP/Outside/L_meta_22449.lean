import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22449

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 24 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [15, 7]⟩, ⟨GateOp.and, [14, 16]⟩, ⟨GateOp.or, [15, 6]⟩, ⟨GateOp.and, [3, 18]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [20, 17]⟩, ⟨GateOp.or, [21, 19]⟩], 22⟩

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

theorem small : circ.size ≤ 13 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (1882100 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22449

theorem PEqualNP.Outside.L_meta_22449 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1882100 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22449.circ, PEqualNP.Outside.L_meta_22449.fits, PEqualNP.Outside.L_meta_22449.small, PEqualNP.Outside.L_meta_22449.right⟩
