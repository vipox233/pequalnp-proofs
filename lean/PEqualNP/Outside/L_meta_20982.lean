import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20982

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 20 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [1, 10]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

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

theorem small : circ.size ≤ 7 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (34295 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20982

theorem PEqualNP.Outside.L_meta_20982 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (34295 : ℕ).testBit (5 * u.val + v.val)) 7 := by
  exact ⟨PEqualNP.Outside.L_meta_20982.circ, PEqualNP.Outside.L_meta_20982.fits, PEqualNP.Outside.L_meta_20982.small, PEqualNP.Outside.L_meta_20982.right⟩
