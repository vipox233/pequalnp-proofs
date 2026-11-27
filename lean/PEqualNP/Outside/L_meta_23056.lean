import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23056

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.or, [5, 16]⟩, ⟨GateOp.or, [17, 8]⟩, ⟨GateOp.and, [2, 18]⟩, ⟨GateOp.or, [17, 7]⟩, ⟨GateOp.and, [3, 20]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [22, 19]⟩, ⟨GateOp.or, [23, 21]⟩], 24⟩

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

theorem small : circ.size ≤ 16 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (4030074 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_23056

theorem PEqualNP.Outside.L_meta_23056 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030074 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  exact ⟨PEqualNP.Outside.L_meta_23056.circ, PEqualNP.Outside.L_meta_23056.fits, PEqualNP.Outside.L_meta_23056.small, PEqualNP.Outside.L_meta_23056.right⟩
