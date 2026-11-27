import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23025

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 21 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

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

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34612 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23025

theorem PEqualNP.Outside.L_meta_23025 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34612 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23025.circ, PEqualNP.Outside.L_meta_23025.fits, PEqualNP.Outside.L_meta_23025.small, PEqualNP.Outside.L_meta_23025.right⟩
