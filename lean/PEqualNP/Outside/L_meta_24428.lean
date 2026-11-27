import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24428_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.or, [10, 12]⟩
  ], 13⟩

def gateListOK (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) && Nat.ble g.inputs.length 2

theorem gateListOK_sound (C : Circuit) (h : gateListOK C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_24428_aux

open PEqualNP.Outside.L_meta_24428_aux in
theorem PEqualNP.Outside.L_meta_24428 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52534 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, gateListOK_sound witness (by decide +kernel), by decide, by decide +kernel⟩
