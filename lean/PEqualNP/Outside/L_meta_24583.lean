import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C_ : Circuit := ⟨[⟨.not, [5]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [2, 0]⟩, ⟨.and, [2, 1]⟩, ⟨.not, [9]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [12, 10]⟩], 13⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem wf_ (C : Circuit) (h : okB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

end PEqualNP.Outside.L_meta_24583_aux

theorem PEqualNP.Outside.L_meta_24583 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6540991 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24583_aux.C_,
   PEqualNP.Outside.L_meta_24583_aux.wf_ PEqualNP.Outside.L_meta_24583_aux.C_ (by decide +kernel),
   by decide, by decide +kernel⟩
