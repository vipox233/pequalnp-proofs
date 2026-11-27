import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24826_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C_ : Circuit := ⟨[⟨.or, [5, 4]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [9, 0]⟩, ⟨.and, [1, 4]⟩, ⟨.not, [10]⟩, ⟨.or, [11, 13]⟩], 14⟩

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

end PEqualNP.Outside.L_meta_24826_aux

theorem PEqualNP.Outside.L_meta_24826 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149439 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24826_aux.C_,
   PEqualNP.Outside.L_meta_24826_aux.wf_ PEqualNP.Outside.L_meta_24826_aux.C_ (by decide +kernel),
   by decide, by decide +kernel⟩
