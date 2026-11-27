import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22020

def circuit : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [8, 5]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22020

open PEqualNP.Outside.L_meta_22020 in
theorem PEqualNP.Outside.L_meta_22020 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33598 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
