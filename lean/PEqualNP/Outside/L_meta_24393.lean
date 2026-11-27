import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_24393

def circuit : Circuit := ⟨[⟨.and, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.not, [11]⟩], 12⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_24393

open PEqualNP.Outside.L_meta_24393 in
theorem PEqualNP.Outside.L_meta_24393 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34634582191 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
