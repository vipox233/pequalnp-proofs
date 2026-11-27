import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_24073

def circuit : Circuit := ⟨[⟨.and, [1, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_24073

open PEqualNP.Outside.L_meta_24073 in
theorem PEqualNP.Outside.L_meta_24073 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267167 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
