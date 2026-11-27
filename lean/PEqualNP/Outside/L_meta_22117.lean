import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22117

def circuit : Circuit := ⟨[⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [9, 5]⟩, ⟨.not, [10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [15, 14]⟩], 16⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22117

open PEqualNP.Outside.L_meta_22117 in
theorem PEqualNP.Outside.L_meta_22117 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18235 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
