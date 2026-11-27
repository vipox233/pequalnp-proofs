import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22349

def circuit : Circuit := ⟨[⟨.not, [0]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [11]⟩, ⟨.and, [3, 12]⟩, ⟨.and, [2, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 14]⟩, ⟨.not, [18]⟩], 19⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22349

open PEqualNP.Outside.L_meta_22349 in
theorem PEqualNP.Outside.L_meta_22349 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17048 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
