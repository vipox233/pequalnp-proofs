import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22352

def circuit : Circuit := ⟨[⟨.not, [1]⟩, ⟨.and, [3, 6]⟩, ⟨.not, [0]⟩, ⟨.and, [4, 8]⟩, ⟨.not, [0]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 12]⟩, ⟨.and, [1, 0]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [15, 11]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [17, 14]⟩, ⟨.not, [18]⟩], 19⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22352

open PEqualNP.Outside.L_meta_22352 in
theorem PEqualNP.Outside.L_meta_22352 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17073 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
