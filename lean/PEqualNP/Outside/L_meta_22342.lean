import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22342

def circuit : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [12, 5]⟩, ⟨.not, [13]⟩, ⟨.and, [1, 14]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [17, 16]⟩], 18⟩

def legal (g : Gate) : Bool :=
  (match g.op with | .and | .or | .not => true | _ => false) && decide (g.inputs.length ≤ 2)

theorem legalCircuit : FanInTwo circuit := by
  have ok : circuit.gates.all legal = true := by decide +kernel
  intro g hg
  have h := List.all_eq_true.mp ok g hg
  cases e : g.op <;> simp [legal, e] at h ⊢ <;> first | assumption | simp_all

end PEqualNP.Outside.L_meta_22342

open PEqualNP.Outside.L_meta_22342 in
theorem PEqualNP.Outside.L_meta_22342 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33937 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨circuit, legalCircuit, by decide, by decide +kernel⟩
