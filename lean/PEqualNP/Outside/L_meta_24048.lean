import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24048_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [5, 11]⟩, ⟨GateOp.or, [7, 12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24048_aux

theorem PEqualNP.Outside.L_meta_24048 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4956 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24048_aux.wit, PEqualNP.Outside.L_meta_24048_aux.wit_p, by decide, by decide +kernel⟩
