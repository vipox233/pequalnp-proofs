import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25298_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [4, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [0, 8]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [9, 13]⟩, ⟨GateOp.not, [14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25298_aux

theorem PEqualNP.Outside.L_meta_25298 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2164031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25298_aux.wit, PEqualNP.Outside.L_meta_25298_aux.wit_p, by decide, by decide +kernel⟩
