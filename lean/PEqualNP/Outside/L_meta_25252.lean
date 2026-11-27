import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25252_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [2, 9]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [10, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25252_aux

theorem PEqualNP.Outside.L_meta_25252 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50734 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25252_aux.wit, PEqualNP.Outside.L_meta_25252_aux.wit_p, by decide, by decide +kernel⟩
