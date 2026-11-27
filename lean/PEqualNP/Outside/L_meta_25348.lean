import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25348_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [1, 2]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.not, [12]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [9, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25348_aux

theorem PEqualNP.Outside.L_meta_25348 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2197151 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25348_aux.wit, PEqualNP.Outside.L_meta_25348_aux.wit_p, by decide, by decide +kernel⟩
