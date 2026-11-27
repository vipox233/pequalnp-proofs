import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25271_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [3, 7]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [1, 9]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [13, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25271_aux

theorem PEqualNP.Outside.L_meta_25271 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147511 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25271_aux.wit, PEqualNP.Outside.L_meta_25271_aux.wit_p, by decide, by decide +kernel⟩
