import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25273_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25273_aux

theorem PEqualNP.Outside.L_meta_25273 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147609 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25273_aux.wit, PEqualNP.Outside.L_meta_25273_aux.wit_p, by decide, by decide +kernel⟩
