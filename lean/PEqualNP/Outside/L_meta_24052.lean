import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24052_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [5, 7]⟩, ⟨GateOp.and, [0, 1]⟩, ⟨GateOp.or, [2, 9]⟩, ⟨GateOp.and, [6, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [8, 12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24052_aux

theorem PEqualNP.Outside.L_meta_24052 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12617 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24052_aux.wit, PEqualNP.Outside.L_meta_24052_aux.wit_p, by decide, by decide +kernel⟩
