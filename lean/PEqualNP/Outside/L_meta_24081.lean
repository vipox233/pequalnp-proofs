import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24081_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [2, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_24081_aux

theorem PEqualNP.Outside.L_meta_24081 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279453 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24081_aux.wit, PEqualNP.Outside.L_meta_24081_aux.wit_p, by decide, by decide +kernel⟩
