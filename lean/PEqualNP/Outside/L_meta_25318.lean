import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25318_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.not, [4]⟩, ⟨GateOp.and, [0, 6]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.and, [6, 12]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.and, [12, 14]⟩], 15⟩

theorem wit_p : FanInTwo wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_25318_aux

theorem PEqualNP.Outside.L_meta_25318 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165679 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25318_aux.wit, PEqualNP.Outside.L_meta_25318_aux.wit_p, by decide, by decide +kernel⟩
