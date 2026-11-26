import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21445_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 2]⟩, ⟨GateOp.or, [7, 5]⟩], 8⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_21445_aux

theorem PEqualNP.Outside.L_meta_21445 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (553951 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21445_aux.wit, PEqualNP.Outside.L_meta_21445_aux.wit_mono, by decide, by decide +kernel⟩
