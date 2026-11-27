import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24116 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266320 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or,[0,4]⟩,⟨.and,[0,4]⟩,⟨.or,[1,2]⟩,⟨.and,[1,2]⟩,⟨.and,[7,3]⟩,⟨.or,[8,9]⟩,⟨.or,[5,10]⟩,⟨.not,[11]⟩,⟨.or,[6,12]⟩],13⟩
  refine ⟨circuit,?_,by decide +kernel,by decide +kernel⟩
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
