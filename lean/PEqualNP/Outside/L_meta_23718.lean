import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23718
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [1, 0]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [6, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.not, [8]⟩, ⟨.and, [5, 9]⟩], 10⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (221 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_23718

theorem PEqualNP.Outside.L_meta_23718 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (221 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_23718.checked
