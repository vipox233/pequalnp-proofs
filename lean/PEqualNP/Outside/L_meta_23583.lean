import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23583
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.and, [3, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [6, 12]⟩], 13⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33712 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_23583

theorem PEqualNP.Outside.L_meta_23583 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33712 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := PEqualNP.Outside.L_meta_23583.checked
