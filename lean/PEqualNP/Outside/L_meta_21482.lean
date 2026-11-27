import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21482
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def net : Circuit := ⟨[⟨.or, [1, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩], 8⟩

theorem basis : FanInTwo net := by
  intro g hg
  simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with e | e | e | e <;> subst g <;> simp

theorem agrees : ∀ i j : Fin 5, net.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (138 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21482

theorem PEqualNP.Outside.L_meta_21482 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (138 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  open PEqualNP.Outside.L_meta_21482 in
  exact ⟨net, basis, by decide, agrees⟩
