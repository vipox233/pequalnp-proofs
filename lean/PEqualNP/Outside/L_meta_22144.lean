import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22144
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Wire 6 (x₂ ∨ x₅) is shared between the two acceptance branches.
def net : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [7, 3]⟩, ⟨.not, [8]⟩,
    ⟨.and, [1, 9]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [10, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩

theorem basis : FanInTwo net := by
  intro g hg
  simp only [net, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with e | e | e | e | e | e | e | e | e | e <;> subst g <;> simp

theorem agrees : ∀ i j : Fin 6, net.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33972 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22144

theorem PEqualNP.Outside.L_meta_22144 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33972 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  open PEqualNP.Outside.L_meta_22144 in
  exact ⟨net, basis, by decide, agrees⟩
