import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24231

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [0, 5]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [6, 9]⟩,
    ⟨.not, [10]⟩], 11⟩

lemma fanIn : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24231

theorem PEqualNP.Outside.L_meta_24231 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34634581921 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_24231.circuit, PEqualNP.Outside.L_meta_24231.fanIn, by decide, by decide +kernel⟩
