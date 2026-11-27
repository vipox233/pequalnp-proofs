import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24682_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[
    ⟨.or, [1, 3]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [7, 8]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.and, [9, 11]⟩,
    ⟨.not, [12]⟩], 13⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24682_aux

set_option maxRecDepth 4000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_24682 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630388663 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24682_aux.circuit, PEqualNP.Outside.L_meta_24682_aux.fanin, by decide, by decide +kernel⟩
