import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24555
open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.not, [4]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.not, [5]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.or, [11, 12]⟩], 13⟩

private theorem gate_types : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_24555

open PEqualNP.Outside.L_meta_24555 in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_24555 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4310959 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨circuit, gate_types, by decide, by decide +kernel⟩
