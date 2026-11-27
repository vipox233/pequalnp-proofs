import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23684
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.or, [2, 7]⟩,
  ⟨.or, [10, 5]⟩,
  ⟨.or, [13, 11]⟩,
  ⟨.or, [12, 8]⟩,
  ⟨.and, [14, 15]⟩,
  ⟨.or, [9, 3]⟩,
  ⟨.and, [13, 17]⟩,
  ⟨.or, [16, 18]⟩], 19⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23684

open PEqualNP.Outside.L_meta_23684 in
theorem PEqualNP.Outside.L_meta_23684 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816696 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
