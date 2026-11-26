import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21126
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.or, [11, 7]⟩,
  ⟨.and, [10, 13]⟩,
  ⟨.or, [12, 8]⟩,
  ⟨.or, [15, 3]⟩,
  ⟨.and, [9, 16]⟩,
  ⟨.or, [14, 17]⟩], 18⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21126

open PEqualNP.Outside.L_meta_21126 in
theorem PEqualNP.Outside.L_meta_21126 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36246 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
