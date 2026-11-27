import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23639
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 10]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.or, [11, 5]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.or, [12, 7]⟩,
  ⟨.and, [13, 15]⟩,
  ⟨.or, [14, 9]⟩,
  ⟨.or, [17, 3]⟩,
  ⟨.and, [10, 18]⟩,
  ⟨.or, [16, 19]⟩], 20⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_23639

open PEqualNP.Outside.L_meta_23639 in
theorem PEqualNP.Outside.L_meta_23639 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (275262 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
