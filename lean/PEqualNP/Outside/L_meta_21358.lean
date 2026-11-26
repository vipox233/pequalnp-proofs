import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21358
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 2]⟩,
  ⟨.or, [0, 6]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [11, 10]⟩,
  ⟨.or, [11, 7]⟩,
  ⟨.and, [12, 14]⟩,
  ⟨.or, [15, 4]⟩,
  ⟨.or, [8, 3]⟩,
  ⟨.and, [13, 17]⟩,
  ⟨.or, [16, 18]⟩], 19⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21358

open PEqualNP.Outside.L_meta_21358 in
theorem PEqualNP.Outside.L_meta_21358 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241339 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
