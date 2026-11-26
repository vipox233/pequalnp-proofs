import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21355
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.and, [0, 8]⟩,
  ⟨.or, [9, 1]⟩,
  ⟨.or, [10, 5]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.or, [0, 12]⟩,
  ⟨.or, [11, 12]⟩,
  ⟨.and, [11, 13]⟩,
  ⟨.or, [15, 4]⟩,
  ⟨.or, [7, 3]⟩,
  ⟨.and, [14, 17]⟩,
  ⟨.or, [16, 18]⟩], 19⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21355

open PEqualNP.Outside.L_meta_21355 in
theorem PEqualNP.Outside.L_meta_21355 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241075 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
