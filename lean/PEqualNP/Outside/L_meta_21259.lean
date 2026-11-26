import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21259
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [1, 9]⟩,
  ⟨.or, [10, 8]⟩,
  ⟨.or, [9, 5]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.and, [13, 12]⟩,
  ⟨.or, [14, 7]⟩,
  ⟨.or, [16, 3]⟩,
  ⟨.and, [11, 17]⟩,
  ⟨.or, [15, 18]⟩], 19⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21259

open PEqualNP.Outside.L_meta_21259 in
theorem PEqualNP.Outside.L_meta_21259 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36350 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
