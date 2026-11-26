import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21191
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [1, 4]⟩,
  ⟨.or, [2, 5]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [10, 7]⟩,
  ⟨.or, [6, 3]⟩,
  ⟨.and, [11, 13]⟩,
  ⟨.or, [0, 14]⟩,
  ⟨.or, [12, 8]⟩,
  ⟨.and, [9, 16]⟩,
  ⟨.or, [17, 15]⟩], 18⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21191

open PEqualNP.Outside.L_meta_21191 in
theorem PEqualNP.Outside.L_meta_21191 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104415 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
