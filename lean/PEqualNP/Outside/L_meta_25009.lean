import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[
  ⟨.or, [11, 5]⟩,
  ⟨.or, [12, 1]⟩,
  ⟨.or, [16, 17]⟩,
  ⟨.or, [0, 8]⟩,
  ⟨.or, [18, 19]⟩,
  ⟨.or, [13, 2]⟩,
  ⟨.or, [4, 14]⟩,
  ⟨.or, [21, 22]⟩,
  ⟨.and, [20, 23]⟩,
  ⟨.or, [15, 2]⟩,
  ⟨.or, [7, 13]⟩,
  ⟨.and, [25, 26]⟩,
  ⟨.or, [21, 17]⟩,
  ⟨.or, [15, 7]⟩,
  ⟨.and, [28, 29]⟩,
  ⟨.or, [3, 10]⟩,
  ⟨.or, [6, 9]⟩,
  ⟨.or, [31, 32]⟩,
  ⟨.or, [29, 22]⟩,
  ⟨.or, [16, 34]⟩,
  ⟨.and, [33, 35]⟩,
  ⟨.or, [30, 36]⟩,
  ⟨.or, [27, 37]⟩,
  ⟨.or, [24, 38]⟩,
  ⟨.or, [31, 18]⟩,
  ⟨.or, [19, 32]⟩,
  ⟨.and, [40, 41]⟩,
  ⟨.or, [39, 42]⟩], 43⟩

lemma mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25009

open PEqualNP.Outside.L_meta_25009 in
theorem PEqualNP.Outside.L_meta_25009 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨witness, mono, by decide, by decide +kernel⟩
