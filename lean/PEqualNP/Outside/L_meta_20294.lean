import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20294

def witness : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [7, 14]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.or, [15, 19]⟩,
    ⟨.or, [16, 22]⟩,
    ⟨.or, [0, 26]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [3, 23]⟩,
    ⟨.or, [0, 21]⟩,
    ⟨.or, [20, 27]⟩,
    ⟨.and, [28, 20]⟩,
    ⟨.and, [25, 32]⟩,
    ⟨.and, [24, 31]⟩,
    ⟨.and, [30, 29]⟩,
    ⟨.or, [33, 34]⟩,
    ⟨.or, [37, 35]⟩,
    ⟨.or, [38, 36]⟩], 39⟩

theorem basis : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20294

theorem PEqualNP.Outside.L_meta_20294 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 24) := by
  exact ⟨PEqualNP.Outside.L_meta_20294.witness, PEqualNP.Outside.L_meta_20294.basis,
    by decide, by decide +kernel⟩
