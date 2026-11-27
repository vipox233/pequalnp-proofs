import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_22713.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
def witness : Circuit := ⟨[⟨.or, [2, 3]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.and, [5, 12]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.and, [18, 19]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.or, [11, 22]⟩], 23⟩
theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem correct : Represents (fun (u : Fin 4) (v : Fin 6) => (908220 : ℕ).testBit (6*u.val+v.val)) witness := by
  decide +kernel
end PEqualNP.Outside.L_meta_22713.Helpers


theorem PEqualNP.Outside.L_meta_22713 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908220 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22713.Helpers.witness, PEqualNP.Outside.L_meta_22713.Helpers.mono, by decide, PEqualNP.Outside.L_meta_22713.Helpers.correct⟩
