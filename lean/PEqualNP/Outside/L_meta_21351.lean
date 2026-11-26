import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_21351.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
def witness : Circuit := ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [3, 9]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [4, 10]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.and, [5, 14]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩], 19⟩
theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem correct : Represents (fun (u : Fin 4) (v : Fin 5) => (128958 : ℕ).testBit (5*u.val+v.val)) witness := by
  decide +kernel
end PEqualNP.Outside.L_meta_21351.Helpers


theorem PEqualNP.Outside.L_meta_21351 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (128958 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21351.Helpers.witness, PEqualNP.Outside.L_meta_21351.Helpers.mono, by decide, PEqualNP.Outside.L_meta_21351.Helpers.correct⟩
