import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_22757.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
def witness : Circuit := ⟨[⟨.and, [0, 8]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [3, 12]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [4, 14]⟩,
    ⟨.and, [2, 15]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [11, 18]⟩,
    ⟨.and, [17, 19]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.or, [10, 22]⟩], 23⟩
theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem correct : Represents (fun (u : Fin 4) (v : Fin 6) => (1940414 : ℕ).testBit (6*u.val+v.val)) witness := by
  decide +kernel
end PEqualNP.Outside.L_meta_22757.Helpers


theorem PEqualNP.Outside.L_meta_22757 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940414 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22757.Helpers.witness, PEqualNP.Outside.L_meta_22757.Helpers.mono, by decide, PEqualNP.Outside.L_meta_22757.Helpers.correct⟩
