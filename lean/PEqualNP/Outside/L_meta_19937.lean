import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_19937.Helpers
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
def witness : Circuit := ⟨[⟨.or, [8, 13]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [19, 13]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.and, [1, 22]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [24, 11]⟩,
    ⟨.and, [2, 25]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.and, [3, 27]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.or, [9, 17]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.and, [7, 35]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [37, 26]⟩,
    ⟨.or, [38, 28]⟩,
    ⟨.or, [39, 30]⟩,
    ⟨.or, [40, 32]⟩,
    ⟨.or, [41, 34]⟩,
    ⟨.or, [42, 36]⟩], 43⟩
theorem mono : PEqualNP.MetaComplexity.Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
theorem correct : Represents (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8*u.val+v.val)) witness := by
  decide +kernel
end PEqualNP.Outside.L_meta_19937.Helpers


theorem PEqualNP.Outside.L_meta_19937 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10691974706225816370 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨PEqualNP.Outside.L_meta_19937.Helpers.witness, PEqualNP.Outside.L_meta_19937.Helpers.mono, by decide, PEqualNP.Outside.L_meta_19937.Helpers.correct⟩
