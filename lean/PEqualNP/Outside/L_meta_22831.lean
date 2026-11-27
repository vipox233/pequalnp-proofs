import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22831_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [2, 9]⟩,
     ⟨.or, [4, 0]⟩,
     ⟨.or, [7, 1]⟩,
     ⟨.or, [11, 12]⟩,
     ⟨.or, [6, 13]⟩,
     ⟨.and, [10, 14]⟩,
     ⟨.or, [3, 12]⟩,
     ⟨.or, [5, 11]⟩,
     ⟨.and, [16, 17]⟩,
     ⟨.or, [18, 15]⟩,
     ⟨.or, [6, 8]⟩,
     ⟨.and, [20, 13]⟩,
     ⟨.or, [21, 19]⟩], 22⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22831_aux

theorem PEqualNP.Outside.L_meta_22831 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843260 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  exact ⟨PEqualNP.Outside.L_meta_22831_aux.circuit, PEqualNP.Outside.L_meta_22831_aux.mono, by decide, by decide +kernel⟩
