import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22397_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [2, 3]⟩,
     ⟨.or, [1, 10]⟩,
     ⟨.and, [5, 11]⟩,
     ⟨.or, [0, 2]⟩,
     ⟨.or, [6, 7]⟩,
     ⟨.and, [13, 14]⟩,
     ⟨.or, [12, 15]⟩,
     ⟨.or, [0, 1]⟩,
     ⟨.or, [8, 9]⟩,
     ⟨.or, [6, 18]⟩,
     ⟨.and, [17, 19]⟩,
     ⟨.or, [4, 20]⟩,
     ⟨.or, [21, 16]⟩], 22⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22397_aux

theorem PEqualNP.Outside.L_meta_22397 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851453 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22397_aux.circuit, PEqualNP.Outside.L_meta_22397_aux.mono, by decide, by decide +kernel⟩
