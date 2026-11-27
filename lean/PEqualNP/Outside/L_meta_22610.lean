import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22610
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[
  ⟨.or,[0,6]⟩,
  ⟨.or,[1,10]⟩,
  ⟨.or,[7,9]⟩,
  ⟨.or,[2,12]⟩,
  ⟨.and,[11,13]⟩,
  ⟨.or,[7,10]⟩,
  ⟨.or,[2,15]⟩,
  ⟨.or,[3,8]⟩,
  ⟨.or,[1,17]⟩,
  ⟨.and,[16,18]⟩,
  ⟨.or,[14,19]⟩,
  ⟨.or,[4,5]⟩,
  ⟨.or,[20,21]⟩],22⟩

theorem legal : Monotone2 circuit := by
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

end PEqualNP.Outside.L_meta_22610

theorem PEqualNP.Outside.L_meta_22610 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4029435 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22610.circuit,PEqualNP.Outside.L_meta_22610.legal,by decide,by decide +kernel⟩
