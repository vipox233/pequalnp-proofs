import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22245
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[
  ⟨.or,[7,8]⟩,
  ⟨.or,[10,9]⟩,
  ⟨.or,[4,0]⟩,
  ⟨.or,[5,1]⟩,
  ⟨.and,[6,2]⟩,
  ⟨.or,[13,12]⟩,
  ⟨.or,[13,6]⟩,
  ⟨.or,[2,16]⟩,
  ⟨.and,[12,17]⟩,
  ⟨.or,[11,18]⟩,
  ⟨.or,[3,19]⟩,
  ⟨.and,[15,20]⟩,
  ⟨.or,[14,21]⟩],22⟩

theorem legal : Monotone2 circuit := by
  intro g hg
  simp only [circuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

end PEqualNP.Outside.L_meta_22245

theorem PEqualNP.Outside.L_meta_22245 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (810622 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact ⟨PEqualNP.Outside.L_meta_22245.circuit,PEqualNP.Outside.L_meta_22245.legal,by decide,by decide +kernel⟩
