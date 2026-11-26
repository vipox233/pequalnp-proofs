import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20871_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [13, 16]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [17, 18]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20871_aux

open PEqualNP.Outside.L_meta_20871_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20871 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (31388737 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
