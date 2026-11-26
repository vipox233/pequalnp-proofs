import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20645_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [2, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20645_aux

open PEqualNP.Outside.L_meta_20645_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20645 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (7570432 : ℕ).testBit (5 * u.val + v.val)) 6) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
