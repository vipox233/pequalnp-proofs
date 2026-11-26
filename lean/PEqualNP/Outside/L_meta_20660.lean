import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search on the 25 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_20660_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 15]⟩], 16⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_20660_aux

open PEqualNP.Outside.L_meta_20660_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20660 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (14060544 : ℕ).testBit (5 * u.val + v.val)) 7) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
