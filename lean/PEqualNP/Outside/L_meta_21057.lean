import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search, replayed on the 20 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_21057_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [4, 16]⟩], 17⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21057_aux

open PEqualNP.Outside.L_meta_21057_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21057 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103797 : ℕ).testBit (5 * u.val + v.val)) 9) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
