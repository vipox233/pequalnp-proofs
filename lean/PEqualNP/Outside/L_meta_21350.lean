import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search, replayed on the 20 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_21350_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [9, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [16, 18]⟩], 19⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21350_aux

open PEqualNP.Outside.L_meta_21350_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21350 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112607 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
