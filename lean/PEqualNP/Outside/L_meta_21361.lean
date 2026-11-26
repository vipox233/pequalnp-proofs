import Mathlib
import PEqualNP.Defs

-- Witness circuit found by an exact SAT search, replayed on the 20 promise inputs (one row and one column on).

namespace PEqualNP.Outside.L_meta_21361_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [11, 14]⟩, ⟨.and, [12, 17]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [15, 19]⟩], 20⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h|h|h|h|h|h|h|h|h|h|h|h <;> subst g <;> simp

end PEqualNP.Outside.L_meta_21361_aux

open PEqualNP.Outside.L_meta_21361_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_21361 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39418 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact ⟨witness, mono, by decide +kernel, by decide +kernel⟩
