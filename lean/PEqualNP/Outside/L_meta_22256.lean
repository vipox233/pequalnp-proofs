import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22256_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The witness, found by a SAT search: wires 0 to 3 are the rows, 4 to 9 the columns, gate j is
wire 10 + j. -/
def witness : Circuit := ⟨[⟨.or, [3, 8]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [12, 18]⟩, ⟨.and, [17, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩

theorem basis : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem correct : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 6) => (816953 : ℕ).testBit (6 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_22256_aux

theorem PEqualNP.Outside.L_meta_22256 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816953 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22256_aux.witness, PEqualNP.Outside.L_meta_22256_aux.basis, by decide,
    PEqualNP.Outside.L_meta_22256_aux.correct⟩
