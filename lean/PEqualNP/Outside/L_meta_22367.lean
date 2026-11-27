import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own formula for
-- AND/OR circuits (notes/data/lrat-link), stated on the promise inputs. The file checks the gate kinds, the
-- gate count and the value on every input with one left and one right vertex on.
namespace PEqualNP.Outside.L_meta_22367
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [18, 20]⟩, ⟨GateOp.or, [19, 21]⟩], 22⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841533 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_22367

theorem PEqualNP.Outside.L_meta_22367 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841533 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22367.circ, PEqualNP.Outside.L_meta_22367.mono, by decide, PEqualNP.Outside.L_meta_22367.rep⟩
