import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own formula for
-- AND/OR circuits (notes/data/lrat-link), stated on the promise inputs. The file checks the gate kinds, the
-- gate count and the value on every input with one left and one right vertex on.
namespace PEqualNP.Outside.L_meta_22388
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [0, 14]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [19, 20]⟩, ⟨GateOp.or, [18, 21]⟩], 22⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843069 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_22388

theorem PEqualNP.Outside.L_meta_22388 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843069 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_22388.circ, PEqualNP.Outside.L_meta_22388.mono, by decide, PEqualNP.Outside.L_meta_22388.rep⟩
