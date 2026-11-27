import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own formula for
-- AND/OR circuits (notes/data/lrat-link), stated on the promise inputs. The file checks the gate kinds, the
-- gate count and the value on every input with one left and one right vertex on.
namespace PEqualNP.Outside.L_meta_23151
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [3, 17]⟩], 18⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 3) (v : Fin 6) => (30445 : ℕ).testBit (6 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_23151

theorem PEqualNP.Outside.L_meta_23151 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30445 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_23151.circ, PEqualNP.Outside.L_meta_23151.mono, by decide, PEqualNP.Outside.L_meta_23151.rep⟩
