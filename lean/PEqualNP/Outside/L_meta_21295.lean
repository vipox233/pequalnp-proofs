import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own formula for
-- AND/OR circuits (notes/data/lrat-link), stated on the promise inputs. The file checks the gate kinds, the
-- gate count and the value on every input with one left and one right vertex on.
namespace PEqualNP.Outside.L_meta_21295
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.and, [10, 15]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [17, 18]⟩], 19⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (40795 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_21295

theorem PEqualNP.Outside.L_meta_21295 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40795 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_21295.circ, PEqualNP.Outside.L_meta_21295.mono, by decide, PEqualNP.Outside.L_meta_21295.rep⟩
