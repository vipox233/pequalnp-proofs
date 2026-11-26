import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own formula for
-- AND/OR circuits (notes/data/lrat-link), stated on the promise inputs. The file checks the gate kinds, the
-- gate count and the value on every input with one left and one right vertex on.
namespace PEqualNP.Outside.L_meta_21322
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [3, 8]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.and, [14, 15]⟩, ⟨GateOp.and, [11, 13]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (104250 : ℕ).testBit (5 * u.val + v.val)) circ := by decide +kernel

end PEqualNP.Outside.L_meta_21322

theorem PEqualNP.Outside.L_meta_21322 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (104250 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_21322.circ, PEqualNP.Outside.L_meta_21322.mono, by decide, PEqualNP.Outside.L_meta_21322.rep⟩
