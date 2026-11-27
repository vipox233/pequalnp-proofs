import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own circuit formula for AND/OR/NOT gates
-- (notes/data/lrat-link), stated on the promise inputs only, in the shape: AND/OR gates, one NOT gate, one
-- last gate. The file checks the gate kinds, the gate count, the number of NOT gates and the value on every
-- promise input.
namespace PEqualNP.Outside.L_meta_25985

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [3, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [9, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [12, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_25985

theorem PEqualNP.Outside.L_meta_25985 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([13, 13, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_25985.wit, by simp [PEqualNP.Outside.L_meta_25985.wit, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide, by decide⟩
