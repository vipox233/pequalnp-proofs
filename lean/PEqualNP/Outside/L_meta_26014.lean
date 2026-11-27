import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own circuit formula
-- (notes/data/lrat-link), stated on the promise inputs only; searched with one NOT (shape: AND/OR gates, one NOT, one last gate).
-- The file checks the gate kinds, the gate count, the number of NOT gates and the value on every promise input.
namespace PEqualNP.Outside.L_meta_26014

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.and, [2, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [1, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_26014

theorem PEqualNP.Outside.L_meta_26014 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 12, 7, 3] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_26014.wit, by simp [PEqualNP.Outside.L_meta_26014.wit, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide, by decide⟩
