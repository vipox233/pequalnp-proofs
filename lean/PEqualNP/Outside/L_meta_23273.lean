import PEqualNP.Defs

-- The circuit was found by a SAT solver (CaDiCaL) on the project's own circuit formula
-- for AND/OR/NOT gates (notes/data/lrat-link), stated on the inputs with two points on (or one). The file checks
-- the gate kinds, the gate count and the value on each of those inputs.
namespace PEqualNP.Outside.L_meta_23273

def wit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [10, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23273

theorem PEqualNP.Outside.L_meta_23273 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34086 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23273.wit, by simp [PEqualNP.Outside.L_meta_23273.wit, PEqualNP.MetaComplexity.FanInTwo], by decide, by decide⟩
