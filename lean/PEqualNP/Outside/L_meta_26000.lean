import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26000 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.and, [2, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.and, [4, 9]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, ?_, by decide, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
