import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26275 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([13, 3, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [10, 12]⟩], 13⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
