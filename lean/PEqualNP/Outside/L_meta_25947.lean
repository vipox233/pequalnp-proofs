import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25947 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([11, 7, 6, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [6, 5]⟩, ⟨.or, [2, 1]⟩, ⟨.and, [8, 9]⟩,
    ⟨.or, [4, 0]⟩, ⟨.or, [6, 2]⟩, ⟨.not, [12]⟩,
    ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
