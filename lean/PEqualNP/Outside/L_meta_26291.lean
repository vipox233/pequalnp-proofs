import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26291 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 7, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C := by
  refine ⟨⟨[⟨.or, [3, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
