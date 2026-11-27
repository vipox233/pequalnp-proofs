import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25967 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 2 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 7, 7, 0] : List ℕ).getD u.val 0).testBit v.val) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 7]⟩, ⟨.not, [8]⟩], 9⟩
  refine ⟨C, ?_, by decide, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, C]
  · decide
