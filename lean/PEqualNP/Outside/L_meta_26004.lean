import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26004 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 7, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [3, 4]⟩,
      ⟨.and, [1, 4]⟩,
      ⟨.and, [2, 7]⟩,
      ⟨.or, [9, 10]⟩,
      ⟨.or, [3, 11]⟩,
      ⟨.not, [12]⟩,
      ⟨.or, [8, 13]⟩], 14⟩
  refine ⟨C, ?_, by decide, by decide, by decide⟩
  simp [PEqualNP.MetaComplexity.FanInTwo, C]
