import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25981_aux

open PEqualNP.CircuitLowerBounds

def witnessCircuit : Circuit :=
  { gates :=
      [ { op := .or, inputs := [2, 5] }
      , { op := .not, inputs := [8] }
      , { op := .and, inputs := [1, 6] }
      , { op := .or, inputs := [0, 4] }
      , { op := .or, inputs := [10, 11] }
      , { op := .and, inputs := [9, 12] }
      , { op := .and, inputs := [2, 5] }
      , { op := .or, inputs := [13, 14] }
      ]
  , output := 15 }

end PEqualNP.Outside.L_meta_25981_aux

theorem PEqualNP.Outside.L_meta_25981 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([13, 5, 2, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨PEqualNP.Outside.L_meta_25981_aux.witnessCircuit, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_25981_aux.witnessCircuit] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
  · decide
