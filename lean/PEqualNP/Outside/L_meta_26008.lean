import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26008_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def table : Fin 4 → Fin 4 → Bool :=
  fun (u : Fin 4) (v : Fin 4) => (([13, 12, 3, 3] : List ℕ).getD u.val 0).testBit v.val

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [2, 3]⟩,
        ⟨GateOp.or, [6, 7]⟩,
        ⟨GateOp.or, [8, 9]⟩,
        ⟨GateOp.and, [8, 9]⟩,
        ⟨GateOp.not, [11]⟩,
        ⟨GateOp.and, [10, 12]⟩,
        ⟨GateOp.and, [0, 4]⟩,
        ⟨GateOp.or, [13, 14]⟩ ],
    output := 15 }

lemma C_fan : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

lemma C_size : C.size ≤ 8 := by decide

lemma C_not : PEqualNP.NotBracket.notCount C ≤ 1 := by decide

lemma C_rep : Represents table C := by
  decide

end PEqualNP.Outside.L_meta_26008_aux

theorem PEqualNP.Outside.L_meta_26008 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
        PEqualNP.NotBracket.notCount C ≤ 1 ∧
          PEqualNP.Represents.Represents
            (fun (u : Fin 4) (v : Fin 4) => (([13, 12, 3, 3] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_26008_aux.C,
    PEqualNP.Outside.L_meta_26008_aux.C_fan,
    PEqualNP.Outside.L_meta_26008_aux.C_size,
    PEqualNP.Outside.L_meta_26008_aux.C_not,
    PEqualNP.Outside.L_meta_26008_aux.C_rep⟩
