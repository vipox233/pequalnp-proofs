import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26019

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [6, 7]⟩, ⟨GateOp.and, [2, 5]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.not, [13]⟩], 14⟩

theorem fanIn : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem size_le : circ.size ≤ 7 := by decide

theorem nots : PEqualNP.NotBracket.notCount circ ≤ 1 := by decide

theorem rep : PEqualNP.Represents.Represents
    (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 13, 3] : List ℕ).getD u.val 0).testBit v.val) circ := by
  decide

end PEqualNP.Outside.L_meta_26019

theorem PEqualNP.Outside.L_meta_26019 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 14, 13, 3] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨PEqualNP.Outside.L_meta_26019.circ, PEqualNP.Outside.L_meta_26019.fanIn,
    PEqualNP.Outside.L_meta_26019.size_le, PEqualNP.Outside.L_meta_26019.nots,
    PEqualNP.Outside.L_meta_26019.rep⟩
