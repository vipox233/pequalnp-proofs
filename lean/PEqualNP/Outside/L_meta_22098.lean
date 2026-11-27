import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22098

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.not, [6]⟩,
      ⟨GateOp.and, [0, 7]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.and, [1, 3]⟩,
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17203 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22098

theorem PEqualNP.Outside.L_meta_22098 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17203 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22098.ckt, PEqualNP.Outside.L_meta_22098.fan, by decide, PEqualNP.Outside.L_meta_22098.ev⟩
