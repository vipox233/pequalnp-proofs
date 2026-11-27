import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22318

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [6, 5]⟩,
      ⟨GateOp.not, [7]⟩,
      ⟨GateOp.and, [1, 8]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.or, [11, 5]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [2, 13]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [0, 15]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [17, 16]⟩
    ],
    output := 18 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18076 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22318

theorem PEqualNP.Outside.L_meta_22318 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18076 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22318.ckt, PEqualNP.Outside.L_meta_22318.fan, by decide, PEqualNP.Outside.L_meta_22318.ev⟩
