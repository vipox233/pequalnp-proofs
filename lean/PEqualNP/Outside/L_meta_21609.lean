import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21609

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [8, 3]⟩,
      ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.and, [1, 11]⟩,
      ⟨GateOp.or, [7, 12]⟩
    ],
    output := 13 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (92 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21609

theorem PEqualNP.Outside.L_meta_21609 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (92 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21609.ckt, PEqualNP.Outside.L_meta_21609.fan, by decide, PEqualNP.Outside.L_meta_21609.ev⟩
