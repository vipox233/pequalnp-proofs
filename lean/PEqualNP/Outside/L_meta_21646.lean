import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21646

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.not, [8]⟩,
      ⟨GateOp.and, [1, 9]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [12, 11]⟩
    ],
    output := 13 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8921 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21646

theorem PEqualNP.Outside.L_meta_21646 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8921 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21646.ckt, PEqualNP.Outside.L_meta_21646.fan, by decide, PEqualNP.Outside.L_meta_21646.ev⟩
