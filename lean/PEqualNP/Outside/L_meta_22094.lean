import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22094

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [6, 5]⟩,
      ⟨GateOp.not, [7]⟩,
      ⟨GateOp.and, [0, 8]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.or, [10, 5]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.and, [1, 3]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17173 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22094

theorem PEqualNP.Outside.L_meta_22094 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17173 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22094.ckt, PEqualNP.Outside.L_meta_22094.fan, by decide, PEqualNP.Outside.L_meta_22094.ev⟩
