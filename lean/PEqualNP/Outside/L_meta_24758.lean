import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24758

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [7, 8]⟩,
      ⟨GateOp.and, [2, 9]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.and, [6, 12]⟩,
      ⟨GateOp.or, [11, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101305 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24758

theorem PEqualNP.Outside.L_meta_24758 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101305 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24758.ckt, PEqualNP.Outside.L_meta_24758.fan, by decide, PEqualNP.Outside.L_meta_24758.ev⟩
