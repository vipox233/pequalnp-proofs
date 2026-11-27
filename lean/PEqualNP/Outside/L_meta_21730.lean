import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21730

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.not, [6]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [9, 4]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.and, [2, 11]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [0, 13]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [15, 14]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4444 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21730

theorem PEqualNP.Outside.L_meta_21730 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4444 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21730.ckt, PEqualNP.Outside.L_meta_21730.fan, by decide, PEqualNP.Outside.L_meta_21730.ev⟩
