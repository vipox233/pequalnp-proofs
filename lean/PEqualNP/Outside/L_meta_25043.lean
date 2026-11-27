import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25043

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.not, [7]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.and, [4, 9]⟩,
      ⟨GateOp.or, [0, 10]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.and, [8, 12]⟩,
      ⟨GateOp.not, [13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583716 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25043

theorem PEqualNP.Outside.L_meta_25043 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270583716 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25043.ckt, PEqualNP.Outside.L_meta_25043.fan, by decide, PEqualNP.Outside.L_meta_25043.ev⟩
