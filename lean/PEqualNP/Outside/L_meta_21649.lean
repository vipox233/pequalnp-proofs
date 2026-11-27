import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21649

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.not, [6]⟩,
      ⟨GateOp.and, [3, 7]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [2, 9]⟩,
      ⟨GateOp.or, [8, 4]⟩,
      ⟨GateOp.or, [11, 10]⟩,
      ⟨GateOp.not, [12]⟩
    ],
    output := 13 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12619 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21649

theorem PEqualNP.Outside.L_meta_21649 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12619 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21649.ckt, PEqualNP.Outside.L_meta_21649.fan, by decide, PEqualNP.Outside.L_meta_21649.ev⟩
