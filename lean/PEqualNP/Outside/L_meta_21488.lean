import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21488

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [1, 2]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.or, [6, 5]⟩,
      ⟨GateOp.not, [7]⟩
    ],
    output := 8 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4167 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21488

theorem PEqualNP.Outside.L_meta_21488 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4167 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21488.ckt, PEqualNP.Outside.L_meta_21488.fan, by decide, PEqualNP.Outside.L_meta_21488.ev⟩
