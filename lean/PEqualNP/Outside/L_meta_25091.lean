import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25091

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.or, [0, 6]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [4, 9]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.and, [7, 11]⟩
    ],
    output := 12 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843582 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25091

theorem PEqualNP.Outside.L_meta_25091 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843582 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25091.ckt, PEqualNP.Outside.L_meta_25091.fan, by decide, PEqualNP.Outside.L_meta_25091.ev⟩
