import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21546

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.and, [3, 5]⟩,
      ⟨GateOp.and, [1, 2]⟩,
      ⟨GateOp.or, [6, 4]⟩,
      ⟨GateOp.or, [8, 7]⟩,
      ⟨GateOp.not, [9]⟩
    ],
    output := 10 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4175 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21546

theorem PEqualNP.Outside.L_meta_21546 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4175 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21546.ckt, PEqualNP.Outside.L_meta_21546.fan, by decide, PEqualNP.Outside.L_meta_21546.ev⟩
