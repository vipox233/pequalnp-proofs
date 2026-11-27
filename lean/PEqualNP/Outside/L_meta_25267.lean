import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25267

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.and, [1, 6]⟩,
      ⟨GateOp.or, [5, 7]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [3, 9]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.not, [9]⟩,
      ⟨GateOp.and, [4, 12]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.not, [14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147477 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25267

theorem PEqualNP.Outside.L_meta_25267 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147477 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25267.ckt, PEqualNP.Outside.L_meta_25267.fan, by decide, PEqualNP.Outside.L_meta_25267.ev⟩
