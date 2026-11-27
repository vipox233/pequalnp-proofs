import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24176

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [1, 4]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.and, [6, 9]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.or, [0, 11]⟩,
      ⟨GateOp.or, [1, 12]⟩,
      ⟨GateOp.or, [4, 13]⟩,
      ⟨GateOp.and, [10, 14]⟩,
      ⟨GateOp.not, [15]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266771 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24176

theorem PEqualNP.Outside.L_meta_24176 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266771 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24176.ckt, PEqualNP.Outside.L_meta_24176.fan, by decide, PEqualNP.Outside.L_meta_24176.ev⟩
