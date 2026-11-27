import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21743

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.and, [2, 6]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.not, [8]⟩,
      ⟨GateOp.and, [3, 9]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.and, [0, 11]⟩,
      ⟨GateOp.and, [1, 4]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [14, 12]⟩,
      ⟨GateOp.or, [15, 13]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21743

theorem PEqualNP.Outside.L_meta_21743 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267166 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21743.ckt, PEqualNP.Outside.L_meta_21743.fan, by decide, PEqualNP.Outside.L_meta_21743.ev⟩
