import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21690

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [1, 8]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [14, 13]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13081 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21690

theorem PEqualNP.Outside.L_meta_21690 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13081 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21690.ckt, PEqualNP.Outside.L_meta_21690.fan, by decide, PEqualNP.Outside.L_meta_21690.ev⟩
