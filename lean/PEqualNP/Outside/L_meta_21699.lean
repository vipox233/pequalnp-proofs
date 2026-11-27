import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21699

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.and, [4, 6]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [8, 3]⟩,
      ⟨GateOp.and, [2, 9]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [3, 11]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [13, 12]⟩,
      ⟨GateOp.not, [14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266835 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21699

theorem PEqualNP.Outside.L_meta_21699 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266835 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21699.ckt, PEqualNP.Outside.L_meta_21699.fan, by decide, PEqualNP.Outside.L_meta_21699.ev⟩
