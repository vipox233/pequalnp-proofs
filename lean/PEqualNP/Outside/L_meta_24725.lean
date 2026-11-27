import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24725

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.and, [2, 8]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [9, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52669 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24725

theorem PEqualNP.Outside.L_meta_24725 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52669 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24725.ckt, PEqualNP.Outside.L_meta_24725.fan, by decide, PEqualNP.Outside.L_meta_24725.ev⟩
