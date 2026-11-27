import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21979

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [3]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.and, [3, 8]⟩,
      ⟨GateOp.and, [1, 2]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.or, [12, 9]⟩,
      ⟨GateOp.or, [13, 10]⟩,
      ⟨GateOp.not, [14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16520 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21979

theorem PEqualNP.Outside.L_meta_21979 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16520 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21979.ckt, PEqualNP.Outside.L_meta_21979.fan, by decide, PEqualNP.Outside.L_meta_21979.ev⟩
