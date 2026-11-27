import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21988

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [3]⟩,
      ⟨GateOp.and, [1, 6]⟩,
      ⟨GateOp.not, [1]⟩,
      ⟨GateOp.and, [3, 8]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.and, [4, 10]⟩,
      ⟨GateOp.or, [5, 7]⟩,
      ⟨GateOp.or, [12, 9]⟩,
      ⟨GateOp.or, [13, 11]⟩,
      ⟨GateOp.not, [14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16917 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21988

theorem PEqualNP.Outside.L_meta_21988 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16917 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21988.ckt, PEqualNP.Outside.L_meta_21988.fan, by decide, PEqualNP.Outside.L_meta_21988.ev⟩
