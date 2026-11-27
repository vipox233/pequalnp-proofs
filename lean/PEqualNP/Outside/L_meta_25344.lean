import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25344

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.not, [4]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.and, [2, 6]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [1, 8]⟩,
      ⟨GateOp.not, [9]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.or, [0, 13]⟩,
      ⟨GateOp.and, [12, 14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25344

theorem PEqualNP.Outside.L_meta_25344 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2182075 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25344.ckt, PEqualNP.Outside.L_meta_25344.fan, by decide, PEqualNP.Outside.L_meta_25344.ev⟩
