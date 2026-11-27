import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25156

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [2, 6]⟩,
      ⟨GateOp.and, [1, 8]⟩,
      ⟨GateOp.or, [3, 9]⟩,
      ⟨GateOp.and, [0, 10]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.or, [7, 12]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.or, [11, 14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16522 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25156

theorem PEqualNP.Outside.L_meta_25156 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16522 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25156.ckt, PEqualNP.Outside.L_meta_25156.fan, by decide, PEqualNP.Outside.L_meta_25156.ev⟩
