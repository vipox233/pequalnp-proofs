import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22220

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [6, 4]⟩,
      ⟨GateOp.or, [7, 5]⟩,
      ⟨GateOp.not, [8]⟩,
      ⟨GateOp.and, [2, 9]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [11, 4]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [1, 14]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [16, 15]⟩
    ],
    output := 17 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22220

theorem PEqualNP.Outside.L_meta_22220 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17950 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22220.ckt, PEqualNP.Outside.L_meta_22220.fan, by decide, PEqualNP.Outside.L_meta_22220.ev⟩
