import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25159

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.and, [0, 7]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [4, 9]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.or, [8, 12]⟩
    ],
    output := 13 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16824 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25159

theorem PEqualNP.Outside.L_meta_25159 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16824 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25159.ckt, PEqualNP.Outside.L_meta_25159.fan, by decide, PEqualNP.Outside.L_meta_25159.ev⟩
