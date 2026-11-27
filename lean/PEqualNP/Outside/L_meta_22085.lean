import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22085

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.or, [7, 4]⟩,
      ⟨GateOp.or, [8, 5]⟩,
      ⟨GateOp.not, [9]⟩,
      ⟨GateOp.and, [2, 10]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.and, [1, 3]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22085

theorem PEqualNP.Outside.L_meta_22085 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16944 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22085.ckt, PEqualNP.Outside.L_meta_22085.fan, by decide, PEqualNP.Outside.L_meta_22085.ev⟩
