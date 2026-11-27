import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21713

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [1]⟩,
      ⟨GateOp.and, [0, 5]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.and, [2, 4]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.not, [10]⟩,
      ⟨GateOp.and, [3, 11]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.or, [14, 12]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279517 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21713

theorem PEqualNP.Outside.L_meta_21713 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279517 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21713.ckt, PEqualNP.Outside.L_meta_21713.fan, by decide, PEqualNP.Outside.L_meta_21713.ev⟩
