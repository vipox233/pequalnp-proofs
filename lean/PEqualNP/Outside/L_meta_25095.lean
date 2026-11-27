import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25095

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [1, 2]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.and, [5, 7]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.and, [0, 2]⟩,
      ⟨GateOp.or, [1, 10]⟩,
      ⟨GateOp.or, [5, 11]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.or, [9, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843961 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25095

theorem PEqualNP.Outside.L_meta_25095 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274843961 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_25095.ckt, PEqualNP.Outside.L_meta_25095.fan, by decide, PEqualNP.Outside.L_meta_25095.ev⟩
