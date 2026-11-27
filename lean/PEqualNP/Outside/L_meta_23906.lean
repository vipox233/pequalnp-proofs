import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23906

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.not, [5]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.and, [7, 8]⟩,
      ⟨GateOp.or, [6, 9]⟩
    ],
    output := 10 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275101 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23906

theorem PEqualNP.Outside.L_meta_23906 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275101 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_23906.ckt, PEqualNP.Outside.L_meta_23906.fan, by decide, PEqualNP.Outside.L_meta_23906.ev⟩
