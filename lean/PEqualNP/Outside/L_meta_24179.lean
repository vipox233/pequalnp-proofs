import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24179

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.and, [3, 8]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.and, [6, 11]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.not, [13]⟩,
      ⟨GateOp.and, [14, 15]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266844 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24179

theorem PEqualNP.Outside.L_meta_24179 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266844 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24179.ckt, PEqualNP.Outside.L_meta_24179.fan, by decide, PEqualNP.Outside.L_meta_24179.ev⟩
