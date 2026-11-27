import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24172

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [7, 9]⟩,
      ⟨GateOp.and, [6, 10]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.and, [8, 13]⟩,
      ⟨GateOp.or, [12, 14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283422 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24172

theorem PEqualNP.Outside.L_meta_24172 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283422 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24172.ckt, PEqualNP.Outside.L_meta_24172.fan, by decide, PEqualNP.Outside.L_meta_24172.ev⟩
