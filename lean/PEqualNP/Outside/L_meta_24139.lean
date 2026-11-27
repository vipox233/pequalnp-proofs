import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24139

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.and, [3, 6]⟩,
      ⟨GateOp.and, [0, 6]⟩,
      ⟨GateOp.and, [2, 4]⟩,
      ⟨GateOp.not, [7]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.and, [10, 11]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [8, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279262 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24139

theorem PEqualNP.Outside.L_meta_24139 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279262 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24139.ckt, PEqualNP.Outside.L_meta_24139.fan, by decide, PEqualNP.Outside.L_meta_24139.ev⟩
