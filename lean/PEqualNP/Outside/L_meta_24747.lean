import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24747

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.and, [6, 7]⟩,
      ⟨GateOp.not, [8]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [2, 10]⟩,
      ⟨GateOp.or, [0, 11]⟩,
      ⟨GateOp.or, [1, 12]⟩,
      ⟨GateOp.and, [9, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100269 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24747

theorem PEqualNP.Outside.L_meta_24747 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100269 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24747.ckt, PEqualNP.Outside.L_meta_24747.fan, by decide, PEqualNP.Outside.L_meta_24747.ev⟩
