import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24129

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 1]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [2, 5]⟩,
      ⟨GateOp.and, [6, 7]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.and, [7, 10]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.not, [11]⟩,
      ⟨GateOp.and, [12, 13]⟩
    ],
    output := 14 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275036 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24129

theorem PEqualNP.Outside.L_meta_24129 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275036 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24129.ckt, PEqualNP.Outside.L_meta_24129.fan, by decide, PEqualNP.Outside.L_meta_24129.ev⟩
