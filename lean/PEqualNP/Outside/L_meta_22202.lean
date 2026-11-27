import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22202

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [1]⟩,
      ⟨GateOp.and, [3, 6]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.and, [4, 8]⟩,
      ⟨GateOp.not, [0]⟩,
      ⟨GateOp.and, [5, 10]⟩,
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.and, [0, 12]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [14, 11]⟩,
      ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.not, [16]⟩
    ],
    output := 17 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17329 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_22202

theorem PEqualNP.Outside.L_meta_22202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17329 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_22202.ckt, PEqualNP.Outside.L_meta_22202.fan, by decide, PEqualNP.Outside.L_meta_22202.ev⟩
