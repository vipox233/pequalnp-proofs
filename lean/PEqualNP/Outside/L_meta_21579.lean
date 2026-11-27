import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.not, [4]⟩,
      ⟨GateOp.and, [2, 5]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [0, 7]⟩,
      ⟨GateOp.or, [3, 4]⟩,
      ⟨GateOp.and, [1, 9]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.or, [11, 10]⟩
    ],
    output := 12 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13212 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21579

theorem PEqualNP.Outside.L_meta_21579 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13212 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21579.ckt, PEqualNP.Outside.L_meta_21579.fan, by decide, PEqualNP.Outside.L_meta_21579.ev⟩
