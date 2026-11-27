import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.and, [1, 4]⟩,
      ⟨GateOp.and, [5, 7]⟩,
      ⟨GateOp.or, [4, 9]⟩,
      ⟨GateOp.and, [6, 10]⟩,
      ⟨GateOp.or, [6, 10]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.or, [13, 14]⟩
    ],
    output := 15 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279260 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24169

theorem PEqualNP.Outside.L_meta_24169 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279260 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_24169.ckt, PEqualNP.Outside.L_meta_24169.fan, by decide, PEqualNP.Outside.L_meta_24169.ev⟩
