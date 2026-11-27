import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21741

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 2]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.not, [6]⟩,
      ⟨GateOp.and, [1, 7]⟩,
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.not, [9]⟩,
      ⟨GateOp.and, [4, 10]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.and, [2, 12]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [14, 13]⟩,
      ⟨GateOp.not, [15]⟩
    ],
    output := 16 }

theorem fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 5, ckt.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266907 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21741

theorem PEqualNP.Outside.L_meta_21741 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266907 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21741.ckt, PEqualNP.Outside.L_meta_21741.fan, by decide, PEqualNP.Outside.L_meta_21741.ev⟩
