import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21915

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.and, [0, 7]⟩,
      ⟨GateOp.and, [2, 3]⟩,
      ⟨GateOp.and, [1, 4]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 11]⟩
    ],
    output := 12 }

theorem fan : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem ev : ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33836 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_21915

theorem PEqualNP.Outside.L_meta_21915 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33836 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨PEqualNP.Outside.L_meta_21915.ckt, PEqualNP.Outside.L_meta_21915.fan, by decide, PEqualNP.Outside.L_meta_21915.ev⟩
