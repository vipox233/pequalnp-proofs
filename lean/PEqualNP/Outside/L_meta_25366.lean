import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25366

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ckt : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [8, 9]⟩,
    ⟨GateOp.and, [3, 6]⟩,
    ⟨GateOp.and, [1, 2]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.not, [14]⟩], 15⟩

theorem ckt_fan : FanInTwo ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by simp, by decide⟩

theorem ckt_size : ckt.size ≤ 10 := by
  decide

theorem ckt_eval :
    ∀ i j : Fin 6, ckt.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2313407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_25366

theorem PEqualNP.Outside.L_meta_25366 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2313407 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_25366.ckt,
   PEqualNP.Outside.L_meta_25366.ckt_fan,
   PEqualNP.Outside.L_meta_25366.ckt_size,
   PEqualNP.Outside.L_meta_25366.ckt_eval⟩
