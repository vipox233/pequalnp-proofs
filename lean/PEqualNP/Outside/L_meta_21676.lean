import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21676
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates := [⟨GateOp.and, [1, 0]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.not, [6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.or, [6, 4]⟩, ⟨GateOp.and, [9, 10]⟩, ⟨GateOp.not, [11]⟩],
    output := 12 }

end PEqualNP.Outside.L_meta_21676

theorem PEqualNP.Outside.L_meta_21676 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275157 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_21676.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_21676.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · decide +kernel
