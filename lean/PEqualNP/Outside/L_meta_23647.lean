import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23647

open PEqualNP.CircuitLowerBounds

deriving instance DecidableEq for GateOp

def c1 : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.and, [0, 1]⟩,
    ⟨GateOp.or, [8, 5]⟩,
    ⟨GateOp.not, [9]⟩,
    ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.and, [6, 10]⟩,
    ⟨GateOp.or, [7, 12]⟩]
  output := 13

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34717 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  have hm : ∀ g ∈ c1.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by decide
  refine ⟨c1, fun g hg => ?_, by decide, by decide +kernel⟩
  obtain ⟨h1, h2⟩ := hm g hg
  exact ⟨by rcases h1 with h | h | h <;> simp [h], h2⟩

end PEqualNP.Outside.L_meta_23647

theorem PEqualNP.Outside.L_meta_23647 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34717 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  PEqualNP.Outside.L_meta_23647.main
