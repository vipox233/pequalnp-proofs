import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19473

open PEqualNP.CircuitLowerBounds

deriving instance DecidableEq for GateOp

def c1 : Circuit where
  gates := [
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.not, [11]⟩,
    ⟨GateOp.or, [0, 10]⟩,
    ⟨GateOp.or, [4, 9]⟩,
    ⟨GateOp.and, [15, 16]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [17, 18]⟩]
  output := 19

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066039 : ℕ).testBit (5 * u.val + v.val)) C := by
  have hm : ∀ g ∈ c1.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by decide
  refine ⟨c1, fun g hg => ?_, by decide, by decide⟩
  obtain ⟨h1, h2⟩ := hm g hg
  exact ⟨by rcases h1 with h | h | h <;> simp [h], h2⟩

end PEqualNP.Outside.L_meta_19473

theorem PEqualNP.Outside.L_meta_19473 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12066039 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19473.main
