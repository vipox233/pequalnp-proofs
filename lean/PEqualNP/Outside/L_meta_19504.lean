import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19504

open PEqualNP.CircuitLowerBounds

deriving instance DecidableEq for GateOp

def c1 : Circuit where
  gates := [
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.and, [10, 12]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.not, [10]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.and, [13, 17]⟩,
    ⟨GateOp.or, [16, 18]⟩]
  output := 19

theorem main : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881278 : ℕ).testBit (5 * u.val + v.val)) C := by
  have hm : ∀ g ∈ c1.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 := by decide
  refine ⟨c1, fun g hg => ?_, by decide, by decide⟩
  obtain ⟨h1, h2⟩ := hm g hg
  exact ⟨by rcases h1 with h | h | h <;> simp [h], h2⟩

end PEqualNP.Outside.L_meta_19504

theorem PEqualNP.Outside.L_meta_19504 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7881278 : ℕ).testBit (5 * u.val + v.val)) C :=
  PEqualNP.Outside.L_meta_19504.main
