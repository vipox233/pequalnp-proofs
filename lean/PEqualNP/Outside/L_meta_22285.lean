import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22285_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wit : Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [18, 19] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [21, 20] }], output := 22 } : PEqualNP.CircuitLowerBounds.Circuit)
def okOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false
theorem okOpSound (g : Gate) (h : okOp g = true) : g.op = .and ∨ g.op = .or := by
  cases hg : g.op <;> simp [okOp, hg] at h ⊢
theorem fit : PEqualNP.MetaComplexity.Monotone2 wit := by
  have hl : wit.gates.all (fun g => okOp g && decide (g.inputs.length ≤ 2)) = true := by decide +kernel
  intro g hg
  have hp := List.all_eq_true.mp hl g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using okOpSound g hp.1, hp.2⟩
end PEqualNP.Outside.L_meta_22285_aux

theorem PEqualNP.Outside.L_meta_22285 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (836983 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_22285_aux.wit, PEqualNP.Outside.L_meta_22285_aux.fit, by decide, ?_⟩
  intro u v
  revert u v
  decide +kernel

