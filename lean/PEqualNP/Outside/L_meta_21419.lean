import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21419_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wit : Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 10] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [4, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [7, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [9, 12] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [17, 18] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [20, 19] }], output := 21 } : PEqualNP.CircuitLowerBounds.Circuit)
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
end PEqualNP.Outside.L_meta_21419_aux

theorem PEqualNP.Outside.L_meta_21419 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112318 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_21419_aux.wit, PEqualNP.Outside.L_meta_21419_aux.fit, by decide, ?_⟩
  intro u v
  revert u v
  decide +kernel

