import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20693_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def wit : Circuit := ({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [3, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [2, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [10, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [4, 8] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 15] }], output := 17 } : PEqualNP.CircuitLowerBounds.Circuit)
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
end PEqualNP.Outside.L_meta_20693_aux

theorem PEqualNP.Outside.L_meta_20693 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (15926272 : ℕ).testBit (5 * u.val + v.val)) 8) := by
  refine ⟨PEqualNP.Outside.L_meta_20693_aux.wit, PEqualNP.Outside.L_meta_20693_aux.fit, by decide, ?_⟩
  intro u v
  revert u v
  decide +kernel

