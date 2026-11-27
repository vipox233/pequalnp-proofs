import Mathlib
import PEqualNP.Defs

-- Witness circuit named in the step, replayed on the 21 inputs with one or two wires on.

namespace PEqualNP.Outside.L_meta_22455_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.not, [6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 15]⟩, ⟨.and, [1, 16]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [17, 18]⟩], 19⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_22455_aux

open PEqualNP.Outside.L_meta_22455_aux in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22455 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20025 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, witnessFit, by decide +kernel, by decide +kernel⟩
