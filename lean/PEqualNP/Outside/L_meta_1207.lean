import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1207_aux
open PEqualNP.CircuitLowerBounds
def c : Circuit := ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 8]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [4, 12]⟩, ⟨GateOp.and, [6, 7]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma eval_bool : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, c.eval [b0, b1, b2, b3, b4, b5, b6, b7] = ((b0 && b1) || (b0 && b2) || (b1 && b3) || (b2 && b4) || (b3 && b5) || (b4 && b5) || (b6 && b7)) := by decide +kernel

lemma wf : PEqualNP.MetaComplexity.Monotone2 c := by
  intro g hg
  simp only [c, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
end PEqualNP.Outside.L_meta_1207_aux
open PEqualNP.Outside.L_meta_1207_aux
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem PEqualNP.Outside.L_meta_1207 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨c, wf, ?_, ?_⟩
  · decide
  · intro x
    have h : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7] := by simp [List.ofFn_succ]
    rw [h]
    exact eval_bool (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
