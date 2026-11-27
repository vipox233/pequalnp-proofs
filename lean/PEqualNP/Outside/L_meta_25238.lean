import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25238

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  { gates := [
      ⟨GateOp.and, [3, 1]⟩,
      ⟨GateOp.and, [2, 4]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [1, 7]⟩,
      ⟨GateOp.or, [9, 0]⟩,
      ⟨GateOp.and, [2, 10]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [10, 2]⟩,
      ⟨GateOp.not, [12]⟩,
      ⟨GateOp.and, [13, 14]⟩
    ],
    output := 15 }

theorem circuit_legal : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨by simp, by decide⟩

theorem circuit_size : circuit.size ≤ 10 := by decide

theorem circuit_spec :
    ∀ i j : Fin 6,
      circuit.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (50331 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_25238

theorem PEqualNP.Outside.L_meta_25238 :
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
        ∀ i j : Fin 6,
          C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
            (50331 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25238.circuit,
    PEqualNP.Outside.L_meta_25238.circuit_legal,
    PEqualNP.Outside.L_meta_25238.circuit_size,
    PEqualNP.Outside.L_meta_25238.circuit_spec⟩
