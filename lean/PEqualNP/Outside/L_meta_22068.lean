import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_22068

def witness : Circuit := ⟨[
  ⟨.and, [1, 2]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.or, [3, 8]⟩,
  ⟨.not, [9]⟩,
  ⟨.or, [0, 10]⟩
  ], 11⟩

end PEqualNP.Outside.L_meta_22068

theorem PEqualNP.Outside.L_meta_22068 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_22068.witness, ?_, by decide +kernel, ?_⟩
  · intro g hg
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    have all : PEqualNP.Outside.L_meta_22068.witness.gates.all (fun h => decide (h.op = .and ∨ h.op = .or ∨ h.op = .not) &&
        decide (h.inputs.length ≤ 2)) = true := by decide +kernel
    have fits := List.all_eq_true.mp all g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at fits
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fits.1, fits.2⟩
  · change ∀ i j : Fin 6, PEqualNP.Outside.L_meta_22068.witness.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (16575 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)
    decide +kernel
