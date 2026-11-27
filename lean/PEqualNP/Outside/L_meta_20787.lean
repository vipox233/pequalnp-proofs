import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20787_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ5 : Circuit :=
  Circuit.mk [
    Gate.mk .or [0, 1], Gate.mk .and [0, 1], Gate.mk .not [6], Gate.mk .and [5, 7],
    Gate.mk .or [8, 2], Gate.mk .and [8, 2], Gate.mk .not [10], Gate.mk .and [9, 11],
    Gate.mk .or [12, 3], Gate.mk .and [12, 3], Gate.mk .not [14], Gate.mk .and [13, 15],
    Gate.mk .or [16, 4], Gate.mk .and [16, 4], Gate.mk .not [18], Gate.mk .and [17, 19]
  ] 20

def circ6 : Circuit :=
  Circuit.mk [
    Gate.mk .or [0, 1], Gate.mk .and [0, 1], Gate.mk .not [7], Gate.mk .and [6, 8],
    Gate.mk .or [9, 2], Gate.mk .and [9, 2], Gate.mk .not [11], Gate.mk .and [10, 12],
    Gate.mk .or [13, 3], Gate.mk .and [13, 3], Gate.mk .not [15], Gate.mk .and [14, 16],
    Gate.mk .or [17, 4], Gate.mk .and [17, 4], Gate.mk .not [19], Gate.mk .and [18, 20],
    Gate.mk .or [21, 5], Gate.mk .and [21, 5], Gate.mk .not [23], Gate.mk .and [22, 24]
  ] 25

def par5 (x : Fin 5 → Bool) : Bool :=
  xor (xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)) (x 4)

def par6 (x : Fin 6 → Bool) : Bool :=
  xor (xor (xor (xor (xor (x 0) (x 1)) (x 2)) (x 3)) (x 4)) (x 5)

theorem solve_20786 (f : (Fin 5 → Bool) → Bool) (hf : ∀ x, f x = par5 x) :
    HasCircuitSize 5 f 16 := by
  refine ⟨circ5, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circ5, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [hf x]
    revert x
    decide +kernel

theorem solve_20787 (f : (Fin 6 → Bool) → Bool) (hf : ∀ x, f x = par6 x) :
    HasCircuitSize 6 f 20 := by
  refine ⟨circ6, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circ6, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro x
    rw [hf x]
    revert x
    decide +kernel

end PEqualNP.Outside.L_meta_20787_aux

theorem PEqualNP.Outside.L_meta_20787 : (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (7608434000728254870 : ℕ).testBit (PEqualNP.MetaComplexity.tableIndex x)) 20) := by
  exact PEqualNP.Outside.L_meta_20787_aux.solve_20787 _ (by decide +kernel)
