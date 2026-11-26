import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19820

def circuit : Circuit :=
  ⟨[
  ⟨.or, [0, 7]⟩,
  ⟨.or, [1, 3]⟩,
  ⟨.or, [2, 6]⟩,
  ⟨.or, [4, 18]⟩,
  ⟨.or, [5, 17]⟩,
  ⟨.or, [4, 16]⟩,
  ⟨.or, [16, 17]⟩,
  ⟨.and, [8, 22]⟩,
  ⟨.or, [3, 19]⟩,
  ⟨.and, [9, 24]⟩,
  ⟨.or, [2, 20]⟩,
  ⟨.and, [10, 26]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.or, [18, 28]⟩,
  ⟨.and, [11, 29]⟩,
  ⟨.or, [5, 21]⟩,
  ⟨.and, [12, 31]⟩,
  ⟨.or, [0, 20]⟩,
  ⟨.and, [13, 33]⟩,
  ⟨.or, [7, 19]⟩,
  ⟨.and, [14, 35]⟩,
  ⟨.or, [6, 21]⟩,
  ⟨.and, [15, 37]⟩,
  ⟨.or, [23, 25]⟩,
  ⟨.or, [27, 39]⟩,
  ⟨.or, [30, 40]⟩,
  ⟨.or, [32, 41]⟩,
  ⟨.or, [34, 42]⟩,
  ⟨.or, [36, 43]⟩,
  ⟨.or, [38, 44]⟩
  ], 45⟩

end PEqualNP.Outside.L_meta_19820

theorem PEqualNP.Outside.L_meta_19820 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15116961972522724785 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  refine ⟨PEqualNP.Outside.L_meta_19820.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    letI : DecidableEq GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
    have all : PEqualNP.Outside.L_meta_19820.circuit.gates.all
        (fun a => decide (a.op = .and ∨ a.op = .or) && decide (a.inputs.length ≤ 2)) = true := by
      decide +kernel
    have h := List.all_eq_true.mp all g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩
  · change ∀ u v : Fin 8, PEqualNP.Outside.L_meta_19820.circuit.eval (PEqualNP.Represents.oneEach u v) =
        (15116961972522724785 : ℕ).testBit (8 * u.val + v.val)
    decide +kernel
