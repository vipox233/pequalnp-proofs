import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_1208 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧ ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 7)) x := by
  let c : Circuit := ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.and, [5, 13]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [15, 12]⟩,
    ⟨.or, [16, 14]⟩], 17⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [Monotone2, c]
  · decide +kernel
