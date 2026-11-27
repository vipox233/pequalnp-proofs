import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.NotBracket PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_25993 :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 8 ∧ notCount C ≤ 1 ∧
      Represents (fun (u : Fin 4) (v : Fin 4) =>
        (([15, 14, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C := by
  -- The three terms test the disjoint types of missing entries under the one-hot promise.
  let circuit : Circuit :=
    ⟨[⟨.or, [2, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [8, 9]⟩,
      ⟨.and, [1, 4]⟩, ⟨.and, [3, 5]⟩, ⟨.or, [10, 11]⟩,
      ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩], 15⟩
  refine ⟨circuit, ?_, by decide, by decide, by decide⟩
  intro gate hgate
  simp [circuit] at hgate
  rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
