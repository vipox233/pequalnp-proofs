import PEqualNP.Defs

theorem PEqualNP.MetaComplexity.L27130 :
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ), (h = 1 ∨ h = 6) →
    ¬ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      (C.wires (List.ofFn x)).getD h false = true := by
  intro C h hh
  rintro ⟨x, _, h1, h6, hw⟩
  have pre : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), ∃ t,
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
    intro gs
    induction gs with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g gs ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      exact ⟨_ :: t, by simpa using ht⟩
  obtain ⟨t, ht⟩ := pre C.gates (List.ofFn x)
  have hwires : C.wires (List.ofFn x) = List.ofFn x ++ t := ht
  rw [hwires] at hw
  rcases hh with rfl | rfl
  · have : (List.ofFn x ++ t).getD 1 false = x 1 := by
      rw [List.getD_append _ _ _ _ (by simp)]; simp
    rw [this, h1] at hw; exact absurd hw (by simp)
  · have : (List.ofFn x ++ t).getD 6 false = x 6 := by
      rw [List.getD_append _ _ _ _ (by simp)]; simp
    rw [this, h6] at hw; exact absurd hw (by simp)
