import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8887_3
    (hExtract :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a b c d : Fin n), a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        (∃ (π : Equiv.Perm (Fin n)), ∀ (u : Fin n), (u, π u) ∈ E) →
        (∀ (v : Fin n), (3 : ℕ) ≤ {e ∈ E | e.1 = v}.card ∧ (3 : ℕ) ≤ {e ∈ E | e.2 = v}.card) →
        PEqualNP.TopForm.IsAO2 (n + n) C →
        (∀ (x : Fin (n + n) → Bool),
          PEqualNP.MetaComplexity.circuitFun (n + n) C x =
            Decidable.decide (∃ (u v : Fin n), (u, v) ∈ E ∧ x (Fin.castAdd n u) = Bool.true ∧ x (Fin.natAdd n v) = Bool.true)) →
        ∃ (k : ℕ) (A B : Fin k → Finset (Fin n)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) ∧
          (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ C.size + (1 : ℕ))
    (hCover :
      ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (k : ℕ)
        (A B : Fin k → Finset (Fin n)),
        (∀ (a b c d : Fin n), a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E)) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ E) →
        (∀ e ∈ E, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (X Y : Finset (Fin n)),
          (∀ e ∈ E, e.1 ∈ X ∨ e.2 ∈ Y) ∧
          E.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (have x1 : (x1 : ℕ) → Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 x5 x6 x7 : Fin x1), x4 ≠ x5 → x6 ≠ x7 → ¬((x4, x6) ∈ x2 ∧ (x4, x7) ∈ x2 ∧ (x5, x6) ∈ x2 ∧ (x5, x7) ∈ x2)) ∧ (∃ (x4 : Equiv.Perm (Fin x1)), ∀ (x5 : Fin x1), (x5, x4 x5) ∈ x2) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ ∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), (x5, x6) ∈ x2 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true); ∀ (x2 : ℕ) (x3 : Finset (Fin x2 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 x2 x3 x4 → (∀ (x6 : Fin x2), (3 : ℕ) ≤ {x7 ∈ x3 | x7.1 = x6}.card ∧ (3 : ℕ) ≤ {x7 ∈ x3 | x7.2 = x6}.card) → x3.card + x2 ≤ x4.size + (1 : ℕ)) := by
  classical
  intro x1 x2 x3 x4 h1 hDeg
  rcases h1 with ⟨hC4, ⟨π, hπ⟩, hAO, hFun⟩
  obtain ⟨k, A, B, hne, hcont, hcov, hcost⟩ := hExtract x2 x3 x4 hC4 ⟨π, hπ⟩ hDeg hAO hFun
  obtain ⟨X, Y, hXY, hle⟩ := hCover x2 x3 k A B hC4 hne hcont hcov
  have hsub : (Finset.univ : Finset (Fin x2)) ⊆ X ∪ Y.image π.symm := by
    intro u _
    rcases hXY (u, π u) (hπ u) with hu | hv
    · exact Finset.mem_union_left _ hu
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨π u, hv, π.symm_apply_apply u⟩)
  have hn : x2 ≤ X.card + Y.card := by
    calc x2 = (Finset.univ : Finset (Fin x2)).card := (Fintype.card_fin x2).symm
      _ ≤ (X ∪ Y.image π.symm).card := Finset.card_le_card hsub
      _ ≤ X.card + (Y.image π.symm).card := Finset.card_union_le X (Y.image π.symm)
      _ ≤ X.card + Y.card := Nat.add_le_add_left Finset.card_image_le X.card
  omega
