import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17162_4
    (hExtract :
      ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) :=
          fun (x5 : Finset (Fin x1 × Fin x2)) =>
            x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};
        ¬(x1 = (3 : ℕ) ∧ ∀ (x6 : Fin x1), ∃ (x7 : Fin x2), ∀ (x8 : Fin x1), (x8, x7) ∈ x3 ↔ x8 ≠ x6) →
        (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 →
          ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
        (∀ (x9 : Fin (x1 + x2) → Bool),
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x9 =
            Decidable.decide (∃ x10 ∈ x3, x9 (Fin.castAdd x2 x10.1) = Bool.true ∧ x9 (Fin.natAdd x1 x10.2) = Bool.true)) →
        (¬∃ (x10 : Finset (Fin x1 × Fin x2)) (x11 : Finset (Fin x1 × Fin x2)) (x12 : Fin (x1 + x2)),
          x10.Nonempty ∧ x10 ∪ x11 = x3 ∧ Disjoint (x5 x10) (x5 x11) ∧
            ∀ x13 ∈ x10, Fin.castAdd x2 x13.1 = x12 ∨ Fin.natAdd x1 x13.2 = x12) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x3) ∧
          (∀ e ∈ x3, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ x4.size + (1 : ℕ))
    (hCover :
      ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (k : ℕ)
        (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
        (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 →
          ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x3) →
        (∀ e ∈ x3, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)),
          (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧
          x3.card + x11.card + x12.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   ¬(x1 = (3 : ℕ) ∧ ∀ (x6 : Fin x1), ∃ (x7 : Fin x2), ∀ (x8 : Fin x1), (x8, x7) ∈ x3 ↔ x8 ≠ x6) → (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x9 = Decidable.decide (∃ x10 ∈ x3, x9 (Fin.castAdd x2 x10.1) = Bool.true ∧ x9 (Fin.natAdd x1 x10.2) = Bool.true)) → (¬∃ (x10 : Finset (Fin x1 × Fin x2)) (x11 : Finset (Fin x1 × Fin x2)) (x12 : Fin (x1 + x2)), x10.Nonempty ∧ x10 ∪ x11 = x3 ∧ Disjoint (x5 x10) (x5 x11) ∧ ∀ x13 ∈ x10, Fin.castAdd x2 x13.1 = x12 ∨ Fin.natAdd x1 x13.2 = x12) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ)) := by
  intro x1 x2 x3 x4 x5 hNot3 hC4 hAO hFun hNoStar
  obtain ⟨k, A, B, hne, hcont, hcov, hcost⟩ := hExtract x1 x2 x3 x4 hNot3 hC4 hAO hFun hNoStar
  obtain ⟨x11, x12, hXY, hle⟩ := hCover x1 x2 x3 k A B hC4 hne hcont hcov
  exact ⟨x11, x12, hXY, le_trans hle hcost⟩
