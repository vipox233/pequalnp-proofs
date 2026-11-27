import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18397_3
    (hExtract :
      ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 →
          ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
        (∀ (x7 : Fin (x1 + x2) → Bool),
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 =
            Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) →
        (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x3) ∧
          (∀ e ∈ x3, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ x4.size + (1 : ℕ))
    (hCover :
      ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (k : ℕ)
        (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
        (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 →
          ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x3) →
        (∀ e ∈ x3, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)),
          (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧
          x3.card + x9.card + x10.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 : Fin x1) (x7 x8 : Fin x2), x5 ≠ x6 → x7 ≠ x8 → ¬((x5, x7) ∈ x3 ∧ (x5, x8) ∈ x3 ∧ (x6, x7) ∈ x3 ∧ (x6, x8) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x7 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x7 = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x2), (x8, x9) ∈ x3 ∧ x7 (Fin.castAdd x2 x8) = Bool.true ∧ x7 (Fin.natAdd x1 x9) = Bool.true)) → (∃ (x8 : Fin x4.gates.length), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x9 : Finset (Fin x1)) (x10 : Finset (Fin x2)), (∀ x11 ∈ x3, x11.1 ∈ x9 ∨ x11.2 ∈ x10) ∧ x3.card + x9.card + x10.card ≤ x4.size + (1 : ℕ)) := by
  intro x1 x2 x3 x4 hC4 hAO hFun hExAnd
  obtain ⟨k, A, B, hne, hcont, hcov, hcost⟩ := hExtract x1 x2 x3 x4 hC4 hAO hFun hExAnd
  obtain ⟨x9, x10, hXY, hle⟩ := hCover x1 x2 x3 k A B hC4 hne hcont hcov
  exact ⟨x9, x10, hXY, le_trans hle hcost⟩
