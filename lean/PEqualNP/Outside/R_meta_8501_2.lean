import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8501_2
    (hExtract :
      ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1))
        (x3 x4 : Fin x1 ↪ Fin (x1 + x1))
        (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x7 x8 : Fin x1), x3 x7 ≠ x4 x8) →
        (∀ (x9 x10 x11 x12 : Fin x1), x9 ≠ x10 → x11 ≠ x12 →
          ¬((x9, x11) ∈ x2 ∧ (x9, x12) ∈ x2 ∧ (x10, x11) ∈ x2 ∧ (x10, x12) ∈ x2)) →
        PEqualNP.TopForm.IsAO2 (x1 + x1) x5 →
        (∀ (x8 : Fin (x1 + x1) → Bool),
          PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 x8 =
            Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1),
              (x9, x10) ∈ x2 ∧ x8 (x3 x9) = Bool.true ∧ x8 (x4 x10) = Bool.true)) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x1)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x2) ∧
          (∀ e ∈ x2, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ x5.size + (1 : ℕ))
    (hCover :
      ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (k : ℕ)
        (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x1)),
        (∀ (x9 x10 x11 x12 : Fin x1), x9 ≠ x10 → x11 ≠ x12 →
          ¬((x9, x11) ∈ x2 ∧ (x9, x12) ∈ x2 ∧ (x10, x11) ∈ x2 ∧ (x10, x12) ∈ x2)) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x2) →
        (∀ e ∈ x2, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (X Y : Finset (Fin x1)),
          (∀ e ∈ x2, e.1 ∈ X ∨ e.2 ∈ Y) ∧
          x2.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x1)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x6 ∧ x8 (x3 x9) = Bool.true ∧ x8 (x4 x10) = Bool.true);   (∀ (x7 x8 : Fin x1), x3 x7 ≠ x4 x8) →     (∀ (x8 x9 : Fin x1), (x8, x9) ∈ x2 → (x8, x8) ∈ x2 ∧ (x9, x9) ∈ x2) →       (∀ (x9 x10 x11 x12 : Fin x1), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x2 ∧ (x9, x12) ∈ x2 ∧ (x10, x11) ∈ x2 ∧ (x10, x12) ∈ x2)) →         have x10 : Finset (Fin x1) := {x10 : Fin x1 | (x10, x10) ∈ x2};         (3 : ℕ) ≤ x10.card → x10.card < x1 → (2 : ℕ) * x10.card ≤ x2.card → (∀ (x14 : Fin x1), (x14, x14) ∈ x2 → (∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x14, x16) ∈ x2) ∧ ∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x16, x14) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x6 x2 x5 → x2.card + x10.card ≤ x5.size + (1 : ℕ)) := by
  intro x1 x2 x3 x4 x5 x6 hDisj hDiag hC4 x10 hGe3 hLt hTwo hDeg hAO hFun
  obtain ⟨k, A, B, hne, hcont, hcov, hcost⟩ := hExtract x1 x2 x3 x4 x5 hDisj hC4 hAO hFun
  obtain ⟨X, Y, hXY, hle⟩ := hCover x1 x2 k A B hC4 hne hcont hcov
  have hSub : x10 ⊆ X ∪ Y := by
    intro u hu
    have huDiag : (u, u) ∈ x2 := by
      simpa [x10] using hu
    rcases hXY (u, u) huDiag with huX | huY
    · exact Finset.mem_union_left Y huX
    · exact Finset.mem_union_right X huY
  have hCard : x10.card ≤ X.card + Y.card :=
    le_trans (Finset.card_le_card hSub) (Finset.card_union_le X Y)
  omega
