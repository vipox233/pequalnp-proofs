import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5324_3
    (hExtract :
      ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2))
        (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)),
        (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 →
          ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x6 →
        (∀ x10 < x6.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∃ (x13 : Fin (x1 + x2) → Bool),
            (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧
            ¬∃ (x14 : Fin x1) (x15 : Fin x2),
              (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) →
        (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool),
          (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true →
          (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true →
          ∃ (x16 : Fin x1) (x17 : Fin x2),
            (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) →
        (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7,
          (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) =>
            Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧
          (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) =>
            Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) →
        ∃ (k : ℕ) (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x3) ∧
          (∀ e ∈ x4, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ x6.size + (2 : ℕ) * x7.card)
    (hCover :
      ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (k : ℕ)
        (A : Fin k → Finset (Fin x1)) (B : Fin k → Finset (Fin x2)),
        (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 →
          ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ a ∈ A i, ∀ b ∈ B i, (a, b) ∈ x3) →
        (∀ e ∈ x4, ∃ i, e.1 ∈ A i ∧ e.2 ∈ B i) →
        ∃ (X : Finset (Fin x1)) (Y : Finset (Fin x2)),
          (∀ e ∈ x4, e.1 ∈ X ∨ e.2 ∈ Y) ∧
          x4.card + X.card + Y.card ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (∀ (x1 x2 : ℕ) (x3 x4 x5 : Finset (Fin x1 × Fin x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x6 → (∀ x10 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) → (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true → (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x2), (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) → (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7, (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧ (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) → x5 ⊆ x4 → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → x4.card + x5.card ≤ x6.size + (2 : ℕ) * x7.card) := by
  classical
  intro x1 x2 x3 x4 x5 x6 x7 hC4 hAO hDirty hSafe hCov4 hSub5 hM1 hM2
  obtain ⟨k, A, B, hne, hcont, hcov, hcost⟩ := hExtract x1 x2 x3 x4 x6 x7 hC4 hAO hDirty hSafe hCov4
  obtain ⟨X, Y, hXY, hle⟩ := hCover x1 x2 x3 x4 k A B hC4 hne hcont hcov
  have hSubL : (x5.filter (fun e => e.1 ∈ X)).card ≤ X.card := by
    calc (x5.filter (fun e => e.1 ∈ X)).card
        = ((x5.filter (fun e => e.1 ∈ X)).image Prod.fst).card :=
          (Finset.card_image_of_injOn (fun a ha b hb hab =>
            hM1 a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab)).symm
      _ ≤ X.card := Finset.card_le_card (fun a ha => by
          rcases Finset.mem_image.mp ha with ⟨e, he, rfl⟩
          exact (Finset.mem_filter.mp he).2)
  have hSubR : (x5.filter (fun e => e.1 ∉ X)).card ≤ Y.card := by
    calc (x5.filter (fun e => e.1 ∉ X)).card
        = ((x5.filter (fun e => e.1 ∉ X)).image Prod.snd).card :=
          (Finset.card_image_of_injOn (fun a ha b hb hab =>
            hM2 a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab)).symm
      _ ≤ Y.card := Finset.card_le_card (fun b hb => by
          rcases Finset.mem_image.mp hb with ⟨e, he, rfl⟩
          rcases Finset.mem_filter.mp he with ⟨he5, heNotX⟩
          rcases hXY e (hSub5 he5) with hL | hR
          · exact False.elim (heNotX hL)
          · exact hR)
  have hSplit : x5.card ≤ (x5.filter (fun e => e.1 ∈ X)).card + (x5.filter (fun e => e.1 ∉ X)).card :=
    le_trans (Finset.card_le_card (fun e he => by
      by_cases h : e.1 ∈ X
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, h⟩)))
      (Finset.card_union_le _ _)
  omega
