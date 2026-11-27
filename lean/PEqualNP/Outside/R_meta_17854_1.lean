import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17854_1
    (hLeft : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (64 : ℕ) ≤ x1.size)
    (hRight : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (64 : ℕ) ≤ x1.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (64 : ℕ) ≤ x1.size) := by
  intro x1 hM hComp hOr
  rcases hOr with hl | hr
  · exact hLeft x1 hM hComp hl
  · exact hRight x1 hM hComp hr
