import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8903_3
    (hOutInput :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x2 × Fin x2)),
        have x6 : ℕ → Prop := fun (x6 : ℕ) => ∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x7 x8) x6 = Bool.false;
        (x4.output < x2 + x2 ∧
          (100 : ℕ) < x1 ∧
          x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧
          (∀ (x9 : Fin x2), (x3 x9).card = x1 + (1 : ℕ)) ∧
          (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x10 ∈ x3 x13 ∧ x11 ∈ x3 x13) ∧
          PEqualNP.TopForm.IsAO2 (x2 + x2) x4 ∧
          x4.output < x2 + x2 + x4.size ∧
          PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 ∧
          x6 x4.output ∧
          (∀ x15 < x4.size, ∀ x17 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x2 + x2 + x15) → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬PEqualNP.EdgeOwnership.InCone (x2 + x2) x4 x15 x17) ∧
          (∀ x16 ∈ x5, x16.1 ∈ x3 x16.2 ∧ ∃ x18 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬x6 (x2 + x2 + x18) ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16.1} {x16.2}) (x2 + x2 + x18) = Bool.true) ∧
          (99 : ℕ) * (x2 * x1) < (100 : ℕ) * x5.card) →
        x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hOutGate :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x2 × Fin x2)),
        have x6 : ℕ → Prop := fun (x6 : ℕ) => ∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x7 x8) x6 = Bool.false;
        (x2 + x2 ≤ x4.output ∧
          (100 : ℕ) < x1 ∧
          x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧
          (∀ (x9 : Fin x2), (x3 x9).card = x1 + (1 : ℕ)) ∧
          (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x10 ∈ x3 x13 ∧ x11 ∈ x3 x13) ∧
          PEqualNP.TopForm.IsAO2 (x2 + x2) x4 ∧
          x4.output < x2 + x2 + x4.size ∧
          PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 ∧
          x6 x4.output ∧
          (∀ x15 < x4.size, ∀ x17 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x2 + x2 + x15) → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬PEqualNP.EdgeOwnership.InCone (x2 + x2) x4 x15 x17) ∧
          (∀ x16 ∈ x5, x16.1 ∈ x3 x16.2 ∧ ∃ x18 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬x6 (x2 + x2 + x18) ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16.1} {x16.2}) (x2 + x2 + x18) = Bool.true) ∧
          (99 : ℕ) * (x2 * x1) < (100 : ℕ) * x5.card) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x2 × Fin x2)),   have x6 : ℕ → Prop := fun (x6 : ℕ) => ∀ (x7 x8 : Finset (Fin x2)), x8.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x7 x8 → PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x7 x8) x6 = Bool.false;   (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x9 : Fin x2), (x3 x9).card = x1 + (1 : ℕ)) → (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x10 ∈ x3 x13 ∧ x11 ∈ x3 x13) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → x6 x4.output → (∀ x15 < x4.size, ∀ x17 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x2 + x2 + x15) → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x17).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬PEqualNP.EdgeOwnership.InCone (x2 + x2) x4 x15 x17) → (∀ x16 ∈ x5, x16.1 ∈ x3 x16.2 ∧ ∃ x18 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x18).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬x6 (x2 + x2 + x18) ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16.1} {x16.2}) (x2 + x2 + x18) = Bool.true) → (99 : ℕ) * (x2 * x1) < (100 : ℕ) * x5.card → x2 * x1 ≤ (100 : ℕ) * x4.size) :=
  fun x1 x2 x3 x4 x5 hx1 hx2 hLine hUniq hAO hOut hRight hSafe hNoCone hUnsafe hCard =>
    Or.elim (Nat.lt_or_ge x4.output (x2 + x2))
      (fun hLt => hOutInput x1 x2 x3 x4 x5 ⟨hLt, hx1, hx2, hLine, hUniq, hAO, hOut, hRight, hSafe, hNoCone, hUnsafe, hCard⟩)
      (fun hGe => hOutGate x1 x2 x3 x4 x5 ⟨hGe, hx1, hx2, hLine, hUniq, hAO, hOut, hRight, hSafe, hNoCone, hUnsafe, hCard⟩)
