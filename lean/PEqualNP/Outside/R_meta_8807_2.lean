import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8807_2
    (hLineInter : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
      (∀ (p q : Fin n), p ≠ q → ∃! l : Fin n, p ∈ S l ∧ q ∈ S l) →
      ∀ (l1 l2 : Fin n), l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ))
    (hWithDual : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (300 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      (∀ (l1 l2 : Fin x2), l1 ≠ l2 → (x3 l1 ∩ x3 l2).card ≤ (1 : ℕ)) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →
      (∃ x13 < x4.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ (x14 : Finset (Fin x2)),
          (100 : ℕ) < x14.card ∧
          have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};
          Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →
      x2 * x1 ≤ (100 : ℕ) * x4.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (300 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →                 (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →                   (∃ x13 < x4.size,                       (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                         ∃ (x14 : Finset (Fin x2)),                           (100 : ℕ) < x14.card ∧                             have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};                             Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →                     x2 * x1 ≤ (100 : ℕ) * x4.size :=
  fun x1 x2 x3 x4 h300 hx2 hcard huniq hAO hout hRight hFalse hGate =>
    hWithDual x1 x2 x3 x4 h300 hx2 hcard huniq (hLineInter x2 x3 huniq) hAO hout hRight hFalse hGate
