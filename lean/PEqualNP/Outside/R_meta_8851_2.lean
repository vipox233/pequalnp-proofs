import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8851_2
    (hNoExtra :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x15 : ℕ) (x16 : Finset (Fin x2)),
        have f : Finset (Fin x2) → Finset (Fin x2) → List Bool := PEqualNP.GenericRejection.incidenceInput;
        have w : Finset (Fin x2) → Finset (Fin x2) → Bool := fun a b => PEqualNP.CircuitLowerBounds.wireValue x4 (f a b) (x2 + x2 + x15);
        have x17 : Fin x2 → Finset (Fin x2) := fun (x17 : Fin x2) => Finset.univ.filter fun (x18 : Fin x2) => w {x18} {x17} = Bool.true;
        ((100 : ℕ) < x1 ∧
          x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧
          (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) ∧
          (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) ∧
          PEqualNP.TopForm.IsAO2 (x2 + x2) x4 ∧
          x4.output < x2 + x2 + x4.size ∧
          (∀ (x14 x15 : Finset (Fin x2)), x4.eval (f x14 x15) = Bool.true ↔ PEqualNP.GenericRejection.incidenceFun x3 x14 x15 = Bool.true) ∧
          x15 < x4.size ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (100 : ℕ) < x16.card ∧
          Set.InjOn x17 ↑x16 ∧
          ∀ x18 ∈ x16, (1 : ℕ) < (x17 x18).card ∧ x17 x18 ⊆ x3 x18 ∧ w (x3 x18)ᶜ {x18} = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x4.size)
    (hHasExtra :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Finset (Fin x2) × Finset (Fin x2))) (x15 : ℕ) (x16 : Finset (Fin x2)),
        have f : Finset (Fin x2) → Finset (Fin x2) → List Bool := PEqualNP.GenericRejection.incidenceInput;
        have w : Finset (Fin x2) → Finset (Fin x2) → Bool := fun a b => PEqualNP.CircuitLowerBounds.wireValue x4 (f a b) (x2 + x2 + x15);
        have x17 : Fin x2 → Finset (Fin x2) := fun (x17 : Fin x2) => Finset.univ.filter fun (x18 : Fin x2) => w {x18} {x17} = Bool.true;
        (x5.Nonempty ∧
          (100 : ℕ) < x1 ∧
          x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧
          (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) ∧
          (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) ∧
          PEqualNP.TopForm.IsAO2 (x2 + x2) x4 ∧
          x4.output < x2 + x2 + x4.size ∧
          (∀ x12 ∈ x5, x1 < x12.2.card ∧ PEqualNP.GenericRejection.IsFalseInput x3 x12.1 x12.2) ∧
          (∀ x13 ∈ x5, ∀ x15 ∈ x5, x15.1 ⊆ x13.1 → x15.2 ⊆ x13.2 → x15 = x13) ∧
          (∀ (x14 x15 : Finset (Fin x2)), x4.eval (f x14 x15) = Bool.true ↔ PEqualNP.GenericRejection.incidenceFun x3 x14 x15 = Bool.true ∨ ∃ x16 ∈ x5, x16.1 ⊆ x14 ∧ x16.2 ⊆ x15) ∧
          x15 < x4.size ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          (100 : ℕ) < x16.card ∧
          Set.InjOn x17 ↑x16 ∧
          ∀ x18 ∈ x16, (1 : ℕ) < (x17 x18).card ∧ x17 x18 ⊆ x3 x18 ∧ w (x3 x18)ᶜ {x18} = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Finset (Fin x2) × Finset (Fin x2))),   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               (∀ x12 ∈ x5, x1 < x12.2.card ∧ PEqualNP.GenericRejection.IsFalseInput x3 x12.1 x12.2) →                 (∀ x13 ∈ x5, ∀ x15 ∈ x5, x15.1 ⊆ x13.1 → x15.2 ⊆ x13.2 → x15 = x13) →                   (∀ (x14 x15 : Finset (Fin x2)), x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.true ↔ PEqualNP.GenericRejection.incidenceFun x3 x14 x15 = Bool.true ∨ ∃ x16 ∈ x5, x16.1 ⊆ x14 ∧ x16.2 ⊆ x15) →                     (∃ x15 < x4.size,                         (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x15).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                           ∃ (x16 : Finset (Fin x2)),                             (100 : ℕ) < x16.card ∧                               have x17 : Fin x2 → Finset (Fin x2) := fun (x17 : Fin x2) => {x18 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x18} {x17}) (x2 + x2 + x15) = Bool.true};                               Set.InjOn x17 ↑x16 ∧ ∀ x18 ∈ x16, (1 : ℕ) < (x17 x18).card ∧ x17 x18 ⊆ x3 x18 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x18)ᶜ {x18}) (x2 + x2 + x15) = Bool.false) →                       x2 * x1 ≤ (100 : ℕ) * x4.size) :=
  fun x1 x2 x3 x4 x5 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    Exists.elim h10 fun x15 hx15 =>
    Exists.elim hx15.2.2 fun x16 hx16 =>
      Or.elim (Finset.eq_empty_or_nonempty x5)
        (fun hE =>
          hNoExtra x1 x2 x3 x4 x15 x16
            ⟨h1, h2, h3, h4, h5, h6,
              fun a b =>
                ⟨fun ha => Or.elim ((h9 a b).mp ha) id (fun hex => Exists.elim hex fun z hz => False.elim (Finset.notMem_empty z (Eq.subst (motive := fun s => z ∈ s) hE hz.1))),
                 fun ha => (h9 a b).mpr (Or.inl ha)⟩,
              hx15.1, hx15.2.1, hx16.1, hx16.2.1, hx16.2.2⟩)
        (fun hNE =>
          hHasExtra x1 x2 x3 x4 x5 x15 x16
            ⟨hNE, h1, h2, h3, h4, h5, h6, h7, h8, h9, hx15.1, hx15.2.1, hx16.1, hx16.2.1, hx16.2.2⟩)
