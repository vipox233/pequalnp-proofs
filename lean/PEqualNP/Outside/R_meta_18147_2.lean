import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18147_2
    (hEssentialAndOutput :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
        (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔
          ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size ∧ (13 : ℕ) ≤ x2.size ∧
        ∀ (i : Fin (26 : ℕ)), ∃ g < x2.size, ↑i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs)
    (hWithEssentialAndOutput :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 ∧
         (13 : ℕ) ≤ x2.size ∧ x2.size ≤ (63 : ℕ) ∧
         (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size ∧
         (∀ (i : Fin (26 : ℕ)), ∃ g < x2.size, ↑i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs) ∧
         (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔
           ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true)) →
        ∃ (x6 : Fin (26 : ℕ)) (x7 : Finset ℕ),
          (5 : ℕ) ≤ x7.card ∧
            ∀ x8 ∈ x7,
              x8 < x2.size ∧
                ∃ x10 < (26 : ℕ) + x8,
                  ∀ (x11 : Fin (26 : ℕ) → Bool),
                    have x12 : List Bool := x2.wires (List.ofFn (Function.update x11 x6 Bool.false));
                    x12.getD ((26 : ℕ) + x8) Bool.false = x12.getD x10 Bool.false) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     x2.size ≤ (63 : ℕ) →       (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →         ∃ (x6 : Fin (26 : ℕ)) (x7 : Finset ℕ),           (5 : ℕ) ≤ x7.card ∧             ∀ x8 ∈ x7,               x8 < x2.size ∧                 ∃ x10 < (26 : ℕ) + x8,                   ∀ (x11 : Fin (26 : ℕ) → Bool),                     have x12 : List Bool := x2.wires (List.ofFn (Function.update x11 x6 Bool.false));                     x12.getD ((26 : ℕ) + x8) Bool.false = x12.getD x10 Bool.false) := by
  intro x1 x2 hAO hSz hSpec
  exact
    let hE := hEssentialAndOutput x2 hAO hSpec
    hWithEssentialAndOutput x2 ⟨hAO, hE.2.2.1, hSz, hE.1, hE.2.1, hE.2.2.2, hSpec⟩
