import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18713_2
    (hLeftEarlier :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      have w : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (c : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.BlindGate.wireValue c (26 : ℕ);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (x3.size = (65 : ℕ) ∧
         PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
         (∀ x8 ∈ x3.gates, x8.inputs.Nodup) ∧
         x3.output = (90 : ℕ) ∧
         x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } ∧
         (∀ (x11 x12 : Fin (13 : ℕ)), x1 x11 x12 →
           have x14 : Fin (26 : ℕ) → Bool := fun (x14 : Fin (26 : ℕ)) => Decidable.decide (x14 = Fin.castAdd (13 : ℕ) x11 ∨ x14 = Fin.natAdd (13 : ℕ) x12);
           w x3 x14 x4 = Bool.true ∧ w x3 x14 x5 = Bool.true) ∧
         (∀ (x12 : Fin (26 : ℕ) → Bool), Maximal (fun (x13 : Fin (26 : ℕ) → Bool) => ¬x2 x13) x12 → w x3 x12 (if x12 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) ∧
         (26 : ℕ) ≤ x4 ∧ (26 : ℕ) ≤ x5 ∧ x4 < x5 ∧
         (∀ x15 < (64 : ℕ), ∃ x17 < (65 : ℕ), x15 < x17 ∧ (26 : ℕ) + x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x17).inputs)) →
        ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : ℕ) (x18 : ℕ),
          x16.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x16 ∧ (∀ x19 ∈ x16.gates, x19.inputs.Nodup) ∧
          x17 ≠ x18 ∧ x17 < (26 : ℕ) + x16.size ∧ x18 < (26 : ℕ) + x16.size ∧
          ∀ (x19 : Fin (26 : ℕ) → Bool), w x16 x19 x17 = w x3 x19 x4 ∧ w x16 x19 x18 = w x3 x19 x5)
    (hRightEarlier :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      have w : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (c : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.BlindGate.wireValue c (26 : ℕ);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        (x3.size = (65 : ℕ) ∧
         PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
         (∀ x8 ∈ x3.gates, x8.inputs.Nodup) ∧
         x3.output = (90 : ℕ) ∧
         x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } ∧
         (∀ (x11 x12 : Fin (13 : ℕ)), x1 x11 x12 →
           have x14 : Fin (26 : ℕ) → Bool := fun (x14 : Fin (26 : ℕ)) => Decidable.decide (x14 = Fin.castAdd (13 : ℕ) x11 ∨ x14 = Fin.natAdd (13 : ℕ) x12);
           w x3 x14 x4 = Bool.true ∧ w x3 x14 x5 = Bool.true) ∧
         (∀ (x12 : Fin (26 : ℕ) → Bool), Maximal (fun (x13 : Fin (26 : ℕ) → Bool) => ¬x2 x13) x12 → w x3 x12 (if x12 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) ∧
         (26 : ℕ) ≤ x4 ∧ (26 : ℕ) ≤ x5 ∧ x5 ≤ x4 ∧
         (∀ x15 < (64 : ℕ), ∃ x17 < (65 : ℕ), x15 < x17 ∧ (26 : ℕ) + x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x17).inputs)) →
        ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : ℕ) (x18 : ℕ),
          x16.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x16 ∧ (∀ x19 ∈ x16.gates, x19.inputs.Nodup) ∧
          x17 ≠ x18 ∧ x17 < (26 : ℕ) + x16.size ∧ x18 < (26 : ℕ) + x16.size ∧
          ∀ (x19 : Fin (26 : ℕ) → Bool), w x16 x19 x17 = w x3 x19 x4 ∧ w x16 x19 x18 = w x3 x19 x5) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x3.size = (65 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →       (∀ x8 ∈ x3.gates, x8.inputs.Nodup) →         x3.output = (90 : ℕ) →           x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →             (∀ (x11 x12 : Fin (13 : ℕ)),                 x1 x11 x12 →                   have x14 : Fin (26 : ℕ) → Bool := fun (x14 : Fin (26 : ℕ)) => Decidable.decide (x14 = Fin.castAdd (13 : ℕ) x11 ∨ x14 = Fin.natAdd (13 : ℕ) x12);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x14 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x14 x5 = Bool.true) →               (∀ (x12 : Fin (26 : ℕ) → Bool), Maximal (fun (x13 : Fin (26 : ℕ) → Bool) => ¬x2 x13) x12 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 (if x12 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) → (26 : ℕ) ≤ x4 → (26 : ℕ) ≤ x5 → (∀ x15 < (64 : ℕ), ∃ x17 < (65 : ℕ), x15 < x17 ∧ (26 : ℕ) + x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x17).inputs) → ∃ (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : ℕ) (x18 : ℕ), x16.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x16 ∧ (∀ x19 ∈ x16.gates, x19.inputs.Nodup) ∧ x17 ≠ x18 ∧ x17 < (26 : ℕ) + x16.size ∧ x18 < (26 : ℕ) + x16.size ∧ ∀ (x19 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x16 (26 : ℕ) x19 x17 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x19 x4 ∧ PEqualNP.BlindGate.wireValue x16 (26 : ℕ) x19 x18 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x19 x5) :=
  fun x3 x4 x5 hSz hAO hNodup hOut hG64 h1s hMax h4 h5 hUsed =>
    Or.elim (Nat.lt_or_ge x4 x5)
      (fun hLt => hLeftEarlier x3 x4 x5 ⟨hSz, hAO, hNodup, hOut, hG64, h1s, hMax, h4, h5, hLt, hUsed⟩)
      (fun hGe => hRightEarlier x3 x4 x5 ⟨hSz, hAO, hNodup, hOut, hG64, h1s, hMax, h4, h5, hGe, hUsed⟩)
