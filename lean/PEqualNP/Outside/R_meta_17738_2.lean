import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17738_2
    (hLe :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun a b =>
        a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ));
      have wv := PEqualNP.BlindGate.wireValue;
      have ic := PEqualNP.SplitCount.InConeOrSelf (26 : ℕ);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x13 : ℕ),
        (x4 ≤ x5 ∧ x3.size = (65 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
          (∀ g ∈ x3.gates, g.inputs.Nodup) ∧ x3.output = (90 : ℕ) ∧
          x3.gates[(64 : ℕ)]? = Option.some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [x4, x5]) ∧
          (∀ (a b : Fin (13 : ℕ)), x1 a b →
            have f : Fin (26 : ℕ) → Bool := fun i => Decidable.decide (i = Fin.castAdd (13 : ℕ) a ∨ i = Fin.natAdd (13 : ℕ) b);
            wv x3 (26 : ℕ) f x4 = Bool.true ∧ wv x3 (26 : ℕ) f x5 = Bool.true) ∧
          (∀ (f : Fin (26 : ℕ) → Bool),
            Maximal (fun g => ¬∃ (a b : Fin (13 : ℕ)), x1 a b ∧ g (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ g (Fin.natAdd (13 : ℕ) b) = Bool.true) f →
            wv x3 (26 : ℕ) f (if f (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) ∧
          x13 < (64 : ℕ) ∧ (26 : ℕ) ≤ x4 ∧ (26 : ℕ) ≤ x5 ∧ ic x3 x13 (x4 - (26 : ℕ)) ∧ ic x3 x13 (x5 - (26 : ℕ))) →
        ∃ (c : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
          c.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) c ∧ (∀ g ∈ c.gates, g.inputs.Nodup) ∧
          u ≠ v ∧ u < (26 : ℕ) + c.size ∧ v < (26 : ℕ) + c.size ∧
          ∀ (f : Fin (26 : ℕ) → Bool), wv c (26 : ℕ) f u = wv x3 (26 : ℕ) f x4 ∧ wv c (26 : ℕ) f v = wv x3 (26 : ℕ) f x5)
    (hGt :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun a b =>
        a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ));
      have wv := PEqualNP.BlindGate.wireValue;
      have ic := PEqualNP.SplitCount.InConeOrSelf (26 : ℕ);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x13 : ℕ),
        (x5 < x4 ∧ x3.size = (65 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
          (∀ g ∈ x3.gates, g.inputs.Nodup) ∧ x3.output = (90 : ℕ) ∧
          x3.gates[(64 : ℕ)]? = Option.some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [x4, x5]) ∧
          (∀ (a b : Fin (13 : ℕ)), x1 a b →
            have f : Fin (26 : ℕ) → Bool := fun i => Decidable.decide (i = Fin.castAdd (13 : ℕ) a ∨ i = Fin.natAdd (13 : ℕ) b);
            wv x3 (26 : ℕ) f x4 = Bool.true ∧ wv x3 (26 : ℕ) f x5 = Bool.true) ∧
          (∀ (f : Fin (26 : ℕ) → Bool),
            Maximal (fun g => ¬∃ (a b : Fin (13 : ℕ)), x1 a b ∧ g (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ g (Fin.natAdd (13 : ℕ) b) = Bool.true) f →
            wv x3 (26 : ℕ) f (if f (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) ∧
          x13 < (64 : ℕ) ∧ (26 : ℕ) ≤ x4 ∧ (26 : ℕ) ≤ x5 ∧ ic x3 x13 (x4 - (26 : ℕ)) ∧ ic x3 x13 (x5 - (26 : ℕ))) →
        ∃ (c : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
          c.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) c ∧ (∀ g ∈ c.gates, g.inputs.Nodup) ∧
          u ≠ v ∧ u < (26 : ℕ) + c.size ∧ v < (26 : ℕ) + c.size ∧
          ∀ (f : Fin (26 : ℕ) → Bool), wv c (26 : ℕ) f u = wv x3 (26 : ℕ) f x4 ∧ wv c (26 : ℕ) f v = wv x3 (26 : ℕ) f x5) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x3.size = (65 : ℕ) →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →       (∀ x8 ∈ x3.gates, x8.inputs.Nodup) →         x3.output = (90 : ℕ) →           x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →             (∀ (x11 x12 : Fin (13 : ℕ)),                 x1 x11 x12 →                   have x14 : Fin (26 : ℕ) → Bool := fun (x14 : Fin (26 : ℕ)) => Decidable.decide (x14 = Fin.castAdd (13 : ℕ) x11 ∨ x14 = Fin.natAdd (13 : ℕ) x12);                   PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x14 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x14 x5 = Bool.true) →               (∀ (x12 : Fin (26 : ℕ) → Bool), Maximal (fun (x13 : Fin (26 : ℕ) → Bool) => ¬x2 x13) x12 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 (if x12 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) → (∃ x13 < (64 : ℕ), (26 : ℕ) ≤ x4 ∧ (26 : ℕ) ≤ x5 ∧ PEqualNP.SplitCount.InConeOrSelf (26 : ℕ) x3 x13 (x4 - (26 : ℕ)) ∧ PEqualNP.SplitCount.InConeOrSelf (26 : ℕ) x3 x13 (x5 - (26 : ℕ))) → ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit) (x15 : ℕ) (x16 : ℕ), x14.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x14 ∧ (∀ x17 ∈ x14.gates, x17.inputs.Nodup) ∧ x15 ≠ x16 ∧ x15 < (26 : ℕ) + x14.size ∧ x16 < (26 : ℕ) + x14.size ∧ ∀ (x17 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x14 (26 : ℕ) x17 x15 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x17 x4 ∧ PEqualNP.BlindGate.wireValue x14 (26 : ℕ) x17 x16 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x17 x5) :=
  fun x3 x4 x5 hSize hAO hNodup hOut hG64 hPos hNeg hCone =>
    Exists.elim hCone fun x13 hx13 =>
      Or.elim (Nat.lt_or_ge x5 x4)
        (fun hgt => hGt x3 x4 x5 x13 ⟨hgt, hSize, hAO, hNodup, hOut, hG64, hPos, hNeg, hx13.1, hx13.2.1, hx13.2.2.1, hx13.2.2.2.1, hx13.2.2.2.2⟩)
        (fun hle => hLe x3 x4 x5 x13 ⟨hle, hSize, hAO, hNodup, hOut, hG64, hPos, hNeg, hx13.1, hx13.2.1, hx13.2.2.1, hx13.2.2.2.1, hx13.2.2.2.2⟩)
