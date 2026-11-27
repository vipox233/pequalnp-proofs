import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18689_1
    (hEvalPG23 :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        (∀ (p l : Fin (13 : ℕ)), x1 p l →
          have v : Fin (26 : ℕ) → Bool := fun i => Decidable.decide (i = Fin.castAdd (13 : ℕ) p ∨ i = Fin.natAdd (13 : ℕ) l);
          PEqualNP.BlindGate.wireValue C (26 : ℕ) v a = Bool.true ∧ PEqualNP.BlindGate.wireValue C (26 : ℕ) v b = Bool.true) →
        (∀ (y : Fin (26 : ℕ) → Bool), Maximal (fun z => ¬x2 z) y →
          PEqualNP.BlindGate.wireValue C (26 : ℕ) y (if y (13 : Fin (26 : ℕ)) = Bool.true then a else b) = Bool.false) →
        ∀ (x : Fin (26 : ℕ) → Bool),
          (PEqualNP.BlindGate.wireValue C (26 : ℕ) x a = Bool.true ∧ PEqualNP.BlindGate.wireValue C (26 : ℕ) x b = Bool.true) ↔ x2 x)
    (hShrink65 :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        b < a →
        C.size ≤ (65 : ℕ) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        (∀ g ∈ C.gates, g.inputs.Nodup) →
        C.output = (90 : ℕ) →
        C.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] : PEqualNP.CircuitLowerBounds.Gate } →
        (∀ (x : Fin (26 : ℕ) → Bool),
          (PEqualNP.BlindGate.wireValue C (26 : ℕ) x a = Bool.true ∧ PEqualNP.BlindGate.wireValue C (26 : ℕ) x b = Bool.true) ↔ x2 x) →
        (∀ (y : Fin (26 : ℕ) → Bool), Maximal (fun z => ¬x2 z) y →
          PEqualNP.BlindGate.wireValue C (26 : ℕ) y (if y (13 : Fin (26 : ℕ)) = Bool.true then a else b) = Bool.false) →
        ∃ (C' : PEqualNP.CircuitLowerBounds.Circuit) (idx a' b' : ℕ),
          C'.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) C' ∧ (∀ g ∈ C'.gates, g.inputs.Nodup) ∧
          C'.output = (26 : ℕ) + idx ∧
          C'.gates[idx]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a', b'] : PEqualNP.CircuitLowerBounds.Gate } ∧
          ∀ (x : Fin (26 : ℕ) → Bool),
            PEqualNP.BlindGate.wireValue C' (26 : ℕ) x a' = PEqualNP.BlindGate.wireValue C (26 : ℕ) x a ∧
            PEqualNP.BlindGate.wireValue C' (26 : ℕ) x b' = PEqualNP.BlindGate.wireValue C (26 : ℕ) x b) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x5 < x4 →     (x3.size ≤ (65 : ℕ) ∧         PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧           (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧             x3.output = (90 : ℕ) ∧               x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } ∧                 (∀ (x7 x8 : Fin (13 : ℕ)),                     x1 x7 x8 →                       have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                       PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true) ∧                   ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), x8.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x8 ∧ (∀ x12 ∈ x8.gates, x12.inputs.Nodup) ∧ x8.output = (26 : ℕ) + x9 ∧ x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x4 ∧ PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x5) :=
  fun C a b hlt h =>
    hShrink65 C a b hlt h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
      (hEvalPG23 C a b h.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2)
      h.2.2.2.2.2.2
