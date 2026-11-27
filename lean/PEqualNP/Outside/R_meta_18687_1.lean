import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18687_1
    (hElimMaximal :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun x1 x2 => x1 = x2 ∨ x1 = x2 + 1 ∨ x1 = x2 + 3 ∨ x1 = x2 + 9;
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun x2 => ∃ (x3 x4 : Fin 13), x1 x3 x4 ∧ x2 (Fin.castAdd 13 x3) = true ∧ x2 (Fin.natAdd 13 x4) = true;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        PEqualNP.TopForm.IsAO2 26 C →
        (∀ x : Fin 26 → Bool, Maximal (fun y => ¬x2 y) x → PEqualNP.BlindGate.wireValue C 26 x (if x 13 = true then u else v) = false) →
        ∀ x : Fin 26 → Bool, ¬x2 x →
          (x 13 = true → PEqualNP.BlindGate.wireValue C 26 x u = false) ∧
          ((x 0 = true ∨ x 1 = true ∨ x 3 = true ∨ x 9 = true) → PEqualNP.BlindGate.wireValue C 26 x v = false))
    (hShrinkNoMax :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun x1 x2 => x1 = x2 ∨ x1 = x2 + 1 ∨ x1 = x2 + 3 ∨ x1 = x2 + 9;
      have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun x2 => ∃ (x3 x4 : Fin 13), x1 x3 x4 ∧ x2 (Fin.castAdd 13 x3) = true ∧ x2 (Fin.natAdd 13 x4) = true;
      have ok : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → ℕ → ℕ → Prop := fun C m k a b =>
        C.size ≤ m ∧ PEqualNP.TopForm.IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        C.output = 26 + k ∧ C.gates[k]? = some { op := .and, inputs := [a, b] };
      have wv : PEqualNP.CircuitLowerBounds.Circuit → (Fin 26 → Bool) → ℕ → Bool := fun C x w =>
        PEqualNP.BlindGate.wireValue C 26 x w;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),
        x4 < x5 →
        ok x3 65 64 x4 x5 →
        (∀ (a b : Fin 13), x1 a b →
          have e : Fin 26 → Bool := fun z => decide (z = Fin.castAdd 13 a ∨ z = Fin.natAdd 13 b);
          wv x3 e x4 = true ∧ wv x3 e x5 = true) →
        (∀ x : Fin 26 → Bool, ¬x2 x →
          (x 13 = true → wv x3 x x4 = false) ∧
          ((x 0 = true ∨ x 1 = true ∨ x 3 = true ∨ x 9 = true) → wv x3 x x5 = false)) →
        ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 x10 x11 : ℕ),
          ok x8 64 x9 x10 x11 ∧
          ∀ x : Fin 26 → Bool, wv x8 x x10 = wv x3 x x4 ∧ wv x8 x x11 = wv x3 x x5) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x4 < x5 →     (x3.size ≤ (65 : ℕ) ∧         PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧           (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧             x3.output = (90 : ℕ) ∧               x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } ∧                 (∀ (x7 x8 : Fin (13 : ℕ)),                     x1 x7 x8 →                       have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                       PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true) ∧                   ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x4 else x5) = Bool.false) →       ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), x8.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x8 ∧ (∀ x12 ∈ x8.gates, x12.inputs.Nodup) ∧ x8.output = (26 : ℕ) + x9 ∧ x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x4 ∧ PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x5) :=
  fun x3 x4 x5 hlt h =>
    Exists.elim
      (hShrinkNoMax x3 x4 x5 hlt
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
        h.2.2.2.2.2.1
        (hElimMaximal x3 x4 x5 h.2.1 h.2.2.2.2.2.2))
      fun x8 h8 =>
      Exists.elim h8 fun x9 h9 =>
      Exists.elim h9 fun x10 h10 =>
      Exists.elim h10 fun x11 h11 =>
        ⟨x8, x9, x10, x11, h11.1.1, h11.1.2.1, h11.1.2.2.1, h11.1.2.2.2.1, h11.1.2.2.2.2, h11.2⟩
