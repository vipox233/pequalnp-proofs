import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18548_2
    (hDegTwoHasAndSplit :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (2 : ℕ) ≤ x1.lineDeg (14 : ℕ) {x2} →
        ∃ (x3 x4 x5 : ℕ),
          x1.gates[x3]? = Option.some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [x4, x5]) ∧
          (1 : ℕ) ≤ (x1.lineDegrees (14 : ℕ) {x2}).getD x4 (0 : ℕ) ∧
          (1 : ℕ) ≤ (x1.lineDegrees (14 : ℕ) {x2}).getD x5 (0 : ℕ))
    (hWithAndSplit :
      have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x3)).getD x2 Bool.false;
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) =>
        ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ),
          x2.gates[x3]? = Option.some x4 →
            x4.inputs = [x5, x6] ∨ x4.inputs = [x6, x5] →
              (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or →
                  ∃ (x10 : Fin (7 : ℕ)) (x11 : Fin (7 : ℕ)),
                    x10 ∈ PEqualNP.CircuitLowerBounds.fanoLines x11 ∧
                      have x12 : Fin ((7 : ℕ) + (7 : ℕ)) → Bool := PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x10) (Fin.natAdd (7 : ℕ) x11);
                      x1 x2 x5 x12 = Bool.false ∧ x1 x2 x6 x12 = Bool.true) ∧
                (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin (14 : ℕ) → Bool), Maximal (fun (x11 : Fin (14 : ℕ) → Bool) => x2.eval (List.ofFn x11) = Bool.false) x10 ∧ x1 x2 x5 x10 = Bool.true ∧ x1 x2 x6 x10 = Bool.false);
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (7 : ℕ)),
        (∀ (x6 : ℕ),
          (x6 = ↑x4 ∨ x6 = (7 : ℕ) + ↑x5) →
          PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 →
          (2 : ℕ) ≤ x3.lineDeg (14 : ℕ) {x6} →
          ∃ (x7 x8 x9 : ℕ),
            x3.gates[x7]? = Option.some (PEqualNP.CircuitLowerBounds.Gate.mk PEqualNP.CircuitLowerBounds.GateOp.and [x8, x9]) ∧
            (1 : ℕ) ≤ (x3.lineDegrees (14 : ℕ) {x6}).getD x8 (0 : ℕ) ∧
            (1 : ℕ) ≤ (x3.lineDegrees (14 : ℕ) {x6}).getD x9 (0 : ℕ)) →
        x3.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 →
        (∀ x8 ∈ x3.gates, x8.inputs.Nodup) →
        PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x3 →
        x2 x3 →
        x4 ∈ PEqualNP.CircuitLowerBounds.fanoLines x5 →
        (2 : ℕ) ≤ x3.lineDeg (14 : ℕ) {↑x4} →
        (2 : ℕ) ≤ x3.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x5} →
        False) :
    (have x1 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x3)).getD x2 Bool.false; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate) (x5 x6 : ℕ),     x2.gates[x3]? = Option.some x4 →       x4.inputs = [x5, x6] ∨ x4.inputs = [x6, x5] →         (x4.op = PEqualNP.CircuitLowerBounds.GateOp.or →             ∃ (x10 : Fin (7 : ℕ)) (x11 : Fin (7 : ℕ)),               x10 ∈ PEqualNP.CircuitLowerBounds.fanoLines x11 ∧                 have x12 : Fin ((7 : ℕ) + (7 : ℕ)) → Bool := PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (7 : ℕ) x10) (Fin.natAdd (7 : ℕ) x11);                 x1 x2 x5 x12 = Bool.false ∧ x1 x2 x6 x12 = Bool.true) ∧           (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin (14 : ℕ) → Bool), Maximal (fun (x11 : Fin (14 : ℕ) → Bool) => x2.eval (List.ofFn x11) = Bool.false) x10 ∧ x1 x2 x5 x10 = Bool.true ∧ x1 x2 x6 x10 = Bool.false); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (7 : ℕ)), x3.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x3 → (∀ x8 ∈ x3.gates, x8.inputs.Nodup) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.CircuitLowerBounds.fanoLines x3 → x2 x3 → x4 ∈ PEqualNP.CircuitLowerBounds.fanoLines x5 → (2 : ℕ) ≤ x3.lineDeg (14 : ℕ) {↑x4} → (2 : ℕ) ≤ x3.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x5} → False) := by
  intro x1 x2 x3 x4 x5
  exact @hWithAndSplit x3 x4 x5 (fun v _ => hDegTwoHasAndSplit x3 v)
