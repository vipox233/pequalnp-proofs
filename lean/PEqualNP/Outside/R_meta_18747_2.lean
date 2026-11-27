import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18747_2
    (hCircuitExplicit :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ))));
      ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        x3.size ≤ (64 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
        (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧
        (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧
        (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧
        ∃ (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),
          have u : ℕ → List Bool := fun k => x3.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (↑x8 = k));
          x3.output = (26 : ℕ) + x4 ∧
          x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧
          (u (0 : ℕ)).getD x5 Bool.false = Bool.false ∧ (u (0 : ℕ)).getD x6 Bool.false = Bool.false ∧
          (u (13 : ℕ)).getD x5 Bool.false = Bool.false ∧ (u (13 : ℕ)).getD x6 Bool.false = Bool.false)
    (hBoolCombine :
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),
        have u : ℕ → List Bool := fun k => x3.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (↑x8 = k));
        ((u (0 : ℕ)).getD x5 Bool.false = Bool.false ∧ (u (0 : ℕ)).getD x6 Bool.false = Bool.false ∧
         (u (13 : ℕ)).getD x5 Bool.false = Bool.false ∧ (u (13 : ℕ)).getD x6 Bool.false = Bool.false) →
        ∀ (x7 : Bool),
          have x8 : List Bool := x3.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (↑x8 = if x7 = Bool.true then (13 : ℕ) else (0 : ℕ)));
          x8.getD x5 Bool.false = Bool.false ∧ x8.getD x6 Bool.false = Bool.false) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∃ (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),               x3.output = (26 : ℕ) + x4 ∧                 x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧                   ∀ (x7 : Bool),                     have x8 : List Bool := x3.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (↑x8 = if x7 = Bool.true then (13 : ℕ) else (0 : ℕ)));                     x8.getD x5 Bool.false = Bool.false ∧ x8.getD x6 Bool.false = Bool.false) :=
  Exists.elim hCircuitExplicit fun x3 hP =>
    ⟨x3, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1,
      Exists.elim hP.2.2.2.2.2 fun x4 h4 =>
        Exists.elim h4 fun x5 h5 =>
          Exists.elim h5 fun x6 h6 =>
            ⟨x4, x5, x6, h6.1, h6.2.1, hBoolCombine x3 x5 x6 h6.2.2⟩⟩
