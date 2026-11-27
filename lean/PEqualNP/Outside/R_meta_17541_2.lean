import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17541_2
    (hOutAnd : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
          x2.size ≤ (63 : ℕ) →
            (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and →
              (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →
                ∃ (x6 : Fin (26 : ℕ)) (x7 : ℕ) (x8 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
                  x8 (0 : ℕ) = x2 ∧
                    PEqualNP.TopForm.IsAO2 (26 : ℕ) (x8 x7) ∧
                      (4 : ℕ) ≤ x7 ∧
                        (x7 = (4 : ℕ) → ∃ (x10 : Fin (26 : ℕ) → Bool), (x8 x7).eval (List.ofFn x10) ≠ (x8 x7).eval (List.ofFn (Function.update x10 x6 Bool.false))) ∧
                          ∀ x9 < x7,
                            have x11 : PEqualNP.CircuitLowerBounds.Circuit := x8 x9;
                            ∃ (x12 : ℕ) (x13 : ℕ),
                              x12 < x11.size ∧
                                x13 < (26 : ℕ) + x12 ∧
                                  x8 (x9 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x11 x12 x13 ∧
                                    ((∀ (x14 : Fin (26 : ℕ) → Bool),
                                        have x15 : List Bool := x11.wires (List.ofFn (Function.update x14 x6 Bool.false));
                                        x15.getD ((26 : ℕ) + x12) Bool.false = x15.getD x13 Bool.false) ∨
                                      x11.output ≠ (26 : ℕ) + x12 ∧ ∀ x14 ∈ List.drop (x12 + (1 : ℕ)) x11.gates, (26 : ℕ) + x12 ∉ x14.inputs))
    (hOutNotAnd : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
          x2.size ≤ (63 : ℕ) →
            (PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and →
              (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →
                ∃ (x6 : Fin (26 : ℕ)) (x7 : ℕ) (x8 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),
                  x8 (0 : ℕ) = x2 ∧
                    PEqualNP.TopForm.IsAO2 (26 : ℕ) (x8 x7) ∧
                      (4 : ℕ) ≤ x7 ∧
                        (x7 = (4 : ℕ) → ∃ (x10 : Fin (26 : ℕ) → Bool), (x8 x7).eval (List.ofFn x10) ≠ (x8 x7).eval (List.ofFn (Function.update x10 x6 Bool.false))) ∧
                          ∀ x9 < x7,
                            have x11 : PEqualNP.CircuitLowerBounds.Circuit := x8 x9;
                            ∃ (x12 : ℕ) (x13 : ℕ),
                              x12 < x11.size ∧
                                x13 < (26 : ℕ) + x12 ∧
                                  x8 (x9 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x11 x12 x13 ∧
                                    ((∀ (x14 : Fin (26 : ℕ) → Bool),
                                        have x15 : List Bool := x11.wires (List.ofFn (Function.update x14 x6 Bool.false));
                                        x15.getD ((26 : ℕ) + x12) Bool.false = x15.getD x13 Bool.false) ∨
                                      x11.output ≠ (26 : ℕ) + x12 ∧ ∀ x14 ∈ List.drop (x12 + (1 : ℕ)) x11.gates, (26 : ℕ) + x12 ∉ x14.inputs)) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     x2.size ≤ (63 : ℕ) →       (∀ (x5 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), x1 x6 x7 ∧ x5 (Fin.castAdd (13 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x7) = Bool.true) →         ∃ (x6 : Fin (26 : ℕ)) (x7 : ℕ) (x8 : ℕ → PEqualNP.CircuitLowerBounds.Circuit),           x8 (0 : ℕ) = x2 ∧             PEqualNP.TopForm.IsAO2 (26 : ℕ) (x8 x7) ∧               (4 : ℕ) ≤ x7 ∧                 (x7 = (4 : ℕ) → ∃ (x10 : Fin (26 : ℕ) → Bool), (x8 x7).eval (List.ofFn x10) ≠ (x8 x7).eval (List.ofFn (Function.update x10 x6 Bool.false))) ∧                   ∀ x9 < x7,                     have x11 : PEqualNP.CircuitLowerBounds.Circuit := x8 x9;                     ∃ (x12 : ℕ) (x13 : ℕ),                       x12 < x11.size ∧                         x13 < (26 : ℕ) + x12 ∧                           x8 (x9 + (1 : ℕ)) = PEqualNP.CircuitMoves.eraseGate (26 : ℕ) x11 x12 x13 ∧                             ((∀ (x14 : Fin (26 : ℕ) → Bool),                                 have x15 : List Bool := x11.wires (List.ofFn (Function.update x14 x6 Bool.false));                                 x15.getD ((26 : ℕ) + x12) Bool.false = x15.getD x13 Bool.false) ∨                               x11.output ≠ (26 : ℕ) + x12 ∧ ∀ x14 ∈ List.drop (x12 + (1 : ℕ)) x11.gates, (26 : ℕ) + x12 ∉ x14.inputs)) :=
  fun x2 hao hsz hspec =>
    Or.elim (Classical.em ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 (x2.output - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and))
      (fun ha => hOutAnd x2 hao hsz ha hspec)
      (fun hna => hOutNotAnd x2 hao hsz hna hspec)
