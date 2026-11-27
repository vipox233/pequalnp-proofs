import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8361_2
    (hLeftBeforeRight :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (x1.size ≤ (27 : ℕ) ∧ x1.output + (1 : ℕ) = (14 : ℕ) + x1.size ∧
         PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧
         (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔
           ∃ (x7 x8 : Fin (7 : ℕ)),
             (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧
             x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true)) →
        have wv : ℕ → (Fin (14 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1;
        have x7 : ℕ → Bool := fun w => wv w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x8 : ℕ → Bool := fun w => wv w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));
        have x9 : ℕ → Bool := fun w => wv w (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;
        have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;
        have x12 : ℕ → Prop := fun g =>
          (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x7 ((14 : ℕ) + g) = Bool.true ∧ x8 ((14 : ℕ) + g) = Bool.false ∧ x9 ((14 : ℕ) + g) = Bool.false;
        have x13 : ℕ → Prop := fun g =>
          x12 g ∧ ∀ (i : Fin (2 : ℕ)), x8 (x10 g i) = Bool.true ∨ x9 (x10 g i) = Bool.true;
        ∀ (x14 x15 x25 x26 : ℕ),
          (x14 < x15 ∧ ¬x11 x14 x15 ∧ ¬x11 x15 x14 ∧
           x11 x14 (x1.size - (1 : ℕ)) ∧ x11 x15 (x1.size - (1 : ℕ)) ∧
           x12 x14 ∧ x12 x15 ∧
           (∀ i : Fin (2 : ℕ), x8 (x10 x14 i) = Bool.false) ∧
           (∀ i : Fin (2 : ℕ), x9 (x10 x15 i) = Bool.false) ∧
           x25 < x26 ∧ ¬x11 x25 x26 ∧ ¬x11 x26 x25 ∧ x13 x25 ∧ x13 x26 ∧ x11 x25 x14 ∧ x11 x26 x15) →
          False)
    (hRightBeforeLeft :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        (x1.size ≤ (27 : ℕ) ∧ x1.output + (1 : ℕ) = (14 : ℕ) + x1.size ∧
         PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧
         (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔
           ∃ (x7 x8 : Fin (7 : ℕ)),
             (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧
             x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true)) →
        have wv : ℕ → (Fin (14 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1;
        have x7 : ℕ → Bool := fun w => wv w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x8 : ℕ → Bool := fun w => wv w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));
        have x9 : ℕ → Bool := fun w => wv w (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;
        have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;
        have x12 : ℕ → Prop := fun g =>
          (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x7 ((14 : ℕ) + g) = Bool.true ∧ x8 ((14 : ℕ) + g) = Bool.false ∧ x9 ((14 : ℕ) + g) = Bool.false;
        have x13 : ℕ → Prop := fun g =>
          x12 g ∧ ∀ (i : Fin (2 : ℕ)), x8 (x10 g i) = Bool.true ∨ x9 (x10 g i) = Bool.true;
        ∀ (x14 x15 x25 x26 : ℕ),
          (x14 < x15 ∧ ¬x11 x14 x15 ∧ ¬x11 x15 x14 ∧
           x11 x14 (x1.size - (1 : ℕ)) ∧ x11 x15 (x1.size - (1 : ℕ)) ∧
           x12 x14 ∧ x12 x15 ∧
           (∀ i : Fin (2 : ℕ), x8 (x10 x14 i) = Bool.false) ∧
           (∀ i : Fin (2 : ℕ), x9 (x10 x15 i) = Bool.false) ∧
           x26 < x25 ∧ ¬x11 x25 x26 ∧ ¬x11 x26 x25 ∧ x13 x25 ∧ x13 x26 ∧ x11 x25 x14 ∧ x11 x26 x15) →
          False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     x1.output + (1 : ℕ) = (14 : ℕ) + x1.size →       PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             have x7 : ℕ → Bool := fun (x7 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x7 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));             have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x8 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));             have x9 : ℕ → Bool := fun (x9 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x9 (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));             have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;             have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;             have x12 : ℕ → Prop := fun (x12 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x7 ((14 : ℕ) + x12) = Bool.true ∧ x8 ((14 : ℕ) + x12) = Bool.false ∧ x9 ((14 : ℕ) + x12) = Bool.false;             have x13 : ℕ → Prop := fun (x13 : ℕ) => x12 x13 ∧ ∀ (x14 : Fin (2 : ℕ)), x8 (x10 x13 x14) = Bool.true ∨ x9 (x10 x13 x14) = Bool.true;             ∀ (x14 x15 : ℕ), x14 < x15 → ¬x11 x14 x15 → ¬x11 x15 x14 → x11 x14 (x1.size - (1 : ℕ)) → x11 x15 (x1.size - (1 : ℕ)) → x12 x14 → x12 x15 → (∀ (x23 : Fin (2 : ℕ)), x8 (x10 x14 x23) = Bool.false) → (∀ (x24 : Fin (2 : ℕ)), x9 (x10 x15 x24) = Bool.false) → (∃ (x25 : ℕ) (x26 : ℕ), x25 ≠ x26 ∧ ¬x11 x25 x26 ∧ ¬x11 x26 x25 ∧ x13 x25 ∧ x13 x26 ∧ x11 x25 x14 ∧ x11 x26 x15) → False) :=
  fun x1 hSz hOut hAO hNodup hEval x14 x15 h1415 hN1415 hN1514 hC14 hC15 h12_14 h12_15 hOp14 hOp15 hEx =>
    Exists.elim hEx fun x25 hEx2 =>
      Exists.elim hEx2 fun x26 hP =>
        Or.elim (Nat.lt_or_gt_of_ne hP.1)
          (fun hLt =>
            hLeftBeforeRight x1 ⟨hSz, hOut, hAO, hNodup, hEval⟩ x14 x15 x25 x26
              ⟨h1415, hN1415, hN1514, hC14, hC15, h12_14, h12_15, hOp14, hOp15,
               hLt, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.2.2.2.2⟩)
          (fun hGt =>
            hRightBeforeLeft x1 ⟨hSz, hOut, hAO, hNodup, hEval⟩ x14 x15 x25 x26
              ⟨h1415, hN1415, hN1514, hC14, hC15, h12_14, h12_15, hOp14, hOp15,
               hGt, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1, hP.2.2.2.2.2.2⟩)
