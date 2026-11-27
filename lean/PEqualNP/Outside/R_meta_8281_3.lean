import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8281_3
    (hOp0 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x11 x12 x19 x20 x29 : ℕ),
        have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;
        have x9 : ℕ → Prop := fun (x9 : ℕ) => (14 : ℕ) + x9 = x1.output ∨ x8 x9 (x1.output - (14 : ℕ));
        have x10 : Fin (14 : ℕ) → ℕ → Prop := fun (x10 : Fin (14 : ℕ)) (x11 : ℕ) => x7 x11 ∧ x9 x11 ∧ x6 ((14 : ℕ) + x11) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), x6 (PEqualNP.TopForm.opnd x1 x11 x12) x10 x10 = Bool.false;
        (x1.size ≤ (27 : ℕ) ∧
         PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
         (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧
         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) ∧
         x11 ≠ x12 ∧ ¬x8 x11 x12 ∧ ¬x8 x12 x11 ∧ x10 (0 : Fin (14 : ℕ)) x11 ∧ x10 (7 : Fin (14 : ℕ)) x12 ∧
         x6 ((14 : ℕ) + x11) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧
         (x19 = x11 ∨ x8 x11 x19) ∧
         PEqualNP.TopForm.opnd x1 x20 (0 : Fin (2 : ℕ)) = (14 : ℕ) + x19 ∧ x7 x20 ∧ x9 x20 ∧
         x6 ((14 : ℕ) + x19) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧
         x6 (PEqualNP.TopForm.opnd x1 x20 (1 : Fin (2 : ℕ))) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧
         x6 (PEqualNP.TopForm.opnd x1 x20 (1 : Fin (2 : ℕ))) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧
         x8 x20 x29 ∧ x9 x29 ∧ ¬x7 x29 ∧ x6 ((14 : ℕ) + x29) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true) →
        False)
    (hOp1 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x11 x12 x19 x20 x29 : ℕ),
        have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;
        have x9 : ℕ → Prop := fun (x9 : ℕ) => (14 : ℕ) + x9 = x1.output ∨ x8 x9 (x1.output - (14 : ℕ));
        have x10 : Fin (14 : ℕ) → ℕ → Prop := fun (x10 : Fin (14 : ℕ)) (x11 : ℕ) => x7 x11 ∧ x9 x11 ∧ x6 ((14 : ℕ) + x11) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), x6 (PEqualNP.TopForm.opnd x1 x11 x12) x10 x10 = Bool.false;
        (x1.size ≤ (27 : ℕ) ∧
         PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
         (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧
         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) ∧
         x11 ≠ x12 ∧ ¬x8 x11 x12 ∧ ¬x8 x12 x11 ∧ x10 (0 : Fin (14 : ℕ)) x11 ∧ x10 (7 : Fin (14 : ℕ)) x12 ∧
         x6 ((14 : ℕ) + x11) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧
         (x19 = x11 ∨ x8 x11 x19) ∧
         PEqualNP.TopForm.opnd x1 x20 (1 : Fin (2 : ℕ)) = (14 : ℕ) + x19 ∧ x7 x20 ∧ x9 x20 ∧
         x6 ((14 : ℕ) + x19) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧
         x6 (PEqualNP.TopForm.opnd x1 x20 (0 : Fin (2 : ℕ))) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧
         x6 (PEqualNP.TopForm.opnd x1 x20 (0 : Fin (2 : ℕ))) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧
         x8 x20 x29 ∧ x9 x29 ∧ ¬x7 x29 ∧ x6 ((14 : ℕ) + x29) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true) →
        False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (∀ (x5 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) →           have x6 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x6 : ℕ) (x7 x8 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8);           have x7 : ℕ → Prop := fun (x7 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and;           have x8 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;           have x9 : ℕ → Prop := fun (x9 : ℕ) => (14 : ℕ) + x9 = x1.output ∨ x8 x9 (x1.output - (14 : ℕ));           have x10 : Fin (14 : ℕ) → ℕ → Prop := fun (x10 : Fin (14 : ℕ)) (x11 : ℕ) => x7 x11 ∧ x9 x11 ∧ x6 ((14 : ℕ) + x11) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), x6 (PEqualNP.TopForm.opnd x1 x11 x12) x10 x10 = Bool.false;           ∀ (x11 x12 : ℕ), x11 ≠ x12 → ¬x8 x11 x12 → ¬x8 x12 x11 → x10 (0 : Fin (14 : ℕ)) x11 → x10 (7 : Fin (14 : ℕ)) x12 → x6 ((14 : ℕ) + x11) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → ∀ (x19 x20 : ℕ) (x21 : Fin (2 : ℕ)), x19 = x11 ∨ x8 x11 x19 → PEqualNP.TopForm.opnd x1 x20 x21 = (14 : ℕ) + x19 → x7 x20 → x9 x20 → x6 ((14 : ℕ) + x19) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → x6 (PEqualNP.TopForm.opnd x1 x20 ((1 : Fin (2 : ℕ)) - x21)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false → x6 (PEqualNP.TopForm.opnd x1 x20 ((1 : Fin (2 : ℕ)) - x21)) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false → (∃ (x29 : ℕ), x8 x20 x29 ∧ x9 x29 ∧ ¬x7 x29 ∧ x6 ((14 : ℕ) + x29) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true) → False) :=
  fun x1 hSz hAO hNodup hEval x11 x12 hNe hNC1 hNC2 h10a h10b h11T x19 x20 x21 hCone =>
    Fin.cases
      (motive := fun (i : Fin (2 : ℕ)) =>
        PEqualNP.TopForm.opnd x1 x20 i = (14 : ℕ) + x19 →
        (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x20).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ((14 : ℕ) + x20 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x20 (x1.output - (14 : ℕ))) →
        PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 ((14 : ℕ) + x19) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true →
        PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x20 ((1 : Fin (2 : ℕ)) - i)) (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false →
        PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x20 ((1 : Fin (2 : ℕ)) - i)) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.false →
        (∃ (x29 : ℕ), PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x20 x29 ∧ ((14 : ℕ) + x29 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x29 (x1.output - (14 : ℕ))) ∧ ¬(PEqualNP.MetaComplexity.NestedCover.gateAt x1 x29).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 ((14 : ℕ) + x29) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ))) = Bool.true) →
        False)
      (fun hOp hAnd hOut hT hF1 hF2 hEx => hEx.elim fun x29 hx29 =>
        hOp0 x1 x11 x12 x19 x20 x29 ⟨hSz, hAO, hNodup, hEval, hNe, hNC1, hNC2, h10a, h10b, h11T, hCone, hOp, hAnd, hOut, hT, hF1, hF2, hx29.1, hx29.2.1, hx29.2.2.1, hx29.2.2.2⟩)
      (Fin.cases
        (fun hOp hAnd hOut hT hF1 hF2 hEx => hEx.elim fun x29 hx29 =>
          hOp1 x1 x11 x12 x19 x20 x29 ⟨hSz, hAO, hNodup, hEval, hNe, hNC1, hNC2, h10a, h10b, h11T, hCone, hOp, hAnd, hOut, hT, hF1, hF2, hx29.1, hx29.2.1, hx29.2.2.1, hx29.2.2.2⟩)
        (fun k => Fin.elim0 k))
      x21
