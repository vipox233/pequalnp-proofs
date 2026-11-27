import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8067_3
    (hAtOutput :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);
        have x3 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;
        have x4 : ℕ → Prop := fun (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x5 : ℕ → ℕ → Prop := fun (x5 x6 : ℕ) => (14 : ℕ) + x6 = x5 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x6 (x5 - (14 : ℕ));
        have x6 : ℕ → Prop := fun (x6 : ℕ) => x2 x6 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 x6 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false;
        have x7 : ℕ → Prop := fun (x7 : ℕ) => x4 x7 ∧ x6 ((14 : ℕ) + x7) ∧ ∃ (x8 : Fin (2 : ℕ)), x2 (x3 x7 x8) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (x3 x7 ((1 : Fin (2 : ℕ)) - x8)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;
        x1.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (∀ x10 ∈ x1.gates, x10.inputs.Nodup) →
        ∀ (x11 : ℕ),
          x4 x11 →
          (14 : ℕ) + x11 = x1.output →
          x2 ((14 : ℕ) + x11) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true →
          (∀ (x15 : Fin (2 : ℕ)), x6 (x3 x11 x15)) →
          (have x16 : Fin (2 : ℕ) → (Fin (14 : ℕ) → Bool) → Bool := fun (x16 : Fin (2 : ℕ)) => PEqualNP.MetaComplexity.circuitFun (14 : ℕ) (PEqualNP.CircuitMoves.eraseGate (14 : ℕ) x1 x11 (x3 x11 x16));
           (fun (x17 : Fin (14 : ℕ) → Bool) => x16 (0 : Fin (2 : ℕ)) x17 && x16 (1 : Fin (2 : ℕ)) x17) = PEqualNP.ReadTwo.fpl (7 : ℕ) fun (x17 x18 : Fin (7 : ℕ)) => x17 ∈ PEqualNP.CircuitLowerBounds.fanoLines x18) →
          (∀ (x17 : Fin (2 : ℕ)), ∃ (x18 : ℕ), x5 (x3 x11 x17) x18 ∧ x7 x18) →
          ∃ (x18 : ℕ), (x5 (x3 x11 (0 : Fin (2 : ℕ))) x18 ∧ x7 x18) ∧ x5 (x3 x11 (1 : Fin (2 : ℕ))) x18 ∧ x7 x18)
    (hBelowOutput :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);
        have x3 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;
        have x4 : ℕ → Prop := fun (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x5 : ℕ → ℕ → Prop := fun (x5 x6 : ℕ) => (14 : ℕ) + x6 = x5 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x6 (x5 - (14 : ℕ));
        have x6 : ℕ → Prop := fun (x6 : ℕ) => x2 x6 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 x6 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false;
        have x7 : ℕ → Prop := fun (x7 : ℕ) => x4 x7 ∧ x6 ((14 : ℕ) + x7) ∧ ∃ (x8 : Fin (2 : ℕ)), x2 (x3 x7 x8) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (x3 x7 ((1 : Fin (2 : ℕ)) - x8)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;
        x1.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →
        (∀ x10 ∈ x1.gates, x10.inputs.Nodup) →
        ∀ (x11 : ℕ),
          x4 x11 →
          PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x11 (x1.output - (14 : ℕ)) →
          x2 ((14 : ℕ) + x11) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true →
          (∀ (x15 : Fin (2 : ℕ)), x6 (x3 x11 x15)) →
          (have x16 : Fin (2 : ℕ) → (Fin (14 : ℕ) → Bool) → Bool := fun (x16 : Fin (2 : ℕ)) => PEqualNP.MetaComplexity.circuitFun (14 : ℕ) (PEqualNP.CircuitMoves.eraseGate (14 : ℕ) x1 x11 (x3 x11 x16));
           (fun (x17 : Fin (14 : ℕ) → Bool) => x16 (0 : Fin (2 : ℕ)) x17 && x16 (1 : Fin (2 : ℕ)) x17) = PEqualNP.ReadTwo.fpl (7 : ℕ) fun (x17 x18 : Fin (7 : ℕ)) => x17 ∈ PEqualNP.CircuitLowerBounds.fanoLines x18) →
          (∀ (x17 : Fin (2 : ℕ)), ∃ (x18 : ℕ), x5 (x3 x11 x17) x18 ∧ x7 x18) →
          ∃ (x18 : ℕ), (x5 (x3 x11 (0 : Fin (2 : ℕ))) x18 ∧ x7 x18) ∧ x5 (x3 x11 (1 : Fin (2 : ℕ))) x18 ∧ x7 x18) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);   have x3 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;   have x4 : ℕ → Prop := fun (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;   have x5 : ℕ → ℕ → Prop := fun (x5 x6 : ℕ) => (14 : ℕ) + x6 = x5 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x6 (x5 - (14 : ℕ));   have x6 : ℕ → Prop := fun (x6 : ℕ) => x2 x6 (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 x6 (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false;   have x7 : ℕ → Prop := fun (x7 : ℕ) => x4 x7 ∧ x6 ((14 : ℕ) + x7) ∧ ∃ (x8 : Fin (2 : ℕ)), x2 (x3 x7 x8) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (x3 x7 ((1 : Fin (2 : ℕ)) - x8)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x10 ∈ x1.gates, x10.inputs.Nodup) →         ∀ (x11 : ℕ),           x4 x11 →             x5 x1.output x11 →               x2 ((14 : ℕ) + x11) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true →                 (∀ (x15 : Fin (2 : ℕ)), x6 (x3 x11 x15)) →                   (have x16 : Fin (2 : ℕ) → (Fin (14 : ℕ) → Bool) → Bool := fun (x16 : Fin (2 : ℕ)) => PEqualNP.MetaComplexity.circuitFun (14 : ℕ) (PEqualNP.CircuitMoves.eraseGate (14 : ℕ) x1 x11 (x3 x11 x16));                     (fun (x17 : Fin (14 : ℕ) → Bool) => x16 (0 : Fin (2 : ℕ)) x17 && x16 (1 : Fin (2 : ℕ)) x17) = PEqualNP.ReadTwo.fpl (7 : ℕ) fun (x17 x18 : Fin (7 : ℕ)) => x17 ∈ PEqualNP.CircuitLowerBounds.fanoLines x18) →                     (∀ (x17 : Fin (2 : ℕ)), ∃ (x18 : ℕ), x5 (x3 x11 x17) x18 ∧ x7 x18) → ∃ (x18 : ℕ), (x5 (x3 x11 (0 : Fin (2 : ℕ))) x18 ∧ x7 x18) ∧ x5 (x3 x11 (1 : Fin (2 : ℕ))) x18 ∧ x7 x18) :=
  fun x1 hSz hAO hNd x11 hAnd hOut =>
    Or.elim hOut
      (fun hEq => hAtOutput x1 hSz hAO hNd x11 hAnd hEq)
      (fun hIn => hBelowOutput x1 hSz hAO hNd x11 hAnd hIn)
