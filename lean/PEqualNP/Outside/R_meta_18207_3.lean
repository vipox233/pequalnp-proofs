import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18207_3
    (hSize63False :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x13 x14 : ℕ),
        have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = x7)) x6 x7;
        have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);
        have x10 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x10 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x10 - (26 : ℕ));
        have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) =>
          have x13 : PEqualNP.CircuitLowerBounds.Gate := x10 x12;
          have x14 : ℕ := x13.inputs.getD (0 : ℕ) (0 : ℕ);
          (26 : ℕ) ≤ x12 ∧ x11 ∈ x13.inputs ∧ (x13.op.eval [Bool.false, Bool.true] = Bool.false ∨ x11 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x13.inputs.getD (1 : ℕ) (0 : ℕ));
        have x12 : ℕ → ℕ → ℕ → Prop := fun (x12 x13 x14 : ℕ) =>
          have x15 : Set ℕ := {x15 : ℕ | x9 {x12} x15 = Bool.true ∧ x9 {x13} x15 = Bool.false};
          have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x16 ∈ (x10 x17).inputs ∧ x16 ∈ x15 ∧ x17 ∈ x15;
          PEqualNP.ReadTwo.isAnd x1 x14 ∧ Relation.ReflTransGen x11 ((26 : ℕ) + x14) x1.output ∧ ∀ x17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x14).inputs, x17 ∈ x15 ∧ Relation.ReflTransGen x16 x12 x17;
        (x1.size = (63 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
          (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 = PEqualNP.ReadTwo.fpl (13 : ℕ) (fun (x5 x6 : Fin (13 : ℕ)) => ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ∧
          x6 (0 : ℕ) (13 : ℕ) = Bool.false ∧
          x6 (13 : ℕ) (0 : ℕ) = Bool.false ∧
          x12 (0 : ℕ) (13 : ℕ) x13 ∧
          x12 (13 : ℕ) (0 : ℕ) x14) →
        False)
    (hSize64False :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x13 x14 : ℕ),
        have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = x7)) x6 x7;
        have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);
        have x10 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x10 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x10 - (26 : ℕ));
        have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) =>
          have x13 : PEqualNP.CircuitLowerBounds.Gate := x10 x12;
          have x14 : ℕ := x13.inputs.getD (0 : ℕ) (0 : ℕ);
          (26 : ℕ) ≤ x12 ∧ x11 ∈ x13.inputs ∧ (x13.op.eval [Bool.false, Bool.true] = Bool.false ∨ x11 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x13.inputs.getD (1 : ℕ) (0 : ℕ));
        have x12 : ℕ → ℕ → ℕ → Prop := fun (x12 x13 x14 : ℕ) =>
          have x15 : Set ℕ := {x15 : ℕ | x9 {x12} x15 = Bool.true ∧ x9 {x13} x15 = Bool.false};
          have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x16 ∈ (x10 x17).inputs ∧ x16 ∈ x15 ∧ x17 ∈ x15;
          PEqualNP.ReadTwo.isAnd x1 x14 ∧ Relation.ReflTransGen x11 ((26 : ℕ) + x14) x1.output ∧ ∀ x17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x14).inputs, x17 ∈ x15 ∧ Relation.ReflTransGen x16 x12 x17;
        (x1.size = (64 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
          (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 = PEqualNP.ReadTwo.fpl (13 : ℕ) (fun (x5 x6 : Fin (13 : ℕ)) => ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) ∧
          x6 (0 : ℕ) (13 : ℕ) = Bool.false ∧
          x6 (13 : ℕ) (0 : ℕ) = Bool.false ∧
          x12 (0 : ℕ) (13 : ℕ) x13 ∧
          x12 (13 : ℕ) (0 : ℕ) x14) →
        False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) →         (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x1 = PEqualNP.ReadTwo.fpl (13 : ℕ) fun (x5 x6 : Fin (13 : ℕ)) => ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →           have x6 : ℕ → ℕ → Bool := fun (x6 x7 : ℕ) => PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = x7)) x6 x7;           x6 (0 : ℕ) (13 : ℕ) = Bool.false →             x6 (13 : ℕ) (0 : ℕ) = Bool.false →               have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);               have x10 : ℕ → PEqualNP.CircuitLowerBounds.Gate := fun (x10 : ℕ) => PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x10 - (26 : ℕ));               have x11 : ℕ → ℕ → Prop := fun (x11 x12 : ℕ) =>                 have x13 : PEqualNP.CircuitLowerBounds.Gate := x10 x12;                 have x14 : ℕ := x13.inputs.getD (0 : ℕ) (0 : ℕ);                 (26 : ℕ) ≤ x12 ∧ x11 ∈ x13.inputs ∧ (x13.op.eval [Bool.false, Bool.true] = Bool.false ∨ x11 = if x9 {(0 : ℕ), (13 : ℕ)} x14 = Bool.true then x14 else x13.inputs.getD (1 : ℕ) (0 : ℕ));               have x12 : ℕ → ℕ → ℕ → Prop := fun (x12 x13 x14 : ℕ) =>                 have x15 : Set ℕ := {x15 : ℕ | x9 {x12} x15 = Bool.true ∧ x9 {x13} x15 = Bool.false};                 have x16 : ℕ → ℕ → Prop := fun (x16 x17 : ℕ) => (26 : ℕ) ≤ x17 ∧ x16 ∈ (x10 x17).inputs ∧ x16 ∈ x15 ∧ x17 ∈ x15;                 PEqualNP.ReadTwo.isAnd x1 x14 ∧ Relation.ReflTransGen x11 ((26 : ℕ) + x14) x1.output ∧ ∀ x17 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x14).inputs, x17 ∈ x15 ∧ Relation.ReflTransGen x16 x12 x17;               (∃ (x13 : ℕ), x12 (0 : ℕ) (13 : ℕ) x13) → (∃ (x14 : ℕ), x12 (13 : ℕ) (0 : ℕ) x14) → (65 : ℕ) ≤ x1.size) :=
  fun x1 h63 hAO hNd hFun hL1 hL2 hE1 hE2 =>
    Or.elim (Nat.lt_or_ge x1.size (65 : ℕ))
      (fun hLt65 =>
        Exists.elim hE1 fun x13 hx13 =>
        Exists.elim hE2 fun x14 hx14 =>
          False.elim
            (Or.elim (Nat.eq_or_lt_of_le h63)
              (fun hEq63 => hSize63False x1 x13 x14 ⟨hEq63.symm, hAO, hNd, hFun, hL1, hL2, hx13, hx14⟩)
              (fun hGt63 => hSize64False x1 x13 x14 ⟨Nat.le_antisymm (Nat.le_of_lt_succ hLt65) hGt63, hAO, hNd, hFun, hL1, hL2, hx13, hx14⟩)))
      id
