import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18276_2
    (hZeroThirteen :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        ((63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧
         (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔
           ∃ (x7 x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧
             x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) ∧
         PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false ∧
         PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false) →
        have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);
        have x10 : ℕ → List ℕ := fun (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs;
        have x11 : ℕ → ℕ → Prop := Relation.ReflTransGen fun (x11 x12 : ℕ) => ∃ (x13 : ℕ), x12 = (26 : ℕ) + x13 ∧ x11 ∈ x10 x13;
        have x12 : ℕ → Prop := PEqualNP.ReadTwo.isAnd x1;
        ∀ (a b c : ℕ),
          (a ≠ b ∧ a < c ∧ b ≠ c ∧ x11 ((26 : ℕ) + a) ((26 : ℕ) + c) ∧ x11 ((26 : ℕ) + c) x1.output ∧ x11 ((26 : ℕ) + b) x1.output ∧
           x12 a ∧ x12 b ∧ x12 c ∧ x9 {(0 : ℕ)} ((26 : ℕ) + a) = Bool.true ∧ x9 {(13 : ℕ)} ((26 : ℕ) + b) = Bool.false ∧
           (∀ w ∈ x10 a, x9 {(0 : ℕ), (13 : ℕ)} w = Bool.true ∧ x9 {(13 : ℕ)} w = Bool.false) ∧
           (∀ w ∈ x10 b, x9 {(0 : ℕ), (13 : ℕ)} w = Bool.true ∧ x9 {(0 : ℕ)} w = Bool.false) ∧
           x9 {(0 : ℕ), (13 : ℕ)} ((26 : ℕ) + c) = Bool.true ∧
           (∃ w ∈ x10 c, x9 {(0 : ℕ)} w = Bool.true) ∧ ∃ w ∈ x10 c, x9 {(0 : ℕ)} w = Bool.false) → False)
    (hThirteenZero :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        ((63 : ℕ) ≤ x1.size ∧ x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧
         (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔
           ∃ (x7 x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧
             x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) ∧
         PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false ∧
         PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false) →
        have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);
        have x10 : ℕ → List ℕ := fun (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs;
        have x11 : ℕ → ℕ → Prop := Relation.ReflTransGen fun (x11 x12 : ℕ) => ∃ (x13 : ℕ), x12 = (26 : ℕ) + x13 ∧ x11 ∈ x10 x13;
        have x12 : ℕ → Prop := PEqualNP.ReadTwo.isAnd x1;
        ∀ (a b c : ℕ),
          (a ≠ b ∧ a < c ∧ b ≠ c ∧ x11 ((26 : ℕ) + a) ((26 : ℕ) + c) ∧ x11 ((26 : ℕ) + c) x1.output ∧ x11 ((26 : ℕ) + b) x1.output ∧
           x12 a ∧ x12 b ∧ x12 c ∧ x9 {(13 : ℕ)} ((26 : ℕ) + a) = Bool.true ∧ x9 {(0 : ℕ)} ((26 : ℕ) + b) = Bool.false ∧
           (∀ w ∈ x10 a, x9 {(0 : ℕ), (13 : ℕ)} w = Bool.true ∧ x9 {(0 : ℕ)} w = Bool.false) ∧
           (∀ w ∈ x10 b, x9 {(0 : ℕ), (13 : ℕ)} w = Bool.true ∧ x9 {(13 : ℕ)} w = Bool.false) ∧
           x9 {(0 : ℕ), (13 : ℕ)} ((26 : ℕ) + c) = Bool.true ∧
           (∃ w ∈ x10 c, x9 {(13 : ℕ)} w = Bool.true) ∧ ∃ w ∈ x10 c, x9 {(13 : ℕ)} w = Bool.false) → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   (63 : ℕ) ≤ x1.size →     x1.size ≤ (64 : ℕ) →       PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ))) ∧ x6 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (13 : ℕ) x8) = Bool.true) →             PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x7 : ℕ) => Decidable.decide (x7 = (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false →               PEqualNP.ReadK.lineSingle x1 (26 : ℕ) (fun (x8 : ℕ) => Decidable.decide (x8 = (0 : ℕ))) (13 : ℕ) (0 : ℕ) = Bool.false →                 have x9 : Finset ℕ → ℕ → Bool := fun (x9 : Finset ℕ) => PEqualNP.ReadTwo.wval x1 (PEqualNP.ReadTwo.indW (26 : ℕ) x9);                 have x10 : ℕ → List ℕ := fun (x10 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).inputs;                 have x11 : ℕ → ℕ → Prop := Relation.ReflTransGen fun (x11 x12 : ℕ) => ∃ (x13 : ℕ), x12 = (26 : ℕ) + x13 ∧ x11 ∈ x10 x13;                 have x12 : ℕ → Prop := PEqualNP.ReadTwo.isAnd x1;                 ∀ (x13 x14 : ℕ), x13 = (0 : ℕ) ∧ x14 = (13 : ℕ) ∨ x13 = (13 : ℕ) ∧ x14 = (0 : ℕ) → ¬∃ (x16 : ℕ) (x17 : ℕ) (x18 : ℕ), x16 ≠ x17 ∧ x16 < x18 ∧ x17 ≠ x18 ∧ x11 ((26 : ℕ) + x16) ((26 : ℕ) + x18) ∧ x11 ((26 : ℕ) + x18) x1.output ∧ x11 ((26 : ℕ) + x17) x1.output ∧ x12 x16 ∧ x12 x17 ∧ x12 x18 ∧ x9 {x13} ((26 : ℕ) + x16) = Bool.true ∧ x9 {x14} ((26 : ℕ) + x17) = Bool.false ∧ (∀ x19 ∈ x10 x16, x9 {(0 : ℕ), (13 : ℕ)} x19 = Bool.true ∧ x9 {x14} x19 = Bool.false) ∧ (∀ x19 ∈ x10 x17, x9 {(0 : ℕ), (13 : ℕ)} x19 = Bool.true ∧ x9 {x13} x19 = Bool.false) ∧ x9 {(0 : ℕ), (13 : ℕ)} ((26 : ℕ) + x18) = Bool.true ∧ (∃ x19 ∈ x10 x18, x9 {x13} x19 = Bool.true) ∧ ∃ x19 ∈ x10 x18, x9 {x13} x19 = Bool.false) :=
  by
    intro x1 h63 h64 hAO hNd hFun hL1 hL2 x9 x10 x11 x12 x13 x14 hSym hEx
    rcases hSym with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hEx with ⟨a, b, c, hc⟩
      exact hZeroThirteen x1 ⟨h63, h64, hAO, hNd, hFun, hL1, hL2⟩ a b c hc
    · rcases hEx with ⟨a, b, c, hc⟩
      exact hThirteenZero x1 ⟨h63, h64, hAO, hNd, hFun, hL1, hL2⟩ a b c hc
