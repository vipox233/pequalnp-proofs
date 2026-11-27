import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18334_2
    (hOutputWireBounds :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
        (∀ (x8 : Fin (26 : ℕ) → Bool), (x2.wires (List.ofFn x8)).getD x2.output Bool.false = Bool.true ↔
          ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x1 x9 x10 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) →
        (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size ∧
        ∀ (i : Fin (26 : ℕ)), ∃ g < x2.size, ↑i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs)
    (hRange56to63 :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        have x7 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;
        (PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 ∧
         (∀ x4 ∈ x2.gates, x4.inputs.Nodup) ∧
         (56 : ℕ) ≤ x2.size ∧ x2.size ≤ (63 : ℕ) ∧
         (26 : ℕ) ≤ x2.output ∧ x2.output < (26 : ℕ) + x2.size ∧
         (∀ (i : Fin (26 : ℕ)), ∃ g < x2.size, ↑i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs) ∧
         (∀ (x8 : Fin (26 : ℕ) → Bool), x7 x8 x2.output = Bool.true ↔
           ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x1 x9 x10 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) ∧
         (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 →
           ∃ x12 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x12.card ∧
             ∀ x13 ∈ x12, ∀ x15 < (26 : ℕ) + x13,
               ∃ (x17 : Fin (26 : ℕ) → Bool), x17 (Fin.castAdd (13 : ℕ) x9) = Bool.false ∧ x17 (Fin.natAdd (13 : ℕ) x10) = Bool.false ∧ x7 x17 x15 ≠ x7 x17 ((26 : ℕ) + x13))) →
        have x10 : ℕ → Prop := fun (x10 : ℕ) =>
          Relation.ReflTransGen (fun (x11 x12 : ℕ) =>
            ∃ (x13 : ℕ) (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate),
              x12 = (26 : ℕ) + x13 ∧ x2.gates[x13]? = Option.some x15 ∧
              (x15.inputs = [x11, x14] ∨ x15.inputs = [x14, x11]) ∧
              (x15.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x7 (fun (x16 : Fin (26 : ℕ)) => Decidable.decide (↑x16 = x10)) x14 = Bool.true))
            ((13 : ℕ) - x10) x2.output;
        x10 (0 : ℕ) ∨ x10 (13 : ℕ)) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       x2.size ≤ (64 : ℕ) →         x2.size ≤ (63 : ℕ) →           have x7 : (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : ℕ) => (x2.wires (List.ofFn x7)).getD x8 Bool.false;           (∀ (x8 : Fin (26 : ℕ) → Bool), x7 x8 x2.output = Bool.true ↔ ∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x1 x9 x10 ∧ x8 (Fin.castAdd (13 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (13 : ℕ) x10) = Bool.true) →             (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → ∃ x12 ⊆ Finset.range x2.size, (56 : ℕ) ≤ x12.card ∧ ∀ x13 ∈ x12, ∀ x15 < (26 : ℕ) + x13, ∃ (x17 : Fin (26 : ℕ) → Bool), x17 (Fin.castAdd (13 : ℕ) x9) = Bool.false ∧ x17 (Fin.natAdd (13 : ℕ) x10) = Bool.false ∧ x7 x17 x15 ≠ x7 x17 ((26 : ℕ) + x13)) →               have x10 : ℕ → Prop := fun (x10 : ℕ) => Relation.ReflTransGen (fun (x11 x12 : ℕ) => ∃ (x13 : ℕ) (x14 : ℕ) (x15 : PEqualNP.CircuitLowerBounds.Gate), x12 = (26 : ℕ) + x13 ∧ x2.gates[x13]? = Option.some x15 ∧ (x15.inputs = [x11, x14] ∨ x15.inputs = [x14, x11]) ∧ (x15.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x7 (fun (x16 : Fin (26 : ℕ)) => Decidable.decide (↑x16 = x10)) x14 = Bool.true)) ((13 : ℕ) - x10) x2.output;               x10 (0 : ℕ) ∨ x10 (13 : ℕ)) := by
  intro x1 x2 hAO hNodup _h64 h63 x7 hSpec h56
  exact
    let hOut := hOutputWireBounds x2 hAO hSpec
    let hGe56 : (56 : ℕ) ≤ x2.size :=
      Exists.elim (h56 (0 : Fin (13 : ℕ)) (0 : Fin (13 : ℕ)) (Or.inl rfl)) fun S hS =>
        Nat.le_trans hS.2.1 (Eq.subst (motive := fun k => S.card ≤ k) (Finset.card_range x2.size) (Finset.card_le_card hS.1))
    hRange56to63 x2 ⟨hAO, hNodup, hGe56, h63, hOut.1, hOut.2.1, hOut.2.2, hSpec, h56⟩
