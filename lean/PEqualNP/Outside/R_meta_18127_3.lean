import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18127_3
    (hSharedGateReaders :
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        (∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), c.gates[i]? = Option.some g →
          ∃ (u v : ℕ), g.inputs = [u, v] ∧ u ≠ v ∧ u < (14 : ℕ) + i ∧ v < (14 : ℕ) + i) →
        (14 : ℕ) ≤ w →
        (2 : ℕ) ≤ List.count w (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs c.gates) →
        ∃ (k g1 g2 : ℕ),
          w = (14 : ℕ) + k ∧ k < g1 ∧ g1 < g2 ∧ g2 < c.size ∧
          w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt c g1).inputs ∧
          w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt c g2).inputs)
    (hWithTwoReaders :
      let x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop :=
        fun (p l : Fin (7 : ℕ)) => p = l ∨ p = l + (1 : Fin (7 : ℕ)) ∨ p = l + (3 : Fin (7 : ℕ));
      let x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
        fun (c : PEqualNP.CircuitLowerBounds.Circuit) =>
          c.size ≤ (27 : ℕ) ∧
          (∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), c.gates[i]? = Option.some g →
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ (u v : ℕ), g.inputs = [u, v] ∧ u ≠ v ∧ u < (14 : ℕ) + i ∧ v < (14 : ℕ) + i) ∧
          ∀ (f : Fin (14 : ℕ) → Bool), c.eval (List.ofFn f) = Bool.true ↔
            ∃ (p l : Fin (7 : ℕ)), x1 p l ∧ f (Fin.castAdd (7 : ℕ) p) = Bool.true ∧ f (Fin.natAdd (7 : ℕ) l) = Bool.true;
      let x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop :=
        fun (c : PEqualNP.CircuitLowerBounds.Circuit) =>
          (List.filter (fun (w : ℕ) => Decidable.decide ((14 : ℕ) ≤ w))
            (c.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs c.gates)).Nodup;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (k g1 g2 : ℕ),
        (x2 x4 ∧
         ¬x3 x4 ∧
         k < g1 ∧ g1 < g2 ∧ g2 < x4.size ∧
         (14 : ℕ) + k ≠ x4.output ∧
         ((14 : ℕ) + k) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 g1).inputs ∧
         ((14 : ℕ) + k) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 g2).inputs ∧
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} ∧
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)}) →
        ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit),
          x2 x10 ∧ x3 x10 ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(7 : ℕ)}) :
    (have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2 x4 → ¬x3 x4 → (∃ (x7 : ℕ), (14 : ℕ) ≤ x7 ∧ x7 ≠ x4.output ∧ (2 : ℕ) ≤ List.count x7 (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x2 x10 ∧ x3 x10 ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(0 : ℕ)} ∧ (2 : ℕ) ≤ x10.lineDeg (14 : ℕ) {(7 : ℕ)}) :=
  fun x4 hx2 hnotx3 hShared hD0 hD7 =>
    Exists.elim hShared fun w hw =>
      Exists.elim
        (hSharedGateReaders x4 w (fun i g hi => (hx2.2.1 i g hi).2) hw.1 hw.2.2)
        fun k hk =>
          Exists.elim hk fun g1 hg1 =>
            Exists.elim hg1 fun g2 hg2 =>
              hWithTwoReaders x4 k g1 g2
                ⟨hx2, hnotx3, hg2.2.1, hg2.2.2.1, hg2.2.2.2.1,
                  hg2.1 ▸ hw.2.1,
                  hg2.1 ▸ hg2.2.2.2.2.1,
                  hg2.1 ▸ hg2.2.2.2.2.2,
                  hD0, hD7⟩
