import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18808_2
    (hTreeUnfold :
      let x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop :=
        fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) =>
          x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true;
      let x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop :=
        fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) =>
          PEqualNP.MetaComplexity.DMFormula.rec (fun (_ : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2;
      let x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ :=
        fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) =>
          PEqualNP.MetaComplexity.DMFormula.rec
            (fun (x5 : Fin (14 : ℕ)) (_ : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ))
            (fun (_ _ : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8)
            (fun (_ _ : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (x4.size ≤ (27 : ℕ) ∧
         PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧
         (∀ x7 ∈ x4.gates, x7.inputs.Nodup) ∧
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} ∧
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} ∧
         (∀ (k : ℕ), k < x4.gates.length →
           (x4.gates.flatMap fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs).count ((14 : ℕ) + k) ≤ (1 : ℕ))) →
        ∃ (x11 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)),
          x2 x11 ∧ x11.leaves ≤ (28 : ℕ) ∧
          (∀ (x12 : Fin (14 : ℕ) → Bool), x11.eval x12 = x4.eval (List.ofFn x12)) ∧
          (2 : ℕ) ≤ x3 (0 : ℕ) x11 ∧ (2 : ℕ) ≤ x3 (7 : ℕ) x11)
    (hHasSharedGate :
      let x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop :=
        fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) =>
          x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true;
      let x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop :=
        fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) =>
          PEqualNP.MetaComplexity.DMFormula.rec (fun (_ : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2;
      let x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ :=
        fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) =>
          PEqualNP.MetaComplexity.DMFormula.rec
            (fun (x5 : Fin (14 : ℕ)) (_ : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ))
            (fun (_ _ : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8)
            (fun (_ _ : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (x4.size ≤ (27 : ℕ) ∧
         PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 ∧
         (∀ x7 ∈ x4.gates, x7.inputs.Nodup) ∧
         (∀ (x8 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x8) = Bool.true ↔
           ∃ (x9 : Fin (7 : ℕ)) (x10 : Fin (7 : ℕ)),
             x9 ∈ PEqualNP.CircuitLowerBounds.fanoLines x10 ∧
             x8 (Fin.castAdd (7 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (7 : ℕ) x10) = Bool.true) ∧
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} ∧
         (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} ∧
         (∃ (k : ℕ), k < x4.gates.length ∧
           (2 : ℕ) ≤ (x4.gates.flatMap fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs).count ((14 : ℕ) + k))) →
        ∃ (x11 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)),
          x2 x11 ∧ x11.leaves ≤ (28 : ℕ) ∧
          (∀ (x12 : Fin (14 : ℕ) → Bool), x11.eval x12 = x4.eval (List.ofFn x12)) ∧
          (2 : ℕ) ≤ x3 (0 : ℕ) x11 ∧ (2 : ℕ) ≤ x3 (7 : ℕ) x11) :
    (have x1 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop → Prop → Prop := fun (x1 x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x3 x4 : Prop) => x3 ∧ x4 ∧ ¬∃ (x5 : Fin (14 : ℕ)), x1 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true ∧ x2 = PEqualNP.MetaComplexity.DMFormula.lit x5 Bool.true; have x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → Prop := fun (x2 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x3 : Fin (14 : ℕ)) (x4 : Bool) => x4 = Bool.true) x1 x1 x2; have x3 : ℕ → PEqualNP.MetaComplexity.DMFormula (14 : ℕ) → ℕ := fun (x3 : ℕ) (x4 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) => PEqualNP.MetaComplexity.DMFormula.rec (fun (x5 : Fin (14 : ℕ)) (x6 : Bool) => if ↑x5 = x3 then (1 : ℕ) else (0 : ℕ)) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => x7 + x8) (fun (x5 x6 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)) (x7 x8 : ℕ) => Max.max x7 x8) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x4 → (∀ x7 ∈ x4.gates, x7.inputs.Nodup) → (∀ (x8 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x8) = Bool.true ↔ ∃ (x9 : Fin (7 : ℕ)) (x10 : Fin (7 : ℕ)), x9 ∈ PEqualNP.CircuitLowerBounds.fanoLines x10 ∧ x8 (Fin.castAdd (7 : ℕ) x9) = Bool.true ∧ x8 (Fin.natAdd (7 : ℕ) x10) = Bool.true) → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(0 : ℕ)} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ)} → ∃ (x11 : PEqualNP.MetaComplexity.DMFormula (14 : ℕ)), x2 x11 ∧ x11.leaves ≤ (28 : ℕ) ∧ (∀ (x12 : Fin (14 : ℕ) → Bool), x11.eval x12 = x4.eval (List.ofFn x12)) ∧ (2 : ℕ) ≤ x3 (0 : ℕ) x11 ∧ (2 : ℕ) ≤ x3 (7 : ℕ) x11) :=
  fun x4 hSz hAO hNd hSpec hD0 hD7 =>
    Or.elim
      (Classical.em (∀ (k : ℕ), k < x4.gates.length →
        (x4.gates.flatMap fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs).count ((14 : ℕ) + k) ≤ (1 : ℕ)))
      (fun hTree => hTreeUnfold x4 ⟨hSz, hAO, hNd, hD0, hD7, hTree⟩)
      (fun hNotTree =>
        Exists.elim (Classical.not_forall.mp hNotTree) fun k hk =>
          hHasSharedGate x4
            ⟨hSz, hAO, hNd, hSpec, hD0, hD7,
              ⟨k, Classical.byContradiction fun hnk => hk fun hlt => False.elim (hnk hlt),
               Nat.lt_of_not_le fun hle => hk fun _ => hle⟩⟩)
