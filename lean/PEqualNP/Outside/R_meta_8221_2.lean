import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8221_2
    (hDeadInput :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (x1 x2 : Fin (13 : ℕ)) =>
          x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (26 : ℕ)),
        (∀ (f g : Fin (26 : ℕ) → Bool), (∀ (j : Fin (26 : ℕ)), j ≠ v → f j = g j) →
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 f =
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 g) →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 →
          (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) =>
            Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))),
          (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧
          (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) =>
            Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x8))
              (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) x10) = Bool.true)
    (hAllEssential :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (x1 x2 : Fin (13 : ℕ)) =>
          x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        (∀ (v : Fin (26 : ℕ)), ∃ (f g : Fin (26 : ℕ) → Bool),
          (∀ (j : Fin (26 : ℕ)), j ≠ v → f j = g j) ∧
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 f ≠
          PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 g) →
        (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 →
          (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) =>
            Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) →
        ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))),
          (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧
          (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧
          (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) =>
            Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x8))
              (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) x10) = Bool.true) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → (∀ (x7 x8 : Fin (13 : ℕ)), x1 x7 x8 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) → ∃ (x8 : Finset (Fin (13 : ℕ))) (x9 : Finset (Fin (13 : ℕ))), (∀ x10 ∈ x8, ∀ x12 ∈ x9, ¬x1 x10 x12) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x8 | x1 x11 x10}.card ≤ (2 : ℕ)) ∧ (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x1 x10 x11}.card ≤ (2 : ℕ)) ∧ (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x8)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x9)) x10) = Bool.true) :=
  fun x2 hM hSz hDegR hDegL hInc =>
    Or.elim
      (Classical.em (∀ (v : Fin (26 : ℕ)), ∃ (f g : Fin (26 : ℕ) → Bool),
        (∀ (j : Fin (26 : ℕ)), j ≠ v → f j = g j) ∧
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 f ≠
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 g))
      (fun hEss => hAllEssential x2 hM hSz hDegR hDegL hEss hInc)
      (fun hNotEss =>
        Exists.elim (Classical.not_forall.mp hNotEss) fun v hv =>
          hDeadInput x2 v
            (fun f g hfg => Classical.byContradiction fun hne => hv ⟨f, g, hfg, hne⟩)
            hInc)
