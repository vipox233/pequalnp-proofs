import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7798_3
    (hLeftGe3 :
      let x1 : Type := Fin (13 : ℕ);
      let x2 : Type := Finset x1;
      have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7;
      have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8;
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false;
      ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 →
        x6 x9 →
        ((3 : ℕ) ≤ x9.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) ∧ (2 : ℕ) ≤ x9.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))) →
        (∃ x10 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 fun (x11 : Fin (26 : ℕ)) => x10.testBit ↑x11) = Bool.true) →
        (∀ (x14 x15 : Fin (26 : ℕ)), (¬∃ (x16 : x1) (x17 : x1), x3 x16 x17 ∧ (x14 = Fin.castAdd (13 : ℕ) x16 ∧ x15 = Fin.natAdd (13 : ℕ) x17 ∨ x15 = Fin.castAdd (13 : ℕ) x16 ∧ x14 = Fin.natAdd (13 : ℕ) x17)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x14 ∨ x17 = x15)) = Bool.false) →
        (64 : ℕ) ≤ x9.size)
    (hRightGe3 :
      let x1 : Type := Fin (13 : ℕ);
      let x2 : Type := Finset x1;
      have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7;
      have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8;
      have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false;
      ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x9 →
        x6 x9 →
        ((2 : ℕ) ≤ x9.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) ∧ (3 : ℕ) ≤ x9.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ))) →
        (∃ x10 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 fun (x11 : Fin (26 : ℕ)) => x10.testBit ↑x11) = Bool.true) →
        (∀ (x14 x15 : Fin (26 : ℕ)), (¬∃ (x16 : x1) (x17 : x1), x3 x16 x17 ∧ (x14 = Fin.castAdd (13 : ℕ) x16 ∧ x15 = Fin.natAdd (13 : ℕ) x17 ∨ x15 = Fin.castAdd (13 : ℕ) x16 ∧ x14 = Fin.natAdd (13 : ℕ) x17)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x14 ∨ x17 = x15)) = Bool.false) →
        (64 : ℕ) ≤ x9.size) :
    (let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x7 x8 : x1), x3 x7 x8 → x4 x6 {x7} {x8} = Bool.true) ∧ ∀ (x7 x8 : x2), x5 x7 x8 → x4 x6 x7 x8 = Bool.false; have x7 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) =>   have x8 : ℕ := x7.lineDeg (26 : ℕ) (Finset.range (13 : ℕ));   have x9 : ℕ := x7.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ));   (2 : ℕ) ≤ Min.min x8 x9 ∧ (3 : ℕ) ≤ Max.max x8 x9; have x8 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ x9 ∈ [(8191 : ℕ), (15860 : ℕ), (31200 : ℕ), (107904 : ℕ)], (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x8 fun (x10 : Fin (26 : ℕ)) => x9.testBit ↑x10) = Bool.true; ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → x6 x9 → x7 x9 → x8 x9 → (∀ (x14 x15 : Fin (26 : ℕ)), (¬∃ (x16 : x1) (x17 : x1), x3 x16 x17 ∧ (x14 = Fin.castAdd (13 : ℕ) x16 ∧ x15 = Fin.natAdd (13 : ℕ) x17 ∨ x15 = Fin.castAdd (13 : ℕ) x16 ∧ x14 = Fin.natAdd (13 : ℕ) x17)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x9 fun (x17 : Fin (26 : ℕ)) => Decidable.decide (x17 = x14 ∨ x17 = x15)) = Bool.false) → (64 : ℕ) ≤ x9.size) :=
  fun x9 hM h6 h7 h8 hNonEdge =>
    Or.elim (le_max_iff.mp h7.2)
      (fun hL3 => hLeftGe3 x9 hM h6 ⟨hL3, le_trans h7.1 (min_le_right _ _)⟩ h8 hNonEdge)
      (fun hR3 => hRightGe3 x9 hM h6 ⟨le_trans h7.1 (min_le_left _ _), hR3⟩ h8 hNonEdge)
