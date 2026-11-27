import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7917_2
    (hHasDeg3 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (3 : ℕ) →
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) →
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
        ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))),
          (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (a b : Fin (13 : ℕ)), ∀ x13 ∈ x10, x1 x13 x12 → x13 = a ∨ x13 = b) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (a b : Fin (13 : ℕ)), ∀ x13 ∈ x11, x1 x12 x13 → x13 = a ∨ x13 = b) ∧
          ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true)
    (hNoDeg3 :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (3 : ℕ) →
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) →
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
        ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))),
          (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (a b : Fin (13 : ℕ)), ∀ x13 ∈ x10, x1 x13 x12 → x13 = a ∨ x13 = b) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (a b : Fin (13 : ℕ)), ∀ x13 ∈ x11, x1 x12 x13 → x13 = a ∨ x13 = b) ∧
          ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) → (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) → ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x10 | x1 x13 x12}.card ≤ (2 : ℕ)) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x1 x12 x13}.card ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true) :=
  fun x2 hM hSz h1 h2 h3 h4 hPos =>
    have hRes :=
      Or.elim (Classical.em (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (3 : ℕ)))
        (fun hd => hHasDeg3 x2 hd hM hSz h1 h2 h3 h4 hPos)
        (fun hnd => hNoDeg3 x2 hnd hM hSz h1 h2 h3 h4 hPos)
    Exists.elim hRes fun x10 hx10 =>
    Exists.elim hx10 fun x11 hw =>
      ⟨x10, x11, hw.1,
        fun x12 =>
          Exists.elim (hw.2.1 x12) fun a ha =>
          Exists.elim ha fun b hab =>
            Nat.le_trans
              (Finset.card_le_card (t := {a, b}) fun y hy =>
                let hy' := Finset.mem_filter.mp hy
                Finset.mem_insert.mpr (Or.imp_right Finset.mem_singleton.mpr (hab y hy'.1 hy'.2)))
              Finset.card_le_two,
        fun x12 =>
          Exists.elim (hw.2.2.1 x12) fun a ha =>
          Exists.elim ha fun b hab =>
            Nat.le_trans
              (Finset.card_le_card (t := {a, b}) fun y hy =>
                let hy' := Finset.mem_filter.mp hy
                Finset.mem_insert.mpr (Or.imp_right Finset.mem_singleton.mpr (hab y hy'.1 hy'.2)))
              Finset.card_le_two,
        hw.2.2.2⟩
