import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7911_2
    (hHasDegThree :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (x1 x2 : Fin (13 : ℕ)) =>
          x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ))
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (3 : ℕ) →
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) →
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
        ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))),
          (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (x13 x14 : Fin (13 : ℕ)), ∀ x15 ∈ x10, x1 x15 x12 → x15 = x13 ∨ x15 = x14) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (x13 x14 : Fin (13 : ℕ)), ∀ x15 ∈ x11, x1 x12 x15 → x15 = x13 ∨ x15 = x14) ∧
          ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true)
    (hNoDegThree :
      let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (x1 x2 : Fin (13 : ℕ)) =>
          x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ))
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (3 : ℕ) →
        PEqualNP.MetaComplexity.Monotone2 x2 →
        x2.size ≤ (63 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) →
        ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) →
        PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) →
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) →
        ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))),
          (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (x13 x14 : Fin (13 : ℕ)), ∀ x15 ∈ x10, x1 x15 x12 → x15 = x13 ∨ x15 = x14) ∧
          (∀ (x12 : Fin (13 : ℕ)), ∃ (x13 x14 : Fin (13 : ℕ)), ∀ x15 ∈ x11, x1 x12 x15 → x15 = x13 ∨ x15 = x14) ∧
          ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (63 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (1 : ℕ) → ¬PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (1 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (2 : ℕ) → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x2 (2 : ℕ) → (∀ (x9 x10 : Fin (13 : ℕ)), x1 x9 x10 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = Fin.castAdd (13 : ℕ) x9 ∨ x12 = Fin.natAdd (13 : ℕ) x10)) = Bool.true) → ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), (∀ x12 ∈ x10, ∀ x14 ∈ x11, ¬x1 x12 x14) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x10 | x1 x13 x12}.card ≤ (2 : ℕ)) ∧ (∀ (x12 : Fin (13 : ℕ)), {x13 ∈ x11 | x1 x12 x13}.card ≤ (2 : ℕ)) ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ x13 ∈ x10, x12 (Fin.castAdd (13 : ℕ) x13) = Bool.true) → (∀ x14 ∈ x11, x12 (Fin.natAdd (13 : ℕ) x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 x12 = Bool.true :=
  fun x2 hM hS hN1R hN1L h2R h2L hE =>
    Exists.elim
      (Or.elim (Classical.em (PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x2 (3 : ℕ)))
        (fun h3 => hHasDegThree x2 h3 hM hS hN1R hN1L h2R h2L hE)
        (fun hn3 => hNoDegThree x2 hn3 hM hS hN1R hN1L h2R h2L hE))
      fun x10 h1 =>
        Exists.elim h1 fun x11 h2 =>
          ⟨x10, x11, h2.1,
            fun x12 =>
              Exists.elim (h2.2.1 x12) fun a ha =>
                Exists.elim ha fun b hab =>
                  le_trans
                    (Finset.card_le_card (fun x13 hx13 =>
                      Or.elim (hab x13 (Finset.mem_filter.mp hx13).1 (Finset.mem_filter.mp hx13).2)
                        (fun h1 => Finset.mem_insert.mpr (Or.inl h1))
                        (fun h2 => Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h2)))))
                    (le_trans (Finset.card_insert_le a {b}) (Nat.add_le_add_right (Finset.card_singleton b).le 1)),
            fun x12 =>
              Exists.elim (h2.2.2.1 x12) fun a ha =>
                Exists.elim ha fun b hab =>
                  le_trans
                    (Finset.card_le_card (fun x13 hx13 =>
                      Or.elim (hab x13 (Finset.mem_filter.mp hx13).1 (Finset.mem_filter.mp hx13).2)
                        (fun h1 => Finset.mem_insert.mpr (Or.inl h1))
                        (fun h2 => Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h2)))))
                    (le_trans (Finset.card_insert_le a {b}) (Nat.add_le_add_right (Finset.card_singleton b).le 1)),
            h2.2.2.2⟩
