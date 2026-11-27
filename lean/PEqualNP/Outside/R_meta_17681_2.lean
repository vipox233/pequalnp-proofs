import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17681_2
    (hJunkFree :
      ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x3.Nonempty →
        (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
        (∀ (z : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 z = Decidable.decide (∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true)) →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit),
          D.size ≤ x4.size ∧
          PEqualNP.TopForm.IsAO2 (x1 + x2) D ∧
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) D = PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 ∧
          ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ (z : Fin (x1 + x2) → Bool), PEqualNP.EdgeOwnership.gateVal (x1 + x2) D j z = Bool.true →
              ∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true)
    (hCleanDelete :
      ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun v e => Fin.castAdd x2 e.1 = v ∨ Fin.natAdd x1 e.2 = v;
        have x6 : Finset (Fin x1 × Fin x2) → (Fin (x1 + x2) → Bool) → Bool := fun E z => Decidable.decide (∃ e ∈ E, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true);
        (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) →
        PEqualNP.TopForm.IsAO2 (x1 + x2) x4 →
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = x6 x3 →
        (∀ j < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ (z : Fin (x1 + x2) → Bool), PEqualNP.EdgeOwnership.gateVal (x1 + x2) x4 j z = Bool.true →
            ∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true) →
        (∃ v : Fin (x1 + x2), (Finset.filter (x5 v) x3).card = (1 : ℕ)) →
        (∀ (u v : Fin (x1 + x2)), u ≠ v → (Finset.filter (x5 u) x3).card = (1 : ℕ) → (∃ e ∈ x3, x5 u e ∧ x5 v e) → (3 : ℕ) ≤ (Finset.filter (x5 v) x3).card) →
        (∀ v : Fin (x1 + x2), {e ∈ x3 | ¬x5 v e}.Nonempty) →
        ∃ v : Fin (x1 + x2), (Finset.filter (x5 v) x3).Nonempty ∧
          ∃ (D : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.Monotone2 D ∧
            PEqualNP.MetaComplexity.circuitFun (x1 + x2) D = x6 ({e ∈ x3 | ¬x5 v e}) ∧
            D.size + (Finset.filter (x5 v) x3).card + (1 : ℕ) ≤ x4.size) :
    (∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → (Fin (x1 + x2) → Bool) → Bool := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ x8 ∈ x6, x7 (Fin.castAdd x2 x8.1) = Bool.true ∧ x7 (Fin.natAdd x1 x8.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = x6 x3 → (∃ (x10 : Fin (x1 + x2)), (Finset.filter (x5 x10) x3).card = (1 : ℕ)) → (∀ (x11 x12 : Fin (x1 + x2)), x11 ≠ x12 → (Finset.filter (x5 x11) x3).card = (1 : ℕ) → (∃ x15 ∈ x3, x5 x11 x15 ∧ x5 x12 x15) → (3 : ℕ) ≤ (Finset.filter (x5 x12) x3).card) → (∀ (x12 : Fin (x1 + x2)), {x13 ∈ x3 | ¬x5 x12 x13}.Nonempty) → ¬x1 % (2 : ℕ) = (0 : ℕ) → ∃ (x14 : Fin (x1 + x2)), (Finset.filter (x5 x14) x3).Nonempty ∧ ∃ (x15 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x15 = x6 ({x16 ∈ x3 | ¬x5 x14 x16}) ∧ x15.size + (Finset.filter (x5 x14) x3).card + (1 : ℕ) ≤ x4.size) := by
  intro x1 x2 x3 x4 x5 x6 hC4 hAO hFun hDeg1 hDeg3 hRem _
  obtain ⟨v0, hv0⟩ := hDeg1
  have hne : x3.Nonempty := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.filter (x5 v0) x3).card)
    exact ⟨e, (Finset.mem_filter.mp he).1⟩
  have hFunPt : ∀ z : Fin (x1 + x2) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 z =
      Decidable.decide (∃ e ∈ x3, z (Fin.castAdd x2 e.1) = Bool.true ∧ z (Fin.natAdd x1 e.2) = Bool.true) := by
    intro z
    exact congrFun hFun z
  obtain ⟨D, hDle, hDAO, hDfun, hDclean⟩ := hJunkFree x1 x2 x3 x4 hne hC4 hAO hFunPt
  obtain ⟨v, hvne, C', hC'm, hC'f, hC'sz⟩ := hCleanDelete x1 x2 x3 D hC4 hDAO (hDfun.trans hFun) hDclean ⟨v0, hv0⟩ hDeg3 hRem
  exact ⟨v, hvne, C', hC'm, hC'f, le_trans hC'sz hDle⟩
