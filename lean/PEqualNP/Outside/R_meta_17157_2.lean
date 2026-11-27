import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17157_2
    (hProjPlaneDual :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)),
        (2 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x4 : Fin x2), (x3 x4).card = x1 + (1 : ℕ)) →
        (∀ (x4 x5 : Fin x2), x4 ≠ x5 → ∃! x6 : Fin x2, x4 ∈ x3 x6 ∧ x5 ∈ x3 x6) →
        ∀ (x4 x5 : Fin x2), x4 ≠ x5 → (x3 x4 ∩ x3 x5).card = (1 : ℕ))
    (hOddOrderDualLB :
      ∀ (x0 x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (100 : ℕ) ≤ x0 →
        x1 = (2 : ℕ) * x0 + (1 : ℕ) →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → (x3 x8 ∩ x3 x9).card = (1 : ℕ)) →
        PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
        x2 + x2 ≤ x4.output →
        x4.output < x2 + x2 + x4.size →
        (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
        (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) →
        x2 * x1 ≤ (100 : ℕ) * x4.size) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → ¬x1 % (2 : ℕ) = (0 : ℕ) → x2 * x1 ≤ (100 : ℕ) * x4.size) :=
  fun x1 x2 x3 x4 hGe200 hN hCard hUniq hAO2 hOutGe hOutLt hOr hRight hFalse hOdd =>
    hOddOrderDualLB (x1 / (2 : ℕ)) x1 x2 x3 x4
      ((Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr hGe200)
      ((Nat.div_add_mod x1 (2 : ℕ)).symm.trans
        (congrArg ((2 : ℕ) * (x1 / (2 : ℕ)) + ·) (Nat.mod_two_ne_zero.mp hOdd)))
      hN hCard hUniq
      (hProjPlaneDual x1 x2 x3
        (Nat.le_trans (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le (198 : ℕ)))) hGe200)
        hN hCard hUniq)
      hAO2 hOutGe hOutLt hOr hRight hFalse
