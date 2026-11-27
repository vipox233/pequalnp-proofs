import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17155_2
    (hProjPlaneDual : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
      (1 : ℕ) ≤ q ∧ N = q ^ (2 : ℕ) + q + (1 : ℕ) ∧
      (∀ l : Fin N, (L l).card = q + (1 : ℕ)) ∧
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) →
      ∀ l1 l2 : Fin N, l1 ≠ l2 → ∃! p : Fin N, p ∈ L l1 ∧ p ∈ L l2)
    (hEvenDualLB : ∀ (m N : ℕ) (L : Fin N → Finset (Fin N)) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (100 : ℕ) ≤ m ∧ N = ((2 : ℕ) * m) ^ (2 : ℕ) + (2 : ℕ) * m + (1 : ℕ) ∧
      (∀ l : Fin N, (L l).card = (2 : ℕ) * m + (1 : ℕ)) ∧
      (∀ p1 p2 : Fin N, p1 ≠ p2 → ∃! l : Fin N, p1 ∈ L l ∧ p2 ∈ L l) ∧
      (∀ l1 l2 : Fin N, l1 ≠ l2 → ∃! p : Fin N, p ∈ L l1 ∧ p ∈ L l2) ∧
      PEqualNP.TopForm.IsAO2 (N + N) C ∧ N + N ≤ C.output ∧ C.output < N + N + C.size ∧
      (∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[C.output - (N + N)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      PEqualNP.GenericRejection.RightOnIncidentPairs L C ∧
      (∀ (P Q : Finset (Fin N)), Q.card ≤ (2 : ℕ) * m → PEqualNP.GenericRejection.IsFalseInput L P Q →
        C.eval (PEqualNP.GenericRejection.incidenceInput P Q) = Bool.false) →
      N * ((2 : ℕ) * m) ≤ (100 : ℕ) * C.size) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x1 % (2 : ℕ) = (0 : ℕ) → x2 * x1 ≤ (100 : ℕ) * x4.size) := by
  intro q N L C h200 hN hCard hUnique hAO hOutLo hOutHi hOutOr hRight hFalse hEven
  have hq : (2 : ℕ) * (q / (2 : ℕ)) = q := (Nat.add_zero _).symm.trans (hEven ▸ Nat.div_add_mod q (2 : ℕ))
  have hm : (100 : ℕ) ≤ q / (2 : ℕ) := (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr h200
  have hDual := hProjPlaneDual q N L ⟨Nat.le_trans (Nat.le_add_left (1 : ℕ) (199 : ℕ)) h200, hN, hCard, hUnique⟩
  exact hq ▸ hEvenDualLB (q / (2 : ℕ)) N L C ⟨hm, hq.symm ▸ hN, hq.symm ▸ hCard, hUnique, hDual, hAO, hOutLo, hOutHi, hOutOr, hRight, hq.symm ▸ hFalse⟩
