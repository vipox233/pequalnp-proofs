import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18272_1
    (hBitBound :
      ∀ (v : ℕ), v < (1099511627776 : ℕ) →
        (v % (65536 : ℕ) ≠ (0 : ℕ) → ∃ (x8 : Fin (16 : ℕ)), v.testBit ↑x8 = Bool.true) ∧
        ((65536 : ℕ) ≤ v → ∃ (x8 : Fin (24 : ℕ)), v.testBit ((16 : ℕ) + ↑x8) = Bool.true) ∧
        (∀ (w : ℕ), w < (1099511627776 : ℕ) → (v &&& w) < (1099511627776 : ℕ) ∧ (v ||| w) < (1099511627776 : ℕ)))
    (hCircuitArith :
      ∃ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 : Fin x1 → ℕ) (x4 : Fin x1 → ℕ) (x5 : ℕ → ℕ) (x6 : List (ℕ × ℕ)),
        (6 : ℕ) ≤ x1 ∧
        x1 + (2 : ℕ) * x6.length = (22 : ℕ) ∧
        (3 : ℕ) ≤ (List.filter x2 (List.finRange x1)).length ∧
        (∀ (x7 : Fin (11 : ℕ)), x5 ↑x7 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x7 (0 : ℕ)) ∧
        (∀ (x7 : Fin x1),
          x3 x7 ≤ x4 x7 ∧
          x4 x7 < (11 : ℕ) + ↑x7 ∧
          (x5 ((11 : ℕ) + ↑x7) = if x2 x7 = Bool.true then x5 (x3 x7) &&& x5 (x4 x7) else x5 (x3 x7) ||| x5 (x4 x7)) ∧
          x5 ((11 : ℕ) + ↑x7) % (65536 : ℕ) ≠ (0 : ℕ) ∧
          (65536 : ℕ) ≤ x5 ((11 : ℕ) + ↑x7) ∧
          ((∃ x8 ∈ x6, (11 : ℕ) + ↑x7 = x8.1 ∨ (11 : ℕ) + ↑x7 = x8.2) ∨ ∃ (x8 : Fin x1), x7 < x8 ∧ ((11 : ℕ) + ↑x7 = x3 x8 ∨ (11 : ℕ) + ↑x7 = x4 x8))) ∧
        (∀ x7 ∈ x6, x7.1 < (11 : ℕ) + x1 ∧ x7.2 < (11 : ℕ) + x1) ∧
        List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ × ℕ) => x5 x7.1 &&& x5 x7.2) x6) = (65535 : ℕ)) :
    ∃ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 : Fin x1 → ℕ) (x4 : Fin x1 → ℕ) (x5 : ℕ → ℕ) (x6 : List (ℕ × ℕ)), (6 : ℕ) ≤ x1 ∧ x1 + (2 : ℕ) * x6.length = (22 : ℕ) ∧ (3 : ℕ) ≤ (List.filter x2 (List.finRange x1)).length ∧ (∀ (x7 : Fin (11 : ℕ)), x5 ↑x7 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x7 (0 : ℕ)) ∧ (∀ (x7 : Fin x1), x3 x7 ≤ x4 x7 ∧ x4 x7 < (11 : ℕ) + ↑x7 ∧ (x5 ((11 : ℕ) + ↑x7) = if x2 x7 = Bool.true then x5 (x3 x7) &&& x5 (x4 x7) else x5 (x3 x7) ||| x5 (x4 x7)) ∧ (∃ (x8 : Fin (16 : ℕ)), (x5 ((11 : ℕ) + ↑x7)).testBit ↑x8 = Bool.true) ∧ (∃ (x8 : Fin (24 : ℕ)), (x5 ((11 : ℕ) + ↑x7)).testBit ((16 : ℕ) + ↑x8) = Bool.true) ∧ ((∃ x8 ∈ x6, (11 : ℕ) + ↑x7 = x8.1 ∨ (11 : ℕ) + ↑x7 = x8.2) ∨ ∃ (x8 : Fin x1), x7 < x8 ∧ ((11 : ℕ) + ↑x7 = x3 x8 ∨ (11 : ℕ) + ↑x7 = x4 x8))) ∧ (∀ x7 ∈ x6, x7.1 < (11 : ℕ) + x1 ∧ x7.2 < (11 : ℕ) + x1) ∧ List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ × ℕ) => x5 x7.1 &&& x5 x7.2) x6) = (65535 : ℕ) := by
  rcases hCircuitArith with ⟨x1, x2, x3, x4, x5, x6, h6, hEq, hAnd, hInit, hGates, hPairs, hOut⟩
  have hBase : ∀ (i : Fin (11 : ℕ)),
      [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ),
       (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ),
       (1065151898146 : ℕ)].getD ↑i (0 : ℕ) < (1099511627776 : ℕ) := by
    decide
  have hLt : ∀ (k : ℕ), k < (11 : ℕ) + x1 → x5 k < (1099511627776 : ℕ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      by_cases hk11 : k < (11 : ℕ)
      · rw [hInit ⟨k, hk11⟩]
        exact hBase ⟨k, hk11⟩
      · have hj : k - (11 : ℕ) < x1 := by omega
        have hkeq : (11 : ℕ) + (k - (11 : ℕ)) = k := by omega
        rcases hGates ⟨k - (11 : ℕ), hj⟩ with ⟨h34, h4lt, hval, _, _, _⟩
        dsimp only at h4lt
        have h3lt : x3 ⟨k - (11 : ℕ), hj⟩ < k := by omega
        have h4lt' : x4 ⟨k - (11 : ℕ), hj⟩ < k := by omega
        have hb3 := ih _ h3lt (by omega)
        have hb4 := ih _ h4lt' (by omega)
        rw [← hkeq, hval]
        cases x2 ⟨k - (11 : ℕ), hj⟩
        · exact ((hBitBound _ hb3).2.2 _ hb4).2
        · exact ((hBitBound _ hb3).2.2 _ hb4).1
  refine ⟨x1, x2, x3, x4, x5, x6, h6, hEq, hAnd, hInit, ?_, hPairs, hOut⟩
  intro x7
  rcases hGates x7 with ⟨h34, h4lt, hval, hPos, hNeg, hUse⟩
  have hbk := hLt ((11 : ℕ) + ↑x7) (by omega)
  exact ⟨h34, h4lt, hval, (hBitBound _ hbk).1 hPos, (hBitBound _ hbk).2.1 hNeg, hUse⟩
