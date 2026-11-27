import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17205_1
    (hCircuit : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (28 : ℕ) ∧ x1.output < (23 : ℕ) + x1.size ∧ ∀ (x2 : Fin (17 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)), x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ))]) = Bool.true ↔ ∃ (p : Fin (6 : ℕ)) (l : Fin (17 : ℕ)), (([(1856 : ℕ), (14400 : ℕ), (114752 : ℕ), (18816 : ℕ), (37504 : ℕ), (74880 : ℕ)] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ∧ x2 (Fin.ofNat (17 : ℕ) ↑p) = Bool.true ∧ x2 l = Bool.true)
    (hTableEquiv : ∀ (p : Fin (6 : ℕ)) (l : Fin (17 : ℕ)), (([(1856 : ℕ), (14400 : ℕ), (114752 : ℕ), (18816 : ℕ), (37504 : ℕ), (74880 : ℕ)] : List ℕ).getD p.val (0 : ℕ)).testBit l.val = Bool.true ↔ ∃ (x4 : Fin (4 : ℕ)), l = Fin.ofNat (17 : ℕ) (if ↑x4 = (0 : ℕ) then (6 : ℕ) + ↑p / (3 : ℕ) else (8 : ℕ) + if ↑p < (3 : ℕ) then (3 : ℕ) * ↑p + (↑x4 - (1 : ℕ)) else (3 : ℕ) * (↑x4 - (1 : ℕ)) + (↑p - (3 : ℕ)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (28 : ℕ) ∧ x1.output < (23 : ℕ) + x1.size ∧ ∀ (x2 : Fin (17 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)), x2 (13 : Fin (17 : ℕ)) || x2 (14 : Fin (17 : ℕ)) || x2 (9 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)), x2 (15 : Fin (17 : ℕ)) || x2 (11 : Fin (17 : ℕ)) || x2 (10 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)), x2 (16 : Fin (17 : ℕ)) || x2 (12 : Fin (17 : ℕ)) || x2 (8 : Fin (17 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (6 : ℕ)) (x4 : Fin (4 : ℕ)), x2 (Fin.ofNat (17 : ℕ) ↑x3) = Bool.true ∧ x2 (Fin.ofNat (17 : ℕ) (if ↑x4 = (0 : ℕ) then (6 : ℕ) + ↑x3 / (3 : ℕ) else (8 : ℕ) + if ↑x3 < (3 : ℕ) then (3 : ℕ) * ↑x3 + (↑x4 - (1 : ℕ)) else (3 : ℕ) * (↑x4 - (1 : ℕ)) + (↑x3 - (3 : ℕ)))) = Bool.true) := by
  obtain ⟨C, hM, hSz, hOut, hEv⟩ := hCircuit
  refine ⟨C, hM, hSz, hOut, ?_⟩
  intro x2
  refine (hEv x2).trans ?_
  constructor
  · intro h
    obtain ⟨p, l, hbit, hp, hl⟩ := h
    obtain ⟨x4, hlEq⟩ := (hTableEquiv p l).mp hbit
    rw [hlEq] at hl
    exact ⟨p, x4, hp, hl⟩
  · intro h
    obtain ⟨p, x4, hp, hl⟩ := h
    exact ⟨p, Fin.ofNat (17 : ℕ) (if ↑x4 = (0 : ℕ) then (6 : ℕ) + ↑p / (3 : ℕ) else (8 : ℕ) + if ↑p < (3 : ℕ) then (3 : ℕ) * ↑p + (↑x4 - (1 : ℕ)) else (3 : ℕ) * (↑x4 - (1 : ℕ)) + (↑p - (3 : ℕ))), (hTableEquiv p _).mpr ⟨x4, rfl⟩, hp, hl⟩
