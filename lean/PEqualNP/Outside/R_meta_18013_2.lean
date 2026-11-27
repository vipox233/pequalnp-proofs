import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18013_2
    (hZeroX4 :
      ∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),
        have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>
          have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;
          [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));
        (↑x1 < (4 : ℕ) ∧
          x4.size = (0 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 ∧
          PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 ∧
          x3.size ≤ (17 : ℕ) ∧
          (9 : ℕ) ≤ x3.output ∧
          x3.output < (9 : ℕ) + x3.size ∧
          (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.true)) →
        ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool),
          x4.eval (x3.wires (List.ofFn x13) ++ [x14 && x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13))
    (hPosX4 :
      ∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),
        have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>
          have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;
          [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));
        (↑x1 < (4 : ℕ) ∧
          (1 : ℕ) ≤ x4.size ∧
          PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 ∧
          PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 ∧
          x3.size + x4.size ≤ (17 : ℕ) ∧
          (9 : ℕ) ≤ x3.output ∧
          x3.output < (9 : ℕ) + x3.size ∧
          (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.true)) →
        ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool),
          x4.eval (x3.wires (List.ofFn x13) ++ [x14 && x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13)) :
    (∀ (x1 : Fin (11 : ℕ)) (x2 : Fin (10 : ℕ)) (x3 x4 : PEqualNP.CircuitLowerBounds.Circuit),   ↑x1 < (4 : ℕ) →     PEqualNP.TopForm.IsAO2 (9 : ℕ) x3 →       PEqualNP.TopForm.IsAO2 ((10 : ℕ) + x3.size) x4 →         x3.size + x4.size ≤ (17 : ℕ) →           (9 : ℕ) ≤ x3.output →             x3.output < (9 : ℕ) + x3.size →               have x11 : (Fin (10 : ℕ) → Bool) → Bool := fun (x11 : Fin (10 : ℕ) → Bool) =>                 have x12 : Fin (11 : ℕ) → Bool := x1.insertNth Bool.false x11;                 [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)].any fun (x13 : ℕ) => x12 (Fin.ofNat (11 : ℕ) (x13 / (11 : ℕ))) && x12 (Fin.ofNat (11 : ℕ) (x13 % (11 : ℕ)));               (∀ (x12 : Fin (9 : ℕ) → Bool), x11 (x2.insertNth Bool.false x12) ≠ x11 (x2.insertNth Bool.true x12) → x3.eval (List.ofFn x12) = Bool.true) → ∃ (x13 : Fin (9 : ℕ) → Bool) (x14 : Bool), x4.eval (x3.wires (List.ofFn x13) ++ [x14 && x3.eval (List.ofFn x13)]) ≠ x11 (x2.insertNth x14 x13)) :=
  fun x1 x2 x3 x4 h1 hAO3 hAO4 hSz hOut1 hOut2 hCov =>
    Or.elim (Nat.eq_zero_or_pos x4.size)
      (fun h0 => hZeroX4 x1 x2 x3 x4 ⟨h1, h0, hAO3, hAO4, Nat.le_trans (Nat.le_add_right _ _) hSz, hOut1, hOut2, hCov⟩)
      (fun hPos => hPosX4 x1 x2 x3 x4 ⟨h1, hPos, hAO3, hAO4, hSz, hOut1, hOut2, hCov⟩)
