import PEqualNP.Defs

-- Reduce unbounded ℕ quantification in L-meta-8277 to bounded modular inputs (x6 < 64, x7 < 2048).
theorem PEqualNP.Outside.R_meta_8277_1
    (hInputPeriod :
      have x1 : List ℕ := [(29 : ℕ), (225 : ℕ), (1793 : ℕ), (294 : ℕ), (586 : ℕ), (1170 : ℕ)];
      have x2 : List ℕ := [(3 : ℕ), (40 : ℕ), (1064 : ℕ), (272 : ℕ), (336 : ℕ), (516 : ℕ), (644 : ℕ), (48 : ℕ), (560 : ℕ), (264 : ℕ), (392 : ℕ), (68 : ℕ), (1092 : ℕ)];
      have x3 : ℕ → ℕ → List Bool := fun (x3 x4 : ℕ) =>
        List.map x3.testBit (List.range (6 : ℕ)) ++ List.map x4.testBit (List.range (11 : ℕ)) ++
          List.map (fun (x5 : ℕ) => Decidable.decide (x4 &&& x5 ≠ (0 : ℕ))) x2;
      ∀ (x6 x7 : ℕ), x3 x6 x7 = x3 (x6 % (64 : ℕ)) (x7 % (2048 : ℕ)))
    (hFiniteWitness :
      have x1 : List ℕ := [(29 : ℕ), (225 : ℕ), (1793 : ℕ), (294 : ℕ), (586 : ℕ), (1170 : ℕ)];
      have x2 : List ℕ := [(3 : ℕ), (40 : ℕ), (1064 : ℕ), (272 : ℕ), (336 : ℕ), (516 : ℕ), (644 : ℕ), (48 : ℕ), (560 : ℕ), (264 : ℕ), (392 : ℕ), (68 : ℕ), (1092 : ℕ)];
      have x3 : ℕ → ℕ → List Bool := fun (x3 x4 : ℕ) =>
        List.map x3.testBit (List.range (6 : ℕ)) ++ List.map x4.testBit (List.range (11 : ℕ)) ++
          List.map (fun (x5 : ℕ) => Decidable.decide (x4 &&& x5 ≠ (0 : ℕ))) x2;
      have x4 : ℕ → ℕ := fun (x4 : ℕ) => (2 : ℕ) ^ x4;
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 (30 : ℕ) x5 ∧
        x5.size = (28 : ℕ) ∧
        x5.output = (57 : ℕ) ∧
        (∀ (x6 : Fin (6 : ℕ)) (x7 : Fin (11 : ℕ)),
          (x1.getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true → x5.eval (x3 (x4 ↑x6) (x4 ↑x7)) = Bool.true) ∧
        ∀ (x6 x7 : ℕ),
          x6 < (64 : ℕ) →
          x7 < (2048 : ℕ) →
          x6 &&& (7 : ℕ) ≠ (7 : ℕ) →
          x6 &&& (56 : ℕ) ≠ (56 : ℕ) →
          (∀ x10 ∈ x1 ++ x2, (List.filter (x7 &&& x10).testBit (List.range (11 : ℕ))).length ≤ (2 : ℕ)) →
          (∀ (x11 : Fin (6 : ℕ)), x6.testBit ↑x11 = Bool.true → x7 &&& x1.getD ↑x11 (0 : ℕ) = (0 : ℕ)) →
          x5.eval (x3 x6 x7) = Bool.false) :
    have x1 : List ℕ := [(29 : ℕ), (225 : ℕ), (1793 : ℕ), (294 : ℕ), (586 : ℕ), (1170 : ℕ)];
    have x2 : List ℕ := [(3 : ℕ), (40 : ℕ), (1064 : ℕ), (272 : ℕ), (336 : ℕ), (516 : ℕ), (644 : ℕ), (48 : ℕ), (560 : ℕ), (264 : ℕ), (392 : ℕ), (68 : ℕ), (1092 : ℕ)];
    have x3 : ℕ → ℕ → List Bool := fun (x3 x4 : ℕ) => List.map x3.testBit (List.range (6 : ℕ)) ++ List.map x4.testBit (List.range (11 : ℕ)) ++ List.map (fun (x5 : ℕ) => Decidable.decide (x4 &&& x5 ≠ (0 : ℕ))) x2;
    have x4 : ℕ → ℕ := fun (x4 : ℕ) => (2 : ℕ) ^ x4;
    ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (30 : ℕ) x5 ∧
      x5.size = (28 : ℕ) ∧
      x5.output = (57 : ℕ) ∧
      (∀ (x6 : Fin (6 : ℕ)) (x7 : Fin (11 : ℕ)), (x1.getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true → x5.eval (x3 (x4 ↑x6) (x4 ↑x7)) = Bool.true) ∧
      ∀ (x6 x7 : ℕ),
        x6 &&& (7 : ℕ) ≠ (7 : ℕ) →
        x6 &&& (56 : ℕ) ≠ (56 : ℕ) →
        (∀ x10 ∈ x1 ++ x2, (List.filter (x7 &&& x10).testBit (List.range (11 : ℕ))).length ≤ (2 : ℕ)) →
        (∀ (x11 : Fin (6 : ℕ)), x6.testBit ↑x11 = Bool.true → x7 &&& x1.getD ↑x11 (0 : ℕ) = (0 : ℕ)) →
        x5.eval (x3 x6 x7) = Bool.false := by
  intro x1 x2 x3 x4
  rcases hFiniteWitness with ⟨C, hAO, hsz, hout, hpos, hneg⟩
  refine ⟨C, hAO, hsz, hout, hpos, ?_⟩
  intro x6 x7 h7 h56 hfilt hdisj
  have hmask : ∀ (a b n : ℕ), b < 2 ^ n → (a % 2 ^ n) &&& b = a &&& b := by
    intro a b n hb
    apply Nat.eq_of_testBit_eq
    intro k
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
    by_cases hk : k < n
    · simp [hk]
    · have hbf : b.testBit k = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hk)))
      simp [hk, hbf]
  have hm_lt : ∀ m ∈ x1 ++ x2, m < 2048 := by decide
  have hx6_7 : (x6 % 64) &&& 7 = x6 &&& 7 := hmask x6 7 6 (by decide)
  have hx6_56 : (x6 % 64) &&& 56 = x6 &&& 56 := hmask x6 56 6 (by decide)
  have hx7_m : ∀ m ∈ x1 ++ x2, (x7 % 2048) &&& m = x7 &&& m :=
    fun m hm => hmask x7 m 11 (hm_lt m hm)
  have hx6_bit : ∀ i : Fin 6, (x6 % 64).testBit i.val = x6.testBit i.val := by
    intro i
    change (x6 % 2 ^ 6).testBit i.val = x6.testBit i.val
    rw [Nat.testBit_mod_two_pow]
    simp [i.isLt]
  have hper : x3 x6 x7 = x3 (x6 % 64) (x7 % 2048) := hInputPeriod x6 x7
  rw [hper]
  refine hneg (x6 % 64) (x7 % 2048) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
    (by rw [hx6_7]; exact h7)
    (by rw [hx6_56]; exact h56)
    (fun m hm => by rw [hx7_m m hm]; exact hfilt m hm)
    (fun i hi => by
      rw [hx6_bit i] at hi
      rw [hx7_m (x1.getD i.val 0) (by
        have hlen : i.val < x1.length := by simp [x1]
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
        exact List.mem_append_left _ (List.getElem_mem hlen))]
      exact hdisj i hi)
