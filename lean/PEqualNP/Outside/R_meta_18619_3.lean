import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18619_3
    (hMono : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.EdgeOwnership.AndOrOnly C →
        ∀ (x y : List Bool),
          x.length = y.length →
            (∀ (i : ℕ), i < x.length → x.getD i Bool.false = Bool.true → y.getD i Bool.false = Bool.true) →
              C.eval x = Bool.true → C.eval y = Bool.true)
    (hPosNeg :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (42 : ℕ) ∧
          (27 : ℕ) ≤ x1.output ∧
            x1.output < (27 : ℕ) + x1.size ∧
              PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧
                (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧
                  (∀ (x3 x4 : Fin (13 : ℕ)),
                    x3 ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] →
                      x4 ≠ (1 : Fin (13 : ℕ)) →
                        (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) →
                          have p : Fin (26 : ℕ) → Bool := fun (i : Fin (26 : ℕ)) => Decidable.decide (i = Fin.castAdd (13 : ℕ) x3 ∨ i = Fin.natAdd (13 : ℕ) x4);
                          x1.eval (List.ofFn p ++ [p (1 : Fin (26 : ℕ)) || p (2 : Fin (26 : ℕ))]) = Bool.true) ∧
                    ∀ (x2 : Fin (26 : ℕ) → Bool),
                      x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true →
                        ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)),
                          x3 ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] ∧
                            x4 ≠ (1 : Fin (13 : ℕ)) ∧
                              (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧
                                x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (42 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true := by
  rcases hPosNeg with ⟨x1, hsz, hlo, hhi, hAO, hnd, hPos, hNeg⟩
  refine ⟨x1, hsz, hlo, hhi, hAO, hnd, fun x2 => ⟨hNeg x2, ?_⟩⟩
  rintro ⟨x3, x4, hx3, hx4, hinc, ht3, ht4⟩
  let p : Fin 26 → Bool := fun i => decide (i = Fin.castAdd 13 x3 ∨ i = Fin.natAdd 13 x4)
  refine hMono x1 hAO.1 (List.ofFn p ++ [p 1 || p 2]) (List.ofFn x2 ++ [x2 1 || x2 2]) ?_ ?_ (hPos x3 x4 hx3 hx4 hinc)
  · simp
  · intro i hi hget
    have hi27 : i < 27 := by simpa using hi
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi27) with hi26 | rfl
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hi26] : i < (List.ofFn p).length), List.getElem?_append_left (by simp [hi26] : i < (List.ofFn x2).length), List.getElem?_ofFn, hi26, dite_true, Option.getD_some] at hget ⊢
      rcases decide_eq_true_eq.mp hget with h | h <;> rw [h] <;> assumption
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp : (List.ofFn p).length ≤ 26), List.getElem?_append_right (by simp : (List.ofFn x2).length ≤ 26), List.length_ofFn, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hget ⊢
      rcases Bool.or_eq_true_iff.mp hget with h | h
      · rcases decide_eq_true_eq.mp h with h' | h'
        · exact Bool.or_eq_true_iff.mpr (Or.inl (h' ▸ ht3))
        · exact Bool.or_eq_true_iff.mpr (Or.inl (h' ▸ ht4))
      · rcases decide_eq_true_eq.mp h with h' | h'
        · exact Bool.or_eq_true_iff.mpr (Or.inr (h' ▸ ht3))
        · exact Bool.or_eq_true_iff.mpr (Or.inr (h' ▸ ht4))
