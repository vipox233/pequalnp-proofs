import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17858_1
    (hTableEquiv : ∀ (a b : Fin (7 : ℕ)),
      ((7 : ℕ) * (a : ℕ) + (b : ℕ)) ∈ [(0 : ℕ), (4 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (12 : ℕ), (15 : ℕ), (16 : ℕ), (20 : ℕ), (21 : ℕ), (23 : ℕ), (24 : ℕ), (29 : ℕ), (31 : ℕ), (32 : ℕ), (37 : ℕ), (39 : ℕ), (40 : ℕ), (45 : ℕ), (47 : ℕ), (48 : ℕ)] ↔
      (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))))
    (hCircuit : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (22 : ℕ) ∧
      PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
      (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧
      (14 : ℕ) ≤ x1.output ∧
      x1.output < (14 : ℕ) + x1.size ∧
      (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true →
        ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)),
          ((7 : ℕ) * (x4 : ℕ) + (x5 : ℕ)) ∈ [(0 : ℕ), (4 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (12 : ℕ), (15 : ℕ), (16 : ℕ), (20 : ℕ), (21 : ℕ), (23 : ℕ), (24 : ℕ), (29 : ℕ), (31 : ℕ), (32 : ℕ), (37 : ℕ), (39 : ℕ), (40 : ℕ), (45 : ℕ), (47 : ℕ), (48 : ℕ)] ∧
          x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧
          x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧
      (∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) →
        ((7 : ℕ) * (x2 : ℕ) + (x3 : ℕ)) ∈ [(0 : ℕ), (4 : ℕ), (6 : ℕ), (7 : ℕ), (8 : ℕ), (12 : ℕ), (15 : ℕ), (16 : ℕ), (20 : ℕ), (21 : ℕ), (23 : ℕ), (24 : ℕ), (29 : ℕ), (31 : ℕ), (32 : ℕ), (37 : ℕ), (39 : ℕ), (40 : ℕ), (45 : ℕ), (47 : ℕ), (48 : ℕ)] →
        x1.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) → x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) := by
  exact Exists.elim hCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1,
      fun x hx =>
        Exists.elim (hC.2.2.2.2.2.1 x hx) fun a ha =>
          Exists.elim ha fun b hb =>
            ⟨a, b, (hTableEquiv a b).mp hb.1, hb.2.1, hb.2.2⟩,
      fun a b hb1 hrel => hC.2.2.2.2.2.2 a b hb1 ((hTableEquiv a b).mpr hrel)⟩
