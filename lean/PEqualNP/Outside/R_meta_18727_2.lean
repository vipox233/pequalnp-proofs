import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18727_2
    (hDiffEquiv :
      ∀ (a b : Fin (13 : ℕ)),
        ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔
          (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))))
    (hCircuitDiff :
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3);
      have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))];
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x4.size ≤ (28 : ℕ) ∧
        (27 : ℕ) ≤ x4.output ∧
        x4.output < (27 : ℕ) + x4.size ∧
        PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧
        (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧
        (∀ (x5 x6 : Fin (13 : ℕ)),
          x6 ∈ [(12 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ))] →
          ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] →
          x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧
        ∀ (x5 : Fin (26 : ℕ) → Bool),
          x4.eval (x3 x5) = Bool.true →
          ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)),
            ↑(x7 - x8) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
            x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧
            x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (26 : ℕ) → Bool := fun (x2 x3 : Fin (13 : ℕ)) (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (13 : ℕ) x3); have x3 : (Fin (26 : ℕ) → Bool) → List Bool := fun (x3 : Fin (26 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (0 : Fin (26 : ℕ)) || x3 (1 : Fin (26 : ℕ))]; ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (28 : ℕ) ∧ (27 : ℕ) ≤ x4.output ∧ x4.output < (27 : ℕ) + x4.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x6 ∈ [(12 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (4 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (10 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ))] → x1 x5 x6 → x4.eval (x3 (x2 x5 x6)) = Bool.true) ∧ ∀ (x5 : Fin (26 : ℕ) → Bool), x4.eval (x3 x5) = Bool.true → ∃ (x7 : Fin (13 : ℕ)) (x8 : Fin (13 : ℕ)), x1 x7 x8 ∧ x5 (Fin.castAdd (13 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) x8) = Bool.true) :=
  Exists.elim hCircuitDiff fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1,
      fun a b hb hab => hC.2.2.2.2.2.1 a b hb ((hDiffEquiv a b).mpr hab),
      fun x hx =>
        Exists.elim (hC.2.2.2.2.2.2 x hx) fun a ha =>
          Exists.elim ha fun b hb =>
            ⟨a, b, (hDiffEquiv a b).mp hb.1, hb.2.1, hb.2.2⟩⟩
