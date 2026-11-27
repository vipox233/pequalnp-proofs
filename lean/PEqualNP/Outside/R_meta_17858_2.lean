import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17858_2
    (hStarEquiv :
      have fano6 : (Fin (14 : ℕ) → Bool) → Bool := fun x =>
        (x (7 : Fin (14 : ℕ)) && (x (0 : Fin (14 : ℕ)) || x (1 : Fin (14 : ℕ)) || x (3 : Fin (14 : ℕ)))) ||
        (x (9 : Fin (14 : ℕ)) && (x (2 : Fin (14 : ℕ)) || x (3 : Fin (14 : ℕ)) || x (5 : Fin (14 : ℕ)))) ||
        (x (10 : Fin (14 : ℕ)) && (x (3 : Fin (14 : ℕ)) || x (4 : Fin (14 : ℕ)) || x (6 : Fin (14 : ℕ)))) ||
        (x (11 : Fin (14 : ℕ)) && (x (4 : Fin (14 : ℕ)) || x (5 : Fin (14 : ℕ)) || x (0 : Fin (14 : ℕ)))) ||
        (x (12 : Fin (14 : ℕ)) && (x (5 : Fin (14 : ℕ)) || x (6 : Fin (14 : ℕ)) || x (1 : Fin (14 : ℕ)))) ||
        (x (13 : Fin (14 : ℕ)) && (x (6 : Fin (14 : ℕ)) || x (0 : Fin (14 : ℕ)) || x (2 : Fin (14 : ℕ))));
      (∀ (x : Fin (14 : ℕ) → Bool),
        ((x (8 : Fin (14 : ℕ)) && (x (1 : Fin (14 : ℕ)) || x (2 : Fin (14 : ℕ)) || x (4 : Fin (14 : ℕ)))) || fano6 x) = Bool.true →
        ∃ (a b : Fin (7 : ℕ)),
          (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))) ∧
          x (Fin.castAdd (7 : ℕ) a) = Bool.true ∧
          x (Fin.natAdd (7 : ℕ) b) = Bool.true) ∧
      (∀ (a b : Fin (7 : ℕ)),
        b ≠ (1 : Fin (7 : ℕ)) →
        (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))) →
        fano6 (fun k => Decidable.decide (k = Fin.castAdd (7 : ℕ) a ∨ k = Fin.natAdd (7 : ℕ) b)) = Bool.true))
    (hStarCircuit :
      have fano6 : (Fin (14 : ℕ) → Bool) → Bool := fun x =>
        (x (7 : Fin (14 : ℕ)) && (x (0 : Fin (14 : ℕ)) || x (1 : Fin (14 : ℕ)) || x (3 : Fin (14 : ℕ)))) ||
        (x (9 : Fin (14 : ℕ)) && (x (2 : Fin (14 : ℕ)) || x (3 : Fin (14 : ℕ)) || x (5 : Fin (14 : ℕ)))) ||
        (x (10 : Fin (14 : ℕ)) && (x (3 : Fin (14 : ℕ)) || x (4 : Fin (14 : ℕ)) || x (6 : Fin (14 : ℕ)))) ||
        (x (11 : Fin (14 : ℕ)) && (x (4 : Fin (14 : ℕ)) || x (5 : Fin (14 : ℕ)) || x (0 : Fin (14 : ℕ)))) ||
        (x (12 : Fin (14 : ℕ)) && (x (5 : Fin (14 : ℕ)) || x (6 : Fin (14 : ℕ)) || x (1 : Fin (14 : ℕ)))) ||
        (x (13 : Fin (14 : ℕ)) && (x (6 : Fin (14 : ℕ)) || x (0 : Fin (14 : ℕ)) || x (2 : Fin (14 : ℕ))));
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (22 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
        (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧
        (14 : ℕ) ≤ x1.output ∧
        x1.output < (14 : ℕ) + x1.size ∧
        ∀ (x2 : Fin (14 : ℕ) → Bool),
          (x1.eval (List.ofFn x2) = Bool.true →
            ((x2 (8 : Fin (14 : ℕ)) && (x2 (1 : Fin (14 : ℕ)) || x2 (2 : Fin (14 : ℕ)) || x2 (4 : Fin (14 : ℕ)))) || fano6 x2) = Bool.true) ∧
          (fano6 x2 = Bool.true → x1.eval (List.ofFn x2) = Bool.true)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ (14 : ℕ) ≤ x1.output ∧ x1.output < (14 : ℕ) + x1.size ∧ (∀ (x2 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x2) = Bool.true → ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x5) = Bool.true) ∧ ∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) → x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) :=
  Exists.elim hStarCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1, hC.2.2.2.2.1,
      fun x hx => hStarEquiv.1 x ((hC.2.2.2.2.2 x).1 hx),
      fun a b hb hab => (hC.2.2.2.2.2 _).2 (hStarEquiv.2 a b hb hab)⟩
