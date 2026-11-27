import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18810_1
    (hFullCircuit :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size ≤ (62 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        C.output < (26 : ℕ) + C.size ∧
        ∀ (a b : Fin (13 : ℕ) → Bool),
          C.eval (List.ofFn fun (i : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases a b i) =
            Decidable.decide (∃ (p l : Fin (13 : ℕ)),
              (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ)) ∨ p = l + (9 : Fin (13 : ℕ))) ∧
                a p = Bool.true ∧ b l = Bool.true))
    (hTestsOfFull :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a b : Fin (13 : ℕ) → Bool),
          C.eval (List.ofFn fun (i : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases a b i) =
            Decidable.decide (∃ (p l : Fin (13 : ℕ)),
              (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ)) ∨ p = l + (9 : Fin (13 : ℕ))) ∧
                a p = Bool.true ∧ b l = Bool.true)) →
        have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))));
        have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4;
        have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
        (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → C.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧
        (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) →
          C.eval (x2 x5 (x1 x5)) = Bool.false ∧
          C.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧
        ∀ (x5 : Bool), C.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ))) = Bool.false) :
    (have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (62 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧ (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧ x4.output < (26 : ℕ) + x4.size ∧ ∀ (x5 : Bool), x4.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ))) = Bool.false) :=
  Exists.elim hFullCircuit fun C hC =>
    ⟨C, hC.1, hC.2.1, hC.2.2.1,
      (hTestsOfFull C hC.2.2.2.2).1,
      (hTestsOfFull C hC.2.2.2.2).2.1,
      hC.2.2.2.1,
      (hTestsOfFull C hC.2.2.2.2).2.2⟩
