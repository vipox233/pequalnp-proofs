import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18810_2
    (hCondEquiv :
      ∀ (x5 x6 : Fin (13 : ℕ)),
        (!(Decidable.decide (x6 = x5) || Decidable.decide (x6 + (1 : Fin (13 : ℕ)) = x5) || Decidable.decide (x6 + (3 : Fin (13 : ℕ)) = x5) || Decidable.decide (x6 + (9 : Fin (13 : ℕ)) = x5))) = Bool.false ↔
          ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])
    (hExistCircuit :
      have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))));
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4;
      have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x4.size ≤ (62 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧
        (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧
        (∀ (x5 x6 : Fin (13 : ℕ)), ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧
        (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧
        x4.output < (26 : ℕ) + x4.size ∧
        x4.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = (0 : ℕ))) = Bool.false ∧
        x4.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = (13 : ℕ))) = Bool.false) :
    (have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ (62 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧ (∀ x5 ∈ x4.gates, x5.inputs.Nodup) ∧ (∀ (x5 x6 : Fin (13 : ℕ)), x1 (x3 x5) x6 = Bool.false → x4.eval (x2 (x3 x5) (x3 x6)) = Bool.true) ∧ (∀ (x5 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x5) ≤ (3 : ℕ) → x4.eval (x2 x5 (x1 x5)) = Bool.false ∧ x4.eval (x2 (fun (x7 : Fin (13 : ℕ)) => !(x5 x7 || x5 (x7 - (1 : Fin (13 : ℕ))) || x5 (x7 - (3 : Fin (13 : ℕ))) || x5 (x7 - (9 : Fin (13 : ℕ))))) x5) = Bool.false) ∧ x4.output < (26 : ℕ) + x4.size ∧ ∀ (x5 : Bool), x4.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => Decidable.decide (↑x6 = if x5 = Bool.true then (13 : ℕ) else (0 : ℕ))) = Bool.false) := by
  rcases hExistCircuit with ⟨C, hSz, hAO, hNd, hPos, hNeg, hOut, hS0, hS13⟩
  refine ⟨C, hSz, hAO, hNd, fun x5 x6 hx => hPos x5 x6 ((hCondEquiv x5 x6).mp hx), hNeg, hOut, fun b => ?_⟩
  cases b
  · simpa using hS0
  · simpa using hS13
