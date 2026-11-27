import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18707_2
    (hLineEquiv :
      ∀ (f : Fin (13 : ℕ) → Bool) (b : Fin (13 : ℕ)),
        (f b || f (b + (1 : Fin (13 : ℕ))) || f (b + (3 : Fin (13 : ℕ))) || f (b + (9 : Fin (13 : ℕ)))) = Bool.true ↔
          ∃ (a : Fin (13 : ℕ)), ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ f a = Bool.true)
    (hCircuitBip :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ) (x4 : ℕ),
        x1.size ≤ (64 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
        (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧
        x1.output = (26 : ℕ) + x2 ∧
        x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧
        (∀ (x5 : Fin (26 : ℕ) → Bool),
          x1.eval (List.ofFn x5) = Bool.true ↔
            ∃ (a b : Fin (13 : ℕ)), ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x5 (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ x5 (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧
        ∃ (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ)),
          (x1.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = x5))).getD x3 Bool.false = Bool.true ∧
          (x1.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = x6))).getD x4 Bool.false = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ) (x4 : ℕ), x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x5 ∈ x1.gates, x5.inputs.Nodup) ∧ x1.output = (26 : ℕ) + x2 ∧ x1.gates[x2]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x3, x4] : PEqualNP.CircuitLowerBounds.Gate } ∧ (∀ (x5 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (13 : ℕ)), x5 (Fin.natAdd (13 : ℕ) x6) = Bool.true ∧ (x5 (Fin.castAdd (13 : ℕ) x6) || x5 (Fin.castAdd (13 : ℕ) (x6 + (1 : Fin (13 : ℕ)))) || x5 (Fin.castAdd (13 : ℕ) (x6 + (3 : Fin (13 : ℕ)))) || x5 (Fin.castAdd (13 : ℕ) (x6 + (9 : Fin (13 : ℕ))))) = Bool.true) ∧ ∃ (x5 : Fin (26 : ℕ)) (x6 : Fin (26 : ℕ)), (x1.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = x5))).getD x3 Bool.false = Bool.true ∧ (x1.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = x6))).getD x4 Bool.false = Bool.true) := by
  rcases hCircuitBip with ⟨x1, x2, x3, x4, hSz, hAO, hNd, hOut, hG, hSpec, hW⟩
  refine ⟨x1, x2, x3, x4, hSz, hAO, hNd, hOut, hG, fun x5 => ?_, hW⟩
  constructor
  · intro hev
    rcases (hSpec x5).mp hev with ⟨a, b, hab, ha, hb⟩
    exact ⟨b, hb, (hLineEquiv (fun i => x5 (Fin.castAdd (13 : ℕ) i)) b).mpr ⟨a, hab, ha⟩⟩
  · rintro ⟨b, hb, hor⟩
    rcases (hLineEquiv (fun i => x5 (Fin.castAdd (13 : ℕ) i)) b).mp hor with ⟨a, hab, ha⟩
    exact (hSpec x5).mpr ⟨a, b, hab, ha, hb⟩
