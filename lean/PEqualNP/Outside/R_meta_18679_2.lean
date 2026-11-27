import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18679_2
    (hStarCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),
        x1.size ≤ (22 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
        (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧
        x2 < (14 : ℕ) + x1.size ∧
        x2 ≠ (2 : ℕ) ∧
        ∀ (x : Fin (14 : ℕ) → Bool),
          PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x x2 = ((x (0 : Fin (14 : ℕ)) && (x (7 : Fin (14 : ℕ)) || x (11 : Fin (14 : ℕ)) || x (13 : Fin (14 : ℕ)))) || (x (1 : Fin (14 : ℕ)) && (x (7 : Fin (14 : ℕ)) || x (8 : Fin (14 : ℕ)) || x (12 : Fin (14 : ℕ)))) || (x (3 : Fin (14 : ℕ)) && (x (7 : Fin (14 : ℕ)) || x (9 : Fin (14 : ℕ)) || x (10 : Fin (14 : ℕ)))) || (x (4 : Fin (14 : ℕ)) && (x (8 : Fin (14 : ℕ)) || x (10 : Fin (14 : ℕ)) || x (11 : Fin (14 : ℕ)))) || (x (5 : Fin (14 : ℕ)) && (x (9 : Fin (14 : ℕ)) || x (11 : Fin (14 : ℕ)) || x (12 : Fin (14 : ℕ)))) || (x (6 : Fin (14 : ℕ)) && (x (10 : Fin (14 : ℕ)) || x (12 : Fin (14 : ℕ)) || x (13 : Fin (14 : ℕ))))))
    (hStarEquiv :
      ∀ (x : Fin (14 : ℕ) → Bool),
        ((x (0 : Fin (14 : ℕ)) && (x (7 : Fin (14 : ℕ)) || x (11 : Fin (14 : ℕ)) || x (13 : Fin (14 : ℕ)))) || (x (1 : Fin (14 : ℕ)) && (x (7 : Fin (14 : ℕ)) || x (8 : Fin (14 : ℕ)) || x (12 : Fin (14 : ℕ)))) || (x (3 : Fin (14 : ℕ)) && (x (7 : Fin (14 : ℕ)) || x (9 : Fin (14 : ℕ)) || x (10 : Fin (14 : ℕ)))) || (x (4 : Fin (14 : ℕ)) && (x (8 : Fin (14 : ℕ)) || x (10 : Fin (14 : ℕ)) || x (11 : Fin (14 : ℕ)))) || (x (5 : Fin (14 : ℕ)) && (x (9 : Fin (14 : ℕ)) || x (11 : Fin (14 : ℕ)) || x (12 : Fin (14 : ℕ)))) || (x (6 : Fin (14 : ℕ)) && (x (10 : Fin (14 : ℕ)) || x (12 : Fin (14 : ℕ)) || x (13 : Fin (14 : ℕ))))) = Bool.true ↔
          ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)),
            x4 ≠ (2 : Fin (7 : ℕ)) ∧
            (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧
            x (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧
            x (Fin.natAdd (7 : ℕ) x5) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧ x2 < (14 : ℕ) + x1.size ∧ x2 ≠ (2 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x3 x2 = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x4 ≠ (2 : Fin (7 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) := by
  obtain ⟨x1, x2, hSz, hAO, hNd, h2, h2Ne, hEv⟩ := hStarCircuit
  refine ⟨x1, x2, hSz, hAO, hNd, h2, h2Ne, fun x => ?_⟩
  exact ⟨fun h => (hStarEquiv x).mp ((hEv x).symm.trans h), fun h => (hEv x).trans ((hStarEquiv x).mpr h)⟩
