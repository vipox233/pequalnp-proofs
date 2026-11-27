import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18763_3
    (hDiffEquiv :
      ∀ (a b : Fin (13 : ℕ)),
        ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ↔
          (a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ))))
    (hCircuitDiff :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ), x1.size ≤ (61 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧ x2 < (26 : ℕ) + x1.size ∧ x3 < (26 : ℕ) + x1.size ∧ x2 ≠ x3 ∧ x2 ≠ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x2 = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x6 ≠ (0 : Fin (13 : ℕ)) ∧ ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x3 = (x4 (0 : Fin (26 : ℕ)) || x4 (1 : Fin (26 : ℕ)) || x4 (3 : Fin (26 : ℕ)) || x4 (9 : Fin (26 : ℕ)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ), x1.size ≤ (61 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧ x2 < (26 : ℕ) + x1.size ∧ x3 < (26 : ℕ) + x1.size ∧ x2 ≠ x3 ∧ x2 ≠ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x2 = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x6 ≠ (0 : Fin (13 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x3 = (x4 (0 : Fin (26 : ℕ)) || x4 (1 : Fin (26 : ℕ)) || x4 (3 : Fin (26 : ℕ)) || x4 (9 : Fin (26 : ℕ)))) := by
  rcases hCircuitDiff with ⟨x1, x2, x3, hSz, hAO, hNd, h2, h3, hNe, h13, hSpec⟩
  refine ⟨x1, x2, x3, hSz, hAO, hNd, h2, h3, hNe, h13, fun x4 => ?_⟩
  rcases hSpec x4 with ⟨hiff, hw3⟩
  refine ⟨⟨fun hv => ?_, fun hex => ?_⟩, hw3⟩
  · rcases hiff.mp hv with ⟨x5, x6, h6, hd, ha, hb⟩
    exact ⟨x5, x6, h6, (hDiffEquiv x5 x6).mp hd, ha, hb⟩
  · rcases hex with ⟨x5, x6, h6, hd, ha, hb⟩
    exact hiff.mpr ⟨x5, x6, h6, (hDiffEquiv x5 x6).mpr hd, ha, hb⟩
