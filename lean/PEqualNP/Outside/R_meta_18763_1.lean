import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18763_1
    (hCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),
        x1.size ≤ (61 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
        (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧
        x2 < (26 : ℕ) + x1.size ∧
        x3 < (26 : ℕ) + x1.size ∧
        x2 ≠ x3 ∧
        x2 ≠ (13 : ℕ) ∧
        ∀ (x4 : Fin (26 : ℕ) → Bool),
          (PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x2 = Bool.true ↔
            ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
              (([(0 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD x6.val (0 : ℕ)).testBit x5.val = Bool.true ∧
              x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧
              x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧
          PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x3 = (x4 (0 : Fin (26 : ℕ)) || x4 (1 : Fin (26 : ℕ)) || x4 (3 : Fin (26 : ℕ)) || x4 (9 : Fin (26 : ℕ))))
    (hTableEquiv :
      ∀ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
        (([(0 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)] : List ℕ).getD x6.val (0 : ℕ)).testBit x5.val = Bool.true ↔
          x6 ≠ (0 : Fin (13 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ)))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ), x1.size ≤ (61 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧ x2 < (26 : ℕ) + x1.size ∧ x3 < (26 : ℕ) + x1.size ∧ x2 ≠ x3 ∧ x2 ≠ (13 : ℕ) ∧ ∀ (x4 : Fin (26 : ℕ) → Bool), (PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x2 = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x6 ≠ (0 : Fin (13 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ PEqualNP.BlindGate.wireValue x1 (26 : ℕ) x4 x3 = (x4 (0 : Fin (26 : ℕ)) || x4 (1 : Fin (26 : ℕ)) || x4 (3 : Fin (26 : ℕ)) || x4 (9 : Fin (26 : ℕ)))) := by
  obtain ⟨x1, x2, x3, hSz, hAO, hNd, h2, h3, hNe, h2Ne, hEval⟩ := hCircuit
  refine ⟨x1, x2, x3, hSz, hAO, hNd, h2, h3, hNe, h2Ne, ?_⟩
  intro x4
  refine ⟨(hEval x4).1.trans (exists_congr (fun x5 => exists_congr (fun x6 => ?_))), (hEval x4).2⟩
  exact Iff.trans (and_congr_left' (hTableEquiv x5 x6)) and_assoc
