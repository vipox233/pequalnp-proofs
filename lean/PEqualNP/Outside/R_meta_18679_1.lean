import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18679_1
    (hTableEquiv :
      ∀ (i j : Fin (7 : ℕ)),
        (i ≠ (2 : Fin (7 : ℕ)) ∧ (i = j ∨ i = j + (1 : Fin (7 : ℕ)) ∨ i = j + (3 : Fin (7 : ℕ)))) ↔
        ([(81 : ℕ), (35 : ℕ), (0 : ℕ), (13 : ℕ), (26 : ℕ), (52 : ℕ), (104 : ℕ)].getD (i : ℕ) (0 : ℕ)).testBit (j : ℕ) = Bool.true)
    (hCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),
        x1.size ≤ (22 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
        (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧
        x2 < (14 : ℕ) + x1.size ∧
        x2 ≠ (2 : ℕ) ∧
        ∀ (x3 : Fin (14 : ℕ) → Bool),
          PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x3 x2 = Bool.true ↔
            ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)),
              ([(81 : ℕ), (35 : ℕ), (0 : ℕ), (13 : ℕ), (26 : ℕ), (52 : ℕ), (104 : ℕ)].getD (x4 : ℕ) (0 : ℕ)).testBit (x5 : ℕ) = Bool.true ∧
              x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧
              x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧ x2 < (14 : ℕ) + x1.size ∧ x2 ≠ (2 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x3 x2 = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x4 ≠ (2 : Fin (7 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) :=
  Exists.elim hCircuit (fun C hC =>
    Exists.elim hC (fun w hw =>
      ⟨C, w, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, fun x =>
        Iff.trans (hw.2.2.2.2.2 x)
          (Iff.intro
            (fun h => Exists.elim h (fun i hi => Exists.elim hi (fun j hj =>
              have hij := (hTableEquiv i j).mpr hj.1
              ⟨i, j, hij.1, hij.2, hj.2.1, hj.2.2⟩)))
            (fun h => Exists.elim h (fun i hi => Exists.elim hi (fun j hj =>
              ⟨i, j, (hTableEquiv i j).mp ⟨hj.1, hj.2.1⟩, hj.2.2.1, hj.2.2.2⟩))))⟩))
