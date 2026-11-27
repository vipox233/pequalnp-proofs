import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18679_3
    (hCompileAO2 : ∀ (codes : List (Bool × ℕ × ℕ)),
      codes.length ≤ (22 : ℕ) →
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (14 : ℕ) + k ∧ g.2.2 < (14 : ℕ) + k) →
          have C : PEqualNP.CircuitLowerBounds.Circuit :=
            ⟨codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (0 : ℕ)⟩;
          PEqualNP.TopForm.IsAO2 (14 : ℕ) C ∧ (∀ x3 ∈ C.gates, x3.inputs.Nodup))
    (hCodeWitness : ∃ (codes : List (Bool × ℕ × ℕ)) (x2 : ℕ),
      codes.length ≤ (22 : ℕ) ∧
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (14 : ℕ) + k ∧ g.2.2 < (14 : ℕ) + k) ∧
          x2 < (14 : ℕ) + codes.length ∧ x2 ≠ (2 : ℕ) ∧
            ∀ (x3 : Fin (14 : ℕ) → Bool),
              PEqualNP.BlindGate.wireValue
                (PEqualNP.CircuitLowerBounds.Circuit.mk
                  (codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩))
                  (0 : ℕ)) (14 : ℕ) x3 x2 = Bool.true ↔
                ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)),
                  x4 ≠ (2 : Fin (7 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧
                    x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), x1.size ≤ (22 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ x3 ∈ x1.gates, x3.inputs.Nodup) ∧ x2 < (14 : ℕ) + x1.size ∧ x2 ≠ (2 : ℕ) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x3 x2 = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x4 ≠ (2 : Fin (7 : ℕ)) ∧ (x4 = x5 ∨ x4 = x5 + (1 : Fin (7 : ℕ)) ∨ x4 = x5 + (3 : Fin (7 : ℕ))) ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true) :=
  Exists.elim hCodeWitness fun codes h1 =>
  Exists.elim h1 fun x2 h =>
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨codes.map (fun g => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (0 : ℕ)⟩
    let hc := hCompileAO2 codes h.1 h.2.1
    have hsz : C.size = codes.length := List.length_map _
    ⟨C, x2, hsz ▸ h.1, hc.1, hc.2, hsz.symm ▸ h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
