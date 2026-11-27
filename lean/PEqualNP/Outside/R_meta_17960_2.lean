import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17960_2
    (hCompileAO2 : ∀ (codes : List (Bool × ℕ × ℕ)),
      codes.length ≤ (63 : ℕ) →
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (26 : ℕ) + k ∧ g.2.2 < (26 : ℕ) + k) →
          have C : PEqualNP.CircuitLowerBounds.Circuit :=
            ⟨codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (0 : ℕ)⟩;
          PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ (∀ x6 ∈ C.gates, x6.inputs.Nodup))
    (hCodeWitness : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>
        have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);
        have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);
        if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4;
      ∃ (codes : List (Bool × ℕ × ℕ)) (x4 : ℕ) (x5 : ℕ),
        codes.length ≤ (63 : ℕ) ∧
          (∀ (k : ℕ), k < codes.length →
            have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
            g.2.1 ≠ g.2.2 ∧ g.2.1 < (26 : ℕ) + k ∧ g.2.2 < (26 : ℕ) + k) ∧
            x4 ≠ x5 ∧ x4 < (26 : ℕ) + codes.length ∧ x5 < (26 : ℕ) + codes.length ∧
              have C : PEqualNP.CircuitLowerBounds.Circuit :=
                ⟨codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (0 : ℕ)⟩;
              (∀ (x6 x7 : Fin (13 : ℕ)), x1 x6 x7 →
                have x9 : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x6) (Fin.natAdd (13 : ℕ) x7);
                PEqualNP.BlindGate.wireValue C (26 : ℕ) x9 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue C (26 : ℕ) x9 x5 = Bool.true) ∧
              ∀ (x6 : Bool) (x7 : Finset (Fin (13 : ℕ))), x7.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue C (26 : ℕ) (x2 x6 x7) (if x2 x6 x7 (13 : Fin ((13 : ℕ) + (13 : ℕ))) = Bool.true then x4 else x5) = Bool.false) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ),   x3.size ≤ (63 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x6 ∈ x3.gates, x6.inputs.Nodup) ∧         x4 ≠ x5 ∧           x4 < (26 : ℕ) + x3.size ∧             x5 < (26 : ℕ) + x3.size ∧               (∀ (x6 x7 : Fin (13 : ℕ)),                   x1 x6 x7 →                     have x9 : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x6) (Fin.natAdd (13 : ℕ) x7);                     PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x9 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x9 x5 = Bool.true) ∧                 ∀ (x6 : Bool) (x7 : Finset (Fin (13 : ℕ))), x7.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (x2 x6 x7) (if x2 x6 x7 (13 : Fin ((13 : ℕ) + (13 : ℕ))) = Bool.true then x4 else x5) = Bool.false) :=
  Exists.elim hCodeWitness fun codes h1 =>
  Exists.elim h1 fun w1 h2 =>
  Exists.elim h2 fun w2 h =>
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨codes.map (fun g => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (0 : ℕ)⟩
    let hc := hCompileAO2 codes h.1 h.2.1
    have hsz : C.size = codes.length := List.length_map _
    ⟨C, w1, w2, hsz ▸ h.1, hc.1, hc.2, h.2.2.1, hsz.symm ▸ h.2.2.2.1, hsz.symm ▸ h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
