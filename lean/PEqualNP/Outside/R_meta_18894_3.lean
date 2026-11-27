import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18894_3
    (hCompileAO2 : ∀ (codes : List (Bool × ℕ × ℕ)) (out : ℕ),
      codes.length ≤ (50 : ℕ) →
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (26 : ℕ) + k ∧ g.2.2 < (26 : ℕ) + k) →
          have C : PEqualNP.CircuitLowerBounds.Circuit :=
            PEqualNP.CircuitLowerBounds.Circuit.mk
              (codes.map (fun (g : Bool × ℕ × ℕ) =>
                PEqualNP.CircuitLowerBounds.Gate.mk
                  (if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and)
                  [g.2.1, g.2.2]))
              out;
          PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ ∀ x5 ∈ C.gates, x5.inputs.Nodup)
    (hCodeWitness :
      have x1 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ));
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (x2 x3 x4 : Fin (13 : ℕ)) => x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ if x2 ∈ x1 then x3 = x2 else x3 ∉ x1;
      ∃ (codes : List (Bool × ℕ × ℕ)) (out : ℕ) (x4 : Fin (13 : ℕ) → ℕ),
        codes.length ≤ (50 : ℕ) ∧
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (26 : ℕ) + k ∧ g.2.2 < (26 : ℕ) + k) ∧
        out < (26 : ℕ) + codes.length ∧
        (∀ x5 ∈ x1, x4 x5 < (26 : ℕ) + codes.length ∧ x4 x5 ≠ ↑x5) ∧
        have x3 : PEqualNP.CircuitLowerBounds.Circuit :=
          PEqualNP.CircuitLowerBounds.Circuit.mk
            (codes.map (fun (g : Bool × ℕ × ℕ) =>
              PEqualNP.CircuitLowerBounds.Gate.mk
                (if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and)
                [g.2.1, g.2.2]))
            out;
        ∀ (x5 : Fin (13 : ℕ)),
          have x6 : ℕ := if x5 ∈ x1 then x4 x5 else out;
          (∀ (x7 x8 : Fin (13 : ℕ)), x2 x5 x7 x8 →
            PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.natAdd (13 : ℕ) x8 ∨ x5 ∉ x1 ∧ x10 = Fin.castAdd (13 : ℕ) x7)) x6 = Bool.true) ∧
          ∀ (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x7, x8 ∉ x1) → (x5 ∈ x1 → x7 = x1ᶜ) →
            PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x7 ∨ x11 ∈ x1)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide ¬∃ (x12 : Fin (13 : ℕ)), x2 x5 x12 x11 ∧ (x12 ∈ x7 ∨ x5 ∈ x1)) x10) x6 = Bool.false) :
    have x1 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)); let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 x4 : Fin (13 : ℕ)) => x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ if x2 ∈ x1 then x3 = x2 else x3 ∉ x1; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (13 : ℕ) → ℕ),   x3.size ≤ (50 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x5 ∈ x3.gates, x5.inputs.Nodup) ∧         x3.output < (26 : ℕ) + x3.size ∧           (∀ x5 ∈ x1, x4 x5 < (26 : ℕ) + x3.size ∧ x4 x5 ≠ ↑x5) ∧             ∀ (x5 : Fin (13 : ℕ)),               have x6 : ℕ := if x5 ∈ x1 then x4 x5 else x3.output;               (∀ (x7 x8 : Fin (13 : ℕ)), x2 x5 x7 x8 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.natAdd (13 : ℕ) x8 ∨ x5 ∉ x1 ∧ x10 = Fin.castAdd (13 : ℕ) x7)) x6 = Bool.true) ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x7, x8 ∉ x1) → (x5 ∈ x1 → x7 = x1ᶜ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x7 ∨ x11 ∈ x1)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide ¬∃ (x12 : Fin (13 : ℕ)), x2 x5 x12 x11 ∧ (x12 ∈ x7 ∨ x5 ∈ x1)) x10) x6 = Bool.false :=
  Exists.elim hCodeWitness fun codes h1 =>
    Exists.elim h1 fun out h2 =>
      Exists.elim h2 fun x4 h =>
        let C : PEqualNP.CircuitLowerBounds.Circuit :=
          PEqualNP.CircuitLowerBounds.Circuit.mk
            (codes.map (fun g =>
              PEqualNP.CircuitLowerBounds.Gate.mk
                (if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and)
                [g.2.1, g.2.2]))
            out
        let hc := hCompileAO2 codes out h.1 h.2.1
        have hsz : C.size = codes.length := List.length_map _
        ⟨C, x4, hsz ▸ h.1, hc.1, hc.2, hsz.symm ▸ h.2.2.1, hsz.symm ▸ h.2.2.2.1, h.2.2.2.2⟩
