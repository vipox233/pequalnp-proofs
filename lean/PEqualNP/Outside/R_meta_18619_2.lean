import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18619_2
    (hCompileAO2 : ∀ (codes : List (Bool × ℕ × ℕ)),
      codes.length ≤ (42 : ℕ) →
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (27 : ℕ) + k ∧ g.2.2 < (27 : ℕ) + k) →
          have C : PEqualNP.CircuitLowerBounds.Circuit :=
            ⟨codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (26 : ℕ) + codes.length⟩;
          PEqualNP.TopForm.IsAO2 (27 : ℕ) C ∧ (∀ x2 ∈ C.gates, x2.inputs.Nodup))
    (hCodeWitness : ∃ (codes : List (Bool × ℕ × ℕ)),
      (1 : ℕ) ≤ codes.length ∧
        codes.length ≤ (42 : ℕ) ∧
          (∀ (k : ℕ), k < codes.length →
            have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
            g.2.1 ≠ g.2.2 ∧ g.2.1 < (27 : ℕ) + k ∧ g.2.2 < (27 : ℕ) + k) ∧
            ∀ (x2 : Fin (26 : ℕ) → Bool),
              (PEqualNP.CircuitLowerBounds.Circuit.mk
                (codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩))
                ((26 : ℕ) + codes.length)).eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔
                ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)),
                  x3 ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] ∧
                    x4 ≠ (1 : Fin (13 : ℕ)) ∧
                      (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧
                        x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (42 : ℕ) ∧ (27 : ℕ) ≤ x1.output ∧ x1.output < (27 : ℕ) + x1.size ∧ PEqualNP.TopForm.IsAO2 (27 : ℕ) x1 ∧ (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧ ∀ (x2 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x2 ++ [x2 (1 : Fin (26 : ℕ)) || x2 (2 : Fin (26 : ℕ))]) = Bool.true ↔ ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ [(0 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (5 : Fin (13 : ℕ)), (6 : Fin (13 : ℕ)), (7 : Fin (13 : ℕ)), (8 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ)), (11 : Fin (13 : ℕ)), (12 : Fin (13 : ℕ))] ∧ x4 ≠ (1 : Fin (13 : ℕ)) ∧ (x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ))) ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true) :=
  Exists.elim hCodeWitness fun codes h =>
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨codes.map (fun g => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (26 : ℕ) + codes.length⟩
    let hc := hCompileAO2 codes h.2.1 h.2.2.1
    have hsz : C.size = codes.length := List.length_map _
    ⟨C, hsz ▸ h.2.1, Nat.add_le_add_left h.1 (26 : ℕ), hsz.symm ▸ Nat.add_lt_add_right (Nat.lt_succ_self (26 : ℕ)) codes.length, hc.1, hc.2, h.2.2.2⟩
