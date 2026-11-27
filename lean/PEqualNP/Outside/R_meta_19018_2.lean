import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_19018_2
    (hConeBounds :
      ∀ (n : ℕ) (c : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ),
        PEqualNP.EdgeOwnership.InCone n c a b → a < b ∧ b < c.gates.length)
    (hNoOrderedChain :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;
        have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
        have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));
        have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
        have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
        have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;
        x1.size ≤ (64 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
        (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧
        (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔
          ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧
        (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧
        ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ),
          x11 < x12 ∧ x12 < x13 ∧ x13 < x1.gates.length ∧ x1.output < (26 : ℕ) + x1.gates.length ∧
          x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = Bool.true ∧ x5 x12 ∧ x4 x12 x8 = Bool.false ∧ x10 x13 x8 ∧ (26 : ℕ) ≤ x1.output) :
    (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → Prop := fun (x5 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (26 : ℕ) + x6 = x1.output ∨ x3 x6 (x1.output - (26 : ℕ));     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x10 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x10 : ℕ) (x11 : Fin (26 : ℕ) → Bool) => x5 x10 ∧ x6 x10 ∧ x4 x10 x9 = Bool.true ∧ ∀ (x12 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x10 x12) x11 = Bool.false;     x1.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧ (∀ x11 ∈ x1.gates, x11.inputs.Nodup) ∧ (∀ (x11 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x11) = Bool.true ↔ ∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x12 - x13 ∈ x2 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧ (∃ x11 < x1.gates.length, x5 x11 ∧ ∃ (x12 : Fin (26 : ℕ) → Bool), x4 x11 x12 = Bool.true ∧ x1.eval (List.ofFn x12) = Bool.false) ∧ ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x3 x11 x12 ∧ x3 x12 x13 ∧ x10 x11 x7 ∧ x4 x11 x8 = Bool.true ∧ x5 x12 ∧ x4 x12 x8 = Bool.false ∧ x10 x13 x8 ∧ (26 : ℕ) ≤ x1.output) :=
  fun hEx =>
    Exists.elim hEx fun x1 h1 =>
      Exists.elim h1.2.2.2.2.2 fun a ha =>
        Exists.elim ha fun b hb =>
          Exists.elim hb fun d hd =>
            hNoOrderedChain
              ⟨x1, h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2.1,
                a, b, d,
                (hConeBounds 26 x1 a b hd.1).1,
                (hConeBounds 26 x1 b d hd.2.1).1,
                (hConeBounds 26 x1 b d hd.2.1).2,
                Or.elim hd.2.2.2.2.2.2.1.2.1
                  (fun hEq => hEq ▸ Nat.add_lt_add_left (hConeBounds 26 x1 b d hd.2.1).2 26)
                  (fun hInO =>
                    Nat.add_sub_of_le hd.2.2.2.2.2.2.2 ▸
                      Nat.add_lt_add_left (hConeBounds 26 x1 d (x1.output - 26) hInO).2 26),
                hd⟩
