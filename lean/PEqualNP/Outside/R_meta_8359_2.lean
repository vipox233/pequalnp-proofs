import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8359_2
    (hLeftZero :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x14 x15 x25 : ℕ),
        have x7 : ℕ → Bool := fun (w : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x8 : ℕ → Bool := fun (w : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));
        have x9 : ℕ → Bool := fun (w : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 w (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;
        have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;
        have x12 : ℕ → Prop := fun (g : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x7 ((14 : ℕ) + g) = Bool.true ∧ x8 ((14 : ℕ) + g) = Bool.false ∧ x9 ((14 : ℕ) + g) = Bool.false;
        (x1.size ≤ (27 : ℕ) ∧
          x1.output + (1 : ℕ) = (14 : ℕ) + x1.size ∧
          PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
          (∀ g ∈ x1.gates, g.inputs.Nodup) ∧
          (∀ (f : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn f) = Bool.true ↔
            ∃ (a b : Fin (7 : ℕ)), (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))) ∧
              f (Fin.castAdd (7 : ℕ) a) = Bool.true ∧ f (Fin.natAdd (7 : ℕ) b) = Bool.true) ∧
          x14 < x15 ∧ ¬x11 x14 x15 ∧ ¬x11 x15 x14 ∧
          x11 x14 (x1.size - (1 : ℕ)) ∧ x11 x15 (x1.size - (1 : ℕ)) ∧
          x12 x14 ∧ x12 x15 ∧
          x12 x25 ∧ (∀ (b : Fin (2 : ℕ)), x8 (x10 x25 b) = Bool.true ∨ x9 (x10 x25 b) = Bool.true) ∧
          x11 x25 x14 ∧ x11 x25 x15 ∧
          (∀ (b : Fin (2 : ℕ)), x8 (x10 x14 b) = Bool.false ∧ x9 (x10 x14 b) = Bool.false) ∧
          (∀ (b : Fin (2 : ℕ)), x9 (x10 x15 b) = Bool.false)) →
        False)
    (hRightZero :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x14 x15 x25 : ℕ),
        have x7 : ℕ → Bool := fun (w : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x8 : ℕ → Bool := fun (w : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 w (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));
        have x9 : ℕ → Bool := fun (w : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 w (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));
        have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;
        have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;
        have x12 : ℕ → Prop := fun (g : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x7 ((14 : ℕ) + g) = Bool.true ∧ x8 ((14 : ℕ) + g) = Bool.false ∧ x9 ((14 : ℕ) + g) = Bool.false;
        (x1.size ≤ (27 : ℕ) ∧
          x1.output + (1 : ℕ) = (14 : ℕ) + x1.size ∧
          PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧
          (∀ g ∈ x1.gates, g.inputs.Nodup) ∧
          (∀ (f : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn f) = Bool.true ↔
            ∃ (a b : Fin (7 : ℕ)), (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))) ∧
              f (Fin.castAdd (7 : ℕ) a) = Bool.true ∧ f (Fin.natAdd (7 : ℕ) b) = Bool.true) ∧
          x14 < x15 ∧ ¬x11 x14 x15 ∧ ¬x11 x15 x14 ∧
          x11 x14 (x1.size - (1 : ℕ)) ∧ x11 x15 (x1.size - (1 : ℕ)) ∧
          x12 x14 ∧ x12 x15 ∧
          x12 x25 ∧ (∀ (b : Fin (2 : ℕ)), x8 (x10 x25 b) = Bool.true ∨ x9 (x10 x25 b) = Bool.true) ∧
          x11 x25 x14 ∧ x11 x25 x15 ∧
          (∀ (b : Fin (2 : ℕ)), x8 (x10 x14 b) = Bool.false) ∧
          (∀ (b : Fin (2 : ℕ)), x8 (x10 x15 b) = Bool.false ∧ x9 (x10 x15 b) = Bool.false)) →
        False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     x1.output + (1 : ℕ) = (14 : ℕ) + x1.size →       PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             have x7 : ℕ → Bool := fun (x7 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x7 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));             have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x8 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));             have x9 : ℕ → Bool := fun (x9 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x9 (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));             have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;             have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;             have x12 : ℕ → Prop := fun (x12 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x7 ((14 : ℕ) + x12) = Bool.true ∧ x8 ((14 : ℕ) + x12) = Bool.false ∧ x9 ((14 : ℕ) + x12) = Bool.false;             have x13 : ℕ → Prop := fun (x13 : ℕ) => x12 x13 ∧ ∀ (x14 : Fin (2 : ℕ)), x8 (x10 x13 x14) = Bool.true ∨ x9 (x10 x13 x14) = Bool.true;             ∀ (x14 x15 : ℕ), x14 < x15 → ¬x11 x14 x15 → ¬x11 x15 x14 → x11 x14 (x1.size - (1 : ℕ)) → x11 x15 (x1.size - (1 : ℕ)) → x12 x14 → x12 x15 → (∀ (x23 : Fin (2 : ℕ)), x8 (x10 x14 x23) = Bool.false) → (∀ (x24 : Fin (2 : ℕ)), x9 (x10 x15 x24) = Bool.false) → (∃ (x25 : ℕ), x13 x25 ∧ x11 x25 x14 ∧ x11 x25 x15 ∧ ((∀ (x26 : Fin (2 : ℕ)), x9 (x10 x14 x26) = Bool.false) ∨ ∀ (x26 : Fin (2 : ℕ)), x8 (x10 x15 x26) = Bool.false)) → False) :=
  fun x1 hSz hOut hAO hNodup hFun x14 x15 hlt hni1 hni2 hc1 hc2 h12_14 h12_15 h14_8 h15_9 hEx =>
    Exists.elim hEx fun x25 hx25 =>
      Or.elim hx25.2.2.2
        (fun hL =>
          hLeftZero x1 x14 x15 x25
            ⟨hSz, hOut, hAO, hNodup, hFun, hlt, hni1, hni2, hc1, hc2, h12_14, h12_15,
              hx25.1.1, hx25.1.2, hx25.2.1, hx25.2.2.1, fun b => ⟨h14_8 b, hL b⟩, h15_9⟩)
        (fun hR =>
          hRightZero x1 x14 x15 x25
            ⟨hSz, hOut, hAO, hNodup, hFun, hlt, hni1, hni2, hc1, hc2, h12_14, h12_15,
              hx25.1.1, hx25.1.2, hx25.2.1, hx25.2.2.1, h14_8, fun b => ⟨hR b, h15_9 b⟩⟩)
