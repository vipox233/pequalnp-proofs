import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18201_3
    (hValidAndInternal :
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (k : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          c.gates[k]? = Option.some g →
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ (u v : ℕ), g.inputs = [u, v] ∧ u ≠ v ∧ u < (26 : ℕ) + k ∧ v < (26 : ℕ) + k) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) c ∧
        (∀ g ∈ c.gates, g.inputs.Nodup) ∧
        (∀ (k : ℕ),
          (PEqualNP.MetaComplexity.NestedCover.gateAt c k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) c k
            (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true →
          (∀ (b : Fin (2 : ℕ)),
            PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) c (PEqualNP.TopForm.opnd c k b)
              (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false ∧
            PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) c (PEqualNP.TopForm.opnd c k b)
              (PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.false) →
          k < c.gates.length ∧
          ∃ (g1 g2 : ℕ), g1 ≠ g2 ∧ g1 < k ∧ g2 < k ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt c k).inputs = [(26 : ℕ) + g1, (26 : ℕ) + g2]))
    (hNoTwoInternal :
      ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        let x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        let x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
        let x6 : ℕ → Prop := fun (k : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 k).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        x1.size ≤ (63 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 ∧
        (∀ g ∈ x1.gates, g.inputs.Nodup) ∧
        (∀ (f : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn f) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)), p - l ∈ x2 ∧ f (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ f (Fin.natAdd (13 : ℕ) l) = Bool.true) ∧
        (∃ k < x1.gates.length, x6 k ∧ ∃ (f : Fin (26 : ℕ) → Bool), x4 k f = Bool.true ∧ x1.eval (List.ofFn f) = Bool.false) ∧
        ∃ (k g1 g2 : ℕ),
          k < x1.gates.length ∧ g1 ≠ g2 ∧ g1 < k ∧ g2 < k ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x1 k).inputs = [(26 : ℕ) + g1, (26 : ℕ) + g2] ∧
          x6 k ∧
          ((26 : ℕ) + k = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 k (x1.output - (26 : ℕ))) ∧
          x4 k (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧
          (∀ (b : Fin (2 : ℕ)),
            PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 k b)
              (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false ∧
            PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 k b)
              (PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.false)) :
    (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size ≤ (63 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ ((26 : ℕ) + x10 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1 x10 (x1.output - (26 : ℕ))) ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false) :=
  fun hEx =>
    Exists.elim hEx fun x1 h1 =>
      let hVI := hValidAndInternal x1 h1.2.1
      Exists.elim h1.2.2.2.2 fun k hk =>
        let hK := hVI.2.2 k hk.1 hk.2.2.1 hk.2.2.2
        Exists.elim hK.2 fun g1 hg1 =>
          Exists.elim hg1 fun g2 hg2 =>
            hNoTwoInternal
              ⟨x1, h1.1, hVI.1, hVI.2.1, h1.2.2.1, h1.2.2.2.1,
                k, g1, g2, hK.1, hg2.1, hg2.2.1, hg2.2.2.1, hg2.2.2.2,
                hk.1, hk.2.1, hk.2.2.1, hk.2.2.2⟩
