import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18609_3
    (hOutGateBounds :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (d out : ℕ) (f : Fin (26 : ℕ) → Bool),
        ((∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = Option.some g →
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ (a b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < (26 : ℕ) + i ∧ b < (26 : ℕ) + i) ∧
          d < C.gates.length ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C d).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C d f = Bool.true ∧
          C.eval (List.ofFn f) = Bool.false ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C out).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (26 : ℕ) + out = C.output ∧
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C out (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧
          ∀ (b : Fin (2 : ℕ)),
            PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C out b) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false ∧
            PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C (PEqualNP.TopForm.opnd C out b) (PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.false) →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧ out < C.size ∧ d ≠ out ∧
          ∀ (b : Fin (2 : ℕ)), (26 : ℕ) ≤ PEqualNP.TopForm.opnd C out b)
    (hRefuteUnpacked :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (d out : ℕ) (f : Fin (26 : ℕ) → Bool),
        have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
        have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C;
        have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) C;
        (C.size ≤ (64 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
          (∀ (v : Fin (26 : ℕ) → Bool), C.eval (List.ofFn v) = Bool.true ↔
            ∃ (a b : Fin (13 : ℕ)), a - b ∈ x2 ∧ v (Fin.castAdd (13 : ℕ) a) = Bool.true ∧ v (Fin.natAdd (13 : ℕ) b) = Bool.true) ∧
          d < C.size ∧ out < C.size ∧ d ≠ out ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C d).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x4 d f = Bool.true ∧ C.eval (List.ofFn f) = Bool.false ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C out).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (26 : ℕ) + out = C.output ∧
          x4 out (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.true ∧
          (∀ (b : Fin (2 : ℕ)),
            x5 (PEqualNP.TopForm.opnd C out b) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false ∧
            x5 (PEqualNP.TopForm.opnd C out b) (PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ))) = Bool.false) ∧
          ∀ (b : Fin (2 : ℕ)), (26 : ℕ) ≤ PEqualNP.TopForm.opnd C out b) →
        False) :
    (¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};     have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;     have x4 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;     have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1;     have x6 : ℕ → Prop := fun (x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).op = x3;     have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));     have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     have x9 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));     x1.size ≤ (64 : ℕ) ∧ (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧ (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧ (∃ x10 < x1.gates.length, x6 x10 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x4 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ), x6 x10 ∧ (26 : ℕ) + x10 = x1.output ∧ x4 x10 x9 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), x5 (PEqualNP.TopForm.opnd x1 x10 x11) x7 = Bool.false ∧ x5 (PEqualNP.TopForm.opnd x1 x10 x11) x8 = Bool.false) :=
  fun hEx =>
    Exists.elim hEx fun C hbody =>
      Exists.elim hbody.2.2.2.1 fun d hd =>
        Exists.elim hd.2.2 fun f hf =>
          Exists.elim hbody.2.2.2.2 fun out hout =>
            have hb := hOutGateBounds C d out f
              ⟨hbody.2.1, hd.1, hd.2.1, hf.1, hf.2, hout.1, hout.2.1, hout.2.2.1, hout.2.2.2⟩
            hRefuteUnpacked C d out f
              ⟨hbody.1, hb.1, hbody.2.2.1, hd.1, hb.2.1, hb.2.2.1, hd.2.1, hf.1, hf.2,
                hout.1, hout.2.1, hout.2.2.1, hout.2.2.2, hb.2.2.2⟩
