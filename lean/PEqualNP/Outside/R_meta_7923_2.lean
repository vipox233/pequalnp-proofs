import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7923_2
    (hDisjointTrue :
      have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x9 x10 x21 : ℕ),
        have x4 : ℕ → Prop := fun (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 fun (x7 : Fin (11 : ℕ)) => x6.testBit ↑x7;
        have x6 : ℕ → Prop := fun (x6 : ℕ) => ∀ x7 ∈ x1, x5 x6 x7 = Bool.false;
        have x7 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;
        have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 fun (x9 : Fin (11 : ℕ)) => x8.testBit ↑x9;
        (PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 ∧ x3.size ≤ (21 : ℕ) ∧ x9 < x10 ∧ x10 < x3.size ∧ x4 x9 ∧ x4 x10 ∧
          (∀ x17 < x3.size, x4 x17 → (x6 x17 ↔ x17 ≠ x9 ∧ x17 ≠ x10)) ∧
          (∀ x18 < x3.size, x4 x18 → x6 x18 → ∀ x22 < x3.size, x4 x22 → ¬x7 x18 x22) ∧
          ¬x7 x9 x10 ∧ ¬x7 x10 x9 ∧
          x21 < x3.size ∧ x4 x21 ∧ x6 x21 ∧ x7 x9 x21 ∧ x7 x10 x21 ∧
          (∀ x22 ∈ x1, x5 x9 x22 = Bool.true → x5 x10 x22 = Bool.false) ∧
          (∀ x23 ∈ x2, x8 x23 = Bool.true) ∧ (∀ x24 ∈ x1, x8 x24 = Bool.false)) →
        False)
    (hCommonVertex :
      have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)];
      have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)];
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x9 x10 x21 : ℕ) (x22 : Fin (11 : ℕ)),
        have x4 : ℕ → Prop := fun (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;
        have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 fun (x7 : Fin (11 : ℕ)) => x6.testBit ↑x7;
        have x6 : ℕ → Prop := fun (x6 : ℕ) => ∀ x7 ∈ x1, x5 x6 x7 = Bool.false;
        have x7 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;
        have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 fun (x9 : Fin (11 : ℕ)) => x8.testBit ↑x9;
        (PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 ∧ x3.size ≤ (21 : ℕ) ∧ x9 < x10 ∧ x10 < x3.size ∧ x4 x9 ∧ x4 x10 ∧
          (∀ x17 < x3.size, x4 x17 → (x6 x17 ↔ x17 ≠ x9 ∧ x17 ≠ x10)) ∧
          (∀ x18 < x3.size, x4 x18 → x6 x18 → ∀ x22 < x3.size, x4 x22 → ¬x7 x18 x22) ∧
          ¬x7 x9 x10 ∧ ¬x7 x10 x9 ∧
          x21 < x3.size ∧ x4 x21 ∧ x6 x21 ∧ x7 x9 x21 ∧ x7 x10 x21 ∧
          (∀ x23 ∈ x1, x23.testBit ↑x22 = Bool.true → x5 x9 x23 = Bool.false ∧ x5 x10 x23 = Bool.false) ∧
          (∀ x23 ∈ x2, x8 x23 = Bool.true) ∧ (∀ x24 ∈ x1, x8 x24 = Bool.false)) →
        False) :
    (have x1 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   have x4 : ℕ → Prop := fun (x4 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and;   have x5 : ℕ → ℕ → Bool := fun (x5 x6 : ℕ) => PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 fun (x7 : Fin (11 : ℕ)) => x6.testBit ↑x7;   have x6 : ℕ → Prop := fun (x6 : ℕ) => ∀ x7 ∈ x1, x5 x6 x7 = Bool.false;   have x7 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;   have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x3 fun (x9 : Fin (11 : ℕ)) => x8.testBit ↑x9;   ∀ (x9 x10 : ℕ), PEqualNP.TopForm.IsAO2 (11 : ℕ) x3 → x3.size ≤ (21 : ℕ) → x9 < x10 → x10 < x3.size → x4 x9 → x4 x10 → (∀ x17 < x3.size, x4 x17 → (x6 x17 ↔ x17 ≠ x9 ∧ x17 ≠ x10)) → (∀ x18 < x3.size, x4 x18 → x6 x18 → ∀ x22 < x3.size, x4 x22 → ¬x7 x18 x22) → ¬x7 x9 x10 → ¬x7 x10 x9 → (∃ x21 < x3.size, x4 x21 ∧ x6 x21 ∧ x7 x9 x21 ∧ x7 x10 x21) → ((∀ x22 ∈ x1, x5 x9 x22 = Bool.true → x5 x10 x22 = Bool.false) ∨ ∃ (x22 : Fin (11 : ℕ)), ∀ x23 ∈ x1, x23.testBit ↑x22 = Bool.true → x5 x9 x23 = Bool.false ∧ x5 x10 x23 = Bool.false) → (∀ x23 ∈ x2, x8 x23 = Bool.true) → (∀ x24 ∈ x1, x8 x24 = Bool.false) → False) :=
  fun x3 x9 x10 hAO hSz hLt h10 hA9 hA10 hClean hTop hN1 hN2 hEx21 hDisj hPos hNeg =>
    Exists.elim hEx21 fun x21 hx21 =>
      Or.elim hDisj
        (fun hD => hDisjointTrue x3 x9 x10 x21 ⟨hAO, hSz, hLt, h10, hA9, hA10, hClean, hTop, hN1, hN2, hx21.1, hx21.2.1, hx21.2.2.1, hx21.2.2.2.1, hx21.2.2.2.2, hD, hPos, hNeg⟩)
        (fun hV => Exists.elim hV fun x22 hx22 =>
          hCommonVertex x3 x9 x10 x21 x22 ⟨hAO, hSz, hLt, h10, hA9, hA10, hClean, hTop, hN1, hN2, hx21.1, hx21.2.1, hx21.2.2.1, hx21.2.2.2.1, hx21.2.2.2.2, hx22, hPos, hNeg⟩)
