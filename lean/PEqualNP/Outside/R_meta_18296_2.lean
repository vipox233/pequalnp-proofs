import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18296_2
    (hUnpackNestedAnds :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) C →
        ∃ (i1 j1 i2 j2 : ℕ),
          (i1, j1) ≠ (i2, j2) ∧
          i1 < C.size ∧ j1 < C.size ∧ i2 < C.size ∧ j2 < C.size ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C i1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone (26 : ℕ) C i1 j1 ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone (26 : ℕ) C i2 j2)
    (hRefuteSmall :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (P L : Finset (Fin (13 : ℕ))) =>
        PEqualNP.GenericRejection.IsFalseInput x1 P L ∧ ((∃ (l : Fin (13 : ℕ)), P ⊆ x1 l) ∨ ∃ (p : Fin (13 : ℕ)), ∀ l ∈ L, p ∈ x1 l);
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (i1 j1 i2 j2 : ℕ) (P1 L1 P2 L2 : Finset (Fin (13 : ℕ))),
        have ga := PEqualNP.MetaComplexity.NestedCover.gateAt C;
        (C.size ≤ (63 : ℕ) ∧
          PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
          PEqualNP.GenericRejection.RightOnIncidentPairs x1 C ∧
          (∀ (P L : Finset (Fin (13 : ℕ))), x2 P L → C.eval (PEqualNP.GenericRejection.incidenceInput P L) = Bool.false) ∧
          (∀ (a b : ℕ), (ga a).op = PEqualNP.CircuitLowerBounds.GateOp.and → (ga b).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) C a b →
            ∃ (P L : Finset (Fin (13 : ℕ))), x2 P L ∧ (C.wires (PEqualNP.GenericRejection.incidenceInput P L)).getD ((26 : ℕ) + a) Bool.false = Bool.true) ∧
          (i1, j1) ≠ (i2, j2) ∧
          i1 < C.size ∧ j1 < C.size ∧ i2 < C.size ∧ j2 < C.size ∧
          (ga i1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (ga j1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) C i1 j1 ∧
          (ga i2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (ga j2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) C i2 j2 ∧
          x2 P1 L1 ∧ (C.wires (PEqualNP.GenericRejection.incidenceInput P1 L1)).getD ((26 : ℕ) + i1) Bool.false = Bool.true ∧
          x2 P2 L2 ∧ (C.wires (PEqualNP.GenericRejection.incidenceInput P2 L2)).getD ((26 : ℕ) + i2) Bool.false = Bool.true) →
        False) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x2 x3 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.IsFalseInput x1 x2 x3 ∧ ((∃ (x4 : Fin (13 : ℕ)), x2 ⊆ x1 x4) ∨ ∃ (x4 : Fin (13 : ℕ)), ∀ x5 ∈ x3, x4 ∈ x1 x5); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 x5 : Finset (Fin (13 : ℕ))), x2 x4 x5 → x3.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 ∧ ∀ (x5 x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6 → ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), x2 x10 x11 ∧ (x4.wires (PEqualNP.GenericRejection.incidenceInput x10 x11)).getD ((26 : ℕ) + x5) Bool.false = Bool.true; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 → x3 x5 → x4 x5 → (64 : ℕ) ≤ x5.size) :=
  fun C hAO h3 h4 =>
    Or.elim (Nat.lt_or_ge C.size (64 : ℕ))
      (fun hlt =>
        False.elim
          (Exists.elim (hUnpackNestedAnds C h4.1) fun i1 h1 =>
            Exists.elim h1 fun j1 h2 =>
              Exists.elim h2 fun i2 h3' =>
                Exists.elim h3' fun j2 hp =>
                  Exists.elim (h4.2 i1 j1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1) fun P1 hP1 =>
                    Exists.elim hP1 fun L1 hw1 =>
                      Exists.elim (h4.2 i2 j2 hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2) fun P2 hP2 =>
                        Exists.elim hP2 fun L2 hw2 =>
                          hRefuteSmall C i1 j1 i2 j2 P1 L1 P2 L2
                            ⟨Nat.le_of_lt_succ hlt, hAO, h3.1, h3.2, h4.2, hp.1,
                              hp.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
                              hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.1,
                              hp.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2,
                              hw1.1, hw1.2, hw2.1, hw2.2⟩))
      (fun hge => hge)
