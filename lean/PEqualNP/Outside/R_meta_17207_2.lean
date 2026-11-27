import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17207_2
    (hAndNotConstWire0 :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)),
          x1.Adj x3 x4 ↔
            ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
              (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧
              (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨
                x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          ∀ x6 < x4.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.true →
            ∃ y : Fin (26 : ℕ) → Bool,
              y (0 : Fin (26 : ℕ)) = Bool.false ∧
              PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 y = Bool.true)
    (hNoNontrivialAndOn0 :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)),
          x1.Adj x3 x4 ↔
            ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
              (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧
              (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨
                x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          ∀ x6 < x4.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.true →
            (∃ y : Fin (26 : ℕ) → Bool,
              y (0 : Fin (26 : ℕ)) = Bool.false ∧
              PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 y = Bool.true) →
            False) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ))) = Bool.false) :=
  fun x1 x2 hAdj x4 hLeast x6 hlt hop =>
    Or.elim
      (Bool.eq_false_or_eq_true
        (PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ)))))
      (fun ht =>
        False.elim
          (@hNoNontrivialAndOn0 x1 x2 hAdj x4 hLeast x6 hlt hop ht
            (@hAndNotConstWire0 x1 x2 hAdj x4 hLeast x6 hlt hop ht)))
      (fun hf => hf)
