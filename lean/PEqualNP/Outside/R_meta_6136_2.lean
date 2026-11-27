import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6136_2
    (hFirstGate : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
      (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
            (0 : ℕ) < x4.gates.length →
              (PEqualNP.MetaComplexity.NestedCover.gateAt x4 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 (0 : ℕ) (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.false)
    (hLaterGate : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
      (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
            ∀ x6 < x4.gates.length,
              (0 : ℕ) < x6 →
                (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →
                  PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.false) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (1 : Fin (26 : ℕ))) = Bool.false) :=
  fun x1 _ hadj x4 hleast x6 hlt hand =>
    Or.elim (Nat.eq_zero_or_pos x6)
      (fun hz => by subst hz; exact hFirstGate x1 hadj x4 hleast hlt hand)
      (fun hp => hLaterGate x1 hadj x4 hleast x6 hlt hp hand)
