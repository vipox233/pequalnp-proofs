import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6138_3
    (hDiffEquiv :
      ∀ (x5 x6 : Fin (13 : ℕ)),
        (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ↔
          ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])
    (hGateFalseDiff :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), ↑(x5 - x6) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO x1 x4 →
          ∀ x6 < x4.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (14 : Fin (26 : ℕ))) = Bool.false) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [DecidableRel x1.Adj], (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨ x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x1 x4 → ∀ x6 < x4.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (14 : Fin (26 : ℕ))) = Bool.false) :=
  fun x1 _ hadj =>
    hGateFalseDiff x1
      (fun x3 x4 =>
        Iff.trans (hadj x3 x4)
          (Iff.intro
            (fun h => Exists.elim h fun x5 h5 => Exists.elim h5 fun x6 h6 => Exists.intro x5 (Exists.intro x6 (And.intro ((hDiffEquiv x5 x6).mp h6.1) h6.2)))
            (fun h => Exists.elim h fun x5 h5 => Exists.elim h5 fun x6 h6 => Exists.intro x5 (Exists.intro x6 (And.intro ((hDiffEquiv x5 x6).mpr h6.1) h6.2)))))
