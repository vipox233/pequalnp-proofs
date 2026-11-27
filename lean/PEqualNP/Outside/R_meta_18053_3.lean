import PEqualNP.Defs

-- Separate Singer-plane non-adjacency (0 non-adjacent to 0, 1, 14) from the IsLeastAO AND-gate property on non-edge pairs.
theorem PEqualNP.Outside.R_meta_18053_3
    (hNoEdge :
      ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), G.Adj x3 x4 ↔
          ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
            (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨
              x5 = x6 + (9 : Fin (13 : ℕ))) ∧
            (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨
              x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ v : Fin (26 : ℕ),
          v = (0 : Fin (26 : ℕ)) ∨ v = (1 : Fin (26 : ℕ)) ∨ v = (14 : Fin (26 : ℕ)) →
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
            (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) v) = Bool.false)
    (hAndNonEdge :
      ∀ (G : SimpleGraph (Fin (26 : ℕ))) [DecidableRel G.Adj],
        (∀ (x3 x4 : Fin (26 : ℕ)), G.Adj x3 x4 ↔
          ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
            (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨
              x5 = x6 + (9 : Fin (13 : ℕ))) ∧
            (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨
              x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.TopForm.IsLeastAO G C →
          ∀ j < C.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            (0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs →
            ∀ v : Fin (26 : ℕ),
              PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
                (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) v) = Bool.false →
              PEqualNP.EdgeOwnership.gateVal (26 : ℕ) C j
                (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) v) = Bool.false) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
      (∀ (x3 x4 : Fin (26 : ℕ)), x1.Adj x3 x4 ↔
        ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)),
          (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨
            x5 = x6 + (9 : Fin (13 : ℕ))) ∧
          (x3 = Fin.castAdd (13 : ℕ) x5 ∧ x4 = Fin.natAdd (13 : ℕ) x6 ∨
            x4 = Fin.castAdd (13 : ℕ) x5 ∧ x3 = Fin.natAdd (13 : ℕ) x6)) →
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x4 →
        ∀ x6 < x4.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (0 : ℕ) ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).inputs →
          ∀ (x10 : Fin (26 : ℕ)),
            x10 = (0 : Fin (26 : ℕ)) ∨ x10 = (1 : Fin (26 : ℕ)) ∨ x10 = (14 : Fin (26 : ℕ)) →
            PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x4 x6
              (PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) x10) = Bool.false := by
  intro x1 _ hadj x4 hleast x6 hx6 hop h0 x10 hx10
  exact hAndNonEdge x1 hadj x4 hleast x6 hx6 hop h0 x10 (hNoEdge x1 hadj x10 hx10)
