import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18573_2
    (hSharedEndpoint :
      let x1 : SimpleGraph (Fin (26 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x1 : ℕ) => List.filterMap (fun (x2 : ℕ) => if (x1 + (13 : ℕ) - x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] then Option.some (x1 + (1 : ℕ), x2 + (14 : ℕ)) else Option.none) (List.range (12 : ℕ))) (List.range (12 : ℕ)));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit (26 : ℕ) x2 →
        x2.size ≤ (55 : ℕ) →
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ →
        ∀ (x6 : ℕ), PEqualNP.CleanedNonEdge.IsDirtyAnd (26 : ℕ) x1 x2 x6 →
        ∀ (x7 x8 x9 x10 : Fin (26 : ℕ)),
          x1.Adj x7 x8 → x1.Adj x9 x10 → x7 < x8 → x9 < x10 → (x7, x8) ≠ (x9, x10) →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true →
          (x7 = x9 ∨ x8 = x10) → False)
    (hDisjointPair :
      let x1 : SimpleGraph (Fin (26 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x1 : ℕ) => List.filterMap (fun (x2 : ℕ) => if (x1 + (13 : ℕ) - x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] then Option.some (x1 + (1 : ℕ), x2 + (14 : ℕ)) else Option.none) (List.range (12 : ℕ))) (List.range (12 : ℕ)));
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit (26 : ℕ) x2 →
        x2.size ≤ (55 : ℕ) →
        PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ →
        ∀ (x6 : ℕ), PEqualNP.CleanedNonEdge.IsDirtyAnd (26 : ℕ) x1 x2 x6 →
        ∀ (x7 x8 x9 x10 : Fin (26 : ℕ)),
          x1.Adj x7 x8 → x1.Adj x9 x10 → x7 < x8 → x9 < x10 → (x7, x8) ≠ (x9, x10) →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true →
          PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true →
          (x7 ≠ x9 ∧ x8 ≠ x10) → False) :
    (let x1 : SimpleGraph (Fin (26 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (26 : ℕ) (List.flatMap (fun (x1 : ℕ) => List.filterMap (fun (x2 : ℕ) => if (x1 + (13 : ℕ) - x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] then Option.some (x1 + (1 : ℕ), x2 + (14 : ℕ)) else Option.none) (List.range (12 : ℕ))) (List.range (12 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit (26 : ℕ) x2 → x2.size ≤ (55 : ℕ) → PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x2 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ → (∃ (x6 : ℕ), PEqualNP.CleanedNonEdge.IsDirtyAnd (26 : ℕ) x1 x2 x6 ∧ ∃ (x7 : Fin (26 : ℕ)) (x8 : Fin (26 : ℕ)) (x9 : Fin (26 : ℕ)) (x10 : Fin (26 : ℕ)), x1.Adj x7 x8 ∧ x1.Adj x9 x10 ∧ x7 < x8 ∧ x9 < x10 ∧ (x7, x8) ≠ (x9, x10) ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x2 x6 (PEqualNP.EdgeOwnership.pairInput x9 x10) = Bool.true) → False) :=
  fun x2 hMin hSz hFun hEx =>
    hEx.elim fun x6 h6 =>
      h6.2.elim fun x7 h7 =>
        h7.elim fun x8 h8 =>
          h8.elim fun x9 h9 =>
            h9.elim fun x10 h10 =>
              (Classical.em (x7 = x9 ∨ x8 = x10)).elim
                (fun hSh => hSharedEndpoint x2 hMin hSz hFun x6 h6.1 x7 x8 x9 x10
                  h10.1 h10.2.1 h10.2.2.1 h10.2.2.2.1 h10.2.2.2.2.1 h10.2.2.2.2.2.1 h10.2.2.2.2.2.2 hSh)
                (fun hDisj => hDisjointPair x2 hMin hSz hFun x6 h6.1 x7 x8 x9 x10
                  h10.1 h10.2.1 h10.2.2.1 h10.2.2.2.1 h10.2.2.2.2.1 h10.2.2.2.2.2.1 h10.2.2.2.2.2.2
                  ⟨fun h => hDisj (Or.inl h), fun h => hDisj (Or.inr h)⟩)
