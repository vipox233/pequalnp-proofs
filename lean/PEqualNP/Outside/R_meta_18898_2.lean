import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18898_2
    (hMoore15 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x4 x5 x6 : Finset (Fin x1)),
        (Disjoint x5 x6 ∧
          x5 ∪ x6 = Finset.univ \ x4 ∧
          x5.card = x6.card ∧
          (3 : ℕ) ≤ x5.card ∧
          (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x5 ∧ x12 ∈ x6 ∨ x11 ∈ x6 ∧ x12 ∈ x5) ∧
          (∀ x12 ∉ x4, (x2.neighborSet x12).ncard = (3 : ℕ)) ∧
          (∀ (x13 : Fin x1) (x14 : x2.Walk x13 x13), x14.IsCycle → (8 : ℕ) ≤ x14.length)) →
        (15 : ℕ) ≤ x5.card ∧
        ∀ (u v w z : Fin x1), u ≠ w → v ≠ z → ¬(x2.Adj u v ∧ x2.Adj u z ∧ x2.Adj w v ∧ x2.Adj w z))
    (hElimMoore :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 x5 x6 : Finset (Fin x1)) (x14 : PEqualNP.CircuitLowerBounds.Circuit),
        (Disjoint x5 x6 ∧
          x5 ∪ x6 = Finset.univ \ x4 ∧
          x5.card = x6.card ∧
          (15 : ℕ) ≤ x5.card ∧
          (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x5 ∧ x12 ∈ x6 ∨ x11 ∈ x6 ∧ x12 ∈ x5) ∧
          (∀ x12 ∉ x4, (x2.neighborSet x12).ncard = (3 : ℕ)) ∧
          (∀ (x13 : Fin x1) (x14 : x2.Walk x13 x13), x14.IsCycle → (8 : ℕ) ≤ x14.length) ∧
          (∀ (u v w z : Fin x1), u ≠ w → v ≠ z → ¬(x2.Adj u v ∧ x2.Adj u z ∧ x2.Adj w v ∧ x2.Adj w z)) ∧
          PEqualNP.MetaComplexity.IsMinimalCircuit x1 x14 ∧
          PEqualNP.EdgeOwnership.AndOrOnly x14 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧
          x14.size + (1 : ℕ) < (4 : ℕ) * x5.card) →
        ∃ (x19 : Fin x1) (x20 : Fin x1),
          x19 ∉ x4 ∧ x20 ∉ x4 ∧ x19 ≠ x20 ∧ ¬x2.Adj x19 x20 ∧
          ∃ (x21 : ℕ), x21 + (8 : ℕ) ≤ x14.size ∧
            PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x22 x19 Bool.false) x20 Bool.false)) x21) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 x5 x6 : Finset (Fin x1)), Disjoint x5 x6 → x5 ∪ x6 = Finset.univ \ x4 → x5.card = x6.card → (3 : ℕ) ≤ x5.card → (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x5 ∧ x12 ∈ x6 ∨ x11 ∈ x6 ∧ x12 ∈ x5) → (∀ x12 ∉ x4, (x2.neighborSet x12).ncard = (3 : ℕ)) → (∀ (x13 : Fin x1) (x14 : x2.Walk x13 x13), x14.IsCycle → (8 : ℕ) ≤ x14.length) → ∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x14 → PEqualNP.EdgeOwnership.AndOrOnly x14 → PEqualNP.MetaComplexity.circuitFun x1 x14 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x14.size + (1 : ℕ) < (4 : ℕ) * x5.card → ∃ (x19 : Fin x1) (x20 : Fin x1), x19 ∉ x4 ∧ x20 ∉ x4 ∧ x19 ≠ x20 ∧ ¬x2.Adj x19 x20 ∧ ∃ (x21 : ℕ), x21 + (8 : ℕ) ≤ x14.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x22 x19 Bool.false) x20 Bool.false)) x21) :=
  fun x1 x2 _ x4 x5 x6 hDisj hUni hCard h3 hBip hDeg hGirth C hMin hAO hFun hSz =>
    have hm := hMoore15 x1 x2 x4 x5 x6 ⟨hDisj, hUni, hCard, h3, hBip, hDeg, hGirth⟩
    hElimMoore x1 x2 x4 x5 x6 C ⟨hDisj, hUni, hCard, hm.1, hBip, hDeg, hGirth, hm.2, hMin, hAO, hFun, hSz⟩
