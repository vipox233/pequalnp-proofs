import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem PEqualNP.Outside.R_meta_18537_2
    (hToTopForm :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj],
        (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) →
        (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
        (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
        (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) →
        ∀ (x8 : ℕ),
          PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 →
          ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.TopForm.IsLeastAO x2 D ∧ PEqualNP.TopForm.TopForm x2 D ∧ D.size ≤ x8)
    (hTopFormToBlock :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) →
        (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
        (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
        (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) →
        PEqualNP.TopForm.IsLeastAO x2 D →
        PEqualNP.TopForm.TopForm x2 D →
        PEqualNP.BicliqueBlockCost.HasBlockCost x2 D.size) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8 := by
  intro x1 x2 x3 hDeg hGirth hNE hConn x8 hCirc
  obtain ⟨D, hLeast, hTF, hDle⟩ := @hToTopForm x1 x2 x3 hDeg hGirth hNE hConn x8 hCirc
  obtain ⟨F, hCov, hCost⟩ := @hTopFormToBlock x1 x2 x3 D hDeg hGirth hNE hConn hLeast hTF
  exact ⟨F, hCov, Nat.le_trans hCost hDle⟩
