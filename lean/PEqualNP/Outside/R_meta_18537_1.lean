import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem PEqualNP.Outside.R_meta_18537_1
    (hPureCubic : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj],
      (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (3 : ℕ)) →
        (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
          (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
            (∀ (x7 x8 : Fin x1), x2.Reachable x7 x8) →
              ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8)
    (hHasIso : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj],
      (∃ (u : Fin x1), (x2.neighborSet u).ncard = (0 : ℕ)) →
        (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) →
          (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) →
            (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) →
              (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) →
                ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj], (∀ (x4 : Fin x1), (x2.neighborSet x4).ncard = (0 : ℕ) ∨ (x2.neighborSet x4).ncard = (3 : ℕ)) → (∀ (x5 : Fin x1) (x6 : x2.Walk x5 x5), x6.IsCycle → (7 : ℕ) ≤ x6.length) → (∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7) → (∀ (x7 x8 : Fin x1), (∃ (x9 : Fin x1), x2.Adj x7 x9) → (∃ (x10 : Fin x1), x2.Adj x8 x10) → x2.Reachable x7 x8) → ∀ (x8 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x8 → PEqualNP.BicliqueBlockCost.HasBlockCost x2 x8 := by
  intro x1 x2 inst hdeg hgirth hedge hconn x8 hcs
  exact Or.elim (Classical.em (∃ u : Fin x1, (x2.neighborSet u).ncard = (0 : ℕ)))
    (fun hiso => @hHasIso x1 x2 inst hiso hdeg hgirth hedge hconn x8 hcs)
    (fun hnoiso =>
      have hall3 : ∀ u : Fin x1, (x2.neighborSet u).ncard = (3 : ℕ) := fun u =>
        Or.elim (hdeg u) (fun h0 => False.elim (hnoiso ⟨u, h0⟩)) id
      have hne : ∀ u : Fin x1, ∃ w : Fin x1, x2.Adj u w := fun u =>
        Exists.elim (Set.nonempty_of_ncard_ne_zero (s := x2.neighborSet u) (by rw [hall3 u]; exact Nat.succ_ne_zero 2))
          fun w hw => ⟨w, hw⟩
      @hPureCubic x1 x2 inst hall3 hgirth hedge (fun a b => hconn a b (hne a) (hne b)) x8 hcs)
