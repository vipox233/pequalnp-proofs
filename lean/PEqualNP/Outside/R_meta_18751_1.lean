import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18751_1
    (hEmpty : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x4 = ∅ → (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x2.edgeSet.ncard + x11.card ≤ x9 + (1 : ℕ))
    (hNonempty : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x4.Nonempty → (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x2.edgeSet.ncard + x11.card ≤ x9 + (1 : ℕ)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x2.edgeSet.ncard + x11.card ≤ x9 + (1 : ℕ)) := by
  intro x1 x2 x3 x4
  by_cases hE : x4 = ∅
  · exact @hEmpty x1 x2 x3 x4 hE
  · exact @hNonempty x1 x2 x3 x4 (Finset.nonempty_iff_ne_empty.mpr hE)
