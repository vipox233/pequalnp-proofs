import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8101_2
    (hTotalWeightBound :
      ∀ (x3 x4 : Fin (20 : ℕ) → Finset (Fin (42 : ℕ))),
        (∀ (x6 : Fin (20 : ℕ)), Disjoint (x3 x6) (x4 x6)) →
        (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin (20 : ℕ) | x7 ∈ x3 x8 ∨ x7 ∈ x4 x8}.ncard ≤ (4 : ℕ)) →
        (∑ x6 : Fin (20 : ℕ), ((x3 x6).card + (x4 x6).card)) ≤ (168 : ℕ))
    (hNoWeightedCover :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x3 x4 : Fin (20 : ℕ) → Finset (Fin (42 : ℕ))),
        (∀ (x6 : Fin (20 : ℕ)), Disjoint (x3 x6) (x4 x6)) →
        (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin (20 : ℕ) | x7 ∈ x3 x8 ∨ x7 ∈ x4 x8}.ncard ≤ (4 : ℕ)) →
        (∀ (x8 x9 : Fin (42 : ℕ)), ↑x8 < (21 : ℕ) → (21 : ℕ) ≤ ↑x9 → ¬x1.Adj x8 x9 → {x13 : Fin (20 : ℕ) | x8 ∈ x3 x13 ∨ x8 ∈ x4 x13 ∨ x9 ∈ x3 x13 ∨ x9 ∈ x4 x13}.ncard ≤ (6 : ℕ)) →
        (∀ (x9 : Finset (Fin (42 : ℕ))), (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) → (∀ x11 ⊆ x9, (∀ (x13 x14 : Fin (42 : ℕ)), x1.Adj x13 x14 → x13 ∈ x11 ∨ x14 ∈ x11) → x9 ⊆ x11) → ∃ (x12 : Finset (Fin (20 : ℕ))) (x13 : Finset (Fin (20 : ℕ))), Disjoint x12 x13 ∧ x12.biUnion x3 ∪ x13.biUnion x4 = x9) →
        (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → ∃ (x13 : Fin (20 : ℕ)), x10 ∈ x3 x13 ∧ x11 ∈ x4 x13 ∨ x11 ∈ x3 x13 ∧ x10 ∈ x4 x13) →
        (∑ x6 : Fin (20 : ℕ), ((x3 x6).card + (x4 x6).card)) ≤ (168 : ℕ) → False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (42 : ℕ))), x2 = (20 : ℕ) → (∀ (x6 : Fin x2), Disjoint (x3 x6) (x4 x6)) → (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin x2 | x7 ∈ x3 x8 ∨ x7 ∈ x4 x8}.ncard ≤ (4 : ℕ)) → (∀ (x8 x9 : Fin (42 : ℕ)), ↑x8 < (21 : ℕ) → (21 : ℕ) ≤ ↑x9 → ¬x1.Adj x8 x9 → {x13 : Fin x2 | x8 ∈ x3 x13 ∨ x8 ∈ x4 x13 ∨ x9 ∈ x3 x13 ∨ x9 ∈ x4 x13}.ncard ≤ (6 : ℕ)) → (∀ (x9 : Finset (Fin (42 : ℕ))), (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) → (∀ x11 ⊆ x9, (∀ (x13 x14 : Fin (42 : ℕ)), x1.Adj x13 x14 → x13 ∈ x11 ∨ x14 ∈ x11) → x9 ⊆ x11) → ∃ (x12 : Finset (Fin x2)) (x13 : Finset (Fin x2)), Disjoint x12 x13 ∧ x12.biUnion x3 ∪ x13.biUnion x4 = x9) → (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → ∃ (x13 : Fin x2), x10 ∈ x3 x13 ∧ x11 ∈ x4 x13 ∨ x11 ∈ x3 x13 ∧ x10 ∈ x4 x13) → False) :=
  let x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]
  fun x2 x3 x4 hx2 =>
    @Eq.rec ℕ (20 : ℕ)
      (fun n _ =>
        ∀ (x3 x4 : Fin n → Finset (Fin (42 : ℕ))),
          (∀ (x6 : Fin n), Disjoint (x3 x6) (x4 x6)) →
          (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin n | x7 ∈ x3 x8 ∨ x7 ∈ x4 x8}.ncard ≤ (4 : ℕ)) →
          (∀ (x8 x9 : Fin (42 : ℕ)), ↑x8 < (21 : ℕ) → (21 : ℕ) ≤ ↑x9 → ¬x1.Adj x8 x9 → {x13 : Fin n | x8 ∈ x3 x13 ∨ x8 ∈ x4 x13 ∨ x9 ∈ x3 x13 ∨ x9 ∈ x4 x13}.ncard ≤ (6 : ℕ)) →
          (∀ (x9 : Finset (Fin (42 : ℕ))), (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) → (∀ x11 ⊆ x9, (∀ (x13 x14 : Fin (42 : ℕ)), x1.Adj x13 x14 → x13 ∈ x11 ∨ x14 ∈ x11) → x9 ⊆ x11) → ∃ (x12 : Finset (Fin n)) (x13 : Finset (Fin n)), Disjoint x12 x13 ∧ x12.biUnion x3 ∪ x13.biUnion x4 = x9) →
          (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → ∃ (x13 : Fin n), x10 ∈ x3 x13 ∧ x11 ∈ x4 x13 ∨ x11 ∈ x3 x13 ∧ x10 ∈ x4 x13) → False)
      (fun x3 x4 hDisj hDeg4 hNonAdj6 hMinCov hEdgeCov =>
        hNoWeightedCover x3 x4 hDisj hDeg4 hNonAdj6 hMinCov hEdgeCov (hTotalWeightBound x3 x4 hDisj hDeg4))
      x2 hx2.symm x3 x4
