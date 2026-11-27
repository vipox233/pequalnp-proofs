import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8101_1
    (hLeftMinCover :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∃ (L0 : Finset (Fin (42 : ℕ))), L0.card = (21 : ℕ) ∧
        (∀ (u v : Fin (42 : ℕ)), x1.Adj u v → u ∈ L0 ∨ v ∈ L0) ∧
        (∀ S' ⊆ L0, (∀ (u v : Fin (42 : ℕ)), x1.Adj u v → u ∈ S' ∨ v ∈ S') → L0 ⊆ S'))
    (hConcrete20 :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x3 x4 : Fin (20 : ℕ) → Finset (Fin (42 : ℕ))),
        (∀ (x6 : Fin (20 : ℕ)), Disjoint (x3 x6) (x4 x6)) →
        (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin (20 : ℕ) | x7 ∈ x3 x8 ∨ x7 ∈ x4 x8}.ncard ≤ (4 : ℕ)) →
        (∀ (x8 x9 : Fin (42 : ℕ)), ↑x8 < (21 : ℕ) → (21 : ℕ) ≤ ↑x9 → ¬x1.Adj x8 x9 → {x13 : Fin (20 : ℕ) | x8 ∈ x3 x13 ∨ x8 ∈ x4 x13 ∨ x9 ∈ x3 x13 ∨ x9 ∈ x4 x13}.ncard ≤ (6 : ℕ)) →
        (∀ (x9 : Finset (Fin (42 : ℕ))), (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) → (∀ x11 ⊆ x9, (∀ (x13 x14 : Fin (42 : ℕ)), x1.Adj x13 x14 → x13 ∈ x11 ∨ x14 ∈ x11) → x9 ⊆ x11) → ∃ (x12 : Finset (Fin (20 : ℕ))) (x13 : Finset (Fin (20 : ℕ))), Disjoint x12 x13 ∧ x12.biUnion x3 ∪ x13.biUnion x4 = x9) →
        (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → ∃ (x13 : Fin (20 : ℕ)), x10 ∈ x3 x13 ∧ x11 ∈ x4 x13 ∨ x11 ∈ x3 x13 ∧ x10 ∈ x4 x13) →
        (∃ (L0 : Finset (Fin (42 : ℕ))) (x12 x13 : Finset (Fin (20 : ℕ))), L0.card = (21 : ℕ) ∧ Disjoint x12 x13 ∧ x12.biUnion x3 ∪ x13.biUnion x4 = L0) →
        False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : ℕ) (x3 x4 : Fin x2 → Finset (Fin (42 : ℕ))), x2 = (20 : ℕ) → (∀ (x6 : Fin x2), Disjoint (x3 x6) (x4 x6)) → (∀ (x7 : Fin (42 : ℕ)), {x8 : Fin x2 | x7 ∈ x3 x8 ∨ x7 ∈ x4 x8}.ncard ≤ (4 : ℕ)) → (∀ (x8 x9 : Fin (42 : ℕ)), ↑x8 < (21 : ℕ) → (21 : ℕ) ≤ ↑x9 → ¬x1.Adj x8 x9 → {x13 : Fin x2 | x8 ∈ x3 x13 ∨ x8 ∈ x4 x13 ∨ x9 ∈ x3 x13 ∨ x9 ∈ x4 x13}.ncard ≤ (6 : ℕ)) → (∀ (x9 : Finset (Fin (42 : ℕ))), (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) → (∀ x11 ⊆ x9, (∀ (x13 x14 : Fin (42 : ℕ)), x1.Adj x13 x14 → x13 ∈ x11 ∨ x14 ∈ x11) → x9 ⊆ x11) → ∃ (x12 : Finset (Fin x2)) (x13 : Finset (Fin x2)), Disjoint x12 x13 ∧ x12.biUnion x3 ∪ x13.biUnion x4 = x9) → (∀ (x10 x11 : Fin (42 : ℕ)), x1.Adj x10 x11 → ∃ (x13 : Fin x2), x10 ∈ x3 x13 ∧ x11 ∈ x4 x13 ∨ x11 ∈ x3 x13 ∧ x10 ∈ x4 x13) → False) := by
  intro x1 x2 x3 x4 hx2 hDisj hDeg4 hNonAdj6 hMinCov hEdgeCov
  cases hx2
  exact Exists.elim hLeftMinCover fun L0 hL0 =>
    Exists.elim (hMinCov L0 hL0.2.1 hL0.2.2) fun x12 hx12 =>
      Exists.elim hx12 fun x13 hx13 =>
        hConcrete20 x3 x4 hDisj hDeg4 hNonAdj6 hMinCov hEdgeCov ⟨L0, x12, x13, hL0.1, hx13.1, hx13.2⟩
