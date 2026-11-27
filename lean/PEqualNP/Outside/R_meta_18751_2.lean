import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18751_2
    (hStripIsolated : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (k : ℕ),
      (∀ v ∉ A, (G.neighborSet v).ncard = (3 : ℕ)) ∧
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → (7 : ℕ) ≤ p.length) ∧
      (∀ u v : Fin n, G.Adj u v → u ∉ A) ∧
      (∃ u v : Fin n, G.Adj u v) ∧
      PEqualNP.MetaComplexity.HasCircuitSize n (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) k →
      ∃ (m : ℕ) (f : Fin m → Fin n),
        (22 : ℕ) ≤ m ∧
        (∀ a : Fin m, ((G.comap f).neighborSet a).ncard = (3 : ℕ)) ∧
        (∀ (a : Fin m) (p : (G.comap f).Walk a a), p.IsCycle → (7 : ℕ) ≤ p.length) ∧
        PEqualNP.MetaComplexity.HasCircuitSize m (PEqualNP.MetaComplexity.NestedCover.graphFun (G.comap f) ∅) k ∧
        ∀ T' : Finset (Fin m), (∀ a b : Fin m, (G.comap f).Adj a b → a ∈ T' ∨ b ∈ T') →
          ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
            G.edgeSet.ncard + T.card ≤ (G.comap f).edgeSet.ncard + T'.card)
    (hCubicGirth7 : ∀ (m : ℕ) (H : SimpleGraph (Fin m)) [DecidableRel H.Adj] (k : ℕ),
      (22 : ℕ) ≤ m ∧
      (∀ a : Fin m, (H.neighborSet a).ncard = (3 : ℕ)) ∧
      (∀ (a : Fin m) (p : H.Walk a a), p.IsCycle → (7 : ℕ) ≤ p.length) ∧
      PEqualNP.MetaComplexity.HasCircuitSize m (PEqualNP.MetaComplexity.NestedCover.graphFun H ∅) k →
      ∃ T : Finset (Fin m), (∀ a b : Fin m, H.Adj a b → a ∈ T ∨ b ∈ T) ∧ H.edgeSet.ncard + T.card ≤ k + (1 : ℕ)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x9 → ∃ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x2.edgeSet.ncard + x11.card ≤ x9 + (1 : ℕ)) := by
  intro n G _ A hDeg hGirth hIso hEdge k hSz
  exact Exists.elim (@hStripIsolated n G _ A k ⟨hDeg, hGirth, hIso, hEdge, hSz⟩) fun m hm =>
    Exists.elim hm fun f hf =>
      Exists.elim (@hCubicGirth7 m (G.comap f) _ k ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩) fun T' hT' =>
        Exists.elim (hf.2.2.2.2 T' hT'.1) fun T hT =>
          ⟨T, hT.1, Nat.le_trans hT.2 hT'.2⟩
