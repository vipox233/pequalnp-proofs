import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18498_2
    (hMooreAndNoShortCycle :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (U : Finset (Fin n)),
        (∀ v ∉ U, (G.neighborSet v).ncard = (3 : ℕ)) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (7 : ℕ) ≤ w.length) →
        (∀ (u v : Fin n), G.Adj u v → u ∉ U) →
        (∃ (u v : Fin n), G.Adj u v) →
        (22 : ℕ) ≤ Uᶜ.card ∧
        (2 : ℕ) * G.edgeFinset.card = (3 : ℕ) * Uᶜ.card ∧
        (∀ (a b c : Fin n), G.Adj a b → G.Adj b c → ¬G.Adj a c) ∧
        (∀ (a b c d : Fin n), a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬G.Adj d a))
    (hWithMoore :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)),
        ((∀ v ∉ x4, (x2.neighborSet v).ncard = (3 : ℕ)) ∧
         (∀ (v : Fin x1) (w : x2.Walk v v), w.IsCycle → (7 : ℕ) ≤ w.length) ∧
         (∀ (u v : Fin x1), x2.Adj u v → u ∉ x4) ∧
         (∃ (u v : Fin x1), x2.Adj u v) ∧
         (22 : ℕ) ≤ x4ᶜ.card ∧
         (2 : ℕ) * x2.edgeFinset.card = (3 : ℕ) * x4ᶜ.card ∧
         (∀ (a b c : Fin x1), x2.Adj a b → x2.Adj b c → ¬x2.Adj a c) ∧
         (∀ (a b c d : Fin x1), a ≠ c → b ≠ d → x2.Adj a b → x2.Adj b c → x2.Adj c d → ¬x2.Adj d a)) →
        ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x9 →
        ∃ x11 ⊆ x4ᶜ, (∀ (u v : Fin x1), x2.Adj u v → u ∈ x11 ∨ v ∈ x11) ∧ x4.card + x2.edgeFinset.card + x11.card ≤ x9 + (1 : ℕ)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), (∀ x5 ∉ x4, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x4) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → ∀ (x9 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4) x9 → ∃ x11 ⊆ x4ᶜ, (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) ∧ x4.card + x2.edgeFinset.card + x11.card ≤ x9 + (1 : ℕ)) :=
  fun x1 x2 _x3 x4 hDeg hGirth hIso hEdge =>
    let hM := hMooreAndNoShortCycle x1 x2 x4 hDeg hGirth hIso hEdge
    hWithMoore x1 x2 x4 ⟨hDeg, hGirth, hIso, hEdge, hM.1, hM.2.1, hM.2.2.1, hM.2.2.2⟩
