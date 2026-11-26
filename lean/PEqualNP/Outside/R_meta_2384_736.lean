import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- The three distinguished vertices are 0, 1 and 2. Every full cover containing
-- all three needs eight vertices; a general full cover needs seven. The finite
-- exchange premise involves only vertex subsets and no circuit or deletion set.
theorem PEqualNP.Outside.R_meta_2384_736
  (exchange : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ K : Finset (Fin 11), K.card < 7 →
      ∃ J T : Finset (Fin 11), J.card ≤ K.card ∧
        (∀ a b, G.Adj a b → (a ∈ K ∨ b ∈ K) → a ∈ J ∨ b ∈ J) ∧
        J ⊆ T ∧ G.IsVertexCover (↑T) ∧ T.card ≤ (if ({0,1,2} : Finset (Fin 11)) ⊆ K then 8 else 7))
  (charge : let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      let U := Ustar G C
      let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      U.card ≤ B → B < 2*U.card → ∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
        (if ({0,1,2} : Finset (Fin 11)) ⊆ K then 8 else 7) ≤ K.card + (B-U.card)) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → ∃ (x11 : Finset (Fin (11 : ℕ))) (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x11 ∧ x1.IsVertexCover ↑(x11 ∪ x12) ∧ x12.card ≤ x8 - x7.card := by
  classical
  let G := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  intro G₀ C sz least top dirty U₀ B₀ lo hi
  let U := Ustar G C
  let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  obtain ⟨K,hK,cost⟩ := charge C sz least top dirty lo hi
  change (if ({0,1,2} : Finset (Fin 11)) ⊆ K then 8 else 7) ≤ K.card + (B-U.card) at cost
  have residual (a b : Fin 11) (h : (G.deleteEdges ↑U).Adj a b) := (SimpleGraph.deleteEdges_adj.mp h).1
  by_cases small : K.card < 7
  · obtain ⟨J,T,jc,keep,jt,tc,cap⟩ := exchange K small
    have hj : (G.deleteEdges ↑U).IsVertexCover (↑J) := by
      intro a b h
      exact keep a b (residual a b h) (hK.1 h)
    have eq := Nat.le_antisymm jc (hK.2 _ hj)
    refine ⟨J,T \ J,⟨hj,fun W hw => jc.trans (hK.2 W hw)⟩,?_,?_⟩
    · rw [Finset.union_sdiff_of_subset jt]
      exact tc
    · change (T \ J).card ≤ B-U.card
      rw [Finset.card_sdiff_of_subset jt,eq]
      omega
  · let T : Finset (Fin 11) := {0,1,3,5,7,8,10}
    have full : G.IsVertexCover (↑T) := by
      change ∀ a b : Fin 11, G.Adj a b → a ∈ T ∨ b ∈ T
      dsimp [G,T]
      decide +kernel
    have hc : T.card = 7 := by decide
    have hr : (G.deleteEdges ↑U).IsVertexCover (↑T) := by
      intro a b h
      exact full (residual a b h)
    refine ⟨T,∅,⟨hr,fun W hw => ?_⟩,by simpa only [Finset.union_empty] using full,Nat.zero_le _⟩
    exact (show T.card ≤ K.card by omega).trans (hK.2 _ hw)
