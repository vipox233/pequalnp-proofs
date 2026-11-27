import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

theorem PEqualNP.Outside.R_meta_18539_1
    (hCircuitToBlock :
      ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] [DecidableRel x3.Adj],
        (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) →
        (∃ (x7 x8 : Fin x1), x2.Adj x7 x8) →
        (∃ (x8 x9 : Fin x1), x3.Adj x8 x9) →
        (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) →
        (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) →
        ∀ (x11 : ℕ),
          PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun (x2 ⊔ x3) ∅) x11 →
          PEqualNP.BicliqueBlockCost.HasBlockCost (x2 ⊔ x3) x11)
    (hBlockToCircuit :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (c : ℕ),
        PEqualNP.BicliqueBlockCost.HasBlockCost G c →
        PEqualNP.MetaComplexity.HasCircuitSize n (PEqualNP.MetaComplexity.NestedCover.graphFun G ∅) c) :
    ∀ (x1 : ℕ) (x2 x3 : SimpleGraph (Fin x1)) [x4 : DecidableRel x2.Adj] [x5 : DecidableRel x3.Adj], (∀ (x6 x7 x8 : Fin x1), x2.Adj x6 x7 → ¬x3.Adj x6 x8) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → (∃ (x8 : Fin x1) (x9 : Fin x1), x3.Adj x8 x9) → (∀ (x9 : Fin x1), ((x2 ⊔ x3).neighborSet x9).ncard = (0 : ℕ) ∨ ((x2 ⊔ x3).neighborSet x9).ncard = (3 : ℕ)) → (∀ (x10 : Fin x1) (x11 : (x2 ⊔ x3).Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun (x2 ⊔ x3) ∅) x11 → ∃ (x13 : ℕ) (x14 : ℕ), x13 + x14 + (1 : ℕ) ≤ x11 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅) x13 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (PEqualNP.MetaComplexity.NestedCover.graphFun x3 ∅) x14 := by
  classical
  intro x1 x2 x3 x4 x5 hDisj hNE2 hNE3 hDeg hGirth x11 hCirc
  obtain ⟨F, hCov, hCost⟩ := @hCircuitToBlock x1 x2 x3 x4 x5 hDisj hNE2 hNE3 hDeg hGirth x11 hCirc
  have hDisj3 : ∀ u v w : Fin x1, x3.Adj u v → ¬x2.Adj u w := fun u v w h3 h2 => hDisj u w v h2 h3
  have hPart : ∀ p ∈ F, (PEqualNP.BicliqueBlockCost.IsBlock x2 p ∧ ¬PEqualNP.BicliqueBlockCost.IsBlock x3 p) ∨
      (PEqualNP.BicliqueBlockCost.IsBlock x3 p ∧ ¬PEqualNP.BicliqueBlockCost.IsBlock x2 p) := by
    intro p hp
    rcases hCov.1 p hp with ⟨hpDisj, ⟨a0, ha0⟩, ⟨b0, hb0⟩, hpAdj⟩
    rcases hpAdj a0 ha0 b0 hb0 with h20 | h30
    · refine Or.inl ⟨⟨hpDisj, ⟨a0, ha0⟩, ⟨b0, hb0⟩, ?_⟩, ?_⟩
      · intro a ha b hb
        have hb0_2 : x2.Adj a0 b := by
          rcases hpAdj a0 ha0 b hb with h | h
          · exact h
          · exact False.elim (hDisj a0 b0 b h20 h)
        rcases hpAdj a ha b hb with h | h
        · exact h
        · exact False.elim (hDisj b a0 a hb0_2.symm h.symm)
      · intro hB3
        exact hDisj a0 b0 b0 h20 (hB3.2.2.2 a0 ha0 b0 hb0)
    · refine Or.inr ⟨⟨hpDisj, ⟨a0, ha0⟩, ⟨b0, hb0⟩, ?_⟩, ?_⟩
      · intro a ha b hb
        have hb0_3 : x3.Adj a0 b := by
          rcases hpAdj a0 ha0 b hb with h | h
          · exact False.elim (hDisj3 a0 b0 b h30 h)
          · exact h
        rcases hpAdj a ha b hb with h | h
        · exact False.elim (hDisj3 b a0 a hb0_3.symm h.symm)
        · exact h
      · intro hB2
        exact hDisj3 a0 b0 b0 h30 (hB2.2.2.2 a0 ha0 b0 hb0)
  let F2 : Finset (PEqualNP.BicliqueBlockCost.Block x1) := F.filter (PEqualNP.BicliqueBlockCost.IsBlock x2)
  let F3 : Finset (PEqualNP.BicliqueBlockCost.Block x1) := F.filter (PEqualNP.BicliqueBlockCost.IsBlock x3)
  have hFdisj : Disjoint F2 F3 := by
    rw [Finset.disjoint_left]
    intro p hp2 hp3
    have h2 := Finset.mem_filter.mp hp2
    have h3 := Finset.mem_filter.mp hp3
    rcases hPart p h2.1 with ⟨_, hno⟩ | ⟨_, hno⟩
    · exact hno h3.2
    · exact hno h2.2
  have hFunion : F2 ∪ F3 = F := by
    ext p
    simp only [F2, F3, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      rcases hPart p hp with ⟨h2, _⟩ | ⟨h3, _⟩
      · exact Or.inl ⟨hp, h2⟩
      · exact Or.inr ⟨hp, h3⟩
  have hCov2 : PEqualNP.BicliqueBlockCost.IsBlockCover x2 F2 := by
    refine ⟨fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
    intro u v huv
    obtain ⟨p, hp, hpcov⟩ := hCov.2 u v (Or.inl huv)
    rcases hPart p hp with ⟨h2, _⟩ | ⟨h3, _⟩
    · exact ⟨p, Finset.mem_filter.mpr ⟨hp, h2⟩, hpcov⟩
    · rcases hpcov with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact False.elim (hDisj u v v huv (h3.2.2.2 u hu v hv))
      · exact False.elim (hDisj u v v huv (h3.2.2.2 v hv u hu).symm)
  have hCov3 : PEqualNP.BicliqueBlockCost.IsBlockCover x3 F3 := by
    refine ⟨fun p hp => (Finset.mem_filter.mp hp).2, ?_⟩
    intro u v huv
    obtain ⟨p, hp, hpcov⟩ := hCov.2 u v (Or.inr huv)
    rcases hPart p hp with ⟨h2, _⟩ | ⟨h3, _⟩
    · rcases hpcov with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact False.elim (hDisj3 u v v huv (h2.2.2.2 u hu v hv))
      · exact False.elim (hDisj3 u v v huv (h2.2.2.2 v hv u hu).symm)
    · exact ⟨p, Finset.mem_filter.mpr ⟨hp, h3⟩, hpcov⟩
  have hF2ne : F2.Nonempty := by
    rcases hNE2 with ⟨u, v, huv⟩
    obtain ⟨p, hp, _⟩ := hCov2.2 u v huv
    exact ⟨p, hp⟩
  have hF3ne : F3.Nonempty := by
    rcases hNE3 with ⟨u, v, huv⟩
    obtain ⟨p, hp, _⟩ := hCov3.2 u v huv
    exact ⟨p, hp⟩
  have hSum : (∑ p ∈ F, PEqualNP.BicliqueBlockCost.blockCost p) =
      (∑ p ∈ F2, PEqualNP.BicliqueBlockCost.blockCost p) +
      (∑ p ∈ F3, PEqualNP.BicliqueBlockCost.blockCost p) := by
    rw [← hFunion, Finset.sum_union hFdisj]
  have hCard : F.card = F2.card + F3.card := by
    rw [← hFunion, Finset.card_union_of_disjoint hFdisj]
  have hPos2 : 1 ≤ F2.card := Finset.card_pos.mpr hF2ne
  have hPos3 : 1 ≤ F3.card := Finset.card_pos.mpr hF3ne
  have hCostEq : PEqualNP.BicliqueBlockCost.familyCost F2 + PEqualNP.BicliqueBlockCost.familyCost F3 + (1 : ℕ) =
      PEqualNP.BicliqueBlockCost.familyCost F := by
    dsimp only [PEqualNP.BicliqueBlockCost.familyCost]
    omega
  have hC2 := @hBlockToCircuit x1 x2 x4 (PEqualNP.BicliqueBlockCost.familyCost F2) ⟨F2, hCov2, le_rfl⟩
  have hC3 := @hBlockToCircuit x1 x3 x5 (PEqualNP.BicliqueBlockCost.familyCost F3) ⟨F3, hCov3, le_rfl⟩
  exact ⟨PEqualNP.BicliqueBlockCost.familyCost F2, PEqualNP.BicliqueBlockCost.familyCost F3, by omega, hC2, hC3⟩
