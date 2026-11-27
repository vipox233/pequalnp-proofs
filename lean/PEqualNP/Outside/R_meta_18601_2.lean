import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18601_2
    (hVC :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
        (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.IsBipartite →
        PEqualNP.TopForm.NoFourCycle x2 →
        (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) →
        (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) →
        ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) →
        PEqualNP.TopForm.IsAO2 x1 x4 →
        PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        ∃ (V : Finset (Fin x1)),
          (∀ u v : Fin x1, x2.Adj u v → u ∈ V ∨ v ∈ V) ∧
          x2.edgeFinset.card + V.card ≤ x4.size + (1 : ℕ) + x1.sqrt)
    (hMatchVC :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (M : G.Subgraph) (V : Finset (Fin n)),
        M.IsPerfectMatching →
        (∀ u v : Fin n, G.Adj u v → u ∈ V ∨ v ∈ V) →
        n ≤ (2 : ℕ) * V.card) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt) := by
  intro x1 x2 x3 x4 hBip hC4 hConn hPM hEx hAO hFun
  obtain ⟨V, hcov, hbd⟩ := @hVC x1 x2 x3 x4 hBip hC4 hConn hPM hEx hAO hFun
  obtain ⟨M, hM⟩ := hPM
  have h2 : x1 ≤ (2 : ℕ) * V.card := hMatchVC x1 x2 M V hM hcov
  omega
