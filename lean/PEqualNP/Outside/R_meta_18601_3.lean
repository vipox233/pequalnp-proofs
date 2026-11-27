import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18601_3
    (hBicliqueExtract :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj]
        (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.IsBipartite →
        PEqualNP.TopForm.NoFourCycle x2 →
        (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) →
        (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) →
        ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) →
        PEqualNP.TopForm.IsAO2 x1 x4 →
        PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        ∃ (k : ℕ) (A B : Fin k → Finset (Fin x1)),
          (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
          (∀ i, ∀ u ∈ A i, ∀ v ∈ B i, x2.Adj u v) ∧
          (∀ u v, x2.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) ∧
          (∑ i : Fin k, ((A i).card + (B i).card)) ≤ x4.size + (1 : ℕ) + x1.sqrt)
    (hBicliquePMBound :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (k : ℕ) (A B : Fin k → Finset (Fin n)),
        PEqualNP.TopForm.NoFourCycle G →
        ∀ (M : G.Subgraph), M.IsPerfectMatching →
        (∀ i, (A i).Nonempty ∧ (B i).Nonempty) →
        (∀ i, ∀ u ∈ A i, ∀ v ∈ B i, G.Adj u v) →
        (∀ u v, G.Adj u v → ∃ i, (u ∈ A i ∧ v ∈ B i) ∨ (v ∈ A i ∧ u ∈ B i)) →
        G.edgeFinset.card + n / (2 : ℕ) ≤ ∑ i : Fin k, ((A i).card + (B i).card)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt) :=
  fun x1 x2 _ x4 hBip hC4 hConn hPM hEx hAO hFun =>
    Exists.elim (hBicliqueExtract x1 x2 x4 hBip hC4 hConn hPM hEx hAO hFun) fun k hk =>
      Exists.elim hk fun A hA =>
        Exists.elim hA fun B hB =>
          Exists.elim hPM fun M hM =>
            Nat.le_trans
              (hBicliquePMBound x1 x2 k A B hC4 M hM hB.1 hB.2.1 hB.2.2.1)
              hB.2.2.2
