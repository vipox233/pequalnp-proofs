import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18601_4
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hTopCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        (∀ (S : Finset (Fin n)), S.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑S)ᶜ G).Connected) →
        (∃ (M : G.Subgraph), M.IsPerfectMatching) →
        ((2 : ℕ) * G.edgeFinset.card - (3 : ℕ) * n) ^ (3 : ℕ) ≤ n ^ (2 : ℕ) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ V : Finset (Fin n),
          (∀ u v : Fin n, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
          G.edgeFinset.card + V.card ≤ D.size + (1 : ℕ) + n.sqrt) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → PEqualNP.TopForm.NoFourCycle x2 → (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) → (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) → ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → PEqualNP.TopForm.IsAO2 x1 x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt := by
  classical
  intro n G _ C hBip hC4 hConn hPM hEx hAO hFun
  obtain ⟨M, hM⟩ := hPM
  let mate : Fin n → Fin n := fun v => Classical.choose (hM.1 (hM.2 v))
  have hmadj : ∀ v : Fin n, M.Adj v (mate v) := fun v => (Classical.choose_spec (hM.1 (hM.2 v))).1
  have hmuniq : ∀ v w : Fin n, M.Adj v w → w = mate v :=
    fun v w h => (Classical.choose_spec (hM.1 (hM.2 v))).2 w h
  have hGadj : ∀ v : Fin n, G.Adj v (mate v) := fun v => M.adj_sub (hmadj v)
  have hminv : ∀ v : Fin n, mate (mate v) = v := fun v => (hmuniq (mate v) v (hmadj v).symm).symm
  have hminj : Function.Injective mate := by
    intro u v huv
    have := congrArg mate huv
    rwa [hminv u, hminv v] at this
  by_cases hemp : G.edgeFinset = ∅
  · have hn0 : n = 0 := by
      by_contra hne
      have hpos : 0 < n := Nat.pos_of_ne_zero hne
      let v0 : Fin n := ⟨0, hpos⟩
      have hmem : s(v0, mate v0) ∈ G.edgeFinset :=
        SimpleGraph.mem_edgeFinset.mpr (hGadj v0)
      rw [hemp] at hmem
      exact Finset.notMem_empty _ hmem
    subst hn0
    rw [hemp, Finset.card_empty]
    omega
  have hGne : G.edgeFinset.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm n G C hC4 hGne hAO hFun
  obtain ⟨V, hVcov, hVbd⟩ := hTopCover n G D hBip hC4 hGne hConn ⟨M, hM⟩ hEx hLeast hTF
  have hsub : (Finset.univ \ V).image mate ⊆ V := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨v, hv, rfl⟩
    have hvnot : v ∉ V := (Finset.mem_sdiff.mp hv).2
    exact (hVcov v (mate v) (hGadj v)).resolve_left hvnot
  have hcompl_le : (Finset.univ \ V).card ≤ V.card := by
    rw [← Finset.card_image_of_injective (Finset.univ \ V) hminj]
    exact Finset.card_le_card hsub
  have htot : V.card + (Finset.univ \ V).card = n := by
    have hdisj : Disjoint V (Finset.univ \ V) := Finset.disjoint_sdiff
    have hunion : V ∪ (Finset.univ \ V) = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ V)
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega
