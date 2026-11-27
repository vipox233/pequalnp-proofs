import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Matching
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18601_5
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hTopFormPM :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.IsBipartite →
        PEqualNP.TopForm.NoFourCycle x2 →
        (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) →
        (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) →
        ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) →
        PEqualNP.TopForm.IsLeastAO x2 x4 →
        PEqualNP.TopForm.TopForm x2 x4 →
        x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      x2.IsBipartite →
      PEqualNP.TopForm.NoFourCycle x2 →
      (∀ (x7 : Finset (Fin x1)), x7.card ≤ (2 : ℕ) → (SimpleGraph.induce (↑x7)ᶜ x2).Connected) →
      (∃ (x8 : x2.Subgraph), x8.IsPerfectMatching) →
      ((2 : ℕ) * x2.edgeFinset.card - (3 : ℕ) * x1) ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) →
      PEqualNP.TopForm.IsAO2 x1 x4 →
      PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
      x2.edgeFinset.card + x1 / (2 : ℕ) ≤ x4.size + (1 : ℕ) + x1.sqrt := by
  classical
  intro x1 x2 x3 x4 hBip hC4 hConn hPM hDens hAO hFun
  by_cases h0 : x1 = 0
  · subst h0
    have hemp : x2.edgeFinset = ∅ := Finset.eq_empty_of_isEmpty _
    rw [hemp]
    simp
  · have hpos : 0 < x1 := Nat.pos_of_ne_zero h0
    rcases hPM with ⟨M, hM⟩
    let v0 : Fin x1 := ⟨0, hpos⟩
    have hv : v0 ∈ M.verts := hM.2 v0
    obtain ⟨w, hw, _⟩ := hM.1 hv
    have hadj : x2.Adj v0 w := M.adj_sub hw
    have hNE : x2.edgeFinset.Nonempty := ⟨s(v0, w), SimpleGraph.mem_edgeFinset.mpr hadj⟩
    obtain ⟨D, hLeast, hTF, hDle⟩ := @hNorm x1 x2 x3 x4 hNE hAO hFun
    have hBnd := @hTopFormPM x1 x2 x3 D hBip hC4 hConn ⟨M, hM⟩ hDens hLeast hTF
    omega
