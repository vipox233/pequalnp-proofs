import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7866_4
    (hAccount :
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        G.edgeFinset.card +
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
          C.size + (PEqualNP.TopForm.Ustar G C).card + (1 : ℕ))
    (hMatchCharge :
      ∃ (c : ℕ), ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (M : Finset (Sym2 (Fin m))),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).Nonempty →
        M ⊆ G.edgeFinset →
        (∀ e ∈ M, ∀ f ∈ M, ∀ v ∈ e, v ∈ f → e = f) →
        (PEqualNP.TopForm.Ustar G C).card + M.card ≤
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card +
          c * (m + (1 : ℕ)).sqrt) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Sym2 (Fin x2))), PEqualNP.TopForm.NoFourCycle x3 → (∃ (x8 : Fin x2) (x9 : Fin x2), x3.Adj x8 x9) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → (∀ x12 ∈ x6, x12 ∈ x3.edgeSet) → (∀ x13 ∈ x6, ∀ x15 ∈ x6, ∀ x17 ∈ x13, x17 ∈ x15 → x13 = x15) → x3.edgeSet.ncard + x6.card ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt := by
  classical
  obtain ⟨c, hc⟩ := hMatchCharge
  refine ⟨c, ?_⟩
  intro m G _x4 C M hno4 hex hLeast hTF hJunk hMsub hMdisj
  rcases hex with ⟨u, v, huv⟩
  have hGne : G.edgeFinset.Nonempty := ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr huv⟩
  have hMsub' : M ⊆ G.edgeFinset := by
    intro e he
    exact SimpleGraph.mem_edgeFinset.mpr (hMsub e he)
  have hncard : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset]
    exact Set.ncard_coe_finset G.edgeFinset
  have hAcc := hAccount m G C hno4 hGne hLeast hTF
  have hChg := hc m G C M hno4 hGne hLeast hTF hJunk hMsub' hMdisj
  omega
