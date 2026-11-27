import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18886_2
    (hStarCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        ∃ (V : Finset (Fin n)),
          (∀ e ∈ PEqualNP.TopForm.starEdges G C, ∃ v ∈ V, v ∈ e) ∧
          V.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (hUstarCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        ∃ (W : Finset (Fin n)),
          (∀ e ∈ PEqualNP.TopForm.Ustar G C, ∃ v ∈ W, v ∈ e) ∧
          W.card + (PEqualNP.TopForm.Ustar G C).card ≤
            (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
            (PEqualNP.TopForm.junk G C).card +
            (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x10 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x10 ∧ x10.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card) :=
  fun n G _ C hC4 hNE hLeast hTF hJunk =>
    Exists.elim (hStarCover n G C hC4 hLeast hTF) fun V1 hV1 =>
      Exists.elim (hUstarCover n G C hC4 hNE hLeast hTF hJunk) fun V2 hV2 =>
        ⟨V1 ∪ V2,
          fun u v huv =>
            Or.elim (Decidable.em (s(u, v) ∈ PEqualNP.TopForm.starEdges G C))
              (fun hs => Exists.elim (hV1.1 s(u, v) hs) fun w hw =>
                Or.elim (Sym2.mem_iff.mp hw.2)
                  (fun hwu => Or.inl (Finset.mem_union_left V2 (hwu ▸ hw.1)))
                  (fun hwv => Or.inr (Finset.mem_union_left V2 (hwv ▸ hw.1))))
              (fun hns => Exists.elim (hV2.1 s(u, v) (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv, hns⟩)) fun w hw =>
                Or.elim (Sym2.mem_iff.mp hw.2)
                  (fun hwu => Or.inl (Finset.mem_union_right V1 (hwu ▸ hw.1)))
                  (fun hwv => Or.inr (Finset.mem_union_right V1 (hwv ▸ hw.1)))),
          by
            have h1 := Finset.card_union_le V1 V2
            have h2 := hV1.2
            have h3 := hV2.2
            omega⟩
