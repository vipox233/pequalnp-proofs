import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8387_2
    (hStarCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        ∃ S : Finset (Fin n),
          (∀ u v : Fin n, G.Adj u v → s(u, v) ∈ PEqualNP.TopForm.starEdges G C → u ∈ S ∨ v ∈ S) ∧
          S.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (hUstarVC :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin (x1 + x1))) [x3 : DecidableRel x2.Adj]
        (x4 : Fin (x1 + x1) → Bool) (x5 : Fin (x1 + x1) → Fin (x1 + x1)) (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle x2 →
        (∀ (x8 x9 : Fin x1), ¬x2.Adj (Fin.castAdd x1 x8) (Fin.castAdd x1 x9)) →
        (∀ (x9 x10 : Fin x1), ¬x2.Adj (Fin.natAdd x1 x9) (Fin.natAdd x1 x10)) →
        (∀ (x10 x11 : Fin (x1 + x1)), x2.Adj x10 x11 → x4 x10 ≠ x4 x11) →
        Function.Involutive x5 →
        (∀ (x12 : Fin (x1 + x1)), x2.Adj x12 (x5 x12)) →
        (∀ (x13 : Fin (x1 + x1)), ∃ (x14 : Fin (x1 + x1)), x2.Adj x13 x14 ∧ x14 ≠ x5 x13) →
        (∀ (x14 : Fin (x1 + x1)), ∃ (x15 : Fin (x1 + x1)), x2.Adj x15 x14 ∧ x15 ≠ x5 x14) →
        PEqualNP.TopForm.IsLeastAO x2 x6 →
        PEqualNP.TopForm.TopForm x2 x6 →
        ∃ V : Finset (Fin (x1 + x1)),
          (∀ u v : Fin (x1 + x1), x2.Adj u v → s(u, v) ∈ PEqualNP.TopForm.Ustar x2 x6 → u ∈ V ∨ v ∈ V) ∧
          V.card + (PEqualNP.TopForm.Ustar x2 x6).card ≤
            (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card + (PEqualNP.TopForm.junk x2 x6).card +
            (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin (x1 + x1))) [x3 : DecidableRel x2.Adj] (x4 : Fin (x1 + x1) → Bool) (x5 : Fin (x1 + x1) → Fin (x1 + x1)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → (∀ (x8 x9 : Fin x1), ¬x2.Adj (Fin.castAdd x1 x8) (Fin.castAdd x1 x9)) → (∀ (x9 x10 : Fin x1), ¬x2.Adj (Fin.natAdd x1 x9) (Fin.natAdd x1 x10)) → (∀ (x10 x11 : Fin (x1 + x1)), x2.Adj x10 x11 → x4 x10 ≠ x4 x11) → Function.Involutive x5 → (∀ (x12 : Fin (x1 + x1)), x2.Adj x12 (x5 x12)) → (∀ (x13 : Fin (x1 + x1)), ∃ (x14 : Fin (x1 + x1)), x2.Adj x13 x14 ∧ x14 ≠ x5 x13) → (∀ (x14 : Fin (x1 + x1)), ∃ (x15 : Fin (x1 + x1)), x2.Adj x15 x14 ∧ x15 ≠ x5 x14) → PEqualNP.TopForm.IsLeastAO x2 x6 → PEqualNP.TopForm.TopForm x2 x6 → (PEqualNP.TopForm.Ustar x2 x6).card + x1 ≤ (PEqualNP.TopForm.tops x2 x6 \ PEqualNP.TopForm.centreless x2 x6).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card + (PEqualNP.TopForm.junk x2 x6).card + (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card) := by
  classical
  intro x1 x2 x3 x4 x5 x6 hC4 hB1 hB2 hCol hInv hMatch hDeg1 hDeg2 hLeast hTF
  obtain ⟨S, hScov, hScard⟩ := @hStarCover (x1 + x1) x2 x3 x6 hC4 hLeast hTF
  obtain ⟨V, hVcov, hVcard⟩ := @hUstarVC x1 x2 x3 x4 x5 x6 hC4 hB1 hB2 hCol hInv hMatch hDeg1 hDeg2 hLeast hTF
  have hWcov : ∀ u : Fin (x1 + x1), u ∈ S ∪ V ∨ x5 u ∈ S ∪ V := by
    intro u
    have hadj : x2.Adj u (x5 u) := hMatch u
    by_cases hs : s(u, x5 u) ∈ PEqualNP.TopForm.starEdges x2 x6
    · rcases hScov u (x5 u) hadj hs with h | h
      · exact Or.inl (Finset.mem_union_left V h)
      · exact Or.inr (Finset.mem_union_left V h)
    · have hu : s(u, x5 u) ∈ PEqualNP.TopForm.Ustar x2 x6 :=
        Finset.mem_sdiff.mpr ⟨x2.mem_edgeFinset.mpr hadj, hs⟩
      rcases hVcov u (x5 u) hadj hu with h | h
      · exact Or.inl (Finset.mem_union_right S h)
      · exact Or.inr (Finset.mem_union_right S h)
  have hUniv : (Finset.univ : Finset (Fin (x1 + x1))) ⊆ (S ∪ V) ∪ (S ∪ V).image x5 := by
    intro u _
    rcases hWcov u with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x5 u, h, hInv u⟩)
  have h1 : x1 + x1 ≤ ((S ∪ V) ∪ (S ∪ V).image x5).card := by
    have := Finset.card_le_card hUniv
    simpa [Finset.card_univ, Fintype.card_fin] using this
  have h2 : ((S ∪ V) ∪ (S ∪ V).image x5).card ≤ (S ∪ V).card + ((S ∪ V).image x5).card :=
    Finset.card_union_le _ _
  have h3 : ((S ∪ V).image x5).card ≤ (S ∪ V).card := Finset.card_image_le
  have h4 : (S ∪ V).card ≤ S.card + V.card := Finset.card_union_le S V
  omega
