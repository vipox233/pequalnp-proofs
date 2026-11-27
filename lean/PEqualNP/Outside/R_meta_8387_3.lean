import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8387_3
    (hStarMatchBound :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (M : Finset (Sym2 (Fin n))),
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        M ⊆ PEqualNP.TopForm.starEdges G C →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → ∀ v : Fin n, ¬(v ∈ e1 ∧ v ∈ e2)) →
        M.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card)
    (hUstarMatchBound :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin (x1 + x1))) [DecidableRel x2.Adj]
        (x4 : Fin (x1 + x1) → Bool) (x5 : Fin (x1 + x1) → Fin (x1 + x1))
        (x6 : PEqualNP.CircuitLowerBounds.Circuit) (M : Finset (Sym2 (Fin (x1 + x1)))),
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
        M ⊆ PEqualNP.TopForm.Ustar x2 x6 →
        (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → ∀ v : Fin (x1 + x1), ¬(v ∈ e1 ∧ v ∈ e2)) →
        (PEqualNP.TopForm.Ustar x2 x6).card + M.card ≤
          (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card +
          (PEqualNP.TopForm.junk x2 x6).card +
          (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin (x1 + x1))) [x3 : DecidableRel x2.Adj] (x4 : Fin (x1 + x1) → Bool) (x5 : Fin (x1 + x1) → Fin (x1 + x1)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → (∀ (x8 x9 : Fin x1), ¬x2.Adj (Fin.castAdd x1 x8) (Fin.castAdd x1 x9)) → (∀ (x9 x10 : Fin x1), ¬x2.Adj (Fin.natAdd x1 x9) (Fin.natAdd x1 x10)) → (∀ (x10 x11 : Fin (x1 + x1)), x2.Adj x10 x11 → x4 x10 ≠ x4 x11) → Function.Involutive x5 → (∀ (x12 : Fin (x1 + x1)), x2.Adj x12 (x5 x12)) → (∀ (x13 : Fin (x1 + x1)), ∃ (x14 : Fin (x1 + x1)), x2.Adj x13 x14 ∧ x14 ≠ x5 x13) → (∀ (x14 : Fin (x1 + x1)), ∃ (x15 : Fin (x1 + x1)), x2.Adj x15 x14 ∧ x15 ≠ x5 x14) → PEqualNP.TopForm.IsLeastAO x2 x6 → PEqualNP.TopForm.TopForm x2 x6 → (PEqualNP.TopForm.Ustar x2 x6).card + x1 ≤ (PEqualNP.TopForm.tops x2 x6 \ PEqualNP.TopForm.centreless x2 x6).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x6).card + (PEqualNP.TopForm.junk x2 x6).card + (PEqualNP.TopForm.orN x2 x6 \ PEqualNP.TopForm.lam x2 x6).card := by
  classical
  intro x1 x2 x3 x4 x5 x6 hC4 hB1 hB2 hCol hInv hMatch hDeg1 hDeg2 hLeast hTF
  have hMapR : ∀ a b : Fin x1, x5 (Fin.castAdd x1 a) ≠ Fin.castAdd x1 b := by
    intro a b h
    exact hB1 a b (h ▸ hMatch (Fin.castAdd x1 a))
  have hcastInj : Function.Injective (Fin.castAdd x1 : Fin x1 → Fin (x1 + x1)) := fun _ _ h => Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val h)
  let f : Fin x1 → Sym2 (Fin (x1 + x1)) := fun a => s(Fin.castAdd x1 a, x5 (Fin.castAdd x1 a))
  have hfInj : Function.Injective f := by
    intro a b h
    change s(Fin.castAdd x1 a, x5 (Fin.castAdd x1 a)) = s(Fin.castAdd x1 b, x5 (Fin.castAdd x1 b)) at h
    rcases Sym2.eq_iff.mp h with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hcastInj h1
    · exact False.elim (hMapR b a h1.symm)
  let M : Finset (Sym2 (Fin (x1 + x1))) := Finset.univ.image f
  have hMcard : M.card = x1 := by
    rw [Finset.card_image_of_injective _ hfInj, Finset.card_univ, Fintype.card_fin]
  have hMdisj : ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 → ∀ v : Fin (x1 + x1), ¬(v ∈ e1 ∧ v ∈ e2) := by
    intro e1 he1 e2 he2 hne v hv
    have hv1 := hv.1
    have hv2 := hv.2
    obtain ⟨a1, _, he1eq⟩ := Finset.mem_image.mp he1
    obtain ⟨a2, _, he2eq⟩ := Finset.mem_image.mp he2
    subst he1eq
    subst he2eq
    have ha : a1 ≠ a2 := fun h => hne (congrArg f h)
    rcases Sym2.mem_iff.mp hv1 with h1 | h1
    · rw [h1] at hv2
      rcases Sym2.mem_iff.mp hv2 with h2 | h2
      · exact ha (hcastInj h2)
      · exact hMapR a2 a1 h2.symm
    · rw [h1] at hv2
      rcases Sym2.mem_iff.mp hv2 with h2 | h2
      · exact hMapR a1 a2 h2
      · have h3 := congrArg x5 h2
        rw [hInv, hInv] at h3
        exact ha (hcastInj h3)
  have hMsub : M ⊆ x2.edgeFinset := by
    intro e he
    obtain ⟨a, _, heeq⟩ := Finset.mem_image.mp he
    subst heeq
    exact x2.mem_edgeFinset.mpr (hMatch (Fin.castAdd x1 a))
  let M1 : Finset (Sym2 (Fin (x1 + x1))) := M.filter (fun e => e ∈ PEqualNP.TopForm.starEdges x2 x6)
  let M2 : Finset (Sym2 (Fin (x1 + x1))) := M.filter (fun e => e ∉ PEqualNP.TopForm.starEdges x2 x6)
  have hM1sub : M1 ⊆ PEqualNP.TopForm.starEdges x2 x6 := fun _ he => (Finset.mem_filter.mp he).2
  have hM2sub : M2 ⊆ PEqualNP.TopForm.Ustar x2 x6 := by
    intro e he
    have hf := Finset.mem_filter.mp he
    exact Finset.mem_sdiff.mpr ⟨hMsub hf.1, hf.2⟩
  have hM1disj : ∀ e1 ∈ M1, ∀ e2 ∈ M1, e1 ≠ e2 → ∀ v : Fin (x1 + x1), ¬(v ∈ e1 ∧ v ∈ e2) :=
    fun e1 h1 e2 h2 => hMdisj e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
  have hM2disj : ∀ e1 ∈ M2, ∀ e2 ∈ M2, e1 ≠ e2 → ∀ v : Fin (x1 + x1), ¬(v ∈ e1 ∧ v ∈ e2) :=
    fun e1 h1 e2 h2 => hMdisj e1 (Finset.mem_filter.mp h1).1 e2 (Finset.mem_filter.mp h2).1
  have hDisj12 : Disjoint M1 M2 := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hUni12 : M1 ∪ M2 = M := by
    ext e
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      rcases h with hL | hR
      · exact hL.1
      · exact hR.1
    · intro hm
      by_cases hs : e ∈ PEqualNP.TopForm.starEdges x2 x6
      · exact Or.inl ⟨hm, hs⟩
      · exact Or.inr ⟨hm, hs⟩
  have hSplit : M1.card + M2.card = M.card := by
    rw [← Finset.card_union_of_disjoint hDisj12, hUni12]
  have h1 := @hStarMatchBound (x1 + x1) x2 x3 x6 M1 hC4 hLeast hTF hM1sub hM1disj
  have h2 := @hUstarMatchBound x1 x2 x3 x4 x5 x6 M2 hC4 hB1 hB2 hCol hInv hMatch hDeg1 hDeg2 hLeast hTF hM2sub hM2disj
  omega
