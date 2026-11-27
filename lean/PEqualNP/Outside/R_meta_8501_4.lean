import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8501_4
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hTopFormDiag :
      ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1))
        (G : SimpleGraph (Fin (x1 + x1))) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        have diag : Finset (Fin x1) := {v : Fin x1 | (v, v) ∈ x2};
        (∀ a b : Fin x1, x3 a ≠ x4 b) →
        (∀ u v : Fin (x1 + x1), G.Adj u v ↔ ∃ a b : Fin x1, (a, b) ∈ x2 ∧ ((u = x3 a ∧ v = x4 b) ∨ (u = x4 b ∧ v = x3 a))) →
        (∀ a b : Fin x1, (a, b) ∈ x2 → (a, a) ∈ x2 ∧ (b, b) ∈ x2) →
        PEqualNP.TopForm.NoFourCycle G →
        (3 : ℕ) ≤ diag.card →
        diag.card < x1 →
        (2 : ℕ) * diag.card ≤ x2.card →
        (∀ v : Fin x1, (v, v) ∈ x2 → (∃ w : Fin x1, w ≠ v ∧ (v, w) ∈ x2) ∧ ∃ w : Fin x1, w ≠ v ∧ (w, v) ∈ x2) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        x2.card + diag.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x1)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x6 ∧ x8 (x3 x9) = Bool.true ∧ x8 (x4 x10) = Bool.true);   (∀ (x7 x8 : Fin x1), x3 x7 ≠ x4 x8) →     (∀ (x8 x9 : Fin x1), (x8, x9) ∈ x2 → (x8, x8) ∈ x2 ∧ (x9, x9) ∈ x2) →       (∀ (x9 x10 x11 x12 : Fin x1), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x2 ∧ (x9, x12) ∈ x2 ∧ (x10, x11) ∈ x2 ∧ (x10, x12) ∈ x2)) →         have x10 : Finset (Fin x1) := {x10 : Fin x1 | (x10, x10) ∈ x2};         (3 : ℕ) ≤ x10.card → x10.card < x1 → (2 : ℕ) * x10.card ≤ x2.card → (∀ (x14 : Fin x1), (x14, x14) ∈ x2 → (∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x14, x16) ∈ x2) ∧ ∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x16, x14) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x6 x2 x5 → x2.card + x10.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro x1 x2 x3 x4 x5 x6 hDisj hDiag hC4 x10 hGe3 hLt h2m hDeg hAO hFun
  let adj : Fin (x1 + x1) → Fin (x1 + x1) → Prop := fun u v =>
    ∃ a b : Fin x1, (a, b) ∈ x2 ∧ ((u = x3 a ∧ v = x4 b) ∨ (u = x4 b ∧ v = x3 a))
  let G : SimpleGraph (Fin (x1 + x1)) :=
    { Adj := adj
      symm := ⟨by
        rintro u v ⟨a, b, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨a, b, h, Or.inr ⟨rfl, rfl⟩⟩
        · exact ⟨a, b, h, Or.inl ⟨rfl, rfl⟩⟩⟩
      loopless := ⟨by
        rintro u ⟨a, b, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact hDisj a b (h1.symm.trans h2)
        · exact hDisj a b (h2.symm.trans h1)⟩ }
  have hGadj : ∀ u v : Fin (x1 + x1), G.Adj u v ↔ ∃ a b : Fin x1, (a, b) ∈ x2 ∧ ((u = x3 a ∧ v = x4 b) ∨ (u = x4 b ∧ v = x3 a)) :=
    fun _ _ => Iff.rfl
  have hlr : ∀ a b : Fin x1, G.Adj (x3 a) (x4 b) ↔ (a, b) ∈ x2 := by
    intro a b
    constructor
    · rintro ⟨a', b', h, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
      · rw [x3.injective h1, x4.injective h2]
        exact h
      · exact False.elim (hDisj a b' h1)
    · intro h
      exact ⟨a, b, h, Or.inl ⟨rfl, rfl⟩⟩
  have hC4G : PEqualNP.TopForm.NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases hx'.1 with ⟨a1, b1, h1, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rcases hx'.2 with ⟨a2, b2, h2, ⟨rfl, hxb2⟩ | ⟨_, hxa2⟩⟩
      · have hb : b1 = b2 := x4.injective hxb2
        subst hb
        rcases hy'.1 with ⟨a3, b3, h3, ⟨ha3, rfl⟩ | ⟨hb3, _⟩⟩
        · have ha : a1 = a3 := x3.injective ha3
          subst ha
          rcases hy'.2 with ⟨a4, b4, h4, ⟨ha4, hb4⟩ | ⟨hb4, _⟩⟩
          · have ha' : a2 = a4 := x3.injective ha4
            have hb' : b3 = b4 := x4.injective hb4
            subst ha'; subst hb'
            by_contra hxy
            exact hC4 a1 a2 b1 b3
              (fun h => huv (congrArg x3 h))
              (fun h => hxy (congrArg x4 h))
              ⟨h1, h3, h2, h4⟩
          · exact False.elim (hDisj a2 b4 hb4)
        · exact False.elim (hDisj a1 b3 hb3)
      · exact False.elim (hDisj a2 b1 hxa2.symm)
    · rcases hx'.2 with ⟨a2, b2, h2, ⟨_, hxa2⟩ | ⟨rfl, hxa2⟩⟩
      · exact False.elim (hDisj a1 b2 hxa2)
      · have ha : a1 = a2 := x3.injective hxa2
        subst ha
        rcases hy'.1 with ⟨a3, b3, h3, ⟨ha3, _⟩ | ⟨hb3, rfl⟩⟩
        · exact False.elim (hDisj a3 b1 ha3.symm)
        · have hb : b1 = b3 := x4.injective hb3
          subst hb
          rcases hy'.2 with ⟨a4, b4, h4, ⟨ha4, _⟩ | ⟨hb4, ha4⟩⟩
          · exact False.elim (hDisj a4 b2 ha4.symm)
          · have hb' : b2 = b4 := x4.injective hb4
            have ha' : a3 = a4 := x3.injective ha4
            subst hb'; subst ha'
            by_contra hxy
            exact hC4 a1 a3 b1 b2
              (fun h => hxy (congrArg x3 h))
              (fun h => huv (congrArg x4 h))
              ⟨h1, h2, h3, h4⟩
  have hne10 : x10.Nonempty := Finset.card_pos.mp (by omega)
  rcases hne10 with ⟨v0, hv0⟩
  have hv0m : (v0, v0) ∈ x2 := (Finset.mem_filter.mp hv0).2
  have hGne : G.edgeFinset.Nonempty :=
    ⟨s(x3 v0, x4 v0), SimpleGraph.mem_edgeFinset.mpr ((hlr v0 v0).mpr hv0m)⟩
  have hcfun : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hFun z]
    change decide (∃ (a b : Fin x1), (a, b) ∈ x2 ∧ z (x3 a) = true ∧ z (x4 b) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (x1 + x1))), z a = true) ||
       decide (∃ u v : Fin (x1 + x1), G.Adj u v ∧ z u = true ∧ z v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, h, ha, hb⟩
      exact ⟨x3 a, x4 b, (hlr a b).mpr h, ha, hb⟩
    · rintro ⟨u, v, ⟨a, b, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨a, b, h, hu, hv⟩
      · exact ⟨a, b, h, hv, hu⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (x1 + x1) G x5 hGne hAO hcfun
  have hBnd := hTopFormDiag x1 x2 x3 x4 G D hDisj hGadj hDiag hC4G hGe3 hLt h2m hDeg hLeast hTF
  change x2.card + x10.card ≤ D.size + (1 : ℕ) at hBnd
  omega
