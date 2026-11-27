import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8499_3
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hTopDeletePendant :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit)
        (u0 v0 : Fin n),
        (∃ col : Fin n → Bool, ∀ u v : Fin n, G.Adj u v → col u ≠ col v) →
        PEqualNP.TopForm.NoFourCycle G →
        G.Adj u0 v0 →
        G.neighborFinset u0 = {v0} →
        (G.deleteEdges {e : Sym2 (Fin n) | u0 ∈ e ∨ v0 ∈ e}).edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 n C' ∧
          PEqualNP.MetaComplexity.circuitFun n C' =
            PEqualNP.MetaComplexity.NestedCover.graphFun (G.deleteEdges {e : Sym2 (Fin n) | u0 ∈ e ∨ v0 ∈ e}) ∅ ∧
          C'.size + (G.neighborFinset v0).card + (1 : ℕ) ≤ D.size) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1) (x7 : Bool),   have x8 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : Finset (Fin x1 × Fin x1)) (x9 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x8 ∧ x10 (x3 x11) = Bool.true ∧ x10 (x4 x12) = Bool.true);   let x9 : Fin x1 → Fin x1 → Prop := fun (x9 x10 : Fin x1) => if x7 = Bool.true then (x10, x9) ∈ x2 else (x9, x10) ∈ x2;   have x10 : Finset (Fin x1) := {x10 : Fin x1 | x10 ≠ x6 ∧ x9 x10 x6};   have x11 : Finset (Fin x1 × Fin x1) := {x11 ∈ x2 | x11.1 ≠ x6 ∧ x11.2 ≠ x6};   (∀ (x12 x13 : Fin x1), x3 x12 ≠ x4 x13) → (∀ (x13 x14 : Fin x1), (x13, x14) ∈ x2 → (x13, x13) ∈ x2 ∧ (x14, x14) ∈ x2) → (∀ (x14 x15 x16 x17 : Fin x1), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x2 ∧ (x14, x17) ∈ x2 ∧ (x15, x16) ∈ x2 ∧ (x15, x17) ∈ x2)) → (x6, x6) ∈ x2 → (∃ (x16 : Fin x1) (x17 : Fin x1), x16 ≠ x17 ∧ (x16, x16) ∈ x11 ∧ (x17, x17) ∈ x11) → (∀ (x17 : Fin x1), x9 x6 x17 → x17 = x6) → (∀ x18 ∈ x10, ∀ x20 ∈ x10, x9 x18 x20 ↔ x18 = x20) → (∀ x19 ∈ x10, ∀ x21 ∈ x10, x19 ≠ x21 → ∀ (x24 : Fin x1), x24 ≠ x6 → ¬(x9 x19 x24 ∧ x9 x21 x24)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x8 x2 x5 → ∃ (x22 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x22 ∧ x8 x11 x22 ∧ x22.size + x10.card + (2 : ℕ) ≤ x5.size := by
  classical
  intro n E f g C a0 dir comp rel nbrs E' hDisj _ hc4 ha0 hTwo hDeg1 _ _ hAO hFun
  let adj : Fin (n + n) → Fin (n + n) → Prop := fun u v =>
    ∃ e ∈ E, (u = f e.1 ∧ v = g e.2) ∨ (v = f e.1 ∧ u = g e.2)
  let G : SimpleGraph (Fin (n + n)) :=
    { Adj := adj
      symm := ⟨by
        rintro u v ⟨e, he, hor⟩
        exact ⟨e, he, hor.symm⟩⟩
      loopless := ⟨by
        rintro u ⟨e, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hDisj e.1 e.2 (h1.symm.trans h2)
        · exact hDisj e.1 e.2 (h1.symm.trans h2)⟩ }
  have hlr : ∀ a b : Fin n, G.Adj (f a) (g b) ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · rintro ⟨⟨u, v⟩, he, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
      · have ha : a = u := f.injective h1
        have hb : b = v := g.injective h2
        subst ha; subst hb
        exact he
      · exact False.elim (hDisj u b h1.symm)
    · intro he
      exact ⟨(a, b), he, Or.inl ⟨rfl, rfl⟩⟩
  have hBip : ∃ col : Fin (n + n) → Bool, ∀ u v : Fin (n + n), G.Adj u v → col u ≠ col v := by
    refine ⟨fun v => decide (∃ a : Fin n, v = f a), ?_⟩
    rintro u v ⟨e, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · have h1 : ∃ a : Fin n, f e.1 = f a := ⟨e.1, rfl⟩
      have h2 : ¬∃ a : Fin n, g e.2 = f a := by
        rintro ⟨a, ha⟩
        exact hDisj a e.2 ha.symm
      simp [h1, h2]
    · have h1 : ¬∃ a : Fin n, g e.2 = f a := by
        rintro ⟨a, ha⟩
        exact hDisj a e.2 ha.symm
      have h2 : ∃ a : Fin n, f e.1 = f a := ⟨e.1, rfl⟩
      simp [h1, h2]
  have hno4 : PEqualNP.TopForm.NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases hx'.1 with ⟨⟨a1, b1⟩, he1, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · rcases hx'.2 with ⟨⟨a2, b2⟩, he2, ⟨rfl, h2⟩ | ⟨h1, _⟩⟩
      · have hb2 : b1 = b2 := g.injective h2
        subst hb2
        rcases hy'.1 with ⟨⟨a3, b3⟩, he3, ⟨h3, rfl⟩ | ⟨_, h4⟩⟩
        · have ha3 : a1 = a3 := f.injective h3
          subst ha3
          by_contra hxy
          exact hc4 a1 a2 b1 b3
            (fun h => huv (congrArg f h))
            (fun h => hxy (congrArg g h))
            ⟨he1, he3, he2, (hlr a2 b3).mp hy'.2⟩
        · exact False.elim (hDisj a1 b3 h4)
      · exact False.elim (hDisj a2 b1 h1.symm)
    · rcases hx'.2 with ⟨⟨a2, b2⟩, he2, ⟨_, h2⟩ | ⟨h1, rfl⟩⟩
      · exact False.elim (hDisj a1 b2 h2)
      · have ha2 : a1 = a2 := f.injective h1
        subst ha2
        rcases hy'.1 with ⟨⟨a3, b3⟩, he3, ⟨h3, _⟩ | ⟨rfl, h4⟩⟩
        · exact False.elim (hDisj a3 b1 h3.symm)
        · have hb3 : b1 = b3 := g.injective h4
          subst hb3
          by_contra hxy
          exact hc4 a1 a3 b1 b2
            (fun h => hxy (congrArg f h))
            (fun h => huv (congrArg g h))
            ⟨he1, he2, he3, (hlr a3 b2).mp hy'.2.symm⟩
  have hGne : G.edgeFinset.Nonempty :=
    ⟨s(f a0, g a0), SimpleGraph.mem_edgeFinset.mpr ((hlr a0 a0).mpr ha0)⟩
  have hcfun : PEqualNP.MetaComplexity.circuitFun (n + n) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hFun z]
    change decide (∃ (a b : Fin n), (a, b) ∈ E ∧ z (f a) = true ∧ z (g b) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (n + n))), z a = true) ||
       decide (∃ u v : Fin (n + n), G.Adj u v ∧ z u = true ∧ z v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨f a, g b, (hlr a b).mpr hab, ha, hb⟩
    · rintro ⟨u, v, ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨e.1, e.2, he, hu, hv⟩
      · exact ⟨e.1, e.2, he, hv, hu⟩
  let u0 : Fin (n + n) := if dir = true then g a0 else f a0
  let v0 : Fin (n + n) := if dir = true then f a0 else g a0
  have huvAdj : G.Adj u0 v0 := by
    cases dir
    · exact (hlr a0 a0).mpr ha0
    · exact ((hlr a0 a0).mpr ha0).symm
  have hu0N : G.neighborFinset u0 = {v0} := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_singleton]
    cases dir
    · constructor
      · rintro ⟨⟨a, b⟩, he, ⟨h1, h2⟩ | ⟨_, h2⟩⟩
        · have ha : a = a0 := f.injective h1.symm
          rw [ha] at he
          have hb : b = a0 := hDeg1 b he
          rw [hb] at h2
          exact h2
        · exact False.elim (hDisj a0 b h2)
      · rintro rfl
        exact (hlr a0 a0).mpr ha0
    · constructor
      · rintro ⟨⟨a, b⟩, he, ⟨h1, _⟩ | ⟨h1, h2⟩⟩
        · exact False.elim (hDisj a a0 h1.symm)
        · have hb : b = a0 := g.injective h2.symm
          rw [hb] at he
          have ha : a = a0 := hDeg1 a he
          rw [ha] at h1
          exact h1
      · rintro rfl
        exact ((hlr a0 a0).mpr ha0).symm
  have hv0Card : (G.neighborFinset v0).card = nbrs.card + 1 := by
    cases dir
    · have hEq : G.neighborFinset v0 = insert (f a0) (nbrs.image f) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_image, nbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨a, b⟩, he, ⟨h1, _⟩ | ⟨h1, h2⟩⟩
          · exact False.elim (hDisj a a0 h1.symm)
          · have hb : b = a0 := g.injective h2.symm
            rw [hb] at he
            by_cases ha : a = a0
            · exact Or.inl (by rw [h1, ha])
            · exact Or.inr ⟨a, ⟨ha, he⟩, h1.symm⟩
        · rintro (rfl | ⟨a, ⟨_, ha⟩, rfl⟩)
          · exact ((hlr a0 a0).mpr ha0).symm
          · exact ((hlr a a0).mpr ha).symm
      have hnot : f a0 ∉ nbrs.image f := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨a, ha, hfa⟩
        exact (Finset.mem_filter.mp ha).2.1 (f.injective hfa)
      rw [hEq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective nbrs f.injective]
    · have hEq : G.neighborFinset v0 = insert (g a0) (nbrs.image g) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_image, nbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨a, b⟩, he, ⟨h1, h2⟩ | ⟨_, h2⟩⟩
          · have ha : a = a0 := f.injective h1.symm
            rw [ha] at he
            by_cases hb : b = a0
            · exact Or.inl (by rw [h2, hb])
            · exact Or.inr ⟨b, ⟨hb, he⟩, h2.symm⟩
          · exact False.elim (hDisj a0 b h2)
        · rintro (rfl | ⟨b, ⟨_, hb⟩, rfl⟩)
          · exact (hlr a0 a0).mpr ha0
          · exact (hlr a0 b).mpr hb
      have hnot : g a0 ∉ nbrs.image g := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨b, hb, hgb⟩
        exact (Finset.mem_filter.mp hb).2.1 (g.injective hgb)
      rw [hEq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective nbrs g.injective]
  have hDelAdj : ∀ a b : Fin n,
      (G.deleteEdges {e : Sym2 (Fin (n + n)) | u0 ∈ e ∨ v0 ∈ e}).Adj (f a) (g b) ↔ (a, b) ∈ E' := by
    intro a b
    rw [SimpleGraph.deleteEdges_adj, hlr a b]
    simp only [Set.mem_setOf_eq, Sym2.mem_iff, E', Finset.mem_filter]
    cases dir
    · constructor
      · rintro ⟨hab, hnot⟩
        refine ⟨hab, fun ha => hnot (Or.inl (Or.inl (congrArg f ha.symm))),
          fun hb => hnot (Or.inr (Or.inr (congrArg g hb.symm)))⟩
      · rintro ⟨hab, ha, hb⟩
        refine ⟨hab, ?_⟩
        rintro ((h | h) | (h | h))
        · exact ha (f.injective h.symm)
        · exact hDisj a0 b h
        · exact hDisj a a0 h.symm
        · exact hb (g.injective h.symm)
    · constructor
      · rintro ⟨hab, hnot⟩
        refine ⟨hab, fun ha => hnot (Or.inr (Or.inl (congrArg f ha.symm))),
          fun hb => hnot (Or.inl (Or.inr (congrArg g hb.symm)))⟩
      · rintro ⟨hab, ha, hb⟩
        refine ⟨hab, ?_⟩
        rintro ((h | h) | (h | h))
        · exact hDisj a a0 h.symm
        · exact hb (g.injective h.symm)
        · exact ha (f.injective h.symm)
        · exact hDisj a0 b h
  have hDelNe : (G.deleteEdges {e : Sym2 (Fin (n + n)) | u0 ∈ e ∨ v0 ∈ e}).edgeFinset.Nonempty := by
    obtain ⟨b1, _, _, hb1, _⟩ := hTwo
    exact ⟨s(f b1, g b1), SimpleGraph.mem_edgeFinset.mpr ((hDelAdj b1 b1).mpr hb1)⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (n + n) G C hGne hAO hcfun
  obtain ⟨C', hC'AO, hC'f, hC'sz⟩ := hTopDeletePendant (n + n) G D u0 v0 hBip hno4 huvAdj hu0N hDelNe hLeast hTF
  refine ⟨C', hC'AO, ?_, ?_⟩
  · intro z
    rw [congrFun hC'f z]
    change (decide (∃ a ∈ (∅ : Finset (Fin (n + n))), z a = true) ||
       decide (∃ u w : Fin (n + n), (G.deleteEdges {e : Sym2 (Fin (n + n)) | u0 ∈ e ∨ v0 ∈ e}).Adj u w ∧ z u = true ∧ z w = true)) =
      decide (∃ (a b : Fin n), (a, b) ∈ E' ∧ z (f a) = true ∧ z (g b) = true)
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨u, w, huw, hu, hw⟩
      have huw' := SimpleGraph.deleteEdges_adj.mp huw
      rcases huw'.1 with ⟨e, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨e.1, e.2, (hDelAdj e.1 e.2).mp huw, hu, hw⟩
      · exact ⟨e.1, e.2, (hDelAdj e.1 e.2).mp huw.symm, hw, hu⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨f a, g b, (hDelAdj a b).mpr hab, ha, hb⟩
  · omega
