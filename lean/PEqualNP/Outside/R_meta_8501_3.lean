import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8501_3
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hGraphCoverLB :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        (∀ c u : Fin n, G.Adj c u → ∃ v w : Fin n, G.Adj c v ∧ G.Adj v w ∧ w ≠ c) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ S : Finset (Fin n),
          (∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S) ∧
          G.edgeFinset.card + S.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x1)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x8 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), (x9, x10) ∈ x6 ∧ x8 (x3 x9) = Bool.true ∧ x8 (x4 x10) = Bool.true);   (∀ (x7 x8 : Fin x1), x3 x7 ≠ x4 x8) →     (∀ (x8 x9 : Fin x1), (x8, x9) ∈ x2 → (x8, x8) ∈ x2 ∧ (x9, x9) ∈ x2) →       (∀ (x9 x10 x11 x12 : Fin x1), x9 ≠ x10 → x11 ≠ x12 → ¬((x9, x11) ∈ x2 ∧ (x9, x12) ∈ x2 ∧ (x10, x11) ∈ x2 ∧ (x10, x12) ∈ x2)) →         have x10 : Finset (Fin x1) := {x10 : Fin x1 | (x10, x10) ∈ x2};         (3 : ℕ) ≤ x10.card → x10.card < x1 → (2 : ℕ) * x10.card ≤ x2.card → (∀ (x14 : Fin x1), (x14, x14) ∈ x2 → (∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x14, x16) ∈ x2) ∧ ∃ (x16 : Fin x1), x16 ≠ x14 ∧ (x16, x14) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x6 x2 x5 → x2.card + x10.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n E f g C comp hDisj hDiag hc4 diag hGe3 _ _ hDeg hAO hFun
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
  let enc : Fin n × Fin n → Sym2 (Fin (n + n)) := fun e => s(f e.1, g e.2)
  have hencInj : Function.Injective enc := by
    intro e1 e2 h
    change s(f e1.1, g e1.2) = s(f e2.1, g e2.2) at h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨hbad, _⟩
    · exact Prod.ext (f.injective h1) (g.injective h2)
    · exact False.elim (hDisj e1.1 e2.2 hbad)
  have hedges : G.edgeFinset = E.image enc := by
    ext s
    induction s using Sym2.ind with
    | _ u v =>
      constructor
      · intro hs
        have hadj : G.Adj u v := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hs
        rcases hadj with ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨e, he, rfl⟩
        · exact Finset.mem_image.mpr ⟨e, he, Sym2.eq_swap⟩
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨e, he, hsym⟩
        rw [← hsym]
        simpa only [enc, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (hlr e.1 e.2).mpr he
  have hedgeCard : G.edgeFinset.card = E.card := by
    rw [hedges, Finset.card_image_of_injective _ hencInj]
  have hGne : G.edgeFinset.Nonempty := by
    obtain ⟨a0, ha0⟩ := Finset.card_pos.mp (by omega : 0 < diag.card)
    have ha0E : (a0, a0) ∈ E := (Finset.mem_filter.mp ha0).2
    rw [← Finset.card_pos, hedgeCard]
    exact Finset.card_pos.mpr ⟨(a0, a0), ha0E⟩
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
  have hNoStar : ∀ c u : Fin (n + n), G.Adj c u → ∃ v w : Fin (n + n), G.Adj c v ∧ G.Adj v w ∧ w ≠ c := by
    intro c u hcu
    rcases hcu with ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · have haa : (e.1, e.1) ∈ E := (hDiag e.1 e.2 he).1
      obtain ⟨a', ha'ne, ha'E⟩ := (hDeg e.1 haa).2
      exact ⟨g e.1, f a', (hlr e.1 e.1).mpr haa, ((hlr a' e.1).mpr ha'E).symm, fun h => ha'ne (f.injective h)⟩
    · have hbb : (e.2, e.2) ∈ E := (hDiag e.1 e.2 he).2
      obtain ⟨b', hb'ne, hb'E⟩ := (hDeg e.2 hbb).1
      exact ⟨f e.2, g b', ((hlr e.2 e.2).mpr hbb).symm, (hlr e.2 b').mpr hb'E, fun h => hb'ne (g.injective h)⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (n + n) G C hGne hAO hcfun
  obtain ⟨S, hScov, hScard⟩ := hGraphCoverLB (n + n) G D hno4 hGne hNoStar hLeast hTF
  let pick : Fin n → Fin (n + n) := fun a => if f a ∈ S then f a else g a
  have hpickInj : Function.Injective pick := by
    intro a b hab
    dsimp only [pick] at hab
    by_cases ha : f a ∈ S <;> by_cases hb : f b ∈ S <;> simp only [ha, hb, ite_true, ite_false] at hab
    · exact f.injective hab
    · exact False.elim (hDisj a b hab)
    · exact False.elim (hDisj b a hab.symm)
    · exact g.injective hab
  have hpickSub : diag.image pick ⊆ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, ha, rfl⟩
    have haa : (a, a) ∈ E := (Finset.mem_filter.mp ha).2
    dsimp only [pick]
    by_cases hfa : f a ∈ S
    · rw [if_pos hfa]
      exact hfa
    · rw [if_neg hfa]
      exact (hScov (f a) (g a) ((hlr a a).mpr haa)).resolve_left hfa
  have hdiagLe : diag.card ≤ S.card := by
    rw [← Finset.card_image_of_injective diag hpickInj]
    exact Finset.card_le_card hpickSub
  omega
