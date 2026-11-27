import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7963_5
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hTopPeel :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        (∃ u : Fin n, (G.neighborFinset u).card = (1 : ℕ)) →
        (∀ u v : Fin n, G.Adj u v → (G.neighborFinset u).card = (1 : ℕ) → (3 : ℕ) ≤ (G.neighborFinset v).card) →
        (∀ v : Fin n, (G.deleteEdges {e : Sym2 (Fin n) | v ∈ e}).edgeFinset.Nonempty) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ v : Fin n,
          (G.neighborFinset v).Nonempty ∧
          ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
            PEqualNP.MetaComplexity.Monotone2 C' ∧
            PEqualNP.MetaComplexity.circuitFun n C' =
              PEqualNP.MetaComplexity.NestedCover.graphFun (G.deleteEdges {e : Sym2 (Fin n) | v ∈ e}) ∅ ∧
            C'.size + (G.neighborFinset v).card + (1 : ℕ) ≤ D.size) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;   have x6 : Finset (Fin x1 × Fin x2) → (Fin (x1 + x2) → Bool) → Bool := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : Fin (x1 + x2) → Bool) => Decidable.decide (∃ x8 ∈ x6, x7 (Fin.castAdd x2 x8.1) = Bool.true ∧ x7 (Fin.natAdd x1 x8.2) = Bool.true);   (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 = x6 x3 → (∃ (x10 : Fin (x1 + x2)), (Finset.filter (x5 x10) x3).card = (1 : ℕ)) → (∀ (x11 x12 : Fin (x1 + x2)), x11 ≠ x12 → (Finset.filter (x5 x11) x3).card = (1 : ℕ) → (∃ x15 ∈ x3, x5 x11 x15 ∧ x5 x12 x15) → (3 : ℕ) ≤ (Finset.filter (x5 x12) x3).card) → (∀ (x12 : Fin (x1 + x2)), {x13 ∈ x3 | ¬x5 x12 x13}.Nonempty) → ∃ (x13 : Fin (x1 + x2)), (Finset.filter (x5 x13) x3).Nonempty ∧ ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x14 ∧ PEqualNP.MetaComplexity.circuitFun (x1 + x2) x14 = x6 ({x15 ∈ x3 | ¬x5 x13 x15}) ∧ x14.size + (Finset.filter (x5 x13) x3).card + (1 : ℕ) ≤ x4.size := by
  classical
  intro n m E C inc fE hc4 hAO hfun hDeg1 hDeg3 hRem
  let left : Fin n → Fin (n + m) := Fin.castAdd m
  let right : Fin m → Fin (n + m) := Fin.natAdd n
  have hsepLR : ∀ (a : Fin n) (b : Fin m), left a ≠ right b := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hleftInj : Function.Injective left := by
    intro a b h
    exact Fin.ext (by simpa [left] using congrArg Fin.val h)
  have hrightInj : Function.Injective right := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [right, Fin.val_natAdd] at hv
    exact Fin.ext (by omega)
  have hsplit : ∀ u : Fin (n + m), (∃ a : Fin n, u = left a) ∨ (∃ b : Fin m, u = right b) :=
    fun u => Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) u
  let adj : Fin (n + m) → Fin (n + m) → Prop := fun u v =>
    ∃ e ∈ E, (u = left e.1 ∧ v = right e.2) ∨ (v = left e.1 ∧ u = right e.2)
  let G : SimpleGraph (Fin (n + m)) :=
    { Adj := adj
      symm := ⟨by
        rintro u v ⟨e, he, hor⟩
        exact ⟨e, he, hor.symm⟩⟩
      loopless := ⟨by
        rintro u ⟨e, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hsepLR e.1 e.2 (h1.symm.trans h2)
        · exact hsepLR e.1 e.2 (h1.symm.trans h2)⟩ }
  have hlr : ∀ (a : Fin n) (b : Fin m), G.Adj (left a) (right b) ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · rintro ⟨⟨u, v⟩, he, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
      · have ha : a = u := hleftInj h1
        have hb : b = v := hrightInj h2
        subst ha; subst hb
        exact he
      · exact False.elim (hsepLR u b h1.symm)
    · intro he
      exact ⟨(a, b), he, Or.inl ⟨rfl, rfl⟩⟩
  have hll : ∀ a b : Fin n, ¬G.Adj (left a) (left b) := by
    rintro a b ⟨⟨u, v⟩, _, ⟨_, h2⟩ | ⟨_, h2⟩⟩
    · exact hsepLR b v h2
    · exact hsepLR a v h2
  have hrr : ∀ a b : Fin m, ¬G.Adj (right a) (right b) := by
    rintro a b ⟨⟨u, v⟩, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩
    · exact hsepLR u a h1.symm
    · exact hsepLR u b h1.symm
  have hno4 : PEqualNP.TopForm.NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases hsplit u with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases hsplit x with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact False.elim (hll a b hx'.1)
      · rcases hsplit y with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · exact False.elim (hll a c hy'.1)
        · rcases hsplit v with ⟨d, rfl⟩ | ⟨d, rfl⟩
          · by_contra hxy
            exact hc4 a d b c
              (fun h => huv (congrArg left h))
              (fun h => hxy (congrArg right h))
              ⟨(hlr a b).mp hx'.1, (hlr a c).mp hy'.1, (hlr d b).mp hx'.2, (hlr d c).mp hy'.2⟩
          · exact False.elim (hrr d b hx'.2)
    · rcases hsplit x with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · rcases hsplit y with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · rcases hsplit v with ⟨d, rfl⟩ | ⟨d, rfl⟩
          · exact False.elim (hll d b hx'.2)
          · by_contra hxy
            exact hc4 b c a d
              (fun h => hxy (congrArg left h))
              (fun h => huv (congrArg right h))
              ⟨(hlr b a).mp hx'.1.symm, (hlr b d).mp hx'.2.symm, (hlr c a).mp hy'.1.symm, (hlr c d).mp hy'.2.symm⟩
        · exact False.elim (hrr a c hy'.1)
      · exact False.elim (hrr a b hx'.1)
  have hdegEq : ∀ v : Fin (n + m), (G.neighborFinset v).card = (Finset.filter (inc v) E).card := by
    intro v
    rcases hsplit v with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · have hnf : G.neighborFinset (left a) = (Finset.filter (inc (left a)) E).image (fun e => right e.2) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_filter]
        constructor
        · intro hw
          rcases hsplit w with ⟨a', rfl⟩ | ⟨b', rfl⟩
          · exact False.elim (hll a a' hw)
          · exact ⟨(a, b'), ⟨(hlr a b').mp hw, Or.inl rfl⟩, rfl⟩
        · rintro ⟨⟨a', b'⟩, ⟨he, h1 | h2⟩, rfl⟩
          · have ha : a' = a := hleftInj h1
            subst ha
            exact (hlr a' b').mpr he
          · exact False.elim (hsepLR a b' h2.symm)
      rw [hnf]
      apply Finset.card_image_of_injOn
      intro e1 he1 e2 he2 hEq
      have hb : e1.2 = e2.2 := hrightInj hEq
      have ha1 : e1.1 = a := by
        rcases (Finset.mem_filter.mp he1).2 with h1 | h2
        · exact hleftInj h1
        · exact False.elim (hsepLR a e1.2 h2.symm)
      have ha2 : e2.1 = a := by
        rcases (Finset.mem_filter.mp he2).2 with h1 | h2
        · exact hleftInj h1
        · exact False.elim (hsepLR a e2.2 h2.symm)
      exact Prod.ext (ha1.trans ha2.symm) hb
    · have hnf : G.neighborFinset (right b) = (Finset.filter (inc (right b)) E).image (fun e => left e.1) := by
        ext w
        simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image, Finset.mem_filter]
        constructor
        · intro hw
          rcases hsplit w with ⟨a', rfl⟩ | ⟨b', rfl⟩
          · exact ⟨(a', b), ⟨(hlr a' b).mp hw.symm, Or.inr rfl⟩, rfl⟩
          · exact False.elim (hrr b b' hw)
        · rintro ⟨⟨a', b'⟩, ⟨he, h1 | h2⟩, rfl⟩
          · exact False.elim (hsepLR a' b h1)
          · have hb : b' = b := hrightInj h2
            subst hb
            exact ((hlr a' b').mpr he).symm
      rw [hnf]
      apply Finset.card_image_of_injOn
      intro e1 he1 e2 he2 hEq
      have ha : e1.1 = e2.1 := hleftInj hEq
      have hb1 : e1.2 = b := by
        rcases (Finset.mem_filter.mp he1).2 with h1 | h2
        · exact False.elim (hsepLR e1.1 b h1)
        · exact hrightInj h2
      have hb2 : e2.2 = b := by
        rcases (Finset.mem_filter.mp he2).2 with h1 | h2
        · exact False.elim (hsepLR e2.1 b h1)
        · exact hrightInj h2
      exact Prod.ext ha (hb1.trans hb2.symm)
  have hGne : G.edgeFinset.Nonempty := by
    obtain ⟨v0, hv0⟩ := hDeg1
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.filter (inc v0) E).card)
    have heE : e ∈ E := (Finset.mem_filter.mp he).1
    exact ⟨s(left e.1, right e.2), SimpleGraph.mem_edgeFinset.mpr ((hlr e.1 e.2).mpr heE)⟩
  have hcfun : PEqualNP.MetaComplexity.circuitFun (n + m) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [congrFun hfun z]
    change decide (∃ e ∈ E, z (left e.1) = true ∧ z (right e.2) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (n + m))), z a = true) ||
       decide (∃ u v : Fin (n + m), G.Adj u v ∧ z u = true ∧ z v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨e, he, ha, hb⟩
      exact ⟨left e.1, right e.2, (hlr e.1 e.2).mpr he, ha, hb⟩
    · rintro ⟨u, v, ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨e, he, hu, hv⟩
      · exact ⟨e, he, hv, hu⟩
  have hDeg1G : ∃ u : Fin (n + m), (G.neighborFinset u).card = 1 := by
    obtain ⟨u, hu⟩ := hDeg1
    exact ⟨u, (hdegEq u).trans hu⟩
  have hDeg3G : ∀ u v : Fin (n + m), G.Adj u v → (G.neighborFinset u).card = 1 → 3 ≤ (G.neighborFinset v).card := by
    intro u v huv hu1
    rw [hdegEq v]
    have hu1' : (Finset.filter (inc u) E).card = 1 := (hdegEq u).symm.trans hu1
    have hne : u ≠ v := G.ne_of_adj huv
    have hex : ∃ e ∈ E, inc u e ∧ inc v e := by
      rcases huv with ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨e, he, Or.inl rfl, Or.inr rfl⟩
      · exact ⟨e, he, Or.inr rfl, Or.inl rfl⟩
    exact hDeg3 u v hne hu1' hex
  have hRemG : ∀ v : Fin (n + m), (G.deleteEdges {e : Sym2 (Fin (n + m)) | v ∈ e}).edgeFinset.Nonempty := by
    intro v
    obtain ⟨e, he⟩ := hRem v
    have he' := Finset.mem_filter.mp he
    refine ⟨s(left e.1, right e.2), SimpleGraph.mem_edgeFinset.mpr ?_⟩
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.deleteEdges_adj]
    refine ⟨(hlr e.1 e.2).mpr he'.1, ?_⟩
    simp only [Set.mem_setOf_eq, Sym2.mem_iff, not_or]
    exact ⟨fun h => he'.2 (Or.inl h.symm), fun h => he'.2 (Or.inr h.symm)⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (n + m) G C hGne hAO hcfun
  obtain ⟨v, hvne, C', hC'm, hC'f, hC'sz⟩ := hTopPeel (n + m) G D hno4 hDeg1G hDeg3G hRemG hLeast hTF
  have hvneE : (Finset.filter (inc v) E).Nonempty := by
    rw [← Finset.card_pos, ← hdegEq v]
    exact Finset.card_pos.mpr hvne
  have hC'fE : PEqualNP.MetaComplexity.circuitFun (n + m) C' = fE ({e ∈ E | ¬inc v e}) := by
    funext z
    rw [congrFun hC'f z]
    change (decide (∃ a ∈ (∅ : Finset (Fin (n + m))), z a = true) ||
       decide (∃ u w : Fin (n + m), (G.deleteEdges {e : Sym2 (Fin (n + m)) | v ∈ e}).Adj u w ∧ z u = true ∧ z w = true)) =
      decide (∃ e ∈ {e ∈ E | ¬inc v e}, z (left e.1) = true ∧ z (right e.2) = true)
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨u, w, huw, hu, hw⟩
      rw [SimpleGraph.deleteEdges_adj] at huw
      rcases huw with ⟨⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hnot⟩
      · have hni : ¬inc v e := by
          intro hinc
          apply hnot
          simp only [Set.mem_setOf_eq, Sym2.mem_iff]
          exact hinc.imp Eq.symm Eq.symm
        exact ⟨e, Finset.mem_filter.mpr ⟨he, hni⟩, hu, hw⟩
      · have hni : ¬inc v e := by
          intro hinc
          apply hnot
          simp only [Set.mem_setOf_eq, Sym2.mem_iff]
          rcases hinc with h1 | h2
          · exact Or.inr h1.symm
          · exact Or.inl h2.symm
        exact ⟨e, Finset.mem_filter.mpr ⟨he, hni⟩, hw, hu⟩
    · rintro ⟨e, he, ha, hb⟩
      have he' := Finset.mem_filter.mp he
      refine ⟨left e.1, right e.2, ?_, ha, hb⟩
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨(hlr e.1 e.2).mpr he'.1, ?_⟩
      simp only [Set.mem_setOf_eq, Sym2.mem_iff, not_or]
      exact ⟨fun h => he'.2 (Or.inl h.symm), fun h => he'.2 (Or.inr h.symm)⟩
  refine ⟨v, hvneE, C', hC'm, hC'fE, ?_⟩
  have hd := hdegEq v
  omega
