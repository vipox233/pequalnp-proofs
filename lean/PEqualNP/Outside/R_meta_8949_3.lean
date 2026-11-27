import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8949_3
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hGraphCoverLB :
      ∀ (n m : ℕ) (G : SimpleGraph (Fin (n + m))) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ a b : Fin n, ¬G.Adj (Fin.castAdd m a) (Fin.castAdd m b)) →
        (∀ a b : Fin m, ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        (∀ c u : Fin (n + m), G.Adj c u → ∃ v w : Fin (n + m), G.Adj c v ∧ G.Adj v w ∧ w ≠ c) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ S : Finset (Fin (n + m)),
          (∀ u v : Fin (n + m), G.Adj u v → u ∈ S ∨ v ∈ S) ∧
          G.edgeFinset.card + S.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : Finset (Fin x1 × Fin x2) → Finset (Fin (x1 + x2)) := fun (x5 : Finset (Fin x1 × Fin x2)) => x5.biUnion fun (x6 : Fin x1 × Fin x2) => {Fin.castAdd x2 x6.1, Fin.natAdd x1 x6.2};   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x4 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x4 x8 = Decidable.decide (∃ x9 ∈ x3, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true)) → (¬∃ (x9 : Finset (Fin x1 × Fin x2)) (x10 : Finset (Fin x1 × Fin x2)) (x11 : Fin (x1 + x2)), x9.Nonempty ∧ x9 ∪ x10 = x3 ∧ Disjoint (x5 x9) (x5 x10) ∧ ∀ x12 ∈ x9, Fin.castAdd x2 x12.1 = x11 ∨ Fin.natAdd x1 x12.2 = x11) → (∃ (x10 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[(1 : ℕ)]? = Option.some x10) → ∃ (x11 : Finset (Fin x1)) (x12 : Finset (Fin x2)), (∀ x13 ∈ x3, x13.1 ∈ x11 ∨ x13.2 ∈ x12) ∧ x3.card + x11.card + x12.card ≤ x4.size + (1 : ℕ) := by
  classical
  intro n m E C verts hc4 hAO hfun hsep _hgate
  by_cases hemp : E = ∅
  · subst hemp
    exact ⟨∅, ∅, by simp, by simp⟩
  have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
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
  let enc : Fin n × Fin m → Sym2 (Fin (n + m)) := fun e => s(left e.1, right e.2)
  have hencInj : Function.Injective enc := by
    intro e1 e2 h
    change s(left e1.1, right e1.2) = s(left e2.1, right e2.2) at h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨hbad, _⟩
    · exact Prod.ext (hleftInj h1) (hrightInj h2)
    · exact False.elim (hsepLR e1.1 e2.2 hbad)
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
    rw [← Finset.card_pos, hedgeCard]
    exact Finset.card_pos.mpr hEne
  have hcfun : PEqualNP.MetaComplexity.circuitFun (n + m) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hfun z]
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
  have hNoStar : ∀ c u : Fin (n + m), G.Adj c u → ∃ v w : Fin (n + m), G.Adj c v ∧ G.Adj v w ∧ w ≠ c := by
    intro c u hcu
    by_contra hno
    have hall : ∀ v w : Fin (n + m), G.Adj c v → G.Adj v w → w = c := by
      intro v w hcv hvw
      by_contra hwc
      exact hno ⟨v, w, hcv, hvw, hwc⟩
    let A : Finset (Fin n × Fin m) := E.filter fun e => left e.1 = c ∨ right e.2 = c
    let B : Finset (Fin n × Fin m) := E.filter fun e => ¬(left e.1 = c ∨ right e.2 = c)
    have hAne : A.Nonempty := by
      rcases hcu with ⟨e, he, ⟨h1, _⟩ | ⟨_, h2⟩⟩
      · exact ⟨e, Finset.mem_filter.mpr ⟨he, Or.inl h1.symm⟩⟩
      · exact ⟨e, Finset.mem_filter.mpr ⟨he, Or.inr h2.symm⟩⟩
    have hAB : A ∪ B = E := by
      ext e
      simp only [A, B, Finset.mem_union, Finset.mem_filter]
      by_cases h : left e.1 = c ∨ right e.2 = c <;> simp [h]
    have hDisj : Disjoint (verts A) (verts B) := by
      rw [Finset.disjoint_left]
      intro z hzA hzB
      rcases Finset.mem_biUnion.mp hzA with ⟨e1, he1, hz1⟩
      rcases Finset.mem_biUnion.mp hzB with ⟨e2, he2, hz2⟩
      have he1' := Finset.mem_filter.mp he1
      have he2' := Finset.mem_filter.mp he2
      have hzc : z ≠ c := by
        intro h
        subst h
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz2
        exact he2'.2 (hz2.imp Eq.symm Eq.symm)
      have hcz : G.Adj c z := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
        rcases he1'.2 with h1 | h2
        · rcases hz1 with rfl | rfl
          · exact False.elim (hzc h1)
          · rw [← h1]; exact (hlr e1.1 e1.2).mpr he1'.1
        · rcases hz1 with rfl | rfl
          · rw [← h2]; exact ((hlr e1.1 e1.2).mpr he1'.1).symm
          · exact False.elim (hzc h2)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz2
      rcases hz2 with rfl | rfl
      · have hwc := hall (left e2.1) (right e2.2) hcz ((hlr e2.1 e2.2).mpr he2'.1)
        exact he2'.2 (Or.inr hwc)
      · have hwc := hall (right e2.2) (left e2.1) hcz ((hlr e2.1 e2.2).mpr he2'.1).symm
        exact he2'.2 (Or.inl hwc)
    exact hsep ⟨A, B, c, hAne, hAB, hDisj, fun e he => (Finset.mem_filter.mp he).2⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (n + m) G C hGne hAO hcfun
  obtain ⟨S, hScov, hScard⟩ := hGraphCoverLB n m G D hll hrr hno4 hGne hNoStar hLeast hTF
  let U : Finset (Fin n) := Finset.univ.filter fun a => left a ∈ S
  let V : Finset (Fin m) := Finset.univ.filter fun b => right b ∈ S
  have hUcov : ∀ e ∈ E, e.1 ∈ U ∨ e.2 ∈ V := by
    intro e he
    rcases hScov (left e.1) (right e.2) ((hlr e.1 e.2).mpr he) with h1 | h2
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
  have hUVeq : U.image left ∪ V.image right = S := by
    ext z
    simp only [U, V, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩) <;> assumption
    · intro hz
      rcases hsplit z with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inl ⟨a, hz, rfl⟩
      · exact Or.inr ⟨b, hz, rfl⟩
  have hUVdisj : Disjoint (U.image left) (V.image right) := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    rcases Finset.mem_image.mp h1 with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨b, _, hab⟩
    exact hsepLR a b hab.symm
  have hUVcard : U.card + V.card = S.card := by
    rw [← Finset.card_image_of_injective U hleftInj,
        ← Finset.card_image_of_injective V hrightInj,
        ← Finset.card_union_of_disjoint hUVdisj, hUVeq]
  refine ⟨U, V, hUcov, ?_⟩
  omega
