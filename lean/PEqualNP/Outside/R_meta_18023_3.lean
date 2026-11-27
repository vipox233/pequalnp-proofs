import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18023_3
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
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ S : Finset (Fin (n + m)),
          (∀ u v : Fin (n + m), G.Adj u v → u ∈ S ∨ v ∈ S) ∧
          G.edgeFinset.card + S.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m R _ C hc4 hAO hfun
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => R e.1 e.2
  have hmemE : ∀ (a : Fin n) (b : Fin m), (a, b) ∈ E ↔ R a b := by
    intro a b
    simp [E]
  by_cases hemp : E = ∅
  · refine ⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_, by simp⟩
    intro a b hab
    have hmem : (a, b) ∈ E := (hmemE a b).mpr hab
    rw [hemp] at hmem
    exact False.elim (Finset.notMem_empty _ hmem)
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
  have hlr : ∀ (a : Fin n) (b : Fin m), G.Adj (left a) (right b) ↔ R a b := by
    intro a b
    constructor
    · rintro ⟨⟨u, v⟩, he, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
      · have ha : a = u := hleftInj h1
        have hb : b = v := hrightInj h2
        subst ha; subst hb
        exact (hmemE a b).mp he
      · exact False.elim (hsepLR u b h1.symm)
    · intro hab
      exact ⟨(a, b), (hmemE a b).mpr hab, Or.inl ⟨rfl, rfl⟩⟩
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
        simpa only [enc, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using
          (hlr e.1 e.2).mpr ((hmemE e.1 e.2).mp he)
  have hedgeCard : G.edgeFinset.card = E.card := by
    rw [hedges, Finset.card_image_of_injective _ hencInj]
  have hGne : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos, hedgeCard]
    exact Finset.card_pos.mpr hEne
  have hcfun : PEqualNP.MetaComplexity.circuitFun (n + m) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hfun z]
    change decide (∃ (a : Fin n) (b : Fin m), R a b ∧ z (left a) = true ∧ z (right b) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (n + m))), z a = true) ||
       decide (∃ u v : Fin (n + m), G.Adj u v ∧ z u = true ∧ z v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨left a, right b, (hlr a b).mpr hab, ha, hb⟩
    · rintro ⟨u, v, ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨e.1, e.2, (hmemE e.1 e.2).mp he, hu, hv⟩
      · exact ⟨e.1, e.2, (hmemE e.1 e.2).mp he, hv, hu⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (n + m) G C hGne hAO hcfun
  obtain ⟨S, hScov, hScard⟩ := hGraphCoverLB n m G D hll hrr hno4 hGne hLeast hTF
  let U : Finset (Fin n) := Finset.univ.filter fun a => left a ∈ S
  let V : Finset (Fin m) := Finset.univ.filter fun b => right b ∈ S
  have hUcov : ∀ (a : Fin n) (b : Fin m), R a b → a ∈ U ∨ b ∈ V := by
    intro a b hab
    rcases hScov (left a) (right b) ((hlr a b).mpr hab) with h1 | h2
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
  let starB : Fin n → Finset (Fin m) := fun a => Finset.univ.filter fun b => R a b
  let starA : Fin m → Finset (Fin n) := fun b => Finset.univ.filter fun a => R a b ∧ a ∉ U
  let U' : Finset (Fin n) := U.filter fun a => (starB a).Nonempty
  let V' : Finset (Fin m) := V.filter fun b => (starA b).Nonempty
  let eU : Fin U'.card ≃ {a : Fin n // a ∈ U'} := (Fintype.equivFinOfCardEq (Fintype.card_coe U')).symm
  let eV : Fin V'.card ≃ {b : Fin m // b ∈ V'} := (Fintype.equivFinOfCardEq (Fintype.card_coe V')).symm
  let A : Fin (U'.card + V'.card) → Finset (Fin n) :=
    Fin.addCases (fun i => {(eU i).1}) (fun j => starA (eV j).1)
  let B : Fin (U'.card + V'.card) → Finset (Fin m) :=
    Fin.addCases (fun i => starB (eU i).1) (fun j => {(eV j).1})
  refine ⟨U'.card + V'.card, A, B, ?_, ?_, ?_, ?_⟩
  · intro idx
    refine Fin.addCases ?_ ?_ idx
    · intro i
      simp only [A, B, Fin.addCases_left]
      exact ⟨Finset.singleton_nonempty _, (Finset.mem_filter.mp (eU i).2).2⟩
    · intro j
      simp only [A, B, Fin.addCases_right]
      exact ⟨(Finset.mem_filter.mp (eV j).2).2, Finset.singleton_nonempty _⟩
  · intro idx
    refine Fin.addCases ?_ ?_ idx
    · intro i a ha b hb
      simp only [A, B, Fin.addCases_left, Finset.mem_singleton] at ha hb
      subst ha
      exact (Finset.mem_filter.mp hb).2
    · intro j a ha b hb
      simp only [A, B, Fin.addCases_right, Finset.mem_singleton] at ha hb
      subst hb
      exact (Finset.mem_filter.mp ha).2.1
  · intro a b hab
    by_cases haU : a ∈ U
    · have hbStar : b ∈ starB a := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩
      have haU' : a ∈ U' := Finset.mem_filter.mpr ⟨haU, ⟨b, hbStar⟩⟩
      refine ⟨Fin.castAdd V'.card (eU.symm ⟨a, haU'⟩), ?_, ?_⟩
      · simp only [A, Fin.addCases_left, Equiv.apply_symm_apply, Finset.mem_singleton]
      · simp only [B, Fin.addCases_left, Equiv.apply_symm_apply]
        exact hbStar
    · have hbV : b ∈ V := (hUcov a b hab).resolve_left haU
      have haStar : a ∈ starA b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, haU⟩
      have hbV' : b ∈ V' := Finset.mem_filter.mpr ⟨hbV, ⟨a, haStar⟩⟩
      refine ⟨Fin.natAdd U'.card (eV.symm ⟨b, hbV'⟩), ?_, ?_⟩
      · simp only [A, Fin.addCases_right, Equiv.apply_symm_apply]
        exact haStar
      · simp only [B, Fin.addCases_right, Equiv.apply_symm_apply, Finset.mem_singleton]
  · have hsumSplit :
        ∑ idx : Fin (U'.card + V'.card), ((A idx).card + (B idx).card) =
          (∑ i : Fin U'.card, ((A (Fin.castAdd V'.card i)).card + (B (Fin.castAdd V'.card i)).card)) +
          (∑ j : Fin V'.card, ((A (Fin.natAdd U'.card j)).card + (B (Fin.natAdd U'.card j)).card)) :=
      Fin.sum_univ_add _
    have hsumL :
        (∑ i : Fin U'.card, ((A (Fin.castAdd V'.card i)).card + (B (Fin.castAdd V'.card i)).card)) =
          U'.card + ∑ a ∈ U', (starB a).card := by
      have h1 :
          (∑ i : Fin U'.card, ((A (Fin.castAdd V'.card i)).card + (B (Fin.castAdd V'.card i)).card)) =
            ∑ i : Fin U'.card, (1 + (starB (eU i).1).card) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [A, B, Fin.addCases_left, Finset.card_singleton]
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      congr 1
      rw [Equiv.sum_comp eU (fun x : {a : Fin n // a ∈ U'} => (starB x.1).card)]
      exact Finset.sum_coe_sort U' (fun a => (starB a).card)
    have hsumR :
        (∑ j : Fin V'.card, ((A (Fin.natAdd U'.card j)).card + (B (Fin.natAdd U'.card j)).card)) =
          (∑ b ∈ V', (starA b).card) + V'.card := by
      have h1 :
          (∑ j : Fin V'.card, ((A (Fin.natAdd U'.card j)).card + (B (Fin.natAdd U'.card j)).card)) =
            ∑ j : Fin V'.card, ((starA (eV j).1).card + 1) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [A, B, Fin.addCases_right, Finset.card_singleton]
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      congr 1
      rw [Equiv.sum_comp eV (fun x : {b : Fin m // b ∈ V'} => (starA x.1).card)]
      exact Finset.sum_coe_sort V' (fun b => (starA b).card)
    let E1 : Finset (Fin n × Fin m) := E.filter fun e => e.1 ∈ U
    let E2 : Finset (Fin n × Fin m) := E.filter fun e => e.1 ∉ U
    have hE12card : E1.card + E2.card = E.card := by
      have hdisj : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro e h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : E1 ∪ E2 = E := by
        ext e
        simp only [E1, E2, Finset.mem_union, Finset.mem_filter]
        by_cases h : e.1 ∈ U <;> simp [h]
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hE1eq : E1 = U.biUnion (fun a => (starB a).image (fun b => (a, b))) := by
      ext ⟨a, b⟩
      simp only [E1, E, starB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨hab, haU⟩
        exact ⟨a, haU, b, hab, rfl⟩
      · rintro ⟨a', ha', b', hab', hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨hab', ha'⟩
    have hE1card : ∑ a ∈ U, (starB a).card = E1.card := by
      rw [hE1eq, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun a _ => ?_
        exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm
      · intro a1 _ a2 _ hne
        exact Finset.disjoint_left.mpr fun p hp1 hp2 => by
          rcases Finset.mem_image.mp hp1 with ⟨b1, _, rfl⟩
          rcases Finset.mem_image.mp hp2 with ⟨b2, _, hpair⟩
          exact hne (Prod.mk.inj hpair).1.symm
    have hE2eq : E2 = V.biUnion (fun b => (starA b).image (fun a => (a, b))) := by
      ext ⟨a, b⟩
      simp only [E2, E, starA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨hab, haU⟩
        exact ⟨b, (hUcov a b hab).resolve_left haU, a, ⟨hab, haU⟩, rfl⟩
      · rintro ⟨b', _, a', ⟨hab', haU'⟩, hpair⟩
        rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
        exact ⟨hab', haU'⟩
    have hE2card : ∑ b ∈ V, (starA b).card = E2.card := by
      rw [hE2eq, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun b _ => ?_
        exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)).symm
      · intro b1 _ b2 _ hne
        exact Finset.disjoint_left.mpr fun p hp1 hp2 => by
          rcases Finset.mem_image.mp hp1 with ⟨a1, _, rfl⟩
          rcases Finset.mem_image.mp hp2 with ⟨a2, _, hpair⟩
          exact hne (Prod.mk.inj hpair).2.symm
    have hsumBle : ∑ a ∈ U', (starB a).card ≤ E1.card := by
      rw [← hE1card]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ U)
    have hsumAle : ∑ b ∈ V', (starA b).card ≤ E2.card := by
      rw [← hE2card]
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ V)
    have hU'le : U'.card ≤ U.card := Finset.card_filter_le U _
    have hV'le : V'.card ≤ V.card := Finset.card_filter_le V _
    rw [hsumSplit, hsumL, hsumR]
    omega
