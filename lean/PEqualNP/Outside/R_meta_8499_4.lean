import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8499_4
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hDeleteTopForm :
      ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1))
        (G : SimpleGraph (Fin (x1 + x1))) [DecidableRel G.Adj]
        (D : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1),
        have dN : Finset (Fin x1) := {v : Fin x1 | v ≠ x6 ∧ (v, x6) ∈ x2};
        have dE : Finset (Fin x1 × Fin x1) := {e ∈ x2 | e.1 ≠ x6 ∧ e.2 ≠ x6};
        (∀ a b : Fin x1, x3 a ≠ x4 b) →
        (∀ u v : Fin (x1 + x1), G.Adj u v ↔ ∃ a b : Fin x1, (a, b) ∈ x2 ∧ ((u = x3 a ∧ v = x4 b) ∨ (u = x4 b ∧ v = x3 a))) →
        (∀ a b : Fin x1, (a, b) ∈ x2 → (a, a) ∈ x2 ∧ (b, b) ∈ x2) →
        PEqualNP.TopForm.NoFourCycle G →
        (x6, x6) ∈ x2 →
        (∃ a b : Fin x1, a ≠ b ∧ (a, a) ∈ dE ∧ (b, b) ∈ dE) →
        (∀ b : Fin x1, (x6, b) ∈ x2 → b = x6) →
        (∀ a ∈ dN, ∀ b ∈ dN, (a, b) ∈ x2 ↔ a = b) →
        (∀ a ∈ dN, ∀ b ∈ dN, a ≠ b → ∀ c : Fin x1, c ≠ x6 → ¬((a, c) ∈ x2 ∧ (b, c) ∈ x2)) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (x1 + x1) E ∧
          (∀ v : Fin (x1 + x1) → Bool,
            PEqualNP.MetaComplexity.circuitFun (x1 + x1) E v =
              Decidable.decide (∃ a b : Fin x1, (a, b) ∈ dE ∧ v (x3 a) = Bool.true ∧ v (x4 b) = Bool.true)) ∧
          E.size + dN.card + (2 : ℕ) ≤ D.size) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 x4 : Fin x1 ↪ Fin (x1 + x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin x1) (x7 : Bool),   have x8 : Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x8 : Finset (Fin x1 × Fin x1)) (x9 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x8 ∧ x10 (x3 x11) = Bool.true ∧ x10 (x4 x12) = Bool.true);   let x9 : Fin x1 → Fin x1 → Prop := fun (x9 x10 : Fin x1) => if x7 = Bool.true then (x10, x9) ∈ x2 else (x9, x10) ∈ x2;   have x10 : Finset (Fin x1) := {x10 : Fin x1 | x10 ≠ x6 ∧ x9 x10 x6};   have x11 : Finset (Fin x1 × Fin x1) := {x11 ∈ x2 | x11.1 ≠ x6 ∧ x11.2 ≠ x6};   (∀ (x12 x13 : Fin x1), x3 x12 ≠ x4 x13) → (∀ (x13 x14 : Fin x1), (x13, x14) ∈ x2 → (x13, x13) ∈ x2 ∧ (x14, x14) ∈ x2) → (∀ (x14 x15 x16 x17 : Fin x1), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x2 ∧ (x14, x17) ∈ x2 ∧ (x15, x16) ∈ x2 ∧ (x15, x17) ∈ x2)) → (x6, x6) ∈ x2 → (∃ (x16 : Fin x1) (x17 : Fin x1), x16 ≠ x17 ∧ (x16, x16) ∈ x11 ∧ (x17, x17) ∈ x11) → (∀ (x17 : Fin x1), x9 x6 x17 → x17 = x6) → (∀ x18 ∈ x10, ∀ x20 ∈ x10, x9 x18 x20 ↔ x18 = x20) → (∀ x19 ∈ x10, ∀ x21 ∈ x10, x19 ≠ x21 → ∀ (x24 : Fin x1), x24 ≠ x6 → ¬(x9 x19 x24 ∧ x9 x21 x24)) → PEqualNP.TopForm.IsAO2 (x1 + x1) x5 → x8 x2 x5 → ∃ (x22 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x1) x22 ∧ x8 x11 x22 ∧ x22.size + x10.card + (2 : ℕ) ≤ x5.size := by
  classical
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 hDisj hDiag hC4 h6 hTwo hDeg1 hInd hDisjN hAO hFun
  by_cases hx7 : x7 = Bool.true
  · have hx9 : ∀ a b : Fin x1, x9 a b ↔ (b, a) ∈ x2 := fun a b => by
      change (if x7 = Bool.true then (b, a) ∈ x2 else (a, b) ∈ x2) ↔ (b, a) ∈ x2
      simp only [hx7, ↓reduceIte]
    let x2' : Finset (Fin x1 × Fin x1) := x2.image Prod.swap
    have hmem : ∀ a b : Fin x1, (a, b) ∈ x2' ↔ (b, a) ∈ x2 := by
      intro a b
      constructor
      · intro h
        obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp h
        have h1 : p.2 = a := congrArg Prod.fst heq
        have h2 : p.1 = b := congrArg Prod.snd heq
        rw [← h2, ← h1]
        exact hp
      · intro h
        exact Finset.mem_image.mpr ⟨(b, a), h, rfl⟩
    have hDisj' : ∀ a b : Fin x1, x4 a ≠ x3 b := fun a b h => hDisj b a h.symm
    have hDiag' : ∀ a b : Fin x1, (a, b) ∈ x2' → (a, a) ∈ x2' ∧ (b, b) ∈ x2' := by
      intro a b h
      have hb := hDiag b a ((hmem a b).mp h)
      exact ⟨(hmem a a).mpr hb.2, (hmem b b).mpr hb.1⟩
    have hC4' : ∀ a b c d : Fin x1, a ≠ b → c ≠ d → ¬((a, c) ∈ x2' ∧ (a, d) ∈ x2' ∧ (b, c) ∈ x2' ∧ (b, d) ∈ x2') := by
      intro a b c d hab hcd h
      exact hC4 c d a b hcd hab ⟨(hmem a c).mp h.1, (hmem b c).mp h.2.2.1, (hmem a d).mp h.2.1, (hmem b d).mp h.2.2.2⟩
    let adj' : Fin (x1 + x1) → Fin (x1 + x1) → Prop := fun u v =>
      ∃ a b : Fin x1, (a, b) ∈ x2' ∧ ((u = x4 a ∧ v = x3 b) ∨ (u = x3 b ∧ v = x4 a))
    let G' : SimpleGraph (Fin (x1 + x1)) :=
      { Adj := adj'
        symm := ⟨by
          rintro u v ⟨a, b, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact ⟨a, b, h, Or.inr ⟨rfl, rfl⟩⟩
          · exact ⟨a, b, h, Or.inl ⟨rfl, rfl⟩⟩⟩
        loopless := ⟨by
          rintro u ⟨a, b, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · exact hDisj' a b (h1.symm.trans h2)
          · exact hDisj' a b (h2.symm.trans h1)⟩ }
    have hG'adj : ∀ u v : Fin (x1 + x1), G'.Adj u v ↔ ∃ a b : Fin x1, (a, b) ∈ x2' ∧ ((u = x4 a ∧ v = x3 b) ∨ (u = x3 b ∧ v = x4 a)) :=
      fun _ _ => Iff.rfl
    have hlr' : ∀ a b : Fin x1, G'.Adj (x4 a) (x3 b) ↔ (a, b) ∈ x2' := by
      intro a b
      constructor
      · rintro ⟨a', b', h, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
        · rw [x4.injective h1, x3.injective h2]; exact h
        · exact False.elim (hDisj' a b' h1)
      · intro h
        exact ⟨a, b, h, Or.inl ⟨rfl, rfl⟩⟩
    have hC4G' : PEqualNP.TopForm.NoFourCycle G' := by
      intro u v huv
      apply Finset.card_le_one.mpr
      intro x hx y hy
      have hx' := (Finset.mem_filter.mp hx).2
      have hy' := (Finset.mem_filter.mp hy).2
      rcases hx'.1 with ⟨a1, b1, h1, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · rcases hx'.2 with ⟨a2, b2, h2, ⟨rfl, hxb2⟩ | ⟨_, hxa2⟩⟩
        · have hb : b1 = b2 := x3.injective hxb2
          subst hb
          rcases hy'.1 with ⟨a3, b3, h3, ⟨ha3, rfl⟩ | ⟨hb3, _⟩⟩
          · have ha : a1 = a3 := x4.injective ha3
            subst ha
            rcases hy'.2 with ⟨a4, b4, h4, ⟨ha4, hb4⟩ | ⟨hb4, _⟩⟩
            · have ha' : a2 = a4 := x4.injective ha4
              have hb' : b3 = b4 := x3.injective hb4
              subst ha'; subst hb'
              by_contra hxy
              exact hC4' a1 a2 b1 b3
                (fun h => huv (congrArg x4 h))
                (fun h => hxy (congrArg x3 h))
                ⟨h1, h3, h2, h4⟩
            · exact False.elim (hDisj' a2 b4 hb4)
          · exact False.elim (hDisj' a1 b3 hb3)
        · exact False.elim (hDisj' a2 b1 hxa2.symm)
      · rcases hx'.2 with ⟨a2, b2, h2, ⟨_, hxa2⟩ | ⟨rfl, hxa2⟩⟩
        · exact False.elim (hDisj' a1 b2 hxa2)
        · have ha : a1 = a2 := x4.injective hxa2
          subst ha
          rcases hy'.1 with ⟨a3, b3, h3, ⟨ha3, _⟩ | ⟨hb3, rfl⟩⟩
          · exact False.elim (hDisj' a3 b1 ha3.symm)
          · have hb : b1 = b3 := x3.injective hb3
            subst hb
            rcases hy'.2 with ⟨a4, b4, h4, ⟨ha4, _⟩ | ⟨hb4, ha4⟩⟩
            · exact False.elim (hDisj' a4 b2 ha4.symm)
            · have hb' : b2 = b4 := x3.injective hb4
              have ha' : a3 = a4 := x4.injective ha4
              subst hb'; subst ha'
              by_contra hxy
              exact hC4' a1 a3 b1 b2
                (fun h => hxy (congrArg x4 h))
                (fun h => huv (congrArg x3 h))
                ⟨h1, h2, h3, h4⟩
    have h6' : (x6, x6) ∈ x2' := (hmem x6 x6).mpr h6
    have hGne' : G'.edgeFinset.Nonempty := ⟨s(x4 x6, x3 x6), SimpleGraph.mem_edgeFinset.mpr ((hlr' x6 x6).mpr h6')⟩
    have hcfun' : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 =
        PEqualNP.MetaComplexity.NestedCover.graphFun G' ∅ := by
      funext z
      rw [hFun z]
      change decide (∃ a b : Fin x1, (a, b) ∈ x2 ∧ z (x3 a) = true ∧ z (x4 b) = true) =
        (decide (∃ a ∈ (∅ : Finset (Fin (x1 + x1))), z a = true) ||
         decide (∃ u v : Fin (x1 + x1), G'.Adj u v ∧ z u = true ∧ z v = true))
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
      rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨a, b, h, ha, hb⟩
        exact ⟨x4 b, x3 a, (hlr' b a).mpr ((hmem b a).mpr h), hb, ha⟩
      · rintro ⟨u, v, ⟨a, b, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
        · exact ⟨b, a, (hmem a b).mp h, hv, hu⟩
        · exact ⟨b, a, (hmem a b).mp h, hu, hv⟩
    have h10eq : ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)) = x10 := by
      ext y
      constructor
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hx9 y x6).mpr ((hmem y x6).mp h1.2)⟩
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hmem y x6).mpr ((hx9 y x6).mp h1.2)⟩
    have hTwo' : ∃ a b : Fin x1, a ≠ b ∧ (a, a) ∈ ({e ∈ x2' | e.1 ≠ x6 ∧ e.2 ≠ x6} : Finset (Fin x1 × Fin x1)) ∧ (b, b) ∈ ({e ∈ x2' | e.1 ≠ x6 ∧ e.2 ≠ x6} : Finset (Fin x1 × Fin x1)) := by
      obtain ⟨a, b, hab, ha, hb⟩ := hTwo
      have ha' := Finset.mem_filter.mp ha
      have hb' := Finset.mem_filter.mp hb
      exact ⟨a, b, hab, Finset.mem_filter.mpr ⟨(hmem a a).mpr ha'.1, ha'.2⟩, Finset.mem_filter.mpr ⟨(hmem b b).mpr hb'.1, hb'.2⟩⟩
    have hDeg1' : ∀ y : Fin x1, (x6, y) ∈ x2' → y = x6 := fun y hy => hDeg1 y ((hx9 x6 y).mpr ((hmem x6 y).mp hy))
    have hInd' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), (a, b) ∈ x2' ↔ a = b := by
      intro a ha b hb
      rw [h10eq] at ha hb
      exact (hmem a b).trans ((hx9 a b).symm.trans (hInd a ha b hb))
    have hDisjN' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)), a ≠ b → ∀ z : Fin x1, z ≠ x6 → ¬((a, z) ∈ x2' ∧ (b, z) ∈ x2') := by
      intro a ha b hb hab z hz hpair
      rw [h10eq] at ha hb
      exact hDisjN a ha b hb hab z hz ⟨(hx9 a z).mpr ((hmem a z).mp hpair.1), (hx9 b z).mpr ((hmem b z).mp hpair.2)⟩
    obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (x1 + x1) G' x5 hGne' hAO hcfun'
    obtain ⟨E, hEAO, hEFun', hESz⟩ := hDeleteTopForm x1 x2' x4 x3 G' D x6 hDisj' hG'adj hDiag' hC4G' h6' hTwo' hDeg1' hInd' hDisjN' hLeast hTF
    refine ⟨E, hEAO, ?_, ?_⟩
    · intro v
      rw [hEFun' v, decide_eq_decide]
      constructor
      · rintro ⟨a, b, hab, ha, hb⟩
        obtain ⟨hab1, hab2⟩ := Finset.mem_filter.mp hab
        exact ⟨b, a, Finset.mem_filter.mpr ⟨(hmem a b).mp hab1, hab2.2, hab2.1⟩, hb, ha⟩
      · rintro ⟨a, b, hab, ha, hb⟩
        obtain ⟨hab1, hab2⟩ := Finset.mem_filter.mp hab
        exact ⟨b, a, Finset.mem_filter.mpr ⟨(hmem b a).mpr hab1, hab2.2, hab2.1⟩, hb, ha⟩
    · change E.size + ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2'} : Finset (Fin x1)).card + (2 : ℕ) ≤ D.size at hESz
      rw [h10eq] at hESz
      omega
  · have hx9 : ∀ a b : Fin x1, x9 a b ↔ (a, b) ∈ x2 := fun a b => by
      change (if x7 = Bool.true then (b, a) ∈ x2 else (a, b) ∈ x2) ↔ (a, b) ∈ x2
      simp only [hx7, Bool.false_eq_true, ↓reduceIte]
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
        · rw [x3.injective h1, x4.injective h2]; exact h
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
    have hGne : G.edgeFinset.Nonempty := ⟨s(x3 x6, x4 x6), SimpleGraph.mem_edgeFinset.mpr ((hlr x6 x6).mpr h6)⟩
    have hcfun : PEqualNP.MetaComplexity.circuitFun (x1 + x1) x5 =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
      funext z
      rw [hFun z]
      change decide (∃ a b : Fin x1, (a, b) ∈ x2 ∧ z (x3 a) = true ∧ z (x4 b) = true) =
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
    have h10eq : ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)) = x10 := by
      ext y
      constructor
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hx9 y x6).mpr h1.2⟩
      · intro hy
        have h1 := (Finset.mem_filter.mp hy).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, h1.1, (hx9 y x6).mp h1.2⟩
    have hDeg1' : ∀ y : Fin x1, (x6, y) ∈ x2 → y = x6 := fun y hy => hDeg1 y ((hx9 x6 y).mpr hy)
    have hInd' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), (a, b) ∈ x2 ↔ a = b := by
      intro a ha b hb
      rw [h10eq] at ha hb
      exact (hx9 a b).symm.trans (hInd a ha b hb)
    have hDisjN' : ∀ a ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), ∀ b ∈ ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)), a ≠ b → ∀ z : Fin x1, z ≠ x6 → ¬((a, z) ∈ x2 ∧ (b, z) ∈ x2) := by
      intro a ha b hb hab z hz hpair
      rw [h10eq] at ha hb
      exact hDisjN a ha b hb hab z hz ⟨(hx9 a z).mpr hpair.1, (hx9 b z).mpr hpair.2⟩
    obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (x1 + x1) G x5 hGne hAO hcfun
    obtain ⟨E, hEAO, hEFun, hESz⟩ := hDeleteTopForm x1 x2 x3 x4 G D x6 hDisj hGadj hDiag hC4G h6 hTwo hDeg1' hInd' hDisjN' hLeast hTF
    refine ⟨E, hEAO, hEFun, ?_⟩
    change E.size + ({y : Fin x1 | y ≠ x6 ∧ (y, x6) ∈ x2} : Finset (Fin x1)).card + (2 : ℕ) ≤ D.size at hESz
    rw [h10eq] at hESz
    omega
