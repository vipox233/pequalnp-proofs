import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53187

theorem main (m d a r : ℕ) (b : Fin r → ℕ) (X : Fin m → Finset (Fin d))
  (Y : Fin m → Finset (Fin a)) (D U : (l : Fin r) → Finset (Finset (Fin (b l))))
  (hDU : ∀ l, ∅ ∈ D l ∧ ∅ ∈ U l) :
  (∃ (E : (l : Fin r) → Finset (Fin d) → ((l : Fin r) → Finset (Fin (b l))) → Finset (Fin (b l)))
      (F : Finset (Fin d) → ((l : Fin r) → Finset (Fin (b l))) → Finset (Fin a)),
    (∀ l x y v w, x ⊆ y → (∀ j, j < l → v j ⊆ w j) → E l x v ⊆ E l y w) ∧
    (∀ x y v w, x ⊆ y → (∀ j, v j ⊆ w j) → F x v ⊆ F y w) ∧
    ∀ i (v : (l : Fin r) → Finset (Fin (b l))), (∀ l, (∃ L ∈ D l, (Finset.univ \ E l (X i) v) \ v l ⊆ L) ∧
      (∃ R ∈ U l, v l \ (Finset.univ \ E l (X i) v) ⊆ R)) → F (X i) v = Y i) ↔
  ∃ (k : Fin r → ℕ) (B : (l : Fin r) → Fin (k l) → Finset (Fin (b l))),
    (∀ l i j, i ≠ j → Disjoint (B l i) (B l j)) ∧
    (∀ l i, ∀ L ∈ D l, ∀ R ∈ U l, ¬ B l i ⊆ L ∪ R) ∧
    ¬ ∃ lo hi : Fin ((Finset.univ : Finset (Fin r)).prod (fun l => k l + 1)) → Fin m,
      (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧
      (∀ t u, t < u → X (hi t) ⊆ X (lo u)) := by
  constructor
  · rintro ⟨E, F, mE, mF, hrun⟩
    let Has : (l : Fin r) → ℕ → Prop := fun l K => ∃ B : Fin K → Finset (Fin (b l)),
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧ (∀ i, ∀ L ∈ D l, ∀ R ∈ U l, ¬ B i ⊆ L ∪ R)
    have bound : ∀ l K, Has l K → K ≤ b l := by
      rintro l K ⟨B, hd, he⟩
      have ne : ∀ i, ∃ e, e ∈ B i := by
        intro i
        have := he i ∅ (hDU l).1 ∅ (hDU l).2
        obtain ⟨e, he', -⟩ := Finset.not_subset.1 this
        exact ⟨e, he'⟩
      choose e he' using ne
      have inj : Function.Injective e := by
        intro i j h
        by_contra hne
        exact Finset.disjoint_left.1 (hd i j hne) (he' i) (h ▸ he' j)
      simpa using Fintype.card_le_of_injective e inj
    have : ∀ l, DecidablePred (Has l) := fun l => Classical.decPred _
    have has0 : ∀ l, Has l 0 := fun l => ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
    let k : Fin r → ℕ := fun l => Nat.findGreatest (Has l) (b l)
    have hk : ∀ l, Has l (k l) := fun l => Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (has0 l)
    have kmax : ∀ l K, Has l K → K ≤ k l := fun l K h => Nat.le_findGreatest (bound l K h) h
    choose B hBd hBe using hk
    refine ⟨k, B, hBd, hBe, ?_⟩
    rintro ⟨lo, hi, hc, hord⟩
    let N := (Finset.univ : Finset (Fin r)).prod (fun l => k l + 1)
    have hN : N = (Finset.univ : Finset (Fin r)).prod (fun l => k l + 1) := rfl
    let idx : Fin (2 * N) → Fin m := fun p =>
      if p.val % 2 = 0 then lo ⟨p.val / 2, by have := p.isLt; omega⟩ else hi ⟨p.val / 2, by have := p.isLt; omega⟩
    have qmono : ∀ p p' : Fin (2 * N), p ≤ p' → X (idx p) ⊆ X (idx p') := by
      intro p p' hpp
      have h1 := p.isLt
      have h2 := p'.isLt
      have hv : p.val ≤ p'.val := hpp
      rcases Nat.lt_or_ge (p.val / 2) (p'.val / 2) with hlt | hge
      · have mid := hord ⟨p.val / 2, by omega⟩ ⟨p'.val / 2, by omega⟩ hlt
        have a1 : X (idx p) ⊆ X (hi ⟨p.val / 2, by omega⟩) := by
          simp only [idx]
          split_ifs
          · exact (hc _).1
          · exact Finset.Subset.refl _
        have a2 : X (lo ⟨p'.val / 2, by omega⟩) ⊆ X (idx p') := by
          simp only [idx]
          split_ifs
          · exact Finset.Subset.refl _
          · exact (hc _).1
        exact (a1.trans mid).trans a2
      · have e : p.val / 2 = p'.val / 2 := le_antisymm (Nat.div_le_div_right hv) hge
        simp only [idx]
        split_ifs with c1 c2 c2
        · simp only [e]; exact Finset.Subset.refl _
        · simp only [e]; exact (hc _).1
        · exfalso; omega
        · simp only [e]; exact Finset.Subset.refl _
    have indep : ∀ (l : Fin r) x v w, (∀ j, j < l → v j = w j) → E l x v = E l x w := by
      intro l x v w h
      exact Finset.Subset.antisymm (mE l x x v w (Finset.Subset.refl _) (fun j hj => by rw [h j hj]))
        (mE l x x w v (Finset.Subset.refl _) (fun j hj => by rw [h j hj]))
    have stage : ∀ n, n ≤ r → ∃ (σ : Fin (2 * N) → (l : Fin r) → Fin (k l + 1))
        (v : Fin (2 * N) → (l : Fin r) → Finset (Fin (b l))),
        (∀ p p' p'', p ≤ p' → p' ≤ p'' → σ p = σ p'' → σ p' = σ p) ∧
        (∀ p p', σ p = σ p' → ∀ j : Fin r, j.val < n → v p j = v p' j) ∧
        (∀ p, ∀ l : Fin r, l.val < n → (∃ L ∈ D l, (Finset.univ \ E l (X (idx p)) (v p)) \ v p l ⊆ L) ∧
          (∃ R ∈ U l, v p l \ (Finset.univ \ E l (X (idx p)) (v p)) ⊆ R)) ∧
        (∀ p, ∀ j : Fin r, n ≤ j.val → σ p j = 0) := by
      intro n
      induction n with
      | zero =>
        intro _
        exact ⟨fun _ _ => 0, fun _ _ => ∅, fun _ _ _ _ _ _ => rfl, fun _ _ _ j h => absurd h (Nat.not_lt_zero _),
          fun _ l h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
      | succ n ih =>
        intro hn
        obtain ⟨σ, v, conv, same, valid, zero⟩ := ih (by omega)
        let l : Fin r := ⟨n, by omega⟩
        let h : Fin (2 * N) → Finset (Fin (b l)) := fun p => Finset.univ \ E l (X (idx p)) (v p)
        have anti : ∀ p p', p ≤ p' → σ p = σ p' → h p' ⊆ h p := by
          intro p p' hpp hs
          have e : E l (X (idx p')) (v p') = E l (X (idx p')) (v p) :=
            indep l _ _ _ (fun j hj => (same p p' hs j hj).symm)
          have sub : E l (X (idx p)) (v p) ⊆ E l (X (idx p')) (v p') := by
            rw [e]
            exact mE l _ _ _ _ (qmono p p' hpp) (fun j _ => Finset.Subset.refl _)
          exact Finset.sdiff_subset_sdiff (Finset.Subset.refl _) sub
        let Esc : Finset (Fin (b l)) → Prop := fun S => ∀ L ∈ D l, ∀ R ∈ U l, ¬ S ⊆ L ∪ R
        let Below : Fin (2 * N) → ℕ → Prop := fun p K => ∃ s e : Fin K → Fin (2 * N),
          (∀ t, s t ≤ e t ∧ σ (s t) = σ p ∧ σ (e t) = σ p ∧ Esc (h (s t) \ h (e t))) ∧
          (∀ t u, t < u → e t ≤ s u) ∧ (∀ t, e t ≤ p)
        have belowBound : ∀ p K, Below p K → K ≤ k l := by
          rintro p K ⟨s, e, h1, h2, -⟩
          apply kmax
          refine ⟨fun t => h (s t) \ h (e t), ?_, fun t => (h1 t).2.2.2⟩
          have lt : ∀ t u, t < u → Disjoint (h (s t) \ h (e t)) (h (s u) \ h (e u)) := by
            intro t u htu
            rw [Finset.disjoint_left]
            intro x hx hx'
            have : h (s u) ⊆ h (e t) := anti _ _ (h2 t u htu) ((h1 t).2.2.1.trans (h1 u).2.1.symm)
            exact (Finset.mem_sdiff.1 hx).2 (this (Finset.mem_sdiff.1 hx').1)
          intro t u hne
          rcases lt_or_gt_of_ne hne with h' | h'
          · exact lt t u h'
          · exact (lt u t h').symm
        have : ∀ p, DecidablePred (Below p) := fun p => Classical.decPred _
        let c : Fin (2 * N) → ℕ := fun p => Nat.findGreatest (Below p) (k l)
        have below0 : ∀ p, Below p 0 := fun p =>
          ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
        have cspec : ∀ p, Below p (c p) := fun p => Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (below0 p)
        have cle : ∀ p, c p ≤ k l := fun p => Nat.findGreatest_le _
        have cmono : ∀ p p', p ≤ p' → σ p = σ p' → c p ≤ c p' := by
          intro p p' hpp hs
          obtain ⟨s, e, h1, h2, h3⟩ := cspec p
          refine Nat.le_findGreatest (cle p) ⟨s, e, fun t => ?_, h2, fun t => (h3 t).trans hpp⟩
          exact ⟨(h1 t).1, (h1 t).2.1.trans hs, (h1 t).2.2.1.trans hs, (h1 t).2.2.2⟩
        have cstep : ∀ p p', p ≤ p' → σ p = σ p' → Esc (h p \ h p') → c p + 1 ≤ c p' := by
          intro p p' hpp hs hesc
          obtain ⟨s, e, h1, h2, h3⟩ := cspec p
          have ext : Below p' (c p + 1) := by
            refine ⟨Fin.snoc s p, Fin.snoc e p', ?_, ?_, ?_⟩
            · intro t
              refine Fin.lastCases ?_ (fun t => ?_) t
              · simp only [Fin.snoc_last]; exact ⟨hpp, hs, trivial, hesc⟩
              · simp only [Fin.snoc_castSucc]
                exact ⟨(h1 t).1, (h1 t).2.1.trans hs, (h1 t).2.2.1.trans hs, (h1 t).2.2.2⟩
            · intro t u htu
              revert htu
              refine Fin.lastCases ?_ (fun t => ?_) t
              · intro h'; exact absurd h' (not_lt.2 (Fin.le_last u))
              · refine Fin.lastCases ?_ (fun u => ?_) u
                · intro _; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact h3 t
                · intro h'; simp only [Fin.snoc_castSucc]; exact h2 t u (by simpa using h')
            · intro t
              refine Fin.lastCases ?_ (fun t => ?_) t
              · simp only [Fin.snoc_last]; exact le_refl p'
              · simp only [Fin.snoc_castSucc]; exact (h3 t).trans hpp
          exact Nat.le_findGreatest (belowBound _ _ ext) ext
        let σ' : Fin (2 * N) → (j : Fin r) → Fin (k j + 1) := fun p =>
          Function.update (σ p) l ⟨c p, Nat.lt_succ_of_le (cle p)⟩
        have split : ∀ p p', σ' p = σ' p' → σ p = σ p' ∧ c p = c p' := by
          intro p p' he
          constructor
          · funext j
            by_cases hj : j = l
            · subst hj
              rw [zero p l (le_refl n), zero p' l (le_refl n)]
            · have := congrFun he j
              simpa only [σ', Function.update_of_ne hj] using this
          · have := congrFun he l
            simp only [σ', Function.update_self] at this
            exact congrArg Fin.val this
        have join : ∀ p p', σ p = σ p' → c p = c p' → σ' p = σ' p' := by
          intro p p' h1 h2
          simp only [σ', h1, h2]
        have word : ∀ lab : (j : Fin r) → Fin (k j + 1), ∃ z : Finset (Fin (b l)), ∀ p, σ' p = lab →
            (∃ L ∈ D l, h p \ z ⊆ L) ∧ (∃ R ∈ U l, z \ h p ⊆ R) := by
          intro lab
          by_cases hne : (Finset.univ.filter (fun p => σ' p = lab)).Nonempty
          · set S := Finset.univ.filter (fun p => σ' p = lab) with hS
            have hs0 : σ' (S.min' hne) = lab := (Finset.mem_filter.1 (S.min'_mem hne)).2
            have he0 : σ' (S.max' hne) = lab := (Finset.mem_filter.1 (S.max'_mem hne)).2
            have se := split _ _ (hs0.trans he0.symm)
            have le_se : S.min' hne ≤ S.max' hne := S.min'_le _ (S.max'_mem hne)
            have notEsc : ¬ Esc (h (S.min' hne) \ h (S.max' hne)) := by
              intro hesc
              have := cstep _ _ le_se se.1 hesc
              omega
            simp only [Esc, not_forall, not_not] at notEsc
            obtain ⟨L, hL, R, hR, hsub⟩ := notEsc
            refine ⟨h (S.max' hne) ∪ ((h (S.min' hne) \ h (S.max' hne)) \ L), fun p hp => ?_⟩
            have pS : p ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
            have sp := split _ _ (hs0.trans hp.symm)
            have pe := split _ _ (hp.trans he0.symm)
            have a1 : h p ⊆ h (S.min' hne) := anti _ _ (S.min'_le _ pS) sp.1
            have a2 : h (S.max' hne) ⊆ h p := anti _ _ (S.le_max' _ pS) pe.1
            refine ⟨⟨L, hL, fun x hx => ?_⟩, ⟨R, hR, fun x hx => ?_⟩⟩
            · obtain ⟨hxp, hxz⟩ := Finset.mem_sdiff.1 hx
              by_contra hxL
              apply hxz
              by_cases hxe : x ∈ h (S.max' hne)
              · exact Finset.mem_union_left _ hxe
              · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_sdiff.2 ⟨a1 hxp, hxe⟩, hxL⟩)
            · obtain ⟨hxz, hxp⟩ := Finset.mem_sdiff.1 hx
              rcases Finset.mem_union.1 hxz with h' | h'
              · exact absurd (a2 h') hxp
              · obtain ⟨hd, hnl⟩ := Finset.mem_sdiff.1 h'
                rcases Finset.mem_union.1 (hsub hd) with h'' | h''
                · exact absurd h'' hnl
                · exact h''
          · exact ⟨∅, fun p hp => absurd ⟨p, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩⟩ hne⟩
        choose Z hZ using word
        let v' : Fin (2 * N) → (j : Fin r) → Finset (Fin (b j)) := fun p => Function.update (v p) l (Z (σ' p))
        have vlow : ∀ p (j : Fin r), j ≠ l → v' p j = v p j := fun p j hj => Function.update_of_ne hj _ _
        have Esame : ∀ p (j : Fin r), j.val ≤ n → E j (X (idx p)) (v' p) = E j (X (idx p)) (v p) := by
          intro p j hj
          apply indep
          intro i hi
          apply vlow
          intro e
          have h1 : i.val < j.val := hi
          have h2 : i.val = n := congrArg Fin.val e
          omega
        refine ⟨σ', v', ?_, ?_, ?_, ?_⟩
        · intro p p' p'' h1 h2 he
          obtain ⟨e1, e2⟩ := split _ _ he
          have s1 := conv p p' p'' h1 h2 e1
          have c1 := cmono p p' h1 s1.symm
          have c2 := cmono p' p'' h2 (s1.trans e1)
          exact join _ _ s1 (by omega)
        · intro p p' he j hj
          obtain ⟨e1, -⟩ := split _ _ he
          by_cases hjl : j = l
          · subst hjl
            simp only [v', Function.update_self, he]
          · rw [vlow p j hjl, vlow p' j hjl]
            have : j.val ≠ n := fun e => hjl (Fin.ext e)
            exact same p p' e1 j (by omega)
        · intro p j hj
          by_cases hjl : j = l
          · subst hjl
            rw [Esame p l (le_refl n)]
            have := hZ (σ' p) p rfl
            simpa only [v', Function.update_self] using this
          · have : j.val ≠ n := fun e => hjl (Fin.ext e)
            rw [Esame p j (by omega), vlow p j hjl]
            exact valid p j (by omega)
        · intro p j hj
          have : j ≠ l := by
            intro e
            have : j.val = n := congrArg Fin.val e
            omega
          simp only [σ', Function.update_of_ne this]
          exact zero p j (by omega)
    obtain ⟨σ, v, conv, same, valid, -⟩ := stage r (le_refl r)
    have differ : ∀ (t : Fin N) (p p' : Fin (2 * N)), p.val = 2 * t.val → p'.val = 2 * t.val + 1 → σ p ≠ σ p' := by
      intro t p p' h1 h2 he
      have i1 : idx p = lo t := by
        simp only [idx]
        rw [if_pos (by omega)]
        exact congrArg lo (Fin.ext (by show p.val / 2 = t.val; omega))
      have i2 : idx p' = hi t := by
        simp only [idx]
        rw [if_neg (by omega)]
        exact congrArg hi (Fin.ext (by show p'.val / 2 = t.val; omega))
      have vv : v p = v p' := funext fun j => same p p' he j j.isLt
      have r1 := hrun (idx p) (v p) (fun l => valid p l l.isLt)
      have r2 := hrun (idx p') (v p') (fun l => valid p' l l.isLt)
      have := mF (X (idx p)) (X (idx p')) (v p) (v p') (qmono p p' (by show p.val ≤ p'.val; omega))
        (fun j => by rw [vv])
      rw [r1, r2, i1, i2] at this
      exact (hc t).2 this
    have Npos : 0 < N := Finset.prod_pos (fun _ _ => Nat.succ_pos _)
    let pick : Fin (N + 1) → Fin (2 * N) := fun t => ⟨if t.val = 0 then 0 else 2 * t.val - 1, by
      have := t.isLt
      split_ifs <;> omega⟩
    have inj : Function.Injective (fun t => σ (pick t)) := by
      have key : ∀ t u : Fin (N + 1), t < u → σ (pick t) ≠ σ (pick u) := by
        intro t u htu he
        have h1 : t.val < u.val := htu
        have h2 := u.isLt
        let w : Fin N := ⟨u.val - 1, by omega⟩
        let mid : Fin (2 * N) := ⟨2 * (u.val - 1), by omega⟩
        have le1 : pick t ≤ mid := by
          show (if t.val = 0 then 0 else 2 * t.val - 1) ≤ 2 * (u.val - 1)
          split_ifs <;> omega
        have le2 : mid ≤ pick u := by
          show 2 * (u.val - 1) ≤ (if u.val = 0 then 0 else 2 * u.val - 1)
          split_ifs <;> omega
        have m1 := conv (pick t) mid (pick u) le1 le2 he
        refine differ w mid (pick u) rfl ?_ (m1.trans he)
        show (if u.val = 0 then 0 else 2 * u.val - 1) = 2 * (u.val - 1) + 1
        split_ifs <;> omega
      intro t u he
      rcases lt_trichotomy t u with h | h | h
      · exact absurd he (key t u h)
      · exact h
      · exact absurd he.symm (key u t h)
    have card := Fintype.card_le_of_injective _ inj
    rw [Fintype.card_pi] at card
    simp only [Fintype.card_fin] at card
    omega
  · rintro ⟨k, B, hdis, hesc, hno⟩
    let N := (Finset.univ : Finset (Fin r)).prod (fun l => k l + 1)
    have hN : N = (Finset.univ : Finset (Fin r)).prod (fun l => k l + 1) := rfl
    have Npos : 0 < N := Finset.prod_pos (fun _ _ => Nat.succ_pos _)
    let Below : Finset (Fin d) → ℕ → Prop := fun x K =>
      ∃ lo hi : Fin K → Fin m, (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧
        (∀ t u, t < u → X (hi t) ⊆ X (lo u)) ∧ ∀ t, X (hi t) ⊆ x
    have : ∀ x, DecidablePred (Below x) := fun x => Classical.decPred _
    let g : Finset (Fin d) → ℕ := fun x => Nat.findGreatest (Below x) (N - 1)
    have below0 : ∀ x, Below x 0 := fun x =>
      ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
    have gspec : ∀ x, Below x (g x) := fun x => Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (below0 x)
    have gle : ∀ x, g x ≤ N - 1 := fun x => Nat.findGreatest_le _
    have gmono : ∀ x y, x ⊆ y → g x ≤ g y := by
      intro x y h
      obtain ⟨lo, hi, h1, h2, h3⟩ := gspec x
      exact Nat.le_findGreatest (gle x) ⟨lo, hi, h1, h2, fun t => (h3 t).trans h⟩
    have step : ∀ i j, X i ⊆ X j → ¬ Y i ⊆ Y j → g (X i) + 1 ≤ g (X j) := by
      intro i j hX hY
      obtain ⟨lo, hi, h1, h2, h3⟩ := gspec (X i)
      have ext : Below (X j) (g (X i) + 1) := by
        refine ⟨Fin.snoc lo i, Fin.snoc hi j, ?_, ?_, ?_⟩
        · intro t
          refine Fin.lastCases ?_ (fun t => ?_) t
          · simp only [Fin.snoc_last]; exact ⟨hX, hY⟩
          · simp only [Fin.snoc_castSucc]; exact h1 t
        · intro t u htu
          revert htu
          refine Fin.lastCases ?_ (fun t => ?_) t
          · intro h; exact absurd h (not_lt.2 (Fin.le_last u))
          · refine Fin.lastCases ?_ (fun u => ?_) u
            · intro _; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact h3 t
            · intro h; simp only [Fin.snoc_castSucc]; exact h2 t u (by simpa using h)
        · intro t
          refine Fin.lastCases ?_ (fun t => ?_) t
          · simp only [Fin.snoc_last]; exact Finset.Subset.refl _
          · simp only [Fin.snoc_castSucc]; exact (h3 t).trans hX
      have : g (X i) + 1 ≤ N - 1 := by
        by_contra hlt
        have e : g (X i) + 1 = N := by have := gle (X i); omega
        rw [e] at ext
        obtain ⟨lo', hi', h1', h2', -⟩ := ext
        exact hno ⟨lo', hi', h1', h2'⟩
      exact Nat.le_findGreatest this ext
    let W : ℕ → ℕ := fun n => ∏ j ∈ Finset.univ.filter (fun j : Fin r => n ≤ j.val), (k j + 1)
    let Good : (l : Fin r) → Finset (Fin (b l)) → ℕ → Prop := fun l z t =>
      ∀ t' : Fin (k l), t ≤ t'.val → ∃ L ∈ D l, B l t' \ L ⊆ z
    have : ∀ l z, DecidablePred (Good l z) := fun l z => Classical.decPred _
    have goodTop : ∀ l z, ∃ t, Good l z t := fun l z =>
      ⟨k l, fun t' h => absurd t'.isLt (not_lt.2 h)⟩
    let δ : (l : Fin r) → Finset (Fin (b l)) → ℕ := fun l z => Nat.find (goodTop l z)
    have δanti : ∀ l z z', z ⊆ z' → δ l z' ≤ δ l z := by
      intro l z z' h
      refine Nat.find_min' _ (fun t' ht => ?_)
      obtain ⟨L, hL, hs⟩ := Nat.find_spec (goodTop l z) t' ht
      exact ⟨L, hL, hs.trans h⟩
    let Gp : ℕ → ((l : Fin r) → Finset (Fin (b l))) → ℕ := fun n v =>
      ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val < n), δ j (v j) * W (j.val + 1)
    have Gpanti : ∀ n (v w : (l : Fin r) → Finset (Fin (b l))), (∀ j : Fin r, j.val < n → v j ⊆ w j) → Gp n w ≤ Gp n v := by
      intro n v w h
      refine Finset.sum_le_sum (fun j hj => Nat.mul_le_mul_right _ ?_)
      exact δanti j _ _ (h j (Finset.mem_filter.1 hj).2)
    let dig : (l : Fin r) → Finset (Fin d) → ((l : Fin r) → Finset (Fin (b l))) → ℕ := fun l x v =>
      min (k l) ((g x - Gp l.val v) / W (l.val + 1))
    let H : (l : Fin r) → ℕ → Finset (Fin (b l)) := fun l t =>
      Finset.univ.filter (fun e => ∃ s : Fin (k l), t ≤ s.val ∧ e ∈ B l s)
    refine ⟨fun l x v => Finset.univ \ H l (dig l x v),
      fun x v => Finset.univ.filter (fun a => ∃ i, a ∈ Y i ∧ X i ⊆ x ∧ Gp r v ≤ g (X i)), ?_, ?_, ?_⟩
    · intro l x y v w hxy hvw
      have dm : dig l x v ≤ dig l y w := by
        have h1 := gmono x y hxy
        have h2 := Gpanti l.val v w (fun j hj => hvw j hj)
        exact min_le_min (le_refl _) (Nat.div_le_div_right (by omega))
      refine Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (fun e he => ?_)
      obtain ⟨-, s, hs, hm⟩ := Finset.mem_filter.1 he
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, s, dm.trans hs, hm⟩
    · intro x y v w hxy hvw e he
      obtain ⟨-, i, h1, h2, h3⟩ := Finset.mem_filter.1 he
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, i, h1, h2.trans hxy,
        (Gpanti r v w (fun j _ => hvw j)).trans h3⟩
    · intro n v hv
      have compl : ∀ l : Fin r, Finset.univ \ (Finset.univ \ H l (dig l (X n) v)) = H l (dig l (X n) v) := by
        intro l
        ext e
        simp
      have decode : ∀ l : Fin r, δ l (v l) = dig l (X n) v := by
        intro l
        obtain ⟨⟨L0, hL0, hdown⟩, ⟨R, hR, hup⟩⟩ := hv l
        simp only [compl] at hdown hup
        apply le_antisymm
        · refine Nat.find_min' _ (fun t' ht => ⟨L0, hL0, fun e he => ?_⟩)
          obtain ⟨heB, heL⟩ := Finset.mem_sdiff.1 he
          by_contra hz
          exact heL (hdown (Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, t', ht, heB⟩, hz⟩))
        · by_contra hlt
          have hlt' : δ l (v l) < dig l (X n) v := not_le.1 hlt
          have hk : dig l (X n) v ≤ k l := min_le_left _ _
          let t' : Fin (k l) := ⟨dig l (X n) v - 1, by omega⟩
          obtain ⟨L, hL, hs⟩ := Nat.find_spec (goodTop l (v l)) t' (by show δ l (v l) ≤ dig l (X n) v - 1; omega)
          apply hesc l t' L hL R hR
          intro e he
          by_cases heL : e ∈ L
          · exact Finset.mem_union_left _ heL
          · refine Finset.mem_union_right _ (hup (Finset.mem_sdiff.2 ⟨hs (Finset.mem_sdiff.2 ⟨he, heL⟩), fun hh => ?_⟩))
            obtain ⟨-, s, hs', hm⟩ := Finset.mem_filter.1 hh
            have : s = t' := by
              by_contra hne
              exact Finset.disjoint_left.1 (hdis l _ _ hne) hm he
            rw [this] at hs'
            have : dig l (X n) v ≤ dig l (X n) v - 1 := hs'
            omega
      have Wsplit : ∀ l : Fin r, W l.val = (k l + 1) * W (l.val + 1) := by
        intro l
        have e : Finset.univ.filter (fun j : Fin r => l.val ≤ j.val) =
            insert l (Finset.univ.filter (fun j : Fin r => l.val + 1 ≤ j.val)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        simp only [W]
        rw [e, Finset.prod_insert (by simp)]
      have inv : ∀ i, i ≤ r → Gp i v ≤ g (X n) ∧ g (X n) - Gp i v < W i := by
        intro i
        induction i with
        | zero =>
          intro _
          have e0 : Gp 0 v = 0 := by simp [Gp]
          have w0 : W 0 = N := by simp [W, hN]
          have := gle (X n)
          rw [e0, w0]
          omega
        | succ i ih =>
          intro hi
          obtain ⟨h1, h2⟩ := ih (by omega)
          let l : Fin r := ⟨i, by omega⟩
          have e : Gp (i + 1) v = Gp i v + δ l (v l) * W (i + 1) := by
            have s : Finset.univ.filter (fun j : Fin r => j.val < i + 1) =
                insert l (Finset.univ.filter (fun j : Fin r => j.val < i)) := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, l]
              omega
            simp only [Gp]
            rw [s, Finset.sum_insert (by simp [l]), add_comm]
          have wpos : 0 < W (i + 1) := Finset.prod_pos (fun _ _ => Nat.succ_pos _)
          have ws : W i = (k l + 1) * W (i + 1) := Wsplit l
          have q : (g (X n) - Gp i v) / W (i + 1) < k l + 1 := by
            rw [Nat.div_lt_iff_lt_mul wpos, ← ws]; exact h2
          have dg : δ l (v l) = (g (X n) - Gp i v) / W (i + 1) := by
            rw [decode l]
            exact min_eq_right (Nat.le_of_lt_succ q)
          have dm := Nat.div_add_mod (g (X n) - Gp i v) (W (i + 1))
          have ml := Nat.mod_lt (g (X n) - Gp i v) wpos
          rw [e, dg, Nat.mul_comm]
          omega
      have total : Gp r v = g (X n) := by
        have := inv r (le_refl r)
        have wr : W r = 1 := by
          have : Finset.univ.filter (fun j : Fin r => r ≤ j.val) = ∅ := by
            ext j
            simp
          simp only [W, this, Finset.prod_empty]
        rw [wr] at this
        omega
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, h1, h2, h3⟩
        by_contra hn
        have := step i n h2 (fun s => hn (s h1))
        omega
      · intro h
        exact ⟨n, h, Finset.Subset.refl _, total.le⟩

end PEqualNP.Outside.L_meta_53187

theorem PEqualNP.Outside.L_meta_53187 : ∀ (m d a r : Nat) (b : Fin r → Nat) (X : Fin m → Finset (Fin d))
  (Y : Fin m → Finset (Fin a)) (D U : (l : Fin r) → Finset (Finset (Fin (b l)))),
  (∀ l, ∅ ∈ D l ∧ ∅ ∈ U l) →
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  let T := (l : Fin r) → Finset (Fin (b l))
  (∃ (E : (l : Fin r) → Finset (Fin d) → T → Finset (Fin (b l)))
      (F : Finset (Fin d) → T → Finset (Fin a)),
    (∀ l x y v w, x ⊆ y → (∀ j, j < l → v j ⊆ w j) → E l x v ⊆ E l y w) ∧
    (∀ x y v w, x ⊆ y → (∀ j, v j ⊆ w j) → F x v ⊆ F y w) ∧
    ∀ i v, (∀ l, let H := Finset.univ \ E l (X i) v
      (∃ L ∈ D l, H \ v l ⊆ L) ∧ (∃ R ∈ U l, v l \ H ⊆ R)) → F (X i) v = Y i) ↔
  ∃ (k : Fin r → Nat) (B : (l : Fin r) → Fin (k l) → Finset (Fin (b l))),
    (∀ l i j, i ≠ j → Disjoint (B l i) (B l j)) ∧
    (∀ l i, ∀ L ∈ D l, ∀ R ∈ U l, ¬ B l i ⊆ L ∪ R) ∧
    ¬ ∃ lo hi : Fin ((Finset.univ : Finset (Fin r)).prod (fun l => k l + 1)) → Fin m,
      (∀ t, X (lo t) ⊆ X (hi t) ∧ ¬ Y (lo t) ⊆ Y (hi t)) ∧
      (∀ t u, t < u → X (hi t) ⊆ X (lo u)) := by
  intro m d a r b X Y D U hDU
  intro T
  convert PEqualNP.Outside.L_meta_53187.main m d a r b X Y D U hDU using 12
  all_goals (congr! 12)
