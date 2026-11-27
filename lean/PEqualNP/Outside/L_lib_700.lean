import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_700_aux

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma prod_zmod2_eq_one {α : Type*} (s : Finset α) (g : α → ZMod 2) :
    (∏ a ∈ s, g a) = 1 ↔ ∀ a ∈ s, g a = 1 := by
  constructor
  · intro h a ha
    rcases zmod2_eq_zero_or_one (g a) with h0 | h1
    · rw [Finset.prod_eq_zero ha h0] at h
      exact absurd h (by decide)
    · exact h1
  · intro h
    exact Finset.prod_eq_one h

lemma indicator_eq_prod {r : ℕ} (u f : Fin r → ZMod 2) :
    (if u = f then (1 : ZMod 2) else 0) = ∏ t : Fin r, (u t + (1 + f t)) := by
  by_cases h : u = f
  · subst h
    simp only [↓reduceIte]
    refine (Finset.prod_eq_one (fun t _ => ?_)).symm
    rcases zmod2_eq_zero_or_one (u t) with hv | hv <;> rw [hv] <;> decide
  · simp only [h, ↓reduceIte]
    have hex : ∃ t : Fin r, u t ≠ f t := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    obtain ⟨t0, ht0⟩ := hex
    refine (Finset.prod_eq_zero (Finset.mem_univ t0) ?_).symm
    rcases zmod2_eq_zero_or_one (u t0) with hu | hu <;>
      rcases zmod2_eq_zero_or_one (f t0) with hf | hf <;>
      simp_all <;> decide

lemma starter_low (r : ℕ) (f : Fin r → ZMod 2) (j : Fin (2 ^ r)) :
    ∃ T : Finset (Finset (Fin (2 ^ r) × Fin r)),
      (∀ m ∈ T, m.card < r) ∧
      ∀ x : Fin (2 ^ r) → Fin r → ZMod 2,
        (∏ t : Fin r, x j t) + (if x j = f then (1 : ZMod 2) else 0) =
          ∑ m ∈ T, ∏ b ∈ m, x b.1 b.2 := by
  let coeff : Finset (Fin r) → ZMod 2 := fun s => ∏ t ∈ Finset.univ \ s, (1 + f t)
  let T0 : Finset (Finset (Fin r)) :=
    (Finset.univ.erase (Finset.univ : Finset (Fin r))).filter (fun s => coeff s = 1)
  let lift : Finset (Fin r) → Finset (Fin (2 ^ r) × Fin r) := fun s => s.image (fun t => (j, t))
  have hlift_inj : Function.Injective lift := by
    intro s1 s2 h
    ext t
    have ht : (j, t) ∈ lift s1 ↔ (j, t) ∈ lift s2 := by rw [h]
    simp only [lift, Finset.mem_image, Prod.mk.injEq, true_and, exists_eq_right] at ht
    exact ht
  refine ⟨T0.image lift, ?_, ?_⟩
  · intro m hm
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hm
    have hs_ne : s ≠ Finset.univ := (Finset.mem_erase.mp (Finset.mem_filter.mp hs).1).1
    have hcard_eq : (lift s).card = s.card := by
      refine Finset.card_image_of_injective s (fun t1 t2 h => (Prod.mk.inj h).2)
    rw [hcard_eq]
    have hss : s ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hs_ne
    have hlt := Finset.card_lt_card hss
    simpa using hlt
  · intro x
    rw [indicator_eq_prod]
    have hexp :
        (∏ t : Fin r, (x j t + (1 + f t))) =
          ∑ s : Finset (Fin r), (∏ t ∈ s, x j t) * coeff s := by
      have hpa := Finset.prod_add (fun t : Fin r => x j t) (fun t : Fin r => 1 + f t) Finset.univ
      rw [hpa, Finset.powerset_univ]
    rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ (Finset.univ : Finset (Fin r)))]
    have hcu : coeff (Finset.univ : Finset (Fin r)) = 1 := by
      simp [coeff]
    rw [hcu, mul_one, ← add_assoc, zmod2_add_self, zero_add]
    rw [Finset.sum_image (fun s1 _ s2 _ h => hlift_inj h)]
    have hsum_filt :
        ∑ s ∈ Finset.univ.erase (Finset.univ : Finset (Fin r)), (∏ t ∈ s, x j t) * coeff s =
          ∑ s ∈ T0, ∏ t ∈ s, x j t := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rcases zmod2_eq_zero_or_one (coeff s) with h0 | h1
      · simp only [h0, mul_zero, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
      · simp only [h1, mul_one, ↓reduceIte]
    rw [hsum_filt]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.prod_image (fun t1 _ t2 _ h => (Prod.mk.inj h).2)]

lemma pred_low (r : ℕ) (hr : 0 < r) (c : ZMod 2) (z : Fin (2 ^ r) → ZMod 2) :
    let pref := (Finset.univ : Finset (Fin r)).filter (fun b => b.val + 1 < r)
    ∃ T : Finset (Finset (Fin (2 ^ r) × Fin r)),
      (∀ m ∈ T, m.card < r) ∧
      ∀ x : Fin (2 ^ r) → Fin r → ZMod 2,
        c + ∑ i : Fin (2 ^ r), (∏ t ∈ pref, x i t) * z i =
          ∑ m ∈ T, ∏ b ∈ m, x b.1 b.2 := by
  dsimp only
  let pref : Finset (Fin r) := Finset.univ.filter (fun b => b.val + 1 < r)
  have hlast : (⟨r - 1, by omega⟩ : Fin r) ∉ pref := by
    simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hpref_lt : pref.card < r := by
    have hss : pref ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun h => hlast (h ▸ Finset.mem_univ _))
    simpa using Finset.card_lt_card hss
  by_cases hr1 : r = 1
  · subst hr1
    have hpref_empty : pref = ∅ := by
      ext b
      simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      omega
    have hval_const : ∀ x : Fin (2 ^ 1) → Fin 1 → ZMod 2,
        c + ∑ i : Fin (2 ^ 1), (∏ t ∈ pref, x i t) * z i = c + ∑ i : Fin (2 ^ 1), z i := by
      intro x
      simp [hpref_empty]
    rcases zmod2_eq_zero_or_one (c + ∑ i : Fin (2 ^ 1), z i) with h0 | h1
    · refine ⟨∅, by simp, fun x => ?_⟩
      rw [hval_const, h0, Finset.sum_empty]
    · refine ⟨{∅}, ?_, fun x => ?_⟩
      · intro m hm
        rw [Finset.mem_singleton.mp hm]
        simp
      · rw [hval_const, h1, Finset.sum_singleton, Finset.prod_empty]
  · have hpref_ne : pref.Nonempty := by
      refine ⟨⟨0, by omega⟩, ?_⟩
      simp only [pref, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    let lift : Fin (2 ^ r) → Finset (Fin (2 ^ r) × Fin r) := fun i => pref.image (fun t => (i, t))
    have hlift_inj : Function.Injective lift := by
      intro i1 i2 h
      obtain ⟨t0, ht0⟩ := hpref_ne
      have hmem : (i1, t0) ∈ lift i2 := h ▸ Finset.mem_image.mpr ⟨t0, ht0, rfl⟩
      obtain ⟨t1, _, ht1⟩ := Finset.mem_image.mp hmem
      exact (Prod.mk.inj ht1).1.symm
    have hlift_ne_empty : ∀ i, lift i ≠ ∅ := by
      intro i heq
      obtain ⟨t0, ht0⟩ := hpref_ne
      have hmem : (i, t0) ∈ lift i := Finset.mem_image.mpr ⟨t0, ht0, rfl⟩
      rw [heq] at hmem
      exact Finset.notMem_empty _ hmem
    let Tz : Finset (Finset (Fin (2 ^ r) × Fin r)) :=
      (Finset.univ.filter (fun i : Fin (2 ^ r) => z i = 1)).image lift
    have hempty_not_mem : ∅ ∉ Tz := by
      intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact hlift_ne_empty i hi
    let T : Finset (Finset (Fin (2 ^ r) × Fin r)) := if c = 1 then insert ∅ Tz else Tz
    refine ⟨T, ?_, ?_⟩
    · intro m hm
      by_cases hc : c = 1
      · simp only [T, hc, ↓reduceIte, Finset.mem_insert] at hm
        rcases hm with rfl | hm
        · simpa using hr
        · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
          have hcard : (lift i).card = pref.card :=
            Finset.card_image_of_injective pref (fun t1 t2 h => (Prod.mk.inj h).2)
          rw [hcard]
          exact hpref_lt
      · simp only [T, hc, ↓reduceIte] at hm
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
        have hcard : (lift i).card = pref.card :=
          Finset.card_image_of_injective pref (fun t1 t2 h => (Prod.mk.inj h).2)
        rw [hcard]
        exact hpref_lt
    · intro x
      have hTz :
          ∑ m ∈ Tz, ∏ b ∈ m, x b.1 b.2 = ∑ i : Fin (2 ^ r), (∏ t ∈ pref, x i t) * z i := by
        rw [Finset.sum_image (fun i1 _ i2 _ h => hlift_inj h), Finset.sum_filter]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rcases zmod2_eq_zero_or_one (z i) with h0 | h1
        · simp only [h0, mul_zero, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
        · simp only [h1, mul_one, ↓reduceIte]
          rw [Finset.prod_image (fun t1 _ t2 _ h => (Prod.mk.inj h).2)]
      rcases zmod2_eq_zero_or_one c with h0 | h1
      · simp only [T, h0, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte, zero_add]
        exact hTz.symm
      · simp only [T, h1, ↓reduceIte]
        rw [Finset.sum_insert hempty_not_mem, Finset.prod_empty, hTz]

lemma card_bijections_fixing_two {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (hcard : Fintype.card α = Fintype.card β)
    (a1 a2 : α) (ha : a1 ≠ a2) (b1 b2 : β) (hb : b1 ≠ b2) :
    ((Finset.univ : Finset (α → β)).filter
      (fun x => Function.Bijective x ∧ x a1 = b1 ∧ x a2 = b2)).card =
      Nat.factorial (Fintype.card α - 2) := by
  let A' := { a : α // a ≠ a1 ∧ a ≠ a2 }
  let B' := { b : β // b ≠ b1 ∧ b ≠ b2 }
  have hcardA' : Fintype.card A' = Fintype.card α - 2 := by
    have h1 : Fintype.card A' = ((Finset.univ : Finset α) \ {a1, a2}).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext a
      simp [not_or]
    rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_pair ha]
  have hcardB' : Fintype.card B' = Fintype.card α - 2 := by
    have h1 : Fintype.card B' = ((Finset.univ : Finset β) \ {b1, b2}).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext b
      simp [not_or]
    rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_pair hb, hcard]
  have hcardEquiv : Fintype.card (A' ≃ B') = Nat.factorial (Fintype.card α - 2) := by
    have eA : A' ≃ Fin (Fintype.card α - 2) := Fintype.equivFinOfCardEq hcardA'
    have eB : B' ≃ Fin (Fintype.card α - 2) := Fintype.equivFinOfCardEq hcardB'
    have eAB : (A' ≃ B') ≃ Equiv.Perm (Fin (Fintype.card α - 2)) :=
      { toFun := fun σ => (eA.symm.trans σ).trans eB
        invFun := fun τ => (eA.trans τ).trans eB.symm
        left_inv := fun σ => by ext x; simp
        right_inv := fun τ => by ext x; simp }
    rw [Fintype.card_congr eAB, Fintype.card_perm, Fintype.card_fin]
  rw [← hcardEquiv, ← Finset.card_univ]
  refine Finset.card_bij (t := (Finset.univ : Finset (A' ≃ B')))
    (fun x hx => ?_) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · have hx' := (Finset.mem_filter.mp hx).2
    have hbij : Function.Bijective x := hx'.1
    have h1 : x a1 = b1 := hx'.2.1
    have h2 : x a2 = b2 := hx'.2.2
    let e := Equiv.ofBijective x hbij
    exact
      { toFun := fun a => ⟨e a.1,
          fun heq => a.2.1 (e.injective (heq.trans h1.symm)),
          fun heq => a.2.2 (e.injective (heq.trans h2.symm))⟩
        invFun := fun b => ⟨e.symm b.1,
          fun heq => b.2.1 (by have := congrArg e heq; simpa [e, h1] using this),
          fun heq => b.2.2 (by have := congrArg e heq; simpa [e, h2] using this)⟩
        left_inv := fun a => by ext; exact e.symm_apply_apply a.1
        right_inv := fun b => by ext; exact e.apply_symm_apply b.1 }
  · intro x1 hx1 x2 hx2 heq
    have hx1' := (Finset.mem_filter.mp hx1).2
    have hx2' := (Finset.mem_filter.mp hx2).2
    funext a
    by_cases h1 : a = a1
    · rw [h1, hx1'.2.1, hx2'.2.1]
    · by_cases h2 : a = a2
      · rw [h2, hx1'.2.2, hx2'.2.2]
      · have hval := congrArg (fun σ : A' ≃ B' => (σ ⟨a, h1, h2⟩).1) heq
        exact hval
  · intro σ _
    let x : α → β := fun a =>
      if h1 : a = a1 then b1
      else if h2 : a = a2 then b2
      else (σ ⟨a, h1, h2⟩).1
    have hx1 : x a1 = b1 := by simp [x]
    have hx2 : x a2 = b2 := by simp [x, ha.symm]
    have hx_inj : Function.Injective x := by
      intro u v huv
      by_cases hu1 : u = a1 <;> by_cases hv1 : v = a1
      · rw [hu1, hv1]
      · by_cases hv2 : v = a2
        · simp only [x, hu1, hv2, ha.symm, ↓reduceDIte] at huv
          exact absurd huv hb
        · simp only [x, hu1, hv1, hv2, ↓reduceDIte] at huv
          exact absurd huv.symm (σ ⟨v, hv1, hv2⟩).2.1
      · by_cases hu2 : u = a2
        · simp only [x, hv1, hu2, ha.symm, ↓reduceDIte] at huv
          exact absurd huv.symm hb
        · simp only [x, hu1, hv1, hu2, ↓reduceDIte] at huv
          exact absurd huv (σ ⟨u, hu1, hu2⟩).2.1
      · by_cases hu2 : u = a2 <;> by_cases hv2 : v = a2
        · rw [hu2, hv2]
        · simp only [x, hv1, hu2, hv2, ha.symm, ↓reduceDIte] at huv
          exact absurd huv.symm (σ ⟨v, hv1, hv2⟩).2.2
        · simp only [x, hu1, hu2, hv2, ha.symm, ↓reduceDIte] at huv
          exact absurd huv (σ ⟨u, hu1, hu2⟩).2.2
        · simp only [x, hu1, hv1, hu2, hv2, ↓reduceDIte] at huv
          have hsub : σ ⟨u, hu1, hu2⟩ = σ ⟨v, hv1, hv2⟩ := Subtype.ext huv
          exact congrArg Subtype.val (σ.injective hsub)
    have hx_bij : Function.Bijective x :=
      (Fintype.bijective_iff_injective_and_card x).mpr ⟨hx_inj, hcard⟩
    refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx_bij, hx1, hx2⟩, ?_⟩
    ext ⟨a, ha1, ha2⟩
    simp [x, ha1, ha2]

end PEqualNP.Outside.L_lib_700_aux

theorem PEqualNP.Outside.L_lib_700 : (∀ (r k : Nat), 0 < r →
  let q := 2^r
  let I := Fin q
  let K := ZMod 2
  let S := Fin r → K
  let V := I → K
  let W := I → S
  let unit := fun (i j : I) => if j = i then (1 : K) else 0
  let target := fun (x : W) (i : I) => ∏ j : Fin r, x i j
  let starter := fun (f : S) (x : W) (i : I) =>
    target x i + (if x i = f then (1 : K) else 0)
  let flag := fun (x : W) (i : I) => ∏ j ∈
    (Finset.univ : Finset (Fin r)).filter (fun b => b.val + 1 < r), x i j
  let low := fun (g : W → K) => ∃ T : Finset (Finset (I × Fin r)),
    (∀ m ∈ T, m.card < r) ∧ ∀ x, g x = ∑ m ∈ T, ∏ b ∈ m, x b.1 b.2
  ∀ (c : Fin k → V) (z : Fin k → I → V),
    let pred := fun (a : Fin k) (x : W) (j : I) =>
      c a j + ∑ i : I, flag x i * z a i j
    let missed := (Finset.univ : Finset (I × I)).filter (fun p =>
      p.1 ≠ p.2 ∧ ∀ a, c a + z a p.1 + z a p.2 ≠ unit p.1)
    let errors := (Finset.univ : Finset W).filter (fun x =>
      (∀ f, starter f x ≠ target x) ∧ ∀ a, pred a x ≠ target x)
    (∀ f j, low (fun x => starter f x j)) ∧ (∀ a j, low (fun x => pred a x j)) ∧
      errors.card = Nat.factorial (q-2) * missed.card) := by
  intro r k hr
  dsimp only
  intro c z
  refine ⟨?_, ?_, ?_⟩
  · intro f j
    exact PEqualNP.Outside.L_lib_700_aux.starter_low r f j
  · intro a j
    exact PEqualNP.Outside.L_lib_700_aux.pred_low r hr (c a j) (fun i => z a i j)
  · let q := 2 ^ r
    let I := Fin q
    let K := ZMod 2
    let S := Fin r → K
    let W := I → S
    let unit : I → I → K := fun i j => if j = i then (1 : K) else 0
    let target : W → I → K := fun x i => ∏ j : Fin r, x i j
    let starter : S → W → I → K := fun f x i => target x i + (if x i = f then (1 : K) else 0)
    let pref : Finset (Fin r) := Finset.univ.filter (fun b => b.val + 1 < r)
    let flag : W → I → K := fun x i => ∏ j ∈ pref, x i j
    let pred : Fin k → W → I → K := fun a x j => c a j + ∑ i : I, flag x i * z a i j
    let missed : Finset (I × I) :=
      Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ∀ a, c a + z a p.1 + z a p.2 ≠ unit p.1)
    let errors : Finset W :=
      Finset.univ.filter (fun x => (∀ f, starter f x ≠ target x) ∧ ∀ a, pred a x ≠ target x)
    let s1 : S := fun _ => 1
    let s0 : S := fun b => if b.val + 1 < r then 1 else 0
    have hs_ne : s1 ≠ s0 := by
      intro h
      have hlast := congrFun h ⟨r - 1, by omega⟩
      simp only [s1, s0] at hlast
      have hlt : ¬ (r - 1 + 1 < r) := by omega
      simp only [hlt, ↓reduceIte] at hlast
      exact absurd hlast (by decide)
    have hcard_IS : Fintype.card I = Fintype.card S := by
      rw [Fintype.card_fin, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hstarter_iff : ∀ x : W, (∀ f : S, starter f x ≠ target x) ↔ Function.Bijective x := by
      intro x
      have hsurj : (∀ f : S, starter f x ≠ target x) ↔ Function.Surjective x := by
        constructor
        · intro hall f
          by_contra hnone
          push Not at hnone
          apply hall f
          funext i
          simp only [starter, hnone i, ↓reduceIte, add_zero]
        · intro hsurj f heq
          obtain ⟨i, hi⟩ := hsurj f
          have hi_eq := congrFun heq i
          simp only [starter, hi, ↓reduceIte] at hi_eq
          have h10 : (1 : ZMod 2) = 0 := by
            have := congrArg (fun t => target x i + t) hi_eq
            simp [← add_assoc] at this
          exact absurd h10 (by decide)
      rw [hsurj]
      exact ⟨fun h => (Fintype.bijective_iff_surjective_and_card x).mpr ⟨h, hcard_IS⟩, fun h => h.2⟩
    have htarget_eq : ∀ (x : W) (p1 : I), Function.Bijective x → x p1 = s1 → target x = unit p1 := by
      intro x p1 hbij hp1
      funext i
      by_cases hi : i = p1
      · subst hi
        simp only [target, unit, ↓reduceIte, hp1, s1, Finset.prod_const_one]
      · simp only [target, unit, hi, ↓reduceIte]
        have hne : x i ≠ s1 := fun h => hi (hbij.1 (h.trans hp1.symm))
        rcases PEqualNP.Outside.L_lib_700_aux.zmod2_eq_zero_or_one (∏ j : Fin r, x i j) with h0 | h1
        · exact h0
        · exfalso
          apply hne
          funext j
          exact (PEqualNP.Outside.L_lib_700_aux.prod_zmod2_eq_one Finset.univ (x i)).mp h1 j (Finset.mem_univ j)
    have hflag_iff : ∀ (x : W) (i : I), flag x i = 1 ↔ x i = s1 ∨ x i = s0 := by
      intro x i
      rw [PEqualNP.Outside.L_lib_700_aux.prod_zmod2_eq_one]
      constructor
      · intro hall
        rcases PEqualNP.Outside.L_lib_700_aux.zmod2_eq_zero_or_one (x i ⟨r - 1, by omega⟩) with h0 | h1
        · right
          funext b
          by_cases hb : b.val + 1 < r
          · simp only [s0, hb, ↓reduceIte]
            exact hall b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
          · simp only [s0, hb, ↓reduceIte]
            have hbe : b = ⟨r - 1, by omega⟩ := by
              apply Fin.ext
              have := b.isLt
              dsimp only
              omega
            rw [hbe, h0]
        · left
          funext b
          by_cases hb : b.val + 1 < r
          · exact hall b (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩)
          · have hbe : b = ⟨r - 1, by omega⟩ := by
              apply Fin.ext
              have := b.isLt
              dsimp only
              omega
            rw [hbe, h1]
      · rintro (h | h) b hb
        · rw [h]
        · rw [h]
          have hlt := (Finset.mem_filter.mp hb).2
          simp [s0, hlt]
    have hpred_eq : ∀ (x : W) (p1 p2 : I), Function.Bijective x → x p1 = s1 → x p2 = s0 →
        ∀ a : Fin k, pred a x = c a + z a p1 + z a p2 := by
      intro x p1 p2 hbij hp1 hp2 a
      have hp12 : p1 ≠ p2 := fun h => hs_ne (hp1.symm.trans (h ▸ hp2))
      funext j
      simp only [pred, Pi.add_apply]
      have hsum : ∑ i : I, flag x i * z a i j = z a p1 j + z a p2 j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p1)]
        have hp2_mem : p2 ∈ Finset.univ.erase p1 := Finset.mem_erase.mpr ⟨hp12.symm, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hp2_mem]
        have hf1 : flag x p1 = 1 := (hflag_iff x p1).mpr (Or.inl hp1)
        have hf2 : flag x p2 = 1 := (hflag_iff x p2).mpr (Or.inr hp2)
        have hrest : ∑ i ∈ (Finset.univ.erase p1).erase p2, flag x i * z a i j = 0 := by
          refine Finset.sum_eq_zero (fun i hi => ?_)
          have hi2 : i ≠ p2 := (Finset.mem_erase.mp hi).1
          have hi1 : i ≠ p1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          have hf0 : flag x i = 0 := by
            rcases PEqualNP.Outside.L_lib_700_aux.zmod2_eq_zero_or_one (flag x i) with h0 | h1
            · exact h0
            · exfalso
              rcases (hflag_iff x i).mp h1 with h | h
              · exact hi1 (hbij.1 (h.trans hp1.symm))
              · exact hi2 (hbij.1 (h.trans hp2.symm))
          rw [hf0, zero_mul]
        rw [hf1, hf2, one_mul, one_mul, hrest, add_zero]
      rw [hsum]
      ring
    let Fiber : (I × I) → Finset W := fun p =>
      Finset.univ.filter (fun x => Function.Bijective x ∧ x p.1 = s1 ∧ x p.2 = s0)
    have herr_eq : errors = missed.biUnion Fiber := by
      ext x
      simp only [errors, missed, Fiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
      rw [hstarter_iff x]
      constructor
      · rintro ⟨hbij, hpred⟩
        obtain ⟨p1, hp1⟩ := hbij.2 s1
        obtain ⟨p2, hp2⟩ := hbij.2 s0
        have hp12 : p1 ≠ p2 := fun h => hs_ne (hp1.symm.trans (h ▸ hp2))
        refine ⟨(p1, p2), ⟨hp12, fun a => ?_⟩, hbij, hp1, hp2⟩
        rw [← hpred_eq x p1 p2 hbij hp1 hp2 a, ← htarget_eq x p1 hbij hp1]
        exact hpred a
      · rintro ⟨⟨p1, p2⟩, ⟨_, hmiss⟩, hbij, hp1, hp2⟩
        refine ⟨hbij, fun a => ?_⟩
        rw [hpred_eq x p1 p2 hbij hp1 hp2 a, htarget_eq x p1 hbij hp1]
        exact hmiss a
    have hdisj : Set.PairwiseDisjoint (missed : Set (I × I)) Fiber := by
      intro p _ p' _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx hx'
      have hx1 := (Finset.mem_filter.mp hx).2
      have hx2 := (Finset.mem_filter.mp hx').2
      apply hne
      refine Prod.ext (hx1.1.1 (hx1.2.1.trans hx2.2.1.symm))
        (hx1.1.1 (hx1.2.2.trans hx2.2.2.symm))
    have hfib_card : ∀ p ∈ missed, (Fiber p).card = Nat.factorial (q - 2) := by
      intro p hp
      have hpne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2.1
      have h := PEqualNP.Outside.L_lib_700_aux.card_bijections_fixing_two hcard_IS p.1 p.2 hpne s1 s0 hs_ne
      simpa [Fiber, I, q] using h
    change errors.card = Nat.factorial (q - 2) * missed.card
    rw [herr_eq, Finset.card_biUnion hdisj, Finset.sum_congr rfl hfib_card,
      Finset.sum_const, smul_eq_mul, mul_comm]
