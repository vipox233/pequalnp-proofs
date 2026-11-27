import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25712_aux

private lemma two_mul_choose_two (m : ℕ) : 2 * Nat.choose m 2 = m * (m - 1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right, mul_add, ih]
    cases m with
    | zero => rfl
    | succ m =>
      simp only [Nat.add_sub_cancel]
      ring

private lemma int_mul_pred_ge (m s : ℕ) :
    2 * (s : ℤ) * (m : ℤ) - (s : ℤ) * ((s : ℤ) + 1) ≤ ((m * (m - 1) : ℕ) : ℤ) := by
  have hcast : ((m * (m - 1) : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
    cases m with
    | zero => simp
    | succ m => simp
  rw [hcast]
  have hnonneg : (0 : ℤ) ≤ ((m : ℤ) - (s : ℤ)) * ((m : ℤ) - (s : ℤ) - 1) := by
    rcases le_or_gt m s with hle | hgt
    · have h1 : (m : ℤ) - (s : ℤ) ≤ 0 := by omega
      have h2 : (m : ℤ) - (s : ℤ) - 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
    · have h1 : 0 ≤ (m : ℤ) - (s : ℤ) := by omega
      have h2 : 0 ≤ (m : ℤ) - (s : ℤ) - 1 := by omega
      exact mul_nonneg h1 h2
  linarith

private lemma color_sig_eq {n q : ℕ} (π : Equiv.Perm (Fin n)) (R C : Fin q → Finset (Fin n))
    {a b : Fin n}
    (hcol : (fun j : Fin q => if a ∈ R j then (0 : Fin 3) else if π a ∈ C j then 1 else 2) =
            (fun j : Fin q => if b ∈ R j then (0 : Fin 3) else if π b ∈ C j then 1 else 2)) :
    (fun j : Fin q => decide (a ∈ R j ∨ π b ∈ C j)) =
    (fun j : Fin q => decide (b ∈ R j ∨ π a ∈ C j)) := by
  funext j
  have hj := congrFun hcol j
  by_cases ha : a ∈ R j
  · simp only [ha, ↓reduceIte] at hj
    by_cases hb : b ∈ R j
    · simp [ha, hb]
    · simp only [hb, ↓reduceIte] at hj
      split_ifs at hj <;> exact absurd hj (by decide)
  · simp only [ha, ↓reduceIte] at hj
    by_cases hb : b ∈ R j
    · simp only [hb, ↓reduceIte] at hj
      split_ifs at hj <;> exact absurd hj (by decide)
    · simp only [hb, ↓reduceIte] at hj
      by_cases hpa : π a ∈ C j
      · simp only [hpa, ↓reduceIte] at hj
        by_cases hpb : π b ∈ C j
        · simp [ha, hb, hpa, hpb]
        · simp only [hpb, ↓reduceIte] at hj
          exact absurd hj (by decide)
      · simp only [hpa, ↓reduceIte] at hj
        by_cases hpb : π b ∈ C j
        · simp only [hpb, ↓reduceIte] at hj
          exact absurd hj (by decide)
        · simp [ha, hb, hpa, hpb]

private lemma mono_pairs_card_ge {n q : ℕ} (col : Fin n → (Fin q → Fin 3)) :
    let colors := 3 ^ q
    let small := n / colors
    let rem := n % colors
    let pairs := (colors - rem) * Nat.choose small 2 + rem * Nat.choose (small + 1) 2
    pairs ≤ ((Finset.univ : Finset (Fin n × Fin n)).filter (fun p => p.1 < p.2 ∧ col p.1 = col p.2)).card := by
  intro colors small rem pairs
  let S : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 < p.2 ∧ col p.1 = col p.2)
  let M : (Fin q → Fin 3) → Finset (Fin n) := fun c => Finset.univ.filter (fun i => col i = c)
  have hS_fib : S.card = ∑ c : Fin q → Fin 3, (S.filter (fun p => col p.1 = c)).card := by
    have hmaps : ∀ p ∈ S, col p.1 ∈ (Finset.univ : Finset (Fin q → Fin 3)) := fun _ _ => Finset.mem_univ _
    exact Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber_two : ∀ c : Fin q → Fin 3,
      2 * (S.filter (fun p => col p.1 = c)).card = (M c).card * ((M c).card - 1) := by
    intro c
    let A := (M c).offDiag.filter (fun p => p.1 < p.2)
    let B := (M c).offDiag.filter (fun p => p.2 < p.1)
    have hA_eq : S.filter (fun p => col p.1 = c) = A := by
      ext ⟨a, b⟩
      simp only [S, A, M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨hlt, hcab⟩, hca⟩
        exact ⟨⟨hca, hcab.symm.trans hca, ne_of_lt hlt⟩, hlt⟩
      · rintro ⟨⟨hca, hcb, _⟩, hlt⟩
        exact ⟨⟨hlt, hca.trans hcb.symm⟩, hca⟩
    have hAB_eq : A.card = B.card := by
      refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
      · intro p hp
        simp only [A, B, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
        exact ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩
      · intro p1 _ p2 _ heq
        exact Prod.ext (Prod.mk.inj heq).2 (Prod.mk.inj heq).1
      · intro p hp
        simp only [A, B, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
        exact ⟨(p.2, p.1), ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩, rfl⟩
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro p hpA hpB
      simp only [A, B, Finset.mem_filter] at hpA hpB
      exact lt_asymm hpA.2 hpB.2
    have hunion : A ∪ B = (M c).offDiag := by
      ext ⟨a, b⟩
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · rintro ⟨ha, hb, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨⟨ha, hb, hne⟩, hlt⟩
        · exact Or.inr ⟨⟨ha, hb, hne⟩, hgt⟩
    have hcard_off : (M c).offDiag.card = (M c).card * ((M c).card - 1) := by
      rw [Finset.offDiag_card]
      cases hmc : (M c).card with
      | zero => simp
      | succ k =>
        rw [Nat.add_sub_cancel, Nat.mul_succ, Nat.add_sub_cancel]
    rw [hA_eq, ← hcard_off, ← hunion, Finset.card_union_of_disjoint hdisj, ← hAB_eq, two_mul]
  have h2S : 2 * S.card = ∑ c : Fin q → Fin 3, (M c).card * ((M c).card - 1) := by
    rw [hS_fib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => hfiber_two c
  have h2pairs : 2 * pairs =
      (colors - rem) * (small * (small - 1)) + rem * ((small + 1) * small) := by
    simp only [pairs, mul_add]
    have h1 : 2 * ((colors - rem) * Nat.choose small 2) = (colors - rem) * (small * (small - 1)) := by
      rw [← mul_assoc, mul_comm 2 (colors - rem), mul_assoc, two_mul_choose_two]
    have h2 : 2 * (rem * Nat.choose (small + 1) 2) = rem * ((small + 1) * small) := by
      rw [← mul_assoc, mul_comm 2 rem, mul_assoc, two_mul_choose_two]
      simp
    rw [h1, h2]
  have hsum_m : ∑ c : Fin q → Fin 3, (M c).card = n := by
    have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin n)), col i ∈ (Finset.univ : Finset (Fin q → Fin 3)) :=
      fun _ _ => Finset.mem_univ _
    have h := Finset.card_eq_sum_card_fiberwise hmaps
    simpa [M] using h.symm
  have hcol_card : (Finset.univ : Finset (Fin q → Fin 3)).card = colors := by
    simp [colors]
  have hcol_pos : 0 < colors := Nat.pow_pos (by omega)
  have hrem_lt : rem < colors := Nat.mod_lt n hcol_pos
  have hdiv_mod : colors * small + rem = n := Nat.div_add_mod n colors
  have hZ : ((2 * pairs : ℕ) : ℤ) ≤ ((2 * S.card : ℕ) : ℤ) := by
    rw [h2S, h2pairs]
    have hsum_le : ∑ c : Fin q → Fin 3, (2 * (small : ℤ) * ((M c).card : ℤ) - (small : ℤ) * ((small : ℤ) + 1)) ≤
        ∑ c : Fin q → Fin 3, (((M c).card * ((M c).card - 1) : ℕ) : ℤ) :=
      Finset.sum_le_sum fun c _ => int_mul_pred_ge (M c).card small
    have hlhs : ∑ c : Fin q → Fin 3, (2 * (small : ℤ) * ((M c).card : ℤ) - (small : ℤ) * ((small : ℤ) + 1)) =
        2 * (small : ℤ) * (n : ℤ) - (colors : ℤ) * ((small : ℤ) * ((small : ℤ) + 1)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, hcol_card, nsmul_eq_mul]
      have hcast_sum : (∑ c : Fin q → Fin 3, ((M c).card : ℤ)) = (n : ℤ) := by
        exact_mod_cast hsum_m
      rw [hcast_sum]
    have hsmall_cast : ((small * (small - 1) : ℕ) : ℤ) = (small : ℤ) * ((small : ℤ) - 1) := by
      cases small with
      | zero => simp
      | succ k => simp
    have hrem_cast : ((colors - rem : ℕ) : ℤ) = (colors : ℤ) - (rem : ℤ) := by
      exact Nat.cast_sub (le_of_lt hrem_lt)
    have hn_cast : (n : ℤ) = (colors : ℤ) * (small : ℤ) + (rem : ℤ) := by
      exact_mod_cast hdiv_mod.symm
    have htarget : (((colors - rem) * (small * (small - 1)) + rem * ((small + 1) * small) : ℕ) : ℤ) =
        2 * (small : ℤ) * (n : ℤ) - (colors : ℤ) * ((small : ℤ) * ((small : ℤ) + 1)) := by
      rw [Nat.cast_add, Nat.cast_mul, hsmall_cast, hrem_cast]
      push_cast
      rw [hn_cast]
      ring
    rw [htarget, ← hlhs]
    simpa [Nat.cast_sum] using hsum_le
  have hN : 2 * pairs ≤ 2 * S.card := Int.ofNat_le.mp hZ
  exact Nat.le_of_mul_le_mul_left hN (by omega)

private lemma bool_xor_cancel_eq (g1 g2 r1 c2 r2 c1 : Bool)
    (h : Bool.xor g1 (Bool.xor r1 c2) = Bool.xor g2 (Bool.xor r2 c1)) :
    Bool.xor g1 g2 = Bool.xor (Bool.xor r1 c1) (Bool.xor r2 c2) := by
  cases g1 <;> cases g2 <;> cases r1 <;> cases c2 <;> cases r2 <;> cases c1 <;> simp_all

private lemma bad_tables_card {n e : ℕ} (π : Equiv.Perm (Fin n)) (f : Fin n → Bool)
    (P : Finset (Fin n × Fin n)) (hP : ∀ p ∈ P, p.1 < p.2) :
    ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
      (P.filter (fun p => Bool.xor (G p.1 (π p.2)) (G p.2 (π p.1)) ≠ Bool.xor (f p.1) (f p.2))).card ≤ e)).card =
    (∑ j ∈ Finset.range (e + 1), Nat.choose P.card j) * 2 ^ (n * n - P.card) := by
  classical
  let A : Finset (Fin n × Fin n) := P.image (fun p => (p.1, π p.2))
  have hA_card : A.card = P.card := by
    apply Finset.card_image_of_injective
    intro p1 p2 heq
    have h1 : p1.1 = p2.1 := (Prod.mk.inj heq).1
    have h2 : p1.2 = p2.2 := π.injective (Prod.mk.inj heq).2
    exact Prod.ext h1 h2
  have hswap_not_A : ∀ p ∈ P, (p.2, π p.1) ∉ A := by
    intro p hp hmem
    obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hmem
    have h1 : q.1 = p.2 := (Prod.mk.inj hEq).1
    have h2 : q.2 = p.1 := π.injective (Prod.mk.inj hEq).2
    have hlt1 := hP p hp
    have hlt2 := hP q hq
    rw [h1, h2] at hlt2
    exact lt_asymm hlt1 hlt2
  have hA_mem : ∀ {i j : Fin n}, (i, j) ∈ A → (i, π.symm j) ∈ P := by
    intro i j hmem
    obtain ⟨q, hq, hEq⟩ := Finset.mem_image.mp hmem
    have h1 : q.1 = i := (Prod.mk.inj hEq).1
    have h2 : q.2 = π.symm j := by
      have := (Prod.mk.inj hEq).2
      rw [← this, Equiv.symm_apply_apply]
    have hqeq : (i, π.symm j) = q := Prod.ext h1.symm h2.symm
    rw [hqeq]
    exact hq
  let Comp := {x : Fin n × Fin n // x ∉ A}
  let Φ : (Fin n → Fin n → Bool) ≃ ((P → Bool) × (Comp → Bool)) :=
    { toFun := fun G =>
        (fun p => Bool.xor (G p.1.1 (π p.1.2)) (G p.1.2 (π p.1.1)),
         fun x => G x.1.1 x.1.2)
      invFun := fun vu i j =>
        if h : (i, j) ∈ A then
          let hp : (i, π.symm j) ∈ P := hA_mem h
          Bool.xor (vu.1 ⟨(i, π.symm j), hp⟩) (vu.2 ⟨(π.symm j, π i), hswap_not_A _ hp⟩)
        else vu.2 ⟨(i, j), h⟩
      left_inv := fun G => by
        funext i j
        dsimp only
        split_ifs with h
        · have hp : (i, π.symm j) ∈ P := hA_mem h
          simp only [Equiv.apply_symm_apply]
          cases G i j <;> cases G (π.symm j) (π i) <;> rfl
        · rfl
      right_inv := fun ⟨v, u⟩ => by
        apply Prod.ext
        · funext ⟨p, hp⟩
          dsimp only
          have h1 : (p.1, π p.2) ∈ A := Finset.mem_image.mpr ⟨p, hp, rfl⟩
          have h2 : (p.2, π p.1) ∉ A := hswap_not_A p hp
          simp only [h1, h2, ↓reduceDIte]
          have hpeq : (⟨(p.1, π.symm (π p.2)), hA_mem h1⟩ : P) = ⟨p, hp⟩ := by
            apply Subtype.ext; apply Prod.ext; rfl; exact Equiv.symm_apply_apply π p.2
          have hceq : (⟨(π.symm (π p.2), π p.1), hswap_not_A _ (hA_mem h1)⟩ : Comp) = ⟨(p.2, π p.1), h2⟩ := by
            apply Subtype.ext; apply Prod.ext; exact Equiv.symm_apply_apply π p.2; rfl
          rw [hpeq, hceq]
          cases v ⟨p, hp⟩ <;> cases u ⟨(p.2, π p.1), h2⟩ <;> rfl
        · funext ⟨x, hx⟩
          dsimp only
          simp [hx] }
  let Vbad : Finset (P → Bool) := Finset.univ.filter (fun v : P → Bool =>
    (Finset.univ.filter (fun p : P => v p ≠ Bool.xor (f p.1.1) (f p.1.2))).card ≤ e)
  have hbij :
      ((Finset.univ : Finset (Fin n → Fin n → Bool)).filter (fun G =>
        (P.filter (fun p => Bool.xor (G p.1 (π p.2)) (G p.2 (π p.1)) ≠ Bool.xor (f p.1) (f p.2))).card ≤ e)).card =
      (Vbad ×ˢ (Finset.univ : Finset (Comp → Bool))).card := by
    refine Finset.card_bij (fun G _ => Φ G) ?_ ?_ ?_
    · intro G hG
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
      have hcard_eq : (Finset.univ.filter (fun p : P => (Φ G).1 p ≠ Bool.xor (f p.1.1) (f p.1.2))).card =
          (P.filter (fun p => Bool.xor (G p.1 (π p.2)) (G p.2 (π p.1)) ≠ Bool.xor (f p.1) (f p.2))).card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact ⟨p.2, hp⟩
        · intro p1 _ p2 _ heq; exact Subtype.ext heq
        · intro p hp
          simp only [Finset.mem_filter] at hp
          exact ⟨⟨p, hp.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩, rfl⟩
      rw [hcard_eq]
      exact hG
    · intro G1 _ G2 _ heq; exact Φ.injective heq
    · intro vu hvu
      simp only [Finset.mem_product, Vbad, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hvu
      refine ⟨Φ.symm vu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Φ.apply_symm_apply vu⟩
      have hcard_eq :
          (P.filter (fun p => Bool.xor (Φ.symm vu p.1 (π p.2)) (Φ.symm vu p.2 (π p.1)) ≠ Bool.xor (f p.1) (f p.2))).card =
          (Finset.univ.filter (fun p : P => vu.1 p ≠ Bool.xor (f p.1.1) (f p.1.2))).card := by
        have hv : ∀ p : P, Bool.xor (Φ.symm vu p.1.1 (π p.1.2)) (Φ.symm vu p.1.2 (π p.1.1)) = vu.1 p := fun p => by
          have := congrArg Prod.fst (Φ.apply_symm_apply vu)
          exact congrFun this p
        refine Finset.card_bij (fun p hp => ⟨p, (Finset.mem_filter.mp hp).1⟩) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          rw [← hv ⟨p, hp.1⟩]
          exact hp.2
        · intro p1 _ p2 _ heq; exact congrArg Subtype.val heq
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          refine ⟨p.1, Finset.mem_filter.mpr ⟨p.2, ?_⟩, rfl⟩
          rw [hv p]; exact hp
      rw [hcard_eq]
      exact hvu
  rw [hbij, Finset.card_product]
  have hComp_card : Fintype.card Comp = n * n - P.card := by
    have h1 : Fintype.card Comp = (Finset.univ \ A).card := by
      refine Fintype.card_of_subtype (Finset.univ \ A) ?_
      intro x; simp
    rw [h1, Finset.card_sdiff, Finset.inter_univ, hA_card]
    simp
  have hU_card : (Finset.univ : Finset (Comp → Bool)).card = 2 ^ (n * n - P.card) := by
    simp [hComp_card]
  have hV_card : Vbad.card = ∑ j ∈ Finset.range (e + 1), Nat.choose P.card j := by
    let D : (P → Bool) → Finset P := fun v => Finset.univ.filter (fun p : P => v p ≠ Bool.xor (f p.1.1) (f p.1.2))
    let Subs : Finset (Finset P) := (Finset.univ : Finset (Finset P)).filter (fun S => S.card ≤ e)
    have hVD : Vbad.card = Subs.card := by
      refine Finset.card_bij (fun v _ => D v) ?_ ?_ ?_
      · intro v hv
        simp only [Vbad, Subs, D, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact hv
      · intro v1 _ v2 _ heq
        funext p
        have hmem := Finset.ext_iff.mp heq p
        simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        cases hv1 : v1 p <;> cases hv2 : v2 p <;> cases hf : Bool.xor (f p.1.1) (f p.1.2) <;>
          simp_all
      · intro S hS
        simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and] at hS
        let v : P → Bool := fun p => if p ∈ S then !(Bool.xor (f p.1.1) (f p.1.2)) else Bool.xor (f p.1.1) (f p.1.2)
        have hDv : D v = S := by
          ext p
          simp only [D, v, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hp : p ∈ S
          · simp [hp]
          · simp [hp]
        exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (D v).card ≤ e by rw [hDv]; exact hS⟩, hDv⟩
    rw [hVD]
    have hmaps : ∀ S ∈ Subs, S.card ∈ Finset.range (e + 1) := by
      intro S hS
      simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and] at hS
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hS)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjle : j ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hset : Subs.filter (fun S => S.card = j) = (Finset.univ : Finset P).powersetCard j := by
      ext S
      simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hjle, h⟩⟩
    rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_coe]
  rw [hV_card, hU_card]

end PEqualNP.Outside.L_meta_25712_aux

theorem PEqualNP.Outside.L_meta_25712 :
    ∀ (n q e : ℕ),
      let I := Fin n
      let Table := I → I → Bool
      let loss := fun (G : Table) (q : ℕ) (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
          (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool) =>
        ((Finset.univ : Finset (I × I)).filter (fun z =>
          out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
            Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))).card
      let colors := 3 ^ q
      let small := n / colors
      let rem := n % colors
      let pairs := (colors - rem) * Nat.choose small 2 + rem * Nat.choose (small + 1) 2
      n.factorial * (2 * colors) ^ n * (∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) < 2 ^ pairs →
        ∃ G : Table, ∀ (π : Equiv.Perm I) (rowFlip colFlip : I → Bool)
          (R C : Fin q → Finset I) (out : Finset I → (Fin q → Bool) → Bool),
          e < loss G q π rowFlip colFlip R C out := by
  intro n q e I Table loss colors small rem pairs hbound
  classical
  let Color := Fin q → Fin 3
  let S : (I → Color) → Finset (I × I) := fun col =>
    Finset.univ.filter (fun p => p.1 < p.2 ∧ col p.1 = col p.2)
  have hS_ge : ∀ col : I → Color, pairs ≤ (S col).card := fun col =>
    PEqualNP.Outside.L_meta_25712_aux.mono_pairs_card_ge col
  have hpairs_le : pairs ≤ n * n := by
    have h0 := hS_ge (fun _ _ => 0)
    have hle : (S (fun _ _ => 0)).card ≤ (Finset.univ : Finset (I × I)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simp only [Finset.card_univ, Fintype.card_prod, I, Fintype.card_fin] at hle
    exact le_trans h0 hle
  let pickP : (I → Color) → Finset (I × I) := fun col =>
    (Finset.exists_subset_card_eq (hS_ge col)).choose
  have hpickP_sub : ∀ col, pickP col ⊆ S col := fun col =>
    (Finset.exists_subset_card_eq (hS_ge col)).choose_spec.1
  have hpickP_card : ∀ col, (pickP col).card = pairs := fun col =>
    (Finset.exists_subset_card_eq (hS_ge col)).choose_spec.2
  let Params := Equiv.Perm I × (I → Bool) × (I → Color)
  let badOf : Params → Finset Table := fun θ =>
    (Finset.univ : Finset Table).filter (fun G =>
      ((pickP θ.2.2).filter (fun p =>
        Bool.xor (G p.1 (θ.1 p.2)) (G p.2 (θ.1 p.1)) ≠ Bool.xor (θ.2.1 p.1) (θ.2.1 p.2))).card ≤ e)
  have hbad_card : ∀ θ : Params,
      (badOf θ).card = (∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) * 2 ^ (n * n - pairs) := by
    intro θ
    have hlt : ∀ p ∈ pickP θ.2.2, p.1 < p.2 := fun p hp =>
      (Finset.mem_filter.mp (hpickP_sub θ.2.2 hp)).2.1
    have h := PEqualNP.Outside.L_meta_25712_aux.bad_tables_card (e := e) θ.1 θ.2.1 (pickP θ.2.2) hlt
    rw [hpickP_card θ.2.2] at h
    exact h
  let AllBad : Finset Table := (Finset.univ : Finset Params).biUnion badOf
  have hParams_card : Fintype.card Params = n.factorial * (2 * colors) ^ n := by
    simp only [Params, Color, I, colors, Fintype.card_prod, Fintype.card_perm, Fintype.card_pi,
      Fintype.card_fin, Fintype.card_bool, Finset.prod_const, Finset.card_univ]
    rw [← mul_pow]
  have hAllBad_lt : AllBad.card < (Finset.univ : Finset Table).card := by
    have hle : AllBad.card ≤
        (n.factorial * (2 * colors) ^ n * ∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) * 2 ^ (n * n - pairs) := by
      calc AllBad.card
          ≤ ∑ θ : Params, (badOf θ).card := Finset.card_biUnion_le
        _ = ∑ _θ : Params, (∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) * 2 ^ (n * n - pairs) :=
            Finset.sum_congr rfl fun θ _ => hbad_card θ
        _ = Fintype.card Params * ((∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) * 2 ^ (n * n - pairs)) := by
            simp
        _ = (n.factorial * (2 * colors) ^ n * ∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) * 2 ^ (n * n - pairs) := by
            rw [hParams_card]; ring
    have hlt : (n.factorial * (2 * colors) ^ n * ∑ j ∈ Finset.range (e + 1), Nat.choose pairs j) * 2 ^ (n * n - pairs) <
        2 ^ pairs * 2 ^ (n * n - pairs) :=
      Nat.mul_lt_mul_of_pos_right hbound (Nat.two_pow_pos _)
    have hpow : 2 ^ pairs * 2 ^ (n * n - pairs) = (Finset.univ : Finset Table).card := by
      rw [← pow_add, Nat.add_sub_cancel' hpairs_le]
      simp [Table, I, pow_mul]
    rw [← hpow]
    exact lt_of_le_of_lt hle hlt
  obtain ⟨G, _, hG_not_bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hAllBad_lt
  refine ⟨G, fun π rowFlip colFlip R C out => ?_⟩
  let f : I → Bool := fun i => Bool.xor (rowFlip i) (colFlip (π i))
  let col : I → Color := fun i j => if i ∈ R j then 0 else if π i ∈ C j then 1 else 2
  have hnot_mem : G ∉ badOf (π, f, col) := fun hmem =>
    hG_not_bad (Finset.mem_biUnion.mpr ⟨(π, f, col), Finset.mem_univ _, hmem⟩)
  have hgt_e : e < ((pickP col).filter (fun p =>
      Bool.xor (G p.1 (π p.2)) (G p.2 (π p.1)) ≠ Bool.xor (f p.1) (f p.2))).card := by
    by_contra hle
    exact hnot_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_of_not_lt hle⟩)
  let L : Finset (I × I) := Finset.univ.filter (fun z =>
    out {z.1, z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
      Bool.xor (G z.1 (π z.2)) (Bool.xor (rowFlip z.1) (colFlip (π z.2))))
  have hcard_le_L : ((pickP col).filter (fun p =>
      Bool.xor (G p.1 (π p.2)) (G p.2 (π p.1)) ≠ Bool.xor (f p.1) (f p.2))).card ≤ L.card := by
    let pick : I × I → I × I := fun p => if p ∈ L then p else (p.2, p.1)
    refine Finset.card_le_card_of_injOn pick ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter] at hp
      have hpS := Finset.mem_filter.mp (hpickP_sub col hp.1)
      have hcol_eq : col p.1 = col p.2 := hpS.2.2
      refine Finset.mem_coe.mpr ?_
      dsimp only [pick]
      by_cases hpL : p ∈ L
      · simp [hpL]
      · simp only [hpL, ↓reduceIte]
        by_contra hswapL
        have h1 : out {p.1, p.2} (fun j => decide (p.1 ∈ R j ∨ π p.2 ∈ C j)) =
            Bool.xor (G p.1 (π p.2)) (Bool.xor (rowFlip p.1) (colFlip (π p.2))) := by
          by_contra hne
          exact hpL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        have h2 : out {p.2, p.1} (fun j => decide (p.2 ∈ R j ∨ π p.1 ∈ C j)) =
            Bool.xor (G p.2 (π p.1)) (Bool.xor (rowFlip p.2) (colFlip (π p.1))) := by
          by_contra hne
          exact hswapL (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
        have hsig := PEqualNP.Outside.L_meta_25712_aux.color_sig_eq π R C hcol_eq
        have hout_eq : out {p.1, p.2} (fun j => decide (p.1 ∈ R j ∨ π p.2 ∈ C j)) =
            out {p.2, p.1} (fun j => decide (p.2 ∈ R j ∨ π p.1 ∈ C j)) := by
          rw [Finset.pair_comm p.1 p.2, hsig]
        rw [h1, h2] at hout_eq
        exact hp.2 (PEqualNP.Outside.L_meta_25712_aux.bool_xor_cancel_eq _ _ _ _ _ _ hout_eq)
    · intro p1 hp1 p2 hp2 heq
      have hp1_lt : p1.1 < p1.2 := (Finset.mem_filter.mp (hpickP_sub col (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).1)).2.1
      have hp2_lt : p2.1 < p2.2 := (Finset.mem_filter.mp (hpickP_sub col (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).1)).2.1
      dsimp only [pick] at heq
      split_ifs at heq with h1 h2 h2
      · exact heq
      · have ha : p1.1 = p2.2 := (Prod.mk.inj heq).1
        have hb : p1.2 = p2.1 := (Prod.mk.inj heq).2
        rw [ha, hb] at hp1_lt
        exact absurd hp1_lt (lt_asymm hp2_lt)
      · have ha : p1.2 = p2.1 := (Prod.mk.inj heq).1
        have hb : p1.1 = p2.2 := (Prod.mk.inj heq).2
        rw [← ha, ← hb] at hp2_lt
        exact absurd hp2_lt (lt_asymm hp1_lt)
      · exact Prod.ext (Prod.mk.inj heq).2 (Prod.mk.inj heq).1
  exact lt_of_lt_of_le hgt_e hcard_le_L
