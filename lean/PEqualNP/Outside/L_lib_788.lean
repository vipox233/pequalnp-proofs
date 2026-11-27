import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_788_aux

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma pow_succ_mul_sub_le (B : ℕ) : ∀ t : ℕ, t ≤ B → (B + 1) ^ t * (B - t) ≤ B ^ (t + 1) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp
  | succ t ih =>
    intro ht
    have ht' : t ≤ B := by omega
    have hih := ih ht'
    have hstep : (B + 1) * (B - (t + 1)) ≤ (B - t) * B := by
      zify [ht, ht']
      nlinarith
    calc (B + 1) ^ (t + 1) * (B - (t + 1))
        = (B + 1) ^ t * ((B + 1) * (B - (t + 1))) := by ring
      _ ≤ (B + 1) ^ t * ((B - t) * B) := Nat.mul_le_mul_left _ hstep
      _ = ((B + 1) ^ t * (B - t)) * B := by ring
      _ ≤ B ^ (t + 1) * B := Nat.mul_le_mul_right B hih
      _ = B ^ (t + 2) := by ring

private lemma nat_le_of_pow_le_pow_left {a b n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra hlt
  have hgt : b < a := Nat.lt_of_not_le hlt
  have hpow : b ^ n < a ^ n := Nat.pow_lt_pow_left hgt hn
  omega

private lemma sum_pow_eq_sum_prod {α : Type*} (s : Finset α) (g : α → ℕ) (r : ℕ) :
    (∑ a ∈ s, g a) ^ r = ∑ f : Fin r → s, ∏ t : Fin r, g (f t).1 := by
  have hps := Fintype.prod_sum (fun (_ : Fin r) (a : s) => g a.1)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hps
  rw [← Finset.sum_coe_sort s g]
  exact hps

private lemma pow_half_le_two_mul (k : ℕ) (hk : 0 < k) :
    (2 * k + 1) ^ k ≤ 2 * (2 * k) ^ k := by
  have h := pow_succ_mul_sub_le (2 * k) k (by omega)
  have hsub : 2 * k - k = k := by omega
  rw [hsub] at h
  have h2 : (2 * k + 1) ^ k * k ≤ (2 * (2 * k) ^ k) * k := by
    calc (2 * k + 1) ^ k * k
        ≤ (2 * k) ^ (k + 1) := h
      _ = (2 * (2 * k) ^ k) * k := by ring
  exact Nat.le_of_mul_le_mul_right h2 hk

private def wt {m : ℕ} (y : Fin m → ZMod 2) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => y j = 1)).card

private lemma wt_le {m : ℕ} (y : Fin m → ZMod 2) : wt y ≤ m := by
  calc wt y ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := by simp

private lemma wt_add_one {m : ℕ} (y : Fin m → ZMod 2) :
    wt (fun j => y j + 1) = m - wt y := by
  have hdisj : Disjoint (Finset.univ.filter (fun j : Fin m => y j = 1))
      (Finset.univ.filter (fun j : Fin m => y j + 1 = 1)) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1] at h2
    exact absurd h2 (by decide)
  have hunion : Finset.univ.filter (fun j : Fin m => y j = 1) ∪
      Finset.univ.filter (fun j : Fin m => y j + 1 = 1) = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rcases zmod2_eq_zero_or_one (y j) with h | h
    · right; rw [h]; decide
    · left; exact h
  have hsum : wt y + wt (fun j => y j + 1) = m := by
    change (Finset.univ.filter (fun j : Fin m => y j = 1)).card +
      (Finset.univ.filter (fun j : Fin m => y j + 1 = 1)).card = m
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  omega

private lemma sum_pow_wt (m A B : ℕ) :
    ∑ y : Fin m → ZMod 2, A ^ wt y * B ^ (m - wt y) = (A + B) ^ m := by
  induction m with
  | zero =>
    have huniq : (Finset.univ : Finset (Fin 0 → ZMod 2)) = {Fin.elim0} := by
      ext y
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [huniq, Finset.sum_singleton]
    simp [wt]
  | succ m ih =>
    have hwt_cons : ∀ (b : ZMod 2) (y : Fin m → ZMod 2),
        wt (Fin.cons (α := fun _ => ZMod 2) b y) = (if b = 1 then 1 else 0) + wt y := by
      intro b y
      unfold wt
      have hsplit : (Finset.univ.filter (fun j : Fin (m + 1) => Fin.cons (α := fun _ => ZMod 2) b y j = 1)).card =
          (if b = 1 then 1 else 0) +
          ((Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ).card := by
        have hdisj : Disjoint (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅)
            ((Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ) := by
          split_ifs
          · rw [Finset.disjoint_singleton_left]
            simp
          · exact Finset.disjoint_empty_left _
        have heq : Finset.univ.filter (fun j : Fin (m + 1) => Fin.cons (α := fun _ => ZMod 2) b y j = 1) =
            (if b = 1 then ({0} : Finset (Fin (m + 1))) else ∅) ∪
            (Finset.univ.filter (fun j : Fin m => y j = 1)).image Fin.succ := by
          ext j
          refine Fin.cases ?_ ?_ j
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero,
              Finset.mem_union, Finset.mem_image, Fin.succ_ne_zero, and_false, exists_false, or_false]
            split_ifs with hb <;> simp [hb]
          · intro i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_succ,
              Finset.mem_union, Finset.mem_image]
            constructor
            · intro hy; right; exact ⟨i, hy, rfl⟩
            · rintro (h0 | ⟨i', hi', hsucc⟩)
              · split_ifs at h0
                · rw [Finset.mem_singleton] at h0; exact absurd h0 (Fin.succ_ne_zero i)
                · exact absurd h0 (Finset.notMem_empty _)
              · cases Fin.succ_injective _ hsucc; exact hi'
        rw [heq, Finset.card_union_of_disjoint hdisj]
        congr 1
        split_ifs <;> simp
      rw [hsplit, Finset.card_image_of_injective _ (Fin.succ_injective m)]
    have hbij : ∑ y : Fin (m + 1) → ZMod 2, A ^ wt y * B ^ (m + 1 - wt y) =
        ∑ p : ZMod 2 × (Fin m → ZMod 2),
          A ^ wt (Fin.cons p.1 p.2) * B ^ (m + 1 - wt (Fin.cons p.1 p.2)) := by
      symm
      apply Finset.sum_bij (fun p _ => Fin.cons p.1 p.2)
      · intro _ _; exact Finset.mem_univ _
      · intro p1 _ p2 _ h
        have h0 : p1.1 = p2.1 := by
          have := congrFun h 0
          simpa using this
        have htl : p1.2 = p2.2 := by
          funext i
          have := congrFun h i.succ
          simpa using this
        exact Prod.ext h0 htl
      · intro y _
        refine ⟨(y 0, fun i => y i.succ), Finset.mem_univ _, ?_⟩
        funext j
        refine Fin.cases ?_ ?_ j
        · simp
        · intro i; simp
      · intro _ _; rfl
    rw [hbij, Fintype.sum_prod_type]
    have huniv2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    rw [huniv2, Finset.sum_pair (by decide : (0 : ZMod 2) ≠ 1)]
    have h0 : ∑ y : Fin m → ZMod 2,
        A ^ wt (Fin.cons 0 y) * B ^ (m + 1 - wt (Fin.cons 0 y)) = B * (A + B) ^ m := by
      have hterm : ∀ y : Fin m → ZMod 2,
          A ^ wt (Fin.cons 0 y) * B ^ (m + 1 - wt (Fin.cons 0 y)) =
          B * (A ^ wt y * B ^ (m - wt y)) := by
        intro y
        rw [hwt_cons]
        have h01 : (0 : ZMod 2) ≠ 1 := by decide
        simp only [h01, ↓reduceIte, zero_add]
        have hle := wt_le y
        have hsub : m + 1 - wt y = (m - wt y) + 1 := by omega
        rw [hsub, pow_succ]
        ring
      simp_rw [hterm, ← Finset.mul_sum, ih]
    have h1 : ∑ y : Fin m → ZMod 2,
        A ^ wt (Fin.cons 1 y) * B ^ (m + 1 - wt (Fin.cons 1 y)) = A * (A + B) ^ m := by
      have hterm : ∀ y : Fin m → ZMod 2,
          A ^ wt (Fin.cons 1 y) * B ^ (m + 1 - wt (Fin.cons 1 y)) =
          A * (A ^ wt y * B ^ (m - wt y)) := by
        intro y
        rw [hwt_cons]
        simp only [↓reduceIte]
        have hsub : m + 1 - (1 + wt y) = m - wt y := by omega
        rw [hsub, Nat.add_comm 1 (wt y), pow_succ]
        ring
      simp_rw [hterm, ← Finset.mul_sum, ih]
    rw [h0, h1, pow_succ]
    ring

private lemma card_toBits_bijective (N : ℕ) :
    Function.Bijective (fun (s : Fin (2 ^ N)) (t : Fin N) =>
      if s.val.testBit t.val then (1 : ZMod 2) else 0) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · intro s1 s2 h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < N
    · have hi' := congrFun h ⟨i, hi⟩
      dsimp only at hi'
      cases hb1 : s1.val.testBit i <;> cases hb2 : s2.val.testBit i
      · rfl
      · simp [hb1, hb2] at hi'
      · simp [hb1, hb2] at hi'
      · rfl
    · have h1 : s1.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s1.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))
      have h2 : s2.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s2.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hi)))
      rw [h1, h2]
  · simp [Fintype.card_fin, ZMod.card]

private lemma card_shift_linear_fiber (n L : ℕ) (hn : 0 < n) (hL : 0 < L)
    (c : Fin n → ZMod 2) (hc : c ≠ 0) (y : Fin L → ZMod 2) :
    (Finset.univ.filter (fun v : Fin (n + L - 1) → ZMod 2 =>
      (fun j : Fin L => ∑ i : Fin n, c i * v ⟨j.val + i.val, by omega⟩) = y)).card = 2 ^ (n - 1) := by
  let N := n + L - 1
  have hN : N = n + L - 1 := rfl
  let Sc : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => c i = 1)
  have hSc_ne : Sc.Nonempty := by
    by_contra hempty
    apply hc
    funext i
    rcases zmod2_eq_zero_or_one (c i) with h0 | h1
    · exact h0
    · exfalso
      exact hempty ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩⟩
  let p : Fin n := Sc.max' hSc_ne
  have hcp : c p = 1 := (Finset.mem_filter.mp (Finset.max'_mem Sc hSc_ne)).2
  have hc_gt : ∀ i : Fin n, p < i → c i = 0 := by
    intro i hgt
    rcases zmod2_eq_zero_or_one (c i) with h0 | h1
    · exact h0
    · exfalso
      have hmem : i ∈ Sc := Finset.mem_filter.mpr ⟨Finset.mem_univ i, h1⟩
      have hle : i ≤ p := Finset.le_max' Sc i hmem
      exact not_le_of_gt hgt hle
  let Φ : (Fin N → ZMod 2) → (Fin L → ZMod 2) :=
    fun v j => ∑ i : Fin n, c i * v ⟨j.val + i.val, by omega⟩
  let Out := { t : Fin N // ¬ (p.val ≤ t.val ∧ t.val < p.val + L) }
  have hOut_card : Fintype.card Out = n - 1 := by
    let InS : Finset (Fin N) := Finset.univ.filter (fun t : Fin N => p.val ≤ t.val ∧ t.val < p.val + L)
    have hIn_card : InS.card = L := by
      have hbij : InS.card = (Finset.univ : Finset (Fin L)).card := by
        symm
        apply Finset.card_bij (fun (j : Fin L) _ => (⟨p.val + j.val, by omega⟩ : Fin N))
        · intro j _
          simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and]
          omega
        · intro j1 _ j2 _ h
          have hv : p.val + j1.val = p.val + j2.val := congrArg Fin.val h
          exact Fin.ext (by omega)
        · intro t ht
          simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          refine ⟨⟨t.val - p.val, by omega⟩, Finset.mem_univ _, Fin.ext (by dsimp only; omega)⟩
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    have hcomp : InS.card + (Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L))).card = N := by
      have hdisj : Disjoint InS (Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L))) := by
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [InS, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact h2 h1
      have hunion : InS ∪ Finset.univ.filter (fun t : Fin N => ¬ (p.val ≤ t.val ∧ t.val < p.val + L)) = Finset.univ := by
        ext t
        simp only [InS, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact em _
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    rw [Fintype.card_subtype]
    omega
  let ψ : (Fin N → ZMod 2) → (Fin L → ZMod 2) × (Out → ZMod 2) :=
    fun v => (Φ v, fun t => v t.1)
  have hψ_bij : Function.Bijective ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · intro v1 v2 hψ
      have hΦ : Φ v1 = Φ v2 := congrArg Prod.fst hψ
      have hOut : ∀ t : Out, v1 t.1 = v2 t.1 := fun t => congrFun (congrArg Prod.snd hψ) t
      have hall : ∀ k : ℕ, ∀ hk : k < N, v1 ⟨k, hk⟩ = v2 ⟨k, hk⟩ := by
        intro k
        induction k using Nat.strong_induction_on with
        | ind k ih =>
          intro hk
          by_cases hwin : p.val ≤ k ∧ k < p.val + L
          · let j : Fin L := ⟨k - p.val, by omega⟩
            have hj := congrFun hΦ j
            dsimp only [Φ] at hj
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p),
                ← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at hj
            have hrest : ∑ i ∈ Finset.univ.erase p, c i * v1 ⟨j.val + i.val, by omega⟩ =
                ∑ i ∈ Finset.univ.erase p, c i * v2 ⟨j.val + i.val, by omega⟩ := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              have hne : i ≠ p := Finset.ne_of_mem_erase hi
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · have hlt_k : j.val + i.val < k := by dsimp only [j]; omega
                rw [ih (j.val + i.val) hlt_k (by omega)]
              · rw [hc_gt i hgt, zero_mul, zero_mul]
            rw [hrest, hcp, one_mul, one_mul] at hj
            have heq_idx : (⟨j.val + p.val, by omega⟩ : Fin N) = ⟨k, hk⟩ := Fin.ext (by dsimp only [j]; omega)
            rw [heq_idx] at hj
            exact add_right_cancel hj
          · exact hOut ⟨⟨k, hk⟩, hwin⟩
      funext t
      exact hall t.val t.isLt
    · rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_fin, Fintype.card_fin, hOut_card, ZMod.card, ← pow_add]
      congr 1
      omega
  have hbij : (Finset.univ.filter (fun v : Fin N → ZMod 2 => Φ v = y)).card =
      (Finset.univ : Finset (Out → ZMod 2)).card := by
    apply Finset.card_bij (fun v _ => (ψ v).2)
    · intro _ _; exact Finset.mem_univ _
    · intro v1 hv1 v2 hv2 heq
      have h1 := (Finset.mem_filter.mp hv1).2
      have h2 := (Finset.mem_filter.mp hv2).2
      exact hψ_bij.1 (Prod.ext (h1.trans h2.symm) heq)
    · intro r _
      rcases hψ_bij.2 (y, r) with ⟨v, hv⟩
      refine ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, congrArg Prod.fst hv⟩, congrArg Prod.snd hv⟩
  rw [hbij, Finset.card_univ, Fintype.card_fun, hOut_card, ZMod.card]

private lemma card_bias_high_bound (k m : ℕ) (hk : 64 ≤ k) (hm : 512 * k ≤ m) :
    2 ^ (k / 16 + k + 2) *
      (Finset.univ.filter (fun y : Fin m → ZMod 2 => 15 * m < 28 * wt y)).card ≤ 2 ^ m := by
  let H : Finset (Fin m → ZMod 2) := Finset.univ.filter (fun y => 15 * m < 28 * wt y)
  have h28 : H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) ≤ (28 ^ 28) ^ m := by
    have hstep1 : H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) =
        ∑ _f : Fin 28 → H, (15 ^ (15 * m) * 13 ^ (13 * m)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, smul_eq_mul]
    have hstep2 : ∑ _f : Fin 28 → H, (15 ^ (15 * m) * 13 ^ (13 * m)) ≤
        ∑ f : Fin 28 → H, ∏ t : Fin 28, (15 ^ wt (f t).1 * 13 ^ (m - wt (f t).1)) := by
      refine Finset.sum_le_sum (fun f _ => ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
      let W : ℕ := ∑ t : Fin 28, wt (f t).1
      have hW_lo : 15 * m ≤ W := by
        have hsum_lo : ∑ _t : Fin 28, (15 * m) ≤ ∑ t : Fin 28, (28 * wt (f t).1) := by
          refine Finset.sum_le_sum (fun t _ => ?_)
          have ht := (Finset.mem_filter.mp (f t).2).2
          omega
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum] at hsum_lo
        exact Nat.le_of_mul_le_mul_left hsum_lo (by decide)
      have hW_comp : W + ∑ t : Fin 28, (m - wt (f t).1) = 28 * m := by
        rw [← Finset.sum_add_distrib]
        calc ∑ t : Fin 28, (wt (f t).1 + (m - wt (f t).1))
            = ∑ _t : Fin 28, m := Finset.sum_congr rfl (fun t _ => by have := wt_le (f t).1; omega)
          _ = 28 * m := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      let rem : ℕ := ∑ t : Fin 28, (m - wt (f t).1)
      have hrem_eq : rem + (W - 15 * m) = 13 * m := by omega
      have hW_eq : W = 15 * m + (W - 15 * m) := by omega
      calc 15 ^ (15 * m) * 13 ^ (13 * m)
          = 15 ^ (15 * m) * (13 ^ rem * 13 ^ (W - 15 * m)) := by rw [← pow_add, hrem_eq]
        _ = 15 ^ (15 * m) * 13 ^ (W - 15 * m) * 13 ^ rem := by ring
        _ ≤ 15 ^ (15 * m) * 15 ^ (W - 15 * m) * 13 ^ rem := by
              refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _))
        _ = 15 ^ W * 13 ^ rem := by rw [← pow_add, ← hW_eq]
    have hstep3 : ∑ f : Fin 28 → H, ∏ t : Fin 28, (15 ^ wt (f t).1 * 13 ^ (m - wt (f t).1)) =
        (∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y)) ^ 28 :=
      (sum_pow_eq_sum_prod H (fun y => 15 ^ wt y * 13 ^ (m - wt y)) 28).symm
    have hstep4 : ∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y) ≤ 28 ^ m := by
      calc ∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y)
          ≤ ∑ y : Fin m → ZMod 2, 15 ^ wt y * 13 ^ (m - wt y) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ H)
        _ = (15 + 13) ^ m := sum_pow_wt m 15 13
        _ = 28 ^ m := by norm_num
    calc H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m))
        ≤ (∑ y ∈ H, 15 ^ wt y * 13 ^ (m - wt y)) ^ 28 := by rw [hstep1, ← hstep3]; exact hstep2
      _ ≤ (28 ^ m) ^ 28 := Nat.pow_le_pow_left hstep4 28
      _ = (28 ^ 28) ^ m := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hbase : 28 ^ 28 * 16 ≤ 15 ^ 15 * 13 ^ 13 * 2 ^ 28 * 15 := by norm_num
  have hbase_m : (28 ^ 28) ^ m * 16 ^ m ≤ (15 ^ (15 * m) * 13 ^ (13 * m)) * (2 ^ m) ^ 28 * 15 ^ m := by
    have hp := Nat.pow_le_pow_left hbase m
    calc (28 ^ 28) ^ m * 16 ^ m
        = (28 ^ 28 * 16) ^ m := by rw [mul_pow]
      _ ≤ (15 ^ 15 * 13 ^ 13 * 2 ^ 28 * 15) ^ m := hp
      _ = (15 ^ 15) ^ m * (13 ^ 13) ^ m * (2 ^ 28) ^ m * 15 ^ m := by simp only [mul_pow]
      _ = (15 ^ (15 * m) * 13 ^ (13 * m)) * (2 ^ m) ^ 28 * 15 ^ m := by
            simp only [← pow_mul, Nat.mul_comm 28 m]
  have h1516 : 15 ^ 11 * 2 ≤ 16 ^ 11 := by norm_num
  have hpow42 : 15 ^ m * 2 ^ (42 * k) ≤ 16 ^ m := by
    have h462 : 11 * (42 * k) ≤ m := by omega
    have hp1 : 15 ^ (11 * (42 * k)) * 2 ^ (42 * k) ≤ 16 ^ (11 * (42 * k)) := by
      calc 15 ^ (11 * (42 * k)) * 2 ^ (42 * k)
          = (15 ^ 11 * 2) ^ (42 * k) := by rw [mul_pow, ← pow_mul]
        _ ≤ (16 ^ 11) ^ (42 * k) := Nat.pow_le_pow_left h1516 (42 * k)
        _ = 16 ^ (11 * (42 * k)) := by rw [← pow_mul]
    have hp2 : 15 ^ (m - 11 * (42 * k)) ≤ 16 ^ (m - 11 * (42 * k)) :=
      Nat.pow_le_pow_left (by decide) _
    have hm_split : 11 * (42 * k) + (m - 11 * (42 * k)) = m := by omega
    calc 15 ^ m * 2 ^ (42 * k)
        = (15 ^ (11 * (42 * k)) * 2 ^ (42 * k)) * 15 ^ (m - 11 * (42 * k)) := by
            conv_lhs => rw [← hm_split, pow_add]
            ring
      _ ≤ 16 ^ (11 * (42 * k)) * 16 ^ (m - 11 * (42 * k)) := Nat.mul_le_mul hp1 hp2
      _ = 16 ^ m := by rw [← pow_add, hm_split]
  have hcomb : H.card ^ 28 * 2 ^ (42 * k) ≤ (2 ^ m) ^ 28 := by
    have hpos : 0 < (15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc H.card ^ 28 * 2 ^ (42 * k) * ((15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m)
        = (H.card ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m))) * 16 ^ m * 2 ^ (42 * k) := by ring
      _ ≤ (28 ^ 28) ^ m * 16 ^ m * 2 ^ (42 * k) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h28)
      _ ≤ ((15 ^ (15 * m) * 13 ^ (13 * m)) * (2 ^ m) ^ 28 * 15 ^ m) * 2 ^ (42 * k) :=
            Nat.mul_le_mul_right _ hbase_m
      _ = (2 ^ m) ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) * (15 ^ m * 2 ^ (42 * k)) := by ring
      _ ≤ (2 ^ m) ^ 28 * (15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m :=
            Nat.mul_le_mul_left _ hpow42
      _ = (2 ^ m) ^ 28 * ((15 ^ (15 * m) * 13 ^ (13 * m)) * 16 ^ m) := by ring
  have hexp : 28 * (k / 16 + k + 2) ≤ 42 * k := by omega
  have hpow_final : (2 ^ (k / 16 + k + 2) * H.card) ^ 28 ≤ (2 ^ m) ^ 28 := by
    calc (2 ^ (k / 16 + k + 2) * H.card) ^ 28
        = H.card ^ 28 * 2 ^ (28 * (k / 16 + k + 2)) := by
            rw [mul_pow, ← pow_mul, Nat.mul_comm 28, Nat.mul_comm]
      _ ≤ H.card ^ 28 * 2 ^ (42 * k) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hexp)
      _ ≤ (2 ^ m) ^ 28 := hcomb
  exact nat_le_of_pow_le_pow_left (by decide : 28 ≠ 0) hpow_final

private lemma card_short_tail_bound (m g B : ℕ) (hg : g ≤ m) (hB : 0 < B) :
    (Finset.univ.filter (fun y : Fin m → ZMod 2 => wt y ≤ g)).card * B ^ m ≤
      (B + 1) ^ m * B ^ g := by
  let T : Finset (Fin m → ZMod 2) := Finset.univ.filter (fun y => wt y ≤ g)
  have hsum : T.card * B ^ (m - g) ≤ (B + 1) ^ m := by
    calc T.card * B ^ (m - g)
        = ∑ _y ∈ T, B ^ (m - g) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ y ∈ T, 1 ^ wt y * B ^ (m - wt y) := by
            refine Finset.sum_le_sum (fun y hy => ?_)
            rw [one_pow, one_mul]
            have hwy := (Finset.mem_filter.mp hy).2
            exact Nat.pow_le_pow_right hB (by omega)
      _ ≤ ∑ y : Fin m → ZMod 2, 1 ^ wt y * B ^ (m - wt y) :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ T)
      _ = (1 + B) ^ m := sum_pow_wt m 1 B
      _ = (B + 1) ^ m := by rw [Nat.add_comm]
  have hm_eq : m - g + g = m := by omega
  calc T.card * B ^ m
      = (T.card * B ^ (m - g)) * B ^ g := by rw [Nat.mul_assoc, ← pow_add, hm_eq]
    _ ≤ (B + 1) ^ m * B ^ g := Nat.mul_le_mul_right _ hsum

private lemma card_short_product_bound (k m : ℕ) (hk : 64 ≤ k) (hm_lo : 512 * k ≤ m) (hm_hi : m ≤ 1024 * k) :
    let g := k / 32
    2 ^ (k / 16 + 2) *
      (Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)).card *
      (Finset.univ.filter (fun z : Fin k → ZMod 2 => wt z ≤ g)).card ≤ 2 ^ k := by
  intro g
  let NS := (Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)).card
  let Tm := (Finset.univ.filter (fun y : Fin m → ZMod 2 => wt y ≤ g)).card
  let Tk := (Finset.univ.filter (fun z : Fin k → ZMod 2 => wt z ≤ g)).card
  have hNS_le : NS ≤ Tm := by
    apply Finset.card_le_card_of_injOn (fun (S : Finset (Fin m)) (j : Fin m) => if j ∈ S then (1 : ZMod 2) else 0)
    · intro S hS
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      have hwt_eq : wt (fun j : Fin m => if j ∈ S then (1 : ZMod 2) else 0) = S.card := by
        unfold wt
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : j ∈ S
        · simp [hj]
        · simp [hj]
      rw [hwt_eq]
      exact hS.2
    · intro S1 _ S2 _ heq
      ext j
      have hj := congrFun heq j
      dsimp only at hj
      by_cases h1 : j ∈ S1 <;> by_cases h2 : j ∈ S2 <;> simp [h1, h2] at hj ⊢
  have hTm_step : Tm ^ 16 ≤ 2 ^ (4 * k + 208 * g) := by
    have h1 := card_short_tail_bound m g 8192 (by omega) (by decide)
    have h16 := Nat.pow_le_pow_left h1 16
    have h8193 : 8193 ^ 4096 ≤ 2 * 8192 ^ 4096 := by
      simpa only [show 2 * 4096 + 1 = 8193 from rfl, show 2 * 4096 = 8192 from rfl] using
        pow_half_le_two_mul 4096 (by decide)
    have hm16 : 16 * m ≤ 4096 * (4 * k) := by omega
    have h8193_m : 8193 ^ (16 * m) ≤ 2 ^ (4 * k) * 8192 ^ (16 * m) := by
      have hpos : 0 < 8192 ^ (4096 * (4 * k) - 16 * m) := by positivity
      refine Nat.le_of_mul_le_mul_right ?_ hpos
      have hsplit : 16 * m + (4096 * (4 * k) - 16 * m) = 4096 * (4 * k) := by omega
      calc 8193 ^ (16 * m) * 8192 ^ (4096 * (4 * k) - 16 * m)
          ≤ 8193 ^ (16 * m) * 8193 ^ (4096 * (4 * k) - 16 * m) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
        _ = (8193 ^ 4096) ^ (4 * k) := by rw [← pow_add, hsplit, pow_mul]
        _ ≤ (2 * 8192 ^ 4096) ^ (4 * k) := Nat.pow_le_pow_left h8193 (4 * k)
        _ = 2 ^ (4 * k) * 8192 ^ (4096 * (4 * k)) := by rw [mul_pow, ← pow_mul]
        _ = 2 ^ (4 * k) * 8192 ^ (16 * m) * 8192 ^ (4096 * (4 * k) - 16 * m) := by
              rw [Nat.mul_assoc, ← pow_add, hsplit]
    have h8192_pow : (8192 ^ g) ^ 16 = 2 ^ (208 * g) := by
      have h8 : (8192 : ℕ) = 2 ^ 13 := by norm_num
      rw [h8, ← pow_mul, ← pow_mul]
      congr 1
      omega
    have hpos : 0 < 8192 ^ (16 * m) := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Tm ^ 16 * 8192 ^ (16 * m)
        = (Tm * 8192 ^ m) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 16]
      _ ≤ (8193 ^ m * 8192 ^ g) ^ 16 := h16
      _ = 8193 ^ (16 * m) * (8192 ^ g) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm m 16]
      _ ≤ (2 ^ (4 * k) * 8192 ^ (16 * m)) * 2 ^ (208 * g) := by
            rw [h8192_pow]; exact Nat.mul_le_mul_right _ h8193_m
      _ = 2 ^ (4 * k + 208 * g) * 8192 ^ (16 * m) := by rw [pow_add]; ring
  have hTk_step : Tk ^ 16 ≤ 2 ^ (k + 80 * g) := by
    have h1 := card_short_tail_bound k g 32 (by omega) (by decide)
    have h16 := Nat.pow_le_pow_left h1 16
    have h33 : 33 ^ 16 ≤ 2 * 32 ^ 16 := by
      simpa only [show 2 * 16 + 1 = 33 from rfl, show 2 * 16 = 32 from rfl] using
        pow_half_le_two_mul 16 (by decide)
    have h33_k : 33 ^ (16 * k) ≤ 2 ^ k * 32 ^ (16 * k) := by
      calc 33 ^ (16 * k)
          = (33 ^ 16) ^ k := by rw [pow_mul]
        _ ≤ (2 * 32 ^ 16) ^ k := Nat.pow_le_pow_left h33 k
        _ = 2 ^ k * 32 ^ (16 * k) := by rw [mul_pow, ← pow_mul]
    have h32_pow : (32 ^ g) ^ 16 = 2 ^ (80 * g) := by
      have h32 : (32 : ℕ) = 2 ^ 5 := by norm_num
      rw [h32, ← pow_mul, ← pow_mul]
      congr 1
      omega
    have hpos : 0 < 32 ^ (16 * k) := by positivity
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc Tk ^ 16 * 32 ^ (16 * k)
        = (Tk * 32 ^ k) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 16]
      _ ≤ (33 ^ k * 32 ^ g) ^ 16 := h16
      _ = 33 ^ (16 * k) * (32 ^ g) ^ 16 := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 16]
      _ ≤ (2 ^ k * 32 ^ (16 * k)) * 2 ^ (80 * g) := by
            rw [h32_pow]; exact Nat.mul_le_mul_right _ h33_k
      _ = 2 ^ (k + 80 * g) * 32 ^ (16 * k) := by rw [pow_add]; ring
  have hpow16 : (2 ^ (k / 16 + 2) * NS * Tk) ^ 16 ≤ (2 ^ k) ^ 16 := by
    have hNS16 : NS ^ 16 ≤ 2 ^ (4 * k + 208 * g) :=
      le_trans (Nat.pow_le_pow_left hNS_le 16) hTm_step
    have hexp : 16 * (k / 16 + 2) + (4 * k + 208 * g) + (k + 80 * g) ≤ 16 * k := by omega
    calc (2 ^ (k / 16 + 2) * NS * Tk) ^ 16
        = 2 ^ (16 * (k / 16 + 2)) * NS ^ 16 * Tk ^ 16 := by
            rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm (k / 16 + 2) 16]
      _ ≤ 2 ^ (16 * (k / 16 + 2)) * 2 ^ (4 * k + 208 * g) * 2 ^ (k + 80 * g) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ hNS16) hTk_step
      _ = 2 ^ (16 * (k / 16 + 2) + (4 * k + 208 * g) + (k + 80 * g)) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (16 * k) := Nat.pow_le_pow_right (by decide) hexp
      _ = (2 ^ k) ^ 16 := by rw [Nat.mul_comm 16 k, pow_mul]
  exact nat_le_of_pow_le_pow_left (by decide : 16 ≠ 0) hpow16

end PEqualNP.Outside.L_lib_788_aux

open PEqualNP.Outside.L_lib_788_aux

theorem PEqualNP.Outside.L_lib_788 :
    (∀ k m : ℕ, 64 ≤ k → 512*k ≤ m → m ≤ 1024*k →
  let F := ZMod 2
  let V := Fin k → F
  let Seed := Fin (2^(k+m-1))
  let win := fun (s : Seed) (j : Fin m) (i : Fin k) =>
    if s.val.testBit (j.val+i.val) then (1 : F) else 0
  let g := k/32
  let good := fun s : Seed =>
    (∀ a : V, a ≠ 0 →
      let w := ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (∑ i : Fin k, a i * win s j i) = 1)).card
      13*m ≤ 28*w ∧ 28*w ≤ 15*m) ∧
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ g →
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i =>
        (∑ j ∈ S, win s j i) = 1)).card
      g < w ∧ w+g < k)
  2^(k/16)*((Finset.univ : Finset Seed).filter (fun s => ¬ good s)).card ≤ 2^(k+m-1)) := by
  intro k m hk hm_lo hm_hi
  dsimp only
  let F := ZMod 2
  let V := Fin k → F
  let N := k + m - 1
  let Seed := Fin (2 ^ N)
  let win : Seed → Fin m → Fin k → F := fun s j i =>
    if s.val.testBit (j.val + i.val) then (1 : F) else 0
  let g := k / 32
  let toBits : Seed → (Fin N → F) := fun s t =>
    if s.val.testBit t.val then (1 : F) else 0
  have htoBits_bij : Function.Bijective toBits := card_toBits_bijective N
  let good := fun s : Seed =>
    (∀ a : V, a ≠ 0 →
      let w := ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (∑ i : Fin k, a i * win s j i) = 1)).card
      13 * m ≤ 28 * w ∧ 28 * w ≤ 15 * m) ∧
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ g →
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i =>
        (∑ j ∈ S, win s j i) = 1)).card
      g < w ∧ w + g < k)
  let badA : V → Finset Seed := fun a =>
    Finset.univ.filter (fun s =>
      let w := ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (∑ i : Fin k, a i * win s j i) = 1)).card
      ¬ (13 * m ≤ 28 * w ∧ 28 * w ≤ 15 * m))
  let badS : Finset (Fin m) → Finset Seed := fun S =>
    Finset.univ.filter (fun s =>
      let w := ((Finset.univ : Finset (Fin k)).filter (fun i =>
        (∑ j ∈ S, win s j i) = 1)).card
      ¬ (g < w ∧ w + g < k))
  let Aset : Finset V := Finset.univ.filter (fun a : V => a ≠ 0)
  let Sset : Finset (Finset (Fin m)) := Finset.univ.filter (fun S : Finset (Fin m) => 0 < S.card ∧ S.card ≤ g)
  have hsub : Finset.univ.filter (fun s : Seed => ¬ good s) ⊆
      Aset.biUnion badA ∪ Sset.biUnion badS := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, good, not_and_or,
      not_forall] at hs
    rw [Finset.mem_union]
    rcases hs with ⟨a, ha, hbad⟩ | ⟨S, hS1, hS2, hbad⟩
    · left
      rw [Finset.mem_biUnion]
      exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ s, not_and_or.mpr hbad⟩⟩
    · right
      rw [Finset.mem_biUnion]
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS1, hS2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ s, not_and_or.mpr hbad⟩⟩
  let Hbias : Finset (Fin m → F) := Finset.univ.filter (fun y => 15 * m < 28 * wt y)
  let Lbias : Finset (Fin m → F) := Finset.univ.filter (fun y => 28 * wt y < 13 * m)
  have hLbias_eq : Lbias.card = Hbias.card := by
    apply Finset.card_bij (fun (y : Fin m → F) _ j => y j + 1)
    · intro y hy
      simp only [Lbias, Hbias, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [wt_add_one y]
      have := wt_le y
      omega
    · intro y1 _ y2 _ heq
      funext j
      have hj := congrFun heq j
      exact add_right_cancel hj
    · intro y hy
      refine ⟨fun j => y j + 1, ?_, ?_⟩
      · simp only [Lbias, Hbias, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        rw [wt_add_one y]
        have := wt_le y
        omega
      · funext j
        dsimp only
        rw [add_assoc, zmod2_add_self, add_zero]
  have hbadA_card : ∀ a ∈ Aset, (badA a).card ≤ 2 * Hbias.card * 2 ^ (k - 1) := by
    intro a ha
    have ha0 : a ≠ 0 := (Finset.mem_filter.mp ha).2
    let φA : Seed → (Fin m → F) := fun s j => ∑ i : Fin k, a i * win s j i
    have hmaps : ∀ s ∈ badA a, φA s ∈ Lbias ∪ Hbias := by
      intro s hs
      have hbad := (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_union, Lbias, Hbias, Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ (13 * m ≤ 28 * wt (φA s) ∧ 28 * wt (φA s) ≤ 15 * m) at hbad
      omega
    have hfiber : ∀ y : Fin m → F, ((badA a).filter (fun s => φA s = y)).card ≤ 2 ^ (k - 1) := by
      intro y
      have hle1 : ((badA a).filter (fun s => φA s = y)).card ≤
          (Finset.univ.filter (fun s : Seed => φA s = y)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      have heq2 : (Finset.univ.filter (fun s : Seed => φA s = y)).card =
          (Finset.univ.filter (fun v : Fin N → F =>
            (fun j : Fin m => ∑ i : Fin k, a i * v ⟨j.val + i.val, by omega⟩) = y)).card := by
        apply Finset.card_bij (fun s _ => toBits s)
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact hs
        · intro s1 _ s2 _ h; exact htoBits_bij.1 h
        · intro v hv
          rcases htoBits_bij.2 v with ⟨s, hs⟩
          refine ⟨s, ?_, hs⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          rw [← hs] at hv
          exact hv
      rw [heq2] at hle1
      have hfib := card_shift_linear_fiber k m (by omega) (by omega) a ha0 y
      rw [hfib] at hle1
      exact hle1
    calc (badA a).card
        = ∑ y ∈ Lbias ∪ Hbias, ((badA a).filter (fun s => φA s = y)).card := by
            rw [Finset.card_eq_sum_card_fiberwise hmaps]
      _ ≤ ∑ _y ∈ Lbias ∪ Hbias, 2 ^ (k - 1) := Finset.sum_le_sum (fun y _ => hfiber y)
      _ = (Lbias ∪ Hbias).card * 2 ^ (k - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (Lbias.card + Hbias.card) * 2 ^ (k - 1) :=
            Nat.mul_le_mul_right _ (Finset.card_union_le Lbias Hbias)
      _ = 2 * Hbias.card * 2 ^ (k - 1) := by rw [hLbias_eq]; ring
  let TkSet : Finset (Fin k → F) := Finset.univ.filter (fun z => wt z ≤ g)
  let HkSet : Finset (Fin k → F) := Finset.univ.filter (fun z => k ≤ wt z + g)
  have hHk_eq : HkSet.card = TkSet.card := by
    apply Finset.card_bij (fun (z : Fin k → F) _ i => z i + 1)
    · intro z hz
      simp only [HkSet, TkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      rw [wt_add_one z]
      have := wt_le z
      omega
    · intro z1 _ z2 _ heq
      funext i
      exact add_right_cancel (congrFun heq i)
    · intro z hz
      refine ⟨fun i => z i + 1, ?_, ?_⟩
      · simp only [HkSet, TkSet, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [wt_add_one z]
        have := wt_le z
        omega
      · funext i
        dsimp only
        rw [add_assoc, zmod2_add_self, add_zero]
  have hbadS_card : ∀ S ∈ Sset, (badS S).card ≤ 2 * TkSet.card * 2 ^ (m - 1) := by
    intro S hS
    have hSpos : 0 < S.card := (Finset.mem_filter.mp hS).2.1
    let cS : Fin m → F := fun j => if j ∈ S then 1 else 0
    have hcS0 : cS ≠ 0 := by
      intro hc
      rcases Finset.card_pos.mp hSpos with ⟨j, hj⟩
      have h0 := congrFun hc j
      simp [cS, hj] at h0
    let φS : Seed → (Fin k → F) := fun s i => ∑ j ∈ S, win s j i
    have hmaps : ∀ s ∈ badS S, φS s ∈ TkSet ∪ HkSet := by
      intro s hs
      have hbad := (Finset.mem_filter.mp hs).2
      simp only [Finset.mem_union, TkSet, HkSet, Finset.mem_filter, Finset.mem_univ, true_and]
      change ¬ (g < wt (φS s) ∧ wt (φS s) + g < k) at hbad
      omega
    have hfiber : ∀ z : Fin k → F, ((badS S).filter (fun s => φS s = z)).card ≤ 2 ^ (m - 1) := by
      intro z
      have hle1 : ((badS S).filter (fun s => φS s = z)).card ≤
          (Finset.univ.filter (fun s : Seed => φS s = z)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      have hN_comm : m + k - 1 = N := by omega
      have heq2 : (Finset.univ.filter (fun s : Seed => φS s = z)).card =
          (Finset.univ.filter (fun v : Fin (m + k - 1) → F =>
            (fun i : Fin k => ∑ j : Fin m, cS j * v ⟨i.val + j.val, by omega⟩) = z)).card := by
        apply Finset.card_bij (fun s _ t => toBits s ⟨t.val, by omega⟩)
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          rw [← hs]
          funext i
          dsimp only [φS, cS, win, toBits]
          have hsum_eq : ∑ j : Fin m, (if j ∈ S then (1 : F) else 0) *
              (if s.val.testBit (i.val + j.val) then (1 : F) else 0) =
              ∑ j ∈ S, (if s.val.testBit (j.val + i.val) then (1 : F) else 0) := by
            rw [← Finset.sum_subset (Finset.subset_univ S)]
            · refine Finset.sum_congr rfl (fun j hj => ?_)
              simp only [hj, ↓reduceIte, one_mul, Nat.add_comm i.val j.val]
            · intro j _ hj
              simp only [hj, ↓reduceIte, zero_mul]
          exact hsum_eq
        · intro s1 _ s2 _ h
          apply htoBits_bij.1
          funext t
          exact congrFun h ⟨t.val, by omega⟩
        · intro v hv
          rcases htoBits_bij.2 (fun t : Fin N => v ⟨t.val, by omega⟩) with ⟨s, hs⟩
          refine ⟨s, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
            rw [← hv]
            funext i
            dsimp only [φS, cS, win]
            have hsum_eq : ∑ j ∈ S, (if s.val.testBit (j.val + i.val) then (1 : F) else 0) =
                ∑ j : Fin m, (if j ∈ S then (1 : F) else 0) * v ⟨i.val + j.val, by omega⟩ := by
              rw [← Finset.sum_subset (Finset.subset_univ S)]
              · refine Finset.sum_congr rfl (fun j hj => ?_)
                have hbit := congrFun hs ⟨j.val + i.val, by omega⟩
                dsimp only [toBits] at hbit
                have hidx : (⟨j.val + i.val, by omega⟩ : Fin (m + k - 1)) = ⟨i.val + j.val, by omega⟩ :=
                  Fin.ext (Nat.add_comm j.val i.val)
                rw [hidx] at hbit
                simp only [hj, ↓reduceIte, one_mul, hbit]
              · intro j _ hj
                simp only [hj, ↓reduceIte, zero_mul]
            exact hsum_eq
          · funext t
            exact congrFun hs ⟨t.val, by omega⟩
      rw [heq2] at hle1
      have hfib := card_shift_linear_fiber m k (by omega) (by omega) cS hcS0 z
      rw [hfib] at hle1
      exact hle1
    calc (badS S).card
        = ∑ z ∈ TkSet ∪ HkSet, ((badS S).filter (fun s => φS s = z)).card := by
            rw [Finset.card_eq_sum_card_fiberwise hmaps]
      _ ≤ ∑ _z ∈ TkSet ∪ HkSet, 2 ^ (m - 1) := Finset.sum_le_sum (fun z _ => hfiber z)
      _ = (TkSet ∪ HkSet).card * 2 ^ (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (TkSet.card + HkSet.card) * 2 ^ (m - 1) :=
            Nat.mul_le_mul_right _ (Finset.card_union_le TkSet HkSet)
      _ = 2 * TkSet.card * 2 ^ (m - 1) := by rw [hHk_eq]; ring
  have hA_total : (Aset.biUnion badA).card ≤ 2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) := by
    calc (Aset.biUnion badA).card
        ≤ ∑ a ∈ Aset, (badA a).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Aset, (2 * Hbias.card * 2 ^ (k - 1)) := Finset.sum_le_sum hbadA_card
      _ = Aset.card * (2 * Hbias.card * 2 ^ (k - 1)) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) := by
            refine Nat.mul_le_mul_right _ ?_
            calc Aset.card ≤ (Finset.univ : Finset V).card := Finset.card_filter_le _ _
              _ = 2 ^ k := by simp [V, F, Fintype.card_fin, ZMod.card]
  have hS_total : (Sset.biUnion badS).card ≤ Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) := by
    calc (Sset.biUnion badS).card
        ≤ ∑ S ∈ Sset, (badS S).card := Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Sset, (2 * TkSet.card * 2 ^ (m - 1)) := Finset.sum_le_sum hbadS_card
      _ = Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) := by rw [Finset.sum_const, smul_eq_mul]
  have htotal : (Finset.univ.filter (fun s : Seed => ¬ good s)).card ≤
      2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) + Sset.card * (2 * TkSet.card * 2 ^ (m - 1)) :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add hA_total hS_total))
  have hboundA : 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)))) ≤ 2 ^ (k + m - 1) := by
    have hb := card_bias_high_bound k m hk hm_lo
    have hpow_eq : 2 ^ m * 2 ^ (k - 1) = 2 ^ (k + m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1))))
        = (2 ^ (k / 16 + k + 2) * Hbias.card) * 2 ^ (k - 1) := by
            simp only [pow_add]
            ring
      _ ≤ 2 ^ m * 2 ^ (k - 1) := Nat.mul_le_mul_right _ hb
      _ = 2 ^ (k + m - 1) := hpow_eq
  have hboundS : 2 * (2 ^ (k / 16) * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1)))) ≤ 2 ^ (k + m - 1) := by
    have hs := card_short_product_bound k m hk hm_lo hm_hi
    have hpow_eq : 2 ^ k * 2 ^ (m - 1) = 2 ^ (k + m - 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 * (2 ^ (k / 16) * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1))))
        = (2 ^ (k / 16 + 2) * Sset.card * TkSet.card) * 2 ^ (m - 1) := by
            simp only [pow_add]
            ring
      _ ≤ 2 ^ k * 2 ^ (m - 1) := Nat.mul_le_mul_right _ hs
      _ = 2 ^ (k + m - 1) := hpow_eq
  have h2mul : 2 * (2 ^ (k / 16) * (Finset.univ.filter (fun s : Seed => ¬ good s)).card) ≤
      2 * 2 ^ (k + m - 1) := by
    calc 2 * (2 ^ (k / 16) * (Finset.univ.filter (fun s : Seed => ¬ good s)).card)
        ≤ 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)) +
            Sset.card * (2 * TkSet.card * 2 ^ (m - 1)))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ htotal)
      _ = 2 * (2 ^ (k / 16) * (2 ^ k * (2 * Hbias.card * 2 ^ (k - 1)))) +
          2 * (2 ^ (k / 16) * (Sset.card * (2 * TkSet.card * 2 ^ (m - 1)))) := by ring
      _ ≤ 2 ^ (k + m - 1) + 2 ^ (k + m - 1) := Nat.add_le_add hboundA hboundS
      _ = 2 * 2 ^ (k + m - 1) := by ring
  exact Nat.le_of_mul_le_mul_left h2mul (by decide)
