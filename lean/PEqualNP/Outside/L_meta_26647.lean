import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26647_aux

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


theorem good_exists :
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


open PEqualNP.CircuitLowerBounds

def wr (gs : List Gate) (x : List Bool) : List Bool := Circuit.wires ⟨gs, 0⟩ x

lemma wr_nil (x : List Bool) : wr [] x = x := rfl

lemma wr_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wr (gs ++ [g]) x = wr gs x ++ [g.op.eval (g.inputs.map fun i => (wr gs x).getD i false)] := by
  simp [wr, Circuit.wires, List.foldl_append]

lemma wr_length (gs : List Gate) (x : List Bool) : (wr gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wr_nil]
  | append_singleton gs g ih => rw [wr_snoc]; simp [ih]; omega

lemma wr_prefix (gs hs : List Gate) (x : List Bool) : ∃ ys, wr (gs ++ hs) x = wr gs x ++ ys := by
  induction hs using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton hs g ih =>
    obtain ⟨ys, h⟩ := ih
    refine ⟨ys ++ [g.op.eval (g.inputs.map fun i => (wr (gs ++ hs) x).getD i false)], ?_⟩
    have e : gs ++ (hs ++ [g]) = (gs ++ hs) ++ [g] := (List.append_assoc _ _ _).symm
    rw [e, wr_snoc, h]
    simp

lemma wr_getD_old (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (wr (gs ++ hs) x).getD i false = (wr gs x).getD i false := by
  obtain ⟨ys, h⟩ := wr_prefix gs hs x
  have hi' : i < (wr gs x).length := by rw [wr_length]; exact hi
  rw [h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi']

lemma wr_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (wr gs x).getD i false = x.getD i false := by
  have := wr_getD_old [] gs x i (by simpa using hi)
  simpa [wr_nil] using this

lemma wr_new (gs : List Gate) (g : Gate) (x : List Bool) :
    (wr (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wr gs x).getD i false) := by
  rw [wr_snoc]
  have : (wr gs x).length = x.length + gs.length := wr_length gs x
  simp [List.getD_eq_getElem?_getD, this]

lemma wr_new' (gs : List Gate) (g : Gate) (x : List Bool) (i : ℕ) (hi : i = x.length + gs.length) :
    (wr (gs ++ [g]) x).getD i false =
      g.op.eval (g.inputs.map fun i => (wr gs x).getD i false) := by
  subst hi; exact wr_new gs g x

def Shape (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def Good (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (∀ i ∈ gs[j].inputs, i < n + j) ∧ Shape gs[j]

lemma good_nil (n : ℕ) : Good n [] := fun j hj => by simp at hj

lemma good_snoc {n : ℕ} {gs : List Gate} {g : Gate} (h : Good n gs)
    (hg : ∀ i ∈ g.inputs, i < n + gs.length) (hs : Shape g) : Good n (gs ++ [g]) := by
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < gs.length
  · have := h j hlt
    simpa [List.getElem_append_left hlt] using this
  · have : j = gs.length := by omega
    subst this
    simpa [hs] using hg


lemma mux_step (n : ℕ) (gs : List Gate) (hgs : Good n gs) (s ns : ℕ)
    (hs : s < n + gs.length) (hns : ns < n + gs.length)
    (hsem : ∀ x : List Bool, x.length = n →
      (wr gs x).getD ns false = !((wr gs x).getD s false))
    (src0 src1 : ℕ → ℕ) (c : ℕ) (h0 : ∀ p < c, src0 p < n + gs.length)
    (h1 : ∀ p < c, src1 p < n + gs.length) :
    ∃ (hs' : List Gate) (idx : ℕ → ℕ), hs'.length = 3 * c ∧ Good n (gs ++ hs') ∧
      (∀ p < c, idx p < n + (gs ++ hs').length) ∧
      ∀ x : List Bool, x.length = n → ∀ p < c, (wr (gs ++ hs') x).getD (idx p) false =
        if (wr gs x).getD s false then (wr gs x).getD (src1 p) false
        else (wr gs x).getD (src0 p) false := by
  induction c with
  | zero => exact ⟨[], fun _ => 0, rfl, by simpa using hgs, by simp, by intros; omega⟩
  | succ c ih =>
    obtain ⟨hs', idx, hlen, hgood, hidx, hval⟩ :=
      ih (fun p hp => h0 p (by omega)) (fun p hp => h1 p (by omega))
    have hL : (gs ++ hs').length = gs.length + 3 * c := by simp [hlen]
    refine ⟨hs' ++ [⟨.and, [src0 c, ns]⟩, ⟨.and, [src1 c, s]⟩,
      ⟨.or, [n + (gs ++ hs').length, n + (gs ++ hs').length + 1]⟩],
      Function.update idx c (n + (gs ++ hs').length + 2), ?_, ?_, ?_, ?_⟩
    · simp [hlen]; ring
    · have e : gs ++ (hs' ++ [(⟨.and, [src0 c, ns]⟩ : Gate), ⟨.and, [src1 c, s]⟩,
          ⟨.or, [n + (gs ++ hs').length, n + (gs ++ hs').length + 1]⟩]) =
          (((gs ++ hs') ++ [(⟨.and, [src0 c, ns]⟩ : Gate)]) ++ [(⟨.and, [src1 c, s]⟩ : Gate)]) ++
          [(⟨.or, [n + (gs ++ hs').length, n + (gs ++ hs').length + 1]⟩ : Gate)] := by
        simp
      rw [e]
      have h0c := h0 c (by omega)
      have h1c := h1 c (by omega)
      refine good_snoc (good_snoc (good_snoc hgood ?_ ?_) ?_ ?_) ?_ ?_
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> omega
      · simp [Shape]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega
      · simp [Shape]
      · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega
      · simp [Shape]
    · intro p hp
      by_cases hpc : p = c
      · subst hpc; simp; omega
      · rw [Function.update_of_ne hpc]
        have := hidx p (by omega)
        simp at this ⊢; omega
    · intro x hx p hp
      subst hx
      have hold : ∀ i, i < x.length + gs.length →
          (wr (gs ++ hs') x).getD i false = (wr gs x).getD i false :=
        fun i hi => wr_getD_old gs hs' x i hi
      have eG : gs ++ (hs' ++ [(⟨.and, [src0 c, ns]⟩ : Gate), ⟨.and, [src1 c, s]⟩,
          ⟨.or, [x.length + (gs ++ hs').length, x.length + (gs ++ hs').length + 1]⟩]) =
          (((gs ++ hs') ++ [(⟨.and, [src0 c, ns]⟩ : Gate)]) ++ [(⟨.and, [src1 c, s]⟩ : Gate)]) ++
          [(⟨.or, [x.length + (gs ++ hs').length, x.length + (gs ++ hs').length + 1]⟩ : Gate)] := by
        simp
      by_cases hpc : p = c
      · subst hpc
        rw [eG]
        have h0c := h0 p (by omega)
        have h1c := h1 p (by omega)
        rw [Function.update_self]
        set G1 := gs ++ hs' with hG1
        have hl : G1.length = gs.length + 3 * p := hL
        rw [wr_new' (G1 ++ [(⟨.and, [src0 p, ns]⟩ : Gate)] ++ [(⟨.and, [src1 p, s]⟩ : Gate)]) _ x
          (x.length + G1.length + 2) (by simp; ring)]
        have q1 : (wr (G1 ++ [(⟨.and, [src0 p, ns]⟩ : Gate)] ++ [(⟨.and, [src1 p, s]⟩ : Gate)]) x).getD
            (x.length + G1.length) false =
            ((wr gs x).getD (src0 p) false && !((wr gs x).getD s false)) := by
          rw [wr_getD_old _ _ x _ (by simp)]
          rw [wr_new' G1 _ x _ rfl]
          have e1 := hold _ h0c
          have e2 := hold _ hns
          have e3 := hsem x rfl
          have e4 := hold _ hs
          simp only [List.map, GateOp.eval, e1, e2, e3, e4]
          simp
        have q2 : (wr (G1 ++ [(⟨.and, [src0 p, ns]⟩ : Gate)] ++ [(⟨.and, [src1 p, s]⟩ : Gate)]) x).getD
            (x.length + G1.length + 1) false =
            ((wr gs x).getD (src1 p) false && (wr gs x).getD s false) := by
          rw [wr_new' (G1 ++ [(⟨.and, [src0 p, ns]⟩ : Gate)]) _ x _ (by simp; ring)]
          simp only [List.map, GateOp.eval]
          rw [wr_getD_old G1 _ x _ (by omega), wr_getD_old G1 _ x _ (by omega)]
          have e1 := hold _ h1c
          have e4 := hold _ hs
          simp only [e1, e4]
          simp
        simp only [List.map, GateOp.eval, q1, q2]
        cases hS : (wr gs x).getD s false <;> simp
      · rw [Function.update_of_ne hpc]
        have hv := hval x rfl p (by omega)
        have hi := hidx p (by omega)
        rw [← List.append_assoc]
        exact (wr_getD_old (gs ++ hs') _ x _ (by omega)).trans hv

def Hh (k t : ℕ) (x : List Bool) : ℕ → ℕ
  | 0 => 0
  | u + 1 => Hh k t x u + if x.getD (k + (t - u - 1)) false then 2 ^ (t - u - 1) else 0

lemma layers_base (k t : ℕ) (hk : 1 ≤ k) (f : ℕ → Bool) :
    ∃ (gs : List Gate) (idx : ℕ → ℕ),
      Good (k + t) gs ∧ gs.length = 3 ∧
      (∀ p, idx p < k + t + gs.length) ∧
      ∀ x : List Bool, x.length = k + t → ∀ p, (wr gs x).getD (idx p) false = f p := by
  refine ⟨([] ++ [(⟨.not, [0]⟩ : Gate)]) ++ [(⟨.and, [0, k + t]⟩ : Gate)] ++
    [(⟨.or, [0, k + t]⟩ : Gate)], fun p => if f p then k + t + 2 else k + t + 1, ?_, by simp, ?_, ?_⟩
  · refine good_snoc (good_snoc (good_snoc (good_nil _) ?_ ?_) ?_ ?_) ?_ ?_
    · intro i hi; simp at hi; subst hi; omega
    · simp [Shape]
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega
    · simp [Shape]
    · intro i hi; simp at hi; rcases hi with rfl | rfl <;> simp <;> omega
    · simp [Shape]
  · intro p; simp; split_ifs <;> omega
  · intro x hx p
    have h0 : 0 < x.length := by omega
    have a0 : (wr [] x).getD 0 false = x.getD 0 false := by rw [wr_nil]
    have w1 : (wr ([] ++ [(⟨.not, [0]⟩ : Gate)]) x).getD (k + t) false = !(x.getD 0 false) := by
      rw [wr_new' [] _ x _ (by simp [hx])]
      simp [GateOp.eval, wr_nil]
    have w2 : (wr (([] ++ [(⟨.not, [0]⟩ : Gate)]) ++ [(⟨.and, [0, k + t]⟩ : Gate)]) x).getD
        (k + t + 1) false = false := by
      rw [wr_new' _ _ x _ (by simp [hx])]
      simp only [List.map, GateOp.eval]
      rw [w1, wr_getD_old [] _ x 0 (by simpa using h0)]
      simp [wr_nil]
    have w3 : (wr ((([] ++ [(⟨.not, [0]⟩ : Gate)]) ++ [(⟨.and, [0, k + t]⟩ : Gate)]) ++
        [(⟨.or, [0, k + t]⟩ : Gate)]) x).getD (k + t + 2) false = true := by
      rw [wr_new' _ _ x _ (by simp [hx])]
      simp only [List.map, GateOp.eval]
      rw [wr_getD_old _ [(⟨.and, [0, k + t]⟩ : Gate)] x 0 (by simp),
        wr_getD_old _ [(⟨.and, [0, k + t]⟩ : Gate)] x (k + t) (by simp [hx]),
        w1, wr_getD_old [] _ x 0 (by simpa using h0)]
      simp [wr_nil]
    have w2' : (wr ((([] ++ [(⟨.not, [0]⟩ : Gate)]) ++ [(⟨.and, [0, k + t]⟩ : Gate)]) ++
        [(⟨.or, [0, k + t]⟩ : Gate)]) x).getD (k + t + 1) false = false := by
      rw [wr_getD_old _ _ x _ (by simp [hx])]; exact w2
    simp only
    split_ifs with hf
    · rw [w3, hf]
    · rw [w2']; simpa using hf

lemma layers (k t : ℕ) (hk : 1 ≤ k) (f : ℕ → Bool) : ∀ u ≤ t,
    ∃ (gs : List Gate) (idx : ℕ → ℕ),
      Good (k + t) gs ∧ gs.length + 3 * 2 ^ (t - u) ≤ 3 + 3 * k * u + 3 * 2 ^ t ∧
      (∀ p < k + 2 ^ (t - u) - 1, idx p < k + t + gs.length) ∧
      ∀ x : List Bool, x.length = k + t → ∀ p < k + 2 ^ (t - u) - 1,
        (wr gs x).getD (idx p) false = f (Hh k t x u + p) := by
  intro u
  induction u with
  | zero =>
    intro _
    obtain ⟨gs, idx, hg, hl, hi, hv⟩ := layers_base k t hk f
    refine ⟨gs, idx, hg, ?_, fun p _ => hi p, ?_⟩
    · simp [hl]
    · intro x hx p _
      simp only [Hh, zero_add]; exact hv x hx p
  | succ u ih =>
    intro hu
    obtain ⟨gs, idx, hg, hl, hi, hv⟩ := ih (by omega)
    obtain ⟨z, hz⟩ : ∃ z, t - u = z + 1 := ⟨t - u - 1, by omega⟩
    have hz' : t - (u + 1) = z := by omega
    have hzu : t - u - 1 = z := by omega
    rw [hz] at hl hi hv
    have hpz : 2 ^ (z + 1) = 2 * 2 ^ z := by ring
    have hgood1 : Good (k + t) (gs ++ [(⟨.not, [k + z]⟩ : Gate)]) :=
      good_snoc hg (by intro i hi; simp at hi; subst hi; omega) (by simp [Shape])
    have hlen1 : (gs ++ [(⟨.not, [k + z]⟩ : Gate)]).length = gs.length + 1 := by simp
    obtain ⟨hs', idx', hlen', hgood', hidx', hval'⟩ := mux_step (k + t)
      (gs ++ [(⟨.not, [k + z]⟩ : Gate)]) hgood1 (k + z) (k + t + gs.length)
      (by omega) (by omega)
      (by
        intro x hx
        rw [wr_new' gs _ x _ (by omega)]
        simp only [List.map, GateOp.eval, List.headD_cons]
        rw [wr_getD_old gs _ x (k + z) (by omega)])
      idx (fun p => idx (p + 2 ^ z)) (k + 2 ^ z - 1)
      (fun p hp => by have := hi p (by omega); omega)
      (fun p hp => by have := hi (p + 2 ^ z) (by omega); omega)
    refine ⟨(gs ++ [(⟨.not, [k + z]⟩ : Gate)]) ++ hs', idx', hgood', ?_, ?_, ?_⟩
    · rw [hz', List.length_append, hlen1, hlen']
      have : 3 * k * (u + 1) = 3 * k * u + 3 * k := by ring
      have h1 : 1 ≤ 2 ^ z := Nat.one_le_two_pow
      omega
    · rw [hz']; exact hidx'
    · intro x hx p hp
      rw [hz'] at hp
      rw [hval' x hx p hp]
      have hs1 : (wr (gs ++ [(⟨.not, [k + z]⟩ : Gate)]) x).getD (k + z) false = x.getD (k + z) false :=
        wr_input _ x _ (by omega)
      have ho : ∀ q, q < k + t + gs.length →
          (wr (gs ++ [(⟨.not, [k + z]⟩ : Gate)]) x).getD q false = (wr gs x).getD q false :=
        fun q hq => wr_getD_old gs _ x q (by omega)
      have hh : Hh k t x (u + 1) = Hh k t x u + if x.getD (k + z) false then 2 ^ z else 0 := by
        simp only [Hh, hzu]
      rw [hs1, ho _ (by have := hi (p + 2 ^ z) (by omega); omega),
        ho _ (by have := hi p (by omega); omega), hh]
      cases hb : x.getD (k + z) false
      · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        exact hv x hx p (by omega)
      · simp only [↓reduceIte]
        rw [hv x hx (p + 2 ^ z) (by omega)]
        congr 1; ring

lemma add_and (n : ℕ) (gs : List Gate) (hg : Good n gs) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) :
    Good n (gs ++ [(⟨.and, [a, b]⟩ : Gate)]) ∧ ∀ x : List Bool, x.length = n →
      (wr (gs ++ [(⟨.and, [a, b]⟩ : Gate)]) x).getD (n + gs.length) false =
        ((wr gs x).getD a false && (wr gs x).getD b false) := by
  refine ⟨good_snoc hg (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
    (by simp [Shape]), ?_⟩
  intro x hx
  subst hx
  rw [wr_new']
  · simp [GateOp.eval, List.getD_eq_getElem?_getD]
  · rfl

lemma add_or (n : ℕ) (gs : List Gate) (hg : Good n gs) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) :
    Good n (gs ++ [(⟨.or, [a, b]⟩ : Gate)]) ∧ ∀ x : List Bool, x.length = n →
      (wr (gs ++ [(⟨.or, [a, b]⟩ : Gate)]) x).getD (n + gs.length) false =
        ((wr gs x).getD a false || (wr gs x).getD b false) := by
  refine ⟨good_snoc hg (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)
    (by simp [Shape]), ?_⟩
  intro x hx
  subst hx
  rw [wr_new']
  · simp [GateOp.eval, List.getD_eq_getElem?_getD]
  · rfl

lemma add_not (n : ℕ) (gs : List Gate) (hg : Good n gs) (a : ℕ) (ha : a < n + gs.length) :
    Good n (gs ++ [(⟨.not, [a]⟩ : Gate)]) ∧ ∀ x : List Bool, x.length = n →
      (wr (gs ++ [(⟨.not, [a]⟩ : Gate)]) x).getD (n + gs.length) false =
        !((wr gs x).getD a false) := by
  refine ⟨good_snoc hg (by intro i hi; simp at hi; subst hi; assumption)
    (by simp [Shape]), ?_⟩
  intro x hx
  subst hx
  rw [wr_new']
  · simp [GateOp.eval, List.getD_eq_getElem?_getD]
  · rfl

lemma add_xor (n : ℕ) (gs : List Gate) (hg : Good n gs) (a b : ℕ) (ha : a < n + gs.length)
    (hb : b < n + gs.length) :
    ∃ hs : List Gate, hs.length = 4 ∧ Good n (gs ++ hs) ∧ ∀ x : List Bool, x.length = n →
      (wr (gs ++ hs) x).getD (n + gs.length + 3) false =
        xor ((wr gs x).getD a false) ((wr gs x).getD b false) := by
  obtain ⟨g1, v1⟩ := add_or n gs hg a b ha hb
  obtain ⟨g2, v2⟩ := add_and n (gs ++ [(⟨.or, [a, b]⟩ : Gate)]) g1 a b (by simp; omega)
    (by simp; omega)
  obtain ⟨g3, v3⟩ := add_not n (gs ++ [(⟨.or, [a, b]⟩ : Gate)] ++ [(⟨.and, [a, b]⟩ : Gate)]) g2
    (n + gs.length + 1) (by simp; omega)
  obtain ⟨g4, v4⟩ := add_and n (gs ++ [(⟨.or, [a, b]⟩ : Gate)] ++ [(⟨.and, [a, b]⟩ : Gate)] ++
    [(⟨.not, [n + gs.length + 1]⟩ : Gate)]) g3 (n + gs.length) (n + gs.length + 2)
    (by simp) (by simp; omega)
  refine ⟨[(⟨.or, [a, b]⟩ : Gate), ⟨.and, [a, b]⟩, ⟨.not, [n + gs.length + 1]⟩,
    ⟨.and, [n + gs.length, n + gs.length + 2]⟩], rfl, ?_, ?_⟩
  · simpa using g4
  · intro x hx
    have e : gs ++ [(⟨.or, [a, b]⟩ : Gate), ⟨.and, [a, b]⟩, ⟨.not, [n + gs.length + 1]⟩,
        ⟨.and, [n + gs.length, n + gs.length + 2]⟩] =
        gs ++ [(⟨.or, [a, b]⟩ : Gate)] ++ [(⟨.and, [a, b]⟩ : Gate)] ++
          [(⟨.not, [n + gs.length + 1]⟩ : Gate)] ++
          [(⟨.and, [n + gs.length, n + gs.length + 2]⟩ : Gate)] := by simp
    rw [e]
    have q := v4 x hx
    simp only [List.length_append, List.length_singleton, List.length_nil] at q
    have e2 : n + (gs.length + 1 + 1 + 1) = n + gs.length + 3 := by ring
    rw [e2] at q
    rw [q]
    have o1 := v1 x hx
    have o2 := v2 x hx
    have o3 := v3 x hx
    simp only [List.length_append, List.length_singleton, List.length_nil] at o2 o3
    rw [show n + (gs.length + 1) = n + gs.length + 1 by ring] at o2
    rw [show n + (gs.length + 1 + 1) = n + gs.length + 2 by ring] at o3
    have c1 : (wr (gs ++ [(⟨.or, [a, b]⟩ : Gate)] ++ [(⟨.and, [a, b]⟩ : Gate)] ++
        [(⟨.not, [n + gs.length + 1]⟩ : Gate)]) x).getD (n + gs.length) false =
        ((wr gs x).getD a false || (wr gs x).getD b false) := by
      rw [wr_getD_old _ _ x _ (by simp; omega), wr_getD_old _ _ x _ (by simp; omega)]
      exact o1
    have ha1 : (wr (gs ++ [(⟨.or, [a, b]⟩ : Gate)]) x).getD a false = (wr gs x).getD a false :=
      wr_getD_old gs _ x a (by omega)
    have hb1 : (wr (gs ++ [(⟨.or, [a, b]⟩ : Gate)]) x).getD b false = (wr gs x).getD b false :=
      wr_getD_old gs _ x b (by omega)
    rw [c1, o3, o2, ha1, hb1]
    cases (wr gs x).getD a false <;> cases (wr gs x).getD b false <;> simp

def Bsum (b : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | m + 1 => xor (Bsum b m) (b m)

lemma dot_stage (n k : ℕ) (hkn : k ≤ n) (gs : List Gate) (hg : Good n gs) (idx : ℕ → ℕ)
    (hi : ∀ p < k, idx p < n + gs.length) (g : List Bool → ℕ → Bool)
    (hv : ∀ x : List Bool, x.length = n → ∀ p < k, (wr gs x).getD (idx p) false = g x p) :
    ∀ m, m + 1 ≤ k → ∃ (hs : List Gate) (out : ℕ), hs.length ≤ 5 * (m + 1) ∧
      Good n (gs ++ hs) ∧ out < n + (gs ++ hs).length ∧
      ∀ x : List Bool, x.length = n → (wr (gs ++ hs) x).getD out false =
        Bsum (fun p => x.getD p false && g x p) (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro hm
    obtain ⟨g1, v1⟩ := add_and n gs hg 0 (idx 0) (by omega) (hi 0 (by omega))
    refine ⟨[(⟨.and, [0, idx 0]⟩ : Gate)], n + gs.length, by simp, g1, by simp, ?_⟩
    intro x hx
    rw [v1 x hx, wr_input _ x 0 (by omega), hv x hx 0 (by omega)]
    simp [Bsum]
  | succ m ih =>
    intro hm
    obtain ⟨hs, out, hl, hgood, hout, hval⟩ := ih (by omega)
    have hL : (gs ++ hs).length = gs.length + hs.length := by simp
    have hi' : idx (m + 1) < n + (gs ++ hs).length := by
      have := hi (m + 1) (by omega); omega
    obtain ⟨g1, v1⟩ := add_and n (gs ++ hs) hgood (m + 1) (idx (m + 1)) (by omega) hi'
    obtain ⟨hs4, hl4, g4, v4⟩ := add_xor n (gs ++ hs ++ [(⟨.and, [m + 1, idx (m + 1)]⟩ : Gate)])
      g1 out (n + (gs ++ hs).length) (by simp; omega) (by simp)
    refine ⟨hs ++ [(⟨.and, [m + 1, idx (m + 1)]⟩ : Gate)] ++ hs4, n + (gs ++ hs ++
      [(⟨.and, [m + 1, idx (m + 1)]⟩ : Gate)]).length + 3, ?_, ?_, ?_, ?_⟩
    · simp [hl4]; omega
    · simpa using g4
    · simp [hl4]; omega
    · intro x hx
      have e : gs ++ (hs ++ [(⟨.and, [m + 1, idx (m + 1)]⟩ : Gate)] ++ hs4) =
          gs ++ hs ++ [(⟨.and, [m + 1, idx (m + 1)]⟩ : Gate)] ++ hs4 := by simp
      rw [e, v4 x hx]
      rw [wr_getD_old _ _ x _ (by simp; omega), v1 x hx, hval x hx, wr_input _ x _ (by omega)]
      have hh : (wr (gs ++ hs) x).getD (idx (m + 1)) false = g x (m + 1) := by
        rw [wr_getD_old gs hs x _ (by have := hi (m + 1) (by omega); omega)]
        exact hv x hx (m + 1) (by omega)
      rw [hh]
      simp [Bsum]

lemma Hh_eq (k t j : ℕ) (hj : j < 2 ^ t) (x : List Bool)
    (hx : ∀ z < t, x.getD (k + z) false = j.testBit z) :
    ∀ u ≤ t, Hh k t x u = j - j % 2 ^ (t - u) := by
  intro u
  induction u with
  | zero => intro _; simp [Hh, Nat.mod_eq_of_lt hj]
  | succ u ih =>
    intro hu
    obtain ⟨z, hz⟩ : ∃ z, t - u = z + 1 := ⟨t - u - 1, by omega⟩
    have hz' : t - (u + 1) = z := by omega
    have hzu : t - u - 1 = z := by omega
    have h1 := ih (by omega)
    rw [hz] at h1
    simp only [Hh, hzu, hz', h1]
    rw [hx z (by omega), Nat.mod_pow_succ]
    have hb : j / 2 ^ z % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hle : j % 2 ^ z + 2 ^ z * (j / 2 ^ z % 2) ≤ j := by
      rw [← Nat.mod_pow_succ]; exact Nat.mod_le _ _
    have hle2 : j % 2 ^ z ≤ j := Nat.mod_le _ _
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases (by omega : j / 2 ^ z % 2 = 0 ∨ j / 2 ^ z % 2 = 1) with h | h
    · rw [h] at hle ⊢; simp
    · rw [h] at hle ⊢; simp; omega

lemma Bsum_sum (b : ℕ → Bool) (m : ℕ) :
    (∑ i ∈ Finset.range m, if b i then (1 : ZMod 2) else 0) = if Bsum b m then 1 else 0 := by
  induction m with
  | zero => simp [Bsum]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    cases h1 : Bsum b m <;> cases h2 : b m <;> simp [Bsum, h1, h2] <;> decide

theorem circuit_main (k t : ℕ) (hk : 1 ≤ k) (hkt : t ≤ k) (f : ℕ → Bool) :
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
    C.output < k+t+C.size ∧ C.size ≤ 3*2^t + 3*k*t + 8*k ∧
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
    ∀ (row : Fin k → Bool) (j : Fin (2^t)),
      C.eval (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
        decide ((∑ i : Fin k, (if row i then (1:ZMod 2) else 0) * (if f (j.val+i.val) then 1 else 0)) = 1) := by
  obtain ⟨gs, idx, hg, hl, hi, hv⟩ := layers k t hk f t le_rfl
  simp only [Nat.sub_self, pow_zero] at hl hi hv
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1] at hi hv
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨hs, out, hsl, hgood, hout, hval⟩ := dot_stage (m + 1 + t) (m + 1) (by omega) gs hg idx
    hi (fun x p => f (Hh (m + 1) t x t + p)) hv m le_rfl
  refine ⟨⟨gs ++ hs, out⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi'
    have hj' : j < (gs ++ hs).length := hj
    have := (hgood j hj').1 i
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt] at hi'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj'] at hi'
    exact this hi'
  · exact hout
  · show (gs ++ hs).length ≤ _
    simp only [List.length_append]
    have : 3 * (m + 1) * t = 3 * (m + 1) * t := rfl
    omega
  · intro gate hgate
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hgate
    exact (hgood j hj).2
  · intro row j
    have hxl : (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)).length
        = m + 1 + t := by simp; omega
    have hev := hval _ hxl
    show (wr (gs ++ hs) _).getD out false = _
    rw [hev]
    set x := List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val) with hxdef
    have hget : ∀ i : Fin (m + 1), x.getD i false = row i := by
      intro i
      rw [hxdef, List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [i.isLt])]
      rw [List.getElem?_ofFn]
      simp [i.isLt]
    have hgetj : ∀ z < t, x.getD (m + 1 + z) false = j.val.testBit z := by
      intro z hz
      rw [hxdef, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      have e : m + 1 + z - (List.ofFn row).length = z := by simp
      rw [e, List.getElem?_ofFn]
      simp [hz]
    have hH : Hh (m + 1) t x t = j.val := by
      rw [Hh_eq (m + 1) t j.val j.isLt x hgetj t le_rfl]
      simp [Nat.mod_one]
    simp only [hH]
    have hs2 := Bsum_sum (fun p => x.getD p false && f (j.val + p)) (m + 1)
    rw [← Fin.sum_univ_eq_sum_range (fun p => if (x.getD p false && f (j.val + p)) then
      (1 : ZMod 2) else 0) (m + 1)] at hs2
    have hterm : ∀ i : Fin (m + 1), (if row i then (1 : ZMod 2) else 0) *
        (if f (j.val + i.val) then 1 else 0) =
        if (x.getD i false && f (j.val + i.val)) then (1 : ZMod 2) else 0 := by
      intro i
      rw [hget i]
      cases row i <;> cases f (j.val + i.val) <;> simp
    simp only [hterm, hs2]
    cases Bsum (fun p => x.getD p false && f (j.val + p)) (m + 1) <;> simp



def Lmap (k : ℕ) {T : Type} (a : T → Fin k → ZMod 2) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (T → ZMod 2) :=
  LinearMap.pi (fun t => (
    { toFun := fun x => ∑ i, x i * a t i
      map_add' := by intro x y; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro c x; simp [Finset.mul_sum, mul_assoc] } :
      (Fin k → ZMod 2) →ₗ[ZMod 2] ZMod 2))

lemma Lmap_apply (k : ℕ) {T : Type} (a : T → Fin k → ZMod 2) (x : Fin k → ZMod 2) (t : T) :
    Lmap k a x t = ∑ i, x i * a t i := rfl

lemma Lmap_surj (k : ℕ) (T : Type) [Fintype T] [DecidableEq T] (a : T → Fin k → ZMod 2)
    (hind : ∀ c : T → ZMod 2, (∀ i, ∑ t, c t * a t i = 0) → c = 0) :
    Function.Surjective (Lmap k a) := by
  rw [← LinearMap.dualMap_injective_iff]
  rw [injective_iff_map_eq_zero]
  intro φ hφ
  have h1 : ∀ x, φ (Lmap k a x) = 0 := by
    intro x
    have := congrArg (fun f => f x) hφ
    simpa [LinearMap.dualMap_apply] using this
  set c : T → ZMod 2 := fun t => φ (fun j => if t = j then 1 else 0) with hcdef
  have hc : ∀ i, ∑ t, c t * a t i = 0 := by
    intro i
    have h := h1 (fun j => if i = j then 1 else 0)
    rw [LinearMap.pi_apply_eq_sum_univ φ] at h
    have e : ∀ t, (Lmap k a (fun j => if i = j then 1 else 0)) t = a t i := by
      intro t
      simp [Lmap_apply]
    simp only [e, smul_eq_mul] at h
    rw [← h]
    exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)
  have hc0 := hind c hc
  refine LinearMap.ext (fun y => ?_)
  rw [LinearMap.pi_apply_eq_sum_univ φ]
  have hcz : ∀ t, (φ fun j => if t = j then (1 : ZMod 2) else 0) = 0 := fun t => by
    have := congrFun hc0 t
    simpa [hcdef] using this
  simp [hcz]

lemma fiber_card_eq {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] [DecidableEq W]
    (L : V →ₗ[ZMod 2] W) (hL : Function.Surjective L) (b : W) :
    (Finset.univ.filter (fun x => L x = b)).card = (Finset.univ.filter (fun x => L x = 0)).card := by
  obtain ⟨x0, hx0⟩ := hL b
  apply Finset.card_nbij' (fun x => x - x0) (fun x => x + x0)
  · intro x hx; simp at hx ⊢; simp [hx, hx0]
  · intro x hx; simp at hx ⊢; simp [hx, hx0]
  · intro x _; simp
  · intro x _; simp

lemma fiber_card {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]
    [AddCommGroup W] [Module (ZMod 2) W] [Fintype W] [DecidableEq W]
    (L : V →ₗ[ZMod 2] W) (hL : Function.Surjective L) (b : W) :
    (Finset.univ.filter (fun x => L x = b)).card * Fintype.card W = Fintype.card V := by
  have h := Finset.card_eq_sum_card_fiberwise (f := L) (s := (Finset.univ : Finset V))
    (t := (Finset.univ : Finset W)) (by intro x _; simp)
  have h2 : ∀ w ∈ (Finset.univ : Finset W),
      (Finset.filter (fun x => L x = w) Finset.univ).card =
      (Finset.univ.filter (fun x => L x = b)).card := by
    intro w _
    rw [fiber_card_eq L hL w, fiber_card_eq L hL b]
  rw [Finset.sum_congr rfl h2] at h
  simp at h
  rw [h, mul_comm]

lemma sys_count (k : ℕ) (ι0 : Type) [Fintype ι0] [DecidableEq ι0] (T : Finset ι0)
    (a : ι0 → Fin k → ZMod 2)
    (hind : ∀ c : ι0 → ZMod 2, (∀ t, t ∉ T → c t = 0) → (∀ i, ∑ t, c t * a t i = 0) → c = 0)
    (b : ι0 → ZMod 2) :
    2 ^ T.card * (Finset.univ.filter (fun x : Fin k → ZMod 2 =>
      ∀ t ∈ T, ∑ i, x i * a t i = b t)).card = 2 ^ k := by
  let a' : {t // t ∈ T} → Fin k → ZMod 2 := fun t => a t.1
  have hsurj : Function.Surjective (Lmap k a') := by
    apply Lmap_surj
    intro c hc
    let c0 : ι0 → ZMod 2 := fun t => if h : t ∈ T then c ⟨t, h⟩ else 0
    have h0 : c0 = 0 := by
      apply hind c0
      · intro t ht; simp [c0, ht]
      · intro i
        have := hc i
        have e : ∑ t, c0 t * a t i = ∑ t : {t // t ∈ T}, c t * a' t i := by
          rw [← Finset.sum_subset (Finset.subset_univ T) (by intro t _ ht; simp [c0, ht])]
          rw [← Finset.sum_coe_sort T]
          refine Finset.sum_congr rfl (fun t _ => ?_)
          simp [c0, a']
        rw [e]; exact this
    funext t
    have := congrFun h0 t.1
    simpa [c0, t.2] using this
  have hf := fiber_card (Lmap k a') hsurj (fun t => b t.1)
  have hset : (Finset.univ.filter (fun x : Fin k → ZMod 2 => Lmap k a' x = fun t => b t.1)) =
      (Finset.univ.filter (fun x : Fin k → ZMod 2 => ∀ t ∈ T, ∑ i, x i * a t i = b t)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, funext_iff, Lmap_apply, a']
    exact ⟨fun h t ht => h ⟨t, ht⟩, fun h t => h t.1 t.2⟩
  rw [hset] at hf
  have hW : Fintype.card ({t // t ∈ T} → ZMod 2) = 2 ^ T.card := by
    simp [Fintype.card_fun]
  have hV : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp
  rw [hW, hV] at hf
  rw [mul_comm]; exact hf

lemma z2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

lemma indep_core (k m : ℕ) (hk : 64 ≤ k) (v : Fin m → Fin k → ZMod 2)
    (hB : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ k/32 →
      k/32 < ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card ∧
      ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card + k/32 < k)
    (P : Finset (Fin k)) (hP : P.card ≤ k/32) (S : Finset (Fin m)) (hS : S.card ≤ k/32)
    (c1 : Fin k → ZMod 2) (c0 : ZMod 2) (d : Fin m → ZMod 2)
    (h1 : ∀ i, i ∉ P → c1 i = 0) (hd : ∀ j, j ∉ S → d j = 0)
    (R : ∀ i, c1 i + c0 + ∑ j, d j * v j i = 0) : c1 = 0 ∧ c0 = 0 ∧ d = 0 := by
  set S' : Finset (Fin m) := Finset.univ.filter (fun j => d j = 1) with hS'
  have hS'S : S' ⊆ S := by
    intro j hj
    by_contra hjS
    have := hd j hjS
    simp [hS'] at hj
    rw [hj] at this
    exact absurd this (by decide)
  have hS'card : S'.card ≤ k / 32 := (Finset.card_le_card hS'S).trans hS
  have hsum : ∀ i, ∑ j, d j * v j i = ∑ j ∈ S', v j i := by
    intro i
    rw [hS', Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rcases z2 (d j) with h | h <;> simp [h]
  have R' : ∀ i, c1 i + c0 + ∑ j ∈ S', v j i = 0 := by
    intro i; rw [← hsum i]; exact R i
  have hdz : S' = ∅ → d = 0 := by
    intro he
    funext j
    rcases z2 (d j) with h | h
    · simpa using h
    · exfalso
      have : j ∈ S' := by simp [hS', h]
      rw [he] at this; simp at this
  by_cases hne : S'.Nonempty
  · exfalso
    obtain ⟨hw1, hw2⟩ := hB S' (Finset.card_pos.mpr hne) hS'card
    set W := (Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S', v j i) = 1) with hW
    rcases z2 c0 with h0 | h0
    · have hsub : W ⊆ P := by
        intro i hi
        by_contra hiP
        have e1 := h1 i hiP
        have e2 := R' i
        simp only [hW, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [e1, h0, hi] at e2
        exact absurd e2 (by decide)
      have := Finset.card_le_card hsub
      omega
    · have hsub : Wᶜ ⊆ P := by
        intro i hi
        by_contra hiP
        have e1 := h1 i hiP
        have e2 := R' i
        simp only [hW, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [e1, h0] at e2
        rcases z2 (∑ j ∈ S', v j i) with h | h
        · rw [h] at e2; exact absurd e2 (by decide)
        · exact hi h
      have := Finset.card_le_card hsub
      have hc := Finset.card_add_card_compl W
      rw [Fintype.card_fin] at hc
      omega
  · have he : S' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    have hd0 := hdz he
    have R'' : ∀ i, c1 i + c0 = 0 := by
      intro i; have := R' i; rw [he] at this; simpa using this
    rcases z2 c0 with h0 | h0
    · refine ⟨?_, h0, hd0⟩
      funext i
      have := R'' i
      rw [h0] at this; simpa using this
    · exfalso
      have hall : ∀ i, i ∈ P := by
        intro i
        by_contra hiP
        have e1 := h1 i hiP
        have := R'' i
        rw [e1, h0] at this
        exact absurd this (by decide)
      have : (Finset.univ : Finset (Fin k)) ⊆ P := fun i _ => hall i
      have := Finset.card_le_card this
      simp at this
      omega

lemma pinned (k m : ℕ) (hk : 64 ≤ k) (v : Fin m → Fin k → ZMod 2)
    (hB : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ k/32 →
      k/32 < ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card ∧
      ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card + k/32 < k)
    (P : Finset (Fin k)) (hP : P.card ≤ k/32)
    (pins : Fin k → ZMod 2) (par : ZMod 2) (S : Finset (Fin m)) (hS : S.card ≤ k/32)
    (target : Fin m → ZMod 2) :
    2^(P.card+1+S.card) *
        ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x =>
          (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par ∧
          (∀ j ∈ S, (∑ i : Fin k, x i * v j i) = target j))).card = 2^k := by
  let a : Fin k ⊕ Unit ⊕ Fin m → Fin k → ZMod 2 :=
    Sum.elim (fun i i' => if i = i' then 1 else 0) (Sum.elim (fun _ _ => 1) v)
  let b : Fin k ⊕ Unit ⊕ Fin m → ZMod 2 :=
    Sum.elim pins (Sum.elim (fun _ => par) target)
  let T : Finset (Fin k ⊕ Unit ⊕ Fin m) := P.disjSum ((Finset.univ : Finset Unit).disjSum S)
  have hind : ∀ c : Fin k ⊕ Unit ⊕ Fin m → ZMod 2, (∀ t, t ∉ T → c t = 0) →
      (∀ i, ∑ t, c t * a t i = 0) → c = 0 := by
    intro c hsupp hsum
    have h1 : ∀ i, i ∉ P → c (Sum.inl i) = 0 := fun i hi =>
      hsupp _ (by simp [T, hi])
    have hd : ∀ j, j ∉ S → c (Sum.inr (Sum.inr j)) = 0 := fun j hj =>
      hsupp _ (by simp [T, hj])
    have R : ∀ i, c (Sum.inl i) + c (Sum.inr (Sum.inl ())) +
        ∑ j, c (Sum.inr (Sum.inr j)) * v j i = 0 := by
      intro i
      have := hsum i
      simp [Fintype.sum_sum_type, a] at this
      rw [add_assoc]; exact this
    obtain ⟨e1, e0, ed⟩ := indep_core k m hk v hB P hP S hS (fun i => c (Sum.inl i))
      (c (Sum.inr (Sum.inl ()))) (fun j => c (Sum.inr (Sum.inr j))) h1 hd R
    funext t
    rcases t with i | u | j
    · exact congrFun e1 i
    · rcases u; exact e0
    · exact congrFun ed j
  have h := sys_count k _ T a hind b
  have hcard : T.card = P.card + 1 + S.card := by
    simp [T, Finset.card_disjSum]; omega
  have hset : (Finset.univ.filter (fun x : Fin k → ZMod 2 =>
      ∀ t ∈ T, ∑ i, x i * a t i = b t)) =
      (Finset.univ.filter (fun x : Fin k → ZMod 2 =>
          (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par ∧
          (∀ j ∈ S, (∑ i : Fin k, x i * v j i) = target j))) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨fun i hi => ?_, ?_, fun j hj => ?_⟩
      · have := hx (Sum.inl i) (by simp [T, hi])
        simpa [a, b] using this
      · have := hx (Sum.inr (Sum.inl ())) (by simp [T])
        simpa [a, b] using this
      · have := hx (Sum.inr (Sum.inr j)) (by simp [T, hj])
        simpa [a, b] using this
    · rintro ⟨hx1, hx2, hx3⟩ t ht
      rcases t with i | u | j
      · have hi : i ∈ P := by simpa [T] using ht
        simpa [a, b] using hx1 i hi
      · simpa [a, b] using hx2
      · have hj : j ∈ S := by simpa [T] using ht
        simpa [a, b] using hx3 j hj
  rw [hset, hcard] at h
  exact h





lemma inj_v (k m : ℕ) (hk : 64 ≤ k) (v : Fin m → Fin k → ZMod 2)
    (hB : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ k/32 →
      k/32 < ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card ∧
      ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card + k/32 < k) :
    Function.Injective v := by
  intro j j' h
  by_contra hne
  have h2 : ({j, j'} : Finset (Fin m)).card = 2 := Finset.card_pair hne
  obtain ⟨h3, _⟩ := hB {j, j'} (by omega) (by omega)
  have : ((Finset.univ : Finset (Fin k)).filter
      (fun i => (∑ j ∈ ({j, j'} : Finset (Fin m)), v j i) = 1)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [Finset.sum_pair hne, ← h] at hi
    have : v j i + v j i = 0 := by rcases z2 (v j i) with h | h <;> rw [h] <;> decide
    rw [this] at hi
    exact absurd hi (by decide)
  rw [this] at h3
  simp at h3

def eps (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma eps_add : ∀ x y : ZMod 2, eps (x + y) = eps x * eps y := by decide

lemma orth : ∀ y : Fin 3 → ZMod 2,
    ∑ u : Fin 3 → ZMod 2, eps (∑ c, u c * y c) = if y = 0 then 8 else 0 := by decide

lemma funct (k : ℕ) (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (hA : Function.Surjective A) (u : Fin 3 → ZMod 2) (hu : u ≠ 0) :
    ∃ a : Fin k → ZMod 2, a ≠ 0 ∧ ∀ x, ∑ c, u c * A x c = ∑ i, a i * x i := by
  refine ⟨fun i => ∑ c, u c * A (fun j => if i = j then 1 else 0) c, ?_, ?_⟩
  · intro h0
    have hf : ∀ x, ∑ c, u c * A x c = 0 := by
      intro x
      have e : ∀ x : Fin k → ZMod 2, ∑ c, u c * A x c =
          ∑ i, (∑ c, u c * A (fun j => if i = j then 1 else 0) c) * x i := by
        intro x
        conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ A x]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => ?_))
        ring
      rw [e]
      simp [congrFun h0]
    obtain ⟨c0, hc0⟩ : ∃ c0, u c0 = 1 := by
      by_contra hn
      simp only [not_exists] at hn
      apply hu
      funext c
      rcases z2 (u c) with h | h
      · simpa using h
      · exact absurd h (hn c)
    obtain ⟨x, hx⟩ := hA (fun c => if c0 = c then 1 else 0)
    have := hf x
    rw [hx] at this
    simp [hc0] at this
  · intro x
    conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ A x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ => ?_))
    ring

lemma sum_eps_bound (k m : ℕ) (v : Fin m → Fin k → ZMod 2) (a : Fin k → ZMod 2)
    (h1 : 13*m ≤ 28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card))
    (h2 : 28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ≤ 15*m)
    (s : ℤ) (hs : s = 1 ∨ s = -1) :
    -(m : ℤ) ≤ 14 * (s * ∑ j : Fin m, eps (∑ i : Fin k, a i * v j i)) := by
  set w := (Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card with hw
  have hsum : ∑ j : Fin m, eps (∑ i : Fin k, a i * v j i) = (m : ℤ) - 2 * (w : ℤ) := by
    have : ∀ j : Fin m, eps (∑ i : Fin k, a i * v j i) =
        1 - 2 * (if (∑ i : Fin k, a i * v j i) = 1 then (1 : ℤ) else 0) := by
      intro j
      rcases z2 (∑ i : Fin k, a i * v j i) with h | h <;> simp [eps, h]
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_boole, hw]
    simp
  rw [hsum]
  have h1' : (13 * m : ℤ) ≤ 28 * w := by exact_mod_cast h1
  have h2' : (28 * w : ℤ) ≤ 15 * m := by exact_mod_cast h2
  rcases hs with rfl | rfl <;> nlinarith

lemma fiber_count (k m : ℕ) (v : Fin m → Fin k → ZMod 2)
    (hA : ∀ a : Fin k → ZMod 2, a ≠ 0 →
      13*m ≤ 28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ∧
      28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ≤ 15*m)
    (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (hAs : Function.Surjective A)
    (z : Fin 3 → ZMod 2) :
    m ≤ 16 * (Finset.univ.filter (fun j : Fin m => A (v j) = z)).card := by
  have hz : ∀ y : Fin 3 → ZMod 2, y + z = 0 ↔ y = z := by
    intro y
    constructor
    · intro h
      funext c
      have := congrFun h c
      simp only [Pi.add_apply, Pi.zero_apply] at this
      revert this
      generalize y c = p
      generalize z c = q
      revert p q; decide
    · intro h
      subst h
      funext c
      simp only [Pi.add_apply, Pi.zero_apply]
      generalize y c = p
      revert p; decide
  have h8 : (8 : ℤ) * ((Finset.univ.filter (fun j : Fin m => A (v j) = z)).card : ℤ) =
      ∑ u : Fin 3 → ZMod 2, eps (∑ c, u c * z c) * ∑ j : Fin m, eps (∑ c, u c * A (v j) c) := by
    have e1 : (8 : ℤ) * ((Finset.univ.filter (fun j : Fin m => A (v j) = z)).card : ℤ) =
        ∑ j : Fin m, (if A (v j) = z then (8 : ℤ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
    rw [e1]
    have e2 : ∀ j : Fin m, (if A (v j) = z then (8 : ℤ) else 0) =
        ∑ u : Fin 3 → ZMod 2, eps (∑ c, u c * z c) * eps (∑ c, u c * A (v j) c) := by
      intro j
      have := orth (A (v j) + z)
      have e3 : (A (v j) + z = 0) ↔ A (v j) = z := hz _
      simp only [e3] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      have : ∑ c, u c * (A (v j) + z) c = ∑ c, u c * A (v j) c + ∑ c, u c * z c := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun c _ => by simp [mul_add])
      rw [this, eps_add, mul_comm]
    rw [Finset.sum_congr rfl (fun j _ => e2 j), Finset.sum_comm]
    exact Finset.sum_congr rfl (fun u _ => by rw [Finset.mul_sum])
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin 3 → ZMod 2))
    (fun u : Fin 3 → ZMod 2 => eps (∑ c, u c * z c) * ∑ j : Fin m, eps (∑ c, u c * A (v j) c))
    (Finset.mem_univ 0)
  rw [← h8] at hsplit
  have h0 : eps (∑ c, (0 : Fin 3 → ZMod 2) c * z c) *
      ∑ j : Fin m, eps (∑ c, (0 : Fin 3 → ZMod 2) c * A (v j) c) = m := by
    simp [eps]
  rw [h0] at hsplit
  have hbound : ∀ u ∈ (Finset.univ : Finset (Fin 3 → ZMod 2)).erase 0,
      -(m : ℤ) ≤ 14 * (eps (∑ c, u c * z c) *
        ∑ j : Fin m, eps (∑ c, u c * A (v j) c)) := by
    intro u hu
    have hu0 : u ≠ 0 := Finset.ne_of_mem_erase hu
    obtain ⟨a, ha0, hfa⟩ := funct k A hAs u hu0
    have e : ∀ j : Fin m, ∑ c, u c * A (v j) c = ∑ i, a i * v j i := fun j => hfa (v j)
    simp only [e]
    obtain ⟨b1, b2⟩ := hA a ha0
    refine sum_eps_bound k m v a b1 b2 _ ?_
    rcases z2 (∑ c, u c * z c) with h | h <;> simp [eps, h]
  have hcard : ((Finset.univ : Finset (Fin 3 → ZMod 2)).erase 0).card = 7 := by decide
  have hsumb := Finset.sum_le_sum hbound
  rw [Finset.sum_const, hcard, ← Finset.mul_sum, nsmul_eq_mul] at hsumb
  push_cast at hsumb
  have : (m : ℤ) ≤ 16 * ((Finset.univ.filter (fun j : Fin m => A (v j) = z)).card : ℤ) := by
    nlinarith
  exact_mod_cast this



lemma fiber_keep (k m : ℕ) (v : Fin m → Fin k → ZMod 2)
    (hA : ∀ a : Fin k → ZMod 2, a ≠ 0 →
      13*m ≤ 28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ∧
      28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ≤ 15*m)
    (keep : Finset (Fin m)) (hkeep : 32*(m-keep.card) ≤ m)
    (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (hAs : Function.Surjective A)
    (z : Fin 3 → ZMod 2) :
    m ≤ 32*(keep.filter (fun j => A (v j) = z)).card := by
  have h1 := fiber_count k m v hA A hAs z
  have hsub : (Finset.univ.filter (fun j : Fin m => A (v j) = z)) ⊆
      keep.filter (fun j => A (v j) = z) ∪ keepᶜ := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    by_cases h : j ∈ keep
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, hj⟩)
    · exact Finset.mem_union_right _ (Finset.mem_compl.mpr h)
  have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h3 : (keepᶜ).card = m - keep.card := by
    rw [Finset.card_compl, Fintype.card_fin]
  omega

theorem alg_main (k m : ℕ) (hk : 64 ≤ k) (hm_lo : 512*k ≤ m) (hm_hi : m ≤ 1024*k)
  (v : Fin m → Fin k → ZMod 2)
  (hA : ∀ a : Fin k → ZMod 2, a ≠ 0 →
      13*m ≤ 28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ∧
      28*((Finset.univ.filter (fun j : Fin m => (∑ i : Fin k, a i * v j i) = 1)).card) ≤ 15*m)
  (hB : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ k/32 →
      k/32 < ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card ∧
      ((Finset.univ : Finset (Fin k)).filter (fun i => (∑ j ∈ S, v j i) = 1)).card + k/32 < k) :
  Function.Injective v ∧
  (∀ (keep : Finset (Fin m)), 32*(m-keep.card) ≤ m →
    ∀ (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)), Function.Surjective A → ∀ z : Fin 3 → ZMod 2,
      m ≤ 32*(keep.filter (fun j => A (v j) = z)).card) ∧
  (∀ (P : Finset (Fin k)), P.card ≤ k/32 →
    ∀ (pins : Fin k → ZMod 2) (par : ZMod 2) (S : Finset (Fin m)), S.card ≤ k/32 → ∀ target : Fin m → ZMod 2,
      2^(P.card+1+S.card) *
        ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun x =>
          (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par ∧
          (∀ j ∈ S, (∑ i : Fin k, x i * v j i) = target j))).card = 2^k) :=
  ⟨inj_v k m hk v hB,
   fun keep hkeep A hAs z => fiber_keep k m v hA keep hkeep A hAs z,
   fun P hP pins par S hS target => pinned k m hk v hB P hP pins par S hS target⟩



theorem exists_of_count {α : Type} [Fintype α] [Nonempty α] (p : α → Prop) [DecidablePred p] (c : ℕ)
    (hc : 2 ≤ c) (h : c * (Finset.univ.filter (fun s => ¬ p s)).card ≤ Fintype.card α) :
    ∃ s, p s := by
  by_contra hne
  have hall : Finset.univ.filter (fun s => ¬ p s) = Finset.univ :=
    Finset.filter_true_of_mem (fun s _ => not_exists.mp hne s)
  rw [hall, Finset.card_univ] at h
  have hpos : 0 < Fintype.card α := Fintype.card_pos
  nlinarith
theorem t_exists (k : ℕ) (hk : 64 ≤ k) : ∃ t : ℕ, 512*k ≤ 2^t ∧ 2^t < 1024*k ∧ t ≤ k := by
  have h1 : 1 < 512*k := by omega
  refine ⟨Nat.clog 2 (512*k), Nat.le_pow_clog (by norm_num) (512*k), ?_⟩
  have hpos : 0 < Nat.clog 2 (512*k) := Nat.clog_pos (by norm_num) h1
  have hlt : 2 ^ (Nat.clog 2 (512*k) - 1) < 512*k := Nat.pow_pred_clog_lt_self 2 h1
  have hsucc : 2 ^ Nat.clog 2 (512*k) = 2 * 2 ^ (Nat.clog 2 (512*k) - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine ⟨by omega, ?_⟩
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ^ (k + 1) ≤ 2 ^ Nat.clog 2 (512*k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : k - 11 < 2 ^ (k - 11) := Nat.lt_two_pow_self
  have h4 : 2 ^ (k+1) = 2 ^ 12 * 2 ^ (k - 11) := by
    rw [← pow_add]; congr 1; omega
  omega

end PEqualNP.Outside.L_meta_26647_aux

theorem PEqualNP.Outside.L_meta_26647 :
 ∀ k : ℕ, 64 ≤ k →
   let F := ZMod 2
   let V := Fin k → F
   ∃ t : ℕ,
     let m := 2^t
     512*k ≤ m ∧ m < 1024*k ∧
     ∃ (s : Fin (2^(k+m-1))) (C : PEqualNP.CircuitLowerBounds.Circuit),
       let v := fun (j : Fin m) (i : Fin k) =>
         if s.val.testBit (j.val+i.val) then (1 : F) else 0
       let dot := fun (x y : V) => ∑ i : Fin k, x i * y i
       Function.Injective v ∧
       (∀ (keep : Finset (Fin m)), 32*(m-keep.card) ≤ m →
         ∀ (A : V →ₗ[F] (Fin 3 → F)), Function.Surjective A → ∀ z : Fin 3 → F,
           m ≤ 32*(keep.filter (fun j => A (v j) = z)).card) ∧
       (∀ (P : Finset (Fin k)), P.card ≤ k/32 →
         ∀ (pins : V) (par : F) (S : Finset (Fin m)), S.card ≤ k/32 → ∀ target : Fin m → F,
           2^(P.card+1+S.card) *
             ((Finset.univ : Finset V).filter (fun x =>
               (∀ i ∈ P, x i = pins i) ∧ (∑ i : Fin k, x i) = par ∧
               (∀ j ∈ S, dot x (v j) = target j))).card = 2^k) ∧
       PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
       C.output < k+t+C.size ∧ C.size ≤ 3080*k+3*k*t ∧
       (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
         (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
       ∀ (row : Fin k → Bool) (j : Fin m),
         C.eval (List.ofFn row ++ List.ofFn (fun z : Fin t => j.val.testBit z.val)) =
           decide (dot (fun i => if row i then 1 else 0) (v j) = 1) := by
  intro k hk
  dsimp only
  obtain ⟨t, hlo, hhi, htk⟩ := PEqualNP.Outside.L_meta_26647_aux.t_exists k hk
  refine ⟨t, hlo, hhi, ?_⟩
  have hg := PEqualNP.Outside.L_meta_26647_aux.good_exists k (2^t) hk hlo hhi.le
  have h16 : 2 ≤ 2^(k/16) := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^(k/16) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Nonempty (Fin (2^(k+2^t-1))) := ⟨⟨0, by positivity⟩⟩
  have hex := PEqualNP.Outside.L_meta_26647_aux.exists_of_count _ (2^(k/16)) h16
    (by rw [Fintype.card_fin]; exact hg)
  obtain ⟨s, hA, hB⟩ := hex
  have alg := PEqualNP.Outside.L_meta_26647_aux.alg_main k (2^t) hk hlo hhi.le
    (fun j i => if s.val.testBit (j.val+i.val) then (1:ZMod 2) else 0) hA hB
  obtain ⟨C, hrb, hout, hsize, hgates, heval⟩ :=
    PEqualNP.Outside.L_meta_26647_aux.circuit_main k t (by omega) htk (fun p => s.val.testBit p)
  refine ⟨s, C, alg.1, alg.2.1, alg.2.2, hrb, hout, ?_, hgates, ?_⟩
  · have h3 : 3*2^t ≤ 3*(1024*k) := by omega
    generalize 3*k*t = u at *
    omega
  · intro row j
    exact heval row j
