import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_322_aux

open PEqualNP.ProofComplexity

private lemma fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  fin_cases x <;> simp

private lemma bne_eq_false_imp {a b : Bool} (h : (a != b) = false) : a = b := by
  cases a <;> cases b <;> simp_all

private lemma bne_eq_true_imp {a b : Bool} (h : (a != b) = true) : a ≠ b := by
  cases a <;> cases b <;> simp_all

private lemma xor_ne_xor_of_ne {a b c : Bool} (h : b ≠ c) : xor a b ≠ xor a c := by
  cases a <;> cases b <;> cases c <;> simp_all

private lemma perm_three_color_aux {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∀ k : ℕ, ∀ S : Finset (Fin n), S.card = k →
      ∃ col : Fin n → Fin 3, ∀ i ∈ S, π i ∈ S → π i ≠ i → col (π i) ≠ col i := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨fun _ => 0, fun i hi => ?_⟩
    rw [Finset.card_eq_zero.mp hS] at hi
    exact False.elim (Finset.notMem_empty i hi)
  | succ k ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    rcases hne with ⟨x, hx⟩
    have hcard : (S.erase x).card = k := by
      rw [Finset.card_erase_of_mem hx, hS]; omega
    rcases ih (S.erase x) hcard with ⟨col', hcol'⟩
    have hex_c : ∃ c : Fin 3, c ≠ col' (π x) ∧ c ≠ col' (π.symm x) := by
      rcases fin3_cases (col' (π x)) with h1 | h1 | h1 <;>
        rcases fin3_cases (col' (π.symm x)) with h2 | h2 | h2
      · exact ⟨1, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨2, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨1, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨2, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨0, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨0, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨1, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨0, by rw [h1]; decide, by rw [h2]; decide⟩
      · exact ⟨0, by rw [h1]; decide, by rw [h2]; decide⟩
    rcases hex_c with ⟨c, hc1, hc2⟩
    refine ⟨Function.update col' x c, fun i hi hpi hne_i => ?_⟩
    by_cases hix : i = x
    · subst hix
      rw [Function.update_self, Function.update_of_ne hne_i]
      exact hc1.symm
    · by_cases hpix : π i = x
      · have hisym : i = π.symm x := by rw [← hpix, Equiv.symm_apply_apply]
        rw [hpix, Function.update_self, Function.update_of_ne hix, hisym]
        exact hc2
      · rw [Function.update_of_ne hpix, Function.update_of_ne hix]
        exact hcol' i (Finset.mem_erase.mpr ⟨hix, hi⟩) (Finset.mem_erase.mpr ⟨hpix, hpi⟩) hne_i

private lemma perm_three_color {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ col : Fin n → Fin 3, ∀ i : Fin n, π i ≠ i → col (π i) ≠ col i := by
  rcases perm_three_color_aux π n Finset.univ (by simp) with ⟨col, hcol⟩
  exact ⟨col, fun i hne => hcol i (Finset.mem_univ _) (Finset.mem_univ _) hne⟩

private lemma sum_prod_indep {n : ℕ} (A : Finset (Fin n)) (f : Fin n → Fin n)
    (hf : ∀ i ∈ A, f i ∉ A) (d : Fin n → Bool) (p q : ℚ) :
    (∑ u : Fin n → Bool, ∏ i ∈ A, (if (u i != xor (u (f i)) (d (f i))) then p else q)) =
      (2 : ℚ) ^ (n - A.card) * (p + q) ^ A.card := by
  let e : (({i : Fin n // i ∈ A} → Bool) × ({i : Fin n // i ∉ A} → Bool)) ≃ (Fin n → Bool) :=
    { toFun := fun wv i => if h : i ∈ A then wv.1 ⟨i, h⟩ else wv.2 ⟨i, h⟩
      invFun := fun u => (fun x => u x.1, fun x => u x.1)
      left_inv := by
        intro ⟨w, v⟩
        ext x
        · simp [x.2]
        · simp [x.2]
      right_inv := by
        intro u
        ext i
        by_cases h : i ∈ A <;> simp [h] }
  rw [← Fintype.sum_equiv e _ _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]
  have hinner : ∀ v : {i : Fin n // i ∉ A} → Bool,
      (∑ w : {i : Fin n // i ∈ A} → Bool,
        ∏ i ∈ A, (if (e (w, v) i != xor (e (w, v) (f i)) (d (f i))) then p else q)) =
      (p + q) ^ A.card := by
    intro v
    have hrew : ∀ w : {i : Fin n // i ∈ A} → Bool,
        (∏ i ∈ A, (if (e (w, v) i != xor (e (w, v) (f i)) (d (f i))) then p else q)) =
        (∏ x : {i : Fin n // i ∈ A},
          (if (w x != xor (v ⟨f x.1, hf x.1 x.2⟩) (d (f x.1))) then p else q)) := by
      intro w
      rw [← Finset.prod_coe_sort A]
      refine Finset.prod_congr rfl (fun x _ => ?_)
      simp [e, x.2, hf x.1 x.2]
    simp_rw [hrew]
    rw [show (∑ w : {i : Fin n // i ∈ A} → Bool,
        ∏ x : {i : Fin n // i ∈ A},
          (if (w x != xor (v ⟨f x.1, hf x.1 x.2⟩) (d (f x.1))) then p else q)) =
        ∏ x : {i : Fin n // i ∈ A},
          ∑ b : Bool, (if (b != xor (v ⟨f x.1, hf x.1 x.2⟩) (d (f x.1))) then p else q) from
      (Fintype.prod_sum (fun (x : {i : Fin n // i ∈ A}) (b : Bool) =>
        if (b != xor (v ⟨f x.1, hf x.1 x.2⟩) (d (f x.1))) then p else q)).symm]
    have hfac : ∀ x : {i : Fin n // i ∈ A},
        (∑ b : Bool, (if (b != xor (v ⟨f x.1, hf x.1 x.2⟩) (d (f x.1))) then p else q)) = p + q := by
      intro x
      cases xor (v ⟨f x.1, hf x.1 x.2⟩) (d (f x.1)) <;> simp [add_comm]
    simp_rw [hfac]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
  simp_rw [hinner]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hcard_not : Fintype.card {i : Fin n // i ∉ A} = n - A.card := by
    have h1 : Fintype.card {i : Fin n // i ∉ A} = Aᶜ.card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by simp))
    rw [h1, Finset.card_compl, Fintype.card_fin]
  rw [hcard_not, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

private lemma chernoff_one_class {n : ℕ} (A : Finset (Fin n)) (f : Fin n → Fin n)
    (hf : ∀ i ∈ A, f i ∉ A) (d : Fin n → Bool) (m : ℕ) :
    let cnt := fun u : Fin n → Bool => (A.filter (fun i => u i != xor (u (f i)) (d (f i)))).card
    let badHi := Finset.univ.filter (fun u : Fin n → Bool => A.card + m ≤ 2 * cnt u)
    let badLo := Finset.univ.filter (fun u : Fin n → Bool => 2 * cnt u + m ≤ A.card)
    (badHi.card : ℚ) * (193 / 192 : ℚ) ^ m ≤ (2 : ℚ) ^ n * (74113 / 74112 : ℚ) ^ n ∧
    (badLo.card : ℚ) * (193 / 192 : ℚ) ^ m ≤ (2 : ℚ) ^ n * (74113 / 74112 : ℚ) ^ n := by
  intro cnt badHi badLo
  have hAc : A.card ≤ n := by
    calc A.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  have hr_ge1 : (1 : ℚ) ≤ 74113 / 74112 := by norm_num
  have hp_ge1 : (1 : ℚ) ≤ 193 / 192 := by norm_num
  have hp_pos : (0 : ℚ) < 193 / 192 := by norm_num
  constructor
  · have hsum := sum_prod_indep A f hf d ((193 / 192 : ℚ) ^ 2) 1
    have hprod : ∀ u : Fin n → Bool,
        (∏ i ∈ A, (if (u i != xor (u (f i)) (d (f i))) then ((193 / 192 : ℚ) ^ 2) else 1)) =
          (193 / 192 : ℚ) ^ (2 * cnt u) := by
      intro u
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, ← pow_mul]
    simp_rw [hprod] at hsum
    have hge : (badHi.card : ℚ) * (193 / 192 : ℚ) ^ (A.card + m) ≤
        ∑ u : Fin n → Bool, (193 / 192 : ℚ) ^ (2 * cnt u) := by
      calc (badHi.card : ℚ) * (193 / 192 : ℚ) ^ (A.card + m)
          = ∑ _u ∈ badHi, (193 / 192 : ℚ) ^ (A.card + m) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ u ∈ badHi, (193 / 192 : ℚ) ^ (2 * cnt u) := by
            refine Finset.sum_le_sum (fun u hu => ?_)
            have hle : A.card + m ≤ 2 * cnt u := (Finset.mem_filter.mp hu).2
            exact pow_le_pow_right₀ hp_ge1 hle
        _ ≤ ∑ u : Fin n → Bool, (193 / 192 : ℚ) ^ (2 * cnt u) := by
            refine Finset.sum_le_univ_sum_of_nonneg (fun u => by positivity)
    rw [hsum] at hge
    have hfactor : ((193 / 192 : ℚ) ^ 2 + 1) = 2 * (193 / 192) * (74113 / 74112) := by norm_num
    rw [hfactor, mul_pow, mul_pow, pow_add] at hge
    have hpow2 : (2 : ℚ) ^ (n - A.card) * (2 : ℚ) ^ A.card = (2 : ℚ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hAc]
    have hge2 : ((badHi.card : ℚ) * (193 / 192 : ℚ) ^ m) * (193 / 192 : ℚ) ^ A.card ≤
        ((2 : ℚ) ^ n * (74113 / 74112 : ℚ) ^ A.card) * (193 / 192 : ℚ) ^ A.card := by
      calc ((badHi.card : ℚ) * (193 / 192 : ℚ) ^ m) * (193 / 192 : ℚ) ^ A.card
          = (badHi.card : ℚ) * ((193 / 192 : ℚ) ^ A.card * (193 / 192 : ℚ) ^ m) := by ring
        _ ≤ (2 : ℚ) ^ (n - A.card) * ((2 : ℚ) ^ A.card * (193 / 192 : ℚ) ^ A.card * (74113 / 74112 : ℚ) ^ A.card) := hge
        _ = ((2 : ℚ) ^ (n - A.card) * (2 : ℚ) ^ A.card) * (74113 / 74112 : ℚ) ^ A.card * (193 / 192 : ℚ) ^ A.card := by ring
        _ = ((2 : ℚ) ^ n * (74113 / 74112 : ℚ) ^ A.card) * (193 / 192 : ℚ) ^ A.card := by rw [hpow2]
    have hcancel := le_of_mul_le_mul_right hge2 (pow_pos hp_pos A.card)
    exact le_trans hcancel (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr_ge1 hAc) (by positivity))
  · have hsum := sum_prod_indep A f hf d 1 ((193 / 192 : ℚ) ^ 2)
    have hprod : ∀ u : Fin n → Bool,
        (∏ i ∈ A, (if (u i != xor (u (f i)) (d (f i))) then (1 : ℚ) else ((193 / 192 : ℚ) ^ 2))) =
          (193 / 192 : ℚ) ^ (2 * (A.card - cnt u)) := by
      intro u
      rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, ← pow_mul]
      congr 2
      have hpart := Finset.card_filter_add_card_filter_not (s := A)
        (p := fun i => (u i != xor (u (f i)) (d (f i))) = true)
      have hsub : (A.filter (fun i => ¬ ((u i != xor (u (f i)) (d (f i))) = true))).card = A.card - cnt u := by
        dsimp only [cnt]; omega
      simpa using hsub
    simp_rw [hprod] at hsum
    have hge : (badLo.card : ℚ) * (193 / 192 : ℚ) ^ (A.card + m) ≤
        ∑ u : Fin n → Bool, (193 / 192 : ℚ) ^ (2 * (A.card - cnt u)) := by
      calc (badLo.card : ℚ) * (193 / 192 : ℚ) ^ (A.card + m)
          = ∑ _u ∈ badLo, (193 / 192 : ℚ) ^ (A.card + m) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ u ∈ badLo, (193 / 192 : ℚ) ^ (2 * (A.card - cnt u)) := by
            refine Finset.sum_le_sum (fun u hu => ?_)
            have hle : 2 * cnt u + m ≤ A.card := (Finset.mem_filter.mp hu).2
            have hle2 : A.card + m ≤ 2 * (A.card - cnt u) := by omega
            exact pow_le_pow_right₀ hp_ge1 hle2
        _ ≤ ∑ u : Fin n → Bool, (193 / 192 : ℚ) ^ (2 * (A.card - cnt u)) := by
            refine Finset.sum_le_univ_sum_of_nonneg (fun u => by positivity)
    rw [hsum] at hge
    have hfactor : (1 + (193 / 192 : ℚ) ^ 2) = 2 * (193 / 192) * (74113 / 74112) := by norm_num
    rw [hfactor, mul_pow, mul_pow, pow_add] at hge
    have hpow2 : (2 : ℚ) ^ (n - A.card) * (2 : ℚ) ^ A.card = (2 : ℚ) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hAc]
    have hge2 : ((badLo.card : ℚ) * (193 / 192 : ℚ) ^ m) * (193 / 192 : ℚ) ^ A.card ≤
        ((2 : ℚ) ^ n * (74113 / 74112 : ℚ) ^ A.card) * (193 / 192 : ℚ) ^ A.card := by
      calc ((badLo.card : ℚ) * (193 / 192 : ℚ) ^ m) * (193 / 192 : ℚ) ^ A.card
          = (badLo.card : ℚ) * ((193 / 192 : ℚ) ^ A.card * (193 / 192 : ℚ) ^ m) := by ring
        _ ≤ (2 : ℚ) ^ (n - A.card) * ((2 : ℚ) ^ A.card * (193 / 192 : ℚ) ^ A.card * (74113 / 74112 : ℚ) ^ A.card) := hge
        _ = ((2 : ℚ) ^ (n - A.card) * (2 : ℚ) ^ A.card) * (74113 / 74112 : ℚ) ^ A.card * (193 / 192 : ℚ) ^ A.card := by ring
        _ = ((2 : ℚ) ^ n * (74113 / 74112 : ℚ) ^ A.card) * (193 / 192 : ℚ) ^ A.card := by rw [hpow2]
    have hcancel := le_of_mul_le_mul_right hge2 (pow_pos hp_pos A.card)
    exact le_trans hcancel (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr_ge1 hAc) (by positivity))

private lemma rat_r192_le : (74113 / 74112 : ℚ) ^ 192 ≤ (998 / 1000 : ℚ) * (193 / 192 : ℚ) := by
  have hb : 1 + (192 : ℚ) * (-1 / 74113 : ℚ) ≤ (1 + (-1 / 74113 : ℚ)) ^ 192 :=
    one_add_mul_le_pow (by norm_num) 192
  have h1 : (73921 / 74113 : ℚ) ≤ (74112 / 74113 : ℚ) ^ 192 := by
    have heq1 : (1 : ℚ) + (192 : ℚ) * (-1 / 74113 : ℚ) = 73921 / 74113 := by norm_num
    have heq2 : (1 : ℚ) + (-1 / 74113 : ℚ) = 74112 / 74113 := by norm_num
    rw [heq1, heq2] at hb; exact hb
  have h2 : (1000 / 998 : ℚ) * (192 / 193 : ℚ) ≤ 73921 / 74113 := by norm_num
  have h3 : (1000 / 998 : ℚ) * (192 / 193 : ℚ) ≤ (74112 / 74113 : ℚ) ^ 192 := le_trans h2 h1
  have hinv : ((74112 / 74113 : ℚ) ^ 192) * ((74113 / 74112 : ℚ) ^ 192) = 1 := by
    rw [← mul_pow]; norm_num
  have hmul : ((1000 / 998 : ℚ) * (192 / 193 : ℚ)) * ((74113 / 74112 : ℚ) ^ 192) ≤ 1 := by
    calc ((1000 / 998 : ℚ) * (192 / 193 : ℚ)) * ((74113 / 74112 : ℚ) ^ 192)
        ≤ ((74112 / 74113 : ℚ) ^ 192) * ((74113 / 74112 : ℚ) ^ 192) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 1 := hinv
  have hpos : (0 : ℚ) < (998 / 1000 : ℚ) * (193 / 192 : ℚ) := by norm_num
  nlinarith

private lemma rat_r192_le_two : (74113 / 74112 : ℚ) ^ 192 ≤ 2 :=
  le_trans rat_r192_le (by norm_num)

private lemma rat_998_500_le_half : (998 / 1000 : ℚ) ^ 500 ≤ 1 / 2 := by
  have hb : 1 + (500 : ℚ) * (2 / 998 : ℚ) ≤ (1 + (2 / 998 : ℚ)) ^ 500 :=
    one_add_mul_le_pow (by norm_num) 500
  have h1 : (2 : ℚ) ≤ (1000 / 998 : ℚ) ^ 500 := by
    have heq : (1 : ℚ) + (2 / 998 : ℚ) = 1000 / 998 := by norm_num
    have h2 : (2 : ℚ) ≤ 1 + (500 : ℚ) * (2 / 998 : ℚ) := by norm_num
    rw [heq] at hb
    exact le_trans h2 hb
  have hinv : ((1000 / 998 : ℚ) ^ 500) * ((998 / 1000 : ℚ) ^ 500) = 1 := by
    rw [← mul_pow]; norm_num
  have hmul : (2 : ℚ) * ((998 / 1000 : ℚ) ^ 500) ≤ 1 := by
    calc (2 : ℚ) * ((998 / 1000 : ℚ) ^ 500)
        ≤ ((1000 / 998 : ℚ) ^ 500) * ((998 / 1000 : ℚ) ^ 500) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := hinv
  exact (le_div_iff₀' (by norm_num : (0 : ℚ) < 2)).mpr hmul

private lemma two_pow_gt_linear (k : ℕ) (hk : 24 ≤ k) : 200000 * (k + 1) < 2 ^ k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h24 : k = 23
    · subst h24; decide
    · have hk' : 24 ≤ k := by omega
      have hih := ih hk'
      rw [pow_succ]
      omega

private lemma tail_decay (n : ℕ) (hn : 4000000 ≤ n) :
    (n : ℚ) * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)) < 1 := by
  let q := n / 192
  have hq_rem : n ≤ 192 * q + 192 := by omega
  have hr_ge1 : (1 : ℚ) ≤ 74113 / 74112 := by norm_num
  have hp_pos : (0 : ℚ) < (193 / 192 : ℚ) ^ q := by positivity
  have hstep1 : (74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ q ≤ 2 * (998 / 1000 : ℚ) ^ q := by
    rw [div_le_iff₀ hp_pos]
    calc (74113 / 74112 : ℚ) ^ n
        ≤ (74113 / 74112 : ℚ) ^ (192 * q + 192) := pow_le_pow_right₀ hr_ge1 hq_rem
      _ = (74113 / 74112 : ℚ) ^ 192 * ((74113 / 74112 : ℚ) ^ 192) ^ q := by
          rw [pow_add, pow_mul, mul_comm]
      _ ≤ 2 * ((998 / 1000 : ℚ) * (193 / 192 : ℚ)) ^ q := by
          exact mul_le_mul rat_r192_le_two (pow_le_pow_left₀ (by positivity) rat_r192_le q)
            (by positivity) (by positivity)
      _ = 2 * (998 / 1000 : ℚ) ^ q * (193 / 192 : ℚ) ^ q := by rw [mul_pow]; ring
  let m := q / 500
  have hm_le : 500 * m ≤ q := by omega
  have hstep2 : (998 / 1000 : ℚ) ^ q ≤ (1 / 2 : ℚ) ^ m := by
    calc (998 / 1000 : ℚ) ^ q
        ≤ (998 / 1000 : ℚ) ^ (500 * m) := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_le
      _ = ((998 / 1000 : ℚ) ^ 500) ^ m := by rw [pow_mul]
      _ ≤ (1 / 2 : ℚ) ^ m := pow_le_pow_left₀ (by positivity) rat_998_500_le_half m
  have hm24 : 24 ≤ m := by omega
  have h2m : 200000 * (m + 1) < 2 ^ m := two_pow_gt_linear m hm24
  have hn_lt : 2 * n < 2 ^ m := by
    have : 2 * n ≤ 200000 * (m + 1) := by omega
    omega
  have hn_lt_q : (2 * n : ℚ) < (2 : ℚ) ^ m := by exact_mod_cast hn_lt
  have h1 : (n : ℚ) * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ q) ≤ (2 * n : ℚ) * (1 / 2 : ℚ) ^ m := by
    calc (n : ℚ) * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ q)
        ≤ (n : ℚ) * (2 * (998 / 1000 : ℚ) ^ q) := mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ ≤ (n : ℚ) * (2 * (1 / 2 : ℚ) ^ m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep2 (by norm_num)) (by positivity)
      _ = (2 * n : ℚ) * (1 / 2 : ℚ) ^ m := by ring
  have h2 : (2 * n : ℚ) * (1 / 2 : ℚ) ^ m < 1 := by
    rw [one_div, inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact hn_lt_q
  exact lt_of_le_of_lt h1 h2

private lemma exists_base_assignment {n r : ℕ} (hn : 4000000 ≤ n) (hrn : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hov : ∀ j l : Fin r, j ≠ l → 128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (j : Fin r) (d : Fin n → Bool) :
    ∃ x₀ : (Bool × Fin n) → Bool,
      (∀ i : Fin n, (x₀ (false, i) != x₀ (true, M j i)) = d i) ∧
      (∀ l : Fin r, l ≠ j →
        128 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x₀ (false, i) ≠ x₀ (true, M l i))).card) n ≤ 3 * n) := by
  let mkX : (Fin n → Bool) → (Bool × Fin n) → Bool := fun u p =>
    match p with
    | (false, i) => u i
    | (true, k) => xor (u ((M j).symm k)) (d ((M j).symm k))
  let badFor : Fin r → Finset (Fin n → Bool) := fun l =>
    if hlj : l = j then ∅
    else Finset.univ.filter (fun u : Fin n → Bool =>
      3 * n < 128 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => mkX u (false, i) ≠ mkX u (true, M l i))).card) n)
  have hbad_bound : ∀ l : Fin r, ((badFor l).card : ℚ) ≤
      6 * ((2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192))) := by
    intro l
    by_cases hlj : l = j
    · simp only [badFor, hlj, ↓reduceDIte, Finset.card_empty, Nat.cast_zero]
      positivity
    · simp only [badFor, hlj, ↓reduceDIte]
      let π : Equiv.Perm (Fin n) := (M l).trans (M j).symm
      rcases perm_three_color π with ⟨col, hcol⟩
      let A : Fin 3 → Finset (Fin n) := fun t => Finset.univ.filter (fun i => π i ≠ i ∧ col i = t)
      have hAf : ∀ t : Fin 3, ∀ i ∈ A t, π i ∉ A t := by
        intro t i hi hpi
        have hi' := (Finset.mem_filter.mp hi).2
        have hpi' := (Finset.mem_filter.mp hpi).2
        exact hcol i hi'.1 (hpi'.2.trans hi'.2.symm)
      let badClass : Fin 3 → Finset (Fin n → Bool) := fun t =>
        let cnt := fun u : Fin n → Bool => (A t |>.filter (fun i => u i != xor (u (π i)) (d (π i)))).card
        Finset.univ.filter (fun u => (A t).card + n / 192 ≤ 2 * cnt u) ∪
        Finset.univ.filter (fun u => 2 * cnt u + n / 192 ≤ (A t).card)
      have hsub : Finset.univ.filter (fun u : Fin n → Bool =>
          3 * n < 128 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => mkX u (false, i) ≠ mkX u (true, M l i))).card) n) ⊆
          badClass 0 ∪ badClass 1 ∪ badClass 2 := by
        intro u hu
        by_contra hnot
        let P : Fin n → Bool := fun i => u i != xor (u (π i)) (d (π i))
        have hok : ∀ t : Fin 3,
            let cnt := ((A t).filter (fun i => P i = true)).card
            2 * cnt < (A t).card + n / 192 ∧ (A t).card < 2 * cnt + n / 192 := by
          intro t
          have hnt : u ∉ badClass t := by
            intro hm; apply hnot
            rcases fin3_cases t with rfl | rfl | rfl <;> simp [hm]
          simp only [badClass, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, not_or] at hnt
          dsimp only [P]
          omega
        have hDeq : (Finset.univ.filter (fun i : Fin n => mkX u (false, i) ≠ mkX u (true, M l i))).card =
            (Finset.univ.filter (fun i : Fin n => P i = true)).card := by
          refine congrArg Finset.card ?_
          ext i; simp [mkX, P, π]
        let F := Finset.univ.filter (fun i : Fin n => π i = i)
        have hFov : 128 * F.card ≤ n := by
          have hFeq : F = Finset.univ.filter (fun i : Fin n => M j i = M l i) := by
            ext i
            simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
            simp only [π, Equiv.trans_apply]
            constructor
            · intro h; have := congrArg (M j) h; simpa using this.symm
            · intro h; rw [← h, Equiv.symm_apply_apply]
          rw [hFeq]; exact hov j l (Ne.symm hlj)
        have hpart_all : F.card + (A 0).card + (A 1).card + (A 2).card = n := by
          have hdisj : Disjoint F (A 0 ∪ A 1 ∪ A 2) := by
            rw [Finset.disjoint_left]; intro i hi h2
            have h1 := (Finset.mem_filter.mp hi).2
            simp only [A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h2
            rcases h2 with (⟨hne, _⟩ | ⟨hne, _⟩) | ⟨hne, _⟩ <;> exact hne h1
          have h01 : Disjoint (A 0) (A 1) := by
            rw [Finset.disjoint_left]; intro i h0 h1
            have c0 := (Finset.mem_filter.mp h0).2.2
            have c1 := (Finset.mem_filter.mp h1).2.2
            rw [c0] at c1; exact absurd c1 (by decide)
          have h012 : Disjoint (A 0 ∪ A 1) (A 2) := by
            rw [Finset.disjoint_left]; intro i h01' h2
            have c2 := (Finset.mem_filter.mp h2).2.2
            simp only [A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h01'
            rcases h01' with ⟨_, c0⟩ | ⟨_, c1⟩
            · rw [c0] at c2; exact absurd c2 (by decide)
            · rw [c1] at c2; exact absurd c2 (by decide)
          have hunion : F ∪ (A 0 ∪ A 1 ∪ A 2) = Finset.univ := by
            ext i; simp only [F, A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            by_cases hpi : π i = i
            · exact Or.inl hpi
            · right
              rcases fin3_cases (col i) with hc | hc | hc <;> simp [hpi, hc]
          have hc := congrArg Finset.card hunion
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint h012,
              Finset.card_union_of_disjoint h01, Finset.card_univ, Fintype.card_fin] at hc
          omega
        have hpart_P : (F.filter (fun i => P i = true)).card +
            ((A 0).filter (fun i => P i = true)).card +
            ((A 1).filter (fun i => P i = true)).card +
            ((A 2).filter (fun i => P i = true)).card =
            (Finset.univ.filter (fun i : Fin n => P i = true)).card := by
          have hunion : F.filter (fun i => P i = true) ∪
              ((A 0).filter (fun i => P i = true) ∪ (A 1).filter (fun i => P i = true) ∪
               (A 2).filter (fun i => P i = true)) = Finset.univ.filter (fun i : Fin n => P i = true) := by
            ext i; simp only [F, A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro (⟨_, hp⟩ | (⟨_, hp⟩ | ⟨_, hp⟩) | ⟨_, hp⟩) <;> exact hp
            · intro hp
              by_cases hpi : π i = i
              · exact Or.inl ⟨hpi, hp⟩
              · right
                rcases fin3_cases (col i) with hc | hc | hc <;> simp [hpi, hp, hc]
          have hd1 : Disjoint (F.filter (fun i => P i = true))
              ((A 0).filter (fun i => P i = true) ∪ (A 1).filter (fun i => P i = true) ∪
               (A 2).filter (fun i => P i = true)) := by
            rw [Finset.disjoint_left]; intro i h1 h2
            have he := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
            simp only [A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h2
            rcases h2 with (⟨⟨hne, _⟩, _⟩ | ⟨⟨hne, _⟩, _⟩) | ⟨⟨hne, _⟩, _⟩ <;> exact hne he
          have hd2 : Disjoint ((A 0).filter (fun i => P i = true)) ((A 1).filter (fun i => P i = true)) := by
            rw [Finset.disjoint_left]; intro i h0 h1
            have c0 := (Finset.mem_filter.mp (Finset.mem_filter.mp h0).1).2.2
            have c1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2.2
            rw [c0] at c1; exact absurd c1 (by decide)
          have hd3 : Disjoint ((A 0).filter (fun i => P i = true) ∪ (A 1).filter (fun i => P i = true))
              ((A 2).filter (fun i => P i = true)) := by
            rw [Finset.disjoint_left]; intro i h01' h2
            have c2 := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2.2
            simp only [A, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at h01'
            rcases h01' with ⟨⟨_, c0⟩, _⟩ | ⟨⟨_, c1⟩, _⟩
            · rw [c0] at c2; exact absurd c2 (by decide)
            · rw [c1] at c2; exact absurd c2 (by decide)
          have hc := congrArg Finset.card hunion
          rw [Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd3,
              Finset.card_union_of_disjoint hd2] at hc
          omega
        have hF_le : (F.filter (fun i => P i = true)).card ≤ F.card := Finset.card_filter_le _ _
        have h0 := hok 0; have h1 := hok 1; have h2 := hok 2
        have hgt := (Finset.mem_filter.mp hu).2
        rw [hDeq, ← hpart_P] at hgt
        have hdist_le : Nat.dist (2 * ((F.filter (fun i => P i = true)).card +
            ((A 0).filter (fun i => P i = true)).card +
            ((A 1).filter (fun i => P i = true)).card +
            ((A 2).filter (fun i => P i = true)).card)) n ≤ F.card + 3 * (n / 192) := by
          simp only [Nat.dist]; omega
        omega
      have hcard_le : (Finset.univ.filter (fun u : Fin n → Bool =>
          3 * n < 128 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => mkX u (false, i) ≠ mkX u (true, M l i))).card) n)).card ≤
          (badClass 0).card + (badClass 1).card + (badClass 2).card := by
        calc _ ≤ (badClass 0 ∪ badClass 1 ∪ badClass 2).card := Finset.card_le_card hsub
          _ ≤ (badClass 0 ∪ badClass 1).card + (badClass 2).card := Finset.card_union_le _ _
          _ ≤ (badClass 0).card + (badClass 1).card + (badClass 2).card := by
              have := Finset.card_union_le (badClass 0) (badClass 1); omega
      have hclass_le : ∀ t : Fin 3, ((badClass t).card : ℚ) ≤
          2 * ((2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192))) := by
        intro t
        have hc := chernoff_one_class (A t) π (hAf t) d (n / 192)
        have hp_pos : (0 : ℚ) < (193 / 192 : ℚ) ^ (n / 192) := by positivity
        have h1 : ((Finset.univ.filter (fun u : Fin n → Bool => (A t).card + n / 192 ≤
            2 * (A t |>.filter (fun i => u i != xor (u (π i)) (d (π i)))).card)).card : ℚ) ≤
            (2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)) := by
          rw [mul_div_assoc', le_div_iff₀ hp_pos]; exact hc.1
        have h2 : ((Finset.univ.filter (fun u : Fin n → Bool =>
            2 * (A t |>.filter (fun i => u i != xor (u (π i)) (d (π i)))).card + n / 192 ≤ (A t).card)).card : ℚ) ≤
            (2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)) := by
          rw [mul_div_assoc', le_div_iff₀ hp_pos]; exact hc.2
        have hun : ((badClass t).card : ℚ) ≤
            ((Finset.univ.filter (fun u : Fin n → Bool => (A t).card + n / 192 ≤
              2 * (A t |>.filter (fun i => u i != xor (u (π i)) (d (π i)))).card)).card : ℚ) +
            ((Finset.univ.filter (fun u : Fin n → Bool =>
              2 * (A t |>.filter (fun i => u i != xor (u (π i)) (d (π i)))).card + n / 192 ≤ (A t).card)).card : ℚ) := by
          exact_mod_cast Finset.card_union_le _ _
        linarith
      have hcast : ((Finset.univ.filter (fun u : Fin n → Bool =>
          3 * n < 128 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => mkX u (false, i) ≠ mkX u (true, M l i))).card) n)).card : ℚ) ≤
          ((badClass 0).card : ℚ) + ((badClass 1).card : ℚ) + ((badClass 2).card : ℚ) := by
        exact_mod_cast hcard_le
      have h0 := hclass_le 0; have h1 := hclass_le 1; have h2 := hclass_le 2
      linarith
  let allBad : Finset (Fin n → Bool) := Finset.univ.biUnion badFor
  have hallBad_lt : allBad.card < (Finset.univ : Finset (Fin n → Bool)).card := by
    have hq_lt : (allBad.card : ℚ) < (2 : ℚ) ^ n := by
      have h1 : (allBad.card : ℚ) ≤ ∑ l : Fin r, ((badFor l).card : ℚ) := by
        exact_mod_cast Finset.card_biUnion_le
      have h2 : ∑ l : Fin r, ((badFor l).card : ℚ) ≤
          (r : ℚ) * (6 * ((2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)))) := by
        calc ∑ l : Fin r, ((badFor l).card : ℚ)
            ≤ ∑ _l : Fin r, (6 * ((2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)))) :=
              Finset.sum_le_sum (fun l _ => hbad_bound l)
          _ = (r : ℚ) * (6 * ((2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)))) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h6r : (6 * r : ℚ) ≤ (n : ℚ) := by exact_mod_cast (show 6 * r ≤ n by omega)
      have h3 : (r : ℚ) * (6 * ((2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)))) ≤
          (2 : ℚ) ^ n * ((n : ℚ) * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192))) := by
        have hnonneg : (0 : ℚ) ≤ (2 : ℚ) ^ n * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192)) := by positivity
        nlinarith
      have h4 : (2 : ℚ) ^ n * ((n : ℚ) * ((74113 / 74112 : ℚ) ^ n / (193 / 192 : ℚ) ^ (n / 192))) < (2 : ℚ) ^ n * 1 :=
        mul_lt_mul_of_pos_left (tail_decay n hn) (by positivity)
      linarith
    have hcard_u : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by simp
    rw [hcard_u]
    exact_mod_cast hq_lt
  have hne : (Finset.univ \ allBad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : Finset.univ ⊆ allBad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  rcases hne with ⟨u, hu⟩
  have hu_not : u ∉ allBad := (Finset.mem_sdiff.mp hu).2
  refine ⟨mkX u, ?_, ?_⟩
  · intro i
    simp [mkX]
  · intro l hlj
    by_contra hgt
    push Not at hgt
    apply hu_not
    refine Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, ?_⟩
    simp [badFor, hlj, hgt]

private lemma hamming_change_le {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x x₀ : (Bool × Fin n) → Bool) (U : Finset (Bool × Fin n))
    (hagree : ∀ v : Bool × Fin n, v ∉ U → x v = x₀ v) :
    Nat.dist
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card
      (Finset.univ.filter (fun i : Fin n => x₀ (false, i) ≠ x₀ (true, σ i))).card ≤ U.card := by
  let S1 := Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))
  let S2 := Finset.univ.filter (fun i : Fin n => x₀ (false, i) ≠ x₀ (true, σ i))
  let C := Finset.univ.filter (fun i : Fin n => (false, i) ∈ U ∨ (true, σ i) ∈ U)
  have hC_le : C.card ≤ U.card := by
    let C1 := Finset.univ.filter (fun i : Fin n => (false, i) ∈ U)
    let C2 := Finset.univ.filter (fun i : Fin n => (true, σ i) ∈ U)
    have hsub : C ⊆ C1 ∪ C2 := by
      intro i hi; simp only [C, C1, C2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact hi
    let img1 := C1.image (fun i => (false, i))
    let img2 := C2.image (fun i => (true, σ i))
    have hc1 : C1.card = img1.card := (Finset.card_image_of_injective C1 (fun a b h => by simpa using h)).symm
    have hc2 : C2.card = img2.card := (Finset.card_image_of_injective C2 (fun a b h => by
      have : σ a = σ b := by simpa using h
      exact σ.injective this)).symm
    have hdisj : Disjoint img1 img2 := by
      rw [Finset.disjoint_left]; intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨i, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨j, _, h⟩
      cases h
    have himg_sub : img1 ∪ img2 ⊆ U := by
      intro p hp
      rcases Finset.mem_union.mp hp with h1 | h2
      · rcases Finset.mem_image.mp h1 with ⟨i, hi, rfl⟩; exact (Finset.mem_filter.mp hi).2
      · rcases Finset.mem_image.mp h2 with ⟨i, hi, rfl⟩; exact (Finset.mem_filter.mp hi).2
    calc C.card ≤ (C1 ∪ C2).card := Finset.card_le_card hsub
      _ ≤ C1.card + C2.card := Finset.card_union_le _ _
      _ = (img1 ∪ img2).card := by rw [Finset.card_union_of_disjoint hdisj, hc1, hc2]
      _ ≤ U.card := Finset.card_le_card himg_sub
  have h12 : S1 ⊆ S2 ∪ C := by
    intro i hi
    by_cases hU : (false, i) ∈ U ∨ (true, σ i) ∈ U
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)
    · push Not at hU
      have h1 := hagree (false, i) hU.1
      have h2 := hagree (true, σ i) hU.2
      have hne := (Finset.mem_filter.mp hi).2
      rw [h1, h2] at hne
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  have h21 : S2 ⊆ S1 ∪ C := by
    intro i hi
    by_cases hU : (false, i) ∈ U ∨ (true, σ i) ∈ U
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU⟩)
    · push Not at hU
      have h1 := hagree (false, i) hU.1
      have h2 := hagree (true, σ i) hU.2
      have hne := (Finset.mem_filter.mp hi).2
      rw [← h1, ← h2] at hne
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  have hl1 : S1.card ≤ S2.card + C.card := le_trans (Finset.card_le_card h12) (Finset.card_union_le _ _)
  have hl2 : S2.card ≤ S1.card + C.card := le_trans (Finset.card_le_card h21) (Finset.card_union_le _ _)
  dsimp only [S1, S2] at hl1 hl2
  simp only [Nat.dist]; omega

private lemma prefix_comparable {α : Type*} {a b u : List α}
    (ha : List.IsPrefix a u) (hb : List.IsPrefix b u) :
    List.IsPrefix a b ∨ List.IsPrefix b a := by
  rcases ha with ⟨ta, rfl⟩
  rcases hb with ⟨tb, h⟩
  induction a generalizing b with
  | nil => exact Or.inl ⟨b, by simp⟩
  | cons x xs ih =>
    cases b with
    | nil => exact Or.inr ⟨x :: xs, by simp⟩
    | cons y ys =>
      simp only [List.cons_append, List.cons.injEq] at h
      rcases h with ⟨rfl, htail⟩
      rcases ih htail with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact Or.inl ⟨t, by simp⟩
      · exact Or.inr ⟨t, by simp⟩

private lemma bag_separates {G : Type*} [DecidableEq G] {h : ℕ}
    {bag : List Bool → Finset G}
    (hconn : ∀ (u v : List Bool) (x : G), u.length ≤ h → v.length ≤ h →
      x ∈ bag u → x ∈ bag v → ∃ b : List Bool,
        List.IsPrefix b u ∧ List.IsPrefix b v ∧
        ∀ z : List Bool, List.IsPrefix b z →
          (List.IsPrefix z u ∨ List.IsPrefix z v) → x ∈ bag z)
    {p u₁ u₂ : List Bool} {x : G}
    (hu₁ : u₁.length ≤ h) (hu₂ : u₂.length ≤ h)
    (hx1 : x ∈ bag u₁) (hx2 : x ∈ bag u₂)
    (hp1 : List.IsPrefix p u₁) (hp2 : ¬ List.IsPrefix p u₂) :
    x ∈ bag p := by
  rcases hconn u₁ u₂ x hu₁ hu₂ hx1 hx2 with ⟨b, hbu1, hbu2, hpath⟩
  rcases prefix_comparable hbu1 hp1 with hbp | hpb
  · exact hpath p hbp (Or.inl hp1)
  · exact False.elim (hp2 (hpb.trans hbu2))

private lemma fooling_set_le_pow {n a c w h : ℕ}
    {addr : (Bool × Fin n) → List Bool}
    (hlen : ∀ v, (addr v).length = h)
    {clauses : Fin c → Clause ((Bool × Fin n) ⊕ Fin a)}
    {bag : List Bool → Finset (((Bool × Fin n) ⊕ Fin a) ⊕ Fin c)}
    (hcov : ∀ v, ∃ u : List Bool, u.length ≤ h ∧ v ∈ bag u)
    (hphys : ∀ v, Sum.inl (Sum.inl v) ∈ bag (addr v))
    (hinc : ∀ j : Fin c, ∀ lit ∈ clauses j, ∃ u : List Bool, u.length ≤ h ∧
      Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u)
    (hconn : ∀ (u v : List Bool) (x : ((Bool × Fin n) ⊕ Fin a) ⊕ Fin c),
      u.length ≤ h → v.length ≤ h →
      x ∈ bag u → x ∈ bag v → ∃ b : List Bool,
        List.IsPrefix b u ∧ List.IsPrefix b v ∧
        ∀ z : List Bool, List.IsPrefix b z →
          (List.IsPrefix z u ∨ List.IsPrefix z v) → x ∈ bag z)
    (hbag_le : ∀ u : List Bool, u.length ≤ h → (bag u).card ≤ w)
    {accept : ((Bool × Fin n) → Bool) → Prop}
    (hiff : ∀ x, accept x ↔ ∃ y : Fin a → Bool, ∀ j : Fin c, ClauseSat (Sum.elim x y) (clauses j))
    (p : List Bool) (hp : p.length ≤ h)
    {ι : Type*} [Fintype ι]
    (xf : ι → (Bool × Fin n) → Bool)
    (hacc : ∀ i : ι, accept (xf i))
    (hfool : ∀ i₁ i₂ : ι, i₁ ≠ i₂ →
      ¬ accept (fun v => if List.IsPrefix p (addr v) then xf i₁ v else xf i₂ v) ∨
      ¬ accept (fun v => if List.IsPrefix p (addr v) then xf i₂ v else xf i₁ v)) :
    Fintype.card ι ≤ 2 ^ w := by
  classical
  let Q := (Bool × Fin n) ⊕ Fin a
  let G := Q ⊕ Fin c
  have hwit : ∀ i : ι, ∃ y : Fin a → Bool, ∀ j : Fin c, ClauseSat (Sum.elim (xf i) y) (clauses j) :=
    fun i => (hiff (xf i)).mp (hacc i)
  let yf : ι → Fin a → Bool := fun i => Classical.choose (hwit i)
  have hyf : ∀ i : ι, ∀ j : Fin c, ClauseSat (Sum.elim (xf i) (yf i)) (clauses j) :=
    fun i => Classical.choose_spec (hwit i)
  let guess : ι → ({g : G // g ∈ bag p} → Bool) := fun i g =>
    match g.1 with
    | Sum.inl q => Sum.elim (xf i) (yf i) q
    | Sum.inr j => decide (∃ lit ∈ clauses j, Sum.elim (xf i) (yf i) lit.1 = lit.2 ∧
        ∃ u : List Bool, u.length ≤ h ∧ List.IsPrefix p u ∧
          Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u)
  have hpaste : ∀ i₁ i₂ : ι, guess i₁ = guess i₂ →
      accept (fun v => if List.IsPrefix p (addr v) then xf i₁ v else xf i₂ v) := by
    intro i₁ i₂ hgeq
    let x' : (Bool × Fin n) → Bool := fun v => if List.IsPrefix p (addr v) then xf i₁ v else xf i₂ v
    let y' : Fin a → Bool := fun k =>
      if (∃ u : List Bool, u.length ≤ h ∧ List.IsPrefix p u ∧ Sum.inl (Sum.inr k) ∈ bag u)
      then yf i₁ k else yf i₂ k
    have hbag_var : ∀ q : Q, Sum.inl q ∈ bag p →
        Sum.elim (xf i₁) (yf i₁) q = Sum.elim (xf i₂) (yf i₂) q := by
      intro q hq
      have h := congrFun hgeq ⟨Sum.inl q, hq⟩
      simpa [guess] using h
    have hagree_in : ∀ q : Q, ∀ u : List Bool, u.length ≤ h → List.IsPrefix p u →
        Sum.inl q ∈ bag u → Sum.elim x' y' q = Sum.elim (xf i₁) (yf i₁) q := by
      intro q u hu hpu hqu
      cases q with
      | inl v =>
        simp only [Sum.elim_inl, x']
        by_cases hpv : List.IsPrefix p (addr v)
        · simp [hpv]
        · simp only [hpv, ↓reduceIte]
          have hvp : Sum.inl (Sum.inl v) ∈ bag p :=
            bag_separates hconn hu (le_of_eq (hlen v)) hqu (hphys v) hpu hpv
          exact (hbag_var (Sum.inl v) hvp).symm
      | inr k =>
        simp only [Sum.elim_inr, y']
        rw [if_pos ⟨u, hu, hpu, hqu⟩]
    have hagree_out : ∀ q : Q, ∀ u : List Bool, u.length ≤ h → ¬ List.IsPrefix p u →
        Sum.inl q ∈ bag u → Sum.elim x' y' q = Sum.elim (xf i₂) (yf i₂) q := by
      intro q u hu hnpu hqu
      cases q with
      | inl v =>
        simp only [Sum.elim_inl, x']
        by_cases hpv : List.IsPrefix p (addr v)
        · simp only [hpv, ↓reduceIte]
          have hvp : Sum.inl (Sum.inl v) ∈ bag p :=
            bag_separates hconn (le_of_eq (hlen v)) hu (hphys v) hqu hpv hnpu
          exact hbag_var (Sum.inl v) hvp
        · simp [hpv]
      | inr k =>
        simp only [Sum.elim_inr, y']
        by_cases hin : ∃ u1 : List Bool, u1.length ≤ h ∧ List.IsPrefix p u1 ∧ Sum.inl (Sum.inr k) ∈ bag u1
        · rw [if_pos hin]
          rcases hin with ⟨u1, hu1, hpu1, hku1⟩
          have hkp : Sum.inl (Sum.inr k) ∈ bag p := bag_separates hconn hu1 hu hku1 hqu hpu1 hnpu
          exact hbag_var (Sum.inr k) hkp
        · rw [if_neg hin]
    rw [hiff]
    refine ⟨y', fun j => ?_⟩
    by_cases hjp : Sum.inr j ∈ bag p
    · by_cases hside : ∃ lit ∈ clauses j, Sum.elim (xf i₁) (yf i₁) lit.1 = lit.2 ∧
          ∃ u : List Bool, u.length ≤ h ∧ List.IsPrefix p u ∧ Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u
      · rcases hside with ⟨lit, hlit, hsat1, u, hu, hpu, hlu, _⟩
        exact ⟨lit, hlit, (hagree_in lit.1 u hu hpu hlu).trans hsat1⟩
      · have hside2 : ¬ ∃ lit ∈ clauses j, Sum.elim (xf i₂) (yf i₂) lit.1 = lit.2 ∧
            ∃ u : List Bool, u.length ≤ h ∧ List.IsPrefix p u ∧ Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u := by
          have hg := congrFun hgeq ⟨Sum.inr j, hjp⟩
          simp only [guess, decide_eq_decide] at hg
          exact fun h => hside (hg.mpr h)
        rcases hyf i₂ j with ⟨lit, hlit, hsat2⟩
        rcases hinc j lit hlit with ⟨u, hu, hlu, hju⟩
        have hnpu : ¬ List.IsPrefix p u := fun hpu => hside2 ⟨lit, hlit, hsat2, u, hu, hpu, hlu, hju⟩
        exact ⟨lit, hlit, (hagree_out lit.1 u hu hnpu hlu).trans hsat2⟩
    · rcases hcov (Sum.inr j) with ⟨u₀, hu₀, hju₀⟩
      by_cases hpu₀ : List.IsPrefix p u₀
      · rcases hyf i₁ j with ⟨lit, hlit, hsat1⟩
        rcases hinc j lit hlit with ⟨u, hu, hlu, hju⟩
        have hpu : List.IsPrefix p u := by
          by_contra hnpu
          exact hjp (bag_separates hconn hu₀ hu hju₀ hju hpu₀ hnpu)
        exact ⟨lit, hlit, (hagree_in lit.1 u hu hpu hlu).trans hsat1⟩
      · rcases hyf i₂ j with ⟨lit, hlit, hsat2⟩
        rcases hinc j lit hlit with ⟨u, hu, hlu, hju⟩
        have hnpu : ¬ List.IsPrefix p u := by
          intro hpu
          exact hjp (bag_separates hconn hu hu₀ hju hju₀ hpu hpu₀)
        exact ⟨lit, hlit, (hagree_out lit.1 u hu hnpu hlu).trans hsat2⟩
  have hinj : Function.Injective guess := by
    intro i₁ i₂ hgeq
    by_contra hne
    rcases hfool i₁ i₂ hne with h1 | h2
    · exact h1 (hpaste i₁ i₂ hgeq)
    · exact h2 (hpaste i₂ i₁ hgeq.symm)
  calc Fintype.card ι
      ≤ Fintype.card ({g : G // g ∈ bag p} → Bool) := Fintype.card_le_of_injective guess hinj
    _ = 2 ^ (bag p).card := by simp
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (hbag_le p hp)

private lemma exists_middle_cut {n h : ℕ} (hn : 4 ≤ n)
    (addr : (Bool × Fin n) → List Bool)
    (hinj : Function.Injective addr) (hlen : ∀ v, (addr v).length = h) :
    ∃ p : List Bool, p.length ≤ h ∧
      2 * n / 3 ≤ (Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v))).card ∧
      (Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v))).card ≤ 4 * n / 3 := by
  let cnt : List Bool → ℕ := fun p =>
    (Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v))).card
  have hstep : ∀ d : ℕ, ∀ p : List Bool, p.length + d = h → 2 * n / 3 ≤ cnt p →
      ∃ q : List Bool, q.length ≤ h ∧ 2 * n / 3 ≤ cnt q ∧ cnt q ≤ 4 * n / 3 := by
    intro d
    induction d with
    | zero =>
      intro p hp hge
      have hplen : p.length = h := by omega
      have hle1 : cnt p ≤ 1 := by
        refine Finset.card_le_one.mpr (fun v₁ hv₁ v₂ hv₂ => ?_)
        have hp1 := (Finset.mem_filter.mp hv₁).2
        have hp2 := (Finset.mem_filter.mp hv₂).2
        have heq1 : p = addr v₁ := List.IsPrefix.eq_of_length hp1 (by rw [hplen, hlen v₁])
        have heq2 : p = addr v₂ := List.IsPrefix.eq_of_length hp2 (by rw [hplen, hlen v₂])
        exact hinj (heq1.symm.trans heq2)
      exact ⟨p, by omega, hge, by omega⟩
    | succ d ih =>
      intro p hp hge
      by_cases hle : cnt p ≤ 4 * n / 3
      · exact ⟨p, by omega, hge, hle⟩
      · have hsplit : cnt (p ++ [false]) + cnt (p ++ [true]) = cnt p := by
          let S := Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v))
          let S0 := Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix (p ++ [false]) (addr v))
          let S1 := Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix (p ++ [true]) (addr v))
          have hdisj : Disjoint S0 S1 := by
            rw [Finset.disjoint_left]; intro v h0 h1
            rcases (Finset.mem_filter.mp h0).2 with ⟨t0, ht0⟩
            rcases (Finset.mem_filter.mp h1).2 with ⟨t1, ht1⟩
            have heq := ht0.trans ht1.symm
            rw [List.append_assoc, List.append_assoc] at heq
            have := List.append_cancel_left heq
            simp at this
          have hunion : S0 ∪ S1 = S := by
            ext v
            simp only [S, S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro (⟨t, ht⟩ | ⟨t, ht⟩)
              · exact ⟨false :: t, by simpa [List.append_assoc] using ht⟩
              · exact ⟨true :: t, by simpa [List.append_assoc] using ht⟩
            · rintro ⟨t, ht⟩
              cases t with
              | nil =>
                have : (addr v).length = p.length := by rw [← ht]; simp
                rw [hlen v] at this; omega
              | cons b bs =>
                cases b
                · exact Or.inl ⟨bs, by simpa [List.append_assoc] using ht⟩
                · exact Or.inr ⟨bs, by simpa [List.append_assoc] using ht⟩
          have hc := congrArg Finset.card hunion
          rw [Finset.card_union_of_disjoint hdisj] at hc
          exact hc
        by_cases h0 : 2 * n / 3 ≤ cnt (p ++ [false])
        · exact ih (p ++ [false]) (by simp; omega) h0
        · exact ih (p ++ [true]) (by simp; omega) (by omega)
  have hroot : cnt [] = 2 * n := by
    simp [cnt]
  exact hstep h [] (by simp) (by rw [hroot]; omega)

private lemma main_bound {n r h a c w : ℕ}
    (hn : 4000000 ≤ n) (hr : 0 < r) (hrn : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hov : ∀ j l : Fin r, j ≠ l → 128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (addr : (Bool × Fin n) → List Bool)
    (hinj : Function.Injective addr) (hlen : ∀ v, (addr v).length = h)
    (clauses : Fin c → Clause ((Bool × Fin n) ⊕ Fin a))
    (bag : List Bool → Finset (((Bool × Fin n) ⊕ Fin a) ⊕ Fin c))
    (hcov : ∀ v, ∃ u : List Bool, u.length ≤ h ∧ v ∈ bag u)
    (hphys : ∀ v, Sum.inl (Sum.inl v) ∈ bag (addr v))
    (hinc : ∀ j : Fin c, ∀ lit ∈ clauses j, ∃ u : List Bool, u.length ≤ h ∧
      Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u)
    (hconn : ∀ (u v : List Bool) (x : ((Bool × Fin n) ⊕ Fin a) ⊕ Fin c),
      u.length ≤ h → v.length ≤ h →
      x ∈ bag u → x ∈ bag v → ∃ b : List Bool,
        List.IsPrefix b u ∧ List.IsPrefix b v ∧
        ∀ z : List Bool, List.IsPrefix b z →
          (List.IsPrefix z u ∨ List.IsPrefix z v) → x ∈ bag z)
    (hbag_le : ∀ u : List Bool, u.length ≤ h → (bag u).card ≤ w)
    (hiff : ∀ x : (Bool × Fin n) → Bool,
      (∀ j : Fin r, 16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card) n ≤ n) ↔
      ∃ y : Fin a → Bool, ∀ j : Fin c, ClauseSat (Sum.elim x y) (clauses j)) :
    (∀ (p : List Bool) (j : Fin r),
      min (Finset.univ.filter (fun i : Fin n =>
        ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, M j i))))).card (n / 128) ≤ w) ∧
    n / 512 + 1 ≤ 2 ^ w := by
  let accept : ((Bool × Fin n) → Bool) → Prop := fun x =>
    ∀ j : Fin r, 16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card) n ≤ n
  let Dmax : ℕ := 17 * n / 32
  have hDmax_ok : 16 * Nat.dist (2 * Dmax) n ≤ n := by
    rw [Nat.dist]; omega
  have hDmax_succ_bad : ∀ D : ℕ, Dmax + 1 ≤ D → ¬ (16 * Nat.dist (2 * D) n ≤ n) := by
    intro D hD; rw [Nat.dist]; omega
  have hpart1 : ∀ (p : List Bool) (j : Fin r),
      min (Finset.univ.filter (fun i : Fin n =>
        ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, M j i))))).card (n / 128) ≤ w := by
    intro p j
    let crossSet := Finset.univ.filter (fun i : Fin n =>
      ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, M j i))))
    by_cases hplen : p.length ≤ h
    · let k := min crossSet.card (n / 128)
      have hk_le_cross : k ≤ crossSet.card := min_le_left _ _
      have hk_le_n : k ≤ n / 128 := min_le_right _ _
      rcases Finset.exists_subset_card_eq hk_le_cross with ⟨S, hSsub, hScard⟩
      have hSc_card : Sᶜ.card = n - k := by rw [Finset.card_compl, Fintype.card_fin, hScard]
      have hDmax_le : Dmax ≤ Sᶜ.card := by omega
      rcases Finset.exists_subset_card_eq hDmax_le with ⟨Dset, hDsub, hDcard⟩
      let d : Fin n → Bool := fun i => decide (i ∈ Dset)
      rcases exists_base_assignment hn hrn M hov j d with ⟨x₀, hx₀j, hx₀l⟩
      let xf : ({i : Fin n // i ∈ S} → Bool) → (Bool × Fin n) → Bool := fun z v =>
        match v with
        | (false, i) => if hi : i ∈ S then xor (x₀ (false, i)) (z ⟨i, hi⟩) else x₀ (false, i)
        | (true, t) =>
            let i := (M j).symm t
            if hi : i ∈ S then xor (x₀ (true, t)) (z ⟨i, hi⟩) else x₀ (true, t)
      have hacc : ∀ z, accept (xf z) := by
        intro z l
        by_cases hlj : l = j
        · subst hlj
          have hfeq : Finset.univ.filter (fun i : Fin n => xf z (false, i) ≠ xf z (true, M l i)) = Dset := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hxj := hx₀j i
            by_cases hi : i ∈ S
            · have hiD : i ∉ Dset := fun h => (Finset.mem_compl.mp (hDsub h)) hi
              simp only [xf, Equiv.symm_apply_apply, hi, ↓reduceDIte]
              have hd0 : d i = false := by simp [d, hiD]
              rw [hd0] at hxj
              have hxe : x₀ (false, i) = x₀ (true, M l i) := bne_eq_false_imp hxj
              rw [hxe]; simp [hiD]
            · simp only [xf, Equiv.symm_apply_apply, hi, ↓reduceDIte]
              by_cases hiD : i ∈ Dset
              · have hd1 : d i = true := by simp [d, hiD]
                rw [hd1] at hxj
                exact ⟨fun _ => hiD, fun _ => bne_eq_true_imp hxj⟩
              · have hd0 : d i = false := by simp [d, hiD]
                rw [hd0] at hxj
                exact ⟨fun hne => absurd (bne_eq_false_imp hxj) hne, fun h => absurd h hiD⟩
          rw [hfeq, hDcard]
          exact hDmax_ok
        · let U : Finset (Bool × Fin n) := S.image (fun i => (false, i)) ∪ S.image (fun i => (true, M j i))
          have hUcard : U.card ≤ 2 * k := by
            calc U.card ≤ (S.image (fun i => (false, i))).card + (S.image (fun i => (true, M j i))).card :=
                  Finset.card_union_le _ _
              _ ≤ S.card + S.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
              _ = 2 * k := by omega
          have hagree : ∀ v : Bool × Fin n, v ∉ U → xf z v = x₀ v := by
            intro ⟨b, t⟩ hv
            cases b
            · have ht : t ∉ S := fun h => hv (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, h, rfl⟩))
              simp [xf, ht]
            · have ht : (M j).symm t ∉ S := fun h => hv (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨(M j).symm t, h, by simp⟩))
              simp [xf, ht]
          have hchg := hamming_change_le (M l) (xf z) x₀ U hagree
          have hbase := hx₀l l hlj
          have htri : Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => xf z (false, i) ≠ xf z (true, M l i))).card) n ≤
              Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x₀ (false, i) ≠ x₀ (true, M l i))).card) n + 2 * U.card := by
            simp only [Nat.dist] at hchg ⊢; omega
          omega
      have hfool : ∀ z₁ z₂ : {i : Fin n // i ∈ S} → Bool, z₁ ≠ z₂ →
          ¬ accept (fun v => if List.IsPrefix p (addr v) then xf z₁ v else xf z₂ v) ∨
          ¬ accept (fun v => if List.IsPrefix p (addr v) then xf z₂ v else xf z₁ v) := by
        intro z₁ z₂ hne
        left
        intro haccp
        have hdiff : ∃ i : {i : Fin n // i ∈ S}, z₁ i ≠ z₂ i := by
          by_contra hall; push Not at hall; exact hne (funext hall)
        rcases hdiff with ⟨⟨i₀, hi₀S⟩, hz0⟩
        let xp : (Bool × Fin n) → Bool := fun v => if List.IsPrefix p (addr v) then xf z₁ v else xf z₂ v
        have hDsub_p : Dset ⊆ Finset.univ.filter (fun i : Fin n => xp (false, i) ≠ xp (true, M j i)) := by
          intro i hiD
          have hiS : i ∉ S := Finset.mem_compl.mp (hDsub hiD)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, xp, xf, Equiv.symm_apply_apply, hiS, ↓reduceDIte, ite_self]
          have hxj := hx₀j i
          have hd1 : d i = true := by simp [d, hiD]
          rw [hd1] at hxj
          exact bne_eq_true_imp hxj
        have hi₀_in : i₀ ∈ Finset.univ.filter (fun i : Fin n => xp (false, i) ≠ xp (true, M j i)) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, xp, xf, Equiv.symm_apply_apply, hi₀S, ↓reduceDIte]
          have hi₀D : i₀ ∉ Dset := fun h => (Finset.mem_compl.mp (hDsub h)) hi₀S
          have hxj := hx₀j i₀
          have hd0 : d i₀ = false := by simp [d, hi₀D]
          rw [hd0] at hxj
          have hxe : x₀ (false, i₀) = x₀ (true, M j i₀) := bne_eq_false_imp hxj
          have hcr := (Finset.mem_filter.mp (hSsub hi₀S)).2
          rw [hxe]
          by_cases hpf : List.IsPrefix p (addr (false, i₀))
          · have hpt : ¬ List.IsPrefix p (addr (true, M j i₀)) := fun h => hcr ⟨fun _ => h, fun _ => hpf⟩
            simp only [hpf, hpt, ↓reduceIte]
            exact xor_ne_xor_of_ne hz0
          · have hpt : List.IsPrefix p (addr (true, M j i₀)) := by
              by_contra hnt; exact hcr ⟨fun h => absurd h hpf, fun h => absurd h hnt⟩
            simp only [hpf, hpt, ↓reduceIte]
            exact xor_ne_xor_of_ne hz0.symm
        have hi₀_notD : i₀ ∉ Dset := fun h => (Finset.mem_compl.mp (hDsub h)) hi₀S
        have hcard_ge : Dmax + 1 ≤ (Finset.univ.filter (fun i : Fin n => xp (false, i) ≠ xp (true, M j i))).card := by
          have hsub' : insert i₀ Dset ⊆ Finset.univ.filter (fun i : Fin n => xp (false, i) ≠ xp (true, M j i)) :=
            Finset.insert_subset_iff.mpr ⟨hi₀_in, hDsub_p⟩
          have hc := Finset.card_le_card hsub'
          rw [Finset.card_insert_of_notMem hi₀_notD, hDcard] at hc
          exact hc
        exact hDmax_succ_bad _ hcard_ge (haccp j)
      have hpow := fooling_set_le_pow hlen hcov hphys hinc hconn hbag_le hiff p hplen xf hacc hfool
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hScard] at hpow
      exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow
    · have hemp : crossSet = ∅ := by
        ext i; simp only [crossSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_not]
        have hf : ¬ List.IsPrefix p (addr (false, i)) := fun hp => by
          have := hp.length_le; rw [hlen] at this; omega
        have ht : ¬ List.IsPrefix p (addr (true, M j i)) := fun hp => by
          have := hp.length_le; rw [hlen] at this; omega
        exact ⟨fun h => absurd h hf, fun h => absurd h ht⟩
      change min crossSet.card (n / 128) ≤ w
      rw [hemp]; simp
  refine ⟨hpart1, ?_⟩
  rcases exists_middle_cut (by omega) addr hinj hlen with ⟨p, hplen, hL_lo, hL_hi⟩
  let j0 : Fin r := ⟨0, hr⟩
  let crossSet := Finset.univ.filter (fun i : Fin n =>
    ¬ (List.IsPrefix p (addr (false, i)) ↔ List.IsPrefix p (addr (true, M j0 i))))
  by_cases hcr_big : n / 128 ≤ crossSet.card
  · have hw_big : n / 128 ≤ w := by
      have h := hpart1 p j0
      rwa [min_eq_right hcr_big] at h
    have hpow_le : n / 512 + 1 ≤ 2 ^ (n / 128) := by
      have hk : n / 512 + 1 ≤ n / 128 := by omega
      exact le_trans hk (le_of_lt Nat.lt_two_pow_self)
    exact le_trans hpow_le (Nat.pow_le_pow_right (by omega) hw_big)
  · push Not at hcr_big
    let PL := Finset.univ.filter (fun i : Fin n =>
      List.IsPrefix p (addr (false, i)) ∧ List.IsPrefix p (addr (true, M j0 i)))
    let PR := Finset.univ.filter (fun i : Fin n =>
      ¬ List.IsPrefix p (addr (false, i)) ∧ ¬ List.IsPrefix p (addr (true, M j0 i)))
    have hcount_L : 2 * PL.card + crossSet.card =
        (Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v))).card := by
      let Lf := Finset.univ.filter (fun i : Fin n => List.IsPrefix p (addr (false, i)))
      let Lt := Finset.univ.filter (fun i : Fin n => List.IsPrefix p (addr (true, M j0 i)))
      have hLsum : (Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v))).card = Lf.card + Lt.card := by
        let S0 := Lf.image (fun i => (false, i))
        let S1 := Lt.image (fun i => (true, M j0 i))
        have hdisj : Disjoint S0 S1 := by
          rw [Finset.disjoint_left]; intro v h0 h1
          rcases Finset.mem_image.mp h0 with ⟨_, _, rfl⟩
          rcases Finset.mem_image.mp h1 with ⟨_, _, h⟩; cases h
        have hunion : S0 ∪ S1 = Finset.univ.filter (fun v : Bool × Fin n => List.IsPrefix p (addr v)) := by
          ext ⟨b, k⟩
          cases b
          · simp [S0, S1, Lf]
          · simp only [S0, S1, Lt, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro (⟨_, _, h⟩ | ⟨i, hi, h⟩)
              · cases h
              · cases h; exact hi
            · intro hk; exact Or.inr ⟨(M j0).symm k, by simpa using hk, by simp⟩
        have hc := congrArg Finset.card hunion
        rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ (fun _ _ h => by simpa using h),
            Finset.card_image_of_injective _ (fun _ _ h => (M j0).injective (by simpa using h))] at hc
        exact hc.symm
      have hPLeq : PL = Lf ∩ Lt := by ext i; simp [PL, Lf, Lt]
      have hcreq : crossSet = (Lf \ Lt) ∪ (Lt \ Lf) := by
        ext i; simp only [crossSet, Lf, Lt, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      have hdisj_cr : Disjoint (Lf \ Lt) (Lt \ Lf) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
      have h1 : (Lf \ Lt).card + (Lf ∩ Lt).card = Lf.card := Finset.card_sdiff_add_card_inter Lf Lt
      have h2 : (Lt \ Lf).card + (Lt ∩ Lf).card = Lt.card := Finset.card_sdiff_add_card_inter Lt Lf
      rw [Finset.inter_comm] at h2
      rw [hLsum, hPLeq, hcreq, Finset.card_union_of_disjoint hdisj_cr]
      omega
    have hcount_tot : PL.card + PR.card + crossSet.card = n := by
      have hdisj1 : Disjoint PL PR := by
        rw [Finset.disjoint_left]; intro i h1 h2
        exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      have hdisj2 : Disjoint (PL ∪ PR) crossSet := by
        rw [Finset.disjoint_left]; intro i h1 h2
        have hc := (Finset.mem_filter.mp h2).2
        rcases Finset.mem_union.mp h1 with hL | hR
        · rcases (Finset.mem_filter.mp hL).2 with ⟨a1, a2⟩; exact hc ⟨fun _ => a2, fun _ => a1⟩
        · rcases (Finset.mem_filter.mp hR).2 with ⟨a1, a2⟩; exact hc ⟨fun h => absurd h a1, fun h => absurd h a2⟩
      have hunion : PL ∪ PR ∪ crossSet = Finset.univ := by
        ext i; simp only [PL, PR, crossSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        tauto
      have hc := congrArg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
          Finset.card_univ, Fintype.card_fin] at hc
      exact hc
    let t := n / 512
    have hPL_ge : t ≤ PL.card := by omega
    have hPR_ge : t ≤ PR.card := by omega
    rcases Finset.exists_subset_card_eq hPL_ge with ⟨AL, hALsub, hALcard⟩
    rcases Finset.exists_subset_card_eq hPR_ge with ⟨AR, hARsub, hARcard⟩
    have hdisj_LR : Disjoint AL AR := by
      rw [Finset.disjoint_left]; intro i h1 h2
      exact (Finset.mem_filter.mp (hARsub h2)).2.1 (Finset.mem_filter.mp (hALsub h1)).2.1
    let rem := (Finset.univ \ (AL ∪ AR))
    have hrem_card : rem.card = n - 2 * t := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
          Finset.card_union_of_disjoint hdisj_LR, Finset.card_univ, Fintype.card_fin, hALcard, hARcard]
      omega
    have hneed_le : Dmax - t ≤ rem.card := by omega
    rcases Finset.exists_subset_card_eq hneed_le with ⟨Dextra, hDex_sub, hDex_card⟩
    let Dset := AR ∪ Dextra
    have hdisj_AR_ex : Disjoint AR Dextra := by
      rw [Finset.disjoint_left]; intro i h1 h2
      have := (Finset.mem_sdiff.mp (hDex_sub h2)).2
      exact this (Finset.mem_union_right _ h1)
    have hdisj_AL_D : Disjoint AL Dset := by
      rw [Finset.disjoint_left]; intro i h1 h2
      rcases Finset.mem_union.mp h2 with hAR | hEx
      · exact Finset.disjoint_left.mp hdisj_LR h1 hAR
      · exact (Finset.mem_sdiff.mp (hDex_sub hEx)).2 (Finset.mem_union_left _ h1)
    have hDcard : Dset.card = Dmax := by
      rw [Finset.card_union_of_disjoint hdisj_AR_ex, hARcard, hDex_card]; omega
    let d : Fin n → Bool := fun i => decide (i ∈ Dset)
    rcases exists_base_assignment hn hrn M hov j0 d with ⟨x₀, hx₀j, hx₀l⟩
    let eL : Fin t ≃ AL := (Finset.equivFinOfCardEq hALcard).symm
    let eR : Fin t ≃ AR := (Finset.equivFinOfCardEq hARcard).symm
    let FL : Fin (t + 1) → Finset (Fin n) := fun m =>
      (Finset.univ.filter (fun k : Fin t => k.val < m.val)).image (fun k => (eL k).1)
    let FR : Fin (t + 1) → Finset (Fin n) := fun m =>
      (Finset.univ.filter (fun k : Fin t => k.val < m.val)).image (fun k => (eR k).1)
    have hFL_card : ∀ m : Fin (t + 1), (FL m).card = m.val := by
      intro m
      rw [Finset.card_image_of_injective _ (fun a b h => eL.injective (Subtype.ext h))]
      have : (Finset.univ.filter (fun k : Fin t => k.val < m.val)).card = m.val := by
        have hm : m.val ≤ t := Nat.le_of_lt_succ m.isLt
        have hbij : Finset.univ.filter (fun k : Fin t => k.val < m.val) =
            (Finset.range m.val).attach.image (fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hm⟩) := by
          ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach, Subtype.exists]
          constructor
          · intro hk; exact ⟨k.val, Finset.mem_range.mpr hk, rfl⟩
          · rintro ⟨a, ha, rfl⟩; exact Finset.mem_range.mp ha
        rw [hbij, Finset.card_image_of_injective _ (fun a b h => Subtype.ext (congrArg Fin.val h)),
            Finset.card_attach, Finset.card_range]
      exact this
    have hFR_card : ∀ m : Fin (t + 1), (FR m).card = m.val := by
      intro m
      rw [Finset.card_image_of_injective _ (fun a b h => eR.injective (Subtype.ext h))]
      have hm : m.val ≤ t := Nat.le_of_lt_succ m.isLt
      have hbij : Finset.univ.filter (fun k : Fin t => k.val < m.val) =
          (Finset.range m.val).attach.image (fun x => ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hm⟩) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_attach, Subtype.exists]
        constructor
        · intro hk; exact ⟨k.val, Finset.mem_range.mpr hk, rfl⟩
        · rintro ⟨a, ha, rfl⟩; exact Finset.mem_range.mp ha
      rw [hbij, Finset.card_image_of_injective _ (fun a b h => Subtype.ext (congrArg Fin.val h)),
          Finset.card_attach, Finset.card_range]
    have hFL_sub : ∀ m, FL m ⊆ AL := by
      intro m i hi; rcases Finset.mem_image.mp hi with ⟨k, _, rfl⟩; exact (eL k).2
    have hFR_sub : ∀ m, FR m ⊆ AR := by
      intro m i hi; rcases Finset.mem_image.mp hi with ⟨k, _, rfl⟩; exact (eR k).2
    let xf : Fin (t + 1) → (Bool × Fin n) → Bool := fun m v =>
      match v with
      | (false, i) => if (i ∈ FL m ∨ i ∈ FR m) then !(x₀ (false, i)) else x₀ (false, i)
      | (true, k) => x₀ (true, k)
    have hDj_paste : ∀ m₁ m₂ : Fin (t + 1),
        let xp : (Bool × Fin n) → Bool := fun v => if List.IsPrefix p (addr v) then xf m₁ v else xf m₂ v
        (Finset.univ.filter (fun i : Fin n => xp (false, i) ≠ xp (true, M j0 i))).card =
          Dmax + m₁.val - m₂.val := by
      intro m₁ m₂ xp
      have hset : Finset.univ.filter (fun i : Fin n => xp (false, i) ≠ xp (true, M j0 i)) =
          (Dset \ FR m₂) ∪ FL m₁ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_sdiff, xp]
        have htrue : (if List.IsPrefix p (addr (true, M j0 i)) then xf m₁ (true, M j0 i) else xf m₂ (true, M j0 i)) =
            x₀ (true, M j0 i) := by simp [xf]
        rw [htrue]
        have hxj := hx₀j i
        by_cases hL : i ∈ FL m₁
        · have hAL : i ∈ AL := hFL_sub m₁ hL
          have hpf : List.IsPrefix p (addr (false, i)) := (Finset.mem_filter.mp (hALsub hAL)).2.1
          have hnotD : i ∉ Dset := Finset.disjoint_left.mp hdisj_AL_D hAL
          have hd0 : d i = false := by simp [d, hnotD]
          rw [hd0] at hxj
          simp only [hpf, ↓reduceIte, xf, hL, true_or, or_true, iff_true]
          have hxe := bne_eq_false_imp hxj
          rw [hxe]; cases x₀ (true, M j0 i) <;> decide
        · by_cases hR : i ∈ FR m₂
          · have hAR : i ∈ AR := hFR_sub m₂ hR
            have hnpf : ¬ List.IsPrefix p (addr (false, i)) := (Finset.mem_filter.mp (hARsub hAR)).2.1
            have hD : i ∈ Dset := Finset.mem_union_left _ hAR
            have hd1 : d i = true := by simp [d, hD]
            rw [hd1] at hxj
            simp only [hnpf, ↓reduceIte, xf, hR, or_true, hL, or_false, not_true_eq_false, and_false, iff_false, not_not]
            have hne := bne_eq_true_imp hxj
            cases h1 : x₀ (false, i) <;> cases h2 : x₀ (true, M j0 i)
            · exact absurd (h1.trans h2.symm) hne
            · rfl
            · rfl
            · exact absurd (h1.trans h2.symm) hne
          · have hflip_false : (if List.IsPrefix p (addr (false, i)) then xf m₁ (false, i) else xf m₂ (false, i)) =
                x₀ (false, i) := by
              by_cases hpf : List.IsPrefix p (addr (false, i))
              · have hnotR1 : i ∉ FR m₁ := fun h => (Finset.mem_filter.mp (hARsub (hFR_sub m₁ h))).2.1 hpf
                simp [hpf, xf, hL, hnotR1]
              · have hnotL2 : i ∉ FL m₂ := fun h => hpf (Finset.mem_filter.mp (hALsub (hFL_sub m₂ h))).2.1
                simp [hpf, xf, hnotL2, hR]
            rw [hflip_false]
            simp only [hR, not_false_eq_true, and_true, hL, or_false]
            by_cases hiD : i ∈ Dset
            · have hd1 : d i = true := by simp [d, hiD]
              rw [hd1] at hxj
              exact ⟨fun _ => hiD, fun _ => bne_eq_true_imp hxj⟩
            · have hd0 : d i = false := by simp [d, hiD]
              rw [hd0] at hxj
              exact ⟨fun hne => absurd (bne_eq_false_imp hxj) hne, fun h => absurd h hiD⟩
      rw [hset]
      have hdisj_u : Disjoint (Dset \ FR m₂) (FL m₁) := by
        rw [Finset.disjoint_left]; intro i h1 h2
        exact Finset.disjoint_left.mp hdisj_AL_D (hFL_sub m₁ h2) (Finset.mem_sdiff.mp h1).1
      have hsub_R : FR m₂ ⊆ Dset := fun i hi => Finset.mem_union_left _ (hFR_sub m₂ hi)
      rw [Finset.card_union_of_disjoint hdisj_u, Finset.card_sdiff,
          Finset.inter_eq_left.mpr hsub_R, hDcard, hFL_card m₁, hFR_card m₂]
      have htm : m₂.val ≤ Dmax := by have := m₂.isLt; omega
      omega
    have hacc : ∀ m : Fin (t + 1), accept (xf m) := by
      intro m l
      by_cases hlj : l = j0
      · rw [hlj]
        have heq : (Finset.univ.filter (fun i : Fin n => xf m (false, i) ≠ xf m (true, M j0 i))).card = Dmax := by
          have h := hDj_paste m m
          simp only [ite_self] at h
          have : Dmax + m.val - m.val = Dmax := by omega
          exact h.trans this
        rw [heq]; exact hDmax_ok
      · let U : Finset (Bool × Fin n) := (FL m ∪ FR m).image (fun i => (false, i))
        have hUcard : U.card ≤ 2 * t := by
          calc U.card ≤ (FL m ∪ FR m).card := Finset.card_image_le
            _ ≤ (FL m).card + (FR m).card := Finset.card_union_le _ _
            _ = 2 * m.val := by rw [hFL_card m, hFR_card m]; omega
            _ ≤ 2 * t := by have := m.isLt; omega
        have hagree : ∀ v : Bool × Fin n, v ∉ U → xf m v = x₀ v := by
          intro ⟨b, k⟩ hv
          cases b
          · have hk : ¬ (k ∈ FL m ∨ k ∈ FR m) := fun h => hv (Finset.mem_image.mpr ⟨k, by simpa using h, rfl⟩)
            simp [xf, hk]
          · simp [xf]
        have hchg := hamming_change_le (M l) (xf m) x₀ U hagree
        have hbase := hx₀l l hlj
        have htri : Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => xf m (false, i) ≠ xf m (true, M l i))).card) n ≤
            Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x₀ (false, i) ≠ x₀ (true, M l i))).card) n + 2 * U.card := by
          simp only [Nat.dist] at hchg ⊢; omega
        omega
    have hfool : ∀ m₁ m₂ : Fin (t + 1), m₁ ≠ m₂ →
        ¬ accept (fun v => if List.IsPrefix p (addr v) then xf m₁ v else xf m₂ v) ∨
        ¬ accept (fun v => if List.IsPrefix p (addr v) then xf m₂ v else xf m₁ v) := by
      intro m₁ m₂ hne
      have hne_val : m₁.val ≠ m₂.val := fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hne_val with hlt | hgt
      · right
        intro haccp
        have hc := hDj_paste m₂ m₁
        have hge : Dmax + 1 ≤ Dmax + m₂.val - m₁.val := by omega
        exact hDmax_succ_bad _ (hc ▸ hge) (haccp j0)
      · left
        intro haccp
        have hc := hDj_paste m₁ m₂
        have hge : Dmax + 1 ≤ Dmax + m₁.val - m₂.val := by omega
        exact hDmax_succ_bad _ (hc ▸ hge) (haccp j0)
    have hpow := fooling_set_le_pow hlen hcov hphys hinc hconn hbag_le hiff p hplen xf hacc hfool
    simpa [t] using hpow

end PEqualNP.Outside.L_pcx_322_aux

theorem PEqualNP.Outside.L_pcx_322 : (∃ N : ℕ, ∀ (n r : ℕ), N ≤ n → 0 < r → 8192*r < n →
  ∀ M : Fin r → Equiv.Perm (Fin n),
    (∀ j l : Fin r, j ≠ l →
      128*(Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
    let V := Bool × Fin n
    let X := V → Bool
    let accept := fun x : X => ∀ j : Fin r,
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      16 * Nat.dist (2*D) n ≤ n
    ∀ (h : ℕ) (addr : V → List Bool), Function.Injective addr →
      (∀ v : V, (addr v).length = h) →
      let crosses := fun (p : List Bool) (j : Fin r) =>
        (Finset.univ.filter (fun i : Fin n =>
          ¬ (List.IsPrefix p (addr (false,i)) ↔ List.IsPrefix p (addr (true,M j i))))).card
      ∀ (a c w : ℕ),
        let Q := V ⊕ Fin a
        let G := Q ⊕ Fin c
        ∀ (clauses : Fin c → PEqualNP.ProofComplexity.Clause Q) (bag : List Bool → Finset G),
          let valid := (∀ v : G, ∃ u : List Bool, u.length ≤ h ∧ v ∈ bag u) ∧
            (∀ v : V, Sum.inl (Sum.inl v) ∈ bag (addr v)) ∧
            (∀ j : Fin c, ∀ lit ∈ clauses j, ∃ u : List Bool, u.length ≤ h ∧
              Sum.inl lit.1 ∈ bag u ∧ Sum.inr j ∈ bag u) ∧
            (∀ (u v : List Bool) (x : G), u.length ≤ h → v.length ≤ h →
              x ∈ bag u → x ∈ bag v → ∃ b : List Bool,
                List.IsPrefix b u ∧ List.IsPrefix b v ∧
                ∀ z : List Bool, List.IsPrefix b z →
                  (List.IsPrefix z u ∨ List.IsPrefix z v) → x ∈ bag z)
          let sat := fun (x : X) (y : Fin a → Bool) =>
            ∀ j : Fin c, PEqualNP.ProofComplexity.ClauseSat (Sum.elim x y) (clauses j)
          valid → (∀ u : List Bool, u.length ≤ h → (bag u).card ≤ w) →
          (∀ x : X, accept x ↔ ∃ y : Fin a → Bool, sat x y) →
          (∀ (p : List Bool) (j : Fin r), min (crosses p j) (n/128) ≤ w) ∧
          n/512 + 1 ≤ 2^w) := by
  refine ⟨4000000, fun n r hn hr hrn M hov h addr hinj hlen a c w clauses bag hval hbag hiff =>
    PEqualNP.Outside.L_pcx_322_aux.main_bound hn hr hrn M hov addr hinj hlen clauses bag
      hval.1 hval.2.1 hval.2.2.1 hval.2.2.2 hbag hiff⟩
