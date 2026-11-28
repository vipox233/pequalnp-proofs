import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1026_aux.Lower
open Finset
def kk {q : ℕ} (a b : Fin q) : ℚ := if a = b then -1 else 1
def KK {q m : ℕ} (x y : Fin m → Fin q) : ℚ := ∏ i, kk (x i) (y i)
def mu {q : ℕ} (a b : Fin q) : ℚ := (if a = b then ((q:ℚ) - 3) else 1) / (2 * ((q:ℚ) - 2))
def MM {q m : ℕ} (x y : Fin m → Fin q) : ℚ := ∏ i, mu (x i) (y i)
def hd {q m : ℕ} (x y : Fin m → Fin q) : ℕ := (univ.filter (fun i => x i ≠ y i)).card
def rho (q : ℕ) : ℚ := ((q:ℚ) - 4) / q
def nu {q : ℕ} (a b : Fin q) : ℚ := kk a b * mu a b
def F3 {q : ℕ} (a a' c : Fin q) : ℚ := ∑ b, nu a b * nu a' b / mu c b
def gg {q : ℕ} (c1 : ℚ) (a a' c : Fin q) : ℚ :=
  if c = a then (if c = a' then 1 else 0) else (if c = a' then 0 else c1)
lemma sum_prod {q m : ℕ} (φ : Fin m → Fin q → ℚ) :
    ∑ y : Fin m → Fin q, ∏ i, φ i (y i) = ∏ i, ∑ b, φ i b := (Fintype.prod_sum φ).symm
lemma sum_ite1 {q : ℕ} (a : Fin q) (u v : ℚ) :
    ∑ b : Fin q, (if a = b then u else v) = u + ((q:ℚ) - 1) * v := by
  have : ∀ b : Fin q, (if a = b then u else v) = v + (if a = b then (u - v) else 0) := by
    intro b; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring
lemma sum_ite2 {q : ℕ} (a c : Fin q) (hac : a ≠ c) (u w v : ℚ) :
    ∑ b : Fin q, (if a = b then u else if c = b then w else v) = u + w + ((q:ℚ) - 2) * v := by
  have : ∀ b : Fin q, (if a = b then u else if c = b then w else v) =
      v + (if a = b then (u - v) else 0) + (if c = b then (w - v) else 0) := by
    intro b
    rcases eq_or_ne a b with h1 | h1
    · have h2 : c ≠ b := fun h2 => hac (h1.trans h2.symm)
      simp only [if_pos h1, if_neg h2]; ring
    · simp only [if_neg h1]
      rcases eq_or_ne c b with h2 | h2
      · simp only [if_pos h2]; ring
      · simp only [if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun b _ => this b), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring
lemma kk_sq {q : ℕ} (a b : Fin q) : kk a b * kk a b = 1 := by
  unfold kk; split_ifs <;> norm_num
lemma abs_kk {q : ℕ} (a b : Fin q) : |kk a b| = 1 := by
  unfold kk; split_ifs <;> norm_num
lemma sum_kk_kk {q : ℕ} (a a' : Fin q) :
    ∑ b, kk a b * kk a' b = if a = a' then (q:ℚ) else (q:ℚ) - 4 := by
  split_ifs with h
  · subst h; simp [kk_sq]
  · have : ∀ b, kk a b * kk a' b = if a = b then -1 else if a' = b then -1 else 1 := by
      intro b
      unfold kk
      rcases eq_or_ne a b with h1 | h1
      · have h2 : a' ≠ b := fun h2 => h (h1.trans h2.symm)
        simp only [if_pos h1, if_neg h2]; ring
      · simp only [if_neg h1]
        rcases eq_or_ne a' b with h2 | h2
        · simp only [if_pos h2]; ring
        · simp only [if_neg h2]; ring
    rw [Finset.sum_congr rfl (fun b _ => this b), sum_ite2 a a' h]; ring
lemma gram_KK {q m : ℕ} (hq : 5 ≤ q) (x x' : Fin m → Fin q) :
    ∑ y, KK x y * KK x' y = (q:ℚ)^m * rho q ^ hd x x' := by
  have h1 : ∀ y : Fin m → Fin q, KK x y * KK x' y = ∏ i, (kk (x i) (y i) * kk (x' i) (y i)) := by
    intro y; unfold KK; rw [prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun y _ => h1 y), sum_prod (fun i b => kk (x i) b * kk (x' i) b)]
  simp only [sum_kk_kk]
  have hq0 : (q:ℚ) ≠ 0 := by
    have : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    exact this.ne'
  have h2 : ∀ i, (if x i = x' i then (q:ℚ) else (q:ℚ) - 4) =
      (q:ℚ) * (if x i = x' i then 1 else rho q) := by
    intro i; unfold rho; split_ifs <;> field_simp
  rw [Finset.prod_congr rfl (fun i _ => h2 i), prod_mul_distrib, prod_const, card_univ,
    Fintype.card_fin, prod_ite]
  simp [hd]
lemma mu_pos {q : ℕ} (hq : 5 ≤ q) (a b : Fin q) : 0 < mu a b := by
  unfold mu
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  apply div_pos
  · split_ifs <;> linarith
  · linarith
lemma mu_le_one {q : ℕ} (hq : 5 ≤ q) (a b : Fin q) : mu a b ≤ 1 := by
  unfold mu
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  rw [div_le_one (by linarith)]
  split_ifs <;> linarith
lemma mu_ge {q : ℕ} (hq : 5 ≤ q) (a b : Fin q) : 1 / (2 * ((q:ℚ) - 2)) ≤ mu a b := by
  unfold mu
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  apply div_le_div_of_nonneg_right _ (by linarith)
  split_ifs <;> linarith
lemma sum_mu {q : ℕ} (hq : 5 ≤ q) (c : Fin q) : ∑ b, mu c b = 1 := by
  unfold mu
  rw [← sum_div, sum_ite1]
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  rw [div_eq_one_iff_eq (by linarith)]
  ring
lemma sum_MM {q m : ℕ} (hq : 5 ≤ q) (x : Fin m → Fin q) : ∑ y, MM x y = 1 := by
  unfold MM
  rw [sum_prod (fun i b => mu (x i) b)]
  simp [sum_mu hq]
lemma MM_pos {q m : ℕ} (hq : 5 ≤ q) (x y : Fin m → Fin q) : 0 < MM x y := by
  unfold MM
  exact prod_pos (fun i _ => mu_pos hq _ _)
lemma abs_KK {q m : ℕ} (x y : Fin m → Fin q) : |KK x y| = 1 := by
  unfold KK
  rw [abs_prod]
  simp [abs_kk]
lemma gram_T {q m : ℕ} (x x' z : Fin m → Fin q) :
    ∑ y, (KK x y * MM x y) * (KK x' y * MM x' y) / MM z y = ∏ i, F3 (x i) (x' i) (z i) := by
  have h1 : ∀ y : Fin m → Fin q, (KK x y * MM x y) * (KK x' y * MM x' y) / MM z y =
      ∏ i, (nu (x i) (y i) * nu (x' i) (y i) / mu (z i) (y i)) := by
    intro y
    unfold KK MM nu
    rw [prod_div_distrib, prod_mul_distrib, prod_mul_distrib, prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun y _ => h1 y),
    sum_prod (fun i b => nu (x i) b * nu (x' i) b / mu (z i) b)]
  rfl
lemma F3_ccc {q : ℕ} (hq : 5 ≤ q) (c : Fin q) : F3 c c c = 1 := by
  unfold F3
  rw [← sum_mu hq c]
  apply Finset.sum_congr rfl
  intro b _
  have hm := (mu_pos hq c b).ne'
  unfold nu
  field_simp
  have := kk_sq c b
  nlinarith [this]
lemma F3_acc {q : ℕ} (hq : 5 ≤ q) (a c : Fin q) (h : a ≠ c) : F3 a c c = 0 := by
  unfold F3
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  have hD : (2 * ((q:ℚ) - 2)) ≠ 0 := by linarith
  have : ∀ b : Fin q, nu a b * nu c b / mu c b =
      if a = b then -((q:ℚ) - 3) / (2 * ((q:ℚ) - 2)) else
        if c = b then -1 / (2 * ((q:ℚ) - 2)) else 1 / (2 * ((q:ℚ) - 2)) := by
    intro b
    have hm := (mu_pos hq c b).ne'
    have e1 : nu a b * nu c b / mu c b = kk a b * mu a b * kk c b := by
      unfold nu; field_simp
    rw [e1]
    unfold kk mu
    rcases eq_or_ne a b with h1 | h1
    · have h2 : c ≠ b := fun h2 => h (h1.trans h2.symm)
      simp only [if_pos h1, if_neg h2]; ring
    · simp only [if_neg h1]
      rcases eq_or_ne c b with h2 | h2
      · simp only [if_pos h2]; ring
      · simp only [if_neg h2]; ring
  rw [Finset.sum_congr rfl (fun b _ => this b), sum_ite2 a c h]
  field_simp
  ring
lemma F3_comm {q : ℕ} (a a' c : Fin q) : F3 a a' c = F3 a' a c := by
  unfold F3
  apply Finset.sum_congr rfl
  intro b _
  ring
lemma F3_abs {q : ℕ} (hq : 5 ≤ q) (a a' c : Fin q) : |F3 a a' c| ≤ 2 * q * ((q:ℚ) - 2) := by
  unfold F3
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ b : Fin q, |nu a b * nu a' b / mu c b| ≤ 2 * ((q:ℚ) - 2) := by
    intro b
    have hm := mu_pos hq c b
    have hge := mu_ge hq c b
    have hn1 : |nu a b| ≤ 1 := by
      unfold nu; rw [abs_mul, abs_kk, one_mul, abs_of_pos (mu_pos hq a b)]; exact mu_le_one hq a b
    have hn2 : |nu a' b| ≤ 1 := by
      unfold nu; rw [abs_mul, abs_kk, one_mul, abs_of_pos (mu_pos hq a' b)]; exact mu_le_one hq a' b
    rw [abs_div, abs_mul, abs_of_pos hm, div_le_iff₀ hm]
    have hq2 : 0 < 2 * ((q:ℚ) - 2) := by linarith
    have : 1 ≤ 2 * ((q:ℚ) - 2) * mu c b := by
      have := mul_le_mul_of_nonneg_left hge hq2.le
      rwa [mul_one_div_cancel hq2.ne'] at this
    nlinarith [abs_nonneg (nu a b), abs_nonneg (nu a' b)]
  refine (Finset.sum_le_sum (fun b _ => this b)).trans ?_
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  nlinarith
lemma F3_le_gg {q : ℕ} (hq : 5 ≤ q) (a a' c : Fin q) :
    |F3 a a' c| ≤ gg (2 * q * ((q:ℚ) - 2)) a a' c := by
  unfold gg
  rcases eq_or_ne c a with h1 | h1
  · subst h1
    rcases eq_or_ne c a' with h2 | h2
    · subst h2; rw [if_pos rfl, if_pos rfl, F3_ccc hq]; norm_num
    · rw [if_pos rfl, if_neg h2, F3_comm, F3_acc hq a' c (Ne.symm h2)]; norm_num
  · simp only [if_neg h1]
    rcases eq_or_ne c a' with h2 | h2
    · subst h2; rw [if_pos rfl, F3_acc hq a c (Ne.symm h1)]; norm_num
    · simp only [if_neg h2]; exact F3_abs hq a a' c
lemma sum_gg {q : ℕ} (c1 : ℚ) (a c : Fin q) :
    ∑ b, gg c1 a b c = if c = a then 1 else ((q:ℚ) - 1) * c1 := by
  unfold gg
  rcases eq_or_ne c a with h1 | h1
  · simp only [if_pos h1]
    rw [Finset.sum_ite_eq]; simp
  · simp only [if_neg h1]
    rw [sum_ite1]; ring
lemma expand {ι κ : Type*} [Fintype κ] (S : Finset ι) (a : ι → ℚ) (G : ι → κ → ℚ) (w : κ → ℚ) :
    ∑ y, (∑ x ∈ S, a x * G x y) ^ 2 / w y =
      ∑ x ∈ S, ∑ x' ∈ S, a x * a x' * ∑ y, G x y * G x' y / w y := by
  simp_rw [sq, sum_mul_sum, sum_div, mul_sum]
  rw [sum_comm]
  apply Finset.sum_congr rfl; intro x _
  rw [sum_comm]
  apply Finset.sum_congr rfl; intro x' _
  apply Finset.sum_congr rfl; intro y _
  ring
lemma amgm {ι : Type*} (s : Finset ι) (F w : ι → ℚ) (t : ℚ) (ht : 0 < t)
    (hw : ∀ i ∈ s, 0 < w i) :
    ∑ i ∈ s, |F i| ≤ (t * ∑ i ∈ s, w i + (∑ i ∈ s, F i ^ 2 / w i) / t) / 2 := by
  rw [mul_sum, sum_div, ← sum_add_distrib, sum_div]
  apply Finset.sum_le_sum; intro i hi
  have hwi := hw i hi
  have h3 : 0 < w i * t := mul_pos hwi ht
  have key : |F i| * 2 * (w i * t) ≤ t * w i * (w i * t) + F i ^ 2 := by
    rw [← sq_abs (F i)]
    nlinarith [sq_nonneg (t * w i - |F i|), abs_nonneg (F i)]
  have e : F i ^ 2 / w i / t = F i ^ 2 / (w i * t) := by rw [div_div]
  rw [e]
  rw [le_div_iff₀ (by norm_num : (0:ℚ) < 2)]
  have : |F i| * 2 ≤ t * w i + F i ^ 2 / (w i * t) := by
    rw [← sub_nonneg]
    have : t * w i + F i ^ 2 / (w i * t) - |F i| * 2 =
        (t * w i * (w i * t) + F i ^ 2 - |F i| * 2 * (w i * t)) / (w i * t) := by
      field_simp
    rw [this]
    apply div_nonneg _ h3.le
    linarith
  linarith
def jj {q m : ℕ} (z x x' : Fin m → Fin q) : ℕ := (univ.filter (fun i => z i ≠ x i ∧ z i = x' i)).card
lemma rho_nonneg {q : ℕ} (hq : 5 ≤ q) : 0 ≤ rho q := by
  unfold rho
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  apply div_nonneg <;> linarith
lemma rho_le_one {q : ℕ} (hq : 5 ≤ q) : rho q ≤ 1 := by
  unfold rho
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  rw [div_le_one (by linarith)]; linarith
lemma rho_lt_one {q : ℕ} (hq : 5 ≤ q) : rho q < 1 := by
  unfold rho
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  rw [div_lt_one (by linarith)]; linarith
lemma hd_ge {q m : ℕ} (z x x' : Fin m → Fin q) : jj z x x' + jj z x' x ≤ hd x x' := by
  unfold jj hd
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases h1 : z i = x i <;> by_cases h2 : z i = x' i <;> by_cases h3 : x i = x' i <;>
    simp_all
lemma ind_le (θ : ℚ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (j t : ℕ) :
    (if j ≤ t then (1:ℚ) else 0) ≤ θ ^ j / θ ^ t := by
  split_ifs with h
  · rw [le_div_iff₀ (pow_pos hθ0 t), one_mul]
    exact pow_le_pow_of_le_one hθ0.le hθ1 h
  · positivity
lemma sum_theta {q m : ℕ} (z x' : Fin m → Fin q) (θ : ℚ) :
    ∑ x : Fin m → Fin q, θ ^ (jj z x x') =
      ∏ i, (if z i = x' i then 1 + ((q:ℚ) - 1) * θ else (q:ℚ)) := by
  have h1 : ∀ x : Fin m → Fin q, θ ^ (jj z x x') =
      ∏ i, (if z i ≠ x i ∧ z i = x' i then θ else 1) := by
    intro x
    rw [prod_ite]; simp [jj]
  rw [Finset.sum_congr rfl (fun x _ => h1 x),
    sum_prod (fun i b => if z i ≠ b ∧ z i = x' i then θ else 1)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : z i = x' i
  · rw [if_pos h]
    have : ∀ b : Fin q, (if z i ≠ b ∧ z i = x' i then θ else 1) = if z i = b then 1 else θ := by
      intro b; by_cases hb : z i = b <;> simp [hb, h]
    rw [Finset.sum_congr rfl (fun b _ => this b), sum_ite1]
  · rw [if_neg h]
    simp [h]
lemma prod_bound {q m : ℕ} (hq : 5 ≤ q) (z x' : Fin m → Fin q) (c : ℚ) (hc : 1 ≤ c) (R : ℕ)
    (hR : hd z x' ≤ R) :
    ∏ i, (if z i = x' i then c else (q:ℚ)) ≤ c ^ m * (q:ℚ) ^ R := by
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  have h1 : ∏ i, (if z i = x' i then c else (q:ℚ)) ≤
      ∏ i : Fin m, (c * (if z i = x' i then 1 else (q:ℚ))) := by
    apply Finset.prod_le_prod₀
    · intro i _; split_ifs <;> linarith
    · intro i _; split_ifs <;> nlinarith
  refine h1.trans ?_
  rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_ite]
  simp only [prod_const_one, one_mul, prod_const]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : (univ.filter (fun i => ¬ z i = x' i)).card ≤ R := by
    have := hR; unfold hd at this; simpa using this
  exact pow_le_pow_right₀ (by linarith) this
lemma bern (m : ℕ) (x : ℚ) (hx0 : 0 ≤ x) (hx : (m:ℚ) * x ≤ 1 / 2) (hx1 : x ≤ 1) :
    (1 + x) ^ m ≤ 2 := by
  have h1 : 1 - (m:ℚ) * x ≤ (1 - x) ^ m := by
    have := one_add_mul_le_pow (a := -x) (by linarith) m
    have e1 : (1:ℚ) + (m:ℚ) * -x = 1 - m * x := by ring
    have e2 : (1:ℚ) + -x = 1 - x := by ring
    rw [e1, e2] at this; exact this
  have h2 : (1 + x) ^ m * (1 - x) ^ m ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ <;> nlinarith
  have h3 : 0 ≤ (1 + x) ^ m := by positivity
  nlinarith [mul_nonneg h3 (show (0:ℚ) ≤ (1 - x) ^ m - 1 / 2 by linarith)]
lemma close_count {q m : ℕ} (hq : 5 ≤ q) (Lm : ℕ) (hm : 0 < Lm) (hmL : m ≤ Lm) (r R : ℕ)
    (z x' : Fin m → Fin q)
    (hR : hd z x' ≤ R) (P : Finset (Fin m → Fin q)) :
    ∑ x ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤
      (2 * ((q:ℚ) - 1) * Lm) ^ (r - 1) * (2 * (q:ℚ) ^ R) := by
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  have hm1 : (1:ℚ) ≤ Lm := by exact_mod_cast hm
  have hmL' : (m:ℚ) ≤ Lm := by exact_mod_cast hmL
  set θ : ℚ := 1 / (2 * ((q:ℚ) - 1) * Lm) with hθ
  have hq1 : (0:ℚ) < (q:ℚ) - 1 := by linarith
  have hD : 0 < 2 * ((q:ℚ) - 1) * Lm := mul_pos (mul_pos two_pos hq1) (by linarith)
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hD]; nlinarith
  have s1 : ∑ x ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤
      ∑ x : Fin m → Fin q, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro i _ _; split_ifs <;> norm_num
  refine s1.trans ?_
  have s2 : ∑ x : Fin m → Fin q, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤
      ∑ x : Fin m → Fin q, θ ^ (jj z x x') / θ ^ (r - 1) :=
    Finset.sum_le_sum (fun x _ => ind_le θ hθ0 hθ1 _ _)
  refine s2.trans ?_
  rw [← sum_div, sum_theta]
  have e : 1 + ((q:ℚ) - 1) * θ = 1 + 1 / (2 * Lm) := by
    rw [hθ]; field_simp [hq1.ne']
  rw [e]
  have hb : (1 + 1 / (2 * (Lm:ℚ))) ^ m ≤ 2 := by
    apply bern
    · positivity
    · rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    · rw [div_le_one (by positivity)]; linarith
  have hp := prod_bound hq z x' (1 + 1 / (2 * (Lm:ℚ))) (by
    have : (0:ℚ) ≤ 1 / (2 * Lm) := by positivity
    linarith) R hR
  have hθr : θ ^ (r - 1) = 1 / (2 * ((q:ℚ) - 1) * Lm) ^ (r - 1) := by
    rw [hθ, one_div_pow]
  rw [hθr, div_div_eq_mul_div, div_one]
  have hqR : (0:ℚ) ≤ (q:ℚ) ^ R := by positivity
  have hpos : (0:ℚ) ≤ (2 * ((q:ℚ) - 1) * Lm) ^ (r - 1) := by positivity
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ hpos
  refine hp.trans ?_
  nlinarith
lemma hd_comp_le {q m t : ℕ} (f : Fin t → Fin m) (hf : Function.Injective f)
    (x y : Fin m → Fin q) : hd (x ∘ f) (y ∘ f) ≤ hd x y := by
  unfold hd
  have hs : (univ.filter (fun i : Fin t => (x ∘ f) i ≠ (y ∘ f) i)).map ⟨f, hf⟩ ⊆
      univ.filter (fun i => x i ≠ y i) := by
    intro i hi
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
      Function.comp] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    exact hj
  have := card_le_card hs
  rwa [card_map] at this
lemma jj_comp_le {q m t : ℕ} (f : Fin t → Fin m) (hf : Function.Injective f)
    (z x x' : Fin m → Fin q) : jj (z ∘ f) (x ∘ f) (x' ∘ f) ≤ jj z x x' := by
  unfold jj
  have hs : (univ.filter (fun i : Fin t => (z ∘ f) i ≠ (x ∘ f) i ∧ (z ∘ f) i = (x' ∘ f) i)).map
      ⟨f, hf⟩ ⊆ univ.filter (fun i => z i ≠ x i ∧ z i = x' i) := by
    intro i hi
    simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk,
      Function.comp] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    exact hj
  have := card_le_card hs
  rwa [card_map] at this
lemma close_count_proj {q m t : ℕ} (hq : 5 ≤ q) (Lm : ℕ) (hm : 0 < Lm) (htL : t ≤ Lm)
    (r R : ℕ) (z x' : Fin m → Fin q) (hR : hd z x' ≤ R) (P : Finset (Fin m → Fin q))
    (f : Fin t → Fin m) (hf : Function.Injective f)
    (hinj : ∀ x ∈ P, ∀ y ∈ P, x ∘ f = y ∘ f → x = y) :
    ∑ x ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤
      (2 * ((q:ℚ) - 1) * Lm) ^ (r - 1) * (2 * (q:ℚ) ^ R) := by
  have h1 : ∑ x ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤
      ∑ x ∈ P, (if jj (z ∘ f) (x ∘ f) (x' ∘ f) ≤ r - 1 then (1:ℚ) else 0) := by
    apply sum_le_sum; intro x _
    have := jj_comp_le f hf z x x'
    split_ifs with h1 h2 <;> first | (exfalso; omega) | norm_num
  refine h1.trans ?_
  rw [← sum_image (f := fun u => if jj (z ∘ f) u (x' ∘ f) ≤ r - 1 then (1:ℚ) else 0)
    (g := fun x => x ∘ f) hinj]
  exact close_count hq Lm hm htL r R (z ∘ f) (x' ∘ f) ((hd_comp_le f hf z x').trans hR) _
lemma U_piece {q m t : ℕ} (hq : 5 ≤ q) (Lm : ℕ) (hm : 0 < Lm) (htL : t ≤ Lm)
    (f : Fin t → Fin m) (hf : Function.Injective f) (r R : ℕ) (z : Fin m → Fin q)
    (P : Finset (Fin m → Fin q)) (hinj : ∀ x ∈ P, ∀ y ∈ P, x ∘ f = y ∘ f → x = y)
    (hP : ∀ x ∈ P, hd z x ≤ R) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) :
    ∑ y : Fin m → Fin q, (∑ x ∈ P, a x * KK x y) ^ 2 ≤
      (q:ℚ) ^ m * (rho q ^ (2 * r) * (P.card : ℚ) ^ 2 +
        2 * (P.card : ℚ) * ((2 * ((q:ℚ) - 1) * Lm) ^ (r - 1) * (2 * (q:ℚ) ^ R))) := by
  have hq0 : (0:ℚ) ≤ (q:ℚ) ^ m := by positivity
  have hρ0 := rho_nonneg hq
  have hρ1 := rho_le_one hq
  set Cc : ℚ := (2 * ((q:ℚ) - 1) * Lm) ^ (r - 1) * (2 * (q:ℚ) ^ R) with hCc
  have e1 := expand P a (fun x y => KK x y) (fun _ => (1:ℚ))
  simp only [div_one] at e1
  rw [e1]
  simp only [gram_KK hq]
  have s1 : ∑ x ∈ P, ∑ x' ∈ P, a x * a x' * ((q:ℚ) ^ m * rho q ^ hd x x') ≤
      ∑ x ∈ P, ∑ x' ∈ P, (q:ℚ) ^ m * (rho q ^ (2 * r) +
        (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) + (if jj z x' x ≤ r - 1 then (1:ℚ) else 0)) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro x' _
    have hpt : rho q ^ hd x x' ≤ rho q ^ (2 * r) +
        (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) + (if jj z x' x ≤ r - 1 then (1:ℚ) else 0) := by
      have hge := hd_ge z x x'
      have hp1 : rho q ^ hd x x' ≤ 1 := pow_le_one₀ hρ0 hρ1
      have hp0 : 0 ≤ rho q ^ (2 * r) := pow_nonneg hρ0 _
      split_ifs with h1 h2 h2
      · linarith
      · linarith
      · linarith
      · have : 2 * r ≤ hd x x' := by omega
        have := pow_le_pow_of_le_one hρ0 hρ1 this
        linarith
    have hab : a x * a x' ≤ 1 := by
      have := abs_mul (a x) (a x')
      have h1 := ha x
      have h2 := ha x'
      have : |a x * a x'| ≤ 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg (a x), abs_nonneg (a x')]
      exact (le_abs_self _).trans this
    have hab' : -1 ≤ a x * a x' := by
      have : |a x * a x'| ≤ 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg (a x), abs_nonneg (a x'), ha x, ha x']
      exact neg_le_of_abs_le this
    have hp0 : 0 ≤ (q:ℚ) ^ m * rho q ^ hd x x' := mul_nonneg hq0 (pow_nonneg hρ0 _)
    have := mul_le_mul_of_nonneg_left hpt hq0
    nlinarith
  refine s1.trans ?_
  simp only [mul_add, sum_add_distrib, ← mul_sum]
  have c1 : ∑ x ∈ P, ∑ x' ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤ (P.card : ℚ) * Cc := by
    rw [sum_comm]
    have : ∀ x' ∈ P, ∑ x ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤ Cc :=
      fun x' hx' => close_count_proj hq Lm hm htL r R z x' (hP x' hx') P f hf hinj
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have c2 : ∑ x ∈ P, ∑ x' ∈ P, (if jj z x' x ≤ r - 1 then (1:ℚ) else 0) ≤ (P.card : ℚ) * Cc := by
    have : ∀ x ∈ P, ∑ x' ∈ P, (if jj z x' x ≤ r - 1 then (1:ℚ) else 0) ≤ Cc :=
      fun x hx => close_count_proj hq Lm hm htL r R z x (hP x hx) P f hf hinj
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have c0 : ∑ x ∈ P, ∑ x' ∈ P, rho q ^ (2 * r) = rho q ^ (2 * r) * (P.card : ℚ) ^ 2 := by
    simp [sum_const]; ring
  rw [c0]
  nlinarith
lemma T_piece {q m : ℕ} (hq : 5 ≤ q) (R : ℕ) (z : Fin m → Fin q)
    (P : Finset (Fin m → Fin q)) (hP : ∀ x ∈ P, hd z x ≤ R) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) :
    ∑ y : Fin m → Fin q, (∑ x ∈ P, a x * (KK x y * MM x y)) ^ 2 / MM z y ≤
      (((q:ℚ) - 1) * (2 * q * ((q:ℚ) - 2))) ^ R * (P.card : ℚ) := by
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  set c1 : ℚ := 2 * q * ((q:ℚ) - 2) with hc1
  have hc1p : 1 ≤ c1 := by rw [hc1]; nlinarith
  rw [expand P a (fun x y => KK x y * MM x y) (fun y => MM z y)]
  simp only [gram_T]
  have hgg0 : ∀ a a' c : Fin q, 0 ≤ gg c1 a a' c := by
    intro a a' c; unfold gg; split_ifs <;> linarith
  have s1 : ∑ x ∈ P, ∑ x' ∈ P, a x * a x' * ∏ i, F3 (x i) (x' i) (z i) ≤
      ∑ x ∈ P, ∑ x' : Fin m → Fin q, ∏ i, gg c1 (x i) (x' i) (z i) := by
    apply Finset.sum_le_sum; intro x _
    have : ∑ x' ∈ P, a x * a x' * ∏ i, F3 (x i) (x' i) (z i) ≤
        ∑ x' ∈ P, ∏ i, gg c1 (x i) (x' i) (z i) := by
      apply Finset.sum_le_sum; intro x' _
      have hab : |a x * a x'| ≤ 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg (a x), abs_nonneg (a x'), ha x, ha x']
      have hprod : |∏ i, F3 (x i) (x' i) (z i)| ≤ ∏ i, gg c1 (x i) (x' i) (z i) := by
        rw [abs_prod]
        apply Finset.prod_le_prod₀
        · intro i _; exact abs_nonneg _
        · intro i _; exact F3_le_gg hq _ _ _
      calc a x * a x' * ∏ i, F3 (x i) (x' i) (z i)
          ≤ |a x * a x' * ∏ i, F3 (x i) (x' i) (z i)| := le_abs_self _
        _ = |a x * a x'| * |∏ i, F3 (x i) (x' i) (z i)| := abs_mul _ _
        _ ≤ 1 * |∏ i, F3 (x i) (x' i) (z i)| :=
          mul_le_mul_of_nonneg_right hab (abs_nonneg _)
        _ ≤ ∏ i, gg c1 (x i) (x' i) (z i) := by rw [one_mul]; exact hprod
    refine this.trans ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro x' _ _
    exact prod_nonneg (fun i _ => hgg0 _ _ _)
  refine s1.trans ?_
  have s2 : ∀ x ∈ P, ∑ x' : Fin m → Fin q, ∏ i, gg c1 (x i) (x' i) (z i) ≤
      (((q:ℚ) - 1) * c1) ^ R := by
    intro x hx
    rw [sum_prod (fun i b => gg c1 (x i) b (z i))]
    simp only [sum_gg]
    rw [prod_ite]
    simp only [prod_const_one, one_mul, prod_const]
    have hcard : (univ.filter (fun i => ¬ z i = x i)).card ≤ R := by
      have := hP x hx; unfold hd at this; simpa using this
    apply pow_le_pow_right₀ _ hcard
    nlinarith
  refine (Finset.sum_le_sum s2).trans ?_
  simp [sum_const]
  ring_nf
  rfl
lemma Rem {q m : ℕ} (hq : 5 ≤ q) (R H : ℕ) (S : Finset (Fin m → Fin q))
    (hS : ∀ z, (S.filter (fun x => hd z x ≤ R)).card < H) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) :
    ∑ y : Fin m → Fin q, (∑ x ∈ S, a x * KK x y) ^ 2 ≤
      (q:ℚ) ^ m * ((H : ℚ) * S.card + rho q ^ (R + 1) * (S.card : ℚ) ^ 2) := by
  have hq0 : (0:ℚ) ≤ (q:ℚ) ^ m := by positivity
  have hρ0 := rho_nonneg hq
  have hρ1 := rho_le_one hq
  have e1 := expand S a (fun x y => KK x y) (fun _ => (1:ℚ))
  simp only [div_one] at e1
  rw [e1]
  simp only [gram_KK hq]
  have s1 : ∑ x ∈ S, ∑ x' ∈ S, a x * a x' * ((q:ℚ) ^ m * rho q ^ hd x x') ≤
      ∑ x ∈ S, ∑ x' ∈ S, (q:ℚ) ^ m * ((if hd x x' ≤ R then (1:ℚ) else 0) + rho q ^ (R + 1)) := by
    apply Finset.sum_le_sum; intro x _
    apply Finset.sum_le_sum; intro x' _
    have hpt : rho q ^ hd x x' ≤ (if hd x x' ≤ R then (1:ℚ) else 0) + rho q ^ (R + 1) := by
      have hp1 : rho q ^ hd x x' ≤ 1 := pow_le_one₀ hρ0 hρ1
      have hp0 : 0 ≤ rho q ^ (R + 1) := pow_nonneg hρ0 _
      split_ifs with h1
      · linarith
      · have : R + 1 ≤ hd x x' := by omega
        have := pow_le_pow_of_le_one hρ0 hρ1 this
        linarith
    have hab : a x * a x' ≤ 1 := by
      have : |a x * a x'| ≤ 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg (a x), abs_nonneg (a x'), ha x, ha x']
      exact (le_abs_self _).trans this
    have hab' : -1 ≤ a x * a x' := by
      have : |a x * a x'| ≤ 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg (a x), abs_nonneg (a x'), ha x, ha x']
      exact neg_le_of_abs_le this
    have hp0 : 0 ≤ (q:ℚ) ^ m * rho q ^ hd x x' := mul_nonneg hq0 (pow_nonneg hρ0 _)
    have := mul_le_mul_of_nonneg_left hpt hq0
    nlinarith
  refine s1.trans ?_
  simp only [mul_add, sum_add_distrib, ← mul_sum]
  have c1 : ∀ x ∈ S, ∑ x' ∈ S, (if hd x x' ≤ R then (1:ℚ) else 0) ≤ (H : ℚ) := by
    intro x _
    rw [sum_boole]
    have := hS x
    exact_mod_cast this.le
  have c1' := Finset.sum_le_sum c1
  have c0 : ∑ x ∈ S, ∑ x' ∈ S, rho q ^ (R + 1) = rho q ^ (R + 1) * (S.card : ℚ) ^ 2 := by
    simp [sum_const]; ring
  rw [c0]
  simp only [sum_const, nsmul_eq_mul] at c1'
  nlinarith
lemma claim_abs {α : Type*} [DecidableEq α] (Φ : Finset α → ℚ) (B : α → α → Prop)
    [DecidableRel B] (Hn : ℕ) (hH : 0 < Hn) (κ c σ : ℚ) (S0 : Finset α)
    (hsub : ∀ (S : Finset α) (z : α), Φ S ≤ Φ (S.filter (B z)) + Φ (S.filter (fun x => ¬ B z x)))
    (hpiece : ∀ (z : α) (P : Finset α), P ⊆ S0 → (∀ x ∈ P, B z x) → Hn ≤ P.card →
      Φ P ≤ κ * (c * P.card))
    (hrem : ∀ S : Finset α, (∀ z, (S.filter (B z)).card < Hn) → Φ S ≤ κ * (c * S.card + σ)) :
    ∀ S : Finset α, S ⊆ S0 → Φ S ≤ κ * (c * S.card + σ) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS0
    by_cases hex : ∃ z, Hn ≤ (S.filter (B z)).card
    · obtain ⟨z, hz⟩ := hex
      have hP : ∀ x ∈ S.filter (B z), B z x := fun x hx => (mem_filter.1 hx).2
      have h1 := hpiece z _ ((filter_subset _ _).trans hS0) hP hz
      have hne : (S.filter (B z)).Nonempty := by rw [← card_pos]; omega
      obtain ⟨x0, hx0⟩ := hne
      have hsub' : S.filter (fun x => ¬ B z x) ⊂ S := by
        refine ⟨filter_subset _ _, ?_⟩
        intro hcon
        have h2 := hcon (mem_filter.1 hx0).1
        exact (mem_filter.1 h2).2 (mem_filter.1 hx0).2
      have h2 := ih _ hsub' ((filter_subset _ _).trans hS0)
      have e : ((S.filter (B z)).card : ℚ) + ((S.filter (fun x => ¬ B z x)).card : ℚ) = S.card := by
        have := Finset.sum_filter_add_sum_filter_not S (B z) (fun _ => (1:ℚ))
        simpa using this
      have h3 := hsub S z
      calc Φ S ≤ Φ (S.filter (B z)) + Φ (S.filter (fun x => ¬ B z x)) := h3
        _ ≤ κ * (c * (S.filter (B z)).card) + κ * (c * (S.filter (fun x => ¬ B z x)).card + σ) :=
          (add_le_add h1 h2)
        _ = κ * (c * S.card + σ) := by rw [← e]; ring
    · simp only [not_exists, not_le] at hex
      exact hrem S hex
def Phi {q m : ℕ} (a : (Fin m → Fin q) → ℚ) (AN : ℚ) (S : Finset (Fin m → Fin q)) : ℚ :=
  ∑ y, |∑ x ∈ S, a x * KK x y| + AN * ∑ y, |∑ x ∈ S, a x * (KK x y * MM x y)|
lemma Phi_sub {q m : ℕ} (a : (Fin m → Fin q) → ℚ) (AN : ℚ) (hAN : 0 ≤ AN)
    (S : Finset (Fin m → Fin q)) (p : (Fin m → Fin q) → Prop) [DecidablePred p] :
    Phi a AN S ≤ Phi a AN (S.filter p) + Phi a AN (S.filter (fun x => ¬ p x)) := by
  unfold Phi
  have h1 : ∀ y, |∑ x ∈ S, a x * KK x y| ≤ |∑ x ∈ S.filter p, a x * KK x y| +
      |∑ x ∈ S.filter (fun x => ¬ p x), a x * KK x y| := by
    intro y
    have := Finset.sum_filter_add_sum_filter_not S p (fun x => a x * KK x y)
    rw [← this]; exact abs_add_le _ _
  have h2 : ∀ y, |∑ x ∈ S, a x * (KK x y * MM x y)| ≤
      |∑ x ∈ S.filter p, a x * (KK x y * MM x y)| +
      |∑ x ∈ S.filter (fun x => ¬ p x), a x * (KK x y * MM x y)| := by
    intro y
    have := Finset.sum_filter_add_sum_filter_not S p (fun x => a x * (KK x y * MM x y))
    rw [← this]; exact abs_add_le _ _
  have s1 := Finset.sum_le_sum (fun y (_ : y ∈ univ) => h1 y)
  have s2 := Finset.sum_le_sum (fun y (_ : y ∈ univ) => h2 y)
  rw [sum_add_distrib] at s1 s2
  nlinarith [mul_le_mul_of_nonneg_left s2 hAN]
lemma card_W (q m : ℕ) : ∑ _y : Fin m → Fin q, (1:ℚ) = (q:ℚ) ^ m := by
  simp [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
lemma Phi_piece {q m t : ℕ} (hq : 5 ≤ q) (Lm : ℕ) (hm : 0 < Lm) (htL : t ≤ Lm)
    (f : Fin t → Fin m) (hf : Function.Injective f) (r R : ℕ) (z : Fin m → Fin q)
    (P : Finset (Fin m → Fin q)) (hinj : ∀ x ∈ P, ∀ y ∈ P, x ∘ f = y ∘ f → x = y)
    (hP : ∀ x ∈ P, hd z x ≤ R) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) (A d : ℚ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hAr : A = rho q ^ r)
    (hd0 : 0 < d)
    (hU : 4 * (2 * ((q:ℚ) - 1)) ^ (r - 1) * (q:ℚ) ^ R * (Lm:ℚ) ^ (r - 1) ≤ d ^ 2 * P.card)
    (hT : (((q:ℚ) - 1) * (2 * q * ((q:ℚ) - 2))) ^ R ≤ d ^ 2 * P.card) (hPpos : 0 < P.card) :
    Phi a (A * (q:ℚ) ^ m) P ≤ (q:ℚ) ^ m * ((A + 2 * d) * P.card) := by
  unfold Phi
  have hNpos : (0:ℚ) < (q:ℚ) ^ m := by
    have : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hPq : (0:ℚ) < P.card := by exact_mod_cast hPpos
  have hU2 := U_piece hq Lm hm htL f hf r R z P hinj hP a ha
  have hT2 := T_piece hq R z P hP a ha
  set t1 : ℚ := (A + d) * P.card with ht1
  have ht1p : 0 < t1 := by rw [ht1]; positivity
  have am1 := amgm univ (fun y => ∑ x ∈ P, a x * KK x y) (fun _ => (1:ℚ)) t1 ht1p
    (fun _ _ => one_pos)
  simp only [div_one, card_W] at am1
  have hX : ∑ y : Fin m → Fin q, (∑ x ∈ P, a x * KK x y) ^ 2 ≤ (q:ℚ) ^ m * t1 ^ 2 := by
    refine hU2.trans ?_
    apply mul_le_mul_of_nonneg_left _ hNpos.le
    rw [show 2 * r = r + r by ring, pow_add, ← hAr, ht1]
    rw [mul_pow (2 * ((q:ℚ) - 1)) (Lm:ℚ)]
    have h1 := mul_le_mul_of_nonneg_right hU hPq.le
    have h2 : 0 ≤ A * d * (P.card:ℚ) ^ 2 := by positivity
    nlinarith [h1, h2]
  have hU3 : ∑ y : Fin m → Fin q, |∑ x ∈ P, a x * KK x y| ≤ (q:ℚ) ^ m * t1 := by
    refine am1.trans ?_
    have : (∑ y : Fin m → Fin q, (∑ x ∈ P, a x * KK x y) ^ 2) / t1 ≤ (q:ℚ) ^ m * t1 := by
      rw [div_le_iff₀ ht1p]; nlinarith
    linarith
  set t2 : ℚ := d * P.card with ht2
  have ht2p : 0 < t2 := by rw [ht2]; positivity
  have am2 := amgm univ (fun y => ∑ x ∈ P, a x * (KK x y * MM x y)) (fun y => MM z y) t2 ht2p
    (fun y _ => MM_pos hq z y)
  rw [sum_MM hq z] at am2
  have hT3 : ∑ y : Fin m → Fin q, |∑ x ∈ P, a x * (KK x y * MM x y)| ≤ t2 := by
    refine am2.trans ?_
    have : (∑ y : Fin m → Fin q, (∑ x ∈ P, a x * (KK x y * MM x y)) ^ 2 / MM z y) / t2 ≤ t2 := by
      rw [div_le_iff₀ ht2p]
      refine hT2.trans ?_
      rw [ht2]; nlinarith
    linarith
  have hAN : 0 ≤ A * (q:ℚ) ^ m := mul_nonneg hA0 hNpos.le
  have := mul_le_mul_of_nonneg_left hT3 hAN
  rw [ht1] at hU3; rw [ht2] at this
  nlinarith [mul_nonneg (mul_nonneg hNpos.le hd0.le) hPq.le, mul_nonneg (sub_nonneg.2 hA1)
    (mul_nonneg (mul_nonneg hNpos.le hd0.le) hPq.le)]
lemma Phi_rem {q m : ℕ} (hq : 5 ≤ q) (R Hn : ℕ) (hH : 0 < Hn) (S : Finset (Fin m → Fin q))
    (hS : ∀ z, (S.filter (fun x => hd z x ≤ R)).card < Hn) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) (A d : ℚ) (hA0 : 0 ≤ A) (hd0 : 0 < d)
    (hρ : rho q ^ (R + 1) ≤ d ^ 2) :
    Phi a (A * (q:ℚ) ^ m) S ≤ (q:ℚ) ^ m * ((A + 2 * d) * S.card + ((Hn : ℚ) / d) / 2) := by
  unfold Phi
  have hNpos : (0:ℚ) < (q:ℚ) ^ m := by
    have : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hHq : (0:ℚ) < Hn := by exact_mod_cast hH
  have hSq : (0:ℚ) ≤ S.card := by positivity
  have hR2 := Rem hq R Hn S hS a ha
  set t1 : ℚ := d * S.card + (Hn : ℚ) / d with ht1
  have ht1p : 0 < t1 := by rw [ht1]; positivity
  have am1 := amgm univ (fun y => ∑ x ∈ S, a x * KK x y) (fun _ => (1:ℚ)) t1 ht1p
    (fun _ _ => one_pos)
  simp only [div_one, card_W] at am1
  have hX : ∑ y : Fin m → Fin q, (∑ x ∈ S, a x * KK x y) ^ 2 ≤
      (q:ℚ) ^ m * (2 * d * S.card * t1) := by
    refine hR2.trans ?_
    apply mul_le_mul_of_nonneg_left _ hNpos.le
    rw [ht1]
    have e : 2 * d * (S.card : ℚ) * (d * S.card + (Hn : ℚ) / d) =
        2 * d ^ 2 * (S.card : ℚ) ^ 2 + 2 * (Hn : ℚ) * S.card := by
      field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_right hρ (sq_nonneg (S.card : ℚ)), mul_nonneg hHq.le hSq]
  have hU3 : ∑ y : Fin m → Fin q, |∑ x ∈ S, a x * KK x y| ≤
      (q:ℚ) ^ m * (t1 + 2 * d * S.card) / 2 := by
    refine am1.trans ?_
    have : (∑ y : Fin m → Fin q, (∑ x ∈ S, a x * KK x y) ^ 2) / t1 ≤
        (q:ℚ) ^ m * (2 * d * S.card) := by
      rw [div_le_iff₀ ht1p]; nlinarith
    linarith
  have hT3 : ∑ y : Fin m → Fin q, |∑ x ∈ S, a x * (KK x y * MM x y)| ≤ S.card := by
    have : ∀ y, |∑ x ∈ S, a x * (KK x y * MM x y)| ≤ ∑ x ∈ S, MM x y := by
      intro y
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum; intro x _
      rw [abs_mul, abs_mul, abs_KK, abs_of_pos (MM_pos hq x y)]
      have := ha x
      have := MM_pos hq x y
      nlinarith
    refine (Finset.sum_le_sum (fun y (_ : y ∈ univ) => this y)).trans ?_
    rw [sum_comm]
    simp [sum_MM hq]
  have hAN : 0 ≤ A * (q:ℚ) ^ m := mul_nonneg hA0 hNpos.le
  have := mul_le_mul_of_nonneg_left hT3 hAN
  rw [ht1] at hU3
  have e2 : (q:ℚ) ^ m * (d * S.card + (Hn:ℚ) / d + 2 * d * S.card) / 2 =
      (q:ℚ) ^ m * ((3 / 2) * d * S.card + ((Hn : ℚ) / d) / 2) := by ring
  rw [e2] at hU3
  nlinarith [mul_nonneg (mul_nonneg hNpos.le hd0.le) hSq]
lemma KK_eq {q m : ℕ} (x y : Fin m → Fin q) :
    KK x y = (-1) ^ ((univ.filter (fun i => x i = y i)).card) := by
  unfold KK kk
  rw [prod_ite]
  simp
lemma MM_eq {q m : ℕ} (hq : 5 ≤ q) (x y : Fin m → Fin q) :
    ((((q - 3) ^ ((univ.filter (fun i => x i = y i)).card) : ℕ) : ℚ) /
      (((2 * (q - 2)) ^ m : ℕ) : ℚ)) = MM x y := by
  unfold MM mu
  rw [prod_div_distrib, prod_ite]
  simp only [prod_const, prod_const_one, mul_one, card_univ, Fintype.card_fin]
  push_cast [Nat.cast_sub (show 3 ≤ q by omega), Nat.cast_sub (show 2 ≤ q by omega)]
  ring
lemma sign_eq (rd l rr : Bool) (e : ℕ) :
    (if rd = xor (xor l rr) (e % 2 == 1) then (1:ℚ) else -1) =
      (if rd = rr then (1:ℚ) else -1) * (if l then (-1:ℚ) else 1) * (-1) ^ e := by
  rcases Nat.even_or_odd e with he | he
  · rw [he.neg_one_pow, show (e % 2 == 1) = false by rw [Nat.even_iff.1 he]; rfl]
    cases rd <;> cases l <;> cases rr <;> simp
  · rw [he.neg_one_pow, show (e % 2 == 1) = true by rw [Nat.odd_iff.1 he]; rfl]
    cases rd <;> cases l <;> cases rr <;> simp
lemma bias_red {q m : ℕ} (hq : 5 ≤ q) (A : ℚ) (hA0 : 0 ≤ A)
    (left right : (Fin m → Fin q) → Bool) (M : ℕ) (send : (Fin m → Fin q) → Fin M)
    (read : Fin M → (Fin m → Fin q) → Bool) :
    (∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, (if read (send x) y =
        xor (xor (left x) (right y)) ((univ.filter (fun i => x i = y i)).card % 2 == 1)
        then (1:ℚ) else -1)) / ((q ^ m : ℕ) : ℚ) ^ 2 +
      A * ((∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q,
        ((((q - 3) ^ ((univ.filter (fun i => x i = y i)).card) : ℕ) : ℚ) /
          (((2 * (q - 2)) ^ m : ℕ) : ℚ)) *
        (if read (send x) y =
          xor (xor (left x) (right y)) ((univ.filter (fun i => x i = y i)).card % 2 == 1)
          then (1:ℚ) else -1)) / ((q ^ m : ℕ) : ℚ)) ≤
    (∑ c : Fin M, Phi (fun x => if left x then (-1:ℚ) else 1) (A * (q:ℚ) ^ m)
      (univ.filter (fun x => send x = c))) / ((q:ℚ) ^ m) ^ 2 := by
  have hNpos : (0:ℚ) < (q:ℚ) ^ m := by
    have : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hN : ((q ^ m : ℕ) : ℚ) = (q:ℚ) ^ m := by push_cast; ring
  set a : (Fin m → Fin q) → ℚ := fun x => if left x then (-1:ℚ) else 1 with ha
  set sg : Fin M → (Fin m → Fin q) → ℚ := fun c y => if read c y = right y then (1:ℚ) else -1
    with hsg
  have hsign : ∀ x y : Fin m → Fin q, (if read (send x) y =
        xor (xor (left x) (right y)) ((univ.filter (fun i => x i = y i)).card % 2 == 1)
        then (1:ℚ) else -1) = sg (send x) y * a x * KK x y := by
    intro x y
    rw [sign_eq, KK_eq]
  simp only [hsign, MM_eq hq, hN]
  set AN : ℚ := A * (q:ℚ) ^ m with hAN
  have hAN0 : 0 ≤ AN := mul_nonneg hA0 hNpos.le
  have e1 : (∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, sg (send x) y * a x * KK x y) /
        ((q:ℚ) ^ m) ^ 2 +
      A * ((∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, MM x y * (sg (send x) y * a x * KK x y)) /
        (q:ℚ) ^ m) =
      (∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q,
        sg (send x) y * a x * KK x y * (1 + AN * MM x y)) / ((q:ℚ) ^ m) ^ 2 := by
    have e2 : ∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q,
        sg (send x) y * a x * KK x y * (1 + AN * MM x y) =
        ∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, sg (send x) y * a x * KK x y +
        AN * ∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, MM x y * (sg (send x) y * a x * KK x y) := by
      rw [mul_sum, ← sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [mul_sum, ← sum_add_distrib]
      apply Finset.sum_congr rfl; intro y _
      ring
    rw [e2, hAN]
    field_simp
  rw [e1]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have key : ∀ (y : Fin m → Fin q) (c : Fin M),
      ∑ x ∈ univ.filter (fun x => send x = c), sg (send x) y * a x * KK x y * (1 + AN * MM x y) ≤
      |∑ x ∈ univ.filter (fun x => send x = c), a x * KK x y| +
        AN * |∑ x ∈ univ.filter (fun x => send x = c), a x * (KK x y * MM x y)| := by
    intro y c
    have e3 : ∑ x ∈ univ.filter (fun x => send x = c),
        sg (send x) y * a x * KK x y * (1 + AN * MM x y) =
        sg c y * (∑ x ∈ univ.filter (fun x => send x = c), a x * KK x y +
          AN * ∑ x ∈ univ.filter (fun x => send x = c), a x * (KK x y * MM x y)) := by
      rw [mul_sum, mul_add, mul_sum, mul_sum, ← sum_add_distrib]
      apply Finset.sum_congr rfl; intro x hx
      rw [(mem_filter.1 hx).2]; ring
    rw [e3]
    have hs : |sg c y| = 1 := by rw [hsg]; dsimp only; split_ifs <;> norm_num
    set U := ∑ x ∈ univ.filter (fun x => send x = c), a x * KK x y
    set T := ∑ x ∈ univ.filter (fun x => send x = c), a x * (KK x y * MM x y)
    calc sg c y * (U + AN * T) ≤ |sg c y * (U + AN * T)| := le_abs_self _
      _ = |U + AN * T| := by rw [abs_mul, hs, one_mul]
      _ ≤ |U| + |AN * T| := abs_add_le _ _
      _ = |U| + AN * |T| := by rw [abs_mul, abs_of_nonneg hAN0]
  calc ∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, sg (send x) y * a x * KK x y * (1 + AN * MM x y)
      = ∑ y : Fin m → Fin q, ∑ x : Fin m → Fin q,
          sg (send x) y * a x * KK x y * (1 + AN * MM x y) := sum_comm
    _ = ∑ y : Fin m → Fin q, ∑ c : Fin M, ∑ x ∈ univ.filter (fun x => send x = c),
          sg (send x) y * a x * KK x y * (1 + AN * MM x y) := by
        apply Finset.sum_congr rfl; intro y _
        rw [Finset.sum_fiberwise]
    _ ≤ ∑ y : Fin m → Fin q, ∑ c : Fin M, (|∑ x ∈ univ.filter (fun x => send x = c), a x * KK x y| +
        AN * |∑ x ∈ univ.filter (fun x => send x = c), a x * (KK x y * MM x y)|) :=
        Finset.sum_le_sum (fun y _ => Finset.sum_le_sum (fun c _ => key y c))
    _ = ∑ c : Fin M, Phi a AN (univ.filter (fun x => send x = c)) := by
        rw [sum_comm]
        apply Finset.sum_congr rfl; intro c _
        unfold Phi
        rw [sum_add_distrib, mul_sum]
lemma main (q r : ℕ) (hq : 5 ≤ q) (hr : 0 < r) (β : ℚ)
    (hβ : (1 - 4 / (q:ℚ)) ^ r < (1 + (1 - 4 / (q:ℚ)) ^ r) * β) :
    ∃ C : ℕ, 0 < C ∧ ∀ (m t : ℕ) (f : Fin t → Fin m), Function.Injective f →
      ∀ (left right : (Fin m → Fin q) → Bool) (M : ℕ)
      (send : (Fin m → Fin q) → Fin M) (read : Fin M → (Fin m → Fin q) → Bool),
      (∀ x y, send x = send y → x ∘ f = y ∘ f → x = y) →
      (1 + (1 - 4 / (q:ℚ)) ^ r) * β ≤
        (∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q, (if read (send x) y =
          xor (xor (left x) (right y)) ((univ.filter (fun i => x i = y i)).card % 2 == 1)
          then (1:ℚ) else -1)) / ((q ^ m : ℕ) : ℚ) ^ 2 +
        (1 - 4 / (q:ℚ)) ^ r * ((∑ x : Fin m → Fin q, ∑ y : Fin m → Fin q,
          ((((q - 3) ^ ((univ.filter (fun i => x i = y i)).card) : ℕ) : ℚ) /
            (((2 * (q - 2)) ^ m : ℕ) : ℚ)) *
          (if read (send x) y =
            xor (xor (left x) (right y)) ((univ.filter (fun i => x i = y i)).card % 2 == 1)
            then (1:ℚ) else -1)) / ((q ^ m : ℕ) : ℚ)) →
      q ^ m ≤ C * M * (t + 1) ^ (r - 1) := by
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  set A : ℚ := (1 - 4 / (q:ℚ)) ^ r with hAdef
  have hAr : A = rho q ^ r := by
    rw [hAdef]; unfold rho; congr 1; field_simp
  have hA0 : 0 ≤ A := by rw [hAr]; exact pow_nonneg (rho_nonneg hq) _
  have hA1 : A ≤ 1 := by rw [hAr]; exact pow_le_one₀ (rho_nonneg hq) (rho_le_one hq)
  set δ : ℚ := (1 + A) * β - A with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set d : ℚ := δ / 8 with hddef
  have hd0 : 0 < d := by rw [hddef]; positivity
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (show (0:ℚ) < d ^ 2 by positivity) (rho_lt_one hq)
  have hρR : rho q ^ (R + 1) ≤ d ^ 2 :=
    (pow_le_pow_of_le_one (rho_nonneg hq) (rho_le_one hq) (Nat.le_succ R)).trans hR.le
  set cU : ℚ := 4 * (2 * ((q:ℚ) - 1)) ^ (r - 1) * (q:ℚ) ^ R with hcU
  set cT : ℚ := (((q:ℚ) - 1) * (2 * q * ((q:ℚ) - 2))) ^ R with hcT
  set K : ℕ := ⌈cU / d ^ 2⌉₊ + ⌈cT / d ^ 2⌉₊ + 1 with hK
  have hK1 : cU / d ^ 2 ≤ K := by
    have := Nat.le_ceil (cU / d ^ 2)
    rw [hK]; push_cast
    have : (0:ℚ) ≤ ⌈cT / d ^ 2⌉₊ := by positivity
    linarith
  have hK2 : cT / d ^ 2 ≤ K := by
    have := Nat.le_ceil (cT / d ^ 2)
    rw [hK]; push_cast
    have : (0:ℚ) ≤ ⌈cU / d ^ 2⌉₊ := by positivity
    linarith
  have hKpos : 0 < K := by rw [hK]; omega
  set C : ℕ := ⌈(K : ℚ) / d ^ 2⌉₊ + 1 with hC
  have hC1 : (K : ℚ) / d ^ 2 ≤ C := by
    have := Nat.le_ceil ((K : ℚ) / d ^ 2)
    rw [hC]; push_cast; linarith
  refine ⟨C, by rw [hC]; omega, ?_⟩
  intro m t f hf left right M send read hsep hbias
  obtain ⟨Lm, hLm⟩ : ∃ Lm : ℕ, Lm = t + 1 := ⟨_, rfl⟩
  have hLm0 : 0 < Lm := by omega
  have htL : t ≤ Lm := by omega
  rw [← hLm]
  have hB := hbias.trans (bias_red hq A hA0 left right M send read)
  clear hbias
  by_contra hcon
  rw [not_le] at hcon
  have hM : 0 < M := by
    have := (send (fun _ => ⟨0, by omega⟩)).isLt
    omega
  have hNpos : (0:ℚ) < (q:ℚ) ^ m := by
    have : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hcon' : (C : ℚ) * M * (Lm : ℚ) ^ (r - 1) < (q:ℚ) ^ m := by exact_mod_cast hcon
  obtain ⟨Hn, hHn⟩ : ∃ Hn : ℕ, Hn = K * Lm ^ (r - 1) := ⟨_, rfl⟩
  have hHpos : 0 < Hn := by rw [hHn]; positivity
  have hmr : (1:ℚ) ≤ (Lm:ℚ) ^ (r - 1) := one_le_pow₀ (by exact_mod_cast hLm0)
  have hHn' : (Hn : ℚ) = K * (Lm:ℚ) ^ (r - 1) := by rw [hHn]; push_cast; ring
  obtain ⟨a, ha⟩ : ∃ a : (Fin m → Fin q) → ℚ, a = fun x => if left x then (-1:ℚ) else 1 :=
    ⟨_, rfl⟩
  rw [← ha] at hB
  have haa : ∀ x, |a x| ≤ 1 := by intro x; rw [ha]; dsimp only; split_ifs <;> norm_num
  have hcl : ∀ c : Fin M, Phi a (A * (q:ℚ) ^ m) (univ.filter (fun x => send x = c)) ≤
      (q:ℚ) ^ m * ((A + 2 * d) * (univ.filter (fun x => send x = c)).card +
        ((Hn : ℚ) / d) / 2) := by
    intro c
    refine claim_abs (Phi a (A * (q:ℚ) ^ m)) (fun z x => hd z x ≤ R) Hn hHpos _ _ _
      (univ.filter (fun x => send x = c)) ?_ ?_ ?_ _ (subset_refl _)
    · intro S z
      exact Phi_sub a _ (mul_nonneg hA0 hNpos.le) S _
    · intro z P hPS hP hPc
      have hinj : ∀ x ∈ P, ∀ y ∈ P, x ∘ f = y ∘ f → x = y := by
        intro x hx y hy hxy
        have hx' := (mem_filter.1 (hPS hx)).2
        have hy' := (mem_filter.1 (hPS hy)).2
        exact hsep x y (hx'.trans hy'.symm) hxy
      have hPc' : (Hn : ℚ) ≤ P.card := by exact_mod_cast hPc
      apply Phi_piece hq Lm hLm0 htL f hf r R z P hinj hP a haa A d hA0 hA1 hAr hd0
      · have h1 : cU ≤ d ^ 2 * K := by
          rw [div_le_iff₀ (by positivity)] at hK1; linarith
        have h2 : cU * (Lm:ℚ) ^ (r - 1) ≤ d ^ 2 * K * (Lm:ℚ) ^ (r - 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h3 : d ^ 2 * (K * (Lm:ℚ) ^ (r - 1)) ≤ d ^ 2 * P.card := by
          rw [← hHn']; exact mul_le_mul_of_nonneg_left hPc' (sq_nonneg d)
        rw [← hcU]
        linarith
      · have h1 : cT ≤ d ^ 2 * K := by
          rw [div_le_iff₀ (by positivity)] at hK2; linarith
        have hKH : (K : ℚ) ≤ Hn := by
          rw [hHn']
          have : (0:ℚ) ≤ K := by positivity
          have := mul_le_mul_of_nonneg_left hmr this
          linarith
        have h3 : d ^ 2 * (K : ℚ) ≤ d ^ 2 * P.card :=
          mul_le_mul_of_nonneg_left (hKH.trans hPc') (sq_nonneg d)
        rw [← hcT]
        linarith
      · omega
    · intro S hS
      exact Phi_rem hq R Hn hHpos S hS a haa A d hA0 hd0 hρR
  have hcard : ∑ c : Fin M, ((univ.filter (fun x => send x = c)).card : ℚ) = (q:ℚ) ^ m := by
    have := Finset.card_eq_sum_card_fiberwise (f := send) (s := univ) (t := univ)
      (fun x _ => mem_univ _)
    have h2 : ((univ : Finset (Fin m → Fin q)).card : ℚ) = (q:ℚ) ^ m := by
      simp [Finset.card_univ, Fintype.card_fin]
    rw [← h2, this]; push_cast; rfl
  have hsum : ∑ c : Fin M, Phi a (A * (q:ℚ) ^ m) (univ.filter (fun x => send x = c)) ≤
      (q:ℚ) ^ m * ((A + 2 * d) * (q:ℚ) ^ m + M * (((Hn : ℚ) / d) / 2)) := by
    refine (Finset.sum_le_sum (fun c _ => hcl c)).trans ?_
    rw [← mul_sum, sum_add_distrib, ← mul_sum, hcard]
    simp [sum_const, card_univ, Fintype.card_fin]
  have hMH : (M : ℚ) * Hn ≤ d ^ 2 * (q:ℚ) ^ m := by
    rw [hHn']
    have h1 : (K : ℚ) ≤ d ^ 2 * C := by rw [div_le_iff₀ (by positivity)] at hC1; linarith
    have h2 : (M : ℚ) * (K * (Lm:ℚ) ^ (r - 1)) ≤ (M : ℚ) * (d ^ 2 * C * (Lm:ℚ) ^ (r - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc (M : ℚ) * (K * (Lm:ℚ) ^ (r - 1)) ≤ (M : ℚ) * (d ^ 2 * C * (Lm:ℚ) ^ (r - 1)) := h2
      _ = d ^ 2 * ((C : ℚ) * M * (Lm : ℚ) ^ (r - 1)) := by ring
      _ ≤ d ^ 2 * (q:ℚ) ^ m := mul_le_mul_of_nonneg_left hcon'.le (sq_nonneg d)
  have hdH : (M : ℚ) * (((Hn : ℚ) / d) / 2) ≤ d / 2 * (q:ℚ) ^ m := by
    rw [show (M : ℚ) * (((Hn : ℚ) / d) / 2) = ((M : ℚ) * Hn) / (2 * d) by ring]
    rw [div_le_iff₀ (by positivity)]
    have : d ^ 2 * (q:ℚ) ^ m = d / 2 * (q:ℚ) ^ m * (2 * d) := by ring
    linarith
  have hfin : (∑ c : Fin M, Phi a (A * (q:ℚ) ^ m) (univ.filter (fun x => send x = c))) /
      ((q:ℚ) ^ m) ^ 2 ≤ A + 2 * d + d / 2 := by
    rw [div_le_iff₀ (by positivity)]
    refine hsum.trans ?_
    have e : ((A + 2 * d) + d / 2) * ((q:ℚ) ^ m) ^ 2 =
        (q:ℚ) ^ m * ((A + 2 * d) * (q:ℚ) ^ m + d / 2 * (q:ℚ) ^ m) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hNpos.le
    linarith
  have hlast : (1 + A) * β ≤ A + 2 * d + d / 2 := hB.trans hfin
  rw [hddef, hδdef] at hlast
  linarith
end PEqualNP.Outside.L_lib_1026_aux.Lower

namespace PEqualNP.Outside.L_lib_1026_aux.Lin

abbrev Words (m : ℕ) (Q : Type) := Fin m → Q

section Rank

variable {K I J O : Type} [Field K] [Fintype I] [Fintype J] [Fintype O]

theorem pivot_coordinates (U : Submodule K (I → K)) :
    ∃ S : Finset I, S.card ≤ Module.finrank K U ∧
      ∀ v ∈ U, (∀ i ∈ S, v i = 0) → v = 0 := by
  classical
  suffices all : ∀ d (V : Submodule K (I → K)), Module.finrank K V = d →
      ∃ S : Finset I, S.card ≤ d ∧
        ∀ v ∈ V, (∀ i ∈ S, v i = 0) → v = 0 from
    all (Module.finrank K U) U rfl
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro V dimension
    by_cases empty : V = ⊥
    · refine ⟨∅, by simp, ?_⟩
      intro v hv _
      simpa [empty] using hv
    · obtain ⟨v, hv, nonzero⟩ : ∃ v ∈ V, v ≠ 0 := by
        by_contra no
        push Not at no
        apply empty
        refine le_antisymm ?_ bot_le
        intro v hv
        rw [no v hv]
        exact Submodule.zero_mem _
      obtain ⟨i, different⟩ : ∃ i, v i ≠ 0 := by
        by_contra no
        push Not at no
        exact nonzero (funext no)
      let coordinate : (I → K) →ₗ[K] K := LinearMap.proj i
      let cut := V ⊓ coordinate.ker
      have smaller : cut < V := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro equal
        have inCut : v ∈ cut := equal ▸ hv
        exact different (LinearMap.mem_ker.mp (Submodule.mem_inf.mp inCut).2)
      have lowerDimension : Module.finrank K cut < d :=
        dimension ▸ Submodule.finrank_lt_finrank_of_lt smaller
      obtain ⟨S, cardS, pivot⟩ := ih _ lowerDimension cut rfl
      refine ⟨insert i S, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
      intro w hw zero
      have hi : coordinate w = 0 := zero i (Finset.mem_insert_self i S)
      exact pivot w ⟨hw, LinearMap.mem_ker.mpr hi⟩
        (fun j hj => zero j (Finset.mem_insert_of_mem hj))

theorem message_pivots (L : ((I → K) × (J → K)) →ₗ[K] (O → K)) :
    let rank := Module.finrank K L.range
    rank ≤ Fintype.card O ∧ rank ≤ Fintype.card I + Fintype.card J ∧
    ∃ S : Finset I, S.card + rank ≤ Fintype.card I + Fintype.card J ∧
      ∀ (x y : I → K) (u v : J → K), L (x, u) = L (y, v) →
        (∀ i ∈ S, x i = y i) → x = y := by
  classical
  dsimp only
  let A : (I → K) →ₗ[K] L.range :=
    L.rangeRestrict.comp (LinearMap.inl K (I → K) (J → K))
  let B : (J → K) →ₗ[K] L.range :=
    L.rangeRestrict.comp (LinearMap.inr K (I → K) (J → K))
  let F := B.range.mkQ.comp A
  have proj (x : I → K) (z : J → K) :
      F x = B.range.mkQ (L.rangeRestrict (x, z)) := by
    have sum : A x + B z = L.rangeRestrict (x, z) := by
      change L.rangeRestrict (x, 0) + L.rangeRestrict (0, z) = _
      rw [← map_add]
      simp
    have vanish : B.range.mkQ (B z) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact ⟨z, rfl⟩
    rw [← sum, map_add, vanish, add_zero]
    rfl
  have onto : Function.Surjective F := by
    intro q
    obtain ⟨r, hr⟩ := B.range.mkQ_surjective q
    obtain ⟨⟨x, z⟩, h⟩ := L.surjective_rangeRestrict r
    exact ⟨x, (proj x z).trans (h ▸ hr)⟩
  have nullity := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto, finrank_top] at nullity
  have quotient := B.range.finrank_quotient_add_finrank
  have bsize := B.finrank_range_le
  have csize := (L.range).finrank_le
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] at nullity bsize csize
  obtain ⟨S, size, determines⟩ := pivot_coordinates F.ker
  refine ⟨csize, by omega, S, by omega, ?_⟩
  intro x y u v equal agreement
  have same : F x = F y := by
    rw [proj x u, proj y v]
    have e : L.rangeRestrict (x, u) = L.rangeRestrict (y, v) := Subtype.ext equal
    rw [e]
  have difference : x - y ∈ F.ker := by rw [LinearMap.mem_ker, map_sub, same, sub_self]
  exact sub_eq_zero.mp (determines (x - y) difference
    (fun i hi => sub_eq_zero.mpr (agreement i hi)))

end Rank

def toField : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := z == 1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem polynomial_absorb (r h : ℕ) (hr : 0 < r) :
    (h + 1)^r ≤ r^r * 2^h := by
  have small : h / r + 1 ≤ 2^(h / r) := by
    generalize h / r = k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      omega
  have quot := Nat.mod_add_div h r
  have remainder := Nat.mod_lt h hr
  calc
    (h + 1)^r ≤ (r * (h / r + 1))^r := by
      apply Nat.pow_le_pow_left
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ = r^r * (h / r + 1)^r := by rw [mul_pow]
    _ ≤ r^r * (2^(h / r))^r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small _)
    _ ≤ r^r * 2^h := by
      rw [← pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self h r))

open PEqualNP.CircuitLowerBounds

section Linearize

variable {V X : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev WireForm (V : Type) [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ) :=
  (((V × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) × ZMod 2)

def formValue {k : ℕ} (w : WireForm V k) (x : V) (h : Fin k → ZMod 2) : ZMod 2 :=
  w.1 (x, h) + w.2

def constForm {k : ℕ} (a : ZMod 2) : WireForm V k := (0, a)

@[simp] theorem value_const {k : ℕ} (a : ZMod 2) (x : V) (h : Fin k → ZMod 2) :
    formValue (constForm a) x h = a := by simp [constForm, formValue]

@[simp] theorem value_zero {k : ℕ} (x : V) (h : Fin k → ZMod 2) :
    formValue (0 : WireForm V k) x h = 0 := by simp [formValue]

@[simp] theorem value_add {k : ℕ} (a b : WireForm V k) (x : V) (h : Fin k → ZMod 2) :
    formValue (a + b) x h = formValue a x h + formValue b x h := by
  simp only [formValue, Prod.fst_add, Prod.snd_add, LinearMap.add_apply]
  ring

def paid (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

noncomputable def paidBool (g : Gate) : Bool := @decide (paid g) (Classical.propDecidable _)

noncomputable def paidCount (gs : List Gate) : ℕ := gs.countP paidBool

def legalOp (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun n => w.getD n false)]

theorem getD_map' {A B : Type} (f : A → B) (l : List A) (i : ℕ) (v : A) :
    (l.map f).getD i (f v) = f (l.getD i v) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem field_even_single (a : Bool) :
    toField (GateOp.eval (.mod 2) [a]) = 1 + toField a := by cases a <;> decide +kernel

theorem field_even_pair (a b : Bool) :
    toField (GateOp.eval (.mod 2) [a, b]) = 1 + toField a + toField b := by
  cases a <;> cases b <;> decide +kernel

theorem field_negate (a : Bool) : toField (!a) = 1 + toField a := by cases a <;> decide +kernel

@[simp] theorem field_false : toField false = 0 := by decide +kernel

@[simp] theorem field_true : toField true = 1 := by decide +kernel

theorem input_shapes {A : Type} (l : List A) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨a, rfl⟩)
  · have short : tail.length + 1 + 1 ≤ 2 := by simpa only [List.length_cons] using h
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    subst tail
    exact Or.inr (Or.inr ⟨a, b, rfl⟩)

def freeForm {k : ℕ} (w : List (WireForm V k)) (g : Gate) : WireForm V k :=
  let args := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => args.headD (constForm 1)
  | .or => args.headD 0
  | .not => constForm 1 + args.headD 0
  | .mod _ => constForm 1 + args.sum
  | .maj => 0

theorem freeForm_value {k : ℕ} (w : List (WireForm V k)) (bits : List Bool)
    (x : V) (h : Fin k → ZMod 2) (g : Gate) (legal : legalOp g) (free : ¬ paid g)
    (inputs : ∀ i, formValue (w.getD i 0) x h = toField (bits.getD i false)) :
    formValue (freeForm w g) x h = toField (g.op.eval (g.inputs.map fun i => bits.getD i false)) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨length, basis⟩ := legal
  change ins.length ≤ 2 at length
  rcases basis with h | h | h | ⟨h, unary⟩
  · change op = .and at h
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp [freeForm, GateOp.eval]
    · simp [freeForm, GateOp.eval, -List.getD_eq_getElem?_getD, inputs]
    · exact (free ⟨Or.inl rfl, rfl⟩).elim
  · change op = .or at h
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp [freeForm, GateOp.eval]
    · simp [freeForm, GateOp.eval, -List.getD_eq_getElem?_getD, inputs]
    · exact (free ⟨Or.inr rfl, rfl⟩).elim
  · change op = .mod 2 at h
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp [freeForm, GateOp.eval]
    · simp [freeForm, -List.getD_eq_getElem?_getD, inputs, field_even_single]
    · simp [freeForm, -List.getD_eq_getElem?_getD, inputs, field_even_pair, add_assoc]
  · change op = .not at h
    change ins.length = 1 at unary
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp at unary
    · simp [freeForm, GateOp.eval, -List.getD_eq_getElem?_getD, inputs, field_negate]
    · simp at unary

def forgetLast (k : ℕ) : (Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  LinearMap.pi (fun j => LinearMap.proj j.castSucc)

def extendForm {k : ℕ} (w : WireForm V k) : WireForm V (k + 1) :=
  (w.1.comp ((LinearMap.fst _ _ _).prod ((forgetLast k).comp (LinearMap.snd _ _ _))), w.2)

def lastForm (k : ℕ) : WireForm V (k + 1) :=
  ((LinearMap.proj (Fin.last k)).comp (LinearMap.snd _ _ _), 0)

@[simp] theorem extendForm_value {k : ℕ} (w : WireForm V k) (x : V)
    (h : Fin k → ZMod 2) (v : ZMod 2) :
    formValue (extendForm w) x (Fin.snoc h v) = formValue w x h := by
  have eq : forgetLast k (Fin.snoc h v) = h := by
    funext i
    change (Fin.snoc (α := fun _ => ZMod 2) h v) i.castSucc = h i
    simp
  change w.1 (x, forgetLast k (Fin.snoc h v)) + w.2 = w.1 (x, h) + w.2
  rw [eq]

@[simp] theorem lastForm_value {k : ℕ} (x : V) (h : Fin k → ZMod 2) (v : ZMod 2) :
    formValue (lastForm k) x (Fin.snoc h v) = v := by
  simp [formValue, lastForm]

theorem affine_wires (raw : X → V) (input : X → List Bool)
    (initial : List (WireForm V 0))
    (hinit : ∀ x, initial.map (fun f => formValue f (raw x) Fin.elim0) = (input x).map toField)
    (gs : List Gate) (legal : ∀ g ∈ gs, legalOp g) :
    ∃ k, k = paidCount gs ∧ ∃ h : X → Fin k → ZMod 2, ∃ forms : List (WireForm V k),
      ∀ x, forms.map (fun f => formValue f (raw x) (h x)) =
        (gs.foldl appendWire (input x)).map toField := by
  classical
  induction gs using List.reverseRecOn with
  | nil => exact ⟨0, rfl, fun _ => Fin.elim0, initial, hinit⟩
  | append_singleton gs g ih =>
    have hg := legal g (by simp)
    obtain ⟨k, hc, h, forms, hf⟩ := ih (fun o ho => legal o (by simp [ho]))
    let bits (x : X) := gs.foldl appendWire (input x)
    let bit (x : X) := g.op.eval (g.inputs.map fun i => (bits x).getD i false)
    have after (x : X) : (gs ++ [g]).foldl appendWire (input x) = bits x ++ [bit x] := by
      simp [List.foldl_append, bits, bit, appendWire]
    by_cases hm : paid g
    · have count : paidCount (gs ++ [g]) = k + 1 := by
        simp [paidCount, List.countP_append, paidBool, hm, hc]
      let hnew (x : X) : Fin (k + 1) → ZMod 2 := Fin.snoc (h x) (toField (bit x))
      refine ⟨k + 1, count.symm, hnew, forms.map extendForm ++ [lastForm k], ?_⟩
      intro x
      rw [after, List.map_append, List.map_append, List.map_map]
      simp only [List.map_cons, List.map_nil, Function.comp_def, hnew, extendForm_value,
        lastForm_value, hf, bits]
    · have count : paidCount (gs ++ [g]) = k := by
        simp [paidCount, List.countP_append, paidBool, hm, hc]
      have inputs (x : X) (i : ℕ) :
          formValue (forms.getD i 0) (raw x) (h x) = toField ((bits x).getD i false) := by
        rw [← getD_map' (fun f => formValue f (raw x) (h x)), hf, value_zero]
        rw [← field_false, getD_map']
      refine ⟨k, count.symm, h, forms ++ [freeForm forms g], ?_⟩
      intro x
      rw [after, List.map_append, List.map_append, hf, List.map_singleton, List.map_singleton]
      rw [freeForm_value forms (bits x) _ _ g hg hm (inputs x)]

end Linearize

open PEqualNP.CircuitLowerBounds

section CircuitLower

variable {a m c : ℕ}

abbrev RawIndex (m a : ℕ) := Fin m × Fin a

def rawBits (x : Words m (Fin a → Bool)) : RawIndex m a → ZMod 2 :=
  fun i => toField (x i.1 i.2)

theorem rawBits_injective : Function.Injective (rawBits (m := m) (a := a)) := by
  intro x y equal
  funext i j
  exact toField.injective (congrFun equal (i,j))

def inputBits (x : Words m (Fin a → Bool)) : List Bool :=
  (List.ofFn x).flatMap fun v => List.ofFn v

def inputForm (i : RawIndex m a) : WireForm (RawIndex m a → ZMod 2) 0 :=
  ((LinearMap.proj i).comp (LinearMap.fst _ _ _), 0)

def inputForms (m a : ℕ) : List (WireForm (RawIndex m a → ZMod 2) 0) :=
  (List.ofFn fun i : Fin m => List.ofFn fun j : Fin a => inputForm (i, j)).flatten

theorem inputForms_eval (x : Words m (Fin a → Bool)) :
    (inputForms m a).map (fun f => formValue f (rawBits x) Fin.elim0) =
      (inputBits x).map toField := by
  simp [inputForms, inputBits, List.flatMap_def, List.map_flatten, List.map_ofFn,
    Function.comp_def, inputForm, formValue, rawBits]

theorem affine_send (C : Circuit) (tap : Fin c → ℕ)
    (legal : ∀ g ∈ C.gates, legalOp g) :
    ∃ k, k = paidCount C.gates ∧ ∃ h : Words m (Fin a → Bool) → Fin k → ZMod 2,
      ∃ L : ((RawIndex m a → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] (Fin c → ZMod 2),
        ∃ γ : Fin c → ZMod 2, ∀ x j,
          toField ((C.wires (inputBits x)).getD (tap j) false) = L (rawBits x,h x) j + γ j := by
  obtain ⟨k, hk, h, forms, hforms⟩ := affine_wires rawBits inputBits
    (inputForms m a) inputForms_eval C.gates legal
  let tapForm j := forms.getD (tap j) 0
  refine ⟨k,hk,h,LinearMap.pi (fun j => (tapForm j).1),fun j => (tapForm j).2,?_⟩
  intro x j
  change _ = formValue (forms.getD (tap j) 0) (rawBits x) (h x)
  rw [← getD_map' (fun f => formValue f (rawBits x) (h x)), hforms, value_zero,
    ← field_false, getD_map']
  rfl

theorem coordinate_projection {k : ℕ}
    (L : ((RawIndex m a → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] (Fin c → ZMod 2))
    (h : Words m (Fin a → Bool) → Fin k → ZMod 2) :
    let d := Module.finrank (ZMod 2) L.range
    d ≤ c ∧ d ≤ a*m+k ∧
    ∃ t, t+d ≤ a*m+k ∧
      ∃ f : Fin t → Fin m, Function.Injective f ∧
        ∀ x y, L.rangeRestrict (rawBits x, h x) = L.rangeRestrict (rawBits y, h y) →
          x ∘ f = y ∘ f → x = y := by
  classical
  obtain ⟨hc, hd, S, hs, membership⟩ := message_pivots L
  simp only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm m a] at hc hd hs
  let T := S.image Prod.fst
  let t := T.card
  let e : T ≃ Fin t := Fintype.equivFinOfCardEq (Fintype.card_coe T)
  let f (j : Fin t) : Fin m := (e.symm j).val
  have inj : Function.Injective f := fun _ _ equal => e.symm.injective (Subtype.ext equal)
  have bound : t ≤ S.card := Finset.card_image_le
  refine ⟨hc,hd,t,by omega,f,inj,?_⟩
  intro x y lin restrict
  apply rawBits_injective
  apply membership _ _ (h x) (h y) (congrArg Subtype.val lin)
  intro i hi
  let p : T := ⟨i.1, Finset.mem_image_of_mem Prod.fst hi⟩
  have hbase : f (e p) = i.1 := by simp [f, p]
  have equal := congrFun restrict (e p)
  change x (f (e p)) = y (f (e p)) at equal
  rw [hbase] at equal
  exact congrArg toField (congrFun equal i.2)

end CircuitLower

end PEqualNP.Outside.L_lib_1026_aux.Lin

namespace PEqualNP.Outside.L_lib_1026_aux.Lower

open PEqualNP.CircuitLowerBounds
open Finset

def Works (a m g : ℕ) (β : ℚ) (b : ℕ) : Prop :=
  b ≤ a*m ∧ ∃ (z : ℕ) (C : Fin z → Circuit) (tap : Fin z → Fin (a*m-b) → ℕ)
    (read : Fin z → (Fin (a*m-b) → Bool) → (Fin m → Fin a → Bool) → Bool),
    0 < z ∧ (∀ s, ((∀ i : Fin (C s).gates.length, ∀ v ∈ ((C s).gates.get i).inputs,
        v < a*m+i.val) ∧
        (∀ h ∈ (C s).gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))) ∧
      (C s).gates.countP (fun h => @decide
        ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)) ≤ g ∧
      ∀ j, tap s j < a*m+(C s).gates.length) ∧
    ∀ x y : Fin m → Fin a → Bool,
      (1+β)*(z : ℚ) ≤ 2*((((Finset.univ : Finset (Fin z)).filter (fun s =>
        read s (fun j => ((C s).wires ((List.ofFn x).flatMap (fun v => List.ofFn v))).getD
          (tap s j) false) y =
          (((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1))).card :
            ℕ) : ℚ)

lemma avg_seed {X : Type} [Fintype X] (z : ℕ) (hz : 0 < z) (w : X → ℚ) (hw : ∀ x, 0 ≤ w x)
    (sg : Fin z → X → ℚ) (β : ℚ) (h : ∀ x, β * z ≤ ∑ s, sg s x) :
    ∃ s, β * ∑ x, w x ≤ ∑ x, w x * sg s x := by
  by_contra hcon
  simp only [not_exists, not_le] at hcon
  have h1 : ∑ s : Fin z, ∑ x, w x * sg s x < ∑ _s : Fin z, β * ∑ x, w x :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, hz⟩, mem_univ _⟩ (fun s _ => hcon s)
  have h2 : ∑ s : Fin z, ∑ x, w x * sg s x = ∑ x, w x * ∑ s, sg s x := by
    rw [Finset.sum_comm]; simp only [Finset.mul_sum]
  have h3 : ∑ x, w x * (β * z) ≤ ∑ x, w x * ∑ s, sg s x :=
    sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (hw x))
  have h4 : ∑ _s : Fin z, β * ∑ x, w x = ∑ x, w x * (β * z) := by
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← sum_mul]
    ring
  linarith

lemma sum_sign {z : ℕ} (P : Fin z → Prop) [DecidablePred P] :
    ∑ s, (if P s then (1:ℚ) else -1) = 2 * ((univ.filter P).card : ℚ) - z := by
  rw [Finset.sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin z))) P
  rw [card_univ, Fintype.card_fin] at this
  have h' : ((univ.filter P).card : ℚ) + ((univ.filter (fun s => ¬ P s)).card : ℚ) = z := by
    exact_mod_cast this
  linarith

lemma final_arith (C r : ℕ) (hr : 0 < r) : ∃ K : ℕ, 0 < K ∧ ∀ (e b t m g : ℕ), b ≤ e →
    t ≤ m → t ≤ e + g → 2^e ≤ C * (t+1)^r → 2^b ≤ K * (1 + min m g)^r := by
  refine ⟨C * 2^r + (C * 2^r)^2 * (2*r)^(2*r) + 1, by omega, ?_⟩
  intro e b t m g hbe htm hteg hmain
  have h2b : 2^b ≤ 2^e := Nat.pow_le_pow_right (by norm_num) hbe
  have hts : t ≤ min m g + e := by
    rcases le_total m g with h | h
    · rw [min_eq_left h]; omega
    · rw [min_eq_right h]; omega
  have hpos : 1 ≤ (1 + min m g)^r := Nat.one_le_pow _ _ (by omega)
  by_cases hes : e ≤ min m g
  · have ht : (t+1)^r ≤ 2^r * (1 + min m g)^r := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) r
    calc 2^b ≤ 2^e := h2b
      _ ≤ C * (t+1)^r := hmain
      _ ≤ C * (2^r * (1 + min m g)^r) := Nat.mul_le_mul_left _ ht
      _ = (C * 2^r) * (1 + min m g)^r := by ring
      _ ≤ (C * 2^r + (C * 2^r)^2 * (2*r)^(2*r) + 1) * (1 + min m g)^r :=
        Nat.mul_le_mul_right _ (by omega)
  · have ht : (t+1)^r ≤ 2^r * (e+1)^r := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) r
    have habs := Lin.polynomial_absorb (2*r) e (by omega)
    have h1 : 2^e ≤ C * 2^r * (e+1)^r :=
      calc 2^e ≤ C * (t+1)^r := hmain
        _ ≤ C * (2^r * (e+1)^r) := Nat.mul_le_mul_left _ ht
        _ = C * 2^r * (e+1)^r := by ring
    have hsq : 2^e * 2^e ≤ ((C * 2^r)^2 * (2*r)^(2*r)) * 2^e :=
      calc 2^e * 2^e ≤ (C * 2^r * (e+1)^r) * (C * 2^r * (e+1)^r) := Nat.mul_le_mul h1 h1
        _ = (C * 2^r)^2 * (e+1)^(2*r) := by ring
        _ ≤ (C * 2^r)^2 * ((2*r)^(2*r) * 2^e) := Nat.mul_le_mul_left _ habs
        _ = ((C * 2^r)^2 * (2*r)^(2*r)) * 2^e := by ring
    have hE : 2^e ≤ (C * 2^r)^2 * (2*r)^(2*r) :=
      Nat.le_of_mul_le_mul_right hsq (by positivity)
    calc 2^b ≤ 2^e := h2b
      _ ≤ (C * 2^r)^2 * (2*r)^(2*r) := hE
      _ ≤ (C * 2^r + (C * 2^r)^2 * (2*r)^(2*r) + 1) := by omega
      _ = (C * 2^r + (C * 2^r)^2 * (2*r)^(2*r) + 1) * 1 := by ring
      _ ≤ (C * 2^r + (C * 2^r)^2 * (2*r)^(2*r) + 1) * (1 + min m g)^r :=
        Nat.mul_le_mul_left _ hpos

lemma linearize_seed {a m c : ℕ} (Cc : Circuit) (tap : Fin c → ℕ)
    (read : (Fin c → Bool) → (Fin m → Fin a → Bool) → Bool)
    (legal : ∀ g ∈ Cc.gates, Lin.legalOp g) :
    ∃ (d t : ℕ) (f : Fin t → Fin m) (send : (Fin m → Fin a → Bool) → Fin (2^d))
      (read' : Fin (2^d) → (Fin m → Fin a → Bool) → Bool),
      d ≤ c ∧ t + d ≤ a*m + Lin.paidCount Cc.gates ∧ Function.Injective f ∧
      (∀ x y, send x = send y → x ∘ f = y ∘ f → x = y) ∧
      ∀ x y, read' (send x) y = read (fun j => (Cc.wires ((List.ofFn x).flatMap
        (fun v => List.ofFn v))).getD (tap j) false) y := by
  classical
  obtain ⟨k, hk, h, L, γ, hforms⟩ := Lin.affine_send (m := m) (a := a) Cc tap legal
  obtain ⟨hd, _, t, htd, f, hf, separate⟩ := Lin.coordinate_projection L h
  let : Fintype L.range := Fintype.ofFinite _
  have cardRange : Fintype.card L.range = 2^(Module.finrank (ZMod 2) L.range) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  let eqv : L.range ≃ Fin (2^(Module.finrank (ZMod 2) L.range)) :=
    Fintype.equivFinOfCardEq cardRange
  let send0 (x : Fin m → Fin a → Bool) : L.range := L.rangeRestrict (Lin.rawBits x, h x)
  let decode (zz : L.range) : Fin c → Bool := fun j => Lin.toField.symm (zz.val j + γ j)
  refine ⟨Module.finrank (ZMod 2) L.range, t, f, fun x => eqv (send0 x),
    fun cc y => read (decode (eqv.symm cc)) y, hd, ?_, hf, ?_, ?_⟩
  · rw [← hk]; exact htd
  · intro x y hxy hfxy
    exact separate x y (eqv.injective hxy) hfxy
  · intro x y
    simp only [Equiv.symm_apply_apply]
    apply congrArg (fun u => read u y)
    funext j
    change Lin.toField.symm (L (Lin.rawBits x, h x) j + γ j) = _
    rw [← hforms, Equiv.symm_apply_apply]
    rfl

lemma sum_mass (a m : ℕ) (hq : 5 ≤ 2^a) (x : Fin m → Fin (2^a)) :
    ∑ y : Fin m → Fin (2^a), ((((2^a - 3) ^ ((univ.filter (fun i => x i = y i)).card) : ℕ) : ℚ) /
      (((2 * (2^a - 2)) ^ m : ℕ) : ℚ)) = 1 := by
  rw [← sum_MM hq x]
  apply sum_congr rfl
  intro y _
  exact MM_eq hq x y

theorem lower_bound (a r : ℕ) (ha : 3 ≤ a) (hr : 0 < r) (β : ℚ)
    (hlo : (1 - 4 / ((2^a : ℕ) : ℚ))^(r+1) / (1 + (1 - 4 / ((2^a : ℕ) : ℚ))^(r+1)) < β) :
    ∃ K : ℕ, 0 < K ∧ ∀ m g : ℕ, 0 < m → ∀ b : ℕ, Works a m g β b →
      2^b ≤ K * (1 + min m g)^r := by
  have h8 : 8 ≤ 2^a := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) ha
    simpa using this
  have hq5 : 5 ≤ 2^a := by omega
  have h8q : (8:ℚ) ≤ ((2^a : ℕ) : ℚ) := by exact_mod_cast h8
  have hA0 : 0 ≤ (1 - 4 / ((2^a : ℕ) : ℚ))^(r+1) := by
    apply pow_nonneg
    rw [sub_nonneg, div_le_one (by linarith)]; linarith
  have hβ : (1 - 4 / ((2^a : ℕ) : ℚ))^(r+1) <
      (1 + (1 - 4 / ((2^a : ℕ) : ℚ))^(r+1)) * β := by
    rw [div_lt_iff₀ (by linarith)] at hlo; linarith
  obtain ⟨C0, hC0, hmain⟩ := main (2^a) (r+1) hq5 (by omega) β hβ
  obtain ⟨K, hK, harith⟩ := final_arith C0 r hr
  refine ⟨K, hK, ?_⟩
  intro m g hm b hwork
  obtain ⟨hb, z, Cs, tap, read, hz, hcs, hwin⟩ := hwork
  set A : ℚ := (1 - 4 / ((2^a : ℕ) : ℚ))^(r+1) with hA
  let e : (Fin a → Bool) ≃ Fin (2^a) := Fintype.equivFinOfCardEq (by simp)
  let N : ℚ := (((2^a)^m : ℕ) : ℚ)
  have hNpos : 0 < N := by positivity
  let eqs := fun (x y : Fin m → Fin (2^a)) => (univ.filter (fun i => x i = y i)).card
  let mass := fun (x y : Fin m → Fin (2^a)) =>
    ((((2^a - 3) ^ (eqs x y)) : ℕ) : ℚ) / (((2 * (2^a - 2)) ^ m : ℕ) : ℚ)
  let msg := fun (s : Fin z) (x : Fin m → Fin a → Bool) (j : Fin (a*m-b)) =>
    ((Cs s).wires ((List.ofFn x).flatMap (fun v => List.ofFn v))).getD (tap s j) false
  let sg := fun (s : Fin z) (p : (Fin m → Fin (2^a)) × (Fin m → Fin (2^a))) =>
    if read s (msg s (fun i => e.symm (p.1 i))) (fun i => e.symm (p.2 i)) =
      (eqs p.1 p.2 % 2 == 1) then (1:ℚ) else -1
  let w := fun (p : (Fin m → Fin (2^a)) × (Fin m → Fin (2^a))) =>
    1 / N^2 + A * (mass p.1 p.2 / N)
  have hmass0 : ∀ x y, 0 ≤ mass x y := fun x y => by positivity
  have hw0 : ∀ p, 0 ≤ w p := fun p => by
    have := hmass0 p.1 p.2
    positivity
  have hsg : ∀ p, β * z ≤ ∑ s, sg s p := by
    intro p
    have hp := hwin (fun i => e.symm (p.1 i)) (fun i => e.symm (p.2 i))
    have heqs : (univ.filter (fun i => e.symm (p.1 i) = e.symm (p.2 i))) =
        univ.filter (fun i => p.1 i = p.2 i) := by
      ext i; simp [e.symm.injective.eq_iff]
    rw [heqs] at hp
    have hs := sum_sign (z := z) (fun s => read s (msg s (fun i => e.symm (p.1 i)))
      (fun i => e.symm (p.2 i)) = (eqs p.1 p.2 % 2 == 1))
    change ∑ s, sg s p = _ at hs
    rw [hs]
    change (1+β)*(z : ℚ) ≤ 2*(((univ.filter (fun s => read s (msg s (fun i => e.symm (p.1 i)))
      (fun i => e.symm (p.2 i)) = (eqs p.1 p.2 % 2 == 1))).card : ℕ) : ℚ) at hp
    linarith
  obtain ⟨s, hs⟩ := avg_seed z hz w hw0 sg β hsg
  have hcard : (Fintype.card (Fin m → Fin (2^a)) : ℚ) = N := by
    simp [N, Fintype.card_fin]
  have hwsum : ∑ p, w p = 1 + A := by
    rw [Fintype.sum_prod_type]
    simp only [w, sum_add_distrib, ← mul_sum, ← sum_div]
    have h1 : ∀ x : Fin m → Fin (2^a), ∑ y : Fin m → Fin (2^a), mass x y = 1 :=
      fun x => sum_mass a m hq5 x
    simp only [h1, sum_const, card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hwsg : ∑ p, w p * sg s p = (∑ x, ∑ y, sg s (x, y)) / N^2 +
      A * ((∑ x, ∑ y, mass x y * sg s (x, y)) / N) := by
    rw [Fintype.sum_prod_type]
    simp only [w, add_mul, sum_add_distrib, sum_div, mul_sum]
    congr 1
    · apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
    · apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _; ring
  rw [hwsum, hwsg] at hs
  obtain ⟨d, t, f, send, read', hd, htd, hf, hsep, hread⟩ :=
    linearize_seed (Cs s) (tap s) (read s) (fun g hg => (hcs s).1.2 g hg)
  have hpaid : Lin.paidCount (Cs s).gates ≤ g := (hcs s).2.1
  have hfin := hmain m t f hf (fun _ => false) (fun _ => false) (2^d)
    (fun x => send (fun i => e.symm (x i))) (fun cc y => read' cc (fun i => e.symm (y i)))
    (by
      intro x y hxy hfxy
      have h1 := hsep _ _ hxy (by
        funext j
        exact congrArg e.symm (congrFun hfxy j))
      funext i
      exact e.symm.injective (congrFun h1 i))
    (by
      have hrw : ∀ x y : Fin m → Fin (2^a),
          (if read' (send (fun i => e.symm (x i))) (fun i => e.symm (y i)) =
            xor (xor false false) ((univ.filter (fun i => x i = y i)).card % 2 == 1)
            then (1:ℚ) else -1) = sg s (x, y) := by
        intro x y
        rw [hread]
        simp only [Bool.false_xor, Bool.xor_false]
        rfl
      simp only [hrw]
      have hN : (((2^a)^m : ℕ) : ℚ) = N := rfl
      rw [hN]
      calc (1 + A) * β = β * (1 + A) := by ring
        _ ≤ _ := hs)
  have hr1 : r + 1 - 1 = r := by omega
  rw [hr1] at hfin
  have hdle : d ≤ a*m := by omega
  have hsplit : (2:ℕ)^(a*m) = 2^(a*m-d) * 2^d := by
    rw [← pow_add]; congr 1; omega
  have hpow : (2^a)^m = 2^(a*m) := by rw [← pow_mul]
  rw [hpow, hsplit] at hfin
  have he : 2^(a*m-d) ≤ C0 * (t+1)^r := by
    have h2 : 2^(a*m-d) * 2^d ≤ (C0 * (t+1)^r) * 2^d := by
      calc 2^(a*m-d) * 2^d ≤ C0 * 2^d * (t+1)^r := hfin
        _ = (C0 * (t+1)^r) * 2^d := by ring
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
  have htm : t ≤ m := by
    have := Fintype.card_le_of_injective f hf
    simpa using this
  exact harith (a*m-d) b t m g (by omega) htm (by omega) he

end PEqualNP.Outside.L_lib_1026_aux.Lower

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

abbrev Syndrome (d : ℕ) := Fin d → ZMod 2
abbrev Pos (d : ℕ) := {v : Syndrome d // v ≠ 0}

theorem cardSyndrome (d : ℕ) : Fintype.card (Syndrome d) = 2 ^ d := by
  simp [Syndrome, ZMod.card]

theorem cardPos (d : ℕ) : Fintype.card (Pos d) = 2 ^ d - 1 := by
  classical
  unfold Pos
  rw [Fintype.card_subtype_compl, cardSyndrome]
  simp

def hbit (b : Bool) : ZMod 2 := if b then 1 else 0

theorem hbit_inj : Function.Injective hbit := by
  decide

def hsyn {d : ℕ} (x : Pos d → Bool) (j : Fin d) : ZMod 2 :=
  ∑ i, hbit (x i) * i.1 j

def project {d : ℕ} (s : Syndrome d) (x : Pos d → Bool) (i : Pos d) : Bool :=
  Bool.xor (x i) (decide (i.val = hsyn x + s))

def syndOption {d : ℕ} : Syndrome d ≃ Option (Pos d) where
  toFun v := if h : v = 0 then none else some ⟨v,h⟩
  invFun o := o.elim 0 Subtype.val
  left_inv v := by by_cases h : v = 0 <;> simp [h]
  right_inv o := by cases o with
    | none => simp
    | some i => simp [i.2]

def syndIndex {d : ℕ} (x : Pos d → Bool) : Syndrome d ≃ Option (Pos d) :=
  (Equiv.addLeft (hsyn x)).trans syndOption

theorem syndIndex_eq_some {d : ℕ} (s : Syndrome d) (x : Pos d → Bool) (i : Pos d) :
    syndIndex x s = some i ↔ i.val = hsyn x + s := by
  change syndOption (hsyn x + s) = some i ↔ _
  rw [← Equiv.eq_symm_apply]
  exact eq_comm

theorem project_eq_edit {d : ℕ} (s : Syndrome d) (x : Pos d → Bool) :
    project s x = fun i => Bool.xor (x i) (decide (syndIndex x s = some i)) := by
  funext i
  simp [project, syndIndex_eq_some]

theorem hsyn_project {d : ℕ} (s : Syndrome d) (x : Pos d → Bool) :
    hsyn (project s x) = s := by
  classical
  have ht (i : Pos d) : hbit (project s x i) =
      hbit (x i) + if i.val = hsyn x + s then 1 else 0 := by
    by_cases h : i.val = hsyn x + s <;> cases hx : x i <;> simp [project,h,hx,hbit]
    decide
  funext j
  have hc : (∑ i : Pos d, (if i.val = hsyn x + s then (1 : ZMod 2) else 0) * i.val j) =
      (hsyn x + s) j := by
    by_cases h : hsyn x + s = 0
    · rw [h]
      have hn (i : Pos d) : i.val ≠ 0 := i.property
      simp [hn]
    · let k : Pos d := ⟨hsyn x + s,h⟩
      have eqv (i : Pos d) : i.val = hsyn x + s ↔ i = k :=
        ⟨fun e => Subtype.ext e, fun e => congrArg Subtype.val e⟩
      simp [eqv, ite_mul, k]
  change (∑ i : Pos d, hbit (project s x i) * i.val j) = s j
  simp_rw [ht,add_mul]
  rw [Finset.sum_add_distrib,hc]
  change hsyn x j + (hsyn x j + s j) = s j
  rw [← add_assoc, ZModModule.add_self, zero_add]

def hpiv {d : ℕ} (j : Fin d) : Pos d :=
  ⟨fun l => if l = j then 1 else 0, by
    intro he
    have hx := congrFun he j
    simp at hx⟩

theorem hpiv_inj (d : ℕ) : Function.Injective (@hpiv d) := by
  intro j k he
  by_contra h
  have hc := congrFun (congrArg Subtype.val he) j
  simp [hpiv,h] at hc

theorem hsyn_ext {d : ℕ} {x y : Pos d → Bool} (hs : hsyn x = hsyn y)
    (hne : ∀ i, (∀ j, i ≠ hpiv j) → x i = y i) : x = y := by
  classical
  funext i
  by_cases h : ∃ j, i = hpiv j
  · obtain ⟨j,rfl⟩ := h
    let T := Finset.univ.erase (hpiv j)
    have hT : ∑ i ∈ T, hbit (x i) * i.val j = ∑ i ∈ T, hbit (y i) * i.val j := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hlp : ∃ k, l = hpiv k
      · obtain ⟨k,rfl⟩ := hlp
        have hkj : j ≠ k := by
          intro h
          subst k
          simp [T] at hl
        simp [hpiv,hkj]
      · rw [hne l (not_exists.mp hlp)]
    have split (w : Pos d → Bool) : (∑ i ∈ T, hbit (w i) * i.val j) + hbit (w (hpiv j)) =
        hsyn w j := by
      simp [hsyn,T,hpiv]
    apply hbit_inj
    apply add_left_cancel (a := ∑ i ∈ T, hbit (y i) * i.val j)
    rw [← hT, split x, hT, split y, hs]
  · exact hne i (not_exists.mp h)

abbrev keepBit {a d : ℕ} (p : Fin a) :=
  {z : Pos d × Fin a // z ∉ Set.range (fun j : Fin d => (hpiv j,p))}

open scoped Classical in
theorem cardKeepBit {a d : ℕ} (p : Fin a) :
    Fintype.card (keepBit (d := d) p) = Fintype.card (Pos d) * a - d := by
  classical
  have hi : Function.Injective (fun j : Fin d => (hpiv j,p)) :=
    fun _ _ h => hpiv_inj _ (congrArg Prod.fst h)
  calc
    _ = Fintype.card (Pos d × Fin a) - Fintype.card (Set.range (fun j : Fin d => (hpiv j,p))) :=
      Fintype.card_subtype_compl (fun z => z ∈ Set.range (fun j : Fin d => (hpiv j,p)))
    _ = _ := by rw [Fintype.card_congr (Equiv.ofInjective _ hi).symm]; simp

def wordProject {a d : ℕ} (p : Fin a) (s : Syndrome d) (x : Pos d → Fin a → Bool)
    (i : Pos d) (k : Fin a) : Bool :=
  if k = p then project s (fun u => x u p) i else x i k

theorem wordProject_eq_edit {a d : ℕ} (p : Fin a) (s : Syndrome d) (x : Pos d → Fin a → Bool)
    (i : Pos d) :
    wordProject p s x i = if syndIndex (fun u => x u p) s = some i then
      Function.update (x i) p (!(x i p)) else x i := by
  classical
  funext k
  by_cases h : syndIndex (fun u => x u p) s = some i <;> by_cases hk : k = p <;>
    simp [wordProject, project_eq_edit, h, hk, Function.update_of_ne]

def wordKeep {a d : ℕ} (p : Fin a) (x : Pos d → Fin a → Bool) (z : keepBit (d := d) p) : Bool :=
  x z.val.1 z.val.2

theorem wordKeep_ext {a d : ℕ} (p : Fin a) {x y : Pos d → Fin a → Bool}
    (hs : hsyn (fun i => x i p) = hsyn (fun i => y i p)) (hk : wordKeep p x = wordKeep p y) :
    x = y := by
  have atK (i : Pos d) (k : Fin a) (h : (i,k) ∉ Set.range (fun j : Fin d => (hpiv j,p))) :
      x i k = y i k := congrFun hk ⟨(i,k),h⟩
  have hbitsp : (fun i => x i p) = fun i => y i p := hsyn_ext hs (by
    intro i hn
    apply atK
    rintro ⟨j,hj⟩
    exact hn j (congrArg Prod.fst hj).symm)
  funext i k
  by_cases he : k = p
  · subst k
    exact congrFun hbitsp i
  · apply atK
    rintro ⟨j,hj⟩
    exact he (congrArg Prod.snd hj).symm

noncomputable def wordDecode {a d : ℕ} (p : Fin a) (s : Syndrome d) (b : keepBit (d := d) p → Bool) :
    Pos d → Fin a → Bool := by
  classical
  exact if h : ∃ x : Pos d → Fin a → Bool, hsyn (fun i => x i p) = s ∧ wordKeep p x = b then h.choose
    else fun _ _ => false

theorem wordDecode_spec {a d : ℕ} (p : Fin a) (s : Syndrome d) (x : Pos d → Fin a → Bool) :
    wordDecode p s (wordKeep p (wordProject p s x)) = wordProject p s x := by
  classical
  have hp : hsyn (fun i => wordProject p s x i p) = s := by
    simpa [wordProject] using hsyn_project s (fun i => x i p)
  have h : ∃ w : Pos d → Fin a → Bool, hsyn (fun i => w i p) = s ∧
      wordKeep p w = wordKeep p (wordProject p s x) := ⟨_,hp,rfl⟩
  rw [wordDecode,dite_eq_left h]
  exact wordKeep_ext p (h.choose_spec.1.trans hp.symm) h.choose_spec.2

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper.HashCore

open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_step_getD (gs : List Gate) :
    ∀ (x : List Bool) (i : ℕ), i < x.length → (gs.foldl step x).getD i false = x.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro x i hi
    simp only [List.foldl_cons]
    rw [ih _ i (by simp only [step, List.length_append, List.length_singleton]; omega)]
    simp only [step]
    exact List.getD_append _ _ _ _ hi

def bitsN (n : ℕ) (v : Fin n → F) : List Bool := List.ofFn (fun j : Fin n => decide (v j = 1))

theorem bitsN_length (n : ℕ) (v : Fin n → F) : (bitsN n v).length = n := by simp [bitsN]

theorem bitsN_getD (n : ℕ) (v : Fin n → F) (j : ℕ) (hj : j < n) :
    (bitsN n v).getD j false = decide (v ⟨j, hj⟩ = 1) := by
  simp [bitsN, List.getD_eq_getElem?_getD, hj]

def GOk (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧ (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.mod 2 ∨
    (h.op = GateOp.not ∧ h.inputs.length = 1))

noncomputable def costG (ds : List Gate) : ℕ :=
  ds.countP (fun h => @decide ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length = 2)
    (Classical.propDecidable _))

open scoped Classical

abbrev V (n : ℕ) := Fin n → F

theorem cardV (n : ℕ) : Fintype.card (V n) = 2^n := by simp [V,F]

def sendT {n q : ℕ} (C : Circuit) (tap : Fin q → ℕ) (x : V n) (j : Fin q) : Bool :=
  (C.wires (bitsN n x)).getD (tap j) false

def boolEquiv (n : ℕ) : V n ≃ (Fin n → Bool) where
  toFun x j := decide (x j = 1)
  invFun x j := if x j then 1 else 0
  left_inv x := by
    funext j
    have hb : ∀ a : F, (if decide (a=1) then (1:F) else 0) = a := by decide
    exact hb (x j)
  right_inv x := by funext j; cases h : x j <;> simp [h]

theorem sqF (a : F) : a*a = a := by revert a; decide

theorem eitherF (a : F) : a = 0 ∨ a = 1 := by revert a; decide

theorem quadratic_factors (N : ℕ) : ∀ (E : Type) [AddCommGroup E] [Module F E] [FiniteDimensional F E],
    Module.finrank F E = N → ∀ Q : QuadraticForm F E,
    ∃ (r : ℕ) (l : E →ₗ[F] F) (a b : Fin r → (E →ₗ[F] F)),
      r ≤ N/2 ∧ ∀ x, Q x = l x + ∑ j, a j x * b j x := by
  classical
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro E _ _ _ hN Q
    have addp (v w : E) : Q (v+w) = Q v + Q w + Q.polarBilin v w := QuadraticMap.map_add Q v w
    by_cases h : ∀ v w, Q.polarBilin v w = 0
    · let l : E →ₗ[F] F := {
        toFun := Q
        map_add' := fun x y => by rw [addp,h,add_zero]
        map_smul' := fun a x => by rw [Q.map_smul,sqF]; rfl }
      exact ⟨0,l,Fin.elim0,Fin.elim0,Nat.zero_le _,fun x => by simp [l]⟩
    push Not at h
    obtain ⟨v,w,hn⟩ := h
    have hvw : Q.polarBilin v w = 1 := (eitherF _).resolve_left hn
    have hwv : Q.polarBilin w v = 1 := (QuadraticMap.polar_comm Q w v).trans hvw
    have self (x : E) : Q.polarBilin x x = 0 := by
      change QuadraticMap.polar Q x x = 0
      rw [Q.polar_self]
      exact (show ∀ z : F, 2 • z = 0 by decide) (Q x)
    let A := Q.polarBilin v
    let B := Q.polarBilin w
    have Av : A v = 0 := self v
    have Aw : A w = 1 := hvw
    have Bv : B v = 1 := hwv
    have Bw : B w = 0 := self w
    let T := A.prod B
    let K := LinearMap.ker T
    have sur : Function.Surjective T := by
      rintro ⟨a,b⟩
      refine ⟨a • w + b • v, Prod.ext ?_ ?_⟩ <;> simp [T,Av,Aw,Bv,Bw]
    have dim : 2 + Module.finrank F K = N := by
      have hh := LinearMap.finrank_range_add_finrank_ker T
      rw [LinearMap.range_eq_top.mpr sur,finrank_top,hN] at hh
      simpa [K,Module.finrank_prod] using hh
    let R0 : E →ₗ[F] E := LinearMap.id - A.smulRight w - B.smulRight v
    have Rmem (x : E) : R0 x ∈ K := by
      apply LinearMap.mem_ker.mpr
      apply Prod.ext <;> simp [R0,T,Av,Aw,Bv,Bw]
    let R := R0.codRestrict K Rmem
    have decomp (x : E) : (R x : E) + A x • w + B x • v = x := by
      change x - A x • w - B x • v + A x • w + B x • v = x
      abel
    have qval (u : K) (a b : F) : Q (u.val + a • w + b • v) =
        Q u.val + a * Q w + b * Q v + a*b := by
      have ha : A u.val = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp u.property)
      have hb : B u.val = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp u.property)
      have huv : Q.polarBilin u.val v = 0 := (QuadraticMap.polar_comm Q _ _).trans ha
      have huw : Q.polarBilin u.val w = 0 := (QuadraticMap.polar_comm Q _ _).trans hb
      rcases eitherF a with rfl | rfl <;> rcases eitherF b with rfl | rfl <;>
        simp [addp,huv,huw,hwv,add_assoc]
      change Q.polarBilin u.val w + Q.polarBilin u.val v = 0
      rw [huw,huv,add_zero]
    obtain ⟨r,l,aa,bb,hr,hq⟩ := ih (Module.finrank F K) (by omega) K rfl (Q.comp K.subtype)
    refine ⟨r+1,l.comp R + (Q w) • A + (Q v) • B,
      Fin.cons A (fun j => (aa j).comp R), Fin.cons B (fun j => (bb j).comp R), by omega, ?_⟩
    intro x
    have hh := qval (R x) (A x) (B x)
    rw [decomp] at hh
    have hk : Q (R x : E) = l (R x) + ∑ j, aa j (R x) * bb j (R x) := hq (R x)
    rw [hh,hk,Fin.sum_univ_succ]
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.comp_apply,Fin.cons_zero,Fin.cons_succ]
    ring

def toField : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := z == 1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def paid (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

noncomputable def paidBool (g : Gate) : Bool := @decide (paid g) (Classical.propDecidable _)

noncomputable def paidCount (gs : List Gate) : ℕ := gs.countP paidBool

def legalOp (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun n => w.getD n false)]
@[local simp] theorem field_false : toField false = 0 := by decide +kernel
section Build

def readsBack (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < n+i.val

abbrev Plan (n : ℕ) :=
  {gs : List Gate // readsBack n gs ∧ ∀ g ∈ gs, legalOp g}

namespace Plan

abbrev gates {n : ℕ} (P : Plan n) : List Gate := P.val

theorem back {n : ℕ} (P : Plan n) : readsBack n P.gates := P.property.1

theorem legal {n : ℕ} (P : Plan n) : ∀ g ∈ P.gates, legalOp g := P.property.2

end Plan

def emptyPlan (n : ℕ) : Plan n := ⟨[], ⟨by simp [readsBack], by simp⟩⟩

def Evaluates {X : Type} {n : ℕ} (input : X → List Bool) (P : Plan n)
    (f : X → Bool) : Prop :=
  ∃ i, i < n+P.gates.length ∧ ∀ x, (P.gates.foldl appendWire (input x)).getD i false = f x

def adds {n : ℕ} (P D : Plan n) (k : ℕ) : Prop :=
  (∃ rest, D.gates = P.gates ++ rest) ∧ paidCount D.gates ≤ paidCount P.gates + k

theorem adds_refl {n : ℕ} (P : Plan n) : adds P P 0 :=
  ⟨⟨[],by simp⟩,by simp⟩

theorem adds_trans {n k l : ℕ} {P D E : Plan n} (h : adds P D k) (j : adds D E l) :
    adds P E (k+l) := by
  obtain ⟨⟨v,hv⟩,hk⟩ := h
  obtain ⟨⟨w,hw⟩,hl⟩ := j
  exact ⟨⟨v++w,by rw [hw,hv,List.append_assoc]⟩,by omega⟩

theorem adds_mono {n k l : ℕ} {P D : Plan n} (h : adds P D k) (le : k ≤ l) :
    adds P D l :=
  ⟨h.1,h.2.trans (Nat.add_le_add_left le _)⟩

theorem appendWire_length (gs : List Gate) (v : List Bool) :
    (gs.foldl appendWire v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih => simp [ih, appendWire]; omega

theorem appendWire_prefix (gs : List Gate) (v : List Bool) :
    ∃ w, gs.foldl appendWire v = v ++ w := by
  induction gs generalizing v with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨w,hw⟩ := ih (appendWire v g)
    refine ⟨[g.op.eval (g.inputs.map fun i => v.getD i false)] ++ w,?_⟩
    rw [List.foldl_cons, hw]
    simp [appendWire]

theorem getD_prefix (v w : List Bool) {i : ℕ} (hi : i < v.length) :
    (v++w).getD i false = v.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem evaluates_ext {X : Type} {n k : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) {P D : Plan n} {f : X → Bool}
    (h : Evaluates input P f) (extend : adds P D k) : Evaluates input D f := by
  obtain ⟨i,hi,hf⟩ := h
  obtain ⟨rest,hr⟩ := extend.1
  refine ⟨i,by rw [hr,List.length_append]; omega,?_⟩
  intro x
  rw [hr,List.foldl_append]
  obtain ⟨w,hw⟩ := appendWire_prefix rest (P.gates.foldl appendWire (input x))
  rw [hw, getD_prefix _ _ (by simpa [appendWire_length,size] using hi)]
  exact hf x

def planGate {n : ℕ} (P : Plan n) (g : Gate)
    (hprev : ∀ w ∈ g.inputs, w < n+P.gates.length) (hlegal : legalOp g) : Plan n := by
  refine ⟨P.gates ++ [g], ?_, ?_⟩
  ·
    intro i w hw
    by_cases h : i.val < P.gates.length
    · have eq : (P.gates ++ [g]).get i = P.gates.get ⟨i.val,h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left h]
      rw [eq] at hw
      exact P.back ⟨i.val,h⟩ w hw
    · have hi : i.val = P.gates.length := by
        have := i.isLt
        simp at this
        omega
      have eq : (P.gates ++ [g]).get i = g := by
        simp [List.get_eq_getElem, hi]
      rw [eq] at hw
      simpa [hi] using hprev w hw
  · intro h hh
    rcases List.mem_append.mp hh with old | new
    · exact P.legal h old
    · have : h = g := by simpa using new
      simpa [this] using hlegal

theorem emit_gate {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (op : GateOp) (w : List ℕ)
    (old : ∀ i ∈ w, i < n + P.gates.length) (legal : legalOp ⟨op,w⟩) :
    ∃ D, adds P D (paidCount [⟨op,w⟩]) ∧ Evaluates input D
      (fun x => op.eval (w.map fun i => (P.gates.foldl appendWire (input x)).getD i false)) := by
  let g : Gate := ⟨op,w⟩
  let D := planGate P g old legal
  refine ⟨D,⟨⟨[g],rfl⟩,?_⟩,n+P.gates.length,?_,?_⟩
  · simp [D,planGate,Plan.gates,paidCount,List.countP_append,g]
  · simp [D,planGate,Plan.gates]
  · intro x
    have index := appendWire_length P.gates (input x)
    rw [size] at index
    change ((P.gates ++ [g]).foldl appendWire (input x)).getD (n+P.gates.length) false = _
    rw [List.foldl_append]
    simp [appendWire, g, ← index, List.getD_eq_getElem?_getD]

theorem emit_const {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (b : Bool) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun _ => b) := by
  cases b
  · simpa [paidCount,paidBool,paid,GateOp.eval] using
      emit_gate size P .or [] (by simp) ⟨by simp,Or.inr (Or.inl rfl)⟩
  · simpa [paidCount,paidBool,paid,GateOp.eval] using
      emit_gate size P .and [] (by simp) ⟨by simp,Or.inl rfl⟩

theorem emit_not {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f : X → Bool} (hf : Evaluates input P f) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => !(f x)) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨D,hd,out⟩ := emit_gate size P .not [i] (by simpa using hi)
    ⟨by simp,Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩
  refine ⟨D,?_,?_⟩
  · simpa [paidCount,paidBool,paid] using hd
  · simpa [GateOp.eval,-List.getD_eq_getElem?_getD,hfi] using out

theorem emit_and {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f g : X → Bool} (hf : Evaluates input P f) (hg : Evaluates input P g) :
    ∃ D, adds P D 1 ∧ Evaluates input D (fun x => f x && g x) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨j,hj,hgj⟩ := hg
  have refs : ∀ w ∈ [i,j], w < n + P.gates.length := by
    simp_all
  obtain ⟨D,hd,out⟩ := emit_gate size P .and [i,j] refs ⟨by simp,Or.inl rfl⟩
  refine ⟨D,?_,?_⟩
  · simpa [paidCount,paidBool,paid] using hd
  · simpa [GateOp.eval,-List.getD_eq_getElem?_getD,hfi,hgj] using out

theorem emit_xor {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f g : X → Bool} (hf : Evaluates input P f) (hg : Evaluates input P g) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => Bool.xor (f x) (g x)) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨j,hj,hgj⟩ := hg
  have refs : ∀ w ∈ [i,j], w < n + P.gates.length := by
    simp_all
  obtain ⟨D,hd,out⟩ := emit_gate size P (.mod 2) [i,j] refs ⟨by simp,Or.inr (Or.inr (Or.inl rfl))⟩
  have cost : adds P D 0 := by simpa [paidCount,paidBool,paid] using hd
  obtain ⟨E,he,result⟩ := emit_not size D out
  have eq (x : X) :
      (!(GateOp.eval (.mod 2) [(P.gates.foldl appendWire (input x)).getD i false,
        (P.gates.foldl appendWire (input x)).getD j false])) = Bool.xor (f x) (g x) := by
    rw [hfi,hgj]
    cases f x <;> cases g x <;> rfl
  refine ⟨E,by simpa using adds_trans cost he,?_⟩
  change Evaluates input E (fun x => !(GateOp.eval (.mod 2)
    [(P.gates.foldl appendWire (input x)).getD i false,
      (P.gates.foldl appendWire (input x)).getD j false])) at result
  rw [funext eq] at result
  exact result

theorem build_many {X I J : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (k : ℕ)
    (s : Finset I) (f : I → J → X → Bool)
    (each : ∀ i ∈ s, ∀ (D : Plan n) (v : ℕ), adds P D v →
      ∃ E, adds D E k ∧ ∀ j, Evaluates input E (f i j)) :
    ∃ D, adds P D (s.card*k) ∧ ∀ i ∈ s, ∀ j, Evaluates input D (f i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P,by simpa using adds_refl P,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨D,extend,results⟩ := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,next,new⟩ := each i (Finset.mem_insert_self _ _) D _ extend
    refine ⟨E,by simpa [Finset.card_insert_of_notMem hi,Nat.add_mul] using adds_trans extend next,?_⟩
    intro j hj p
    rcases Finset.mem_insert.mp hj with eq | old
    · simpa [eq] using new p
    · exact evaluates_ext size (results j old p) next

end Build
open scoped BigOperators

section Synthesis

variable {X : Type} {n : ℕ} {input : X → List Bool}
variable (size : ∀ x, (input x).length = n)

theorem field_xor (a b : Bool) : toField (Bool.xor a b) = toField a + toField b := by
  cases a <;> cases b <;> decide +kernel

include size in
theorem emit_sum {I : Type} (P : Plan n) (S : Finset I) (f : I → X → Bool)
    (h : ∀ i ∈ S, Evaluates input P (f i)) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => toField.symm (∑ i ∈ S, toField (f i x))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [← field_false] using emit_const size P false
  | @insert i S hi ih =>
    obtain ⟨D,hd,prev⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have current := evaluates_ext size (h i (Finset.mem_insert_self _ _)) hd
    obtain ⟨E,he,sum⟩ := emit_xor size D current prev
    refine ⟨E,by simpa using adds_trans hd he,?_⟩
    have eq (x : X) :
        Bool.xor (f i x) (toField.symm (∑ j ∈ S, toField (f j x))) =
          toField.symm (∑ j ∈ insert i S, toField (f j x)) := by
      apply toField.injective
      simp [field_xor, Finset.sum_insert hi]
    simpa only [funext eq] using sum

include size in
theorem build_values {I : Type} (P : Plan n) (k : ℕ)
    (S : Finset I) (f : I → X → Bool)
    (each : ∀ i ∈ S, ∀ (D : Plan n) (v : ℕ), adds P D v →
      ∃ E, adds D E k ∧ Evaluates input E (f i)) :
    ∃ D, adds P D (S.card*k) ∧ ∀ i ∈ S, Evaluates input D (f i) := by
  obtain ⟨D,hd,h⟩ := build_many size P k S (fun i (_ : Unit) => f i) (by
    intro i hi D v hd
    obtain ⟨E,he,eval⟩ := each i hi D v hd
    exact ⟨E,he,fun _ => eval⟩)
  exact ⟨D,hd,fun i hi => h i hi ()⟩

end Synthesis

abbrev evF {n : ℕ} (P : Plan n) (f : V n → F) := Evaluates (bitsN n) P (fun x => toField.symm (f x))

theorem evF_ext {n k : ℕ} {P D : Plan n} {f : V n → F} (h : evF P f) (hd : adds P D k) :
    evF D f := evaluates_ext (bitsN_length n) h hd

theorem emit_addF {n : ℕ} (P : Plan n) {f g : V n → F} (hf : evF P f) (hg : evF P g) :
    ∃ D, adds P D 0 ∧ evF D (fun x => f x + g x) := by
  obtain ⟨D,hd,he⟩ := emit_xor (bitsN_length n) P hf hg
  refine ⟨D,hd,?_⟩
  have h (x : V n) : xor (toField.symm (f x)) (toField.symm (g x)) = toField.symm (f x + g x) :=
    toField.injective (by simp [field_xor])
  simpa only [funext h] using he

theorem emit_mulF {n : ℕ} (P : Plan n) {f g : V n → F} (hf : evF P f) (hg : evF P g) :
    ∃ D, adds P D 1 ∧ evF D (fun x => f x * g x) := by
  obtain ⟨D,hd,he⟩ := emit_and (bitsN_length n) P hf hg
  refine ⟨D,hd,?_⟩
  have h (a b : F) : (toField.symm a && toField.symm b) = toField.symm (a*b) := by revert a b; decide
  simpa only [h] using he

theorem emit_linear {n : ℕ} (P : Plan n) (L : V n →ₗ[F] F) :
    ∃ D, adds P D 0 ∧ evF D L := by
  classical
  let S := (Finset.univ : Finset (Fin n)).filter (fun i => L (Pi.single i (1:F)) = 1)
  have he (x : V n) : L x = ∑ i ∈ S, x i := by
    have hx : x = ∑ i, x i • Pi.single i (1:F) := by ext j; simp [Finset.sum_apply,Pi.single_apply]
    calc
      _ = L (∑ i, x i • Pi.single i 1) := congrArg L hx
      _ = _ := by
        rw [map_sum,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        rcases (show ∀ z : F, z = 0 ∨ z = 1 by decide) (L (Pi.single i 1)) with hh | hh <;> simp [hh]
  have hi (i : Fin n) : evF P (fun x => x i) := by
    refine ⟨i.val,by have := i.isLt; omega,?_⟩
    intro x
    change (P.gates.foldl step (bitsN n x)).getD i.val false = _
    rw [foldl_step_getD P.gates _ _ (by simp [bitsN]),bitsN_getD _ _ _ i.isLt]
    exact (show ∀ a : F, decide (a=1) = toField.symm a by decide) (x i)
  obtain ⟨D,hd,hdv⟩ := emit_sum (bitsN_length n) P S (fun i x => toField.symm (x i)) (fun i _ => hi i)
  refine ⟨D,hd,?_⟩
  unfold evF
  simpa only [Equiv.apply_symm_apply,he] using hdv

theorem emit_linproduct {n : ℕ} (P : Plan n) (L M : V n →ₗ[F] F) :
    ∃ D, adds P D 1 ∧ evF D (fun x => L x * M x) := by
  obtain ⟨D,hD,hL⟩ := emit_linear P L
  obtain ⟨E,hE,hM⟩ := emit_linear D M
  obtain ⟨G,hG,hout⟩ := emit_mulF E (evF_ext hL hE) hM
  exact ⟨G,by simpa using adds_trans (adds_trans hD hE) hG,hout⟩

theorem compile_message {n h t : ℕ} (L : Fin h → (V n →ₗ[F] F)) (K : V n →ₗ[F] V t)
    (c : F) (ell : V t →ₗ[F] F) (Q : QuadraticForm F (V t)) :
    ∃ (C : Circuit) (tap : Fin (h+1) → ℕ),
      (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
      (∀ G ∈ C.gates, GOk G) ∧ costG C.gates ≤ t/2 ∧
      (∀ j, tap j < n+C.gates.length) ∧
      (∀ x j, sendT C tap x j.succ = toField.symm (L j x)) ∧
      ∀ x, sendT C tap x 0 = toField.symm (c + ell (K x) + Q (K x)) := by
  classical
  obtain ⟨r,l,a,b,hr,hq⟩ := quadratic_factors t (V t) (by simp [V]) Q
  let P := emptyPlan n
  obtain ⟨D,hD,haddr⟩ := build_values (bitsN_length n) P 0 Finset.univ
    (fun j x => toField.symm (L j x)) (fun j _ E _ _ => emit_linear E (L j))
  let prod := fun (j : Fin r) (x : V n) => a j (K x) * b j (K x)
  obtain ⟨E,hE,hterms⟩ := build_values (bitsN_length n) D 1 Finset.univ
    (fun j x => toField.symm (prod j x)) (fun j _ G _ _ => emit_linproduct G ((a j).comp K) ((b j).comp K))
  obtain ⟨G,hG,hqsum⟩ := emit_sum (bitsN_length n) E Finset.univ
    (fun j x => toField.symm (prod j x)) hterms
  have hsum : evF G (fun x => ∑ j, prod j x) := by
    simpa only [evF,Equiv.apply_symm_apply] using hqsum
  obtain ⟨H,hH,hl⟩ := emit_linear G ((ell+l).comp K)
  obtain ⟨I,hI,hout⟩ := emit_addF H hl (evF_ext hsum hH)
  obtain ⟨J,hJ,hconst⟩ := emit_const (bitsN_length n) I (toField.symm c)
  obtain ⟨S,hS,hfinal⟩ := emit_addF J (f:=fun _ => c) hconst (evF_ext hout hJ)
  have hext := adds_trans (adds_trans (adds_trans (adds_trans (adds_trans hE hG) hH) hI) hJ) hS
  have cost := (adds_trans hD hext).2
  have costS : paidCount S.gates ≤ t/2 := by
    simpa [P,emptyPlan,Plan.gates,paidCount] using cost.trans (show _ ≤ t/2 by simpa [P,emptyPlan,Plan.gates,paidCount] using hr)
  obtain ⟨last,hlast,hval⟩ := hfinal
  have addrs (j : Fin h) := evaluates_ext (bitsN_length n) (haddr j (Finset.mem_univ _)) hext
  choose tp htp htv using addrs
  refine ⟨⟨S.gates,0⟩, Fin.cases last tp,S.back,S.legal,costS,Fin.cases hlast htp,?_,?_⟩
  · intro x j
    exact htv j x
  · intro x
    have := hval x
    change (S.gates.foldl appendWire (bitsN n x)).getD last false = _
    rw [this,hq]
    simp only [LinearMap.comp_apply,LinearMap.add_apply,prod]
    ring

def poly (n : ℕ) : Submodule F (V n → F) := by
  refine { carrier := {f | ∃ (c : F) (L : V n →ₗ[F] F) (Q : QuadraticForm F (V n)), ∀ x, f x = c + L x + Q x}, zero_mem' := ⟨0,0,0,by simp⟩, add_mem' := ?_, smul_mem' := ?_ }
  · rintro f g ⟨c,L,Q,h⟩ ⟨d,M,R,k⟩
    exact ⟨c+d,L+M,Q+R,fun x => by simp [h,k]; abel⟩
  · rintro c f ⟨d,L,Q,k⟩
    exact ⟨c*d,c•L,c•Q,fun x => by simp [k,mul_add]⟩

theorem affine_cut {n : ℕ} (a b c : V n) (hab : a ≠ b) (hac : a ≠ c) :
    ∃ (k : F) (L : V n →ₗ[F] F), k+L a = 1 ∧ k+L b = 0 ∧ k+L c = 0 := by
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ b i := by by_contra! h; exact hab (funext h)
  obtain ⟨j,hj⟩ : ∃ j, a j ≠ c j := by by_contra! h; exact hac (funext h)
  by_cases e : b i = c i
  · refine ⟨b i,LinearMap.proj i,?_⟩
    change b i + a i = 1 ∧ b i + b i = 0 ∧ b i + c i = 0
    exact (show ∀ x y z : F, x ≠ y → y = z → y+x=1 ∧ y+y=0 ∧ y+z=0 by decide) _ _ _ hi e
  by_cases f : b j = c j
  · refine ⟨c j,LinearMap.proj j,?_⟩
    change c j + a j = 1 ∧ c j+b j = 0 ∧ c j+c j = 0
    exact (show ∀ x y z : F, x ≠ z → y=z → z+x=1 ∧ z+y=0 ∧ z+z=0 by decide) _ _ _ hj f
  refine ⟨b i+b j,(LinearMap.proj i : V n →ₗ[F] F) + LinearMap.proj j,?_⟩
  exact (show ∀ x y z u v w : F, x ≠ y → y ≠ z → u ≠ w → v ≠ w →
    y+v+(x+u)=1 ∧ y+v+(y+v)=0 ∧ y+v+(z+w)=0 by
    intro x y z u v w h1 h2 h3 h4; fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases u <;> fin_cases v <;> fin_cases w <;> first | contradiction | exact ⟨rfl,rfl,rfl⟩) _ _ _ _ _ _ hi e hj f

theorem poly_indicator {n : ℕ} (a b c d : V n) (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) :
    ∃ p : poly n, p.val a=1 ∧ p.val b=0 ∧ p.val c=0 ∧ p.val d=0 := by
  obtain ⟨k,L,ha,hb,hc⟩ := affine_cut a b c ab ac
  obtain ⟨l,M,ha',hd,_⟩ := affine_cut a d d ad ad
  let f := fun x => (k+L x)*(l+M x)
  have hf : f ∈ poly n := ⟨k*l,k•M+l•L,QuadraticMap.linMulLin L M,fun x => by simp [f]; ring⟩
  exact ⟨⟨f,hf⟩,by simp [f,ha,ha'],by simp [f,hb],by simp [f,hc],by simp [f,hd]⟩

def phase (a : F) : ℝ := if a=0 then 1 else -1

theorem phase_zero : phase 0 = 1 := by simp [phase]
theorem phase_one : phase 1 = -1 := by simp [phase]
theorem phase_sq (a : F) : phase a * phase a = 1 := by unfold phase; split <;> norm_num
theorem phase_add (a b : F) : phase (a+b) = phase a * phase b := by
  have h : (1:F)+1=0 := by decide
  rcases eitherF a with rfl | rfl <;> rcases eitherF b with rfl | rfl <;> simp [h,phase_zero,phase_one]

noncomputable def signQ {n : ℕ} (s : poly n) (x : V n) : ℝ := phase (s.val x)

theorem shift_cancel {S : Type} [Fintype S] [AddCommGroup S] (f : S → ℝ) (d : S)
    (h : ∀ s, f (s+d) = -f s) : ∑ s, f s = 0 := by
  have he : (∑ s, f (s+d)) = ∑ s, f s := Fintype.sum_equiv (Equiv.addRight d) _ _ (fun s => rfl)
  simp_rw [h,Finset.sum_neg_distrib] at he
  linarith

theorem qpair {n : ℕ} (a b : V n) :
    (∑ s : poly n, signQ s a * signQ s b) = if a=b then (Fintype.card (poly n) : ℝ) else 0 := by
  classical
  by_cases h : a=b
  · subst b; simp [signQ,phase_sq]
  rw [ite_eq_right h]
  obtain ⟨p,h1,h2,_,_⟩ := poly_indicator a b b b h h h
  apply shift_cancel (d:=p)
  intro s
  change phase (s.val a+p.val a)*phase (s.val b+p.val b) = _
  simp only [phase_add,h1,h2,phase_one,phase_zero,signQ]
  ring

theorem qfour_unique {n : ℕ} (a b c d : V n) (ab : a≠b) (ac : a≠c) (ad : a≠d) :
    (∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d) = 0 := by
  obtain ⟨p,h1,h2,h3,h4⟩ := poly_indicator a b c d ab ac ad
  apply shift_cancel (d:=p)
  intro s
  change phase (s.val a+p.val a)*phase (s.val b+p.val b)*phase (s.val c+p.val c)*phase (s.val d+p.val d) = _
  simp only [phase_add,h1,h2,h3,h4,phase_one,phase_zero,signQ]
  ring

theorem qfour {n : ℕ} (a b c d : V n) :
    ∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d =
      if a=b then (if c=d then (Fintype.card (poly n) : ℝ) else 0)
      else if a=c then (if b=d then (Fintype.card (poly n) : ℝ) else 0)
      else if a=d then (if b=c then (Fintype.card (poly n) : ℝ) else 0) else 0 := by
  have hsq (s : poly n) (x : V n) : signQ s x * signQ s x = 1 := phase_sq _
  by_cases hab : a=b
  · subst b; simp only [hsq,one_mul,ite_true]; exact qpair c d
  simp only [hab,ite_false]
  by_cases hac : a=c
  · subst c; simp only [ite_true]
    rw [← qpair b d]
    apply Finset.sum_congr rfl
    intro s _
    linear_combination (signQ s b * signQ s d) * hsq s a
  simp only [hac,ite_false]
  by_cases had : a=d
  · subst d; simp only [ite_true]
    rw [← qpair b c]
    apply Finset.sum_congr rfl
    intro s _
    linear_combination (signQ s b * signQ s c) * hsq s a
  simpa [had] using qfour_unique a b c d hab hac had

noncomputable def smix {n : ℕ} (u : V n → ℝ) (s : poly n) : ℝ := ∑ x, u x * signQ s x

theorem qsecond {n : ℕ} (u : V n → ℝ) :
    ∑ s : poly n, (smix u s)^2 = (Fintype.card (poly n) : ℝ) * ∑ x, (u x)^2 := by
  classical
  have ex (s : poly n) : (smix u s)^2 = ∑ a, ∑ b, (u a*u b) * (signQ s a * signQ s b) := by
    simp only [smix,pow_two,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))
  simp_rw [ex]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,qpair]
  simp [mul_ite,sq,mul_comm]

theorem qweight {n : ℕ} (u : V n → ℝ) (a b c d : V n) :
    (u a*u b*u c*u d) * (∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d) ≤
      (if d=c then if b=a then (Fintype.card (poly n) : ℝ)*(u a)^2*(u c)^2 else 0 else 0) +
      (if d=b then if c=a then (Fintype.card (poly n) : ℝ)*(u a)^2*(u b)^2 else 0 else 0) +
      (if d=a then if c=b then (Fintype.card (poly n) : ℝ)*(u a)^2*(u b)^2 else 0 else 0) := by
  have hfour (x : V n) : 0 ≤ (Fintype.card (poly n) : ℝ) * (u x)^4 := by positivity
  rw [qfour]
  split_ifs <;> subst_vars <;> simp_all only [not_true_eq_false,zero_add,add_zero,mul_zero] <;>
    first | ring_nf; positivity | ring_nf; rfl | nlinarith [hfour d]

theorem qfourth {n : ℕ} (u : V n → ℝ) :
    ∑ s : poly n, (smix u s)^4 ≤ (Fintype.card (poly n) : ℝ) * (3*(∑ x, (u x)^2)^2) := by
  classical
  let N := (Fintype.card (poly n) : ℝ)
  have ex (s : poly n) : (smix u s)^4 = ∑ a, ∑ b, ∑ c, ∑ d,
      (u a*u b*u c*u d) * (signQ s a * signQ s b * signQ s c * signQ s d) := by
    rw [show (smix u s)^4 = smix u s * smix u s * smix u s * smix u s by ring]
    simp only [smix,Finset.sum_mul,Finset.mul_sum]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    ring
  calc
    _ = ∑ a, ∑ b, ∑ c, ∑ d, (u a*u b*u c*u d) * (∑ s : poly n, signQ s a * signQ s b * signQ s c * signQ s d) := by
      simp_rw [ex]
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro b _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro c _
      rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro d _
      rw [Finset.mul_sum]
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
      ((if d=c then if b=a then N*(u a)^2*(u c)^2 else 0 else 0) +
       (if d=b then if c=a then N*(u a)^2*(u b)^2 else 0 else 0) +
       (if d=a then if c=b then N*(u a)^2*(u b)^2 else 0 else 0)) := by
      repeat' (apply Finset.sum_le_sum; intro _ _)
      apply qweight
    _ = _ := by
      simp [Finset.sum_add_distrib,Finset.sum_ite_irrel,← Finset.mul_sum,← Finset.sum_mul,N]
      ring

noncomputable def mixL {I S : Type} [Fintype I] (σ : I → S → ℝ) :
    (I → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun u s := ∑ i, u i * σ i s
  map_add' a b := by ext s; simp [add_mul,Finset.sum_add_distrib]
  map_smul' c a := by ext s; simp [mul_assoc,Finset.mul_sum]

noncomputable def valL {I : Type} [Fintype I] (a : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ i, u i * a i
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' c u := by simp [mul_assoc,Finset.mul_sum]

noncomputable def absSum (S : Type) [Fintype S] : Seminorm ℝ (S → ℝ) := by
  refine { toFun := fun f => ∑ s, |f s|, map_zero' := by simp, add_le' := ?_, neg' := ?_, smul' := ?_ }
  · intro f g; simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s:=Finset.univ) (fun s _ => abs_add_le (f s) (g s))
  · intro f; simp
  · intro c f; simp [abs_mul,Finset.mul_sum,Real.norm_eq_abs]

theorem bounded_decoder {I S : Type} [Fintype I] [Fintype S] (σ : I → S → ℝ) (a : I → ℝ)
    (h : ∀ u, valL a u ≤ absSum S (mixL σ u)) :
    ∃ d : S → ℝ, (∀ s, |d s| ≤ 1) ∧ ∀ i, ∑ s, σ i s * d s = a i := by
  classical
  let A := mixL σ
  let Z := valL a
  obtain ⟨B,hB⟩ := A.rangeRestrict.exists_rightInverse_of_surjective A.range_rangeRestrict
  have sub (v : LinearMap.range A) : A (B v) = v.val := congrArg Subtype.val (LinearMap.congr_fun hB v)
  have ker (u : I → ℝ) (hu : A u = 0) : Z u = 0 := by
    have hp : Z u ≤ absSum S (A u) := h u
    have hn : Z (-u) ≤ absSum S (A (-u)) := h (-u)
    rw [hu,map_zero] at hp
    rw [map_neg,map_neg,hu,neg_zero,map_zero] at hn
    linarith
  let f := Z.comp B
  have hd (v : LinearMap.range A) : f v ≤ absSum S v.val := by
    change Z (B v) ≤ _
    exact (h (B v)).trans_eq (congrArg (absSum S) (sub v))
  obtain ⟨g,hg,hbound⟩ := Module.Dual.exists_extension_of_le_seminorm_real (LinearMap.range A) f hd
  have he (u : I → ℝ) : g (A u) = Z u := by
    have hk := ker (B (A.rangeRestrict u)-u) (by rw [map_sub,sub]; exact sub_self _)
    rw [map_sub] at hk
    calc
      _ = f (A.rangeRestrict u) := hg _
      _ = _ := sub_eq_zero.mp hk
  refine ⟨fun s => g (Pi.single s 1),?_,?_⟩
  · intro s
    have hb := hbound (Pi.single s 1)
    change |g (Pi.single s 1)| ≤ ∑ j : S, |(Pi.single s (1:ℝ)) j| at hb
    simpa [Pi.single_apply,abs_ite] using hb
  · intro i
    have hm : A (Pi.single i 1) = σ i := by ext s; simp [A,mixL,Pi.single_apply]
    have hz : Z (Pi.single i 1) = a i := by simp [Z,valL,Pi.single_apply]
    have hs : σ i = ∑ s, σ i s • Pi.single s (1:ℝ) := by ext j; simp [Finset.sum_apply,Pi.single_apply]
    calc
      _ = g (σ i) := by conv_rhs => rw [hs,map_sum]; simp only [map_smul,smul_eq_mul]
      _ = _ := by rw [← hm,he,hz]

theorem moment_l1 {S : Type} [Fintype S] [Nonempty S] (X : S → ℝ) (Z : ℝ)
    (hz : 0 ≤ Z) (h2 : ∑ s, (X s)^2 = (Fintype.card S : ℝ)*Z)
    (h4 : ∑ s, (X s)^4 ≤ (Fintype.card S : ℝ)*(3*Z^2)) :
    (Fintype.card S : ℝ)^2*Z ≤ 3*(∑ s, |X s|)^2 := by
  let N := (Fintype.card S : ℝ)
  let M := ∑ s, |X s|
  let T := ∑ s, |X s|^3
  let V4 := ∑ s, (X s)^4
  have hn : 0 < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have ha (x : ℝ) : |x|^2 = x^2 := sq_abs x
  have eq4 (x : ℝ) : (x^2)^2 = |x| * |x|^3 := by
    rw [← ha x]; ring
  have eq6 (x : ℝ) : (|x|^3)^2 = x^2*x^4 := by
    rw [show (|x|^3)^2 = (|x|^2)^3 by ring,ha]; ring
  have h23 : (N*Z)^2 ≤ M*T := by
    rw [← h2]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun s _ => abs_nonneg (X s))
      (fun s _ => pow_nonneg (abs_nonneg (X s)) 3) (fun s _ => (eq4 (X s)).le)
  have h34 : T^2 ≤ (N*Z)*V4 := by
    rw [← h2]
    exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun s _ => sq_nonneg (X s))
      (fun s _ => by positivity) (fun s _ => (eq6 (X s)).le)
  by_cases h0 : Z=0
  · simp [h0]; positivity
  have hZ : 0 < Z := lt_of_le_of_ne hz (Ne.symm h0)
  have hu : (N*Z)^4 ≤ M^2 * ((N*Z)*(N*(3*Z^2))) := by
    calc (N*Z)^4 = ((N*Z)^2)^2 := by ring
         _ ≤ (M*T)^2 := pow_le_pow_left₀ (sq_nonneg _) h23 2
         _ = M^2 * T^2 := mul_pow M T 2
         _ ≤ M^2 * ((N*Z)*V4) := mul_le_mul_of_nonneg_left h34 (sq_nonneg M)
         _ ≤ _ := by gcongr
  change N^2*Z ≤ 3*M^2
  apply le_of_mul_le_mul_left (a := N^2*Z^3) _ (by positivity)
  nlinarith only [hu]

theorem quadratic_decoder {n : ℕ} (a : V n → ℝ) (ha : 3*(∑ i, (a i)^2) ≤ 1) :
    ∃ d : poly n → ℝ, (∀ s, |d s| ≤ 1) ∧
      ∀ i, ∑ s, signQ s i * d s = (Fintype.card (poly n) : ℝ)*a i := by
  classical
  let N := (Fintype.card (poly n) : ℝ)
  apply bounded_decoder (fun i s => signQ s i) (fun i => N*a i)
  intro u
  let Z := ∑ i, (u i)^2
  let T := ∑ i, (a i)^2
  let M := ∑ s, |smix u s|
  let v := ∑ i, u i * a i
  have mom : N^2*Z ≤ 3*M^2 := moment_l1 (smix u) Z (by dsimp [Z]; positivity) (qsecond u) (qfourth u)
  have cs : v^2 ≤ Z*T := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hs : (N*v)^2 ≤ M^2 := by
    calc (N*v)^2 = N^2*v^2 := mul_pow _ _ 2
         _ ≤ N^2*(Z*T) := mul_le_mul_of_nonneg_left cs (sq_nonneg _)
         _ = (N^2*Z)*T := by ring
         _ ≤ (3*M^2)*T := mul_le_mul_of_nonneg_right mom (by dsimp [T]; positivity)
         _ = M^2*(3*T) := by ring
         _ ≤ M^2*1 := mul_le_mul_of_nonneg_left ha (sq_nonneg _)
         _ = _ := mul_one _
  have mpos : 0 ≤ M := by dsimp [M]; positivity
  have hl := (le_abs_self (N*v)).trans ((sq_le_sq.mp hs).trans_eq (abs_of_nonneg mpos))
  change ∑ i, u i * (N*a i) ≤ M
  calc _ = N*v := by dsimp [v]; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
       _ ≤ _ := hl

abbrev Aut (n : ℕ) := V n ≃ₗ[F] V n

theorem move_nonzero {n : ℕ} (u v : V n) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ e : Aut n, e u = v := by
  obtain ⟨k,L,hk,hl,hm⟩ := affine_cut (0:V n) u v hu.symm hv.symm
  have h1 : k=1 := by simpa using hk
  have lu : L u=1 := (show ∀ x : F, 1+x=0 → x=1 by decide) _ (h1 ▸ hl)
  have lv : L v=1 := (show ∀ x : F, 1+x=0 → x=1 by decide) _ (h1 ▸ hm)
  let T : V n →ₗ[F] V n := LinearMap.id + L.smulRight (u+v)
  have lf (x : V n) : L (T x) = L x := by simp [T,lu,lv]; exact (show ∀ a : F, a+a=0 by decide) (L x)
  have inv : Function.Involutive T := by
    intro x
    change T x + L (T x) • (u+v) = x
    rw [lf]
    change (x + L x • (u+v)) + L x • (u+v) = x
    rw [add_assoc,← add_smul,show L x+L x=0 from (show ∀ a : F, a+a=0 by decide) (L x),zero_smul,add_zero]
  refine ⟨LinearEquiv.ofBijective T inv.bijective,?_⟩
  change u + L u • (u+v) = v
  have hu0 : u+u=0 := by ext j; exact (show ∀ a : F, a+a=0 by decide) (u j)
  rw [lu,one_smul,← add_assoc,hu0,zero_add]

noncomputable def collN {n h t : ℕ} [Fintype (Aut n)] (R : V n ≃ₗ[F] V h × V t) (v : V n) : ℚ :=
  ∑ e : Aut n, if (R (e v)).1=0 then 1 else 0

theorem hash_collision {n h t : ℕ} [Fintype (Aut n)] (R : V n ≃ₗ[F] V h × V t)
    (hn : n=h+t) (x z : V n) (hx : x ≠ z) :
    (2:ℚ)^h * (∑ e : Aut n, if (R (e x)).1 = (R (e z)).1 then (1:ℚ) else 0) ≤
      (Fintype.card (Aut n) : ℚ) := by
  classical
  let d := x-z
  have hdn : d≠0 := sub_ne_zero.mpr hx
  have minc (w : V n) : collN R d ≤ collN R w := by
    by_cases hw : w=0
    · subst w; unfold collN; apply Finset.sum_le_sum; intro e _; split <;> simp
    obtain ⟨g,hg⟩ := move_nonzero d w hdn hw
    let perm : Aut n ≃ Aut n := {
      toFun := fun e => g.trans e
      invFun := fun e => g.symm.trans e
      left_inv := fun e => by ext i; simp
      right_inv := fun e => by ext i; simp }
    let f := fun e : Aut n => if (R (e d)).1=0 then (1:ℚ) else 0
    apply le_of_eq
    calc collN R d = ∑ e : Aut n, f (perm e) := (Equiv.sum_comp perm f).symm
         _ = _ := by simp [collN,f,perm,hg]
  have per (e : Aut n) : (∑ d : V n, if (R (e d)).1=0 then (1:ℚ) else 0) = 2^t := by
    let f := fun p : V h × V t => if p.1=0 then (1:ℚ) else 0
    calc _ = ∑ p : V h × V t, f p := Equiv.sum_comp (e.trans R).toEquiv f
         _ = _ := by
           rw [Fintype.sum_prod_type]
           trans ∑ a : V h, if a=0 then (2:ℚ)^t else 0
           · apply Finset.sum_congr rfl; intro a _; by_cases ha : a=0 <;> simp [f,ha]
           · simp
  have total : (∑ v : V n, collN R v) = (Fintype.card (Aut n):ℚ) * 2^t := by
    unfold collN
    rw [Finset.sum_comm]
    simp_rw [per]
    simp
  have cm : (2:ℚ)^n * collN R d ≤ (Fintype.card (Aut n):ℚ) * 2^t := by
    calc _ = ∑ _w : V n, collN R d := by simp
         _ ≤ _ := Finset.sum_le_sum (fun w _ => minc w)
         _ = _ := total
  have eq : (∑ e : Aut n, if (R (e x)).1 = (R (e z)).1 then (1:ℚ) else 0) = collN R d := by
    simp [collN,d,sub_eq_zero]
  rw [eq]
  apply le_of_mul_le_mul_right (a:=(2:ℚ)^t) _ (by positivity)
  rw [show (2:ℚ)^n = 2^h*2^t by rw [hn,pow_add]] at cm
  linarith only [cm]

theorem round_orthogonal {I S : Type} [Fintype I] [Fintype S] [Nonempty S] [DecidableEq I]
    (σ : I → S → ℚ) (a : I → ℚ) (d : S → ℝ) (hb : ∀ s, |d s| ≤ 31/32)
    (hs : ∀ i s, |σ i s| = 1)
    (hp : ∀ i j, ∑ s, σ i s * σ j s = if i=j then (Fintype.card S : ℚ) else 0)
    (hd : ∀ i, ∑ s, (σ i s : ℝ)*d s = (Fintype.card S : ℝ)*a i) :
    ∃ c : S → ℚ, (∀ s, |c s| ≤ 1) ∧ ∀ i, ∑ s, σ i s*c s = (Fintype.card S : ℚ)*a i := by
  classical
  let N := (Fintype.card S : ℚ)
  let ε := 1/(64*((Fintype.card I : ℝ)+1))
  have heps : 0 < ε := by dsimp [ε]; positivity
  have hn : (0:ℚ) < N := by dsimp [N]; exact_mod_cast Fintype.card_pos
  have hnr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hn
  have hex (s : S) : ∃ v : ℚ, |(v:ℝ)-d s| ≤ ε := by
    obtain ⟨v,hv1,hv2⟩ := exists_rat_btwn (show d s-ε < d s+ε by linarith)
    exact ⟨v,abs_le.mpr ⟨by linarith,by linarith⟩⟩
  choose v hv using hex
  let err := fun i => a i - (∑ s, σ i s * v s)/N
  have hcast (i s) : |(σ i s : ℝ)| = 1 := by exact_mod_cast hs i s
  have herr (i : I) : |(err i : ℝ)| ≤ ε := by
    have he : (N:ℝ) * (err i : ℝ) = ∑ s, (σ i s : ℝ)*(d s-v s) := by
      simp only [mul_sub,Finset.sum_sub_distrib,hd,err,Rat.cast_sub,Rat.cast_div,Rat.cast_sum,Rat.cast_mul]
      have hncast : (N:ℝ) = (Fintype.card S : ℝ) := by simp [N]
      rw [← hncast]
      field_simp
    apply le_of_mul_le_mul_left (a:=(N:ℝ)) _ hnr
    calc (N:ℝ)*|(err i:ℝ)| = |(N:ℝ)*(err i:ℝ)| := by rw [abs_mul,abs_of_pos hnr]
         _ = _ := congrArg abs he
         _ ≤ ∑ s, |(σ i s:ℝ)*(d s-v s)| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _s : S, ε := Finset.sum_le_sum (fun s _ => by rw [abs_mul,hcast,one_mul,abs_sub_comm]; exact hv s)
         _ = _ := by simp [N]
  refine ⟨fun s => v s + ∑ i, σ i s*err i,?_,?_⟩
  · intro s
    have hv1 : |(v s:ℝ)| ≤ 31/32+ε := by
      have tmp := abs_add_le ((v s:ℝ)-d s) (d s)
      rw [sub_add_cancel] at tmp
      linarith [hv s,hb s]
    have hcorr : |∑ i, (σ i s:ℝ)*(err i:ℝ)| ≤ (Fintype.card I:ℝ)*ε := by
      calc _ ≤ ∑ i, |(σ i s:ℝ)*(err i:ℝ)| := Finset.abs_sum_le_sum_abs _ _
           _ ≤ ∑ _i : I, ε := Finset.sum_le_sum (fun i _ => by rw [abs_mul,hcast,one_mul]; exact herr i)
           _ = _ := by simp
    have he0 : ((Fintype.card I:ℝ)+1)*ε = 1/64 := by dsimp [ε]; field_simp
    have hrat : |(v s:ℝ)+∑ i, (σ i s:ℝ)*(err i:ℝ)| ≤ 1 := by
      have h := abs_add_le (v s:ℝ) (∑ i, (σ i s:ℝ)*(err i:ℝ))
      nlinarith only [h,hv1,hcorr,he0]
    exact_mod_cast hrat
  · intro i
    calc
      _ = (∑ s, σ i s * v s) + ∑ j, (∑ s, σ i s * σ j s)*err j := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm (f:=fun s j => σ i s * (σ j s * err j))]
        simp [mul_assoc]
      _ = (∑ s, σ i s * v s) + N*err i := by simp [hp,ite_mul,N]
      _ = _ := by dsimp only [err]; field_simp [hn.ne']; dsimp [N]; ring

def gain (v : ℚ) : ℚ := (31/16)/(1+3*v)

noncomputable def bucketMass {I B : Type} [Fintype I] [DecidableEq B] (A : I → B) (w : I → ℚ) (b : B) : ℚ :=
  ∑ z, (w z)^2 * (if A z=b then 1 else 0)

theorem gain_average {I S B : Type} [Fintype I] [Fintype S] [DecidableEq B]
    (A : S → I → B) (w : I → ℚ) (x : I) (H : ℚ) (hH : 0 < H)
    (hl : 0 ≤ w x) (hh : w x ≤ 1/2) (mass : 16*(∑ z, (w z)^2) ≤ H)
    (col : ∀ z, z≠x → H*(∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ Fintype.card S) :
    (Fintype.card S : ℚ) ≤ ∑ s, gain (bucketMass (A s) w (A s x)) := by
  classical
  let N := (Fintype.card S : ℚ)
  have hn : 0 ≤ N := Nat.cast_nonneg _
  have c (z : I) : (∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ N/H + if z=x then N else 0 := by
    by_cases hz : z=x
    · subst z; simp [N]; positivity
    · rw [ite_eq_right hz,add_zero]
      apply (le_div_iff₀ hH).2
      simpa [mul_comm] using col z hz
  let V0 := fun s => bucketMass (A s) w (A s x)
  have htotal : ∑ s, V0 s ≤ N*(5/16) := by
    have ex : ∑ s, V0 s = ∑ z, (w z)^2*(∑ s, if A s z=A s x then (1:ℚ) else 0) := by
      dsimp only [V0,bucketMass]; rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    rw [ex]
    calc _ ≤ ∑ z, (w z)^2 * (N/H + if z=x then N else 0) :=
              Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (c z) (sq_nonneg _))
         _ = (∑ z, (w z)^2)*(N/H) + (w x)^2*N := by simp [mul_add,mul_ite,Finset.sum_add_distrib,Finset.sum_mul]
         _ ≤ (H/16)*(N/H) + (1/2)^2*N := by
              gcongr
              · linarith
         _ = _ := by field_simp; ring
  have vpos s : 0 ≤ V0 s := by
    unfold V0 bucketMass; exact Finset.sum_nonneg (fun z _ => mul_nonneg (sq_nonneg _) (by split <;> norm_num))
  have tan (s : S) : 1 - (48/31)*(V0 s-5/16) ≤ gain (V0 s) := by
    apply (le_div_iff₀ (show 0 < 1+3*V0 s by linarith [vpos s])).2
    nlinarith [sq_nonneg (V0 s-5/16)]
  have summ := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => tan s)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one] at summ
  change N ≤ ∑ s, gain (V0 s)
  change N-48/31*(∑ s, V0 s - _ ) ≤ _ at summ
  linarith

def signR {n : ℕ} (p : poly n) (x : V n) : ℚ := if p.val x=0 then 1 else -1

theorem sign_cast {n : ℕ} (p : poly n) (x : V n) : (signR p x : ℝ) = signQ p x := by
  by_cases h : p.val x = 0 <;> simp [signR,signQ,phase,h]

theorem rational_bucket {n : ℕ} (a : V n → ℚ) :
    ∃ d : poly n → ℚ, (∀ s, |d s| ≤ 1) ∧
      ∀ i, ∑ s, signR s i * d s = (Fintype.card (poly n) : ℚ) * (gain (∑ j, (a j)^2) * a i) := by
  classical
  let S := ∑ i, (a i)^2
  let c : ℚ := 2/(1+3*S)
  have hs : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hpos : 0 < 1+3*S := by linarith
  have hh : 3 * ∑ i, (c*a i)^2 ≤ 1 := by
    simp only [mul_pow,← Finset.mul_sum]
    change 3*(c^2*S) ≤ 1
    dsimp [c]
    field_simp
    nlinarith [sq_nonneg (1-3*S)]
  obtain ⟨d,hb,hc⟩ := quadratic_decoder (fun i => ((c*a i:ℚ):ℝ)) (by exact_mod_cast hh)
  apply round_orthogonal (fun i s => signR s i) (fun i => gain S*a i) (fun s => (31/32)*d s)
  · intro s
    rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 31/32)]
    nlinarith [hb s]
  · intro i s
    unfold signR; split <;> norm_num
  · intro i j
    have hc2 := qpair i j
    by_cases h : i=j <;> simp only [h,ite_true,ite_false] at hc2 ⊢ <;>
      simp_rw [← sign_cast] at hc2 <;> exact_mod_cast hc2
  · intro i
    calc (∑ s, (signR s i : ℝ) * (31/32 * d s)) = (31/32)*∑ s, signQ s i*d s := by
           rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; rw [sign_cast]; ring
         _ = _ := by
           rw [hc i]
           simp [c,gain]
           ring

def bs (b : Bool) : ℚ := if b then -1 else 1

theorem bs_sq (b : Bool) : bs b * bs b = 1 := by cases b <;> norm_num [bs]
theorem abs_bs (b : Bool) : |bs b| = 1 := by cases b <;> norm_num [bs]

noncomputable def listVal {I B : Type} [DecidableEq B] (A : I → B) (tru : I → Bool)
    (D : Finset I) (b : B) (base : ℚ) : ℚ := by
  classical
  exact if h : ∃ z ∈ D, A z=b then bs (tru (Classical.choose h)) else base

theorem listVal_bound {I B : Type} [DecidableEq B] (A : I → B) (tru : I → Bool)
    (D : Finset I) (b : B) (base : ℚ) (hb : |base|≤1) : |listVal A tru D b base| ≤ 1 := by
  unfold listVal; split <;> simp [abs_bs,hb]

theorem list_point {I B : Type} [DecidableEq I] [DecidableEq B]
    (A : I → B) (tru : I → Bool) (x : I) (D : Finset I) (base : ℚ) (hb : |base|≤1) :
    (if x∈D then 1 else bs (tru x)*base) - 2*(((D.erase x).filter (fun z => A z=A x)).card : ℚ) ≤
      bs (tru x) * listVal A tru D (A x) base := by
  classical
  let E := (D.erase x).filter (fun z => A z=A x)
  by_cases hz : E.card=0
  · have alone (z : I) (hd : z∈D) (he : A z=A x) : z=x := by
      by_contra hn
      have hm : z∈E := Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hn,hd⟩,he⟩
      exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨z,hm⟩)) hz
    change (if x∈D then 1 else bs (tru x)*base) - 2*(E.card:ℚ) ≤ _
    simp only [hz,Nat.cast_zero,mul_zero,sub_zero]
    by_cases hx : x∈D
    · have h : ∃ z∈D, A z=A x := ⟨x,hx,rfl⟩
      have hc := Classical.choose_spec h
      simp [listVal,hx,h,alone _ hc.1 hc.2,bs_sq]
    · have h : ¬∃ z∈D, A z=A x := by rintro ⟨z,hd,he⟩; exact hx (alone z hd he ▸ hd)
      simp [listVal,hx,h]
  · have he : (1:ℚ) ≤ E.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hb2 := (abs_le.mp (show |bs (tru x) * listVal A tru D (A x) base| ≤ 1 by rw [abs_mul,abs_bs,one_mul]; exact listVal_bound _ _ _ _ _ hb)).1
    have hb1 := (abs_le.mp (show |bs (tru x)*base| ≤ 1 by simpa [abs_mul,abs_bs] using hb)).2
    change (if x∈D then 1 else bs (tru x)*base) - 2*(E.card:ℚ) ≤ _
    split <;> linarith

theorem list_average {I S B : Type} [Fintype S] [DecidableEq I] [DecidableEq B]
    (A : S → I → B) (x : I) (D : Finset I) (H : ℚ) (hH : 0 < H)
    (col : ∀ z, z≠x → H*(∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ Fintype.card S) :
    (∑ e, (((D.erase x).filter (fun z => A e z=A e x)).card : ℚ)) ≤
      (D.card:ℚ)*(Fintype.card S:ℚ)/H := by
  classical
  calc _ = ∑ z ∈ D.erase x, ∑ e, if A e z=A e x then (1:ℚ) else 0 := by
             simp_rw [Finset.natCast_card_filter]; rw [Finset.sum_comm]
       _ ≤ ∑ _z ∈ D.erase x, (Fintype.card S:ℚ)/H := Finset.sum_le_sum (fun z hz => by
             apply (le_div_iff₀ hH).2; simpa [mul_comm] using col z (Finset.ne_of_mem_erase hz))
       _ ≤ _ := by
             rw [Finset.sum_const,nsmul_eq_mul,← mul_div_assoc]
             have hcard : (D.erase x).card ≤ D.card := Finset.card_le_card (Finset.erase_subset _ _)
             exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)) hH.le

theorem list_total {I S B Q : Type} [Fintype S] [Fintype Q] [DecidableEq I] [DecidableEq B]
    (A : S → I → B) (tru : I → Bool) (x : I) (D : Finset I) (H w : ℚ) (hH : 0 < H)
    (base : S → Q → ℚ) (hb : ∀ s q, |base s q| ≤ 1)
    (lo : w * ((Fintype.card S:ℚ)*Fintype.card Q) ≤ ∑ s, ∑ q, bs (tru x)*base s q)
    (col : ∀ z, z≠x → H*(∑ s, if A s z=A s x then (1:ℚ) else 0) ≤ Fintype.card S) :
    ((if x∈D then 1 else w) - 2*D.card/H) * ((Fintype.card S:ℚ)*Fintype.card Q) ≤
      ∑ s, ∑ q, bs (tru x)*listVal (A s) tru D (A s x) (base s q) := by
  classical
  let E := fun s => (((D.erase x).filter (fun z => A s z=A s x)).card : ℚ)
  let N := (Fintype.card S : ℚ)
  let M := (Fintype.card Q : ℚ)
  let raw := fun s q => if x∈D then 1 else bs (tru x)*base s q
  have hpoint (s : S) (q : Q) : raw s q - 2*E s ≤ bs (tru x)*listVal (A s) tru D (A s x) (base s q) :=
    list_point (A s) tru x D _ (hb s q)
  have hraw : (if x∈D then 1 else w)*(N*M) ≤ ∑ s, ∑ q, raw s q := by
    by_cases hx : x∈D
    · simp [hx,raw,N,M]
    · simpa only [hx,ite_false,raw] using lo
  have herr : ∑ s, ∑ _q : Q, 2*E s ≤ (2*D.card/H)*(N*M) := by
    have he := list_average A x D H hH col
    change (∑ e, E e) ≤ (D.card:ℚ)*N/H at he
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
    change M * (2 * ∑ e, E e) ≤ _
    calc _ ≤ M*(2*((D.card:ℚ)*N/H)) := by gcongr
         _ = _ := by ring
  have agg := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => Finset.sum_le_sum (s:=Finset.univ) (fun q _ => hpoint s q))
  simp only [Finset.sum_sub_distrib] at agg
  change ((if x∈D then 1 else w) - 2*D.card/H) * (N*M) ≤ _
  linarith

theorem bucket_profile {n h t : ℕ} (T : V n ≃ₗ[F] V h × V t) (w : V n → ℚ) (b : V h) :
    bucketMass (fun x => (T x).1) w b = ∑ r : V t, (w (T.symm (b,r)))^2 := by
  classical
  calc _ = ∑ p : V h × V t, (w (T.symm p))^2*(if p.1=b then 1 else 0) :=
             Fintype.sum_equiv T.toEquiv _ _ (fun x => by simp)
       _ = _ := by
             rw [Fintype.sum_prod_type]
             trans ∑ a : V h, if a=b then (∑ z : V t, (w (T.symm (b,z)))^2) else 0
             · apply Finset.sum_congr rfl; intro a _; by_cases ha : a=b <;> simp [ha]
             · simp

noncomputable def msgH {n h t : ℕ} (R : V n ≃ₗ[F] V h × V t) (s : Aut n × poly t) (x : V n) : V h × Bool :=
  ((R (s.1 x)).1, toField.symm (s.2.val (R (s.1 x)).2))

theorem soft_protocol {n h t : ℕ} {Y : Type} [Fintype (Aut n)] (R : V n ≃ₗ[F] V h × V t) (hn : n=h+t)
    (truth : V n → Y → Bool) (w : V n → Y → ℚ) (D : Y → Finset (V n))
    (hw : ∀ x y, 0 ≤ w x y ∧ w x y ≤ 1/2) (mass : ∀ y, 16*(∑ x, (w x y)^2) ≤ (2:ℚ)^h) :
    ∃ p : (Aut n × poly t) → (V h × Bool) → Y → ℚ,
      (∀ s m y, |p s m y| ≤ 1) ∧ ∀ x y,
        ((if x∈D y then 1 else w x y)-2*(D y).card/(2:ℚ)^h) * (Fintype.card (Aut n × poly t):ℚ) ≤
          ∑ s, bs (truth x y)*p s (msgH R s x) y := by
  classical
  let E := fun e : Aut n => e.trans R
  let A := fun (e : Aut n) (x : V n) => (E e x).1
  let K := fun (e : Aut n) (x : V n) => (E e x).2
  let X := fun (e : Aut n) (b : V h) (r : V t) => (E e).symm (b,r)
  have get (e : Aut n) (x : V n) : X e (A e x) (K e x) = x := by simp [X,A,K]
  let a := fun e b y r => bs (truth (X e b r) y) * w (X e b r) y
  have en (e b y) : (∑ r, (a e b y r)^2) = bucketMass (A e) (fun z => w z y) b := by
    rw [bucket_profile (E e)]
    have hb (v:Bool) : (bs v)^2=1 := by rw [pow_two,bs_sq]
    simp [a,X,mul_pow,hb]
  have hex (e : Aut n) (b : V h) (y : Y) := rational_bucket (a e b y)
  choose raw hbd hcorr using hex
  let base := fun (s : Aut n × poly t) (m : V h × Bool) (y : Y) => bs m.2 * raw s.1 m.1 y s.2
  let p := fun (s : Aut n × poly t) (m : V h × Bool) (y : Y) =>
    listVal (A s.1) (fun z => truth z y) (D y) m.1 (base s m y)
  have hb (s m y) : |base s m y| ≤ 1 := by dsimp [base]; rw [abs_mul,abs_bs,one_mul]; exact hbd _ _ _ _
  refine ⟨p,fun s m y => listVal_bound _ _ _ _ _ (hb s m y),?_⟩
  intro x y
  have col (z : V n) (hz : z≠x) : (2:ℚ)^h*(∑ e, if A e z=A e x then (1:ℚ) else 0) ≤ Fintype.card (Aut n) :=
    hash_collision R hn z x hz
  have avg := gain_average A (fun z => w z y) x ((2:ℚ)^h) (by positivity) (hw x y).1 (hw x y).2 (mass y) col
  let N := (Fintype.card (poly t):ℚ)
  have signBit (q : poly t) (z : V t) : bs (toField.symm (q.val z)) = signR q z := by
    rcases eitherF (q.val z) with he | he <;> norm_num [signR,he,bs,toField]
  have per (e : Aut n) : (∑ q : poly t, bs (truth x y)*base (e,q) (msgH R (e,q) x) y) =
      N*(gain (bucketMass (A e) (fun z => w z y) (A e x)) * w x y) := by
    change (∑ q : poly t, bs (truth x y) * (bs (toField.symm (q.val (K e x))) * raw e (A e x) y q)) = _
    simp_rw [signBit]
    rw [← Finset.mul_sum,hcorr,en]
    dsimp only [a]
    rw [get]
    change bs (truth x y) * (N * (_ * (bs (truth x y) * w x y))) = _
    linear_combination (N*gain (bucketMass (A e) (fun z => w z y) (A e x))*w x y)*bs_sq (truth x y)
  have lo : w x y * ((Fintype.card (Aut n):ℚ)*N) ≤ ∑ e, ∑ q : poly t, bs (truth x y)*base (e,q) (msgH R (e,q) x) y := by
    simp_rw [per]
    rw [← Finset.mul_sum,← Finset.sum_mul]
    calc _ = N*((Fintype.card (Aut n):ℚ)*w x y) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right avg (hw x y).1) (Nat.cast_nonneg _)
  have result := list_total A (fun z => truth z y) x (D y) ((2:ℚ)^h) (w x y) (by positivity)
    (fun e q => base (e,q) (msgH R (e,q) x) y) (fun e q => hb _ _ _) lo col
  rw [Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type]
  exact result

def msgDecode {h : ℕ} (m : Fin (h+1) → Bool) : V h × Bool := (fun j => toField (m j.succ),m 0)

theorem synth_message {n h t : ℕ} (R : V n ≃ₗ[F] V h × V t) (s : Aut n × poly t) :
    ∃ (C : Circuit) (tap : Fin (h+1) → ℕ),
      (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v<n+i.val) ∧
      (∀ G ∈ C.gates, GOk G) ∧ costG C.gates ≤ t/2 ∧
      (∀ j, tap j < n+C.gates.length) ∧ ∀ x, msgDecode (sendT C tap x) = msgH R s x := by
  obtain ⟨c,l,Q,hq⟩ := s.2.property
  let E := (s.1.trans R).toLinearMap
  let L : Fin h → (V n →ₗ[F] F) := fun j => (LinearMap.proj j).comp ((LinearMap.fst F (V h) (V t)).comp E)
  let K := (LinearMap.snd F (V h) (V t)).comp E
  obtain ⟨C,tap,hb,ho,hc,ht,haddr,hquad⟩ := compile_message L K c l Q
  refine ⟨C,tap,hb,ho,hc,ht,?_⟩
  intro x
  apply Prod.ext
  · funext j
    change toField (sendT C tap x j.succ) = _
    rw [haddr,Equiv.apply_symm_apply]; rfl
  · change sendT C tap x 0 = toField.symm (s.2.val _)
    rw [hquad,hq]; rfl

end PEqualNP.Outside.L_lib_1026_aux.Upper.HashCore

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

def mixSign (b : Bool) : ℚ := if b then 1 else -1

theorem mixSign_negParity (b : Bool) :
    mixSign b = -(if b then (-1 : ℚ) else 1) := by
  cases b <;> norm_num [mixSign]

def mixLegal (n : ℕ) (C : Circuit) : Prop :=
  (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n + i.val) ∧
  (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))

noncomputable def mixCost (C : Circuit) : ℕ :=
  C.gates.countP (fun h => @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2)
    (Classical.propDecidable _))

def ScoreProto {X : Type} (flat : X → List Bool) (truth : X → X → Bool)
    (n k g : ℕ) (ν : X → X → ℚ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (_ : Nonempty S) (C : S → Circuit)
    (tap : S → Fin k → ℕ) (read : S → (Fin k → Bool) → X → ℚ),
    (∀ s, mixLegal n (C s) ∧ mixCost (C s) ≤ g ∧ ∀ j, tap s j < n+(C s).gates.length) ∧
    (∀ s t y, |read s t y| ≤ 1) ∧
    ∀ x y, ν x y ≤ 𝔼 s, mixSign (truth x y) * read s
      (fun j => ((C s).wires (flat x)).getD (tap s j) false) y

private theorem mix_expect_prod {A B : Type*} [Fintype A] [Fintype B] (f : A × B → ℚ) :
    (𝔼 p, f p) = 𝔼 a, 𝔼 b, f (a,b) := by
  simpa only [Finset.univ_product_univ] using Finset.expect_product Finset.univ Finset.univ f

private theorem mix_expect_equiv {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (f : A → ℚ) :
    (𝔼 a, f a) = 𝔼 b, f (e.symm b) := by
  apply Finset.expect_equiv e <;> simp

private theorem mix_coin (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (D : ℕ) (_ : 0 < D) (f : Fin D → Bool), ∀ a b : ℚ,
      (𝔼 k, (if f k then a else b)) = p*a+(1-p)*b := by
  let n := p.num.toNat
  let D := p.den
  have hd : 0 < D := p.den_pos
  have hd' : (0 : ℚ) < D := by positivity
  have hn : (n : ℚ) / D = p := by
    have h : 0 ≤ p.num := Rat.num_nonneg.mpr hp
    have he : (n : ℤ) = p.num := Int.toNat_of_nonneg h
    rw [← p.num_div_den]
    exact congrArg (· / (D : ℚ)) (by exact_mod_cast he : (n : ℚ) = (p.num : ℚ))
  have hle : n ≤ D := by
    exact_mod_cast (div_le_one hd').mp (hn.trans_le hp1)
  let f (k : Fin D) := decide (k.val < n)
  have hc : (Finset.univ.filter (fun k : Fin D => k.val < n)).card = n := by
    rcases hle.eq_or_lt with h|h
    · simp [h]
    · let a : Fin D := ⟨n,h⟩
      have he : (Finset.univ.filter (fun k : Fin D => k.val < n)) = Finset.Iio a := by
        ext; simp [a, Fin.lt_def]
      rw [he, Fin.card_Iio]
  refine ⟨D, hd, f, ?_⟩
  intro a b
  apply mul_left_cancel₀ hd'.ne'
  conv_lhs => lhs; rw [← Fintype.card_fin D]
  rw [Fintype.card_mul_expect]
  have hh := Finset.univ.card_filter_add_card_filter_not (fun k : Fin D => k.val < n)
  simp only [hc, Finset.card_univ, Fintype.card_fin] at hh
  have hh' : (Finset.univ.filter fun k : Fin D => ¬k.val < n).card = D-n := by omega
  simp only [f, decide_eq_true_eq, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, hc, hh', Nat.cast_sub hle]
  rw [← hn]
  field_simp

theorem scoreProto_mix {X : Type} {flat : X → List Bool} {truth : X → X → Bool}
    {n k g : ℕ} {ν μ : X → X → ℚ} (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (h₁ : ScoreProto flat truth n k g ν) (h₂ : ScoreProto flat truth n k g μ) :
    ScoreProto flat truth n k g (fun x y => p*ν x y + (1-p)*μ x y) := by
  classical
  obtain ⟨S,_,_,C,t,f,hC,hf,h⟩ := h₁
  obtain ⟨T,_,_,E,u,v,hE,hv,h'⟩ := h₂
  obtain ⟨D,hd,coin,hcoin⟩ := mix_coin p hp hp1
  let _ : Nonempty (Fin D) := ⟨⟨0,hd⟩⟩
  let Z := Fin D × (S × T)
  let c (z : Z) := if coin z.1 then C z.2.1 else E z.2.2
  let w (z : Z) := if coin z.1 then t z.2.1 else u z.2.2
  let a (z : Z) := if coin z.1 then f z.2.1 else v z.2.2
  refine ⟨Z, inferInstance, inferInstance, c,w,a,?_,?_,?_⟩
  · rintro ⟨i,s,b⟩
    cases hb : coin i
    · simpa only [c,w,hb,Bool.false_eq_true,ite_false] using hE b
    · simpa only [c,w,hb,ite_true] using hC s
  · rintro ⟨i,s,b⟩ m y
    cases hb : coin i
    · simpa only [a,hb,Bool.false_eq_true,ite_false] using hv b m y
    · simpa only [a,hb,ite_true] using hf s m y
  intro x y
  let F (s : S) := mixSign (truth x y) * f s (fun j => ((C s).wires (flat x)).getD (t s j) false) y
  let V (b : T) := mixSign (truth x y) * v b (fun j => ((E b).wires (flat x)).getD (u b j) false) y
  calc
    _ ≤ p*(𝔼 s, F s) + (1-p)*(𝔼 b, V b) :=
      (add_le_add (mul_le_mul_of_nonneg_left (h x y) hp)
        (mul_le_mul_of_nonneg_left (h' x y) (sub_nonneg.mpr hp1)))
    _ = 𝔼 i, (if coin i then (𝔼 s, F s) else (𝔼 b, V b)) := (hcoin _ _).symm
    _ = _ := by
      rw [mix_expect_prod]
      apply Finset.expect_congr rfl
      intro i _
      rw [mix_expect_prod]
      cases hb : coin i <;> simp [c,w,a,hb,F,V]

theorem scoreProto_expand {X : Type} {flat : X → List Bool} {truth : X → X → Bool}
    {n k k' g g' : ℕ} {ν ν' : X → X → ℚ} (h : ScoreProto flat truth n k g ν)
    (hn : 0 < n) (hk : k ≤ k') (hg : g ≤ g') (hν : ∀ x y, ν' x y ≤ ν x y) :
    ScoreProto flat truth n k' g' ν' := by
  classical
  obtain ⟨S,_,_,C,t,f,hC,hf,h⟩ := h
  let t' (s : S) (j : Fin k') := if H : j.val < k then t s ⟨j.val,H⟩ else 0
  let f' (s : S) (b : Fin k' → Bool) := f s (fun i => b (Fin.castLE hk i))
  refine ⟨S,inferInstance,inferInstance,C,t',f',?_,fun s b y => hf s _ y,?_⟩
  · intro s
    refine ⟨(hC s).1,(hC s).2.1.trans hg,?_⟩
    intro j
    dsimp only [t']
    split
    · exact (hC s).2.2 _
    · omega
  intro x y
  simpa only [f',t',Fin.castLE,Fin.is_lt,dite_eq_left] using (hν x y).trans (h x y)

private theorem mix_round {U : Type} [Fintype U] (g : U → ℚ) (hg : ∀ u, |g u| ≤ 1) :
    ∃ (T : Type) (_ : Fintype T) (_ : Nonempty T) (out : T → U → Bool),
      ∀ u, (𝔼 t, mixSign (out t u)) = g u := by
  classical
  have h (u : U) := abs_le.mp (hg u)
  have hc (u : U) := mix_coin ((1+g u)/2) (by linarith [(h u).1]) (by linarith [(h u).2])
  choose D hd f hf using hc
  let A := fun u => Fin (D u)
  let _ (u : U) : Nonempty (A u) := ⟨⟨0,hd u⟩⟩
  refine ⟨∀ u, A u, inferInstance, inferInstance, fun t u => f u (t u), ?_⟩
  intro u
  rw [mix_expect_equiv (Equiv.piSplitAt u A), mix_expect_prod]
  simp only [Equiv.piSplitAt_symm_apply, dite_eq_left, Finset.expect_const Finset.univ_nonempty]
  change (𝔼 k, (if f u k then (1 : ℚ) else -1)) = _
  rw [hf]
  ring

theorem scoreProto_compile {X : Type} [Fintype X] {flat : X → List Bool}
    {truth : X → X → Bool} {n k g : ℕ} {ν : X → X → ℚ}
    (h : ScoreProto flat truth n k g ν) {β : ℚ} (hb : ∀ x y, β ≤ ν x y) :
    ∃ (z : ℕ) (C : Fin z → Circuit) (tap : Fin z → Fin k → ℕ)
      (read : Fin z → (Fin k → Bool) → X → Bool), 0 < z ∧
      (∀ s, mixLegal n (C s) ∧ mixCost (C s) ≤ g ∧ ∀ j, tap s j < n+(C s).gates.length) ∧
      ∀ x y, (1+β)*(z : ℚ) ≤ 2*(((Finset.univ : Finset (Fin z)).filter (fun s =>
        read s (fun j => ((C s).wires (flat x)).getD (tap s j) false) y = truth x y)).card : ℚ) := by
  classical
  obtain ⟨S,_,_,C,t,f,hC,hf,h⟩ := h
  obtain ⟨T,_,_,out,hout⟩ := mix_round
    (fun u : S × (Fin k → Bool) × X => f u.1 u.2.1 u.2.2) (fun u => hf _ _ _)
  let e := Fintype.equivFin (S × T)
  let z := Fintype.card (S × T)
  let F (i : Fin z) (x : X) := fun j => ((C (e.symm i).1).wires (flat x)).getD (t (e.symm i).1 j) false
  let G (i : Fin z) (m : Fin k → Bool) (y : X) := out (e.symm i).2 ((e.symm i).1,m,y)
  refine ⟨z,fun i => C (e.symm i).1,fun i => t (e.symm i).1,G,Fintype.card_pos,fun i => hC _,?_⟩
  intro x y
  have he : (𝔼 i : Fin z, mixSign (truth x y) * mixSign (G i (F i x) y)) =
      𝔼 s, mixSign (truth x y) * f s (fun j => ((C s).wires (flat x)).getD (t s j) false) y := by
    rw [mix_expect_equiv e.symm, mix_expect_prod]
    simp only [Equiv.symm_symm,F,G,Equiv.symm_apply_apply,← Finset.mul_expect,hout]
  have ha := ((hb x y).trans (h x y)).trans_eq he.symm
  have hh (i : Fin z) : mixSign (truth x y) * mixSign (G i (F i x) y) =
      2*(if G i (F i x) y = truth x y then (1 : ℚ) else 0) - 1 := by
    cases truth x y <;> cases G i (F i x) y <;> norm_num [mixSign]
  have hpos : 0 ≤ (z : ℚ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left ha hpos
  conv at hbound => rhs; lhs; rw [← Fintype.card_fin z]
  rw [Fintype.card_mul_expect] at hbound
  simp only [hh,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_boole,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hbound
  change (1+β)*(z : ℚ) ≤ 2*(((Finset.univ : Finset (Fin z)).filter
    (fun i => G i (F i x) y = truth x y)).card : ℚ)
  linarith

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators Classical
open HashCore

theorem hashProto {X : Type} [Fintype X] [DecidableEq X] {n h : ℕ}
    (e : X ≃ (Fin n → Bool)) (hh : h ≤ n)
    (truth : X → X → Bool) (w : X → X → ℚ) (D : X → Finset X)
    (hw : ∀ x y, 0 ≤ w x y) (hm : ∀ y, 16*(∑ x, (w x y)^2) ≤ (2:ℚ)^h) :
    ScoreProto (fun x => List.ofFn (e x)) truth n (h+1) ((n-h)/2)
      (fun x y => (if x∈D y then 1 else 3/4*min (w x y) (1/2)) - 2*(D y).card/(2:ℚ)^h) := by
  classical
  let t := n-h
  have hn : n=h+t := by dsimp [t]; omega
  let R : V n ≃ₗ[F] V h × V t := LinearEquiv.ofFinrankEq _ _ (by simp [V,Module.finrank_prod,hn])
  let E := (boolEquiv n).trans e.symm
  let tru := fun (v : V n) (y : X) => truth (E v) y
  let wt := fun (v : V n) (y : X) => min (w (E v) y) (1/2:ℚ)
  let des := fun y => (D y).map E.symm.toEmbedding
  have hcwt (v y) : 0 ≤ wt v y ∧ wt v y ≤ 1/2 :=
    ⟨le_min (hw _ _) (by norm_num),min_le_right _ _⟩
  have mass (y) : 16*(∑ v : V n, (wt v y)^2) ≤ (2:ℚ)^h := by
    have hb (v : V n) : (wt v y)^2 ≤ (w (E v) y)^2 :=
      pow_le_pow_left₀ (hcwt v y).1 (min_le_left _ _) 2
    calc _ ≤ 16*∑ v : V n, (w (E v) y)^2 :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hb v)) (by norm_num)
         _ = 16*∑ x : X, (w x y)^2 := by rw [Equiv.sum_comp E (fun x => (w x y)^2)]
         _ ≤ _ := hm y
  let _ : Finite (Aut n) := Finite.of_injective (fun f : Aut n => (f : V n → V n))
    (fun f g he => LinearEquiv.ext (fun v => congrFun he v))
  let _ : Fintype (Aut n) := Fintype.ofFinite _
  let _ : Nonempty (Aut n) := ⟨LinearEquiv.refl F (V n)⟩
  obtain ⟨p,hp,hsoft⟩ := soft_protocol R hn tru wt des hcwt mass
  choose C tap hback hops hcost htaps hmsg using synth_message R
  refine ⟨Aut n × poly t,inferInstance,inferInstance,C,tap,
    fun s m y => -p s (msgDecode m) y,
    fun s => ⟨⟨hback s,hops s⟩,hcost s,htaps s⟩,fun s m y => by simpa using hp s (msgDecode m) y,?_⟩
  intro x y
  let v := E.symm x
  have ex : E v=x := E.apply_symm_apply _
  have he : v∈des y ↔ x∈D y := by simp [des,v]
  have hcard : (des y).card=(D y).card := Finset.card_map _
  have hbits : bitsN n v = List.ofFn (e x) := by
    apply congrArg List.ofFn
    exact (boolEquiv n).apply_symm_apply (e x)
  have hdecode (s : Aut n × poly t) :
      msgDecode (fun j => ((C s).wires (List.ofFn (e x))).getD (tap s j) false) = msgH R s v := by
    rw [← hbits]; exact hmsg s v
  have sgn (b : Bool) : mixSign b = -bs b := by cases b <;> rfl
  simp only [hdecode,sgn,neg_mul_neg]
  rw [Fintype.expect_eq_sum_div_card]
  apply (le_div_iff₀ (by exact_mod_cast Fintype.card_pos : (0:ℚ)<Fintype.card (Aut n × poly t))).2
  have hs := hsoft v y
  simp only [he,hcard,wt,tru,ex] at hs
  apply le_trans _ hs
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sub_le_sub_right
  split
  · rfl
  · linarith [le_min (hw x y) (by norm_num : (0:ℚ) ≤ 1/2)]

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators

theorem calExp (d : ℕ) : d + 1 ≤ 2^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    omega

theorem calParams (W : ℚ) (K r : ℕ) (L₀ : ℚ) :
    ∃ B d₀ : ℕ, 0 < B ∧ B ≤ d₀ ∧
      2 * (K : ℚ) ≤ (2:ℚ)^(B-1) ∧
      32 * W^2 * (2*(r:ℚ)^2+1) ≤ (2:ℚ)^(B-1) ∧
      ∀ d, d₀ ≤ d → 0 < d ∧ L₀ ≤ (2:ℚ)^d := by
  let t := ⌈max (2 * (K:ℚ)) (32 * W^2 * (2*(r:ℚ)^2+1))⌉₊
  have ht : max (2 * (K:ℚ)) (32 * W^2 * (2*(r:ℚ)^2+1)) ≤ t := Nat.le_ceil _
  have ht' : (t:ℚ) ≤ (2:ℚ)^t := by exact_mod_cast (show t ≤ 2^t by have := calExp t; omega)
  refine ⟨t+1, max (t+1) ⌈L₀⌉₊, by omega, le_max_left _ _, ?_, ?_, ?_⟩
  · simpa using (le_max_left _ _).trans (ht.trans ht')
  · simpa using (le_max_right _ _).trans (ht.trans ht')
  · intro d hd
    have hd₁ := (le_max_left _ _).trans hd
    have hd₂ := (le_max_right _ _).trans hd
    refine ⟨by omega, (Nat.le_ceil L₀).trans ?_⟩
    exact_mod_cast (show ⌈L₀⌉₊ ≤ 2^d by have := calExp d; omega)

theorem calDimensions {a r B d : ℕ} (ha : 3 ≤ a) (hr : 0 < r) (hB : 0 < B)
    (hBd : B ≤ d) :
    let k := 2^d - 1
    let n := a*(r*k)
    let b := r*d-B
    let h := n-b-1
    0 < k ∧ 0 < n ∧ b ≤ n ∧ h ≤ n ∧ h+1 = n-b ∧ n-r*d ≤ h+1 ∧
      (n-h)/2 ≤ 2*r*2^d ∧
      (2:ℚ)^h * ((2:ℚ)^d)^r = (2:ℚ)^n * (2:ℚ)^(B-1) := by
  dsimp only
  have hde := calExp d
  have hk : d ≤ 2^d-1 := by omega
  have hk' : 0 < 2^d-1 := by omega
  have hb := Nat.mul_le_mul_left r hk
  have hm : 0 < r*(2^d-1) := Nat.mul_pos hr hk'
  have hn' : r*(2^d-1) < a*(r*(2^d-1)) :=
    (Nat.lt_mul_iff_one_lt_left hm).2 (by omega)
  have hBr : B ≤ r*d := hBd.trans (Nat.le_mul_of_pos_left _ hr)
  have he : a*(r*(2^d-1))-(r*d-B)-1+d*r = a*(r*(2^d-1)) + (B-1) := by
    rw [Nat.mul_comm d r]
    omega
  have he' : r*(2^d-1) ≤ r*2^d := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have he'' : r*2^d ≤ 2*r*2^d :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨hk', by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · omega
  · rw [← pow_mul, ← pow_add, ← pow_add, he]

theorem calBounds {X : Type} [Fintype X] {r B d n h K : ℕ} {W δ : ℚ}
    (hd : 0 < d)
    (hc : (Fintype.card X : ℚ) = (2:ℚ)^n)
    (hH : (2:ℚ)^h * ((2:ℚ)^d)^r = (2:ℚ)^n * (2:ℚ)^(B-1))
    (hK : 2 * (K:ℚ) ≤ (2:ℚ)^(B-1))
    (hW : 32 * W^2 * (2*(r:ℚ)^2+1) ≤ (2:ℚ)^(B-1))
    (hrW : W = 0 ∨ r = 1)
    (dev : X → ℚ)
    (ht : (((Finset.univ.filter fun x => δ < dev x).card : ℕ):ℚ) ≤
      K * (Fintype.card X : ℚ) / ((2:ℚ)^d)^(r+1))
    (hs : ∑ x, (dev x)^2 ≤ (r:ℚ)^2*(Fintype.card X : ℚ)/((2:ℚ)^d-1)) :
    2 * (((Finset.univ.filter fun x => δ < dev x).card : ℕ):ℚ) / (2:ℚ)^h ≤
      1 / (2:ℚ)^d ∧
      16*(∑ x, (W*(dev x+1/(2:ℚ)^d))^2) ≤ (2:ℚ)^h := by
  let L : ℚ := 2^d
  let N : ℚ := 2^n
  let H : ℚ := 2^h
  have hL2 : 2 ≤ L := by
    change (2:ℚ) ≤ 2^d
    exact_mod_cast (show 2 ≤ 2^d by have := calExp d; omega)
  have hL : 0 < L := by linarith
  have hH₀ : 0 < H := by dsimp [H]; positivity
  have hN₀ : 0 ≤ N := by dsimp [N]; positivity
  change H * L^r = N * _ at hH
  change (Fintype.card X : ℚ) = N at hc
  rw [hc] at ht hs
  change _ ≤ K * N / L^(r+1) at ht
  change _ ≤ (r:ℚ)^2 * N / (L-1) at hs
  constructor
  · change _ / H ≤ 1 / L
    apply (le_div_iff₀ hL).2
    rw [div_mul_eq_mul_div, div_le_one hH₀]
    apply (le_of_mul_le_mul_right _ (pow_pos hL r))
    rw [hH]
    have ht' := (le_div_iff₀ (pow_pos hL (r+1))).1 ht
    rw [pow_succ] at ht'
    calc
      _ = 2*(_ * (L^r*L)) := by ring
      _ ≤ 2*((K:ℚ)*N) := by linarith
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hK hN₀]
  · rcases hrW with rfl | rfl
    · simp
    change 16*(∑ x, (W * (dev x + 1/L))^2) ≤ H
    simp only [pow_one] at hH
    have hle : ∑ x, (dev x+1/L)^2 ≤
        2*(∑ x, (dev x)^2) + 2*N*(1/L)^2 := by
      calc
        _ ≤ ∑ x, (2*(dev x)^2 + 2*(1/L)^2) :=
          Finset.sum_le_sum fun x _ => by nlinarith [sq_nonneg (dev x-1/L)]
        _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, hc]; ring
    have hσ : (∑ x, (dev x)^2) * L ≤ 2 * (1:ℚ)^2 * N := by
      have hs' := (le_div_iff₀ (by linarith : 0 < L-1)).1 hs
      have hn : 0 ≤ ∑ x, (dev x)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      norm_num at hs' ⊢
      nlinarith [mul_nonneg hn (show 0 ≤ L-2 by linarith)]
    have hσ' : (1/L)^2*L ≤ 1 := by
      field_simp
      nlinarith [mul_nonneg hL.le (show 0 ≤ L-1 by linarith)]
    have hsum : (∑ x, (dev x+1/L)^2)*L ≤ 2*(2*(1:ℚ)^2+1)*N := by
      calc
        _ ≤ (2*(∑ x, (dev x)^2) + 2*N*(1/L)^2)*L := mul_le_mul_of_nonneg_right hle hL.le
        _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hσ' hN₀]
    apply (le_of_mul_le_mul_right _ hL)
    rw [hH]
    simp_rw [mul_pow, ← Finset.mul_sum]
    calc
      _ = 16*W^2*((∑ x, (dev x+1/L)^2)*L) := by ring
      _ ≤ 16*W^2*(2*(2*(1:ℚ)^2+1)*N) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by
        norm_num at hW
        nlinarith [mul_le_mul_of_nonneg_left hW hN₀]

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

theorem em_params {A β C E η : ℚ} (hA : 0 < A) (hA1 : A ≤ 1)
    (hβ : β ≤ A/(1+A)) (hC : 0 ≤ C) (hE : 0 ≤ E) (hη : 0 < η) :
    ∃ W δ L₀ : ℚ, 0 ≤ W ∧ 0 < δ ∧ δ ≤ η ∧ 0 < L₀ ∧
      (β < A/(1+A) → W = 0) ∧ ∀ L : ℚ, L₀ ≤ L →
        ∃ p : ℚ, 0 ≤ p ∧ p ≤ 1 ∧ ∀ d b h : ℚ, 0 ≤ d → -(E/L) ≤ b →
          (d ≤ δ → A-C*d-E/L ≤ b) →
          (if δ < d then 1 else 3/4*min (W*(d+1/L)) (1/2)) - 1/L ≤ h →
          β ≤ (1-p)*b+p*h := by
  let P := A/(1+A)
  let K := C+2*E+4
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hP1 : P < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hkey : (1-P)*A = P := by dsimp [P]; field_simp; ring
  have hchoices : ∃ W δ : ℚ, 0 ≤ W ∧ 0 < δ ∧ δ ≤ η ∧ (β < P → W = 0) ∧
      ∀ d e : ℚ, 0 ≤ d → 0 ≤ e → d ≤ δ → e ≤ δ →
        K*(d+e) ≤ P-β + P*(3/4*min (W*(d+e)) (1/2)) := by
    by_cases hlt : β < P
    · let t := (P-β)/(2*K)
      have ht : 0 < t := div_pos (sub_pos.mpr hlt) (by positivity)
      refine ⟨0,min η t,le_rfl,lt_min hη ht,min_le_left _ _,fun _ => rfl,?_⟩
      intro d e hd he hd₁ he₁
      have ht₁ : d ≤ t := hd₁.trans (min_le_right _ _)
      have ht₂ : e ≤ t := he₁.trans (min_le_right _ _)
      have H₁ := (le_div_iff₀ (show 0 < 2*K by positivity)).1 ht₁
      have H₂ := (le_div_iff₀ (show 0 < 2*K by positivity)).1 ht₂
      norm_num
      linarith
    · let W := 2*K/P
      have hW : 0 < W := div_pos (by positivity) hP
      have hWP : W*P = 2*K := div_mul_cancel₀ _ hP.ne'
      let t := 1/(4*W)
      have ht : 0 < t := by dsimp [t]; positivity
      refine ⟨W,min η t,hW.le,lt_min hη ht,min_le_left _ _,fun h => (hlt h).elim,?_⟩
      intro d e hd he hd₁ he₁
      have ht₁ : d ≤ t := hd₁.trans (min_le_right _ _)
      have ht₂ : e ≤ t := he₁.trans (min_le_right _ _)
      have H₁ := (le_div_iff₀ (show 0 < 4*W by positivity)).1 ht₁
      have H₂ := (le_div_iff₀ (show 0 < 4*W by positivity)).1 ht₂
      rw [min_eq_left (show W*(d+e) ≤ 1/2 by linarith)]
      change β ≤ P at hβ
      have hscale := congrArg (fun x : ℚ => x*(d+e)) hWP
      nlinarith only [hβ,hscale,mul_nonneg hK.le (add_nonneg hd he)]
  obtain ⟨W,δ,hW,hδ,hδη,hWβ,hw⟩ := hchoices
  let L₀ := max (1/δ) ((E+2)/(1-P))
  have hL₀ : 0 < L₀ := (one_div_pos.mpr hδ).trans_le (le_max_left _ _)
  refine ⟨W,δ,L₀,hW,hδ,hδη,hL₀,hWβ,?_⟩
  intro L hL
  have hLpos := hL₀.trans_le hL
  let e := 1/L
  have he : 0 < e := one_div_pos.mpr hLpos
  have heδ : e ≤ δ := by
    have hu : 1/δ ≤ L := (le_max_left _ _).trans hL
    exact (div_le_iff₀ hLpos).2 (by linarith [(div_le_iff₀ hδ).1 hu])
  let p := P + (E+2)*e
  have hp₀ : P ≤ p := by dsimp [p]; linarith [mul_nonneg (by linarith : 0 ≤ E+2) he.le]
  have hp := hP.le.trans hp₀
  have hp1 : p ≤ 1 := by
    have hu : (E+2)/(1-P) ≤ L := (le_max_right _ _).trans hL
    have h : (E+2)/L ≤ 1-P := (div_le_iff₀ hLpos).2
      (by linarith [(div_le_iff₀ (sub_pos.mpr hP1)).1 hu])
    dsimp [p,e]
    rw [mul_one_div]
    linarith
  refine ⟨p,hp,hp1,?_⟩
  intro d b h hd hb₀ hb hh
  have hEdiv : E/L = E*e := by dsimp [e]; ring
  rw [hEdiv] at hb₀ hb
  change (if δ < d then 1 else 3/4*min (W*(d+e)) (1/2)) - e ≤ h at hh
  have hc : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hpe : p*e ≤ e := mul_le_of_le_one_left he.le hp1
  by_cases hfar : δ < d
  · rw [ite_eq_left hfar] at hh
    have Hb := mul_le_mul_of_nonneg_left hb₀ hc
    have Hh := mul_le_mul_of_nonneg_left hh hp
    have He := mul_nonneg hp (mul_nonneg hE he.le)
    change β ≤ P at hβ
    dsimp only [p] at hp₀ ⊢ Hb Hh He hpe
    nlinarith only [Hb,Hh,He,hpe,he.le,hβ]
  · rw [ite_eq_right hfar] at hh
    have hnear := le_of_not_gt hfar
    let R := 3/4*min (W*(d+e)) (1/2)
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have Hb := mul_le_mul_of_nonneg_left (hb hnear) hc
    have Hh := mul_le_mul_of_nonneg_left hh hp
    have HR := mul_le_mul_of_nonneg_right hp₀ hR
    have Hscale := hw d e hd he.le hnear heδ
    change K*(d+e) ≤ P-β+P*R at Hscale
    change p*(R-e) ≤ p*h at Hh
    have HC := mul_nonneg hp (add_nonneg (mul_nonneg hC hd) (mul_nonneg hE he.le))
    have HA := mul_le_of_le_one_right (mul_nonneg (by linarith : 0 ≤ E+2) he.le) hA1
    have Hloss : C*d+(2*E+3)*e ≤ K*(d+e) := by
      dsimp [K]
      nlinarith only [mul_nonneg hE hd,hd,he.le,mul_nonneg hC he.le]
    dsimp only [p] at Hb Hh HR HC hpe ⊢
    nlinarith only [Hb,Hh,HR,HC,hkey,hpe,Hscale,Hloss,HA]

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators

def corrFlip {a : ℕ} (p : Fin a) (v : Fin a → Bool) : Fin a → Bool :=
  Function.update v p (!(v p))

theorem corrFlip_invol {a : ℕ} (p : Fin a) (v : Fin a → Bool) :
    corrFlip p (corrFlip p v) = v := by
  funext j
  by_cases h : j = p <;> simp [corrFlip, h]

theorem corrFlip_ne {a : ℕ} (p : Fin a) (v : Fin a → Bool) : corrFlip p v ≠ v := by
  intro h
  have h' := congrFun h p
  simp [corrFlip] at h'

def corrSet {a : ℕ} (p : Fin a) (y : Fin a → Bool) : Finset (Fin a → Bool) :=
  {y, corrFlip p y}

theorem corrSet_card {a : ℕ} (p : Fin a) (y : Fin a → Bool) : (corrSet p y).card = 2 := by
  simp [corrSet, Ne.symm (corrFlip_ne p y)]

theorem corrSet_flip {a : ℕ} (p : Fin a) (x y : Fin a → Bool) :
    corrFlip p x ∈ corrSet p y ↔ x ∈ corrSet p y := by
  have h := Function.Involutive.injective (corrFlip_invol p)
  simp only [corrSet, Finset.mem_insert, Finset.mem_singleton, h.eq_iff]
  have h1 : corrFlip p x = y ↔ x = corrFlip p y :=
    ⟨fun e => by rw [← e, corrFlip_invol], fun e => by rw [e, corrFlip_invol]⟩
  rw [h1, or_comm]

section
variable {I S : Type} [Fintype I] {a r : ℕ}
abbrev CorrBlock (I : Type) (a : ℕ) := I → Fin a → Bool

def corrCount (p : Fin a) (x y : CorrBlock I a) : ℕ :=
  (Finset.univ.filter fun i => x i ∈ corrSet p (y i)).card

def corrRaw (p : Fin a) (x y : CorrBlock I a) : ℚ :=
  1 - 2*(corrCount p x y : ℚ)/((Fintype.card I : ℚ) + 1)

def corrDelta (p : Fin a) (x y : CorrBlock I a) : ℚ :=
  (corrCount p x y : ℚ)/(Fintype.card I : ℚ) - (2:ℚ)/Fintype.card (Fin a → Bool)

def corrDev (p : Fin a) (x y : Fin r → CorrBlock I a) : ℚ :=
  ∑ j, |corrDelta p (x j) (y j)|

def corrBias (p : Fin a) (x y : Fin r → CorrBlock I a) : ℚ :=
  ∏ j, |corrRaw p (x j) (y j)|

def corrSpin (x y : CorrBlock I a) : ℚ :=
  ∏ i, if x i = y i then (-1 : ℚ) else 1

def corrReadOne (p : Fin a) (z y : CorrBlock I a) : ℚ :=
  (if corrRaw p z y < 0 then (-1 : ℚ) else 1) * corrSpin z y

def corrRead (p : Fin a) (z y : Fin r → CorrBlock I a) : ℚ :=
  -(∏ j, corrReadOne p (z j) (y j))

def corrTruth (x y : Fin r → CorrBlock I a) : Bool :=
  ((Finset.univ.filter fun ji : Fin r × I => x ji.1 ji.2 = y ji.1 ji.2).card % 2 == 1)

private lemma corrSpin_abs (x y : CorrBlock I a) : |corrSpin x y| = 1 := by
  unfold corrSpin
  rw [Finset.abs_prod]
  simp [apply_ite abs]

theorem corrRead_abs (p : Fin a) (z y : Fin r → CorrBlock I a) : |corrRead p z y| = 1 := by
  simp [corrRead, Finset.abs_prod, corrReadOne, apply_ite abs, corrSpin_abs]

private lemma corrParity (n : ℕ) :
    (-1 : ℚ)^n = (if n % 2 == 1 then (-1:ℚ) else 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [Nat.add_mod, h]

theorem corrTruth_sign (x y : Fin r → CorrBlock I a) :
    (if corrTruth x y then (1:ℚ) else -1) = -(∏ j, corrSpin (x j) (y j)) := by
  rw [show (∏ j, corrSpin (x j) (y j)) =
      ∏ ji : Fin r × I, (if x ji.1 ji.2 = y ji.1 ji.2 then (-1:ℚ) else 1) from
    by rw [Fintype.prod_prod_type]; rfl]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, corrParity]
  unfold corrTruth
  split <;> simp

section
variable [DecidableEq I]

private def corrEdit (p : Fin a) (x : CorrBlock I a) (t : Option I) : CorrBlock I a :=
  fun i => if t = some i then corrFlip p (x i) else x i

private theorem corrEdit_count (p : Fin a) (x y : CorrBlock I a) (t : Option I) :
    corrCount p (corrEdit p x t) y = corrCount p x y := by
  unfold corrCount
  congr 1
  apply Finset.filter_congr
  intro i _
  unfold corrEdit
  split <;> simp [corrSet_flip]

private theorem corrEdit_spin (p : Fin a) (x y : CorrBlock I a) (t : Option I) :
    corrSpin x y * corrSpin (corrEdit p x t) y =
      t.elim 1 (fun i => if x i ∈ corrSet p (y i) then (-1:ℚ) else 1) := by
  unfold corrSpin
  rw [← Finset.prod_mul_distrib]
  have base (u v : Fin a → Bool) :
      (if u = v then (-1:ℚ) else 1) * (if u = v then -1 else 1) = 1 := by
    split <;> norm_num
  cases t with
  | none => simp [corrEdit, base]
  | some k =>
    have hfac (i : I) :
        (if x i = y i then (-1 : ℚ) else 1) *
        (if corrEdit p x (some k) i = y i then -1 else 1) =
        if k = i then (if x i ∈ corrSet p (y i) then -1 else 1) else 1 := by
      by_cases h : k = i
      · subst i
        have hflip : corrFlip p (x k) = y k ↔ x k = corrFlip p (y k) :=
          ⟨fun e => by rw [← e, corrFlip_invol], fun e => by rw [e, corrFlip_invol]⟩
        simp only [corrEdit, ↓reduceIte, corrSet, Finset.mem_insert,
          Finset.mem_singleton, hflip]
        by_cases h1 : x k = y k
        · simp [h1, Ne.symm (corrFlip_ne p (y k))]
        · simp [h1]
      · simp [h, corrEdit, base]
    simp_rw [hfac]
    simp

private lemma corr_edit_avg (p : Fin a) (x y : CorrBlock I a) :
    (𝔼 t : Option I, corrSpin x y * corrSpin (corrEdit p x t) y) = corrRaw p x y := by
  apply mul_left_cancel₀ (show (Fintype.card (Option I) : ℚ) ≠ 0 by positivity)
  rw [Fintype.card_mul_expect, Fintype.sum_option, Fintype.card_option]
  simp only [corrEdit_spin, Option.elim_none, Option.elim_some]
  have h (i : I) :
      (if x i ∈ corrSet p (y i) then (-1:ℚ) else 1) =
      1 - 2*(if x i ∈ corrSet p (y i) then (1:ℚ) else 0) := by split <;> norm_num
  simp_rw [h]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, Finset.sum_boole, Nat.cast_add, Nat.cast_one, corrRaw, corrCount]
  field_simp
  ring

private lemma corrReadOne_avg [Fintype S] (p : Fin a) (x y : CorrBlock I a) (e : S ≃ Option I) :
    (𝔼 s : S, corrSpin x y * corrReadOne p (corrEdit p x (e s)) y) = |corrRaw p x y| := by
  have he : (𝔼 s : S, corrSpin x y * corrSpin (corrEdit p x (e s)) y) =
      𝔼 t : Option I, corrSpin x y * corrSpin (corrEdit p x t) y := by
    apply Finset.expect_equiv e <;> simp
  have hr (s : S) : corrRaw p (corrEdit p x (e s)) y = corrRaw p x y := by
    simp [corrRaw, corrEdit_count]
  simp only [corrReadOne, hr, mul_left_comm (corrSpin x y)]
  rw [← Finset.mul_expect, he, corr_edit_avg]
  split_ifs with h
  · simp [abs_of_neg h]
  · simp [abs_of_nonneg (le_of_not_gt h)]

private lemma corr_prod_avg [Fintype S] (f : Fin r → S → ℚ) :
    (𝔼 s : Fin r → S, ∏ j, f j (s j)) = ∏ j, (𝔼 s : S, f j s) := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.prod_sum]

theorem corrRead_mean [Fintype S] (p : Fin a) (x y : Fin r → CorrBlock I a)
    (z : (Fin r → S) → Fin r → CorrBlock I a) (e : Fin r → S ≃ Option I)
    (hz : ∀ s j i, z s j i = if e j (s j) = some i then corrFlip p (x j i) else x j i) :
    (𝔼 s : Fin r → S, (if corrTruth x y then (1:ℚ) else -1) * corrRead p (z s) y) =
      corrBias p x y := by
  have hz' (s : Fin r → S) (j : Fin r) : z s j = corrEdit p (x j) (e j (s j)) :=
    funext (hz s j)
  simp only [corrTruth_sign, corrRead, neg_mul_neg, ← Finset.prod_mul_distrib, hz',
    corr_prod_avg (fun j s => corrSpin (x j) (y j) * corrReadOne p (corrEdit p (x j) (e j s)) (y j)),
    corrReadOne_avg, corrBias]

end

private lemma corr_product_lower (u d : Fin r → ℚ) {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hu : ∀ j, 0 ≤ u j) (hu' : ∀ j, u j ≤ 1) (hd : ∀ j, 0 ≤ d j)
    (hb : ∀ j, ρ - d j ≤ u j) :
    ρ^r - ∑ j, d j ≤ ∏ j, u j := by
  have h (s : Finset (Fin r)) : ρ^s.card - ∑ j ∈ s, d j ≤ ∏ j ∈ s, u j := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.card_insert_of_notMem hi, pow_succ, Finset.sum_insert hi, Finset.prod_insert hi]
      have hp := Finset.prod_nonneg (s := s) (fun j _ => hu j)
      have hp' := Finset.prod_le_one₀ (s := s) (fun j _ => hu j) (fun j _ => hu' j)
      have hsum := Finset.sum_nonneg (s := s) (fun j _ => hd j)
      nlinarith [mul_nonneg (sub_nonneg.mpr ih) h0,
        mul_nonneg (sub_nonneg.mpr (hb i)) hp, mul_nonneg (hd i) (sub_nonneg.mpr hp'),
        mul_nonneg (sub_nonneg.mpr h1) hsum]
  simpa using h Finset.univ

theorem corrBias_bounds [Nonempty I] (p : Fin a)
    (hq : (4:ℚ) ≤ Fintype.card (Fin a → Bool)) (x y : Fin r → CorrBlock I a) :
    0 ≤ corrBias p x y ∧
    (1 - (4:ℚ)/Fintype.card (Fin a → Bool))^r - 2*corrDev p x y ≤ corrBias p x y := by
  constructor
  · exact Finset.prod_nonneg (fun j _ => abs_nonneg _)
  let L : ℚ := Fintype.card I
  let q : ℚ := Fintype.card (Fin a → Bool)
  have hL : 0 < L := by dsimp [L]; positivity
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hc (j : Fin r) : (corrCount p (x j) (y j) : ℚ) ≤ L := by
    unfold L corrCount
    rw [← Finset.card_univ]
    exact_mod_cast Finset.card_filter_le Finset.univ (fun i => x j i ∈ corrSet p (y j i))
  unfold corrDev corrBias
  rw [Finset.mul_sum]
  apply corr_product_lower _ _
  · exact sub_nonneg.mpr ((div_le_one hq0).2 hq)
  · exact sub_le_self _ (by positivity)
  · exact fun _ => abs_nonneg _
  · intro j
    unfold corrRaw
    change |1 - 2*(corrCount p (x j) (y j) : ℚ)/(L+1)| ≤ 1
    rw [abs_le]
    constructor
    · have := (div_le_iff₀ (show 0 < L+1 by linarith)).2
        (show 2*(corrCount p (x j) (y j) : ℚ) ≤ 2*(L+1) by linarith [hc j])
      linarith
    · exact sub_le_self _ (by positivity)
  · exact fun _ => by positivity
  · intro j
    change 1-4/q-2*|(corrCount p (x j) (y j) : ℚ)/L-2/q| ≤
      |1-2*(corrCount p (x j) (y j) : ℚ)/(L+1)|
    apply le_trans _ (le_abs_self _)
    have h := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*(corrCount p (x j) (y j) : ℚ))
      hL (show L ≤ L+1 by linarith)
    have hd := le_abs_self ((corrCount p (x j) (y j) : ℚ)/L-2/q)
    rw [mul_div_assoc, mul_div_assoc] at h
    rw [mul_div_assoc, show (4:ℚ)/q = 2*(2/q) by ring]
    linarith

end
end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

theorem dyadicBudget {r G c d₀ : ℕ} (P : ℕ → ℕ → ℕ → Prop)
    (hzero : ∀ m g, 0 < m → P m g 0)
    (hlarge : ∀ d, d₀ ≤ d → ∀ m g, r*(2^d-1) ≤ m → G*r*2^d ≤ g →
      ∃ b, P m g b ∧ r*d ≤ b+c) :
    ∃ K : ℕ, 0 < K ∧ ∀ m g, 0 < m →
      ∃ b, P m g b ∧ (1+min m g)^r ≤ K*2^b := by
  let A := (G+1)*(r+1)
  have ha : 0 < A := Nat.mul_pos (by omega) (by omega)
  have har : r ≤ A := by dsimp [A]; nlinarith
  have hag : G*r ≤ A := by dsimp [A]; nlinarith
  let K := (A*2^d₀)^r + (A*2)^r * 2^c
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro m g hm
  let T := min m g
  by_cases h : A*2^d₀ ≤ T
  · have hpow : 2^d₀ ≤ T/A :=
      (Nat.le_div_iff_mul_le ha).2 (by simpa only [mul_comm] using h)
    have hne : T/A ≠ 0 := ne_of_gt ((pow_pos (by decide : 0 < (2:ℕ)) d₀).trans_le hpow)
    let d := (T/A).log2
    have hd : d₀ ≤ d := (Nat.le_log2 hne).2 hpow
    have hsize : A*2^d ≤ T := by
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le ha).1 (Nat.log2_self_le hne)
    have hub : 1+T ≤ (A*2)*2^d := by
      have hlt : T/A < 2^(d+1) := Nat.lt_log2_self
      have ht := (Nat.div_lt_iff_lt_mul ha).1 hlt
      rw [pow_succ] at ht
      rw [show (A*2)*2^d = 2^d*2*A by ring]
      omega
    obtain ⟨b, hb, hs⟩ := hlarge d hd m g
      ((Nat.mul_le_mul har (Nat.sub_le _ _)).trans (hsize.trans (min_le_left _ _)))
      ((Nat.mul_le_mul_right _ hag).trans (hsize.trans (min_le_right _ _)))
    refine ⟨b, hb, ?_⟩
    calc
      (1+T)^r ≤ ((A*2)*2^d)^r := Nat.pow_le_pow_left hub _
      _ = (A*2)^r*2^(r*d) := by rw [mul_pow, ← pow_mul, Nat.mul_comm d r]
      _ ≤ (A*2)^r*2^(b+c) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hs)
      _ = ((A*2)^r*2^c)*2^b := by rw [pow_add]; ring
      _ ≤ K*2^b := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  · refine ⟨0, hzero m g hm, ?_⟩
    rw [pow_zero, mul_one]
    exact (Nat.pow_le_pow_left (show 1+T ≤ A*2^d₀ by omega) _).trans (Nat.le_add_right _ _)

open PEqualNP.CircuitLowerBounds

def padGate (k : ℕ) (v : Gate) : Gate := ⟨v.op, v.inputs.map (k+·)⟩

def padCircuit (k : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (padGate k), k+C.output⟩

theorem pad_wires (p x : List Bool) (C : Circuit) :
    (padCircuit p.length C).wires (p++x) = p++C.wires x := by
  cases C with | mk gs o =>
    dsimp [padCircuit, Circuit.wires]
    induction gs generalizing x with
    | nil => rfl
    | cons u gs ih =>
      simp only [List.map_cons, List.foldl_cons, padGate, List.map_map]
      have hf : ((fun i => (p++x).getD i false) ∘ (p.length+·)) = fun i => x.getD i false := by
        funext i
        change (p++x).getD (p.length+i) false = _
        rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      rw [hf, List.append_assoc, ih]

abbrev PadWord (a m : ℕ) := Fin m → Fin a → Bool

def padFlat {a m : ℕ} (x : PadWord a m) : List Bool :=
  (List.ofFn x).flatMap List.ofFn

def padTruth {a m : ℕ} (x y : PadWord a m) : Bool :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1

def padLegal (n : ℕ) (C : Circuit) : Prop :=
  (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
    (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
      (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))

noncomputable def padCost (C : Circuit) : ℕ :=
  C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))

def padWorks (a m g : ℕ) (β : ℚ) (b : ℕ) : Prop :=
  let n := a*m
  b ≤ n ∧ ∃ (z : Nat) (C : Fin z → Circuit) (tap : Fin z → Fin (n-b) → Nat)
    (read : Fin z → (Fin (n-b) → Bool) → PadWord a m → Bool),
    0 < z ∧ (∀ s, padLegal n (C s) ∧ padCost (C s) ≤ g ∧
      ∀ j, tap s j < n+(C s).gates.length) ∧
    ∀ x y : PadWord a m,
      let hits := ((Finset.univ : Finset (Fin z)).filter (fun s =>
        read s (fun j => ((C s).wires (padFlat x)).getD (tap s j) false) y = padTruth x y)).card
      (1+β)*(z : ℚ) ≤ 2*(hits : ℚ)

theorem pad_preserves_legal {n : ℕ} (k : ℕ) {C : Circuit} (hC : padLegal n C) :
    padLegal (k+n) (padCircuit k C) := by
  constructor
  · intro i v hv
    let i₀ : Fin C.gates.length := ⟨i.val, by simpa [padCircuit] using i.isLt⟩
    have hi : (padCircuit k C).gates.get i = padGate k (C.gates.get i₀) := by
      change (C.gates.map _)[i.val] = padGate k (C.gates[i.val]'i₀.isLt)
      rw [List.getElem_map]
    rw [hi] at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    have := hC.1 i₀ u hu
    dsimp [i₀] at this
    omega
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    simpa only [padGate, List.length_map] using hC.2 u hu

theorem pad_preserves_cost (k : ℕ) (C : Circuit) : padCost (padCircuit k C) = padCost C := by
  classical
  unfold padCost padCircuit
  rw [List.countP_map]
  congr 1
  funext h
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, decide_eq_true_eq, padGate, List.length_map]

def padPre {a t m : ℕ} (x : PadWord a (t+m)) : PadWord a t := fun i => x (i.castAdd m)
def padSuf {a t m : ℕ} (x : PadWord a (t+m)) : PadWord a m := fun i => x (i.natAdd t)

theorem padFlat_length {a m : ℕ} (x : PadWord a m) : (padFlat x).length = a*m := by
  induction m with
  | zero => simp [padFlat]
  | succ m ih =>
    rw [padFlat, List.ofFn_succ, List.flatMap_cons, List.length_append, List.length_ofFn]
    rw [← padFlat, ih, Nat.mul_succ, Nat.add_comm]

theorem padFlat_split {a t m : ℕ} (x : PadWord a (t+m)) :
    padFlat x = padFlat (padPre x) ++ padFlat (padSuf x) := by
  rw [padFlat, List.ofFn_add, List.flatMap_append]; rfl

def padBit {t a : ℕ} (i : Fin t) (j : Fin a) : Fin (a*t) :=
  ⟨a*i.val+j.val, by
    calc
      a*i.val+j.val < a*i.val+a := Nat.add_lt_add_left j.isLt _
      _ = a*(i.val+1) := (Nat.mul_succ _ _).symm
      _ ≤ _ := Nat.mul_le_mul_left _ i.isLt⟩

theorem padBit_read {a m : ℕ} (x : PadWord a m) (i : Fin m) (j : Fin a) :
    (padFlat x).getD (padBit i j).val false = x i j := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [padFlat, List.ofFn_succ, List.flatMap_cons]
    refine Fin.cases ?_ (fun l => ?_) i
    · rw [show (padBit (0 : Fin (m+1)) j).val = j.val by simp [padBit]]
      rw [List.getD_append _ _ _ _ (by simp)]
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    · rw [List.getD_append_right _ _ _ _ (by simp [padBit, Nat.mul_succ]; omega)]
      rw [List.length_ofFn]
      have hl : (padBit l.succ j).val - a = (padBit l j).val := by
        simp only [padBit, Fin.val_succ, Nat.mul_succ]; omega
      rw [hl]
      exact ih _ _

theorem padTruth_split {a t m : ℕ} (x y : PadWord a (t+m)) :
    padTruth x y = xor (padTruth (padPre x) (padPre y)) (padTruth (padSuf x) (padSuf y)) := by
  let c {l : ℕ} (u v : PadWord a l) := (Finset.univ.filter (fun i => u i = v i)).card
  have hadd : c x y = c (padPre x) (padPre y) + c (padSuf x) (padSuf y) := by
    simp only [c, Finset.card_filter]
    rw [Fin.sum_univ_add]; rfl
  change (c x y % 2 == 1) = xor _ _
  rw [hadd]
  change ((_ + _) % 2 == 1) = xor (c (padPre x) (padPre y) % 2 == 1)
    (c (padSuf x) (padSuf y) % 2 == 1)
  generalize c (padPre x) (padPre y) = u, c (padSuf x) (padSuf y) = v
  have hu : u%2 = 0 ∨ u%2 = 1 := by omega
  have hv : v%2 = 0 ∨ v%2 = 1 := by omega
  rw [Nat.add_mod]
  rcases hu with h|h <;> rcases hv with h'|h' <;> rw [h, h'] <;> decide

theorem pad_extend {a m g g' b : ℕ} {β : ℚ} (t : ℕ)
    (hg : g ≤ g') (h : padWorks a m g β b) : padWorks a (t+m) g' β b := by
  rcases h with ⟨hb, z, C, taps, reads, hz, hC, hwin⟩
  let k := a*t
  let l := a*m
  let n := a*(t+m)
  have hab : l ≤ n := by dsimp [l, n]; rw [Nat.mul_add]; omega
  have hn : n = k+l := Nat.mul_add _ _ _
  have hb' : b ≤ l := hb
  have hq : n-b = k+(l-b) := by omega
  let left : Fin k → Fin (n-b) := fun i => ⟨i.val, by omega⟩
  let right : Fin (l-b) → Fin (n-b) := fun j => ⟨k+j.val, by omega⟩
  let tap' (s : Fin z) (j : Fin (n-b)) :=
    if hj : j.val < k then j.val else k + taps s ⟨j.val-k, by omega⟩
  have tapL (s : Fin z) (i : Fin k) : tap' s (left i) = i.val := by
    simp [tap', left]
  have tapR (s : Fin z) (j : Fin (l-b)) : tap' s (right j) = k+taps s j := by
    simp [tap', right]
  let msg (s : Fin z) (x : PadWord a (t+m)) (i : Fin (n-b)) :=
    ((padCircuit k (C s)).wires (padFlat x)).getD (tap' s i) false
  let pre (u : Fin (n-b) → Bool) : PadWord a t := fun i j => u (left (padBit i j))
  let read' (s : Fin z) (u : Fin (n-b) → Bool) (y : PadWord a (t+m)) :=
    xor (padTruth (pre u) (padPre y)) (reads s (fun j => u (right j)) (padSuf y))
  refine ⟨hb'.trans hab, z, fun s => padCircuit k (C s), tap', read', hz, ?_, ?_⟩
  · intro s
    have ⟨hL, hG, hT⟩ := hC s
    refine ⟨?_, (pad_preserves_cost _ _).le.trans (hG.trans hg), ?_⟩
    · change padLegal n _
      rw [hn]; exact pad_preserves_legal k hL
    · intro j
      change tap' s j < n+(padCircuit k (C s)).gates.length
      simp only [padCircuit, List.length_map]
      dsimp only [tap']
      split
      · omega
      · rename_i hj
        have ht := hT ⟨j.val-k, by omega⟩
        change taps s _ < l+(C s).gates.length at ht
        omega
  · intro x y
    have hw (s : Fin z) :
        (padCircuit k (C s)).wires (padFlat x) =
          padFlat (padPre x) ++ (C s).wires (padFlat (padSuf x)) := by
      rw [padFlat_split]
      simpa only [padFlat_length] using pad_wires (padFlat (padPre x)) (padFlat (padSuf x)) (C s)
    have hx (s : Fin z) : pre (msg s x) = padPre x := by
      funext i j
      change ((padCircuit k (C s)).wires (padFlat x)).getD (tap' s (left (padBit i j))) false = _
      rw [hw s, tapL, List.getD_append _ _ _ _ (by rw [padFlat_length]; exact (padBit i j).isLt)]
      exact padBit_read _ _ _
    have hs (s : Fin z) (j : Fin (l-b)) :
        msg s x (right j) = ((C s).wires (padFlat (padSuf x))).getD (taps s j) false := by
      dsimp only [msg]
      rw [hw s, tapR, List.getD_append_right _ _ _ _ (by rw [padFlat_length]; exact Nat.le_add_right ..),
        padFlat_length, Nat.add_sub_cancel_left]
    have he (s : Fin z) : read' s (msg s x) y = padTruth x y ↔
        reads s (fun j => ((C s).wires (padFlat (padSuf x))).getD (taps s j) false) (padSuf y) =
          padTruth (padSuf x) (padSuf y) := by
      dsimp only [read']
      rw [hx, padTruth_split x y, show (fun j => msg s x (right j)) = _ from funext (hs s)]
      cases padTruth (padPre x) (padPre y) <;> simp <;> rfl
    have hsets :
        (Finset.univ.filter (fun s => read' s (msg s x) y = padTruth x y)) =
        Finset.univ.filter (fun s =>
          reads s (fun j => ((C s).wires (padFlat (padSuf x))).getD (taps s j) false) (padSuf y) =
            padTruth (padSuf x) (padSuf y)) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
    change (1+β)*(z:ℚ) ≤ 2*((Finset.univ.filter (fun s => read' s (msg s x) y = padTruth x y)).card:ℚ)
    rw [hsets]
    exact hwin _ _

theorem pad_zero {a g : ℕ} {β : ℚ} (hβ : β ≤ 1) : padWorks a 0 g β 0 := by
  refine ⟨Nat.zero_le _, 1, fun _ => ⟨[],0⟩, fun _ j => j.val, fun _ _ _ => false, by decide,
    ?_, ?_⟩
  · simp [padLegal, padCost]
  · intro x y
    simp [padTruth]
    linarith

theorem padDyadic {a r G B d₀ : ℕ} {β : ℚ} (hβ : β ≤ 1)
    (h : ∀ d, d₀ ≤ d → padWorks a (r*(2^d-1)) (G*r*2^d) β (r*d-B)) :
    ∃ K : ℕ, 0 < K ∧ ∀ m g, 0 < m →
      ∃ b, padWorks a m g β b ∧ (1+min m g)^r ≤ K*2^b := by
  apply dyadicBudget (r := r) (G := G) (c := B) (d₀ := d₀) (fun m g => padWorks a m g β)
  · intro m g _
    simpa only [Nat.add_zero] using pad_extend m (le_refl g) (pad_zero (a := a) hβ)
  · intro d hd m g hm hg
    have hw := pad_extend (m-r*(2^d-1)) hg (h d hd)
    rw [Nat.sub_add_cancel hm] at hw
    exact ⟨r*d-B, hw, by omega⟩

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open HashCore

theorem circLiteral {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (f : X → ZMod 2)
    (hf : Evaluates input P (fun x => toField.symm (f x))) (t : ZMod 2) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => decide (t = f x)) := by
  rcases eitherF t with ht | ht <;> subst t
  · obtain ⟨D,hd,h⟩ := emit_not size P hf
    have eq : ∀ z : ZMod 2, (!toField.symm z) = decide (0 = z) := by decide
    exact ⟨D,hd,by simpa only [eq] using h⟩
  · have eq : ∀ z : ZMod 2, toField.symm z = decide (1 = z) := by decide
    exact ⟨P,adds_refl P,by simpa only [eq] using hf⟩

theorem circDecode {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (d : ℕ) (P : Plan n) (f : X → Syndrome d)
    (hf : ∀ j, Evaluates input P (fun x => toField.symm (f x j))) :
    ∃ D, adds P D (2 * (2^d - 1)) ∧
      ∀ i : Syndrome d, Evaluates input D (fun x => decide (i = f x)) := by
  classical
  induction d generalizing P with
  | zero =>
    obtain ⟨D,hd,h⟩ := emit_const size P true
    refine ⟨D,by simpa using hd,?_⟩
    intro i
    have eq (x : X) : decide (i = f x) = true := decide_eq_true (Subsingleton.elim _ _)
    simpa only [eq] using h
  | succ d ih =>
    obtain ⟨D,hD,htail⟩ := ih P (fun x j => f x j.succ) (fun j => hf j.succ)
    let vals := fun (i : Syndrome (d+1)) (x : X) => decide (i = f x)
    obtain ⟨E,hE,hout⟩ := build_values size D 1 Finset.univ vals (by
      intro i _ A k hA
      obtain ⟨B,hB,bl⟩ := circLiteral size A (fun x => f x 0)
        (evaluates_ext size (hf 0) (adds_trans hD hA)) (i 0)
      have tl := evaluates_ext size (htail (fun j => i j.succ)) (adds_trans hA hB)
      obtain ⟨C,hC,hc⟩ := emit_and size B bl tl
      have e (x : X) : (decide (i 0 = f x 0) && decide ((fun j : Fin d => i j.succ) =
          fun j : Fin d => f x j.succ)) = vals i x := by
        apply Bool.eq_iff_iff.mpr
        simp only [vals, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro ⟨hz,hs⟩
          exact funext (Fin.cases hz (fun j => congrFun hs j))
        · rintro rfl
          exact ⟨rfl,rfl⟩
      exact ⟨C,by simpa using adds_trans hB hC,by simpa only [funext e] using hc⟩)
    refine ⟨E,adds_mono (adds_trans hD hE) ?_,fun i => hout i (Finset.mem_univ _)⟩
    simp only [Finset.card_univ, cardSyndrome, mul_one, pow_succ]
    have : 0 < 2^d := by positivity
    omega

theorem circSyndBit {X : Type} {n d : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (w : X → Pos d → Bool)
    (h : ∀ i, Evaluates input P (fun x => w x i)) (s : Syndrome d) (j : Fin d) :
    ∃ D, adds P D 0 ∧ Evaluates input D
      (fun x => toField.symm ((hsyn (w x) + s) j)) := by
  classical
  let T := Finset.univ.filter (fun i : Pos d => i.val j = 1)
  obtain ⟨A,hA,eA⟩ := emit_sum size P T (fun i x => w x i) (fun i _ => h i)
  obtain ⟨B,hB,eB⟩ := emit_const size A (toField.symm (s j))
  obtain ⟨C,hC,ec⟩ := emit_xor size B (evaluates_ext size eA hB) eB
  have sumEq (x : X) : (∑ i ∈ T, toField (w x i)) = hsyn (w x) j := by
    simp only [T, Finset.sum_filter, hsyn]
    apply Finset.sum_congr rfl
    intro i _
    rcases eitherF (i.val j) with hi | hi <;> simp [hi, toField, hbit]
  have he (x : X) : Bool.xor (toField.symm (∑ i ∈ T, toField (w x i)))
      (toField.symm (s j)) = toField.symm ((hsyn (w x) + s) j) := by
    apply toField.injective
    simp only [field_xor, Equiv.apply_symm_apply, sumEq, Pi.add_apply]
  exact ⟨C,by simpa using adds_trans (adds_trans hA hB) hC,by simpa only [funext he] using ec⟩

theorem compileWord {X : Type} {n d a : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (w : X → Pos d → Fin a → Bool)
    (h : ∀ i j, Evaluates input P (fun x => w x i j)) (p : Fin a) (s : Syndrome d) :
    ∃ D, adds P D (2*2^d) ∧ ∀ i j, Evaluates input D (fun x => wordProject p s (w x) i j) := by
  classical
  let f := fun (x : X) => hsyn (fun i => w x i p) + s
  obtain ⟨A,hA,eA⟩ := build_values size P 0 Finset.univ
    (fun j x => toField.symm (f x j)) (by
      intro j _ D k hD
      exact circSyndBit size D (fun x i => w x i p) (fun i => evaluates_ext size (h i p) hD) s j)
  obtain ⟨B,hB,eqB⟩ := circDecode size d A f (fun j => eA j (Finset.mem_univ _))
  obtain ⟨C,hC,eC⟩ := build_values size B 0 Finset.univ
    (fun (i : Pos d) x => project s (fun u => w x u p) i) (by
      intro i _ D k hD
      exact emit_xor size D (evaluates_ext size (h i p) (adds_trans (adds_trans hA hB) hD))
        (evaluates_ext size (eqB i.val) hD))
  have hTot := adds_trans (adds_trans hA hB) hC
  refine ⟨C,adds_mono hTot (by simp),?_⟩
  intro i j
  by_cases hj : j = p
  · simpa only [wordProject, ite_eq_left hj] using eC i (Finset.mem_univ _)
  · simpa only [wordProject, ite_eq_right hj] using evaluates_ext size (h i j) hTot

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open PEqualNP.CircuitLowerBounds

noncomputable def blockIndex (r d : ℕ) : Fin r × Pos d ≃ Fin (r*(2^d-1)) :=
  (Fintype.equivFin _).trans (finCongr (by simp))

noncomputable def blockEquiv (r d a : ℕ) :
    (Fin r → Pos d → Fin a → Bool) ≃ (Fin (r*(2^d-1)) → Fin a → Bool) :=
  (Equiv.curry _ _ _).symm.trans ((blockIndex r d).arrowCongr (Equiv.refl _))

def bbIndex (m a : ℕ) : Fin m × Fin a ≃ Fin (a*m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m a))

def bbBits (m a : ℕ) : (Fin m → Fin a → Bool) ≃ (Fin (a*m) → Bool) :=
  (Equiv.curry _ _ _).symm.trans ((bbIndex m a).arrowCongr (Equiv.refl _))

noncomputable def blockFlatEquiv (r d a : ℕ) :
    (Fin r → Pos d → Fin a → Bool) ≃ (Fin (a*(r*(2^d-1))) → Bool) :=
  (blockEquiv r d a).trans (bbBits _ _)

noncomputable def bbFlat (r d a : ℕ) (x : Fin r → Pos d → Fin a → Bool) : List Bool :=
  List.ofFn (blockFlatEquiv r d a x)

theorem bbBits_flat {m a : ℕ} (x : Fin m → Fin a → Bool) :
    List.ofFn (bbBits m a x) = (List.ofFn x).flatMap List.ofFn := by
  rw [List.ofFn_congr (Nat.mul_comm a m), List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  change Function.uncurry x ((bbIndex m a).symm _) = x i j
  have h := (bbIndex m a).symm_apply_apply (i,j)
  convert congrArg (Function.uncurry x) h using 2
  congr 1
  apply Fin.ext
  change _ = j.val + a * i.val
  dsimp
  ac_rfl
  rfl

theorem block_flat (r d a : ℕ) (x : Fin r → Pos d → Fin a → Bool) :
    List.ofFn (blockFlatEquiv r d a x) = (List.ofFn (blockEquiv r d a x)).flatMap List.ofFn :=
  bbBits_flat (blockEquiv r d a x)

theorem block_matches (r d a : ℕ) (x y : Fin r → Pos d → Fin a → Bool) :
    (Finset.univ.filter (fun i => blockEquiv r d a x i = blockEquiv r d a y i)).card =
    (Finset.univ.filter (fun i : Fin r × Pos d => x i.1 i.2 = y i.1 i.2)).card := by
  apply Finset.card_equiv (blockIndex r d).symm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

open HashCore in
theorem blockBuild {r d a k : ℕ} (p : Fin a) (s : Fin r → Syndrome d)
    (hk : a*(r*(2^d-1))-r*d ≤ k) (hn : 0 < a*(r*(2^d-1))) :
    ∃ (C : Circuit) (tap : Fin k → ℕ) (recover : (Fin k → Bool) → Fin r → Pos d → Fin a → Bool),
      mixLegal (a*(r*(2^d-1))) C ∧ mixCost C ≤ r*(2*2^d) ∧
      (∀ j, tap j < a*(r*(2^d-1))+C.gates.length) ∧
      ∀ x, recover (fun j => (C.wires (bbFlat r d a x)).getD (tap j) false) =
        fun j => wordProject p (s j) (x j) := by
  classical
  let m := r*(2^d-1)
  let n := a*m
  let X := Fin r → Pos d → Fin a → Bool
  let input := bbFlat r d a
  have size (x : X) : (input x).length = n := List.length_ofFn
  let P := emptyPlan n
  have raw (t : Fin r) (i : Pos d) (b : Fin a) :
      Evaluates input P (fun x : X => x t i b) := by
    let e := blockIndex r d
    let u := bbIndex m a ((e (t,i)),b)
    refine ⟨u.val, by change u.val < n + 0; exact u.isLt, ?_⟩
    intro x
    change (List.ofFn (blockFlatEquiv r d a x)).getD u.val false = _
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact u.isLt), List.getElem_ofFn]
    change Function.uncurry (blockEquiv r d a x) ((bbIndex m a).symm ((bbIndex m a) _)) = _
    rw [Equiv.symm_apply_apply]
    change Function.uncurry x (e.symm (e (t,i))) b = _
    rw [Equiv.symm_apply_apply]
    rfl
  let f (t : Fin r) (b : keepBit (d := d) p) (x : X) := wordKeep p (wordProject p (s t) (x t)) b
  obtain ⟨D,hD,ev⟩ := build_many size P (2*2^d) Finset.univ f (by
    intro t _ D v prev
    obtain ⟨E,he,hf⟩ := compileWord size D (fun x : X => x t)
      (fun i b => evaluates_ext size (raw t i b) prev) p (s t)
    exact ⟨E,he,fun b => hf b.val.1 b.val.2⟩)
  let C : Circuit := ⟨D.gates,0⟩
  let J := Fin r × keepBit (d := d) p
  have len : Fintype.card J = a*m-r*d := by
    change Fintype.card (Fin r × keepBit (d := d) p) = _
    rw [Fintype.card_prod, Fintype.card_fin, cardKeepBit, cardPos, Nat.mul_sub]
    dsimp [m]
    ac_rfl
  let e := Fintype.equivFin J
  let t : J → Fin k := fun j => (e j).castLE (len.le.trans hk)
  have ti : Function.Injective t := fun _ _ h => e.injective (Fin.ext (congrArg (fun z : Fin k => z.val) h))
  have allEv (j : J) := ev j.1 (Finset.mem_univ _) j.2
  choose addr addrLt addrVal using allEv
  let tap : Fin k → ℕ := fun z => if h : ∃ j, t j = z then addr h.choose else 0
  have tap_t (j : J) : tap (t j) = addr j := by
    dsimp [tap]
    have h : ∃ l, t l = t j := ⟨j,rfl⟩
    rw [dite_eq_left h]
    congr 1
    exact ti h.choose_spec
  refine ⟨C,tap,fun bits i => wordDecode p (s i) (fun b => bits (t (i,b))), D.property, ?_, ?_, ?_⟩
  · change paidCount D.gates ≤ _
    simpa only [P, emptyPlan, Plan.gates, paidCount, List.countP_nil, Nat.zero_add, Finset.card_univ,
      Fintype.card_fin] using hD.2
  · intro j
    dsimp [tap]
    split
    · apply addrLt
    · exact lt_of_lt_of_le hn (Nat.le_add_right _ _)
  · intro x
    funext i
    change wordDecode p (s i) (fun b => (C.wires (bbFlat r d a x)).getD (tap (t (i,b))) false) =
      wordProject p (s i) (x i)
    rw [← wordDecode_spec p (s i) (x i)]
    apply congrArg (wordDecode p (s i))
    funext b
    rw [tap_t]
    exact addrVal (i,b) x

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory

def fracDev {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (S : I → Finset A) (x : I → A) (c : ℕ) : ℚ :=
  ((Finset.univ.filter fun i => x i ∈ S i).card : ℚ) / Fintype.card I -
    (c : ℚ) / Fintype.card A

def blockDev {r : ℕ} {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (S : Fin r → I → Finset A) (x : Fin r → I → A) (c : ℕ) : ℚ :=
  ∑ j, |fracDev (S j) (x j) c|

theorem blockDev_nonneg {r : ℕ} {I A : Type*} [Fintype I] [Fintype A] [DecidableEq A]
    (S : Fin r → I → Finset A) (x : Fin r → I → A) (c : ℕ) : 0 ≤ blockDev S x c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem dev_sum_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}
    (hi : iIndepFun X μ) (hm : ∀ i, Measurable (X i))
    (hb : ∀ i ω, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i, (X i ω - ∫ z, X i z ∂μ)|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * (Fintype.card ι : ℝ) * (1 / 4))) := by
  let Y := fun i ω => X i ω - ∫ z, X i z ∂μ
  have hY : iIndepFun Y μ := hi.comp
    (fun i t => t - ∫ z, X i z ∂μ) (fun i => measurable_id.sub_const _)
  have hYn : iIndepFun (fun i ω => -Y i ω) μ :=
    hY.comp (fun _ t => -t) (fun _ => measurable_id.neg)
  have hG (i : ι) : HasSubgaussianMGF (Y i) (1 / 4) μ := by
    have he : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
      apply NNReal.coe_injective
      norm_num
    rw [← he]
    exact hasSubgaussianMGF_of_mem_Icc (hm i).aemeasurable (ae_of_all _ (hb i))
  have hp := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hY
    (s := Finset.univ) (fun i _ => hG i) hε
  have hn := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYn
    (s := Finset.univ) (fun i _ => (hG i).neg) hε
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    ← mul_assoc, Finset.sum_neg_distrib] at hp hn
  change μ.real {ω | ε ≤ |∑ i, Y i ω|} ≤ _
  have hevent : {ω | ε ≤ |∑ i, Y i ω|} =
      {ω | ε ≤ ∑ i, Y i ω} ∪ {ω | ε ≤ -(∑ i, Y i ω)} := by
    ext ω
    simp [abs_eq_max_neg, le_max_iff]
  rw [hevent]
  linarith [measureReal_union_le (μ := μ) {ω | ε ≤ ∑ i, Y i ω}
    {ω | ε ≤ -(∑ i, Y i ω)}]

private theorem fracDev_exp {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    [Nonempty I] [Nonempty A] (S : I → Finset A) (c : ℕ) (hc : ∀ i, (S i).card = c)
    (t : ℚ) (ht : 0 ≤ t) :
    ((Finset.univ.filter fun x => t ≤ |fracDev S x c|).card : ℝ) /
      Fintype.card (I → A) ≤ 2 * Real.exp (-2 * Fintype.card I * (t : ℝ)^2) := by
  classical
  let : MeasurableSpace A := ⊤
  let : DiscreteMeasurableSpace A := ⟨fun _ => trivial⟩
  let μ : Measure A := uniformOn Set.univ
  let ν : Measure (I → A) := uniformOn Set.univ
  have hν : ν = Measure.pi (fun _ : I => μ) := by
    simpa [ν, μ] using (uniformOn_pi (f := fun _ : I => (Set.univ : Set A)))
  let X := fun (i : I) (x : I → A) => if x i ∈ S i then (1 : ℝ) else 0
  let f := fun (i : I) (a : A) => if a ∈ S i then (1 : ℝ) else 0
  have hf (i : I) : Measurable (f i) := Measurable.of_discrete
  have hX (i : I) : Measurable (X i) := (hf i).comp (measurable_pi_apply i)
  have hind : iIndepFun X ν := by
    rw [hν]
    exact iIndepFun_pi (fun i => (hf i).aemeasurable)
  have hmean (i : I) : (∫ x, X i x ∂ν) = (c : ℝ) / Fintype.card A := by
    rw [hν]
    change (∫ x, f i (x i) ∂Measure.pi (fun _ : I => μ)) = _
    have hpres := measurePreserving_eval (fun _ : I => μ) i
    have hmap := integral_map (μ := Measure.pi (fun _ : I => μ))
      hpres.measurable.aemeasurable (hf i).aestronglyMeasurable
    rw [hpres.map_eq] at hmap
    rw [← hmap]
    have hfi : f i = ((S i : Set A)).indicator (1 : A → ℝ) := by
      funext a
      simp [f, Set.indicator_apply]
    rw [hfi, integral_indicator_one (S i).measurableSet]
    have he := congrArg ENNReal.toReal (uniformOn_apply_finset
      (s := (Finset.univ : Finset A)) (t := S i))
    simpa [μ, measureReal_def, ENNReal.toReal_div, hc] using he
  let m := Fintype.card I
  have hm : 0 < (m : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have htail := dev_sum_tail ν hind hX
    (fun i x => by by_cases h : x i ∈ S i <;> simp [X,h]) ((m : ℝ) * t)
    (mul_nonneg hm.le (by exact_mod_cast ht))
  simp only [hmean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at htail
  let B := Finset.univ.filter fun x => t ≤ |fracDev S x c|
  have hs : (B : Set (I → A)) = {x | (m : ℝ) * t ≤
      |(∑ i, X i x) - Fintype.card I * ((c : ℝ) / Fintype.card A)|} := by
    ext x
    simp only [B, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    rw [← Rat.cast_le (K := ℝ)]
    push_cast [fracDev]
    simp only [X, Finset.sum_boole]
    rw [div_sub' hm.ne', abs_div, abs_of_pos hm, le_div_iff₀ hm, mul_comm (t : ℝ)]
  rw [← hs] at htail
  have he := congrArg ENNReal.toReal (uniformOn_apply_finset
    (s := (Finset.univ : Finset (I → A))) (t := B))
  have hb : ν.real (B : Set (I → A)) = (B.card : ℝ) / Fintype.card (I → A) := by
    simpa [ν, measureReal_def, ENNReal.toReal_div] using he
  rw [hb] at htail
  have harg : -((m : ℝ) * t)^2 / (2 * m * (1 / 4)) = -2 * m * (t : ℝ)^2 := by
    field_simp
    ring
  simpa only [show Fintype.card I = m from rfl, harg] using htail

private theorem dev_exp_poly (s : ℕ) (t : ℚ) (ht : 0 < t) :
    ∃ K : ℕ, ∀ m : ℕ, 0 < m →
      2 * Real.exp (-2*m*(t : ℝ)^2) ≤ K / (1+(m : ℝ))^s := by
  obtain ⟨K,hK⟩ := exists_nat_ge (2 * (s.factorial : ℝ) / (t : ℝ)^(2*s))
  refine ⟨K,fun m hm => ?_⟩
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let z : ℝ := 2*m*(t : ℝ)^2
  have hz := Real.pow_div_factorial_le_exp (x := z) (by dsimp [z]; positivity) s
  have hz' : z^s ≤ Real.exp z * s.factorial :=
    (div_le_iff₀ (by positivity)).mp hz
  have hp : (1+(m : ℝ))^s * (t : ℝ)^(2*s) ≤ Real.exp z * s.factorial := by
    rw [pow_mul, ← mul_pow]
    exact le_trans (pow_le_pow_left₀ (by positivity) (by dsimp [z]; nlinarith [sq_nonneg (t : ℝ), mul_nonneg (sub_nonneg.mpr hm') (sq_nonneg (t : ℝ))]) s) hz'
  rw [show -2*(m : ℝ)*(t : ℝ)^2 = -z by dsimp [z]; ring, Real.exp_neg]
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = 2*(1+(m : ℝ))^s / Real.exp z := by ring
    _ ≤ 2 * (s.factorial : ℝ) / (t : ℝ)^(2*s) := by
      apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).2
      linarith
    _ ≤ _ := hK

theorem fracDev_tail (s : ℕ) (t : ℚ) (ht : 0 < t) :
    ∃ K : ℕ, ∀ {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
      [Nonempty I] [Nonempty A] (S : I → Finset A) (c : ℕ), (∀ i, (S i).card = c) →
        ((Finset.univ.filter fun x => t ≤ |fracDev S x c|).card : ℚ) ≤
          K * (Fintype.card (I → A) : ℚ) / (1+Fintype.card I)^s := by
  obtain ⟨K,hK⟩ := dev_exp_poly s t ht
  refine ⟨K,fun {I A} _ _ _ _ _ _ S c hc => ?_⟩
  have h := (fracDev_exp S c hc t ht.le).trans (hK _ Fintype.card_pos)
  rw [div_le_iff₀ (by positivity)] at h
  rw [div_mul_eq_mul_div] at h
  apply (Rat.cast_le (K := ℝ)).mp
  push_cast
  exact h

private theorem dev_split {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (i : I) (f : (I → A) → ℚ) :
    (𝔼 x, f x) = 𝔼 a, 𝔼 t, f ((Equiv.piSplitAt i (fun _ => A)).symm (a,t)) := by
  let e := Equiv.piSplitAt i (fun _ => A)
  calc
    _ = 𝔼 p, f (e.symm p) := by apply Finset.expect_equiv e <;> simp
    _ = _ := by
      simpa only [Finset.univ_product_univ] using
        Finset.expect_product Finset.univ Finset.univ (fun p => f (e.symm p))

private theorem dev_eval {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (i : I) (f : A → ℚ) : (𝔼 x : I → A, f (x i)) = 𝔼 a, f a := by
  rw [dev_split i]
  simp [Equiv.piSplitAt]

private theorem dev_var {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    (s : Finset I) (v : I → A → ℚ) (hm : ∀ i, (𝔼 a, v i a) = 0)
    (hb : ∀ i a, |v i a| ≤ 1) :
    (𝔼 x : I → A, (∑ i ∈ s, v i (x i))^2) ≤ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    let e := Equiv.piSplitAt i (fun _ => A)
    have hj (a : A) (t : {j : I // j ≠ i} → A) :
        (∑ j ∈ s, v j (e.symm (a,t) j)) =
        ∑ j ∈ s.attach, v j.1 (t ⟨j.1, fun he => hi (he ▸ j.2)⟩) := by
      rw [← Finset.sum_attach s]
      apply Finset.sum_congr rfl
      intro j _
      have hji : j.1 ≠ i := fun he => hi (he ▸ j.2)
      simp [e, Equiv.piSplitAt, hji]
    have hz : (𝔼 x : I → A, v i (x i) * (∑ j ∈ s, v j (x j))) = 0 := by
      rw [dev_split i]
      change (𝔼 a, 𝔼 t, v i (e.symm (a,t) i) * (∑ j ∈ s, v j (e.symm (a,t) j))) = _
      simp_rw [show ∀ (a : A) t, e.symm (a,t) i = a by simp [e, Equiv.piSplitAt],
        hj, ← Finset.mul_expect, ← Finset.expect_mul, hm, zero_mul]
    have h2 : (𝔼 x : I → A, v i (x i)^2) ≤ 1 := by
      rw [dev_eval i (fun a => v i a^2), ← Finset.expect_const (Finset.univ_nonempty (α := A)) (1 : ℚ)]
      exact Finset.expect_le_expect fun a _ => by
        simpa only [sq_abs] using pow_le_one₀ (abs_nonneg _) (hb i a) (n := 2)
    simp only [Finset.sum_insert hi, show ∀ a b : ℚ, (a+b)^2 = a^2+2*(a*b)+b^2 by intros; ring,
      Finset.expect_add_distrib, ← Finset.mul_expect, hz, Finset.card_insert_of_notMem hi,
      Nat.cast_add, Nat.cast_one]
    linarith

theorem fracDev_sq_avg_le {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    [Nonempty I] [Nonempty A] (S : I → Finset A) (c : ℕ) (hc : ∀ i, (S i).card = c) :
    (𝔼 x, (fracDev S x c)^2) ≤ 1 / Fintype.card I := by
  let m := Fintype.card I
  let q := Fintype.card A
  have hm : 0 < (m : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  have hq : 0 < (q : ℚ) := Nat.cast_pos.mpr Fintype.card_pos
  let v (i : I) (a : A) : ℚ := (if a ∈ S i then 1 else 0) - c/q
  have h0 (i : I) : (𝔼 a, v i a) = 0 := by
    simp [v, Finset.expect_sub_distrib, Fintype.expect_eq_sum_div_card, hc, q]
  have hb (i : I) (a : A) : |v i a| ≤ 1 := by
    have h : c ≤ q := (hc i) ▸ Finset.card_le_univ (S i)
    have h' : (c : ℚ) / q ≤ 1 := (div_le_one hq).mpr (by exact_mod_cast h)
    have h'' : (0 : ℚ) ≤ c/q := by positivity
    rw [abs_le]
    by_cases ha : a ∈ S i <;> simp only [v, ha, ite_true, ite_false] <;> constructor <;> linarith
  have hd (x : I → A) : fracDev S x c = (∑ j, v j (x j)) / m := by
    simp only [fracDev,v,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,Finset.sum_boole]
    change _/(m : ℚ) - (c : ℚ)/q = (_ - (m : ℚ)*(c/q))/m
    field_simp
  simp_rw [hd, div_pow, ← Finset.expect_div]
  calc
    _ ≤ (m : ℚ) / (m : ℚ)^2 := by
      gcongr
      simpa [m] using dev_var Finset.univ v h0 hb
    _ = _ := by change _ = 1/(m : ℚ); field_simp

theorem blockDev_sq_sum_le {r : ℕ} {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] [DecidableEq A] [Nonempty I] [Nonempty A]
    (S : Fin r → I → Finset A) (c : ℕ) (hc : ∀ j i, (S j i).card = c) :
    (∑ x, (blockDev S x c)^2) ≤
      (r : ℚ)^2 * Fintype.card (Fin r → I → A) / Fintype.card I := by
  have h (x : Fin r → I → A) : (blockDev S x c)^2 ≤
      r * ∑ j, (fracDev (S j) (x j) c)^2 := by
    simpa [blockDev] using (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => |fracDev (S j) (x j) c|))
  have h' : (𝔼 x, (blockDev S x c)^2) ≤ (r : ℚ)^2 / Fintype.card I := by
    calc
      _ ≤ 𝔼 x : Fin r → I → A, (r : ℚ)* ∑ j, (fracDev (S j) (x j) c)^2 :=
        Finset.expect_le_expect fun x _ => h x
      _ = (r : ℚ) * ∑ j, 𝔼 a, (fracDev (S j) a c)^2 := by
        rw [← Finset.mul_expect, Finset.expect_sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun j _ => dev_eval j (fun a => (fracDev (S j) a c)^2)
      _ ≤ (r : ℚ) * ∑ _ : Fin r, 1 / (Fintype.card I : ℚ) := by
        gcongr with j
        exact fracDev_sq_avg_le (S j) c (hc j)
      _ = _ := by simp [nsmul_eq_mul]; ring
  rw [← Fintype.card_mul_expect]
  calc
    _ ≤ (Fintype.card (Fin r → I → A) : ℚ) * ((r : ℚ)^2 / Fintype.card I) := by gcongr
    _ = _ := by ring

private theorem dev_ind {X : Type*} [Fintype X] (P : X → Prop) [DecidablePred P] :
    (𝔼 x, if P x then (1 : ℚ) else 0) =
      ((Finset.univ.filter P).card : ℚ) / Fintype.card X := by
  simp [Fintype.expect_eq_sum_div_card]

theorem blockDev_tail (r s : ℕ) (hr : 0 < r) (t : ℚ) (ht : 0 < t) :
    ∃ K : ℕ, ∀ {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
      [Nonempty I] [Nonempty A] (S : Fin r → I → Finset A) (c : ℕ), (∀ j i, (S j i).card = c) →
        ((Finset.univ.filter fun x => t ≤ blockDev S x c).card : ℚ) ≤
          K * (Fintype.card (Fin r → I → A) : ℚ) / (1+Fintype.card I)^s := by
  let : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  obtain ⟨K,hK⟩ := fracDev_tail s (t/r) (by positivity)
  refine ⟨r*K,fun {I A} _ _ _ _ _ _ S c hc => ?_⟩
  let W := I → A
  let B := fun (j : Fin r) (x : W) => t/r ≤ |fracDev (S j) x c|
  have hj (j : Fin r) : (𝔼 x : W, if B j x then (1 : ℚ) else 0) ≤ K / (1+Fintype.card I)^s := by
    rw [dev_ind, div_le_iff₀ (by positivity), div_mul_eq_mul_div]
    exact hK (S j) c (hc j)
  have hl (x : Fin r → W) : (if t ≤ blockDev S x c then (1 : ℚ) else 0) ≤
      ∑ j, if B j (x j) then 1 else 0 := by
    split_ifs with h
    · obtain ⟨j,hj⟩ : ∃ j, B j (x j) := by
        by_contra! ha
        have hab (j : Fin r) (_ : j ∈ Finset.univ) : |fracDev (S j) (x j) c| < t/r :=
          lt_of_not_ge (ha j)
        have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty hab
        have hr' : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, mul_div_cancel₀ _ hr'] at this
        exact (not_lt.mpr h) this
      exact le_trans (by simp [hj]) (Finset.single_le_sum (f := fun j => if B j (x j) then (1 : ℚ) else 0)
        (fun _ _ => by split <;> norm_num) (Finset.mem_univ j))
    · positivity
  have h : (𝔼 x, if t ≤ blockDev S x c then (1 : ℚ) else 0) ≤ (r : ℚ)*K/(1+Fintype.card I)^s := by
    calc
      _ ≤ _ := Finset.expect_le_expect fun x _ => hl x
      _ = ∑ j, 𝔼 a, if B j a then (1 : ℚ) else 0 := by
        rw [Finset.expect_sum_comm]
        exact Finset.sum_congr rfl fun j _ => dev_eval j (fun a => if B j a then (1 : ℚ) else 0)
      _ ≤ ∑ _ : Fin r, (K : ℚ)/(1+Fintype.card I)^s := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp [nsmul_eq_mul]; ring
  rw [dev_ind, div_le_iff₀ (by positivity), div_mul_eq_mul_div] at h
  simpa [Nat.cast_mul] using h

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

def nearSets {r a : ℕ} {I : Type} (p : Fin a) (y : Fin r → I → Fin a → Bool)
    (j : Fin r) (i : I) : Finset (Fin a → Bool) := corrSet p (y j i)

theorem radialProto {r d a k g : ℕ} (ha : 3 ≤ a) (p : Fin a)
    (hk : a*(r*(2^d-1))-r*d ≤ k) (hn : 0 < a*(r*(2^d-1))) (hg : r*(2*2^d) ≤ g) :
    ScoreProto (bbFlat r d a) corrTruth (a*(r*(2^d-1))) k g
      (fun x y => max 0 ((1 - 4 / (2^a:ℚ))^r - 2*blockDev (nearSets p y) x 2)) := by
  classical
  have hpos : 0 < Fintype.card (Pos d) := by
    rw [cardPos]
    exact Nat.pos_of_mul_pos_left (Nat.pos_of_mul_pos_left hn)
  let _ : Nonempty (Pos d) := Fintype.card_pos_iff.mp hpos
  choose C tap recover hc hcost ht hrecover using
    fun s : Fin r → Syndrome d => blockBuild p s hk hn
  refine ⟨Fin r → Syndrome d, inferInstance, inferInstance, C, tap,
    fun s m y => corrRead p (recover s m) y, fun s => ⟨hc s, (hcost s).trans hg, ht s⟩,
    fun s m y => (corrRead_abs p (recover s m) y).le, ?_⟩
  intro x y
  have he := corrRead_mean p x y (fun s j => wordProject p (s j) (x j))
    (fun j => syndIndex (fun i => x j i p))
    (fun s j i => wordProject_eq_edit p (s j) (x j) i)
  simp only [hrecover, mixSign, he]
  have hcard : (Fintype.card (Fin a → Bool) : ℚ) = 2^a := by simp
  have h4 : (4:ℚ) ≤ Fintype.card (Fin a → Bool) := by
    rw [hcard]
    calc
      (4:ℚ) ≤ 2^3 := by norm_num
      _ ≤ 2^a := pow_le_pow_right₀ (by norm_num) ha
  obtain ⟨h0,h1⟩ := corrBias_bounds p h4 x y
  rw [hcard] at h1
  exact max_le h0 h1

theorem blockCompile {a r d b g : ℕ} {β : ℚ}
    {ν : (Fin r → Pos d → Fin a → Bool) → (Fin r → Pos d → Fin a → Bool) → ℚ}
    (hb : b ≤ a*(r*(2^d-1)))
    (h : ScoreProto (bbFlat r d a) corrTruth (a*(r*(2^d-1))) (a*(r*(2^d-1))-b) g ν)
    (hβ : ∀ x y, β ≤ ν x y) :
    padWorks a (r*(2^d-1)) g β b := by
  classical
  let e := blockEquiv r d a
  have hf (x) : bbFlat r d a x = padFlat (e x) := block_flat r d a x
  have hp (x y) : corrTruth x y = padTruth (e x) (e y) :=
    congrArg (fun m : ℕ => m % 2 == 1) (block_matches r d a x y).symm
  obtain ⟨z,C,t,v,hz,hC,hh⟩ := scoreProto_compile h hβ
  refine ⟨hb,z,C,t,fun s m y => v s m (e.symm y),hz,hC,?_⟩
  intro x y
  simpa only [hf,hp,Equiv.apply_symm_apply] using hh (e.symm x) (e.symm y)

end PEqualNP.Outside.L_lib_1026_aux.Upper

namespace PEqualNP.Outside.L_lib_1026_aux.Upper

open scoped BigOperators

theorem upper_bound (a r : ℕ) (ha : 3 ≤ a) (hr : 0 < r) (β : ℚ)
    (hb :
      let ρ := 1 - 4 / ((2^a : ℕ) : ℚ)
      let τ := fun j : ℕ => ρ^j / (1+ρ^j)
      β < τ r ∨ (r = 1 ∧ β = τ r)) :
    ∃ K : ℕ, 0 < K ∧ ∀ m g : ℕ, 0 < m →
      ∃ b : ℕ, padWorks a m g β b ∧ (1+min m g)^r ≤ K*2^b := by
  classical
  let ρ := 1 - 4 / (2:ℚ)^a
  let A := ρ^r
  have hb' : β < A/(1+A) ∨ (r=1 ∧ β = A/(1+A)) := by simpa [A,ρ] using hb
  have hq : (8:ℚ) ≤ 2^a :=
    calc
      (8:ℚ) = 2^3 := by norm_num
      _ ≤ 2^a := pow_le_pow_right₀ (by norm_num) ha
  have hρ : 0 < ρ := by
    have : 4/(2:ℚ)^a < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    dsimp [ρ]; linarith
  have hρ' : ρ ≤ 1 := sub_le_self _ (by positivity)
  have hA : 0 < A := pow_pos hρ _
  have hA' : A ≤ 1 := pow_le_one₀ hρ.le hρ'
  have hβ : β ≤ A/(1+A) := hb'.elim le_of_lt (fun v => v.2.le)
  have hβ' : β ≤ 1 := hβ.trans ((div_le_one (by positivity)).mpr (by linarith))
  obtain ⟨W,δ,L₀,hW,hδ,_,_,hWβ,hMix⟩ := em_params hA hA' hβ
    (C := 2) (E := 0) (η := 1) (by norm_num) (by norm_num) (by norm_num)
  have hWr : W=0 ∨ r=1 := hb'.elim (fun v => Or.inl (hWβ v)) (fun v => Or.inr v.1)
  obtain ⟨K,hK⟩ := blockDev_tail r (r+1) hr δ hδ
  obtain ⟨B,d₀,hB,hBd₀,hBK,hBW,hL⟩ := calParams W K r L₀
  apply padDyadic (G := 2) (B := B) (d₀ := d₀) hβ'
  intro d hd
  obtain ⟨hdpos,hLmin⟩ := hL d hd
  obtain ⟨hk,hn,hb₁,hh,hh₁,hh₂,hg,hH⟩ := calDimensions ha hr hB (hBd₀.trans hd)
  let n := a*(r*(2^d-1))
  let b := r*d-B
  let h := n-b-1
  let L : ℚ := 2^d
  have hLpos : 0 < L := by dsimp [L]; positivity
  let X := Fin r → Pos d → Fin a → Bool
  have : Nonempty (Pos d) := Fintype.card_pos_iff.mp (by rwa [cardPos])
  let e : X ≃ (Fin n → Bool) := blockFlatEquiv r d a
  have hc : (Fintype.card X : ℚ) = (2:ℚ)^n := by
    rw [Fintype.card_congr e]
    simp
  let p : Fin a := ⟨0, by omega⟩
  let dev (x y : X) : ℚ := blockDev (nearSets p y) x 2
  have hdev (x y) : 0 ≤ dev x y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let D (y : X) := Finset.univ.filter fun x => δ < dev x y
  let w (x y : X) := W*(dev x y+1/L)
  have hw (x y : X) : 0 ≤ w x y :=
    mul_nonneg hW (add_nonneg (hdev _ _) (one_div_pos.mpr hLpos).le)
  have hS (y : X) (j : Fin r) (i : Pos d) : (nearSets p y j i).card = 2 :=
    corrSet_card p (y j i)
  have hI : (Fintype.card (Pos d) : ℚ) = L-1 := by
    rw [cardPos, Nat.cast_sub (Nat.one_le_two_pow)]
    simp [L]
  have hIL : (1:ℚ)+Fintype.card (Pos d) = L := by rw [hI]; ring
  have hbounds (y : X) : 2*((D y).card:ℚ)/(2:ℚ)^h ≤ 1/L ∧
      16*(∑ x, (w x y)^2) ≤ (2:ℚ)^h := by
    apply calBounds hdpos hc hH hBK hBW hWr (fun x => dev x y)
    · have ht := hK (nearSets p y) 2 (hS y)
      rw [hIL] at ht
      apply le_trans _ ht
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      exact Finset.monotone_filter_right _ (fun _ _ v => le_of_lt v)
    · simpa only [dev, hI] using blockDev_sq_sum_le (nearSets p y) 2 (hS y)
  have hhProto := hashProto e hh corrTruth w D hw (fun y => (hbounds y).2)
  let hreward (x y : X) : ℚ := (if δ < dev x y then 1 else 3/4 * min (w x y) (1/2)) - 1/L
  have hp' : ScoreProto (bbFlat r d a) corrTruth n (n-b) (2*r*2^d) hreward := by
    apply scoreProto_expand hhProto hn hh₁.le hg
    intro x y
    simp only [hreward, D, Finset.mem_filter, Finset.mem_univ, true_and]
    exact sub_le_sub_left (hbounds y).1 _
  have hrg : r*(2*2^d) ≤ 2*r*2^d := by rw [← Nat.mul_assoc, Nat.mul_comm r 2]
  have hrd := radialProto (r := r) (d := d) (k := n-b) ha p (hh₂.trans hh₁.le) hn hrg
  obtain ⟨u,hu,hu₁,huMix⟩ := hMix L hLmin
  apply blockCompile hb₁ (scoreProto_mix u hu hu₁ hp' hrd)
  intro x y
  rw [add_comm]
  apply huMix (dev x y) _ _ (hdev x y)
  · simp
  · intro _
    simp [A,ρ,dev]
  · rfl

end PEqualNP.Outside.L_lib_1026_aux.Upper

theorem PEqualNP.Outside.L_lib_1026 : (∀ (a r : Nat), 3 ≤ a → 0 < r →
  let q := 2^a
  let ρ : ℚ := 1 - 4 / (q : ℚ)
  let τ := fun (j : Nat) => ρ^j / (1+ρ^j)
  ∀ β : ℚ, τ (r+1) < β → (β < τ r ∨ (r = 1 ∧ β = τ r)) →
    ∃ K : Nat, 0 < K ∧ ∀ (m g : Nat), 0 < m →
      let n := a*m
      let W := Fin m → Fin a → Bool
      let Circ := PEqualNP.CircuitLowerBounds.Circuit
      let legal := fun (C : Circ) =>
        (∀ i : Fin C.gates.length, ∀ v ∈ (C.gates.get i).inputs, v < n+i.val) ∧
        (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
          (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
      let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
        ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
      let works := fun (b : Nat) =>
        b ≤ n ∧ ∃ (z : Nat) (C : Fin z → Circ) (tap : Fin z → Fin (n-b) → Nat)
          (read : Fin z → (Fin (n-b) → Bool) → W → Bool),
          0 < z ∧ (∀ s, legal (C s) ∧ cost (C s) ≤ g ∧
            ∀ j, tap s j < n+(C s).gates.length) ∧
          ∀ x y : W,
            let truth := ((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card % 2 == 1
            let hits := ((Finset.univ : Finset (Fin z)).filter (fun s =>
              read s (fun j => ((C s).wires ((List.ofFn x).flatMap (fun v => List.ofFn v))).getD
                (tap s j) false) y = truth)).card
            (1+β)*(z : ℚ) ≤ 2*(hits : ℚ)
      let scale := (1+min m g)^r
      (∀ b : Nat, works b → 2^b ≤ K*scale) ∧
        ∃ b : Nat, works b ∧ scale ≤ K*2^b) := by
  intro a r ha hr q ρ τ β h1 h2
  dsimp only [τ, ρ, q] at h1 h2
  obtain ⟨K1, hK1, hlow⟩ := PEqualNP.Outside.L_lib_1026_aux.Lower.lower_bound a r ha hr β
    (by simpa using h1)
  obtain ⟨K2, hK2, hup⟩ := PEqualNP.Outside.L_lib_1026_aux.Upper.upper_bound a r ha hr β
    (by simpa using h2)
  refine ⟨K1 * K2, Nat.mul_pos hK1 hK2, ?_⟩
  intro m g hm n W Circ legal cost works scale
  refine ⟨fun b hb => ?_, ?_⟩
  · have h := hlow m g hm b hb
    calc 2^b ≤ K1 * (1 + min m g)^r := h
      _ ≤ K1 * K2 * (1 + min m g)^r := by
        rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hK2)
  · obtain ⟨b, hb, hsc⟩ := hup m g hm
    refine ⟨b, hb, ?_⟩
    calc (1 + min m g)^r ≤ K2 * 2^b := hsc
      _ ≤ K1 * K2 * 2^b := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hK1)
