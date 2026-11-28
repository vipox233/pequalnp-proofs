import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_962
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
lemma close_count {q m : ℕ} (hq : 5 ≤ q) (hm : 0 < m) (r R : ℕ) (z x' : Fin m → Fin q)
    (hR : hd z x' ≤ R) (P : Finset (Fin m → Fin q)) :
    ∑ x ∈ P, (if jj z x x' ≤ r - 1 then (1:ℚ) else 0) ≤
      (2 * ((q:ℚ) - 1) * m) ^ (r - 1) * (2 * (q:ℚ) ^ R) := by
  have h5 : (5:ℚ) ≤ q := by exact_mod_cast hq
  have hm1 : (1:ℚ) ≤ m := by exact_mod_cast hm
  set θ : ℚ := 1 / (2 * ((q:ℚ) - 1) * m) with hθ
  have hq1 : (0:ℚ) < (q:ℚ) - 1 := by linarith
  have hD : 0 < 2 * ((q:ℚ) - 1) * m := mul_pos (mul_pos two_pos hq1) (by linarith)
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
  have e : 1 + ((q:ℚ) - 1) * θ = 1 + 1 / (2 * m) := by
    rw [hθ]; field_simp [hq1.ne']
  rw [e]
  have hb : (1 + 1 / (2 * (m:ℚ))) ^ m ≤ 2 := by
    apply bern
    · positivity
    · field_simp; norm_num
    · rw [div_le_one (by positivity)]; linarith
  have hp := prod_bound hq z x' (1 + 1 / (2 * (m:ℚ))) (by
    have : (0:ℚ) ≤ 1 / (2 * m) := by positivity
    linarith) R hR
  have hθr : θ ^ (r - 1) = 1 / (2 * ((q:ℚ) - 1) * m) ^ (r - 1) := by
    rw [hθ, one_div_pow]
  rw [hθr, div_div_eq_mul_div, div_one]
  have hqR : (0:ℚ) ≤ (q:ℚ) ^ R := by positivity
  have hpos : (0:ℚ) ≤ (2 * ((q:ℚ) - 1) * m) ^ (r - 1) := by positivity
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ hpos
  refine hp.trans ?_
  nlinarith
lemma U_piece {q m : ℕ} (hq : 5 ≤ q) (hm : 0 < m) (r R : ℕ) (z : Fin m → Fin q)
    (P : Finset (Fin m → Fin q)) (hP : ∀ x ∈ P, hd z x ≤ R) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) :
    ∑ y : Fin m → Fin q, (∑ x ∈ P, a x * KK x y) ^ 2 ≤
      (q:ℚ) ^ m * (rho q ^ (2 * r) * (P.card : ℚ) ^ 2 +
        2 * (P.card : ℚ) * ((2 * ((q:ℚ) - 1) * m) ^ (r - 1) * (2 * (q:ℚ) ^ R))) := by
  have hq0 : (0:ℚ) ≤ (q:ℚ) ^ m := by positivity
  have hρ0 := rho_nonneg hq
  have hρ1 := rho_le_one hq
  set Cc : ℚ := (2 * ((q:ℚ) - 1) * m) ^ (r - 1) * (2 * (q:ℚ) ^ R) with hCc
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
      fun x' hx' => close_count hq hm r R z x' (hP x' hx') P
    refine (Finset.sum_le_sum this).trans ?_
    simp
  have c2 : ∑ x ∈ P, ∑ x' ∈ P, (if jj z x' x ≤ r - 1 then (1:ℚ) else 0) ≤ (P.card : ℚ) * Cc := by
    have : ∀ x ∈ P, ∑ x' ∈ P, (if jj z x' x ≤ r - 1 then (1:ℚ) else 0) ≤ Cc :=
      fun x hx => close_count hq hm r R z x (hP x hx) P
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
    [DecidableRel B] (Hn : ℕ) (hH : 0 < Hn) (κ c σ : ℚ)
    (hsub : ∀ (S : Finset α) (z : α), Φ S ≤ Φ (S.filter (B z)) + Φ (S.filter (fun x => ¬ B z x)))
    (hpiece : ∀ (z : α) (P : Finset α), (∀ x ∈ P, B z x) → Hn ≤ P.card → Φ P ≤ κ * (c * P.card))
    (hrem : ∀ S : Finset α, (∀ z, (S.filter (B z)).card < Hn) → Φ S ≤ κ * (c * S.card + σ)) :
    ∀ S : Finset α, Φ S ≤ κ * (c * S.card + σ) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hex : ∃ z, Hn ≤ (S.filter (B z)).card
    · obtain ⟨z, hz⟩ := hex
      have hP : ∀ x ∈ S.filter (B z), B z x := fun x hx => (mem_filter.1 hx).2
      have h1 := hpiece z _ hP hz
      have hne : (S.filter (B z)).Nonempty := by rw [← card_pos]; omega
      obtain ⟨x0, hx0⟩ := hne
      have hsub' : S.filter (fun x => ¬ B z x) ⊂ S := by
        refine ⟨filter_subset _ _, ?_⟩
        intro hcon
        have h2 := hcon (mem_filter.1 hx0).1
        exact (mem_filter.1 h2).2 (mem_filter.1 hx0).2
      have h2 := ih _ hsub'
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
lemma Phi_piece {q m : ℕ} (hq : 5 ≤ q) (hm : 0 < m) (r R : ℕ) (z : Fin m → Fin q)
    (P : Finset (Fin m → Fin q)) (hP : ∀ x ∈ P, hd z x ≤ R) (a : (Fin m → Fin q) → ℚ)
    (ha : ∀ x, |a x| ≤ 1) (A d : ℚ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hAr : A = rho q ^ r)
    (hd0 : 0 < d)
    (hU : 4 * (2 * ((q:ℚ) - 1)) ^ (r - 1) * (q:ℚ) ^ R * (m:ℚ) ^ (r - 1) ≤ d ^ 2 * P.card)
    (hT : (((q:ℚ) - 1) * (2 * q * ((q:ℚ) - 2))) ^ R ≤ d ^ 2 * P.card) (hPpos : 0 < P.card) :
    Phi a (A * (q:ℚ) ^ m) P ≤ (q:ℚ) ^ m * ((A + 2 * d) * P.card) := by
  unfold Phi
  have hNpos : (0:ℚ) < (q:ℚ) ^ m := by
    have : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hPq : (0:ℚ) < P.card := by exact_mod_cast hPpos
  have hU2 := U_piece hq hm r R z P hP a ha
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
    rw [mul_pow (2 * ((q:ℚ) - 1)) (m:ℚ)]
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
    ∃ C : ℕ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ (left right : (Fin m → Fin q) → Bool) (M : ℕ)
      (send : (Fin m → Fin q) → Fin M) (read : Fin M → (Fin m → Fin q) → Bool),
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
      q ^ m ≤ C * M * m ^ (r - 1) := by
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
  intro m hm left right M send read hbias
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
  have hcon' : (C : ℚ) * M * (m : ℚ) ^ (r - 1) < (q:ℚ) ^ m := by exact_mod_cast hcon
  obtain ⟨Hn, hHn⟩ : ∃ Hn : ℕ, Hn = K * m ^ (r - 1) := ⟨_, rfl⟩
  have hHpos : 0 < Hn := by rw [hHn]; positivity
  have hmr : (1:ℚ) ≤ (m:ℚ) ^ (r - 1) := one_le_pow₀ (by exact_mod_cast hm)
  have hHn' : (Hn : ℚ) = K * (m:ℚ) ^ (r - 1) := by rw [hHn]; push_cast; ring
  obtain ⟨a, ha⟩ : ∃ a : (Fin m → Fin q) → ℚ, a = fun x => if left x then (-1:ℚ) else 1 :=
    ⟨_, rfl⟩
  rw [← ha] at hB
  have haa : ∀ x, |a x| ≤ 1 := by intro x; rw [ha]; dsimp only; split_ifs <;> norm_num
  have hcl : ∀ S : Finset (Fin m → Fin q), Phi a (A * (q:ℚ) ^ m) S ≤
      (q:ℚ) ^ m * ((A + 2 * d) * S.card + ((Hn : ℚ) / d) / 2) := by
    apply claim_abs (Phi a (A * (q:ℚ) ^ m)) (fun z x => hd z x ≤ R) Hn hHpos
    · intro S z
      exact Phi_sub a _ (mul_nonneg hA0 hNpos.le) S _
    · intro z P hP hPc
      have hPc' : (Hn : ℚ) ≤ P.card := by exact_mod_cast hPc
      apply Phi_piece hq hm r R z P hP a haa A d hA0 hA1 hAr hd0
      · have h1 : cU ≤ d ^ 2 * K := by
          rw [div_le_iff₀ (by positivity)] at hK1; linarith
        have h2 : cU * (m:ℚ) ^ (r - 1) ≤ d ^ 2 * K * (m:ℚ) ^ (r - 1) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
        have h3 : d ^ 2 * (K * (m:ℚ) ^ (r - 1)) ≤ d ^ 2 * P.card := by
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
    refine (Finset.sum_le_sum (fun c _ => hcl _)).trans ?_
    rw [← mul_sum, sum_add_distrib, ← mul_sum, hcard]
    simp [sum_const, card_univ, Fintype.card_fin]
  have hMH : (M : ℚ) * Hn ≤ d ^ 2 * (q:ℚ) ^ m := by
    rw [hHn']
    have h1 : (K : ℚ) ≤ d ^ 2 * C := by rw [div_le_iff₀ (by positivity)] at hC1; linarith
    have h2 : (M : ℚ) * (K * (m:ℚ) ^ (r - 1)) ≤ (M : ℚ) * (d ^ 2 * C * (m:ℚ) ^ (r - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    calc (M : ℚ) * (K * (m:ℚ) ^ (r - 1)) ≤ (M : ℚ) * (d ^ 2 * C * (m:ℚ) ^ (r - 1)) := h2
      _ = d ^ 2 * ((C : ℚ) * M * (m : ℚ) ^ (r - 1)) := by ring
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
end PEqualNP.Outside.L_lib_962
theorem PEqualNP.Outside.L_lib_962 : ∀ (q r : Nat), 5 ≤ q → 0 < r →
  let A : ℚ := (1-4/(q : ℚ))^r
  ∀ β : ℚ, A < (1+A)*β →
    ∃ C : Nat, 0 < C ∧ ∀ m : Nat, 0 < m →
      let W := Fin m → Fin q
      let N := q^m
      let eqs := fun (x y : W) =>
        ((Finset.univ : Finset (Fin m)).filter (fun i => x i = y i)).card
      let mass := fun (x y : W) => (((q-3)^(eqs x y) : Nat) : ℚ) /
        (((2*(q-2))^m : Nat) : ℚ)
      ∀ (left right : W → Bool) (M : Nat) (send : W → Fin M)
          (read : Fin M → W → Bool),
        let sign := fun (x y : W) => if read (send x) y =
          xor (xor (left x) (right y)) (eqs x y % 2 == 1) then (1 : ℚ) else -1
        let uniformBias := (∑ x : W, ∑ y : W, sign x y) / (N : ℚ)^2
        let tiltedBias := (∑ x : W, ∑ y : W, mass x y * sign x y) / (N : ℚ)
        (1+A)*β ≤ uniformBias+A*tiltedBias → N ≤ C*M*m^(r-1) := by
  intro q r hq hr A β hβ
  obtain ⟨C, hC, hmain⟩ := PEqualNP.Outside.L_lib_962.main q r hq hr β hβ
  exact ⟨C, hC, fun m hm left right M send read hb => hmain m hm left right M send read hb⟩
