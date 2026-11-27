import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_633_aux

open scoped BigOperators

abbrev Tab (N : ℕ) := Fin N → Fin N → Bool

def had {N : ℕ} (M : Tab N) : Prop :=
  ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N

def sample {N : ℕ} (D : Tab N) (r c : Fin N → Fin N) (u v : Fin N → Bool) (i j : Fin N) : Bool :=
  xor (xor (u i) (v j)) (D (r i) (c j))

def clone {N : ℕ} (A B : Tab N) : Prop :=
  ∃ i j : Fin N, i ≠ j ∧ ∃ flip : Bool,
    ∀ x y, B x y = if x = i then xor flip (A j y) else A x y

def rowErr {N : ℕ} (A B : Tab N) (i : Fin N) : ℕ :=
  ((Finset.univ : Finset (Fin N)).filter (fun j => A i j ≠ B i j)).card

def errors {N : ℕ} (A B : Tab N) : ℕ :=
  ∑ i : Fin N, rowErr A B i

def sgn (b : Bool) : ℝ := if b then -1 else 1

lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

lemma sgn_mul_eq (a b : Bool) : sgn a * sgn b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> simp [sgn]

lemma sgn_abs (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

lemma sgn_sub_eq (a b : Bool) : |sgn a - sgn b| = if a ≠ b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [sgn]

lemma sgn_add_eq (a b : Bool) : |sgn a + sgn b| = if a = b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [sgn]

lemma had_even {N : ℕ} (hN : 8 ≤ N) {M : Tab N} (hM : had M) : 2 * (N / 2) = N := by
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by simp
  have hd := hM ⟨0, by omega⟩ ⟨1, by omega⟩ h01
  omega

lemma sum_sgn_mul_rows {N : ℕ} (A B : Tab N) (i₁ i₂ : Fin N) :
    ∑ j : Fin N, sgn (A i₁ j) * sgn (B i₂ j) =
      (N : ℝ) - 2 * (((Finset.univ : Finset (Fin N)).filter (fun j => A i₁ j ≠ B i₂ j)).card : ℝ) := by
  have h1 : ∀ j : Fin N, sgn (A i₁ j) * sgn (B i₂ j) = (1 : ℝ) - if A i₁ j ≠ B i₂ j then 2 else 0 := by
    intro j
    cases A i₁ j <;> cases B i₂ j <;> norm_num [sgn]
  simp_rw [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  ring

lemma had_iff_orth {N : ℕ} (M : Tab N) :
    had M ↔ ∀ a b : Fin N, ∑ j : Fin N, sgn (M a j) * sgn (M b j) = if a = b then (N : ℝ) else 0 := by
  constructor
  · intro hM a b
    by_cases hab : a = b
    · subst hab
      simp [sgn_sq]
    · rw [if_neg hab, sum_sgn_mul_rows]
      have hd := hM a b hab
      have hcast : (2 : ℝ) * (((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card : ℝ) = (N : ℝ) := by
        exact_mod_cast hd
      linarith
  · intro horth a b hab
    have h0 := horth a b
    rw [if_neg hab, sum_sgn_mul_rows] at h0
    have hcast : (2 : ℝ) * (((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card : ℝ) = (N : ℝ) := by
      linarith
    exact_mod_cast hcast

lemma had_swap {N : ℕ} (hN : 1 ≤ N) {M : Tab N} (hM : had M) : had (Function.swap M) := by
  have horth := (had_iff_orth M).mp hM
  let A : Matrix (Fin N) (Fin N) ℝ := Matrix.of (fun i j => sgn (M i j))
  have hNpos : (N : ℝ) ≠ 0 := by positivity
  have hmul : ((N : ℝ)⁻¹ • A) * A.transpose = 1 := by
    ext a b
    simp only [Matrix.smul_mul, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.of_apply, Matrix.one_apply, smul_eq_mul, A]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, horth a b]
    split_ifs <;> simp [hNpos]
  have hmul' : A.transpose * ((N : ℝ)⁻¹ • A) = 1 := mul_eq_one_comm.mp hmul
  rw [had_iff_orth]
  intro a b
  have hent := congr_fun (congr_fun hmul' a) b
  simp only [Matrix.mul_smul, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.one_apply, smul_eq_mul, A] at hent
  have hpull : ∑ x : Fin N, sgn (M x a) * ((N : ℝ)⁻¹ * sgn (M x b)) =
      (N : ℝ)⁻¹ * ∑ x : Fin N, sgn (M x a) * sgn (M x b) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring
  rw [hpull] at hent
  have hsum : ∑ x : Fin N, sgn (M x a) * sgn (M x b) = if a = b then (N : ℝ) else 0 := by
    split_ifs at hent ⊢
    · have : (N : ℝ) * ((N : ℝ)⁻¹ * ∑ x : Fin N, sgn (M x a) * sgn (M x b)) = (N : ℝ) * 1 :=
        congr_arg ((N : ℝ) * ·) hent
      rw [← mul_assoc, mul_inv_cancel₀ hNpos, one_mul, mul_one] at this
      exact this
    · exact (mul_eq_zero.mp hent).resolve_left (inv_ne_zero hNpos)
  simpa [Function.swap] using hsum

lemma had_col_sum {N : ℕ} (hN : 1 ≤ N) {M : Tab N} (hM : had M) (j₁ j₂ : Fin N) :
    ∑ i : Fin N, sgn (M i j₁) * sgn (M i j₂) = if j₁ = j₂ then (N : ℝ) else 0 := by
  have hsw := (had_iff_orth (Function.swap M)).mp (had_swap hN hM) j₁ j₂
  simpa [Function.swap] using hsw

lemma had_sample_bij {N : ℕ} {D : Tab N} (hD : had D)
    {r c : Fin N → Fin N} (hr : Function.Injective r) (hc : Function.Injective c)
    (u v : Fin N → Bool) : had (sample D r c u v) := by
  have hc_bij : Function.Bijective c := (Finite.injective_iff_bijective).mp hc
  let e : Fin N ≃ Fin N := Equiv.ofBijective c hc_bij
  rw [had_iff_orth]
  intro a b
  have h1 : ∀ j : Fin N, sgn (sample D r c u v a j) * sgn (sample D r c u v b j) =
      (sgn (u a) * sgn (u b)) * (sgn (D (r a) (c j)) * sgn (D (r b) (c j))) := by
    intro j
    simp only [sample, sgn_xor]
    have hv := sgn_sq (v j)
    linear_combination (sgn (u a) * sgn (u b) * sgn (D (r a) (c j)) * sgn (D (r b) (c j))) * hv
  simp_rw [h1, ← Finset.mul_sum]
  have hsum : ∑ j : Fin N, sgn (D (r a) (c j)) * sgn (D (r b) (c j)) =
      ∑ y : Fin N, sgn (D (r a) y) * sgn (D (r b) y) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hsum, (had_iff_orth D).mp hD (r a) (r b)]
  by_cases hab : a = b
  · subst hab; simp [sgn_sq]
  · have hrab : r a ≠ r b := fun h => hab (hr h)
    simp [hab, hrab]

lemma errors_swap {N : ℕ} (A B : Tab N) : errors (Function.swap A) (Function.swap B) = errors A B := by
  unfold errors rowErr
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]

lemma sample_swap {N : ℕ} (D : Tab N) (r c : Fin N → Fin N) (u v : Fin N → Bool) :
    Function.swap (sample D r c u v) = sample (Function.swap D) c r v u := by
  funext i j
  simp only [Function.swap, sample]
  cases u j <;> cases v i <;> cases D (r j) (c i) <;> rfl

lemma filter_xor_card {N : ℕ} {M : Tab N} (hM : had M) {a b : Fin N} (hab : a ≠ b) (flip : Bool) :
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor flip (M b j))).card = N := by
  cases flip
  · simpa using hM a b hab
  · have hcomp : ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ xor true (M b j))).card +
        ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N := by
      have h1 : ∀ j : Fin N, (M a j ≠ xor true (M b j)) ↔ ¬ (M a j ≠ M b j) := by
        intro j; cases M a j <;> cases M b j <;> decide
      simp_rw [h1]
      have hcard := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
        (p := fun j => M a j ≠ M b j)
      simp only [Finset.card_univ, Fintype.card_fin] at hcard
      omega
    have hd := hM a b hab
    omega

lemma xor_cancel_left (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

lemma pair_err_ge {N : ℕ} (hN : 8 ≤ N) {H : Tab N} (hH : had H) {K : Tab N}
    {i₀ i₁ : Fin N} (hne : i₀ ≠ i₁) {flip : Bool}
    (hrel : ∀ j, K i₀ j = xor flip (K i₁ j)) :
    2 * (rowErr H K i₀ + rowErr H K i₁) ≥ N := by
  have hd := filter_xor_card hH hne flip
  have hsub : (Finset.univ : Finset (Fin N)).filter (fun j => H i₀ j ≠ xor flip (H i₁ j)) ⊆
      (Finset.univ : Finset (Fin N)).filter (fun j => H i₀ j ≠ K i₀ j) ∪
      (Finset.univ : Finset (Fin N)).filter (fun j => H i₁ j ≠ K i₁ j) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hj ⊢
    by_contra h
    push_neg at h
    rcases h with ⟨h0, h1⟩
    apply hj
    rw [h0, h1, hrel j]
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    ((Finset.univ : Finset (Fin N)).filter (fun j => H i₀ j ≠ K i₀ j))
    ((Finset.univ : Finset (Fin N)).filter (fun j => H i₁ j ≠ K i₁ j))
  unfold rowErr
  omega

lemma bool4_overlap (e00 e01 e10 e11 : Bool) :
    (if xor e00 e10 then 1 else 0) + (if xor e01 e11 then 1 else 0) +
    (if xor e00 e01 then 1 else 0) + (if xor e10 e11 then 1 else 0) ≤
    (if e00 then 1 else 0) + (if e01 then 1 else 0) +
    (if e10 then 1 else 0) + (if e11 then 1 else 0) + 2 := by
  cases e00 <;> cases e01 <;> cases e10 <;> cases e11 <;> decide

lemma case_both_noninj {N : ℕ} (hN : 8 ≤ N) {H D : Tab N} (hH : had H)
    {r c : Fin N → Fin N} (hr : ¬ Function.Injective r) (hc : ¬ Function.Injective c)
    (u v : Fin N → Bool) :
    N ≤ errors H (sample D r c u v) + 2 := by
  set K := sample D r c u v
  simp only [Function.Injective, not_forall] at hr hc
  rcases hr with ⟨i₀, i₁, hr_eq, hi_ne⟩
  rcases hc with ⟨j₀, j₁, hc_eq, hj_ne⟩
  let fr : Bool := xor (u i₀) (u i₁)
  let fc : Bool := xor (v j₀) (v j₁)
  have hKr : ∀ j, K i₀ j = xor fr (K i₁ j) := by
    intro j; simp only [K, sample, fr, hr_eq]
    cases u i₀ <;> cases u i₁ <;> cases v j <;> cases D (r i₁) (c j) <;> rfl
  have hKc : ∀ i, K i j₀ = xor fc (K i j₁) := by
    intro i; simp only [K, sample, fc, hc_eq]
    cases u i <;> cases v j₀ <;> cases v j₁ <;> cases D (r i) (c j₁) <;> rfl
  let ind : Fin N → Fin N → ℕ := fun i j => if H i j ≠ K i j then 1 else 0
  have herr_eq : errors H K = ∑ i : Fin N, ∑ j : Fin N, ind i j := by
    unfold errors rowErr ind
    simp_rw [Finset.card_filter]
  let S_r : Finset (Fin N) := {i₀, i₁}
  let S_c : Finset (Fin N) := {j₀, j₁}
  have herr_split : ∑ i : Fin N, ∑ j : Fin N, ind i j ≥
      (∑ j ∈ S_cᶜ, (ind i₀ j + ind i₁ j)) +
      (∑ i ∈ S_rᶜ, (ind i j₀ + ind i j₁)) +
      (ind i₀ j₀ + ind i₀ j₁ + ind i₁ j₀ + ind i₁ j₁) := by
    have h1 : ∑ i : Fin N, ∑ j : Fin N, ind i j =
        (∑ i ∈ S_r, ∑ j : Fin N, ind i j) + (∑ i ∈ S_rᶜ, ∑ j : Fin N, ind i j) := by
      rw [Finset.sum_add_sum_compl]
    have h2 : ∑ i ∈ S_r, ∑ j : Fin N, ind i j =
        (∑ j ∈ S_cᶜ, (ind i₀ j + ind i₁ j)) + (ind i₀ j₀ + ind i₀ j₁ + ind i₁ j₀ + ind i₁ j₁) := by
      rw [Finset.sum_pair hi_ne]
      have hs0 := (Finset.sum_add_sum_compl S_c (fun j => ind i₀ j)).symm
      have hs1 := (Finset.sum_add_sum_compl S_c (fun j => ind i₁ j)).symm
      rw [Finset.sum_pair hj_ne] at hs0 hs1
      rw [hs0, hs1, Finset.sum_add_distrib]
      omega
    have h3 : ∑ i ∈ S_rᶜ, ∑ j : Fin N, ind i j ≥ ∑ i ∈ S_rᶜ, (ind i j₀ + ind i j₁) := by
      apply Finset.sum_le_sum
      intro i _
      have hs := (Finset.sum_add_sum_compl S_c (fun j => ind i j)).symm
      rw [Finset.sum_pair hj_ne] at hs
      omega
    omega
  let a : Fin N → ℕ := fun j => if H i₀ j ≠ xor fr (H i₁ j) then 1 else 0
  let b : Fin N → ℕ := fun i => if H i j₀ ≠ xor fc (H i j₁) then 1 else 0
  have ha_sum : 2 * (∑ j : Fin N, a j) = N := by
    have := filter_xor_card hH hi_ne fr
    simpa [a, Finset.card_filter] using this
  have hb_sum : 2 * (∑ i : Fin N, b i) = N := by
    have hHsw := had_swap (by omega) hH
    have := filter_xor_card hHsw hj_ne fc
    simpa [b, Function.swap, Finset.card_filter] using this
  have hrow_compl : ∑ j ∈ S_cᶜ, (ind i₀ j + ind i₁ j) ≥ ∑ j ∈ S_cᶜ, a j := by
    apply Finset.sum_le_sum
    intro j _
    simp only [ind, a, hKr j]
    cases H i₀ j <;> cases H i₁ j <;> cases K i₁ j <;> cases fr <;> decide
  have hcol_compl : ∑ i ∈ S_rᶜ, (ind i j₀ + ind i j₁) ≥ ∑ i ∈ S_rᶜ, b i := by
    apply Finset.sum_le_sum
    intro i _
    simp only [ind, b, hKc i]
    cases H i j₀ <;> cases H i j₁ <;> cases K i j₁ <;> cases fc <;> decide
  have ha_split : ∑ j ∈ S_cᶜ, a j + (a j₀ + a j₁) = ∑ j : Fin N, a j := by
    have := Finset.sum_add_sum_compl S_c a
    rw [Finset.sum_pair hj_ne] at this
    omega
  have hb_split : ∑ i ∈ S_rᶜ, b i + (b i₀ + b i₁) = ∑ i : Fin N, b i := by
    have := Finset.sum_add_sum_compl S_r b
    rw [Finset.sum_pair hi_ne] at this
    omega
  have h4 : a j₀ + a j₁ + b i₀ + b i₁ ≤ ind i₀ j₀ + ind i₀ j₁ + ind i₁ j₀ + ind i₁ j₁ + 2 := by
    let e00 : Bool := decide (H i₀ j₀ ≠ K i₀ j₀)
    let e01 : Bool := decide (H i₀ j₁ ≠ K i₀ j₁)
    let e10 : Bool := decide (H i₁ j₀ ≠ K i₁ j₀)
    let e11 : Bool := decide (H i₁ j₁ ≠ K i₁ j₁)
    have hbo := bool4_overlap e00 e01 e10 e11
    have h0 : a j₀ = if xor e00 e10 then 1 else 0 := by
      simp only [a, e00, e10, hKr j₀]
      cases H i₀ j₀ <;> cases H i₁ j₀ <;> cases K i₁ j₀ <;> cases fr <;> decide
    have h1 : a j₁ = if xor e01 e11 then 1 else 0 := by
      simp only [a, e01, e11, hKr j₁]
      cases H i₀ j₁ <;> cases H i₁ j₁ <;> cases K i₁ j₁ <;> cases fr <;> decide
    have h2 : b i₀ = if xor e00 e01 then 1 else 0 := by
      simp only [b, e00, e01, hKc i₀]
      cases H i₀ j₀ <;> cases H i₀ j₁ <;> cases K i₀ j₁ <;> cases fc <;> decide
    have h3 : b i₁ = if xor e10 e11 then 1 else 0 := by
      simp only [b, e10, e11, hKc i₁]
      cases H i₁ j₀ <;> cases H i₁ j₁ <;> cases K i₁ j₁ <;> cases fc <;> decide
    have hi00 : ind i₀ j₀ = if e00 then 1 else 0 := by simp [ind, e00]
    have hi01 : ind i₀ j₁ = if e01 then 1 else 0 := by simp [ind, e01]
    have hi10 : ind i₁ j₀ = if e10 then 1 else 0 := by simp [ind, e10]
    have hi11 : ind i₁ j₁ = if e11 then 1 else 0 := by simp [ind, e11]
    omega
  rw [herr_eq]
  omega

lemma parseval_rows {N : ℕ} (hN : 1 ≤ N) {H : Tab N} (hH : had H) (w : Fin N → ℝ)
    (hw : ∀ j, w j * w j = 1) :
    ∑ i : Fin N, (∑ j : Fin N, w j * sgn (H i j)) ^ 2 = (N : ℝ) ^ 2 := by
  have h1 : ∀ i : Fin N, (∑ j : Fin N, w j * sgn (H i j)) ^ 2 =
      ∑ j₁ : Fin N, ∑ j₂ : Fin N, w j₁ * w j₂ * (sgn (H i j₁) * sgn (H i j₂)) := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j₁ _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j₂ _
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ j₁ : Fin N, ∑ i : Fin N, ∑ j₂ : Fin N, w j₁ * w j₂ * (sgn (H i j₁) * sgn (H i j₂)) =
      (N : ℝ) := by
    intro j₁
    rw [Finset.sum_comm]
    have h3 : ∀ j₂ : Fin N, ∑ i : Fin N, w j₁ * w j₂ * (sgn (H i j₁) * sgn (H i j₂)) =
        if j₁ = j₂ then (N : ℝ) else 0 := by
      intro j₂
      rw [← Finset.mul_sum, had_col_sum hN hH j₁ j₂]
      split_ifs with heq
      · subst heq; rw [hw j₁, one_mul]
      · simp
    simp_rw [h3]
    simp
  simp_rw [h2]
  simp [sq]

lemma inner_bound_diff {N : ℕ} (A B : Tab N) (i : Fin N) (w : Fin N → ℝ) (hw : ∀ j, |w j| = 1) :
    |∑ j : Fin N, (sgn (A i j) - sgn (B i j)) * w j| ≤ 2 * (rowErr A B i : ℝ) := by
  calc |∑ j : Fin N, (sgn (A i j) - sgn (B i j)) * w j|
      ≤ ∑ j : Fin N, |(sgn (A i j) - sgn (B i j)) * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin N, if A i j ≠ B i j then (2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, hw j, mul_one, sgn_sub_eq]
    _ = 2 * (rowErr A B i : ℝ) := by
        unfold rowErr
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        ring

lemma inner_bound_add {N : ℕ} (A B : Tab N) (i : Fin N) (w : Fin N → ℝ) (hw : ∀ j, |w j| = 1) :
    |∑ j : Fin N, (sgn (A i j) + sgn (B i j)) * w j| ≤ 2 * ((N : ℝ) - (rowErr A B i : ℝ)) := by
  have hcomp : ((Finset.univ : Finset (Fin N)).filter (fun j => A i j = B i j)).card +
      rowErr A B i = N := by
    unfold rowErr
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun j => A i j = B i j)
    simpa using this
  calc |∑ j : Fin N, (sgn (A i j) + sgn (B i j)) * w j|
      ≤ ∑ j : Fin N, |(sgn (A i j) + sgn (B i j)) * w j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin N, if A i j = B i j then (2 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, hw j, mul_one, sgn_add_eq]
    _ = 2 * ((N : ℝ) - (rowErr A B i : ℝ)) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
        have hc : (((Finset.univ : Finset (Fin N)).filter (fun j => A i j = B i j)).card : ℝ) +
            (rowErr A B i : ℝ) = (N : ℝ) := by exact_mod_cast hcomp
        linarith

lemma had_trade_bound {N : ℕ} (hN : 1 ≤ N) {H K : Tab N} (hH : had H) (hK : had K)
    (hne : errors H K ≠ 0) : N ≤ errors H K := by
  have hex : ∃ i₀ : Fin N, 0 < rowErr H K i₀ := by
    by_contra h
    push_neg at h
    apply hne
    unfold errors
    exact Finset.sum_eq_zero (fun i _ => Nat.eq_zero_of_le_zero (h i))
  rcases hex with ⟨i₀, hm0_pos⟩
  set m0 := rowErr H K i₀
  have hm0_le : m0 ≤ N := by
    unfold m0 rowErr
    exact le_trans (Finset.card_filter_le _ _) (by simp)
  by_cases hm0_eq : m0 = N
  · have hle : m0 ≤ errors H K := by
      unfold errors m0
      exact Finset.single_le_sum (fun i _ => Nat.zero_le (rowErr H K i)) (Finset.mem_univ i₀)
    omega
  have hm0_lt : m0 < N := lt_of_le_of_ne hm0_le hm0_eq
  have hpars := parseval_rows hN hH (fun j => sgn (K i₀ j)) (fun j => sgn_sq (K i₀ j))
  have hsplit : ∑ i : Fin N, (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) ^ 2 =
      (∑ j : Fin N, sgn (K i₀ j) * sgn (H i₀ j)) ^ 2 +
      ∑ i ∈ (Finset.univ.erase i₀), (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
  have hdiag : ∑ j : Fin N, sgn (K i₀ j) * sgn (H i₀ j) = (N : ℝ) - 2 * (m0 : ℝ) := by
    have h1 : ∀ j : Fin N, sgn (K i₀ j) * sgn (H i₀ j) = sgn (H i₀ j) * sgn (K i₀ j) :=
      fun j => mul_comm _ _
    simp_rw [h1]
    exact sum_sgn_mul_rows H K i₀ i₀
  have hrest_eq : ∑ i ∈ (Finset.univ.erase i₀), (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) ^ 2 =
      4 * (m0 : ℝ) * ((N : ℝ) - (m0 : ℝ)) := by
    rw [hdiag] at hsplit
    linarith
  have hterm_mi : ∀ i ∈ (Finset.univ.erase i₀),
      |∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)| ≤ 2 * (rowErr H K i : ℝ) := by
    intro i hi
    have hne_i : i₀ ≠ i := (Finset.ne_of_mem_erase hi).symm
    have horthK : ∑ j : Fin N, sgn (K i₀ j) * sgn (K i j) = 0 := by
      have := (had_iff_orth K).mp hK i₀ i
      simpa [hne_i] using this
    have heq : ∑ j : Fin N, sgn (K i₀ j) * sgn (H i j) =
        ∑ j : Fin N, (sgn (H i j) - sgn (K i j)) * sgn (K i₀ j) := by
      have hsub : ∑ j : Fin N, (sgn (H i j) - sgn (K i j)) * sgn (K i₀ j) =
          (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) - (∑ j : Fin N, sgn (K i₀ j) * sgn (K i j)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      linarith
    rw [heq]
    exact inner_bound_diff H K i (fun j => sgn (K i₀ j)) (fun j => sgn_abs _)
  have hterm_m0 : ∀ i ∈ (Finset.univ.erase i₀),
      |∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)| ≤ 2 * (m0 : ℝ) := by
    intro i hi
    have hne_i : i₀ ≠ i := (Finset.ne_of_mem_erase hi).symm
    have horthH : ∑ j : Fin N, sgn (H i₀ j) * sgn (H i j) = 0 := by
      have := (had_iff_orth H).mp hH i₀ i
      simpa [hne_i] using this
    have heq : -(∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) =
        ∑ j : Fin N, (sgn (H i₀ j) - sgn (K i₀ j)) * sgn (H i j) := by
      have hsub : ∑ j : Fin N, (sgn (H i₀ j) - sgn (K i₀ j)) * sgn (H i j) =
          (∑ j : Fin N, sgn (H i₀ j) * sgn (H i j)) - (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      linarith
    rw [← abs_neg, heq]
    exact inner_bound_diff H K i₀ (fun j => sgn (H i j)) (fun j => sgn_abs _)
  have hterm_comp : ∀ i ∈ (Finset.univ.erase i₀),
      |∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)| ≤ 2 * ((N : ℝ) - (m0 : ℝ)) := by
    intro i hi
    have hne_i : i₀ ≠ i := (Finset.ne_of_mem_erase hi).symm
    have horthH : ∑ j : Fin N, sgn (H i₀ j) * sgn (H i j) = 0 := by
      have := (had_iff_orth H).mp hH i₀ i
      simpa [hne_i] using this
    have heq : ∑ j : Fin N, sgn (K i₀ j) * sgn (H i j) =
        ∑ j : Fin N, (sgn (H i₀ j) + sgn (K i₀ j)) * sgn (H i j) := by
      have hadd : ∑ j : Fin N, (sgn (H i₀ j) + sgn (K i₀ j)) * sgn (H i j) =
          (∑ j : Fin N, sgn (H i₀ j) * sgn (H i j)) + (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      linarith
    rw [heq]
    exact inner_bound_add H K i₀ (fun j => sgn (H i j)) (fun j => sgn_abs _)
  set c : ℝ := min (m0 : ℝ) ((N : ℝ) - (m0 : ℝ))
  have hc_pos : 0 < c := by
    have h1 : (0 : ℝ) < (m0 : ℝ) := by exact_mod_cast hm0_pos
    have h2 : (0 : ℝ) < (N : ℝ) - (m0 : ℝ) := by
      have : (m0 : ℝ) < (N : ℝ) := by exact_mod_cast hm0_lt
      linarith
    exact lt_min h1 h2
  have hsum_le : ∑ i ∈ (Finset.univ.erase i₀), (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) ^ 2 ≤
      4 * c * ∑ i ∈ (Finset.univ.erase i₀), (rowErr H K i : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h1 := hterm_mi i hi
    have h2 : |∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)| ≤ 2 * c := by
      rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      exact le_min (hterm_m0 i hi) (hterm_comp i hi)
    have hsq : (∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)) ^ 2 =
        |∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)| * |∑ j : Fin N, sgn (K i₀ j) * sgn (H i j)| := by
      rw [← sq, sq_abs]
    rw [hsq]
    have hmul := mul_le_mul h2 h1 (abs_nonneg _) (by linarith)
    linarith
  have herr_cast : (errors H K : ℝ) = (m0 : ℝ) + ∑ i ∈ (Finset.univ.erase i₀), (rowErr H K i : ℝ) := by
    unfold errors m0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    push_cast
    rfl
  have hreal : (N : ℝ) ≤ (errors H K : ℝ) := by
    by_cases hle : (m0 : ℝ) ≤ (N : ℝ) - (m0 : ℝ)
    · have hc_eq : c = (m0 : ℝ) := min_eq_left hle
      rw [hrest_eq, hc_eq] at hsum_le
      have hm0_r : (0 : ℝ) < (m0 : ℝ) := by exact_mod_cast hm0_pos
      have : (N : ℝ) - (m0 : ℝ) ≤ ∑ i ∈ (Finset.univ.erase i₀), (rowErr H K i : ℝ) := by
        nlinarith
      linarith
    · push_neg at hle
      have hc_eq : c = (N : ℝ) - (m0 : ℝ) := min_eq_right (le_of_lt hle)
      rw [hrest_eq, hc_eq] at hsum_le
      have hcomp_r : (0 : ℝ) < (N : ℝ) - (m0 : ℝ) := by
        have : (m0 : ℝ) < (N : ℝ) := by exact_mod_cast hm0_lt
        linarith
      have : (m0 : ℝ) ≤ ∑ i ∈ (Finset.univ.erase i₀), (rowErr H K i : ℝ) := by
        nlinarith
      linarith
  exact_mod_cast hreal

lemma span_three_pm {N : ℕ} (hN : 1 ≤ N)
    (v₁ v₂ v₃ h : Fin N → ℝ)
    (hv₁ : ∀ j, v₁ j * v₁ j = 1) (hv₂ : ∀ j, v₂ j * v₂ j = 1) (hv₃ : ∀ j, v₃ j * v₃ j = 1)
    (hh : ∀ j, h j * h j = 1)
    (h12 : ∑ j : Fin N, v₁ j * v₂ j = 0)
    (h13 : ∑ j : Fin N, v₁ j * v₃ j = 0)
    (h23 : ∑ j : Fin N, v₂ j * v₃ j = 0)
    (c₁ c₂ c₃ : ℝ)
    (hspan : ∀ j, h j = c₁ * v₁ j + c₂ * v₂ j + c₃ * v₃ j) :
    (∀ j, h j = v₁ j) ∨ (∀ j, h j = -v₁ j) ∨
    (∀ j, h j = v₂ j) ∨ (∀ j, h j = -v₂ j) ∨
    (∀ j, h j = v₃ j) ∨ (∀ j, h j = -v₃ j) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hcsq : c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2 = 1 := by
    have hsum : ∑ j : Fin N, h j * h j = (N : ℝ) := by simp [hh]
    have hexp : ∑ j : Fin N, h j * h j =
        (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2) * (N : ℝ) +
        2 * c₁ * c₂ * (∑ j : Fin N, v₁ j * v₂ j) +
        2 * c₁ * c₃ * (∑ j : Fin N, v₁ j * v₃ j) +
        2 * c₂ * c₃ * (∑ j : Fin N, v₂ j * v₃ j) := by
      have hterm : ∀ j : Fin N, h j * h j =
          (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2) +
          2 * c₁ * c₂ * (v₁ j * v₂ j) +
          2 * c₁ * c₃ * (v₁ j * v₃ j) +
          2 * c₂ * c₃ * (v₂ j * v₃ j) := by
        intro j
        rw [hspan j]
        have s1 := hv₁ j; have s2 := hv₂ j; have s3 := hv₃ j
        linear_combination c₁ ^ 2 * s1 + c₂ ^ 2 * s2 + c₃ ^ 2 * s3
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h12, h13, h23] at hexp
    nlinarith
  set α := c₁ * c₂
  set β := c₁ * c₃
  set γ := c₂ * c₃
  have hpt : ∀ j : Fin N, α * (v₁ j * v₂ j) + β * (v₁ j * v₃ j) + γ * (v₂ j * v₃ j) = 0 := by
    intro j
    have h1 := hh j
    rw [hspan j] at h1
    have s1 := hv₁ j; have s2 := hv₂ j; have s3 := hv₃ j
    have h2 : (c₁ * v₁ j + c₂ * v₂ j + c₃ * v₃ j) * (c₁ * v₁ j + c₂ * v₂ j + c₃ * v₃ j) =
        (c₁ ^ 2 + c₂ ^ 2 + c₃ ^ 2) +
        2 * (α * (v₁ j * v₂ j) + β * (v₁ j * v₃ j) + γ * (v₂ j * v₃ j)) := by
      simp only [α, β, γ]
      linear_combination c₁ ^ 2 * s1 + c₂ ^ 2 * s2 + c₃ ^ 2 * s3
    linarith
  have hpyth1 : α ^ 2 + β ^ 2 = γ ^ 2 := by
    have hpt2 : ∀ j : Fin N, α ^ 2 + β ^ 2 + 2 * α * β * (v₂ j * v₃ j) = γ ^ 2 := by
      intro j
      have hp := hpt j
      have s1 := hv₁ j; have s2 := hv₂ j; have s3 := hv₃ j
      have hsq : (α * (v₁ j * v₂ j) + β * (v₁ j * v₃ j)) ^ 2 = (-(γ * (v₂ j * v₃ j))) ^ 2 := by
        rw [show α * (v₁ j * v₂ j) + β * (v₁ j * v₃ j) = -(γ * (v₂ j * v₃ j)) by linarith]
      have hL : (α * (v₁ j * v₂ j) + β * (v₁ j * v₃ j)) ^ 2 =
          α ^ 2 + β ^ 2 + 2 * α * β * (v₂ j * v₃ j) := by
        linear_combination (α ^ 2 * v₂ j * v₂ j + 2 * α * β * v₂ j * v₃ j + β ^ 2 * v₃ j * v₃ j) * s1 +
          α ^ 2 * s2 + β ^ 2 * s3
      have hR : (-(γ * (v₂ j * v₃ j))) ^ 2 = γ ^ 2 := by
        linear_combination γ ^ 2 * v₃ j * v₃ j * s2 + γ ^ 2 * s3
      linarith
    have hsum : ∑ j : Fin N, (α ^ 2 + β ^ 2 + 2 * α * β * (v₂ j * v₃ j)) = ∑ _j : Fin N, γ ^ 2 :=
      Finset.sum_congr rfl (fun j _ => hpt2 j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h23, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith
  have hpyth2 : α ^ 2 + γ ^ 2 = β ^ 2 := by
    have hpt2 : ∀ j : Fin N, α ^ 2 + γ ^ 2 + 2 * α * γ * (v₁ j * v₃ j) = β ^ 2 := by
      intro j
      have hp := hpt j
      have s1 := hv₁ j; have s2 := hv₂ j; have s3 := hv₃ j
      have hsq : (α * (v₁ j * v₂ j) + γ * (v₂ j * v₃ j)) ^ 2 = (-(β * (v₁ j * v₃ j))) ^ 2 := by
        rw [show α * (v₁ j * v₂ j) + γ * (v₂ j * v₃ j) = -(β * (v₁ j * v₃ j)) by linarith]
      have hL : (α * (v₁ j * v₂ j) + γ * (v₂ j * v₃ j)) ^ 2 =
          α ^ 2 + γ ^ 2 + 2 * α * γ * (v₁ j * v₃ j) := by
        linear_combination (α ^ 2 * v₁ j * v₁ j + 2 * α * γ * v₁ j * v₃ j + γ ^ 2 * v₃ j * v₃ j) * s2 +
          α ^ 2 * s1 + γ ^ 2 * s3
      have hR : (-(β * (v₁ j * v₃ j))) ^ 2 = β ^ 2 := by
        linear_combination β ^ 2 * v₃ j * v₃ j * s1 + β ^ 2 * s3
      linarith
    have hsum : ∑ j : Fin N, (α ^ 2 + γ ^ 2 + 2 * α * γ * (v₁ j * v₃ j)) = ∑ _j : Fin N, β ^ 2 :=
      Finset.sum_congr rfl (fun j _ => hpt2 j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h13, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith
  have hpyth3 : β ^ 2 + γ ^ 2 = α ^ 2 := by
    have hpt2 : ∀ j : Fin N, β ^ 2 + γ ^ 2 + 2 * β * γ * (v₁ j * v₂ j) = α ^ 2 := by
      intro j
      have hp := hpt j
      have s1 := hv₁ j; have s2 := hv₂ j; have s3 := hv₃ j
      have hsq : (β * (v₁ j * v₃ j) + γ * (v₂ j * v₃ j)) ^ 2 = (-(α * (v₁ j * v₂ j))) ^ 2 := by
        rw [show β * (v₁ j * v₃ j) + γ * (v₂ j * v₃ j) = -(α * (v₁ j * v₂ j)) by linarith]
      have hL : (β * (v₁ j * v₃ j) + γ * (v₂ j * v₃ j)) ^ 2 =
          β ^ 2 + γ ^ 2 + 2 * β * γ * (v₁ j * v₂ j) := by
        linear_combination (β ^ 2 * v₁ j * v₁ j + 2 * β * γ * v₁ j * v₂ j + γ ^ 2 * v₂ j * v₂ j) * s3 +
          β ^ 2 * s1 + γ ^ 2 * s2
      have hR : (-(α * (v₁ j * v₂ j))) ^ 2 = α ^ 2 := by
        linear_combination α ^ 2 * v₂ j * v₂ j * s1 + α ^ 2 * s2
      linarith
    have hsum : ∑ j : Fin N, (β ^ 2 + γ ^ 2 + 2 * β * γ * (v₁ j * v₂ j)) = ∑ _j : Fin N, α ^ 2 :=
      Finset.sum_congr rfl (fun j _ => hpt2 j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h12, mul_zero, add_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    nlinarith
  have hα : α = 0 := by nlinarith
  have hβ : β = 0 := by nlinarith
  have hγ : γ = 0 := by nlinarith
  by_cases hc1 : c₁ = 0
  · by_cases hc2 : c₂ = 0
    · have hc3 : c₃ = 1 ∨ c₃ = -1 := sq_eq_one_iff.mp (by nlinarith)
      rcases hc3 with rfl | rfl
      · right; right; right; right; left; intro j; simp [hspan j, hc1, hc2]
      · right; right; right; right; right; intro j; simp [hspan j, hc1, hc2]
    · have hc3 : c₃ = 0 := (mul_eq_zero.mp hγ).resolve_left hc2
      have hc2' : c₂ = 1 ∨ c₂ = -1 := sq_eq_one_iff.mp (by nlinarith)
      rcases hc2' with rfl | rfl
      · right; right; left; intro j; simp [hspan j, hc1, hc3]
      · right; right; right; left; intro j; simp [hspan j, hc1, hc3]
  · have hc2 : c₂ = 0 := (mul_eq_zero.mp hα).resolve_left hc1
    have hc3 : c₃ = 0 := (mul_eq_zero.mp hβ).resolve_left hc1
    have hc1' : c₁ = 1 ∨ c₁ = -1 := sq_eq_one_iff.mp (by nlinarith)
    rcases hc1' with rfl | rfl
    · left; intro j; simp [hspan j, hc2, hc3]
    · right; left; intro j; simp [hspan j, hc2, hc3]

lemma span_two_pm {N : ℕ} (hN : 1 ≤ N)
    (v₁ v₂ h : Fin N → ℝ)
    (hv₁ : ∀ j, v₁ j * v₁ j = 1) (hv₂ : ∀ j, v₂ j * v₂ j = 1)
    (hh : ∀ j, h j * h j = 1)
    (h12 : ∑ j : Fin N, v₁ j * v₂ j = 0)
    (c₁ c₂ : ℝ)
    (hspan : ∀ j, h j = c₁ * v₁ j + c₂ * v₂ j) :
    (∀ j, h j = v₁ j) ∨ (∀ j, h j = -v₁ j) ∨
    (∀ j, h j = v₂ j) ∨ (∀ j, h j = -v₂ j) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hcsq : c₁ ^ 2 + c₂ ^ 2 = 1 := by
    have hsum : ∑ j : Fin N, h j * h j = (N : ℝ) := by simp [hh]
    have hexp : ∑ j : Fin N, h j * h j =
        (c₁ ^ 2 + c₂ ^ 2) * (N : ℝ) + 2 * c₁ * c₂ * (∑ j : Fin N, v₁ j * v₂ j) := by
      have hterm : ∀ j : Fin N, h j * h j = (c₁ ^ 2 + c₂ ^ 2) + 2 * c₁ * c₂ * (v₁ j * v₂ j) := by
        intro j; rw [hspan j]
        linear_combination c₁ ^ 2 * hv₁ j + c₂ ^ 2 * hv₂ j
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [h12] at hexp
    nlinarith
  have hpt : c₁ * c₂ = 0 := by
    have h0 := hh ⟨0, by omega⟩
    rw [hspan ⟨0, by omega⟩] at h0
    have s1 := hv₁ ⟨0, by omega⟩; have s2 := hv₂ ⟨0, by omega⟩
    have h1 : 2 * c₁ * c₂ * (v₁ ⟨0, by omega⟩ * v₂ ⟨0, by omega⟩) = 0 := by
      linear_combination h0 - c₁ ^ 2 * s1 - c₂ ^ 2 * s2 - hcsq
    have hvne : v₁ ⟨0, by omega⟩ * v₂ ⟨0, by omega⟩ ≠ 0 := by
      intro hz
      have : (v₁ ⟨0, by omega⟩ * v₂ ⟨0, by omega⟩) ^ 2 = 1 := by
        linear_combination (v₂ ⟨0, by omega⟩ ^ 2) * s1 + s2
      rw [hz] at this; norm_num at this
    have : 2 * c₁ * c₂ = 0 := (mul_eq_zero.mp h1).resolve_right hvne
    linarith
  by_cases hc1 : c₁ = 0
  · have hc2 : c₂ = 1 ∨ c₂ = -1 := sq_eq_one_iff.mp (by nlinarith)
    rcases hc2 with rfl | rfl
    · right; right; left; intro j; simp [hspan j, hc1]
    · right; right; right; intro j; simp [hspan j, hc1]
  · have hc2 : c₂ = 0 := (mul_eq_zero.mp hpt).resolve_left hc1
    have hc1' : c₁ = 1 ∨ c₁ = -1 := sq_eq_one_iff.mp (by nlinarith)
    rcases hc1' with rfl | rfl
    · left; intro j; simp [hspan j, hc2]
    · right; left; intro j; simp [hspan j, hc2]

lemma fiber_err_bound {N : ℕ} (hN : 8 ≤ N) {H D' : Tab N} (hH : had H)
    {r : Fin N → Fin N} {u : Fin N → Bool}
    (x : Fin N) (F : Finset (Fin N)) (hF : F = Finset.univ.filter (fun i => r i = x))
    (hcard : 2 ≤ F.card) :
    F.card * N ≤ 4 * ∑ i ∈ F, rowErr H (fun i j => xor (u i) (D' (r i) j)) i := by
  set K : Tab N := fun i j => xor (u i) (D' (r i) j)
  have hpair : ∀ a ∈ F, ∀ b ∈ F, a ≠ b → N ≤ 2 * (rowErr H K a + rowErr H K b) := by
    intro a ha b hb hab
    rw [hF, Finset.mem_filter] at ha hb
    have hrel : ∀ j, K a j = xor (xor (u a) (u b)) (K b j) := by
      intro j
      simp only [K, ha.2, hb.2]
      cases u a <;> cases u b <;> cases D' x j <;> rfl
    exact pair_err_ge hN hH hab hrel
  have hsum_pairs : ∑ a ∈ F, ∑ b ∈ F.erase a, N ≤
      ∑ a ∈ F, ∑ b ∈ F.erase a, 2 * (rowErr H K a + rowErr H K b) := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    exact hpair a ha b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
  have hLHS : ∑ a ∈ F, ∑ b ∈ F.erase a, N = F.card * (F.card - 1) * N := by
    have h1 : ∀ a ∈ F, ∑ _b ∈ F.erase a, N = (F.card - 1) * N := by
      intro a ha
      rw [Finset.sum_const, Finset.card_erase_of_mem ha, smul_eq_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_assoc]
  have hRHS : ∑ a ∈ F, ∑ b ∈ F.erase a, 2 * (rowErr H K a + rowErr H K b) =
      4 * (F.card - 1) * ∑ i ∈ F, rowErr H K i := by
    have hsplit : ∀ a ∈ F, ∑ b ∈ F.erase a, 2 * (rowErr H K a + rowErr H K b) =
        2 * (F.card - 1) * rowErr H K a + 2 * ∑ b ∈ F.erase a, rowErr H K b := by
      intro a ha
      simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem ha,
        smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ a ∈ F, ∑ b ∈ F.erase a, rowErr H K b = (F.card - 1) * ∑ i ∈ F, rowErr H K i := by
      have h3 : ∀ a ∈ F, ∑ b ∈ F.erase a, rowErr H K b + rowErr H K a = ∑ i ∈ F, rowErr H K i :=
        fun a ha => Finset.sum_erase_add F (rowErr H K) ha
      have h4 : ∑ a ∈ F, (∑ b ∈ F.erase a, rowErr H K b + rowErr H K a) =
          F.card * ∑ i ∈ F, rowErr H K i := by
        rw [Finset.sum_congr rfl h3, Finset.sum_const, smul_eq_mul]
      rw [Finset.sum_add_distrib] at h4
      have h5 : (F.card - 1) * (∑ i ∈ F, rowErr H K i) + ∑ i ∈ F, rowErr H K i =
          F.card * ∑ i ∈ F, rowErr H K i := by
        cases hc : F.card with
        | zero => omega
        | succ m => simp [Nat.succ_mul]
      omega
    rw [h2]
    ring
  rw [hLHS, hRHS] at hsum_pairs
  have hpos : 0 < F.card - 1 := by omega
  have hmul_le : (F.card - 1) * (F.card * N) ≤ (F.card - 1) * (4 * ∑ i ∈ F, rowErr H K i) := by
    linarith
  exact Nat.le_of_mul_le_mul_left hmul_le hpos

lemma sgn_eq_iff_bool (a b : Bool) : sgn a = sgn b ↔ a = b := by
  cases a <;> cases b <;> norm_num [sgn]

lemma sgn_eq_neg_iff_bool (a b : Bool) : sgn a = -sgn b ↔ a = xor true b := by
  cases a <;> cases b <;> norm_num [sgn]

lemma case_r_noninj_c_inj {N : ℕ} (hN : 8 ≤ N) {H D : Tab N} (hH : had H) (hD : had D)
    {r c : Fin N → Fin N} (hr : ¬ Function.Injective r) (hc : Function.Injective c)
    (u v : Fin N → Bool) (herr : errors H (sample D r c u v) + 2 < N) :
    (∃ (f g : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sample D f g a b) ∧
    (2 * errors H (sample D r c u v) = N ∧ clone H (sample D r c u v)) := by
  classical
  have hc_bij : Function.Bijective c := (Finite.injective_iff_bijective).mp hc
  let cPerm : Equiv.Perm (Fin N) := Equiv.ofBijective c hc_bij
  let D' : Tab N := fun x j => xor (v j) (D x (c j))
  have hD' : had D' := by
    have h1 := had_sample_bij hD Function.injective_id hc (fun _ => false) v
    have h2 : sample D id c (fun _ => false) v = D' := by
      funext x j; simp [sample, D']
    rwa [h2] at h1
  set K : Tab N := sample D r c u v
  have hK_eq : K = fun i j => xor (u i) (D' (r i) j) := by
    funext i j
    simp only [K, sample, D']
    cases u i <;> cases v j <;> cases D (r i) (c j) <;> rfl
  have hex_rep : ∃ x₀ : Fin N, 2 ≤ (Finset.univ.filter (fun i => r i = x₀)).card := by
    simp only [Function.Injective, not_forall] at hr
    rcases hr with ⟨i₀, i₁, heq, hne⟩
    refine ⟨r i₀, ?_⟩
    have hsub : ({i₀, i₁} : Finset (Fin N)) ⊆ Finset.univ.filter (fun i => r i = r i₀) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl
      · rfl
      · exact heq.symm
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hne] at this
  rcases hex_rep with ⟨x₀, hx₀_card⟩
  set F : Finset (Fin N) := Finset.univ.filter (fun i => r i = x₀)
  have hEF : F.card * N ≤ 4 * ∑ i ∈ F, rowErr H K i := by
    rw [hK_eq]
    exact fiber_err_bound hN hH x₀ F rfl hx₀_card
  have hF_le : ∑ i ∈ F, rowErr H K i ≤ errors H K :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hp_le3 : F.card ≤ 3 := by
    by_contra h
    push_neg at h
    have : 4 * N ≤ F.card * N := Nat.mul_le_mul_right N h
    omega
  have huniq_rep : ∀ x : Fin N, x ≠ x₀ → (Finset.univ.filter (fun i => r i = x)).card ≤ 1 := by
    intro x hne
    by_contra h
    push_neg at h
    set Fx := Finset.univ.filter (fun i => r i = x)
    have hEFx : Fx.card * N ≤ 4 * ∑ i ∈ Fx, rowErr H K i := by
      rw [hK_eq]
      exact fiber_err_bound hN hH x Fx rfl h
    have hdisj : Disjoint F Fx := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [F, Fx, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
      exact hne (hi2.symm.trans hi1)
    have hsum_le : ∑ i ∈ F, rowErr H K i + ∑ i ∈ Fx, rowErr H K i ≤ errors H K := by
      rw [← Finset.sum_union hdisj]
      exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    have : 4 * N ≤ (F.card + Fx.card) * N := by
      apply Nat.mul_le_mul_right N; omega
    rw [add_mul] at this
    omega
  have hr_inj_compl : Set.InjOn r (Fᶜ : Finset (Fin N)) := by
    intro i hi j hj hij
    by_contra hne
    have hri : r i ≠ x₀ := by
      simp only [Finset.mem_coe, Finset.mem_compl, F, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact hi
    have hcard1 := huniq_rep (r i) hri
    have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ.filter (fun t => r t = r i) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases ht with rfl | rfl
      · rfl
      · exact hij.symm
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at this
    omega
  set U : Finset (Fin N) := Fᶜ.filter (fun i => rowErr H K i = 0)
  set Csing : Finset (Fin N) := Fᶜ.filter (fun i => rowErr H K i ≠ 0)
  set p := F.card
  set k := Csing.card
  have hUC_disj : Disjoint U Csing := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [U, Csing, Finset.mem_filter] at hi1 hi2
    exact hi2.2 hi1.2
  have hUC_union : U ∪ Csing = Fᶜ := by
    ext i
    simp only [U, Csing, Finset.mem_union, Finset.mem_filter]
    tauto
  have hU_card : U.card + k + p = N := by
    have h1 : U.card + k = Fᶜ.card := by
      rw [← Finset.card_union_of_disjoint hUC_disj, hUC_union]
    have h2 : Fᶜ.card + p = N := by
      simpa [p] using Finset.card_compl_add_card F
    omega
  set rU : Finset (Fin N) := U.image r
  have hrU_card : rU.card = U.card := by
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    apply hr_inj_compl
    · exact (Finset.mem_filter.mp hi).1
    · exact (Finset.mem_filter.mp hj).1
    · exact hij
  set B' : Finset (Fin N) := rUᶜ
  have hB'_card : B'.card = k + p := by
    have h1 : B'.card + rU.card = N := by simpa [B'] using Finset.card_compl_add_card rU
    omega
  have hU_eq_HK : ∀ j ∈ U, ∀ t : Fin N, H j t = K j t := by
    intro j hj t
    have h0 : rowErr H K j = 0 := (Finset.mem_filter.mp hj).2
    unfold rowErr at h0
    rw [Finset.card_eq_zero] at h0
    by_contra hne
    have : t ∈ Finset.univ.filter (fun s => H j s ≠ K j s) := by simp [hne]
    rw [h0] at this
    exact Finset.notMem_empty t this
  have horth_rU : ∀ i ∈ Uᶜ, ∀ z ∈ rU, ∑ t : Fin N, sgn (H i t) * sgn (D' z t) = 0 := by
    intro i hi z hz
    rcases Finset.mem_image.mp hz with ⟨j, hjU, rfl⟩
    have hij : i ≠ j := by
      intro heq; subst heq
      exact (Finset.mem_compl.mp hi) hjU
    have hHj : ∀ t, sgn (D' (r j) t) = sgn (u j) * sgn (H j t) := by
      intro t
      rw [hU_eq_HK j hjU t, hK_eq]
      simp only [sgn_xor]
      have := sgn_sq (u j)
      linear_combination -(sgn (D' (r j) t)) * this
    simp_rw [hHj]
    have hpull : ∑ t : Fin N, sgn (H i t) * (sgn (u j) * sgn (H j t)) =
        sgn (u j) * ∑ t : Fin N, sgn (H i t) * sgn (H j t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro t _; ring
    rw [hpull, (had_iff_orth H).mp hH i j, if_neg hij, mul_zero]
  have hsing_lb : ∀ i ∈ Csing, N ≤ (k + p) * rowErr H K i := by
    intro i hiC
    have hiFc : i ∈ Fᶜ := (Finset.mem_filter.mp hiC).1
    have hmi_pos : 0 < rowErr H K i := Nat.pos_of_ne_zero (Finset.mem_filter.mp hiC).2
    have hiUc : i ∈ Uᶜ := by
      rw [Finset.mem_compl]
      intro hiU
      exact (Finset.mem_filter.mp hiC).2 (Finset.mem_filter.mp hiU).2
    have hri_B' : r i ∈ B' := by
      rw [Finset.mem_compl]
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨j, hjU, hrj⟩
      have hij : j = i := hr_inj_compl (Finset.mem_filter.mp hjU).1 hiFc hrj
      subst hij
      exact (Finset.mem_compl.mp hiUc) hjU
    have hpars := parseval_rows (by omega) hD' (fun t => sgn (H i t)) (fun t => sgn_sq _)
    have hsumB' : ∑ y ∈ B', (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2 = (N : ℝ) ^ 2 := by
      have hsplit := Finset.sum_add_sum_compl rU
        (fun y => (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2)
      have hzero : ∑ y ∈ rU, (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2 = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        rw [horth_rU i hiUc y hy, sq, zero_mul]
      linarith
    have hdiag : (∑ t : Fin N, sgn (H i t) * sgn (D' (r i) t)) ^ 2 =
        ((N : ℝ) - 2 * (rowErr H K i : ℝ)) ^ 2 := by
      have h1 : ∀ t : Fin N, sgn (H i t) * sgn (D' (r i) t) =
          sgn (u i) * (sgn (H i t) * sgn (K i t)) := by
        intro t
        rw [hK_eq]
        simp only [sgn_xor]
        have := sgn_sq (u i)
        linear_combination -(sgn (H i t) * sgn (D' (r i) t)) * this
      simp_rw [h1, ← Finset.mul_sum, mul_pow]
      have hsq : sgn (u i) ^ 2 = 1 := by rw [sq, sgn_sq]
      rw [hsq, one_mul, sum_sgn_mul_rows H K i i]
      rfl
    have hrest : ∑ y ∈ B'.erase (r i), (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2 =
        4 * (rowErr H K i : ℝ) * ((N : ℝ) - (rowErr H K i : ℝ)) := by
      have hsp := Finset.add_sum_erase B'
        (fun y => (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2) hri_B'
      rw [hdiag] at hsp
      linarith
    have hterm_le : ∀ y ∈ B'.erase (r i),
        (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2 ≤ 4 * (rowErr H K i : ℝ) ^ 2 := by
      intro y hy
      have hne_y : r i ≠ y := (Finset.ne_of_mem_erase hy).symm
      have horth_y : ∑ t : Fin N, sgn (K i t) * sgn (D' y t) = 0 := by
        have h1 : ∀ t : Fin N, sgn (K i t) * sgn (D' y t) =
            sgn (u i) * (sgn (D' (r i) t) * sgn (D' y t)) := by
          intro t; rw [hK_eq]; simp only [sgn_xor]; ring
        simp_rw [h1, ← Finset.mul_sum, (had_iff_orth D').mp hD' (r i) y, if_neg hne_y, mul_zero]
      have heq : ∑ t : Fin N, sgn (H i t) * sgn (D' y t) =
          ∑ t : Fin N, (sgn (H i t) - sgn (K i t)) * sgn (D' y t) := by
        have hsub : ∑ t : Fin N, (sgn (H i t) - sgn (K i t)) * sgn (D' y t) =
            (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) - (∑ t : Fin N, sgn (K i t) * sgn (D' y t)) := by
          rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro t _; ring
        linarith
      have habs : |∑ t : Fin N, sgn (H i t) * sgn (D' y t)| ≤ 2 * (rowErr H K i : ℝ) := by
        rw [heq]
        exact inner_bound_diff H K i (fun t => sgn (D' y t)) (fun t => sgn_abs _)
      have hsq : (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2 ≤ (2 * (rowErr H K i : ℝ)) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      linarith
    have hsum_le : ∑ y ∈ B'.erase (r i), (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2 ≤
        ((k + p - 1 : ℕ) : ℝ) * (4 * (rowErr H K i : ℝ) ^ 2) := by
      calc ∑ y ∈ B'.erase (r i), (∑ t : Fin N, sgn (H i t) * sgn (D' y t)) ^ 2
          ≤ ∑ _y ∈ B'.erase (r i), (4 * (rowErr H K i : ℝ) ^ 2) := Finset.sum_le_sum hterm_le
        _ = ((B'.erase (r i)).card : ℝ) * (4 * (rowErr H K i : ℝ) ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((k + p - 1 : ℕ) : ℝ) * (4 * (rowErr H K i : ℝ) ^ 2) := by
            rw [Finset.card_erase_of_mem hri_B', hB'_card]
    have hmi_r : (0 : ℝ) < (rowErr H K i : ℝ) := by exact_mod_cast hmi_pos
    have hkp_ge1 : 1 ≤ k + p := by omega
    have hkp_cast : ((k + p - 1 : ℕ) : ℝ) + 1 = ((k + p : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hkp_ge1
    have hreal : (N : ℝ) ≤ ((k + p : ℕ) : ℝ) * (rowErr H K i : ℝ) := by
      nlinarith
    exact_mod_cast hreal
  have hEsing : k * N ≤ (k + p) * ∑ i ∈ Csing, rowErr H K i := by
    calc k * N = ∑ _i ∈ Csing, N := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ i ∈ Csing, (k + p) * rowErr H K i := Finset.sum_le_sum hsing_lb
      _ = (k + p) * ∑ i ∈ Csing, rowErr H K i := by rw [← Finset.mul_sum]
  have hFC_disj : Disjoint F Csing := by
    rw [Finset.disjoint_left]
    intro i hiF hiC
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hiC).1) hiF
  have hFC_le : ∑ i ∈ F, rowErr H K i + ∑ i ∈ Csing, rowErr H K i ≤ errors H K := by
    rw [← Finset.sum_union hFC_disj]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hkp_le3 : k + p ≤ 3 := by
    by_contra h
    push_neg at h
    have hcomb : (p * (k + p) + 4 * k) * N ≤ 4 * (k + p) * errors H K := by
      have h1 : (k + p) * (p * N) ≤ (k + p) * (4 * ∑ i ∈ F, rowErr H K i) :=
        Nat.mul_le_mul_left (k + p) hEF
      have h2 : 4 * (k * N) ≤ 4 * ((k + p) * ∑ i ∈ Csing, rowErr H K i) :=
        Nat.mul_le_mul_left 4 hEsing
      have h3 : 4 * (k + p) * (∑ i ∈ F, rowErr H K i + ∑ i ∈ Csing, rowErr H K i) ≤
          4 * (k + p) * errors H K := Nat.mul_le_mul_left _ hFC_le
      nlinarith
    have hcoeff : 4 * (k + p) ≤ p * (k + p) + 4 * k := by
      have hp2 : 2 ≤ p := hx₀_card
      have hp3 : p ≤ 3 := hp_le3
      interval_cases p <;> omega
    have h4 : 4 * (k + p) * N ≤ (p * (k + p) + 4 * k) * N := Nat.mul_le_mul_right N hcoeff
    have hlt : 4 * (k + p) * errors H K < 4 * (k + p) * N := by
      apply Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    omega
  have hspan_all : ∀ i ∈ Uᶜ, ∀ t : Fin N,
      sgn (H i t) = ∑ y ∈ B', ((∑ s : Fin N, sgn (H i s) * sgn (D' y s)) / (N : ℝ)) * sgn (D' y t) := by
    intro i hi t
    have hNpos : (N : ℝ) ≠ 0 := by positivity
    have hfull : ∑ y : Fin N, (∑ s : Fin N, sgn (H i s) * sgn (D' y s)) * sgn (D' y t) =
        (N : ℝ) * sgn (H i t) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      have h1 : ∀ s : Fin N, ∑ y : Fin N, sgn (H i s) * sgn (D' y s) * sgn (D' y t) =
          if s = t then (N : ℝ) * sgn (H i t) else 0 := by
        intro s
        have h2 : ∑ y : Fin N, sgn (H i s) * sgn (D' y s) * sgn (D' y t) =
            sgn (H i s) * ∑ y : Fin N, sgn (D' y s) * sgn (D' y t) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro y _; ring
        rw [h2, had_col_sum (by omega) hD' s t]
        split_ifs with hst
        · subst hst; ring
        · simp
      simp_rw [h1]
      simp
    have hsplit := Finset.sum_add_sum_compl rU
      (fun y => (∑ s : Fin N, sgn (H i s) * sgn (D' y s)) * sgn (D' y t))
    have hzero : ∑ y ∈ rU, (∑ s : Fin N, sgn (H i s) * sgn (D' y s)) * sgn (D' y t) = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      rw [horth_rU i hi y hy, zero_mul]
    have hB'sum : ∑ y ∈ B', (∑ s : Fin N, sgn (H i s) * sgn (D' y s)) * sgn (D' y t) =
        (N : ℝ) * sgn (H i t) := by linarith
    calc sgn (H i t) = ((N : ℝ) * sgn (H i t)) / (N : ℝ) := by field_simp [hNpos]
      _ = (∑ y ∈ B', (∑ s : Fin N, sgn (H i s) * sgn (D' y s)) * sgn (D' y t)) / (N : ℝ) := by
          rw [hB'sum]
      _ = ∑ y ∈ B', ((∑ s : Fin N, sgn (H i s) * sgn (D' y s)) / (N : ℝ)) * sgn (D' y t) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl; intro y _; ring
  have hrow_D' : ∀ i : Fin N, ∃ y : Fin N, ∃ s : Bool, ∀ t : Fin N, H i t = xor s (D' y t) := by
    intro i
    by_cases hiU : i ∈ U
    · refine ⟨r i, u i, fun t => ?_⟩
      rw [hU_eq_HK i hiU t, hK_eq]
    · have hiUc : i ∈ Uᶜ := Finset.mem_compl.mpr hiU
      have hB'23 : B'.card = 2 ∨ B'.card = 3 := by omega
      rcases hB'23 with h2 | h3
      · rcases Finset.card_eq_two.mp h2 with ⟨y₁, y₂, h12, hB'eq⟩
        let c₁ := (∑ s : Fin N, sgn (H i s) * sgn (D' y₁ s)) / (N : ℝ)
        let c₂ := (∑ s : Fin N, sgn (H i s) * sgn (D' y₂ s)) / (N : ℝ)
        have hsp : ∀ t, sgn (H i t) = c₁ * sgn (D' y₁ t) + c₂ * sgn (D' y₂ t) := by
          intro t
          have := hspan_all i hiUc t
          rw [hB'eq, Finset.sum_pair h12] at this
          exact this
        have hres := span_two_pm (by omega)
          (fun t => sgn (D' y₁ t)) (fun t => sgn (D' y₂ t)) (fun t => sgn (H i t))
          (fun t => sgn_sq _) (fun t => sgn_sq _) (fun t => sgn_sq _)
          (by simpa [h12] using (had_iff_orth D').mp hD' y₁ y₂) c₁ c₂ hsp
        rcases hres with h | h | h | h
        · exact ⟨y₁, false, fun t => by simpa using (sgn_eq_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₁, true, fun t => (sgn_eq_neg_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₂, false, fun t => by simpa using (sgn_eq_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₂, true, fun t => (sgn_eq_neg_iff_bool _ _).mp (h t)⟩
      · rcases Finset.card_eq_three.mp h3 with ⟨y₁, y₂, y₃, h12, h13, h23, hB'eq⟩
        let c₁ := (∑ s : Fin N, sgn (H i s) * sgn (D' y₁ s)) / (N : ℝ)
        let c₂ := (∑ s : Fin N, sgn (H i s) * sgn (D' y₂ s)) / (N : ℝ)
        let c₃ := (∑ s : Fin N, sgn (H i s) * sgn (D' y₃ s)) / (N : ℝ)
        have hsp : ∀ t, sgn (H i t) = c₁ * sgn (D' y₁ t) + c₂ * sgn (D' y₂ t) + c₃ * sgn (D' y₃ t) := by
          intro t
          have := hspan_all i hiUc t
          rw [hB'eq, Finset.sum_insert (by simp [h12, h13]), Finset.sum_pair h23] at this
          linarith
        have hres := span_three_pm (by omega)
          (fun t => sgn (D' y₁ t)) (fun t => sgn (D' y₂ t)) (fun t => sgn (D' y₃ t))
          (fun t => sgn (H i t))
          (fun t => sgn_sq _) (fun t => sgn_sq _) (fun t => sgn_sq _) (fun t => sgn_sq _)
          (by simpa [h12] using (had_iff_orth D').mp hD' y₁ y₂)
          (by simpa [h13] using (had_iff_orth D').mp hD' y₁ y₃)
          (by simpa [h23] using (had_iff_orth D').mp hD' y₂ y₃)
          c₁ c₂ c₃ hsp
        rcases hres with h | h | h | h | h | h
        · exact ⟨y₁, false, fun t => by simpa using (sgn_eq_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₁, true, fun t => (sgn_eq_neg_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₂, false, fun t => by simpa using (sgn_eq_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₂, true, fun t => (sgn_eq_neg_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₃, false, fun t => by simpa using (sgn_eq_iff_bool _ _).mp (h t)⟩
        · exact ⟨y₃, true, fun t => (sgn_eq_neg_iff_bool _ _).mp (h t)⟩
  choose f a hfa using hrow_D'
  have hf_inj : Function.Injective f := by
    intro i₁ i₂ hfeq
    by_contra hne
    have hd := hH i₁ i₂ hne
    by_cases ha : a i₁ = a i₂
    · have h0 : ((Finset.univ : Finset (Fin N)).filter (fun j => H i₁ j ≠ H i₂ j)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        simp [hfa i₁ j, hfa i₂ j, hfeq, ha]
      omega
    · have hNcard : ((Finset.univ : Finset (Fin N)).filter (fun j => H i₁ j ≠ H i₂ j)).card = N := by
        have h1 : ∀ j : Fin N, H i₁ j ≠ H i₂ j := by
          intro j
          rw [hfa i₁ j, hfa i₂ j, hfeq]
          cases ha1 : a i₁ <;> cases ha2 : a i₂ <;> cases D' (f i₂) j <;> simp_all
        simp [h1]
      omega
  let fPerm : Equiv.Perm (Fin N) := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf_inj)
  have hH_sample : H = sample D fPerm cPerm a v := by
    funext i j
    simp only [sample, fPerm, cPerm, Equiv.ofBijective_apply]
    rw [hfa i j]
    simp only [D']
    cases a i <;> cases v j <;> cases D (f i) (c j) <;> rfl
  have hrow_cases : ∀ i : Fin N,
      (r i ≠ f i → 2 * rowErr H K i = N) ∧
      (r i = f i → rowErr H K i = 0 ∨ rowErr H K i = N) := by
    intro i
    constructor
    · intro hne
      have h1 : ∀ j : Fin N, (H i j ≠ K i j) ↔ (D' (f i) j ≠ xor (xor (a i) (u i)) (D' (r i) j)) := by
        intro j
        rw [hfa i j, hK_eq]
        dsimp only
        cases a i <;> cases u i <;> cases D' (f i) j <;> cases D' (r i) j <;> decide
      unfold rowErr
      simp_rw [h1]
      exact filter_xor_card hD' hne.symm (xor (a i) (u i))
    · intro heq
      by_cases hau : a i = u i
      · left
        unfold rowErr
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro j _
        simp [hfa i j, hK_eq, heq, hau]
      · right
        unfold rowErr
        have h1 : ∀ j : Fin N, H i j ≠ K i j := by
          intro j
          rw [hfa i j, hK_eq]
          dsimp only
          rw [heq]
          cases ha1 : a i <;> cases hu1 : u i <;> cases D' (f i) j <;> simp_all
        simp [h1]
  have hnoN : ∀ i : Fin N, rowErr H K i ≠ N := by
    intro i hi
    have hle : rowErr H K i ≤ errors H K :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hex_diff : ∃ i₀ : Fin N, r i₀ ≠ f i₀ := by
    by_contra h
    push_neg at h
    apply hr
    intro i₁ i₂ heq
    exact hf_inj (by rw [← h i₁, ← h i₂, heq])
  rcases hex_diff with ⟨i₀, hi₀_diff⟩
  have hmi₀ : 2 * rowErr H K i₀ = N := (hrow_cases i₀).1 hi₀_diff
  have hrest_zero : ∀ i : Fin N, i ≠ i₀ → rowErr H K i = 0 ∧ r i = f i := by
    intro i hi
    have hsum2 : rowErr H K i₀ + rowErr H K i ≤ errors H K := by
      unfold errors
      have hsub : ({i₀, i} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := rowErr H K) hsub (fun _ _ _ => Nat.zero_le _)
      rwa [Finset.sum_pair hi.symm] at this
    by_cases hrf : r i = f i
    · rcases (hrow_cases i).2 hrf with h0 | hN'
      · exact ⟨h0, hrf⟩
      · exact absurd hN' (hnoN i)
    · have hmi := (hrow_cases i).1 hrf
      omega
  have herr_half : 2 * errors H K = N := by
    have hsum : errors H K = rowErr H K i₀ := by
      unfold errors
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
      have hz : ∑ i ∈ Finset.univ.erase i₀, rowErr H K i = 0 :=
        Finset.sum_eq_zero (fun i hi => (hrest_zero i (Finset.ne_of_mem_erase hi)).1)
      omega
    omega
  let j₀ : Fin N := fPerm.symm (r i₀)
  have hfj₀ : f j₀ = r i₀ := by
    have h1 : fPerm j₀ = r i₀ := fPerm.apply_symm_apply (r i₀)
    simpa [fPerm] using h1
  have hj₀_ne : i₀ ≠ j₀ := by
    intro heq
    exact hi₀_diff (by rw [← hfj₀, ← heq])
  have hrj₀ : r j₀ = r i₀ := by
    rw [(hrest_zero j₀ hj₀_ne.symm).2, hfj₀]
  have hclone : clone H K := by
    refine ⟨i₀, j₀, hj₀_ne, xor (u i₀) (u j₀), fun x y => ?_⟩
    by_cases hx : x = i₀
    · subst hx
      have hKj₀ : K j₀ y = H j₀ y := by
        have h0 := (hrest_zero j₀ hj₀_ne.symm).1
        unfold rowErr at h0
        rw [Finset.card_eq_zero] at h0
        by_contra hne
        have : y ∈ Finset.univ.filter (fun s => H j₀ s ≠ K j₀ s) := by
          simp [Ne.symm hne]
        rw [h0] at this
        exact Finset.notMem_empty y this
      rw [if_pos rfl, ← hKj₀, hK_eq]
      dsimp only
      rw [hrj₀]
      cases u x <;> cases u j₀ <;> cases D' (r x) y <;> rfl
    · rw [if_neg hx]
      have h0 := (hrest_zero x hx).1
      unfold rowErr at h0
      rw [Finset.card_eq_zero] at h0
      by_contra hne
      have : y ∈ Finset.univ.filter (fun s => H x s ≠ K x s) := by
        simp [Ne.symm hne]
      rw [h0] at this
      exact Finset.notMem_empty y this
  exact ⟨⟨fPerm, cPerm, a, v, hH_sample⟩, herr_half, hclone⟩

lemma attainment {N : ℕ} (hN : 8 ≤ N) {H : Tab N} (hH : had H) :
    ∃ (r c : Fin N → Fin N) (u v : Fin N → Bool),
      ¬ Function.Injective r ∧ ¬ Function.Injective c ∧
      errors H (sample H r c u v) + 2 = N := by
  let i₀ : Fin N := ⟨0, by omega⟩
  let i₁ : Fin N := ⟨1, by omega⟩
  have hi_ne : i₀ ≠ i₁ := by simp [i₀, i₁]
  set S : Finset (Fin N) := Finset.univ.filter (fun j => H i₀ j = H i₁ j)
  have hScard : 2 * S.card = N := by
    have hd := hH i₀ i₁ hi_ne
    have hcomp := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
      (p := fun j => H i₀ j = H i₁ j)
    simp only [Finset.card_univ, Fintype.card_fin] at hcomp
    change S.card + (Finset.univ.filter (fun j => H i₀ j ≠ H i₁ j)).card = N at hcomp
    omega
  have hS_gt1 : 1 < S.card := by omega
  rcases Finset.one_lt_card.mp hS_gt1 with ⟨j₀, hj₀, j₁, hj₁, hj_ne⟩
  have hH0 : H i₀ j₀ = H i₁ j₀ := (Finset.mem_filter.mp hj₀).2
  have hH1 : H i₀ j₁ = H i₁ j₁ := (Finset.mem_filter.mp hj₁).2
  let r : Fin N → Fin N := fun x => if x = i₀ then i₁ else x
  let c : Fin N → Fin N := fun y => if y = j₀ then j₁ else y
  let u : Fin N → Bool := fun x => decide (x = i₀)
  let β : Bool := decide (H i₀ j₀ = H i₀ j₁)
  let v : Fin N → Bool := fun y => if y = j₀ then β else false
  have hr_noninj : ¬ Function.Injective r := by
    intro hinj
    have : r i₀ = r i₁ := by simp [r, hi_ne.symm]
    exact hi_ne (hinj this)
  have hc_noninj : ¬ Function.Injective c := by
    intro hinj
    have : c j₀ = c j₁ := by simp [c, hj_ne.symm]
    exact hj_ne (hinj this)
  set K := sample H r c u v
  have hK_corner : K i₀ j₀ = H i₀ j₀ := by
    simp only [K, sample, r, c, u, v, β, ↓reduceIte, decide_true]
    rw [← hH1]
    cases H i₀ j₀ <;> cases H i₀ j₁ <;> rfl
  have hK_row : ∀ y : Fin N, y ≠ j₀ → K i₀ y = xor true (H i₁ y) := by
    intro y hy
    simp only [K, sample, r, c, u, v, ↓reduceIte, if_neg hy, decide_true]
    cases H i₁ y <;> rfl
  have hK_col : ∀ x : Fin N, x ≠ i₀ → K x j₀ = xor β (H x j₁) := by
    intro x hx
    simp only [K, sample, r, c, u, v, if_neg hx, ↓reduceIte, decide_eq_false hx]
    cases β <;> cases H x j₁ <;> rfl
  have hK_other : ∀ x y : Fin N, x ≠ i₀ → y ≠ j₀ → K x y = H x y := by
    intro x y hx hy
    simp only [K, sample, r, c, u, v, if_neg hx, if_neg hy, decide_eq_false hx]
    cases H x y <;> rfl
  have hrow_i0 : 2 * (rowErr H K i₀ + 1) = N := by
    have hfull := filter_xor_card hH hi_ne true
    have hmem : j₀ ∈ Finset.univ.filter (fun y => H i₀ y ≠ xor true (H i₁ y)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hH0]
      cases H i₁ j₀ <;> decide
    have heq_set : Finset.univ.filter (fun y => H i₀ y ≠ K i₀ y) =
        (Finset.univ.filter (fun y => H i₀ y ≠ xor true (H i₁ y))).erase j₀ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hy : y = j₀
      · subst hy; simp [hK_corner]
      · simp [hy, hK_row y hy]
    unfold rowErr
    rw [heq_set, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ (Finset.univ.filter (fun y => H i₀ y ≠ xor true (H i₁ y))).card :=
      Finset.card_pos.mpr ⟨j₀, hmem⟩
    omega
  have hrest_rows : 2 * (∑ x ∈ Finset.univ.erase i₀, rowErr H K x + 1) = N := by
    have hHsw := had_swap (by omega) hH
    have hfull := filter_xor_card hHsw hj_ne β
    have hmem : i₀ ∈ Finset.univ.filter (fun x => H x j₀ ≠ xor β (H x j₁)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, β]
      cases H i₀ j₀ <;> cases H i₀ j₁ <;> decide
    have hrow_x : ∀ x ∈ Finset.univ.erase i₀,
        rowErr H K x = if H x j₀ ≠ xor β (H x j₁) then 1 else 0 := by
      intro x hx
      have hne : x ≠ i₀ := Finset.ne_of_mem_erase hx
      unfold rowErr
      by_cases hc' : H x j₀ ≠ xor β (H x j₁)
      · rw [if_pos hc']
        have hset : Finset.univ.filter (fun y => H x y ≠ K x y) = {j₀} := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          by_cases hy : y = j₀
          · subst hy; simp [hK_col x hne, hc']
          · simp [hy, hK_other x y hne hy]
        rw [hset, Finset.card_singleton]
      · rw [if_neg hc']
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro y _
        by_cases hy : y = j₀
        · subst hy; rw [hK_col x hne]; exact hc'
        · rw [hK_other x y hne hy]; exact not_not.mpr rfl
    have hsum : ∑ x ∈ Finset.univ.erase i₀, rowErr H K x =
        ((Finset.univ.filter (fun x => H x j₀ ≠ xor β (H x j₁))).erase i₀).card := by
      rw [Finset.sum_congr rfl hrow_x]
      have h1 : ((Finset.univ.filter (fun x => H x j₀ ≠ xor β (H x j₁))).erase i₀) =
          (Finset.univ.erase i₀).filter (fun x => H x j₀ ≠ xor β (H x j₁)) := by
        ext x; simp [and_comm]
      rw [h1, Finset.card_filter]
    rw [hsum, Finset.card_erase_of_mem hmem]
    have hpos : 1 ≤ (Finset.univ.filter (fun x => H x j₀ ≠ xor β (H x j₁))).card :=
      Finset.card_pos.mpr ⟨i₀, hmem⟩
    simpa [Function.swap] using (by omega : 2 * ((Finset.univ.filter (fun x => H x j₀ ≠ xor β (H x j₁))).card - 1 + 1) =
      2 * (Finset.univ.filter (fun x => H x j₀ ≠ xor β (H x j₁))).card).trans hfull
  have herr_total : errors H K + 2 = N := by
    have hsplit : errors H K = rowErr H K i₀ + ∑ x ∈ Finset.univ.erase i₀, rowErr H K x := by
      unfold errors
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
    omega
  exact ⟨r, c, u, v, hr_noninj, hc_noninj, herr_total⟩

end PEqualNP.Outside.L_lib_633_aux

theorem PEqualNP.Outside.L_lib_633 : (∀ N : ℕ, 8 ≤ N →
  let T := Fin N → Fin N → Bool
  let had := fun (M : T) => ∀ a b : Fin N, a ≠ b →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun j => M a j ≠ M b j)).card = N
  let sample := fun (D : T) (r c : Fin N → Fin N) (u v : Fin N → Bool) (i j : Fin N) =>
    xor (xor (u i) (v j)) (D (r i) (c j))
  let clone := fun (A B : T) => ∃ i j : Fin N, i ≠ j ∧ ∃ flip : Bool,
    ∀ x y, B x y = if x = i then xor flip (A j y) else A x y
  let errors := fun (A B : T) =>
    ∑ i : Fin N, ((Finset.univ : Finset (Fin N)).filter (fun j => A i j ≠ B i j)).card
  ∀ H D : T, had H → had D →
    (∀ (r c : Fin N → Fin N) (u v : Fin N → Bool),
      let K := sample D r c u v
      errors H K + 2 < N →
        (∃ (f g : Equiv.Perm (Fin N)) (a b : Fin N → Bool), H = sample D f g a b) ∧
        (errors H K = 0 ∨ (2 * errors H K = N ∧
          (clone H K ∨ clone (Function.swap H) (Function.swap K))))) ∧
    (∃ (r c : Fin N → Fin N) (u v : Fin N → Bool),
      ¬ Function.Injective r ∧ ¬ Function.Injective c ∧ errors H (sample H r c u v) + 2 = N)) := by
  intro N hN T had_l sample_l clone_l errors_l H D hH hD
  have hH' : PEqualNP.Outside.L_lib_633_aux.had H := hH
  have hD' : PEqualNP.Outside.L_lib_633_aux.had D := hD
  constructor
  · intro r c u v K herr
    have herr' : PEqualNP.Outside.L_lib_633_aux.errors H (PEqualNP.Outside.L_lib_633_aux.sample D r c u v) + 2 < N := herr
    by_cases hr : Function.Injective r
    · by_cases hc : Function.Injective c
      · have hKhad := PEqualNP.Outside.L_lib_633_aux.had_sample_bij hD' hr hc u v
        have hzero : PEqualNP.Outside.L_lib_633_aux.errors H (PEqualNP.Outside.L_lib_633_aux.sample D r c u v) = 0 := by
          by_contra hne
          have hge := PEqualNP.Outside.L_lib_633_aux.had_trade_bound (by omega) hH' hKhad hne
          omega
        have hHK : H = PEqualNP.Outside.L_lib_633_aux.sample D r c u v := by
          funext i j
          have hrow : PEqualNP.Outside.L_lib_633_aux.rowErr H (PEqualNP.Outside.L_lib_633_aux.sample D r c u v) i = 0 := by
            have hle : PEqualNP.Outside.L_lib_633_aux.rowErr H (PEqualNP.Outside.L_lib_633_aux.sample D r c u v) i ≤
                PEqualNP.Outside.L_lib_633_aux.errors H (PEqualNP.Outside.L_lib_633_aux.sample D r c u v) :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
            omega
          unfold PEqualNP.Outside.L_lib_633_aux.rowErr at hrow
          rw [Finset.card_eq_zero] at hrow
          by_contra hne
          have : j ∈ Finset.univ.filter (fun t => H i t ≠ PEqualNP.Outside.L_lib_633_aux.sample D r c u v i t) := by
            simp [hne]
          rw [hrow] at this
          exact Finset.notMem_empty j this
        let fPerm : Equiv.Perm (Fin N) := Equiv.ofBijective r ((Finite.injective_iff_bijective).mp hr)
        let gPerm : Equiv.Perm (Fin N) := Equiv.ofBijective c ((Finite.injective_iff_bijective).mp hc)
        exact ⟨⟨fPerm, gPerm, u, v, hHK⟩, Or.inl hzero⟩
      · have hHsw := PEqualNP.Outside.L_lib_633_aux.had_swap (by omega) hH'
        have hDsw := PEqualNP.Outside.L_lib_633_aux.had_swap (by omega) hD'
        have herr_sw : PEqualNP.Outside.L_lib_633_aux.errors (Function.swap H)
            (PEqualNP.Outside.L_lib_633_aux.sample (Function.swap D) c r v u) + 2 < N := by
          rw [← PEqualNP.Outside.L_lib_633_aux.sample_swap, PEqualNP.Outside.L_lib_633_aux.errors_swap]
          exact herr'
        obtain ⟨⟨gPerm, fPerm, b, a, hsw_eq⟩, hhalf, hcl⟩ :=
          PEqualNP.Outside.L_lib_633_aux.case_r_noninj_c_inj hN hHsw hDsw hc hr v u herr_sw
        have hH_eq : H = PEqualNP.Outside.L_lib_633_aux.sample D fPerm gPerm a b := by
          funext i j
          have := congr_fun (congr_fun hsw_eq j) i
          simpa [Function.swap, PEqualNP.Outside.L_lib_633_aux.sample, Bool.xor_comm] using this
        have hhalf' : 2 * PEqualNP.Outside.L_lib_633_aux.errors H (PEqualNP.Outside.L_lib_633_aux.sample D r c u v) = N := by
          rw [← PEqualNP.Outside.L_lib_633_aux.errors_swap, PEqualNP.Outside.L_lib_633_aux.sample_swap]
          exact hhalf
        have hcl' : PEqualNP.Outside.L_lib_633_aux.clone (Function.swap H)
            (Function.swap (PEqualNP.Outside.L_lib_633_aux.sample D r c u v)) := by
          rw [PEqualNP.Outside.L_lib_633_aux.sample_swap]
          exact hcl
        exact ⟨⟨fPerm, gPerm, a, b, hH_eq⟩, Or.inr ⟨hhalf', Or.inr hcl'⟩⟩
    · by_cases hc : Function.Injective c
      · obtain ⟨heq, hhalf, hcl⟩ :=
          PEqualNP.Outside.L_lib_633_aux.case_r_noninj_c_inj hN hH' hD' hr hc u v herr'
        exact ⟨heq, Or.inr ⟨hhalf, Or.inl hcl⟩⟩
      · have hge := @PEqualNP.Outside.L_lib_633_aux.case_both_noninj N hN H D hH' r c hr hc u v
        omega
  · exact PEqualNP.Outside.L_lib_633_aux.attainment hN hH'
