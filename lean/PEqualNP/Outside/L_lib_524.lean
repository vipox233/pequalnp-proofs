import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_524_aux

def bitsOf : ℕ → ℕ → List Bool
  | 0, _ => []
  | l + 1, k => bitsOf l (k / 2) ++ [decide (k % 2 = 1)]

noncomputable def dyadicVal : List Bool → ℝ
  | [] => 0
  | b :: bs => ((if b then (1 : ℝ) else 0) + dyadicVal bs) / 2

theorem bitsOf_length (l k : ℕ) : (bitsOf l k).length = l := by
  induction l generalizing k with
  | zero => rfl
  | succ l ih => simp [bitsOf, ih]

theorem dyadicVal_nonneg (w : List Bool) : 0 ≤ dyadicVal w := by
  induction w with
  | nil => simp [dyadicVal]
  | cons b bs ih =>
    unfold dyadicVal
    cases b <;> simp <;> linarith

theorem dyadicVal_lt_one (w : List Bool) : dyadicVal w < 1 := by
  induction w with
  | nil => simp [dyadicVal]
  | cons b bs ih =>
    unfold dyadicVal
    cases b <;> simp <;> linarith

theorem dyadicVal_append (w₁ w₂ : List Bool) :
    dyadicVal (w₁ ++ w₂) = dyadicVal w₁ + dyadicVal w₂ / (2 : ℝ) ^ w₁.length := by
  induction w₁ with
  | nil => simp [dyadicVal]
  | cons b bs ih =>
    simp only [List.cons_append, dyadicVal, ih, List.length_cons, pow_succ]
    ring

theorem dyadicVal_bitsOf (l k : ℕ) (hk : k < 2 ^ l) :
    dyadicVal (bitsOf l k) = (k : ℝ) / (2 : ℝ) ^ l := by
  induction l generalizing k with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    simp [bitsOf, dyadicVal]
  | succ l ih =>
    unfold bitsOf
    rw [dyadicVal_append, bitsOf_length, ih (k / 2) (by omega)]
    have hrem : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
    have hdiv : (k : ℝ) = 2 * ((k / 2 : ℕ) : ℝ) + ((k % 2 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod k 2).symm
    rcases hrem with h0 | h1
    · simp only [h0, dyadicVal, pow_succ]
      rw [hdiv, h0]
      norm_num
      ring
    · simp only [h1, dyadicVal, pow_succ]
      rw [hdiv, h1]
      norm_num
      ring

theorem lex_of_dyadicVal_le (w₁ w₂ : List Bool)
    (h : dyadicVal w₁ + 1 / (2 : ℝ) ^ w₁.length ≤ dyadicVal w₂) :
    List.Lex (fun a b : Bool => a = false ∧ b = true) w₁ w₂ := by
  induction w₁ generalizing w₂ with
  | nil =>
    simp only [dyadicVal, List.length_nil, pow_zero, div_one, zero_add] at h
    linarith [dyadicVal_lt_one w₂]
  | cons b₁ r₁ ih =>
    cases w₂ with
    | nil =>
      have h0 : dyadicVal [] = 0 := rfl
      rw [h0] at h
      have h1 : 0 ≤ dyadicVal (b₁ :: r₁) := dyadicVal_nonneg _
      have h2 : (0 : ℝ) < 1 / (2 : ℝ) ^ (b₁ :: r₁).length := by positivity
      linarith
    | cons b₂ r₂ =>
      cases b₁ <;> cases b₂
      · apply List.Lex.cons
        apply ih r₂
        simp only [dyadicVal, Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons, pow_succ] at h
        rw [show (1 : ℝ) / ((2 : ℝ) ^ r₁.length * 2) = (1 / (2 : ℝ) ^ r₁.length) / 2 by ring] at h
        linarith
      · exact List.Lex.rel ⟨rfl, rfl⟩
      · exfalso
        simp only [dyadicVal, Bool.false_eq_true, ↓reduceIte, zero_add] at h
        have h1 : 0 ≤ dyadicVal r₁ := dyadicVal_nonneg r₁
        have h2 : dyadicVal r₂ < 1 := dyadicVal_lt_one r₂
        have h3 : (0 : ℝ) < 1 / (2 : ℝ) ^ (true :: r₁).length := by positivity
        linarith
      · apply List.Lex.cons
        apply ih r₂
        simp only [dyadicVal, ↓reduceIte, List.length_cons, pow_succ] at h
        rw [show (1 : ℝ) / ((2 : ℝ) ^ r₁.length * 2) = (1 / (2 : ℝ) ^ r₁.length) / 2 by ring] at h
        linarith

theorem main (m : ℕ) (p : Fin m → ℝ) (hp : ∀ i, 0 < p i) (hsum : (∑ i, p i) = 1) :
    ∃ code : Fin m → List Bool,
      (∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j) ∧
      (∀ i j, i < j → List.Lex (fun a b : Bool => a = false ∧ b = true) (code i) (code j)) ∧
      ∀ i, ((code i).length : ℝ) < -Real.log (p i) / Real.log 2 + 2 := by
  let F : Fin m → ℝ := fun i => ∑ j ∈ Finset.univ.filter (· < i), p j
  let mid : Fin m → ℝ := fun i => F i + p i / 2
  have hF_nonneg : ∀ i, 0 ≤ F i := fun i => Finset.sum_nonneg (fun j _ => le_of_lt (hp j))
  have hF_add_le : ∀ i, F i + p i ≤ 1 := by
    intro i
    have hsub : insert i (Finset.univ.filter (· < i)) ⊆ Finset.univ := Finset.subset_univ _
    have hnotmem : i ∉ Finset.univ.filter (· < i) := by simp
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => le_of_lt (hp j))
    rw [Finset.sum_insert hnotmem, hsum] at hle
    dsimp only [F]
    linarith
  have hF_mono : ∀ i j, i < j → F i + p i ≤ F j := by
    intro i j hij
    have hsub : insert i (Finset.univ.filter (· < i)) ⊆ Finset.univ.filter (· < j) := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      rcases hr with rfl | hlt
      · exact hij
      · exact lt_trans hlt hij
    have hnotmem : i ∉ Finset.univ.filter (· < i) := by simp
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => le_of_lt (hp r))
    rw [Finset.sum_insert hnotmem] at hle
    dsimp only [F]
    linarith
  have hp_le_one : ∀ i, p i ≤ 1 := by
    intro i
    linarith [hF_nonneg i, hF_add_le i]
  have hmid_pos : ∀ i, 0 < mid i := fun i => by dsimp only [mid]; linarith [hF_nonneg i, hp i]
  have hmid_lt_one : ∀ i, mid i < 1 := fun i => by dsimp only [mid]; linarith [hF_add_le i, hp i]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let L : Fin m → ℕ := fun i => Nat.ceil (-Real.log (p i) / Real.log 2 + 1)
  have hL_lt : ∀ i, (L i : ℝ) < -Real.log (p i) / Real.log 2 + 2 := by
    intro i
    have hy_nonneg : 0 ≤ -Real.log (p i) / Real.log 2 + 1 := by
      have hlp : Real.log (p i) ≤ 0 := Real.log_nonpos (le_of_lt (hp i)) (hp_le_one i)
      have hdiv : 0 ≤ -Real.log (p i) / Real.log 2 := div_nonneg (by linarith) (le_of_lt hlog2)
      linarith
    have hcl := Nat.ceil_lt_add_one hy_nonneg
    dsimp only [L]
    linarith
  have hL_pow : ∀ i, (1 : ℝ) / (2 : ℝ) ^ (L i) ≤ p i / 2 := by
    intro i
    have hce : -Real.log (p i) / Real.log 2 + 1 ≤ (L i : ℝ) := Nat.le_ceil _
    have hmul : -Real.log (p i) + Real.log 2 ≤ (L i : ℝ) * Real.log 2 := by
      have h1 := mul_le_mul_of_nonneg_right hce (le_of_lt hlog2)
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hlog2), one_mul] at h1
      exact h1
    have hexp := Real.exp_le_exp.mpr hmul
    have hlhs : Real.exp (-Real.log (p i) + Real.log 2) = 2 / p i := by
      rw [Real.exp_add, Real.exp_neg, Real.exp_log (hp i), Real.exp_log (by norm_num)]
      ring
    have hrhs : Real.exp ((L i : ℝ) * Real.log 2) = (2 : ℝ) ^ (L i) := by
      rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
    rw [hlhs, hrhs] at hexp
    have h2p : (0 : ℝ) < (2 : ℝ) ^ (L i) := by positivity
    rw [div_le_div_iff₀ h2p (by norm_num : (0 : ℝ) < 2)]
    have hmul2 := mul_le_mul_of_nonneg_left hexp (le_of_lt (hp i))
    rw [mul_div_cancel₀ _ (ne_of_gt (hp i))] at hmul2
    linarith
  let k : Fin m → ℕ := fun i => Nat.floor (mid i * (2 : ℝ) ^ (L i))
  have hk_lt : ∀ i, k i < 2 ^ (L i) := by
    intro i
    have hprod : mid i * (2 : ℝ) ^ (L i) < ((2 ^ (L i) : ℕ) : ℝ) := by
      push_cast
      have h2p : (0 : ℝ) < (2 : ℝ) ^ (L i) := by positivity
      nlinarith [hmid_lt_one i]
    exact (Nat.floor_lt (mul_nonneg (le_of_lt (hmid_pos i)) (by positivity))).mpr hprod
  let code : Fin m → List Bool := fun i => bitsOf (L i) (k i)
  have hlen : ∀ i, (code i).length = L i := fun i => bitsOf_length (L i) (k i)
  have hdval : ∀ i, dyadicVal (code i) = (k i : ℝ) / (2 : ℝ) ^ (L i) :=
    fun i => dyadicVal_bitsOf (L i) (k i) (hk_lt i)
  have hinterval : ∀ i, F i < dyadicVal (code i) ∧
      dyadicVal (code i) + 1 / (2 : ℝ) ^ (code i).length ≤ F i + p i := by
    intro i
    have h2p : (0 : ℝ) < (2 : ℝ) ^ (L i) := by positivity
    have hfl1 : (k i : ℝ) ≤ mid i * (2 : ℝ) ^ (L i) :=
      Nat.floor_le (mul_nonneg (le_of_lt (hmid_pos i)) (by positivity))
    have hfl2 : mid i * (2 : ℝ) ^ (L i) < (k i : ℝ) + 1 := Nat.lt_floor_add_one _
    have ha_le : dyadicVal (code i) ≤ mid i := by
      rw [hdval i, div_le_iff₀ h2p]
      exact hfl1
    have hmid_lt_b : mid i < dyadicVal (code i) + 1 / (2 : ℝ) ^ (L i) := by
      rw [hdval i, ← add_div, lt_div_iff₀ h2p]
      exact hfl2
    rw [hlen i]
    constructor
    · dsimp only [mid] at hmid_lt_b
      linarith [hL_pow i]
    · dsimp only [mid] at ha_le
      linarith [hL_pow i]
  have hsep : ∀ i j, i < j → dyadicVal (code i) + 1 / (2 : ℝ) ^ (code i).length < dyadicVal (code j) := by
    intro i j hij
    have hi := (hinterval i).2
    have hj := (hinterval j).1
    have hm := hF_mono i j hij
    linarith
  refine ⟨code, ?_, ?_, ?_⟩
  · intro i j ⟨tail, htail⟩
    have hdv : dyadicVal (code j) = dyadicVal (code i) + dyadicVal tail / (2 : ℝ) ^ (code i).length := by
      rw [htail, dyadicVal_append]
    have hge : dyadicVal (code i) ≤ dyadicVal (code j) := by
      rw [hdv]
      have : 0 ≤ dyadicVal tail / (2 : ℝ) ^ (code i).length :=
        div_nonneg (dyadicVal_nonneg tail) (by positivity)
      linarith
    have hlt : dyadicVal (code j) < dyadicVal (code i) + 1 / (2 : ℝ) ^ (code i).length := by
      rw [hdv]
      have : dyadicVal tail / (2 : ℝ) ^ (code i).length < 1 / (2 : ℝ) ^ (code i).length :=
        div_lt_div_of_pos_right (dyadicVal_lt_one tail) (by positivity)
      linarith
    rcases lt_trichotomy i j with hij | rfl | hji
    · linarith [hsep i j hij]
    · rfl
    · have h2p : (0 : ℝ) < 1 / (2 : ℝ) ^ (code j).length := by positivity
      linarith [hsep j i hji]
  · intro i j hij
    exact lex_of_dyadicVal_le (code i) (code j) (le_of_lt (hsep i j hij))
  · intro i
    rw [hlen i]
    exact hL_lt i

end PEqualNP.Outside.L_lib_524_aux

theorem PEqualNP.Outside.L_lib_524 : (∀ (m : ℕ) (p : Fin m → ℝ),
  (∀ i, 0 < p i) → (∑ i, p i) = 1 →
  let prefixCode := fun (code : Fin m → List Bool) =>
    ∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j
  ∃ code, prefixCode code ∧
    (∀ i j, i < j → List.Lex (fun a b : Bool => a = false ∧ b = true) (code i) (code j)) ∧
    ∀ i, ((code i).length : ℝ) < -Real.log (p i) / Real.log 2 + 2) :=
  PEqualNP.Outside.L_lib_524_aux.main
