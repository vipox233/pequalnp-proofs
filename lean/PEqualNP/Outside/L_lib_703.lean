import Mathlib

namespace PEqualNP.Outside.L_lib_703_aux

open Matrix

theorem bsum (e h y : ℝ) (he : e = 1 ∨ e = -1) :
    (∑ b : Bool, (if e * |h| = (if b then (-1 : ℝ) else 1) * h then h * y else 0)) = h * y := by
  rw [Fintype.sum_bool]
  simp only [if_true, Bool.false_eq_true, if_false]
  rcases lt_trichotomy h 0 with hh | hh | hh
  · rw [abs_of_neg hh]
    rcases he with rfl | rfl
    · rw [if_pos (by ring), if_neg (by intro c; linarith)]; ring
    · rw [if_neg (by intro c; linarith), if_pos (by ring)]; ring
  · subst hh; simp
  · rw [abs_of_pos hh]
    rcases he with rfl | rfl
    · rw [if_neg (by intro c; linarith), if_pos (by ring)]; ring
    · rw [if_pos (by ring), if_neg (by intro c; linarith)]; ring

theorem swap_sum {n : ℕ} (G : Fin n → Bool → Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    (∑ u : Fin n → Bool, ∏ i, G (σ i) (u (σ i)) i) = ∏ i, ∑ b : Bool, G (σ i) b i := by
  have e1 : ∀ u : Fin n → Bool, (∏ i, G (σ i) (u (σ i)) i) = ∏ r, G r (u r) (σ.symm r) := by
    intro u
    rw [← Equiv.prod_comp σ (fun r => G r (u r) (σ.symm r))]
    simp
  have e2 : (∏ i, ∑ b : Bool, G (σ i) b i) = ∏ r, ∑ b : Bool, G r b (σ.symm r) := by
    rw [← Equiv.prod_comp σ (fun r => ∑ b : Bool, G r b (σ.symm r))]
    simp
  rw [Finset.sum_congr rfl (fun u _ => e1 u), e2, Fintype.prod_sum]

def ep {n : ℕ} (s : Fin n × Fin n → Bool) (i j : Fin n) : ℝ := if s (i,j) then (-1 : ℝ) else 1
def vv {n : ℕ} (u : Fin n → Bool) (i : Fin n) : ℝ := if u i then (-1 : ℝ) else 1
noncomputable def ps {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (u : Fin n → Bool) (i j : Fin n) : ℝ :=
  if ep s i j * |H i j| = vv u i * H i j then |H i j| else 0
noncomputable def TT {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (u : Fin n → Bool) : ℝ :=
  Matrix.det (Matrix.of (fun i j => ep s i j * ps H s u i j))
def PP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := Matrix.permanent (Matrix.of (fun i j => (A i j)^2))

theorem ep_pm {n : ℕ} (s : Fin n × Fin n → Bool) (i j : Fin n) : ep s i j = 1 ∨ ep s i j = -1 := by
  unfold ep; split_ifs <;> simp

theorem vv_sq {n : ℕ} (u : Fin n → Bool) : (∏ i, vv u i) * (∏ i, vv u i) = 1 := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  unfold vv; split_ifs <;> norm_num

theorem part1 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    (∑ u : Fin n → Bool, (∏ i, vv u i) * TT H s u) = H.det := by
  have hT : ∀ u, TT H s u = (∏ i, vv u i) *
      Matrix.det (Matrix.of (fun i j => if ep s i j * |H i j| = vv u i * H i j then H i j else 0)) := by
    intro u
    unfold TT
    rw [← Matrix.det_mul_column]
    congr 1
    ext i j
    simp only [Matrix.of_apply, ps]
    split_ifs with h
    · exact h
    · simp
  simp only [hT, ← mul_assoc, vv_sq, one_mul]
  simp only [Matrix.det_apply, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Finset.smul_sum]
  congr 1
  have := swap_sum (fun r b j => if ep s r j * |H r j| = (if b then (-1 : ℝ) else 1) * H r j then H r j else 0) σ
  rw [show (∑ u : Fin n → Bool, ∏ i, (if ep s (σ i) i * |H (σ i) i| = vv u (σ i) * H (σ i) i then H (σ i) i else 0))
      = ∑ u : Fin n → Bool, ∏ i, (if ep s (σ i) i * |H (σ i) i| = (if u (σ i) then (-1 : ℝ) else 1) * H (σ i) i
        then H (σ i) i else 0) from rfl, this]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have := bsum (ep s (σ i) i) (H (σ i) i) 1 (ep_pm s _ _)
  simpa using this

theorem part2 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    (∑ u : Fin n → Bool, PP (Matrix.of (ps H s u))) = PP H := by
  unfold PP
  simp only [Matrix.permanent, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hsq : ∀ (u : Fin n → Bool) (i : Fin n), (ps H s u (σ i) i)^2 =
      (if ep s (σ i) i * |H (σ i) i| = (if u (σ i) then (-1 : ℝ) else 1) * H (σ i) i
        then H (σ i) i * H (σ i) i else 0) := by
    intro u i
    unfold ps vv
    split_ifs <;> simp [sq_abs, sq]
  simp only [hsq]
  rw [swap_sum (fun r b j => if ep s r j * |H r j| = (if b then (-1 : ℝ) else 1) * H r j
    then H r j * H r j else 0) σ]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [bsum (ep s (σ i) i) (H (σ i) i) (H (σ i) i) (ep_pm s _ _), sq]

theorem PP_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ PP A := by
  unfold PP Matrix.permanent
  exact Finset.sum_nonneg (fun σ _ => Finset.prod_nonneg (fun i _ => by simp [sq_nonneg]))

theorem TT_zero {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (u : Fin n → Bool)
    (h : PP (Matrix.of (ps H s u)) = 0) : TT H s u = 0 := by
  unfold PP Matrix.permanent at h
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun σ _ => Finset.prod_nonneg
    (fun i _ => by simp [sq_nonneg]))).mp h
  unfold TT
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  have hs := h0 σ (Finset.mem_univ _)
  simp only [Matrix.of_apply] at hs ⊢
  rw [Finset.prod_pow] at hs
  have hp : ∏ i, ps H s u (σ i) i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
  rw [Finset.prod_mul_distrib, hp, mul_zero, smul_zero]

theorem part3 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (hP : 0 < PP H) :
    ∃ u : Fin n → Bool, 0 < PP (Matrix.of (ps H s u)) ∧
      H.det^2 * PP (Matrix.of (ps H s u)) ≤ (2 : ℝ)^n * (TT H s u)^2 * PP H := by
  by_contra hneg
  push_neg at hneg
  set S := (Finset.univ : Finset (Fin n → Bool)).filter (fun u => 0 < PP (Matrix.of (ps H s u)))
  have hp : ∀ u, PP (Matrix.of (ps H s u)) ≠ 0 → u ∈ S := by
    intro u hu
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact lt_of_le_of_ne (PP_nonneg _) (Ne.symm hu)
  have hsumP : ∑ u ∈ S, PP (Matrix.of (ps H s u)) = PP H := by
    rw [← part2 H s]
    exact Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => by
      by_contra hc; exact hu (hp u hc))
  have hdet : ∑ u ∈ S, (∏ i, vv u i) * TT H s u = H.det := by
    rw [← part1 H s]
    exact Finset.sum_subset (Finset.subset_univ _) (fun u _ hu => by
      by_contra hc
      apply hu (hp u ?_)
      intro hz
      exact hc (by rw [TT_zero H s u hz, mul_zero]))
  have hSne : S.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    rw [he, Finset.sum_empty] at hsumP
    linarith
  have hcs := Finset.sq_sum_div_le_sum_sq_div S (fun u => (∏ i, vv u i) * TT H s u)
    (g := fun u => PP (Matrix.of (ps H s u))) (fun u hu => (Finset.mem_filter.mp hu).2)
  rw [hdet, hsumP] at hcs
  have hsq : ∀ u, ((∏ i, vv u i) * TT H s u)^2 = (TT H s u)^2 := by
    intro u
    have := vv_sq u
    calc ((∏ i, vv u i) * TT H s u)^2 = ((∏ i, vv u i) * (∏ i, vv u i)) * (TT H s u)^2 := by ring
      _ = (TT H s u)^2 := by rw [this, one_mul]
  simp only [hsq] at hcs
  have hlt : ∀ u ∈ S, (TT H s u)^2 / PP (Matrix.of (ps H s u)) < H.det^2 / ((2 : ℝ)^n * PP H) := by
    intro u hu
    have hpu := (Finset.mem_filter.mp hu).2
    have h2 := hneg u hpu
    rw [div_lt_div_iff₀ hpu (by positivity)]
    linarith
  have hsum := Finset.sum_lt_sum_of_nonempty hSne hlt
  rw [Finset.sum_const] at hsum
  have hcard : (S.card : ℝ) ≤ (2 : ℝ)^n := by
    have := Finset.card_le_univ S
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this
    exact_mod_cast this
  have hD : 0 ≤ H.det^2 / ((2 : ℝ)^n * PP H) := by positivity
  have h3 : S.card • (H.det^2 / ((2 : ℝ)^n * PP H)) ≤ H.det^2 / PP H := by
    rw [nsmul_eq_mul]
    calc (S.card : ℝ) * (H.det^2 / ((2 : ℝ)^n * PP H)) ≤ (2 : ℝ)^n * (H.det^2 / ((2 : ℝ)^n * PP H)) :=
          mul_le_mul_of_nonneg_right hcard hD
      _ = H.det^2 / PP H := by field_simp
  linarith

end PEqualNP.Outside.L_lib_703_aux

theorem PEqualNP.Outside.L_lib_703 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool),
  let I := Fin n
  let ε := fun i j => if s (i,j) then (-1 : ℝ) else 1
  let v := fun (u : I → Bool) i => if u i then (-1 : ℝ) else 1
  let pos := fun (u : I → Bool) (i j : I) =>
    if ε i j * |H i j| = v u i * H i j then |H i j| else 0
  let T := fun (u : I → Bool) => Matrix.det (fun i j => ε i j * pos u i j : Matrix I I ℝ)
  let P := fun A : Matrix I I ℝ => Matrix.permanent (fun i j => (A i j)^2)
  (∑ u : I → Bool, (∏ i : I, v u i) * T u) = H.det ∧
    (∑ u : I → Bool, P (pos u)) = P H ∧
    (0 < P H → ∃ u : I → Bool, 0 < P (pos u) ∧
      H.det^2 * P (pos u) ≤ (2 : ℝ)^n * (T u)^2 * P H) := by
  intro n H s I ε v pos T P
  exact ⟨PEqualNP.Outside.L_lib_703_aux.part1 H s, PEqualNP.Outside.L_lib_703_aux.part2 H s,
    PEqualNP.Outside.L_lib_703_aux.part3 H s⟩
