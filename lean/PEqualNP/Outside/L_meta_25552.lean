import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25552_aux
noncomputable section

open Finset BigOperators

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma weighted_shift_mean_var3 {ι : Type*} [Fintype ι] (w y : ι → ℝ) (b : ℝ)
    (hw : ∑ i, w i = 1) :
    ∑ i, w i*(b+y i) = b + ∑ i, w i*y i := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw]
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma weighted_shift_second_var3 {ι : Type*} [Fintype ι] (w y : ι → ℝ) (b : ℝ)
    (hw : ∑ i, w i = 1) :
    ∑ i, w i*(b+y i)^2 = b^2 + 2*b*(∑ i, w i*y i) + ∑ i, w i*(y i)^2 := by
  have hcross : (∑ i, w i*(2*b*y i)) = 2*b*(∑ i, w i*y i) := by
    calc
      _ = ∑ i, (w i*y i)*(2*b) := by congr 1; funext i; ring
      _ = (∑ i, w i*y i)*(2*b) := by rw [Finset.sum_mul]
      _ = _ := by ring
  have hconst : (∑ i, w i*b^2) = b^2 := by
    calc
      _ = (∑ i, w i)*b^2 := by rw [Finset.sum_mul]
      _ = _ := by rw [hw]; ring
  simp_rw [add_sq, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hconst, hcross]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def hit (l : Fin 8) : Bool := l.val.testBit 2
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def aligned (m : Fin 3) (l : Fin 8) : Bool :=
  ((m.val == 1) && l.val.testBit 0 && l.val.testBit 1) ||
  ((m.val == 2) && l.val.testBit 1)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def gain (m : Fin 3) (l : Fin 8) : ℕ :=
  (hit l).toNat + (aligned m l && hit l).toNat
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def next (m : Fin 3) (l : Fin 8) : Fin 3 :=
  ⟨if aligned m l then (if hit l then 0 else 2) else 1, by split_ifs <;> omega⟩
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def letterMass (q : ℝ) (l : Fin 8) : ℝ :=
  if hit l then q/4 else (1-q)/4
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def trans (q : ℝ) (m j : Fin 3) : ℝ :=
  ∑ l : Fin 8, if next m l = j then letterMass q l else 0
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def stepMean (q : ℝ) (m : Fin 3) : ℝ :=
  ∑ l : Fin 8, letterMass q l * (gain m l : ℝ)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def stepSecond (q : ℝ) (m : Fin 3) : ℝ :=
  ∑ l : Fin 8, letterMass q l * (gain m l : ℝ)^2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def stat (q : ℝ) (m : Fin 3) : ℝ :=
  if m.val = 0 then q/(3+2*q) else if m.val = 1 then 2*(1+q)/(3+2*q) else (1-q)/(3+2*q)
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def rate (q : ℝ) : ℝ := 2*q*(2+q)/(3+2*q)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem trans_table (q : ℝ) :
  trans q 0 0 = 0 ∧ trans q 0 1 = 1 ∧ trans q 0 2 = 0 ∧
  trans q 1 0 = q/4 ∧ trans q 1 1 = 3/4 ∧ trans q 1 2 = (1-q)/4 ∧
  trans q 2 0 = q/2 ∧ trans q 2 1 = 1/2 ∧ trans q 2 2 = (1-q)/2 := by
  repeat' constructor <;>
    norm_num [trans, next, aligned, hit, letterMass, Fin.sum_univ_succ, Nat.testBit] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem mean_table (q : ℝ) :
  stepMean q 0 = q ∧ stepMean q 1 = 5*q/4 ∧ stepMean q 2 = 3*q/2 := by
  repeat' constructor <;>
    norm_num [stepMean, gain, aligned, hit, letterMass, Fin.sum_univ_succ, Nat.testBit] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem second_table (q : ℝ) :
  stepSecond q 0 = q ∧ stepSecond q 1 = 7*q/4 ∧ stepSecond q 2 = 5*q/2 := by
  repeat' constructor <;>
    norm_num [stepSecond, gain, aligned, hit, letterMass, Fin.sum_univ_succ, Nat.testBit] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stat_sum (q : ℝ) (hq : 3+2*q ≠ 0) : (∑ m : Fin 3, stat q m) = 1 := by
  norm_num [stat, Fin.sum_univ_succ]
  have hq' : 3+q*2 ≠ 0 := by
    intro hh
    apply hq
    nlinarith [hh]
  field_simp [hq']
  <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stat_stationary (q : ℝ) (hq : 0 < 3+2*q) :
  ∀ j : Fin 3, (∑ m : Fin 3, stat q m * trans q m j) = stat q j := by
  intro j
  have ht := trans_table q
  fin_cases j <;> simp [stat, Fin.sum_univ_succ, ht] <;> field_simp <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stat_rate (q : ℝ) : (∑ m : Fin 3, stat q m * stepMean q m) = rate q := by
  have hm := mean_table q
  norm_num [stat, rate, Fin.sum_univ_succ, hm]
  <;> field_simp
  <;> ring



set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem oneStepVar_le_one (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) (m : Fin 3) :
    stepSecond q m - (stepMean q m)^2 ≤ 1 := by
  fin_cases m
  · change stepSecond q 0 - (stepMean q 0)^2 ≤ 1
    rw [(mean_table q).1, (second_table q).1]
    nlinarith [sq_nonneg q]
  · change stepSecond q 1 - (stepMean q 1)^2 ≤ 1
    rw [(mean_table q).2.1, (second_table q).2.1]
    nlinarith [sq_nonneg q]
  · change stepSecond q 2 - (stepMean q 2)^2 ≤ 1
    rw [(mean_table q).2.2, (second_table q).2.2]
    nlinarith [sq_nonneg q]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem rate_shift (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) :
    rate q ≤ 5/8 - (1/2-q) := by
  have hden : 0 < 3+2*q := by linarith
  unfold rate
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg (q - 1/2)]

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def meanR (q : ℝ) : Nat → Fin 3 → ℝ
  | 0, _ => 0
  | n+1, m => ∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + meanR q n (next m l))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem meanR_step (q : ℝ) (n : Nat) :
    meanR q (n+1) 0 = q + meanR q n 1 ∧
    meanR q (n+1) 1 = 5*q/4 + q/4*meanR q n 0 + 3/4*meanR q n 1 + (1-q)/4*meanR q n 2 ∧
    meanR q (n+1) 2 = 3*q/2 + q/2*meanR q n 0 + 1/2*meanR q n 1 + (1-q)/2*meanR q n 2 := by
  repeat' constructor <;>
    norm_num [meanR, letterMass, gain, next, aligned, hit, Fin.sum_univ_succ, Nat.testBit] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem meanR_shape (q : ℝ) (n : Nat) :
    meanR q n 1 - meanR q n 0 = meanR q n 2 - meanR q n 1 := by
  induction n with
  | zero => simp [meanR]
  | succ n ih =>
    have hs := meanR_step q n
    rw [hs.1, hs.2.1, hs.2.2]
    nlinarith [ih]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem meanR_gap_nonneg (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) (n : Nat) :
    0 ≤ meanR q n 1 - meanR q n 0 := by
  induction n with
  | zero => simp [meanR]
  | succ n ih =>
    have hs := meanR_step q n
    have hshape := meanR_shape q n
    have hgap : meanR q (n+1) 1 - meanR q (n+1) 0 =
        q/4 + ((1-2*q)/4) * (meanR q n 1 - meanR q n 0) := by
      rw [hs.2.1, hs.1]
      nlinarith [hshape]
    rw [hgap]
    have hlam : 0 ≤ (1 - 2*q)/4 := by nlinarith [hqhi]
    positivity

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem meanR_gap_le (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) (n : Nat) :
    meanR q n 1 - meanR q n 0 ≤ 5/38 := by
  induction n with
  | zero => norm_num [meanR]
  | succ n ih =>
    have hs := meanR_step q n
    have hshape := meanR_shape q n
    have hgap : meanR q (n+1) 1 - meanR q (n+1) 0 =
        q/4 + ((1-2*q)/4) * (meanR q n 1 - meanR q n 0) := by
      rw [hs.2.1, hs.1]
      nlinarith [hshape]
    rw [hgap]
    have hq4 : q/4 ≤ 1/8 := by nlinarith [hqhi]
    have hlam0 : 0 ≤ (1 - 2*q)/4 := by nlinarith [hqhi]
    have hlam1 : (1 - 2*q)/4 ≤ 1/20 := by nlinarith [hqlo]
    have hgap0 : 0 ≤ meanR q n 1 - meanR q n 0 := meanR_gap_nonneg q hqlo hqhi n
    nlinarith [ih, hlam0, hlam1, hgap0]

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem finite_variance_range_two_le_one_var {ι : Type*} [Fintype ι]
    (w z : ι → ℝ) (hw : ∑ i, w i = 1)
    (hw0 : ∀ i, 0 ≤ w i) (hz0 : ∀ i, 0 ≤ z i) (hz2 : ∀ i, z i ≤ 2) :
    ∑ i, w i * z i^2 - (∑ i, w i*z i)^2 ≤ 1 := by
  have hmoment : ∑ i, w i * z i^2 ≤ 2 * (∑ i, w i*z i) := by
    calc
      ∑ i, w i*z i^2 ≤ ∑ i, w i*(2*z i) := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (by nlinarith [hz0 i, hz2 i]) (hw0 i)
      _ = 2 * (∑ i, w i*z i) := by
        calc
          _ = ∑ i, 2*(w i*z i) := by congr 1; funext i; ring
          _ = _ := (Finset.mul_sum _ _ _).symm
  nlinarith [sq_nonneg ((∑ i, w i*z i)-1)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma mass_sum_one_var3 (q : ℝ) : (∑ l : Fin 8, letterMass q l) = 1 := by
  norm_num [letterMass, hit, Fin.sum_univ_succ, Nat.testBit]
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma aug_range_var3 (g : ℝ) (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (m : Fin 3) (l : Fin 8) :
    0 ≤ (gain m l : ℝ) + g * (next m l).val ∧
      (gain m l : ℝ) + g * (next m l).val ≤ 2 := by
  fin_cases m <;> fin_cases l <;>
    norm_num [gain, next, aligned, hit, Nat.testBit] <;> constructor <;> nlinarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def augMean_var3 (q g : ℝ) (m : Fin 3) : ℝ :=
  ∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + g * (next m l).val)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def augSecond_var3 (q g : ℝ) (m : Fin 3) : ℝ :=
  ∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + g * (next m l).val)^2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem augVar_le_one_var3 (q g : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (m : Fin 3) :
    augSecond_var3 q g m - (augMean_var3 q g m)^2 ≤ 1 := by
  apply finite_variance_range_two_le_one_var
    (fun l => letterMass q l) (fun l => (gain m l : ℝ) + g * (next m l).val)
  · exact mass_sum_one_var3 q
  · intro l; unfold letterMass; split <;> positivity
  · exact fun l => (aug_range_var3 g hg0 hg1 m l).1
  · exact fun l => (aug_range_var3 g hg0 hg1 m l).2

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma meanR_affine_var3 (q : ℝ) (n : Nat) :
    ∀ m : Fin 3, meanR q n m = meanR q n 0 + (m.val : ℝ) * (meanR q n 1 - meanR q n 0) := by
  intro m
  fin_cases m
  · simp
  · simp
  · have h := meanR_shape q n
    norm_num
    linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem oneStepFutureVariance_le_one_var3 (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2)
    (n : Nat) (m : Fin 3) :
    (∑ l : Fin 8, letterMass q l *
      ((gain m l : ℝ) + meanR q n (next m l))^2) -
      (meanR q (n+1) m)^2 ≤ 1 := by
  let b : ℝ := meanR q n 0
  let g : ℝ := meanR q n 1 - meanR q n 0
  have hg0 : 0 ≤ g := by dsimp [g]; exact meanR_gap_nonneg q hqlo hqhi n
  have hg1 : g ≤ 1 := by dsimp [g]; have h := meanR_gap_le q hqlo hqhi n; linarith
  have hf := meanR_affine_var3 q n
  have hms : ∑ l : Fin 8, letterMass q l = 1 := mass_sum_one_var3 q
  have hmean : meanR q (n+1) m = b + augMean_var3 q g m := by
    rw [meanR]
    unfold augMean_var3
    calc
      (∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + meanR q n (next m l))) =
          ∑ l : Fin 8, letterMass q l * (b + ((gain m l : ℝ) + g * (next m l).val)) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hf (next m l)]
            dsimp [b, g]
            ring
      _ = b + ∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + g * (next m l).val) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hms]
            ring
  have hsecond : (∑ l : Fin 8, letterMass q l *
      ((gain m l : ℝ) + meanR q n (next m l))^2) =
      b^2 + 2*b*augMean_var3 q g m + augSecond_var3 q g m := by
    calc
      _ = ∑ l : Fin 8, letterMass q l *
          (b + ((gain m l : ℝ) + g * (next m l).val))^2 := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hf (next m l)]
            dsimp [b, g]
            ring
      _ = b^2 + 2*b*augMean_var3 q g m + augSecond_var3 q g m := by
            simpa [augMean_var3, augSecond_var3] using
              (weighted_shift_second_var3 (fun l : Fin 8 => letterMass q l)
                (fun l => (gain m l : ℝ) + g * (next m l).val) b hms)
  rw [hsecond, hmean]
  have hv := augVar_le_one_var3 q g (by linarith) (by linarith) hg0 hg1 m
  dsimp [augMean_var3, augSecond_var3] at hv ⊢
  nlinarith [hv]

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def secondR_var3 (q : ℝ) : Nat → Fin 3 → ℝ
  | 0, _ => 0
  | n+1, m => ∑ l : Fin 8, letterMass q l *
      ((gain m l : ℝ)^2 + 2*(gain m l : ℝ)*meanR q n (next m l) + secondR_var3 q n (next m l))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def varianceR_var3 (q : ℝ) (n : Nat) (m : Fin 3) : ℝ :=
  secondR_var3 q n m - (meanR q n m)^2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem varianceR_step_var3 (q : ℝ) (n : Nat) (m : Fin 3) :
    varianceR_var3 q (n+1) m =
      (∑ l : Fin 8, letterMass q l * varianceR_var3 q n (next m l)) +
      ((∑ l : Fin 8, letterMass q l *
        ((gain m l : ℝ) + meanR q n (next m l))^2) - (meanR q (n+1) m)^2) := by
  unfold varianceR_var3
  change (∑ l : Fin 8, letterMass q l *
      ((gain m l : ℝ)^2 + 2*(gain m l : ℝ)*meanR q n (next m l) + secondR_var3 q n (next m l))) -
      (meanR q (n+1) m)^2 = _
  have hpoint (l : Fin 8) :
      (gain m l : ℝ)^2 + 2*(gain m l : ℝ)*meanR q n (next m l) + secondR_var3 q n (next m l) =
      varianceR_var3 q n (next m l) + ((gain m l : ℝ)+meanR q n (next m l))^2 := by
    unfold varianceR_var3
    ring
  have hsumvar :
      (∑ l : Fin 8, letterMass q l * varianceR_var3 q n (next m l)) =
      (∑ l : Fin 8, letterMass q l * secondR_var3 q n (next m l)) -
        (∑ l : Fin 8, letterMass q l * (meanR q n (next m l))^2) := by
    calc
      _ = ∑ l : Fin 8, letterMass q l *
          (secondR_var3 q n (next m l) - (meanR q n (next m l))^2) := by
            apply Finset.sum_congr rfl
            intro l hl
            simp [varianceR_var3]
      _ = _ := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
  have hmoment :
      (∑ l : Fin 8, letterMass q l *
        ((gain m l : ℝ)^2 + 2*(gain m l : ℝ)*meanR q n (next m l) + secondR_var3 q n (next m l))) =
      (∑ l : Fin 8, letterMass q l * varianceR_var3 q n (next m l)) +
        (∑ l : Fin 8, letterMass q l * ((gain m l : ℝ)+meanR q n (next m l))^2) := by
    calc
      _ = ∑ l : Fin 8, letterMass q l *
          (varianceR_var3 q n (next m l) + ((gain m l : ℝ)+meanR q n (next m l))^2) := by
            apply Finset.sum_congr rfl
            intro l hl
            rw [hpoint l]
      _ = _ := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
  have hsumvar' :
      (∑ l : Fin 8, letterMass q l *
        (secondR_var3 q n (next m l) - (meanR q n (next m l))^2)) =
      (∑ l : Fin 8, letterMass q l * varianceR_var3 q n (next m l)) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsumvar]
  rw [hmoment]
  rw [hsumvar']
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem varianceR_le_n_var3 (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) :
    ∀ n m, varianceR_var3 q n m ≤ n := by
  intro n
  induction n with
  | zero => intro m; simp [varianceR_var3, secondR_var3, meanR]
  | succ n ih =>
      intro m
      rw [varianceR_step_var3]
      have hsum : (∑ l : Fin 8, letterMass q l * varianceR_var3 q n (next m l)) ≤ n := by
        have hq0 : 0 ≤ q := by linarith
        have hq1 : q ≤ 1 := by linarith
        calc
          _ ≤ ∑ l : Fin 8, letterMass q l * (n:ℝ) := Finset.sum_le_sum fun l _ =>
            mul_le_mul_of_nonneg_left (ih (next m l)) (by
              unfold letterMass
              split <;> positivity)
          _ = n := by rw [← Finset.sum_mul, mass_sum_one_var3]; simp
      have hone := oneStepFutureVariance_le_one_var3 q hqlo hqhi n m
      push_cast
      linarith

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
abbrev Path (n : Nat) := Fin n → Fin 8

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathWeight (q : ℝ) : (n : Nat) → Path n → ℝ
  | 0, _ => 1
  | n+1, w => letterMass q (w 0) * pathWeight q n (Fin.tail w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathReward (q : ℝ) : (n : Nat) → Fin 3 → Path n → ℕ
  | 0, _, _ => 0
  | n+1, m, w => gain m (w 0) + pathReward q n (next m (w 0)) (Fin.tail w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathMean (q : ℝ) (n : Nat) (m : Fin 3) : ℝ :=
  ∑ w : Path n, pathWeight q n w * (pathReward q n m w : ℝ)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathSecond (q : ℝ) (n : Nat) (m : Fin 3) : ℝ :=
  ∑ w : Path n, pathWeight q n w * (pathReward q n m w : ℝ)^2

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathWeight_sum_one (q : ℝ) : ∀ n, (∑ w : Path n, pathWeight q n w) = 1 := by
  intro n
  induction n with
  | zero => simp [pathWeight, Path]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 8)
    have heq : (∑ w : Path (n+1), pathWeight q (n+1) w) =
        ∑ p : Fin 8 × Path n, letterMass q p.1 * pathWeight q n p.2 := by
      exact Fintype.sum_equiv e.symm (fun w => pathWeight q (n+1) w)
        (fun p => letterMass q p.1 * pathWeight q n p.2) (by
          intro w
          simp [pathWeight, e, Fin.consEquiv_apply])
    rw [heq, Fintype.sum_prod_type]
    calc
      _ = ∑ x : Fin 8, letterMass q x := by
        apply Finset.sum_congr rfl
        intro x hx
        have hinner : (∑ y : Path n, letterMass q x * pathWeight q n y) = letterMass q x := by
          calc
            _ = letterMass q x * (∑ y : Path n, pathWeight q n y) := by
              rw [← Finset.mul_sum]
            _ = letterMass q x := by rw [ih]; ring
        simpa using hinner
      _ = 1 := mass_sum_one_var3 q

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathMean_eq_meanR_var3 (q : ℝ) : ∀ n m, pathMean q n m = meanR q n m := by
  intro n
  induction n with
  | zero => intro m; simp [pathMean, pathWeight, pathReward, meanR]
  | succ n ih =>
      intro m
      let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 8)
      have heq : pathMean q (n+1) m =
          ∑ p : Fin 8 × Path n, letterMass q p.1 * pathWeight q n p.2 *
            ((gain m p.1 : ℝ) + (pathReward q n (next m p.1) p.2 : ℝ)) := by
        unfold pathMean
        exact Fintype.sum_equiv e.symm
          (fun w => pathWeight q (n+1) w * (pathReward q (n+1) m w : ℝ))
          (fun p => letterMass q p.1 * pathWeight q n p.2 *
            ((gain m p.1 : ℝ) + (pathReward q n (next m p.1) p.2 : ℝ))) (by
              intro w
              simp [pathWeight, pathReward, e, Fin.consEquiv_apply]
              <;> push_cast
              <;> ring)
      rw [heq, Fintype.sum_prod_type]
      have hinner (l : Fin 8) :
          (∑ w : Path n, letterMass q l * pathWeight q n w *
            ((gain m l : ℝ) + (pathReward q n (next m l) w : ℝ))) =
          letterMass q l * ((gain m l : ℝ) + pathMean q n (next m l)) := by
        have hnorm := pathWeight_sum_one q n
        have hgain : (∑ w : Path n, letterMass q l * pathWeight q n w * (gain m l : ℝ)) =
            letterMass q l * (gain m l : ℝ) * (∑ w : Path n, pathWeight q n w) := by
          calc
            _ = letterMass q l * (∑ w : Path n, pathWeight q n w * (gain m l : ℝ)) := by
              simp_rw [mul_assoc]
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.sum_mul]; ring
        have hreward : (∑ w : Path n, letterMass q l * pathWeight q n w *
            (pathReward q n (next m l) w : ℝ)) = letterMass q l *
              (∑ w : Path n, pathWeight q n w * (pathReward q n (next m l) w : ℝ)) := by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
        calc
          _ = (∑ w : Path n, letterMass q l * pathWeight q n w * (gain m l : ℝ)) +
              (∑ w : Path n, letterMass q l * pathWeight q n w *
                (pathReward q n (next m l) w : ℝ)) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib]
          _ = _ := by rw [hgain, hreward, hnorm]; simp [pathMean]; ring
      calc
        _ = ∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + pathMean q n (next m l)) := by
          apply Finset.sum_congr rfl
          intro l hl
          exact hinner l
        _ = ∑ l : Fin 8, letterMass q l * ((gain m l : ℝ) + meanR q n (next m l)) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [ih (next m l)]
        _ = meanR q (n+1) m := by
          rw [meanR]

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathSecond_eq_secondR_var3 (q : ℝ) : ∀ n m, pathSecond q n m = secondR_var3 q n m := by
  intro n
  induction n with
  | zero => intro m; simp [pathSecond, pathWeight, pathReward, secondR_var3]
  | succ n ih =>
      intro m
      let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 8)
      have heq : pathSecond q (n+1) m =
          ∑ p : Fin 8 × Path n, letterMass q p.1 * pathWeight q n p.2 *
            ((gain m p.1 : ℝ) + (pathReward q n (next m p.1) p.2 : ℝ))^2 := by
        unfold pathSecond
        exact Fintype.sum_equiv e.symm
          (fun w => pathWeight q (n+1) w * (pathReward q (n+1) m w : ℝ)^2)
          (fun p => letterMass q p.1 * pathWeight q n p.2 *
            ((gain m p.1 : ℝ) + (pathReward q n (next m p.1) p.2 : ℝ))^2) (by
              intro w
              simp [pathWeight, pathReward, e, Fin.consEquiv_apply])
      rw [heq, Fintype.sum_prod_type]
      have hinner (l : Fin 8) :
          (∑ w : Path n, letterMass q l * pathWeight q n w *
            ((gain m l : ℝ) + (pathReward q n (next m l) w : ℝ))^2) =
          letterMass q l * ((gain m l : ℝ)^2 +
            2*(gain m l : ℝ)*meanR q n (next m l) + secondR_var3 q n (next m l)) := by
        have hnorm := pathWeight_sum_one q n
        have hmean := pathMean_eq_meanR_var3 q n (next m l)
        have hsecond := ih (next m l)
        have hcross : (∑ w : Path n, pathWeight q n w *
              (pathReward q n (next m l) w : ℝ)) = meanR q n (next m l) := by
          simpa [pathMean] using hmean
        have hsq : (∑ w : Path n, pathWeight q n w *
              (pathReward q n (next m l) w : ℝ)^2) = secondR_var3 q n (next m l) := by
          simpa [pathSecond] using hsecond
        have hbase : (∑ w : Path n, letterMass q l * pathWeight q n w *
              (gain m l : ℝ)^2) = letterMass q l * (gain m l : ℝ)^2 := by
          calc
            _ = letterMass q l * (gain m l : ℝ)^2 * (∑ w : Path n, pathWeight q n w) := by
              calc
                _ = ∑ w : Path n, (letterMass q l * (gain m l : ℝ)^2) * pathWeight q n w := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  ring
                _ = _ := by rw [← Finset.mul_sum]
            _ = _ := by rw [hnorm]; ring
        have hcross' : (∑ w : Path n, letterMass q l * pathWeight q n w *
              (2*(gain m l : ℝ)*(pathReward q n (next m l) w : ℝ))) =
              letterMass q l * (2*(gain m l : ℝ)*meanR q n (next m l)) := by
          calc
            _ = (letterMass q l * (2*(gain m l : ℝ))) *
                (∑ w : Path n, pathWeight q n w * (pathReward q n (next m l) w : ℝ)) := by
              calc
                _ = ∑ w : Path n, (letterMass q l * (2*(gain m l : ℝ))) *
                    (pathWeight q n w * (pathReward q n (next m l) w : ℝ)) := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  ring
                _ = _ := by rw [← Finset.mul_sum]
            _ = _ := by rw [hcross]; ring
        have hsq' : (∑ w : Path n, letterMass q l * pathWeight q n w *
              (pathReward q n (next m l) w : ℝ)^2) =
              letterMass q l * secondR_var3 q n (next m l) := by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum, hsq]
        calc
          _ = (∑ w : Path n, letterMass q l * pathWeight q n w * (gain m l : ℝ)^2) +
              (∑ w : Path n, letterMass q l * pathWeight q n w *
                (2*(gain m l : ℝ)*(pathReward q n (next m l) w : ℝ))) +
              (∑ w : Path n, letterMass q l * pathWeight q n w *
                (pathReward q n (next m l) w : ℝ)^2) := by
            simp_rw [add_sq, mul_add]
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ = _ := by rw [hbase, hcross', hsq']; ring
      calc
        _ = ∑ l : Fin 8, letterMass q l *
              ((gain m l : ℝ)^2 + 2*(gain m l : ℝ)*meanR q n (next m l) +
                secondR_var3 q n (next m l)) := by
          apply Finset.sum_congr rfl
          intro l hl
          exact hinner l
        _ = secondR_var3 q (n+1) m := by
          rw [secondR_var3]

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma letterMass_nonneg_var3 (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (l : Fin 8) :
    0 ≤ letterMass q l := by
  unfold letterMass
  split <;> positivity

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathWeight_nonneg_var3 (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∀ n w, 0 ≤ pathWeight q n w := by
  intro n
  induction n with
  | zero => intro w; simp [pathWeight]
  | succ n ih =>
      intro w
      exact mul_nonneg (letterMass_nonneg_var3 q hq0 hq1 (w 0)) (ih (Fin.tail w))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathVariance_centered_eq_var3 (q : ℝ) (n : Nat) (m : Fin 3)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ w : Path n, pathWeight q n w *
      ((pathReward q n m w : ℝ) - meanR q n m)^2) = varianceR_var3 q n m := by
  have hnorm := pathWeight_sum_one q n
  have hmean := pathMean_eq_meanR_var3 q n m
  have hsecond := pathSecond_eq_secondR_var3 q n m
  have hmean' : (∑ w : Path n, pathWeight q n w * (pathReward q n m w : ℝ)) = meanR q n m := by
    simpa [pathMean] using hmean
  have hsecond' : (∑ w : Path n, pathWeight q n w * (pathReward q n m w : ℝ)^2) = secondR_var3 q n m := by
    simpa [pathSecond] using hsecond
  have hsq : (∑ w : Path n, pathWeight q n w *
      ((pathReward q n m w : ℝ) - meanR q n m)^2) =
      secondR_var3 q n m - 2*meanR q n m * meanR q n m + (meanR q n m)^2 := by
    have hh := weighted_shift_second_var3 (fun w : Path n => pathWeight q n w)
      (fun w => (pathReward q n m w : ℝ)) (-meanR q n m) hnorm
    rw [hsecond', hmean'] at hh
    calc
      _ = ∑ w : Path n, pathWeight q n w *
          (-meanR q n m + (pathReward q n m w : ℝ))^2 := by
            apply Finset.sum_congr rfl
            intro w hw
            congr 2
            ring
      _ = (-meanR q n m)^2 + 2*(-meanR q n m)*meanR q n m + secondR_var3 q n m := hh
      _ = meanR q n m ^ 2 - 2*meanR q n m*meanR q n m + secondR_var3 q n m := by ring
      _ = secondR_var3 q n m - 2*meanR q n m*meanR q n m + (meanR q n m)^2 := by ring
  rw [hsq]
  unfold varianceR_var3
  ring

namespace CantelliLocal

variable {α : Type*} [Fintype α] [DecidableEq α]
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def mass (w : α → ℝ) (s : Finset α) : ℝ := ∑ a ∈ s, w a

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem upperTail (w X : α → ℝ) (μ t : ℝ) (hw : ∀ a, 0 ≤ w a)
    (hnorm : ∑ a, w a = 1) (hmean : ∑ a, w a * X a = μ) (ht : 0 < t) :
    mass w (Finset.univ.filter fun a => μ + t < X a) ≤
      (∑ a, w a * (X a - μ)^2) / ((∑ a, w a * (X a - μ)^2) + t^2) := by
  classical
  let v := ∑ a, w a * (X a - μ)^2
  have hv : 0 ≤ v := by
    dsimp [v]
    apply Finset.sum_nonneg
    intro a ha
    exact mul_nonneg (hw a) (sq_nonneg _)
  have hcenter : ∑ a, w a * (X a - μ) = 0 := by
    calc
      _ = (∑ a, w a * X a) - ∑ a, w a * μ := by
        rw [show (fun a => w a * (X a-μ)) = (fun a => w a*X a-w a*μ) by funext a; ring,
          Finset.sum_sub_distrib]
      _ = μ-μ := by rw [hmean, ← Finset.sum_mul, hnorm]; ring
      _ = 0 := sub_self μ
  have hsecond : ∑ a, w a * (X a - μ + v/t)^2 = v+(v/t)^2 := by
    rw [show (fun a => w a*(X a-μ+v/t)^2) =
      (fun a => w a*((X a-μ)^2+2*(X a-μ)*(v/t)+(v/t)^2)) by funext a; ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hcross : ∑ a, w a*(2*(X a-μ)*(v/t))=0 := by
      rw [show (fun a => w a*(2*(X a-μ)*(v/t))) =
        (fun a => (2*(v/t))*(w a*(X a-μ))) by funext a; ring,
        ← Finset.mul_sum, hcenter]
      ring
    rw [hcross]
    have hconst : ∑ a, w a*(v/t)^2=(v/t)^2 := by rw [← Finset.sum_mul, hnorm]; ring
    dsimp [v]
    rw [hconst]
    ring
  let E := Finset.univ.filter fun a => μ+t<X a
  have hpoint (a : α) (ha : a ∈ E) : (t+v/t)^2 ≤ (X a-μ+v/t)^2 := by
    have hxa : μ+t<X a := by simpa [E] using ha
    have hp : 0<t+v/t := by positivity
    nlinarith [sq_nonneg (X a-μ+v/t-(t+v/t))]
  have hsub : mass w E*(t+v/t)^2 ≤ ∑ a ∈ E, w a*(X a-μ+v/t)^2 := by
    unfold mass
    calc
      _ = ∑ a ∈ E, w a*(t+v/t)^2 := by rw [Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hpoint a ha) (hw a)
  have hfull : ∑ a ∈ E, w a*(X a-μ+v/t)^2 ≤ ∑ a, w a*(X a-μ+v/t)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
      (fun a ha hn => mul_nonneg (hw a) (sq_nonneg _))
  have hineq : mass w E*(t+v/t)^2 ≤ v+(v/t)^2 := le_trans hsub (by rw [← hsecond]; exact hfull)
  have hden : 0<v+t^2 := by positivity
  have hscaled : mass w E*(v+t^2)≤v := by
    have htne : t≠0 := ne_of_gt ht
    have hform : (t+v/t)^2=(v+t^2)^2/t^2 := by field_simp; ring
    have hrhs : v+(v/t)^2=v*(v+t^2)/t^2 := by field_simp; ring
    rw [hform,hrhs] at hineq
    have ht2 : 0<t^2 := sq_pos_of_pos ht
    field_simp [htne] at hineq
    nlinarith
  have hresult := (le_div_iff₀ hden).2 hscaled
  simpa [E, v, mass] using hresult
end CantelliLocal

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem path_reward_lower_event_var3 (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2)
    (n : Nat) (m : Fin 3) (d t : ℝ) (ht : 0 < t)
    (hgap : meanR q n m + t ≤ d) :
    CantelliLocal.mass (pathWeight q n)
      (Finset.univ.filter fun w : Path n => (pathReward q n m w : ℝ) ≤ d) ≥
      t^2 / ((n:ℝ)+t^2) := by
  classical
  let X : Path n → ℝ := fun w => (pathReward q n m w : ℝ)
  let μ : ℝ := meanR q n m
  let bad := Finset.univ.filter fun w : Path n => d < X w
  let tail := Finset.univ.filter fun w : Path n => μ+t < X w
  let good := Finset.univ.filter fun w : Path n => X w ≤ d
  have hw (w : Path n) : 0 ≤ pathWeight q n w :=
    pathWeight_nonneg_var3 q (by linarith) (by linarith) n w
  have hnorm : (∑ w : Path n, pathWeight q n w) = 1 := pathWeight_sum_one q n
  have hmean : (∑ w : Path n, pathWeight q n w * X w) = μ := by
    simpa [X, μ, pathMean] using pathMean_eq_meanR_var3 q n m
  have hvar : (∑ w : Path n, pathWeight q n w * (X w-μ)^2) = varianceR_var3 q n m := by
    simpa [X, μ] using pathVariance_centered_eq_var3 q n m (by linarith) (by linarith)
  have hvnonneg : 0 ≤ varianceR_var3 q n m := by
    rw [← hvar]
    apply Finset.sum_nonneg
    intro w hw'
    exact mul_nonneg (hw w) (sq_nonneg _)
  have hvle : varianceR_var3 q n m ≤ n := varianceR_le_n_var3 q hqlo hqhi n m
  have hcant := CantelliLocal.upperTail (pathWeight q n) X μ t hw hnorm hmean ht
  have hsubset : bad ⊆ tail := by
    intro w hw'
    simp only [bad, tail, Finset.mem_filter, Finset.mem_univ, true_and] at hw' ⊢
    dsimp [X, μ]
    linarith [hgap]
  have hbadle : CantelliLocal.mass (pathWeight q n) bad ≤
      CantelliLocal.mass (pathWeight q n) tail := by
    unfold CantelliLocal.mass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun w hw' hnot => hw w)
  have hsplit : CantelliLocal.mass (pathWeight q n) good +
      CantelliLocal.mass (pathWeight q n) bad = 1 := by
    have hs := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
      (p := fun w : Path n => d < X w) (f := pathWeight q n)
    have hcompl : (Finset.univ.filter fun w : Path n => ¬ d < X w) = good := by
      ext w
      simp [good, X, not_lt]
    have hs' : CantelliLocal.mass (pathWeight q n) bad +
        CantelliLocal.mass (pathWeight q n) good = 1 := by
      simpa [CantelliLocal.mass, bad, good, hcompl, hnorm] using hs
    linarith
  have htailbound : CantelliLocal.mass (pathWeight q n) tail ≤
      varianceR_var3 q n m / (varianceR_var3 q n m + t^2) := by
    simpa [CantelliLocal.mass, tail, X, μ, hvar] using hcant
  have hden1 : 0 < varianceR_var3 q n m + t^2 := by positivity
  have hden2 : 0 < (n:ℝ)+t^2 := by positivity
  have hfrac : varianceR_var3 q n m / (varianceR_var3 q n m+t^2) ≤
      (n:ℝ)/((n:ℝ)+t^2) := by
    apply (div_le_div_iff₀ hden1 hden2).2
    have hm := mul_le_mul_of_nonneg_right hvle (sq_nonneg t)
    nlinarith [hm]
  have hbad : CantelliLocal.mass (pathWeight q n) bad ≤ (n:ℝ)/((n:ℝ)+t^2) :=
    le_trans hbadle (le_trans htailbound hfrac)
  change CantelliLocal.mass (pathWeight q n) good ≥ t^2 / ((n:ℝ)+t^2)
  have hgood : CantelliLocal.mass (pathWeight q n) good =
      1 - CantelliLocal.mass (pathWeight q n) bad := by linarith [hsplit]
  rw [hgood]
  have hres : 1 - (n:ℝ)/((n:ℝ)+t^2) = t^2/((n:ℝ)+t^2) := by
    field_simp [ne_of_gt hden2]
    ring
  linarith

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathCode (n : Nat) (w : Path n) : Nat :=
  Nat.ofDigits 8 (List.ofFn fun i => (w i).val)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathCode_lt (n : Nat) (w : Path n) : pathCode n w < 8^n := by
  unfold pathCode
  have hdigits : ∀ x ∈ List.ofFn (fun i : Fin n => (w i).val), x < 8 := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact (w i).isLt
  have h := Nat.ofDigits_lt_base_pow_length (by norm_num : 1 < 8) hdigits
  simpa using h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathCode_digit (n : Nat) (w : Path n) (i : Nat) (hi : i < n) :
    ((pathCode n w) >>> (3*i)) % 8 = (w ⟨i, hi⟩).val := by
  unfold pathCode
  rw [Nat.shiftRight_eq_div_pow]
  have hpow : 2^(3*i)=8^i := by
    calc
      2^(3*i) = (2^3)^i := by rw [Nat.pow_mul]
      _ = 8^i := by norm_num
  rw [hpow, Nat.ofDigits_div_pow_eq_ofDigits_drop i (by norm_num)]
  · have hlen : i < (List.ofFn (fun j : Fin n => (w j).val)).length := by simpa using hi
    rw [List.drop_eq_getElem_cons hlen, Nat.ofDigits_cons]
    simp [Nat.mod_eq_of_lt (w ⟨i, hi⟩).isLt]
  · intro x hx
    simp only [List.mem_ofFn] at hx
    rcases hx with ⟨j, rfl⟩
    exact (w j).isLt

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathCode_injective (n : Nat) : Function.Injective (pathCode n) := by
  intro w z h
  funext i
  apply Fin.ext
  have hw := pathCode_digit n w i.val i.isLt
  have hz := pathCode_digit n z i.val i.isLt
  rw [h] at hw
  rw [hw] at hz
  exact hz

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathCodeFin (n : Nat) (w : Path n) : Fin (8^n) :=
  ⟨pathCode n w, pathCode_lt n w⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathCodeFin_bijective (n : Nat) : Function.Bijective (pathCodeFin n) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro w z h
    apply pathCode_injective n
    exact Fin.ext_iff.mp h
  · simp [pathCodeFin, Path, Fintype.card_fun]

end L25552Tilt

namespace L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def runMode : (n : Nat) → Fin 3 → Path n → Fin 3
  | 0, m, _ => m
  | n+1, m, w => runMode n (next m (w 0)) (Fin.tail w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathFold : (n : Nat) → Path n → Fin 3 → Fin 3 × Nat
  | n, w, m => (List.ofFn (fun i : Fin n => w i)).foldl
      (fun st l => (next st.1 l, st.2 + gain st.1 l)) (m, 0)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma fold_gain_offset (l : List (Fin 8)) (m : Fin 3) (g : Nat) :
    l.foldl (fun st x => (next st.1 x, st.2 + gain st.1 x)) (m,g) =
      let z := l.foldl (fun st x => (next st.1 x, st.2 + gain st.1 x)) (m,0)
      (z.1, g + z.2) := by
  induction l generalizing m g with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have h1 := ih (next m x) (g + gain m x)
      have h2 := ih (next m x) (gain m x)
      simp only [List.foldl_cons] at h1 h2 ⊢
      simp only [Nat.zero_add] at h1 h2 ⊢
      rw [h1, h2]
      apply Prod.ext
      · rfl
      · omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathFold_eq_runMode_gain : ∀ n (w : Path n) (m : Fin 3),
    pathFold n w m = (runMode n m w, pathReward (1/2) n m w) := by
  intro n
  induction n with
  | zero => intro w m; rfl
  | succ n ih =>
      intro w m
      simp only [pathFold, runMode, pathReward, List.ofFn_succ, List.foldl_cons]
      rw [fold_gain_offset]
      simp only [Nat.zero_add]
      let z := (List.ofFn (fun i : Fin n => (Fin.tail w) i)).foldl
        (fun st l => (next st.1 l, st.2 + gain st.1 l)) (next m (w 0), 0)
      change (z.1, gain m (w 0) + z.2) =
        (runMode n (next m (w 0)) (Fin.tail w),
          gain m (w 0) + pathReward (1/2) n (next m (w 0)) (Fin.tail w))
      have hh := ih (Fin.tail w) (next m (w 0))
      change z = (runMode n (next m (w 0)) (Fin.tail w),
        pathReward (1/2) n (next m (w 0)) (Fin.tail w)) at hh
      rw [hh]

end L25552Tilt

namespace L25552NatBridge

open L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def moveN (mode letter : Nat) : Nat × Nat :=
  let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
    ((mode == 2) && letter.testBit 1)
  let hit := letter.testBit 2
  (if aligned then (if hit then 0 else 2) else 1,
    hit.toNat + (aligned && hit).toNat)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def foldN (code : Nat) (digits : List Nat) (st : Nat × Nat) : Nat × Nat :=
  digits.foldl (fun st pos =>
    let r := moveN st.1 ((code >>> (3*pos)) % 8)
    (r.1, st.2+r.2)) st

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def stateN (code n mode : Nat) : Nat × Nat := foldN code (List.range n) (mode,0)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem move_fin (m : Fin 3) (l : Fin 8) :
    moveN m.val l.val = ((next m l).val, gain m l) := by
  fin_cases m <;> fin_cases l <;> decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathCode_succ (n : Nat) (w : Path (n+1)) :
    pathCode (n+1) w = (w 0).val + 8 * pathCode n (Fin.tail w) := by
  unfold pathCode
  rw [List.ofFn_succ, Nat.ofDigits_cons]
  simp [Fin.tail]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathCode_mod (n : Nat) (w : Path (n+1)) :
    pathCode (n+1) w % 8 = (w 0).val := by
  rw [pathCode_succ]
  simp [Nat.mod_eq_of_lt (w 0).isLt]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathCode_div (n : Nat) (w : Path (n+1)) :
    pathCode (n+1) w / 8 = pathCode n (Fin.tail w) := by
  rw [pathCode_succ]
  have h := (w 0).isLt
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem digit_shiftN (c i : Nat) :
    (c >>> (3*(i+1))) % 8 = ((c/8) >>> (3*i)) % 8 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hexp : 2^(3*(i+1)) = 8 * 2^(3*i) := by
    have : 3*(i+1) = 3*i+3 := by omega
    rw [this, pow_add]
    norm_num [pow_succ]
    ring
  rw [hexp, Nat.div_div_eq_div_mul]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem foldShiftN (code : Nat) (digits : List Nat) (st : Nat × Nat) :
    foldN code (digits.map Nat.succ) st = foldN (code/8) digits st := by
  induction digits generalizing st with
  | nil => rfl
  | cons i is ih =>
    simp only [foldN, List.map_cons, List.foldl_cons]
    rw [digit_shiftN code i]
    exact ih _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stateSuccN (code n mode : Nat) :
    stateN code (n+1) mode = foldN (code/8) (List.range n)
      ((moveN mode (code % 8)).1, (moveN mode (code % 8)).2) := by
  unfold stateN
  rw [List.range_succ_eq_map]
  unfold foldN
  simp only [List.foldl_cons, Nat.mul_zero, Nat.shiftRight_zero, Nat.zero_add]
  exact foldShiftN code (List.range n) _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem foldAddN (code : Nat) (digits : List Nat) (m r s : Nat) :
    foldN code digits (m,r+s) =
      let q := foldN code digits (m,s); (q.1,r+q.2) := by
  induction digits generalizing m r s with
  | nil => simp [foldN]
  | cons i is ih =>
    simp only [foldN, List.foldl_cons]
    let z := moveN m ((code >>> (3*i)) % 8)
    have hz := ih z.1 r (s+z.2)
    simp only [Nat.add_assoc]
    change foldN code is (z.1, r+(s+z.2)) =
      ((foldN code is (z.1,s+z.2)).1, r+(foldN code is (z.1,s+z.2)).2)
    exact hz

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stateRewardSuccN (code n mode : Nat) :
    (stateN code (n+1) mode).2 =
      (moveN mode (code % 8)).2 + (stateN (code/8) n (moveN mode (code % 8)).1).2 := by
  rw [stateSuccN]
  let z := moveN mode (code % 8)
  have hadd := foldAddN (code/8) (List.range n) z.1 z.2 0
  simp only [Nat.add_zero] at hadd
  rw [hadd]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathReward_eq_stateN : ∀ n (w : Path n) (m : Fin 3),
    (stateN (pathCode n w) n m.val).2 = pathReward (1/2) n m w := by
  intro n
  induction n with
  | zero => intro w m; simp [stateN, foldN, pathReward]
  | succ n ih =>
    intro w m
    rw [stateRewardSuccN, pathCode_mod, pathCode_div]
    have hm := move_fin m (w 0)
    change moveN m.val (w 0).val = ((next m (w 0)).val, gain m (w 0)) at hm
    rw [hm]
    change gain m (w 0) +
      (stateN (pathCode n (Fin.tail w)) n (next m (w 0)).val).2 =
        gain m (w 0) + pathReward (1/2) n (next m (w 0)) (Fin.tail w)
    rw [ih (Fin.tail w) (next m (w 0))]

end L25552NatBridge

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def recMgf25552 {S A : Type*} [Fintype A] [Nonempty A]
    (next : S → A → S) (gain : S → A → ℝ) (t : ℝ) : Nat → S → ℝ
  | 0, _ => 1
  | n+1, s => (Fintype.card A : ℝ)⁻¹ *
      ∑ a : A, Real.exp (t * gain s a) * recMgf25552 next gain t n (next s a)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem recMgf25552_bound {S A : Type*} [Fintype A] [Nonempty A]
    (next : S → A → S) (gain : S → A → ℝ) (t : ℝ)
    (hstep : ∀ s, (Fintype.card A : ℝ)⁻¹ *
       ∑ a : A, Real.exp (t * gain s a) ≤ Real.exp (50 * t ^ 2)) :
    ∀ n s, recMgf25552 next gain t n s ≤ Real.exp (50 * (n : ℝ) * t ^ 2) := by
  intro n
  induction n with
  | zero => intro s; simp [recMgf25552]
  | succ n ih =>
    intro s
    simp only [recMgf25552]
    have hc : 0 ≤ (Fintype.card A : ℝ)⁻¹ := by positivity
    calc
      (Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, Real.exp (t * gain s a) * recMgf25552 next gain t n (next s a)
          ≤ (Fintype.card A : ℝ)⁻¹ *
             ∑ a : A, Real.exp (t * gain s a) * Real.exp (50 * (n : ℝ) * t ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hc
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (ih (next s a)) (le_of_lt (Real.exp_pos _))
      _ = ((Fintype.card A : ℝ)⁻¹ *
             ∑ a : A, Real.exp (t * gain s a)) * Real.exp (50 * (n : ℝ) * t ^ 2) := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ Real.exp (50 * t ^ 2) * Real.exp (50 * (n : ℝ) * t ^ 2) := by
            exact mul_le_mul_of_nonneg_right (hstep s) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (50 * ((n+1 : ℕ) : ℝ) * t ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring

open Real

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def klBinary25552 (q p : ℝ) : ℝ :=
  q * log (q/p) + (1-q) * log ((1-q)/(1-p))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem binary_entropy_lower25552 {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q*log q + (1-q)*log (1-q) ≥ -log 2 := by
  have hq' : 0 < 1-q := by linarith
  have hleftlog := Real.log_le_sub_one_of_pos (show 0 < (2*q)⁻¹ by positivity)
  rw [Real.log_inv] at hleftlog
  have hleft : q*log (2*q) ≥ q-(1:ℝ)/2 := by
    have hmul : q*((2*q)⁻¹) = (1:ℝ)/2 := by field_simp
    nlinarith [hleftlog, hmul]
  have hrightlog := Real.log_le_sub_one_of_pos (show 0 < (2*(1-q))⁻¹ by positivity)
  rw [Real.log_inv] at hrightlog
  have hright : (1-q)*log (2*(1-q)) ≥ (1-q)-(1:ℝ)/2 := by
    have hmul : (1-q)*((2*(1-q))⁻¹) = (1:ℝ)/2 := by field_simp
    nlinarith [hrightlog, hmul]
  have hident : q*log (2*q)+(1-q)*log (2*(1-q)) =
      q*log q+(1-q)*log (1-q)+log 2 := by
    have h1 : log (2*q)=log 2+log q := by rw [Real.log_mul (by norm_num) (ne_of_gt hq0)]
    have h2 : log (2*(1-q))=log 2+log (1-q) := by rw [Real.log_mul (by norm_num) (ne_of_gt hq')]
    rw [h1,h2]
    ring
  have hsum : q*log q+(1-q)*log (1-q)+log 2 ≥ 0 := by
    rw [← hident]
    linarith [hleft, hright]
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem klBinary_lower25552 {q p : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    klBinary25552 q p ≥ q*log (p⁻¹)-log 2 := by
  have hq' : 0 < 1-q := by linarith
  have hp' : 0 < 1-p := by linarith
  have hlogp : log (p⁻¹) = -log p := Real.log_inv p
  have hlog1p : log (1-p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hent := binary_entropy_lower25552 hq0 hq1
  unfold klBinary25552
  rw [Real.log_div (ne_of_gt hq0) (ne_of_gt hp0),
      Real.log_div (ne_of_gt hq') (ne_of_gt hp')]
  have hnonneg : 0 ≤ log (p⁻¹) := by
    have hpInv : 1 < p⁻¹ := (one_lt_inv₀ hp0).2 hp1
    exact le_of_lt (Real.log_pos hpInv)
  have hrewrite :
      q * (log q - log p) + (1-q) * (log (1-q) - log (1-p)) =
      (q * log q + (1-q) * log (1-q)) + q * log (p⁻¹) - (1-q) * log (1-p) := by
    calc
      _ = (q * log q + (1-q) * log (1-q)) + q * (-log p) - (1-q) * log (1-p) := by ring
      _ = _ := by rw [← hlogp]
  rw [hrewrite]
  nlinarith [hent, mul_nonneg (le_of_lt hq') (neg_nonneg.mpr hlog1p)]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem change_measure_binary_bound25552 {q p K a : ℝ}
    (ha : 0 < a) (haq : a ≤ q) (hq0 : 0 < q) (hq1 : q < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hK : 0 ≤ K)
    (hkl : klBinary25552 q p ≤ K) :
    Real.exp (-(K+log 2)/a) ≤ p := by
  have hklower := klBinary_lower25552 hq0 hq1 hp0 hp1
  have hqlog : q*log (p⁻¹) ≤ K+log 2 := by linarith
  have hnum : 0 ≤ K+log 2 := by positivity
  have hlog : log (p⁻¹) ≤ (K+log 2)/a := by
    apply (le_div_iff₀ ha).2
    have := hqlog
    have hmul : a*log (p⁻¹) ≤ q*log (p⁻¹) := by
      by_cases hl : 0 ≤ log (p⁻¹)
      · exact mul_le_mul_of_nonneg_right haq hl
      · have hpInv : 1 < p⁻¹ := (one_lt_inv₀ hp0).2 hp1
        have hposlog := Real.log_pos hpInv
        exact False.elim (hl (le_of_lt hposlog))
    linarith
  have hexp : p⁻¹ ≤ Real.exp ((K+log 2)/a) := (Real.log_le_iff_le_exp (inv_pos.mpr hp0)).1 hlog
  have hmul : 1 ≤ p*Real.exp ((K+log 2)/a) := by
    have h' := mul_le_mul_of_nonneg_right hexp (le_of_lt hp0)
    have hpiden : p⁻¹ * p = (1:ℝ) := inv_mul_cancel₀ (ne_of_gt hp0)
    nlinarith [h']
  have hfinal : 1 / Real.exp ((K+log 2)/a) ≤ p := by
    apply (div_le_iff₀ (Real.exp_pos _)).2
    nlinarith [hmul]
  have heq : -(K+log 2)/a = -((K+log 2)/a) := by ring
  rw [heq, Real.exp_neg]
  simpa [one_div] using hfinal

open Real

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma normalized_kl_nonneg25552 {α : Type*} [Fintype α] [DecidableEq α]
    (r s : α → ℝ) (hr : ∀ i, 0 < r i) (hs : ∀ i, 0 < s i)
    (hrsum : ∑ i, r i = 1) (hssum : ∑ i, s i = 1) :
    0 ≤ ∑ i, r i * log (r i / s i) := by
  have hterm (i : α) : r i * log (r i / s i) ≥ r i - s i := by
    have hlog := Real.log_le_sub_one_of_pos (div_pos (hs i) (hr i))
    rw [Real.log_div (ne_of_gt (hs i)) (ne_of_gt (hr i))] at hlog
    have hlogid : log (r i / s i) = -log (s i / r i) := by
      rw [Real.log_div (ne_of_gt (hr i)) (ne_of_gt (hs i)),
          Real.log_div (ne_of_gt (hs i)) (ne_of_gt (hr i))]
      ring
    have hratio : log (s i / r i) = log (s i) - log (r i) := by
      rw [Real.log_div (ne_of_gt (hs i)) (ne_of_gt (hr i))]
    rw [hlogid]
    have hmulineq := mul_le_mul_of_nonneg_left hlog (le_of_lt (hr i))
    have hmul : r i * (s i / r i) = s i := by
      calc
        r i * (s i / r i) = r i * (s i * (r i)⁻¹) := by rw [div_eq_mul_inv]
        _ = s i * (r i * (r i)⁻¹) := by ring
        _ = s i := by rw [mul_inv_cancel₀ (ne_of_gt (hr i)), mul_one]
    rw [← hratio] at hmulineq
    nlinarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [Finset.sum_sub_distrib, hrsum, hssum] at hsum
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma logsum_lower25552 {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (ht : t.Nonempty) (q p : α → ℝ)
    (hq : ∀ i ∈ t, 0 < q i) (hp : ∀ i ∈ t, 0 < p i) :
    (∑ i ∈ t, q i) * log ((∑ i ∈ t, q i) / (∑ i ∈ t, p i)) ≤
      ∑ i ∈ t, q i * log (q i / p i) := by
  classical
  let T := {i // i ∈ t}
  let Q : ℝ := ∑ i ∈ t, q i
  let P : ℝ := ∑ i ∈ t, p i
  have hQ : 0 < Q := by
    dsimp [Q]
    obtain ⟨i, hi⟩ := ht
    have hqi := hq i hi
    have hsum : q i ≤ ∑ j ∈ t, q j := Finset.single_le_sum (fun j hj => le_of_lt (hq j hj)) hi
    linarith
  have hP : 0 < P := by
    dsimp [P]
    obtain ⟨i, hi⟩ := ht
    have hpi := hp i hi
    have hsum : p i ≤ ∑ j ∈ t, p j := Finset.single_le_sum (fun j hj => le_of_lt (hp j hj)) hi
    linarith
  let r : T → ℝ := fun i => q i.1 / Q
  let s : T → ℝ := fun i => p i.1 / P
  have hr (i : T) : 0 < r i := by dsimp [r]; exact div_pos (hq i.1 i.2) hQ
  have hs (i : T) : 0 < s i := by dsimp [s]; exact div_pos (hp i.1 i.2) hP
  have hrsum : ∑ i : T, r i = 1 := by
    rw [← Finset.sum_subtype t (fun _ => Iff.rfl) (fun i => q i / Q)]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    dsimp [Q]
    exact mul_inv_cancel₀ (ne_of_gt hQ)
  have hssum : ∑ i : T, s i = 1 := by
    rw [← Finset.sum_subtype t (fun _ => Iff.rfl) (fun i => p i / P)]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    dsimp [P]
    exact mul_inv_cancel₀ (ne_of_gt hP)
  have hkl := normalized_kl_nonneg25552 r s hr hs hrsum hssum
  have hpoint (i : T) :
      r i * log (r i / s i) = (q i.1 / Q) * (log (q i.1 / p i.1) - log (Q/P)) := by
    dsimp [r, s]
    have hqa : 0 < q i.1 := hq i.1 i.2
    have hpa : 0 < p i.1 := hp i.1 i.2
    have h1 : q i.1 / Q / (p i.1 / P) = (q i.1 / p i.1) / (Q/P) := by field_simp
    rw [h1, Real.log_div (div_ne_zero (ne_of_gt hqa) (ne_of_gt hpa))
      (div_ne_zero (ne_of_gt hQ) (ne_of_gt hP)),
      Real.log_div (ne_of_gt hqa) (ne_of_gt hpa),
      Real.log_div (ne_of_gt hQ) (ne_of_gt hP)]
  have hsumid : ∑ i : T, r i * log (r i / s i) =
      (1/Q) * (∑ i ∈ t, q i * log (q i / p i) - Q * log (Q/P)) := by
    rw [Finset.sum_congr rfl (fun i _ => hpoint i)]
    rw [← Finset.sum_subtype t (fun _ => Iff.rfl)
      (fun i => q i / Q * (log (q i / p i) - log (Q/P)))]
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div]
    simp_rw [mul_sub]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_mul]
    dsimp [Q, P]
    ring
  have := hkl
  rw [hsumid] at this
  have hscale : 0 ≤ ∑ i ∈ t, q i * log (q i / p i) - Q * log (Q/P) := by
    have hmul := mul_nonneg (le_of_lt hQ) this
    have hinv : Q * (1/Q) = 1 := by field_simp [ne_of_gt hQ]
    rw [← mul_assoc, hinv, one_mul] at hmul
    dsimp [Q] at hmul ⊢
    linarith
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem event_logsum_data_processing25552 {α : Type*} [Fintype α] [DecidableEq α]
    (q p : α → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 < p i)
    (hqs : ∑ i, q i = 1) (hps : ∑ i, p i = 1) (E : Finset α)
    (hE : E.Nonempty) (hEc : Eᶜ.Nonempty) :
    (∑ i ∈ E, q i) * log ((∑ i ∈ E, q i) / (∑ i ∈ E, p i)) +
      (∑ i ∈ Eᶜ, q i) * log ((∑ i ∈ Eᶜ, q i) / (∑ i ∈ Eᶜ, p i)) ≤
      ∑ i, q i * log (q i / p i) := by
  have h1 := logsum_lower25552 E hE q p (fun i hi => hq i) (fun i hi => hp i)
  have h2 := logsum_lower25552 Eᶜ hEc q p
    (fun i hi => hq i) (fun i hi => hp i)
  have hsplit := Finset.sum_add_sum_compl E (fun i => q i * log (q i / p i))
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def klAtom25552 (q p : ℝ) : ℝ := if q = 0 then 0 else q * log (q/p)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem event_logsum_data_processing_all25552 {α : Type*} [Fintype α] [DecidableEq α]
    (q p : α → ℝ) (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 < p i)
    (hqs : ∑ i, q i = 1) (hps : ∑ i, p i = 1) (E : Finset α) :
    klAtom25552 (∑ i ∈ E, q i) (∑ i ∈ E, p i) +
      klAtom25552 (∑ i ∈ Eᶜ, q i) (∑ i ∈ Eᶜ, p i) ≤
      ∑ i, q i * log (q i / p i) := by
  have hfull : 0 ≤ ∑ i, q i * log (q i / p i) :=
    normalized_kl_nonneg25552 q p hq hp hqs hps
  by_cases hE : E.Nonempty
  · by_cases hEc : Eᶜ.Nonempty
    · have hmain := event_logsum_data_processing25552 q p hq hp hqs hps E hE hEc
      have hqe : 0 < ∑ i ∈ E, q i := by
        rcases hE with ⟨i, hi⟩
        have := Finset.single_le_sum (fun j hj => le_of_lt (hq j)) hi
        linarith [hq i]
      have hpe : 0 < ∑ i ∈ E, p i := by
        rcases hE with ⟨i, hi⟩
        have := Finset.single_le_sum (fun j hj => le_of_lt (hp j)) hi
        linarith [hp i]
      have hqec : 0 < ∑ i ∈ Eᶜ, q i := by
        rcases hEc with ⟨i, hi⟩
        have := Finset.single_le_sum (fun j hj => le_of_lt (hq j)) hi
        linarith [hq i]
      have hpec : 0 < ∑ i ∈ Eᶜ, p i := by
        rcases hEc with ⟨i, hi⟩
        have := Finset.single_le_sum (fun j hj => le_of_lt (hp j)) hi
        linarith [hp i]
      simpa [klAtom25552, ne_of_gt hqe, ne_of_gt hpe, ne_of_gt hqec, ne_of_gt hpec] using hmain
    · have hEc0 : Eᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hEc
      have hEuniv : E = Finset.univ := (Finset.compl_eq_empty_iff E).1 hEc0
      rw [hEuniv]
      simp [klAtom25552, hqs, hps]
      exact hfull
  · have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hE
    rw [hE0]
    simp [klAtom25552, hqs, hps]
    exact hfull

open Finset BigOperators Real
open L25552Tilt

namespace L25552PathKL

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathKL (q : ℝ) (n : Nat) : ℝ :=
  ∑ w : Path n, pathWeight q n w * log (pathWeight q n w / pathWeight (1/2) n w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def letterKL (q : ℝ) : ℝ :=
  ∑ l : Fin 8, letterMass q l * log (letterMass q l / letterMass (1/2) l)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma letterMass_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (l : Fin 8) :
    0 < letterMass q l := by
  unfold letterMass
  split_ifs <;> positivity

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathWeight_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : ∀ n (w : Path n),
    0 < pathWeight q n w := by
  intro n
  induction n with
  | zero => intro w; simp [pathWeight]
  | succ n ih =>
    intro w
    simp only [pathWeight]
    exact mul_pos (letterMass_pos q hq0 hq1 _) (ih (Fin.tail w))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma letterMass_half (l : Fin 8) : letterMass (1/2) l = 1/8 := by
  unfold letterMass
  split_ifs <;> norm_num

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathLogRatio_succ (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : Nat)
    (w : Path (n+1)) :
    log (pathWeight q (n+1) w / pathWeight (1/2) (n+1) w) =
      log (letterMass q (w 0) / letterMass (1/2) (w 0)) +
      log (pathWeight q n (Fin.tail w) / pathWeight (1/2) n (Fin.tail w)) := by
  have hq := letterMass_pos q hq0 hq1 (w 0)
  have hu : 0 < letterMass (1/2) (w 0) := by rw [letterMass_half]; norm_num
  have ht := pathWeight_pos q hq0 hq1 n (Fin.tail w)
  have huTail : 0 < pathWeight (1/2) n (Fin.tail w) :=
    pathWeight_pos (1/2) (by norm_num) (by norm_num) n (Fin.tail w)
  rw [pathWeight, pathWeight]
  have hdiv :
      letterMass q (w 0) * pathWeight q n (Fin.tail w) /
          (letterMass (1/2) (w 0) * pathWeight (1/2) n (Fin.tail w)) =
      (letterMass q (w 0) / letterMass (1/2) (w 0)) *
          (pathWeight q n (Fin.tail w) / pathWeight (1/2) n (Fin.tail w)) := by
    field_simp
  rw [hdiv, Real.log_mul (ne_of_gt (div_pos hq hu)) (ne_of_gt (div_pos ht huTail))]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathKL_succ (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) (n : Nat) :
    pathKL q (n+1) = letterKL q + pathKL q n := by
  unfold pathKL letterKL
  let e : (Fin 8 × Path n) ≃ Path (n+1) :=
    Fin.consEquiv (fun _ : Fin (n+1) => Fin 8)
  have hsum :
      (∑ w : Path (n+1), pathWeight q (n+1) w *
          log (pathWeight q (n+1) w / pathWeight (1/2) (n+1) w)) =
      ∑ p : Fin 8 × Path n,
        letterMass q p.1 * pathWeight q n p.2 *
          log (pathWeight q (n+1) (e p) / pathWeight (1/2) (n+1) (e p)) := by
    exact Fintype.sum_equiv e.symm _ _ (by
      intro w
      simp [pathWeight, e, Fin.consEquiv_apply])
  rw [hsum]
  simp_rw [pathLogRatio_succ q hq0 hq1 n]
  simp only [e, Fin.consEquiv_apply, Fin.cons_zero, Fin.tail_cons]
  rw [Fintype.sum_prod_type]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hnorm : ∑ w : Path n, pathWeight q n w = 1 := pathWeight_sum_one q n
  have hnormu : ∑ l : Fin 8, letterMass q l = 1 := mass_sum_one_var3 q
  have hfirst :
      (∑ l : Fin 8, ∑ w : Path n,
        letterMass q l * pathWeight q n w *
          log (letterMass q l / letterMass (1/2) l)) = letterKL q := by
    calc
      _ = ∑ l : Fin 8, letterMass q l * log (letterMass q l / letterMass (1/2) l) *
            (∑ w : Path n, pathWeight q n w) := by
        apply Finset.sum_congr rfl
        intro l hl
        calc
          _ = ∑ w : Path n,
              (letterMass q l * log (letterMass q l / letterMass (1/2) l)) * pathWeight q n w := by
            apply Finset.sum_congr rfl
            intro w hw
            ring
          _ = _ := by rw [← Finset.mul_sum]
      _ = letterKL q := by simp [letterKL, hnorm]
  have hsecond :
      (∑ l : Fin 8, ∑ w : Path n,
        letterMass q l * pathWeight q n w *
          log (pathWeight q n w / pathWeight (1/2) n w)) = pathKL q n := by
    calc
      _ = ∑ l : Fin 8, letterMass q l *
            (∑ w : Path n, pathWeight q n w *
              log (pathWeight q n w / pathWeight (1/2) n w)) := by
        apply Finset.sum_congr rfl
        intro l hl
        calc
          _ = ∑ w : Path n, letterMass q l *
              (pathWeight q n w * log (pathWeight q n w / pathWeight (1/2) n w)) := by
            apply Finset.sum_congr rfl
            intro w hw
            ring
          _ = _ := by rw [← Finset.mul_sum]
      _ = pathKL q n := by
        simp [pathKL, hnormu, ← Finset.sum_mul]
  rw [hfirst, hsecond]
  rfl


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem letterKL_eq_binary (q : ℝ) :
    letterKL q = klBinary25552 q (1/2) := by
  unfold letterKL klBinary25552
  norm_num [letterMass, hit, Fin.sum_univ_succ, Nat.testBit] <;> ring_nf


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathKL_eq_n_binary (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) : ∀ n,
    pathKL q n = (n:ℝ) * klBinary25552 q (1/2) := by
  intro n
  induction n with
  | zero =>
      classical
      unfold pathKL
      have hratio (w : Path 0) : pathWeight q 0 w / pathWeight (1/2) 0 w = 1 := by simp [pathWeight]
      simp_rw [hratio]
      simp [pathWeight]
  | succ n ih =>
      rw [pathKL_succ q hq0 hq1 n, ih, letterKL_eq_binary]
      push_cast
      ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def eventMass (weights : Path n → ℝ) (E : Finset (Path n)) : ℝ :=
  ∑ w ∈ E, weights w

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem path_event_binary_kl_le (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : Nat) (E : Finset (Path n)) (hE : E.Nonempty) (hEc : Eᶜ.Nonempty) :
    klBinary25552 (eventMass (pathWeight q n) E)
      (eventMass (pathWeight (1/2) n) E) ≤ pathKL q n := by
  let Q : Path n → ℝ := pathWeight q n
  let P : Path n → ℝ := pathWeight (1/2) n
  have hQpos : ∀ w, 0 < Q w := pathWeight_pos q hq0 hq1 n
  have hPpos : ∀ w, 0 < P w := pathWeight_pos (1/2) (by norm_num) (by norm_num) n
  have hQsum : ∑ w, Q w = 1 := pathWeight_sum_one q n
  have hPsum : ∑ w, P w = 1 := pathWeight_sum_one (1/2) n
  have hdp := event_logsum_data_processing25552 Q P hQpos hPpos hQsum hPsum E hE hEc
  have hQsplit := Finset.sum_add_sum_compl E (fun w => Q w)
  have hPsplit := Finset.sum_add_sum_compl E (fun w => P w)
  have hQcomp : eventMass Q Eᶜ = 1 - eventMass Q E := by
    dsimp [eventMass]
    have := hQsplit
    dsimp [Q] at this
    rw [hQsum] at this
    linarith
  have hPcomp : eventMass P Eᶜ = 1 - eventMass P E := by
    dsimp [eventMass]
    have := hPsplit
    dsimp [P] at this
    rw [hPsum] at this
    linarith
  unfold klBinary25552
  dsimp [eventMass] at *
  rw [← hQcomp, ← hPcomp]
  exact hdp

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma eventMass_pos_of_nonempty (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : Nat) (E : Finset (Path n)) (hE : E.Nonempty) :
    0 < eventMass (pathWeight q n) E := by
  dsimp [eventMass]
  rcases hE with ⟨w, hw⟩
  have hterm := pathWeight_pos q hq0 hq1 n w
  have hsum := Finset.single_le_sum
    (fun x hx => le_of_lt (pathWeight_pos q hq0 hq1 n x)) hw
  exact lt_of_lt_of_le hterm hsum

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma eventMass_lt_one_of_complement_nonempty (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : Nat) (E : Finset (Path n)) (hEc : Eᶜ.Nonempty) :
    eventMass (pathWeight q n) E < 1 := by
  have hnorm := pathWeight_sum_one q n
  have hc := eventMass_pos_of_nonempty q hq0 hq1 n Eᶜ hEc
  have hs := Finset.sum_add_sum_compl E (fun w => pathWeight q n w)
  dsimp [eventMass] at hs hc ⊢
  rw [hnorm] at hs
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem path_event_lower_change_measure (q a K : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : Nat) (E : Finset (Path n)) (hE : E.Nonempty) (hEc : Eᶜ.Nonempty)
    (ha : 0 < a) (haQ : a ≤ eventMass (pathWeight q n) E)
    (hK : 0 ≤ K) (hkl : (n:ℝ) * klBinary25552 q (1/2) ≤ K) :
    Real.exp (-(K + log 2)/a) ≤ eventMass (pathWeight (1/2) n) E := by
  have hpath : pathKL q n ≤ K := by
    rw [pathKL_eq_n_binary q hq0 hq1 n]
    exact hkl
  apply change_measure_binary_bound25552 ha haQ
    (eventMass_pos_of_nonempty q hq0 hq1 n E hE)
    (eventMass_lt_one_of_complement_nonempty q hq0 hq1 n E hEc)
    (eventMass_pos_of_nonempty (1/2) (by norm_num) (by norm_num) n E hE)
    (eventMass_lt_one_of_complement_nonempty (1/2) (by norm_num) (by norm_num) n E hEc)
    hK
  exact le_trans (path_event_binary_kl_le q hq0 hq1 n E hE hEc) hpath

end L25552PathKL

open scoped BigOperators

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
abbrev CodeL (n : Nat) := Fin (8^n)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def moveL (mode letter : Nat) : Nat × Nat :=
  let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
    ((mode == 2) && letter.testBit 1)
  let hit := letter.testBit 2
  (if aligned then (if hit then 0 else 2) else 1,
    hit.toNat + (aligned && hit).toNat)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def foldL (code : Nat) (digits : List Nat) (st : Nat × Nat) : Nat × Nat :=
  digits.foldl (fun st pos =>
    let r := moveL st.1 ((code >>> (3*pos)) % 8)
    (r.1, st.2+r.2)) st

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def stateL (code n mode : Nat) : Nat × Nat := foldL code (List.range n) (mode,0)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem digit_shiftL (c i : Nat) :
    (c >>> (3*(i+1))) % 8 = ((c/8) >>> (3*i)) % 8 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hexp : 2^(3*(i+1)) = 8 * 2^(3*i) := by
    have : 3*(i+1) = 3*i+3 := by omega
    rw [this, pow_add]
    norm_num [pow_succ]
    ring
  rw [hexp, Nat.div_div_eq_div_mul]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def codeSplitL (n : Nat) : CodeL (n+1) ≃ (Fin 8 × CodeL n) where
  toFun c := (⟨c.val % 8, Nat.mod_lt _ (by omega)⟩, ⟨c.val / 8, by
    have hc : c.val < 8*8^n := by
      have hp : 8^(n+1)=8*8^n := by rw [pow_succ]; ring
      simpa [hp] using c.isLt
    have hq : 8*(c.val/8) ≤ c.val := by simpa [Nat.mul_comm] using (Nat.div_mul_le_self c.val 8)
    omega
  ⟩)
  invFun p := ⟨p.1.val+8*p.2.val, by
    have hp : 8^(n+1)=8*8^n := by rw [pow_succ]; ring
    rw [hp]
    have hprod : 8*p.2.val < 8*8^n := Nat.mul_lt_mul_of_pos_left p.2.isLt (by omega)
    omega
  ⟩
  left_inv c := by
    apply Fin.ext
    have h:=Nat.mod_add_div c.val 8
    omega
  right_inv p := by
    apply Prod.ext
    · apply Fin.ext
      have hm : (p.1.val + 8*p.2.val) % 8 = p.1.val := by
        rw [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt p.1.isLt]
        norm_num
      exact hm
    · apply Fin.ext
      change (p.1.val+8*p.2.val)/8 = p.2.val
      rw [Nat.add_mul_div_left _ _ (by omega)]
      simp [Nat.div_eq_of_lt p.1.isLt]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem foldShiftL (code : Nat) (digits : List Nat) (st : Nat × Nat) :
    foldL code (digits.map Nat.succ) st = foldL (code/8) digits st := by
  induction digits generalizing st with
  | nil => rfl
  | cons i is ih =>
    simp only [foldL, List.map_cons, List.foldl_cons]
    rw [digit_shiftL code i]
    exact ih _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stateSuccL (code n mode : Nat) :
    stateL code (n+1) mode = foldL (code/8) (List.range n)
      ((moveL mode (code % 8)).1, (moveL mode (code % 8)).2) := by
  unfold stateL
  rw [List.range_succ_eq_map]
  unfold foldL
  simp only [List.foldl_cons]
  simp only [Nat.mul_zero, Nat.shiftRight_zero, Nat.zero_add]
  exact foldShiftL code (List.range n) _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem foldAddL (code : Nat) (digits : List Nat) (m r s : Nat) :
    foldL code digits (m,r+s) =
      let q := foldL code digits (m,s); (q.1,r+q.2) := by
  induction digits generalizing m r s with
  | nil => simp [foldL]
  | cons i is ih =>
    simp only [foldL, List.foldl_cons]
    let z := moveL m ((code >>> (3*i)) % 8)
    have hz := ih z.1 r (s+z.2)
    simp only [Nat.add_assoc]
    change foldL code is (z.1, r+(s+z.2)) =
      ((foldL code is (z.1,s+z.2)).1, r+(foldL code is (z.1,s+z.2)).2)
    exact hz

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem moveRewardLE2L (m l : Nat) : (moveL m l).2 ≤ 2 := by
  change (l.testBit 2).toNat +
    ((((m == 1) && l.testBit 0 && l.testBit 1) || ((m == 2) && l.testBit 1)) && l.testBit 2).toNat ≤ 2
  have h1 : (l.testBit 2).toNat ≤ 1 := by cases l.testBit 2 <;> decide
  have h2 : ((((m == 1) && l.testBit 0 && l.testBit 1) || ((m == 2) && l.testBit 1)) && l.testBit 2).toNat ≤ 1 := by
    generalize h : ((((m == 1) && l.testBit 0 && l.testBit 1) || ((m == 2) && l.testBit 1)) && l.testBit 2) = b
    cases b <;> decide
  omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stateRewardLE2L (n code mode : Nat) : (stateL code n mode).2 ≤ 2*n := by
  induction n generalizing code mode with
  | zero => simp [stateL, foldL]
  | succ n ih =>
    rw [stateSuccL]
    let r := moveL mode (code % 8)
    have hadd := foldAddL (code/8) (List.range n) r.1 r.2 0
    simp only [Nat.add_zero] at hadd
    rw [hadd]
    have hr := moveRewardLE2L mode (code % 8)
    change r.2 ≤ 2 at hr
    have ht := ih (code/8) r.1
    change r.2 + (stateL (code/8) n r.1).2 ≤ 2*(n+1)
    omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stateRewardSuccL (code n mode : Nat) :
    (stateL code (n+1) mode).2 =
      (moveL mode (code % 8)).2 +
        (stateL (code/8) n (moveL mode (code % 8)).1).2 := by
  rw [stateSuccL]
  let z := moveL mode (code % 8)
  have hadd := foldAddL (code/8) (List.range n) z.1 z.2 0
  simp only [Nat.add_zero] at hadd
  rw [hadd]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def qWeightL (reward : Nat) (depth : Int) : ℝ :=
  if (reward : Int) ≤ depth then 1 else (2:ℝ)^(depth - reward)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def qPriceL (n : Nat) (depth : Int) (mode : Nat) : ℝ :=
  ∑ c : CodeL n, qWeightL (stateL c.val n mode).2 depth

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem qWeight_addL (r R : Nat) (depth : Int) :
    qWeightL (r+R) depth = qWeightL R (depth-r) := by
  unfold qWeightL
  have hcond : ((r+R:Int) ≤ depth) ↔ (R:Int) ≤ depth-r := by omega
  by_cases h : ((r+R:Int) ≤ depth)
  · have h' : (R:Int) ≤ depth-r := hcond.mp h
    simp [h,h', sub_sub, Int.cast_add]
  · have h' : ¬ ((R:Int) ≤ depth-r) := fun hR => h (hcond.mpr hR)
    simp [h,h', sub_sub, Int.cast_add]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem qPrice_succL (n : Nat) (depth : Int) (mode : Nat) :
    qPriceL (n+1) depth mode =
      ∑ l : Fin 8, qPriceL n (depth - (moveL mode l.val).2) (moveL mode l.val).1 := by
  unfold qPriceL
  rw [Fintype.sum_equiv (codeSplitL n)
    (fun c : CodeL (n+1) => qWeightL (stateL c.val (n+1) mode).2 depth)
    (fun p : Fin 8 × CodeL n =>
      qWeightL (stateL p.2.val n (moveL mode p.1.val).1).2
        (depth - (moveL mode p.1.val).2)) (by
      intro c
      simp [codeSplitL]
      rw [stateRewardSuccL]
      exact qWeight_addL (moveL mode (c.val % 8)).2
        (stateL (c.val/8) n (moveL mode (c.val % 8)).1).2 depth)]
  rw [Fintype.sum_prod_type]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def natPriceL (n d : Nat) : Nat :=
  ∑ c : CodeL n, 2^(2*n - ((stateL c.val n 0).2 - d))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem qWeight_nat_bridgeL (r n d : Nat) (hr : r ≤ 2*n) :
    (2:ℝ)^(2*n - (r-d)) = (2:ℝ)^(2*n) * qWeightL r (d:Int) := by
  by_cases hrd : r ≤ d
  · simp [qWeightL, hrd]
  · have hdr : d < r := by omega
    have hsub : r-d ≤ 2*n := by omega
    have heq : 2*n - (r-d) + (r-d) = 2*n := Nat.sub_add_cancel hsub
    have hsubInt : (d:Int) - r = -((r-d : Nat) : Int) := by omega
    rw [qWeightL, if_neg (by omega : ¬ (r:Int) ≤ d), hsubInt, zpow_neg, zpow_natCast]
    exact pow_sub₀ (2:ℝ) (by norm_num) hsub

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem natPrice_eq_qPriceL (n d : Nat) :
    (natPriceL n d : ℝ) = (2:ℝ)^(2*n) * qPriceL n (d:Int) 0 := by
  unfold natPriceL qPriceL
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    (∑ c : CodeL n, (2:ℝ)^(2*n - ((stateL c.val n 0).2 - d))) =
        ∑ c : CodeL n, (2:ℝ)^(2*n) * qWeightL (stateL c.val n 0).2 (d:Int) := by
      apply Fintype.sum_congr
      intro c
      exact qWeight_nat_bridgeL (stateL c.val n 0).2 n d (stateRewardLE2L n c.val 0)
    _ = (2:ℝ)^(2*n) * ∑ c : CodeL n, qWeightL (stateL c.val n 0).2 (d:Int) := by
      exact (Finset.mul_sum (Finset.univ : Finset (CodeL n))
        (fun c : CodeL n => qWeightL (stateL c.val n 0).2 (d:Int)) ((2:ℝ)^(2*n))).symm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def natPriceListL (n d : Nat) : Nat :=
  ((List.range (8^n)).map (fun codeWord =>
    2^(2*n - ((stateL codeWord n 0).2 - d)))).sum

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem natPriceList_eq_natPriceL (n d : Nat) :
    natPriceListL n d = natPriceL n d := by
  unfold natPriceListL natPriceL
  calc
    ((List.range (8^n)).map (fun c => 2^(2*n - ((stateL c n 0).2-d)))).sum =
        ∑ c ∈ Finset.range (8^n), 2^(2*n - ((stateL c n 0).2-d)) := by
      rw [← List.sum_toFinset (fun c : Nat => 2^(2*n - ((stateL c n 0).2-d)))
        (List.nodup_range (n:=8^n))]
      rw [List.toFinset_range]
    _ = ∑ c : Fin (8^n), 2^(2*n - ((stateL c.val n 0).2-d)) := by
      simpa using (Fin.sum_univ_eq_sum_range
        (fun c : Nat => 2^(2*n - ((stateL c n 0).2-d))) (8^n)).symm

open Real

namespace Lmeta25552Constants

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma log_two_lower_seven_twelfths : (7:ℝ)/12 ≤ log 2 := by
  have h43 := Real.log_le_sub_one_of_pos (x := (3:ℝ)/4) (by norm_num)
  have h32 := Real.log_le_sub_one_of_pos (x := (2:ℝ)/3) (by norm_num)
  have h43' : log (4/3:ℝ) ≥ 1/4 := by
    rw [show (4:ℝ)/3 = ((3:ℝ)/4)⁻¹ by norm_num, Real.log_inv]
    norm_num at h43 ⊢
    linarith
  have h32' : log (3/2:ℝ) ≥ 1/3 := by
    rw [show (3:ℝ)/2 = ((2:ℝ)/3)⁻¹ by norm_num, Real.log_inv]
    norm_num at h32 ⊢
    linarith
  have hmul : (4:ℝ)/3 * (3/2) = 2 := by norm_num
  rw [← hmul, Real.log_mul (by norm_num) (by norm_num)]
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma log_two_upper_seven_tenths : log 2 ≤ (7:ℝ)/10 := by
  apply (Real.log_le_iff_le_exp (by norm_num)).2
  have hexp : Real.exp ((7:ℝ)/10) = Real.exp ((40:ℝ) * ((7:ℝ)/400)) := by norm_num
  rw [hexp]
  have he := Real.exp_nat_mul ((7:ℝ)/400) 40
  have he' : Real.exp ((40:ℝ) * ((7:ℝ)/400)) = Real.exp ((7:ℝ)/400)^40 := by
    simpa using he
  rw [he']
  have hlin0 := Real.add_one_le_exp ((7:ℝ)/400)
  have hlin : (1:ℝ) + (7:ℝ)/400 ≤ Real.exp ((7:ℝ)/400) := by nlinarith
  have hpow : (2:ℝ) ≤ ((407:ℝ)/400)^40 := by norm_num
  have hlin' : (407:ℝ)/400 ≤ Real.exp ((7:ℝ)/400) := by nlinarith [hlin]
  have hpowle : ((407:ℝ)/400)^40 ≤ Real.exp ((7:ℝ)/400)^40 := by
    exact pow_le_pow_left₀ (by norm_num) hlin' 40
  nlinarith [hpow, hpowle]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma fixed_kl_one : (1:ℝ)/5 * log ((3456:ℝ)/3125) ≤ (11:ℝ)/500 := by
  have hlog := Real.log_le_sub_one_of_pos (x := (3456:ℝ)/3125) (by norm_num)
  nlinarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma fixed_exponent_lt_seven (n : ℕ) (hn : 13 ≤ n) (hn' : n ≤ 110) :
    ((11:ℝ)/500*n + 7/10) / (529*n/(40000+529*n)) < 7 := by
  have hnRlo : (13:ℝ) ≤ n := by exact_mod_cast hn
  have hnRhi : (n:ℝ) ≤ 110 := by exact_mod_cast hn'
  have hlo : 0 ≤ (n:ℝ)-13 := by linarith
  have hhi : 0 ≤ 110-(n:ℝ) := by linarith
  have hquad : (n:ℝ)^2 ≤ 123*n - 1430 := by nlinarith [mul_nonneg hlo hhi]
  have hden : 0 < 40000 + 529*(n:ℝ) := by positivity
  have hpos : 0 < 529*(n:ℝ)/(40000+529*(n:ℝ)) := by positivity
  rw [div_lt_iff₀ hpos]
  have hrw : 7*(529*(n:ℝ)/(40000+529*(n:ℝ))) = (3703*(n:ℝ))/(40000+529*(n:ℝ)) := by ring
  rw [hrw, lt_div_iff₀ hden]
  nlinarith [hquad, hnRlo]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma adaptive_gap_compare (x : ℝ) (hx : 0 ≤ x) (B : ℕ) (hB0 : 1 ≤ B) (hB : 128*x ≤ B) :
    25*x/384 + 25*Real.sqrt x/24 + 25/6 + 7/5 ≤ 12*(B:ℝ)*Real.log 2 := by
  have hlog := log_two_lower_seven_twelfths
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsquare : (Real.sqrt x)^2 = x := Real.sq_sqrt hx
  have hB' : (128:ℝ)*x ≤ (B:ℝ) := hB
  have htarget : (12:ℝ)*(B:ℝ)*Real.log 2 ≥ 7*(B:ℝ) := by nlinarith
  by_cases hx1 : x ≤ 1
  · have hroot : Real.sqrt x ≤ 1 := by nlinarith [Real.sq_sqrt hx]
    have hsmall : 25*x/384 + 25*Real.sqrt x/24 + 25/6 + 7/5 ≤ 7 := by
      nlinarith [hx, hx1, hroot]
    have hbone : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB0
    nlinarith
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hroot : Real.sqrt x ≤ x := by
      nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x]
    have hlarge : 25*x/384 + 25*Real.sqrt x/24 + 25/6 + 7/5 ≤ 7*x := by
      nlinarith [hroot, hx1']
    have hscale : 7*x ≤ 7*(B:ℝ) := by nlinarith [hB']
    nlinarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma adaptive_floor_budget (n D : Nat) (hn : 0 < n) :
    (128:ℝ)*(D:ℝ)^2/n ≤ (1 + 128*D^2/n : Nat) := by
  let m : Nat := 128*D^2
  let q : Nat := m/n
  let r : Nat := m % n
  have hdiv : r + n*q = m := Nat.mod_add_div m n
  have hr : r < n := Nat.mod_lt m hn
  have hcast : (r:ℝ) + (n:ℝ)*(q:ℝ) = (m:ℝ) := by exact_mod_cast hdiv
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hrR : (r:ℝ) < n := by exact_mod_cast hr
  have hmeq : (m:ℝ) = 128*(D:ℝ)^2 := by dsimp [m]; norm_num
  have hfloorUpper : (m:ℝ)/n < (q:ℝ)+1 := by
    have hrd : (r:ℝ)/n < 1 := (div_lt_one hnR).2 hrR
    have hrewrite : (m:ℝ) = (r:ℝ) + (n:ℝ)*(q:ℝ) := hcast.symm
    rw [hrewrite]
    field_simp [ne_of_gt hnR]
    nlinarith
  have hB : ((1 + 128*D^2/n : Nat):ℝ) = 1+(q:ℝ) := by norm_num [q, m]
  rw [hB]
  have hleft : 128*(D:ℝ)^2/n = (m:ℝ)/n := by rw [← hmeq]
  rw [hleft]
  linarith [hfloorUpper]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma adaptive_epsilon_lt_one_tenth (n D : Nat) (hn : 111 ≤ n) (hD : D < n/32) :
    (D:ℝ)/(8*n) + 1/Real.sqrt n < (1:ℝ)/10 := by
  have hnR : (111:ℝ) ≤ n := by exact_mod_cast hn
  have hD' : (D:ℝ) < (n:ℝ)/32 := by
    have hDcast : (D:ℝ) < (n/32:Nat) := by exact_mod_cast hD
    have hdiv : ((n/32:Nat):ℝ) ≤ (n:ℝ)/32 := Nat.cast_div_le
    linarith
  have hsqrt : (1:ℝ)/Real.sqrt n < (123:ℝ)/1280 := by
    have hs : (Real.sqrt n)^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
    have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    have hsq : (1280:ℝ)^2 < (123:ℝ)^2*n := by nlinarith [hnR]
    have hnum : (1:ℝ) < (123:ℝ)/1280*Real.sqrt n := by nlinarith [hs, hsq]
    rw [div_lt_iff₀ hspos]
    norm_num at hnum ⊢
    linarith
  have hlinear : (D:ℝ)/(8*n) < (1:ℝ)/256 := by
    have hnpos : 0 < 8*(n:ℝ) := by positivity
    rw [show (D:ℝ)/(8*n) = (D:ℝ)/(8*(n:ℝ)) by norm_cast, div_lt_iff₀ hnpos]
    nlinarith [hD']
  norm_num at hsqrt
  have hsqrt' : (1:ℝ)/Real.sqrt (n:ℝ) < (123:ℝ)/1280 := by simpa [one_div] using hsqrt
  linarith

end Lmeta25552Constants

open Real Set


namespace Lmeta25552KL

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def kl (e : ℝ) : ℝ :=
  (1/2-e)*log (1-2*e) + (1/2+e)*log (1+2*e)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def logOdds (e : ℝ) : ℝ := log (1+2*e) - log (1-2*e)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def klDeriv (e : ℝ) : ℝ := 25/6*e - logOdds e

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def klSecond (e : ℝ) : ℝ := 25/6 - 4/(1-4*e^2)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma linminus_hasDeriv (e : ℝ) : HasDerivAt (fun x : ℝ => 1-2*x) (-2) e := by
  convert (hasDerivAt_const e (1:ℝ)).sub ((hasDerivAt_id e).const_mul (2:ℝ)) using 1
  · ext x
    simp
  · norm_num

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma linplus_hasDeriv (e : ℝ) : HasDerivAt (fun x : ℝ => 1+2*x) 2 e := by
  convert (hasDerivAt_const e (1:ℝ)).add ((hasDerivAt_id e).const_mul (2:ℝ)) using 1
  · ext x
    simp
  · norm_num

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma kl_hasDeriv (e : ℝ) (he : |e| < 1/2) : HasDerivAt kl (logOdds e) e := by
  have hminus : 1-2*e ≠ 0 := by have := abs_lt.mp he; linarith
  have hplus : 1+2*e ≠ 0 := by have := abs_lt.mp he; linarith
  have hm := HasDerivAt.log (linminus_hasDeriv e) hminus
  have hp := HasDerivAt.log (linplus_hasDeriv e) hplus
  have hleft := (hasDerivAt_const e (1/2:ℝ)).sub (hasDerivAt_id e)
  have hright := (hasDerivAt_const e (1/2:ℝ)).add (hasDerivAt_id e)
  have hprod1 := hleft.mul hm
  have hprod2 := hright.mul hp
  have hsum := hprod1.add hprod2
  convert hsum using 1
  · funext x
    rfl
  · unfold logOdds
    simp [id]
    field_simp [hminus, hplus]
    ring_nf

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma logOdds_hasDeriv (e : ℝ) (he : |e| < 1/2) :
    HasDerivAt logOdds (4/(1-4*e^2)) e := by
  have hminus : 1-2*e ≠ 0 := by have := abs_lt.mp he; linarith
  have hplus : 1+2*e ≠ 0 := by have := abs_lt.mp he; linarith
  have hm := HasDerivAt.log (linminus_hasDeriv e) hminus
  have hp := HasDerivAt.log (linplus_hasDeriv e) hplus
  have hprod : 1-4*e^2 ≠ 0 := by
    have he' := abs_lt.mp he
    nlinarith
  have hplus' : 1+e*2 ≠ 0 := by intro h; apply hplus; nlinarith
  have hminus' : 1-e*2 ≠ 0 := by intro h; apply hminus; nlinarith
  convert hp.sub hm using 1
  · funext x
    rfl
  · field_simp [hminus, hplus, hplus', hminus', hprod]
    ring_nf

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma kl_second_deriv (e : ℝ) (he : |e| < 1/2) :
    deriv klDeriv e = klSecond e := by
  have hh := logOdds_hasDeriv e he
  have hl := (hasDerivAt_id e).const_mul (25/6:ℝ)
  have hg := hl.sub hh
  have h := hg.deriv
  unfold klDeriv klSecond
  have hfun : (fun y : ℝ => 25/6*id y) - logOdds =
      (fun y : ℝ => 25/6*y - logOdds y) := by funext y; rfl
  rw [hfun] at h
  simpa using h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma kl_deriv (e : ℝ) (he : |e| < 1/2) : deriv kl e = logOdds e := (kl_hasDeriv e he).deriv


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def gap (e : ℝ) : ℝ := 25/12*e^2 - kl e

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma gap_hasDeriv (e : ℝ) (he : |e| < 1/2) : HasDerivAt gap (klDeriv e) e := by
  have hs := (hasDerivAt_id e).mul (hasDerivAt_id e)
  have hc := hs.const_mul (25/12:ℝ)
  have hk := kl_hasDeriv e he
  have hg := hc.sub hk
  convert hg using 1
  · funext x
    simp [gap, kl, id, pow_two]
  · unfold klDeriv
    simp only [id_eq]
    norm_num [pow_two]
    ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma abs_lt_half_of_Icc {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/10)) : |x| < 1/2 := by
  rcases hx with ⟨hlo,hhi⟩
  rw [abs_of_nonneg hlo]
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma klSecond_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/10)) : 0 ≤ klSecond x := by
  rcases hx with ⟨hlo,hhi⟩
  have hden : 0 < 1-4*x^2 := by nlinarith
  unfold klSecond
  rw [sub_nonneg]
  rw [div_le_iff₀ hden]
  nlinarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma klDeriv_mono : MonotoneOn klDeriv (Icc (0:ℝ) (1/10)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1/10))
  · intro x hx
    have hlog := logOdds_hasDeriv x (abs_lt_half_of_Icc hx)
    have hlin := (hasDerivAt_id x).const_mul (25/6:ℝ)
    have hc : ContinuousAt klDeriv x := by
      change ContinuousAt (fun y : ℝ => 25/6*y - logOdds y) x
      exact hlin.continuousAt.sub hlog.continuousAt
    exact hc.continuousWithinAt
  · intro x hx
    have hlog := logOdds_hasDeriv x (abs_lt_half_of_Icc (interior_subset hx))
    have hlin := (hasDerivAt_id x).const_mul (25/6:ℝ)
    have hd : DifferentiableAt ℝ klDeriv x := by
      change DifferentiableAt ℝ (fun y : ℝ => 25/6*y - logOdds y) x
      exact hlin.differentiableAt.sub hlog.differentiableAt
    exact hd.differentiableWithinAt
  · intro x hx
    rw [kl_second_deriv x (abs_lt_half_of_Icc (interior_subset hx))]
    exact klSecond_nonneg (interior_subset hx)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma gap_nonneg {e : ℝ} (he : e ∈ Icc (0:ℝ) (1/10)) : 0 ≤ gap e := by
  have hmono : MonotoneOn gap (Icc (0:ℝ) (1/10)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1/10))
    · intro x hx
      exact (gap_hasDeriv x (abs_lt_half_of_Icc hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (gap_hasDeriv x (abs_lt_half_of_Icc (interior_subset hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(gap_hasDeriv x (abs_lt_half_of_Icc (interior_subset hx))).deriv]
      have h0 : (0:ℝ) ∈ Icc (0:ℝ) (1/10) := by norm_num
      have hxD : x ∈ Icc (0:ℝ) (1/10) := interior_subset hx
      have hder : klDeriv 0 ≤ klDeriv x := klDeriv_mono h0 hxD (by linarith [hxD.1])
      have hz : klDeriv 0 = 0 := by simp [klDeriv, logOdds]
      rw [hz] at hder
      exact hder
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) (1/10) := by norm_num
  have he' : 0 ≤ e := he.1
  have hg0 : gap 0 = 0 := by simp [gap, kl]
  have := hmono h0 he he'
  linarith [hg0]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem bernoulli_kl_quadratic (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1/10) :
    (1/2-e)*Real.log (2*(1/2-e)) + (1/2+e)*Real.log (2*(1/2+e)) ≤ 25/12*e^2 := by
  have he : e ∈ Icc (0:ℝ) (1/10) := ⟨he0, he1⟩
  have hgap := gap_nonneg he
  unfold gap kl at hgap
  have hlog1 : Real.log (2*(1/2-e)) = Real.log (1-2*e) := by congr 1 <;> ring
  have hlog2 : Real.log (2*(1/2+e)) = Real.log (1+2*e) := by congr 1 <;> ring
  rw [hlog1,hlog2]
  linarith

end Lmeta25552KL

open Finset BigOperators Real
open L25552Tilt L25552NatBridge L25552PathKL

namespace L25552PriceLower

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def priceFinReal (n d : Nat) : ℝ :=
  ∑ c : Fin (8^n), (2:ℝ)^(2*n - ((stateN c.val n 0).2 - d))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def goodEvent (n d : Nat) : Finset (Path n) :=
  Finset.univ.filter fun w => pathReward (1/2) n 0 w ≤ d

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma uniform_pathWeight (n : Nat) (w : Path n) :
    pathWeight (1/2) n w = (1/8:ℝ)^n := by
  induction n with
  | zero => simp [pathWeight]
  | succ n ih =>
      change letterMass (1/2) (w 0) * pathWeight (1/2) n (Fin.tail w) = (1/8:ℝ)^(n+1)
      rw [letterMass_half, ih, pow_succ]
      ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma power_scale (n : Nat) :
    (1/8:ℝ)^n * (2:ℝ)^(5*n) = (2:ℝ)^(2*n) := by
  have hcancel : (1/8:ℝ)^n * (2:ℝ)^(3*n) = 1 := by
    calc
      (1/8:ℝ)^n * (2:ℝ)^(3*n) = (1/8:ℝ)^n * ((2:ℝ)^3)^n := by rw [pow_mul]
      _ = ((1/8:ℝ) * (2:ℝ)^3)^n := by rw [mul_pow]
      _ = 1 := by norm_num
  have hsplit : 5*n = 3*n + 2*n := by omega
  rw [hsplit, pow_add]
  calc
    (1/8:ℝ)^n * ((2:ℝ)^(3*n) * (2:ℝ)^(2*n)) =
        ((1/8:ℝ)^n * (2:ℝ)^(3*n)) * (2:ℝ)^(2*n) := by ring
    _ = (2:ℝ)^(2*n) := by rw [hcancel, one_mul]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma price_reindex (n d : Nat) : priceFinReal n d =
    ∑ w : Path n, (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)) := by
  unfold priceFinReal
  symm
  let e : Path n ≃ Fin (8^n) := Equiv.ofBijective (pathCodeFin n) (pathCodeFin_bijective n)
  exact Fintype.sum_equiv e
    (fun w : Path n => (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)))
    (fun c : Fin (8^n) => (2:ℝ)^(2*n - ((stateN c.val n 0).2 - d)))
    (by intro w; rfl)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma priceTerm_good (n d : Nat) (w : Path n) (hw : w ∈ goodEvent n d) :
    (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)) = (2:ℝ)^(2*n) := by
  have hr := pathReward_eq_stateN n w (0:Fin 3)
  have hreward : (stateN (pathCode n w) n 0).2 ≤ d := by
    have hle := (Finset.mem_filter.mp hw).2
    have hr' : (stateN (pathCode n w) n 0).2 = pathReward (1/2) n 0 w := by simpa using hr
    rw [hr']
    exact hle
  simp [Nat.sub_eq_zero_of_le hreward]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma priceFinReal_lower_of_mass (n d : Nat) (b : ℝ)
    (hb : b ≤ eventMass (pathWeight (1/2) n) (goodEvent n d)) :
    b * (2:ℝ)^(5*n) ≤ priceFinReal n d := by
  have hmass_eq : eventMass (pathWeight (1/2) n) (goodEvent n d) =
      ∑ w ∈ goodEvent n d, (1/8:ℝ)^n := by
    simp only [eventMass]
    apply Finset.sum_congr rfl
    intro w hw
    exact uniform_pathWeight n w
  have hsum_good :
      (∑ w ∈ goodEvent n d, (2:ℝ)^(2*n)) ≤
      ∑ w : Path n, (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)) := by
    have hleft :
        (∑ w ∈ goodEvent n d, (2:ℝ)^(2*n)) =
        ∑ w ∈ goodEvent n d, (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)) := by
      apply Finset.sum_congr rfl
      intro w hw
      symm
      exact priceTerm_good n d w hw
    rw [hleft]
    have hsplit := Finset.sum_add_sum_compl (goodEvent n d)
      (fun w : Path n => (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)))
    have hnonneg : 0 ≤ ∑ w ∈ (goodEvent n d)ᶜ,
        (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)) := by
      apply Finset.sum_nonneg
      intro w hw
      positivity
    linarith
  have hscaleSum :
      (∑ w ∈ goodEvent n d, (1/8:ℝ)^n) * (2:ℝ)^(5*n) =
      ∑ w ∈ goodEvent n d, (2:ℝ)^(2*n) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    exact power_scale n
  calc
    b * (2:ℝ)^(5*n) ≤
        eventMass (pathWeight (1/2) n) (goodEvent n d) * (2:ℝ)^(5*n) :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = _ := by rw [hmass_eq, hscaleSum]
    _ ≤ priceFinReal n d := by
      calc
        _ ≤ ∑ w : Path n, (2:ℝ)^(2*n - ((stateN (pathCode n w) n 0).2 - d)) := hsum_good
        _ = priceFinReal n d := (price_reindex n d).symm

end L25552PriceLower

namespace L25552PriceLower

open L25552PathKL L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathReward_param_irrel : ∀ (n : Nat) (q q' : ℝ) (m : Fin 3) (w : Path n),
    pathReward q n m w = pathReward q' n m w := by
  intro n
  induction n with
  | zero => intro q q' m w; simp [pathReward]
  | succ n ih =>
      intro q q' m w
      simp only [pathReward]
      congr 1
      exact ih q q' (next m (w 0)) (Fin.tail w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma goodEvent_eq_real_filter (n d : Nat) :
    goodEvent n d = Finset.univ.filter fun w : Path n =>
      (pathReward (1/2) n 0 w : ℝ) ≤ (d:ℝ) := by
  ext w
  simp [goodEvent, Nat.cast_le]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem priceFinReal_lower_change_measure (q K t : ℝ) (n d : Nat)
    (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2)
    (ht : 0 < t) (hgap : meanR q n 0 + t ≤ d)
    (hkl : (n:ℝ) * klBinary25552 q (1/2) ≤ K) (hK : 0 ≤ K)
    (hgoodc : (goodEvent n d)ᶜ.Nonempty) :
    Real.exp (-(K + log 2) / (t^2 / ((n:ℝ)+t^2))) *
      (2:ℝ)^(5*n) ≤ priceFinReal n d := by
  have hq0 : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  let a := t^2 / ((n:ℝ)+t^2)
  have ha : 0 < a := by dsimp [a]; positivity
  have hQ : a ≤ eventMass (pathWeight q n) (goodEvent n d) := by
    have hh := path_reward_lower_event_var3 q hqlo hqhi n 0 (d:ℝ) t ht hgap
    have hsets : (Finset.univ.filter fun w : Path n =>
        (pathReward q n 0 w : ℝ) ≤ (d:ℝ)) = goodEvent n d := by
      ext w
      simp [goodEvent, pathReward_param_irrel n q (1/2) 0 w, Nat.cast_le]
    have hh' : a ≤ eventMass (pathWeight q n)
        (Finset.univ.filter fun w : Path n => (pathReward q n 0 w : ℝ) ≤ (d:ℝ)) := by
      simpa [a, eventMass, CantelliLocal.mass] using hh
    rw [hsets] at hh'
    exact hh'
  have hgood : (goodEvent n d).Nonempty := by
    by_contra hn
    have he : goodEvent n d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he, eventMass] at hQ
    simp at hQ
    linarith
  have hp := path_event_lower_change_measure q a K hq0 hq1 n (goodEvent n d)
    hgood hgoodc ha hQ hK hkl
  exact priceFinReal_lower_of_mass n d (Real.exp (-(K+log 2)/a)) hp

end L25552PriceLower

namespace L25552PriceLower

open L25552PathKL L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem priceFinReal_lower_change_measure_all (q K t : ℝ) (n d : Nat)
    (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2)
    (ht : 0 < t) (hgap : meanR q n 0 + t ≤ d)
    (hkl : (n:ℝ) * klBinary25552 q (1/2) ≤ K) (hK : 0 ≤ K) :
    Real.exp (-(K + log 2) / (t^2 / ((n:ℝ)+t^2))) *
      (2:ℝ)^(5*n) ≤ priceFinReal n d := by
  by_cases hgoodc : (goodEvent n d)ᶜ.Nonempty
  · exact priceFinReal_lower_change_measure q K t n d hqlo hqhi ht hgap hkl hK hgoodc
  · have hc : (goodEvent n d)ᶜ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hgoodc
    have hmass : eventMass (pathWeight (1/2) n) (goodEvent n d) = 1 := by
      have hs := Finset.sum_add_sum_compl (goodEvent n d)
        (fun w : Path n => pathWeight (1/2) n w)
      have hnorm := pathWeight_sum_one (1/2) n
      have hcompl : eventMass (pathWeight (1/2) n) (goodEvent n d)ᶜ = 0 := by
        simp [eventMass, hc]
      rw [hnorm] at hs
      have hsum : eventMass (pathWeight (1/2) n) (goodEvent n d) +
          eventMass (pathWeight (1/2) n) (goodEvent n d)ᶜ = 1 := by
        simpa [eventMass] using hs
      rw [hcompl] at hsum
      linarith
    have hprice := priceFinReal_lower_of_mass n d 1 (by rw [hmass])
    have hlog : 0 ≤ log (2:ℝ) := le_of_lt (Real.log_pos (by norm_num))
    have harg : -(K + log 2) / (t^2 / ((n:ℝ)+t^2)) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
    have hexp : Real.exp (-(K + log 2) / (t^2 / ((n:ℝ)+t^2))) ≤ 1 :=
      Real.exp_le_one_iff.mpr harg
    calc
      _ ≤ 1 * (2:ℝ)^(5*n) := mul_le_mul_of_nonneg_right hexp (by positivity)
      _ ≤ priceFinReal n d := by simpa using hprice

end L25552PriceLower

namespace L25552PriceLower

open L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem first_price_ineq_real (q K t : ℝ) (n d blocks : Nat)
    (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2)
    (ht : 0 < t) (hgap : meanR q n 0 + t ≤ d)
    (hkl : (n:ℝ) * klBinary25552 q (1/2) ≤ K) (hK : 0 ≤ K)
    (hbudget : 1 ≤ (2:ℝ)^(12*blocks) *
      Real.exp (-(K+log 2)/(t^2/((n:ℝ)+t^2)))) :
    (2:ℝ)^(5*n) ≤ (2:ℝ)^(12*blocks) * priceFinReal n d := by
  have hp := priceFinReal_lower_change_measure_all q K t n d hqlo hqhi ht hgap hkl hK
  calc
    (2:ℝ)^(5*n) = 1 * (2:ℝ)^(5*n) := by ring
    _ ≤ ((2:ℝ)^(12*blocks) * Real.exp (-(K+log 2)/(t^2/((n:ℝ)+t^2)))) *
          (2:ℝ)^(5*n) := mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = (2:ℝ)^(12*blocks) *
          (Real.exp (-(K+log 2)/(t^2/((n:ℝ)+t^2))) * (2:ℝ)^(5*n)) := by ring
    _ ≤ (2:ℝ)^(12*blocks) * priceFinReal n d :=
      mul_le_mul_of_nonneg_left hp (by positivity)

end L25552PriceLower

open Finset BigOperators Real
open L25552Tilt L25552NatBridge L25552PathKL L25552PriceLower

namespace L25552Integration

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem stateN_eq_stateL (c n m : Nat) :
    L25552NatBridge.stateN c n m = stateL c n m := by
  rfl


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def finCodeEquiv (n : Nat) : Fin (8^n) ≃ CodeL n := Equiv.refl _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem priceFinReal_eq_natPriceL (n d : Nat) :
    priceFinReal n d = (natPriceL n d : ℝ) := by
  unfold priceFinReal natPriceL
  rw [Nat.cast_sum]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact Fintype.sum_equiv (finCodeEquiv n)
    (fun c : Fin (8^n) => (2:ℝ)^(2*n - ((stateN c.val n 0).2 - d)))
    (fun c : CodeL n => (2:ℝ)^(2*n - ((stateL c.val n 0).2 - d)))
    (by intro c; rfl)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem priceFinReal_eq_target_natPriceList (n d : Nat) :
    priceFinReal n d = (natPriceListL n d : ℝ) := by
  rw [priceFinReal_eq_natPriceL, ← natPriceList_eq_natPriceL]

end L25552Integration

namespace L25552MeanBoundLocal
open L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem meanR_gap_le_fixed_local (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) :
    ∀ n, meanR q n 1 - meanR q n 0 ≤ q / (3 + 2*q) := by
  have hden : 0 < 3 + 2*q := by linarith
  have hc0 : 0 ≤ (1 - 2*q)/4 := by linarith
  intro n
  induction n with
  | zero => simp [meanR]; positivity
  | succ n ih =>
      have hs := meanR_step q n
      have hshape := meanR_shape q n
      have hgap : meanR q (n+1) 1 - meanR q (n+1) 0 =
          q/4 + ((1-2*q)/4) * (meanR q n 1 - meanR q n 0) := by
        rw [hs.2.1, hs.1]
        nlinarith [hshape]
      rw [hgap]
      have hfix : q/4 + ((1-2*q)/4) * (q/(3+2*q)) = q/(3+2*q) := by
        field_simp
        ring
      nlinarith [mul_le_mul_of_nonneg_left ih hc0]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem meanR_initial_le_rate_local (q : ℝ) (hqlo : (2:ℝ)/5 ≤ q) (hqhi : q ≤ 1/2) :
    ∀ n, meanR q n 0 ≤ (n:ℝ) * rate q := by
  have hden : 3 + 2*q ≠ 0 := by linarith
  intro n
  induction n with
  | zero => simp [meanR]
  | succ n ih =>
      have hs := meanR_step q n
      have hgap := meanR_gap_le_fixed_local q hqlo hqhi n
      have hrate : q + q/(3+2*q) = rate q := by
        unfold rate
        field_simp
        ring
      rw [hs.1]
      have hrewrite : meanR q n 1 = meanR q n 0 + (meanR q n 1 - meanR q n 0) := by ring
      rw [hrewrite]
      have hncast : ((n+1:Nat):ℝ) = (n:ℝ)+1 := by norm_num
      rw [hncast]
      nlinarith
end L25552MeanBoundLocal

namespace L25552Integration
open Lmeta25552Constants L25552PriceLower L25552PathKL L25552Tilt L25552MeanBoundLocal

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma small_deficit_d_lower (n d : Nat) (hn : 0 < n)
    (hD : 32*(5*n-8*d) < n) : (159:ℝ)/256*(n:ℝ) ≤ d := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  by_cases h : 5*n ≤ 8*d
  · have hcast : (5:ℝ)*n ≤ 8*d := by exact_mod_cast h
    nlinarith
  · have hsubord : 8*d ≤ 5*n := by omega
    have hsubeq : ((5*n - 8*d:Nat):ℝ) = (5:ℝ)*n - 8*d := by
      rw [Nat.cast_sub hsubord]
      norm_num
    have hratio : (32:ℝ)*((5*n-8*d:Nat):ℝ) < n := by exact_mod_cast hD
    rw [hsubeq] at hratio
    nlinarith

end L25552Integration

namespace L25552Integration
open Lmeta25552Constants L25552PriceLower L25552PathKL L25552Tilt L25552MeanBoundLocal

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma binary_fixed_kl_eq :
    klBinary25552 (2/5) (1/2) = (1:ℝ)/5 * log ((3456:ℝ)/3125) := by
  unfold klBinary25552
  have h1 : (2:ℝ)/5 / (1/2) = 4/5 := by norm_num
  have h2 : (1-(2:ℝ)/5) / (1-(1/2)) = 6/5 := by norm_num
  rw [h1, h2]
  have hprod : (3456:ℝ)/3125 = (4/5)^2 * (6/5)^3 := by norm_num
  rw [hprod, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma medium_first_real (n d : Nat) (hn : 13 ≤ n) (hn' : n ≤ 110)
    (hD : 32*(5*n-8*d) < n) :
    (2:ℝ)^(5*n) ≤ (2:ℝ)^(12*(1+128*(5*n-8*d)^2/n)) * priceFinReal n d := by
  let D : Nat := 5*n-8*d
  let B : Nat := 1+128*D^2/n
  let t : ℝ := (23:ℝ)/200*n
  let K : ℝ := (11:ℝ)/500*n
  have hnpos : 0<n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hnpos
  have hdlo := small_deficit_d_lower n d hnpos (by simpa [D] using hD)
  have hqlo : (2:ℝ)/5 ≤ (2:ℝ)/5 := le_rfl
  have hqhi : (2:ℝ)/5 ≤ 1/2 := by norm_num
  have hrate : rate (2/5) = (48:ℝ)/95 := by norm_num [rate]
  have hmean := meanR_initial_le_rate_local (2/5) hqlo hqhi n
  have hgap : meanR (2/5) n 0 + t ≤ d := by
    dsimp [t]
    rw [hrate] at hmean
    nlinarith [hmean, hdlo]
  have hKL : klBinary25552 (2/5) (1/2) ≤ (11:ℝ)/500 := by
    rw [binary_fixed_kl_eq]
    exact fixed_kl_one
  have hkl : (n:ℝ)*klBinary25552 (2/5) (1/2) ≤ K := by
    dsimp [K]
    calc
      (n:ℝ)*klBinary25552 (2/5) (1/2) ≤ (n:ℝ)*((11:ℝ)/500) :=
        mul_le_mul_of_nonneg_left hKL (by positivity)
      _ = K := by dsimp [K]; ring
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : t^2 / ((n:ℝ)+t^2) =
      (529:ℝ)*n/(40000+529*n) := by
    dsimp [t]
    have hden : (n:ℝ) ≠ 0 := ne_of_gt hnR
    field_simp [hden]
    ring
  have hE : (K+log 2)/(t^2/((n:ℝ)+t^2)) < 7 := by
    rw [hA]
    have hnum : K+log 2 ≤ (11:ℝ)/500*n+7/10 := by
      dsimp [K]
      linarith [log_two_upper_seven_tenths]
    have hconst := fixed_exponent_lt_seven n hn hn'
    have hden : 0 < (529:ℝ)*n/(40000+529*n) := by positivity
    have hcmp : (K+log 2)/((529:ℝ)*n/(40000+529*n)) ≤
        ((11:ℝ)/500*n+7/10)/(529*n/(40000+529*n)) := by
      apply (div_le_div_iff₀ hden hden).2
      nlinarith
    exact lt_of_le_of_lt hcmp hconst
  have hB0 : 1 ≤ B := by dsimp [B]; exact Nat.le_add_right 1 _
  have hloglo := log_two_lower_seven_twelfths
  have hbudgetArg : 0 ≤ (12*(B:ℝ))*log 2 - (K+log 2)/(t^2/((n:ℝ)+t^2)) := by
    have hBcast : (1:ℝ) ≤ B := by exact_mod_cast hB0
    nlinarith [hE, hloglo]
  have hpow : (2:ℝ)^(12*B) = Real.exp ((12*B:Nat)*log 2) := by
    calc
      (2:ℝ)^(12*B) = (Real.exp (log 2))^(12*B) := by rw [Real.exp_log (by norm_num)]
      _ = Real.exp ((12*B:Nat)*log 2) := (Real.exp_nat_mul (log 2) (12*B)).symm
  have hbudget : 1 ≤ (2:ℝ)^(12*B) *
      Real.exp (-(K+log 2)/(t^2/((n:ℝ)+t^2))) := by
    rw [hpow, ← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have harg : (↑(12*B):ℝ)*log 2 + -(K+log 2)/(t^2/((n:ℝ)+t^2)) =
        12*(B:ℝ)*log 2 - (K+log 2)/(t^2/((n:ℝ)+t^2)) := by push_cast; ring
    rw [harg]
    exact hbudgetArg
  have hres := first_price_ineq_real (2/5) K t n d B hqlo hqhi
    (by dsimp [t]; positivity) hgap hkl hK hbudget
  simpa [B,D] using hres

end L25552Integration


namespace L25552Integration
open Lmeta25552Constants Lmeta25552KL L25552PriceLower L25552PathKL L25552Tilt L25552MeanBoundLocal

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma d_ge_five_eighths_sub_deficit (n d D : Nat) (hD : D = 5*n-8*d) :
    (5:ℝ)*(n:ℝ)/8 - (D:ℝ)/8 ≤ d := by
  by_cases h : 5*n ≤ 8*d
  · have hD0 : D = 0 := by rw [hD, Nat.sub_eq_zero_of_le h]
    rw [hD0]
    have hc : (5:ℝ)*(n:ℝ) ≤ 8*d := by exact_mod_cast h
    nlinarith
  · have hsub : 8*d ≤ 5*n := by omega
    have hcast : (D:ℝ) = (5:ℝ)*(n:ℝ) - 8*d := by
      rw [hD, Nat.cast_sub hsub]
      norm_num
    rw [hcast]
    nlinarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma adaptive_kl_eq (q δ : ℝ) (hq : q = 1/2-δ) :
    klBinary25552 q (1/2) =
      (1/2-δ)*log (2*(1/2-δ)) + (1/2+δ)*log (2*(1/2+δ)) := by
  unfold klBinary25552
  rw [hq]
  have h1 : (1/2-δ)/(1/2) = 2*(1/2-δ) := by ring
  have h2 : (1-(1/2-δ))/(1-(1/2)) = 2*(1/2+δ) := by ring
  rw [h1,h2]
  have hcoef : 1-(1/2-δ)=1/2+δ := by ring
  rw [hcoef]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma adaptive_epsilon_lt_real (n D : Nat) (hn : 111 ≤ n)
    (hD : 32*D < n) :
    (D:ℝ)/(8*n) + 1/Real.sqrt n < (1:ℝ)/10 := by
  have hnR : (111:ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0:ℝ) < n := by linarith
  have hs : (Real.sqrt n)^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
  have hspos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hsq : (1280:ℝ)^2 < (123:ℝ)^2*n := by nlinarith [hnR]
  have hnum : (1:ℝ) < (123:ℝ)/1280*Real.sqrt n := by nlinarith [hs,hsq]
  have hroot : 1/Real.sqrt n < (123:ℝ)/1280 := by
    rw [div_lt_iff₀ hspos]
    exact hnum
  have hDcast : (32:ℝ)*(D:ℝ) < n := by exact_mod_cast hD
  have hlin : (D:ℝ)/(8*n) < (1:ℝ)/256 := by
    rw [div_lt_iff₀ (by positivity : (0:ℝ)<8*n)]
    nlinarith [hDcast]
  norm_num at hroot ⊢
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma adaptive_first_real (n d : Nat) (hn : 111 ≤ n)
    (hD : 32*(5*n-8*d) < n) :
    (2:ℝ)^(5*n) ≤ (2:ℝ)^(12*(1+128*(5*n-8*d)^2/n)) * priceFinReal n d := by
  let D : Nat := 5*n-8*d
  let δ : ℝ := (D:ℝ)/(8*n) + 1/Real.sqrt n
  let q : ℝ := 1/2-δ
  let t : ℝ := Real.sqrt n
  let K : ℝ := (25:ℝ)/12 * n * δ^2
  let B : Nat := 1+128*D^2/n
  let x : ℝ := (D:ℝ)^2/n
  have hnpos : 0<n := by omega
  have hnR : 0<(n:ℝ) := by exact_mod_cast hnpos
  have hδlt : δ < 1/10 := by
    simpa [δ,D] using adaptive_epsilon_lt_real n (5*n-8*d) hn (by simpa [D] using hD)
  have hδnonneg : 0≤δ := by dsimp [δ]; positivity
  have hqlo : (2:ℝ)/5 ≤ q := by dsimp [q]; linarith
  have hqhi : q≤1/2 := by dsimp [q]; linarith
  have hq : q=1/2-δ := rfl
  have ht : 0<t := by dsimp [t]; exact Real.sqrt_pos.2 hnR
  have hrootSq : t^2=(n:ℝ) := by dsimp [t]; exact Real.sq_sqrt (le_of_lt hnR)
  have hdlower := d_ge_five_eighths_sub_deficit n d D (by rfl)
  have hdeltaN : δ*(n:ℝ)=(D:ℝ)/8+t := by
    dsimp [δ,t]
    have hs : Real.sqrt (n:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
    have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnR
    field_simp [hs,hnne]
    nlinarith [Real.sq_sqrt (le_of_lt hnR)]
  have hrate := rate_shift q hqlo hqhi
  have hmean0 := meanR_initial_le_rate_local q hqlo hqhi n
  have hmeanBound : meanR q n 0 ≤ (n:ℝ)*(5/8-δ) := by
    have hr : rate q≤(5:ℝ)/8-δ := by simpa [q] using hrate
    exact le_trans hmean0 (mul_le_mul_of_nonneg_left hr (by positivity))
  have hgap : meanR q n 0+t≤d := by
    calc
      meanR q n 0+t ≤ (n:ℝ)*(5/8-δ)+t := by linarith [hmeanBound]
      _ = (5:ℝ)*(n:ℝ)/8-(D:ℝ)/8 := by nlinarith [hdeltaN]
      _ ≤ d := hdlower
  have hklEq := adaptive_kl_eq q δ hq
  have hklQuad := bernoulli_kl_quadratic δ hδnonneg (le_of_lt hδlt)
  have hklBase : klBinary25552 q (1/2)≤(25:ℝ)/12*δ^2 := by
    rw [hklEq]
    exact hklQuad
  have hkl : (n:ℝ)*klBinary25552 q (1/2)≤K := by
    dsimp [K]
    calc
      (n:ℝ)*klBinary25552 q (1/2) ≤ (n:ℝ)*((25:ℝ)/12*δ^2) :=
        mul_le_mul_of_nonneg_left hklBase (by positivity)
      _ = K := by dsimp [K]; ring
  have hK : 0≤K := by dsimp [K]; positivity
  have hA : t^2/((n:ℝ)+t^2)=1/2 := by
    rw [hrootSq]
    field_simp
    norm_num
  have hsqrtx : Real.sqrt x=(D:ℝ)/t := by
    dsimp [x,t]
    rw [Real.sqrt_div (sq_nonneg (D:ℝ)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg D)]
  have hnDeltaSq : (n:ℝ)*δ^2=x/64+Real.sqrt x/4+1 := by
    have hsq : (n:ℝ)*δ^2=(δ*(n:ℝ))^2/(n:ℝ) := by
      field_simp [ne_of_gt hnR]
    rw [hsq,hdeltaN]
    have hnn : (n:ℝ)≠0 := ne_of_gt hnR
    rw [hsqrtx]
    dsimp [x]
    field_simp [hnn,ne_of_gt ht]
    nlinarith [hrootSq]
  have hE : (K+log 2)/(t^2/((n:ℝ)+t^2)) ≤
      25*x/384+25*Real.sqrt x/24+25/6+7/5 := by
    rw [hA]
    have hKval : K=(25:ℝ)/12*((n:ℝ)*δ^2) := by dsimp [K]; ring
    rw [hKval,hnDeltaSq]
    have hlog := log_two_upper_seven_tenths
    nlinarith
  have hx : 0≤x := by dsimp [x]; positivity
  have hB0 : 1≤B := by dsimp [B]; exact Nat.le_add_right 1 _
  have hB : (128:ℝ)*x≤B := by
    have hfloor := adaptive_floor_budget n D hnpos
    push_cast at hfloor
    have hleft : (128:ℝ)*(D:ℝ)^2/(n:ℝ) =
        (128:ℝ)*((D:ℝ)^2/(n:ℝ)) := by
      field_simp [ne_of_gt hnR]
    rw [hleft] at hfloor
    simpa [x,B] using hfloor
  have hbudgetArg : 0≤(12*(B:ℝ))*log 2-(K+log 2)/(t^2/((n:ℝ)+t^2)) := by
    have hcmp := adaptive_gap_compare x hx B hB0 hB
    nlinarith [hcmp,hE]
  have hpow : (2:ℝ)^(12*B)=Real.exp ((12*B:Nat)*log 2) := by
    calc
      (2:ℝ)^(12*B)=(Real.exp (log 2))^(12*B) := by rw [Real.exp_log (by norm_num)]
      _=Real.exp ((12*B:Nat)*log 2) := (Real.exp_nat_mul (log 2) (12*B)).symm
  have hbudget : 1≤(2:ℝ)^(12*B)*Real.exp (-(K+log 2)/(t^2/((n:ℝ)+t^2))) := by
    rw [hpow,←Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    have harg : (↑(12*B):ℝ)*log 2+-(K+log 2)/(t^2/((n:ℝ)+t^2))=
        12*(B:ℝ)*log 2-(K+log 2)/(t^2/((n:ℝ)+t^2)) := by push_cast; ring
    rw [harg]
    exact hbudgetArg
  have hres := first_price_ineq_real q K t n d B hqlo hqhi ht hgap hkl hK hbudget
  simpa [B,D] using hres

end L25552Integration

namespace L25552Integration

 theorem medium_first_nat (n d : Nat) (hn : 13 ≤ n) (hn' : n ≤ 110)
    (hD : 32*(5*n-8*d) < n) :
    2^(5*n) ≤ 2^(12*(1+128*(5*n-8*d)^2/n)) * natPriceListL n d := by
  have h := medium_first_real n d hn hn' hD
  rw [priceFinReal_eq_target_natPriceList] at h
  exact_mod_cast h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem adaptive_first_nat (n d : Nat) (hn : 111 ≤ n)
    (hD : 32*(5*n-8*d) < n) :
    2^(5*n) ≤ 2^(12*(1+128*(5*n-8*d)^2/n)) * natPriceListL n d := by
  have h := adaptive_first_real n d hn hD
  rw [priceFinReal_eq_target_natPriceList] at h
  exact_mod_cast h

end L25552Integration

namespace L25552Integration
open L25552Tilt L25552PriceLower L25552PathKL

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
abbrev NoHitLetter := {l : Fin 8 // hit l = false}

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def zeroHitEvent (n : Nat) : Finset (Path n) :=
  Finset.univ.filter fun w => ∀ i, hit (w i) = false

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def zeroHitPathEquiv (n : Nat) :
    {w : Path n // w ∈ zeroHitEvent n} ≃ (Fin n → NoHitLetter) where
  toFun w i := ⟨w.1 i, (Finset.mem_filter.mp w.2).2 i⟩
  invFun f := ⟨fun i => (f i).val, by
    apply Finset.mem_filter.mpr
    constructor
    · simp
    · intro i
      exact (f i).property⟩
  left_inv w := by
    apply Subtype.ext
    funext i
    rfl
  right_inv f := by
    apply funext
    intro i
    apply Subtype.ext
    rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma card_noHitLetter : Fintype.card NoHitLetter = 4 := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma card_zeroHitEvent (n : Nat) : (zeroHitEvent n).card = 4^n := by
  classical
  have hc := Fintype.card_congr (zeroHitPathEquiv n)
  rw [Fintype.card_fun, card_noHitLetter] at hc
  have hcard : Fintype.card {w : Path n // w ∈ zeroHitEvent n} = 4^n := by
    simpa [zeroHitEvent] using hc
  exact (Fintype.card_coe (zeroHitEvent n)).symm.trans hcard

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma zeroHitEvent_mass (n : Nat) :
    eventMass (pathWeight (1/2) n) (zeroHitEvent n) = (1/2:ℝ)^n := by
  classical
  unfold eventMass
  simp_rw [uniform_pathWeight]
  calc
    (∑ w ∈ zeroHitEvent n, (1/8:ℝ)^n) =
        (↑(zeroHitEvent n).card:ℝ) * (1/8:ℝ)^n := by simp [Finset.sum_const]
    _ = (4:ℝ)^n * (1/8:ℝ)^n := by simp [card_zeroHitEvent]
    _ = (1/2:ℝ)^n := by
      rw [← mul_pow]
      norm_num

end L25552Integration

namespace L25552Integration

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma zeroHit_reward_zero (q : ℝ) (n : Nat) (m : Fin 3) (w : Path n)
    (hw : w ∈ zeroHitEvent n) : pathReward q n m w = 0 := by
  revert m
  induction n with
  | zero => intro m; simp [pathReward]
  | succ n ih =>
      intro m
      have hmem : ∀ i, hit (w i) = false := (Finset.mem_filter.mp hw).2
      simp only [pathReward]
      have hg : gain m (w 0) = 0 := by
        unfold gain
        rw [hmem 0]
        simp
      rw [hg]
      have htail : Fin.tail w ∈ zeroHitEvent n := by
        apply Finset.mem_filter.mpr
        constructor
        · simp
        · intro i
          exact hmem i.succ
      simpa using ih (Fin.tail w) htail (next m (w 0))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma zeroHit_mass_le_good (n d : Nat) :
    eventMass (pathWeight (1/2) n) (zeroHitEvent n) ≤
      eventMass (pathWeight (1/2) n) (goodEvent n d) := by
  classical
  have hsub : zeroHitEvent n ⊆ goodEvent n d := by
    intro w hw
    simp only [goodEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zeroHit_reward_zero (1/2) n 0 w hw]
    omega
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun w hw hnot => le_of_lt (pathWeight_pos (1/2) (by norm_num) (by norm_num) n w))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma zeroHit_price_lower_real (n d : Nat) :
    (2:ℝ)^(4*n) ≤ priceFinReal n d := by
  have hmass : (1/2:ℝ)^n ≤ eventMass (pathWeight (1/2) n) (goodEvent n d) := by
    rw [← zeroHitEvent_mass n]
    exact zeroHit_mass_le_good n d
  have hp := priceFinReal_lower_of_mass n d ((1/2:ℝ)^n) hmass
  have hscale : (1/2:ℝ)^n*(2:ℝ)^(5*n)=(2:ℝ)^(4*n) := by
    calc
      (1/2:ℝ)^n*(2:ℝ)^(5*n)=((1/2:ℝ)*(2:ℝ)^5)^n := by
        rw [pow_mul, ←mul_pow]
      _=(2:ℝ)^(4*n) := by
        rw [pow_mul]
        norm_num
  linarith

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma zeroHit_price_nat (n d B : Nat) (hneed : n≤12*B) :
    2^(5*n) ≤ 2^(12*B)*natPriceListL n d := by
  have hp := zeroHit_price_lower_real n d
  rw [priceFinReal_eq_target_natPriceList] at hp
  have hpow : 5*n≤12*B+4*n := by omega
  have hpown : 2^(5*n)≤2^(12*B+4*n) := Nat.pow_le_pow_right (by omega) hpow
  have hprice : 2^(4*n)≤natPriceListL n d := by exact_mod_cast hp
  calc
    2^(5*n)≤2^(12*B+4*n) := hpown
    _=2^(12*B)*2^(4*n) := by rw [pow_add]
    _≤2^(12*B)*natPriceListL n d := Nat.mul_le_mul_left _ hprice

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem lower_first_nat_all (n d : Nat) (hn : 0<n) :
    2^(5*n)≤2^(12*(1+128*(5*n-8*d)^2/n))*natPriceListL n d := by
  let D : Nat := 5*n-8*d
  let B : Nat := 1+128*D^2/n
  by_cases hnsmall : n≤12
  · have hB : 1≤B := by dsimp [B]; exact Nat.le_add_right 1 _
    have hneed : n≤12*B := by omega
    have h := zeroHit_price_nat n d B hneed
    simpa [B,D] using h
  · have hnlarge : 13≤n := by omega
    by_cases hratio : 32*D<n
    · by_cases hmedium : n≤110
      · have h := medium_first_nat n d hnlarge hmedium (by simpa [D] using hratio)
        simpa [D] using h
      · have hn111 : 111≤n := by omega
        have h := adaptive_first_nat n d hn111 (by simpa [D] using hratio)
        simpa [D] using h
    · have hneedD : n≤32*D := by omega
      have hquot : 4*D≤128*D^2/n := by
        apply (Nat.le_div_iff_mul_le hn).2
        nlinarith
      have hB : 1+4*D≤B := by
        dsimp [B]
        exact Nat.add_le_add_left hquot 1
      have hneed : n≤12*B := by omega
      have h := zeroHit_price_nat n d B hneed
      simpa [B,D] using h

end L25552Integration

open Finset L25552Tilt Real

namespace L25552Upper

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def compStep (m : Fin 3) (l : Fin 8) : ℝ :=
  8 * (gain m l : ℝ) - 5 + (next m l).val - m.val

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem compStep_bounds (m : Fin 3) (l : Fin 8) :
    -10 ≤ compStep m l ∧ compStep m l ≤ 10 := by
  fin_cases m <;> fin_cases l <;>
    norm_num [compStep, gain, next, aligned, hit, Nat.testBit]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem compStep_mean (m : Fin 3) :
    (∑ l : Fin 8, compStep m l) = 0 := by
  fin_cases m <;>
    norm_num [compStep, gain, next, aligned, hit, Nat.testBit,
      Fin.sum_univ_succ] <;> ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem uniform_compStep_mgf (m : Fin 3) (t : ℝ) :
    (8:ℝ)⁻¹ * ∑ l : Fin 8, exp (t * compStep m l) ≤ exp (50*t^2) := by
  have hterm (l : Fin 8) : exp (t * compStep m l) ≤
      cosh (10*t) + (compStep m l / 10) * sinh (10*t) := by
    have hb := compStep_bounds m l
    have habs : |compStep m l / 10| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hb.1, hb.2]
    have h := Real.exp_mul_le_cosh_add_mul_sinh habs (10*t)
    have heq : compStep m l / 10 * (10*t) = t * compStep m l := by ring
    rw [heq] at h
    exact h
  have hsum := Finset.sum_le_sum (fun l (_ : l ∈ Finset.univ) => hterm l)
  have hmean := compStep_mean m
  have hsumrhs : (∑ l : Fin 8, (cosh (10*t) + (compStep m l / 10) * sinh (10*t))) =
      8 * cosh (10*t) := by
    rw [Finset.sum_add_distrib]
    have hconst : (∑ _l : Fin 8, cosh (10*t)) = 8 * cosh (10*t) := by simp
    have hvar : (∑ l : Fin 8, (compStep m l / 10) * sinh (10*t)) = 0 := by
      calc
        _ = ∑ l : Fin 8, compStep m l * (sinh (10*t) / 10) := by
          apply Finset.sum_congr rfl
          intro l hl
          ring
        _ = (∑ l : Fin 8, compStep m l) * (sinh (10*t) / 10) := by
          rw [Finset.sum_mul]
        _ = 0 := by rw [hmean]; ring
    rw [hconst, hvar]
    ring
  have hcosh := Real.cosh_le_exp_half_sq (10*t)
  calc
    (8:ℝ)⁻¹ * ∑ l : Fin 8, exp (t * compStep m l)
      ≤ (8:ℝ)⁻¹ * ∑ l : Fin 8,
          (cosh (10*t) + (compStep m l / 10) * sinh (10*t)) := by
            apply mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = cosh (10*t) := by rw [hsumrhs]; field_simp
    _ ≤ exp (50*t^2) := by
      calc
        cosh (10*t) ≤ exp ((10*t)^2/2) := hcosh
        _ = exp (50*t^2) := by congr 1; ring

end L25552Upper

namespace L25552Upper

open L25552Tilt

 def compPath : (n : Nat) → Fin 3 → Path n → ℝ
  | 0, _, _ => 0
  | n+1, m, w => compStep m (w 0) + compPath n (next m (w 0)) (Fin.tail w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem compPath_telescopes : ∀ n (m : Fin 3) (w : Path n),
    compPath n m w = 8 * (pathReward (1/2) n m w : ℝ) - 5*n +
      (runMode n m w).val - m.val := by
  intro n
  induction n with
  | zero => intro m w; simp [compPath, pathReward, runMode]
  | succ n ih =>
    intro m w
    simp only [compPath, pathReward, runMode]
    rw [ih]
    simp only [Nat.cast_succ, Nat.cast_ofNat]
    unfold compStep
    push_cast
    ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def pathExpAvg (t : ℝ) (n : Nat) (m : Fin 3) : ℝ :=
  ∑ w : Path n, pathWeight (1/2) n w * exp (t * compPath n m w)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathExpAvg_eq_recMgf (t : ℝ) : ∀ n m,
    pathExpAvg t n m = recMgf25552 next compStep t n m := by
  intro n
  induction n with
  | zero => intro m; simp [pathExpAvg, pathWeight, compPath, recMgf25552, L25552Tilt.Path]
  | succ n ih =>
    intro m
    let e := Fin.consEquiv (fun _ : Fin (n+1) => Fin 8)
    have heq : pathExpAvg t (n+1) m =
        ∑ p : Fin 8 × Path n,
          letterMass (1/2) p.1 * pathWeight (1/2) n p.2 *
            exp (t * (compStep m p.1 + compPath n (next m p.1) p.2)) := by
      unfold pathExpAvg
      exact Fintype.sum_equiv e.symm
        (fun w => pathWeight (1/2) (n+1) w * exp (t * compPath (n+1) m w))
        (fun p => letterMass (1/2) p.1 * pathWeight (1/2) n p.2 *
          exp (t * (compStep m p.1 + compPath n (next m p.1) p.2))) (by
            intro w
            simp [pathWeight, compPath, e])
    rw [heq, Fintype.sum_prod_type]
    have hinner (l : Fin 8) :
        (∑ w : Path n, letterMass (1/2) l * pathWeight (1/2) n w *
          exp (t * (compStep m l + compPath n (next m l) w))) =
        letterMass (1/2) l * exp (t * compStep m l) * pathExpAvg t n (next m l) := by
      calc
        _ = ∑ w : Path n, letterMass (1/2) l * exp (t * compStep m l) *
              (pathWeight (1/2) n w * exp (t * compPath n (next m l) w)) := by
          apply Finset.sum_congr rfl
          intro w hw
          rw [show t * (compStep m l + compPath n (next m l) w) =
              t * compStep m l + t * compPath n (next m l) w by ring, Real.exp_add]
          ring
        _ = letterMass (1/2) l * exp (t * compStep m l) *
              (∑ w : Path n, pathWeight (1/2) n w * exp (t * compPath n (next m l) w)) := by
          rw [Finset.mul_sum]
        _ = letterMass (1/2) l * exp (t * compStep m l) * pathExpAvg t n (next m l) := rfl
    simp_rw [hinner, ih]
    have hmass (l : Fin 8) : letterMass (1/2) l = (8:ℝ)⁻¹ := by
      unfold letterMass
      split <;> norm_num
    simp_rw [hmass]
    simp [recMgf25552]
    calc
      _ = ∑ x : Fin 8, (8:ℝ)⁻¹ *
            (exp (t * compStep m x) * recMgf25552 next compStep t n (next m x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
      _ = (8:ℝ)⁻¹ * ∑ x : Fin 8,
            exp (t * compStep m x) * recMgf25552 next compStep t n (next m x) := by
          rw [Finset.mul_sum]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathExpAvg_bound (t : ℝ) (ht : 0 ≤ t) (n : Nat) (m : Fin 3) :
    pathExpAvg t n m ≤ exp (50 * n * t^2) := by
  rw [pathExpAvg_eq_recMgf]
  exact recMgf25552_bound next compStep t (fun s => uniform_compStep_mgf s t) n m

end L25552Upper

namespace L25552Upper

open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def letterMeasure25552 : MeasureTheory.Measure (Fin 8) :=
  (8:ENNReal)⁻¹ • (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 8))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem letterMeasure25552_prob : IsProbabilityMeasure letterMeasure25552 := by
  rw [MeasureTheory.isProbabilityMeasure_iff]
  have huniv : letterMeasure25552 Set.univ = (8:ENNReal)⁻¹ * 8 := by
    simp [letterMeasure25552, Measure.count_apply]
  rw [huniv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem compStep_tight_bounds (m : Fin 3) (l : Fin 8) :
    -6 ≤ compStep m l ∧ compStep m l ≤ 10 := by
  fin_cases m <;> fin_cases l <;>
    norm_num [compStep, gain, next, aligned, hit, Nat.testBit]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem uniform_compStep_mgf_sharp (m : Fin 3) (t : ℝ) (ht : 0 < t) :
    (8:ℝ)⁻¹ * ∑ l : Fin 8, exp (t * (-compStep m l)) ≤ exp (32*t^2) := by
  letI : IsProbabilityMeasure letterMeasure25552 := letterMeasure25552_prob
  let X : Fin 8 → ℝ := fun l => -compStep m l
  have hX : AEMeasurable X letterMeasure25552 := by
    fun_prop
  have hb : ∀ᵐ l ∂letterMeasure25552, X l ∈ Set.Icc (-10:ℝ) 6 := by
    apply ae_of_all
    intro l
    have h := compStep_tight_bounds m l
    change -compStep m l ∈ Set.Icc (-10:ℝ) 6
    simp only [Set.mem_Icc]
    constructor <;> linarith
  have hmean : letterMeasure25552[X] = 0 := by
    change (∫ l, X l ∂letterMeasure25552) = 0
    rw [show letterMeasure25552 = (8:ENNReal)⁻¹ •
        (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 8)) by rfl,
      MeasureTheory.integral_smul_measure, MeasureTheory.integral_count]
    have hcoef : ((8:ENNReal)⁻¹).toReal = (8:ℝ)⁻¹ := by norm_num
    rw [hcoef]
    change (8:ℝ)⁻¹ * ∑ l : Fin 8, (-compStep m l) = 0
    have hsum0 : (∑ l : Fin 8, (-compStep m l)) = 0 := by
      rw [Finset.sum_neg_distrib, compStep_mean]
      simp
    rw [hsum0]
    simp
  have hmgf := ProbabilityTheory.mgf_le_of_mem_Icc_of_integral_eq_zero hX hb hmean ht
  have hsum : mgf X letterMeasure25552 t =
      (8:ℝ)⁻¹ * ∑ l : Fin 8, exp (t * (-compStep m l)) := by
    rw [mgf, show letterMeasure25552 = (8:ENNReal)⁻¹ •
        (MeasureTheory.Measure.count : MeasureTheory.Measure (Fin 8)) by rfl,
      MeasureTheory.integral_smul_measure, MeasureTheory.integral_count]
    have hcoef : ((8:ENNReal)⁻¹).toReal = (8:ℝ)⁻¹ := by norm_num
    rw [hcoef]
    rfl
  rw [hsum] at hmgf
  have hnorm : ‖(6:ℝ)-(-10)‖₊ = (16:NNReal) := by norm_num
  rw [hnorm] at hmgf
  have hexp : ((↑(16:NNReal) / 2)^2 * t^2 / 2) = 32*t^2 := by norm_num; ring
  rw [hexp] at hmgf
  exact hmgf

end L25552Upper

namespace L25552Upper

open L25552Tilt

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem uniform_compStep_mgf_neg (m : Fin 3) (t : ℝ) (ht : t < 0) :
    (8:ℝ)⁻¹ * ∑ l : Fin 8, exp (t * compStep m l) ≤ exp (32*t^2) := by
  have h := uniform_compStep_mgf_sharp m (-t) (by linarith)
  have hsum : (∑ l : Fin 8, exp (t * compStep m l)) =
      ∑ l : Fin 8, exp ((-t) * (-compStep m l)) := by
    apply Finset.sum_congr rfl
    intro l hl
    congr 1
    ring
  rw [hsum]
  have hpow : 32 * (-t)^2 = 32*t^2 := by ring
  rw [hpow] at h
  exact h

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem recMgf25552_bound32 {S A : Type*} [Fintype A] [Nonempty A]
    (next : S → A → S) (gain : S → A → ℝ) (t : ℝ)
    (hstep : ∀ s, (Fintype.card A : ℝ)⁻¹ *
       ∑ a : A, Real.exp (t * gain s a) ≤ Real.exp (32 * t ^ 2)) :
    ∀ n s, recMgf25552 next gain t n s ≤ Real.exp (32 * (n : ℝ) * t ^ 2) := by
  intro n
  induction n with
  | zero => intro s; simp [recMgf25552]
  | succ n ih =>
    intro s
    simp only [recMgf25552]
    have hc : 0 ≤ (Fintype.card A : ℝ)⁻¹ := by positivity
    calc
      (Fintype.card A : ℝ)⁻¹ *
          ∑ a : A, Real.exp (t * gain s a) * recMgf25552 next gain t n (next s a)
          ≤ (Fintype.card A : ℝ)⁻¹ *
             ∑ a : A, Real.exp (t * gain s a) * Real.exp (32 * (n : ℝ) * t ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ hc
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (ih (next s a)) (le_of_lt (Real.exp_pos _))
      _ = ((Fintype.card A : ℝ)⁻¹ *
             ∑ a : A, Real.exp (t * gain s a)) * Real.exp (32 * (n : ℝ) * t ^ 2) := by
            rw [← Finset.sum_mul]
            ring
      _ ≤ Real.exp (32 * t ^ 2) * Real.exp (32 * (n : ℝ) * t ^ 2) := by
            exact mul_le_mul_of_nonneg_right (hstep s) (le_of_lt (Real.exp_pos _))
      _ = Real.exp (32 * ((n+1 : ℕ) : ℝ) * t ^ 2) := by
            rw [← Real.exp_add]
            congr 1
            push_cast
            ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem pathExpAvg_bound_neg (t : ℝ) (ht : t < 0) (n : Nat) (m : Fin 3) :
    pathExpAvg t n m ≤ exp (32 * n * t^2) := by
  rw [pathExpAvg_eq_recMgf]
  exact recMgf25552_bound32 next compStep t
    (fun s => uniform_compStep_mgf_neg s t ht) n m

end L25552Upper

open Finset


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem cdf_from_mgf_hoeffding25552 {α : Type*} [Fintype α]
    (p : α → ℝ) (S : α → ℝ) (n A : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hn : 0 < n) (hA : 0 ≤ A)
    (hmgf : (∑ a : α, p a * Real.exp (-(A / (64*n)) * S a)) ≤
      Real.exp (32*n*(A/(64*n))^2)) :
    (∑ a : α, if S a ≤ -A then p a else 0) ≤ Real.exp (-(A^2/(128*n))) := by
  let t : ℝ := A / (64*n)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpoint (a : α) : (if S a ≤ -A then p a else 0) ≤
      p a * (Real.exp (-t*A) * Real.exp (-t*S a)) := by
    by_cases he : S a ≤ -A
    · simp only [if_pos he]
      have hfactor : 1 ≤ Real.exp (-t*A) * Real.exp (-t*S a) := by
        rw [← Real.exp_add]
        have : 0 ≤ -t*A + -t*S a := by nlinarith
        simpa using (Real.exp_le_exp.mpr this)
      nlinarith [hp a]
    · simp only [if_neg he]
      exact mul_nonneg (hp a) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  calc
    ∑ a : α, (if S a ≤ -A then p a else 0)
      ≤ ∑ a : α, p a * (Real.exp (-t*A) * Real.exp (-t*S a)) :=
        sum_le_sum fun a _ => hpoint a
    _ = Real.exp (-t*A) * (∑ a : α, p a * Real.exp (-t*S a)) := by
        calc
          _ = ∑ a : α, Real.exp (-t*A) * (p a * Real.exp (-t*S a)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = _ := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-t*A) * Real.exp (32*n*t^2) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
        simpa [t] using hmgf
    _ = Real.exp (-(A^2/(128*n))) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [t]
        field_simp
        <;> ring


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem large_block_arithmetic25552 (n D k : Nat)
    (hn : 0 < n) (hD : D ≤ 5*n) (hk : k = D^2 / (200*n)) (hk2 : 2 ≤ k) :
    16 ≤ n ∧ 80 ≤ D ∧ 40*k ≤ D := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hDR : (D:ℝ) ≤ 5*n := by exact_mod_cast hD
  have hdiv := Nat.div_mul_le_self (D^2) (200*n)
  rw [← hk] at hdiv
  have hdivR : (k:ℝ) * (200*n) ≤ (D:ℝ)^2 := by
    exact_mod_cast hdiv
  have hDsq : 400*(n:ℝ) ≤ (D:ℝ)^2 := by
    have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk2
    nlinarith [hdivR]
  have hn16 : 16 ≤ n := by
    have hnR16 : (16:ℝ) ≤ n := by nlinarith [hDR, hDsq]
    exact_mod_cast hnR16
  have hD80 : 80 ≤ D := by
    have hD80R : (80:ℝ) ≤ D := by nlinarith [hDsq, hn16]
    exact_mod_cast hD80R
  have hdivN : k * (200*n) ≤ D^2 := by
    rw [hk]
    exact Nat.div_mul_le_self (D^2) (200*n)
  have hdivR' : (k:ℝ) * (200*n) ≤ (D:ℝ)^2 := by exact_mod_cast hdivN
  have hKupper : (k:ℝ) ≤ (D:ℝ)^2/(200*n) := by
    exact (le_div_iff₀ (by positivity : (0:ℝ) < 200*n)).2 hdivR' 
  have h40R : (40:ℝ)*k ≤ D := by
    calc
      40*k ≤ 40*((D:ℝ)^2/(200*n)) := by nlinarith [hKupper]
      _ = (D:ℝ)^2/(5*n) := by field_simp; ring
      _ ≤ D := (div_le_iff₀ (by positivity : (0:ℝ) < 5*n)).2 (by nlinarith [hDR])
  have h40 : 40*k ≤ D := by exact_mod_cast h40R
  exact ⟨hn16,hD80,h40⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem exp_tail_le_pow25552 (n D k A : Nat)
    (hn : 0 < n) (hD : D ≤ 5*n) (hk : k = D^2/(200*n))
    (hk2 : 2 ≤ k) (hA : 3*D ≤ 4*A) :
    Real.exp (-((A:ℝ)^2/(128*n))) ≤ ((2:ℝ)^k)⁻¹ := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hDk : (k:ℝ) ≤ (D:ℝ)^2/(200*n) := by
    have hdivN : k * (200*n) ≤ D^2 := by
      rw [hk]
      exact Nat.div_mul_le_self (D^2) (200*n)
    have hden : (0:ℝ) < 200*n := by positivity
    have hcast : (k:ℝ) * (200*n:ℝ) ≤ (D:ℝ)^2 := by exact_mod_cast hdivN
    exact (le_div_iff₀ hden).2 hcast
  have hkR : (0:ℝ) ≤ k := by positivity
  have hlog : Real.log 2 ≤ (3:ℝ)/4 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hAcast : (3:ℝ)*(D:ℝ) ≤ 4*(A:ℝ) := by exact_mod_cast hA
  have hAsq : (9:ℝ)*(D:ℝ)^2/16 ≤ (A:ℝ)^2 := by nlinarith
  have hfrac : (3:ℝ)/4 * ((D:ℝ)^2/(200*n)) ≤ (A:ℝ)^2/(128*n) := by
    have hmul : (3:ℝ)/4 * ((D:ℝ)^2/(200*n)) ≤ (9:ℝ)*(D:ℝ)^2/16/(128*n) := by
      rw [show (3:ℝ)/4 * ((D:ℝ)^2/(200*n)) = (3*(D:ℝ)^2)/(800*n) by ring]
      apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 800*n)
        (by positivity : (0:ℝ) < 128*n)).2
      nlinarith [hAsq]
    have hmul2 : (9:ℝ)*(D:ℝ)^2/16/(128*n) ≤ (A:ℝ)^2/(128*n) := by
      exact div_le_div_of_nonneg_right hAsq (by positivity)
    exact le_trans hmul hmul2
  have hcomp : (k:ℝ)*Real.log 2 ≤ (A:ℝ)^2/(128*n) := by
    calc
      (k:ℝ)*Real.log 2 ≤ (k:ℝ)*(3/4) := mul_le_mul_of_nonneg_left hlog hkR
      _ ≤ ((D:ℝ)^2/(200*n))*(3/4) := by nlinarith [hDk]
      _ = (3/4)*((D:ℝ)^2/(200*n)) := by ring
      _ ≤ (A:ℝ)^2/(128*n) := hfrac
  have hpow : (2:ℝ)^k = Real.exp ((k:ℝ)*Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0:ℝ)<2)]
    congr 1
    ring
  calc
    Real.exp (-((A:ℝ)^2/(128*n))) ≤ Real.exp (-((k:ℝ)*Real.log 2)) :=
      Real.exp_le_exp.mpr (by linarith [hcomp])
    _ = ((2:ℝ)^k)⁻¹ := by rw [hpow, Real.exp_neg]



set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem reward_tail25552 {α : Type*} [Fintype α]
    (p : α → ℝ) (reward pot : α → Nat) (gain : α → ℝ)
    (n d D k A : Nat)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a : α, p a = 1)
    (hn : 0 < n) (hD : D = 5*n - 8*d) (hDle : D ≤ 5*n)
    (hk : k = D^2/(200*n)) (hk2 : 2 ≤ k)
    (hA : A = D - 8*k - 2)
    (hpot : ∀ a, pot a ≤ 2)
    (htel : ∀ a, gain a = 8*(reward a : ℝ) + pot a - 5*n)
    (hmgf : (∑ a : α, p a * Real.exp (-((A:ℝ)/(64*n)) * gain a)) ≤
      Real.exp (32*n*((A:ℝ)/(64*n))^2)) :
    (∑ a : α, if reward a ≤ d+k then p a else 0) ≤ ((2:ℝ)^k)⁻¹ := by
  have harith := large_block_arithmetic25552 n D k hn hDle hk hk2
  have hApos : 0 < A := by
    have hAcast : (3:ℝ)*(D:ℝ) ≤ 4*(A:ℝ) := by
      rw [hA]
      have hn16 := harith.1
      have hD80 := harith.2.1
      have h40k := harith.2.2
      have hcalc : 4*(D - 8*k - 2) ≥ 3*D := by omega
      exact_mod_cast hcalc
    have hDpositive : 0 < D := by omega
    omega
  have hAcoeff : 3*D ≤ 4*A := by
    have hn16 := harith.1
    have hD80 := harith.2.1
    have h40k := harith.2.2
    have hcalc : 4*(D - 8*k - 2) ≥ 3*D := by omega
    rw [hA]
    omega
  have hsub : 8*d ≤ 5*n := by
    have hD80 := harith.2.1
    rw [hD] at hD80
    omega
  have hDdef : (D:ℝ) = 5*(n:ℝ) - 8*(d:ℝ) := by
    rw [hD, Nat.cast_sub hsub]
    norm_num
  have hAeq : A + 8*k + 2 = D := by rw [hA]; omega
  have hArel : (D:ℝ) = (A:ℝ) + 8*k + 2 := by exact_mod_cast hAeq.symm
  have hcut (a : α) (hr : reward a ≤ d+k) : gain a ≤ -(A:ℝ) := by
    rw [htel a]
    have hpot' : (pot a:ℝ) ≤ 2 := by exact_mod_cast hpot a
    have hrewR : (reward a:ℝ) ≤ (d:ℝ)+k := by exact_mod_cast hr
    rw [hDdef] at hArel
    nlinarith
  have hmgf' : (∑ a : α, p a * Real.exp (-((A:ℝ)/(64*n)) * gain a)) ≤
      Real.exp (32*n*((A:ℝ)/(64*n))^2) := hmgf
  have htail := cdf_from_mgf_hoeffding25552 p gain n A hp (by exact_mod_cast hn)
    (by exact_mod_cast Nat.zero_le A) (by simpa using hmgf')
  calc
    ∑ a : α, (if reward a ≤ d+k then p a else 0)
      ≤ ∑ a : α, (if gain a ≤ -(A:ℝ) then p a else 0) :=
        sum_le_sum fun a _ => by
          split_ifs with hr hg
          · exact le_rfl
          · exact False.elim (hg (hcut a hr))
          · exact hp a
          · simp
    _ ≤ Real.exp (-((A:ℝ)^2/(128*n))) := by
      have hnR : (0:ℝ) < n := by exact_mod_cast hn
      simpa using htail
    _ ≤ ((2:ℝ)^k)⁻¹ := exp_tail_le_pow25552 n D k A hn hDle hk hk2 hAcoeff

open Finset


set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
def priceWeight25552 (r d : Nat) : ℝ := ((2 : ℝ) ^ (r - d))⁻¹

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem price_tail_split25552 {α : Type*} [Fintype α]
    (p : α → ℝ) (reward : α → Nat) (d k : Nat)
    (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a : α, p a = 1) :
    (∑ a : α, p a * priceWeight25552 (reward a) d) ≤
      (∑ a : α, if reward a ≤ d + k then p a else 0) + ((2 : ℝ) ^ (k+1))⁻¹ := by
  have hpoint (a : α) : p a * priceWeight25552 (reward a) d ≤
      (if reward a ≤ d+k then p a else 0) + p a * ((2 : ℝ) ^ (k+1))⁻¹ := by
    by_cases hlo : reward a ≤ d+k
    · simp only [if_pos hlo]
      have hw : priceWeight25552 (reward a) d ≤ 1 := by
        unfold priceWeight25552
        have hpow : 1 ≤ (2 : ℝ) ^ (reward a - d) := one_le_pow₀ (by norm_num)
        rw [inv_le_one₀ (by positivity : (0:ℝ) < (2:ℝ) ^ (reward a-d))]
        exact hpow
      have hmul : p a * priceWeight25552 (reward a) d ≤ p a := by
        simpa using mul_le_mul_of_nonneg_left hw (hp a)
      have hpowpos : 0 < (2:ℝ)^(k+1) := by positivity
      have hpos : 0 ≤ p a * ((2:ℝ)^(k+1))⁻¹ := mul_nonneg (hp a) (le_of_lt (inv_pos.mpr hpowpos))
      exact le_trans hmul (le_add_of_nonneg_right hpos)
    · simp only [if_neg hlo]
      have hdiff : k+1 ≤ reward a - d := by omega
      have hpow : (2 : ℝ) ^ (k+1) ≤ (2 : ℝ) ^ (reward a - d) :=
        pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hdiff
      have hw : priceWeight25552 (reward a) d ≤ ((2 : ℝ) ^ (k+1))⁻¹ := by
        unfold priceWeight25552
        exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
      have hmul : p a * priceWeight25552 (reward a) d ≤ p a * ((2:ℝ)^(k+1))⁻¹ :=
        mul_le_mul_of_nonneg_left hw (hp a)
      linarith
  calc
    ∑ a : α, p a * priceWeight25552 (reward a) d
      ≤ ∑ a : α, ((if reward a ≤ d+k then p a else 0) + p a * ((2 : ℝ) ^ (k+1))⁻¹) :=
        sum_le_sum fun a _ => hpoint a
    _ = (∑ a : α, if reward a ≤ d+k then p a else 0) +
        (∑ a : α, p a) * ((2 : ℝ) ^ (k+1))⁻¹ := by
        rw [sum_add_distrib, sum_mul]
    _ = (∑ a : α, if reward a ≤ d+k then p a else 0) + ((2 : ℝ) ^ (k+1))⁻¹ := by rw [hsum]; ring

open Finset L25552Tilt L25552Upper


namespace Lmeta25552Upper

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem path_reward_tail25552 (n d D k A : Nat)
    (hn : 0 < n) (hD : D = 5*n - 8*d) (hDle : D ≤ 5*n)
    (hk : k = D^2/(200*n)) (hk2 : 2 ≤ k)
    (hA : A = D - 8*k - 2) :
    (∑ w : Path n, if pathReward (1/2) n 0 w ≤ d+k then pathWeight (1/2) n w else 0)
      ≤ ((2:ℝ)^k)⁻¹ := by
  have harith := large_block_arithmetic25552 n D k hn hDle hk hk2
  have hnonneg : ∀ n, ∀ w : Path n, 0 ≤ pathWeight (1/2) n w := by
    intro n
    induction n with
    | zero => intro w; simp [pathWeight]
    | succ n ih =>
      intro w
      simp only [pathWeight]
      exact mul_nonneg (letterMass_nonneg_var3 (1/2) (by norm_num) (by norm_num) (w 0))
        (ih (Fin.tail w))
  let p : Path n → ℝ := pathWeight (1/2) n
  let reward : Path n → Nat := pathReward (1/2) n 0
  let pot : Path n → Nat := fun w => (runMode n 0 w).val
  let gain' : Path n → ℝ := compPath n 0
  have hp : ∀ w, 0 ≤ p w := by
    intro w
    exact hnonneg n w
  have hsum : ∑ w : Path n, p w = 1 := by
    dsimp [p]
    exact pathWeight_sum_one (1/2) n
  have hpot : ∀ w, pot w ≤ 2 := by
    intro w
    dsimp [pot]
    have hb := (runMode n 0 w).isLt
    omega
  have htel : ∀ w, gain' w = 8*(reward w : ℝ) + pot w - 5*n := by
    intro w
    dsimp [gain', reward, pot]
    have ht := compPath_telescopes n 0 w
    rw [ht]
    simp
    ring
  have hmgf : (∑ w : Path n, p w * Real.exp (-((A:ℝ)/(64*n)) * gain' w)) ≤
      Real.exp (32*n*((A:ℝ)/(64*n))^2) := by
    have hApos : 0 < A := by
      rw [hA]
      have hD80 := harith.2.1
      have h40k := harith.2.2
      omega
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    have htpos : 0 < (A:ℝ)/(64*n) := by
      apply div_pos
      · exact_mod_cast hApos
      · positivity
    have ht : -((A:ℝ)/(64*n)) < 0 := by linarith
    have hb := pathExpAvg_bound_neg (-((A:ℝ)/(64*n))) ht n 0
    have heq : (∑ w : Path n, p w * Real.exp (-((A:ℝ)/(64*n)) * gain' w)) =
        pathExpAvg (-((A:ℝ)/(64*n))) n 0 := by
      simpa [p, gain', pathExpAvg]
    have hsquare : (-((A:ℝ)/(64*n)))^2 = ((A:ℝ)/(64*n))^2 := by ring
    calc
      _ = pathExpAvg (-((A:ℝ)/(64*n))) n 0 := heq
      _ ≤ Real.exp (32*n*((A:ℝ)/(64*n))^2) := by
        rw [← hsquare]
        exact hb
  simpa [p, reward, pot, gain'] using
    (reward_tail25552 p reward pot gain' n d D k A hp hsum hn hD hDle hk hk2 hA hpot htel hmgf)

end Lmeta25552Upper

open Finset L25552Tilt L25552Upper L25552PriceLower


namespace Lmeta25552UpperPrice

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma gain_le_two_price (m : Fin 3) (l : Fin 8) : gain m l ≤ 2 := by
  fin_cases m <;> fin_cases l <;> norm_num [gain, hit, aligned, Nat.testBit]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathReward_le_two (n : Nat) (m : Fin 3) (w : Path n) :
    pathReward (1/2) n m w ≤ 2*n := by
  induction n generalizing m with
  | zero => simp [pathReward]
  | succ n ih =>
    simp only [pathReward]
    have hg := gain_le_two_price m (w 0)
    have hi := ih (next m (w 0)) (Fin.tail w)
    omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma priceFinReal_eq_pathExpectation (n d : Nat) :
    priceFinReal n d = (2:ℝ)^(5*n) *
      ∑ w : Path n, pathWeight (1/2) n w * priceWeight25552 (pathReward (1/2) n 0 w) d := by
  calc
    priceFinReal n d =
        ∑ w : Path n, (2:ℝ)^(2*n - ((L25552NatBridge.stateN (pathCode n w) n 0).2 - d)) :=
          price_reindex n d
    _ = ∑ w : Path n, (2:ℝ)^(5*n) *
        (pathWeight (1/2) n w * priceWeight25552 (pathReward (1/2) n 0 w) d) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hrw : (L25552NatBridge.stateN (pathCode n w) n 0).2 =
          pathReward (1/2) n 0 w := by
        simpa using L25552NatBridge.pathReward_eq_stateN n w (0:Fin 3)
      rw [hrw, uniform_pathWeight]
      let r := pathReward (1/2) n 0 w
      have hr : r ≤ 2*n := pathReward_le_two n 0 w
      have hx : r-d ≤ 2*n := by omega
      have hpowadd : (2:ℝ)^(2*n) = (2:ℝ)^(2*n-(r-d)) * (2:ℝ)^(r-d) := by
        calc
          (2:ℝ)^(2*n) = (2:ℝ)^(2*n-(r-d)+(r-d)) := by rw [Nat.sub_add_cancel hx]
          _ = _ := by rw [pow_add]
      have hpow : (2:ℝ)^(2*n-(r-d)) = (2:ℝ)^(2*n) * ((2:ℝ)^(r-d))⁻¹ := by
        calc
          _ = (2:ℝ)^(2*n-(r-d)) * 1 := by ring
          _ = (2:ℝ)^(2*n-(r-d)) * ((2:ℝ)^(r-d) * ((2:ℝ)^(r-d))⁻¹) := by
            rw [mul_inv_cancel₀ (by positivity : (2:ℝ)^(r-d) ≠ 0)]
          _ = ((2:ℝ)^(2*n-(r-d)) * (2:ℝ)^(r-d)) * ((2:ℝ)^(r-d))⁻¹ := by ring
          _ = (2:ℝ)^(2*n) * ((2:ℝ)^(r-d))⁻¹ := by rw [hpowadd]
      rw [show pathReward (1/2) n 0 w = r by rfl, show (2:ℝ)^(2*n - (r-d)) = (2:ℝ)^(2*n) * ((2:ℝ)^(r-d))⁻¹ by exact hpow]
      unfold priceWeight25552
      rw [← power_scale n]
      ring
    _ = (2:ℝ)^(5*n) *
        ∑ w : Path n, pathWeight (1/2) n w * priceWeight25552 (pathReward (1/2) n 0 w) d := by
      rw [Finset.mul_sum]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem priceFinReal_upper_of_large_deficit (n d : Nat) (hn : 0 < n)
    (hk2 : 2 ≤ (5*n-8*d)^2/(200*n)) :
    priceFinReal n d ≤ (2:ℝ)^(5*n+1 - (5*n-8*d)^2/(200*n)) := by
  let D := 5*n-8*d
  let k := D^2/(200*n)
  let A := D-8*k-2
  have hD : D = 5*n-8*d := rfl
  have hDle : D ≤ 5*n := by dsimp [D]; omega
  have hk : k = D^2/(200*n) := rfl
  have hDpos : 0 < n := hn
  have hlarge := large_block_arithmetic25552 n D k hn hDle hk hk2
  have hpath := Lmeta25552Upper.path_reward_tail25552 n d D k A hn hD hDle hk hk2 rfl
  have pathWeight_nonneg_price : ∀ n, ∀ w : Path n, 0 ≤ pathWeight (1/2) n w := by
    intro n
    induction n with
    | zero => intro w; simp [pathWeight]
    | succ n ih =>
      intro w
      simp only [pathWeight]
      exact mul_nonneg (letterMass_nonneg_var3 (1/2) (by norm_num) (by norm_num) (w 0)) (ih (Fin.tail w))
  have havg := price_tail_split25552 (pathWeight (1/2) n)
      (pathReward (1/2) n 0) d k
      (pathWeight_nonneg_price n)
      (pathWeight_sum_one (1/2) n)
  have hlow : (∑ w : Path n, if pathReward (1/2) n 0 w ≤ d+k then pathWeight (1/2) n w else 0) ≤ ((2:ℝ)^k)⁻¹ := hpath
  have hpowstep : ((2:ℝ)^(k+1))⁻¹ = ((2:ℝ)^k)⁻¹ / 2 := by
    rw [pow_succ]
    field_simp
  have havg' : (∑ w : Path n, pathWeight (1/2) n w *
      priceWeight25552 (pathReward (1/2) n 0 w) d) ≤ 2*((2:ℝ)^k)⁻¹ := by
    have := havg
    rw [hpowstep] at this
    calc
      _ ≤ (∑ w : Path n, if pathReward (1/2) n 0 w ≤ d+k then pathWeight (1/2) n w else 0) + ((2:ℝ)^k)⁻¹ / 2 := this
      _ ≤ ((2:ℝ)^k)⁻¹ + ((2:ℝ)^k)⁻¹ / 2 := add_le_add hlow le_rfl
      _ ≤ 2 * ((2:ℝ)^k)⁻¹ := by
        have hx : 0 ≤ ((2:ℝ)^k)⁻¹ := by positivity
        nlinarith
  have hprice := priceFinReal_eq_pathExpectation n d
  have hmul : priceFinReal n d ≤ (2:ℝ)^(5*n) * (2*((2:ℝ)^k)⁻¹) := by
    rw [hprice]
    exact mul_le_mul_of_nonneg_left havg' (by positivity)
  have hkbound : k ≤ 5*n+1 := by omega
  have hpowid : (2:ℝ)^(5*n+1) = (2:ℝ)^k * (2:ℝ)^(5*n+1-k) := by
    rw [← pow_add]
    congr 1
    omega
  have hmulid : (2:ℝ)^(5*n) * (2*((2:ℝ)^k)⁻¹) = (2:ℝ)^(5*n+1-k) := by
    calc
      (2:ℝ)^(5*n) * (2*((2:ℝ)^k)⁻¹) = (2:ℝ)^(5*n+1) / (2:ℝ)^k := by
        rw [pow_succ]
        field_simp
      _ = (2:ℝ)^(5*n+1-k) := by
        rw [hpowid]
        field_simp
  rw [hmulid] at hmul
  exact hmul

end Lmeta25552UpperPrice

open Finset L25552Tilt L25552PriceLower L25552Integration Lmeta25552UpperPrice

namespace Lmeta25552UpperNat

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma pathWeight_nonneg_upper : ∀ n, ∀ w : Path n, 0 ≤ pathWeight (1/2) n w := by
  intro n
  induction n with
  | zero => intro w; simp [pathWeight]
  | succ n ih =>
    intro w
    simp only [pathWeight]
    exact mul_nonneg (letterMass_nonneg_var3 (1/2) (by norm_num) (by norm_num) (w 0)) (ih (Fin.tail w))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
lemma priceWeight_le_one_upper (r d : Nat) : priceWeight25552 r d ≤ 1 := by
  unfold priceWeight25552
  have hp : 1 ≤ (2:ℝ)^(r-d) := one_le_pow₀ (by norm_num)
  rw [inv_le_one₀ (by positivity : (0:ℝ)<(2:ℝ)^(r-d))]
  exact hp

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem priceFinReal_upper_trivial (n d : Nat) : priceFinReal n d ≤ (2:ℝ)^(5*n) := by
  have hsum : (∑ w : Path n, pathWeight (1/2) n w *
      priceWeight25552 (pathReward (1/2) n 0 w) d) ≤ 1 := by
    calc
      _ ≤ ∑ w : Path n, pathWeight (1/2) n w :=
        Finset.sum_le_sum fun w _ => by
          simpa using (mul_le_mul_of_nonneg_left
            (priceWeight_le_one_upper (pathReward (1/2) n 0 w) d)
            (pathWeight_nonneg_upper n w))
      _ = 1 := pathWeight_sum_one (1/2) n
  calc
    priceFinReal n d = (2:ℝ)^(5*n) *
        ∑ w : Path n, pathWeight (1/2) n w * priceWeight25552 (pathReward (1/2) n 0 w) d :=
      priceFinReal_eq_pathExpectation n d
    _ ≤ (2:ℝ)^(5*n) * 1 := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (2:ℝ)^(5*n) := by ring

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem upper_second_25552 (n d : Nat) (hn : 0 < n) :
    2^((5*n-8*d)^2/(200*n)) * natPriceListL n d ≤ 2^(5*n+1) := by
  let D := 5*n-8*d
  let k := D^2/(200*n)
  by_cases hk1 : k ≤ 1
  · have hpriceR : priceFinReal n d ≤ (2:ℝ)^(5*n) := priceFinReal_upper_trivial n d
    have hprice : natPriceListL n d ≤ 2^(5*n) := by
      have hcast : (natPriceListL n d : ℝ) ≤ (2:ℝ)^(5*n) := by
        rw [← priceFinReal_eq_target_natPriceList]
        exact hpriceR
      exact_mod_cast hcast
    have hkpow : 2^k ≤ 2 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk1
    calc
      2^k * natPriceListL n d ≤ 2 * 2^(5*n) := Nat.mul_le_mul hkpow hprice
      _ = 2^(5*n+1) := by rw [pow_succ]; ring
  · have hk2 : 2 ≤ k := by omega
    have hlarge := priceFinReal_upper_of_large_deficit n d hn (by simpa [D,k] using hk2)
    have hprice : natPriceListL n d ≤ 2^(5*n+1-k) := by
      have hcast : (natPriceListL n d : ℝ) ≤ (2:ℝ)^(5*n+1-k) := by
        rw [← priceFinReal_eq_target_natPriceList]
        simpa [D,k] using hlarge
      exact_mod_cast hcast
    have hkbound : k ≤ 5*n+1 := by
      have hD : D ≤ 5*n := by dsimp [D]; omega
      have hlarge' := large_block_arithmetic25552 n D k hn hD rfl hk2
      have : 40*k ≤ D := hlarge'.2.2
      omega
    calc
      2^k * natPriceListL n d ≤ 2^k * 2^(5*n+1-k) := Nat.mul_le_mul_left _ hprice
      _ = 2^(5*n+1) := by
        rw [← pow_add]
        congr 1
        omega

end Lmeta25552UpperNat

end
end PEqualNP.Outside.L_meta_25552_aux

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_25552 : (let move := fun (mode letter : Nat) =>
    let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)
    let hit := letter.testBit 2
    (if aligned then (if hit then 0 else 2) else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (0, 0)
  let price := fun (n depth : Nat) =>
    ((List.range (8 ^ n)).map (fun codeWord =>
      2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum
  ∀ (n d : Nat), 0 < n →
    let deficit := 5 * n - 8 * d
    let blocks := 1 + 128 * deficit ^ 2 / n
    2 ^ (5 * n) ≤ 2 ^ (12 * blocks) * price n d ∧
      2 ^ (deficit ^ 2 / (200 * n)) * price n d ≤ 2 ^ (5 * n + 1)) := by
  intro move summary price n d hn
  change (2^(5*n) ≤ 2^(12*(1+128*(5*n-8*d)^2/n))*
      PEqualNP.Outside.L_meta_25552_aux.natPriceListL n d) ∧
    (2^((5*n-8*d)^2/(200*n))*
      PEqualNP.Outside.L_meta_25552_aux.natPriceListL n d ≤ 2^(5*n+1))
  exact ⟨
    PEqualNP.Outside.L_meta_25552_aux.L25552Integration.lower_first_nat_all n d hn,
    PEqualNP.Outside.L_meta_25552_aux.Lmeta25552UpperNat.upper_second_25552 n d hn⟩
