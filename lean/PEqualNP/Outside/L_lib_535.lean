import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_535

open Finset Real

noncomputable def g (a b : ℕ) : ℝ :=
  (Nat.choose (2*a) a : ℝ) * (Nat.choose (2*b) b : ℝ) / ((4:ℝ)^(a+b) * (Nat.choose (a+b) a : ℝ))

theorem cb_succ (a : ℕ) :
    (Nat.choose (2*(a+1)) (a+1) : ℝ) = 2*(2*(a:ℝ)+1)/((a:ℝ)+1) * (Nat.choose (2*a) a : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ a
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  have h' : ((a:ℝ)+1) * (Nat.choose (2*(a+1)) (a+1) : ℝ) = 2*(2*(a:ℝ)+1) * (Nat.choose (2*a) a : ℝ) := by
    exact_mod_cast h
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linarith [h']

theorem ch_succ_left (a b : ℕ) :
    (Nat.choose (a+1+b) (a+1) : ℝ) = ((a:ℝ)+b+1)/((a:ℝ)+1) * (Nat.choose (a+b) a : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (a+b) a
  have e : a + 1 + b = a + b + 1 := by ring
  rw [e]
  have h' : ((a:ℝ)+b+1) * (Nat.choose (a+b) a : ℝ) = (Nat.choose (a+b+1) (a+1) : ℝ) * ((a:ℝ)+1) := by
    exact_mod_cast h
  rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
  linarith [h']

theorem ch_succ_right (a b : ℕ) :
    (Nat.choose (a+(b+1)) a : ℝ) = ((a:ℝ)+b+1)/((b:ℝ)+1) * (Nat.choose (a+b) a : ℝ) := by
  have s1 : Nat.choose (a+(b+1)) a = Nat.choose (b+1+a) (b+1) := by
    rw [Nat.choose_symm_add, show a + (b+1) = b + 1 + a by ring]
  have s2 : Nat.choose (a+b) a = Nat.choose (b+a) b := by
    rw [Nat.choose_symm_add, show a + b = b + a by ring]
  rw [s1, s2, ch_succ_left b a]
  congr 1
  ring

theorem g_zero : g 0 0 = 1 := by simp [g]

theorem g_succ_left (a b : ℕ) : g (a+1) b = g a b * (((a:ℝ) + 1/2) / ((a:ℝ)+b+1)) := by
  unfold g
  rw [cb_succ, ch_succ_left, show a+1+b = (a+b)+1 by ring, pow_succ]
  have h1 : (0:ℝ) < Nat.choose (a+b) a := by exact_mod_cast Nat.choose_pos (by omega)
  have h2 : (0:ℝ) < Nat.choose (2*a) a := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp
  ring

theorem g_succ_right (a b : ℕ) : g a (b+1) = g a b * (((b:ℝ) + 1/2) / ((a:ℝ)+b+1)) := by
  unfold g
  rw [cb_succ, ch_succ_right, show a+(b+1) = (a+b)+1 by ring, pow_succ]
  have h1 : (0:ℝ) < Nat.choose (a+b) a := by exact_mod_cast Nat.choose_pos (by omega)
  have h2 : (0:ℝ) < Nat.choose (2*b) b := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp
  ring

def cnt (w : ℕ → Bool) (t : ℕ) : ℕ := ((Finset.range t).filter (fun j => w j = true)).card

theorem cnt_le (w : ℕ → Bool) (t : ℕ) : cnt w t ≤ t :=
  (Finset.card_filter_le _ _).trans (Finset.card_range t).le

theorem cnt_succ (w : ℕ → Bool) (t : ℕ) :
    cnt w (t+1) = cnt w t + (if w t = true then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

noncomputable def fac (w : ℕ → Bool) (j : ℕ) : ℝ :=
  ((if w j = true then (cnt w j : ℝ) else ((j - cnt w j : ℕ) : ℝ)) + 1/2) / ((j:ℝ)+1)

theorem prod_fac (w : ℕ → Bool) (t : ℕ) :
    ∏ j ∈ Finset.range t, fac w j = g (cnt w t) (t - cnt w t) := by
  induction t with
  | zero => simp [cnt, g_zero]
  | succ t ih =>
    rw [Finset.prod_range_succ, ih, cnt_succ]
    have hle := cnt_le w t
    unfold fac
    by_cases hw : w t = true
    · rw [if_pos hw, if_pos hw, show t + 1 - (cnt w t + 1) = t - cnt w t by omega, g_succ_left]
      congr 2
      push_cast [Nat.cast_sub hle]
      ring
    · rw [if_neg hw, if_neg hw, add_zero, show t + 1 - cnt w t = (t - cnt w t) + 1 by omega,
        g_succ_right]
      congr 2
      push_cast [Nat.cast_sub hle]
      ring

def wext {n : ℕ} (w : Fin n → Bool) (j : ℕ) : Bool := if h : j < n then w ⟨j, h⟩ else false

theorem ones_eq {n : ℕ} (w : Fin n → Bool) (t : ℕ) (ht : t ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < t ∧ w j = true)).card = cnt (wext w) t := by
  unfold cnt
  apply Finset.card_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show j.val ∈ (Finset.range t).filter (fun j => wext w j = true)
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hj.1, ?_⟩
    simp [wext, j.isLt, hj.2]
  · intro a _ b _ h
    exact Fin.ext h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    have hxn : x < n := by omega
    refine ⟨⟨x, hxn⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hx.1, ?_⟩
    have h2 := hx.2
    simp only [wext, hxn, dite_true] at h2
    exact h2

theorem KT_eq (n : ℕ) (w : Fin n → Bool) :
    (∏ j : Fin n, ((if w j then
        (((Finset.univ : Finset (Fin n)).filter (fun i => i.val < j.val ∧ w i = true)).card : ℝ)
      else ((j.val - ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < j.val ∧ w i = true)).card : ℕ) : ℝ))
        + 1/2) / ((j.val : ℝ)+1))
      = g (cnt (wext w) n) (n - cnt (wext w) n) := by
  rw [← prod_fac]
  rw [← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hw : w j = wext w j.val := by simp [wext, j.isLt]
  rw [ones_eq w j.val j.isLt.le]
  unfold fac
  rw [hw]

theorem fact_upper (m : ℕ) (hm : 1 ≤ m) :
    (m.factorial : ℝ) ≤ exp 1 * √(m:ℝ) * ((m:ℝ) / exp 1)^m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hs : Stirling.stirlingSeq (j+1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le j)
  rw [Stirling.stirlingSeq_one] at hs
  unfold Stirling.stirlingSeq at hs
  have hpos : 0 < √(2 * ((j+1:ℕ):ℝ)) * (((j+1:ℕ):ℝ) / exp 1)^(j+1) := by positivity
  rw [div_le_iff₀ hpos] at hs
  calc ((j+1).factorial : ℝ)
      ≤ exp 1 / √2 * (√(2 * ((j+1:ℕ):ℝ)) * (((j+1:ℕ):ℝ) / exp 1)^(j+1)) := hs
    _ = exp 1 * √((j+1:ℕ):ℝ) * (((j+1:ℕ):ℝ) / exp 1)^(j+1) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have : √(2:ℝ) ≠ 0 := by positivity
      field_simp

theorem two_pow (m : ℕ) : (((2*m : ℕ) : ℝ) / exp 1)^(2*m) = 4^m * (((m:ℝ) / exp 1)^m)^2 := by
  push_cast
  rw [mul_div_assoc, mul_pow, show (2:ℝ)^(2*m) = 4^m by rw [pow_mul]; norm_num]
  ring

theorem fact_lower_two (m : ℕ) :
    √(4*π) * √(m:ℝ) * (4^m * (((m:ℝ) / exp 1)^m)^2) ≤ ((2*m).factorial : ℝ) := by
  have h := Stirling.le_factorial_stirling (2*m)
  rw [two_pow] at h
  have e : √(2*π*((2*m:ℕ):ℝ)) = √(4*π) * √(m:ℝ) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast
    ring
  rw [e] at h
  exact h

theorem const_bound (n : ℕ) : exp 1 ^ 3 * √(n:ℝ) ≤ 64 * π * √((n:ℝ)+1) := by
  have he : exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he3 : exp 1 ^ 3 ≤ 27 := by
    calc exp 1 ^ 3 ≤ 3 ^ 3 := pow_le_pow_left₀ (by positivity) he 3
      _ = 27 := by norm_num
  have hs : √(n:ℝ) ≤ √((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
  have hpi := Real.pi_gt_three
  have h0 : 0 ≤ √(n:ℝ) := Real.sqrt_nonneg _
  have h1 : 0 ≤ √((n:ℝ)+1) := Real.sqrt_nonneg _
  nlinarith

theorem sqrt4pi : 3 ≤ √(4*π) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  have := Real.pi_gt_three
  linarith

theorem endpoint (n : ℕ) (hn : 1 ≤ n) :
    (4:ℝ)^n * n.factorial * n.factorial ≤ 16 * √((n:ℝ)+1) * (2*n).factorial := by
  have hu := fact_upper n hn
  have hl := fact_lower_two n
  set x := ((n:ℝ) / exp 1)^n with hx
  have hx0 : 0 < x := by positivity
  have hf0 : (0:ℝ) ≤ n.factorial := by positivity
  have hsn : √(n:ℝ) * √(n:ℝ) = n := Real.mul_self_sqrt (by positivity)
  have hs : √(n:ℝ) ≤ √((n:ℝ)+1) := Real.sqrt_le_sqrt (by linarith)
  have he : exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have h4 := sqrt4pi
  have hsq0 : 0 ≤ √(n:ℝ) := Real.sqrt_nonneg _
  have hp4 : (0:ℝ) < 4^n := by positivity
  calc (4:ℝ)^n * n.factorial * n.factorial
      ≤ 4^n * (exp 1 * √(n:ℝ) * x) * (exp 1 * √(n:ℝ) * x) := by gcongr
    _ = (exp 1)^2 * (√(n:ℝ) * √(n:ℝ)) * (4^n * x^2) := by ring
    _ ≤ 9 * (√((n:ℝ)+1) * √(n:ℝ)) * (4^n * x^2) := by
      gcongr
      all_goals first | exact hs | nlinarith [Real.exp_pos 1]
    _ ≤ 16 * √((n:ℝ)+1) * (√(4*π) * √(n:ℝ) * (4^n * x^2)) := by
      have h1 : 0 ≤ √((n:ℝ)+1) := Real.sqrt_nonneg _
      have h2 : 0 ≤ √((n:ℝ)+1) * √(n:ℝ) * (4^n * x^2) := by positivity
      nlinarith
    _ ≤ 16 * √((n:ℝ)+1) * (2*n).factorial := by gcongr

theorem interior (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ((k:ℝ)/((k+l:ℕ):ℝ))^k * ((l:ℝ)/((k+l:ℕ):ℝ))^l *
        ((4:ℝ)^(k+l) * (k.factorial * l.factorial * (k+l).factorial))
      ≤ 16 * √(((k+l:ℕ):ℝ)+1) * ((2*k).factorial * (2*l).factorial) := by
  have hkn := fact_upper k hk
  have hln := fact_upper l hl
  have hnn := fact_upper (k+l) (by omega)
  have h2k := fact_lower_two k
  have h2l := fact_lower_two l
  set N : ℝ := ((k+l:ℕ):ℝ) with hN
  set xk := ((k:ℝ) / exp 1)^k with hxk
  set xl := ((l:ℝ) / exp 1)^l with hxl
  set xn := (N / exp 1)^(k+l) with hxn
  set M := ((k:ℝ)/N)^k * ((l:ℝ)/N)^l with hM
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast (show 0 < k + l by omega)
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hlpos : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hMx : M * xn = xk * xl := by
    rw [hM, hxn, hxk, hxl, div_pow, div_pow, div_pow, div_pow, div_pow, pow_add, pow_add]
    have : N = (k:ℝ) + l := by rw [hN]; push_cast; ring
    rw [this]
    field_simp
  have hM0 : 0 ≤ M := by positivity
  have hxk0 : 0 < xk := by positivity
  have hxl0 : 0 < xl := by positivity
  have hxn0 : 0 < xn := by positivity
  have hc := const_bound (k+l)
  have h4 : √(4*π) * √(4*π) = 4*π := Real.mul_self_sqrt (by positivity)
  set Q := (4:ℝ)^(k+l) * √(k:ℝ) * √(l:ℝ) * xk^2 * xl^2 with hQ
  have hQ0 : 0 ≤ Q := by positivity
  calc M * ((4:ℝ)^(k+l) * (k.factorial * l.factorial * (k+l).factorial))
      ≤ M * ((4:ℝ)^(k+l) * ((exp 1 * √(k:ℝ) * xk) * (exp 1 * √(l:ℝ) * xl) * (exp 1 * √N * xn))) := by
        gcongr
    _ = exp 1 ^ 3 * √N * (4^(k+l) * √(k:ℝ) * √(l:ℝ) * xk * xl) * (M * xn) := by ring
    _ = exp 1 ^ 3 * √N * Q := by rw [hMx, hQ]; ring
    _ ≤ 64 * π * √(N+1) * Q := by gcongr
    _ = 16 * √(N+1) * ((√(4*π) * √(k:ℝ) * (4^k * xk^2)) * (√(4*π) * √(l:ℝ) * (4^l * xl^2))) := by
        rw [hQ, pow_add]
        linear_combination (16 * √(N+1) * √(k:ℝ) * √(l:ℝ) * 4^k * 4^l * xk^2 * xl^2) * h4.symm
    _ ≤ 16 * √(N+1) * ((2*k).factorial * (2*l).factorial) := by gcongr

theorem ml (k l : ℕ) (hn : 0 < k + l) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p^k * (1-p)^l ≤ ((k:ℝ)/((k+l:ℕ):ℝ))^k * ((l:ℝ)/((k+l:ℕ):ℝ))^l := by
  have hN : (((k+l:ℕ):ℝ)) = (k:ℝ) + l := by push_cast; ring
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hl : (l:ℝ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add]
    rw [div_self hl, one_pow]
    exact pow_le_one₀ (by linarith) (by linarith)
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have hk' : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    simp only [pow_zero, mul_one, Nat.cast_zero, add_zero]
    rw [div_self hk', one_pow]
    exact pow_le_one₀ hp0 hp1
  rw [hN]
  have hkp : (0:ℝ) < k := by exact_mod_cast hk
  have hlp : (0:ℝ) < l := by exact_mod_cast hl
  set a := (k:ℝ) / ((k:ℝ) + l) with ha
  set b := (l:ℝ) / ((k:ℝ) + l) with hb
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have h1 : p / a ≤ exp (p / a - 1) := by have := Real.add_one_le_exp (p / a - 1); linarith
  have h2 : (1-p) / b ≤ exp ((1-p) / b - 1) := by
    have := Real.add_one_le_exp ((1-p) / b - 1); linarith
  have h1' : (p / a)^k ≤ exp ((k:ℝ) * (p / a - 1)) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) h1 k
  have h2' : ((1-p) / b)^l ≤ exp ((l:ℝ) * ((1-p) / b - 1)) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (div_nonneg (by linarith) hb0.le) h2 l
  have hsum : (k:ℝ) * (p / a - 1) + (l:ℝ) * ((1-p) / b - 1) = 0 := by
    rw [ha, hb]; field_simp; ring
  have hprod : (p / a)^k * ((1-p) / b)^l ≤ 1 := by
    calc (p / a)^k * ((1-p) / b)^l ≤ exp ((k:ℝ) * (p / a - 1)) * exp ((l:ℝ) * ((1-p) / b - 1)) :=
          mul_le_mul h1' h2' (pow_nonneg (div_nonneg (by linarith) hb0.le) l) (by positivity)
      _ = exp ((k:ℝ) * (p / a - 1) + (l:ℝ) * ((1-p) / b - 1)) := (Real.exp_add _ _).symm
      _ = 1 := by rw [hsum, Real.exp_zero]
  have hsa : (p / a)^k * a^k = p^k := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ha0.ne')]
  have hsb : ((1-p) / b)^l * b^l = (1-p)^l := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hb0.ne')]
  have hsplit : p^k * (1-p)^l = ((p / a)^k * ((1-p) / b)^l) * (a^k * b^l) := by
    rw [← hsa, ← hsb]; ring
  rw [hsplit]
  calc ((p / a)^k * ((1-p) / b)^l) * (a^k * b^l) ≤ 1 * (a^k * b^l) := by
        gcongr
    _ = a^k * b^l := one_mul _

theorem closed_fact (k l : ℕ) :
    (Nat.choose (2*k) k : ℝ) * (Nat.choose (2*l) l : ℝ) / ((4:ℝ)^(k+l) * (Nat.choose (k+l) k : ℝ))
      = ((2*k).factorial * (2*l).factorial : ℝ) /
          ((4:ℝ)^(k+l) * (k.factorial * l.factorial * (k+l).factorial)) := by
  have e1 : (Nat.choose (2*k) k : ℝ) * k.factorial * k.factorial = (2*k).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2*k by omega)
    rw [show 2*k - k = k by omega] at this
    exact_mod_cast this
  have e2 : (Nat.choose (2*l) l : ℝ) * l.factorial * l.factorial = (2*l).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show l ≤ 2*l by omega)
    rw [show 2*l - l = l by omega] at this
    exact_mod_cast this
  have e3 : (Nat.choose (k+l) k : ℝ) * k.factorial * l.factorial = (k+l).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (show k ≤ k+l by omega)
    rw [show k + l - k = l by omega] at this
    exact_mod_cast this
  rw [← e1, ← e2, ← e3]
  have hk : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hl : (0:ℝ) < l.factorial := by exact_mod_cast Nat.factorial_pos l
  have hc : (0:ℝ) < Nat.choose (k+l) k := by exact_mod_cast Nat.choose_pos (by omega)
  field_simp

theorem bound_closed (k l : ℕ) (hn : 0 < k + l) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p^k * (1-p)^l ≤ 16 * √(((k+l:ℕ):ℝ)+1) *
      ((Nat.choose (2*k) k : ℝ) * (Nat.choose (2*l) l : ℝ) / ((4:ℝ)^(k+l) * (Nat.choose (k+l) k : ℝ))) := by
  refine (ml k l hn p hp0 hp1).trans ?_
  rw [closed_fact, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hl : ((l:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show l ≠ 0 by omega)
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
      mul_zero, one_mul]
    rw [div_self hl, one_pow, one_mul]
    have := endpoint l (by omega)
    linarith
  rcases Nat.eq_zero_or_pos l with hl | hl
  · subst hl
    have hk' : ((k:ℕ):ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    simp only [pow_zero, mul_one, Nat.cast_zero, add_zero, Nat.factorial_zero, Nat.cast_one,
      mul_zero]
    rw [div_self hk', one_pow, one_mul]
    have := endpoint k (by omega)
    linarith
  exact interior k l hk hl

end PEqualNP.Outside.L_lib_535

theorem PEqualNP.Outside.L_lib_535 : (∀ (n : ℕ) (w : Fin n → Bool), 0 < n →
  let ones := fun (t : ℕ) => ((Finset.univ : Finset (Fin n)).filter
    (fun j => j.val < t ∧ w j = true)).card
  let k := ones n
  let KT := ∏ j : Fin n, ((if w j then (ones j.val : ℝ) else ((j.val - ones j.val : ℕ) : ℝ)) + 1/2) / ((j.val : ℝ)+1)
  let closed := (Nat.choose (2*k) k : ℝ) * (Nat.choose (2*(n-k)) (n-k) : ℝ) /
    ((4:ℝ)^n * (Nat.choose n k : ℝ))
  KT = closed ∧ ∀ p : ℝ, 0 ≤ p → p ≤ 1 →
    p^k * (1-p)^(n-k) ≤ 16*Real.sqrt ((n:ℝ)+1)*KT) := by
  intro n w hn
  dsimp only
  have hk : ((Finset.univ : Finset (Fin n)).filter (fun j => j.val < n ∧ w j = true)).card
      = PEqualNP.Outside.L_lib_535.cnt (PEqualNP.Outside.L_lib_535.wext w) n :=
    PEqualNP.Outside.L_lib_535.ones_eq w n le_rfl
  have hkn : PEqualNP.Outside.L_lib_535.cnt (PEqualNP.Outside.L_lib_535.wext w) n ≤ n :=
    PEqualNP.Outside.L_lib_535.cnt_le _ n
  have hKT := PEqualNP.Outside.L_lib_535.KT_eq n w
  rw [hk]
  set c := PEqualNP.Outside.L_lib_535.cnt (PEqualNP.Outside.L_lib_535.wext w) n with hc
  have hg : PEqualNP.Outside.L_lib_535.g c (n - c) =
      (Nat.choose (2*c) c : ℝ) * (Nat.choose (2*(n-c)) (n-c) : ℝ) / ((4:ℝ)^n * (Nat.choose n c : ℝ)) := by
    unfold PEqualNP.Outside.L_lib_535.g
    rw [Nat.add_sub_cancel' hkn]
  refine ⟨hKT.trans hg, fun p hp0 hp1 => ?_⟩
  rw [hKT, hg]
  have := PEqualNP.Outside.L_lib_535.bound_closed c (n - c) (by omega) p hp0 hp1
  rw [Nat.add_sub_cancel' hkn] at this
  exact this
