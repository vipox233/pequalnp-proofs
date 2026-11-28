import PEqualNP.Defs
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

namespace PEqualNP.Outside.L_lib_944_aux

private lemma two_pow_pred_le_fact : ∀ j : ℕ, 1 ≤ j → 2 ^ (j - 1) ≤ j.factorial
  | 0, h => by omega
  | 1, _ => by simp
  | n + 2, _ => by
    have ih := two_pow_pred_le_fact (n + 1) (by omega)
    have h1 : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    have h2 : (n + 2).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ (n + 1)
    have h3 : 2 * 2 ^ n ≤ (n + 2) * (n + 1).factorial :=
      Nat.mul_le_mul (by omega) ih
    simpa [h1, h2] using h3

private lemma fact_mul_choose_le_pow (n k : ℕ) : k.factorial * n.choose k ≤ n ^ k := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow n k

private lemma sum_two_pow_le_strong (k : ℕ) :
    (∑ j ∈ Finset.range k, 2 ^ (k - j)) + 2 ≤ 2 * 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 : ∑ j ∈ Finset.range k, 2 ^ (k + 1 - j) =
        2 * ∑ j ∈ Finset.range k, 2 ^ (k - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < k := Finset.mem_range.mp hj
      have hsub : k + 1 - j = (k - j) + 1 := by omega
      rw [hsub, pow_succ']
    rw [h1]
    have hlast : k + 1 - k = 1 := by omega
    rw [hlast, pow_one]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

private lemma sum_two_pow_le (k : ℕ) :
    (∑ j ∈ Finset.range k, 2 ^ (k - j)) ≤ 2 * 2 ^ k :=
  le_trans (Nat.le_add_right _ 2) (sum_two_pow_le_strong k)

private lemma add_one_pow_le_three_mul_pow (k : ℕ) : (k + 1) ^ k ≤ 3 * k ^ k := by
  cases k with
  | zero => simp
  | succ n =>
    set k := n + 1
    have h2k_pos : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
    suffices h : 2 ^ k * (k + 1) ^ k ≤ 2 ^ k * (3 * k ^ k) by
      exact Nat.le_of_mul_le_mul_left h h2k_pos
    have hexp : (k + 1) ^ k = ∑ j ∈ Finset.range (k + 1), k.choose j * k ^ (k - j) := by
      have h1 : (k + 1) ^ k = (1 + k) ^ k := by ring
      rw [h1, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [mul_comm]
    rw [hexp, Finset.mul_sum, Finset.sum_range_succ']
    have h0 : 2 ^ k * (k.choose 0 * k ^ (k - 0)) = 2 ^ k * k ^ k := by simp
    rw [h0]
    have hrest :
        ∑ j ∈ Finset.range k, 2 ^ k * (k.choose (j + 1) * k ^ (k - (j + 1))) ≤
          (∑ j ∈ Finset.range k, 2 ^ (k - j)) * k ^ k := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j < k := Finset.mem_range.mp hj
      have hsplit : 2 ^ k = 2 ^ (k - j) * 2 ^ j := by
        rw [← pow_add]
        congr 1
        omega
      have hfact : 2 ^ j ≤ (j + 1).factorial := two_pow_pred_le_fact (j + 1) (by omega)
      have hch : (j + 1).factorial * k.choose (j + 1) ≤ k ^ (j + 1) :=
        fact_mul_choose_le_pow k (j + 1)
      have hstep : 2 ^ j * k.choose (j + 1) ≤ k ^ (j + 1) :=
        le_trans (Nat.mul_le_mul_right _ hfact) hch
      have hpowk : k ^ (j + 1) * k ^ (k - (j + 1)) = k ^ k := by
        rw [← pow_add]
        congr 1
        omega
      calc
        2 ^ k * (k.choose (j + 1) * k ^ (k - (j + 1)))
            = 2 ^ (k - j) * ((2 ^ j * k.choose (j + 1)) * k ^ (k - (j + 1))) := by
              rw [hsplit]; ring
        _ ≤ 2 ^ (k - j) * (k ^ (j + 1) * k ^ (k - (j + 1))) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hstep)
        _ = 2 ^ (k - j) * k ^ k := by rw [hpowk]
    have hsum2 : (∑ j ∈ Finset.range k, 2 ^ (k - j)) * k ^ k ≤ 2 * 2 ^ k * k ^ k :=
      Nat.mul_le_mul_right _ (sum_two_pow_le k)
    calc
      (∑ j ∈ Finset.range k, 2 ^ k * (k.choose (j + 1) * k ^ (k - (j + 1)))) + 2 ^ k * k ^ k
          ≤ 2 * 2 ^ k * k ^ k + 2 ^ k * k ^ k := Nat.add_le_add_right (le_trans hrest hsum2) _
      _ = 2 ^ k * (3 * k ^ k) := by ring

private lemma pow_le_three_pow_mul_factorial (k : ℕ) : k ^ k ≤ 3 ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := add_one_pow_le_three_mul_pow k
    calc
      (k + 1) ^ (k + 1) = (k + 1) * (k + 1) ^ k := by rw [pow_succ']
      _ ≤ (k + 1) * (3 * k ^ k) := Nat.mul_le_mul_left _ h1
      _ ≤ (k + 1) * (3 * (3 ^ k * k.factorial)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ih)
      _ = 3 ^ (k + 1) * (k + 1).factorial := by
        rw [Nat.factorial_succ, pow_succ']; ring

private lemma choose_upper_bound (n k : ℕ) : k ^ k * n.choose k ≤ (3 * n) ^ k := by
  have h1 := pow_le_three_pow_mul_factorial k
  have h2 := fact_mul_choose_le_pow n k
  calc
    k ^ k * n.choose k ≤ (3 ^ k * k.factorial) * n.choose k := Nat.mul_le_mul_right _ h1
    _ = 3 ^ k * (k.factorial * n.choose k) := by ring
    _ ≤ 3 ^ k * n ^ k := Nat.mul_le_mul_left _ h2
    _ = (3 * n) ^ k := by rw [mul_pow]

private lemma choose_lower_bound : ∀ (a n : ℕ), a ≤ n → n ^ a ≤ a ^ a * n.choose a
  | 0, n, _ => by simp
  | a + 1, 0, h => by omega
  | a + 1, M + 1, h => by
    have haM : a ≤ M := by omega
    have ih := choose_lower_bound a M haM
    have hchoose : (a + 1) * (M + 1).choose (a + 1) = (M + 1) * M.choose a := by
      have := Nat.add_one_mul_choose_eq M a
      linarith
    have hmul : a * (M + 1) ≤ (a + 1) * M := by nlinarith
    have hpow : a ^ a * (M + 1) ^ a ≤ (a + 1) ^ a * M ^ a := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hmul a
    have haa_pos : 0 < a ^ a := by
      cases a with
      | zero => simp
      | succ k => positivity
    have hstep : a ^ a * (M + 1) ^ a ≤ a ^ a * ((a + 1) ^ a * M.choose a) := by
      calc
        a ^ a * (M + 1) ^ a ≤ (a + 1) ^ a * M ^ a := hpow
        _ ≤ (a + 1) ^ a * (a ^ a * M.choose a) := Nat.mul_le_mul_left _ ih
        _ = a ^ a * ((a + 1) ^ a * M.choose a) := by ring
    have hbase : (M + 1) ^ a ≤ (a + 1) ^ a * M.choose a :=
      Nat.le_of_mul_le_mul_left hstep haa_pos
    calc
      (M + 1) ^ (a + 1) = (M + 1) * (M + 1) ^ a := by rw [pow_succ']
      _ ≤ (M + 1) * ((a + 1) ^ a * M.choose a) := Nat.mul_le_mul_left _ hbase
      _ = (a + 1) ^ a * ((M + 1) * M.choose a) := by ring
      _ = (a + 1) ^ a * ((a + 1) * (M + 1).choose (a + 1)) := by rw [← hchoose]
      _ = (a + 1) ^ (a + 1) * (M + 1).choose (a + 1) := by rw [pow_succ']; ring

private lemma choose_lower_pow (N a k : ℕ) (hka : k ≤ a) (haN : a ≤ N) (ha_pos : 0 < a) :
    N ^ k ≤ a ^ k * N.choose a := by
  have h1 := choose_lower_bound a N haN
  have hsplit : a = k + (a - k) := by omega
  have hpowN : N ^ a = N ^ k * N ^ (a - k) := by rw [← pow_add, ← hsplit]
  have hpowa : a ^ a = a ^ k * a ^ (a - k) := by rw [← pow_add, ← hsplit]
  have hrem : a ^ (a - k) ≤ N ^ (a - k) := Nat.pow_le_pow_left haN (a - k)
  have hrem_pos : 0 < a ^ (a - k) := Nat.pow_pos ha_pos
  have hcomb : a ^ (a - k) * N ^ k ≤ a ^ (a - k) * (a ^ k * N.choose a) := by
    calc
      a ^ (a - k) * N ^ k ≤ N ^ (a - k) * N ^ k := Nat.mul_le_mul_right _ hrem
      _ = N ^ a := by rw [hpowN]; ring
      _ ≤ a ^ a * N.choose a := h1
      _ = a ^ (a - k) * (a ^ k * N.choose a) := by rw [hpowa]; ring
  exact Nat.le_of_mul_le_mul_left hcomb hrem_pos

private lemma mul_succ_le_four_pow : ∀ t : ℕ, 1 ≤ t → t * (t + 1) ≤ 4 ^ t
  | 0, h => by omega
  | 1, _ => by norm_num
  | t + 2, _ => by
    have ih := mul_succ_le_four_pow (t + 1) (by omega)
    have h1 : (t + 2) * (t + 3) ≤ 4 * ((t + 1) * (t + 2)) := by nlinarith
    have h2 : 4 * ((t + 1) * (t + 2)) ≤ 4 * 4 ^ (t + 1) := Nat.mul_le_mul_left 4 ih
    have h3 : 4 * 4 ^ (t + 1) = 4 ^ (t + 2) := by ring
    exact le_trans h1 (h2.trans_eq h3)

private lemma union_bound_ineq (N t a0 a1 : ℕ)
    (hN : 0 < N) (ht : 1 ≤ t)
    (ha0_lo : 24 * t ≤ a0) (ha0_hi : a0 ≤ 51 * t) (ha0_N : 5 * a0 ≤ 3 * N)
    (ha1_lo : 24 * t ≤ a1) (ha1_hi : a1 ≤ 51 * t) (ha1_N : 5 * a1 ≤ 3 * N) :
    8 * N * (t + 1) * (6 * N).choose t < N.choose a0 * N.choose a1 := by
  have ha0_leN : a0 ≤ N := by omega
  have ha1_leN : a1 ≤ N := by omega
  have ha0_pos : 0 < a0 := by omega
  have ha1_pos : 0 < a1 := by omega
  have hlo0 : N ^ (24 * t) ≤ a0 ^ (24 * t) * N.choose a0 :=
    choose_lower_pow N a0 (24 * t) ha0_lo ha0_leN ha0_pos
  have hlo1 : N ^ (24 * t) ≤ a1 ^ (24 * t) * N.choose a1 :=
    choose_lower_pow N a1 (24 * t) ha1_lo ha1_leN ha1_pos
  set E := 47 * t - 1
  have hE_add : E + (t + 1) = 48 * t := by omega
  have hE_split : E = 23 * t + (24 * t - 1) := by omega
  have hE_ge : 30 * t ≤ E := by omega
  have ha0_split : a0 ^ (24 * t) = a0 ^ (23 * t) * a0 ^ t := by
    rw [← pow_add]; congr 1; omega
  have ha1_split : a1 ^ (24 * t) = a1 ^ (24 * t - 1) * a1 := by
    rw [← pow_succ]; congr 1; omega
  have h5a0 : 5 ^ (23 * t) * a0 ^ (23 * t) ≤ (3 * N) ^ (23 * t) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left ha0_N _
  have h5a1 : 5 ^ (24 * t - 1) * a1 ^ (24 * t - 1) ≤ (3 * N) ^ (24 * t - 1) := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left ha1_N _
  have h5_prod : 5 ^ E * (a0 ^ (24 * t) * a1 ^ (24 * t)) ≤
      (3 * N) ^ E * (51 * t) ^ (t + 1) := by
    have hpow5 : 5 ^ E = 5 ^ (23 * t) * 5 ^ (24 * t - 1) := by rw [hE_split, pow_add]
    have hpow3N : (3 * N) ^ E = (3 * N) ^ (23 * t) * (3 * N) ^ (24 * t - 1) := by
      rw [hE_split, pow_add]
    have hpow51 : (51 * t) ^ (t + 1) = (51 * t) ^ t * (51 * t) := by rw [pow_succ]
    have hhi0 : a0 ^ t ≤ (51 * t) ^ t := Nat.pow_le_pow_left ha0_hi t
    have hm1 : (5 ^ (23 * t) * a0 ^ (23 * t)) * (5 ^ (24 * t - 1) * a1 ^ (24 * t - 1)) ≤
        (3 * N) ^ (23 * t) * (3 * N) ^ (24 * t - 1) := Nat.mul_le_mul h5a0 h5a1
    have hm2 : a0 ^ t * a1 ≤ (51 * t) ^ t * (51 * t) := Nat.mul_le_mul hhi0 ha1_hi
    calc
      5 ^ E * (a0 ^ (24 * t) * a1 ^ (24 * t))
          = ((5 ^ (23 * t) * a0 ^ (23 * t)) * (5 ^ (24 * t - 1) * a1 ^ (24 * t - 1))) *
              (a0 ^ t * a1) := by rw [hpow5, ha0_split, ha1_split]; ring
      _ ≤ ((3 * N) ^ (23 * t) * (3 * N) ^ (24 * t - 1)) * ((51 * t) ^ t * (51 * t)) :=
            Nat.mul_le_mul hm1 hm2
      _ = (3 * N) ^ E * (51 * t) ^ (t + 1) := by rw [hpow3N, hpow51]
  have hN48 : N ^ (48 * t) ≤ a0 ^ (24 * t) * a1 ^ (24 * t) * (N.choose a0 * N.choose a1) := by
    calc
      N ^ (48 * t) = N ^ (24 * t) * N ^ (24 * t) := by rw [← pow_add]; congr 1; omega
      _ ≤ (a0 ^ (24 * t) * N.choose a0) * (a1 ^ (24 * t) * N.choose a1) :=
            Nat.mul_le_mul hlo0 hlo1
      _ = a0 ^ (24 * t) * a1 ^ (24 * t) * (N.choose a0 * N.choose a1) := by ring
  have hRHS_big : N ^ E * (5 ^ E * N ^ (t + 1)) ≤
      N ^ E * (3 ^ E * (51 * t) ^ (t + 1) * (N.choose a0 * N.choose a1)) := by
    have hNE : N ^ (48 * t) = N ^ E * N ^ (t + 1) := by rw [← pow_add, hE_add]
    calc
      N ^ E * (5 ^ E * N ^ (t + 1)) = 5 ^ E * N ^ (48 * t) := by rw [hNE]; ring
      _ ≤ 5 ^ E * (a0 ^ (24 * t) * a1 ^ (24 * t) * (N.choose a0 * N.choose a1)) :=
            Nat.mul_le_mul_left _ hN48
      _ = (5 ^ E * (a0 ^ (24 * t) * a1 ^ (24 * t))) * (N.choose a0 * N.choose a1) := by ring
      _ ≤ ((3 * N) ^ E * (51 * t) ^ (t + 1)) * (N.choose a0 * N.choose a1) :=
            Nat.mul_le_mul_right _ h5_prod
      _ = N ^ E * (3 ^ E * (51 * t) ^ (t + 1) * (N.choose a0 * N.choose a1)) := by
            rw [mul_pow]; ring
  have hRHS : 5 ^ E * N ^ (t + 1) ≤ 3 ^ E * (51 * t) ^ (t + 1) * (N.choose a0 * N.choose a1) :=
    Nat.le_of_mul_le_mul_left hRHS_big (Nat.pow_pos hN)
  have hch_up : t ^ t * (6 * N).choose t ≤ (18 * N) ^ t := by
    have h18 : 3 * (6 * N) = 18 * N := by ring
    simpa [h18] using choose_upper_bound (6 * N) t
  have hLHS : 3 ^ E * (51 * t) ^ (t + 1) * (8 * N * (t + 1) * (6 * N).choose t) ≤
      (408 * (t * (t + 1)) * 918 ^ t * 3 ^ E) * N ^ (t + 1) := by
    have h51 : (51 * t) ^ (t + 1) = (51 * t) * (51 ^ t * t ^ t) := by
      rw [pow_succ', mul_pow]
    have h18 : (18 * N) ^ t = 18 ^ t * N ^ t := mul_pow 18 N t
    have h918 : 51 ^ t * 18 ^ t = 918 ^ t := by rw [← mul_pow]; rfl
    have hNt : N * N ^ t = N ^ (t + 1) := by rw [pow_succ']
    calc
      3 ^ E * (51 * t) ^ (t + 1) * (8 * N * (t + 1) * (6 * N).choose t)
          = 408 * (t * (t + 1)) * 51 ^ t * 3 ^ E * N * (t ^ t * (6 * N).choose t) := by
            rw [h51]; ring
      _ ≤ 408 * (t * (t + 1)) * 51 ^ t * 3 ^ E * N * (18 * N) ^ t :=
            Nat.mul_le_mul_left _ hch_up
      _ = (408 * (t * (t + 1)) * (51 ^ t * 18 ^ t) * 3 ^ E) * (N * N ^ t) := by
            rw [h18]; ring
      _ = (408 * (t * (t + 1)) * 918 ^ t * 3 ^ E) * N ^ (t + 1) := by rw [h918, hNt]
  have hcoeff : 408 * (t * (t + 1)) * 918 ^ t * 3 ^ E < 5 ^ E := by
    have h408 : 408 ≤ 408 ^ t := Nat.le_self_pow (by omega) 408
    have h4t : t * (t + 1) ≤ 4 ^ t := mul_succ_le_four_pow t ht
    have hprod_t : 408 * (t * (t + 1)) * 918 ^ t ≤ 1498176 ^ t := by
      have h1 : 408 * (t * (t + 1)) ≤ 408 ^ t * 4 ^ t := Nat.mul_le_mul h408 h4t
      have h2 : 408 * (t * (t + 1)) * 918 ^ t ≤ (408 ^ t * 4 ^ t) * 918 ^ t :=
        Nat.mul_le_mul_right _ h1
      have h3 : (408 ^ t * 4 ^ t) * 918 ^ t = 1498176 ^ t := by
        rw [← mul_pow, ← mul_pow]; rfl
      exact h2.trans_eq h3
    have hconst : 1498176 * 3 ^ 30 < 5 ^ 30 := by norm_num
    have hpow_lt : (1498176 * 3 ^ 30) ^ t < (5 ^ 30) ^ t :=
      Nat.pow_lt_pow_left hconst (by omega)
    have hE_rem : 3 ^ (E - 30 * t) ≤ 5 ^ (E - 30 * t) := Nat.pow_le_pow_left (by omega) _
    have h3E : 3 ^ E = (3 ^ 30) ^ t * 3 ^ (E - 30 * t) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have h5E : 5 ^ E = (5 ^ 30) ^ t * 5 ^ (E - 30 * t) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have hpos_rem : 0 < 3 ^ (E - 30 * t) := by positivity
    calc
      408 * (t * (t + 1)) * 918 ^ t * 3 ^ E
          ≤ 1498176 ^ t * 3 ^ E := Nat.mul_le_mul_right _ hprod_t
      _ = (1498176 * 3 ^ 30) ^ t * 3 ^ (E - 30 * t) := by rw [h3E, mul_pow]; ring
      _ < (5 ^ 30) ^ t * 3 ^ (E - 30 * t) := Nat.mul_lt_mul_of_pos_right hpow_lt hpos_rem
      _ ≤ (5 ^ 30) ^ t * 5 ^ (E - 30 * t) := Nat.mul_le_mul_left _ hE_rem
      _ = 5 ^ E := h5E.symm
  have hstrict :
      3 ^ E * (51 * t) ^ (t + 1) * (8 * N * (t + 1) * (6 * N).choose t) <
        3 ^ E * (51 * t) ^ (t + 1) * (N.choose a0 * N.choose a1) := by
    calc
      3 ^ E * (51 * t) ^ (t + 1) * (8 * N * (t + 1) * (6 * N).choose t)
          ≤ (408 * (t * (t + 1)) * 918 ^ t * 3 ^ E) * N ^ (t + 1) := hLHS
      _ < 5 ^ E * N ^ (t + 1) := Nat.mul_lt_mul_of_pos_right hcoeff (Nat.pow_pos hN)
      _ ≤ 3 ^ E * (51 * t) ^ (t + 1) * (N.choose a0 * N.choose a1) := hRHS
  exact Nat.lt_of_mul_lt_mul_left hstrict

private lemma choose_le_of_le_half (M s t : ℕ) (hst : s ≤ t) (ht : 2 * t ≤ M) :
    M.choose s ≤ M.choose t := by
  induction hst with
  | refl => exact le_rfl
  | @step m hsm ih =>
    have hm : 2 * (m + 1) ≤ M := by omega
    have hstep : M.choose m ≤ M.choose (m + 1) := by
      have hid : (m + 1) * M.choose (m + 1) = (M - m) * M.choose m := by
        have := Nat.choose_succ_right_eq M m
        linarith
      have hle : (m + 1) * M.choose m ≤ (M - m) * M.choose m :=
        Nat.mul_le_mul_right _ (by omega)
      rw [← hid] at hle
      exact Nat.le_of_mul_le_mul_left hle (by omega)
    exact le_trans (ih (by omega)) hstep

private def cycStep (M : ℕ) (hM : 0 < M) (p : Fin M) (j : ℕ) : Fin M :=
  ⟨(p.val + j) % M, Nat.mod_lt _ hM⟩

private def cycDist (M : ℕ) (p q : Fin M) : ℕ :=
  (q.val + M - p.val) % M

private lemma cycStep_zero (M : ℕ) (hM : 0 < M) (p : Fin M) : cycStep M hM p 0 = p := by
  ext
  simp [cycStep, Nat.mod_eq_of_lt p.isLt]

private lemma cycStep_add (M : ℕ) (hM : 0 < M) (p : Fin M) (a b : ℕ) :
    cycStep M hM (cycStep M hM p a) b = cycStep M hM p (a + b) := by
  ext
  simp [cycStep, Nat.mod_add_mod, Nat.add_assoc]

private lemma cycStep_inj (M : ℕ) (hM : 0 < M) (p : Fin M) (j1 j2 : ℕ)
    (h1 : j1 < M) (h2 : j2 < M) (heq : cycStep M hM p j1 = cycStep M hM p j2) : j1 = j2 := by
  have hv : (p.val + j1) % M = (p.val + j2) % M := congrArg Fin.val heq
  have hp := p.isLt
  by_cases c1 : p.val + j1 < M <;> by_cases c2 : p.val + j2 < M
  · rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_of_lt c2] at hv; omega
  · have hlt2 : p.val + j2 - M < M := by omega
    rw [Nat.mod_eq_of_lt c1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hv
    omega
  · have hlt1 : p.val + j1 - M < M := by omega
    rw [Nat.mod_eq_of_lt c2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1] at hv
    omega
  · have hlt1 : p.val + j1 - M < M := by omega
    have hlt2 : p.val + j2 - M < M := by omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at hv
    omega

private lemma cycDist_lt_of_step_eq (M L : ℕ) (hM : 0 < M) (hLM : L ≤ M)
    (p q : Fin M) (j1 j2 : ℕ) (h1 : j1 < L) (h2 : j2 < L)
    (heq : cycStep M hM p j1 = cycStep M hM q j2) :
    cycDist M p q < L ∨ cycDist M q p < L := by
  have hv : (p.val + j1) % M = (q.val + j2) % M := congrArg Fin.val heq
  have hp := p.isLt
  have hq := q.isLt
  by_cases hle : j2 ≤ j1
  · left
    have hdiff : (q.val + M - p.val) % M = j1 - j2 := by
      have hmod1 : (q.val + M - p.val + j2) % M = (j1 + M) % M := by
        have hsum : q.val + M - p.val + j2 + p.val = q.val + j2 + M := by omega
        have h2' : (q.val + j2 + M) % M = (p.val + j1) % M := by
          rw [Nat.add_mod_right]; exact hv.symm
        have h3' : (q.val + M - p.val + j2) % M = (j1) % M := by
          have : (q.val + M - p.val + j2 + p.val) % M = (j1 + p.val) % M := by
            rw [hsum, h2', Nat.add_comm]
          have := Nat.ModEq.add_right_cancel' p.val this
          exact this
        rw [Nat.add_mod_right]
        exact h3'
      have h4' : (q.val + M - p.val) % M = (j1 - j2) % M := by
        have h5 : (q.val + M - p.val + j2) % M = (j1 - j2 + j2) % M := by
          rw [hmod1, Nat.add_mod_right, Nat.sub_add_cancel hle]
        exact Nat.ModEq.add_right_cancel' j2 h5
      rw [h4', Nat.mod_eq_of_lt (by omega)]
    rw [cycDist, hdiff]
    omega
  · right
    have hle' : j1 ≤ j2 := by omega
    have hdiff : (p.val + M - q.val) % M = j2 - j1 := by
      have hmod1 : (p.val + M - q.val + j1) % M = j2 % M := by
        have hsum : p.val + M - q.val + j1 + q.val = p.val + j1 + M := by omega
        have h2' : (p.val + j1 + M) % M = (q.val + j2) % M := by
          rw [Nat.add_mod_right]; exact hv
        have : (p.val + M - q.val + j1 + q.val) % M = (j2 + q.val) % M := by
          rw [hsum, h2', Nat.add_comm]
        exact Nat.ModEq.add_right_cancel' q.val this
      have h4' : (p.val + M - q.val) % M = (j2 - j1) % M := by
        have h5 : (p.val + M - q.val + j1) % M = (j2 - j1 + j1) % M := by
          rw [hmod1, Nat.sub_add_cancel hle']
        exact Nat.ModEq.add_right_cancel' j1 h5
      rw [h4', Nat.mod_eq_of_lt (by omega)]
    rw [cycDist, hdiff]
    omega

private lemma cycle_tf_eq_ft (M : ℕ) (hM : 0 < M) (z : Fin M → Bool) :
    2 * (Finset.univ.filter (fun p : Fin M =>
      z p = true ∧ z (cycStep M hM p 1) = false)).card =
      (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card := by
  let e : Fin M ≃ Fin M :=
    { toFun := fun p => cycStep M hM p 1
      invFun := fun p => ⟨(p.val + M - 1) % M, Nat.mod_lt _ hM⟩
      left_inv := fun p => by
        ext
        simp only [cycStep]
        have hp := p.isLt
        by_cases h : p.val + 1 < M
        · rw [Nat.mod_eq_of_lt h]
          have : p.val + 1 + M - 1 = p.val + M := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hp]
        · have hp1 : p.val + 1 = M := by omega
          rw [hp1, Nat.mod_self]
          have : 0 + M - 1 = p.val := by omega
          rw [this, Nat.mod_eq_of_lt hp]
      right_inv := fun p => by
        ext
        simp only [cycStep]
        have hp := p.isLt
        by_cases h : p.val = 0
        · rw [h]
          have h1 : 0 + M - 1 = M - 1 := by omega
          have h2 : (M - 1) % M = M - 1 := Nat.mod_eq_of_lt (by omega)
          have h3 : M - 1 + 1 = M := by omega
          rw [h1, h2, h3, Nat.mod_self]
        · have hlt : p.val - 1 < M := by omega
          have : (p.val + M - 1) % M = p.val - 1 := by
            have h1 : p.val + M - 1 = (p.val - 1) + M := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
          rw [this]
          have : p.val - 1 + 1 = p.val := by omega
          rw [this, Nat.mod_eq_of_lt hp] }
  let S_tf := Finset.univ.filter (fun p : Fin M => z p = true ∧ z (e p) = false)
  let S_ft := Finset.univ.filter (fun p : Fin M => z p = false ∧ z (e p) = true)
  let S_tt := Finset.univ.filter (fun p : Fin M => z p = true ∧ z (e p) = true)
  let S_t := Finset.univ.filter (fun p : Fin M => z p = true)
  let S_nt := Finset.univ.filter (fun p : Fin M => z (e p) = true)
  have hshift : S_nt.card = S_t.card := by
    refine Finset.card_bij (fun p _ => e p) ?_ ?_ ?_
    · intro p hp
      simp only [S_nt, S_t, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact hp
    · intro a _ b _ hab; exact e.injective hab
    · intro b hb
      refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
      simp only [S_nt, S_t, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      simpa using hb
  have h1 : S_tf.card + S_tt.card = S_t.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p
      simp only [S_tf, S_tt, S_t, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases z p <;> cases z (e p) <;> simp
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [S_tf, S_tt, Finset.mem_filter] at hp1 hp2
      rw [hp1.2.2] at hp2
      exact Bool.false_ne_true hp2.2.2
  have h2 : S_ft.card + S_tt.card = S_nt.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p
      simp only [S_ft, S_tt, S_nt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases z p <;> cases z (e p) <;> simp
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [S_ft, S_tt, Finset.mem_filter] at hp1 hp2
      rw [hp1.2.1] at hp2
      exact Bool.false_ne_true hp2.2.1
  have h3 : S_tf.card + S_ft.card =
      (Finset.univ.filter (fun p : Fin M => z p ≠ z (e p))).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p
      simp only [S_tf, S_ft, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      cases z p <;> cases z (e p) <;> simp
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [S_tf, S_ft, Finset.mem_filter] at hp1 hp2
      rw [hp1.2.1] at hp2
      exact Bool.false_ne_true.symm hp2.2.1
  have heq : S_tf.card = S_ft.card := by omega
  change 2 * S_tf.card = (Finset.univ.filter (fun p : Fin M => z p ≠ z (e p))).card
  omega

private lemma cycle_port_spacing (M L : ℕ) (hM : 0 < M) (hL : 0 < L) (hLM : L ≤ M)
    (z : Fin M → Bool) (P : Finset (Fin M))
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → L ≤ cycDist M p q) :
    2 * L * (P.filter (fun p => z p = true)).card ≤
      L * (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card +
      2 * (Finset.univ.filter (fun p : Fin M => z p = true)).card := by
  let W : Fin M → Finset (Fin M) :=
    fun p => (Finset.range L).image (fun j => cycStep M hM p j)
  have hW_card : ∀ p : Fin M, (W p).card = L := by
    intro p
    rw [Finset.card_image_of_injOn]
    · exact Finset.card_range L
    · intro j1 hj1 j2 hj2 heq
      exact cycStep_inj M hM p j1 j2
        (lt_of_lt_of_le (Finset.mem_range.mp hj1) hLM)
        (lt_of_lt_of_le (Finset.mem_range.mp hj2) hLM) heq
  have hW_disj : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → Disjoint (W p) (W q) := by
    intro p hp q hq hne
    rw [Finset.disjoint_left]
    intro x hxp hxq
    rcases Finset.mem_image.mp hxp with ⟨j1, hj1, rfl⟩
    rcases Finset.mem_image.mp hxq with ⟨j2, hj2, heq⟩
    have hlt := cycDist_lt_of_step_eq M L hM hLM p q j1 j2
      (Finset.mem_range.mp hj1) (Finset.mem_range.mp hj2) heq.symm
    rcases hlt with h1 | h2
    · exact absurd (hsep p hp q hq hne) (by omega)
    · exact absurd (hsep q hq p hp hne.symm) (by omega)
  let Pt := P.filter (fun p => z p = true)
  let Pfull := Pt.filter (fun p => ∀ j ∈ Finset.range L, z (cycStep M hM p j) = true)
  let Pbdry := Pt.filter (fun p => ¬ ∀ j ∈ Finset.range L, z (cycStep M hM p j) = true)
  have hPt_split : Pt.card = Pfull.card + Pbdry.card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext p
      simp only [Pfull, Pbdry, Finset.mem_union, Finset.mem_filter]
      tauto
    · rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Pfull, Pbdry, Finset.mem_filter] at hp1 hp2
      exact hp2.2 hp1.2
  have hfull_bound : L * Pfull.card ≤ (Finset.univ.filter (fun u : Fin M => z u = true)).card := by
    have hsub : Pfull.biUnion W ⊆ Finset.univ.filter (fun u : Fin M => z u = true) := by
      intro u hu
      rcases Finset.mem_biUnion.mp hu with ⟨p, hp, huW⟩
      rcases Finset.mem_image.mp huW with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hp).2 j hj
    have hcard_u : (Pfull.biUnion W).card = Pfull.card * L := by
      rw [Finset.card_biUnion]
      · simp [hW_card]
      · intro p hp q hq hne
        exact hW_disj p (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
          q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1 hne
    have hle := Finset.card_le_card hsub
    rw [hcard_u] at hle
    linarith
  have hbdry_exists : ∀ p ∈ Pbdry,
      ∃ j < L, z (cycStep M hM p j) = true ∧ z (cycStep M hM p (j + 1)) = false := by
    intro p hp
    have hpPt : p ∈ Pt := (Finset.mem_filter.mp hp).1
    have hzp : z p = true := (Finset.mem_filter.mp hpPt).2
    have hnot : ¬ ∀ j ∈ Finset.range L, z (cycStep M hM p j) = true := (Finset.mem_filter.mp hp).2
    push_neg at hnot
    rcases hnot with ⟨k, hk, hzk⟩
    have hkL : k < L := Finset.mem_range.mp hk
    have hzkf : z (cycStep M hM p k) = false := by
      cases h : z (cycStep M hM p k)
      · rfl
      · exact absurd h hzk
    have hfind : ∀ n, n < L → z (cycStep M hM p n) = false →
        ∃ j < n, z (cycStep M hM p j) = true ∧ z (cycStep M hM p (j + 1)) = false := by
      intro n
      induction n with
      | zero =>
        intro _ h0
        rw [cycStep_zero] at h0
        rw [hzp] at h0
        exact absurd h0 Bool.false_ne_true.symm
      | succ m ih =>
        intro hm hmf
        cases hz_m : z (cycStep M hM p m)
        · rcases ih (by omega) hz_m with ⟨j, hj, ht, hf⟩
          exact ⟨j, by omega, ht, hf⟩
        · exact ⟨m, by omega, hz_m, hmf⟩
    rcases hfind k hkL hzkf with ⟨j, hj, ht, hf⟩
    exact ⟨j, by omega, ht, hf⟩
  have hbdry_bound : Pbdry.card ≤
      (Finset.univ.filter (fun u : Fin M => z u = true ∧ z (cycStep M hM u 1) = false)).card := by
    classical
    let wit : Fin M → Fin M := fun p =>
      if h : p ∈ Pbdry then cycStep M hM p (Classical.choose (hbdry_exists p h)) else p
    refine Finset.card_le_card_of_injOn wit ?_ ?_
    · intro p hp
      have hp' : p ∈ Pbdry := Finset.mem_coe.mp hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [wit, dif_pos hp']
      have hspec := Classical.choose_spec (hbdry_exists p hp')
      refine ⟨hspec.2.1, ?_⟩
      rw [cycStep_add]
      exact hspec.2.2
    · intro p1 hp1 p2 hp2 heq
      by_contra hne
      simp only [Finset.mem_coe] at hp1 hp2
      have h1 := Classical.choose_spec (hbdry_exists p1 hp1)
      have h2 := Classical.choose_spec (hbdry_exists p2 hp2)
      have hmem1 : wit p1 ∈ W p1 := by
        simp only [wit, dif_pos hp1, W, Finset.mem_image, Finset.mem_range]
        exact ⟨_, h1.1, rfl⟩
      have hmem2 : wit p2 ∈ W p2 := by
        simp only [wit, dif_pos hp2, W, Finset.mem_image, Finset.mem_range]
        exact ⟨_, h2.1, rfl⟩
      rw [heq] at hmem1
      have hdisj := hW_disj p1 (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1
        p2 (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1 hne
      exact Finset.disjoint_left.mp hdisj hmem1 hmem2
  have htf := cycle_tf_eq_ft M hM z
  have h2bdry : 2 * Pbdry.card ≤
      (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card := by omega
  have hLbdry : 2 * L * Pbdry.card ≤
      L * (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card := by
    calc
      2 * L * Pbdry.card = L * (2 * Pbdry.card) := by ring
      _ ≤ L * (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card :=
            Nat.mul_le_mul_left L h2bdry
  have hLfull : 2 * L * Pfull.card ≤
      2 * (Finset.univ.filter (fun p : Fin M => z p = true)).card := by
    calc
      2 * L * Pfull.card = 2 * (L * Pfull.card) := by ring
      _ ≤ 2 * (Finset.univ.filter (fun p : Fin M => z p = true)).card :=
            Nat.mul_le_mul_left 2 hfull_bound
  calc
    2 * L * Pt.card = 2 * L * Pfull.card + 2 * L * Pbdry.card := by rw [hPt_split]; ring
    _ ≤ 2 * (Finset.univ.filter (fun p : Fin M => z p = true)).card +
        L * (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card :=
          Nat.add_le_add hLfull hLbdry
    _ = L * (Finset.univ.filter (fun p : Fin M => z p ≠ z (cycStep M hM p 1))).card +
        2 * (Finset.univ.filter (fun p : Fin M => z p = true)).card := by ring

section RingGeometry

variable (b : ℕ)

private abbrev Nval (b : ℕ) : ℕ := b + 1

private def ringVert (b : ℕ) (r : Bool) (p : Fin (2 * (b + 1))) : Bool × (Bool × Fin (b + 1)) :=
  if p.val % 2 = 0 then
    (false, (r, ⟨p.val / 2, by omega⟩))
  else
    (true, (r, ⟨(p.val / 2 + 1) % (b + 1), Nat.mod_lt _ (by omega)⟩))

private def ringPos (b : ℕ) (s : Bool) (k : Fin (b + 1)) : Fin (2 * (b + 1)) :=
  if s = false then
    ⟨2 * k.val, by omega⟩
  else
    ⟨if k.val = 0 then 2 * (b + 1) - 1 else 2 * k.val - 1, by split_ifs <;> omega⟩

private lemma ringVert_ringPos (b : ℕ) (r s : Bool) (k : Fin (b + 1)) :
    ringVert b r (ringPos b s k) = (s, (r, k)) := by
  cases s
  · simp only [ringPos, ringVert, ↓reduceIte]
    have hmod : (2 * k.val) % 2 = 0 := by omega
    rw [if_pos hmod]
    ext <;> simp
  · by_cases hk : k.val = 0
    · have hp : ringPos b true k = ⟨2 * (b + 1) - 1, by omega⟩ := by
        ext; simp [ringPos, hk]
      rw [hp]
      unfold ringVert
      have hmod : (2 * (b + 1) - 1) % 2 ≠ 0 := by omega
      rw [if_neg hmod]
      have hdiv : ((2 * (b + 1) - 1) / 2 + 1) % (b + 1) = 0 := by
        have h1 : (2 * (b + 1) - 1) / 2 + 1 = b + 1 := by omega
        rw [h1, Nat.mod_self]
      ext
      · rfl
      · rfl
      · simp [hdiv, hk]
    · have hp : ringPos b true k = ⟨2 * k.val - 1, by omega⟩ := by
        ext; simp [ringPos, hk]
      rw [hp]
      unfold ringVert
      have hmod : (2 * k.val - 1) % 2 ≠ 0 := by omega
      rw [if_neg hmod]
      have hdiv : ((2 * k.val - 1) / 2 + 1) % (b + 1) = k.val := by
        have h1 : (2 * k.val - 1) / 2 + 1 = k.val := by omega
        rw [h1, Nat.mod_eq_of_lt k.isLt]
      ext
      · rfl
      · rfl
      · simp [hdiv]

private lemma ringPos_ringVert (b : ℕ) (r : Bool) (p : Fin (2 * (b + 1))) :
    ringPos b (ringVert b r p).1 (ringVert b r p).2.2 = p := by
  ext
  by_cases h : p.val % 2 = 0
  · simp only [ringVert, if_pos h, ringPos, ↓reduceIte]
    omega
  · simp only [ringVert, if_neg h, ringPos, Bool.true_eq_false, ↓reduceIte]
    by_cases htop : p.val / 2 + 1 = b + 1
    · have hmod : (p.val / 2 + 1) % (b + 1) = 0 := by rw [htop, Nat.mod_self]
      rw [if_pos hmod]
      omega
    · have hlt : p.val / 2 + 1 < b + 1 := by omega
      have hmod : (p.val / 2 + 1) % (b + 1) = p.val / 2 + 1 := Nat.mod_eq_of_lt hlt
      have hne : (p.val / 2 + 1) % (b + 1) ≠ 0 := by rw [hmod]; omega
      rw [if_neg hne, hmod]
      omega

private lemma ringVert_ring (b : ℕ) (r : Bool) (p : Fin (2 * (b + 1))) :
    (ringVert b r p).2.1 = r := by
  unfold ringVert
  split_ifs <;> rfl

private lemma ringVert_inj (b : ℕ) (r : Bool) : Function.Injective (ringVert b r) := by
  intro p1 p2 heq
  have h1 := ringPos_ringVert b r p1
  have h2 := ringPos_ringVert b r p2
  rw [heq] at h1
  exact h1.symm.trans h2

private lemma fin_add_one_val (b : ℕ) (k : Fin (b + 1)) :
    (k + 1).val = (k.val + 1) % (b + 1) := by
  change (k.val + (1 % (b + 1))) % (b + 1) = (k.val + 1) % (b + 1)
  rw [Nat.add_mod_mod]

private lemma ringVert_step_even (b : ℕ) (r : Bool) (k : Fin (b + 1)) :
    ringVert b r (cycStep (2 * (b + 1)) (by omega) ⟨2 * k.val, by omega⟩ 1) =
      (true, (r, k + 1)) := by
  have hlt : 2 * k.val + 1 < 2 * (b + 1) := by omega
  have hstep : cycStep (2 * (b + 1)) (by omega) ⟨2 * k.val, by omega⟩ 1 = ⟨2 * k.val + 1, hlt⟩ := by
    ext; simp [cycStep, Nat.mod_eq_of_lt hlt]
  rw [hstep]
  unfold ringVert
  have hodd : (2 * k.val + 1) % 2 ≠ 0 := by omega
  rw [if_neg hodd]
  ext
  · rfl
  · rfl
  · simp [fin_add_one_val]
    have : (2 * k.val + 1) / 2 = k.val := by omega
    rw [this]

private lemma ringVert_step_odd (b : ℕ) (r : Bool) (k : Fin (b + 1)) :
    ringVert b r (cycStep (2 * (b + 1)) (by omega) (ringPos b true k) 1) =
      (false, (r, k)) := by
  have hstep : cycStep (2 * (b + 1)) (by omega) (ringPos b true k) 1 = ringPos b false k := by
    ext
    simp only [cycStep, ringPos, Bool.true_eq_false, ↓reduceIte]
    by_cases hk : k.val = 0
    · rw [if_pos hk, hk]
      have : 2 * (b + 1) - 1 + 1 = 2 * (b + 1) := by omega
      rw [this, Nat.mod_self]
    · rw [if_neg hk]
      have : 2 * k.val - 1 + 1 = 2 * k.val := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [hstep, ringVert_ringPos]

private def ringB (b : ℕ) (r : Bool) (y : Bool × (Bool × Fin (b + 1)) → Bool) : ℕ :=
  (Finset.univ.filter (fun p : Fin (2 * (b + 1)) =>
    y (ringVert b r p) ≠ y (ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1)))).card

private lemma ringB_eq_red_add_blue (b : ℕ) (y : Bool × (Bool × Fin (b + 1)) → Bool) :
    ringB b false y + ringB b true y =
      (Finset.univ.filter (fun i : Bool × Fin (b + 1) => y (false, i) ≠ y (true, i))).card +
      (Finset.univ.filter (fun i : Bool × Fin (b + 1) =>
        y (false, i) ≠ y (true, (i.1, i.2 + 1)))).card := by
  have hsingle : ∀ r : Bool,
      ringB b r y =
        (Finset.univ.filter (fun k : Fin (b + 1) => y (false, (r, k)) ≠ y (true, (r, k)))).card +
        (Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (r, k)) ≠ y (true, (r, k + 1)))).card := by
    intro r
    let S := Finset.univ.filter (fun p : Fin (2 * (b + 1)) =>
      y (ringVert b r p) ≠ y (ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1)))
    let Seven := S.filter (fun p => p.val % 2 = 0)
    let Sodd := S.filter (fun p => p.val % 2 ≠ 0)
    have hsplit : S.card = Sodd.card + Seven.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext p
        simp only [Sodd, Seven, Finset.mem_union, Finset.mem_filter]
        tauto
      · rw [Finset.disjoint_left]
        intro p h1 h2
        exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hblue_eq : Seven.card =
        (Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (r, k)) ≠ y (true, (r, k + 1)))).card := by
      refine Finset.card_bij (fun p _ => (ringVert b r p).2.2) ?_ ?_ ?_
      · intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hev := (Finset.mem_filter.mp hp).2
        have hplt : p.val < 2 * (b + 1) := p.isLt
        let k : Fin (b + 1) := ⟨p.val / 2, by omega⟩
        have hpval : p = ⟨2 * k.val, by omega⟩ := by ext; dsimp only [k]; omega
        have hrv : ringVert b r p = (false, (r, k)) := by
          unfold ringVert; rw [if_pos hev]
        have hstep : ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1) = (true, (r, k + 1)) := by
          have h1 : cycStep (2 * (b + 1)) (by omega) p 1 =
              cycStep (2 * (b + 1)) (by omega) ⟨2 * k.val, by omega⟩ 1 := by
            congr 1
          rw [h1]
          exact ringVert_step_even b r k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hne := (Finset.mem_filter.mp hpS).2
        rw [hrv, hstep] at hne
        rw [hrv]
        exact hne
      · intro p1 hp1 p2 hp2 heq
        have hev1 := (Finset.mem_filter.mp hp1).2
        have hev2 := (Finset.mem_filter.mp hp2).2
        have hv1 : (ringVert b r p1).2.2.val = p1.val / 2 := by unfold ringVert; rw [if_pos hev1]
        have hv2 : (ringVert b r p2).2.2.val = p2.val / 2 := by unfold ringVert; rw [if_pos hev2]
        have hval := congrArg Fin.val heq
        rw [hv1, hv2] at hval
        ext; omega
      · intro k hk
        refine ⟨ringPos b false k, ?_, ?_⟩
        · simp only [Seven, S, Finset.mem_filter, Finset.mem_univ, true_and]
          have hpos : ringPos b false k = ⟨2 * k.val, by omega⟩ := by
            simp [ringPos]
          refine ⟨?_, by simp [hpos]⟩
          rw [ringVert_ringPos, hpos, ringVert_step_even]
          exact (Finset.mem_filter.mp hk).2
        · simp [ringVert_ringPos]
    have hred_eq : Sodd.card =
        (Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (r, k)) ≠ y (true, (r, k)))).card := by
      refine Finset.card_bij (fun p _ => (ringVert b r p).2.2) ?_ ?_ ?_
      · intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        have hodd := (Finset.mem_filter.mp hp).2
        set k : Fin (b + 1) := (ringVert b r p).2.2
        have hrv : ringVert b r p = (true, (r, k)) := by
          have : (ringVert b r p).1 = true := by unfold ringVert; rw [if_neg hodd]
          have hrg := ringVert_ring b r p
          ext
          · exact this
          · exact hrg
          · rfl
        have hp_eq : p = ringPos b true k := by
          have := ringPos_ringVert b r p
          rw [hrv] at this
          exact this.symm
        have hstep : ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1) = (false, (r, k)) := by
          rw [hp_eq]; exact ringVert_step_odd b r k
        have hne := (Finset.mem_filter.mp hpS).2
        rw [hrv, hstep] at hne
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hne.symm
      · intro p1 hp1 p2 hp2 heq
        have hodd1 := (Finset.mem_filter.mp hp1).2
        have hodd2 := (Finset.mem_filter.mp hp2).2
        have h1 : ringVert b r p1 = (true, (r, (ringVert b r p1).2.2)) := by
          ext
          · unfold ringVert; rw [if_neg hodd1]
          · exact ringVert_ring b r p1
          · rfl
        have h2 : ringVert b r p2 = (true, (r, (ringVert b r p2).2.2)) := by
          ext
          · unfold ringVert; rw [if_neg hodd2]
          · exact ringVert_ring b r p2
          · rfl
        apply ringVert_inj b r
        rw [h1, h2, heq]
      · intro k hk
        refine ⟨ringPos b true k, ?_, ?_⟩
        · simp only [Sodd, S, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · rw [ringVert_ringPos, ringVert_step_odd]
            exact Ne.symm (Finset.mem_filter.mp hk).2
          · simp only [ringPos, Bool.true_eq_false, ↓reduceIte]
            split_ifs <;> omega
        · simp [ringVert_ringPos]
    change S.card = _
    rw [hsplit, hred_eq, hblue_eq]
  have hsplit_I : ∀ P : Bool × Fin (b + 1) → Prop, [DecidablePred P] →
      (Finset.univ.filter P).card =
        (Finset.univ.filter (fun k : Fin (b + 1) => P (false, k))).card +
        (Finset.univ.filter (fun k : Fin (b + 1) => P (true, k))).card := by
    intro P _
    have hdisj : Disjoint
        ((Finset.univ.filter (fun k : Fin (b + 1) => P (false, k))).image (fun k => (false, k)))
        ((Finset.univ.filter (fun k : Fin (b + 1) => P (true, k))).image (fun k => (true, k))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨k1, _, rfl⟩
      rcases Finset.mem_image.mp hx2 with ⟨k2, _, heq⟩
      exact Bool.false_ne_true.symm (congrArg Prod.fst heq)
    have hunion : Finset.univ.filter P =
        (Finset.univ.filter (fun k : Fin (b + 1) => P (false, k))).image (fun k => (false, k)) ∪
        (Finset.univ.filter (fun k : Fin (b + 1) => P (true, k))).image (fun k => (true, k)) := by
      ext ⟨r, k⟩
      cases r <;> simp
    rw [hunion, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
        Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  rw [hsingle false, hsingle true,
      hsplit_I (fun i => y (false, i) ≠ y (true, i)),
      hsplit_I (fun i => y (false, i) ≠ y (true, (i.1, i.2 + 1)))]
  ring

private lemma ring_mass_sum (b : ℕ) (y : Bool × (Bool × Fin (b + 1)) → Bool) :
    (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card =
      (Finset.univ.filter (fun p : Fin (2 * (b + 1)) => y (ringVert b false p) = true)).card +
      (Finset.univ.filter (fun p : Fin (2 * (b + 1)) => y (ringVert b true p) = true)).card := by
  let S0 := (Finset.univ.filter (fun p : Fin (2 * (b + 1)) => y (ringVert b false p) = true)).image
    (ringVert b false)
  let S1 := (Finset.univ.filter (fun p : Fin (2 * (b + 1)) => y (ringVert b true p) = true)).image
    (ringVert b true)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro u hu0 hu1
    rcases Finset.mem_image.mp hu0 with ⟨p0, _, rfl⟩
    rcases Finset.mem_image.mp hu1 with ⟨p1, _, heq⟩
    have h0 := ringVert_ring b false p0
    have h1 := ringVert_ring b true p1
    rw [heq] at h1
    rw [h0] at h1
    exact Bool.false_ne_true h1
  have hunion : Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true) = S0 ∪ S1 := by
    ext ⟨s, ⟨r, k⟩⟩
    simp only [S0, S1, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hy
      cases r
      · left; exact ⟨ringPos b s k, by rw [ringVert_ringPos]; exact hy, ringVert_ringPos b false s k⟩
      · right; exact ⟨ringPos b s k, by rw [ringVert_ringPos]; exact hy, ringVert_ringPos b true s k⟩
    · rintro (⟨p, hp, hpeq⟩ | ⟨p, hp, hpeq⟩) <;> rw [← hpeq] <;> exact hp
  rw [hunion, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (ringVert_inj b false),
      Finset.card_image_of_injective _ (ringVert_inj b true)]

private lemma ring_recover (b : ℕ) (r : Bool) (y1 y2 : Bool × (Bool × Fin (b + 1)) → Bool)
    (h0 : y1 (ringVert b r ⟨0, by omega⟩) = y2 (ringVert b r ⟨0, by omega⟩))
    (hedge : ∀ p : Fin (2 * (b + 1)),
      (y1 (ringVert b r p) ≠ y1 (ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1))) ↔
      (y2 (ringVert b r p) ≠ y2 (ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1)))) :
    ∀ p : Fin (2 * (b + 1)), y1 (ringVert b r p) = y2 (ringVert b r p) := by
  have hind : ∀ i (hi : i < 2 * (b + 1)),
      y1 (ringVert b r ⟨i, hi⟩) = y2 (ringVert b r ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      have hk' : k < 2 * (b + 1) := by omega
      have hprev := ih hk'
      have hst : cycStep (2 * (b + 1)) (by omega) ⟨k, hk'⟩ 1 = ⟨k + 1, hk⟩ := by
        ext; simp [cycStep, Nat.mod_eq_of_lt hk]
      have he := hedge ⟨k, hk'⟩
      rw [hst, hprev] at he
      cases a : y1 (ringVert b r ⟨k + 1, hk⟩) <;>
        cases c : y2 (ringVert b r ⟨k + 1, hk⟩) <;>
        cases d : y2 (ringVert b r ⟨k, hk'⟩) <;>
        simp [a, c, d] at he ⊢
  intro p
  exact hind p.val p.isLt

private lemma ring_zero_bdry_const (b : ℕ) (r : Bool) (y : Bool × (Bool × Fin (b + 1)) → Bool)
    (hzero : ringB b r y = 0) :
    ∀ p : Fin (2 * (b + 1)), y (ringVert b r p) = y (ringVert b r ⟨0, by omega⟩) := by
  have hall : ∀ p : Fin (2 * (b + 1)),
      y (ringVert b r p) = y (ringVert b r (cycStep (2 * (b + 1)) (by omega) p 1)) := by
    intro p
    by_contra hne
    have hmem : p ∈ Finset.univ.filter (fun q : Fin (2 * (b + 1)) =>
        y (ringVert b r q) ≠ y (ringVert b r (cycStep (2 * (b + 1)) (by omega) q 1))) := by
      simp [hne]
    have hpos := Finset.card_pos.mpr ⟨p, hmem⟩
    exact absurd hpos (by unfold ringB at hzero; omega)
  let yconst : Bool × (Bool × Fin (b + 1)) → Bool := fun _ => y (ringVert b r ⟨0, by omega⟩)
  exact ring_recover b r y yconst rfl (fun p => by simp [yconst, hall p])

private lemma cycDist_ringPos_ge (b L : ℕ) (hL : 1 ≤ L) (hLN : 2 * L ≤ b + 1)
    (s1 s2 : Bool) (k1 k2 : Fin (b + 1))
    (hd1 : L ≤ cycDist (b + 1) k1 k2) (hd2 : L ≤ cycDist (b + 1) k2 k1) :
    L ≤ cycDist (2 * (b + 1)) (ringPos b s1 k1) (ringPos b s2 k2) := by
  let N := b + 1
  let M := 2 * N
  have hk1 : k1.val < N := k1.isLt
  have hk2 : k2.val < N := k2.isLt
  have hd1' : L ≤ (k2.val + N - k1.val) % N := hd1
  have hd2' : L ≤ (k1.val + N - k2.val) % N := hd2
  have hcase : (k1.val ≤ k2.val ∧ L ≤ k2.val - k1.val ∧ k2.val - k1.val ≤ N - L) ∨
      (k2.val < k1.val ∧ L ≤ k1.val - k2.val ∧ k1.val - k2.val ≤ N - L) := by
    by_cases hle : k1.val ≤ k2.val
    · left
      have hm1 : (k2.val + N - k1.val) % N = k2.val - k1.val := by
        have h1 : k2.val + N - k1.val = (k2.val - k1.val) + N := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hm2 : (k1.val + N - k2.val) % N = if k1.val = k2.val then 0 else N - (k2.val - k1.val) := by
        split_ifs with heq
        · have : k1.val + N - k2.val = N := by omega
          rw [this, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      rw [hm1] at hd1'
      rw [hm2] at hd2'
      split_ifs at hd2' with heq
      · omega
      · omega
    · right
      have hm1 : (k2.val + N - k1.val) % N = N - (k1.val - k2.val) := by
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      have hm2 : (k1.val + N - k2.val) % N = k1.val - k2.val := by
        have h1 : k1.val + N - k2.val = (k1.val - k2.val) + N := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hm1] at hd1'
      rw [hm2] at hd2'
      omega
  unfold cycDist
  have hpos_val : ∀ s k, (ringPos b s k).val =
      if s = false then 2 * k.val else if k.val = 0 then M - 1 else 2 * k.val - 1 := by
    intro s k; unfold ringPos; split_ifs <;> rfl
  rw [hpos_val s1 k1, hpos_val s2 k2]
  rcases hcase with ⟨hle, hlo, hhi⟩ | ⟨hlt, hlo, hhi⟩
  · cases s1 <;> cases s2 <;> simp only [↓reduceIte, Bool.true_eq_false]
    · have h1 : 2 * k2.val + M - 2 * k1.val = 2 * (k2.val - k1.val) + M := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · split_ifs with hk20
      · omega
      · have h1 : 2 * k2.val - 1 + M - 2 * k1.val = (2 * (k2.val - k1.val) - 1) + M := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · split_ifs with hk10
      · have h1 : 2 * k2.val + M - (M - 1) = 2 * k2.val + 1 := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]; omega
      · have h1 : 2 * k2.val + M - (2 * k1.val - 1) = (2 * (k2.val - k1.val) + 1) + M := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · split_ifs with hk20 hk10
      · omega
      · omega
      · have h1 : 2 * k2.val - 1 + M - (M - 1) = 2 * k2.val := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]; omega
      · have h1 : 2 * k2.val - 1 + M - (2 * k1.val - 1) = 2 * (k2.val - k1.val) + M := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  · cases s1 <;> cases s2 <;> simp only [↓reduceIte, Bool.true_eq_false]
    · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · split_ifs with hk20
      · have h1 : M - 1 + M - 2 * k1.val = (M - 1 - 2 * k1.val) + M := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · split_ifs with hk10
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · split_ifs with hk20 hk10
      · omega
      · have h1 : M - 1 + M - (2 * k1.val - 1) = (M - 2 * k1.val) + M := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
      · omega
      · rw [Nat.mod_eq_of_lt (by omega)]; omega

end RingGeometry

section ExpanderExistence

private lemma card_equiv_of_card_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (h : Fintype.card α = Fintype.card β) :
    Fintype.card (α ≃ β) = (Fintype.card α).factorial := by
  let e : α ≃ β := Fintype.equivOfCardEq h
  have h1 : Fintype.card (α ≃ β) = Fintype.card (α ≃ α) :=
    Fintype.card_congr (Equiv.equivCongr (Equiv.refl α) e.symm)
  rw [h1, Fintype.card_perm]

private lemma card_perm_image_eq (N : ℕ) (S T : Finset (Fin N)) (hST : S.card = T.card) :
    ((Finset.univ : Finset (Equiv.Perm (Fin N))).filter
      (fun σ : Equiv.Perm (Fin N) => S.image (fun x => σ x) = T)).card ≤
      S.card.factorial * (N - S.card).factorial := by
  classical
  let Sc := Sᶜ
  let Tc := Tᶜ
  have hSc : Fintype.card { x : Fin N // x ∈ Sc } = N - S.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hTc : Fintype.card { x : Fin N // x ∈ Tc } = N - T.card := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hS_coe : Fintype.card { x : Fin N // x ∈ S } = S.card := Fintype.card_coe S
  have hT_coe : Fintype.card { x : Fin N // x ∈ T } = T.card := Fintype.card_coe T
  let F := (Finset.univ : Finset (Equiv.Perm (Fin N))).filter
    (fun σ : Equiv.Perm (Fin N) => S.image (fun x => σ x) = T)
  have hmem_T : ∀ σ ∈ F, ∀ x : { x : Fin N // x ∈ S }, σ x.1 ∈ T := by
    intro σ hσ x
    have hEq := (Finset.mem_filter.mp hσ).2
    rw [← hEq]
    exact Finset.mem_image_of_mem (fun x => σ x) x.2
  have hmem_S : ∀ σ ∈ F, ∀ y : { y : Fin N // y ∈ T }, σ.symm y.1 ∈ S := by
    intro σ hσ y
    have hEq := (Finset.mem_filter.mp hσ).2
    have hy : y.1 ∈ S.image (fun x => σ x) := hEq ▸ y.2
    rcases Finset.mem_image.mp hy with ⟨x, hx, hxy⟩
    have : σ.symm y.1 = x := by rw [← hxy]; exact σ.symm_apply_apply x
    rw [this]; exact hx
  have hmem_Tc : ∀ σ ∈ F, ∀ x : { x : Fin N // x ∈ Sc }, σ x.1 ∈ Tc := by
    intro σ hσ x
    simp only [Tc, Finset.mem_compl]
    intro hT
    have hxS : σ.symm (σ x.1) ∈ S := hmem_S σ hσ ⟨σ x.1, hT⟩
    rw [σ.symm_apply_apply] at hxS
    exact Finset.mem_compl.mp x.2 hxS
  have hmem_Sc : ∀ σ ∈ F, ∀ y : { y : Fin N // y ∈ Tc }, σ.symm y.1 ∈ Sc := by
    intro σ hσ y
    simp only [Sc, Finset.mem_compl]
    intro hS
    have hyT : σ (σ.symm y.1) ∈ T := hmem_T σ hσ ⟨σ.symm y.1, hS⟩
    rw [σ.apply_symm_apply] at hyT
    exact Finset.mem_compl.mp y.2 hyT
  let restrictF : Equiv.Perm (Fin N) →
      Option (({ x : Fin N // x ∈ S } ≃ { y : Fin N // y ∈ T }) ×
        ({ x : Fin N // x ∈ Sc } ≃ { y : Fin N // y ∈ Tc })) := fun σ =>
    if h : σ ∈ F then
      some (
        { toFun := fun x => ⟨σ x.1, hmem_T σ h x⟩
          invFun := fun y => ⟨σ.symm y.1, hmem_S σ h y⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
          right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) },
        { toFun := fun x => ⟨σ x.1, hmem_Tc σ h x⟩
          invFun := fun y => ⟨σ.symm y.1, hmem_Sc σ h y⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply x.1)
          right_inv := fun y => Subtype.ext (σ.apply_symm_apply y.1) }
      )
    else none
  let tgt := Finset.univ.image (some : ({ x : Fin N // x ∈ S } ≃ { y : Fin N // y ∈ T }) ×
    ({ x : Fin N // x ∈ Sc } ≃ { y : Fin N // y ∈ Tc }) → Option _)
  have hle : F.card ≤ tgt.card := by
    refine Finset.card_le_card_of_injOn restrictF ?_ ?_
    · intro σ hσ
      simp only [Finset.mem_coe] at hσ
      simp only [tgt, restrictF, dif_pos hσ, Finset.mem_coe, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact ⟨_, rfl⟩
    · intro σ1 h1 σ2 h2 heq
      simp only [Finset.mem_coe] at h1 h2
      simp only [restrictF, dif_pos h1, dif_pos h2, Option.some.injEq, Prod.mk.injEq] at heq
      ext x
      by_cases hx : x ∈ S
      · have hval : σ1 x = σ2 x := by
          have := congrArg (fun e => (e ⟨x, hx⟩).1) heq.1
          simpa using this
        exact congrArg Fin.val hval
      · have hx' : x ∈ Sc := Finset.mem_compl.mpr hx
        have hval : σ1 x = σ2 x := by
          have := congrArg (fun e => (e ⟨x, hx'⟩).1) heq.2
          simpa using this
        exact congrArg Fin.val hval
  have htgt_card : tgt.card = S.card.factorial * (N - S.card).factorial := by
    rw [Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_univ,
        Fintype.card_prod,
        card_equiv_of_card_eq (by rw [hS_coe, hT_coe, hST]),
        card_equiv_of_card_eq (by rw [hSc, hTc, hST]),
        hS_coe, hSc]
  exact hle.trans_eq htgt_card

private def crossFull (b : ℕ) (σ0 σ1 : Equiv.Perm (Fin (b + 1)))
    (y : Bool × (Bool × Fin (b + 1)) → Bool) : ℕ :=
  (Finset.univ.filter (fun k : Fin (b + 1) =>
    y (false, (false, k)) ≠ y (true, (true, σ0 k)))).card +
  (Finset.univ.filter (fun k : Fin (b + 1) =>
    y (false, (true, k)) ≠ y (true, (false, σ1 k)))).card

private lemma rail_diff_le (b : ℕ) (P Q : Fin (b + 1) → Bool) (σ : Equiv.Perm (Fin (b + 1))) :
    (Finset.univ.filter (fun k => P k = true)).card ≤
      (Finset.univ.filter (fun k => Q k = true)).card +
      (Finset.univ.filter (fun k => P k ≠ Q (σ k))).card ∧
    (Finset.univ.filter (fun k => Q k = true)).card ≤
      (Finset.univ.filter (fun k => P k = true)).card +
      (Finset.univ.filter (fun k => P k ≠ Q (σ k))).card := by
  have hQeq : (Finset.univ.filter (fun k => Q k = true)).card =
      (Finset.univ.filter (fun k => Q (σ k) = true)).card := by
    refine Finset.card_bij (fun k _ => σ.symm k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      simpa using hk
    · intro a _ b _ h; exact σ.symm.injective h
    · intro k hk
      refine ⟨σ k, ?_, σ.symm_apply_apply k⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk
  rw [hQeq]
  constructor
  · have hsub : Finset.univ.filter (fun k => P k = true) ⊆
        Finset.univ.filter (fun k => Q (σ k) = true) ∪
        Finset.univ.filter (fun k => P k ≠ Q (σ k)) := by
      intro k hk
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      cases hq : Q (σ k)
      · right; rw [hk]; exact Bool.false_ne_true.symm
      · left; rfl
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  · have hsub : Finset.univ.filter (fun k => Q (σ k) = true) ⊆
        Finset.univ.filter (fun k => P k = true) ∪
        Finset.univ.filter (fun k => P k ≠ Q (σ k)) := by
      intro k hk
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      cases hp : P k
      · right; rw [hk]; exact Bool.false_ne_true
      · left; rfl
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

private lemma connected_bdry_pos (b : ℕ) (σ0 σ1 : Equiv.Perm (Fin (b + 1)))
    (y : Bool × (Bool × Fin (b + 1)) → Bool)
    (hm1 : 0 < (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card)
    (hm2 : (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card ≤
      2 * (b + 1)) :
    0 < ringB b false y + ringB b true y + crossFull b σ0 σ1 y := by
  by_contra h0
  have hR0 : ringB b false y = 0 := by omega
  have hR1 : ringB b true y = 0 := by omega
  have hX : crossFull b σ0 σ1 y = 0 := by omega
  have hc0 := ring_zero_bdry_const b false y hR0
  have hc1 := ring_zero_bdry_const b true y hR1
  have hX0 : (Finset.univ.filter (fun k : Fin (b + 1) =>
      y (false, (false, k)) ≠ y (true, (true, σ0 k)))).card = 0 := by
    unfold crossFull at hX; omega
  have hlink : y (false, (false, ⟨0, by omega⟩)) = y (true, (true, σ0 ⟨0, by omega⟩)) := by
    by_contra hne
    have hmem : (⟨0, by omega⟩ : Fin (b + 1)) ∈ Finset.univ.filter (fun k : Fin (b + 1) =>
        y (false, (false, k)) ≠ y (true, (true, σ0 k))) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hne
    have hpos := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hsame : y (ringVert b false ⟨0, by omega⟩) = y (ringVert b true ⟨0, by omega⟩) := by
    have ha : ringVert b false ⟨0, by omega⟩ = (false, (false, ⟨0, by omega⟩)) := by
      unfold ringVert; simp
    have hb := hc1 (ringPos b true (σ0 ⟨0, by omega⟩))
    rw [ringVert_ringPos] at hb
    rw [ha, hlink, hb]
  set c := y (ringVert b false ⟨0, by omega⟩)
  have hall : ∀ u : Bool × (Bool × Fin (b + 1)), y u = c := by
    rintro ⟨s, ⟨r, k⟩⟩
    cases r
    · have := hc0 (ringPos b s k); rw [ringVert_ringPos] at this; exact this
    · have := hc1 (ringPos b s k); rw [ringVert_ringPos] at this; exact this.trans hsame.symm
  cases hc : c
  · have hzero : (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _
      rw [hall u, hc]
      exact Bool.false_ne_true
    omega
  · have hfull : (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card =
        4 * (b + 1) := by
      have heq : Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true) =
          Finset.univ := by
        ext u; simp [hall u, hc]
      rw [heq, Finset.card_univ, Fintype.card_prod, Fintype.card_prod, Fintype.card_bool,
          Fintype.card_fin]
      ring
    omega

private lemma exists_expander_perms (b : ℕ) :
    ∃ σ0 σ1 : Equiv.Perm (Fin (b + 1)),
      ∀ y : Bool × (Bool × Fin (b + 1)) → Bool,
        let mass := (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card
        2 * mass ≤ 4 * (b + 1) →
        mass ≤ 100 * (ringB b false y + ringB b true y + crossFull b σ0 σ1 y) := by
  let N := b + 1
  have hN : 0 < N := by omega
  let P := Equiv.Perm (Fin N)
  let Y := Bool × (Bool × Fin N) → Bool
  let massOf : Y → ℕ := fun y =>
    (Finset.univ.filter (fun u : Bool × (Bool × Fin N) => y u = true)).card
  let A0 : Y → Finset (Fin N) := fun y => Finset.univ.filter (fun k => y (false, (false, k)) = true)
  let B0 : Y → Finset (Fin N) := fun y => Finset.univ.filter (fun k => y (true, (false, k)) = true)
  let A1 : Y → Finset (Fin N) := fun y => Finset.univ.filter (fun k => y (false, (true, k)) = true)
  let B1 : Y → Finset (Fin N) := fun y => Finset.univ.filter (fun k => y (true, (true, k)) = true)
  have hmass_four : ∀ y : Y,
      massOf y = (A0 y).card + (B0 y).card + (A1 y).card + (B1 y).card := by
    intro y
    have hsplit : ∀ s r : Bool,
        (Finset.univ.filter (fun u : Bool × (Bool × Fin N) =>
          u.1 = s ∧ u.2.1 = r ∧ y u = true)).card =
        (Finset.univ.filter (fun k : Fin N => y (s, (r, k)) = true)).card := by
      intro s r
      refine Finset.card_bij (fun u _ => u.2.2) ?_ ?_ ?_
      · intro ⟨s', ⟨r', k⟩⟩ hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        rcases hu with ⟨rfl, rfl, hy⟩; exact hy
      · intro ⟨s1, ⟨r1, k1⟩⟩ h1 ⟨s2, ⟨r2, k2⟩⟩ h2 hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        rcases h1 with ⟨rfl, rfl, _⟩; rcases h2 with ⟨rfl, rfl, _⟩
        dsimp only at hk; rw [hk]
      · intro k hk
        refine ⟨(s, (r, k)), ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        exact hk
    let S := fun s r => Finset.univ.filter (fun u : Bool × (Bool × Fin N) =>
      u.1 = s ∧ u.2.1 = r ∧ y u = true)
    have hdisj01 : Disjoint (S false false) (S true false) := by
      rw [Finset.disjoint_left]; intro u h1 h2
      have a := (Finset.mem_filter.mp h1).2.1
      have c := (Finset.mem_filter.mp h2).2.1
      rw [a] at c; exact Bool.false_ne_true c
    have hdisj23 : Disjoint (S false true) (S true true) := by
      rw [Finset.disjoint_left]; intro u h1 h2
      have a := (Finset.mem_filter.mp h1).2.1
      have c := (Finset.mem_filter.mp h2).2.1
      rw [a] at c; exact Bool.false_ne_true c
    have hdisj_lr : Disjoint (S false false ∪ S true false) (S false true ∪ S true true) := by
      rw [Finset.disjoint_left]; intro u h1 h2
      have r1 : u.2.1 = false := by
        rcases Finset.mem_union.mp h1 with h | h <;> exact (Finset.mem_filter.mp h).2.2.1
      have r2 : u.2.1 = true := by
        rcases Finset.mem_union.mp h2 with h | h <;> exact (Finset.mem_filter.mp h).2.2.1
      rw [r1] at r2; exact Bool.false_ne_true r2
    have hunion : Finset.univ.filter (fun u : Bool × (Bool × Fin N) => y u = true) =
        (S false false ∪ S true false) ∪ (S false true ∪ S true true) := by
      ext ⟨s, ⟨r, k⟩⟩
      cases s <;> cases r <;> simp [S]
    change (Finset.univ.filter (fun u : Bool × (Bool × Fin N) => y u = true)).card = _
    rw [hunion, Finset.card_union_of_disjoint hdisj_lr,
        Finset.card_union_of_disjoint hdisj01, Finset.card_union_of_disjoint hdisj23,
        hsplit false false, hsplit true false, hsplit false true, hsplit true true]
    simp only [A0, B0, A1, B1]
    ring
  let BadFor : ℕ → Finset (Y × P × P) := fun m =>
    Finset.univ.filter (fun x =>
      massOf x.1 = m ∧ 100 * (ringB b false x.1 + ringB b true x.1 + crossFull b x.2.1 x.2.2 x.1) < m)
  have hBadFor_bound : ∀ m ∈ Finset.Icc 101 (2 * N),
      (BadFor m).card * (2 * N) ≤ N.factorial * N.factorial := by
    intro m hm
    have hm101 : 101 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm2N : m ≤ 2 * N := (Finset.mem_Icc.mp hm).2
    set t := (m - 1) / 100
    have ht1 : 1 ≤ t := by omega
    have ht_lo : 100 * t < m := by omega
    have ht_hi : m ≤ 100 * (t + 1) := by omega
    have ht_half : 2 * t ≤ 6 * N := by omega
    let Eset : Y × P × P → Finset (Fin (6 * N)) := fun x =>
      let y := x.1
      let σ0 := x.2.1
      let σ1 := x.2.2
      ((Finset.univ.filter (fun p : Fin (2 * N) =>
          y (ringVert b false p) ≠ y (ringVert b false (cycStep (2 * N) (by omega) p 1)))).image
          (fun p => ⟨p.val, by omega⟩)) ∪
      ((Finset.univ.filter (fun p : Fin (2 * N) =>
          y (ringVert b true p) ≠ y (ringVert b true (cycStep (2 * N) (by omega) p 1)))).image
          (fun p => ⟨2 * N + p.val, by omega⟩)) ∪
      ((Finset.univ.filter (fun k : Fin N =>
          y (false, (false, σ0.symm k)) ≠ y (true, (true, k)))).image
          (fun k => ⟨4 * N + k.val, by omega⟩)) ∪
      ((Finset.univ.filter (fun k : Fin N =>
          y (false, (true, σ1.symm k)) ≠ y (true, (false, k)))).image
          (fun k => ⟨5 * N + k.val, by omega⟩))
    have hEset_card : ∀ x : Y × P × P,
        (Eset x).card = ringB b false x.1 + ringB b true x.1 + crossFull b x.2.1 x.2.2 x.1 := by
      intro ⟨y, σ0, σ1⟩
      let S1 := (Finset.univ.filter (fun p : Fin (2 * N) =>
        y (ringVert b false p) ≠ y (ringVert b false (cycStep (2 * N) (by omega) p 1)))).image
        (fun p => (⟨p.val, by omega⟩ : Fin (6 * N)))
      let S2 := (Finset.univ.filter (fun p : Fin (2 * N) =>
        y (ringVert b true p) ≠ y (ringVert b true (cycStep (2 * N) (by omega) p 1)))).image
        (fun p => (⟨2 * N + p.val, by omega⟩ : Fin (6 * N)))
      let S3 := (Finset.univ.filter (fun k : Fin N =>
        y (false, (false, σ0.symm k)) ≠ y (true, (true, k)))).image
        (fun k => (⟨4 * N + k.val, by omega⟩ : Fin (6 * N)))
      let S4 := (Finset.univ.filter (fun k : Fin N =>
        y (false, (true, σ1.symm k)) ≠ y (true, (false, k)))).image
        (fun k => (⟨5 * N + k.val, by omega⟩ : Fin (6 * N)))
      have hd12 : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]; intro z h1 h2
        rcases Finset.mem_image.mp h1 with ⟨p1, _, rfl⟩
        rcases Finset.mem_image.mp h2 with ⟨p2, _, heq⟩
        have := congrArg Fin.val heq; simp only at this; omega
      have hd123 : Disjoint (S1 ∪ S2) S3 := by
        rw [Finset.disjoint_left]; intro z h1 h2
        rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
        rcases Finset.mem_union.mp h1 with h | h
        · rcases Finset.mem_image.mp h with ⟨p, _, heq⟩
          have := congrArg Fin.val heq; simp only at this; omega
        · rcases Finset.mem_image.mp h with ⟨p, _, heq⟩
          have := congrArg Fin.val heq; simp only at this; omega
      have hd1234 : Disjoint (S1 ∪ S2 ∪ S3) S4 := by
        rw [Finset.disjoint_left]; intro z h1 h2
        rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
        rcases Finset.mem_union.mp h1 with h12 | h3
        · rcases Finset.mem_union.mp h12 with h | h
          · rcases Finset.mem_image.mp h with ⟨p, _, heq⟩
            have := congrArg Fin.val heq; simp only at this; omega
          · rcases Finset.mem_image.mp h with ⟨p, _, heq⟩
            have := congrArg Fin.val heq; simp only at this; omega
        · rcases Finset.mem_image.mp h3 with ⟨p, _, heq⟩
          have := congrArg Fin.val heq; simp only at this; omega
      have hS1 : S1.card = ringB b false y := by
        rw [Finset.card_image_of_injective]
        · rfl
        · intro a c h; exact Fin.ext (by simpa using congrArg Fin.val h)
      have hS2 : S2.card = ringB b true y := by
        rw [Finset.card_image_of_injective]
        · rfl
        · intro a c h; ext; have := congrArg Fin.val h; simp only at this; omega
      have hS3 : S3.card = (Finset.univ.filter (fun k : Fin N =>
          y (false, (false, k)) ≠ y (true, (true, σ0 k)))).card := by
        rw [Finset.card_image_of_injective]
        · refine Finset.card_bij (fun k _ => σ0.symm k) ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            simpa [σ0.apply_symm_apply] using hk
          · intro a _ c _ h; exact σ0.symm.injective h
          · intro k hk
            refine ⟨σ0 k, ?_, σ0.symm_apply_apply k⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            simpa [σ0.symm_apply_apply] using hk
        · intro a c h; ext; have := congrArg Fin.val h; simp only at this; omega
      have hS4 : S4.card = (Finset.univ.filter (fun k : Fin N =>
          y (false, (true, k)) ≠ y (true, (false, σ1 k)))).card := by
        rw [Finset.card_image_of_injective]
        · refine Finset.card_bij (fun k _ => σ1.symm k) ?_ ?_ ?_
          · intro k hk
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            simpa [σ1.apply_symm_apply] using hk
          · intro a _ c _ h; exact σ1.symm.injective h
          · intro k hk
            refine ⟨σ1 k, ?_, σ1.symm_apply_apply k⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
            simpa [σ1.symm_apply_apply] using hk
        · intro a c h; ext; have := congrArg Fin.val h; simp only at this; omega
      change (S1 ∪ S2 ∪ S3 ∪ S4).card = _
      rw [Finset.card_union_of_disjoint hd1234, Finset.card_union_of_disjoint hd123,
          Finset.card_union_of_disjoint hd12, hS1, hS2, hS3, hS4]
      unfold crossFull
      ring
    let Enc : Y × P × P → (Bool × Bool) × Finset (Fin (6 * N)) := fun x =>
      ((x.1 (ringVert b false ⟨0, by omega⟩), x.1 (ringVert b true ⟨0, by omega⟩)), Eset x)
    let Keys : Finset ((Bool × Bool) × Finset (Fin (6 * N))) :=
      (Finset.univ : Finset (Bool × Bool)) ×ˢ
        ((Finset.range (t + 1)).biUnion (fun s => (Finset.univ : Finset (Fin (6 * N))).powersetCard s))
    have hEnc_mem : ∀ x ∈ BadFor m, Enc x ∈ Keys := by
      intro x hx
      have hbd := (Finset.mem_filter.mp hx).2.2
      have hle_t : (Eset x).card ≤ t := by rw [hEset_card x]; omega
      simp only [Keys, Enc, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_powersetCard]
      exact ⟨(Eset x).card, by omega, Finset.subset_univ _, rfl⟩
    have hKeys_card : Keys.card ≤ 4 * (t + 1) * (6 * N).choose t := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
      have hu : ((Finset.range (t + 1)).biUnion (fun s =>
          (Finset.univ : Finset (Fin (6 * N))).powersetCard s)).card ≤
          (t + 1) * (6 * N).choose t := by
        calc
          ((Finset.range (t + 1)).biUnion (fun s =>
              (Finset.univ : Finset (Fin (6 * N))).powersetCard s)).card
              ≤ ∑ s ∈ Finset.range (t + 1),
                  ((Finset.univ : Finset (Fin (6 * N))).powersetCard s).card :=
                Finset.card_biUnion_le
          _ = ∑ s ∈ Finset.range (t + 1), (6 * N).choose s := by
                refine Finset.sum_congr rfl fun s _ => ?_
                rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
          _ ≤ ∑ _s ∈ Finset.range (t + 1), (6 * N).choose t := by
                refine Finset.sum_le_sum fun s hs => ?_
                exact choose_le_of_le_half (6 * N) s t (by have := Finset.mem_range.mp hs; omega)
                  ht_half
          _ = (t + 1) * (6 * N).choose t := by simp
      calc
        2 * 2 * ((Finset.range (t + 1)).biUnion _).card
            ≤ 4 * ((t + 1) * (6 * N).choose t) := Nat.mul_le_mul_left 4 hu
        _ = 4 * (t + 1) * (6 * N).choose t := by ring
    have hEnc_eq_y : ∀ x1 x2 : Y × P × P, Enc x1 = Enc x2 →
        x1.1 = x2.1 ∧ (A0 x1.1).image x1.2.1 = (A0 x1.1).image x2.2.1 ∧
        (A1 x1.1).image x1.2.2 = (A1 x1.1).image x2.2.2 := by
      rintro ⟨y1, σ01, σ11⟩ ⟨y2, σ02, σ12⟩ heq
      simp only [Enc, Prod.mk.injEq] at heq
      rcases heq with ⟨⟨h0f, h0t⟩, hE⟩
      have hmemE : ∀ z : Fin (6 * N), z ∈ Eset (y1, σ01, σ11) ↔ z ∈ Eset (y2, σ02, σ12) := by
        intro z; rw [hE]
      have hE_r0 : ∀ p : Fin (2 * N),
          (y1 (ringVert b false p) ≠ y1 (ringVert b false (cycStep (2 * N) (by omega) p 1))) ↔
          (y2 (ringVert b false p) ≠ y2 (ringVert b false (cycStep (2 * N) (by omega) p 1))) := by
        intro p
        have h := hmemE ⟨p.val, by omega⟩
        have hside : ∀ (y : Y) (s0 s1 : P),
            (⟨p.val, by omega⟩ : Fin (6 * N)) ∈ Eset (y, s0, s1) ↔
              y (ringVert b false p) ≠ y (ringVert b false (cycStep (2 * N) (by omega) p 1)) := by
          intro y s0 s1
          simp only [Eset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro (((⟨q, hq, heq'⟩ | ⟨q, _, heq'⟩) | ⟨q, _, heq'⟩) | ⟨q, _, heq'⟩)
            · have : q = p := Fin.ext (by simpa using congrArg Fin.val heq')
              rwa [← this]
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have := congrArg Fin.val heq'; simp only at this; omega
          · intro hp'; exact Or.inl (Or.inl (Or.inl ⟨p, hp', rfl⟩))
        rwa [hside y1 σ01 σ11, hside y2 σ02 σ12] at h
      have hE_r1 : ∀ p : Fin (2 * N),
          (y1 (ringVert b true p) ≠ y1 (ringVert b true (cycStep (2 * N) (by omega) p 1))) ↔
          (y2 (ringVert b true p) ≠ y2 (ringVert b true (cycStep (2 * N) (by omega) p 1))) := by
        intro p
        have h := hmemE ⟨2 * N + p.val, by omega⟩
        have hside : ∀ (y : Y) (s0 s1 : P),
            (⟨2 * N + p.val, by omega⟩ : Fin (6 * N)) ∈ Eset (y, s0, s1) ↔
              y (ringVert b true p) ≠ y (ringVert b true (cycStep (2 * N) (by omega) p 1)) := by
          intro y s0 s1
          simp only [Eset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro (((⟨q, _, heq'⟩ | ⟨q, hq, heq'⟩) | ⟨q, _, heq'⟩) | ⟨q, _, heq'⟩)
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have : q = p := by ext; have := congrArg Fin.val heq'; simp only at this; omega
              rwa [← this]
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have := congrArg Fin.val heq'; simp only at this; omega
          · intro hp'; exact Or.inl (Or.inl (Or.inr ⟨p, hp', rfl⟩))
        rwa [hside y1 σ01 σ11, hside y2 σ02 σ12] at h
      have hy0 := ring_recover b false y1 y2 h0f hE_r0
      have hy1 := ring_recover b true y1 y2 h0t hE_r1
      have hy_eq : y1 = y2 := by
        funext ⟨s, ⟨r, k⟩⟩
        cases r
        · have := hy0 (ringPos b s k); simpa [ringVert_ringPos] using this
        · have := hy1 (ringPos b s k); simpa [ringVert_ringPos] using this
      subst hy_eq
      refine ⟨rfl, ?_, ?_⟩
      · ext k
        have h := hmemE ⟨4 * N + k.val, by omega⟩
        have hside : ∀ (s0 s1 : P),
            (⟨4 * N + k.val, by omega⟩ : Fin (6 * N)) ∈ Eset (y1, s0, s1) ↔
              y1 (false, (false, s0.symm k)) ≠ y1 (true, (true, k)) := by
          intro s0 s1
          simp only [Eset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro (((⟨q, _, heq'⟩ | ⟨q, _, heq'⟩) | ⟨q, hq, heq'⟩) | ⟨q, _, heq'⟩)
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have : q = k := by ext; have := congrArg Fin.val heq'; simp only at this; omega
              rwa [← this]
            · have := congrArg Fin.val heq'; simp only at this; omega
          · intro hk'; exact Or.inl (Or.inr ⟨k, hk', rfl⟩)
        rw [hside σ01 σ11, hside σ02 σ12] at h
        have hmem_im : ∀ s0 : P, k ∈ (A0 y1).image s0 ↔ y1 (false, (false, s0.symm k)) = true := by
          intro s0
          simp only [A0, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩; simpa [s0.symm_apply_apply] using hj
          · intro hj; exact ⟨s0.symm k, hj, s0.apply_symm_apply k⟩
        rw [hmem_im σ01, hmem_im σ02]
        cases a : y1 (false, (false, σ01.symm k)) <;>
          cases c : y1 (false, (false, σ02.symm k)) <;>
          cases d : y1 (true, (true, k)) <;>
          simp [a, c, d] at h ⊢
      · ext k
        have h := hmemE ⟨5 * N + k.val, by omega⟩
        have hside : ∀ (s0 s1 : P),
            (⟨5 * N + k.val, by omega⟩ : Fin (6 * N)) ∈ Eset (y1, s0, s1) ↔
              y1 (false, (true, s1.symm k)) ≠ y1 (true, (false, k)) := by
          intro s0 s1
          simp only [Eset, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
            true_and]
          constructor
          · rintro (((⟨q, _, heq'⟩ | ⟨q, _, heq'⟩) | ⟨q, _, heq'⟩) | ⟨q, hq, heq'⟩)
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have := congrArg Fin.val heq'; simp only at this; omega
            · have : q = k := by ext; have := congrArg Fin.val heq'; simp only at this; omega
              rwa [← this]
          · intro hk'; exact Or.inr ⟨k, hk', rfl⟩
        rw [hside σ01 σ11, hside σ02 σ12] at h
        have hmem_im : ∀ s1 : P, k ∈ (A1 y1).image s1 ↔ y1 (false, (true, s1.symm k)) = true := by
          intro s1
          simp only [A1, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, hj, rfl⟩; simpa [s1.symm_apply_apply] using hj
          · intro hj; exact ⟨s1.symm k, hj, s1.apply_symm_apply k⟩
        rw [hmem_im σ11, hmem_im σ12]
        cases a : y1 (false, (true, σ11.symm k)) <;>
          cases c : y1 (false, (true, σ12.symm k)) <;>
          cases d : y1 (true, (false, k)) <;>
          simp [a, c, d] at h ⊢
    have hfiber : ∀ key ∈ Keys,
        ((BadFor m).filter (fun x => Enc x = key)).card * (8 * N * (t + 1) * (6 * N).choose t) ≤
          N.factorial * N.factorial := by
      intro key _
      by_cases hne : ((BadFor m).filter (fun x => Enc x = key)).Nonempty
      · rcases hne with ⟨⟨y0, σ00, σ10⟩, hx0⟩
        have hx0_bad : (y0, σ00, σ10) ∈ BadFor m := (Finset.mem_filter.mp hx0).1
        have hx0_key : Enc (y0, σ00, σ10) = key := (Finset.mem_filter.mp hx0).2
        have hm0 : massOf y0 = m := (Finset.mem_filter.mp hx0_bad).2.1
        have hbd0 : ringB b false y0 + ringB b true y0 + crossFull b σ00 σ10 y0 ≤ t := by
          have hlt0 := (Finset.mem_filter.mp hx0_bad).2.2
          dsimp only at hlt0
          omega
        have hRB := ringB_eq_red_add_blue b y0
        have hred0_le : (Finset.univ.filter (fun k : Fin (b + 1) =>
            y0 (false, (false, k)) ≠ y0 (true, (false, k)))).card ≤ ringB b false y0 + ringB b true y0 := by
          have hsub : (Finset.univ.filter (fun k : Fin (b + 1) =>
              y0 (false, (false, k)) ≠ y0 (true, (false, k)))).image (fun k => (false, k)) ⊆
              Finset.univ.filter (fun i : Bool × Fin (b + 1) => y0 (false, i) ≠ y0 (true, i)) := by
            intro i hi
            rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
            simpa using hk
          have hle := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)] at hle
          omega
        have hred1_le : (Finset.univ.filter (fun k : Fin (b + 1) =>
            y0 (false, (true, k)) ≠ y0 (true, (true, k)))).card ≤ ringB b false y0 + ringB b true y0 := by
          have hsub : (Finset.univ.filter (fun k : Fin (b + 1) =>
              y0 (false, (true, k)) ≠ y0 (true, (true, k)))).image (fun k => (true, k)) ⊆
              Finset.univ.filter (fun i : Bool × Fin (b + 1) => y0 (false, i) ≠ y0 (true, i)) := by
            intro i hi
            rcases Finset.mem_image.mp hi with ⟨k, hk, rfl⟩
            simpa using hk
          have hle := Finset.card_le_card hsub
          rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)] at hle
          omega
        have hdiff_r0 := rail_diff_le b (fun k => y0 (false, (false, k)))
          (fun k => y0 (true, (false, k))) (Equiv.refl _)
        have hdiff_r1 := rail_diff_le b (fun k => y0 (false, (true, k)))
          (fun k => y0 (true, (true, k))) (Equiv.refl _)
        have hdiff_x0 := rail_diff_le b (fun k => y0 (false, (false, k)))
          (fun k => y0 (true, (true, k))) σ00
        have hdiff_x1 := rail_diff_le b (fun k => y0 (false, (true, k)))
          (fun k => y0 (true, (false, k))) σ10
        set a0 := (A0 y0).card
        set b0 := (B0 y0).card
        set a1 := (A1 y0).card
        set b1 := (B1 y0).card
        have hm4 : m = a0 + b0 + a1 + b1 := by rw [← hm0]; exact hmass_four y0
        have hX0_le : (Finset.univ.filter (fun k : Fin (b + 1) =>
            y0 (false, (false, k)) ≠ y0 (true, (true, σ00 k)))).card ≤ crossFull b σ00 σ10 y0 := by
          unfold crossFull; omega
        have hX1_le : (Finset.univ.filter (fun k : Fin (b + 1) =>
            y0 (false, (true, k)) ≠ y0 (true, (false, σ10 k)))).card ≤ crossFull b σ00 σ10 y0 := by
          unfold crossFull; omega
        have hbal : (24 * t ≤ a0 ∧ a0 ≤ 51 * t ∧ 5 * a0 ≤ 3 * N) ∧
            (24 * t ≤ a1 ∧ a1 ≤ 51 * t ∧ 5 * a1 ≤ 3 * N) := by
          have hr0a : a0 ≤ b0 + (ringB b false y0 + ringB b true y0) := by
            have h1 := hdiff_r0.1
            simp only [Equiv.refl_apply] at h1
            have h2 : a0 ≤ b0 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (false, k)) ≠ y0 (true, (false, k)))).card := h1
            omega
          have hr0b : b0 ≤ a0 + (ringB b false y0 + ringB b true y0) := by
            have h1 := hdiff_r0.2
            simp only [Equiv.refl_apply] at h1
            have h2 : b0 ≤ a0 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (false, k)) ≠ y0 (true, (false, k)))).card := h1
            omega
          have hr1a : a1 ≤ b1 + (ringB b false y0 + ringB b true y0) := by
            have h1 := hdiff_r1.1
            simp only [Equiv.refl_apply] at h1
            have h2 : a1 ≤ b1 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (true, k)) ≠ y0 (true, (true, k)))).card := h1
            omega
          have hr1b : b1 ≤ a1 + (ringB b false y0 + ringB b true y0) := by
            have h1 := hdiff_r1.2
            simp only [Equiv.refl_apply] at h1
            have h2 : b1 ≤ a1 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (true, k)) ≠ y0 (true, (true, k)))).card := h1
            omega
          have hx0a : a0 ≤ b1 + crossFull b σ00 σ10 y0 := by
            have h2 : a0 ≤ b1 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (false, k)) ≠ y0 (true, (true, σ00 k)))).card := hdiff_x0.1
            omega
          have hx0b : b1 ≤ a0 + crossFull b σ00 σ10 y0 := by
            have h2 : b1 ≤ a0 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (false, k)) ≠ y0 (true, (true, σ00 k)))).card := hdiff_x0.2
            omega
          have hx1a : a1 ≤ b0 + crossFull b σ00 σ10 y0 := by
            have h2 : a1 ≤ b0 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (true, k)) ≠ y0 (true, (false, σ10 k)))).card := hdiff_x1.1
            omega
          have hx1b : b0 ≤ a1 + crossFull b σ00 σ10 y0 := by
            have h2 : b0 ≤ a1 + (Finset.univ.filter (fun k : Fin (b + 1) =>
                y0 (false, (true, k)) ≠ y0 (true, (false, σ10 k)))).card := hdiff_x1.2
            omega
          refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega⟩⟩
        let T0 := (A0 y0).image (fun k => σ00 k)
        let T1 := (A1 y0).image (fun k => σ10 k)
        have hT0 : (A0 y0).card = T0.card := (Finset.card_image_of_injective _ σ00.injective).symm
        have hT1 : (A1 y0).card = T1.card := (Finset.card_image_of_injective _ σ10.injective).symm
        let F0 := (Finset.univ : Finset P).filter (fun σ : P => (A0 y0).image (fun k => σ k) = T0)
        let F1 := (Finset.univ : Finset P).filter (fun σ : P => (A1 y0).image (fun k => σ k) = T1)
        have hfib_le : ((BadFor m).filter (fun x => Enc x = key)).card ≤ F0.card * F1.card := by
          rw [← Finset.card_product]
          refine Finset.card_le_card_of_injOn (fun x => (x.2.1, x.2.2)) ?_ ?_
          · intro x hx
            have hEq := hEnc_eq_y (y0, σ00, σ10) x (hx0_key.trans (Finset.mem_filter.mp hx).2.symm)
            simp only [F0, F1, T0, T1, Finset.mem_coe, Finset.mem_product, Finset.mem_filter,
              Finset.mem_univ, true_and]
            exact ⟨hEq.2.1.symm, hEq.2.2.symm⟩
          · intro x1 hx1 x2 hx2 hpair
            have hEq1 := hEnc_eq_y (y0, σ00, σ10) x1 (hx0_key.trans (Finset.mem_filter.mp hx1).2.symm)
            have hEq2 := hEnc_eq_y (y0, σ00, σ10) x2 (hx0_key.trans (Finset.mem_filter.mp hx2).2.symm)
            rcases x1 with ⟨y1, s01, s11⟩
            rcases x2 with ⟨y2, s02, s12⟩
            have hs0 : s01 = s02 := congrArg Prod.fst hpair
            have hs1 : s11 = s12 := congrArg Prod.snd hpair
            have hy12 : y1 = y2 := hEq1.1.symm.trans hEq2.1
            exact Prod.ext hy12 (Prod.ext hs0 hs1)
        have hF0_le : F0.card ≤ a0.factorial * (N - a0).factorial :=
          card_perm_image_eq N (A0 y0) T0 hT0
        have hF1_le : F1.card ≤ a1.factorial * (N - a1).factorial :=
          card_perm_image_eq N (A1 y0) T1 hT1
        have hub := union_bound_ineq N t a0 a1 hN ht1
          hbal.1.1 hbal.1.2.1 hbal.1.2.2 hbal.2.1 hbal.2.2.1 hbal.2.2.2
        have hch0 : N.choose a0 * a0.factorial * (N - a0).factorial = N.factorial :=
          Nat.choose_mul_factorial_mul_factorial (by omega)
        have hch1 : N.choose a1 * a1.factorial * (N - a1).factorial = N.factorial :=
          Nat.choose_mul_factorial_mul_factorial (by omega)
        calc
          ((BadFor m).filter (fun x => Enc x = key)).card * (8 * N * (t + 1) * (6 * N).choose t)
              ≤ (a0.factorial * (N - a0).factorial * (a1.factorial * (N - a1).factorial)) *
                  (N.choose a0 * N.choose a1) :=
                Nat.mul_le_mul (le_trans hfib_le (Nat.mul_le_mul hF0_le hF1_le)) (le_of_lt hub)
          _ = (N.choose a0 * a0.factorial * (N - a0).factorial) *
                (N.choose a1 * a1.factorial * (N - a1).factorial) := by ring
          _ = N.factorial * N.factorial := by rw [hch0, hch1]
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
    have hsum_fib : (BadFor m).card =
        ∑ key ∈ Keys, ((BadFor m).filter (fun x => Enc x = key)).card :=
      Finset.card_eq_sum_card_fiberwise hEnc_mem
    have hmul_all : (BadFor m).card * (8 * N * (t + 1) * (6 * N).choose t) ≤
        Keys.card * (N.factorial * N.factorial) := by
      rw [hsum_fib, Finset.sum_mul]
      calc
        ∑ key ∈ Keys, ((BadFor m).filter (fun x => Enc x = key)).card *
            (8 * N * (t + 1) * (6 * N).choose t)
            ≤ ∑ _key ∈ Keys, (N.factorial * N.factorial) := Finset.sum_le_sum hfiber
        _ = Keys.card * (N.factorial * N.factorial) := by simp
    have hcomb : (4 * (t + 1) * (6 * N).choose t) * ((BadFor m).card * (2 * N)) ≤
        (4 * (t + 1) * (6 * N).choose t) * (N.factorial * N.factorial) := by
      calc
        (4 * (t + 1) * (6 * N).choose t) * ((BadFor m).card * (2 * N))
            = (BadFor m).card * (8 * N * (t + 1) * (6 * N).choose t) := by ring
        _ ≤ Keys.card * (N.factorial * N.factorial) := hmul_all
        _ ≤ (4 * (t + 1) * (6 * N).choose t) * (N.factorial * N.factorial) :=
              Nat.mul_le_mul_right _ hKeys_card
    have hpos_fac : 0 < 4 * (t + 1) * (6 * N).choose t :=
      Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    exact Nat.le_of_mul_le_mul_left hcomb hpos_fac
  let BadPerms : Finset (P × P) := Finset.univ.filter (fun p =>
    ∃ y : Y, massOf y ≤ 2 * N ∧
      100 * (ringB b false y + ringB b true y + crossFull b p.1 p.2 y) < massOf y)
  have hBadPerms_sub : BadPerms ⊆
      (Finset.Icc 101 (2 * N)).biUnion (fun m => (BadFor m).image (fun x => x.2)) := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨y, hmy, hbad⟩
    have hmpos : 0 < massOf y := by omega
    have hpos_bdry := connected_bdry_pos b p.1 p.2 y hmpos hmy
    have hm101 : 101 ≤ massOf y := by omega
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image]
    exact ⟨massOf y, ⟨hm101, hmy⟩, (y, p), by simp [BadFor, hbad], rfl⟩
  have hBadPerms_lt : BadPerms.card < N.factorial * N.factorial := by
    have hcard_sum : BadPerms.card ≤ ∑ m ∈ Finset.Icc 101 (2 * N), (BadFor m).card := by
      calc
        BadPerms.card ≤ ((Finset.Icc 101 (2 * N)).biUnion (fun m => (BadFor m).image Prod.snd)).card :=
          Finset.card_le_card hBadPerms_sub
        _ ≤ ∑ m ∈ Finset.Icc 101 (2 * N), ((BadFor m).image Prod.snd).card := Finset.card_biUnion_le
        _ ≤ ∑ m ∈ Finset.Icc 101 (2 * N), (BadFor m).card :=
          Finset.sum_le_sum fun _ _ => Finset.card_image_le
    have hmul : BadPerms.card * (2 * N) < (N.factorial * N.factorial) * (2 * N) := by
      have hIcc_lt : (Finset.Icc 101 (2 * N)).card < 2 * N := by
        rw [Nat.card_Icc]; omega
      calc
        BadPerms.card * (2 * N)
            ≤ (∑ m ∈ Finset.Icc 101 (2 * N), (BadFor m).card) * (2 * N) :=
              Nat.mul_le_mul_right _ hcard_sum
        _ = ∑ m ∈ Finset.Icc 101 (2 * N), (BadFor m).card * (2 * N) := Finset.sum_mul ..
        _ ≤ ∑ _m ∈ Finset.Icc 101 (2 * N), (N.factorial * N.factorial) :=
              Finset.sum_le_sum hBadFor_bound
        _ = (Finset.Icc 101 (2 * N)).card * (N.factorial * N.factorial) := by simp
        _ < (2 * N) * (N.factorial * N.factorial) :=
              Nat.mul_lt_mul_of_pos_right hIcc_lt
                (Nat.mul_pos (Nat.factorial_pos N) (Nat.factorial_pos N))
        _ = (N.factorial * N.factorial) * (2 * N) := by ring
    exact Nat.lt_of_mul_lt_mul_right hmul
  have huniv_card : (Finset.univ : Finset (P × P)).card = N.factorial * N.factorial := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  have hex : ∃ p ∈ (Finset.univ : Finset (P × P)), p ∉ BadPerms :=
    Finset.exists_mem_notMem_of_card_lt_card (by rw [huniv_card]; exact hBadPerms_lt)
  rcases hex with ⟨⟨σ0, σ1⟩, _, hnot⟩
  refine ⟨σ0, σ1, fun y hmass => ?_⟩
  by_contra hlt
  have hmem : (σ0, σ1) ∈ BadPerms := by
    have hm_eq : massOf y =
        (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card := rfl
    simp only [BadPerms, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨y, by omega, by omega⟩
  exact hnot hmem

end ExpanderExistence

section GreedyPick

private lemma card_ball_le (N L : ℕ) (hN : 0 < N) (c : Fin N) :
    (Finset.univ.filter (fun k : Fin N => cycDist N c k < L ∨ cycDist N k c < L)).card ≤ 2 * L := by
  let S1 := (Finset.range L).image (fun j => cycStep N hN c j)
  let S2 := (Finset.range L).image (fun j => (⟨(c.val + N - j % N) % N, Nat.mod_lt _ hN⟩ : Fin N))
  have hsub : Finset.univ.filter (fun k : Fin N => cycDist N c k < L ∨ cycDist N k c < L) ⊆
      S1 ∪ S2 := by
    intro k hk
    have hdisj := (Finset.mem_filter.mp hk).2
    rw [Finset.mem_union]
    rcases hdisj with h1 | h2
    · left
      simp only [S1, Finset.mem_image, Finset.mem_range]
      refine ⟨cycDist N c k, h1, ?_⟩
      ext
      simp only [cycStep, cycDist]
      have hc := c.isLt
      have hk' := k.isLt
      rw [Nat.add_mod_mod]
      have : c.val + (k.val + N - c.val) = k.val + N := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
    · right
      simp only [S2, Finset.mem_image, Finset.mem_range]
      refine ⟨cycDist N k c, h2, ?_⟩
      ext
      dsimp only
      have hc := c.isLt
      have hk' := k.isLt
      have hdlt : cycDist N k c < N := Nat.mod_lt _ hN
      rw [Nat.mod_eq_of_lt hdlt]
      by_cases hle : k.val ≤ c.val
      · have hd : cycDist N k c = c.val - k.val := by
          unfold cycDist
          have h1 : c.val + N - k.val = (c.val - k.val) + N := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hd]
        have h2 : c.val + N - (c.val - k.val) = k.val + N := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
      · have hd : cycDist N k c = N - (k.val - c.val) := by
          unfold cycDist
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        rw [hd]
        have h2 : c.val + N - (N - (k.val - c.val)) = k.val := by omega
        rw [h2, Nat.mod_eq_of_lt hk']
  calc
    (Finset.univ.filter (fun k : Fin N => cycDist N c k < L ∨ cycDist N k c < L)).card
        ≤ (S1 ∪ S2).card := Finset.card_le_card hsub
    _ ≤ S1.card + S2.card := Finset.card_union_le S1 S2
    _ ≤ L + L := by
      have h1 : S1.card ≤ L := le_trans Finset.card_image_le (by simp)
      have h2 : S2.card ≤ L := le_trans Finset.card_image_le (by simp)
      omega
    _ = 2 * L := by ring

private lemma exists_spaced_pick (b L d : ℕ) (hL : 1 ≤ L) (hN : 4 * L * d < b + 1)
    (σ0 σ1 : Equiv.Perm (Fin (b + 1))) (pol : Fin d → Bool) :
    ∃ f : Fin d → Fin (b + 1),
      let c0 : Fin d → Fin (b + 1) := fun j => if pol j = false then f j else σ1 (f j)
      let c1 : Fin d → Fin (b + 1) := fun j => if pol j = true then f j else σ0 (f j)
      ∀ j1 j2 : Fin d, j1 ≠ j2 →
        L ≤ cycDist (b + 1) (c0 j1) (c0 j2) ∧ L ≤ cycDist (b + 1) (c1 j1) (c1 j2) := by
  classical
  let N := b + 1
  have hNpos : 0 < N := by omega
  have hind : ∀ (n : ℕ) (hn : n ≤ d),
      ∃ f : Fin n → Fin N,
        ∀ j1 j2 : Fin n, j1 ≠ j2 →
          let p1 := pol ⟨j1.val, by omega⟩
          let p2 := pol ⟨j2.val, by omega⟩
          let c0 := fun (j : Fin n) => if pol ⟨j.val, by omega⟩ = false then f j else σ1 (f j)
          let c1 := fun (j : Fin n) => if pol ⟨j.val, by omega⟩ = true then f j else σ0 (f j)
          L ≤ cycDist N (c0 j1) (c0 j2) ∧ L ≤ cycDist N (c1 j1) (c1 j2) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ m ih =>
      intro hm
      rcases ih (by omega) with ⟨f, hf⟩
      let c0 : Fin m → Fin N := fun j => if pol ⟨j.val, by omega⟩ = false then f j else σ1 (f j)
      let c1 : Fin m → Fin N := fun j => if pol ⟨j.val, by omega⟩ = true then f j else σ0 (f j)
      let pnew := pol ⟨m, by omega⟩
      let map0 : Fin N → Fin N := fun k => if pnew = false then k else σ1 k
      let map1 : Fin N → Fin N := fun k => if pnew = true then k else σ0 k
      have hmap0_bij : Function.Bijective map0 := by
        unfold map0; split_ifs
        · exact Function.bijective_id
        · exact σ1.bijective
      have hmap1_bij : Function.Bijective map1 := by
        unfold map1; split_ifs
        · exact Function.bijective_id
        · exact σ0.bijective
      let bad : Fin m → Finset (Fin N) := fun j =>
        Finset.univ.filter (fun k : Fin N =>
          cycDist N (c0 j) (map0 k) < L ∨ cycDist N (map0 k) (c0 j) < L ∨
          cycDist N (c1 j) (map1 k) < L ∨ cycDist N (map1 k) (c1 j) < L)
      have hbad_le : ∀ j : Fin m, (bad j).card ≤ 4 * L := by
        intro j
        let B0 := Finset.univ.filter (fun k : Fin N =>
          cycDist N (c0 j) (map0 k) < L ∨ cycDist N (map0 k) (c0 j) < L)
        let B1 := Finset.univ.filter (fun k : Fin N =>
          cycDist N (c1 j) (map1 k) < L ∨ cycDist N (map1 k) (c1 j) < L)
        have hsub : bad j ⊆ B0 ∪ B1 := by
          intro k hk
          simp only [bad, B0, B1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
          tauto
        have hB0 : B0.card ≤ 2 * L := by
          have heq : B0.card = (Finset.univ.filter (fun k : Fin N =>
              cycDist N (c0 j) k < L ∨ cycDist N k (c0 j) < L)).card := by
            refine Finset.card_bij (fun k _ => map0 k) ?_ ?_ ?_
            · intro k hk; simpa [B0] using hk
            · intro a _ c _ h; exact hmap0_bij.1 h
            · intro y hy
              rcases hmap0_bij.2 y with ⟨k, rfl⟩
              exact ⟨k, by simpa [B0] using hy, rfl⟩
          rw [heq]; exact card_ball_le N L hNpos (c0 j)
        have hB1 : B1.card ≤ 2 * L := by
          have heq : B1.card = (Finset.univ.filter (fun k : Fin N =>
              cycDist N (c1 j) k < L ∨ cycDist N k (c1 j) < L)).card := by
            refine Finset.card_bij (fun k _ => map1 k) ?_ ?_ ?_
            · intro k hk; simpa [B1] using hk
            · intro a _ c _ h; exact hmap1_bij.1 h
            · intro y hy
              rcases hmap1_bij.2 y with ⟨k, rfl⟩
              exact ⟨k, by simpa [B1] using hy, rfl⟩
          rw [heq]; exact card_ball_le N L hNpos (c1 j)
        calc
          (bad j).card ≤ (B0 ∪ B1).card := Finset.card_le_card hsub
          _ ≤ B0.card + B1.card := Finset.card_union_le B0 B1
          _ ≤ 2 * L + 2 * L := Nat.add_le_add hB0 hB1
          _ = 4 * L := by ring
      let allBad := (Finset.univ : Finset (Fin m)).biUnion bad
      have hallBad_lt : allBad.card < (Finset.univ : Finset (Fin N)).card := by
        rw [Finset.card_univ, Fintype.card_fin]
        calc
          allBad.card ≤ ∑ j : Fin m, (bad j).card := Finset.card_biUnion_le
          _ ≤ ∑ _j : Fin m, (4 * L) := Finset.sum_le_sum fun j _ => hbad_le j
          _ = m * (4 * L) := by simp
          _ < N := by show m * (4 * L) < b + 1; nlinarith
      rcases Finset.exists_mem_notMem_of_card_lt_card hallBad_lt with ⟨knew, _, hknew⟩
      let f' : Fin (m + 1) → Fin N := fun j =>
        if h : j.val < m then f ⟨j.val, h⟩ else knew
      refine ⟨f', fun j1 j2 hne => ?_⟩
      by_cases h1 : j1.val < m <;> by_cases h2 : j2.val < m
      · have hne' : (⟨j1.val, h1⟩ : Fin m) ≠ ⟨j2.val, h2⟩ := by
          intro heq; apply hne; exact Fin.ext (by simpa using congrArg Fin.val heq)
        simpa [f', dif_pos h1, dif_pos h2] using hf ⟨j1.val, h1⟩ ⟨j2.val, h2⟩ hne'
      · have hj2 : j2.val = m := by omega
        have hnot : knew ∉ bad ⟨j1.val, h1⟩ := fun hmem =>
          hknew (Finset.mem_biUnion.mpr ⟨⟨j1.val, h1⟩, Finset.mem_univ _, hmem⟩)
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hnot
        have hpol2 : pol ⟨j2.val, by omega⟩ = pnew := by simp [pnew, hj2]
        have hf1 : f' j1 = f ⟨j1.val, h1⟩ := by simp [f', dif_pos h1]
        have hf2 : f' j2 = knew := by simp [f', dif_neg h2]
        dsimp only
        rw [hf1, hf2, hpol2]
        exact ⟨hnot.1, hnot.2.2.1⟩
      · have hj1 : j1.val = m := by omega
        have hnot : knew ∉ bad ⟨j2.val, h2⟩ := fun hmem =>
          hknew (Finset.mem_biUnion.mpr ⟨⟨j2.val, h2⟩, Finset.mem_univ _, hmem⟩)
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_lt] at hnot
        have hpol1 : pol ⟨j1.val, by omega⟩ = pnew := by simp [pnew, hj1]
        have hf1 : f' j1 = knew := by simp [f', dif_neg h1]
        have hf2 : f' j2 = f ⟨j2.val, h2⟩ := by simp [f', dif_pos h2]
        dsimp only
        rw [hf1, hf2, hpol1]
        exact ⟨hnot.2.1, hnot.2.2.2⟩
      · exfalso; apply hne; ext; omega
  rcases hind d le_rfl with ⟨f, hf⟩
  exact ⟨f, fun j1 j2 hne => by simpa using hf j1 j2 hne⟩

end GreedyPick

end PEqualNP.Outside.L_lib_944_aux

theorem PEqualNP.Outside.L_lib_944 : (∃ C : ℕ, 0 < C ∧ ∀ (d : ℕ) (pol : Fin d → Bool),
  ∃ b : ℕ, b + 1 ≤ C * (d + 1) ∧
    let I := Bool × Fin (b + 1)
    ∃ (π : Equiv.Perm I) (pick : Fin d ↪ I),
      (∀ i, (π i).1 = !(i.1)) ∧ (∀ j, (pick j).1 = pol j) ∧
      ∀ y : Bool × I → Bool,
        let mass := (Finset.univ.filter (fun u : Bool × I => y u = true)).card
        let red := (Finset.univ.filter (fun i : I => y (false,i) ≠ y (true,i))).card
        let blue := (Finset.univ.filter (fun i : I =>
          y (false,i) ≠ y (true,(i.1,i.2+1)))).card
        let cuts := Finset.univ.image (fun j : Fin d => pick j)
        let cross := (Finset.univ.filter (fun i : I =>
          i ∉ cuts ∧ y (false,i) ≠ y (true,π i))).card
        let ports := ∑ j : Fin d, ((y (false,pick j)).toNat + (y (true,π (pick j))).toNat)
        2 * mass ≤ 4 * (b+1) → mass + C * ports ≤ C * (red + blue + cross)) := by
  classical
  refine ⟨2000, by omega, fun d pol => ?_⟩
  refine ⟨2000 * (d + 1) - 1, by omega, ?_⟩
  set b := 2000 * (d + 1) - 1
  have hNval : b + 1 = 2000 * (d + 1) := by omega
  let I := Bool × Fin (b + 1)
  rcases PEqualNP.Outside.L_lib_944_aux.exists_expander_perms b with ⟨σ0, σ1, hexp⟩
  rcases PEqualNP.Outside.L_lib_944_aux.exists_spaced_pick b 500 d (by omega) (by omega) σ0 σ1 pol with
    ⟨f, hf_sep⟩
  let π : Equiv.Perm I :=
    { toFun := fun i => if i.1 = false then (true, σ0 i.2) else (false, σ1 i.2)
      invFun := fun i => if i.1 = true then (false, σ0.symm i.2) else (true, σ1.symm i.2)
      left_inv := fun ⟨r, k⟩ => by cases r <;> simp
      right_inv := fun ⟨r, k⟩ => by cases r <;> simp }
  have hπ_swap : ∀ i : I, (π i).1 = !(i.1) := by
    rintro ⟨r, k⟩; cases r <;> simp [π]
  have hpick_inj : Function.Injective (fun j : Fin d => ((pol j, f j) : I)) := by
    intro j1 j2 heq
    by_contra hne
    have hpol : pol j1 = pol j2 := congrArg Prod.fst heq
    have hf_eq : f j1 = f j2 := congrArg Prod.snd heq
    have hsep := hf_sep j1 j2 hne
    cases hp : pol j1
    · have h1 := hsep.1
      simp only [hp, ← hpol, ↓reduceIte, hf_eq] at h1
      have h0 : PEqualNP.Outside.L_lib_944_aux.cycDist (b + 1) (f j2) (f j2) = 0 := by
        unfold PEqualNP.Outside.L_lib_944_aux.cycDist
        have : (f j2).val + (b + 1) - (f j2).val = b + 1 := by omega
        rw [this, Nat.mod_self]
      omega
    · have h2 := hsep.2
      simp only [hp, ← hpol, ↓reduceIte, hf_eq] at h2
      have h0 : PEqualNP.Outside.L_lib_944_aux.cycDist (b + 1) (f j2) (f j2) = 0 := by
        unfold PEqualNP.Outside.L_lib_944_aux.cycDist
        have : (f j2).val + (b + 1) - (f j2).val = b + 1 := by omega
        rw [this, Nat.mod_self]
      omega
  let pick : Fin d ↪ I := ⟨fun j => (pol j, f j), hpick_inj⟩
  refine ⟨π, pick, hπ_swap, fun j => rfl, fun y hmass => ?_⟩
  set mass := (Finset.univ.filter (fun u : Bool × I => y u = true)).card
  set red := (Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, i))).card
  set blue := (Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, (i.1, i.2 + 1)))).card
  set cuts := Finset.univ.image (fun j : Fin d => pick j)
  set cross := (Finset.univ.filter (fun i : I => i ∉ cuts ∧ y (false, i) ≠ y (true, π i))).card
  set ports := ∑ j : Fin d, ((y (false, pick j)).toNat + (y (true, π (pick j))).toNat)
  have hR_eq : PEqualNP.Outside.L_lib_944_aux.ringB b false y +
      PEqualNP.Outside.L_lib_944_aux.ringB b true y = red + blue :=
    PEqualNP.Outside.L_lib_944_aux.ringB_eq_red_add_blue b y
  have hXfull_eq : PEqualNP.Outside.L_lib_944_aux.crossFull b σ0 σ1 y =
      (Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, π i))).card := by
    have hdisj : Disjoint
        ((Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (false, k)) ≠ y (true, (true, σ0 k)))).image (fun k => (false, k)))
        ((Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (true, k)) ≠ y (true, (false, σ1 k)))).image (fun k => (true, k))) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨_, _, h⟩
      exact Bool.false_ne_true.symm (congrArg Prod.fst h)
    have hunion : Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, π i)) =
        (Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (false, k)) ≠ y (true, (true, σ0 k)))).image (fun k => (false, k)) ∪
        (Finset.univ.filter (fun k : Fin (b + 1) =>
          y (false, (true, k)) ≠ y (true, (false, σ1 k)))).image (fun k => (true, k)) := by
      ext ⟨r, k⟩
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      cases r
      · change y (false, (false, k)) ≠ y (true, (true, σ0 k)) ↔ _
        constructor
        · intro h; exact Or.inl ⟨k, h, rfl⟩
        · rintro (⟨a, ha, heq⟩ | ⟨a, _, heq⟩)
          · cases heq; exact ha
          · cases heq
      · change y (false, (true, k)) ≠ y (true, (false, σ1 k)) ↔ _
        constructor
        · intro h; exact Or.inr ⟨k, h, rfl⟩
        · rintro (⟨a, _, heq⟩ | ⟨a, ha, heq⟩)
          · cases heq
          · cases heq; exact ha
    rw [hunion, Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h),
        Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
    rfl
  have hcut_loss : PEqualNP.Outside.L_lib_944_aux.crossFull b σ0 σ1 y ≤ cross + ports := by
    rw [hXfull_eq]
    have hsub : Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, π i)) ⊆
        Finset.univ.filter (fun i : I => i ∉ cuts ∧ y (false, i) ≠ y (true, π i)) ∪
        Finset.univ.filter (fun i : I => i ∈ cuts ∧ y (false, i) ≠ y (true, π i)) := by
      intro i hi
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_cases hc : i ∈ cuts
      · right; exact ⟨hc, hi⟩
      · left; exact ⟨hc, hi⟩
    have hloss_le : (Finset.univ.filter (fun i : I => i ∈ cuts ∧ y (false, i) ≠ y (true, π i))).card ≤
        ports := by
      have hbi : (Finset.univ.filter (fun i : I => i ∈ cuts ∧ y (false, i) ≠ y (true, π i))).card =
          (Finset.univ.filter (fun j : Fin d => y (false, pick j) ≠ y (true, π (pick j)))).card := by
        symm
        refine Finset.card_bij (fun j _ => pick j) ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ j), hj⟩
        · intro a _ c _ h; exact pick.injective h
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases Finset.mem_image.mp hi.1 with ⟨j, _, rfl⟩
          exact ⟨j, by simpa using hi.2, rfl⟩
      rw [hbi, Finset.card_filter]
      refine Finset.sum_le_sum fun j _ => ?_
      cases y (false, pick j) <;> cases y (true, π (pick j)) <;> simp
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left hloss_le _))
  let p0 : Fin d → Fin (2 * (b + 1)) := fun j =>
    if pol j = false then PEqualNP.Outside.L_lib_944_aux.ringPos b false (f j)
    else PEqualNP.Outside.L_lib_944_aux.ringPos b true (σ1 (f j))
  let p1 : Fin d → Fin (2 * (b + 1)) := fun j =>
    if pol j = true then PEqualNP.Outside.L_lib_944_aux.ringPos b false (f j)
    else PEqualNP.Outside.L_lib_944_aux.ringPos b true (σ0 (f j))
  have hp0_sep : ∀ j1 j2 : Fin d, j1 ≠ j2 →
      500 ≤ PEqualNP.Outside.L_lib_944_aux.cycDist (2 * (b + 1)) (p0 j1) (p0 j2) := by
    intro j1 j2 hne
    have h12 := hf_sep j1 j2 hne
    have h21 := hf_sep j2 j1 hne.symm
    dsimp only [p0]
    cases hp1 : pol j1 <;> cases hp2 : pol j2 <;> simp only [hp1, hp2, ↓reduceIte, Bool.true_eq_false]
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        false false (f j1) (f j2) (by simpa [hp1, hp2] using h12.1) (by simpa [hp1, hp2] using h21.1)
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        false true (f j1) (σ1 (f j2)) (by simpa [hp1, hp2] using h12.1) (by simpa [hp1, hp2] using h21.1)
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        true false (σ1 (f j1)) (f j2) (by simpa [hp1, hp2] using h12.1) (by simpa [hp1, hp2] using h21.1)
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        true true (σ1 (f j1)) (σ1 (f j2)) (by simpa [hp1, hp2] using h12.1) (by simpa [hp1, hp2] using h21.1)
  have hp1_sep : ∀ j1 j2 : Fin d, j1 ≠ j2 →
      500 ≤ PEqualNP.Outside.L_lib_944_aux.cycDist (2 * (b + 1)) (p1 j1) (p1 j2) := by
    intro j1 j2 hne
    have h12 := hf_sep j1 j2 hne
    have h21 := hf_sep j2 j1 hne.symm
    dsimp only [p1]
    cases hp1 : pol j1 <;> cases hp2 : pol j2 <;> simp only [hp1, hp2, ↓reduceIte, Bool.false_eq_true]
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        true true (σ0 (f j1)) (σ0 (f j2)) (by simpa [hp1, hp2] using h12.2) (by simpa [hp1, hp2] using h21.2)
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        true false (σ0 (f j1)) (f j2) (by simpa [hp1, hp2] using h12.2) (by simpa [hp1, hp2] using h21.2)
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        false true (f j1) (σ0 (f j2)) (by simpa [hp1, hp2] using h12.2) (by simpa [hp1, hp2] using h21.2)
    · exact PEqualNP.Outside.L_lib_944_aux.cycDist_ringPos_ge b 500 (by omega) (by omega)
        false false (f j1) (f j2) (by simpa [hp1, hp2] using h12.2) (by simpa [hp1, hp2] using h21.2)
  have hp0_inj : Function.Injective p0 := by
    intro j1 j2 heq
    by_contra hne
    have h := hp0_sep j1 j2 hne
    rw [heq] at h
    have h0 : PEqualNP.Outside.L_lib_944_aux.cycDist (2 * (b + 1)) (p0 j2) (p0 j2) = 0 := by
      unfold PEqualNP.Outside.L_lib_944_aux.cycDist
      have : (p0 j2).val + 2 * (b + 1) - (p0 j2).val = 2 * (b + 1) := by omega
      rw [this, Nat.mod_self]
    omega
  have hp1_inj : Function.Injective p1 := by
    intro j1 j2 heq
    by_contra hne
    have h := hp1_sep j1 j2 hne
    rw [heq] at h
    have h0 : PEqualNP.Outside.L_lib_944_aux.cycDist (2 * (b + 1)) (p1 j2) (p1 j2) = 0 := by
      unfold PEqualNP.Outside.L_lib_944_aux.cycDist
      have : (p1 j2).val + 2 * (b + 1) - (p1 j2).val = 2 * (b + 1) := by omega
      rw [this, Nat.mod_self]
    omega
  let P0 := Finset.univ.image p0
  let P1 := Finset.univ.image p1
  have hports_eq : ports =
      (P0.filter (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b false p) = true)).card +
      (P1.filter (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b true p) = true)).card := by
    have h0 : (P0.filter (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b false p) = true)).card =
        ∑ j : Fin d, (y (PEqualNP.Outside.L_lib_944_aux.ringVert b false (p0 j))).toNat := by
      have hbi : (P0.filter (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b false p) = true)).card =
          (Finset.univ.filter (fun j : Fin d =>
            y (PEqualNP.Outside.L_lib_944_aux.ringVert b false (p0 j)) = true)).card := by
        symm
        refine Finset.card_bij (fun j _ => p0 j) ?_ ?_ ?_
        · intro j hj
          simp only [P0, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hj ⊢
          exact ⟨⟨j, rfl⟩, hj⟩
        · intro a _ c _ h; exact hp0_inj h
        · intro p hp
          rcases Finset.mem_image.mp (Finset.mem_filter.mp hp).1 with ⟨j, _, rfl⟩
          exact ⟨j, by simpa using (Finset.mem_filter.mp hp).2, rfl⟩
      rw [hbi, Finset.card_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases y (PEqualNP.Outside.L_lib_944_aux.ringVert b false (p0 j)) <;> simp
    have h1 : (P1.filter (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b true p) = true)).card =
        ∑ j : Fin d, (y (PEqualNP.Outside.L_lib_944_aux.ringVert b true (p1 j))).toNat := by
      have hbi : (P1.filter (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b true p) = true)).card =
          (Finset.univ.filter (fun j : Fin d =>
            y (PEqualNP.Outside.L_lib_944_aux.ringVert b true (p1 j)) = true)).card := by
        symm
        refine Finset.card_bij (fun j _ => p1 j) ?_ ?_ ?_
        · intro j hj
          simp only [P1, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hj ⊢
          exact ⟨⟨j, rfl⟩, hj⟩
        · intro a _ c _ h; exact hp1_inj h
        · intro p hp
          rcases Finset.mem_image.mp (Finset.mem_filter.mp hp).1 with ⟨j, _, rfl⟩
          exact ⟨j, by simpa using (Finset.mem_filter.mp hp).2, rfl⟩
      rw [hbi, Finset.card_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases y (PEqualNP.Outside.L_lib_944_aux.ringVert b true (p1 j)) <;> simp
    rw [h0, h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases hp : pol j
    · simp only [pick, π, p0, p1, Function.Embedding.coeFn_mk, Equiv.coe_fn_mk, hp,
        ↓reduceIte, Bool.false_eq_true, PEqualNP.Outside.L_lib_944_aux.ringVert_ringPos]
    · simp only [pick, π, p0, p1, Function.Embedding.coeFn_mk, Equiv.coe_fn_mk, hp,
        ↓reduceIte, Bool.true_eq_false, PEqualNP.Outside.L_lib_944_aux.ringVert_ringPos]
      ring
  have hsp0 := PEqualNP.Outside.L_lib_944_aux.cycle_port_spacing (2 * (b + 1)) 500
    (by omega) (by omega) (by omega)
    (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b false p)) P0 (by
      intro q1 hq1 q2 hq2 hne
      rcases Finset.mem_image.mp hq1 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp hq2 with ⟨j2, _, rfl⟩
      exact hp0_sep j1 j2 (fun h => hne (congrArg p0 h)))
  have hsp1 := PEqualNP.Outside.L_lib_944_aux.cycle_port_spacing (2 * (b + 1)) 500
    (by omega) (by omega) (by omega)
    (fun p => y (PEqualNP.Outside.L_lib_944_aux.ringVert b true p)) P1 (by
      intro q1 hq1 q2 hq2 hne
      rcases Finset.mem_image.mp hq1 with ⟨j1, _, rfl⟩
      rcases Finset.mem_image.mp hq2 with ⟨j2, _, rfl⟩
      exact hp1_sep j1 j2 (fun h => hne (congrArg p1 h)))
  have hmass_split : mass =
      (Finset.univ.filter (fun p : Fin (2 * (b + 1)) =>
        y (PEqualNP.Outside.L_lib_944_aux.ringVert b false p) = true)).card +
      (Finset.univ.filter (fun p : Fin (2 * (b + 1)) =>
        y (PEqualNP.Outside.L_lib_944_aux.ringVert b true p) = true)).card :=
    PEqualNP.Outside.L_lib_944_aux.ring_mass_sum b y
  have hport_bound : 1000 * ports ≤ 500 * (red + blue) + 2 * mass := by
    have hsum := Nat.add_le_add hsp0 hsp1
    change 2 * 500 * _ + 2 * 500 * _ ≤
      500 * PEqualNP.Outside.L_lib_944_aux.ringB b false y + 2 * _ +
      (500 * PEqualNP.Outside.L_lib_944_aux.ringB b true y + 2 * _) at hsum
    omega
  have hexp_y : mass ≤ 100 * (PEqualNP.Outside.L_lib_944_aux.ringB b false y +
      PEqualNP.Outside.L_lib_944_aux.ringB b true y +
      PEqualNP.Outside.L_lib_944_aux.crossFull b σ0 σ1 y) := hexp y hmass
  omega
