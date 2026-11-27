import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_854

open Polynomial

noncomputable def delta (P : Polynomial ℚ) : Polynomial ℚ :=
  P.comp (X + 1) - P

noncomputable def nabla (P : Polynomial ℚ) : Polynomial ℚ :=
  P - P.comp (X - 1)

theorem delta_eval (P : Polynomial ℚ) (x : ℚ) :
    (delta P).eval x = P.eval (x + 1) - P.eval x := by
  simp [delta]

theorem nabla_eval (P : Polynomial ℚ) (x : ℚ) :
    (nabla P).eval x = P.eval x - P.eval (x - 1) := by
  simp [nabla]

theorem delta_add (P Q : Polynomial ℚ) : delta (P + Q) = delta P + delta Q := by
  simp [delta, add_comp]
  ring

theorem delta_C_mul (c : ℚ) (P : Polynomial ℚ) : delta (C c * P) = C c * delta P := by
  simp [delta, mul_comp]
  ring

theorem delta_C (c : ℚ) : delta (C c) = 0 := by
  simp [delta]

theorem nabla_eq_delta_comp (P : Polynomial ℚ) :
    nabla P = (delta P).comp (X - 1) := by
  simp [nabla, delta, sub_comp, comp_assoc]

theorem delta_X_pow_natDegree_le (k : ℕ) :
    (delta (X ^ (k + 1) : Polynomial ℚ)).natDegree ≤ k := by
  unfold delta
  rw [pow_comp, X_comp]
  rw [add_pow]
  rw [Finset.sum_range_succ]
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, add_sub_cancel_right]
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le k, ?_⟩
  intro m hm
  have hmk : m < k + 1 := Finset.mem_range.mp hm
  have h1 : (X ^ m * (Nat.choose (k + 1) m : Polynomial ℚ)).natDegree ≤ m := by
    exact (natDegree_mul_le).trans (by simp [natDegree_natCast])
  simp only [Function.comp_apply]
  omega

theorem delta_natDegree_le (P : Polynomial ℚ) (n : ℕ) (h : P.natDegree ≤ n + 1) :
    (delta P).natDegree ≤ n := by
  have hP : P = ∑ k ∈ Finset.range (n + 2), C (P.coeff k) * X ^ k :=
    as_sum_range_C_mul_X_pow' P (show P.natDegree < n + 2 by omega)
  rw [hP]
  have hlin : ∀ m : ℕ, delta (∑ k ∈ Finset.range m, C (P.coeff k) * X ^ k) =
      ∑ k ∈ Finset.range m, C (P.coeff k) * delta (X ^ k) := by
    intro m
    induction m with
    | zero => simp [delta]
    | succ m ih =>
      rw [Finset.sum_range_succ, delta_add, ih, delta_C_mul, Finset.sum_range_succ]
  rw [hlin]
  refine (natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le n, ?_⟩
  intro k hk
  have hkn : k < n + 2 := Finset.mem_range.mp hk
  cases k with
  | zero =>
    simp [delta]
  | succ m =>
    refine (natDegree_mul_le).trans ?_
    have hd := delta_X_pow_natDegree_le m
    have hc : (C (P.coeff (m + 1))).natDegree = 0 := natDegree_C _
    omega

theorem delta_eq_zero_of_natDegree_zero (P : Polynomial ℚ) (h : P.natDegree = 0) :
    delta P = 0 := by
  rw [eq_C_of_natDegree_eq_zero h, delta_C]

theorem nabla_natDegree_le (P : Polynomial ℚ) (n : ℕ) (h : P.natDegree ≤ n + 1) :
    (nabla P).natDegree ≤ n := by
  rw [nabla_eq_delta_comp]
  refine (natDegree_comp_le).trans ?_
  have h1 : (delta P).natDegree ≤ n := delta_natDegree_le P n h
  have h2 : (X - 1 : Polynomial ℚ).natDegree = 1 := by compute_degree!
  rw [h2, mul_one]
  exact h1

theorem nabla_eq_zero_of_natDegree_zero (P : Polynomial ℚ) (h : P.natDegree = 0) :
    nabla P = 0 := by
  rw [nabla_eq_delta_comp, delta_eq_zero_of_natDegree_zero P h, zero_comp]

theorem delta_iter_natDegree_le (k : ℕ) : ∀ (n : ℕ) (P : Polynomial ℚ),
    P.natDegree ≤ n + k → (delta^[k] P).natDegree ≤ n := by
  induction k with
  | zero =>
    intro n P h
    simpa using h
  | succ k ih =>
    intro n P h
    rw [Function.iterate_succ_apply']
    exact delta_natDegree_le _ n (ih (n + 1) P (by omega))

theorem nabla_iter_eq_zero (k : ℕ) : ∀ (P : Polynomial ℚ),
    P.natDegree ≤ k → nabla^[k + 1] P = 0 := by
  induction k with
  | zero =>
    intro P h
    exact nabla_eq_zero_of_natDegree_zero P (Nat.le_zero.mp h)
  | succ k ih =>
    intro P h
    rw [Function.iterate_succ_apply]
    exact ih (nabla P) (nabla_natDegree_le P k h)

theorem delta_iter_eval (k : ℕ) : ∀ (P : Polynomial ℚ) (x : ℚ),
    (delta^[k] P).eval x =
      ∑ s ∈ Finset.range (k + 1), (-1 : ℚ) ^ (k - s) * (Nat.choose k s : ℚ) * P.eval (x + (s : ℚ)) := by
  induction k with
  | zero =>
    intro P x
    simp
  | succ k ih =>
    intro P x
    rw [Function.iterate_succ_apply', delta_eval, ih P (x + 1), ih P x]
    rw [Finset.sum_range_succ' _ (k + 1)]
    have hsplit : ∑ s ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (k + 1 - (s + 1)) * (Nat.choose (k + 1) (s + 1) : ℚ) * P.eval (x + ((s + 1 : ℕ) : ℚ)) =
        ∑ s ∈ Finset.range (k + 1),
          (-1 : ℚ) ^ (k - s) * (Nat.choose k s : ℚ) * P.eval (x + 1 + (s : ℚ)) +
        ∑ s ∈ Finset.range (k + 1),
          (-1 : ℚ) ^ (k - s) * (Nat.choose k (s + 1) : ℚ) * P.eval (x + 1 + (s : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      rw [Nat.succ_sub_succ, Nat.choose_succ_succ, Nat.cast_add]
      have hx : x + ((s + 1 : ℕ) : ℚ) = x + 1 + (s : ℚ) := by push_cast; ring
      rw [hx]
      ring
    rw [hsplit]
    have hshift : ∑ s ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (k - s) * (Nat.choose k s : ℚ) * P.eval (x + (s : ℚ)) =
        (-1 : ℚ) ^ k * P.eval x +
        ∑ s ∈ Finset.range k,
          (-1 : ℚ) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ℚ) * P.eval (x + 1 + (s : ℚ)) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.cast_zero, add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      have hx : x + ((s + 1 : ℕ) : ℚ) = x + 1 + (s : ℚ) := by push_cast; ring
      rw [hx]
    have htop : ∑ s ∈ Finset.range (k + 1),
        (-1 : ℚ) ^ (k - s) * (Nat.choose k (s + 1) : ℚ) * P.eval (x + 1 + (s : ℚ)) =
        ∑ s ∈ Finset.range k,
          (-1 : ℚ) ^ (k - s) * (Nat.choose k (s + 1) : ℚ) * P.eval (x + 1 + (s : ℚ)) := by
      rw [Finset.sum_range_succ]
      simp
    have hneg : ∑ s ∈ Finset.range k,
        (-1 : ℚ) ^ (k - s) * (Nat.choose k (s + 1) : ℚ) * P.eval (x + 1 + (s : ℚ)) =
        - ∑ s ∈ Finset.range k,
          (-1 : ℚ) ^ (k - (s + 1)) * (Nat.choose k (s + 1) : ℚ) * P.eval (x + 1 + (s : ℚ)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      have hsk : s < k := Finset.mem_range.mp hs
      have hpow : k - s = (k - (s + 1)) + 1 := by omega
      rw [hpow, pow_succ]
      ring
    rw [hshift, htop, hneg]
    simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.cast_zero, add_zero, pow_succ]
    ring

theorem sum_by_parts_zero (D : ℕ) (f g : ℚ → ℚ) :
    ∑ i ∈ Finset.range (D + 1), (f ((i : ℚ) + 1) - f (i : ℚ)) * g (i : ℚ) =
      f ((D : ℚ) + 1) * g (D : ℚ) - f 0 * g 0 -
      ∑ i ∈ Finset.Ico 1 (D + 1), f (i : ℚ) * (g (i : ℚ) - g ((i : ℚ) - 1)) := by
  induction D with
  | zero =>
    simp
    ring
  | succ D ih =>
    rw [Finset.sum_range_succ, ih]
    have hico : Finset.Ico 1 (D + 1 + 1) = insert (D + 1) (Finset.Ico 1 (D + 1)) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hnotmem : D + 1 ∉ Finset.Ico 1 (D + 1) := by simp
    rw [hico, Finset.sum_insert hnotmem]
    push_cast
    have hsub : (D : ℚ) + 1 - 1 = (D : ℚ) := by ring
    rw [hsub]
    ring

theorem sum_by_parts_one (D : ℕ) (f g : ℚ → ℚ) (h1 : f 1 = 0) (hR : f ((D : ℚ) + 1) = 0) :
    ∑ i ∈ Finset.Ico 1 (D + 1), (f ((i : ℚ) + 1) - f (i : ℚ)) * g (i : ℚ) =
      - ∑ i ∈ Finset.Ico 1 (D + 1), f (i : ℚ) * (g (i : ℚ) - g ((i : ℚ) - 1)) := by
  have hgen : ∀ n : ℕ, 1 ≤ n →
      ∑ i ∈ Finset.Ico 1 n, (f ((i : ℚ) + 1) - f (i : ℚ)) * g (i : ℚ) =
        f (n : ℚ) * g ((n : ℚ) - 1) - f 1 * g 0 -
        ∑ i ∈ Finset.Ico 1 n, f (i : ℚ) * (g (i : ℚ) - g ((i : ℚ) - 1)) := by
    intro n hn
    induction n with
    | zero => omega
    | succ m ih =>
      by_cases hm : m = 0
      · subst hm
        simp
      · have h1m : 1 ≤ m := by omega
        have hico : Finset.Ico 1 (m + 1) = insert m (Finset.Ico 1 m) := by
          ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
        have hnm : m ∉ Finset.Ico 1 m := by simp
        rw [hico, Finset.sum_insert hnm, Finset.sum_insert hnm, ih h1m]
        push_cast
        have hsub : (m : ℚ) + 1 - 1 = (m : ℚ) := by ring
        rw [hsub]
        ring
  have h := hgen (D + 1) (by omega)
  push_cast at h
  rw [h, h1, hR]
  ring

noncomputable def G (D d : ℕ) : Polynomial ℚ :=
  (∏ j ∈ Finset.range d, (X - C ((1 + j : ℕ) : ℚ))) *
  (∏ j ∈ Finset.range (d + 1), (X - C ((D + 1 + j : ℕ) : ℚ)))

theorem prod_X_sub_natDegree_le (n : ℕ) (c : ℕ → ℚ) :
    (∏ j ∈ Finset.range n, (X - C (c j))).natDegree ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    refine (natDegree_mul_le).trans ?_
    have h1 : (X - C (c n)).natDegree = 1 := natDegree_X_sub_C (c n)
    omega

theorem G_natDegree_le (D d : ℕ) : (G D d).natDegree ≤ d + (d + 1) := by
  unfold G
  refine (natDegree_mul_le).trans ?_
  have h1 := prod_X_sub_natDegree_le d (fun j => ((1 + j : ℕ) : ℚ))
  have h2 := prod_X_sub_natDegree_le (d + 1) (fun j => ((D + 1 + j : ℕ) : ℚ))
  omega

theorem G_eval_left (D d n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ d) :
    (G D d).eval (n : ℚ) = 0 := by
  unfold G
  rw [eval_mul, eval_prod]
  have hmem : n - 1 ∈ Finset.range d := Finset.mem_range.mpr (by omega)
  have hzero : (∏ j ∈ Finset.range d, (X - C ((1 + j : ℕ) : ℚ)).eval (n : ℚ)) = 0 := by
    apply Finset.prod_eq_zero hmem
    simp only [eval_sub, eval_X, eval_C]
    have : 1 + (n - 1) = n := by omega
    rw [this, sub_self]
  rw [hzero, zero_mul]

theorem G_eval_right (D d n : ℕ) (h1 : D + 1 ≤ n) (h2 : n ≤ D + d + 1) :
    (G D d).eval (n : ℚ) = 0 := by
  unfold G
  rw [eval_mul, eval_prod, eval_prod]
  have hmem : n - (D + 1) ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have hzero : (∏ j ∈ Finset.range (d + 1), (X - C ((D + 1 + j : ℕ) : ℚ)).eval (n : ℚ)) = 0 := by
    apply Finset.prod_eq_zero hmem
    simp only [eval_sub, eval_X, eval_C]
    have : D + 1 + (n - (D + 1)) = n := by omega
    rw [this, sub_self]
  rw [hzero, mul_zero]

theorem prod_range_add_eq_descFactorial (a k : ℕ) :
    ∏ j ∈ Finset.range k, (a + j) = Nat.descFactorial (a + k - 1) k := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ']
    have h1 : ∏ j ∈ Finset.range k, (a + (j + 1)) = ∏ j ∈ Finset.range k, ((a + 1) + j) := by
      apply Finset.prod_congr rfl; intro j _; ring
    rw [h1, ih (a + 1), add_zero]
    have h2 : a + 1 + k - 1 = a + k := by omega
    have h3 : a + (k + 1) - 1 = a + k := by omega
    rw [h2, h3, Nat.descFactorial_succ]
    have h4 : a + k - k = a := by omega
    rw [h4, mul_comm]

theorem prod_range_succ_eq_factorial (k : ℕ) :
    ∏ j ∈ Finset.range k, (1 + j) = k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    ring

theorem G_eval_zero (D d : ℕ) :
    (G D d).eval 0 =
      - ((d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
        (Nat.choose (D + d + 1) (d + 1) : ℚ)) := by
  unfold G
  rw [eval_mul, eval_prod, eval_prod]
  have h1 : (∏ j ∈ Finset.range d, (X - C ((1 + j : ℕ) : ℚ)).eval 0) =
      (-1 : ℚ) ^ d * (d.factorial : ℚ) := by
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    have hneg : ∀ j : ℕ, -((1 + j : ℕ) : ℚ) = (-1 : ℚ) * ((1 + j : ℕ) : ℚ) := fun j => by ring
    simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    rw [← Nat.cast_prod, prod_range_succ_eq_factorial]
  have h2 : (∏ j ∈ Finset.range (d + 1), (X - C ((D + 1 + j : ℕ) : ℚ)).eval 0) =
      (-1 : ℚ) ^ (d + 1) * (((d + 1).factorial : ℚ) * (Nat.choose (D + d + 1) (d + 1) : ℚ)) := by
    simp only [eval_sub, eval_X, eval_C, zero_sub]
    have hneg : ∀ j : ℕ, -((D + 1 + j : ℕ) : ℚ) = (-1 : ℚ) * ((D + 1 + j : ℕ) : ℚ) := fun j => by ring
    simp_rw [hneg, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    rw [← Nat.cast_prod, prod_range_add_eq_descFactorial]
    have hsub : D + 1 + (d + 1) - 1 = D + d + 1 := by omega
    rw [hsub, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hsq : (-1 : ℚ) ^ d * (-1 : ℚ) ^ d = 1 := by
    rw [← mul_pow]; norm_num
  rw [h1, h2, pow_succ]
  calc (-1 : ℚ) ^ d * (d.factorial : ℚ) *
        ((-1 : ℚ) ^ d * (-1 : ℚ) * (((d + 1).factorial : ℚ) * (Nat.choose (D + d + 1) (d + 1) : ℚ)))
      = - (((-1 : ℚ) ^ d * (-1 : ℚ) ^ d) * (d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
          (Nat.choose (D + d + 1) (d + 1) : ℚ)) := by ring
    _ = - ((d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
          (Nat.choose (D + d + 1) (d + 1) : ℚ)) := by rw [hsq]; ring

theorem G_eval_succ (D d : ℕ) (hdD : d ≤ D) :
    (G D d).eval ((d + 1 : ℕ) : ℚ) =
      (-1 : ℚ) ^ (d + 1) * (d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
        (Nat.choose D (d + 1) : ℚ) := by
  unfold G
  rw [eval_mul, eval_prod, eval_prod]
  have h1 : (∏ j ∈ Finset.range d, (X - C ((1 + j : ℕ) : ℚ)).eval ((d + 1 : ℕ) : ℚ)) =
      (d.factorial : ℚ) := by
    simp only [eval_sub, eval_X, eval_C]
    have heq : ∏ j ∈ Finset.range d, (((d + 1 : ℕ) : ℚ) - ((1 + j : ℕ) : ℚ)) =
        ∏ j ∈ Finset.range d, (((d - j : ℕ) : ℚ)) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      have : (d - j : ℕ) + (1 + j) = d + 1 := by omega
      have hcast : ((d - j : ℕ) : ℚ) + ((1 + j : ℕ) : ℚ) = ((d + 1 : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    rw [heq, ← Nat.cast_prod]
    have hrev : ∏ j ∈ Finset.range d, (d - j) = ∏ j ∈ Finset.range d, (1 + j) := by
      rw [← Finset.prod_range_reflect (fun j => 1 + j) d]
      apply Finset.prod_congr rfl
      intro j hj
      have hjd : j < d := Finset.mem_range.mp hj
      omega
    rw [hrev, prod_range_succ_eq_factorial]
  have h2 : (∏ j ∈ Finset.range (d + 1), (X - C ((D + 1 + j : ℕ) : ℚ)).eval ((d + 1 : ℕ) : ℚ)) =
      (-1 : ℚ) ^ (d + 1) * (((d + 1).factorial : ℚ) * (Nat.choose D (d + 1) : ℚ)) := by
    simp only [eval_sub, eval_X, eval_C]
    have heq : ∏ j ∈ Finset.range (d + 1), (((d + 1 : ℕ) : ℚ) - ((D + 1 + j : ℕ) : ℚ)) =
        ∏ j ∈ Finset.range (d + 1), ((-1 : ℚ) * (((D - d + j : ℕ) : ℚ))) := by
      apply Finset.prod_congr rfl
      intro j _
      have : (D - d + j) + (d + 1) = D + 1 + j := by omega
      have hcast : ((D - d + j : ℕ) : ℚ) + ((d + 1 : ℕ) : ℚ) = ((D + 1 + j : ℕ) : ℚ) := by exact_mod_cast this
      linarith
    rw [heq, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    rw [← Nat.cast_prod]
    by_cases hlt : d < D
    · rw [prod_range_add_eq_descFactorial]
      have hsub : D - d + (d + 1) - 1 = D := by omega
      rw [hsub, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    · have heqD : d = D := by omega
      subst heqD
      have h0 : ∏ j ∈ Finset.range (d + 1), (d - d + j) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.zero_lt_succ d))
        simp
      rw [h0, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self d)]
      simp
  rw [h1, h2]
  ring

theorem delta_m_G_right_zero (D d m n : ℕ) (h1 : D + 1 ≤ n) (h2 : n + m ≤ D + d + 1) :
    (delta^[m] (G D d)).eval (n : ℚ) = 0 := by
  rw [delta_iter_eval]
  apply Finset.sum_eq_zero
  intro s hs
  have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hev : (G D d).eval ((n : ℚ) + (s : ℚ)) = 0 := by
    rw [← Nat.cast_add]
    exact G_eval_right D d (n + s) (by omega) (by omega)
  rw [hev, mul_zero]

theorem delta_m_G_one_zero (D d m : ℕ) (hm : m < d) :
    (delta^[m] (G D d)).eval 1 = 0 := by
  rw [delta_iter_eval]
  apply Finset.sum_eq_zero
  intro s hs
  have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hev : (G D d).eval (1 + (s : ℚ)) = 0 := by
    have : (1 : ℚ) + (s : ℚ) = ((1 + s : ℕ) : ℚ) := by push_cast; ring
    rw [this]
    exact G_eval_left D d (1 + s) (by omega) (by omega)
  rw [hev, mul_zero]

theorem delta_m_G_zero (D d m : ℕ) (hm : m ≤ d) :
    (delta^[m] (G D d)).eval 0 = (-1 : ℚ) ^ m * (G D d).eval 0 := by
  rw [delta_iter_eval]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro s hs hs0
    have hsm : s ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hev : (G D d).eval (0 + (s : ℚ)) = 0 := by
      rw [zero_add]
      exact G_eval_left D d s (by omega) (by omega)
    rw [hev, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.zero_lt_succ m)) h

theorem delta_succ_G_zero (D d : ℕ) (hdD : d ≤ D) :
    (delta^[d + 1] (G D d)).eval 0 =
      (-1 : ℚ) ^ d * (d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
        ((Nat.choose (D + d + 1) (d + 1) : ℚ) - (Nat.choose D (d + 1) : ℚ)) := by
  rw [delta_iter_eval]
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  have hmid : ∑ s ∈ Finset.range d,
      (-1 : ℚ) ^ (d + 1 - (s + 1)) * (Nat.choose (d + 1) (s + 1) : ℚ) *
        (G D d).eval (0 + ((s + 1 : ℕ) : ℚ)) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have hsd : s < d := Finset.mem_range.mp hs
    rw [zero_add, G_eval_left D d (s + 1) (by omega) (by omega), mul_zero]
  rw [hmid, zero_add]
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.cast_zero, add_zero,
    Nat.sub_self, pow_zero, Nat.choose_self, one_mul, zero_add]
  rw [G_eval_zero, G_eval_succ D d hdD, pow_succ]
  ring

theorem sum_ico_delta_iter (D d : ℕ) : ∀ (m : ℕ), m ≤ d → ∀ (r : Polynomial ℚ),
    ∑ i ∈ Finset.Ico 1 (D + 1), (delta^[m] (G D d)).eval (i : ℚ) * r.eval (i : ℚ) =
      (-1 : ℚ) ^ m * ∑ i ∈ Finset.Ico 1 (D + 1), (G D d).eval (i : ℚ) * (nabla^[m] r).eval (i : ℚ) := by
  intro m
  induction m with
  | zero =>
    intro _ r
    simp
  | succ m ih =>
    intro hm r
    have hstep : ∑ i ∈ Finset.Ico 1 (D + 1),
        (delta^[m + 1] (G D d)).eval (i : ℚ) * r.eval (i : ℚ) =
        - ∑ i ∈ Finset.Ico 1 (D + 1),
          (delta^[m] (G D d)).eval (i : ℚ) * (nabla r).eval (i : ℚ) := by
      have heq1 : ∑ i ∈ Finset.Ico 1 (D + 1),
          (delta^[m + 1] (G D d)).eval (i : ℚ) * r.eval (i : ℚ) =
          ∑ i ∈ Finset.Ico 1 (D + 1),
            ((delta^[m] (G D d)).eval ((i : ℚ) + 1) - (delta^[m] (G D d)).eval (i : ℚ)) * r.eval (i : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Function.iterate_succ_apply', delta_eval]
      rw [heq1]
      rw [sum_by_parts_one D (fun x => (delta^[m] (G D d)).eval x) (fun x => r.eval x)
        (delta_m_G_one_zero D d m (by omega))
        (by
          have : ((D : ℚ) + 1) = ((D + 1 : ℕ) : ℚ) := by push_cast; ring
          rw [this]
          exact delta_m_G_right_zero D d m (D + 1) le_rfl (by omega))]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [nabla_eval]
    rw [hstep, ih (by omega) (nabla r), Function.iterate_succ_apply, pow_succ]
    ring

theorem H_orth (D d : ℕ) (q : Polynomial ℚ) (hq : q.natDegree ≤ d) :
    ∑ i ∈ Finset.range (D + 1), (delta^[d + 1] (G D d)).eval (i : ℚ) * q.eval (i : ℚ) =
      (-1 : ℚ) ^ d * (d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
        (Nat.choose (D + d + 1) (d + 1) : ℚ) * q.eval 0 := by
  have heq1 : ∑ i ∈ Finset.range (D + 1),
      (delta^[d + 1] (G D d)).eval (i : ℚ) * q.eval (i : ℚ) =
      ∑ i ∈ Finset.range (D + 1),
        ((delta^[d] (G D d)).eval ((i : ℚ) + 1) - (delta^[d] (G D d)).eval (i : ℚ)) * q.eval (i : ℚ) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Function.iterate_succ_apply', delta_eval]
  rw [heq1, sum_by_parts_zero D (fun x => (delta^[d] (G D d)).eval x) (fun x => q.eval x)]
  have hR : (delta^[d] (G D d)).eval ((D : ℚ) + 1) = 0 := by
    have : ((D : ℚ) + 1) = ((D + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [this]
    exact delta_m_G_right_zero D d d (D + 1) le_rfl (by omega)
  have hL : (delta^[d] (G D d)).eval 0 = (-1 : ℚ) ^ d * (G D d).eval 0 :=
    delta_m_G_zero D d d le_rfl
  have hico : ∑ i ∈ Finset.Ico 1 (D + 1),
      (delta^[d] (G D d)).eval (i : ℚ) * (q.eval (i : ℚ) - q.eval ((i : ℚ) - 1)) = 0 := by
    have hrew : ∑ i ∈ Finset.Ico 1 (D + 1),
        (delta^[d] (G D d)).eval (i : ℚ) * (q.eval (i : ℚ) - q.eval ((i : ℚ) - 1)) =
        ∑ i ∈ Finset.Ico 1 (D + 1),
          (delta^[d] (G D d)).eval (i : ℚ) * (nabla q).eval (i : ℚ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [nabla_eval]
    rw [hrew, sum_ico_delta_iter D d d le_rfl (nabla q)]
    have hzero : nabla^[d] (nabla q) = 0 := by
      rw [← Function.iterate_succ_apply]
      exact nabla_iter_eq_zero d q hq
    rw [hzero]
    simp
  rw [hR, hL, hico, G_eval_zero]
  ring

theorem eval_poly_eq_fin_sum (d : ℕ) (P : Polynomial ℚ) (hP : P.natDegree ≤ d) (x : ℚ) :
    P.eval x = ∑ j : Fin (d + 1), P.coeff j.val * x ^ j.val := by
  rw [eval_eq_sum_range' (lt_of_le_of_lt hP (Nat.lt_succ_self d)), ← Fin.sum_univ_eq_sum_range]

theorem fin_sum_eq_poly_eval (d : ℕ) (v : Fin (d + 1) → ℚ) :
    ∃ Q : Polynomial ℚ, Q.natDegree ≤ d ∧ ∀ x : ℚ, (∑ j : Fin (d + 1), v j * x ^ j.val) = Q.eval x := by
  refine ⟨∑ j : Fin (d + 1), C (v j) * X ^ j.val, ?_, ?_⟩
  · refine (natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    refine ⟨Nat.zero_le d, ?_⟩
    intro j _
    refine (natDegree_mul_le).trans ?_
    simp only [natDegree_C, zero_add, natDegree_X_pow]
    omega
  · intro x
    rw [← Polynomial.coe_evalRingHom, map_sum]
    simp [Polynomial.coe_evalRingHom]

theorem main (D d : ℕ) (hdD : d ≤ D) :
    let eval := fun (w : Fin (d+1) → ℚ) (x : ℚ) => ∑ j, w j * x^j.val
    let delta0 := fun (i : Fin (D+1)) => if i.val = 0 then (1 : ℚ) else 0
    let loss := fun w => ∑ i : Fin (D+1), (delta0 i - eval w (i.val : ℚ))^2
    ∃ w : Fin (d+1) → ℚ,
      loss w = (Nat.choose D (d+1) : ℚ) / (Nat.choose (D+d+1) (d+1) : ℚ) ∧
      ∀ v : Fin (d+1) → ℚ,
        loss v = loss w + ∑ i : Fin (D+1), (eval v (i.val : ℚ) - eval w (i.val : ℚ))^2 := by
  intro eval delta0 loss
  let C0 : ℚ := (-1 : ℚ) ^ d * (d.factorial : ℚ) * ((d + 1).factorial : ℚ) *
    (Nat.choose (D + d + 1) (d + 1) : ℚ)
  have hC0_ne : C0 ≠ 0 := by
    have h1 : (-1 : ℚ) ^ d ≠ 0 := pow_ne_zero d (by norm_num)
    have h2 : (d.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
    have h3 : ((d + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (d + 1))
    have h4 : (Nat.choose (D + d + 1) (d + 1) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4
  let Pstar : Polynomial ℚ := C C0⁻¹ * (delta^[d + 1] (G D d))
  have hPstar_deg : Pstar.natDegree ≤ d := by
    refine (natDegree_mul_le).trans ?_
    have h1 : (C C0⁻¹).natDegree = 0 := natDegree_C _
    have h2 := delta_iter_natDegree_le (d + 1) d (G D d) (G_natDegree_le D d)
    omega
  let w : Fin (d + 1) → ℚ := fun j => Pstar.coeff j.val
  have hw_eval : ∀ x : ℚ, eval w x = Pstar.eval x := fun x =>
    (eval_poly_eq_fin_sum d Pstar hPstar_deg x).symm
  have horth_poly : ∀ Q : Polynomial ℚ, Q.natDegree ≤ d →
      ∑ i : Fin (D + 1), (delta0 i - Pstar.eval (i.val : ℚ)) * Q.eval (i.val : ℚ) = 0 := by
    intro Q hQ
    have hsplit : ∑ i : Fin (D + 1), (delta0 i - Pstar.eval (i.val : ℚ)) * Q.eval (i.val : ℚ) =
        (∑ i : Fin (D + 1), delta0 i * Q.eval (i.val : ℚ)) -
        (∑ i : Fin (D + 1), Pstar.eval (i.val : ℚ) * Q.eval (i.val : ℚ)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hsplit]
    have h1 : (∑ i : Fin (D + 1), delta0 i * Q.eval (i.val : ℚ)) = Q.eval 0 := by
      rw [Finset.sum_eq_single (0 : Fin (D + 1))]
      · simp [delta0]
      · intro i _ hi
        simp [delta0, hi]
      · intro h; exact absurd (Finset.mem_univ _) h
    have h2 : (∑ i : Fin (D + 1), Pstar.eval (i.val : ℚ) * Q.eval (i.val : ℚ)) = Q.eval 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => Pstar.eval (i : ℚ) * Q.eval (i : ℚ))]
      have hfac : ∑ i ∈ Finset.range (D + 1), Pstar.eval (i : ℚ) * Q.eval (i : ℚ) =
          C0⁻¹ * ∑ i ∈ Finset.range (D + 1), (delta^[d + 1] (G D d)).eval (i : ℚ) * Q.eval (i : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pstar, eval_mul, eval_C]
        ring
      rw [hfac, H_orth D d Q hQ]
      change C0⁻¹ * (C0 * Q.eval 0) = Q.eval 0
      field_simp [hC0_ne]
    rw [h1, h2, sub_self]
  refine ⟨w, ?_, ?_⟩
  · have hloss : loss w = 1 - Pstar.eval 0 := by
      have h0 := horth_poly Pstar hPstar_deg
      have hexp : loss w = (∑ i : Fin (D + 1), (delta0 i - Pstar.eval (i.val : ℚ)) * delta0 i) -
          (∑ i : Fin (D + 1), (delta0 i - Pstar.eval (i.val : ℚ)) * Pstar.eval (i.val : ℚ)) := by
        simp only [loss, hw_eval]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hexp, h0, sub_zero]
      rw [Finset.sum_eq_single (0 : Fin (D + 1))]
      · simp [delta0]
      · intro i _ hi
        simp [delta0, hi]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hloss]
    have hP0 : Pstar.eval 0 = 1 - (Nat.choose D (d + 1) : ℚ) / (Nat.choose (D + d + 1) (d + 1) : ℚ) := by
      simp only [Pstar, eval_mul, eval_C]
      rw [delta_succ_G_zero D d hdD]
      have hfac_ne : (-1 : ℚ) ^ d * (d.factorial : ℚ) * ((d + 1).factorial : ℚ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero (pow_ne_zero d (by norm_num))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)))
          (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (d + 1)))
      have hch_ne : (Nat.choose (D + d + 1) (d + 1) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (by omega)))
      dsimp only [C0]
      field_simp [hfac_ne, hch_ne]
    rw [hP0]
    ring
  · intro v
    obtain ⟨Qv, hQv_deg, hQv_eval⟩ := fin_sum_eq_poly_eval d v
    have hv_eval : ∀ x : ℚ, eval v x = Qv.eval x := hQv_eval
    have hdiff_deg : (Qv - Pstar).natDegree ≤ d :=
      (natDegree_sub_le Qv Pstar).trans (max_le hQv_deg hPstar_deg)
    have horth := horth_poly (Qv - Pstar) hdiff_deg
    have hexp : loss v = loss w +
        (∑ i : Fin (D + 1), (eval v (i.val : ℚ) - eval w (i.val : ℚ)) ^ 2) -
        2 * (∑ i : Fin (D + 1), (delta0 i - Pstar.eval (i.val : ℚ)) * (Qv - Pstar).eval (i.val : ℚ)) := by
      simp only [loss, hw_eval, hv_eval, eval_sub]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hexp, horth, mul_zero, sub_zero]

end PEqualNP.Outside.L_lib_854

theorem PEqualNP.Outside.L_lib_854 : (∀ (D d : ℕ), d ≤ D →
  let eval := fun (w : Fin (d+1) → ℚ) (x : ℚ) => ∑ j, w j * x^j.val
  let delta := fun (i : Fin (D+1)) => if i.val = 0 then (1 : ℚ) else 0
  let loss := fun w => ∑ i : Fin (D+1), (delta i - eval w (i.val : ℚ))^2
  ∃ w : Fin (d+1) → ℚ,
    loss w = (Nat.choose D (d+1) : ℚ) / (Nat.choose (D+d+1) (d+1) : ℚ) ∧
    ∀ v : Fin (d+1) → ℚ,
      loss v = loss w + ∑ i : Fin (D+1), (eval v (i.val : ℚ) - eval w (i.val : ℚ))^2) :=
  PEqualNP.Outside.L_lib_854.main
