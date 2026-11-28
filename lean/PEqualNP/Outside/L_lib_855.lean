import Mathlib

open scoped BigOperators Polynomial
open Polynomial

namespace PEqualNP.Outside.L_lib_855

private noncomputable def grid (D d : ℕ) : ℤ[X] :=
  (∏ a ∈ Finset.range d, (C ((a : ℤ) + 1) - X)) *
    ∏ b ∈ Finset.range (d + 1), (C ((D : ℤ) + (b : ℤ) + 1) - X)

private noncomputable def step (p : ℤ[X]) : ℤ[X] := p - p.comp (X + C 1)

private noncomputable def diff (k : ℕ) (p : ℤ[X]) : ℤ[X] := (step^[k]) p

private lemma grid_factor_degree (r : ℤ) : (C r - X).natDegree = 1 := by
  rw [natDegree_sub, natDegree_X_sub_C]

private lemma grid_factor_prod_degree_le (n : ℕ) (f : ℕ → ℤ) :
    (∏ a ∈ Finset.range n, (C (f a) - X)).natDegree ≤ n := by
  refine (natDegree_prod_le (Finset.range n) (fun a => C (f a) - X)).trans ?_
  calc
    _ ≤ ∑ _a ∈ Finset.range n, 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact (grid_factor_degree (f a)).le
    _ = n := by simp

private lemma grid_natDegree_le (D d : ℕ) : (grid D d).natDegree ≤ 2 * d + 1 := by
  have h₁ := grid_factor_prod_degree_le d (fun a => (a : ℤ) + 1)
  have h₂ := grid_factor_prod_degree_le (d + 1) (fun b => (D : ℤ) + (b : ℤ) + 1)
  unfold grid
  exact natDegree_mul_le.trans (by omega)

private lemma step_eval (p : ℤ[X]) (x : ℤ) :
    (step p).eval x = p.eval x - p.eval (x + 1) := by
  simp [step, eval_sub, eval_comp]

private lemma step_natDegree_le (p : ℤ[X]) : (step p).natDegree ≤ p.natDegree - 1 := by
  have hdeg : (X + C (1 : ℤ)).natDegree = 1 := natDegree_X_add_C _
  have hlead : (X + C (1 : ℤ)).leadingCoeff = 1 := leadingCoeff_X_add_C _
  have hcomp : (p.comp (X + C 1)).natDegree ≤ p.natDegree := by
    calc
      _ ≤ p.natDegree * (X + C (1 : ℤ)).natDegree := natDegree_comp_le
      _ = _ := by rw [hdeg, mul_one]
  have hcoeff : (p.comp (X + C 1)).coeff p.natDegree = p.leadingCoeff := by
    simpa only [hdeg, mul_one, hlead, one_pow] using
      (coeff_comp_degree_mul_degree (p := p) (q := X + C 1) (hdeg.trans_ne one_ne_zero))
  apply natDegree_le_pred
  · exact (natDegree_sub_le _ _).trans (max_le le_rfl hcomp)
  · simp only [step, coeff_sub, coeff_natDegree, hcoeff, sub_self]

private lemma step_degree_lt {p : ℤ[X]} {k : ℕ} (hk : 0 < k) (hp : p.natDegree ≤ k) :
    (step p).natDegree < k := by
  have h := step_natDegree_le p
  omega

private lemma diff_succ (k : ℕ) (p : ℤ[X]) : diff (k + 1) p = step (diff k p) :=
  Function.iterate_succ_apply' step k p

private lemma diff_natDegree_le (k : ℕ) (p : ℤ[X]) :
    (diff k p).natDegree ≤ p.natDegree - k := by
  induction k with
  | zero => simp [diff]
  | succ k ih =>
    rw [diff_succ]
    have h := step_natDegree_le (diff k p)
    omega

private lemma grid_diff_natDegree_le (D d : ℕ) :
    (diff (d + 1) (grid D d)).natDegree ≤ d := by
  have h₁ := diff_natDegree_le (d + 1) (grid D d)
  have h₂ := grid_natDegree_le D d
  omega

private noncomputable def gridShift (x : ℤ) (p : ℤ[X]) : ℤ[X] := p.comp (X + C x)

private lemma gridShift_step (x : ℤ) (p : ℤ[X]) :
    gridShift x (step p) = gridShift x p - gridShift (x + 1) p := by
  simp only [gridShift, step, sub_comp, comp_assoc, add_comp, X_comp, C_comp, add_assoc, ← map_add]

private lemma grid_factor_comp (r x : ℤ) :
    (C r - X).comp (X + C x) = C (r - x) - X := by
  rw [sub_comp, C_comp, X_comp, sub_add_eq_sub_sub, sub_right_comm, map_sub]

private lemma gridShift_grid (D d : ℕ) (x : ℤ) :
    gridShift x (grid D d) =
      (∏ a ∈ Finset.range d, (C ((a : ℤ) + 1 - x) - X)) *
        ∏ b ∈ Finset.range (d + 1), (C ((D : ℤ) + (b : ℤ) + 1 - x) - X) := by
  simp only [gridShift, grid, mul_comp, prod_comp, grid_factor_comp]

private lemma coeff_grid_factor_mul_bound (r A B : ℤ) (p : ℤ[X])
    (hr : |r| + 1 ≤ B) (hp : ∀ j, |p.coeff j| ≤ A) (j : ℕ) :
    |((C r - X) * p).coeff j| ≤ A * B := by
  have hA : 0 ≤ A := (abs_nonneg (p.coeff 0)).trans (hp 0)
  have hX : |(X * p).coeff j| ≤ A := by
    cases j with
    | zero =>
      have hx : (X * p).coeff 0 = 0 := coeff_X_mul_zero p
      rw [hx, abs_zero]
      exact hA
    | succ n =>
      have hx : (X * p).coeff (n + 1) = p.coeff n := coeff_X_mul p n
      rw [hx]
      exact hp n
  have hC : |(C r * p).coeff j| ≤ |r| * A := by
    calc
      _ = |r * p.coeff j| := congrArg (abs : ℤ → ℤ) (coeff_C_mul (a := r) (n := j) p)
      _ = |r| * |p.coeff j| := abs_mul r _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hp j) (abs_nonneg r)
  have hs : ((C r - X) * p).coeff j = (C r * p).coeff j - (X * p).coeff j := by
    rw [sub_mul, coeff_sub]
  calc
    _ = |(C r * p).coeff j - (X * p).coeff j| := congrArg (abs : ℤ → ℤ) hs
    _ ≤ |(C r * p).coeff j| + |(X * p).coeff j| := abs_sub _ _
    _ ≤ |r| * A + A := add_le_add hC hX
    _ = A * (|r| + 1) := by rw [mul_add, mul_one, mul_comm A |r|]
    _ ≤ A * B := mul_le_mul_of_nonneg_left hr hA

private lemma coeff_grid_factor_prod_mul_bound (f : ℕ → ℤ) (n : ℕ) (A B : ℤ) (p : ℤ[X])
    (hf : ∀ a < n, |f a| + 1 ≤ B) (hp : ∀ j, |p.coeff j| ≤ A) (j : ℕ) :
    |(((∏ a ∈ Finset.range n, (C (f a) - X)) * p).coeff j)| ≤ A * B ^ n := by
  induction n generalizing j with
  | zero => simpa using hp j
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_assoc, mul_left_comm, pow_succ,
      ← mul_assoc A (B ^ n) B]
    exact coeff_grid_factor_mul_bound _ _ _ _ (hf n (by omega))
      (fun i => ih (fun a ha => hf a (by omega)) i) j

private lemma gridShift_grid_coeff_bound {D d s : ℕ} (hd : d ≤ D) (hs : s ≤ d + 1) (j : ℕ) :
    |(gridShift (s : ℤ) (grid D d)).coeff j| ≤ (2 * ((D : ℤ) + 2)) ^ (2 * d + 1) := by
  let B : ℤ := 2 * ((D : ℤ) + 2)
  let f : ℕ → ℤ := fun a => (a : ℤ) + 1 - s
  let g : ℕ → ℤ := fun b => (D : ℤ) + (b : ℤ) + 1 - s
  have hf : ∀ a < d, |f a| + 1 ≤ B := by
    intro a ha
    apply le_sub_iff_add_le.mp
    exact abs_le.mpr ⟨by dsimp [B, f]; omega, by dsimp [B, f]; omega⟩
  have hg : ∀ b < d + 1, |g b| + 1 ≤ B := by
    intro b hb
    apply le_sub_iff_add_le.mp
    exact abs_le.mpr ⟨by dsimp [B, g]; omega, by dsimp [B, g]; omega⟩
  have hone (i : ℕ) : |(1 : ℤ[X]).coeff i| ≤ (1 : ℤ) := by
    by_cases hi : i = 0 <;> simp [coeff_one, hi]
  let q : ℤ[X] := ∏ b ∈ Finset.range (d + 1), (C (g b) - X)
  have hq (i : ℕ) : |q.coeff i| ≤ B ^ (d + 1) := by
    simpa only [q, mul_one, one_mul] using
      coeff_grid_factor_prod_mul_bound g (d + 1) 1 B 1 hg hone i
  rw [gridShift_grid]
  change |(((∏ a ∈ Finset.range d, (C (f a) - X)) * q).coeff j)| ≤ B ^ (2 * d + 1)
  rw [show 2 * d + 1 = (d + 1) + d by omega, pow_add]
  exact coeff_grid_factor_prod_mul_bound f d _ B q hf hq j

-- At each step the translated coefficient is a difference of two coefficients at neighboring shifts.
private lemma gridShift_diff_coeff_bound {D d : ℕ} (hd : d ≤ D) (j k s : ℕ)
    (hks : s + k ≤ d + 1) :
    |(gridShift (s : ℤ) (diff k (grid D d))).coeff j| ≤
      (2 * ((D : ℤ) + 2)) ^ (2 * d + 1 + k) := by
  let B : ℤ := 2 * ((D : ℤ) + 2)
  have hB : 2 ≤ B := by dsimp [B]; omega
  change _ ≤ B ^ (2 * d + 1 + k)
  induction k generalizing s with
  | zero => simpa [diff] using gridShift_grid_coeff_bound hd (by omega : s ≤ d + 1) j
  | succ k ih =>
    have h₀ := ih s (by omega)
    have h₁ := ih (s + 1) (by omega)
    push_cast at h₁
    rw [diff_succ, gridShift_step, coeff_sub, ← add_assoc, pow_succ]
    refine (abs_sub _ _).trans ((add_le_add h₀ h₁).trans ?_)
    rw [← mul_two]
    exact mul_le_mul_of_nonneg_left hB (pow_nonneg (by omega) _)

private lemma grid_diff_coeff_bound {D d : ℕ} (hd : d ≤ D) (j : ℕ) :
    |(diff (d + 1) (grid D d)).coeff j| ≤ (2 * ((D : ℤ) + 2)) ^ (3 * (d + 1)) := by
  have h := gridShift_diff_coeff_bound hd j (d + 1) 0 (by omega)
  simp [gridShift] at h
  exact h.trans (pow_le_pow_right₀ (by omega) (by omega))





private def sd : ℕ → (ℕ → ℤ) → ℕ → ℤ
  | 0, g => g
  | k+1, g => fun i => sd k g i - sd k g (i+1)

private lemma sd_shift (k : ℕ) (g : ℕ → ℤ) (i : ℕ) :
    sd k (fun j => g (j+1)) i = sd k g (i+1) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp only [sd, ih]

private lemma sd_congr {k i : ℕ} {g h : ℕ → ℤ}
    (he : ∀ j, i ≤ j → j ≤ i+k → g j = h j) : sd k g i = sd k h i := by
  induction k generalizing i with
  | zero => exact he i le_rfl (by omega)
  | succ k ih =>
    simp only [sd]
    rw [ih (fun j hj hj' => he j hj (by omega)),
      ih (fun j hj hj' => he j (by omega) (by omega))]

private lemma sd_eq_last {k i : ℕ} {g : ℕ → ℤ}
    (hz : ∀ j, i ≤ j → j < i+k → g j = 0) :
    sd k g i = (-1 : ℤ)^k * g (i+k) := by
  induction k generalizing i with
  | zero => simp [sd]
  | succ k ih =>
    simp only [sd]
    have h0 : sd k g i = 0 := by
      rw [ih (fun j hj hj' => hz j hj (by omega)), hz (i+k) (by omega) (by omega), mul_zero]
    rw [h0, ih (fun j hj hj' => hz j (by omega) (by omega)), pow_succ,
      show i+1+k = i+(k+1) by omega]
    ring

private lemma sd_zero {k i : ℕ} {g : ℕ → ℤ}
    (hz : ∀ j, i ≤ j → j ≤ i+k → g j = 0) : sd k g i = 0 := by
  rw [sd_eq_last (fun j hj hj' => hz j hj (by omega)), hz (i+k) (by omega) le_rfl, mul_zero]

private lemma sd_add (k : ℕ) (g h : ℕ → ℤ) (i : ℕ) :
    sd k (fun j => g j + h j) i = sd k g i + sd k h i := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp only [sd, ih]; ring

private lemma sd_delta (k i : ℕ) (A : ℤ) :
    sd k (fun j => if j = 0 then A else 0) i = if i = 0 then A else 0 := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih => simp [sd, ih]

private lemma sd_eval (k : ℕ) (p : ℤ[X]) (i : ℕ) :
    sd k (fun j => p.eval (j : ℤ)) i = (diff k p).eval (i : ℤ) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    rw [show diff (k+1) p = step (diff k p) by simp [diff, Function.iterate_succ_apply']]
    simp [sd, ih, step, Polynomial.eval_comp]

private lemma sd_parts (n : ℕ) (g : ℕ → ℤ) (p : ℤ[X])
    (hg0 : g 0 = 0) (hgn : g n = 0) :
    (∑ i ∈ Finset.range n, (g i - g (i+1)) * p.eval (i : ℤ)) =
      -(∑ i ∈ Finset.range n, g (i+1) * (step p).eval (i : ℤ)) := by
  simp only [step, Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, ← Nat.cast_succ, sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hshift := Finset.sum_range_succ' (f := fun i => g i * p.eval (i : ℤ)) n
  rw [Finset.sum_range_succ] at hshift
  simp only [hg0, hgn, zero_mul, add_zero] at hshift
  rw [hshift]
  ring

private lemma sd_orthogonal (k n : ℕ) (g : ℕ → ℤ) (p : ℤ[X])
    (hl : ∀ i < k, g i = 0) (hr : ∀ i ≥ n, g i = 0)
    (hp : p = 0 ∨ p.natDegree < k) :
    (∑ i ∈ Finset.range n, sd k g i * p.eval (i : ℤ)) = 0 := by
  induction k generalizing g p with
  | zero => rcases hp with rfl | hp
            · simp
            · omega
  | succ k ih =>
    rcases hp with rfl | hp
    · simp
    simp only [sd]
    rw [sd_parts n (sd k g) p]
    · simp_rw [← sd_shift]
      rw [ih (fun i => g (i+1)) (step p)]
      · simp
      · intro i hi; exact hl _ (by omega)
      · intro i hi; exact hr _ (by omega)
      · by_cases hk : 0 < k
        · exact Or.inr (step_degree_lt hk (by omega))
        · have hdeg : p.natDegree = 0 := by omega
          left
          conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
          simp [step]
    · exact sd_zero (fun j _ hj => hl j (by omega))
    · exact sd_zero (fun j hj _ => hr j hj)

private noncomputable def boundedGrid (D d : ℕ) (i : ℕ) : ℤ :=
  if i ≤ D ∧ i ≠ 0 then (grid D d).eval (i : ℤ) else 0

private lemma grid_left_root {D d i : ℕ} (hi : 0 < i) (hi' : i ≤ d) :
    (grid D d).eval (i : ℤ) = 0 := by
  simp only [grid, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  have hzero : (∏ x ∈ Finset.range d, ((x:ℤ)+1-(i:ℤ))) = 0 := by
    apply Finset.prod_eq_zero (i := i-1) (Finset.mem_range.mpr (by omega))
    have hh : i-1+1 = i := by omega
    exact sub_eq_zero.mpr (by exact_mod_cast hh)
  rw [hzero, zero_mul]

private lemma grid_right_root {D d i : ℕ} (hi : D < i) (hi' : i ≤ D+(d+1)) :
    (grid D d).eval (i : ℤ) = 0 := by
  simp only [grid, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  have hzero : (∏ x ∈ Finset.range (d+1), ((D:ℤ)+(x:ℤ)+1-(i:ℤ))) = 0 := by
    apply Finset.prod_eq_zero (i := i-D-1) (Finset.mem_range.mpr (by omega))
    have hh : D+(i-D-1)+1 = i := by omega
    exact sub_eq_zero.mpr (by exact_mod_cast hh)
  rw [hzero, mul_zero]

private lemma boundedGrid_left {D d i : ℕ} (hi : i < d+1) : boundedGrid D d i = 0 := by
  unfold boundedGrid
  split
  · rename_i h; exact grid_left_root (by omega) (by omega)
  · rfl

private lemma boundedGrid_decomp {D d i : ℕ} (hi : i ≤ D+(d+1)) :
    boundedGrid D d i + (if i = 0 then (grid D d).eval 0 else 0) =
      (grid D d).eval (i : ℤ) := by
  by_cases h0 : i = 0
  · subst i; simp [boundedGrid]
  by_cases hD : i ≤ D
  · simp [boundedGrid, hD, h0]
  · simp [boundedGrid, hD, h0, grid_right_root (by omega : D < i) hi]

private lemma residual_eq {D d i : ℕ} (hi : i ≤ D) :
    -(sd (d+1) (boundedGrid D d) i) =
      (if i = 0 then (grid D d).eval 0 else 0) - (diff (d+1) (grid D d)).eval (i : ℤ) := by
  have h := sd_congr (k := d+1) (i := i)
    (g := fun j => boundedGrid D d j + (if j = 0 then (grid D d).eval 0 else 0))
    (h := fun j => (grid D d).eval (j : ℤ))
    (fun j _ hj => boundedGrid_decomp (by omega))
  rw [sd_add, sd_delta, sd_eval] at h
  omega

private lemma residual_head (D d : ℕ) :
    -(sd (d+1) (boundedGrid D d) 0) = (-1 : ℤ)^d * (grid D d).eval ((d+1 : ℕ) : ℤ) := by
  rw [sd_eq_last (fun j _ hj => boundedGrid_left (by simpa using hj)), zero_add, pow_succ]
  by_cases h : d+1 ≤ D
  · simp [boundedGrid, h]
  · rw [grid_right_root (by omega : D < d+1) (by omega)]
    simp [boundedGrid, h]





private lemma grid_at_zero (D d : ℕ) :
    (grid D d).eval 0 = (d.factorial : ℤ) * ((d+1).factorial : ℤ) * ((D+d+1).choose (d+1) : ℤ) := by
  simp only [grid, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, sub_zero]
  have hl : (∏ x ∈ Finset.range d, ((x:ℤ)+1)) = (d.factorial : ℤ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial d
  have hr : (∏ x ∈ Finset.range (d+1), ((D:ℤ)+(x:ℤ)+1)) =
      ((d+1).factorial : ℤ) * ((D+d+1).choose (d+1) : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
      Nat.cast_prod]
    rw [← Finset.prod_range_reflect (fun x => (D:ℤ)+(x:ℤ)+1)]
    apply Finset.prod_congr rfl
    intro x hx
    have h := Finset.mem_range.mp hx
    simp only [Nat.add_sub_cancel]
    rw [Nat.cast_sub (by omega : x ≤ d), Nat.cast_sub (by omega : x ≤ D+d+1)]
    push_cast
    ring
  rw [hl, hr]
  ring

private lemma grid_at_end (D d : ℕ) (hd : d ≤ D) :
    (-1 : ℤ)^d * (grid D d).eval ((d+1 : ℕ) : ℤ) =
      (d.factorial : ℤ) * ((d+1).factorial : ℤ) * (D.choose (d+1) : ℤ) := by
  simp only [grid, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X]
  have hl : (∏ x ∈ Finset.range d, ((x:ℤ)+1-((d+1 : ℕ):ℤ))) =
      (-1 : ℤ)^d * (d.factorial : ℤ) := by
    have he : (∏ x ∈ Finset.range d, ((x:ℤ)+1-((d+1 : ℕ):ℤ))) =
        ∏ x ∈ Finset.range d, ((-1 : ℤ) * ((d-x : ℕ):ℤ)) := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hx))]
      push_cast
      ring
    rw [he, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
      ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose,
      Nat.choose_self, mul_one]
  have hr : (∏ x ∈ Finset.range (d+1), ((D:ℤ)+(x:ℤ)+1-((d+1 : ℕ):ℤ))) =
      ((d+1).factorial : ℤ) * (D.choose (d+1) : ℤ) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range,
      Nat.cast_prod]
    rw [← Finset.prod_range_reflect (fun x => (D:ℤ)+(x:ℤ)+1-((d+1 : ℕ):ℤ))]
    apply Finset.prod_congr rfl
    intro x hx
    have h := Finset.mem_range.mp hx
    simp only [Nat.add_sub_cancel]
    rw [Nat.cast_sub (by omega : x ≤ d), Nat.cast_sub (by omega : x ≤ D)]
    push_cast
    ring
  rw [hl, hr]
  have hsgn : (-1 : ℤ)^d * (-1)^d = 1 := by
    rw [← mul_pow]; norm_num
  calc
    (-1 : ℤ)^d * ((-1)^d * (d.factorial : ℤ) * (((d+1).factorial : ℤ) * (D.choose (d+1) : ℤ))) =
        ((-1 : ℤ)^d * (-1)^d) * ((d.factorial : ℤ) * ((d+1).factorial : ℤ) * (D.choose (d+1) : ℤ)) := by ring
    _ = _ := by rw [hsgn, one_mul]

private lemma grid_den_bound (D d : ℕ) (hd : d ≤ D) :
    (grid D d).eval 0 ≤ (2*((D:ℤ)+2))^(2*d+1) := by
  simp only [grid, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X, sub_zero]
  let B : ℤ := 2*((D:ℤ)+2)
  change (∏ i ∈ Finset.range d, ((i:ℤ)+1)) * (∏ i ∈ Finset.range (d+1), ((D:ℤ)+(i:ℤ)+1)) ≤ B^(2*d+1)
  have hl : (∏ i ∈ Finset.range d, ((i:ℤ)+1)) ≤ B^d := by
    rw [show B^d = ∏ _ ∈ Finset.range d, B by simp]
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    · intro i hi
      have h : i < d := Finset.mem_range.mp hi
      have h' : (i:ℤ) ≤ D := by exact_mod_cast (by omega : i ≤ D)
      dsimp [B]; omega
  have hr : (∏ i ∈ Finset.range (d+1), ((D:ℤ)+(i:ℤ)+1)) ≤ B^(d+1) := by
    rw [show B^(d+1) = ∏ _ ∈ Finset.range (d+1), B by simp]
    apply Finset.prod_le_prod₀
    · intro i hi; positivity
    · intro i hi
      have h : i < d+1 := Finset.mem_range.mp hi
      have h' : (i:ℤ) ≤ D := by exact_mod_cast (by omega : i ≤ D)
      dsimp [B]; omega
  calc
    _ ≤ B^d * B^(d+1) := mul_le_mul hl hr (by positivity) (by dsimp [B]; positivity)
    _ = _ := by rw [← pow_add, show d+(d+1) = 2*d+1 by omega]





private lemma square_sum_center {I : Type*} [Fintype I] [Nonempty I]
    (r : I → ℤ) (A P : ℤ) (hA : 0 < A) (hP : 0 ≤ P)
    (hmax : (∑ i, (r i)^2) ≤ A^2) (hsharp : 2*P^2*(∑ i, (r i)^2) < A^2) :
    ∃ c : ℤ, |c| ≤ 2*A ∧ ∀ i, |2*r i-c| * (2*P) < 2*A := by
  classical
  obtain ⟨lo, -, hlo⟩ := Finset.exists_min_image Finset.univ r Finset.univ_nonempty
  obtain ⟨hi, -, hhi⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hsingle (i : I) : (r i)^2 ≤ ∑ j, (r j)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (r j)) (Finset.mem_univ i)
  refine ⟨r lo + r hi, ?_, ?_⟩
  · calc
      |r lo+r hi| ≤ |r lo| + |r hi| := abs_add_le _ _
      _ ≤ 2*A := by
        have h₁ := abs_le_of_sq_le_sq ((hsingle lo).trans hmax) hA.le
        have h₂ := abs_le_of_sq_le_sq ((hsingle hi).trans hmax) hA.le
        linarith
  · intro i
    have hdist : |2*r i-(r lo+r hi)| ≤ r hi-r lo := by
      apply abs_le.mpr
      have h₁ := hlo i (Finset.mem_univ i)
      have h₂ := hhi i (Finset.mem_univ i)
      constructor <;> linarith
    have hdist0 : 0 ≤ r hi-r lo := sub_nonneg.mpr (hlo hi (Finset.mem_univ hi))
    have hpair : (r hi-r lo)^2 ≤ 2*(∑ j, (r j)^2) := by
      by_cases he : hi = lo
      · rw [he, sub_self, zero_pow (by decide : 2 ≠ 0)]
        positivity
      · have hsum : (r hi)^2 + (r lo)^2 ≤ ∑ j, (r j)^2 := by
          rw [← Finset.sum_pair he (f := fun j => (r j)^2)]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => sq_nonneg (r j))
        nlinarith [sq_nonneg (r hi+r lo)]
    apply (mul_le_mul_of_nonneg_right hdist (by omega : 0 ≤ 2*P)).trans_lt
    apply (sq_lt_sq₀ (mul_nonneg hdist0 (by omega)) (by omega)).mp
    calc
      ((r hi-r lo)*(2*P))^2 = (r hi-r lo)^2 * (2*P)^2 := by ring
      _ ≤ (2*(∑ j, (r j)^2))*(2*P)^2 := mul_le_mul_of_nonneg_right hpair (sq_nonneg _)
      _ = 4*(2*P^2*(∑ j, (r j)^2)) := by ring
      _ < 4*A^2 := mul_lt_mul_of_pos_left hsharp (by decide)
      _ = (2*A)^2 := by ring

private lemma center_square_data {I : Type*} [Fintype I]
    (r : I → ℤ) (o : I) (A Csmall Cbig P : ℤ) (hA : 0 < A) (hbig : 0 < Cbig)
    (horth : (∑ i, (r i)^2) = A*r o) (hquot : r o*Cbig = A*Csmall)
    (hchoose : 2*P^2*Csmall < Cbig) :
    (∑ i, (r i)^2) ≤ A^2 ∧ 2*P^2*(∑ i, (r i)^2) < A^2 := by
  classical
  have hsingle : (r o)^2 ≤ ∑ i, (r i)^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (r j)) (Finset.mem_univ o)
  rw [horth] at hsingle ⊢
  constructor
  · have hle : r o ≤ A := by
      by_contra! h
      have hp : 0 < r o := hA.trans h
      have hc := mul_lt_mul_of_pos_left h hp
      nlinarith
    simpa [pow_two] using mul_le_mul_of_nonneg_left hle hA.le
  · have hs : 2*P^2*r o < A := by
      apply lt_of_mul_lt_mul_right _ hbig.le
      calc
        (2*P^2*r o)*Cbig = A*(2*P^2*Csmall) := by
          calc
            _ = 2*P^2*(r o*Cbig) := by ring
            _ = _ := by rw [hquot]; ring
        _ < A*Cbig := mul_lt_mul_of_pos_left hchoose hA
    calc
      2*P^2*(A*r o) = A*(2*P^2*r o) := by ring
      _ < A*A := mul_lt_mul_of_pos_left hs hA
      _ = A^2 := by ring




-- The factorial recurrences expose the successive numerator and denominator factors.
private lemma factorial_ratio_bound (D k : ℕ) (hk : k ≤ D + 1) :
    (D.descFactorial k : ℝ) ≤
      Real.exp (- (k : ℝ)^2 / (2 * D + 1)) * ((D + 1).ascFactorial k : ℝ) := by
  induction k with
  | zero => simp
  | succ j ih =>
      have hj : j ≤ D := by omega
      have hjR : (j : ℝ) ≤ D := by exact_mod_cast hj
      have hM : (0 : ℝ) < 2 * D + 1 := by positivity
      have hden : (0 : ℝ) < (D : ℝ) + 1 + j := by positivity
      have hu : (0 : ℝ) ≤ 2 * j + 1 := by positivity
      have hstep : (D : ℝ) - j ≤
          Real.exp (-(2 * (j : ℝ) + 1) / (2 * D + 1)) * (D + 1 + j) := by
        have hfrac : (2 * (j : ℝ) + 1) / (2 * D + 1) ≤
            (2 * (j : ℝ) + 1) / (D + 1 + j) :=
          div_le_div_of_nonneg_left hu hden (by linarith)
        have he := Real.add_one_le_exp (-(2 * (j : ℝ) + 1) / (2 * D + 1))
        apply (div_le_iff₀ hden).mp
        calc
          ((D : ℝ) - j) / (D + 1 + j) = 1 - (2 * (j : ℝ) + 1) / (D + 1 + j) := by
            field_simp
            ring
          _ ≤ Real.exp (-(2 * (j : ℝ) + 1) / (2 * D + 1)) := by
            rw [neg_div] at he ⊢
            linarith
      rw [Nat.descFactorial_succ, Nat.ascFactorial_succ]
      push_cast [Nat.cast_sub hj]
      calc
        ((D : ℝ) - j) * (D.descFactorial j : ℝ) ≤
            (Real.exp (-(2 * (j : ℝ) + 1) / (2 * D + 1)) * (D + 1 + j)) *
              (Real.exp (-(j : ℝ)^2 / (2 * D + 1)) * ((D + 1).ascFactorial j : ℝ)) :=
          mul_le_mul hstep (ih (by omega)) (by positivity)
            (mul_nonneg (Real.exp_pos _).le hden.le)
        _ = _ := by
          rw [mul_mul_mul_comm, ← Real.exp_add]
          congr 2
          rw [← add_div]
          congr 1
          ring

private lemma choose_target (D d P : ℕ) (hd : d ≤ D)
    (h : 2*P^2*Nat.choose D (d+1) < Nat.choose (D+d+1) (d+1) ∨
      ∃ b : ℕ, P ≤ 2^b ∧ (2*D+1)*(2*b+2) ≤ (d+1)^2) :
    2*P^2*Nat.choose D (d+1) < Nat.choose (D+d+1) (d+1) := by
  rcases h with h | ⟨b, hP, hb⟩
  · exact h
  let k := d + 1
  change 2*P^2*Nat.choose D k < Nat.choose (D+d+1) k
  rw [show D + d + 1 = D + k by omega]
  have hratio := factorial_ratio_bound D k (by dsimp [k]; omega)
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_factorial_mul_choose] at hratio
  push_cast at hratio
  rw [mul_left_comm (Real.exp _) (k.factorial : ℝ)] at hratio
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hchoose := (mul_le_mul_iff_right₀ hfac).mp hratio
  have hbR : (2 * (D : ℝ) + 1) * (2 * (b : ℝ) + 2) ≤ (k : ℝ)^2 := by
    exact_mod_cast hb
  have hearg : (↑(2*b+2) : ℝ) * 1 ≤ (k : ℝ)^2 / (2 * D + 1) := by
    apply (le_div_iff₀ (by positivity)).mpr
    push_cast
    nlinarith
  have he : (2 : ℝ)^(2*b+2) < Real.exp ((k : ℝ)^2 / (2 * D + 1)) :=
    (pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by omega)).trans_le
      (by rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr hearg)
  have hPR : (P : ℝ) ≤ (2 : ℝ)^b := by exact_mod_cast hP
  have hweight : 2 * (P : ℝ)^2 < Real.exp ((k : ℝ)^2 / (2 * D + 1)) := by
    apply lt_of_le_of_lt _ he
    calc
      2 * (P : ℝ)^2 ≤ 2 * ((2 : ℝ)^b)^2 := by gcongr
      _ ≤ (2 : ℝ)^(2*b+2) := by
        rw [pow_add, mul_comm 2 b, pow_mul]
        norm_num
        nlinarith [sq_nonneg ((2 : ℝ)^b)]
  have hweight' : 2 * (P : ℝ)^2 * Real.exp (-(k : ℝ)^2 / (2 * D + 1)) < 1 := by
    rw [neg_div, Real.exp_neg]
    exact (mul_inv_lt_iff₀ (Real.exp_pos _)).mpr (by simpa using hweight)
  have hpos : (0 : ℝ) < ((D + k).choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left k D)
  exact_mod_cast (calc
    2 * (P : ℝ)^2 * (D.choose k : ℝ) ≤
        2 * (P : ℝ)^2 * (Real.exp (-(k : ℝ)^2 / (2 * D + 1)) * ((D + k).choose k : ℝ)) :=
      mul_le_mul_of_nonneg_left hchoose (by positivity)
    _ < ((D + k).choose k : ℝ) := by
      rw [← mul_assoc]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hweight' hpos)





private lemma recovery_binomial (d : ℕ) (j : Fin (d + 1)) (x y : ℤ) :
    (x + y)^j.val = ∑ l : Fin (d + 1), (Nat.choose j.val l.val : ℤ) *
      y^(j.val-l.val) * x^l.val := by
  rw [add_pow, Finset.sum_fin_eq_sum_range]
  let term := fun l : ℕ => (Nat.choose j.val l : ℤ) * y^(j.val-l) * x^l
  calc
    _ = ∑ l ∈ Finset.range (j.val + 1), term l := by
      apply Finset.sum_congr rfl
      intro l _
      dsimp [term]
      ring
    _ = ∑ l ∈ Finset.range (d + 1), term l := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro l _ hl
      have hlt : j.val < l := by simpa [Finset.mem_range] using hl
      simp [term, Nat.choose_eq_zero_of_lt hlt]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      simp only [dite_eq_left (Finset.mem_range.mp hl), term]

private lemma recovery_read (D d : ℕ) (w : Fin (d + 1) → ℤ)
    (f : Fin (D + 1) → ℕ) (s : ℕ) :
    (∑ j : Fin (d+1), w j *
      ∑ l : Fin (d+1), (Nat.choose j.val l.val : ℤ) *
        (-(s : ℤ))^(j.val-l.val) * (↑(∑ i : Fin (D+1), f i * i.val^l.val) : ℤ)) =
    ∑ i : Fin (D+1), (f i : ℤ) * ∑ j : Fin (d+1), w j * ((i.val : ℤ)-(s : ℤ))^j.val := by
  push_cast
  simp only [Finset.mul_sum]
  conv_lhs =>
    enter [2, j]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sub_eq_add_neg, recovery_binomial, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

private lemma recovery_weighted (D P den : ℕ) (poly : ℤ → ℤ) (hden : 0 < den)
    (herr : ∀ i : Fin (D+1), |(if i.val = 0 then (den : ℤ) else 0) - poly i.val| *
      (2 * (P : ℤ)) < den)
    (f : Fin (D+1) → ℕ) (hf : (∑ i, f i) ≤ P) (s : ℕ) (hs : s < D+1) :
    let z := ∑ i : Fin (D+1), if s ≤ i.val then (f i : ℤ) * poly ((i.val : ℤ)-(s : ℤ)) else 0
    (2*z+(den : ℤ))/(2*(den : ℤ)) = f ⟨s, hs⟩ := by
  dsimp only
  let z : ℤ := ∑ i : Fin (D+1),
    if s ≤ i.val then (f i : ℤ) * poly ((i.val : ℤ)-(s : ℤ)) else 0
  let a : ℤ := f ⟨s, hs⟩
  change (2*z+(den : ℤ))/(2*(den : ℤ)) = a
  let err := fun i : Fin (D+1) => |(if i.val = 0 then (den : ℤ) else 0) - poly i.val|
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ err
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hmax : 0 ≤ err k := abs_nonneg _
  let step := fun i : Fin (D+1) => if s ≤ i.val then
    (f i : ℤ) * ((if i.val = s then (den : ℤ) else 0) - poly ((i.val : ℤ)-(s : ℤ))) else 0
  have hdelta : (den : ℤ) * a = ∑ i : Fin (D+1), if i.val = s then (den : ℤ) * f i else 0 := by
    symm
    rw [Finset.sum_eq_single (⟨s, hs⟩ : Fin (D+1))]
    · simp [a]
    · intro i _ hi
      exact ite_eq_right (fun he => hi (Fin.ext he))
    · simp
  have herror : (den : ℤ) * a - z = ∑ i, step i := by
    rw [hdelta]
    unfold z
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : s ≤ i.val
    · simp only [step, ite_eq_left hi, mul_sub]
      split <;> ring
    · have hne : i.val ≠ s := by omega
      simp [step, hi, hne]
  have hstep (i : Fin (D+1)) : |step i| ≤ (f i : ℤ) * err k := by
    by_cases hi : s ≤ i.val
    · let t : Fin (D+1) := ⟨i.val-s, by have := i.isLt; omega⟩
      have ht : (t.val : ℤ) = (i.val : ℤ) - (s : ℤ) := Int.ofNat_sub hi
      have hzero : t.val = 0 ↔ i.val = s := by dsimp [t]; omega
      have he : |(if i.val = s then (den : ℤ) else 0) - poly ((i.val : ℤ)-(s : ℤ))| = err t := by
        unfold err
        simp only [ht, hzero]
      have hfi : 0 ≤ (f i : ℤ) := by positivity
      rw [show step i = _ from ite_eq_left hi, abs_mul, abs_of_nonneg hfi, he]
      exact mul_le_mul_of_nonneg_left (hk t (Finset.mem_univ _)) (by positivity)
    · simpa [step, hi] using mul_nonneg (show 0 ≤ (f i : ℤ) by positivity) hmax
  have hmass : (∑ i : Fin (D+1), (f i : ℤ)) ≤ (P : ℤ) := by exact_mod_cast hf
  have habs : |(den : ℤ) * a - z| ≤ (P : ℤ) * err k := by
    rw [herror]
    calc
      _ ≤ ∑ i, |step i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (f i : ℤ) * err k := Finset.sum_le_sum (fun i _ => hstep i)
      _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hmass hmax
  have hstrict : |2 * ((den : ℤ) * a - z)| < den := by
    rw [abs_mul, abs_of_nonneg (by decide : (0 : ℤ) ≤ 2)]
    calc
      _ ≤ 2 * ((P : ℤ) * err k) := mul_le_mul_of_nonneg_left habs (by decide)
      _ < _ := by
        convert herr k using 1
        ring
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hstrict
  have hpos : 0 < 2 * (den : ℤ) := by positivity
  apply le_antisymm
  · have hlt : (2*z+(den : ℤ))/(2*(den : ℤ)) < a + 1 :=
      (Int.ediv_lt_iff_lt_mul hpos).2 (by nlinarith)
    omega
  · exact (Int.le_ediv_iff_mul_le hpos).2 (by nlinarith)

private lemma recover_of_uniform (D d P den : ℕ) (w : Fin (d+1) → ℤ)
    (hden : 0 < den)
    (herr : ∀ i : Fin (D+1), |(if i.val = 0 then (den : ℤ) else 0) -
      ∑ j : Fin (d+1), w j * (i.val : ℤ)^j.val| * (2 * (P : ℤ)) < den) :
    ∀ (f : Fin (D+1) → ℕ), (∑ i, f i) ≤ P →
      let mom := fun (l : Fin (d+1)) => ∑ i : Fin (D+1), f i * i.val^l.val
      let poly := fun (x : ℤ) => ∑ j, w j * x^j.val
      let readAt := fun (s : ℕ) => ∑ j : Fin (d+1), w j *
        ∑ l : Fin (d+1), (Nat.choose j.val l.val : ℤ) *
          (-(s : ℤ))^(j.val-l.val) * (mom l : ℤ)
      let recovered := (List.range (D+1)).foldl (fun (xs : List ℤ) (s : ℕ) =>
        let old := ∑ i ∈ Finset.range s, xs.getD i 0 * poly ((i : ℤ)-(s : ℤ))
        let z := readAt s - old
        xs ++ [(2*z+(den : ℤ))/(2*(den : ℤ))]) []
      recovered = List.ofFn (fun i : Fin (D+1) => (f i : ℤ)) := by
  intro f hf mom poly readAt recovered
  let coeff (i : ℕ) : ℤ := if hi : i < D + 1 then (f ⟨i, hi⟩ : ℤ) else 0
  let update (xs : List ℤ) (s : ℕ) :=
    let old := ∑ i ∈ Finset.range s, xs.getD i 0 * poly ((i : ℤ)-(s : ℤ))
    let z := readAt s - old
    xs ++ [(2*z+(den : ℤ))/(2*(den : ℤ))]
  have hprefix (n : ℕ) (hn : n ≤ D+1) :
      (List.range n).foldl update [] = (List.range n).map coeff := by
    induction n with
    | zero => rfl
    | succ s ih =>
      have hs : s < D + 1 := by omega
      rw [List.range_succ, List.foldl_append, ih (by omega), List.map_append]
      simp only [List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil]
      unfold update
      dsimp only
      congr 2
      have hold : (∑ i ∈ Finset.range s, ((List.range s).map coeff).getD i 0 *
          poly ((i : ℤ)-(s : ℤ))) = ∑ i : Fin (D+1), if i.val < s then
             (f i : ℤ) * poly ((i.val : ℤ)-(s : ℤ)) else 0 := by
        let term := fun i : ℕ => if i < s then coeff i * poly ((i : ℤ)-(s : ℤ)) else 0
        calc
          _ = ∑ i ∈ Finset.range s, term i := by
            apply Finset.sum_congr rfl
            intro i hi
            have his := Finset.mem_range.mp hi
            have hlen : i < ((List.range s).map coeff).length := by simpa using his
            rw [List.getD_eq_getElem _ 0 hlen, List.getElem_map, List.getElem_range]
            simp [term, his]
          _ = ∑ i ∈ Finset.range (D+1), term i := by
            apply Finset.sum_subset (Finset.range_mono (by omega))
            intro i _ hi
            simp [term, Finset.mem_range.not.mp hi]
          _ = ∑ i : Fin (D+1), term i.val := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            simp only [dite_eq_left (Finset.mem_range.mp hi)]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [term, coeff, dite_eq_left i.isLt, Fin.eta]
      have hz : readAt s - (∑ i ∈ Finset.range s, ((List.range s).map coeff).getD i 0 *
          poly ((i : ℤ)-(s : ℤ))) = ∑ i : Fin (D+1), if s ≤ i.val then
            (f i : ℤ) * poly ((i.val : ℤ)-(s : ℤ)) else 0 := by
        rw [hold, show readAt s = ∑ i : Fin (D+1), (f i : ℤ) * poly ((i.val : ℤ)-(s : ℤ))
              from recovery_read D d w f s, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i.val < s
        · simp [hi, show ¬s ≤ i.val by omega]
        · simp [hi, show s ≤ i.val by omega]
      rw [hz, show coeff s = (f ⟨s, hs⟩ : ℤ) by simp only [coeff, dite_eq_left hs]]
      exact recovery_weighted D P den poly hden herr f hf s hs
  change (List.range (D+1)).foldl update [] = _
  rw [hprefix _ le_rfl]
  apply List.ext_getElem
  · simp
  · intro n hn₁ hn₂
    have hn : n < D + 1 := by simpa using hn₁
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    simp only [coeff, dite_eq_left hn]


set_option maxHeartbeats 400000 in
private lemma uniform_weights (D d P : ℕ) (hd : d ≤ D)
    (hchoose : 2*P^2*Nat.choose D (d+1) < Nat.choose (D+d+1) (d+1)) :
    let bound := (2*(D+2))^(8*(d+1)^2)
    ∃ (den : ℕ) (w : Fin (d+1) → ℤ), 0 < den ∧ den ≤ bound ∧
      (∀ j, (w j).natAbs ≤ bound) ∧
      ∀ i : Fin (D+1), |(if i.val = 0 then (den : ℤ) else 0) -
        ∑ j : Fin (d+1), w j * (i.val : ℤ)^j.val| * (2*(P : ℤ)) < (den : ℤ) := by
  classical
  let q := diff (d+1) (grid D d)
  let A := (grid D d).eval 0
  let o : Fin (D+1) := 0
  let r : Fin (D+1) → ℤ := fun i => -(sd (d+1) (boundedGrid D d) i.val)
  have hq : q.natDegree ≤ d := grid_diff_natDegree_le D d
  have hbig : 0 < ((D+d+1).choose (d+1) : ℤ) := by
    exact_mod_cast Nat.choose_pos (show d+1 ≤ D+d+1 by omega)
  have hA : 0 < A := by
    dsimp [A]
    rw [grid_at_zero]
    positivity
  have hquot : r o * ((D+d+1).choose (d+1) : ℤ) = A*(D.choose (d+1) : ℤ) := by
    change -(sd (d+1) (boundedGrid D d) 0) * _ = (grid D d).eval 0 * _
    rw [residual_head, grid_at_end D d hd, grid_at_zero]
    ring
  have hr (i : Fin (D+1)) : r i = (if i = o then A else 0) - q.eval (i.val : ℤ) := by
    have h := residual_eq (D := D) (d := d) (i := i.val) (by omega)
    have ho : i = o ↔ i.val = 0 := by
      change i = 0 ↔ i.val = (0 : Fin (D+1)).val
      exact Fin.ext_iff
    by_cases he : i = o
    · rw [if_pos he]
      rw [if_pos (ho.mp he)] at h
      exact h
    · rw [if_neg he]
      rw [if_neg (fun h' => he (ho.mpr h'))] at h
      exact h
  have horth : (∑ i : Fin (D+1), r i * q.eval (i.val : ℤ)) = 0 := by
    have h := sd_orthogonal (d+1) (D+1) (boundedGrid D d) q
      (fun _ hi => boundedGrid_left hi)
      (fun i hi => by simp [boundedGrid, show ¬ i ≤ D by omega]) (Or.inr (by omega))
    simp only [r, neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
    calc
      _ = ∑ i ∈ Finset.range (D+1), sd (d+1) (boundedGrid D d) i * q.eval (i : ℤ) :=
        Fin.sum_univ_eq_sum_range (fun i => sd (d+1) (boundedGrid D d) i * q.eval (i : ℤ)) _
      _ = 0 := h
  have hnorm : (∑ i, (r i)^2) = A*r o := by
    calc
      (∑ i, (r i)^2) = (∑ i : Fin (D+1), r i * (if i = o then A else 0)) -
          (∑ i : Fin (D+1), r i * q.eval (i.val : ℤ)) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [← mul_sub, ← hr i, pow_two]
      _ = _ := by
        rw [horth, sub_zero]
        simp [mul_comm, Finset.sum_ite_eq']
  obtain ⟨hmax, hsharp⟩ := center_square_data r o A _ _ P hA hbig hnorm hquot (by exact_mod_cast hchoose)
  obtain ⟨c, hc, herr⟩ := square_sum_center r A P hA (by positivity) hmax hsharp
  let den := (2*A).toNat
  let w : Fin (d+1) → ℤ := fun j => 2*q.coeff j.val + if j = 0 then c else 0
  have hden : (den : ℤ) = 2*A := Int.toNat_of_nonneg (by omega)
  have hdenpos : 0 < den := by exact_mod_cast (show 0 < (den:ℤ) by rw [hden]; omega)
  let B : ℤ := 2*((D:ℤ)+2)
  have hB : 4 ≤ B := by dsimp [B]; omega
  have hAB : A ≤ B^(3*(d+1)) :=
    (grid_den_bound D d hd).trans (pow_le_pow_right₀ (by omega) (by omega))
  have hfinal : 4*B^(3*(d+1)) ≤ B^(8*(d+1)^2) := by
    calc
      _ ≤ B^(3*(d+1))*B := by
        rw [mul_comm 4]
        exact mul_le_mul_of_nonneg_left hB (pow_nonneg (by omega) _)
      _ = B^(3*(d+1)+1) := (pow_succ _ _).symm
      _ ≤ _ := by
        apply pow_le_pow_right₀ (by omega)
        nlinarith
  have hdenbound : (den : ℤ) ≤ B^(8*(d+1)^2) := by
    rw [hden]
    exact (show 2*A ≤ 4*B^(3*(d+1)) by linarith).trans hfinal
  refine ⟨den, w, hdenpos, ?_, ?_, ?_⟩
  · unfold B at hdenbound
    exact_mod_cast hdenbound
  · intro j
    have hw : |w j| ≤ B^(8*(d+1)^2) := by
      apply le_trans (abs_add_le _ _)
      rw [abs_mul, show |(2:ℤ)| = 2 by norm_num]
      have h₁ : |q.coeff j.val| ≤ B^(3*(d+1)) := grid_diff_coeff_bound hd j.val
      have h₂ : |(if j = 0 then c else 0)| ≤ 2*A := by
        split_ifs
        · exact hc
        · simpa using (show 0 ≤ 2*A by omega)
      exact (show 2*|q.coeff j.val| + |(if j = 0 then c else 0)| ≤ 4*B^(3*(d+1)) by linarith).trans hfinal
    unfold B at hw
    rw [← Int.natCast_natAbs] at hw
    exact_mod_cast hw
  · intro i
    have hqeval : q.eval (i.val : ℤ) = ∑ j : Fin (d+1), q.coeff j.val * (i.val : ℤ)^j.val := by
      calc
        _ = ∑ j ∈ Finset.range (d+1), q.coeff j * (i.val : ℤ)^j :=
          Polynomial.eval_eq_sum_range' (by omega) _
        _ = _ := (Fin.sum_univ_eq_sum_range (fun j => q.coeff j * (i.val : ℤ)^j) _).symm
    have hweval : (∑ j : Fin (d+1), w j * (i.val : ℤ)^j.val) = 2*q.eval (i.val : ℤ)+c := by
      simp only [w, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, ← hqeval,
        ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.val_zero, pow_zero, mul_one]
    have hδ : (if i.val = 0 then (den : ℤ) else 0) = 2*(if i = o then A else 0) := by
      rw [hden]
      by_cases hi : i = o
      · subst i; simp [o]
      · have hzero : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [hi, hzero]
    rw [hδ, hweval, hden]
    convert herr i using 3
    rw [hr]
    ring

end PEqualNP.Outside.L_lib_855

theorem PEqualNP.Outside.L_lib_855 :
    ∀ (D d P : ℕ), d ≤ D →
      (2*P^2*Nat.choose D (d+1) < Nat.choose (D+d+1) (d+1) ∨
        ∃ b : ℕ, P ≤ 2^b ∧ (2*D+1)*(2*b+2) ≤ (d+1)^2) →
      let bound := (2*(D+2))^(8*(d+1)^2)
      ∃ (den : ℕ) (w : Fin (d+1) → ℤ), 0 < den ∧ den ≤ bound ∧
        (∀ j, (w j).natAbs ≤ bound) ∧
        ∀ (f : Fin (D+1) → ℕ), (∑ i, f i) ≤ P →
          let mom := fun (l : Fin (d+1)) => ∑ i : Fin (D+1), f i * i.val^l.val
          let poly := fun (x : ℤ) => ∑ j, w j * x^j.val
          let readAt := fun (s : ℕ) => ∑ j : Fin (d+1), w j *
            ∑ l : Fin (d+1), (Nat.choose j.val l.val : ℤ) *
              (-(s : ℤ))^(j.val-l.val) * (mom l : ℤ)
          let recovered := (List.range (D+1)).foldl (fun (xs : List ℤ) (s : ℕ) =>
            let old := ∑ i ∈ Finset.range s, xs.getD i 0 * poly ((i : ℤ)-(s : ℤ))
            let z := readAt s - old
            xs ++ [(2*z+(den : ℤ))/(2*(den : ℤ))]) []
          recovered = List.ofFn (fun i : Fin (D+1) => (f i : ℤ)) := by
  intro D d P hd h
  obtain ⟨den, w, hden, hb, hw, herr⟩ := PEqualNP.Outside.L_lib_855.uniform_weights D d P hd
    (PEqualNP.Outside.L_lib_855.choose_target D d P hd h)
  exact ⟨den, w, hden, hb, hw, PEqualNP.Outside.L_lib_855.recover_of_uniform D d P den w hden herr⟩
