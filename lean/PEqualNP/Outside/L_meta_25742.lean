import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25742_aux

def dfact (m : ℕ) : ℕ := ∏ i ∈ Finset.range m, (2 * i + 1)

lemma dfact_pos (m : ℕ) : 0 < dfact m := by
  unfold dfact
  apply Finset.prod_pos
  intro i _
  omega

lemma two_mul_factorial_eq (m : ℕ) : (2 * m).factorial = 2 ^ m * m.factorial * dfact m := by
  induction m with
  | zero => simp [dfact]
  | succ m ih =>
    have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, ih]
    have hdf : dfact (m + 1) = dfact m * (2 * m + 1) := Finset.prod_range_succ _ m
    rw [hdf, pow_succ, Nat.factorial_succ]
    ring

lemma choose_two_mul_dfact_le (m r : ℕ) (hr : r ≤ m) :
    Nat.choose (2 * m) (2 * r) * dfact r ≤ dfact m * Nat.choose m r := by
  have heq : Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) = dfact m * Nat.choose m r := by
    have hpos : 0 < 2 ^ m * r.factorial * (m - r).factorial := by
      positivity
    apply Nat.eq_of_mul_eq_mul_left hpos
    have h1 : 2 ^ m * r.factorial * (m - r).factorial *
        (Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r)) =
        Nat.choose (2 * m) (2 * r) * (2 * r).factorial * (2 * (m - r)).factorial := by
      rw [two_mul_factorial_eq r, two_mul_factorial_eq (m - r)]
      have hp : 2 ^ r * 2 ^ (m - r) = 2 ^ m := by
        rw [← pow_add, Nat.add_sub_cancel' hr]
      calc 2 ^ m * r.factorial * (m - r).factorial *
              (Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r))
          = (2 ^ r * 2 ^ (m - r)) * r.factorial * (m - r).factorial *
              (Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r)) := by rw [hp]
        _ = Nat.choose (2 * m) (2 * r) * (2 ^ r * r.factorial * dfact r) *
              (2 ^ (m - r) * (m - r).factorial * dfact (m - r)) := by ring
    have h2 : Nat.choose (2 * m) (2 * r) * (2 * r).factorial * (2 * (m - r)).factorial =
        (2 * m).factorial := by
      have hsub : 2 * m - 2 * r = 2 * (m - r) := by omega
      rw [← hsub]
      exact Nat.choose_mul_factorial_mul_factorial (by omega)
    have h3 : 2 ^ m * r.factorial * (m - r).factorial * (dfact m * Nat.choose m r) =
        (2 * m).factorial := by
      rw [two_mul_factorial_eq m]
      have hcm := Nat.choose_mul_factorial_mul_factorial hr
      calc 2 ^ m * r.factorial * (m - r).factorial * (dfact m * Nat.choose m r)
          = 2 ^ m * (Nat.choose m r * r.factorial * (m - r).factorial) * dfact m := by ring
        _ = 2 ^ m * m.factorial * dfact m := by rw [hcm]
    rw [h1, h2, h3]
  have hd : 1 ≤ dfact (m - r) := dfact_pos (m - r)
  calc Nat.choose (2 * m) (2 * r) * dfact r
      = Nat.choose (2 * m) (2 * r) * dfact r * 1 := (Nat.mul_one _).symm
    _ ≤ Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) := Nat.mul_le_mul_left _ hd
    _ = dfact m * Nat.choose m r := heq

lemma nat_le_of_pow_le_pow {a b n : ℕ} (hn : n ≠ 0) (h : a ^ n ≤ b ^ n) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  exact Nat.not_lt.mpr h (Nat.pow_lt_pow_left hlt hn)

lemma dfact_le_pow (a : ℕ) : dfact a ≤ a ^ a := by
  have hsq : (dfact a) ^ 2 ≤ (a ^ a) ^ 2 := by
    have hrev : dfact a = ∏ i ∈ Finset.range a, (2 * (a - 1 - i) + 1) := by
      unfold dfact
      rw [← Finset.prod_range_reflect (fun i => 2 * i + 1) a]
    have hpair : (dfact a) ^ 2 = ∏ i ∈ Finset.range a, ((2 * i + 1) * (2 * (a - 1 - i) + 1)) := by
      rw [sq]
      conv_lhs => rhs; rw [hrev]
      unfold dfact
      rw [← Finset.prod_mul_distrib]
    rw [hpair]
    have hbound : ∏ i ∈ Finset.range a, ((2 * i + 1) * (2 * (a - 1 - i) + 1)) ≤
        ∏ _i ∈ Finset.range a, a ^ 2 := by
      apply Finset.prod_le_prod
      intro i hi
      have hia : i < a := Finset.mem_range.mp hi
      have hsum : (2 * i + 1) + (2 * (a - 1 - i) + 1) = 2 * a := by omega
      have hle : 4 * ((2 * i + 1) * (2 * (a - 1 - i) + 1)) ≤ ((2 * i + 1) + (2 * (a - 1 - i) + 1)) ^ 2 := by
        zify
        nlinarith [sq_nonneg ((2 * (i : ℤ) + 1) - (2 * ((a - 1 - i : ℕ) : ℤ) + 1))]
      rw [hsum] at hle
      have : (2 * a) ^ 2 = 4 * a ^ 2 := by ring
      omega
    calc ∏ i ∈ Finset.range a, ((2 * i + 1) * (2 * (a - 1 - i) + 1))
        ≤ ∏ _i ∈ Finset.range a, a ^ 2 := hbound
      _ = (a ^ 2) ^ a := by simp
      _ = (a ^ a) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  exact nat_le_of_pow_le_pow (by omega : 2 ≠ 0) hsq

lemma even_pow_add_sub (X a : ℤ) (m : ℕ) :
    (X + a) ^ (2 * m) + (X - a) ^ (2 * m) =
      2 * ∑ r ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * r) : ℤ) * X ^ (2 * r) * a ^ (2 * (m - r)) := by
  have h1 : (X + a) ^ (2 * m) =
      ∑ j ∈ Finset.range (2 * m + 1), X ^ j * a ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) := by
    exact add_pow X a (2 * m)
  have h2 : (X - a) ^ (2 * m) =
      ∑ j ∈ Finset.range (2 * m + 1), X ^ j * (-a) ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) := by
    rw [sub_eq_add_neg]; exact add_pow X (-a) (2 * m)
  rw [h1, h2, ← Finset.sum_add_distrib]
  have hcomb : ∀ j ∈ Finset.range (2 * m + 1),
      X ^ j * a ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) +
      X ^ j * (-a) ^ (2 * m - j) * (Nat.choose (2 * m) j : ℤ) =
      if Even j then 2 * ((Nat.choose (2 * m) j : ℤ) * X ^ j * a ^ (2 * m - j)) else 0 := by
    intro j hj
    have hjle : j ≤ 2 * m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hev : Even j
    · simp only [hev, ite_true]
      rcases hev with ⟨r, rfl⟩
      have hsub : 2 * m - (r + r) = 2 * (m - r) := by omega
      rw [hsub, pow_mul, pow_mul, neg_sq]
      ring
    · simp only [hev, ite_false]
      have hodd : Odd (2 * m - j) := by
        rw [Nat.not_even_iff_odd] at hev
        rcases hev with ⟨r, rfl⟩
        exact ⟨m - r - 1, by omega⟩
      rw [Odd.neg_pow hodd]
      ring
  rw [Finset.sum_congr rfl hcomb, ← Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_bij (fun j _ => j / 2) ?_ ?_ ?_ ?_
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjr, _⟩
    have hjlt : j < 2 * m + 1 := Finset.mem_range.mp hjr
    exact Finset.mem_range.mpr (by omega)
  · intro j₁ hj₁ j₂ hj₂ hdiv
    rcases (Finset.mem_filter.mp hj₁).2 with ⟨r₁, rfl⟩
    rcases (Finset.mem_filter.mp hj₂).2 with ⟨r₂, rfl⟩
    omega
  · intro r hr
    have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    refine ⟨2 * r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨r, by omega⟩⟩, by omega⟩
  · intro j hj
    rcases (Finset.mem_filter.mp hj).2 with ⟨r, rfl⟩
    have hdiv : (r + r) / 2 = r := by omega
    have hr2 : r + r = 2 * r := by omega
    have hsub : 2 * m - 2 * r = 2 * (m - r) := by omega
    rw [hdiv, hr2, hsub]

def bitSign (b : Bool) : ℤ := if b then -1 else 1

lemma bitSign_xor (a b : Bool) : bitSign (Bool.xor a b) = bitSign a * bitSign b := by
  cases a <;> cases b <;> rfl

lemma bitSign_sq (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> rfl

lemma cube_moment_bool (k : ℕ) : ∀ (m : ℕ) (v : Fin k → ℤ),
    (∑ z : Fin k → Bool, (∑ l : Fin k, v l * bitSign (z l)) ^ (2 * m)) ≤
      (2 ^ k : ℤ) * (dfact m : ℤ) * (∑ l : Fin k, (v l) ^ 2) ^ m := by
  induction k with
  | zero =>
    intro m v
    cases m with
    | zero => simp [dfact]
    | succ m =>
      simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_pow (by omega : 2 * (m + 1) ≠ 0),
        Finset.sum_const_zero, zero_pow (by omega : m + 1 ≠ 0), mul_zero, le_refl]
  | succ k ih =>
    intro m v
    let eSplit : ((Fin k → Bool) × Bool) ≃ (Fin (k + 1) → Bool) :=
      { toFun := fun p => Fin.snoc p.1 p.2,
        invFun := fun z => (Fin.init z, z (Fin.last k)),
        left_inv := fun ⟨z', b⟩ => by
          ext i
          · simp [Fin.init_snoc]
          · simp [Fin.snoc_last],
        right_inv := fun z => Fin.snoc_init_self z }
    rw [← Equiv.sum_comp eSplit, Fintype.sum_prod_type]
    have hinner : ∀ z' : Fin k → Bool,
        (∑ b : Bool, (∑ l : Fin (k + 1), v l * bitSign (eSplit (z', b) l)) ^ (2 * m)) =
        ((∑ l : Fin k, v l.castSucc * bitSign (z' l)) + v (Fin.last k)) ^ (2 * m) +
        ((∑ l : Fin k, v l.castSucc * bitSign (z' l)) - v (Fin.last k)) ^ (2 * m) := by
      intro z'
      rw [Fintype.sum_bool]
      have htrue : (∑ l : Fin (k + 1), v l * bitSign (eSplit (z', true) l)) =
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) - v (Fin.last k) := by
        rw [Fin.sum_univ_castSucc]
        simp only [eSplit, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last, bitSign, ite_true]
        ring
      have hfalse : (∑ l : Fin (k + 1), v l * bitSign (eSplit (z', false) l)) =
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) + v (Fin.last k) := by
        rw [Fin.sum_univ_castSucc]
        simp only [eSplit, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last, bitSign, Bool.false_eq_true, ite_false]
        ring
      rw [htrue, hfalse, add_comm]
    simp_rw [hinner, even_pow_add_sub]
    rw [← Finset.mul_sum, Finset.sum_comm]
    set S : ℤ := ∑ l : Fin k, (v l.castSucc) ^ 2
    set a : ℤ := v (Fin.last k)
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hterm_le : ∀ r ∈ Finset.range (m + 1),
        (∑ z' : Fin k → Bool, (Nat.choose (2 * m) (2 * r) : ℤ) *
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))) ≤
        (2 ^ k : ℤ) * (dfact m : ℤ) * ((Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := by
      intro r hr
      have hrm : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hpull : (∑ z' : Fin k → Bool, (Nat.choose (2 * m) (2 * r) : ℤ) *
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))) =
          ((Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r))) *
          ∑ z' : Fin k → Bool, (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro z' _; ring
      rw [hpull]
      have hca_nn : 0 ≤ (Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r)) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [pow_mul]; exact pow_nonneg (sq_nonneg a) _
      have hih := ih r (fun l => v l.castSucc)
      have hstep1 := mul_le_mul_of_nonneg_left hih hca_nn
      have hch : (Nat.choose (2 * m) (2 * r) : ℤ) * (dfact r : ℤ) ≤
          (dfact m : ℤ) * (Nat.choose m r : ℤ) := by
        exact_mod_cast choose_two_mul_dfact_le m r hrm
      have hpow_nn : 0 ≤ (2 ^ k : ℤ) * S ^ r * (a ^ 2) ^ (m - r) :=
        mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hS_nn _)) (pow_nonneg (sq_nonneg a) _)
      have hstep2 := mul_le_mul_of_nonneg_right hch hpow_nn
      have hsqa : a ^ (2 * (m - r)) = (a ^ 2) ^ (m - r) := pow_mul a 2 (m - r)
      calc ((Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r))) *
              ∑ z' : Fin k → Bool, (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r)
          ≤ ((Nat.choose (2 * m) (2 * r) : ℤ) * a ^ (2 * (m - r))) *
              ((2 ^ k : ℤ) * (dfact r : ℤ) * S ^ r) := hstep1
        _ = ((Nat.choose (2 * m) (2 * r) : ℤ) * (dfact r : ℤ)) *
              ((2 ^ k : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := by rw [hsqa]; ring
        _ ≤ ((dfact m : ℤ) * (Nat.choose m r : ℤ)) *
              ((2 ^ k : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := hstep2
        _ = (2 ^ k : ℤ) * (dfact m : ℤ) * ((Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) := by ring
    have hsum_le : (∑ r ∈ Finset.range (m + 1), ∑ z' : Fin k → Bool,
        (Nat.choose (2 * m) (2 * r) : ℤ) *
          (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))) ≤
        ∑ r ∈ Finset.range (m + 1),
          (2 ^ k : ℤ) * (dfact m : ℤ) * ((Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) :=
      Finset.sum_le_sum hterm_le
    have hbinom : (∑ r ∈ Finset.range (m + 1),
        (Nat.choose m r : ℤ) * S ^ r * (a ^ 2) ^ (m - r)) = (S + a ^ 2) ^ m := by
      rw [add_pow]
      apply Finset.sum_congr rfl; intro r _; ring
    have hS_full : (∑ l : Fin (k + 1), (v l) ^ 2) = S + a ^ 2 := Fin.sum_univ_castSucc _
    rw [← Finset.mul_sum, hbinom] at hsum_le
    rw [hS_full]
    calc 2 * ∑ r ∈ Finset.range (m + 1), ∑ z' : Fin k → Bool,
            (Nat.choose (2 * m) (2 * r) : ℤ) *
              (∑ l : Fin k, v l.castSucc * bitSign (z' l)) ^ (2 * r) * a ^ (2 * (m - r))
        ≤ 2 * ((2 ^ k : ℤ) * (dfact m : ℤ) * (S + a ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left hsum_le (by norm_num)
      _ = (2 ^ (k + 1) : ℤ) * (dfact m : ℤ) * (S + a ^ 2) ^ m := by rw [pow_succ]; ring

lemma fin_pow2_equiv_bits (k : ℕ) :
    Function.Bijective (fun (x : Fin (2 ^ k)) (l : Fin k) => x.val.testBit l.val) := by
  have hcard : Fintype.card (Fin (2 ^ k)) = Fintype.card (Fin k → Bool) := by
    simp
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, hcard⟩
  intro x y hxy
  ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact congrFun hxy ⟨i, hi⟩
  · have hx : x.val < 2 ^ i := lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    have hy : y.val < 2 ^ i := lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

lemma cube_moment_fin (k m : ℕ) (v : Fin k → ℤ) :
    (∑ z : Fin (2 ^ k), (∑ l : Fin k, v l * bitSign (z.val.testBit l.val)) ^ (2 * m)) ≤
      (2 ^ k : ℤ) * (dfact m : ℤ) * (∑ l : Fin k, (v l) ^ 2) ^ m := by
  let e : Fin (2 ^ k) ≃ (Fin k → Bool) := Equiv.ofBijective _ (fin_pow2_equiv_bits k)
  have heq : (∑ z : Fin (2 ^ k), (∑ l : Fin k, v l * bitSign (z.val.testBit l.val)) ^ (2 * m)) =
      ∑ z : Fin k → Bool, (∑ l : Fin k, v l * bitSign (z l)) ^ (2 * m) :=
    Equiv.sum_comp e (fun z : Fin k → Bool => (∑ l : Fin k, v l * bitSign (z l)) ^ (2 * m))
  rw [heq]
  exact cube_moment_bool k m v

lemma chebyshev_pow {ι : Type*} (I : Finset ι) (w a : ι → ℚ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (ha : ∀ i ∈ I, 0 ≤ a i) (m : ℕ) :
    (∑ i ∈ I, w i * a i ^ m) * (∑ i ∈ I, w i * a i) ≤
      (∑ i ∈ I, w i) * (∑ i ∈ I, w i * a i ^ (m + 1)) := by
  have hdiff : 2 * ((∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) -
      (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j)) =
      ∑ i ∈ I, ∑ j ∈ I, w i * w j * (a i ^ m - a j ^ m) * (a i - a j) := by
    have h1 : (∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a j ^ (m + 1) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have h2 : (∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a i ^ (m + 1) := by
      rw [h1, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    have h3 : (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a i ^ m * a j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    have h4 : (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j) =
        ∑ i ∈ I, ∑ j ∈ I, w i * w j * a j ^ m * a i := by
      rw [h3, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    have hL : 2 * ((∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) -
        (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j)) =
        ((∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1)) + (∑ i ∈ I, w i) * (∑ j ∈ I, w j * a j ^ (m + 1))) -
        ((∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j) + (∑ i ∈ I, w i * a i ^ m) * (∑ j ∈ I, w j * a j)) := by
      ring
    rw [hL]
    conv_lhs =>
      arg 1
      arg 1; rw [h1]
    conv_lhs =>
      arg 1
      arg 2; rw [h2]
    conv_lhs =>
      arg 2
      arg 1; rw [h3]
    conv_lhs =>
      arg 2
      arg 2; rw [h4]
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [pow_succ, pow_succ]
    ring
  have hnn : 0 ≤ ∑ i ∈ I, ∑ j ∈ I, w i * w j * (a i ^ m - a j ^ m) * (a i - a j) := by
    apply Finset.sum_nonneg; intro i hi
    apply Finset.sum_nonneg; intro j hj
    have hwi := hw i hi
    have hwj := hw j hj
    have hai := ha i hi
    have haj := ha j hj
    have hprod : 0 ≤ (a i ^ m - a j ^ m) * (a i - a j) := by
      rcases le_total (a i) (a j) with hle | hle
      · have hpm : a i ^ m ≤ a j ^ m := pow_le_pow_left₀ hai hle m
        exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hpm) (sub_nonpos.mpr hle)
      · have hpm : a j ^ m ≤ a i ^ m := pow_le_pow_left₀ haj hle m
        exact mul_nonneg (sub_nonneg.mpr hpm) (sub_nonneg.mpr hle)
    have : w i * w j * (a i ^ m - a j ^ m) * (a i - a j) =
        (w i * w j) * ((a i ^ m - a j ^ m) * (a i - a j)) := by ring
    rw [this]
    exact mul_nonneg (mul_nonneg hwi hwj) hprod
  linarith

lemma weighted_pow_mean {ι : Type*} (I : Finset ι) (w a : ι → ℚ)
    (hw : ∀ i ∈ I, 0 ≤ w i) (ha : ∀ i ∈ I, 0 ≤ a i) :
    ∀ m : ℕ, 0 < m →
      (∑ i ∈ I, w i * a i) ^ m ≤ (∑ i ∈ I, w i) ^ (m - 1) * (∑ i ∈ I, w i * a i ^ m) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m =>
      have hih := ih (by omega)
      have hsum_nn : 0 ≤ ∑ i ∈ I, w i * a i := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (ha i hi))
      have hw_nn : 0 ≤ ∑ i ∈ I, w i := Finset.sum_nonneg hw
      have h1 : (∑ i ∈ I, w i * a i) ^ (m + 2) ≤
          (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i * a i ^ (m + 1)) * (∑ i ∈ I, w i * a i)) := by
        rw [pow_succ]
        calc (∑ i ∈ I, w i * a i) ^ (m + 1) * (∑ i ∈ I, w i * a i)
            ≤ ((∑ i ∈ I, w i) ^ m * (∑ i ∈ I, w i * a i ^ (m + 1))) * (∑ i ∈ I, w i * a i) :=
              mul_le_mul_of_nonneg_right hih hsum_nn
          _ = (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i * a i ^ (m + 1)) * (∑ i ∈ I, w i * a i)) := by ring
      have h2 := chebyshev_pow I w a hw ha (m + 1)
      calc (∑ i ∈ I, w i * a i) ^ (m + 2)
          ≤ (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i * a i ^ (m + 1)) * (∑ i ∈ I, w i * a i)) := h1
        _ ≤ (∑ i ∈ I, w i) ^ m * ((∑ i ∈ I, w i) * (∑ i ∈ I, w i * a i ^ (m + 2))) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hw_nn m)
        _ = (∑ i ∈ I, w i) ^ (m + 1) * (∑ i ∈ I, w i * a i ^ (m + 2)) := by rw [pow_succ]; ring

lemma group_energy_bound {k : ℕ} (S : Finset (Fin (2 ^ k))) (w : Fin (2 ^ k) → ℤ)
    (hw : ∀ x ∈ S, w x = 1 ∨ w x = -1) (m : ℕ) (hm : 0 < m) :
    let M := fun l : Fin k => ∑ x ∈ S, w x * bitSign (x.val.testBit l.val)
    let L := ∑ l : Fin k, (M l) ^ 2
    L ^ m ≤ (2 ^ k : ℤ) * (dfact m : ℤ) * (S.card : ℤ) ^ (2 * m - 1) := by
  intro M L
  have hL_nn : 0 ≤ L := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hL0 : L = 0
  · rw [hL0, zero_pow (by omega : m ≠ 0)]
    positivity
  · have hL_pos : 0 < L := lt_of_le_of_ne hL_nn (Ne.symm hL0)
    let g : Fin (2 ^ k) → ℤ := fun z => ∑ l : Fin k, M l * bitSign (z.val.testBit l.val)
    have hL_eq : L = ∑ z ∈ S, w z * g z := by
      dsimp only [L, g]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      have : (∑ z ∈ S, w z * (M l * bitSign (z.val.testBit l.val))) =
          M l * ∑ z ∈ S, w z * bitSign (z.val.testBit l.val) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
      rw [this, sq]
    have hL_le_abs : L ≤ ∑ z ∈ S, |g z| := by
      rw [hL_eq]
      apply Finset.sum_le_sum
      intro z hz
      rcases hw z hz with h1 | h2
      · rw [h1, one_mul]; exact le_abs_self _
      · rw [h2, neg_one_mul]; exact neg_le_abs _
    have hL_pow : L ^ (2 * m) ≤ (S.card : ℤ) ^ (2 * m - 1) * ∑ z ∈ S, (g z) ^ (2 * m) := by
      have hq := weighted_pow_mean S (fun _ => (1 : ℚ)) (fun z => (|g z| : ℚ))
        (fun _ _ => zero_le_one) (fun z _ => by exact_mod_cast abs_nonneg (g z)) (2 * m) (by omega)
      have hL_q : (L : ℚ) ≤ ∑ z ∈ S, (|g z| : ℚ) := by exact_mod_cast hL_le_abs
      have hpow_q : (L : ℚ) ^ (2 * m) ≤ (∑ z ∈ S, (|g z| : ℚ)) ^ (2 * m) :=
        pow_le_pow_left₀ (by exact_mod_cast hL_nn) hL_q (2 * m)
      have h1 : (∑ z ∈ S, (1 : ℚ) * (|g z| : ℚ)) = ∑ z ∈ S, (|g z| : ℚ) := by simp
      have h2 : (∑ _z ∈ S, (1 : ℚ)) = (S.card : ℚ) := by simp
      have h3 : (∑ z ∈ S, (1 : ℚ) * (|g z| : ℚ) ^ (2 * m)) = ∑ z ∈ S, ((g z : ℚ) ^ (2 * m)) := by
        apply Finset.sum_congr rfl; intro z _
        rw [one_mul, pow_mul, pow_mul]
        have : (|g z| : ℚ) ^ 2 = (g z : ℚ) ^ 2 := by exact_mod_cast sq_abs (g z)
        rw [this]
      rw [h1, h2, h3] at hq
      have hcomb := le_trans hpow_q hq
      exact_mod_cast hcomb
    have hsum_le_all : (∑ z ∈ S, (g z) ^ (2 * m)) ≤ ∑ z : Fin (2 ^ k), (g z) ^ (2 * m) := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro z
      rw [pow_mul]; exact pow_nonneg (sq_nonneg _) m
    have hcube : (∑ z : Fin (2 ^ k), (g z) ^ (2 * m)) ≤ (2 ^ k : ℤ) * (dfact m : ℤ) * L ^ m :=
      cube_moment_fin k m M
    have hprod : L ^ m * L ^ m ≤ ((2 ^ k : ℤ) * (dfact m : ℤ) * (S.card : ℤ) ^ (2 * m - 1)) * L ^ m := by
      calc L ^ m * L ^ m = L ^ (2 * m) := by rw [← pow_add, two_mul]
        _ ≤ (S.card : ℤ) ^ (2 * m - 1) * ∑ z ∈ S, (g z) ^ (2 * m) := hL_pow
        _ ≤ (S.card : ℤ) ^ (2 * m - 1) * ∑ z : Fin (2 ^ k), (g z) ^ (2 * m) :=
            mul_le_mul_of_nonneg_left hsum_le_all (pow_nonneg (Nat.cast_nonneg _) _)
        _ ≤ (S.card : ℤ) ^ (2 * m - 1) * ((2 ^ k : ℤ) * (dfact m : ℤ) * L ^ m) :=
            mul_le_mul_of_nonneg_left hcube (pow_nonneg (Nat.cast_nonneg _) _)
        _ = ((2 ^ k : ℤ) * (dfact m : ℤ) * (S.card : ℤ) ^ (2 * m - 1)) * L ^ m := by ring
    exact le_of_mul_le_mul_right hprod (pow_pos hL_pos m)

end PEqualNP.Outside.L_meta_25742_aux

theorem PEqualNP.Outside.L_meta_25742 :
∀ k : ℕ,
  let N := 2^k
  ∀ (addr : Fin N → Fin k) (G : Fin N → Fin N → Bool) (A B : Finset (Fin N)),
    (∀ x ∉ A, ∀ y ∉ B, G x y = x.val.testBit (addr y).val) →
    ∀ (π : Equiv.Perm (Fin N)) (U R C : Finset (Fin N)) (f g : Fin N → Bool)
        (D : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool),
      let K := (Finset.univ \ (R ∪ C)).filter (fun label => label ∉ A ∧ π label ∉ B)
      let h := K.card
      let count := fun j : Fin k => (K.filter (fun i => addr (π i) = j)).card
      let mask := fun (x y : Fin N) => if x = y then
        (if x ∈ U then ({x} : Finset (Fin N)) else ∅) else {x,y}
      let e := (Finset.univ.filter (fun z : Fin N × Fin N =>
        D (mask z.1 z.2) (R ∩ {z.1}) (C ∩ {z.2}) ≠
          xor (G z.1 (π z.2)) (xor (f z.1) (g z.2)))).card
      (∀ m : ℕ, 0 < m →
        (h^2-4*e)^m ≤ N * (∏ i ∈ Finset.range m, (2*i+1)) *
          h^(m-1) * (∑ j : Fin k, (count j)^m)) ∧
      (∀ a cap : ℕ, 0 < a → N ≤ 2^a*cap → (∀ j, count j ≤ cap) →
        h^2 ≤ 4*e + 2*a*cap*h) := by
  intro k N addr G A B hG π U R C f g D K h count mask e
  have hcount_sum : ∑ j : Fin k, count j = h := by
    dsimp only [count, h]
    rw [← Finset.card_biUnion]
    · congr 1
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
      exact ⟨fun ⟨_, hi, _⟩ => hi, fun hi => ⟨addr (π i), hi, rfl⟩⟩
    · intro j₁ _ j₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro i h1 h2
      exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  have hpart1 : ∀ m : ℕ, 0 < m →
      (h ^ 2 - 4 * e) ^ m ≤ N * (∏ i ∈ Finset.range m, (2 * i + 1)) *
        h ^ (m - 1) * (∑ j : Fin k, (count j) ^ m) := by
    intro m hm
    by_cases htriv : h ^ 2 ≤ 4 * e
    · have h0 : h ^ 2 - 4 * e = 0 := Nat.sub_eq_zero_of_le htriv
      rw [h0, zero_pow (by omega : m ≠ 0)]
      exact Nat.zero_le _
    · push Not at htriv
      have hh_pos : 0 < h := by
        by_contra h0; have : h = 0 := by omega
        rw [this] at htriv; simp at htriv
      let σ := PEqualNP.Outside.L_meta_25742_aux.bitSign
      let T : Fin N → Fin N → ℤ := fun x y => σ (xor (G x (π y)) (xor (f x) (g y)))
      let err : Fin N → Fin N → ℤ := fun x y =>
        if D (mask x y) (R ∩ {x}) (C ∩ {y}) ≠ xor (G x (π y)) (xor (f x) (g y)) then 1 else 0
      have herr_sum : (∑ x : Fin N, ∑ y : Fin N, err x y) = (e : ℤ) := by
        rw [← Fintype.sum_prod_type']
        dsimp only [err, e]
        rw [Finset.sum_boole]
      have hpair_bd : ∀ x ∈ K, ∀ y ∈ K, 1 - T x y * T y x ≤ 2 * (err x y + err y x) := by
        intro x hx y hy
        have hxRC : x ∉ R ∪ C := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx).1).2
        have hyRC : y ∉ R ∪ C := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
        have hxR : R ∩ {x} = ∅ := by
          ext z; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hzR, rfl⟩; exact hxRC (Finset.mem_union_left C hzR)
        have hyR : R ∩ {y} = ∅ := by
          ext z; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hzR, rfl⟩; exact hyRC (Finset.mem_union_left C hzR)
        have hxC : C ∩ {x} = ∅ := by
          ext z; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hzC, rfl⟩; exact hxRC (Finset.mem_union_right R hzC)
        have hyC : C ∩ {y} = ∅ := by
          ext z; simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
          rintro ⟨hzC, rfl⟩; exact hyRC (Finset.mem_union_right R hzC)
        by_cases hxy : x = y
        · subst hxy
          have hsq : T x x * T x x = 1 := PEqualNP.Outside.L_meta_25742_aux.bitSign_sq _
          rw [hsq, sub_self]
          have hnn : 0 ≤ err x x := by dsimp only [err]; split_ifs <;> norm_num
          linarith
        · have hmask : mask x y = mask y x := by
            dsimp only [mask]
            have hyx : y ≠ x := Ne.symm hxy
            simp only [hxy, hyx, ite_false]
            exact Finset.pair_comm x y
          have hD : D (mask x y) (R ∩ {x}) (C ∩ {y}) = D (mask y x) (R ∩ {y}) (C ∩ {x}) := by
            rw [hmask, hxR, hyR, hxC, hyC]
          by_cases hsame : xor (G x (π y)) (xor (f x) (g y)) = xor (G y (π x)) (xor (f y) (g x))
          · have hTeq : T x y = T y x := by dsimp only [T]; rw [hsame]
            rw [hTeq, PEqualNP.Outside.L_meta_25742_aux.bitSign_sq, sub_self]
            have h1 : 0 ≤ err x y := by dsimp only [err]; split_ifs <;> norm_num
            have h2 : 0 ≤ err y x := by dsimp only [err]; split_ifs <;> norm_num
            linarith
          · have h1 : err x y = 1 ∨ err y x = 1 := by
              by_cases hc : D (mask x y) (R ∩ {x}) (C ∩ {y}) = xor (G x (π y)) (xor (f x) (g y))
              · right
                have hne2 : D (mask y x) (R ∩ {y}) (C ∩ {x}) ≠ xor (G y (π x)) (xor (f y) (g x)) := by
                  rw [← hD, hc]; exact hsame
                simp [err, hne2]
              · left; simp [err, hc]
            have hTprod : -1 ≤ T x y * T y x := by
              dsimp only [T, σ, PEqualNP.Outside.L_meta_25742_aux.bitSign]
              split_ifs <;> norm_num
            have he1 : 0 ≤ err x y := by dsimp only [err]; split_ifs <;> norm_num
            have he2 : 0 ≤ err y x := by dsimp only [err]; split_ifs <;> norm_num
            rcases h1 with h1 | h1 <;> linarith
      have hquad_ge : ((h : ℤ) ^ 2 - 4 * (e : ℤ)) ≤ ∑ x ∈ K, ∑ y ∈ K, T x y * T y x := by
        have hsum1 := Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy => hpair_bd x hx y hy))
        have hLHS : (∑ x ∈ K, ∑ y ∈ K, (1 - T x y * T y x)) =
            (h : ℤ) ^ 2 - ∑ x ∈ K, ∑ y ∈ K, T x y * T y x := by
          simp_rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
          have : (h : ℤ) * (h : ℤ) = (h : ℤ) ^ 2 := (sq _).symm
          dsimp only [h]; linarith
        have hRHS : (∑ x ∈ K, ∑ y ∈ K, 2 * (err x y + err y x)) ≤ 4 * (e : ℤ) := by
          have hnn : ∀ x y : Fin N, 0 ≤ err x y := fun x y => by dsimp only [err]; split_ifs <;> norm_num
          have hs1 : (∑ x ∈ K, ∑ y ∈ K, err x y) ≤ (e : ℤ) := by
            rw [← herr_sum]
            calc ∑ x ∈ K, ∑ y ∈ K, err x y
                ≤ ∑ x ∈ K, ∑ y : Fin N, err x y :=
                  Finset.sum_le_sum (fun x _ => Finset.sum_le_univ_sum_of_nonneg (fun y => hnn x y))
              _ ≤ ∑ x : Fin N, ∑ y : Fin N, err x y :=
                  Finset.sum_le_univ_sum_of_nonneg (fun x => Finset.sum_nonneg (fun y _ => hnn x y))
          have hs2 : (∑ x ∈ K, ∑ y ∈ K, err y x) = ∑ x ∈ K, ∑ y ∈ K, err x y := Finset.sum_comm
          simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, hs2]
          linarith
        rw [hLHS] at hsum1
        linarith
      let w : Fin N → ℤ := fun x => σ (f x) * σ (g x)
      let Kg : Fin k → Finset (Fin N) := fun j => K.filter (fun i => addr (π i) = j)
      let M : Fin k → Fin k → ℤ := fun j l => ∑ x ∈ Kg j, w x * σ (x.val.testBit l.val)
      let L : Fin k → ℤ := fun j => ∑ l : Fin k, (M j l) ^ 2
      have hT_fact : ∀ x ∈ K, ∀ y ∈ K,
          T x y * T y x = (w x * σ (x.val.testBit (addr (π y)).val)) *
            (w y * σ (y.val.testBit (addr (π x)).val)) := by
        intro x hx y hy
        have hxAB := (Finset.mem_filter.mp hx).2
        have hyAB := (Finset.mem_filter.mp hy).2
        dsimp only [T, w, σ]
        rw [hG x hxAB.1 (π y) hyAB.2, hG y hyAB.1 (π x) hxAB.2]
        simp only [PEqualNP.Outside.L_meta_25742_aux.bitSign_xor]
        ring
      have htr_eq : (∑ x ∈ K, ∑ y ∈ K, T x y * T y x) = ∑ j : Fin k, ∑ l : Fin k, M j l * M l j := by
        have h1 : (∑ x ∈ K, ∑ y ∈ K, T x y * T y x) =
            ∑ x ∈ K, ∑ y ∈ K, (w x * σ (x.val.testBit (addr (π y)).val)) *
              (w y * σ (y.val.testBit (addr (π x)).val)) :=
          Finset.sum_congr rfl (fun x hx => Finset.sum_congr rfl (fun y hy => hT_fact x hx y hy))
        rw [h1]
        have hpartK : K = Finset.univ.biUnion Kg := by
          ext x
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Kg, Finset.mem_filter]
          exact ⟨fun hx => ⟨addr (π x), hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩
        have hdisjK : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) Kg := by
          intro j₁ _ j₂ _ hne
          rw [Function.onFun, Finset.disjoint_left]
          intro x hx1 hx2
          exact hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
        conv_lhs =>
          rw [hpartK, Finset.sum_biUnion hdisjK]
        apply Finset.sum_congr rfl
        intro j _
        conv_lhs =>
          arg 2; ext x
          rw [Finset.sum_biUnion hdisjK]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        dsimp only [M]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        have hxj : addr (π x) = j := (Finset.mem_filter.mp hx).2
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        have hyl : addr (π y) = l := (Finset.mem_filter.mp hy).2
        rw [hxj, hyl]
      have htr_le : (∑ j : Fin k, ∑ l : Fin k, M j l * M l j) ≤ ∑ j : Fin k, L j := by
        have h2 : 2 * (∑ j : Fin k, ∑ l : Fin k, M j l * M l j) ≤ 2 * (∑ j : Fin k, L j) := by
          have hsym : (∑ j : Fin k, ∑ l : Fin k, (M l j) ^ 2) = ∑ j : Fin k, L j := by
            rw [Finset.sum_comm]
          have hL2 : 2 * (∑ j : Fin k, L j) = ∑ j : Fin k, ∑ l : Fin k, ((M j l) ^ 2 + (M l j) ^ 2) := by
            simp_rw [Finset.sum_add_distrib, hsym]
            dsimp only [L]; ring
          rw [hL2, Finset.mul_sum]
          apply Finset.sum_le_sum; intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum; intro l _
          nlinarith [sq_nonneg (M j l - M l j)]
        linarith
      have hL_sum_ge : ((h : ℤ) ^ 2 - 4 * (e : ℤ)) ≤ ∑ j : Fin k, L j := by
        linarith
      have hL_bd : ∀ j : Fin k, (L j) ^ m ≤
          (N : ℤ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℤ) * (count j : ℤ) ^ (2 * m - 1) := by
        intro j
        have hw1 : ∀ x ∈ Kg j, w x = 1 ∨ w x = -1 := fun x _ => by
          dsimp only [w, σ, PEqualNP.Outside.L_meta_25742_aux.bitSign]
          split_ifs <;> decide
        exact PEqualNP.Outside.L_meta_25742_aux.group_energy_bound (Kg j) w hw1 m hm
      have hL_zero : ∀ j : Fin k, count j = 0 → L j = 0 := by
        intro j hc0
        have hKe : Kg j = ∅ := Finset.card_eq_zero.mp hc0
        dsimp only [L, M]
        simp [hKe]
      set posJ := Finset.univ.filter (fun j : Fin k => 0 < count j)
      have hsum_posJ : ∑ j : Fin k, L j = ∑ j ∈ posJ, L j := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hnot
        have hc0 : count j = 0 := by
          have := Finset.mem_filter.not.mp hnot
          simp only [Finset.mem_univ, true_and] at this
          omega
        exact hL_zero j hc0
      have hcount_posJ : ∑ j ∈ posJ, count j = h := by
        rw [← hcount_sum]
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j _ hnot
        have := Finset.mem_filter.not.mp hnot
        simp only [Finset.mem_univ, true_and] at this
        omega
      have hHolder_q : (∑ j ∈ posJ, (L j : ℚ)) ^ m ≤
          (h : ℚ) ^ (m - 1) * ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) := by
        have hq := PEqualNP.Outside.L_meta_25742_aux.weighted_pow_mean posJ
          (fun j => (count j : ℚ)) (fun j => (L j : ℚ) / (count j : ℚ))
          (fun j _ => Nat.cast_nonneg _)
          (fun j _ => div_nonneg (by exact_mod_cast (Finset.sum_nonneg (fun _ _ => sq_nonneg _) : (0 : ℤ) ≤ L j)) (Nat.cast_nonneg _))
          m hm
        have hL1 : (∑ j ∈ posJ, (count j : ℚ) * ((L j : ℚ) / (count j : ℚ))) = ∑ j ∈ posJ, (L j : ℚ) := by
          apply Finset.sum_congr rfl; intro j hj
          have hcpos : (count j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_filter.mp hj).2)
          exact mul_div_cancel₀ _ hcpos
        have hL2 : (∑ j ∈ posJ, (count j : ℚ)) = (h : ℚ) := by exact_mod_cast hcount_posJ
        have hL3 : (∑ j ∈ posJ, (count j : ℚ) * ((L j : ℚ) / (count j : ℚ)) ^ m) =
            ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) := by
          apply Finset.sum_congr rfl; intro j hj
          have hcpos : (count j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Finset.mem_filter.mp hj).2)
          rw [div_pow]
          have hpow : (count j : ℚ) ^ m = (count j : ℚ) * (count j : ℚ) ^ (m - 1) := by
            conv_lhs => rw [show m = (m - 1) + 1 by omega, pow_succ]
            ring
          rw [hpow]
          field_simp [hcpos]
        rw [hL1, hL2, hL3] at hq
        exact hq
      have hterm_q : ∀ j ∈ posJ,
          (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) ≤
          (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * (count j : ℚ) ^ m := by
        intro j hj
        have hcpos : (0 : ℚ) < (count j : ℚ) := Nat.cast_pos.mpr (Finset.mem_filter.mp hj).2
        have hpow_pos : (0 : ℚ) < (count j : ℚ) ^ (m - 1) := pow_pos hcpos _
        rw [div_le_iff₀ hpow_pos]
        have hbd_q : (L j : ℚ) ^ m ≤
            (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * (count j : ℚ) ^ (2 * m - 1) := by
          exact_mod_cast hL_bd j
        have hpow_eq : (count j : ℚ) ^ m * (count j : ℚ) ^ (m - 1) = (count j : ℚ) ^ (2 * m - 1) := by
          rw [← pow_add]; congr 1; omega
        calc (L j : ℚ) ^ m
            ≤ (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * (count j : ℚ) ^ (2 * m - 1) := hbd_q
          _ = (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * (count j : ℚ) ^ m *
                (count j : ℚ) ^ (m - 1) := by rw [← hpow_eq]; ring
      have hsum_q : (∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1)) ≤
          (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * ∑ j : Fin k, (count j : ℚ) ^ m := by
        calc ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1)
            ≤ ∑ j ∈ posJ, (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * (count j : ℚ) ^ m :=
              Finset.sum_le_sum hterm_q
          _ = (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * ∑ j ∈ posJ, (count j : ℚ) ^ m := by
              rw [← Finset.mul_sum]
          _ ≤ (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) * ∑ j : Fin k, (count j : ℚ) ^ m := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Finset.sum_le_univ_sum_of_nonneg
              intro j; positivity
      have hsub_q : ((h ^ 2 - 4 * e : ℕ) : ℚ) ≤ ∑ j ∈ posJ, (L j : ℚ) := by
        have hcast : ((h ^ 2 - 4 * e : ℕ) : ℤ) = (h : ℤ) ^ 2 - 4 * (e : ℤ) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        have hle_z : ((h ^ 2 - 4 * e : ℕ) : ℤ) ≤ ∑ j ∈ posJ, L j := by
          rw [hcast, ← hsum_posJ]; exact hL_sum_ge
        exact_mod_cast hle_z
      have hfinal_q : ((h ^ 2 - 4 * e : ℕ) : ℚ) ^ m ≤
          (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) *
            (h : ℚ) ^ (m - 1) * (∑ j : Fin k, (count j : ℚ) ^ m) := by
        calc ((h ^ 2 - 4 * e : ℕ) : ℚ) ^ m
            ≤ (∑ j ∈ posJ, (L j : ℚ)) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) hsub_q m
          _ ≤ (h : ℚ) ^ (m - 1) * ∑ j ∈ posJ, (L j : ℚ) ^ m / (count j : ℚ) ^ (m - 1) := hHolder_q
          _ ≤ (h : ℚ) ^ (m - 1) * ((N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) *
                ∑ j : Fin k, (count j : ℚ) ^ m) :=
              mul_le_mul_of_nonneg_left hsum_q (by positivity)
          _ = (N : ℚ) * (PEqualNP.Outside.L_meta_25742_aux.dfact m : ℚ) *
                (h : ℚ) ^ (m - 1) * (∑ j : Fin k, (count j : ℚ) ^ m) := by ring
      have hfinal_nat : (h ^ 2 - 4 * e) ^ m ≤
          N * PEqualNP.Outside.L_meta_25742_aux.dfact m * h ^ (m - 1) * (∑ j : Fin k, (count j) ^ m) := by
        exact_mod_cast hfinal_q
      exact hfinal_nat
  refine ⟨hpart1, ?_⟩
  intro a cap ha hNcap hcap
  by_cases hh0 : h = 0
  · rw [hh0]; simp
  · by_cases hle : h ^ 2 ≤ 4 * e
    · omega
    · have hp := hpart1 a ha
      have hdf : ∏ i ∈ Finset.range a, (2 * i + 1) ≤ a ^ a :=
        PEqualNP.Outside.L_meta_25742_aux.dfact_le_pow a
      have hsum_cap : ∑ j : Fin k, (count j) ^ a ≤ h * cap ^ (a - 1) := by
        calc ∑ j : Fin k, (count j) ^ a
            = ∑ j : Fin k, count j * (count j) ^ (a - 1) := by
              apply Finset.sum_congr rfl; intro j _
              conv_lhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
              ring
          _ ≤ ∑ j : Fin k, count j * cap ^ (a - 1) := by
              apply Finset.sum_le_sum; intro j _
              exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hcap j) _)
          _ = (∑ j : Fin k, count j) * cap ^ (a - 1) := (Finset.sum_mul _ _ _).symm
          _ = h * cap ^ (a - 1) := by rw [hcount_sum]
      have hpow_le : (h ^ 2 - 4 * e) ^ a ≤ (2 * a * cap * h) ^ a := by
        have h1 : N * (∏ i ∈ Finset.range a, (2 * i + 1)) * h ^ (a - 1) * (∑ j : Fin k, (count j) ^ a) ≤
            (2 ^ a * cap) * a ^ a * h ^ (a - 1) * (h * cap ^ (a - 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hNcap hdf) le_rfl) hsum_cap
        have h2 : (2 ^ a * cap) * a ^ a * h ^ (a - 1) * (h * cap ^ (a - 1)) = (2 * a * cap * h) ^ a := by
          have hhc : h ^ (a - 1) * h = h ^ a := by
            conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
          have hcc : cap * cap ^ (a - 1) = cap ^ a := by
            conv_rhs => rw [show a = (a - 1) + 1 by omega, pow_succ]
            ring
          calc (2 ^ a * cap) * a ^ a * h ^ (a - 1) * (h * cap ^ (a - 1))
              = 2 ^ a * a ^ a * (cap * cap ^ (a - 1)) * (h ^ (a - 1) * h) := by ring
            _ = 2 ^ a * a ^ a * cap ^ a * h ^ a := by rw [hcc, hhc]
            _ = (2 * a * cap * h) ^ a := by rw [mul_pow, mul_pow, mul_pow]
        exact le_trans hp (h2 ▸ h1)
      have hsub_le : h ^ 2 - 4 * e ≤ 2 * a * cap * h :=
        PEqualNP.Outside.L_meta_25742_aux.nat_le_of_pow_le_pow (by omega : a ≠ 0) hpow_le
      omega
