import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_602_aux

def dfact (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, (2 * j + 1)

lemma dfact_zero : dfact 0 = 1 := by
  simp [dfact]

lemma dfact_succ (n : ℕ) : dfact (n + 1) = dfact n * (2 * n + 1) := by
  simp [dfact, Finset.prod_range_succ]

lemma dfact_pos (n : ℕ) : 0 < dfact n := by
  induction n with
  | zero => simp [dfact_zero]
  | succ n ih =>
    rw [dfact_succ]
    exact Nat.mul_pos ih (by omega)

lemma dfact_cast (n : ℕ) :
    (dfact n : ℝ) = ∏ j ∈ Finset.range n, (2 * (j : ℝ) + 1) := by
  unfold dfact
  push_cast
  rfl

lemma factorial_two_mul (n : ℕ) :
    (2 * n).factorial = 2 ^ n * n.factorial * dfact n := by
  induction n with
  | zero => simp [dfact_zero]
  | succ n ih =>
    have h1 : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [h1, Nat.factorial_succ, Nat.factorial_succ, ih, dfact_succ, Nat.factorial_succ, Nat.pow_succ]
    ring

lemma choose_even_mul_dfact {m r : ℕ} (hrm : r ≤ m) :
    Nat.choose (2 * m) (2 * r) * dfact r ≤ Nat.choose m r * dfact m := by
  have heq : Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) = Nat.choose m r * dfact m := by
    have hpos : 0 < (2 * r).factorial * (2 * (m - r)).factorial :=
      Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
    apply Nat.eq_of_mul_eq_mul_right hpos
    have hsub : 2 * m - 2 * r = 2 * (m - r) := by omega
    have hcho1 : Nat.choose (2 * m) (2 * r) * ((2 * r).factorial * (2 * (m - r)).factorial) =
        (2 * m).factorial := by
      rw [← hsub, ← Nat.mul_assoc]
      exact Nat.choose_mul_factorial_mul_factorial (by omega : 2 * r ≤ 2 * m)
    have hcho2 : Nat.choose m r * (r.factorial * (m - r).factorial) = m.factorial := by
      rw [← Nat.mul_assoc]
      exact Nat.choose_mul_factorial_mul_factorial hrm
    have hpow : 2 ^ r * 2 ^ (m - r) = 2 ^ m := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hrm]
    calc Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) *
            ((2 * r).factorial * (2 * (m - r)).factorial)
        = (Nat.choose (2 * m) (2 * r) * ((2 * r).factorial * (2 * (m - r)).factorial)) *
            dfact r * dfact (m - r) := by ring
      _ = (2 * m).factorial * dfact r * dfact (m - r) := by rw [hcho1]
      _ = 2 ^ m * m.factorial * dfact m * dfact r * dfact (m - r) := by rw [factorial_two_mul]
      _ = (2 ^ r * 2 ^ (m - r)) * (Nat.choose m r * (r.factorial * (m - r).factorial)) *
            dfact m * dfact r * dfact (m - r) := by rw [hpow, hcho2]
      _ = Nat.choose m r * dfact m *
            ((2 ^ r * r.factorial * dfact r) * (2 ^ (m - r) * (m - r).factorial * dfact (m - r))) := by ring
      _ = Nat.choose m r * dfact m * ((2 * r).factorial * (2 * (m - r)).factorial) := by
            rw [← factorial_two_mul r, ← factorial_two_mul (m - r)]
  have h1 : 1 ≤ dfact (m - r) := dfact_pos (m - r)
  calc Nat.choose (2 * m) (2 * r) * dfact r
      = Nat.choose (2 * m) (2 * r) * dfact r * 1 := by ring
    _ ≤ Nat.choose (2 * m) (2 * r) * dfact r * dfact (m - r) :=
        Nat.mul_le_mul_left _ h1
    _ = Nat.choose m r * dfact m := heq

lemma chebyshev_pow {α : Type*} (S : Finset α) (a : α → ℝ) (ha : ∀ x ∈ S, 0 ≤ a x) (p : ℕ) :
    (∑ x ∈ S, a x) * (∑ y ∈ S, (a y) ^ p) ≤ (S.card : ℝ) * (∑ x ∈ S, (a x) ^ (p + 1)) := by
  have hnn : 0 ≤ ∑ x ∈ S, ∑ y ∈ S, (a x - a y) * ((a x) ^ p - (a y) ^ p) := by
    apply Finset.sum_nonneg
    intro x hx
    apply Finset.sum_nonneg
    intro y hy
    rcases le_total (a x) (a y) with hle | hle
    · have hp : (a x) ^ p ≤ (a y) ^ p := pow_le_pow_left₀ (ha x hx) hle p
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hle) (sub_nonpos.mpr hp)
    · have hp : (a y) ^ p ≤ (a x) ^ p := pow_le_pow_left₀ (ha y hy) hle p
      exact mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr hp)
  have hexp : ∑ x ∈ S, ∑ y ∈ S, (a x - a y) * ((a x) ^ p - (a y) ^ p) =
      2 * (S.card : ℝ) * (∑ x ∈ S, (a x) ^ (p + 1)) -
        2 * (∑ x ∈ S, a x) * (∑ y ∈ S, (a y) ^ p) := by
    have hterm : ∀ x y : α,
        (a x - a y) * ((a x) ^ p - (a y) ^ p) =
          (a x) ^ (p + 1) - a x * (a y) ^ p - a y * (a x) ^ p + (a y) ^ (p + 1) := by
      intro x y
      rw [pow_succ]
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Finset.mul_sum]
    ring
  linarith

lemma power_mean_nat {α : Type*} (S : Finset α) (a : α → ℝ) (ha : ∀ x ∈ S, 0 ≤ a x) :
    ∀ p : ℕ, 0 < p → (∑ x ∈ S, a x) ^ p ≤ (S.card : ℝ) ^ (p - 1) * (∑ x ∈ S, (a x) ^ p) := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ p ih =>
    intro _
    cases p with
    | zero =>
      simp
    | succ q =>
      have hih := ih (by omega)
      have hsum_nn : 0 ≤ ∑ x ∈ S, a x := Finset.sum_nonneg ha
      have hcard_nn : 0 ≤ (S.card : ℝ) ^ q := pow_nonneg (Nat.cast_nonneg _) q
      have hch := chebyshev_pow S a ha (q + 1)
      have hsub1 : q + 1 - 1 = q := by omega
      have hsub2 : q + 1 + 1 - 1 = q + 1 := by omega
      rw [hsub1] at hih
      rw [hsub2]
      calc (∑ x ∈ S, a x) ^ (q + 1 + 1)
          = (∑ x ∈ S, a x) * (∑ x ∈ S, a x) ^ (q + 1) := by rw [pow_succ, mul_comm]
        _ ≤ (∑ x ∈ S, a x) * ((S.card : ℝ) ^ q * (∑ x ∈ S, (a x) ^ (q + 1))) :=
            mul_le_mul_of_nonneg_left hih hsum_nn
        _ = (S.card : ℝ) ^ q * ((∑ x ∈ S, a x) * (∑ y ∈ S, (a y) ^ (q + 1))) := by ring
        _ ≤ (S.card : ℝ) ^ q * ((S.card : ℝ) * (∑ x ∈ S, (a x) ^ (q + 1 + 1))) :=
            mul_le_mul_of_nonneg_left hch hcard_nn
        _ = (S.card : ℝ) ^ (q + 1) * (∑ x ∈ S, (a x) ^ (q + 1 + 1)) := by
            rw [pow_succ]; ring

lemma add_pow_even_sum (y c : ℝ) (m : ℕ) :
    (y + c) ^ (2 * m) + (y - c) ^ (2 * m) =
      2 * ∑ r ∈ Finset.range (m + 1),
        (Nat.choose (2 * m) (2 * r) : ℝ) * y ^ (2 * r) * (c ^ 2) ^ (m - r) := by
  rw [add_pow, sub_eq_add_neg, add_pow, ← Finset.sum_add_distrib]
  have hpair : ∀ i ∈ Finset.range (2 * m + 1),
      y ^ i * c ^ (2 * m - i) * (Nat.choose (2 * m) i : ℝ) +
        y ^ i * (-c) ^ (2 * m - i) * (Nat.choose (2 * m) i : ℝ) =
      if Even i then
        2 * ((Nat.choose (2 * m) i : ℝ) * y ^ i * c ^ (2 * m - i))
      else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    by_cases hev : Even i
    · have hev2 : Even (2 * m - i) := by
        rcases hev with ⟨t, rfl⟩
        exact ⟨m - t, by omega⟩
      simp only [hev, ite_true, hev2.neg_pow]
      ring
    · have hodd2 : Odd (2 * m - i) := by
        rw [Nat.not_even_iff_odd] at hev
        rcases hev with ⟨t, rfl⟩
        exact ⟨m - t - 1, by omega⟩
      simp only [hev, ite_false, hodd2.neg_pow]
      ring
  rw [Finset.sum_congr rfl hpair, ← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_nbij (fun r => 2 * r)
  · intro r hr
    rw [Finset.mem_range] at hr
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, ⟨r, by omega⟩⟩
  · intro r1 _ r2 _ heq
    dsimp only at heq
    omega
  · intro i hi
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
    rcases hi.2 with ⟨r, hr⟩
    refine ⟨r, ?_, by dsimp only; omega⟩
    rw [Finset.mem_coe, Finset.mem_range]
    omega
  · intro r hr
    rw [Finset.mem_range] at hr
    have hpow : (c ^ 2) ^ (m - r) = c ^ (2 * m - 2 * r) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow]

def rbit (x j : ℕ) : ℝ :=
  if x.testBit j then (-1 : ℝ) else 1

lemma testBit_two_pow_add_lt {k y j : ℕ} (hjk : j < k) :
    (2 ^ k + y).testBit j = y.testBit j := by
  have hpow : 2 ^ k = 2 ^ j * 2 ^ (k - j) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hjk)]
  have heven : 2 ^ (k - j) % 2 = 0 := by
    have h1 : k - j = (k - j - 1) + 1 := by omega
    rw [h1, Nat.pow_succ]
    omega
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hpow,
      Nat.mul_add_div (Nat.two_pow_pos j)]
  have hmod : (2 ^ (k - j) + y / 2 ^ j) % 2 = (y / 2 ^ j) % 2 := by omega
  rw [hmod]

lemma testBit_two_pow_add_self {k y : ℕ} (hy : y < 2 ^ k) :
    (2 ^ k + y).testBit k = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h1 : 2 ^ k + y = 2 ^ k * 1 + y := by omega
  rw [h1, Nat.mul_add_div (Nat.two_pow_pos k), Nat.div_eq_of_lt hy]
  rfl

lemma cube_even_moment : ∀ (k : ℕ) (m : ℕ) (v : Fin k → ℝ),
    ∑ x : Fin (2 ^ k), (∑ j : Fin k, v j * rbit x.val j.val) ^ (2 * m) ≤
      ((2 ^ k : ℕ) : ℝ) * (dfact m : ℝ) * (∑ j : Fin k, (v j) ^ 2) ^ m := by
  intro k
  induction k with
  | zero =>
    intro m v
    cases m with
    | zero => simp [dfact_zero]
    | succ m =>
      have h0 : (0 : ℝ) ^ (2 * (m + 1)) = 0 := zero_pow (by omega)
      simp [h0]
  | succ k ih =>
    intro m v
    let v' : Fin k → ℝ := fun j => v ⟨j.val, by omega⟩
    let c : ℝ := v ⟨k, by omega⟩
    let eSplit : Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k) × Bool :=
      { toFun := fun x => (⟨x.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩, decide (2 ^ k ≤ x.val))
        invFun := fun p => ⟨p.1.val + if p.2 then 2 ^ k else 0, by
          cases p.2
          · simp; exact lt_of_lt_of_le p.1.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
          · simp only [ite_true]; rw [Nat.pow_succ]; have := p.1.isLt; omega⟩
        left_inv := fun x => by
          apply Fin.ext
          dsimp only
          have hx : x.val < 2 * 2 ^ k := by
            have h1 : x.val < 2 ^ (k + 1) := x.isLt
            have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
            omega
          by_cases h : 2 ^ k ≤ x.val
          · simp only [h, decide_true, ite_true]
            have hmod : x.val % 2 ^ k = x.val - 2 ^ k := by
              have h1 : x.val = (x.val - 2 ^ k) + 2 ^ k := by omega
              conv_lhs => rw [h1]
              rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
          · simp only [h, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
            exact Nat.mod_eq_of_lt (by omega)
        right_inv := fun ⟨y, b⟩ => by
          apply Prod.ext
          · apply Fin.ext
            dsimp only
            cases b
            · simp [Nat.mod_eq_of_lt y.isLt]
            · simp [Nat.add_mod_right, Nat.mod_eq_of_lt y.isLt]
          · dsimp only
            cases b
            · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
              have hlt : ¬ (2 ^ k ≤ y.val) := by have := y.isLt; omega
              exact decide_eq_false hlt
            · simp only [ite_true]
              have hge : 2 ^ k ≤ y.val + 2 ^ k := Nat.le_add_left _ _
              exact decide_eq_true hge }
    have hsplit_sum :
        ∑ x : Fin (2 ^ (k + 1)), (∑ j : Fin (k + 1), v j * rbit x.val j.val) ^ (2 * m) =
        ∑ y : Fin (2 ^ k),
          ((∑ j : Fin k, v' j * rbit y.val j.val + c) ^ (2 * m) +
           (∑ j : Fin k, v' j * rbit y.val j.val - c) ^ (2 * m)) := by
      rw [Fintype.sum_equiv eSplit _ (fun p => (∑ j : Fin (k + 1), v j * rbit (eSplit.symm p).val j.val) ^ (2 * m))
        (fun x => by simp)]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro y _
      rw [Fintype.sum_bool, add_comm]
      have hterm : ∀ b : Bool,
          ∑ j : Fin (k + 1), v j * rbit (eSplit.symm (y, b)).val j.val =
            (∑ j : Fin k, v' j * rbit y.val j.val) + (if b then -c else c) := by
        intro b
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro j _
          have hval : (eSplit.symm (y, b)).val = y.val + if b then 2 ^ k else 0 := rfl
          have hcs : j.castSucc = ⟨j.val, by omega⟩ := rfl
          dsimp only [v', rbit]
          rw [hval, hcs]
          have htb : (y.val + if b then 2 ^ k else 0).testBit j.val = y.val.testBit j.val := by
            cases b
            · simp
            · simp only [ite_true]
              rw [Nat.add_comm]
              exact testBit_two_pow_add_lt j.isLt
          rw [htb]
        · have hval : (eSplit.symm (y, b)).val = y.val + if b then 2 ^ k else 0 := rfl
          dsimp only [c, rbit, Fin.last]
          rw [hval]
          have htb : (y.val + if b then 2 ^ k else 0).testBit k = b := by
            cases b
            · simp [Nat.testBit_lt_two_pow y.isLt]
            · simp only [ite_true]
              rw [Nat.add_comm]
              exact testBit_two_pow_add_self y.isLt
          rw [htb]
          cases b <;> simp
      rw [hterm false, hterm true]
      simp [sub_eq_add_neg]
    rw [hsplit_sum]
    simp_rw [add_pow_even_sum]
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hstep :
        2 * ∑ r ∈ Finset.range (m + 1),
          ∑ y : Fin (2 ^ k),
            (Nat.choose (2 * m) (2 * r) : ℝ) *
              (∑ j : Fin k, v' j * rbit y.val j.val) ^ (2 * r) * (c ^ 2) ^ (m - r) ≤
        2 * ∑ r ∈ Finset.range (m + 1),
          ((2 ^ k : ℕ) : ℝ) * (Nat.choose m r : ℝ) * (dfact m : ℝ) *
            (∑ j : Fin k, (v' j) ^ 2) ^ r * (c ^ 2) ^ (m - r) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro r hr
      rw [Finset.mem_range] at hr
      have hfactor :
          ∑ y : Fin (2 ^ k),
            (Nat.choose (2 * m) (2 * r) : ℝ) *
              (∑ j : Fin k, v' j * rbit y.val j.val) ^ (2 * r) * (c ^ 2) ^ (m - r) =
          (Nat.choose (2 * m) (2 * r) : ℝ) * (c ^ 2) ^ (m - r) *
            ∑ y : Fin (2 ^ k), (∑ j : Fin k, v' j * rbit y.val j.val) ^ (2 * r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [hfactor]
      have hih := ih r v'
      have hcoeff_nn : 0 ≤ (Nat.choose (2 * m) (2 * r) : ℝ) * (c ^ 2) ^ (m - r) :=
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sq_nonneg c) _)
      have h1 := mul_le_mul_of_nonneg_left hih hcoeff_nn
      have hcho : (Nat.choose (2 * m) (2 * r) : ℝ) * (dfact r : ℝ) ≤
          (Nat.choose m r : ℝ) * (dfact m : ℝ) := by
        exact_mod_cast choose_even_mul_dfact (by omega : r ≤ m)
      have hE_nn : 0 ≤ ((2 ^ k : ℕ) : ℝ) * (∑ j : Fin k, (v' j) ^ 2) ^ r * (c ^ 2) ^ (m - r) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) _))
          (pow_nonneg (sq_nonneg c) _)
      have h2 := mul_le_mul_of_nonneg_right hcho hE_nn
      linarith
    have hrhs :
        2 * ∑ r ∈ Finset.range (m + 1),
          ((2 ^ k : ℕ) : ℝ) * (Nat.choose m r : ℝ) * (dfact m : ℝ) *
            (∑ j : Fin k, (v' j) ^ 2) ^ r * (c ^ 2) ^ (m - r) =
        ((2 ^ (k + 1) : ℕ) : ℝ) * (dfact m : ℝ) * (∑ j : Fin (k + 1), (v j) ^ 2) ^ m := by
      rw [Fin.sum_univ_castSucc]
      change _ = ((2 ^ (k + 1) : ℕ) : ℝ) * (dfact m : ℝ) * ((∑ j : Fin k, (v' j) ^ 2) + c ^ 2) ^ m
      rw [add_pow, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [Nat.pow_succ]
      push_cast
      ring
    linarith

end PEqualNP.Outside.L_lib_602_aux

theorem PEqualNP.Outside.L_lib_602 :
∀ (k m : ℕ), 0 < m →
  let N := 2^k
  ∀ (S : Finset (Fin N)) (b : Fin N → Bool),
    let v := fun (j : Fin k) =>
      ∑ x ∈ S, if xor (b x) (x.val.testBit j.val) then (-1 : ℝ) else 1
    let energy := ∑ j : Fin k, (v j)^2
    energy^m ≤ (N : ℝ) * (S.card : ℝ)^(2*m-1) * (∏ j ∈ Finset.range m, (2*(j:ℝ)+1)) := by
  intro k m hm
  dsimp only
  intro S b
  set v : Fin k → ℝ := fun j =>
    ∑ x ∈ S, if xor (b x) (x.val.testBit j.val) then (-1 : ℝ) else 1
  set energy : ℝ := ∑ j : Fin k, (v j) ^ 2
  have henergy_nn : 0 ≤ energy := Finset.sum_nonneg (fun j _ => sq_nonneg (v j))
  rw [← PEqualNP.Outside.L_lib_602_aux.dfact_cast]
  by_cases hE0 : energy = 0
  · rw [hE0, zero_pow (Nat.ne_of_gt hm)]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)
  · have hEpos : 0 < energy := lt_of_le_of_ne henergy_nn (Ne.symm hE0)
    have hEm_pos : 0 < energy ^ m := pow_pos hEpos m
    let σ : Fin (2 ^ k) → ℝ := fun x => if b x then (-1 : ℝ) else 1
    let g : Fin (2 ^ k) → ℝ := fun x => ∑ j : Fin k, v j * PEqualNP.Outside.L_lib_602_aux.rbit x.val j.val
    have hv_eq : ∀ j : Fin k, v j = ∑ x ∈ S, σ x * PEqualNP.Outside.L_lib_602_aux.rbit x.val j.val := by
      intro j
      apply Finset.sum_congr rfl
      intro x _
      dsimp only [σ, PEqualNP.Outside.L_lib_602_aux.rbit]
      cases b x <;> cases x.val.testBit j.val <;> norm_num
    have hE_sum : energy = ∑ x ∈ S, σ x * g x := by
      calc energy = ∑ j : Fin k, v j * v j := by
              apply Finset.sum_congr rfl; intro j _; rw [sq]
        _ = ∑ j : Fin k, v j * ∑ x ∈ S, σ x * PEqualNP.Outside.L_lib_602_aux.rbit x.val j.val := by
              apply Finset.sum_congr rfl; intro j _; rw [hv_eq j]
        _ = ∑ j : Fin k, ∑ x ∈ S, σ x * (v j * PEqualNP.Outside.L_lib_602_aux.rbit x.val j.val) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro x _
              ring
        _ = ∑ x ∈ S, ∑ j : Fin k, σ x * (v j * PEqualNP.Outside.L_lib_602_aux.rbit x.val j.val) :=
              Finset.sum_comm
        _ = ∑ x ∈ S, σ x * g x := by
              apply Finset.sum_congr rfl
              intro x _
              rw [← Finset.mul_sum]
    have hE_le_abs : energy ≤ ∑ x ∈ S, |g x| := by
      rw [hE_sum]
      apply Finset.sum_le_sum
      intro x _
      have h1 : σ x * g x ≤ |σ x * g x| := le_abs_self _
      have h2 : |σ x * g x| = |g x| := by
        rw [abs_mul]
        dsimp only [σ]
        cases b x <;> norm_num
      linarith
    have hpow_le : energy ^ (2 * m) ≤ (∑ x ∈ S, |g x|) ^ (2 * m) :=
      pow_le_pow_left₀ henergy_nn hE_le_abs (2 * m)
    have hpm := PEqualNP.Outside.L_lib_602_aux.power_mean_nat S (fun x => |g x|)
      (fun x _ => abs_nonneg _) (2 * m) (by omega)
    have habs_pow : ∑ x ∈ S, |g x| ^ (2 * m) = ∑ x ∈ S, (g x) ^ (2 * m) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [pow_mul, sq_abs, ← pow_mul]
    have hsub_cube : ∑ x ∈ S, (g x) ^ (2 * m) ≤ ∑ x : Fin (2 ^ k), (g x) ^ (2 * m) := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro x
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) m
    have hcube := PEqualNP.Outside.L_lib_602_aux.cube_even_moment k m v
    have hbig : energy ^ (2 * m) ≤
        ((2 ^ k : ℕ) : ℝ) * (S.card : ℝ) ^ (2 * m - 1) *
          (PEqualNP.Outside.L_lib_602_aux.dfact m : ℝ) * energy ^ m := by
      have hcard_nn : 0 ≤ (S.card : ℝ) ^ (2 * m - 1) := pow_nonneg (Nat.cast_nonneg _) _
      calc energy ^ (2 * m)
          ≤ (∑ x ∈ S, |g x|) ^ (2 * m) := hpow_le
        _ ≤ (S.card : ℝ) ^ (2 * m - 1) * (∑ x ∈ S, |g x| ^ (2 * m)) := hpm
        _ = (S.card : ℝ) ^ (2 * m - 1) * (∑ x ∈ S, (g x) ^ (2 * m)) := by rw [habs_pow]
        _ ≤ (S.card : ℝ) ^ (2 * m - 1) * (∑ x : Fin (2 ^ k), (g x) ^ (2 * m)) :=
              mul_le_mul_of_nonneg_left hsub_cube hcard_nn
        _ ≤ (S.card : ℝ) ^ (2 * m - 1) *
              (((2 ^ k : ℕ) : ℝ) * (PEqualNP.Outside.L_lib_602_aux.dfact m : ℝ) * energy ^ m) :=
              mul_le_mul_of_nonneg_left hcube hcard_nn
        _ = ((2 ^ k : ℕ) : ℝ) * (S.card : ℝ) ^ (2 * m - 1) *
              (PEqualNP.Outside.L_lib_602_aux.dfact m : ℝ) * energy ^ m := by ring
    have h2m : energy ^ (2 * m) = energy ^ m * energy ^ m := by
      rw [two_mul, pow_add]
    rw [h2m] at hbig
    exact le_of_mul_le_mul_right hbig hEm_pos
