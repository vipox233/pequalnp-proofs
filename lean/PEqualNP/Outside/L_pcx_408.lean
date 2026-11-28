import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_408_aux

lemma pow_mul_choose_ge (N t : ℕ) (ht : t ≤ N) :
    N ^ t ≤ t ^ t * Nat.choose N t := by
  have hfac : 0 < t.factorial := Nat.factorial_pos t
  apply Nat.le_of_mul_le_mul_right _ hfac
  have h1 : N ^ t * t.factorial = ∏ i ∈ Finset.range t, (N * (t - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    clear ht hfac
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ']
      simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
      rw [← ih, Nat.factorial_succ, mul_comm]
  have hdesc : N.descFactorial t = ∏ i ∈ Finset.range t, (N - i) := by
    clear ht hfac h1
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, Finset.prod_range_succ, ← ih, mul_comm]
  have h2 : t ^ t * Nat.choose N t * t.factorial = ∏ i ∈ Finset.range t, (t * (N - i)) := by
    rw [mul_assoc, mul_comm (Nat.choose N t), ← Nat.descFactorial_eq_factorial_mul_choose,
      hdesc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h1, h2]
  apply Finset.prod_le_prod
  intro i hi
  have hi' : i < t := Finset.mem_range.mp hi
  have hle : i ≤ t := le_of_lt hi'
  have hleN : i ≤ N := le_trans hle ht
  zify [hle, hleN]
  nlinarith

lemma factorial_mul_choose_le_pow (M r : ℕ) :
    r.factorial * Nat.choose M r ≤ M ^ r := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow M r

lemma two_pow_pred_le_factorial : ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ k.factorial := by
  intro k hk
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m' =>
      have hm : 1 ≤ m' + 1 := by omega
      have h1 := ih hm
      simp only [Nat.add_sub_cancel] at h1 ⊢
      rw [Nat.factorial_succ, pow_succ']
      have h2 : 2 ≤ m' + 2 := by omega
      exact Nat.mul_le_mul h2 h1

lemma succ_pow_le_three_mul_pow (r : ℕ) : (r + 1) ^ r ≤ 3 * r ^ r := by
  cases r with
  | zero => simp
  | succ m =>
    set r := m + 1
    have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
    apply Nat.le_of_mul_le_mul_left _ hpos
    rw [Nat.add_comm r 1, add_pow]
    simp only [one_pow, one_mul, Nat.cast_id]
    rw [Finset.mul_sum, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range r, 2 ^ r * (r ^ (r - (k + 1)) * Nat.choose r (k + 1)) ≤
        ∑ k ∈ Finset.range r, 2 ^ (r - k) * r ^ r := by
      apply Finset.sum_le_sum
      intro k hk
      have hkr : k < r := Finset.mem_range.mp hk
      have hfac := two_pow_pred_le_factorial (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hfac
      have hch := factorial_mul_choose_le_pow r (k + 1)
      have hstep : 2 ^ k * Nat.choose r (k + 1) ≤ r ^ (k + 1) :=
        le_trans (Nat.mul_le_mul_right _ hfac) hch
      have hpow2 : 2 ^ r = 2 ^ (r - k) * 2 ^ k := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hkr)]
      have hpowr : r ^ (r - (k + 1)) * r ^ (k + 1) = r ^ r := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      calc 2 ^ r * (r ^ (r - (k + 1)) * Nat.choose r (k + 1))
          = 2 ^ (r - k) * (r ^ (r - (k + 1)) * (2 ^ k * Nat.choose r (k + 1))) := by
            rw [hpow2]; ring
        _ ≤ 2 ^ (r - k) * (r ^ (r - (k + 1)) * r ^ (k + 1)) := by gcongr
        _ = 2 ^ (r - k) * r ^ r := by rw [hpowr]
    have hgeo : ∑ k ∈ Finset.range r, 2 ^ (r - k) ≤ 2 * 2 ^ r := by
      clear hsum hpos
      induction r with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ']
        simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
        have h1 : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
        omega
    calc ∑ k ∈ Finset.range r, 2 ^ r * (r ^ (r - (k + 1)) * Nat.choose r (k + 1)) +
          2 ^ r * r ^ r
        ≤ ∑ k ∈ Finset.range r, 2 ^ (r - k) * r ^ r + 2 ^ r * r ^ r := by gcongr
      _ = (∑ k ∈ Finset.range r, 2 ^ (r - k)) * r ^ r + 2 ^ r * r ^ r := by
          rw [Finset.sum_mul]
      _ ≤ (2 * 2 ^ r) * r ^ r + 2 ^ r * r ^ r := by gcongr
      _ = 2 ^ r * (3 * r ^ r) := by ring

lemma three_pow_mul_factorial_ge_pow (r : ℕ) : r ^ r ≤ 3 ^ r * r.factorial := by
  induction r with
  | zero => simp
  | succ m ih =>
    have h1 := succ_pow_le_three_mul_pow m
    calc (m + 1) ^ (m + 1) = (m + 1) * (m + 1) ^ m := by rw [pow_succ']
      _ ≤ (m + 1) * (3 * m ^ m) := Nat.mul_le_mul_left _ h1
      _ ≤ (m + 1) * (3 * (3 ^ m * m.factorial)) := by gcongr
      _ = 3 ^ (m + 1) * (m + 1).factorial := by
          rw [pow_succ', Nat.factorial_succ]; ring

lemma choose_le_choose_succ (N k : ℕ) (hk : 2 * k + 1 ≤ N) :
    Nat.choose N k ≤ Nat.choose N (k + 1) := by
  have hf1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ N by omega)
  have hf2 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ N by omega)
  have hsub : N - k = (N - (k + 1)) + 1 := by omega
  have heq : (k + 1) * Nat.choose N (k + 1) * (k.factorial * (N - (k + 1)).factorial) =
      (N - k) * Nat.choose N k * (k.factorial * (N - (k + 1)).factorial) := by
    calc (k + 1) * Nat.choose N (k + 1) * (k.factorial * (N - (k + 1)).factorial)
        = Nat.choose N (k + 1) * (k + 1).factorial * (N - (k + 1)).factorial := by
          rw [Nat.factorial_succ]; ring
      _ = N.factorial := hf2
      _ = Nat.choose N k * k.factorial * (N - k).factorial := hf1.symm
      _ = (N - k) * Nat.choose N k * (k.factorial * (N - (k + 1)).factorial) := by
          rw [hsub, Nat.factorial_succ, ← hsub]; ring
  have hpos : 0 < k.factorial * (N - (k + 1)).factorial := by
    exact Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (N - (k + 1)))
  have hmul : (k + 1) * Nat.choose N (k + 1) = (N - k) * Nat.choose N k :=
    Nat.eq_of_mul_eq_mul_right hpos heq
  have h1 : k + 1 ≤ N - k := by omega
  have h2 : (k + 1) * Nat.choose N k ≤ (k + 1) * Nat.choose N (k + 1) := by
    rw [hmul]; exact Nat.mul_le_mul_right _ h1
  exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos k)

lemma choose_mono_half (N t a : ℕ) (hta : t ≤ a) (ha : 2 * a ≤ N) :
    Nat.choose N t ≤ Nat.choose N a := by
  induction a with
  | zero =>
    have : t = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    by_cases htk : t ≤ k
    · exact le_trans (ih htk (by omega)) (choose_le_choose_succ N k (by omega))
    · have : t = k + 1 := by omega
      subst this; exact le_rfl

lemma choose_le_choose_of_mid (N t a : ℕ) (h1 : t ≤ a) (h2 : a + t ≤ N) :
    Nat.choose N t ≤ Nat.choose N a := by
  by_cases ha : 2 * a ≤ N
  · exact choose_mono_half N t a h1 ha
  · have hsym : Nat.choose N a = Nat.choose N (N - a) := by
      rw [Nat.choose_symm (by omega)]
    rw [hsym]
    exact choose_mono_half N t (N - a) (by omega) (by omega)

lemma key_binom_ineq (N r : ℕ) (hr : 1 ≤ r) (hN : 64 * r ≤ N) :
    2 ^ r * 4 * (r + 1) ^ 3 * Nat.choose (4 * N) r * (Nat.choose N r) ^ 2 * 2 <
      (Nat.choose N (16 * r)) ^ 2 := by
  have hrpos : 0 < r := by omega
  have hNpos : 0 < N := by omega
  have hfac3 : r ^ (3 * r) ≤ 27 ^ r * r.factorial ^ 3 := by
    have h := three_pow_mul_factorial_ge_pow r
    have h3 : (r ^ r) ^ 3 ≤ (3 ^ r * r.factorial) ^ 3 := Nat.pow_le_pow_left h 3
    calc r ^ (3 * r) = (r ^ r) ^ 3 := by rw [← pow_mul, mul_comm]
      _ ≤ (3 ^ r * r.factorial) ^ 3 := h3
      _ = 27 ^ r * r.factorial ^ 3 := by
          rw [mul_pow, ← pow_mul, mul_comm r 3, pow_mul]
          norm_num
  have hch1 : r.factorial * Nat.choose (4 * N) r ≤ (4 * N) ^ r :=
    factorial_mul_choose_le_pow (4 * N) r
  have hch2 : (r.factorial * Nat.choose N r) ^ 2 ≤ (N ^ r) ^ 2 :=
    Nat.pow_le_pow_left (factorial_mul_choose_le_pow N r) 2
  have htop : r ^ (3 * r) * (Nat.choose (4 * N) r * (Nat.choose N r) ^ 2) ≤
      108 ^ r * N ^ (3 * r) := by
    calc r ^ (3 * r) * (Nat.choose (4 * N) r * (Nat.choose N r) ^ 2)
        ≤ (27 ^ r * r.factorial ^ 3) * (Nat.choose (4 * N) r * (Nat.choose N r) ^ 2) :=
          Nat.mul_le_mul_right _ hfac3
      _ = 27 ^ r * ((r.factorial * Nat.choose (4 * N) r) * (r.factorial * Nat.choose N r) ^ 2) := by
          ring
      _ ≤ 27 ^ r * ((4 * N) ^ r * (N ^ r) ^ 2) := by gcongr
      _ = 108 ^ r * N ^ (3 * r) := by
          rw [mul_pow, ← pow_mul]
          have h108 : (27 : ℕ) ^ r * 4 ^ r = 108 ^ r := by rw [← mul_pow]; norm_num
          have hN3 : N ^ r * N ^ (r * 2) = N ^ (3 * r) := by rw [← pow_add]; congr 1; ring
          calc 27 ^ r * (4 ^ r * N ^ r * N ^ (r * 2))
              = (27 ^ r * 4 ^ r) * (N ^ r * N ^ (r * 2)) := by ring
            _ = 108 ^ r * N ^ (3 * r) := by rw [h108, hN3]
  have hbot1 : N ^ (16 * r) ≤ (16 * r) ^ (16 * r) * Nat.choose N (16 * r) :=
    pow_mul_choose_ge N (16 * r) (by omega)
  have hbot : N ^ (32 * r) ≤ (16 * r) ^ (32 * r) * (Nat.choose N (16 * r)) ^ 2 := by
    have h2 := Nat.pow_le_pow_left hbot1 2
    rw [mul_pow, ← pow_mul, ← pow_mul] at h2
    have e1 : 16 * r * 2 = 32 * r := by ring
    rwa [e1] at h2
  have hmulpos : 0 < r ^ (3 * r) * (16 * r) ^ (32 * r) := by positivity
  apply Nat.lt_of_mul_lt_mul_left (a := r ^ (3 * r) * (16 * r) ^ (32 * r))
  have hr1 : r + 1 ≤ 2 ^ r := by
    clear hN hfac3 hch1 hch2 htop hbot1 hbot hmulpos
    induction r with
    | zero => omega
    | succ m ih =>
      cases m with
      | zero => simp
      | succ m' =>
        have h := ih (by omega)
        rw [pow_succ']
        omega
  have hr1cube : 8 * (r + 1) ^ 3 ≤ 64 ^ r := by
    have hc : (r + 1) ^ 3 ≤ (2 ^ r) ^ 3 := Nat.pow_le_pow_left hr1 3
    have h8 : 8 ≤ 8 ^ r := by
      have : 8 ^ 1 ≤ 8 ^ r := Nat.pow_le_pow_right (by omega) hr
      simpa using this
    calc 8 * (r + 1) ^ 3 ≤ 8 ^ r * (2 ^ r) ^ 3 := Nat.mul_le_mul h8 hc
      _ = 64 ^ r := by
          rw [← pow_mul, mul_comm r 3, pow_mul, ← mul_pow]
          norm_num
  have hconst : 64 * 2 * 108 * 16 ^ 32 < 64 ^ 29 := by decide
  have hconst_r : (64 * 2 * 108 * 16 ^ 32) ^ r < (64 ^ 29) ^ r :=
    Nat.pow_lt_pow_left hconst (by omega)
  have hNpow : (64 ^ 29) ^ r * r ^ (29 * r) ≤ N ^ (29 * r) := by
    calc (64 ^ 29) ^ r * r ^ (29 * r) = (64 * r) ^ (29 * r) := by
          rw [← pow_mul, mul_pow]
      _ ≤ N ^ (29 * r) := Nat.pow_le_pow_left hN (29 * r)
  have hN32 : N ^ (3 * r) * N ^ (29 * r) = N ^ (32 * r) := by
    rw [← pow_add]; congr 1; ring
  have h16split : (16 * r) ^ (32 * r) = (16 ^ 32) ^ r * (r ^ (3 * r) * r ^ (29 * r)) := by
    rw [mul_pow, ← pow_mul, ← pow_add]
    congr 1; congr 1; ring
  have hLHS : r ^ (3 * r) * (16 * r) ^ (32 * r) *
      (2 ^ r * 4 * (r + 1) ^ 3 * Nat.choose (4 * N) r * (Nat.choose N r) ^ 2 * 2) ≤
      (64 * 2 * 108 * 16 ^ 32) ^ r * (r ^ (3 * r) * r ^ (29 * r) * N ^ (3 * r)) := by
    calc r ^ (3 * r) * (16 * r) ^ (32 * r) *
          (2 ^ r * 4 * (r + 1) ^ 3 * Nat.choose (4 * N) r * (Nat.choose N r) ^ 2 * 2)
        = (8 * (r + 1) ^ 3) * 2 ^ r * (16 * r) ^ (32 * r) *
          (r ^ (3 * r) * (Nat.choose (4 * N) r * (Nat.choose N r) ^ 2)) := by ring
      _ ≤ 64 ^ r * 2 ^ r * (16 * r) ^ (32 * r) * (108 ^ r * N ^ (3 * r)) := by gcongr
      _ = (64 ^ r * 2 ^ r * 108 ^ r * (16 ^ 32) ^ r) *
          (r ^ (3 * r) * r ^ (29 * r) * N ^ (3 * r)) := by rw [h16split]; ring
      _ = (64 * 2 * 108 * 16 ^ 32) ^ r * (r ^ (3 * r) * r ^ (29 * r) * N ^ (3 * r)) := by
          simp only [mul_pow]
  have hRHS : (64 ^ 29) ^ r * (r ^ (3 * r) * r ^ (29 * r) * N ^ (3 * r)) ≤
      r ^ (3 * r) * (16 * r) ^ (32 * r) * (Nat.choose N (16 * r)) ^ 2 := by
    calc (64 ^ 29) ^ r * (r ^ (3 * r) * r ^ (29 * r) * N ^ (3 * r))
        = r ^ (3 * r) * (N ^ (3 * r) * ((64 ^ 29) ^ r * r ^ (29 * r))) := by ring
      _ ≤ r ^ (3 * r) * (N ^ (3 * r) * N ^ (29 * r)) := by gcongr
      _ = r ^ (3 * r) * N ^ (32 * r) := by rw [hN32]
      _ ≤ r ^ (3 * r) * ((16 * r) ^ (32 * r) * (Nat.choose N (16 * r)) ^ 2) :=
          Nat.mul_le_mul_left _ hbot
      _ = r ^ (3 * r) * (16 * r) ^ (32 * r) * (Nat.choose N (16 * r)) ^ 2 := by ring
  have hmid : 0 < r ^ (3 * r) * r ^ (29 * r) * N ^ (3 * r) := by positivity
  exact lt_of_le_of_lt hLHS (lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hconst_r hmid) hRHS)

def railMass (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) : ℕ :=
  (Finset.univ.filter (fun u : Bool × (Bool × Fin N) => y u = true)).card

def railRed (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Bool × Fin N => y (false, i) ≠ y (true, i))).card

def railBlue (N : ℕ) [NeZero N] (y : Bool × (Bool × Fin N) → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Bool × Fin N =>
    y (false, i) ≠ y (true, (i.1, i.2 + 1)))).card

def railCross0 (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) (p0 : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter (fun k : Fin N =>
    y (false, (false, k)) ≠ y (true, (true, p0 k)))).card

def railCross1 (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) (p1 : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter (fun k : Fin N =>
    y (false, (true, k)) ≠ y (true, (false, p1 k)))).card

def mkCrossPerm (N : ℕ) (p0 p1 : Equiv.Perm (Fin N)) : Equiv.Perm (Bool × Fin N) where
  toFun := fun i => if i.1 then (false, p1 i.2) else (true, p0 i.2)
  invFun := fun i => if i.1 then (false, p0.symm i.2) else (true, p1.symm i.2)
  left_inv := by
    intro ⟨b, k⟩
    cases b <;> simp
  right_inv := by
    intro ⟨b, k⟩
    cases b <;> simp

lemma mkCrossPerm_fst (N : ℕ) (p0 p1 : Equiv.Perm (Fin N)) (i : Bool × Fin N) :
    (mkCrossPerm N p0 p1 i).1 = !i.1 := by
  rcases i with ⟨b, k⟩
  cases b <;> rfl

lemma card_filter_le_of_finset_sum {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) :
    (Finset.univ.filter (fun S : Finset α => S.card ≤ r)).card =
      ∑ k ∈ Finset.range (r + 1), Nat.choose (Fintype.card α) k := by
  have h : Finset.univ.filter (fun S : Finset α => S.card ≤ r) =
      (Finset.range (r + 1)).biUnion (fun k => Finset.powersetCard k (Finset.univ : Finset α)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro hS; exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨k, hk, hcard⟩; omega
  rw [h, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro S hi hj
    rw [Finset.mem_powersetCard] at hi hj
    exact hij (hi.2.symm.trans hj.2)

lemma sum_choose_le (M r : ℕ) (hr : 2 * r ≤ M) :
    ∑ k ∈ Finset.range (r + 1), Nat.choose M k ≤ (r + 1) * Nat.choose M r := by
  calc ∑ k ∈ Finset.range (r + 1), Nat.choose M k
      ≤ ∑ _k ∈ Finset.range (r + 1), Nat.choose M r := by
        apply Finset.sum_le_sum
        intro k hk
        exact choose_mono_half M k r (by have := Finset.mem_range.mp hk; omega) hr
    _ = (r + 1) * Nat.choose M r := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma bdry_inj_rail (N : ℕ) [NeZero N] (hN : 0 < N)
    (y1 y2 : Bool × (Bool × Fin N) → Bool)
    (h0 : y1 (true, (false, ⟨0, hN⟩)) = y2 (true, (false, ⟨0, hN⟩)))
    (h1 : y1 (true, (true, ⟨0, hN⟩)) = y2 (true, (true, ⟨0, hN⟩)))
    (hred : ∀ i : Bool × Fin N,
      (y1 (false, i) ≠ y1 (true, i)) ↔ (y2 (false, i) ≠ y2 (true, i)))
    (hblue : ∀ i : Bool × Fin N,
      (y1 (false, i) ≠ y1 (true, (i.1, i.2 + 1))) ↔
        (y2 (false, i) ≠ y2 (true, (i.1, i.2 + 1)))) :
    y1 = y2 := by
  have hstep : ∀ (a b c d : Bool), a = c → ((b ≠ a) ↔ (d ≠ c)) → b = d := by
    intro a b c d hac hiff
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  have hrail : ∀ (r : Bool) (k : ℕ) (hk : k < N),
      y1 (true, (r, ⟨k, hk⟩)) = y2 (true, (r, ⟨k, hk⟩)) ∧
      y1 (false, (r, ⟨k, hk⟩)) = y2 (false, (r, ⟨k, hk⟩)) := by
    intro r k
    induction k with
    | zero =>
      intro hk
      have ht : y1 (true, (r, ⟨0, hk⟩)) = y2 (true, (r, ⟨0, hk⟩)) := by
        cases r
        · exact h0
        · exact h1
      exact ⟨ht, hstep _ _ _ _ ht (hred (r, ⟨0, hk⟩))⟩
    | succ m ih =>
      intro hk
      have hm : m < N := by omega
      have hprev := ih hm
      have hsucc : (⟨m, hm⟩ : Fin N) + 1 = ⟨m + 1, hk⟩ := by
        apply Fin.ext
        have h1' : (1 : Fin N).val = 1 % N := rfl
        have hmod : (m + 1 % N) % N = m + 1 := by
          by_cases hN1 : N = 1
          · omega
          · rw [Nat.mod_eq_of_lt (by omega : 1 < N), Nat.mod_eq_of_lt hk]
        exact hmod
      have hb := hblue (r, ⟨m, hm⟩)
      rw [hsucc] at hb
      have ht : y1 (true, (r, ⟨m + 1, hk⟩)) = y2 (true, (r, ⟨m + 1, hk⟩)) := by
        have hb' : (y1 (true, (r, ⟨m + 1, hk⟩)) ≠ y1 (false, (r, ⟨m, hm⟩))) ↔
            (y2 (true, (r, ⟨m + 1, hk⟩)) ≠ y2 (false, (r, ⟨m, hm⟩))) := by
          simpa [ne_comm] using hb
        exact hstep _ _ _ _ hprev.2 hb'
      exact ⟨ht, hstep _ _ _ _ ht (hred (r, ⟨m + 1, hk⟩))⟩
  funext ⟨side, r, k⟩
  cases side
  · exact (hrail r k.val k.isLt).2
  · exact (hrail r k.val k.isLt).1

lemma card_filter_bool_prod {α : Type*} [Fintype α] [DecidableEq α]
    (P : Bool × α → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun a : α => P (false, a))).card +
      (Finset.univ.filter (fun a : α => P (true, a))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fintype.sum_prod_type,
    Fintype.sum_bool, add_comm]

lemma decide_ne_xor_iff (a b c : Bool) : (decide (a ≠ c) ≠ decide (b ≠ c)) ↔ (a ≠ b) := by
  cases a <;> cases b <;> cases c <;> decide

lemma decide_ne_xor_not_iff (a b c : Bool) : (decide (a ≠ c) ≠ decide (b ≠ !c)) ↔ (a = b) := by
  cases a <;> cases b <;> cases c <;> decide

lemma xor_eq_iff_false (a b r : Bool) :
    (decide (a ≠ false) = decide (b ≠ !r)) ↔ decide (a ≠ b) ≠ r := by
  cases a <;> cases b <;> cases r <;> decide

lemma xor_eq_iff_true (a b r : Bool) :
    (decide (a ≠ r) = decide (b ≠ true)) ↔ decide (a ≠ b) ≠ r := by
  cases a <;> cases b <;> cases r <;> decide

lemma port_step_bool (x1 x2 r y1f y2t y2f y1t : Bool) :
    (if decide (x1 ≠ x2) ≠ r then 2 else 0) ≤
    (if y1f = y2t then 1 else 0) +
    (if y2f = y1t then 1 else 0) +
    ((decide (y1f ≠ decide (x1 ≠ false))).toNat +
     (decide (y1t ≠ decide (x1 ≠ true))).toNat) +
    ((decide (y2f ≠ decide (x2 ≠ r))).toNat +
     (decide (y2t ≠ decide (x2 ≠ !r))).toNat) := by
  cases x1 <;> cases x2 <;> cases r <;> cases y1f <;> cases y2t <;> cases y2f <;> cases y1t <;> decide

lemma card_rail_bdry_le (N r : ℕ) [NeZero N] (hN : 0 < N) (hr : 2 * r ≤ 4 * N) :
    (Finset.univ.filter (fun y : Bool × (Bool × Fin N) → Bool =>
      railRed N y + railBlue N y ≤ r)).card ≤ 4 * (r + 1) * Nat.choose (4 * N) r := by
  let Edge := Bool × (Bool × Fin N)
  let mkBdry : (Bool × (Bool × Fin N) → Bool) → (Bool × Bool) × Finset Edge := fun y =>
    ((y (true, (false, ⟨0, hN⟩)), y (true, (true, ⟨0, hN⟩))),
     Finset.univ.filter (fun e : Edge =>
       if e.1 then y (false, e.2) ≠ y (true, (e.2.1, e.2.2 + 1))
       else y (false, e.2) ≠ y (true, e.2)))
  have hcardB : ∀ y, (mkBdry y).2.card = railRed N y + railBlue N y := by
    intro y
    exact card_filter_bool_prod (fun e : Edge =>
      if e.1 then y (false, e.2) ≠ y (true, (e.2.1, e.2.2 + 1))
      else y (false, e.2) ≠ y (true, e.2))
  have hinj : Function.Injective mkBdry := by
    intro y1 y2 h
    have hp : (mkBdry y1).1 = (mkBdry y2).1 := congrArg Prod.fst h
    have hs : (mkBdry y1).2 = (mkBdry y2).2 := congrArg Prod.snd h
    have h0 : y1 (true, (false, ⟨0, hN⟩)) = y2 (true, (false, ⟨0, hN⟩)) :=
      congrArg Prod.fst hp
    have h1 : y1 (true, (true, ⟨0, hN⟩)) = y2 (true, (true, ⟨0, hN⟩)) :=
      congrArg Prod.snd hp
    have hred : ∀ i, (y1 (false, i) ≠ y1 (true, i)) ↔ (y2 (false, i) ≠ y2 (true, i)) := by
      intro i
      have := Finset.ext_iff.mp hs (false, i)
      simpa [mkBdry] using this
    have hblue : ∀ i,
        (y1 (false, i) ≠ y1 (true, (i.1, i.2 + 1))) ↔
          (y2 (false, i) ≠ y2 (true, (i.1, i.2 + 1))) := by
      intro i
      have := Finset.ext_iff.mp hs (true, i)
      simpa [mkBdry] using this
    exact bdry_inj_rail N hN y1 y2 h0 h1 hred hblue
  let target : Finset ((Bool × Bool) × Finset Edge) :=
    Finset.univ ×ˢ (Finset.univ.filter (fun S : Finset Edge => S.card ≤ r))
  have hsub : (Finset.univ.filter (fun y => railRed N y + railBlue N y ≤ r)).image mkBdry ⊆
      target := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [target, Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
    rw [hcardB y]
    exact hy
  have hcard1 : (Finset.univ.filter (fun y => railRed N y + railBlue N y ≤ r)).card ≤
      target.card := by
    rw [← Finset.card_image_of_injective _ hinj]
    exact Finset.card_le_card hsub
  have hEdge : Fintype.card Edge = 4 * N := by
    simp [Edge, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring
  have htarget : target.card = 4 * ∑ k ∈ Finset.range (r + 1), Nat.choose (4 * N) k := by
    rw [Finset.card_product, Finset.card_univ, card_filter_le_of_finset_sum, hEdge]
    simp
  calc (Finset.univ.filter (fun y => railRed N y + railBlue N y ≤ r)).card
      ≤ 4 * ∑ k ∈ Finset.range (r + 1), Nat.choose (4 * N) k := by rwa [htarget] at hcard1
    _ ≤ 4 * ((r + 1) * Nat.choose (4 * N) r) :=
        Nat.mul_le_mul_left 4 (sum_choose_le (4 * N) r hr)
    _ = 4 * (r + 1) * Nat.choose (4 * N) r := by ring

lemma card_perm_image_eq (N : ℕ) (S U : Finset (Fin N)) (hSU : S.card = U.card) :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card =
      S.card.factorial * (N - S.card).factorial := by
  classical
  let e1 : {p : Equiv.Perm (Fin N) // S.image p = U} ≃
      ({x : Fin N // x ∈ S} ≃ {x : Fin N // x ∈ U}) ×
      ({x : Fin N // x ∉ S} ≃ {x : Fin N // x ∉ U}) :=
    { toFun := fun ⟨p, hp⟩ =>
        (⟨fun x => ⟨p x.1, by rw [← hp]; exact Finset.mem_image_of_mem p x.2⟩,
          fun y => ⟨p.symm y.1, by
            have hy : y.1 ∈ S.image p := by rw [hp]; exact y.2
            rcases Finset.mem_image.mp hy with ⟨x, hx, hpx⟩
            have : p.symm y.1 = x := by rw [← hpx, p.symm_apply_apply]
            rwa [this]⟩,
          fun x => by ext; simp,
          fun y => by ext; simp⟩,
         ⟨fun x => ⟨p x.1, by
            intro hmem
            rw [← hp] at hmem
            rcases Finset.mem_image.mp hmem with ⟨z, hz, hpz⟩
            have : z = x.1 := p.injective hpz
            exact x.2 (this ▸ hz)⟩,
          fun y => ⟨p.symm y.1, by
            intro hmem
            have h1 : p (p.symm y.1) ∈ S.image p := Finset.mem_image_of_mem p hmem
            rw [hp, p.apply_symm_apply] at h1
            exact y.2 h1⟩,
          fun x => by ext; simp,
          fun y => by ext; simp⟩)
      invFun := fun ⟨f, g⟩ =>
        ⟨⟨fun x => if hx : x ∈ S then (f ⟨x, hx⟩).1 else (g ⟨x, hx⟩).1,
          fun y => if hy : y ∈ U then (f.symm ⟨y, hy⟩).1 else (g.symm ⟨y, hy⟩).1,
          fun x => by
            by_cases hx : x ∈ S
            · simp only [hx, ↓reduceDIte, (f ⟨x, hx⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply]
            · simp only [hx, ↓reduceDIte, (g ⟨x, hx⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply],
          fun y => by
            by_cases hy : y ∈ U
            · simp only [hy, ↓reduceDIte, (f.symm ⟨y, hy⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply]
            · simp only [hy, ↓reduceDIte, (g.symm ⟨y, hy⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply]⟩,
         by
           ext y
           simp only [Finset.mem_image, Equiv.coe_fn_mk]
           constructor
           · rintro ⟨x, hx, rfl⟩
             simp only [hx, ↓reduceDIte, (f ⟨x, hx⟩).2]
           · intro hy
             refine ⟨(f.symm ⟨y, hy⟩).1, (f.symm ⟨y, hy⟩).2, ?_⟩
             simp only [(f.symm ⟨y, hy⟩).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]⟩
      left_inv := fun ⟨p, hp⟩ => by
        ext x
        by_cases hx : x ∈ S <;> simp [hx]
      right_inv := fun ⟨f, g⟩ => by
        ext x
        · simp [x.2]
        · simp [x.2] }
  have hc1 : (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card =
      Fintype.card {p : Equiv.Perm (Fin N) // S.image p = U} := by
    rw [Fintype.card_subtype]
  rw [hc1, Fintype.card_congr e1, Fintype.card_prod]
  have hS : Fintype.card {x : Fin N // x ∈ S} = S.card := Fintype.card_coe S
  have hU : Fintype.card {x : Fin N // x ∈ U} = U.card := Fintype.card_coe U
  have hSc : Fintype.card {x : Fin N // x ∉ S} = N - S.card := by
    have := Fintype.card_subtype_compl (fun x : Fin N => x ∈ S)
    rw [Fintype.card_fin, hS] at this
    exact this
  have hUc : Fintype.card {x : Fin N // x ∉ U} = N - U.card := by
    have := Fintype.card_subtype_compl (fun x : Fin N => x ∈ U)
    rw [Fintype.card_fin, hU] at this
    exact this
  have he1 : Fintype.card ({x : Fin N // x ∈ S} ≃ {x : Fin N // x ∈ U}) = S.card.factorial := by
    have eS : {x : Fin N // x ∈ S} ≃ Fin S.card := Fintype.equivFinOfCardEq hS
    have eU : {x : Fin N // x ∈ U} ≃ Fin S.card := Fintype.equivFinOfCardEq (hU.trans hSU.symm)
    rw [Fintype.card_congr (Equiv.equivCongr eS eU), Fintype.card_perm, Fintype.card_fin]
  have he2 : Fintype.card ({x : Fin N // x ∉ S} ≃ {x : Fin N // x ∉ U}) =
      (N - S.card).factorial := by
    have eSc : {x : Fin N // x ∉ S} ≃ Fin (N - S.card) := Fintype.equivFinOfCardEq hSc
    have eUc : {x : Fin N // x ∉ U} ≃ Fin (N - S.card) :=
      Fintype.equivFinOfCardEq (by rw [hUc, hSU])
    rw [Fintype.card_congr (Equiv.equivCongr eSc eUc), Fintype.card_perm, Fintype.card_fin]
  rw [he1, he2]

lemma card_perm_cross_le (N r : ℕ) (S T : Finset (Fin N)) (hr : 2 * r ≤ N) :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin N) =>
      (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).card ≤ r)).card *
      Nat.choose N S.card ≤ N.factorial * ((r + 1) * Nat.choose N r) := by
  classical
  have hdiff : ∀ p : Equiv.Perm (Fin N),
      (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).card =
        (symmDiff (S.image p) T).card := by
    intro p
    have hbi : (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).image p =
        symmDiff (S.image p) T := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_symmDiff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        by_cases h1 : k ∈ S
        · left
          refine ⟨⟨k, h1, rfl⟩, ?_⟩
          intro h2; exact hk (propext (iff_of_true h1 h2))
        · right
          have h2 : p k ∈ T := by
            by_contra h2; exact hk (propext (iff_of_false h1 h2))
          refine ⟨h2, ?_⟩
          rintro ⟨z, hz, hpz⟩
          exact h1 (p.injective hpz ▸ hz)
      · rintro (⟨⟨k, hk, rfl⟩, h2⟩ | ⟨h2, h1⟩)
        · exact ⟨k, fun h => h2 (by rw [← h]; exact hk), rfl⟩
        · refine ⟨p.symm y, ?_, p.apply_symm_apply y⟩
          intro h
          have : p.symm y ∈ S := by rw [h, p.apply_symm_apply]; exact h2
          exact h1 ⟨p.symm y, this, p.apply_symm_apply y⟩
    rw [← hbi, Finset.card_image_of_injective _ p.injective]
  let goodU : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun U : Finset (Fin N) => U.card = S.card ∧ (symmDiff U T).card ≤ r)
  have hpart : (Finset.univ.filter (fun p : Equiv.Perm (Fin N) =>
      (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).card ≤ r)).card =
      ∑ U ∈ goodU, (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, goodU, hdiff]
      constructor
      · intro hp
        exact ⟨S.image p, ⟨Finset.card_image_of_injective S p.injective, hp⟩, rfl⟩
      · rintro ⟨U, ⟨_, hU⟩, rfl⟩
        exact hU
    · intro U1 _ U2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      exact hne (hp1.symm.trans hp2)
  have hsum : ∑ U ∈ goodU, (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card =
      goodU.card * (S.card.factorial * (N - S.card).factorial) := by
    calc ∑ U ∈ goodU, (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card
        = ∑ _U ∈ goodU, (S.card.factorial * (N - S.card).factorial) := by
          apply Finset.sum_congr rfl
          intro U hU
          simp only [goodU, Finset.mem_filter, Finset.mem_univ, true_and] at hU
          exact card_perm_image_eq N S U hU.1.symm
      _ = goodU.card * (S.card.factorial * (N - S.card).factorial) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hgoodU : goodU.card ≤ (r + 1) * Nat.choose N r := by
    have hinj : Function.Injective (fun U : Finset (Fin N) => symmDiff U T) := by
      intro U1 U2 h
      have := congrArg (fun X => symmDiff X T) h
      simpa [symmDiff_symmDiff_cancel_right] using this
    have hsub : goodU.image (fun U => symmDiff U T) ⊆
        Finset.univ.filter (fun D : Finset (Fin N) => D.card ≤ r) := by
      intro D hD
      rcases Finset.mem_image.mp hD with ⟨U, hU, rfl⟩
      simp only [goodU, Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
      exact hU.2
    calc goodU.card = (goodU.image (fun U => symmDiff U T)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.univ.filter (fun D : Finset (Fin N) => D.card ≤ r)).card :=
          Finset.card_le_card hsub
      _ = ∑ k ∈ Finset.range (r + 1), Nat.choose N k := by
          rw [card_filter_le_of_finset_sum, Fintype.card_fin]
      _ ≤ (r + 1) * Nat.choose N r := sum_choose_le N r hr
  have hS_le : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hfac : Nat.choose N S.card * (S.card.factorial * (N - S.card).factorial) = N.factorial := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hS_le
  rw [hpart, hsum]
  calc goodU.card * (S.card.factorial * (N - S.card).factorial) * Nat.choose N S.card
      = goodU.card * (Nat.choose N S.card * (S.card.factorial * (N - S.card).factorial)) := by ring
    _ = goodU.card * N.factorial := by rw [hfac]
    _ ≤ ((r + 1) * Nat.choose N r) * N.factorial := Nat.mul_le_mul_right _ hgoodU
    _ = N.factorial * ((r + 1) * Nat.choose N r) := by ring

lemma zero_bdry_impossible (N : ℕ) [NeZero N] (hN : 0 < N) (p0 p1 : Equiv.Perm (Fin N))
    (y : Bool × (Bool × Fin N) → Bool)
    (hm1 : 0 < railMass N y) (hm2 : 2 * railMass N y ≤ 4 * N) :
    0 < railRed N y + railBlue N y + railCross0 N y p0 + railCross1 N y p1 := by
  by_contra h0
  have hred0 : railRed N y = 0 := by omega
  have hblue0 : railBlue N y = 0 := by omega
  have hc0 : railCross0 N y p0 = 0 := by omega
  have hred : ∀ i, y (false, i) = y (true, i) := by
    intro i
    by_contra hne
    have hmem : i ∈ Finset.univ.filter (fun j : Bool × Fin N => y (false, j) ≠ y (true, j)) := by
      simp [hne]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    exact Nat.ne_of_gt this hred0
  have hblue : ∀ i, y (false, i) = y (true, (i.1, i.2 + 1)) := by
    intro i
    by_contra hne
    have hmem : i ∈ Finset.univ.filter (fun j : Bool × Fin N =>
        y (false, j) ≠ y (true, (j.1, j.2 + 1))) := by
      simp [hne]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    exact Nat.ne_of_gt this hblue0
  have hcross : ∀ k, y (false, (false, k)) = y (true, (true, p0 k)) := by
    intro k
    by_contra hne
    have hmem : k ∈ Finset.univ.filter (fun j : Fin N =>
        y (false, (false, j)) ≠ y (true, (true, p0 j))) := by
      simp [hne]
    have := Finset.card_pos.mpr ⟨k, hmem⟩
    exact Nat.ne_of_gt this hc0
  have hrail_const : ∀ (r : Bool) (k : ℕ) (hk : k < N),
      y (true, (r, ⟨k, hk⟩)) = y (true, (r, ⟨0, hN⟩)) := by
    intro r k
    induction k with
    | zero => intro _; rfl
    | succ m ih =>
      intro hk
      have hm : m < N := by omega
      have hsucc : (⟨m, hm⟩ : Fin N) + 1 = ⟨m + 1, hk⟩ := by
        apply Fin.ext
        by_cases hN1 : N = 1
        · omega
        · change (m + 1 % N) % N = m + 1
          rw [Nat.mod_eq_of_lt (by omega : 1 < N), Nat.mod_eq_of_lt hk]
      calc y (true, (r, ⟨m + 1, hk⟩))
          = y (true, (r, (⟨m, hm⟩ : Fin N) + 1)) := by rw [hsucc]
        _ = y (false, (r, ⟨m, hm⟩)) := (hblue (r, ⟨m, hm⟩)).symm
        _ = y (true, (r, ⟨m, hm⟩)) := hred (r, ⟨m, hm⟩)
        _ = y (true, (r, ⟨0, hN⟩)) := ih hm
  have hboth : y (true, (true, ⟨0, hN⟩)) = y (true, (false, ⟨0, hN⟩)) := by
    calc y (true, (true, ⟨0, hN⟩))
        = y (true, (true, p0 ⟨0, hN⟩)) := (hrail_const true (p0 ⟨0, hN⟩).val (p0 ⟨0, hN⟩).isLt).symm
      _ = y (false, (false, ⟨0, hN⟩)) := (hcross ⟨0, hN⟩).symm
      _ = y (true, (false, ⟨0, hN⟩)) := hred (false, ⟨0, hN⟩)
  set c := y (true, (false, ⟨0, hN⟩))
  have hall : ∀ u : Bool × (Bool × Fin N), y u = c := by
    intro ⟨side, r, k⟩
    have ht : y (true, (r, k)) = c := by
      have h1 := hrail_const r k.val k.isLt
      cases r
      · exact h1
      · exact h1.trans hboth
    cases side
    · exact (hred (r, k)).trans ht
    · exact ht
  cases hc : c
  · have : railMass N y = 0 := by
      unfold railMass
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro u _; simp [hall u, hc]
    omega
  · have : railMass N y = 4 * N := by
      unfold railMass
      have hfilt : Finset.univ.filter (fun u : Bool × (Bool × Fin N) => y u = true) = Finset.univ := by
        ext u; simp [hall u, hc]
      rw [hfilt, Finset.card_univ]
      simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
      ring
    omega

lemma card_filter_diff_le (N : ℕ) (f g : Fin N → Bool) :
    (Finset.univ.filter (fun k : Fin N => f k = true)).card ≤
      (Finset.univ.filter (fun k : Fin N => g k = true)).card +
      (Finset.univ.filter (fun k : Fin N => f k ≠ g k)).card := by
  have hsub : Finset.univ.filter (fun k : Fin N => f k = true) ⊆
      (Finset.univ.filter (fun k : Fin N => g k = true)) ∪
      (Finset.univ.filter (fun k : Fin N => f k ≠ g k)) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hk ⊢
    by_cases hg : g k = true
    · exact Or.inl hg
    · exact Or.inr (by rw [hk]; exact fun h => hg h.symm)
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

lemma railMass_split (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) :
    railMass N y =
      (Finset.univ.filter (fun k : Fin N => y (false, (false, k)) = true)).card +
      (Finset.univ.filter (fun k : Fin N => y (true, (false, k)) = true)).card +
      (Finset.univ.filter (fun k : Fin N => y (false, (true, k)) = true)).card +
      (Finset.univ.filter (fun k : Fin N => y (true, (true, k)) = true)).card := by
  unfold railMass
  let e : Bool × (Bool × Fin N) ≃ (Bool × Bool) × Fin N :=
    ⟨fun x => ((x.1, x.2.1), x.2.2), fun x => (x.1.1, (x.1.2, x.2)),
     fun _ => rfl, fun _ => rfl⟩
  have h1 : (Finset.univ.filter (fun u : Bool × (Bool × Fin N) => y u = true)).card =
      ∑ p : Bool × Bool, (Finset.univ.filter (fun k : Fin N => y (p.1, (p.2, k)) = true)).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun u _ => ⟨(u.1, u.2.1), u.2.2⟩) ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hu ⊢
      exact hu
    · intro u1 _ u2 _ h
      rcases u1 with ⟨a1, b1, k1⟩
      rcases u2 with ⟨a2, b2, k2⟩
      simp only [Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq] at h
      rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
      rfl
    · intro ⟨⟨a, b⟩, k⟩ h
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at h
      exact ⟨(a, (b, k)), by simp [h], rfl⟩
  rw [h1]
  have hsum : ∑ p : Bool × Bool,
      (Finset.univ.filter (fun k : Fin N => y (p.1, (p.2, k)) = true)).card =
      (Finset.univ.filter (fun k : Fin N => y (false, (false, k)) = true)).card +
      (Finset.univ.filter (fun k : Fin N => y (true, (false, k)) = true)).card +
      (Finset.univ.filter (fun k : Fin N => y (false, (true, k)) = true)).card +
      (Finset.univ.filter (fun k : Fin N => y (true, (true, k)) = true)).card := by
    simp [Fintype.sum_prod_type, Fintype.sum_bool]
    ring
  exact hsum

lemma rail_balance (N : ℕ) (p0 p1 : Equiv.Perm (Fin N))
    (y : Bool × (Bool × Fin N) → Bool) (r : ℕ)
    (hR : railRed N y ≤ r) (hC0 : railCross0 N y p0 ≤ r) (hC1 : railCross1 N y p1 ≤ r)
    (hm1 : 128 * r < railMass N y) (hm2 : 2 * railMass N y ≤ 4 * N) :
    let a0 := (Finset.univ.filter (fun k : Fin N => y (false, (false, k)) = true)).card
    let a1 := (Finset.univ.filter (fun k : Fin N => y (false, (true, k)) = true)).card
    16 * r ≤ a0 ∧ a0 + 16 * r ≤ N ∧ 16 * r ≤ a1 ∧ a1 + 16 * r ≤ N := by
  set a0 := (Finset.univ.filter (fun k : Fin N => y (false, (false, k)) = true)).card
  set b0 := (Finset.univ.filter (fun k : Fin N => y (true, (false, k)) = true)).card
  set a1 := (Finset.univ.filter (fun k : Fin N => y (false, (true, k)) = true)).card
  set b1 := (Finset.univ.filter (fun k : Fin N => y (true, (true, k)) = true)).card
  have hmass : railMass N y = a0 + b0 + a1 + b1 := railMass_split N y
  have hred0 : (Finset.univ.filter (fun k : Fin N =>
      y (false, (false, k)) ≠ y (true, (false, k)))).card ≤ railRed N y := by
    unfold railRed
    have hsub : (Finset.univ.filter (fun k : Fin N =>
        y (false, (false, k)) ≠ y (true, (false, k)))).image (fun k => (false, k)) ⊆
        Finset.univ.filter (fun i : Bool × Fin N => y (false, i) ≠ y (true, i)) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk
    rw [← Finset.card_image_of_injective _ (f := fun k : Fin N => (false, k)) (fun _ _ h => by simpa using h)]
    exact Finset.card_le_card hsub
  have hred1 : (Finset.univ.filter (fun k : Fin N =>
      y (false, (true, k)) ≠ y (true, (true, k)))).card ≤ railRed N y := by
    unfold railRed
    have hsub : (Finset.univ.filter (fun k : Fin N =>
        y (false, (true, k)) ≠ y (true, (true, k)))).image (fun k => (true, k)) ⊆
        Finset.univ.filter (fun i : Bool × Fin N => y (false, i) ≠ y (true, i)) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk
    rw [← Finset.card_image_of_injective _ (f := fun k : Fin N => (true, k)) (fun _ _ h => by simpa using h)]
    exact Finset.card_le_card hsub
  have hb1_eq : (Finset.univ.filter (fun k : Fin N => y (true, (true, p0 k)) = true)).card = b1 := by
    refine Finset.card_bij (fun k _ => p0 k) ?_ ?_ ?_
    · intro k hk; simpa using hk
    · intro k1 _ k2 _ h; exact p0.injective h
    · intro k hk; exact ⟨p0.symm k, by simpa using hk, p0.apply_symm_apply k⟩
  have hb0_eq : (Finset.univ.filter (fun k : Fin N => y (true, (false, p1 k)) = true)).card = b0 := by
    refine Finset.card_bij (fun k _ => p1 k) ?_ ?_ ?_
    · intro k hk; simpa using hk
    · intro k1 _ k2 _ h; exact p1.injective h
    · intro k hk; exact ⟨p1.symm k, by simpa using hk, p1.apply_symm_apply k⟩
  have ha0_b0 : a0 ≤ b0 + r := by
    have := card_filter_diff_le N (fun k => y (false, (false, k))) (fun k => y (true, (false, k)))
    omega
  have hb0_a0 : b0 ≤ a0 + r := by
    have := card_filter_diff_le N (fun k => y (true, (false, k))) (fun k => y (false, (false, k)))
    have hsym : (Finset.univ.filter (fun k : Fin N =>
        y (true, (false, k)) ≠ y (false, (false, k)))).card =
        (Finset.univ.filter (fun k : Fin N =>
        y (false, (false, k)) ≠ y (true, (false, k)))).card := by
      congr 1; ext k; simp [ne_comm]
    omega
  have ha1_b1 : a1 ≤ b1 + r := by
    have := card_filter_diff_le N (fun k => y (false, (true, k))) (fun k => y (true, (true, k)))
    omega
  have hb1_a1 : b1 ≤ a1 + r := by
    have := card_filter_diff_le N (fun k => y (true, (true, k))) (fun k => y (false, (true, k)))
    have hsym : (Finset.univ.filter (fun k : Fin N =>
        y (true, (true, k)) ≠ y (false, (true, k)))).card =
        (Finset.univ.filter (fun k : Fin N =>
        y (false, (true, k)) ≠ y (true, (true, k)))).card := by
      congr 1; ext k; simp [ne_comm]
    omega
  have ha0_b1 : a0 ≤ b1 + r := by
    have := card_filter_diff_le N (fun k => y (false, (false, k))) (fun k => y (true, (true, p0 k)))
    rw [hb1_eq] at this
    exact le_trans this (Nat.add_le_add_left hC0 b1)
  have hb1_a0 : b1 ≤ a0 + r := by
    have := card_filter_diff_le N (fun k => y (true, (true, p0 k))) (fun k => y (false, (false, k)))
    rw [hb1_eq] at this
    have hsym : (Finset.univ.filter (fun k : Fin N =>
        y (true, (true, p0 k)) ≠ y (false, (false, k)))).card = railCross0 N y p0 := by
      unfold railCross0; congr 1; ext k; simp [ne_comm]
    rw [hsym] at this
    exact le_trans this (Nat.add_le_add_left hC0 a0)
  have ha1_b0 : a1 ≤ b0 + r := by
    have := card_filter_diff_le N (fun k => y (false, (true, k))) (fun k => y (true, (false, p1 k)))
    rw [hb0_eq] at this
    exact le_trans this (Nat.add_le_add_left hC1 b0)
  have hb0_a1 : b0 ≤ a1 + r := by
    have := card_filter_diff_le N (fun k => y (true, (false, p1 k))) (fun k => y (false, (true, k)))
    rw [hb0_eq] at this
    have hsym : (Finset.univ.filter (fun k : Fin N =>
        y (true, (false, p1 k)) ≠ y (false, (true, k)))).card = railCross1 N y p1 := by
      unfold railCross1; congr 1; ext k; simp [ne_comm]
    rw [hsym] at this
    exact le_trans this (Nat.add_le_add_left hC1 a1)
  omega

lemma exists_expander_perms (N : ℕ) [NeZero N] (hN : 0 < N) :
    ∃ p0 p1 : Equiv.Perm (Fin N),
      ∀ y : Bool × (Bool × Fin N) → Bool,
        2 * railMass N y ≤ 4 * N →
        railMass N y ≤ 128 * (railRed N y + railBlue N y +
          railCross0 N y p0 + railCross1 N y p1) := by
  classical
  let P := Equiv.Perm (Fin N) × Equiv.Perm (Fin N)
  let isBad : P → (Bool × (Bool × Fin N) → Bool) → Prop := fun p y =>
    2 * railMass N y ≤ 4 * N ∧
    128 * (railRed N y + railBlue N y + railCross0 N y p.1 + railCross1 N y p.2) < railMass N y
  let badCount : P → ℕ := fun p =>
    (Finset.univ.filter (fun y => isBad p y)).card
  suffices hsum_lt : ∑ p : P, badCount p < Fintype.card P by
    have hne : (Finset.univ : Finset P).Nonempty := ⟨(1, 1), Finset.mem_univ _⟩
    have hex : ∃ p ∈ (Finset.univ : Finset P), badCount p < 1 := by
      by_contra hall
      push_neg at hall
      have hge : Fintype.card P ≤ ∑ p : P, badCount p := by
        calc Fintype.card P = ∑ _p : P, 1 := by simp
          _ ≤ ∑ p : P, badCount p := Finset.sum_le_sum (fun p _ => hall p (Finset.mem_univ p))
      omega
    rcases hex with ⟨⟨p0, p1⟩, _, hlt⟩
    refine ⟨p0, p1, ?_⟩
    intro y hm
    by_contra hbad
    have hmem : y ∈ Finset.univ.filter (fun z => isBad (p0, p1) z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, isBad]
      exact ⟨hm, by omega⟩
    have hpos_card := Finset.card_pos.mpr ⟨y, hmem⟩
    change (Finset.univ.filter (fun z => isBad (p0, p1) z)).card < 1 at hlt
    omega
  let Rmax := N / 64
  let badR : ℕ → P → Finset (Bool × (Bool × Fin N) → Bool) := fun r p =>
    Finset.univ.filter (fun y =>
      railRed N y + railBlue N y ≤ r ∧
      railCross0 N y p.1 ≤ r ∧
      railCross1 N y p.2 ≤ r ∧
      128 * r < railMass N y ∧
      2 * railMass N y ≤ 4 * N)
  have hcover : ∀ p : P, badCount p ≤ ∑ r ∈ Finset.Icc 1 Rmax, (badR r p).card := by
    intro p
    have hsub : Finset.univ.filter (fun y => isBad p y) ⊆
        (Finset.Icc 1 Rmax).biUnion (fun r => badR r p) := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, isBad] at hy
      set r := railRed N y + railBlue N y + railCross0 N y p.1 + railCross1 N y p.2
      have hmpos : 0 < railMass N y := by omega
      have hrpos : 0 < r := zero_bdry_impossible N hN p.1 p.2 y hmpos hy.1
      have hrle : r ≤ Rmax := by
        have : 128 * r < 2 * N := by omega
        omega
      refine Finset.mem_biUnion.mpr ⟨r, Finset.mem_Icc.mpr ⟨hrpos, hrle⟩, ?_⟩
      simp only [badR, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by omega, by omega, by omega, hy.2, hy.1⟩
    exact le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
  have hcardP : Fintype.card P = N.factorial ^ 2 := by
    simp [P, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, sq]
  have hper_r : ∀ r ∈ Finset.Icc 1 Rmax,
      2 ^ r * (∑ p : P, (badR r p).card) * 2 < Fintype.card P := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrN : 64 * r ≤ N := by
      have := (Finset.mem_Icc.mp hr).2
      omega
    let Y_r := Finset.univ.filter (fun y : Bool × (Bool × Fin N) → Bool =>
      railRed N y + railBlue N y ≤ r ∧ 128 * r < railMass N y ∧ 2 * railMass N y ≤ 4 * N)
    have hswap : ∑ p : P, (badR r p).card =
        ∑ y ∈ Y_r, (Finset.univ.filter (fun p : P =>
          railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r)).card := by
      have h1 : ∀ p : P, (badR r p).card =
          ∑ y ∈ Y_r, if railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r then 1 else 0 := by
        intro p
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1
        ext y
        simp only [badR, Y_r, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_boole, Nat.cast_id]
    have hY_card : Y_r.card ≤ 4 * (r + 1) * Nat.choose (4 * N) r := by
      have hsub : Y_r ⊆ Finset.univ.filter (fun y => railRed N y + railBlue N y ≤ r) := by
        intro y hy
        simp only [Y_r, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
        exact hy.1
      exact le_trans (Finset.card_le_card hsub) (card_rail_bdry_le N r hN (by omega))
    have hper_y : ∀ y ∈ Y_r,
        (Finset.univ.filter (fun p : P =>
          railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r)).card *
          (Nat.choose N (16 * r)) ^ 2 ≤
        N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2 := by
      intro y hy
      simp only [Y_r, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      by_cases hexp : ∃ p : P, railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r
      · rcases hexp with ⟨⟨q0, q1⟩, hq0, hq1⟩
        have hbal := rail_balance N q0 q1 y r (by omega) hq0 hq1 hy.2.1 hy.2.2
        let S0 := Finset.univ.filter (fun k : Fin N => y (false, (false, k)) = true)
        let T0 := Finset.univ.filter (fun k : Fin N => y (true, (true, k)) = true)
        let S1 := Finset.univ.filter (fun k : Fin N => y (false, (true, k)) = true)
        let T1 := Finset.univ.filter (fun k : Fin N => y (true, (false, k)) = true)
        have hprod : (Finset.univ.filter (fun p : P =>
            railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r)).card =
            (Finset.univ.filter (fun p0 : Equiv.Perm (Fin N) => railCross0 N y p0 ≤ r)).card *
            (Finset.univ.filter (fun p1 : Equiv.Perm (Fin N) => railCross1 N y p1 ≤ r)).card := by
          rw [← Finset.card_product]
          congr 1
          ext ⟨p0, p1⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Finset.mem_product]
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hc0_eq : ∀ p0 : Equiv.Perm (Fin N),
            railCross0 N y p0 =
              (Finset.univ.filter (fun k : Fin N => (k ∈ S0) ≠ (p0 k ∈ T0))).card := by
          intro p0; unfold railCross0; congr 1; ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S0, T0]
          cases y (false, (false, k)) <;> cases y (true, (true, p0 k)) <;> simp
        have hc1_eq : ∀ p1 : Equiv.Perm (Fin N),
            railCross1 N y p1 =
              (Finset.univ.filter (fun k : Fin N => (k ∈ S1) ≠ (p1 k ∈ T1))).card := by
          intro p1; unfold railCross1; congr 1; ext k
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S1, T1]
          cases y (false, (true, k)) <;> cases y (true, (false, p1 k)) <;> simp
        have hb0 := card_perm_cross_le N r S0 T0 (by omega)
        have hb1 := card_perm_cross_le N r S1 T1 (by omega)
        simp_rw [← hc0_eq] at hb0
        simp_rw [← hc1_eq] at hb1
        have hch0 : Nat.choose N (16 * r) ≤ Nat.choose N S0.card :=
          choose_le_choose_of_mid N (16 * r) S0.card hbal.1 hbal.2.1
        have hch1 : Nat.choose N (16 * r) ≤ Nat.choose N S1.card :=
          choose_le_choose_of_mid N (16 * r) S1.card hbal.2.2.1 hbal.2.2.2
        rw [hprod]
        calc (Finset.univ.filter (fun p0 => railCross0 N y p0 ≤ r)).card *
              (Finset.univ.filter (fun p1 => railCross1 N y p1 ≤ r)).card *
              (Nat.choose N (16 * r)) ^ 2
            = ((Finset.univ.filter (fun p0 => railCross0 N y p0 ≤ r)).card *
                Nat.choose N (16 * r)) *
              ((Finset.univ.filter (fun p1 => railCross1 N y p1 ≤ r)).card *
                Nat.choose N (16 * r)) := by ring
          _ ≤ ((Finset.univ.filter (fun p0 => railCross0 N y p0 ≤ r)).card *
                Nat.choose N S0.card) *
              ((Finset.univ.filter (fun p1 => railCross1 N y p1 ≤ r)).card *
                Nat.choose N S1.card) := by gcongr
          _ ≤ (N.factorial * ((r + 1) * Nat.choose N r)) *
              (N.factorial * ((r + 1) * Nat.choose N r)) := Nat.mul_le_mul hb0 hb1
          _ = N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2 := by ring
      · have hempty : Finset.univ.filter (fun p : P =>
            railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro p _ h
          exact hexp ⟨p, h⟩
        rw [hempty, Finset.card_empty, zero_mul]
        exact Nat.zero_le _
    have hch_pos : 0 < (Nat.choose N (16 * r)) ^ 2 := by
      have : 0 < Nat.choose N (16 * r) := Nat.choose_pos (by omega)
      positivity
    apply Nat.lt_of_mul_lt_mul_right (a := (Nat.choose N (16 * r)) ^ 2)
    have hsum_y : (∑ p : P, (badR r p).card) * (Nat.choose N (16 * r)) ^ 2 ≤
        Y_r.card * (N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2) := by
      rw [hswap, Finset.sum_mul]
      calc ∑ y ∈ Y_r, (Finset.univ.filter (fun p : P =>
              railCross0 N y p.1 ≤ r ∧ railCross1 N y p.2 ≤ r)).card *
              (Nat.choose N (16 * r)) ^ 2
          ≤ ∑ _y ∈ Y_r, (N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2) :=
            Finset.sum_le_sum hper_y
        _ = Y_r.card * (N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hkey := key_binom_ineq N r hr1 hrN
    have hfac_pos : 0 < N.factorial ^ 2 := by
      have := Nat.factorial_pos N; positivity
    rw [hcardP]
    calc 2 ^ r * (∑ p : P, (badR r p).card) * 2 * (Nat.choose N (16 * r)) ^ 2
        = 2 ^ r * 2 * ((∑ p : P, (badR r p).card) * (Nat.choose N (16 * r)) ^ 2) := by ring
      _ ≤ 2 ^ r * 2 * (Y_r.card * (N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2)) :=
          Nat.mul_le_mul_left _ hsum_y
      _ ≤ 2 ^ r * 2 * (4 * (r + 1) * Nat.choose (4 * N) r *
            (N.factorial ^ 2 * ((r + 1) * Nat.choose N r) ^ 2)) := by gcongr
      _ = N.factorial ^ 2 *
          (2 ^ r * 4 * (r + 1) ^ 3 * Nat.choose (4 * N) r * (Nat.choose N r) ^ 2 * 2) := by ring
      _ < N.factorial ^ 2 * (Nat.choose N (16 * r)) ^ 2 :=
          Nat.mul_lt_mul_of_pos_left hkey hfac_pos
  have hsum_all : ∑ p : P, badCount p ≤
      ∑ r ∈ Finset.Icc 1 Rmax, ∑ p : P, (badR r p).card := by
    calc ∑ p : P, badCount p
        ≤ ∑ p : P, ∑ r ∈ Finset.Icc 1 Rmax, (badR r p).card :=
          Finset.sum_le_sum (fun p _ => hcover p)
      _ = ∑ r ∈ Finset.Icc 1 Rmax, ∑ p : P, (badR r p).card := Finset.sum_comm
  have hpow_pos : 0 < 2 ^ Rmax := Nat.two_pow_pos Rmax
  apply Nat.lt_of_mul_lt_mul_left (a := 2 ^ Rmax)
  have hscale : 2 ^ Rmax * (∑ r ∈ Finset.Icc 1 Rmax, ∑ p : P, (badR r p).card) <
      2 ^ Rmax * Fintype.card P := by
    by_cases hR0 : Rmax = 0
    · simp only [hR0, Finset.Icc_eq_empty (by omega : ¬(1 ≤ 0)), Finset.sum_empty, mul_zero,
        pow_zero, one_mul, hcardP]
      have := Nat.factorial_pos N; positivity
    · rw [Finset.mul_sum]
      have hterm : ∀ r ∈ Finset.Icc 1 Rmax,
          2 ^ Rmax * (∑ p : P, (badR r p).card) ≤ 2 ^ (Rmax - r) * Fintype.card P := by
        intro r hr
        have hrle : r ≤ Rmax := (Finset.mem_Icc.mp hr).2
        have hlt := hper_r r hr
        have hsplit : 2 ^ Rmax = 2 ^ (Rmax - r) * 2 ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hrle]
        rw [hsplit]
        calc 2 ^ (Rmax - r) * 2 ^ r * ∑ p : P, (badR r p).card
            ≤ 2 ^ (Rmax - r) * (2 ^ r * (∑ p : P, (badR r p).card) * 2) := by
              have : 2 ^ r * ∑ p : P, (badR r p).card ≤
                  2 ^ r * (∑ p : P, (badR r p).card) * 2 := by omega
              calc 2 ^ (Rmax - r) * 2 ^ r * ∑ p : P, (badR r p).card
                  = 2 ^ (Rmax - r) * (2 ^ r * ∑ p : P, (badR r p).card) := by ring
                _ ≤ 2 ^ (Rmax - r) * (2 ^ r * (∑ p : P, (badR r p).card) * 2) :=
                    Nat.mul_le_mul_left _ this
          _ ≤ 2 ^ (Rmax - r) * Fintype.card P := Nat.mul_le_mul_left _ (le_of_lt hlt)
      have hgeo : ∑ r ∈ Finset.Icc 1 Rmax, 2 ^ (Rmax - r) < 2 ^ Rmax := by
        clear hper_r hsum_all hpow_pos hR0 hterm
        induction Rmax with
        | zero => simp
        | succ k ih =>
          have hsplit : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsplit, Finset.sum_insert (by simp)]
          simp only [Nat.sub_self, pow_zero]
          have h2 : ∑ x ∈ Finset.Icc 1 k, 2 ^ (k + 1 - x) =
              2 * ∑ x ∈ Finset.Icc 1 k, 2 ^ (k - x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            have hxk : x ≤ k := (Finset.mem_Icc.mp hx).2
            have he : k + 1 - x = (k - x) + 1 := by omega
            rw [he, pow_succ']
          rw [h2, pow_succ']
          omega
      have hPpos : 0 < Fintype.card P := by rw [hcardP]; have := Nat.factorial_pos N; positivity
      calc ∑ r ∈ Finset.Icc 1 Rmax, 2 ^ Rmax * ∑ p : P, (badR r p).card
          ≤ ∑ r ∈ Finset.Icc 1 Rmax, 2 ^ (Rmax - r) * Fintype.card P :=
            Finset.sum_le_sum hterm
        _ = (∑ r ∈ Finset.Icc 1 Rmax, 2 ^ (Rmax - r)) * Fintype.card P := by
            rw [Finset.sum_mul]
        _ < 2 ^ Rmax * Fintype.card P := Nat.mul_lt_mul_of_pos_right hgeo hPpos
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hsum_all) hscale

lemma cycle_tf_eq_ft (M : ℕ) [NeZero M] (hM : 0 < M) (f : Fin M → Bool) :
    (Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false)).card =
      (Finset.univ.filter (fun v : Fin M => f v = false ∧ f (v + 1) = true)).card := by
  have hshift : ∑ v : Fin M, (f (v + 1)).toNat = ∑ v : Fin M, (f v).toNat := by
    refine Fintype.sum_equiv (Equiv.addRight (1 : Fin M)) _ _ (fun _ => rfl)
  have hpt : ∀ v : Fin M,
      (f v).toNat + (if f v = false ∧ f (v + 1) = true then 1 else 0) =
      (f (v + 1)).toNat + (if f v = true ∧ f (v + 1) = false then 1 else 0) := by
    intro v
    cases f v <;> cases f (v + 1) <;> rfl
  have hsum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun v _ => hpt v)
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hsum
  rw [hshift] at hsum
  omega

lemma cycle_two_mul_tf_eq_bdry (M : ℕ) [NeZero M] (hM : 0 < M) (f : Fin M → Bool) :
    2 * (Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false)).card =
      (Finset.univ.filter (fun v : Fin M => f v ≠ f (v + 1))).card := by
  have hsplit : Finset.univ.filter (fun v : Fin M => f v ≠ f (v + 1)) =
      (Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false)) ∪
      (Finset.univ.filter (fun v : Fin M => f v = false ∧ f (v + 1) = true)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    cases f v <;> cases f (v + 1) <;> simp
  rw [hsplit, Finset.card_union_of_disjoint]
  · rw [← cycle_tf_eq_ft M hM f]; ring
  · rw [Finset.disjoint_left]
    intro v h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    rw [h1.1] at h2
    exact Bool.noConfusion h2.1

def fwdArc (M D : ℕ) [NeZero M] (p : Fin M) : Finset (Fin M) :=
  (Finset.range D).image (fun j => p + Fin.ofNat M j)

lemma fin_ofNat_add (M : ℕ) [NeZero M] (a b : ℕ) :
    Fin.ofNat M a + Fin.ofNat M b = Fin.ofNat M (a + b) := by
  apply Fin.ext
  change (a % M + b % M) % M = (a + b) % M
  exact (Nat.add_mod a b M).symm

lemma card_fwdArc (M D : ℕ) [NeZero M] (hDM : D ≤ M) (p : Fin M) :
    (fwdArc M D p).card = D := by
  unfold fwdArc
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro j1 hj1 j2 hj2 h
  have hj1' : j1 < M := lt_of_lt_of_le (Finset.mem_range.mp hj1) hDM
  have hj2' : j2 < M := lt_of_lt_of_le (Finset.mem_range.mp hj2) hDM
  have heq : Fin.ofNat M j1 = Fin.ofNat M j2 := add_left_cancel h
  have hval := congrArg Fin.val heq
  change j1 % M = j2 % M at hval
  rwa [Nat.mod_eq_of_lt hj1', Nat.mod_eq_of_lt hj2'] at hval

lemma cycle_port_bound (M D : ℕ) [NeZero M] (hM : 0 < M) (hDM : D ≤ M)
    (P : Finset (Fin M))
    (hdisj : ∀ p1 ∈ P, ∀ p2 ∈ P, p1 ≠ p2 → Disjoint (fwdArc M D p1) (fwdArc M D p2))
    (f : Fin M → Bool) :
    2 * D * (P.filter (fun p => f p = true)).card ≤
      2 * (Finset.univ.filter (fun v : Fin M => f v = true)).card +
      D * (Finset.univ.filter (fun v : Fin M => f v ≠ f (v + 1))).card := by
  classical
  let Ptrue := P.filter (fun p => f p = true)
  let Pfull := Ptrue.filter (fun p => ∀ j ∈ Finset.range D, f (p + Fin.ofNat M j) = true)
  let Pflip := Ptrue.filter (fun p => ∃ j ∈ Finset.range D, f (p + Fin.ofNat M j) = false)
  have hPsplit : Ptrue.card = Pfull.card + Pflip.card := by
    have hun : Ptrue = Pfull ∪ Pflip := by
      ext p
      simp only [Pfull, Pflip, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hp
        by_cases h : ∀ j ∈ Finset.range D, f (p + Fin.ofNat M j) = true
        · exact Or.inl ⟨hp, h⟩
        · push_neg at h
          rcases h with ⟨j, hj, hf⟩
          exact Or.inr ⟨hp, ⟨j, hj, by cases hx : f (p + Fin.ofNat M j) <;> simp_all⟩⟩
      · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    rw [hun, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Pfull, Pflip, Finset.mem_filter] at h1 h2
    rcases h2.2 with ⟨j, hj, hf⟩
    have := h1.2 j hj
    rw [this] at hf
    exact Bool.noConfusion hf
  have hfull : D * Pfull.card ≤ (Finset.univ.filter (fun v : Fin M => f v = true)).card := by
    have hsub : Pfull.biUnion (fwdArc M D) ⊆ Finset.univ.filter (fun v : Fin M => f v = true) := by
      intro v hv
      rcases Finset.mem_biUnion.mp hv with ⟨p, hp, hvp⟩
      simp only [Pfull, Finset.mem_filter] at hp
      rcases Finset.mem_image.mp hvp with ⟨j, hj, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hp.2 j hj
    have hcard : (Pfull.biUnion (fwdArc M D)).card = D * Pfull.card := by
      rw [Finset.card_biUnion]
      · simp_rw [card_fwdArc M D hDM]
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      · intro p1 hp1 p2 hp2 hne
        have hp1' : p1 ∈ P := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1
        have hp2' : p2 ∈ P := (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1
        exact hdisj p1 hp1' p2 hp2' hne
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hflip : Pflip.card ≤
      (Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false)).card := by
    have hex_edge : ∀ p ∈ Pflip,
        ∃ u ∈ fwdArc M D p, f u = true ∧ f (u + 1) = false := by
      intro p hp
      simp only [Pflip, Ptrue, Finset.mem_filter] at hp
      have hfp : f p = true := hp.1.2
      have hex : ∃ j, j < D ∧ f (p + Fin.ofNat M j) = false := by
        rcases hp.2 with ⟨j, hj, hf⟩
        exact ⟨j, Finset.mem_range.mp hj, hf⟩
      let j0 := Nat.find hex
      have hj0 : j0 < D ∧ f (p + Fin.ofNat M j0) = false := Nat.find_spec hex
      have hj0_pos : 0 < j0 := by
        by_contra h0
        have : j0 = 0 := by omega
        rw [this] at hj0
        have hzero : p + Fin.ofNat M 0 = p := by
          apply Fin.ext; change (p.val + 0 % M) % M = p.val; simp [Nat.mod_eq_of_lt p.isLt]
        rw [hzero, hfp] at hj0
        exact Bool.noConfusion hj0.2
      have hprev_lt : j0 - 1 < j0 := by omega
      have hprev_true : f (p + Fin.ofNat M (j0 - 1)) = true := by
        have hmin := Nat.find_min hex hprev_lt
        push_neg at hmin
        have hne := hmin (by omega)
        cases hx : f (p + Fin.ofNat M (j0 - 1)) <;> simp_all
      refine ⟨p + Fin.ofNat M (j0 - 1), ?_, hprev_true, ?_⟩
      · exact Finset.mem_image.mpr ⟨j0 - 1, Finset.mem_range.mpr (by omega), rfl⟩
      · have hadd : p + Fin.ofNat M (j0 - 1) + 1 = p + Fin.ofNat M j0 := by
          rw [add_assoc]
          congr 1
          have h1eq : (1 : Fin M) = Fin.ofNat M 1 := rfl
          rw [h1eq, fin_ofNat_add, Nat.sub_add_cancel hj0_pos]
        rw [hadd]
        exact hj0.2
    let witness : Fin M → Fin M := fun p =>
      if hp : p ∈ Pflip then Classical.choose (hex_edge p hp) else p
    have hw_mem : ∀ p ∈ Pflip, witness p ∈ fwdArc M D p := by
      intro p hp
      simp only [witness, hp, ↓reduceDIte]
      exact (Classical.choose_spec (hex_edge p hp)).1
    have hw_tf : ∀ p ∈ Pflip,
        witness p ∈ Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false) := by
      intro p hp
      simp only [witness, hp, ↓reduceDIte, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (Classical.choose_spec (hex_edge p hp)).2
    have hw_inj : Set.InjOn witness Pflip := by
      intro p1 hp1 p2 hp2 heq
      by_contra hne
      have hp1' : p1 ∈ P := (Finset.mem_filter.mp (Finset.mem_filter.mp hp1).1).1
      have hp2' : p2 ∈ P := (Finset.mem_filter.mp (Finset.mem_filter.mp hp2).1).1
      have hd := hdisj p1 hp1' p2 hp2' hne
      have h1 := hw_mem p1 hp1
      have h2 := hw_mem p2 hp2
      rw [heq] at h1
      exact Finset.disjoint_left.mp hd h1 h2
    calc Pflip.card = (Pflip.image witness).card := (Finset.card_image_of_injOn hw_inj).symm
      _ ≤ (Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false)).card := by
          apply Finset.card_le_card
          intro u hu
          rcases Finset.mem_image.mp hu with ⟨p, hp, rfl⟩
          exact hw_tf p hp
  have hbdry := cycle_two_mul_tf_eq_bdry M hM f
  calc 2 * D * Ptrue.card = 2 * (D * Pfull.card) + D * (2 * Pflip.card) := by rw [hPsplit]; ring
    _ ≤ 2 * (Finset.univ.filter (fun v : Fin M => f v = true)).card +
        D * (2 * (Finset.univ.filter (fun v : Fin M => f v = true ∧ f (v + 1) = false)).card) := by
        gcongr
    _ = 2 * (Finset.univ.filter (fun v : Fin M => f v = true)).card +
        D * (Finset.univ.filter (fun v : Fin M => f v ≠ f (v + 1))).card := by rw [hbdry]

lemma card_arc_overlap_le (M D : ℕ) [NeZero M] (q : Fin M) :
    (Finset.univ.filter (fun p : Fin M => ¬Disjoint (fwdArc M D p) (fwdArc M D q))).card ≤
      2 * D := by
  have hsub : Finset.univ.filter (fun p : Fin M => ¬Disjoint (fwdArc M D p) (fwdArc M D q)) ⊆
      ((Finset.range D).image (fun j => q + Fin.ofNat M j)) ∪
      ((Finset.range D).image (fun j => q - Fin.ofNat M j)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_disjoint_iff] at hp
    rcases hp with ⟨v, hv1, hv2⟩
    rcases Finset.mem_image.mp hv1 with ⟨j1, hj1, rfl⟩
    rcases Finset.mem_image.mp hv2 with ⟨j2, hj2, heq⟩
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range]
    have hj1' := Finset.mem_range.mp hj1
    have hj2' := Finset.mem_range.mp hj2
    by_cases hle : j1 ≤ j2
    · left
      refine ⟨j2 - j1, by omega, ?_⟩
      have hcast : Fin.ofNat M (j2 - j1) + Fin.ofNat M j1 = Fin.ofNat M j2 := by
        rw [fin_ofNat_add, Nat.sub_add_cancel hle]
      apply add_right_cancel (b := Fin.ofNat M j1)
      rw [add_assoc, hcast, heq]
    · right
      refine ⟨j1 - j2, by omega, ?_⟩
      have hcast : Fin.ofNat M (j1 - j2) + Fin.ofNat M j2 = Fin.ofNat M j1 := by
        rw [fin_ofNat_add, Nat.sub_add_cancel (by omega)]
      apply add_right_cancel (b := Fin.ofNat M j1)
      conv_lhs => rw [← hcast, ← add_assoc, sub_add_cancel]
      exact heq
  calc (Finset.univ.filter (fun p : Fin M => ¬Disjoint (fwdArc M D p) (fwdArc M D q))).card
      ≤ (((Finset.range D).image (fun j => q + Fin.ofNat M j)) ∪
         ((Finset.range D).image (fun j => q - Fin.ofNat M j))).card := Finset.card_le_card hsub
    _ ≤ ((Finset.range D).image (fun j => q + Fin.ofNat M j)).card +
        ((Finset.range D).image (fun j => q - Fin.ofNat M j)).card := Finset.card_union_le _ _
    _ ≤ (Finset.range D).card + (Finset.range D).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ = 2 * D := by simp; ring

def cycleIdx (N : ℕ) (side : Bool) (k : Fin N) : Fin (2 * N) :=
  ⟨2 * k.val + if side then 0 else 1, by have := k.isLt; cases side <;> simp <;> omega⟩

lemma cycleIdx_inj (N : ℕ) (side : Bool) : Function.Injective (cycleIdx N side) := by
  intro k1 k2 h
  have hv := congrArg Fin.val h
  simp only [cycleIdx] at hv
  apply Fin.ext
  omega

lemma cycleIdx_ne_side (N : ℕ) (k1 k2 : Fin N) :
    cycleIdx N false k1 ≠ cycleIdx N true k2 := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cycleIdx, Bool.false_eq_true, ↓reduceIte] at hv
  omega

lemma cycleIdx_succ_true (N : ℕ) [NeZero (2 * N)] (k : Fin N) :
    cycleIdx N true k + 1 = cycleIdx N false k := by
  apply Fin.ext
  have hN : 0 < N := Fin.pos k
  have hk := k.isLt
  change (2 * k.val + 0 + 1 % (2 * N)) % (2 * N) = 2 * k.val + 1
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * N), Nat.add_zero, Nat.mod_eq_of_lt (by omega)]

lemma cycleIdx_succ_false (N : ℕ) [NeZero N] [NeZero (2 * N)] (k : Fin N) :
    cycleIdx N false k + 1 = cycleIdx N true (k + 1) := by
  apply Fin.ext
  have hN : 0 < N := Fin.pos k
  have hk := k.isLt
  change (2 * k.val + 1 + 1 % (2 * N)) % (2 * N) = 2 * ((k.val + 1 % N) % N) + 0
  rw [Nat.mod_eq_of_lt (by omega : 1 < 2 * N), Nat.add_zero]
  by_cases hN1 : N = 1
  · have hk0 : k.val = 0 := by omega
    subst hN1; simp [hk0]
  · rw [Nat.mod_eq_of_lt (by omega : 1 < N)]
    by_cases hlast : k.val + 1 < N
    · rw [Nat.mod_eq_of_lt hlast, Nat.mod_eq_of_lt (by omega)]
      ring
    · have hk' : k.val + 1 = N := by omega
      rw [hk', Nat.mod_self]
      have h2 : 2 * k.val + 1 + 1 = 2 * N := by omega
      rw [h2, Nat.mod_self]

def railToCycle (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) (r : Bool) : Fin (2 * N) → Bool :=
  fun t => y (decide (t.val % 2 = 0), (r, ⟨t.val / 2, by have := t.isLt; omega⟩))

lemma railToCycle_cycleIdx (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) (r side : Bool) (k : Fin N) :
    railToCycle N y r (cycleIdx N side k) = y (side, (r, k)) := by
  unfold railToCycle cycleIdx
  cases side
  · have hmod : (2 * k.val + 1) % 2 = 1 := by omega
    have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, hmod]
    congr 1; exact Prod.ext rfl (Prod.ext rfl (Fin.ext hdiv))
  · have hmod : (2 * k.val + 0) % 2 = 0 := by omega
    have hdiv : (2 * k.val + 0) / 2 = k.val := by omega
    simp only [↓reduceIte, hmod, decide_true]
    congr 1; exact Prod.ext rfl (Prod.ext rfl (Fin.ext hdiv))

lemma railToCycle_mass (N : ℕ) (y : Bool × (Bool × Fin N) → Bool) :
    (Finset.univ.filter (fun t : Fin (2 * N) => railToCycle N y false t = true)).card +
    (Finset.univ.filter (fun t : Fin (2 * N) => railToCycle N y true t = true)).card =
      railMass N y := by
  unfold railMass
  let e : Bool × Fin (2 * N) ≃ Bool × (Bool × Fin N) :=
    ⟨fun x => (decide (x.2.val % 2 = 0), (x.1, ⟨x.2.val / 2, by have := x.2.isLt; omega⟩)),
     fun u => (u.2.1, cycleIdx N u.1 u.2.2),
     fun ⟨r, t⟩ => by
       ext
       · rfl
       · simp only [cycleIdx]
         by_cases he : t.val % 2 = 0
         · simp only [he, decide_true, ↓reduceIte, Nat.add_zero]
           omega
         · simp only [he, decide_false, Bool.false_eq_true, ↓reduceIte]
           omega,
     fun ⟨side, r, k⟩ => by
       cases side
       · have hmod : (2 * k.val + 1) % 2 = 1 := by omega
         have hdiv : (2 * k.val + 1) / 2 = k.val := by omega
         simp only [cycleIdx, Bool.false_eq_true, ↓reduceIte, hmod]
         exact Prod.ext rfl (Prod.ext rfl (Fin.ext hdiv))
       · have hmod : (2 * k.val + 0) % 2 = 0 := by omega
         have hdiv : (2 * k.val + 0) / 2 = k.val := by omega
         simp only [cycleIdx, ↓reduceIte, hmod, decide_true]
         exact Prod.ext rfl (Prod.ext rfl (Fin.ext hdiv))⟩
  have hsum : (Finset.univ.filter (fun t : Fin (2 * N) => railToCycle N y false t = true)).card +
      (Finset.univ.filter (fun t : Fin (2 * N) => railToCycle N y true t = true)).card =
      (Finset.univ.filter (fun x : Bool × Fin (2 * N) => railToCycle N y x.1 x.2 = true)).card :=
    (card_filter_bool_prod (fun x : Bool × Fin (2 * N) => railToCycle N y x.1 x.2 = true)).symm
  rw [hsum]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx
  · intro x1 _ x2 _ h; exact e.injective h
  · intro u hu
    refine ⟨e.symm u, ?_, e.apply_symm_apply u⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    have heq : railToCycle N y (e.symm u).1 (e.symm u).2 = y u := by
      rcases u with ⟨side, r, k⟩
      exact railToCycle_cycleIdx N y r side k
    rwa [heq]

lemma railToCycle_bdry (N : ℕ) [NeZero N] [NeZero (2 * N)] (y : Bool × (Bool × Fin N) → Bool) :
    (Finset.univ.filter (fun t : Fin (2 * N) =>
      railToCycle N y false t ≠ railToCycle N y false (t + 1))).card +
    (Finset.univ.filter (fun t : Fin (2 * N) =>
      railToCycle N y true t ≠ railToCycle N y true (t + 1))).card =
      railRed N y + railBlue N y := by
  have hone : ∀ r : Bool,
      (Finset.univ.filter (fun t : Fin (2 * N) =>
        railToCycle N y r t ≠ railToCycle N y r (t + 1))).card =
      (Finset.univ.filter (fun k : Fin N => y (false, (r, k)) ≠ y (true, (r, k)))).card +
      (Finset.univ.filter (fun k : Fin N => y (false, (r, k)) ≠ y (true, (r, k + 1)))).card := by
    intro r
    have hsplit : Finset.univ.filter (fun t : Fin (2 * N) =>
          railToCycle N y r t ≠ railToCycle N y r (t + 1)) =
        ((Finset.univ.filter (fun k : Fin N => y (false, (r, k)) ≠ y (true, (r, k)))).map
          ⟨cycleIdx N true, cycleIdx_inj N true⟩) ∪
        ((Finset.univ.filter (fun k : Fin N => y (false, (r, k)) ≠ y (true, (r, k + 1)))).map
          ⟨cycleIdx N false, cycleIdx_inj N false⟩) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_map, Function.Embedding.coeFn_mk]
      let k : Fin N := ⟨t.val / 2, by omega⟩
      by_cases he : t.val % 2 = 0
      · have ht : t = cycleIdx N true k := by
          apply Fin.ext; simp only [cycleIdx, k, ↓reduceIte, Nat.add_zero]; omega
        rw [ht, cycleIdx_succ_true, railToCycle_cycleIdx, railToCycle_cycleIdx]
        constructor
        · intro h; left; exact ⟨k, h.symm, rfl⟩
        · rintro (⟨k', hk', hEq⟩ | ⟨k', _, hEq⟩)
          · have := cycleIdx_inj N true hEq; subst this; exact hk'.symm
          · exact absurd hEq (cycleIdx_ne_side N k' k)
      · have ht : t = cycleIdx N false k := by
          apply Fin.ext; simp only [cycleIdx, k, Bool.false_eq_true, ↓reduceIte]; omega
        rw [ht, cycleIdx_succ_false, railToCycle_cycleIdx, railToCycle_cycleIdx]
        constructor
        · intro h; right; exact ⟨k, h, rfl⟩
        · rintro (⟨k', _, hEq⟩ | ⟨k', hk', hEq⟩)
          · exact absurd hEq.symm (cycleIdx_ne_side N k k')
          · have := cycleIdx_inj N false hEq; subst this; exact hk'
    rw [hsplit, Finset.card_union_of_disjoint]
    · simp
    · rw [Finset.disjoint_left]
      intro t ht1 ht2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at ht1 ht2
      rcases ht1 with ⟨k1, _, rfl⟩
      rcases ht2 with ⟨k2, _, h⟩
      exact cycleIdx_ne_side N k2 k1 h
  rw [hone false, hone true]
  have hred : railRed N y =
      (Finset.univ.filter (fun k : Fin N => y (false, (false, k)) ≠ y (true, (false, k)))).card +
      (Finset.univ.filter (fun k : Fin N => y (false, (true, k)) ≠ y (true, (true, k)))).card :=
    card_filter_bool_prod (fun i : Bool × Fin N => y (false, i) ≠ y (true, i))
  have hblue : railBlue N y =
      (Finset.univ.filter (fun k : Fin N =>
        y (false, (false, k)) ≠ y (true, (false, k + 1)))).card +
      (Finset.univ.filter (fun k : Fin N =>
        y (false, (true, k)) ≠ y (true, (true, k + 1)))).card :=
    card_filter_bool_prod (fun i : Bool × Fin N => y (false, i) ≠ y (true, (i.1, i.2 + 1)))
  rw [hred, hblue]
  ring

lemma exists_spaced_pick (d : ℕ) (pol : Fin d → Bool)
    (N : ℕ) [NeZero (2 * N)] (hN : 16384 * (d + 1) ≤ N)
    (π : Equiv.Perm (Bool × Fin N)) (hπ : ∀ i, (π i).1 = !i.1) :
    ∃ pick : Fin d ↪ Bool × Fin N,
      (∀ j, (pick j).1 = pol j) ∧
      (∀ j1 j2 : Fin d, j1 ≠ j2 →
        (pol j1 = pol j2 →
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false (pick j1).2))
                   (fwdArc (2 * N) 2048 (cycleIdx N false (pick j2).2))) ∧
        (pol j1 = pol j2 →
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (pick j1)).2))
                   (fwdArc (2 * N) 2048 (cycleIdx N true (π (pick j2)).2))) ∧
        (pol j1 = !(pol j2) →
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false (pick j1).2))
                   (fwdArc (2 * N) 2048 (cycleIdx N true (π (pick j2)).2)))) := by
  classical
  have hbuild : ∀ k (hk : k ≤ d),
      ∃ f : Fin k → Bool × Fin N,
        (∀ j : Fin k, (f j).1 = pol ⟨j.val, lt_of_lt_of_le j.isLt hk⟩) ∧
        (∀ j1 j2 : Fin k, j1 ≠ j2 →
          f j1 ≠ f j2 ∧
          (pol ⟨j1.val, lt_of_lt_of_le j1.isLt hk⟩ = pol ⟨j2.val, lt_of_lt_of_le j2.isLt hk⟩ →
            Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false (f j1).2))
                     (fwdArc (2 * N) 2048 (cycleIdx N false (f j2).2))) ∧
          (pol ⟨j1.val, lt_of_lt_of_le j1.isLt hk⟩ = pol ⟨j2.val, lt_of_lt_of_le j2.isLt hk⟩ →
            Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j1)).2))
                     (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j2)).2))) ∧
          (pol ⟨j1.val, lt_of_lt_of_le j1.isLt hk⟩ = !(pol ⟨j2.val, lt_of_lt_of_le j2.isLt hk⟩) →
            Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false (f j1).2))
                     (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j2)).2)))) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
    | succ m ih =>
      intro hm
      rcases ih (by omega) with ⟨f, hpol, hsp⟩
      let r0 := pol ⟨m, hm⟩
      let badA : Finset (Fin N) :=
        Finset.univ.biUnion (fun j : Fin m =>
          Finset.univ.filter (fun x : Fin N =>
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                      (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∨
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                      (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)) ∨
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                      (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∨
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                      (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2))))
      have hbad_one : ∀ (g : Fin N → Fin (2 * N)), Function.Injective g →
          ∀ q : Fin (2 * N),
          (Finset.univ.filter (fun x : Fin N =>
            ¬Disjoint (fwdArc (2 * N) 2048 (g x)) (fwdArc (2 * N) 2048 q))).card ≤ 4096 := by
        intro g hg q
        have hsub : (Finset.univ.filter (fun x : Fin N =>
            ¬Disjoint (fwdArc (2 * N) 2048 (g x)) (fwdArc (2 * N) 2048 q))).image g ⊆
            Finset.univ.filter (fun p : Fin (2 * N) =>
              ¬Disjoint (fwdArc (2 * N) 2048 p) (fwdArc (2 * N) 2048 q)) := by
          intro p hp
          rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          exact hx
        rw [← Finset.card_image_of_injective _ hg]
        exact le_trans (Finset.card_le_card hsub) (card_arc_overlap_le (2 * N) 2048 q)
      have hπ_inj : Function.Injective (fun x : Fin N => cycleIdx N true (π (r0, x)).2) := by
        intro x1 x2 h
        have h1 : (π (r0, x1)).2 = (π (r0, x2)).2 := cycleIdx_inj N true h
        have h2 : (π (r0, x1)).1 = (π (r0, x2)).1 := by rw [hπ, hπ]
        have h3 : π (r0, x1) = π (r0, x2) := Prod.ext h2 h1
        exact congrArg Prod.snd (π.injective h3)
      have hbad_lt : badA.card < N := by
        have h1 : badA.card ≤ ∑ _j : Fin m, 16384 := by
          refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum ?_)
          intro j _
          have ha := hbad_one (cycleIdx N false) (cycleIdx_inj N false)
            (cycleIdx N false (f j).2)
          have hb := hbad_one (cycleIdx N false) (cycleIdx_inj N false)
            (cycleIdx N true (π (f j)).2)
          have hc := hbad_one (fun x => cycleIdx N true (π (r0, x)).2) hπ_inj
            (cycleIdx N false (f j).2)
          have hd := hbad_one (fun x => cycleIdx N true (π (r0, x)).2) hπ_inj
            (cycleIdx N true (π (f j)).2)
          have hu : Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∨
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)) ∨
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∨
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                        (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2))) ⊆
              (Finset.univ.filter (fun x : Fin N =>
                ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                          (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)))) ∪
              (Finset.univ.filter (fun x : Fin N =>
                ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                          (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)))) ∪
              (Finset.univ.filter (fun x : Fin N =>
                ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                          (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)))) ∪
              (Finset.univ.filter (fun x : Fin N =>
                ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                          (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)))) := by
            intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hx ⊢
            rcases hx with h | h | h | h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
          have hle := Finset.card_le_card hu
          have hu1 := Finset.card_union_le
            ((Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)))) ∪
             (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)))) ∪
             (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)))))
            (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                        (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2))))
          have hu2 := Finset.card_union_le
            ((Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)))) ∪
             (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)))))
            (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2))))
          have hu3 := Finset.card_union_le
            (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2))))
            (Finset.univ.filter (fun x : Fin N =>
              ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                        (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2))))
          omega
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
        have hltN : m * 16384 < N := by omega
        exact lt_of_le_of_lt h1 hltN
      have hex : ∃ x0 : Fin N, x0 ∉ badA := by
        by_contra hall
        push_neg at hall
        have huniv : badA = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
        rw [huniv, Finset.card_univ, Fintype.card_fin] at hbad_lt
        exact lt_irrefl N hbad_lt
      rcases hex with ⟨x0, hx0⟩
      have hgood : ∀ j : Fin m,
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x0))
                   (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∧
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x0))
                   (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)) ∧
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x0)).2))
                   (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∧
          Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x0)).2))
                   (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)) := by
        intro j
        have hnot : x0 ∉ Finset.univ.filter (fun x : Fin N =>
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                      (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∨
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N false x))
                      (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2)) ∨
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                      (fwdArc (2 * N) 2048 (cycleIdx N false (f j).2)) ∨
            ¬Disjoint (fwdArc (2 * N) 2048 (cycleIdx N true (π (r0, x)).2))
                      (fwdArc (2 * N) 2048 (cycleIdx N true (π (f j)).2))) := by
          intro hmem
          exact hx0 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hmem⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hnot
        exact ⟨hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩
      let f' : Fin (m + 1) → Bool × Fin N := fun j =>
        if hj : j.val < m then f ⟨j.val, hj⟩ else (r0, x0)
      have hne_new : ∀ j : Fin m, (r0, x0) ≠ f j := by
        intro j heq
        have hx : x0 = (f j).2 := congrArg Prod.snd heq
        have hd := (hgood j).1
        rw [hx] at hd
        have hmem : cycleIdx N false (f j).2 ∈ fwdArc (2 * N) 2048 (cycleIdx N false (f j).2) := by
          refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
          apply Fin.ext
          change ((cycleIdx N false (f j).2).val + 0 % (2 * N)) % (2 * N) = (cycleIdx N false (f j).2).val
          simp [Nat.mod_eq_of_lt (cycleIdx N false (f j).2).isLt]
        exact Finset.disjoint_left.mp hd hmem hmem
      refine ⟨f', ?_, ?_⟩
      · intro j
        by_cases hj : j.val < m
        · simp only [f', hj, ↓reduceDIte]
          exact hpol ⟨j.val, hj⟩
        · have hjm : j.val = m := by omega
          simp only [f', hj, ↓reduceDIte]
          have hfin : (⟨j.val, by omega⟩ : Fin d) = ⟨m, hm⟩ := Fin.ext hjm
          rw [hfin]
      · intro j1 j2 hne
        by_cases h1 : j1.val < m <;> by_cases h2 : j2.val < m
        · simp only [f', h1, h2, ↓reduceDIte]
          have hne' : (⟨j1.val, h1⟩ : Fin m) ≠ ⟨j2.val, h2⟩ := by
            intro h; exact hne (Fin.ext (congrArg (fun x : Fin m => x.val) h))
          exact hsp ⟨j1.val, h1⟩ ⟨j2.val, h2⟩ hne'
        · simp only [f', h1, h2, ↓reduceDIte]
          have hg := hgood ⟨j1.val, h1⟩
          refine ⟨(hne_new ⟨j1.val, h1⟩).symm,
            fun _ => hg.1.symm, fun _ => hg.2.2.2.symm, fun _ => hg.2.2.1.symm⟩
        · simp only [f', h1, h2, ↓reduceDIte]
          have hg := hgood ⟨j2.val, h2⟩
          refine ⟨hne_new ⟨j2.val, h2⟩,
            fun _ => hg.1, fun _ => hg.2.2.2, fun _ => hg.2.1⟩
        · exfalso
          exact hne (Fin.ext (by omega))
  rcases hbuild d le_rfl with ⟨f, hpol, hsp⟩
  refine ⟨⟨f, fun j1 j2 h => by
    by_contra hne
    exact (hsp j1 j2 hne).1 h⟩, hpol, ?_⟩
  intro j1 j2 hne
  exact (hsp j1 j2 hne).2

lemma two_rail_amplifier (d : ℕ) (pol : Fin d → Bool) :
    ∃ b : ℕ, b + 1 = 16384 * (d + 1) ∧
      let I := Bool × Fin (b + 1)
      ∃ (π : Equiv.Perm I) (pick : Fin d ↪ I),
        (∀ i, (π i).1 = !(i.1)) ∧ (∀ j, (pick j).1 = pol j) ∧
        ∀ y : Bool × I → Bool,
          let mass := (Finset.univ.filter (fun u : Bool × I => y u = true)).card
          let red := (Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, i))).card
          let blue := (Finset.univ.filter (fun i : I =>
            y (false, i) ≠ y (true, (i.1, i.2 + 1)))).card
          let cuts := Finset.univ.image (fun j : Fin d => pick j)
          let cross := (Finset.univ.filter (fun i : I =>
            i ∉ cuts ∧ y (false, i) ≠ y (true, π i))).card
          let ports := ∑ j : Fin d, ((y (false, pick j)).toNat + (y (true, π (pick j))).toNat)
          2 * mass ≤ 4 * (b + 1) → mass + 65536 * ports ≤ 65536 * (red + blue + cross) := by
  classical
  let N := 16384 * (d + 1)
  have hNpos : 0 < N := by positivity
  let b := N - 1
  have hb : b + 1 = N := Nat.sub_add_cancel (by omega)
  haveI : NeZero (2 * (b + 1)) := ⟨by omega⟩
  rcases exists_expander_perms (b + 1) (by omega) with ⟨p0, p1, hexp⟩
  let π := mkCrossPerm (b + 1) p0 p1
  have hπ : ∀ i, (π i).1 = !i.1 := mkCrossPerm_fst (b + 1) p0 p1
  rcases exists_spaced_pick d pol (b + 1) (by omega) π hπ with ⟨pick, hpol, hsp⟩
  refine ⟨b, hb, π, pick, hπ, hpol, ?_⟩
  intro y
  dsimp only
  intro hmass_le
  set mass := (Finset.univ.filter (fun u : Bool × (Bool × Fin (b + 1)) => y u = true)).card
  set red := (Finset.univ.filter (fun i : Bool × Fin (b + 1) => y (false, i) ≠ y (true, i))).card
  set blue := (Finset.univ.filter (fun i : Bool × Fin (b + 1) =>
    y (false, i) ≠ y (true, (i.1, i.2 + 1)))).card
  set cuts := Finset.univ.image (fun j : Fin d => pick j)
  set cross := (Finset.univ.filter (fun i : Bool × Fin (b + 1) =>
    i ∉ cuts ∧ y (false, i) ≠ y (true, π i))).card
  set ports := ∑ j : Fin d, ((y (false, pick j)).toNat + (y (true, π (pick j))).toNat)
  have hcross_full : railCross0 (b + 1) y p0 + railCross1 (b + 1) y p1 =
      (Finset.univ.filter (fun i : Bool × Fin (b + 1) => y (false, i) ≠ y (true, π i))).card :=
    (card_filter_bool_prod (fun i : Bool × Fin (b + 1) => y (false, i) ≠ y (true, π i))).symm
  have hfull_le : railCross0 (b + 1) y p0 + railCross1 (b + 1) y p1 ≤ cross + ports := by
    rw [hcross_full]
    have hsplit : Finset.univ.filter (fun i : Bool × Fin (b + 1) => y (false, i) ≠ y (true, π i)) =
        (Finset.univ.filter (fun i : Bool × Fin (b + 1) => i ∉ cuts ∧ y (false, i) ≠ y (true, π i))) ∪
        (Finset.univ.filter (fun i : Bool × Fin (b + 1) => i ∈ cuts ∧ y (false, i) ≠ y (true, π i))) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hc : i ∈ cuts <;> simp [hc]
    rw [hsplit]
    have hle1 := Finset.card_union_le
      (Finset.univ.filter (fun i : Bool × Fin (b + 1) => i ∉ cuts ∧ y (false, i) ≠ y (true, π i)))
      (Finset.univ.filter (fun i : Bool × Fin (b + 1) => i ∈ cuts ∧ y (false, i) ≠ y (true, π i)))
    have hdel : (Finset.univ.filter (fun i : Bool × Fin (b + 1) =>
        i ∈ cuts ∧ y (false, i) ≠ y (true, π i))).card ≤ ports := by
      have hbij : (Finset.univ.filter (fun i : Bool × Fin (b + 1) =>
          i ∈ cuts ∧ y (false, i) ≠ y (true, π i))).card =
          (Finset.univ.filter (fun j : Fin d =>
            y (false, pick j) ≠ y (true, π (pick j)))).card := by
        refine (Finset.card_bij (fun j _ => pick j) ?_ ?_ ?_).symm
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          exact ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hj⟩
        · intro j1 _ j2 _ h; exact pick.injective h
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases Finset.mem_image.mp hi.1 with ⟨j, _, rfl⟩
          exact ⟨j, by simp [hi.2], rfl⟩
      rw [hbij]
      calc (Finset.univ.filter (fun j : Fin d => y (false, pick j) ≠ y (true, π (pick j)))).card
          = ∑ j : Fin d, if y (false, pick j) ≠ y (true, π (pick j)) then 1 else 0 := by
            rw [Finset.sum_boole, Nat.cast_id]
        _ ≤ ∑ j : Fin d, ((y (false, pick j)).toNat + (y (true, π (pick j))).toNat) := by
            apply Finset.sum_le_sum
            intro j _
            cases y (false, pick j) <;> cases y (true, π (pick j)) <;> simp
    exact le_trans hle1 (Nat.add_le_add_left hdel cross)
  have hexp_bound : mass ≤ 128 * (red + blue + cross + ports) := by
    have h1 := hexp y hmass_le
    change mass ≤ 128 * (red + blue + railCross0 (b + 1) y p0 + railCross1 (b + 1) y p1) at h1
    omega
  let Pr : Bool → Finset (Fin (2 * (b + 1))) := fun r =>
    ((Finset.univ.filter (fun j : Fin d => pol j = r)).image
      (fun j => cycleIdx (b + 1) false (pick j).2)) ∪
    ((Finset.univ.filter (fun j : Fin d => pol j = !r)).image
      (fun j => cycleIdx (b + 1) true (π (pick j)).2))
  have hPr_disj : ∀ r : Bool, ∀ p1 ∈ Pr r, ∀ p2 ∈ Pr r, p1 ≠ p2 →
      Disjoint (fwdArc (2 * (b + 1)) 2048 p1) (fwdArc (2 * (b + 1)) 2048 p2) := by
    intro r p1 hp1 p2 hp2 hne
    simp only [Pr, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp1 hp2
    rcases hp1 with ⟨j1, hj1, rfl⟩ | ⟨j1, hj1, rfl⟩ <;>
    rcases hp2 with ⟨j2, hj2, rfl⟩ | ⟨j2, hj2, rfl⟩
    · have hjne : j1 ≠ j2 := fun h => hne (by subst h; rfl)
      exact (hsp j1 j2 hjne).1 (hj1.trans hj2.symm)
    · have hjne : j1 ≠ j2 := fun h => by subst h; rw [hj1] at hj2; cases r <;> simp at hj2
      exact (hsp j1 j2 hjne).2.2 (by rw [hj1, hj2]; cases r <;> rfl)
    · have hjne : j2 ≠ j1 := fun h => by subst h; rw [hj2] at hj1; cases r <;> simp at hj1
      exact ((hsp j2 j1 hjne).2.2 (by rw [hj2, hj1]; cases r <;> rfl)).symm
    · have hjne : j1 ≠ j2 := fun h => hne (by subst h; rfl)
      exact (hsp j1 j2 hjne).2.1 (hj1.trans hj2.symm)
  have hports_eq : ports =
      ((Pr false).filter (fun p => railToCycle (b + 1) y false p = true)).card +
      ((Pr true).filter (fun p => railToCycle (b + 1) y true p = true)).card := by
    have hone_r : ∀ r : Bool,
        ((Pr r).filter (fun p => railToCycle (b + 1) y r p = true)).card =
        (Finset.univ.filter (fun j : Fin d => pol j = r ∧ y (false, pick j) = true)).card +
        (Finset.univ.filter (fun j : Fin d => pol j = !r ∧ y (true, π (pick j)) = true)).card := by
      intro r
      rw [Finset.filter_union, Finset.card_union_of_disjoint]
      · refine congrArg₂ HAdd.hAdd ?_ ?_
        · refine (Finset.card_bij (fun j _ => cycleIdx (b + 1) false (pick j).2) ?_ ?_ ?_).symm
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hj ⊢
            refine ⟨⟨j, hj.1, rfl⟩, ?_⟩
            rw [railToCycle_cycleIdx]
            have hfst : (pick j).1 = r := (hpol j).trans hj.1
            have hpair : (r, (pick j).2) = pick j := Prod.ext hfst.symm rfl
            rw [hpair]; exact hj.2
          · intro j1 hj1 j2 hj2 heq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
            have hsnd := cycleIdx_inj (b + 1) false heq
            have hfst : (pick j1).1 = (pick j2).1 := by rw [hpol, hpol, hj1.1, hj2.1]
            exact pick.injective (Prod.ext hfst hsnd)
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp
            rcases hp.1 with ⟨j, hj, rfl⟩
            refine ⟨j, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨hj, ?_⟩
            have h2 := hp.2
            rw [railToCycle_cycleIdx] at h2
            have hfst : (pick j).1 = r := (hpol j).trans hj
            have hpair : (r, (pick j).2) = pick j := Prod.ext hfst.symm rfl
            rwa [hpair] at h2
        · refine (Finset.card_bij (fun j _ => cycleIdx (b + 1) true (π (pick j)).2) ?_ ?_ ?_).symm
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hj ⊢
            refine ⟨⟨j, hj.1, rfl⟩, ?_⟩
            rw [railToCycle_cycleIdx]
            have hfst : (π (pick j)).1 = r := by rw [hπ, hpol, hj.1]; cases r <;> rfl
            have hpair : (r, (π (pick j)).2) = π (pick j) := Prod.ext hfst.symm rfl
            rw [hpair]; exact hj.2
          · intro j1 hj1 j2 hj2 heq
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj1 hj2
            have hsnd := cycleIdx_inj (b + 1) true heq
            have hfst : (π (pick j1)).1 = (π (pick j2)).1 := by
              rw [hπ, hπ, hpol, hpol, hj1.1, hj2.1]
            exact pick.injective (π.injective (Prod.ext hfst hsnd))
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp
            rcases hp.1 with ⟨j, hj, rfl⟩
            refine ⟨j, ?_, rfl⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨hj, ?_⟩
            have h2 := hp.2
            rw [railToCycle_cycleIdx] at h2
            have hfst : (π (pick j)).1 = r := by rw [hπ, hpol, hj]; cases r <;> rfl
            have hpair : (r, (π (pick j)).2) = π (pick j) := Prod.ext hfst.symm rfl
            rwa [hpair] at h2
      · rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_filter, Finset.mem_image] at hp1 hp2
        rcases hp1.1 with ⟨j1, _, rfl⟩
        rcases hp2.1 with ⟨j2, _, h⟩
        exact cycleIdx_ne_side (b + 1) (pick j1).2 (π (pick j2)).2 h.symm
    rw [hone_r false, hone_r true]
    have hsplit1 : (Finset.univ.filter (fun j : Fin d => pol j = false ∧ y (false, pick j) = true)).card +
        (Finset.univ.filter (fun j : Fin d => pol j = true ∧ y (false, pick j) = true)).card =
        ∑ j : Fin d, (y (false, pick j)).toNat := by
      rw [← Finset.card_union_of_disjoint]
      · have hun : (Finset.univ.filter (fun j : Fin d => pol j = false ∧ y (false, pick j) = true)) ∪
            (Finset.univ.filter (fun j : Fin d => pol j = true ∧ y (false, pick j) = true)) =
            Finset.univ.filter (fun j : Fin d => y (false, pick j) = true) := by
          ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases pol j <;> simp
        rw [hun, Finset.card_filter]
        apply Finset.sum_congr rfl
        intro j _; cases y (false, pick j) <;> rfl
      · rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [Finset.mem_filter] at h1 h2
        rw [h1.2.1] at h2; exact Bool.noConfusion h2.2.1
    have hsplit2 : (Finset.univ.filter (fun j : Fin d => pol j = !false ∧ y (true, π (pick j)) = true)).card +
        (Finset.univ.filter (fun j : Fin d => pol j = !true ∧ y (true, π (pick j)) = true)).card =
        ∑ j : Fin d, (y (true, π (pick j))).toNat := by
      rw [← Finset.card_union_of_disjoint]
      · have hun : (Finset.univ.filter (fun j : Fin d => pol j = !false ∧ y (true, π (pick j)) = true)) ∪
            (Finset.univ.filter (fun j : Fin d => pol j = !true ∧ y (true, π (pick j)) = true)) =
            Finset.univ.filter (fun j : Fin d => y (true, π (pick j)) = true) := by
          ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          cases pol j <;> simp
        rw [hun, Finset.card_filter]
        apply Finset.sum_congr rfl
        intro j _; cases y (true, π (pick j)) <;> rfl
      · rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [Finset.mem_filter] at h1 h2
        rw [h1.2.1] at h2; exact Bool.noConfusion h2.2.1
    have hports_sum : ports =
        (∑ j : Fin d, (y (false, pick j)).toNat) + (∑ j : Fin d, (y (true, π (pick j))).toNat) :=
      Finset.sum_add_distrib
    omega
  have hcp0 := cycle_port_bound (2 * (b + 1)) 2048 (by omega) (by omega) (Pr false)
    (hPr_disj false) (railToCycle (b + 1) y false)
  have hcp1 := cycle_port_bound (2 * (b + 1)) 2048 (by omega) (by omega) (Pr true)
    (hPr_disj true) (railToCycle (b + 1) y true)
  have hmass_eq := railToCycle_mass (b + 1) y
  have hbdry_eq := railToCycle_bdry (b + 1) y
  change (Finset.univ.filter (fun t : Fin (2 * (b + 1)) => railToCycle (b + 1) y false t = true)).card +
    (Finset.univ.filter (fun t : Fin (2 * (b + 1)) => railToCycle (b + 1) y true t = true)).card =
    mass at hmass_eq
  change (Finset.univ.filter (fun t : Fin (2 * (b + 1)) =>
      railToCycle (b + 1) y false t ≠ railToCycle (b + 1) y false (t + 1))).card +
    (Finset.univ.filter (fun t : Fin (2 * (b + 1)) =>
      railToCycle (b + 1) y true t ≠ railToCycle (b + 1) y true (t + 1))).card =
    red + blue at hbdry_eq
  have hports_bound : 4096 * ports ≤ 2 * mass + 2048 * (red + blue) := by omega
  omega

noncomputable def swapPairs {α : Type*} [DecidableEq α] {m : ℕ}
    (u v : Fin m → α)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdisj : ∀ e1 e2 : Fin m, u e1 ≠ v e2) : Equiv.Perm α := by
  classical
  let f : α → α := fun a =>
    if h1 : ∃ e : Fin m, u e = a then v (Classical.choose h1)
    else if h2 : ∃ e : Fin m, v e = a then u (Classical.choose h2)
    else a
  have hfu : ∀ e : Fin m, f (u e) = v e := by
    intro e
    have h1 : ∃ e' : Fin m, u e' = u e := ⟨e, rfl⟩
    simp only [f, h1, ↓reduceDIte]
    have hch : u (Classical.choose h1) = u e := Classical.choose_spec h1
    rw [hu hch]
  have hfv : ∀ e : Fin m, f (v e) = u e := by
    intro e
    have h1 : ¬∃ e' : Fin m, u e' = v e := by
      rintro ⟨e', he'⟩; exact hdisj e' e he'
    have h2 : ∃ e' : Fin m, v e' = v e := ⟨e, rfl⟩
    simp only [f, h1, ↓reduceDIte, h2]
    have hch : v (Classical.choose h2) = v e := Classical.choose_spec h2
    rw [hv hch]
  have hff : ∀ a : α, f (f a) = a := by
    intro a
    by_cases h1 : ∃ e : Fin m, u e = a
    · rcases h1 with ⟨e, rfl⟩
      rw [hfu e, hfv e]
    · by_cases h2 : ∃ e : Fin m, v e = a
      · rcases h2 with ⟨e, rfl⟩
        rw [hfv e, hfu e]
      · simp only [f, h1, h2, ↓reduceDIte]
  exact ⟨f, f, hff, hff⟩

lemma swapPairs_apply_left {α : Type*} [DecidableEq α] {m : ℕ}
    (u v : Fin m → α)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdisj : ∀ e1 e2 : Fin m, u e1 ≠ v e2) (e : Fin m) :
    swapPairs u v hu hv hdisj (u e) = v e := by
  classical
  change (if h1 : ∃ e' : Fin m, u e' = u e then v (Classical.choose h1)
    else if h2 : ∃ e' : Fin m, v e' = u e then u (Classical.choose h2)
    else u e) = v e
  have h1 : ∃ e' : Fin m, u e' = u e := ⟨e, rfl⟩
  simp only [h1, ↓reduceDIte]
  rw [hu (Classical.choose_spec h1)]

lemma swapPairs_apply_right {α : Type*} [DecidableEq α] {m : ℕ}
    (u v : Fin m → α)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdisj : ∀ e1 e2 : Fin m, u e1 ≠ v e2) (e : Fin m) :
    swapPairs u v hu hv hdisj (v e) = u e := by
  classical
  change (if h1 : ∃ e' : Fin m, u e' = v e then v (Classical.choose h1)
    else if h2 : ∃ e' : Fin m, v e' = v e then u (Classical.choose h2)
    else v e) = u e
  have h1 : ¬∃ e' : Fin m, u e' = v e := by rintro ⟨e', he'⟩; exact hdisj e' e he'
  have h2 : ∃ e' : Fin m, v e' = v e := ⟨e, rfl⟩
  simp only [h1, ↓reduceDIte, h2]
  rw [hv (Classical.choose_spec h2)]

lemma swapPairs_apply_other {α : Type*} [DecidableEq α] {m : ℕ}
    (u v : Fin m → α)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hdisj : ∀ e1 e2 : Fin m, u e1 ≠ v e2) (a : α)
    (h1 : ∀ e, u e ≠ a) (h2 : ∀ e, v e ≠ a) :
    swapPairs u v hu hv hdisj a = a := by
  classical
  change (if h1' : ∃ e' : Fin m, u e' = a then v (Classical.choose h1')
    else if h2' : ∃ e' : Fin m, v e' = a then u (Classical.choose h2')
    else a) = a
  have hn1 : ¬∃ e' : Fin m, u e' = a := by rintro ⟨e', he'⟩; exact h1 e' he'
  have hn2 : ¬∃ e' : Fin m, v e' = a := by rintro ⟨e', he'⟩; exact h2 e' he'
  simp only [hn1, hn2, ↓reduceDIte]

lemma main_proof :
    ∃ C : ℕ, 0 < C ∧ ∀ (v m : ℕ) (ep : Fin m → Bool → Fin v) (rhs : Fin m → Bool),
      let X := Fin v → Bool
      let add := fun (a b : Bool) => decide (a ≠ b)
      let bad := fun (x : X) => (Finset.univ.filter (fun e : Fin m =>
        add (x (ep e false)) (x (ep e true)) ≠ rhs e)).card
      let deg := fun (j : Fin v) => (Finset.univ.filter (fun p : Fin m × Bool => ep p.1 p.2 = j)).card
      ∃ n : ℕ, n ≤ C*(v+m) ∧
        let V := Bool × Fin n
        let Y := V → Bool
        ∃ (σ τ : Equiv.Perm (Fin n)) (owner : Fin n → Fin v) (neg : Fin n → Bool)
          (dec : Y → X),
          (∀ j : Fin v,
            let pos := (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = false)).card
            let inv := (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = true)).card
            0 < pos ∧ pos = inv ∧ pos + inv ≤ C*(1+deg j)) ∧
          let enc := fun (x : X) (p : V) => add (x (owner p.2)) (neg p.2)
          let cost := fun (y : Y) =>
            (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card +
            (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card +
            (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
          (∀ x : X, dec (enc x) = x ∧ cost (enc x) = 2 * bad x) ∧
          ∀ y : Y, (Finset.univ.filter (fun p : V => y p ≠ enc (dec y) p)).card +
            C*(2*bad (dec y)) ≤ C*cost y := by
  classical
  refine ⟨65536, by omega, ?_⟩
  intro v m ep rhs
  dsimp only
  let X := Fin v → Bool
  let xorB := fun (a b : Bool) => decide (a ≠ b)
  let bad := fun (x : X) => (Finset.univ.filter (fun e : Fin m =>
    xorB (x (ep e false)) (x (ep e true)) ≠ rhs e)).card
  let deg := fun (j : Fin v) => (Finset.univ.filter (fun p : Fin m × Bool => ep p.1 p.2 = j)).card
  let incSet := fun (j : Fin v) => Finset.univ.filter (fun p : Fin m × Bool => ep p.1 p.2 = j)
  let eInc : ∀ j : Fin v, Fin (deg j) ≃ {p : Fin m × Bool // p ∈ incSet j} := fun j =>
    (Fintype.equivFinOfCardEq (Fintype.card_coe (incSet j))).symm
  let pol : ∀ j : Fin v, Fin (deg j) → Bool := fun j k =>
    if (eInc j k).1.2 then rhs (eInc j k).1.1 else false
  have hamp : ∀ j : Fin v,
      ∃ b : ℕ, b + 1 = 16384 * (deg j + 1) ∧
        let I := Bool × Fin (b + 1)
        ∃ (π : Equiv.Perm I) (pick : Fin (deg j) ↪ I),
          (∀ i, (π i).1 = !(i.1)) ∧ (∀ k, (pick k).1 = pol j k) ∧
          ∀ y : Bool × I → Bool,
            let mass := (Finset.univ.filter (fun u : Bool × I => y u = true)).card
            let red := (Finset.univ.filter (fun i : I => y (false, i) ≠ y (true, i))).card
            let blue := (Finset.univ.filter (fun i : I =>
              y (false, i) ≠ y (true, (i.1, i.2 + 1)))).card
            let cuts := Finset.univ.image (fun k : Fin (deg j) => pick k)
            let cross := (Finset.univ.filter (fun i : I =>
              i ∉ cuts ∧ y (false, i) ≠ y (true, π i))).card
            let ports := ∑ k : Fin (deg j), ((y (false, pick k)).toNat + (y (true, π (pick k))).toNat)
            2 * mass ≤ 4 * (b + 1) → mass + 65536 * ports ≤ 65536 * (red + blue + cross) :=
    fun j => two_rail_amplifier (deg j) (pol j)
  choose b hb π pick hπ hpol hbound using hamp
  let Tot := Σ j : Fin v, Bool × Fin (b j + 1)
  let n := Fintype.card Tot
  have hdeg_sum : ∑ j : Fin v, deg j = 2 * m := by
    have h1 : ∑ j : Fin v, deg j =
        (Finset.univ.biUnion (fun j : Fin v => incSet j)).card := by
      rw [Finset.card_biUnion]
      intro j1 _ j2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [incSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (h1.symm.trans h2)
    have huniv : Finset.univ.biUnion (fun j : Fin v => incSet j) = (Finset.univ : Finset (Fin m × Bool)) := by
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, incSet, Finset.mem_filter]
      exact iff_true_intro ⟨ep p.1 p.2, rfl⟩
    rw [h1, huniv, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have hn_eq : n = ∑ j : Fin v, 2 * (b j + 1) := by
    simp only [n, Tot, Fintype.card_sigma, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  have hn_le : n ≤ 65536 * (v + m) := by
    rw [hn_eq]
    have h1 : ∑ j : Fin v, 2 * (b j + 1) = 32768 * (v + 2 * m) := by
      calc ∑ j : Fin v, 2 * (b j + 1)
          = ∑ j : Fin v, 32768 * (deg j + 1) := by
            apply Finset.sum_congr rfl; intro j _; rw [hb j]; ring
        _ = 32768 * ∑ j : Fin v, (deg j + 1) := by rw [Finset.mul_sum]
        _ = 32768 * ((∑ j : Fin v, deg j) + v) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              smul_eq_mul, mul_one]
        _ = 32768 * (v + 2 * m) := by rw [hdeg_sum]; ring
    omega
  refine ⟨n, hn_le, ?_⟩
  let eTot : Fin n ≃ Tot := (Fintype.equivFin Tot).symm
  let σTot : Equiv.Perm Tot :=
    { toFun := fun s => ⟨s.1, (s.2.1, s.2.2 + 1)⟩
      invFun := fun s => ⟨s.1, (s.2.1, s.2.2 - 1)⟩
      left_inv := fun ⟨j, r, k⟩ => by simp
      right_inv := fun ⟨j, r, k⟩ => by simp }
  let τ0Tot : Equiv.Perm Tot :=
    { toFun := fun s => ⟨s.1, π s.1 s.2⟩
      invFun := fun s => ⟨s.1, (π s.1).symm s.2⟩
      left_inv := fun ⟨j, i⟩ => by simp
      right_inv := fun ⟨j, i⟩ => by simp }
  let portOf : Fin m × Bool → Tot := fun p =>
    let j := ep p.1 p.2
    let k := (eInc j).symm ⟨p, by simp [incSet, j]⟩
    ⟨j, pick j k⟩
  have hportOf_inj : Function.Injective portOf := by
    intro p1 p2 h
    have h1 : ep p1.1 p1.2 = ep p2.1 p2.2 := congrArg Sigma.fst h
    have h2 : HEq (pick (ep p1.1 p1.2) ((eInc (ep p1.1 p1.2)).symm ⟨p1, by simp [incSet]⟩))
                  (pick (ep p2.1 p2.2) ((eInc (ep p2.1 p2.2)).symm ⟨p2, by simp [incSet]⟩)) :=
      (Sigma.mk.inj_iff.mp h).2
    generalize_proofs hp1 hp2 at h2
    have hsub : ∀ (j1 j2 : Fin v) (hj : j1 = j2) (k1 : Fin (deg j1)) (k2 : Fin (deg j2)),
        HEq (pick j1 k1) (pick j2 k2) →
        (eInc j1 k1).1 = (eInc j2 k2).1 := by
      intro j1 j2 hj k1 k2 hh
      subst hj
      have hk := (pick j1).injective (eq_of_heq hh)
      rw [hk]
    have heq := hsub _ _ h1 _ _ h2
    simpa only [Equiv.apply_symm_apply] using heq
  let uPort : Fin m → Tot := fun e => τ0Tot (portOf (e, false))
  let vPort : Fin m → Tot := fun e => τ0Tot (portOf (e, true))
  have huPort_inj : Function.Injective uPort :=
    τ0Tot.injective.comp (hportOf_inj.comp (fun _ _ h => congrArg Prod.fst h))
  have hvPort_inj : Function.Injective vPort :=
    τ0Tot.injective.comp (hportOf_inj.comp (fun _ _ h => congrArg Prod.fst h))
  have huv_disj : ∀ e1 e2 : Fin m, uPort e1 ≠ vPort e2 := by
    intro e1 e2 h
    have h1 := hportOf_inj (τ0Tot.injective h)
    have h2 := congrArg Prod.snd h1
    exact Bool.noConfusion h2
  let swTot : Equiv.Perm Tot := swapPairs uPort vPort huPort_inj hvPort_inj huv_disj
  let τTot : Equiv.Perm Tot := τ0Tot.trans swTot
  let σ : Equiv.Perm (Fin n) := (eTot.trans σTot).trans eTot.symm
  let τ : Equiv.Perm (Fin n) := (eTot.trans τTot).trans eTot.symm
  let owner : Fin n → Fin v := fun i => (eTot i).1
  let neg : Fin n → Bool := fun i => (eTot i).2.1
  let dec : (Bool × Fin n → Bool) → X := fun y j =>
    let zCount := (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) =>
      xorB (y (u.1, eTot.symm ⟨j, u.2⟩)) u.2.1 = true)).card
    decide (4 * (b j + 1) < 2 * zCount)
  have hport_eInc : ∀ (j : Fin v) (k : Fin (deg j)), portOf (eInc j k).1 = ⟨j, pick j k⟩ := by
    intro j k
    have hj : ep (eInc j k).1.1 (eInc j k).1.2 = j := (Finset.mem_filter.mp (eInc j k).2).2
    have haux : ∀ (j' : Fin v) (hj' : j' = j) (hp' : (eInc j k).1 ∈ incSet j'),
        (⟨j', pick j' ((eInc j').symm ⟨(eInc j k).1, hp'⟩)⟩ : Tot) = ⟨j, pick j k⟩ := by
      intro j' hj' hp'
      cases hj'
      have hsub : (⟨(eInc j k).1, hp'⟩ : {p : Fin m × Bool // p ∈ incSet j}) = eInc j k :=
        Subtype.ext rfl
      rw [hsub, Equiv.symm_apply_apply]
    exact haux _ hj _
  have heTot_fst : ∀ s : Tot, (eTot (eTot.symm s)).1 = s.1 := fun s => by
    rw [Equiv.apply_symm_apply]
  have heTot_snd : ∀ s : Tot, (eTot (eTot.symm s)).2.1 = s.2.1 := fun s => by
    rw [Equiv.apply_symm_apply]
  refine ⟨σ, τ, owner, neg, dec, ?_, ?_, ?_⟩
  · intro j
    have hcard : ∀ r : Bool,
        (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = r)).card = b j + 1 := by
      intro r
      have hbij : (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = r)).card =
          (Finset.univ : Finset (Fin (b j + 1))).card := by
        refine (Finset.card_bij (fun (k : Fin (b j + 1)) _ => eTot.symm ⟨j, (r, k)⟩) ?_ ?_ ?_).symm
        · intro k _
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, owner, neg, heTot_fst, heTot_snd]
        · intro k1 _ k2 _ h
          have h1 := eTot.symm.injective h
          have h2 : (r, k1) = (r, k2) := eq_of_heq (Sigma.mk.inj_iff.mp h1).2
          exact congrArg Prod.snd h2
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          rcases h1 : eTot i with ⟨j1, r1, k1⟩
          have hj1 : j1 = j := by have h := hi.1; simp only [owner, h1] at h; exact h
          have hr1 : r1 = r := (congrArg (fun p : Tot => p.2.1) h1).symm.trans hi.2
          subst hj1; subst hr1
          refine ⟨k1, Finset.mem_univ _, ?_⟩
          rw [← h1, Equiv.symm_apply_apply]
      rw [hbij, Finset.card_univ, Fintype.card_fin]
    change 0 < (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = false)).card ∧
      (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = false)).card =
        (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = true)).card ∧
      (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = false)).card +
        (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = true)).card ≤
        65536 * (1 + deg j)
    rw [hcard false, hcard true]
    have hbj := hb j
    omega
  · intro x
    have hxor_cancel : ∀ a b : Bool, xorB (xorB a b) b = a := by
      intro a b; cases a <;> cases b <;> rfl
    have hdec : dec (fun p => xorB (x (owner p.2)) (neg p.2)) = x := by
      funext j
      simp only [dec, owner, neg, heTot_fst, heTot_snd, hxor_cancel]
      cases hx : x j
      · have h0 : (Finset.univ.filter (fun _ : Bool × (Bool × Fin (b j + 1)) => false = true)).card = 0 := by
          simp
        rw [h0]
        simp
      · have hall : (Finset.univ.filter (fun _ : Bool × (Bool × Fin (b j + 1)) => true = true)).card =
            4 * (b j + 1) := by
          simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
          ring
        rw [hall]
        have hpos : 0 < b j + 1 := Nat.succ_pos (b j)
        simp [show 4 * (b j + 1) < 2 * (4 * (b j + 1)) by omega]
    refine ⟨hdec, ?_⟩
    have h1 : (Finset.univ.filter (fun i : Fin n =>
        xorB (x (owner i)) (neg i) ≠ xorB (x (owner i)) (neg i))).card = 0 := by
      simp
    have h2 : (Finset.univ.filter (fun i : Fin n =>
        xorB (x (owner i)) (neg i) ≠ xorB (x (owner (σ i))) (neg (σ i)))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _
      simp only [owner, neg, σ, Equiv.trans_apply, heTot_fst, heTot_snd, σTot, Equiv.coe_fn_mk,
        not_not]
    rw [h1, h2, zero_add, zero_add]
    have hport_neg_false : ∀ e : Fin m, (portOf (e, false)).2.1 = false := by
      intro e
      simp only [portOf, hpol]
      simp only [pol, Equiv.apply_symm_apply, Bool.false_eq_true, ↓reduceIte]
    have hport_neg_true : ∀ e : Fin m, (portOf (e, true)).2.1 = rhs e := by
      intro e
      simp only [portOf, hpol]
      simp only [pol, Equiv.apply_symm_apply, ↓reduceIte]
    have htau_cond : ∀ s : Tot,
        (xorB (x s.1) s.2.1 = xorB (x (τTot s).1) (τTot s).2.1) ↔
        ∃ e : Fin m, (s = portOf (e, false) ∨ s = portOf (e, true)) ∧
          xorB (x (ep e false)) (x (ep e true)) ≠ rhs e := by
      intro s
      by_cases hpf : ∃ e : Fin m, s = portOf (e, false)
      · rcases hpf with ⟨e, rfl⟩
        have hts : τTot (portOf (e, false)) = vPort e := by
          simp only [τTot, Equiv.trans_apply, swTot]
          exact swapPairs_apply_left uPort vPort huPort_inj hvPort_inj huv_disj e
        rw [hts]
        have hf1 : (portOf (e, false)).1 = ep e false := rfl
        have hf2 : (portOf (e, false)).2.1 = false := hport_neg_false e
        have hv1 : (vPort e).1 = ep e true := rfl
        have hv2 : (vPort e).2.1 = !(rhs e) := by
          simp only [vPort, τ0Tot, Equiv.coe_fn_mk, hπ, hport_neg_true]
        rw [hf2, hv2, hf1, hv1]
        constructor
        · intro heq
          exact ⟨e, Or.inl rfl, (xor_eq_iff_false (x (ep e false)) (x (ep e true)) (rhs e)).mp heq⟩
        · rintro ⟨e', he', hbad⟩
          have heq_e : e' = e := by
            rcases he' with h | h
            · exact (congrArg Prod.fst (hportOf_inj h)).symm
            · exact Bool.noConfusion (congrArg Prod.snd (hportOf_inj h))
          subst heq_e
          exact (xor_eq_iff_false (x (ep e' false)) (x (ep e' true)) (rhs e')).mpr hbad
      · by_cases hpt : ∃ e : Fin m, s = portOf (e, true)
        · rcases hpt with ⟨e, rfl⟩
          have hts : τTot (portOf (e, true)) = uPort e := by
            simp only [τTot, Equiv.trans_apply, swTot]
            exact swapPairs_apply_right uPort vPort huPort_inj hvPort_inj huv_disj e
          rw [hts]
          have ht1 : (portOf (e, true)).1 = ep e true := rfl
          have ht2 : (portOf (e, true)).2.1 = rhs e := hport_neg_true e
          have hu1 : (uPort e).1 = ep e false := rfl
          have hu2 : (uPort e).2.1 = true := by
            simp only [uPort, τ0Tot, Equiv.coe_fn_mk, hπ, hport_neg_false]; rfl
          rw [ht2, hu2, ht1, hu1]
          constructor
          · intro heq
            exact ⟨e, Or.inr rfl, (xor_eq_iff_true (x (ep e true)) (x (ep e false)) (rhs e)).mp heq |>
              fun h => by
                have hcomm : xorB (x (ep e false)) (x (ep e true)) = xorB (x (ep e true)) (x (ep e false)) := by
                  cases x (ep e false) <;> cases x (ep e true) <;> rfl
                rw [hcomm]; exact h⟩
          · rintro ⟨e', he', hbad⟩
            have heq_e : e' = e := by
              rcases he' with h | h
              · exact Bool.noConfusion (congrArg Prod.snd (hportOf_inj h))
              · exact (congrArg Prod.fst (hportOf_inj h)).symm
            subst heq_e
            have hcomm : xorB (x (ep e' false)) (x (ep e' true)) = xorB (x (ep e' true)) (x (ep e' false)) := by
              cases x (ep e' false) <;> cases x (ep e' true) <;> rfl
            rw [hcomm] at hbad
            exact (xor_eq_iff_true (x (ep e' true)) (x (ep e' false)) (rhs e')).mpr hbad
        · have hts : τTot s = τ0Tot s := by
            simp only [τTot, Equiv.trans_apply, swTot]
            apply swapPairs_apply_other
            · intro e he; exact hpf ⟨e, (τ0Tot.injective he).symm⟩
            · intro e he; exact hpt ⟨e, (τ0Tot.injective he).symm⟩
          rw [hts]
          have h1' : (τ0Tot s).1 = s.1 := rfl
          have h2' : (τ0Tot s).2.1 = !s.2.1 := hπ s.1 s.2
          rw [h2', h1']
          constructor
          · intro heq
            exfalso
            cases h1 : x s.1 <;> cases h2 : s.2.1 <;> simp [xorB, h1, h2] at heq
          · rintro ⟨e, he | he, _⟩
            · exact absurd ⟨e, he⟩ hpf
            · exact absurd ⟨e, he⟩ hpt
    have hcard_tau : (Finset.univ.filter (fun i : Fin n =>
        xorB (x (owner i)) (neg i) = xorB (x (owner (τ i))) (neg (τ i)))).card =
        (Finset.univ.filter (fun s : Tot =>
        xorB (x s.1) s.2.1 = xorB (x (τTot s).1) (τTot s).2.1)).card := by
      refine Finset.card_bij (fun i _ => eTot i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, owner, neg, τ,
          Equiv.trans_apply, heTot_fst, heTot_snd] at hi ⊢
        exact hi
      · intro i1 _ i2 _ h; exact eTot.injective h
      · intro s hs
        refine ⟨eTot.symm s, ?_, eTot.apply_symm_apply s⟩
        rw [Finset.mem_filter] at hs ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        change xorB (x (eTot (eTot.symm s)).1) (eTot (eTot.symm s)).2.1 =
          xorB (x (eTot (eTot.symm (τTot (eTot (eTot.symm s))))).1)
            (eTot (eTot.symm (τTot (eTot (eTot.symm s))))).2.1
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
        exact hs.2
    rw [hcard_tau]
    have hbij2 : (Finset.univ.filter (fun s : Tot =>
        xorB (x s.1) s.2.1 = xorB (x (τTot s).1) (τTot s).2.1)).card =
        (Finset.univ.filter (fun p : Fin m × Bool =>
        xorB (x (ep p.1 false)) (x (ep p.1 true)) ≠ rhs p.1)).card := by
      refine (Finset.card_bij (fun p _ => portOf p) ?_ ?_ ?_).symm
      · intro ⟨e, side⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        rw [htau_cond]
        cases side
        · exact ⟨e, Or.inl rfl, hp⟩
        · exact ⟨e, Or.inr rfl, hp⟩
      · intro p1 _ p2 _ h; exact hportOf_inj h
      · intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        rcases (htau_cond s).mp hs with ⟨e, rfl | rfl, hbad⟩
        · exact ⟨(e, false), by simp [hbad], rfl⟩
        · exact ⟨(e, true), by simp [hbad], rfl⟩
    rw [hbij2]
    have hprod : (Finset.univ.filter (fun p : Fin m × Bool =>
        xorB (x (ep p.1 false)) (x (ep p.1 true)) ≠ rhs p.1)).card =
        2 * bad x := by
      have heq : Finset.univ.filter (fun p : Fin m × Bool =>
          xorB (x (ep p.1 false)) (x (ep p.1 true)) ≠ rhs p.1) =
          (Finset.univ.filter (fun e : Fin m =>
            xorB (x (ep e false)) (x (ep e true)) ≠ rhs e)) ×ˢ (Finset.univ : Finset Bool) := by
        ext ⟨e, side⟩; simp
      rw [heq, Finset.card_product, Finset.card_univ, Fintype.card_bool, mul_comm]
    exact hprod
  · intro y
    let x := dec y
    let w : ∀ j : Fin v, Bool × (Bool × Fin (b j + 1)) → Bool := fun j u =>
      decide (y (u.1, eTot.symm ⟨j, u.2⟩) ≠ xorB (x j) u.2.1)
    have hw_mass_le : ∀ j : Fin v,
        2 * (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) => w j u = true)).card ≤
          4 * (b j + 1) := by
      intro j
      set zCount := (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) =>
        xorB (y (u.1, eTot.symm ⟨j, u.2⟩)) u.2.1 = true)).card
      have hx_def : x j = decide (4 * (b j + 1) < 2 * zCount) := rfl
      by_cases hgt : 4 * (b j + 1) < 2 * zCount
      · have hxj : x j = true := by rw [hx_def]; simp [hgt]
        have hcomp : (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) => w j u = true)).card +
            zCount = 4 * (b j + 1) := by
          have hun : (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) => w j u = true)) ∪
              (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) =>
                xorB (y (u.1, eTot.symm ⟨j, u.2⟩)) u.2.1 = true)) = Finset.univ := by
            ext u
            simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true,
              w, hxj]
            cases y (u.1, eTot.symm ⟨j, u.2⟩) <;> cases u.2.1 <;> simp [xorB]
          have hdisj : Disjoint
              (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) => w j u = true))
              (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) =>
                xorB (y (u.1, eTot.symm ⟨j, u.2⟩)) u.2.1 = true)) := by
            rw [Finset.disjoint_left]
            intro u h1 h2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, w, hxj] at h1 h2
            cases h_y : y (u.1, eTot.symm ⟨j, u.2⟩) <;> cases h_r : u.2.1 <;>
              simp [xorB, h_y, h_r] at h1 h2
          rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ]
          simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
          ring
        omega
      · have hxj : x j = false := by rw [hx_def]; simp [hgt]
        have heq : (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) => w j u = true)).card =
            zCount := by
          congr 1; ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, w, hxj]
          cases y (u.1, eTot.symm ⟨j, u.2⟩) <;> cases u.2.1 <;> decide
        omega
    have hamp_j : ∀ j : Fin v,
        (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) => w j u = true)).card +
        65536 * (∑ k : Fin (deg j), ((w j (false, pick j k)).toNat +
          (w j (true, π j (pick j k))).toNat)) ≤
        65536 * (
          (Finset.univ.filter (fun i : Bool × Fin (b j + 1) =>
            w j (false, i) ≠ w j (true, i))).card +
          (Finset.univ.filter (fun i : Bool × Fin (b j + 1) =>
            w j (false, i) ≠ w j (true, (i.1, i.2 + 1)))).card +
          (Finset.univ.filter (fun i : Bool × Fin (b j + 1) =>
            i ∉ Finset.univ.image (fun k : Fin (deg j) => pick j k) ∧
            w j (false, i) ≠ w j (true, π j i))).card) :=
      fun j => hbound j (w j) (hw_mass_le j)
    have hdist_eq : (Finset.univ.filter (fun p : Bool × Fin n =>
        y p ≠ xorB (x (owner p.2)) (neg p.2))).card =
        ∑ j : Fin v, (Finset.univ.filter (fun u : Bool × (Bool × Fin (b j + 1)) =>
          w j u = true)).card := by
      rw [← Finset.card_sigma]
      refine (Finset.card_bij (fun (q : Σ j : Fin v, Bool × (Bool × Fin (b j + 1))) _ =>
        (q.2.1, eTot.symm ⟨q.1, q.2.2⟩)) ?_ ?_ ?_).symm
      · intro ⟨j, side, r, k⟩ hu
        simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, w] at hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, owner, neg, heTot_fst, heTot_snd]
        exact of_decide_eq_true hu
      · intro ⟨j1, s1, rk1⟩ _ ⟨j2, s2, rk2⟩ _ h
        have hs : s1 = s2 := congrArg Prod.fst h
        have hi : (⟨j1, rk1⟩ : Tot) = ⟨j2, rk2⟩ := eTot.symm.injective (congrArg Prod.snd h)
        rcases Sigma.mk.inj_iff.mp hi with ⟨rfl, hrk⟩
        subst hs
        rw [eq_of_heq hrk]
      · intro ⟨side, i⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, owner, neg] at hp
        refine ⟨⟨(eTot i).1, (side, (eTot i).2)⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, w,
            Sigma.eta, Equiv.symm_apply_apply]
          exact decide_eq_true hp
        · simp only [Sigma.eta, Equiv.symm_apply_apply]
    have hred_eq : (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, i))).card =
        ∑ j : Fin v, (Finset.univ.filter (fun i : Bool × Fin (b j + 1) =>
          w j (false, i) ≠ w j (true, i))).card := by
      rw [← Finset.card_sigma]
      refine (Finset.card_bij (fun (s : Tot) _ => eTot.symm s) ?_ ?_ ?_).symm
      · intro ⟨j, r, k⟩ hu
        rw [Finset.mem_sigma] at hu
        have hu' : w j (false, (r, k)) ≠ w j (true, (r, k)) := (Finset.mem_filter.mp hu.2).2
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (decide_ne_xor_iff _ _ _).mp hu'⟩
      · intro s1 _ s2 _ h; exact eTot.symm.injective h
      · intro i hi
        have hi' : y (false, i) ≠ y (true, i) := (Finset.mem_filter.mp hi).2
        refine ⟨eTot i, ?_, Equiv.symm_apply_apply eTot i⟩
        rw [Finset.mem_sigma, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
        simp only [w, Sigma.eta, Equiv.symm_apply_apply]
        exact (decide_ne_xor_iff _ _ _).mpr hi'
    have hblue_eq : (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, σ i))).card =
        ∑ j : Fin v, (Finset.univ.filter (fun i : Bool × Fin (b j + 1) =>
          w j (false, i) ≠ w j (true, (i.1, i.2 + 1)))).card := by
      rw [← Finset.card_sigma]
      refine (Finset.card_bij (fun (s : Tot) _ => eTot.symm s) ?_ ?_ ?_).symm
      · intro ⟨j, r, k⟩ hu
        rw [Finset.mem_sigma] at hu
        have hu' : w j (false, (r, k)) ≠ w j (true, (r, k + 1)) := (Finset.mem_filter.mp hu.2).2
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply, σTot, Equiv.coe_fn_mk]
        exact (decide_ne_xor_iff _ _ _).mp hu'
      · intro s1 _ s2 _ h; exact eTot.symm.injective h
      · intro i hi
        have hi' : y (false, i) ≠ y (true, eTot.symm ⟨(eTot i).1, ((eTot i).2.1, (eTot i).2.2 + 1)⟩) :=
          (Finset.mem_filter.mp hi).2
        refine ⟨eTot i, ?_, Equiv.symm_apply_apply eTot i⟩
        rw [Finset.mem_sigma, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩
        simp only [w, Sigma.eta, Equiv.symm_apply_apply]
        exact (decide_ne_xor_iff _ _ _).mpr hi'
    let extPorts : Finset Tot := Finset.univ.image portOf
    have hcross_split :
        (∑ j : Fin v, (Finset.univ.filter (fun i : Bool × Fin (b j + 1) =>
          i ∉ Finset.univ.image (fun k : Fin (deg j) => pick j k) ∧
          w j (false, i) ≠ w j (true, π j i))).card) +
        (Finset.univ.filter (fun p : Fin m × Bool =>
          y (false, eTot.symm (portOf p)) = y (true, eTot.symm (τTot (portOf p))))).card =
        (Finset.univ.filter (fun i : Fin n => y (false, i) = y (true, τ i))).card := by
      have htau_tot : (Finset.univ.filter (fun i : Fin n => y (false, i) = y (true, τ i))).card =
          (Finset.univ.filter (fun s : Tot =>
            y (false, eTot.symm s) = y (true, eTot.symm (τTot s)))).card := by
        refine (Finset.card_bij (fun (s : Tot) _ => eTot.symm s) ?_ ?_ ?_).symm
        · intro s hs
          have hs' := (Finset.mem_filter.mp hs).2
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          simp only [τ, Equiv.trans_apply, Equiv.apply_symm_apply]
          exact hs'
        · intro s1 _ s2 _ h; exact eTot.symm.injective h
        · intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          refine ⟨eTot i, ?_, Equiv.symm_apply_apply eTot i⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          simpa only [τ, Equiv.trans_apply, Equiv.symm_apply_apply] using hi'
      rw [htau_tot]
      have hpart : (Finset.univ.filter (fun s : Tot =>
            y (false, eTot.symm s) = y (true, eTot.symm (τTot s)))).card =
          (Finset.univ.filter (fun s : Tot =>
            s ∉ extPorts ∧ y (false, eTot.symm s) = y (true, eTot.symm (τTot s)))).card +
          (Finset.univ.filter (fun s : Tot =>
            s ∈ extPorts ∧ y (false, eTot.symm s) = y (true, eTot.symm (τTot s)))).card := by
        rw [← Finset.card_union_of_disjoint]
        · congr 1; ext s
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
          tauto
        · rw [Finset.disjoint_left]
          intro s h1 h2
          simp only [Finset.mem_filter] at h1 h2
          exact h1.2.1 h2.2.1
      rw [hpart]
      congr 1
      · rw [← Finset.card_sigma]
        refine Finset.card_bij (fun s _ => s) ?_ (fun _ _ _ _ h => h) ?_
        · intro ⟨j, i⟩ hu
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hu ⊢
          have hnot_ext : (⟨j, i⟩ : Tot) ∉ extPorts := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨p, _, hp⟩
            have hj : ep p.1 p.2 = j := congrArg Sigma.fst hp
            have hk : i = pick j ((eInc j).symm ⟨p, by simp [incSet, hj]⟩) := by
              have h2 := (Sigma.mk.inj_iff.mp hp).2
              generalize_proofs hp' at h2
              revert h2
              cases hj
              intro h2
              exact (eq_of_heq h2).symm
            exact hu.1 (Finset.mem_image.mpr ⟨(eInc j).symm ⟨p, by simp [incSet, hj]⟩,
              Finset.mem_univ _, hk.symm⟩)
          have htau_eq : τTot ⟨j, i⟩ = ⟨j, π j i⟩ := by
            simp only [τTot, Equiv.trans_apply, swTot]
            apply swapPairs_apply_other
            · intro e he
              have := τ0Tot.injective he
              exact hnot_ext (Finset.mem_image.mpr ⟨(e, false), Finset.mem_univ _, this⟩)
            · intro e he
              have := τ0Tot.injective he
              exact hnot_ext (Finset.mem_image.mpr ⟨(e, true), Finset.mem_univ _, this⟩)
          refine ⟨hnot_ext, ?_⟩
          rw [htau_eq]
          have hne := hu.2
          simp only [w, hπ] at hne
          have hxor_not : xorB (x j) (!i.1) = !(xorB (x j) i.1) := by
            cases x j <;> cases i.1 <;> rfl
          rw [hxor_not] at hne
          exact (decide_ne_xor_not_iff _ _ _).mp hne
        · intro ⟨j, i⟩ hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          refine ⟨⟨j, i⟩, ?_, rfl⟩
          simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and]
          have hnot_cut : i ∉ Finset.univ.image (fun k : Fin (deg j) => pick j k) := by
            intro hmem
            rcases Finset.mem_image.mp hmem with ⟨k, _, rfl⟩
            exact hs.1 (Finset.mem_image.mpr ⟨(eInc j k).1, Finset.mem_univ _, hport_eInc j k⟩)
          have htau_eq : τTot ⟨j, i⟩ = ⟨j, π j i⟩ := by
            simp only [τTot, Equiv.trans_apply, swTot]
            apply swapPairs_apply_other
            · intro e he
              exact hs.1 (Finset.mem_image.mpr ⟨(e, false), Finset.mem_univ _, τ0Tot.injective he⟩)
            · intro e he
              exact hs.1 (Finset.mem_image.mpr ⟨(e, true), Finset.mem_univ _, τ0Tot.injective he⟩)
          refine ⟨hnot_cut, ?_⟩
          have heq := hs.2
          rw [htau_eq] at heq
          simp only [w, hπ]
          have hxor_not : xorB (x j) (!i.1) = !(xorB (x j) i.1) := by
            cases x j <;> cases i.1 <;> rfl
          rw [hxor_not]
          exact (decide_ne_xor_not_iff _ _ _).mpr heq
      · refine Finset.card_bij (fun p _ => portOf p) ?_ ?_ ?_
        · intro p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
          exact ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩, hp⟩
        · intro p1 _ p2 _ h; exact hportOf_inj h
        · intro s hs
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          rcases Finset.mem_image.mp hs.1 with ⟨p, _, rfl⟩
          exact ⟨p, by simp [hs.2], rfl⟩
    have hports_sum : ∑ j : Fin v, ∑ k : Fin (deg j),
        ((w j (false, pick j k)).toNat + (w j (true, π j (pick j k))).toNat) =
        ∑ p : Fin m × Bool,
          ((w (ep p.1 p.2) (false, (portOf p).2)).toNat +
           (w (ep p.1 p.2) (true, π (ep p.1 p.2) (portOf p).2)).toNat) := by
      have h1 : ∀ j : Fin v, ∑ k : Fin (deg j),
          ((w j (false, pick j k)).toNat + (w j (true, π j (pick j k))).toNat) =
          ∑ p ∈ incSet j,
            ((w (ep p.1 p.2) (false, (portOf p).2)).toNat +
             (w (ep p.1 p.2) (true, π (ep p.1 p.2) (portOf p).2)).toNat) := by
        intro j
        rw [← Finset.sum_coe_sort (incSet j)]
        refine Fintype.sum_equiv (eInc j) _ _ ?_
        intro k
        have haux : ∀ (s : Tot) (hs : s = ⟨j, pick j k⟩),
            ((w s.1 (false, s.2)).toNat + (w s.1 (true, π s.1 s.2)).toNat) =
            ((w j (false, pick j k)).toNat + (w j (true, π j (pick j k))).toNat) := by
          intro s hs; rw [hs]
        exact (haux (portOf (eInc j k).1) (hport_eInc j k)).symm
      simp_rw [h1]
      rw [← Finset.sum_biUnion]
      · have huniv : Finset.univ.biUnion (fun j : Fin v => incSet j) =
            (Finset.univ : Finset (Fin m × Bool)) := by
          ext p
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, incSet, Finset.mem_filter]
          exact iff_true_intro ⟨ep p.1 p.2, rfl⟩
        rw [huniv]
      · intro j1 _ j2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p h1 h2
        simp only [incSet, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact hne (h1.symm.trans h2)
    have hbad_bound : 2 * bad x ≤
        (Finset.univ.filter (fun p : Fin m × Bool =>
          y (false, eTot.symm (portOf p)) = y (true, eTot.symm (τTot (portOf p))))).card +
        ∑ p : Fin m × Bool,
          ((w (ep p.1 p.2) (false, (portOf p).2)).toNat +
           (w (ep p.1 p.2) (true, π (ep p.1 p.2) (portOf p).2)).toNat) := by
      have hport_neg_false : ∀ e : Fin m, (portOf (e, false)).2.1 = false := by
        intro e; simp only [portOf, hpol, pol, Equiv.apply_symm_apply, Bool.false_eq_true, ↓reduceIte]
      have hport_neg_true : ∀ e : Fin m, (portOf (e, true)).2.1 = rhs e := by
        intro e; simp only [portOf, hpol, pol, Equiv.apply_symm_apply, ↓reduceIte]
      have hstep : ∀ e : Fin m,
          (if xorB (x (ep e false)) (x (ep e true)) ≠ rhs e then 2 else 0) ≤
          (if y (false, eTot.symm (portOf (e, false))) = y (true, eTot.symm (τTot (portOf (e, false))))
            then 1 else 0) +
          (if y (false, eTot.symm (portOf (e, true))) = y (true, eTot.symm (τTot (portOf (e, true))))
            then 1 else 0) +
          ((w (ep e false) (false, (portOf (e, false)).2)).toNat +
           (w (ep e false) (true, π (ep e false) (portOf (e, false)).2)).toNat) +
          ((w (ep e true) (false, (portOf (e, true)).2)).toNat +
           (w (ep e true) (true, π (ep e true) (portOf (e, true)).2)).toNat) := by
        intro e
        have ht1 : τTot (portOf (e, false)) = vPort e := by
          simp only [τTot, Equiv.trans_apply, swTot]
          exact swapPairs_apply_left uPort vPort huPort_inj hvPort_inj huv_disj e
        have ht2 : τTot (portOf (e, true)) = uPort e := by
          simp only [τTot, Equiv.trans_apply, swTot]
          exact swapPairs_apply_right uPort vPort huPort_inj hvPort_inj huv_disj e
        rw [ht1, ht2]
        have hf_neg := hport_neg_false e
        have ht_neg := hport_neg_true e
        have hu_neg : (π (ep e false) (portOf (e, false)).2).1 = true := by
          rw [hπ, hf_neg]; rfl
        have hv_neg : (π (ep e true) (portOf (e, true)).2).1 = !(rhs e) := by
          rw [hπ, ht_neg]
        simp only [w, uPort, vPort, τ0Tot, Equiv.coe_fn_mk, hf_neg, ht_neg, hu_neg, hv_neg]
        have heq1 : (⟨ep e false, (portOf (e, false)).2⟩ : Tot) = portOf (e, false) := rfl
        have heq2 : (⟨ep e true, (portOf (e, true)).2⟩ : Tot) = portOf (e, true) := rfl
        rw [heq1, heq2]
        exact port_step_bool (x (ep e false)) (x (ep e true)) (rhs e)
          (y (false, eTot.symm (portOf (e, false))))
          (y (true, eTot.symm ⟨ep e true, π (ep e true) (portOf (e, true)).2⟩))
          (y (false, eTot.symm (portOf (e, true))))
          (y (true, eTot.symm ⟨ep e false, π (ep e false) (portOf (e, false)).2⟩))
      have hsum_step := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hstep e)
      have hlhs : ∑ e : Fin m, (if xorB (x (ep e false)) (x (ep e true)) ≠ rhs e then 2 else 0) =
          2 * bad x := by
        have h2 : ∀ e : Fin m,
            (if xorB (x (ep e false)) (x (ep e true)) ≠ rhs e then 2 else 0) =
            2 * (if xorB (x (ep e false)) (x (ep e true)) ≠ rhs e then 1 else 0) := by
          intro e; split_ifs <;> rfl
        simp_rw [h2, ← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]
        rfl
      have hrhs1 : ∑ e : Fin m,
          ((if y (false, eTot.symm (portOf (e, false))) = y (true, eTot.symm (τTot (portOf (e, false))))
              then 1 else 0) +
           (if y (false, eTot.symm (portOf (e, true))) = y (true, eTot.symm (τTot (portOf (e, true))))
              then 1 else 0)) =
          (Finset.univ.filter (fun p : Fin m × Bool =>
            y (false, eTot.symm (portOf p)) = y (true, eTot.symm (τTot (portOf p))))).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        simp only [Fintype.sum_bool]
        apply Finset.sum_congr rfl; intro e _; ring
      have hrhs2 : ∑ e : Fin m,
          (((w (ep e false) (false, (portOf (e, false)).2)).toNat +
            (w (ep e false) (true, π (ep e false) (portOf (e, false)).2)).toNat) +
           ((w (ep e true) (false, (portOf (e, true)).2)).toNat +
            (w (ep e true) (true, π (ep e true) (portOf (e, true)).2)).toNat)) =
          ∑ p : Fin m × Bool,
            ((w (ep p.1 p.2) (false, (portOf p).2)).toNat +
             (w (ep p.1 p.2) (true, π (ep p.1 p.2) (portOf p).2)).toNat) := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool]
        apply Finset.sum_congr rfl; intro e _; ring
      calc 2 * bad x
          = ∑ e : Fin m, (if xorB (x (ep e false)) (x (ep e true)) ≠ rhs e then 2 else 0) := hlhs.symm
        _ ≤ ∑ e : Fin m,
            ((if y (false, eTot.symm (portOf (e, false))) = y (true, eTot.symm (τTot (portOf (e, false))))
                then 1 else 0) +
             (if y (false, eTot.symm (portOf (e, true))) = y (true, eTot.symm (τTot (portOf (e, true))))
                then 1 else 0) +
             ((w (ep e false) (false, (portOf (e, false)).2)).toNat +
              (w (ep e false) (true, π (ep e false) (portOf (e, false)).2)).toNat) +
             ((w (ep e true) (false, (portOf (e, true)).2)).toNat +
              (w (ep e true) (true, π (ep e true) (portOf (e, true)).2)).toNat)) := hsum_step
        _ = (∑ e : Fin m,
              ((if y (false, eTot.symm (portOf (e, false))) = y (true, eTot.symm (τTot (portOf (e, false))))
                  then 1 else 0) +
               (if y (false, eTot.symm (portOf (e, true))) = y (true, eTot.symm (τTot (portOf (e, true))))
                  then 1 else 0))) +
            (∑ e : Fin m,
              (((w (ep e false) (false, (portOf (e, false)).2)).toNat +
                (w (ep e false) (true, π (ep e false) (portOf (e, false)).2)).toNat) +
               ((w (ep e true) (false, (portOf (e, true)).2)).toNat +
                (w (ep e true) (true, π (ep e true) (portOf (e, true)).2)).toNat))) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl; intro e _; ring
        _ = (Finset.univ.filter (fun p : Fin m × Bool =>
              y (false, eTot.symm (portOf p)) = y (true, eTot.symm (τTot (portOf p))))).card +
            ∑ p : Fin m × Bool,
              ((w (ep p.1 p.2) (false, (portOf p).2)).toNat +
               (w (ep p.1 p.2) (true, π (ep p.1 p.2) (portOf p).2)).toNat) := by
              rw [hrhs1, hrhs2]
    have hsum_amp := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hamp_j j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_amp
    rw [← hdist_eq, ← hred_eq, ← hblue_eq, hports_sum] at hsum_amp
    change (Finset.univ.filter (fun p : Bool × Fin n => y p ≠ xorB (x (owner p.2)) (neg p.2))).card +
        65536 * (2 * bad x) ≤
      65536 * ((Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false, i) ≠ y (true, σ i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false, i) = y (true, τ i))).card)
    omega

end PEqualNP.Outside.L_pcx_408_aux

theorem PEqualNP.Outside.L_pcx_408 :
    ∃ C : ℕ, 0 < C ∧ ∀ (v m : ℕ) (ep : Fin m → Bool → Fin v) (rhs : Fin m → Bool),
  let X := Fin v → Bool
  let add := fun (a b : Bool) => decide (a ≠ b)
  let bad := fun (x : X) => (Finset.univ.filter (fun e : Fin m =>
    add (x (ep e false)) (x (ep e true)) ≠ rhs e)).card
  let deg := fun (j : Fin v) => (Finset.univ.filter (fun p : Fin m × Bool => ep p.1 p.2 = j)).card
  ∃ n : ℕ, n ≤ C*(v+m) ∧
    let V := Bool × Fin n
    let Y := V → Bool
    ∃ (σ τ : Equiv.Perm (Fin n)) (owner : Fin n → Fin v) (neg : Fin n → Bool)
      (dec : Y → X),
      (∀ j : Fin v,
        let pos := (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = false)).card
        let inv := (Finset.univ.filter (fun i : Fin n => owner i = j ∧ neg i = true)).card
        0 < pos ∧ pos = inv ∧ pos + inv ≤ C*(1+deg j)) ∧
      let enc := fun (x : X) (p : V) => add (x (owner p.2)) (neg p.2)
      let cost := fun (y : Y) =>
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false,i) ≠ y (true,σ i))).card +
        (Finset.univ.filter (fun i : Fin n => y (false,i) = y (true,τ i))).card
      (∀ x : X, dec (enc x) = x ∧ cost (enc x) = 2 * bad x) ∧
      ∀ y : Y, (Finset.univ.filter (fun p : V => y p ≠ enc (dec y) p)).card +
        C*(2*bad (dec y)) ≤ C*cost y :=
  PEqualNP.Outside.L_pcx_408_aux.main_proof

