import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25908_aux

private def z2OfBool (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma z2OfBool_inj {a b : Bool} (h : z2OfBool a = z2OfBool b) : a = b := by
  cases a <;> cases b <;> simp [z2OfBool] at h <;> rfl

private lemma z2OfBool_xor (a b : Bool) : z2OfBool (xor a b) = z2OfBool a + z2OfBool b := by
  cases a <;> cases b <;> decide

private lemma z2OfBool_and (a b : Bool) : z2OfBool (a && b) = z2OfBool a * z2OfBool b := by
  cases a <;> cases b <;> decide

private lemma z2_nat_eq_mod2 (k : ℕ) : (k : ZMod 2) = z2OfBool (k % 2 == 1) := by
  have h : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases h with h0 | h1
  · have hdiv : 2 ∣ k := Nat.dvd_of_mod_eq_zero h0
    rcases hdiv with ⟨q, rfl⟩
    rw [Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul]
    simp [z2OfBool, h0]
  · have hEq : k = 2 * (k / 2) + 1 := by omega
    conv_lhs => rw [hEq]
    rw [Nat.cast_add, Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul, zero_add,
      Nat.cast_one]
    simp [z2OfBool, h1]

private lemma z2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl hx
  · rfl

private lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private def stepRun {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0

private lemma stepRun_succ {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n : ℕ) :
    stepRun ask x (n + 1) =
      stepRun ask x n + ((ask n (stepRun ask x n) x).toNat <<< n) := by
  simp only [stepRun, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private lemma stepRun_lt {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) :
    ∀ n : ℕ, stepRun ask x n < 2 ^ n
  | 0 => by simp [stepRun]
  | n + 1 => by
      rw [stepRun_succ, Nat.shiftLeft_eq]
      have ih := stepRun_lt ask x n
      cases ask n (stepRun ask x n) x <;> simp [pow_succ] <;> omega

private lemma testBit_add_shift {h n : ℕ} (hh : h < 2 ^ n) (b : Bool) (p : ℕ) :
    (h + (b.toNat <<< n)).testBit p =
      if p < n then h.testBit p else if p = n then b else false := by
  rw [Nat.shiftLeft_eq]
  cases b
  · simp only [Bool.toNat_false, zero_mul, add_zero]
    split_ifs with h1 h2
    · rfl
    · subst h2
      exact Nat.testBit_lt_two_pow hh
    · have hlt : h < 2 ^ p := lt_of_lt_of_le hh (Nat.pow_le_pow_right (by omega) (by omega))
      exact Nat.testBit_lt_two_pow hlt
  · simp only [Bool.toNat_true, one_mul]
    split_ifs with h1 h2
    · rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ^ n = 2 ^ p * 2 ^ (n - p) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
      have hdiv : (h + 2 ^ n) / 2 ^ p = h / 2 ^ p + 2 ^ (n - p) := by
        rw [hpow, Nat.add_mul_div_left _ _ (by positivity)]
      have heven : 2 ∣ 2 ^ (n - p) := by
        have hsub : 1 ≤ n - p := by omega
        have h2 : 2 ^ (n - p) = 2 * 2 ^ (n - p - 1) := by
          rw [← pow_succ', Nat.sub_add_cancel hsub]
        exact ⟨2 ^ (n - p - 1), h2⟩
      rw [hdiv]
      rcases heven with ⟨q, hq⟩
      rw [hq]
      simp [Nat.add_mul_mod_self_left]
    · subst h2
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (h + 2 ^ p) / 2 ^ p = 1 := by
        rw [Nat.add_div_right _ (by positivity), Nat.div_eq_of_lt hh]
      simp [hdiv]
    · have hlt : h + 2 ^ n < 2 ^ p := by
        have h2 : 2 ^ (n + 1) ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
        rw [pow_succ] at h2
        omega
      exact Nat.testBit_lt_two_pow hlt

private lemma stepRun_testBit {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) :
    ∀ n p : ℕ, p < n → (stepRun ask x n).testBit p = ask p (stepRun ask x p) x
  | 0, _, hp => by omega
  | n + 1, p, hp => by
      rw [stepRun_succ, testBit_add_shift (stepRun_lt ask x n)]
      by_cases hpn : p < n
      · simp only [hpn, ↓reduceIte]
        exact stepRun_testBit ask x n p hpn
      · have hpeq : p = n := by omega
        subst hpeq
        simp

private lemma stepRun_eq_iff {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n path : ℕ)
    (hpath : path < 2 ^ n) :
    stepRun ask x n = path ↔
      ∀ u : Fin n, ask u.val (path % 2 ^ u.val) x = path.testBit u.val := by
  constructor
  · intro heq u
    have hprev : stepRun ask x u.val = path % 2 ^ u.val := by
      apply Nat.eq_of_testBit_eq
      intro p
      rw [Nat.testBit_mod_two_pow]
      by_cases hp : p < u.val
      · simp only [hp, decide_true, Bool.true_and]
        rw [stepRun_testBit ask x u.val p hp, ← heq,
          stepRun_testBit ask x n p (lt_trans hp u.isLt)]
      · simp only [hp, decide_false, Bool.false_and]
        exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (stepRun_lt ask x u.val)
          (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [← hprev, ← stepRun_testBit ask x n u.val u.isLt, heq]
  · intro hall
    have hprefix : ∀ r : ℕ, r ≤ n → stepRun ask x r = path % 2 ^ r := by
      intro r
      induction r with
      | zero => intro _; simp [stepRun, Nat.mod_one]
      | succ r ih =>
        intro hr
        have hrlt : r < n := by omega
        have hih := ih (by omega)
        apply Nat.eq_of_testBit_eq
        intro p
        rw [stepRun_succ, testBit_add_shift (stepRun_lt ask x r), Nat.testBit_mod_two_pow]
        by_cases hpr : p < r
        · have hpr1 : p < r + 1 := by omega
          simp only [hpr, hpr1, ↓reduceIte, decide_true, Bool.true_and]
          rw [hih, Nat.testBit_mod_two_pow]
          simp [hpr]
        · by_cases hpeq : p = r
          · subst hpeq
            simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, decide_true, Bool.true_and]
            rw [hih]
            exact hall ⟨p, hrlt⟩
          · have hnlt : ¬(p < r + 1) := by omega
            simp [hpr, hpeq, hnlt]
    have hfin := hprefix n (le_refl n)
    rwa [Nat.mod_eq_of_lt hpath] at hfin

private lemma choose_two_pow_mod_two (s c : ℕ) (hc : c < 2 ^ (s + 1)) :
    c.choose (2 ^ s) % 2 = if 2 ^ s ≤ c then 1 else 0 := by
  by_cases hle : 2 ^ s ≤ c
  · simp only [hle, ↓reduceIte]
    have hq : c - 2 ^ s < 2 ^ s := by
      rw [pow_succ] at hc
      omega
    let q := c - 2 ^ s
    have hcq : c = 2 ^ s + q := by omega
    rw [hcq]
    have hpoly_pow : ∀ t : ℕ,
        ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ (2 ^ t)) =
        1 + Polynomial.X ^ (2 ^ t) := by
      intro t
      induction t with
      | zero => simp
      | succ t ih =>
        rw [pow_succ, pow_mul, ih]
        have h2 : ∀ A B : Polynomial (ZMod 2), (A + B) ^ 2 = A ^ 2 + B ^ 2 := by
          intro A B
          have hchar : (2 : Polynomial (ZMod 2)) = 0 := by
            calc
              (2 : Polynomial (ZMod 2)) = 1 + 1 := by ring
              _ = Polynomial.C (1 : ZMod 2) + Polynomial.C (1 : ZMod 2) := by rw [Polynomial.C_1]
              _ = Polynomial.C ((1 : ZMod 2) + 1) := Polynomial.C_add.symm
              _ = Polynomial.C 0 := by rfl
              _ = 0 := Polynomial.C_0
          calc
            (A + B) ^ 2 = A ^ 2 + 2 * (A * B) + B ^ 2 := by ring
            _ = A ^ 2 + B ^ 2 := by rw [hchar, zero_mul, add_zero]
        rw [h2, one_pow, ← pow_mul]
    have hmul :
        ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ (2 ^ s + q)) =
        (1 + Polynomial.X) ^ q + Polynomial.X ^ (2 ^ s) * (1 + Polynomial.X) ^ q := by
      rw [pow_add, hpoly_pow s, add_mul, one_mul]
    have hcoeff := congr_arg (fun P : Polynomial (ZMod 2) => P.coeff (2 ^ s)) hmul
    have hlhs :
        ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ (2 ^ s + q)).coeff (2 ^ s) =
        (((2 ^ s + q).choose (2 ^ s) : ℕ) : ZMod 2) := by
      rw [add_comm (1 : Polynomial (ZMod 2)) Polynomial.X, Polynomial.coeff_X_add_one_pow]
    have hrhs1 : ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ q).coeff (2 ^ s) = 0 := by
      refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
      have hdeg : ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ q).natDegree ≤ q := by
        calc
          ((1 + Polynomial.X : Polynomial (ZMod 2)) ^ q).natDegree
              ≤ q * (1 + Polynomial.X : Polynomial (ZMod 2)).natDegree :=
                Polynomial.natDegree_pow_le
          _ ≤ q * 1 := by
                refine Nat.mul_le_mul_left q ?_
                rw [add_comm]
                simp
          _ = q := mul_one q
      omega
    have hrhs2 :
        (Polynomial.X ^ (2 ^ s) * (1 + Polynomial.X : Polynomial (ZMod 2)) ^ q).coeff (2 ^ s) = 1 := by
      rw [Polynomial.coeff_X_pow_mul', Nat.sub_self]
      simp [Polynomial.coeff_zero_eq_eval_zero]
    rw [hlhs, Polynomial.coeff_add, hrhs1, hrhs2, zero_add] at hcoeff
    rw [z2_nat_eq_mod2] at hcoeff
    have hmod : ((2 ^ s + q).choose (2 ^ s) % 2 == 1) = true := z2OfBool_inj hcoeff
    simpa using hmod
  · simp only [hle, ↓reduceIte]
    have hlt : c < 2 ^ s := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]

private def Poly (V : Type*) := Finset V → ZMod 2

private def evalPoly {V : Type*} [Fintype V] [DecidableEq V] (P : Poly V) (x : V → Bool) : ZMod 2 :=
  ∑ mon : Finset V, P mon * ∏ v ∈ mon, z2OfBool (x v)

private def degLe {V : Type*} (P : Poly V) (b : ℕ) : Prop :=
  ∀ mon : Finset V, P mon ≠ 0 → mon.card ≤ b

private def polyZero (V : Type*) : Poly V := fun _ => 0

private def polyOne (V : Type*) [DecidableEq V] : Poly V := fun mon => if mon = ∅ then 1 else 0

private def polyVar {V : Type*} [DecidableEq V] (v : V) : Poly V :=
  fun mon => if mon = {v} then 1 else 0

private def polyMon {V : Type*} [DecidableEq V] (m0 : Finset V) : Poly V :=
  fun mon => if mon = m0 then 1 else 0

private def polyAdd {V : Type*} (P Q : Poly V) : Poly V := fun mon => P mon + Q mon

private def polyMul {V : Type*} [Fintype V] [DecidableEq V] (P Q : Poly V) : Poly V :=
  fun mon => ∑ m₁ : Finset V, ∑ m₂ : Finset V, if m₁ ∪ m₂ = mon then P m₁ * Q m₂ else 0

private lemma evalPoly_zero {V : Type*} [Fintype V] [DecidableEq V] (x : V → Bool) :
    evalPoly (polyZero V) x = 0 := by
  simp [evalPoly, polyZero]

private lemma evalPoly_one {V : Type*} [Fintype V] [DecidableEq V] (x : V → Bool) :
    evalPoly (polyOne V) x = 1 := by
  simp [evalPoly, polyOne]

private lemma evalPoly_var {V : Type*} [Fintype V] [DecidableEq V] (v : V) (x : V → Bool) :
    evalPoly (polyVar v) x = z2OfBool (x v) := by
  simp [evalPoly, polyVar]

private lemma evalPoly_mon {V : Type*} [Fintype V] [DecidableEq V] (m0 : Finset V) (x : V → Bool) :
    evalPoly (polyMon m0) x = ∏ v ∈ m0, z2OfBool (x v) := by
  simp [evalPoly, polyMon]

private lemma evalPoly_add {V : Type*} [Fintype V] [DecidableEq V] (P Q : Poly V) (x : V → Bool) :
    evalPoly (polyAdd P Q) x = evalPoly P x + evalPoly Q x := by
  simp only [evalPoly, polyAdd, add_mul, Finset.sum_add_distrib]

private lemma prod_z2_union {V : Type*} [DecidableEq V] (m₁ m₂ : Finset V) (x : V → Bool) :
    (∏ v ∈ m₁, z2OfBool (x v)) * (∏ v ∈ m₂, z2OfBool (x v)) =
    ∏ v ∈ m₁ ∪ m₂, z2OfBool (x v) := by
  have h1 : ∀ m : Finset V, ∏ v ∈ m, z2OfBool (x v) =
      if ∀ v ∈ m, x v = true then (1 : ZMod 2) else 0 := by
    intro m
    split_ifs with hall
    · refine Finset.prod_eq_one fun v hv => by
        have hxv := hall v hv
        simp [z2OfBool, hxv]
    · push Not at hall
      rcases hall with ⟨v, hv, hxv⟩
      have hxf : x v = false := by cases hx : x v <;> simp_all
      exact Finset.prod_eq_zero hv (by simp [z2OfBool, hxf])
  have hiff : (∀ v ∈ m₁ ∪ m₂, x v = true) ↔ (∀ v ∈ m₁, x v = true) ∧ (∀ v ∈ m₂, x v = true) := by
    constructor
    · intro h
      exact ⟨fun v hv => h v (Finset.mem_union_left _ hv), fun v hv => h v (Finset.mem_union_right _ hv)⟩
    · intro ⟨h₁, h₂⟩ v hv
      exact (Finset.mem_union.mp hv).elim (h₁ v) (h₂ v)
  rw [h1 m₁, h1 m₂, h1 (m₁ ∪ m₂)]
  simp_rw [hiff]
  split_ifs <;> first | exact mul_one _ | exact mul_zero _ | tauto

private lemma evalPoly_mul {V : Type*} [Fintype V] [DecidableEq V] (P Q : Poly V) (x : V → Bool) :
    evalPoly (polyMul P Q) x = evalPoly P x * evalPoly Q x := by
  simp only [evalPoly, polyMul]
  calc
    ∑ mon : Finset V,
        (∑ m₁ : Finset V, ∑ m₂ : Finset V, if m₁ ∪ m₂ = mon then P m₁ * Q m₂ else 0) *
        ∏ v ∈ mon, z2OfBool (x v)
        = ∑ mon : Finset V, ∑ m₁ : Finset V, ∑ m₂ : Finset V,
            if m₁ ∪ m₂ = mon then (P m₁ * Q m₂) * ∏ v ∈ mon, z2OfBool (x v) else 0 := by
          refine Finset.sum_congr rfl fun mon _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m₁ _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m₂ _ => by split_ifs <;> simp
    _ = ∑ m₁ : Finset V, ∑ mon : Finset V, ∑ m₂ : Finset V,
          if m₁ ∪ m₂ = mon then (P m₁ * Q m₂) * ∏ v ∈ mon, z2OfBool (x v) else 0 :=
          Finset.sum_comm
    _ = ∑ m₁ : Finset V, ∑ m₂ : Finset V, ∑ mon : Finset V,
          if m₁ ∪ m₂ = mon then (P m₁ * Q m₂) * ∏ v ∈ mon, z2OfBool (x v) else 0 := by
          refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_comm
    _ = ∑ m₁ : Finset V, ∑ m₂ : Finset V,
          (P m₁ * ∏ v ∈ m₁, z2OfBool (x v)) * (Q m₂ * ∏ v ∈ m₂, z2OfBool (x v)) := by
          refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
          simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← prod_z2_union]
          ring
    _ = (∑ m₁ : Finset V, P m₁ * ∏ v ∈ m₁, z2OfBool (x v)) *
        (∑ m₂ : Finset V, Q m₂ * ∏ v ∈ m₂, z2OfBool (x v)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun m₁ _ => (Finset.mul_sum ..).symm

private lemma degLe_zero {V : Type*} (b : ℕ) : degLe (polyZero V) b := fun _ h => absurd rfl h

private lemma degLe_one {V : Type*} [DecidableEq V] (b : ℕ) : degLe (polyOne V) b := by
  intro mon h
  simp only [polyOne] at h
  split_ifs at h with hm
  · subst hm; simp
  · exact absurd rfl h

private lemma degLe_var {V : Type*} [DecidableEq V] (v : V) : degLe (polyVar v) 1 := by
  intro mon h
  simp only [polyVar] at h
  split_ifs at h with hm
  · subst hm; simp
  · exact absurd rfl h

private lemma degLe_mon {V : Type*} [DecidableEq V] (m0 : Finset V) : degLe (polyMon m0) m0.card := by
  intro mon h
  simp only [polyMon] at h
  split_ifs at h with hm
  · subst hm; exact le_refl _
  · exact absurd rfl h

private lemma degLe_mono {V : Type*} {P : Poly V} {a b : ℕ} (h : degLe P a) (hab : a ≤ b) :
    degLe P b := fun mon hm => le_trans (h mon hm) hab

private lemma degLe_add {V : Type*} {P Q : Poly V} {b : ℕ} (hP : degLe P b) (hQ : degLe Q b) :
    degLe (polyAdd P Q) b := by
  intro mon h
  by_cases h1 : P mon = 0
  · simp only [polyAdd, h1, zero_add] at h
    exact hQ mon h
  · exact hP mon h1

private lemma degLe_mul {V : Type*} [Fintype V] [DecidableEq V] {P Q : Poly V} {a b : ℕ}
    (hP : degLe P a) (hQ : degLe Q b) :
    degLe (polyMul P Q) (a + b) := by
  intro mon h
  simp only [polyMul] at h
  by_contra hgt
  have hzero : ∀ m₁ : Finset V, ∀ m₂ : Finset V,
      (if m₁ ∪ m₂ = mon then P m₁ * Q m₂ else 0) = 0 := by
    intro m₁ m₂
    split_ifs with hu
    · by_cases h1 : P m₁ = 0
      · simp [h1]
      · by_cases h2 : Q m₂ = 0
        · simp [h2]
        · have hc1 := hP m₁ h1
          have hc2 := hQ m₂ h2
          have hcu : (m₁ ∪ m₂).card ≤ m₁.card + m₂.card := Finset.card_union_le m₁ m₂
          rw [hu] at hcu
          omega
    · rfl
  have hsum : ∑ m₁ : Finset V, ∑ m₂ : Finset V,
      (if m₁ ∪ m₂ = mon then P m₁ * Q m₂ else 0) = 0 :=
    Finset.sum_eq_zero fun m₁ _ => Finset.sum_eq_zero fun m₂ _ => hzero m₁ m₂
  exact h hsum

private def polySumList {V : Type*} : List (Poly V) → Poly V
  | [] => polyZero V
  | P :: Ps => polyAdd P (polySumList Ps)

private lemma evalPoly_sumList {V : Type*} [Fintype V] [DecidableEq V]
    (Ps : List (Poly V)) (x : V → Bool) :
    evalPoly (polySumList Ps) x = (Ps.map (fun P => evalPoly P x)).sum := by
  induction Ps with
  | nil => simp [polySumList, evalPoly_zero]
  | cons P Ps ih => simp [polySumList, evalPoly_add, ih]

private lemma degLe_sumList {V : Type*} {b : ℕ} (Ps : List (Poly V))
    (hPs : ∀ P ∈ Ps, degLe P b) :
    degLe (polySumList Ps) b := by
  induction Ps with
  | nil => exact degLe_zero b
  | cons P Ps ih =>
    exact degLe_add (hPs P (List.mem_cons_self ..))
      (ih fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ))

private lemma supp_sumList {V : Type*} (S : Finset (Finset V)) (Ps : List (Poly V))
    (hPs : ∀ P ∈ Ps, ∀ mon, P mon ≠ 0 → mon ∈ S) :
    ∀ mon, polySumList Ps mon ≠ 0 → mon ∈ S := by
  induction Ps with
  | nil => intro mon h; exact absurd rfl h
  | cons P Ps ih =>
    intro mon h
    by_cases h1 : P mon = 0
    · simp only [polySumList, polyAdd, h1, zero_add] at h
      exact ih (fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ)) mon h
    · exact hPs P (List.mem_cons_self ..) mon h1

private def polyProdList {V : Type*} [Fintype V] [DecidableEq V] : List (Poly V) → Poly V
  | [] => polyOne V
  | P :: Ps => polyMul P (polyProdList Ps)

private lemma evalPoly_prodList {V : Type*} [Fintype V] [DecidableEq V]
    (Ps : List (Poly V)) (x : V → Bool) :
    evalPoly (polyProdList Ps) x = (Ps.map (fun P => evalPoly P x)).prod := by
  induction Ps with
  | nil => simp [polyProdList, evalPoly_one]
  | cons P Ps ih => simp [polyProdList, evalPoly_mul, ih]

private lemma degLe_prodList {V : Type*} [Fintype V] [DecidableEq V] {d : ℕ}
    (Ps : List (Poly V)) (hPs : ∀ P ∈ Ps, degLe P d) :
    degLe (polyProdList Ps) (Ps.length * d) := by
  induction Ps with
  | nil =>
    simp only [polyProdList, List.length_nil, zero_mul]
    exact degLe_one 0
  | cons P Ps ih =>
    have h1 := degLe_mul (hPs P (List.mem_cons_self ..))
      (ih fun Q hQ => hPs Q (List.mem_cons_of_mem _ hQ))
    have hlen : d + Ps.length * d = (P :: Ps).length * d := by
      simp only [List.length_cons]
      ring
    rwa [hlen] at h1

private lemma prod_add_lowdeg {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 1 ≤ c) :
    ∀ Ps : List (Poly V × Poly V),
      (∀ pq ∈ Ps, degLe pq.1 c ∧ degLe pq.2 (c - 1)) →
      ∃ E : Poly V, degLe E (Ps.length * c - 1) ∧
        ∀ x : V → Bool,
          evalPoly (polyProdList (Ps.map (fun pq => polyAdd pq.1 pq.2))) x =
          evalPoly (polyProdList (Ps.map Prod.fst)) x + evalPoly E x
  | [], _ =>
      ⟨polyZero V, degLe_zero _, fun x => by simp [polyProdList, evalPoly_one, evalPoly_zero]⟩
  | [(U, Q)], hPs =>
      ⟨Q, by
        have h := (hPs (U, Q) (List.mem_cons_self ..)).2
        simp only [List.length_singleton, one_mul]
        exact h,
       fun x => by simp [polyProdList, evalPoly_mul, evalPoly_add, evalPoly_one]⟩
  | (U, Q) :: p :: rest, hPs => by
      have hUQ := hPs (U, Q) (List.mem_cons_self ..)
      rcases prod_add_lowdeg hc (p :: rest) (fun pq hpq => hPs pq (List.mem_cons_of_mem _ hpq)) with
        ⟨Erest, hEdeg, hEeval⟩
      let Urest := polyProdList ((p :: rest).map Prod.fst)
      have hUrest_deg : degLe Urest ((p :: rest).length * c) := by
        have h1 := degLe_prodList (d := c) ((p :: rest).map Prod.fst) (by
          intro P hP
          rcases List.mem_map.mp hP with ⟨pq, hpq, rfl⟩
          exact (hPs pq (List.mem_cons_of_mem _ hpq)).1)
        have hlen : ((p :: rest).map Prod.fst).length * c = (p :: rest).length * c := by
          simp [List.length_map]
        rwa [hlen] at h1
      let E := polyAdd (polyMul U Erest) (polyAdd (polyMul Q Urest) (polyMul Q Erest))
      have hlen_eq : ((U, Q) :: p :: rest).length * c = c + (p :: rest).length * c := by
        simp only [List.length_cons]
        ring
      have hpos_rest : 1 ≤ (p :: rest).length * c := by
        calc 1 ≤ c := hc
          _ = 1 * c := (one_mul c).symm
          _ ≤ (p :: rest).length * c := Nat.mul_le_mul_right c (by simp)
      have hE : degLe E (((U, Q) :: p :: rest).length * c - 1) := by
        rw [hlen_eq]
        refine degLe_add ?_ (degLe_add ?_ ?_)
        · exact degLe_mono (degLe_mul hUQ.1 hEdeg) (by omega)
        · exact degLe_mono (degLe_mul hUQ.2 hUrest_deg) (by omega)
        · exact degLe_mono (degLe_mul hUQ.2 hEdeg) (by omega)
      refine ⟨E, hE, fun x => ?_⟩
      change evalPoly (polyMul (polyAdd U Q) (polyProdList ((p :: rest).map (fun pq => polyAdd pq.1 pq.2)))) x =
        evalPoly (polyMul U Urest) x + evalPoly E x
      rw [evalPoly_mul, evalPoly_add, hEeval x]
      simp only [E, Urest, evalPoly_add, evalPoly_mul]
      ring

private lemma deg_of_poly {V : Type*} [Fintype V] [DecidableEq V]
    {b : ℕ} {f : (V → Bool) → Bool} (P : Poly V)
    (hdeg : degLe P b) (heval : ∀ x : V → Bool, z2OfBool (f x) = evalPoly P x) :
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1) := by
  classical
  let terms : Finset (Finset V) := Finset.univ.filter (fun mon => P mon ≠ 0)
  refine ⟨terms, ?_, ?_⟩
  · intro mon hm
    exact hdeg mon (Finset.mem_filter.mp hm).2
  · intro input
    apply z2OfBool_inj
    rw [heval input, ← z2_nat_eq_mod2]
    simp only [evalPoly]
    have hsub :
        ∑ mon : Finset V, P mon * ∏ v ∈ mon, z2OfBool (input v) =
        ∑ mon ∈ terms, ∏ v ∈ mon, z2OfBool (input v) := by
      have h1 : ∀ mon : Finset V,
          P mon * ∏ v ∈ mon, z2OfBool (input v) =
          if mon ∈ terms then ∏ v ∈ mon, z2OfBool (input v) else 0 := by
        intro mon
        by_cases hm : P mon = 0
        · simp [terms, hm]
        · have h1val : P mon = 1 := z2_eq_one_of_ne_zero hm
          simp [terms, h1val]
      simp_rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
    rw [hsub]
    have hterm : ∀ mon ∈ terms,
        ∏ v ∈ mon, z2OfBool (input v) =
        if ∀ v ∈ mon, input v = true then (1 : ZMod 2) else 0 := by
      intro mon _
      split_ifs with hall
      · refine Finset.prod_eq_one fun v hv => by
          have hxv := hall v hv
          simp [z2OfBool, hxv]
      · push Not at hall
        rcases hall with ⟨v, hv, hxv⟩
        have hxf : input v = false := by cases hx : input v <;> simp_all
        exact Finset.prod_eq_zero hv (by simp [z2OfBool, hxf])
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]

private lemma poly_of_deg {V : Type*} [Fintype V] [DecidableEq V]
    {b : ℕ} {f : (V → Bool) → Bool}
    (hf : ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)) :
    ∃ P : Poly V, degLe P b ∧ ∀ x : V → Bool, evalPoly P x = z2OfBool (f x) := by
  classical
  rcases hf with ⟨terms, hdeg, heval⟩
  let P : Poly V := fun mon => if mon ∈ terms then 1 else 0
  refine ⟨P, ?_, ?_⟩
  · intro mon hm
    simp only [P] at hm
    split_ifs at hm with hmem
    · exact hdeg mon hmem
    · exact absurd rfl hm
  · intro x
    rw [heval x, ← z2_nat_eq_mod2]
    simp only [evalPoly, P]
    have h1 : ∀ mon : Finset V,
        (if mon ∈ terms then (1 : ZMod 2) else 0) * ∏ v ∈ mon, z2OfBool (x v) =
        if mon ∈ terms then ∏ v ∈ mon, z2OfBool (x v) else 0 := by
      intro mon
      split_ifs <;> simp
    simp_rw [h1, Finset.sum_ite_mem, Finset.univ_inter]
    have hterm : ∀ mon ∈ terms,
        ∏ v ∈ mon, z2OfBool (x v) =
        if ∀ v ∈ mon, x v = true then (1 : ZMod 2) else 0 := by
      intro mon _
      split_ifs with hall
      · refine Finset.prod_eq_one fun v hv => by
          have hxv := hall v hv
          simp [z2OfBool, hxv]
      · push Not at hall
        rcases hall with ⟨v, hv, hxv⟩
        have hxf : x v = false := by cases hx : x v <;> simp_all
        exact Finset.prod_eq_zero hv (by simp [z2OfBool, hxf])
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]

private lemma cube_sum_mod2_indep {V : Type*} [Fintype V] [DecidableEq V]
    (v0 : V) (F : (V → Bool) → ZMod 2)
    (hindep : ∀ z : V → Bool, F (Function.update z v0 (!z v0)) = F z) :
    ∑ z : V → Bool, F z = 0 := by
  let S0 := (Finset.univ : Finset (V → Bool)).filter (fun z => z v0 = false)
  let S1 := (Finset.univ : Finset (V → Bool)).filter (fun z => z v0 = true)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [S0, S1, Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext z
    simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases z v0 <;> simp
  have hbij : ∑ z ∈ S0, F z = ∑ z ∈ S1, F z := by
    refine Finset.sum_bij (fun z _ => Function.update z v0 true) ?_ ?_ ?_ ?_
    · intro z _
      simp [S1]
    · intro z₁ hz₁ z₂ hz₂ hEq
      funext v
      by_cases hv : v = v0
      · subst hv
        rw [(Finset.mem_filter.mp hz₁).2, (Finset.mem_filter.mp hz₂).2]
      · have := congr_fun hEq v
        simpa [Function.update, hv] using this
    · intro z hz
      refine ⟨Function.update z v0 false, ?_, ?_⟩
      · simp [S0]
      · funext v
        by_cases hv : v = v0
        · subst hv
          simpa [Function.update] using (Finset.mem_filter.mp hz).2.symm
        · simp [Function.update, hv]
    · intro z hz
      have hzk : z v0 = false := (Finset.mem_filter.mp hz).2
      have hupd : Function.update z v0 (!z v0) = Function.update z v0 true := by simp [hzk]
      rw [← hupd, hindep z]
  rw [← hunion, Finset.sum_union hdisj, hbij]
  exact z2_add_self _

private lemma cube_sum_mod2_mon {V : Type*} [Fintype V] [DecidableEq V] (mon : Finset V) :
    ∑ z : V → Bool, ∏ v ∈ mon, z2OfBool (z v) =
      if mon = Finset.univ then (1 : ZMod 2) else 0 := by
  by_cases hu : mon = Finset.univ
  · subst hu
    simp only [↓reduceIte]
    have hsplit :
        ∑ z : V → Bool, ∏ v : V, z2OfBool (z v) =
        (∏ v : V, z2OfBool true) +
        ∑ z ∈ (Finset.univ : Finset (V → Bool)).erase (fun _ => true), ∏ v : V, z2OfBool (z v) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : V => true))]
    rw [hsplit]
    have h1 : ∏ _v : V, z2OfBool true = 1 := Finset.prod_eq_one fun _ _ => rfl
    have h2 : ∑ z ∈ (Finset.univ : Finset (V → Bool)).erase (fun _ => true),
        ∏ v : V, z2OfBool (z v) = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      have hne : z ≠ fun _ => true := (Finset.mem_erase.mp hz).1
      have hex : ∃ v : V, z v = false := by
        by_contra hall
        push Not at hall
        apply hne
        funext v
        cases hv : z v
        · exact absurd hv (hall v)
        · rfl
      rcases hex with ⟨v, hv⟩
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [z2OfBool, hv])
    rw [h1, h2, add_zero]
  · simp only [hu, ↓reduceIte]
    have hex : ∃ v0 : V, v0 ∉ mon := by
      by_contra hall
      push Not at hall
      apply hu
      ext v
      simp [hall v]
    rcases hex with ⟨v0, hv0⟩
    refine cube_sum_mod2_indep v0 _ ?_
    intro z
    refine Finset.prod_congr rfl fun v hv => ?_
    have hne : v ≠ v0 := fun h => hv0 (h ▸ hv)
    simp [Function.update, hne]

private def rot (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word j : ℕ) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

private def step (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

private def mix (k word : ℕ) : ℕ :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

private def stateAt (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ row)

private lemma stateAt_zero (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row key : ℕ) :
    stateAt k constant row 0 key = rot k 1 key ^^^ row := rfl

private lemma stateAt_succ (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row s key : ℕ) :
    stateAt k constant row (s + 1) key =
      step k (mix k (stateAt k constant row s key)) ^^^ rot k (2 * s) key ^^^
        (constant (s + 1)).val := by
  simp [stateAt, List.range_succ]

private lemma rot_lt (k s word : ℕ) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma xor_lt {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

private lemma testBit_rot {k s word b : ℕ} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

private lemma testBit_foldl_or (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

private lemma testBit_step_all (k word b : ℕ) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

private lemma testBit_step {k word b : ℕ} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

private lemma step_lt (k word : ℕ) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

private lemma stateAt_lt (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row : Fin (2 ^ k)) (rounds key : ℕ) :
    stateAt k constant row.val rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) row.isLt
  | succ s =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (s + 1)).isLt

private lemma testBit_mix {k word b : ℕ} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
    (mix k word).testBit b =
      xor (xor (word.testBit b) (word.testBit ((b + k - 1) % k)))
        (word.testBit ((b + 1) % k)) := by
  unfold mix
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot hw hb, testBit_rot hw hb]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have h3 : (b + k - (k - 1)) % k = (b + 1) % k := by congr 1; omega
  rw [h3]

private lemma mod_sub_eq {k p s : ℕ} (hk : 0 < k) (hsp : s ≤ p) :
    (p % k + k - s % k) % k = (p - s) % k := by
  have hdiv : p - s + s = p := Nat.sub_add_cancel hsp
  have h1 : (p % k + k - s % k + s % k) % k = p % k := by
    have hlt : s % k < k := Nat.mod_lt s hk
    have hadd : p % k + k - s % k + s % k = p % k + k := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_mod]
  have h2 : ((p - s) % k + s % k) % k = p % k := by
    rw [Nat.mod_add_mod, Nat.add_mod_mod, hdiv]
  set A := (p % k + k - s % k) % k
  set B := (p - s) % k
  set C := s % k
  have ha : A < k := Nat.mod_lt _ hk
  have hb : B < k := Nat.mod_lt _ hk
  have hs : C < k := Nat.mod_lt s hk
  have h3 : (A + C) % k = (B + C) % k := by
    rw [Nat.mod_add_mod, h1, ← h2]
  by_cases h1lt : A + C < k <;> by_cases h2lt : B + C < k
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega

private lemma testBit_stateAt_succ {k : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row : Fin (2 ^ k)) (s : ℕ) (key : Fin (2 ^ k)) (q : ℕ) (hq : 1 ≤ q) :
    (stateAt k constant row.val (s + 1) key.val).testBit (q % k) =
      let prev := fun r : ℕ => (stateAt k constant row.val s key.val).testBit (r % k)
      let m0 := xor (xor (prev q) (prev (q - 1))) (prev (q + 1))
      let m1 := xor (xor (prev (q + 1)) (prev q)) (prev (q + 2))
      let m2 := xor (xor (prev (q + 2)) (prev (q + 1))) (prev (q + 3))
      let st := xor m0 (!m1 && m2)
      xor (xor st ((rot k (2 * s) key.val).testBit (q % k)))
        ((constant (s + 1)).val.testBit (q % k)) := by
  have hk0 : 0 < k := by omega
  rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt q hk0)]
  unfold stepBit
  have hm : ∀ d : ℕ, (mix k (stateAt k constant row.val s key.val)).testBit ((q % k + d) % k) =
      xor (xor ((stateAt k constant row.val s key.val).testBit ((q + d) % k))
               ((stateAt k constant row.val s key.val).testBit ((q + d - 1) % k)))
          ((stateAt k constant row.val s key.val).testBit ((q + d + 1) % k)) := by
    intro d
    have hlt : (q % k + d) % k < k := Nat.mod_lt _ hk0
    rw [testBit_mix hk (stateAt_lt k constant row s key.val) hlt]
    have h0 : (q % k + d) % k = (q + d) % k := Nat.mod_add_mod q k d
    have h1 : ((q + d) % k + k - 1) % k = (q + d - 1) % k := by
      have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
      conv_lhs => rw [h1m]
      exact mod_sub_eq hk0 (by omega)
    have h2 : ((q + d) % k + 1) % k = (q + d + 1) % k := Nat.mod_add_mod (q + d) k 1
    rw [h0, h1, h2]
  have hm0 := hm 0
  simp only [Nat.add_zero, Nat.mod_mod] at hm0
  have hm1 := hm 1
  have hm2 := hm 2
  have he1 : q + 1 - 1 = q := by omega
  have he2 : q + 2 - 1 = q + 1 := by omega
  have he3 : q + 1 + 1 = q + 2 := by omega
  have he4 : q + 2 + 1 = q + 3 := by omega
  rw [he1, he3] at hm1
  rw [he2, he4] at hm2
  rw [hm0, hm1, hm2]

private def rawTwoRound (old6 old7 alpha beta e0 y0 y1 y2 : Bool) : Bool :=
  let old8 := xor old6 old7
  let z0 := xor old6 y0
  let z1 := xor (xor old8 y0) y1
  let z2 := xor (xor y0 y1) y2
  let f4 := beta
  let f5 := xor (!alpha) beta
  let f6 := xor alpha z0
  let f7 := xor beta (!z0 && z1)
  let f8 := xor (xor (xor z0 (!z1 && z2)) y0) e0
  let w5 := xor (xor f4 f5) f6
  let w6 := xor (xor f5 f6) f7
  let w7 := xor (xor f6 f7) f8
  xor w5 (!w6 && w7)

private lemma rawTwoRound_decomp (old6 old7 alpha beta e0 y0 y1 y2 : Bool) :
    let d0 := old6
    let d1 := old7
    let d2 := xor (xor (xor (xor true old7) alpha) beta) e0
    let res := fun a b c => xor (rawTwoRound old6 old7 alpha beta e0 a b c)
      ((xor a d0) && (xor b d1) && (xor c d2))
    let c0 := res false false false
    let l0 := xor (res true false false) c0
    let l1 := xor (res false true false) c0
    let l2 := xor (res false false true) c0
    rawTwoRound old6 old7 alpha beta e0 y0 y1 y2 =
      xor ((xor y0 d0) && (xor y1 d1) && (xor y2 d2))
        (xor (xor (xor c0 (l0 && y0)) (l1 && y1)) (l2 && y2)) := by
  cases old6 <;> cases old7 <;> cases alpha <;> cases beta <;>
    cases e0 <;> cases y0 <;> cases y1 <;> cases y2 <;> rfl

private lemma bool_xor_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

private lemma guarded_two_round_formula {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (p : ℕ)
    (hgood :
      let old := fun j : ℕ => (stateAt k constant row.val 0 ref.val).testBit ((p + j) % k)
      let first := fun j : ℕ => (stateAt k constant row.val 1 ref.val).testBit ((p + j) % k)
      let τ := xor (xor (old 6) (old 7)) (old 8)
      let α := xor (xor (xor (old 5) (old 6)) (old 7))
        (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
      let β := xor τ
        (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
      τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !α ∧ first 4 = β) :
    ∃ (s0 s1 s2 c0 l0 l1 l2 : Bool),
      ∀ key : Fin (2 ^ k),
        (∀ j : Fin 9,
          (stateAt k constant row.val 0 key.val).testBit ((p + j.val) % k) =
          (stateAt k constant row.val 0 ref.val).testBit ((p + j.val) % k)) →
        let u0 := key.val.testBit ((p + 8) % k)
        let u1 := key.val.testBit ((p + 9) % k)
        let u2 := key.val.testBit ((p + 10) % k)
        (stateAt k constant row.val 2 key.val).testBit ((p + 5) % k) =
          xor ((xor u0 s0) && (xor u1 s1) && (xor u2 s2))
            (xor (xor (xor c0 (l0 && u0)) (l1 && u1)) (l2 && u2)) := by
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  let oldRef := fun j : ℕ => (stateAt k constant row.val 0 ref.val).testBit ((p + j) % k)
  let firstRef := fun j : ℕ => (stateAt k constant row.val 1 ref.val).testBit ((p + j) % k)
  let τ := xor (xor (oldRef 6) (oldRef 7)) (oldRef 8)
  let inj1_6 := xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))
  let inj1_7 := xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k))
  let α := xor (xor (xor (oldRef 5) (oldRef 6)) (oldRef 7)) inj1_6
  let β := xor τ inj1_7
  rcases hgood with ⟨hτ, _, hf45, hf4⟩
  have hτ' : τ = false := hτ
  have hf4' : firstRef 4 = β := hf4
  have hf45' : xor (firstRef 4) (firstRef 5) = !α := hf45
  let row9 := row.val.testBit ((p + 9) % k)
  let row10 := row.val.testBit ((p + 10) % k)
  let row11 := row.val.testBit ((p + 11) % k)
  let c18 := (constant 1).val.testBit ((p + 8) % k)
  let e0 := xor row9 c18
  let i25 := xor ((rot k 2 ref.val).testBit ((p + 5) % k)) ((constant 2).val.testBit ((p + 5) % k))
  let d0 := oldRef 6
  let d1 := oldRef 7
  let d2 := xor (xor (xor (xor true (oldRef 7)) α) β) e0
  let res := fun a b c => xor (rawTwoRound (oldRef 6) (oldRef 7) α β e0 a b c)
    ((xor a d0) && (xor b d1) && (xor c d2))
  let rc0 := res false false false
  let rl0 := xor (res true false false) rc0
  let rl1 := xor (res false true false) rc0
  let rl2 := xor (res false false true) rc0
  let s0 := xor d0 row9
  let s1 := xor d1 row10
  let s2 := xor d2 row11
  let c0 := xor (xor (xor (xor rc0 (rl0 && row9)) (rl1 && row10)) (rl2 && row11)) i25
  refine ⟨s0, s1, s2, c0, rl0, rl1, rl2, ?_⟩
  intro key hpin u0 u1 u2
  have hbit0 : ∀ (kw : Fin (2 ^ k)) (j : ℕ), 1 ≤ j →
      (stateAt k constant row.val 0 kw.val).testBit ((p + j) % k) =
      xor (kw.val.testBit ((p + j - 1) % k)) (row.val.testBit ((p + j) % k)) := by
    intro kw j hj
    rw [stateAt_zero, Nat.testBit_xor, testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hsub := mod_sub_eq hk0 (p := p + j) (s := 1) (by omega)
    rw [h1m] at hsub ⊢
    rw [hsub]
  have hkey_pin : ∀ r : ℕ, r < 8 →
      key.val.testBit ((p + r) % k) = ref.val.testBit ((p + r) % k) := by
    intro r hr
    have hp1 := hpin ⟨r + 1, by omega⟩
    rw [hbit0 key (r + 1) (by omega), hbit0 ref (r + 1) (by omega)] at hp1
    have hsub : p + (r + 1) - 1 = p + r := by omega
    rw [hsub] at hp1
    have := congr_arg (fun b => xor b (row.val.testBit ((p + (r + 1)) % k))) hp1
    simpa [bool_xor_cancel] using this
  have hrot0_eq : ∀ (kw : Fin (2 ^ k)) (q : ℕ),
      (rot k 0 kw.val).testBit (q % k) = kw.val.testBit (q % k) := by
    intro kw q
    rw [testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    simp [Nat.zero_mod, Nat.add_mod_right]
  have hrot2_eq : ∀ (kw : Fin (2 ^ k)),
      (rot k 2 kw.val).testBit ((p + 5) % k) = kw.val.testBit ((p + 3) % k) := by
    intro kw
    rw [testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    have h2m : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have hsub := mod_sub_eq hk0 (p := p + 5) (s := 2) (by omega)
    rw [h2m] at hsub ⊢
    have hp3 : p + 5 - 2 = p + 3 := by omega
    rw [hsub, hp3]
  have hold_eq : ∀ j : ℕ, j < 9 →
      (stateAt k constant row.val 0 key.val).testBit ((p + j) % k) = oldRef j :=
    fun j hj => hpin ⟨j, hj⟩
  have hfirst4 : (stateAt k constant row.val 1 key.val).testBit ((p + 4) % k) = β := by
    rw [← hf4']
    change (stateAt k constant row.val 1 key.val).testBit ((p + 4) % k) =
      (stateAt k constant row.val 1 ref.val).testBit ((p + 4) % k)
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 4) (by omega),
        testBit_stateAt_succ hk2 constant row 0 ref (p + 4) (by omega)]
    have ha3 : p + 4 - 1 = p + 3 := by omega
    have ha5 : p + 4 + 1 = p + 5 := by omega
    have ha6 : p + 4 + 2 = p + 6 := by omega
    have ha7 : p + 4 + 3 = p + 7 := by omega
    simp only [ha3, ha5, ha6, ha7, mul_zero, hrot0_eq, hold_eq 3 (by omega),
      hold_eq 4 (by omega), hold_eq 5 (by omega), hold_eq 6 (by omega), hold_eq 7 (by omega),
      hkey_pin 4 (by omega)]
    rfl
  have hfirst5 : (stateAt k constant row.val 1 key.val).testBit ((p + 5) % k) = xor (!α) β := by
    have hf5 : firstRef 5 = xor (!α) β := by
      have h1 := congr_arg (fun b => xor b (firstRef 4)) hf45'
      have hcomm : xor (xor (firstRef 4) (firstRef 5)) (firstRef 4) = firstRef 5 := by
        cases firstRef 4 <;> cases firstRef 5 <;> rfl
      rw [hcomm, hf4'] at h1
      exact h1
    rw [← hf5]
    change (stateAt k constant row.val 1 key.val).testBit ((p + 5) % k) =
      (stateAt k constant row.val 1 ref.val).testBit ((p + 5) % k)
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 5) (by omega),
        testBit_stateAt_succ hk2 constant row 0 ref (p + 5) (by omega)]
    have ha4 : p + 5 - 1 = p + 4 := by omega
    have ha6 : p + 5 + 1 = p + 6 := by omega
    have ha7 : p + 5 + 2 = p + 7 := by omega
    have ha8 : p + 5 + 3 = p + 8 := by omega
    simp only [ha4, ha6, ha7, ha8, mul_zero, hrot0_eq, hold_eq 4 (by omega),
      hold_eq 5 (by omega), hold_eq 6 (by omega), hold_eq 7 (by omega), hold_eq 8 (by omega),
      hkey_pin 5 (by omega)]
    rfl
  let y0 := xor u0 row9
  let y1 := xor u1 row10
  let y2 := xor u2 row11
  have hy0_eq : (stateAt k constant row.val 0 key.val).testBit ((p + 9) % k) = y0 := by
    rw [hbit0 key 9 (by omega)]
    have : p + 9 - 1 = p + 8 := by omega
    rw [this]
  have hy1_eq : (stateAt k constant row.val 0 key.val).testBit ((p + 10) % k) = y1 := by
    rw [hbit0 key 10 (by omega)]
    have : p + 10 - 1 = p + 9 := by omega
    rw [this]
  have hy2_eq : (stateAt k constant row.val 0 key.val).testBit ((p + 11) % k) = y2 := by
    rw [hbit0 key 11 (by omega)]
    have : p + 11 - 1 = p + 10 := by omega
    rw [this]
  have hold8_eq : oldRef 8 = xor (oldRef 6) (oldRef 7) := by
    have : xor (xor (oldRef 6) (oldRef 7)) (oldRef 8) = false := hτ
    cases h6 : oldRef 6 <;> cases h7 : oldRef 7 <;> cases h8 : oldRef 8 <;> simp_all
  have hfirst6 : (stateAt k constant row.val 1 key.val).testBit ((p + 6) % k) =
      xor α (xor (oldRef 6) y0) := by
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 6) (by omega)]
    have ha5 : p + 6 - 1 = p + 5 := by omega
    have ha7 : p + 6 + 1 = p + 7 := by omega
    have ha8 : p + 6 + 2 = p + 8 := by omega
    have ha9 : p + 6 + 3 = p + 9 := by omega
    simp only [ha5, ha7, ha8, ha9, mul_zero, hrot0_eq, hold_eq 5 (by omega),
      hold_eq 6 (by omega), hold_eq 7 (by omega), hold_eq 8 (by omega), hy0_eq,
      hkey_pin 6 (by omega)]
    have hα_def : α = xor (xor (xor (oldRef 5) (oldRef 6)) (oldRef 7))
        (xor (ref.val.testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))) := by
      simp only [α, inj1_6, hrot0_eq]
    rw [hα_def, hold8_eq]
    cases oldRef 5 <;> cases oldRef 6 <;> cases oldRef 7 <;> cases y0 <;>
      cases ref.val.testBit ((p + 6) % k) <;> cases (constant 1).val.testBit ((p + 6) % k) <;> rfl
  have hfirst7 : (stateAt k constant row.val 1 key.val).testBit ((p + 7) % k) =
      xor β (!(xor (oldRef 6) y0) && xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1) := by
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 7) (by omega)]
    have ha6 : p + 7 - 1 = p + 6 := by omega
    have ha8 : p + 7 + 1 = p + 8 := by omega
    have ha9 : p + 7 + 2 = p + 9 := by omega
    have ha10 : p + 7 + 3 = p + 10 := by omega
    simp only [ha6, ha8, ha9, ha10, mul_zero, hrot0_eq, hold_eq 6 (by omega),
      hold_eq 7 (by omega), hold_eq 8 (by omega), hy0_eq, hy1_eq, hkey_pin 7 (by omega)]
    have hβ_def : β = xor (ref.val.testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)) := by
      simp only [β, hτ', inj1_7, hrot0_eq, Bool.false_xor]
    rw [hβ_def, hold8_eq]
    cases oldRef 6 <;> cases oldRef 7 <;> cases y0 <;> cases y1 <;>
      cases ref.val.testBit ((p + 7) % k) <;> cases (constant 1).val.testBit ((p + 7) % k) <;> rfl
  have hfirst8 : (stateAt k constant row.val 1 key.val).testBit ((p + 8) % k) =
      xor (xor (xor (xor (oldRef 6) y0)
        (!(xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1) && xor (xor y0 y1) y2)) y0) e0 := by
    rw [testBit_stateAt_succ hk2 constant row 0 key (p + 8) (by omega)]
    have ha7 : p + 8 - 1 = p + 7 := by omega
    have ha9 : p + 8 + 1 = p + 9 := by omega
    have ha10 : p + 8 + 2 = p + 10 := by omega
    have ha11 : p + 8 + 3 = p + 11 := by omega
    simp only [ha7, ha9, ha10, ha11, mul_zero, hrot0_eq, hold_eq 7 (by omega),
      hold_eq 8 (by omega), hy0_eq, hy1_eq, hy2_eq]
    have hu0_y0 : key.val.testBit ((p + 8) % k) = xor y0 row9 := by
      simp only [y0, u0, bool_xor_cancel]
    rw [hu0_y0, hold8_eq]
    simp only [e0, c18]
    cases oldRef 6 <;> cases oldRef 7 <;> cases y0 <;> cases y1 <;> cases y2 <;>
      cases row9 <;> cases (constant 1).val.testBit ((p + 8) % k) <;> rfl
  rw [testBit_stateAt_succ hk2 constant row 1 key (p + 5) (by omega)]
  have ha4 : p + 5 - 1 = p + 4 := by omega
  have ha6 : p + 5 + 1 = p + 6 := by omega
  have ha7 : p + 5 + 2 = p + 7 := by omega
  have ha8 : p + 5 + 3 = p + 8 := by omega
  simp only [ha4, ha6, ha7, ha8, mul_one, hfirst4, hfirst5, hfirst6, hfirst7, hfirst8]
  have hi25_eq :
      xor ((rot k 2 key.val).testBit ((p + 5) % k)) ((constant 2).val.testBit ((p + 5) % k)) = i25 := by
    simp only [i25, hrot2_eq, hkey_pin 3 (by omega)]
  have hxor_assoc : ∀ a b c : Bool, xor (xor a b) c = xor a (xor b c) := by
    intro a b c; cases a <;> cases b <;> cases c <;> rfl
  rw [hxor_assoc, hi25_eq]
  have hraw :
      xor (xor (xor (xor (!α) β) β) (xor α (xor (oldRef 6) y0)))
        (!(xor (xor (xor α (xor (oldRef 6) y0)) (xor (!α) β))
          (xor β (!(xor (oldRef 6) y0) && xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1))) &&
          xor (xor (xor β (!(xor (oldRef 6) y0) && xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1))
            (xor α (xor (oldRef 6) y0)))
            (xor (xor (xor (xor (oldRef 6) y0)
              (!(xor (xor (xor (oldRef 6) (oldRef 7)) y0) y1) && xor (xor y0 y1) y2)) y0) e0)) =
      rawTwoRound (oldRef 6) (oldRef 7) α β e0 y0 y1 y2 := by
    simp only [rawTwoRound]
    cases oldRef 6 <;> cases oldRef 7 <;> cases α <;> cases β <;> cases e0 <;>
      cases y0 <;> cases y1 <;> cases y2 <;> rfl
  rw [hraw, rawTwoRound_decomp]
  have hshift : ∀ a0 a1 a2 r0 r1 r2 q0 q1 q2 k0 k1 k2 k3 k4 : Bool,
      xor (xor ((xor (xor a0 r0) q0) && (xor (xor a1 r1) q1) && (xor (xor a2 r2) q2))
          (xor (xor (xor k0 (k1 && xor a0 r0)) (k2 && xor a1 r1)) (k3 && xor a2 r2))) k4 =
      xor ((xor a0 (xor q0 r0)) && (xor a1 (xor q1 r1)) && (xor a2 (xor q2 r2)))
          (xor (xor (xor (xor (xor (xor (xor k0 (k1 && r0)) (k2 && r1)) (k3 && r2)) k4)
            (k1 && a0)) (k2 && a1)) (k3 && a2)) := by
    intro a0 a1 a2 r0 r1 r2 q0 q1 q2 k0 k1 k2 k3 k4
    apply z2OfBool_inj
    simp only [z2OfBool_xor, z2OfBool_and]
    ring
  exact hshift u0 u1 u2 row9 row10 row11 d0 d1 d2 rc0 rl0 rl1 rl2 i25

private lemma pullPoly_exists {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (idx : V ↪ Fin k) (s : V → Bool) (e : Fin k → Bool)
    (P : Poly (Fin k)) {u : ℕ} (hdeg : degLe P u) :
    ∃ Q : Poly V, degLe Q u ∧
      ∀ y : V → Bool,
        evalPoly Q y = evalPoly P (fun q : Fin k =>
          if h : ∃ v : V, idx v = q then xor (y (Classical.choose h)) (s (Classical.choose h))
          else e q) := by
  classical
  let pullVar : Fin k → Poly V := fun q =>
    if h : ∃ v : V, idx v = q then
      if s (Classical.choose h) then polyAdd (polyOne V) (polyVar (Classical.choose h))
      else polyVar (Classical.choose h)
    else if e q then polyOne V else polyZero V
  have hpull_deg : ∀ q : Fin k, degLe (pullVar q) 1 := by
    intro q
    simp only [pullVar]
    split_ifs
    · exact degLe_add (degLe_one 1) (degLe_var _)
    · exact degLe_var _
    · exact degLe_one 1
    · exact degLe_zero 1
  have hpull_eval : ∀ q : Fin k, ∀ y : V → Bool,
      evalPoly (pullVar q) y =
      z2OfBool (if h : ∃ v : V, idx v = q then xor (y (Classical.choose h)) (s (Classical.choose h))
        else e q) := by
    intro q y
    simp only [pullVar]
    split_ifs with h hs he
    · rw [evalPoly_add, evalPoly_one, evalPoly_var, hs]
      cases y (Classical.choose h) <;> decide
    · rw [evalPoly_var]
      have hsf : s (Classical.choose h) = false := by cases hs' : s (Classical.choose h) <;> simp_all
      rw [hsf]
      cases y (Classical.choose h) <;> rfl
    · rw [evalPoly_one, he]; rfl
    · rw [evalPoly_zero]
      have hef : e q = false := by cases he' : e q <;> simp_all
      rw [hef]; rfl
  let suppList := (Finset.univ.filter (fun mon : Finset (Fin k) => P mon ≠ 0)).toList
  let Q : Poly V := polySumList (suppList.map (fun mon => polyProdList (mon.toList.map pullVar)))
  refine ⟨Q, ?_, ?_⟩
  · refine degLe_sumList _ ?_
    intro R hR
    rcases List.mem_map.mp hR with ⟨mon, hmon, rfl⟩
    have hPne : P mon ≠ 0 := (Finset.mem_filter.mp (Finset.mem_toList.mp hmon)).2
    have h1 := degLe_prodList (d := 1) (mon.toList.map pullVar) (by
      intro T hT
      rcases List.mem_map.mp hT with ⟨q, _, rfl⟩
      exact hpull_deg q)
    have hlen : (mon.toList.map pullVar).length * 1 ≤ u := by
      simp [Finset.length_toList]
      exact hdeg mon hPne
    exact degLe_mono h1 hlen
  · intro y
    simp only [Q, evalPoly_sumList, List.map_map]
    have hsum_eq :
        (suppList.map ((fun R => evalPoly R y) ∘ (fun mon => polyProdList (mon.toList.map pullVar)))).sum =
        ∑ mon ∈ Finset.univ.filter (fun mon : Finset (Fin k) => P mon ≠ 0),
          evalPoly (polyProdList (mon.toList.map pullVar)) y := by
      rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList (Finset.univ.filter _),
        Multiset.map_coe, Multiset.sum_coe]
      rfl
    rw [hsum_eq]
    have hterm : ∀ mon ∈ Finset.univ.filter (fun mon : Finset (Fin k) => P mon ≠ 0),
        evalPoly (polyProdList (mon.toList.map pullVar)) y =
        P mon * ∏ q ∈ mon, z2OfBool (if h : ∃ v : V, idx v = q then
          xor (y (Classical.choose h)) (s (Classical.choose h)) else e q) := by
      intro mon hmon
      have hP1 : P mon = 1 := z2_eq_one_of_ne_zero (Finset.mem_filter.mp hmon).2
      rw [hP1, one_mul, evalPoly_prodList, List.map_map]
      have hprod_eq :
          (mon.toList.map ((fun R => evalPoly R y) ∘ pullVar)).prod =
          ∏ q ∈ mon, evalPoly (pullVar q) y := by
        rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList mon, Multiset.map_coe, Multiset.prod_coe]
        rfl
      rw [hprod_eq]
      exact Finset.prod_congr rfl fun q _ => hpull_eval q y
    rw [Finset.sum_congr rfl hterm]
    simp only [evalPoly]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro mon _ hnot
    have hP0 : P mon = 0 := by
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ mon, hne⟩)
    rw [hP0, zero_mul]

private def fullBlocks {m : ℕ} (mon : Finset (Fin m × Fin 3)) : Finset (Fin m) :=
  (Finset.univ : Finset (Fin m)).filter (fun i => (i, 0) ∈ mon ∧ (i, 1) ∈ mon ∧ (i, 2) ∈ mon)

private def goodMons (m t : ℕ) : Finset (Finset (Fin m × Fin 3)) :=
  (Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => (fullBlocks mon).card < t)

private lemma card_nonfull_three :
    ((Finset.univ : Finset (Finset (Fin 3))).filter (fun A => A ≠ Finset.univ)).card = 7 := by
  decide

private lemma card_fiber_fullBlocks (m : ℕ) (F : Finset (Fin m)) :
    ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => fullBlocks mon = F)).card =
      7 ^ (m - F.card) := by
  classical
  let NonFull := {A : Finset (Fin 3) // A ≠ Finset.univ}
  let Rest := {i : Fin m // i ∉ F}
  let toFun : (Rest → NonFull) → Finset (Fin m × Fin 3) := fun f =>
    (Finset.univ : Finset (Fin m × Fin 3)).filter (fun p =>
      if h : p.1 ∈ F then True else p.2 ∈ (f ⟨p.1, h⟩).1)
  have hmem : ∀ f : Rest → NonFull,
      toFun f ∈ (Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => fullBlocks mon = F) := by
    intro f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext i
    simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and, toFun]
    by_cases hi : i ∈ F
    · simp [hi]
    · simp only [hi, ↓reduceDIte, iff_false]
      intro ⟨h0, h1, h2⟩
      apply (f ⟨i, hi⟩).2
      ext r
      fin_cases r <;> simp [h0, h1, h2]
  have hinj : Function.Injective toFun := by
    intro f₁ f₂ hEq
    funext ⟨i, hi⟩
    apply Subtype.ext
    ext r
    have hm := congr_arg (fun S => (i, r) ∈ S) hEq
    simpa [toFun, hi] using hm
  have hsurj : ∀ mon ∈ (Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => fullBlocks mon = F),
      ∃ f : Rest → NonFull, toFun f = mon := by
    intro mon hmon
    have hF : fullBlocks mon = F := (Finset.mem_filter.mp hmon).2
    let f : Rest → NonFull := fun ⟨i, hi⟩ =>
      ⟨(Finset.univ : Finset (Fin 3)).filter (fun r => (i, r) ∈ mon), by
        intro hall
        have hiF : i ∈ fullBlocks mon := by
          simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨?_, ?_, ?_⟩
          · have h0 : (0 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)).filter (fun r => (i, r) ∈ mon) := by
              rw [hall]; exact Finset.mem_univ _
            exact (Finset.mem_filter.mp h0).2
          · have h1 : (1 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)).filter (fun r => (i, r) ∈ mon) := by
              rw [hall]; exact Finset.mem_univ _
            exact (Finset.mem_filter.mp h1).2
          · have h2 : (2 : Fin 3) ∈ (Finset.univ : Finset (Fin 3)).filter (fun r => (i, r) ∈ mon) := by
              rw [hall]; exact Finset.mem_univ _
            exact (Finset.mem_filter.mp h2).2
        rw [hF] at hiF
        exact hi hiF⟩
    refine ⟨f, ?_⟩
    ext ⟨i, r⟩
    simp only [toFun, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : i ∈ F
    · simp only [hi, ↓reduceDIte, true_iff]
      rw [← hF] at hi
      have h3 := (Finset.mem_filter.mp hi).2
      fin_cases r
      · exact h3.1
      · exact h3.2.1
      · exact h3.2.2
    · simp [hi, f]
  have hcard_eq :
      ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => fullBlocks mon = F)).card =
      Fintype.card (Rest → NonFull) := by
    symm
    refine Finset.card_bij (fun f _ => toFun f) (fun f _ => hmem f)
      (fun f₁ _ f₂ _ h => hinj h) (fun mon hmon => by
        rcases hsurj mon hmon with ⟨f, hf⟩
        exact ⟨f, Finset.mem_univ f, hf⟩)
  rw [hcard_eq, Fintype.card_fun]
  have hNF : Fintype.card NonFull = 7 := by
    have h1 : Fintype.card NonFull =
        ((Finset.univ : Finset (Finset (Fin 3))).filter (fun A => A ≠ Finset.univ)).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
          invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, card_nonfull_three]
  have hRest : Fintype.card Rest = m - F.card := by
    have h1 : Fintype.card Rest = ((Finset.univ : Finset (Fin m)) \ F).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun x => ⟨x.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, x.2⟩⟩
          invFun := fun x => ⟨x.1, (Finset.mem_sdiff.mp x.2).2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin]
  rw [hNF, hRest]

private lemma card_goodMons (m t : ℕ) :
    (goodMons m t).card =
      (Finset.range (m + 1)).sum (fun filled =>
        if filled < t then Nat.choose m filled * 7 ^ (m - filled) else 0) := by
  classical
  have h1 :
      (goodMons m t).card =
      ∑ F : Finset (Fin m),
        if F.card < t then
          ((Finset.univ : Finset (Finset (Fin m × Fin 3))).filter (fun mon => fullBlocks mon = F)).card
        else 0 := by
    have hmaps : ∀ mon ∈ goodMons m t, fullBlocks mon ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun F => F.card < t) := by
      intro mon hmon
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hmon).2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    split_ifs with hlt
    · congr 1
      ext mon
      simp only [goodMons, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨_, hEq⟩; exact hEq
      · intro hEq; exact ⟨hEq.symm ▸ hlt, hEq⟩
    · rfl
  rw [h1]
  simp_rw [card_fiber_fullBlocks]
  have hmaps2 : ∀ F ∈ (Finset.univ : Finset (Finset (Fin m))), F.card ∈ Finset.range (m + 1) := by
    intro F _
    rw [Finset.mem_range]
    have : F.card ≤ m := by
      calc F.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ F
        _ = m := Fintype.card_fin m
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps2]
  refine Finset.sum_congr rfl fun filled hfilled => ?_
  have hcongr :
      ∑ F ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun F => F.card = filled),
        (if F.card < t then 7 ^ (m - F.card) else 0) =
      ∑ _F ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun F => F.card = filled),
        (if filled < t then 7 ^ (m - filled) else 0) :=
    Finset.sum_congr rfl fun F hF => by rw [(Finset.mem_filter.mp hF).2]
  rw [hcongr, Finset.sum_const, smul_eq_mul]
  have hpc :
      ((Finset.univ : Finset (Finset (Fin m))).filter (fun F => F.card = filled)).card =
      Nat.choose m filled := by
    have hEq :
        (Finset.univ : Finset (Finset (Fin m))).filter (fun F => F.card = filled) =
        Finset.powersetCard filled (Finset.univ : Finset (Fin m)) := by
      ext F
      simp [Finset.mem_powersetCard]
    rw [hEq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hpc]
  split_ifs <;> simp

private lemma sum_binomial_seven (m : ℕ) :
    (Finset.range (m + 1)).sum (fun filled => Nat.choose m filled * 7 ^ (m - filled)) = 8 ^ m := by
  have h := add_pow (1 : ℕ) 7 m
  rw [show (1 : ℕ) + 7 = 8 from rfl] at h
  rw [h]
  refine Finset.sum_congr rfl fun filled _ => by simp [mul_comm]

private lemma slice_hit_card_le {m b d L : ℕ} (hL : 1 ≤ L)
    (Ppath : Fin (2 ^ d) → Poly (Fin m × Fin 3))
    (hPdeg : ∀ path, degLe (Ppath path) (b * d))
    (runFn : (Fin m × Fin 3 → Bool) → Fin (2 ^ d))
    (hPeval : ∀ path y, evalPoly (Ppath path) y = if runFn y = path then 1 else 0)
    (Qleaf : Fin (2 ^ d) → Fin L → Fin m → Poly (Fin m × Fin 3))
    (hQdeg : ∀ path a i, degLe (Qleaf path a i) 2)
    (H : Finset (Fin m × Fin 3 → Bool))
    (hH : ∀ y ∈ H, ∃ a : Fin L, ∀ i : Fin m,
      evalPoly (Qleaf (runFn y) a i) y = z2OfBool (y (i, 0) && y (i, 1) && y (i, 2))) :
    H.card ≤
      (Finset.range (m + 1)).sum (fun filled =>
        if filled < L * (b * d + 1) then Nat.choose m filled * 7 ^ (m - filled) else 0) := by
  classical
  let V := Fin m × Fin 3
  let t : ℕ := b * d + 1
  have ht : 1 ≤ t := by omega
  let W := goodMons m (L * t)
  have hred : ∀ D : ℕ, ∀ mon : Finset V, mon.card ≤ D →
      ∃ R : Poly V, (∀ m', R m' ≠ 0 → m' ∈ W) ∧
        ∀ y ∈ H, evalPoly R y = ∏ v ∈ mon, z2OfBool (y v) := by
    intro D
    induction D with
    | zero =>
      intro mon hcard
      have hempty : mon = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
      subst hempty
      refine ⟨polyOne V, ?_, fun y _ => by simp [evalPoly_one]⟩
      intro m' hm'
      simp only [polyOne] at hm'
      split_ifs at hm' with hm0
      · subst hm0
        simp only [W, goodMons, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfb : fullBlocks (∅ : Finset V) = ∅ := by
          ext i; simp [fullBlocks]
        rw [hfb, Finset.card_empty]
        have : 1 ≤ L * t := Nat.mul_pos hL ht
        omega
      · exact absurd rfl hm'
    | succ D ih =>
      intro mon hcard
      by_cases hgood : mon ∈ W
      · refine ⟨polyMon mon, ?_, fun y _ => evalPoly_mon mon y⟩
        intro m' hm'
        simp only [polyMon] at hm'
        split_ifs at hm' with hEq
        · subst hEq; exact hgood
        · exact absurd rfl hm'
      · have hge : L * t ≤ (fullBlocks mon).card := by
          simp only [W, goodMons, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hgood
          exact hgood
        let e : Fin (fullBlocks mon).card ↪o Fin m := (fullBlocks mon).orderEmbOfFin rfl
        have he_mem : ∀ idx : Fin (fullBlocks mon).card, e idx ∈ fullBlocks mon :=
          fun idx => (fullBlocks mon).orderEmbOfFin_mem rfl idx
        let S : Fin L → Finset (Fin m) := fun a =>
          (Finset.univ : Finset (Fin t)).image (fun r =>
            e ⟨a.val * t + r.val, by
              have ha1 : a.val + 1 ≤ L := a.isLt
              have hmul : (a.val + 1) * t ≤ L * t := Nat.mul_le_mul_right t ha1
              rw [add_mul, one_mul] at hmul
              omega⟩)
        have hS_card : ∀ a : Fin L, (S a).card = t := by
          intro a
          rw [Finset.card_image_of_injective]
          · simp
          · intro r₁ r₂ hEq
            have h1 := e.injective hEq
            simp only [Fin.mk.injEq] at h1
            exact Fin.ext (by omega)
        have hS_sub : ∀ a : Fin L, S a ⊆ fullBlocks mon := by
          intro a i hi
          rcases Finset.mem_image.mp hi with ⟨r, _, rfl⟩
          exact he_mem _
        have hS_disj : ∀ a₁ a₂ : Fin L, a₁ ≠ a₂ → Disjoint (S a₁) (S a₂) := by
          intro a₁ a₂ hne
          rw [Finset.disjoint_left]
          intro i h1 h2
          rcases Finset.mem_image.mp h1 with ⟨r₁, _, rfl⟩
          rcases Finset.mem_image.mp h2 with ⟨r₂, _, hEq⟩
          have hidx := e.injective hEq
          simp only [Fin.mk.injEq] at hidx
          have ha_eq : a₁.val = a₂.val := by
            have hlt1 : r₁.val < t := r₁.isLt
            have hlt2 : r₂.val < t := r₂.isLt
            have hd1 : (a₁.val * t + r₁.val) / t = a₁.val := by
              rw [mul_comm, Nat.mul_add_div ht, Nat.div_eq_of_lt hlt1, add_zero]
            have hd2 : (a₂.val * t + r₂.val) / t = a₂.val := by
              rw [mul_comm, Nat.mul_add_div ht, Nat.div_eq_of_lt hlt2, add_zero]
            rw [← hd1, ← hidx, hd2]
          exact hne (Fin.ext ha_eq)
        let blockMon : Fin m → Finset V := fun i => {(i, 0), (i, 1), (i, 2)}
        have hbm_card : ∀ i : Fin m, (blockMon i).card = 3 := by
          intro i
          simp only [blockMon]
          rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
          · intro h
            simp only [Finset.mem_singleton] at h
            have h2 : (1 : Fin 3) = 2 := congr_arg Prod.snd h
            exact absurd h2 (by decide)
          · intro h
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h
            · have h2 : (0 : Fin 3) = 1 := congr_arg Prod.snd h
              exact absurd h2 (by decide)
            · have h2 : (0 : Fin 3) = 2 := congr_arg Prod.snd h
              exact absurd h2 (by decide)
        let monA : Fin L → Finset V := fun a => (S a).biUnion blockMon
        have hmonA_card : ∀ a : Fin L, (monA a).card = 3 * t := by
          intro a
          rw [Finset.card_biUnion]
          · simp [hbm_card, hS_card a, mul_comm]
          · intro i₁ _ i₂ _ hne
            change Disjoint (blockMon i₁) (blockMon i₂)
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            simp only [blockMon, Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
            rcases hp1 with rfl | rfl | rfl <;> rcases hp2 with h | h | h <;>
              exact hne (congr_arg Prod.fst h)
        let monAll : Finset V := Finset.univ.biUnion monA
        have hmonAll_card : monAll.card = 3 * L * t := by
          rw [Finset.card_biUnion]
          · simp [hmonA_card]; ring
          · intro a₁ _ a₂ _ hne
            change Disjoint (monA a₁) (monA a₂)
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            rcases Finset.mem_biUnion.mp hp1 with ⟨i₁, hi₁, hpi₁⟩
            rcases Finset.mem_biUnion.mp hp2 with ⟨i₂, hi₂, hpi₂⟩
            have hi_eq : i₁ = i₂ := by
              simp only [blockMon, Finset.mem_insert, Finset.mem_singleton] at hpi₁ hpi₂
              rcases hpi₁ with rfl | rfl | rfl <;> rcases hpi₂ with h | h | h <;>
                exact congr_arg Prod.fst h
            subst hi_eq
            exact Finset.disjoint_left.mp (hS_disj a₁ a₂ hne) hi₁ hi₂
        have hmonAll_sub : monAll ⊆ mon := by
          intro p hp
          rcases Finset.mem_biUnion.mp hp with ⟨a, _, hpa⟩
          rcases Finset.mem_biUnion.mp hpa with ⟨i, hi, hpi⟩
          have hfb := (Finset.mem_filter.mp (hS_sub a hi)).2
          simp only [blockMon, Finset.mem_insert, Finset.mem_singleton] at hpi
          rcases hpi with rfl | rfl | rfl
          · exact hfb.1
          · exact hfb.2.1
          · exact hfb.2.2
        let Ua : Fin L → Poly V := fun a => polyMon (monA a)
        let Qa : Fin L → Poly V := fun a =>
          polySumList (List.ofFn (fun path : Fin (2 ^ d) =>
            polyMul (Ppath path) (polyProdList ((S a).toList.map (Qleaf path a)))))
        have hUa_deg : ∀ a : Fin L, degLe (Ua a) (3 * t) := by
          intro a
          rw [← hmonA_card a]
          exact degLe_mon (monA a)
        have hQa_deg : ∀ a : Fin L, degLe (Qa a) (3 * t - 1) := by
          intro a
          refine degLe_sumList _ ?_
          intro R hR
          rcases List.mem_ofFn.mp hR with ⟨path, rfl⟩
          have h1 := degLe_prodList (d := 2) ((S a).toList.map (Qleaf path a)) (by
            intro T hT
            rcases List.mem_map.mp hT with ⟨i, _, rfl⟩
            exact hQdeg path a i)
          have hlen : ((S a).toList.map (Qleaf path a)).length * 2 = 2 * t := by
            simp [Finset.length_toList, hS_card a, mul_comm]
          rw [hlen] at h1
          have h2 := degLe_mul (hPdeg path) h1
          exact degLe_mono h2 (by omega)
        have hUa_eval : ∀ a : Fin L, ∀ y : V → Bool,
            evalPoly (Ua a) y = ∏ i ∈ S a, z2OfBool (y (i, 0) && y (i, 1) && y (i, 2)) := by
          intro a y
          rw [evalPoly_mon, Finset.prod_biUnion]
          · refine Finset.prod_congr rfl fun i _ => ?_
            simp only [blockMon]
            rw [Finset.prod_insert, Finset.prod_insert, Finset.prod_singleton]
            · simp [z2OfBool_and, mul_assoc]
            · intro h
              simp only [Finset.mem_singleton] at h
              have h2 : (1 : Fin 3) = 2 := congr_arg Prod.snd h
              exact absurd h2 (by decide)
            · intro h
              simp only [Finset.mem_insert, Finset.mem_singleton] at h
              rcases h with h | h
              · have h2 : (0 : Fin 3) = 1 := congr_arg Prod.snd h
                exact absurd h2 (by decide)
              · have h2 : (0 : Fin 3) = 2 := congr_arg Prod.snd h
                exact absurd h2 (by decide)
          · intro i₁ _ i₂ _ hne
            change Disjoint (blockMon i₁) (blockMon i₂)
            rw [Finset.disjoint_left]
            intro p hp1 hp2
            simp only [blockMon, Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
            rcases hp1 with rfl | rfl | rfl <;> rcases hp2 with h | h | h <;>
              exact hne (congr_arg Prod.fst h)
        have hQa_eval : ∀ a : Fin L, ∀ y : V → Bool,
            evalPoly (Qa a) y = ∏ i ∈ S a, evalPoly (Qleaf (runFn y) a i) y := by
          intro a y
          simp only [Qa, evalPoly_sumList, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
            evalPoly_mul, hPeval]
          have hite : ∀ path : Fin (2 ^ d),
              (if runFn y = path then (1 : ZMod 2) else 0) *
                evalPoly (polyProdList ((S a).toList.map (Qleaf path a))) y =
              if path = runFn y then
                evalPoly (polyProdList ((S a).toList.map (Qleaf path a))) y
              else 0 := by
            intro path
            by_cases h : path = runFn y
            · subst h; simp
            · have h' : runFn y ≠ path := Ne.symm h
              simp [h, h']
          simp_rw [hite]
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          rw [evalPoly_prodList, List.map_map]
          rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList (S a), Multiset.map_coe, Multiset.prod_coe]
          rfl
        let pairs : List (Poly V × Poly V) := List.ofFn (fun a : Fin L => (Ua a, Qa a))
        rcases prod_add_lowdeg (c := 3 * t) (by omega) pairs (by
          intro pq hpq
          rcases List.mem_ofFn.mp hpq with ⟨a, rfl⟩
          exact ⟨hUa_deg a, hQa_deg a⟩) with ⟨E, hEdeg, hEeval⟩
        have hElen : pairs.length * (3 * t) - 1 = 3 * L * t - 1 := by
          simp only [pairs, List.length_ofFn]
          have : L * (3 * t) = 3 * L * t := by ring
          rw [this]
        rw [hElen] at hEdeg
        have hprod_U : ∀ y : V → Bool,
            evalPoly (polyProdList (pairs.map Prod.fst)) y = ∏ v ∈ monAll, z2OfBool (y v) := by
          intro y
          rw [evalPoly_prodList, List.map_map]
          simp only [pairs, List.map_ofFn, List.prod_ofFn, Function.comp_apply, Ua, evalPoly_mon]
          rw [← Finset.prod_biUnion]
          intro a₁ _ a₂ _ hne
          change Disjoint (monA a₁) (monA a₂)
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          rcases Finset.mem_biUnion.mp hp1 with ⟨i₁, hi₁, hpi₁⟩
          rcases Finset.mem_biUnion.mp hp2 with ⟨i₂, hi₂, hpi₂⟩
          have hi_eq : i₁ = i₂ := by
            simp only [blockMon, Finset.mem_insert, Finset.mem_singleton] at hpi₁ hpi₂
            rcases hpi₁ with rfl | rfl | rfl <;> rcases hpi₂ with h | h | h <;>
              exact congr_arg Prod.fst h
          subst hi_eq
          exact Finset.disjoint_left.mp (hS_disj a₁ a₂ hne) hi₁ hi₂
        have hprod_zero : ∀ y ∈ H,
            evalPoly (polyProdList (pairs.map (fun pq => polyAdd pq.1 pq.2))) y = 0 := by
          intro y hy
          rcases hH y hy with ⟨a0, ha0⟩
          rw [evalPoly_prodList, List.map_map]
          simp only [pairs, List.map_ofFn, List.prod_ofFn, Function.comp_apply, evalPoly_add]
          refine Finset.prod_eq_zero (Finset.mem_univ a0) ?_
          rw [hUa_eval a0 y, hQa_eval a0 y]
          have heq : ∏ i ∈ S a0, evalPoly (Qleaf (runFn y) a0 i) y =
              ∏ i ∈ S a0, z2OfBool (y (i, 0) && y (i, 1) && y (i, 2)) :=
            Finset.prod_congr rfl fun i _ => ha0 i
          rw [heq]
          exact z2_add_self _
        have hE_eq_all : ∀ y ∈ H, evalPoly E y = ∏ v ∈ monAll, z2OfBool (y v) := by
          intro y hy
          have h0 := hprod_zero y hy
          rw [hEeval y, hprod_U y] at h0
          have hadd := congr_arg (fun z : ZMod 2 => z + evalPoly E y) h0
          simp only [zero_add, add_assoc, z2_add_self, add_zero] at hadd
          exact hadd.symm
        let monRem : Finset V := mon \ monAll
        let E' : Poly V := polyMul E (polyMon monRem)
        have hmonRem_card : monRem.card = mon.card - 3 * L * t := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hmonAll_sub, hmonAll_card]
        have hmonAll_le : 3 * L * t ≤ mon.card := by
          rw [← hmonAll_card]
          exact Finset.card_le_card hmonAll_sub
        have h3Lt_pos : 1 ≤ 3 * L * t := by
          rw [mul_assoc]
          have : 1 ≤ L * t := Nat.mul_pos hL ht
          omega
        have hE'_deg : degLe E' D := by
          have h1 := degLe_mul hEdeg (degLe_mon monRem)
          rw [hmonRem_card] at h1
          have hsum := Nat.add_sub_cancel' hmonAll_le
          have hsub : 3 * L * t - 1 + (mon.card - 3 * L * t) ≤ D := by omega
          exact degLe_mono h1 hsub
        have hE'_eval : ∀ y ∈ H, evalPoly E' y = ∏ v ∈ mon, z2OfBool (y v) := by
          intro y hy
          rw [evalPoly_mul, hE_eq_all y hy, evalPoly_mon, prod_z2_union,
            Finset.union_sdiff_of_subset hmonAll_sub]
        let suppE' := (Finset.univ.filter (fun m' : Finset V => E' m' ≠ 0)).toList
        have hih_each : ∀ m' : Finset V, m' ∈ suppE' →
            ∃ R : Poly V, (∀ m'', R m'' ≠ 0 → m'' ∈ W) ∧
              ∀ y ∈ H, evalPoly R y = ∏ v ∈ m', z2OfBool (y v) := by
          intro m' hm'
          exact ih m' (hE'_deg m' (Finset.mem_filter.mp (Finset.mem_toList.mp hm')).2)
        let Rtot : Poly V := polySumList (suppE'.map (fun m' =>
          if h : m' ∈ suppE' then Classical.choose (hih_each m' h) else polyZero V))
        refine ⟨Rtot, ?_, ?_⟩
        · refine supp_sumList W _ ?_
          intro R hR
          rcases List.mem_map.mp hR with ⟨m', hm', rfl⟩
          simp only [hm', ↓reduceDIte]
          exact (Classical.choose_spec (hih_each m' hm')).1
        · intro y hy
          rw [← hE'_eval y hy]
          simp only [Rtot, evalPoly_sumList, List.map_map]
          have hsum_eq :
              (suppE'.map ((fun R => evalPoly R y) ∘ (fun m' =>
                if h : m' ∈ suppE' then Classical.choose (hih_each m' h) else polyZero V))).sum =
              ∑ m' ∈ Finset.univ.filter (fun m' : Finset V => E' m' ≠ 0),
                evalPoly (if h : m' ∈ suppE' then Classical.choose (hih_each m' h) else polyZero V) y := by
            rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList (Finset.univ.filter _),
              Multiset.map_coe, Multiset.sum_coe]
            rfl
          rw [hsum_eq]
          have hcongr :
              ∑ m' ∈ Finset.univ.filter (fun m' : Finset V => E' m' ≠ 0),
                evalPoly (if h : m' ∈ suppE' then Classical.choose (hih_each m' h) else polyZero V) y =
              ∑ m' ∈ Finset.univ.filter (fun m' : Finset V => E' m' ≠ 0),
                E' m' * ∏ v ∈ m', z2OfBool (y v) := by
            refine Finset.sum_congr rfl fun m' hm' => ?_
            have hm'l : m' ∈ suppE' := Finset.mem_toList.mpr hm'
            have hE1 : E' m' = 1 := z2_eq_one_of_ne_zero (Finset.mem_filter.mp hm').2
            simp only [hm'l, ↓reduceDIte, hE1, one_mul]
            exact (Classical.choose_spec (hih_each m' hm'l)).2 y hy
          rw [hcongr]
          simp only [evalPoly]
          refine Finset.sum_subset (Finset.subset_univ _) ?_
          intro m' _ hnot
          have h0 : E' m' = 0 := by
            by_contra hne
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ m', hne⟩)
          rw [h0, zero_mul]
  let Phi : (W → ZMod 2) → (H → ZMod 2) := fun c y =>
    ∑ mon : W, c mon * ∏ v ∈ mon.1, z2OfBool (y.1 v)
  have hPhi_surj : Function.Surjective Phi := by
    intro f
    have hpt : ∀ y0 : H, ∃ R : Poly V, (∀ m', R m' ≠ 0 → m' ∈ W) ∧
        ∀ y : H, evalPoly R y.1 = if y = y0 then 1 else 0 := by
      intro y0
      let ind : Poly V := polyProdList ((Finset.univ : Finset V).toList.map (fun v : V =>
        if y0.1 v then polyVar v else polyAdd (polyOne V) (polyVar v)))
      have hind_eval : ∀ y : V → Bool, evalPoly ind y = if y = y0.1 then 1 else 0 := by
        intro y
        simp only [ind, evalPoly_prodList, List.map_map]
        have hprod_eq :
            ((Finset.univ : Finset V).toList.map
              ((fun P => evalPoly P y) ∘ (fun v : V =>
                if y0.1 v then polyVar v else polyAdd (polyOne V) (polyVar v)))).prod =
            ∏ v : V, evalPoly (if y0.1 v then polyVar v else polyAdd (polyOne V) (polyVar v)) y := by
          rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList (Finset.univ : Finset V),
            Multiset.map_coe, Multiset.prod_coe]
          rfl
        rw [hprod_eq]
        have hlit : ∀ v : V,
            evalPoly (if y0.1 v then polyVar v else polyAdd (polyOne V) (polyVar v)) y =
            if y v = y0.1 v then (1 : ZMod 2) else 0 := by
          intro v
          cases h1 : y0.1 v <;> cases h2 : y v <;>
            simp only [evalPoly_var, evalPoly_add, evalPoly_one, z2OfBool, h2, ↓reduceIte,
              Bool.false_eq_true, Bool.true_eq_false] <;> decide
        simp_rw [hlit]
        by_cases hEq : y = y0.1
        · subst hEq
          simp only [↓reduceIte]
          exact Finset.prod_eq_one fun v _ => by simp
        · simp only [hEq, ↓reduceIte]
          have hex : ∃ v : V, y v ≠ y0.1 v := by
            by_contra hall
            push Not at hall
            exact hEq (funext hall)
          rcases hex with ⟨v, hv⟩
          exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
      let suppInd := (Finset.univ.filter (fun m' : Finset V => ind m' ≠ 0)).toList
      have hred_each : ∀ m' : Finset V,
          ∃ R : Poly V, (∀ m'', R m'' ≠ 0 → m'' ∈ W) ∧
            ∀ y ∈ H, evalPoly R y = ∏ v ∈ m', z2OfBool (y v) :=
        fun m' => hred m'.card m' (le_refl _)
      let Rpt : Poly V := polySumList (suppInd.map (fun m' => Classical.choose (hred_each m')))
      refine ⟨Rpt, ?_, ?_⟩
      · refine supp_sumList W _ ?_
        intro R hR
        rcases List.mem_map.mp hR with ⟨m', _, rfl⟩
        exact (Classical.choose_spec (hred_each m')).1
      · intro y
        have h1 : evalPoly Rpt y.1 = evalPoly ind y.1 := by
          simp only [Rpt, evalPoly_sumList, List.map_map]
          have hsum_eq :
              (suppInd.map ((fun R => evalPoly R y.1) ∘ (fun m' => Classical.choose (hred_each m')))).sum =
              ∑ m' ∈ Finset.univ.filter (fun m' : Finset V => ind m' ≠ 0),
                evalPoly (Classical.choose (hred_each m')) y.1 := by
            rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList (Finset.univ.filter _),
              Multiset.map_coe, Multiset.sum_coe]
            rfl
          rw [hsum_eq]
          have hcongr :
              ∑ m' ∈ Finset.univ.filter (fun m' : Finset V => ind m' ≠ 0),
                evalPoly (Classical.choose (hred_each m')) y.1 =
              ∑ m' ∈ Finset.univ.filter (fun m' : Finset V => ind m' ≠ 0),
                ind m' * ∏ v ∈ m', z2OfBool (y.1 v) := by
            refine Finset.sum_congr rfl fun m' hm' => ?_
            have hI1 : ind m' = 1 := z2_eq_one_of_ne_zero (Finset.mem_filter.mp hm').2
            rw [hI1, one_mul]
            exact (Classical.choose_spec (hred_each m')).2 y.1 y.2
          rw [hcongr]
          simp only [evalPoly]
          refine Finset.sum_subset (Finset.subset_univ _) ?_
          intro m' _ hnot
          have h0 : ind m' = 0 := by
            by_contra hne
            exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ m', hne⟩)
          rw [h0, zero_mul]
        rw [h1, hind_eval y.1]
        by_cases hEq : y = y0
        · subst hEq; simp
        · have hne : y.1 ≠ y0.1 := fun h => hEq (Subtype.ext h)
          simp [hEq, hne]
    let c : W → ZMod 2 := fun mon =>
      ∑ y0 : H, f y0 * (Classical.choose (hpt y0)) mon.1
    refine ⟨c, ?_⟩
    funext y
    simp only [Phi, c]
    calc
      ∑ mon : W, (∑ y0 : H, f y0 * (Classical.choose (hpt y0)) mon.1) * ∏ v ∈ mon.1, z2OfBool (y.1 v)
          = ∑ mon : W, ∑ y0 : H, f y0 * ((Classical.choose (hpt y0)) mon.1 * ∏ v ∈ mon.1, z2OfBool (y.1 v)) := by
            refine Finset.sum_congr rfl fun mon _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun y0 _ => by ring
      _ = ∑ y0 : H, ∑ mon : W, f y0 * ((Classical.choose (hpt y0)) mon.1 * ∏ v ∈ mon.1, z2OfBool (y.1 v)) :=
            Finset.sum_comm
      _ = ∑ y0 : H, f y0 * evalPoly (Classical.choose (hpt y0)) y.1 := by
            refine Finset.sum_congr rfl fun y0 _ => ?_
            rw [← Finset.mul_sum]
            congr 1
            let R : Poly V := Classical.choose (hpt y0)
            change ∑ mon : W, R mon.1 * ∏ v ∈ mon.1, z2OfBool (y.1 v) = evalPoly R y.1
            simp only [evalPoly]
            rw [Finset.sum_coe_sort W (fun mon => R mon * ∏ v ∈ mon, z2OfBool (y.1 v))]
            refine Finset.sum_subset (Finset.subset_univ _) ?_
            intro mon _ hnot
            have h0 : R mon = 0 := by
              by_contra hne
              exact hnot ((Classical.choose_spec (hpt y0)).1 mon hne)
            rw [h0, zero_mul]
      _ = ∑ y0 : H, f y0 * (if y = y0 then 1 else 0) :=
            Finset.sum_congr rfl fun y0 _ => by rw [(Classical.choose_spec (hpt y0)).2 y]
      _ = f y := by
            have h1 : ∀ y0 : H, f y0 * (if y = y0 then (1 : ZMod 2) else 0) =
                if y0 = y then f y0 else 0 := by
              intro y0
              by_cases h : y0 = y
              · subst h; simp
              · have h' : y ≠ y0 := Ne.symm h
                simp [h, h']
            simp_rw [h1]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hcard_le : Fintype.card (H → ZMod 2) ≤ Fintype.card (W → ZMod 2) :=
    Fintype.card_le_of_surjective Phi hPhi_surj
  simp only [Fintype.card_fun, Fintype.card_coe, ZMod.card] at hcard_le
  have hHW : H.card ≤ W.card := (Nat.pow_le_pow_iff_right (a := 2) (by omega)).mp hcard_le
  rwa [card_goodMons] at hHW

private lemma slice_odd_preimage {m d L : ℕ} (hL : 1 ≤ L)
    (Qleaf : Fin (2 ^ d) → Fin L → Fin m → Poly (Fin m × Fin 3))
    (hQdeg : ∀ path a i, degLe (Qleaf path a i) 2)
    (hcover : ∀ y : Fin m × Fin 3 → Bool, ∃ (path : Fin (2 ^ d)) (a : Fin L), ∀ i : Fin m,
      evalPoly (Qleaf path a i) y = z2OfBool (y (i, 0) && y (i, 1) && y (i, 2))) :
    m + 1 ≤ L * 2 ^ d := by
  classical
  by_contra hlt
  let N : ℕ := L * 2 ^ d
  have hNm : N ≤ m := by omega
  have hNpos : 1 ≤ N := Nat.mul_pos hL (Nat.two_pow_pos d)
  let eN : Fin N ≃ Fin (2 ^ d) × Fin L :=
    Fintype.equivOfCardEq (by simp [N, mul_comm])
  let emb : (Fin N × Fin 3 → Bool) → (Fin m × Fin 3 → Bool) := fun y' p =>
    if h : p.1.val < N then y' (⟨p.1.val, h⟩, p.2) else false
  have hrestrict : ∀ (P : Poly (Fin m × Fin 3)), degLe P 2 →
      ∃ Q : Poly (Fin N × Fin 3), degLe Q 2 ∧ ∀ y', evalPoly Q y' = evalPoly P (emb y') := by
    intro P hP
    let pullV : Fin m × Fin 3 → Poly (Fin N × Fin 3) := fun p =>
      if h : p.1.val < N then polyVar (⟨p.1.val, h⟩, p.2) else polyZero _
    have hpd : ∀ p, degLe (pullV p) 1 := by
      intro p
      simp only [pullV]
      split_ifs
      · exact degLe_var _
      · exact degLe_zero 1
    have hpe : ∀ p y', evalPoly (pullV p) y' = z2OfBool (emb y' p) := by
      intro p y'
      simp only [pullV, emb]
      split_ifs
      · exact evalPoly_var _ y'
      · exact evalPoly_zero y'
    let suppP := (Finset.univ.filter (fun mon : Finset (Fin m × Fin 3) => P mon ≠ 0)).toList
    let Q : Poly (Fin N × Fin 3) := polySumList (suppP.map (fun mon => polyProdList (mon.toList.map pullV)))
    refine ⟨Q, ?_, ?_⟩
    · refine degLe_sumList _ ?_
      intro R hR
      rcases List.mem_map.mp hR with ⟨mon, hmon, rfl⟩
      have h1 := degLe_prodList (d := 1) (mon.toList.map pullV) (by
        intro T hT
        rcases List.mem_map.mp hT with ⟨p, _, rfl⟩
        exact hpd p)
      have hlen : (mon.toList.map pullV).length * 1 ≤ 2 := by
        simp [Finset.length_toList]
        exact hP mon (Finset.mem_filter.mp (Finset.mem_toList.mp hmon)).2
      exact degLe_mono h1 hlen
    · intro y'
      simp only [Q, evalPoly_sumList, List.map_map]
      have hsum_eq :
          (suppP.map ((fun R => evalPoly R y') ∘ (fun mon => polyProdList (mon.toList.map pullV)))).sum =
          ∑ mon ∈ Finset.univ.filter (fun mon : Finset (Fin m × Fin 3) => P mon ≠ 0),
            evalPoly (polyProdList (mon.toList.map pullV)) y' := by
        rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList (Finset.univ.filter _),
          Multiset.map_coe, Multiset.sum_coe]
        rfl
      rw [hsum_eq]
      have hcongr :
          ∑ mon ∈ Finset.univ.filter (fun mon : Finset (Fin m × Fin 3) => P mon ≠ 0),
            evalPoly (polyProdList (mon.toList.map pullV)) y' =
          ∑ mon ∈ Finset.univ.filter (fun mon : Finset (Fin m × Fin 3) => P mon ≠ 0),
            P mon * ∏ p ∈ mon, z2OfBool (emb y' p) := by
        refine Finset.sum_congr rfl fun mon hmon => ?_
        have hP1 : P mon = 1 := z2_eq_one_of_ne_zero (Finset.mem_filter.mp hmon).2
        rw [hP1, one_mul, evalPoly_prodList, List.map_map]
        have hprod_eq :
            (mon.toList.map ((fun R => evalPoly R y') ∘ pullV)).prod =
            ∏ p ∈ mon, evalPoly (pullV p) y' := by
          rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList mon, Multiset.map_coe, Multiset.prod_coe]
          rfl
        rw [hprod_eq]
        exact Finset.prod_congr rfl fun p _ => hpe p y'
      rw [hcongr]
      simp only [evalPoly]
      refine Finset.sum_subset (Finset.subset_univ _) ?_
      intro mon _ hnot
      have h0 : P mon = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ mon, hne⟩)
      rw [h0, zero_mul]
  let U : Fin N → Poly (Fin N × Fin 3) := fun c => polyMon {(c, 0), (c, 1), (c, 2)}
  let Q : Fin N → Poly (Fin N × Fin 3) := fun c =>
    Classical.choose (hrestrict (Qleaf (eN c).1 (eN c).2 ⟨c.val, by omega⟩)
      (hQdeg (eN c).1 (eN c).2 ⟨c.val, by omega⟩))
  have hQ_deg : ∀ c : Fin N, degLe (Q c) 2 := fun c =>
    (Classical.choose_spec (hrestrict (Qleaf (eN c).1 (eN c).2 ⟨c.val, by omega⟩)
      (hQdeg (eN c).1 (eN c).2 ⟨c.val, by omega⟩))).1
  have hQ_eval : ∀ c : Fin N, ∀ y',
      evalPoly (Q c) y' = evalPoly (Qleaf (eN c).1 (eN c).2 ⟨c.val, by omega⟩) (emb y') := fun c =>
    (Classical.choose_spec (hrestrict (Qleaf (eN c).1 (eN c).2 ⟨c.val, by omega⟩)
      (hQdeg (eN c).1 (eN c).2 ⟨c.val, by omega⟩))).2
  let pairs : List (Poly (Fin N × Fin 3) × Poly (Fin N × Fin 3)) :=
    List.ofFn (fun c : Fin N => (U c, Q c))
  rcases prod_add_lowdeg (c := 3) (by omega) pairs (by
    intro pq hpq
    rcases List.mem_ofFn.mp hpq with ⟨c, rfl⟩
    refine ⟨?_, hQ_deg c⟩
    have hcard3 : ({(c, (0 : Fin 3)), (c, 1), (c, 2)} : Finset (Fin N × Fin 3)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · intro h; simp only [Finset.mem_singleton, Prod.mk.injEq] at h; exact absurd h.2 (by decide)
      · intro h; simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
        rcases h with h | h <;> exact absurd h.2 (by decide)
    exact degLe_mono (degLe_mon _) (le_of_eq hcard3)) with ⟨E, hEdeg, hEeval⟩
  have hElen : pairs.length * 3 - 1 = 3 * N - 1 := by
    simp only [pairs, List.length_ofFn, mul_comm]
  rw [hElen] at hEdeg
  have hsum_E : ∑ y' : Fin N × Fin 3 → Bool, evalPoly E y' = 0 := by
    simp only [evalPoly]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun mon _ => ?_
    rw [← Finset.mul_sum, cube_sum_mod2_mon]
    by_cases hu : mon = Finset.univ
    · subst hu
      have hE0 : E Finset.univ = 0 := by
        by_contra hne
        have hle := hEdeg Finset.univ hne
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hle
        omega
      simp [hE0]
    · simp [hu]
  have hsum_U : ∑ y' : Fin N × Fin 3 → Bool, evalPoly (polyProdList (pairs.map Prod.fst)) y' = 1 := by
    have hprod_eq : ∀ y' : Fin N × Fin 3 → Bool,
        evalPoly (polyProdList (pairs.map Prod.fst)) y' =
        ∏ p : Fin N × Fin 3, z2OfBool (y' p) := by
      intro y'
      rw [evalPoly_prodList, List.map_map]
      simp only [pairs, List.map_ofFn, List.prod_ofFn, Function.comp_apply, U, evalPoly_mon]
      rw [← Finset.prod_biUnion]
      · congr 1
        ext ⟨c, r⟩
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq, iff_true]
        refine ⟨c, ?_⟩
        fin_cases r <;> simp
      · intro c₁ _ c₂ _ hne
        change Disjoint ({(c₁, (0 : Fin 3)), (c₁, 1), (c₁, 2)} : Finset (Fin N × Fin 3))
          {(c₂, 0), (c₂, 1), (c₂, 2)}
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
        rcases hp1 with rfl | rfl | rfl <;> rcases hp2 with h | h | h <;>
          exact hne (congr_arg Prod.fst h)
    simp_rw [hprod_eq]
    rw [cube_sum_mod2_mon]
    simp
  have hsum_tot :
      ∑ y' : Fin N × Fin 3 → Bool,
        evalPoly (polyProdList (pairs.map (fun pq => polyAdd pq.1 pq.2))) y' = 1 := by
    simp_rw [hEeval, Finset.sum_add_distrib, hsum_U, hsum_E, add_zero]
  have hsum_zero :
      ∑ y' : Fin N × Fin 3 → Bool,
        evalPoly (polyProdList (pairs.map (fun pq => polyAdd pq.1 pq.2))) y' = 0 := by
    refine Finset.sum_eq_zero fun y' _ => ?_
    rcases hcover (emb y') with ⟨path, a, hcov⟩
    let c0 : Fin N := eN.symm (path, a)
    rw [evalPoly_prodList, List.map_map]
    simp only [pairs, List.map_ofFn, List.prod_ofFn, Function.comp_apply, evalPoly_add]
    refine Finset.prod_eq_zero (Finset.mem_univ c0) ?_
    rw [hQ_eval c0 y']
    have hec : eN c0 = (path, a) := eN.apply_symm_apply (path, a)
    rw [hec]
    have hc1 := hcov ⟨c0.val, by omega⟩
    rw [hc1]
    have hUeval : evalPoly (U c0) y' =
        z2OfBool (emb y' (⟨c0.val, by omega⟩, 0) &&
          emb y' (⟨c0.val, by omega⟩, 1) && emb y' (⟨c0.val, by omega⟩, 2)) := by
      simp only [U, evalPoly_mon, emb, c0.isLt, ↓reduceDIte]
      simp [z2OfBool_and, mul_assoc]
    rw [hUeval]
    exact z2_add_self _
  rw [hsum_tot] at hsum_zero
  exact absurd hsum_zero (by decide)

private lemma clog_bounds {a rem : ℕ} (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hrem : rem < 2 ^ a - 1) :
    rem < 2 ^ Nat.clog 2 (rem + 1) ∧ Nat.clog 2 (rem + 1) ≤ a := by
  interval_cases a <;> interval_cases rem <;> decide

private lemma choose_deg_le {a b r : ℕ} (ha1 : 1 ≤ a) (ha3 : a ≤ 3) (hb1 : 1 ≤ b) (hba : b ≤ a)
    (hr : r < b) :
    (r + 1) * 2 ^ (b - 1 - r) ≤ 2 ^ (a - 1) := by
  interval_cases a <;> interval_cases b <;> interval_cases r <;> decide

private lemma choose_count_deg_K {k m : ℕ} (idx : Fin m × Fin 3 → Fin k) (s : Fin m × Fin 3 → Bool)
    (G : Finset (Fin m)) (r : ℕ) (hr : r < 3) (pat : Fin (r + 1) → Bool) (T : ℕ) :
    let K := Fin (2 ^ k)
    let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
    let par := fun (n : ℕ) => n % 2 == 1
    let f : K → Bool := fun x =>
      decide ((G.filter (fun i =>
        ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t)).card.choose T % 2 = 1)
    ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ (r + 1) * T) ∧
      ∀ key, f key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card) := by
  classical
  intro K bitOf par f
  let litPoly : Fin m → Fin (r + 1) → Poly (Fin k) := fun i t =>
    let q := idx (i, ⟨t.val, by omega⟩)
    let target := xor (pat t) (s (i, ⟨t.val, by omega⟩))
    if target then polyVar q else polyAdd (polyOne (Fin k)) (polyVar q)
  have hlit_deg : ∀ i t, degLe (litPoly i t) 1 := by
    intro i t
    simp only [litPoly]
    split_ifs
    · exact degLe_var _
    · exact degLe_add (degLe_one 1) (degLe_var _)
  have hlit_eval : ∀ i t (w : Fin k → Bool), evalPoly (litPoly i t) w =
      if xor (w (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t then (1 : ZMod 2) else 0 := by
    intro i t w
    simp only [litPoly]
    cases pat t <;> cases s (i, ⟨t.val, by omega⟩) <;>
      cases hw : w (idx (i, ⟨t.val, by omega⟩)) <;>
      simp only [evalPoly_var, evalPoly_add, evalPoly_one, z2OfBool, hw,
        Bool.xor_false, Bool.xor_true, Bool.not_false, Bool.not_true,
        ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false] <;> decide
  let rowPoly : Fin m → Poly (Fin k) := fun i =>
    polyProdList (List.ofFn (fun t : Fin (r + 1) => litPoly i t))
  have hrow_deg : ∀ i, degLe (rowPoly i) (r + 1) := by
    intro i
    have h1 := degLe_prodList (d := 1) (List.ofFn (fun t : Fin (r + 1) => litPoly i t))
      (by intro P hP; rcases List.mem_ofFn.mp hP with ⟨t, rfl⟩; exact hlit_deg i t)
    have hlen : (List.ofFn (fun t : Fin (r + 1) => litPoly i t)).length * 1 = r + 1 := by
      simp [List.length_ofFn]
    rwa [hlen] at h1
  have hrow_eval : ∀ i (w : Fin k → Bool), evalPoly (rowPoly i) w =
      if ∀ t : Fin (r + 1), xor (w (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t
      then (1 : ZMod 2) else 0 := by
    intro i w
    rw [evalPoly_prodList, List.map_ofFn, List.prod_ofFn]
    simp_rw [Function.comp_apply, hlit_eval]
    split_ifs with hall
    · refine Finset.prod_eq_one fun t _ => ?_
      split_ifs with h
      · rfl
      · exact absurd (hall t) h
    · push Not at hall
      rcases hall with ⟨t, ht⟩
      refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
      split_ifs with h
      · exact absurd h ht
      · rfl
  let setsList : List (Finset (Fin m)) := (Finset.powersetCard T G).toList
  let setPoly : Finset (Fin m) → Poly (Fin k) := fun S => polyProdList (S.toList.map rowPoly)
  let totalPoly : Poly (Fin k) := polySumList (setsList.map setPoly)
  have htotal_deg : degLe totalPoly ((r + 1) * T) := by
    refine degLe_sumList _ ?_
    intro P hP
    rcases List.mem_map.mp hP with ⟨S, hS, rfl⟩
    have hScard : S.card = T := (Finset.mem_powersetCard.mp (Finset.mem_toList.mp hS)).2
    have h1 := degLe_prodList (d := r + 1) (S.toList.map rowPoly)
      (by intro Q hQ; rcases List.mem_map.mp hQ with ⟨i, _, rfl⟩; exact hrow_deg i)
    have hlen : (S.toList.map rowPoly).length * (r + 1) = (r + 1) * T := by
      simp [Finset.length_toList, hScard, mul_comm]
    rwa [hlen] at h1
  let fW : (Fin k → Bool) → Bool := fun w =>
    decide ((G.filter (fun i =>
      ∀ t : Fin (r + 1), xor (w (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t)).card.choose T % 2 = 1)
  have hfW : ∀ w : Fin k → Bool, z2OfBool (fW w) = evalPoly totalPoly w := by
    intro w
    let Good := G.filter (fun i =>
      ∀ t : Fin (r + 1), xor (w (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t)
    have heval_set_G : ∀ S ∈ Finset.powersetCard T G,
        evalPoly (setPoly S) w = if S ⊆ Good then (1 : ZMod 2) else 0 := by
      intro S hSG
      have hsubG : S ⊆ G := (Finset.mem_powersetCard.mp hSG).1
      simp only [setPoly]
      rw [evalPoly_prodList, List.map_map]
      have hprod_eq :
          (S.toList.map ((fun P => evalPoly P w) ∘ rowPoly)).prod =
          ∏ i ∈ S, evalPoly (rowPoly i) w := by
        rw [Finset.prod_eq_multiset_prod, ← Finset.coe_toList S, Multiset.map_coe, Multiset.prod_coe]
        rfl
      rw [hprod_eq]
      by_cases hsub : S ⊆ Good
      · simp only [hsub, ↓reduceIte]
        refine Finset.prod_eq_one fun i hi => ?_
        have hgi := (Finset.mem_filter.mp (hsub hi)).2
        rw [hrow_eval]
        split_ifs
        rfl
      · simp only [hsub, ↓reduceIte]
        have hex : ∃ i ∈ S, i ∉ Good := by
          by_contra hall
          push Not at hall
          exact hsub hall
        rcases hex with ⟨i, hiS, hiG⟩
        have hng : ¬(∀ t : Fin (r + 1), xor (w (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t) :=
          fun h => hiG (Finset.mem_filter.mpr ⟨hsubG hiS, h⟩)
        exact Finset.prod_eq_zero hiS (by rw [hrow_eval]; simp [hng])
    have heval_tot : evalPoly totalPoly w = ((Good.card.choose T : ℕ) : ZMod 2) := by
      simp only [totalPoly]
      rw [evalPoly_sumList, List.map_map]
      have hsum_eq :
          (setsList.map ((fun P => evalPoly P w) ∘ setPoly)).sum =
          ∑ S ∈ Finset.powersetCard T G, evalPoly (setPoly S) w := by
        rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList (Finset.powersetCard T G),
          Multiset.map_coe, Multiset.sum_coe]
        rfl
      rw [hsum_eq, Finset.sum_congr rfl heval_set_G, Finset.sum_boole]
      have hf_eq : (Finset.powersetCard T G).filter (fun S => S ⊆ Good) = Finset.powersetCard T Good := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        constructor
        · intro ⟨⟨_, hcard⟩, hsub⟩; exact ⟨hsub, hcard⟩
        · intro ⟨hsub, hcard⟩
          exact ⟨⟨fun i hi => (Finset.mem_filter.mp (hsub hi)).1, hcard⟩, hsub⟩
      rw [hf_eq, Finset.card_powersetCard]
    rw [heval_tot, z2_nat_eq_mod2]
    have hfeq : fW w = (Good.card.choose T % 2 == 1) := by
      change decide (Good.card.choose T % 2 = 1) = (Good.card.choose T % 2 == 1)
      cases h : Good.card.choose T % 2 == 1 <;> simp_all
    rw [hfeq]
  rcases deg_of_poly totalPoly htotal_deg hfW with ⟨terms, hdeg, heval⟩
  refine ⟨terms, hdeg, fun key => ?_⟩
  convert heval (bitOf key)

private lemma deg2_cancel_triple {k : ℕ} (q0 q1 q2 : Fin k) (s0 s1 s2 c0 l0 l1 l2 p0 p1 p2 : Bool) :
    let K := Fin (2 ^ k)
    let bitOf := fun (x : K) (i : Fin k) => x.val.testBit i.val
    let par := fun (n : ℕ) => n % 2 == 1
    let g : K → Bool := fun x =>
      let y0 := xor (bitOf x q0) s0
      let y1 := xor (bitOf x q1) s1
      let y2 := xor (bitOf x q2) s2
      let u0 := bitOf x q0
      let u1 := bitOf x q1
      let u2 := bitOf x q2
      xor (xor (y0 && y1 && y2) (xor y0 (!p0) && xor y1 (!p1) && xor y2 (!p2)))
        (xor (xor (xor c0 (l0 && u0)) (l1 && u1)) (l2 && u2))
    ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ 2) ∧
      ∀ key, g key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card) := by
  intro K bitOf par g
  let lin : Fin k → Bool → Poly (Fin k) := fun q b =>
    if b then polyAdd (polyOne (Fin k)) (polyVar q) else polyVar q
  have hlin_deg : ∀ q b, degLe (lin q b) 1 := by
    intro q b
    simp only [lin]
    split_ifs
    · exact degLe_add (degLe_one 1) (degLe_var q)
    · exact degLe_var q
  have hlin_eval : ∀ q b (w : Fin k → Bool), evalPoly (lin q b) w = z2OfBool (xor (w q) b) := by
    intro q b w
    simp only [lin]
    cases b <;> cases hw : w q <;>
      simp only [evalPoly_var, evalPoly_add, evalPoly_one, z2OfBool, hw, ↓reduceIte,
        Bool.false_eq_true, Bool.xor_false, Bool.xor_true] <;> decide
  let constP : Bool → Poly (Fin k) := fun b => if b then polyOne (Fin k) else polyZero (Fin k)
  have hconst_deg : ∀ b d, degLe (constP b) d := by
    intro b d
    cases b
    · exact degLe_zero d
    · exact degLe_one d
  have hconst_eval : ∀ b (w : Fin k → Bool), evalPoly (constP b) w = z2OfBool b := by
    intro b w
    cases b <;> simp [constP, evalPoly_one, evalPoly_zero, z2OfBool]
  let Y0 := lin q0 s0
  let Y1 := lin q1 s1
  let Y2 := lin q2 s2
  let k0 := !p0
  let k1 := !p1
  let k2 := !p2
  let P_cancel : Poly (Fin k) :=
    polySumList [
      polyMul (constP k0) (polyMul Y1 Y2),
      polyMul (constP k1) (polyMul Y0 Y2),
      polyMul (constP k2) (polyMul Y0 Y1),
      polyMul (constP (k0 && k1)) Y2,
      polyMul (constP (k0 && k2)) Y1,
      polyMul (constP (k1 && k2)) Y0,
      constP (k0 && k1 && k2)
    ]
  let P_aff : Poly (Fin k) :=
    polySumList [
      constP c0,
      polyMul (constP l0) (polyVar q0),
      polyMul (constP l1) (polyVar q1),
      polyMul (constP l2) (polyVar q2)
    ]
  let P := polyAdd P_cancel P_aff
  have hP_deg : degLe P 2 := by
    refine degLe_add ?_ ?_
    · refine degLe_sumList _ ?_
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (degLe_mul (hlin_deg _ _) (hlin_deg _ _))) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (degLe_mul (hlin_deg _ _) (hlin_deg _ _))) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (degLe_mul (hlin_deg _ _) (hlin_deg _ _))) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (hlin_deg _ _)) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (hlin_deg _ _)) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (hlin_deg _ _)) (by omega)
      · exact hconst_deg _ 2
    · refine degLe_sumList _ ?_
      intro R hR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      rcases hR with rfl | rfl | rfl | rfl
      · exact hconst_deg _ 2
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (degLe_var _)) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (degLe_var _)) (by omega)
      · exact degLe_mono (degLe_mul (hconst_deg _ 0) (degLe_var _)) (by omega)
  let gW : (Fin k → Bool) → Bool := fun w =>
    let y0 := xor (w q0) s0
    let y1 := xor (w q1) s1
    let y2 := xor (w q2) s2
    xor (xor (y0 && y1 && y2) (xor y0 (!p0) && xor y1 (!p1) && xor y2 (!p2)))
      (xor (xor (xor c0 (l0 && w q0)) (l1 && w q1)) (l2 && w q2))
  have hgW : ∀ w : Fin k → Bool, z2OfBool (gW w) = evalPoly P w := by
    intro w
    simp only [gW, P, P_cancel, P_aff, evalPoly_add, evalPoly_sumList, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, evalPoly_mul, evalPoly_var, hconst_eval, Y0, Y1, Y2,
      hlin_eval, z2OfBool_xor, z2OfBool_and, k0, k1, k2]
    have hcancel : ∀ a b c q0 q1 q2 : ZMod 2,
        a * b * c + (a + q0) * (b + q1) * (c + q2) =
        q0 * (b * c) + q1 * (a * c) + q2 * (a * b) +
        (q0 * q1) * c + (q0 * q2) * b + (q1 * q2) * a + q0 * q1 * q2 := by
      intro a b c q0 q1 q2
      have h : a * b * c + (a + q0) * (b + q1) * (c + q2) =
          (a * b * c + a * b * c) + (q0 * (b * c) + q1 * (a * c) + q2 * (a * b) +
          (q0 * q1) * c + (q0 * q2) * b + (q1 * q2) * a + q0 * q1 * q2) := by ring
      rw [h, z2_add_self, zero_add]
    rw [hcancel]
    ring
  rcases deg_of_poly P hP_deg hgW with ⟨terms, hdeg, heval⟩
  refine ⟨terms, hdeg, fun key => ?_⟩
  convert heval (bitOf key)

private lemma part2_upper {k m : ℕ} (_hk : 12 ≤ k)
    (idx : Fin m × Fin 3 → Fin k) (s0 s1 s2 c0 l0 l1 l2 : Fin m → Bool)
    (out : Fin (2 ^ k) → Fin m → Bool)
    (fiber : Finset (Fin (2 ^ k)))
    (hout : ∀ x ∈ fiber, ∀ i : Fin m,
      let u0 := x.val.testBit (idx (i, 0)).val
      let u1 := x.val.testBit (idx (i, 1)).val
      let u2 := x.val.testBit (idx (i, 2)).val
      out x i = xor ((xor u0 (s0 i)) && (xor u1 (s1 i)) && (xor u2 (s2 i)))
        (xor (xor (xor (c0 i) (l0 i && u0)) (l1 i && u1)) (l2 i && u2)))
    (a : ℕ) (ha1 : 1 ≤ a) (ha3 : a ≤ 3) :
    let K := Fin (2 ^ k)
    let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
    let par := fun (n : ℕ) => n % 2 == 1
    let deg := fun (u : ℕ) (f : K → Bool) =>
      ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ u) ∧
        ∀ key, f key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card)
    let run := fun (steps : ℕ) (ask : ℕ → ℕ → K → Bool) (x : K) =>
      (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
    let size := 2 ^ a - 1
    let steps := a * (m / size) + Nat.clog 2 (m % size + 1)
    ∃ (choose : ℕ → ℕ → K → Bool) (pred : ℕ → Fin m → K → Bool),
      (∀ (level : Fin steps) (path : ℕ), deg (2 ^ (a - 1)) (choose level.val path)) ∧
      (∀ path i, deg 2 (pred path i)) ∧
      ∀ x ∈ fiber, ∀ i, pred (run steps choose x) i x = out x i := by
  classical
  intro K bitOf par deg run size steps
  let q := m / size
  let rem := m % size
  let bLast := Nat.clog 2 (rem + 1)
  have hsize_pos : 0 < size := by
    simp only [size]
    interval_cases a <;> decide
  have hrem_lt : rem < size := Nat.mod_lt m hsize_pos
  have hclog := clog_bounds ha1 ha3 hrem_lt
  have hbLast_le : bLast ≤ a := hclog.2
  have hrem_pow : rem < 2 ^ bLast := hclog.1
  let s : Fin m × Fin 3 → Bool := fun p =>
    match p.2 with
    | ⟨0, _⟩ => s0 p.1
    | ⟨1, _⟩ => s1 p.1
    | ⟨2, _⟩ => s2 p.1
  let grp : ℕ → Finset (Fin m) := fun g =>
    (Finset.univ : Finset (Fin m)).filter (fun i => g * size ≤ i.val ∧ i.val < (g + 1) * size)
  let lastGrp : Finset (Fin m) :=
    (Finset.univ : Finset (Fin m)).filter (fun i => q * size ≤ i.val)
  let choose : ℕ → ℕ → K → Bool := fun level path x =>
    if hfull : level < a * q then
      let g := level / a
      let r := level % a
      have hr : r < a := Nat.mod_lt level (by omega)
      let pat : Fin (r + 1) → Bool := fun t =>
        if t.val < r then path.testBit (g * a + t.val) else false
      let cnt := ((grp g).filter (fun i =>
        ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t)).card
      decide (cnt.choose (2 ^ (a - 1 - r)) % 2 = 1)
    else if hlast : level < a * q + bLast then
      let r := level - a * q
      have hr : r < bLast := by omega
      let pat : Fin (r + 1) → Bool := fun t =>
        if t.val < r then path.testBit (a * q + t.val) else false
      let cnt := (lastGrp.filter (fun i =>
        ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩))) (s (i, ⟨t.val, by omega⟩)) = pat t)).card
      decide (cnt.choose (2 ^ (bLast - 1 - r)) % 2 = 1)
    else false
  let prefixOf : ℕ → Fin m → Fin 3 → Bool := fun path i t =>
    if i.val < q * size then
      let g := i.val / size
      if t.val < a then path.testBit (g * a + t.val) else false
    else
      if t.val < bLast then path.testBit (a * q + t.val) else false
  let pred : ℕ → Fin m → K → Bool := fun path i x =>
    let y0 := xor (bitOf x (idx (i, 0))) (s0 i)
    let y1 := xor (bitOf x (idx (i, 1))) (s1 i)
    let y2 := xor (bitOf x (idx (i, 2))) (s2 i)
    let u0 := bitOf x (idx (i, 0))
    let u1 := bitOf x (idx (i, 1))
    let u2 := bitOf x (idx (i, 2))
    let p0 := prefixOf path i 0
    let p1 := prefixOf path i 1
    let p2 := prefixOf path i 2
    xor (xor (y0 && y1 && y2) (xor y0 (!p0) && xor y1 (!p1) && xor y2 (!p2)))
      (xor (xor (xor (c0 i) (l0 i && u0)) (l1 i && u1)) (l2 i && u2))
  refine ⟨choose, pred, ?_, ?_, ?_⟩
  · intro level path
    by_cases hfull : level.val < a * q
    · let g := level.val / a
      let r := level.val % a
      have hr : r < a := Nat.mod_lt level.val (by omega)
      let pat : Fin (r + 1) → Bool := fun t =>
        if t.val < r then path.testBit (g * a + t.val) else false
      have hfn : choose level.val path = (fun x =>
          decide (((grp g).filter (fun i =>
            ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
              (s (i, ⟨t.val, by omega⟩)) = pat t)).card.choose (2 ^ (a - 1 - r)) % 2 = 1)) := by
        ext x
        simp only [choose, hfull, ↓reduceDIte]
        rfl
      rw [hfn]
      rcases choose_count_deg_K idx s (grp g) r (by omega) pat (2 ^ (a - 1 - r)) with ⟨terms, hdeg, heval⟩
      have hbd := choose_deg_le ha1 ha3 ha1 (le_refl a) hr
      exact ⟨terms, fun mon hm => le_trans (hdeg mon hm) hbd, heval⟩
    · have hlast : level.val < a * q + bLast := level.isLt
      let r := level.val - a * q
      have hr : r < bLast := by omega
      have hb1 : 1 ≤ bLast := by omega
      let pat : Fin (r + 1) → Bool := fun t =>
        if t.val < r then path.testBit (a * q + t.val) else false
      have hfn : choose level.val path = (fun x =>
          decide ((lastGrp.filter (fun i =>
            ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
              (s (i, ⟨t.val, by omega⟩)) = pat t)).card.choose (2 ^ (bLast - 1 - r)) % 2 = 1)) := by
        ext x
        simp only [choose, hfull, hlast, ↓reduceDIte]
        rfl
      rw [hfn]
      rcases choose_count_deg_K idx s lastGrp r (by omega) pat (2 ^ (bLast - 1 - r)) with ⟨terms, hdeg, heval⟩
      have hbd := choose_deg_le ha1 ha3 hb1 hbLast_le hr
      exact ⟨terms, fun mon hm => le_trans (hdeg mon hm) hbd, heval⟩
  · intro path i
    exact deg2_cancel_triple (idx (i, 0)) (idx (i, 1)) (idx (i, 2))
      (s0 i) (s1 i) (s2 i) (c0 i) (l0 i) (l1 i) (l2 i)
      (prefixOf path i 0) (prefixOf path i 1) (prefixOf path i 2)
  · intro x hx
    have hblock_inv : ∀ (G : Finset (Fin m)) (base b : ℕ) (_hb3 : b ≤ 3),
        base + b ≤ steps → G.card < 2 ^ b →
        (∀ (r : ℕ) (_hr : r < b),
          choose (base + r) (stepRun choose x (base + r)) x =
          decide ((G.filter (fun i =>
            ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
              (s (i, ⟨t.val, by omega⟩)) =
              (if t.val < r then (stepRun choose x (base + r)).testBit (base + t.val) else false))).card.choose
              (2 ^ (b - 1 - r)) % 2 = 1)) →
        ∀ (r : ℕ) (_hr : r ≤ b),
          (G.filter (fun i =>
            ∀ t : Fin r, xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
              (s (i, ⟨t.val, by omega⟩)) =
              (stepRun choose x (base + r)).testBit (base + t.val))).card < 2 ^ (b - r) := by
      intro G base b hb3 hbase hGcard hchoose r
      induction r with
      | zero =>
        intro _
        calc
          (G.filter _).card ≤ G.card := Finset.card_filter_le _ _
          _ < 2 ^ b := hGcard
          _ = 2 ^ (b - 0) := by simp
      | succ r ih =>
        intro hrb
        have hlt_b : r < b := by omega
        have hih := ih (by omega)
        let pos := base + r
        let Sprev := G.filter (fun i =>
          ∀ t : Fin r, xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
            (s (i, ⟨t.val, by omega⟩)) = (stepRun choose x pos).testBit (base + t.val))
        let S0 := Sprev.filter (fun i =>
          xor (bitOf x (idx (i, ⟨r, by omega⟩))) (s (i, ⟨r, by omega⟩)) = false)
        let S1 := Sprev.filter (fun i =>
          xor (bitOf x (idx (i, ⟨r, by omega⟩))) (s (i, ⟨r, by omega⟩)) = true)
        have hS01_disj : Disjoint S0 S1 := by
          rw [Finset.disjoint_left]
          intro i h1 h2
          simp only [S0, S1, Finset.mem_filter] at h1 h2
          rw [h1.2] at h2
          exact Bool.noConfusion h2.2
        have hS01_union : S0 ∪ S1 = Sprev := by
          ext i
          simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
          cases xor (bitOf x (idx (i, ⟨r, by omega⟩))) (s (i, ⟨r, by omega⟩)) <;> simp
        have hS01_card : S0.card + S1.card = Sprev.card := by
          rw [← Finset.card_union_of_disjoint hS01_disj, hS01_union]
        have hSprev_lt : Sprev.card < 2 ^ (b - r) := hih
        have hstep_eq : base + (r + 1) = pos + 1 := by omega
        have hbit_prev : ∀ t : Fin r,
            (stepRun choose x (pos + 1)).testBit (base + t.val) =
            (stepRun choose x pos).testBit (base + t.val) := by
          intro t
          rw [stepRun_succ, testBit_add_shift (stepRun_lt choose x pos)]
          have : base + t.val < pos := by omega
          simp [this]
        have hbit_cur :
            (stepRun choose x (pos + 1)).testBit pos = choose pos (stepRun choose x pos) x := by
          rw [stepRun_succ, testBit_add_shift (stepRun_lt choose x pos)]
          simp
        have hS0_eq :
            S0 = G.filter (fun i =>
              ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
                (s (i, ⟨t.val, by omega⟩)) =
                (if t.val < r then (stepRun choose x pos).testBit (base + t.val) else false)) := by
          ext i
          dsimp only [S0, Sprev]
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
          constructor
          · intro h
            refine ⟨h.1.1, fun t => ?_⟩
            by_cases ht : t.val < r
            · simp only [ht, ↓reduceIte]
              exact h.1.2 ⟨t.val, ht⟩
            · have hteq : t.val = r := by omega
              simp only [ht, ↓reduceIte]
              have hfin : (⟨t.val, by omega⟩ : Fin 3) = ⟨r, by omega⟩ := Fin.ext hteq
              rw [hfin]
              exact h.2
          · intro h
            refine ⟨⟨h.1, fun t => ?_⟩, ?_⟩
            · have h1 := h.2 ⟨t.val, by omega⟩
              simpa [t.isLt] using h1
            · have h1 := h.2 ⟨r, by omega⟩
              simpa using h1
        have hchoose_eq : choose pos (stepRun choose x pos) x = decide (2 ^ (b - 1 - r) ≤ S0.card) := by
          have hs_eq : b - r = (b - 1 - r) + 1 := by omega
          have hS0_lt : S0.card < 2 ^ ((b - 1 - r) + 1) := by
            rw [← hs_eq]
            omega
          have hch := hchoose r hlt_b
          rw [← hS0_eq] at hch
          rw [hch, choose_two_pow_mod_two (b - 1 - r) S0.card hS0_lt]
          by_cases hle : 2 ^ (b - 1 - r) ≤ S0.card <;> simp [hle]
        have hSnext_eq :
            G.filter (fun i =>
              ∀ t : Fin (r + 1), xor (bitOf x (idx (i, ⟨t.val, by omega⟩)))
                (s (i, ⟨t.val, by omega⟩)) =
                (stepRun choose x (base + (r + 1))).testBit (base + t.val)) =
            if 2 ^ (b - 1 - r) ≤ S0.card then S1 else S0 := by
          ext i
          rw [hstep_eq]
          by_cases hle : 2 ^ (b - 1 - r) ≤ S0.card
          · simp only [hle, ↓reduceIte]
            dsimp only [S1, Sprev]
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
            constructor
            · intro h
              refine ⟨⟨h.1, fun t => ?_⟩, ?_⟩
              · have h1 := h.2 ⟨t.val, by omega⟩
                rwa [hbit_prev t] at h1
              · have h1 := h.2 ⟨r, by omega⟩
                rw [show base + r = pos from rfl, hbit_cur, hchoose_eq] at h1
                simpa [hle] using h1
            · intro h
              refine ⟨h.1.1, fun t => ?_⟩
              by_cases ht : t.val < r
              · rw [hbit_prev ⟨t.val, ht⟩]
                exact h.1.2 ⟨t.val, ht⟩
              · have hteq : t.val = r := by omega
                have hfin : (⟨t.val, by omega⟩ : Fin 3) = ⟨r, by omega⟩ := Fin.ext hteq
                rw [hfin, hteq, show base + r = pos from rfl, hbit_cur, hchoose_eq]
                simpa [hle] using h.2
          · simp only [hle, ↓reduceIte]
            dsimp only [S0, Sprev]
            rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
            constructor
            · intro h
              refine ⟨⟨h.1, fun t => ?_⟩, ?_⟩
              · have h1 := h.2 ⟨t.val, by omega⟩
                rwa [hbit_prev t] at h1
              · have h1 := h.2 ⟨r, by omega⟩
                rw [show base + r = pos from rfl, hbit_cur, hchoose_eq] at h1
                simpa [hle] using h1
            · intro h
              refine ⟨h.1.1, fun t => ?_⟩
              by_cases ht : t.val < r
              · rw [hbit_prev ⟨t.val, ht⟩]
                exact h.1.2 ⟨t.val, ht⟩
              · have hteq : t.val = r := by omega
                have hfin : (⟨t.val, by omega⟩ : Fin 3) = ⟨r, by omega⟩ := Fin.ext hteq
                rw [hfin, hteq, show base + r = pos from rfl, hbit_cur, hchoose_eq]
                simpa [hle] using h.2
        rw [hSnext_eq]
        have hbr : b - (r + 1) = b - 1 - r := by omega
        have h2pow : 2 ^ (b - r) = 2 * 2 ^ (b - 1 - r) := by
          have : b - r = (b - 1 - r) + 1 := by omega
          rw [this, pow_succ']
        rw [hbr]
        split_ifs with hle <;> omega
    intro i
    have hrun_eq : run steps choose x = stepRun choose x steps := rfl
    have hmiss : ∃ t : Fin 3,
        xor (bitOf x (idx (i, t))) (s (i, t)) ≠ prefixOf (stepRun choose x steps) i t := by
      by_cases hiq : i.val < q * size
      · let g := i.val / size
        have hg_lt : g < q := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hiq)
        have hi_mem : i ∈ grp g := by
          simp only [grp, Finset.mem_filter, Finset.mem_univ, true_and]
          have h1 := Nat.div_mul_le_self i.val size
          have h2 : i.val < g * size + size := by
            have hdm : size * g + i.val % size = i.val := Nat.div_add_mod i.val size
            have hgs : g * size = size * g := mul_comm g size
            have hml := Nat.mod_lt i.val hsize_pos
            omega
          rw [add_mul, one_mul]
          exact ⟨h1, h2⟩
        have hgrp_card : (grp g).card < 2 ^ a := by
          have hsub : (grp g).image Fin.val ⊆ Finset.Ico (g * size) ((g + 1) * size) := by
            intro v hv
            rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
            exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hj).2
          have hc1 : (grp g).card = ((grp g).image Fin.val).card :=
            (Finset.card_image_of_injective _ Fin.val_injective).symm
          have hc2 := Finset.card_le_card hsub
          rw [Nat.card_Ico] at hc2
          have hsub_eq : (g + 1) * size - g * size = size := by
            rw [add_mul, one_mul]; omega
          rw [hsub_eq] at hc2
          have : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by omega)
          omega
        have hsteps_eq : steps = a * q + bLast := rfl
        have hinv_g := hblock_inv (grp g) (g * a) a ha3 (by
          have h1 : (g + 1) * a ≤ q * a := Nat.mul_le_mul_right a (by omega)
          rw [add_mul, one_mul] at h1
          have h2 : q * a = a * q := mul_comm q a
          omega) hgrp_card (by
          intro r hr
          have hlt : g * a + r < a * q := by
            have h1 : (g + 1) * a ≤ q * a := Nat.mul_le_mul_right a (by omega)
            rw [add_mul, one_mul] at h1
            have h2 : q * a = a * q := mul_comm q a
            omega
          have hdiv : (g * a + r) / a = g := by
            rw [mul_comm g a, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, add_zero]
          have hmod : (g * a + r) % a = r := by
            rw [mul_comm g a, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
          simp only [choose, hlt, ↓reduceDIte]
          have hset :
              (grp ((g * a + r) / a)).filter (fun j =>
                ∀ t : Fin ((g * a + r) % a + 1),
                  xor (bitOf x (idx (j, ⟨t.val, by have := Nat.mod_lt (g * a + r) (by omega); omega⟩)))
                    (s (j, ⟨t.val, by have := Nat.mod_lt (g * a + r) (by omega); omega⟩)) =
                  (if t.val < (g * a + r) % a then (stepRun choose x (g * a + r)).testBit ((g * a + r) / a * a + t.val) else false)) =
              (grp g).filter (fun j =>
                ∀ t : Fin (r + 1),
                  xor (bitOf x (idx (j, ⟨t.val, by omega⟩))) (s (j, ⟨t.val, by omega⟩)) =
                  (if t.val < r then (stepRun choose x (g * a + r)).testBit (g * a + t.val) else false)) := by
            rw [hdiv]
            ext j
            simp only [Finset.mem_filter]
            constructor <;> intro ⟨hjG, hj⟩
            · refine ⟨hjG, fun t => ?_⟩
              have h1 := hj ⟨t.val, by omega⟩
              simp only [hmod] at h1
              exact h1
            · refine ⟨hjG, fun t => ?_⟩
              have h1 := hj ⟨t.val, by omega⟩
              simp only [hmod]
              exact h1
          rw [hset, hmod]) a (le_refl a)
        simp only [Nat.sub_self, pow_zero] at hinv_g
        by_contra hall
        push Not at hall
        have him : i ∈ (grp g).filter (fun j =>
            ∀ t : Fin a, xor (bitOf x (idx (j, ⟨t.val, by omega⟩))) (s (j, ⟨t.val, by omega⟩)) =
              (stepRun choose x (g * a + a)).testBit (g * a + t.val)) := by
          refine Finset.mem_filter.mpr ⟨hi_mem, fun t => ?_⟩
          have ht3 : t.val < 3 := by omega
          have h1 := hall ⟨t.val, ht3⟩
          simp only [prefixOf, hiq, ↓reduceIte, t.isLt] at h1
          have hlt_s : g * a + t.val < steps := by
            have h1' : (g + 1) * a ≤ q * a := Nat.mul_le_mul_right a (by omega)
            rw [add_mul, one_mul] at h1'
            have h2' : q * a = a * q := mul_comm q a
            omega
          have hlt_a : g * a + t.val < g * a + a := by omega
          rw [stepRun_testBit choose x steps _ hlt_s,
              ← stepRun_testBit choose x (g * a + a) _ hlt_a] at h1
          exact h1
        have hpos := Finset.card_pos.mpr ⟨i, him⟩
        omega
      · have hi_mem : i ∈ lastGrp := Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega⟩
        have hrem_pos : 0 < rem := by
          have hdiv := Nat.div_add_mod m size
          have : q * size ≤ i.val := by omega
          have : i.val < m := i.isLt
          have hmq : size * q + rem = m := hdiv
          have hqm : q * size = size * q := mul_comm q size
          omega
        have hlast_card : lastGrp.card < 2 ^ bLast := by
          have hsub : lastGrp.image Fin.val ⊆ Finset.Ico (q * size) m := by
            intro v hv
            rcases Finset.mem_image.mp hv with ⟨j, hj, rfl⟩
            exact Finset.mem_Ico.mpr ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
          have hc1 : lastGrp.card = (lastGrp.image Fin.val).card :=
            (Finset.card_image_of_injective _ Fin.val_injective).symm
          have hc2 := Finset.card_le_card hsub
          rw [Nat.card_Ico] at hc2
          have hmq : size * q + rem = m := Nat.div_add_mod m size
          have hsub_eq : m - q * size = rem := by
            have hqm : q * size = size * q := mul_comm q size
            omega
          rw [hsub_eq] at hc2
          omega
        have hinv_last := hblock_inv lastGrp (a * q) bLast (by omega) (le_refl steps) hlast_card (by
          intro r hr
          have hnfull : ¬(a * q + r < a * q) := by omega
          have hlt : a * q + r < a * q + bLast := by omega
          have hsub : a * q + r - a * q = r := by omega
          simp only [choose, hnfull, hlt, ↓reduceDIte]
          have hset :
              lastGrp.filter (fun j =>
                ∀ t : Fin (a * q + r - a * q + 1),
                  xor (bitOf x (idx (j, ⟨t.val, by omega⟩))) (s (j, ⟨t.val, by omega⟩)) =
                  (if t.val < a * q + r - a * q then (stepRun choose x (a * q + r)).testBit (a * q + t.val) else false)) =
              lastGrp.filter (fun j =>
                ∀ t : Fin (r + 1),
                  xor (bitOf x (idx (j, ⟨t.val, by omega⟩))) (s (j, ⟨t.val, by omega⟩)) =
                  (if t.val < r then (stepRun choose x (a * q + r)).testBit (a * q + t.val) else false)) := by
            ext j
            simp only [Finset.mem_filter]
            constructor <;> intro ⟨hjG, hj⟩
            · refine ⟨hjG, fun t => ?_⟩
              have h1 := hj ⟨t.val, by omega⟩
              simp only [hsub] at h1
              exact h1
            · refine ⟨hjG, fun t => ?_⟩
              have h1 := hj ⟨t.val, by omega⟩
              simp only [hsub]
              exact h1
          rw [hset, hsub]) bLast (le_refl bLast)
        simp only [Nat.sub_self, pow_zero] at hinv_last
        by_contra hall
        push Not at hall
        have him : i ∈ lastGrp.filter (fun j =>
            ∀ t : Fin bLast, xor (bitOf x (idx (j, ⟨t.val, by omega⟩))) (s (j, ⟨t.val, by omega⟩)) =
              (stepRun choose x (a * q + bLast)).testBit (a * q + t.val)) := by
          refine Finset.mem_filter.mpr ⟨hi_mem, fun t => ?_⟩
          have ht3 : t.val < 3 := by omega
          have h1 := hall ⟨t.val, ht3⟩
          simp only [prefixOf, hiq, ↓reduceIte, t.isLt] at h1
          exact h1
        have hpos := Finset.card_pos.mpr ⟨i, him⟩
        omega
    rw [hrun_eq, hout x hx i]
    simp only [pred]
    have hkill :
        (xor (xor (bitOf x (idx (i, 0))) (s0 i)) (!prefixOf (stepRun choose x steps) i 0) &&
         xor (xor (bitOf x (idx (i, 1))) (s1 i)) (!prefixOf (stepRun choose x steps) i 1) &&
         xor (xor (bitOf x (idx (i, 2))) (s2 i)) (!prefixOf (stepRun choose x steps) i 2)) = false := by
      have hneq_false : ∀ a b : Bool, a ≠ b → xor a (!b) = false := by
        intro a b h; cases a <;> cases b <;> simp_all
      rcases hmiss with ⟨t, ht⟩
      fin_cases t
      · simp only [s] at ht
        change xor (bitOf x (idx (i, 0))) (s0 i) ≠ prefixOf (stepRun choose x steps) i 0 at ht
        rw [hneq_false _ _ ht]
        rfl
      · simp only [s] at ht
        change xor (bitOf x (idx (i, 1))) (s1 i) ≠ prefixOf (stepRun choose x steps) i 1 at ht
        rw [hneq_false _ _ ht]
        simp
      · simp only [s] at ht
        change xor (bitOf x (idx (i, 2))) (s2 i) ≠ prefixOf (stepRun choose x steps) i 2 at ht
        rw [hneq_false _ _ ht]
        simp
    rw [hkill, Bool.xor_false]

private def wordOf (k : ℕ) (w : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨∑ q : Fin k, if w q then 2 ^ q.val else 0, by
    have hsum : ∑ q : Fin k, (if w q then 2 ^ q.val else 0) ≤ ∑ q : Fin k, 2 ^ q.val :=
      Finset.sum_le_sum fun q _ => by cases w q <;> simp
    have hgeom : ∑ q : Fin k, 2 ^ q.val = 2 ^ k - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i)]
      have h1 := Nat.geomSum_eq (by omega : 2 ≤ 2) k
      simpa using h1
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
    omega⟩

private lemma testBit_wordOf (k : ℕ) (w : Fin k → Bool) (q : Fin k) :
    (wordOf k w).val.testBit q.val = w q := by
  have haux : ∀ n : ℕ, ∀ g : ℕ → Bool, ∀ j : ℕ, j < n →
      (∑ i ∈ Finset.range n, if g i then 2 ^ i else 0).testBit j = g j := by
    intro n
    induction n with
    | zero => intro _ _ hj; omega
    | succ n ih =>
      intro g j hj
      rw [Finset.sum_range_succ]
      have hlt : ∑ i ∈ Finset.range n, (if g i then 2 ^ i else 0) < 2 ^ n := by
        have h1 : ∑ i ∈ Finset.range n, (if g i then 2 ^ i else 0) ≤ ∑ i ∈ Finset.range n, 2 ^ i :=
          Finset.sum_le_sum fun i _ => by cases g i <;> simp
        have h2 : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
          have := Nat.geomSum_eq (by omega : 2 ≤ 2) n
          simpa using this
        have h3 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by omega)
        omega
      have hshift : (if g n then 2 ^ n else 0) = (g n).toNat <<< n := by
        rw [Nat.shiftLeft_eq]
        cases g n <;> simp
      rw [hshift, testBit_add_shift hlt]
      by_cases hjn : j < n
      · simp only [hjn, ↓reduceIte]
        exact ih g j hjn
      · have hjeq : j = n := by omega
        subst hjeq
        simp
  have hcongr :
      ∑ i : Fin k, (if w i then 2 ^ i.val else 0) =
      ∑ i : Fin k, (if (if h : i.val < k then w ⟨i.val, h⟩ else false) then 2 ^ i.val else 0) :=
    Finset.sum_congr rfl fun i _ => by simp [i.isLt]
  simp only [wordOf]
  rw [hcongr, Fin.sum_univ_eq_sum_range (fun i => if (if h : i < k then w ⟨i, h⟩ else false) then 2 ^ i else 0)]
  have h1 := haux k (fun i => if h : i < k then w ⟨i, h⟩ else false) q.val q.isLt
  simpa [q.isLt] using h1

private lemma wordOf_testBit (k : ℕ) (x : Fin (2 ^ k)) :
    wordOf k (fun i : Fin k => x.val.testBit i.val) = x := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact testBit_wordOf k (fun i : Fin k => x.val.testBit i.val) ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (wordOf k _).isLt
          (Nat.pow_le_pow_right (by omega) (by omega))),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt
          (Nat.pow_le_pow_right (by omega) (by omega)))]

private lemma main_proof :
    ∀ (k : ℕ), 0 < k → ∀ (constant : ℕ → Fin (2 ^ k)) (m : ℕ) (starts : Fin m → ℕ),
    Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k) →
    ∀ (row ref : Fin (2 ^ k)),
    (∀ i : Fin m,
      let old := fun j : ℕ => (stateAt k constant row.val 0 ref.val).testBit ((starts i + j) % k)
      let first := fun j : ℕ => (stateAt k constant row.val 1 ref.val).testBit ((starts i + j) % k)
      let τ := xor (xor (old 6) (old 7)) (old 8)
      let α := xor (xor (xor (old 5) (old 6)) (old 7))
        (xor ((rot k 0 ref.val).testBit ((starts i + 6) % k)) ((constant 1).val.testBit ((starts i + 6) % k)))
      let β := xor τ
        (xor ((rot k 0 ref.val).testBit ((starts i + 7) % k)) ((constant 1).val.testBit ((starts i + 7) % k)))
      τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !α ∧ first 4 = β) →
    ∀ (pin : Finset (Fin k)),
    (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k) →
    (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k) →
    let K := Fin (2 ^ k)
    let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
    let par := fun (n : ℕ) => n % 2 == 1
    let fiber := (Finset.univ : Finset K).filter (fun keyWord =>
      ∀ z ∈ pin, (stateAt k constant row.val 0 keyWord.val).testBit (z.val % k) =
        (stateAt k constant row.val 0 ref.val).testBit (z.val % k))
    let deg := fun (u : ℕ) (f : K → Bool) =>
      ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ u) ∧
        ∀ key, f key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card)
    let run := fun (steps : ℕ) (ask : ℕ → ℕ → K → Bool) (x : K) =>
      (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
    let out := fun (input : K) (i : Fin m) =>
      (stateAt k constant row.val 2 input.val).testBit ((starts i + 5) % k)
    (∀ (b d L : ℕ) (ask : ℕ → ℕ → K → Bool) (leaf : ℕ → Fin L → Fin m → K → Bool),
      (∀ (u : Fin d) (path : ℕ), deg b (ask u.val path)) →
      (∀ path a i, deg 2 (leaf path a i)) →
      let hit := fiber.filter (fun sample => ∃ a, ∀ i, leaf (run d ask sample) a i sample = out sample i)
      let count := (Finset.range (m + 1)).sum (fun filled =>
        if filled < L * (b * d + 1) then Nat.choose m filled * 7 ^ (m - filled) else 0)
      8 ^ m * hit.card ≤ fiber.card * count ∧
      (hit = fiber → m + 1 ≤ L * 2 ^ d ∧ m < L * (b * d + 1))) ∧
    ∀ a : ℕ, 1 ≤ a → a ≤ 3 →
      let size := 2 ^ a - 1
      let steps := a * (m / size) + Nat.clog 2 (m % size + 1)
      ∃ (choose : ℕ → ℕ → K → Bool) (pred : ℕ → Fin m → K → Bool),
        (∀ (level : Fin steps) (path : ℕ), deg (2 ^ (a - 1)) (choose level.val path)) ∧
        (∀ path i, deg 2 (pred path i)) ∧
        ∀ x ∈ fiber, ∀ i, pred (run steps choose x) i x = out x i := by
  classical
  intro k hk constant m starts hinj row ref hgood pin hpin_in hpin_out K bitOf par fiber deg run out
  have href_mem : ref ∈ fiber := Finset.mem_filter.mpr ⟨Finset.mem_univ ref, fun _ _ => rfl⟩
  have hfiber_pos : 1 ≤ fiber.card := Finset.card_pos.mpr ⟨ref, href_mem⟩
  by_cases hm0 : m = 0
  · constructor
    · intro b d L ask leaf _ _ hit count
      by_cases hL : L = 0
      · have hhit0 : hit = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rcases (Finset.mem_filter.mp hx).2 with ⟨a, _⟩
          have := a.isLt
          omega
        refine ⟨by simp [hhit0], fun heq => ?_⟩
        rw [hhit0] at heq
        have : fiber.card = 0 := by rw [← heq]; rfl
        omega
      · have hcount : count = 1 := by
          have hpos : 0 < L * (b * d + 1) := Nat.mul_pos (by omega) (by omega)
          simp [count, hm0, hpos]
        refine ⟨?_, ?_⟩
        · rw [hcount, hm0, pow_zero, one_mul, mul_one]
          exact Finset.card_filter_le _ _
        · intro _
          have h1 : 1 ≤ L * 2 ^ d := Nat.mul_pos (by omega) (Nat.two_pow_pos d)
          have h2 : 0 < L * (b * d + 1) := Nat.mul_pos (by omega) (by omega)
          omega
    · intro a ha1 ha3 size steps
      refine ⟨fun _ _ _ => false, fun _ _ _ => false, ?_, ?_, ?_⟩
      · intro level _
        have hsteps0 : steps = 0 := by
          simp only [steps, size, hm0]
          interval_cases a <;> decide
        have := level.isLt
        omega
      · intro _ i
        have := i.isLt
        omega
      · intro _ _ i
        have := i.isLt
        omega
  · have hk12 : 12 ≤ k := by
      let f : Fin m × Fin 12 → Fin k := fun z => ⟨(starts z.1 + z.2.val) % k, Nat.mod_lt _ hk⟩
      have hf : Function.Injective f := fun z₁ z₂ h => hinj (congr_arg Fin.val h)
      have hc := Fintype.card_le_of_injective f hf
      simp only [Fintype.card_prod, Fintype.card_fin] at hc
      have : 1 ≤ m := by omega
      have : 12 ≤ m * 12 := by nlinarith
      omega
    have hformula : ∀ i : Fin m,
        ∃ (s0 s1 s2 c0 l0 l1 l2 : Bool),
          ∀ key ∈ fiber,
            let u0 := key.val.testBit ((starts i + 8) % k)
            let u1 := key.val.testBit ((starts i + 9) % k)
            let u2 := key.val.testBit ((starts i + 10) % k)
            out key i =
              xor ((xor u0 s0) && (xor u1 s1) && (xor u2 s2))
                (xor (xor (xor c0 (l0 && u0)) (l1 && u1)) (l2 && u2)) := by
      intro i
      rcases guarded_two_round_formula hk12 constant row ref (starts i) (hgood i) with
        ⟨s0, s1, s2, c0, l0, l1, l2, hf⟩
      refine ⟨s0, s1, s2, c0, l0, l1, l2, fun key hkey => hf key ?_⟩
      intro j
      rcases hpin_in i j with ⟨z, hzpin, hzval⟩
      have hz := (Finset.mem_filter.mp hkey).2 z hzpin
      rw [Nat.mod_eq_of_lt z.isLt, hzval] at hz
      exact hz
    let s0 : Fin m → Bool := fun i => Classical.choose (hformula i)
    let s1 : Fin m → Bool := fun i => Classical.choose (Classical.choose_spec (hformula i))
    let s2 : Fin m → Bool := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (hformula i)))
    let c0 : Fin m → Bool := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hformula i))))
    let l0 : Fin m → Bool := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hformula i)))))
    let l1 : Fin m → Bool := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hformula i))))))
    let l2 : Fin m → Bool := fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hformula i)))))))
    have hout_eq : ∀ key ∈ fiber, ∀ i : Fin m,
        let u0 := key.val.testBit ((starts i + 8) % k)
        let u1 := key.val.testBit ((starts i + 9) % k)
        let u2 := key.val.testBit ((starts i + 10) % k)
        out key i =
          xor ((xor u0 (s0 i)) && (xor u1 (s1 i)) && (xor u2 (s2 i)))
            (xor (xor (xor (c0 i) (l0 i && u0)) (l1 i && u1)) (l2 i && u2)) :=
      fun key hkey i =>
        Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hformula i))))))) key hkey
    let idxFun : Fin m × Fin 3 → Fin k := fun p => ⟨(starts p.1 + 8 + p.2.val) % k, Nat.mod_lt _ hk⟩
    have hidx_inj : Function.Injective idxFun := by
      intro p₁ p₂ hEq
      have hv : (starts p₁.1 + 8 + p₁.2.val) % k = (starts p₂.1 + 8 + p₂.2.val) % k :=
        congr_arg Fin.val hEq
      have h1 := hinj (a₁ := (p₁.1, ⟨8 + p₁.2.val, by omega⟩))
        (a₂ := (p₂.1, ⟨8 + p₂.2.val, by omega⟩)) (by
          change (starts p₁.1 + (8 + p₁.2.val)) % k = (starts p₂.1 + (8 + p₂.2.val)) % k
          have e1 : starts p₁.1 + (8 + p₁.2.val) = starts p₁.1 + 8 + p₁.2.val := by omega
          have e2 : starts p₂.1 + (8 + p₂.2.val) = starts p₂.1 + 8 + p₂.2.val := by omega
          rw [e1, e2]; exact hv)
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h1
      exact Prod.ext h1.1 (Fin.ext (by omega))
    let idx : Fin m × Fin 3 ↪ Fin k := ⟨idxFun, hidx_inj⟩
    constructor
    · intro b d L ask leaf hask hleaf hit count
      by_cases hL : L = 0
      · have hhit0 : hit = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro x hx
          rcases (Finset.mem_filter.mp hx).2 with ⟨a, _⟩
          have := a.isLt
          omega
        refine ⟨by simp [hhit0], fun heq => ?_⟩
        rw [hhit0] at heq
        have : fiber.card = 0 := by rw [← heq]; rfl
        omega
      · have hL1 : 1 ≤ L := by omega
        let pinRaw : Finset (Fin k) := pin.image (fun z => ⟨(z.val + k - 1) % k, Nat.mod_lt _ hk⟩)
        have hfiber_iff : ∀ kw : K, kw ∈ fiber ↔ ∀ q ∈ pinRaw, bitOf kw q = bitOf ref q := by
          intro kw
          simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, pinRaw, Finset.mem_image,
            forall_exists_index, and_imp]
          have hbit : ∀ (x : K) (z : Fin k),
              (stateAt k constant row.val 0 x.val).testBit (z.val % k) =
              xor (bitOf x ⟨(z.val + k - 1) % k, Nat.mod_lt _ hk⟩) (row.val.testBit z.val) := by
            intro x z
            rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, Nat.testBit_xor, testBit_rot x.isLt z.isLt]
            have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
            rw [h1m]
          constructor
          · intro h q z hz hq
            subst hq
            have h1 := h z hz
            rw [hbit kw z, hbit ref z] at h1
            have := congr_arg (fun b => xor b (row.val.testBit z.val)) h1
            simpa [bool_xor_cancel] using this
          · intro h z hz
            rw [hbit kw z, hbit ref z, h _ z hz rfl]
        let active : Finset (Fin k) := Finset.univ.image idx
        have hdisj_pa : Disjoint pinRaw active := by
          rw [Finset.disjoint_left]
          intro q hqp hqa
          rcases Finset.mem_image.mp hqp with ⟨z, hzpin, hzq⟩
          rcases Finset.mem_image.mp hqa with ⟨p, _, hpq⟩
          have h1 : (z.val + k - 1) % k = (starts p.1 + 8 + p.2.val) % k := by
            have := congr_arg Fin.val (hzq.trans hpq.symm)
            exact this
          have h2 : z.val = (starts p.1 + 9 + p.2.val) % k := by
            have hadd : (z.val + k - 1 + 1) % k = z.val := by
              have : z.val + k - 1 + 1 = z.val + k := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
            have hadd2 : (starts p.1 + 8 + p.2.val + 1) % k = (starts p.1 + 9 + p.2.val) % k := by
              congr 1; omega
            rw [← hadd, ← Nat.mod_add_mod, h1, Nat.mod_add_mod, hadd2]
          exact hpin_out p.1 p.2 z hzpin h2
        let extSet : Finset (Fin k) := Finset.univ \ (pinRaw ∪ active)
        let s : Fin m × Fin 3 → Bool := fun p =>
          match p.2 with
          | ⟨0, _⟩ => s0 p.1
          | ⟨1, _⟩ => s1 p.1
          | ⟨2, _⟩ => s2 p.1
        have hbit_wordOf : ∀ (w : Fin k → Bool) (q : Fin k), bitOf (wordOf k w) q = w q :=
          testBit_wordOf k
        have hwordOf_bit : ∀ x : K, wordOf k (bitOf x) = x := wordOf_testBit k
        let mkExt : (extSet → Bool) → Fin k → Bool := fun e q =>
          if h : q ∈ extSet then e ⟨q, h⟩ else bitOf ref q
        let mkKey : (extSet → Bool) → (Fin m × Fin 3 → Bool) → K := fun e y =>
          wordOf k (fun q =>
            if h : ∃ v : Fin m × Fin 3, idx v = q then
              xor (y (Classical.choose h)) (s (Classical.choose h))
            else mkExt e q)
        have hmkKey_fiber : ∀ e y, mkKey e y ∈ fiber := by
          intro e y
          rw [hfiber_iff]
          intro q hqp
          simp only [mkKey, hbit_wordOf]
          have hna : ¬∃ v : Fin m × Fin 3, idx v = q := by
            rintro ⟨v, rfl⟩
            exact Finset.disjoint_left.mp hdisj_pa hqp (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
          have hne : q ∉ extSet := by
            simp [extSet, hqp]
          simp [hna, mkExt, hne]
        have hmkKey_idx : ∀ e y v, bitOf (mkKey e y) (idx v) = xor (y v) (s v) := by
          intro e y v
          simp only [mkKey, hbit_wordOf]
          have hex : ∃ v' : Fin m × Fin 3, idx v' = idx v := ⟨v, rfl⟩
          simp only [hex, ↓reduceDIte]
          have hch : Classical.choose hex = v := idx.injective (Classical.choose_spec hex)
          rw [hch]
        have hmkKey_bij :
            ∀ x ∈ fiber, ∃! p : (extSet → Bool) × (Fin m × Fin 3 → Bool), mkKey p.1 p.2 = x := by
          intro x hx
          let e0 : extSet → Bool := fun q => bitOf x q.1
          let y0 : Fin m × Fin 3 → Bool := fun v => xor (bitOf x (idx v)) (s v)
          refine ⟨(e0, y0), ?_, ?_⟩
          · rw [← hwordOf_bit x]
            apply congr_arg (wordOf k)
            funext q
            by_cases ha : ∃ v : Fin m × Fin 3, idx v = q
            · rcases ha with ⟨v, rfl⟩
              have hex : ∃ v' : Fin m × Fin 3, idx v' = idx v := ⟨v, rfl⟩
              simp only [hex, ↓reduceDIte]
              have hch : Classical.choose hex = v := idx.injective (Classical.choose_spec hex)
              rw [hch]
              exact bool_xor_cancel (bitOf x (idx v)) (s v)
            · simp only [ha, ↓reduceDIte, mkExt]
              by_cases he : q ∈ extSet
              · simp [he, e0]
              · have hqp : q ∈ pinRaw := by
                  simp only [extSet, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
                    not_not] at he
                  rcases he with hp | hact
                  · exact hp
                  · rcases Finset.mem_image.mp hact with ⟨v, _, hv⟩
                    exact absurd ⟨v, hv⟩ ha
                simp only [he, ↓reduceDIte]
                exact ((hfiber_iff x).mp hx q hqp).symm
          · rintro ⟨e, y⟩ hEq
            have hbitEq : ∀ q : Fin k, bitOf (mkKey e y) q = bitOf x q := fun q => by rw [hEq]
            apply Prod.ext
            · funext ⟨q, hqe⟩
              have hna : ¬∃ v : Fin m × Fin 3, idx v = q := by
                rintro ⟨v, rfl⟩
                have hmem : idx v ∈ active := Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
                simp [extSet, hmem] at hqe
              have h1 := hbitEq q
              simp only [mkKey, hbit_wordOf, hna, ↓reduceDIte, mkExt, hqe] at h1
              exact h1
            · funext v
              have h1 := hbitEq (idx v)
              rw [hmkKey_idx e y v] at h1
              have := congr_arg (fun b => xor b (s v)) h1
              simpa [bool_xor_cancel, y0] using this
        have hfiber_card : fiber.card = Fintype.card (extSet → Bool) * 8 ^ m := by
          have h1 : fiber.card = Fintype.card ((extSet → Bool) × (Fin m × Fin 3 → Bool)) := by
            symm
            refine Finset.card_bij (fun p _ => mkKey p.1 p.2) (fun p _ => hmkKey_fiber p.1 p.2) ?_ ?_
            · intro p₁ _ p₂ _ hEq
              have hu := hmkKey_bij (mkKey p₁.1 p₁.2) (hmkKey_fiber p₁.1 p₁.2)
              rcases hu with ⟨p0, _, huniq⟩
              exact (huniq p₁ rfl).trans (huniq p₂ hEq.symm).symm
            · intro x hx
              rcases hmkKey_bij x hx with ⟨p, hp, _⟩
              exact ⟨p, Finset.mem_univ p, hp⟩
          rw [h1, Fintype.card_prod]
          congr 1
          simp [Fintype.card_fun, Fintype.card_prod, mul_comm m 3, pow_mul]
        have hslice_bound : ∀ e : extSet → Bool,
            let H := (Finset.univ : Finset (Fin m × Fin 3 → Bool)).filter (fun y => mkKey e y ∈ hit)
            H.card ≤ count ∧ (H = Finset.univ → m + 1 ≤ L * 2 ^ d) := by
          intro e H
          have hPask : ∀ (u : Fin d) (path : ℕ),
              ∃ P : Poly (Fin m × Fin 3), degLe P b ∧
                ∀ y, evalPoly P y = z2OfBool (ask u.val path (mkKey e y)) := by
            intro u path
            rcases poly_of_deg (f := fun w => ask u.val path (wordOf k w)) (by
              rcases hask u path with ⟨terms, hdeg, heval⟩
              refine ⟨terms, hdeg, fun w => ?_⟩
              have h := heval (wordOf k w)
              simp only [par, hbit_wordOf] at h
              convert h) with ⟨Pk, hPk_deg, hPk_eval⟩
            rcases pullPoly_exists idx s (mkExt e) Pk hPk_deg with ⟨Q, hQ_deg, hQ_eval⟩
            exact ⟨Q, hQ_deg, fun y => by rw [hQ_eval y, hPk_eval]⟩
          let Ppath : Fin (2 ^ d) → Poly (Fin m × Fin 3) := fun path =>
            polyProdList (List.ofFn (fun u : Fin d =>
              let Pu := Classical.choose (hPask u (path.val % 2 ^ u.val))
              if path.val.testBit u.val then Pu else polyAdd (polyOne _) Pu))
          have hPpath_deg : ∀ path : Fin (2 ^ d), degLe (Ppath path) (b * d) := by
            intro path
            have h1 := degLe_prodList (d := b) (List.ofFn (fun u : Fin d =>
              let Pu := Classical.choose (hPask u (path.val % 2 ^ u.val))
              if path.val.testBit u.val then Pu else polyAdd (polyOne _) Pu)) (by
              intro R hR
              rcases List.mem_ofFn.mp hR with ⟨u, rfl⟩
              split_ifs
              · exact (Classical.choose_spec (hPask u (path.val % 2 ^ u.val))).1
              · exact degLe_add (degLe_one b) (Classical.choose_spec (hPask u (path.val % 2 ^ u.val))).1)
            have hlen : (List.ofFn (fun u : Fin d =>
                let Pu := Classical.choose (hPask u (path.val % 2 ^ u.val))
                if path.val.testBit u.val then Pu else polyAdd (polyOne _) Pu)).length * b = b * d := by
              simp [List.length_ofFn, mul_comm]
            rwa [hlen] at h1
          let runFn : (Fin m × Fin 3 → Bool) → Fin (2 ^ d) := fun y =>
            ⟨stepRun ask (mkKey e y) d, stepRun_lt ask _ d⟩
          have hPpath_eval : ∀ path y, evalPoly (Ppath path) y = if runFn y = path then 1 else 0 := by
            intro path y
            simp only [Ppath, evalPoly_prodList, List.map_ofFn, List.prod_ofFn, Function.comp_apply]
            have hlit : ∀ u : Fin d,
                evalPoly (if path.val.testBit u.val then Classical.choose (hPask u (path.val % 2 ^ u.val))
                  else polyAdd (polyOne _) (Classical.choose (hPask u (path.val % 2 ^ u.val)))) y =
                if ask u.val (path.val % 2 ^ u.val) (mkKey e y) = path.val.testBit u.val then (1 : ZMod 2) else 0 := by
              intro u
              have hev := (Classical.choose_spec (hPask u (path.val % 2 ^ u.val))).2 y
              cases hp : path.val.testBit u.val <;> cases ha : ask u.val (path.val % 2 ^ u.val) (mkKey e y)
              · simp only [Bool.false_eq_true, ↓reduceIte, evalPoly_add, evalPoly_one]
                rw [hev, ha]; decide
              · simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, evalPoly_add, evalPoly_one]
                rw [hev, ha]; decide
              · simp only [↓reduceIte, Bool.false_eq_true]
                rw [hev, ha]; rfl
              · simp only [↓reduceIte]
                rw [hev, ha]; rfl
            simp_rw [hlit]
            have hiff : runFn y = path ↔
                ∀ u : Fin d, ask u.val (path.val % 2 ^ u.val) (mkKey e y) = path.val.testBit u.val := by
              constructor
              · intro hEq
                exact (stepRun_eq_iff ask (mkKey e y) d path.val path.isLt).mp (congr_arg Fin.val hEq)
              · intro hall
                exact Fin.ext ((stepRun_eq_iff ask (mkKey e y) d path.val path.isLt).mpr hall)
            by_cases hEq : runFn y = path
            · simp only [hEq, ↓reduceIte]
              have hall := hiff.mp hEq
              refine Finset.prod_eq_one fun u _ => ?_
              simp [hall u]
            · simp only [hEq, ↓reduceIte]
              have hnot : ¬∀ u : Fin d, ask u.val (path.val % 2 ^ u.val) (mkKey e y) = path.val.testBit u.val :=
                fun h => hEq (hiff.mpr h)
              push Not at hnot
              rcases hnot with ⟨u, hu⟩
              exact Finset.prod_eq_zero (Finset.mem_univ u) (by simp [hu])
          have hQleaf : ∀ (path : Fin (2 ^ d)) (a : Fin L) (i : Fin m),
              ∃ Q : Poly (Fin m × Fin 3), degLe Q 2 ∧
                ∀ y, evalPoly Q y =
                  z2OfBool (xor (leaf path.val a i (mkKey e y))
                    (xor (xor (xor (c0 i) (l0 i && bitOf (mkKey e y) (idx (i, 0))))
                      (l1 i && bitOf (mkKey e y) (idx (i, 1))))
                      (l2 i && bitOf (mkKey e y) (idx (i, 2))))) := by
            intro path a i
            rcases poly_of_deg (f := fun w => leaf path.val a i (wordOf k w)) (by
              rcases hleaf path.val a i with ⟨terms, hdeg, heval⟩
              refine ⟨terms, hdeg, fun w => ?_⟩
              have h := heval (wordOf k w)
              simp only [par, hbit_wordOf] at h
              convert h) with ⟨Pk, hPk_deg, hPk_eval⟩
            let constP : Bool → Poly (Fin k) := fun b => if b then polyOne (Fin k) else polyZero (Fin k)
            let Paff : Poly (Fin k) := polySumList [
              constP (c0 i),
              polyMul (constP (l0 i)) (polyVar (idx (i, 0))),
              polyMul (constP (l1 i)) (polyVar (idx (i, 1))),
              polyMul (constP (l2 i)) (polyVar (idx (i, 2)))
            ]
            have hPaff_deg : degLe Paff 2 := by
              refine degLe_sumList _ ?_
              intro R hR
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
              rcases hR with rfl | rfl | rfl | rfl
              · cases c0 i <;> [exact degLe_zero 2; exact degLe_one 2]
              · cases l0 i <;> [exact degLe_mono (degLe_mul (degLe_zero 0) (degLe_var _)) (by omega);
                  exact degLe_mono (degLe_mul (degLe_one 0) (degLe_var _)) (by omega)]
              · cases l1 i <;> [exact degLe_mono (degLe_mul (degLe_zero 0) (degLe_var _)) (by omega);
                  exact degLe_mono (degLe_mul (degLe_one 0) (degLe_var _)) (by omega)]
              · cases l2 i <;> [exact degLe_mono (degLe_mul (degLe_zero 0) (degLe_var _)) (by omega);
                  exact degLe_mono (degLe_mul (degLe_one 0) (degLe_var _)) (by omega)]
            have hPaff_eval : ∀ w : Fin k → Bool,
                evalPoly Paff w = z2OfBool (xor (xor (xor (c0 i) (l0 i && w (idx (i, 0))))
                  (l1 i && w (idx (i, 1)))) (l2 i && w (idx (i, 2)))) := by
              intro w
              have hc : ∀ b, evalPoly (constP b) w = z2OfBool b := by
                intro b; cases b <;> simp [constP, evalPoly_one, evalPoly_zero, z2OfBool]
              simp only [Paff, evalPoly_sumList, List.map_cons, List.map_nil, List.sum_cons,
                List.sum_nil, add_zero, evalPoly_mul, evalPoly_var, hc, z2OfBool_xor, z2OfBool_and]
              ring
            rcases pullPoly_exists idx s (mkExt e) (polyAdd Pk Paff) (degLe_add hPk_deg hPaff_deg) with
              ⟨Q, hQ_deg, hQ_eval⟩
            refine ⟨Q, hQ_deg, fun y => ?_⟩
            rw [hQ_eval y, evalPoly_add, hPk_eval, hPaff_eval]
            simp only [mkKey, hbit_wordOf, z2OfBool_xor]
          let Qleaf : Fin (2 ^ d) → Fin L → Fin m → Poly (Fin m × Fin 3) := fun path a i =>
            Classical.choose (hQleaf path a i)
          have hQleaf_deg : ∀ path a i, degLe (Qleaf path a i) 2 := fun path a i =>
            (Classical.choose_spec (hQleaf path a i)).1
          have hH_sat : ∀ y ∈ H, ∃ a : Fin L, ∀ i : Fin m,
              evalPoly (Qleaf (runFn y) a i) y = z2OfBool (y (i, 0) && y (i, 1) && y (i, 2)) := by
            intro y hy
            have hyhit : mkKey e y ∈ hit := (Finset.mem_filter.mp hy).2
            rcases (Finset.mem_filter.mp hyhit).2 with ⟨a, ha⟩
            refine ⟨a, fun i => ?_⟩
            rw [(Classical.choose_spec (hQleaf (runFn y) a i)).2 y]
            have h1 := ha i
            have hrun : run d ask (mkKey e y) = (runFn y).val := rfl
            rw [hrun] at h1
            rw [h1, hout_eq (mkKey e y) (hmkKey_fiber e y) i]
            have hu0 : (mkKey e y).val.testBit ((starts i + 8) % k) = bitOf (mkKey e y) (idx (i, 0)) := rfl
            have hu1 : (mkKey e y).val.testBit ((starts i + 9) % k) = bitOf (mkKey e y) (idx (i, 1)) := rfl
            have hu2 : (mkKey e y).val.testBit ((starts i + 10) % k) = bitOf (mkKey e y) (idx (i, 2)) := rfl
            rw [hu0, hu1, hu2, bool_xor_cancel, hmkKey_idx e y (i, 0), hmkKey_idx e y (i, 1),
              hmkKey_idx e y (i, 2)]
            simp only [s, bool_xor_cancel]
          refine ⟨slice_hit_card_le hL1 Ppath hPpath_deg runFn hPpath_eval Qleaf hQleaf_deg H hH_sat, ?_⟩
          intro hHuniv
          refine slice_odd_preimage hL1 Qleaf hQleaf_deg ?_
          intro y
          have hy : y ∈ H := hHuniv.symm ▸ Finset.mem_univ y
          rcases hH_sat y hy with ⟨a, ha⟩
          exact ⟨runFn y, a, ha⟩
        have hhit_sum :
            hit.card = ∑ e : extSet → Bool,
              ((Finset.univ : Finset (Fin m × Fin 3 → Bool)).filter (fun y => mkKey e y ∈ hit)).card := by
          have h1 :
              hit.card =
              ((Finset.univ : Finset ((extSet → Bool) × (Fin m × Fin 3 → Bool))).filter
                (fun p => mkKey p.1 p.2 ∈ hit)).card := by
            symm
            refine Finset.card_bij (fun p _ => mkKey p.1 p.2)
              (fun p hp => (Finset.mem_filter.mp hp).2) ?_ ?_
            · intro p₁ _ p₂ _ hEq
              have hu := hmkKey_bij (mkKey p₁.1 p₁.2) (hmkKey_fiber p₁.1 p₁.2)
              rcases hu with ⟨p0, _, huniq⟩
              exact (huniq p₁ rfl).trans (huniq p₂ hEq.symm).symm
            · intro x hx
              have hxf : x ∈ fiber := (Finset.mem_filter.mp hx).1
              rcases hmkKey_bij x hxf with ⟨p, hp, _⟩
              exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp.symm ▸ hx⟩, hp⟩
          rw [h1, Finset.card_filter, Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun e _ => (Finset.card_filter _ _).symm
        have hhit_le : hit.card ≤ Fintype.card (extSet → Bool) * count := by
          rw [hhit_sum]
          calc
            ∑ e : extSet → Bool,
                ((Finset.univ : Finset (Fin m × Fin 3 → Bool)).filter (fun y => mkKey e y ∈ hit)).card
                ≤ ∑ _e : extSet → Bool, count := Finset.sum_le_sum fun e _ => (hslice_bound e).1
            _ = Fintype.card (extSet → Bool) * count := by simp
        have hmain_le : 8 ^ m * hit.card ≤ fiber.card * count := by
          rw [hfiber_card]
          calc
            8 ^ m * hit.card ≤ 8 ^ m * (Fintype.card (extSet → Bool) * count) :=
              Nat.mul_le_mul_left (8 ^ m) hhit_le
            _ = Fintype.card (extSet → Bool) * 8 ^ m * count := by ring
        refine ⟨hmain_le, ?_⟩
        intro hEq
        let e0 : extSet → Bool := fun q => bitOf ref q.1
        have hHuniv : (Finset.univ : Finset (Fin m × Fin 3 → Bool)).filter (fun y => mkKey e0 y ∈ hit) =
            Finset.univ := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true, hEq]
          exact hmkKey_fiber e0 y
        refine ⟨(hslice_bound e0).2 hHuniv, ?_⟩
        by_contra hnotlt
        have hle : L * (b * d + 1) ≤ m := by omega
        have hcount_lt : count < 8 ^ m := by
          have htot := sum_binomial_seven m
          have hle_sum : count + 1 ≤
              (Finset.range (m + 1)).sum (fun filled => Nat.choose m filled * 7 ^ (m - filled)) := by
            rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, mul_one]
            simp only [count, Finset.sum_range_succ]
            have hnm : ¬(m < L * (b * d + 1)) := by omega
            simp only [hnm, ↓reduceIte, add_zero]
            have hle1 :
                (Finset.range m).sum (fun filled =>
                  if filled < L * (b * d + 1) then Nat.choose m filled * 7 ^ (m - filled) else 0) ≤
                (Finset.range m).sum (fun filled => Nat.choose m filled * 7 ^ (m - filled)) :=
              Finset.sum_le_sum fun filled _ => by split_ifs <;> omega
            omega
          omega
        rw [hEq] at hmain_le
        have h8_le : 8 ^ m ≤ count := Nat.le_of_mul_le_mul_left (by
          rw [mul_comm (8 ^ m) fiber.card] at hmain_le
          exact hmain_le) hfiber_pos
        omega
    · intro a ha1 ha3
      exact part2_upper hk12 idx s0 s1 s2 c0 l0 l1 l2 out fiber hout_eq a ha1 ha3

end PEqualNP.Outside.L_meta_25908_aux

open PEqualNP.Outside.L_meta_25908_aux in
theorem PEqualNP.Outside.L_meta_25908 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let fiber := (Finset.univ : Finset K).filter (fun keyWord =>
    ∀ z ∈ pin, bit row.val 0 keyWord.val z.val = bit row.val 0 ref.val z.val)
  let deg := fun (u : Nat) (f : K → Bool) =>
    ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ key, f key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card)
  let run := fun (steps : Nat) (ask : Nat → Nat → K → Bool) (x : K) =>
    (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
  let out := fun (input : K) (i : Fin m) => bit row.val 2 input.val (starts i+5)
  (∀ (b d L : Nat) (ask : Nat → Nat → K → Bool) (leaf : Nat → Fin L → Fin m → K → Bool),
    (∀ (u : Fin d) (path : Nat), deg b (ask u.val path)) →
    (∀ path a i, deg 2 (leaf path a i)) →
    let hit := fiber.filter (fun sample => ∃ a, ∀ i, leaf (run d ask sample) a i sample = out sample i)
    let count := (Finset.range (m+1)).sum (fun filled =>
      if filled < L*(b*d+1) then Nat.choose m filled * 7^(m-filled) else 0)
    8^m * hit.card ≤ fiber.card * count ∧
    (hit = fiber → m+1 ≤ L*2^d ∧ m < L*(b*d+1))) ∧
  ∀ a : Nat, 1 ≤ a → a ≤ 3 →
    let size := 2^a-1
    let steps := a*(m/size) + Nat.clog 2 (m % size+1)
    ∃ (choose : Nat → Nat → K → Bool) (pred : Nat → Fin m → K → Bool),
      (∀ (level : Fin steps) (path : Nat), deg (2^(a-1)) (choose level.val path)) ∧
      (∀ path i, deg 2 (pred path i)) ∧
      ∀ x ∈ fiber, ∀ i, pred (run steps choose x) i x = out x i) := by
  intro k hk constant rot0 step0 state0 injected0 bit0 m starts hinj good0 row ref hgood pin hpin_in hpin_out
  exact main_proof k hk constant m starts hinj row ref hgood pin hpin_in hpin_out
