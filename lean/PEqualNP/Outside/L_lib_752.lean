import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_752_aux

private def z2OfBool (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma z2OfBool_inj {a b : Bool} (h : z2OfBool a = z2OfBool b) : a = b := by
  cases a <;> cases b <;> simp [z2OfBool] at h <;> rfl

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

private def stepRun {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0

private lemma stepRun_zero {W : Type*} (ask : ℕ → ℕ → W → Bool) (x : W) :
    stepRun ask x 0 = 0 := rfl

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

private lemma testBit_mod_two_pow (x a t : ℕ) (ht : t < a) :
    (x % 2 ^ a).testBit t = x.testBit t := by
  rw [Nat.testBit_mod_two_pow]
  simp [ht]

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
  split_ifs <;> first | exact mul_one _ | exact mul_zero _ | exact zero_mul _ | tauto

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

private lemma degLe_zero {V : Type*} (b : ℕ) : degLe (polyZero V) b := by
  intro mon h
  exact absurd rfl h

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

private lemma choose_count_deg {g a : ℕ} (_ha : 0 < a) (j : Fin g) (r : ℕ) (hr : r < a)
    (pat : Fin (r + 1) → Bool) (T : ℕ) :
    let M := 2 ^ a
    let m := M - 1
    let V := Fin g × Fin m × Fin a
    let W := V → Bool
    let f : W → Bool := fun x =>
      decide ((((Finset.univ : Finset (Fin m)).filter
        (fun i => ∀ t : Fin (r + 1), x (j, i, ⟨t.val, by omega⟩) = pat t)).card.choose T) % 2 = 1)
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ (r + 1) * T) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ v ∈ mon, input v = true)).card % 2) == 1) := by
  intro M m V W f
  let litPoly : Fin m → Fin (r + 1) → Poly V := fun i t =>
    if pat t then polyVar (j, i, ⟨t.val, by omega⟩)
    else polyAdd (polyOne V) (polyVar (j, i, ⟨t.val, by omega⟩))
  have hlit_deg : ∀ i t, degLe (litPoly i t) 1 := by
    intro i t
    simp only [litPoly]
    split_ifs
    · exact degLe_var _
    · exact degLe_add (degLe_one 1) (degLe_var _)
  have hlit_eval : ∀ i t x, evalPoly (litPoly i t) x =
      if x (j, i, ⟨t.val, by omega⟩) = pat t then (1 : ZMod 2) else 0 := by
    intro i t x
    simp only [litPoly]
    cases hp : pat t <;> cases hx : x (j, i, ⟨t.val, by omega⟩) <;>
      simp only [evalPoly_add, evalPoly_one, evalPoly_var, z2OfBool, hx, ↓reduceIte,
        Bool.false_eq_true, Bool.true_eq_false] <;> decide
  let rowPoly : Fin m → Poly V := fun i =>
    polyProdList (List.ofFn (fun t : Fin (r + 1) => litPoly i t))
  have hrow_deg : ∀ i, degLe (rowPoly i) (r + 1) := by
    intro i
    have h1 := degLe_prodList (d := 1) (List.ofFn (fun t : Fin (r + 1) => litPoly i t))
      (by intro P hP; rcases List.mem_ofFn.mp hP with ⟨t, rfl⟩; exact hlit_deg i t)
    have hlen : (List.ofFn (fun t : Fin (r + 1) => litPoly i t)).length * 1 = r + 1 := by
      simp [List.length_ofFn]
    rwa [hlen] at h1
  have hrow_eval : ∀ i x, evalPoly (rowPoly i) x =
      if ∀ t : Fin (r + 1), x (j, i, ⟨t.val, by omega⟩) = pat t then (1 : ZMod 2) else 0 := by
    intro i x
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
  let setsList : List (Finset (Fin m)) := (Finset.powersetCard T (Finset.univ : Finset (Fin m))).toList
  let setPoly : Finset (Fin m) → Poly V := fun S => polyProdList (S.toList.map rowPoly)
  let totalPoly : Poly V := polySumList (setsList.map setPoly)
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
  refine deg_of_poly totalPoly htotal_deg ?_
  intro x
  let Good := (Finset.univ : Finset (Fin m)).filter
    (fun i => ∀ t : Fin (r + 1), x (j, i, ⟨t.val, by omega⟩) = pat t)
  have heval_set : ∀ S : Finset (Fin m),
      evalPoly (setPoly S) x = if S ⊆ Good then (1 : ZMod 2) else 0 := by
    intro S
    simp only [setPoly]
    rw [evalPoly_prodList, List.map_map]
    have hprod_eq :
        (S.toList.map ((fun P => evalPoly P x) ∘ rowPoly)).prod =
        ∏ i ∈ S, evalPoly (rowPoly i) x := by
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
      have hng : ¬(∀ t : Fin (r + 1), x (j, i, ⟨t.val, by omega⟩) = pat t) := by
        intro h
        exact hiG (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
      exact Finset.prod_eq_zero hiS (by rw [hrow_eval]; simp [hng])
  have heval_tot : evalPoly totalPoly x = ((Good.card.choose T : ℕ) : ZMod 2) := by
    simp only [totalPoly]
    rw [evalPoly_sumList, List.map_map]
    have hsum_eq :
        (setsList.map ((fun P => evalPoly P x) ∘ setPoly)).sum =
        ∑ S ∈ Finset.powersetCard T (Finset.univ : Finset (Fin m)), evalPoly (setPoly S) x := by
      rw [Finset.sum_eq_multiset_sum, ← Finset.coe_toList (Finset.powersetCard T _),
        Multiset.map_coe, Multiset.sum_coe]
      rfl
    rw [hsum_eq]
    have hcongr :
        ∑ S ∈ Finset.powersetCard T (Finset.univ : Finset (Fin m)), evalPoly (setPoly S) x =
        ∑ S ∈ Finset.powersetCard T (Finset.univ : Finset (Fin m)),
          if S ⊆ Good then (1 : ZMod 2) else 0 :=
      Finset.sum_congr rfl fun S _ => heval_set S
    rw [hcongr, Finset.sum_boole]
    have hf_eq :
        (Finset.powersetCard T (Finset.univ : Finset (Fin m))).filter (fun S => S ⊆ Good) =
        Finset.powersetCard T Good := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      tauto
    rw [hf_eq, Finset.card_powersetCard]
  rw [heval_tot, z2_nat_eq_mod2]
  have hf_eq : f x = (Good.card.choose T % 2 == 1) := by
    change decide (Good.card.choose T % 2 = 1) = (Good.card.choose T % 2 == 1)
    cases h : Good.card.choose T % 2 == 1 <;> simp_all
  rw [hf_eq]

private lemma part1_adaptive {g a : ℕ} (_hg : 0 < g) (ha : 0 < a) :
    let M := 2 ^ a
    let m := M - 1
    let d := g * a
    let V := Fin g × Fin m × Fin a
    let W := V → Bool
    let deg := fun (b : ℕ) (f : W → Bool) =>
      ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
        ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
    let Y := Fin g → Fin M
    let valid := fun (x : W) (choice : Y) =>
      ∀ j i, ∃ v : Fin a, x (j, i, v) ≠ (choice j).val.testBit v.val
    let run := fun (ask : ℕ → ℕ → W → Bool) (x : W) =>
      (List.range d).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
    ∃ (choose : ℕ → ℕ → W → Bool) (decode : ℕ → Y),
      (∀ (u : Fin d) (h : ℕ),
        deg ((u.val % a + 1) * 2 ^ (a - 1 - u.val % a)) (choose u.val h)) ∧
      ∀ input, valid input (decode (run choose input)) := by
  intro M m d V W deg Y valid run
  let choose : ℕ → ℕ → W → Bool := fun pos h x =>
    if hpos : pos < d then
      let j : Fin g := ⟨pos / a, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hpos)⟩
      let r : ℕ := pos % a
      let pat : Fin (r + 1) → Bool := fun t =>
        if t.val < r then h.testBit (j.val * a + t.val) else false
      let cnt := ((Finset.univ : Finset (Fin m)).filter
        (fun i => ∀ t : Fin (r + 1), x (j, i, ⟨t.val, by have := Nat.mod_lt pos ha; omega⟩) = pat t)).card
      decide (cnt.choose (2 ^ (a - 1 - r)) % 2 = 1)
    else false
  let decode : ℕ → Y := fun trace j => ⟨(trace >>> (j.val * a)) % M, Nat.mod_lt _ (by positivity)⟩
  refine ⟨choose, decode, ?_, ?_⟩
  · intro u h
    have hu : u.val < d := u.isLt
    let j : Fin g := ⟨u.val / a, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hu)⟩
    let r : ℕ := u.val % a
    have hr : r < a := Nat.mod_lt u.val ha
    let pat : Fin (r + 1) → Bool := fun t =>
      if t.val < r then h.testBit (j.val * a + t.val) else false
    have hfn : choose u.val h = (fun x =>
        decide ((((Finset.univ : Finset (Fin m)).filter
          (fun i => ∀ t : Fin (r + 1), x (j, i, ⟨t.val, by omega⟩) = pat t)).card.choose
          (2 ^ (a - 1 - r))) % 2 = 1)) := by
      ext x
      simp only [choose, hu, ↓reduceDIte]
      rfl
    rw [hfn]
    exact choose_count_deg ha j r hr pat (2 ^ (a - 1 - r))
  · intro input j
    have hinv : ∀ (r : ℕ) (hra : r ≤ a),
        ((Finset.univ : Finset (Fin m)).filter
          (fun i => ∀ t : Fin r,
            input (j, i, ⟨t.val, by omega⟩) =
            (stepRun choose input (j.val * a + r)).testBit (j.val * a + t.val))).card <
        2 ^ (a - r) := by
      intro r
      induction r with
      | zero =>
        intro _
        calc
          ((Finset.univ : Finset (Fin m)).filter _).card ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_filter_le _ _
          _ = m := by simp
          _ < 2 ^ a := by
            have h1 : 1 ≤ 2 ^ a := Nat.one_le_pow a 2 (by omega)
            simp only [m, M]
            omega
          _ = 2 ^ (a - 0) := by simp
      | succ r ih =>
        intro hra
        have hlt_a : r < a := by omega
        have hih := ih (by omega)
        let pos := j.val * a + r
        have hpos_lt : pos < d := by
          have hj1 : j.val + 1 ≤ g := j.isLt
          have hmul : (j.val + 1) * a ≤ g * a := Nat.mul_le_mul_right a hj1
          rw [add_mul, one_mul] at hmul
          omega
        have hpos_div : pos / a = j.val := by
          simp only [pos]
          rw [mul_comm j.val a, Nat.mul_add_div ha, Nat.div_eq_of_lt hlt_a, add_zero]
        have hpos_mod : pos % a = r := by
          simp only [pos]
          rw [mul_comm j.val a, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_a]
        let Sprev := (Finset.univ : Finset (Fin m)).filter
          (fun i => ∀ t : Fin r,
            input (j, i, ⟨t.val, by omega⟩) =
            (stepRun choose input pos).testBit (j.val * a + t.val))
        let S0 := Sprev.filter (fun i => input (j, i, ⟨r, hlt_a⟩) = false)
        let S1 := Sprev.filter (fun i => input (j, i, ⟨r, hlt_a⟩) = true)
        have hS01_disj : Disjoint S0 S1 := by
          rw [Finset.disjoint_left]
          intro i h1 h2
          simp only [S0, S1, Finset.mem_filter] at h1 h2
          rw [h1.2] at h2
          exact Bool.noConfusion h2.2
        have hS01_union : S0 ∪ S1 = Sprev := by
          ext i
          simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
          cases input (j, i, ⟨r, hlt_a⟩) <;> simp
        have hS01_card : S0.card + S1.card = Sprev.card := by
          rw [← Finset.card_union_of_disjoint hS01_disj, hS01_union]
        have hstep_eq : j.val * a + (r + 1) = pos + 1 := by omega
        have hbit_prev : ∀ t : Fin r,
            (stepRun choose input (pos + 1)).testBit (j.val * a + t.val) =
            (stepRun choose input pos).testBit (j.val * a + t.val) := by
          intro t
          rw [stepRun_succ, testBit_add_shift (stepRun_lt choose input pos)]
          have : j.val * a + t.val < pos := by omega
          simp [this]
        have hbit_cur :
            (stepRun choose input (pos + 1)).testBit pos =
            choose pos (stepRun choose input pos) input := by
          rw [stepRun_succ, testBit_add_shift (stepRun_lt choose input pos)]
          simp
        have hS0_eq :
            S0 = (Finset.univ : Finset (Fin m)).filter
              (fun i => ∀ t : Fin (r + 1),
                input (j, i, ⟨t.val, by omega⟩) =
                (if t.val < r then (stepRun choose input pos).testBit (j.val * a + t.val) else false)) := by
          ext i
          simp only [S0, Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨h1, h2⟩ t
            by_cases ht : t.val < r
            · simp only [ht, ↓reduceIte]
              exact h1 ⟨t.val, ht⟩
            · have hteq : t.val = r := by omega
              simp only [ht, ↓reduceIte]
              have hfin : (⟨t.val, by omega⟩ : Fin a) = ⟨r, hlt_a⟩ := Fin.ext hteq
              rw [hfin]
              exact h2
          · intro h
            refine ⟨fun t => ?_, ?_⟩
            · have := h ⟨t.val, by omega⟩
              simpa [t.isLt] using this
            · have := h ⟨r, by omega⟩
              simpa using this
        have hSprev_lt : Sprev.card < 2 ^ (a - r) := hih
        have hchoose_eq :
            choose pos (stepRun choose input pos) input =
            decide (2 ^ (a - 1 - r) ≤ S0.card) := by
          have hs_eq : a - r = (a - 1 - r) + 1 := by omega
          have hS0_lt : S0.card < 2 ^ ((a - 1 - r) + 1) := by
            rw [← hs_eq]
            omega
          have hch :
              choose pos (stepRun choose input pos) input =
              decide (S0.card.choose (2 ^ (a - 1 - r)) % 2 = 1) := by
            simp only [choose, hpos_lt, ↓reduceDIte]
            have hset_eq :
                (Finset.univ : Finset (Fin m)).filter
                  (fun i => ∀ t : Fin (pos % a + 1),
                    input (⟨pos / a, Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hpos_lt)⟩, i,
                      ⟨t.val, by have := Nat.mod_lt pos ha; omega⟩) =
                    (if t.val < pos % a then (stepRun choose input pos).testBit ((pos / a) * a + t.val) else false)) =
                S0 := by
              rw [hS0_eq]
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor <;> intro hi t
              · have h1 := hi ⟨t.val, by omega⟩
                simp only [hpos_div, hpos_mod] at h1 ⊢
                exact h1
              · have h1 := hi ⟨t.val, by omega⟩
                simp only [hpos_div, hpos_mod] at h1 ⊢
                exact h1
            rw [hset_eq, hpos_mod]
          rw [hch, choose_two_pow_mod_two (a - 1 - r) S0.card hS0_lt]
          by_cases hle : 2 ^ (a - 1 - r) ≤ S0.card <;> simp [hle]
        have hSnext_eq :
            (Finset.univ : Finset (Fin m)).filter
              (fun i => ∀ t : Fin (r + 1),
                input (j, i, ⟨t.val, by omega⟩) =
                (stepRun choose input (j.val * a + (r + 1))).testBit (j.val * a + t.val)) =
            if 2 ^ (a - 1 - r) ≤ S0.card then S1 else S0 := by
          ext i
          rw [hstep_eq]
          by_cases hle : 2 ^ (a - 1 - r) ≤ S0.card
          · simp only [hle, ↓reduceIte, S1, Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hi
              refine ⟨fun t => ?_, ?_⟩
              · have := hi ⟨t.val, by omega⟩
                rwa [hbit_prev t] at this
              · have := hi ⟨r, by omega⟩
                rw [show j.val * a + r = pos from rfl, hbit_cur, hchoose_eq] at this
                simpa [hle] using this
            · intro ⟨h1, h2⟩ t
              by_cases ht : t.val < r
              · rw [hbit_prev ⟨t.val, ht⟩]
                exact h1 ⟨t.val, ht⟩
              · have hteq : t.val = r := by omega
                have hfin : (⟨t.val, by omega⟩ : Fin a) = ⟨r, hlt_a⟩ := Fin.ext hteq
                rw [hfin, hteq, show j.val * a + r = pos from rfl, hbit_cur, hchoose_eq]
                simpa [hle] using h2
          · simp only [hle, ↓reduceIte, S0, Sprev, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro hi
              refine ⟨fun t => ?_, ?_⟩
              · have := hi ⟨t.val, by omega⟩
                rwa [hbit_prev t] at this
              · have := hi ⟨r, by omega⟩
                rw [show j.val * a + r = pos from rfl, hbit_cur, hchoose_eq] at this
                simpa [hle] using this
            · intro ⟨h1, h2⟩ t
              by_cases ht : t.val < r
              · rw [hbit_prev ⟨t.val, ht⟩]
                exact h1 ⟨t.val, ht⟩
              · have hteq : t.val = r := by omega
                have hfin : (⟨t.val, by omega⟩ : Fin a) = ⟨r, hlt_a⟩ := Fin.ext hteq
                rw [hfin, hteq, show j.val * a + r = pos from rfl, hbit_cur, hchoose_eq]
                simpa [hle] using h2
        rw [hSnext_eq]
        have har : a - (r + 1) = a - 1 - r := by omega
        have h2pow : 2 ^ (a - r) = 2 * 2 ^ (a - 1 - r) := by
          have : a - r = (a - 1 - r) + 1 := by omega
          rw [this, pow_succ']
        rw [har]
        split_ifs with hle <;> omega
    have hfinal := hinv a (le_refl a)
    simp only [Nat.sub_self, pow_zero] at hfinal
    have hcard_lt1 :
        ((Finset.univ : Finset (Fin m)).filter
          (fun i => ∀ t : Fin a,
            input (j, i, t) =
            (stepRun choose input (j.val * a + a)).testBit (j.val * a + t.val))).card < 1 := hfinal
    have hcard0 :
        ((Finset.univ : Finset (Fin m)).filter
          (fun i => ∀ t : Fin a,
            input (j, i, t) =
            (stepRun choose input (j.val * a + a)).testBit (j.val * a + t.val))).card = 0 := by
      omega
    intro i
    by_contra hall
    push Not at hall
    have hmem : i ∈ (Finset.univ : Finset (Fin m)).filter
        (fun i => ∀ t : Fin a,
          input (j, i, t) =
          (stepRun choose input (j.val * a + a)).testBit (j.val * a + t.val)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro t
      have h1 := hall t
      have hbit_dec :
          (decode (run choose input) j).val.testBit t.val =
          (stepRun choose input (j.val * a + a)).testBit (j.val * a + t.val) := by
        have hja_le : j.val * a + t.val < d := by
          have hj1 : j.val + 1 ≤ g := j.isLt
          have hmul : (j.val + 1) * a ≤ g * a := Nat.mul_le_mul_right a hj1
          rw [add_mul, one_mul] at hmul
          omega
        have hja_a : j.val * a + t.val < j.val * a + a := by omega
        have hrun : run choose input = stepRun choose input d := rfl
        simp only [decode, hrun]
        rw [testBit_mod_two_pow _ a t.val t.isLt, Nat.testBit_shiftRight,
          stepRun_testBit choose input d _ hja_le,
          stepRun_testBit choose input (j.val * a + a) _ hja_a]
      rw [h1, hbit_dec]
    have hpos : 0 < ((Finset.univ : Finset (Fin m)).filter _).card := Finset.card_pos.mpr ⟨i, hmem⟩
    omega

private lemma part2_min_length {g a n : ℕ}
    (choose : ℕ → ℕ → (Fin g × Fin (2 ^ a - 1) × Fin a → Bool) → Bool)
    (decode : ℕ → (Fin g → Fin (2 ^ a)))
    (hvalid : ∀ input, ∀ j i, ∃ v : Fin a,
      input (j, i, v) ≠ (decode (stepRun choose input n) j).val.testBit v.val) :
    g * a ≤ n := by
  let M := 2 ^ a
  let m := M - 1
  let Y := Fin g → Fin M
  have hcard_other : ∀ w : Fin M, Fintype.card {u : Fin M // u ≠ w} = m := by
    intro w
    have h1 : Fintype.card {u : Fin M // u ≠ w} = ((Finset.univ : Finset (Fin M)).erase w).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun u => ⟨u.1, Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩⟩
          invFun := fun u => ⟨u.1, (Finset.mem_erase.mp u.2).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin]
  let otherEquiv : ∀ w : Fin M, Fin m ≃ {u : Fin M // u ≠ w} := fun w =>
    Fintype.equivOfCardEq (by simp [hcard_other w])
  let forceInput : Y → (Fin g × Fin m × Fin a → Bool) := fun y =>
    fun ⟨j, i, v⟩ => (otherEquiv (y j) i).1.val.testBit v.val
  have hdec_force : ∀ y : Y, decode (stepRun choose (forceInput y) n) = y := by
    intro y
    funext j
    by_contra hne
    let i : Fin m := (otherEquiv (y j)).symm ⟨decode (stepRun choose (forceInput y) n) j, hne⟩
    rcases hvalid (forceInput y) j i with ⟨v, hv⟩
    have hei : (otherEquiv (y j) i).1 = decode (stepRun choose (forceInput y) n) j := by
      simp [i]
    exact hv (by dsimp only [forceInput]; rw [hei])
  let enc : Y → Fin (2 ^ n) := fun y => ⟨stepRun choose (forceInput y) n, stepRun_lt choose _ n⟩
  have henc_inj : Function.Injective enc := by
    intro y₁ y₂ h
    have hv : stepRun choose (forceInput y₁) n = stepRun choose (forceInput y₂) n :=
      congr_arg Fin.val h
    rw [← hdec_force y₁, ← hdec_force y₂, hv]
  have hcard_le : Fintype.card Y ≤ Fintype.card (Fin (2 ^ n)) :=
    Fintype.card_le_of_injective enc henc_inj
  have hcardY : Fintype.card Y = 2 ^ (g * a) := by
    simp [Y, M, ← pow_mul, mul_comm]
  rw [hcardY, Fintype.card_fin] at hcard_le
  exact (Nat.pow_le_pow_iff_right (a := 2) (by omega)).mp hcard_le

private lemma cube_sum_mod2_const_flip {t : ℕ} (ht : 1 ≤ t) (b : Bool) :
    ∑ z : Fin t → Bool,
      z2OfBool (if z = (fun _ => false) then !b else b) = (1 : ZMod 2) := by
  have hsplit :
      ∑ z : Fin t → Bool, z2OfBool (if z = (fun _ => false) then !b else b) =
      z2OfBool (!b) + ∑ z ∈ (Finset.univ : Finset (Fin t → Bool)).erase (fun _ => false), z2OfBool b := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (fun _ : Fin t => false))]
    simp only [↓reduceIte]
    congr 1
    refine Finset.sum_congr rfl fun z hz => ?_
    have hne : z ≠ fun _ => false := (Finset.mem_erase.mp hz).1
    simp [hne]
  rw [hsplit, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  have h2t : ((2 ^ t - 1 : ℕ) : ZMod 2) = 1 := by
    have hge1 : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
    have hpow : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← pow_succ', Nat.sub_add_cancel ht]
    have hmod : (2 ^ t - 1) % 2 = 1 := by omega
    rw [z2_nat_eq_mod2]
    simp [hmod, z2OfBool]
  rw [h2t, one_mul]
  cases b <;> decide

private lemma cube_sum_mod2_indep {t : ℕ} (k0 : Fin t) (F : (Fin t → Bool) → ZMod 2)
    (hindep : ∀ z : Fin t → Bool, F (Function.update z k0 (!z k0)) = F z) :
    ∑ z : Fin t → Bool, F z = 0 := by
  let S0 := (Finset.univ : Finset (Fin t → Bool)).filter (fun z => z k0 = false)
  let S1 := (Finset.univ : Finset (Fin t → Bool)).filter (fun z => z k0 = true)
  have hdisj : Disjoint S0 S1 := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    simp only [S0, S1, Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  have hunion : S0 ∪ S1 = Finset.univ := by
    ext z
    simp only [S0, S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases z k0 <;> simp
  have hbij : ∑ z ∈ S0, F z = ∑ z ∈ S1, F z := by
    refine Finset.sum_bij (fun z _ => Function.update z k0 true) ?_ ?_ ?_ ?_
    · intro z _
      simp [S1]
    · intro z₁ hz₁ z₂ hz₂ hEq
      funext k
      by_cases hk : k = k0
      · subst hk
        have h1 := (Finset.mem_filter.mp hz₁).2
        have h2 := (Finset.mem_filter.mp hz₂).2
        rw [h1, h2]
      · have := congr_fun hEq k
        simpa [Function.update, hk] using this
    · intro z hz
      refine ⟨Function.update z k0 false, ?_, ?_⟩
      · simp [S0]
      · funext k
        by_cases hk : k = k0
        · subst hk
          simpa [Function.update] using (Finset.mem_filter.mp hz).2.symm
        · simp [Function.update, hk]
    · intro z hz
      have hzk : z k0 = false := (Finset.mem_filter.mp hz).2
      have hupd : Function.update z k0 (!z k0) = Function.update z k0 true := by
        simp [hzk]
      rw [← hupd, hindep z]
  rw [← hunion, Finset.sum_union hdisj, hbij]
  have h2 : ∀ a : ZMod 2, a + a = 0 := by intro a; fin_cases a <;> decide
  exact h2 _

private lemma exists_line_step {g M : ℕ} (F : (Fin g → Fin M) → Bool)
    {y₁ y₂ : Fin g → Fin M} (hne : F y₁ ≠ F y₂) :
    ∃ (j0 : Fin g) (y0 : Fin g → Fin M) (c₁ c₂ : Fin M),
      F (Function.update y0 j0 c₁) ≠ F (Function.update y0 j0 c₂) := by
  have haux : ∀ n : ℕ, ∀ y₁ y₂ : Fin g → Fin M,
      ((Finset.univ : Finset (Fin g)).filter (fun j => y₁ j ≠ y₂ j)).card ≤ n →
      F y₁ ≠ F y₂ →
      ∃ (j0 : Fin g) (y0 : Fin g → Fin M) (c₁ c₂ : Fin M),
        F (Function.update y0 j0 c₁) ≠ F (Function.update y0 j0 c₂) := by
    intro n
    induction n with
    | zero =>
      intro y₁ y₂ hc hne
      have hempty := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)
      have heq : y₁ = y₂ := by
        funext j
        by_contra hj
        have : j ∈ (Finset.univ : Finset (Fin g)).filter (fun j => y₁ j ≠ y₂ j) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        rw [hempty] at this
        exact Finset.notMem_empty j this
      exact absurd (by rw [heq]) hne
    | succ n ih =>
      intro y₁ y₂ hc hne
      have hne_set : ((Finset.univ : Finset (Fin g)).filter (fun j => y₁ j ≠ y₂ j)).Nonempty := by
        by_contra hempty
        have heq : y₁ = y₂ := by
          funext j
          by_contra hj
          exact hempty ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
        exact hne (by rw [heq])
      rcases hne_set with ⟨j0, hj0⟩
      let ymid := Function.update y₁ j0 (y₂ j0)
      by_cases h1 : F y₁ ≠ F ymid
      · refine ⟨j0, y₁, y₁ j0, y₂ j0, ?_⟩
        simpa [ymid, Function.update_eq_self] using h1
      · push Not at h1
        have h2 : F ymid ≠ F y₂ := by rwa [← h1]
        have hsub :
            (Finset.univ : Finset (Fin g)).filter (fun j => ymid j ≠ y₂ j) ⊆
            ((Finset.univ : Finset (Fin g)).filter (fun j => y₁ j ≠ y₂ j)).erase j0 := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hj ⊢
          have hjne : j ≠ j0 := by
            intro h
            subst h
            simp [ymid] at hj
          refine ⟨hjne, ?_⟩
          simpa [ymid, Function.update, hjne] using hj
        have hcard' : ((Finset.univ : Finset (Fin g)).filter (fun j => ymid j ≠ y₂ j)).card ≤ n := by
          have h1 := Finset.card_le_card hsub
          rw [Finset.card_erase_of_mem hj0] at h1
          omega
        exact ih ymid y₂ hcard' h2
  exact haux g y₁ y₂ (by
    calc
      ((Finset.univ : Finset (Fin g)).filter _).card ≤ (Finset.univ : Finset (Fin g)).card :=
        Finset.card_filter_le _ _
      _ = g := by simp) hne

private lemma part3_degree_lower {g a : ℕ} (_hg : 0 < g) (ha : 0 < a)
    (ask : Fin (g * a) → (Fin g × Fin (2 ^ a - 1) × Fin a → Bool) → Bool)
    (report : (Fin (g * a) → Bool) → (Fin g → Fin (2 ^ a)))
    (label : Fin g → Fin (2 ^ a - 1) → Fin (2 ^ a) → Fin a → Bool)
    (hvalid : ∀ x j i, (fun rawBit => x (j, i, rawBit)) ≠ label j i (report (fun u => ask u x) j))
    (mask : Finset (Fin (g * a))) (hmask : mask.Nonempty)
    (b : ℕ) (terms : Finset (Finset (Fin g × Fin (2 ^ a - 1) × Fin a)))
    (hterms_deg : ∀ mon ∈ terms, mon.card ≤ b)
    (hterms_eval : ∀ word,
      (((mask.filter (fun bitId => ask bitId word = true)).card % 2) == 1) =
      (((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2) == 1)) :
    2 ^ (a - 1) ≤ b := by
  let M := 2 ^ a
  let m := M - 1
  let d := g * a
  let V := Fin g × Fin m × Fin a
  let W := V → Bool
  let Y := Fin g → Fin M
  have hcard_other : ∀ w : Fin M, Fintype.card {u : Fin M // u ≠ w} = m := by
    intro w
    have h1 : Fintype.card {u : Fin M // u ≠ w} = ((Finset.univ : Finset (Fin M)).erase w).card := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr
        { toFun := fun u => ⟨u.1, Finset.mem_erase.mpr ⟨u.2, Finset.mem_univ _⟩⟩
          invFun := fun u => ⟨u.1, (Finset.mem_erase.mp u.2).1⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin]
  let otherEquiv : ∀ w : Fin M, Fin m ≃ {u : Fin M // u ≠ w} := fun w =>
    Fintype.equivOfCardEq (by simp [hcard_other w])
  let forced : Y → W := fun y =>
    fun ⟨j, i, v⟩ => label j i (otherEquiv (y j) i).1 v
  have hrep_forced : ∀ y : Y, report (fun u => ask u (forced y)) = y := by
    intro y
    funext j
    by_contra hne
    let i : Fin m := (otherEquiv (y j)).symm ⟨report (fun u => ask u (forced y)) j, hne⟩
    have hEq : (fun rawBit => forced y (j, i, rawBit)) =
        label j i (report (fun u => ask u (forced y)) j) := by
      funext v
      have hei : (otherEquiv (y j) i).1 = report (fun u => ask u (forced y)) j := by simp [i]
      dsimp only [forced]
      rw [hei]
    exact hvalid (forced y) j i hEq
  have hrep_surj : Function.Surjective report :=
    fun y => ⟨fun u => ask u (forced y), hrep_forced y⟩
  have hcard_eq : Fintype.card (Fin d → Bool) = Fintype.card Y := by
    simp [Y, M, d, ← pow_mul, mul_comm]
  have hrep_bij : Function.Bijective report :=
    (Fintype.bijective_iff_surjective_and_card report).mpr ⟨hrep_surj, hcard_eq⟩
  let repEquiv : (Fin d → Bool) ≃ Y := Equiv.ofBijective report hrep_bij
  let parity : (Fin d → Bool) → Bool := fun s =>
    (((mask.filter (fun u => s u = true)).card % 2) == 1)
  let F : Y → Bool := fun y => parity (repEquiv.symm y)
  have hF_ask : ∀ x : W, parity (fun u => ask u x) = F (report (fun u => ask u x)) := by
    intro x
    have h1 : repEquiv.symm (report (fun u => ask u x)) = fun u => ask u x :=
      repEquiv.symm_apply_apply (fun u => ask u x)
    dsimp only [F]
    rw [h1]
  rcases hmask with ⟨u0, hu0⟩
  let s0 : Fin d → Bool := fun _ => false
  let s1 : Fin d → Bool := fun u => decide (u = u0)
  have hp0 : parity s0 = false := by
    simp [parity, s0]
  have hp1 : parity s1 = true := by
    have hf : mask.filter (fun u => s1 u = true) = {u0} := by
      ext u
      simp only [s1, Finset.mem_filter, Finset.mem_singleton, decide_eq_true_eq]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨h ▸ hu0, h⟩⟩
    simp [parity, hf]
  have hF_ne : F (repEquiv s0) ≠ F (repEquiv s1) := by
    simp only [F, Equiv.symm_apply_apply, hp0, hp1]
    decide
  rcases exists_line_step F hF_ne with ⟨j0, y0, c1, c2, hline⟩
  let phi : Fin M → Bool := fun c => F (Function.update y0 j0 c)
  let Sf := (Finset.univ : Finset (Fin M)).filter (fun c => phi c = false)
  let St := (Finset.univ : Finset (Fin M)).filter (fun c => phi c = true)
  have hSft_disj : Disjoint Sf St := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    simp only [Sf, St, Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  have hSft_union : Sf ∪ St = Finset.univ := by
    ext c
    simp only [Sf, St, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases phi c <;> simp
  have hSft_card : Sf.card + St.card = M := by
    rw [← Finset.card_union_of_disjoint hSft_disj, hSft_union, Finset.card_univ, Fintype.card_fin]
  have hSf_ne : Sf.Nonempty := by
    cases h1 : phi c1 <;> cases h2 : phi c2
    · exact ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact ⟨c2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
    · exfalso; exact hline (by simp [phi] at h1 h2; rw [h1, h2])
  have hSt_ne : St.Nonempty := by
    cases h1 : phi c1 <;> cases h2 : phi c2
    · exfalso; exact hline (by simp [phi] at h1 h2; rw [h1, h2])
    · exact ⟨c2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩⟩
    · exact ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
    · exact ⟨c1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩
  let t : ℕ := 2 ^ (a - 1)
  have ht_pos : 1 ≤ t := Nat.one_le_pow (a - 1) 2 (by omega)
  have hM_eq : M = 2 * t := by
    simp only [M, t]
    rw [← pow_succ', Nat.sub_add_cancel ha]
  have ht_le_m : t ≤ m := by
    simp only [m]
    omega
  let bmaj : Bool := decide (t ≤ St.card)
  let Smaj := (Finset.univ : Finset (Fin M)).filter (fun c => phi c = bmaj)
  have hSmaj_ge : t ≤ Smaj.card := by
    by_cases hst : t ≤ St.card
    · have hbm : bmaj = true := by simp [bmaj, hst]
      have hEq : Smaj = St := by simp [Smaj, St, hbm]
      rw [hEq]
      exact hst
    · have hbm : bmaj = false := by simp [bmaj, hst]
      have hEq : Smaj = Sf := by simp [Smaj, Sf, hbm]
      rw [hEq]
      omega
  have hex_cstar : ∃ cstar : Fin M, phi cstar = !bmaj := by
    by_cases hst : t ≤ St.card
    · have hbm : bmaj = true := by simp [bmaj, hst]
      rcases hSf_ne with ⟨c, hc⟩
      exact ⟨c, by simp [hbm, (Finset.mem_filter.mp hc).2]⟩
    · have hbm : bmaj = false := by simp [bmaj, hst]
      rcases hSt_ne with ⟨c, hc⟩
      exact ⟨c, by simp [hbm, (Finset.mem_filter.mp hc).2]⟩
  rcases hex_cstar with ⟨cstar, hcstar⟩
  rcases Finset.exists_subset_card_eq hSmaj_ge with ⟨S0, hS0_sub, hS0_card⟩
  have hcstar_nS0 : cstar ∉ S0 := by
    intro hmem
    have h1 := (Finset.mem_filter.mp (hS0_sub hmem)).2
    rw [hcstar] at h1
    cases bmaj <;> simp at h1
  let eS0 : Fin t ≃ S0 := Fintype.equivOfCardEq (by simp [Fintype.card_coe, hS0_card])
  let R : Finset (Fin M) := Finset.univ \ insert cstar S0
  have hR_card : R.card = m - t := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, Finset.card_insert_of_notMem hcstar_nS0, hS0_card]
    simp only [m]
    omega
  let eR : Fin (m - t) ≃ R := Fintype.equivOfCardEq (by simp [Fintype.card_coe, hR_card])
  let emb : (Fin t → Bool) → W := fun z => fun ⟨j, i, v⟩ =>
    if j = j0 then
      if hi : i.val < t then
        if z ⟨i.val, hi⟩ then label j0 i cstar v else label j0 i (eS0 ⟨i.val, hi⟩).1 v
      else
        label j0 i (eR ⟨i.val - t, by omega⟩).1 v
    else forced y0 (j, i, v)
  have hrep_other : ∀ z : Fin t → Bool, ∀ j : Fin g, j ≠ j0 →
      report (fun u => ask u (emb z)) j = y0 j := by
    intro z j hjne
    by_contra hne
    let i : Fin m := (otherEquiv (y0 j)).symm ⟨report (fun u => ask u (emb z)) j, hne⟩
    have hEq : (fun rawBit => emb z (j, i, rawBit)) =
        label j i (report (fun u => ask u (emb z)) j) := by
      funext v
      have hei : (otherEquiv (y0 j) i).1 = report (fun u => ask u (emb z)) j := by simp [i]
      simp only [emb, hjne, ↓reduceIte]
      dsimp only [forced]
      rw [hei]
    exact hvalid (emb z) j i hEq
  have hrep_j0_nR : ∀ z : Fin t → Bool, report (fun u => ask u (emb z)) j0 ∉ R := by
    intro z hmem
    let k : Fin (m - t) := eR.symm ⟨report (fun u => ask u (emb z)) j0, hmem⟩
    let i : Fin m := ⟨t + k.val, by omega⟩
    have hi_nlt : ¬(i.val < t) := by simp [i]
    have hEq : (fun rawBit => emb z (j0, i, rawBit)) =
        label j0 i (report (fun u => ask u (emb z)) j0) := by
      funext v
      have hsub : (⟨i.val - t, by omega⟩ : Fin (m - t)) = k := Fin.ext (by simp [i])
      have hek : (eR k).1 = report (fun u => ask u (emb z)) j0 := by simp [k]
      simp only [emb, ↓reduceIte, hi_nlt, ↓reduceDIte, hsub, hek]
    exact hvalid (emb z) j0 i hEq
  have hphi_emb : ∀ z : Fin t → Bool,
      F (report (fun u => ask u (emb z))) =
      if z = (fun _ => false) then !bmaj else bmaj := by
    intro z
    have hupd : report (fun u => ask u (emb z)) =
        Function.update y0 j0 (report (fun u => ask u (emb z)) j0) := by
      funext j
      by_cases hj : j = j0
      · subst hj; simp
      · simp [Function.update, hj, hrep_other z j hj]
    rw [hupd]
    change phi (report (fun u => ask u (emb z)) j0) = _
    have hmem_ins : report (fun u => ask u (emb z)) j0 ∈ insert cstar S0 := by
      by_contra hnot
      exact hrep_j0_nR z (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩)
    by_cases hz : z = fun _ => false
    · simp only [hz, ↓reduceIte]
      have hEq_cstar : report (fun u => ask u (emb (fun _ => false))) j0 = cstar := by
        rcases Finset.mem_insert.mp (hz ▸ hmem_ins) with hc | hS
        · exact hc
        · exfalso
          let k : Fin t := eS0.symm ⟨report (fun u => ask u (emb (fun _ => false))) j0, hS⟩
          let i : Fin m := ⟨k.val, by omega⟩
          have hilt : i.val < t := k.isLt
          have hEq : (fun rawBit => emb (fun _ => false) (j0, i, rawBit)) =
              label j0 i (report (fun u => ask u (emb (fun _ => false))) j0) := by
            funext v
            have hk : (⟨i.val, hilt⟩ : Fin t) = k := Fin.ext rfl
            have hek : (eS0 k).1 = report (fun u => ask u (emb (fun _ => false))) j0 := by simp [k]
            simp only [emb, ↓reduceIte, hilt, ↓reduceDIte, hk, Bool.false_eq_true, hek]
          exact hvalid (emb (fun _ => false)) j0 i hEq
      rw [hEq_cstar, hcstar]
    · simp only [hz, ↓reduceIte]
      have hex_k : ∃ k : Fin t, z k = true := by
        by_contra hall
        push Not at hall
        apply hz
        funext k
        cases hk : z k
        · rfl
        · exact absurd hk (hall k)
      rcases hex_k with ⟨k, hzk⟩
      have hne_cstar : report (fun u => ask u (emb z)) j0 ≠ cstar := by
        intro hc
        let i : Fin m := ⟨k.val, by omega⟩
        have hilt : i.val < t := k.isLt
        have hEq : (fun rawBit => emb z (j0, i, rawBit)) =
            label j0 i (report (fun u => ask u (emb z)) j0) := by
          funext v
          have hk : (⟨i.val, hilt⟩ : Fin t) = k := Fin.ext rfl
          simp only [emb, ↓reduceIte, hilt, ↓reduceDIte, hk, hzk, hc]
        exact hvalid (emb z) j0 i hEq
      have hmem_S0 : report (fun u => ask u (emb z)) j0 ∈ S0 :=
        (Finset.mem_insert.mp hmem_ins).resolve_left hne_cstar
      exact (Finset.mem_filter.mp (hS0_sub hmem_S0)).2
  by_contra hlt_b
  have hbt : b < t := by omega
  have hlhs :
      ∑ z : Fin t → Bool, z2OfBool (parity (fun u => ask u (emb z))) = (1 : ZMod 2) := by
    have h1 : ∀ z : Fin t → Bool,
        z2OfBool (parity (fun u => ask u (emb z))) =
        z2OfBool (if z = (fun _ => false) then !bmaj else bmaj) := by
      intro z
      rw [hF_ask (emb z), hphi_emb z]
    simp_rw [h1]
    exact cube_sum_mod2_const_flip ht_pos bmaj
  have hrhs :
      ∑ z : Fin t → Bool, z2OfBool (parity (fun u => ask u (emb z))) = (0 : ZMod 2) := by
    have hpar_sum : ∀ z : Fin t → Bool,
        z2OfBool (parity (fun u => ask u (emb z))) =
        ∑ mon ∈ terms, ∏ v ∈ mon, z2OfBool (emb z v) := by
      intro z
      have hev := hterms_eval (emb z)
      change z2OfBool (((mask.filter (fun bitId => ask bitId (emb z) = true)).card % 2) == 1) = _
      rw [hev, ← z2_nat_eq_mod2]
      have h1 : ∀ mon ∈ terms,
          ∏ v ∈ mon, z2OfBool (emb z v) =
          if ∀ v ∈ mon, emb z v = true then (1 : ZMod 2) else 0 := by
        intro mon _
        split_ifs with hall
        · refine Finset.prod_eq_one fun v hv => by
            have hxv := hall v hv
            simp [z2OfBool, hxv]
        · push Not at hall
          rcases hall with ⟨v, hv, hxv⟩
          have hxf : emb z v = false := by cases hx : emb z v <;> simp_all
          exact Finset.prod_eq_zero hv (by simp [z2OfBool, hxf])
      rw [Finset.sum_congr rfl h1, Finset.sum_boole]
    simp_rw [hpar_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun mon hmon => ?_
    have hmc : mon.card < t := lt_of_le_of_lt (hterms_deg mon hmon) hbt
    let touched : Finset (Fin t) :=
      (Finset.univ : Finset (Fin t)).filter (fun k => ∃ v ∈ mon, v.1 = j0 ∧ v.2.1.val = k.val)
    have htouch_le : touched.card ≤ mon.card := by
      let proj : Fin t → V := fun k =>
        if hk : ∃ v ∈ mon, v.1 = j0 ∧ v.2.1.val = k.val then Classical.choose hk
        else (j0, ⟨0, by omega⟩, ⟨0, ha⟩)
      refine Finset.card_le_card_of_injOn proj ?_ ?_
      · intro k hk
        have hex := (Finset.mem_filter.mp hk).2
        simp only [proj, hex, ↓reduceDIte]
        exact (Classical.choose_spec hex).1
      · intro k₁ hk₁ k₂ hk₂ hEq
        have hex₁ := (Finset.mem_filter.mp hk₁).2
        have hex₂ := (Finset.mem_filter.mp hk₂).2
        simp only [proj, hex₁, hex₂, ↓reduceDIte] at hEq
        have hv₁ := (Classical.choose_spec hex₁).2.2
        have hv₂ := (Classical.choose_spec hex₂).2.2
        rw [hEq] at hv₁
        exact Fin.ext (hv₁.symm.trans hv₂)
    have hex_untouched : ∃ k0 : Fin t, k0 ∉ touched := by
      by_contra hall
      push Not at hall
      have hsub : (Finset.univ : Finset (Fin t)) ⊆ touched := fun k _ => hall k
      have hle := Finset.card_le_card hsub
      simp only [Finset.card_univ, Fintype.card_fin] at hle
      omega
    rcases hex_untouched with ⟨k0, hk0⟩
    refine cube_sum_mod2_indep k0 (fun z => ∏ v ∈ mon, z2OfBool (emb z v)) ?_
    intro z
    refine Finset.prod_congr rfl fun v hv => ?_
    have hveq : emb (Function.update z k0 (!z k0)) v = emb z v := by
      rcases v with ⟨j, i, bit⟩
      by_cases hj : j = j0
      · rw [hj]
        by_cases hi : i.val < t
        · have hne_k0 : (⟨i.val, hi⟩ : Fin t) ≠ k0 := by
            intro hkeq
            apply hk0
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ k0, ⟨(j, i, bit), hv, hj, ?_⟩⟩
            exact congr_arg Fin.val hkeq
          simp only [emb, ↓reduceIte, hi, ↓reduceDIte, Function.update, hne_k0]
        · simp only [emb, ↓reduceIte, hi, ↓reduceDIte]
      · simp only [emb, hj, ↓reduceIte]
    rw [hveq]
  rw [hlhs] at hrhs
  exact absurd hrhs (by decide)

end PEqualNP.Outside.L_lib_752_aux

open PEqualNP.Outside.L_lib_752_aux in
theorem PEqualNP.Outside.L_lib_752 : (∀ (g a : Nat), 0 < g → 0 < a →
  let M := 2^a
  let m := M-1
  let d := g*a
  let V := Fin g × Fin m × Fin a
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → Fin M
  let valid := fun (x : W) (choice : Y) =>
    ∀ j i, ∃ v : Fin a, x (j,i,v) ≠ (choice j).val.testBit v.val
  let run := fun (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range d).foldl (fun h pos => h + ((ask pos h x).toNat <<< pos)) 0
  (∃ (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
    (∀ (u : Fin d) (h : Nat),
      deg ((u.val % a+1)*2^(a-1-u.val % a)) (choose u.val h)) ∧
    ∀ input, valid input (decode (run choose input))) ∧
  (∀ (n : Nat) (choose : Nat → Nat → W → Bool) (decode : Nat → Y),
    (∀ input, valid input (decode ((List.range n).foldl (fun trace tick =>
      trace + ((choose tick trace input).toNat <<< tick)) 0))) → d ≤ n) ∧
  ∀ (ask : Fin d → W → Bool) (report : (Fin d → Bool) → Y)
    (label : Fin g → Fin m → Fin M → Fin a → Bool),
    (∀ x j i, (fun rawBit => x (j,i,rawBit)) ≠ label j i (report (fun u => ask u x) j)) →
    ∀ (mask : Finset (Fin d)), mask.Nonempty → ∀ b : Nat,
      deg b (fun word => (((mask.filter (fun bitId => ask bitId word = true)).card % 2) == 1)) →
      2^(a-1) ≤ b) := by
  intro g a hg ha M m d V W deg Y valid run
  refine ⟨part1_adaptive hg ha, ?_, ?_⟩
  · intro n choose decode hvalid
    exact part2_min_length choose decode hvalid
  · intro ask report label hvalid mask hmask b ⟨terms, hdeg, heval⟩
    exact part3_degree_lower hg ha ask report label hvalid mask hmask b terms hdeg heval
