import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_435


namespace PEqualNP.Outside.L_meta_29717_aux

-- Adapted from lean/PEqualNP/Outside/L_meta_25908.lean at aa09e431801306f5bbb1bf3ef922df30f6b0d8f3.
private def z2OfBool (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma z2OfBool_inj {a b : Bool} (h : z2OfBool a = z2OfBool b) : a = b := by
  cases a <;> cases b <;> simp [z2OfBool] at h <;> rfl

private lemma z2OfBool_xor (a b : Bool) : z2OfBool (xor a b) = z2OfBool a + z2OfBool b := by
  cases a <;> cases b <;> decide

private lemma z2OfBool_and (a b : Bool) : z2OfBool (a && b) = z2OfBool a * z2OfBool b := by
  cases a <;> cases b <;> decide


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


private lemma parity_leaf_dvd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {d path : ℕ} (hp : path < 2 ^ d)
    (ask : ℕ → ℕ → (ι → ZMod 2) → Bool)
    (lin : ℕ → ℕ → (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : ℕ → ℕ → ZMod 2)
    (ha : ∀ t h x, z2OfBool (ask t h x) = lin t h x + c t h) :
    2 ^ (Fintype.card ι - d) ∣
      (Finset.univ.filter (fun x => stepRun ask x d = path)).card := by
  classical
  let L : (ι → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2) :=
    LinearMap.pi fun t => lin t.val (path % 2 ^ t.val)
  let goal : Fin d → ZMod 2 :=
    fun t => z2OfBool (path.testBit t.val) - c t.val (path % 2 ^ t.val)
  have hleaf (x : ι → ZMod 2) : stepRun ask x d = path ↔ L x = goal := by
    rw [stepRun_eq_iff ask x d path hp]
    constructor
    · intro h
      funext t
      change lin t.val (path % 2 ^ t.val) x = _
      rw [eq_sub_iff_add_eq, ← ha, h t]
    · intro h t
      apply z2OfBool_inj
      rw [ha, ← eq_sub_iff_add_eq]
      exact congrFun h t
  by_cases hex : ∃ x, L x = goal
  · obtain ⟨x, hx⟩ := hex
    let S := Finset.univ.filter (fun y => stepRun ask y d = path)
    let e : ↥S ≃ LinearMap.ker L :=
      { toFun := fun y => ⟨y.val - x, by
          have hy := (hleaf y.val).1 (Finset.mem_filter.mp y.property).2
          simp [LinearMap.mem_ker, map_sub, hy, hx]⟩
        invFun := fun z => ⟨z.val + x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hleaf _).2 (by
          have hz := LinearMap.mem_ker.mp z.property
          simp [map_add, hz, hx])⟩⟩
        left_inv := fun y => Subtype.ext (sub_add_cancel _ _)
        right_inv := fun z => Subtype.ext (add_sub_cancel_right _ _) }
    have hrank := L.finrank_range_add_finrank_ker
    have hrange : Module.finrank (ZMod 2) L.range ≤ d := by
      simpa using Submodule.finrank_le L.range
    have hker : Fintype.card ι - d ≤ Module.finrank (ZMod 2) L.ker := by
      rw [Module.finrank_pi] at hrank
      omega
    change 2 ^ (Fintype.card ι - d) ∣ S.card
    rw [← Fintype.card_coe, Fintype.card_congr e,
      Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥L.ker)]
    simpa using pow_dvd_pow (2 : ℕ) hker
  · have hEmpty : (Finset.univ.filter (fun x => stepRun ask x d = path)) = ∅ := by
      ext x
      simpa [hleaf] using (fun hx => hex ⟨x, hx⟩ : ¬ L x = goal)
    rw [hEmpty, Finset.card_empty]
    exact dvd_zero _

private lemma parity_value_dvd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {T : Type*} [DecidableEq T] (d : ℕ)
    (ask : ℕ → ℕ → (ι → ZMod 2) → Bool)
    (lin : ℕ → ℕ → (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (c : ℕ → ℕ → ZMod 2)
    (ha : ∀ t h x, z2OfBool (ask t h x) = lin t h x + c t h)
    (decode : ℕ → T) (y : T) :
    2 ^ (Fintype.card ι - d) ∣
      (Finset.univ.filter (fun x => decode (stepRun ask x d) = y)).card := by
  classical
  let paths := (Finset.range (2 ^ d)).filter (fun p => decode p = y)
  let leaf := fun p => Finset.univ.filter (fun x => stepRun ask x d = p)
  have hUnion : (Finset.univ.filter (fun x => decode (stepRun ask x d) = y)) =
      paths.biUnion leaf := by
    ext x
    simp only [paths, leaf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range]
    constructor
    · intro hx
      exact ⟨_, ⟨stepRun_lt ask x d, hx⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact hp.2
  rw [hUnion, Finset.card_biUnion]
  · exact Finset.dvd_sum fun p hp =>
      parity_leaf_dvd (Finset.mem_range.mp (Finset.mem_filter.mp hp).1) ask lin c ha
  · intro p _ q _ hpq
    change Disjoint (leaf p) (leaf q)
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact hpq ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hx').2)

private def boolOfZ2 (x : ZMod 2) : Bool := decide (x ≠ 0)

private lemma z2_boolOf (x : ZMod 2) : z2OfBool (boolOfZ2 x) = x := by
  fin_cases x
  · change z2OfBool (boolOfZ2 (0 : ZMod 2)) = 0
    decide
  · change z2OfBool (boolOfZ2 (1 : ZMod 2)) = 1
    decide

private noncomputable def restrictedKey {ι : Type*} {k : ℕ}
    (idx : ι ↪ Fin k) (ref : Fin (2 ^ k)) (x : ι → ZMod 2) : Fin (2 ^ k) := by
  classical
  exact wordOf k fun q =>
    if h : ∃ i, idx i = q then
      xor (ref.val.testBit q.val) (boolOfZ2 (x (Classical.choose h)))
    else ref.val.testBit q.val

private lemma restrictedKey_idx {ι : Type*} {k : ℕ}
    (idx : ι ↪ Fin k) (ref : Fin (2 ^ k)) (x : ι → ZMod 2) (i : ι) :
    (restrictedKey idx ref x).val.testBit (idx i).val =
      xor (ref.val.testBit (idx i).val) (boolOfZ2 (x i)) := by
  classical
  simp only [restrictedKey, testBit_wordOf]
  have h : ∃ j, idx j = idx i := ⟨i, rfl⟩
  simp only [h, ↓reduceDIte, idx.injective (Classical.choose_spec h)]

private lemma restrictedKey_outside {ι : Type*} {k : ℕ}
    (idx : ι ↪ Fin k) (ref : Fin (2 ^ k)) (x : ι → ZMod 2) (q : Fin k)
    (h : ¬ ∃ j, idx j = q) :
    (restrictedKey idx ref x).val.testBit q.val = ref.val.testBit q.val := by
  classical
  simp [restrictedKey, testBit_wordOf, h]

private def keyJoin {k : ℕ} (ref left right : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨(left.val ^^^ right.val ^^^ ref.val) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

private lemma keyJoin_bit {k : ℕ} (ref left right : Fin (2 ^ k)) (q : Fin k) :
    (keyJoin ref left right).val.testBit q.val =
      xor (xor (left.val.testBit q.val) (right.val.testBit q.val)) (ref.val.testBit q.val) := by
  simp [keyJoin, Nat.testBit_mod_two_pow, q.isLt, Nat.testBit_xor]

private lemma keyJoin_restricted {ι : Type*} {k : ℕ}
    (idx : ι ↪ Fin k) (ref : Fin (2 ^ k)) (x y : ι → ZMod 2) :
    keyJoin ref (restrictedKey idx ref x) (restrictedKey idx ref y) =
      restrictedKey idx ref (x + y) := by
  classical
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro p
  by_cases hp : p < k
  · let q : Fin k := ⟨p, hp⟩
    change (keyJoin _ _ _).val.testBit q.val = (restrictedKey _ _ _).val.testBit q.val
    rw [keyJoin_bit]
    by_cases hh : ∃ i, idx i = q
    · obtain ⟨i, hi⟩ := hh
      rw [← hi]
      simp only [restrictedKey_idx]
      apply z2OfBool_inj
      simp only [z2OfBool_xor, z2_boolOf, Pi.add_apply]
      have hzero (a : ZMod 2) : a + a = 0 := by fin_cases a <;> decide
      convert congrArg (fun t => t + (x i + y i) + z2OfBool (ref.val.testBit (idx i).val))
        (hzero (z2OfBool (ref.val.testBit (idx i).val))) using 1 <;> ring
    · simp only [restrictedKey_outside idx ref _ q hh]
      have hh' (b : Bool) : xor (xor b b) b = b := by cases b <;> rfl
      exact hh' _
  · have hpow : 2 ^ k ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (keyJoin _ _ _).isLt hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (restrictedKey _ _ _).isLt hpow)]

private def parityAns {k : ℕ} (mask : Fin k → Bool) (key : Fin (2 ^ k)) : Bool :=
  (∑ j : Fin k, (mask j && key.val.testBit j.val).toNat) % 2 == 1

private lemma z2_nat_eq_mod2 (n : ℕ) :
    (n : ZMod 2) = z2OfBool (n % 2 == 1) := by
  have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rw [← ZMod.natCast_mod n 2]
  rcases h with h | h <;> rw [h] <;> decide

private lemma z2_bool_toNat (a : Bool) : ((a.toNat : ℕ) : ZMod 2) = z2OfBool a := by
  cases a <;> decide

private lemma restricted_parity_affine {ι : Type*} {k : ℕ}
    (idx : ι ↪ Fin k) (ref : Fin (2 ^ k)) (mask : Fin k → Bool) :
    ∃ L : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∃ c : ZMod 2,
      ∀ x, z2OfBool (parityAns mask (restrictedKey idx ref x)) = L x + c := by
  classical
  let linearBit (j : Fin k) : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    if h : ∃ i, idx i = j then LinearMap.proj (Classical.choose h) else 0
  refine ⟨∑ j : Fin k, z2OfBool (mask j) • linearBit j,
    ∑ j : Fin k, z2OfBool (mask j) * z2OfBool (ref.val.testBit j.val), ?_⟩
  intro x
  have hbit (j : Fin k) :
      z2OfBool ((restrictedKey idx ref x).val.testBit j.val) =
        linearBit j x + z2OfBool (ref.val.testBit j.val) := by
    by_cases hp : ∃ i, idx i = j
    · obtain ⟨i, rfl⟩ := hp
      have hi : ∃ t, idx t = idx i := ⟨i, rfl⟩
      simp only [restrictedKey_idx, z2OfBool_xor, z2_boolOf, linearBit, hi, ↓reduceDIte,
        idx.injective (Classical.choose_spec hi), LinearMap.proj_apply]
      exact add_comm _ _
    · simp [linearBit, hp, restrictedKey_outside _ _ _ _ hp]
  unfold parityAns
  rw [← z2_nat_eq_mod2, Nat.cast_sum, LinearMap.sum_apply, ← Finset.sum_add_distrib]
  congr 1
  funext j
  simp only [z2_bool_toNat, z2OfBool_and, hbit, LinearMap.smul_apply, smul_eq_mul, mul_add]

private def keyBit {k : ℕ} (key : Fin (2 ^ k)) (q : Fin k) : Bool := key.val.testBit q.val

private def stateBit {k : ℕ} (constant : ℕ → Fin (2 ^ k))
    (row key : Fin (2 ^ k)) (n p : ℕ) : Bool :=
  (stateAt k constant row.val n key.val).testBit (p % k)

private def goodAt {k : ℕ} (constant : ℕ → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (p : ℕ) : Prop :=
  let old := fun j => stateBit constant row ref 0 (p+j)
  let first := fun j => stateBit constant row ref 1 (p+j)
  let τ := xor (xor (old 6) (old 7)) (old 8)
  let a := xor (xor (xor (old 5) (old 6)) (old 7))
    (xor ((rot k 0 ref.val).testBit ((p+6) % k)) ((constant 1).val.testBit ((p+6) % k)))
  let b := xor τ
    (xor ((rot k 0 ref.val).testBit ((p+7) % k)) ((constant 1).val.testBit ((p+7) % k)))
  τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
    xor (first 4) (first 5) = !a ∧ first 4 = b

private def samePins {k : ℕ} (constant : ℕ → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (pin : Finset (Fin k)) (key : Fin (2 ^ k)) : Prop :=
  ∀ z ∈ pin, stateBit constant row key 0 z.val = stateBit constant row ref 0 z.val

private def tripleOut (s l : Fin 3 → Bool) (c : Bool) (v : Fin 3 → Bool) : Bool :=
  xor ((xor (v 0) (s 0)) && (xor (v 1) (s 1)) && (xor (v 2) (s 2)))
    (xor (xor (xor c (l 0 && v 0)) (l 1 && v 1)) (l 2 && v 2))

private lemma guard_coordinates {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    (starts : Fin m → ℕ)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k))
    (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k))
    (hgood : ∀ i, goodAt constant row ref (starts i))
    (pin : Finset (Fin k))
    (hpin : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k)
    (hfree : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k) :
    ∃ (idx : Fin m × Fin 3 ↪ Fin k) (s l : Fin m → Fin 3 → Bool) (c : Fin m → Bool),
      (∀ x, samePins constant row ref pin (restrictedKey idx ref x)) ∧
      ∀ key, samePins constant row ref pin key → ∀ i,
        stateBit constant row key 2 (starts i + 5) =
          tripleOut (s i) (l i) (c i) (fun j => keyBit key (idx (i,j))) := by
  classical
  let all : Fin m × Fin 12 ↪ Fin k := ⟨fun z => ⟨_, Nat.mod_lt (starts z.1 + z.2.val) hk⟩,
    fun _ _ e => hinj (congrArg Fin.val e)⟩
  let sub : Fin 12 ↪ Fin m × Fin 12 :=
    ⟨fun j => (⟨0, hm⟩, j), fun _ _ e => congrArg Prod.snd e⟩
  have hk12 : 12 ≤ k := by simpa using Fintype.card_le_of_embedding (sub.trans all)
  let idx : Fin m × Fin 3 ↪ Fin k :=
    (⟨fun z => (z.1, ⟨8 + z.2.val, by omega⟩), by
      intro a b e
      have h₁ := congrArg Prod.fst e
      have h₂ := congrArg (fun p : Fin m × Fin 12 => p.2.val) e
      exact Prod.ext h₁ (Fin.ext (by dsimp at h₂; omega))⟩ :
      Fin m × Fin 3 ↪ Fin m × Fin 12).trans all
  have idx_val (i : Fin m) (j : Fin 3) : (idx (i,j)).val = (starts i + 8 + j.val) % k := by
    change (starts i + (8 + j.val)) % k = _
    rw [Nat.add_assoc]
  have hex (i : Fin m) : ∃ (s l : Fin 3 → Bool) (c : Bool),
      ∀ key, samePins constant row ref pin key →
        stateBit constant row key 2 (starts i + 5) =
          tripleOut s l c (fun j => keyBit key (idx (i,j))) := by
    obtain ⟨s0, s1, s2, c, l0, l1, l2, hf⟩ :=
      guarded_two_round_formula hk12 constant row ref (starts i) (hgood i)
    refine ⟨![s0,s1,s2], ![l0,l1,l2], c, fun key hkey => ?_⟩
    have hold (j : Fin 9) : stateBit constant row key 0 (starts i + j.val) =
        stateBit constant row ref 0 (starts i + j.val) := by
      obtain ⟨z, hz, hval⟩ := hpin i j
      have hh := hkey z hz
      simpa only [stateBit, Nat.mod_eq_of_lt z.isLt, hval, Nat.mod_mod] using hh
    simpa [stateBit, tripleOut, keyBit, idx_val, Nat.add_assoc] using hf key hold
  choose s l c hc using hex
  refine ⟨idx, s, l, c, ?_, fun key hkey i => hc i key hkey⟩
  intro x z hz
  let q : Fin k := ⟨(z.val + k - 1) % k, Nat.mod_lt _ hk⟩
  have hq : ¬ ∃ j, idx j = q := by
    rintro ⟨⟨i,j⟩, hj⟩
    have hv := congrArg Fin.val hj
    rw [idx_val] at hv
    change _ = (z.val + k - 1) % k at hv
    apply hfree i j z hz
    have ha : (z.val + k - 1 + 1) % k = z.val := by
      rw [show z.val + k - 1 + 1 = z.val + k by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]
    calc
      z.val = (z.val + k - 1 + 1) % k := ha.symm
      _ = ((z.val + k - 1) % k + 1) % k := (Nat.mod_add_mod ..).symm
      _ = ((starts i + 8 + j.val) % k + 1) % k := by rw [hv]
      _ = (starts i + 9 + j.val) % k := by rw [Nat.mod_add_mod]; congr 1; omega
  have hbit (key : Fin (2 ^ k)) :
      stateBit constant row key 0 z.val = xor (keyBit key q) (row.val.testBit z.val) := by
    unfold stateBit keyBit
    rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, Nat.testBit_xor, testBit_rot key.isLt z.isLt,
      Nat.mod_eq_of_lt (show 1 < k by omega)]
  rw [hbit, hbit]
  unfold keyBit
  rw [restrictedKey_outside _ _ _ _ hq]

private lemma syndrome_count {m r : ℕ}
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (f : Fin m → (Fin 3 → ZMod 2) → ZMod 2) :
    (Finset.univ.filter (fun x : Fin m → Fin 3 → ZMod 2 => A (fun i => f i (x i)) = 0)).card =
      ∑ z : Fin m → ZMod 2, if A z = 0 then
        ∏ i, if z i = 0 then (Finset.univ.filter (fun b => f i b = 0)).card
          else 8 - (Finset.univ.filter (fun b => f i b = 0)).card
      else 0 := by
  classical
  let block (i : Fin m) (v : ZMod 2) := (Finset.univ.filter (fun b => f i b = v)).card
  have hblock (i : Fin m) (v : ZMod 2) :
      block i v = if v = 0 then block i 0 else 8 - block i 0 := by
    by_cases h : v = 0
    · simp [h]
    · have hcases (t : ZMod 2) : t = 0 ∨ t = 1 := by
        fin_cases t
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hv : v = 1 := (hcases v).resolve_left h
      have heq (b : Fin 3 → ZMod 2) : f i b = v ↔ ¬ f i b = 0 := by
        rw [hv]
        rcases hcases (f i b) with ht | ht <;> rw [ht] <;> decide
      have hcard : Fintype.card (Fin 3 → ZMod 2) = 8 := by simp
      simp only [h, ↓reduceIte, block]
      simp_rw [heq]
      rw [← Fintype.card_subtype, Fintype.card_subtype_compl, Fintype.card_subtype, hcard]
  change _ = ∑ z : Fin m → ZMod 2, if A z = 0 then
    ∏ i, if z i = 0 then block i 0 else 8 - block i 0 else 0
  simp_rw [← hblock]
  let e : {x : Fin m → Fin 3 → ZMod 2 // A (fun i => f i (x i)) = 0} ≃
      (Σ z : {z : Fin m → ZMod 2 // A z = 0},
        ∀ i, {b : Fin 3 → ZMod 2 // f i b = z.val i}) :=
    { toFun := fun x => ⟨⟨fun i => f i (x.val i), x.property⟩, fun i => ⟨x.val i, rfl⟩⟩
      invFun := fun z => ⟨fun i => (z.2 i).val, by
        have h : (fun i => f i ((z.2 i).val)) = z.1.val := funext fun i => (z.2 i).property
        rw [h]; exact z.1.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := by
        rintro ⟨z,b⟩
        have eqv : (fun i => f i (b i).val) = z.val :=
          funext fun i => (b i).property
        apply Sigma.ext (Subtype.ext eqv)
        apply Function.hfunext rfl
        intro i j hij
        cases eq_of_heq hij
        apply (Subtype.heq_iff_coe_eq (fun x => by
          change f i x = f i (b i).val ↔ f i x = z.val i
          rw [(b i).property])).2
        rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [Fintype.card_pi, Fintype.card_subtype]
  rw [← Finset.sum_filter]
  symm
  exact Finset.sum_subtype (Finset.univ.filter (fun z : Fin m → ZMod 2 => A z = 0))
    (fun z => by simp) (fun z => ∏ i, block i (z i))



-- The upper bounds do not require the singleton decomposition: after two bits
-- are known, any Boolean function of the only remaining bit is affine over ZMod 2.
private def upperBlockSyndrome {m r : ℕ} (A : (Fin m → ZMod 2) →ₗ[ZMod 2] Fin r → ZMod 2)
    (block : Fin m → Bool → Bool → Bool → Bool) (x : Fin m × Fin 3 → Bool) : Fin r → ZMod 2 :=
  A (fun i => z2OfBool (block i (x (i, 0)) (x (i, 1)) (x (i, 2))))

private def upperParityValue {k : ℕ} (mask x : Fin k → Bool) : Bool :=
  (∑ j : Fin k, (mask j && x j).toNat) % 2 == 1

private lemma upperParityValue_single {k : ℕ} (p : Fin k) (x : Fin k → Bool) :
    upperParityValue (fun j => decide (j = p)) x = x p := by
  have hs : ∑ j : Fin k, (decide (j = p) && x j).toNat = (x p).toNat := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  cases hp : x p <;> simp [upperParityValue, hs, hp]

private lemma upperZ2_of_beq_one (a : ZMod 2) : z2OfBool (a == 1) = a := by
  fin_cases a
  · change z2OfBool ((0 : ZMod 2) == 1) = 0
    decide
  · change z2OfBool ((1 : ZMod 2) == 1) = 1
    decide

private lemma upperParityValue_z2 {k : ℕ} (mask x : Fin k → Bool) :
    z2OfBool (upperParityValue mask x) = ∑ j : Fin k, z2OfBool (mask j) * z2OfBool (x j) := by
  let n : ℕ := ∑ j : Fin k, (mask j && x j).toNat
  change z2OfBool (n % 2 == 1) = _
  have h : z2OfBool (n % 2 == 1) = ((n % 2 : ℕ) : ZMod 2) := by
    rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with hn | hn <;> simp [hn, z2OfBool]
  rw [h, ZMod.natCast_mod]
  simp only [n, Nat.cast_sum, ← z2OfBool_and]
  exact Finset.sum_congr rfl fun j _ => by cases (mask j && x j) <;> rfl

private def upperExtend {m k : ℕ} (e : Fin m ↪ Fin k)
    (c : Fin m → ZMod 2) (j : Fin k) : ZMod 2 :=
  ∑ i : Fin m, if e i = j then c i else 0

private lemma upperExtend_apply {m k : ℕ} (e : Fin m ↪ Fin k) (c : Fin m → ZMod 2) (i : Fin m) :
    upperExtend e c (e i) = c i := by
  rw [upperExtend, Finset.sum_eq_single i]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

private lemma upperExtend_sum {m k : ℕ} (e : Fin m ↪ Fin k) (c : Fin m → ZMod 2)
    (x : Fin k → Bool) :
    ∑ j : Fin k, upperExtend e c j * z2OfBool (x j) =
      ∑ i : Fin m, c i * z2OfBool (x (e i)) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by rw [upperExtend_apply]
  · intro j _ hj
    have h : ∀ i, e i ≠ j := fun i hi => hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)
    simp [upperExtend, h]

private lemma upperOneBit (f : Bool → Bool) (b : Bool) :
    z2OfBool (f b) = z2OfBool (f false) +
      z2OfBool b * (z2OfBool (f true) - z2OfBool (f false)) := by
  cases b <;> simp [z2OfBool]

private lemma constructiveParityUpper {K : Type*} {k m r depth : ℕ}
    (bits : K → Fin k → Bool) (idx : Fin m × Fin 3 ↪ Fin k)
    (block : Fin m → Bool → Bool → Bool → Bool)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] Fin r → ZMod 2) (hd : 2 * m + r ≤ depth) :
    ∃ (ask : ℕ → ℕ → Fin k → Bool) (decode : ℕ → Fin r → ZMod 2),
      ∀ key : K, decode (stepRun (fun t log x => upperParityValue (ask t log) (bits x)) key depth) =
        upperBlockSyndrome A block (fun p => bits key (idx p)) := by
  let slot : Fin m × Fin 2 ≃ Fin (2 * m) := finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))
  let coord (p : Fin m × Fin 2) : Fin k := idx (p.1, p.2.castLE (by omega))
  let third : Fin m ↪ Fin k := ⟨fun i => idx (i, 2), fun _ _ h => congrArg Prod.fst (idx.injective h)⟩
  let localFn (log : ℕ) (i : Fin m) : Bool → Bool :=
    block i (log.testBit (slot (i, 0)).val) (log.testBit (slot (i, 1)).val)
  let base (log : ℕ) (i : Fin m) : ZMod 2 := z2OfBool (localFn log i false)
  let delta (log : ℕ) (i : Fin m) : Fin m → ZMod 2 := fun j =>
    if j = i then z2OfBool (localFn log i true) - base log i else 0
  let ask (t log : ℕ) (j : Fin k) : Bool :=
    if ht : t < 2 * m then decide (j = coord (slot.symm ⟨t, ht⟩))
    else if hq : t - 2 * m < r then (upperExtend third (fun i => A (delta log i) ⟨t - 2 * m, hq⟩) j == 1)
    else false
  let decode (log : ℕ) (q : Fin r) : ZMod 2 :=
    A (base log) q + z2OfBool (log.testBit (2 * m + q.val))
  refine ⟨ask, decode, fun key => ?_⟩
  let run := stepRun (fun t log x => upperParityValue (ask t log) (bits x)) key
  have readPrefix (n : ℕ) (hn : 2 * m ≤ n) (p : Fin m × Fin 2) :
      (run n).testBit (slot p).val = bits key (coord p) := by
    have hp := (slot p).isLt
    change (stepRun _ key n).testBit (slot p).val = _
    rw [stepRun_testBit _ _ _ _ (hp.trans_le hn)]
    simpa only [ask, dite_eq_left hp, Fin.eta, Equiv.symm_apply_apply] using
      upperParityValue_single (coord p) (bits key)
  have readLocal (n : ℕ) (hn : 2 * m ≤ n) (i : Fin m) :
      localFn (run n) i = block i (bits key (idx (i, 0))) (bits key (idx (i, 1))) := by
    simp only [localFn, readPrefix n hn (i, 0), readPrefix n hn (i, 1)]
    rfl
  have coefficients (n : ℕ) (hn : 2 * m ≤ n) :
      (fun i => z2OfBool (block i (bits key (idx (i, 0))) (bits key (idx (i, 1))) (bits key (idx (i, 2))))) =
        base (run depth) + ∑ i : Fin m, z2OfBool (bits key (third i)) • delta (run n) i := by
    funext j
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp only [base, delta, ite_eq_left rfl, readLocal n hn, readLocal depth (by omega : 2 * m ≤ depth)]
      exact upperOneBit _ _
    · intro i _ hij
      simp [delta, Ne.symm hij]
    · simp
  funext q
  let t := 2 * m + q.val
  have ht : t < depth := by have := q.isLt; dsimp [t]; omega
  have htn : 2 * m ≤ t := Nat.le_add_right _ _
  have htq : t - 2 * m = q.val := by dsimp [t]; omega
  have hread : z2OfBool ((run depth).testBit t) =
      ∑ i : Fin m, A (delta (run t) i) q * z2OfBool (bits key (third i)) := by
    change z2OfBool ((stepRun _ key depth).testBit t) = _
    rw [stepRun_testBit _ _ _ _ ht]
    simp only [ask, dite_eq_right (not_lt_of_ge htn), htq, q.isLt, dite_eq_left, Fin.eta]
    rw [upperParityValue_z2]
    simp only [upperZ2_of_beq_one]
    exact upperExtend_sum _ _ _
  change A (base (run depth)) q + z2OfBool ((run depth).testBit t) =
    A (fun i => z2OfBool (block i (bits key (idx (i, 0))) (bits key (idx (i, 1))) (bits key (idx (i, 2))))) q
  rw [hread, coefficients t htn, map_add, map_sum]
  simp only [Pi.add_apply, Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

private lemma constructiveCommUpper {K : Type*} {k m r depth : ℕ}
    (bits : K → Fin k → Bool) (idx : Fin m × Fin 3 ↪ Fin k)
    (block : Fin m → Bool → Bool → Bool → Bool)
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] Fin r → ZMod 2) (ref : K) (join : K → K → K)
    (hjoin : ∀ left right j, bits (join left right) j = xor (xor (bits left j) (bits right j)) (bits ref j))
    (hd : 3 * m ≤ depth) :
    ∃ (alice : ℕ → ℕ → Bool) (speak : ℕ → ℕ → K → Bool) (decode : ℕ → K → Fin r → ZMod 2),
      ∀ left right : K,
        decode (stepRun (fun t log (p : K × K) =>
          speak t log (if alice t log then p.1 else p.2)) (left, right) depth) right =
          upperBlockSyndrome A block (fun p => bits (join left right) (idx p)) := by
  let slot : Fin m × Fin 3 ≃ Fin (3 * m) := finProdFinEquiv.trans (finCongr (Nat.mul_comm m 3))
  let speak (t : ℕ) (_log : ℕ) (key : K) : Bool :=
    if h : t < 3 * m then bits key (idx (slot.symm ⟨t, h⟩)) else false
  let decode (log : ℕ) (right : K) : Fin r → ZMod 2 := upperBlockSyndrome A block fun p =>
    xor (xor (log.testBit (slot p).val) (bits right (idx p))) (bits ref (idx p))
  refine ⟨fun _ _ => true, speak, decode, fun left right => ?_⟩
  change decode (stepRun speak left depth) right = _
  have hbit (p : Fin m × Fin 3) : (stepRun speak left depth).testBit (slot p).val = bits left (idx p) := by
    have hp := (slot p).isLt
    rw [stepRun_testBit _ _ _ _ (hp.trans_le hd)]
    simp only [speak, dite_eq_left hp, Fin.eta, Equiv.symm_apply_apply]
  have hx (p : Fin m × Fin 3) :
      xor (xor ((stepRun speak left depth).testBit (slot p).val) (bits right (idx p))) (bits ref (idx p)) =
        bits (join left right) (idx p) := by rw [hbit, hjoin]
  exact congrArg (upperBlockSyndrome A block) (funext hx)



open scoped BigOperators

namespace TripleWalsh

abbrev Block := Fin 3 → ZMod 2

abbrev Blocks (m : ℕ) := Fin m → Block

def sign (R : Type*) [Ring R] (u : ZMod 2) : R := if u = 0 then 1 else -1

theorem sign_add (R : Type*) [Ring R] (u v : ZMod 2) :
    sign R (u + v) = sign R u * sign R v := by
  have hbit (b : ZMod 2) : b = 0 ∨ b = 1 := by
    fin_cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rcases hbit u with rfl | rfl <;> rcases hbit v with rfl | rfl <;> simp [sign, h11]

private theorem sign_one (R : Type*) [Ring R] : sign R 1 = -1 := by
  simp [sign]

theorem sign_sum {ι R : Type*} [CommRing R] (s : Finset ι) (v : ι → ZMod 2) :
    sign R (∑ i ∈ s, v i) = ∏ i ∈ s, sign R (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert i s hi ih => simp [hi, ih, sign_add]

def dot (a x : Block) : ZMod 2 := ∑ j, a j * x j

def affineSingleton (a : Block) (c : ZMod 2) (p x : Block) : ZMod 2 :=
  c + dot a x + if x = p then 1 else 0

/-- Translating the inputs shifts the singleton and adjusts only the affine constant. -/
theorem affineSingleton_translate (a p t x : Block) (c : ZMod 2) :
    affineSingleton a c p (t + x) = affineSingleton a (c + dot a t) (p + t) x := by
  have h₂ (u : ZMod 2) : u + u = 0 := by fin_cases u <;> decide
  have ht : t + t = (0 : Block) := by
    funext j
    exact h₂ (t j)
  have hiff : t + x = p ↔ x = p + t := by
    constructor
    · intro h
      calc
        x = (t + x) + t := by rw [add_right_comm, ht, zero_add]
        _ = p + t := by rw [h]
    · intro h
      rw [h, add_left_comm, ht, add_zero]
  rw [affineSingleton, affineSingleton, if_congr hiff rfl rfl]
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_assoc]

private theorem bit_sum (R : Type*) [CommRing R] (a : ZMod 2) :
    (∑ x : ZMod 2, sign R (a * x)) = if a = 0 then 2 else 0 := by
  have hu : (Finset.univ : Finset (ZMod 2)) = {0, 1} := rfl
  rw [hu, Finset.sum_insert (by simp), Finset.sum_singleton]
  by_cases h : a = 0
  · simp [sign, h]
    ring
  · simp [sign, h]

/-- The singleton changes only one term, by minus twice its unperturbed sign. -/
theorem coeff_eq (R : Type*) [CommRing R] (a s p : Block) (c : ZMod 2) :
    (∑ x : Block, sign R (affineSingleton a c p x + dot s x)) =
      sign R c * (∏ j : Fin 3, if a j + s j = 0 then 2 else 0) -
        2 * sign R (c + dot a p + dot s p) := by
  classical
  let g (x : Block) := c + dot a x + dot s x
  have hpoint (x : Block) :
      sign R (affineSingleton a c p x + dot s x) =
        sign R (g x) - if x = p then 2 * sign R (g p) else 0 := by
    by_cases h : x = p
    · subst x
      simp only [affineSingleton, ite_true]
      rw [add_right_comm (c + dot a p) 1, ← show g p = c + dot a p + dot s p from rfl,
        sign_add, sign_one]
      ring
    · simp [affineSingleton, g, h]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  have hg (x : Block) : g x = c + ∑ j : Fin 3, (a j + s j) * x j := by
    simp only [g, dot, add_mul, Finset.sum_add_distrib, add_assoc]
  simp_rw [hg, sign_add, sign_sum]
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun j : Fin 3 =>
    fun u : ZMod 2 => sign R ((a j + s j) * u))]
  simp_rw [bit_sum]

private theorem coeff_values (R : Type*) [CommRing R] (a s p : Block) (c : ZMod 2) :
    let C := ∑ x : Block, sign R (affineSingleton a c p x + dot s x)
    C = 2 ∨ C = -2 ∨ C = 6 ∨ C = -6 := by
  rw [coeff_eq]
  by_cases h : ∀ j : Fin 3, a j + s j = 0
  · have hp : dot a p + dot s p = 0 := by
      unfold dot
      rw [← Finset.sum_add_distrib]
      simp_rw [← add_mul, h, zero_mul]
      simp
    rw [add_assoc, hp, add_zero]
    simp only [h, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases hc : c = 0 <;> norm_num [sign, hc]
  · push Not at h
    obtain ⟨j, hj⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj), mul_zero, zero_sub]
    by_cases hp : c + dot a p + dot s p = 0 <;> norm_num [sign, hp]

/-- An affine function on three bits with one value toggled takes each output an odd
number of times. -/
theorem count_odd (a p : Block) (c b : ZMod 2) :
    Odd ((Finset.univ.filter fun x : Block => affineSingleton a c p x = b).card) := by
  classical
  let C := (Finset.univ.filter fun x : Block => affineSingleton a c p x = b).card
  have hp (x : Block) :
      sign ℤ (affineSingleton a (c + b) p x + dot 0 x) =
        2 * (if affineSingleton a c p x = b then 1 else 0) - 1 := by
    have hz : dot 0 x = 0 := by simp [dot]
    rw [hz, add_zero]
    have ht : affineSingleton a (c + b) p x = affineSingleton a c p x + b := by
      unfold affineSingleton
      ac_rfl
    rw [ht]
    generalize affineSingleton a c p x = u
    fin_cases u <;> fin_cases b <;> decide
  have hs : (∑ x : Block, sign ℤ (affineSingleton a (c + b) p x + dot 0 x)) =
      2 * (C : ℤ) - 8 := by
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
    simp [C]
  have hv := coeff_values ℤ a 0 p (c + b)
  change (_ = 2 ∨ _ = -2 ∨ _ = 6 ∨ _ = -6) at hv
  rw [hs] at hv
  change Odd C
  rw [Nat.odd_iff]
  rcases hv with h | h | h | h <;> omega

/-- The coefficient of the sign of a sum of independent block outputs factors over blocks. -/
theorem factor (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → Block → ZMod 2)
    (s : Blocks m) :
    (∑ x : Blocks m, if (∑ i, dot (s i) (x i)) = 0 then
      sign R (∑ i, f i (x i)) else -sign R (∑ i, f i (x i))) =
        ∏ i, ∑ x : Block, sign R (f i x + dot (s i) x) := by
  classical
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [← sign_sum, Finset.sum_add_distrib, sign_add]
  by_cases h : (∑ i, dot (s i) (x i)) = 0 <;> simp [sign, h]

/-- Every Walsh coefficient of the sign of the sum of the triple outputs is nonzero. -/
theorem all_nonzero {m : ℕ} (a p s : Blocks m) (c : Fin m → ZMod 2) :
    (∑ x : Blocks m, if (∑ i, dot (s i) (x i)) = 0 then
      sign ℚ (∑ i, affineSingleton (a i) (c i) (p i) (x i)) else
      -sign ℚ (∑ i, affineSingleton (a i) (c i) (p i) (x i))) ≠ 0 := by
  rw [factor ℚ (fun i => affineSingleton (a i) (c i) (p i))]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have h := coeff_values ℚ (a i) (s i) (p i) (c i)
  rcases h with h | h | h | h <;> rw [h] <;> norm_num

def blockIndex (m : ℕ) : Fin m × Fin 3 ≃ Fin (3 * m) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm m 3))

def toBlocks (m : ℕ) : (Fin (3 * m) → ZMod 2) ≃ Blocks m :=
  (Equiv.arrowCongr (blockIndex m).symm (Equiv.refl _)).trans (Equiv.curry _ _ _)

theorem dot_toBlocks {m : ℕ} (s x : Fin (3 * m) → ZMod 2) :
    (∑ j, s j * x j) = ∑ i, dot (toBlocks m s i) (toBlocks m x i) := by
  rw [← Equiv.sum_comp (blockIndex m) (fun j => s j * x j), Fintype.sum_prod_type]
  rfl

theorem all_nonzero_flat {m : ℕ} (a p : Blocks m) (c : Fin m → ZMod 2)
    (s : Fin (3 * m) → ZMod 2) :
    let f := fun x : Fin (3 * m) → ZMod 2 =>
      sign ℚ (∑ i, affineSingleton (a i) (c i) (p i) (toBlocks m x i))
    (∑ x : Fin (3 * m) → ZMod 2, if (∑ j, s j * x j) = 0 then f x else -f x) ≠ 0 := by
  dsimp only
  simp_rw [dot_toBlocks]
  exact (Equiv.sum_comp (toBlocks m) _).trans_ne (all_nonzero a p (toBlocks m s) c)

end TripleWalsh


namespace SyndromeDivisibility

open scoped BigOperators Classical
open Finset

private abbrev Bits (m : ℕ) := Fin m → ZMod 2

noncomputable section Weighted

private def sign (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

private theorem sign_add (x y : ZMod 2) : sign (x + y) = sign x * sign y := by
  fin_cases x <;> fin_cases y <;> decide

private theorem prod_sign (s : Finset ι) (v : ι → ZMod 2) :
    (∏ i ∈ s, sign (v i)) = sign (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert i s hi ih => simp [hi, ih, sign_add]

private theorem sum_sign {m r : ℕ} (A : Bits m →ₗ[ZMod 2] Bits r)
    (s : Finset (Fin m)) :
    (∑ z : A.ker, sign (∑ i ∈ s, (z : Bits m) i)) =
      if (∀ z : A.ker, ∑ i ∈ s, (z : Bits m) i = 0) then (Fintype.card A.ker : ℤ) else 0 := by
  classical
  split_ifs with h
  · simp [h, sign]
  · obtain ⟨w, hw⟩ := not_forall.mp h
    -- Translation by a point with sign −1 negates the whole sum.
    let f : A.ker → ℤ := fun z => sign (∑ i ∈ s, (z : Bits m) i)
    have hshift (z : A.ker) : f (z + w) = -f z := by
      change sign (∑ i ∈ s, ((z : Bits m) i + (w : Bits m) i)) = -f z
      rw [Finset.sum_add_distrib, sign_add]
      simp only [sign, hw, ite_false, mul_neg, mul_one]
      rfl
    have hcancel : -(∑ z : A.ker, f z) = ∑ z : A.ker, f z := calc
      _ = ∑ z : A.ker, -f z := by rw [Finset.sum_neg_distrib]
      _ = ∑ z : A.ker, f (z + w) := by simp_rw [hshift]
      _ = _ := Equiv.sum_comp (Equiv.addRight w) f
    change (∑ z : A.ker, f z) = 0
    omega

private theorem card_ker {m r : ℕ} (A : Bits m →ₗ[ZMod 2] Bits r)
    (hA : Function.Surjective A) : Fintype.card A.ker = 2 ^ (m - r) := by
  have hfun (n : ℕ) : Module.finrank (ZMod 2) (Bits n) = n := by
    simp only [Bits, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hrange : Module.finrank (ZMod 2) A.range = r := by
    rw [LinearMap.range_eq_top.mpr hA, finrank_top]
    exact hfun r
  have hr : r + Module.finrank (ZMod 2) A.ker = m := calc
    _ = Module.finrank (ZMod 2) A.range + Module.finrank (ZMod 2) A.ker :=
      congrArg (· + _) hrange.symm
    _ = Module.finrank (ZMod 2) (Bits m) := A.finrank_range_add_finrank_ker
    _ = m := hfun m
  have hd : Module.finrank (ZMod 2) A.ker = m - r := by omega
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hd]

private theorem kernelWeightedCount_exact_two {m r : ℕ}
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (full : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hA : Function.Surjective A) (hfull : ∀ z, full (A z) = ∑ i, z i)
    (a : Fin m → ℕ) (haOdd : ∀ i, Odd (a i)) (haBound : ∀ i, a i ≤ 8) :
    let N := ∑ z : A.ker, ∏ i, if (z : Fin m → ZMod 2) i = 0 then a i else 8 - a i
    2 ^ (m - r) ∣ N ∧ ¬ 2 ^ (m - r + 1) ∣ N := by
  classical
  let N := ∑ z : A.ker, ∏ i, if (z : Bits m) i = 0 then a i else 8 - a i
  change 2 ^ (m - r) ∣ N ∧ ¬ 2 ^ (m - r + 1) ∣ N
  -- Each block weight is `4 + (a i - 4) * sign (z i)`.
  let d : Fin m → ℤ := fun i => (a i : ℤ) - 4
  let coeff : Finset (Fin m) → ℤ := fun s => (∏ i ∈ s, d i) * ∏ _i ∈ sᶜ, 4
  let trivial : Finset (Fin m) → Prop := fun s => ∀ z : A.ker, ∑ i ∈ s, (z : Bits m) i = 0
  let Q : ℤ := ∑ s : Finset (Fin m), if trivial s then coeff s else 0
  have hexpand (z : A.ker) :
      ((∏ i, if (z : Bits m) i = 0 then a i else 8 - a i : ℕ) : ℤ) =
        ∑ s : Finset (Fin m), coeff s * sign (∑ i ∈ s, (z : Bits m) i) := by
    rw [Nat.cast_prod]
    calc
      _ = ∏ i : Fin m, (d i * sign ((z : Bits m) i) + 4) := by
        apply Finset.prod_congr rfl
        intro i _
        by_cases hz : (z : Bits m) i = 0
        · simp only [hz, ite_true, sign, mul_one, d]
          ring
        · simp only [hz, ite_false, sign, Int.ofNat_sub (haBound i), d]
          ring
      _ = _ := by
        rw [Fintype.prod_add]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.prod_mul_distrib, prod_sign]
        unfold coeff
        ring
  have hcount : (N : ℤ) = (2 : ℤ) ^ (m - r) * Q := by
    unfold N
    rw [Nat.cast_sum]
    simp_rw [hexpand]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.mul_sum, sum_sign]
    change coeff s * (if trivial s then (Fintype.card A.ker : ℤ) else 0) = _
    rw [card_ker A hA]
    push_cast
    by_cases hs : trivial s <;> simp [hs, mul_comm]
  have htrivial : trivial univ := by
    intro z
    rw [← hfull, LinearMap.mem_ker.mp z.property, map_zero]
  -- The full subset has trivial sign on the kernel, and all other coefficients are even.
  have hQ : (Q : ZMod 2) = 1 := by
    unfold Q
    rw [Int.cast_sum, Finset.sum_eq_single univ]
    · rw [ite_eq_left htrivial]
      simp only [coeff, compl_univ, Finset.prod_empty, mul_one, Int.cast_prod]
      apply Finset.prod_eq_one
      intro i _
      simp [d, (haOdd i).natCast_zmod_two, show (4 : ZMod 2) = 0 by decide]
    · intro s _ hs
      by_cases ht : trivial s
      · have hne : sᶜ.Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          exact fun hn => hs (by simpa using congrArg (fun t : Finset (Fin m) => tᶜ) hn)
        simp [ht, coeff, Finset.prod_const, ne_of_gt (Finset.card_pos.mpr hne),
          show (4 : ZMod 2) = 0 by decide]
      · simp [ht]
    · simp
  constructor
  · have hdvd : (((2 : ℕ) ^ (m - r) : ℕ) : ℤ) ∣ (N : ℤ) :=
      ⟨Q, by simpa using hcount⟩
    exact Int.natCast_dvd_natCast.mp hdvd
  · intro h
    have hdvd : (2 : ℤ) ^ (m - r + 1) ∣ (N : ℤ) := by exact_mod_cast h
    rw [hcount, pow_succ] at hdvd
    have ht : (2 : ℤ) ∣ Q :=
      (mul_dvd_mul_iff_left (pow_ne_zero _ (by decide : (2 : ℤ) ≠ 0))).mp hdvd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd Q 2).mpr ht
    exact zero_ne_one (hz.symm.trans hQ)

/-- The weighted zero-syndrome count has exact two-adic exponent `m - r`. -/
theorem weightedCount_exact_two {m r : ℕ}
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (full : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hA : Function.Surjective A) (hfull : ∀ z, full (A z) = ∑ i, z i)
    (a : Fin m → ℕ) (haOdd : ∀ i, Odd (a i)) (haBound : ∀ i, a i ≤ 8) :
    let N := ∑ z : Fin m → ZMod 2, if A z = 0 then
      ∏ i, if z i = 0 then a i else 8 - a i
      else 0
    2 ^ (m - r) ∣ N ∧ ¬ 2 ^ (m - r + 1) ∣ N := by
  classical
  dsimp only
  rw [← Finset.sum_filter,
    Finset.sum_subtype (p := fun z => z ∈ A.ker) _ (fun z => by simp [LinearMap.mem_ker])]
  exact kernelWeightedCount_exact_two A full hA hfull a haOdd haBound

end Weighted

end SyndromeDivisibility


namespace CommLogRank

private def log (put : ℕ → ℕ → Bool → ℕ) (bits : ℕ → ℕ → Bool) (t : ℕ) : ℕ :=
  (List.range t).foldl (fun l j => put l j (bits j l)) 0

private theorem log_succ (put : ℕ → ℕ → Bool → ℕ) (bits : ℕ → ℕ → Bool) (t : ℕ) :
    log put bits (t + 1) = put (log put bits t) t (bits t (log put bits t)) := by
  simp [log, List.range_succ, List.foldl_append]

/-- A fixed-depth adaptive protocol with Bob-local decoding factors through one column per
bit transcript. The numeric log update need not be injective. -/
theorem rank_le {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℚ) (depth : ℕ) (put : ℕ → ℕ → Bool → ℕ)
    (alice : ℕ → ℕ → Bool) (speak : ℕ → ℕ → I → Bool) (decode : ℕ → I → ℚ)
    (h : ∀ x y, decode ((List.range depth).foldl (fun l j =>
      put l j (speak j l (if alice j l then x else y))) 0) y = M x y) :
    M.rank ≤ 2 ^ depth := by
  classical
  let T := Fin depth → Bool
  let play (x y : I) (j l : ℕ) := speak j l (if alice j l then x else y)
  let run (x y : I) := log put (play x y)
  let read (z : T) (j : ℕ) := if hj : j < depth then z ⟨j, hj⟩ else false
  let replay (z : T) := log put (fun j _ => read z j)
  let actual (x y : I) (j : Fin depth) := play x y j (run x y j)
  let L (z : T) (x : I) := ∀ j : Fin depth,
    alice j (replay z j) = true → speak j (replay z j) x = z j
  let R (z : T) (y : I) := ∀ j : Fin depth,
    alice j (replay z j) = false → speak j (replay z j) y = z j
  have replay_succ (z : T) (j : ℕ) (hj : j < depth) :
      replay z (j + 1) = put (replay z j) j (z ⟨j, hj⟩) := by
    simp [replay, log_succ, read, hj]
  have run_succ (x y : I) (j : ℕ) :
      run x y (j + 1) = put (run x y j) j (play x y j (run x y j)) :=
    log_succ _ _ _
  have replay_actual (x y : I) (k : ℕ) (hk : k ≤ depth) :
      replay (actual x y) k = run x y k := by
    induction k with
    | zero => rfl
    | succ j ih =>
      rw [replay_succ _ _ (by omega), run_succ, ih (by omega)]
  have rectangle (z : T) (x y : I) : L z x ∧ R z y ↔ z = actual x y := by
    constructor
    · rintro ⟨hL, hR⟩
      have step (j : Fin depth) : play x y j (replay z j) = z j := by
        cases e : alice j (replay z j) with
        | false => simpa [play, e] using hR j e
        | true => simpa [play, e] using hL j e
      have agree (k : ℕ) (hk : k ≤ depth) : replay z k = run x y k := by
        induction k with
        | zero => rfl
        | succ j ih =>
          have hj : j < depth := by omega
          rw [replay_succ _ _ hj, run_succ, ← ih (by omega)]
          exact congrArg (put (replay z j) j) (step ⟨j, hj⟩).symm
      funext j
      have hj := step j
      rw [agree j j.isLt.le] at hj
      exact hj.symm
    · rintro rfl
      constructor
      · intro j hj
        rw [replay_actual x y j j.isLt.le] at hj ⊢
        simp [actual, play, hj]
      · intro j hj
        rw [replay_actual x y j j.isLt.le] at hj ⊢
        simp [actual, play, hj]
  let A : Matrix I T ℚ := fun x z => if L z x then 1 else 0
  let B : Matrix T I ℚ := fun z y => if R z y then decode (replay z depth) y else 0
  -- Adapts the rectangle factorization in lean/PEqualNP/Outside/L_meta_230.lean
  -- at aa09e431801306f5bbb1bf3ef922df30f6b0d8f3.
  have hfactor : M = A * B := by
    ext x y
    rw [Matrix.mul_apply]
    calc
      M x y = decode (run x y depth) y := (h x y).symm
      _ = A x (actual x y) * B (actual x y) y := by
        obtain ⟨hL, hR⟩ := (rectangle (actual x y) x y).2 rfl
        simp [A, B, hL, hR, replay_actual x y depth le_rfl]
      _ = ∑ z, A x z * B z y := by
        symm
        apply Finset.sum_eq_single (actual x y)
        · intro z _ hz
          by_cases hL : L z x
          · have hR : ¬ R z y := fun hR => hz ((rectangle z x y).1 ⟨hL, hR⟩)
            simp [B, hR]
          · simp [A, hL]
        · simp
  rw [hfactor]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa [T] using A.rank_le_card_width)

/-- Full Walsh support forces at least `n` rounds, even when Bob retains his input
for local decoding. -/
theorem depth_ge_of_walsh (n depth : ℕ) (f : (Fin n → ZMod 2) → ℚ)
    (hwalsh : ∀ s : Fin n → ZMod 2, (∑ v : Fin n → ZMod 2,
      if ∑ i : Fin n, s i * v i = 0 then f v else -f v) ≠ 0)
    (put : ℕ → ℕ → Bool → ℕ) (alice : ℕ → ℕ → Bool)
    (speak : ℕ → ℕ → (Fin n → ZMod 2) → Bool)
    (decode : ℕ → (Fin n → ZMod 2) → ℚ)
    (h : ∀ x y, decode ((List.range depth).foldl (fun l j =>
      put l j (speak j l (if alice j l then x else y))) 0) y = f (x + y)) :
    n ≤ depth := by
  let X : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℚ := fun x y => f (x + y)
  have hfull : X.rank = 2 ^ n := by
    simpa [X, hwalsh, Fintype.card_fun] using PEqualNP.Outside.L_lib_435 n f
  have hb := rank_le X depth put alice speak decode h
  rw [hfull] at hb
  exact (pow_le_pow_iff_right₀ (show (1 : ℕ) < 2 by decide)).1 hb

end CommLogRank



private lemma samePins_join {k : ℕ} (hk : 0 < k) (constant : ℕ → Fin (2 ^ k))
    (row ref left right : Fin (2 ^ k)) (pin : Finset (Fin k))
    (hl : samePins constant row ref pin left) (hr : samePins constant row ref pin right) :
    samePins constant row ref pin (keyJoin ref left right) := by
  intro z hz
  let q : Fin k := ⟨(z.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩
  have hb (key : Fin (2 ^ k)) : stateBit constant row key 0 z.val =
      xor (keyBit key q) (row.val.testBit z.val) := by
    unfold stateBit keyBit
    rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, Nat.testBit_xor, testBit_rot key.isLt z.isLt]
  have hpin (key : Fin (2 ^ k)) (h : samePins constant row ref pin key) :
      keyBit key q = keyBit ref q := by
    have he := h z hz
    rw [hb, hb] at he
    simpa only [bool_xor_cancel] using congrArg (fun v => xor v (row.val.testBit z.val)) he
  rw [hb, hb]
  unfold keyBit
  rw [keyJoin_bit]
  change xor (xor (xor (keyBit left q) (keyBit right q)) (keyBit ref q)) _ =
    xor (keyBit ref q) _
  rw [hpin left hl, hpin right hr]
  exact congrArg (fun v => xor v (row.val.testBit z.val))
    ((by decide : ∀ v : Bool, xor (xor v v) v = v) _)

private lemma triple_affine (s l v : Fin 3 → Bool) (c : Bool) (x : TripleWalsh.Block) :
    z2OfBool (tripleOut s l c (fun j => xor (v j) (boolOfZ2 (x j)))) =
      TripleWalsh.affineSingleton (fun j => z2OfBool (l j))
        (z2OfBool c + TripleWalsh.dot (fun j => z2OfBool (l j)) (fun j => z2OfBool (v j)))
        (fun j => z2OfBool (!(s j)) + z2OfBool (v j)) x := by
  let w := fun j => xor (v j) (boolOfZ2 (x j))
  let p := fun j => z2OfBool (!(s j)) + z2OfBool (v j)
  have hb (j : Fin 3) : xor (w j) (s j) = true ↔ x j = p j := by
    have h : ∀ a b t : Bool, xor (xor a t) b = true ↔
        z2OfBool t = z2OfBool (!b) + z2OfBool a := by decide
    simpa only [w, p, z2_boolOf] using h (v j) (s j) (boolOfZ2 (x j))
  have hs : ((xor (w 0) (s 0)) && (xor (w 1) (s 1)) && (xor (w 2) (s 2))) = true ↔ x = p := by
    simp only [Bool.and_eq_true, hb]
    constructor
    · rintro ⟨⟨h0,h1⟩,h2⟩
      funext j
      fin_cases j <;> assumption
    · intro h
      subst x
      simp
  have hind : z2OfBool ((xor (w 0) (s 0)) && (xor (w 1) (s 1)) && (xor (w 2) (s 2))) =
      if x = p then 1 else 0 := by
    simp [z2OfBool, ← hs]
  change z2OfBool (tripleOut s l c w) = TripleWalsh.affineSingleton _ _ p x
  unfold tripleOut TripleWalsh.affineSingleton TripleWalsh.dot
  rw [z2OfBool_xor, hind]
  simp only [w, z2OfBool_xor, z2OfBool_and, z2_boolOf, Fin.sum_univ_three]
  ring

private lemma flat_syndrome_count {m r : ℕ}
    (A : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (f : Fin m → TripleWalsh.Block → ZMod 2) :
    (Finset.univ.filter (fun x : Fin (3 * m) → ZMod 2 =>
      A (fun i => f i (TripleWalsh.toBlocks m x i)) = 0)).card =
    (Finset.univ.filter (fun x : TripleWalsh.Blocks m => A (fun i => f i (x i)) = 0)).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact (TripleWalsh.toBlocks m).subtypeEquiv (fun _ => Iff.rfl)

end PEqualNP.Outside.L_meta_29717_aux


open PEqualNP.Outside.L_meta_29717_aux in
theorem PEqualNP.Outside.L_meta_29717 :
∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
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
  ∀ (r depth : Nat), 0 < r →
    let F := ZMod 2
    let R := Fin r → F
    let G := Fin m → F
    ∀ (A : G →ₗ[F] R) (full : R →ₗ[F] F), Function.Surjective A →
    (∀ z : G, full (A z) = ∑ i : Fin m, z i) →
    let K := Fin (2^k)
    let fiber := fun key : K =>
      ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val
    let target := fun key : K => A (fun i =>
      if bit row.val 2 key.val (starts i+5) then (1 : F) else 0)
    let put := fun (log t : Nat) (v : Bool) => log + (v.toNat <<< t)
    let run := fun (ask : Nat → Nat → Fin k → Bool) (key : K) =>
      (List.range depth).foldl (fun log t =>
        let value := (∑ j : Fin k, (ask t log j && key.val.testBit j.val).toNat) % 2 == 1
        put log t value) 0
    let computes := ∃ (ask : Nat → Nat → Fin k → Bool) (decode : Nat → R),
      ∀ key : K, fiber key → decode (run ask key) = target key
    let join := fun (left right : K) =>
      (⟨(left.val ^^^ right.val ^^^ ref.val) % 2^k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩ : K)
    let talk := fun (alice : Nat → Nat → Bool) (speak : Nat → Nat → K → Bool)
        (left right : K) =>
      (List.range depth).foldl (fun log t =>
        put log t (speak t log (if alice t log then left else right))) 0
    let protocol := ∃ (alice : Nat → Nat → Bool) (speak : Nat → Nat → K → Bool)
        (decode : Nat → K → R), ∀ left right : K, fiber left → fiber right →
      decode (talk alice speak left right) right = target (join left right)
    And (Iff computes (2*m+r ≤ depth)) (Iff protocol (3*m ≤ depth)) := by
  classical
  intro k hk constant
  dsimp only
  intro m starts hm hinj row ref hgood pin hpin hfree r depth _hr A full hA hfull
  obtain ⟨idx, s, l, c, hfiber, hout⟩ :=
    guard_coordinates hk hm starts hinj constant row ref hgood pin hpin hfree
  let block (i : Fin m) (a b d : Bool) := tripleOut (s i) (l i) (c i) ![a,b,d]
  let target (key : Fin (2 ^ k)) : Fin r → ZMod 2 :=
    A (fun i => z2OfBool (stateBit constant row key 2 (starts i + 5)))
  have htarget (key : Fin (2 ^ k)) (h : samePins constant row ref pin key) :
      target key = upperBlockSyndrome A block (fun p => keyBit key (idx p)) := by
    apply congrArg A
    funext i
    rw [hout key h i]
    congr 2
    funext j
    fin_cases j <;> rfl
  let flatIdx : Fin (3 * m) ↪ Fin k := (TripleWalsh.blockIndex m).symm.toEmbedding.trans idx
  let liftKey := restrictedKey flatIdx ref
  have hlift (x : Fin (3 * m) → ZMod 2) :
      liftKey x = restrictedKey idx ref (fun p => TripleWalsh.toBlocks m x p.1 p.2) := by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · let q : Fin k := ⟨j, hj⟩
      change (restrictedKey flatIdx ref x).val.testBit q.val =
        (restrictedKey idx ref _).val.testBit q.val
      by_cases hq : ∃ p, idx p = q
      · obtain ⟨p, hp⟩ := hq
        have hp' : flatIdx (TripleWalsh.blockIndex m p) = idx p := by simp [flatIdx]
        rw [← hp, ← hp', restrictedKey_idx, hp', restrictedKey_idx]
        rfl
      · have hq' : ¬∃ t, flatIdx t = q := by
          rintro ⟨t, ht⟩
          exact hq ⟨(TripleWalsh.blockIndex m).symm t, ht⟩
        rw [restrictedKey_outside _ _ _ _ hq', restrictedKey_outside _ _ _ _ hq]
    · have hpow : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (liftKey x).isLt hpow),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (restrictedKey _ _ _).isLt hpow)]
  have hLiftFiber (x : Fin (3 * m) → ZMod 2) : samePins constant row ref pin (liftKey x) := by
    rw [hlift]
    exact hfiber _
  let refBit (i : Fin m) (j : Fin 3) := keyBit ref (idx (i,j))
  let a : TripleWalsh.Blocks m := fun i j => z2OfBool (l i j)
  let p : TripleWalsh.Blocks m := fun i j => z2OfBool (!(s i j)) + z2OfBool (refBit i j)
  let b : Fin m → ZMod 2 := fun i => z2OfBool (c i) + TripleWalsh.dot (a i) (fun j => z2OfBool (refBit i j))
  let f := fun i => TripleWalsh.affineSingleton (a i) (b i) (p i)
  have hLiftTarget (x : Fin (3 * m) → ZMod 2) :
      target (liftKey x) = A (fun i => f i (TripleWalsh.toBlocks m x i)) := by
    apply congrArg A
    funext i
    rw [hout (liftKey x) (hLiftFiber x) i, hlift]
    simp only [keyBit, restrictedKey_idx]
    exact triple_affine (s i) (l i) (refBit i) (c i) _
  constructor
  · constructor
    · rintro ⟨ask, decode, hd⟩
      let q t log x := parityAns (ask t log) (liftKey x)
      have hAffine (t log : ℕ) := restricted_parity_affine flatIdx ref (ask t log)
      choose L C hLC using hAffine
      have hDvd := parity_value_dvd depth q L C hLC decode (0 : Fin r → ZMod 2)
      have hRun (x : Fin (3 * m) → ZMod 2) :
          decode (stepRun q x depth) = A (fun i => f i (TripleWalsh.toBlocks m x i)) :=
        (hd (liftKey x) (hLiftFiber x)).trans (hLiftTarget x)
      simp only [hRun, Fintype.card_fin] at hDvd
      rw [flat_syndrome_count, syndrome_count] at hDvd
      let count (i : Fin m) := (Finset.univ.filter (fun v => f i v = 0)).card
      have hOdd (i : Fin m) : Odd (count i) := TripleWalsh.count_odd _ _ _ _
      have hBound (i : Fin m) : count i ≤ 8 := by
        exact (Finset.card_filter_le _ _).trans (by decide)
      have notDvd := (SyndromeDivisibility.weightedCount_exact_two A full hA hfull count hOdd hBound).2
      have hmr : r ≤ m := by
        have hh := Fintype.card_le_of_surjective A hA
        simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at hh
        exact (pow_le_pow_iff_right₀ (show (1 : ℕ) < 2 by decide)).1 hh
      by_contra hn
      exact notDvd ((pow_dvd_pow (2 : ℕ) (show m - r + 1 ≤ 3 * m - depth by omega)).trans hDvd)
    · intro h
      obtain ⟨ask, decode, hd⟩ := constructiveParityUpper (fun key => keyBit key) idx block A h
      exact ⟨ask, decode, fun key hk' => (hd key).trans (htarget key hk').symm⟩
  · constructor
    · rintro ⟨alice, speak, decode, hd⟩
      let ff (x : Fin (3 * m) → ZMod 2) :=
        TripleWalsh.sign ℚ (∑ i, f i (TripleWalsh.toBlocks m x i))
      apply CommLogRank.depth_ge_of_walsh (3 * m) depth ff (TripleWalsh.all_nonzero_flat a p b)
        (fun log t v => log + (v.toNat <<< t)) alice (fun t log x => speak t log (liftKey x))
        (fun log y => TripleWalsh.sign ℚ (full (decode log (liftKey y))))
      intro x y
      have hh := hd (liftKey x) (liftKey y) (hLiftFiber x) (hLiftFiber y)
      have hj : keyJoin ref (liftKey x) (liftKey y) = liftKey (x + y) :=
        keyJoin_restricted flatIdx ref x y
      change decode _ (liftKey y) = target (keyJoin ref (liftKey x) (liftKey y)) at hh
      rw [hj, hLiftTarget] at hh
      unfold ff
      rw [← hfull]
      apply congrArg (fun z => TripleWalsh.sign ℚ (full z))
      convert hh using 3
      funext log t
      split <;> rfl
    · intro h
      obtain ⟨alice, speak, decode, hd⟩ :=
        constructiveCommUpper (fun key => keyBit key) idx block A ref (keyJoin ref) (keyJoin_bit ref) h
      exact ⟨alice, speak, decode, fun left right hl hr => (hd left right).trans
        (htarget _ (samePins_join hk constant row ref left right pin hl hr)).symm⟩
