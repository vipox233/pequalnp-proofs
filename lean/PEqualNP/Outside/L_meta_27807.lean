import Mathlib

namespace PEqualNP.Outside.L_meta_27807_aux

namespace LocalGuard

-- The bit-level round computation and word encoding below are copied from
-- lean/PEqualNP/Outside/L_meta_25908.lean at ffb37fe488688105b2922181213183aa8d2c05b3.
-- The subsequent bridges adapt that file's raw-pin and guarded formula arguments.

private def z2OfBool (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma z2OfBool_inj {a b : Bool} (h : z2OfBool a = z2OfBool b) : a = b := by
  cases a <;> cases b <;> simp [z2OfBool] at h <;> rfl

private lemma z2OfBool_xor (a b : Bool) : z2OfBool (xor a b) = z2OfBool a + z2OfBool b := by
  cases a <;> cases b <;> decide

private lemma z2OfBool_and (a b : Bool) : z2OfBool (a && b) = z2OfBool a * z2OfBool b := by
  cases a <;> cases b <;> decide

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

-- Shift the round-zero pin back through the one-cell rotation.
private def pinShift {k : ℕ} (hk : 0 < k) (z : Fin k) : Fin k :=
  ⟨(k + z.val - 1) % k, Nat.mod_lt _ hk⟩

private lemma pinShift_succ {k : ℕ} (hk : 0 < k) (z : Fin k) :
    ((pinShift hk z).val + 1) % k = z.val := by
  change (((k + z.val - 1) % k) + 1) % k = z.val
  rw [Nat.mod_add_mod]
  have h : k + z.val - 1 + 1 = z.val + k := by omega
  rw [h, Nat.add_mod_right, Nat.mod_eq_of_lt z.isLt]

private lemma pinShift_injective {k : ℕ} (hk : 0 < k) : Function.Injective (pinShift hk) := by
  intro a b h
  apply Fin.ext
  rw [← pinShift_succ hk a, ← pinShift_succ hk b, h]

private def rawPins {k : ℕ} (hk : 0 < k) (pin : Finset (Fin k)) : Finset (Fin k) :=
  pin.map ⟨pinShift hk, pinShift_injective hk⟩

private lemma rawPins_card {k : ℕ} (hk : 0 < k) (pin : Finset (Fin k)) :
    (rawPins hk pin).card = pin.card := by simp [rawPins]

private lemma roundZero_pin {k : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row key : Fin (2 ^ k)) (z : Fin k) :
    (stateAt k constant row.val 0 key.val).testBit (z.val % k) =
      xor (key.val.testBit (pinShift (by omega : 0 < k) z).val) (row.val.testBit z.val) := by
  rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, Nat.testBit_xor, testBit_rot key.isLt z.isLt]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.add_comm z.val k] <;> rfl

private lemma fiber_iff_raw {k : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (pin : Finset (Fin k)) :
    (∀ z ∈ pin, (stateAt k constant row.val 0 key.val).testBit (z.val % k) =
      (stateAt k constant row.val 0 ref.val).testBit (z.val % k)) ↔
    (∀ q ∈ rawPins (by omega : 0 < k) pin, key.val.testBit q.val = ref.val.testBit q.val) := by
  constructor
  · intro h q hq
    rcases Finset.mem_map.mp hq with ⟨z, hz, rfl⟩
    have hz' := h z hz
    rw [roundZero_pin hk constant row key, roundZero_pin hk constant row ref] at hz'
    have hc := congr_arg (fun b => xor b (row.val.testBit z.val)) hz'
    change key.val.testBit (pinShift (by omega : 0 < k) z).val =
      ref.val.testBit (pinShift (by omega : 0 < k) z).val
    simpa only [bool_xor_cancel] using hc
  · intro h z hz
    have hq : pinShift (by omega : 0 < k) z ∈ rawPins (by omega : 0 < k) pin :=
      Finset.mem_map.mpr ⟨z, hz, rfl⟩
    rw [roundZero_pin hk constant row key, roundZero_pin hk constant row ref, h _ hq]

private def blockIndex {k m : ℕ} (hk : 0 < k) (starts : Fin m → ℕ)
    (p : Fin m × Fin 3) : Fin k :=
  ⟨(starts p.1 + 8 + p.2.val) % k, Nat.mod_lt _ hk⟩

private lemma blockIndex_injective {k m : ℕ} (hk : 0 < k) (starts : Fin m → ℕ)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k)) :
    Function.Injective (blockIndex hk starts) := by
  intro p₁ p₂ hEq
  have hv : (starts p₁.1 + 8 + p₁.2.val) % k = (starts p₂.1 + 8 + p₂.2.val) % k :=
    congr_arg Fin.val hEq
  have hb₁ := p₁.2.isLt
  have hb₂ := p₂.2.isLt
  have h1 := hinj (a₁ := (p₁.1, ⟨8 + p₁.2.val, by omega⟩))
    (a₂ := (p₂.1, ⟨8 + p₂.2.val, by omega⟩)) (by simpa only [← Nat.add_assoc] using hv)
  simp only [Prod.mk.injEq, Fin.mk.injEq] at h1
  exact Prod.ext h1.1 (Fin.ext (by omega))

private lemma blockIndex_notMem_rawPins {k m : ℕ} (hk : 0 < k) (starts : Fin m → ℕ)
    (pin : Finset (Fin k))
    (hpin_out : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k)
    (p : Fin m × Fin 3) : blockIndex hk starts p ∉ rawPins hk pin := by
  intro hp
  rcases Finset.mem_map.mp hp with ⟨z, hz, hEq⟩
  have h1 : pinShift hk z = blockIndex hk starts p := hEq
  apply hpin_out p.1 p.2 z hz
  rw [← pinShift_succ hk z, h1]
  change (((starts p.1 + 8 + p.2.val) % k) + 1) % k = (starts p.1 + 9 + p.2.val) % k
  rw [Nat.mod_add_mod]
  congr 1
  omega

private lemma window_width {k m : ℕ} (hk : 0 < k) (hm : 1 ≤ m) (starts : Fin m → ℕ)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k)) :
    12 ≤ k := by
  let f : Fin m × Fin 12 → Fin k := fun z => ⟨(starts z.1 + z.2.val) % k, Nat.mod_lt _ hk⟩
  have hf : Function.Injective f := fun _ _ h => hinj (congr_arg Fin.val h)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  omega

private def roundBit {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (rounds : ℕ) (key : Fin (2 ^ k)) (pos : ℕ) : Bool :=
  (stateAt k constant row.val rounds key.val).testBit (pos % k)

private def goodAt {k : ℕ} (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (p : ℕ) : Prop :=
  let old := fun j : ℕ => roundBit constant row 0 ref (p + j)
  let first := fun j : ℕ => roundBit constant row 1 ref (p + j)
  let τ := xor (xor (old 6) (old 7)) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7))
    (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
  let β := xor τ
    (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
  τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
    xor (first 4) (first 5) = !α ∧ first 4 = β

private lemma guarded_block_formula {k m : ℕ} (hk : 12 ≤ k)
    (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (starts : Fin m → ℕ)
    (pin : Finset (Fin k)) (hpin_in : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k)
    (i : Fin m) (hgood : goodAt constant row ref (starts i)) :
    ∃ (s l : Fin 3 → Bool) (c : Bool), ∀ key : Fin (2 ^ k),
      (∀ q ∈ rawPins (by omega : 0 < k) pin, key.val.testBit q.val = ref.val.testBit q.val) →
      let u := fun j : Fin 3 => key.val.testBit (blockIndex (by omega : 0 < k) starts (i, j)).val
      roundBit constant row 2 key (starts i + 5) =
        xor ((xor (u 0) (s 0)) && (xor (u 1) (s 1)) && (xor (u 2) (s 2)))
          (xor (xor (xor c (l 0 && u 0)) (l 1 && u 1)) (l 2 && u 2)) := by
  rcases guarded_two_round_formula hk constant row ref (starts i) hgood with
    ⟨s0, s1, s2, c, l0, l1, l2, hf⟩
  refine ⟨![s0, s1, s2], ![l0, l1, l2], c, fun key hkey => ?_⟩
  have hold := (fiber_iff_raw (by omega) constant row ref key pin).mpr hkey
  have hh := hf key (fun j => by
    obtain ⟨z, hz, hzval⟩ := hpin_in i j
    have hz' := hold z hz
    rwa [Nat.mod_eq_of_lt z.isLt, hzval] at hz')
  simpa [roundBit, blockIndex] using hh

end LocalGuard

-- Transcript lemmas adapted from L_meta_25908.lean at ffb37fe488688105b2922181213183aa8d2c05b3.
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

private abbrev F := ZMod 2
private abbrev Vec (I : Type*) := I → F

private def asBool (x : F) : Bool := x == 1

private lemma boolRound (b : Bool) : asBool (z2OfBool b) = b := by cases b <;> decide

private lemma fieldRound (a : F) : z2OfBool (asBool a) = a := by fin_cases a <;> rfl

private lemma asBool_inj : Function.Injective asBool := fun x y h => by
  simpa only [fieldRound] using congrArg z2OfBool h

private lemma eq_of_ne_f (a b : F) (h : a ≠ b) : a = b + 1 := by
  fin_cases a <;> fin_cases b <;> first | exact (h rfl).elim | rfl

private def queryAnswer {I : Type*}
    (ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F)) (bias : ℕ → ℕ → F) :
    ℕ → ℕ → F × Vec I → Bool :=
  fun t p w => asBool (z2OfBool (ask t p).1 * w.1 + (ask t p).2 w.2 + bias t p)

private lemma matches_ref {I : Type*}
    (ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F)) (bias : ℕ → ℕ → F)
    (n : ℕ) (b b₀ : F) (x : Vec I) :
    let path := stepRun (queryAnswer ask bias) (b₀, 0) n
    stepRun (queryAnswer ask bias) (b, x) n = path ↔
      ∀ t : Fin n, let q := ask t (path % 2 ^ t.val)
        z2OfBool q.1 * (b - b₀) + q.2 x = 0 := by
  intro path
  let a := queryAnswer ask bias
  have hp : path < 2 ^ n := stepRun_lt a (b₀, 0) n
  have h₀ := (stepRun_eq_iff a (b₀, 0) n path hp).mp rfl
  rw [stepRun_eq_iff a (b, x) n path hp]
  simp_rw [← h₀]
  constructor <;> intro h t <;> specialize h t
  · have he := asBool_inj h
    change z2OfBool (ask t _).1 * b + (ask t _).2 x + bias t _ =
      z2OfBool (ask t _).1 * b₀ + (ask t _).2 0 + bias t _ at he
    simp only [map_zero, add_zero] at he
    calc
      _ = (z2OfBool (ask t (path % 2 ^ t.val)).1 * b + (ask t _).2 x + bias t _) -
          (z2OfBool (ask t _).1 * b₀ + bias t _) := by ring
      _ = 0 := by rw [he, sub_self]
  · apply congrArg asBool
    simp only [map_zero, add_zero]
    change z2OfBool (ask t _).1 * (b - b₀) + (ask t _).2 x = 0 at h
    rw [← sub_eq_zero]
    convert h using 1 <;> ring

private lemma nonzero_kernel {I J : Type*} [Fintype I] [Fintype J]
    (h : Fintype.card J < Fintype.card I) (A : Vec I →ₗ[F] Vec J) :
    ∃ x, x ≠ 0 ∧ A x = 0 := by
  classical
  have hc : Fintype.card (Vec J) < Fintype.card (Vec I) := by
    simp only [Vec, Fintype.card_fun, ZMod.card]
    exact Nat.pow_lt_pow_right (by decide) h
  have hn : ¬ Function.Injective A := fun ha =>
    (not_le_of_gt hc) (Fintype.card_le_of_injective A ha)
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hn
  exact ⟨x-y, sub_ne_zero.mpr hne, by rw [map_sub, hxy, sub_self]⟩

private lemma sum_vanishes {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Vec I →ₗ[F] Vec J) (g : Vec I → F) {v : Vec I}
    (hv : v ≠ 0) (hAv : A v = 0) (hg : ∀ x, g (x + v) = g x) :
    ∑ x ∈ (Finset.univ.filter fun x => A x = 0), g x = 0 := by
  classical
  apply Finset.sum_involution (fun x _ => x + v)
  · intro x _
    rw [hg, z2_add_self]
  · intro x _ _ he
    exact hv (add_left_cancel (he.trans (add_zero x).symm))
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hx', hAv]⟩
  · intro x _
    have hh : v + v = 0 := by funext i; exact z2_add_self (v i)
    rw [add_assoc, hh, add_zero]

private lemma sum_vanishes_small {I J K : Type*} [Fintype I] [DecidableEq I] [Fintype J] [Fintype K]
    (A : Vec I →ₗ[F] Vec J) (C : Vec I →ₗ[F] Vec K)
    (h : Fintype.card J + Fintype.card K < Fintype.card I)
    (g : Vec K → F) :
    ∑ x ∈ (Finset.univ.filter fun x => A x = 0), g (C x) = 0 := by
  let B : Vec I →ₗ[F] Vec (J ⊕ K) :=
    LinearMap.pi (Sum.elim (fun j => (LinearMap.proj j).comp A)
      (fun j => (LinearMap.proj j).comp C))
  obtain ⟨v, hv, hBv⟩ := nonzero_kernel (by simpa using h) B
  have hAv : A v = 0 := by
    funext j
    exact congrFun hBv (.inl j)
  have hCv : C v = 0 := by
    funext j
    exact congrFun hBv (.inr j)
  exact sum_vanishes A (g ∘ C) hv hAv (by intro x; simp [hCv])

private def correct {I : Type*}
    (n : ℕ) (f : Vec I → F) (ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F))
    (bias : ℕ → ℕ → F) (read : ℕ → Bool) : Prop :=
  (∀ b : F, read (stepRun (queryAnswer ask bias) (b, 0) n) = false) ∧
    ∀ x : Vec I, x ≠ 0 → read (stepRun (queryAnswer ask bias) (f x, x) n) = true

private lemma fixed_lower {I : Type*} [Fintype I] {n : ℕ} {f : Vec I → F}
    {ask : ℕ → Bool × (Vec I →ₗ[F] F)} {bias : ℕ → ℕ → F} {read : ℕ → Bool}
    (h : correct n f (fun t _ => ask t) bias read) : Fintype.card I ≤ n := by
  by_contra! hg
  let A : Vec I →ₗ[F] Vec (Fin n) := LinearMap.pi (fun t => (ask t).2)
  obtain ⟨x,hx,hAx⟩ := nonzero_kernel (by simpa using hg) A
  have hm := (matches_ref (fun t _ => ask t) bias n (f x) (f x) x).mpr
    (fun t => by simpa [A] using congrFun hAx t)
  have ht := h.2 x hx
  rw [hm, h.1] at ht
  contradiction

private lemma adaptive_lower {I M : Type*} [Fintype I] [DecidableEq I] [Fintype M]
    {n : ℕ} {f : Vec I → F}
    (L : Vec I →ₗ[F] F) (c : F)
    (C : M → Vec I →ₗ[F] Vec (Fin 3)) (shift : M → Vec (Fin 3))
    (hf : ∀ x, f x = L x + c + ∑ i, ∏ j, (C i x j + shift i j))
    {ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F)} {bias : ℕ → ℕ → F} {read : ℕ → Bool}
    (h : correct n f ask bias read) : Fintype.card I - 2 ≤ n := by
  classical
  by_contra! hg
  let b₀ := f 0
  let p := stepRun (queryAnswer ask bias) (b₀, 0) n
  let q := fun t : Fin n => ask t (p % 2 ^ t.val)
  have hno (x : Vec I) (hx : x ≠ 0)
      (hr : ∀ t : Fin n, z2OfBool (q t).1 * (f x - b₀) + (q t).2 x = 0) : False := by
    have hm := (matches_ref ask bias n (f x) b₀ x).mpr hr
    have ht := h.2 x hx
    rw [hm, h.1] at ht
    contradiction
  by_cases hm : ∃ r : Fin n, (q r).1 = true
  · obtain ⟨r, hr⟩ := hm
    let J := {t : Fin n // t ≠ r}
    let A : Vec I →ₗ[F] Vec J :=
      LinearMap.pi (fun t : J => (q t.val).2 + z2OfBool (q t.val).1 • (q r).2)
    have hJ : Fintype.card J = n - 1 := by
      simpa [J] using Fintype.card_subtype_compl (fun t : Fin n => t = r)
    have hsize : Fintype.card J + 3 < Fintype.card I := by
      have := r.isLt
      omega
    let S := Finset.univ.filter fun x : Vec I => A x = 0
    let B := L + (q r).2
    have hδ (x : Vec I) (hx : x ∈ S) :
        f x + (q r).2 x + b₀ + 1 = if x = 0 then 1 else 0 := by
      by_cases hzero : x = 0
      · subst x
        simp [b₀, z2_add_self]
      · have hd : f x ≠ b₀ + (q r).2 x := by
          intro he
          apply hno x hzero
          intro t
          rw [he, add_sub_cancel_left]
          by_cases htr : t = r
          · subst t
            simp [hr, z2OfBool, z2_add_self]
          · have hAt := congrFun (Finset.mem_filter.mp hx).2 (⟨t, htr⟩ : J)
            change (q t).2 x + z2OfBool (q t).1 * (q r).2 x = 0 at hAt
            rwa [add_comm]
        rw [eq_of_ne_f _ _ hd, if_neg hzero]
        calc
          _ = (b₀ + b₀) + ((q r).2 x + (q r).2 x) + ((1 : F) + 1) := by ring
          _ = 0 := by simp [z2_add_self]
    have hA (x : Vec I) :
        f x + (q r).2 x + b₀ + 1 =
          (B x + (c + b₀ + 1)) + ∑ i, ∏ j, (C i x j + shift i j) := by
      rw [hf]
      simp only [B, LinearMap.add_apply]
      ring
    have hBs : ∑ x ∈ S, (B x + (c + b₀ + 1)) = 0 := by
      let P : Vec I →ₗ[F] Vec Unit := LinearMap.pi (fun _ => B)
      exact sum_vanishes_small A P (by simpa using (show Fintype.card J + 1 < Fintype.card I from by omega))
        (fun w => w () + (c + b₀ + 1))
    have hCs (i : M) : ∑ x ∈ S, ∏ j, (C i x j + shift i j) = 0 :=
      sum_vanishes_small A (C i) (by simpa using hsize) (fun w => ∏ j, (w j + shift i j))
    have hsum : ∑ x ∈ S, (f x + (q r).2 x + b₀ + 1) = 0 := by
      simp_rw [hA]
      rw [Finset.sum_add_distrib, hBs, Finset.sum_comm]
      simp [hCs]
    have hOne : ∑ x ∈ S, (f x + (q r).2 x + b₀ + 1) = 1 := by
      calc
        _ = ∑ x ∈ S, if x = 0 then (1 : F) else 0 := Finset.sum_congr rfl hδ
        _ = 1 := by simp [S]
    exact one_ne_zero (hOne.symm.trans hsum)
  · have hq (t : Fin n) : (q t).1 = false := by
      cases ht : (q t).1
      · rfl
      · exact (hm ⟨t, ht⟩).elim
    let A : Vec I →ₗ[F] Vec (Fin n) := LinearMap.pi (fun t => (q t).2)
    obtain ⟨x,hx,hAx⟩ := nonzero_kernel (by simpa using (show n < Fintype.card I from by omega)) A
    refine hno x hx (fun t => ?_)
    simpa [A, hq t, z2OfBool] using congrFun hAx t

private lemma correct_of_no_collision {I : Type*}
    (n : ℕ) (f : Vec I → F) (ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F))
    (bias : ℕ → ℕ → F)
    (h : ∀ (x : Vec I), x ≠ 0 → ∀ b : F,
      stepRun (queryAnswer ask bias) (f x, x) n ≠ stepRun (queryAnswer ask bias) (b, 0) n) :
    ∃ read, correct n f ask bias read := by
  classical
  refine ⟨fun p => decide (∀ b : F, p ≠ stepRun (queryAnswer ask bias) (b, 0) n),
    ?_, ?_⟩
  · intro b
    exact decide_eq_false (fun hb => hb b rfl)
  · intro x hx
    exact decide_eq_true (h x hx)

private lemma fixed_upper {I : Type*} [Fintype I]
    (n : ℕ) (f : Vec I → F) (offset : (Vec I →ₗ[F] F) → F) (h : Fintype.card I ≤ n) :
    ∃ (ask : ℕ → Bool × (Vec I →ₗ[F] F)) (read : ℕ → Bool),
      correct n f (fun t _ => ask t) (fun t _ => offset (ask t).2) read := by
  classical
  let E := Fintype.equivFin I
  let ask (t : ℕ) : Bool × (Vec I →ₗ[F] F) :=
    (false, if ht : t < Fintype.card I then LinearMap.proj (E.symm ⟨t, ht⟩) else 0)
  refine ⟨ask, ?_⟩
  apply correct_of_no_collision
  intro x hx b he
  apply hx
  funext i
  have ht := (matches_ref (fun t _ => ask t) (fun t _ => offset (ask t).2) n (f x) b x).mp
    he (⟨(E i).val, lt_of_lt_of_le (E i).isLt h⟩ : Fin n)
  simpa [ask, (E i).isLt, z2OfBool] using ht

private lemma adaptive_upper_schedule {I J : Type*} [Fintype J]
    (n : ℕ) (f : Vec I → F) (offset : (Vec I →ₗ[F] F) → F)
    (L : Vec I →ₗ[F] F) (C : F → Vec I →ₗ[F] Vec J)
    (hn : Fintype.card J + 1 ≤ n)
    (h : ∀ x : Vec I, x ≠ 0 → C (f x + L x) x ≠ 0) :
    ∃ (ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F)) (read : ℕ → Bool),
      correct n f ask (fun t p => offset (ask t p).2) read := by
  classical
  let E := Fintype.equivFin J
  let ask (t p : ℕ) : Bool × (Vec I →ₗ[F] F) :=
    if t = 0 then (true, L) else
      (false, if ht : t - 1 < Fintype.card J then
        (LinearMap.proj (E.symm ⟨t - 1, ht⟩)).comp (C (z2OfBool (p.testBit 0) + offset L)) else 0)
  refine ⟨ask, ?_⟩
  apply correct_of_no_collision
  intro x hx b he
  let bias := fun t p => offset (ask t p).2
  let path := stepRun (queryAnswer ask bias) (b, 0) n
  have hpos : 0 < n := by omega
  have hr := (matches_ref ask bias n (f x) b x).mp he
  have hf := hr ⟨0, hpos⟩
  have hf' : f x - b + L x = 0 := by simpa [ask, z2OfBool] using hf
  have hb : f x + L x = b := by linear_combination hf'
  have hbit : z2OfBool (path.testBit 0) = b + offset L := by
    rw [stepRun_testBit _ _ n 0 hpos]
    simp only [queryAnswer, ask, bias, ↓reduceIte, show z2OfBool true = 1 from rfl,
      one_mul, map_zero, add_zero, fieldRound]
  apply h x hx
  rw [hb]
  funext j
  let t : ℕ := (E j).val + 1
  have ht : t < n := by have := (E j).isLt; dsimp [t]; omega
  have htn : t ≠ 0 := by simp [t]
  have htm : t - 1 = (E j).val := by simp [t]
  have hlt : t - 1 < Fintype.card J := by rw [htm]; exact (E j).isLt
  have hbit' : z2OfBool ((path % 2 ^ t).testBit 0) + offset L = b := by
    rw [Nat.testBit_mod_two_pow, decide_eq_true (Nat.pos_of_ne_zero htn), Bool.true_and,
      hbit, add_assoc, z2_add_self, add_zero]
  have hj := hr (⟨t, ht⟩ : Fin n)
  change z2OfBool (ask t (path % 2 ^ t)).1 * (f x - b) +
    (ask t (path % 2 ^ t)).2 x = 0 at hj
  have hrow : ask t (path % 2 ^ t) = (false, (LinearMap.proj j).comp (C b)) := by
    simp only [ask, ite_eq_right htn, dite_eq_left hlt, hbit']
    have hE : (⟨t - 1, hlt⟩ : Fin (Fintype.card J)) = E j := Fin.ext htm
    rw [hE, Equiv.symm_apply_apply]
  rw [hrow] at hj
  simpa [z2OfBool] using hj

private abbrev TwoTripleF := ZMod 2
private abbrev TwoTripleT := Fin 3 → TwoTripleF
private abbrev TwoTripleX := TwoTripleT × TwoTripleT

private def twoTripleG (a b : TwoTripleT) (p : TwoTripleX) : TwoTripleF :=
  (if p.1 = a then 1 else 0) + (if p.2 = b then 1 else 0)

private def twoTripleCenter (a : Bool) : TwoTripleT :=
  if a then (fun j => if j = 0 then 1 else 0) else 0

private def twoTripleFirst (i : Fin 3) : TwoTripleX →ₗ[TwoTripleF] TwoTripleF :=
  (LinearMap.proj i : TwoTripleT →ₗ[TwoTripleF] TwoTripleF).comp
    (LinearMap.fst TwoTripleF TwoTripleT TwoTripleT)

private def twoTripleSecond (i : Fin 3) : TwoTripleX →ₗ[TwoTripleF] TwoTripleF :=
  (LinearMap.proj i : TwoTripleT →ₗ[TwoTripleF] TwoTripleF).comp
    (LinearMap.snd TwoTripleF TwoTripleT TwoTripleT)

private def twoTripleRows (r s t : TwoTripleX →ₗ[TwoTripleF] TwoTripleF) :
    TwoTripleX →ₗ[TwoTripleF] TwoTripleT :=
  LinearMap.pi ((![r, s, t]) : Fin 3 → TwoTripleX →ₗ[TwoTripleF] TwoTripleF)

-- The rows in each arm give the common correction and the two kernel conditions.
private def twoTripleQueries (a b : Bool) :
    (TwoTripleX →ₗ[TwoTripleF] TwoTripleF) ×
      (TwoTripleX →ₗ[TwoTripleF] TwoTripleT) × (TwoTripleX →ₗ[TwoTripleF] TwoTripleT) :=
  let u := twoTripleFirst 0
  let v := twoTripleFirst 1
  let w := twoTripleFirst 2
  let x := twoTripleSecond 0
  let y := twoTripleSecond 1
  let z := twoTripleSecond 2
  match a, b with
  | false, false => (0, twoTripleRows (u + x) (v + y) (w + z), twoTripleRows x y z)
  | true, false  => (x, twoTripleRows u y z, twoTripleRows x (v + y) (w + z))
  | false, true  => (u, twoTripleRows v w x, twoTripleRows (u + x) y z)
  | true, true   => (v, twoTripleRows u v x, twoTripleRows (w + x) (v + y) z)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem twoTripleTable :
    ∀ (a b : Bool) (p : TwoTripleX),
      let q := twoTripleQueries a b
      let G := twoTripleG (twoTripleCenter a) (twoTripleCenter b)
      (p ≠ 0 → q.2.1 p = 0 → G p + q.1 p = G 0) ∧
      (p ≠ 0 → q.2.2 p = 0 → G p + q.1 p = G 0 + 1) := by
  decide

private theorem twoTripleBinary : ∀ x : TwoTripleF, x = 0 ∨ x = 1 := by decide

private theorem twoTripleAddSelf : ∀ x : TwoTripleF, x + x = 0 := by decide

-- First place a nonzero center coordinate at zero, then clear the other coordinates.
private def twoTripleChange (a : TwoTripleT) (e : Equiv.Perm (Fin 3)) :
    TwoTripleT →ₗ[TwoTripleF] TwoTripleT :=
  LinearMap.pi fun j =>
    (LinearMap.proj (e j) : TwoTripleT →ₗ[TwoTripleF] TwoTripleF) +
      (if j = 0 then 0 else a (e j)) •
        (LinearMap.proj (e 0) : TwoTripleT →ₗ[TwoTripleF] TwoTripleF)

private theorem twoTripleChange_apply (a : TwoTripleT) (e : Equiv.Perm (Fin 3))
    (p : TwoTripleT) (j : Fin 3) :
    twoTripleChange a e p j = p (e j) + (if j = 0 then 0 else a (e j)) * p (e 0) := rfl

private theorem twoTripleChange_injective (a : TwoTripleT) (e : Equiv.Perm (Fin 3)) :
    Function.Injective (twoTripleChange a e) := by
  intro p q h
  have h0 : p (e 0) = q (e 0) := by
    simpa only [twoTripleChange_apply, ite_true, zero_mul, add_zero] using
      congrFun h (0 : Fin 3)
  funext i
  obtain ⟨j, rfl⟩ := e.surjective i
  have hj := congrFun h j
  simp only [twoTripleChange_apply, h0] at hj
  exact add_right_cancel hj

private theorem twoTripleNormalize (a : TwoTripleT) :
    ∃ (c : Bool) (A : TwoTripleT →ₗ[TwoTripleF] TwoTripleT),
      Function.Injective A ∧ A a = twoTripleCenter c := by
  by_cases ha : a = 0
  · refine ⟨false, LinearMap.id, fun _ _ h => h, ?_⟩
    simp [ha, twoTripleCenter]
  · have hex : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    obtain ⟨i, hi⟩ := hex
    have h1 : a i = 1 := (twoTripleBinary (a i)).resolve_left hi
    let e := Equiv.swap (0 : Fin 3) i
    have h0 : a (e 0) = 1 := by simpa [e] using h1
    refine ⟨true, twoTripleChange a e, twoTripleChange_injective a e, ?_⟩
    funext j
    rw [twoTripleChange_apply, h0]
    by_cases hj : j = 0 <;> simp [twoTripleCenter, hj, h0, twoTripleAddSelf]

private theorem twoTripleCertificates (a b : TwoTripleT) :
    ∃ (L : TwoTripleX →ₗ[TwoTripleF] TwoTripleF) (C₀ C₁ : TwoTripleX →ₗ[TwoTripleF] TwoTripleT),
      (∀ p : TwoTripleX, p ≠ 0 → C₀ p = 0 → twoTripleG a b p + L p = twoTripleG a b 0) ∧
      (∀ p : TwoTripleX, p ≠ 0 → C₁ p = 0 → twoTripleG a b p + L p = twoTripleG a b 0 + 1) := by
  obtain ⟨ca, A, hA, ha⟩ := twoTripleNormalize a
  obtain ⟨cb, B, hB, hb⟩ := twoTripleNormalize b
  let P := A.prodMap B
  have hP : Function.Injective P := by
    intro p q h
    exact Prod.ext (hA (congrArg Prod.fst h)) (hB (congrArg Prod.snd h))
  have hPnz (p : TwoTripleX) (hp : p ≠ 0) : P p ≠ 0 :=
    fun h => hp (hP (h.trans P.map_zero.symm))
  have hG (p : TwoTripleX) :
      twoTripleG (twoTripleCenter ca) (twoTripleCenter cb) (P p) = twoTripleG a b p := by
    have ea : (P p).1 = twoTripleCenter ca ↔ p.1 = a := by
      change A p.1 = twoTripleCenter ca ↔ p.1 = a
      rw [← ha]
      exact hA.eq_iff
    have eb : (P p).2 = twoTripleCenter cb ↔ p.2 = b := by
      change B p.2 = twoTripleCenter cb ↔ p.2 = b
      rw [← hb]
      exact hB.eq_iff
    simp only [twoTripleG, ea, eb]
  have hG0 : twoTripleG (twoTripleCenter ca) (twoTripleCenter cb) 0 = twoTripleG a b 0 := by
    simpa only [map_zero] using hG 0
  let q := twoTripleQueries ca cb
  refine ⟨q.1.comp P, q.2.1.comp P, q.2.2.comp P, ?_, ?_⟩
  · intro p hp hc
    simpa only [hG, hG0, LinearMap.comp_apply] using
      (twoTripleTable ca cb (P p)).1 (hPnz p hp) hc
  · intro p hp hc
    simpa only [hG, hG0, LinearMap.comp_apply] using
      (twoTripleTable ca cb (P p)).2 (hPnz p hp) hc

private def blockProj {I M : Type*} (idx : M × Fin 3 → I) (i : M) :
    Vec I →ₗ[F] Vec (Fin 3) := LinearMap.pi fun j => LinearMap.proj (idx (i,j))

private lemma product_point (x s : Vec (Fin 3)) :
    (∏ j, (x j + s j)) = if x = (fun j => 1 + s j) then 1 else 0 := by
  classical
  split_ifs with he
  · subst x
    apply Finset.prod_eq_one
    intro j _
    rw [add_assoc, z2_add_self, add_zero]
  · have hex : ∃ j, x j ≠ 1 + s j := by
      by_contra! h
      exact he (funext h)
    obtain ⟨j,hj⟩ := hex
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hs := eq_of_ne_f _ _ hj
    rw [hs]
    calc
      _ = ((1 : F) + 1) + (s j + s j) := by ring
      _ = 0 := by simp [z2_add_self]

private lemma adaptive_upper_blocks {I M : Type*} [Fintype I] [Fintype M]
    (i₀ i₁ : M) (hi : i₀ ≠ i₁) (idx : M × Fin 3 → I) (hinj : Function.Injective idx)
    (n : ℕ) (f : Vec I → F) (offset : (Vec I →ₗ[F] F) → F)
    (L : Vec I →ₗ[F] F) (c : F) (shift : M → Vec (Fin 3))
    (hf : ∀ x, f x = L x + c + ∑ i, ∏ j, (x (idx (i,j)) + shift i j))
    (hn : Fintype.card I - 2 ≤ n) :
    ∃ (ask : ℕ → ℕ → Bool × (Vec I →ₗ[F] F)) (read : ℕ → Bool),
      correct n f ask (fun t p => offset (ask t p).2) read := by
  classical
  let ix : Bool × Fin 3 → I := fun q => idx ((if q.1 then i₁ else i₀), q.2)
  have hix : Function.Injective ix := by
    rintro ⟨a,j⟩ ⟨b,l⟩ he
    have h := hinj he
    have hj := congrArg Prod.snd h
    have hab := congrArg Prod.fst h
    have hbb : a = b := by
      cases a <;> cases b <;> simp_all [hi, Ne.symm hi]
    exact Prod.ext hbb hj
  let R := {z : I // z ∉ Set.range ix}
  have h6 : Fintype.card {z : I // z ∈ Set.range ix} = 6 := by
    exact (Fintype.card_congr (Equiv.ofInjective ix hix)).symm.trans (by decide)
  have hR : Fintype.card R = Fintype.card I - 6 := by
    rw [Fintype.card_subtype_compl, h6]
  have h6le : 6 ≤ Fintype.card I := by
    simpa using Fintype.card_le_of_injective ix hix
  let P := (blockProj idx i₀).prod (blockProj idx i₁)
  let Rest : Vec I →ₗ[F] Vec R := LinearMap.pi fun r : R => LinearMap.proj r.val
  let a := fun j => 1 + shift i₀ j
  let b := fun j => 1 + shift i₁ j
  obtain ⟨A,C₀,C₁,h₀,h₁⟩ := twoTripleCertificates a b
  let G := twoTripleG a b
  let U := L + A.comp P
  let C (v : F) : Vec I →ₗ[F] Vec (Fin 3 ⊕ R) :=
    LinearMap.pi (Sum.elim
      (fun j => (LinearMap.proj j).comp ((if v = f 0 then C₁ else C₀).comp P))
      (fun r => (LinearMap.proj r).comp Rest))
  apply adaptive_upper_schedule n f offset U C (by simp only [Fintype.card_sum, Fintype.card_fin, hR]; omega)
  intro x hx hC
  have hr (r : R) : x r.val = 0 := congrFun hC (.inr r)
  have hp : P x ≠ 0 := by
    intro he
    apply hx
    funext r
    by_cases hmem : r ∈ Set.range ix
    · obtain ⟨⟨v,j⟩,rfl⟩ := hmem
      cases v
      · exact congrFun (congrArg Prod.fst he) j
      · exact congrFun (congrArg Prod.snd he) j
    · exact hr ⟨r,hmem⟩
  have ho (i : M) (ha : i ≠ i₀) (hb : i ≠ i₁) (j : Fin 3) : x (idx (i,j)) = 0 := by
    apply hr ⟨idx (i,j), ?_⟩
    rintro ⟨⟨v,l⟩, he⟩
    have hh : (if v then i₁ else i₀) = i := congrArg Prod.fst (hinj he)
    cases v
    · exact ha hh.symm
    · exact hb hh.symm
  let T (y : Vec I) (i : M) := ∏ j, (y (idx (i,j)) + shift i j)
  have hs : ∑ i, (T x i - T 0 i) = (T x i₀ - T 0 i₀) + (T x i₁ - T 0 i₁) := by
    calc
      _ = ∑ i, ((if i = i₀ then T x i₀ - T 0 i₀ else 0) +
          (if i = i₁ then T x i₁ - T 0 i₁ else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases h0 : i = i₀
        · subst i
          simp [hi]
        by_cases h1 : i = i₁
        · subst i
          simp [Ne.symm hi]
        simp [h0, h1, T, ho i h0 h1]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hT (y : Vec I) : T y i₀ + T y i₁ = G (P y) := by
    change (∏ j, ((P y).1 j + shift i₀ j)) + (∏ j, ((P y).2 j + shift i₁ j)) = _
    rw [product_point, product_point]
    rfl
  have hcomp : f x + U x = f 0 + (G (P x) + A (P x) - G 0) := by
    have hf' (y : Vec I) : f y = L y + c + ∑ i, T y i := hf y
    rw [Finset.sum_sub_distrib] at hs
    have hv0 : P 0 = 0 := map_zero P
    have ht0 := hT 0
    rw [hv0] at ht0
    simp only [hf', U, LinearMap.add_apply, LinearMap.comp_apply, map_zero]
    rw [show L x + c + (∑ i, T x i) + (L x + A (P x)) =
      (L x + L x) + (c + (∑ i, T x i) + A (P x)) by ring, z2_add_self, zero_add]
    linear_combination hs + hT x - ht0
  by_cases hb : f x + U x = f 0
  · have hker : C₁ (P x) = 0 := by
      funext j
      simpa [C, hb] using congrFun hC (.inl j)
    have he := h₁ (P x) hp hker
    change G (P x) + A (P x) = G 0 + 1 at he
    rw [he, add_sub_cancel_left] at hcomp
    exact one_ne_zero (add_left_cancel (hcomp.symm.trans (hb.trans (add_zero (f 0)).symm)))
  · have hker : C₀ (P x) = 0 := by
      funext j
      simpa [C, hb] using congrFun hC (.inl j)
    have he := h₀ (P x) hp hker
    change G (P x) + A (P x) = G 0 at he
    exact hb (by rwa [he, sub_self, add_zero] at hcomp)

open LocalGuard

private abbrev Free {k : ℕ} (pin : Finset (Fin k)) := {j : Fin k // j ∉ pin}

private def extendFree {k : ℕ} (pin : Finset (Fin k)) (x : Vec (Free pin)) (j : Fin k) : F :=
  if hj : j ∉ pin then x ⟨j,hj⟩ else 0

private def rawField {k : ℕ} (key : Fin (2 ^ k)) (j : Fin k) : F := z2OfBool (key.val.testBit j.val)

private def keyAt {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k)) (x : Vec (Free pin)) : Fin (2 ^ k) :=
  wordOf k fun j => asBool (rawField ref j + extendFree pin x j)

private lemma rawField_keyAt {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (x : Vec (Free pin)) (j : Fin k) :
    rawField (keyAt pin ref x) j = rawField ref j + extendFree pin x j := by
  simp only [rawField, keyAt, testBit_wordOf, fieldRound]

private lemma keyAt_fiber {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (x : Vec (Free pin)) (j : Fin k) (hj : j ∈ pin) :
    (keyAt pin ref x).val.testBit j.val = ref.val.testBit j.val := by
  apply z2OfBool_inj
  exact (rawField_keyAt pin ref x j).trans (by simp [extendFree, hj, rawField])

private lemma keyAt_zero {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k)) : keyAt pin ref 0 = ref := by
  unfold keyAt
  convert wordOf_testBit k ref using 2
  funext j
  by_cases hj : j ∈ pin <;> simp [extendFree, hj, rawField, boolRound]

private lemma keyAt_eq_ref {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k)) (x : Vec (Free pin)) :
    keyAt pin ref x = ref ↔ x = 0 := by
  constructor
  · intro h
    funext j
    have hj := rawField_keyAt pin ref x j.val
    rw [h] at hj
    have h' : rawField ref j.val + 0 = rawField ref j.val + x j := by
      simpa only [add_zero, extendFree, dif_pos j.property] using hj
    exact (add_left_cancel h').symm
  · rintro rfl
    exact keyAt_zero pin ref

private lemma keyAt_surj {k : ℕ} (pin : Finset (Fin k)) (ref key : Fin (2 ^ k))
    (hx : ∀ j ∈ pin, key.val.testBit j.val = ref.val.testBit j.val) :
    ∃ x : Vec (Free pin), keyAt pin ref x = key := by
  let x : Vec (Free pin) := fun j => rawField ref j + rawField key j
  refine ⟨x, ?_⟩
  unfold keyAt
  convert wordOf_testBit k key using 2
  funext j
  by_cases hj : j ∈ pin
  · simp [rawField, extendFree, hj, hx j hj, boolRound]
  · simp [x, extendFree, hj, ← add_assoc, z2_add_self, rawField, boolRound]

private lemma free_card {k : ℕ} (pin : Finset (Fin k)) : Fintype.card (Free pin) = k - pin.card := by
  classical
  have h := Fintype.card_subtype_compl (fun j : Fin k => j ∈ pin)
  simpa using h

private def maskForm {k : ℕ} (pin : Finset (Fin k)) (mask : Fin k → Bool) : Vec (Free pin) →ₗ[F] F :=
  ∑ j : Free pin, z2OfBool (mask j.val) • LinearMap.proj j

private def maskOffset {k : ℕ} (ref : Fin (2 ^ k)) (mask : Fin k → Bool) : F :=
  ∑ j : Fin k, z2OfBool (mask j) * rawField ref j

private def formMask {k : ℕ} (pin : Finset (Fin k)) (L : Vec (Free pin) →ₗ[F] F) (j : Fin k) : Bool :=
  if hj : j ∉ pin then asBool (L (Pi.single (⟨j, hj⟩ : Free pin) 1)) else false

private lemma maskForm_apply {k : ℕ} (pin : Finset (Fin k)) (mask : Fin k → Bool)
    (x : Vec (Free pin)) : maskForm pin mask x = ∑ j : Free pin, z2OfBool (mask j.val) * x j := by
  classical
  simp [maskForm, LinearMap.sum_apply, smul_eq_mul]

private lemma formMask_inverse {k : ℕ} (pin : Finset (Fin k)) (L : Vec (Free pin) →ₗ[F] F) :
    maskForm pin (formMask pin L) = L := by
  classical
  apply LinearMap.ext
  intro x
  have hx : (∑ j : Free pin, x j • Pi.single j (1 : F)) = x := by
    funext i
    rw [Finset.sum_apply, Fintype.sum_eq_single i]
    · simp
    · intro j hji
      simp [Pi.single_apply, hji]
  conv_rhs => rw [← hx]
  rw [map_sum, maskForm_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp [formMask, j.property, fieldRound, smul_eq_mul, mul_comm]

private lemma maskDot_keyAt {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (mask : Fin k → Bool) (x : Vec (Free pin)) :
    (∑ j : Fin k, z2OfBool (mask j) * rawField (keyAt pin ref x) j) =
      maskForm pin mask x + maskOffset ref mask := by
  classical
  simp only [rawField_keyAt, mul_add, Finset.sum_add_distrib, maskOffset, maskForm_apply]
  rw [add_comm]
  congr 1
  let g (j : Fin k) : F := z2OfBool (mask j) * extendFree pin x j
  calc
    (∑ j : Fin k, g j) = ∑ j ∈ pinᶜ, g j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hmem : j ∈ pin := by simpa using hj
      simp [g, extendFree, hmem]
    _ = ∑ j : Free pin, g j.val := Finset.sum_subtype pinᶜ (fun _ => Finset.mem_compl) g
    _ = _ := Finset.sum_congr rfl fun j _ => by simp [g, extendFree, j.property]

private def wordAnswer {k : ℕ} (ask : ℕ → ℕ → Bool × (Fin k → Bool)) :
    ℕ → ℕ → Bool × Fin (2 ^ k) → Bool := fun t p w =>
  let mask := ask t p
  let v := (∑ j : Fin k, (mask.2 j && w.2.val.testBit j.val).toNat) % 2 == 1
  xor (mask.1 && w.1) v

private lemma z2OfBool_toNat (v : Bool) : (v.toNat : F) = z2OfBool v := by cases v <;> rfl

private lemma z2_sum_bool {I : Type*} [Fintype I] (v : I → Bool) :
    z2OfBool ((∑ j, (v j).toNat) % 2 == 1) = ∑ j, z2OfBool (v j) := by
  rw [← z2_nat_eq_mod2, Nat.cast_sum]
  simp only [z2OfBool_toNat]

private lemma wordAnswer_eq {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (ask : ℕ → ℕ → Bool × (Fin k → Bool)) (t p : ℕ) (b : F) (x : Vec (Free pin)) :
    wordAnswer ask t p (asBool b, keyAt pin ref x) =
      queryAnswer (fun t p => ((ask t p).1, maskForm pin (ask t p).2))
        (fun t p => maskOffset ref (ask t p).2) t p (b,x) := by
  apply z2OfBool_inj
  simp only [wordAnswer, queryAnswer, fieldRound, z2OfBool_xor, z2OfBool_and, z2_sum_bool]
  have h := maskDot_keyAt pin ref (ask t p).2 x
  simp only [rawField] at h
  rw [h, add_assoc]

private lemma runWord_eq {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (ask : ℕ → ℕ → Bool × (Fin k → Bool)) (n : ℕ) (b : F) (x : Vec (Free pin)) :
    stepRun (wordAnswer ask) (asBool b, keyAt pin ref x) n =
      stepRun (queryAnswer (fun t p => ((ask t p).1, maskForm pin (ask t p).2))
        (fun t p => maskOffset ref (ask t p).2)) (b,x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [stepRun_succ, stepRun_succ, ih, wordAnswer_eq]

private def wordCorrect {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (target : Fin (2 ^ k) → Bool) (n : ℕ) (ask : ℕ → ℕ → Bool × (Fin k → Bool)) (read : ℕ → Bool) : Prop :=
  (∀ b : Bool, read (stepRun (wordAnswer ask) (b,ref) n) = false) ∧
    ∀ key, (∀ j ∈ pin, key.val.testBit j.val = ref.val.testBit j.val) → key ≠ ref →
      read (stepRun (wordAnswer ask) (target key,key) n) = true

private lemma wordCorrect_iff {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (target : Fin (2 ^ k) → Bool) (n : ℕ) (ask : ℕ → ℕ → Bool × (Fin k → Bool)) (read : ℕ → Bool) :
    wordCorrect pin ref target n ask read ↔
      correct n (fun x => z2OfBool (target (keyAt pin ref x)))
        (fun t p => ((ask t p).1, maskForm pin (ask t p).2))
        (fun t p => maskOffset ref (ask t p).2) read := by
  constructor
  · intro h
    constructor
    · intro b
      rw [← runWord_eq, keyAt_zero]
      exact h.1 _
    · intro x hx
      rw [← runWord_eq, boolRound]
      exact h.2 _ (keyAt_fiber pin ref x) (fun he => hx ((keyAt_eq_ref pin ref x).mp he))
  · intro h
    constructor
    · intro b
      have he := h.1 (z2OfBool b)
      rwa [← runWord_eq, keyAt_zero, boolRound] at he
    · intro key hkey hne
      obtain ⟨x, rfl⟩ := keyAt_surj pin ref key hkey
      have he := h.2 x (fun he => hne ((keyAt_eq_ref pin ref x).mpr he))
      rwa [← runWord_eq, boolRound] at he

private lemma wordCorrect_of_linear {k : ℕ} (pin : Finset (Fin k)) (ref : Fin (2 ^ k))
    (target : Fin (2 ^ k) → Bool) (n : ℕ) (ask : ℕ → ℕ → Bool × (Vec (Free pin) →ₗ[F] F)) (read : ℕ → Bool)
    (h : correct n (fun x => z2OfBool (target (keyAt pin ref x))) ask
        (fun t p => maskOffset ref (formMask pin (ask t p).2)) read) :
    wordCorrect pin ref target n (fun t p => ((ask t p).1, formMask pin (ask t p).2)) read := by
  apply (wordCorrect_iff pin ref target n _ read).mpr
  simpa only [formMask_inverse, Prod.eta] using h

private def targetWord {k m : ℕ} (constant : ℕ → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (starts : Fin m → ℕ) (key : Fin (2 ^ k)) : Bool :=
  (∑ i, (roundBit constant row 2 key (starts i + 5)).toNat) % 2 == 1

private lemma guarded_target {k m : ℕ} (hk : 12 ≤ k)
    (constant : ℕ → Fin (2 ^ k)) (row ref : Fin (2 ^ k)) (starts : Fin m → ℕ)
    (pin : Finset (Fin k)) (hgood : ∀ i, goodAt constant row ref (starts i))
    (hpin_in : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k)
    (hpin_out : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k) :
    let hk₀ : 0 < k := by omega
    let rp := rawPins hk₀ pin
    let idx : Fin m × Fin 3 → Free rp := fun z =>
      ⟨blockIndex hk₀ starts z, blockIndex_notMem_rawPins hk₀ starts pin hpin_out z⟩
    ∃ (L : Vec (Free rp) →ₗ[F] F) (c : F) (shift : Fin m → Vec (Fin 3)),
      ∀ x, z2OfBool (targetWord constant row starts (keyAt rp ref x)) =
        L x + c + ∑ i, ∏ j, (x (idx (i,j)) + shift i j) := by
  classical
  intro hk₀ rp idx
  choose s l c h using fun i => guarded_block_formula hk constant row ref starts pin hpin_in i (hgood i)
  let d (i : Fin m) (j : Fin 3) : F := rawField ref (idx (i,j)).val
  let u (i : Fin m) (j : Fin 3) : F := z2OfBool (l i j)
  let L : Vec (Free rp) →ₗ[F] F := ∑ i : Fin m, ∑ j : Fin 3,
    u i j • (LinearMap.proj (idx (i,j)) : Vec (Free rp) →ₗ[F] F)
  let bias := ∑ i : Fin m, (z2OfBool (c i) + ∑ j : Fin 3, u i j * d i j)
  let shift := fun i j => d i j + z2OfBool (s i j)
  refine ⟨L,bias,shift,?_⟩
  intro x
  have hm (i : Fin m) : z2OfBool (roundBit constant row 2 (keyAt rp ref x) (starts i + 5)) =
      (∏ j, (x (idx (i,j)) + shift i j)) +
      ((∑ j, u i j * x (idx (i,j))) + (z2OfBool (c i) + ∑ j, u i j * d i j)) := by
    have he := congrArg z2OfBool (h i (keyAt rp ref x) (keyAt_fiber rp ref x))
    simp only [z2OfBool_xor, z2OfBool_and] at he
    have hv (j : Fin 3) : z2OfBool ((keyAt rp ref x).val.testBit (blockIndex hk₀ starts (i,j)).val) =
        d i j + x (idx (i,j)) := by
      exact (rawField_keyAt rp ref x (idx (i,j)).val).trans
        (by rw [extendFree, dif_pos (idx (i,j)).property])
    simp only [hv] at he
    rw [he, Fin.prod_univ_three]
    simp only [Fin.sum_univ_three, u, shift]
    ring
  simp only [targetWord, z2_sum_bool, hm, Finset.sum_add_distrib, L, bias, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, LinearMap.proj_apply]
  ring

set_option maxHeartbeats 1000000 in
private lemma proveBlockProtocol {k m : ℕ} (hk : 0 < k)
    (constant : ℕ → Fin (2 ^ k)) (starts : Fin m → ℕ) (hm : 2 ≤ m)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k))
    (row ref : Fin (2 ^ k)) (hgood : ∀ i, goodAt constant row ref (starts i))
    (pin : Finset (Fin k))
    (hpin_in : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k)
    (hpin_out : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k)
    (depth : ℕ) :
    let rp := rawPins hk pin
    let tg := targetWord constant row starts
    ((∃ ask read, wordCorrect rp ref tg depth ask read) ↔ k - pin.card - 2 ≤ depth) ∧
    ((∃ (masks : ℕ → Bool × (Fin k → Bool)) (read : ℕ → Bool),
        wordCorrect rp ref tg depth (fun t _ => masks t) read) ↔ k - pin.card ≤ depth) := by
  classical
  intro rp tg
  let idx : Fin m × Fin 3 → Free rp := fun z =>
    ⟨blockIndex hk starts z, blockIndex_notMem_rawPins hk starts pin hpin_out z⟩
  have hi : Function.Injective idx := fun x y h => blockIndex_injective hk starts hinj (congrArg Subtype.val h)
  have hcard : Fintype.card (Free rp) = k - pin.card := by rw [free_card, rawPins_card]
  obtain ⟨L,c,shift,hf⟩ := guarded_target (window_width hk (by omega) starts hinj)
    constant row ref starts pin hgood hpin_in hpin_out
  let offset := fun A => maskOffset ref (formMask rp A)
  let f := fun x => z2OfBool (tg (keyAt rp ref x))
  constructor
  · constructor
    · rintro ⟨ask,read,hr⟩
      rw [← hcard]
      exact adaptive_lower L c (blockProj idx) shift hf ((wordCorrect_iff rp ref tg depth ask read).mp hr)
    · intro hd
      let i₀ : Fin m := ⟨0, by omega⟩
      let i₁ : Fin m := ⟨1, by omega⟩
      have he : i₀ ≠ i₁ := by intro he; have := congrArg Fin.val he; contradiction
      obtain ⟨ask,read,hr⟩ := adaptive_upper_blocks i₀ i₁ he idx hi depth f offset L c shift hf
        (by rwa [hcard])
      exact ⟨_,read,wordCorrect_of_linear rp ref tg depth ask read hr⟩
  · constructor
    · rintro ⟨ask,read,hr⟩
      rw [← hcard]
      exact fixed_lower (ask := fun t => ((ask t).1, maskForm rp (ask t).2))
        ((wordCorrect_iff rp ref tg depth (fun t _ => ask t) read).mp hr)
    · intro hd
      obtain ⟨ask,read,hr⟩ := fixed_upper depth f offset (by rwa [hcard])
      exact ⟨fun t => ((ask t).1, formMask rp (ask t).2),read,
        wordCorrect_of_linear rp ref tg depth (fun t _ => ask t) read hr⟩

private lemma correct_iff_fiber {k m : ℕ} (hk : 2 ≤ k) (constant : ℕ → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (starts : Fin m → ℕ) (pin : Finset (Fin k)) (depth : ℕ)
    (ask : ℕ → ℕ → Bool × (Fin k → Bool)) (read : ℕ → Bool) :
    wordCorrect (rawPins (by omega : 0 < k) pin) ref (targetWord constant row starts) depth ask read ↔
      (∀ b : Bool, read (stepRun (wordAnswer ask) (b,ref) depth) = false) ∧
      (∀ key, (∀ z ∈ pin, roundBit constant row 0 key z.val = roundBit constant row 0 ref z.val) →
        key ≠ ref → read (stepRun (wordAnswer ask) (targetWord constant row starts key,key) depth) = true) := by
  unfold wordCorrect
  simp_rw [roundBit, fiber_iff_raw hk constant row ref]

end PEqualNP.Outside.L_meta_27807_aux

open PEqualNP.Outside.L_meta_27807_aux PEqualNP.Outside.L_meta_27807_aux.LocalGuard

theorem PEqualNP.Outside.L_meta_27807 :
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
    2 ≤ m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
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
    ∀ depth : Nat,
      let K := Fin (2^k)
      let inFiber := fun key : K =>
        ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val
      let target := fun key : K =>
        (∑ i : Fin m, (bit row.val 2 key.val (starts i+5)).toNat) % 2 == 1
      let run := fun (ask : Nat → Nat → Bool × (Fin k → Bool)) (b : Bool) (key : K) =>
        (List.range depth).foldl (fun history time =>
          let mask := ask time history
          let value := (∑ j : Fin k, (mask.2 j && key.val.testBit j.val).toNat) % 2 == 1
          history + ((xor (mask.1 && b) value).toNat <<< time)) 0
      let right := fun (ask : Nat → Nat → Bool × (Fin k → Bool)) (read : Nat → Bool) =>
        (∀ b : Bool, read (run ask b ref) = false) ∧
        (∀ key : K, inFiber key → key ≠ ref → read (run ask (target key) key) = true)
      let free := k-pin.card
      And
        (Iff (∃ ask read, right ask read) (free-2 ≤ depth))
        (Iff (∃ (masks : Nat → Bool × (Fin k → Bool)) (read : Nat → Bool),
          right (fun time _ => masks time) read) (free ≤ depth)) := by
  intro k hk constant rot step state injected bit m starts hm hinj good row ref hgood pin hp ho depth
    K inFiber target run right free
  have hk' := window_width hk (by omega) starts hinj
  have hw (ask : Nat → Nat → Bool × (Fin k → Bool)) (read : Nat → Bool) :
      wordCorrect (rawPins hk pin) ref (targetWord constant row starts) depth ask read ↔ right ask read :=
    correct_iff_fiber (by omega) constant row ref starts pin depth ask read
  simp_rw [← hw]
  exact proveBlockProtocol hk constant starts hm hinj row ref hgood pin hp ho depth
