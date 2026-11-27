import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25884_aux

open scoped Classical

private def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word j : Nat) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

private def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

private def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

private def stateAt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ u.val)

private lemma stateAt_zero (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (key : Nat) :
    stateAt k u constant 0 key = rot k 1 key ^^^ u.val := rfl

private lemma stateAt_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (s key : Nat) :
    stateAt k u constant (s + 1) key =
      step k (mix k (stateAt k u constant s key)) ^^^ rot k (2 * s) key ^^^ (constant (s + 1)).val := by
  simp [stateAt, List.range_succ]

private lemma rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

private lemma testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
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

private lemma testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
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

private lemma testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

private lemma testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

private lemma step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

private lemma stateAt_lt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) :
    stateAt k u constant rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) u.isLt
  | succ s =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (s + 1)).isLt

private lemma testBit_mix {k word b : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
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

private lemma mod_sub_eq {k p s : Nat} (hk : 0 < k) (hsp : s ≤ p) :
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

private lemma testBit_stateAt_succ {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (s : Nat) (key : Fin (2 ^ k)) (p : Nat) (hp : 1 ≤ p) :
    let prev := fun q => (stateAt k u constant s key.val).testBit (q % k)
    let m0 := xor (xor (prev p) (prev (p - 1))) (prev (p + 1))
    let m1 := xor (xor (prev (p + 1)) (prev p)) (prev (p + 2))
    let m2 := xor (xor (prev (p + 2)) (prev (p + 1))) (prev (p + 3))
    let inj := xor ((rot k (2 * s) key.val).testBit (p % k)) ((constant (s + 1)).val.testBit (p % k))
    (stateAt k u constant (s + 1) key.val).testBit (p % k) =
      xor (xor m0 (!m1 && m2)) inj := by
  have hk_pos : 0 < k := by omega
  intro prev m0 m1 m2 inj
  rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk_pos)]
  unfold stepBit
  have hm : ∀ d, (mix k (stateAt k u constant s key.val)).testBit ((p % k + d) % k) =
      xor (xor (prev (p + d)) (prev (p + d - 1))) (prev (p + d + 1)) := by
    intro d
    have hlt : (p % k + d) % k < k := Nat.mod_lt _ hk_pos
    rw [testBit_mix hk (stateAt_lt k u constant s key.val) hlt]
    have h0 : (p % k + d) % k = (p + d) % k := by rw [Nat.mod_add_mod]
    have hsub : ((p % k + d) % k + k - 1) % k = (p + d - 1) % k := by
      rw [h0]
      simpa [Nat.mod_eq_of_lt (by omega : 1 < k)] using mod_sub_eq hk_pos (by omega : 1 ≤ p + d)
    have hadd : ((p % k + d) % k + 1) % k = (p + d + 1) % k := by
      rw [h0, Nat.mod_add_mod]
    rw [hsub, hadd, h0]
  have hm0 := hm 0
  simp only [Nat.add_zero, Nat.mod_mod] at hm0
  have hm1 := hm 1
  have hm2 := hm 2
  rw [hm0, hm1, hm2]
  simp only [m0, m1, m2, inj, Nat.add_sub_cancel, show p + 2 - 1 = p + 1 by omega]
  cases prev p <;> cases prev (p - 1) <;> cases prev (p + 1) <;> cases prev (p + 2) <;>
    cases prev (p + 3) <;> cases (rot k (2 * s) key.val).testBit (p % k) <;>
    cases (constant (s + 1)).val.testBit (p % k) <;> rfl

private abbrev Sym := Fin 3 → Bool

private def winFn (old7 old8 α β c8 inj2 : Bool) (x : Sym) : Bool :=
  let u0 := xor (xor old7 old8) (x 0)
  let u1 := xor (xor old8 (x 0)) (x 1)
  let u2 := xor (xor (x 0) (x 1)) (x 2)
  let f4 := β
  let f5 := xor (!α) β
  let f6 := xor α u0
  let f7 := xor (!u0 && u1) β
  let f8 := xor (xor (xor u0 (!u1 && u2)) (x 0)) c8
  let M5 := xor (xor f4 f5) f6
  let M6 := xor (xor f5 f6) f7
  let M7 := xor (xor f6 f7) f8
  xor (xor M5 (!M6 && M7)) inj2

private lemma keyBit_from_state0 {k : Nat} (hk : 2 ≤ k) (row key : Fin (2 ^ k)) (pos : Nat) :
    key.val.testBit (pos % k) =
      xor ((stateAt k row (fun _ => 0) 0 key.val).testBit ((pos + 1) % k))
          (row.val.testBit ((pos + 1) % k)) := by
  have hk_pos : 0 < k := by omega
  rw [stateAt_zero, Nat.testBit_xor, testBit_rot key.isLt (Nat.mod_lt (pos + 1) hk_pos)]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hsub : ((pos + 1) % k + k - 1 % k) % k = pos % k := by
    simpa [Nat.add_sub_cancel] using mod_sub_eq hk_pos (by omega : 1 ≤ pos + 1)
  rw [hsub]
  cases key.val.testBit (pos % k) <;> cases row.val.testBit ((pos + 1) % k) <;> rfl

private lemma window_out_eq_winFn {k : Nat} (hk : 2 ≤ k) (constant : Nat → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (p : Nat)
    (hgood :
      let old := fun j => (stateAt k row constant 0 ref.val).testBit ((p + j) % k)
      let first := fun j => (stateAt k row constant 1 ref.val).testBit ((p + j) % k)
      let τ := xor (xor (old 6) (old 7)) (old 8)
      let α := xor (xor (xor (old 5) (old 6)) (old 7))
        (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
      let β := xor τ
        (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
      τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !α ∧ first 4 = β) :
    ∀ sample : Fin (2 ^ k),
        (∀ j : Fin 9, (stateAt k row constant 0 sample.val).testBit ((p + j.val) % k) =
          (stateAt k row constant 0 ref.val).testBit ((p + j.val) % k)) →
        (stateAt k row constant 2 sample.val).testBit ((p + 5) % k) =
          winFn
            ((stateAt k row constant 0 ref.val).testBit ((p + 7) % k))
            ((stateAt k row constant 0 ref.val).testBit ((p + 8) % k))
            (xor (xor (xor
              ((stateAt k row constant 0 ref.val).testBit ((p + 5) % k))
              ((stateAt k row constant 0 ref.val).testBit ((p + 6) % k)))
              ((stateAt k row constant 0 ref.val).testBit ((p + 7) % k)))
              (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))))
            (xor (xor (xor
              ((stateAt k row constant 0 ref.val).testBit ((p + 6) % k))
              ((stateAt k row constant 0 ref.val).testBit ((p + 7) % k)))
              ((stateAt k row constant 0 ref.val).testBit ((p + 8) % k)))
              (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k))))
            (xor (row.val.testBit ((p + 9) % k)) ((constant 1).val.testBit ((p + 8) % k)))
            (xor ((rot k 2 ref.val).testBit ((p + 5) % k)) ((constant 2).val.testBit ((p + 5) % k)))
            (fun v => (stateAt k row constant 0 sample.val).testBit ((p + 9 + v.val) % k)) := by
  have hk_pos : 0 < k := by omega
  let old := fun j => (stateAt k row constant 0 ref.val).testBit ((p + j) % k)
  let first := fun j => (stateAt k row constant 1 ref.val).testBit ((p + j) % k)
  let inj1 := fun (key : Fin (2 ^ k)) (j : Nat) =>
    xor ((rot k 0 key.val).testBit ((p + j) % k)) ((constant 1).val.testBit ((p + j) % k))
  let inj2 := fun (key : Fin (2 ^ k)) (j : Nat) =>
    xor ((rot k 2 key.val).testBit ((p + j) % k)) ((constant 2).val.testBit ((p + j) % k))
  let τ := xor (xor (old 6) (old 7)) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (inj1 ref 6)
  let β := xor τ (inj1 ref 7)
  have hτ : τ = false := hgood.1
  have hf45 : xor (first 4) (first 5) = !α := hgood.2.2.1
  have hf4 : first 4 = β := hgood.2.2.2
  have hf5 : first 5 = xor (!α) β := by
    rw [hf4] at hf45
    generalize first 5 = f5 at hf45 ⊢
    generalize α = a0 at hf45 ⊢
    generalize β = b0 at hf45 ⊢
    cases f5 <;> cases a0 <;> cases b0 <;> simp_all
  let c8 := xor (row.val.testBit ((p + 9) % k)) ((constant 1).val.testBit ((p + 8) % k))
  intro sample hpin
  have hpin_nat : ∀ j < 9, (stateAt k row constant 0 sample.val).testBit ((p + j) % k) = old j :=
    fun j hj => hpin ⟨j, hj⟩
  have hrot0 : ∀ (key : Fin (2 ^ k)) (q : Nat), (rot k 0 key.val).testBit (q % k) = key.val.testBit (q % k) := by
    intro key q
    rw [testBit_rot key.isLt (Nat.mod_lt q hk_pos)]
    simp [Nat.mod_eq_of_lt hk_pos]
  have hinj1_eq : ∀ j < 8, inj1 sample j = inj1 ref j := by
    intro j hj
    simp only [inj1, hrot0]
    have hks := keyBit_from_state0 hk row sample (p + j)
    have hkr := keyBit_from_state0 hk row ref (p + j)
    have hp1 : (stateAt k row constant 0 sample.val).testBit ((p + j + 1) % k) =
        (stateAt k row constant 0 ref.val).testBit ((p + j + 1) % k) := by
      have := hpin_nat (j + 1) (by omega)
      simpa [Nat.add_assoc] using this
    rw [hks, hkr]
    simp only [stateAt_zero] at hp1 ⊢
    rw [hp1]
  have hinj1_8 : inj1 sample 8 =
      xor ((stateAt k row constant 0 sample.val).testBit ((p + 9) % k)) c8 := by
    simp only [inj1, hrot0, c8]
    have hks := keyBit_from_state0 hk row sample (p + 8)
    rw [hks]
    simp only [stateAt_zero, Nat.add_assoc]
    cases (rot k 1 sample.val ^^^ row.val).testBit ((p + 9) % k) <;>
      cases row.val.testBit ((p + 9) % k) <;>
      cases (constant 1).val.testBit ((p + 8) % k) <;> rfl
  have hinj2_5 : inj2 sample 5 = inj2 ref 5 := by
    simp only [inj2]
    rw [testBit_rot sample.isLt (Nat.mod_lt (p + 5) hk_pos),
        testBit_rot ref.isLt (Nat.mod_lt (p + 5) hk_pos)]
    have hsub : ((p + 5) % k + k - 2 % k) % k = (p + 3) % k := by
      simpa [show p + 5 - 2 = p + 3 by omega] using mod_sub_eq hk_pos (by omega : 2 ≤ p + 5)
    rw [hsub]
    have hks := keyBit_from_state0 hk row sample (p + 3)
    have hkr := keyBit_from_state0 hk row ref (p + 3)
    have hp4 : (stateAt k row constant 0 sample.val).testBit ((p + 3 + 1) % k) =
        (stateAt k row constant 0 ref.val).testBit ((p + 3 + 1) % k) := by
      have := hpin_nat 4 (by omega)
      simpa [Nat.add_assoc] using this
    rw [hks, hkr]
    simp only [stateAt_zero] at hp4 ⊢
    rw [hp4]
  have hstep1_s : ∀ j, 1 ≤ j →
      (stateAt k row constant 1 sample.val).testBit ((p + j) % k) =
        let prev := fun q => (stateAt k row constant 0 sample.val).testBit ((p + q) % k)
        let m0 := xor (xor (prev j) (prev (j - 1))) (prev (j + 1))
        let m1 := xor (xor (prev (j + 1)) (prev j)) (prev (j + 2))
        let m2 := xor (xor (prev (j + 2)) (prev (j + 1))) (prev (j + 3))
        xor (xor m0 (!m1 && m2)) (inj1 sample j) := by
    intro j hj
    have h := testBit_stateAt_succ hk row constant 0 sample (p + j) (by omega)
    simpa [Nat.add_assoc, show p + j - 1 = p + (j - 1) by omega, inj1] using h
  have hstep1_r : ∀ j, 1 ≤ j →
      first j =
        let m0 := xor (xor (old j) (old (j - 1))) (old (j + 1))
        let m1 := xor (xor (old (j + 1)) (old j)) (old (j + 2))
        let m2 := xor (xor (old (j + 2)) (old (j + 1))) (old (j + 3))
        xor (xor m0 (!m1 && m2)) (inj1 ref j) := by
    intro j hj
    have h := testBit_stateAt_succ hk row constant 0 ref (p + j) (by omega)
    simpa [first, old, Nat.add_assoc, show p + j - 1 = p + (j - 1) by omega, inj1] using h
  have hf4_eq : (stateAt k row constant 1 sample.val).testBit ((p + 4) % k) = β := by
    rw [← hf4, hstep1_s 4 (by omega), hstep1_r 4 (by omega)]
    simp only [hpin_nat 3 (by omega), hpin_nat 4 (by omega), hpin_nat 5 (by omega),
      hpin_nat 6 (by omega), hpin_nat 7 (by omega), hinj1_eq 4 (by omega)]
  have hf5_eq : (stateAt k row constant 1 sample.val).testBit ((p + 5) % k) = xor (!α) β := by
    rw [← hf5, hstep1_s 5 (by omega), hstep1_r 5 (by omega)]
    simp only [hpin_nat 4 (by omega), hpin_nat 5 (by omega), hpin_nat 6 (by omega),
      hpin_nat 7 (by omega), hpin_nat 8 (by omega), hinj1_eq 5 (by omega)]
  set x0 := (stateAt k row constant 0 sample.val).testBit ((p + 9) % k)
  set x1 := (stateAt k row constant 0 sample.val).testBit ((p + 10) % k)
  set x2 := (stateAt k row constant 0 sample.val).testBit ((p + 11) % k)
  have hf6_eq : (stateAt k row constant 1 sample.val).testBit ((p + 6) % k) =
      xor α (xor (xor (old 7) (old 8)) x0) := by
    rw [hstep1_s 6 (by omega)]
    dsimp only
    simp only [hpin_nat 5 (by omega), hpin_nat 6 (by omega), hpin_nat 7 (by omega),
      hpin_nat 8 (by omega), hinj1_eq 6 (by omega)]
    have h678 : xor (xor (old 7) (old 6)) (old 8) = false := by
      have : xor (xor (old 7) (old 6)) (old 8) = τ := by
        simp only [τ]; cases old 6 <;> cases old 7 <;> cases old 8 <;> rfl
      rw [this, hτ]
    rw [h678]
    change xor (xor (xor (old 6) (old 5)) (old 7)) (!false && xor (xor (old 8) (old 7)) x0) |>
      fun t => xor t (inj1 ref 6) = xor α (xor (xor (old 7) (old 8)) x0)
    simp only [α]
    cases old 5 <;> cases old 6 <;> cases old 7 <;> cases old 8 <;> cases x0 <;> cases inj1 ref 6 <;> rfl
  have hf7_eq : (stateAt k row constant 1 sample.val).testBit ((p + 7) % k) =
      xor (!(xor (xor (old 7) (old 8)) x0) && xor (xor (old 8) x0) x1) β := by
    rw [hstep1_s 7 (by omega)]
    dsimp only
    simp only [hpin_nat 6 (by omega), hpin_nat 7 (by omega), hpin_nat 8 (by omega),
      hinj1_eq 7 (by omega)]
    have h678 : xor (xor (old 7) (old 6)) (old 8) = false := by
      have : xor (xor (old 7) (old 6)) (old 8) = τ := by
        simp only [τ]; cases old 6 <;> cases old 7 <;> cases old 8 <;> rfl
      rw [this, hτ]
    have hβ : inj1 ref 7 = β := by simp [β, hτ]
    rw [h678, hβ]
    change xor (xor false (!(xor (xor (old 8) (old 7)) x0) && xor (xor x0 (old 8)) x1)) β =
      xor (!(xor (xor (old 7) (old 8)) x0) && xor (xor (old 8) x0) x1) β
    cases old 7 <;> cases old 8 <;> cases x0 <;> cases x1 <;> cases β <;> rfl
  have hf8_eq : (stateAt k row constant 1 sample.val).testBit ((p + 8) % k) =
      xor (xor (xor (xor (xor (old 7) (old 8)) x0)
        (!(xor (xor (old 8) x0) x1) && xor (xor x0 x1) x2)) x0) c8 := by
    rw [hstep1_s 8 (by omega)]
    dsimp only
    simp only [hpin_nat 7 (by omega), hpin_nat 8 (by omega), hinj1_8]
    change xor (xor (xor (xor (old 8) (old 7)) x0)
      (!(xor (xor x0 (old 8)) x1) && xor (xor x1 x0) x2)) (xor x0 c8) = _
    cases old 7 <;> cases old 8 <;> cases x0 <;> cases x1 <;> cases x2 <;> cases c8 <;> rfl
  have hstep2 := testBit_stateAt_succ hk row constant 1 sample (p + 5) (by omega)
  dsimp only at hstep2
  have h54 : p + 5 - 1 = p + 4 := by omega
  have h56 : p + 5 + 1 = p + 6 := by omega
  have h57 : p + 5 + 2 = p + 7 := by omega
  have h58 : p + 5 + 3 = p + 8 := by omega
  rw [h54, h56, h57, h58, hf4_eq, hf5_eq, hf6_eq, hf7_eq, hf8_eq] at hstep2
  have hinj2_eq : xor ((rot k (2 * 1) sample.val).testBit ((p + 5) % k))
      ((constant 2).val.testBit ((p + 5) % k)) = inj2 ref 5 := hinj2_5
  rw [hinj2_eq] at hstep2
  rw [hstep2]
  have hx0 : (stateAt k row constant 0 sample.val).testBit ((p + 9 + (0 : Fin 3).val) % k) = x0 := rfl
  have hx1 : (stateAt k row constant 0 sample.val).testBit ((p + 9 + (1 : Fin 3).val) % k) = x1 := rfl
  have hx2 : (stateAt k row constant 0 sample.val).testBit ((p + 9 + (2 : Fin 3).val) % k) = x2 := rfl
  simp only [winFn, hx0, hx1, hx2]
  have hcomm3 : ∀ a b c : Bool, xor (xor a b) c = xor (xor b a) c := by decide
  rw [hcomm3 (xor (!α) β) β, hcomm3 (xor α (xor (xor (old 7) (old 8)) x0)) (xor (!α) β),
    hcomm3 (xor (!(xor (xor (old 7) (old 8)) x0) && xor (xor (old 8) x0) x1) β)
      (xor α (xor (xor (old 7) (old 8)) x0))]


private noncomputable def wordEquiv (k : Nat) : Fin (2^k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective (fun w i => w.val.testBit i.val) (by
    apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    · intro a b h
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < k
      · exact congrFun h ⟨j, hj⟩
      · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
          Nat.testBit_lt_two_pow (b.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
    · simp)

private lemma winFn_count (a b c d e f t : Bool) :
    ((Finset.univ : Finset Sym).filter (fun x => winFn a b c d e f x = t)).card =
      if t = !f then 5 else 3 := by
  revert a b c d e f t
  decide

private lemma block_count {k m n : Nat}
    (pos : Fin m → Fin n → Fin k)
    (hinj : Function.Injective (fun z : Fin m × Fin n => pos z.1 z.2))
    (pin : Finset (Fin k)) (fixed : Fin k → Bool)
    (hdisj : ∀ i j, pos i j ∉ pin)
    (C : Fin m → (Fin n → Bool) → Prop) [∀ i, DecidablePred (C i)] :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun f =>
      (∀ z ∈ pin, f z = fixed z) ∧ ∀ i, C i (fun j => f (pos i j)))).card =
      2^(k-pin.card-m*n) *
        ∏ i : Fin m, ((Finset.univ : Finset (Fin n → Bool)).filter (C i)).card := by
  classical
  let used := Finset.univ.image (fun z : Fin m × Fin n => pos z.1 z.2)
  let free := (Finset.univ \ pin) \ used
  let pack (f : free → Bool) (w : (i : Fin m) → {s : Fin n → Bool // C i s})
      (b : Fin k) : Bool :=
    if hb : b ∈ pin then fixed b
    else if hu : b ∈ used then
      let z := Classical.choose (Finset.mem_image.mp hu)
      (w z.1).val z.2
    else f ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩, hu⟩⟩
  have pp : ∀ f w b, b ∈ pin → pack f w b = fixed b := by
    intro f w b hb
    simp [pack, hb]
  have pw : ∀ f w i j, pack f w (pos i j) = (w i).val j := by
    intro f w i j
    have hu : pos i j ∈ used := Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩
    simp only [pack, hdisj i j, ↓reduceDIte, hu]
    have hz := (Classical.choose_spec (Finset.mem_image.mp hu)).2
    have heq := @hinj (Classical.choose (Finset.mem_image.mp hu)) (i,j) hz
    rw [heq]
  have pf : ∀ f w (b : free), pack f w b.val = f b := by
    intro f w b
    have hn := (Finset.mem_sdiff.mp b.property).2
    have hp := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp b.property).1).2
    simp [pack, hn, hp]
  let e : {f : Fin k → Bool // (∀ z ∈ pin, f z = fixed z) ∧
      ∀ i, C i (fun j => f (pos i j))} ≃
      ((free → Bool) × ((i : Fin m) → {s : Fin n → Bool // C i s})) :=
    { toFun := fun f => (fun b => f.val b.val, fun i => ⟨fun j => f.val (pos i j), f.property.2 i⟩)
      invFun := fun p => ⟨pack p.1 p.2, fun b hb => pp _ _ b hb,
        fun i => by simpa only [pw] using (p.2 i).property⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext b
        change pack (fun b => f.val b.val)
          (fun i => ⟨fun j => f.val (pos i j), f.property.2 i⟩) b = f.val b
        by_cases hp : b ∈ pin
        · exact (pp (fun b => f.val b.val)
            (fun i => ⟨fun j => f.val (pos i j), f.property.2 i⟩) b hp).trans
              (f.property.1 b hp).symm
        · by_cases hu : b ∈ used
          · obtain ⟨⟨i,j⟩, _, rfl⟩ := Finset.mem_image.mp hu
            exact pw (fun b => f.val b.val)
              (fun i => ⟨fun j => f.val (pos i j), f.property.2 i⟩) i j
          · exact pf (fun b => f.val b.val)
              (fun i => ⟨fun j => f.val (pos i j), f.property.2 i⟩) ⟨b, Finset.mem_sdiff.mpr
              ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hp⟩, hu⟩⟩
      right_inv := fun ⟨f,w⟩ => by
        apply Prod.ext
        · funext b
          exact pf _ _ b
        · funext i
          apply Subtype.ext
          funext j
          exact pw _ _ i j }
  have hused : used.card = m*n := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hd : Disjoint pin used := by
    rw [Finset.disjoint_left]
    intro b hp hu
    obtain ⟨⟨i,j⟩, _, rfl⟩ := Finset.mem_image.mp hu
    exact hdisj i j hp
  have hfree : free.card = k-pin.card-m*n := by
    rw [Finset.card_sdiff_of_subset (by
      intro b hb
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.disjoint_right.mp hd) hb⟩)]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ pin), Finset.card_univ,
      Fintype.card_fin, hused]
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_coe, hfree, Fintype.card_pi]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact Fintype.card_subtype _ 

private lemma count_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (P : A → Prop) (Q : B → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ a, P a ↔ Q (e a)) :
    (Finset.univ.filter P).card = (Finset.univ.filter Q).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (e.subtypeEquiv h)

private lemma rot_back {k : Nat} (hk : 0 < k) (w : Fin (2^k)) :
    rot k 1 (rot k (k-1) w.val) = w.val := by
  by_cases hk1 : k = 1
  · subst k
    revert w
    decide
  have hk2 : 2 ≤ k := by omega
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · rw [testBit_rot (rot_lt _ _ _) hj,
      testBit_rot w.isLt (Nat.mod_lt _ hk)]
    simp only [Nat.mod_eq_of_lt (by omega : 1 < k),
      Nat.mod_eq_of_lt (by omega : k-1 < k)]
    have hidx : (((j+k-1)%k+k-(k-1))%k) = j := by
      have h : (j+k-1)%k+k-(k-1) = (j+k-1)%k+1 := by omega
      rw [h, Nat.mod_add_mod, show j+k-1+1 = j+k by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    rw [hidx]
  · rw [Nat.testBit_lt_two_pow ((rot_lt k 1 _).trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
      Nat.testBit_lt_two_pow (w.isLt.trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]

private def anchorRef {k : Nat} (anchor row : Fin (2^k)) : Fin (2^k) :=
  ⟨rot k (k-1) (row.val ^^^ anchor.val) % 2^k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

private lemma anchorRef_state {k : Nat} (hk : 0 < k)
    (constant : Nat → Fin (2^k)) (anchor row : Fin (2^k)) :
    stateAt k row constant 0 (anchorRef anchor row).val = anchor.val := by
  rw [stateAt_zero]
  simp only [anchorRef, Nat.mod_eq_of_lt (rot_lt k _ _)]
  rw [rot_back hk ⟨row.val ^^^ anchor.val, xor_lt row.isLt anchor.isLt⟩]
  exact Nat.xor_right_comm _ _ _ |>.trans (by simp)

private noncomputable def initialEquiv {k : Nat} (hk : 0 < k)
    (constant : Nat → Fin (2^k)) (row : Fin (2^k)) :
    Fin (2^k) ≃ (Fin k → Bool) :=
  (Equiv.ofBijective
    (fun q : Fin (2^k) => (⟨stateAt k row constant 0 q.val, stateAt_lt _ _ _ _ _⟩ : Fin (2^k)))
    (by
      have hs : Function.Surjective
          (fun q : Fin (2^k) => (⟨stateAt k row constant 0 q.val, stateAt_lt _ _ _ _ _⟩ : Fin (2^k))) := by
        intro w
        exact ⟨anchorRef w row, Fin.ext (anchorRef_state hk constant w row)⟩
      exact ⟨(Finite.injective_iff_surjective).mpr hs, hs⟩)).trans (wordEquiv k)

private def bit {k : Nat} (constant : Nat → Fin (2^k))
    (row : Fin (2^k)) (r : Nat) (key : Fin (2^k)) (p : Nat) : Bool :=
  (stateAt k row constant r key.val).testBit (p % k)

private def injected {k : Nat} (constant : Nat → Fin (2^k))
    (r : Nat) (key : Fin (2^k)) (p : Nat) : Bool :=
  xor ((rot k (2*(r-1)) key.val).testBit (p%k)) ((constant r).val.testBit (p%k))

private abbrev good {k : Nat} (constant : Nat → Fin (2^k))
    (row ref : Fin (2^k)) (p : Nat) : Prop :=
  let old := fun j => bit constant row 0 ref (p+j)
  let first := fun j => bit constant row 1 ref (p+j)
  let τ := xor (xor (old 6) (old 7)) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected constant 1 ref (p+6))
  let β := xor τ (injected constant 1 ref (p+7))
  τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
    xor (first 4) (first 5) = !α ∧ first 4 = β

private def maj {k : Nat} (constant : Nat → Fin (2^k))
    (ref : Fin (2^k)) (p : Nat) : Bool := !(injected constant 2 ref (p+5))

private def windowFn {k : Nat} (constant : Nat → Fin (2^k))
    (row ref : Fin (2^k)) (p : Nat) : Sym → Bool :=
  let old := fun j => bit constant row 0 ref (p+j)
  let τ := xor (xor (old 6) (old 7)) (old 8)
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected constant 1 ref (p+6))
  let β := xor τ (injected constant 1 ref (p+7))
  winFn (old 7) (old 8) α β
    (xor (row.val.testBit ((p+9)%k)) ((constant 1).val.testBit ((p+8)%k)))
    (injected constant 2 ref (p+5))

private lemma window_eq {k : Nat} (hk : 2 ≤ k) (constant : Nat → Fin (2^k))
    (row ref : Fin (2^k)) (p : Nat) (hg : good constant row ref p)
    (q : Fin (2^k)) (hp : ∀ j : Fin 9, bit constant row 0 q (p+j.val) =
      bit constant row 0 ref (p+j.val)) :
    bit constant row 2 q (p+5) =
      windowFn constant row ref p (fun j => bit constant row 0 q (p+9+j.val)) :=
  window_out_eq_winFn hk constant row ref p hg q hp

private lemma initialEquiv_apply {k : Nat} (hk : 0 < k)
    (constant : Nat → Fin (2^k)) (row q : Fin (2^k)) (b : Fin k) :
    initialEquiv hk constant row q b = bit constant row 0 q b.val := by
  change (stateAt k row constant 0 q.val).testBit b.val =
    (stateAt k row constant 0 q.val).testBit (b.val % k)
  rw [Nat.mod_eq_of_lt b.isLt]

private lemma subwindow_inj {k m n a : Nat} (hk : 0 < k)
    (starts : Fin m → Nat)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k))
    (ha : a+n ≤ 12) :
    Function.Injective (fun z : Fin m × Fin n =>
      (⟨(starts z.1+a+z.2.val)%k, Nat.mod_lt _ hk⟩ : Fin k)) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ h
  have hv : (starts i+(a+j.val))%k = (starts i'+(a+j'.val))%k := by
    simpa [Nat.add_assoc] using congrArg Fin.val h
  have hh := @hinj (i,⟨a+j.val,by omega⟩) (i',⟨a+j'.val,by omega⟩) hv
  refine Prod.ext (show i = i' from congrArg Prod.fst hh) ?_
  change j = j'
  apply Fin.ext
  have := congrArg (fun z => z.2.val) hh
  dsimp at this
  omega

private lemma count_keys {k m : Nat} (hk : 0 < k) (constant : Nat → Fin (2^k))
    (starts : Fin m → Nat)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k))
    (row ref : Fin (2^k)) (hg : ∀ i, good constant row ref (starts i))
    (pin : Finset (Fin k))
    (hp9 : ∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val)%k)
    (hp3 : ∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val)%k)
    (target : Fin m → Bool) :
    ((Finset.univ : Finset (Fin (2^k))).filter (fun q =>
      (∀ z ∈ pin, bit constant row 0 q z.val = bit constant row 0 ref z.val) ∧
      ∀ i, bit constant row 2 q (starts i+5) = target i)).card =
      2^(k-pin.card-3*m) *
        5^((Finset.univ.filter (fun i => target i == maj constant ref (starts i))).card) *
        3^(m-(Finset.univ.filter (fun i => target i == maj constant ref (starts i))).card) := by
  classical
  let pos : Fin m → Fin 3 → Fin k := fun i j => ⟨(starts i+9+j.val)%k, Nat.mod_lt _ hk⟩
  let C : Fin m → Sym → Prop := fun i x => windowFn constant row ref (starts i) x = target i
  have hpos : Function.Injective (fun z : Fin m × Fin 3 => pos z.1 z.2) :=
    subwindow_inj hk starts hinj (by omega)
  have hnot : ∀ i j, pos i j ∉ pin := by
    intro i j hm
    exact hp3 i j (pos i j) hm rfl
  have hout : ∀ q : Fin (2^k),
      (∀ z ∈ pin, bit constant row 0 q z.val = bit constant row 0 ref z.val) →
      ∀ i, bit constant row 2 q (starts i+5) =
        windowFn constant row ref (starts i) (fun j => initialEquiv hk constant row q (pos i j)) := by
    intro q hp i
    have hk12 : 12 ≤ k := by
      have h := Fintype.card_le_of_injective
        (fun j : Fin 12 => (⟨(starts i+j.val)%k, Nat.mod_lt _ hk⟩ : Fin k))
        (fun a b h => by
          have hh := @hinj (i,a) (i,b) (congrArg Fin.val h)
          exact congrArg Prod.snd hh)
      simpa using h
    have hh := window_eq (by omega) constant row ref (starts i) (hg i) q (by
      intro j
      obtain ⟨z,hz,hv⟩ := hp9 i j
      have hh := hp z hz
      simpa only [bit, hv, Nat.mod_mod] using hh)
    simpa only [initialEquiv_apply, bit, pos, Nat.mod_mod] using hh
  have hc := count_equiv (initialEquiv hk constant row)
    (fun q => (∀ z ∈ pin, bit constant row 0 q z.val = bit constant row 0 ref z.val) ∧
      ∀ i, bit constant row 2 q (starts i+5) = target i)
    (fun f => (∀ z ∈ pin, f z = bit constant row 0 ref z.val) ∧ ∀ i, C i (fun j => f (pos i j)))
    (by
      intro q
      simp only [initialEquiv_apply]
      constructor
      · rintro ⟨hp,ho⟩
        refine ⟨hp,fun i => ?_⟩
        simpa only [C, initialEquiv_apply] using (hout q hp i).symm.trans (ho i)
      · rintro ⟨hp,ho⟩
        refine ⟨hp,fun i => ?_⟩
        have hi := hout q hp i
        simp only [initialEquiv_apply] at hi
        exact hi.trans (ho i))
  rw [hc, block_count pos hpos pin (fun z => bit constant row 0 ref z.val) hnot C]
  have hcount : ∀ i, ((Finset.univ : Finset Sym).filter (C i)).card =
      if target i = maj constant ref (starts i) then 5 else 3 := by
    intro i
    exact winFn_count _ _ _ _ _ _ _
  simp_rw [hcount]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Nat.mul_comm m 3]
  have hneg : (Finset.univ.filter (fun i => ¬ target i = maj constant ref (starts i))).card =
      m - (Finset.univ.filter (fun i => target i = maj constant ref (starts i))).card := by
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => target i = maj constant ref (starts i))
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    omega
  rw [hneg]
  simp only [beq_iff_eq]
  ring

private abbrev rowModel (d3 d4 d5 da db dm : Bool) (orient : Option Bool)
    (x : Fin 5 → Bool) : Prop :=
  xor (xor (xor d3 (x 0)) (xor d4 (x 1))) (xor d5 (x 2)) = true ∧
    xor (xor d4 (x 1)) (xor d5 (x 2)) = !(xor da (x 3)) ∧
    xor d4 (x 1) = xor db (x 4) ∧
    ∀ b : Bool, orient = some b → (!(xor dm (x 0))) = b

private lemma rowModel_count (d3 d4 d5 da db dm : Bool) (orient : Option Bool) :
    ((Finset.univ : Finset (Fin 5 → Bool)).filter (rowModel d3 d4 d5 da db dm orient)).card =
      if orient.isSome then 2 else 4 := by
  revert d3 d4 d5 da db dm orient
  decide

private abbrev rowFn {k : Nat} (constant : Nat → Fin (2^k)) (anchor : Fin (2^k))
    (p : Nat) (orient : Option Bool) : (Fin 5 → Bool) → Prop :=
  let a := fun j => anchor.val.testBit ((p+j)%k)
  let d := fun j => xor (xor ((step k (mix k anchor.val)).testBit ((p+j)%k)) (a (j+1)))
    ((constant 1).val.testBit ((p+j)%k))
  rowModel (d 3) (d 4) (d 5)
    (xor (xor (xor (a 5) (a 6)) (a 7)) (xor (a 7) ((constant 1).val.testBit ((p+6)%k))))
    (xor (a 8) ((constant 1).val.testBit ((p+7)%k)))
    (xor (a 4) ((constant 2).val.testBit ((p+5)%k))) orient

set_option maxHeartbeats 1000000 in
private lemma row_condition {k : Nat} (hk : 2 ≤ k) (constant : Nat → Fin (2^k))
    (anchor row : Fin (2^k)) (p : Nat) (orient : Option Bool)
    (ht : xor (xor (anchor.val.testBit ((p+6)%k)) (anchor.val.testBit ((p+7)%k)))
      (anchor.val.testBit ((p+8)%k)) = false) :
    (good constant row (anchorRef anchor row) p ∧
      ∀ b, orient = some b → maj constant (anchorRef anchor row) p = b) ↔
      rowFn constant anchor p orient (fun j => row.val.testBit ((p+4+j.val)%k)) := by
  have hk0 : 0 < k := by omega
  let ref := anchorRef anchor row
  have hstate : stateAt k row constant 0 ref.val = anchor.val := anchorRef_state hk0 constant anchor row
  have hbit0 : ∀ j, bit constant row 0 ref (p+j) = anchor.val.testBit ((p+j)%k) := by
    intro j
    exact congrArg (fun w : Nat => w.testBit ((p+j)%k)) hstate
  have hkey : ∀ j, ref.val.testBit ((p+j)%k) =
      xor (anchor.val.testBit ((p+j+1)%k)) (row.val.testBit ((p+j+1)%k)) := by
    intro j
    have hh := keyBit_from_state0 hk row ref (p+j)
    have hs0 : stateAt k row (fun _ => 0) 0 ref.val = anchor.val := anchorRef_state hk0 _ anchor row
    rwa [hs0] at hh
  have hr0 : rot k 0 ref.val = ref.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · rw [testBit_rot ref.isLt hj]
      simp [Nat.mod_eq_of_lt hj]
    · rw [Nat.testBit_lt_two_pow ((rot_lt k 0 _).trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
        Nat.testBit_lt_two_pow (ref.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
  have hinj1 : ∀ j, injected constant 1 ref (p+j) =
      xor (xor (anchor.val.testBit ((p+j+1)%k)) ((constant 1).val.testBit ((p+j)%k)))
        (row.val.testBit ((p+j+1)%k)) := by
    intro j
    change xor ((rot k 0 ref.val).testBit ((p+j)%k)) _ = _
    rw [hr0, hkey]
    exact Bool.xor_right_comm _ _ _
  have hfirst : ∀ j, bit constant row 1 ref (p+j) =
      xor (xor (xor ((step k (mix k anchor.val)).testBit ((p+j)%k))
        (anchor.val.testBit ((p+j+1)%k))) ((constant 1).val.testBit ((p+j)%k)))
        (row.val.testBit ((p+j+1)%k)) := by
    intro j
    unfold bit
    rw [stateAt_succ, hstate, Nat.testBit_xor, Nat.testBit_xor]
    change xor (xor ((step k (mix k anchor.val)).testBit ((p+j)%k))
      ((rot k 0 ref.val).testBit ((p+j)%k))) _ = _
    rw [hr0, hkey]
    rw [← Bool.xor_assoc, Bool.xor_right_comm
      (xor ((step k (mix k anchor.val)).testBit ((p+j)%k)) (anchor.val.testBit ((p+j+1)%k)))]
  have hmaj : maj constant ref p =
      !(xor (xor (anchor.val.testBit ((p+4)%k)) ((constant 2).val.testBit ((p+5)%k)))
        (row.val.testBit ((p+4)%k))) := by
    unfold maj injected
    rw [testBit_rot ref.isLt (Nat.mod_lt _ hk0)]
    have hsub : ((p+5)%k+k-2%k)%k = (p+3)%k := by
      simpa [show p+5-2=p+3 by omega] using mod_sub_eq hk0 (by omega : 2 ≤ p+5)
    simp only [show 2*(2-1)=2 by decide]
    rw [hsub, hkey]
    rw [Bool.xor_right_comm (anchor.val.testBit ((p+4)%k))]
  change (good constant row ref p ∧
    ∀ b, orient = some b → maj constant ref p = b) ↔ _
  unfold good rowFn rowModel
  dsimp only
  simp only [hbit0, hfirst, hinj1, hmaj]
  simp only [show p+3+1=p+4 by omega, show p+4+1=p+5 by omega,
    show p+5+1=p+6 by omega, show p+6+1=p+7 by omega, show p+7+1=p+8 by omega,
    Fin.val_zero, Fin.val_one, show (2:Fin 5).val=2 from rfl,
    show (3:Fin 5).val=3 from rfl, show (4:Fin 5).val=4 from rfl,
    ht, Bool.false_xor]
  simp only [← Bool.xor_assoc, true_and, and_assoc]

private lemma count_rows {k m : Nat} (hk : 0 < k) (constant : Nat → Fin (2^k))
    (starts : Fin m → Nat)
    (hinj : Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k))
    (anchor : Fin (2^k))
    (ht : ∀ i, xor (xor (anchor.val.testBit ((starts i+6)%k)) (anchor.val.testBit ((starts i+7)%k)))
      (anchor.val.testBit ((starts i+8)%k)) = false)
    (orient : Fin m → Option Bool) :
    ((Finset.univ : Finset (Fin (2^k))).filter (fun row =>
      ∀ i, good constant row (anchorRef anchor row) (starts i) ∧
        ∀ b, orient i = some b → maj constant (anchorRef anchor row) (starts i) = b)).card =
      2^(k-3*m-(Finset.univ.filter (fun i => (orient i).isSome)).card) := by
  classical
  let pos : Fin m → Fin 5 → Fin k := fun i j => ⟨(starts i+4+j.val)%k, Nat.mod_lt _ hk⟩
  let C := fun i => rowFn constant anchor (starts i) (orient i)
  have hpos : Function.Injective (fun z : Fin m × Fin 5 => pos z.1 z.2) :=
    subwindow_inj hk starts hinj (by omega)
  have htotal : m*5 ≤ k := by
    have h := Fintype.card_le_of_injective (fun z : Fin m × Fin 5 => pos z.1 z.2) hpos
    simpa using h
  have hc := count_equiv (wordEquiv k)
    (fun row => ∀ i, good constant row (anchorRef anchor row) (starts i) ∧
      ∀ b, orient i = some b → maj constant (anchorRef anchor row) (starts i) = b)
    (fun f => (∀ z ∈ (∅ : Finset (Fin k)), f z = false) ∧
      ∀ i, C i (fun j => f (pos i j)))
    (by
      intro row
      simp only [Finset.notMem_empty, false_implies, implies_true, true_and]
      apply forall_congr'
      intro i
      have hk12 : 12 ≤ k := by
        have h := Fintype.card_le_of_injective
          (fun j : Fin 12 => (⟨(starts i+j.val)%k, Nat.mod_lt _ hk⟩ : Fin k))
          (fun a b h => by
            have hh := @hinj (i,a) (i,b) (congrArg Fin.val h)
            exact congrArg Prod.snd hh)
        simpa using h
      exact row_condition (by omega) constant anchor row (starts i) (orient i) (ht i))
  rw [hc, block_count pos hpos ∅ (fun _ => false) (by simp) C]
  have hcount : ∀ i, ((Finset.univ : Finset (Fin 5 → Bool)).filter (C i)).card =
      if (orient i).isSome then 2 else 4 := by
    intro i
    unfold C rowFn
    exact rowModel_count _ _ _ _ _ _ _
  simp_rw [hcount]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_empty, Nat.sub_zero]
  let h := (Finset.univ.filter (fun i => (orient i).isSome)).card
  have hp : h ≤ m := by
    have hh := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun i => (orient i).isSome)
    simpa only [Finset.card_univ, Fintype.card_fin] using hh
  have hneg : (Finset.univ.filter (fun i => ¬ (orient i).isSome = true)).card = m-h := by
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
      (fun i => (orient i).isSome = true)
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    omega
  rw [hneg]
  change 2^(k-m*5) * (2^h * 4^(m-h)) = 2^(k-3*m-h)
  calc
    _ = 2^((k-m*5)+h+2*(m-h)) := by
      rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul]
      ring
    _ = _ := by congr 1; omega

end PEqualNP.Outside.L_meta_25884_aux

theorem PEqualNP.Outside.L_meta_25884 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  let maj := fun (ref : Fin (2^k)) (p : Nat) => !(injected 2 ref.val (p+5))
  (∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
    ∀ pin : Finset (Fin k),
    (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
    (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
    ∀ target : Fin m → Bool,
    let h := (Finset.univ.filter (fun i => target i == maj ref (starts i))).card
    let keys := (Finset.univ : Finset (Fin (2^k))).filter (fun q =>
      (∀ z ∈ pin, bit row.val 0 q.val z.val = bit row.val 0 ref.val z.val) ∧
      ∀ i, bit row.val 2 q.val (starts i+5) = target i)
    keys.card = 2^(k-pin.card-3*m) * 5^h * 3^(m-h)) ∧
  (∀ anchor : Fin (2^k),
    let refOf := fun (row : Fin (2^k)) =>
      (⟨(rot (k-1) (row.val ^^^ anchor.val)) % (2^k), Nat.mod_lt _ (Nat.two_pow_pos k)⟩ : Fin (2^k))
    (∀ row : Fin (2^k), state row.val 0 (refOf row).val = anchor.val) ∧
    ((∀ i, let p := starts i
      xor (xor (anchor.val.testBit ((p+6) % k)) (anchor.val.testBit ((p+7) % k)))
        (anchor.val.testBit ((p+8) % k)) = false) →
      ∀ orient : Fin m → Option Bool,
      let prescribed := (Finset.univ.filter (fun i => (orient i).isSome)).card
      let rows := (Finset.univ : Finset (Fin (2^k))).filter (fun row =>
        ∀ i, good row (refOf row) (starts i) ∧
          ∀ b : Bool, orient i = some b → maj (refOf row) (starts i) = b)
      rows.card = 2^(k-3*m-prescribed)))) := by
  intro k hk constant
  dsimp only
  intro m starts hinj
  constructor
  · exact PEqualNP.Outside.L_meta_25884_aux.count_keys hk constant starts hinj
  · intro anchor
    constructor
    · intro row
      exact PEqualNP.Outside.L_meta_25884_aux.anchorRef_state hk constant anchor row
    · intro ht orient
      exact PEqualNP.Outside.L_meta_25884_aux.count_rows hk constant starts hinj anchor ht orient
