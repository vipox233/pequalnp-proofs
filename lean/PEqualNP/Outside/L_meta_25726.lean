import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25726_aux

open scoped Classical

private abbrev Z2 := ZMod 2

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

private def xorAll (f : Sym → Bool) : Bool :=
  xor (xor (xor (f ![false, false, false]) (f ![false, false, true]))
           (xor (f ![false, true, false]) (f ![false, true, true])))
      (xor (xor (f ![true, false, false]) (f ![true, false, true]))
           (xor (f ![true, true, false]) (f ![true, true, true])))

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

private lemma xorAll_winFn (old7 old8 α β c8 inj2 : Bool) :
    xorAll (winFn old7 old8 α β c8 inj2) = true := by
  revert old7 old8 α β c8 inj2
  decide

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
    ∃ F : Sym → Bool, xorAll F = true ∧
      ∀ sample : Fin (2 ^ k),
        (∀ j : Fin 9, (stateAt k row constant 0 sample.val).testBit ((p + j.val) % k) =
          (stateAt k row constant 0 ref.val).testBit ((p + j.val) % k)) →
        (stateAt k row constant 2 sample.val).testBit ((p + 5) % k) =
          F (fun v => (stateAt k row constant 0 sample.val).testBit ((p + 9 + v.val) % k)) := by
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
  refine ⟨winFn (old 7) (old 8) α β c8 (inj2 ref 5), xorAll_winFn _ _ _ _ _ _, ?_⟩
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

private def parBool (n : Nat) : Bool := n % 2 == 1

private def isLow (f : Sym → Bool) : Prop :=
  ∃ monomials : Finset (Finset (Fin 3)),
    (∀ mon ∈ monomials, mon.card ≤ 2) ∧ ∀ symbol,
      f symbol = parBool ((monomials.filter (fun mon => ∀ coord ∈ mon, symbol coord = true)).card)

private lemma parBool_add (a b : Nat) : parBool (a + b) = xor (parBool a) (parBool b) := by
  simp only [parBool]
  have : (a + b) % 2 = (a % 2 + b % 2) % 2 := Nat.add_mod a b 2
  rw [this]
  have ha : a % 2 = 0 ∨ a % 2 = 1 := by omega
  have hb : b % 2 = 0 ∨ b % 2 = 1 := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

private lemma xorAll_xor (f g : Sym → Bool) :
    xorAll (fun s => xor (f s) (g s)) = xor (xorAll f) (xorAll g) := by
  simp only [xorAll]
  generalize f ![false, false, false] = a0; generalize g ![false, false, false] = b0
  generalize f ![false, false, true] = a1; generalize g ![false, false, true] = b1
  generalize f ![false, true, false] = a2; generalize g ![false, true, false] = b2
  generalize f ![false, true, true] = a3; generalize g ![false, true, true] = b3
  generalize f ![true, false, false] = a4; generalize g ![true, false, false] = b4
  generalize f ![true, false, true] = a5; generalize g ![true, false, true] = b5
  generalize f ![true, true, false] = a6; generalize g ![true, true, false] = b6
  generalize f ![true, true, true] = a7; generalize g ![true, true, true] = b7
  have hcomm : ∀ x y z w : Bool, xor (xor x y) (xor z w) = xor (xor x z) (xor y w) := by decide
  have h4 : ∀ x0 y0 x1 y1 x2 y2 x3 y3 : Bool,
      xor (xor (xor x0 y0) (xor x1 y1)) (xor (xor x2 y2) (xor x3 y3)) =
      xor (xor (xor x0 x1) (xor x2 x3)) (xor (xor y0 y1) (xor y2 y3)) := by decide
  rw [h4 a0 b0 a1 b1 a2 b2 a3 b3, h4 a4 b4 a5 b5 a6 b6 a7 b7, hcomm]

private lemma xorAll_monomial_le_two (mon : Finset (Fin 3)) (hcard : mon.card ≤ 2) :
    xorAll (fun s => decide (∀ c ∈ mon, s c = true)) = false := by
  revert mon hcard
  decide

private lemma low_imp_xorAll_false {f : Sym → Bool} (hf : isLow f) : xorAll f = false := by
  obtain ⟨M, hMcard, hMf⟩ := hf
  have hfun : f = fun s => parBool ((M.filter (fun mon => ∀ c ∈ mon, s c = true)).card) :=
    funext hMf
  rw [hfun]
  clear hMf hfun
  induction M using Finset.induction_on with
  | empty => decide
  | insert a S ha ih =>
    have hS : ∀ mon ∈ S, mon.card ≤ 2 := fun mon hm => hMcard mon (Finset.mem_insert_of_mem hm)
    have ha_card : a.card ≤ 2 := hMcard a (Finset.mem_insert_self a S)
    have hsplit : (fun s : Sym => parBool (((insert a S).filter (fun mon => ∀ c ∈ mon, s c = true)).card)) =
        fun s : Sym => xor (decide (∀ c ∈ a, s c = true))
          (parBool ((S.filter (fun mon => ∀ c ∈ mon, s c = true)).card)) := by
      funext s
      rw [Finset.filter_insert]
      split_ifs with h
      · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), parBool_add,
          decide_eq_true h]
        cases parBool (S.filter (fun mon => ∀ c ∈ mon, s c = true)).card <;> rfl
      · simp [h]
    rw [hsplit, xorAll_xor, xorAll_monomial_le_two a ha_card, ih hS]
    rfl

private lemma isLow_xor {f g : Sym → Bool} (hf : isLow f) (hg : isLow g) :
    isLow (fun s => xor (f s) (g s)) := by
  obtain ⟨Mf, hMf_card, hMf⟩ := hf
  obtain ⟨Mg, hMg_card, hMg⟩ := hg
  refine ⟨symmDiff Mf Mg, ?_, ?_⟩
  · intro mon hm
    rw [Finset.mem_symmDiff] at hm
    rcases hm with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact hMf_card mon h1
    · exact hMg_card mon h2
  · intro s
    dsimp only
    rw [hMf s, hMg s]
    set P : Finset (Fin 3) → Prop := fun mon => ∀ c ∈ mon, s c = true
    have hsd : ((symmDiff Mf Mg).filter P).card + 2 * ((Mf ∩ Mg).filter P).card =
        (Mf.filter P).card + (Mg.filter P).card := by
      have h1 : (Mf.filter P) = ((Mf \ Mg).filter P) ∪ ((Mf ∩ Mg).filter P) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have h2 : (Mg.filter P) = ((Mg \ Mf).filter P) ∪ ((Mf ∩ Mg).filter P) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        tauto
      have h3 : (symmDiff Mf Mg).filter P = ((Mf \ Mg).filter P) ∪ ((Mg \ Mf).filter P) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
        tauto
      have hd1 : Disjoint ((Mf \ Mg).filter P) ((Mf ∩ Mg).filter P) :=
        Finset.disjoint_left.mpr fun x hx1 hx2 =>
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2
            (Finset.mem_inter.mp (Finset.mem_filter.mp hx2).1).2
      have hd2 : Disjoint ((Mg \ Mf).filter P) ((Mf ∩ Mg).filter P) :=
        Finset.disjoint_left.mpr fun x hx1 hx2 =>
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2
            (Finset.mem_inter.mp (Finset.mem_filter.mp hx2).1).1
      have hd3 : Disjoint ((Mf \ Mg).filter P) ((Mg \ Mf).filter P) :=
        Finset.disjoint_left.mpr fun x hx1 hx2 =>
          (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx1).1).2
            (Finset.mem_sdiff.mp (Finset.mem_filter.mp hx2).1).1
      rw [h1, h2, h3, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
        Finset.card_union_of_disjoint hd3]
      omega
    have hpar := congrArg parBool hsd
    rw [parBool_add, parBool_add] at hpar
    have h2 : parBool (2 * ((Mf ∩ Mg).filter P).card) = false := by
      simp [parBool]
    rw [h2, Bool.xor_false] at hpar
    exact hpar.symm

private lemma isLow_false : isLow (fun _ => false) :=
  ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), fun _ => rfl⟩

private lemma isLow_pair_diff (s0 : Sym) :
    isLow (fun s => xor (decide (s = s0)) (decide (s = fun _ => false))) := by
  have hcheck : ∀ b0 b1 b2 : Bool,
      let s0' : Sym := ![b0, b1, b2]
      ∃ M : Finset (Finset (Fin 3)),
        (∀ mon ∈ M, mon.card ≤ 2) ∧
        ∀ c0 c1 c2 : Bool,
          let s : Sym := ![c0, c1, c2]
          xor (decide (s = s0')) (decide (s = fun _ => false)) =
            parBool ((M.filter (fun mon => ∀ c ∈ mon, s c = true)).card) := by
    intro b0 b1 b2
    cases b0 <;> cases b1 <;> cases b2
    · exact ⟨∅, by decide, by decide⟩
    · exact ⟨{{0, 1}, {0}, {1}, ∅}, by decide, by decide⟩
    · exact ⟨{{0, 2}, {0}, {2}, ∅}, by decide, by decide⟩
    · exact ⟨{{0, 1}, {0, 2}, {0}, {1}, {2}, ∅}, by decide, by decide⟩
    · exact ⟨{{1, 2}, {1}, {2}, ∅}, by decide, by decide⟩
    · exact ⟨{{0, 1}, {1, 2}, {0}, {1}, {2}, ∅}, by decide, by decide⟩
    · exact ⟨{{0, 2}, {1, 2}, {0}, {1}, {2}, ∅}, by decide, by decide⟩
    · exact ⟨{{0, 1}, {0, 2}, {1, 2}, {0}, {1}, {2}, ∅}, by decide, by decide⟩
  obtain ⟨M, hMc, hMeq⟩ := hcheck (s0 0) (s0 1) (s0 2)
  have hs0 : s0 = ![s0 0, s0 1, s0 2] := by
    funext i; fin_cases i <;> rfl
  refine ⟨M, hMc, fun s => ?_⟩
  have hs : s = ![s 0, s 1, s 2] := by
    funext i; fin_cases i <;> rfl
  rw [hs, hs0]
  exact hMeq (s 0) (s 1) (s 2)

private lemma xorAll_false_imp_low {f : Sym → Bool} (hf : xorAll f = false) : isLow f := by
  let S : Finset Sym := (Finset.univ : Finset Sym).filter (fun s => f s = true)
  have hS_even : parBool S.card = false := by
    have hcard : ∀ g : Sym → Bool,
        parBool (((Finset.univ : Finset Sym).filter (fun s => g s = true)).card) = xorAll g := by
      intro g
      have hsum : ((Finset.univ : Finset Sym).filter (fun s => g s = true)).card =
          ∑ s : Sym, (g s).toNat := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => by cases g s <;> rfl
      rw [hsum]
      let e8 : Fin 8 ≃ Sym :=
        { toFun := fun a =>
            match a.val with
            | 0 => ![false, false, false]
            | 1 => ![false, false, true]
            | 2 => ![false, true, false]
            | 3 => ![false, true, true]
            | 4 => ![true, false, false]
            | 5 => ![true, false, true]
            | 6 => ![true, true, false]
            | _ => ![true, true, true]
          invFun := fun s => ⟨4 * (s 0).toNat + 2 * (s 1).toNat + (s 2).toNat, by
            cases s 0 <;> cases s 1 <;> cases s 2 <;> decide⟩
          left_inv := fun a => by fin_cases a <;> decide
          right_inv := fun s => by
            funext v
            have hs : s = ![s 0, s 1, s 2] := by funext i; fin_cases i <;> rfl
            rw [hs]
            fin_cases v <;> cases s 0 <;> cases s 1 <;> cases s 2 <;> decide }
      rw [← Equiv.sum_comp e8, Fin.sum_univ_eight]
      simp only [e8, Equiv.coe_fn_mk, Fin.val_zero, Fin.val_one, Fin.val_two, parBool_add, xorAll]
      have htb : ∀ b : Bool, parBool b.toNat = b := fun b => by cases b <;> rfl
      simp only [htb]
      generalize g ![false, false, false] = b0
      generalize g ![false, false, true] = b1
      generalize g ![false, true, false] = b2
      generalize g ![false, true, true] = b3
      generalize g ![true, false, false] = b4
      generalize g ![true, false, true] = b5
      generalize g ![true, true, false] = b6
      generalize g ![true, true, true] = b7
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
        cases b4 <;> cases b5 <;> cases b6 <;> cases b7 <;> rfl
    rw [hcard, hf]
  have hfold : ∀ (T : Finset Sym),
      isLow (fun s => parBool ((T.filter (fun t => t = s)).card) |>
        fun b => xor b (if s = (fun _ => false) then parBool T.card else false)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      simpa [parBool] using isLow_false
    | insert a T ha ih =>
      have heq : (fun s : Sym => xor (parBool (((insert a T).filter (fun t => t = s)).card))
          (if s = (fun _ => false) then parBool (insert a T).card else false)) =
          fun s : Sym => xor
            (xor (decide (s = a)) (decide (s = fun _ => false)))
            (xor (parBool ((T.filter (fun t => t = s)).card))
              (if s = (fun _ => false) then parBool T.card else false)) := by
        funext s
        rw [Finset.filter_insert, Finset.card_insert_of_notMem ha, parBool_add]
        by_cases hsa : a = s
        · subst hsa
          rw [if_pos rfl, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1),
            parBool_add]
          by_cases hs0 : a = (fun _ => false) <;> simp [hs0, parBool] <;>
            cases parBool (T.filter (fun t => t = a)).card <;> cases parBool T.card <;> rfl
        · rw [if_neg hsa]
          have hsne : s ≠ a := Ne.symm hsa
          by_cases hs0 : s = (fun _ => false)
          · have h0ne : (fun _ => false) ≠ a := hs0 ▸ hsne
            have hp1 : parBool 1 = true := rfl
            simp only [hs0, ↓reduceIte, decide_true, decide_eq_false h0ne, hp1]
            cases parBool (T.filter (fun t => t = fun _ => false)).card <;>
              cases parBool T.card <;> rfl
          · simp only [hs0, ↓reduceIte, decide_false, decide_eq_false hsne]
            cases parBool (T.filter (fun t => t = s)).card <;>
              cases parBool T.card <;> rfl
      rw [heq]
      exact isLow_xor (isLow_pair_diff a) ih
  have hS := hfold S
  have hf_eq : f = fun s => xor (parBool ((S.filter (fun t => t = s)).card))
      (if s = (fun _ => false) then parBool S.card else false) := by
    funext s
    rw [hS_even]
    simp only [ite_self, Bool.xor_false]
    by_cases hfs : f s = true
    · have hsS : s ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfs⟩
      have hfilt : S.filter (fun t => t = s) = {s} := by
        ext t; simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨h ▸ hsS, h⟩⟩
      rw [hfilt, Finset.card_singleton, hfs]; rfl
    · have hfs0 : f s = false := Bool.eq_false_iff.mpr hfs
      have hsS : s ∉ S := fun hm => hfs (Finset.mem_filter.mp hm).2
      have hfilt : S.filter (fun t => t = s) = ∅ := by
        ext t; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        rintro ⟨ht, rfl⟩; exact hsS ht
      rw [hfilt, Finset.card_empty, hfs0]; rfl
  rwa [hf_eq]

private lemma low_misses_symbol {F g : Sym → Bool} (hF : xorAll F = true) (hg : isLow g) :
    ∃ s0 : Sym, g s0 ≠ F s0 := by
  by_contra hall
  push Not at hall
  have hfg : g = F := funext hall
  have h1 := low_imp_xorAll_false hg
  rw [hfg, hF] at h1
  exact Bool.noConfusion h1

private lemma low_flipAt {F : Sym → Bool} (hF : xorAll F = true) (s0 : Sym) :
    isLow (fun s => if s = s0 then !(F s) else F s) := by
  apply xorAll_false_imp_low
  have heq : (fun s => if s = s0 then !(F s) else F s) =
      fun s => xor (F s) (decide (s = s0)) := by
    funext s
    by_cases h : s = s0 <;> simp [h]
  rw [heq, xorAll_xor, hF]
  have hind : xorAll (fun s => decide (s = s0)) = true := by
    have hs0 : s0 = ![s0 0, s0 1, s0 2] := by funext i; fin_cases i <;> rfl
    rw [hs0]
    cases s0 0 <;> cases s0 1 <;> cases s0 2 <;> decide
  rw [hind]
  rfl

private def symEquiv : Fin 8 ≃ Sym where
  toFun a v := a.val.testBit v.val
  invFun s := ⟨(s 0).toNat + 2 * (s 1).toNat + 4 * (s 2).toNat, by
    cases s 0 <;> cases s 1 <;> cases s 2 <;> decide⟩
  left_inv a := by fin_cases a <;> decide
  right_inv s := by
    funext v
    have hs : s = ![s 0, s 1, s 2] := by funext i; fin_cases i <;> rfl
    rw [hs]
    fin_cases v <;> cases s 0 <;> cases s 1 <;> cases s 2 <;> decide

private def missCount (r k : Nat) : Nat :=
  ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun w =>
    ∀ a : Fin k, ∃ j : Fin r, (w j).val = a.val)).card

private lemma missCount_zero_zero : missCount 0 0 = 1 := by
  decide

private lemma missCount_zero_succ (k : Nat) : missCount 0 (k + 1) = 0 := by
  simp only [missCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _ h
  obtain ⟨j, _⟩ := h ⟨0, Nat.succ_pos k⟩
  exact j.elim0

private lemma missCount_succ_zero (r : Nat) : missCount (r + 1) 0 = 8 * missCount r 0 := by
  unfold missCount
  rw [Finset.filter_eq_self.mpr (fun _ _ a => a.elim0),
      Finset.filter_eq_self.mpr (fun _ _ a => a.elim0),
      Finset.card_univ, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin,
      Nat.pow_succ, Nat.mul_comm]

private lemma missCount_eq_perm {r k : Nat} (hk : k ≤ 8) (S : Finset (Fin 8)) (hS : S.card = k) :
    ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun w =>
      ∀ v ∈ S, ∃ j : Fin r, w j = v)).card = missCount r k := by
  let T : Finset (Fin 8) := (Finset.univ : Finset (Fin 8)).filter (fun v => v.val < k)
  have hT : T.card = k := by
    have hbij : T.card = (Finset.univ : Finset (Fin k)).card := by
      refine Finset.card_bij (fun v hv => (⟨v.val, (Finset.mem_filter.mp hv).2⟩ : Fin k)) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (congrArg (fun x : Fin k => x.val) h)
      · intro a _
        refine ⟨⟨a.val, lt_of_lt_of_le a.isLt hk⟩, ?_, Fin.ext rfl⟩
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact a.isLt
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  have hSc : Sᶜ.card = Tᶜ.card := by
    rw [Finset.card_compl, Finset.card_compl, hS, hT]
  have e1 : S ≃ T := Fintype.equivOfCardEq (by simp [hS, hT])
  have e2 : (Sᶜ : Finset (Fin 8)) ≃ (Tᶜ : Finset (Fin 8)) :=
    Fintype.equivOfCardEq (by simp [hS, hT])
  let σ : Fin 8 ≃ Fin 8 :=
    { toFun := fun v => if hv : v ∈ S then (e1 ⟨v, hv⟩).1 else (e2 ⟨v, Finset.mem_compl.mpr hv⟩).1
      invFun := fun v => if hv : v ∈ T then (e1.symm ⟨v, hv⟩).1 else (e2.symm ⟨v, Finset.mem_compl.mpr hv⟩).1
      left_inv := fun v => by
        by_cases hv : v ∈ S
        · simp only [hv, ↓reduceDIte, (e1 ⟨v, hv⟩).2]
          exact congrArg Subtype.val (e1.symm_apply_apply ⟨v, hv⟩)
        · have hnot : (e2 ⟨v, Finset.mem_compl.mpr hv⟩).1 ∉ T :=
            Finset.mem_compl.mp (e2 ⟨v, Finset.mem_compl.mpr hv⟩).2
          simp only [hv, hnot, ↓reduceDIte]
          exact congrArg Subtype.val (e2.symm_apply_apply ⟨v, Finset.mem_compl.mpr hv⟩)
      right_inv := fun v => by
        by_cases hv : v ∈ T
        · simp only [hv, ↓reduceDIte, (e1.symm ⟨v, hv⟩).2]
          exact congrArg Subtype.val (e1.apply_symm_apply ⟨v, hv⟩)
        · have hnot : (e2.symm ⟨v, Finset.mem_compl.mpr hv⟩).1 ∉ S :=
            Finset.mem_compl.mp (e2.symm ⟨v, Finset.mem_compl.mpr hv⟩).2
          simp only [hv, hnot, ↓reduceDIte]
          exact congrArg Subtype.val (e2.apply_symm_apply ⟨v, Finset.mem_compl.mpr hv⟩) }
  have hσ_mem : ∀ v : Fin 8, σ v ∈ T ↔ v ∈ S := by
    intro v
    by_cases hv : v ∈ S
    · simp only [σ, Equiv.coe_fn_mk, hv, ↓reduceDIte, iff_true]; exact (e1 ⟨v, hv⟩).2
    · simp only [σ, Equiv.coe_fn_mk, hv, ↓reduceDIte, iff_false]
      exact Finset.mem_compl.mp (e2 ⟨v, Finset.mem_compl.mpr hv⟩).2
  unfold missCount
  refine Finset.card_bij (fun w _ => fun j => σ (w j)) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro a
    let t : Fin 8 := ⟨a.val, lt_of_lt_of_le a.isLt hk⟩
    have htT : t ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isLt⟩
    have hinvS : σ.symm t ∈ S := (hσ_mem (σ.symm t)).mp (by simpa using htT)
    obtain ⟨j, hj⟩ := hw (σ.symm t) hinvS
    refine ⟨j, ?_⟩
    rw [hj, σ.apply_symm_apply]
  · intro w1 _ w2 _ h
    funext j
    exact σ.injective (congrFun h j)
  · intro w' hw'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw'
    refine ⟨fun j => σ.symm (w' j), ?_, funext fun j => σ.apply_symm_apply (w' j)⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro v hvS
    have hσT : σ v ∈ T := (hσ_mem v).mpr hvS
    have hlt : (σ v).val < k := (Finset.mem_filter.mp hσT).2
    obtain ⟨j, hj⟩ := hw' ⟨(σ v).val, hlt⟩
    refine ⟨j, ?_⟩
    have hEq : w' j = σ v := Fin.ext hj
    rw [hEq, σ.symm_apply_apply]

private lemma missCount_succ_succ (r k : Nat) (hk : k + 1 ≤ 8) :
    missCount (r + 1) (k + 1) = (k + 1) * missCount r k + (7 - k) * missCount r (k + 1) := by
  let g : (Fin (r + 1) → Fin 8) → Fin 8 × (Fin r → Fin 8) := fun w => (w 0, fun j => w j.succ)
  have hbij : missCount (r + 1) (k + 1) =
      ∑ v : Fin 8, ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun rest =>
        ∀ a : Fin (k + 1), v.val = a.val ∨ ∃ j : Fin r, (rest j).val = a.val)).card := by
    have h1 : missCount (r + 1) (k + 1) =
        ((Finset.univ : Finset (Fin 8 × (Fin r → Fin 8))).filter (fun p =>
          ∀ a : Fin (k + 1), p.1.val = a.val ∨ ∃ j : Fin r, (p.2 j).val = a.val)).card := by
      refine Finset.card_bij (fun w _ => g w) ?_ ?_ ?_
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, g] at hw ⊢
        intro a
        obtain ⟨j, hj⟩ := hw a
        refine Fin.cases ?_ (fun j' => ?_) j hj
        · intro h0; exact Or.inl h0
        · intro hs; exact Or.inr ⟨j', hs⟩
      · intro w1 _ w2 _ h
        funext j
        refine Fin.cases ?_ (fun j' => ?_) j
        · exact congrArg Prod.fst h
        · exact congrFun (congrArg Prod.snd h) j'
      · rintro ⟨v, rest⟩ hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        refine ⟨Fin.cons v rest, ?_, by ext <;> simp [g]⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro a
        rcases hp a with hv | ⟨j, hj⟩
        · exact ⟨0, hv⟩
        · exact ⟨j.succ, hj⟩
    rw [h1, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [hbij]
  have hterm : ∀ v : Fin 8,
      ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun rest =>
        ∀ a : Fin (k + 1), v.val = a.val ∨ ∃ j : Fin r, (rest j).val = a.val)).card =
      if v.val < k + 1 then missCount r k else missCount r (k + 1) := by
    intro v
    split_ifs with hv
    · let S : Finset (Fin 8) := ((Finset.univ : Finset (Fin 8)).filter (fun u => u.val < k + 1)).erase v
      have hScard : S.card = k := by
        have hT : ((Finset.univ : Finset (Fin 8)).filter (fun u => u.val < k + 1)).card = k + 1 := by
          have hbijT : ((Finset.univ : Finset (Fin 8)).filter (fun u => u.val < k + 1)).card =
              (Finset.univ : Finset (Fin (k + 1))).card := by
            refine Finset.card_bij (fun u hu => (⟨u.val, (Finset.mem_filter.mp hu).2⟩ : Fin (k + 1))) ?_ ?_ ?_
            · intro _ _; exact Finset.mem_univ _
            · intro a _ b _ h; exact Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) h)
            · intro a _
              refine ⟨⟨a.val, lt_of_lt_of_le a.isLt hk⟩, ?_, Fin.ext rfl⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact a.isLt
          rw [hbijT, Finset.card_univ, Fintype.card_fin]
        have hmemv : v ∈ (Finset.univ : Finset (Fin 8)).filter (fun u => u.val < k + 1) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
        rw [Finset.card_erase_of_mem hmemv, hT]
        omega
      rw [← missCount_eq_perm (by omega : k ≤ 8) S hScard]
      congr 1; ext rest
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, Finset.mem_erase]
      constructor
      · intro h u ⟨hne, hult⟩
        rcases h ⟨u.val, hult⟩ with hv' | ⟨j, hj⟩
        · exact absurd (Fin.ext hv'.symm) hne
        · exact ⟨j, Fin.ext hj⟩
      · intro h a
        by_cases hva : v.val = a.val
        · exact Or.inl hva
        · right
          let u : Fin 8 := ⟨a.val, lt_of_lt_of_le a.isLt hk⟩
          have huS : u ≠ v ∧ u.val < k + 1 := ⟨fun heq => hva (congrArg Fin.val heq).symm, a.isLt⟩
          obtain ⟨j, hj⟩ := h u huS
          exact ⟨j, congrArg Fin.val hj⟩
    · unfold missCount
      congr 1; ext rest
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h a
        rcases h a with hva | hrest
        · omega
        · exact hrest
      · intro h a; exact Or.inr (h a)
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have hc1 : ((Finset.univ : Finset (Fin 8)).filter (fun v => v.val < k + 1)).card = k + 1 := by
    have hbij1 : ((Finset.univ : Finset (Fin 8)).filter (fun v => v.val < k + 1)).card =
        (Finset.univ : Finset (Fin (k + 1))).card := by
      refine Finset.card_bij (fun u hu => (⟨u.val, (Finset.mem_filter.mp hu).2⟩ : Fin (k + 1))) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a _ b _ h; exact Fin.ext (congrArg (fun x : Fin (k + 1) => x.val) h)
      · intro a _
        refine ⟨⟨a.val, lt_of_lt_of_le a.isLt hk⟩, ?_, Fin.ext rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact a.isLt
    rw [hbij1, Finset.card_univ, Fintype.card_fin]
  have hc2 : ((Finset.univ : Finset (Fin 8)).filter (fun v => ¬ v.val < k + 1)).card = 7 - k := by
    have htot := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 8))) (p := fun v => v.val < k + 1)
    rw [Finset.card_univ, Fintype.card_fin, hc1] at htot
    omega
  rw [hc1, hc2]

private lemma missCount_convex (r : Nat) :
    ∀ t, t + 2 ≤ 8 →
      (missCount r (t + 1) : Int) - (missCount r (t + 2) : Int) ≤
        (missCount r t : Int) - (missCount r (t + 1) : Int) := by
  induction r with
  | zero =>
    intro t ht
    cases t with
    | zero =>
      simp [missCount_zero_zero, missCount_zero_succ]
    | succ t =>
      simp [missCount_zero_succ]
  | succ r ih =>
    intro t ht
    cases t with
    | zero =>
      have h0 : (missCount (r + 1) 0 : Int) = 8 * (missCount r 0 : Int) := by
        exact_mod_cast missCount_succ_zero r
      have h1 : (missCount (r + 1) 1 : Int) = 1 * (missCount r 0 : Int) + 7 * (missCount r 1 : Int) := by
        exact_mod_cast missCount_succ_succ r 0 (by omega)
      have h2 : (missCount (r + 1) 2 : Int) = 2 * (missCount r 1 : Int) + 6 * (missCount r 2 : Int) := by
        exact_mod_cast missCount_succ_succ r 1 (by omega)
      have ih0 := ih 0 (by omega)
      linarith
    | succ t =>
      have h0 : (missCount (r + 1) (t + 1) : Int) =
          (t + 1 : Int) * (missCount r t : Int) + (7 - t : Int) * (missCount r (t + 1) : Int) := by
        have h := congrArg (Nat.cast (R := Int)) (missCount_succ_succ r t (by omega))
        have hsub : ((7 - t : Nat) : Int) = 7 - (t : Int) := by omega
        push_cast [hsub] at h
        linarith
      have h1 : (missCount (r + 1) (t + 2) : Int) =
          (t + 2 : Int) * (missCount r (t + 1) : Int) + (6 - t : Int) * (missCount r (t + 2) : Int) := by
        have h := congrArg (Nat.cast (R := Int)) (missCount_succ_succ r (t + 1) (by omega))
        have hsub : ((6 - t : Nat) : Int) = 6 - (t : Int) := by omega
        push_cast [hsub] at h
        linarith
      have h2 : (missCount (r + 1) (t + 3) : Int) =
          (t + 3 : Int) * (missCount r (t + 2) : Int) + (5 - t : Int) * (missCount r (t + 3) : Int) := by
        have h := congrArg (Nat.cast (R := Int)) (missCount_succ_succ r (t + 2) (by omega))
        have hsub : ((5 - t : Nat) : Int) = 5 - (t : Int) := by omega
        push_cast [hsub] at h
        linarith
      have ih1 := ih t (by omega)
      have ih2 := ih (t + 1) (by omega)
      have ht_nonneg : (0 : Int) ≤ (t + 1 : Int) := by omega
      have h5t_nonneg : (0 : Int) ≤ (5 - t : Int) := by omega
      nlinarith

private lemma missCount_antitone_diff (r a b : Nat) (hab : a ≤ b) (hb : b + 1 ≤ 8) :
    (missCount r b : Int) - (missCount r (b + 1) : Int) ≤
      (missCount r a : Int) - (missCount r (a + 1) : Int) := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; exact le_rfl
  | succ b ih =>
    by_cases h : a = b + 1
    · subst h; exact le_rfl
    · have hab' : a ≤ b := by omega
      exact le_trans (missCount_convex r b (by omega)) (ih hab' (by omega))

private lemma missCount_sub_ge (r k c : Nat) (hck : c ≤ k) (hk : k ≤ 8) :
    (c : Int) * ((missCount r (k - 1) : Int) - (missCount r k : Int)) ≤
      (missCount r (k - c) : Int) - (missCount r k : Int) := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hck' : c ≤ k := by omega
    have h1 := ih hck'
    have h2 := missCount_antitone_diff r (k - (c + 1)) (k - 1) (by omega) (by omega)
    have heq1 : k - (c + 1) + 1 = k - c := by omega
    have heq2 : k - 1 + 1 = k := by omega
    rw [heq1, heq2] at h2
    push_cast
    linarith

private lemma missed_le_card_bad (r : Nat) :
    ∀ (k : Nat) (_hk : k ≤ 8) (bad : Fin k → Fin r → Fin 8),
      missCount r k ≤
        ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun w =>
          ∀ a : Fin k, ∃ j : Fin r, w j = bad a j)).card := by
  induction r with
  | zero =>
    intro k hk bad
    cases k with
    | zero =>
      rw [missCount_zero_zero]
      have : ((Finset.univ : Finset (Fin 0 → Fin 8)).filter (fun w =>
          ∀ a : Fin 0, ∃ j : Fin 0, w j = bad a j)).card = 1 := by
        rw [Finset.filter_eq_self.mpr (fun _ _ a => a.elim0)]
        simp
      omega
    | succ k =>
      rw [missCount_zero_succ]
      exact Nat.zero_le _
  | succ r ih =>
    intro k hk bad
    cases k with
    | zero =>
      unfold missCount
      rw [Finset.filter_eq_self.mpr (fun _ _ a => a.elim0),
          Finset.filter_eq_self.mpr (fun _ _ a => a.elim0)]
    | succ k =>
      let g : (Fin (r + 1) → Fin 8) → Fin 8 × (Fin r → Fin 8) := fun w => (w 0, fun j => w j.succ)
      have hsplit :
          ((Finset.univ : Finset (Fin (r + 1) → Fin 8)).filter (fun w =>
            ∀ a : Fin (k + 1), ∃ j : Fin (r + 1), w j = bad a j)).card =
          ∑ v : Fin 8, ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun rest =>
            ∀ a : Fin (k + 1), bad a 0 ≠ v → ∃ j : Fin r, rest j = bad a j.succ)).card := by
        have h1 :
            ((Finset.univ : Finset (Fin (r + 1) → Fin 8)).filter (fun w =>
              ∀ a : Fin (k + 1), ∃ j : Fin (r + 1), w j = bad a j)).card =
            ((Finset.univ : Finset (Fin 8 × (Fin r → Fin 8))).filter (fun p =>
              ∀ a : Fin (k + 1), bad a 0 ≠ p.1 → ∃ j : Fin r, p.2 j = bad a j.succ)).card := by
          refine Finset.card_bij (fun w _ => g w) ?_ ?_ ?_
          · intro w hw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, g] at hw ⊢
            intro a hne
            obtain ⟨j, hj⟩ := hw a
            refine Fin.cases ?_ (fun j' => ?_) j hj
            · intro h0; exact absurd h0.symm hne
            · intro hs; exact ⟨j', hs⟩
          · intro w1 _ w2 _ h
            funext j
            refine Fin.cases ?_ (fun j' => ?_) j
            · exact congrArg Prod.fst h
            · exact congrFun (congrArg Prod.snd h) j'
          · rintro ⟨v, rest⟩ hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
            refine ⟨Fin.cons v rest, ?_, by ext <;> simp [g]⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro a
            by_cases hv : bad a 0 = v
            · exact ⟨0, hv.symm⟩
            · obtain ⟨j, hj⟩ := hp a hv
              exact ⟨j.succ, hj⟩
        rw [h1, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [hsplit]
      let c : Fin 8 → Nat := fun v =>
        ((Finset.univ : Finset (Fin (k + 1))).filter (fun a => bad a 0 = v)).card
      have hc_le : ∀ v : Fin 8, c v ≤ k + 1 := fun v => by
        calc c v ≤ (Finset.univ : Finset (Fin (k + 1))).card := Finset.card_filter_le _ _
          _ = k + 1 := by simp
      have hc_sum : ∑ v : Fin 8, c v = k + 1 := by
        have := Finset.card_eq_sum_card_fiberwise (f := fun a : Fin (k + 1) => bad a 0)
          (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
        simpa [c] using this.symm
      have hterm_ge : ∀ v : Fin 8,
          missCount r (k + 1 - c v) ≤
            ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun rest =>
              ∀ a : Fin (k + 1), bad a 0 ≠ v → ∃ j : Fin r, rest j = bad a j.succ)).card := by
        intro v
        let rem : Finset (Fin (k + 1)) :=
          (Finset.univ : Finset (Fin (k + 1))).filter (fun a => bad a 0 ≠ v)
        have hrem_card : rem.card = k + 1 - c v := by
          have htot := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin (k + 1)))) (p := fun a => bad a 0 = v)
          rw [Finset.card_univ, Fintype.card_fin] at htot
          change c v + rem.card = k + 1 at htot
          omega
        let e : Fin (k + 1 - c v) ≃ rem := Fintype.equivOfCardEq (by simp [hrem_card])
        have hih := ih (k + 1 - c v) (by omega) (fun b j => bad (e b).1 j.succ)
        refine le_trans hih (le_of_eq ?_)
        congr 1; ext rest
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h a ha
          have ha_rem : a ∈ rem := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
          obtain ⟨j, hj⟩ := h (e.symm ⟨a, ha_rem⟩)
          refine ⟨j, ?_⟩
          simpa using hj
        · intro h b
          exact h (e b).1 (Finset.mem_filter.mp (e b).2).2
      have hsum_ge : ∑ v : Fin 8, missCount r (k + 1 - c v) ≤
          ∑ v : Fin 8, ((Finset.univ : Finset (Fin r → Fin 8)).filter (fun rest =>
            ∀ a : Fin (k + 1), bad a 0 ≠ v → ∃ j : Fin r, rest j = bad a j.succ)).card :=
        Finset.sum_le_sum fun v _ => hterm_ge v
      refine le_trans ?_ hsum_ge
      rw [missCount_succ_succ r k hk]
      have hint : ((k + 1) * missCount r k + (7 - k) * missCount r (k + 1) : Int) ≤
          ∑ v : Fin 8, (missCount r (k + 1 - c v) : Int) := by
        have hsub : ∀ v : Fin 8,
            (c v : Int) * ((missCount r k : Int) - (missCount r (k + 1) : Int)) ≤
              (missCount r (k + 1 - c v) : Int) - (missCount r (k + 1) : Int) := fun v => by
          simpa using missCount_sub_ge r (k + 1) (c v) (hc_le v) hk
        have hsum_sub := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 8))) (fun v _ => hsub v)
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul] at hsum_sub
        have hcsum_int : (∑ v : Fin 8, (c v : Int)) = (k + 1 : Int) := by exact_mod_cast hc_sum
        rw [hcsum_int] at hsum_sub
        have h8 : ((8 : Nat) : Int) = 8 := rfl
        rw [h8] at hsum_sub
        have h7k : ((7 - k : Nat) : Int) = 7 - (k : Int) := by omega
        linarith
      have hint' : (((k + 1) * missCount r k + (7 - k) * missCount r (k + 1) : Nat) : Int) ≤
          ((∑ v : Fin 8, missCount r (k + 1 - c v) : Nat) : Int) := by
        have h7k : ((7 - k : Nat) : Int) = 7 - (k : Int) := by omega
        push_cast [h7k]
        exact hint
      exact_mod_cast hint'

private lemma exists_surjective_block_proj (m : Nat) :
    ∀ (d : Nat) (Φ : (Fin m → Fin 3 → Z2) →ₗ[Z2] (Fin d → Z2)),
      ∃ J : Finset (Fin m), J.card = m - d ∧
        Function.Surjective (fun x : LinearMap.ker Φ => fun i : J => x.1 i.1) := by
  intro d
  induction d with
  | zero =>
    intro Φ
    refine ⟨Finset.univ, by simp, ?_⟩
    intro y
    refine ⟨⟨fun i => y ⟨i, Finset.mem_univ i⟩, ?_⟩, ?_⟩
    · ext u; exact u.elim0
    · funext i; rfl
  | succ d ih =>
    intro Φ
    let Φ0 : (Fin m → Fin 3 → Z2) →ₗ[Z2] (Fin d → Z2) :=
      { toFun := fun x u => Φ x u.castSucc
        map_add' := fun x y => by funext u; simp
        map_smul' := fun c x => by funext u; simp }
    let ℓ : (Fin m → Fin 3 → Z2) →ₗ[Z2] Z2 :=
      { toFun := fun x => Φ x (Fin.last d)
        map_add' := fun x y => by simp
        map_smul' := fun c x => by simp }
    obtain ⟨J0, hJ0_card, hJ0_surj⟩ := ih Φ0
    by_cases hmd : m ≤ d
    · refine ⟨∅, by simp; omega, ?_⟩
      intro y
      refine ⟨0, ?_⟩
      funext i
      exact absurd i.2 (Finset.notMem_empty _)
    · have hJ0_pos : 0 < J0.card := by omega
      have hker_iff : ∀ x, x ∈ LinearMap.ker Φ ↔ x ∈ LinearMap.ker Φ0 ∧ ℓ x = 0 := by
        intro x
        simp only [LinearMap.mem_ker, Φ0, ℓ, LinearMap.coe_mk, AddHom.coe_mk]
        constructor
        · intro h
          refine ⟨funext fun u => congrFun h u.castSucc, congrFun h (Fin.last d)⟩
        · rintro ⟨h0, hl⟩
          funext u
          refine Fin.lastCases hl (fun u' => congrFun h0 u') u
      by_cases hex : ∃ z : LinearMap.ker Φ0, (∀ i ∈ J0, z.1 i = 0) ∧ ℓ z.1 = 1
      · obtain ⟨z, hz0, hz1⟩ := hex
        obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hJ0_pos
        refine ⟨J0.erase i0, by rw [Finset.card_erase_of_mem hi0, hJ0_card]; omega, ?_⟩
        intro y
        let y0 : J0 → Fin 3 → Z2 := fun i =>
          if hi : i.1 = i0 then 0 else y ⟨i.1, Finset.mem_erase.mpr ⟨hi, i.2⟩⟩
        obtain ⟨x, hx⟩ := hJ0_surj y0
        by_cases hlx : ℓ x.1 = 0
        · refine ⟨⟨x.1, (hker_iff x.1).mpr ⟨x.2, hlx⟩⟩, ?_⟩
          funext i
          have hne : i.1 ≠ i0 := (Finset.mem_erase.mp i.2).1
          have hiJ0 : i.1 ∈ J0 := (Finset.mem_erase.mp i.2).2
          have := congrFun hx ⟨i.1, hiJ0⟩
          simpa [y0, hne] using this
        · have hlx1 : ℓ x.1 = 1 := by
            generalize ℓ x.1 = a at hlx ⊢
            fin_cases a
            · exact absurd rfl hlx
            · rfl
          refine ⟨⟨x.1 + z.1, (hker_iff _).mpr ⟨Submodule.add_mem _ x.2 z.2, by
            rw [map_add, hlx1, hz1]; rfl⟩⟩, ?_⟩
          funext i
          have hne : i.1 ≠ i0 := (Finset.mem_erase.mp i.2).1
          have hiJ0 : i.1 ∈ J0 := (Finset.mem_erase.mp i.2).2
          have := congrFun hx ⟨i.1, hiJ0⟩
          simp only [Pi.add_apply, hz0 i.1 hiJ0, add_zero]
          simpa [y0, hne] using this
      · push Not at hex
        have hfact : ∀ x1 x2 : LinearMap.ker Φ0,
            (∀ i ∈ J0, x1.1 i = x2.1 i) → ℓ x1.1 = ℓ x2.1 := by
          intro x1 x2 heq
          have h0 : ∀ i ∈ J0, (x1 - x2).1 i = 0 := fun i hi => by
            simp [heq i hi]
          have hne1 : ℓ (x1 - x2).1 ≠ 1 := hex (x1 - x2) h0
          have hzero : ℓ (x1 - x2).1 = 0 := by
            generalize ℓ (x1 - x2).1 = a at hne1 ⊢
            fin_cases a
            · rfl
            · exact absurd rfl hne1
          simp only [Submodule.coe_sub, map_sub, sub_eq_zero] at hzero
          exact hzero
        by_cases htriv : ∀ x : LinearMap.ker Φ0, ℓ x.1 = 0
        · obtain ⟨i0, hi0⟩ := Finset.card_pos.mp hJ0_pos
          refine ⟨J0.erase i0, by rw [Finset.card_erase_of_mem hi0, hJ0_card]; omega, ?_⟩
          intro y
          let y0 : J0 → Fin 3 → Z2 := fun i =>
            if hi : i.1 = i0 then 0 else y ⟨i.1, Finset.mem_erase.mpr ⟨hi, i.2⟩⟩
          obtain ⟨x, hx⟩ := hJ0_surj y0
          refine ⟨⟨x.1, (hker_iff x.1).mpr ⟨x.2, htriv x⟩⟩, ?_⟩
          funext i
          have hne : i.1 ≠ i0 := (Finset.mem_erase.mp i.2).1
          have hiJ0 : i.1 ∈ J0 := (Finset.mem_erase.mp i.2).2
          have := congrFun hx ⟨i.1, hiJ0⟩
          simpa [y0, hne] using this
        · push Not at htriv
          obtain ⟨xbad, hxbad⟩ := htriv
          have hex_i0 : ∃ i0 : J0, ∃ v0 : Fin 3,
              ∃ z : LinearMap.ker Φ0,
                (fun i : J0 => z.1 i.1) = Pi.single i0 (Pi.single v0 (1 : Z2)) ∧ ℓ z.1 = 1 := by
            by_contra hnone
            push Not at hnone
            have hbasis_zero : ∀ (i0 : J0) (v0 : Fin 3),
                ∀ z : LinearMap.ker Φ0,
                  (fun i : J0 => z.1 i.1) = Pi.single i0 (Pi.single v0 (1 : Z2)) → ℓ z.1 = 0 := by
              intro i0 v0 z hz
              have hne1 := hnone i0 v0 z hz
              generalize ℓ z.1 = a at hne1 ⊢
              fin_cases a
              · rfl
              · exact absurd rfl hne1
            let liftBasis : J0 → Fin 3 → LinearMap.ker Φ0 := fun i0 v0 =>
              Classical.choose (hJ0_surj (Pi.single i0 (Pi.single v0 (1 : Z2))))
            have hlift_spec : ∀ (i0 : J0) (v0 : Fin 3),
                (fun i : J0 => (liftBasis i0 v0).1 i.1) = Pi.single i0 (Pi.single v0 (1 : Z2)) :=
              fun i0 v0 => Classical.choose_spec (hJ0_surj (Pi.single i0 (Pi.single v0 (1 : Z2))))
            let xsum : LinearMap.ker Φ0 :=
              ∑ i0 : J0, ∑ v0 : Fin 3, xbad.1 i0.1 v0 • liftBasis i0 v0
            have hxsum_eq : ∀ i ∈ J0, xbad.1 i = xsum.1 i := by
              intro i hi
              funext v
              simp only [xsum, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
                Pi.smul_apply, smul_eq_mul]
              rw [Finset.sum_eq_single (⟨i, hi⟩ : J0)]
              · rw [Finset.sum_eq_single v]
                · have := congrFun (congrFun (hlift_spec ⟨i, hi⟩ v) ⟨i, hi⟩) v
                  simp only [Pi.single_eq_same] at this
                  rw [this, mul_one]
                · intro v' _ hv'
                  have := congrFun (congrFun (hlift_spec ⟨i, hi⟩ v') ⟨i, hi⟩) v
                  simp only [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hv')] at this
                  rw [this, mul_zero]
                · intro h0; exact absurd (Finset.mem_univ v) h0
              · intro i' _ hi'
                refine Finset.sum_eq_zero fun v' _ => ?_
                have := congrFun (hlift_spec i' v') ⟨i, hi⟩
                simp only [Pi.single_eq_of_ne (Ne.symm hi')] at this
                rw [this]; simp
              · intro h0; exact absurd (Finset.mem_univ _) h0
            have hl_eq := hfact xbad xsum hxsum_eq
            have hl_xsum : ℓ xsum.1 = 0 := by
              simp only [xsum, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul]
              refine Finset.sum_eq_zero fun i0 _ => Finset.sum_eq_zero fun v0 _ => ?_
              rw [hbasis_zero i0 v0 (liftBasis i0 v0) (hlift_spec i0 v0), mul_zero]
            rw [hl_xsum] at hl_eq
            exact hxbad hl_eq
          obtain ⟨i0, v0, z, hz_proj, hz1⟩ := hex_i0
          refine ⟨J0.erase i0.1, by rw [Finset.card_erase_of_mem i0.2, hJ0_card]; omega, ?_⟩
          intro y
          let y0 : J0 → Fin 3 → Z2 := fun i =>
            if hi : i.1 = i0.1 then 0 else y ⟨i.1, Finset.mem_erase.mpr ⟨hi, i.2⟩⟩
          obtain ⟨x, hx⟩ := hJ0_surj y0
          have hz_zero_on : ∀ i : J0.erase i0.1, z.1 i.1 = 0 := by
            intro i
            have hne : (⟨i.1, (Finset.mem_erase.mp i.2).2⟩ : J0) ≠ i0 := fun h =>
              (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val h)
            have := congrFun hz_proj ⟨i.1, (Finset.mem_erase.mp i.2).2⟩
            simpa [Pi.single_eq_of_ne hne] using this
          by_cases hlx : ℓ x.1 = 0
          · refine ⟨⟨x.1, (hker_iff x.1).mpr ⟨x.2, hlx⟩⟩, ?_⟩
            funext i
            have hne : i.1 ≠ i0.1 := (Finset.mem_erase.mp i.2).1
            have hiJ0 : i.1 ∈ J0 := (Finset.mem_erase.mp i.2).2
            have hne' : (⟨i.1, hiJ0⟩ : J0) ≠ i0 := fun h => hne (congrArg Subtype.val h)
            have := congrFun hx ⟨i.1, hiJ0⟩
            simpa [y0, hne, hne'] using this
          · have hlx1 : ℓ x.1 = 1 := by
              generalize ℓ x.1 = a at hlx ⊢
              fin_cases a
              · exact absurd rfl hlx
              · rfl
            refine ⟨⟨x.1 + z.1, (hker_iff _).mpr ⟨Submodule.add_mem _ x.2 z.2, by
              rw [map_add, hlx1, hz1]; rfl⟩⟩, ?_⟩
            funext i
            have hne : i.1 ≠ i0.1 := (Finset.mem_erase.mp i.2).1
            have hiJ0 : i.1 ∈ J0 := (Finset.mem_erase.mp i.2).2
            have hne' : (⟨i.1, hiJ0⟩ : J0) ≠ i0 := fun h => hne (congrArg Subtype.val h)
            have := congrFun hx ⟨i.1, hiJ0⟩
            simp only [Pi.add_apply, hz_zero_on i, add_zero]
            simpa [y0, hne, hne'] using this

private def runFold {α : Type*} (steps : Nat) (ask : Nat → Nat → α → Bool) (x : α) : Nat :=
  (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0

private lemma runFold_lt {α : Type*} (steps : Nat) (ask : Nat → Nat → α → Bool) (x : α) :
    runFold steps ask x < 2 ^ steps := by
  induction steps with
  | zero => simp [runFold]
  | succ n ih =>
    simp only [runFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hbit : (ask n (runFold n ask x) x).toNat <<< n ≤ 2 ^ n := by
      cases ask n (runFold n ask x) x <;> simp [Nat.shiftLeft_eq]
    rw [Nat.pow_succ]
    change runFold n ask x + ((ask n (runFold n ask x) x).toNat <<< n) < 2 ^ n * 2
    omega

private lemma runFold_add {α : Type*} (d s : Nat) (ask : Nat → Nat → α → Bool) (x : α) :
    ∃ t : Fin (2 ^ s), runFold (d + s) ask x = runFold d ask x + (t.val <<< d) := by
  induction s with
  | zero =>
    refine ⟨⟨0, by omega⟩, ?_⟩
    simp [runFold]
  | succ s ih =>
    obtain ⟨t, ht⟩ := ih
    have hstep : runFold (d + (s + 1)) ask x =
        runFold (d + s) ask x + ((ask (d + s) (runFold (d + s) ask x) x).toNat <<< (d + s)) := by
      simp only [runFold, show d + (s + 1) = (d + s) + 1 by omega, List.range_succ,
        List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep, ht]
    let b := (ask (d + s) (runFold d ask x + (t.val <<< d)) x).toNat
    have hb : b ≤ 1 := by
      dsimp only [b]
      cases ask (d + s) (runFold d ask x + (t.val <<< d)) x <;> decide
    refine ⟨⟨t.val + b * 2 ^ s, by rw [Nat.pow_succ]; nlinarith [t.isLt]⟩, ?_⟩
    simp only [Nat.shiftLeft_eq, b]
    rw [Nat.pow_add]
    ring

private lemma add_two_pow_testBit {a n j : Nat} (ha : a < 2 ^ n) :
    (a + 2 ^ n).testBit j = (a.testBit j || decide (j = n)) := by
  by_cases hlt : j < n
  · have hsub : 1 ≤ n - j := by omega
    have hpow : 2 ^ n = 2 ^ j * 2 ^ (n - j) := by rw [← Nat.pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
    have hdiv : (a + 2 ^ n) / 2 ^ j = a / 2 ^ j + 2 ^ (n - j) := by
      rw [hpow, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j)]
    have heven : 2 ∣ 2 ^ (n - j) := dvd_pow_self 2 (by omega)
    obtain ⟨q, hq⟩ := heven
    simp only [Nat.testBit_eq_decide_div_mod_eq, hdiv, hq, Nat.add_mul_mod_self_left,
      show j ≠ n by omega, decide_false, Bool.or_false]
  · by_cases heq : j = n
    · subst heq
      have hdiv : (a + 2 ^ j) / 2 ^ j = 1 := by
        rw [Nat.add_div_right _ (Nat.two_pow_pos j), Nat.div_eq_of_lt ha]
      simp [Nat.testBit_eq_decide_div_mod_eq, hdiv]
    · have hgt : n + 1 ≤ j := by omega
      have hlt2 : a + 2 ^ n < 2 ^ j := by
        have h1 : a + 2 ^ n < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right Nat.zero_lt_two hgt)
      have ha2 : a < 2 ^ j := lt_of_lt_of_le ha (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))
      simp [Nat.testBit_lt_two_pow hlt2, Nat.testBit_lt_two_pow ha2, show j ≠ n by omega]

private lemma runFold_testBit {α : Type*} (steps : Nat) (ask : Nat → Nat → α → Bool) (x : α)
    (j : Nat) (hj : j < steps) :
    (runFold steps ask x).testBit j = ask j (runFold j ask x) x := by
  induction steps with
  | zero => omega
  | succ n ih =>
    have hstep : runFold (n + 1) ask x =
        runFold n ask x + ((ask n (runFold n ask x) x).toNat <<< n) := by
      simp only [runFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    have hlt := runFold_lt n ask x
    cases hbit : ask n (runFold n ask x) x
    · simp only [Bool.toNat_false, Nat.zero_shiftLeft, Nat.add_zero]
      by_cases hjn : j = n
      · subst hjn; rw [hbit]; exact Nat.testBit_lt_two_pow hlt
      · exact ih (by omega)
    · simp only [Bool.toNat_true, Nat.shiftLeft_eq, one_mul]
      rw [add_two_pow_testBit hlt]
      by_cases hjn : j = n
      · subst hjn; simp [hbit]
      · simp [hjn, ih (by omega)]

private lemma toZ2_parBool (n : Nat) :
    (if parBool n then (1 : Z2) else 0) = (n : Z2) := by
  simp only [parBool]
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hcast : (n : Z2) = ((n % 2 : Nat) : Z2) := by
    rw [← ZMod.natCast_mod n 2]
  rw [hcast]
  rcases hmod with h | h <;> simp [h]

private lemma card_filter_eq_sum_z2 {k : Nat} (mask : Finset (Fin k)) (v : Fin k → Z2) :
    ((mask.filter (fun b => v b = 1)).card : Z2) = ∑ b ∈ mask, v b := by
  induction mask using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.filter_insert, Finset.sum_insert ha]
    by_cases hv : v a = 1
    · rw [if_pos hv, Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1),
        Nat.cast_add, Nat.cast_one, ih, hv, add_comm]
    · have hv0 : v a = 0 := by
        generalize v a = x at hv ⊢
        fin_cases x
        · rfl
        · exact absurd rfl hv
      rw [if_neg hv, ih, hv0, zero_add]

private lemma bool_toZ2_xor (a b : Bool) :
    (if xor a b then (1 : Z2) else 0) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> rfl

private lemma bool_toZ2_inj (a b : Bool)
    (h : (if a then (1 : Z2) else 0) = (if b then 1 else 0)) : a = b := by
  cases a <;> cases b <;> simp_all

private lemma sum_two_pow_testBit : ∀ (n : Nat) (f : Fin n → Bool) (j : Nat),
    (∑ i : Fin n, (if f i then 2 ^ i.val else 0)).testBit j =
      if hj : j < n then f ⟨j, hj⟩ else false := by
  intro n
  induction n with
  | zero => intro f j; simp
  | succ n ih =>
    intro f j
    rw [Fin.sum_univ_castSucc]
    have hlt : ∑ i : Fin n, (if f i.castSucc then 2 ^ i.val else 0) < 2 ^ n := by
      have h1 : ∀ (m : Nat) (g : Fin m → Bool),
          ∑ i : Fin m, (if g i then 2 ^ i.val else 0) < 2 ^ m := by
        intro m; induction m with
        | zero => intro g; simp
        | succ m ihm =>
          intro g; rw [Fin.sum_univ_castSucc, Nat.pow_succ]
          have := ihm (fun i => g i.castSucc)
          have h2 : (if g (Fin.last m) then 2 ^ m else 0) ≤ 2 ^ m := by split_ifs <;> omega
          simp only [Fin.val_castSucc, Fin.val_last] at this ⊢
          omega
      exact h1 n (fun i => f i.castSucc)
    simp only [Fin.val_castSucc, Fin.val_last]
    cases hf : f (Fin.last n)
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, ih (fun i => f i.castSucc) j]
      by_cases hjn : j = n
      · subst hjn
        have hlast : (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) = Fin.last j := rfl
        simp [hlast, hf]
      · split_ifs with h1 h2
        · rfl
        · omega
        · omega
        · rfl
    · simp only [↓reduceIte]
      rw [add_two_pow_testBit hlt, ih (fun i => f i.castSucc) j]
      by_cases hjn : j = n
      · subst hjn
        have hlast : (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) = Fin.last j := rfl
        simp [hlast, hf]
      · split_ifs with h1 h2
        · simp [hjn]
        · omega
        · omega
        · simp [hjn]

private def finPowEquiv (k : Nat) : Fin (2 ^ k) ≃ (Fin k → Z2) where
  toFun q i := if q.val.testBit i.val then 1 else 0
  invFun v := ⟨∑ i : Fin k, (if v i = 1 then 2 ^ i.val else 0), by
    have hlt : ∀ (n : Nat) (f : Fin n → Z2),
        ∑ i : Fin n, (if f i = 1 then 2 ^ i.val else 0) < 2 ^ n := by
      intro n
      induction n with
      | zero => intro f; simp
      | succ n ih =>
        intro f
        rw [Fin.sum_univ_castSucc, Nat.pow_succ]
        have h1 := ih (fun i => f i.castSucc)
        have h2 : (if f (Fin.last n) = 1 then 2 ^ n else 0) ≤ 2 ^ n := by split_ifs <;> omega
        simp only [Fin.val_castSucc, Fin.val_last] at h1 ⊢
        omega
    exact hlt k v⟩
  left_inv q := by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    dsimp only
    have hconv : (∑ i : Fin k, if (if q.val.testBit i.val = true then (1 : Z2) else 0) = 1 then 2 ^ i.val else 0) =
        ∑ i : Fin k, if q.val.testBit i.val then 2 ^ i.val else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      cases q.val.testBit i.val <;> simp
    rw [hconv, sum_two_pow_testBit k (fun i => q.val.testBit i.val) j]
    split_ifs with hj
    · rfl
    · exact (Nat.testBit_lt_two_pow (q.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm
  right_inv v := by
    funext j
    change (if (∑ i : Fin k, if v i = 1 then 2 ^ i.val else 0).testBit j.val = true then (1 : Z2) else 0) = v j
    have hconv : (∑ i : Fin k, if v i = 1 then 2 ^ i.val else 0) =
        ∑ i : Fin k, if decide (v i = 1) then 2 ^ i.val else 0 := by
      refine Finset.sum_congr rfl fun i _ => by simp
    rw [hconv, sum_two_pow_testBit k (fun i => decide (v i = 1)) j.val, dif_pos j.isLt]
    generalize v j = a
    fin_cases a <;> rfl

private theorem main_aux :
  ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot0 := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step0 := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step0 (prev ^^^ rot0 1 prev ^^^ rot0 (k - 1) prev) ^^^ rot0 (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot0 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot0 (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k) →
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
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val)%k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val)%k) →
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let fiber := (Finset.univ : Finset K).filter (fun keyWord =>
    ∀ z ∈ pin, bit row.val 0 keyWord.val z.val = bit row.val 0 ref.val z.val)
  let run := fun (steps : Nat) (ask : Nat → Nat → K → Bool) (x : K) =>
    (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
  let out := fun (input : K) (i : Fin m) => bit row.val 2 input.val (starts i+5)
  let Symbol := Fin 3 → Bool
  let triple := fun (raw : K) (idx : Fin m) (v : Fin 3) =>
    bit row.val 0 raw.val (starts idx+9+v.val)
  let low := fun (f : Symbol → Bool) => ∃ monomials : Finset (Finset (Fin 3)),
    (∀ mon ∈ monomials, mon.card ≤ 2) ∧ ∀ symbol,
      f symbol = par ((monomials.filter (fun mon => ∀ coord ∈ mon, symbol coord = true)).card)
  ∀ (d s L : Nat), 2^s*L ≤ 8 →
    let res := m-d
    let Kslots := 2^s*L
    let missed := ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun residualWord =>
      ∀ a : Fin Kslots, ∃ j, (residualWord j).val = a.val)).card
    let affine := fun (ask : Nat → Nat → K → Bool) =>
      ∀ u : Fin d, ∀ path, ∃ (mask : Finset (Fin k)) (c : Bool), ∀ raw,
        ask u.val path raw = xor c (par ((mask.filter (fun b => bitOf raw b = true)).card))
    let listOK := fun (leaf : Nat → Fin L → Fin m → Symbol → Bool) =>
      ∀ history label i, low (leaf history label i)
    let hit := fun (ask : Nat → Nat → K → Bool)
        (leaf : Nat → Fin L → Fin m → Symbol → Bool) =>
      (fiber.filter (fun sample => ∃ a, ∀ i,
        leaf (run (d+s) ask sample) a i (triple sample i) = out sample i)).card
    ∀ H : Nat,
      (∃ ask leaf, affine ask ∧ listOK leaf ∧ H ≤ hit ask leaf) ↔
        8^res * H ≤ fiber.card * (8^res - missed) := by
  intro k hk_pos constant rot0 step0 state injected bit m starts hinj good row ref hgood
    pin hpin9 hpin3 K bitOf par fiber run out Symbol triple low d s L hKslots_le
    res Kslots missed affine listOK hit H
  by_cases hL0 : L = 0
  · subst hL0
    have hK0 : Kslots = 0 := by simp [Kslots]
    have hmissed : missed = 8 ^ res := by
      dsimp only [missed]
      rw [Finset.filter_eq_self.mpr (fun _ _ a => by have := a.isLt; omega),
        Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    have hhit0 : ∀ ask leaf, hit ask leaf = 0 := fun ask leaf => by
      simp only [hit, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro _ _ ⟨a, _⟩; exact a.elim0
    rw [hmissed, Nat.sub_self, Nat.mul_zero]
    constructor
    · rintro ⟨ask, leaf, _, _, hH⟩
      rw [hhit0] at hH
      have : H = 0 := by omega
      simp [this]
    · intro hH
      have hH0 : H = 0 := by
        have hpos : 0 < 8 ^ res := Nat.pow_pos (by omega)
        nlinarith
      refine ⟨fun _ _ _ => false, fun _ a => a.elim0, ?_, ?_, by omega⟩
      · intro u path; exact ⟨∅, false, fun _ => rfl⟩
      · intro _ a; exact a.elim0
  have hL_pos : 0 < L := by omega
  by_cases hm0 : m = 0
  · subst hm0
    have hres0 : res = 0 := by simp [res]
    have hKpos : 0 < Kslots := Nat.mul_pos (Nat.two_pow_pos s) hL_pos
    have hmissed0 : missed = 0 := by
      simp only [missed, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w _ h
      obtain ⟨j, _⟩ := h ⟨0, hKpos⟩
      have := j.isLt
      omega
    rw [hres0, hmissed0, Nat.pow_zero, Nat.sub_zero, Nat.one_mul, Nat.mul_one]
    constructor
    · rintro ⟨ask, leaf, _, _, hH⟩
      exact le_trans hH (Finset.card_filter_le _ _)
    · intro hH
      refine ⟨fun _ _ _ => false, fun _ _ i => i.elim0, ?_, ?_, ?_⟩
      · intro u path; exact ⟨∅, false, fun _ => rfl⟩
      · intro _ _ i; exact i.elim0
      · have hfull : hit (fun _ _ _ => false) (fun _ _ i => i.elim0) = fiber.card := by
          simp only [hit]
          rw [Finset.filter_true_of_mem (fun _ _ => ⟨⟨0, hL_pos⟩, fun i => i.elim0⟩)]
        rw [hfull]; exact hH
  have hm_pos : 0 < m := by omega
  have hk12 : 12 ≤ k := by
    have hcard := Fintype.card_le_of_injective
      (fun z : Fin m × Fin 12 => (⟨(starts z.1 + z.2.val) % k, Nat.mod_lt _ hk_pos⟩ : Fin k))
      (fun a b h => hinj (congrArg Fin.val h))
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    nlinarith
  have hk2 : 2 ≤ k := by omega
  have hstate_eq : ∀ r key, state row.val r key = stateAt k row constant r key := fun r key => rfl
  have hwin_ex : ∀ i : Fin m, ∃ F : Sym → Bool, xorAll F = true ∧
      ∀ sample ∈ fiber, out sample i = F (triple sample i) := by
    intro i
    obtain ⟨F, hFx, hFout⟩ := window_out_eq_winFn hk2 constant row ref (starts i) (hgood i)
    refine ⟨F, hFx, fun sample hsf => ?_⟩
    apply hFout sample
    intro j
    obtain ⟨z, hzpin, hzval⟩ := hpin9 i j
    have hmem := (Finset.mem_filter.mp hsf).2 z hzpin
    have hzmod : z.val % k = z.val := Nat.mod_eq_of_lt z.isLt
    simpa [bit, hstate_eq, hzval, hzmod] using hmem
  let Fwin : Fin m → Sym → Bool := fun i => Classical.choose (hwin_ex i)
  have hFwin_xor : ∀ i : Fin m, xorAll (Fwin i) = true :=
    fun i => (Classical.choose_spec (hwin_ex i)).1
  have hFwin_out : ∀ i : Fin m, ∀ sample ∈ fiber, out sample i = Fwin i (triple sample i) :=
    fun i => (Classical.choose_spec (hwin_ex i)).2
  let predIdx : Fin k ≃ Fin k :=
    { toFun := fun b => ⟨(b.val + k - 1) % k, Nat.mod_lt _ hk_pos⟩
      invFun := fun b => ⟨(b.val + 1) % k, Nat.mod_lt _ hk_pos⟩
      left_inv := fun b => Fin.ext (by
        dsimp only
        have h1 : ((b.val + k - 1) % k + 1) % k = (b.val + k - 1 + 1) % k := by
          rw [Nat.mod_add_mod]
        rw [h1, show b.val + k - 1 + 1 = b.val + k by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt b.isLt])
      right_inv := fun b => Fin.ext (by
        dsimp only
        have h1 : ((b.val + 1) % k + k - 1) % k = (b.val + 1 - 1) % k := by
          simpa [Nat.mod_eq_of_lt (by omega : 1 < k)] using mod_sub_eq hk_pos (by omega : 1 ≤ b.val + 1)
        rw [h1, Nat.add_sub_cancel, Nat.mod_eq_of_lt b.isLt]) }
  let posOf : Fin m → Fin 3 → Fin k := fun i v => ⟨(starts i + 9 + v.val) % k, Nat.mod_lt _ hk_pos⟩
  have hposOf_inj : Function.Injective (fun iv : Fin m × Fin 3 => posOf iv.1 iv.2) := by
    rintro ⟨i1, v1⟩ ⟨i2, v2⟩ h
    have hval : (starts i1 + (9 + v1.val)) % k = (starts i2 + (9 + v2.val)) % k := by
      simpa [posOf, Nat.add_assoc] using congrArg Fin.val h
    have hinj' := @hinj (i1, ⟨9 + v1.val, by omega⟩) (i2, ⟨9 + v2.val, by omega⟩) hval
    have hi : i1 = i2 := congrArg Prod.fst hinj'
    have hv : v1 = v2 := Fin.ext (by have := congrArg (fun z => z.2.val) hinj'; dsimp at this; omega)
    exact Prod.ext hi hv
  let varOf : Fin m → Fin 3 → Fin k := fun i v => predIdx (posOf i v)
  have hvarOf_inj : Function.Injective (fun iv : Fin m × Fin 3 => varOf iv.1 iv.2) :=
    predIdx.injective.comp hposOf_inj
  let pinVar : Finset (Fin k) := pin.image predIdx
  have hvarOf_not_pin : ∀ i v, varOf i v ∉ pinVar := by
    intro i v hm
    obtain ⟨z, hzpin, hzeq⟩ := Finset.mem_image.mp hm
    have hpos_eq : z = posOf i v := predIdx.injective hzeq
    exact hpin3 i v z hzpin (congrArg Fin.val hpos_eq)
  have hbit0_eq : ∀ (q : K) (b : Fin k),
      bit row.val 0 q.val b.val = xor (bitOf q (predIdx b)) (row.val.testBit b.val) := by
    intro q b
    have hmod : b.val % k = b.val := Nat.mod_eq_of_lt b.isLt
    simp only [bit, state, List.range_zero, List.foldl_nil, hmod, Nat.testBit_xor]
    have hrot : (rot0 1 q.val).testBit b.val = q.val.testBit (predIdx b).val := by
      have := testBit_rot (s := 1) q.isLt b.isLt
      simpa [rot0, rot, predIdx, Nat.mod_eq_of_lt (by omega : 1 < k)] using this
    rw [hrot]
  have hfiber_iff : ∀ q : K, q ∈ fiber ↔ ∀ b ∈ pinVar, finPowEquiv k q b = finPowEquiv k ref b := by
    intro q
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and, pinVar, Finset.mem_image]
    constructor
    · intro h b ⟨z, hzpin, hzeq⟩
      subst hzeq
      have hz := h z hzpin
      rw [hbit0_eq q z, hbit0_eq ref z] at hz
      have hbo : bitOf q (predIdx z) = bitOf ref (predIdx z) := by
        generalize bitOf q (predIdx z) = a1 at hz ⊢
        generalize bitOf ref (predIdx z) = a2 at hz ⊢
        generalize row.val.testBit z.val = a3 at hz
        cases a1 <;> cases a2 <;> cases a3 <;> simp_all
      simp [finPowEquiv, bitOf, hbo]
    · intro h z hzpin
      rw [hbit0_eq q z, hbit0_eq ref z]
      have hfz := h (predIdx z) ⟨z, hzpin, rfl⟩
      have hbo : bitOf q (predIdx z) = bitOf ref (predIdx z) :=
        bool_toZ2_inj _ _ hfz
      rw [hbo]
  have htriple_eq : ∀ (q : K) (i : Fin m) (v : Fin 3),
      triple q i v = xor (bitOf q (varOf i v)) (row.val.testBit (posOf i v).val) := by
    intro q i v
    have h1 := hbit0_eq q (posOf i v)
    simpa [triple, bit, posOf, varOf, Nat.mod_eq_of_lt (posOf i v).isLt] using h1
  let winVar : Finset (Fin k) := (Finset.univ : Finset (Fin m × Fin 3)).image (fun iv => varOf iv.1 iv.2)
  let extVar : Finset (Fin k) := (Finset.univ \ pinVar) \ winVar
  have hdisj_pw : Disjoint pinVar winVar := by
    rw [Finset.disjoint_left]
    intro b hbp hbw
    obtain ⟨⟨i, v⟩, _, rfl⟩ := Finset.mem_image.mp hbw
    exact hvarOf_not_pin i v hbp
  let decodeSym : (Fin m → Fin 3 → Z2) → (Fin m → Sym) :=
    fun w i v => xor (decide (w i v = 1)) (row.val.testBit (posOf i v).val)
  let encodeSym : (Fin m → Sym) → (Fin m → Fin 3 → Z2) :=
    fun s i v => if xor (s i v) (row.val.testBit (posOf i v).val) then 1 else 0
  have hdec_enc : ∀ s, decodeSym (encodeSym s) = s := by
    intro s; funext i v
    have hdec : ∀ (b r : Bool), xor (decide ((if xor b r then (1 : Z2) else 0) = 1)) r = b := by decide
    exact hdec (s i v) (row.val.testBit (posOf i v).val)
  have henc_dec : ∀ w, encodeSym (decodeSym w) = w := by
    intro w; funext i v
    have henc : ∀ (a : Z2) (r : Bool), (if xor (xor (decide (a = 1)) r) r then (1 : Z2) else 0) = a := by decide
    exact henc (w i v) (row.val.testBit (posOf i v).val)
  let packVec : (extVar → Z2) → (Fin m → Fin 3 → Z2) → (Fin k → Z2) := fun ext w b =>
    if hb : b ∈ pinVar then finPowEquiv k ref b
    else if hw : b ∈ winVar then
      let iv := Classical.choose (Finset.mem_image.mp hw)
      w iv.1 iv.2
    else ext ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hb⟩, hw⟩⟩
  have hpack_pin : ∀ ext w b, b ∈ pinVar → packVec ext w b = finPowEquiv k ref b := by
    intro ext w b hb; simp [packVec, hb]
  have hpack_win : ∀ ext w i v, packVec ext w (varOf i v) = w i v := by
    intro ext w i v
    have hnotp : varOf i v ∉ pinVar := hvarOf_not_pin i v
    have hmemw : varOf i v ∈ winVar := Finset.mem_image.mpr ⟨(i, v), Finset.mem_univ _, rfl⟩
    simp only [packVec, hnotp, ↓reduceDIte, hmemw]
    have hspec := (Classical.choose_spec (Finset.mem_image.mp hmemw)).2
    have heq : Classical.choose (Finset.mem_image.mp hmemw) = (i, v) := hvarOf_inj hspec
    rw [heq]
  have hpack_ext : ∀ ext w (b : extVar), packVec ext w b.1 = ext b := by
    intro ext w b
    have hnotw : b.1 ∉ winVar := (Finset.mem_sdiff.mp b.2).2
    have hnotp : b.1 ∉ pinVar := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp b.2).1).2
    simp [packVec, hnotp, hnotw]
  let fiberEquiv : fiber ≃ ((extVar → Z2) × (Fin m → Fin 3 → Z2)) :=
    { toFun := fun q =>
        (fun b => finPowEquiv k q.1 b.1, fun i v => finPowEquiv k q.1 (varOf i v))
      invFun := fun p =>
        ⟨(finPowEquiv k).symm (packVec p.1 p.2), (hfiber_iff _).mpr fun b hb => by
          rw [(finPowEquiv k).apply_symm_apply, hpack_pin _ _ b hb]⟩
      left_inv := fun q => by
        apply Subtype.ext
        apply (finPowEquiv k).injective
        rw [(finPowEquiv k).apply_symm_apply]
        funext b
        by_cases hbp : b ∈ pinVar
        · rw [hpack_pin _ _ b hbp, (hfiber_iff q.1).mp q.2 b hbp]
        · by_cases hbw : b ∈ winVar
          · obtain ⟨⟨i, v⟩, _, rfl⟩ := Finset.mem_image.mp hbw
            rw [hpack_win]
          · have hbext : b ∈ extVar :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbp⟩, hbw⟩
            exact hpack_ext _ _ ⟨b, hbext⟩
      right_inv := fun ⟨ext, w⟩ => by
        ext b
        · simp only [(finPowEquiv k).apply_symm_apply, hpack_ext]
        · simp only [(finPowEquiv k).apply_symm_apply, hpack_win] }
  have hfiber_card : fiber.card = Fintype.card (extVar → Z2) * 8 ^ m := by
    rw [← Fintype.card_coe fiber, Fintype.card_congr fiberEquiv, Fintype.card_prod]
    congr 1
    simp [Fintype.card_fun, Fintype.card_fin]
  have htriple_pack : ∀ ext w i,
      triple ((finPowEquiv k).symm (packVec ext w)) i = decodeSym w i := by
    intro ext w i
    funext v
    rw [htriple_eq]
    have hbv : finPowEquiv k ((finPowEquiv k).symm (packVec ext w)) (varOf i v) = w i v := by
      rw [(finPowEquiv k).apply_symm_apply, hpack_win]
    change (if ((finPowEquiv k).symm (packVec ext w)).val.testBit (varOf i v).val = true then (1 : Z2) else 0) = w i v at hbv
    have hbool : (((finPowEquiv k).symm (packVec ext w)).val.testBit (varOf i v).val) =
        decide (w i v = 1) := by
      cases htb : ((finPowEquiv k).symm (packVec ext w)).val.testBit (varOf i v).val
      · rw [htb] at hbv; simp at hbv; simp [← hbv]
      · rw [htb] at hbv; simp at hbv; simp [← hbv]
    change xor (((finPowEquiv k).symm (packVec ext w)).val.testBit (varOf i v).val) (row.val.testBit (posOf i v).val) =
      xor (decide (w i v = 1)) (row.val.testBit (posOf i v).val)
    rw [hbool]
  constructor
  · rintro ⟨ask, leaf, haff, hlist, hH⟩
    refine le_trans (Nat.mul_le_mul_left (8 ^ res) hH) ?_
    have hpart_ext :
        hit ask leaf =
          ∑ ext : extVar → Z2,
            ((Finset.univ : Finset (Fin m → Fin 3 → Z2)).filter (fun w =>
              let q := (finPowEquiv k).symm (packVec ext w)
              ∃ a : Fin L, ∀ i : Fin m,
                leaf (run (d + s) ask q) a i (triple q i) = out q i)).card := by
      have h1 : hit ask leaf =
          ((Finset.univ : Finset ((extVar → Z2) × (Fin m → Fin 3 → Z2))).filter (fun p =>
            let q := (finPowEquiv k).symm (packVec p.1 p.2)
            ∃ a : Fin L, ∀ i : Fin m,
              leaf (run (d + s) ask q) a i (triple q i) = out q i)).card := by
        refine Finset.card_bij (fun q hq => fiberEquiv ⟨q, (Finset.mem_filter.mp hq).1⟩) ?_ ?_ ?_
        · intro q hq
          have hqf : q ∈ fiber := (Finset.mem_filter.mp hq).1
          have hqcond := (Finset.mem_filter.mp hq).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hback : (finPowEquiv k).symm (packVec (fiberEquiv ⟨q, hqf⟩).1 (fiberEquiv ⟨q, hqf⟩).2) = q :=
            congrArg Subtype.val (fiberEquiv.left_inv ⟨q, hqf⟩)
          simpa [hback] using hqcond
        · intro q1 hq1 q2 hq2 h
          exact congrArg Subtype.val (fiberEquiv.injective h)
        · rintro ⟨ext, w⟩ hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
          let q : fiber := fiberEquiv.symm (ext, w)
          refine ⟨q.1, Finset.mem_filter.mpr ⟨q.2, hp⟩, by simpa [q] using fiberEquiv.apply_symm_apply (ext, w)⟩
      rw [h1, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun ext _ => ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [hpart_ext, hfiber_card, Finset.mul_sum,
      show Fintype.card (extVar → Z2) * 8 ^ m * (8 ^ res - missed) =
        ∑ _ext : extVar → Z2, 8 ^ m * (8 ^ res - missed) by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_assoc]]
    refine Finset.sum_le_sum fun ext _ => ?_
    let evalQ : (Fin m → Fin 3 → Z2) → K := fun w => (finPowEquiv k).symm (packVec ext w)
    have hevalQ_mem : ∀ w, evalQ w ∈ fiber := fun w =>
      (hfiber_iff _).mpr fun b hb => by rw [(finPowEquiv k).apply_symm_apply, hpack_pin _ _ b hb]
    let pref : (Fin m → Fin 3 → Z2) → Fin (2 ^ d) := fun w =>
      ⟨runFold d ask (evalQ w), runFold_lt d ask (evalQ w)⟩
    have hsplit_pref :
        ((Finset.univ : Finset (Fin m → Fin 3 → Z2)).filter (fun w =>
          ∃ a : Fin L, ∀ i : Fin m,
            leaf (run (d + s) ask (evalQ w)) a i (triple (evalQ w) i) = out (evalQ w) i)).card =
        ∑ p : Fin (2 ^ d),
          (((Finset.univ : Finset (Fin m → Fin 3 → Z2)).filter (fun w => pref w = p)).filter (fun w =>
            ∃ a : Fin L, ∀ i : Fin m,
              leaf (run (d + s) ask (evalQ w)) a i (triple (evalQ w) i) = out (evalQ w) i)).card := by
      have := Finset.card_eq_sum_card_fiberwise (f := pref)
        (s := (Finset.univ : Finset (Fin m → Fin 3 → Z2)).filter (fun w =>
          ∃ a : Fin L, ∀ i : Fin m,
            leaf (run (d + s) ask (evalQ w)) a i (triple (evalQ w) i) = out (evalQ w) i))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [this]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1; ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩
    have htot_pref :
        ∑ p : Fin (2 ^ d),
          ((Finset.univ : Finset (Fin m → Fin 3 → Z2)).filter (fun w => pref w = p)).card = 8 ^ m := by
      have := Finset.card_eq_sum_card_fiberwise (f := pref)
        (s := (Finset.univ : Finset (Fin m → Fin 3 → Z2)))
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      rw [← this, Finset.card_univ]
      simp [Fintype.card_fun, Fintype.card_fin]
    rw [hsplit_pref, ← htot_pref, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    set Cp := (Finset.univ : Finset (Fin m → Fin 3 → Z2)).filter (fun w => pref w = p)
    by_cases hCp_empty : Cp.Nonempty
    · obtain ⟨w0, hw0_mem⟩ := hCp_empty
      have hw0_pref : pref w0 = p := (Finset.mem_filter.mp hw0_mem).2
      have haff_form : ∀ u : Fin d, ∃ (ℓ : (Fin m → Fin 3 → Z2) →ₗ[Z2] Z2) (c0 : Z2),
          ∀ w, (if ask u.val (runFold u.val ask (evalQ w0)) (evalQ w) then (1 : Z2) else 0) = ℓ w + c0 := by
        intro u
        obtain ⟨mask, c, hmask⟩ := haff u (runFold u.val ask (evalQ w0))
        let ℓ : (Fin m → Fin 3 → Z2) →ₗ[Z2] Z2 :=
          { toFun := fun w =>
              ∑ i : Fin m, ∑ v : Fin 3, if varOf i v ∈ mask then w i v else 0
            map_add' := fun x y => by
              simp only [Pi.add_apply]
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun v _ => by split_ifs <;> simp
            map_smul' := fun a x => by
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun v _ => by split_ifs <;> simp }
        let c0 : Z2 := (if c then 1 else 0) +
          ∑ b ∈ mask \ winVar, packVec ext 0 b
        refine ⟨ℓ, c0, fun w => ?_⟩
        rw [hmask (evalQ w), bool_toZ2_xor]
        have hpar_eq : par = parBool := rfl
        rw [hpar_eq, toZ2_parBool]
        have hfilt_eq : (mask.filter (fun b => bitOf (evalQ w) b = true)).card =
            (mask.filter (fun b => packVec ext w b = 1)).card := by
          congr 1; ext b
          simp only [Finset.mem_filter]
          refine and_congr_right fun _ => ?_
          have hfv : finPowEquiv k (evalQ w) b = packVec ext w b := by
            simp [evalQ]
          simp only [finPowEquiv, Equiv.coe_fn_mk] at hfv
          simp only [bitOf]
          cases htb : (evalQ w).val.testBit b.val <;> simp [htb] at hfv <;> simp [← hfv]
        rw [hfilt_eq, card_filter_eq_sum_z2]
        have hsplit_mask : ∑ b ∈ mask, packVec ext w b =
            (∑ b ∈ mask ∩ winVar, packVec ext w b) + (∑ b ∈ mask \ winVar, packVec ext w b) := by
          have hunion : (mask ∩ winVar) ∪ (mask \ winVar) = mask := by
            ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
            by_cases hxw : x ∈ winVar <;> simp [hxw]
          rw [← Finset.sum_union (Finset.disjoint_left.mpr fun x hx1 hx2 =>
            (Finset.mem_sdiff.mp hx2).2 (Finset.mem_inter.mp hx1).2), hunion]
        rw [hsplit_mask]
        have hmw : ∑ b ∈ mask ∩ winVar, packVec ext w b = ℓ w := by
          have hbij_w : ∑ b ∈ mask ∩ winVar, packVec ext w b =
              ∑ iv ∈ (Finset.univ : Finset (Fin m × Fin 3)).filter (fun iv => varOf iv.1 iv.2 ∈ mask),
                w iv.1 iv.2 := by
            refine (Finset.sum_bij (fun iv _ => varOf iv.1 iv.2) ?_ ?_ ?_ ?_).symm
            · intro iv hiv
              exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hiv).2,
                Finset.mem_image.mpr ⟨iv, Finset.mem_univ _, rfl⟩⟩
            · intro a _ b _ h; exact hvarOf_inj h
            · intro b hb
              obtain ⟨hbm, hbw⟩ := Finset.mem_inter.mp hb
              obtain ⟨iv, _, rfl⟩ := Finset.mem_image.mp hbw
              exact ⟨iv, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbm⟩, rfl⟩
            · intro iv _; exact (hpack_win ext w iv.1 iv.2).symm
          rw [hbij_w, Finset.sum_filter, Fintype.sum_prod_type]
          rfl
        have hms : ∑ b ∈ mask \ winVar, packVec ext w b = ∑ b ∈ mask \ winVar, packVec ext 0 b := by
          refine Finset.sum_congr rfl fun b hb => ?_
          have hnotw : b ∉ winVar := (Finset.mem_sdiff.mp hb).2
          by_cases hbp : b ∈ pinVar
          · rw [hpack_pin _ _ b hbp, hpack_pin _ _ b hbp]
          · have hbext : b ∈ extVar :=
              Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbp⟩, hnotw⟩
            rw [hpack_ext ext w ⟨b, hbext⟩, hpack_ext ext 0 ⟨b, hbext⟩]
        rw [hmw, hms]
        simp only [c0]
        ring
      let Φ : (Fin m → Fin 3 → Z2) →ₗ[Z2] (Fin d → Z2) :=
        { toFun := fun w u => (Classical.choose (haff_form u)) w
          map_add' := fun x y => by funext u; simp
          map_smul' := fun c x => by funext u; simp }
      have hCp_coset : ∀ w, w ∈ Cp ↔ w - w0 ∈ LinearMap.ker Φ := by
        intro w
        simp only [Cp, Finset.mem_filter, Finset.mem_univ, true_and, LinearMap.mem_ker]
        have hpref_iff : pref w = p ↔ ∀ u : Fin d,
            ask u.val (runFold u.val ask (evalQ w0)) (evalQ w) =
              ask u.val (runFold u.val ask (evalQ w0)) (evalQ w0) := by
          constructor
          · intro hp u
            have hrun_eq : runFold d ask (evalQ w) = runFold d ask (evalQ w0) := by
              have h1 : (pref w).val = p.val := congrArg Fin.val hp
              have h2 : (pref w0).val = p.val := congrArg Fin.val hw0_pref
              exact h1.trans h2.symm
            have hprefix_eq : ∀ n ≤ d, runFold n ask (evalQ w) = runFold n ask (evalQ w0) := by
              intro n hn
              apply Nat.eq_of_testBit_eq
              intro j
              by_cases hjn : j < n
              · have h1 := runFold_testBit d ask (evalQ w) j (by omega)
                have h2 := runFold_testBit d ask (evalQ w0) j (by omega)
                have h3 := runFold_testBit n ask (evalQ w) j hjn
                have h4 := runFold_testBit n ask (evalQ w0) j hjn
                rw [h3, h4, ← h1, ← h2, hrun_eq]
              · have h1 := Nat.testBit_lt_two_pow (i := j) ((runFold_lt n ask (evalQ w)).trans_le
                  (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
                have h2 := Nat.testBit_lt_two_pow (i := j) ((runFold_lt n ask (evalQ w0)).trans_le
                  (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
                rw [h1, h2]
            have h1 := runFold_testBit d ask (evalQ w) u.val u.isLt
            have h2 := runFold_testBit d ask (evalQ w0) u.val u.isLt
            rw [hprefix_eq u.val (le_of_lt u.isLt)] at h1
            rw [← h1, ← h2, hrun_eq]
          · intro hall
            have hprefix_eq : ∀ n ≤ d, runFold n ask (evalQ w) = runFold n ask (evalQ w0) := by
              intro n
              induction n with
              | zero => intro _; rfl
              | succ n ih =>
                intro hn
                have hprev := ih (by omega)
                simp only [runFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
                change runFold n ask (evalQ w) + ((ask n (runFold n ask (evalQ w)) (evalQ w)).toNat <<< n) =
                  runFold n ask (evalQ w0) + ((ask n (runFold n ask (evalQ w0)) (evalQ w0)).toNat <<< n)
                rw [hprev, hall ⟨n, by omega⟩]
            apply Fin.ext
            have h0 : (pref w0).val = p.val := congrArg Fin.val hw0_pref
            exact (hprefix_eq d le_rfl).trans h0
        rw [hpref_iff]
        constructor
        · intro hall
          funext u
          obtain ⟨c0, hc0⟩ := Classical.choose_spec (haff_form u)
          have h1 := hc0 w
          have h2 := hc0 w0
          rw [hall u] at h1
          have h3 : (Classical.choose (haff_form u)) w + c0 =
              (Classical.choose (haff_form u)) w0 + c0 := h1.symm.trans h2
          have h4 := add_right_cancel h3
          simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, map_sub, Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
          exact h4
        · intro hker u
          obtain ⟨c0, hc0⟩ := Classical.choose_spec (haff_form u)
          have h0 : (Classical.choose (haff_form u)) (w - w0) = 0 := congrFun hker u
          rw [map_sub, sub_eq_zero] at h0
          apply bool_toZ2_inj
          rw [hc0 w, hc0 w0, h0]
      obtain ⟨J, hJ_card, hJ_surj⟩ := exists_surjective_block_proj m d Φ
      let eJ : Fin res ≃ J := Fintype.equivOfCardEq (by simp [hJ_card, res])
      let πJ : LinearMap.ker Φ →ₗ[Z2] (J → Fin 3 → Z2) :=
        { toFun := fun x i => x.1 i.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hπJ_surj : Function.Surjective πJ := hJ_surj
      have hfib_card : ∀ y : J → Fin 3 → Z2,
          ((Finset.univ : Finset (LinearMap.ker Φ)).filter (fun x => πJ x = y)).card =
            Fintype.card (LinearMap.ker πJ) := by
        intro y
        obtain ⟨x0, hx0⟩ := hπJ_surj y
        rw [← Finset.card_univ]
        refine Finset.card_bij (fun x hx => (⟨x - x0, by
          simp only [LinearMap.mem_ker, map_sub, (Finset.mem_filter.mp hx).2, hx0, sub_self]⟩ : LinearMap.ker πJ)) ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro a _ b _ h
          have : a - x0 = b - x0 := congrArg Subtype.val h
          exact sub_left_inj.mp this
        · intro z _
          refine ⟨z.1 + x0, ?_, Subtype.ext (by simp)⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_add,
            LinearMap.mem_ker.mp z.2, hx0, zero_add]
      have hCp_card_eq : Cp.card = Fintype.card (LinearMap.ker πJ) * 8 ^ res := by
        have h1 : Cp.card = Fintype.card (LinearMap.ker Φ) := by
          rw [← Finset.card_univ]
          refine Finset.card_bij (fun w hw => (⟨w - w0, (hCp_coset w).mp hw⟩ : LinearMap.ker Φ)) ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ h
            exact sub_left_inj.mp (congrArg Subtype.val h)
          · intro x _
            refine ⟨x.1 + w0, (hCp_coset _).mpr (by simpa using x.2), Subtype.ext (by simp)⟩
        rw [h1]
        have h2 := Finset.card_eq_sum_card_fiberwise (f := πJ)
          (s := (Finset.univ : Finset (LinearMap.ker Φ)))
          (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
        rw [Finset.card_univ] at h2
        rw [h2]
        simp_rw [hfib_card]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
          Fintype.card_coe, hJ_card, Fintype.card_fin, smul_eq_mul, mul_comm]
        rfl
      let eSlots : Fin Kslots ≃ (Fin (2 ^ s) × Fin L) := finProdFinEquiv.symm
      let bad : Fin Kslots → Fin res → Fin 8 := fun slot j =>
        let ta := eSlots slot
        let hist := p.val + (ta.1.val <<< d)
        let i := (eJ j).1
        symEquiv.symm (Classical.choose (low_misses_symbol (hFwin_xor i) (hlist hist ta.2 i)))
      have hbad_ne : ∀ (slot : Fin Kslots) (j : Fin res),
          let ta := eSlots slot
          let hist := p.val + (ta.1.val <<< d)
          let i := (eJ j).1
          leaf hist ta.2 i (symEquiv (bad slot j)) ≠ Fwin i (symEquiv (bad slot j)) := by
        intro slot j
        simp only [bad, Equiv.apply_symm_apply]
        exact Classical.choose_spec (low_misses_symbol (hFwin_xor (eJ j).1) (hlist _ _ _))
      let resWordOf : (Fin m → Fin 3 → Z2) → (Fin res → Fin 8) :=
        fun w j => symEquiv.symm (decodeSym w (eJ j).1)
      have hCp_hit_sub :
          (Cp.filter (fun w =>
            ∃ a : Fin L, ∀ i : Fin m,
              leaf (run (d + s) ask (evalQ w)) a i (triple (evalQ w) i) = out (evalQ w) i)).card ≤
          (Cp.filter (fun w =>
            ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, resWordOf w j = bad slot j)).card := by
        refine Finset.card_le_card fun w hw => ?_
        obtain ⟨hwCp, a, ha⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_filter.mpr ⟨hwCp, fun hall => ?_⟩
        obtain ⟨t, ht⟩ := runFold_add d s ask (evalQ w)
        have hrun_eq : run (d + s) ask (evalQ w) = p.val + (t.val <<< d) := by
          have hp0 : runFold d ask (evalQ w) = p.val := congrArg Fin.val (Finset.mem_filter.mp hwCp).2
          rw [hp0] at ht
          exact ht
        let slot : Fin Kslots := eSlots.symm (t, a)
        obtain ⟨j, hj⟩ := hall slot
        have hne := hbad_ne slot j
        simp only [slot, Equiv.apply_symm_apply] at hne
        have hgood_j := ha (eJ j).1
        rw [hrun_eq, hFwin_out (eJ j).1 (evalQ w) (hevalQ_mem w), htriple_pack] at hgood_j
        have hsym_eq : decodeSym w (eJ j).1 = symEquiv (bad slot j) := by
          rw [← hj]; exact (symEquiv.apply_symm_apply _).symm
        rw [hsym_eq] at hgood_j
        exact hne hgood_j
      have hCp_notmiss :
          (Cp.filter (fun w =>
            ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, resWordOf w j = bad slot j)).card =
          Fintype.card (LinearMap.ker πJ) *
            ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
              ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)).card := by
        have h1 := Finset.card_eq_sum_card_fiberwise (f := resWordOf)
          (s := Cp.filter (fun w =>
            ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, resWordOf w j = bad slot j))
          (t := (Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
            ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j))
          (fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩)
        rw [h1]
        have hfib_rw : ∀ rw0 ∈ (Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
            ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j),
            ((Cp.filter (fun w =>
              ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, resWordOf w j = bad slot j)).filter
              (fun w => resWordOf w = rw0)).card = Fintype.card (LinearMap.ker πJ) := by
          intro rw0 hrw0
          have hrw0_cond := (Finset.mem_filter.mp hrw0).2
          let y : J → Fin 3 → Z2 := fun i v =>
            (if xor (symEquiv (rw0 (eJ.symm i)) v) (row.val.testBit (posOf i.1 v).val) then (1 : Z2) else 0) - w0 i.1 v
          rw [← hfib_card y]
          refine Finset.card_bij (fun w hw => (⟨w - w0, (hCp_coset w).mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1⟩ : LinearMap.ker Φ)) ?_ ?_ ?_
          · intro w hw
            have hreq : resWordOf w = rw0 := (Finset.mem_filter.mp hw).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, πJ, LinearMap.coe_mk, AddHom.coe_mk]
            funext i v
            simp only [Pi.sub_apply, y]
            congr 1
            have hi := congrFun hreq (eJ.symm i)
            simp only [resWordOf, Equiv.apply_symm_apply] at hi
            have hdec : decodeSym w i.1 = symEquiv (rw0 (eJ.symm i)) := by
              rw [← hi, symEquiv.apply_symm_apply]
            have hwi := congrFun (congrFun (henc_dec w) i.1) v
            simp only [encodeSym, hdec] at hwi
            exact hwi.symm
          · intro a _ b _ h
            exact sub_left_inj.mp (congrArg Subtype.val h)
          · intro x hx
            have hπx : πJ x = y := (Finset.mem_filter.mp hx).2
            have hrw_eq : resWordOf (x.1 + w0) = rw0 := by
              funext j
              apply symEquiv.injective
              simp only [resWordOf, Equiv.apply_symm_apply]
              funext v
              have hxv := congrFun (congrFun hπx (eJ j)) v
              simp only [πJ, LinearMap.coe_mk, AddHom.coe_mk, y, Equiv.symm_apply_apply] at hxv
              have hadd : (x.1 + w0) (eJ j).1 v =
                  if xor (symEquiv (rw0 j) v) (row.val.testBit (posOf (eJ j).1 v).val) then 1 else 0 := by
                simp only [Pi.add_apply, hxv, sub_add_cancel]
              simp only [decodeSym, hadd]
              cases symEquiv (rw0 j) v <;> cases row.val.testBit (posOf (eJ j).1 v).val <;> rfl
            refine ⟨x.1 + w0, ?_, Subtype.ext (by simp)⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨(hCp_coset _).mpr (by simpa using x.2),
              by rw [hrw_eq]; exact hrw0_cond⟩, hrw_eq⟩
        rw [Finset.sum_congr rfl hfib_rw, Finset.sum_const, smul_eq_mul, mul_comm]
      have hbad_bound := missed_le_card_bad res Kslots hKslots_le bad
      have hcompl :
          ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
            ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)).card +
          ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
            ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)).card = 8 ^ res := by
        have htot := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin res → Fin 8)))
          (p := fun rw0 => ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
        omega
      have hnm_le : ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
          ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)).card ≤ 8 ^ res - missed := by
        have hmiss_eq : missed = missCount res Kslots := rfl
        rw [hmiss_eq]
        omega
      calc 8 ^ res * (Cp.filter _).card
          ≤ 8 ^ res * (Fintype.card (LinearMap.ker πJ) *
              ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
                ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)).card) := by
            rw [← hCp_notmiss]
            exact Nat.mul_le_mul_left _ hCp_hit_sub
        _ = (Fintype.card (LinearMap.ker πJ) * 8 ^ res) *
              ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun rw0 =>
                ¬ ∀ slot : Fin Kslots, ∃ j : Fin res, rw0 j = bad slot j)).card := by ring
        _ ≤ Cp.card * (8 ^ res - missed) := by
            rw [← hCp_card_eq]
            exact Nat.mul_le_mul_left _ hnm_le
    · rw [Finset.not_nonempty_iff_eq_empty] at hCp_empty
      simp [hCp_empty]
  · intro hH
    let q := min d m
    have hq_add : q + res = m := by omega
    let resWord : K → (Fin res → Fin 8) := fun raw j =>
      symEquiv.symm (triple raw ⟨q + j.val, by omega⟩)
    let pickBucket : K → Fin (2 ^ s) := fun raw =>
      if h : ∃ a : Fin Kslots, ∀ j : Fin res, (resWord raw j).val ≠ a.val then
        let a := Classical.choose h
        ⟨a.val / L, by
          have ha : a.val < 2 ^ s * L := a.isLt
          exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ha)⟩
      else ⟨0, Nat.two_pow_pos s⟩
    let ask : Nat → Nat → K → Bool := fun levelId _ raw =>
      if h1 : levelId < q then
        triple raw ⟨levelId, by omega⟩ 0
      else if levelId < d then
        false
      else if levelId < d + s then
        (pickBucket raw).val.testBit (levelId - d)
      else false
    have haff : affine ask := by
      intro u path
      by_cases h1 : u.val < q
      · refine ⟨{varOf ⟨u.val, by omega⟩ 0}, row.val.testBit (posOf ⟨u.val, by omega⟩ 0).val, fun raw => ?_⟩
        simp only [ask, h1, ↓reduceDIte, htriple_eq]
        have hpar : par ((({varOf ⟨u.val, by omega⟩ 0} : Finset (Fin k)).filter (fun b => bitOf raw b = true)).card) =
            bitOf raw (varOf ⟨u.val, by omega⟩ 0) := by
          rw [Finset.filter_singleton]
          cases bitOf raw (varOf ⟨u.val, by omega⟩ 0) <;> rfl
        rw [hpar, Bool.xor_comm]
      · refine ⟨∅, false, fun raw => ?_⟩
        simp [ask, h1, u.isLt, par]
    let leaf : Nat → Fin L → Fin m → Symbol → Bool := fun history label i =>
      if i.val < q then
        let b := history.testBit i.val
        fun sym => if sym = (fun v => if v = 0 then !b else false) then !(Fwin i sym) else Fwin i sym
      else
        let bucket := (history >>> d) % 2 ^ s
        let slotVal := bucket * L + label.val
        let sym0 := symEquiv ⟨slotVal, by
          have hb : bucket < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
          have h1 : bucket * L + label.val < 2 ^ s * L := by
            have : (bucket + 1) * L ≤ 2 ^ s * L := Nat.mul_le_mul_right L hb
            nlinarith [label.isLt]
          omega⟩
        fun sym => if sym = sym0 then !(Fwin i sym) else Fwin i sym
    have hlist : listOK leaf := by
      intro history label i
      simp only [leaf]
      split_ifs
      · exact low_flipAt (hFwin_xor i) _
      · exact low_flipAt (hFwin_xor i) _
    have hrun_q : ∀ (raw : K) (u : Nat) (hu : u < q),
        (run (d + s) ask raw).testBit u = triple raw ⟨u, lt_of_lt_of_le hu (Nat.min_le_right d m)⟩ 0 := by
      intro raw u hu
      have hud : u < d := lt_of_lt_of_le hu (Nat.min_le_left d m)
      have h1 := runFold_testBit (d + s) ask raw u (by omega)
      simpa [run, runFold, ask, hu] using h1
    have hrun_bucket : ∀ raw : K,
        ((run (d + s) ask raw) >>> d) % 2 ^ s = (pickBucket raw).val := by
      intro raw
      apply Nat.eq_of_testBit_eq
      intro t
      rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
      by_cases hts : t < s
      · simp only [hts, decide_true, Bool.true_and]
        have h1 := runFold_testBit (d + s) ask raw (d + t) (by omega)
        have hnot1 : ¬ (d + t < q) := by omega
        have hnot2 : ¬ (d + t < d) := by omega
        have hlt3 : d + t < d + s := by omega
        simpa [run, runFold, ask, hnot1, hnot2, hlt3, Nat.add_sub_cancel_left] using h1
      · simp only [hts, decide_false, Bool.false_and]
        exact (Nat.testBit_lt_two_pow ((pickBucket raw).isLt.trans_le
          (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm
    have hhit_ge :
        (fiber.filter (fun raw =>
          ∃ a : Fin Kslots, ∀ j : Fin res, (resWord raw j).val ≠ a.val)).card ≤ hit ask leaf := by
      refine Finset.card_le_card fun raw hraw => ?_
      obtain ⟨hraw_f, hex_a⟩ := Finset.mem_filter.mp hraw
      refine Finset.mem_filter.mpr ⟨hraw_f, ?_⟩
      let a := Classical.choose hex_a
      have ha_spec : ∀ j : Fin res, (resWord raw j).val ≠ a.val := Classical.choose_spec hex_a
      refine ⟨⟨a.val % L, Nat.mod_lt _ hL_pos⟩, fun i => ?_⟩
      rw [hFwin_out i raw hraw_f]
      simp only [leaf]
      split_ifs with hiq
      · have hbit : (run (d + s) ask raw).testBit i.val = triple raw i 0 := hrun_q raw i.val hiq
        have hne : triple raw i ≠ (fun v => if v = 0 then !((run (d + s) ask raw).testBit i.val) else false) := by
          intro h
          have h0 := congrFun h 0
          simp only [↓reduceIte, hbit] at h0
          cases hb : triple raw i 0 <;> rw [hb] at h0 <;> exact Bool.noConfusion h0
        simp only [hne, ↓reduceIte]
      · have hbuck : ((run (d + s) ask raw) >>> d) % 2 ^ s = a.val / L := by
          rw [hrun_bucket raw]
          simp [pickBucket, hex_a, a]
        have hslot : ((run (d + s) ask raw) >>> d) % 2 ^ s * L + a.val % L = a.val := by
          rw [hbuck, Nat.mul_comm, Nat.div_add_mod]
        have hne : triple raw i ≠ symEquiv ⟨((run (d + s) ask raw) >>> d) % 2 ^ s * L + a.val % L, by
            have hb : ((run (d + s) ask raw) >>> d) % 2 ^ s < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
            have h1 : ((run (d + s) ask raw) >>> d) % 2 ^ s * L + a.val % L < 2 ^ s * L := by
              have : (((run (d + s) ask raw) >>> d) % 2 ^ s + 1) * L ≤ 2 ^ s * L :=
                Nat.mul_le_mul_right L hb
              nlinarith [Nat.mod_lt a.val hL_pos]
            omega⟩ := by
          intro h
          have hq_le : q ≤ i.val := Nat.le_of_not_lt hiq
          have hj_lt : i.val - q < res := by omega
          have hja := ha_spec ⟨i.val - q, hj_lt⟩
          have hi_eq : (⟨q + (i.val - q), by have := i.isLt; omega⟩ : Fin m) = i :=
            Fin.ext (Nat.add_sub_of_le hq_le)
          have hres_eq : resWord raw ⟨i.val - q, hj_lt⟩ = symEquiv.symm (triple raw i) := by
            simp only [resWord, hi_eq]
          rw [hres_eq, h, symEquiv.symm_apply_apply] at hja
          exact hja hslot
        simp only [hne, ↓reduceIte]
    have hgood_card :
        8 ^ res * (fiber.filter (fun raw =>
          ∃ a : Fin Kslots, ∀ j : Fin res, (resWord raw j).val ≠ a.val)).card =
        fiber.card * (8 ^ res - missed) := by
      have hcard_eq :
          (fiber.filter (fun raw =>
            ∃ a : Fin Kslots, ∀ j : Fin res, (resWord raw j).val ≠ a.val)).card =
          Fintype.card (extVar → Z2) * 8 ^ q * (8 ^ res - missed) := by
        let eM : (Fin m → Fin 3 → Z2) ≃ ((Fin q → Fin 3 → Z2) × (Fin res → Fin 8)) :=
          { toFun := fun w =>
              (fun i => w ⟨i.val, by omega⟩, fun j => symEquiv.symm (decodeSym w ⟨q + j.val, by omega⟩))
            invFun := fun p i =>
              if hi : i.val < q then p.1 ⟨i.val, hi⟩
              else encodeSym (fun _ => symEquiv (p.2 ⟨i.val - q, by omega⟩)) i
            left_inv := fun w => by
              funext i v
              dsimp only
              split_ifs with hi
              · rfl
              · have heq : (⟨q + (i.val - q), by have := i.isLt; omega⟩ : Fin m) = i :=
                  Fin.ext (Nat.add_sub_of_le (Nat.le_of_not_lt hi))
                simp only [heq, Equiv.apply_symm_apply]
                exact congrFun (congrFun (henc_dec w) i) v
            right_inv := fun ⟨w1, w2⟩ => by
              refine Prod.ext (funext fun i => funext fun v => by simp [i.isLt]) (funext fun i => ?_)
              dsimp only
              apply symEquiv.injective
              simp only [Equiv.apply_symm_apply]
              funext v
              have hnot : ¬ (q + i.val < q) := by omega
              simp only [decodeSym, hnot, ↓reduceDIte, Nat.add_sub_cancel_left, encodeSym]
              have hdec : ∀ (b r : Bool), xor (decide ((if xor b r then (1 : Z2) else 0) = 1)) r = b := by decide
              exact hdec (symEquiv (w2 i) v) (row.val.testBit (posOf ⟨q + i.val, by omega⟩ v).val) }
        have hbij :
            (fiber.filter (fun raw =>
              ∃ a : Fin Kslots, ∀ j : Fin res, (resWord raw j).val ≠ a.val)).card =
            ((Finset.univ : Finset (((extVar → Z2) × (Fin q → Fin 3 → Z2)) × (Fin res → Fin 8))).filter
              (fun p => ∃ a : Fin Kslots, ∀ j : Fin res, (p.2 j).val ≠ a.val)).card := by
          refine Finset.card_bij (fun raw hraw =>
            let p := fiberEquiv ⟨raw, (Finset.mem_filter.mp hraw).1⟩
            let q2 := eM p.2
            ((p.1, q2.1), q2.2)) ?_ ?_ ?_
          · intro raw hraw
            have hrf := (Finset.mem_filter.mp hraw).1
            have hrc := (Finset.mem_filter.mp hraw).2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            have hback : (finPowEquiv k).symm (packVec (fiberEquiv ⟨raw, hrf⟩).1 (fiberEquiv ⟨raw, hrf⟩).2) = raw :=
              congrArg Subtype.val (fiberEquiv.left_inv ⟨raw, hrf⟩)
            have hrw : (eM (fiberEquiv ⟨raw, hrf⟩).2).2 = resWord raw := by
              funext j
              simp only [eM, Equiv.coe_fn_mk, resWord]
              rw [← htriple_pack (fiberEquiv ⟨raw, hrf⟩).1 (fiberEquiv ⟨raw, hrf⟩).2 ⟨q + j.val, by omega⟩, hback]
            rw [hrw]
            exact hrc
          · intro r1 hr1 r2 hr2 h
            have hp1 : (fiberEquiv ⟨r1, (Finset.mem_filter.mp hr1).1⟩).1 =
                (fiberEquiv ⟨r2, (Finset.mem_filter.mp hr2).1⟩).1 := congrArg (fun z => z.1.1) h
            have hp2 : eM (fiberEquiv ⟨r1, (Finset.mem_filter.mp hr1).1⟩).2 =
                eM (fiberEquiv ⟨r2, (Finset.mem_filter.mp hr2).1⟩).2 :=
              Prod.ext (congrArg (fun z => z.1.2) h) (congrArg (fun z => z.2) h)
            exact congrArg Subtype.val (fiberEquiv.injective (Prod.ext hp1 (eM.injective hp2)))
          · rintro ⟨⟨ext, w1⟩, w2⟩ hp
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
            let raw : fiber := fiberEquiv.symm (ext, eM.symm (w1, w2))
            have hrw : resWord raw.1 = w2 := by
              funext j
              simp only [resWord, raw, fiberEquiv, Equiv.coe_fn_symm_mk]
              have htp := htriple_pack ext (eM.symm (w1, w2)) ⟨q + j.val, by omega⟩
              rw [htp]
              have := congrFun (congrArg Prod.snd (eM.apply_symm_apply (w1, w2))) j
              simpa [eM] using this
            refine ⟨raw.1, Finset.mem_filter.mpr ⟨raw.2, by rw [hrw]; exact hp⟩, ?_⟩
            have hfe : fiberEquiv ⟨raw.1, raw.2⟩ = (ext, eM.symm (w1, w2)) :=
              fiberEquiv.apply_symm_apply _
            simp [hfe]
        rw [hbij]
        have hprod :
            ((Finset.univ : Finset (((extVar → Z2) × (Fin q → Fin 3 → Z2)) × (Fin res → Fin 8))).filter
              (fun p => ∃ a : Fin Kslots, ∀ j : Fin res, (p.2 j).val ≠ a.val)) =
            (Finset.univ : Finset ((extVar → Z2) × (Fin q → Fin 3 → Z2))) ×ˢ
              ((Finset.univ : Finset (Fin res → Fin 8)).filter
                (fun w2 => ∃ a : Fin Kslots, ∀ j : Fin res, (w2 j).val ≠ a.val)) := by
          ext ⟨p1, w2⟩
          simp
        rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_prod]
        have hcompl :
            ((Finset.univ : Finset (Fin res → Fin 8)).filter
              (fun w2 => ∃ a : Fin Kslots, ∀ j : Fin res, (w2 j).val ≠ a.val)).card = 8 ^ res - missed := by
          have htot := Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin res → Fin 8)))
            (p := fun w2 => ∀ a : Fin Kslots, ∃ j : Fin res, (w2 j).val = a.val)
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
          have hneg : ((Finset.univ : Finset (Fin res → Fin 8)).filter
              (fun w2 => ¬ ∀ a : Fin Kslots, ∃ j : Fin res, (w2 j).val = a.val)) =
              ((Finset.univ : Finset (Fin res → Fin 8)).filter
                (fun w2 => ∃ a : Fin Kslots, ∀ j : Fin res, (w2 j).val ≠ a.val)) := by
            ext w2
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            push Not
            rfl
          rw [hneg] at htot
          change missed + _ = 8 ^ res at htot
          omega
        rw [hcompl]
        congr 1
        congr 1
        simp [Fintype.card_fin]
      rw [hcard_eq, hfiber_card]
      calc 8 ^ res * (Fintype.card (extVar → Z2) * 8 ^ q * (8 ^ res - missed))
          = Fintype.card (extVar → Z2) * (8 ^ q * 8 ^ res) * (8 ^ res - missed) := by ring
        _ = Fintype.card (extVar → Z2) * 8 ^ m * (8 ^ res - missed) := by rw [← pow_add, hq_add]
    refine ⟨ask, leaf, haff, hlist, ?_⟩
    have h8pos : 0 < 8 ^ res := Nat.pow_pos (by omega)
    have hmul : 8 ^ res * H ≤ 8 ^ res * hit ask leaf := by
      calc 8 ^ res * H ≤ fiber.card * (8 ^ res - missed) := hH
        _ = 8 ^ res * (fiber.filter (fun raw =>
              ∃ a : Fin Kslots, ∀ j : Fin res, (resWord raw j).val ≠ a.val)).card := hgood_card.symm
        _ ≤ 8 ^ res * hit ask leaf := Nat.mul_le_mul_left _ hhit_ge
    exact Nat.le_of_mul_le_mul_left hmul h8pos

end PEqualNP.Outside.L_meta_25726_aux

theorem PEqualNP.Outside.L_meta_25726 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k) →
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
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val)%k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val)%k) →
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let fiber := (Finset.univ : Finset K).filter (fun keyWord =>
    ∀ z ∈ pin, bit row.val 0 keyWord.val z.val = bit row.val 0 ref.val z.val)
  let run := fun (steps : Nat) (ask : Nat → Nat → K → Bool) (x : K) =>
    (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
  let out := fun (input : K) (i : Fin m) => bit row.val 2 input.val (starts i+5)
  let Symbol := Fin 3 → Bool
  let triple := fun (raw : K) (idx : Fin m) (v : Fin 3) =>
    bit row.val 0 raw.val (starts idx+9+v.val)
  let low := fun (f : Symbol → Bool) => ∃ monomials : Finset (Finset (Fin 3)),
    (∀ mon ∈ monomials, mon.card ≤ 2) ∧ ∀ symbol,
      f symbol = par ((monomials.filter (fun mon => ∀ coord ∈ mon, symbol coord = true)).card)
  ∀ (d s L : Nat), 2^s*L ≤ 8 →
    let res := m-d
    let Kslots := 2^s*L
    let missed := ((Finset.univ : Finset (Fin res → Fin 8)).filter (fun residualWord =>
      ∀ a : Fin Kslots, ∃ j, (residualWord j).val = a.val)).card
    let affine := fun (ask : Nat → Nat → K → Bool) =>
      ∀ u : Fin d, ∀ path, ∃ (mask : Finset (Fin k)) (c : Bool), ∀ raw,
        ask u.val path raw = xor c (par ((mask.filter (fun b => bitOf raw b = true)).card))
    let listOK := fun (leaf : Nat → Fin L → Fin m → Symbol → Bool) =>
      ∀ history label i, low (leaf history label i)
    let hit := fun (ask : Nat → Nat → K → Bool)
        (leaf : Nat → Fin L → Fin m → Symbol → Bool) =>
      (fiber.filter (fun sample => ∃ a, ∀ i,
        leaf (run (d+s) ask sample) a i (triple sample i) = out sample i)).card
    ∀ H : Nat,
      (∃ ask leaf, affine ask ∧ listOK leaf ∧ H ≤ hit ask leaf) ↔
        8^res * H ≤ fiber.card * (8^res - missed)) :=
  PEqualNP.Outside.L_meta_25726_aux.main_aux
