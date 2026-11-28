import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic

namespace PEqualNP.Outside.L_meta_32044

private def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word j : Nat) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

private def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

private def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

private def stateAt (k : Nat) (constant : Nat → Fin (2 ^ k)) (row rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ row)

private lemma stateAt_zero (k : Nat) (constant : Nat → Fin (2 ^ k)) (row key : Nat) :
    stateAt k constant row 0 key = rot k 1 key ^^^ row := rfl

private lemma stateAt_succ (k : Nat) (constant : Nat → Fin (2 ^ k)) (row s key : Nat) :
    stateAt k constant row (s + 1) key =
      step k (mix k (stateAt k constant row s key)) ^^^ rot k (2 * s) key ^^^
        (constant (s + 1)).val := by
  simp [stateAt, List.range_succ]

private lemma rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma lt_two_pow_of_testBit {k x : Nat} (h : ∀ j, k ≤ j → x.testBit j = false) :
    x < 2 ^ k := by
  have hmod : x % 2 ^ k = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < k
    · simp [hj]
    · simp [hj, h j (by omega)]
  rw [← hmod]
  exact Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply lt_two_pow_of_testBit
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
  apply lt_two_pow_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

private lemma stateAt_lt (k : Nat) (constant : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k)) (rounds key : Nat) :
    stateAt k constant row.val rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) row.isLt
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

private lemma testBit_stateAt_succ {k : Nat} (hk : 2 ≤ k) (constant : Nat → Fin (2 ^ k))
    (row : Fin (2 ^ k)) (s : Nat) (key : Fin (2 ^ k)) (q : Nat) (hq : 1 ≤ q) :
    (stateAt k constant row.val (s + 1) key.val).testBit (q % k) =
      let prev := fun r : Nat => (stateAt k constant row.val s key.val).testBit (r % k)
      let m0 := xor (xor (prev q) (prev (q - 1))) (prev (q + 1))
      let m1 := xor (xor (prev (q + 1)) (prev q)) (prev (q + 2))
      let m2 := xor (xor (prev (q + 2)) (prev (q + 1))) (prev (q + 3))
      let st := xor m0 (!m1 && m2)
      xor (xor st ((rot k (2 * s) key.val).testBit (q % k)))
        ((constant (s + 1)).val.testBit (q % k)) := by
  have hk0 : 0 < k := by omega
  rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt q hk0)]
  unfold stepBit
  have hm : ∀ d : Nat, (mix k (stateAt k constant row.val s key.val)).testBit ((q % k + d) % k) =
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

private lemma bool_xor_shift_aff (a0 a1 a2 r0 r1 r2 k0 k1 k2 k3 k4 : Bool) :
    xor (xor (xor (xor k0 (k1 && xor a0 r0)) (k2 && xor a1 r1)) (k3 && xor a2 r2)) k4 =
      xor (xor (xor (xor (xor (xor (xor k0 (k1 && r0)) (k2 && r1)) (k3 && r2)) k4)
        (k1 && a0)) (k2 && a1)) (k3 && a2) := by
  have h1 : (k1 && xor a0 r0) = xor (k1 && a0) (k1 && r0) := by cases k1 <;> cases a0 <;> cases r0 <;> rfl
  have h2 : (k2 && xor a1 r1) = xor (k2 && a1) (k2 && r1) := by cases k2 <;> cases a1 <;> cases r1 <;> rfl
  have h3 : (k3 && xor a2 r2) = xor (k3 && a2) (k3 && r2) := by cases k3 <;> cases a2 <;> cases r2 <;> rfl
  rw [h1, h2, h3]
  generalize (k1 && a0) = x1
  generalize (k1 && r0) = y1
  generalize (k2 && a1) = x2
  generalize (k2 && r1) = y2
  generalize (k3 && a2) = x3
  generalize (k3 && r2) = y3
  cases k0 <;> cases k4 <;> cases x1 <;> cases y1 <;> cases x2 <;> cases y2 <;> cases x3 <;> cases y3 <;> rfl

private lemma guarded_two_round_formula {k : Nat} (hk : 12 ≤ k) (constant : Nat → Fin (2 ^ k))
    (row ref : Fin (2 ^ k)) (p : Nat)
    (hgood :
      let old := fun j : Nat => (stateAt k constant row.val 0 ref.val).testBit ((p + j) % k)
      let first := fun j : Nat => (stateAt k constant row.val 1 ref.val).testBit ((p + j) % k)
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
  let oldRef := fun j : Nat => (stateAt k constant row.val 0 ref.val).testBit ((p + j) % k)
  let firstRef := fun j : Nat => (stateAt k constant row.val 1 ref.val).testBit ((p + j) % k)
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
  have hbit0 : ∀ (kw : Fin (2 ^ k)) (j : Nat), 1 ≤ j →
      (stateAt k constant row.val 0 kw.val).testBit ((p + j) % k) =
      xor (kw.val.testBit ((p + j - 1) % k)) (row.val.testBit ((p + j) % k)) := by
    intro kw j hj
    rw [stateAt_zero, Nat.testBit_xor, testBit_rot kw.isLt (Nat.mod_lt _ hk0)]
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hsub := mod_sub_eq hk0 (p := p + j) (s := 1) (by omega)
    rw [h1m] at hsub ⊢
    rw [hsub]
  have hkey_pin : ∀ r : Nat, r < 8 →
      key.val.testBit ((p + r) % k) = ref.val.testBit ((p + r) % k) := by
    intro r hr
    have hp1 := hpin ⟨r + 1, by omega⟩
    rw [hbit0 key (r + 1) (by omega), hbit0 ref (r + 1) (by omega)] at hp1
    have hsub : p + (r + 1) - 1 = p + r := by omega
    rw [hsub] at hp1
    have := congr_arg (fun b => xor b (row.val.testBit ((p + (r + 1)) % k))) hp1
    simpa [bool_xor_cancel] using this
  have hrot0_eq : ∀ (kw : Fin (2 ^ k)) (q : Nat),
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
  have hold_eq : ∀ j : Nat, j < 9 →
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
  have hx0 : xor y0 d0 = xor u0 s0 := by
    simp only [y0, s0]; cases u0 <;> cases row9 <;> cases d0 <;> rfl
  have hx1 : xor y1 d1 = xor u1 s1 := by
    simp only [y1, s1]; cases u1 <;> cases row10 <;> cases d1 <;> rfl
  have hx2 : xor y2 d2 = xor u2 s2 := by
    simp only [y2, s2]; cases u2 <;> cases row11 <;> cases d2 <;> rfl
  rw [hx0, hx1, hx2, hxor_assoc]
  exact congrArg (xor _) (bool_xor_shift_aff u0 u1 u2 row9 row10 row11 rc0 rl0 rl1 rl2 i25)

private lemma cubic_shift_eq (s0 s1 s2 u0 u1 u2 : Bool) :
    ((xor u0 s0) && (xor u1 s1) && (xor u2 s2)) =
      xor (u0 && u1 && u2)
        (xor (xor (xor (s0 && s1 && s2)
          (xor (xor ((s1 && s2) && u0) ((s0 && s2) && u1)) ((s0 && s1) && u2)))
          (xor (s2 && u0 && u1) (s1 && u0 && u2))) (s0 && u1 && u2)) := by
  cases s0 <;> cases s1 <;> cases s2 <;> cases u0 <;> cases u1 <;> cases u2 <;> rfl

private def z2 (b : Bool) : ZMod 2 := if b then 1 else 0

private lemma z2_eq (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨m, hm⟩
  match m, hm with
  | 0, _ => exact Or.inl rfl
  | 1, _ => exact Or.inr rfl

private lemma z2_inj {a b : Bool} (h : z2 a = z2 b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

private lemma z2_xor (a b : Bool) : z2 (xor a b) = z2 a + z2 b := by
  cases a <;> cases b <;> rfl

private lemma z2_and (a b : Bool) : z2 (a && b) = z2 a * z2 b := by
  cases a <;> cases b <;> rfl

private lemma z2_bne (a b : Bool) : z2 (a != b) = z2 a + z2 b := by
  cases a <;> cases b <;> rfl

private lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases z2_eq x with rfl | rfl <;> rfl

private lemma z2_add_eq_zero {x y : ZMod 2} : x + y = 0 ↔ x = y :=
  ⟨fun h => by rw [← add_zero x, ← z2_add_self y, ← add_assoc, h, zero_add],
   fun h => h ▸ z2_add_self y⟩

private lemma z2_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (z2_eq x).resolve_left h

private lemma z2_bool_of_val (x : ZMod 2) : z2 (decide (x = 1)) = x := by
  rcases z2_eq x with rfl | rfl <;> rfl

private lemma z2_natCast_eq (n : Nat) : (n : ZMod 2) = z2 (n % 2 == 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.cast_succ, ih]
    by_cases hn : n % 2 = 0
    · have h1 : (n + 1) % 2 = 1 := by omega
      simp [hn, h1, z2]
    · have hn1 : n % 2 = 1 := by omega
      have h0 : (n + 1) % 2 = 0 := by omega
      simp [hn1, h0, z2]
      rfl

private def par (n : Nat) : Bool := n % 2 == 1

private lemma z2_par_sum {α : Type*} (s : Finset α) (f : α → Bool) :
    z2 (par (∑ i ∈ s, (f i).toNat)) = ∑ i ∈ s, z2 (f i) := by
  unfold par
  rw [← z2_natCast_eq, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by cases f i <;> rfl

private lemma mul_sum_z2 {α : Type*} [DecidableEq α] (s : Finset α) (a : ZMod 2) (f : α → ZMod 2) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => simp [Finset.sum_insert hx, mul_add, ih]

private lemma sum_mul_z2 {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ZMod 2) (a : ZMod 2) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := by
  rw [mul_comm, mul_sum_z2]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

private def toBits {k : Nat} (x : Fin (2 ^ k)) : Fin k → Bool :=
  fun i => x.val.testBit i.val

private def ofBits {k : Nat} (w : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨(List.range k).foldl (fun acc j =>
    acc ||| ((if h : j < k then w ⟨j, h⟩ else false).toNat <<< j)) 0,
    lt_two_pow_of_testBit fun j hj => by
      rw [testBit_foldl_or]
      have hmem : j ∉ List.range k := by simp [Nat.not_lt_of_ge hj]
      simp [hmem]⟩

private lemma toBits_ofBits {k : Nat} (w : Fin k → Bool) : toBits (ofBits w) = w := by
  funext i
  simp only [toBits, ofBits]
  rw [testBit_foldl_or]
  have hmem : i.val ∈ List.range k := List.mem_range.mpr i.isLt
  simp [hmem, i.isLt]

private lemma ofBits_toBits {k : Nat} (x : Fin (2 ^ k)) : ofBits (toBits x) = x := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [ofBits, toBits]
  rw [testBit_foldl_or]
  by_cases hj : j < k
  · simp [List.mem_range.mpr hj, hj]
  · have hmem : j ∉ List.range k := by simp [hj]
    have hhi : x.val.testBit j = false :=
      Nat.testBit_lt_two_pow (x.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    simp [hmem, hhi]

private def bitsEquiv (k : Nat) : Fin (2 ^ k) ≃ (Fin k → Bool) where
  toFun := toBits
  invFun := ofBits
  left_inv := ofBits_toBits
  right_inv := toBits_ofBits

private abbrev Poly (V : Type*) := Finset V → ZMod 2

private def evalMon {V : Type*} (M : Finset V) (y : V → Bool) : ZMod 2 :=
  if ∀ v ∈ M, y v = true then 1 else 0

private def evalPoly {V : Type*} [Fintype V] (P : Poly V) (y : V → Bool) : ZMod 2 :=
  ∑ M : Finset V, P M * evalMon M y

private def degLe {V : Type*} (P : Poly V) (d : Nat) : Prop :=
  ∀ M, P M ≠ 0 → M.card ≤ d

private def polyZero (V : Type*) : Poly V := fun _ => 0

private def polyOne (V : Type*) [DecidableEq V] : Poly V := fun M => if M = ∅ then 1 else 0

private def polyVar {V : Type*} [DecidableEq V] (v : V) : Poly V := fun M => if M = {v} then 1 else 0

private def polyMon {V : Type*} [DecidableEq V] (M0 : Finset V) : Poly V :=
  fun M => if M = M0 then 1 else 0

private def polyAdd {V : Type*} (P Q : Poly V) : Poly V := fun M => P M + Q M

private def polyMul {V : Type*} [Fintype V] [DecidableEq V] (P Q : Poly V) : Poly V :=
  fun M => ∑ A : Finset V, ∑ B : Finset V, if A ∪ B = M then P A * Q B else 0

private lemma evalMon_empty {V : Type*} (y : V → Bool) : evalMon (∅ : Finset V) y = 1 := by
  simp [evalMon]

private lemma evalMon_singleton {V : Type*} (v : V) (y : V → Bool) :
    evalMon ({v} : Finset V) y = z2 (y v) := by
  cases hy : y v <;> simp [evalMon, z2, hy]

private lemma ite_t {α : Type*} {p : Prop} [Decidable p] {a b : α} (h : p) :
    (if p then a else b) = a := by simp only [h, ↓reduceIte]

private lemma ite_f {α : Type*} {p : Prop} [Decidable p] {a b : α} (h : ¬ p) :
    (if p then a else b) = b := by simp only [h, ↓reduceIte]

private lemma evalMon_union {V : Type*} [DecidableEq V] (A B : Finset V) (y : V → Bool) :
    evalMon (A ∪ B) y = evalMon A y * evalMon B y := by
  unfold evalMon
  by_cases hA : ∀ v ∈ A, y v = true <;> by_cases hB : ∀ v ∈ B, y v = true
  · have hAB : ∀ v ∈ A ∪ B, y v = true := fun v hv => by
      rcases Finset.mem_union.mp hv with h | h
      · exact hA v h
      · exact hB v h
    rw [ite_t hAB, ite_t hA, ite_t hB, mul_one]
  · have hAB : ¬ ∀ v ∈ A ∪ B, y v = true := fun h => hB fun v hv => h v (Finset.mem_union_right A hv)
    rw [ite_f hAB, ite_t hA, ite_f hB, mul_zero]
  · have hAB : ¬ ∀ v ∈ A ∪ B, y v = true := fun h => hA fun v hv => h v (Finset.mem_union_left B hv)
    rw [ite_f hAB, ite_f hA, ite_t hB, zero_mul]
  · have hAB : ¬ ∀ v ∈ A ∪ B, y v = true := fun h => hA fun v hv => h v (Finset.mem_union_left B hv)
    rw [ite_f hAB, ite_f hA, ite_f hB, zero_mul]

private lemma evalPoly_zero {V : Type*} [Fintype V] (y : V → Bool) :
    evalPoly (polyZero V) y = 0 := by
  simp [evalPoly, polyZero]

private lemma evalPoly_mon {V : Type*} [Fintype V] [DecidableEq V] (M0 : Finset V) (y : V → Bool) :
    evalPoly (polyMon M0) y = evalMon M0 y := by
  unfold evalPoly polyMon
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ M0)]
  simp only [↓reduceIte, one_mul]
  rw [Finset.sum_eq_zero (fun M hM => by
    simp only [Finset.ne_of_mem_erase hM, ↓reduceIte, zero_mul]), add_zero]

private lemma evalPoly_one {V : Type*} [Fintype V] [DecidableEq V] (y : V → Bool) :
    evalPoly (polyOne V) y = 1 := by
  change evalPoly (polyMon (∅ : Finset V)) y = 1
  rw [evalPoly_mon, evalMon_empty]

private lemma evalPoly_var {V : Type*} [Fintype V] [DecidableEq V] (v : V) (y : V → Bool) :
    evalPoly (polyVar v) y = z2 (y v) := by
  change evalPoly (polyMon ({v} : Finset V)) y = z2 (y v)
  rw [evalPoly_mon, evalMon_singleton]

private lemma evalPoly_add {V : Type*} [Fintype V] (P Q : Poly V) (y : V → Bool) :
    evalPoly (polyAdd P Q) y = evalPoly P y + evalPoly Q y := by
  simp only [evalPoly, polyAdd, add_mul, Finset.sum_add_distrib]

private lemma evalPoly_mul {V : Type*} [Fintype V] [DecidableEq V] (P Q : Poly V) (y : V → Bool) :
    evalPoly (polyMul P Q) y = evalPoly P y * evalPoly Q y := by
  unfold evalPoly polyMul
  have h1 : (∑ M : Finset V, (∑ A : Finset V, ∑ B : Finset V,
        if A ∪ B = M then P A * Q B else 0) * evalMon M y) =
      ∑ M : Finset V, ∑ A : Finset V, ∑ B : Finset V,
        if A ∪ B = M then P A * Q B * evalMon M y else 0 := by
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [sum_mul_z2]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [sum_mul_z2]
    refine Finset.sum_congr rfl fun B _ => ?_
    split_ifs <;> simp
  rw [h1, Finset.sum_comm]
  have h2 : (∑ A : Finset V, ∑ M : Finset V, ∑ B : Finset V,
        if A ∪ B = M then P A * Q B * evalMon M y else 0) =
      ∑ A : Finset V, ∑ B : Finset V, P A * evalMon A y * (Q B * evalMon B y) := by
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (A ∪ B))]
    simp only [↓reduceIte]
    rw [Finset.sum_eq_zero (fun M hM => by
      have hne : A ∪ B ≠ M := (Finset.ne_of_mem_erase hM).symm
      simp only [hne, ↓reduceIte]), add_zero, evalMon_union]
    rw [mul_assoc (P A), mul_left_comm (Q B), ← mul_assoc (P A), mul_assoc]
  rw [h2, sum_mul_z2]
  exact Finset.sum_congr rfl fun A _ => (mul_sum_z2 _ _ _).symm

private lemma degLe_zero {V : Type*} (d : Nat) : degLe (polyZero V) d :=
  fun _ h => absurd rfl h

private lemma degLe_one {V : Type*} [DecidableEq V] (d : Nat) : degLe (polyOne V) d := by
  intro M hM
  unfold polyOne at hM
  split_ifs at hM with h
  · subst h; simp
  · exact absurd rfl hM

private lemma degLe_var {V : Type*} [DecidableEq V] (v : V) : degLe (polyVar v) 1 := by
  intro M hM
  unfold polyVar at hM
  split_ifs at hM with h
  · subst h; simp
  · exact absurd rfl hM

private lemma degLe_mon {V : Type*} [DecidableEq V] (M0 : Finset V) : degLe (polyMon M0) M0.card := by
  intro M hM
  unfold polyMon at hM
  split_ifs at hM with h
  · subst h; exact le_rfl
  · exact absurd rfl hM

private lemma degLe_mono {V : Type*} {P : Poly V} {a b : Nat} (h : degLe P a) (hab : a ≤ b) :
    degLe P b := fun M hM => (h M hM).trans hab

private lemma degLe_add {V : Type*} {P Q : Poly V} {d : Nat} (hP : degLe P d) (hQ : degLe Q d) :
    degLe (polyAdd P Q) d := by
  intro M hM
  by_cases hPM : P M = 0
  · have hQM : Q M ≠ 0 := by
      intro h0
      apply hM
      simp [polyAdd, hPM, h0]
    exact hQ M hQM
  · exact hP M hPM

private lemma degLe_mul {V : Type*} [Fintype V] [DecidableEq V] {P Q : Poly V} {a b : Nat}
    (hP : degLe P a) (hQ : degLe Q b) : degLe (polyMul P Q) (a + b) := by
  intro M hM
  have hex : ∃ A : Finset V, ∃ B : Finset V, A ∪ B = M ∧ P A ≠ 0 ∧ Q B ≠ 0 := by
    by_contra hall
    apply hM
    unfold polyMul
    apply Finset.sum_eq_zero
    intro A _
    apply Finset.sum_eq_zero
    intro B _
    split_ifs with hAB
    · by_cases hPA : P A = 0
      · simp [hPA]
      · by_cases hQB : Q B = 0
        · simp [hQB]
        · exact absurd ⟨A, B, hAB, hPA, hQB⟩ hall
    · rfl
  rcases hex with ⟨A, B, rfl, hPA, hQB⟩
  exact (Finset.card_union_le A B).trans (Nat.add_le_add (hP A hPA) (hQ B hQB))

private lemma exists_poly_finset_sum {V α : Type*} [Fintype V] [DecidableEq α]
    (s : Finset α) (f : α → (V → Bool) → ZMod 2) (d : Nat)
    (hf : ∀ i ∈ s, ∃ P : Poly V, degLe P d ∧ ∀ y, evalPoly P y = f i y) :
    ∃ P : Poly V, degLe P d ∧ ∀ y, evalPoly P y = ∑ i ∈ s, f i y := by
  induction s using Finset.induction_on with
  | empty => exact ⟨polyZero V, degLe_zero d, fun y => by simp [evalPoly_zero]⟩
  | insert a s ha ih =>
    obtain ⟨Pa, hPa, hePa⟩ := hf a (Finset.mem_insert_self a s)
    obtain ⟨Ps, hPs, hePs⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine ⟨polyAdd Pa Ps, degLe_add hPa hPs, fun y => ?_⟩
    rw [evalPoly_add, hePa, hePs, Finset.sum_insert ha]

private lemma exists_poly_of_fun {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → Bool) → ZMod 2) : ∃ P : Poly V, ∀ y, evalPoly P y = f y := by
  have hind : ∀ z : V → Bool, ∃ P : Poly V, ∀ y, evalPoly P y = if y = z then 1 else 0 := by
    intro z
    have hprod : ∀ s : Finset V, ∃ P : Poly V, ∀ y,
        evalPoly P y = if ∀ v ∈ s, y v = z v then 1 else 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨polyOne V, fun y => by simp [evalPoly_one]⟩
      | insert a s ha ih =>
        obtain ⟨Ps, hPs⟩ := ih
        let Pa : Poly V := if z a then polyVar a else polyAdd (polyVar a) (polyOne V)
        refine ⟨polyMul Pa Ps, fun y => ?_⟩
        rw [evalPoly_mul, hPs]
        have hPa : evalPoly Pa y = if y a = z a then 1 else 0 := by
          cases hza : z a <;> cases hya : y a
          · simp only [Pa, hza, Bool.false_eq_true, ↓reduceIte, evalPoly_add, evalPoly_var,
              evalPoly_one, z2, hya, zero_add]
          · simp only [Pa, hza, Bool.false_eq_true, ↓reduceIte, evalPoly_add, evalPoly_var,
              evalPoly_one, z2, hya, Bool.true_eq_false]
            rfl
          · simp only [Pa, hza, ↓reduceIte, evalPoly_var, z2, hya, Bool.false_eq_true]
          · simp only [Pa, hza, ↓reduceIte, evalPoly_var, z2, hya]
        rw [hPa]
        by_cases h1 : y a = z a <;> by_cases h2 : ∀ v ∈ s, y v = z v
        · have hall : ∀ v ∈ insert a s, y v = z v := fun v hv => by
            rcases Finset.mem_insert.mp hv with rfl | h
            · exact h1
            · exact h2 v h
          rw [ite_t h1, ite_t h2, ite_t hall, mul_one]
        · have hnot : ¬ ∀ v ∈ insert a s, y v = z v :=
            fun h => h2 fun v hv => h v (Finset.mem_insert_of_mem hv)
          rw [ite_t h1, ite_f h2, ite_f hnot, mul_zero]
        · have hnot : ¬ ∀ v ∈ insert a s, y v = z v :=
            fun h => h1 (h a (Finset.mem_insert_self a s))
          rw [ite_f h1, ite_t h2, ite_f hnot, zero_mul]
        · have hnot : ¬ ∀ v ∈ insert a s, y v = z v :=
            fun h => h1 (h a (Finset.mem_insert_self a s))
          rw [ite_f h1, ite_f h2, ite_f hnot, zero_mul]
    obtain ⟨P, hP⟩ := hprod Finset.univ
    refine ⟨P, fun y => ?_⟩
    rw [hP y]
    have hiff : (∀ v ∈ (Finset.univ : Finset V), y v = z v) ↔ y = z :=
      ⟨fun h => funext fun v => h v (Finset.mem_univ v), fun h v _ => congrFun h v⟩
    by_cases hy : y = z
    · rw [ite_t (hiff.mpr hy), ite_t hy]
    · rw [ite_f (fun h => hy (hiff.mp h)), ite_f hy]
  have hsum : ∀ s : Finset (V → Bool), ∃ P : Poly V, ∀ y,
      evalPoly P y = ∑ z ∈ s, if y = z then f z else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨polyZero V, fun y => by simp [evalPoly_zero]⟩
    | insert z s hz ih =>
      obtain ⟨Ps, hPs⟩ := ih
      rcases z2_eq (f z) with h0 | h1
      · refine ⟨Ps, fun y => ?_⟩
        rw [Finset.sum_insert hz, h0, ite_self, zero_add, hPs]
      · obtain ⟨Pz, hPz⟩ := hind z
        refine ⟨polyAdd Pz Ps, fun y => ?_⟩
        rw [evalPoly_add, hPz, hPs, Finset.sum_insert hz, h1]
  obtain ⟨P, hP⟩ := hsum Finset.univ
  refine ⟨P, fun y => ?_⟩
  rw [hP y, ← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
  simp only [↓reduceIte]
  rw [Finset.sum_eq_zero (fun z hz => by
    have hne : y ≠ z := (Finset.ne_of_mem_erase hz).symm
    simp [hne]), add_zero]

private def triple {r : Nat} (i : Fin r) : Finset (Fin r × Fin 3) :=
  {(i, 0), (i, 1), (i, 2)}

private lemma card_triple {r : Nat} (i : Fin r) : (triple i).card = 3 := by
  unfold triple
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
  · simp
  · simp

private lemma mem_triple_iff {r : Nat} {i : Fin r} {v : Fin r × Fin 3} :
    v ∈ triple i ↔ v.1 = i := by
  rcases v with ⟨i', j⟩
  unfold triple
  constructor
  · intro hv
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hv
    rcases hv with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  · rintro rfl
    rcases j with ⟨jv, hjv⟩
    match jv, hjv with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp

private lemma card_biUnion_triple {r : Nat} (S : Finset (Fin r)) :
    (S.biUnion triple).card = 3 * S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.biUnion_insert, Finset.card_union_of_disjoint, card_triple, ih,
      Finset.card_insert_of_notMem hi]
    · omega
    · rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [mem_triple_iff] at hv1
      rcases Finset.mem_biUnion.mp hv2 with ⟨j, hj, hvj⟩
      rw [mem_triple_iff] at hvj
      exact hi (hv1 ▸ hvj ▸ hj)

private def fullBlocks {r : Nat} (M : Finset (Fin r × Fin 3)) : Finset (Fin r) :=
  Finset.univ.filter fun i => triple i ⊆ M

private def goodMons (r e : Nat) : Finset (Finset (Fin r × Fin 3)) :=
  Finset.univ.filter fun M => (fullBlocks M).card ≤ e

private lemma prod_triples_lead {r : Nat} (G : Fin r → Poly (Fin r × Fin 3))
    (hG : ∀ i, degLe (G i) 2) (S : Finset (Fin r)) :
    ∃ D : Poly (Fin r × Fin 3),
      degLe D (3 * S.card - 1) ∧
      (S = ∅ → D = polyZero _) ∧
      ∀ y, (∏ i ∈ S, evalPoly (polyAdd (polyMon (triple i)) (G i)) y) =
        evalMon (S.biUnion triple) y + evalPoly D y := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨polyZero _, degLe_zero _, fun _ => rfl, fun y => ?_⟩
    simp [evalMon_empty, evalPoly_zero]
  | insert i S hi ih =>
    obtain ⟨D, hDdeg, hD0, hDeval⟩ := ih
    let P1 := polyMul (polyMon (triple i)) D
    let P2 := polyMul (G i) (polyMon (S.biUnion triple))
    let P3 := polyMul (G i) D
    let D' := polyAdd (polyAdd P1 P2) P3
    have hcard : (insert i S).card = S.card + 1 := Finset.card_insert_of_notMem hi
    have hD1 : degLe P1 (3 * (insert i S).card - 1) := by
      by_cases hS : S = ∅
      · subst hS
        have hDz := hD0 rfl
        have hP1z : P1 = polyZero _ := by
          funext M
          simp [P1, polyMul, hDz, polyZero]
        rw [hP1z]
        exact degLe_zero _
      · have hSpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
        have hle := degLe_mul (degLe_mon (triple i)) hDdeg
        rw [card_triple] at hle
        exact degLe_mono hle (by omega)
    have hD2 : degLe P2 (3 * (insert i S).card - 1) := by
      have hle := degLe_mul (hG i) (degLe_mon (S.biUnion triple))
      rw [card_biUnion_triple] at hle
      exact degLe_mono hle (by omega)
    have hD3 : degLe P3 (3 * (insert i S).card - 1) := by
      by_cases hS : S = ∅
      · subst hS
        have hDz := hD0 rfl
        have hP3z : P3 = polyZero _ := by
          funext M
          simp [P3, polyMul, hDz, polyZero]
        rw [hP3z]
        exact degLe_zero _
      · have hSpos : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
        have hle := degLe_mul (hG i) hDdeg
        exact degLe_mono hle (by omega)
    refine ⟨D', degLe_add (degLe_add hD1 hD2) hD3,
      fun h => absurd h (Finset.insert_ne_empty i S), fun y => ?_⟩
    rw [Finset.prod_insert hi, hDeval y, evalPoly_add, evalPoly_mon,
      Finset.biUnion_insert, evalMon_union]
    simp only [D', P1, P2, P3, evalPoly_add, evalPoly_mul, evalPoly_mon]
    rw [add_mul, mul_add, mul_add]
    ac_rfl

private lemma slice_card_le_goodMons {r e : Nat} (G : Fin r → Poly (Fin r × Fin 3))
    (hG : ∀ i, degLe (G i) 2) :
    let E := fun i => polyAdd (polyMon (triple i)) (G i)
    let H := (Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y =>
      ((Finset.univ : Finset (Fin r)).filter (fun i => evalPoly (E i) y = 1)).card ≤ e)
    H.card ≤ (goodMons r e).card := by
  intro E H
  have hred : ∀ n : Nat, ∀ M : Finset (Fin r × Fin 3), M.card = n →
      ∃ c : goodMons r e → ZMod 2, ∀ y ∈ H,
        evalMon M y = ∑ N : goodMons r e, c N * evalMon N.val y := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro M hMcard
      by_cases hgood : (fullBlocks M).card ≤ e
      · have hMmem : M ∈ goodMons r e := Finset.mem_filter.mpr ⟨Finset.mem_univ M, hgood⟩
        refine ⟨fun N => if N = ⟨M, hMmem⟩ then 1 else 0, fun y _ => ?_⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨M, hMmem⟩ : goodMons r e))]
        simp only [↓reduceIte, one_mul]
        rw [Finset.sum_eq_zero (fun N hN => by
          simp only [Finset.ne_of_mem_erase hN, ↓reduceIte, zero_mul]), add_zero]
      · let S := fullBlocks M
        have hSgt : e < S.card := Nat.lt_of_not_ge hgood
        have hSpos : 1 ≤ S.card := by omega
        let B := S.biUnion triple
        have hBsub : B ⊆ M := by
          intro v hv
          rcases Finset.mem_biUnion.mp hv with ⟨i, hi, hvi⟩
          exact (Finset.mem_filter.mp hi).2 hvi
        let R := M \ B
        have hRdisj : Disjoint R B := Finset.sdiff_disjoint
        have hRunion : R ∪ B = M := Finset.sdiff_union_of_subset hBsub
        have hRcard : R.card + 3 * S.card = M.card := by
          rw [← card_biUnion_triple S, ← Finset.card_union_of_disjoint hRdisj, hRunion]
        obtain ⟨D, hDdeg, _, hDeval⟩ := prod_triples_lead G hG S
        let Q := polyMul (polyMon R) D
        have hQdeg : degLe Q (M.card - 1) := by
          have hle := degLe_mul (degLe_mon R) hDdeg
          exact degLe_mono hle (by omega)
        have hMeq : ∀ y ∈ H, evalMon M y = evalPoly Q y := by
          intro y hy
          have hyH : ((Finset.univ : Finset (Fin r)).filter
              (fun i => evalPoly (E i) y = 1)).card ≤ e := (Finset.mem_filter.mp hy).2
          have hex0 : ∃ i ∈ S, evalPoly (E i) y = 0 := by
            by_contra hall
            have hsub : S ⊆ Finset.univ.filter (fun i => evalPoly (E i) y = 1) := by
              intro i hi
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, z2_ne_zero fun h0 => hall ⟨i, hi, h0⟩⟩
            have hle := Finset.card_le_card hsub
            omega
          rcases hex0 with ⟨i0, hi0, hEi0⟩
          have hprod0 : (∏ i ∈ S, evalPoly (E i) y) = 0 :=
            Finset.prod_eq_zero hi0 hEi0
          have hsum0 : evalMon B y + evalPoly D y = 0 := by
            rw [← hDeval y, hprod0]
          have hBeq : evalMon B y = evalPoly D y := z2_add_eq_zero.mp hsum0
          rw [← hRunion, evalMon_union, hBeq]
          simp only [Q, evalPoly_mul, evalPoly_mon]
        have hsubC : ∀ M' : Finset (Fin r × Fin 3),
            ∃ c : goodMons r e → ZMod 2, ∀ y ∈ H,
              Q M' * evalMon M' y = ∑ N : goodMons r e, c N * evalMon N.val y := by
          intro M'
          by_cases hQM' : Q M' = 0
          · exact ⟨fun _ => 0, fun y _ => by simp [hQM']⟩
          · have hlt : M'.card < n := by
              have := hQdeg M' hQM'
              omega
            obtain ⟨c, hc⟩ := ih M'.card hlt M' rfl
            have hQM1 : Q M' = 1 := z2_ne_zero hQM'
            exact ⟨c, fun y hy => by rw [hQM1, one_mul, hc y hy]⟩
        choose cFun hcFun using hsubC
        refine ⟨fun N => ∑ M' : Finset (Fin r × Fin 3), cFun M' N, fun y hy => ?_⟩
        rw [hMeq y hy]
        unfold evalPoly
        calc ∑ M' : Finset (Fin r × Fin 3), Q M' * evalMon M' y
            = ∑ M' : Finset (Fin r × Fin 3), ∑ N : goodMons r e, cFun M' N * evalMon N.val y :=
              Finset.sum_congr rfl fun M' _ => hcFun M' y hy
          _ = ∑ N : goodMons r e, ∑ M' : Finset (Fin r × Fin 3), cFun M' N * evalMon N.val y :=
              Finset.sum_comm
          _ = ∑ N : goodMons r e, (∑ M' : Finset (Fin r × Fin 3), cFun M' N) * evalMon N.val y :=
              Finset.sum_congr rfl fun N _ => (sum_mul_z2 _ _ _).symm
  let evalMap : (goodMons r e → ZMod 2) → (H → ZMod 2) :=
    fun c y => ∑ N : goodMons r e, c N * evalMon N.val y.val
  have hsurj : Function.Surjective evalMap := by
    intro g
    let gExt : (Fin r × Fin 3 → Bool) → ZMod 2 :=
      fun y => if h : y ∈ H then g ⟨y, h⟩ else 0
    obtain ⟨P, hP⟩ := exists_poly_of_fun gExt
    have hterm : ∀ M : Finset (Fin r × Fin 3),
        ∃ c : goodMons r e → ZMod 2, ∀ y ∈ H,
          P M * evalMon M y = ∑ N : goodMons r e, c N * evalMon N.val y := by
      intro M
      by_cases hPM : P M = 0
      · exact ⟨fun _ => 0, fun y _ => by simp [hPM]⟩
      · obtain ⟨c, hc⟩ := hred M.card M rfl
        have hPM1 : P M = 1 := z2_ne_zero hPM
        exact ⟨c, fun y hy => by rw [hPM1, one_mul, hc y hy]⟩
    choose cM hcM using hterm
    refine ⟨fun N => ∑ M : Finset (Fin r × Fin 3), cM M N, funext fun ⟨y, hy⟩ => ?_⟩
    simp only [evalMap]
    calc ∑ N : goodMons r e, (∑ M : Finset (Fin r × Fin 3), cM M N) * evalMon N.val y
        = ∑ N : goodMons r e, ∑ M : Finset (Fin r × Fin 3), cM M N * evalMon N.val y :=
          Finset.sum_congr rfl fun N _ => sum_mul_z2 _ _ _
      _ = ∑ M : Finset (Fin r × Fin 3), ∑ N : goodMons r e, cM M N * evalMon N.val y :=
          Finset.sum_comm
      _ = ∑ M : Finset (Fin r × Fin 3), P M * evalMon M y :=
          Finset.sum_congr rfl fun M _ => (hcM M y hy).symm
      _ = evalPoly P y := rfl
      _ = gExt y := hP y
      _ = g ⟨y, hy⟩ := by simp [gExt, hy]
  have hcardLe := Fintype.card_le_of_surjective evalMap hsurj
  simp only [Fintype.card_fun, Fintype.card_coe, ZMod.card] at hcardLe
  by_contra hlt
  have hgt : (goodMons r e).card < H.card := Nat.lt_of_not_ge hlt
  have hpow : 2 ^ (goodMons r e).card < 2 ^ H.card := Nat.pow_lt_pow_right (by omega : 1 < 2) hgt
  omega

private lemma card_triple_bad_eq_F (r : Nat) (F : Finset (Fin r)) :
    ((Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y =>
      (Finset.univ.filter (fun i : Fin r => y (i, 0) && y (i, 1) && y (i, 2))) = F)).card =
    7 ^ (r - F.card) := by
  let allT : Fin 3 → Bool := fun _ => true
  let allowed : Fin r → Finset (Fin 3 → Bool) :=
    fun i => if i ∈ F then {allT} else Finset.univ.erase allT
  have hcard_all : ∀ i : Fin r, (allowed i).card = if i ∈ F then 1 else 7 := by
    intro i
    by_cases hi : i ∈ F
    · simp [allowed, hi]
    · simp only [allowed, hi, ↓reduceIte, Finset.card_erase_of_mem (Finset.mem_univ allT),
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      rfl
  let S := Fintype.piFinset allowed
  have hbij : ((Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y =>
      (Finset.univ.filter (fun i : Fin r => y (i, 0) && y (i, 1) && y (i, 2))) = F)).card =
      S.card := by
    refine Finset.card_nbij (fun y i j => y (i, j)) ?_ ?_ ?_
    · intro y hy
      have hFeq : Finset.univ.filter (fun i : Fin r => y (i, 0) && y (i, 1) && y (i, 2)) = F :=
        (Finset.mem_filter.mp hy).2
      change (fun i j => y (i, j)) ∈ Fintype.piFinset allowed
      rw [Fintype.mem_piFinset]
      intro i
      by_cases hi : i ∈ F
      · have hhi : (y (i, 0) && y (i, 1) && y (i, 2)) = true := by
          rw [← hFeq] at hi
          exact (Finset.mem_filter.mp hi).2
        simp only [allowed, hi, ↓reduceIte, Finset.mem_singleton]
        funext j
        have h0 : y (i, 0) = true := by cases h : y (i, 0) <;> simp [h] at hhi ⊢
        have h1 : y (i, 1) = true := by cases h : y (i, 1) <;> simp [h] at hhi ⊢
        have h2 : y (i, 2) = true := by cases h : y (i, 2) <;> simp [h] at hhi ⊢
        rcases j with ⟨jv, hjv⟩
        match jv, hjv with
        | 0, _ => exact h0
        | 1, _ => exact h1
        | 2, _ => exact h2
      · have hhi : (y (i, 0) && y (i, 1) && y (i, 2)) ≠ true := by
          intro ht
          apply hi
          rw [← hFeq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, ht⟩
        simp only [allowed, hi, ↓reduceIte, Finset.mem_erase]
        refine ⟨fun heq => hhi ?_, Finset.mem_univ _⟩
        have h0 := congrFun heq 0
        have h1 := congrFun heq 1
        have h2 := congrFun heq 2
        simp [allT] at h0 h1 h2
        simp [h0, h1, h2]
    · intro y1 _ y2 _ h
      funext ⟨i, j⟩
      exact congrFun (congrFun h i) j
    · intro f hf
      change f ∈ Fintype.piFinset allowed at hf
      rw [Fintype.mem_piFinset] at hf
      refine ⟨fun p => f p.1 p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hfi := hf i
      by_cases hi : i ∈ F
      · simp only [allowed, hi, ↓reduceIte, Finset.mem_singleton] at hfi
        simp [hfi, allT, hi]
      · simp only [allowed, hi, ↓reduceIte, Finset.mem_erase] at hfi
        constructor
        · intro h3
          exfalso
          apply hfi.1
          funext j
          have h0 : f i 0 = true := by cases h : f i 0 <;> simp [h] at h3 ⊢
          have h1 : f i 1 = true := by cases h : f i 1 <;> simp [h] at h3 ⊢
          have h2 : f i 2 = true := by cases h : f i 2 <;> simp [h] at h3 ⊢
          rcases j with ⟨jv, hjv⟩
          match jv, hjv with
          | 0, _ => exact h0
          | 1, _ => exact h1
          | 2, _ => exact h2
        · intro h; exact absurd h hi
  rw [hbij, Fintype.card_piFinset]
  calc ∏ i : Fin r, (allowed i).card
      = ∏ i : Fin r, (if i ∈ F then 1 else 7) := Finset.prod_congr rfl fun i _ => hcard_all i
    _ = ∏ i ∈ Finset.univ \ F, (7 : Nat) := by
        rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => i ∈ F)]
        have h1 : (∏ i ∈ Finset.univ.filter (fun i => i ∈ F), if i ∈ F then 1 else 7) = 1 :=
          Finset.prod_eq_one fun i hi => by simp [(Finset.mem_filter.mp hi).2]
        have h2 : Finset.univ.filter (fun i => ¬ i ∈ F) = Finset.univ \ F := by
          ext i; simp
        rw [h1, one_mul, h2]
        exact Finset.prod_congr rfl fun i hi => by simp [(Finset.mem_sdiff.mp hi).2]
    _ = 7 ^ (Finset.univ \ F).card := Finset.prod_const 7
    _ = 7 ^ (r - F.card) := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ F), Finset.card_univ, Fintype.card_fin]

private lemma card_triple_bad_le (r e : Nat) :
    ((Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y =>
      ((Finset.univ : Finset (Fin r)).filter
        (fun i => y (i, 0) && y (i, 1) && y (i, 2))).card ≤ e)).card =
    ∑ j ∈ Finset.range (min e r + 1), Nat.choose r j * 7 ^ (r - j) := by
  let badOf := fun (y : Fin r × Fin 3 → Bool) =>
    Finset.univ.filter (fun i : Fin r => y (i, 0) && y (i, 1) && y (i, 2))
  let goodF := (Finset.univ : Finset (Finset (Fin r))).filter (fun F => F.card ≤ e)
  have hpart : ((Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y => (badOf y).card ≤ e)).card =
      ∑ F ∈ goodF, ((Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y => badOf y = F)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := badOf) (t := goodF)]
    · refine Finset.sum_congr rfl fun F hF => congrArg Finset.card ?_
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hFe : F.card ≤ e := (Finset.mem_filter.mp hF).2
      exact ⟨fun h => h.2, fun h => ⟨h ▸ hFe, h⟩⟩
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hy).2⟩
  rw [hpart]
  have h1 : (∑ F ∈ goodF, ((Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y => badOf y = F)).card) =
      ∑ F ∈ goodF, 7 ^ (r - F.card) :=
    Finset.sum_congr rfl fun F _ => card_triple_bad_eq_F r F
  rw [h1]
  have hpart2 : (∑ F ∈ goodF, 7 ^ (r - F.card)) =
      ∑ j ∈ Finset.range (min e r + 1),
        ∑ F ∈ goodF.filter (fun F => F.card = j), 7 ^ (r - F.card) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := Finset.card)]
    intro F hF
    rw [Finset.mem_range]
    have h1 : F.card ≤ e := (Finset.mem_filter.mp hF).2
    have h2 : F.card ≤ r := by
      have := Finset.card_le_univ F
      simpa using this
    omega
  rw [hpart2]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjle : j ≤ e := by rw [Finset.mem_range] at hj; omega
  have hfilt : goodF.filter (fun F => F.card = j) = (Finset.univ : Finset (Fin r)).powersetCard j := by
    ext F
    simp only [goodF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
      Finset.subset_univ]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hjle, h⟩⟩
  rw [hfilt]
  calc ∑ F ∈ (Finset.univ : Finset (Fin r)).powersetCard j, 7 ^ (r - F.card)
      = ∑ _F ∈ (Finset.univ : Finset (Fin r)).powersetCard j, 7 ^ (r - j) :=
        Finset.sum_congr rfl fun F hF => by rw [(Finset.mem_powersetCard.mp hF).2]
    _ = ((Finset.univ : Finset (Fin r)).powersetCard j).card * 7 ^ (r - j) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = Nat.choose r j * 7 ^ (r - j) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma card_goodMons (r e : Nat) :
    (goodMons r e).card = ∑ j ∈ Finset.range (min e r + 1), Nat.choose r j * 7 ^ (r - j) := by
  rw [← card_triple_bad_le r e]
  refine Finset.card_nbij (fun M v => decide (v ∈ M)) ?_ ?_ ?_
  · intro M hM
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hfb : (Finset.univ.filter fun i : Fin r =>
        decide ((i, 0) ∈ M) && decide ((i, 1) ∈ M) && decide ((i, 2) ∈ M)) = fullBlocks M := by
      ext i
      unfold fullBlocks triple
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h v hv
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact h.1.1
        · exact h.1.2
        · exact h.2
      · intro h
        have h0 : (i, 0) ∈ M := h (by simp)
        have h1 : (i, 1) ∈ M := h (by simp)
        have h2 : (i, 2) ∈ M := h (by simp)
        simp [h0, h1, h2]
    rw [hfb]
    exact (Finset.mem_filter.mp hM).2
  · intro M1 _ M2 _ h
    ext v
    have hv := congrFun h v
    simpa using hv
  · intro y hy
    let M : Finset (Fin r × Fin 3) := Finset.univ.filter (fun v => y v = true)
    refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · have hfb : fullBlocks M = Finset.univ.filter (fun i : Fin r => y (i, 0) && y (i, 1) && y (i, 2)) := by
        ext i
        unfold fullBlocks triple
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          have h0 : y (i, 0) = true := (Finset.mem_filter.mp (h (by simp))).2
          have h1 : y (i, 1) = true := (Finset.mem_filter.mp (h (by simp))).2
          have h2 : y (i, 2) = true := (Finset.mem_filter.mp (h (by simp))).2
          simp [h0, h1, h2]
        · intro h v hv
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rcases hv with rfl | rfl | rfl
          · cases h0 : y (i, 0) <;> simp [h0] at h ⊢
          · cases h1 : y (i, 1) <;> simp [h1] at h ⊢
          · cases h2 : y (i, 2) <;> simp [h2] at h ⊢
      rw [hfb]
      exact (Finset.mem_filter.mp hy).2
    · funext v
      simp [M]

private def linBits {k : Nat} (mask : Fin k → Bool) (w : Fin k → Bool) : Bool :=
  par (∑ i : Fin k, (mask i && w i).toNat)

private def quadBits {k : Nat} (g : (Fin k → Bool) → Bool) : Prop :=
  ∃ (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool),
    ∀ w, g w = xor (xor b (linBits l w))
      (par (∑ i : Fin k, ∑ j : Fin k, (a i j && w i && w j).toNat))

private lemma z2_linBits {k : Nat} (mask w : Fin k → Bool) :
    z2 (linBits mask w) = ∑ i : Fin k, z2 (mask i) * z2 (w i) := by
  rw [linBits, z2_par_sum]
  exact Finset.sum_congr rfl fun i _ => z2_and (mask i) (w i)

private lemma z2_quadBits_iff {k : Nat} (g : (Fin k → Bool) → Bool) :
    quadBits g ↔ ∃ (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool),
      ∀ w, z2 (g w) = z2 b + (∑ i : Fin k, z2 (l i) * z2 (w i)) +
        ∑ i : Fin k, ∑ j : Fin k, z2 (a i j) * z2 (w i) * z2 (w j) := by
  constructor
  · rintro ⟨b, l, a, hg⟩
    refine ⟨b, l, a, fun w => ?_⟩
    rw [hg w, z2_xor, z2_xor, z2_linBits]
    unfold par
    rw [← z2_natCast_eq, Nat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases a i j <;> cases w i <;> cases w j <;> rfl
  · rintro ⟨b, l, a, hg⟩
    refine ⟨b, l, a, fun w => z2_inj ?_⟩
    rw [hg w, z2_xor, z2_xor, z2_linBits]
    unfold par
    rw [← z2_natCast_eq, Nat.cast_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases a i j <;> cases w i <;> cases w j <;> rfl

private lemma quadBits_const {k : Nat} (c : Bool) : quadBits (fun _ : Fin k → Bool => c) := by
  rw [z2_quadBits_iff]
  exact ⟨c, fun _ => false, fun _ _ => false, fun w => by simp [z2]⟩

private lemma quadBits_var {k : Nat} (c : Bool) (v : Fin k) :
    quadBits (fun w : Fin k → Bool => c && w v) := by
  rw [z2_quadBits_iff]
  refine ⟨false, fun i => if i = v then c else false, fun _ _ => false, fun w => ?_⟩
  simp only [z2, Bool.false_eq_true, ↓reduceIte, zero_add, zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  simp only [↓reduceIte]
  rw [Finset.sum_eq_zero (fun i hi => by
    simp only [Finset.ne_of_mem_erase hi, ↓reduceIte, Bool.false_eq_true, zero_mul]), add_zero]
  cases c <;> cases w v <;> rfl

private lemma quadBits_and2 {k : Nat} (c : Bool) (v1 v2 : Fin k) :
    quadBits (fun w : Fin k → Bool => c && w v1 && w v2) := by
  rw [z2_quadBits_iff]
  refine ⟨false, fun _ => false, fun i j => if i = v1 ∧ j = v2 then c else false, fun w => ?_⟩
  simp only [z2, Bool.false_eq_true, ↓reduceIte, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v1)]
  rw [Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero fun j _ => by
    have hne : ¬ (i = v1 ∧ j = v2) := fun h => Finset.ne_of_mem_erase hi h.1
    simp only [hne, ↓reduceIte, Bool.false_eq_true, zero_mul]), add_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v2)]
  simp only [and_self, ↓reduceIte]
  rw [Finset.sum_eq_zero (fun j hj => by
    have hne : j ≠ v2 := Finset.ne_of_mem_erase hj
    simp [hne]), add_zero]
  cases c <;> cases w v1 <;> cases w v2 <;> rfl

private lemma quadBits_xor {k : Nat} {g1 g2 : (Fin k → Bool) → Bool}
    (h1 : quadBits g1) (h2 : quadBits g2) :
    quadBits (fun w => xor (g1 w) (g2 w)) := by
  rw [z2_quadBits_iff] at h1 h2 ⊢
  rcases h1 with ⟨b1, l1, a1, hg1⟩
  rcases h2 with ⟨b2, l2, a2, hg2⟩
  refine ⟨xor b1 b2, fun i => xor (l1 i) (l2 i), fun i j => xor (a1 i j) (a2 i j), fun w => ?_⟩
  rw [z2_xor, hg1 w, hg2 w, z2_xor]
  have hl : (∑ i : Fin k, z2 (xor (l1 i) (l2 i)) * z2 (w i)) =
      (∑ i : Fin k, z2 (l1 i) * z2 (w i)) + (∑ i : Fin k, z2 (l2 i) * z2 (w i)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [z2_xor, add_mul]
  have ha : (∑ i : Fin k, ∑ j : Fin k, z2 (xor (a1 i j) (a2 i j)) * z2 (w i) * z2 (w j)) =
      (∑ i : Fin k, ∑ j : Fin k, z2 (a1 i j) * z2 (w i) * z2 (w j)) +
      (∑ i : Fin k, ∑ j : Fin k, z2 (a2 i j) * z2 (w i) * z2 (w j)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [z2_xor, add_mul, add_mul]
  rw [hl, ha]
  ac_rfl

private def inAff {k : Nat} (pinKey S : Finset (Fin k)) (refBits b0 : Fin k → Bool)
    (coeff : Fin k → Fin k → Bool) (w : Fin k → Bool) : Bool :=
  decide ((∀ z ∈ pinKey, w z = refBits z) ∧
    ∀ s ∈ S, w s = xor (b0 s) (par (∑ v ∈ (Finset.univ \ pinKey) \ S, (coeff s v && w v).toNat)))

private lemma z2_inAff_eq {k : Nat} {pinKey S : Finset (Fin k)} {refBits b0 : Fin k → Bool}
    {coeff : Fin k → Fin k → Bool} {w : Fin k → Bool}
    (hw : inAff pinKey S refBits b0 coeff w = true) :
    (∀ z ∈ pinKey, w z = refBits z) ∧
    ∀ s ∈ S, z2 (w s) = z2 (b0 s) +
      ∑ v ∈ (Finset.univ \ pinKey) \ S, z2 (coeff s v) * z2 (w v) := by
  have h := of_decide_eq_true hw
  refine ⟨h.1, fun s hs => ?_⟩
  rw [h.2 s hs, z2_xor, z2_par_sum]
  exact congrArg (z2 (b0 s) + ·) (Finset.sum_congr rfl fun v _ => z2_and (coeff s v) (w v))

private lemma inAff_iff_z2 {k : Nat} (pinKey S : Finset (Fin k)) (refBits b0 : Fin k → Bool)
    (coeff : Fin k → Fin k → Bool) (w : Fin k → Bool) :
    inAff pinKey S refBits b0 coeff w = true ↔
      (∀ z ∈ pinKey, w z = refBits z) ∧
      ∀ s ∈ S, z2 (w s) = z2 (b0 s) +
        ∑ v ∈ (Finset.univ \ pinKey) \ S, z2 (coeff s v) * z2 (w v) := by
  constructor
  · exact z2_inAff_eq
  · rintro ⟨h1, h2⟩
    unfold inAff
    rw [decide_eq_true_eq]
    refine ⟨h1, fun s hs => z2_inj ?_⟩
    rw [h2 s hs, z2_xor, z2_par_sum]
    exact congrArg (z2 (b0 s) + ·) (Finset.sum_congr rfl fun v _ => (z2_and (coeff s v) (w v)).symm)

private lemma card_inAff {k : Nat} (pinKey S : Finset (Fin k)) (hS : S ⊆ Finset.univ \ pinKey)
    (refBits b0 : Fin k → Bool) (coeff : Fin k → Fin k → Bool) :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun w => inAff pinKey S refBits b0 coeff w = true)).card =
      2 ^ (k - pinKey.card - S.card) := by
  let Free := (Finset.univ \ pinKey) \ S
  have hFree_card : Free.card = k - pinKey.card - S.card := by
    rw [Finset.card_sdiff_of_subset hS, Finset.card_sdiff_of_subset (Finset.subset_univ pinKey),
      Finset.card_univ, Fintype.card_fin]
  have hdisj : Disjoint pinKey S :=
    Finset.disjoint_left.mpr fun x hxp hxS => (Finset.mem_sdiff.mp (hS hxS)).2 hxp
  let lift : ({v : Fin k // v ∈ Free} → Bool) → (Fin k → Bool) := fun u z =>
    if z ∈ pinKey then refBits z
    else if z ∈ S then xor (b0 z) (par (∑ v ∈ Free, (coeff z v &&
      (if hv : v ∈ Free then u ⟨v, hv⟩ else false)).toNat))
    else if hz : z ∈ Free then u ⟨z, hz⟩ else false
  have hbij : ((Finset.univ : Finset (Fin k → Bool)).filter
      (fun w => inAff pinKey S refBits b0 coeff w = true)).card =
      Fintype.card ({v : Fin k // v ∈ Free} → Bool) := by
    rw [← Finset.card_univ]
    refine Finset.card_nbij (fun w v => w v.val) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro w1 hw1 w2 hw2 h
      have h1 := (inAff_iff_z2 pinKey S refBits b0 coeff w1).mp (Finset.mem_filter.mp hw1).2
      have h2 := (inAff_iff_z2 pinKey S refBits b0 coeff w2).mp (Finset.mem_filter.mp hw2).2
      funext z
      by_cases hzp : z ∈ pinKey
      · rw [h1.1 z hzp, h2.1 z hzp]
      · by_cases hzS : z ∈ S
        · apply z2_inj
          rw [h1.2 z hzS, h2.2 z hzS]
          congr 1
          refine Finset.sum_congr rfl fun v hv => ?_
          have hveq : w1 v = w2 v := congrFun h ⟨v, hv⟩
          rw [hveq]
        · have hzF : z ∈ Free :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzp⟩, hzS⟩
          exact congrFun h ⟨z, hzF⟩
    · intro u _
      refine ⟨lift u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · unfold inAff
        rw [decide_eq_true_eq]
        refine ⟨fun z hz => by simp [lift, hz], fun s hs => ?_⟩
        have hsp : s ∉ pinKey := Finset.disjoint_right.mp hdisj hs
        simp only [lift, hsp, hs, ↓reduceIte]
        congr 2
        refine Finset.sum_congr rfl fun v hv => ?_
        have hvp : v ∉ pinKey := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
        have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
        simp [hvp, hvS]
      · funext ⟨v, hv⟩
        have hvp : v ∉ pinKey := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
        have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
        simp [lift, hvp, hvS, hv]
  rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hFree_card]

private lemma splitAff {k : Nat} (pinKey S : Finset (Fin k)) (hS : S ⊆ Finset.univ \ pinKey)
    (refBits b0 : Fin k → Bool) (coeff : Fin k → Fin k → Bool) (mask : Fin k → Bool) :
    (∃ c : Bool, ∀ w, inAff pinKey S refBits b0 coeff w = true → linBits mask w = c) ∨
    (∃ v0 ∈ (Finset.univ \ pinKey) \ S,
      ∀ b : Bool, ∃ (b0' : Fin k → Bool) (coeff' : Fin k → Fin k → Bool),
        ∀ w, (inAff pinKey S refBits b0 coeff w = true ∧ linBits mask w = b) ↔
          inAff pinKey (insert v0 S) refBits b0' coeff' w = true) := by
  let F := Finset.univ \ pinKey
  let Free := F \ S
  have hdisj : Disjoint pinKey S :=
    Finset.disjoint_left.mpr fun x hxp hxS => (Finset.mem_sdiff.mp (hS hxS)).2 hxp
  have hpart : ∀ g : Fin k → ZMod 2,
      (∑ z : Fin k, g z) = (∑ z ∈ pinKey, g z) + (∑ s ∈ S, g s) + (∑ v ∈ Free, g v) := by
    intro g
    have h1 : Finset.univ = pinKey ∪ F := by
      ext z; simp [F]
    have h2 : F = S ∪ Free := (Finset.union_sdiff_of_subset hS).symm
    have hd1 : Disjoint pinKey F := Finset.disjoint_sdiff
    have hd2 : Disjoint S Free := Finset.disjoint_sdiff
    rw [h1, Finset.sum_union hd1, h2, Finset.sum_union hd2, add_assoc]
  let constVal : ZMod 2 :=
    (∑ z ∈ pinKey, z2 (mask z) * z2 (refBits z)) + (∑ s ∈ S, z2 (mask s) * z2 (b0 s))
  let effMask : Fin k → ZMod 2 :=
    fun v => z2 (mask v) + ∑ s ∈ S, z2 (mask s) * z2 (coeff s v)
  have hlin_eq : ∀ w, inAff pinKey S refBits b0 coeff w = true →
      z2 (linBits mask w) = constVal + ∑ v ∈ Free, effMask v * z2 (w v) := by
    intro w hw
    obtain ⟨hpin, hS_eq⟩ := z2_inAff_eq hw
    rw [z2_linBits, hpart]
    have hp : (∑ z ∈ pinKey, z2 (mask z) * z2 (w z)) =
        ∑ z ∈ pinKey, z2 (mask z) * z2 (refBits z) :=
      Finset.sum_congr rfl fun z hz => by rw [hpin z hz]
    have hs : (∑ s ∈ S, z2 (mask s) * z2 (w s)) =
        (∑ s ∈ S, z2 (mask s) * z2 (b0 s)) +
        ∑ v ∈ Free, (∑ s ∈ S, z2 (mask s) * z2 (coeff s v)) * z2 (w v) := by
      calc ∑ s ∈ S, z2 (mask s) * z2 (w s)
          = ∑ s ∈ S, z2 (mask s) * (z2 (b0 s) + ∑ v ∈ Free, z2 (coeff s v) * z2 (w v)) :=
            Finset.sum_congr rfl fun s hs => by rw [hS_eq s hs]
        _ = (∑ s ∈ S, z2 (mask s) * z2 (b0 s)) +
            ∑ s ∈ S, ∑ v ∈ Free, z2 (mask s) * z2 (coeff s v) * z2 (w v) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun s _ => ?_
            rw [mul_add, mul_sum_z2]
            exact congrArg (_ + ·) (Finset.sum_congr rfl fun v _ => (mul_assoc _ _ _).symm)
        _ = (∑ s ∈ S, z2 (mask s) * z2 (b0 s)) +
            ∑ v ∈ Free, (∑ s ∈ S, z2 (mask s) * z2 (coeff s v)) * z2 (w v) := by
            congr 1
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun v _ => (sum_mul_z2 _ _ _).symm
    have hcomb : (∑ v ∈ Free, (∑ s ∈ S, z2 (mask s) * z2 (coeff s v)) * z2 (w v)) +
        (∑ v ∈ Free, z2 (mask v) * z2 (w v)) =
        ∑ v ∈ Free, effMask v * z2 (w v) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => ?_
      simp only [effMask, add_mul]
      rw [add_comm]
    rw [hp, hs, ← hcomb]
    dsimp only [constVal]
    ac_rfl
  by_cases hex : ∃ v0 ∈ Free, effMask v0 ≠ 0
  · right
    rcases hex with ⟨v0, hv0, hv0ne⟩
    have hv0_1 : effMask v0 = 1 := z2_ne_zero hv0ne
    have hv0_notS : v0 ∉ S := (Finset.mem_sdiff.mp hv0).2
    have hFree' : F \ insert v0 S = Free.erase v0 := by
      ext v
      simp only [Free, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
      tauto
    refine ⟨v0, hv0, fun b => ?_⟩
    let b0v : Bool := decide (constVal + z2 b = 1)
    let cfv : Fin k → Bool := fun v => decide (effMask v = 1)
    let b0' : Fin k → Bool := fun s =>
      if s = v0 then b0v else xor (b0 s) (coeff s v0 && b0v)
    let coeff' : Fin k → Fin k → Bool := fun s v =>
      if s = v0 then cfv v else xor (coeff s v) (coeff s v0 && cfv v)
    refine ⟨b0', coeff', fun w => ?_⟩
    rw [inAff_iff_z2, inAff_iff_z2]
    have hlin_split : ∀ (hwA : inAff pinKey S refBits b0 coeff w = true),
        (linBits mask w = b) ↔
          z2 (w v0) = z2 b0v + ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v) := by
      intro hwA
      have hle := hlin_eq w hwA
      rw [← Finset.add_sum_erase _ _ hv0, hv0_1, one_mul] at hle
      have hcf : (∑ v ∈ Free.erase v0, effMask v * z2 (w v)) =
          ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v) :=
        Finset.sum_congr rfl fun v _ => by rw [z2_bool_of_val (effMask v)]
      rw [hcf] at hle
      constructor
      · intro hb
        rw [hb] at hle
        have h0 : z2 b + (constVal + (z2 (w v0) + ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v))) = 0 :=
          z2_add_eq_zero.mpr hle
        rw [z2_bool_of_val]
        apply z2_add_eq_zero.mp
        calc z2 (w v0) + (constVal + z2 b + ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v))
            = z2 b + (constVal + (z2 (w v0) + ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v))) := by
              ac_rfl
          _ = 0 := h0
      · intro hwv0
        apply z2_inj
        rw [hle, hwv0, z2_bool_of_val]
        rw [add_assoc (constVal + z2 b), z2_add_self, add_zero, ← add_assoc, z2_add_self, zero_add]
    have hsub_s : ∀ s ∈ S,
        z2 (b0 s) + ∑ v ∈ Free, z2 (coeff s v) * z2 (w v) =
          (z2 (b0' s) + ∑ v ∈ Free.erase v0, z2 (coeff' s v) * z2 (w v)) +
          z2 (coeff s v0) * (z2 (w v0) + (z2 b0v + ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v))) := by
      intro s hs
      have hne : s ≠ v0 := fun h => hv0_notS (h ▸ hs)
      rw [← Finset.add_sum_erase _ _ hv0]
      simp only [b0', coeff', hne, ↓reduceIte, z2_xor, z2_and]
      have hsum_cf : (∑ v ∈ Free.erase v0, (z2 (coeff s v) + z2 (coeff s v0) * z2 (cfv v)) * z2 (w v)) =
          (∑ v ∈ Free.erase v0, z2 (coeff s v) * z2 (w v)) +
          z2 (coeff s v0) * (∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v)) := by
        rw [mul_sum_z2, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by rw [add_mul, mul_assoc]
      rw [hsum_cf, mul_add, mul_add]
      set X0 := z2 (b0 s)
      set X1 := z2 (coeff s v0) * z2 b0v
      set X2 := ∑ v ∈ Free.erase v0, z2 (coeff s v) * z2 (w v)
      set X3 := z2 (coeff s v0) * ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v)
      set X4 := z2 (coeff s v0) * z2 (w v0)
      calc X0 + (X4 + X2)
          = X0 + (X4 + X2) + (X1 + X1) + (X3 + X3) := by rw [z2_add_self, add_zero, z2_add_self, add_zero]
        _ = (X0 + X1 + (X2 + X3)) + (X4 + (X1 + X3)) := by ac_rfl
    constructor
    · rintro ⟨⟨hpin, hSeq⟩, hlin⟩
      have hwA : inAff pinKey S refBits b0 coeff w = true :=
        (inAff_iff_z2 pinKey S refBits b0 coeff w).mpr ⟨hpin, hSeq⟩
      have hwv0 := (hlin_split hwA).mp hlin
      refine ⟨hpin, fun s hs => ?_⟩
      change z2 (w s) = z2 (b0' s) + ∑ v ∈ F \ insert v0 S, z2 (coeff' s v) * z2 (w v)
      rw [hFree']
      rcases Finset.mem_insert.mp hs with rfl | hsS
      · simpa only [b0', coeff', ↓reduceIte] using hwv0
      · rw [hSeq s hsS, hsub_s s hsS, hwv0, z2_add_self, mul_zero, add_zero]
    · rintro ⟨hpin, hS'eq⟩
      have hwv0 : z2 (w v0) = z2 b0v + ∑ v ∈ Free.erase v0, z2 (cfv v) * z2 (w v) := by
        have h := hS'eq v0 (Finset.mem_insert_self v0 S)
        change z2 (w v0) = z2 (b0' v0) + ∑ v ∈ F \ insert v0 S, z2 (coeff' v0 v) * z2 (w v) at h
        rw [hFree'] at h
        simpa only [b0', coeff', ↓reduceIte] using h
      have hSeq : ∀ s ∈ S, z2 (w s) = z2 (b0 s) + ∑ v ∈ Free, z2 (coeff s v) * z2 (w v) := by
        intro s hs
        have h := hS'eq s (Finset.mem_insert_of_mem hs)
        change z2 (w s) = z2 (b0' s) + ∑ v ∈ F \ insert v0 S, z2 (coeff' s v) * z2 (w v) at h
        rw [hFree'] at h
        rw [hsub_s s hs, hwv0, z2_add_self, mul_zero, add_zero]
        exact h
      have hwA : inAff pinKey S refBits b0 coeff w = true :=
        (inAff_iff_z2 pinKey S refBits b0 coeff w).mpr ⟨hpin, hSeq⟩
      exact ⟨⟨hpin, hSeq⟩, (hlin_split hwA).mpr hwv0⟩
  · left
    refine ⟨decide (constVal = 1), fun w hw => z2_inj ?_⟩
    rw [hlin_eq w hw, z2_bool_of_val]
    have h0 : (∑ v ∈ Free, effMask v * z2 (w v)) = 0 :=
      Finset.sum_eq_zero fun v hv => by
        have hve : effMask v = 0 := by
          by_contra hne
          exact hex ⟨v, hv, hne⟩
        rw [hve, zero_mul]
    rw [h0, add_zero]

private lemma pullQuad_aff {k r : Nat} (pinKey S : Finset (Fin k))
    (hS : S ⊆ Finset.univ \ pinKey) (refBits b0 : Fin k → Bool) (coeff : Fin k → Fin k → Bool)
    (vIdx : Fin r × Fin 3 ↪ Fin k)
    (hvFree : ∀ p, vIdx p ∈ (Finset.univ \ pinKey) \ S)
    (wR : Fin k → Bool) :
    let Free := (Finset.univ \ pinKey) \ S
    let embed : (Fin r × Fin 3 → Bool) → (Fin k → Bool) := fun y z =>
      if z ∈ pinKey then refBits z
      else if z ∈ S then xor (b0 z) (par (∑ v ∈ Free, (coeff z v &&
        (if h : ∃ p, vIdx p = v then y (Classical.choose h) else wR v)).toNat))
      else if h : ∃ p, vIdx p = z then y (Classical.choose h) else wR z
    (∀ y, inAff pinKey S refBits b0 coeff (embed y) = true) ∧
    (∀ y p, embed y (vIdx p) = y p) ∧
    (∀ g : (Fin k → Bool) → Bool, quadBits g →
      ∃ G : Poly (Fin r × Fin 3), degLe G 2 ∧ ∀ y, evalPoly G y = z2 (g (embed y))) := by
  intro Free embed
  have hdisj : Disjoint pinKey S :=
    Finset.disjoint_left.mpr fun x hxp hxS => (Finset.mem_sdiff.mp (hS hxS)).2 hxp
  have hinner : ∀ y (v : Fin k), v ∈ Free →
      embed y v = if h : ∃ p, vIdx p = v then y (Classical.choose h) else wR v := by
    intro y v hv
    have hvp : v ∉ pinKey := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    simp [embed, hvp, hvS]
  have hembed_in : ∀ y, inAff pinKey S refBits b0 coeff (embed y) = true := by
    intro y
    unfold inAff
    rw [decide_eq_true_eq]
    refine ⟨fun z hz => by simp [embed, hz], fun s hs => ?_⟩
    have hsp : s ∉ pinKey := Finset.disjoint_right.mp hdisj hs
    conv_lhs => unfold embed; simp only [hsp, hs, ↓reduceIte]
    congr 2
    exact Finset.sum_congr rfl fun v hv => by rw [hinner y v hv]
  have hembed_v : ∀ y p, embed y (vIdx p) = y p := by
    intro y p
    rw [hinner y (vIdx p) (hvFree p)]
    have hex : ∃ q, vIdx q = vIdx p := ⟨p, rfl⟩
    simp only [hex, ↓reduceDIte]
    exact congrArg y (vIdx.injective (Classical.choose_spec hex))
  have hcoord_deg1 : ∀ z : Fin k,
      ∃ P : Poly (Fin r × Fin 3), degLe P 1 ∧ ∀ y, evalPoly P y = z2 (embed y z) := by
    have hfree_deg1 : ∀ v : Fin k,
        ∃ P : Poly (Fin r × Fin 3), degLe P 1 ∧ ∀ y,
          evalPoly P y = z2 (if h : ∃ p, vIdx p = v then y (Classical.choose h) else wR v) := by
      intro v
      by_cases h : ∃ p, vIdx p = v
      · refine ⟨polyVar (Classical.choose h), degLe_var _, fun y => ?_⟩
        rw [evalPoly_var]
        simp only [h, ↓reduceDIte]
      · refine ⟨if wR v then polyOne _ else polyZero _, ?_, fun y => ?_⟩
        · split_ifs
          · exact degLe_one 1
          · exact degLe_zero 1
        · simp only [h, ↓reduceDIte]
          cases hrv : wR v <;> simp [evalPoly_one, evalPoly_zero, z2]
    intro z
    by_cases hzp : z ∈ pinKey
    · refine ⟨if refBits z then polyOne _ else polyZero _, ?_, fun y => ?_⟩
      · split_ifs
        · exact degLe_one 1
        · exact degLe_zero 1
      · simp only [embed, hzp, ↓reduceIte]
        cases refBits z <;> simp [evalPoly_one, evalPoly_zero, z2]
    · by_cases hzS : z ∈ S
      · obtain ⟨Psum, hPsum_deg, hPsum_eval⟩ :=
          exists_poly_finset_sum Free
            (fun v y => z2 (coeff z v) *
              z2 (if h : ∃ p, vIdx p = v then y (Classical.choose h) else wR v))
            1 (fun v _ => by
              cases hcv : coeff z v
              · exact ⟨polyZero _, degLe_zero 1, fun y => by simp [evalPoly_zero, z2]⟩
              · obtain ⟨Pv, hPv_deg, hPv_eval⟩ := hfree_deg1 v
                exact ⟨Pv, hPv_deg, fun y => by simp [hPv_eval, z2]⟩)
        let Pconst : Poly (Fin r × Fin 3) := if b0 z then polyOne _ else polyZero _
        have hPc_deg : degLe Pconst 1 := by
          unfold Pconst; split_ifs
          · exact degLe_one 1
          · exact degLe_zero 1
        refine ⟨polyAdd Pconst Psum, degLe_add hPc_deg hPsum_deg, fun y => ?_⟩
        simp only [embed, hzp, hzS, ↓reduceIte, z2_xor, z2_par_sum]
        rw [evalPoly_add, hPsum_eval y]
        have hPc_eval : evalPoly Pconst y = z2 (b0 z) := by
          cases hb : b0 z <;> simp [Pconst, hb, evalPoly_one, evalPoly_zero, z2]
        rw [hPc_eval]
        congr 1
        exact Finset.sum_congr rfl fun v _ => (z2_and (coeff z v) _).symm
      · obtain ⟨Pv, hPv_deg, hPv_eval⟩ := hfree_deg1 z
        refine ⟨Pv, hPv_deg, fun y => ?_⟩
        simp only [embed, hzp, hzS, ↓reduceIte]
        exact hPv_eval y
  refine ⟨hembed_in, hembed_v, fun g hg => ?_⟩
  rw [z2_quadBits_iff] at hg
  rcases hg with ⟨b, l, a, hgeq⟩
  choose coordP hcoordDeg hcoordEval using hcoord_deg1
  let Pb : Poly (Fin r × Fin 3) := if b then polyOne _ else polyZero _
  have hPb_deg : degLe Pb 2 := by
    unfold Pb; split_ifs
    · exact degLe_one 2
    · exact degLe_zero 2
  have hPb_eval : ∀ y, evalPoly Pb y = z2 b := fun y => by
    cases b <;> simp [Pb, evalPoly_one, evalPoly_zero, z2]
  obtain ⟨Pl, hPl_deg, hPl_eval⟩ := exists_poly_finset_sum Finset.univ
    (fun i y => z2 (l i) * z2 (embed y i)) 2 (fun i _ => by
      cases l i
      · exact ⟨polyZero _, degLe_zero 2, fun y => by simp [evalPoly_zero, z2]⟩
      · exact ⟨coordP i, degLe_mono (hcoordDeg i) (by omega), fun y => by
          simp [hcoordEval i y, z2]⟩)
  obtain ⟨Pa, hPa_deg, hPa_eval⟩ := exists_poly_finset_sum Finset.univ
    (fun i y => ∑ j : Fin k, z2 (a i j) * z2 (embed y i) * z2 (embed y j)) 2 (fun i _ =>
      exists_poly_finset_sum Finset.univ
        (fun j y => z2 (a i j) * z2 (embed y i) * z2 (embed y j)) 2 (fun j _ => by
          cases a i j
          · exact ⟨polyZero _, degLe_zero 2, fun y => by simp [evalPoly_zero, z2]⟩
          · exact ⟨polyMul (coordP i) (coordP j),
              degLe_mul (hcoordDeg i) (hcoordDeg j), fun y => by
                rw [evalPoly_mul, hcoordEval i y, hcoordEval j y]
                simp [z2]⟩))
  refine ⟨polyAdd (polyAdd Pb Pl) Pa, degLe_add (degLe_add hPb_deg hPl_deg) hPa_deg, fun y => ?_⟩
  rw [hgeq (embed y), evalPoly_add, evalPoly_add, hPb_eval y, hPl_eval y, hPa_eval y]

private lemma score_aff_le_B {k m : Nat}
    (pinKey S : Finset (Fin k)) (hS : S ⊆ Finset.univ \ pinKey)
    (refBits b0 : Fin k → Bool) (coeff : Fin k → Fin k → Bool)
    (tKey : Fin m × Fin 3 ↪ Fin k)
    (htFree : ∀ p, tKey p ∉ pinKey)
    (Q : Fin m → (Fin k → Bool) → Bool) (hQ : ∀ i, quadBits (Q i))
    (P : Fin m → (Fin k → Bool) → Bool) (hP : ∀ i, quadBits (P i))
    (e : Nat) :
    let target := fun (w : Fin k → Bool) (i : Fin m) =>
      xor (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) (Q i w)
    let r := m - S.card
    (((Finset.univ : Finset (Fin k → Bool)).filter
      (fun w => inAff pinKey S refBits b0 coeff w = true)).filter
      (fun w => ((Finset.univ : Finset (Fin m)).filter
        (fun i => P i w != target w i)).card ≤ e)).card ≤
    2 ^ (k - pinKey.card - S.card - 3 * r) *
      ∑ j ∈ Finset.range (min e r + 1), Nat.choose r j * 7 ^ (r - j) := by
  intro target r
  by_cases hSm : m ≤ S.card
  · have hr0 : r = 0 := Nat.sub_eq_zero_of_le hSm
    simp only [hr0, Nat.mul_zero, Nat.sub_zero, Nat.min_zero, Nat.zero_add,
      Finset.range_one, Finset.sum_singleton, Nat.choose_self, pow_zero, mul_one]
    calc (((Finset.univ : Finset (Fin k → Bool)).filter
            (fun w => inAff pinKey S refBits b0 coeff w = true)).filter _).card
        ≤ ((Finset.univ : Finset (Fin k → Bool)).filter
            (fun w => inAff pinKey S refBits b0 coeff w = true)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ (k - pinKey.card - S.card) := card_inAff pinKey S hS refBits b0 coeff
  · have hSlt : S.card < m := Nat.lt_of_not_ge hSm
    let U := (Finset.univ : Finset (Fin m)).filter (fun i =>
      tKey (i, 0) ∉ S ∧ tKey (i, 1) ∉ S ∧ tKey (i, 2) ∉ S)
    have hUcard : r ≤ U.card := by
      let hit := (Finset.univ : Finset (Fin m)) \ U
      have hhit_le : hit.card ≤ S.card := by
        have hex : ∀ i ∈ hit, ∃ j : Fin 3, tKey (i, j) ∈ S := by
          intro i hi
          have hnotU : i ∉ U := (Finset.mem_sdiff.mp hi).2
          by_contra hall
          apply hnotU
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_, ?_, ?_⟩
          · exact fun h => hall ⟨0, h⟩
          · exact fun h => hall ⟨1, h⟩
          · exact fun h => hall ⟨2, h⟩
        choose jOf hjOf using hex
        have hinj : Set.InjOn (fun i => if h : i ∈ hit then tKey (i, jOf i h) else tKey (i, 0)) hit := by
          intro i1 h1 i2 h2 heq
          have h1' : i1 ∈ hit := h1
          have h2' : i2 ∈ hit := h2
          simp only [h1', h2', ↓reduceDIte] at heq
          exact congrArg Prod.fst (tKey.injective heq)
        have himg : hit.image (fun i => if h : i ∈ hit then tKey (i, jOf i h) else tKey (i, 0)) ⊆ S := by
          intro v hv
          rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
          simp only [hi, ↓reduceDIte]
          exact hjOf i hi
        calc hit.card
            = (hit.image _).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ S.card := Finset.card_le_card himg
      have hUs : U.card + hit.card = m := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ U), Finset.card_univ, Fintype.card_fin]
        have : U.card ≤ m := by
          have := Finset.card_le_univ U
          simpa using this
        omega
      omega
    obtain ⟨U0, hU0sub, hU0card⟩ := Finset.exists_subset_card_eq hUcard
    let eU0 : Fin r ≃ {i : Fin m // i ∈ U0} :=
      (Equiv.cast (congrArg Fin hU0card)).symm.trans (Finset.equivFin U0).symm
    let ι : Fin r ↪ Fin m :=
      ⟨fun i => (eU0 i).val, fun i1 i2 h => eU0.injective (Subtype.ext h)⟩
    let vIdx : Fin r × Fin 3 ↪ Fin k :=
      ⟨fun p => tKey (ι p.1, p.2), fun p1 p2 h => by
        have h12 := tKey.injective h
        exact Prod.ext (ι.injective (Prod.mk.inj h12).1) (Prod.mk.inj h12).2⟩
    let Free := (Finset.univ \ pinKey) \ S
    have hvFree : ∀ p : Fin r × Fin 3, vIdx p ∈ Free := by
      intro ⟨i, j⟩
      have hiU : ι i ∈ U := hU0sub (eU0 i).property
      have hnotS := (Finset.mem_filter.mp hiU).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, htFree _⟩, ?_⟩
      rcases j with ⟨jv, hjv⟩
      match jv, hjv with
      | 0, _ => exact hnotS.1
      | 1, _ => exact hnotS.2.1
      | 2, _ => exact hnotS.2.2
    let V0 : Finset (Fin k) := Finset.univ.image vIdx
    have hV0sub : V0 ⊆ Free := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨p, _, rfl⟩
      exact hvFree p
    have hV0card : V0.card = 3 * r := by
      rw [Finset.card_image_of_injective _ vIdx.injective, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      omega
    let R := Free \ V0
    have hRcard : R.card = k - pinKey.card - S.card - 3 * r := by
      rw [Finset.card_sdiff_of_subset hV0sub, hV0card,
        Finset.card_sdiff_of_subset hS, Finset.card_sdiff_of_subset (Finset.subset_univ pinKey),
        Finset.card_univ, Fintype.card_fin]
    let A := (Finset.univ : Finset (Fin k → Bool)).filter
      (fun w => inAff pinKey S refBits b0 coeff w = true)
    let GoodA := A.filter (fun w =>
      ((Finset.univ : Finset (Fin m)).filter (fun i => P i w != target w i)).card ≤ e)
    have hpart : GoodA.card =
        ∑ wR : {z : Fin k // z ∈ R} → Bool,
          (GoodA.filter (fun w => (fun z : {z : Fin k // z ∈ R} => w z.val) = wR)).card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun (w : Fin k → Bool) (z : {z : Fin k // z ∈ R}) => w z.val) (t := Finset.univ)]
      intro _ _; exact Finset.mem_univ _
    rw [hpart]
    have hslice : ∀ wR : {z : Fin k // z ∈ R} → Bool,
        (GoodA.filter (fun w => (fun z : {z : Fin k // z ∈ R} => w z.val) = wR)).card ≤
          ∑ j ∈ Finset.range (min e r + 1), Nat.choose r j * 7 ^ (r - j) := by
      intro wR
      let wRExt : Fin k → Bool := fun z => if hz : z ∈ R then wR ⟨z, hz⟩ else false
      obtain ⟨hembed_in, hembed_v, hpull⟩ :=
        pullQuad_aff pinKey S hS refBits b0 coeff vIdx hvFree wRExt
      let embed : (Fin r × Fin 3 → Bool) → (Fin k → Bool) := fun y z =>
        if z ∈ pinKey then refBits z
        else if z ∈ S then xor (b0 z) (par (∑ v ∈ Free, (coeff z v &&
          (if h : ∃ p, vIdx p = v then y (Classical.choose h) else wRExt v)).toNat))
        else if h : ∃ p, vIdx p = z then y (Classical.choose h) else wRExt z
      have hGex : ∀ i : Fin r, ∃ Gi : Poly (Fin r × Fin 3), degLe Gi 2 ∧
          ∀ y, evalPoly Gi y = z2 (xor (P (ι i) (embed y)) (Q (ι i) (embed y))) := by
        intro i
        exact hpull (fun w => xor (P (ι i) w) (Q (ι i) w)) (quadBits_xor (hP (ι i)) (hQ (ι i)))
      choose G hGdeg hGeval using hGex
      let E := fun i => polyAdd (polyMon (triple i)) (G i)
      let H := (Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y =>
        ((Finset.univ : Finset (Fin r)).filter (fun i => evalPoly (E i) y = 1)).card ≤ e)
      have hleH : (GoodA.filter (fun w => (fun z : {z : Fin k // z ∈ R} => w z.val) = wR)).card ≤
          H.card := by
        refine Finset.card_le_card_of_injOn (fun w p => w (vIdx p)) ?_ ?_
        · intro w hw
          have hwGood := (Finset.mem_filter.mp hw).1
          have hwR := (Finset.mem_filter.mp hw).2
          have hwA := (Finset.mem_filter.mp hwGood).1
          have hwErr := (Finset.mem_filter.mp hwGood).2
          have hwAff : inAff pinKey S refBits b0 coeff w = true := (Finset.mem_filter.mp hwA).2
          have hw_eq : w = embed (fun p => w (vIdx p)) := by
            have h1 := (inAff_iff_z2 pinKey S refBits b0 coeff w).mp hwAff
            have h2 := (inAff_iff_z2 pinKey S refBits b0 coeff (embed (fun p => w (vIdx p)))).mp
              (hembed_in (fun p => w (vIdx p)))
            have hFree_eq : ∀ v ∈ Free, w v = embed (fun p => w (vIdx p)) v := by
              intro v hv
              by_cases hvV0 : v ∈ V0
              · rcases Finset.mem_image.mp hvV0 with ⟨p, _, rfl⟩
                exact (hembed_v (fun q => w (vIdx q)) p).symm
              · have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨hv, hvV0⟩
                have hvp : v ∉ pinKey := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2
                have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
                have hnex : ¬ ∃ p, vIdx p = v := fun ⟨p, hp⟩ =>
                  hvV0 (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩)
                have hwrv : w v = wR ⟨v, hvR⟩ := congrFun hwR ⟨v, hvR⟩
                simp only [embed, hvp, hvS, ↓reduceIte, hnex, ↓reduceDIte, wRExt, hvR, hwrv]
            funext z
            by_cases hzp : z ∈ pinKey
            · rw [h1.1 z hzp, h2.1 z hzp]
            · by_cases hzS : z ∈ S
              · apply z2_inj
                rw [h1.2 z hzS, h2.2 z hzS]
                congr 1
                exact Finset.sum_congr rfl fun v hv => by rw [hFree_eq v hv]
              · exact hFree_eq z (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzp⟩, hzS⟩)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hsub : ((Finset.univ : Finset (Fin r)).filter
                (fun i => evalPoly (E i) (fun p => w (vIdx p)) = 1)).image ι ⊆
              (Finset.univ : Finset (Fin m)).filter (fun i => P i w != target w i) := by
            intro j hj
            rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
            have hE1 : evalPoly (E i) (fun p => w (vIdx p)) = 1 := (Finset.mem_filter.mp hi).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            have hEt : evalPoly (E i) (fun p => w (vIdx p)) = z2 (P (ι i) w != target w (ι i)) := by
              simp only [E, evalPoly_add, evalPoly_mon, hGeval i, ← hw_eq]
              have hmon : evalMon (triple i) (fun p => w (vIdx p)) =
                  z2 (w (tKey (ι i, 0)) && w (tKey (ι i, 1)) && w (tKey (ι i, 2))) := by
                have hiff : (∀ v ∈ triple i, w (vIdx v) = true) ↔
                    (w (tKey (ι i, 0)) && w (tKey (ι i, 1)) && w (tKey (ι i, 2))) = true := by
                  simp only [triple, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp,
                    forall_eq, Bool.and_eq_true, and_assoc]
                  rfl
                by_cases h3 : (w (tKey (ι i, 0)) && w (tKey (ι i, 1)) && w (tKey (ι i, 2))) = true
                · unfold evalMon
                  split_ifs with h
                  · rw [h3]; rfl
                  · exact absurd (hiff.mpr h3) h
                · have h3f : (w (tKey (ι i, 0)) && w (tKey (ι i, 1)) && w (tKey (ι i, 2))) = false :=
                    Bool.eq_false_iff.mpr h3
                  unfold evalMon
                  split_ifs with h
                  · exact absurd (hiff.mp h) h3
                  · rw [h3f]; rfl
              rw [hmon, z2_bne]
              simp only [target, z2_xor]
              rw [add_comm (z2 (P (ι i) w)), ← add_assoc, add_comm (z2 (P (ι i) w))]
            rw [hEt] at hE1
            exact z2_inj hE1
          calc ((Finset.univ : Finset (Fin r)).filter
                (fun i => evalPoly (E i) (fun p => w (vIdx p)) = 1)).card
              = (((Finset.univ : Finset (Fin r)).filter
                  (fun i => evalPoly (E i) (fun p => w (vIdx p)) = 1)).image ι).card :=
                (Finset.card_image_of_injective _ ι.injective).symm
            _ ≤ ((Finset.univ : Finset (Fin m)).filter (fun i => P i w != target w i)).card :=
                Finset.card_le_card hsub
            _ ≤ e := hwErr
        · intro w1 hw1 w2 hw2 heq
          have hw1Aff : inAff pinKey S refBits b0 coeff w1 = true :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw1).1).1).2
          have hw2Aff : inAff pinKey S refBits b0 coeff w2 = true :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hw2).1).1).2
          have hw1R : (fun z : {z : Fin k // z ∈ R} => w1 z.val) = wR := (Finset.mem_filter.mp hw1).2
          have hw2R : (fun z : {z : Fin k // z ∈ R} => w2 z.val) = wR := (Finset.mem_filter.mp hw2).2
          have h1 := (inAff_iff_z2 pinKey S refBits b0 coeff w1).mp hw1Aff
          have h2 := (inAff_iff_z2 pinKey S refBits b0 coeff w2).mp hw2Aff
          have hFree_eq : ∀ v ∈ Free, w1 v = w2 v := by
            intro v hv
            by_cases hvV0 : v ∈ V0
            · rcases Finset.mem_image.mp hvV0 with ⟨p, _, rfl⟩
              exact congrFun heq p
            · have hvR : v ∈ R := Finset.mem_sdiff.mpr ⟨hv, hvV0⟩
              rw [congrFun hw1R ⟨v, hvR⟩, congrFun hw2R ⟨v, hvR⟩]
          funext z
          by_cases hzp : z ∈ pinKey
          · rw [h1.1 z hzp, h2.1 z hzp]
          · by_cases hzS : z ∈ S
            · apply z2_inj
              rw [h1.2 z hzS, h2.2 z hzS]
              congr 1
              exact Finset.sum_congr rfl fun v hv => by rw [hFree_eq v hv]
            · exact hFree_eq z (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzp⟩, hzS⟩)
      exact hleH.trans ((slice_card_le_goodMons G hGdeg).trans (le_of_eq (card_goodMons r e)))
    have hsum_le : ∀ (s : Finset ({z : Fin k // z ∈ R} → Bool)) (f : ({z : Fin k // z ∈ R} → Bool) → Nat) (c : Nat),
        (∀ x ∈ s, f x ≤ c) → (∑ x ∈ s, f x) ≤ s.card * c := by
      intro s f c hf
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, Nat.add_mul, Nat.one_mul,
          Nat.add_comm (s.card * c)]
        exact Nat.add_le_add (hf a (Finset.mem_insert_self a s))
          (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))
    have hres := hsum_le Finset.univ _ _ (fun wR _ => hslice wR)
    have hcardR : (Finset.univ : Finset ({z : Fin k // z ∈ R} → Bool)).card =
        2 ^ (k - pinKey.card - S.card - 3 * r) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hRcard]
    rwa [hcardR] at hres

private def T_fn (r e : Nat) : Nat :=
  ∑ j ∈ Finset.range (min e r + 1), Nat.choose r j * 7 ^ (r - j)

private def B_fn (F_sz m p e : Nat) : Nat :=
  let r := m - p
  2 ^ (F_sz - p - 3 * r) * T_fn r e

private def delta_fn (F_sz m e j : Nat) : Nat :=
  if j < m then
    2 ^ (F_sz - 3 * m + 2 * j) * (Nat.choose (m - j - 1) e * 7 ^ (m - j - 1 - e))
  else 0

private lemma T_step_le (r : Nat) : ∀ t, t ≤ r →
    8 * ∑ j ∈ Finset.range (t + 1), Nat.choose r j * 7 ^ (r - j) =
      (∑ j ∈ Finset.range (t + 1), Nat.choose (r + 1) j * 7 ^ (r + 1 - j)) +
        Nat.choose r t * 7 ^ (r - t) := by
  intro t
  induction t with
  | zero =>
    intro _
    change 8 * (∑ j ∈ Finset.range 1, Nat.choose r j * 7 ^ (r - j)) =
      (∑ j ∈ Finset.range 1, Nat.choose (r + 1) j * 7 ^ (r + 1 - j)) +
        Nat.choose r 0 * 7 ^ (r - 0)
    simp only [Finset.range_one, Finset.sum_singleton, Nat.choose_zero_right, Nat.sub_zero,
      Nat.one_mul, Nat.pow_succ]
    omega
  | succ t ih =>
    intro ht
    have ht' : t ≤ r := by omega
    conv_lhs => rw [Finset.sum_range_succ, Nat.mul_add, ih ht']
    conv_rhs => rw [Finset.sum_range_succ]
    have hrt : r - t = (r - (t + 1)) + 1 := by omega
    have hr1 : r + 1 - (t + 1) = r - t := by omega
    rw [hr1, hrt, Nat.pow_succ, Nat.choose_succ_succ]
    set P := 7 ^ (r - (t + 1))
    set C0 := Nat.choose r t
    set C1 := Nat.choose r (t + 1)
    have hEq : C0 * (P * 7) + 8 * (C1 * P) = (C0 + C1) * (P * 7) + C1 * P := by
      rw [Nat.add_mul]
      have h8 : 8 * (C1 * P) = C1 * (P * 7) + C1 * P := by
        have h7 : C1 * (P * 7) = 7 * (C1 * P) := by
          rw [Nat.mul_comm P 7, ← Nat.mul_assoc, Nat.mul_comm C1 7, Nat.mul_assoc]
        rw [h7]; omega
      rw [h8, ← Nat.add_assoc]
    rw [Nat.add_assoc, hEq, ← Nat.add_assoc]

private lemma T_full (r : Nat) :
    ∑ j ∈ Finset.range (r + 1), Nat.choose r j * 7 ^ (r - j) = 8 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h := T_step_le r r le_rfl
    rw [ih, Nat.choose_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one] at h
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, Nat.pow_zero, Nat.mul_one, ← h,
      Nat.pow_succ, Nat.mul_comm]

private lemma T_step (r e : Nat) :
    8 * T_fn r e = T_fn (r + 1) e + Nat.choose r e * 7 ^ (r - e) := by
  unfold T_fn
  by_cases her : e ≤ r
  · have h1 : min e r = e := Nat.min_eq_left her
    have h2 : min e (r + 1) = e := Nat.min_eq_left (by omega)
    rw [h1, h2]
    exact T_step_le r e her
  · have hlt : r < e := Nat.lt_of_not_ge her
    have h1 : min e r = r := Nat.min_eq_right (by omega)
    have h2 : min e (r + 1) = r + 1 := Nat.min_eq_right (by omega)
    rw [h1, h2, T_full r, T_full (r + 1), Nat.choose_eq_zero_of_lt hlt, Nat.zero_mul,
      Nat.add_zero, Nat.pow_succ, Nat.mul_comm]

private lemma two_mul_B_succ {F_sz m e j : Nat} (h3m : 3 * m ≤ F_sz) (hj : j < F_sz) :
    2 * B_fn F_sz m (j + 1) e = B_fn F_sz m j e + delta_fn F_sz m e j := by
  unfold B_fn delta_fn
  by_cases hjm : j < m
  · simp only [hjm, ↓reduceIte]
    have he1 : F_sz - (j + 1) - 3 * (m - (j + 1)) = (F_sz - 3 * m + 2 * j) + 2 := by omega
    have he2 : F_sz - j - 3 * (m - j) = F_sz - 3 * m + 2 * j := by omega
    have hmr : m - (j + 1) + 1 = m - j := by omega
    have hmr' : m - (j + 1) = m - j - 1 := by omega
    rw [he1, he2, Nat.pow_add, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    have h24 : 2 * (2 ^ (F_sz - 3 * m + 2 * j) * (2 * 2) * T_fn (m - (j + 1)) e) =
        2 ^ (F_sz - 3 * m + 2 * j) * (8 * T_fn (m - (j + 1)) e) := by
      rw [Nat.mul_assoc (2 ^ _), Nat.mul_left_comm 2 (2 ^ _)]
      congr 1
      have : 2 * (2 * 2 * T_fn (m - (j + 1)) e) = 8 * T_fn (m - (j + 1)) e := by omega
      exact this
    rw [h24, T_step (m - (j + 1)) e, Nat.mul_add, hmr, hmr']
  · simp only [hjm, ↓reduceIte, Nat.add_zero]
    have hm1 : m - j = 0 := by omega
    have hm2 : m - (j + 1) = 0 := by omega
    rw [hm1, hm2, Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    have hT0 : T_fn 0 e = 1 := by
      simp [T_fn]
    rw [hT0, Nat.mul_one, Nat.mul_one]
    have hsub : F_sz - j = (F_sz - (j + 1)) + 1 := by omega
    rw [hsub, Nat.pow_succ, Nat.mul_comm]

private lemma choose_le_succ (q e : Nat) : Nat.choose q e ≤ Nat.choose (q + 1) e := by
  cases e with
  | zero => simp
  | succ e =>
    rw [Nat.choose_succ_succ]
    exact Nat.le_add_left _ _

private lemma delta_step {F_sz m e j : Nat} :
    delta_fn F_sz m e (j + 1) ≤ delta_fn F_sz m e j := by
  unfold delta_fn
  by_cases hj1 : j + 1 < m
  · have hj : j < m := by omega
    simp only [hj1, hj, ↓reduceIte]
    set q := m - (j + 1) - 1
    have hq1 : m - j - 1 = q + 1 := by omega
    rw [hq1]
    by_cases hqe : e ≤ q
    · have hpow2 : F_sz - 3 * m + 2 * (j + 1) = (F_sz - 3 * m + 2 * j) + 2 := by omega
      have hpow7 : q + 1 - e = (q - e) + 1 := by omega
      rw [hpow2, hpow7, Nat.pow_add, Nat.pow_succ 7 (q - e)]
      have h4 : 2 ^ 2 = 4 := rfl
      rw [h4]
      have hc : Nat.choose q e ≤ Nat.choose (q + 1) e := choose_le_succ q e
      calc 2 ^ (F_sz - 3 * m + 2 * j) * 4 * (Nat.choose q e * 7 ^ (q - e))
          = 2 ^ (F_sz - 3 * m + 2 * j) * (Nat.choose q e * (7 ^ (q - e) * 4)) := by
            rw [Nat.mul_assoc (2 ^ _), Nat.mul_comm 4, Nat.mul_assoc (Nat.choose q e),
              Nat.mul_comm (7 ^ (q - e)) 4]
        _ ≤ 2 ^ (F_sz - 3 * m + 2 * j) * (Nat.choose (q + 1) e * (7 ^ (q - e) * 7)) := by
            apply Nat.mul_le_mul_left
            exact Nat.mul_le_mul hc (Nat.mul_le_mul_left _ (by omega))
    · have hlt : q < e := Nat.lt_of_not_ge hqe
      rw [Nat.choose_eq_zero_of_lt hlt, Nat.zero_mul, Nat.mul_zero]
      exact Nat.zero_le _
  · simp only [hj1, ↓reduceIte]
    exact Nat.zero_le _

private lemma delta_antitone {F_sz m e i j : Nat} (hij : i ≤ j) :
    delta_fn F_sz m e j ≤ delta_fn F_sz m e i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    rw [← Nat.add_assoc]
    exact delta_step.trans ih

private lemma telescope_B {F_sz m e d : Nat} (h3m : 3 * m ≤ F_sz) (hd : d ≤ F_sz) :
    B_fn F_sz m 0 e + ∑ j ∈ Finset.range d, 2 ^ j * delta_fn F_sz m e j =
      2 ^ d * B_fn F_sz m d e := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ih (by omega), ← Nat.mul_add,
      ← two_mul_B_succ h3m (by omega), ← Nat.mul_assoc, Nat.pow_succ]

private lemma sum_pow_two_range (d : Nat) :
    ∑ j ∈ Finset.range d, 2 ^ j = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih, Nat.pow_succ]
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    omega

private lemma nat_sum_le_sum {α : Type*} [DecidableEq α] (s : Finset α) (f g : α → Nat)
    (h : ∀ x ∈ s, f x ≤ g x) : (∑ x ∈ s, f x) ≤ ∑ x ∈ s, g x := by
  induction s using Finset.induction_on with
  | empty => exact le_rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Nat.add_le_add (h a (Finset.mem_insert_self a s))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

private lemma nat_sum_mul_const {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Nat) (c : Nat) :
    (∑ x ∈ s, f x * c) = (∑ x ∈ s, f x) * c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, Nat.add_mul]

private lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have hd : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hu : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hp : p x <;> simp [hp]
  rw [← Finset.card_union_of_disjoint hd, hu]

private lemma greedy_bound {F_sz m e L N_len : Nat}
    (h3m : 3 * m ≤ F_sz) (hL : 0 < L)
    (cnt : Nat → Nat) (hcap : ∀ j, cnt j ≤ 2 ^ j)
    (hsum : (∑ j ∈ Finset.range N_len, cnt j) ≤ L - 1) :
    let M := min L (2 ^ m)
    let d := Nat.log2 M
    let a := M - 2 ^ d
    B_fn F_sz m 0 e + ∑ j ∈ Finset.range N_len, cnt j * delta_fn F_sz m e j ≤
      (2 ^ d - a) * B_fn F_sz m d e + 2 * a * B_fn F_sz m (d + 1) e := by
  intro M d a
  have hMpos : 0 < M := Nat.lt_min.mpr ⟨hL, Nat.two_pow_pos m⟩
  have hMne : M ≠ 0 := by omega
  have h2d_le : 2 ^ d ≤ M := Nat.log2_self_le hMne
  have hM_lt : M < 2 ^ (d + 1) := Nat.lt_log2_self
  have ha_lt : a < 2 ^ d := by
    have : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
    omega
  have hd_le_m : d ≤ m := by
    by_contra hgt
    have hlt : m < d := Nat.lt_of_not_ge hgt
    have hp : 2 ^ m < 2 ^ d := Nat.pow_lt_pow_right (by omega : 1 < 2) hlt
    have hMle : M ≤ 2 ^ m := Nat.min_le_right L (2 ^ m)
    omega
  by_cases hLge : 2 ^ m ≤ L
  · have hMeq : M = 2 ^ m := Nat.min_eq_right hLge
    have hdeq : d = m := by
      have h1 : 2 ^ d ≤ 2 ^ m := hMeq ▸ h2d_le
      have h2 : 2 ^ m < 2 ^ (d + 1) := hMeq ▸ hM_lt
      by_contra hne
      have hlt : d < m := by omega
      have h3 : 2 ^ (d + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)
      omega
    have ha0 : a = 0 := by
      have h2eq : 2 ^ d = 2 ^ m := congrArg (2 ^ ·) hdeq
      dsimp only [a]
      omega
    simp only [ha0, Nat.sub_zero, Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
    rw [hdeq, ← telescope_B h3m (by omega : m ≤ F_sz)]
    apply Nat.add_le_add_left
    let R := max N_len m
    have hsub1 : (∑ j ∈ Finset.range N_len, cnt j * delta_fn F_sz m e j) ≤
        ∑ j ∈ Finset.range R, cnt j * delta_fn F_sz m e j := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j => j < N_len)]
      have hf : (Finset.range R).filter (fun j => j < N_len) = Finset.range N_len := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hf]
      exact Nat.le_add_right _ _
    have hsplit : (∑ j ∈ Finset.range R, cnt j * delta_fn F_sz m e j) =
        ∑ j ∈ Finset.range m, cnt j * delta_fn F_sz m e j := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j => j < m)]
      have hf1 : (Finset.range R).filter (fun j => j < m) = Finset.range m := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      have hf2 : (∑ j ∈ (Finset.range R).filter (fun j => ¬ j < m), cnt j * delta_fn F_sz m e j) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          have hnm : ¬ j < m := (Finset.mem_filter.mp hj).2
          simp [delta_fn, hnm]
      rw [hf1, hf2, Nat.add_zero]
    rw [hsplit] at hsub1
    exact hsub1.trans (nat_sum_le_sum (Finset.range m) _ _ fun j _ =>
      Nat.mul_le_mul_right _ (hcap j))
  · have hLlt : L < 2 ^ m := Nat.lt_of_not_ge hLge
    have hMeq : M = L := Nat.min_eq_left (by omega)
    have hd_lt_m : d < m := by
      by_contra hge
      have hdeq : d = m := by omega
      have : 2 ^ m ≤ L := by rw [← hMeq, ← hdeq]; exact h2d_le
      omega
    let cnt' : Nat → Nat := fun j => if j < N_len then cnt j else 0
    let R := max N_len d
    have hcnt'_cap : ∀ j, cnt' j ≤ 2 ^ j := fun j => by
      dsimp only [cnt']; split_ifs
      · exact hcap j
      · exact Nat.zero_le _
    have hcnt'_sum : (∑ j ∈ Finset.range R, cnt' j) ≤ L - 1 := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j => j < N_len)]
      have hf1 : (Finset.range R).filter (fun j => j < N_len) = Finset.range N_len := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      have h1 : (∑ j ∈ Finset.range N_len, cnt' j) = ∑ j ∈ Finset.range N_len, cnt j :=
        Finset.sum_congr rfl fun j hj => by simp [cnt', Finset.mem_range.mp hj]
      have h2 : (∑ j ∈ (Finset.range R).filter (fun j => ¬ j < N_len), cnt' j) = 0 :=
        Finset.sum_eq_zero fun j hj => by simp [cnt', (Finset.mem_filter.mp hj).2]
      rw [hf1, h1, h2, Nat.add_zero]
      exact hsum
    have hcnt'_obj : (∑ j ∈ Finset.range N_len, cnt j * delta_fn F_sz m e j) =
        ∑ j ∈ Finset.range R, cnt' j * delta_fn F_sz m e j := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j => j < N_len)]
      have hf1 : (Finset.range R).filter (fun j => j < N_len) = Finset.range N_len := by
        ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
      have h1 : (∑ j ∈ Finset.range N_len, cnt' j * delta_fn F_sz m e j) =
          ∑ j ∈ Finset.range N_len, cnt j * delta_fn F_sz m e j :=
        Finset.sum_congr rfl fun j hj => by simp [cnt', Finset.mem_range.mp hj]
      have h2 : (∑ j ∈ (Finset.range R).filter (fun j => ¬ j < N_len), cnt' j * delta_fn F_sz m e j) = 0 :=
        Finset.sum_eq_zero fun j hj => by simp [cnt', (Finset.mem_filter.mp hj).2]
      rw [hf1, h1, h2, Nat.add_zero]
    have hlo_eq : (Finset.range R).filter (fun j => j < d) = Finset.range d := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
    let hiSet := (Finset.range R).filter (fun j => ¬ j < d)
    have hsum_split : (∑ j ∈ Finset.range d, cnt' j) + (∑ j ∈ hiSet, cnt' j) ≤
        (∑ j ∈ Finset.range d, 2 ^ j) + a := by
      have hs1 := hcnt'_sum
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j => j < d), hlo_eq] at hs1
      change (∑ j ∈ Finset.range d, cnt' j) + (∑ j ∈ hiSet, cnt' j) ≤ L - 1 at hs1
      rw [sum_pow_two_range d]
      have h2dpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
      have h2d_leL : 2 ^ d ≤ L := hMeq ▸ h2d_le
      have ha_eq : a = L - 2 ^ d := by simp [a, hMeq]
      omega
    have hlo_add : (∑ j ∈ Finset.range d, cnt' j) + (∑ j ∈ Finset.range d, (2 ^ j - cnt' j)) =
        ∑ j ∈ Finset.range d, 2 ^ j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Nat.add_sub_cancel' (hcnt'_cap j)
    have hhi_le : (∑ j ∈ hiSet, cnt' j) ≤ (∑ j ∈ Finset.range d, (2 ^ j - cnt' j)) + a := by
      omega
    have hstep1 : (∑ j ∈ hiSet, cnt' j * delta_fn F_sz m e j) ≤
        (∑ j ∈ Finset.range d, (2 ^ j - cnt' j) * delta_fn F_sz m e j) + a * delta_fn F_sz m e d := by
      calc ∑ j ∈ hiSet, cnt' j * delta_fn F_sz m e j
          ≤ ∑ j ∈ hiSet, cnt' j * delta_fn F_sz m e d :=
            nat_sum_le_sum hiSet _ _ fun j hj =>
              Nat.mul_le_mul_left _ (delta_antitone (by
                have hnd : ¬ j < d := (Finset.mem_filter.mp hj).2
                omega))
        _ = (∑ j ∈ hiSet, cnt' j) * delta_fn F_sz m e d := nat_sum_mul_const _ _ _
        _ ≤ ((∑ j ∈ Finset.range d, (2 ^ j - cnt' j)) + a) * delta_fn F_sz m e d :=
            Nat.mul_le_mul_right _ hhi_le
        _ = (∑ j ∈ Finset.range d, (2 ^ j - cnt' j) * delta_fn F_sz m e d) +
            a * delta_fn F_sz m e d := by
            rw [Nat.add_mul, nat_sum_mul_const]
        _ ≤ (∑ j ∈ Finset.range d, (2 ^ j - cnt' j) * delta_fn F_sz m e j) +
            a * delta_fn F_sz m e d := by
            apply Nat.add_le_add_right
            exact nat_sum_le_sum (Finset.range d) _ _ fun j hj =>
              Nat.mul_le_mul_left _ (delta_antitone (by have := Finset.mem_range.mp hj; omega))
    have hstep2 : (∑ j ∈ Finset.range R, cnt' j * delta_fn F_sz m e j) ≤
        (∑ j ∈ Finset.range d, 2 ^ j * delta_fn F_sz m e j) + a * delta_fn F_sz m e d := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.range R) (fun j => j < d), hlo_eq]
      have hcomb : (∑ j ∈ Finset.range d, cnt' j * delta_fn F_sz m e j) +
          (∑ j ∈ Finset.range d, (2 ^ j - cnt' j) * delta_fn F_sz m e j) =
          ∑ j ∈ Finset.range d, 2 ^ j * delta_fn F_sz m e j := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by
          rw [← Nat.add_mul, Nat.add_sub_cancel' (hcnt'_cap j)]
      calc (∑ j ∈ Finset.range d, cnt' j * delta_fn F_sz m e j) +
            (∑ j ∈ hiSet, cnt' j * delta_fn F_sz m e j)
          ≤ (∑ j ∈ Finset.range d, cnt' j * delta_fn F_sz m e j) +
            ((∑ j ∈ Finset.range d, (2 ^ j - cnt' j) * delta_fn F_sz m e j) +
              a * delta_fn F_sz m e d) := Nat.add_le_add_left hstep1 _
        _ = (∑ j ∈ Finset.range d, 2 ^ j * delta_fn F_sz m e j) +
            a * delta_fn F_sz m e d := by rw [← Nat.add_assoc, hcomb]
    have htele : B_fn F_sz m 0 e + (∑ j ∈ Finset.range d, 2 ^ j * delta_fn F_sz m e j) +
        a * delta_fn F_sz m e d =
        (2 ^ d - a) * B_fn F_sz m d e + 2 * a * B_fn F_sz m (d + 1) e := by
      rw [telescope_B h3m (by omega : d ≤ F_sz)]
      have hsplit2d : 2 ^ d = (2 ^ d - a) + a := (Nat.sub_add_cancel (by omega)).symm
      conv_lhs => rw [hsplit2d]
      rw [Nat.add_mul, Nat.add_assoc, ← Nat.mul_add, ← two_mul_B_succ h3m (by omega : d < F_sz)]
      rw [Nat.mul_left_comm a 2 (B_fn F_sz m (d + 1) e), Nat.mul_assoc 2 a]
    rw [hcnt'_obj]
    calc B_fn F_sz m 0 e + ∑ j ∈ Finset.range R, cnt' j * delta_fn F_sz m e j
        ≤ B_fn F_sz m 0 e + ((∑ j ∈ Finset.range d, 2 ^ j * delta_fn F_sz m e j) +
            a * delta_fn F_sz m e d) := Nat.add_le_add_left hstep2 _
      _ = (2 ^ d - a) * B_fn F_sz m d e + 2 * a * B_fn F_sz m (d + 1) e := by
          rw [← Nat.add_assoc, htele]

private def runIter {α : Type*} (f : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => runIter f n (f x)

private lemma foldl_const_eq_runIter {α β : Type*} (f : α → α) (xs : List β) (x : α) :
    xs.foldl (fun p _ => f p) x = runIter f xs.length x := by
  induction xs generalizing x with
  | nil => rfl
  | cons _ xs ih => exact ih (f x)

private lemma runIter_fixed {α : Type*} {f : α → α} {x : α} (hx : f x = x) :
    ∀ n, runIter f n x = x
  | 0 => rfl
  | n + 1 => by simp only [runIter, hx]; exact runIter_fixed hx n

private def isPref (p q : List Bool) : Bool :=
  decide (p.length ≤ q.length ∧ q.take p.length = p)

private def subT (T : Finset (List Bool)) (p : List Bool) : Finset (List Bool) :=
  T.filter (fun q => isPref p q = true)

private lemma subT_split_card {T : Finset (List Bool)} {p : List Bool} (hp : p ∈ T) :
    (subT T (p ++ [false])).card + (subT T (p ++ [true])).card + 1 ≤ (subT T p).card := by
  have hp_mem : p ∈ subT T p :=
    Finset.mem_filter.mpr ⟨hp, decide_eq_true ⟨le_rfl, List.take_length⟩⟩
  have hsub_b : ∀ b : Bool, subT T (p ++ [b]) ⊆ (subT T p).erase p := by
    intro b q hq
    have hqT : q ∈ T := (Finset.mem_filter.mp hq).1
    have hqp : (p ++ [b]).length ≤ q.length ∧ q.take (p ++ [b]).length = p ++ [b] :=
      of_decide_eq_true (Finset.mem_filter.mp hq).2
    have hlen : p.length + 1 ≤ q.length := by simpa using hqp.1
    have hne : q ≠ p := fun h => by subst h; omega
    have htake : q.take p.length = p := by
      have h1 : (q.take (p.length + 1)).take p.length = q.take p.length := by
        rw [List.take_take, Nat.min_eq_left (by omega)]
      have h2 : q.take (p.length + 1) = p ++ [b] := by simpa using hqp.2
      rw [← h1, h2, List.take_left]
    exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hqT, decide_eq_true ⟨by omega, htake⟩⟩⟩
  have hdisj : Disjoint (subT T (p ++ [false])) (subT T (p ++ [true])) := by
    rw [Finset.disjoint_left]
    intro q h0 h1
    have ht0 : q.take (p.length + 1) = p ++ [false] := by
      simpa using (of_decide_eq_true (Finset.mem_filter.mp h0).2).2
    have ht1 : q.take (p.length + 1) = p ++ [true] := by
      simpa using (of_decide_eq_true (Finset.mem_filter.mp h1).2).2
    have heq : p ++ [false] = p ++ [true] := ht0.symm.trans ht1
    have hlast := List.append_cancel_left heq
    exact Bool.false_ne_true (List.cons.inj hlast).1
  have hunion : subT T (p ++ [false]) ∪ subT T (p ++ [true]) ⊆ (subT T p).erase p :=
    Finset.union_subset (hsub_b false) (hsub_b true)
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hp_mem] at hcard
  have hpos : 1 ≤ (subT T p).card := Finset.card_pos.mpr ⟨p, hp_mem⟩
  omega

private lemma tree_aff_bound {k m : Nat}
    (pinKey : Finset (Fin k)) (refBits : Fin k → Bool)
    (tKey : Fin m × Fin 3 ↪ Fin k) (htFree : ∀ p, tKey p ∉ pinKey)
    (h3m : 3 * m ≤ k - pinKey.card)
    (Q : Fin m → (Fin k → Bool) → Bool) (hQ : ∀ i, quadBits (Q i))
    (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
    (P : List Bool → Fin m → (Fin k → Bool) → Bool) (hP : ∀ p i, quadBits (P p i))
    (e : Nat) :
    let target := fun (w : Fin k → Bool) (i : Fin m) =>
      xor (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) (Q i w)
    let stepRun := fun (w : Fin k → Bool) (p : List Bool) =>
      if p ∈ T then p ++ [linBits (ask p) w] else p
    ∀ (t : Nat) (p : List Bool) (n : Nat) (S : Finset (Fin k))
      (_hS : S ⊆ Finset.univ \ pinKey) (b0 : Fin k → Bool) (coeff : Fin k → Fin k → Bool),
      (subT T p).card = t →
      ∃ cnt : Nat → Nat,
        (∀ j, cnt j ≤ 2 ^ j) ∧
        (∑ j ∈ Finset.range (t + 1), cnt j) ≤ t ∧
        (((Finset.univ : Finset (Fin k → Bool)).filter
          (fun w => inAff pinKey S refBits b0 coeff w = true)).filter
          (fun w => ((Finset.univ : Finset (Fin m)).filter
            (fun i => P (runIter (stepRun w) n p) i w != target w i)).card ≤ e)).card ≤
        B_fn (k - pinKey.card) m S.card e +
          ∑ j ∈ Finset.range (t + 1), cnt j * delta_fn (k - pinKey.card) m e (S.card + j) := by
  intro target stepRun t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro p n S hS b0 coeff ht
    let A := (Finset.univ : Finset (Fin k → Bool)).filter
      (fun w => inAff pinKey S refBits b0 coeff w = true)
    have hbase : (∀ w ∈ A, runIter (stepRun w) n p = p) →
        ∃ cnt : Nat → Nat,
          (∀ j, cnt j ≤ 2 ^ j) ∧
          (∑ j ∈ Finset.range (t + 1), cnt j) ≤ t ∧
          (A.filter (fun w => ((Finset.univ : Finset (Fin m)).filter
            (fun i => P (runIter (stepRun w) n p) i w != target w i)).card ≤ e)).card ≤
          B_fn (k - pinKey.card) m S.card e +
            ∑ j ∈ Finset.range (t + 1), cnt j * delta_fn (k - pinKey.card) m e (S.card + j) := by
      intro hfix
      refine ⟨fun _ => 0, fun _ => Nat.zero_le _, by simp, ?_⟩
      simp only [Nat.zero_mul, Finset.sum_const_zero, Nat.add_zero]
      have hfeq : A.filter (fun w => ((Finset.univ : Finset (Fin m)).filter
            (fun i => P (runIter (stepRun w) n p) i w != target w i)).card ≤ e) =
          A.filter (fun w => ((Finset.univ : Finset (Fin m)).filter
            (fun i => P p i w != target w i)).card ≤ e) := by
        ext w
        simp only [Finset.mem_filter]
        exact ⟨fun ⟨hwA, h⟩ => ⟨hwA, by rwa [hfix w hwA] at h⟩,
               fun ⟨hwA, h⟩ => ⟨hwA, by rwa [hfix w hwA]⟩⟩
      rw [hfeq]
      exact score_aff_le_B pinKey S hS refBits b0 coeff tKey htFree Q hQ (P p) (hP p) e
    cases n with
    | zero => exact hbase fun _ _ => rfl
    | succ n =>
      by_cases hpT : p ∈ T
      · have hsplitT := subT_split_card hpT
        rw [ht] at hsplitT
        set t0 := (subT T (p ++ [false])).card
        set t1 := (subT T (p ++ [true])).card
        have ht0_lt : t0 < t := by omega
        have ht1_lt : t1 < t := by omega
        have hstep_run : ∀ w, runIter (stepRun w) (n + 1) p =
            runIter (stepRun w) n (p ++ [linBits (ask p) w]) := by
          intro w
          simp only [runIter, stepRun, hpT, ↓reduceIte]
        rcases splitAff pinKey S hS refBits b0 coeff (ask p) with ⟨c, hc⟩ | ⟨v0, hv0, hsplit⟩
        · have hsub_eq : A.filter (fun w => ((Finset.univ : Finset (Fin m)).filter
              (fun i => P (runIter (stepRun w) (n + 1) p) i w != target w i)).card ≤ e) =
            A.filter (fun w => ((Finset.univ : Finset (Fin m)).filter
              (fun i => P (runIter (stepRun w) n (p ++ [c])) i w != target w i)).card ≤ e) := by
            ext w
            simp only [Finset.mem_filter]
            refine ⟨fun ⟨hwA, h⟩ => ⟨hwA, ?_⟩, fun ⟨hwA, h⟩ => ⟨hwA, ?_⟩⟩
            · rwa [hstep_run w, hc w (Finset.mem_filter.mp hwA).2] at h
            · rwa [hstep_run w, hc w (Finset.mem_filter.mp hwA).2]
          set tc := (subT T (p ++ [c])).card
          have htc_lt : tc < t := by cases c <;> omega
          obtain ⟨cntC, hcapC, hsumC, hleC⟩ := ih tc htc_lt (p ++ [c]) n S hS b0 coeff rfl
          let cnt : Nat → Nat := fun j => if j ≤ tc then cntC j else 0
          refine ⟨cnt, fun j => by dsimp only [cnt]; split_ifs; exact hcapC j; exact Nat.zero_le _, ?_, ?_⟩
          · have hsplit_sum : (∑ j ∈ Finset.range (t + 1), cnt j) =
                ∑ j ∈ Finset.range (tc + 1), cntC j := by
              rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (t + 1)) (fun j => j ≤ tc)]
              have hf : (Finset.range (t + 1)).filter (fun j => j ≤ tc) = Finset.range (tc + 1) := by
                ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
              have h1 : (∑ j ∈ Finset.range (tc + 1), cnt j) = ∑ j ∈ Finset.range (tc + 1), cntC j :=
                Finset.sum_congr rfl fun j hj => by simp [cnt, show j ≤ tc by have := Finset.mem_range.mp hj; omega]
              have h2 : (∑ j ∈ (Finset.range (t + 1)).filter (fun j => ¬ j ≤ tc), cnt j) = 0 :=
                Finset.sum_eq_zero fun j hj => by simp [cnt, (Finset.mem_filter.mp hj).2]
              rw [hf, h1, h2, Nat.add_zero]
            rw [hsplit_sum]
            omega
          · have hsplit_obj : (∑ j ∈ Finset.range (t + 1), cnt j * delta_fn (k - pinKey.card) m e (S.card + j)) =
                ∑ j ∈ Finset.range (tc + 1), cntC j * delta_fn (k - pinKey.card) m e (S.card + j) := by
              rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (t + 1)) (fun j => j ≤ tc)]
              have hf : (Finset.range (t + 1)).filter (fun j => j ≤ tc) = Finset.range (tc + 1) := by
                ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
              have h1 : (∑ j ∈ Finset.range (tc + 1), cnt j * delta_fn (k - pinKey.card) m e (S.card + j)) =
                  ∑ j ∈ Finset.range (tc + 1), cntC j * delta_fn (k - pinKey.card) m e (S.card + j) :=
                Finset.sum_congr rfl fun j hj => by simp [cnt, show j ≤ tc by have := Finset.mem_range.mp hj; omega]
              have h2 : (∑ j ∈ (Finset.range (t + 1)).filter (fun j => ¬ j ≤ tc),
                  cnt j * delta_fn (k - pinKey.card) m e (S.card + j)) = 0 :=
                Finset.sum_eq_zero fun j hj => by simp [cnt, (Finset.mem_filter.mp hj).2]
              rw [hf, h1, h2, Nat.add_zero]
            rw [hsub_eq, hsplit_obj]
            exact hleC
        · obtain ⟨b0_0, coeff_0, hiff0⟩ := hsplit false
          obtain ⟨b0_1, coeff_1, hiff1⟩ := hsplit true
          have hv0F : v0 ∈ Finset.univ \ pinKey := (Finset.mem_sdiff.mp hv0).1
          have hv0notS : v0 ∉ S := (Finset.mem_sdiff.mp hv0).2
          have hS' : insert v0 S ⊆ Finset.univ \ pinKey := Finset.insert_subset_iff.mpr ⟨hv0F, hS⟩
          have hS'card : (insert v0 S).card = S.card + 1 := Finset.card_insert_of_notMem hv0notS
          have hSlt : S.card < k - pinKey.card := by
            have hle := Finset.card_le_card hS'
            rw [hS'card, Finset.card_sdiff_of_subset (Finset.subset_univ pinKey),
              Finset.card_univ, Fintype.card_fin] at hle
            omega
          obtain ⟨cnt0, hcap0, hsum0, hle0⟩ :=
            ih t0 ht0_lt (p ++ [false]) n (insert v0 S) hS' b0_0 coeff_0 rfl
          obtain ⟨cnt1, hcap1, hsum1, hle1⟩ :=
            ih t1 ht1_lt (p ++ [true]) n (insert v0 S) hS' b0_1 coeff_1 rfl
          rw [hS'card] at hle0 hle1
          let c0' : Nat → Nat := fun j => if j ≤ t0 then cnt0 j else 0
          let c1' : Nat → Nat := fun j => if j ≤ t1 then cnt1 j else 0
          let cnt : Nat → Nat := fun j =>
            match j with
            | 0 => 1
            | j + 1 => c0' j + c1' j
          have hsum_c0 : (∑ j ∈ Finset.range t, c0' j) = ∑ j ∈ Finset.range (t0 + 1), cnt0 j := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range t) (fun j => j ≤ t0)]
            have hf : (Finset.range t).filter (fun j => j ≤ t0) = Finset.range (t0 + 1) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
            have h1 : (∑ j ∈ Finset.range (t0 + 1), c0' j) = ∑ j ∈ Finset.range (t0 + 1), cnt0 j :=
              Finset.sum_congr rfl fun j hj => by simp [c0', show j ≤ t0 by have := Finset.mem_range.mp hj; omega]
            have h2 : (∑ j ∈ (Finset.range t).filter (fun j => ¬ j ≤ t0), c0' j) = 0 :=
              Finset.sum_eq_zero fun j hj => by simp [c0', (Finset.mem_filter.mp hj).2]
            rw [hf, h1, h2, Nat.add_zero]
          have hsum_c1 : (∑ j ∈ Finset.range t, c1' j) = ∑ j ∈ Finset.range (t1 + 1), cnt1 j := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range t) (fun j => j ≤ t1)]
            have hf : (Finset.range t).filter (fun j => j ≤ t1) = Finset.range (t1 + 1) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
            have h1 : (∑ j ∈ Finset.range (t1 + 1), c1' j) = ∑ j ∈ Finset.range (t1 + 1), cnt1 j :=
              Finset.sum_congr rfl fun j hj => by simp [c1', show j ≤ t1 by have := Finset.mem_range.mp hj; omega]
            have h2 : (∑ j ∈ (Finset.range t).filter (fun j => ¬ j ≤ t1), c1' j) = 0 :=
              Finset.sum_eq_zero fun j hj => by simp [c1', (Finset.mem_filter.mp hj).2]
            rw [hf, h1, h2, Nat.add_zero]
          have hobj_c0 : (∑ j ∈ Finset.range t, c0' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) =
              ∑ j ∈ Finset.range (t0 + 1), cnt0 j * delta_fn (k - pinKey.card) m e (S.card + 1 + j) := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range t) (fun j => j ≤ t0)]
            have hf : (Finset.range t).filter (fun j => j ≤ t0) = Finset.range (t0 + 1) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
            have h1 : (∑ j ∈ Finset.range (t0 + 1), c0' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) =
                ∑ j ∈ Finset.range (t0 + 1), cnt0 j * delta_fn (k - pinKey.card) m e (S.card + 1 + j) :=
              Finset.sum_congr rfl fun j hj => by simp [c0', show j ≤ t0 by have := Finset.mem_range.mp hj; omega]
            have h2 : (∑ j ∈ (Finset.range t).filter (fun j => ¬ j ≤ t0),
                c0' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) = 0 :=
              Finset.sum_eq_zero fun j hj => by simp [c0', (Finset.mem_filter.mp hj).2]
            rw [hf, h1, h2, Nat.add_zero]
          have hobj_c1 : (∑ j ∈ Finset.range t, c1' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) =
              ∑ j ∈ Finset.range (t1 + 1), cnt1 j * delta_fn (k - pinKey.card) m e (S.card + 1 + j) := by
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.range t) (fun j => j ≤ t1)]
            have hf : (Finset.range t).filter (fun j => j ≤ t1) = Finset.range (t1 + 1) := by
              ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
            have h1 : (∑ j ∈ Finset.range (t1 + 1), c1' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) =
                ∑ j ∈ Finset.range (t1 + 1), cnt1 j * delta_fn (k - pinKey.card) m e (S.card + 1 + j) :=
              Finset.sum_congr rfl fun j hj => by simp [c1', show j ≤ t1 by have := Finset.mem_range.mp hj; omega]
            have h2 : (∑ j ∈ (Finset.range t).filter (fun j => ¬ j ≤ t1),
                c1' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) = 0 :=
              Finset.sum_eq_zero fun j hj => by simp [c1', (Finset.mem_filter.mp hj).2]
            rw [hf, h1, h2, Nat.add_zero]
          refine ⟨cnt, ?_, ?_, ?_⟩
          · intro j
            cases j with
            | zero => simp [cnt]
            | succ j =>
              simp only [cnt, Nat.pow_succ]
              have h0 : c0' j ≤ 2 ^ j := by dsimp only [c0']; split_ifs; exact hcap0 j; exact Nat.zero_le _
              have h1 : c1' j ≤ 2 ^ j := by dsimp only [c1']; split_ifs; exact hcap1 j; exact Nat.zero_le _
              omega
          · rw [Finset.sum_range_succ']
            simp only [cnt, Finset.sum_add_distrib, hsum_c0, hsum_c1]
            omega
          · let G_all := A.filter (fun w => ((Finset.univ : Finset (Fin m)).filter
              (fun i => P (runIter (stepRun w) (n + 1) p) i w != target w i)).card ≤ e)
            have hpartA : G_all.card =
                (G_all.filter (fun w => linBits (ask p) w = false)).card +
                (G_all.filter (fun w => linBits (ask p) w = true)).card := by
              have h := card_filter_add_not G_all (fun w => linBits (ask p) w = false)
              rw [← h]
              congr 1
              apply congrArg Finset.card
              ext w
              simp only [Finset.mem_filter]
              cases linBits (ask p) w <;> simp
            have hG0 : G_all.filter (fun w => linBits (ask p) w = false) =
                ((Finset.univ : Finset (Fin k → Bool)).filter
                  (fun w => inAff pinKey (insert v0 S) refBits b0_0 coeff_0 w = true)).filter
                  (fun w => ((Finset.univ : Finset (Fin m)).filter
                    (fun i => P (runIter (stepRun w) n (p ++ [false])) i w != target w i)).card ≤ e) := by
              ext w
              simp only [G_all, A, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨⟨hwA, herr⟩, hlin⟩
                refine ⟨(hiff0 w).mp ⟨hwA, hlin⟩, ?_⟩
                rwa [hstep_run w, hlin] at herr
              · rintro ⟨hwA', herr⟩
                obtain ⟨hwA, hlin⟩ := (hiff0 w).mpr hwA'
                refine ⟨⟨hwA, ?_⟩, hlin⟩
                rwa [hstep_run w, hlin]
            have hG1 : G_all.filter (fun w => linBits (ask p) w = true) =
                ((Finset.univ : Finset (Fin k → Bool)).filter
                  (fun w => inAff pinKey (insert v0 S) refBits b0_1 coeff_1 w = true)).filter
                  (fun w => ((Finset.univ : Finset (Fin m)).filter
                    (fun i => P (runIter (stepRun w) n (p ++ [true])) i w != target w i)).card ≤ e) := by
              ext w
              simp only [G_all, A, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨⟨hwA, herr⟩, hlin⟩
                refine ⟨(hiff1 w).mp ⟨hwA, hlin⟩, ?_⟩
                rwa [hstep_run w, hlin] at herr
              · rintro ⟨hwA', herr⟩
                obtain ⟨hwA, hlin⟩ := (hiff1 w).mpr hwA'
                refine ⟨⟨hwA, ?_⟩, hlin⟩
                rwa [hstep_run w, hlin]
            rw [hpartA, hG0, hG1]
            have hsum_rhs : (∑ j ∈ Finset.range (t + 1),
                cnt j * delta_fn (k - pinKey.card) m e (S.card + j)) =
                delta_fn (k - pinKey.card) m e S.card +
                (∑ j ∈ Finset.range (t0 + 1), cnt0 j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) +
                (∑ j ∈ Finset.range (t1 + 1), cnt1 j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) := by
              rw [Finset.sum_range_succ']
              simp only [cnt, Nat.add_zero, Nat.one_mul]
              have hshift : (∑ j ∈ Finset.range t, (c0' j + c1' j) *
                  delta_fn (k - pinKey.card) m e (S.card + (j + 1))) =
                  (∑ j ∈ Finset.range t, c0' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) +
                  (∑ j ∈ Finset.range t, c1' j * delta_fn (k - pinKey.card) m e (S.card + 1 + j)) := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun j _ => ?_
                have ha : S.card + (j + 1) = S.card + 1 + j := by omega
                rw [ha, Nat.add_mul]
              rw [hshift, hobj_c0, hobj_c1]
              omega
            rw [hsum_rhs, ← Nat.add_assoc, ← Nat.add_assoc, ← two_mul_B_succ h3m hSlt]
            have hadd := Nat.add_le_add hle0 hle1
            omega
      · exact hbase fun w _ => runIter_fixed (by simp [stepRun, hpT]) (n + 1)

private def bitsVal : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

private def listOfNat : Nat → Nat → List Bool
  | 0, _ => []
  | len + 1, n => (n % 2 == 1) :: listOfNat len (n / 2)

private lemma length_listOfNat (len n : Nat) : (listOfNat len n).length = len := by
  induction len generalizing n with
  | zero => rfl
  | succ len ih => simp [listOfNat, ih]

private lemma bitsVal_listOfNat : ∀ len n, n < 2 ^ len → bitsVal (listOfNat len n) = n
  | 0, n, hn => by simp [listOfNat, bitsVal]; omega
  | len + 1, n, hn => by
    simp only [listOfNat, bitsVal]
    have hlt : n / 2 < 2 ^ len := by
      have : 2 ^ (len + 1) = 2 ^ len * 2 := Nat.pow_succ 2 len
      omega
    rw [bitsVal_listOfNat len (n / 2) hlt]
    have hbit : (n % 2 == 1).toNat = n % 2 := by
      by_cases h : n % 2 = 0
      · simp [h]
      · have h1 : n % 2 = 1 := by omega
        simp [h1]
    rw [hbit]
    omega

private lemma bitsVal_lt_pow : ∀ l : List Bool, bitsVal l < 2 ^ l.length
  | [] => by simp [bitsVal]
  | b :: bs => by
    simp only [bitsVal, List.length_cons, Nat.pow_succ]
    have ih := bitsVal_lt_pow bs
    cases b <;> simp <;> omega

private lemma listOfNat_bitsVal : ∀ l : List Bool, listOfNat l.length (bitsVal l) = l
  | [] => rfl
  | b :: bs => by
    simp only [List.length_cons, bitsVal, listOfNat]
    have hmod : ((b.toNat + 2 * bitsVal bs) % 2 == 1) = b := by
      cases b <;> simp
    have hdiv : (b.toNat + 2 * bitsVal bs) / 2 = bitsVal bs := by
      cases b
      · simp
      · simp; omega
    rw [hmod, hdiv, listOfNat_bitsVal bs]

private def allLists (len : Nat) : Finset (List Bool) :=
  (Finset.range (2 ^ len)).image (listOfNat len)

private lemma card_allLists (len : Nat) : (allLists len).card = 2 ^ len := by
  unfold allLists
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb heq
  have ha' : a < 2 ^ len := Finset.mem_range.mp ha
  have hb' : b < 2 ^ len := Finset.mem_range.mp hb
  have h := congrArg bitsVal heq
  rwa [bitsVal_listOfNat len a ha', bitsVal_listOfNat len b hb'] at h

private lemma mem_allLists {len : Nat} {l : List Bool} :
    l ∈ allLists len ↔ l.length = len := by
  unfold allLists
  rw [Finset.mem_image]
  constructor
  · rintro ⟨n, _, rfl⟩
    exact length_listOfNat len n
  · intro hlen
    refine ⟨bitsVal l, Finset.mem_range.mpr (hlen ▸ bitsVal_lt_pow l), ?_⟩
    rw [← hlen, listOfNat_bitsVal]

private def optTree (d a : Nat) : Finset (List Bool) :=
  ((Finset.range d).biUnion allLists) ∪ ((Finset.range a).image (listOfNat d))

private lemma mem_optTree {d a : Nat} (ha : a < 2 ^ d) {l : List Bool} :
    l ∈ optTree d a ↔ l.length < d ∨ (l.length = d ∧ bitsVal l < a) := by
  unfold optTree
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro (⟨j, hj, hjl⟩ | ⟨n, hn, rfl⟩)
    · left
      rw [mem_allLists] at hjl
      rw [hjl]
      exact Finset.mem_range.mp hj
    · right
      have hn' : n < a := Finset.mem_range.mp hn
      exact ⟨length_listOfNat d n, by rw [bitsVal_listOfNat d n (by omega)]; exact hn'⟩
  · rintro (hlt | ⟨hlen, hval⟩)
    · left
      exact ⟨l.length, Finset.mem_range.mpr hlt, mem_allLists.mpr rfl⟩
    · right
      refine ⟨bitsVal l, Finset.mem_range.mpr hval, ?_⟩
      rw [← hlen, listOfNat_bitsVal]

private lemma card_optTree {d a : Nat} (ha : a < 2 ^ d) :
    (optTree d a).card = 2 ^ d - 1 + a := by
  unfold optTree
  have hdisj_bi : Set.PairwiseDisjoint (↑(Finset.range d) : Set Nat) allLists := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro l hi hj
    rw [mem_allLists] at hi hj
    exact hij (hi.symm.trans hj)
  have hdisj_u : Disjoint ((Finset.range d).biUnion allLists) ((Finset.range a).image (listOfNat d)) := by
    rw [Finset.disjoint_left]
    intro l h1 h2
    rcases Finset.mem_biUnion.mp h1 with ⟨j, hj, hjl⟩
    rcases Finset.mem_image.mp h2 with ⟨n, _, rfl⟩
    rw [mem_allLists, length_listOfNat] at hjl
    have hj' : j < d := Finset.mem_range.mp hj
    omega
  have hcard1 : ((Finset.range d).biUnion allLists).card = 2 ^ d - 1 := by
    rw [Finset.card_biUnion hdisj_bi]
    calc ∑ j ∈ Finset.range d, (allLists j).card
        = ∑ j ∈ Finset.range d, 2 ^ j := Finset.sum_congr rfl fun j _ => card_allLists j
      _ = 2 ^ d - 1 := sum_pow_two_range d
  have hcard2 : ((Finset.range a).image (listOfNat d)).card = a := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro x hx y hy heq
    have hx' : x < 2 ^ d := (Finset.mem_range.mp hx).trans ha
    have hy' : y < 2 ^ d := (Finset.mem_range.mp hy).trans ha
    have h := congrArg bitsVal heq
    rwa [bitsVal_listOfNat d x hx', bitsVal_listOfNat d y hy'] at h
  rw [Finset.card_union_of_disjoint hdisj_u, hcard1, hcard2]

private def prefBits {k m : Nat} (tKey : Fin m × Fin 3 ↪ Fin k) (w : Fin k → Bool) (len : Nat) : List Bool :=
  List.ofFn fun t : Fin len => if h : t.val < m then w (tKey (⟨t.val, h⟩, 0)) else false

private lemma prefBits_length {k m : Nat} (tKey : Fin m × Fin 3 ↪ Fin k) (w : Fin k → Bool) (len : Nat) :
    (prefBits tKey w len).length = len := List.length_ofFn

private lemma prefBits_succ {k m : Nat} (tKey : Fin m × Fin 3 ↪ Fin k) (w : Fin k → Bool) (len : Nat) :
    prefBits tKey w (len + 1) =
      prefBits tKey w len ++ [if h : len < m then w (tKey (⟨len, h⟩, 0)) else false] := by
  apply List.ext_getElem
  · simp [prefBits_length]
  · intro i h1 h2
    simp only [prefBits, List.getElem_ofFn, List.getElem_append, List.length_ofFn]
    by_cases hi : i < len
    · simp [hi]
    · have hieq : i = len := by simp [prefBits_length] at h1; omega
      subst hieq
      simp

private def optAsk {k m : Nat} (tKey : Fin m × Fin 3 ↪ Fin k) (p : List Bool) (j : Fin k) : Bool :=
  if h : p.length < m then decide (j = tKey (⟨p.length, h⟩, 0)) else false

private lemma linBits_optAsk {k m : Nat} (tKey : Fin m × Fin 3 ↪ Fin k) (p : List Bool)
    (hp : p.length < m) (w : Fin k → Bool) :
    linBits (optAsk tKey p) w = w (tKey (⟨p.length, hp⟩, 0)) := by
  apply z2_inj
  rw [z2_linBits]
  let v0 := tKey (⟨p.length, hp⟩, 0)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v0)]
  have hv0 : z2 (optAsk tKey p v0) * z2 (w v0) = z2 (w v0) := by
    simp [optAsk, hp, v0, z2]
  have hrest : (∑ i ∈ Finset.univ.erase v0, z2 (optAsk tKey p i) * z2 (w i)) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have hne : i ≠ v0 := Finset.ne_of_mem_erase hi
      simp [optAsk, hp, v0, hne, z2]
  rw [hv0, hrest, add_zero]

private lemma card_optAsk_le_one {k m : Nat} (tKey : Fin m × Fin 3 ↪ Fin k) (p : List Bool) :
    ((Finset.univ : Finset (Fin k)).filter (fun j => optAsk tKey p j = true)).card ≤ 1 := by
  by_cases hp : p.length < m
  · have hfilt : (Finset.univ : Finset (Fin k)).filter (fun j => optAsk tKey p j = true) =
        {tKey (⟨p.length, hp⟩, 0)} := by
      ext j
      simp [optAsk, hp]
    rw [hfilt, Finset.card_singleton]
  · have hfilt : (Finset.univ : Finset (Fin k)).filter (fun j => optAsk tKey p j = true) = ∅ := by
      ext j
      simp [optAsk, hp]
    rw [hfilt, Finset.card_empty]
    exact Nat.zero_le 1

private lemma run_optTree {k m d a : Nat} (tKey : Fin m × Fin 3 ↪ Fin k)
    (hd : d ≤ m) (ha : a < 2 ^ d) (hdm : 0 < a → d < m) (w : Fin k → Bool) :
    let stepRun := fun (p : List Bool) =>
      if p ∈ optTree d a then p ++ [linBits (optAsk tKey p) w] else p
    runIter stepRun (optTree d a).card [] =
      if bitsVal (prefBits tKey w d) < a then prefBits tKey w (d + 1) else prefBits tKey w d := by
  intro stepRun
  have hrun_pref : ∀ t ≤ d, ∀ n, t ≤ n →
      runIter stepRun n [] = runIter stepRun (n - t) (prefBits tKey w t) := by
    intro t
    induction t with
    | zero => intro _ n _; rfl
    | succ t ih =>
      intro ht n hn
      have h1 := ih (by omega) n (by omega)
      rw [h1]
      have hsub : n - t = (n - (t + 1)) + 1 := by omega
      rw [hsub]
      simp only [runIter, stepRun]
      have hmem : prefBits tKey w t ∈ optTree d a := by
        rw [mem_optTree ha]
        left
        rw [prefBits_length]
        omega
      have htm : t < m := by omega
      have hlen : (prefBits tKey w t).length < m := by rw [prefBits_length]; exact htm
      have hlin : linBits (optAsk tKey (prefBits tKey w t)) w = w (tKey (⟨t, htm⟩, 0)) := by
        rw [linBits_optAsk tKey (prefBits tKey w t) hlen w]
        congr 1
        congr 1
        exact Prod.ext (Fin.ext (prefBits_length tKey w t)) rfl
      simp only [hmem, ↓reduceIte, hlin]
      have hps : prefBits tKey w t ++ [w (tKey (⟨t, htm⟩, 0))] = prefBits tKey w (t + 1) := by
        rw [prefBits_succ]; simp [htm]
      rw [hps]
  have h2d_ge_all : ∀ n : Nat, n + 1 ≤ 2 ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.pow_succ]
      omega
  have h2d_ge : d + 1 ≤ 2 ^ d := h2d_ge_all d
  have hcard_ge : d ≤ (optTree d a).card := by
    rw [card_optTree ha]
    omega
  rw [hrun_pref d le_rfl (optTree d a).card hcard_ge]
  by_cases hlt : bitsVal (prefBits tKey w d) < a
  · rw [ite_t hlt]
    have ha_pos : 0 < a := by omega
    have hdm' : d < m := hdm ha_pos
    have hcard_ge1 : d + 1 ≤ (optTree d a).card := by
      rw [card_optTree ha]
      omega
    have hsub1 : (optTree d a).card - d = ((optTree d a).card - (d + 1)) + 1 := by omega
    rw [hsub1]
    simp only [runIter, stepRun]
    have hmem : prefBits tKey w d ∈ optTree d a := by
      rw [mem_optTree ha]
      right
      exact ⟨prefBits_length tKey w d, hlt⟩
    have hlen : (prefBits tKey w d).length < m := by rw [prefBits_length]; exact hdm'
    have hlin : linBits (optAsk tKey (prefBits tKey w d)) w = w (tKey (⟨d, hdm'⟩, 0)) := by
      rw [linBits_optAsk tKey (prefBits tKey w d) hlen w]
      congr 1
      congr 1
      exact Prod.ext (Fin.ext (prefBits_length tKey w d)) rfl
    simp only [hmem, ↓reduceIte, hlin]
    have hps : prefBits tKey w d ++ [w (tKey (⟨d, hdm'⟩, 0))] = prefBits tKey w (d + 1) := by
      rw [prefBits_succ]; simp [hdm']
    rw [hps]
    have hnotmem : prefBits tKey w (d + 1) ∉ optTree d a := by
      rw [mem_optTree ha, prefBits_length]
      omega
    exact runIter_fixed (by simp only [stepRun, hnotmem, ↓reduceIte]) _
  · rw [ite_f hlt]
    have hnotmem : prefBits tKey w d ∉ optTree d a := by
      rw [mem_optTree ha, prefBits_length]
      omega
    exact runIter_fixed (by simp only [stepRun, hnotmem, ↓reduceIte]) _

private lemma card_fiber_prefix_tail {k m : Nat}
    (pinKey : Finset (Fin k)) (refBits : Fin k → Bool)
    (tKey : Fin m × Fin 3 ↪ Fin k) (htFree : ∀ p, tKey p ∉ pinKey)
    (len : Nat) (hlen : len ≤ m)
    (cond : (Fin len → Bool) → Bool) (e : Nat) :
    ((Finset.univ : Finset (Fin k → Bool)).filter (fun w =>
      (∀ z ∈ pinKey, w z = refBits z) ∧
      cond (fun t : Fin len => w (tKey (⟨t.val, lt_of_lt_of_le t.isLt hlen⟩, 0))) = true ∧
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        len ≤ i.val ∧ (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true)).card ≤ e)).card =
    ((Finset.univ : Finset (Fin len → Bool)).filter (fun u => cond u = true)).card *
      B_fn (k - pinKey.card) m len e := by
  let r := m - len
  let p0Idx : Fin len ↪ Fin k :=
    ⟨fun t => tKey (⟨t.val, lt_of_lt_of_le t.isLt hlen⟩, 0),
     fun t1 t2 h => Fin.ext (Fin.mk.inj (Prod.mk.inj (tKey.injective h)).1)⟩
  let tailIdx : Fin r × Fin 3 ↪ Fin k :=
    ⟨fun p => tKey (⟨len + p.1.val, by omega⟩, p.2),
     fun p1 p2 h => by
       have h12 := Prod.mk.inj (tKey.injective h)
       have hfst : len + p1.1.val = len + p2.1.val := congrArg Fin.val h12.1
       exact Prod.ext (Fin.ext (by omega)) h12.2⟩
  let P0 : Finset (Fin k) := Finset.univ.image p0Idx
  let Tail : Finset (Fin k) := Finset.univ.image tailIdx
  let Used : Finset (Fin k) := pinKey ∪ P0 ∪ Tail
  let Rest : Finset (Fin k) := Finset.univ \ Used
  have hd_pP0 : Disjoint pinKey P0 := by
    rw [Finset.disjoint_left]
    intro z hzp hzP0
    rcases Finset.mem_image.mp hzP0 with ⟨t, _, rfl⟩
    exact htFree _ hzp
  have hd_pT : Disjoint pinKey Tail := by
    rw [Finset.disjoint_left]
    intro z hzp hzT
    rcases Finset.mem_image.mp hzT with ⟨p, _, rfl⟩
    exact htFree _ hzp
  have hd_P0T : Disjoint P0 Tail := by
    rw [Finset.disjoint_left]
    intro z hzP0 hzT
    rcases Finset.mem_image.mp hzP0 with ⟨t, _, rfl⟩
    rcases Finset.mem_image.mp hzT with ⟨p, _, hp⟩
    have h12 := Prod.mk.inj (tKey.injective hp)
    have hval : len + p.1.val = t.val := congrArg Fin.val h12.1
    omega
  have hd_uT : Disjoint (pinKey ∪ P0) Tail := Finset.disjoint_union_left.mpr ⟨hd_pT, hd_P0T⟩
  have hP0_card : P0.card = len := by
    rw [Finset.card_image_of_injective _ p0Idx.injective, Finset.card_univ, Fintype.card_fin]
  have hTail_card : Tail.card = 3 * r := by
    rw [Finset.card_image_of_injective _ tailIdx.injective, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega
  have hUsed_card : Used.card = pinKey.card + len + 3 * r := by
    rw [Finset.card_union_of_disjoint hd_uT, Finset.card_union_of_disjoint hd_pP0, hP0_card, hTail_card]
  have hRest_card : Rest.card = k - pinKey.card - len - 3 * r := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ Used), Finset.card_univ, Fintype.card_fin,
      hUsed_card]
    omega
  let Scond := (Finset.univ : Finset (Fin len → Bool)).filter (fun u => cond u = true)
  let Stail := (Finset.univ : Finset (Fin r × Fin 3 → Bool)).filter (fun y =>
    ((Finset.univ : Finset (Fin r)).filter (fun j => y (j, 0) && y (j, 1) && y (j, 2))).card ≤ e)
  let Srest : Finset ({z : Fin k // z ∈ Rest} → Bool) := Finset.univ
  have hcard_err : ∀ w : Fin k → Bool,
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        len ≤ i.val ∧ (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true)).card =
      ((Finset.univ : Finset (Fin r)).filter (fun j =>
        w (tailIdx (j, 0)) && w (tailIdx (j, 1)) && w (tailIdx (j, 2)))).card := by
    intro w
    symm
    refine Finset.card_nbij (fun j : Fin r => (⟨len + j.val, by dsimp only [r]; omega⟩ : Fin m)) ?_ ?_ ?_
    · intro j hj
      have h1 : (w (tailIdx (j, 0)) && w (tailIdx (j, 1)) && w (tailIdx (j, 2))) = true :=
        (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.le_add_right len j.val, ?_⟩
      exact h1
    · intro j1 _ j2 _ heq
      have hv : len + j1.val = len + j2.val := Fin.mk.inj heq
      exact Fin.ext (by omega)
    · intro i hi
      have h1 := (Finset.mem_filter.mp hi).2
      have hle : len ≤ i.val := h1.1
      have hlt : i.val - len < r := by dsimp only [r]; omega
      refine ⟨⟨i.val - len, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Fin.ext (by dsimp only; omega)⟩
      have heq : (⟨len + (i.val - len), by omega⟩ : Fin m) = i := Fin.ext (by dsimp only; omega)
      change (w (tKey (⟨len + (i.val - len), _⟩, 0)) &&
        w (tKey (⟨len + (i.val - len), _⟩, 1)) &&
        w (tKey (⟨len + (i.val - len), _⟩, 2))) = true
      rw [heq]
      exact h1.2
  let splitFn : (Fin k → Bool) → (Fin len → Bool) × ((Fin r × Fin 3 → Bool) × ({z : Fin k // z ∈ Rest} → Bool)) :=
    fun w => (fun t => w (p0Idx t), (fun p => w (tailIdx p), fun z => w z.val))
  let joinFn : (Fin len → Bool) × ((Fin r × Fin 3 → Bool) × ({z : Fin k // z ∈ Rest} → Bool)) → (Fin k → Bool) :=
    fun trip z =>
      if z ∈ pinKey then refBits z
      else if h1 : ∃ t, p0Idx t = z then trip.1 (Classical.choose h1)
      else if h2 : ∃ p, tailIdx p = z then trip.2.1 (Classical.choose h2)
      else if h3 : z ∈ Rest then trip.2.2 ⟨z, h3⟩
      else false
  have hbij : ((Finset.univ : Finset (Fin k → Bool)).filter (fun w =>
      (∀ z ∈ pinKey, w z = refBits z) ∧
      cond (fun t : Fin len => w (tKey (⟨t.val, lt_of_lt_of_le t.isLt hlen⟩, 0))) = true ∧
      ((Finset.univ : Finset (Fin m)).filter (fun i =>
        len ≤ i.val ∧ (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true)).card ≤ e)).card =
      (Scond ×ˢ (Stail ×ˢ Srest)).card := by
    refine Finset.card_nbij splitFn ?_ ?_ ?_
    · intro w hw
      obtain ⟨_, hcond, herr⟩ := (Finset.mem_filter.mp hw).2
      change splitFn w ∈ Scond ×ˢ (Stail ×ˢ Srest)
      rw [Finset.mem_product, Finset.mem_product]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcond⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
      rwa [← hcard_err w]
    · intro w1 hw1 w2 hw2 heq
      have hp1 := (Finset.mem_filter.mp hw1).2.1
      have hp2 := (Finset.mem_filter.mp hw2).2.1
      have h1 : (fun t => w1 (p0Idx t)) = (fun t => w2 (p0Idx t)) := congrArg Prod.fst heq
      have h2 : (fun p => w1 (tailIdx p)) = (fun p => w2 (tailIdx p)) :=
        congrArg (fun x => x.2.1) heq
      have h3 : (fun z : {z : Fin k // z ∈ Rest} => w1 z.val) = (fun z => w2 z.val) :=
        congrArg (fun x => x.2.2) heq
      funext z
      by_cases hzp : z ∈ pinKey
      · rw [hp1 z hzp, hp2 z hzp]
      · by_cases hzP0 : z ∈ P0
        · rcases Finset.mem_image.mp hzP0 with ⟨t, _, rfl⟩
          exact congrFun h1 t
        · by_cases hzT : z ∈ Tail
          · rcases Finset.mem_image.mp hzT with ⟨p, _, rfl⟩
            exact congrFun h2 p
          · have hzR : z ∈ Rest := by
              refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, ?_⟩
              simp [Used, hzp, hzP0, hzT]
            exact congrFun h3 ⟨z, hzR⟩
    · intro trip htrip
      change trip ∈ Scond ×ˢ (Stail ×ˢ Srest) at htrip
      rw [Finset.mem_product, Finset.mem_product] at htrip
      rcases htrip with ⟨hcond, htail, _⟩
      have hjoin_pin : ∀ z ∈ pinKey, joinFn trip z = refBits z := fun z hz => by
        simp [joinFn, hz]
      have hjoin_p0 : ∀ t : Fin len, joinFn trip (p0Idx t) = trip.1 t := by
        intro t
        have hnp : p0Idx t ∉ pinKey := htFree _
        have hex : ∃ t', p0Idx t' = p0Idx t := ⟨t, rfl⟩
        simp only [joinFn, hnp, ↓reduceIte, hex, ↓reduceDIte]
        exact congrArg trip.1 (p0Idx.injective (Classical.choose_spec hex))
      have hjoin_tail : ∀ p : Fin r × Fin 3, joinFn trip (tailIdx p) = trip.2.1 p := by
        intro p
        have hnp : tailIdx p ∉ pinKey := htFree _
        have hn1 : ¬ ∃ t, p0Idx t = tailIdx p := fun ⟨t, ht⟩ =>
          Finset.disjoint_left.mp hd_P0T (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)
            (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)
        have hex : ∃ p', tailIdx p' = tailIdx p := ⟨p, rfl⟩
        simp only [joinFn, hnp, ↓reduceIte, hn1, hex, ↓reduceDIte]
        exact congrArg trip.2.1 (tailIdx.injective (Classical.choose_spec hex))
      have hjoin_rest : ∀ z : {z : Fin k // z ∈ Rest}, joinFn trip z.val = trip.2.2 z := by
        intro ⟨z, hz⟩
        have hnu : z ∉ Used := (Finset.mem_sdiff.mp hz).2
        have hnp : z ∉ pinKey := fun h => hnu (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hn1 : ¬ ∃ t, p0Idx t = z := fun ⟨t, ht⟩ =>
          hnu (Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, ht⟩)))
        have hn2 : ¬ ∃ p, tailIdx p = z := fun ⟨p, hp⟩ =>
          hnu (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, hp⟩))
        simp only [joinFn, hnp, ↓reduceIte, hn1, hn2, hz, ↓reduceDIte]
      have hsplit_join : splitFn (joinFn trip) = trip := by
        rcases trip with ⟨u, y, wR⟩
        refine Prod.ext (funext hjoin_p0) (Prod.ext (funext hjoin_tail) (funext hjoin_rest))
      refine ⟨joinFn trip, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjoin_pin, ?_, ?_⟩, hsplit_join⟩
      · have heq : (fun t : Fin len => joinFn trip (p0Idx t)) = trip.1 := funext hjoin_p0
        change cond (fun t : Fin len => joinFn trip (p0Idx t)) = true
        rw [heq]
        exact (Finset.mem_filter.mp hcond).2
      · rw [hcard_err (joinFn trip)]
        have hfeq : (Finset.univ.filter fun j : Fin r =>
            joinFn trip (tailIdx (j, 0)) && joinFn trip (tailIdx (j, 1)) && joinFn trip (tailIdx (j, 2))) =
            (Finset.univ.filter fun j : Fin r =>
              trip.2.1 (j, 0) && trip.2.1 (j, 1) && trip.2.1 (j, 2)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hjoin_tail]
        rw [hfeq]
        exact (Finset.mem_filter.mp htail).2
  rw [hbij, Finset.card_product, Finset.card_product, card_triple_bad_le r e]
  have hSrest_card : Srest.card = 2 ^ (k - pinKey.card - len - 3 * r) := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hRest_card]
  rw [hSrest_card, Nat.mul_comm _ (2 ^ (k - pinKey.card - len - 3 * r))]
  rfl

private lemma card_fin_bitsVal_lt (d a : Nat) (ha : a ≤ 2 ^ d) :
    ((Finset.univ : Finset (Fin d → Bool)).filter (fun u => bitsVal (List.ofFn u) < a)).card = a := by
  have hbij : ((Finset.univ : Finset (Fin d → Bool)).filter (fun u => bitsVal (List.ofFn u) < a)).card =
      (Finset.range a).card := by
    refine Finset.card_nbij (fun u => bitsVal (List.ofFn u)) ?_ ?_ ?_
    · intro u hu
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hu).2
    · intro u1 _ u2 _ heq
      dsimp only at heq
      have h1 := listOfNat_bitsVal (List.ofFn u1)
      have h2 := listOfNat_bitsVal (List.ofFn u2)
      rw [List.length_ofFn] at h1 h2
      have hlist : List.ofFn u1 = List.ofFn u2 := by
        rw [← h1, ← h2, heq]
      funext i
      have hi := congrArg (fun l : List Bool => l[i.val]?) hlist
      simpa using hi
    · intro n hn
      have hn' : n < a := Finset.mem_range.mp hn
      have hlen : (listOfNat d n).length = d := length_listOfNat d n
      let u : Fin d → Bool := fun i => (listOfNat d n)[i.val]'(by rw [hlen]; exact i.isLt)
      have hofFn : List.ofFn u = listOfNat d n := by
        apply List.ext_getElem
        · simp [hlen]
        · intro i h1 h2
          simp [u]
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [hofFn, bitsVal_listOfNat d n (by omega)]
        exact hn'
      · dsimp only
        rw [hofFn, bitsVal_listOfNat d n (by omega)]
  rw [hbij, Finset.card_range]

private lemma card_fin_bitsVal_ge (d a : Nat) (ha : a ≤ 2 ^ d) :
    ((Finset.univ : Finset (Fin d → Bool)).filter (fun u => a ≤ bitsVal (List.ofFn u))).card =
      2 ^ d - a := by
  have htot := card_filter_add_not (Finset.univ : Finset (Fin d → Bool)) (fun u => bitsVal (List.ofFn u) < a)
  rw [card_fin_bitsVal_lt d a ha, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin] at htot
  have hfilt : (Finset.univ : Finset (Fin d → Bool)).filter (fun u => ¬ bitsVal (List.ofFn u) < a) =
      (Finset.univ : Finset (Fin d → Bool)).filter (fun u => a ≤ bitsVal (List.ofFn u)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [hfilt] at htot
  omega

private lemma card_fin_succ_bitsVal_lt (d a : Nat) (ha : a ≤ 2 ^ d) :
    ((Finset.univ : Finset (Fin (d + 1) → Bool)).filter (fun u =>
      bitsVal (List.ofFn fun t : Fin d => u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) < a)).card =
      2 * a := by
  let S0 := (Finset.univ : Finset (Fin d → Bool)).filter (fun u => bitsVal (List.ofFn u) < a)
  have hbij : ((Finset.univ : Finset (Fin (d + 1) → Bool)).filter (fun u =>
      bitsVal (List.ofFn fun t : Fin d => u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) < a)).card =
      (S0 ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_nbij (fun u => (fun t : Fin d => u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩, u ⟨d, Nat.lt_succ_self d⟩))
      ?_ ?_ ?_
    · intro u hu
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩,
        Finset.mem_univ _⟩
    · intro u1 _ u2 _ heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      funext ⟨i, hi⟩
      by_cases hlt : i < d
      · exact congrFun h1 ⟨i, hlt⟩
      · have hieq : i = d := by omega
        subst hieq
        exact h2
    · intro p hp
      rcases p with ⟨u0, b⟩
      let u : Fin (d + 1) → Bool := fun i => if h : i.val < d then u0 ⟨i.val, h⟩ else b
      have hpre : (fun t : Fin d => u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) = u0 := by
        funext t; simp [u, t.isLt]
      have hlast : u ⟨d, Nat.lt_succ_self d⟩ = b := by simp [u]
      refine ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, Prod.ext hpre hlast⟩
      rw [hpre]
      exact (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
  rw [hbij, Finset.card_product, card_fin_bitsVal_lt d a ha, Finset.card_univ, Fintype.card_bool,
    Nat.mul_comm]

private lemma getElem_ite_list {α : Type*} (c : Prop) [Decidable c] (l1 l2 : List α)
    (i : Nat) (h : i < (if c then l1 else l2).length) :
    (if c then l1 else l2)[i]'h =
      if hc : c then l1[i]'(by simpa [hc] using h) else l2[i]'(by simpa [hc] using h) := by
  by_cases hc : c <;> simp [hc]

private lemma main_proof :
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
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1 + z.2.val) % k) →
  let good := fun (row ref : Fin (2 ^ k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p + j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p + j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p + 6))
    let β := xor τ (injected 1 ref.val (p + 7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2 ^ k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i + j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i + 9 + j.val) % k) →
  ∀ L : Nat, 0 < L →
  let K := Fin (2 ^ k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let lin := fun (mask : Fin k → Bool) (q : K) =>
    par (∑ i : Fin k, (mask i && bitOf q i).toNat)
  let quad := fun (g : K → Bool) => ∃ (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool),
    ∀ q, g q = xor (xor b (lin l q))
      (par (∑ i : Fin k, ∑ j : Fin k, (a i j && bitOf q i && bitOf q j).toNat))
  let fiber := (Finset.univ : Finset K).filter (fun q =>
    ∀ z ∈ pin, bit row.val 0 q.val z.val = bit row.val 0 ref.val z.val)
  let target := fun (x : K) (i : Fin m) => bit row.val 2 x.val (starts i + 5)
  let run := fun (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool) (x : K) =>
    (List.range T.card).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [lin (ask p) x] else p) []
  let score := fun (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
      (P : List Bool → Fin m → K → Bool) (e : Nat) =>
    (fiber.filter (fun x =>
      ((Finset.univ : Finset (Fin m)).filter
        (fun i => P (run T ask x) i x != target x i)).card ≤ e)).card
  let B := fun (p e : Nat) =>
    let r := m - p
    2 ^ (k - pin.card - p - 3 * r) *
      ∑ j ∈ Finset.range (min e r + 1), Nat.choose r j * 7 ^ (r - j)
  let M := min L (2 ^ m)
  let d := Nat.log2 M
  let a := M - 2 ^ d
  let N := fun e : Nat => (2 ^ d - a) * B d e + 2 * a * B (d + 1) e
  (∀ (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
      (P : List Bool → Fin m → K → Bool), T.card < L →
    (∀ p i, quad (P p i)) → ∀ e, score T ask P e ≤ N e) ∧
  ∃ (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
      (P : List Bool → Fin m → K → Bool),
    T.card < L ∧ (∀ p, ((Finset.univ : Finset (Fin k)).filter (fun j => ask p j = true)).card ≤ 1) ∧
    (∀ p i, quad (P p i)) ∧ ∀ e, score T ask P e = N e := by
  intro k hk constant rot0 step0 state0 injected0 bit0 m starts hinj good0 row ref hgood
    pin hpin hfree L hL K bitOf par0 lin0 quad0 fiber target run0 score0 B0 M d a N0
  let rotBack : Fin k → Fin k := fun z => ⟨(z.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩
  have hrotBack_inj : Function.Injective rotBack := by
    intro z1 z2 h
    have hv : (z1.val + k - 1 % k) % k = (z2.val + k - 1 % k) % k := congrArg Fin.val h
    have h1m : 1 % k < k := Nat.mod_lt 1 hk
    apply Fin.ext
    have h1 : (z1.val + k - 1 % k + 1 % k) % k = z1.val := by
      have ha : z1.val + k - 1 % k + 1 % k = z1.val + k := by omega
      rw [ha, Nat.add_mod_right, Nat.mod_eq_of_lt z1.isLt]
    have h2 : (z2.val + k - 1 % k + 1 % k) % k = z2.val := by
      have ha : z2.val + k - 1 % k + 1 % k = z2.val + k := by omega
      rw [ha, Nat.add_mod_right, Nat.mod_eq_of_lt z2.isLt]
    rw [← h1, ← h2, ← Nat.mod_add_mod, hv, Nat.mod_add_mod]
  let pinKey : Finset (Fin k) := pin.image rotBack
  have hpinKey_card : pinKey.card = pin.card := Finset.card_image_of_injective pin hrotBack_inj
  have hfiber_iff : ∀ q : K, q ∈ fiber ↔ ∀ z ∈ pinKey, toBits q z = toBits ref z := by
    intro q
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h w hw
      rcases Finset.mem_image.mp hw with ⟨z, hz, rfl⟩
      have hqz := h z hz
      change (stateAt k constant row.val 0 q.val).testBit (z.val % k) =
        (stateAt k constant row.val 0 ref.val).testBit (z.val % k) at hqz
      rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, stateAt_zero, Nat.testBit_xor, Nat.testBit_xor,
        testBit_rot q.isLt z.isLt, testBit_rot ref.isLt z.isLt] at hqz
      have := congrArg (fun b => xor b (row.val.testBit z.val)) hqz
      simpa only [bool_xor_cancel, toBits, rotBack] using this
    · intro h z hz
      change (stateAt k constant row.val 0 q.val).testBit (z.val % k) =
        (stateAt k constant row.val 0 ref.val).testBit (z.val % k)
      rw [Nat.mod_eq_of_lt z.isLt, stateAt_zero, stateAt_zero, Nat.testBit_xor, Nat.testBit_xor,
        testBit_rot q.isLt z.isLt, testBit_rot ref.isLt z.isLt]
      have hw := h (rotBack z) (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
      simp only [toBits, rotBack] at hw
      rw [hw]
  have hfiber_card : fiber.card = 2 ^ (k - pin.card) := by
    have hbij : fiber.card =
        ((Finset.univ : Finset (Fin k → Bool)).filter
          (fun w => inAff pinKey ∅ (toBits ref) (fun _ => false) (fun _ _ => false) w = true)).card := by
      refine Finset.card_nbij toBits ?_ ?_ ?_
      · intro q hq
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        unfold inAff
        rw [decide_eq_true_eq]
        exact ⟨(hfiber_iff q).mp hq, fun _ h => absurd h (Finset.notMem_empty _)⟩
      · intro q1 _ q2 _ h
        exact (bitsEquiv k).injective h
      · intro w hw
        refine ⟨ofBits w, (hfiber_iff (ofBits w)).mpr ?_, toBits_ofBits w⟩
        rw [toBits_ofBits]
        exact (of_decide_eq_true (Finset.mem_filter.mp hw).2).1
    rw [hbij, card_inAff pinKey ∅ (Finset.empty_subset _), hpinKey_card, Finset.card_empty, Nat.sub_zero]
  cases m with
  | zero =>
    have hM1 : M = 1 := Nat.min_eq_right hL
    have hd0 : d = 0 := by simp [d, hM1]
    have ha0 : a = 0 := by simp [a, hM1, hd0]
    have hNe : ∀ e, N0 e = 2 ^ (k - pin.card) := fun e => by
      simp [N0, B0, hd0, ha0]
    have hscore_eq : ∀ T ask P e, score0 T ask P e = 2 ^ (k - pin.card) := by
      intro T ask P e
      have hfilt : fiber.filter (fun x =>
          ((Finset.univ : Finset (Fin 0)).filter
            (fun i => P (run0 T ask x) i x != target x i)).card ≤ e) = fiber := by
        ext x
        simp
      simp only [score0, hfilt, hfiber_card]
    constructor
    · intro T ask P _ _ e
      rw [hscore_eq, hNe]
    · refine ⟨∅, fun _ _ => false, fun _ i => Fin.elim0 i, by simpa using hL, ?_, ?_, ?_⟩
      · intro p; simp
      · intro p i; exact Fin.elim0 i
      · intro e; exact (hscore_eq ∅ (fun _ _ => false) (fun _ i => Fin.elim0 i) e).trans (hNe e).symm
  | succ m' =>
    let m := m' + 1
    have hk12 : 12 ≤ k := by
      let f12 : Fin 12 → Fin k := fun j => ⟨(starts ⟨0, Nat.succ_pos m'⟩ + j.val) % k, Nat.mod_lt _ hk⟩
      have hf12 : Function.Injective f12 := fun j1 j2 h =>
        (Prod.mk.inj (hinj (congrArg Fin.val h))).2
      have hle := Fintype.card_le_of_injective f12 hf12
      simpa using hle
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    let tKey : Fin m × Fin 3 ↪ Fin k :=
      ⟨fun p => ⟨(starts p.1 + 8 + p.2.val) % k, Nat.mod_lt _ hk⟩,
       fun p1 p2 h => by
         have hv : (starts p1.1 + (8 + p1.2.val)) % k = (starts p2.1 + (8 + p2.2.val)) % k := by
           simpa [Nat.add_assoc] using congrArg Fin.val h
         let z1 : Fin m × Fin 12 := (p1.1, ⟨8 + p1.2.val, by omega⟩)
         let z2 : Fin m × Fin 12 := (p2.1, ⟨8 + p2.2.val, by omega⟩)
         have hz : z1 = z2 := hinj hv
         have hf := Prod.mk.inj hz
         exact Prod.ext hf.1 (Fin.ext (by have := Fin.mk.inj hf.2; omega))⟩
    have htKey_eq_rotBack : ∀ i (j : Fin 3),
        tKey (i, j) = rotBack ⟨(starts i + 9 + j.val) % k, Nat.mod_lt _ hk⟩ := by
      intro i j
      apply Fin.ext
      change (starts i + 8 + j.val) % k = ((starts i + 9 + j.val) % k + k - 1 % k) % k
      have hsub := mod_sub_eq hk (p := starts i + 9 + j.val) (s := 1) (by omega)
      rw [hsub]
      congr 1
      omega
    have htFree : ∀ p, tKey p ∉ pinKey := by
      intro ⟨i, j⟩ hmem
      rcases Finset.mem_image.mp hmem with ⟨z, hz, hzeq⟩
      rw [htKey_eq_rotBack i j] at hzeq
      have hzf := hrotBack_inj hzeq
      exact hfree i j z hz (congrArg Fin.val hzf)
    have h3m : 3 * m ≤ k - pinKey.card := by
      have hdisj : Disjoint pinKey (Finset.univ.image tKey) := by
        rw [Finset.disjoint_left]
        intro z hzp hzT
        rcases Finset.mem_image.mp hzT with ⟨p, _, rfl⟩
        exact htFree p hzp
      have hle := Finset.card_le_univ (pinKey ∪ Finset.univ.image tKey)
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ tKey.injective,
        Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        Fintype.card_fin] at hle
      omega
    have hQex : ∀ i : Fin m, ∃ Qi : (Fin k → Bool) → Bool, quadBits Qi ∧
        ∀ q ∈ fiber, target q i =
          xor (toBits q (tKey (i, 0)) && toBits q (tKey (i, 1)) && toBits q (tKey (i, 2)))
            (Qi (toBits q)) := by
      intro i
      obtain ⟨s0, s1, s2, c0, l0, l1, l2, hform⟩ :=
        guarded_two_round_formula hk12 constant row ref (starts i) (hgood i)
      let v0 := tKey (i, 0)
      let v1 := tKey (i, 1)
      let v2 := tKey (i, 2)
      let Qi : (Fin k → Bool) → Bool := fun w =>
        xor
          (xor (xor (xor (s0 && s1 && s2)
            (xor (xor ((s1 && s2) && w v0) ((s0 && s2) && w v1)) ((s0 && s1) && w v2)))
            (xor (s2 && w v0 && w v1) (s1 && w v0 && w v2))) (s0 && w v1 && w v2))
          (xor (xor (xor c0 (l0 && w v0)) (l1 && w v1)) (l2 && w v2))
      have hQi : quadBits Qi := by
        apply quadBits_xor
        · apply quadBits_xor
          · apply quadBits_xor
            · apply quadBits_xor
              · exact quadBits_const _
              · apply quadBits_xor
                · exact quadBits_xor (quadBits_var _ v0) (quadBits_var _ v1)
                · exact quadBits_var _ v2
            · exact quadBits_xor (quadBits_and2 _ v0 v1) (quadBits_and2 _ v0 v2)
          · exact quadBits_and2 _ v1 v2
        · exact quadBits_xor
            (quadBits_xor (quadBits_xor (quadBits_const c0) (quadBits_var l0 v0)) (quadBits_var l1 v1))
            (quadBits_var l2 v2)
      refine ⟨Qi, hQi, fun q hq => ?_⟩
      have hpin9 : ∀ j : Fin 9,
          (stateAt k constant row.val 0 q.val).testBit ((starts i + j.val) % k) =
          (stateAt k constant row.val 0 ref.val).testBit ((starts i + j.val) % k) := by
        intro j
        obtain ⟨z, hz, hzval⟩ := hpin i j
        have hqz := (Finset.mem_filter.mp hq).2 z hz
        change (stateAt k constant row.val 0 q.val).testBit (z.val % k) =
          (stateAt k constant row.val 0 ref.val).testBit (z.val % k) at hqz
        rw [Nat.mod_eq_of_lt z.isLt, hzval] at hqz
        exact hqz
      have hf := hform q hpin9
      change (stateAt k constant row.val 2 q.val).testBit ((starts i + 5) % k) = _
      rw [hf]
      have hu0 : q.val.testBit ((starts i + 8) % k) = toBits q v0 := by
        change q.val.testBit ((starts i + 8) % k) = q.val.testBit ((starts i + 8 + 0) % k)
        simp
      have hu1 : q.val.testBit ((starts i + 9) % k) = toBits q v1 := by
        change q.val.testBit ((starts i + 9) % k) = q.val.testBit ((starts i + 8 + 1) % k)
        congr 2
      have hu2 : q.val.testBit ((starts i + 10) % k) = toBits q v2 := by
        change q.val.testBit ((starts i + 10) % k) = q.val.testBit ((starts i + 8 + 2) % k)
        congr 2
      rw [hu0, hu1, hu2, cubic_shift_eq]
      have hxa : ∀ x y z : Bool, xor (xor x y) z = xor x (xor y z) := by
        intro x y z; cases x <;> cases y <;> cases z <;> rfl
      exact hxa _ _ _
    choose Q hQ htarget_eq using hQex
    have hquad_iff : ∀ g : K → Bool, quad0 g ↔ quadBits (fun w => g (ofBits w)) := by
      intro g
      constructor
      · rintro ⟨b, l, aa, hg⟩
        refine ⟨b, l, aa, fun w => ?_⟩
        have hb : ∀ i : Fin k, bitOf (ofBits w) i = w i := fun i => congrFun (toBits_ofBits w) i
        have hgw := hg (ofBits w)
        simp only [lin0, par0, hb] at hgw
        exact hgw
      · rintro ⟨b, l, aa, hg⟩
        refine ⟨b, l, aa, fun q => ?_⟩
        have hgw := hg (toBits q)
        dsimp only at hgw
        rw [ofBits_toBits] at hgw
        exact hgw
    have hrun_eq : ∀ T ask (q : K),
        run0 T ask q =
          runIter (fun p => if p ∈ T then p ++ [linBits (ask p) (toBits q)] else p) T.card [] := by
      intro T ask q
      change (List.range T.card).foldl
        (fun p _ => if p ∈ T then p ++ [linBits (ask p) (toBits q)] else p) [] = _
      rw [foldl_const_eq_runIter, List.length_range]
    have hB_eq : ∀ p e, B0 p e = B_fn (k - pinKey.card) m p e := by
      intro p e
      simp only [B0, B_fn, T_fn, hpinKey_card, m]
    constructor
    · intro T ask P hTL hP e
      let Pbits : List Bool → Fin m → (Fin k → Bool) → Bool := fun p i w => P p i (ofBits w)
      have hPbits : ∀ p i, quadBits (Pbits p i) := fun p i => (hquad_iff (P p i)).mp (hP p i)
      let targetBits : (Fin k → Bool) → Fin m → Bool := fun w i =>
        xor (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) (Q i w)
      let stepRun := fun (w : Fin k → Bool) (p : List Bool) =>
        if p ∈ T then p ++ [linBits (ask p) w] else p
      have hscore_bij : score0 T ask P e =
          (((Finset.univ : Finset (Fin k → Bool)).filter
            (fun w => inAff pinKey ∅ (toBits ref) (fun _ => false) (fun _ _ => false) w = true)).filter
            (fun w => ((Finset.univ : Finset (Fin m)).filter
              (fun i => Pbits (runIter (stepRun w) T.card []) i w != targetBits w i)).card ≤ e)).card := by
        unfold score0
        refine Finset.card_nbij toBits ?_ ?_ ?_
        · intro x hx
          have hxf := (Finset.mem_filter.mp hx).1
          have hxerr := (Finset.mem_filter.mp hx).2
          have haff : inAff pinKey ∅ (toBits ref) (fun _ => false) (fun _ _ => false) (toBits x) = true := by
            unfold inAff; rw [decide_eq_true_eq]
            exact ⟨(hfiber_iff x).mp hxf, fun _ h => absurd h (Finset.notMem_empty _)⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, haff⟩, ?_⟩
          have hfeq : (Finset.univ.filter fun i : Fin m =>
              Pbits (runIter (stepRun (toBits x)) T.card []) i (toBits x) != targetBits (toBits x) i) =
              Finset.univ.filter fun i : Fin m => P (run0 T ask x) i x != target x i := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pbits, ofBits_toBits,
              stepRun, ← hrun_eq T ask x, ← htarget_eq i x hxf, targetBits]
          rw [hfeq]
          exact hxerr
        · intro x1 _ x2 _ h
          exact (bitsEquiv k).injective h
        · intro w hw
          have hwAff := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
          have hwErr := (Finset.mem_filter.mp hw).2
          have hof_fib : ofBits w ∈ fiber := (hfiber_iff (ofBits w)).mpr (by
            rw [toBits_ofBits]
            exact (of_decide_eq_true hwAff).1)
          refine ⟨ofBits w, Finset.mem_filter.mpr ⟨hof_fib, ?_⟩, toBits_ofBits w⟩
          have hfeq : (Finset.univ.filter fun i : Fin m => P (run0 T ask (ofBits w)) i (ofBits w) != target (ofBits w) i) =
              Finset.univ.filter fun i : Fin m =>
                Pbits (runIter (stepRun w) T.card []) i w != targetBits w i := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pbits,
              stepRun, hrun_eq T ask (ofBits w), toBits_ofBits, htarget_eq i (ofBits w) hof_fib, targetBits]
          rw [hfeq]
          exact hwErr
      have hsub_empty : subT T [] = T := by
        ext q
        simp [subT, isPref]
      obtain ⟨cnt, hcap, hsum, hle⟩ :=
        tree_aff_bound pinKey (toBits ref) tKey htFree h3m Q hQ T ask Pbits hPbits e
          T.card [] T.card ∅ (Finset.empty_subset _) (fun _ => false) (fun _ _ => false)
          (by rw [hsub_empty])
      rw [hscore_bij]
      simp only [Finset.card_empty, Nat.zero_add] at hle
      have hsumL : (∑ j ∈ Finset.range (T.card + 1), cnt j) ≤ L - 1 := by omega
      have hgb := greedy_bound (F_sz := k - pinKey.card) (m := m) (e := e) (L := L) h3m hL cnt hcap hsumL
      dsimp only at hgb
      have hNeq : N0 e = (2 ^ d - a) * B_fn (k - pinKey.card) m d e +
          2 * a * B_fn (k - pinKey.card) m (d + 1) e := by
        simp only [N0, hB_eq]
      rw [hNeq]
      exact hle.trans hgb
    · have hMpos : 0 < M := Nat.lt_min.mpr ⟨hL, Nat.two_pow_pos m⟩
      have h2d_le : 2 ^ d ≤ M := Nat.log2_self_le (by omega)
      have hM_lt : M < 2 ^ (d + 1) := Nat.lt_log2_self
      have ha_lt : a < 2 ^ d := by
        have : 2 ^ (d + 1) = 2 ^ d * 2 := Nat.pow_succ 2 d
        omega
      have hd_le_m : d ≤ m := by
        by_contra hgt
        have hlt : m < d := Nat.lt_of_not_ge hgt
        have hp : 2 ^ m < 2 ^ d := Nat.pow_lt_pow_right (by omega : 1 < 2) hlt
        have hMle : M ≤ 2 ^ m := Nat.min_le_right L (2 ^ m)
        omega
      have hdm : 0 < a → d < m := by
        intro hapos
        by_contra hge
        have hdeq : d = m := by omega
        have h2eq : 2 ^ d = 2 ^ m := congrArg (2 ^ ·) hdeq
        have hMle : M ≤ 2 ^ m := Nat.min_le_right L (2 ^ m)
        have ha_def : a = M - 2 ^ d := rfl
        omega
      let Tstar := optTree d a
      let askStar := optAsk tKey
      let PstarBits : List Bool → Fin m → (Fin k → Bool) → Bool := fun p i w =>
        if h : i.val < p.length then
          xor (p[i.val] && w (tKey (i, 1)) && w (tKey (i, 2))) (Q i w)
        else Q i w
      let Pstar : List Bool → Fin m → K → Bool := fun p i q => PstarBits p i (toBits q)
      have hTcard : Tstar.card < L := by
        rw [card_optTree ha_lt]
        have hMle : M ≤ L := Nat.min_le_left L (2 ^ m)
        have h2dpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
        omega
      have hPstar_quad : ∀ p i, quad0 (Pstar p i) := by
        intro p i
        rw [hquad_iff]
        have heq : (fun w => Pstar p i (ofBits w)) = PstarBits p i := by
          funext w; simp [Pstar, toBits_ofBits]
        rw [heq]
        dsimp only [PstarBits]
        by_cases h : i.val < p.length
        · simp only [h, ↓reduceDIte]
          exact quadBits_xor (quadBits_and2 p[i.val] (tKey (i, 1)) (tKey (i, 2))) (hQ i)
        · simp only [h, ↓reduceDIte]
          exact hQ i
      refine ⟨Tstar, askStar, Pstar, hTcard, card_optAsk_le_one tKey, hPstar_quad, fun e => ?_⟩
      let S_all := (Finset.univ : Finset (Fin k → Bool)).filter (fun w =>
        (∀ z ∈ pinKey, w z = toBits ref z) ∧
        ((Finset.univ : Finset (Fin m)).filter (fun i =>
          let len := if bitsVal (prefBits tKey w d) < a then d + 1 else d
          len ≤ i.val ∧ (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true)).card ≤ e)
      have hscore_eq_S : score0 Tstar askStar Pstar e = S_all.card := by
        unfold score0
        refine Finset.card_nbij toBits ?_ ?_ ?_
        · intro x hx
          have hxf := (Finset.mem_filter.mp hx).1
          have hxerr := (Finset.mem_filter.mp hx).2
          have hrun := run_optTree tKey hd_le_m ha_lt hdm (toBits x)
          have hrunx : run0 Tstar askStar x =
              if bitsVal (prefBits tKey (toBits x) d) < a then
                prefBits tKey (toBits x) (d + 1)
              else prefBits tKey (toBits x) d := by
            rw [hrun_eq]; exact hrun
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hfiber_iff x).mp hxf, ?_⟩
          have hfeq : (Finset.univ.filter fun i : Fin m =>
              (if bitsVal (prefBits tKey (toBits x) d) < a then d + 1 else d) ≤ i.val ∧
              (toBits x (tKey (i, 0)) && toBits x (tKey (i, 1)) && toBits x (tKey (i, 2))) = true) =
              Finset.univ.filter fun i : Fin m => Pstar (run0 Tstar askStar x) i x != target x i := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pstar, hrunx,
              htarget_eq i x hxf, PstarBits]
            set len := if bitsVal (prefBits tKey (toBits x) d) < a then d + 1 else d
            have hplen : (if bitsVal (prefBits tKey (toBits x) d) < a then
                prefBits tKey (toBits x) (d + 1) else prefBits tKey (toBits x) d).length = len := by
              dsimp only [len]; split_ifs <;> exact prefBits_length _ _ _
            by_cases hil : i.val < len
            · have hil' : i.val < (if bitsVal (prefBits tKey (toBits x) d) < a then
                  prefBits tKey (toBits x) (d + 1) else prefBits tKey (toBits x) d).length := by omega
              have hget : (if bitsVal (prefBits tKey (toBits x) d) < a then
                  prefBits tKey (toBits x) (d + 1) else prefBits tKey (toBits x) d)[i.val]'hil' =
                  toBits x (tKey (i, 0)) := by
                rw [getElem_ite_list]
                split_ifs <;> simp only [prefBits, List.getElem_ofFn, i.isLt, ↓reduceDIte, Fin.eta]
              simp only [hil', ↓reduceDIte, hget, bne_self_eq_false, Bool.false_eq_true, iff_false]
              omega
            · have hil' : ¬ i.val < (if bitsVal (prefBits tKey (toBits x) d) < a then
                  prefBits tKey (toBits x) (d + 1) else prefBits tKey (toBits x) d).length := by omega
              have hle : len ≤ i.val := by omega
              simp only [hil', ↓reduceDIte, hle, true_and]
              cases toBits x (tKey (i, 0)) && toBits x (tKey (i, 1)) && toBits x (tKey (i, 2)) <;>
                cases Q i (toBits x) <;> simp
          rw [hfeq]
          exact hxerr
        · intro x1 _ x2 _ h
          exact (bitsEquiv k).injective h
        · intro w hw
          have hwp := (Finset.mem_filter.mp hw).2.1
          have hwerr := (Finset.mem_filter.mp hw).2.2
          have hof_fib : ofBits w ∈ fiber := (hfiber_iff (ofBits w)).mpr (by rw [toBits_ofBits]; exact hwp)
          refine ⟨ofBits w, Finset.mem_filter.mpr ⟨hof_fib, ?_⟩, toBits_ofBits w⟩
          have hrun := run_optTree tKey hd_le_m ha_lt hdm w
          have hrunx : run0 Tstar askStar (ofBits w) =
              if bitsVal (prefBits tKey w d) < a then
                prefBits tKey w (d + 1)
              else prefBits tKey w d := by
            rw [hrun_eq, toBits_ofBits]; exact hrun
          have hfeq : (Finset.univ.filter fun i : Fin m =>
              Pstar (run0 Tstar askStar (ofBits w)) i (ofBits w) != target (ofBits w) i) =
              Finset.univ.filter fun i : Fin m =>
                (if bitsVal (prefBits tKey w d) < a then d + 1 else d) ≤ i.val ∧
                (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pstar, hrunx,
              htarget_eq i (ofBits w) hof_fib, toBits_ofBits, PstarBits]
            set len := if bitsVal (prefBits tKey w d) < a then d + 1 else d
            have hplen : (if bitsVal (prefBits tKey w d) < a then
                prefBits tKey w (d + 1) else prefBits tKey w d).length = len := by
              dsimp only [len]; split_ifs <;> exact prefBits_length _ _ _
            by_cases hil : i.val < len
            · have hil' : i.val < (if bitsVal (prefBits tKey w d) < a then
                  prefBits tKey w (d + 1) else prefBits tKey w d).length := by omega
              have hget : (if bitsVal (prefBits tKey w d) < a then
                  prefBits tKey w (d + 1) else prefBits tKey w d)[i.val]'hil' =
                  w (tKey (i, 0)) := by
                rw [getElem_ite_list]
                split_ifs <;> simp only [prefBits, List.getElem_ofFn, i.isLt, ↓reduceDIte, Fin.eta]
              simp only [hil', ↓reduceDIte, hget, bne_self_eq_false, Bool.false_eq_true, false_iff]
              omega
            · have hil' : ¬ i.val < (if bitsVal (prefBits tKey w d) < a then
                  prefBits tKey w (d + 1) else prefBits tKey w d).length := by omega
              have hle : len ≤ i.val := by omega
              simp only [hil', ↓reduceDIte, hle, true_and]
              cases w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2)) <;>
                cases Q i w <;> simp
          rw [hfeq]
          exact hwerr
      rw [hscore_eq_S]
      have hpartS : S_all.card =
          (S_all.filter (fun w => ¬ bitsVal (prefBits tKey w d) < a)).card +
          (S_all.filter (fun w => bitsVal (prefBits tKey w d) < a)).card := by
        rw [Nat.add_comm]
        exact (card_filter_add_not S_all (fun w => bitsVal (prefBits tKey w d) < a)).symm
      rw [hpartS]
      have hpart1 : (S_all.filter (fun w => ¬ bitsVal (prefBits tKey w d) < a)).card =
          (2 ^ d - a) * B0 d e := by
        have hfeq : S_all.filter (fun w => ¬ bitsVal (prefBits tKey w d) < a) =
            (Finset.univ : Finset (Fin k → Bool)).filter (fun w =>
              (∀ z ∈ pinKey, w z = toBits ref z) ∧
              decide (a ≤ bitsVal (List.ofFn fun t : Fin d =>
                w (tKey (⟨t.val, lt_of_lt_of_le t.isLt hd_le_m⟩, 0)))) = true ∧
              ((Finset.univ : Finset (Fin m)).filter (fun i =>
                d ≤ i.val ∧ (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true)).card ≤ e) := by
          ext w
          have hpref_eq : prefBits tKey w d =
              List.ofFn fun t : Fin d => w (tKey (⟨t.val, lt_of_lt_of_le t.isLt hd_le_m⟩, 0)) := by
            unfold prefBits
            congr 1
            funext t
            simp [lt_of_lt_of_le t.isLt hd_le_m]
          simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, hpref_eq]
          constructor
          · rintro ⟨⟨hpinw, herr⟩, hnot⟩
            simp only [hnot, ↓reduceIte] at herr
            exact ⟨hpinw, by omega, herr⟩
          · rintro ⟨hpinw, hge, herr⟩
            have hnot : ¬ bitsVal (List.ofFn fun t : Fin d =>
                w (tKey (⟨t.val, lt_of_lt_of_le t.isLt hd_le_m⟩, 0))) < a := by omega
            refine ⟨⟨hpinw, ?_⟩, hnot⟩
            simpa only [hnot, ↓reduceIte] using herr
        rw [hfeq, card_fiber_prefix_tail pinKey (toBits ref) tKey htFree d hd_le_m
          (fun u => decide (a ≤ bitsVal (List.ofFn u))) e]
        simp only [decide_eq_true_eq, card_fin_bitsVal_ge d a (by omega), hB_eq]
      have hpart2 : (S_all.filter (fun w => bitsVal (prefBits tKey w d) < a)).card =
          2 * a * B0 (d + 1) e := by
        by_cases ha0 : a = 0
        · rw [ha0]
          simp
        · have hd1_le : d + 1 ≤ m := hdm (by omega)
          have hfeq : S_all.filter (fun w => bitsVal (prefBits tKey w d) < a) =
              (Finset.univ : Finset (Fin k → Bool)).filter (fun w =>
                (∀ z ∈ pinKey, w z = toBits ref z) ∧
                decide (bitsVal (List.ofFn fun t : Fin d =>
                  w (tKey (⟨t.val, lt_of_lt_of_le (Nat.lt_succ_of_lt t.isLt) hd1_le⟩, 0))) < a) = true ∧
                ((Finset.univ : Finset (Fin m)).filter (fun i =>
                  d + 1 ≤ i.val ∧ (w (tKey (i, 0)) && w (tKey (i, 1)) && w (tKey (i, 2))) = true)).card ≤ e) := by
            ext w
            have hpref_eq : prefBits tKey w d =
                List.ofFn fun t : Fin d =>
                  w (tKey (⟨t.val, lt_of_lt_of_le (Nat.lt_succ_of_lt t.isLt) hd1_le⟩, 0)) := by
              unfold prefBits
              congr 1
              funext t
              simp [lt_of_lt_of_le (Nat.lt_succ_of_lt t.isLt) hd1_le]
            simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, hpref_eq]
            constructor
            · rintro ⟨⟨hpinw, herr⟩, hlt⟩
              simp only [hlt, ↓reduceIte] at herr
              exact ⟨hpinw, hlt, herr⟩
            · rintro ⟨hpinw, hlt, herr⟩
              refine ⟨⟨hpinw, ?_⟩, hlt⟩
              simpa only [hlt, ↓reduceIte] using herr
          rw [hfeq, card_fiber_prefix_tail pinKey (toBits ref) tKey htFree (d + 1) hd1_le
            (fun u => decide (bitsVal (List.ofFn fun t : Fin d => u ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩) < a)) e]
          simp only [decide_eq_true_eq, card_fin_succ_bitsVal_lt d a (by omega), hB_eq]
      rw [hpart1, hpart2]

end PEqualNP.Outside.L_meta_32044

theorem PEqualNP.Outside.L_meta_32044 : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  ∀ L : Nat, 0 < L →
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let lin := fun (mask : Fin k → Bool) (q : K) =>
    par (∑ i : Fin k, (mask i && bitOf q i).toNat)
  let quad := fun (g : K → Bool) => ∃ (b : Bool) (l : Fin k → Bool) (a : Fin k → Fin k → Bool),
    ∀ q, g q = xor (xor b (lin l q))
      (par (∑ i : Fin k, ∑ j : Fin k, (a i j && bitOf q i && bitOf q j).toNat))
  let fiber := (Finset.univ : Finset K).filter (fun q =>
    ∀ z ∈ pin, bit row.val 0 q.val z.val = bit row.val 0 ref.val z.val)
  let target := fun (x : K) (i : Fin m) => bit row.val 2 x.val (starts i+5)
  let run := fun (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool) (x : K) =>
    (List.range T.card).foldl (fun (p : List Bool) _ =>
      if p ∈ T then p ++ [lin (ask p) x] else p) []
  let score := fun (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
      (P : List Bool → Fin m → K → Bool) (e : Nat) =>
    (fiber.filter (fun x =>
      ((Finset.univ : Finset (Fin m)).filter
        (fun i => P (run T ask x) i x != target x i)).card ≤ e)).card
  let B := fun (p e : Nat) =>
    let r := m-p
    2^(k-pin.card-p-3*r) *
      ∑ j ∈ Finset.range (min e r+1), Nat.choose r j * 7^(r-j)
  let M := min L (2^m)
  let d := Nat.log2 M
  let a := M-2^d
  let N := fun e : Nat => (2^d-a)*B d e + 2*a*B (d+1) e
  (∀ (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
      (P : List Bool → Fin m → K → Bool), T.card < L →
    (∀ p i, quad (P p i)) → ∀ e, score T ask P e ≤ N e) ∧
  ∃ (T : Finset (List Bool)) (ask : List Bool → Fin k → Bool)
      (P : List Bool → Fin m → K → Bool),
    T.card < L ∧ (∀ p, ((Finset.univ : Finset (Fin k)).filter (fun j => ask p j = true)).card ≤ 1) ∧
    (∀ p i, quad (P p i)) ∧ ∀ e, score T ask P e = N e :=
  PEqualNP.Outside.L_meta_32044.main_proof
