import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25528_aux

private def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word b : Nat) : Bool :=
  xor (word.testBit b) (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))

private def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc b =>
    acc ||| ((xor (word.testBit b)
      (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0

private def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

private def stateAt (k : Nat) (c : Nat → Fin (2 ^ k)) (u rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev t =>
    step k (mix k prev) ^^^ rot k (2 * t) key ^^^ (c (t + 1)).val) (rot k 1 key ^^^ u)

private def flipBit (k pos w : Nat) : Nat :=
  w ^^^ (1 <<< (pos % k))

private theorem stateAt_zero (k : Nat) (c : Nat → Fin (2 ^ k)) (u key : Nat) :
    stateAt k c u 0 key = rot k 1 key ^^^ u := rfl

private theorem stateAt_succ (k : Nat) (c : Nat → Fin (2 ^ k)) (u t key : Nat) :
    stateAt k c u (t + 1) key =
      step k (mix k (stateAt k c u t key)) ^^^ rot k (2 * t) key ^^^ (c (t + 1)).val := by
  simp [stateAt, List.range_succ]

private theorem rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private theorem xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

private theorem flipBit_lt {k pos w : Nat} (hk : 0 < k) (hw : w < 2 ^ k) :
    flipBit k pos w < 2 ^ k := by
  unfold flipBit
  have hp : pos % k < k := Nat.mod_lt _ hk
  have h1 : 1 <<< (pos % k) < 2 ^ k := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) hp
  exact xor_lt hw h1

private theorem testBit_flipBit {k pos w b : Nat} :
    (flipBit k pos w).testBit b = xor (w.testBit b) (decide (b = pos % k)) := by
  unfold flipBit
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  by_cases h : pos % k = b
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
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

private theorem testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc j : Nat) :
    (xs.foldl (fun a b => a ||| ((p b).toNat <<< b)) acc).testBit j =
      (acc.testBit j || (decide (j ∈ xs) && p j)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hbj : b = j
    · subst b
      cases p j <;> simp
    · by_cases hle : b ≤ j
      · have hsub : 1 ≤ j - b := by omega
        have hbt : (p b).toNat.testBit (j - b) = false := by
          cases p b
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hbj]
      · simp [hle, Ne.symm hbj]

private theorem testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

private theorem testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

private theorem step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

private theorem stateAt_lt {k : Nat} (c : Nat → Fin (2 ^ k)) {u : Nat} (hu : u < 2 ^ k)
    (rounds key : Nat) : stateAt k c u rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) hu
  | succ t =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (c (t + 1)).isLt

private theorem testBit_mix {k word b : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
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

private theorem mod_cancel_left {k Q d : Nat} (hk : 0 < k) (hd : d < k) :
    ((Q + d) % k + k - Q % k) % k = d := by
  have hq : Q % k < k := Nat.mod_lt Q hk
  have hdiv := Nat.div_add_mod Q k
  rw [show (Q + d) % k + k - Q % k = (Q + d) % k + (k - Q % k) by omega, Nat.mod_add_mod,
    show Q + d + (k - Q % k) = d + k * (Q / k + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

private theorem mod_eq_imp_eq {k Q d₁ d₂ : Nat} (hd₁ : d₁ < k) (hd₂ : d₂ < k)
    (h : (Q + d₁) % k = (Q + d₂) % k) : d₁ = d₂ := by
  have hk : 0 < k := by omega
  have h1 : ((Q + d₁) % k + k - Q % k) % k = ((Q + d₂) % k + k - Q % k) % k := by rw [h]
  rw [mod_cancel_left hk hd₁, mod_cancel_left hk hd₂] at h1
  exact h1

private theorem mod_shift_ne {k A d₁ d₂ : Nat} (h1 : d₁ < d₂) (h2 : d₂ < d₁ + k) :
    (A + d₁) % k ≠ (A + d₂) % k := by
  intro heq
  have hk : 0 < k := by omega
  have hdiff : d₂ - d₁ < k := by omega
  have hA1 : A + d₂ = (A + d₁) + (d₂ - d₁) := by omega
  rw [hA1] at heq
  have h0 : (A + d₁ + 0) % k = (A + d₁ + (d₂ - d₁)) % k := by simpa using heq
  have hzero := mod_eq_imp_eq hk hdiff h0
  omega

private theorem testBit_rot_xor_flip {k s pos w b : Nat} (hk : 0 < k) (hw : w < 2 ^ k) (hb : b < k) :
    xor ((rot k s w).testBit b) ((rot k s (flipBit k pos w)).testBit b) =
      decide (b = (pos + s) % k) := by
  rw [testBit_rot hw hb, testBit_rot (flipBit_lt hk hw) hb, testBit_flipBit]
  have hcancel (a c : Bool) : xor a (xor a c) = c := by cases a <;> cases c <;> rfl
  rw [hcancel]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hs : s % k < k := Nat.mod_lt _ hk
  constructor
  · intro h
    have h1 : ((b + k - s % k) + s % k) % k = (pos % k + s % k) % k := by
      rw [← Nat.mod_add_mod (b + k - s % k), h, Nat.mod_add_mod]
    rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hb] at h1
    rw [h1, Nat.mod_add_mod, Nat.add_mod_mod]
  · intro h
    subst h
    have h1 : ((pos + s) % k + k - s % k) % k = ((pos + s) % k + (k - s % k)) % k := by
      congr 1; omega
    have hdiv := Nat.div_add_mod s k
    rw [h1, Nat.mod_add_mod,
      show pos + s + (k - s % k) = pos + k * (s / k + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
      Nat.add_mul_mod_self_left]

private theorem rot_one_rot_km1 {k w : Nat} (hk : 2 ≤ k) (hw : w < 2 ^ k) :
    rot k 1 (rot k (k - 1) w) = w := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · rw [testBit_rot (rot_lt k (k - 1) w) hb, testBit_rot hw (Nat.mod_lt _ (by omega))]
    have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]
    have hidx : ((b + k - 1) % k + k - (k - 1)) % k = b := by
      rw [show (b + k - 1) % k + k - (k - 1) = (b + k - 1) % k + 1 by omega,
        Nat.mod_add_mod, show b + k - 1 + 1 = b + k by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hb]
    rw [hidx]
  · have hge : k ≤ b := by omega
    have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hge
    rw [Nat.testBit_lt_two_pow ((rot_lt k 1 _).trans_le hpow),
        Nat.testBit_lt_two_pow (hw.trans_le hpow)]

private def keyOf (k u s0 : Nat) : Nat :=
  rot k (k - 1) (s0 ^^^ u)

private theorem keyOf_lt (k u s0 : Nat) : keyOf k u s0 < 2 ^ k :=
  rot_lt k (k - 1) (s0 ^^^ u)

private theorem stateAt_zero_keyOf {k u s0 : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 2 ≤ k) (hu : u < 2 ^ k) (hs0 : s0 < 2 ^ k) :
    stateAt k c u 0 (keyOf k u s0) = s0 := by
  rw [stateAt_zero]
  unfold keyOf
  rw [rot_one_rot_km1 hk (xor_lt hs0 hu)]
  apply Nat.eq_of_testBit_eq
  intro b
  simp only [Nat.testBit_xor]
  cases s0.testBit b <;> cases u.testBit b <;> rfl

private theorem testBit_foldl_or_pos (pos : Nat → Nat) (val : Nat → Bool) (xs : List Nat)
    (acc b : Nat) :
    (xs.foldl (fun a d => a ||| ((val d).toNat <<< pos d)) acc).testBit b =
      (acc.testBit b || xs.any (fun d => decide (pos d = b) && val d)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons d xs ih =>
    simp only [List.foldl_cons, List.any_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hdb : pos d = b
    · rw [hdb]
      cases acc.testBit b <;> cases val d <;> simp
    · by_cases hle : pos d ≤ b
      · have hsub : 1 ≤ b - pos d := by omega
        have hbt : (val d).toNat.testBit (b - pos d) = false := by
          cases val d
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, hdb]
      · simp [hle, hdb]

private def buildWord (k Q : Nat) (val : Nat → Bool) : Nat :=
  (List.range k).foldl (fun acc d => acc ||| ((val d).toNat <<< ((Q + d) % k))) 0

private theorem buildWord_lt {k Q : Nat} (hk : 0 < k) (val : Nat → Bool) :
    buildWord k Q val < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  unfold buildWord
  rw [testBit_foldl_or_pos, Nat.zero_testBit, Bool.false_or]
  rw [List.any_eq_false]
  intro d _
  have hlt : (Q + d) % k < k := Nat.mod_lt _ hk
  have hne : (Q + d) % k ≠ b := by omega
  simp [hne]

private theorem testBit_buildWord {k Q d : Nat} (hd : d < k) (val : Nat → Bool) :
    (buildWord k Q val).testBit ((Q + d) % k) = val d := by
  unfold buildWord
  rw [testBit_foldl_or_pos, Nat.zero_testBit, Bool.false_or]
  cases hv : val d with
  | true =>
    rw [List.any_eq_true]
    exact ⟨d, List.mem_range.mpr hd, by simp [hv]⟩
  | false =>
    rw [List.any_eq_false]
    intro d' hd'
    have hd'lt : d' < k := List.mem_range.mp hd'
    by_cases heq : (Q + d') % k = (Q + d) % k
    · have hdd : d' = d := mod_eq_imp_eq hd'lt hd heq
      subst hdd
      simp [hv]
    · simp [heq]

private theorem mod_Q_sub1 {k Q d : Nat} (hk : 2 ≤ k) (hd : 1 ≤ d) :
    ((Q + d) % k + k - 1) % k = (Q + (d - 1)) % k := by
  rw [show (Q + d) % k + k - 1 = (Q + d) % k + (k - 1) by omega, Nat.mod_add_mod,
    show Q + d + (k - 1) = (Q + (d - 1)) + k by omega, Nat.add_mod_right]

private theorem mod_Q_add {k Q d m : Nat} :
    ((Q + d) % k + m) % k = (Q + (d + m)) % k := by
  rw [Nat.mod_add_mod, Nat.add_assoc]

private theorem testBit_mix_Q {k Q d word : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hd : 1 ≤ d) :
    (mix k word).testBit ((Q + d) % k) =
      xor (xor (word.testBit ((Q + d) % k)) (word.testBit ((Q + (d - 1)) % k)))
        (word.testBit ((Q + (d + 1)) % k)) := by
  have hkpos : 0 < k := by omega
  rw [testBit_mix hk hw (Nat.mod_lt _ hkpos), mod_Q_sub1 hk hd, mod_Q_add]

private theorem testBit_mix_diff_Q {k Q d s₁ s₂ : Nat} (hk : 2 ≤ k)
    (hs₁ : s₁ < 2 ^ k) (hs₂ : s₂ < 2 ^ k) (hd : 1 ≤ d) :
    xor ((mix k s₁).testBit ((Q + d) % k)) ((mix k s₂).testBit ((Q + d) % k)) =
      xor (xor (xor (s₁.testBit ((Q + d) % k)) (s₂.testBit ((Q + d) % k)))
               (xor (s₁.testBit ((Q + (d - 1)) % k)) (s₂.testBit ((Q + (d - 1)) % k))))
          (xor (s₁.testBit ((Q + (d + 1)) % k)) (s₂.testBit ((Q + (d + 1)) % k))) := by
  rw [testBit_mix_Q hk hs₁ hd, testBit_mix_Q hk hs₂ hd]
  cases s₁.testBit ((Q + d) % k) <;> cases s₂.testBit ((Q + d) % k) <;>
    cases s₁.testBit ((Q + (d - 1)) % k) <;> cases s₂.testBit ((Q + (d - 1)) % k) <;>
    cases s₁.testBit ((Q + (d + 1)) % k) <;> cases s₂.testBit ((Q + (d + 1)) % k) <;> rfl

private theorem testBit_step_Q {k Q d word : Nat} (hk : 0 < k) :
    (step k word).testBit ((Q + d) % k) =
      xor (word.testBit ((Q + d) % k))
        (!(word.testBit ((Q + (d + 1)) % k)) && word.testBit ((Q + (d + 2)) % k)) := by
  rw [testBit_step (Nat.mod_lt _ hk)]
  unfold stepBit
  rw [mod_Q_add, mod_Q_add]

private theorem s1_bit_Q {k Q d u w : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 2 ≤ k) (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hd : 1 ≤ d) :
    let s0 := stateAt k c u 0 w
    let x := fun j => s0.testBit ((Q + j) % k)
    let M := fun j => (mix k s0).testBit ((Q + j) % k)
    let F := fun j => xor (u.testBit ((Q + j + 1) % k)) ((c 1).val.testBit ((Q + j) % k))
    (stateAt k c u 1 w).testBit ((Q + d) % k) =
      xor (xor (xor (x (d - 1)) (x d)) (!(M (d + 1)) && M (d + 2))) (F d) := by
  intro s0 x M F
  have hkpos : 0 < k := by omega
  have hs0 : s0 < 2 ^ k := stateAt_lt c hu 0 w
  rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step_Q hkpos]
  have hrot0 : (rot k (2 * 0) w).testBit ((Q + d) % k) = w.testBit ((Q + d) % k) := by
    rw [testBit_rot hw (Nat.mod_lt _ hkpos)]
    simp only [Nat.mul_zero, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
  have hwbit : w.testBit ((Q + d) % k) = xor (x (d + 1)) (u.testBit ((Q + d + 1) % k)) := by
    have hx : x (d + 1) = xor (w.testBit ((Q + d) % k)) (u.testBit ((Q + d + 1) % k)) := by
      dsimp only [x, s0]
      rw [stateAt_zero, Nat.testBit_xor, testBit_rot hw (Nat.mod_lt _ hkpos)]
      have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1, mod_Q_sub1 hk (by omega)]
      have he : d + 1 - 1 = d := by omega
      have he2 : Q + (d + 1) = Q + d + 1 := by omega
      rw [he, he2]
    rw [hx]
    cases w.testBit ((Q + d) % k) <;> cases u.testBit ((Q + d + 1) % k) <;> rfl
  have hMd : M d = xor (xor (x d) (x (d - 1))) (x (d + 1)) := testBit_mix_Q hk hs0 hd
  rw [hrot0, hwbit]
  change xor (xor (xor (M d) (!(M (d + 1)) && M (d + 2)))
    (xor (x (d + 1)) (u.testBit ((Q + d + 1) % k)))) ((c 1).val.testBit ((Q + d) % k)) =
    xor (xor (xor (x (d - 1)) (x d)) (!(M (d + 1)) && M (d + 2))) (F d)
  rw [hMd]
  dsimp only [F]
  cases x (d - 1) <;> cases x d <;> cases x (d + 1) <;>
    cases M (d + 1) <;> cases M (d + 2) <;>
    cases u.testBit ((Q + d + 1) % k) <;> cases (c 1).val.testBit ((Q + d) % k) <;> rfl

private theorem s0_diff_Q {k Q u w d : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 11 ≤ k) (hw : w < 2 ^ k) (hd : d < k) :
    let wf := flipBit k (Q + 4) w
    xor ((stateAt k c u 0 w).testBit ((Q + d) % k))
      ((stateAt k c u 0 wf).testBit ((Q + d) % k)) = decide (d = 5) := by
  intro wf
  have hkpos : 0 < k := by omega
  rw [stateAt_zero, stateAt_zero, Nat.testBit_xor, Nat.testBit_xor]
  have hcancel (a b v : Bool) : xor (xor a v) (xor b v) = xor a b := by
    cases a <;> cases b <;> cases v <;> rfl
  rw [hcancel, testBit_rot_xor_flip hkpos hw (Nat.mod_lt _ hkpos)]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have he : Q + 4 + 1 = Q + 5 := by omega
  rw [he]
  constructor
  · intro h; exact mod_eq_imp_eq hd (by omega) h
  · intro h; subst h; rfl

private theorem mix0_diff_Q {k Q u w d : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 11 ≤ k) (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hd : d < k) :
    let wf := flipBit k (Q + 4) w
    xor ((mix k (stateAt k c u 0 w)).testBit ((Q + d) % k))
      ((mix k (stateAt k c u 0 wf)).testBit ((Q + d) % k)) =
      decide (d = 4 ∨ d = 5 ∨ d = 6) := by
  intro wf
  have hkpos : 0 < k := by omega
  have hs0 : stateAt k c u 0 w < 2 ^ k := stateAt_lt c hu 0 w
  have hs0f : stateAt k c u 0 wf < 2 ^ k := stateAt_lt c hu 0 wf
  rw [testBit_mix (by omega) hs0 (Nat.mod_lt _ hkpos),
      testBit_mix (by omega) hs0f (Nat.mod_lt _ hkpos)]
  have hrearr (a1 a2 b1 b2 c1 c2 : Bool) :
      xor (xor (xor a1 b1) c1) (xor (xor a2 b2) c2) =
        xor (xor (xor a1 a2) (xor b1 b2)) (xor c1 c2) := by
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> rfl
  rw [hrearr, s0_diff_Q c hk hw hd]
  have hprev : xor ((stateAt k c u 0 w).testBit (((Q + d) % k + k - 1) % k))
      ((stateAt k c u 0 wf).testBit (((Q + d) % k + k - 1) % k)) = decide (d = 6) := by
    by_cases hd0 : d = 0
    · subst hd0
      have he : ((Q + 0) % k + k - 1) % k = (Q + (k - 1)) % k := by
        rw [show (Q + 0) % k + k - 1 = (Q + 0) % k + (k - 1) by omega, Nat.mod_add_mod, Nat.add_zero]
      rw [he, s0_diff_Q c hk hw (by omega)]
      simp [show k - 1 ≠ 5 by omega]
    · rw [mod_Q_sub1 (by omega) (by omega), s0_diff_Q c hk hw (by omega)]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
  have hnext : xor ((stateAt k c u 0 w).testBit (((Q + d) % k + 1) % k))
      ((stateAt k c u 0 wf).testBit (((Q + d) % k + 1) % k)) = decide (d = 4) := by
    rw [mod_Q_add]
    by_cases hdk : d + 1 < k
    · rw [s0_diff_Q c hk hw hdk]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · have he : (Q + (d + 1)) % k = (Q + 0) % k := by
        rw [show Q + (d + 1) = Q + 0 + k by omega, Nat.add_mod_right]
      rw [he, s0_diff_Q c hk hw hkpos]
      simp [show d ≠ 4 by omega]
  rw [hprev, hnext]
  by_cases h4 : d = 4
  · subst h4; rfl
  · by_cases h5 : d = 5
    · subst h5; rfl
    · by_cases h6 : d = 6
      · subst h6; rfl
      · simp [h4, h5, h6]

private theorem s1_diff_Q {k Q u w d : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 11 ≤ k) (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hd : d < k) :
    let wf := flipBit k (Q + 4) w
    let M := fun j => (mix k (stateAt k c u 0 w)).testBit ((Q + j) % k)
    xor ((stateAt k c u 1 w).testBit ((Q + d) % k))
      ((stateAt k c u 1 wf).testBit ((Q + d) % k)) =
      if d = 2 then !(M 3)
      else if d = 3 then xor (M 4) (M 5)
      else if d = 4 then xor (M 5) (M 6)
      else if d = 5 then !(M 7)
      else if d = 6 then true
      else false := by
  intro wf M
  have hkpos : 0 < k := by omega
  rw [stateAt_succ, stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
  have hrearr (a1 a2 b1 b2 v : Bool) :
      xor (xor (xor a1 b1) v) (xor (xor a2 b2) v) = xor (xor a1 a2) (xor b1 b2) := by
    cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases v <;> rfl
  rw [hrearr, testBit_step_Q hkpos, testBit_step_Q hkpos]
  have hkey : xor ((rot k (2 * 0) w).testBit ((Q + d) % k))
      ((rot k (2 * 0) wf).testBit ((Q + d) % k)) = decide (d = 4) := by
    rw [testBit_rot_xor_flip hkpos hw (Nat.mod_lt _ hkpos)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Nat.mul_zero, Nat.add_zero]
    constructor
    · intro h; exact mod_eq_imp_eq hd (by omega) h
    · intro h; subst h; rfl
  rw [hkey]
  have hmd0 := mix0_diff_Q (Q := Q) c hk hu hw hd
  have hmd_any : ∀ j, j < k →
      (mix k (stateAt k c u 0 wf)).testBit ((Q + j) % k) =
        xor (M j) (decide (j = 4 ∨ j = 5 ∨ j = 6)) := by
    intro j hj
    have h := mix0_diff_Q (Q := Q) c hk hu hw hj
    change xor (M j) ((mix k (stateAt k c u 0 wf)).testBit ((Q + j) % k)) = _ at h
    rw [← h]
    cases M j <;> cases (mix k (stateAt k c u 0 wf)).testBit ((Q + j) % k) <;> rfl
  have hmd1 : (mix k (stateAt k c u 0 wf)).testBit ((Q + (d + 1)) % k) =
      xor (M (d + 1)) (decide (d = 3 ∨ d = 4 ∨ d = 5)) := by
    by_cases hlt : d + 1 < k
    · rw [hmd_any (d + 1) hlt]
      have hd1 : decide (d + 1 = 4 ∨ d + 1 = 5 ∨ d + 1 = 6) = decide (d = 3 ∨ d = 4 ∨ d = 5) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [hd1]
    · have he : (Q + (d + 1)) % k = (Q + 0) % k := by
        rw [show Q + (d + 1) = Q + 0 + k by omega, Nat.add_mod_right]
      have hm0 : M (d + 1) = M 0 := by dsimp only [M]; rw [he]
      rw [he, hmd_any 0 hkpos, hm0]
      have hne : decide (d = 3 ∨ d = 4 ∨ d = 5) = false := by rw [decide_eq_false_iff_not]; omega
      rw [hne]; rfl
  have hmd2 : (mix k (stateAt k c u 0 wf)).testBit ((Q + (d + 2)) % k) =
      xor (M (d + 2)) (decide (d = 2 ∨ d = 3 ∨ d = 4)) := by
    by_cases hlt : d + 2 < k
    · rw [hmd_any (d + 2) hlt]
      have hd2 : decide (d + 2 = 4 ∨ d + 2 = 5 ∨ d + 2 = 6) = decide (d = 2 ∨ d = 3 ∨ d = 4) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [hd2]
    · have hsub : d + 2 - k < 2 := by omega
      have he : (Q + (d + 2)) % k = (Q + (d + 2 - k)) % k := by
        rw [show Q + (d + 2) = Q + (d + 2 - k) + k by omega, Nat.add_mod_right]
      have hm2 : M (d + 2) = M (d + 2 - k) := by dsimp only [M]; rw [he]
      rw [he, hmd_any (d + 2 - k) (by omega), hm2]
      have hne1 : decide (d + 2 - k = 4 ∨ d + 2 - k = 5 ∨ d + 2 - k = 6) = false := by
        rw [decide_eq_false_iff_not]; omega
      have hne2 : decide (d = 2 ∨ d = 3 ∨ d = 4) = false := by
        rw [decide_eq_false_iff_not]; omega
      rw [hne1, hne2]
  have hmd0' : (mix k (stateAt k c u 0 wf)).testBit ((Q + d) % k) =
      xor (M d) (decide (d = 4 ∨ d = 5 ∨ d = 6)) := hmd_any d hd
  rw [hmd0', hmd1, hmd2]
  change xor (xor (xor (M d) (!(M (d + 1)) && M (d + 2)))
    (xor (xor (M d) (decide (d = 4 ∨ d = 5 ∨ d = 6)))
      (!(xor (M (d + 1)) (decide (d = 3 ∨ d = 4 ∨ d = 5))) &&
        xor (M (d + 2)) (decide (d = 2 ∨ d = 3 ∨ d = 4))))) (decide (d = 4)) = _
  by_cases h2 : d = 2
  · subst h2
    simp only [↓reduceIte]
    cases M 2 <;> cases M 3 <;> cases M 4 <;> rfl
  · by_cases h3 : d = 3
    · subst h3
      simp only [h2, ↓reduceIte]
      cases M 3 <;> cases M 4 <;> cases M 5 <;> rfl
    · by_cases h4 : d = 4
      · subst h4
        simp only [h2, h3, ↓reduceIte]
        cases M 4 <;> cases M 5 <;> cases M 6 <;> rfl
      · by_cases h5 : d = 5
        · subst h5
          simp only [h2, h3, h4, ↓reduceIte]
          cases M 5 <;> cases M 6 <;> cases M 7 <;> rfl
        · by_cases h6 : d = 6
          · subst h6
            simp only [h2, h3, h4, h5, ↓reduceIte]
            cases M 6 <;> cases M 7 <;> cases M 8 <;> rfl
          · simp only [h2, h3, h4, h5, h6, ↓reduceIte, or_self, decide_false]
            cases M d <;> cases M (d + 1) <;> cases M (d + 2) <;> rfl

private theorem s2_diff_patA {k Q u w d : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 11 ≤ k) (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hd : d < k)
    (h1 : ∀ j, j < k →
      xor ((stateAt k c u 1 w).testBit ((Q + j) % k))
        ((stateAt k c u 1 (flipBit k (Q + 4) w)).testBit ((Q + j) % k)) = decide (j = 6)) :
    let wf := flipBit k (Q + 4) w
    let N := fun j => (mix k (stateAt k c u 1 w)).testBit ((Q + j) % k)
    (d < 5 ∨ 8 ≤ d) →
    N 4 = true →
    N 5 = N 6 →
    (stateAt k c u 2 w).testBit ((Q + d) % k) = (stateAt k c u 2 wf).testBit ((Q + d) % k) := by
  intro wf N hrange hN4 hN56
  have hkpos : 0 < k := by omega
  have hs1 : stateAt k c u 1 w < 2 ^ k := stateAt_lt c hu 1 w
  have hs1f : stateAt k c u 1 wf < 2 ^ k := stateAt_lt c hu 1 wf
  have hmix1 : ∀ j, j < k →
      (mix k (stateAt k c u 1 wf)).testBit ((Q + j) % k) =
        xor (N j) (decide (j = 5 ∨ j = 6 ∨ j = 7)) := by
    intro j hj
    have hdiff : xor (N j) ((mix k (stateAt k c u 1 wf)).testBit ((Q + j) % k)) =
        decide (j = 5 ∨ j = 6 ∨ j = 7) := by
      dsimp only [N]
      rw [testBit_mix (by omega) hs1 (Nat.mod_lt _ hkpos),
          testBit_mix (by omega) hs1f (Nat.mod_lt _ hkpos)]
      have hrearr (a1 a2 b1 b2 c1 c2 : Bool) :
          xor (xor (xor a1 b1) c1) (xor (xor a2 b2) c2) =
            xor (xor (xor a1 a2) (xor b1 b2)) (xor c1 c2) := by
        cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> rfl
      rw [hrearr, h1 j hj]
      have hprev : xor ((stateAt k c u 1 w).testBit (((Q + j) % k + k - 1) % k))
          ((stateAt k c u 1 wf).testBit (((Q + j) % k + k - 1) % k)) = decide (j = 7) := by
        by_cases hj0 : j = 0
        · subst hj0
          have he : ((Q + 0) % k + k - 1) % k = (Q + (k - 1)) % k := by
            rw [show (Q + 0) % k + k - 1 = (Q + 0) % k + (k - 1) by omega, Nat.mod_add_mod, Nat.add_zero]
          rw [he, h1 (k - 1) (by omega)]
          simp [show k - 1 ≠ 6 by omega]
        · rw [mod_Q_sub1 (by omega) (by omega), h1 (j - 1) (by omega)]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      have hnext : xor ((stateAt k c u 1 w).testBit (((Q + j) % k + 1) % k))
          ((stateAt k c u 1 wf).testBit (((Q + j) % k + 1) % k)) = decide (j = 5) := by
        rw [mod_Q_add]
        by_cases hjk : j + 1 < k
        · rw [h1 (j + 1) hjk]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
        · have he : (Q + (j + 1)) % k = (Q + 0) % k := by
            rw [show Q + (j + 1) = Q + 0 + k by omega, Nat.add_mod_right]
          rw [he, h1 0 hkpos]
          simp [show j ≠ 5 by omega]
      rw [hprev, hnext]
      by_cases h5 : j = 5
      · subst h5; rfl
      · by_cases h6 : j = 6
        · subst h6; rfl
        · by_cases h7 : j = 7
          · subst h7; rfl
          · simp [h5, h6, h7]
    rw [← hdiff]
    cases N j <;> cases (mix k (stateAt k c u 1 wf)).testBit ((Q + j) % k) <;> rfl
  have hkey : (rot k (2 * 1) w).testBit ((Q + d) % k) = (rot k (2 * 1) wf).testBit ((Q + d) % k) := by
    have hx := testBit_rot_xor_flip (s := 2 * 1) (pos := Q + 4) hkpos hw (Nat.mod_lt (Q + d) hkpos)
    have hne : (Q + d) % k ≠ (Q + 4 + 2 * 1) % k := by
      intro heq
      have he : Q + 4 + 2 * 1 = Q + 6 := by omega
      rw [he] at heq
      have h6 := mod_eq_imp_eq hd (by omega) heq
      omega
    rw [decide_eq_false hne] at hx
    dsimp only [wf]
    cases a : (rot k (2 * 1) w).testBit ((Q + d) % k) <;>
      cases b : (rot k (2 * 1) (flipBit k (Q + 4) w)).testBit ((Q + d) % k) <;> simp [a, b] at hx ⊢
  rw [stateAt_succ k c u 1 w, stateAt_succ k c u 1 wf,
      Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      hkey, testBit_step_Q hkpos, testBit_step_Q hkpos]
  have hm0 := hmix1 d hd
  have hm1 : (mix k (stateAt k c u 1 wf)).testBit ((Q + (d + 1)) % k) =
      xor (N (d + 1)) (decide (d = 4 ∨ d = 5 ∨ d = 6)) := by
    by_cases hlt : d + 1 < k
    · rw [hmix1 (d + 1) hlt]
      have hd1 : decide (d + 1 = 5 ∨ d + 1 = 6 ∨ d + 1 = 7) = decide (d = 4 ∨ d = 5 ∨ d = 6) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [hd1]
    · have he : (Q + (d + 1)) % k = (Q + 0) % k := by
        rw [show Q + (d + 1) = Q + 0 + k by omega, Nat.add_mod_right]
      have hn0 : N (d + 1) = N 0 := by dsimp only [N]; rw [he]
      rw [he, hmix1 0 hkpos, hn0]
      have hne : decide (d = 4 ∨ d = 5 ∨ d = 6) = false := by rw [decide_eq_false_iff_not]; omega
      rw [hne]; rfl
  have hm2 : (mix k (stateAt k c u 1 wf)).testBit ((Q + (d + 2)) % k) =
      xor (N (d + 2)) (decide (d = 3 ∨ d = 4 ∨ d = 5)) := by
    by_cases hlt : d + 2 < k
    · rw [hmix1 (d + 2) hlt]
      have hd2 : decide (d + 2 = 5 ∨ d + 2 = 6 ∨ d + 2 = 7) = decide (d = 3 ∨ d = 4 ∨ d = 5) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [hd2]
    · have he : (Q + (d + 2)) % k = (Q + (d + 2 - k)) % k := by
        rw [show Q + (d + 2) = Q + (d + 2 - k) + k by omega, Nat.add_mod_right]
      have hn2 : N (d + 2) = N (d + 2 - k) := by dsimp only [N]; rw [he]
      rw [he, hmix1 (d + 2 - k) (by omega), hn2]
      have hne1 : decide (d + 2 - k = 5 ∨ d + 2 - k = 6 ∨ d + 2 - k = 7) = false := by
        rw [decide_eq_false_iff_not]; omega
      have hne2 : decide (d = 3 ∨ d = 4 ∨ d = 5) = false := by
        rw [decide_eq_false_iff_not]; omega
      rw [hne1, hne2]
  rw [hm0, hm1, hm2]
  have hstep_eq : xor (N d) (!(N (d + 1)) && N (d + 2)) =
      xor (xor (N d) (decide (d = 5 ∨ d = 6 ∨ d = 7)))
        (!(xor (N (d + 1)) (decide (d = 4 ∨ d = 5 ∨ d = 6))) &&
          xor (N (d + 2)) (decide (d = 3 ∨ d = 4 ∨ d = 5))) := by
    by_cases h3 : d = 3
    · subst h3
      simp only [show ¬(3 = 5 ∨ 3 = 6 ∨ 3 = 7) by omega,
        show ¬(3 = 4 ∨ 3 = 5 ∨ 3 = 6) by omega, decide_false, Bool.xor_false]
      rw [hN4]
      simp
    · by_cases h4 : d = 4
      · subst h4
        simp only [show ¬(4 = 5 ∨ 4 = 6 ∨ 4 = 7) by omega, decide_false, Bool.xor_false]
        rw [hN56]
        cases N 4 <;> cases N 6 <;> rfl
      · simp only [show ¬(d = 5 ∨ d = 6 ∨ d = 7) by omega,
          show ¬(d = 4 ∨ d = 5 ∨ d = 6) by omega,
          show ¬(d = 3 ∨ d = 4 ∨ d = 5) by omega, decide_false, Bool.xor_false]
  change xor (xor (xor (N d) (!(N (d + 1)) && N (d + 2))) _) _ =
    xor (xor (xor (xor (N d) (decide (d = 5 ∨ d = 6 ∨ d = 7)))
      (!(xor (N (d + 1)) (decide (d = 4 ∨ d = 5 ∨ d = 6))) &&
        xor (N (d + 2)) (decide (d = 3 ∨ d = 4 ∨ d = 5)))) _) _
  rw [hstep_eq]

private theorem s2_diff_patB {k Q u w d : Nat} (c : Nat → Fin (2 ^ k))
    (hk : 11 ≤ k) (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hd : d < k)
    (h1 : ∀ j, j < k →
      xor ((stateAt k c u 1 w).testBit ((Q + j) % k))
        ((stateAt k c u 1 (flipBit k (Q + 4) w)).testBit ((Q + j) % k)) =
        decide (j = 4 ∨ j = 5 ∨ j = 6)) :
    let wf := flipBit k (Q + 4) w
    let N := fun j => (mix k (stateAt k c u 1 w)).testBit ((Q + j) % k)
    (d < 6 ∨ 8 ≤ d) →
    N 2 = true →
    N 4 = false →
    N 6 = false →
    (stateAt k c u 2 w).testBit ((Q + d) % k) = (stateAt k c u 2 wf).testBit ((Q + d) % k) := by
  intro wf N hrange hN2 hN4 hN6
  have hkpos : 0 < k := by omega
  have hs1 : stateAt k c u 1 w < 2 ^ k := stateAt_lt c hu 1 w
  have hs1f : stateAt k c u 1 wf < 2 ^ k := stateAt_lt c hu 1 wf
  have hmix1 : ∀ j, j < k →
      (mix k (stateAt k c u 1 wf)).testBit ((Q + j) % k) =
        xor (N j) (decide (j = 3 ∨ j = 5 ∨ j = 7)) := by
    intro j hj
    have hdiff : xor (N j) ((mix k (stateAt k c u 1 wf)).testBit ((Q + j) % k)) =
        decide (j = 3 ∨ j = 5 ∨ j = 7) := by
      dsimp only [N]
      rw [testBit_mix (by omega) hs1 (Nat.mod_lt _ hkpos),
          testBit_mix (by omega) hs1f (Nat.mod_lt _ hkpos)]
      have hrearr (a1 a2 b1 b2 c1 c2 : Bool) :
          xor (xor (xor a1 b1) c1) (xor (xor a2 b2) c2) =
            xor (xor (xor a1 a2) (xor b1 b2)) (xor c1 c2) := by
        cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases c1 <;> cases c2 <;> rfl
      rw [hrearr, h1 j hj]
      have hprev : xor ((stateAt k c u 1 w).testBit (((Q + j) % k + k - 1) % k))
          ((stateAt k c u 1 wf).testBit (((Q + j) % k + k - 1) % k)) =
          decide (j = 5 ∨ j = 6 ∨ j = 7) := by
        by_cases hj0 : j = 0
        · subst hj0
          have he : ((Q + 0) % k + k - 1) % k = (Q + (k - 1)) % k := by
            rw [show (Q + 0) % k + k - 1 = (Q + 0) % k + (k - 1) by omega, Nat.mod_add_mod, Nat.add_zero]
          rw [he, h1 (k - 1) (by omega)]
          have hne : decide (k - 1 = 4 ∨ k - 1 = 5 ∨ k - 1 = 6) = false := by
            rw [decide_eq_false_iff_not]; omega
          rw [hne]; rfl
        · rw [mod_Q_sub1 (by omega) (by omega), h1 (j - 1) (by omega)]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      have hnext : xor ((stateAt k c u 1 w).testBit (((Q + j) % k + 1) % k))
          ((stateAt k c u 1 wf).testBit (((Q + j) % k + 1) % k)) =
          decide (j = 3 ∨ j = 4 ∨ j = 5) := by
        rw [mod_Q_add]
        by_cases hjk : j + 1 < k
        · rw [h1 (j + 1) hjk]
          apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
        · have he : (Q + (j + 1)) % k = (Q + 0) % k := by
            rw [show Q + (j + 1) = Q + 0 + k by omega, Nat.add_mod_right]
          rw [he, h1 0 hkpos]
          simp [show ¬(j = 3 ∨ j = 4 ∨ j = 5) by omega]
      rw [hprev, hnext]
      by_cases h3 : j = 3
      · subst h3; rfl
      · by_cases h4 : j = 4
        · subst h4; rfl
        · by_cases h5 : j = 5
          · subst h5; rfl
          · by_cases h6 : j = 6
            · subst h6; rfl
            · by_cases h7 : j = 7
              · subst h7; rfl
              · simp [h3, h4, h5, h6, h7]
    rw [← hdiff]
    cases N j <;> cases (mix k (stateAt k c u 1 wf)).testBit ((Q + j) % k) <;> rfl
  have hkey : (rot k (2 * 1) w).testBit ((Q + d) % k) = (rot k (2 * 1) wf).testBit ((Q + d) % k) := by
    have hx := testBit_rot_xor_flip (s := 2 * 1) (pos := Q + 4) hkpos hw (Nat.mod_lt (Q + d) hkpos)
    have hne : (Q + d) % k ≠ (Q + 4 + 2 * 1) % k := by
      intro heq
      have he : Q + 4 + 2 * 1 = Q + 6 := by omega
      rw [he] at heq
      have h6 := mod_eq_imp_eq hd (by omega) heq
      omega
    rw [decide_eq_false hne] at hx
    dsimp only [wf]
    cases a : (rot k (2 * 1) w).testBit ((Q + d) % k) <;>
      cases b : (rot k (2 * 1) (flipBit k (Q + 4) w)).testBit ((Q + d) % k) <;> simp [a, b] at hx ⊢
  rw [stateAt_succ k c u 1 w, stateAt_succ k c u 1 wf,
      Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      hkey, testBit_step_Q hkpos, testBit_step_Q hkpos]
  have hm0 := hmix1 d hd
  have hm1 : (mix k (stateAt k c u 1 wf)).testBit ((Q + (d + 1)) % k) =
      xor (N (d + 1)) (decide (d = 2 ∨ d = 4 ∨ d = 6)) := by
    by_cases hlt : d + 1 < k
    · rw [hmix1 (d + 1) hlt]
      have hd1 : decide (d + 1 = 3 ∨ d + 1 = 5 ∨ d + 1 = 7) = decide (d = 2 ∨ d = 4 ∨ d = 6) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [hd1]
    · have he : (Q + (d + 1)) % k = (Q + 0) % k := by
        rw [show Q + (d + 1) = Q + 0 + k by omega, Nat.add_mod_right]
      have hn0 : N (d + 1) = N 0 := by dsimp only [N]; rw [he]
      rw [he, hmix1 0 hkpos, hn0]
      have hne : decide (d = 2 ∨ d = 4 ∨ d = 6) = false := by rw [decide_eq_false_iff_not]; omega
      rw [hne]; rfl
  have hm2 : (mix k (stateAt k c u 1 wf)).testBit ((Q + (d + 2)) % k) =
      xor (N (d + 2)) (decide (d = 1 ∨ d = 3 ∨ d = 5)) := by
    by_cases hlt : d + 2 < k
    · rw [hmix1 (d + 2) hlt]
      have hd2 : decide (d + 2 = 3 ∨ d + 2 = 5 ∨ d + 2 = 7) = decide (d = 1 ∨ d = 3 ∨ d = 5) := by
        apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
      rw [hd2]
    · have he : (Q + (d + 2)) % k = (Q + (d + 2 - k)) % k := by
        rw [show Q + (d + 2) = Q + (d + 2 - k) + k by omega, Nat.add_mod_right]
      have hn2 : N (d + 2) = N (d + 2 - k) := by dsimp only [N]; rw [he]
      rw [he, hmix1 (d + 2 - k) (by omega), hn2]
      have hne1 : decide (d + 2 - k = 3 ∨ d + 2 - k = 5 ∨ d + 2 - k = 7) = false := by
        rw [decide_eq_false_iff_not]; omega
      have hne2 : decide (d = 1 ∨ d = 3 ∨ d = 5) = false := by
        rw [decide_eq_false_iff_not]; omega
      rw [hne1, hne2]
  rw [hm0, hm1, hm2]
  have hstep_eq : xor (N d) (!(N (d + 1)) && N (d + 2)) =
      xor (xor (N d) (decide (d = 3 ∨ d = 5 ∨ d = 7)))
        (!(xor (N (d + 1)) (decide (d = 2 ∨ d = 4 ∨ d = 6))) &&
          xor (N (d + 2)) (decide (d = 1 ∨ d = 3 ∨ d = 5))) := by
    by_cases h1d : d = 1
    · subst h1d
      simp only [show ¬(1 = 3 ∨ 1 = 5 ∨ 1 = 7) by omega,
        show ¬(1 = 2 ∨ 1 = 4 ∨ 1 = 6) by omega, decide_false, Bool.xor_false]
      rw [hN2]; simp
    · by_cases h2d : d = 2
      · subst h2d
        simp only [show ¬(2 = 3 ∨ 2 = 5 ∨ 2 = 7) by omega,
          show ¬(2 = 1 ∨ 2 = 3 ∨ 2 = 5) by omega, decide_false, Bool.xor_false]
        rw [hN4]; simp
      · by_cases h3d : d = 3
        · subst h3d
          simp only [show ¬(3 = 2 ∨ 3 = 4 ∨ 3 = 6) by omega, decide_false, Bool.xor_false]
          rw [hN4]
          cases N 3 <;> cases N 5 <;> rfl
        · by_cases h4d : d = 4
          · subst h4d
            simp only [show ¬(4 = 3 ∨ 4 = 5 ∨ 4 = 7) by omega,
              show ¬(4 = 1 ∨ 4 = 3 ∨ 4 = 5) by omega, decide_false, Bool.xor_false]
            rw [hN6]; simp
          · by_cases h5d : d = 5
            · subst h5d
              simp only [show ¬(5 = 2 ∨ 5 = 4 ∨ 5 = 6) by omega, decide_false, Bool.xor_false]
              rw [hN6]
              cases N 5 <;> cases N 7 <;> rfl
            · simp only [show ¬(d = 3 ∨ d = 5 ∨ d = 7) by omega,
                show ¬(d = 2 ∨ d = 4 ∨ d = 6) by omega,
                show ¬(d = 1 ∨ d = 3 ∨ d = 5) by omega, decide_false, Bool.xor_false]
  change xor (xor (xor (N d) (!(N (d + 1)) && N (d + 2))) _) _ =
    xor (xor (xor (xor (N d) (decide (d = 3 ∨ d = 5 ∨ d = 7)))
      (!(xor (N (d + 1)) (decide (d = 2 ∨ d = 4 ∨ d = 6))) &&
        xor (N (d + 2)) (decide (d = 1 ∨ d = 3 ∨ d = 5)))) _) _
  rw [hstep_eq]

private theorem step_mix_congr_pos {k z₁ z₂ A j : Nat} (hk : 3 ≤ k)
    (hz₁ : z₁ < 2 ^ k) (hz₂ : z₂ < 2 ^ k) (hj : 1 ≤ j)
    (hm1 : z₁.testBit ((A + (j - 1)) % k) = z₂.testBit ((A + (j - 1)) % k))
    (h0 : z₁.testBit ((A + j) % k) = z₂.testBit ((A + j) % k))
    (h1 : z₁.testBit ((A + (j + 1)) % k) = z₂.testBit ((A + (j + 1)) % k))
    (h2 : z₁.testBit ((A + (j + 2)) % k) = z₂.testBit ((A + (j + 2)) % k))
    (h3 : z₁.testBit ((A + (j + 3)) % k) = z₂.testBit ((A + (j + 3)) % k)) :
    (step k (mix k z₁)).testBit ((A + j) % k) = (step k (mix k z₂)).testBit ((A + j) % k) := by
  have hkpos : 0 < k := by omega
  rw [testBit_step_Q hkpos, testBit_step_Q hkpos]
  rw [testBit_mix_Q (by omega) hz₁ hj, testBit_mix_Q (by omega) hz₂ hj]
  rw [testBit_mix_Q (by omega) hz₁ (by omega), testBit_mix_Q (by omega) hz₂ (by omega)]
  rw [testBit_mix_Q (by omega) hz₁ (by omega), testBit_mix_Q (by omega) hz₂ (by omega)]
  have e1 : j + 1 - 1 = j := by omega
  have e2 : j + 1 + 1 = j + 2 := by omega
  have e3 : j + 2 - 1 = j + 1 := by omega
  have e4 : j + 2 + 1 = j + 3 := by omega
  rw [e1, e2, e3, e4, hm1, h0, h1, h2, h3]

private theorem round2_implies_final_flip {k r e u i w : Nat} (c : Nat → Fin (2 ^ k))
    (hr : 4 ≤ r) (he4 : 4 ≤ e) (he6 : e ≤ 6) (hk : k + 3 + e = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k) (hw : w < 2 ^ k) :
    let q := i + 3 * r - e
    let wf := flipBit k (q - 1) w
    let left := (i + r * k + 2 - r) % k
    (∀ j, j ≤ 4 * (r - 2) →
      (stateAt k c u 2 w).testBit ((left + j) % k) =
        (stateAt k c u 2 wf).testBit ((left + j) % k)) →
    (stateAt k c u r wf).testBit i = !((stateAt k c u r w).testBit i) := by
  intro q wf left hagree2
  have hkpos : 0 < k := by omega
  have hk3 : 3 ≤ k := by omega
  have hleft_add : ∀ j, (left + j) % k = (i + r * k + 2 - r + j) % k := by
    intro j
    dsimp only [left]
    rw [Nat.mod_add_mod]
  have hprop : ∀ m, m < r - 2 → ∀ j, m ≤ j → j ≤ 4 * (r - 2) - 3 * m →
      (stateAt k c u (2 + m) w).testBit ((left + j) % k) =
        (stateAt k c u (2 + m) wf).testBit ((left + j) % k) := by
    intro m
    induction m with
    | zero =>
      intro _ j _ hj
      exact hagree2 j (by omega)
    | succ m ih =>
      intro hm j hjlo hjhi
      have hprev := ih (by omega)
      have hstep : (step k (mix k (stateAt k c u (2 + m) w))).testBit ((left + j) % k) =
          (step k (mix k (stateAt k c u (2 + m) wf))).testBit ((left + j) % k) := by
        apply step_mix_congr_pos hk3 (stateAt_lt c hu (2 + m) w) (stateAt_lt c hu (2 + m) wf) (by omega)
        · exact hprev (j - 1) (by omega) (by omega)
        · exact hprev j (by omega) (by omega)
        · exact hprev (j + 1) (by omega) (by omega)
        · exact hprev (j + 2) (by omega) (by omega)
        · exact hprev (j + 3) (by omega) (by omega)
      have hkey : (rot k (2 * (2 + m)) w).testBit ((left + j) % k) =
          (rot k (2 * (2 + m)) wf).testBit ((left + j) % k) := by
        have hx := testBit_rot_xor_flip (s := 2 * (2 + m)) (pos := q - 1) hkpos hw
          (Nat.mod_lt (left + j) hkpos)
        have hne : (left + j) % k ≠ (q - 1 + 2 * (2 + m)) % k := by
          rw [hleft_add]
          have hqeq : (q - 1 + 2 * (2 + m)) % k =
              (i + r * k + 2 - r + (4 * r + 2 * (2 + m) - e - 3)) % k := by
            have he : i + r * k + 2 - r + (4 * r + 2 * (2 + m) - e - 3) =
                (q - 1 + 2 * (2 + m)) + k * r := by
              dsimp only [q]
              have hrk : r ≤ r * k := Nat.le_mul_of_pos_right r hkpos
              rw [Nat.mul_comm k r]
              omega
            rw [he, Nat.add_mul_mod_self_left]
          rw [hqeq]
          exact mod_shift_ne (by omega) (by omega)
        rw [decide_eq_false hne] at hx
        dsimp only [wf]
        cases a : (rot k (2 * (2 + m)) w).testBit ((left + j) % k) <;>
          cases b : (rot k (2 * (2 + m)) (flipBit k (q - 1) w)).testBit ((left + j) % k) <;>
          simp [a, b] at hx ⊢
      have h2m : 2 + (m + 1) = (2 + m) + 1 := by omega
      rw [h2m, stateAt_succ, stateAt_succ, Nat.testBit_xor, Nat.testBit_xor,
          Nat.testBit_xor, Nat.testBit_xor, hstep, hkey]
  have hrm1 := hprop (r - 3) (by omega)
  have h2r : 2 + (r - 3) = r - 1 := by omega
  rw [h2r] at hrm1
  have hleft_i : (left + (r - 2)) % k = i := by
    rw [hleft_add]
    have hrk : r ≤ r * k := Nat.le_mul_of_pos_right r hkpos
    have he : i + r * k + 2 - r + (r - 2) = i + k * r := by
      rw [Nat.mul_comm k r]; omega
    rw [he, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  have hstep_r : (step k (mix k (stateAt k c u (r - 1) w))).testBit i =
      (step k (mix k (stateAt k c u (r - 1) wf))).testBit i := by
    rw [← hleft_i]
    apply step_mix_congr_pos hk3 (stateAt_lt c hu (r - 1) w) (stateAt_lt c hu (r - 1) wf) (by omega)
    · exact hrm1 (r - 2 - 1) (by omega) (by omega)
    · exact hrm1 (r - 2) (by omega) (by omega)
    · exact hrm1 (r - 2 + 1) (by omega) (by omega)
    · exact hrm1 (r - 2 + 2) (by omega) (by omega)
    · exact hrm1 (r - 2 + 3) (by omega) (by omega)
  have hkey_r : xor ((rot k (2 * (r - 1)) w).testBit i)
      ((rot k (2 * (r - 1)) wf).testBit i) = true := by
    rw [testBit_rot_xor_flip hkpos hw hi]
    have he : (q - 1 + 2 * (r - 1)) % k = i := by
      have h1 : q - 1 + 2 * (r - 1) = i + k := by dsimp only [q]; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    rw [he]; simp
  have hr_eq : r = (r - 1) + 1 := by omega
  conv_lhs => rw [hr_eq]
  conv_rhs => rw [hr_eq]
  rw [stateAt_succ, stateAt_succ, Nat.testBit_xor, Nat.testBit_xor,
      Nat.testBit_xor, Nat.testBit_xor, hstep_r]
  cases (step k (mix k (stateAt k c u (r - 1) wf))).testBit i <;>
    cases a : (rot k (2 * (r - 1)) w).testBit i <;>
    cases b : (rot k (2 * (r - 1)) wf).testBit i <;>
    cases (c (r - 1 + 1)).val.testBit i <;>
    simp [a, b] at hkey_r ⊢

private def valTrue (F : Nat → Bool) (z : Nat) (d : Nat) : Bool :=
  let b0 := z.testBit 0
  let b1 := z.testBit 1
  let b2 := z.testBit 2
  let b3 := z.testBit 3
  let b4 := z.testBit 4
  let x2 := !(xor b2 b3)
  let x6 := b2
  let x7 := b3
  let x8 := !(xor x6 x7)
  let x9 := xor x7 x8
  let x10 := xor (xor (xor x8 x9) (F 4)) (F 7)
  match d with
  | 0 => b0
  | 1 => b1
  | 2 => x2
  | 3 => b2
  | 4 => b3
  | 5 => b4
  | 6 => x6
  | 7 => x7
  | 8 => x8
  | 9 => x9
  | 10 => x10
  | d => z.testBit (d - 6)

private def valFalse (F : Nat → Bool) (z : Nat) (d : Nat) : Bool :=
  let b0 := z.testBit 0
  let b1 := z.testBit 1
  let b2 := z.testBit 2
  let b3 := z.testBit 3
  let x2 := !(xor b1 b2)
  let x0 := xor (xor (xor (xor b0 x2) (F 1)) (F 2)) (F 3)
  let x6 := b1
  let x7 := !b2
  let x8 := xor x6 x7
  let x9 := xor x7 x8
  let x10 := !(xor (xor (xor (xor x8 x9) (F 5)) (F 6)) (F 7))
  match d with
  | 0 => x0
  | 1 => b0
  | 2 => x2
  | 3 => b1
  | 4 => b2
  | 5 => b3
  | 6 => x6
  | 7 => x7
  | 8 => x8
  | 9 => x9
  | 10 => x10
  | d => z.testBit (d - 7)

private theorem valTrue_inj {k : Nat} (F : Nat → Bool) (hk : 11 ≤ k) {z₁ z₂ : Nat}
    (hz₁ : z₁ < 2 ^ (k - 6)) (hz₂ : z₂ < 2 ^ (k - 6))
    (heq : ∀ d, d < k → valTrue F z₁ d = valTrue F z₂ d) : z₁ = z₂ := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k - 6
  · by_cases h0 : j = 0
    · subst h0; exact heq 0 (by omega)
    · by_cases h1 : j = 1
      · subst h1; exact heq 1 (by omega)
      · by_cases h2 : j = 2
        · subst h2; exact heq 3 (by omega)
        · by_cases h3 : j = 3
          · subst h3; exact heq 4 (by omega)
          · by_cases h4 : j = 4
            · subst h4; exact heq 5 (by omega)
            · have hge : 11 ≤ j + 6 := by omega
              have h := heq (j + 6) (by omega)
              have hval : ∀ z, valTrue F z (j + 6) = z.testBit j := by
                intro z
                have hex : ∃ n, j + 6 = n + 11 := ⟨j - 5, by omega⟩
                rcases hex with ⟨n, hn⟩
                rw [hn]
                change z.testBit (n + 11 - 6) = z.testBit j
                congr 1; omega
              rw [hval z₁, hval z₂] at h
              exact h
  · have hpow := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k - 6 ≤ j)
    rw [Nat.testBit_lt_two_pow (hz₁.trans_le hpow), Nat.testBit_lt_two_pow (hz₂.trans_le hpow)]

private theorem valFalse_inj {k : Nat} (F : Nat → Bool) (hk : 11 ≤ k) {z₁ z₂ : Nat}
    (hz₁ : z₁ < 2 ^ (k - 7)) (hz₂ : z₂ < 2 ^ (k - 7))
    (heq : ∀ d, d < k → valFalse F z₁ d = valFalse F z₂ d) : z₁ = z₂ := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k - 7
  · by_cases h0 : j = 0
    · subst h0; exact heq 1 (by omega)
    · by_cases h1 : j = 1
      · subst h1; exact heq 3 (by omega)
      · by_cases h2 : j = 2
        · subst h2; exact heq 4 (by omega)
        · by_cases h3 : j = 3
          · subst h3; exact heq 5 (by omega)
          · have h := heq (j + 7) (by omega)
            have hval : ∀ z, valFalse F z (j + 7) = z.testBit j := by
              intro z
              have hex : ∃ n, j + 7 = n + 11 := ⟨j - 4, by omega⟩
              rcases hex with ⟨n, hn⟩
              rw [hn]
              change z.testBit (n + 11 - 7) = z.testBit j
              congr 1; omega
            rw [hval z₁, hval z₂] at h
            exact h
  · have hpow := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k - 7 ≤ j)
    rw [Nat.testBit_lt_two_pow (hz₁.trans_le hpow), Nat.testBit_lt_two_pow (hz₂.trans_le hpow)]

private theorem key_true_good {k r e u i z : Nat} (c : Nat → Fin (2 ^ k))
    (hr : 4 ≤ r) (he4 : 4 ≤ e) (he5 : e ≤ 5) (hk : k + 3 + e = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k) :
    let q := i + 3 * r - e
    let Q := q - 5
    let F := fun j => xor (u.testBit ((Q + j + 1) % k)) ((c 1).val.testBit ((Q + j) % k))
    let w := keyOf k u (buildWord k Q (valTrue F z))
    let wf := flipBit k (q - 1) w
    let left := (i + r * k + 2 - r) % k
    xor (xor (F 3) (F 4)) (F 5) = true →
    ∀ j, j ≤ 4 * (r - 2) →
      (stateAt k c u 2 w).testBit ((left + j) % k) =
        (stateAt k c u 2 wf).testBit ((left + j) % k) := by
  intro q Q F w wf left hpar j hj
  have hk11 : 11 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hQ5 : Q + 5 = q := by dsimp only [Q, q]; omega
  have hQ4 : Q + 4 = q - 1 := by dsimp only [Q, q]; omega
  have hs0_lt : buildWord k Q (valTrue F z) < 2 ^ k := buildWord_lt hkpos _
  have hw : w < 2 ^ k := keyOf_lt k u _
  have hs0 : stateAt k c u 0 w = buildWord k Q (valTrue F z) := stateAt_zero_keyOf c hk2 hu hs0_lt
  have hx : ∀ d, d < k → (stateAt k c u 0 w).testBit ((Q + d) % k) = valTrue F z d := by
    intro d hd
    rw [hs0, testBit_buildWord hd]
  let M := fun d => (mix k (stateAt k c u 0 w)).testBit ((Q + d) % k)
  have hM : ∀ d, 1 ≤ d → d + 1 < k →
      M d = xor (xor (valTrue F z d) (valTrue F z (d - 1))) (valTrue F z (d + 1)) := by
    intro d hd1 hd2
    dsimp only [M]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 0 w) hd1,
        hx d (by omega), hx (d - 1) (by omega), hx (d + 1) (by omega)]
  have hM3 : M 3 = true := by
    rw [hM 3 (by omega) (by omega)]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> rfl
  have hM45 : M 4 = M 5 := by
    rw [hM 4 (by omega) (by omega), hM 5 (by omega) (by omega)]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> cases z.testBit 4 <;> rfl
  have hM56 : M 5 = M 6 := by
    rw [hM 5 (by omega) (by omega), hM 6 (by omega) (by omega)]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> cases z.testBit 4 <;> rfl
  have hM7 : M 7 = true := by
    rw [hM 7 (by omega) (by omega)]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> rfl
  have hM8 : M 8 = false := by
    rw [hM 8 (by omega) (by omega)]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> rfl
  have hM9 : M 9 = xor (F 4) (F 7) := by
    rw [hM 9 (by omega) (by omega)]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> cases F 4 <;> cases F 7 <;> rfl
  have hs1d : ∀ d, d < k →
      xor ((stateAt k c u 1 w).testBit ((Q + d) % k))
        ((stateAt k c u 1 (flipBit k (Q + 4) w)).testBit ((Q + d) % k)) = decide (d = 6) := by
    intro d hd
    rw [s1_diff_Q c hk11 hu hw hd]
    change (if d = 2 then !(M 3)
      else if d = 3 then xor (M 4) (M 5)
      else if d = 4 then xor (M 5) (M 6)
      else if d = 5 then !(M 7)
      else if d = 6 then true
      else false) = decide (d = 6)
    rw [hM3, hM45, hM56, hM7]
    simp only [Bool.not_true, Bool.xor_self]
    by_cases h2 : d = 2
    · subst h2; rfl
    · by_cases h3 : d = 3
      · subst h3; rfl
      · by_cases h4 : d = 4
        · subst h4; rfl
        · by_cases h5 : d = 5
          · subst h5; rfl
          · by_cases h6 : d = 6
            · subst h6; rfl
            · simp [h2, h3, h4, h5, h6]
  have hs1b : ∀ d, 1 ≤ d → d < k →
      (stateAt k c u 1 w).testBit ((Q + d) % k) =
        xor (xor (xor (valTrue F z (d - 1)) (valTrue F z d)) (!(M (d + 1)) && M (d + 2))) (F d) := by
    intro d hd1 hdk
    rw [s1_bit_Q c hk2 hu hw hd1]
    dsimp only
    rw [hx (d - 1) (by omega), hx d hdk]
  let N := fun d => (mix k (stateAt k c u 1 w)).testBit ((Q + d) % k)
  have hN4 : N 4 = true := by
    dsimp only [N]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 1 w) (by omega),
        hs1b 4 (by omega) (by omega), hs1b 3 (by omega) (by omega), hs1b 5 (by omega) (by omega)]
    rw [hM45, hM56, hM7]
    have hM6v : M 6 = xor (xor (valTrue F z 6) (valTrue F z 5)) (valTrue F z 7) :=
      hM 6 (by omega) (by omega)
    rw [hM6v]
    dsimp only [valTrue]
    cases z.testBit 2 <;> cases z.testBit 3 <;> cases z.testBit 4 <;>
      cases h3 : F 3 <;> cases h4 : F 4 <;> cases h5 : F 5 <;>
      simp [h3, h4, h5] at hpar ⊢
  have hN56 : N 5 = N 6 := by
    dsimp only [N]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 1 w) (by omega),
        testBit_mix_Q hk2 (stateAt_lt c hu 1 w) (by omega)]
    have h47 : (stateAt k c u 1 w).testBit ((Q + 4) % k) =
        (stateAt k c u 1 w).testBit ((Q + 7) % k) := by
      rw [hs1b 4 (by omega) (by omega), hs1b 7 (by omega) (by omega)]
      rw [hM56, hM8, hM9]
      dsimp only [valTrue]
      cases z.testBit 2 <;> cases z.testBit 3 <;> cases M 6 <;> cases F 4 <;> cases F 7 <;> rfl
    have he1 : 5 - 1 = 4 := rfl
    have he2 : 5 + 1 = 6 := rfl
    have he3 : 6 - 1 = 5 := rfl
    have he4 : 6 + 1 = 7 := rfl
    rw [he1, he2, he3, he4, h47]
    cases (stateAt k c u 1 w).testBit ((Q + 5) % k) <;>
      cases (stateAt k c u 1 w).testBit ((Q + 6) % k) <;>
      cases (stateAt k c u 1 w).testBit ((Q + 7) % k) <;> rfl
  have hleft_Q : (left + j) % k = (Q + ((r + 4 + j) % k)) % k := by
    dsimp only [left]
    rw [Nat.mod_add_mod, Nat.add_mod_mod]
    have hrk : r ≤ r * k := Nat.le_mul_of_pos_right r hkpos
    have hkrk : k ≤ r * k := Nat.le_mul_of_pos_left k (by omega)
    have he : i + r * k + 2 - r + j = Q + (r + 4 + j) + k * (r - 1) := by
      have hmul : k * (r - 1) = r * k - k := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm]
      dsimp only [Q, q]
      rw [hmul]
      omega
    rw [he, Nat.add_mul_mod_self_left]
  rw [hleft_Q]
  have hwf : wf = flipBit k (Q + 4) w := by dsimp only [wf]; rw [hQ4]
  rw [hwf]
  have hd_range : (r + 4 + j) % k < 5 ∨ 8 ≤ (r + 4 + j) % k := by
    by_cases hlt : r + 4 + j < k
    · right; rw [Nat.mod_eq_of_lt hlt]; omega
    · left
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  exact s2_diff_patA c hk11 hu hw (Nat.mod_lt _ hkpos) hs1d hd_range hN4 hN56

private theorem key_false_good {k r e u i z : Nat} (c : Nat → Fin (2 ^ k))
    (hr : 4 ≤ r) (he4 : 4 ≤ e) (he6 : e ≤ 6) (hk : k + 3 + e = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k) :
    let q := i + 3 * r - e
    let Q := q - 5
    let F := fun j => xor (u.testBit ((Q + j + 1) % k)) ((c 1).val.testBit ((Q + j) % k))
    let w := keyOf k u (buildWord k Q (valFalse F z))
    let wf := flipBit k (q - 1) w
    let left := (i + r * k + 2 - r) % k
    xor (xor (F 3) (F 4)) (F 5) = false →
    ∀ j, j ≤ 4 * (r - 2) →
      (stateAt k c u 2 w).testBit ((left + j) % k) =
        (stateAt k c u 2 wf).testBit ((left + j) % k) := by
  intro q Q F w wf left hpar j hj
  have hk11 : 11 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hQ4 : Q + 4 = q - 1 := by dsimp only [Q, q]; omega
  have hs0_lt : buildWord k Q (valFalse F z) < 2 ^ k := buildWord_lt hkpos _
  have hw : w < 2 ^ k := keyOf_lt k u _
  have hs0 : stateAt k c u 0 w = buildWord k Q (valFalse F z) := stateAt_zero_keyOf c hk2 hu hs0_lt
  have hx : ∀ d, d < k → (stateAt k c u 0 w).testBit ((Q + d) % k) = valFalse F z d := by
    intro d hd
    rw [hs0, testBit_buildWord hd]
  let M := fun d => (mix k (stateAt k c u 0 w)).testBit ((Q + d) % k)
  have hM : ∀ d, 1 ≤ d → d + 1 < k →
      M d = xor (xor (valFalse F z d) (valFalse F z (d - 1))) (valFalse F z (d + 1)) := by
    intro d hd1 hd2
    dsimp only [M]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 0 w) hd1,
        hx d (by omega), hx (d - 1) (by omega), hx (d + 1) (by omega)]
  have hM2 : M 2 = xor (xor (valFalse F z 1) (valFalse F z 2)) (valFalse F z 3) := by
    rw [hM 2 (by omega) (by omega)]
    cases valFalse F z 1 <;> cases valFalse F z 2 <;> cases valFalse F z 3 <;> rfl
  have hM3 : M 3 = true := by
    rw [hM 3 (by omega) (by omega)]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> rfl
  have hM45 : M 4 = M 5 := by
    rw [hM 4 (by omega) (by omega), hM 5 (by omega) (by omega)]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> cases z.testBit 3 <;> rfl
  have hM6 : M 6 = !(M 5) := by
    rw [hM 5 (by omega) (by omega), hM 6 (by omega) (by omega)]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> cases z.testBit 3 <;> rfl
  have hM7 : M 7 = false := by
    rw [hM 7 (by omega) (by omega)]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> rfl
  have hM8 : M 8 = false := by
    rw [hM 8 (by omega) (by omega)]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> rfl
  have hM9 : M 9 = !(xor (xor (F 5) (F 6)) (F 7)) := by
    rw [hM 9 (by omega) (by omega)]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> cases F 5 <;> cases F 6 <;> cases F 7 <;> rfl
  have hs1d : ∀ d, d < k →
      xor ((stateAt k c u 1 w).testBit ((Q + d) % k))
        ((stateAt k c u 1 (flipBit k (Q + 4) w)).testBit ((Q + d) % k)) =
        decide (d = 4 ∨ d = 5 ∨ d = 6) := by
    intro d hd
    rw [s1_diff_Q c hk11 hu hw hd]
    change (if d = 2 then !(M 3)
      else if d = 3 then xor (M 4) (M 5)
      else if d = 4 then xor (M 5) (M 6)
      else if d = 5 then !(M 7)
      else if d = 6 then true
      else false) = decide (d = 4 ∨ d = 5 ∨ d = 6)
    rw [hM3, hM45, hM6, hM7]
    have hxn : xor (M 5) (!(M 5)) = true := by cases M 5 <;> rfl
    rw [hxn]
    simp only [Bool.not_true, Bool.not_false, Bool.xor_self]
    by_cases h2 : d = 2
    · subst h2; rfl
    · by_cases h3 : d = 3
      · subst h3; rfl
      · by_cases h4 : d = 4
        · subst h4; rfl
        · by_cases h5 : d = 5
          · subst h5; rfl
          · by_cases h6 : d = 6
            · subst h6; rfl
            · simp [h2, h3, h4, h5, h6]
  have hs1b : ∀ d, 1 ≤ d → d < k →
      (stateAt k c u 1 w).testBit ((Q + d) % k) =
        xor (xor (xor (valFalse F z (d - 1)) (valFalse F z d)) (!(M (d + 1)) && M (d + 2))) (F d) := by
    intro d hd1 hdk
    rw [s1_bit_Q c hk2 hu hw hd1]
    dsimp only
    rw [hx (d - 1) (by omega), hx d hdk]
  let N := fun d => (mix k (stateAt k c u 1 w)).testBit ((Q + d) % k)
  have hN2 : N 2 = true := by
    dsimp only [N]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 1 w) (by omega),
        hs1b 2 (by omega) (by omega), hs1b 1 (by omega) (by omega), hs1b 3 (by omega) (by omega)]
    rw [hM2, hM3, hM45]
    dsimp only [valFalse]
    cases z.testBit 0 <;> cases z.testBit 1 <;> cases z.testBit 2 <;>
      cases M 5 <;> cases F 1 <;> cases F 2 <;> cases F 3 <;> rfl
  have hN4 : N 4 = false := by
    dsimp only [N]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 1 w) (by omega),
        hs1b 4 (by omega) (by omega), hs1b 3 (by omega) (by omega), hs1b 5 (by omega) (by omega)]
    rw [hM45, hM6, hM7]
    have hM5v : M 5 = xor (xor (valFalse F z 4) (valFalse F z 3)) (valFalse F z 5) := by
      rw [← hM45, hM 4 (by omega) (by omega)]
    rw [hM5v]
    dsimp only [valFalse]
    cases z.testBit 1 <;> cases z.testBit 2 <;> cases z.testBit 3 <;>
      cases h3 : F 3 <;> cases h4 : F 4 <;> cases h5 : F 5 <;>
      simp [h3, h4, h5] at hpar ⊢
  have hN6 : N 6 = false := by
    dsimp only [N]
    rw [testBit_mix_Q hk2 (stateAt_lt c hu 1 w) (by omega),
        hs1b 6 (by omega) (by omega), hs1b 5 (by omega) (by omega), hs1b 7 (by omega) (by omega)]
    rw [hM7, hM8, hM9]
    dsimp only [valFalse]
    cases M 6 <;> cases z.testBit 1 <;> cases z.testBit 2 <;> cases z.testBit 3 <;>
      cases F 5 <;> cases F 6 <;> cases F 7 <;> rfl
  have hleft_Q : (left + j) % k = (Q + ((r + 4 + j) % k)) % k := by
    dsimp only [left]
    rw [Nat.mod_add_mod, Nat.add_mod_mod]
    have hrk : r ≤ r * k := Nat.le_mul_of_pos_right r hkpos
    have hkrk : k ≤ r * k := Nat.le_mul_of_pos_left k (by omega)
    have he : i + r * k + 2 - r + j = Q + (r + 4 + j) + k * (r - 1) := by
      have hmul : k * (r - 1) = r * k - k := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm]
      dsimp only [Q, q]
      rw [hmul]
      omega
    rw [he, Nat.add_mul_mod_self_left]
  rw [hleft_Q]
  have hwf : wf = flipBit k (Q + 4) w := by dsimp only [wf]; rw [hQ4]
  rw [hwf]
  have hd_range : (r + 4 + j) % k < 6 ∨ 8 ≤ (r + 4 + j) % k := by
    by_cases hlt : r + 4 + j < k
    · right; rw [Nat.mod_eq_of_lt hlt]; omega
    · left
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  exact s2_diff_patB c hk11 hu hw (Nat.mod_lt _ hkpos) hs1d hd_range hN2 hN4 hN6

private theorem count_le_filter_range {N M : Nat} (p : Nat → Bool) (f : Nat → Nat)
    (hlt : ∀ z, z < N → f z < M)
    (hp : ∀ z, z < N → p (f z) = true)
    (hinj : ∀ z₁ z₂, z₁ < N → z₂ < N → f z₁ = f z₂ → z₁ = z₂) :
    N ≤ ((List.range M).filter p).length := by
  have hnodup_map : ((List.range N).map f).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro z₁ hz₁ z₂ hz₂ hf
    exact hinj z₁ z₂ (List.mem_range.mp hz₁) (List.mem_range.mp hz₂) hf
  have hnodup_flt : ((List.range M).filter p).Nodup :=
    List.nodup_range.filter p
  have hsub : ((List.range N).map f).toFinset ⊆ ((List.range M).filter p).toFinset := by
    intro w hw
    rw [List.mem_toFinset, List.mem_map] at hw
    rcases hw with ⟨z, hz, rfl⟩
    have hzlt : z < N := List.mem_range.mp hz
    rw [List.mem_toFinset, List.mem_filter, List.mem_range]
    exact ⟨hlt z hzlt, hp z hzlt⟩
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup_map, List.toFinset_card_of_nodup hnodup_flt,
      List.length_map, List.length_range] at hcard
  exact hcard

private theorem main (k r e : Nat) (hr : 4 ≤ r) (he4 : 4 ≤ e) (he6 : e ≤ 6)
    (hk : k + 3 + e = 5 * r) (c : Nat → Fin (2 ^ k)) (u i : Nat) (hu : u < 2 ^ k) (hi : i < k) :
    let rot0 := fun (s word : Nat) =>
      ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
    let step0 := fun (word : Nat) =>
      (List.range k).foldl (fun acc b =>
        acc ||| ((xor (word.testBit b)
          (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
    let state := fun (rounds key : Nat) =>
      (List.range rounds).foldl (fun prev t =>
        step0 (prev ^^^ rot0 1 prev ^^^ rot0 (k - 1) prev) ^^^ rot0 (2 * t) key ^^^
          (c (t + 1)).val) (rot0 1 key ^^^ u)
    let q := i + 3 * r - e
    let fixed := fun (position : Nat) =>
      xor (u.testBit ((position + 1) % k)) ((c 1).val.testBit (position % k))
    let parity := xor (xor (fixed (q - 2)) (fixed (q - 1))) (fixed q)
    let mate := fun (key : Nat) => key ^^^ (1 <<< ((q - 1) % k))
    let left := (i + r * k + 2 - r) % k
    let good := fun (w : Nat) =>
      let a := state 2 w
      let b := state 2 (mate w)
      (List.range (4 * (r - 2) + 1)).all (fun j =>
        a.testBit ((left + j) % k) == b.testBit ((left + j) % k)) &&
      ((state r (mate w)).testBit i == !((state r w).testBit i))
    (e ≤ 5 ∨ parity = false) →
    2 ^ (k - (if parity then 6 else 7)) ≤ ((List.range (2 ^ k)).filter good).length := by
  intro rot0 step0 state q fixed parity mate left good hcond
  have hk11 : 11 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  let Q := q - 5
  let F := fun j => xor (u.testBit ((Q + j + 1) % k)) ((c 1).val.testBit ((Q + j) % k))
  have hFpar : xor (xor (F 3) (F 4)) (F 5) = parity := by
    dsimp only [parity, fixed, F, Q, q]
    have e3 : i + 3 * r - e - 5 + 3 = i + 3 * r - e - 2 := by omega
    have e4 : i + 3 * r - e - 5 + 4 = i + 3 * r - e - 1 := by omega
    have e5 : i + 3 * r - e - 5 + 5 = i + 3 * r - e := by omega
    rw [e3, e4, e5]
  have hgood_of : ∀ w, w < 2 ^ k →
      (∀ j, j ≤ 4 * (r - 2) →
        (stateAt k c u 2 w).testBit ((left + j) % k) =
          (stateAt k c u 2 (flipBit k (q - 1) w)).testBit ((left + j) % k)) →
      good w = true := by
    intro w hw hag
    have hflip := round2_implies_final_flip c hr he4 he6 hk hu hi hw hag
    dsimp only [good]
    rw [Bool.and_eq_true, List.all_eq_true]
    constructor
    · intro j hj
      have hjle : j ≤ 4 * (r - 2) := by
        have := List.mem_range.mp hj
        omega
      change ((stateAt k c u 2 w).testBit ((left + j) % k) ==
        (stateAt k c u 2 (flipBit k (q - 1) w)).testBit ((left + j) % k)) = true
      rw [hag j hjle]
      simp
    · change ((stateAt k c u r (flipBit k (q - 1) w)).testBit i ==
        !((stateAt k c u r w).testBit i)) = true
      rw [hflip]
      simp
  cases hp : parity with
  | true =>
    simp only [↓reduceIte]
    have he5 : e ≤ 5 := by
      rcases hcond with h5 | hf
      · exact h5
      · rw [hp] at hf; cases hf
    have hFpar' : xor (xor (F 3) (F 4)) (F 5) = true := hFpar.trans hp
    apply count_le_filter_range good (fun z => keyOf k u (buildWord k Q (valTrue F z)))
    · intro z _; exact keyOf_lt k u _
    · intro z _
      apply hgood_of _ (keyOf_lt k u _)
      exact key_true_good c hr he4 he5 hk hu hi hFpar'
    · intro z₁ z₂ hz₁ hz₂ heq
      have hs0_eq : buildWord k Q (valTrue F z₁) = buildWord k Q (valTrue F z₂) := by
        have h1 := stateAt_zero_keyOf c hk2 hu (buildWord_lt (Q := Q) hkpos (valTrue F z₁))
        have h2 := stateAt_zero_keyOf c hk2 hu (buildWord_lt (Q := Q) hkpos (valTrue F z₂))
        rw [heq] at h1
        exact h1.symm.trans h2
      apply valTrue_inj F hk11 hz₁ hz₂
      intro d hd
      rw [← testBit_buildWord hd (valTrue F z₁), ← testBit_buildWord hd (valTrue F z₂), hs0_eq]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hFpar' : xor (xor (F 3) (F 4)) (F 5) = false := hFpar.trans hp
    apply count_le_filter_range good (fun z => keyOf k u (buildWord k Q (valFalse F z)))
    · intro z _; exact keyOf_lt k u _
    · intro z _
      apply hgood_of _ (keyOf_lt k u _)
      exact key_false_good c hr he4 he6 hk hu hi hFpar'
    · intro z₁ z₂ hz₁ hz₂ heq
      have hs0_eq : buildWord k Q (valFalse F z₁) = buildWord k Q (valFalse F z₂) := by
        have h1 := stateAt_zero_keyOf c hk2 hu (buildWord_lt (Q := Q) hkpos (valFalse F z₁))
        have h2 := stateAt_zero_keyOf c hk2 hu (buildWord_lt (Q := Q) hkpos (valFalse F z₂))
        rw [heq] at h1
        exact h1.symm.trans h2
      apply valFalse_inj F hk11 hz₁ hz₂
      intro d hd
      rw [← testBit_buildWord hd (valFalse F z₁), ← testBit_buildWord hd (valFalse F z₂), hs0_eq]

end PEqualNP.Outside.L_meta_25528_aux

theorem PEqualNP.Outside.L_meta_25528 :
∀ (k r e : Nat), 4 ≤ r → 4 ≤ e → e ≤ 6 → k + 3 + e = 5 * r →
  ∀ (c : Nat → Fin (2 ^ k)) (u i : Nat), u < 2 ^ k → i < k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (rounds key : Nat) =>
    (List.range rounds).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (c (t + 1)).val) (rot 1 key ^^^ u)
  let q := i + 3 * r - e
  let fixed := fun (position : Nat) =>
    xor (u.testBit ((position + 1) % k)) ((c 1).val.testBit (position % k))
  let parity := xor (xor (fixed (q - 2)) (fixed (q - 1))) (fixed q)
  let mate := fun (key : Nat) => key ^^^ (1 <<< ((q - 1) % k))
  let left := (i + r * k + 2 - r) % k
  let good := fun (w : Nat) =>
    let a := state 2 w
    let b := state 2 (mate w)
    (List.range (4 * (r - 2) + 1)).all (fun j =>
      a.testBit ((left + j) % k) == b.testBit ((left + j) % k)) &&
    ((state r (mate w)).testBit i == !((state r w).testBit i))
  (e ≤ 5 ∨ parity = false) →
  2 ^ (k - (if parity then 6 else 7)) ≤ ((List.range (2 ^ k)).filter good).length :=
  PEqualNP.Outside.L_meta_25528_aux.main
