import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25515_aux

private def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word b : Nat) : Bool :=
  xor (word.testBit b) (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))

private def wordStep (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc b => if stepBit k word b then acc ||| 2 ^ b else acc) 0

private def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

private def stateRec (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key : Nat) : Nat → Nat
  | 0 => rot k 1 key ^^^ u
  | t + 1 =>
      let prev := stateRec k constants u key t
      wordStep k (mix k prev) ^^^ rot k (2 * t) key ^^^ (constants (t + 1)).val

private def preWord (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key t : Nat) : Nat :=
  wordStep k (mix k (stateRec k constants u key (t - 1)))

private def waveWord (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u key t : Nat) : Nat :=
  if t < r then stateRec k constants u key t else preWord k constants u key r

private def pos (k r i t δ : Nat) : Nat :=
  (i + 3 * (r - t) + k - δ) % k

private def maxSat (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => if p (n + 1) then n + 1 else maxSat p n

private theorem maxSat_le (p : Nat → Bool) (m : Nat) : maxSat p m ≤ m := by
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    simp only [maxSat]
    cases p (m + 1)
    · exact Nat.le_trans ih (Nat.le_succ m)
    · exact Nat.le_refl (m + 1)

private theorem maxSat_spec (p : Nat → Bool) (m : Nat) (h : ∃ δ, δ ≤ m ∧ p δ = true) :
    p (maxSat p m) = true := by
  induction m with
  | zero =>
    rcases h with ⟨δ, hδ, hp⟩
    have h0 : δ = 0 := by omega
    subst h0
    exact hp
  | succ m ih =>
    simp only [maxSat]
    cases hp1 : p (m + 1) with
    | true => exact hp1
    | false =>
      apply ih
      rcases h with ⟨δ, hδ, hp⟩
      refine ⟨δ, ?_, hp⟩
      by_cases heq : δ = m + 1
      · subst heq
        rw [hp1] at hp
        cases hp
      · omega

private theorem le_maxSat (p : Nat → Bool) (m δ : Nat) (hδ : δ ≤ m) (hp : p δ = true) :
    δ ≤ maxSat p m := by
  induction m with
  | zero => omega
  | succ m ih =>
    simp only [maxSat]
    cases hp1 : p (m + 1) with
    | true => exact hδ
    | false =>
      apply ih
      by_cases heq : δ = m + 1
      · subst heq
        rw [hp1] at hp
        cases hp
      · omega

private theorem lt_two_pow_of_bits {n k : Nat} (h : ∀ j, k ≤ j → n.testBit j = false) :
    n < 2 ^ k := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [h j (Nat.zero_le j), Nat.zero_testBit]
    rw [hn]
    exact Nat.zero_lt_one
  | succ k ih =>
    have hdiv : n / 2 < 2 ^ k := by
      apply ih
      intro j hj
      rw [← Nat.testBit_succ]
      exact h (j + 1) (Nat.succ_le_succ hj)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega

private theorem testBit_foldl_set (p : Nat → Bool) (xs : List Nat) (acc j : Nat) :
    (xs.foldl (fun a b => if p b then a ||| 2 ^ b else a) acc).testBit j =
      (acc.testBit j || (decide (j ∈ xs) && p j)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases hbj : b = j
    · subst b
      cases p j <;> simp
    · cases p b <;> simp [hbj, Ne.symm hbj]

private theorem testBit_wordStep_all (k word j : Nat) :
    (wordStep k word).testBit j = (decide (j < k) && stepBit k word j) := by
  simp only [wordStep, testBit_foldl_set, Nat.zero_testBit, Bool.false_or, List.mem_range]

private theorem testBit_wordStep {k word j : Nat} (hj : j < k) :
    (wordStep k word).testBit j =
      xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k)) := by
  simp [testBit_wordStep_all, stepBit, hj]

private theorem wordStep_lt (k word : Nat) : wordStep k word < 2 ^ k := by
  apply lt_two_pow_of_bits
  intro j hj
  simp [testBit_wordStep_all, Nat.not_lt_of_ge hj]

private theorem wordStep_eq (k word : Nat) :
    wordStep k word = (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0 := by
  unfold wordStep
  congr 1
  funext a b
  change (if stepBit k word b then a ||| 2 ^ b else a) =
    a ||| ((stepBit k word b).toNat <<< b)
  cases stepBit k word b <;> simp [Nat.shiftLeft_eq]

private theorem rot_lt {k s w : Nat} : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem lt_xor {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ b < 2 ^ k := by
  apply lt_two_pow_of_bits
  intro j hj
  have hm : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hm),
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hm)]

private theorem bit_rot {k s w j : Nat} (hw : w < 2 ^ k) (hj : j < k) :
    (rot k s w).testBit j = w.testBit ((j + k - s % k) % k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  simp only [rot, Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ j
  · have hz : w.testBit (k - s % k + j) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega)))
    have he : (j + k - s % k) % k = j - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ j + k - s % k), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (j + k - s % k) % k = k - s % k + j := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

private theorem stateRec_lt {k : Nat} (constants : Nat → Fin (2 ^ k)) {u key : Nat}
    (hu : u < 2 ^ k) (t : Nat) : stateRec k constants u key t < 2 ^ k := by
  cases t with
  | zero => exact lt_xor rot_lt hu
  | succ t => exact lt_xor (lt_xor (wordStep_lt _ _) rot_lt) (constants (t + 1)).isLt

private theorem round_fold {α : Type*} (f : Nat → α) (op : α → Nat → α)
    (hf : ∀ j, f (j + 1) = op (f j) j) (t : Nat) :
    (List.range t).foldl op (f 0) = f t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, hf]

private theorem stateRec_eq_fold (k : Nat) (constants : Nat → Fin (2 ^ k)) (u key rounds : Nat) :
    (List.range rounds).foldl (fun prev t =>
      wordStep k (mix k prev) ^^^ rot k (2 * t) key ^^^ (constants (t + 1)).val)
      (rot k 1 key ^^^ u) = stateRec k constants u key rounds := by
  exact round_fold (stateRec k constants u key) _ (fun _ => rfl) rounds

private theorem mod_add_cancel_right {k a b c : Nat} (h : (a + c) % k = (b + c) % k) :
    a % k = b % k := by
  by_cases hk : k = 0
  · subst hk
    simp only [Nat.mod_zero] at h ⊢
    omega
  · have hpos : 0 < k := Nat.pos_of_ne_zero hk
    set x := a % k
    set y := b % k
    set z := c % k
    have hx : x < k := Nat.mod_lt a hpos
    have hy : y < k := Nat.mod_lt b hpos
    have hz : z < k := Nat.mod_lt c hpos
    have h1 : (x + z) % k = (y + z) % k := by
      rw [← Nat.add_mod, ← Nat.add_mod]
      exact h
    by_cases hca : x + z < k
    · by_cases hcb : y + z < k
      · rw [Nat.mod_eq_of_lt hca, Nat.mod_eq_of_lt hcb] at h1
        omega
      · rw [Nat.mod_eq_of_lt hca, Nat.mod_eq_sub_mod (by omega : k ≤ y + z),
            Nat.mod_eq_of_lt (by omega : y + z - k < k)] at h1
        omega
    · by_cases hcb : y + z < k
      · rw [Nat.mod_eq_sub_mod (by omega : k ≤ x + z),
            Nat.mod_eq_of_lt (by omega : x + z - k < k), Nat.mod_eq_of_lt hcb] at h1
        omega
      · rw [Nat.mod_eq_sub_mod (by omega : k ≤ x + z),
            Nat.mod_eq_of_lt (by omega : x + z - k < k),
            Nat.mod_eq_sub_mod (by omega : k ≤ y + z),
            Nat.mod_eq_of_lt (by omega : y + z - k < k)] at h1
        omega

private theorem mod_ne_between {k m n : Nat} (hm : m < k) (h1 : m < n) (h2 : n < k + m) :
    n % k ≠ m % k := by
  rw [Nat.mod_eq_of_lt hm]
  by_cases hlt : n < k
  · rw [Nat.mod_eq_of_lt hlt]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem mod_ne_of_lt_add {k a b : Nat} (h1 : a < b) (h2 : b < a + k) :
    b % k ≠ a % k := by
  intro heq
  have hsub : ((b - a) + a) % k = (0 + a) % k := by
    have he1 : b - a + a = b := by omega
    rw [he1, Nat.zero_add]
    exact heq
  have h0 : (b - a) % k = 0 % k := mod_add_cancel_right hsub
  rw [Nat.mod_eq_of_lt (by omega : b - a < k), Nat.zero_mod] at h0
  omega

private theorem bit_mix {k w j : Nat} (hk : 2 ≤ k) (hw : w < 2 ^ k) (hj : j < k) :
    (mix k w).testBit j =
      xor (xor (w.testBit j) (w.testBit ((j + k - 1) % k))) (w.testBit ((j + 1) % k)) := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  have h3 : (j + k - (k - 1)) % k = (j + 1) % k := by
    have he : j + k - (k - 1) = j + 1 := by omega
    rw [he]
  simp only [mix, Nat.testBit_xor, bit_rot hw hj, h1, h2, h3]

private theorem sub1_add_mod {k p m : Nat} (hk : 2 ≤ k) (hm : 1 ≤ m) :
    ((p + m) % k + k - 1) % k = (p + (m - 1)) % k := by
  apply mod_add_cancel_right (c := 1)
  have h1 : (p + m) % k + k - 1 + 1 = (p + m) % k + k := by omega
  have h2 : p + (m - 1) + 1 = p + m := by omega
  rw [h1, h2, Nat.add_mod_right, Nat.mod_mod]

private theorem add_mod_add_mod {k a b : Nat} : ((a % k) + b) % k = (a + b) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem sub_mod_shift {k x s : Nat} (hk : 0 < k) (hsx : s ≤ x) :
    (x % k + k - s % k) % k = (x - s) % k := by
  have hs : s % k < k := Nat.mod_lt s hk
  apply mod_add_cancel_right (c := s)
  have h1 : (x - s) + s = x := by omega
  rw [h1]
  have h2 : (x % k + k - s % k + s) % k = (x % k + k - s % k + s % k) % k := by
    rw [Nat.add_mod (x % k + k - s % k) s, Nat.add_mod (x % k + k - s % k) (s % k), Nat.mod_mod s k]
  rw [h2]
  have h3 : x % k + k - s % k + s % k = x % k + k := by omega
  rw [h3, Nat.add_mod_right, Nat.mod_mod]

private theorem step_mix_congr {k z₁ z₂ p : Nat} (hk : 3 ≤ k)
    (hz1 : z₁ < 2 ^ k) (hz2 : z₂ < 2 ^ k) (hp : p < k)
    (hm1 : z₁.testBit ((p + k - 1) % k) = z₂.testBit ((p + k - 1) % k))
    (h0 : z₁.testBit p = z₂.testBit p)
    (h1 : z₁.testBit ((p + 1) % k) = z₂.testBit ((p + 1) % k))
    (h2 : z₁.testBit ((p + 2) % k) = z₂.testBit ((p + 2) % k))
    (h3 : z₁.testBit ((p + 3) % k) = z₂.testBit ((p + 3) % k)) :
    (wordStep k (mix k z₁)).testBit p = (wordStep k (mix k z₂)).testBit p := by
  have hp1 : (p + 1) % k < k := Nat.mod_lt _ (by omega)
  have hp2 : (p + 2) % k < k := Nat.mod_lt _ (by omega)
  have h1m : ((p + 1) % k + k - 1) % k = p := by
    rw [sub1_add_mod (by omega) (by omega)]
    simp [Nat.mod_eq_of_lt hp]
  have h1p : ((p + 1) % k + 1) % k = (p + 2) % k := by
    rw [add_mod_add_mod]
  have h2m : ((p + 2) % k + k - 1) % k = (p + 1) % k := by
    rw [sub1_add_mod (by omega) (by omega)]
  have h2p : ((p + 2) % k + 1) % k = (p + 3) % k := by
    rw [add_mod_add_mod]
  rw [testBit_wordStep hp, testBit_wordStep hp]
  rw [bit_mix (by omega) hz1 hp, bit_mix (by omega) hz2 hp]
  rw [bit_mix (by omega) hz1 hp1, bit_mix (by omega) hz2 hp1]
  rw [bit_mix (by omega) hz1 hp2, bit_mix (by omega) hz2 hp2]
  rw [h1m, h1p, h2m, h2p, hm1, h0, h1, h2, h3]

private theorem step_mix_forced_parity {k z₁ z₂ p : Nat} (hk : 3 ≤ k)
    (hz1 : z₁ < 2 ^ k) (hz2 : z₂ < 2 ^ k) (hp : p < k)
    (hm1 : z₁.testBit ((p + k - 1) % k) = z₂.testBit ((p + k - 1) % k))
    (h0 : z₁.testBit p = z₂.testBit p)
    (h1 : z₁.testBit ((p + 1) % k) = z₂.testBit ((p + 1) % k))
    (h2 : z₁.testBit ((p + 2) % k) = z₂.testBit ((p + 2) % k))
    (hne : (wordStep k (mix k z₁)).testBit p ≠ (wordStep k (mix k z₂)).testBit p) :
    xor (xor (z₁.testBit p) (z₁.testBit ((p + 1) % k))) (z₁.testBit ((p + 2) % k)) = false := by
  have hp1 : (p + 1) % k < k := Nat.mod_lt _ (by omega)
  have h1m : ((p + 1) % k + k - 1) % k = p := by
    rw [sub1_add_mod (by omega) (by omega)]
    simp [Nat.mod_eq_of_lt hp]
  have h1p : ((p + 1) % k + 1) % k = (p + 2) % k := by
    rw [add_mod_add_mod]
  have hm0 : (mix k z₁).testBit p = (mix k z₂).testBit p := by
    rw [bit_mix (by omega) hz1 hp, bit_mix (by omega) hz2 hp, hm1, h0, h1]
  have hm1' : (mix k z₁).testBit ((p + 1) % k) = (mix k z₂).testBit ((p + 1) % k) := by
    rw [bit_mix (by omega) hz1 hp1, bit_mix (by omega) hz2 hp1, h1m, h1p, h0, h1, h2]
  have hmixf : (mix k z₁).testBit ((p + 1) % k) = false := by
    cases hval : (mix k z₁).testBit ((p + 1) % k) with
    | false => rfl
    | true =>
      exfalso
      apply hne
      rw [testBit_wordStep hp, testBit_wordStep hp, ← hm0, ← hm1', hval]
      simp
  rw [bit_mix (by omega) hz1 hp1, h1m, h1p] at hmixf
  rw [Bool.xor_comm (z₁.testBit p) (z₁.testBit ((p + 1) % k))]
  exact hmixf

private theorem rot_diff_zero_iff {k s S base mask j : Nat}
    (hbase : base < 2 ^ k) (hmask : mask < 2 ^ k) (hj : j < k) :
    (rot k s base).testBit j = (rot k s (base ^^^ rot k S mask)).testBit j ↔
      mask.testBit (((j + k - s % k) % k + k - S % k) % k) = false := by
  have halt : base ^^^ rot k S mask < 2 ^ k := lt_xor hbase rot_lt
  have hp : (j + k - s % k) % k < k := Nat.mod_lt _ (by omega)
  rw [bit_rot hbase hj, bit_rot halt hj, Nat.testBit_xor, bit_rot hmask hp]
  cases base.testBit ((j + k - s % k) % k) <;>
    cases mask.testBit (((j + k - s % k) % k + k - S % k) % k) <;> simp

private theorem rot_idx_mod {k s S j : Nat} (hk : 0 < k) :
    (((j + k - s % k) % k + k - S % k) % k + s + S) % k = j % k := by
  have hs : s % k < k := Nat.mod_lt s hk
  have hS : S % k < k := Nat.mod_lt S hk
  have h1 : (((j + k - s % k) % k + k - S % k) % k + S % k) % k = (j + k - s % k) % k := by
    rw [add_mod_add_mod]
    have he : (j + k - s % k) % k + k - S % k + S % k = (j + k - s % k) % k + k := by omega
    rw [he, Nat.add_mod_right, Nat.mod_mod]
  have h2 : ((j + k - s % k) % k + s % k) % k = j % k := by
    rw [add_mod_add_mod]
    have he : j + k - s % k + s % k = j + k := by omega
    rw [he, Nat.add_mod_right]
  have hstep1 :
      (((j + k - s % k) % k + k - S % k) % k + s + S) % k =
        ((((j + k - s % k) % k + k - S % k) % k + S % k) % k + s % k) % k := by
    set x := ((j + k - s % k) % k + k - S % k) % k
    have ha : (x + s + S) % k = (x + s + S % k) % k := by
      rw [Nat.add_mod (x + s) S, Nat.add_mod (x + s) (S % k), Nat.mod_mod]
    have hb : x + s + S % k = (x + S % k) + s := by omega
    rw [ha, hb, Nat.add_mod (x + S % k) s]
  rw [hstep1, h1, h2]

private theorem pos_add_mod {k r i t δ : Nat} (hδ : δ ≤ k) :
    (pos k r i t δ + δ) % k = (i + 3 * (r - t)) % k := by
  unfold pos
  rw [add_mod_add_mod]
  have he : i + 3 * (r - t) + k - δ + δ = i + 3 * (r - t) + k := by omega
  rw [he, Nat.add_mod_right]

private theorem pos_prev_m1 {k r i t δ : Nat} (hk : 2 ≤ k) (ht1 : 1 ≤ t) (htr : t ≤ r)
    (hδ : δ + 4 ≤ k) :
    (pos k r i t δ + k - 1) % k = pos k r i (t - 1) (δ + 4) := by
  unfold pos
  apply mod_add_cancel_right (c := 1)
  have h1 : (i + 3 * (r - t) + k - δ) % k + k - 1 + 1 =
      (i + 3 * (r - t) + k - δ) % k + k := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_mod]
  congr 1
  omega

private theorem pos_prev_0 {k r i t δ : Nat} (ht1 : 1 ≤ t) (htr : t ≤ r) (hδ : δ + 3 ≤ k) :
    pos k r i t δ = pos k r i (t - 1) (δ + 3) := by
  unfold pos
  congr 1
  omega

private theorem pos_prev_1 {k r i t δ : Nat} (ht1 : 1 ≤ t) (htr : t ≤ r) (hδ : δ + 2 ≤ k) :
    (pos k r i t δ + 1) % k = pos k r i (t - 1) (δ + 2) := by
  unfold pos
  rw [add_mod_add_mod]
  congr 1
  omega

private theorem pos_prev_2 {k r i t δ : Nat} (ht1 : 1 ≤ t) (htr : t ≤ r) (hδ : δ + 1 ≤ k) :
    (pos k r i t δ + 2) % k = pos k r i (t - 1) (δ + 1) := by
  unfold pos
  rw [add_mod_add_mod]
  congr 1
  omega

private theorem pos_prev_3 {k r i t δ : Nat} (ht1 : 1 ≤ t) (htr : t ≤ r) (hδ : δ ≤ k) :
    (pos k r i t δ + 3) % k = pos k r i (t - 1) δ := by
  unfold pos
  rw [add_mod_add_mod]
  congr 1
  omega

private theorem key_inj_agree {k r e q i t s δ : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (htr : t ≤ r) (hδ : δ ≤ 4 * (r - t))
    (hlo : e + q < 3 * t + s + δ) (hhi : 3 * t + s + δ + q ≤ k + e + q)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q)) :
    let S := i + 3 * r + k - e - q
    (rot k s base.val).testBit (pos k r i t δ) =
      (rot k s (base.val ^^^ rot k S mask.val)).testBit (pos k r i t δ) := by
  intro S
  have hkpos : 0 < k := by omega
  have hqle : q ≤ k := by omega
  have hmaskk : mask.val < 2 ^ k :=
    Nat.lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right (by omega) hqle)
  have hpos : pos k r i t δ < k := Nat.mod_lt _ hkpos
  rw [rot_diff_zero_iff base.isLt hmaskk hpos]
  set a := ((pos k r i t δ + k - s % k) % k + k - S % k) % k
  by_cases ha : a < q
  · exfalso
    have hmod1 : (a + s + S) % k = (pos k r i t δ) % k := rot_idx_mod hkpos
    have hmod2 : ((a + s + S) + (e + q + δ)) % k = (pos k r i t δ + (e + q + δ)) % k := by
      rw [Nat.add_mod (a + s + S), hmod1, ← Nat.add_mod]
    have hS : S + e + q = i + 3 * r + k := by
      dsimp only [S]
      omega
    have hlhs : ((a + s + S) + (e + q + δ)) % k =
        ((3 * t + s + δ + a) + (i + 3 * (r - t))) % k := by
      have he : a + s + S + (e + q + δ) =
          (3 * t + s + δ + a) + (i + 3 * (r - t)) + k := by omega
      rw [he, Nat.add_mod_right]
    have hrhs : (pos k r i t δ + (e + q + δ)) % k =
        ((e + q) + (i + 3 * (r - t))) % k := by
      have he : pos k r i t δ + (e + q + δ) = (pos k r i t δ + δ) + (e + q) := by omega
      rw [he, Nat.add_mod, pos_add_mod (by omega : δ ≤ k), ← Nat.add_mod]
      congr 1
      omega
    rw [hlhs, hrhs] at hmod2
    have hfin : (3 * t + s + δ + a) % k = (e + q) % k := mod_add_cancel_right hmod2
    exact mod_ne_between (by omega : e + q < k) (by omega) (by omega) hfin
  · exact Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right (by omega) (by omega)))

private theorem state_agree_high {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q)) :
    let alt := base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val
    ∀ t, t < r → ∀ δ, e + q ≤ δ → δ ≤ 4 * (r - t) →
      (stateRec k constants u base.val t).testBit (pos k r i t δ) =
        (stateRec k constants u alt t).testBit (pos k r i t δ) := by
  intro alt t
  induction t with
  | zero =>
    intro h0 δ hlo hhi
    simp only [stateRec, Nat.testBit_xor]
    have hinj := key_inj_agree (i := i) (t := 0) (s := 1) (δ := δ)
      hq hr hk (by omega) hhi (by omega) (by omega) base mask
    rw [hinj]
  | succ t ih =>
    intro ht δ hlo hhi
    have htr : t < r := by omega
    have hsb : stateRec k constants u base.val t < 2 ^ k := stateRec_lt constants hu t
    have hsa : stateRec k constants u alt t < 2 ^ k := stateRec_lt constants hu t
    have hpos : pos k r i (t + 1) δ < k := Nat.mod_lt _ (by omega)
    have hstep :
        (wordStep k (mix k (stateRec k constants u base.val t))).testBit (pos k r i (t + 1) δ) =
        (wordStep k (mix k (stateRec k constants u alt t))).testBit (pos k r i (t + 1) δ) := by
      apply step_mix_congr (by omega) hsb hsa hpos
      · rw [pos_prev_m1 (by omega) (by omega) (by omega) (by omega)]
        exact ih htr (δ + 4) (by omega) (by omega)
      · rw [pos_prev_0 (by omega) (by omega) (by omega)]
        exact ih htr (δ + 3) (by omega) (by omega)
      · rw [pos_prev_1 (by omega) (by omega) (by omega)]
        exact ih htr (δ + 2) (by omega) (by omega)
      · rw [pos_prev_2 (by omega) (by omega) (by omega)]
        exact ih htr (δ + 1) (by omega) (by omega)
      · rw [pos_prev_3 (by omega) (by omega) (by omega)]
        exact ih htr δ (by omega) (by omega)
    have hinj := key_inj_agree (i := i) (t := t + 1) (s := 2 * t) (δ := δ)
      hq hr hk (by omega) hhi (by omega) (by omega) base mask
    simp only [stateRec, Nat.testBit_xor]
    rw [hstep, hinj]

private theorem wave_diff_iff_pre {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    {t δ : Nat} (hcut : e + q + 3 < t) (htr : t ≤ r) (hδ : δ ≤ 4 * (r - t)) :
    let alt := base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val
    ((waveWord k r constants u base.val t).testBit (pos k r i t δ) ≠
      (waveWord k r constants u alt t).testBit (pos k r i t δ)) ↔
    ((preWord k constants u base.val t).testBit (pos k r i t δ) ≠
      (preWord k constants u alt t).testBit (pos k r i t δ)) := by
  intro alt
  by_cases hlt : t < r
  · unfold waveWord
    simp only [hlt, ↓reduceIte]
    cases t with
    | zero => omega
    | succ t =>
      simp only [stateRec, preWord, Nat.add_sub_cancel, Nat.testBit_xor]
      have hinj := key_inj_agree (i := i) (t := t + 1) (s := 2 * t) (δ := δ)
        hq hr hk htr hδ (by omega) (by omega) base mask
      rw [hinj]
      cases (wordStep k (mix k (stateRec k constants u base.val t))).testBit (pos k r i (t + 1) δ) <;>
        cases (wordStep k (mix k (stateRec k constants u alt t))).testBit (pos k r i (t + 1) δ) <;>
        cases (rot k (2 * t) alt).testBit (pos k r i (t + 1) δ) <;>
        cases (constants (t + 1)).val.testBit (pos k r i (t + 1) δ) <;> simp
  · have hteq : t = r := by omega
    subst hteq
    unfold waveWord
    simp only [lt_irrefl, ↓reduceIte]

private theorem pre_diff_implies_prev {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    {t δ : Nat} (ht1 : 1 ≤ t) (htr : t ≤ r) (hδ : δ ≤ 4 * (r - t))
    (hne : (preWord k constants u base.val t).testBit (pos k r i t δ) ≠
      (preWord k constants u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) t).testBit
        (pos k r i t δ)) :
    ∃ δ', δ ≤ δ' ∧ δ' ≤ δ + 4 ∧
      (stateRec k constants u base.val (t - 1)).testBit (pos k r i (t - 1) δ') ≠
      (stateRec k constants u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) (t - 1)).testBit
        (pos k r i (t - 1) δ') := by
  set alt := base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val
  set z1 := stateRec k constants u base.val (t - 1)
  set z2 := stateRec k constants u alt (t - 1)
  have hz1 : z1 < 2 ^ k := stateRec_lt constants hu (t - 1)
  have hz2 : z2 < 2 ^ k := stateRec_lt constants hu (t - 1)
  have hpos : pos k r i t δ < k := Nat.mod_lt _ (by omega)
  by_cases h4 : z1.testBit (pos k r i (t - 1) (δ + 4)) = z2.testBit (pos k r i (t - 1) (δ + 4))
  · by_cases h3 : z1.testBit (pos k r i (t - 1) (δ + 3)) = z2.testBit (pos k r i (t - 1) (δ + 3))
    · by_cases h2 : z1.testBit (pos k r i (t - 1) (δ + 2)) = z2.testBit (pos k r i (t - 1) (δ + 2))
      · by_cases h1 : z1.testBit (pos k r i (t - 1) (δ + 1)) = z2.testBit (pos k r i (t - 1) (δ + 1))
        · by_cases h0 : z1.testBit (pos k r i (t - 1) δ) = z2.testBit (pos k r i (t - 1) δ)
          · exfalso
            apply hne
            apply step_mix_congr (by omega) hz1 hz2 hpos
            · rw [pos_prev_m1 (by omega) ht1 htr (by omega)]; exact h4
            · rw [pos_prev_0 ht1 htr (by omega)]; exact h3
            · rw [pos_prev_1 ht1 htr (by omega)]; exact h2
            · rw [pos_prev_2 ht1 htr (by omega)]; exact h1
            · rw [pos_prev_3 ht1 htr (by omega)]; exact h0
          · exact ⟨δ, by omega, by omega, h0⟩
        · exact ⟨δ + 1, by omega, by omega, h1⟩
      · exact ⟨δ + 2, by omega, by omega, h2⟩
    · exact ⟨δ + 3, by omega, by omega, h3⟩
  · exact ⟨δ + 4, by omega, by omega, h4⟩

private def parityEq (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i t δ : Nat)
    (key : Fin (2 ^ k)) : Bool :=
  let z := stateRec k constants u key.val (t - 1)
  let b := i + 3 * (r - t) + k - δ
  xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k))) (z.testBit ((b + 2) % k))

private theorem exists_history (k r e q : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k)
    (base : Fin (2 ^ k)) (mask : Fin (2 ^ q))
    (hdiff : (preWord k constants u base.val r).testBit i ≠
      (preWord k constants u (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i) :
    let cut := e + q + 3
    ∃ d : Nat → Nat,
      (∀ t, cut ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) ∧
      (∀ t, cut < t → t ≤ r → d t ≤ d (t - 1)) ∧
      ∀ t, cut < t → t ≤ r - e →
        (∀ s, cut ≤ s → s < t → s + d s < t + d t) →
        parityEq k r constants u i t (d t) base = false := by
  intro cut
  set alt := base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val
  let pDiff : Nat → Nat → Bool := fun t δ =>
    (waveWord k r constants u base.val t).testBit (pos k r i t δ) !=
      (waveWord k r constants u alt t).testBit (pos k r i t δ)
  let d : Nat → Nat := fun t => maxSat (pDiff t) (4 * (r - t))
  have hpDiff_true : ∀ t δ, pDiff t δ = true ↔
      (waveWord k r constants u base.val t).testBit (pos k r i t δ) ≠
        (waveWord k r constants u alt t).testBit (pos k r i t δ) := by
    intro t δ
    simp [pDiff]
  have hnonempty : ∀ n, n ≤ r - cut →
      ∃ δ, δ ≤ 4 * n ∧ pDiff (r - n) δ = true := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, by omega, ?_⟩
      rw [hpDiff_true]
      have hpos0 : pos k r i (r - 0) 0 = i := by
        unfold pos
        have he : i + 3 * (r - (r - 0)) + k - 0 = i + k := by omega
        rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      rw [hpos0]
      unfold waveWord
      simp only [Nat.sub_zero, lt_irrefl, ↓reduceIte]
      exact hdiff
    | succ n ih =>
      intro hn
      rcases ih (by omega) with ⟨δ, hδ, hpd⟩
      rw [hpDiff_true] at hpd
      have hpre := (wave_diff_iff_pre constants hq hr hk base mask
        (t := r - n) (δ := δ) (by omega) (by omega) (by omega)).mp hpd
      rcases pre_diff_implies_prev constants hq hr hk hu base mask
        (t := r - n) (δ := δ) (by omega) (by omega) (by omega) hpre with ⟨δ', h1, h2, hne⟩
      refine ⟨δ', by omega, ?_⟩
      rw [hpDiff_true]
      have hsub : r - n - 1 = r - (n + 1) := by omega
      rw [hsub] at hne
      unfold waveWord
      have hlt : r - (n + 1) < r := by omega
      simp only [hlt, ↓reduceIte]
      exact hne
  have hex : ∀ t, cut ≤ t → t ≤ r → ∃ δ, δ ≤ 4 * (r - t) ∧ pDiff t δ = true := by
    intro t hcut htr
    have h := hnonempty (r - t) (by omega)
    have hrt : r - (r - t) = t := by omega
    rw [hrt] at h
    exact h
  have hd_true : ∀ t, cut ≤ t → t ≤ r →
      (waveWord k r constants u base.val t).testBit (pos k r i t (d t)) ≠
        (waveWord k r constants u alt t).testBit (pos k r i t (d t)) := by
    intro t hcut htr
    rw [← hpDiff_true]
    exact maxSat_spec (pDiff t) (4 * (r - t)) (hex t hcut htr)
  have hd_le : ∀ t, d t ≤ 4 * (r - t) := fun t => maxSat_le (pDiff t) (4 * (r - t))
  have hd_mono : ∀ t, cut < t → t ≤ r → d t ≤ d (t - 1) := by
    intro t hcut htr
    have hdt : d t ≤ 4 * (r - t) := hd_le t
    have hwt := hd_true t (by omega) htr
    have hpre := (wave_diff_iff_pre constants hq hr hk base mask
      hcut htr hdt).mp hwt
    rcases pre_diff_implies_prev constants hq hr hk hu base mask
      (by omega) htr hdt hpre with ⟨δ', h1, h2, hne⟩
    have hpd' : pDiff (t - 1) δ' = true := by
      rw [hpDiff_true]
      unfold waveWord
      have hlt : t - 1 < r := by omega
      simp only [hlt, ↓reduceIte]
      exact hne
    have hle' : δ' ≤ d (t - 1) := le_maxSat (pDiff (t - 1)) (4 * (r - (t - 1))) δ' (by omega) hpd'
    omega
  refine ⟨d, ?_, hd_mono, ?_⟩
  · intro t hcut htr
    refine ⟨?_, hd_le t⟩
    by_cases hlt : t < r
    · by_contra hge
      have hagree := state_agree_high (i := i) constants hq hr hk hu base mask t hlt (d t) (by omega) (hd_le t)
      have hne := hd_true t hcut htr
      unfold waveWord at hne
      simp only [hlt, ↓reduceIte] at hne
      exact hne hagree
    · have hteq : t = r := by omega
      have h0 : d t ≤ 4 * (r - t) := hd_le t
      omega
  · intro t hcut htre hrec
    have htr : t ≤ r := by omega
    have hdt : d t ≤ 4 * (r - t) := hd_le t
    have hltprev : t - 1 < r := by omega
    have hrec1 : (t - 1) + d (t - 1) < t + d t := hrec (t - 1) (by omega) (by omega)
    have hmono1 : d t ≤ d (t - 1) := hd_mono t hcut htr
    have hdeq : d (t - 1) = d t := by omega
    have hagree_gt : ∀ δ', d t < δ' → δ' ≤ 4 * (r - (t - 1)) →
        (stateRec k constants u base.val (t - 1)).testBit (pos k r i (t - 1) δ') =
          (stateRec k constants u alt (t - 1)).testBit (pos k r i (t - 1) δ') := by
      intro δ' hgt hle
      by_contra hne
      have hpd' : pDiff (t - 1) δ' = true := by
        rw [hpDiff_true]
        unfold waveWord
        simp only [hltprev, ↓reduceIte]
        exact hne
      have hle' : δ' ≤ d (t - 1) := le_maxSat (pDiff (t - 1)) (4 * (r - (t - 1))) δ' hle hpd'
      omega
    have hwt := hd_true t (by omega) htr
    have hpre := (wave_diff_iff_pre constants hq hr hk base mask
      hcut htr hdt).mp hwt
    have hpos : pos k r i t (d t) < k := Nat.mod_lt _ (by omega)
    have hforced := step_mix_forced_parity (by omega)
      (stateRec_lt constants hu (t - 1)) (stateRec_lt constants hu (t - 1)) hpos
      (by rw [pos_prev_m1 (by omega) (by omega) htr (by omega)]
          exact hagree_gt (d t + 4) (by omega) (by omega))
      (by rw [pos_prev_0 (by omega) htr (by omega)]
          exact hagree_gt (d t + 3) (by omega) (by omega))
      (by rw [pos_prev_1 (by omega) htr (by omega)]
          exact hagree_gt (d t + 2) (by omega) (by omega))
      (by rw [pos_prev_2 (by omega) htr (by omega)]
          exact hagree_gt (d t + 1) (by omega) (by omega))
      hpre
    have hb0 : (i + 3 * (r - t) + k - d t) % k = pos k r i t (d t) := rfl
    have hb1 : (i + 3 * (r - t) + k - d t + 1) % k = (pos k r i t (d t) + 1) % k := by
      unfold pos
      rw [add_mod_add_mod]
    have hb2 : (i + 3 * (r - t) + k - d t + 2) % k = (pos k r i t (d t) + 2) % k := by
      unfold pos
      rw [add_mod_add_mod]
    unfold parityEq
    dsimp only
    rw [hb0, hb1, hb2]
    exact hforced

private def decLists : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | L + 1, 0 => [List.replicate (L + 1) 0]
  | L + 1, B + 1 =>
      (decLists L (B + 1)).map (fun xs => (B + 1) :: xs) ++ decLists (L + 1) B

private theorem decLists_length : ∀ L B, (decLists L B).length = Nat.choose (L + B) B
  | 0, B => by simp [decLists]
  | L + 1, 0 => by simp [decLists]
  | L + 1, B + 1 => by
    simp only [decLists, List.length_append, List.length_map,
      decLists_length L (B + 1), decLists_length (L + 1) B]
    have h1 : L + (B + 1) = L + B + 1 := by omega
    have h2 : L + 1 + B = L + B + 1 := by omega
    have h3 : L + 1 + (B + 1) = L + B + 1 + 1 := by omega
    rw [h1, h2, h3, Nat.choose_succ_succ (L + B + 1) B, Nat.add_comm]

private theorem decLists_spec : ∀ L B xs, xs ∈ decLists L B →
    xs.length = L ∧ (∀ j, j < L → xs.getD j 0 ≤ B) ∧
      (∀ j, j + 1 < L → xs.getD (j + 1) 0 ≤ xs.getD j 0)
  | 0, B, xs, h => by
    simp only [decLists, List.mem_singleton] at h
    subst h
    refine ⟨rfl, ?_, ?_⟩ <;> omega
  | L + 1, 0, xs, h => by
    simp only [decLists, List.mem_singleton] at h
    subst h
    refine ⟨List.length_replicate, ?_, ?_⟩
    · intro j hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj]
    · intro j hj
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj, Nat.lt_of_succ_lt hj]
  | L + 1, B + 1, xs, h => by
    simp only [decLists, List.mem_append, List.mem_map] at h
    rcases h with ⟨tl, htl, rfl⟩ | h2
    · rcases decLists_spec L (B + 1) tl htl with ⟨hlen, hle, hdec⟩
      refine ⟨by simp [hlen], ?_, ?_⟩
      · intro j hj
        cases j with
        | zero => simp
        | succ j =>
          simpa [List.getD_cons_succ] using hle j (by omega)
      · intro j hj
        cases j with
        | zero =>
          simpa [List.getD_cons_succ, List.getD_cons_zero] using hle 0 (by omega)
        | succ j =>
          simpa [List.getD_cons_succ] using hdec j (by omega)
    · rcases decLists_spec (L + 1) B xs h2 with ⟨hlen, hle, hdec⟩
      refine ⟨hlen, ?_, hdec⟩
      intro j hj
      exact Nat.le_trans (hle j hj) (Nat.le_succ B)

private theorem mem_decLists : ∀ L B xs,
    xs.length = L →
    (∀ j, j < L → xs.getD j 0 ≤ B) →
    (∀ j, j + 1 < L → xs.getD (j + 1) 0 ≤ xs.getD j 0) →
    xs ∈ decLists L B
  | 0, B, xs, hlen, _, _ => by
    cases xs with
    | nil => simp [decLists]
    | cons _ _ => simp at hlen
  | L + 1, 0, xs, hlen, hle, _ => by
    simp only [decLists, List.mem_singleton]
    apply List.ext_getElem (by simp [hlen])
    intro j hj1 hj2
    have h0 := hle j (by omega)
    have hget : xs.getD j 0 = xs[j] := by
      simp [List.getD_eq_getElem?_getD, hj1]
    rw [hget] at h0
    simp [List.getElem_replicate]
    omega
  | L + 1, B + 1, xs, hlen, hle, hdec => by
    cases xs with
    | nil => simp at hlen
    | cons a tl =>
      simp only [decLists, List.mem_append, List.mem_map]
      have ha : a ≤ B + 1 := by
        simpa [List.getD_cons_zero] using hle 0 (by omega)
      by_cases heq : a = B + 1
      · left
        refine ⟨tl, ?_, by rw [heq]⟩
        apply mem_decLists L (B + 1) tl (by simp at hlen; omega)
        · intro j hj
          simpa [List.getD_cons_succ] using hle (j + 1) (by omega)
        · intro j hj
          simpa [List.getD_cons_succ] using hdec (j + 1) (by omega)
      · right
        have haB : a ≤ B := by omega
        have hall : ∀ j, j < L + 1 → (a :: tl).getD j 0 ≤ a := by
          intro j
          induction j with
          | zero => intro _; simp
          | succ j ih =>
            intro hj
            exact Nat.le_trans (hdec j hj) (ih (by omega))
        apply mem_decLists (L + 1) B (a :: tl) hlen
        · intro j hj
          exact Nat.le_trans (hall j hj) haB
        · exact hdec

private def dOf (cut : Nat) (xs : List Nat) (t : Nat) : Nat :=
  xs.getD (t - cut) 0

private def isRec (d : Nat → Nat) (cut t : Nat) : Bool :=
  (List.range (t - cut)).all (fun j => decide ((cut + j) + d (cut + j) < t + d t))

private theorem isRec_iff (d : Nat → Nat) (cut t : Nat) :
    isRec d cut t = true ↔ ∀ s, cut ≤ s → s < t → s + d s < t + d t := by
  unfold isRec
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h s hcs hst
    have h1 := h (s - cut) (by omega)
    have he : cut + (s - cut) = s := by omega
    rw [he] at h1
    exact h1
  · intro h j hj
    exact h (cut + j) (by omega) (by omega)

private def recList (d : Nat → Nat) (cut n : Nat) : List Nat :=
  ((List.range n).map (fun j => cut + 1 + j)).filter (isRec d cut)

private theorem recList_succ (d : Nat → Nat) (cut n : Nat) :
    recList d cut (n + 1) =
      recList d cut n ++ (if isRec d cut (cut + 1 + n) then [cut + 1 + n] else []) := by
  unfold recList
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil, List.filter_append,
      List.filter_cons, List.filter_nil]

private theorem recList_pairwise (d : Nat → Nat) (cut n : Nat) :
    (recList d cut n).Pairwise (· < ·) := by
  unfold recList
  apply List.Pairwise.filter
  apply List.pairwise_map.mpr
  refine List.Pairwise.imp ?_ List.pairwise_lt_range
  intro a b hab
  omega

private theorem mem_recList (d : Nat → Nat) (cut n t : Nat) :
    t ∈ recList d cut n ↔
      cut < t ∧ t ≤ cut + n ∧ ∀ s, cut ≤ s → s < t → s + d s < t + d t := by
  unfold recList
  simp only [List.mem_filter, List.mem_map, List.mem_range, isRec_iff]
  constructor
  · rintro ⟨⟨j, hj, rfl⟩, hrec⟩
    exact ⟨by omega, by omega, hrec⟩
  · rintro ⟨h1, h2, hrec⟩
    exact ⟨⟨t - cut - 1, by omega, by omega⟩, hrec⟩

private def runMax (d : Nat → Nat) (cut : Nat) : Nat → Nat
  | 0 => cut + d cut
  | n + 1 => max (runMax d cut n) ((cut + n + 1) + d (cut + n + 1))

private theorem le_runMax (d : Nat → Nat) (cut : Nat) :
    ∀ n j, j ≤ n → (cut + j) + d (cut + j) ≤ runMax d cut n
  | 0, j, hj => by
    have h0 : j = 0 := by omega
    subst h0
    simp [runMax]
  | n + 1, j, hj => by
    by_cases heq : j = n + 1
    · subst heq
      simp only [runMax]
      exact Nat.le_max_right _ _
    · simp only [runMax]
      exact Nat.le_trans (le_runMax d cut n j (by omega)) (Nat.le_max_left _ _)

private theorem runMax_le_recList (d : Nat → Nat) (cut : Nat) :
    ∀ n, (∀ j, j < n → d (cut + j + 1) ≤ d (cut + j)) →
      runMax d cut n ≤ cut + d cut + (recList d cut n).length
  | 0, _ => by
    simp [runMax, recList]
  | n + 1, hmono => by
    have ih := runMax_le_recList d cut n (fun j hj => hmono j (by omega))
    rw [recList_succ]
    simp only [runMax]
    cases hrec : isRec d cut (cut + 1 + n) with
    | true =>
      have hlen : (recList d cut n ++ [cut + 1 + n]).length = (recList d cut n).length + 1 := by
        simp
      rw [if_pos rfl, hlen]
      have hstep : (cut + n + 1) + d (cut + n + 1) ≤ runMax d cut n + 1 := by
        have hprev := le_runMax d cut n n (Nat.le_refl n)
        have hm := hmono n (Nat.lt_succ_self n)
        omega
      omega
    | false =>
      have hlen : (recList d cut n ++ []).length = (recList d cut n).length := by simp
      rw [if_neg (by simp), hlen]
      have hnot : ¬ ∀ s, cut ≤ s → s < cut + 1 + n → s + d s < (cut + 1 + n) + d (cut + 1 + n) := by
        rw [← isRec_iff]
        simp [hrec]
      have hex : ∃ s, cut ≤ s ∧ s < cut + 1 + n ∧ (cut + 1 + n) + d (cut + 1 + n) ≤ s + d s := by
        by_contra hall
        apply hnot
        intro s h1 h2
        by_contra hle
        exact hall ⟨s, h1, h2, by omega⟩
      rcases hex with ⟨s, hs1, hs2, hle⟩
      have hsmax : s + d s ≤ runMax d cut n := by
        have h1 := le_runMax d cut n (s - cut) (by omega)
        have he : cut + (s - cut) = s := by omega
        rw [he] at h1
        exact h1
      have he2 : cut + n + 1 = cut + 1 + n := by omega
      rw [he2]
      omega

private theorem recList_length_ge (d : Nat → Nat) (cut n B : Nat)
    (h0 : d cut ≤ B) (hmono : ∀ j, j < n → d (cut + j + 1) ≤ d (cut + j)) :
    n - B ≤ (recList d cut n).length := by
  have h1 := le_runMax d cut n n (Nat.le_refl n)
  have h2 := runMax_le_recList d cut n hmono
  omega

private def flipBit (k : Nat) (key : Fin (2 ^ k)) (p : Nat) (hp : p < k) : Fin (2 ^ k) :=
  ⟨key.val ^^^ 2 ^ p, lt_xor key.isLt (Nat.pow_lt_pow_right (by omega) hp)⟩

private theorem flipBit_involutive {k : Nat} (key : Fin (2 ^ k)) (p : Nat) (hp : p < k) :
    flipBit k (flipBit k key p hp) p hp = key := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [flipBit, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

private theorem testBit_flipBit_self {k : Nat} (key : Fin (2 ^ k)) (p : Nat) (hp : p < k) :
    (flipBit k key p hp).val.testBit p = !(key.val.testBit p) := by
  simp [flipBit, Nat.testBit_xor, Nat.testBit_two_pow_self]

private theorem testBit_flipBit_ne {k : Nat} (key : Fin (2 ^ k)) {p j : Nat}
    (hp : p < k) (hne : j ≠ p) :
    (flipBit k key p hp).val.testBit j = key.val.testBit j := by
  have h2 : (2 ^ p).testBit j = false := by
    rw [Nat.testBit_two_pow]
    simp [Ne.symm hne]
  simp [flipBit, Nat.testBit_xor, h2]

private def yRaw (k r i t δ : Nat) : Nat :=
  i + 3 * r + k + 4 - 5 * t - δ

private theorem stateRec_flip_agree {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    {t δ Y : Nat} (hcut : e + q + 3 < t) (htre : t ≤ r - e) (hδ : δ < e + q)
    (hY1 : Y ≤ yRaw k r i t δ) (hY2 : yRaw k r i t δ + 5 * t - 6 < Y + k)
    (key : Fin (2 ^ k)) :
    let p := Y % k
    have hp : p < k := Nat.mod_lt _ (by omega)
    let key' := flipBit k key p hp
    let b := i + 3 * (r - t) + k - δ
    ∀ τ, τ ≤ t - 2 → ∀ x, b - (t - 1 - τ) ≤ x → x ≤ b + 2 + 3 * (t - 1 - τ) →
      (stateRec k constants u key.val τ).testBit (x % k) =
        (stateRec k constants u key'.val τ).testBit (x % k) := by
  intro p hp key' b τ
  induction τ with
  | zero =>
    intro hτ x hx1 hx2
    have hxmod : x % k < k := Nat.mod_lt _ (by omega)
    have h1x : 1 ≤ x := by
      dsimp only [b] at hx1
      omega
    have hne : (x - 1) % k ≠ p := by
      dsimp only [p]
      apply mod_ne_of_lt_add
      · dsimp only [b] at hx1
        unfold yRaw at hY1
        omega
      · dsimp only [b] at hx2
        unfold yRaw at hY2
        omega
    simp only [stateRec, Nat.testBit_xor]
    rw [bit_rot key.isLt hxmod, bit_rot key'.isLt hxmod, sub_mod_shift (by omega) h1x]
    rw [testBit_flipBit_ne key hp hne]
  | succ τ ih =>
    intro hτ x hx1 hx2
    have hxmod : x % k < k := Nat.mod_lt _ (by omega)
    have hsb1 : stateRec k constants u key.val τ < 2 ^ k := stateRec_lt constants hu τ
    have hsb2 : stateRec k constants u key'.val τ < 2 ^ k := stateRec_lt constants hu τ
    have h1x : 1 ≤ x := by
      dsimp only [b] at hx1
      omega
    have hxm1 : (x % k + k - 1) % k = (x - 1) % k := by
      have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      have h2 := sub_mod_shift (k := k) (s := 1) (by omega) h1x
      rw [h1] at h2
      exact h2
    have hstep :
        (wordStep k (mix k (stateRec k constants u key.val τ))).testBit (x % k) =
        (wordStep k (mix k (stateRec k constants u key'.val τ))).testBit (x % k) := by
      apply step_mix_congr (by omega) hsb1 hsb2 hxmod
      · rw [hxm1]
        exact ih (by omega) (x - 1) (by omega) (by omega)
      · exact ih (by omega) x (by omega) (by omega)
      · rw [add_mod_add_mod]
        exact ih (by omega) (x + 1) (by omega) (by omega)
      · rw [add_mod_add_mod]
        exact ih (by omega) (x + 2) (by omega) (by omega)
      · rw [add_mod_add_mod]
        exact ih (by omega) (x + 3) (by omega) (by omega)
    have h2τx : 2 * τ ≤ x := by
      dsimp only [b] at hx1
      omega
    have hne : (x - 2 * τ) % k ≠ p := by
      dsimp only [p]
      apply mod_ne_of_lt_add
      · dsimp only [b] at hx1
        unfold yRaw at hY1
        omega
      · dsimp only [b] at hx2
        unfold yRaw at hY2
        omega
    simp only [stateRec, Nat.testBit_xor]
    rw [hstep, bit_rot key.isLt hxmod, bit_rot key'.isLt hxmod, sub_mod_shift (by omega) h2τx]
    rw [testBit_flipBit_ne key hp hne]

private theorem pre_flip_agree {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    {t δ Y : Nat} (hcut : e + q + 3 < t) (htre : t ≤ r - e) (hδ : δ < e + q)
    (hY1 : Y ≤ yRaw k r i t δ) (hY2 : yRaw k r i t δ + 5 * t - 6 < Y + k)
    (key : Fin (2 ^ k)) (off : Nat) (hoff : off ≤ 2) :
    let p := Y % k
    have hp : p < k := Nat.mod_lt _ (by omega)
    let key' := flipBit k key p hp
    let b := i + 3 * (r - t) + k - δ
    (wordStep k (mix k (stateRec k constants u key.val (t - 2)))).testBit ((b + off) % k) =
      (wordStep k (mix k (stateRec k constants u key'.val (t - 2)))).testBit ((b + off) % k) := by
  intro p hp key' b
  have hcone := stateRec_flip_agree constants hq hr hk hu hcut htre hδ hY1 hY2 key (t - 2) (by omega)
  have hsb1 : stateRec k constants u key.val (t - 2) < 2 ^ k := stateRec_lt constants hu (t - 2)
  have hsb2 : stateRec k constants u key'.val (t - 2) < 2 ^ k := stateRec_lt constants hu (t - 2)
  have hbm : (b + off) % k < k := Nat.mod_lt _ (by omega)
  have h1b : 1 ≤ b + off := by
    dsimp only [b]
    omega
  have hbm1 : ((b + off) % k + k - 1) % k = (b + off - 1) % k := by
    have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 := sub_mod_shift (k := k) (s := 1) (by omega) h1b
    rw [h1] at h2
    exact h2
  apply step_mix_congr (by omega) hsb1 hsb2 hbm
  · rw [hbm1]
    exact hcone (b + off - 1) (by omega) (by omega)
  · exact hcone (b + off) (by omega) (by omega)
  · rw [add_mod_add_mod]
    exact hcone (b + off + 1) (by omega) (by omega)
  · rw [add_mod_add_mod]
    exact hcone (b + off + 2) (by omega) (by omega)
  · rw [add_mod_add_mod]
    exact hcone (b + off + 3) (by omega) (by omega)

private theorem parityEq_flip_self {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    {t δ : Nat} (hcut : e + q + 3 < t) (htre : t ≤ r - e) (hδ : δ < e + q)
    (key : Fin (2 ^ k)) :
    let p := yRaw k r i t δ % k
    have hp : p < k := Nat.mod_lt _ (by omega)
    parityEq k r constants u i t δ (flipBit k key p hp) = !(parityEq k r constants u i t δ key) := by
  intro p hp
  set key' := flipBit k key p hp
  set b := i + 3 * (r - t) + k - δ
  have hY1 : yRaw k r i t δ ≤ yRaw k r i t δ := Nat.le_refl _
  have hY2 : yRaw k r i t δ + 5 * t - 6 < yRaw k r i t δ + k := by omega
  have hpre0 := pre_flip_agree constants hq hr hk hu hcut htre hδ hY1 hY2 key 0 (by omega)
  have hpre1 := pre_flip_agree constants hq hr hk hu hcut htre hδ hY1 hY2 key 1 (by omega)
  have hpre2 := pre_flip_agree constants hq hr hk hu hcut htre hδ hY1 hY2 key 2 (by omega)
  simp only [Nat.add_zero] at hpre0
  have ht1 : t - 1 = (t - 2) + 1 := by omega
  have h0b : 2 * (t - 2) ≤ b := by
    dsimp only [b]
    omega
  have hsub0 : (b - 2 * (t - 2)) % k = p := by
    dsimp only [b, p]
    unfold yRaw
    congr 1
    omega
  have hsub1 : (b + 1 - 2 * (t - 2)) % k ≠ p := by
    dsimp only [b, p]
    apply mod_ne_of_lt_add <;> (unfold yRaw; omega)
  have hsub2 : (b + 2 - 2 * (t - 2)) % k ≠ p := by
    dsimp only [b, p]
    apply mod_ne_of_lt_add <;> (unfold yRaw; omega)
  have hz0 : (stateRec k constants u key'.val (t - 1)).testBit (b % k) =
      !((stateRec k constants u key.val (t - 1)).testBit (b % k)) := by
    rw [ht1]
    simp only [stateRec, Nat.testBit_xor]
    have hpre0' : (wordStep k (mix k (stateRec k constants u key.val (t - 2)))).testBit (b % k) =
        (wordStep k (mix k (stateRec k constants u key'.val (t - 2)))).testBit (b % k) := hpre0
    rw [← hpre0', bit_rot key.isLt (Nat.mod_lt _ (by omega)),
        bit_rot key'.isLt (Nat.mod_lt _ (by omega)),
        sub_mod_shift (by omega) h0b, hsub0, testBit_flipBit_self]
    cases (wordStep k (mix k (stateRec k constants u key.val (t - 2)))).testBit (b % k) <;>
      cases key.val.testBit p <;>
      cases (constants (t - 2 + 1)).val.testBit (b % k) <;> rfl
  have hz1 : (stateRec k constants u key'.val (t - 1)).testBit ((b + 1) % k) =
      (stateRec k constants u key.val (t - 1)).testBit ((b + 1) % k) := by
    rw [ht1]
    simp only [stateRec, Nat.testBit_xor]
    rw [hpre1, bit_rot key.isLt (Nat.mod_lt _ (by omega)),
        bit_rot key'.isLt (Nat.mod_lt _ (by omega)),
        sub_mod_shift (by omega) (by omega : 2 * (t - 2) ≤ b + 1),
        testBit_flipBit_ne key hp hsub1]
  have hz2 : (stateRec k constants u key'.val (t - 1)).testBit ((b + 2) % k) =
      (stateRec k constants u key.val (t - 1)).testBit ((b + 2) % k) := by
    rw [ht1]
    simp only [stateRec, Nat.testBit_xor]
    rw [hpre2, bit_rot key.isLt (Nat.mod_lt _ (by omega)),
        bit_rot key'.isLt (Nat.mod_lt _ (by omega)),
        sub_mod_shift (by omega) (by omega : 2 * (t - 2) ≤ b + 2),
        testBit_flipBit_ne key hp hsub2]
  unfold parityEq
  dsimp only
  change xor (xor ((stateRec k constants u key'.val (t - 1)).testBit (b % k))
    ((stateRec k constants u key'.val (t - 1)).testBit ((b + 1) % k)))
    ((stateRec k constants u key'.val (t - 1)).testBit ((b + 2) % k)) =
    !(xor (xor ((stateRec k constants u key.val (t - 1)).testBit (b % k))
      ((stateRec k constants u key.val (t - 1)).testBit ((b + 1) % k)))
      ((stateRec k constants u key.val (t - 1)).testBit ((b + 2) % k)))
  rw [hz0, hz1, hz2]
  cases (stateRec k constants u key.val (t - 1)).testBit (b % k) <;>
    cases (stateRec k constants u key.val (t - 1)).testBit ((b + 1) % k) <;>
    cases (stateRec k constants u key.val (t - 1)).testBit ((b + 2) % k) <;> rfl

private theorem parityEq_flip_later {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    {t t' δ δ' : Nat} (hcut : e + q + 3 < t) (htt' : t < t') (htre' : t' ≤ r - e)
    (hδ : δ < e + q) (hδ' : δ' ≤ δ) (hrec : t + δ < t' + δ')
    (key : Fin (2 ^ k)) :
    let p := yRaw k r i t' δ' % k
    have hp : p < k := Nat.mod_lt _ (by omega)
    parityEq k r constants u i t δ (flipBit k key p hp) = parityEq k r constants u i t δ key := by
  intro p hp
  set key' := flipBit k key p hp
  set b := i + 3 * (r - t) + k - δ
  have hY1 : yRaw k r i t' δ' ≤ yRaw k r i t δ := by
    unfold yRaw
    omega
  have hY2 : yRaw k r i t δ + 5 * t - 6 < yRaw k r i t' δ' + k := by
    unfold yRaw
    omega
  have hpre0 := pre_flip_agree constants hq hr hk hu hcut (by omega) hδ hY1 hY2 key 0 (by omega)
  have hpre1 := pre_flip_agree constants hq hr hk hu hcut (by omega) hδ hY1 hY2 key 1 (by omega)
  have hpre2 := pre_flip_agree constants hq hr hk hu hcut (by omega) hδ hY1 hY2 key 2 (by omega)
  simp only [Nat.add_zero] at hpre0
  have ht1 : t - 1 = (t - 2) + 1 := by omega
  have h0b : 2 * (t - 2) ≤ b := by
    dsimp only [b]
    omega
  have hsub0 : (b - 2 * (t - 2)) % k ≠ p := by
    dsimp only [b, p]
    apply mod_ne_of_lt_add <;> (unfold yRaw; omega)
  have hsub1 : (b + 1 - 2 * (t - 2)) % k ≠ p := by
    dsimp only [b, p]
    apply mod_ne_of_lt_add <;> (unfold yRaw; omega)
  have hsub2 : (b + 2 - 2 * (t - 2)) % k ≠ p := by
    dsimp only [b, p]
    apply mod_ne_of_lt_add <;> (unfold yRaw; omega)
  have hz0 : (stateRec k constants u key'.val (t - 1)).testBit (b % k) =
      (stateRec k constants u key.val (t - 1)).testBit (b % k) := by
    rw [ht1]
    simp only [stateRec, Nat.testBit_xor]
    rw [hpre0, bit_rot key.isLt (Nat.mod_lt _ (by omega)),
        bit_rot key'.isLt (Nat.mod_lt _ (by omega)),
        sub_mod_shift (by omega) h0b, testBit_flipBit_ne key hp hsub0]
  have hz1 : (stateRec k constants u key'.val (t - 1)).testBit ((b + 1) % k) =
      (stateRec k constants u key.val (t - 1)).testBit ((b + 1) % k) := by
    rw [ht1]
    simp only [stateRec, Nat.testBit_xor]
    rw [hpre1, bit_rot key.isLt (Nat.mod_lt _ (by omega)),
        bit_rot key'.isLt (Nat.mod_lt _ (by omega)),
        sub_mod_shift (by omega) (by omega : 2 * (t - 2) ≤ b + 1),
        testBit_flipBit_ne key hp hsub1]
  have hz2 : (stateRec k constants u key'.val (t - 1)).testBit ((b + 2) % k) =
      (stateRec k constants u key.val (t - 1)).testBit ((b + 2) % k) := by
    rw [ht1]
    simp only [stateRec, Nat.testBit_xor]
    rw [hpre2, bit_rot key.isLt (Nat.mod_lt _ (by omega)),
        bit_rot key'.isLt (Nat.mod_lt _ (by omega)),
        sub_mod_shift (by omega) (by omega : 2 * (t - 2) ≤ b + 2),
        testBit_flipBit_ne key hp hsub2]
  unfold parityEq
  dsimp only
  change xor (xor ((stateRec k constants u key'.val (t - 1)).testBit (b % k))
    ((stateRec k constants u key'.val (t - 1)).testBit ((b + 1) % k)))
    ((stateRec k constants u key'.val (t - 1)).testBit ((b + 2) % k)) =
    xor (xor ((stateRec k constants u key.val (t - 1)).testBit (b % k))
      ((stateRec k constants u key.val (t - 1)).testBit ((b + 1) % k)))
      ((stateRec k constants u key.val (t - 1)).testBit ((b + 2) % k))
  rw [hz0, hz1, hz2]

private theorem card_triangular_filter {k : Nat}
    (ps : List Nat) (Es : List (Fin (2 ^ k) → Bool))
    (hlen : ps.length = Es.length)
    (hp_lt : ∀ j (hj : j < ps.length), ps[j] < k)
    (hflip : ∀ j (hj : j < Es.length) (key : Fin (2 ^ k)),
      Es[j] (flipBit k key (ps[j]'(by omega)) (hp_lt j (by omega))) = !(Es[j] key))
    (hpres : ∀ a j (ha : a < j) (hj : j < Es.length) (key : Fin (2 ^ k)),
      (Es[a]'(by omega)) (flipBit k key (ps[j]'(by omega)) (hp_lt j (by omega))) =
        (Es[a]'(by omega)) key) :
    ∀ m (hm : m ≤ Es.length),
      2 ^ m * ((Finset.univ : Finset (Fin (2 ^ k))).filter
        (fun key => ∀ j (hj : j < m), (Es[j]'(by omega)) key = false)).card = 2 ^ k := by
  intro m
  induction m with
  | zero =>
    intro _
    simp
  | succ m ih =>
    intro hm
    let S : Finset (Fin (2 ^ k)) := (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun key => ∀ j (hj : j < m), (Es[j]'(by omega)) key = false)
    let S0 : Finset (Fin (2 ^ k)) := S.filter (fun key => (Es[m]'(by omega)) key = false)
    let S1 : Finset (Fin (2 ^ k)) := S.filter (fun key => ¬ ((Es[m]'(by omega)) key = false))
    have hS0_eq : (Finset.univ : Finset (Fin (2 ^ k))).filter
        (fun key => ∀ j (hj : j < m + 1), (Es[j]'(by omega)) key = false) = S0 := by
      ext key
      simp only [S0, S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨fun j hj => h j (by omega), h m (by omega)⟩
      · rintro ⟨h1, h2⟩ j hj
        by_cases hjm : j = m
        · subst hjm
          exact h2
        · exact h1 j (by omega)
    have hsum : S0.card + S1.card = S.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext key
        simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        by_cases hval : (Es[m]'(by omega)) key = false <;> simp [hval]
      · rw [Finset.disjoint_left]
        intro key h0 h1
        simp only [S0, S1, Finset.mem_filter] at h0 h1
        exact h1.2 h0.2
    have hpm : ps[m]'(by omega) < k := hp_lt m (by omega)
    have hbij : S0.card = S1.card := by
      refine Finset.card_bij (fun key _ => flipBit k key (ps[m]'(by omega)) hpm) ?_ ?_ ?_
      · intro key hkey
        simp only [S0, S, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hkey ⊢
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [hpres j m hj (by omega) key]
          exact hkey.1 j hj
        · rw [hflip m (by omega) key, hkey.2]
          decide
      · intro a _ b _ hab
        have h1 := congrArg (fun x => flipBit k x (ps[m]'(by omega)) hpm) hab
        rw [flipBit_involutive, flipBit_involutive] at h1
        exact h1
      · intro key hkey
        refine ⟨flipBit k key (ps[m]'(by omega)) hpm, ?_, flipBit_involutive key _ hpm⟩
        simp only [S0, S, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hkey ⊢
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [hpres j m hj (by omega) key]
          exact hkey.1 j hj
        · rw [hflip m (by omega) key]
          cases hval : (Es[m]'(by omega)) key with
          | false => exact absurd hval hkey.2
          | true => rfl
    rw [hS0_eq]
    have hih := ih (by omega)
    have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := Nat.pow_succ 2 m
    rw [hpow, Nat.mul_assoc]
    have h2 : 2 * S0.card = S.card := by omega
    rw [h2]
    exact hih

private theorem card_fiber_le {k r e q : Nat} (constants : Nat → Fin (2 ^ k)) {u i : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (xs : List Nat) (hxs : xs ∈ decLists ((r - e) - (e + q + 3) + 1) (e + q - 1)) :
    let cut := e + q + 3
    let d := dOf cut xs
    let recs := recList d cut ((r - e) - cut)
    ((Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun key => ∀ t ∈ recs, parityEq k r constants u i t (d t) key = false)).card ≤
      2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
  intro cut d recs
  rcases decLists_spec _ _ xs hxs with ⟨hlen, hle, hdec⟩
  let ps : List Nat := recs.map (fun t => yRaw k r i t (d t) % k)
  let Es : List (Fin (2 ^ k) → Bool) := recs.map (fun t => parityEq k r constants u i t (d t))
  have hlen_pe : ps.length = Es.length := by simp [ps, Es]
  have hkpos : 0 < k := by omega
  have hp_lt : ∀ j (hj : j < ps.length), ps[j] < k := by
    intro j hj
    simp only [ps, List.getElem_map]
    exact Nat.mod_lt _ hkpos
  have hd_lt : ∀ t, cut ≤ t → t ≤ r - e → d t < e + q := by
    intro t h1 h2
    have h := hle (t - cut) (by omega)
    dsimp only [d, dOf]
    omega
  have hd_anti : ∀ t1 t2, cut ≤ t1 → t1 ≤ t2 → t2 ≤ r - e → d t2 ≤ d t1 := by
    intro t1 t2 h1 h12 h2
    have hstep : ∀ m, t1 + m ≤ r - e → d (t1 + m) ≤ d t1 := by
      intro m
      induction m with
      | zero => intro _; exact Nat.le_refl _
      | succ m ih =>
        intro hm
        have hstep1 := hdec (t1 + m - cut) (by omega)
        have he1 : t1 + m - cut + 1 = t1 + (m + 1) - cut := by omega
        rw [he1] at hstep1
        exact Nat.le_trans hstep1 (ih (by omega))
    have h := hstep (t2 - t1) (by omega)
    have he : t1 + (t2 - t1) = t2 := by omega
    rw [he] at h
    exact h
  have hpw := recList_pairwise d cut ((r - e) - cut)
  have hrec_lt : ∀ a b (ha : a < b) (hb : b < recs.length), recs[a] < recs[b] :=
    fun a b ha hb => List.pairwise_iff_getElem.mp hpw a b (Nat.lt_trans ha hb) hb ha
  have hflip : ∀ j (hj : j < Es.length) (key : Fin (2 ^ k)),
      Es[j] (flipBit k key (ps[j]'(by omega)) (hp_lt j (by omega))) = !(Es[j] key) := by
    intro j hj key
    have hjr : j < recs.length := by simp [Es] at hj; exact hj
    have hmem : recs[j] ∈ recs := List.getElem_mem hjr
    rcases (mem_recList d cut ((r - e) - cut) recs[j]).mp hmem with ⟨h1, h2, _⟩
    simp only [Es, ps, List.getElem_map]
    exact parityEq_flip_self constants hq hr hk hu h1 (by omega) (hd_lt _ (by omega) (by omega)) key
  have hpres : ∀ a j (ha : a < j) (hj : j < Es.length) (key : Fin (2 ^ k)),
      (Es[a]'(by omega)) (flipBit k key (ps[j]'(by omega)) (hp_lt j (by omega))) =
        (Es[a]'(by omega)) key := by
    intro a j ha hj key
    have hjr : j < recs.length := by simp [Es] at hj; exact hj
    have har : a < recs.length := Nat.lt_trans ha hjr
    have hmema : recs[a] ∈ recs := List.getElem_mem har
    have hmemj : recs[j] ∈ recs := List.getElem_mem hjr
    rcases (mem_recList d cut ((r - e) - cut) recs[a]).mp hmema with ⟨ha1, ha2, _⟩
    rcases (mem_recList d cut ((r - e) - cut) recs[j]).mp hmemj with ⟨hj1, hj2, hjrec⟩
    have hlt : recs[a] < recs[j] := hrec_lt a j ha hjr
    have hrec_aj : recs[a] + d recs[a] < recs[j] + d recs[j] := hjrec recs[a] (by omega) hlt
    have hanti_aj : d recs[j] ≤ d recs[a] := hd_anti recs[a] recs[j] (by omega) (by omega) (by omega)
    simp only [Es, ps, List.getElem_map]
    exact parityEq_flip_later constants hq hr hk hu ha1 hlt (by omega)
      (hd_lt _ (by omega) (by omega)) hanti_aj hrec_aj key
  have hcard_eq := card_triangular_filter ps Es hlen_pe hp_lt hflip hpres Es.length (Nat.le_refl _)
  have hfilt_eq :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter
        (fun key => ∀ t ∈ recs, parityEq k r constants u i t (d t) key = false)) =
      ((Finset.univ : Finset (Fin (2 ^ k))).filter
        (fun key => ∀ j (hj : j < Es.length), Es[j] key = false)) := by
    ext key
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j hj
      have hjr : j < recs.length := by simp [Es] at hj; exact hj
      simp only [Es, List.getElem_map]
      exact h recs[j] (List.getElem_mem hjr)
    · intro h t ht
      rcases List.getElem_of_mem ht with ⟨j, hj, rfl⟩
      have hje : j < Es.length := by simp [Es]; exact hj
      simpa [Es] using h j hje
  rw [hfilt_eq]
  have hrec_ge : r - (3 * e + 2 * q + 2) ≤ Es.length := by
    have hlenE : Es.length = recs.length := by simp [Es]
    rw [hlenE]
    have hge := recList_length_ge d cut ((r - e) - cut) (e + q - 1)
      (by simpa [d, dOf] using hle 0 (by omega))
      (by
        intro j hj
        have hd1 := hdec j (by omega)
        dsimp only [d, dOf]
        have he1 : cut + j + 1 - cut = j + 1 := by omega
        have he2 : cut + j - cut = j := by omega
        rw [he1, he2]
        exact hd1)
    change (r - e) - cut - (e + q - 1) ≤ recs.length at hge
    dsimp only [cut] at hge
    omega
  set M := r - (3 * e + 2 * q + 2)
  have hMk : M ≤ k := by omega
  have hmul : 2 ^ M * ((Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun key => ∀ j (hj : j < Es.length), Es[j] key = false)).card ≤ 2 ^ M * 2 ^ (k - M) := by
    have hpow_le : 2 ^ M ≤ 2 ^ Es.length := Nat.pow_le_pow_right (by omega) hrec_ge
    have hstep1 := Nat.mul_le_mul_right
      ((Finset.univ : Finset (Fin (2 ^ k))).filter
        (fun key => ∀ j (hj : j < Es.length), Es[j] key = false)).card hpow_le
    rw [hcard_eq] at hstep1
    have hpow_add : 2 ^ M * 2 ^ (k - M) = 2 ^ k := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hpow_add]
    exact hstep1
  exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos M)

private theorem solve_25515 (k r e q : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hu : u < 2 ^ k) (hi : i < k) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
      ∃ mask : Fin (2 ^ q),
        (preWord k constants u base.val r).testBit i ≠
          (preWord k constants u
            (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i)).card ≤
      Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
  let cut := e + q + 3
  let L := (r - e) - cut + 1
  let B := e + q - 1
  let H : Finset (List Nat) := (decLists L B).toFinset
  let Fiber : List Nat → Finset (Fin (2 ^ k)) := fun xs =>
    (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun key => ∀ t ∈ recList (dOf cut xs) cut ((r - e) - cut),
        parityEq k r constants u i t (dOf cut xs t) key = false)
  have hsub :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          (preWord k constants u base.val r).testBit i ≠
            (preWord k constants u
              (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i)) ⊆
      H.biUnion Fiber := by
    intro base hbase
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbase
    rcases hbase with ⟨mask, hdiff⟩
    rcases exists_history k r e q constants u i hq hr hk hu hi base mask hdiff with
      ⟨d, hd_bd, hd_mono, hd_par⟩
    let xs : List Nat := (List.range L).map (fun j => d (cut + j))
    have hxs_get : ∀ j, j < L → xs.getD j 0 = d (cut + j) := by
      intro j hj
      simp only [xs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
        Option.map_some, Option.getD_some]
    have hxs_mem : xs ∈ decLists L B := by
      apply mem_decLists L B xs (by simp [xs])
      · intro j hj
        rw [hxs_get j hj]
        have hbd := (hd_bd (cut + j) (by omega) (by omega)).1
        omega
      · intro j hj
        rw [hxs_get (j + 1) hj, hxs_get j (by omega)]
        have hm := hd_mono (cut + j + 1) (by omega) (by omega)
        have he : cut + j + 1 - 1 = cut + j := by omega
        rw [he] at hm
        have he2 : cut + (j + 1) = cut + j + 1 := by omega
        rw [he2]
        exact hm
    have hdOf_eq : ∀ t, cut ≤ t → t ≤ r - e → dOf cut xs t = d t := by
      intro t h1 h2
      dsimp only [dOf]
      rw [hxs_get (t - cut) (by omega)]
      congr 1
      omega
    rw [Finset.mem_biUnion]
    refine ⟨xs, List.mem_toFinset.mpr hxs_mem, ?_⟩
    simp only [Fiber, Finset.mem_filter, Finset.mem_univ, true_and]
    intro t ht
    rcases (mem_recList (dOf cut xs) cut ((r - e) - cut) t).mp ht with ⟨ht1, ht2, htrec⟩
    rw [hdOf_eq t (by omega) (by omega)]
    apply hd_par t ht1 (by omega)
    intro s hs1 hs2
    have h1 := htrec s hs1 hs2
    rw [hdOf_eq s hs1 (by omega), hdOf_eq t (by omega) (by omega)] at h1
    exact h1
  have h1 :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          (preWord k constants u base.val r).testBit i ≠
            (preWord k constants u
              (base.val ^^^ rot k (i + 3 * r + k - e - q) mask.val) r).testBit i)).card ≤
      (H.biUnion Fiber).card := Finset.card_le_card hsub
  have h2 : (H.biUnion Fiber).card ≤ ∑ xs ∈ H, (Fiber xs).card := Finset.card_biUnion_le
  have h3 : ∑ xs ∈ H, (Fiber xs).card ≤
      ∑ _xs ∈ H, 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
    apply Finset.sum_le_sum
    intro xs hxs
    exact card_fiber_le constants hq hr hk hu xs (List.mem_toFinset.mp hxs)
  have h4 : ∑ _xs ∈ H, 2 ^ (k - (r - (3 * e + 2 * q + 2))) =
      H.card * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
    simp
  have hH_card : H.card ≤ Nat.choose (r + (e + q) + 1) (e + q) := by
    have hc1 : H.card ≤ (decLists L B).length := List.toFinset_card_le _
    rw [decLists_length] at hc1
    have hc2 : Nat.choose (L + B) B ≤ Nat.choose (L + B + 1) (B + 1) := by
      rw [Nat.choose_succ_succ]
      omega
    have hc3 : Nat.choose (L + B + 1) (B + 1) ≤ Nat.choose (r + (e + q) + 1) (e + q) := by
      have hB : B + 1 = e + q := by omega
      rw [hB]
      exact Nat.choose_le_choose (e + q) (by omega)
    exact Nat.le_trans hc1 (Nat.le_trans hc2 hc3)
  calc
    _ ≤ (H.biUnion Fiber).card := h1
    _ ≤ ∑ xs ∈ H, (Fiber xs).card := h2
    _ ≤ ∑ _xs ∈ H, 2 ^ (k - (r - (3 * e + 2 * q + 2))) := h3
    _ = H.card * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := h4
    _ ≤ Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) :=
      Nat.mul_le_mul_right _ hH_card

end PEqualNP.Outside.L_meta_25515_aux

theorem PEqualNP.Outside.L_meta_25515 :
    ∀ (k r e q : ℕ) (constants : ℕ → Fin (2 ^ k)) (u i : ℕ),
      0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r → u < 2 ^ k → i < k →
      let rot := fun (s word : ℕ) =>
        ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
      let step := fun (word : ℕ) =>
        (List.range k).foldl (fun acc b =>
          acc ||| ((xor (word.testBit b)
            (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
      let state := fun (key rounds : ℕ) =>
        (List.range rounds).foldl (fun prev t =>
          step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
            (constants (t + 1)).val) (rot 1 key ^^^ u)
      let before := fun subject : ℕ =>
        let prev := state subject (r - 1)
        (step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev)).testBit i
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val))).card ≤
        Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
  intro k r e q constants u i hq hr hk hu hi rot step state before
  have hstep : ∀ w, step w = PEqualNP.Outside.L_meta_25515_aux.wordStep k w := fun w =>
    (PEqualNP.Outside.L_meta_25515_aux.wordStep_eq k w).symm
  have hstate : ∀ key rounds,
      state key rounds = PEqualNP.Outside.L_meta_25515_aux.stateRec k constants u key rounds := by
    intro key rounds
    dsimp only [state]
    have hfn :
        (fun prev t =>
          step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
            (constants (t + 1)).val) =
        (fun prev t =>
          PEqualNP.Outside.L_meta_25515_aux.wordStep k
            (PEqualNP.Outside.L_meta_25515_aux.mix k prev) ^^^
            PEqualNP.Outside.L_meta_25515_aux.rot k (2 * t) key ^^^
            (constants (t + 1)).val) := by
      funext prev t
      rw [hstep]
      rfl
    rw [hfn]
    exact PEqualNP.Outside.L_meta_25515_aux.stateRec_eq_fold k constants u key rounds
  have hbefore : ∀ subject,
      before subject =
        (PEqualNP.Outside.L_meta_25515_aux.preWord k constants u subject r).testBit i := by
    intro subject
    dsimp only [before]
    rw [hstate, hstep]
    rfl
  have hfilt :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val))) =
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun base =>
        ∃ mask : Fin (2 ^ q),
          (PEqualNP.Outside.L_meta_25515_aux.preWord k constants u base.val r).testBit i ≠
            (PEqualNP.Outside.L_meta_25515_aux.preWord k constants u
              (base.val ^^^ PEqualNP.Outside.L_meta_25515_aux.rot k (i + 3 * r + k - e - q)
                mask.val) r).testBit i)) := by
    ext base
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨mask, h⟩
      refine ⟨mask, ?_⟩
      rw [← hbefore, ← hbefore]
      exact h
    · rintro ⟨mask, h⟩
      refine ⟨mask, ?_⟩
      rw [hbefore, hbefore]
      exact h
  rw [hfilt]
  exact PEqualNP.Outside.L_meta_25515_aux.solve_25515 k r e q constants u i hq hr hk hu hi
