import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25520_aux

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
    (hδ : δ < e + q) (hδ' : δ' ≤ δ) (hrec : t + δ ≤ t' + δ')
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

private def exactWeight : Nat → Nat → List (List Bool)
  | 0, 0 => [[]]
  | 0, _ + 1 => []
  | n + 1, 0 => [List.replicate (n + 1) false]
  | n + 1, d + 1 =>
      (exactWeight n (d + 1)).map (false :: ·) ++ (exactWeight n d).map (true :: ·)

private theorem exactWeight_length : ∀ n d, (exactWeight n d).length = Nat.choose n d
  | 0, 0 => by simp [exactWeight]
  | 0, d + 1 => by simp [exactWeight]
  | n + 1, 0 => by simp [exactWeight]
  | n + 1, d + 1 => by
    simp only [exactWeight, List.length_append, List.length_map,
      exactWeight_length n (d + 1), exactWeight_length n d]
    rw [Nat.choose_succ_succ n d, Nat.add_comm]

private theorem mem_exactWeight : ∀ n d (w : List Bool),
    w ∈ exactWeight n d ↔ w.length = n ∧ w.count true = d
  | 0, 0, w => by
    cases w <;> simp [exactWeight]
  | 0, d + 1, w => by
    cases w <;> simp [exactWeight]
  | n + 1, 0, w => by
    simp only [exactWeight, List.mem_singleton]
    constructor
    · rintro rfl
      simp [List.count_replicate]
    · rintro ⟨hlen, hcnt⟩
      apply List.ext_getElem (by simp [hlen])
      intro j hj1 hj2
      simp only [List.getElem_replicate]
      cases hval : w[j] with
      | false => rfl
      | true =>
        have hmem : true ∈ w := by
          rw [← hval]
          exact List.getElem_mem hj1
        have hpos : 0 < w.count true := List.count_pos_iff.mpr hmem
        omega
  | n + 1, d + 1, w => by
    simp only [exactWeight, List.mem_append, List.mem_map]
    cases w with
    | nil => simp
    | cons b tl =>
      cases b with
      | false =>
        simp [mem_exactWeight n (d + 1) tl]
      | true =>
        simp [mem_exactWeight n d tl]

private def lowWeight (n D : Nat) : List (List Bool) :=
  (List.range (D + 1)).flatMap (exactWeight n)

private theorem mem_lowWeight (n D : Nat) (w : List Bool) :
    w ∈ lowWeight n D ↔ w.length = n ∧ w.count true ≤ D := by
  unfold lowWeight
  simp only [List.mem_flatMap, List.mem_range, mem_exactWeight]
  constructor
  · rintro ⟨d, hd, hlen, hcnt⟩
    exact ⟨hlen, by omega⟩
  · rintro ⟨hlen, hle⟩
    exact ⟨w.count true, by omega, hlen, rfl⟩

private theorem lowWeight_length (n D : Nat) :
    (lowWeight n D).length = ∑ j ∈ Finset.range (D + 1), Nat.choose n j := by
  unfold lowWeight
  induction D with
  | zero =>
    simp [exactWeight_length]
  | succ D ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, exactWeight_length,
        Finset.sum_range_succ (fun j => Nat.choose n j) (D + 1)]

private def greedyTrace (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i cut D : Nat)
    (key : Fin (2 ^ k)) : Nat → List Bool
  | 0 => []
  | s + 1 =>
      let prev := greedyTrace k r constants u i cut D key s
      let ones := prev.count true
      let ans := if ones ≤ D then parityEq k r constants u i (cut + 1 + s) (D - ones) key else false
      prev ++ [ans]

private theorem greedyTrace_length (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i cut D : Nat)
    (key : Fin (2 ^ k)) : ∀ s, (greedyTrace k r constants u i cut D key s).length = s
  | 0 => rfl
  | s + 1 => by
    simp [greedyTrace, greedyTrace_length k r constants u i cut D key s]

private theorem greedyTrace_count_le_len (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i cut D : Nat)
    (key : Fin (2 ^ k)) (s : Nat) :
    (greedyTrace k r constants u i cut D key s).count true ≤ s := by
  have h := List.count_le_length (a := true) (l := greedyTrace k r constants u i cut D key s)
  rw [greedyTrace_length] at h
  exact h

private theorem greedyTrace_eq_take_iff (k r : Nat) (constants : Nat → Fin (2 ^ k)) (u i cut D : Nat)
    (key : Fin (2 ^ k)) (w : List Bool) (hwc : w.count true ≤ D) :
    ∀ s (hs : s ≤ w.length),
      (greedyTrace k r constants u i cut D key s = w.take s ↔
        ∀ a (ha : a < s),
          parityEq k r constants u i (cut + 1 + a) (D - (w.take a).count true) key = w[a]'(by omega))
  | 0, _ => by simp [greedyTrace]
  | s + 1, hs => by
    have ih := greedyTrace_eq_take_iff k r constants u i cut D key w hwc s (by omega)
    have htake : w.take (s + 1) = w.take s ++ [w[s]'(by omega)] := List.take_succ_eq_append_getElem (by omega)
    have hcnt_le : (w.take s).count true ≤ D := by
      have hsub : (w.take s).count true ≤ w.count true := by
        have hsp : w = w.take s ++ w.drop s := (List.take_append_drop s w).symm
        conv_rhs => rw [hsp]
        rw [List.count_append]
        omega
      omega
    rw [greedyTrace, htake]
    constructor
    · intro heq
      have hlen1 : (greedyTrace k r constants u i cut D key s).length = (w.take s).length := by
        rw [greedyTrace_length, List.length_take]
        omega
      have hsplit := List.append_inj heq hlen1
      have hprev := ih.mp hsplit.1
      have hlast : (if (greedyTrace k r constants u i cut D key s).count true ≤ D then
          parityEq k r constants u i (cut + 1 + s)
            (D - (greedyTrace k r constants u i cut D key s).count true) key
          else false) = w[s]'(by omega) := by
        simpa using hsplit.2
      rw [hsplit.1, if_pos hcnt_le] at hlast
      intro a ha
      by_cases has : a = s
      · subst has; exact hlast
      · exact hprev a (by omega)
    · intro hall
      have hprev : greedyTrace k r constants u i cut D key s = w.take s :=
        ih.mpr (fun a ha => hall a (by omega))
      rw [hprev, if_pos hcnt_le, hall s (by omega)]

private theorem greedyTrace_good_of_history (k r e q : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (base : Fin (2 ^ k)) (d : Nat → Nat)
    (hd_bd : ∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t))
    (hd_mono : ∀ t, e + q + 3 < t → t ≤ r → d t ≤ d (t - 1))
    (hd_par : ∀ t, e + q + 3 < t → t ≤ r - e →
      (∀ s, e + q + 3 ≤ s → s < t → s + d s < t + d t) →
      parityEq k r constants u i t (d t) base = false) :
    let cut := e + q + 3
    let N := (r - e) - cut
    let D := e + q - 1
    (greedyTrace k r constants u i cut D base N).count true ≤ D := by
  intro cut N D
  have hinv : ∀ s, s ≤ N →
      runMax d cut s < cut + 1 + D + (s - (greedyTrace k r constants u i cut D base s).count true) := by
    intro s
    induction s with
    | zero =>
      intro _
      simp only [runMax, greedyTrace, List.count_nil, Nat.sub_zero, Nat.add_zero]
      have h0 := (hd_bd cut (Nat.le_refl _) (by omega)).1
      omega
    | succ s ih =>
      intro hs
      have hih := ih (by omega)
      have hrm_ge : cut + s ≤ runMax d cut s := by
        have h := le_runMax d cut s s (Nat.le_refl s)
        omega
      have hcnt_le_s := greedyTrace_count_le_len k r constants u i cut D base s
      have hones_le : (greedyTrace k r constants u i cut D base s).count true ≤ D := by omega
      set ones := (greedyTrace k r constants u i cut D base s).count true
      set t := cut + 1 + s
      have hdt_step : t + d t ≤ runMax d cut s + 1 := by
        have hprev := le_runMax d cut s s (Nat.le_refl s)
        have hmon := hd_mono t (by omega) (by omega)
        have hsub : t - 1 = cut + s := by omega
        rw [hsub] at hmon
        omega
      have hstep_eq : greedyTrace k r constants u i cut D base (s + 1) =
          greedyTrace k r constants u i cut D base s ++
            [parityEq k r constants u i t (D - ones) base] := by
        simp only [greedyTrace, ones, t, hones_le, ↓reduceIte]
      rw [hstep_eq, List.count_append]
      cases hans : parityEq k r constants u i t (D - ones) base with
      | false =>
        have hc0 : [false].count true = 0 := rfl
        rw [hc0, Nat.add_zero]
        simp only [runMax]
        have he : cut + s + 1 = t := by omega
        rw [he]
        omega
      | true =>
        have hc1 : [true].count true = 1 := rfl
        rw [hc1]
        have hlt_t : t + d t < cut + 1 + D + (s - ones) := by
          by_contra hge
          have heq_t : t + d t = cut + 1 + D + (s - ones) := by omega
          have hrec : ∀ u', cut ≤ u' → u' < t → u' + d u' < t + d t := by
            intro u' hu1 hu2
            have hle := le_runMax d cut s (u' - cut) (by omega)
            have heu : cut + (u' - cut) = u' := by omega
            rw [heu] at hle
            omega
          have hpar := hd_par t (by omega) (by omega) hrec
          have hdeq : d t = D - ones := by omega
          rw [hdeq] at hpar
          rw [hpar] at hans
          cases hans
        simp only [runMax]
        have he : cut + s + 1 = t := by omega
        rw [he]
        omega
  have hN := hinv N (Nat.le_refl N)
  have hrmN : cut + N ≤ runMax d cut N := by
    have h := le_runMax d cut N N (Nat.le_refl N)
    omega
  have hcntN := greedyTrace_count_le_len k r constants u i cut D base N
  omega


namespace GateBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

variable {α : Type*}

private def Scheduled (n : Nat) (F : α → (Fin n → Bool) → Bool) (k : Nat) (S : Set α) : Prop :=
  ∃ gs : List Gate, gs.length = k ∧ ReadsBack n ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x

private theorem wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem start {n : Nat} {F : α → (Fin n → Bool) → Bool}
    (input : Fin n → α) (h : ∀ i x, F (input i) x = x i) :
    Scheduled n F 0 (Set.range input) := by
  refine ⟨[], rfl, ?_, ?_, ?_⟩
  · simp [ReadsBack]
  · simp [FanInTwo]
  · intro a ha
    obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
    refine ⟨i.val, by simp, fun x => ?_⟩
    change (List.ofFn x).getD i.val false = F (input i) x
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, h i x]

private theorem restrict {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S T : Set α}
    (h : Scheduled n F k S) (hsub : T ⊆ S) : Scheduled n F k T := by
  obtain ⟨gs, hs, hr, hf, hw⟩ := h
  exact ⟨gs, hs, hr, hf, fun a ha => hw a (hsub ha)⟩

private theorem realizeDeps {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < n + k ∧
      ∀ x : Fin n → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = F a x)
    (deps : List α) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < n + k) ∧
      ∀ x : Fin n → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => F a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

private theorem push {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α}
    (h : Scheduled n F k S) (op : GateOp) (deps : List α) (out : α)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, F out x = op.eval (deps.map fun a => F a x)) :
    Scheduled n F (k + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin n → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = n + k := by
    rw [wireLength]
    simpa using congrArg (n + ·) hgs
  have hsnoc (x : Fin n → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [F out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    change g' ∈ gs ++ [g] at hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · have heq : g' = g := List.mem_singleton.mp hg'
      subst g'
      refine ⟨hop, ?_⟩
      change is.length ≤ 2
      simpa only [his] using hlen
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨n + k, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

private theorem finish {n k : Nat} {F : α → (Fin n → Bool) → Bool} {S : Set α} {out : α}
    (h : Scheduled n F k S) (hout : out ∈ S) :
    ∃ C : Circuit, C.size = k ∧ ReadsBack n C ∧ FanInTwo C ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F out x := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨i, _, hi⟩ := hw out hout
  exact ⟨⟨gs, i⟩, hgs, hr, hf, hi⟩

end GateBridge

namespace Build25533

open PEqualNP.CircuitLowerBounds

variable {n : Nat}
private abbrev Sig (n : Nat) := (Fin n → Bool) → Bool

private def Build (A B : Set (Sig n)) (b : Nat) : Prop :=
  True ∧ (∀ {m S}, GateBridge.Scheduled n id m S → A ⊆ S →
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B))

private theorem Build.run {A B : Set (Sig n)} {b m S} (H : Build A B b)
    (HS : GateBridge.Scheduled n id m S) (hA : A ⊆ S) :
    ∃ c ≤ b, GateBridge.Scheduled n id (m + c) (S ∪ B) := H.2 HS hA

private theorem idle {A B : Set (Sig n)} (h : B ⊆ A) : Build A B 0 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨0, Nat.le_refl _, ?_⟩
  simpa [Set.union_eq_left.mpr (h.trans hA)] using HS

private theorem relax {A B C D : Set (Sig n)} {b d : Nat}
    (H : Build A B b) (hA : A ⊆ C) (hB : D ⊆ B) (h : b ≤ d) : Build C D d := by
  refine ⟨trivial, ?_⟩
  intro m S HS hC
  obtain ⟨c, hc, HS'⟩ := H.run HS (hA.trans hC)
  exact ⟨c, hc.trans h, GateBridge.restrict HS' (Set.union_subset_union le_rfl hB)⟩

private theorem seq {A B C : Set (Sig n)} {b c : Nat}
    (H : Build A B b) (J : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  obtain ⟨d, hd, K⟩ := H.run HS hA
  obtain ⟨e, he, K'⟩ := J.run K (Set.union_subset_union hA le_rfl)
  exact ⟨d + e, Nat.add_le_add hd he, by simpa [Nat.add_assoc, Set.union_assoc] using K'⟩

private theorem one {A : Set (Sig n)} (op : GateOp) (deps : List (Sig n))
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : deps.length ≤ 2)
    (hd : ∀ g ∈ deps, g ∈ A) (f : Sig n)
    (hv : ∀ x, f x = op.eval (deps.map fun g => g x)) : Build A {f} 1 := by
  refine ⟨trivial, ?_⟩
  intro m S HS hA
  refine ⟨1, le_rfl, ?_⟩
  have h := GateBridge.push HS op deps f hop hlen (fun g hg => hA (hd g hg)) hv
  rw [Set.insert_eq] at h
  exact GateBridge.restrict h (by intro g hg; exact hg.elim Or.inr Or.inl)

private def an (f g : Sig n) : Sig n := fun x => f x && g x
private def or (f g : Sig n) : Sig n := fun x => f x || g x
private def nt (f : Sig n) : Sig n := fun x => !f x
private def xo (f g : Sig n) : Sig n := fun x => xor (f x) (g x)

private theorem andG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {an f g} 1 :=
  one .and [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, an])

private theorem orG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {or f g} 1 :=
  one .or [f, g] (by simp) (by simp) (by simpa using And.intro hf hg) _ (by simp [GateOp.eval, or])

private theorem notG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) : Build A {nt f} 1 :=
  one .not [f] (by simp) (by simp) (by simpa using hf) _ (by simp [GateOp.eval, nt])

private theorem xorG {A : Set (Sig n)} {f g : Sig n} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {xo f g} 4 := by
  have he : xo f g = an (or f g) (nt (an f g)) := by
    funext x
    change xor (f x) (g x) = ((f x || g x) && !(f x && g x))
    cases f x <;> cases g x <;> rfl
  rw [he]
  have h1 := andG hf hg
  have h2 := orG (A := A ∪ {an f g}) (Or.inl hf) (Or.inl hg)
  have h3 := notG (A := A ∪ ({an f g} ∪ {or f g})) (f := an f g) (by simp)
  have h4 := andG (A := A ∪ (({an f g} ∪ {or f g}) ∪ {nt (an f g)}))
    (f := or f g) (g := nt (an f g)) (by simp) (by simp)
  exact relax (seq (seq (seq h1 h2) h3) h4) le_rfl (by simp) le_rfl

private theorem constG {A : Set (Sig n)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b
  · exact one .or [] (by simp) (by simp) (by simp) _ (by intro; rfl)
  · exact one .and [] (by simp) (by simp) (by simp) _ (by intro; rfl)

private theorem mixG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) : Build A {xo (xo f g) h} 8 := by
  exact relax (seq (xorG hf hg)
    (xorG (A := A ∪ {xo f g}) (f := xo f g) (by simp) (Or.inl hh))) le_rfl (by simp) le_rfl

private theorem nonlinG {A : Set (Sig n)} {f g h : Sig n}
    (hf : f ∈ A) (hg : g ∈ A) (hh : h ∈ A) :
    Build A {xo f (an (nt g) h)} 6 := by
  have h1 := notG hg
  have h2 := andG (A := A ∪ {nt g}) (f := nt g) (by simp) (Or.inl hh)
  have h3 := xorG (A := A ∪ ({nt g} ∪ {an (nt g) h})) (Or.inl hf)
    (g := an (nt g) h) (by simp)
  exact relax (seq (seq h1 h2) h3) le_rfl (by simp) le_rfl

private theorem flipG {A : Set (Sig n)} {f : Sig n} (hf : f ∈ A) (b : Bool) :
    Build A {fun x => xor (f x) b} 1 := by
  cases b
  · have he : (fun x => xor (f x) false) = f := by funext x; cases f x <;> rfl
    rw [he]
    exact relax (idle (Set.singleton_subset_iff.mpr hf)) le_rfl le_rfl (by omega)
  · have he : (fun x => xor (f x) true) = nt f := by
      funext x
      change xor (f x) true = !f x
      cases f x <;> rfl
    rw [he]
    exact notG hf

private theorem pivotG {A : Set (Sig n)} {a b c u : Sig n}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hu : u ∈ A) (d : Bool) :
    Build A {fun w => xor (xor (xor (a w) (!(b w) && c w)) (u w)) d} 11 := by
  let f := xo a (an (nt b) c)
  have H1 : Build A {f} 6 := nonlinG ha hb hc
  let g := xo f u
  have H2 : Build (A ∪ {f}) {g} 4 := xorG (Or.inr rfl) (Or.inl hu)
  have H3 := flipG (A := A ∪ ({f} ∪ {g})) (f := g) (by simp) d
  exact relax (seq (seq H1 H2) H3) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

private theorem listBuild {α : Type*} {A : Set (Sig n)} (xs : List α)
    (F : α → Sig n) (c : Nat) (H : ∀ a ∈ xs, Build A {F a} c) :
    Build A {f | ∃ a ∈ xs, f = F a} (xs.length * c) := by
  induction xs with
  | nil =>
    exact relax (idle (A := A) (B := ∅) (by simp)) le_rfl (by simp) (by simp)
  | cons a xs ih =>
    have h1 := H a List.mem_cons_self
    have h2 := ih (fun b hb => H b (List.mem_cons_of_mem a hb))
    have h2' := relax h2 (C := A ∪ {F a}) Set.subset_union_left le_rfl le_rfl
    refine relax (seq h1 h2') le_rfl ?_ ?_
    · rintro f ⟨b, hb, rfl⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl rfl
      · exact Or.inr ⟨b, hb, rfl⟩
    · simp only [List.length_cons]
      rw [Nat.succ_mul, Nat.add_comm]

private theorem finG {k : Nat} {A : Set (Sig n)} (F : Fin k → Sig n) (c : Nat)
    (H : ∀ i, Build A {F i} c) : Build A (Set.range F) (k * c) := by
  have h := listBuild (List.finRange k) F c (fun i _ => H i)
  rw [List.length_finRange] at h
  refine relax h le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact ⟨i, List.mem_finRange i, rfl⟩

private theorem anyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    exact idle (Set.singleton_subset_iff.mpr hfalse)
  | cons f xs IH =>
    have H := IH (fun g hg => hs g (List.mem_cons_of_mem f hg))
    have K := orG (A := A ∪ {fun x => xs.any (fun g => g x)})
      (Or.inl (hs f List.mem_cons_self)) (Or.inr rfl)
    exact relax (seq H K) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) (by simp)

private theorem notAnyG {A : Set (Sig n)} (xs : List (Sig n))
    (hs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => !(xs.any (fun f => f x))} (xs.length + 1) :=
  relax (seq (anyG xs hs hfalse) (notG (f := fun x => xs.any (fun f => f x))
    (Or.inr rfl))) le_rfl (Set.singleton_subset_iff.mpr (Or.inr rfl)) le_rfl

end Build25533

namespace Circuit25533

open Build25533
open PEqualNP.MetaComplexity (tableIndex)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private theorem pack_succ {n : Nat} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
        + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem pack_lt : ∀ {n : Nat} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n IH =>
    intro x
    rw [pack_succ, pow_succ]
    have := IH (fun i : Fin n => x i.castSucc)
    split <;> omega

private theorem bit_pack : ∀ {n : Nat} (x : Fin n → Bool) (i : Fin n),
    (tableIndex x).testBit i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n IH =>
    intro x i
    have hlt := pack_lt (fun i : Fin n => x i.castSucc)
    rw [pack_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · change (tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2 ^ n else 0)).testBit j.val = x j.castSucc
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero]; exact IH _ j
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]; exact IH _ j

private theorem lt_two_pow_iff_testBit {n k a : Nat} (hn : n < 2 ^ k) :
    n < 2 ^ a ↔ ∀ i, a ≤ i → i < k → n.testBit i = false := by
  constructor
  · intro ha i hai _
    exact Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hai))
  · intro h
    apply lt_two_pow_of_bits
    intro i hai
    by_cases hi : i < k
    · exact h i hai hi
    · exact Nat.testBit_lt_two_pow
        (hn.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hi)))

private theorem xor_lt {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply lt_two_pow_of_bits
  intro j hj
  have hp := Nat.pow_le_pow_right Nat.zero_lt_two hj
  rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hp), Nat.testBit_lt_two_pow (hb.trans_le hp)]
  rfl

private def consts (k : Nat) : Nat → Fin (2 ^ k) :=
  fun j => ⟨3 ^ (k + j) % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private def updateRound (k d e t w state : Nat) : Nat :=
  wordStep k (state ^^^ rot k d state ^^^ rot k (k - d) state) ^^^ rot k e w ^^^ (consts k t).val

private def rowWord (k w u : Nat) : Nat → Nat :=
  stateRec k (consts k) u w

private def colWord (k r w v : Nat) : Nat → Nat
  | 0 => rot k 3 w ^^^ v
  | t + 1 => updateRound k 2 (3 * (t + 1) + 1) (r + (t + 1)) w (colWord k r w v t)

private theorem upd_lt (k d e t w state : Nat) : updateRound k d e t w state < 2 ^ k :=
  xor_lt (xor_lt (wordStep_lt _ _) rot_lt) (consts k t).isLt

private theorem rowWord_lt {k w u : Nat} (hu : u < 2 ^ k) (t : Nat) : rowWord k w u t < 2 ^ k :=
  stateRec_lt (consts k) hu t

private theorem colWord_lt {k r w v : Nat} (hv : v < 2 ^ k) (t : Nat) : colWord k r w v t < 2 ^ k := by
  cases t
  · exact xor_lt rot_lt hv
  · exact upd_lt ..

private theorem round_fold {α : Type*} (f : Nat → α) (op : α → Nat → α)
    (hf : ∀ j, f (j + 1) = op (f j) j) (t : Nat) :
    (List.range t).foldl op (f 0) = f t := by
  induction t with
  | zero => rfl
  | succ t IH => rw [List.range_succ, List.foldl_append, IH, List.foldl_cons, List.foldl_nil, hf]

private def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩
private def bits {k n : Nat} (w : (Fin n → Bool) → Nat) (i : Fin k) : Sig n :=
  fun v => (w v).testBit i
private def prev {k : Nat} (hk : 0 < k) (i : Fin k) (d : Nat) : Fin k := ix hk (i.val + k - d % k)

private theorem rotG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    {w : (Fin n → Bool) → Nat} (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, bits w i ∈ A)
    (d : Nat) (i : Fin k) : bits (fun v => rot k d (w v)) i ∈ A := by
  convert hs (prev hk i d) using 1
  funext v
  exact bit_rot (s := d) (hw v) i.isLt

private theorem xorBits {k n : Nat} {A : Set (Sig n)} {w u : (Fin n → Bool) → Nat} (i : Fin k)
    (hw : bits w i ∈ A) (hu : bits u i ∈ A) :
    Build A {bits (fun v => w v ^^^ u v) i} 4 := by
  have he : bits (fun v => w v ^^^ u v) i = xo (bits w i) (bits u i) := by
    funext v; exact Nat.testBit_xor ..
  rw [he]; exact xorG hw hu

private theorem roundG {k n : Nat} (hk : 0 < k) {A : Set (Sig n)} (d : Nat)
    (w s : (Fin n → Bool) → Nat) (hw : ∀ v, w v < 2 ^ k) (hs : ∀ v, s v < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hS : ∀ i : Fin k, bits s i ∈ A) (e t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun v => updateRound k d e t (w v) (s v)) i)) (19 * k) := by
  let w1 := fun v => s v ^^^ rot k d (s v) ^^^ rot k (k - d) (s v)
  let F := fun i : Fin k => bits w1 i
  have H : Build A (Set.range F) (k * 8) := finG F 8 fun i => by
    have E : F i = xo (xo (bits s i) (bits (fun v => rot k d (s v)) i))
        (bits (fun v => rot k (k - d) (s v)) i) := by
      funext v; simp only [F, bits, w1, Nat.testBit_xor, xo]
    rw [E]
    exact mixG (hS i) (rotG hk hs hS d i) (rotG hk hs hS (k - d) i)
  let G := fun i : Fin k => bits (fun v => updateRound k d e t (w v) (s v)) i
  have J : Build (A ∪ Set.range F) (Set.range G) (k * 11) := finG G 11 fun i => by
    have E : G i = (fun v => xor (xor (xor (F i v) (!(F (ix hk (i.val + 1)) v) && F (ix hk (i.val + 2)) v))
      (bits (fun v => rot k e (w v)) i v)) ((consts k t).val.testBit i)) := by
      funext v
      simp only [G, bits, updateRound, Nat.testBit_xor, testBit_wordStep i.isLt]
      simp only [F, bits, w1, ix, Nat.testBit_xor]
    rw [E]
    exact pivotG (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩)
      (Or.inl (rotG hk hw hW e i)) _
  exact relax (seq H J) le_rfl Set.subset_union_right (by omega)

private theorem rowSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (w u : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hu : ∀ x, u x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hU : ∀ i : Fin k, bits u i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm] using (finG (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) 0) i) 4
      (fun i => xorBits i (rotG hk hw hW 1 i) (hU i)))
  | succ t IH =>
    have H := roundG hk 1 (A := A ∪ Set.range (fun i : Fin k => bits (fun x => rowWord k (w x) (u x) t) i))
      w (fun x => rowWord k (w x) (u x) t) hw
      (fun x => rowWord_lt (hu x) t) (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩)
      (2 * t) (t + 1)
    have hbd : 4 * k + 19 * k * t + 19 * k ≤ 4 * k + 19 * k * (t + 1) := by
      rw [Nat.mul_succ]
      omega
    exact relax (seq IH H) le_rfl Set.subset_union_right hbd

private theorem colSchedule {k n : Nat} (hk : 0 < k) {A : Set (Sig n)}
    (r : Nat) (w v : (Fin n → Bool) → Nat) (hw : ∀ x, w x < 2 ^ k) (hv : ∀ x, v x < 2 ^ k)
    (hW : ∀ i : Fin k, bits w i ∈ A) (hV : ∀ i : Fin k, bits v i ∈ A) (t : Nat) :
    Build A (Set.range (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) t) i)) (4 * k + 19 * k * t) := by
  induction t with
  | zero =>
    simpa [Nat.mul_comm] using (finG (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) 0) i) 4
      (fun i => xorBits i (rotG hk hw hW 3 i) (hV i)))
  | succ t IH =>
    have H := roundG hk 2 (A := A ∪ Set.range (fun i : Fin k => bits (fun x => colWord k r (w x) (v x) t) i))
      w (fun x => colWord k r (w x) (v x) t) hw
      (fun x => colWord_lt (hv x) t) (fun i => Or.inl (hW i)) (fun i => Or.inr ⟨i, rfl⟩)
      (3 * (t + 1) + 1) (r + (t + 1))
    have hbd : 4 * k + 19 * k * t + 19 * k ≤ 4 * k + 19 * k * (t + 1) := by
      rw [Nat.mul_succ]
      omega
    exact relax (seq IH H) le_rfl Set.subset_union_right hbd

private theorem thresholds {k n : Nat} {A : Set (Sig n)} (h : Nat) (w : (Fin n → Bool) → Nat)
    (hw : ∀ v, w v < 2 ^ k) (hs : ∀ i : Fin k, h ≤ i.val → bits w i ∈ A)
    (hfalse : (fun _ => false) ∈ A) : Build A {fun v => decide (w v < 2 ^ h)} (k + 1) := by
  let xs : List (Fin k) := (List.finRange k).filter (fun i => decide (h ≤ i.val))
  have hs' : ∀ f ∈ xs.map (bits w), f ∈ A := by
    intro f hf
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact hs i (by simpa [xs] using hi)
  have he : (fun v => !((xs.map (bits w)).any (fun f => f v))) = (fun v => decide (w v < 2 ^ h)) := by
    funext v
    apply Bool.eq_iff_iff.mpr
    rw [Bool.not_eq_true', decide_eq_true_eq, lt_two_pow_iff_testBit (hw v)]
    simp only [List.any_eq_false, List.mem_map, forall_exists_index, and_imp]
    constructor
    · intro H i hi hik
      exact Bool.eq_false_iff.mpr (H _ ⟨i, hik⟩ (by simp [xs, hi]) rfl)
    · intro H f i hi he
      subst f
      exact Bool.eq_false_iff.mp (H _ (by simpa [xs] using hi) i.isLt)
  rw [← he]
  refine relax (notAnyG _ hs' hfalse) le_rfl le_rfl (Nat.succ_le_succ ?_)
  simpa [xs] using (List.length_filter_le (p := fun i : Fin k => decide (h ≤ i.val)) (List.finRange k))

private def setBit (k w p : Nat) (b : Bool) : Nat :=
  tableIndex (fun i : Fin k => if i.val = p then b else w.testBit i.val)

private theorem setBit_lt {k w p : Nat} {b : Bool} : setBit k w p b < 2 ^ k := pack_lt _

private theorem testBit_setBit {k w p i : Nat} {b : Bool} (hi : i < k) :
    (setBit k w p b).testBit i = if i = p then b else w.testBit i :=
  bit_pack (fun j : Fin k => if j.val = p then b else w.testBit j.val) ⟨i, hi⟩

private def inputs (n : Nat) : Set (Sig n) := Set.range (fun i : Fin n => fun v => v i)
private def base (n : Nat) : Set (Sig n) := inputs n ∪ {fun _ => false, fun _ => true}

private theorem inputG (n : Nat) : Build (inputs n) {fun _ => false, fun _ => true} 2 := by
  simpa only [Set.singleton_union] using
    (seq (constG (A := inputs n) false) (constG (A := inputs n ∪ {fun _ => false}) true))

private def U (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.castAdd k i)
private def V (k : Nat) (v : Fin (k + k) → Bool) : Nat := tableIndex fun i : Fin k => v (Fin.natAdd k i)
private theorem U_lt (k : Nat) (v) : U k v < 2 ^ k := pack_lt _
private theorem V_lt (k : Nat) (v) : V k v < 2 ^ k := pack_lt _
private theorem bitU (k : Nat) (i : Fin k) : bits (U k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.castAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.castAdd k j)) i).symm⟩
private theorem bitV (k : Nat) (i : Fin k) : bits (V k) i ∈ base (k + k) :=
  Or.inl ⟨Fin.natAdd k i, funext fun v => (bit_pack (fun j : Fin k => v (Fin.natAdd k j)) i).symm⟩

private theorem constBit_mem {n : Nat} (b : Bool) : (fun _ : Fin n → Bool => b) ∈ base n := by
  cases b <;> exact Or.inr (by simp)

private theorem testSlotCircuit {k r : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (W : (Fin (k + k) → Bool) → Nat) (hWlt : ∀ v, W v < 2 ^ k)
    (hW : ∀ i : Fin k, bits W i ∈ A) (hU : ∀ i : Fin k, bits (U k) i ∈ A)
    (hV : ∀ i : Fin k, bits (V k) i ∈ A) (hf : (fun _ => false) ∈ A) :
    Build A {(fun v =>
      decide (rowWord k (W v) (U k v) r < 2 ^ (k - (k + 1) / 2)) &&
      decide (colWord k r (W v) (V k v) r < 2 ^ (k - (k + 1) / 2)))}
      (2 * (4 * k + 19 * k * r) + 2 * k + 3) := by
  let h := k - (k + 1) / 2
  let R := Set.range (fun i : Fin k => bits (fun v => rowWord k (W v) (U k v) r) i)
  have HR : Build A R (4 * k + 19 * k * r) := rowSchedule hk W (U k) hWlt (U_lt k) hW hU r
  let C := Set.range (fun i : Fin k => bits (fun v => colWord k r (W v) (V k v) r) i)
  have HC : Build (A ∪ R) C (4 * k + 19 * k * r) :=
    colSchedule hk r W (V k) hWlt (V_lt k) (fun i => Or.inl (hW i)) (fun i => Or.inl (hV i)) r
  let rl : Sig (k + k) := fun v => decide (rowWord k (W v) (U k v) r < 2 ^ h)
  let cl : Sig (k + k) := fun v => decide (colWord k r (W v) (V k v) r < 2 ^ h)
  have Hrl : Build (A ∪ (R ∪ C)) {rl} (k + 1) :=
    thresholds h _ (fun v => rowWord_lt (U_lt k v) r) (fun i _ => Or.inr (Or.inl ⟨i, rfl⟩)) (Or.inl hf)
  have Hcl : Build (A ∪ ((R ∪ C) ∪ {rl})) {cl} (k + 1) :=
    thresholds h _ (fun v => colWord_lt (V_lt k v) r) (fun i _ => Or.inr (Or.inl (Or.inr ⟨i, rfl⟩))) (Or.inl hf)
  have HA : Build (A ∪ (((R ∪ C) ∪ {rl}) ∪ {cl})) {an rl cl} 1 :=
    andG (f := rl) (g := cl) (by simp) (by simp)
  refine relax (seq (seq (seq (seq HR HC) Hrl) Hcl) HA) le_rfl Set.subset_union_right ?_
  omega

private def ordInit (k r q vis : Nat) : Nat :=
  let P0 := k - q - (2 * r - 2)
  tableIndex (fun i : Fin k =>
    if i.val < P0 then vis.testBit i.val
    else if P0 + q ≤ i.val then vis.testBit (i.val - q)
    else false)

private theorem ordInit_lt {k r q vis : Nat} : ordInit k r q vis < 2 ^ k := pack_lt _

private def ordDecode (k r q u : Nat) : Nat → Nat → Nat
  | 0, w => w
  | s + 1, w =>
    let w' := ordDecode k r q u s w
    let a := q - 1 - s
    let i := k - q + a
    let p := k - q - (2 * r - 2) + a
    setBit k w' p ((rowWord k w' u r).testBit i)

private theorem ordDecode_lt {k r q u s w : Nat} (hw : w < 2 ^ k) :
    ordDecode k r q u s w < 2 ^ k := by
  induction s with
  | zero => exact hw
  | succ s _ => exact setBit_lt

private theorem ordDecode_unchanged {k r q u s w m : Nat} (hm : m < k)
    (hs : s ≤ q) (hkr : q + (2 * r - 2) ≤ k)
    (hout : m < k - q - (2 * r - 2) + (q - s) ∨ k - (2 * r - 2) ≤ m) :
    (ordDecode k r q u s w).testBit m = w.testBit m := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [ordDecode]
    rw [testBit_setBit hm]
    have hne : m ≠ k - q - (2 * r - 2) + (q - 1 - s) := by omega
    simp only [hne, ↓reduceIte]
    exact ih (by omega) (by omega)

private theorem ordDecode_circuit {k r q : Nat} (hk : 0 < k) {A : Set (Sig (k + k))}
    (W0 : (Fin (k + k) → Bool) → Nat) (hW0lt : ∀ v, W0 v < 2 ^ k)
    (hW0 : ∀ i : Fin k, bits W0 i ∈ A) (hU : ∀ i : Fin k, bits (U k) i ∈ A)
    (hq : q ≤ k) (s : Nat) (hs : s ≤ q) :
    Build A (Set.range (fun i : Fin k => bits (fun v => ordDecode k r q (U k v) s (W0 v)) i))
      (s * (4 * k + 19 * k * r)) := by
  induction s with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by omega)
    rintro _ ⟨i, rfl⟩
    exact hW0 i
  | succ s ih =>
    let W' := fun v => ordDecode k r q (U k v) s (W0 v)
    let R' := Set.range (fun i : Fin k => bits W' i)
    have hW'lt : ∀ v, W' v < 2 ^ k := fun v => ordDecode_lt (hW0lt v)
    let RW := Set.range (fun i : Fin k => bits (fun v => rowWord k (W' v) (U k v) r) i)
    have HR : Build (A ∪ R') RW (4 * k + 19 * k * r) :=
      rowSchedule hk W' (U k) hW'lt (U_lt k) (fun i => Or.inr ⟨i, rfl⟩) (fun i => Or.inl (hU i)) r
    have hbd : s * (4 * k + 19 * k * r) + (4 * k + 19 * k * r) ≤ (s + 1) * (4 * k + 19 * k * r) := by
      rw [Nat.succ_mul s]
    refine relax (seq (ih (by omega)) HR) le_rfl ?_ hbd
    rintro _ ⟨m, rfl⟩
    let a := q - 1 - s
    let p := k - q - (2 * r - 2) + a
    let idx := k - q + a
    by_cases hmp : m.val = p
    · right
      refine ⟨⟨idx, by dsimp [idx, a]; omega⟩, ?_⟩
      funext v
      simp only [bits, ordDecode]
      rw [testBit_setBit m.isLt]
      simp only [show m.val = k - q - (2 * r - 2) + (q - 1 - s) from hmp, ↓reduceIte]
      rfl
    · left
      refine ⟨m, ?_⟩
      funext v
      simp only [bits, ordDecode]
      rw [testBit_setBit m.isLt]
      simp only [show ¬ m.val = k - q - (2 * r - 2) + (q - 1 - s) from hmp, ↓reduceIte]

private theorem rowWord_final_xor {k r w u i : Nat} (hr : 1 ≤ r) (hk : 2 * (r - 1) < k)
    (hw : w < 2 ^ k) (hi : i < k) :
    (rowWord k w u r).testBit i =
      xor (xor ((preWord k (consts k) u w r).testBit i) ((consts k r).val.testBit i))
        (w.testBit ((i + k - 2 * (r - 1)) % k)) := by
  have he : r - 1 + 1 = r := by omega
  conv_lhs => rw [← he]; unfold rowWord stateRec
  simp only [preWord, Nat.testBit_xor, he]
  rw [bit_rot hw hi, Nat.mod_eq_of_lt hk]
  cases (wordStep k (mix k (stateRec k (consts k) u w (r - 1)))).testBit i <;>
    cases w.testBit ((i + k - 2 * (r - 1)) % k) <;>
    cases (consts k r).val.testBit i <;> rfl

private theorem ordDecode_match {k r e q u raw vis : Nat}
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (hu : u < 2 ^ k) (hraw : raw < 2 ^ k)
    (hpass : rowWord k raw u r < 2 ^ (k - (k + 1) / 2))
    (hnonexc : ∀ a : Fin q, ∀ mask : Fin (2 ^ q),
      (preWord k (consts k) u raw r).testBit (k - q + a.val) =
        (preWord k (consts k) u
          (raw ^^^ rot k (k - q + a.val + 3 * r + k - e - q) mask.val) r).testBit (k - q + a.val))
    (hvis : ∀ j < k - q, vis.testBit j =
      if j < k - q - (2 * r - 2) then raw.testBit j else raw.testBit (j + q)) :
    ∀ s ≤ q, ∀ m < k,
      (m < k - q - (2 * r - 2) ∨ k - q - (2 * r - 2) + (q - s) ≤ m) →
        (ordDecode k r q u s (ordInit k r q vis)).testBit m = raw.testBit m := by
  let P0 := k - q - (2 * r - 2)
  have hP0_init : ∀ m < k, (m < P0 ∨ P0 + q ≤ m) →
      (ordInit k r q vis).testBit m = raw.testBit m := by
    intro m hm hm'
    simp only [ordInit, bit_pack _ ⟨m, hm⟩]
    by_cases h1 : m < P0
    · simp only [show m < k - q - (2 * r - 2) from h1, ↓reduceIte]
      rw [hvis m (by omega)]
      simp only [show m < k - q - (2 * r - 2) from h1, ↓reduceIte]
    · have h2 : P0 + q ≤ m := by omega
      simp only [show ¬ m < k - q - (2 * r - 2) from h1, ↓reduceIte,
        show k - q - (2 * r - 2) + q ≤ m from h2]
      rw [hvis (m - q) (by omega)]
      simp only [show ¬ m - q < k - q - (2 * r - 2) from by omega, ↓reduceIte]
      congr 1
      omega
  have hP0_zero : ∀ m < k, P0 ≤ m → m < P0 + q → (ordInit k r q vis).testBit m = false := by
    intro m hm h1 h2
    simp only [ordInit, bit_pack _ ⟨m, hm⟩]
    simp only [show ¬ m < k - q - (2 * r - 2) from by omega, ↓reduceIte,
      show ¬ k - q - (2 * r - 2) + q ≤ m from by omega]
  intro s
  induction s with
  | zero =>
    intro _ m hm hm'
    simp only [ordDecode, Nat.sub_zero] at hm' ⊢
    exact hP0_init m hm hm'
  | succ s ih =>
    intro hs m hm hm'
    have hprev := ih (by omega)
    let w' := ordDecode k r q u s (ordInit k r q vis)
    have hw' : w' < 2 ^ k := ordDecode_lt ordInit_lt
    let a := q - 1 - s
    let i := k - q + a
    let p := P0 + a
    have ha_lt : a < q := by omega
    have hi_lt : i < k := by dsimp [i]; omega
    have hp_lt : p < k := by dsimp [p, P0]; omega
    have hp_zero : w'.testBit p = false := by
      dsimp [w']
      rw [ordDecode_unchanged hp_lt (by omega) (by omega) (Or.inl (by dsimp [p, P0, a]; omega))]
      exact hP0_zero p hp_lt (by dsimp [p, P0]; omega) (by dsimp [p, P0, a]; omega)
    have hidx : (i + k - 2 * (r - 1)) % k = p := by
      have he : i + k - 2 * (r - 1) = p + k := by dsimp [i, p, P0]; omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hp_lt]
    let sh := i + 3 * r + k - e - q
    have hsh_mod : sh % k = P0 - (q - 1) + a := by
      have he : sh = (P0 - (q - 1) + a) + 2 * k := by dsimp [sh, i, P0]; omega
      rw [he, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by dsimp [P0]; omega)]
    let maskVal : Nat := tableIndex (fun j : Fin q =>
      xor (raw.testBit ((sh + j.val) % k)) (w'.testBit ((sh + j.val) % k)))
    let mask : Fin (2 ^ q) := ⟨maskVal, pack_lt _⟩
    have hw'_eq : w' = raw ^^^ rot k sh mask.val := by
      apply Nat.eq_of_testBit_eq
      intro x
      by_cases hx : x < k
      · rw [Nat.testBit_xor, bit_rot (lt_of_lt_of_le mask.isLt (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))) hx]
        let d := (x + k - sh % k) % k
        have hsd : (sh + d) % k = x := by
          have h1 : sh % k < k := Nat.mod_lt _ (by omega)
          have h2 : (sh + (x + k - sh % k) % k) % k = (sh % k + (x + k - sh % k)) % k := by
            rw [Nat.add_mod_mod, ← Nat.mod_add_mod]
          rw [h2]
          have h3 : sh % k + (x + k - sh % k) = x + k := by omega
          rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hx]
        by_cases hd : d < q
        · have hmbit : mask.val.testBit d = xor (raw.testBit x) (w'.testBit x) := by
            change maskVal.testBit d = _
            rw [bit_pack _ ⟨d, hd⟩, hsd]
          rw [hmbit]
          cases raw.testBit x <;> cases w'.testBit x <;> rfl
        · have hmbit : mask.val.testBit d = false :=
            Nat.testBit_lt_two_pow (mask.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
          rw [hmbit, Bool.xor_false]
          have hnot : x < P0 ∨ P0 + (q - s) ≤ x := by
            by_contra hmid
            have hx1 : P0 ≤ x := by omega
            have hx2 : x < P0 + (q - s) := by omega
            have hd_eq : d = x - (P0 - (q - 1) + a) := by
              dsimp only [d]
              rw [hsh_mod]
              have he : x + k - (P0 - (q - 1) + a) = (x - (P0 - (q - 1) + a)) + k := by dsimp [P0]; omega
              rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [P0]; omega)]
            omega
          exact hprev x hx hnot
      · have hp2 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ x)
        rw [Nat.testBit_lt_two_pow (hw'.trans_le hp2),
            Nat.testBit_lt_two_pow ((xor_lt hraw rot_lt).trans_le hp2)]
    have hpre_eq : (preWord k (consts k) u w' r).testBit i =
        (preWord k (consts k) u raw r).testBit i := by
      rw [hw'_eq]
      exact (hnonexc ⟨a, ha_lt⟩ mask).symm
    have hraw0 : (rowWord k raw u r).testBit i = false := by
      have hh : k - (k + 1) / 2 ≤ i := by dsimp [i]; omega
      exact (lt_two_pow_iff_testBit (rowWord_lt hu r)).mp hpass i hh hi_lt
    have hbit : (rowWord k w' u r).testBit i = raw.testBit p := by
      rw [rowWord_final_xor (by omega) (by omega) hw' hi_lt, hidx, hp_zero, Bool.xor_false, hpre_eq]
      rw [rowWord_final_xor (by omega) (by omega) hraw hi_lt, hidx] at hraw0
      cases hp1 : (preWord k (consts k) u raw r).testBit i <;>
        cases hp2 : (consts k r).val.testBit i <;>
        cases hp3 : raw.testBit p <;>
        (simp only [hp1, hp2, hp3] at hraw0; first | rfl | cases hraw0)
    simp only [ordDecode]
    rw [testBit_setBit hm]
    by_cases hmp : m = p
    · subst hmp
      simp only [p, P0, a, ↓reduceIte]
      exact hbit
    · simp only [show ¬ m = k - q - (2 * r - 2) + (q - 1 - s) from hmp, ↓reduceIte]
      exact hprev m hm (by dsimp [p, P0, a] at hmp; omega)

private def excPivs (k r e q i : Nat) (tr : List Bool) : List Nat :=
  let cut := e + q + 3
  let N := (r - e) - cut
  let D := e + q - 1
  (List.range N).map (fun s => yRaw k r i (cut + 1 + s) (D - (tr.take s).count true) % k)

private def excOff (k r e q i : Nat) (tr : List Bool) : List Nat :=
  let ps := excPivs k r e q i tr
  (List.range k).filter (fun p => decide (p ∉ ps))

private theorem excPivs_nodup {k r e q i : Nat} (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hk : k + e + 3 = 5 * r) (tr : List Bool) (htr_c : tr.count true ≤ e + q - 1) :
    (excPivs k r e q i tr).Nodup := by
  let cut := e + q + 3
  let N := (r - e) - cut
  let D := e + q - 1
  have htake_le : ∀ s, (tr.take s).count true ≤ D := by
    intro s
    have hsp : tr = tr.take s ++ tr.drop s := (List.take_append_drop s tr).symm
    have hle : (tr.take s).count true ≤ tr.count true := by
      conv_rhs => rw [hsp]
      rw [List.count_append]
      omega
    omega
  have htake_mono : ∀ a b, a ≤ b →
      (tr.take a).count true ≤ (tr.take b).count true ∧
      (tr.take b).count true - (tr.take a).count true ≤ b - a := by
    intro a b hab
    have hsp : tr.take b = tr.take a ++ (tr.drop a).take (b - a) := by
      rw [← List.take_add]
      congr 1
      omega
    rw [hsp, List.count_append]
    have hcl : ((tr.drop a).take (b - a)).count true ≤ b - a := by
      have h1 := List.count_le_length (a := true) (l := (tr.drop a).take (b - a))
      rw [List.length_take] at h1
      omega
    omega
  unfold excPivs
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  intro a ha b hb hab
  simp only [List.mem_range] at ha hb
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hm := htake_mono a b (by omega)
    have hta := htake_le a
    have htb := htake_le b
    have hdiff := mod_ne_of_lt_add (k := k)
      (a := yRaw k r i (cut + 1 + b) (D - (tr.take b).count true))
      (b := yRaw k r i (cut + 1 + a) (D - (tr.take a).count true))
      (by unfold yRaw; omega) (by unfold yRaw; omega)
    exact hdiff hab
  · have hm := htake_mono b a (by omega)
    have hta := htake_le a
    have htb := htake_le b
    have hdiff := mod_ne_of_lt_add (k := k)
      (a := yRaw k r i (cut + 1 + a) (D - (tr.take a).count true))
      (b := yRaw k r i (cut + 1 + b) (D - (tr.take b).count true))
      (by unfold yRaw; omega) (by unfold yRaw; omega)
    exact hdiff hab.symm

private theorem excOff_length {k r e q i : Nat} (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hk : k + e + 3 = 5 * r) (tr : List Bool) (htr_c : tr.count true ≤ e + q - 1) :
    (excOff k r e q i tr).length = k - ((r - e) - (e + q + 3)) := by
  let ps := excPivs k r e q i tr
  have hnodup : ps.Nodup := excPivs_nodup hq hr hk tr htr_c
  have hps_lt : ∀ p ∈ ps, p < k := by
    intro p hp
    simp only [ps, excPivs, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨s, _, rfl⟩
    exact Nat.mod_lt _ (by omega)
  have hps_len : ps.length = (r - e) - (e + q + 3) := by simp [ps, excPivs]
  have h1 : ((List.range k).filter (fun p => decide (p ∉ ps))).length +
      ((List.range k).filter (fun p => decide (p ∈ ps))).length = k := by
    have hsum : ∀ (l : List Nat),
        (l.filter (fun p => decide (p ∉ ps))).length +
        (l.filter (fun p => decide (p ∈ ps))).length = l.length := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        by_cases hx : x ∈ ps
        · simp only [List.filter_cons, List.length_cons, hx, decide_true, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
          omega
        · simp only [List.filter_cons, List.length_cons, hx, decide_false, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte]
          omega
    simpa [List.length_range] using hsum (List.range k)
  have h2 : ((List.range k).filter (fun p => decide (p ∈ ps))).length = ps.length := by
    have hnd1 : ((List.range k).filter (fun p => decide (p ∈ ps))).Nodup :=
      List.Nodup.filter _ List.nodup_range
    have heq : ((List.range k).filter (fun p => decide (p ∈ ps))).toFinset = ps.toFinset := by
      ext x
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨hps_lt x h, h⟩⟩
    rw [← List.toFinset_card_of_nodup hnd1, heq, List.toFinset_card_of_nodup hnodup]
  change ((List.range k).filter (fun p => decide (p ∉ ps))).length = _
  omega

private def initFromList (k : Nat) (ps : List Nat) (rest : Nat) : Nat :=
  (List.range ps.length).foldl (fun acc j => setBit k acc (ps.getD j 0) (rest.testBit j)) 0

private theorem initFromList_aux_lt (k : Nat) (ps : List Nat) (rest : Nat) :
    ∀ n acc, acc < 2 ^ k →
      ((List.range n).foldl (fun a j => setBit k a (ps.getD j 0) (rest.testBit j)) acc) < 2 ^ k
  | 0, acc, hacc => hacc
  | n + 1, acc, hacc => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact setBit_lt

private theorem initFromList_lt {k : Nat} {ps : List Nat} {rest : Nat} :
    initFromList k ps rest < 2 ^ k :=
  initFromList_aux_lt k ps rest ps.length 0 (Nat.two_pow_pos k)

private theorem initFromList_aux_testBit (k : Nat) (ps : List Nat) (rest : Nat)
    (hnodup : ps.Nodup) (m : Nat) (hm : m < k) :
    ∀ n (hn : n ≤ ps.length),
      (((List.range n).foldl (fun a j => setBit k a (ps.getD j 0) (rest.testBit j)) 0).testBit m =
        match (List.range n).find? (fun j => decide (ps.getD j 0 = m)) with
        | some j => rest.testBit j
        | none => false) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp
  | succ n ih =>
    intro hn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, testBit_setBit hm]
    rw [List.find?_append]
    by_cases hhit : ps.getD n 0 = m
    · have hprev_none : (List.range n).find? (fun j => decide (ps.getD j 0 = m)) = none := by
        rw [List.find?_eq_none]
        intro j hj
        simp only [List.mem_range] at hj
        simp only [decide_eq_true_eq]
        intro heq
        have hj' : ps[j]'(by omega) = ps[n]'(by omega) := by
          have e1 : ps.getD j 0 = ps[j]'(by omega) := by simp [List.getD_eq_getElem?_getD, show j < ps.length by omega]
          have e2 : ps.getD n 0 = ps[n]'(by omega) := by simp [List.getD_eq_getElem?_getD, show n < ps.length by omega]
          rw [← e1, ← e2, heq, hhit]
        have := (List.Nodup.getElem_inj_iff hnodup).mp hj'
        omega
      rw [hprev_none]
      simp [Eq.symm hhit]
    · have hne : m ≠ ps.getD n 0 := Ne.symm hhit
      simp only [hne, ↓reduceIte]
      rw [ih (by omega)]
      cases hfind : (List.range n).find? (fun j => decide (ps.getD j 0 = m)) with
      | some j => simp
      | none =>
        simp only [Option.none_or, List.find?_cons, List.find?_nil]
        simp only [List.getD_eq_getElem?_getD] at hhit ⊢
        simp [hhit]

private theorem initFromList_testBit_mem {k : Nat} {ps : List Nat} {rest : Nat}
    (hnodup : ps.Nodup) {j : Nat} (hj : j < ps.length) (hlt : ps[j] < k) :
    (initFromList k ps rest).testBit ps[j] = rest.testBit j := by
  unfold initFromList
  rw [initFromList_aux_testBit k ps rest hnodup ps[j] hlt ps.length (Nat.le_refl _)]
  have hex : ∃ j', (List.range ps.length).find? (fun x => decide (ps.getD x 0 = ps[j])) = some j' := by
    by_contra hno
    cases h : (List.range ps.length).find? (fun x => decide (ps.getD x 0 = ps[j])) with
    | some j' => exact hno ⟨j', h⟩
    | none =>
      have hnone := List.find?_eq_none.mp h j (List.mem_range.mpr hj)
      simp only [decide_eq_true_eq] at hnone
      have e : ps.getD j 0 = ps[j] := by simp [List.getD_eq_getElem?_getD, hj]
      exact hnone e
  rcases hex with ⟨j', hj'⟩
  rw [hj']
  have hmem := List.mem_of_find?_eq_some hj'
  have hpred := List.find?_some hj'
  simp only [List.mem_range] at hmem
  simp only [decide_eq_true_eq] at hpred
  have e : ps.getD j' 0 = ps[j']'(hmem) := by simp [List.getD_eq_getElem?_getD, hmem]
  rw [e] at hpred
  have heq := (List.Nodup.getElem_inj_iff hnodup).mp hpred
  subst heq
  rfl

private theorem initFromList_testBit_not_mem {k : Nat} {ps : List Nat} {rest : Nat}
    (hnodup : ps.Nodup) {m : Nat} (hm : m < k) (hnot : m ∉ ps) :
    (initFromList k ps rest).testBit m = false := by
  unfold initFromList
  rw [initFromList_aux_testBit k ps rest hnodup m hm ps.length (Nat.le_refl _)]
  have hnone : (List.range ps.length).find? (fun j => decide (ps.getD j 0 = m)) = none := by
    rw [List.find?_eq_none]
    intro j hj
    simp only [List.mem_range] at hj
    simp only [decide_eq_true_eq]
    intro heq
    have e : ps.getD j 0 = ps[j]'(hj) := by simp [List.getD_eq_getElem?_getD, hj]
    rw [e] at heq
    exact hnot (heq ▸ List.getElem_mem hj)
  rw [hnone]

private def excDecode (k r e q i : Nat) (tr : List Bool) (u : Nat) : Nat → Nat → Nat
  | 0, w => w
  | s + 1, w =>
    let w' := excDecode k r e q i tr u s w
    let cut := e + q + 3
    let D := e + q - 1
    let t := cut + 1 + s
    let δ := D - (tr.take s).count true
    let p := yRaw k r i t δ % k
    let b := i + 3 * (r - t) + k - δ
    let st := rowWord k w' u (t - 1)
    let par := xor (xor (st.testBit (b % k)) (st.testBit ((b + 1) % k))) (st.testBit ((b + 2) % k))
    setBit k w' p (xor par (tr.getD s false))

private theorem excDecode_lt {k r e q i : Nat} {tr : List Bool} {u s w : Nat} (hw : w < 2 ^ k) :
    excDecode k r e q i tr u s w < 2 ^ k := by
  induction s with
  | zero => exact hw
  | succ s _ => exact setBit_lt

private theorem excDecode_circuit {k r e q i : Nat} (hk : 0 < k) (hr : 3 * e + 2 * q + 3 ≤ r)
    {A : Set (Sig (k + k))} (tr : List Bool)
    (W0 : (Fin (k + k) → Bool) → Nat) (hW0lt : ∀ v, W0 v < 2 ^ k)
    (hW0 : ∀ j : Fin k, bits W0 j ∈ A) (hU : ∀ j : Fin k, bits (U k) j ∈ A)
    (s : Nat) (hs : s ≤ (r - e) - (e + q + 3)) :
    Build A (Set.range (fun j : Fin k => bits (fun v => excDecode k r e q i tr (U k v) s (W0 v)) j))
      (s * (4 * k + 19 * k * r + 9)) := by
  induction s with
  | zero =>
    refine relax (idle ?_) le_rfl le_rfl (by omega)
    rintro _ ⟨j, rfl⟩
    exact hW0 j
  | succ s ih =>
    let W' := fun v => excDecode k r e q i tr (U k v) s (W0 v)
    let R' := Set.range (fun j : Fin k => bits W' j)
    have hW'lt : ∀ v, W' v < 2 ^ k := fun v => excDecode_lt (hW0lt v)
    let cut := e + q + 3
    let D := e + q - 1
    let t := cut + 1 + s
    let δ := D - (tr.take s).count true
    let p := yRaw k r i t δ % k
    let b := i + 3 * (r - t) + k - δ
    let ST := Set.range (fun j : Fin k => bits (fun v => rowWord k (W' v) (U k v) (t - 1)) j)
    have HST : Build (A ∪ R') ST (4 * k + 19 * k * r) := by
      have H0 := rowSchedule (A := A ∪ R') hk W' (U k) hW'lt (U_lt k) (fun j => Or.inr ⟨j, rfl⟩)
        (fun j => Or.inl (hU j)) (t - 1)
      have htr : t - 1 ≤ r := by dsimp [t, cut]; omega
      exact relax H0 le_rfl le_rfl (Nat.add_le_add_left (Nat.mul_le_mul_left (19 * k) htr) (4 * k))
    let f0 : Sig (k + k) := bits (fun v => rowWord k (W' v) (U k v) (t - 1)) (ix hk b)
    let f1 : Sig (k + k) := bits (fun v => rowWord k (W' v) (U k v) (t - 1)) (ix hk (b + 1))
    let f2 : Sig (k + k) := bits (fun v => rowWord k (W' v) (U k v) (t - 1)) (ix hk (b + 2))
    let parSig : Sig (k + k) := xo (xo f0 f1) f2
    have Hpar : Build ((A ∪ R') ∪ ST) {parSig} 8 :=
      mixG (Or.inr ⟨ix hk b, rfl⟩) (Or.inr ⟨ix hk (b + 1), rfl⟩) (Or.inr ⟨ix hk (b + 2), rfl⟩)
    let bitSig : Sig (k + k) := fun v => xor (parSig v) (tr.getD s false)
    have Hbit : Build ((A ∪ R') ∪ (ST ∪ {parSig})) {bitSig} 1 :=
      flipG (Or.inr (Or.inr rfl)) (tr.getD s false)
    have Hstep : Build (A ∪ R') (ST ∪ ({parSig} ∪ {bitSig})) (4 * k + 19 * k * r + 9) := by
      have H12 := seq HST Hpar
      have H123 := seq H12 Hbit
      refine relax H123 le_rfl ?_ (by omega)
      rintro g (hg | (hg | hg))
      · exact Or.inl (Or.inl hg)
      · exact Or.inl (Or.inr hg)
      · exact Or.inr hg
    have Htot := seq (ih (by omega)) Hstep
    have hbd : s * (4 * k + 19 * k * r + 9) + (4 * k + 19 * k * r + 9) ≤
        (s + 1) * (4 * k + 19 * k * r + 9) := by
      rw [Nat.succ_mul s]
    refine relax Htot le_rfl ?_ hbd
    rintro _ ⟨m, rfl⟩
    by_cases hmp : m.val = p
    · right
      right
      right
      change bits (fun v => excDecode k r e q i tr (U k v) (s + 1) (W0 v)) m = bitSig
      funext v
      simp only [bits, excDecode]
      rw [testBit_setBit m.isLt]
      have hmp' : m.val = yRaw k r i (e + q + 3 + 1 + s) (e + q - 1 - (tr.take s).count true) % k := hmp
      simp only [hmp', ↓reduceIte]
      rfl
    · left
      refine ⟨m, ?_⟩
      funext v
      simp only [bits, excDecode]
      rw [testBit_setBit m.isLt]
      have hmp' : ¬ m.val = yRaw k r i (e + q + 3 + 1 + s) (e + q - 1 - (tr.take s).count true) % k := hmp
      simp only [hmp', ↓reduceIte]

private def flipMaskList (k : Nat) : List Nat → Fin (2 ^ k) → Fin (2 ^ k)
  | [], key => key
  | p :: ps, key =>
    let key' := flipMaskList k ps key
    if hp : p < k then
      if key'.val.testBit p then flipBit k key' p hp else key'
    else key'

private theorem flipMaskList_testBit_of_mem {k : Nat} (ps : List Nat) (key : Fin (2 ^ k))
    (m : Nat) (hm : m < k) (hmem : m ∈ ps) :
    (flipMaskList k ps key).val.testBit m = false := by
  induction ps with
  | nil => cases hmem
  | cons p ps ih =>
    simp only [flipMaskList]
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · rw [dif_pos hm]
      cases hbit : (flipMaskList k ps key).val.testBit m with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hbit
      | true =>
        simp only [↓reduceIte]
        rw [testBit_flipBit_self, hbit]
        rfl
    · have hih := ih hmem'
      by_cases hp : p < k
      · rw [dif_pos hp]
        by_cases hbit : (flipMaskList k ps key).val.testBit p = true
        · rw [if_pos hbit]
          by_cases hmp : m = p
          · subst hmp
            rw [hih] at hbit
            cases hbit
          · rw [testBit_flipBit_ne _ hp hmp]
            exact hih
        · rw [if_neg hbit]
          exact hih
      · rw [dif_neg hp]
        exact hih

private theorem flipMaskList_testBit_of_not_mem {k : Nat} (ps : List Nat) (key : Fin (2 ^ k))
    (m : Nat) (hnot : m ∉ ps) :
    (flipMaskList k ps key).val.testBit m = key.val.testBit m := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hmp : m ≠ p := fun h => hnot (h ▸ List.mem_cons_self)
    have hnot' : m ∉ ps := fun h => hnot (List.mem_cons_of_mem p h)
    simp only [flipMaskList]
    by_cases hp : p < k
    · rw [dif_pos hp]
      by_cases hbit : (flipMaskList k ps key).val.testBit p = true
      · rw [if_pos hbit, testBit_flipBit_ne _ hp hmp]
        exact ih hnot'
      · rw [if_neg hbit]
        exact ih hnot'
    · rw [dif_neg hp]
      exact ih hnot'

private theorem parityEq_flipMaskList {k r e q i : Nat} (u : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (tr : List Bool) (htr_c : tr.count true ≤ e + q - 1)
    {s : Nat} (hs : s < (r - e) - (e + q + 3)) (key : Fin (2 ^ k)) :
    let cut := e + q + 3
    let D := e + q - 1
    let t := cut + 1 + s
    let δ := D - (tr.take s).count true
    parityEq k r (consts k) u i t δ (flipMaskList k ((excPivs k r e q i tr).drop (s + 1)) key) =
      parityEq k r (consts k) u i t δ key := by
  intro cut D t δ
  have htake_le : ∀ a, (tr.take a).count true ≤ D := by
    intro a
    have hsp : tr = tr.take a ++ tr.drop a := (List.take_append_drop a tr).symm
    have hle : (tr.take a).count true ≤ tr.count true := by
      conv_rhs => rw [hsp]
      rw [List.count_append]
      omega
    omega
  have htake_mono : ∀ a b, a ≤ b →
      (tr.take a).count true ≤ (tr.take b).count true ∧
      (tr.take b).count true - (tr.take a).count true ≤ b - a := by
    intro a b hab
    have hsp : tr.take b = tr.take a ++ (tr.drop a).take (b - a) := by
      rw [← List.take_add]
      congr 1
      omega
    rw [hsp, List.count_append]
    have hcl : ((tr.drop a).take (b - a)).count true ≤ b - a := by
      have h1 := List.count_le_length (a := true) (l := (tr.drop a).take (b - a))
      rw [List.length_take] at h1
      omega
    omega
  have hgen : ∀ (ps : List Nat),
      (∀ p ∈ ps, ∃ j, s < j ∧ j < (r - e) - cut ∧
        p = yRaw k r i (cut + 1 + j) (D - (tr.take j).count true) % k) →
      parityEq k r (consts k) u i t δ (flipMaskList k ps key) =
        parityEq k r (consts k) u i t δ key := by
    intro ps
    induction ps with
    | nil => intro _; rfl
    | cons p ps ih =>
      intro hmem
      have hih := ih (fun x hx => hmem x (List.mem_cons_of_mem p hx))
      rcases hmem p List.mem_cons_self with ⟨j, hsj, hjN, hp_eq⟩
      simp only [flipMaskList]
      have hp_lt : p < k := by rw [hp_eq]; exact Nat.mod_lt _ (by omega)
      rw [dif_pos hp_lt]
      by_cases hbit : (flipMaskList k ps key).val.testBit p = true
      · rw [if_pos hbit]
        have hm := htake_mono s j (by omega)
        have hts := htake_le s
        have htj := htake_le j
        have hpar := parityEq_flip_later (i := i) (consts k) hq hr hk hu
          (t := t) (t' := cut + 1 + j) (δ := δ) (δ' := D - (tr.take j).count true)
          (by dsimp [t, cut]; omega) (by dsimp [t, cut]; omega) (by omega)
          (by dsimp [δ, D]; omega) (by dsimp [δ, D]; omega) (by dsimp [t, δ, D]; omega)
          (flipMaskList k ps key)
        simp only [← hp_eq] at hpar
        rw [hpar, hih]
      · rw [if_neg hbit, hih]
  apply hgen
  intro p hp
  rcases List.getElem_of_mem hp with ⟨a, ha, hval⟩
  have hlen : (excPivs k r e q i tr).length = (r - e) - cut := by simp [excPivs, cut]
  have ha' : s + 1 + a < (r - e) - cut := by
    rw [List.length_drop, hlen] at ha
    omega
  refine ⟨s + 1 + a, by omega, ha', ?_⟩
  rw [← hval, List.getElem_drop]
  simp [excPivs, cut, D]

private theorem excDecode_match {k r e q i u : Nat} (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r)
    (hk : k + e + 3 = 5 * r) (hu : u < 2 ^ k)
    (raw : Fin (2 ^ k)) (tr : List Bool)
    (htr_len : tr.length = (r - e) - (e + q + 3)) (htr_c : tr.count true ≤ e + q - 1)
    (htr_eq : greedyTrace k r (consts k) u i (e + q + 3) (e + q - 1) raw ((r - e) - (e + q + 3)) = tr)
    (rest : Nat)
    (hrest : ∀ j (hj : j < (excOff k r e q i tr).length),
      rest.testBit j = raw.val.testBit ((excOff k r e q i tr)[j]'hj)) :
    let cut := e + q + 3
    let N := (r - e) - cut
    ∀ s ≤ N, ∀ m < k,
      (excDecode k r e q i tr u s (initFromList k (excOff k r e q i tr) rest)).testBit m =
        if m ∈ (excPivs k r e q i tr).drop s then false else raw.val.testBit m := by
  intro cut N
  let ps := excPivs k r e q i tr
  let offs := excOff k r e q i tr
  have hps_nodup : ps.Nodup := excPivs_nodup hq hr hk tr htr_c
  have hps_len : ps.length = N := by simp [ps, excPivs, N, cut]
  have hoffs_nodup : offs.Nodup := List.Nodup.filter _ List.nodup_range
  have htake_eq : ∀ a (ha : a < N),
      parityEq k r (consts k) u i (cut + 1 + a) ((e + q - 1) - (tr.take a).count true) raw =
        tr[a]'(by omega) := by
    have htr_take : tr = tr.take N := by
      have he : N = tr.length := htr_len.symm
      rw [he, List.take_length]
    have hiff := (greedyTrace_eq_take_iff k r (consts k) u i cut (e + q - 1) raw tr htr_c N (by omega)).mp
    rw [htr_take] at htr_eq
    exact hiff htr_eq
  intro s
  induction s with
  | zero =>
    intro _ m hm
    simp only [excDecode, List.drop_zero]
    by_cases hmem : m ∈ ps
    · have hmem' : m ∈ excPivs k r e q i tr := hmem
      simp only [hmem', ↓reduceIte]
      have hnot : m ∉ offs := by
        simp only [offs, excOff, List.mem_filter, List.mem_range, decide_eq_true_eq]
        intro h
        exact h.2 hmem
      exact initFromList_testBit_not_mem hoffs_nodup hm hnot
    · have hmem' : m ∉ excPivs k r e q i tr := hmem
      simp only [hmem', ↓reduceIte]
      have hmem_off : m ∈ offs := by
        simp only [offs, excOff, List.mem_filter, List.mem_range, decide_eq_true_eq]
        exact ⟨hm, hmem⟩
      rcases List.getElem_of_mem hmem_off with ⟨j, hj, hval⟩
      rw [← hval, initFromList_testBit_mem hoffs_nodup hj (by rw [hval]; exact hm), hrest j hj]
  | succ s ih =>
    intro hs m hm
    have hprev := ih (by omega)
    let w' := excDecode k r e q i tr u s (initFromList k offs rest)
    have hw' : w' < 2 ^ k := excDecode_lt initFromList_lt
    let D := e + q - 1
    let t := cut + 1 + s
    let δ := D - (tr.take s).count true
    let p := yRaw k r i t δ % k
    have hp_lt : p < k := Nat.mod_lt _ (by omega)
    have hps_s : ps[s]'(by omega) = p := by simp [ps, excPivs, p, t, δ, cut, D]
    have hdrop_eq : ps.drop s = p :: ps.drop (s + 1) := by
      have h1 : ps[s]'(by omega) :: ps.drop (s + 1) = ps.drop s := List.cons_getElem_drop_succ
      rw [hps_s] at h1
      exact h1.symm
    have hp_not_later : p ∉ ps.drop (s + 1) := by
      have hnd_drop : (ps.drop s).Nodup :=
        (List.nodup_append.mp (by rw [List.take_append_drop s ps]; exact hps_nodup)).2.1
      rw [hdrop_eq] at hnd_drop
      exact (List.nodup_cons.mp hnd_drop).1
    let wMid : Fin (2 ^ k) := flipMaskList k (ps.drop (s + 1)) raw
    have hpar_mid : parityEq k r (consts k) u i t δ wMid = tr[s]'(by omega) := by
      have h1 := parityEq_flipMaskList (k := k) (r := r) (e := e) (q := q) (i := i) u hq hr hk hu
        tr htr_c (s := s) (by omega) raw
      rw [h1]
      exact htake_eq s (by omega)
    have hwMid_p : wMid.val.testBit p = raw.val.testBit p :=
      flipMaskList_testBit_of_not_mem (ps.drop (s + 1)) raw p hp_not_later
    have hbit_eq :
        xor (parityEq k r (consts k) u i t δ ⟨w', hw'⟩) (tr.getD s false) = raw.val.testBit p := by
      have hget : tr.getD s false = tr[s]'(by omega) := by
        simp [List.getD_eq_getElem?_getD, show s < tr.length by omega]
      rw [hget]
      cases hrawp : raw.val.testBit p with
      | false =>
        have hw'_mid : (⟨w', hw'⟩ : Fin (2 ^ k)) = wMid := by
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro x
          by_cases hx : x < k
          · rw [hprev x hx, hdrop_eq]
            by_cases hxp : x = p
            · subst hxp
              simp only [List.mem_cons_self, ↓reduceIte]
              rw [hwMid_p, hrawp]
            · by_cases hxl : x ∈ ps.drop (s + 1)
              · simp only [List.mem_cons, hxp, false_or, hxl, ↓reduceIte]
                exact (flipMaskList_testBit_of_mem (ps.drop (s + 1)) raw x hx hxl).symm
              · simp only [List.mem_cons, hxp, false_or, hxl, ↓reduceIte]
                exact (flipMaskList_testBit_of_not_mem (ps.drop (s + 1)) raw x hxl).symm
          · have hp2 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ x)
            rw [Nat.testBit_lt_two_pow (hw'.trans_le hp2),
                Nat.testBit_lt_two_pow (wMid.isLt.trans_le hp2)]
        rw [hw'_mid, hpar_mid, Bool.xor_self]
      | true =>
        have hw'_flip : (⟨w', hw'⟩ : Fin (2 ^ k)) = flipBit k wMid p hp_lt := by
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro x
          by_cases hx : x < k
          · rw [hprev x hx, hdrop_eq]
            by_cases hxp : x = p
            · subst hxp
              simp only [List.mem_cons_self, ↓reduceIte]
              rw [testBit_flipBit_self, hwMid_p, hrawp]
              rfl
            · rw [testBit_flipBit_ne wMid hp_lt hxp]
              by_cases hxl : x ∈ ps.drop (s + 1)
              · simp only [List.mem_cons, hxp, false_or, hxl, ↓reduceIte]
                exact (flipMaskList_testBit_of_mem (ps.drop (s + 1)) raw x hx hxl).symm
              · simp only [List.mem_cons, hxp, false_or, hxl, ↓reduceIte]
                exact (flipMaskList_testBit_of_not_mem (ps.drop (s + 1)) raw x hxl).symm
          · have hp2 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ x)
            rw [Nat.testBit_lt_two_pow (hw'.trans_le hp2),
                Nat.testBit_lt_two_pow ((flipBit k wMid p hp_lt).isLt.trans_le hp2)]
        rw [hw'_flip]
        have hself := parityEq_flip_self (i := i) (consts k) hq hr hk hu
          (t := t) (δ := δ) (by dsimp [t, cut]; omega) (by dsimp [t, cut]; omega) (by dsimp [δ, D]; omega) wMid
        simp only [show yRaw k r i t δ % k = p from rfl] at hself
        rw [hself, hpar_mid]
        cases tr[s]'(by omega) <;> rfl
    simp only [excDecode]
    rw [testBit_setBit hm]
    by_cases hmp : m = p
    · subst hmp
      have hnot_l : p ∉ (excPivs k r e q i tr).drop (s + 1) := hp_not_later
      simp only [hnot_l, ↓reduceIte]
      have hmp' : p = yRaw k r i (e + q + 3 + 1 + s) (e + q - 1 - (tr.take s).count true) % k := rfl
      simp only [hmp', ↓reduceIte]
      exact hbit_eq
    · have hmp' : ¬ m = yRaw k r i (e + q + 3 + 1 + s) (e + q - 1 - (tr.take s).count true) % k := hmp
      simp only [hmp', ↓reduceIte]
      have hdrop_eq' : (excPivs k r e q i tr).drop s = p :: (excPivs k r e q i tr).drop (s + 1) := hdrop_eq
      rw [hprev m hm, hdrop_eq']
      simp only [List.mem_cons, hmp, false_or]

private theorem flatMap_length_const {α β : Type*} (l : List α) (f : α → List β) (m : Nat)
    (hm : ∀ x ∈ l, (f x).length = m) : (l.flatMap f).length = l.length * m := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      hm x List.mem_cons_self, ih (fun y hy => hm y (List.mem_cons_of_mem x hy)), Nat.succ_mul]
    omega

private theorem solve_25533 (k r e q : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) :
    let h := (k + 1) / 2
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    let E := (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N)
    ∃ C : Circuit, FanInTwo C ∧ ReadsBack (k + k) C ∧
      C.size ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 * (2 ^ (k - q) + q * E) ∧
      ∀ v : Fin (k + k) → Bool, C.eval (List.ofFn v) =
        (List.range (2 ^ k)).any (fun w =>
          decide (rowWord k w (U k v) r < 2 ^ (k - h)) &&
          decide (colWord k r w (V k v) r < 2 ^ (k - h))) := by
  intro h N D E
  have hkpos : 0 < k := by omega
  let cut := e + q + 3
  let S : Nat := (r + 2) * (4 * k + 19 * k * r + 9) + 2 * k + 3
  let WordTest (W : (Fin (k + k) → Bool) → Nat) : Sig (k + k) := fun v =>
    decide (rowWord k (W v) (U k v) r < 2 ^ (k - h)) &&
    decide (colWord k r (W v) (V k v) r < 2 ^ (k - h))
  let ordW (vis : Fin (2 ^ (k - q))) (v : Fin (k + k) → Bool) : Nat :=
    ordDecode k r q (U k v) q (ordInit k r q vis.val)
  let ordF (vis : Fin (2 ^ (k - q))) : Sig (k + k) := WordTest (ordW vis)
  let excW (a : Fin q) (tr : List Bool) (rest : Fin (2 ^ (k - N))) (v : Fin (k + k) → Bool) : Nat :=
    excDecode k r e q (k - q + a.val) tr (U k v) N
      (initFromList k (excOff k r e q (k - q + a.val) tr) rest.val)
  let excF (a : Fin q) (tr : List Bool) (rest : Fin (2 ^ (k - N))) : Sig (k + k) :=
    WordTest (excW a tr rest)
  let ordSlots : List (Sig (k + k)) := (List.finRange (2 ^ (k - q))).map ordF
  let excSlots : List (Sig (k + k)) :=
    (List.finRange q).flatMap (fun a =>
      (lowWeight N D).flatMap (fun tr =>
        (List.finRange (2 ^ (k - N))).map (fun rest => excF a tr rest)))
  let allSlots : List (Sig (k + k)) := ordSlots ++ excSlots
  have hord_build : ∀ vis : Fin (2 ^ (k - q)), Build (base (k + k)) {ordF vis} S := by
    intro vis
    let W0 : (Fin (k + k) → Bool) → Nat := fun _ => ordInit k r q vis.val
    let S1 := Set.range (fun j : Fin k => bits (ordW vis) j)
    have H1 : Build (base (k + k)) S1 (q * (4 * k + 19 * k * r)) :=
      ordDecode_circuit hkpos W0 (fun _ => ordInit_lt)
        (fun j => constBit_mem ((ordInit k r q vis.val).testBit j.val))
        (bitU k) (by omega) q (Nat.le_refl q)
    have H2 : Build (base (k + k) ∪ S1) {ordF vis} (2 * (4 * k + 19 * k * r) + 2 * k + 3) :=
      testSlotCircuit hkpos (ordW vis) (fun _ => ordDecode_lt ordInit_lt)
        (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (bitU k j))
        (fun j => Or.inl (bitV k j)) (Or.inl (constBit_mem false))
    refine relax (seq H1 H2) le_rfl Set.subset_union_right ?_
    have hq_le : q + 2 ≤ r + 2 := by omega
    have h1 := Nat.mul_le_mul hq_le (show 4 * k + 19 * k * r ≤ 4 * k + 19 * k * r + 9 by omega)
    dsimp only [S]
    rw [Nat.add_mul] at h1
    omega
  have hexc_build : ∀ (a : Fin q) (tr : List Bool) (rest : Fin (2 ^ (k - N))),
      Build (base (k + k)) {excF a tr rest} S := by
    intro a tr rest
    let W0 : (Fin (k + k) → Bool) → Nat :=
      fun _ => initFromList k (excOff k r e q (k - q + a.val) tr) rest.val
    let S1 := Set.range (fun j : Fin k => bits (excW a tr rest) j)
    have H1 : Build (base (k + k)) S1 (N * (4 * k + 19 * k * r + 9)) :=
      excDecode_circuit hkpos hr tr W0 (fun _ => initFromList_lt)
        (fun j => constBit_mem ((W0 (fun _ => false)).testBit j.val))
        (bitU k) N (Nat.le_refl N)
    have H2 : Build (base (k + k) ∪ S1) {excF a tr rest} (2 * (4 * k + 19 * k * r) + 2 * k + 3) :=
      testSlotCircuit hkpos (excW a tr rest) (fun _ => excDecode_lt initFromList_lt)
        (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (bitU k j))
        (fun j => Or.inl (bitV k j)) (Or.inl (constBit_mem false))
    refine relax (seq H1 H2) le_rfl Set.subset_union_right ?_
    have hN_le : N + 2 ≤ r + 2 := by dsimp [N]; omega
    have h1 := Nat.mul_le_mul_right (4 * k + 19 * k * r + 9) hN_le
    dsimp only [S]
    rw [Nat.add_mul] at h1
    omega
  have hall_build : ∀ f ∈ allSlots, Build (base (k + k)) {f} S := by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · rcases List.mem_map.mp hf with ⟨vis, _, rfl⟩
      exact hord_build vis
    · rcases List.mem_flatMap.mp hf with ⟨a, _, hf1⟩
      rcases List.mem_flatMap.mp hf1 with ⟨tr, _, hf2⟩
      rcases List.mem_map.mp hf2 with ⟨rest, _, rfl⟩
      exact hexc_build a tr rest
  have Hs : Build (base (k + k)) {f | ∃ g ∈ allSlots, f = g} (allSlots.length * S) :=
    listBuild allSlots id S hall_build
  let O : Sig (k + k) := fun v => allSlots.any (fun f => f v)
  have Ho : Build (base (k + k) ∪ {f | ∃ g ∈ allSlots, f = g}) {O} allSlots.length :=
    anyG allSlots (fun f hf => Or.inr ⟨f, hf, rfl⟩) (Or.inl (constBit_mem false))
  have Htot : Build (inputs (k + k)) {O} (2 + (allSlots.length * S + allSlots.length)) :=
    relax (seq (inputG (k + k)) (seq Hs Ho)) le_rfl
      (Set.singleton_subset_iff.mpr (Or.inr (Or.inr rfl))) le_rfl
  obtain ⟨c, hc, HS⟩ :=
    Htot.run (GateBridge.start (F := id) (fun j : Fin (k + k) => fun v => v j) (by intros; rfl)) le_rfl
  clear Htot
  obtain ⟨C, hsize, hread, hfan, hout⟩ := GateBridge.finish HS (Or.inr (Set.mem_singleton O))
  have hlen_ord : ordSlots.length = 2 ^ (k - q) := by simp [ordSlots]
  have hlen_exc : excSlots.length = q * E := by
    dsimp only [excSlots, E]
    rw [flatMap_length_const (List.finRange q) _ ((∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N))]
    · simp
    · intro a _
      rw [flatMap_length_const (lowWeight N D) _ (2 ^ (k - N))]
      · rw [lowWeight_length]
      · intro tr _
        simp
  have hlen_all : allSlots.length = 2 ^ (k - q) + q * E := by
    dsimp only [allSlots]
    rw [List.length_append, hlen_ord, hlen_exc]
  refine ⟨C, hfan, hread, ?_, fun v => ?_⟩
  · rw [hsize, Nat.zero_add]
    have hM_pos : 1 ≤ allSlots.length := by
      rw [hlen_all]
      have h2 := Nat.two_pow_pos (k - q)
      omega
    have hS3 : S + 3 ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 := by
      have ha1 : 4 * k + 19 * k * r + 9 ≤ 32 * ((k + 1) * (r + 1)) := by
        have hkr : k * r ≤ (k + 1) * (r + 1) := Nat.mul_le_mul (Nat.le_succ k) (Nat.le_succ r)
        have hk1 : k ≤ (k + 1) * (r + 1) :=
          Nat.le_trans (Nat.le_succ k) (Nat.le_mul_of_pos_right (k + 1) (Nat.succ_pos r))
        have h11 : 1 ≤ (k + 1) * (r + 1) := Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos r)
        rw [Nat.mul_assoc 19 k r]
        omega
      have ha2 : r + 2 ≤ 2 * (r + 1) := by omega
      have ha3 : (r + 2) * (4 * k + 19 * k * r + 9) ≤ 64 * ((k + 1) * (r + 1) ^ 2) := by
        calc
          (r + 2) * (4 * k + 19 * k * r + 9)
              ≤ (2 * (r + 1)) * (32 * ((k + 1) * (r + 1))) := Nat.mul_le_mul ha2 ha1
          _ = 64 * ((k + 1) * (r + 1) ^ 2) := by
              rw [Nat.pow_two]
              have e1 : (2 * (r + 1)) * (32 * ((k + 1) * (r + 1))) =
                  (2 * 32) * ((k + 1) * ((r + 1) * (r + 1))) := by
                simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
              exact e1
      have ha4 : 2 * k + 6 ≤ 6 * ((k + 1) * (r + 1) ^ 2) := by
        have hrr : 1 ≤ (r + 1) ^ 2 := Nat.pow_pos (Nat.succ_pos r)
        have hkm : k + 1 ≤ (k + 1) * (r + 1) ^ 2 := Nat.le_mul_of_pos_right (k + 1) hrr
        omega
      have ha5 : (k + 1) * (r + 1) ^ 2 ≤ (k + 1) ^ 3 * (r + 1) ^ 2 := by
        apply Nat.mul_le_mul_right
        have h1 : k + 1 ≤ (k + 1) * (k + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
        have h2 : (k + 1) * (k + 1) ≤ (k + 1) * (k + 1) * (k + 1) :=
          Nat.le_mul_of_pos_right _ (Nat.succ_pos k)
        simpa [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using Nat.le_trans h1 h2
      dsimp only [S]
      have h70 : 70 * ((k + 1) * (r + 1) ^ 2) ≤ 1000 * ((k + 1) ^ 3 * (r + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) ha5
      have hassoc : 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 = 1000 * ((k + 1) ^ 3 * (r + 1) ^ 2) :=
        Nat.mul_assoc 1000 ((k + 1) ^ 3) ((r + 1) ^ 2)
      rw [hassoc]
      omega
    have hstep1 : c ≤ allSlots.length * (S + 3) := by
      have h3 : allSlots.length * (S + 3) = allSlots.length * S + allSlots.length * 3 :=
        Nat.mul_add allSlots.length S 3
      omega
    have hstep2 : allSlots.length * (S + 3) ≤ allSlots.length * (1000 * (k + 1) ^ 3 * (r + 1) ^ 2) :=
      Nat.mul_le_mul_left _ hS3
    rw [hlen_all] at hstep1 hstep2
    rw [Nat.mul_comm]
    exact Nat.le_trans hstep1 hstep2
  · rw [hout]
    change O v = _
    apply Bool.eq_iff_iff.mpr
    simp only [O, List.any_eq_true, List.mem_range]
    constructor
    · rintro ⟨f, hf, hfv⟩
      rcases List.mem_append.mp hf with hf | hf
      · rcases List.mem_map.mp hf with ⟨vis, _, rfl⟩
        exact ⟨ordW vis v, ordDecode_lt ordInit_lt, hfv⟩
      · rcases List.mem_flatMap.mp hf with ⟨a, _, hf1⟩
        rcases List.mem_flatMap.mp hf1 with ⟨tr, _, hf2⟩
        rcases List.mem_map.mp hf2 with ⟨rest, _, rfl⟩
        exact ⟨excW a tr rest v, excDecode_lt initFromList_lt, hfv⟩
    · rintro ⟨raw, hraw, hraw'⟩
      have hraw1 : rowWord k raw (U k v) r < 2 ^ (k - h) :=
        of_decide_eq_true (Bool.and_eq_true_iff.mp hraw').1
      by_cases hex : ∃ a : Fin q, ∃ mask : Fin (2 ^ q),
          (preWord k (consts k) (U k v) raw r).testBit (k - q + a.val) ≠
            (preWord k (consts k) (U k v)
              (raw ^^^ rot k (k - q + a.val + 3 * r + k - e - q) mask.val) r).testBit (k - q + a.val)
      · rcases hex with ⟨a, mask, hdiff⟩
        let i := k - q + a.val
        have hi : i < k := by dsimp [i]; omega
        rcases exists_history k r e q (consts k) (U k v) i hq hr hk (U_lt k v) hi ⟨raw, hraw⟩ mask hdiff with
          ⟨d, hd_bd, hd_mono, hd_par⟩
        have hcnt := greedyTrace_good_of_history k r e q (consts k) (U k v) i hq hr ⟨raw, hraw⟩ d hd_bd hd_mono hd_par
        let tr := greedyTrace k r (consts k) (U k v) i cut D ⟨raw, hraw⟩ N
        have htr_len : tr.length = N := greedyTrace_length k r (consts k) (U k v) i cut D ⟨raw, hraw⟩ N
        have htr_mem : tr ∈ lowWeight N D := (mem_lowWeight N D tr).mpr ⟨htr_len, hcnt⟩
        have hoff_len : (excOff k r e q i tr).length = k - N := excOff_length hq hr hk tr hcnt
        let restVal : Nat := tableIndex (fun j : Fin (k - N) =>
          raw.testBit ((excOff k r e q i tr)[j.val]'(by omega)))
        let rest : Fin (2 ^ (k - N)) := ⟨restVal, pack_lt _⟩
        have hrest : ∀ j (hj : j < (excOff k r e q i tr).length),
            rest.val.testBit j = raw.testBit ((excOff k r e q i tr)[j]'hj) := by
          intro j hj
          exact bit_pack _ ⟨j, by omega⟩
        have hdec : excW a tr rest v = raw := by
          apply Nat.eq_of_testBit_eq
          intro m
          by_cases hm : m < k
          · have hdm := excDecode_match hq hr hk (U_lt k v) ⟨raw, hraw⟩ tr htr_len hcnt rfl rest.val hrest N (Nat.le_refl N) m hm
            have hdrop_nil : (excPivs k r e q i tr).drop N = [] := by
              rw [List.drop_eq_nil_iff]
              simp [excPivs, N, cut]
            rw [hdrop_nil] at hdm
            simpa only [excW, List.not_mem_nil, ↓reduceIte] using hdm
          · have hp2 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ m)
            rw [Nat.testBit_lt_two_pow ((excDecode_lt initFromList_lt).trans_le hp2),
                Nat.testBit_lt_two_pow (hraw.trans_le hp2)]
        refine ⟨excF a tr rest, List.mem_append_right _ ?_, ?_⟩
        · rw [List.mem_flatMap]
          refine ⟨a, List.mem_finRange a, ?_⟩
          rw [List.mem_flatMap]
          refine ⟨tr, htr_mem, ?_⟩
          rw [List.mem_map]
          exact ⟨rest, List.mem_finRange rest, rfl⟩
        · simpa only [excF, WordTest, hdec] using hraw'
      · have hnonexc : ∀ a : Fin q, ∀ mask : Fin (2 ^ q),
            (preWord k (consts k) (U k v) raw r).testBit (k - q + a.val) =
              (preWord k (consts k) (U k v)
                (raw ^^^ rot k (k - q + a.val + 3 * r + k - e - q) mask.val) r).testBit (k - q + a.val) := by
          intro a mask
          by_contra hne
          exact hex ⟨a, mask, hne⟩
        let visVal : Nat := tableIndex (fun j : Fin (k - q) =>
          if j.val < k - q - (2 * r - 2) then raw.testBit j.val else raw.testBit (j.val + q))
        let vis : Fin (2 ^ (k - q)) := ⟨visVal, pack_lt _⟩
        have hvis : ∀ j < k - q, vis.val.testBit j =
            if j < k - q - (2 * r - 2) then raw.testBit j else raw.testBit (j + q) := by
          intro j hj
          exact bit_pack _ ⟨j, hj⟩
        have hdec : ordW vis v = raw := by
          apply Nat.eq_of_testBit_eq
          intro m
          by_cases hm : m < k
          · have hdm := ordDecode_match hq hr hk (U_lt k v) hraw hraw1 hnonexc hvis q (Nat.le_refl q) m hm (by omega)
            exact hdm
          · have hp2 := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ m)
            rw [Nat.testBit_lt_two_pow ((ordDecode_lt ordInit_lt).trans_le hp2),
                Nat.testBit_lt_two_pow (hraw.trans_le hp2)]
        refine ⟨ordF vis, List.mem_append_left _ ?_, ?_⟩
        · rw [List.mem_map]
          exact ⟨vis, List.mem_finRange vis, rfl⟩
        · simpa only [ordF, WordTest, hdec] using hraw'

end Circuit25533


private theorem choose_le_add_diag : ∀ (a b t : Nat), Nat.choose a b ≤ Nat.choose (a + t) (b + t)
  | a, b, 0 => Nat.le_refl _
  | a, b, t + 1 => by
    have ih := choose_le_add_diag a b t
    have hstep : Nat.choose (a + t) (b + t) ≤ Nat.choose (a + t + 1) (b + t + 1) := by
      rw [Nat.choose_succ_succ]
      omega
    exact Nat.le_trans ih hstep

private theorem succ_le_two_pow : ∀ (d : Nat), d + 1 ≤ 2 ^ d
  | 0 => Nat.le_refl 1
  | d + 1 => by
    have ih := succ_le_two_pow d
    rw [Nat.pow_succ]
    omega

private theorem tail_bound_25520 (k r e q : Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r) :
    let N := (r - e) - (e + q + 3)
    let D := e + q - 1
    let E := (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N)
    E ≤ Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
  intro N D E
  have hterm : ∀ j ∈ Finset.range (D + 1), Nat.choose N j ≤ Nat.choose (r + (e + q) + 1) (e + q) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have h1 := choose_le_add_diag N j (e + q - j)
    have hjeq : j + (e + q - j) = e + q := by dsimp [D] at hj; omega
    rw [hjeq] at h1
    have h2 : Nat.choose (N + (e + q - j)) (e + q) ≤ Nat.choose (r + (e + q) + 1) (e + q) :=
      Nat.choose_le_choose (e + q) (by dsimp [N]; omega)
    exact Nat.le_trans h1 h2
  have hsum : ∑ j ∈ Finset.range (D + 1), Nat.choose N j ≤
      (D + 1) * Nat.choose (r + (e + q) + 1) (e + q) := by
    have h1 := Finset.sum_le_sum hterm
    simpa [Finset.sum_const, Finset.card_range] using h1
  have hpow : D + (k - N) = k - (r - (3 * e + 2 * q + 2)) := by
    dsimp [N, D]
    omega
  calc
    E = (∑ j ∈ Finset.range (D + 1), Nat.choose N j) * 2 ^ (k - N) := rfl
    _ ≤ ((D + 1) * Nat.choose (r + (e + q) + 1) (e + q)) * 2 ^ (k - N) :=
      Nat.mul_le_mul_right _ hsum
    _ ≤ (2 ^ D * Nat.choose (r + (e + q) + 1) (e + q)) * 2 ^ (k - N) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (succ_le_two_pow D))
    _ = Nat.choose (r + (e + q) + 1) (e + q) * (2 ^ D * 2 ^ (k - N)) := by
      rw [Nat.mul_comm (2 ^ D), Nat.mul_assoc]
    _ = Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
      rw [← Nat.pow_add, hpow]

end PEqualNP.Outside.L_meta_25520_aux

theorem PEqualNP.Outside.L_meta_25520 : ∀ (k r e q : Nat), 0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 *
      (2 ^ (k - q) + q * Nat.choose (r + (e + q) + 1) (e + q) *
        2 ^ (k - (r - (3 * e + 2 * q + 2)))) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro k r e q hq hr hk
  have rowEq (w u : Nat) :
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 1 s ^^^
            PEqualNP.Outside.L_meta_25520_aux.rot k (k - 1) s).testBit i)
            (!((s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 1 s ^^^
              PEqualNP.Outside.L_meta_25520_aux.rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 1 s ^^^
              PEqualNP.Outside.L_meta_25520_aux.rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k (2 * t) w ^^^ (3 ^ (k + (t + 1)) % 2 ^ k))
        (PEqualNP.Outside.L_meta_25520_aux.rot k 1 w ^^^ u) =
      PEqualNP.Outside.L_meta_25520_aux.Circuit25533.rowWord k w u r := by
    simp only [← PEqualNP.Outside.L_meta_25520_aux.wordStep_eq]
    exact PEqualNP.Outside.L_meta_25520_aux.Circuit25533.round_fold
      (PEqualNP.Outside.L_meta_25520_aux.Circuit25533.rowWord k w u)
      (fun s t => PEqualNP.Outside.L_meta_25520_aux.wordStep k
        (PEqualNP.Outside.L_meta_25520_aux.mix k s) ^^^
        PEqualNP.Outside.L_meta_25520_aux.rot k (2 * t) w ^^^
        (PEqualNP.Outside.L_meta_25520_aux.Circuit25533.consts k (t + 1)).val)
      (by intros; rfl) r
  have colEq (w v : Nat) :
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 2 s ^^^
            PEqualNP.Outside.L_meta_25520_aux.rot k (k - 2) s).testBit i)
            (!((s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 2 s ^^^
              PEqualNP.Outside.L_meta_25520_aux.rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 2 s ^^^
              PEqualNP.Outside.L_meta_25520_aux.rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k (3 * (t + 1) + 1) w ^^^ (3 ^ (k + (r + (t + 1))) % 2 ^ k))
        (PEqualNP.Outside.L_meta_25520_aux.rot k 3 w ^^^ v) =
      PEqualNP.Outside.L_meta_25520_aux.Circuit25533.colWord k r w v r := by
    simp only [← PEqualNP.Outside.L_meta_25520_aux.wordStep_eq]
    exact PEqualNP.Outside.L_meta_25520_aux.Circuit25533.round_fold
      (PEqualNP.Outside.L_meta_25520_aux.Circuit25533.colWord k r w v)
      (fun s t => PEqualNP.Outside.L_meta_25520_aux.Circuit25533.updateRound k 2
        (3 * (t + 1) + 1) (r + (t + 1)) w s)
      (by intros; rfl) r
  dsimp only
  obtain ⟨C, hFan, hRead, hSize, hEval⟩ :=
    PEqualNP.Outside.L_meta_25520_aux.Circuit25533.solve_25533 k r e q hq hr hk
  have htail := PEqualNP.Outside.L_meta_25520_aux.tail_bound_25520 k r e q hq hr hk
  have hSize' : C.size ≤ 1000 * (k + 1) ^ 3 * (r + 1) ^ 2 *
      (2 ^ (k - q) + q * Nat.choose (r + (e + q) + 1) (e + q) *
        2 ^ (k - (r - (3 * e + 2 * q + 2)))) := by
    have hqE : q * ((∑ j ∈ Finset.range (e + q - 1 + 1), Nat.choose (r - e - (e + q + 3)) j) *
        2 ^ (k - (r - e - (e + q + 3)))) ≤
        q * Nat.choose (r + (e + q) + 1) (e + q) * 2 ^ (k - (r - (3 * e + 2 * q + 2))) := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left q htail
    exact Nat.le_trans hSize (Nat.mul_le_mul_left _ (Nat.add_le_add_left hqE _))
  refine ⟨C, hFan, hRead, hSize', fun b => ?_⟩
  rw [hEval]
  unfold PEqualNP.Represents.adjFun
  dsimp only
  simp only [← PEqualNP.Outside.L_meta_25520_aux.wordStep_eq] at rowEq colEq ⊢
  change _ = (List.range (2 ^ k)).any (fun w =>
    decide ((List.range r).foldl (fun s t =>
      PEqualNP.Outside.L_meta_25520_aux.wordStep k
        (s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 1 s ^^^
          PEqualNP.Outside.L_meta_25520_aux.rot k (k - 1) s) ^^^
        PEqualNP.Outside.L_meta_25520_aux.rot k (2 * t) w ^^^ (3 ^ (k + (t + 1)) % 2 ^ k))
      (PEqualNP.Outside.L_meta_25520_aux.rot k 1 w ^^^
        ((PEqualNP.Outside.L_meta_25520_aux.Circuit25533.U k b) % 2 ^ k)) < 2 ^ (k - (k + 1) / 2)) &&
    decide ((List.range r).foldl (fun s t =>
      PEqualNP.Outside.L_meta_25520_aux.wordStep k
        (s ^^^ PEqualNP.Outside.L_meta_25520_aux.rot k 2 s ^^^
          PEqualNP.Outside.L_meta_25520_aux.rot k (k - 2) s) ^^^
        PEqualNP.Outside.L_meta_25520_aux.rot k (3 * (t + 1) + 1) w ^^^
        (3 ^ (k + (r + (t + 1))) % 2 ^ k))
      (PEqualNP.Outside.L_meta_25520_aux.rot k 3 w ^^^
        ((PEqualNP.Outside.L_meta_25520_aux.Circuit25533.V k b) % 2 ^ k)) < 2 ^ (k - (k + 1) / 2)))
  simp only [Nat.mod_eq_of_lt (PEqualNP.Outside.L_meta_25520_aux.Circuit25533.U_lt k b),
    Nat.mod_eq_of_lt (PEqualNP.Outside.L_meta_25520_aux.Circuit25533.V_lt k b), rowEq, colEq]
