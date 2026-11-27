import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25514_aux

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

private theorem mix_lt {k w : Nat} (hw : w < 2 ^ k) : mix k w < 2 ^ k :=
  lt_xor (lt_xor hw rot_lt) rot_lt

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

private theorem rot_idx_mod {k s S j : Nat} (hk : 0 < k) (hj : j < k) :
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
    have hmod1 : (a + s + S) % k = (pos k r i t δ) % k := rot_idx_mod hkpos hpos
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

private theorem solve_25514 (k r e q : Nat) (constants : Nat → Fin (2 ^ k)) (u i : Nat)
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
        let z := stateRec k constants u base.val (t - 1)
        let b := i + 3 * (r - t) + k - d t
        xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
          (z.testBit ((b + 2) % k)) = false := by
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
    dsimp only
    rw [hb0, hb1, hb2]
    exact hforced

end PEqualNP.Outside.L_meta_25514_aux

theorem PEqualNP.Outside.L_meta_25514 :
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
      let cut := e + q + 3
      ∀ (base : Fin (2 ^ k)) (mask : Fin (2 ^ q)),
        before base.val ≠ before (base.val ^^^ rot (i + 3 * r + k - e - q) mask.val) →
        ∃ d : ℕ → ℕ,
          (∀ t, cut ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) ∧
          (∀ t, cut < t → t ≤ r → d t ≤ d (t - 1)) ∧
          ∀ t, cut < t → t ≤ r - e →
            (∀ s, cut ≤ s → s < t → s + d s < t + d t) →
            let z := state base.val (t - 1)
            let b := i + 3 * (r - t) + k - d t
            xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
              (z.testBit ((b + 2) % k)) = false := by
  intro k r e q constants u i hq hr hk hu hi rot step state before cut base mask hdiff
  have hstep : ∀ w, step w = PEqualNP.Outside.L_meta_25514_aux.wordStep k w := fun w =>
    (PEqualNP.Outside.L_meta_25514_aux.wordStep_eq k w).symm
  have hstate : ∀ key rounds,
      state key rounds = PEqualNP.Outside.L_meta_25514_aux.stateRec k constants u key rounds := by
    intro key rounds
    dsimp only [state]
    have hfn :
        (fun prev t =>
          step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
            (constants (t + 1)).val) =
        (fun prev t =>
          PEqualNP.Outside.L_meta_25514_aux.wordStep k
            (PEqualNP.Outside.L_meta_25514_aux.mix k prev) ^^^
            PEqualNP.Outside.L_meta_25514_aux.rot k (2 * t) key ^^^
            (constants (t + 1)).val) := by
      funext prev t
      rw [hstep]
      rfl
    rw [hfn]
    exact PEqualNP.Outside.L_meta_25514_aux.stateRec_eq_fold k constants u key rounds
  have hbefore : ∀ subject,
      before subject =
        (PEqualNP.Outside.L_meta_25514_aux.preWord k constants u subject r).testBit i := by
    intro subject
    dsimp only [before]
    rw [hstate, hstep]
    rfl
  have hdiff' :
      (PEqualNP.Outside.L_meta_25514_aux.preWord k constants u base.val r).testBit i ≠
      (PEqualNP.Outside.L_meta_25514_aux.preWord k constants u
        (base.val ^^^ PEqualNP.Outside.L_meta_25514_aux.rot k (i + 3 * r + k - e - q) mask.val) r).testBit i := by
    rw [← hbefore, ← hbefore]
    exact hdiff
  rcases PEqualNP.Outside.L_meta_25514_aux.solve_25514 k r e q constants u i hq hr hk hu hi
    base mask hdiff' with ⟨d, h1, h2, h3⟩
  refine ⟨d, h1, h2, ?_⟩
  intro t hcut htre hrec
  dsimp only
  rw [hstate]
  exact h3 t hcut htre hrec
