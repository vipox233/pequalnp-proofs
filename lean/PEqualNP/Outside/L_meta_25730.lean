import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

-- Proof by Jonathan Nanhu (merged PR #41935, L_meta_29733, commit 87ac0d28), renamed for the statement posted as L-meta-25730.

namespace PEqualNP.Outside.L_meta_25730

def ofBits (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0

lemma foldl_or_shift_testBit (f : Nat → Bool) (l : List Nat) (acc j : Nat) :
    (l.foldl (fun a i => a ||| ((f i).toNat <<< i)) acc).testBit j =
      (acc.testBit j || (j ∈ l && f j)) := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft, List.mem_cons]
    by_cases hja : j = a
    · subst hja
      have hb0 : ((f j).toNat).testBit 0 = f j := by cases f j <;> simp
      simp only [ge_iff_le, le_refl, Nat.sub_self, hb0, decide_true, Bool.true_and, true_or]
      cases acc.testBit j <;> cases f j <;> simp
    · have hne : (decide (j ≥ a) && ((f a).toNat).testBit (j - a)) = false := by
        by_cases hge : j ≥ a
        · have hpos : 0 < j - a := by omega
          have hzero : ((f a).toNat).testBit (j - a) = false := by
            cases f a
            · simp
            · simp only [Bool.toNat_true]
              exact Nat.testBit_lt_two_pow (Nat.one_lt_two_pow (by omega))
          simp [hge, hzero]
        · simp [hge]
      have hne_dec : decide (j = a ∨ j ∈ t) = decide (j ∈ t) := by
        simp [hja]
      rw [hne, hne_dec]
      cases acc.testBit j <;> simp

lemma ofBits_testBit (n : Nat) (f : Nat → Bool) (j : Nat) :
    (ofBits n f).testBit j = if j < n then f j else false := by
  unfold ofBits
  rw [foldl_or_shift_testBit]
  simp [List.mem_range]

lemma lt_two_pow_of_testBit {x n : Nat} (h : ∀ j, n ≤ j → x.testBit j = false) : x < 2 ^ n := by
  have heq : x % 2 ^ n = x := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow]
    by_cases hj : j < n
    · simp [hj]
    · simp [hj, h j (by omega)]
  rw [← heq]
  exact Nat.mod_lt x (Nat.two_pow_pos n)

lemma ofBits_lt (n : Nat) (f : Nat → Bool) : ofBits n f < 2 ^ n := by
  apply lt_two_pow_of_testBit
  intro j hj
  rw [ofBits_testBit]
  simp [Nat.not_lt.mpr hj]

lemma xor_lt_two_pow {x y n : Nat} (hx : x < 2 ^ n) (hy : y < 2 ^ n) : (x ^^^ y) < 2 ^ n := by
  apply lt_two_pow_of_testBit
  intro j hj
  rw [Nat.testBit_xor, Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj)),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) hj))]
  rfl

lemma shiftRight_lt_two_pow {x k a : Nat} (hx : x < 2 ^ k) (ha : a ≤ k) :
    x >>> (k - a) < 2 ^ a := by
  apply lt_two_pow_of_testBit
  intro j hj
  rw [Nat.testBit_shiftRight]
  have hge : k ≤ k - a + j := by omega
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge))

lemma testBit_one_shiftLeft (p j : Nat) : (1 <<< p).testBit j = decide (j = p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases h : j = p
  · subst h
    simp
  · by_cases hge : p ≤ j
    · have hpos : 0 < j - p := by omega
      have hlt : 1 < 2 ^ (j - p) := Nat.one_lt_two_pow (by omega)
      simp [h, hge, Nat.testBit_lt_two_pow hlt]
    · simp [h, hge]

lemma flipBit_lt {x p k : Nat} (hx : x < 2 ^ k) (hp : p < k) : x ^^^ (1 <<< p) < 2 ^ k := by
  apply xor_lt_two_pow hx
  rw [Nat.shiftLeft_eq, one_mul]
  exact Nat.pow_lt_pow_right (by omega) hp

lemma testBit_flipBit (x p j : Nat) :
    (x ^^^ (1 <<< p)).testBit j = if j = p then !(x.testBit j) else x.testBit j := by
  rw [Nat.testBit_xor, testBit_one_shiftLeft]
  by_cases h : j = p <;> simp [h]

def bitAt (k x i : Nat) : Bool := x.testBit (i % k)

lemma bitAt_mod (k x i : Nat) : bitAt k x (i % k) = bitAt k x i := by
  simp [bitAt]

lemma bitAt_add_k (k x i : Nat) : bitAt k x (i + k) = bitAt k x i := by
  simp [bitAt, Nat.add_mod_right]

lemma bitAt_lt {k x i : Nat} (hi : i < k) : bitAt k x i = x.testBit i := by
  simp [bitAt, Nat.mod_eq_of_lt hi]

def rot (k offset x : Nat) : Nat :=
  ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k

lemma rot_lt {k offset x : Nat} : rot k offset x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma bitAt_rot_add {k offset x j : Nat} (hk : 0 < k) (hx : x < 2 ^ k) :
    bitAt k (rot k offset x) (j + offset) = bitAt k x j := by
  unfold bitAt rot
  set s := offset % k
  have hs : s < k := Nat.mod_lt offset hk
  set i := (j + offset) % k
  have hi : i < k := Nat.mod_lt _ hk
  simp only [Nat.testBit_mod_two_pow, hi, decide_true, Bool.true_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hi_eq : i = (j % k + s) % k := by
    simp [i, s, Nat.add_mod]
  have hjk : j % k < k := Nat.mod_lt j hk
  by_cases hsum : j % k + s < k
  · have hi_val : i = j % k + s := by rw [hi_eq, Nat.mod_eq_of_lt hsum]
    have hge1 : s ≤ i := by omega
    have hge2 : k ≤ k - s + i := by omega
    have hzero : x.testBit (k - s + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge2))
    have hsub : i - s = j % k := by omega
    simp [hge1, hzero, hsub]
  · have hi_val : i = j % k + s - k := by
      rw [hi_eq]
      have hlt2 : j % k + s - k < k := by omega
      have hmod : (j % k + s) % k = (j % k + s - k) % k := by
        have hsum_eq : j % k + s = (j % k + s - k) + k := by omega
        conv_lhs => rw [hsum_eq]
        rw [Nat.add_mod_right]
      rw [hmod, Nat.mod_eq_of_lt hlt2]
    have hlt1 : ¬ s ≤ i := by omega
    have hadd : k - s + i = j % k := by omega
    simp [hlt1, hadd]

lemma bitAt_rot_sub {k offset x i : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (hi : offset ≤ i) :
    bitAt k (rot k offset x) i = bitAt k x (i - offset) := by
  have h := bitAt_rot_add (k := k) (offset := offset) (x := x) (j := i - offset) hk hx
  rwa [Nat.sub_add_cancel hi] at h

lemma bitAt_rot_rev {k offset x i : Nat} (hk : 0 < k) (hx : x < 2 ^ k) :
    bitAt k (rot k (k - offset % k) x) i = bitAt k x (i + offset) := by
  have hs : offset % k < k := Nat.mod_lt offset hk
  have hmod : ((i + offset) + (k - offset % k)) % k = i % k := by
    have hdiv : offset = k * (offset / k) + offset % k := (Nat.div_add_mod offset k).symm
    have hrew : (i + offset) + (k - offset % k) = i + k * (offset / k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have h1 : bitAt k (rot k (k - offset % k) x) i =
      bitAt k (rot k (k - offset % k) x) ((i + offset) + (k - offset % k)) := by
    simp [bitAt, hmod]
  rw [h1]
  exact bitAt_rot_add hk hx

def mix (k gap value : Nat) : Nat :=
  value ^^^ rot k gap value ^^^ rot k (k - gap) value

lemma mix_lt {k gap v : Nat} (hv : v < 2 ^ k) : mix k gap v < 2 ^ k :=
  xor_lt_two_pow (xor_lt_two_pow hv rot_lt) rot_lt

lemma bitAt_mix {k gap v i : Nat} (hk : 0 < k) (hv : v < 2 ^ k) (hgap : gap < k) (hi : gap ≤ i) :
    bitAt k (mix k gap v) i =
      xor (xor (bitAt k v i) (bitAt k v (i - gap))) (bitAt k v (i + gap)) := by
  unfold mix
  have hmod : gap % k = gap := Nat.mod_eq_of_lt hgap
  have h1 : bitAt k (v ^^^ rot k gap v ^^^ rot k (k - gap) v) i =
      xor (xor (bitAt k v i) (bitAt k (rot k gap v) i)) (bitAt k (rot k (k - gap) v) i) := by
    simp [bitAt, Nat.testBit_xor]
  rw [h1, bitAt_rot_sub hk hv hi]
  have h2 : bitAt k (rot k (k - gap) v) i = bitAt k v (i + gap) := by
    have hr := bitAt_rot_rev (k := k) (offset := gap) (x := v) (i := i) hk hv
    rwa [hmod] at hr
  rw [h2]

def chi (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0

lemma chi_eq_ofBits (k word : Nat) :
    chi k word = ofBits k (fun site =>
      xor (word.testBit site)
        (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))) := rfl

lemma chi_lt {k word : Nat} : chi k word < 2 ^ k := by
  rw [chi_eq_ofBits]
  exact ofBits_lt k _

lemma bitAt_chi {k word i : Nat} (hk : 0 < k) :
    bitAt k (chi k word) i =
      xor (bitAt k word i) (!(bitAt k word (i + 1)) && bitAt k word (i + 2)) := by
  unfold bitAt
  simp only [chi_eq_ofBits, ofBits_testBit, Nat.mod_lt i hk, ↓reduceIte]
  have h1 : (i % k + 1) % k = (i + 1) % k := by simp [Nat.add_mod]
  have h2 : (i % k + 2) % k = (i + 2) % k := by simp [Nat.add_mod]
  rw [h1, h2]

def step (k r : Nat) (constants : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) : Nat :=
  chi k (mix k (if col then 2 else 1) prev) ^^^
    rot k (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
    (constants (if col then r + t else t)).val

lemma step_lt {k r : Nat} {c : Nat → Fin (2 ^ k)} {col : Bool} {raw prev t : Nat} :
    step k r c col raw prev t < 2 ^ k :=
  xor_lt_two_pow (xor_lt_two_pow chi_lt rot_lt) (c _).isLt

def stateStep (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun v tick => step k r c side key v (tick + 1))
    (rot k (if side then 3 else 1) key ^^^ name)

lemma stateStep_zero (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) :
    stateStep k r c side key name 0 = rot k (if side then 3 else 1) key ^^^ name := rfl

lemma stateStep_succ (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name n : Nat) :
    stateStep k r c side key name (n + 1) =
      step k r c side key (stateStep k r c side key name n) (n + 1) := by
  unfold stateStep
  rw [List.range_succ, List.foldl_append]
  rfl

lemma stateStep_lt {k r : Nat} {c : Nat → Fin (2 ^ k)} {side : Bool} {key name n : Nat}
    (hname : name < 2 ^ k) :
    stateStep k r c side key name n < 2 ^ k := by
  cases n with
  | zero => exact xor_lt_two_pow rot_lt hname
  | succ n =>
    rw [stateStep_succ]
    exact step_lt

def AgreeOn (k lo hi x y : Nat) : Prop :=
  ∀ i, lo ≤ i → i < hi → bitAt k x i = bitAt k y i

lemma agreeOn_mono {k lo1 hi1 lo2 hi2 x y : Nat}
    (h : AgreeOn k lo1 hi1 x y) (hlo : lo1 ≤ lo2) (hhi : hi2 ≤ hi1) :
    AgreeOn k lo2 hi2 x y :=
  fun i h1 h2 => h i (le_trans hlo h1) (lt_of_lt_of_le h2 hhi)

lemma xor_congr_left {a a' b : Bool} : xor (xor a b) (xor a' b) = xor a a' := by
  cases a <;> cases a' <;> cases b <;> rfl

lemma xor_congr_right {a b b' : Bool} : xor (xor a b) (xor a b') = xor b b' := by
  cases a <;> cases b <;> cases b' <;> rfl

def leftRow (t : Nat) : Nat := max (t + 1) (2 * (t - 1))

lemma row_dep {k r : Nat} {c : Nat → Fin (2 ^ k)} {row : Nat} (hk : 2 ≤ k) (hrow : row < 2 ^ k) :
    ∀ t w w' i, w < 2 ^ k → w' < 2 ^ k → leftRow t ≤ i →
      AgreeOn k (i - leftRow t) (i + 3 * t) w w' →
      bitAt k (stateStep k r c false w row t) i =
        bitAt k (stateStep k r c false w' row t) i := by
  intro t
  induction t with
  | zero =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_zero, stateStep_zero]
    simp only [Bool.false_eq_true, ↓reduceIte, bitAt, Nat.testBit_xor]
    have h1 : leftRow 0 = 1 := rfl
    have hr := hAg (i - 1) (by omega) (by omega)
    have hb1 : bitAt k (rot k 1 w) i = bitAt k w (i - 1) := bitAt_rot_sub (by omega) hw (by omega)
    have hb2 : bitAt k (rot k 1 w') i = bitAt k w' (i - 1) := bitAt_rot_sub (by omega) hw' (by omega)
    unfold bitAt at hb1 hb2 hr
    rw [hb1, hb2, hr]
  | succ t ih =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_succ, stateStep_succ]
    unfold step
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    have hlt1 : stateStep k r c false w row t < 2 ^ k := stateStep_lt hrow
    have hlt2 : stateStep k r c false w' row t < 2 ^ k := stateStep_lt hrow
    have hL : leftRow t + 1 ≤ leftRow (t + 1) := by unfold leftRow; omega
    have hraw : 2 * t ≤ leftRow (t + 1) := by unfold leftRow; omega
    have hM : ∀ d ≤ 2, bitAt k (mix k 1 (stateStep k r c false w row t)) (i + d) =
        bitAt k (mix k 1 (stateStep k r c false w' row t)) (i + d) := by
      intro d hd
      rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
        bitAt_mix (by omega) hlt2 (by omega) (by omega)]
      have h0 : bitAt k (stateStep k r c false w row t) (i + d) =
          bitAt k (stateStep k r c false w' row t) (i + d) :=
        ih w w' (i + d) hw hw' (by omega) (agreeOn_mono hAg (by omega) (by omega))
      have hm1 : bitAt k (stateStep k r c false w row t) (i + d - 1) =
          bitAt k (stateStep k r c false w' row t) (i + d - 1) :=
        ih w w' (i + d - 1) hw hw' (by omega) (agreeOn_mono hAg (by omega) (by omega))
      have hp1 : bitAt k (stateStep k r c false w row t) (i + d + 1) =
          bitAt k (stateStep k r c false w' row t) (i + d + 1) :=
        ih w w' (i + d + 1) hw hw' (by omega) (agreeOn_mono hAg (by omega) (by omega))
      rw [h0, hm1, hp1]
    have hM0 := hM 0 (by omega)
    simp only [Nat.add_zero] at hM0
    have hchi : bitAt k (chi k (mix k 1 (stateStep k r c false w row t))) i =
        bitAt k (chi k (mix k 1 (stateStep k r c false w' row t))) i := by
      rw [bitAt_chi (by omega), bitAt_chi (by omega), hM0, hM 1 (by omega), hM 2 (by omega)]
    have hrot : bitAt k (rot k (2 * t) w) i = bitAt k (rot k (2 * t) w') i := by
      rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
      exact hAg (i - 2 * t) (by omega) (by omega)
    have hxor : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
        xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
      intro a b d
      simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, hchi, hrot]

lemma row_pivot {k r : Nat} {c : Nat → Fin (2 ^ k)} {row : Nat} (hk : 2 ≤ k) (hrow : row < 2 ^ k) :
    ∀ t, t ≠ 3 → ∀ w w' i, w < 2 ^ k → w' < 2 ^ k → leftRow t ≤ i →
      AgreeOn k (i - leftRow t + 1) (i + 3 * t) w w' →
      xor (bitAt k (stateStep k r c false w row t) i)
          (bitAt k (stateStep k r c false w' row t) i) =
        xor (bitAt k w (i - leftRow t)) (bitAt k w' (i - leftRow t)) := by
  intro t ht
  induction t with
  | zero =>
    intro w w' i hw hw' hi _
    rw [stateStep_zero, stateStep_zero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hxor : ∀ a b, bitAt k (a ^^^ b) i = xor (bitAt k a i) (bitAt k b i) := by
      intro a b; simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, xor_congr_left]
    have hL : leftRow 0 = 1 := rfl
    rw [hL, bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
  | succ t ih =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_succ, stateStep_succ]
    unfold step
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    have hlt1 : stateStep k r c false w row t < 2 ^ k := stateStep_lt hrow
    have hlt2 : stateStep k r c false w' row t < 2 ^ k := stateStep_lt hrow
    have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
        xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
      intro a b d; simp [bitAt, Nat.testBit_xor]
    rw [hxor3, hxor3, xor_congr_left]
    by_cases ht3 : t < 3
    · have ht_ne3 : t ≠ 3 := by omega
      have hL_eq : leftRow (t + 1) = leftRow t + 1 := by
        simp only [leftRow, Nat.add_sub_cancel]
        omega
      have hraw_gt : i - leftRow (t + 1) + 1 ≤ i - 2 * t := by
        simp only [leftRow, Nat.add_sub_cancel] at hi ⊢
        omega
      have hraw_lt : i - 2 * t < i + 3 * (t + 1) := by omega
      have hrot : bitAt k (rot k (2 * t) w) i = bitAt k (rot k (2 * t) w') i := by
        rw [bitAt_rot_sub (by omega) hw (by unfold leftRow at hi; omega),
          bitAt_rot_sub (by omega) hw' (by unfold leftRow at hi; omega)]
        exact hAg (i - 2 * t) hraw_gt hraw_lt
      rw [hrot, xor_congr_left, bitAt_chi (by omega), bitAt_chi (by omega)]
      have hM_eq : ∀ d, 1 ≤ d → d ≤ 2 →
          bitAt k (mix k 1 (stateStep k r c false w row t)) (i + d) =
            bitAt k (mix k 1 (stateStep k r c false w' row t)) (i + d) := by
        intro d hd1 hd2
        rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
          bitAt_mix (by omega) hlt2 (by omega) (by omega)]
        have h0 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hm1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d - 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d + 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        rw [h0, hm1, hp1]
      rw [hM_eq 1 (by omega) (by omega), hM_eq 2 (by omega) (by omega), xor_congr_left]
      rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
        bitAt_mix (by omega) hlt2 (by omega) (by omega)]
      have h0 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' i hw hw'
        (by omega) (agreeOn_mono hAg (by omega) (by omega))
      have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + 1) hw hw'
        (by omega) (agreeOn_mono hAg (by omega) (by omega))
      rw [h0, hp1, xor_congr_left, xor_congr_right]
      have hpiv := ih ht_ne3 w w' (i - 1) hw hw' (by omega)
        (agreeOn_mono hAg (by omega) (by omega))
      have hsub_eq : i - 1 - leftRow t = i - leftRow (t + 1) := by omega
      rwa [hsub_eq] at hpiv
    · have ht_ge3 : 3 ≤ t := by omega
      have hL_eq : leftRow (t + 1) = 2 * t := by
        simp only [leftRow, Nat.add_sub_cancel]
        omega
      have hprev_lt : leftRow t + 1 < 2 * t := by
        simp only [leftRow]
        omega
      have hM_all : ∀ d ≤ 2,
          bitAt k (mix k 1 (stateStep k r c false w row t)) (i + d) =
            bitAt k (mix k 1 (stateStep k r c false w' row t)) (i + d) := by
        intro d hd
        rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
          bitAt_mix (by omega) hlt2 (by omega) (by omega)]
        have h0 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hm1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d - 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow t w w' (i + d + 1) hw hw'
          (by omega) (agreeOn_mono hAg (by omega) (by omega))
        rw [h0, hm1, hp1]
      have hM0 := hM_all 0 (by omega)
      simp only [Nat.add_zero] at hM0
      have hchi : bitAt k (chi k (mix k 1 (stateStep k r c false w row t))) i =
          bitAt k (chi k (mix k 1 (stateStep k r c false w' row t))) i := by
        rw [bitAt_chi (by omega), bitAt_chi (by omega),
          hM0, hM_all 1 (by omega), hM_all 2 (by omega)]
      rw [hchi, xor_congr_right, hL_eq,
        bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]

lemma row_mix_pivot {k r : Nat} {c : Nat → Fin (2 ^ k)} {row : Nat} (hk : 2 ≤ k) (hrow : row < 2 ^ k)
    {t : Nat} (ht1 : 1 ≤ t) (ht4 : t ≠ 4) {w w' i : Nat}
    (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hi : leftRow (t - 1) + 1 ≤ i)
    (hAg : AgreeOn k (i - (leftRow (t - 1) + 1) + 1) (i + 3 * t - 2) w w') :
    xor (bitAt k (mix k 1 (stateStep k r c false w row (t - 1))) i)
        (bitAt k (mix k 1 (stateStep k r c false w' row (t - 1))) i) =
      xor (bitAt k w (i - (leftRow (t - 1) + 1))) (bitAt k w' (i - (leftRow (t - 1) + 1))) := by
  have hlt1 : stateStep k r c false w row (t - 1) < 2 ^ k := stateStep_lt hrow
  have hlt2 : stateStep k r c false w' row (t - 1) < 2 ^ k := stateStep_lt hrow
  rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
    bitAt_mix (by omega) hlt2 (by omega) (by omega)]
  have h0 := row_dep (r := r) (c := c) (row := row) hk hrow (t - 1) w w' i hw hw'
    (by omega) (agreeOn_mono hAg (by omega) (by omega))
  have hp1 := row_dep (r := r) (c := c) (row := row) hk hrow (t - 1) w w' (i + 1) hw hw'
    (by omega) (agreeOn_mono hAg (by omega) (by omega))
  rw [h0, hp1, xor_congr_left, xor_congr_right]
  have hpiv := row_pivot (r := r) (c := c) (row := row) hk hrow (t - 1) (by omega) w w' (i - 1) hw hw'
    (by omega) (agreeOn_mono hAg (by omega) (by omega))
  have hsub : i - 1 - leftRow (t - 1) = i - (leftRow (t - 1) + 1) := by omega
  rwa [hsub] at hpiv

def leftCol (t : Nat) : Nat := max (2 * t + 3) (3 * t + 1)

lemma col_dep {k r : Nat} {c : Nat → Fin (2 ^ k)} {col : Nat} (hk : 3 ≤ k) (hcol : col < 2 ^ k) :
    ∀ t w w' i, w < 2 ^ k → w' < 2 ^ k → leftCol t ≤ i →
      AgreeOn k (i - leftCol t) (if t = 0 then i - 2 else i + 4 * t - 2) w w' →
      bitAt k (stateStep k r c true w col t) i =
        bitAt k (stateStep k r c true w' col t) i := by
  intro t
  induction t with
  | zero =>
    intro w w' i hw hw' hi hAg
    rw [stateStep_zero, stateStep_zero]
    simp only [↓reduceIte]
    have hL : leftCol 0 = 3 := rfl
    have hxor : ∀ a b, bitAt k (a ^^^ b) i = xor (bitAt k a i) (bitAt k b i) := by
      intro a b; simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
    have h1 := hAg (i - 3) (by omega) (by simp; omega)
    rw [h1]
  | succ t ih =>
    intro w w' i hw hw' hi hAg
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte] at hAg
    rw [stateStep_succ, stateStep_succ]
    unfold step
    simp only [↓reduceIte]
    have hlt1 : stateStep k r c true w col t < 2 ^ k := stateStep_lt hcol
    have hlt2 : stateStep k r c true w' col t < 2 ^ k := stateStep_lt hcol
    have hL : leftCol t + 2 ≤ leftCol (t + 1) := by unfold leftCol; omega
    have hraw : 3 * (t + 1) + 1 ≤ leftCol (t + 1) := by unfold leftCol; omega
    have hN : ∀ d ≤ 2, bitAt k (mix k 2 (stateStep k r c true w col t)) (i + d) =
        bitAt k (mix k 2 (stateStep k r c true w' col t)) (i + d) := by
      intro d hd
      rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
        bitAt_mix (by omega) hlt2 (by omega) (by omega)]
      have h0 : bitAt k (stateStep k r c true w col t) (i + d) =
          bitAt k (stateStep k r c true w' col t) (i + d) :=
        ih w w' (i + d) hw hw' (by omega)
          (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
      have hm2 : bitAt k (stateStep k r c true w col t) (i + d - 2) =
          bitAt k (stateStep k r c true w' col t) (i + d - 2) :=
        ih w w' (i + d - 2) hw hw' (by omega)
          (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
      have hp2 : bitAt k (stateStep k r c true w col t) (i + d + 2) =
          bitAt k (stateStep k r c true w' col t) (i + d + 2) :=
        ih w w' (i + d + 2) hw hw' (by omega)
          (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
      rw [h0, hm2, hp2]
    have hN0 := hN 0 (by omega)
    simp only [Nat.add_zero] at hN0
    have hchi : bitAt k (chi k (mix k 2 (stateStep k r c true w col t))) i =
        bitAt k (chi k (mix k 2 (stateStep k r c true w' col t))) i := by
      rw [bitAt_chi (by omega), bitAt_chi (by omega),
        hN0, hN 1 (by omega), hN 2 (by omega)]
    have hrot : bitAt k (rot k (3 * (t + 1) + 1) w) i = bitAt k (rot k (3 * (t + 1) + 1) w') i := by
      rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
      exact hAg (i - (3 * (t + 1) + 1)) (by omega) (by omega)
    have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
        xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
      intro a b d; simp [bitAt, Nat.testBit_xor]
    rw [hxor3, hxor3, hchi, hrot]

lemma col_pivot {k r : Nat} {c : Nat → Fin (2 ^ k)} {col : Nat} (hk : 3 ≤ k) (hcol : col < 2 ^ k)
    {t : Nat} (ht : 3 ≤ t) {w w' i : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hi : 3 * t + 1 ≤ i)
    (hAg : AgreeOn k (i - (3 * t + 1) + 1) (i + 4 * t - 2) w w') :
    xor (bitAt k (stateStep k r c true w col t) i)
        (bitAt k (stateStep k r c true w' col t) i) =
      xor (bitAt k w (i - (3 * t + 1))) (bitAt k w' (i - (3 * t + 1))) := by
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [stateStep_succ, stateStep_succ]
  unfold step
  simp only [↓reduceIte]
  have hlt1 : stateStep k r c true w col t' < 2 ^ k := stateStep_lt hcol
  have hlt2 : stateStep k r c true w' col t' < 2 ^ k := stateStep_lt hcol
  have hprev : leftCol t' + 2 < 3 * (t' + 1) + 1 := by unfold leftCol; omega
  have hN : ∀ d ≤ 2, bitAt k (mix k 2 (stateStep k r c true w col t')) (i + d) =
      bitAt k (mix k 2 (stateStep k r c true w' col t')) (i + d) := by
    intro d hd
    rw [bitAt_mix (by omega) hlt1 (by omega) (by omega),
      bitAt_mix (by omega) hlt2 (by omega) (by omega)]
    have h0 := col_dep (r := r) (c := c) (col := col) hk hcol t' w w' (i + d) hw hw'
      (by omega) (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
    have hm2 := col_dep (r := r) (c := c) (col := col) hk hcol t' w w' (i + d - 2) hw hw'
      (by omega) (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
    have hp2 := col_dep (r := r) (c := c) (col := col) hk hcol t' w w' (i + d + 2) hw hw'
      (by omega) (agreeOn_mono hAg (by omega) (by split_ifs <;> omega))
    rw [h0, hm2, hp2]
  have hN0 := hN 0 (by omega)
  simp only [Nat.add_zero] at hN0
  have hchi : bitAt k (chi k (mix k 2 (stateStep k r c true w col t'))) i =
      bitAt k (chi k (mix k 2 (stateStep k r c true w' col t'))) i := by
    rw [bitAt_chi (by omega), bitAt_chi (by omega),
      hN0, hN 1 (by omega), hN 2 (by omega)]
  have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
      xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
    intro a b d; simp [bitAt, Nat.testBit_xor]
  rw [hxor3, hxor3, xor_congr_left, hchi, xor_congr_right,
    bitAt_rot_sub (by omega) hw hi, bitAt_rot_sub (by omega) hw' hi]

lemma triangular_solve {k base m : Nat} (hbm : base + m ≤ k)
    (F : Nat → Nat) (hF_lt : ∀ w < 2 ^ k, F w < 2 ^ m)
    (hTri : ∀ j < m, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < base ∨ base + j < s) → w.testBit s = w'.testBit s) →
      xor ((F w).testBit j) ((F w').testBit j) =
        xor (w.testBit (base + j)) (w'.testBit (base + j)))
    (w0 : Nat) (hw0 : w0 < 2 ^ k) (target : Nat) (htgt : target < 2 ^ m) :
    ∃! w : Fin (2 ^ k),
      (∀ s < k, (s < base ∨ base + m ≤ s) → w.val.testBit s = w0.testBit s) ∧
      F w.val = target := by
  have hex : ∀ d ≤ m, ∃ w < 2 ^ k,
      (∀ s < k, (s < base ∨ base + m ≤ s) → w.testBit s = w0.testBit s) ∧
      (∀ j, m - d ≤ j → j < m → (F w).testBit j = target.testBit j) := by
    intro d
    induction d with
    | zero =>
      intro _
      refine ⟨w0, hw0, fun _ _ _ => rfl, ?_⟩
      intro j hj1 hj2
      omega
    | succ d ih =>
      intro hd
      rcases ih (by omega) with ⟨w, hw, hout, htop⟩
      let j0 := m - (d + 1)
      have hj0 : j0 < m := by omega
      by_cases hmatch : (F w).testBit j0 = target.testBit j0
      · refine ⟨w, hw, hout, ?_⟩
        intro j hj1 hj2
        by_cases heq : j = j0
        · rw [heq]; exact hmatch
        · exact htop j (by omega) hj2
      · let w' := w ^^^ (1 <<< (base + j0))
        have hw' : w' < 2 ^ k := flipBit_lt hw (by omega)
        refine ⟨w', hw', ?_, ?_⟩
        · intro s hs hso
          rw [testBit_flipBit]
          have hne : s ≠ base + j0 := by omega
          simp [hne, hout s hs hso]
        · intro j hj1 hj2
          by_cases heq : j = j0
          · subst heq
            have hAg : ∀ s < k, (s < base ∨ base + j0 < s) → w.testBit s = w'.testBit s := by
              intro s _ hso
              rw [testBit_flipBit]
              have hne : s ≠ base + j0 := by omega
              simp [hne]
            have hxor := hTri j0 hj0 w w' hw hw' hAg
            have hflip : w'.testBit (base + j0) = !(w.testBit (base + j0)) := by
              simp [w']
            rw [hflip] at hxor
            cases hb1 : (F w).testBit j0 <;> cases hb2 : (F w').testBit j0 <;>
              cases ht : target.testBit j0 <;> cases hwb : w.testBit (base + j0) <;>
              simp_all
          · have hgt : j0 < j := by omega
            have hAg : ∀ s < k, (s < base ∨ base + j < s) → w.testBit s = w'.testBit s := by
              intro s _ hso
              rw [testBit_flipBit]
              have hne : s ≠ base + j0 := by omega
              simp [hne]
            have hxor := hTri j hj2 w w' hw hw' hAg
            have hsame : w'.testBit (base + j) = w.testBit (base + j) := by
              have hne : base + j ≠ base + j0 := by omega
              simp only [w', testBit_flipBit, hne, ↓reduceIte]
            rw [hsame] at hxor
            have hFeq : (F w').testBit j = (F w).testBit j := by
              cases h1 : (F w).testBit j <;> cases h2 : (F w').testBit j <;> simp_all
            rw [hFeq]
            exact htop j (by omega) hj2
  rcases hex m (le_refl _) with ⟨w, hw, hout, hall⟩
  have hFw : F w = target := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < m
    · exact hall j (by omega) hj
    · have hge : m ≤ j := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hF_lt w hw) (Nat.pow_le_pow_right (by omega) hge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by omega) hge))]
  refine ⟨⟨w, hw⟩, ⟨hout, hFw⟩, ?_⟩
  rintro ⟨w2, hw2⟩ ⟨hout2, hFw2⟩
  apply Fin.ext
  have htop_eq : ∀ d ≤ m, ∀ j, m - d ≤ j → j < m → w2.testBit (base + j) = w.testBit (base + j) := by
    intro d
    induction d with
    | zero => intro _ j hj1 hj2; omega
    | succ d ih =>
      intro hd j hj1 hj2
      by_cases heq : j = m - (d + 1)
      · subst heq
        have hAg : ∀ s < k, (s < base ∨ base + (m - (d + 1)) < s) → w2.testBit s = w.testBit s := by
          intro s hs hso
          rcases hso with hlt | hgt
          · rw [hout2 s hs (Or.inl hlt), hout s hs (Or.inl hlt)]
          · by_cases hge : base + m ≤ s
            · rw [hout2 s hs (Or.inr hge), hout s hs (Or.inr hge)]
            · have hsub := ih (by omega) (s - base) (by omega) (by omega)
              have hrew : base + (s - base) = s := by omega
              rwa [hrew] at hsub
        have hxor := hTri (m - (d + 1)) (by omega) w2 w hw2 hw hAg
        rw [hFw2, hFw] at hxor
        cases h1 : w2.testBit (base + (m - (d + 1))) <;>
          cases h2 : w.testBit (base + (m - (d + 1))) <;> simp_all
      · exact ih (by omega) j (by omega) hj2
  apply Nat.eq_of_testBit_eq
  intro s
  by_cases hsk : s < k
  · by_cases hin : base ≤ s ∧ s < base + m
    · have h1 := htop_eq m (le_refl _) (s - base) (by omega) (by omega)
      have hrew : base + (s - base) = s := by omega
      rwa [hrew] at h1
    · have hso : s < base ∨ base + m ≤ s := by omega
      rw [hout2 s hsk hso, hout s hsk hso]
  · have hge : k ≤ s := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hw2 (Nat.pow_le_pow_right (by omega) hge)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))]

def histStep (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (ref : Nat)
    (triple : Nat × Nat × Nat) (idx : Nat) : Nat × Nat × Nat :=
  let time := idx + 1
  let place := k - q + 3 * (r - time) + min (q - 1) triple.2.2
  let bit := (mix k 1 triple.1).testBit ((place + 1) % k)
  let next := step k r sched false ref triple.1 time
  if time = 4 then (next, triple.2.1, triple.2.2)
  else (next, 2 * triple.2.1 + bit.toNat, triple.2.2 + bit.toNat)

def histFold (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) : Nat × Nat × Nat :=
  (List.range n).foldl (histStep k r q sched ref) (rot k 1 ref ^^^ row, 0, 0)

lemma histFold_zero (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref : Nat) :
    histFold k r q sched row ref 0 = (rot k 1 ref ^^^ row, 0, 0) := rfl

lemma histFold_succ (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) :
    histFold k r q sched row ref (n + 1) =
      histStep k r q sched ref (histFold k r q sched row ref n) n := by
  unfold histFold
  rw [List.range_succ, List.foldl_append]
  rfl

lemma histFold_fst (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) :
    (histFold k r q sched row ref n).1 = stateStep k r sched false ref row n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [histFold_succ, stateStep_succ]
    unfold histStep
    dsimp only
    split_ifs <;> simp [ih]

def recCount (n : Nat) : Nat := if n < 4 then n else n - 1

def bitWeight (m code : Nat) : Nat :=
  ((List.range m).filter (fun jj => code.testBit jj)).length

lemma bitWeight_step (m code : Nat) (b : Bool) :
    bitWeight (m + 1) (2 * code + b.toNat) = bitWeight m code + b.toNat := by
  unfold bitWeight
  rw [List.range_succ_eq_map, List.filter_cons]
  have h0 : (2 * code + b.toNat).testBit 0 = b := by
    cases b <;> simp [Nat.testBit_zero]
  have hsucc : ∀ j, (2 * code + b.toNat).testBit (j + 1) = code.testBit j := by
    intro j
    rw [Nat.testBit_succ]
    have hdiv : (2 * code + b.toNat) / 2 = code := by
      cases b
      · simp
      · simp only [Bool.toNat_true]; omega
    rw [hdiv]
  rw [List.filter_map]
  have hcomp : ((fun jj => (2 * code + b.toNat).testBit jj) ∘ Nat.succ) =
      (fun jj => code.testBit jj) := by
    funext j
    exact hsucc j
  rw [hcomp, h0]
  cases b <;> simp [List.length_map]

lemma histFold_code_weight (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n : Nat) :
    (histFold k r q sched row ref n).2.1 < 2 ^ (recCount n) ∧
    (histFold k r q sched row ref n).2.2 =
      bitWeight (recCount n) (histFold k r q sched row ref n).2.1 := by
  induction n with
  | zero =>
    simp [histFold_zero, recCount, bitWeight]
  | succ n ih =>
    rw [histFold_succ]
    unfold histStep
    dsimp only
    by_cases h4 : n + 1 = 4
    · have hrec : recCount (n + 1) = recCount n := by unfold recCount; split_ifs <;> omega
      rw [hrec]
      simp only [h4, ↓reduceIte]
      exact ih
    · have hrec : recCount (n + 1) = recCount n + 1 := by unfold recCount; split_ifs <;> omega
      rw [hrec]
      simp only [h4, ↓reduceIte]
      constructor
      · have hb : ((mix k 1 (histFold k r q sched row ref n).1).testBit
            ((k - q + 3 * (r - (n + 1)) + min (q - 1) (histFold k r q sched row ref n).2.2 + 1) % k)).toNat ≤ 1 := by
          cases (mix k 1 (histFold k r q sched row ref n).1).testBit _ <;> decide
        have h1 := ih.1
        rw [Nat.pow_succ]
        omega
      · rw [bitWeight_step, ih.2]

lemma histFold_code_testBit (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref : Nat) :
    ∀ n m, m ≤ n →
      ∀ j < recCount m,
        (histFold k r q sched row ref n).2.1.testBit (j + (recCount n - recCount m)) =
          (histFold k r q sched row ref m).2.1.testBit j := by
  intro n
  induction n with
  | zero =>
    intro m hm j hj
    have hm0 : m = 0 := by omega
    subst hm0
    simp
  | succ n ih =>
    intro m hm j hj
    by_cases hmeq : m = n + 1
    · subst hmeq
      simp
    · have hmn : m ≤ n := by omega
      rw [histFold_succ]
      unfold histStep
      dsimp only
      by_cases h4 : n + 1 = 4
      · have hrec : recCount (n + 1) = recCount n := by unfold recCount; split_ifs <;> omega
        rw [hrec]
        simp only [h4, ↓reduceIte]
        exact ih m hmn j hj
      · have hrec : recCount (n + 1) = recCount n + 1 := by unfold recCount; split_ifs <;> omega
        have hrm : recCount m ≤ recCount n := by unfold recCount; split_ifs <;> omega
        simp only [h4, ↓reduceIte]
        have hidx : j + (recCount (n + 1) - recCount m) =
            (j + (recCount n - recCount m)) + 1 := by omega
        rw [hidx, Nat.testBit_succ]
        set bb := (mix k 1 (histFold k r q sched row ref n).1).testBit
          ((k - q + 3 * (r - (n + 1)) + min (q - 1) (histFold k r q sched row ref n).2.2 + 1) % k)
        have hdiv : (2 * (histFold k r q sched row ref n).2.1 + bb.toNat) / 2 =
            (histFold k r q sched row ref n).2.1 := by
          cases bb
          · simp
          · simp only [Bool.toNat_true]; omega
        rw [hdiv]
        exact ih m hmn j hj

lemma histFold_emit_bit (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref n ell : Nat)
    (hn : n + 1 ≤ ell) (h4 : n + 1 ≠ 4) :
    (histFold k r q sched row ref ell).2.1.testBit (recCount ell - recCount (n + 1)) =
      (mix k 1 (stateStep k r sched false ref row n)).testBit
        ((k - q + 3 * (r - (n + 1)) + min (q - 1) (histFold k r q sched row ref n).2.2 + 1) % k) := by
  have h1 := histFold_code_testBit k r q sched row ref ell (n + 1) hn 0
    (by unfold recCount; split_ifs <;> omega)
  simp only [Nat.zero_add] at h1
  rw [h1, histFold_succ]
  unfold histStep
  simp only [h4, ↓reduceIte, histFold_fst]
  cases (mix k 1 (stateStep k r sched false ref row n)).testBit _ <;> simp [Nat.testBit_zero]

def roundOf (s : Nat) : Nat := if s < 3 then s + 1 else s + 2

def targetCount (tries hist s : Nat) : Nat :=
  ((List.range s).filter (fun j => hist.testBit (tries - 1 - j))).length

lemma targetCount_zero (tries hist : Nat) : targetCount tries hist 0 = 0 := rfl

lemma targetCount_succ (tries hist s : Nat) :
    targetCount tries hist (s + 1) =
      targetCount tries hist s + (hist.testBit (tries - 1 - s)).toNat := by
  unfold targetCount
  rw [List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  cases hist.testBit (tries - 1 - s) <;> simp

lemma targetCount_le (tries hist s : Nat) : targetCount tries hist s ≤ s := by
  induction s with
  | zero => simp [targetCount_zero]
  | succ s ih =>
    rw [targetCount_succ]
    cases hist.testBit (tries - 1 - s) <;> simp <;> omega

lemma histFold_cnt_of_prefix (k r q ell : Nat) (sched : Nat → Fin (2 ^ k)) (row ref hist : Nat)
    (_hell : 5 ≤ ell) :
    ∀ s ≤ ell - 1,
      (∀ j < s,
        (mix k 1 (stateStep k r sched false ref row (roundOf j - 1))).testBit
          ((k - q + 3 * (r - roundOf j) +
            min (q - 1) (histFold k r q sched row ref (roundOf j - 1)).2.2 + 1) % k) =
          hist.testBit (ell - 1 - 1 - j)) →
      (histFold k r q sched row ref (if s < 3 then s else s + 1)).2.2 =
        targetCount (ell - 1) hist s := by
  intro s
  induction s with
  | zero =>
    intro _ _
    simp [histFold_zero, targetCount_zero]
  | succ s ih =>
    intro hs hpre
    have hprev := ih (by omega) (fun j hj => hpre j (by omega))
    have hbit := hpre s (by omega)
    rw [targetCount_succ, ← hprev]
    by_cases hs2 : s < 2
    · have hs3 : s + 1 < 3 := by omega
      have hs3' : s < 3 := by omega
      have hro : roundOf s = s + 1 := by unfold roundOf; simp [hs3']
      simp only [hs3, hs3', ↓reduceIte] at hprev ⊢
      rw [hro, Nat.add_sub_cancel] at hbit
      rw [histFold_succ]
      unfold histStep
      have hne4 : s + 1 ≠ 4 := by omega
      simp only [hne4, ↓reduceIte, histFold_fst, hbit]
    · by_cases hs2eq : s = 2
      · subst hs2eq
        have hro : roundOf 2 = 3 := by unfold roundOf; decide
        rw [hro] at hbit
        simp only [show ¬ (2 + 1 < 3) by omega, show (2 < 3) by omega, ↓reduceIte] at hprev ⊢
        rw [histFold_succ]
        unfold histStep
        simp only [show 3 + 1 = 4 by decide, ↓reduceIte]
        rw [histFold_succ]
        unfold histStep
        simp only [show 2 + 1 ≠ 4 by decide, ↓reduceIte, histFold_fst]
        rw [hbit]
      · have hsge3 : 3 ≤ s := by omega
        have hro : roundOf s = s + 2 := by unfold roundOf; split_ifs <;> omega
        simp only [show ¬ (s + 1 < 3) by omega, show ¬ (s < 3) by omega, ↓reduceIte] at hprev ⊢
        rw [hro] at hbit
        have hsub : s + 2 - 1 = s + 1 := by omega
        rw [hsub] at hbit
        rw [histFold_succ]
        unfold histStep
        have hne4 : s + 1 + 1 ≠ 4 := by omega
        simp only [hne4, ↓reduceIte, histFold_fst]
        have heq1 : s + 1 + 1 = s + 2 := by omega
        rw [heq1, hbit]

lemma histFold_eq_iff_bits (k r q ell : Nat) (sched : Nat → Fin (2 ^ k)) (row ref hist : Nat)
    (hell : 5 ≤ ell) (hhist : hist < 2 ^ (ell - 1)) :
    (histFold k r q sched row ref ell).2.1 = hist ↔
      ∀ s < ell - 1,
        (mix k 1 (stateStep k r sched false ref row (roundOf s - 1))).testBit
          ((k - q + 3 * (r - roundOf s) +
            min (q - 1) (histFold k r q sched row ref (roundOf s - 1)).2.2 + 1) % k) =
          hist.testBit (ell - 1 - 1 - s) := by
  have hrec_ell : recCount ell = ell - 1 := by unfold recCount; split_ifs <;> omega
  have hlt_code : (histFold k r q sched row ref ell).2.1 < 2 ^ (ell - 1) := by
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row ref ell).1
  constructor
  · intro heq s hs
    have hro_lt : roundOf s ≤ ell := by unfold roundOf; split_ifs <;> omega
    have hro_ne4 : roundOf s ≠ 4 := by unfold roundOf; split_ifs <;> omega
    have hro_pos : 1 ≤ roundOf s := by unfold roundOf; split_ifs <;> omega
    have hrec_ro : recCount (roundOf s) = s + 1 := by unfold roundOf recCount; split_ifs <;> omega
    have hem := histFold_emit_bit k r q sched row ref (roundOf s - 1) ell
      (by omega) (by omega)
    rw [Nat.sub_add_cancel hro_pos, hrec_ell, hrec_ro, heq] at hem
    have hidx : ell - 1 - (s + 1) = ell - 1 - 1 - s := by omega
    rw [hidx] at hem
    exact hem.symm
  · intro hbits
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < ell - 1
    · let s := ell - 1 - 1 - j
      have hs : s < ell - 1 := by omega
      have hj_eq : ell - 1 - 1 - s = j := by omega
      have hro_lt : roundOf s ≤ ell := by unfold roundOf; split_ifs <;> omega
      have hro_ne4 : roundOf s ≠ 4 := by unfold roundOf; split_ifs <;> omega
      have hro_pos : 1 ≤ roundOf s := by unfold roundOf; split_ifs <;> omega
      have hrec_ro : recCount (roundOf s) = s + 1 := by unfold roundOf recCount; split_ifs <;> omega
      have hem := histFold_emit_bit k r q sched row ref (roundOf s - 1) ell
        (by omega) (by omega)
      rw [Nat.sub_add_cancel hro_pos, hrec_ell, hrec_ro] at hem
      have hidx : ell - 1 - (s + 1) = j := by omega
      rw [hidx] at hem
      rw [hem, hbits s hs, hj_eq]
    · have hge : ell - 1 ≤ j := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt_code (Nat.pow_le_pow_right (by omega) hge)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hhist (Nat.pow_le_pow_right (by omega) hge))]

def pivOf (r q ell hist s : Nat) : Nat :=
  if s < 3 then
    (5 * r - 3) + 1 - q - 4 * (s + 1) + min (q - 1) (targetCount (ell - 1) hist s)
  else
    (5 * r - 3) + 5 - q - 5 * (s + 2) + min (q - 1) (targetCount (ell - 1) hist s)

lemma pivOf_lt (r q ell hist s : Nat) (hq : 0 < q) (hell5 : 5 ≤ ell) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (hs : s < ell - 1) :
    pivOf r q ell hist s < 5 * r - 3 - q := by
  unfold pivOf
  have hc : targetCount (ell - 1) hist s ≤ s := targetCount_le _ _ _
  split_ifs <;> omega

lemma pivOf_strictAnti (r q ell hist : Nat) (hq : 0 < q) (hell5 : 5 ≤ ell)
    (h5 : 5 * ell + q ≤ 5 * r + 2) :
    ∀ s1 s2, s1 < s2 → s2 < ell - 1 → pivOf r q ell hist s2 < pivOf r q ell hist s1 := by
  have hstep : ∀ s, s + 1 < ell - 1 → pivOf r q ell hist (s + 1) < pivOf r q ell hist s := by
    intro s hs
    unfold pivOf
    have hc1 := targetCount_succ (ell - 1) hist s
    have hble : (hist.testBit (ell - 1 - 1 - s)).toNat ≤ 1 := by
      cases hist.testBit _ <;> decide
    have hcle := targetCount_le (ell - 1) hist s
    have hcle1 := targetCount_le (ell - 1) hist (s + 1)
    split_ifs <;> omega
  intro s1 s2 hlt hs2
  obtain ⟨d, rfl⟩ : ∃ d, s2 = s1 + (d + 1) := ⟨s2 - s1 - 1, by omega⟩
  induction d with
  | zero => exact hstep s1 (by omega)
  | succ d ih =>
    exact lt_trans (hstep (s1 + (d + 1)) (by omega)) (ih (by omega) (by omega))

lemma pivOf_bit_pivot {k r q ell : Nat} {sched : Nat → Fin (2 ^ k)} {row : Nat}
    (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k) (hell5 : 5 ≤ ell) (hellr : ell ≤ r)
    (h5 : 5 * ell + q ≤ 5 * r + 2) (hrow : row < 2 ^ k)
    (hist : Nat) {s : Nat} (hs : s < ell - 1)
    {tag1 tag2 : Nat} (htag1 : tag1 < 2 ^ (5 * r - 3 - q)) (htag2 : tag2 < 2 ^ (5 * r - 3 - q))
    (hAgTag : ∀ j, pivOf r q ell hist s < j → j < 5 * r - 3 - q →
      tag1.testBit j = tag2.testBit j) :
    xor ((mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) tag1) row (roundOf s - 1))).testBit
          ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist s) + 1) % k))
        ((mix k 1 (stateStep k r sched false (rot k (k - (2 * r - 2)) tag2) row (roundOf s - 1))).testBit
          ((k - q + 3 * (r - roundOf s) + min (q - 1) (targetCount (ell - 1) hist s) + 1) % k)) =
      xor (tag1.testBit (pivOf r q ell hist s)) (tag2.testBit (pivOf r q ell hist s)) := by
  set start := k - (2 * r - 2)
  set ref1 := rot k start tag1
  set ref2 := rot k start tag2
  set t := roundOf s
  set d := min (q - 1) (targetCount (ell - 1) hist s)
  set place := k - q + 3 * (r - t) + d
  have hk_pos : 0 < k := by omega
  have huq_lt_k : 5 * r - 3 - q < k := by omega
  have htag1_k : tag1 < 2 ^ k :=
    lt_trans htag1 (Nat.pow_lt_pow_right (by omega) huq_lt_k)
  have htag2_k : tag2 < 2 ^ k :=
    lt_trans htag2 (Nat.pow_lt_pow_right (by omega) huq_lt_k)
  have href1_k : ref1 < 2 ^ k := rot_lt
  have href2_k : ref2 < 2 ^ k := rot_lt
  have ht1 : 1 ≤ t := by simp only [t, roundOf]; split_ifs <;> omega
  have ht4 : t ≠ 4 := by simp only [t, roundOf]; split_ifs <;> omega
  have htle : t ≤ ell := by simp only [t, roundOf]; split_ifs <;> omega
  have hdl : d ≤ q - 1 := Nat.min_le_left _ _
  have hdc : d ≤ s := le_trans (Nat.min_le_right _ _) (targetCount_le _ _ _)
  have hplace_ge : leftRow (t - 1) + 1 ≤ place + 1 := by
    simp only [place, leftRow, t, roundOf]
    split_ifs <;> omega
  have hpi_eq : place + 1 - (leftRow (t - 1) + 1) = start + pivOf r q ell hist s := by
    have hL : leftRow (t - 1) + 1 = if s < 3 then t + 1 else 2 * t - 3 := by
      simp only [leftRow, t, roundOf]
      split_ifs <;> omega
    rw [hL]
    simp only [place, start, pivOf, t, d, roundOf]
    split_ifs <;> omega
  have hhi_le : place + 1 + 3 * t - 2 ≤ start + k := by
    simp only [place, start]
    omega
  have hAgRef : AgreeOn k (place + 1 - (leftRow (t - 1) + 1) + 1) (place + 1 + 3 * t - 2)
      ref1 ref2 := by
    intro i hi1 hi2
    have hge_start : start ≤ i := by omega
    have hsub_lt_k : i - start < k := by omega
    have hsub_gt_piv : pivOf r q ell hist s < i - start := by omega
    rw [bitAt_rot_sub hk_pos htag1_k hge_start, bitAt_rot_sub hk_pos htag2_k hge_start,
      bitAt_lt hsub_lt_k, bitAt_lt hsub_lt_k]
    by_cases hlt_uq : i - start < 5 * r - 3 - q
    · exact hAgTag (i - start) hsub_gt_piv hlt_uq
    · have hge_uq : 5 * r - 3 - q ≤ i - start := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le htag1 (Nat.pow_le_pow_right (by omega) hge_uq)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le htag2 (Nat.pow_le_pow_right (by omega) hge_uq))]
  have hpiv := row_mix_pivot (r := r) (c := sched) (row := row) (by omega) hrow ht1 ht4
    href1_k href2_k hplace_ge hAgRef
  unfold bitAt at hpiv
  rw [hpi_eq] at hpiv
  have h1 : bitAt k ref1 (start + pivOf r q ell hist s) = tag1.testBit (pivOf r q ell hist s) := by
    rw [Nat.add_comm, bitAt_rot_add hk_pos htag1_k,
      bitAt_lt (lt_trans (pivOf_lt r q ell hist s hq hell5 h5 hs) huq_lt_k)]
  have h2 : bitAt k ref2 (start + pivOf r q ell hist s) = tag2.testBit (pivOf r q ell hist s) := by
    rw [Nat.add_comm, bitAt_rot_add hk_pos htag2_k,
      bitAt_lt (lt_trans (pivOf_lt r q ell hist s hq hell5 h5 hs) huq_lt_k)]
  unfold bitAt at h1 h2
  rw [h1, h2] at hpiv
  exact hpiv

lemma part1_card {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (hist : Fin (2 ^ (ell - 1))) :
    ((Finset.univ : Finset (Fin (2 ^ (5 * r - 3 - q)))).filter
      (fun tag => (histFold k r q sched row.val (rot k (k - (2 * r - 2)) tag.val) ell).2.1 = hist.val)).card =
      2 ^ (5 * r - 3 - q - (ell - 1)) := by
  let start := k - (2 * r - 2)
  let m := 5 * r - 3 - q
  let tries := ell - 1
  let pivFin : Fin tries → Fin m := fun s =>
    ⟨pivOf r q ell hist.val s.val, pivOf_lt r q ell hist.val s.val hq hell5 h5 s.isLt⟩
  have hpivInj : Function.Injective pivFin := by
    intro s1 s2 heq
    by_contra hne
    have hval : pivOf r q ell hist.val s1.val = pivOf r q ell hist.val s2.val :=
      congrArg Fin.val heq
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · exact absurd hval (Nat.ne_of_gt (pivOf_strictAnti r q ell hist.val hq hell5 h5 _ _ hlt s2.isLt))
    · exact absurd hval (Nat.ne_of_lt (pivOf_strictAnti r q ell hist.val hq hell5 h5 _ _ hgt s1.isLt))
  let pivSet : Finset (Fin m) := Finset.univ.image pivFin
  have hpivCard : pivSet.card = tries := by
    rw [Finset.card_image_of_injective _ hpivInj, Finset.card_univ, Fintype.card_fin]
  let freeSet : Finset (Fin m) := Finset.univ \ pivSet
  have hfreeCard : freeSet.card = m - tries := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hpivCard]
  let goodSet : Finset (Fin (2 ^ m)) := Finset.univ.filter
    (fun tag => (histFold k r q sched row.val (rot k start tag.val) ell).2.1 = hist.val)
  let restr : {tag : Fin (2 ^ m) // tag ∈ goodSet} → (freeSet → Bool) :=
    fun tag j => tag.1.val.testBit j.1.val
  have hmem_free : ∀ j : Fin m, j ∉ freeSet ↔ ∃ s : Fin tries, pivOf r q ell hist.val s.val = j.val := by
    intro j
    simp only [freeSet, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not, pivSet,
      Finset.mem_image]
    constructor
    · rintro ⟨s, hs⟩
      exact ⟨s, congrArg Fin.val hs⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, Fin.ext hs⟩
  have hprefix_agree : ∀ tag1 tag2 : Nat, tag1 < 2 ^ m → tag2 < 2 ^ m →
      ∀ s ≤ tries,
        (∀ j, (s < tries → pivOf r q ell hist.val s < j) → j < m → tag1.testBit j = tag2.testBit j) →
        (∀ i < s,
          (mix k 1 (stateStep k r sched false (rot k start tag1) row.val (roundOf i - 1))).testBit
            ((k - q + 3 * (r - roundOf i) +
              min (q - 1) (histFold k r q sched row.val (rot k start tag1) (roundOf i - 1)).2.2 + 1) % k) =
            hist.val.testBit (tries - 1 - i)) →
        (∀ i < s,
          (mix k 1 (stateStep k r sched false (rot k start tag2) row.val (roundOf i - 1))).testBit
            ((k - q + 3 * (r - roundOf i) +
              min (q - 1) (histFold k r q sched row.val (rot k start tag2) (roundOf i - 1)).2.2 + 1) % k) =
            hist.val.testBit (tries - 1 - i)) := by
    intro tag1 tag2 ht1 ht2 s hs hAg hpre1
    have hstep : ∀ n ≤ s,
        ∀ i < n,
          (mix k 1 (stateStep k r sched false (rot k start tag2) row.val (roundOf i - 1))).testBit
            ((k - q + 3 * (r - roundOf i) +
              min (q - 1) (histFold k r q sched row.val (rot k start tag2) (roundOf i - 1)).2.2 + 1) % k) =
            hist.val.testBit (tries - 1 - i) := by
      intro n
      induction n with
      | zero => intro _ i hi; omega
      | succ n ih =>
        intro hn i hi
        by_cases hin : i < n
        · exact ih (by omega) i hin
        · have hieq : i = n := by omega
          subst i
          have hpre2 := ih (by omega)
          have hc1 := histFold_cnt_of_prefix k r q ell sched row.val (rot k start tag1) hist.val
            hell5 n (by omega) (fun j hj => hpre1 j (by omega))
          have hc2 := histFold_cnt_of_prefix k r q ell sched row.val (rot k start tag2) hist.val
            hell5 n (by omega) hpre2
          have hidx_eq : roundOf n - 1 = if n < 3 then n else n + 1 := by
            unfold roundOf; split_ifs <;> omega
          rw [← hidx_eq] at hc1 hc2
          have hAg_n : ∀ j, pivOf r q ell hist.val n < j → j < m → tag1.testBit j = tag2.testBit j := by
            intro j hj1 hj2
            apply hAg j _ hj2
            intro hst
            exact lt_trans (pivOf_strictAnti r q ell hist.val hq hell5 h5 n s (by omega) hst) hj1
          have hsame_piv : tag1.testBit (pivOf r q ell hist.val n) =
              tag2.testBit (pivOf r q ell hist.val n) := by
            apply hAg (pivOf r q ell hist.val n) _ (pivOf_lt r q ell hist.val n hq hell5 h5 (by omega))
            intro hst
            exact pivOf_strictAnti r q ell hist.val hq hell5 h5 n s (by omega) hst
          have hpiv := pivOf_bit_pivot (sched := sched) hq hqr hk7 hell5 hellr h5 row.isLt hist.val (by omega)
            ht1 ht2 hAg_n
          rw [hsame_piv] at hpiv
          have heq_bit :
              (mix k 1 (stateStep k r sched false (rot k start tag2) row.val (roundOf n - 1))).testBit
                ((k - q + 3 * (r - roundOf n) +
                  min (q - 1) (targetCount tries hist.val n) + 1) % k) =
              (mix k 1 (stateStep k r sched false (rot k start tag1) row.val (roundOf n - 1))).testBit
                ((k - q + 3 * (r - roundOf n) +
                  min (q - 1) (targetCount tries hist.val n) + 1) % k) := by
            have hxor_eq : ∀ a b x : Bool, xor a b = xor x x → b = a := by decide
            exact hxor_eq _ _ _ hpiv
          rw [hc2, heq_bit, ← hc1]
          exact hpre1 n (by omega)
    exact hstep s (le_refl _)
  have hbij : Function.Bijective restr := by
    constructor
    · rintro ⟨t1, ht1⟩ ⟨t2, ht2⟩ hreq
      apply Subtype.ext
      apply Fin.ext
      have hg1 : (histFold k r q sched row.val (rot k start t1.val) ell).2.1 = hist.val :=
        (Finset.mem_filter.mp ht1).2
      have hg2 : (histFold k r q sched row.val (rot k start t2.val) ell).2.1 = hist.val :=
        (Finset.mem_filter.mp ht2).2
      have hbits1 := (histFold_eq_iff_bits k r q ell sched row.val (rot k start t1.val) hist.val
        hell5 hist.isLt).mp hg1
      have hbits2 := (histFold_eq_iff_bits k r q ell sched row.val (rot k start t2.val) hist.val
        hell5 hist.isLt).mp hg2
      have hfree_eq : ∀ j : Fin m, j ∈ freeSet → t1.val.testBit j.val = t2.val.testBit j.val := by
        intro j hj
        exact congrFun hreq ⟨j, hj⟩
      have hdown : ∀ s ≤ tries,
          ∀ j, (s < tries → pivOf r q ell hist.val s < j) → j < m →
            t1.val.testBit j = t2.val.testBit j := by
        intro s
        induction s with
        | zero =>
          intro _ j hj1 hj2
          have hjfree : (⟨j, hj2⟩ : Fin m) ∈ freeSet := by
            by_contra hnf
            rcases (hmem_free ⟨j, hj2⟩).mp hnf with ⟨s', hs'⟩
            simp only at hs'
            have h0 : pivOf r q ell hist.val 0 < j := hj1 (by omega)
            by_cases hs'0 : s'.val = 0
            · rw [hs'0] at hs'; omega
            · have hlt := pivOf_strictAnti r q ell hist.val hq hell5 h5 0 s'.val (by omega) s'.isLt
              omega
          exact hfree_eq ⟨j, hj2⟩ hjfree
        | succ s ih =>
          intro hs j hj1 hj2
          have hAg_s : ∀ j', pivOf r q ell hist.val s < j' → j' < m →
              t1.val.testBit j' = t2.val.testBit j' :=
            fun j' h1 h2 => ih (by omega) j' (fun _ => h1) h2
          by_cases hgt : pivOf r q ell hist.val s < j
          · exact hAg_s j hgt hj2
          · by_cases heq_piv : j = pivOf r q ell hist.val s
            · subst heq_piv
              have hc1 := histFold_cnt_of_prefix k r q ell sched row.val (rot k start t1.val)
                hist.val hell5 s (by omega) (fun i hi => hbits1 i (by omega))
              have hc2 := histFold_cnt_of_prefix k r q ell sched row.val (rot k start t2.val)
                hist.val hell5 s (by omega) (fun i hi => hbits2 i (by omega))
              have hidx_eq : roundOf s - 1 = if s < 3 then s else s + 1 := by
                unfold roundOf; split_ifs <;> omega
              rw [← hidx_eq] at hc1 hc2
              have hpiv := pivOf_bit_pivot (sched := sched) hq hqr hk7 hell5 hellr h5 row.isLt hist.val (by omega)
                t1.isLt t2.isLt hAg_s
              have hb1 := hbits1 s (by omega)
              have hb2 := hbits2 s (by omega)
              rw [hc1] at hb1
              rw [hc2] at hb2
              rw [hb1, hb2] at hpiv
              have hxor_eq : ∀ a b x : Bool, xor x x = xor a b → a = b := by decide
              exact hxor_eq _ _ _ hpiv
            · have hjfree : (⟨j, hj2⟩ : Fin m) ∈ freeSet := by
                by_contra hnf
                rcases (hmem_free ⟨j, hj2⟩).mp hnf with ⟨s', hs'⟩
                simp only at hs'
                by_cases hlt1 : s'.val < s
                · have := pivOf_strictAnti r q ell hist.val hq hell5 h5 s'.val s hlt1 (by omega)
                  omega
                · by_cases heq1 : s'.val = s
                  · rw [heq1] at hs'; omega
                  · have hlt_tr : s + 1 < tries := by omega
                    have hj_gt : pivOf r q ell hist.val (s + 1) < j := hj1 hlt_tr
                    by_cases heq2 : s'.val = s + 1
                    · rw [heq2] at hs'; omega
                    · have := pivOf_strictAnti r q ell hist.val hq hell5 h5 (s + 1) s'.val
                        (by omega) s'.isLt
                      omega
              exact hfree_eq ⟨j, hj2⟩ hjfree
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < m
      · exact hdown tries (le_refl _) j (fun h => by omega) hj
      · have hge : m ≤ j := by omega
        rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le t1.isLt (Nat.pow_le_pow_right (by omega) hge)),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le t2.isLt (Nat.pow_le_pow_right (by omega) hge))]
    · intro f
      have hbuild : ∀ s ≤ tries, ∃ tag < 2 ^ m,
          (∀ j : freeSet, tag.testBit j.1.val = f j) ∧
          (∀ i < s,
            (mix k 1 (stateStep k r sched false (rot k start tag) row.val (roundOf i - 1))).testBit
              ((k - q + 3 * (r - roundOf i) +
                min (q - 1) (histFold k r q sched row.val (rot k start tag) (roundOf i - 1)).2.2 + 1) % k) =
              hist.val.testBit (tries - 1 - i)) := by
        intro s
        induction s with
        | zero =>
          intro _
          let tag0 := ofBits m (fun j =>
            if h : j < m then
              if hf : (⟨j, h⟩ : Fin m) ∈ freeSet then f ⟨⟨j, h⟩, hf⟩ else false
            else false)
          refine ⟨tag0, ofBits_lt m _, ?_, fun i hi => by omega⟩
          intro ⟨⟨j, hj⟩, hfj⟩
          simp [tag0, ofBits_testBit, hj, hfj]
        | succ s ih =>
          intro hs
          rcases ih (by omega) with ⟨tag, htag, hfree, hpre⟩
          have hc := histFold_cnt_of_prefix k r q ell sched row.val (rot k start tag) hist.val
            hell5 s (by omega) hpre
          have hidx_eq : roundOf s - 1 = if s < 3 then s else s + 1 := by
            unfold roundOf; split_ifs <;> omega
          rw [← hidx_eq] at hc
          by_cases hmatch :
              (mix k 1 (stateStep k r sched false (rot k start tag) row.val (roundOf s - 1))).testBit
                ((k - q + 3 * (r - roundOf s) +
                  min (q - 1) (histFold k r q sched row.val (rot k start tag) (roundOf s - 1)).2.2 + 1) % k) =
                hist.val.testBit (tries - 1 - s)
          · refine ⟨tag, htag, hfree, ?_⟩
            intro i hi
            by_cases his : i < s
            · exact hpre i his
            · have hieq : i = s := by omega
              subst i
              exact hmatch
          · let p := pivOf r q ell hist.val s
            have hp_lt : p < m := pivOf_lt r q ell hist.val s hq hell5 h5 (by omega)
            let tag' := tag ^^^ (1 <<< p)
            have htag' : tag' < 2 ^ m := flipBit_lt htag hp_lt
            have hAg_above : ∀ j, (s < tries → p < j) → j < m → tag.testBit j = tag'.testBit j := by
              intro j hj1 _
              have hlt_j : p < j := hj1 (by omega)
              rw [testBit_flipBit]
              simp [Nat.ne_of_gt hlt_j]
            have hpre' := hprefix_agree tag tag' htag htag' s (by omega) hAg_above hpre
            have hc' := histFold_cnt_of_prefix k r q ell sched row.val (rot k start tag') hist.val
              hell5 s (by omega) hpre'
            rw [← hidx_eq] at hc'
            refine ⟨tag', htag', ?_, ?_⟩
            · intro ⟨⟨j, hj⟩, hfj⟩
              have hne : j ≠ p := by
                intro heq
                have hnf : (⟨j, hj⟩ : Fin m) ∉ freeSet :=
                  (hmem_free ⟨j, hj⟩).mpr ⟨⟨s, by omega⟩, heq.symm⟩
                exact hnf hfj
              rw [testBit_flipBit]
              simp [hne, hfree ⟨⟨j, hj⟩, hfj⟩]
            · intro i hi
              by_cases his : i < s
              · exact hpre' i his
              · have hieq : i = s := by omega
                subst i
                have hpiv := pivOf_bit_pivot (sched := sched) hq hqr hk7 hell5 hellr h5 row.isLt hist.val (by omega)
                  htag htag' (fun j h1 h2 => hAg_above j (fun _ => h1) h2)
                have hfl : tag'.testBit p = !(tag.testBit p) := by simp [tag']
                rw [hfl] at hpiv
                rw [hc] at hmatch
                rw [hc']
                have hxor_flip : ∀ a b c x : Bool, xor a b = xor x (!x) → a ≠ c → b = c := by decide
                exact hxor_flip _ _ _ _ hpiv hmatch
      rcases hbuild tries (le_refl _) with ⟨tag, htag, hfree, hall⟩
      have hhist_eq : (histFold k r q sched row.val (rot k start tag) ell).2.1 = hist.val :=
        (histFold_eq_iff_bits k r q ell sched row.val (rot k start tag) hist.val hell5 hist.isLt).mpr hall
      refine ⟨⟨⟨tag, htag⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhist_eq⟩⟩, ?_⟩
      funext j
      exact hfree j
  have hcard_eq : Fintype.card {tag : Fin (2 ^ m) // tag ∈ goodSet} =
      Fintype.card (freeSet → Bool) := Fintype.card_of_bijective hbij
  rw [Fintype.card_coe] at hcard_eq
  show goodSet.card = 2 ^ (m - tries)
  rw [hcard_eq, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hfreeCard]

lemma agree_step_false {k r : Nat} {c : Nat → Fin (2 ^ k)}
    {w w' X X' t lo hi loW hiW : Nat}
    (hk : 2 ≤ k) (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hX : X < 2 ^ k) (hX' : X' < 2 ^ k)
    (hAgX : AgreeOn k lo hi X X') (hAgW : AgreeOn k loW hiW w w')
    (ht : 1 ≤ t) (hlo_ge : 2 * (t - 1) ≤ max (lo + 1) (loW + 2 * (t - 1))) :
    AgreeOn k (max (lo + 1) (loW + 2 * (t - 1))) (min (hi - 3) (hiW + 2 * (t - 1)))
      (step k r c false w X t) (step k r c false w' X' t) := by
  intro i hi1 hi2
  unfold step
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) i =
      xor (xor (bitAt k a i) (bitAt k b i)) (bitAt k d i) := by
    intro a b d; simp [bitAt, Nat.testBit_xor]
  rw [hxor3, hxor3]
  have hM : ∀ d ≤ 2, bitAt k (mix k 1 X) (i + d) = bitAt k (mix k 1 X') (i + d) := by
    intro d hd
    rw [bitAt_mix (by omega) hX (by omega) (by omega),
      bitAt_mix (by omega) hX' (by omega) (by omega)]
    rw [hAgX (i + d) (by omega) (by omega),
      hAgX (i + d - 1) (by omega) (by omega),
      hAgX (i + d + 1) (by omega) (by omega)]
  have hM0 := hM 0 (by omega)
  simp only [Nat.add_zero] at hM0
  have hchi : bitAt k (chi k (mix k 1 X)) i = bitAt k (chi k (mix k 1 X')) i := by
    rw [bitAt_chi (by omega), bitAt_chi (by omega),
      hM0, hM 1 (by omega), hM 2 (by omega)]
  have hrot : bitAt k (rot k (2 * (t - 1)) w) i = bitAt k (rot k (2 * (t - 1)) w') i := by
    rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
    exact hAgW (i - 2 * (t - 1)) (by omega) (by omega)
  rw [hchi, hrot]

lemma agree_step_false_guard {k r : Nat} {c : Nat → Fin (2 ^ k)}
    {w w' X X' t lo hi loW hiW : Nat}
    (hk : 2 ≤ k) (hw : w < 2 ^ k) (hw' : w' < 2 ^ k) (hX : X < 2 ^ k) (hX' : X' < 2 ^ k)
    (hAgX : AgreeOn k lo hi X X') (hAgW : AgreeOn k loW hiW w w')
    (ht : 1 ≤ t) (hlo_ge : 2 * (t - 1) ≤ max (lo + 1) (loW + 2 * (t - 1)))
    (hguard_bit : lo + 1 ≤ hi - 3 → bitAt k (mix k 1 X) (hi - 2) = true) :
    AgreeOn k (max (lo + 1) (loW + 2 * (t - 1))) (min (hi - 2) (hiW + 2 * (t - 1)))
      (step k r c false w X t) (step k r c false w' X' t) := by
  intro i hi1 hi2
  by_cases hlt : i < hi - 3
  · exact agree_step_false hk hw hw' hX hX' hAgX hAgW ht hlo_ge i hi1 (by omega)
  · have hieq : i = hi - 3 := by omega
    subst hieq
    have hguard_lo : lo + 1 ≤ hi - 3 := le_trans (le_max_left _ _) hi1
    unfold step
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hxor3 : ∀ a b d, bitAt k (a ^^^ b ^^^ d) (hi - 3) =
        xor (xor (bitAt k a (hi - 3)) (bitAt k b (hi - 3))) (bitAt k d (hi - 3)) := by
      intro a b d; simp [bitAt, Nat.testBit_xor]
    rw [hxor3, hxor3]
    have hM0 : bitAt k (mix k 1 X) (hi - 3) = bitAt k (mix k 1 X') (hi - 3) := by
      rw [bitAt_mix (by omega) hX (by omega) (by omega),
        bitAt_mix (by omega) hX' (by omega) (by omega)]
      rw [hAgX (hi - 3) (by omega) (by omega),
        hAgX (hi - 3 - 1) (by omega) (by omega),
        hAgX (hi - 3 + 1) (by omega) (by omega)]
    have hM1 : bitAt k (mix k 1 X) (hi - 3 + 1) = bitAt k (mix k 1 X') (hi - 3 + 1) := by
      rw [bitAt_mix (by omega) hX (by omega) (by omega),
        bitAt_mix (by omega) hX' (by omega) (by omega)]
      rw [hAgX (hi - 3 + 1) (by omega) (by omega),
        hAgX (hi - 3 + 1 - 1) (by omega) (by omega),
        hAgX (hi - 3 + 1 + 1) (by omega) (by omega)]
    have hgb : bitAt k (mix k 1 X) (hi - 3 + 1) = true := by
      have heq2 : hi - 3 + 1 = hi - 2 := by omega
      rw [heq2]
      exact hguard_bit hguard_lo
    have hchi : bitAt k (chi k (mix k 1 X)) (hi - 3) = bitAt k (chi k (mix k 1 X')) (hi - 3) := by
      rw [bitAt_chi (by omega), bitAt_chi (by omega), ← hM1, hgb, hM0]
      simp
    have hrot : bitAt k (rot k (2 * (t - 1)) w) (hi - 3) =
        bitAt k (rot k (2 * (t - 1)) w') (hi - 3) := by
      rw [bitAt_rot_sub (by omega) hw (by omega), bitAt_rot_sub (by omega) hw' (by omega)]
      exact hAgW (hi - 3 - 2 * (t - 1)) (by omega) (by omega)
    rw [hchi, hrot]

def loU (k r t : Nat) : Nat :=
  if t = 0 then k - 2 * r + 3
  else if t = 1 then k - 2 * r + 4
  else if t = 2 then k - 2 * r + 5
  else k - 2 * (r - t)

lemma histFold_cnt_le (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (row ref t : Nat) :
    (histFold k r q sched row ref t).2.2 ≤ t := by
  have hcw := (histFold_code_weight k r q sched row ref t).2
  have hbl : bitWeight (recCount t) (histFold k r q sched row ref t).2.1 ≤ recCount t := by
    unfold bitWeight
    exact le_trans (List.length_filter_le _ _) (by simp)
  have hrec : recCount t ≤ t := by unfold recCount; split_ifs <;> omega
  omega

lemma loU_step {k r t : Nat} (hr : 5 ≤ r) (hk : 7 * r ≤ k) (ht : t + 1 ≤ r) :
    max (loU k r t + 1) (k - (2 * r - 2) + 2 * t) ≤ loU k r (t + 1) := by
  rw [max_le_iff]
  rcases t with _ | _ | _ | t
  · simp [loU]; omega
  · simp [loU]; omega
  · simp [loU]; omega
  · have h1 : loU k r (t + 3) = k - 2 * (r - (t + 3)) := by
      simp [loU, show t + 3 ≠ 1 by omega, show t + 3 ≠ 2 by omega]
    have h2 : loU k r (t + 4) = k - 2 * (r - (t + 4)) := by
      simp [loU, show t + 4 ≠ 1 by omega, show t + 4 ≠ 2 by omega]
    change loU k r (t + 3) + 1 ≤ loU k r (t + 4) ∧ k - (2 * r - 2) + 2 * (t + 3) ≤ loU k r (t + 4)
    rw [h1, h2]
    omega

lemma loU_ge {k r t : Nat} :
    2 * t ≤ max (loU k r t + 1) (k - (2 * r - 2) + 2 * t) := by
  rw [le_max_iff]
  right
  omega

lemma agree_row_vs_ref {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (w : Nat) (hw : w < 2 ^ k)
    (hproj : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val)) :
    ∀ t ≤ ell,
      AgreeOn k (loU k r t)
        (k - q + 3 * (r - t) + min q (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) t).2.2)
        (stateStep k r sched false w row.val t)
        (stateStep k r sched false (rot k (k - (2 * r - 2)) seedTag.val) row.val t) := by
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have href : ref < 2 ^ k := rot_lt
  intro t ht
  induction t with
  | zero =>
    intro i hi1 hi2
    simp only [loU, histFold_zero, ↓reduceIte, Nat.sub_zero, Nat.min_zero, Nat.add_zero] at hi1 hi2
    rw [stateStep_zero, stateStep_zero]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hxor : ∀ a b, bitAt k (a ^^^ b) i = xor (bitAt k a i) (bitAt k b i) := by
      intro a b; simp [bitAt, Nat.testBit_xor]
    rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega),
      bitAt_rot_sub (by omega) href (by omega)]
    rw [hproj (i - 1) (by omega) (by omega)]
  | succ t ih =>
    have hprev := ih (by omega)
    have hX1 : stateStep k r sched false w row.val t < 2 ^ k := stateStep_lt row.isLt
    have hX2 : stateStep k r sched false ref row.val t < 2 ^ k := stateStep_lt row.isLt
    set c_t := (histFold k r q sched row.val ref t).2.2
    have hc_le : c_t ≤ t := histFold_cnt_le k r q sched row.val ref t
    rw [stateStep_succ, stateStep_succ]
    have hlo_step := loU_step (k := k) (r := r) (t := t) (by omega) (by omega) (by omega)
    have hlo_ge := loU_ge (k := k) (r := r) (t := t)
    by_cases hguard : t + 1 ≠ 4 ∧ c_t < q ∧
        (mix k 1 (stateStep k r sched false ref row.val t)).testBit
          ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = true
    · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t + 1 := by
        rw [histFold_succ]
        unfold histStep
        simp only [hguard.1, ↓reduceIte, histFold_fst]
        rw [hguard.2.2]
        simp only [Bool.toNat_true]
        omega
      have hhi_eq : k - q + 3 * (r - t) + min q c_t - 2 =
          k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1 := by omega
      have hgb_w : loU k r t + 1 ≤ k - q + 3 * (r - t) + min q c_t - 3 →
          bitAt k (mix k 1 (stateStep k r sched false w row.val t))
            (k - q + 3 * (r - t) + min q c_t - 2) = true := by
        intro hguard_lo
        have hMeq : bitAt k (mix k 1 (stateStep k r sched false w row.val t))
            (k - q + 3 * (r - t) + min q c_t - 2) =
            bitAt k (mix k 1 (stateStep k r sched false ref row.val t))
              (k - q + 3 * (r - t) + min q c_t - 2) := by
          rw [bitAt_mix (by omega) hX1 (by omega) (by omega),
            bitAt_mix (by omega) hX2 (by omega) (by omega)]
          rw [hprev _ (by omega) (by omega),
            hprev _ (by omega) (by omega),
            hprev _ (by omega) (by omega)]
        rw [hMeq, hhi_eq]
        exact hguard.2.2
      have hst := agree_step_false_guard (r := r) (c := sched) (t := t + 1) (by omega) hw href hX1 hX2
        hprev hproj (by omega) (by simp) hgb_w
      simp only [Nat.add_sub_cancel] at hst
      rw [hmin_eq]
      exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
    · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t := by
        rw [histFold_succ]
        unfold histStep
        by_cases h4 : t + 1 = 4
        · simp [h4, c_t]
        · simp only [h4, ↓reduceIte, histFold_fst]
          by_cases hcq : c_t < q
          · have hb_false : (mix k 1 (stateStep k r sched false ref row.val t)).testBit
                ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = false := by
              cases hb : (mix k 1 (stateStep k r sched false ref row.val t)).testBit _
              · rfl
              · exact absurd ⟨h4, hcq, hb⟩ hguard
            rw [hb_false]
            simp [c_t]
          · omega
      have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw href hX1 hX2
        hprev hproj (by omega) (by simp)
      simp only [Nat.add_sub_cancel] at hst
      rw [hmin_eq]
      exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)

lemma loU_sub_step {k r a t : Nat} (hr : 5 ≤ r) (hk : 7 * r ≤ k) (ha : a ≤ k - (5 * r - 3))
    (ht : t + 1 ≤ r) :
    max (loU k r t - a + 1) (k - a - (2 * r - 2) + 2 * t) ≤ loU k r (t + 1) - a := by
  rw [max_le_iff]
  rcases t with _ | _ | _ | t
  · simp [loU]; omega
  · simp [loU]; omega
  · simp [loU]; omega
  · have h1 : loU k r (t + 3) = k - 2 * (r - (t + 3)) := by
      simp [loU, show t + 3 ≠ 1 by omega, show t + 3 ≠ 2 by omega]
    have h2 : loU k r (t + 4) = k - 2 * (r - (t + 4)) := by
      simp [loU, show t + 4 ≠ 1 by omega, show t + 4 ≠ 2 by omega]
    change loU k r (t + 3) - a + 1 ≤ loU k r (t + 4) - a ∧
      k - a - (2 * r - 2) + 2 * (t + 3) ≤ loU k r (t + 4) - a
    rw [h1, h2]
    omega

lemma loU_sub_ge {k r a t : Nat} :
    2 * t ≤ max (loU k r t - a + 1) (k - a - (2 * r - 2) + 2 * t) := by
  rw [le_max_iff]
  right
  omega


lemma project_iff_agree {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (seedTag : Fin (2 ^ (5 * r - 3 - q))) (w : Nat) (hw : w < 2 ^ k) :
    rot k (k - (k - (2 * r - 2)) % k) w % 2 ^ (5 * r - 3 - q) = seedTag.val ↔
      AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w (rot k (k - (2 * r - 2)) seedTag.val) := by
  set start := k - (2 * r - 2)
  have hk_pos : 0 < k := by omega
  have huq_lt : 5 * r - 3 - q < k := by omega
  have hseed_k : seedTag.val < 2 ^ k :=
    lt_trans seedTag.isLt (Nat.pow_lt_pow_right (by omega) huq_lt)
  constructor
  · intro heq i hi1 hi2
    have hs_lt : i - start < 5 * r - 3 - q := by omega
    have hbit : (rot k (k - start % k) w % 2 ^ (5 * r - 3 - q)).testBit (i - start) =
        seedTag.val.testBit (i - start) := by rw [heq]
    simp only [Nat.testBit_mod_two_pow, hs_lt, decide_true, Bool.true_and] at hbit
    have h1 : bitAt k (rot k (k - start % k) w) (i - start) = bitAt k w i := by
      have hr := bitAt_rot_rev (k := k) (offset := start) (x := w) (i := i - start) hk_pos hw
      rwa [Nat.sub_add_cancel hi1] at hr
    have h2 : bitAt k (rot k start seedTag.val) i = seedTag.val.testBit (i - start) := by
      rw [bitAt_rot_sub hk_pos hseed_k hi1, bitAt_lt (lt_trans hs_lt huq_lt)]
    rw [h2, ← hbit, ← h1, bitAt_lt (lt_trans hs_lt huq_lt)]
  · intro hAg
    apply Nat.eq_of_testBit_eq
    intro s
    rw [Nat.testBit_mod_two_pow]
    by_cases hs : s < 5 * r - 3 - q
    · simp only [hs, decide_true, Bool.true_and]
      have h1 : bitAt k (rot k (k - start % k) w) s = bitAt k w (s + start) :=
        bitAt_rot_rev (k := k) (offset := start) (x := w) (i := s) hk_pos hw
      have h2 : bitAt k (rot k start seedTag.val) (s + start) = seedTag.val.testBit s := by
        rw [bitAt_rot_add hk_pos hseed_k, bitAt_lt (lt_trans hs huq_lt)]
      rw [← bitAt_lt (lt_trans hs huq_lt), h1, hAg (s + start) (by omega) (by omega), h2]
    · simp only [hs, decide_false, Bool.false_and]
      have hge : 5 * r - 3 - q ≤ s := by omega
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le seedTag.isLt (Nat.pow_le_pow_right (by omega) hge))).symm

lemma project_iff_outside {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (seedTag : Fin (2 ^ (5 * r - 3 - q))) (w : Nat) :
    AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w (rot k (k - (2 * r - 2)) seedTag.val) ↔
      ∀ s < k, (s < 3 * r - 1 - q ∨ k - (2 * r - 2) ≤ s) →
        w.testBit s = (rot k (k - (2 * r - 2)) seedTag.val).testBit s := by
  constructor
  · intro hAg s hsk hso
    rcases hso with hlt | hge
    · have h1 := hAg (k + s) (by omega) (by omega)
      rw [Nat.add_comm, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk] at h1
      exact h1
    · have h1 := hAg s hge (by omega)
      rwa [bitAt_lt hsk, bitAt_lt hsk] at h1
  · intro hout i hi1 hi2
    by_cases hik : i < k
    · rw [bitAt_lt hik, bitAt_lt hik]
      exact hout i hik (Or.inr hi1)
    · have hsub : i - k < 3 * r - 1 - q := by omega
      have hsk : i - k < k := by omega
      have hrew : i = (i - k) + k := by omega
      rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
      exact hout (i - k) hsk (Or.inl hsub)


lemma agree_row_freeze_low {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    {w w' : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hproj1 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hproj2 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w'
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hAgA : AgreeOn k (k - min ((k + 1) / 2) (k - (5 * r - 3)) - (2 * r - 2)) (k - (2 * r - 2)) w w') :
    (stateStep k r sched false w row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) -
          (q - bitWeight (ell - 1)
            (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)) =
      (stateStep k r sched false w' row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) -
          (q - bitWeight (ell - 1)
            (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)) := by
  set a := min ((k + 1) / 2) (k - (5 * r - 3))
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have ha_le : a ≤ k - (5 * r - 3) := Nat.min_le_right _ _
  have hqa : q ≤ a := by simp only [a]; omega
  have hAgW : AgreeOn k (k - a - (2 * r - 2)) (k + 3 * r - 1 - q) w w' := by
    intro i hi1 hi2
    by_cases hmid : i < k - (2 * r - 2)
    · exact hAgA i hi1 hmid
    · rw [hproj1 i (by omega) hi2, hproj2 i (by omega) hi2]
  have href_ag := agree_row_vs_ref hq hqr hk7 hell5 hellr h5 sched row seedTag w hw hproj1
  have hstep_all : ∀ t ≤ r,
      AgreeOn k (loU k r t - a)
        (k - q + 3 * (r - t) + min q (histFold k r q sched row.val ref (min t ell)).2.2)
        (stateStep k r sched false w row.val t)
        (stateStep k r sched false w' row.val t) := by
    intro t ht
    induction t with
    | zero =>
      intro i hi1 hi2
      simp only [loU, Nat.zero_min, histFold_zero, ↓reduceIte, Nat.sub_zero, Nat.min_zero,
        Nat.add_zero] at hi1 hi2
      rw [stateStep_zero, stateStep_zero]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hxor : ∀ x y, bitAt k (x ^^^ y) i = xor (bitAt k x i) (bitAt k y i) := by
        intro x y; simp [bitAt, Nat.testBit_xor]
      rw [hxor, hxor, bitAt_rot_sub (by omega) hw (by omega),
        bitAt_rot_sub (by omega) hw' (by omega)]
      rw [hAgW (i - 1) (by omega) (by omega)]
    | succ t ih =>
      have hprev := ih (by omega)
      have hX1 : stateStep k r sched false w row.val t < 2 ^ k := stateStep_lt row.isLt
      have hX2 : stateStep k r sched false w' row.val t < 2 ^ k := stateStep_lt row.isLt
      rw [stateStep_succ, stateStep_succ]
      have hlo_step := loU_sub_step (k := k) (r := r) (a := a) (t := t) (by omega) (by omega) ha_le (by omega)
      have hlo_ge := loU_sub_ge (k := k) (r := r) (a := a) (t := t)
      by_cases htle : t + 1 ≤ ell
      · have hmin1 : min (t + 1) ell = t + 1 := Nat.min_eq_left htle
        have hmin0 : min t ell = t := Nat.min_eq_left (by omega)
        rw [hmin1]
        rw [hmin0] at hprev
        set c_t := (histFold k r q sched row.val ref t).2.2
        have hc_le : c_t ≤ t := histFold_cnt_le k r q sched row.val ref t
        have href_t : AgreeOn k (loU k r t) (k - q + 3 * (r - t) + min q c_t)
            (stateStep k r sched false w row.val t)
            (stateStep k r sched false ref row.val t) := href_ag t (by omega)
        have hXref : stateStep k r sched false ref row.val t < 2 ^ k := stateStep_lt row.isLt
        by_cases hguard : t + 1 ≠ 4 ∧ c_t < q ∧
            (mix k 1 (stateStep k r sched false ref row.val t)).testBit
              ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = true
        · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t + 1 := by
            rw [histFold_succ]
            unfold histStep
            simp only [hguard.1, ↓reduceIte, histFold_fst]
            rw [hguard.2.2]
            simp only [Bool.toNat_true]
            omega
          have hhi_eq : k - q + 3 * (r - t) + min q c_t - 2 =
              k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1 := by omega
          have hlo_ref : loU k r t ≤ k - q + 3 * (r - t) + min q c_t - 3 := by
            unfold loU
            split_ifs <;> omega
          have hgb_w : loU k r t - a + 1 ≤ k - q + 3 * (r - t) + min q c_t - 3 →
              bitAt k (mix k 1 (stateStep k r sched false w row.val t))
                (k - q + 3 * (r - t) + min q c_t - 2) = true := by
            intro _
            have hMeq : bitAt k (mix k 1 (stateStep k r sched false w row.val t))
                (k - q + 3 * (r - t) + min q c_t - 2) =
                bitAt k (mix k 1 (stateStep k r sched false ref row.val t))
                  (k - q + 3 * (r - t) + min q c_t - 2) := by
              rw [bitAt_mix (by omega) hX1 (by omega) (by omega),
                bitAt_mix (by omega) hXref (by omega) (by omega)]
              rw [href_t _ (by omega) (by omega),
                href_t _ (by omega) (by omega),
                href_t _ (by omega) (by omega)]
            rw [hMeq, hhi_eq]
            exact hguard.2.2
          have hst := agree_step_false_guard (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
            hprev hAgW (by omega) (by simp) hgb_w
          simp only [Nat.add_sub_cancel] at hst
          rw [hmin_eq]
          exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
        · have hmin_eq : min q (histFold k r q sched row.val ref (t + 1)).2.2 = min q c_t := by
            rw [histFold_succ]
            unfold histStep
            by_cases h4 : t + 1 = 4
            · simp [h4, c_t]
            · simp only [h4, ↓reduceIte, histFold_fst]
              by_cases hcq : c_t < q
              · have hb_false : (mix k 1 (stateStep k r sched false ref row.val t)).testBit
                    ((k - q + 3 * (r - (t + 1)) + min (q - 1) c_t + 1) % k) = false := by
                  cases hb : (mix k 1 (stateStep k r sched false ref row.val t)).testBit _
                  · rfl
                  · exact absurd ⟨h4, hcq, hb⟩ hguard
                rw [hb_false]
                simp [c_t]
              · omega
          have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
            hprev hAgW (by omega) (by simp)
          simp only [Nat.add_sub_cancel] at hst
          rw [hmin_eq]
          exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
      · have hmin1 : min (t + 1) ell = ell := Nat.min_eq_right (by omega)
        have hmin0 : min t ell = ell := Nat.min_eq_right (by omega)
        rw [hmin1]
        rw [hmin0] at hprev
        have hc_ell : (histFold k r q sched row.val ref ell).2.2 ≤ ell :=
          histFold_cnt_le k r q sched row.val ref ell
        have hst := agree_step_false (r := r) (c := sched) (t := t + 1) (by omega) hw hw' hX1 hX2
          hprev hAgW (by omega) (by simp)
        simp only [Nat.add_sub_cancel] at hst
        exact agreeOn_mono hst hlo_step (by rw [le_min_iff]; omega)
  have hfin := hstep_all r (le_refl _)
  have hlo_r : loU k r r - a = k - a := by unfold loU; split_ifs <;> omega
  have hmin_r : min r ell = ell := Nat.min_eq_right hellr
  have hrec_ell : recCount ell = ell - 1 := by unfold recCount; split_ifs <;> omega
  set wt := bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1
  set d := q - wt
  have hcnt_eq : (histFold k r q sched row.val ref ell).2.2 = wt := by
    dsimp only [wt]
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row.val ref ell).2
  rw [hlo_r, hmin_r, hcnt_eq, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hfin
  have hhi_eq : k - q + min q wt = k - d := by omega
  rw [hhi_eq] at hfin
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hj : j < a - d
  · simp only [hj, decide_true, Bool.true_and]
    have hlt_d : k - a + j < k - d := by omega
    have hlt_k : k - a + j < k := by omega
    have hbit := hfin (k - a + j) (by omega) hlt_d
    rwa [bitAt_lt hlt_k, bitAt_lt hlt_k] at hbit
  · simp [hj]

lemma slice_eq_iff {w base len x : Nat} (hx : x < 2 ^ len) :
    (w >>> base) % 2 ^ len = x ↔ ∀ j < len, w.testBit (base + j) = x.testBit j := by
  constructor
  · intro heq j hj
    have hb : ((w >>> base) % 2 ^ len).testBit j = x.testBit j := by rw [heq]
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight] at hb
    exact hb
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hj : j < len
    · simp only [hj, decide_true, Bool.true_and]
      exact hall j hj
    · simp only [hj, decide_false, Bool.false_and]
      have hge : len ≤ j := by omega
      exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge))).symm

lemma row_tri {k r q : Nat} (hq : 0 < q) (_hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hr5 : 5 ≤ r) (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k)) :
    let a := min ((k + 1) / 2) (k - (5 * r - 3))
    let baseA := k - a - (2 * r - 2)
    ∀ j < a, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor ((stateStep k r sched false w row.val r >>> (k - a)).testBit j)
          ((stateStep k r sched false w' row.val r >>> (k - a)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
  intro a baseA j hj w w' hw hw' hout
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  have hi_lt : k - a + j < k := by omega
  rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
  have hL : leftRow r = 2 * (r - 1) := by unfold leftRow; omega
  have hAg : AgreeOn k (k - a + j - leftRow r + 1) (k - a + j + 3 * r) w w' := by
    intro i hi1 hi2
    by_cases hik : i < k
    · rw [bitAt_lt hik, bitAt_lt hik]
      exact hout i hik (Or.inr (by omega))
    · have hlt_base : i - k < baseA := by omega
      have hsk : i - k < k := by omega
      have hrew : i = (i - k) + k := by omega
      rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
      exact hout (i - k) hsk (Or.inl hlt_base)
  have hpiv := row_pivot (r := r) (c := sched) (row := row.val) (by omega) row.isLt r (by omega)
    w w' (k - a + j) hw hw' (by omega) hAg
  have hidx : k - a + j - leftRow r = baseA + j := by omega
  rw [hidx] at hpiv
  simpa [bitAt_lt hi_lt, bitAt_lt (show baseA + j < k by omega)] using hpiv

lemma col_tri {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hr5 : 5 ≤ r) (sched : Nat → Fin (2 ^ k)) (col : Fin (2 ^ k)) :
    let g := (k - (k + 1) / 2) - (5 * r - 3)
    let baseQG := 3 * r - 1 - q
    ∀ j < q + g, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseQG ∨ baseQG + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j)
          (((stateStep k r sched true w' col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j) =
        xor (w.testBit (baseQG + j)) (w'.testBit (baseQG + j)) := by
  intro g baseQG j hj w w' hw hw' hout
  simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight]
  have h6rg : 6 * r + g ≤ k := by simp only [g]; omega
  have hi_lt : 6 * r - q + j < k := by omega
  rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
  have hwrap : 6 * r - q + j + 4 * r - 2 ≤ k + baseQG := by
    simp only [baseQG, g] at hj ⊢
    omega
  have hAg : AgreeOn k (6 * r - q + j - (3 * r + 1) + 1) (6 * r - q + j + 4 * r - 2) w w' := by
    intro i hi1 hi2
    by_cases hik : i < k
    · rw [bitAt_lt hik, bitAt_lt hik]
      exact hout i hik (Or.inr (by omega))
    · have hlt_base : i - k < baseQG := by omega
      have hsk : i - k < k := by omega
      have hrew : i = (i - k) + k := by omega
      rw [hrew, bitAt_add_k, bitAt_add_k, bitAt_lt hsk, bitAt_lt hsk]
      exact hout (i - k) hsk (Or.inl hlt_base)
  have hpiv := col_pivot (r := r) (c := sched) (col := col.val) (by omega) col.isLt (t := r) (by omega)
    hw hw' (i := 6 * r - q + j) (by omega) hAg
  have hidx : 6 * r - q + j - (3 * r + 1) = baseQG + j := by omega
  rw [hidx] at hpiv
  simpa [bitAt_lt hi_lt, bitAt_lt (show baseQG + j < k by omega)] using hpiv

lemma fiber_unique_of_xA {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hr5 : 5 ≤ r) (sched : Nat → Fin (2 ^ k)) (col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (colTarget : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3)))))
    (xA : Fin (2 ^ (min ((k + 1) / 2) (k - (5 * r - 3))))) :
    let a := min ((k + 1) / 2) (k - (5 * r - 3))
    let g := (k - (k + 1) / 2) - (5 * r - 3)
    let start := k - (2 * r - 2)
    let baseA := k - a - (2 * r - 2)
    ∃! w : Fin (2 ^ k),
      rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
      (w.val >>> baseA) % 2 ^ a = xA.val ∧
      (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val := by
  intro a g start baseA
  let baseQG := 3 * r - 1 - q
  have hsum_ag : a + g = k - (5 * r - 3) := by simp only [a, g]; omega
  have hmid_eq : baseQG + (q + g) = baseA := by simp only [baseQG, baseA]; omega
  have hA_end : baseA + a = start := by simp only [baseA, start]; omega
  let w0 := ofBits k (fun i =>
    if baseA ≤ i ∧ i < start then xA.val.testBit (i - baseA)
    else (rot k start seedTag.val).testBit i)
  have hw0 : w0 < 2 ^ k := ofBits_lt k _
  have hcond_iff : ∀ w : Fin (2 ^ k),
      (∀ s < k, (s < baseQG ∨ baseQG + (q + g) ≤ s) → w.val.testBit s = w0.testBit s) ↔
      (rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
        (w.val >>> baseA) % 2 ^ a = xA.val) := by
    intro w
    constructor
    · intro hout
      constructor
      · rw [project_iff_agree hq hqr hk7 seedTag w.val w.isLt,
          project_iff_outside hq hqr hk7 seedTag w.val]
        intro s hsk hso
        have h1 := hout s hsk (by rcases hso with h1 | h2 <;> [exact Or.inl h1; exact Or.inr (by omega)])
        have hnotA : ¬ (baseA ≤ s ∧ s < start) := by rcases hso with h1 | h2 <;> omega
        simpa [w0, ofBits_testBit, hsk, hnotA] using h1
      · rw [slice_eq_iff xA.isLt]
        intro j hj
        have hs : baseA + j < k := by omega
        have h1 := hout (baseA + j) hs (Or.inr (by omega))
        have hin : baseA ≤ baseA + j ∧ baseA + j < start := ⟨by omega, by omega⟩
        simpa [w0, ofBits_testBit, hs, hin] using h1
    · rintro ⟨hproj, hxA⟩ s hsk hso
      by_cases hin : baseA ≤ s ∧ s < start
      · simp only [w0, ofBits_testBit, hsk, hin, ↓reduceIte]
        have h1 := (slice_eq_iff xA.isLt).mp hxA (s - baseA) (by omega)
        rwa [Nat.add_sub_cancel' hin.1] at h1
      · simp only [w0, ofBits_testBit, hsk, hin, ↓reduceIte]
        have hproj_out := (project_iff_outside hq hqr hk7 seedTag w.val).mp
          ((project_iff_agree hq hqr hk7 seedTag w.val w.isLt).mp hproj)
        exact hproj_out s hsk (by rcases hso with h1 | h2 <;> omega)
  have hsolve := triangular_solve (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    (col_tri hq hqr hk7 hr5 sched col) w0 hw0 colTarget.val colTarget.isLt
  rcases hsolve with ⟨w, ⟨hw_out, hw_col⟩, huniq⟩
  have ⟨hw_proj, hw_xA⟩ := (hcond_iff w).mp hw_out
  refine ⟨w, ⟨hw_proj, hw_xA, hw_col⟩, ?_⟩
  rintro w' ⟨hw'_proj, hw'_xA, hw'_col⟩
  exact huniq w' ⟨(hcond_iff w').mpr ⟨hw'_proj, hw'_xA⟩, hw'_col⟩

lemma keepFiber_card {k r q : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hr5 : 5 ≤ r) (sched : Nat → Fin (2 ^ k)) (col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (colTarget : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3))))) :
    let a := min ((k + 1) / 2) (k - (5 * r - 3))
    let g := (k - (k + 1) / 2) - (5 * r - 3)
    let start := k - (2 * r - 2)
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
      rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
      (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val)).card =
      2 ^ a := by
  intro a g start
  let baseA := k - a - (2 * r - 2)
  have hcard :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
        (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val)).card =
      (Finset.univ : Finset (Fin (2 ^ a))).card := by
    refine Finset.card_bij
      (fun w _ => (⟨(w.val >>> baseA) % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩ : Fin (2 ^ a)))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      let xA : Fin (2 ^ a) := ⟨(w1.val >>> baseA) % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩
      rcases fiber_unique_of_xA hq hqr hk7 hr5 sched col seedTag colTarget xA with ⟨wU, _, hU⟩
      have h1 : w1 = wU := hU w1 ⟨hw1.1, rfl, hw1.2⟩
      have h2 : w2 = wU := hU w2 ⟨hw2.1, (congrArg Fin.val heq).symm, hw2.2⟩
      rw [h1, h2]
    · intro xA _
      rcases fiber_unique_of_xA hq hqr hk7 hr5 sched col seedTag colTarget xA with ⟨w, ⟨hp, hx, hc⟩, _⟩
      refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, hc⟩, Fin.ext hx⟩
  rw [hcard, Finset.card_univ, Fintype.card_fin]

lemma lowRow_fiber_card {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (colTarget : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3))))) :
    let a := min ((k + 1) / 2) (k - (5 * r - 3))
    let g := (k - (k + 1) / 2) - (5 * r - 3)
    let start := k - (2 * r - 2)
    let d := q - bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k start seedTag.val) ell).2.1
    ∀ yLo : Fin (2 ^ (a - d)),
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
        (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val ∧
        (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val)).card =
        2 ^ d := by
  intro a g start d yLo
  have hr5 : 5 ≤ r := by omega
  have hqa : q ≤ a := by simp only [a]; omega
  have hda : d ≤ a := by simp only [d]; omega
  let baseA := k - a - (2 * r - 2)
  have hA_end : baseA + a = start := by simp only [baseA, start]; omega
  have hhi_end : baseA + (a - d) + d = start := by omega
  have hrow_low_tri : ∀ j < a - d, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - d)).testBit j)
          (((stateStep k r sched false w' row.val r >>> (k - a)) % 2 ^ (a - d)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
    intro j hj w w' hw hw' hout
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]
    exact row_tri hq hqr hk7 hr5 sched row j (by omega) w w' hw hw' hout
  have hcard :
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
        (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val ∧
        (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val)).card =
      (Finset.univ : Finset (Fin (2 ^ d))).card := by
    refine Finset.card_bij
      (fun w _ => (⟨(w.val >>> (baseA + (a - d))) % 2 ^ d, Nat.mod_lt _ (Nat.two_pow_pos d)⟩ : Fin (2 ^ d)))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro w1 hw1 w2 hw2 heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
      have hhi_bits : ∀ j < d, w1.val.testBit (baseA + (a - d) + j) = w2.val.testBit (baseA + (a - d) + j) := by
        intro j hj
        have h1 := congrArg (fun z : Fin (2 ^ d) => z.val.testBit j) heq
        simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight] at h1
        exact h1
      let w1Ref := ofBits k (fun i =>
        if baseA ≤ i ∧ i < start then w1.val.testBit i else (rot k start seedTag.val).testBit i)
      let w2Ref := ofBits k (fun i =>
        if baseA ≤ i ∧ i < start then w2.val.testBit i else (rot k start seedTag.val).testBit i)
      have hw1Ref_lt : w1Ref < 2 ^ k := ofBits_lt k _
      have hw2Ref_lt : w2Ref < 2 ^ k := ofBits_lt k _
      have hw1Ref_proj : AgreeOn k start (k + 3 * r - 1 - q) w1Ref (rot k start seedTag.val) := by
        rw [project_iff_outside hq hqr hk7 seedTag w1Ref]
        intro s hsk hso
        have hnotA : ¬ (baseA ≤ s ∧ s < start) := by rcases hso with h1 | h2 <;> omega
        simp only [w1Ref, ofBits_testBit, hsk, hnotA, ↓reduceIte]
        rfl
      have hw2Ref_proj : AgreeOn k start (k + 3 * r - 1 - q) w2Ref (rot k start seedTag.val) := by
        rw [project_iff_outside hq hqr hk7 seedTag w2Ref]
        intro s hsk hso
        have hnotA : ¬ (baseA ≤ s ∧ s < start) := by rcases hso with h1 | h2 <;> omega
        simp only [w2Ref, ofBits_testBit, hsk, hnotA, ↓reduceIte]
        rfl
      have hw1_proj_ag := (project_iff_agree hq hqr hk7 seedTag w1.val w1.isLt).mp hw1.1
      have hw2_proj_ag := (project_iff_agree hq hqr hk7 seedTag w2.val w2.isLt).mp hw2.1
      have hw1_agA : AgreeOn k baseA start w1Ref w1.val := by
        intro i hi1 hi2
        have hik : i < k := by omega
        simp [bitAt_lt hik, w1Ref, ofBits_testBit, hik, hi1, hi2]
      have hw2_agA : AgreeOn k baseA start w2Ref w2.val := by
        intro i hi1 hi2
        have hik : i < k := by omega
        simp [bitAt_lt hik, w2Ref, ofBits_testBit, hik, hi1, hi2]
      have hw1Ref_row : (stateStep k r sched false w1Ref row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val := by
        rw [agree_row_freeze_low hq hqr hk7 hell5 hellr h5 sched row seedTag hw1Ref_lt w1.isLt
          hw1Ref_proj hw1_proj_ag hw1_agA, hw1.2.2]
      have hw2Ref_row : (stateStep k r sched false w2Ref row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val := by
        rw [agree_row_freeze_low hq hqr hk7 hell5 hellr h5 sched row seedTag hw2Ref_lt w2.isLt
          hw2Ref_proj hw2_proj_ag hw2_agA, hw2.2.2]
      have hout_eq : ∀ s < k, (s < baseA ∨ baseA + (a - d) ≤ s) → w1Ref.testBit s = w2Ref.testBit s := by
        intro s hsk hso
        by_cases hin : baseA ≤ s ∧ s < start
        · simp only [w1Ref, w2Ref, ofBits_testBit, hsk, hin, ↓reduceIte]
          have hge : baseA + (a - d) ≤ s := by omega
          have hj := hhi_bits (s - (baseA + (a - d))) (by omega)
          rwa [Nat.add_sub_cancel' hge] at hj
        · simp only [w1Ref, w2Ref, ofBits_testBit, hsk, hin, ↓reduceIte]
      rcases triangular_solve (k := k) (base := baseA) (m := a - d) (by omega)
        (fun w => (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - d))
        (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
        hrow_low_tri w2Ref hw2Ref_lt yLo.val yLo.isLt with ⟨wU, _, hU⟩
      have h1U : (⟨w1Ref, hw1Ref_lt⟩ : Fin (2 ^ k)) = wU := hU ⟨w1Ref, hw1Ref_lt⟩ ⟨hout_eq, hw1Ref_row⟩
      have h2U : (⟨w2Ref, hw2Ref_lt⟩ : Fin (2 ^ k)) = wU := hU ⟨w2Ref, hw2Ref_lt⟩ ⟨fun _ _ _ => rfl, hw2Ref_row⟩
      have hRef_eq : w1Ref = w2Ref := congrArg Fin.val (h1U.trans h2U.symm)
      have hxA_eq : (w1.val >>> baseA) % 2 ^ a = (w2.val >>> baseA) % 2 ^ a := by
        rw [slice_eq_iff (Nat.mod_lt _ (Nat.two_pow_pos a))]
        intro j hj
        have hbj : baseA + j < k := by omega
        have hin : baseA ≤ baseA + j ∧ baseA + j < start := ⟨by omega, by omega⟩
        have hb : w1Ref.testBit (baseA + j) = w2Ref.testBit (baseA + j) := by rw [hRef_eq]
        simp only [w1Ref, w2Ref, ofBits_testBit, hbj, hin, and_self, ↓reduceIte] at hb
        simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight, hb]
      let xA : Fin (2 ^ a) := ⟨(w1.val >>> baseA) % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩
      rcases fiber_unique_of_xA hq hqr hk7 hr5 sched col seedTag colTarget xA with ⟨wF, _, hF⟩
      have h1F : w1 = wF := hF w1 ⟨hw1.1, rfl, hw1.2.1⟩
      have h2F : w2 = wF := hF w2 ⟨hw2.1, hxA_eq.symm, hw2.2.1⟩
      rw [h1F, h2F]
    · intro zHi _
      let wBase := ofBits k (fun i =>
        if baseA + (a - d) ≤ i ∧ i < start then zHi.val.testBit (i - (baseA + (a - d)))
        else (rot k start seedTag.val).testBit i)
      have hwBase_lt : wBase < 2 ^ k := ofBits_lt k _
      rcases triangular_solve (k := k) (base := baseA) (m := a - d) (by omega)
        (fun w => (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - d))
        (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
        hrow_low_tri wBase hwBase_lt yLo.val yLo.isLt with ⟨wStar, ⟨hwStar_out, hwStar_row⟩, _⟩
      let xAStar : Fin (2 ^ a) := ⟨(wStar.val >>> baseA) % 2 ^ a, Nat.mod_lt _ (Nat.two_pow_pos a)⟩
      rcases fiber_unique_of_xA hq hqr hk7 hr5 sched col seedTag colTarget xAStar with
        ⟨w, ⟨hw_proj, hw_xA, hw_col⟩, _⟩
      have hwStar_proj : AgreeOn k start (k + 3 * r - 1 - q) wStar.val (rot k start seedTag.val) := by
        rw [project_iff_outside hq hqr hk7 seedTag wStar.val]
        intro s hsk hso
        have h1 := hwStar_out s hsk (by rcases hso with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
        have hnotHi : ¬ (baseA + (a - d) ≤ s ∧ s < start) := by rcases hso with h1 | h2 <;> omega
        simpa [wBase, ofBits_testBit, hsk, hnotHi] using h1
      have hw_proj_ag := (project_iff_agree hq hqr hk7 seedTag w.val w.isLt).mp hw_proj
      have hw_agA : AgreeOn k baseA start w.val wStar.val := by
        intro i hi1 hi2
        have hik : i < k := by omega
        rw [bitAt_lt hik, bitAt_lt hik]
        have h1 := (slice_eq_iff xAStar.isLt).mp hw_xA (i - baseA) (by omega)
        simp only [xAStar, Nat.testBit_mod_two_pow, show i - baseA < a by omega, decide_true,
          Bool.true_and, Nat.testBit_shiftRight] at h1
        rwa [Nat.add_sub_cancel' hi1] at h1
      have hw_row : (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val := by
        rw [agree_row_freeze_low hq hqr hk7 hell5 hellr h5 sched row seedTag w.isLt wStar.isLt
          hw_proj_ag hwStar_proj hw_agA, hwStar_row]
      have hw_zHi : (w.val >>> (baseA + (a - d))) % 2 ^ d = zHi.val := by
        rw [slice_eq_iff zHi.isLt]
        intro j hj
        have hs : baseA + (a - d) + j < k := by omega
        have h1 := hw_agA (baseA + (a - d) + j) (by omega) (by omega)
        rw [bitAt_lt hs, bitAt_lt hs] at h1
        have h2 := hwStar_out (baseA + (a - d) + j) hs (Or.inr (by omega))
        have hin : baseA + (a - d) ≤ baseA + (a - d) + j ∧ baseA + (a - d) + j < start :=
          ⟨by omega, by omega⟩
        rw [h1, h2]
        simp [wBase, ofBits_testBit, hs, hin]
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw_proj, hw_col, hw_row⟩, Fin.ext hw_zHi⟩
  rw [hcard, Finset.card_univ, Fintype.card_fin]

lemma finset_sum_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → Nat)
    (h : ∀ x ∈ s, f x ≤ g x) : ∑ x ∈ s, f x ≤ ∑ x ∈ s, g x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Nat.add_le_add (h a (Finset.mem_insert_self a s))
      (ih fun x hx => h x (Finset.mem_insert_of_mem hx))

lemma cell_card_le {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (colTarget : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3)))))
    (s : Nat) (hs : s ≤ min ((k + 1) / 2) (k - (5 * r - 3))) :
    let a := min ((k + 1) / 2) (k - (5 * r - 3))
    let g := (k - (k + 1) / 2) - (5 * r - 3)
    let start := k - (2 * r - 2)
    let d := q - bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k start seedTag.val) ell).2.1
    ∀ y : Fin (2 ^ (a - s)),
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
        (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val ∧
        (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s) = y.val)).card ≤
        2 ^ (max s d) := by
  intro a g start d y
  have hqa : q ≤ a := by simp only [a]; omega
  have hda : d ≤ a := by simp only [d]; omega
  set cell := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
    (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val ∧
    (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s) = y.val)
  by_cases hsd : s ≤ d
  · have hmax : max s d = d := Nat.max_eq_right hsd
    rw [hmax]
    let yLo : Fin (2 ^ (a - d)) := ⟨y.val % 2 ^ (a - d), Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    have hsub : cell ⊆ (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
        (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val ∧
        (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val) := by
      intro w hw
      simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      refine ⟨hw.1, hw.2.1, ?_⟩
      have hdvd : 2 ^ (a - d) ∣ 2 ^ (a - s) := Nat.pow_dvd_pow 2 (by omega)
      rw [← Nat.mod_mod_of_dvd _ hdvd, hw.2.2]
    exact le_trans (Finset.card_le_card hsub)
      (le_of_eq (lowRow_fiber_card hq hqr hk7 hell5 hellr h5 sched row col seedTag colTarget yLo))
  · have hds : d ≤ s := by omega
    have hmax : max s d = s := Nat.max_eq_left hds
    rw [hmax]
    let T : Finset (Fin (2 ^ (a - d))) :=
      Finset.univ.filter (fun yLo => yLo.val % 2 ^ (a - s) = y.val)
    have hpow_ad : 2 ^ (a - s) * 2 ^ (s - d) = 2 ^ (a - d) := by
      rw [← Nat.pow_add, show (a - s) + (s - d) = a - d by omega]
    have hT_card : T.card = 2 ^ (s - d) := by
      have hbij : (Finset.univ : Finset (Fin (2 ^ (s - d)))).card = T.card := by
        refine Finset.card_bij
          (fun t _ => (⟨y.val + 2 ^ (a - s) * t.val, by
            have h1 := y.isLt
            have h2 := t.isLt
            have h3 : 2 ^ (a - s) * (t.val + 1) ≤ 2 ^ (a - s) * 2 ^ (s - d) :=
              Nat.mul_le_mul_left _ h2
            rw [Nat.mul_add, Nat.mul_one, hpow_ad] at h3
            omega⟩ : Fin (2 ^ (a - d))))
          ?_ ?_ ?_
        · intro t _
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
        · intro t1 _ t2 _ heq
          have hv : y.val + 2 ^ (a - s) * t1.val = y.val + 2 ^ (a - s) * t2.val :=
            congrArg Fin.val heq
          exact Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (a - s)) (Nat.add_left_cancel hv))
        · intro yLo hyLo
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hyLo
          let tv := yLo.val / 2 ^ (a - s)
          have htv : tv < 2 ^ (s - d) := Nat.div_lt_of_lt_mul (by rw [hpow_ad]; exact yLo.isLt)
          refine ⟨⟨tv, htv⟩, Finset.mem_univ _, Fin.ext ?_⟩
          dsimp only [tv]
          rw [← hyLo, Nat.mod_add_div]
      rw [← hbij, Finset.card_univ, Fintype.card_fin]
    have hmaps : Set.MapsTo
        (fun w : Fin (2 ^ k) => (⟨(stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d),
          Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (a - d))))
        (cell : Set (Fin (2 ^ k))) (T : Set (Fin (2 ^ (a - d)))) := by
      intro w hw
      simp only [Finset.mem_coe, cell, T, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      have hdvd : 2 ^ (a - s) ∣ 2 ^ (a - d) := Nat.pow_dvd_pow 2 (by omega)
      rw [Nat.mod_mod_of_dvd _ hdvd, hw.2.2]
    have hle : ∑ yLo ∈ T,
        (cell.filter (fun w =>
          (⟨(stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d),
            Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (a - d))) = yLo)).card ≤
        ∑ _yLo ∈ T, 2 ^ d := by
      apply finset_sum_le_sum
      intro yLo _
      have hsub : cell.filter (fun w =>
          (⟨(stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d),
            Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (a - d))) = yLo) ⊆
          (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
            rot k (k - start % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
            (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = colTarget.val ∧
            (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - d) = yLo.val) := by
        intro w hw
        simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        exact ⟨hw.1.1, hw.1.2.1, congrArg Fin.val hw.2⟩
      exact le_trans (Finset.card_le_card hsub)
        (le_of_eq (lowRow_fiber_card hq hqr hk7 hell5 hellr h5 sched row col seedTag colTarget yLo))
    calc cell.card
        = ∑ yLo ∈ T, (cell.filter _).card := Finset.card_eq_sum_card_fiberwise hmaps
      _ ≤ ∑ _yLo ∈ T, 2 ^ d := hle
      _ = T.card * 2 ^ d := by rw [Finset.sum_const, smul_eq_mul]
      _ = 2 ^ (s - d) * 2 ^ d := by rw [hT_card]
      _ = 2 ^ s := by rw [← Nat.pow_add, Nat.sub_add_cancel hds]

lemma card_bitWeight (m : Nat) :
    ∀ j, ((Finset.range (2 ^ m)).filter (fun c => bitWeight m c = j)).card = Nat.choose m j := by
  induction m with
  | zero =>
    intro j
    cases j with
    | zero => simp [bitWeight]
    | succ j => simp [bitWeight]
  | succ m ih =>
    intro j
    set S := (Finset.range (2 ^ (m + 1))).filter (fun c => bitWeight (m + 1) c = j)
    have hsplit := (Finset.card_filter_add_card_filter_not (s := S) (p := fun c => c % 2 = 0)).symm
    have heven : (S.filter (fun c => c % 2 = 0)).card =
        ((Finset.range (2 ^ m)).filter (fun c => bitWeight m c = j)).card := by
      refine Finset.card_bij (fun c _ => c / 2) ?_ ?_ ?_
      · intro c hc
        simp only [S, Finset.mem_filter, Finset.mem_range] at hc ⊢
        have hc_eq : c = 2 * (c / 2) + Bool.false.toNat := by simp; omega
        have hlt : c / 2 < 2 ^ m := by rw [Nat.pow_succ] at hc; omega
        have hw : bitWeight (m + 1) c = bitWeight m (c / 2) := by
          conv_lhs => rw [hc_eq]
          rw [bitWeight_step]
          simp
        exact ⟨hlt, by omega⟩
      · intro c1 hc1 c2 hc2 heq
        simp only [Finset.mem_filter] at hc1 hc2
        omega
      · intro c' hc'
        simp only [S, Finset.mem_filter, Finset.mem_range] at hc' ⊢
        refine ⟨2 * c', ⟨⟨by rw [Nat.pow_succ]; omega, ?_⟩, by omega⟩, by omega⟩
        have hstep := bitWeight_step m c' false
        simpa [hc'.2] using hstep
    cases j with
    | zero =>
      have hodd : (S.filter (fun c => ¬ c % 2 = 0)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro c hc hne
        simp only [S, Finset.mem_filter, Finset.mem_range] at hc
        have hc_eq : c = 2 * (c / 2) + Bool.true.toNat := by simp; omega
        have hw : bitWeight (m + 1) c = bitWeight m (c / 2) + 1 := by
          conv_lhs => rw [hc_eq]
          rw [bitWeight_step]
          simp
        omega
      rw [hsplit, heven, hodd, ih 0, Nat.add_zero]
      simp
    | succ j' =>
      have hodd : (S.filter (fun c => ¬ c % 2 = 0)).card =
          ((Finset.range (2 ^ m)).filter (fun c => bitWeight m c = j')).card := by
        refine Finset.card_bij (fun c _ => c / 2) ?_ ?_ ?_
        · intro c hc
          simp only [S, Finset.mem_filter, Finset.mem_range] at hc ⊢
          have hc_eq : c = 2 * (c / 2) + Bool.true.toNat := by simp; omega
          have hlt : c / 2 < 2 ^ m := by rw [Nat.pow_succ] at hc; omega
          have hw : bitWeight (m + 1) c = bitWeight m (c / 2) + 1 := by
            conv_lhs => rw [hc_eq]
            rw [bitWeight_step]
            simp
          exact ⟨hlt, by omega⟩
        · intro c1 hc1 c2 hc2 heq
          simp only [Finset.mem_filter] at hc1 hc2
          omega
        · intro c' hc'
          simp only [S, Finset.mem_filter, Finset.mem_range] at hc' ⊢
          refine ⟨2 * c' + 1, ⟨⟨by rw [Nat.pow_succ]; omega, ?_⟩, by omega⟩, by omega⟩
          have hstep := bitWeight_step m c' true
          simpa [hc'.2] using hstep
      rw [hsplit, heven, hodd, ih (j' + 1), ih j', Nat.choose_succ_succ, Nat.add_comm]

def paritySign (n x mask : Nat) : ℤ :=
  if ((List.range n).filter (fun i => x.testBit i && mask.testBit i)).length % 2 = 0
  then 1 else -1

lemma paritySign_zero (n x : Nat) : paritySign n x 0 = 1 := by
  unfold paritySign
  have hnil : (List.range n).filter (fun i => x.testBit i && (0 : Nat).testBit i) = [] := by
    rw [List.filter_eq_nil_iff]
    intro i _
    simp
  rw [hnil]
  rfl

lemma paritySign_mod_left (n x mask : Nat) :
    paritySign n (x % 2 ^ n) mask = paritySign n x mask := by
  unfold paritySign
  have heq : (List.range n).filter (fun i => (x % 2 ^ n).testBit i && mask.testBit i) =
      (List.range n).filter (fun i => x.testBit i && mask.testBit i) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  rw [heq]

lemma paritySign_mod_right (n x mask : Nat) :
    paritySign n x (mask % 2 ^ n) = paritySign n x mask := by
  unfold paritySign
  have heq : (List.range n).filter (fun i => x.testBit i && (mask % 2 ^ n).testBit i) =
      (List.range n).filter (fun i => x.testBit i && mask.testBit i) := by
    apply List.filter_congr
    intro i hi
    rw [List.mem_range] at hi
    rw [Nat.testBit_mod_two_pow]
    simp [hi]
  rw [heq]

lemma paritySign_succ (n x mask : Nat) :
    paritySign (n + 1) x mask =
      (if x.testBit n && mask.testBit n then (-1 : ℤ) else 1) * paritySign n x mask := by
  unfold paritySign
  rw [List.range_succ, List.filter_append, List.length_append]
  simp only [List.filter_cons, List.filter_nil]
  cases h : (x.testBit n && mask.testBit n)
  · simp
  · simp only [↓reduceIte, List.length_cons, List.length_nil, zero_add]
    split_ifs <;> omega

lemma testBit_pow_add_lt {n m i : Nat} (hi : i < n) :
    (2 ^ n + m).testBit i = m.testBit i := by
  have hd : n = i + ((n - i - 1) + 1) := by omega
  have hpow : 2 ^ n = 2 ^ i * (2 * 2 ^ (n - i - 1)) := by
    conv_lhs => rw [hd, Nat.pow_add, Nat.pow_succ, Nat.mul_comm (2 ^ (n - i - 1)) 2]
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, hpow,
    Nat.mul_add_div (Nat.two_pow_pos i), Nat.mul_add_mod]

lemma testBit_pow_add_self {n m : Nat} (hm : m < 2 ^ n) :
    (2 ^ n + m).testBit n = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hdiv : (2 ^ n + m) / 2 ^ n = 1 := by
    rw [Nat.add_div_left _ (Nat.two_pow_pos n), Nat.div_eq_of_lt hm]
  rw [hdiv]
  rfl

lemma paritySign_ortho (n : Nat) :
    ∀ x y, x < 2 ^ n → y < 2 ^ n →
      ∑ mask ∈ Finset.range (2 ^ n), paritySign n x mask * paritySign n y mask =
        if x = y then (2 : ℤ) ^ n else 0 := by
  induction n with
  | zero =>
    intro x y hx hy
    have hx0 : x = 0 := by omega
    have hy0 : y = 0 := by omega
    subst hx0; subst hy0
    simp [paritySign]
  | succ n ih =>
    intro x y hx hy
    have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ, Nat.mul_two]
    rw [h2, Finset.sum_range_add, ← Finset.sum_add_distrib]
    have hterm : ∀ m ∈ Finset.range (2 ^ n),
        paritySign (n + 1) x m * paritySign (n + 1) y m +
          paritySign (n + 1) x (2 ^ n + m) * paritySign (n + 1) y (2 ^ n + m) =
        (if x.testBit n = y.testBit n then (2 : ℤ) else 0) *
          (paritySign n (x % 2 ^ n) m * paritySign n (y % 2 ^ n) m) := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hmn : m.testBit n = false := Nat.testBit_lt_two_pow hm
      have hm2n : (2 ^ n + m).testBit n = true := testBit_pow_add_self hm
      have hm_mod : (2 ^ n + m) % 2 ^ n = m := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt hm]
      have hs1x : paritySign (n + 1) x m = paritySign n (x % 2 ^ n) m := by
        simp only [paritySign_succ, hmn, Bool.and_false, Bool.false_eq_true, ↓reduceIte, one_mul,
          paritySign_mod_left]
      have hs1y : paritySign (n + 1) y m = paritySign n (y % 2 ^ n) m := by
        simp only [paritySign_succ, hmn, Bool.and_false, Bool.false_eq_true, ↓reduceIte, one_mul,
          paritySign_mod_left]
      have hs2x : paritySign (n + 1) x (2 ^ n + m) =
          (if x.testBit n then (-1 : ℤ) else 1) * paritySign n (x % 2 ^ n) m := by
        rw [paritySign_succ, hm2n, Bool.and_true, ← paritySign_mod_right, hm_mod, paritySign_mod_left]
      have hs2y : paritySign (n + 1) y (2 ^ n + m) =
          (if y.testBit n then (-1 : ℤ) else 1) * paritySign n (y % 2 ^ n) m := by
        rw [paritySign_succ, hm2n, Bool.and_true, ← paritySign_mod_right, hm_mod, paritySign_mod_left]
      rw [hs1x, hs1y, hs2x, hs2y]
      cases x.testBit n <;> cases y.testBit n <;> simp <;> linarith
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
      ih (x % 2 ^ n) (y % 2 ^ n) (Nat.mod_lt _ (Nat.two_pow_pos n)) (Nat.mod_lt _ (Nat.two_pow_pos n))]
    by_cases hbit : x.testBit n = y.testBit n
    · simp only [hbit, ↓reduceIte]
      have heq_iff : x % 2 ^ n = y % 2 ^ n ↔ x = y := by
        constructor
        · intro hmod
          apply Nat.eq_of_testBit_eq
          intro j
          by_cases hjn : j < n
          · have h1 := congrArg (fun t => t.testBit j) hmod
            simpa [Nat.testBit_mod_two_pow, hjn] using h1
          · by_cases hjeq : j = n
            · rw [hjeq, hbit]
            · have hge : n + 1 ≤ j := by omega
              rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge)),
                Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) hge))]
        · intro hxy; rw [hxy]
      by_cases hxy : x = y
      · simp only [hxy, ↓reduceIte]
        rw [pow_succ, mul_comm]
      · have hm : x % 2 ^ n ≠ y % 2 ^ n := fun h => hxy (heq_iff.mp h)
        simp [hxy, hm]
    · have hne : x ≠ y := fun h => hbit (by rw [h])
      simp [hbit, hne]

lemma walsh_parseval (n : Nat) (f : Nat → ℤ) :
    ∑ mask ∈ Finset.range (2 ^ n),
      (∑ x ∈ Finset.range (2 ^ n), f x * paritySign n x mask) ^ 2 =
    (2 : ℤ) ^ n * ∑ x ∈ Finset.range (2 ^ n), (f x) ^ 2 := by
  have hexp : ∀ mask ∈ Finset.range (2 ^ n),
      (∑ x ∈ Finset.range (2 ^ n), f x * paritySign n x mask) ^ 2 =
      ∑ x ∈ Finset.range (2 ^ n), ∑ y ∈ Finset.range (2 ^ n),
        (f x * f y) * (paritySign n x mask * paritySign n y mask) := by
    intro mask _
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have h1 : f x * paritySign n x mask * (f y * paritySign n y mask) =
        f x * f y * (paritySign n x mask * paritySign n y mask) := by
      rw [mul_assoc, ← mul_assoc (paritySign n x mask), mul_comm (paritySign n x mask) (f y),
        mul_assoc, mul_assoc]
    exact h1
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hinner : ∀ x ∈ Finset.range (2 ^ n),
      ∑ mask ∈ Finset.range (2 ^ n), ∑ y ∈ Finset.range (2 ^ n),
        (f x * f y) * (paritySign n x mask * paritySign n y mask) =
      (2 : ℤ) ^ n * (f x) ^ 2 := by
    intro x hx
    rw [Finset.sum_comm]
    have hy : ∀ y ∈ Finset.range (2 ^ n),
        ∑ mask ∈ Finset.range (2 ^ n),
          (f x * f y) * (paritySign n x mask * paritySign n y mask) =
        if x = y then (2 : ℤ) ^ n * (f x) ^ 2 else 0 := by
      intro y hy
      rw [← Finset.mul_sum, paritySign_ortho n x y (Finset.mem_range.mp hx) (Finset.mem_range.mp hy)]
      by_cases hxy : x = y
      · subst hxy
        simp only [↓reduceIte, sq, mul_comm]
      · simp [hxy]
    rw [Finset.sum_congr rfl hy, Finset.sum_ite_eq]
    simp [hx]
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

lemma sum_range_pow_add (p b : Nat) (F : Nat → Nat) :
    ∑ x ∈ Finset.range (2 ^ (p + b)), F x =
      ∑ seedTag : Fin (2 ^ p), ∑ y : Fin (2 ^ b), F (seedTag.val + 2 ^ p * y.val) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij
    (fun z _ => z.1.val + 2 ^ p * z.2.val)
    ?_ ?_ ?_ (fun _ _ => rfl)
  · intro z _
    rw [Finset.mem_range]
    have h1 := z.1.isLt
    have h2 := z.2.isLt
    have h3 : 2 ^ p * (z.2.val + 1) ≤ 2 ^ p * 2 ^ b := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add] at h3
    omega
  · intro z1 _ z2 _ heq
    have hmod : z1.1.val = z2.1.val := by
      have h1 : (z1.1.val + 2 ^ p * z1.2.val) % 2 ^ p = (z2.1.val + 2 ^ p * z2.2.val) % 2 ^ p :=
        by rw [heq]
      rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt z1.1.isLt, Nat.mod_eq_of_lt z2.1.isLt] at h1
      exact h1
    have hmul : 2 ^ p * z1.2.val = 2 ^ p * z2.2.val := by omega
    have hdiv : z1.2.val = z2.2.val := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos p) hmul
    exact Prod.ext (Fin.ext hmod) (Fin.ext hdiv)
  · intro x hx
    rw [Finset.mem_range] at hx
    have h1 : x % 2 ^ p < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
    have h2 : x / 2 ^ p < 2 ^ b := Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hx)
    refine ⟨(⟨x % 2 ^ p, h1⟩, ⟨x / 2 ^ p, h2⟩), Finset.mem_univ _, ?_⟩
    exact Nat.mod_add_div x (2 ^ p)

lemma sum_seed_excess_aux {p tries q s : Nat} (histVal : Nat → Nat)
    (hhist_lt : ∀ tag : Nat, histVal tag < 2 ^ tries)
    (hcard : ∀ hist : Fin (2 ^ tries),
      ((Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => histVal tag.val = hist.val)).card =
        2 ^ (p - tries)) :
    ∑ seedTag : Fin (2 ^ p), (2 ^ (max s (q - bitWeight tries (histVal seedTag.val))) - 2 ^ s) =
      2 ^ (p - tries) * ∑ j ∈ Finset.range (tries + 1),
        Nat.choose tries j * (2 ^ (max s (q - j)) - 2 ^ s) := by
  let g : Fin (2 ^ p) → Fin (2 ^ tries) := fun tag => ⟨histVal tag.val, hhist_lt tag.val⟩
  let F : Fin (2 ^ p) → Nat := fun tag => 2 ^ (max s (q - bitWeight tries (histVal tag.val))) - 2 ^ s
  have h1 : ∑ seedTag : Fin (2 ^ p), F seedTag =
      ∑ hist : Fin (2 ^ tries), ∑ seedTag ∈ (Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => g tag = hist),
        F seedTag :=
    (Finset.sum_fiberwise_of_maps_to (g := g) (t := (Finset.univ : Finset (Fin (2 ^ tries))))
      (fun _ _ => Finset.mem_univ _) F).symm
  change ∑ seedTag : Fin (2 ^ p), F seedTag = _
  rw [h1]
  have h2 : ∀ hist : Fin (2 ^ tries),
      ∑ seedTag ∈ (Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => g tag = hist), F seedTag =
      2 ^ (p - tries) * (2 ^ (max s (q - bitWeight tries hist.val)) - 2 ^ s) := by
    intro hist
    have hcongr : ∑ seedTag ∈ (Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => g tag = hist),
        F seedTag =
        ∑ _seedTag ∈ (Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => g tag = hist),
        (2 ^ (max s (q - bitWeight tries hist.val)) - 2 ^ s) := by
      apply Finset.sum_congr rfl
      intro seedTag hmem
      have heq : histVal seedTag.val = hist.val := congrArg Fin.val (Finset.mem_filter.mp hmem).2
      simp only [F, heq]
    rw [hcongr, Finset.sum_const, smul_eq_mul]
    have hset : (Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => g tag = hist) =
        (Finset.univ : Finset (Fin (2 ^ p))).filter (fun tag => histVal tag.val = hist.val) := by
      ext tag
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, g, Fin.ext_iff]
    rw [hset, hcard hist]
  rw [Finset.sum_congr rfl (fun hist _ => h2 hist), ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range (fun c => 2 ^ (max s (q - bitWeight tries c)) - 2 ^ s) (2 ^ tries)]
  congr 1
  have hbw_le : ∀ c ∈ Finset.range (2 ^ tries), bitWeight tries c ∈ Finset.range (tries + 1) := by
    intro c _
    rw [Finset.mem_range]
    have hbl : bitWeight tries c ≤ tries := by
      unfold bitWeight
      exact le_trans (List.length_filter_le _ _) (by simp)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hbw_le]
  apply Finset.sum_congr rfl
  intro j _
  have hcongr : ∑ c ∈ (Finset.range (2 ^ tries)).filter (fun c => bitWeight tries c = j),
      (2 ^ (max s (q - bitWeight tries c)) - 2 ^ s) =
      ∑ _c ∈ (Finset.range (2 ^ tries)).filter (fun c => bitWeight tries c = j),
      (2 ^ (max s (q - j)) - 2 ^ s) :=
    Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.mp hc).2])
  rw [hcongr, Finset.sum_const, smul_eq_mul, card_bitWeight tries j]

lemma walsh_energy_bound {α : Type*} [DecidableEq α] (keep : Finset α)
    (len p a s tries excess : Nat) (obs : α → Nat)
    (hobs_lt : ∀ w ∈ keep, obs w < 2 ^ len)
    (hkeep_card : keep.card = 2 ^ (p + a)) (hlen : len = p + (a - s)) (hsa : s ≤ a)
    (hsum_sq : ∑ x ∈ Finset.range (2 ^ len), ((keep.filter (fun w => obs w = x)).card) ^ 2 ≤
      2 ^ a * (2 ^ (p - tries) * excess + 2 ^ p * 2 ^ s)) :
    (∑ mask ∈ Finset.range (2 ^ len - 1),
      (∑ w ∈ keep, paritySign len (obs w) (mask + 1)) ^ 2) ≤
    (↑(2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess : Nat) : ℤ) := by
  let cnt : Nat → Nat := fun x => (keep.filter (fun w => obs w = x)).card
  let coeff : Nat → ℤ := fun mask => ∑ w ∈ keep, paritySign len (obs w) mask
  have hcoeff_eq : ∀ mask, coeff mask =
      ∑ x ∈ Finset.range (2 ^ len), (cnt x : ℤ) * paritySign len x mask := by
    intro mask
    dsimp only [coeff]
    rw [← Finset.sum_fiberwise_of_maps_to (g := obs)
      (t := Finset.range (2 ^ len)) (fun w hw => Finset.mem_range.mpr (hobs_lt w hw))]
    apply Finset.sum_congr rfl
    intro x _
    have hcongr : ∑ w ∈ keep.filter (fun w => obs w = x), paritySign len (obs w) mask =
        ∑ _w ∈ keep.filter (fun w => obs w = x), paritySign len x mask :=
      Finset.sum_congr rfl (fun w hw => by rw [(Finset.mem_filter.mp hw).2])
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
  have hcoeff0 : coeff 0 = ((2 ^ (p + a) : Nat) : ℤ) := by
    dsimp only [coeff]
    have hcongr : ∑ w ∈ keep, paritySign len (obs w) 0 = ∑ _w ∈ keep, (1 : ℤ) :=
      Finset.sum_congr rfl (fun w _ => paritySign_zero len (obs w))
    rw [hcongr, Finset.sum_const, nsmul_eq_mul, mul_one, hkeep_card]
  have hparseval : (∑ mask ∈ Finset.range (2 ^ len - 1), (coeff (mask + 1)) ^ 2) +
      (((2 ^ (p + a) : Nat) : ℤ)) ^ 2 =
      ((2 ^ len : Nat) : ℤ) * ∑ x ∈ Finset.range (2 ^ len), ((cnt x : ℤ)) ^ 2 := by
    have hpos : 1 ≤ 2 ^ len := Nat.two_pow_pos len
    have hsucc : ∑ mask ∈ Finset.range (2 ^ len), (coeff mask) ^ 2 =
        (∑ mask ∈ Finset.range (2 ^ len - 1), (coeff (mask + 1)) ^ 2) + (coeff 0) ^ 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hpos, Finset.sum_range_succ']
    rw [← hcoeff0, ← hsucc]
    have h1 : ∑ mask ∈ Finset.range (2 ^ len), (coeff mask) ^ 2 =
        ∑ mask ∈ Finset.range (2 ^ len),
          (∑ x ∈ Finset.range (2 ^ len), (cnt x : ℤ) * paritySign len x mask) ^ 2 :=
      Finset.sum_congr rfl (fun mask _ => by rw [hcoeff_eq mask])
    rw [h1, walsh_parseval len (fun x => (cnt x : ℤ)), Nat.cast_pow, Nat.cast_ofNat]
  have hnat_bound :
      2 ^ len * ∑ x ∈ Finset.range (2 ^ len), (cnt x) ^ 2 ≤
        2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess + (2 ^ (p + a)) ^ 2 := by
    have h1 := Nat.mul_le_mul_left (2 ^ len) hsum_sq
    have hbase : 2 ^ len * (2 ^ a * (2 ^ p * 2 ^ s)) = (2 ^ (p + a)) ^ 2 := by
      rw [sq, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega
    have hmain : 2 ^ len * (2 ^ a * (2 ^ (p - tries) * excess)) =
        2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_assoc (2 ^ len) (2 ^ a),
        Nat.mul_comm (2 ^ a) (2 ^ (p - tries)), ← Nat.mul_assoc]
    rw [Nat.mul_add, Nat.mul_add, hbase, hmain] at h1
    exact h1
  have hint_bound :
      ((2 ^ len : Nat) : ℤ) * ∑ x ∈ Finset.range (2 ^ len), ((cnt x : ℤ)) ^ 2 ≤
        (↑(2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess : Nat) : ℤ) + (((2 ^ (p + a) : Nat) : ℤ)) ^ 2 := by
    have hcast : ((2 ^ len * ∑ x ∈ Finset.range (2 ^ len), (cnt x) ^ 2 : Nat) : ℤ) ≤
        ((2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess + (2 ^ (p + a)) ^ 2 : Nat) : ℤ) :=
      Int.ofNat_le.mpr hnat_bound
    have hlhs : ((2 ^ len * ∑ x ∈ Finset.range (2 ^ len), (cnt x) ^ 2 : Nat) : ℤ) =
        ((2 ^ len : Nat) : ℤ) * ∑ x ∈ Finset.range (2 ^ len), ((cnt x : ℤ)) ^ 2 := by
      simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow]
    have hrhs : ((2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess + (2 ^ (p + a)) ^ 2 : Nat) : ℤ) =
        (↑(2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess : Nat) : ℤ) + (((2 ^ (p + a) : Nat) : ℤ)) ^ 2 := by
      rw [Nat.cast_add, Nat.cast_pow]
    rw [hlhs, hrhs] at hcast
    exact hcast
  change (∑ mask ∈ Finset.range (2 ^ len - 1), (coeff (mask + 1)) ^ 2) ≤ _
  linarith

theorem main_29733 :
    ∀ (k r q ell : Nat), 0 < q → q+2 ≤ r → 7*r+q ≤ k → k-(k+1)/2+q ≤ 6*r →
      5 ≤ ell → ell ≤ r → 5*ell+q ≤ 5*r+2 →
      let h := (k+1)/2
      let z := k-h
      let u := 5*r-3
      let tries := ell-1
      let rot := fun (offset x : Nat) =>
        ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
      let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
      let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
        acc ||| ((xor (word.testBit site)
          (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
      let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
        chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
          (constants (if col then r+t else t)).val
      let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
        (List.range r).foldl (fun v tick => step c side key v (tick+1))
          (rot (if side then 3 else 1) key ^^^ name)
      let start := k-(2*r-2)
      let a := min h (k-u)
      let g := z-u
      let project := fun (wordAt : Nat) => rot (k-(start % k)) wordAt % 2^(u-q)
      let p := u-q
      ∀ (sched : Nat → Fin (2^k)) (row col : Fin (2^k))
        (pick : Nat → Fin (2^(q+g))) (s : Nat), s ≤ a →
        let len := p+(a-s)
        let obs := fun (raw : Nat) => project raw +
          2^p * ((state sched false raw row.val >>> (k-a)) % 2^(a-s))
        let keep := (Finset.univ : Finset (Fin (2^k))).filter (fun w =>
          (state sched true w.val col.val >>> (6*r-q)) % 2^(q+g) = (pick (project w.val)).val)
        let coeff := fun (mask : Nat) => ∑ w ∈ keep,
          if ((List.range len).filter (fun i => (obs w.val).testBit i && mask.testBit i)).length % 2 = 0
          then (1 : ℤ) else -1
        let excess := ∑ j ∈ Finset.range (tries+1),
          Nat.choose tries j * (2^(max s (q-j)) - 2^s)
        keep.card = 2^(p+a) ∧
          (∑ mask ∈ Finset.range (2^len-1), (coeff (mask+1))^2) ≤
            (↑(2^len * 2^(p-tries) * 2^a * excess : Nat) : ℤ) := by
  intro k r q ell hq hqr hk7 _ hell5 hellr h5
  dsimp only
  intro sched row col pick s hs
  let h := (k + 1) / 2
  let z := k - h
  let u := 5 * r - 3
  let tries := ell - 1
  let start := k - (2 * r - 2)
  let a := min h (k - u)
  let g := z - u
  let p := u - q
  let len := p + (a - s)
  have hr5 : 5 ≤ r := by omega
  have hsa : s ≤ a := hs
  let project : Nat → Nat := fun wordAt => rot k (k - start % k) wordAt % 2 ^ p
  let obs : Nat → Nat := fun raw =>
    project raw + 2 ^ p * ((stateStep k r sched false raw row.val r >>> (k - a)) % 2 ^ (a - s))
  let keep : Finset (Fin (2 ^ k)) := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = (pick (project w.val)).val)
  let excess : Nat := ∑ j ∈ Finset.range (tries + 1),
    Nat.choose tries j * (2 ^ (max s (q - j)) - 2 ^ s)
  change keep.card = 2 ^ (p + a) ∧
    (∑ mask ∈ Finset.range (2 ^ len - 1),
      (∑ w ∈ keep, paritySign len (obs w.val) (mask + 1)) ^ 2) ≤
      (↑(2 ^ len * 2 ^ (p - tries) * 2 ^ a * excess : Nat) : ℤ)
  have hkeep_fiber : ∀ seedTag : Fin (2 ^ p),
      (keep.filter (fun w =>
        (⟨project w.val, Nat.mod_lt _ (Nat.two_pow_pos p)⟩ : Fin (2 ^ p)) = seedTag)).card = 2 ^ a := by
    intro seedTag
    have hset : keep.filter (fun w =>
        (⟨project w.val, Nat.mod_lt _ (Nat.two_pow_pos p)⟩ : Fin (2 ^ p)) = seedTag) =
        (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
          rot k (k - start % k) w.val % 2 ^ p = seedTag.val ∧
          (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) =
            (pick seedTag.val).val) := by
      ext w
      simp only [keep, project, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
      constructor
      · rintro ⟨hc, hp⟩
        exact ⟨hp, by rw [← hp]; exact hc⟩
      · rintro ⟨hp, hc⟩
        exact ⟨by rw [hp]; exact hc, hp⟩
    rw [hset]
    exact keepFiber_card hq hqr hk7 hr5 sched col seedTag (pick seedTag.val)
  have hkeep_card : keep.card = 2 ^ (p + a) := by
    have hmaps : Set.MapsTo
        (fun w : Fin (2 ^ k) => (⟨project w.val, Nat.mod_lt _ (Nat.two_pow_pos p)⟩ : Fin (2 ^ p)))
        (keep : Set (Fin (2 ^ k))) ((Finset.univ : Finset (Fin (2 ^ p))) : Set (Fin (2 ^ p))) :=
      fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hcongr : ∑ seedTag : Fin (2 ^ p),
        (keep.filter (fun w =>
          (⟨project w.val, Nat.mod_lt _ (Nat.two_pow_pos p)⟩ : Fin (2 ^ p)) = seedTag)).card =
        ∑ _seedTag : Fin (2 ^ p), 2 ^ a :=
      Finset.sum_congr rfl (fun seedTag _ => hkeep_fiber seedTag)
    rw [hcongr, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Nat.pow_add]
  refine ⟨hkeep_card, ?_⟩
  have hobs_lt : ∀ w ∈ keep, obs w.val < 2 ^ len := by
    intro w _
    have h1 : project w.val < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
    have h2 : (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s) < 2 ^ (a - s) :=
      Nat.mod_lt _ (Nat.two_pow_pos (a - s))
    have h3 : 2 ^ p * ((stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s) + 1) ≤
        2 ^ p * 2 ^ (a - s) := Nat.mul_le_mul_left _ h2
    rw [Nat.mul_add, Nat.mul_one, ← Nat.pow_add] at h3
    dsimp only [obs, len]
    omega
  let cnt : Nat → Nat := fun x => (keep.filter (fun w => obs w.val = x)).card
  let histVal : Nat → Nat := fun tag =>
    (histFold k r q sched row.val (rot k start tag) ell).2.1
  let dOf : Nat → Nat := fun tag => q - bitWeight tries (histVal tag)
  have hcell_eq : ∀ (seedTag : Fin (2 ^ p)) (y : Fin (2 ^ (a - s))),
      cnt (seedTag.val + 2 ^ p * y.val) =
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        rot k (k - start % k) w.val % 2 ^ p = seedTag.val ∧
        (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) = (pick seedTag.val).val ∧
        (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s) = y.val)).card := by
    intro seedTag y
    dsimp only [cnt]
    congr 1
    ext w
    simp only [keep, obs, project, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hcol, hobs⟩
      have hp_lt : rot k (k - start % k) w.val % 2 ^ p < 2 ^ p := Nat.mod_lt _ (Nat.two_pow_pos p)
      have hproj_eq : rot k (k - start % k) w.val % 2 ^ p = seedTag.val := by
        have h1 := congrArg (fun t => t % 2 ^ p) hobs
        rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt hp_lt, Nat.mod_eq_of_lt seedTag.isLt] at h1
        exact h1
      have hmul : 2 ^ p * ((stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s)) =
          2 ^ p * y.val := by omega
      have hy_eq : (stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s) = y.val :=
        Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos p) hmul
      exact ⟨hproj_eq, by rw [← hproj_eq]; exact hcol, hy_eq⟩
    · rintro ⟨hproj_eq, hcol, hy_eq⟩
      exact ⟨by rw [hproj_eq]; exact hcol, by rw [hproj_eq, hy_eq]⟩
  have hfiber_sq : ∀ seedTag : Fin (2 ^ p),
      ∑ y : Fin (2 ^ (a - s)), (cnt (seedTag.val + 2 ^ p * y.val)) ^ 2 ≤
        2 ^ (max s (dOf seedTag.val)) * 2 ^ a := by
    intro seedTag
    have hsum_cells : ∑ y : Fin (2 ^ (a - s)), cnt (seedTag.val + 2 ^ p * y.val) = 2 ^ a := by
      have hmaps : Set.MapsTo
          (fun w : Fin (2 ^ k) =>
            (⟨(stateStep k r sched false w.val row.val r >>> (k - a)) % 2 ^ (a - s),
              Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ (a - s))))
          ((Finset.univ.filter (fun w : Fin (2 ^ k) =>
            rot k (k - start % k) w.val % 2 ^ p = seedTag.val ∧
            (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) =
              (pick seedTag.val).val)) : Set (Fin (2 ^ k)))
          ((Finset.univ : Finset (Fin (2 ^ (a - s)))) : Set (Fin (2 ^ (a - s)))) :=
        fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
      have hfc : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
            rot k (k - start % k) w.val % 2 ^ p = seedTag.val ∧
            (stateStep k r sched true w.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) =
              (pick seedTag.val).val)).card = 2 ^ a :=
        keepFiber_card hq hqr hk7 hr5 sched col seedTag (pick seedTag.val)
      rw [Finset.card_eq_sum_card_fiberwise hmaps] at hfc
      rw [← hfc]
      apply Finset.sum_congr rfl
      intro y _
      rw [hcell_eq seedTag y]
      congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
    calc ∑ y : Fin (2 ^ (a - s)), (cnt (seedTag.val + 2 ^ p * y.val)) ^ 2
        ≤ ∑ y : Fin (2 ^ (a - s)),
            2 ^ (max s (dOf seedTag.val)) * cnt (seedTag.val + 2 ^ p * y.val) := by
          apply finset_sum_le_sum
          intro y _
          rw [sq]
          apply Nat.mul_le_mul_right
          rw [hcell_eq seedTag y]
          exact cell_card_le hq hqr hk7 hell5 hellr h5 sched row col seedTag (pick seedTag.val) s hsa y
      _ = 2 ^ (max s (dOf seedTag.val)) *
            ∑ y : Fin (2 ^ (a - s)), cnt (seedTag.val + 2 ^ p * y.val) := by
          rw [← Finset.mul_sum]
      _ = 2 ^ (max s (dOf seedTag.val)) * 2 ^ a := by rw [hsum_cells]
  have hhist_lt : ∀ tag : Nat, histVal tag < 2 ^ tries := by
    intro tag
    have hrec : recCount ell = tries := by unfold recCount; simp only [tries]; split_ifs <;> omega
    rw [← hrec]
    exact (histFold_code_weight k r q sched row.val (rot k start tag) ell).1
  have hseed_excess :
      ∑ seedTag : Fin (2 ^ p), (2 ^ (max s (dOf seedTag.val)) - 2 ^ s) =
        2 ^ (p - tries) * excess :=
    sum_seed_excess_aux histVal hhist_lt (fun hist => part1_card hq hqr hk7 hell5 hellr h5 sched row hist)
  have hsum_sq_nat :
      ∑ x ∈ Finset.range (2 ^ len), (cnt x) ^ 2 ≤
        2 ^ a * (2 ^ (p - tries) * excess + 2 ^ p * 2 ^ s) := by
    rw [show len = p + (a - s) from rfl, sum_range_pow_add p (a - s) (fun x => (cnt x) ^ 2)]
    calc ∑ seedTag : Fin (2 ^ p), ∑ y : Fin (2 ^ (a - s)), (cnt (seedTag.val + 2 ^ p * y.val)) ^ 2
        ≤ ∑ seedTag : Fin (2 ^ p), 2 ^ (max s (dOf seedTag.val)) * 2 ^ a :=
          finset_sum_le_sum _ _ _ (fun seedTag _ => hfiber_sq seedTag)
      _ = 2 ^ a * ∑ seedTag : Fin (2 ^ p), 2 ^ (max s (dOf seedTag.val)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro seedTag _
          exact Nat.mul_comm _ _
      _ = 2 ^ a * ∑ seedTag : Fin (2 ^ p), ((2 ^ (max s (dOf seedTag.val)) - 2 ^ s) + 2 ^ s) := by
          congr 1
          apply Finset.sum_congr rfl
          intro seedTag _
          have hle : 2 ^ s ≤ 2 ^ (max s (dOf seedTag.val)) :=
            Nat.pow_le_pow_right (by omega) (le_max_left _ _)
          exact (Nat.sub_add_cancel hle).symm
      _ = 2 ^ a * ((∑ seedTag : Fin (2 ^ p), (2 ^ (max s (dOf seedTag.val)) - 2 ^ s)) +
            ∑ _seedTag : Fin (2 ^ p), 2 ^ s) := by
          rw [Finset.sum_add_distrib]
      _ = 2 ^ a * (2 ^ (p - tries) * excess + 2 ^ p * 2 ^ s) := by
          rw [hseed_excess, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact walsh_energy_bound keep len p a s tries excess (fun w => obs w.val)
    hobs_lt hkeep_card rfl hsa hsum_sq_nat

end PEqualNP.Outside.L_meta_25730

theorem PEqualNP.Outside.L_meta_25730 :
  ∀ (k r q ell : Nat), 0 < q → q+2 ≤ r → 7*r+q ≤ k → k-(k+1)/2+q ≤ 6*r →
    5 ≤ ell → ell ≤ r → 5*ell+q ≤ 5*r+2 →
    let h := (k+1)/2
    let z := k-h
    let u := 5*r-3
    let tries := ell-1
    let rot := fun (offset x : Nat) =>
      ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
    let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
    let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
      acc ||| ((xor (word.testBit site)
        (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
    let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
      chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
        (constants (if col then r+t else t)).val
    let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
      (List.range r).foldl (fun v tick => step c side key v (tick+1))
        (rot (if side then 3 else 1) key ^^^ name)
    let start := k-(2*r-2)
    let a := min h (k-u)
    let g := z-u
    let project := fun (wordAt : Nat) => rot (k-(start % k)) wordAt % 2^(u-q)
    let p := u-q
    ∀ (sched : Nat → Fin (2^k)) (row col : Fin (2^k))
      (pick : Nat → Fin (2^(q+g))) (s : Nat), s ≤ a →
      let len := p+(a-s)
      let obs := fun (raw : Nat) => project raw +
        2^p * ((state sched false raw row.val >>> (k-a)) % 2^(a-s))
      let keep := (Finset.univ : Finset (Fin (2^k))).filter (fun w =>
        (state sched true w.val col.val >>> (6*r-q)) % 2^(q+g) = (pick (project w.val)).val)
      let coeff := fun (mask : Nat) => ∑ w ∈ keep,
        if ((List.range len).filter (fun i => (obs w.val).testBit i && mask.testBit i)).length % 2 = 0
        then (1 : ℤ) else -1
      let excess := ∑ j ∈ Finset.range (tries+1),
        Nat.choose tries j * (2^(max s (q-j)) - 2^s)
      keep.card = 2^(p+a) ∧
        (∑ mask ∈ Finset.range (2^len-1), (coeff (mask+1))^2) ≤
          (↑(2^len * 2^(p-tries) * 2^a * excess : Nat) : ℤ) :=
  PEqualNP.Outside.L_meta_25730.main_29733
