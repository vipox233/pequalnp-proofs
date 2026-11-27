import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29732_aux

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
              rw [Nat.testBit_eq_false_of_lt]
              exact Nat.one_lt_two_pow (by omega)
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

lemma agree_row_freeze {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (hwt : q ≤ bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)
    {w w' : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hproj1 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hproj2 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w'
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hAgA : AgreeOn k (k - min ((k + 1) / 2) (k - (5 * r - 3)) - (2 * r - 2)) (k - (2 * r - 2)) w w') :
    (stateStep k r sched false w row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) =
      (stateStep k r sched false w' row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) := by
  set a := min ((k + 1) / 2) (k - (5 * r - 3))
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have ha_le : a ≤ k - (5 * r - 3) := Nat.min_le_right _ _
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
  have hcnt_eq : (histFold k r q sched row.val ref ell).2.2 =
      bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1 := by
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row.val ref ell).2
  have hmin_q : min q (histFold k r q sched row.val ref ell).2.2 = q := by
    rw [hcnt_eq]
    exact Nat.min_eq_left hwt
  rw [hlo_r, hmin_r, hmin_q, Nat.sub_self, Nat.mul_zero, Nat.add_zero,
    Nat.sub_add_cancel (by omega)] at hfin
  have hXr1 : stateStep k r sched false w row.val r < 2 ^ k := stateStep_lt row.isLt
  have hXr2 : stateStep k r sched false w' row.val r < 2 ^ k := stateStep_lt row.isLt
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hj : j < a
  · have hlt : k - a + j < k := by omega
    have hbit := hfin (k - a + j) (by omega) hlt
    rwa [bitAt_lt hlt, bitAt_lt hlt] at hbit
  · have hge : k ≤ k - a + j := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hXr1 (Nat.pow_le_pow_right (by omega) hge)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hXr2 (Nat.pow_le_pow_right (by omega) hge))]

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

lemma agree_row_freeze_lo {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q)))
    (hwt : bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1 < q)
    {w w' : Nat} (hw : w < 2 ^ k) (hw' : w' < 2 ^ k)
    (hproj1 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hproj2 : AgreeOn k (k - (2 * r - 2)) (k + 3 * r - 1 - q) w'
      (rot k (k - (2 * r - 2)) seedTag.val))
    (hAgA : AgreeOn k (k - min ((k + 1) / 2) (k - (5 * r - 3)) - (2 * r - 2)) (k - (2 * r - 2)) w w') :
    (stateStep k r sched false w row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - (q - bitWeight (ell - 1)
          (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)) =
      (stateStep k r sched false w' row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - (q - bitWeight (ell - 1)
          (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)) := by
  set a := min ((k + 1) / 2) (k - (5 * r - 3))
  set ref := rot k (k - (2 * r - 2)) seedTag.val
  have ha_le : a ≤ k - (5 * r - 3) := Nat.min_le_right _ _
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
  have hcnt_eq : (histFold k r q sched row.val ref ell).2.2 =
      bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1 := by
    rw [← hrec_ell]
    exact (histFold_code_weight k r q sched row.val ref ell).2
  set cw := bitWeight (ell - 1) (histFold k r q sched row.val ref ell).2.1 with hcw
  have hmin_q : min q (histFold k r q sched row.val ref ell).2.2 = cw := by
    rw [hcnt_eq]
    exact Nat.min_eq_right hwt.le
  rw [hlo_r, hmin_r, hmin_q, Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hfin
  have hXr1 : stateStep k r sched false w row.val r < 2 ^ k := stateStep_lt row.isLt
  have hXr2 : stateStep k r sched false w' row.val r < 2 ^ k := stateStep_lt row.isLt
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hj : j < a - (q - cw)
  · simp only [hj, decide_true, Bool.true_and]
    have hlt : k - a + j < k := by omega
    have hbit := hfin (k - a + j) (by omega) (by omega)
    rwa [bitAt_lt hlt, bitAt_lt hlt] at hbit
  · simp [hj]

lemma spare_bit {x p m spare s : Nat} (h : (x >>> p) % 2 ^ m = spare) (h1 : p ≤ s) (h2 : s < p + m) :
    x.testBit s = spare.testBit (s - p) := by
  have hb := congrArg (fun y => y.testBit (s - p)) h
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight] at hb
  have hlt : s - p < m := by omega
  have he : p + (s - p) = s := by omega
  simp only [hlt, decide_true, Bool.true_and, he] at hb
  exact hb

lemma part2_lo {k r q ell : Nat} (hq : 0 < q) (hqr : q + 2 ≤ r) (hk7 : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5 : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k))
    (seedTag : Fin (2 ^ (5 * r - 3 - q))) (c : Nat)
    (hc : c = bitWeight (ell - 1)
      (histFold k r q sched row.val (rot k (k - (2 * r - 2)) seedTag.val) ell).2.1)
    (hwt : c < q) (m : Nat) (hm : m = q - c)
    (spare : Fin (2 ^ m))
    (rowPart : Fin (2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - m)))
    (colBits : Fin (2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3))))) :
    ∃! w : Fin (2 ^ k),
      rot k (k - (k - (2 * r - 2)) % k) w.val % 2 ^ (5 * r - 3 - q) = seedTag.val ∧
      (w.val >>> (k - (2 * r - 2) - m)) % 2 ^ m = spare.val ∧
      (stateStep k r sched false w.val row.val r >>> (k - min ((k + 1) / 2) (k - (5 * r - 3)))) %
        2 ^ (min ((k + 1) / 2) (k - (5 * r - 3)) - m) = rowPart.val ∧
      (stateStep k r sched true w.val col.val r >>> (6 * r - q)) %
        2 ^ (q + ((k - (k + 1) / 2) - (5 * r - 3))) = colBits.val := by
  let h := (k + 1) / 2
  let z := k - h
  let u := 5 * r - 3
  let start := k - (2 * r - 2)
  let a := min h (k - u)
  let g := z - u
  have hsum_ag : a + g = k - u := by
    simp only [a, g, z, h, u]
    omega
  have hma : m ≤ a := by
    simp only [a, h, u]
    omega
  set baseQG := 3 * r - 1 - q
  set baseA := k - a - (2 * r - 2)
  have hmid_eq : baseQG + (q + g) = baseA := by
    simp only [baseQG, baseA]
    omega
  have hm_start : m ≤ start := by
    simp only [start]
    omega
  have hA_end : baseA + a = start := by
    simp only [baseA, start]
    omega
  have hfreeze : ∀ {w w' : Nat}, w < 2 ^ k → w' < 2 ^ k →
      AgreeOn k start (k + 3 * r - 1 - q) w (rot k start seedTag.val) →
      AgreeOn k start (k + 3 * r - 1 - q) w' (rot k start seedTag.val) →
      AgreeOn k baseA start w w' →
      (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m) =
        (stateStep k r sched false w' row.val r >>> (k - a)) % 2 ^ (a - m) := by
    intro w w' hw hw' h1 h2 h3
    have hfr := agree_row_freeze_lo hq hqr hk7 hell5 hellr h5 sched row seedTag (hc ▸ hwt)
      hw hw' h1 h2 h3
    rw [← hc, ← hm] at hfr
    exact hfr
  have hrow_tri0 : ∀ j < a, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor ((stateStep k r sched false w row.val r >>> (k - a)).testBit j)
          ((stateStep k r sched false w' row.val r >>> (k - a)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
    intro j hj w w' hw hw' hout
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
  have hrow_tri : ∀ j < a - m, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseA ∨ baseA + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m)).testBit j)
          (((stateStep k r sched false w' row.val r >>> (k - a)) % 2 ^ (a - m)).testBit j) =
        xor (w.testBit (baseA + j)) (w'.testBit (baseA + j)) := by
    intro j hj w w' hw hw' hout
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]
    exact hrow_tri0 j (by omega) w w' hw hw' hout
  have hcol_tri : ∀ j < q + g, ∀ w w', w < 2 ^ k → w' < 2 ^ k →
      (∀ s < k, (s < baseQG ∨ baseQG + j < s) → w.testBit s = w'.testBit s) →
      xor (((stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j)
          (((stateStep k r sched true w' col.val r >>> (6 * r - q)) % 2 ^ (q + g)).testBit j) =
        xor (w.testBit (baseQG + j)) (w'.testBit (baseQG + j)) := by
    intro j hj w w' hw hw' hout
    simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and, Nat.testBit_shiftRight]
    have h6rg : 6 * r + g ≤ k := by
      simp only [g, z, h, u]
      omega
    have hi_lt : 6 * r - q + j < k := by omega
    rw [← bitAt_lt hi_lt, ← bitAt_lt hi_lt]
    have hwrap : 6 * r - q + j + 4 * r - 2 ≤ k + baseQG := by
      simp only [baseQG, g, z, h, u] at hj ⊢
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

  let w0 := ofBits k (fun s => if start - m ≤ s ∧ s < start then spare.val.testBit (s - (start - m))
    else (rot k start seedTag.val).testBit s)
  have hw0 : w0 < 2 ^ k := ofBits_lt k _
  have hw0_out : ∀ s < k, (s < baseQG ∨ start ≤ s) →
      w0.testBit s = (rot k start seedTag.val).testBit s := by
    intro s hsk hso
    have hn : ¬ (start - m ≤ s ∧ s < start) := by rcases hso with h1 | h1 <;> omega
    simp only [w0, ofBits_testBit, hsk, hn, ↓reduceIte]
  have hw0_sp : ∀ s, start - m ≤ s → s < start →
      w0.testBit s = spare.val.testBit (s - (start - m)) := by
    intro s h1 h2
    have hsk : s < k := by omega
    simp only [w0, ofBits_testBit, hsk, h1, h2, and_self, ↓reduceIte]
  have hsolveA := triangular_solve (k := k) (base := baseA) (m := a - m) (by omega)
    (fun w => (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hrow_tri w0 hw0 rowPart.val rowPart.isLt
  rcases hsolveA with ⟨w1, ⟨hw1_out, hw1_row⟩, _⟩
  have hsolveQG := triangular_solve (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hcol_tri w1.val w1.isLt colBits.val colBits.isLt
  rcases hsolveQG with ⟨w2, ⟨hw2_out, hw2_col⟩, _⟩
  have hw1_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w1.val (rot k start seedTag.val) := by
    rw [project_iff_outside hq hqr hk7 seedTag w1.val]
    intro s hsk hso
    rw [hw1_out s hsk (by rcases hso with h1 | h1 <;> omega)]
    exact hw0_out s hsk hso
  have hw2_eq_w1 : ∀ s < k, (s < baseQG ∨ baseA ≤ s) → w2.val.testBit s = w1.val.testBit s := by
    intro s hsk hso
    exact hw2_out s hsk (by rcases hso with h1 | h1 <;> omega)
  have hw2_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w2.val (rot k start seedTag.val) := by
    rw [project_iff_outside hq hqr hk7 seedTag w2.val]
    intro s hsk hso
    rw [hw2_eq_w1 s hsk (by rcases hso with h1 | h1 <;> omega)]
    exact (project_iff_outside hq hqr hk7 seedTag w1.val).mp hw1_proj_ag s hsk hso
  have hw2_proj : rot k (k - start % k) w2.val % 2 ^ (u - q) = seedTag.val :=
    (project_iff_agree hq hqr hk7 seedTag w2.val w2.isLt).mpr hw2_proj_ag
  have hw2_sp_bit : ∀ s, start - m ≤ s → s < start →
      w2.val.testBit s = spare.val.testBit (s - (start - m)) := by
    intro s h1 h2
    have hsk : s < k := by omega
    rw [hw2_eq_w1 s hsk (Or.inr (by omega)), hw1_out s hsk (Or.inr (by omega))]
    exact hw0_sp s h1 h2
  have hw2_sp : (w2.val >>> (start - m)) % 2 ^ m = spare.val := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    by_cases hj : j < m
    · simp only [hj, decide_true, Bool.true_and]
      rw [hw2_sp_bit (start - m + j) (by omega) (by omega)]
      congr 1
      omega
    · simp only [hj, decide_false, Bool.false_and]
      exact (Nat.testBit_lt_two_pow
        (lt_of_lt_of_le spare.isLt (Nat.pow_le_pow_right (by omega) (by omega)))).symm
  have hw2_agA : AgreeOn k baseA start w2.val w1.val := by
    intro i hi1 hi2
    have hik : i < k := by omega
    rw [bitAt_lt hik, bitAt_lt hik]
    exact hw2_eq_w1 i hik (Or.inr hi1)
  have hw2_row : (stateStep k r sched false w2.val row.val r >>> (k - a)) % 2 ^ (a - m) =
      rowPart.val := by
    rw [hfreeze w2.isLt w1.isLt hw2_proj_ag hw1_proj_ag hw2_agA]
    exact hw1_row
  refine ⟨w2, ⟨hw2_proj, hw2_sp, hw2_row, hw2_col⟩, ?_⟩
  rintro w3 ⟨hw3_proj, hw3_sp, hw3_row, hw3_col⟩
  have hw3_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) w3.val (rot k start seedTag.val) :=
    (project_iff_agree hq hqr hk7 seedTag w3.val w3.isLt).mp hw3_proj
  have hw3_sp_bit : ∀ s, start - m ≤ s → s < start →
      w3.val.testBit s = spare.val.testBit (s - (start - m)) := by
    intro s h1 h2
    exact spare_bit hw3_sp h1 (by omega)
  let wMix := ofBits k (fun j => if baseA ≤ j ∧ j < start then w3.val.testBit j else w2.val.testBit j)
  have hwMix_lt : wMix < 2 ^ k := ofBits_lt k _
  have hwMix_proj_ag : AgreeOn k start (k + 3 * r - 1 - q) wMix (rot k start seedTag.val) := by
    rw [project_iff_outside hq hqr hk7 seedTag wMix]
    intro s hsk hso
    have hnotA : ¬ (baseA ≤ s ∧ s < start) := by
      rcases hso with hlt | hge <;> omega
    simp only [wMix, ofBits_testBit, hsk, hnotA, ↓reduceIte]
    exact (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk hso
  have hwMix_agA : AgreeOn k baseA start wMix w3.val := by
    intro i hi1 hi2
    have hik : i < k := by omega
    simp [bitAt_lt hik, wMix, ofBits_testBit, hik, hi1, hi2]
  have hwMix_row : (stateStep k r sched false wMix row.val r >>> (k - a)) % 2 ^ (a - m) =
      rowPart.val := by
    rw [hfreeze hwMix_lt w3.isLt hwMix_proj_ag hw3_proj_ag hwMix_agA]
    exact hw3_row
  have hwMix_eq_w2 : (⟨wMix, hwMix_lt⟩ : Fin (2 ^ k)) = w2 := by
    have huniqA := triangular_solve (k := k) (base := baseA) (m := a - m) (by omega)
      (fun w => (stateStep k r sched false w row.val r >>> (k - a)) % 2 ^ (a - m))
      (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
      hrow_tri w2.val w2.isLt rowPart.val rowPart.isLt
    rcases huniqA with ⟨wU, _, hU⟩
    have h1 : (⟨wMix, hwMix_lt⟩ : Fin (2 ^ k)) = wU := by
      apply hU
      refine ⟨?_, hwMix_row⟩
      intro s hsk hso
      show wMix.testBit s = w2.val.testBit s
      by_cases hin : baseA ≤ s ∧ s < start
      · simp only [wMix, ofBits_testBit, hsk, hin, and_self, ↓reduceIte]
        have hs1 : start - m ≤ s := by rcases hso with h1 | h1 <;> omega
        rw [hw3_sp_bit s hs1 hin.2, hw2_sp_bit s hs1 hin.2]
      · simp only [wMix, ofBits_testBit, hsk, hin, ↓reduceIte]
    have h2 : w2 = wU := hU w2 ⟨fun _ _ _ => rfl, hw2_row⟩
    rw [h1, h2]
  have hw3_eq_w2_A : ∀ s < k, (s < baseQG ∨ baseQG + (q + g) ≤ s) →
      w3.val.testBit s = w2.val.testBit s := by
    intro s hsk hso
    rcases hso with hlt | hge
    · rw [(project_iff_outside hq hqr hk7 seedTag w3.val).mp hw3_proj_ag s hsk (Or.inl hlt),
        (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk (Or.inl hlt)]
    · by_cases hst : start ≤ s
      · rw [(project_iff_outside hq hqr hk7 seedTag w3.val).mp hw3_proj_ag s hsk (Or.inr hst),
          (project_iff_outside hq hqr hk7 seedTag w2.val).mp hw2_proj_ag s hsk (Or.inr hst)]
      · have hval : wMix = w2.val := congrArg Fin.val hwMix_eq_w2
        have hbit : wMix.testBit s = w2.val.testBit s := by rw [hval]
        have hin : baseA ≤ s ∧ s < start := ⟨by omega, by omega⟩
        simp only [wMix, ofBits_testBit, hsk, hin, and_self, ↓reduceIte] at hbit
        exact hbit
  have huniqQG := triangular_solve (k := k) (base := baseQG) (m := q + g) (by omega)
    (fun w => (stateStep k r sched true w col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (fun _ _ => Nat.mod_lt _ (Nat.two_pow_pos _))
    hcol_tri w2.val w2.isLt colBits.val colBits.isLt
  rcases huniqQG with ⟨wU, _, hU⟩
  have h1 : w3 = wU := hU w3 ⟨hw3_eq_w2_A, hw3_col⟩
  have h2 : w2 = wU := hU w2 ⟨fun _ _ _ => rfl, hw2_col⟩
  rw [h1, h2]

theorem main :
(∀ (k r q ell : Nat), 0 < q → q+2 ≤ r → 7*r+q ≤ k → k-(k+1)/2+q ≤ 6*r →
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
  let weight := fun (code : Nat) => ((List.range tries).filter (fun jj => code.testBit jj)).length
  ∀ (sched : Nat → Fin (2^k)) (row col : Fin (2^k)),
    let history := fun (label : Nat) =>
      let ref := rot start label
      let init : Nat × Nat × Nat := (rot 1 ref ^^^ row.val, 0, 0)
      let final := (List.range ell).foldl (fun triple idx =>
        let time := idx+1
        let place := k-q+3*(r-time)+min (q-1) triple.2.2
        let bit := (mix 1 triple.1).testBit ((place+1) % k)
        let next := step sched false ref triple.1 time
        if time=4 then (next, triple.2.1, triple.2.2)
        else (next, 2*triple.2.1+bit.toNat, triple.2.2+bit.toNat)) init
      final.2.1
    ∀ tag : Fin (2^(u-q)),
      let hits := weight (history tag.val)
      hits < q →
      let missed := q-hits
      ∀ (spare : Fin (2^missed)) (rowPart : Fin (2^(a-missed)))
        (columnPart : Fin (2^(q+g))),
        ∃! w : Fin (2^k), project w.val = tag.val ∧
          (w.val >>> (start-missed)) % 2^missed = spare.val ∧
          (state sched false w.val row.val >>> (k-a)) % 2^(a-missed) = rowPart.val ∧
          (state sched true w.val col.val >>> (6*r-q)) % 2^(q+g) = columnPart.val) := by
  intro k r q ell hq hqr hk7 _ hell5 hellr h5
  dsimp only
  intro sched row col tag hlt spare rowPart columnPart
  exact part2_lo hq hqr hk7 hell5 hellr h5 sched row col tag _ rfl hlt _ rfl spare rowPart columnPart

end PEqualNP.Outside.L_meta_29732_aux

theorem PEqualNP.Outside.L_meta_29732 : (∀ (k r q ell : Nat), 0 < q → q+2 ≤ r → 7*r+q ≤ k → k-(k+1)/2+q ≤ 6*r →
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
  let weight := fun (code : Nat) => ((List.range tries).filter (fun jj => code.testBit jj)).length
  ∀ (sched : Nat → Fin (2^k)) (row col : Fin (2^k)),
    let history := fun (label : Nat) =>
      let ref := rot start label
      let init : Nat × Nat × Nat := (rot 1 ref ^^^ row.val, 0, 0)
      let final := (List.range ell).foldl (fun triple idx =>
        let time := idx+1
        let place := k-q+3*(r-time)+min (q-1) triple.2.2
        let bit := (mix 1 triple.1).testBit ((place+1) % k)
        let next := step sched false ref triple.1 time
        if time=4 then (next, triple.2.1, triple.2.2)
        else (next, 2*triple.2.1+bit.toNat, triple.2.2+bit.toNat)) init
      final.2.1
    ∀ tag : Fin (2^(u-q)),
      let hits := weight (history tag.val)
      hits < q →
      let missed := q-hits
      ∀ (spare : Fin (2^missed)) (rowPart : Fin (2^(a-missed)))
        (columnPart : Fin (2^(q+g))),
        ∃! w : Fin (2^k), project w.val = tag.val ∧
          (w.val >>> (start-missed)) % 2^missed = spare.val ∧
          (state sched false w.val row.val >>> (k-a)) % 2^(a-missed) = rowPart.val ∧
          (state sched true w.val col.val >>> (6*r-q)) % 2^(q+g) = columnPart.val) := by
  exact PEqualNP.Outside.L_meta_29732_aux.main
