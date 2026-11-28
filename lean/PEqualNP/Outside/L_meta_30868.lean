import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Finite

namespace PEqualNP.Outside.L_meta_30868_aux

def bVal (r : ℕ) : ℕ :=
  if r = 0 then 2 else if r = 1 then 7 else 7 * r - 2

def rotFn (k d x : ℕ) : ℕ :=
  ((x <<< (d % k)) ||| (x >>> (k - d % k))) % 2 ^ k

def chiStep (k x acc i : ℕ) : ℕ :=
  acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)

def chiPrefix (k x m : ℕ) : ℕ :=
  (List.range m).foldl (chiStep k x) 0

def chiFn (k x : ℕ) : ℕ :=
  chiPrefix k x k

def mixFn (k gap z : ℕ) : ℕ :=
  z ^^^ rotFn k gap z ^^^ rotFn k (k - gap % k) z

def stepFn (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key z j : ℕ) : ℕ :=
  let gap : ℕ := if col then 2 else 1
  let mixed := mixFn k gap z
  chiFn k mixed ^^^ rotFn k (if col then 3 * (j + 1) + 1 else 2 * j) key ^^^
    (masks (if col then r + j else j)).val

def runPrefix (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key nm m : ℕ) : ℕ :=
  (List.range m).foldl (stepFn k r masks col key) (rotFn k (if col then 3 else 1) key ^^^ nm)

def nameFn (k r h gap : ℕ) (base : Fin (2 ^ k)) (word : Fin (2 ^ h)) : ℕ :=
  let lo := k - h - gap * r
  base.val % 2 ^ lo + (word.val <<< lo) + ((base.val >>> (lo + h)) <<< (lo + h))

lemma testBit_eq_false_of_lt_two_pow {x k i : ℕ} (hx : x < 2 ^ k) (hi : k ≤ i) :
    x.testBit i = false := by
  rw [← Nat.mod_eq_of_lt hx, Nat.testBit_mod_two_pow]
  have hni : ¬ i < k := by omega
  simp [hni]

lemma lt_two_pow_of_testBit_eq_false {x k : ℕ} (hx : ∀ i, k ≤ i → x.testBit i = false) :
    x < 2 ^ k := by
  have hmod : x = x % 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < k
    · simp [hi]
    · have hk : k ≤ i := by omega
      simp [hi, hx i hk]
  rw [hmod]
  exact Nat.mod_lt x (Nat.two_pow_pos k)

lemma eq_of_testBit_eq_lt {x y k : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ i < k, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact h i hi
  · rw [testBit_eq_false_of_lt_two_pow hx (by omega),
        testBit_eq_false_of_lt_two_pow hy (by omega)]

lemma xor_lt_two_pow {x y k : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k) : x ^^^ y < 2 ^ k := by
  apply lt_two_pow_of_testBit_eq_false
  intro i hi
  rw [Nat.testBit_xor, testBit_eq_false_of_lt_two_pow hx hi,
      testBit_eq_false_of_lt_two_pow hy hi]
  rfl

lemma shr_lt_two_pow {z k h : ℕ} (hz : z < 2 ^ k) (hh : h ≤ k) : z >>> (k - h) < 2 ^ h := by
  apply lt_two_pow_of_testBit_eq_false
  intro i hi
  rw [Nat.testBit_shiftRight]
  exact testBit_eq_false_of_lt_two_pow hz (by omega)

lemma shr_eq_iff {z k h : ℕ} (hz : z < 2 ^ k) (a : Fin (2 ^ h)) (hh : h ≤ k) :
    z >>> (k - h) = a.val ↔ ∀ t < h, z.testBit (k - h + t) = a.val.testBit t := by
  constructor
  · intro hEq t ht
    rw [← hEq, Nat.testBit_shiftRight]
  · intro hBits
    apply eq_of_testBit_eq_lt (shr_lt_two_pow hz hh) a.isLt
    intro t ht
    rw [Nat.testBit_shiftRight]
    exact hBits t ht

lemma rotFn_lt (k d x : ℕ) : rotFn k d x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotFn_testBit {k x : ℕ} (hk : 0 < k) (hx : x < 2 ^ k) (d i : ℕ) (hi : i < k) :
    (rotFn k d x).testBit i = x.testBit ((i + k - d % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  set s := d % k
  have hs : s < k := Nat.mod_lt d hk
  by_cases hs0 : s = 0
  · rw [hs0]
    have hge : k ≤ k - 0 + i := by omega
    rw [testBit_eq_false_of_lt_two_pow hx hge]
    simp only [Nat.zero_le, decide_true, Bool.true_and, Nat.sub_zero, Bool.or_false]
    congr 1
    have h1 : (i + k) % k = i := by
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    exact h1.symm
  · by_cases hsi : s ≤ i
    · have hge : k ≤ k - s + i := by omega
      rw [testBit_eq_false_of_lt_two_pow hx hge]
      simp only [hsi, decide_true, Bool.true_and, Bool.or_false]
      congr 1
      have h1 : i + k - s = (i - s) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · have hlt : i + k - s < k := by omega
      have heq : k - s + i = i + k - s := by omega
      simp only [hsi, decide_false, Bool.false_and, Bool.false_or]
      rw [Nat.mod_eq_of_lt hlt, heq]

lemma chiPrefix_succ (k x m : ℕ) :
    chiPrefix k x (m + 1) = chiStep k x (chiPrefix k x m) m := by
  unfold chiPrefix
  rw [List.range_succ, List.foldl_concat]

lemma chiPrefix_testBit (k x m i : ℕ) :
    (chiPrefix k x m).testBit i =
      if i < m then xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))
      else false := by
  induction m with
  | zero =>
    simp [chiPrefix]
  | succ m ih =>
    rw [chiPrefix_succ, chiStep, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have h1 : i < m + 1 := by omega
      have h2 : ¬ m ≤ i := by omega
      simp [him, h1, h2]
    · by_cases hieq : i = m
      · subst hieq
        simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, le_refl, decide_true, Bool.true_and,
          Nat.sub_self, Bool.false_or]
        cases (xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))) <;> rfl
      · have h1 : ¬ i < m + 1 := by omega
        have h2 : 1 ≤ i - m := by omega
        have hlt2 : (xor (x.testBit m)
            (!(x.testBit ((m + 1) % k)) && x.testBit ((m + 2) % k))).toNat < 2 ^ 1 := by
          cases (xor (x.testBit m)
            (!(x.testBit ((m + 1) % k)) && x.testBit ((m + 2) % k))) <;> decide
        rw [testBit_eq_false_of_lt_two_pow hlt2 h2]
        simp [him, h1]

lemma chiFn_lt (k x : ℕ) : chiFn k x < 2 ^ k := by
  apply lt_two_pow_of_testBit_eq_false
  intro i hi
  rw [chiFn, chiPrefix_testBit]
  have hni : ¬ i < k := by omega
  simp [hni]

lemma chiFn_testBit {k i : ℕ} (hi : i < k) (x : ℕ) :
    (chiFn k x).testBit i =
      xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k)) := by
  rw [chiFn, chiPrefix_testBit]
  simp [hi]

lemma runPrefix_zero (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key nm : ℕ) :
    runPrefix k r masks col key nm 0 = rotFn k (if col then 3 else 1) key ^^^ nm := rfl

lemma runPrefix_succ (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key nm m : ℕ) :
    runPrefix k r masks col key nm (m + 1) =
      stepFn k r masks col key (runPrefix k r masks col key nm m) m := by
  unfold runPrefix
  rw [List.range_succ, List.foldl_concat]

lemma stepFn_lt (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key z j : ℕ) :
    stepFn k r masks col key z j < 2 ^ k := by
  unfold stepFn
  exact xor_lt_two_pow (xor_lt_two_pow (chiFn_lt k _) (rotFn_lt k _ _)) (masks _).isLt

lemma runPrefix_lt {k r : ℕ} (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key nm : ℕ)
    (hnm : nm < 2 ^ k) : ∀ m, runPrefix k r masks col key nm m < 2 ^ k
  | 0 => xor_lt_two_pow (rotFn_lt k _ _) hnm
  | m + 1 => by
    rw [runPrefix_succ]
    exact stepFn_lt k r masks col key _ m

lemma testBit_add_shiftLeft {a b m i : ℕ} (ha : a < 2 ^ m) :
    (a + (b <<< m)).testBit i = if i < m then a.testBit i else b.testBit (i - m) := by
  rw [Nat.shiftLeft_eq]
  simp only [Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < m
  · simp only [hi, ↓reduceIte]
    have hpow : 2 ^ m = 2 ^ i * 2 ^ (m - i) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
    have hdiv : (a + b * 2 ^ m) / 2 ^ i = a / 2 ^ i + b * 2 ^ (m - i) := by
      rw [hpow, ← Nat.mul_assoc, Nat.mul_comm b (2 ^ i), Nat.mul_assoc,
          Nat.add_mul_div_left _ _ (Nat.two_pow_pos i)]
    have heven : 2 ∣ 2 ^ (m - i) := by
      have hm1 : 1 ≤ m - i := by omega
      rw [← Nat.pow_one 2]
      exact Nat.pow_dvd_pow 2 hm1
    rcases heven with ⟨c, hc⟩
    rw [hdiv, hc, ← Nat.mul_assoc, Nat.mul_comm (b * 2) c, Nat.mul_comm b 2,
        ← Nat.mul_assoc, Nat.mul_comm c 2, Nat.mul_assoc, Nat.add_mul_mod_self_left]
  · simp only [hi, ↓reduceIte]
    have hmi : m ≤ i := by omega
    have hpow : 2 ^ i = 2 ^ m * 2 ^ (i - m) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hmi]
    have hdiv1 : (a + b * 2 ^ m) / 2 ^ m = b := by
      rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos m), Nat.div_eq_of_lt ha, Nat.zero_add]
    rw [hpow, ← Nat.div_div_eq_div_mul, hdiv1]

lemma nameFn_testBit_all {k r h gap : ℕ} (base : Fin (2 ^ k)) (word : Fin (2 ^ h)) (i : ℕ) :
    (nameFn k r h gap base word).testBit i =
      if k - h - gap * r ≤ i ∧ i < k - h - gap * r + h then
        word.val.testBit (i - (k - h - gap * r))
      else base.val.testBit i := by
  unfold nameFn
  dsimp only
  set lo := k - h - gap * r
  have h1 : base.val % 2 ^ lo < 2 ^ lo := Nat.mod_lt _ (Nat.two_pow_pos lo)
  have hmid_lt : base.val % 2 ^ lo + (word.val <<< lo) < 2 ^ (lo + h) := by
    rw [Nat.shiftLeft_eq, Nat.pow_add]
    have hw : word.val + 1 ≤ 2 ^ h := word.isLt
    have hmul : (word.val + 1) * 2 ^ lo ≤ 2 ^ h * 2 ^ lo := Nat.mul_le_mul_right _ hw
    have hcomm : 2 ^ h * 2 ^ lo = 2 ^ lo * 2 ^ h := Nat.mul_comm _ _
    have hdist : (word.val + 1) * 2 ^ lo = word.val * 2 ^ lo + 2 ^ lo := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [testBit_add_shiftLeft hmid_lt]
  by_cases hhi : i < lo + h
  · simp only [hhi, ↓reduceIte]
    rw [testBit_add_shiftLeft h1]
    by_cases hlo : i < lo
    · have hnot : ¬ (lo ≤ i ∧ i < lo + h) := by omega
      simp [hlo, hnot, Nat.testBit_mod_two_pow]
    · have hyes : lo ≤ i ∧ i < lo + h := by omega
      simp [hlo, hyes]
  · have hnot : ¬ (lo ≤ i ∧ i < lo + h) := by omega
    have hadd : lo + h + (i - (lo + h)) = i := by omega
    simp [hhi, hnot, Nat.testBit_shiftRight, hadd]

lemma nameFn_lt {k r h gap : ℕ} (hle : k - h - gap * r + h ≤ k)
    (base : Fin (2 ^ k)) (word : Fin (2 ^ h)) :
    nameFn k r h gap base word < 2 ^ k := by
  apply lt_two_pow_of_testBit_eq_false
  intro i hi
  rw [nameFn_testBit_all]
  have hnot : ¬ (k - h - gap * r ≤ i ∧ i < k - h - gap * r + h) := by omega
  simp only [hnot, ↓reduceIte]
  exact testBit_eq_false_of_lt_two_pow base.isLt hi

lemma mixFn_testBit {k gap z i : ℕ} (hgap0 : 0 < gap) (hgapk : gap < k)
    (hz : z < 2 ^ k) (hi : i < k) :
    (mixFn k gap z).testBit i =
      xor (xor (z.testBit i) (z.testBit ((i + k - gap) % k))) (z.testBit ((i + gap) % k)) := by
  have hk : 0 < k := by omega
  unfold mixFn
  rw [Nat.testBit_xor, Nat.testBit_xor, rotFn_testBit hk hz gap i hi,
      rotFn_testBit hk hz (k - gap % k) i hi]
  have hgm : gap % k = gap := Nat.mod_eq_of_lt hgapk
  have hkgm : (k - gap) % k = k - gap := Nat.mod_eq_of_lt (by omega)
  rw [hgm, hkgm]
  have hsub : i + k - (k - gap) = i + gap := by omega
  rw [hsub]

lemma mixFn_lt {k gap z : ℕ} (hz : z < 2 ^ k) : mixFn k gap z < 2 ^ k :=
  xor_lt_two_pow (xor_lt_two_pow hz (rotFn_lt k _ _)) (rotFn_lt k _ _)

lemma chi_mix_agree {k gap z1 z2 i : ℕ} (hgap0 : 0 < gap) (hgapk : gap < k)
    (hz1 : z1 < 2 ^ k) (hz2 : z2 < 2 ^ k) (hi : i < k)
    (hwin : ∀ u ≤ 2 + 2 * gap,
      z1.testBit ((i + k - gap + u) % k) = z2.testBit ((i + k - gap + u) % k)) :
    (chiFn k (mixFn k gap z1)).testBit i = (chiFn k (mixFn k gap z2)).testBit i := by
  have hk : 0 < k := by omega
  rw [chiFn_testBit hi, chiFn_testBit hi]
  have hmix : ∀ d ≤ 2,
      (mixFn k gap z1).testBit ((i + d) % k) = (mixFn k gap z2).testBit ((i + d) % k) := by
    intro d hd
    have hid : (i + d) % k < k := Nat.mod_lt _ hk
    rw [mixFn_testBit hgap0 hgapk hz1 hid, mixFn_testBit hgap0 hgapk hz2 hid]
    have e1 : (i + d) % k = (i + k - gap + (gap + d)) % k := by
      have h1 : i + k - gap + (gap + d) = (i + d) + k := by omega
      rw [h1, Nat.add_mod_right]
    have e2 : ((i + d) % k + k - gap) % k = (i + k - gap + d) % k := by
      have h1 : ((i + d) % k + k - gap) = (i + d) % k + (k - gap) := by omega
      have h2 : (i + d) + (k - gap) = i + k - gap + d := by omega
      rw [h1, Nat.mod_add_mod, h2]
    have e3 : ((i + d) % k + gap) % k = (i + k - gap + (2 * gap + d)) % k := by
      have h1 : i + k - gap + (2 * gap + d) = (i + d + gap) + k := by omega
      rw [Nat.mod_add_mod, h1, Nat.add_mod_right]
    rw [e2, e3, e1, hwin (gap + d) (by omega), hwin d (by omega), hwin (2 * gap + d) (by omega)]
  have h0 := hmix 0 (by omega)
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hi] at h0
  rw [h0, hmix 1 (by omega), hmix 2 (by omega)]

lemma chi_mix_pivot_iff {k gap z1 z2 i : ℕ} (hgap0 : 0 < gap) (hgapk : gap < k)
    (hz1 : z1 < 2 ^ k) (hz2 : z2 < 2 ^ k) (hi : i < k)
    (hwin : ∀ u, 1 ≤ u → u ≤ 2 + 2 * gap →
      z1.testBit ((i + k - gap + u) % k) = z2.testBit ((i + k - gap + u) % k)) :
    ((chiFn k (mixFn k gap z1)).testBit i = (chiFn k (mixFn k gap z2)).testBit i) ↔
      (z1.testBit ((i + k - gap) % k) = z2.testBit ((i + k - gap) % k)) := by
  have hk : 0 < k := by omega
  rw [chiFn_testBit hi, chiFn_testBit hi]
  have hmix_pos : ∀ d, 1 ≤ d → d ≤ 2 →
      (mixFn k gap z1).testBit ((i + d) % k) = (mixFn k gap z2).testBit ((i + d) % k) := by
    intro d hd1 hd2
    have hid : (i + d) % k < k := Nat.mod_lt _ hk
    rw [mixFn_testBit hgap0 hgapk hz1 hid, mixFn_testBit hgap0 hgapk hz2 hid]
    have e1 : (i + d) % k = (i + k - gap + (gap + d)) % k := by
      have h1 : i + k - gap + (gap + d) = (i + d) + k := by omega
      rw [h1, Nat.add_mod_right]
    have e2 : ((i + d) % k + k - gap) % k = (i + k - gap + d) % k := by
      have h1 : ((i + d) % k + k - gap) = (i + d) % k + (k - gap) := by omega
      have h2 : (i + d) + (k - gap) = i + k - gap + d := by omega
      rw [h1, Nat.mod_add_mod, h2]
    have e3 : ((i + d) % k + gap) % k = (i + k - gap + (2 * gap + d)) % k := by
      have h1 : i + k - gap + (2 * gap + d) = (i + d + gap) + k := by omega
      rw [Nat.mod_add_mod, h1, Nat.add_mod_right]
    rw [e2, e3, e1, hwin (gap + d) (by omega) (by omega),
        hwin d (by omega) (by omega), hwin (2 * gap + d) (by omega) (by omega)]
  rw [hmix_pos 1 (by omega) (by omega), hmix_pos 2 (by omega) (by omega)]
  rw [mixFn_testBit hgap0 hgapk hz1 hi, mixFn_testBit hgap0 hgapk hz2 hi]
  have e0 : i = (i + k - gap + gap) % k := by
    have h1 : i + k - gap + gap = i + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  have e2 : (i + gap) % k = (i + k - gap + 2 * gap) % k := by
    have h1 : i + k - gap + 2 * gap = (i + gap) + k := by omega
    rw [h1, Nat.add_mod_right]
  have hbit0 : z1.testBit i = z2.testBit i := by
    conv_lhs => rw [e0]
    conv_rhs => rw [e0]
    exact hwin gap (by omega) (by omega)
  have hbit2 : z1.testBit ((i + gap) % k) = z2.testBit ((i + gap) % k) := by
    rw [e2]
    exact hwin (2 * gap) (by omega) (by omega)
  rw [hbit0, hbit2]
  generalize z1.testBit ((i + k - gap) % k) = a
  generalize z2.testBit ((i + k - gap) % k) = b
  generalize z2.testBit i = c
  generalize z2.testBit ((i + gap) % k) = d
  generalize (!(mixFn k gap z2).testBit ((i + 1) % k) && (mixFn k gap z2).testBit ((i + 2) % k)) = e
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

lemma runPrefix_nm_agree {k r : ℕ} (hk : 3 ≤ k) (masks : ℕ → Fin (2 ^ k)) (col : Bool)
    (key nm1 nm2 : ℕ) (hnm1 : nm1 < 2 ^ k) (hnm2 : nm2 < 2 ^ k) :
    ∀ j i, i < k →
      (∀ u ≤ j * (2 + 2 * (if col then 2 else 1)),
        nm1.testBit ((i + j * k - j * (if col then 2 else 1) + u) % k) =
        nm2.testBit ((i + j * k - j * (if col then 2 else 1) + u) % k)) →
      (runPrefix k r masks col key nm1 j).testBit i =
      (runPrefix k r masks col key nm2 j).testBit i := by
  intro j
  induction j with
  | zero =>
    intro i hi hwin
    have h0 := hwin 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.mod_eq_of_lt hi] at h0
    rw [runPrefix_zero, runPrefix_zero, Nat.testBit_xor, Nat.testBit_xor, h0]
  | succ j ih =>
    intro i hi hwin
    set gap : ℕ := if col then 2 else 1
    have hgap0 : 0 < gap := by cases col <;> decide
    have hgapk : gap < k := by cases col <;> dsimp [gap] <;> omega
    have hjk : j * gap ≤ j * k := Nat.mul_le_mul_left j (Nat.le_of_lt hgapk)
    rw [runPrefix_succ, runPrefix_succ]
    unfold stepFn
    dsimp only
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    congr 2
    apply chi_mix_agree hgap0 hgapk (runPrefix_lt masks col key nm1 hnm1 j)
      (runPrefix_lt masks col key nm2 hnm2 j) hi
    intro v hv
    have hi' : (i + k - gap + v) % k < k := Nat.mod_lt _ (by omega)
    apply ih ((i + k - gap + v) % k) hi'
    intro w hw
    have hmod : ((i + k - gap + v) % k + j * k - j * gap + w) % k =
        (i + (j + 1) * k - (j + 1) * gap + (v + w)) % k := by
      have h1 : (i + k - gap + v) % k + j * k - j * gap + w =
          (i + k - gap + v) % k + (j * k - j * gap + w) := by omega
      have h2 : (i + k - gap + v) + (j * k - j * gap + w) =
          i + (j + 1) * k - (j + 1) * gap + (v + w) := by
        have hm1 : (j + 1) * k = j * k + k := Nat.succ_mul j k
        have hm2 : (j + 1) * gap = j * gap + gap := Nat.succ_mul j gap
        omega
      rw [h1, Nat.mod_add_mod, h2]
    rw [hmod]
    have hvw : v + w ≤ (j + 1) * (2 + 2 * gap) := by
      have hm : (j + 1) * (2 + 2 * gap) = j * (2 + 2 * gap) + (2 + 2 * gap) := Nat.succ_mul _ _
      omega
    exact hwin (v + w) hvw

lemma runPrefix_nm_pivot_iff {k r : ℕ} (hk : 3 ≤ k) (masks : ℕ → Fin (2 ^ k)) (col : Bool)
    (key nm1 nm2 : ℕ) (hnm1 : nm1 < 2 ^ k) (hnm2 : nm2 < 2 ^ k) :
    ∀ j i, i < k →
      (∀ u, 1 ≤ u → u ≤ j * (2 + 2 * (if col then 2 else 1)) →
        nm1.testBit ((i + j * k - j * (if col then 2 else 1) + u) % k) =
        nm2.testBit ((i + j * k - j * (if col then 2 else 1) + u) % k)) →
      ((runPrefix k r masks col key nm1 j).testBit i =
       (runPrefix k r masks col key nm2 j).testBit i ↔
        nm1.testBit ((i + j * k - j * (if col then 2 else 1)) % k) =
        nm2.testBit ((i + j * k - j * (if col then 2 else 1)) % k)) := by
  intro j
  induction j with
  | zero =>
    intro i hi _
    simp only [Nat.zero_mul, Nat.add_zero, Nat.sub_zero, Nat.mod_eq_of_lt hi,
      runPrefix_zero, Nat.testBit_xor]
    generalize (rotFn k (if col then 3 else 1) key).testBit i = a
    generalize nm1.testBit i = b
    generalize nm2.testBit i = c
    cases a <;> cases b <;> cases c <;> decide
  | succ j ih =>
    intro i hi hwin
    set gap : ℕ := if col then 2 else 1
    have hgap0 : 0 < gap := by cases col <;> decide
    have hgapk : gap < k := by cases col <;> dsimp [gap] <;> omega
    have hjk : j * gap ≤ j * k := Nat.mul_le_mul_left j (Nat.le_of_lt hgapk)
    rw [runPrefix_succ, runPrefix_succ]
    unfold stepFn
    dsimp only
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    have hxor_iff :
        (xor (xor ((chiFn k (mixFn k gap (runPrefix k r masks col key nm1 j))).testBit i)
                  ((rotFn k (if col then 3 * (j + 1) + 1 else 2 * j) key).testBit i))
             ((masks (if col then r + j else j)).val.testBit i) =
         xor (xor ((chiFn k (mixFn k gap (runPrefix k r masks col key nm2 j))).testBit i)
                  ((rotFn k (if col then 3 * (j + 1) + 1 else 2 * j) key).testBit i))
             ((masks (if col then r + j else j)).val.testBit i)) ↔
        ((chiFn k (mixFn k gap (runPrefix k r masks col key nm1 j))).testBit i =
         (chiFn k (mixFn k gap (runPrefix k r masks col key nm2 j))).testBit i) := by
      generalize (chiFn k (mixFn k gap (runPrefix k r masks col key nm1 j))).testBit i = a
      generalize (chiFn k (mixFn k gap (runPrefix k r masks col key nm2 j))).testBit i = b
      generalize (rotFn k (if col then 3 * (j + 1) + 1 else 2 * j) key).testBit i = c
      generalize (masks (if col then r + j else j)).val.testBit i = d
      cases a <;> cases b <;> cases c <;> cases d <;> decide
    rw [hxor_iff]
    have hstep_iff :
        ((chiFn k (mixFn k gap (runPrefix k r masks col key nm1 j))).testBit i =
         (chiFn k (mixFn k gap (runPrefix k r masks col key nm2 j))).testBit i) ↔
        ((runPrefix k r masks col key nm1 j).testBit ((i + k - gap) % k) =
         (runPrefix k r masks col key nm2 j).testBit ((i + k - gap) % k)) := by
      apply chi_mix_pivot_iff hgap0 hgapk (runPrefix_lt masks col key nm1 hnm1 j)
        (runPrefix_lt masks col key nm2 hnm2 j) hi
      intro v hv1 hv2
      have hi' : (i + k - gap + v) % k < k := Nat.mod_lt _ (by omega)
      apply runPrefix_nm_agree hk masks col key nm1 nm2 hnm1 hnm2 j ((i + k - gap + v) % k) hi'
      intro w hw
      change w ≤ j * (2 + 2 * gap) at hw
      have hmod : ((i + k - gap + v) % k + j * k - j * gap + w) % k =
          (i + (j + 1) * k - (j + 1) * gap + (v + w)) % k := by
        have h1 : (i + k - gap + v) % k + j * k - j * gap + w =
            (i + k - gap + v) % k + (j * k - j * gap + w) := by omega
        have h2 : (i + k - gap + v) + (j * k - j * gap + w) =
            i + (j + 1) * k - (j + 1) * gap + (v + w) := by
          have hm1 : (j + 1) * k = j * k + k := Nat.succ_mul j k
          have hm2 : (j + 1) * gap = j * gap + gap := Nat.succ_mul j gap
          omega
        rw [h1, Nat.mod_add_mod, h2]
      rw [hmod]
      have hvw : v + w ≤ (j + 1) * (2 + 2 * gap) := by
        have hm : (j + 1) * (2 + 2 * gap) = j * (2 + 2 * gap) + (2 + 2 * gap) := Nat.succ_mul _ _
        omega
      exact hwin (v + w) (by omega) hvw
    rw [hstep_iff]
    have hi0 : (i + k - gap) % k < k := Nat.mod_lt _ (by omega)
    have hih := ih ((i + k - gap) % k) hi0 (by
      intro w hw1 hw2
      change w ≤ j * (2 + 2 * gap) at hw2
      have hmod : ((i + k - gap) % k + j * k - j * gap + w) % k =
          (i + (j + 1) * k - (j + 1) * gap + w) % k := by
        have h1 : (i + k - gap) % k + j * k - j * gap + w =
            (i + k - gap) % k + (j * k - j * gap + w) := by omega
        have h2 : (i + k - gap) + (j * k - j * gap + w) =
            i + (j + 1) * k - (j + 1) * gap + w := by
          have hm1 : (j + 1) * k = j * k + k := Nat.succ_mul j k
          have hm2 : (j + 1) * gap = j * gap + gap := Nat.succ_mul j gap
          omega
        rw [h1, Nat.mod_add_mod, h2]
      rw [hmod]
      have hw3 : w ≤ (j + 1) * (2 + 2 * gap) := by
        have hm : (j + 1) * (2 + 2 * gap) = j * (2 + 2 * gap) + (2 + 2 * gap) := Nat.succ_mul _ _
        omega
      exact hwin w hw1 hw3)
    rw [hih]
    have hmod0 : ((i + k - gap) % k + j * k - j * gap) % k =
        (i + (j + 1) * k - (j + 1) * gap) % k := by
      have h1 : (i + k - gap) % k + j * k - j * gap =
          (i + k - gap) % k + (j * k - j * gap) := by omega
      have h2 : (i + k - gap) + (j * k - j * gap) =
          i + (j + 1) * k - (j + 1) * gap := by
        have hm1 : (j + 1) * k = j * k + k := Nat.succ_mul j k
        have hm2 : (j + 1) * gap = j * gap + gap := Nat.succ_mul j gap
        omega
      rw [h1, Nat.mod_add_mod, h2]
    rw [hmod0]

lemma unitriangular_bijective {h : ℕ} (Phi : Fin (2 ^ h) → Fin (2 ^ h))
    (hstep : ∀ t < h, ∀ w1 w2 : Fin (2 ^ h),
      (∀ s, t < s → s < h → w1.val.testBit s = w2.val.testBit s) →
      ((Phi w1).val.testBit t = (Phi w2).val.testBit t ↔
        w1.val.testBit t = w2.val.testBit t)) :
    Function.Bijective Phi := by
  have hinj : Function.Injective Phi := by
    intro w1 w2 hEq
    by_contra hne
    have hval : w1.val ≠ w2.val := fun hv => hne (Fin.ext hv)
    let S := (Finset.range h).filter (fun t => w1.val.testBit t ≠ w2.val.testBit t)
    have hS : S.Nonempty := by
      by_contra hEmp
      rw [Finset.not_nonempty_iff_eq_empty] at hEmp
      apply hval
      apply eq_of_testBit_eq_lt w1.isLt w2.isLt
      intro t ht
      by_contra hbit
      have hmem : t ∈ S := by
        simp [S, Finset.mem_filter, Finset.mem_range, ht, hbit]
      rw [hEmp] at hmem
      exact Finset.notMem_empty t hmem
    let t := S.max' hS
    have ht_mem : t ∈ S := Finset.max'_mem S hS
    have ht_lt : t < h := by
      simp only [S, Finset.mem_filter, Finset.mem_range] at ht_mem
      exact ht_mem.1
    have ht_ne : w1.val.testBit t ≠ w2.val.testBit t := by
      simp only [S, Finset.mem_filter, Finset.mem_range] at ht_mem
      exact ht_mem.2
    have hhi : ∀ s, t < s → s < h → w1.val.testBit s = w2.val.testBit s := by
      intro s hts hsh
      by_contra hbit
      have hs_mem : s ∈ S := by
        simp [S, Finset.mem_filter, Finset.mem_range, hsh, hbit]
      have hle : s ≤ t := Finset.le_max' S s hs_mem
      omega
    have hiff := hstep t ht_lt w1 w2 hhi
    have hphi : (Phi w1).val.testBit t = (Phi w2).val.testBit t := by rw [hEq]
    exact ht_ne (hiff.mp hphi)
  exact hinj.bijective_of_finite

lemma bVal_bounds {r : ℕ} (hr : r ≤ 1 ∨ 4 ≤ r) :
    2 ≤ bVal r ∧ 6 * r ≤ bVal r := by
  unfold bVal
  rcases hr with hr1 | hr4
  · interval_cases r <;> decide
  · have h0 : r ≠ 0 := by omega
    have h1 : r ≠ 1 := by omega
    simp [h0, h1]
    omega

lemma word_map_bijective {k r h : ℕ} (hh : 0 < h) (hr : r ≤ 1 ∨ 4 ≤ r) (hb : h + bVal r ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key : ℕ) (base : Fin (2 ^ k)) :
    let gap : ℕ := if col then 2 else 1
    Function.Bijective (fun word : Fin (2 ^ h) =>
      (⟨runPrefix k r masks col key (nameFn k r h gap base word) r >>> (k - h),
        shr_lt_two_pow
          (runPrefix_lt masks col key _ (nameFn_lt (by
            have hbb := bVal_bounds hr
            cases col <;> dsimp [gap] <;> omega) base word) r)
          (by have hbb := bVal_bounds hr; omega)⟩ : Fin (2 ^ h))) := by
  intro gap
  have hbb := bVal_bounds hr
  have hk3 : 3 ≤ k := by omega
  have hgap_le : gap ≤ 2 := by cases col <;> decide
  have h6r : r * (2 + 2 * gap) ≤ bVal r := by
    have h1 : 2 + 2 * gap ≤ 6 := by omega
    have h2 : r * (2 + 2 * gap) ≤ r * 6 := Nat.mul_le_mul_left r h1
    omega
  have hgr_le : gap * r ≤ k - h := by
    have h1 : gap * r ≤ 2 * r := Nat.mul_le_mul_right r hgap_le
    omega
  have hlo_add : k - h - gap * r + h ≤ k := by omega
  apply unitriangular_bijective
  intro t ht w1 w2 hhi
  dsimp only
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  have hi : k - h + t < k := by omega
  have hnm1 : nameFn k r h gap base w1 < 2 ^ k := nameFn_lt hlo_add base w1
  have hnm2 : nameFn k r h gap base w2 < 2 ^ k := nameFn_lt hlo_add base w2
  have hpiv := @runPrefix_nm_pivot_iff k r hk3 masks col key _ _ hnm1 hnm2 r (k - h + t) hi (by
    intro u hu1 hu2
    change u ≤ r * (2 + 2 * gap) at hu2
    have hidx : (k - h + t + r * k - r * gap + u) % k = (k - h - gap * r + t + u) % k := by
      have hrg : r * gap = gap * r := Nat.mul_comm r gap
      have h1 : k - h + t + r * k - r * gap + u = (k - h - gap * r + t + u) + r * k := by omega
      rw [h1, Nat.add_mul_mod_self_right]
    rw [hidx, nameFn_testBit_all, nameFn_testBit_all]
    set lo := k - h - gap * r
    by_cases htu : t + u < h
    · have hlt : lo + t + u < k := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have hin : lo ≤ lo + t + u ∧ lo + t + u < lo + h := by omega
      simp only [hin.1, hin.2, and_self, ↓reduceIte]
      have hsub : lo + t + u - lo = t + u := by omega
      rw [hsub]
      exact hhi (t + u) (by omega) htu
    · by_cases hlt : lo + t + u < k
      · rw [Nat.mod_eq_of_lt hlt]
        have hout : ¬ (lo ≤ lo + t + u ∧ lo + t + u < lo + h) := by omega
        simp [hout]
      · have hwrap : lo + t + u - k < lo := by
          have hrg : r * (2 + 2 * gap) = r * (2 + gap) + gap * r := by
            cases col <;> dsimp [gap] <;> omega
          omega
        have hlt2 : lo + t + u - k < k := by omega
        have hmod2 : (lo + t + u) % k = lo + t + u - k := by
          have h1 : lo + t + u = (lo + t + u - k) + k := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
        rw [hmod2]
        have hout : ¬ (lo ≤ lo + t + u - k ∧ lo + t + u - k < lo + h) := by omega
        simp [hout])
  rw [hpiv]
  have hidx0 : (k - h + t + r * k - r * gap) % k = k - h - gap * r + t := by
    have hrg : r * gap = gap * r := Nat.mul_comm r gap
    have h1 : k - h + t + r * k - r * gap = (k - h - gap * r + t) + r * k := by omega
    rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [hidx0, nameFn_testBit_all, nameFn_testBit_all]
  set lo := k - h - gap * r
  have hin0 : lo ≤ lo + t ∧ lo + t < lo + h := by omega
  simp only [hin0.1, hin0.2, and_self, ↓reduceIte]
  have hsub0 : lo + t - lo = t := by omega
  rw [hsub0]

def keyL (col : Bool) (j : ℕ) : ℕ :=
  if col then max (2 * j + 3) (3 * j + 1) else max (j + 1) (2 * j - 2)

def keyW (col : Bool) (j : ℕ) : ℕ :=
  if col then keyL true j + 4 * j - 3 else keyL false j + 3 * j - 1

lemma runPrefix_key_agree {k r : ℕ} (hk : 3 ≤ k) (masks : ℕ → Fin (2 ^ k)) (col : Bool)
    (nm : ℕ) (hnm : nm < 2 ^ k) (key1 key2 : ℕ) (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k) :
    ∀ j, (∀ m < j, (if col then 3 * (m + 1) + 1 else 2 * m) < k) →
      keyL col j ≤ k →
      ∀ i < k,
      (∀ u ≤ keyW col j,
        key1.testBit ((i + 2 * k - keyL col j + u) % k) =
        key2.testBit ((i + 2 * k - keyL col j + u) % k)) →
      (runPrefix k r masks col key1 nm j).testBit i =
      (runPrefix k r masks col key2 nm j).testBit i := by
  intro j
  induction j with
  | zero =>
    intro _ _ i hi hwin
    rw [runPrefix_zero, runPrefix_zero, Nat.testBit_xor, Nat.testBit_xor]
    congr 1
    rw [rotFn_testBit (by omega) hk1 _ i hi, rotFn_testBit (by omega) hk2 _ i hi]
    have h0 := hwin 0 (Nat.zero_le _)
    cases col
    · have hL0 : keyL false 0 = 1 := by decide
      rw [hL0, Nat.add_zero] at h0
      simp only [Bool.false_eq_true, ↓reduceIte]
      have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      have h2 : i + 2 * k - 1 = (i + k - 1) + k := by omega
      rw [h2, Nat.add_mod_right] at h0
      rw [h1m]
      exact h0
    · have hL0 : keyL true 0 = 3 := by decide
      rw [hL0, Nat.add_zero] at h0
      simp only [↓reduceIte]
      by_cases hk3 : 3 < k
      · have hm : 3 % k = 3 := Nat.mod_eq_of_lt hk3
        have h2 : i + 2 * k - 3 = (i + k - 3) + k := by omega
        rw [h2, Nat.add_mod_right] at h0
        rw [hm]
        exact h0
      · have hkeq : k = 3 := by omega
        subst hkeq
        simp only [Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
        have h2 : (i + 2 * 3 - 3) % 3 = i := by
          have h3 : i + 2 * 3 - 3 = i + 3 := by omega
          rw [h3, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
        rw [h2] at h0
        exact h0
  | succ j ih =>
    intro hstep_lt hL_le i hi hwin
    set gap : ℕ := if col then 2 else 1
    have hgap0 : 0 < gap := by cases col <;> decide
    have hgapk : gap < k := by cases col <;> dsimp [gap] <;> omega
    have hL_step : keyL col j + gap ≤ keyL col (j + 1) := by
      cases col <;> dsimp [gap, keyL] <;> omega
    have hL_j_le : keyL col j ≤ k := by omega
    have hW_step : keyL col (j + 1) + keyW col j + (2 + gap) ≤ keyL col j + keyW col (j + 1) := by
      cases col <;> dsimp [gap, keyL, keyW] <;> omega
    have hs_le : (if col then 3 * (j + 1) + 1 else 2 * j) ≤ keyL col (j + 1) := by
      cases col <;> dsimp [keyL] <;> omega
    have hs_in : keyL col (j + 1) - (if col then 3 * (j + 1) + 1 else 2 * j) ≤ keyW col (j + 1) := by
      cases col <;> dsimp [keyL, keyW] <;> omega
    have hs_lt : (if col then 3 * (j + 1) + 1 else 2 * j) < k := hstep_lt j (Nat.lt_succ_self j)
    rw [runPrefix_succ, runPrefix_succ]
    unfold stepFn
    dsimp only
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    have hchi :
        (chiFn k (mixFn k gap (runPrefix k r masks col key1 nm j))).testBit i =
        (chiFn k (mixFn k gap (runPrefix k r masks col key2 nm j))).testBit i := by
      apply chi_mix_agree hgap0 hgapk (runPrefix_lt masks col key1 nm hnm j)
        (runPrefix_lt masks col key2 nm hnm j) hi
      intro v hv
      have hi' : (i + k - gap + v) % k < k := Nat.mod_lt _ (by omega)
      apply ih (fun m hm => hstep_lt m (Nat.lt_trans hm (Nat.lt_succ_self j))) hL_j_le _ hi'
      intro w hw
      set u := (keyL col (j + 1) - (keyL col j + gap)) + (v + w)
      have hu : u ≤ keyW col (j + 1) := by omega
      have hmod : ((i + k - gap + v) % k + 2 * k - keyL col j + w) % k =
          (i + 2 * k - keyL col (j + 1) + u) % k := by
        have h1 : (i + k - gap + v) % k + 2 * k - keyL col j + w =
            (i + k - gap + v) % k + (2 * k - keyL col j + w) := by omega
        have h2 : (i + k - gap + v) + (2 * k - keyL col j + w) =
            (i + 2 * k - keyL col (j + 1) + u) + k := by omega
        rw [h1, Nat.mod_add_mod, h2, Nat.add_mod_right]
      rw [hmod]
      exact hwin u hu
    have hrot :
        (rotFn k (if col then 3 * (j + 1) + 1 else 2 * j) key1).testBit i =
        (rotFn k (if col then 3 * (j + 1) + 1 else 2 * j) key2).testBit i := by
      rw [rotFn_testBit (by omega) hk1 _ i hi, rotFn_testBit (by omega) hk2 _ i hi]
      rw [Nat.mod_eq_of_lt hs_lt]
      set s := if col then 3 * (j + 1) + 1 else 2 * j
      set u := keyL col (j + 1) - s
      have hmod : (i + k - s) % k = (i + 2 * k - keyL col (j + 1) + u) % k := by
        have h1 : i + 2 * k - keyL col (j + 1) + u = (i + k - s) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hmod]
      exact hwin u hs_in
    rw [hchi, hrot]

def wStart (k r h : ℕ) : ℕ :=
  if r = 0 then 2 * k - h - 3
  else if r = 1 then 2 * k - h - 5
  else 2 * k - h - (3 * r + 1)

def pStart (k r h : ℕ) (col : Bool) : ℕ :=
  if r = 0 then (if col then 2 * k - h - 3 else 2 * k - h - 1)
  else if r = 1 then (if col then 2 * k - h - 5 else 2 * k - h - 2)
  else (if col then 2 * k - h - (3 * r + 1) else 2 * k - h - (2 * r - 2))

lemma run_key_window {k r h : ℕ} (hh : 0 < h) (hr : r ≤ 1 ∨ 4 ≤ r) (hb : h + bVal r ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (col : Bool) (nm : ℕ) (hnm : nm < 2 ^ k)
    (key1 key2 : ℕ) (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k)
    (hwin : ∀ n < h + bVal r,
      key1.testBit ((wStart k r h + n) % k) = key2.testBit ((wStart k r h + n) % k)) :
    runPrefix k r masks col key1 nm r >>> (k - h) =
    runPrefix k r masks col key2 nm r >>> (k - h) := by
  have hbb := bVal_bounds hr
  have hk3 : 3 ≤ k := by omega
  apply eq_of_testBit_eq_lt
    (shr_lt_two_pow (runPrefix_lt masks col key1 nm hnm r) (by omega))
    (shr_lt_two_pow (runPrefix_lt masks col key2 nm hnm r) (by omega))
  intro t ht
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  have hi : k - h + t < k := by omega
  have hstep_lt : ∀ m < r, (if col then 3 * (m + 1) + 1 else 2 * m) < k := by
    intro m hm
    rcases hr with hr1 | hr4
    · interval_cases r
      · omega
      · unfold bVal at hb
        simp only [Nat.one_ne_zero, ↓reduceIte] at hb
        cases col <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
    · have h0 : r ≠ 0 := by omega
      have h1 : r ≠ 1 := by omega
      unfold bVal at hb
      simp only [h0, h1, ↓reduceIte] at hb
      cases col <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hLr : keyL col r ≤ k := by
    rcases hr with hr1 | hr4
    · interval_cases r
      · cases col <;> simp only [keyL, Bool.false_eq_true, ↓reduceIte] <;> omega
      · unfold bVal at hb
        simp only [Nat.one_ne_zero, ↓reduceIte] at hb
        cases col <;> simp only [keyL, Bool.false_eq_true, ↓reduceIte] <;> omega
    · have h0 : r ≠ 0 := by omega
      have h1 : r ≠ 1 := by omega
      unfold bVal at hb
      simp only [h0, h1, ↓reduceIte] at hb
      cases col <;> simp only [keyL, Bool.false_eq_true, ↓reduceIte] <;> omega
  apply runPrefix_key_agree hk3 masks col nm hnm key1 key2 hk1 hk2 r hstep_lt hLr (k - h + t) hi
  intro u hu
  rcases hr with hr1 | hr4
  · interval_cases r
    · unfold bVal at hb hwin
      simp only [↓reduceIte] at hb hwin
      unfold wStart at hwin
      simp only [↓reduceIte] at hwin
      cases col
      · have hL0 : keyL false 0 = 1 := by decide
        have hW0 : keyW false 0 = 0 := by decide
        rw [hL0]
        rw [hW0] at hu
        have hu0 : u = 0 := by omega
        subst hu0
        have hmod : (k - h + t + 2 * k - 1 + 0) % k = (2 * k - h - 3 + (t + 2)) % k := by
          have h1 : k - h + t + 2 * k - 1 + 0 = (2 * k - h - 3 + (t + 2)) + k := by omega
          rw [h1, Nat.add_mod_right]
        rw [hmod]
        exact hwin (t + 2) (by omega)
      · have hL0 : keyL true 0 = 3 := by decide
        have hW0 : keyW true 0 = 0 := by decide
        rw [hL0]
        rw [hW0] at hu
        have hu0 : u = 0 := by omega
        subst hu0
        have hmod : (k - h + t + 2 * k - 3 + 0) % k = (2 * k - h - 3 + t) % k := by
          have h1 : k - h + t + 2 * k - 3 + 0 = (2 * k - h - 3 + t) + k := by omega
          rw [h1, Nat.add_mod_right]
        rw [hmod]
        exact hwin t (by omega)
    · unfold bVal at hb hwin
      simp only [Nat.one_ne_zero, ↓reduceIte] at hb hwin
      unfold wStart at hwin
      simp only [Nat.one_ne_zero, ↓reduceIte] at hwin
      cases col
      · have hL1 : keyL false 1 = 2 := by decide
        have hW1 : keyW false 1 = 4 := by decide
        rw [hL1]
        rw [hW1] at hu
        have hmod : (k - h + t + 2 * k - 2 + u) % k =
            (2 * k - h - 5 + (t + u + 3)) % k := by
          have h1 : k - h + t + 2 * k - 2 + u =
              (2 * k - h - 5 + (t + u + 3)) + k := by omega
          rw [h1, Nat.add_mod_right]
        rw [hmod]
        exact hwin (t + u + 3) (by omega)
      · have hL1 : keyL true 1 = 5 := by decide
        have hW1 : keyW true 1 = 6 := by decide
        rw [hL1]
        rw [hW1] at hu
        have hmod : (k - h + t + 2 * k - 5 + u) % k =
            (2 * k - h - 5 + (t + u)) % k := by
          have h1 : k - h + t + 2 * k - 5 + u =
              (2 * k - h - 5 + (t + u)) + k := by omega
          rw [h1, Nat.add_mod_right]
        rw [hmod]
        exact hwin (t + u) (by omega)
  · have h0 : r ≠ 0 := by omega
    have h1 : r ≠ 1 := by omega
    unfold bVal at hb hwin
    simp only [h0, h1, ↓reduceIte] at hb hwin
    unfold wStart at hwin
    simp only [h0, h1, ↓reduceIte] at hwin
    cases col
    · dsimp [keyL, keyW] at hu ⊢
      have hmod : (k - h + t + 2 * k - max (r + 1) (2 * r - 2) + u) % k =
          (2 * k - h - (3 * r + 1) + (t + u + r + 3)) % k := by
        have h1 : k - h + t + 2 * k - max (r + 1) (2 * r - 2) + u =
            (2 * k - h - (3 * r + 1) + (t + u + r + 3)) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hmod]
      exact hwin (t + u + r + 3) (by omega)
    · dsimp [keyL, keyW] at hu ⊢
      have hmod : (k - h + t + 2 * k - max (2 * r + 3) (3 * r + 1) + u) % k =
          (2 * k - h - (3 * r + 1) + (t + u)) % k := by
        have h1 : k - h + t + 2 * k - max (2 * r + 3) (3 * r + 1) + u =
            (2 * k - h - (3 * r + 1) + (t + u)) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hmod]
      exact hwin (t + u) (by omega)

lemma run_key_pivot_iff {k r h : ℕ} (hh : 0 < h) (hr : r ≤ 1 ∨ 4 ≤ r) (hb : h + bVal r ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (col : Bool) (nm : ℕ) (hnm : nm < 2 ^ k)
    (key1 key2 : ℕ) (hk1 : key1 < 2 ^ k) (hk2 : key2 < 2 ^ k)
    (t : ℕ) (ht : t < h)
    (hwin : ∀ u, 1 ≤ u → u ≤ bVal r →
      key1.testBit ((pStart k r h col + t + u) % k) =
      key2.testBit ((pStart k r h col + t + u) % k)) :
    ((runPrefix k r masks col key1 nm r).testBit (k - h + t) =
     (runPrefix k r masks col key2 nm r).testBit (k - h + t)) ↔
      (key1.testBit ((pStart k r h col + t) % k) =
       key2.testBit ((pStart k r h col + t) % k)) := by
  have hbb := bVal_bounds hr
  have hk3 : 3 ≤ k := by omega
  have hi : k - h + t < k := by omega
  rcases hr with hr1 | hr4
  · interval_cases r
    · unfold bVal at hb hwin
      simp only [↓reduceIte] at hb hwin
      unfold pStart
      simp only [↓reduceIte]
      rw [runPrefix_zero, runPrefix_zero, Nat.testBit_xor, Nat.testBit_xor]
      have hxor :
          (xor ((rotFn k (if col then 3 else 1) key1).testBit (k - h + t)) (nm.testBit (k - h + t)) =
           xor ((rotFn k (if col then 3 else 1) key2).testBit (k - h + t)) (nm.testBit (k - h + t))) ↔
          ((rotFn k (if col then 3 else 1) key1).testBit (k - h + t) =
           (rotFn k (if col then 3 else 1) key2).testBit (k - h + t)) := by
        generalize (rotFn k (if col then 3 else 1) key1).testBit (k - h + t) = a
        generalize (rotFn k (if col then 3 else 1) key2).testBit (k - h + t) = b
        generalize nm.testBit (k - h + t) = c
        cases a <;> cases b <;> cases c <;> decide
      rw [hxor, rotFn_testBit (by omega) hk1 _ _ hi, rotFn_testBit (by omega) hk2 _ _ hi]
      cases col
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hm1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hmod : (k - h + t + k - 1) % k = (2 * k - h - 1 + t) % k := by
          congr 1; omega
        rw [hm1, hmod]
      · simp only [↓reduceIte]
        by_cases hkgt : 3 < k
        · have hm3 : 3 % k = 3 := Nat.mod_eq_of_lt hkgt
          have hmod : (k - h + t + k - 3) % k = (2 * k - h - 3 + t) % k := by
            congr 1; omega
          rw [hm3, hmod]
        · have hkeq : k = 3 := by omega
          subst hkeq
          have hmod : (3 - h + t + 3 - 3 % 3) % 3 = (2 * 3 - h - 3 + t) % 3 := by
            have h1 : 3 - h + t + 3 - 3 % 3 = (2 * 3 - h - 3 + t) + 3 := by omega
            rw [h1, Nat.add_mod_right]
          rw [hmod]
    · unfold bVal at hb hwin
      simp only [Nat.one_ne_zero, ↓reduceIte] at hb hwin
      unfold pStart at hwin ⊢
      simp only [Nat.one_ne_zero, ↓reduceIte] at hwin ⊢
      set gap : ℕ := if col then 2 else 1
      have hgap0 : 0 < gap := by cases col <;> decide
      have hgapk : gap < k := by cases col <;> dsimp [gap] <;> omega
      rw [runPrefix_succ, runPrefix_succ]
      unfold stepFn
      dsimp only
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
      have hrot_eq :
          (rotFn k (if col then 3 * (0 + 1) + 1 else 2 * 0) key1).testBit (k - h + t) =
          (rotFn k (if col then 3 * (0 + 1) + 1 else 2 * 0) key2).testBit (k - h + t) := by
        rw [rotFn_testBit (by omega) hk1 _ _ hi, rotFn_testBit (by omega) hk2 _ _ hi]
        cases col
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.mul_zero, Nat.zero_mod, Nat.sub_zero]
          have hmod : (k - h + t + k) % k = (2 * k - h - 2 + t + 2) % k := by
            congr 1; omega
          rw [hmod]
          exact hwin 2 (by omega) (by omega)
        · simp only [↓reduceIte]
          have hm4 : (3 * (0 + 1) + 1) % k = 4 := Nat.mod_eq_of_lt (by omega)
          have hmod : (k - h + t + k - 4) % k = (2 * k - h - 5 + t + 1) % k := by
            congr 1; omega
          rw [hm4, hmod]
          exact hwin 1 (by omega) (by omega)
      rw [hrot_eq]
      have hxor :
          (xor (xor ((chiFn k (mixFn k (if col then 2 else 1) (runPrefix k 1 masks col key1 nm 0))).testBit (k - h + t))
                    ((rotFn k (if col then 3 * (0 + 1) + 1 else 2 * 0) key2).testBit (k - h + t)))
               ((masks (if col then 1 + 0 else 0)).val.testBit (k - h + t)) =
           xor (xor ((chiFn k (mixFn k (if col then 2 else 1) (runPrefix k 1 masks col key2 nm 0))).testBit (k - h + t))
                    ((rotFn k (if col then 3 * (0 + 1) + 1 else 2 * 0) key2).testBit (k - h + t)))
               ((masks (if col then 1 + 0 else 0)).val.testBit (k - h + t))) ↔
          ((chiFn k (mixFn k gap (runPrefix k 1 masks col key1 nm 0))).testBit (k - h + t) =
           (chiFn k (mixFn k gap (runPrefix k 1 masks col key2 nm 0))).testBit (k - h + t)) := by
        dsimp only [gap]
        generalize (chiFn k (mixFn k (if col then 2 else 1) (runPrefix k 1 masks col key1 nm 0))).testBit (k - h + t) = a
        generalize (chiFn k (mixFn k (if col then 2 else 1) (runPrefix k 1 masks col key2 nm 0))).testBit (k - h + t) = b
        generalize (rotFn k (if col then 3 * (0 + 1) + 1 else 2 * 0) key2).testBit (k - h + t) = c
        generalize (masks (if col then 1 + 0 else 0)).val.testBit (k - h + t) = d
        cases a <;> cases b <;> cases c <;> cases d <;> decide
      rw [hxor]
      rw [chi_mix_pivot_iff hgap0 hgapk (runPrefix_lt masks col key1 nm hnm 0)
            (runPrefix_lt masks col key2 nm hnm 0) hi (by
        intro u hu1 hu2
        have hi' : (k - h + t + k - gap + u) % k < k := Nat.mod_lt _ (by omega)
        rw [runPrefix_zero, runPrefix_zero, Nat.testBit_xor, Nat.testBit_xor]
        congr 1
        rw [rotFn_testBit (by omega) hk1 _ _ hi', rotFn_testBit (by omega) hk2 _ _ hi']
        cases col
        · dsimp [gap] at hu2 ⊢
          have hm1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
          rw [hm1]
          have hmod : ((k - h + t + k - 1 + u) % k + k - 1) % k =
              (2 * k - h - 2 + t + u) % k := by
            have h1 : (k - h + t + k - 1 + u) % k + k - 1 =
                (k - h + t + k - 1 + u) % k + (k - 1) := by omega
            have h2 : (k - h + t + k - 1 + u) + (k - 1) = (2 * k - h - 2 + t + u) + k := by omega
            rw [h1, Nat.mod_add_mod, h2, Nat.add_mod_right]
          rw [hmod]
          exact hwin u hu1 (by omega)
        · dsimp [gap] at hu2 ⊢
          have hm3 : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
          rw [hm3]
          have hmod : ((k - h + t + k - 2 + u) % k + k - 3) % k =
              (2 * k - h - 5 + t + u) % k := by
            have h1 : (k - h + t + k - 2 + u) % k + k - 3 =
                (k - h + t + k - 2 + u) % k + (k - 3) := by omega
            have h2 : (k - h + t + k - 2 + u) + (k - 3) = (2 * k - h - 5 + t + u) + k := by omega
            rw [h1, Nat.mod_add_mod, h2, Nat.add_mod_right]
          rw [hmod]
          exact hwin u hu1 (by omega))]
      have hi0 : (k - h + t + k - gap) % k < k := Nat.mod_lt _ (by omega)
      rw [runPrefix_zero, runPrefix_zero, Nat.testBit_xor, Nat.testBit_xor]
      have hxor0 :
          (xor ((rotFn k (if col then 3 else 1) key1).testBit ((k - h + t + k - gap) % k))
               (nm.testBit ((k - h + t + k - gap) % k)) =
           xor ((rotFn k (if col then 3 else 1) key2).testBit ((k - h + t + k - gap) % k))
               (nm.testBit ((k - h + t + k - gap) % k))) ↔
          ((rotFn k (if col then 3 else 1) key1).testBit ((k - h + t + k - gap) % k) =
           (rotFn k (if col then 3 else 1) key2).testBit ((k - h + t + k - gap) % k)) := by
        generalize (rotFn k (if col then 3 else 1) key1).testBit ((k - h + t + k - gap) % k) = a
        generalize (rotFn k (if col then 3 else 1) key2).testBit ((k - h + t + k - gap) % k) = b
        generalize nm.testBit ((k - h + t + k - gap) % k) = c
        cases a <;> cases b <;> cases c <;> decide
      rw [hxor0, rotFn_testBit (by omega) hk1 _ _ hi0, rotFn_testBit (by omega) hk2 _ _ hi0]
      cases col
      · dsimp [gap]
        have hm1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        rw [hm1]
        have hmod : ((k - h + t + k - 1) % k + k - 1) % k = (2 * k - h - 2 + t) % k := by
          have h1 : (k - h + t + k - 1) % k + k - 1 = (k - h + t + k - 1) % k + (k - 1) := by omega
          have h2 : (k - h + t + k - 1) + (k - 1) = (2 * k - h - 2 + t) + k := by omega
          rw [h1, Nat.mod_add_mod, h2, Nat.add_mod_right]
        rw [hmod]
      · dsimp [gap]
        have hm3 : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
        rw [hm3]
        have hmod : ((k - h + t + k - 2) % k + k - 3) % k = (2 * k - h - 5 + t) % k := by
          have h1 : (k - h + t + k - 2) % k + k - 3 = (k - h + t + k - 2) % k + (k - 3) := by omega
          have h2 : (k - h + t + k - 2) + (k - 3) = (2 * k - h - 5 + t) + k := by omega
          rw [h1, Nat.mod_add_mod, h2, Nat.add_mod_right]
        rw [hmod]
  · have h0 : r ≠ 0 := by omega
    have h1 : r ≠ 1 := by omega
    unfold bVal at hb hwin
    simp only [h0, h1, ↓reduceIte] at hb hwin
    unfold pStart at hwin ⊢
    simp only [h0, h1, ↓reduceIte] at hwin ⊢
    set gap : ℕ := if col then 2 else 1
    have hgap0 : 0 < gap := by cases col <;> decide
    have hgapk : gap < k := by cases col <;> dsimp [gap] <;> omega
    have hr_eq : r = (r - 1) + 1 := by omega
    have hstep_r : ∀ key, runPrefix k r masks col key nm r =
        stepFn k r masks col key (runPrefix k r masks col key nm (r - 1)) (r - 1) := by
      intro key
      nth_rw 2 [hr_eq]
      exact runPrefix_succ k r masks col key nm (r - 1)
    rw [hstep_r key1, hstep_r key2]
    unfold stepFn
    dsimp only
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    have hchi_eq :
        (chiFn k (mixFn k (if col then 2 else 1) (runPrefix k r masks col key1 nm (r - 1)))).testBit (k - h + t) =
        (chiFn k (mixFn k (if col then 2 else 1) (runPrefix k r masks col key2 nm (r - 1)))).testBit (k - h + t) := by
      change (chiFn k (mixFn k gap (runPrefix k r masks col key1 nm (r - 1)))).testBit (k - h + t) =
             (chiFn k (mixFn k gap (runPrefix k r masks col key2 nm (r - 1)))).testBit (k - h + t)
      apply chi_mix_agree hgap0 hgapk (runPrefix_lt masks col key1 nm hnm (r - 1))
        (runPrefix_lt masks col key2 nm hnm (r - 1)) hi
      intro v hv
      have hi' : (k - h + t + k - gap + v) % k < k := Nat.mod_lt _ (by omega)
      have hstep_lt : ∀ m < r - 1, (if col then 3 * (m + 1) + 1 else 2 * m) < k := by
        intro m hm
        cases col <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
      have hLr1 : keyL col (r - 1) ≤ k := by
        cases col <;> simp only [keyL, Bool.false_eq_true, ↓reduceIte] <;> omega
      apply runPrefix_key_agree hk3 masks col nm hnm key1 key2 hk1 hk2 (r - 1) hstep_lt hLr1 _ hi'
      intro w hw
      cases col
      · dsimp [gap, keyL, keyW] at hv hw ⊢
        set u := 1 + v + w
        have hmod : ((k - h + t + k - 1 + v) % k + 2 * k - max (r - 1 + 1) (2 * (r - 1) - 2) + w) % k =
            (2 * k - h - (2 * r - 2) + t + u) % k := by
          have h1 : (k - h + t + k - 1 + v) % k + 2 * k - max (r - 1 + 1) (2 * (r - 1) - 2) + w =
              (k - h + t + k - 1 + v) % k + (2 * k - max (r - 1 + 1) (2 * (r - 1) - 2) + w) := by omega
          have h2 : (k - h + t + k - 1 + v) + (2 * k - max (r - 1 + 1) (2 * (r - 1) - 2) + w) =
              (2 * k - h - (2 * r - 2) + t + u) + 2 * k := by omega
          rw [h1, Nat.mod_add_mod, h2, Nat.add_mul_mod_self_right]
        rw [hmod]
        exact hwin u (by omega) (by omega)
      · dsimp [gap, keyL, keyW] at hv hw ⊢
        set u := 1 + v + w
        have hmod : ((k - h + t + k - 2 + v) % k + 2 * k - max (2 * (r - 1) + 3) (3 * (r - 1) + 1) + w) % k =
            (2 * k - h - (3 * r + 1) + t + u) % k := by
          have h1 : (k - h + t + k - 2 + v) % k + 2 * k - max (2 * (r - 1) + 3) (3 * (r - 1) + 1) + w =
              (k - h + t + k - 2 + v) % k + (2 * k - max (2 * (r - 1) + 3) (3 * (r - 1) + 1) + w) := by omega
          have h2 : (k - h + t + k - 2 + v) + (2 * k - max (2 * (r - 1) + 3) (3 * (r - 1) + 1) + w) =
              (2 * k - h - (3 * r + 1) + t + u) + 2 * k := by omega
          rw [h1, Nat.mod_add_mod, h2, Nat.add_mul_mod_self_right]
        rw [hmod]
        exact hwin u (by omega) (by omega)
    rw [hchi_eq]
    have hxor :
        (xor (xor ((chiFn k (mixFn k (if col then 2 else 1) (runPrefix k r masks col key2 nm (r - 1)))).testBit (k - h + t))
                  ((rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) key1).testBit (k - h + t)))
             ((masks (if col then r + (r - 1) else r - 1)).val.testBit (k - h + t)) =
         xor (xor ((chiFn k (mixFn k (if col then 2 else 1) (runPrefix k r masks col key2 nm (r - 1)))).testBit (k - h + t))
                  ((rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) key2).testBit (k - h + t)))
             ((masks (if col then r + (r - 1) else r - 1)).val.testBit (k - h + t))) ↔
        ((rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) key1).testBit (k - h + t) =
         (rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) key2).testBit (k - h + t)) := by
      generalize (chiFn k (mixFn k (if col then 2 else 1) (runPrefix k r masks col key2 nm (r - 1)))).testBit (k - h + t) = a
      generalize (rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) key1).testBit (k - h + t) = b
      generalize (rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) key2).testBit (k - h + t) = c
      generalize (masks (if col then r + (r - 1) else r - 1)).val.testBit (k - h + t) = d
      cases a <;> cases b <;> cases c <;> cases d <;> decide
    rw [hxor, rotFn_testBit (by omega) hk1 _ _ hi, rotFn_testBit (by omega) hk2 _ _ hi]
    cases col
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hm : (2 * (r - 1)) % k = 2 * r - 2 := by
        have heq : 2 * (r - 1) = 2 * r - 2 := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
      have hmod : (k - h + t + k - (2 * r - 2)) % k = (2 * k - h - (2 * r - 2) + t) % k := by
        congr 1; omega
      rw [hm, hmod]
    · simp only [↓reduceIte]
      have hm : (3 * (r - 1 + 1) + 1) % k = 3 * r + 1 := by
        have heq : 3 * (r - 1 + 1) + 1 = 3 * r + 1 := by omega
        rw [heq, Nat.mod_eq_of_lt (by omega)]
      have hmod : (k - h + t + k - (3 * r + 1)) % k = (2 * k - h - (3 * r + 1) + t) % k := by
        congr 1; omega
      rw [hm, hmod]

def bitsToNat : ∀ {m : ℕ}, (Fin m → Bool) → ℕ
  | 0, _ => 0
  | _ + 1, f => (f 0).toNat + 2 * bitsToNat (fun i => f i.succ)

lemma bitsToNat_lt : ∀ {m : ℕ} (f : Fin m → Bool), bitsToNat f < 2 ^ m
  | 0, _ => by simp [bitsToNat]
  | m + 1, f => by
    unfold bitsToNat
    have ih := bitsToNat_lt (fun i : Fin m => f i.succ)
    have hb : (f 0).toNat ≤ 1 := by cases f 0 <;> decide
    rw [Nat.pow_succ]
    omega

lemma bitsToNat_testBit : ∀ {m : ℕ} (f : Fin m → Bool) (i : Fin m),
    (bitsToNat f).testBit i.val = f i
  | 0, _, i => Fin.elim0 i
  | m + 1, f, i => by
    refine Fin.cases ?_ ?_ i
    · unfold bitsToNat
      simp only [Fin.val_zero, Nat.testBit_zero]
      cases f 0 <;> simp [Nat.add_mul_mod_self_left]
    · intro j
      unfold bitsToNat
      rw [Fin.val_succ, Nat.testBit_succ]
      have hdiv : ((f 0).toNat + 2 * bitsToNat (fun l : Fin m => f l.succ)) / 2 =
          bitsToNat (fun l : Fin m => f l.succ) := by
        rw [Nat.add_mul_div_left _ _ (by decide)]
        have hz : (f 0).toNat / 2 = 0 := by cases f 0 <;> decide
        omega
      rw [hdiv]
      exact bitsToNat_testBit (fun l : Fin m => f l.succ) j

def finPowEquiv (m : ℕ) : Fin (2 ^ m) ≃ (Fin m → Bool) where
  toFun x i := x.val.testBit i.val
  invFun f := ⟨bitsToNat f, bitsToNat_lt f⟩
  left_inv x := by
    apply Fin.ext
    dsimp only
    apply eq_of_testBit_eq_lt (bitsToNat_lt _) x.isLt
    intro i hi
    exact bitsToNat_testBit (fun j : Fin m => x.val.testBit j.val) ⟨i, hi⟩
  right_inv f := by
    funext i
    dsimp only
    exact bitsToNat_testBit f i

def shiftPerm (k p0 : ℕ) (hk : 0 < k) : Fin k ≃ Fin k where
  toFun i := ⟨(p0 + i.val) % k, Nat.mod_lt _ hk⟩
  invFun j := ⟨(j.val + k - p0 % k) % k, Nat.mod_lt _ hk⟩
  left_inv i := by
    apply Fin.ext
    dsimp only
    have hp : p0 % k < k := Nat.mod_lt p0 hk
    have hdiv : k * (p0 / k) + p0 % k = p0 := Nat.div_add_mod p0 k
    have h1 : (p0 + i.val) % k + k - p0 % k = (p0 + i.val) % k + (k - p0 % k) := by omega
    have h2 : (p0 + i.val) + (k - p0 % k) = i.val + k * (p0 / k + 1) := by
      have hmul : k * (p0 / k + 1) = k * (p0 / k) + k := by rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [h1, Nat.mod_add_mod, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
  right_inv j := by
    apply Fin.ext
    dsimp only
    have hp : p0 % k < k := Nat.mod_lt p0 hk
    have hdiv : k * (p0 / k) + p0 % k = p0 := Nat.div_add_mod p0 k
    have h2 : p0 + (j.val + k - p0 % k) = j.val + k * (p0 / k + 1) := by
      have hmul : k * (p0 / k + 1) = k * (p0 / k) + k := by rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [Nat.add_mod_mod, h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]

def bitsSplit (k m : ℕ) (hm : m ≤ k) : (Fin k → Bool) ≃ (Fin m → Bool) × (Fin (k - m) → Bool) where
  toFun f :=
    (fun i => f ⟨i.val, lt_of_lt_of_le i.isLt hm⟩,
     fun j => f ⟨m + j.val, by omega⟩)
  invFun p i :=
    if hi : i.val < m then p.1 ⟨i.val, hi⟩ else p.2 ⟨i.val - m, by omega⟩
  left_inv f := by
    funext i
    dsimp only
    by_cases hi : i.val < m
    · simp [hi]
    · simp only [hi, ↓reduceDIte]
      congr 1
      apply Fin.ext
      dsimp only
      omega
  right_inv p := by
    rcases p with ⟨f1, f2⟩
    apply Prod.ext
    · funext i
      simp [i.isLt]
    · funext j
      have hnot : ¬ m + j.val < m := by omega
      simp only [hnot, ↓reduceDIte]
      congr 1
      apply Fin.ext
      dsimp only
      omega

def cyclicSplit (k p0 m : ℕ) (hk : 0 < k) (hm : m ≤ k) :
    Fin (2 ^ k) ≃ Fin (2 ^ m) × Fin (2 ^ (k - m)) :=
  ((finPowEquiv k).trans
    (Equiv.arrowCongr (shiftPerm k p0 hk).symm (Equiv.refl Bool))).trans
    ((bitsSplit k m hm).trans
      ((finPowEquiv m).symm.prodCongr (finPowEquiv (k - m)).symm))

lemma cyclicSplit_symm_testBit_left {k p0 m : ℕ} (hk : 0 < k) (hm : m ≤ k)
    (u : Fin (2 ^ m)) (v : Fin (2 ^ (k - m))) (i : ℕ) (hi : i < m) :
    ((cyclicSplit k p0 m hk hm).symm (u, v)).val.testBit ((p0 + i) % k) = u.val.testBit i := by
  set key := (cyclicSplit k p0 m hk hm).symm (u, v)
  have h : finPowEquiv m (cyclicSplit k p0 m hk hm key).1 ⟨i, hi⟩ = finPowEquiv m u ⟨i, hi⟩ :=
    congrArg (fun p => finPowEquiv m p.1 ⟨i, hi⟩)
      ((cyclicSplit k p0 m hk hm).apply_symm_apply (u, v))
  simp only [cyclicSplit, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.apply_symm_apply, bitsSplit, Equiv.coe_fn_mk, Equiv.arrowCongr_apply,
    Equiv.symm_symm, shiftPerm, finPowEquiv] at h
  exact h

lemma cyclicSplit_symm_testBit_right {k p0 m : ℕ} (hk : 0 < k) (hm : m ≤ k)
    (u : Fin (2 ^ m)) (v : Fin (2 ^ (k - m))) (j : ℕ) (hj : j < k - m) :
    ((cyclicSplit k p0 m hk hm).symm (u, v)).val.testBit ((p0 + (m + j)) % k) =
      v.val.testBit j := by
  set key := (cyclicSplit k p0 m hk hm).symm (u, v)
  have h : finPowEquiv (k - m) (cyclicSplit k p0 m hk hm key).2 ⟨j, hj⟩ =
      finPowEquiv (k - m) v ⟨j, hj⟩ :=
    congrArg (fun p => finPowEquiv (k - m) p.2 ⟨j, hj⟩)
      ((cyclicSplit k p0 m hk hm).apply_symm_apply (u, v))
  simp only [cyclicSplit, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply,
    Equiv.apply_symm_apply, bitsSplit, Equiv.coe_fn_mk, Equiv.arrowCongr_apply,
    Equiv.symm_symm, shiftPerm, finPowEquiv] at h
  exact h

lemma card_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (p : α → Prop) [DecidablePred p] [DecidablePred (fun b => p (e.symm b))] :
    (Finset.univ.filter p).card = (Finset.univ.filter (fun b => p (e.symm b))).card := by
  refine Finset.card_bij (fun a _ => e a) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    simpa only [Equiv.symm_apply_apply] using ha
  · intro a1 _ a2 _ h
    exact e.injective h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hb

lemma fixed_name_key_count {k r h : ℕ} (hh : 0 < h) (hr : r ≤ 1 ∨ 4 ≤ r) (hb : h + bVal r ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (col : Bool) (nm : ℕ) (hnm : nm < 2 ^ k) (target : Fin (2 ^ h)) :
    (Finset.univ.filter (fun key : Fin (2 ^ k) =>
      runPrefix k r masks col key.val nm r >>> (k - h) = target.val)).card = 2 ^ (k - h) := by
  have hbb := bVal_bounds hr
  have hk : 0 < k := by omega
  have hhk : h ≤ k := by omega
  set p0 := pStart k r h col
  set e := cyclicSplit k p0 h hk hhk
  rw [card_filter_equiv e]
  have hbij : ∀ v : Fin (2 ^ (k - h)), Function.Bijective (fun u : Fin (2 ^ h) =>
      (⟨runPrefix k r masks col (e.symm (u, v)).val nm r >>> (k - h),
        shr_lt_two_pow (runPrefix_lt masks col _ nm hnm r) hhk⟩ : Fin (2 ^ h))) := by
    intro v
    apply unitriangular_bijective
    intro t ht u1 u2 hhi
    dsimp only
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    have hpiv := run_key_pivot_iff hh hr hb masks col nm hnm
      (e.symm (u1, v)).val (e.symm (u2, v)).val (e.symm (u1, v)).isLt (e.symm (u2, v)).isLt t ht (by
        intro u hu1 hu2
        have htu_lt : t + u < k := by omega
        have hassoc : p0 + t + u = p0 + (t + u) := by omega
        rw [hassoc]
        by_cases htu : t + u < h
        · rw [cyclicSplit_symm_testBit_left hk hhk u1 v (t + u) htu,
              cyclicSplit_symm_testBit_left hk hhk u2 v (t + u) htu]
          exact hhi (t + u) (by omega) htu
        · have hj : t + u - h < k - h := by omega
          have heq : t + u = h + (t + u - h) := by omega
          rw [heq, cyclicSplit_symm_testBit_right hk hhk u1 v (t + u - h) hj,
              cyclicSplit_symm_testBit_right hk hhk u2 v (t + u - h) hj])
    rw [hpiv, cyclicSplit_symm_testBit_left hk hhk u1 v t ht,
        cyclicSplit_symm_testBit_left hk hhk u2 v t ht]
  have hprod :
      (Finset.univ.filter (fun p : Fin (2 ^ h) × Fin (2 ^ (k - h)) =>
        runPrefix k r masks col (e.symm p).val nm r >>> (k - h) = target.val)).card =
      ∑ v : Fin (2 ^ (k - h)),
        (Finset.univ.filter (fun u : Fin (2 ^ h) =>
          runPrefix k r masks col (e.symm (u, v)).val nm r >>> (k - h) = target.val)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.card_filter]
  rw [hprod]
  have hone : ∀ v : Fin (2 ^ (k - h)),
      (Finset.univ.filter (fun u : Fin (2 ^ h) =>
        runPrefix k r masks col (e.symm (u, v)).val nm r >>> (k - h) = target.val)).card = 1 := by
    intro v
    rcases (hbij v).2 target with ⟨u0, hu0⟩
    have hfilt :
        Finset.univ.filter (fun u : Fin (2 ^ h) =>
          runPrefix k r masks col (e.symm (u, v)).val nm r >>> (k - h) = target.val) = {u0} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hEq
        apply (hbij v).1
        apply Fin.ext
        dsimp only
        rw [hEq]
        exact (congrArg Fin.val hu0).symm
      · intro hEq
        subst hEq
        exact congrArg Fin.val hu0
    rw [hfilt, Finset.card_singleton]
  simp [hone]

lemma birkhoff_nat {N : ℕ} : ∀ (d : ℕ) (Q : Fin N → Fin N → ℕ),
    (∀ x, ∑ y : Fin N, Q x y = d) →
    (∀ y, ∑ x : Fin N, Q x y = d) →
    ∃ perms : Fin d → Equiv.Perm (Fin N),
      ∀ x y : Fin N, Q x y = (Finset.univ.filter (fun j : Fin d => perms j x = y)).card := by
  intro d
  induction d with
  | zero =>
    intro Q hrow _
    refine ⟨Fin.elim0, fun x y => ?_⟩
    have hle : Q x y ≤ ∑ y' : Fin N, Q x y' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    rw [hrow x] at hle
    simp only [Nat.le_zero.mp hle]
    simp
  | succ d ih =>
    intro Q hrow hcol
    let t : Fin N → Finset (Fin N) := fun x => Finset.univ.filter (fun y => 0 < Q x y)
    have hHall : ∀ s : Finset (Fin N), s.card ≤ (s.biUnion t).card := by
      intro s
      set T := s.biUnion t
      have h1 : s.card * (d + 1) = ∑ x ∈ s, ∑ y ∈ T, Q x y := by
        calc
          s.card * (d + 1) = ∑ _x ∈ s, (d + 1) := by rw [Finset.sum_const, smul_eq_mul]
          _ = ∑ x ∈ s, ∑ y : Fin N, Q x y := Finset.sum_congr rfl fun x _ => (hrow x).symm
          _ = ∑ x ∈ s, ∑ y ∈ T, Q x y := by
            refine Finset.sum_congr rfl fun x hx => ?_
            symm
            refine Finset.sum_subset (Finset.subset_univ T) fun y _ hyT => ?_
            by_contra hnz
            have hpos : 0 < Q x y := Nat.pos_of_ne_zero hnz
            have hyt : y ∈ t x := by simp [t, hpos]
            exact hyT (Finset.mem_biUnion.mpr ⟨x, hx, hyt⟩)
      have h2 : ∑ x ∈ s, ∑ y ∈ T, Q x y ≤ T.card * (d + 1) := by
        rw [Finset.sum_comm]
        calc
          ∑ y ∈ T, ∑ x ∈ s, Q x y ≤ ∑ y ∈ T, ∑ x : Fin N, Q x y := by
            refine Finset.sum_le_sum fun y _ => ?_
            exact Finset.sum_le_sum_of_subset (Finset.subset_univ s)
          _ = ∑ _y ∈ T, (d + 1) := Finset.sum_congr rfl fun y _ => hcol y
          _ = T.card * (d + 1) := by rw [Finset.sum_const, smul_eq_mul]
      exact Nat.le_of_mul_le_mul_right (h1 ▸ h2) (Nat.succ_pos d)
    rcases (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hHall
      with ⟨f, hf_inj, hf_mem⟩
    let σ : Equiv.Perm (Fin N) := Equiv.ofBijective f hf_inj.bijective_of_finite
    have hpos : ∀ x : Fin N, 1 ≤ Q x (σ x) := by
      intro x
      have hx : f x ∈ t x := hf_mem x
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hx
    let Q' : Fin N → Fin N → ℕ := fun x y => Q x y - if σ x = y then 1 else 0
    have hadd : ∀ x y : Fin N, Q' x y + (if σ x = y then 1 else 0) = Q x y := by
      intro x y
      dsimp only [Q']
      by_cases hxy : σ x = y
      · subst hxy
        have hp := hpos x
        simp only [↓reduceIte]
        omega
      · simp [hxy]
    have hrow' : ∀ x, ∑ y : Fin N, Q' x y = d := by
      intro x
      have hsum : (∑ y : Fin N, Q' x y) + (∑ y : Fin N, if σ x = y then 1 else 0) = d + 1 := by
        rw [← Finset.sum_add_distrib]
        calc
          ∑ y : Fin N, (Q' x y + if σ x = y then 1 else 0) = ∑ y : Fin N, Q x y :=
            Finset.sum_congr rfl fun y _ => hadd x y
          _ = d + 1 := hrow x
      have hone : (∑ y : Fin N, if σ x = y then 1 else 0) = 1 := by simp
      omega
    have hcol' : ∀ y, ∑ x : Fin N, Q' x y = d := by
      intro y
      have hsum : (∑ x : Fin N, Q' x y) + (∑ x : Fin N, if σ x = y then 1 else 0) = d + 1 := by
        rw [← Finset.sum_add_distrib]
        calc
          ∑ x : Fin N, (Q' x y + if σ x = y then 1 else 0) = ∑ x : Fin N, Q x y :=
            Finset.sum_congr rfl fun x _ => hadd x y
          _ = d + 1 := hcol y
      have hone : (∑ x : Fin N, if σ x = y then 1 else 0) = 1 := by
        have hrew : (∑ x : Fin N, if σ x = y then 1 else 0) =
            ∑ x : Fin N, if x = σ.symm y then 1 else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          have hiff : σ x = y ↔ x = σ.symm y := by
            constructor
            · intro h; rw [← h, Equiv.symm_apply_apply]
            · intro h; rw [h, Equiv.apply_symm_apply]
          by_cases h : x = σ.symm y
          · simp [h]
          · simp [h, mt hiff.mp h]
        rw [hrew]
        simp
      omega
    rcases ih Q' hrow' hcol' with ⟨perms', hperms'⟩
    refine ⟨Fin.cons σ perms', fun x y => ?_⟩
    rw [Finset.card_filter, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Finset.card_filter, ← hperms' x y]
    have ha := hadd x y
    omega

lemma main_proof : (∀ (k r h : ℕ), 0 < h → (r ≤ 1 ∨ 4 ≤ r) →
  let b := if r = 0 then 2 else if r = 1 then 7 else 7*r-2
  h+b ≤ k →
  let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → Fin (2^k)) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let name := fun (gap : ℕ) (base : Fin (2^k)) (word : Fin (2^h)) =>
    let lo := k-h-gap*r
    base.val % 2^lo + (word.val <<< lo) + ((base.val >>> (lo+h)) <<< (lo+h))
  ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (rowBase colBase : Fin (2^k)),
    ∃ perms : Fin (2^b) → Equiv.Perm (Fin (2^h)),
      ∀ x y : Fin (2^h),
        (Finset.univ.filter (fun key : Fin (2^k) =>
          run masks false key.val (name 1 rowBase x) >>> (k-h) = a.val ∧
          run masks true key.val (name 2 colBase y) >>> (k-h) = c.val)).card =
        2^(k-h-b) * (Finset.univ.filter (fun j : Fin (2^b) => perms j x = y)).card) := by
  intro k r h hh hr b hb rot chi run name masks a c rowBase colBase
  have hbb := bVal_bounds hr
  have hbeq : b = bVal r := rfl
  have hbk : h + bVal r ≤ k := hb
  have hk : 0 < k := by omega
  have hhk : h ≤ k := by omega
  have hnm_row : ∀ x : Fin (2 ^ h), nameFn k r h 1 rowBase x < 2 ^ k := fun x =>
    nameFn_lt (by omega) rowBase x
  have hnm_col : ∀ y : Fin (2 ^ h), nameFn k r h 2 colBase y < 2 ^ k := fun y =>
    nameFn_lt (by omega) colBase y
  set eW := cyclicSplit k (wStart k r h) (h + bVal r) hk hbk
  let z0 : Fin (2 ^ (k - (h + bVal r))) := ⟨0, Nat.two_pow_pos _⟩
  let M : Fin (2 ^ h) → Fin (2 ^ h) → ℕ := fun x y =>
    (Finset.univ.filter (fun key : Fin (2 ^ k) =>
      runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
      runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val)).card
  let Q : Fin (2 ^ h) → Fin (2 ^ h) → ℕ := fun x y =>
    (Finset.univ.filter (fun u : Fin (2 ^ (h + bVal r)) =>
      runPrefix k r masks false (eW.symm (u, z0)).val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
      runPrefix k r masks true (eW.symm (u, z0)).val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val)).card
  have hM_eq : ∀ x y : Fin (2 ^ h), M x y = 2 ^ (k - h - bVal r) * Q x y := by
    intro x y
    dsimp only [M, Q]
    rw [card_filter_equiv eW]
    have hind : ∀ u : Fin (2 ^ (h + bVal r)), ∀ v : Fin (2 ^ (k - (h + bVal r))),
        (runPrefix k r masks false (eW.symm (u, v)).val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
         runPrefix k r masks true (eW.symm (u, v)).val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val) ↔
        (runPrefix k r masks false (eW.symm (u, z0)).val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
         runPrefix k r masks true (eW.symm (u, z0)).val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val) := by
      intro u v
      have hagree : ∀ n < h + bVal r,
          (eW.symm (u, v)).val.testBit ((wStart k r h + n) % k) =
          (eW.symm (u, z0)).val.testBit ((wStart k r h + n) % k) := by
        intro n hn
        rw [cyclicSplit_symm_testBit_left hk hbk u v n hn,
            cyclicSplit_symm_testBit_left hk hbk u z0 n hn]
      have hrw1 := run_key_window hh hr hbk masks false _ (hnm_row x)
        (eW.symm (u, v)).val (eW.symm (u, z0)).val (eW.symm (u, v)).isLt (eW.symm (u, z0)).isLt hagree
      have hrw2 := run_key_window hh hr hbk masks true _ (hnm_col y)
        (eW.symm (u, v)).val (eW.symm (u, z0)).val (eW.symm (u, v)).isLt (eW.symm (u, z0)).isLt hagree
      rw [hrw1, hrw2]
    rw [Finset.card_filter, Fintype.sum_prod_type_right]
    have hsum :
        ∑ v : Fin (2 ^ (k - (h + bVal r))),
          ∑ u : Fin (2 ^ (h + bVal r)),
            (if runPrefix k r masks false (eW.symm (u, v)).val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
                runPrefix k r masks true (eW.symm (u, v)).val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
             then 1 else 0) =
        ∑ _v : Fin (2 ^ (k - (h + bVal r))),
          (Finset.univ.filter (fun u : Fin (2 ^ (h + bVal r)) =>
            runPrefix k r masks false (eW.symm (u, z0)).val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
            runPrefix k r masks true (eW.symm (u, z0)).val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val)).card := by
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h1 : runPrefix k r masks false (eW.symm (u, z0)).val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
          runPrefix k r masks true (eW.symm (u, z0)).val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
      · simp [h1, (hind u v).mpr h1]
      · simp [h1, mt (hind u v).mp h1]
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.sub_sub]
  have hpow : 2 ^ (k - h) = 2 ^ (k - h - bVal r) * 2 ^ bVal r := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hQ_row : ∀ x : Fin (2 ^ h), ∑ y : Fin (2 ^ h), Q x y = 2 ^ bVal r := by
    intro x
    have hMsum : ∑ y : Fin (2 ^ h), M x y = 2 ^ (k - h) := by
      calc
        ∑ y : Fin (2 ^ h), M x y
            = ∑ y : Fin (2 ^ h), ∑ key : Fin (2 ^ k),
                if runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
                   runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
                then 1 else 0 := by
              refine Finset.sum_congr rfl fun y _ => ?_
              exact Finset.card_filter _ _
        _ = ∑ key : Fin (2 ^ k), ∑ y : Fin (2 ^ h),
                if runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
                   runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
                then 1 else 0 := Finset.sum_comm
        _ = ∑ key : Fin (2 ^ k),
                if runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val
                then 1 else 0 := by
              refine Finset.sum_congr rfl fun key _ => ?_
              by_cases hrow_ok : runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val
              · simp only [hrow_ok, true_and, ↓reduceIte]
                have hbij := word_map_bijective hh hr hbk masks true key.val colBase
                rcases hbij.2 c with ⟨y0, hy0⟩
                rw [← Finset.card_filter]
                have hfilt : Finset.univ.filter (fun y : Fin (2 ^ h) =>
                    runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val) = {y0} := by
                  ext y
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · intro hEq
                    apply hbij.1
                    apply Fin.ext
                    dsimp only
                    simp only [↓reduceIte]
                    rw [hEq]
                    simpa using (congrArg Fin.val hy0).symm
                  · intro hEq
                    subst hEq
                    simpa using congrArg Fin.val hy0
                rw [hfilt, Finset.card_singleton]
              · simp [hrow_ok]
        _ = (Finset.univ.filter (fun key : Fin (2 ^ k) =>
              runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val)).card :=
            (Finset.card_filter _ _).symm
        _ = 2 ^ (k - h) := fixed_name_key_count hh hr hbk masks false _ (hnm_row x) a
    have hmul : 2 ^ (k - h - bVal r) * ∑ y : Fin (2 ^ h), Q x y =
        2 ^ (k - h - bVal r) * 2 ^ bVal r := by
      rw [Finset.mul_sum]
      calc
        ∑ y : Fin (2 ^ h), 2 ^ (k - h - bVal r) * Q x y = ∑ y : Fin (2 ^ h), M x y :=
          Finset.sum_congr rfl fun y _ => (hM_eq x y).symm
        _ = 2 ^ (k - h) := hMsum
        _ = 2 ^ (k - h - bVal r) * 2 ^ bVal r := hpow
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) hmul
  have hQ_col : ∀ y : Fin (2 ^ h), ∑ x : Fin (2 ^ h), Q x y = 2 ^ bVal r := by
    intro y
    have hMsum : ∑ x : Fin (2 ^ h), M x y = 2 ^ (k - h) := by
      calc
        ∑ x : Fin (2 ^ h), M x y
            = ∑ x : Fin (2 ^ h), ∑ key : Fin (2 ^ k),
                if runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
                   runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
                then 1 else 0 := by
              refine Finset.sum_congr rfl fun x _ => ?_
              exact Finset.card_filter _ _
        _ = ∑ key : Fin (2 ^ k), ∑ x : Fin (2 ^ h),
                if runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val ∧
                   runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
                then 1 else 0 := Finset.sum_comm
        _ = ∑ key : Fin (2 ^ k),
                if runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
                then 1 else 0 := by
              refine Finset.sum_congr rfl fun key _ => ?_
              by_cases hcol_ok : runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val
              · simp only [hcol_ok, and_true, ↓reduceIte]
                have hbij := word_map_bijective hh hr hbk masks false key.val rowBase
                rcases hbij.2 a with ⟨x0, hx0⟩
                rw [← Finset.card_filter]
                have hfilt : Finset.univ.filter (fun x : Fin (2 ^ h) =>
                    runPrefix k r masks false key.val (nameFn k r h 1 rowBase x) r >>> (k - h) = a.val) = {x0} := by
                  ext x
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · intro hEq
                    apply hbij.1
                    apply Fin.ext
                    dsimp only
                    simp only [Bool.false_eq_true, ↓reduceIte]
                    rw [hEq]
                    simpa using (congrArg Fin.val hx0).symm
                  · intro hEq
                    subst hEq
                    simpa using congrArg Fin.val hx0
                rw [hfilt, Finset.card_singleton]
              · simp [hcol_ok]
        _ = (Finset.univ.filter (fun key : Fin (2 ^ k) =>
              runPrefix k r masks true key.val (nameFn k r h 2 colBase y) r >>> (k - h) = c.val)).card :=
            (Finset.card_filter _ _).symm
        _ = 2 ^ (k - h) := fixed_name_key_count hh hr hbk masks true _ (hnm_col y) c
    have hmul : 2 ^ (k - h - bVal r) * ∑ x : Fin (2 ^ h), Q x y =
        2 ^ (k - h - bVal r) * 2 ^ bVal r := by
      rw [Finset.mul_sum]
      calc
        ∑ x : Fin (2 ^ h), 2 ^ (k - h - bVal r) * Q x y = ∑ x : Fin (2 ^ h), M x y :=
          Finset.sum_congr rfl fun x _ => (hM_eq x y).symm
        _ = 2 ^ (k - h) := hMsum
        _ = 2 ^ (k - h - bVal r) * 2 ^ bVal r := hpow
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) hmul
  rcases birkhoff_nat (2 ^ bVal r) Q hQ_row hQ_col with ⟨perms, hperms⟩
  refine ⟨perms, fun x y => ?_⟩
  have hxy := hM_eq x y
  rw [hperms x y] at hxy
  exact hxy

end PEqualNP.Outside.L_meta_30868_aux

theorem PEqualNP.Outside.L_meta_30868 : (∀ (k r h : ℕ), 0 < h → (r ≤ 1 ∨ 4 ≤ r) →
  let b := if r = 0 then 2 else if r = 1 then 7 else 7*r-2
  h+b ≤ k →
  let rot := fun (d x : ℕ) => ((x <<< (d % k)) ||| (x >>> (k-d % k))) % 2^k
  let chi := fun (x : ℕ) => (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1) % k)) && x.testBit ((i+2) % k))).toNat <<< i)) 0
  let run := fun (masks : ℕ → Fin (2^k)) (col : Bool) (key name : ℕ) =>
    let gap : ℕ := if col then 2 else 1
    (List.range r).foldl (fun z j =>
      let mixed := z ^^^ rot gap z ^^^ rot (k-gap % k) z
      chi mixed ^^^ rot (if col then 3*(j+1)+1 else 2*j) key ^^^
        (masks (if col then r+j else j)).val) (rot (if col then 3 else 1) key ^^^ name)
  let name := fun (gap : ℕ) (base : Fin (2^k)) (word : Fin (2^h)) =>
    let lo := k-h-gap*r
    base.val % 2^lo + (word.val <<< lo) + ((base.val >>> (lo+h)) <<< (lo+h))
  ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (rowBase colBase : Fin (2^k)),
    ∃ perms : Fin (2^b) → Equiv.Perm (Fin (2^h)),
      ∀ x y : Fin (2^h),
        (Finset.univ.filter (fun key : Fin (2^k) =>
          run masks false key.val (name 1 rowBase x) >>> (k-h) = a.val ∧
          run masks true key.val (name 2 colBase y) >>> (k-h) = c.val)).card =
        2^(k-h-b) * (Finset.univ.filter (fun j : Fin (2^b) => perms j x = y)).card) :=
  PEqualNP.Outside.L_meta_30868_aux.main_proof
