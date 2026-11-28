import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Finite

namespace PEqualNP.Outside.L_meta_32021

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

section BitBridge

def rotN (k d x : ℕ) : ℕ :=
  ((x <<< (d % k)) ||| (x >>> (k - d % k))) % 2 ^ k

def chiN (k x : ℕ) : ℕ :=
  (List.range k).foldl (fun (acc i : ℕ) =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

def runN (k r : ℕ) (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key nameVal : ℕ) : ℕ :=
  let gap : ℕ := if col then 2 else 1
  (List.range r).foldl (fun z j =>
    let mixed := z ^^^ rotN k gap z ^^^ rotN k (k - gap % k) z
    chiN k mixed ^^^ rotN k (if col then 3 * (j + 1) + 1 else 2 * j) key ^^^
      (masks (if col then r + j else j)).val) (rotN k (if col then 3 else 1) key ^^^ nameVal)

def nameN (k r h gap : ℕ) (base : Fin (2 ^ k)) (word : Fin (2 ^ h)) : ℕ :=
  let lo := k - h - gap * r
  base.val % 2 ^ lo + (word.val <<< lo) + ((base.val >>> (lo + h)) <<< (lo + h))

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_two : (2 : ZMod 2) = 0 := rfl

lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by
  fin_cases x <;> rfl

lemma zmod2_ne_add_one (a : ZMod 2) : a ≠ a + 1 := by
  intro h
  fin_cases a <;> cases h

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma testBit_add_mul_two_pow {x y s i : ℕ} (hx : x < 2 ^ s) :
    (x + y * 2 ^ s).testBit i = if i < s then x.testBit i else y.testBit (i - s) := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.testBit_eq_decide_div_mod_eq]
  by_cases hi : i < s
  · rw [if_pos hi]
    have hpow : 2 ^ s = 2 ^ i * 2 ^ (s - i) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hi)]
    have hrew1 : y * 2 ^ s = (y * 2 ^ (s - i)) * 2 ^ i := by
      rw [hpow]; ring
    have hdiv : (x + y * 2 ^ s) / 2 ^ i = x / 2 ^ i + y * 2 ^ (s - i) := by
      rw [hrew1, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    have h2 : 2 ∣ 2 ^ (s - i) := by
      obtain ⟨d, hd⟩ : ∃ d, s - i = d + 1 := ⟨s - i - 1, by omega⟩
      rw [hd, pow_succ]
      exact Nat.dvd_mul_left 2 (2 ^ d)
    obtain ⟨q, hq⟩ := h2
    have hrew2 : y * 2 ^ (s - i) = (y * q) * 2 := by
      rw [hq]; ring
    rw [hdiv, hrew2, Nat.add_mul_mod_self_right]
  · rw [if_neg hi]
    have hpow : 2 ^ i = 2 ^ s * 2 ^ (i - s) := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_not_lt hi)]
    rw [hpow, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ (Nat.two_pow_pos s),
      Nat.div_eq_of_lt hx, Nat.zero_add]

lemma lt_two_pow_of_testBit {n k : ℕ} (h : ∀ i ≥ k, n.testBit i = false) : n < 2 ^ k := by
  have heq : n % 2 ^ k = n := Nat.eq_of_testBit_eq fun i => by
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < k
    · simp [hi]
    · simp [hi, h i (Nat.le_of_not_lt hi)]
  rw [← heq]
  exact Nat.mod_lt n (Nat.two_pow_pos k)

lemma nat_xor_lt_two_pow {k a b : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  refine lt_two_pow_of_testBit fun i hi => ?_
  rw [Nat.testBit_xor,
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi)),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hi))]
  rfl

lemma rotN_lt (k d x : ℕ) : rotN k d x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma pack_foldl_spec (f : ℕ → Bool) : ∀ m : ℕ,
    let val := (List.range m).foldl (fun (acc i : ℕ) => acc ||| ((f i).toNat <<< i)) 0
    val < 2 ^ m ∧ ∀ j : ℕ, val.testBit j = if j < m then f j else false
  | 0 => ⟨by simp, fun j => by simp⟩
  | m + 1 => by
    dsimp only
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have ih := pack_foldl_spec f m
    dsimp only at ih
    set acc := (List.range m).foldl (fun (acc i : ℕ) => acc ||| ((f i).toNat <<< i)) 0
    have hbit : ∀ j : ℕ, (acc ||| ((f m).toNat <<< m)).testBit j =
        if j < m + 1 then f j else false := by
      intro j
      rw [Nat.testBit_or, ih.2 j, Nat.testBit_shiftLeft]
      by_cases hjm : j < m
      · have hjm1 : j < m + 1 := by omega
        have hnot : ¬ m ≤ j := by omega
        simp [hjm, hjm1, hnot]
      · by_cases hjeq : j = m
        · subst hjeq
          simp only [lt_irrefl, ↓reduceIte, le_refl, decide_true, Nat.sub_self, Bool.false_or,
            Bool.true_and, Nat.lt_add_one]
          cases f j <;> decide
        · have hnot1 : ¬ j < m + 1 := by omega
          have hgt : 0 < j - m := by omega
          have htb : (f m).toNat.testBit (j - m) = false := by
            cases f m
            · simp
            · exact Nat.testBit_lt_two_pow (by
                have h2 : 2 ≤ 2 ^ (j - m) := by
                  calc 2 = 2 ^ 1 := rfl
                    _ ≤ 2 ^ (j - m) := Nat.pow_le_pow_right (by omega) hgt
                simp only [Bool.toNat_true]
                omega)
          simp [hjm, hnot1, htb]
    refine ⟨lt_two_pow_of_testBit fun j hj => ?_, hbit⟩
    rw [hbit j, if_neg (by omega)]

lemma chiN_lt (k x : ℕ) : chiN k x < 2 ^ k :=
  (pack_foldl_spec (fun i => xor (x.testBit i)
    (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))) k).1

lemma chiN_testBit (k x j : ℕ) (hj : j < k) :
    (chiN k x).testBit j =
      xor (x.testBit j) (!(x.testBit ((j + 1) % k)) && x.testBit ((j + 2) % k)) := by
  have h := (pack_foldl_spec
    (fun i => xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))) k).2 j
  rw [if_pos hj] at h
  exact h

lemma nameN_spec {k r h gap : ℕ} (hle : gap * r + h ≤ k)
    (base : Fin (2 ^ k)) (word : Fin (2 ^ h)) :
    let lo := k - h - gap * r
    nameN k r h gap base word < 2 ^ k ∧
    ∀ j < k, (nameN k r h gap base word).testBit j =
      if lo ≤ j ∧ j < lo + h then word.val.testBit (j - lo) else base.val.testBit j := by
  intro lo
  have hloh : lo + h ≤ k := by dsimp [lo]; omega
  have hA : base.val % 2 ^ lo < 2 ^ lo := Nat.mod_lt _ (Nat.two_pow_pos lo)
  have hB : word.val <<< lo = word.val * 2 ^ lo := Nat.shiftLeft_eq _ _
  have hAB_lt : base.val % 2 ^ lo + (word.val <<< lo) < 2 ^ (lo + h) := by
    rw [hB, pow_add]
    have hw : word.val + 1 ≤ 2 ^ h := word.isLt
    have hmul : word.val * 2 ^ lo + 2 ^ lo ≤ 2 ^ h * 2 ^ lo := by
      rw [← Nat.add_one_mul]
      exact Nat.mul_le_mul_right (2 ^ lo) hw
    rw [Nat.mul_comm (2 ^ lo) (2 ^ h)]
    omega
  have hC : (base.val >>> (lo + h)) <<< (lo + h) = (base.val / 2 ^ (lo + h)) * 2 ^ (lo + h) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have hlt : nameN k r h gap base word < 2 ^ k := by
    unfold nameN
    change base.val % 2 ^ lo + (word.val <<< lo) + ((base.val >>> (lo + h)) <<< (lo + h)) < 2 ^ k
    rw [hC]
    have hq : base.val / 2 ^ (lo + h) < 2 ^ (k - (lo + h)) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (lo + h)), ← pow_add,
        Nat.sub_add_cancel hloh]
      exact base.isLt
    have hq1 : base.val / 2 ^ (lo + h) + 1 ≤ 2 ^ (k - (lo + h)) := hq
    have hmul : (base.val / 2 ^ (lo + h)) * 2 ^ (lo + h) + 2 ^ (lo + h) ≤
        2 ^ (k - (lo + h)) * 2 ^ (lo + h) := by
      rw [← Nat.add_one_mul]
      exact Nat.mul_le_mul_right _ hq1
    rw [← pow_add, Nat.sub_add_cancel hloh] at hmul
    omega
  refine ⟨hlt, fun j _ => ?_⟩
  unfold nameN
  change (base.val % 2 ^ lo + (word.val <<< lo) + ((base.val >>> (lo + h)) <<< (lo + h))).testBit j = _
  rw [hC, testBit_add_mul_two_pow hAB_lt]
  by_cases hj1 : j < lo + h
  · rw [if_pos hj1, hB, testBit_add_mul_two_pow hA]
    by_cases hj0 : j < lo
    · rw [if_pos hj0, if_neg (by omega), Nat.testBit_mod_two_pow, decide_eq_true hj0, Bool.true_and]
    · rw [if_neg hj0, if_pos ⟨Nat.le_of_not_lt hj0, hj1⟩]
  · rw [if_neg hj1, if_neg (by omega), ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
      Nat.add_sub_cancel' (Nat.le_of_not_lt hj1)]

lemma runN_lt {k r : ℕ} (masks : ℕ → Fin (2 ^ k)) (col : Bool) (key nameVal : ℕ)
    (hname : nameVal < 2 ^ k) :
    runN k r masks col key nameVal < 2 ^ k := by
  have haux : ∀ (t : ℕ) (offset : ℕ),
      (List.range t).foldl (fun z j =>
        let gap : ℕ := if col then 2 else 1
        let mixed := z ^^^ rotN k gap z ^^^ rotN k (k - gap % k) z
        chiN k mixed ^^^ rotN k (if col then 3 * (j + 1) + 1 else 2 * j) key ^^^
          (masks (if col then offset + j else j)).val)
        (rotN k (if col then 3 else 1) key ^^^ nameVal) < 2 ^ k := by
    intro t offset
    induction t with
    | zero => exact nat_xor_lt_two_pow (rotN_lt k _ key) hname
    | succ t ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact nat_xor_lt_two_pow
        (nat_xor_lt_two_pow (chiN_lt k _) (rotN_lt k _ key))
        (masks _).isLt
  exact haux r r

def toW (k : ℕ) [NeZero k] (x : ℕ) : ZMod k → ZMod 2 :=
  fun i => b2z (x.testBit i.val)

def fromW (k : ℕ) [NeZero k] (w : ZMod k → ZMod 2) : Fin (2 ^ k) :=
  ⟨(List.range k).foldl (fun (acc i : ℕ) =>
      acc ||| ((decide (w (i : ZMod k) = 1)).toNat <<< i)) 0,
    (pack_foldl_spec (fun (i : ℕ) => decide (w (i : ZMod k) = 1)) k).1⟩

lemma toW_fromW (k : ℕ) [NeZero k] (w : ZMod k → ZMod 2) :
    toW k (fromW k w).val = w := by
  funext i
  dsimp only [toW, fromW, b2z]
  have hlt : i.val < k := ZMod.val_lt i
  have hb := (pack_foldl_spec (fun (j : ℕ) => decide (w (j : ZMod k) = 1)) k).2 i.val
  rw [if_pos hlt] at hb
  rw [hb, ZMod.natCast_zmod_val]
  rcases zmod2_eq_zero_or_one (w i) with h0 | h1
  · simp [h0]
  · simp [h1]

lemma fromW_toW (k : ℕ) [NeZero k] (x : Fin (2 ^ k)) :
    fromW k (toW k x.val) = x := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  dsimp only [fromW]
  rw [(pack_foldl_spec (fun (i : ℕ) => decide (toW k x.val (i : ZMod k) = 1)) k).2 j]
  by_cases hj : j < k
  · rw [if_pos hj]
    simp only [toW, b2z, ZMod.val_natCast, Nat.mod_eq_of_lt hj]
    cases x.val.testBit j <;> simp
  · rw [if_neg hj]
    symm
    exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hj)))

def finPowEquivW (k : ℕ) [NeZero k] : Fin (2 ^ k) ≃ (ZMod k → ZMod 2) where
  toFun x := toW k x.val
  invFun := fromW k
  left_inv := fromW_toW k
  right_inv := toW_fromW k

lemma toW_xor (k : ℕ) [NeZero k] (a b : ℕ) :
    toW k (a ^^^ b) = toW k a + toW k b := by
  funext i
  simp only [toW, Pi.add_apply, Nat.testBit_xor]
  exact b2z_xor _ _

def turn {k : ℕ} (d : ℕ) (w : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun i => w (i - (d : ZMod k))

def mix {k : ℕ} (d : ℕ) (w : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun i => w (i - (d : ZMod k)) + w i + w (i + (d : ZMod k))

def chi {k : ℕ} (w : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun i => w i + (1 + w (i + 1)) * w (i + 2)

lemma toW_rot (k : ℕ) [NeZero k] (d x : ℕ) (hx : x < 2 ^ k) :
    toW k (rotN k d x) = turn d (toW k x) := by
  funext i
  dsimp only [toW, rotN, turn]
  have hi : i.val < k := ZMod.val_lt i
  have hkpos : 0 < k := NeZero.pos k
  have hmod : d % k < k := Nat.mod_lt d hkpos
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hd_cast : (d : ZMod k) = ((d % k : ℕ) : ZMod k) := by
    rw [← ZMod.natCast_mod]
  by_cases hle : d % k ≤ i.val
  · have hge : k ≤ (k - d % k) + i.val := by omega
    have hhi : x.testBit ((k - d % k) + i.val) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hge))
    rw [decide_eq_true hle, Bool.true_and, hhi, Bool.or_false]
    have hval : (i - (d : ZMod k)).val = i.val - d % k := by
      have heq : i - (d : ZMod k) = ((i.val - d % k : ℕ) : ZMod k) := by
        rw [hd_cast, Nat.cast_sub hle, ZMod.natCast_zmod_val]
      rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [hval]
  · have hlt : i.val < d % k := Nat.lt_of_not_ge hle
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or]
    have hval : (i - (d : ZMod k)).val = (k - d % k) + i.val := by
      have heq : i - (d : ZMod k) = (((k - d % k) + i.val : ℕ) : ZMod k) := by
        rw [hd_cast, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt hmod), ZMod.natCast_self,
          ZMod.natCast_zmod_val]
        ring
      rw [heq, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [hval]

lemma toW_mix (k : ℕ) [NeZero k] (gap z : ℕ) (hg : gap < k) (hz : z < 2 ^ k) :
    toW k (z ^^^ rotN k gap z ^^^ rotN k (k - gap % k) z) = mix gap (toW k z) := by
  rw [toW_xor, toW_xor, toW_rot k gap z hz, toW_rot k (k - gap % k) z hz]
  funext i
  simp only [Pi.add_apply, turn, mix]
  have h1 : ((k - gap % k : ℕ) : ZMod k) = - (gap : ZMod k) := by
    rw [Nat.mod_eq_of_lt hg, Nat.cast_sub (Nat.le_of_lt hg), ZMod.natCast_self, zero_sub]
  rw [h1, sub_neg_eq_add]
  ring

lemma toW_chi (k : ℕ) [NeZero k] (x : ℕ) :
    toW k (chiN k x) = chi (toW k x) := by
  funext i
  have hi : i.val < k := ZMod.val_lt i
  simp only [toW, chi, chiN_testBit k x i.val hi]
  have h1 : (i + 1).val = (i.val + 1) % k := by
    rw [← ZMod.val_natCast, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
  have h2 : (i + 2).val = (i.val + 2) % k := by
    rw [← ZMod.val_natCast, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val]
  rw [h1, h2, b2z_xor, b2z_and, b2z_not]

def rowSt {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u key : ZMod k → ZMod 2) : ℕ → ZMod k → ZMod 2
  | 0 => turn 1 key + u
  | t + 1 => chi (mix 1 (rowSt cr u key t)) + turn (2 * t) key + cr t

def colSt {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (v key : ZMod k → ZMod 2) : ℕ → ZMod k → ZMod 2
  | 0 => turn 3 key + v
  | t + 1 => chi (mix 2 (colSt cc v key t)) + turn (3 * (t + 1) + 1) key + cc t

lemma toW_runN_false {k : ℕ} [NeZero k] (hk : 1 < k) (r : ℕ) (masks : ℕ → Fin (2 ^ k))
    (key nameVal : ℕ) (hkey : key < 2 ^ k) (hname : nameVal < 2 ^ k) :
    toW k (runN k r masks false key nameVal) =
      rowSt (fun j => toW k (masks j).val) (toW k nameVal) (toW k key) r := by
  induction r with
  | zero =>
    unfold runN rowSt
    simp only [Bool.false_eq_true, ↓reduceIte, List.range_zero, List.foldl_nil]
    rw [toW_xor, toW_rot k 1 key hkey]
  | succ t ih =>
    unfold runN
    simp only [Bool.false_eq_true, ↓reduceIte, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    have hprev_lt : runN k t masks false key nameVal < 2 ^ k := runN_lt masks false key nameVal hname
    change toW k (chiN k (runN k t masks false key nameVal ^^^
        rotN k 1 (runN k t masks false key nameVal) ^^^
        rotN k (k - 1 % k) (runN k t masks false key nameVal)) ^^^
      rotN k (2 * t) key ^^^ (masks t).val) = _
    rw [toW_xor, toW_xor, toW_chi, toW_mix k 1 _ hk hprev_lt, toW_rot k (2 * t) key hkey, ih]
    rfl

lemma toW_runN_true {k : ℕ} [NeZero k] (hk : 2 < k) (r : ℕ) (masks : ℕ → Fin (2 ^ k))
    (key nameVal : ℕ) (hkey : key < 2 ^ k) (hname : nameVal < 2 ^ k) :
    toW k (runN k r masks true key nameVal) =
      colSt (fun j => toW k (masks (r + j)).val) (toW k nameVal) (toW k key) r := by
  have haux : ∀ (t : ℕ) (offset : ℕ),
      toW k ((List.range t).foldl (fun z j =>
        let mixed := z ^^^ rotN k 2 z ^^^ rotN k (k - 2 % k) z
        chiN k mixed ^^^ rotN k (3 * (j + 1) + 1) key ^^^ (masks (offset + j)).val)
        (rotN k 3 key ^^^ nameVal)) =
      colSt (fun j => toW k (masks (offset + j)).val) (toW k nameVal) (toW k key) t := by
    intro t offset
    induction t with
    | zero =>
      simp only [List.range_zero, List.foldl_nil, colSt]
      rw [toW_xor, toW_rot k 3 key hkey]
    | succ t ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      set prev := (List.range t).foldl (fun z j =>
        let mixed := z ^^^ rotN k 2 z ^^^ rotN k (k - 2 % k) z
        chiN k mixed ^^^ rotN k (3 * (j + 1) + 1) key ^^^ (masks (offset + j)).val)
        (rotN k 3 key ^^^ nameVal)
      have hprev_lt : prev < 2 ^ k := by
        clear ih
        induction t with
        | zero => exact nat_xor_lt_two_pow (rotN_lt k 3 key) hname
        | succ m ihm =>
          dsimp only [prev] at ihm ⊢
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
          exact nat_xor_lt_two_pow (nat_xor_lt_two_pow (chiN_lt k _) (rotN_lt k _ key))
            (masks _).isLt
      rw [toW_xor, toW_xor, toW_chi, toW_mix k 2 prev hk hprev_lt,
        toW_rot k (3 * (t + 1) + 1) key hkey, ih]
      rfl
  exact haux r r

lemma shr_eq_iff_win {k h : ℕ} [NeZero k] (hh : h ≤ k) (out : ℕ) (hout : out < 2 ^ k)
    (tgt : Fin (2 ^ h)) :
    out >>> (k - h) = tgt.val ↔
      ∀ c : ℕ, c < h → toW k out ((k - h + c : ℕ) : ZMod k) = b2z (tgt.val.testBit c) := by
  constructor
  · intro heq c hc
    dsimp only [toW]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hb : (out >>> (k - h)).testBit c = tgt.val.testBit c := by rw [heq]
    rw [Nat.testBit_shiftRight] at hb
    rw [hb]
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro c
    rw [Nat.testBit_shiftRight]
    by_cases hc : c < h
    · have h1 := hall c hc
      dsimp only [toW, b2z] at h1
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at h1
      cases ha : out.testBit (k - h + c) <;> cases hb : tgt.val.testBit c
      · rfl
      · rw [ha, hb] at h1; exact absurd h1 (by decide)
      · rw [ha, hb] at h1; exact absurd h1 (by decide)
      · rfl
    · have h1 : out.testBit (k - h + c) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hout (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : tgt.val.testBit c = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le tgt.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [h1, h2]

end BitBridge

section CipherPivots

def flp {k : ℕ} (p : ZMod k) (x : ZMod k → ZMod 2) : ZMod k → ZMod 2 :=
  fun i => if i = p then x i + 1 else x i

lemma flp_self {k : ℕ} (p : ZMod k) (x : ZMod k → ZMod 2) :
    flp p x p = x p + 1 := if_pos rfl

lemma flp_ne {k : ℕ} {p i : ZMod k} (h : i ≠ p) (x : ZMod k → ZMod 2) :
    flp p x i = x i := if_neg h

lemma flp_eq_add {k : ℕ} (p : ZMod k) (x : ZMod k → ZMod 2) :
    flp p x = x + fun i => if i = p then 1 else 0 := by
  funext i
  by_cases h : i = p
  · subst h; simp only [flp, Pi.add_apply, ↓reduceIte]
  · simp only [flp, Pi.add_apply, h, ↓reduceIte, add_zero]

lemma natCast_ne {k : ℕ} (a b : ℕ) (h1 : a < b) (h2 : b < a + k) :
    ((a : ℕ) : ZMod k) ≠ ((b : ℕ) : ZMod k) := by
  intro h
  rw [ZMod.natCast_eq_natCast_iff] at h
  have h3 := (Nat.modEq_iff_dvd' h1.le).mp h
  have h4 := Nat.le_of_dvd (by omega) h3
  omega

lemma nat_ne_zero {k : ℕ} (n : ℕ) (h1 : 0 < n) (h2 : n < k) :
    ((n : ℕ) : ZMod k) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h4 := Nat.le_of_dvd h1 h
  omega

lemma zmod_shift_ne_int {k : ℕ} (p : ZMod k) (a b : ℤ)
    (h1 : 0 < |a - b|) (h2 : |a - b| < (k : ℤ)) :
    p + (a : ZMod k) ≠ p + (b : ZMod k) := by
  intro heq
  have h0 : ((a - b : ℤ) : ZMod k) = 0 := by
    push_cast
    linear_combination heq
  have habs : ((Int.natAbs (a - b) : ℕ) : ℤ) = |a - b| := Int.natCast_natAbs (a - b)
  rcases Int.natAbs_eq (a - b) with hnat | hnat
  · have hcast : ((Int.natAbs (a - b) : ℕ) : ZMod k) = 0 := by
      rw [← Int.cast_natCast, ← hnat]
      exact h0
    exact nat_ne_zero _ (by omega) (by omega) hcast
  · have hcast : ((Int.natAbs (a - b) : ℕ) : ZMod k) = 0 := by
      rw [← Int.cast_natCast]
      have hneg : -((Int.natAbs (a - b) : ℤ) : ZMod k) = 0 := by
        rw [← Int.cast_neg, ← hnat]
        exact h0
      exact neg_eq_zero.mp hneg
    exact nat_ne_zero _ (by omega) (by omega) hcast

lemma halve_mask {k : ℕ} [NeZero k] (A : (ZMod k → ZMod 2) → Prop) (δ : ZMod k → ZMod 2)
    (E : (ZMod k → ZMod 2) → ZMod 2) (t : ZMod 2)
    (hA : ∀ x, A x → A (x + δ))
    (hE : ∀ x, E (x + δ) = E x + 1) :
    2 * Nat.card {x // A x ∧ E x = t} = Nat.card {x // A x} := by
  classical
  have hinv : ∀ x : ZMod k → ZMod 2, (x + δ) + δ = x := fun x => by
    funext i; simp only [Pi.add_apply, add_assoc, zmod2_add_self, add_zero]
  let S0 := Finset.univ.filter fun x : ZMod k → ZMod 2 => A x ∧ E x = t
  let S1 := Finset.univ.filter fun x : ZMod k → ZMod 2 => A x ∧ E x = t + 1
  let SA := Finset.univ.filter fun x : ZMod k → ZMod 2 => A x
  have hcard_eq : S0.card = S1.card := by
    refine Finset.card_nbij' (fun x => x + δ) (fun x => x + δ) ?_ ?_ ?_ ?_
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨_, hAx, hEx⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA x hAx, by rw [hE x, hEx]⟩
    · intro x hx
      rcases Finset.mem_filter.mp hx with ⟨_, hAx, hEx⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA x hAx, ?_⟩
      rw [hE x, hEx, add_assoc, zmod2_add_self, add_zero]
    · intro x _; exact hinv x
    · intro x _; exact hinv x
  have hunion : S0 ∪ S1 = SA := by
    ext x
    simp only [S0, S1, SA, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      have hcases : E x = t ∨ E x = t + 1 := by
        rcases zmod2_eq_zero_or_one (E x) with h0 | h0 <;> rcases zmod2_eq_zero_or_one t with h1 | h1
        · exact Or.inl (h0.trans h1.symm)
        · exact Or.inr (by rw [h0, h1]; rfl)
        · exact Or.inr (by rw [h0, h1]; rfl)
        · exact Or.inl (h0.trans h1.symm)
      rcases hcases with h0 | h1
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
  have hdisj : Disjoint S0 S1 :=
    Finset.disjoint_left.mpr fun x h0 h1 =>
      zmod2_ne_add_one t ((Finset.mem_filter.mp h0).2.2.symm.trans (Finset.mem_filter.mp h1).2.2)
  have hSA : SA.card = 2 * S0.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj, ← hcard_eq, two_mul]
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_subtype]
  exact hSA.symm

lemma tri_mask {k : ℕ} [NeZero k] (A : (ZMod k → ZMod 2) → Prop) :
    ∀ (n : ℕ) (δ : ℕ → ZMod k → ZMod 2) (E : ℕ → (ZMod k → ZMod 2) → ZMod 2) (t : ℕ → ZMod 2),
      (∀ j < n, ∀ x, A x → A (x + δ j)) →
      (∀ j < n, ∀ x, E j (x + δ j) = E j x + 1) →
      (∀ j j', j < j' → j' < n → ∀ x, E j' (x + δ j) = E j' x) →
      2 ^ n * Nat.card {x // A x ∧ ∀ j < n, E j x = t j} = Nat.card {x // A x}
  | 0, _, _, _, _, _, _ => by
    simp only [pow_zero, one_mul, Nat.not_lt_zero, false_implies, implies_true, and_true]
  | n + 1, δ, E, t, hA, hF, hI => by
    have h1 := tri_mask A n (fun j => δ (j + 1)) (fun j => E (j + 1)) (fun j => t (j + 1))
      (fun j hj => hA (j + 1) (by omega))
      (fun j hj => hF (j + 1) (by omega))
      (fun j j' hlt hj' => hI (j + 1) (j' + 1) (by omega) (by omega))
    have h2 := halve_mask (fun x => A x ∧ ∀ j < n, E (j + 1) x = t (j + 1)) (δ 0) (E 0) (t 0)
      (fun x hx => ⟨hA 0 (by omega) x hx.1,
        fun j hj => (hI 0 (j + 1) (by omega) (by omega) x).trans (hx.2 j hj)⟩)
      (hF 0 (by omega))
    have h3 : Nat.card {x // A x ∧ ∀ j < n + 1, E j x = t j} =
        Nat.card {x // (A x ∧ ∀ j < n, E (j + 1) x = t (j + 1)) ∧ E 0 x = t 0} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
      constructor
      · intro hx; exact ⟨⟨hx.1, fun j hj => hx.2 (j + 1) (by omega)⟩, hx.2 0 (by omega)⟩
      · intro hx
        refine ⟨hx.1.1, fun j hj => ?_⟩
        rcases j with _ | j
        · exact hx.2
        · exact hx.1.2 j (by omega)
    rw [h3, pow_succ, mul_assoc, h2]
    exact h1

def Dep {k : ℕ} (F : (ZMod k → ZMod 2) → ZMod k → ZMod 2) (a w : ℕ) : Prop :=
  ∀ (i p : ZMod k), (∀ δ : ℕ, δ < w → p ≠ i - (a : ZMod k) + (δ : ZMod k)) →
    ∀ x, F (flp p x) i = F x i

def Piv {k : ℕ} (F : (ZMod k → ZMod 2) → ZMod k → ZMod 2) (a : ℕ) : Prop :=
  ∀ (i : ZMod k) (x : ZMod k → ZMod 2), F (flp (i - (a : ZMod k)) x) i = F x i + 1

lemma dep_const {k : ℕ} (c : ZMod k → ZMod 2) (a w : ℕ) : Dep (fun _ => c) a w :=
  fun _ _ _ _ => rfl

lemma dep_weaken {k : ℕ} {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ} (hF : Dep F a w)
    (a' w' : ℕ) (ha : a ≤ a') (hw : w + a' - a ≤ w') : Dep F a' w' := by
  intro i p hp x
  refine hF i p (fun δ hδ heq => hp (δ + (a' - a)) (by omega) ?_) x
  rw [heq, Nat.cast_add, Nat.cast_sub ha]
  ring

lemma dep_add {k : ℕ} {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ}
    (hF : Dep F a w) (hG : Dep G a w) : Dep (fun x => F x + G x) a w := by
  intro i p hp x
  show F (flp p x) i + G (flp p x) i = F x i + G x i
  rw [hF i p hp x, hG i p hp x]

lemma dep_turn {k : ℕ} (d : ℕ) : Dep (fun x : ZMod k → ZMod 2 => turn d x) d 1 := by
  intro i p hp x
  refine flp_ne ?_ x
  intro heq
  exact hp 0 (by omega) (by rw [← heq, Nat.cast_zero, add_zero])

lemma piv_turn {k : ℕ} (d : ℕ) : Piv (fun x : ZMod k → ZMod 2 => turn d x) d :=
  fun i x => flp_self (i - (d : ZMod k)) x

lemma dep_id {k : ℕ} : Dep (fun x : ZMod k → ZMod 2 => x) 0 1 := by
  intro i p hp x
  refine flp_ne ?_ x
  intro heq
  exact hp 0 (by omega) (by rw [← heq, Nat.cast_zero, sub_zero, add_zero])

lemma piv_id {k : ℕ} : Piv (fun x : ZMod k → ZMod 2 => x) 0 := by
  intro i x
  rw [Nat.cast_zero, sub_zero]
  exact flp_self i x

lemma phi_congr {k : ℕ} (d : ℕ) (s s' : ZMod k → ZMod 2) (i : ZMod k)
    (hs : ∀ ε : ℕ, ε ≤ 2 * d + 2 →
      s (i - (d : ZMod k) + (ε : ZMod k)) = s' (i - (d : ZMod k) + (ε : ZMod k))) :
    chi (mix d s) i = chi (mix d s') i := by
  have e0 : s (i - (d : ZMod k)) = s' (i - (d : ZMod k)) := by
    have h := hs 0 (by omega); rwa [Nat.cast_zero, add_zero] at h
  have e1 : s i = s' i := by
    have h := hs d (by omega); rwa [sub_add_cancel] at h
  have e2 : s (i + (d : ZMod k)) = s' (i + (d : ZMod k)) := by
    have h := hs (2 * d) (by omega)
    have e : i - (d : ZMod k) + ((2 * d : ℕ) : ZMod k) = i + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e3 : s (i + 1 - (d : ZMod k)) = s' (i + 1 - (d : ZMod k)) := by
    have h := hs 1 (by omega)
    have e : i - (d : ZMod k) + ((1 : ℕ) : ZMod k) = i + 1 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e4 : s (i + 1) = s' (i + 1) := by
    have h := hs (d + 1) (by omega)
    have e : i - (d : ZMod k) + ((d + 1 : ℕ) : ZMod k) = i + 1 := by push_cast; ring
    rwa [e] at h
  have e5 : s (i + 1 + (d : ZMod k)) = s' (i + 1 + (d : ZMod k)) := by
    have h := hs (2 * d + 1) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 1 : ℕ) : ZMod k) = i + 1 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e6 : s (i + 2 - (d : ZMod k)) = s' (i + 2 - (d : ZMod k)) := by
    have h := hs 2 (by omega)
    have e : i - (d : ZMod k) + ((2 : ℕ) : ZMod k) = i + 2 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e7 : s (i + 2) = s' (i + 2) := by
    have h := hs (d + 2) (by omega)
    have e : i - (d : ZMod k) + ((d + 2 : ℕ) : ZMod k) = i + 2 := by push_cast; ring
    rwa [e] at h
  have e8 : s (i + 2 + (d : ZMod k)) = s' (i + 2 + (d : ZMod k)) := by
    have h := hs (2 * d + 2) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 2 : ℕ) : ZMod k) = i + 2 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  show s (i - (d : ZMod k)) + s i + s (i + (d : ZMod k)) +
      (1 + (s (i + 1 - (d : ZMod k)) + s (i + 1) + s (i + 1 + (d : ZMod k)))) *
        (s (i + 2 - (d : ZMod k)) + s (i + 2) + s (i + 2 + (d : ZMod k))) =
    s' (i - (d : ZMod k)) + s' i + s' (i + (d : ZMod k)) +
      (1 + (s' (i + 1 - (d : ZMod k)) + s' (i + 1) + s' (i + 1 + (d : ZMod k)))) *
        (s' (i + 2 - (d : ZMod k)) + s' (i + 2) + s' (i + 2 + (d : ZMod k)))
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]

lemma phi_flip {k : ℕ} (d : ℕ) (hd : 1 ≤ d) (s s' : ZMod k → ZMod 2) (i : ZMod k)
    (h0 : s (i - (d : ZMod k)) = s' (i - (d : ZMod k)) + 1)
    (hs : ∀ ε : ℕ, 1 ≤ ε → ε ≤ 2 * d + 2 →
      s (i - (d : ZMod k) + (ε : ZMod k)) = s' (i - (d : ZMod k) + (ε : ZMod k))) :
    chi (mix d s) i = chi (mix d s') i + 1 := by
  have e1 : s i = s' i := by
    have h := hs d hd (by omega); rwa [sub_add_cancel] at h
  have e2 : s (i + (d : ZMod k)) = s' (i + (d : ZMod k)) := by
    have h := hs (2 * d) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 * d : ℕ) : ZMod k) = i + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e3 : s (i + 1 - (d : ZMod k)) = s' (i + 1 - (d : ZMod k)) := by
    have h := hs 1 (by omega) (by omega)
    have e : i - (d : ZMod k) + ((1 : ℕ) : ZMod k) = i + 1 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e4 : s (i + 1) = s' (i + 1) := by
    have h := hs (d + 1) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((d + 1 : ℕ) : ZMod k) = i + 1 := by push_cast; ring
    rwa [e] at h
  have e5 : s (i + 1 + (d : ZMod k)) = s' (i + 1 + (d : ZMod k)) := by
    have h := hs (2 * d + 1) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 1 : ℕ) : ZMod k) = i + 1 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e6 : s (i + 2 - (d : ZMod k)) = s' (i + 2 - (d : ZMod k)) := by
    have h := hs 2 (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 : ℕ) : ZMod k) = i + 2 - (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  have e7 : s (i + 2) = s' (i + 2) := by
    have h := hs (d + 2) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((d + 2 : ℕ) : ZMod k) = i + 2 := by push_cast; ring
    rwa [e] at h
  have e8 : s (i + 2 + (d : ZMod k)) = s' (i + 2 + (d : ZMod k)) := by
    have h := hs (2 * d + 2) (by omega) (by omega)
    have e : i - (d : ZMod k) + ((2 * d + 2 : ℕ) : ZMod k) = i + 2 + (d : ZMod k) := by push_cast; ring
    rwa [e] at h
  show s (i - (d : ZMod k)) + s i + s (i + (d : ZMod k)) +
      (1 + (s (i + 1 - (d : ZMod k)) + s (i + 1) + s (i + 1 + (d : ZMod k)))) *
        (s (i + 2 - (d : ZMod k)) + s (i + 2) + s (i + 2 + (d : ZMod k))) =
    s' (i - (d : ZMod k)) + s' i + s' (i + (d : ZMod k)) +
      (1 + (s' (i + 1 - (d : ZMod k)) + s' (i + 1) + s' (i + 1 + (d : ZMod k)))) *
        (s' (i + 2 - (d : ZMod k)) + s' (i + 2) + s' (i + 2 + (d : ZMod k))) + 1
  rw [h0, e1, e2, e3, e4, e5, e6, e7, e8]
  ring

lemma dep_phi {k : ℕ} (d : ℕ) {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ}
    (hF : Dep F a w) : Dep (fun x => chi (mix d (F x))) (a + d) (w + 2 * d + 2) := by
  intro i p hp x
  refine phi_congr d _ _ i (fun ε hε => hF _ p (fun δ hδ heq => hp (ε + δ) (by omega) ?_) x)
  rw [heq]; push_cast; ring

lemma piv_phi {k : ℕ} (d : ℕ) (hd : 1 ≤ d) {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ}
    (hk : w + 2 * d + 1 < k) (hF : Dep F a w) (hP : Piv F a) :
    Piv (fun x => chi (mix d (F x))) (a + d) := by
  intro i x
  refine phi_flip d hd _ _ i ?_ ?_
  · have h := hP (i - (d : ZMod k)) x
    have e : i - ((a + d : ℕ) : ZMod k) = i - (d : ZMod k) - (a : ZMod k) := by push_cast; ring
    rwa [e]
  · intro ε h1 h2
    refine hF _ _ (fun δ hδ heq => ?_) x
    have h0 : ((ε + δ : ℕ) : ZMod k) = 0 := by
      push_cast at heq ⊢
      linear_combination -heq
    exact nat_ne_zero (ε + δ) (by omega) (by omega) h0

lemma piv_add_left {k : ℕ} {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a : ℕ} (hF : Piv F a)
    (hG : ∀ (i : ZMod k) (x : ZMod k → ZMod 2), G (flp (i - (a : ZMod k)) x) i = G x i) :
    Piv (fun x => F x + G x) a := by
  intro i x
  show F (flp (i - (a : ZMod k)) x) i + G (flp (i - (a : ZMod k)) x) i = F x i + G x i + 1
  rw [hF i x, hG i x]
  ring

lemma piv_add_right {k : ℕ} {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a : ℕ}
    (hF : ∀ (i : ZMod k) (x : ZMod k → ZMod 2), F (flp (i - (a : ZMod k)) x) i = F x i)
    (hG : Piv G a) : Piv (fun x => F x + G x) a := by
  intro i x
  show F (flp (i - (a : ZMod k)) x) i + G (flp (i - (a : ZMod k)) x) i = F x i + G x i + 1
  rw [hF i x, hG i x]
  ring

lemma dep_left {k : ℕ} {G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a' w' : ℕ} (hG : Dep G a' w')
    (a : ℕ) (h1 : a' < a) (h2 : w' + a - a' ≤ k) (i : ZMod k) (x : ZMod k → ZMod 2) :
    G (flp (i - (a : ZMod k)) x) i = G x i := by
  refine hG _ _ (fun δ hδ heq => ?_) x
  have h0 : ((δ + (a - a') : ℕ) : ZMod k) = 0 := by
    rw [Nat.cast_add, Nat.cast_sub h1.le]
    linear_combination -heq
  exact nat_ne_zero _ (by omega) (by omega) h0

lemma dep_cancel_piv {k : ℕ} {F G : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ}
    (ha : 1 ≤ a) (hw : 1 ≤ w) (hF : Dep F a w) (hPF : Piv F a) (hPG : Piv G a)
    (hG : Dep G a 1) : Dep (fun x => F x + G x) (a - 1) (w - 1) := by
  intro i p hp x
  by_cases hpa : p = i - (a : ZMod k)
  · subst hpa
    show F (flp (i - (a : ZMod k)) x) i + G (flp (i - (a : ZMod k)) x) i = F x i + G x i
    rw [hPF i x, hPG i x]
    have h1 : (F x i + 1) + (G x i + 1) = F x i + G x i + (1 + 1) := by ring
    rw [h1, zmod2_add_self, add_zero]
  · have hFp : F (flp p x) i = F x i := by
      refine hF i p (fun δ hδ heq => ?_) x
      rcases δ with _ | δ'
      · simp only [Nat.cast_zero, add_zero] at heq; exact hpa heq
      · refine hp δ' (by omega) ?_
        rw [heq, Nat.cast_sub ha, Nat.cast_one, Nat.cast_add, Nat.cast_one]
        ring
    have hGp : G (flp p x) i = G x i := by
      refine hG i p (fun δ hδ heq => ?_) x
      have h0 : δ = 0 := by omega
      subst h0
      simp only [Nat.cast_zero, add_zero] at heq
      exact hpa heq
    show F (flp p x) i + G (flp p x) i = F x i + G x i
    rw [hFp, hGp]

lemma dep_congr_set {k : ℕ} [NeZero k] {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2} {a w : ℕ}
    (hF : Dep F a w) (i : ZMod k) (x y : ZMod k → ZMod 2)
    (hxy : ∀ δ : ℕ, δ < w →
      x (i - (a : ZMod k) + (δ : ZMod k)) = y (i - (a : ZMod k) + (δ : ZMod k))) :
    F x i = F y i := by
  classical
  let D : Finset (ZMod k) := Finset.univ.filter (fun p => x p ≠ y p)
  have haux : ∀ (S : Finset (ZMod k)) (x : ZMod k → ZMod 2),
      (∀ p ∈ S, ∀ δ < w, p ≠ i - (a : ZMod k) + (δ : ZMod k)) →
      (∀ p, x p ≠ y p → p ∈ S) → F x i = F y i := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro x _ hsub
      have hxeq : x = y := funext fun p => by_contra fun hne => Finset.notMem_empty p (hsub p hne)
      rw [hxeq]
    | insert q s hqs ih =>
      intro x hforb hsub
      by_cases hxq : x q = y q
      · exact ih x (fun p hp => hforb p (Finset.mem_insert_of_mem hp)) (fun p hp =>
          (Finset.mem_insert.mp (hsub p hp)).resolve_left fun h => hp (h ▸ hxq))
      · have hflip : F (flp q x) i = F x i := hF i q (hforb q (Finset.mem_insert_self q s)) x
        rw [← hflip]
        refine ih (flp q x) (fun p hp => hforb p (Finset.mem_insert_of_mem hp)) (fun p hp => ?_)
        by_cases hpq : p = q
        · subst hpq
          exfalso
          have h1 : x p ≠ y p := hxq
          have h2 : flp p x p = x p + 1 := flp_self p x
          have hx_cases : x p = 0 ∨ x p = 1 := zmod2_eq_zero_or_one (x p)
          have hy_cases : y p = 0 ∨ y p = 1 := zmod2_eq_zero_or_one (y p)
          rcases hx_cases with h0 | h0 <;> rcases hy_cases with h1' | h1'
          · exact h1 (h0.trans h1'.symm)
          · exact hp (by rw [h2, h0, h1']; decide)
          · exact hp (by rw [h2, h0, h1']; decide)
          · exact h1 (h0.trans h1'.symm)
        · rw [flp_ne hpq] at hp
          exact (Finset.mem_insert.mp (hsub p hp)).resolve_left hpq
  refine haux D x (fun p hp δ hδ heq => ?_)
    (fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩)
  exact (Finset.mem_filter.mp hp).2 (heq ▸ hxy δ hδ)

lemma row_name_dep {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun u => rowSt cr u key t) t (4 * t + 1) := by
  induction t with
  | zero => exact dep_add (dep_const (turn 1 key) 0 1) dep_id
  | succ t ih =>
    exact dep_weaken (dep_add (dep_add (dep_phi 1 ih) (dep_const (turn (2 * t) key) _ _))
      (dep_const (cr t) _ _)) _ _ (by omega) (by omega)

lemma row_name_piv {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ)
    (hk : 4 * t < k) : Piv (fun u => rowSt cr u key t) t := by
  induction t with
  | zero => exact piv_add_right (fun _ _ => rfl) piv_id
  | succ t ih =>
    exact piv_add_left (piv_add_left
      (piv_phi 1 le_rfl (by omega) (row_name_dep cr key t) (ih (by omega))) (fun _ _ => rfl))
      (fun _ _ => rfl)

lemma col_name_dep {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun v => colSt cc v key t) (2 * t) (6 * t + 1) := by
  induction t with
  | zero => exact dep_add (dep_const (turn 3 key) 0 1) dep_id
  | succ t ih =>
    exact dep_weaken (dep_add (dep_add (dep_phi 2 ih)
      (dep_const (turn (3 * (t + 1) + 1) key) _ _)) (dep_const (cc t) _ _)) _ _
      (by omega) (by omega)

lemma col_name_piv {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (key : ZMod k → ZMod 2) (t : ℕ)
    (hk : 6 * t < k) : Piv (fun v => colSt cc v key t) (2 * t) := by
  induction t with
  | zero => exact piv_add_right (fun _ _ => rfl) piv_id
  | succ t ih =>
    exact piv_add_left (piv_add_left
      (piv_phi 2 (by omega) (by omega) (col_name_dep cc key t) (ih (by omega))) (fun _ _ => rfl))
      (fun _ _ => rfl)

lemma row_key_dep {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun key => rowSt cr u key t) (max (t + 1) (2 * t - 2))
      (max (t + 1) (2 * t - 2) + 3 * t) := by
  induction t with
  | zero => exact dep_weaken (dep_add (dep_turn 1) (dep_const u 1 1)) _ _ (by omega) (by omega)
  | succ t ih =>
    have hA := dep_weaken (dep_phi 1 ih) (max (t + 1 + 1) (2 * (t + 1) - 2))
      (max (t + 1 + 1) (2 * (t + 1) - 2) + 3 * (t + 1)) (by omega) (by omega)
    have hB := dep_weaken (dep_turn (k := k) (2 * t)) (max (t + 1 + 1) (2 * (t + 1) - 2))
      (max (t + 1 + 1) (2 * (t + 1) - 2) + 3 * (t + 1)) (by omega) (by omega)
    exact dep_add (dep_add hA hB) (dep_const (cr t) _ _)

lemma col_key_dep {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (t : ℕ) :
    Dep (fun key => colSt cc v key t) (max (2 * t + 3) (3 * t + 1))
      (max (2 * t + 3) (3 * t + 1) + 4 * t - 2) := by
  induction t with
  | zero => exact dep_weaken (dep_add (dep_turn 3) (dep_const v 3 1)) _ _ (by omega) (by omega)
  | succ t ih =>
    have hA := dep_weaken (dep_phi 2 ih) (max (2 * (t + 1) + 3) (3 * (t + 1) + 1))
      (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) + 4 * (t + 1) - 2) (by omega) (by omega)
    have hB := dep_weaken (dep_turn (k := k) (3 * (t + 1) + 1))
      (max (2 * (t + 1) + 3) (3 * (t + 1) + 1))
      (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) + 4 * (t + 1) - 2) (by omega) (by omega)
    exact dep_add (dep_add hA hB) (dep_const (cc t) _ _)

lemma row_key_piv_zero {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) :
    Piv (fun key => rowSt cr u key 0) 1 :=
  piv_add_left (piv_turn 1) (fun _ _ => rfl)

lemma col_key_piv_zero {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) :
    Piv (fun key => colSt cc v key 0) 3 :=
  piv_add_left (piv_turn 3) (fun _ _ => rfl)

lemma row_key_piv_one {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (hk : 4 < k) :
    Piv (fun key => rowSt cr u key 1) 2 := by
  have hP0 : Piv (fun key : ZMod k → ZMod 2 => turn 1 key + u) 1 :=
    piv_add_left (piv_turn 1) (fun _ _ => rfl)
  have hD0 : Dep (fun key : ZMod k → ZMod 2 => turn 1 key + u) 1 1 :=
    dep_add (dep_turn 1) (dep_const u 1 1)
  have hP := piv_phi 1 le_rfl (by omega) hD0 hP0
  have hL := dep_left (dep_turn (k := k) 0) 2 (by omega) (by omega)
  exact piv_add_left (piv_add_left hP hL) (fun _ _ => rfl)

lemma col_key_piv_one {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (hk : 6 < k) :
    Piv (fun key => colSt cc v key 1) 5 := by
  have hP0 : Piv (fun key : ZMod k → ZMod 2 => turn 3 key + v) 3 :=
    piv_add_left (piv_turn 3) (fun _ _ => rfl)
  have hD0 : Dep (fun key : ZMod k → ZMod 2 => turn 3 key + v) 3 1 :=
    dep_add (dep_turn 3) (dep_const v 3 1)
  have hP := piv_phi 2 (by omega) (by omega) hD0 hP0
  have hL := dep_left (dep_turn (k := k) 4) 5 (by omega) (by omega)
  exact piv_add_left (piv_add_left hP hL) (fun _ _ => rfl)

lemma row_key_piv_two {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (hk : 8 < k) :
    Piv (fun key => rowSt cr u key 2) 3 := by
  have hD1 : Dep (fun key => rowSt cr u key 1) 2 5 := row_key_dep cr u 1
  have hP1 : Piv (fun key => rowSt cr u key 1) 2 := row_key_piv_one cr u (by omega)
  have hP := piv_phi 1 le_rfl (by omega) hD1 hP1
  have hL := dep_left (dep_turn (k := k) 2) 3 (by omega) (by omega)
  exact piv_add_left (piv_add_left hP hL) (fun _ _ => rfl)

lemma row_key_piv_big {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2) (t : ℕ) (ht : 3 ≤ t)
    (hk : 5 * t + 3 ≤ k) : Piv (fun key => rowSt cr u key (t + 1)) (2 * t) := by
  have hD := dep_phi 1 (row_key_dep cr u t)
  have hL := dep_left hD (2 * t) (by omega) (by omega)
  exact piv_add_left (piv_add_right hL (piv_turn (2 * t))) (fun _ _ => rfl)

lemma col_key_piv_big {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (t : ℕ) (ht : 2 ≤ t)
    (hk : 7 * t + 6 ≤ k) : Piv (fun key => colSt cc v key (t + 1)) (3 * (t + 1) + 1) := by
  have hD := dep_phi 2 (col_key_dep cc v t)
  have hL := dep_left hD (3 * (t + 1) + 1) (by omega) (by omega)
  exact piv_add_left (piv_add_right hL (piv_turn (3 * (t + 1) + 1))) (fun _ _ => rfl)

lemma col_key_dep_two_sharp {k : ℕ} (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2)
    (hk : 12 < k) : Dep (fun key => colSt cc v key 2) 6 12 := by
  have hD1 : Dep (fun key => colSt cc v key 1) 5 7 := col_key_dep cc v 1
  have hP1 : Piv (fun key => colSt cc v key 1) 5 := col_key_piv_one cc v (by omega)
  have hDphi : Dep (fun key => chi (mix 2 (colSt cc v key 1))) 7 13 := dep_phi 2 hD1
  have hPphi : Piv (fun key => chi (mix 2 (colSt cc v key 1))) 7 :=
    piv_phi 2 (by omega) (by omega) hD1 hP1
  have hcancel : Dep (fun key => chi (mix 2 (colSt cc v key 1)) + turn 7 key) 6 12 :=
    dep_cancel_piv (by omega) (by omega) hDphi hPphi (piv_turn 7) (dep_turn 7)
  exact dep_add hcancel (dep_const (cc 1) 6 12)

lemma row_key_dep_three_sharp {k : ℕ} (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2)
    (hk : 12 < k) : Dep (fun key => rowSt cr u key 3) 3 12 := by
  have hD2 : Dep (fun key => rowSt cr u key 2) 3 9 := row_key_dep cr u 2
  have hP2 : Piv (fun key => rowSt cr u key 2) 3 := row_key_piv_two cr u (by omega)
  have hDphi : Dep (fun key => chi (mix 1 (rowSt cr u key 2))) 4 13 := dep_phi 1 hD2
  have hPphi : Piv (fun key => chi (mix 1 (rowSt cr u key 2))) 4 :=
    piv_phi 1 le_rfl (by omega) hD2 hP2
  have hcancel : Dep (fun key => chi (mix 1 (rowSt cr u key 2)) + turn 4 key) 3 12 :=
    dep_cancel_piv (by omega) (by omega) hDphi hPphi (piv_turn 4) (dep_turn 4)
  exact dep_add hcancel (dep_const (cr 2) 3 12)

def maskInt {k : ℕ} (p : ZMod k) (offs : List ℤ) : ZMod k → ZMod 2 :=
  fun i => if offs.any (fun (b : ℤ) => decide (i = p + (b : ZMod k))) then 1 else 0

lemma maskInt_apply_of_lt {k : ℕ} (p : ZMod k) (offs : List ℤ) (a : ℤ)
    (hdist : ∀ b ∈ offs, |a - b| < (k : ℤ)) :
    maskInt p offs (p + (a : ZMod k)) = if a ∈ offs then 1 else 0 := by
  dsimp only [maskInt]
  by_cases ha : a ∈ offs
  · have hany : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k))) = true :=
      List.any_eq_true.mpr ⟨a, ha, decide_eq_true rfl⟩
    rw [hany, if_pos rfl, if_pos ha]
  · have hnot : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k))) = false := by
      by_contra h
      have htrue : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k))) = true := by
        cases hv : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k)))
        · exact absurd hv h
        · rfl
      obtain ⟨b, hb, hdec⟩ := List.any_eq_true.mp htrue
      have heq : p + (a : ZMod k) = p + (b : ZMod k) := of_decide_eq_true hdec
      have hne : a ≠ b := fun h0 => ha (h0 ▸ hb)
      exact zmod_shift_ne_int p a b (abs_pos.mpr (sub_ne_zero.mpr hne)) (hdist b hb) heq
    rw [hnot, if_neg Bool.false_ne_true, if_neg ha]

lemma maskInt_zero_of_lt {k : ℕ} (p : ZMod k) (offs : List ℤ) (a : ℤ)
    (hdist : ∀ b ∈ offs, 0 < |a - b| ∧ |a - b| < (k : ℤ)) :
    maskInt p offs (p + (a : ZMod k)) = 0 := by
  dsimp only [maskInt]
  have hnot : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k))) = false := by
    by_contra h
    have htrue : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k))) = true := by
      cases hv : offs.any (fun (b : ℤ) => decide (p + (a : ZMod k) = p + (b : ZMod k)))
      · exact absurd hv h
      · rfl
    obtain ⟨b, hb, hdec⟩ := List.any_eq_true.mp htrue
    have hd := hdist b hb
    exact zmod_shift_ne_int p a b hd.1 hd.2 (of_decide_eq_true hdec)
  rw [hnot, if_neg Bool.false_ne_true]

lemma mix_add_linear {k : ℕ} (d : ℕ) (x y : ZMod k → ZMod 2) :
    mix d (x + y) = mix d x + mix d y := by
  funext i; simp only [mix, Pi.add_apply]; ring

lemma turn_add_linear {k : ℕ} (d : ℕ) (x y : ZMod k → ZMod 2) :
    turn d (x + y) = turn d x + turn d y := by
  funext i; simp only [turn, Pi.add_apply]

lemma chi_add_at {k : ℕ} (y y' : ZMod k → ZMod 2) (i : ZMod k)
    (h0 : y' i = y i + 1) (h1 : y' (i + 1) = y (i + 1)) (h2 : y' (i + 2) = y (i + 2)) :
    chi y' i = chi y i + 1 := by
  simp only [chi, h0, h1, h2]; ring

lemma chi_eq_at {k : ℕ} (y y' : ZMod k → ZMod 2) (i : ZMod k)
    (h0 : y' i = y i) (h1 : y' (i + 1) = y (i + 1)) (h2 : y' (i + 2) = y (i + 2)) :
    chi y' i = chi y i := by
  simp only [chi, h0, h1, h2]

lemma col2_packet_flip {k : ℕ} (hk : 13 ≤ k) (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2)
    (p : ZMod k) (key : ZMod k → ZMod 2) :
    let Δ : ZMod k → ZMod 2 := maskInt p [-3, -1, 3, 5]
    colSt cc v (key + Δ) 2 p = colSt cc v key 2 p + 1 ∧
    colSt cc v (key + Δ) 2 (p + 1) = colSt cc v key 2 (p + 1) ∧
    colSt cc v (key + Δ) 2 (p + 2) = colSt cc v key 2 (p + 2) ∧
    colSt cc v (key + Δ) 2 (p + 3) = colSt cc v key 2 (p + 3) := by
  intro Δ
  have hΔ : ∀ a : ℤ, -7 ≤ a → a ≤ 8 →
      Δ (p + (a : ZMod k)) = if a ∈ ([-3, -1, 3, 5] : List ℤ) then 1 else 0 := by
    intro a h1 h2
    refine maskInt_apply_of_lt p [-3, -1, 3, 5] a fun b hb => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> exact abs_lt.mpr ⟨by omega, by omega⟩
  have hmix0 : ∀ a : ℤ, -2 ≤ a → a ≤ 9 →
      mix 2 (turn 3 Δ) (p + (a : ZMod k)) = if a = -2 then 1 else 0 := by
    intro a h1 h2
    dsimp only [mix, turn]
    simp only [Nat.cast_ofNat]
    have e1 : p + (a : ZMod k) - (2 : ZMod k) - (3 : ZMod k) = p + ((a - 5 : ℤ) : ZMod k) := by
      push_cast; ring
    have e2 : p + (a : ZMod k) - (3 : ZMod k) = p + ((a - 3 : ℤ) : ZMod k) := by
      push_cast; ring
    have e3 : p + (a : ZMod k) + (2 : ZMod k) - (3 : ZMod k) = p + ((a - 1 : ℤ) : ZMod k) := by
      push_cast; ring
    rw [e1, e2, e3, hΔ (a - 5) (by omega) (by omega), hΔ (a - 3) (by omega) (by omega),
      hΔ (a - 1) (by omega) (by omega)]
    interval_cases a <;> decide
  let s0 := colSt cc v key 0
  let s0' := colSt cc v (key + Δ) 0
  have hs0' : s0' = s0 + turn 3 Δ := by
    funext i; simp only [s0', s0, colSt, turn_add_linear, Pi.add_apply]; ring
  have hmy0 : ∀ a : ℤ, -2 ≤ a → a ≤ 9 →
      mix 2 s0' (p + (a : ZMod k)) = mix 2 s0 (p + (a : ZMod k)) + if a = -2 then 1 else 0 := by
    intro a h1 h2
    rw [hs0', mix_add_linear, Pi.add_apply, hmix0 a h1 h2]
  have hs1 : ∀ a : ℤ, -2 ≤ a → a ≤ 7 →
      colSt cc v (key + Δ) 1 (p + (a : ZMod k)) =
        colSt cc v key 1 (p + (a : ZMod k)) +
          if a = -2 ∨ a = 1 ∨ a = 3 ∨ a = 7 then 1 else 0 := by
    intro a h1 h2
    change chi (mix 2 s0') (p + (a : ZMod k)) + turn 4 (key + Δ) (p + (a : ZMod k)) + cc 0 _ =
      chi (mix 2 s0) (p + (a : ZMod k)) + turn 4 key (p + (a : ZMod k)) + cc 0 _ + _
    have ht4 : turn 4 (key + Δ) (p + (a : ZMod k)) =
        turn 4 key (p + (a : ZMod k)) + Δ (p + ((a - 4 : ℤ) : ZMod k)) := by
      rw [turn_add_linear, Pi.add_apply]
      dsimp only [turn]
      simp only [Nat.cast_ofNat]
      have e : p + (a : ZMod k) - (4 : ZMod k) = p + ((a - 4 : ℤ) : ZMod k) := by push_cast; ring
      rw [e]
    rw [ht4, hΔ (a - 4) (by omega) (by omega)]
    have hp1 : p + (a : ZMod k) + 1 = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    have hp2 : p + (a : ZMod k) + 2 = p + ((a + 2 : ℤ) : ZMod k) := by push_cast; ring
    have hchi : chi (mix 2 s0') (p + (a : ZMod k)) =
        chi (mix 2 s0) (p + (a : ZMod k)) + if a = -2 then 1 else 0 := by
      by_cases ha : a = -2
      · subst ha
        rw [if_pos rfl]
        refine chi_add_at (mix 2 s0) (mix 2 s0') (p + ((-2 : ℤ) : ZMod k)) ?_ ?_ ?_
        · simpa using hmy0 (-2) (by omega) (by omega)
        · rw [hp1]; simpa using hmy0 (-1) (by omega) (by omega)
        · rw [hp2]; simpa using hmy0 0 (by omega) (by omega)
      · rw [if_neg ha, add_zero]
        refine chi_eq_at (mix 2 s0) (mix 2 s0') (p + (a : ZMod k)) ?_ ?_ ?_
        · have h := hmy0 a h1 (by omega)
          rw [if_neg ha, add_zero] at h
          exact h
        · rw [hp1]
          have h := hmy0 (a + 1) (by omega) (by omega)
          have hne : a + 1 ≠ -2 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
        · rw [hp2]
          have h := hmy0 (a + 2) (by omega) (by omega)
          have hne : a + 2 ≠ -2 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
    rw [hchi]
    have hcomb : (if a = -2 then (1 : ZMod 2) else 0) +
        (if a - 4 ∈ ([-3, -1, 3, 5] : List ℤ) then 1 else 0) =
        if a = -2 ∨ a = 1 ∨ a = 3 ∨ a = 7 then 1 else 0 := by
      interval_cases a <;> decide
    calc
      chi (mix 2 s0) (p + (a : ZMod k)) + (if a = -2 then 1 else 0) +
          (turn 4 key (p + (a : ZMod k)) + if a - 4 ∈ ([-3, -1, 3, 5] : List ℤ) then 1 else 0) +
          cc 0 (p + (a : ZMod k))
        = chi (mix 2 s0) (p + (a : ZMod k)) + turn 4 key (p + (a : ZMod k)) +
            cc 0 (p + (a : ZMod k)) +
            ((if a = -2 then 1 else 0) + if a - 4 ∈ ([-3, -1, 3, 5] : List ℤ) then 1 else 0) := by ring
      _ = _ := by rw [hcomb]
  have hmix1 : ∀ a : ℤ, 0 ≤ a → a ≤ 5 →
      mix 2 (colSt cc v (key + Δ) 1) (p + (a : ZMod k)) =
        mix 2 (colSt cc v key 1) (p + (a : ZMod k)) + if a = 0 then 1 else 0 := by
    intro a h1 h2
    dsimp only [mix]
    simp only [Nat.cast_ofNat]
    have e1 : p + (a : ZMod k) - (2 : ZMod k) = p + ((a - 2 : ℤ) : ZMod k) := by push_cast; ring
    have e2 : p + (a : ZMod k) + (2 : ZMod k) = p + ((a + 2 : ℤ) : ZMod k) := by push_cast; ring
    rw [e1, e2, hs1 (a - 2) (by omega) (by omega), hs1 a (by omega) (by omega),
      hs1 (a + 2) (by omega) (by omega)]
    have hsum : (if a - 2 = -2 ∨ a - 2 = 1 ∨ a - 2 = 3 ∨ a - 2 = 7 then (1 : ZMod 2) else 0) +
        (if a = -2 ∨ a = 1 ∨ a = 3 ∨ a = 7 then 1 else 0) +
        (if a + 2 = -2 ∨ a + 2 = 1 ∨ a + 2 = 3 ∨ a + 2 = 7 then 1 else 0) =
        if a = 0 then 1 else 0 := by
      interval_cases a <;> decide
    calc
      (colSt cc v key 1 (p + ((a - 2 : ℤ) : ZMod k)) + _) +
          (colSt cc v key 1 (p + (a : ZMod k)) + _) +
          (colSt cc v key 1 (p + ((a + 2 : ℤ) : ZMod k)) + _)
        = colSt cc v key 1 (p + ((a - 2 : ℤ) : ZMod k)) +
            colSt cc v key 1 (p + (a : ZMod k)) +
            colSt cc v key 1 (p + ((a + 2 : ℤ) : ZMod k)) +
            ((if a - 2 = -2 ∨ a - 2 = 1 ∨ a - 2 = 3 ∨ a - 2 = 7 then 1 else 0) +
             (if a = -2 ∨ a = 1 ∨ a = 3 ∨ a = 7 then 1 else 0) +
             (if a + 2 = -2 ∨ a + 2 = 1 ∨ a + 2 = 3 ∨ a + 2 = 7 then 1 else 0)) := by ring
      _ = _ := by rw [hsum]
  have hs2 : ∀ a : ℤ, 0 ≤ a → a ≤ 3 →
      colSt cc v (key + Δ) 2 (p + (a : ZMod k)) =
        colSt cc v key 2 (p + (a : ZMod k)) + if a = 0 then 1 else 0 := by
    intro a h1 h2
    change chi (mix 2 (colSt cc v (key + Δ) 1)) (p + (a : ZMod k)) +
        turn 7 (key + Δ) (p + (a : ZMod k)) + cc 1 _ =
      chi (mix 2 (colSt cc v key 1)) (p + (a : ZMod k)) +
        turn 7 key (p + (a : ZMod k)) + cc 1 _ + _
    have ht7 : turn 7 (key + Δ) (p + (a : ZMod k)) = turn 7 key (p + (a : ZMod k)) := by
      rw [turn_add_linear, Pi.add_apply]
      dsimp only [turn]
      simp only [Nat.cast_ofNat]
      have e : p + (a : ZMod k) - (7 : ZMod k) = p + ((a - 7 : ℤ) : ZMod k) := by push_cast; ring
      rw [e, hΔ (a - 7) (by omega) (by omega)]
      have h0 : (if a - 7 ∈ ([-3, -1, 3, 5] : List ℤ) then (1 : ZMod 2) else 0) = 0 := by
        interval_cases a <;> decide
      rw [h0, add_zero]
    rw [ht7]
    have hp1 : p + (a : ZMod k) + 1 = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    have hp2 : p + (a : ZMod k) + 2 = p + ((a + 2 : ℤ) : ZMod k) := by push_cast; ring
    have hchi : chi (mix 2 (colSt cc v (key + Δ) 1)) (p + (a : ZMod k)) =
        chi (mix 2 (colSt cc v key 1)) (p + (a : ZMod k)) + if a = 0 then 1 else 0 := by
      by_cases ha : a = 0
      · subst ha
        rw [if_pos rfl]
        refine chi_add_at _ _ (p + ((0 : ℤ) : ZMod k)) ?_ ?_ ?_
        · simpa using hmix1 0 (by omega) (by omega)
        · rw [hp1]; simpa using hmix1 1 (by omega) (by omega)
        · rw [hp2]; simpa using hmix1 2 (by omega) (by omega)
      · rw [if_neg ha, add_zero]
        refine chi_eq_at _ _ (p + (a : ZMod k)) ?_ ?_ ?_
        · have h := hmix1 a h1 (by omega)
          rw [if_neg ha, add_zero] at h
          exact h
        · rw [hp1]
          have h := hmix1 (a + 1) (by omega) (by omega)
          have hne : a + 1 ≠ 0 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
        · rw [hp2]
          have h := hmix1 (a + 2) (by omega) (by omega)
          have hne : a + 2 ≠ 0 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
    rw [hchi]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hs2 0 (by omega) (by omega)
  · simpa using hs2 1 (by omega) (by omega)
  · simpa using hs2 2 (by omega) (by omega)
  · simpa using hs2 3 (by omega) (by omega)

lemma row3_packet_flip {k : ℕ} (hk : 20 ≤ k) (cr : ℕ → ZMod k → ZMod 2) (u : ZMod k → ZMod 2)
    (p : ZMod k) (key : ZMod k → ZMod 2) :
    let Δ : ZMod k → ZMod 2 := maskInt p [-2, -1, 1, 2, 4, 5, 7, 8]
    rowSt cr u (key + Δ) 3 p = rowSt cr u key 3 p + 1 ∧
    rowSt cr u (key + Δ) 3 (p + 1) = rowSt cr u key 3 (p + 1) := by
  intro Δ
  have hΔ : ∀ a : ℤ, -4 ≤ a → a ≤ 9 →
      Δ (p + (a : ZMod k)) = if a ∈ ([-2, -1, 1, 2, 4, 5, 7, 8] : List ℤ) then 1 else 0 := by
    intro a h1 h2
    refine maskInt_apply_of_lt p [-2, -1, 1, 2, 4, 5, 7, 8] a fun b hb => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact abs_lt.mpr ⟨by omega, by omega⟩
  have hmix0 : ∀ a : ℤ, -2 ≤ a → a ≤ 9 →
      mix 1 (turn 1 Δ) (p + (a : ZMod k)) = if a = -2 then 1 else 0 := by
    intro a h1 h2
    dsimp only [mix, turn]
    simp only [Nat.cast_one]
    have e1 : p + (a : ZMod k) - (1 : ZMod k) - (1 : ZMod k) = p + ((a - 2 : ℤ) : ZMod k) := by
      push_cast; ring
    have e2 : p + (a : ZMod k) - (1 : ZMod k) = p + ((a - 1 : ℤ) : ZMod k) := by
      push_cast; ring
    have e3 : p + (a : ZMod k) + (1 : ZMod k) - (1 : ZMod k) = p + (a : ZMod k) := by
      push_cast; ring
    rw [e1, e2, e3, hΔ (a - 2) (by omega) (by omega), hΔ (a - 1) (by omega) (by omega),
      hΔ a (by omega) (by omega)]
    interval_cases a <;> decide
  let s0 := rowSt cr u key 0
  let s0' := rowSt cr u (key + Δ) 0
  have hs0' : s0' = s0 + turn 1 Δ := by
    funext i; simp only [s0', s0, rowSt, turn_add_linear, Pi.add_apply]; ring
  have hmy0 : ∀ a : ℤ, -2 ≤ a → a ≤ 9 →
      mix 1 s0' (p + (a : ZMod k)) = mix 1 s0 (p + (a : ZMod k)) + if a = -2 then 1 else 0 := by
    intro a h1 h2
    rw [hs0', mix_add_linear, Pi.add_apply, hmix0 a h1 h2]
  have hs1 : ∀ a : ℤ, -2 ≤ a → a ≤ 7 →
      rowSt cr u (key + Δ) 1 (p + (a : ZMod k)) =
        rowSt cr u key 1 (p + (a : ZMod k)) +
          if a ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0 := by
    intro a h1 h2
    change chi (mix 1 s0') (p + (a : ZMod k)) + turn 0 (key + Δ) (p + (a : ZMod k)) + cr 0 _ =
      chi (mix 1 s0) (p + (a : ZMod k)) + turn 0 key (p + (a : ZMod k)) + cr 0 _ + _
    have ht0 : turn 0 (key + Δ) (p + (a : ZMod k)) =
        turn 0 key (p + (a : ZMod k)) + Δ (p + (a : ZMod k)) := by
      rw [turn_add_linear, Pi.add_apply]
      simp only [turn, Nat.cast_zero, sub_zero]
    rw [ht0, hΔ a (by omega) (by omega)]
    have hp1 : p + (a : ZMod k) + 1 = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    have hp2 : p + (a : ZMod k) + 2 = p + ((a + 2 : ℤ) : ZMod k) := by push_cast; ring
    have hchi : chi (mix 1 s0') (p + (a : ZMod k)) =
        chi (mix 1 s0) (p + (a : ZMod k)) + if a = -2 then 1 else 0 := by
      by_cases ha : a = -2
      · subst ha
        rw [if_pos rfl]
        refine chi_add_at (mix 1 s0) (mix 1 s0') (p + ((-2 : ℤ) : ZMod k)) ?_ ?_ ?_
        · simpa using hmy0 (-2) (by omega) (by omega)
        · rw [hp1]; simpa using hmy0 (-1) (by omega) (by omega)
        · rw [hp2]; simpa using hmy0 0 (by omega) (by omega)
      · rw [if_neg ha, add_zero]
        refine chi_eq_at (mix 1 s0) (mix 1 s0') (p + (a : ZMod k)) ?_ ?_ ?_
        · have h := hmy0 a h1 (by omega)
          rw [if_neg ha, add_zero] at h
          exact h
        · rw [hp1]
          have h := hmy0 (a + 1) (by omega) (by omega)
          have hne : a + 1 ≠ -2 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
        · rw [hp2]
          have h := hmy0 (a + 2) (by omega) (by omega)
          have hne : a + 2 ≠ -2 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
    rw [hchi]
    have hcomb : (if a = -2 then (1 : ZMod 2) else 0) +
        (if a ∈ ([-2, -1, 1, 2, 4, 5, 7, 8] : List ℤ) then 1 else 0) =
        if a ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0 := by
      interval_cases a <;> decide
    calc
      chi (mix 1 s0) (p + (a : ZMod k)) + (if a = -2 then 1 else 0) +
          (turn 0 key (p + (a : ZMod k)) + _) + cr 0 (p + (a : ZMod k))
        = chi (mix 1 s0) (p + (a : ZMod k)) + turn 0 key (p + (a : ZMod k)) +
            cr 0 (p + (a : ZMod k)) +
            ((if a = -2 then 1 else 0) + if a ∈ ([-2, -1, 1, 2, 4, 5, 7, 8] : List ℤ) then 1 else 0) := by ring
      _ = _ := by rw [hcomb]
  have hmix1 : ∀ a : ℤ, -1 ≤ a → a ≤ 6 →
      mix 1 (rowSt cr u (key + Δ) 1) (p + (a : ZMod k)) =
        mix 1 (rowSt cr u key 1) (p + (a : ZMod k)) + if a = -1 then 1 else 0 := by
    intro a h1 h2
    dsimp only [mix]
    simp only [Nat.cast_one]
    have e1 : p + (a : ZMod k) - (1 : ZMod k) = p + ((a - 1 : ℤ) : ZMod k) := by push_cast; ring
    have e2 : p + (a : ZMod k) + (1 : ZMod k) = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    rw [e1, e2, hs1 (a - 1) (by omega) (by omega), hs1 a (by omega) (by omega),
      hs1 (a + 1) (by omega) (by omega)]
    have hsum : (if a - 1 ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then (1 : ZMod 2) else 0) +
        (if a ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0) +
        (if a + 1 ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0) =
        if a = -1 then 1 else 0 := by
      interval_cases a <;> decide
    calc
      (rowSt cr u key 1 (p + ((a - 1 : ℤ) : ZMod k)) + _) +
          (rowSt cr u key 1 (p + (a : ZMod k)) + _) +
          (rowSt cr u key 1 (p + ((a + 1 : ℤ) : ZMod k)) + _)
        = rowSt cr u key 1 (p + ((a - 1 : ℤ) : ZMod k)) +
            rowSt cr u key 1 (p + (a : ZMod k)) +
            rowSt cr u key 1 (p + ((a + 1 : ℤ) : ZMod k)) +
            ((if a - 1 ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0) +
             (if a ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0) +
             (if a + 1 ∈ ([-1, 1, 2, 4, 5, 7] : List ℤ) then 1 else 0)) := by ring
      _ = _ := by rw [hsum]
  have hs2 : ∀ a : ℤ, -1 ≤ a → a ≤ 4 →
      rowSt cr u (key + Δ) 2 (p + (a : ZMod k)) =
        rowSt cr u key 2 (p + (a : ZMod k)) +
          if a ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0 := by
    intro a h1 h2
    change chi (mix 1 (rowSt cr u (key + Δ) 1)) (p + (a : ZMod k)) +
        turn 2 (key + Δ) (p + (a : ZMod k)) + cr 1 _ =
      chi (mix 1 (rowSt cr u key 1)) (p + (a : ZMod k)) +
        turn 2 key (p + (a : ZMod k)) + cr 1 _ + _
    have ht2 : turn 2 (key + Δ) (p + (a : ZMod k)) =
        turn 2 key (p + (a : ZMod k)) + Δ (p + ((a - 2 : ℤ) : ZMod k)) := by
      rw [turn_add_linear, Pi.add_apply]
      dsimp only [turn]
      simp only [Nat.cast_ofNat]
      have e : p + (a : ZMod k) - (2 : ZMod k) = p + ((a - 2 : ℤ) : ZMod k) := by push_cast; ring
      rw [e]
    rw [ht2, hΔ (a - 2) (by omega) (by omega)]
    have hp1 : p + (a : ZMod k) + 1 = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    have hp2 : p + (a : ZMod k) + 2 = p + ((a + 2 : ℤ) : ZMod k) := by push_cast; ring
    have hchi : chi (mix 1 (rowSt cr u (key + Δ) 1)) (p + (a : ZMod k)) =
        chi (mix 1 (rowSt cr u key 1)) (p + (a : ZMod k)) + if a = -1 then 1 else 0 := by
      by_cases ha : a = -1
      · subst ha
        rw [if_pos rfl]
        refine chi_add_at _ _ (p + ((-1 : ℤ) : ZMod k)) ?_ ?_ ?_
        · simpa using hmix1 (-1) (by omega) (by omega)
        · rw [hp1]; simpa using hmix1 0 (by omega) (by omega)
        · rw [hp2]; simpa using hmix1 1 (by omega) (by omega)
      · rw [if_neg ha, add_zero]
        refine chi_eq_at _ _ (p + (a : ZMod k)) ?_ ?_ ?_
        · have h := hmix1 a h1 (by omega)
          rw [if_neg ha, add_zero] at h
          exact h
        · rw [hp1]
          have h := hmix1 (a + 1) (by omega) (by omega)
          have hne : a + 1 ≠ -1 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
        · rw [hp2]
          have h := hmix1 (a + 2) (by omega) (by omega)
          have hne : a + 2 ≠ -1 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
    rw [hchi]
    have hcomb : (if a = -1 then (1 : ZMod 2) else 0) +
        (if a - 2 ∈ ([-2, -1, 1, 2, 4, 5, 7, 8] : List ℤ) then 1 else 0) =
        if a ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0 := by
      interval_cases a <;> decide
    calc
      chi (mix 1 (rowSt cr u key 1)) (p + (a : ZMod k)) + (if a = -1 then 1 else 0) +
          (turn 2 key (p + (a : ZMod k)) + _) + cr 1 (p + (a : ZMod k))
        = chi (mix 1 (rowSt cr u key 1)) (p + (a : ZMod k)) + turn 2 key (p + (a : ZMod k)) +
            cr 1 (p + (a : ZMod k)) +
            ((if a = -1 then 1 else 0) +
             if a - 2 ∈ ([-2, -1, 1, 2, 4, 5, 7, 8] : List ℤ) then 1 else 0) := by ring
      _ = _ := by rw [hcomb]
  have hmix2 : ∀ a : ℤ, 0 ≤ a → a ≤ 3 →
      mix 1 (rowSt cr u (key + Δ) 2) (p + (a : ZMod k)) =
        mix 1 (rowSt cr u key 2) (p + (a : ZMod k)) + if a = 0 then 1 else 0 := by
    intro a h1 h2
    dsimp only [mix]
    simp only [Nat.cast_one]
    have e1 : p + (a : ZMod k) - (1 : ZMod k) = p + ((a - 1 : ℤ) : ZMod k) := by push_cast; ring
    have e2 : p + (a : ZMod k) + (1 : ZMod k) = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    rw [e1, e2, hs2 (a - 1) (by omega) (by omega), hs2 a (by omega) (by omega),
      hs2 (a + 1) (by omega) (by omega)]
    have hsum : (if a - 1 ∈ ([-1, 0, 1, 3, 4] : List ℤ) then (1 : ZMod 2) else 0) +
        (if a ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0) +
        (if a + 1 ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0) =
        if a = 0 then 1 else 0 := by
      interval_cases a <;> decide
    calc
      (rowSt cr u key 2 (p + ((a - 1 : ℤ) : ZMod k)) + _) +
          (rowSt cr u key 2 (p + (a : ZMod k)) + _) +
          (rowSt cr u key 2 (p + ((a + 1 : ℤ) : ZMod k)) + _)
        = rowSt cr u key 2 (p + ((a - 1 : ℤ) : ZMod k)) +
            rowSt cr u key 2 (p + (a : ZMod k)) +
            rowSt cr u key 2 (p + ((a + 1 : ℤ) : ZMod k)) +
            ((if a - 1 ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0) +
             (if a ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0) +
             (if a + 1 ∈ ([-1, 0, 1, 3, 4] : List ℤ) then 1 else 0)) := by ring
      _ = _ := by rw [hsum]
  have hs3 : ∀ a : ℤ, 0 ≤ a → a ≤ 1 →
      rowSt cr u (key + Δ) 3 (p + (a : ZMod k)) =
        rowSt cr u key 3 (p + (a : ZMod k)) + if a = 0 then 1 else 0 := by
    intro a h1 h2
    change chi (mix 1 (rowSt cr u (key + Δ) 2)) (p + (a : ZMod k)) +
        turn 4 (key + Δ) (p + (a : ZMod k)) + cr 2 _ =
      chi (mix 1 (rowSt cr u key 2)) (p + (a : ZMod k)) +
        turn 4 key (p + (a : ZMod k)) + cr 2 _ + _
    have ht4 : turn 4 (key + Δ) (p + (a : ZMod k)) = turn 4 key (p + (a : ZMod k)) := by
      rw [turn_add_linear, Pi.add_apply]
      dsimp only [turn]
      simp only [Nat.cast_ofNat]
      have e : p + (a : ZMod k) - (4 : ZMod k) = p + ((a - 4 : ℤ) : ZMod k) := by push_cast; ring
      rw [e, hΔ (a - 4) (by omega) (by omega)]
      have h0 : (if a - 4 ∈ ([-2, -1, 1, 2, 4, 5, 7, 8] : List ℤ) then (1 : ZMod 2) else 0) = 0 := by
        interval_cases a <;> decide
      rw [h0, add_zero]
    rw [ht4]
    have hp1 : p + (a : ZMod k) + 1 = p + ((a + 1 : ℤ) : ZMod k) := by push_cast; ring
    have hp2 : p + (a : ZMod k) + 2 = p + ((a + 2 : ℤ) : ZMod k) := by push_cast; ring
    have hchi : chi (mix 1 (rowSt cr u (key + Δ) 2)) (p + (a : ZMod k)) =
        chi (mix 1 (rowSt cr u key 2)) (p + (a : ZMod k)) + if a = 0 then 1 else 0 := by
      by_cases ha : a = 0
      · subst ha
        rw [if_pos rfl]
        refine chi_add_at _ _ (p + ((0 : ℤ) : ZMod k)) ?_ ?_ ?_
        · simpa using hmix2 0 (by omega) (by omega)
        · rw [hp1]; simpa using hmix2 1 (by omega) (by omega)
        · rw [hp2]; simpa using hmix2 2 (by omega) (by omega)
      · rw [if_neg ha, add_zero]
        refine chi_eq_at _ _ (p + (a : ZMod k)) ?_ ?_ ?_
        · have h := hmix2 a h1 (by omega)
          rw [if_neg ha, add_zero] at h
          exact h
        · rw [hp1]
          have h := hmix2 (a + 1) (by omega) (by omega)
          have hne : a + 1 ≠ 0 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
        · rw [hp2]
          have h := hmix2 (a + 2) (by omega) (by omega)
          have hne : a + 2 ≠ 0 := by omega
          rw [if_neg hne, add_zero] at h
          exact h
    rw [hchi]
    ring
  exact ⟨by simpa using hs3 0 (by omega) (by omega), by simpa using hs3 1 (by omega) (by omega)⟩

lemma card_win_eq_of_dep_piv {k h a w : ℕ} [NeZero k]
    {F : (ZMod k → ZMod 2) → ZMod k → ZMod 2}
    (hF : Dep F a w) (hP : Piv F a) (hh : h ≤ k) (hw : w + h ≤ k + 1)
    (tgt : ℕ → ZMod 2) :
    Nat.card {key : ZMod k → ZMod 2 // ∀ c < h, F key ((k - h + c : ℕ) : ZMod k) = tgt c} =
      2 ^ (k - h) := by
  have htri := tri_mask (fun _ : ZMod k → ZMod 2 => True) h
    (fun c i => if i = ((k - h + c : ℕ) : ZMod k) - (a : ZMod k) then 1 else 0)
    (fun c key => F key ((k - h + c : ℕ) : ZMod k))
    tgt
    (fun _ _ _ _ => trivial)
    (fun c _ key => by
      rw [← flp_eq_add]
      exact hP ((k - h + c : ℕ) : ZMod k) key)
    (fun c c' hcc' hc' key => by
      rw [← flp_eq_add]
      refine hF _ _ (fun δ hδ heq => ?_) key
      have h0 : (((c' - c) + δ : ℕ) : ZMod k) = 0 := by
        rw [Nat.cast_add, Nat.cast_sub hcc'.le]
        have heq' : ((k - h + c : ℕ) : ZMod k) - (a : ZMod k) =
            ((k - h + c' : ℕ) : ZMod k) - (a : ZMod k) + (δ : ZMod k) := heq
        push_cast at heq' ⊢
        linear_combination -heq'
      exact nat_ne_zero _ (by omega) (by omega) h0)
  have hU : Nat.card {key : ZMod k → ZMod 2 // True} = 2 ^ k := by
    rw [Nat.card_eq_fintype_card]
    simp [Fintype.card_pi, ZMod.card]
  have hEq : Nat.card {key : ZMod k → ZMod 2 // True ∧ ∀ c < h, F key ((k - h + c : ℕ) : ZMod k) = tgt c} =
      Nat.card {key : ZMod k → ZMod 2 // ∀ c < h, F key ((k - h + c : ℕ) : ZMod k) = tgt c} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩)
  rw [hEq, hU] at htri
  have hpow : 2 ^ k = 2 ^ h * 2 ^ (k - h) := by rw [← pow_add, Nat.add_sub_of_le hh]
  rw [hpow] at htri
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos h) htri

lemma card_win_le_col2 {k h : ℕ} [NeZero k] (hh : 0 < h) (hk : h + 12 ≤ k)
    (cc : ℕ → ZMod k → ZMod 2) (v : ZMod k → ZMod 2) (tgt : ℕ → ZMod 2) :
    let u := 4 * (h / 15) + min 4 (h % 15)
    Nat.card {key : ZMod k → ZMod 2 // ∀ c < h, colSt cc v key 2 ((k - h + c : ℕ) : ZMod k) = tgt c} ≤
      2 ^ (k - u) := by
  intro u
  have hu_le : u ≤ h := by dsimp [u]; omega
  let idx : ℕ → ℕ := fun m => 15 * (m / 4) + m % 4
  have hidx_lt : ∀ m < u, idx m < h := by
    intro m hm; dsimp [idx, u] at hm ⊢; omega
  have hsub : Nat.card {key : ZMod k → ZMod 2 //
        ∀ c < h, colSt cc v key 2 ((k - h + c : ℕ) : ZMod k) = tgt c} ≤
      Nat.card {key : ZMod k → ZMod 2 //
        True ∧ ∀ m < u, colSt cc v key 2 ((k - h + idx m : ℕ) : ZMod k) = tgt (idx m)} := by
    refine Nat.card_le_card_of_injective
      (Subtype.map id fun key hkey => ⟨trivial, fun m hm => hkey (idx m) (hidx_lt m hm)⟩)
      (Subtype.map_injective _ Function.injective_id)
  have hdep := col_key_dep_two_sharp cc v (by omega)
  have htri := tri_mask (fun _ : ZMod k → ZMod 2 => True) u
    (fun m => maskInt ((k - h + idx m : ℕ) : ZMod k) [-3, -1, 3, 5])
    (fun m key => colSt cc v key 2 ((k - h + idx m : ℕ) : ZMod k))
    (fun m => tgt (idx m))
    (fun _ _ _ _ => trivial)
    (fun m _ key => (col2_packet_flip (by omega) cc v ((k - h + idx m : ℕ) : ZMod k) key).1)
    (fun m m' hmm' hm' key => by
      have hlt_idx : idx m < idx m' := by dsimp [idx]; omega
      set d := idx m' - idx m
      have hpm' : ((k - h + idx m' : ℕ) : ZMod k) =
          ((k - h + idx m : ℕ) : ZMod k) + (d : ZMod k) := by
        have h1 : k - h + idx m' = (k - h + idx m) + d := by omega
        rw [h1, Nat.cast_add]
      by_cases hsame : m / 4 = m' / 4
      · have hd_cases : d = 1 ∨ d = 2 ∨ d = 3 := by dsimp [d, idx]; omega
        have hpf := col2_packet_flip (by omega) cc v ((k - h + idx m : ℕ) : ZMod k) key
        rcases hd_cases with hd1 | hd2 | hd3
        · rw [hpm', hd1, Nat.cast_one]; exact hpf.2.1
        · rw [hpm', hd2, Nat.cast_ofNat]; exact hpf.2.2.1
        · rw [hpm', hd3, Nat.cast_ofNat]; exact hpf.2.2.2
      · have hd12 : 12 ≤ d := by dsimp [d, idx]; omega
        have hd_lt : d < h := by have := hidx_lt m' hm'; omega
        refine dep_congr_set hdep ((k - h + idx m' : ℕ) : ZMod k)
          (key + maskInt ((k - h + idx m : ℕ) : ZMod k) [-3, -1, 3, 5]) key fun ε hε => ?_
        rw [Pi.add_apply]
        simp only [Nat.cast_ofNat]
        have hpt : ((k - h + idx m' : ℕ) : ZMod k) - (6 : ZMod k) + (ε : ZMod k) =
            ((k - h + idx m : ℕ) : ZMod k) + (((d + ε : ℤ) - 6 : ℤ) : ZMod k) := by
          rw [hpm']; push_cast; ring
        rw [hpt, maskInt_zero_of_lt _ [-3, -1, 3, 5] ((d + ε : ℤ) - 6) (fun b hb => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl <;>
            exact ⟨abs_pos.mpr (by omega), abs_lt.mpr ⟨by omega, by omega⟩⟩), add_zero])
  have hU : Nat.card {key : ZMod k → ZMod 2 // True} = 2 ^ k := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_pi, ZMod.card]
  rw [hU] at htri
  have hpow : 2 ^ k = 2 ^ u * 2 ^ (k - u) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  rw [hpow] at htri
  have heq := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos u) htri
  omega

lemma card_win_le_row3 {k h : ℕ} [NeZero k] (hh : 0 < h) (hk : h + 19 ≤ k)
    (cr : ℕ → ZMod k → ZMod 2) (uW : ZMod k → ZMod 2) (tgt : ℕ → ZMod 2) :
    let u := 2 * (h / 13) + min 2 (h % 13)
    Nat.card {key : ZMod k → ZMod 2 // ∀ c < h, rowSt cr uW key 3 ((k - h + c : ℕ) : ZMod k) = tgt c} ≤
      2 ^ (k - u) := by
  intro u
  have hu_le : u ≤ h := by dsimp [u]; omega
  let idx : ℕ → ℕ := fun m => 13 * (m / 2) + m % 2
  have hidx_lt : ∀ m < u, idx m < h := by
    intro m hm; dsimp [idx, u] at hm ⊢; omega
  have hsub : Nat.card {key : ZMod k → ZMod 2 //
        ∀ c < h, rowSt cr uW key 3 ((k - h + c : ℕ) : ZMod k) = tgt c} ≤
      Nat.card {key : ZMod k → ZMod 2 //
        True ∧ ∀ m < u, rowSt cr uW key 3 ((k - h + idx m : ℕ) : ZMod k) = tgt (idx m)} := by
    refine Nat.card_le_card_of_injective
      (Subtype.map id fun key hkey => ⟨trivial, fun m hm => hkey (idx m) (hidx_lt m hm)⟩)
      (Subtype.map_injective _ Function.injective_id)
  have hdep := row_key_dep_three_sharp cr uW (by omega)
  have htri := tri_mask (fun _ : ZMod k → ZMod 2 => True) u
    (fun m => maskInt ((k - h + idx m : ℕ) : ZMod k) [-2, -1, 1, 2, 4, 5, 7, 8])
    (fun m key => rowSt cr uW key 3 ((k - h + idx m : ℕ) : ZMod k))
    (fun m => tgt (idx m))
    (fun _ _ _ _ => trivial)
    (fun m _ key => (row3_packet_flip (by omega) cr uW ((k - h + idx m : ℕ) : ZMod k) key).1)
    (fun m m' hmm' hm' key => by
      have hlt_idx : idx m < idx m' := by dsimp [idx]; omega
      set d := idx m' - idx m
      have hpm' : ((k - h + idx m' : ℕ) : ZMod k) =
          ((k - h + idx m : ℕ) : ZMod k) + (d : ZMod k) := by
        have h1 : k - h + idx m' = (k - h + idx m) + d := by omega
        rw [h1, Nat.cast_add]
      by_cases hsame : m / 2 = m' / 2
      · have hd1 : d = 1 := by dsimp [d, idx]; omega
        rw [hpm', hd1, Nat.cast_one]
        exact (row3_packet_flip (by omega) cr uW ((k - h + idx m : ℕ) : ZMod k) key).2
      · have hd12 : 12 ≤ d := by dsimp [d, idx]; omega
        have hd_lt : d < h := by have := hidx_lt m' hm'; omega
        refine dep_congr_set hdep ((k - h + idx m' : ℕ) : ZMod k)
          (key + maskInt ((k - h + idx m : ℕ) : ZMod k) [-2, -1, 1, 2, 4, 5, 7, 8]) key fun ε hε => ?_
        rw [Pi.add_apply]
        simp only [Nat.cast_ofNat]
        have hpt : ((k - h + idx m' : ℕ) : ZMod k) - (3 : ZMod k) + (ε : ZMod k) =
            ((k - h + idx m : ℕ) : ZMod k) + (((d + ε : ℤ) - 3 : ℤ) : ZMod k) := by
          rw [hpm']; push_cast; ring
        rw [hpt, maskInt_zero_of_lt _ [-2, -1, 1, 2, 4, 5, 7, 8] ((d + ε : ℤ) - 3) (fun b hb => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact ⟨abs_pos.mpr (by omega), abs_lt.mpr ⟨by omega, by omega⟩⟩), add_zero])
  have hU : Nat.card {key : ZMod k → ZMod 2 // True} = 2 ^ k := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_pi, ZMod.card]
  rw [hU] at htri
  have hpow : 2 ^ k = 2 ^ u * 2 ^ (k - u) := by rw [← pow_add, Nat.add_sub_of_le (by omega)]
  rw [hpow] at htri
  have heq := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos u) htri
  omega

lemma unique_slice_of_dep_piv {k r h gap w : ℕ} [NeZero k]
    (hgap : gap * r + h ≤ k) (hw : w + h ≤ k + 1)
    (base : Fin (2 ^ k))
    (F : (ZMod k → ZMod 2) → ZMod k → ZMod 2)
    (hF : Dep F (gap * r) w) (hP : Piv F (gap * r)) (tgt : Fin (2 ^ h)) :
    ∃! word : Fin (2 ^ h),
      ∀ c < h, F (toW k (nameN k r h gap base word)) ((k - h + c : ℕ) : ZMod k) =
        b2z (tgt.val.testBit c) := by
  let lo := k - h - gap * r
  let G : Fin (2 ^ h) → Fin (2 ^ h) := fun word =>
    ⟨(List.range h).foldl (fun acc c =>
      acc ||| ((decide (F (toW k (nameN k r h gap base word))
        ((k - h + c : ℕ) : ZMod k) = 1)).toNat <<< c)) 0,
      (pack_foldl_spec _ h).1⟩
  have hG_iff : ∀ word : Fin (2 ^ h),
      G word = tgt ↔ ∀ c < h, F (toW k (nameN k r h gap base word)) ((k - h + c : ℕ) : ZMod k) =
        b2z (tgt.val.testBit c) := by
    intro word
    constructor
    · intro hEq c hc
      have hb : (G word).val.testBit c = tgt.val.testBit c := by rw [hEq]
      dsimp only [G] at hb
      rw [(pack_foldl_spec _ h).2 c, if_pos hc] at hb
      have hv : F (toW k (nameN k r h gap base word)) ((k - h + c : ℕ) : ZMod k) = 0 ∨
          F (toW k (nameN k r h gap base word)) ((k - h + c : ℕ) : ZMod k) = 1 :=
        zmod2_eq_zero_or_one _
      rcases hv with h0 | h1
      · rw [h0] at hb ⊢; simp only [zero_ne_one, decide_false] at hb; rw [← hb]; rfl
      · rw [h1] at hb ⊢; simp only [decide_true] at hb; rw [← hb]; rfl
    · intro hall
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro c
      dsimp only [G]
      rw [(pack_foldl_spec _ h).2 c]
      by_cases hc : c < h
      · rw [if_pos hc, hall c hc]
        cases tgt.val.testBit c <;> decide
      · rw [if_neg hc]
        symm
        exact Nat.testBit_lt_two_pow
          (lt_of_lt_of_le tgt.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hc)))
  have hG_inj : Function.Injective G := by
    intro x y hxy
    by_contra hne
    have hdiff : ∃ c < h, x.val.testBit c ≠ y.val.testBit c := by
      by_contra hall
      apply hne
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro c
      by_cases hc : c < h
      · exact by_contra fun h => hall ⟨c, hc, h⟩
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hc))),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hc)))]
    let S : Finset ℕ := (Finset.range h).filter fun c => x.val.testBit c ≠ y.val.testBit c
    have hSne : S.Nonempty := by
      obtain ⟨c, hc, hneq⟩ := hdiff
      exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, hneq⟩⟩
    let c := S.max' hSne
    have hc_mem : c ∈ S := Finset.max'_mem S hSne
    have hc_lt : c < h := Finset.mem_range.mp (Finset.mem_filter.mp hc_mem).1
    have hc_diff : x.val.testBit c ≠ y.val.testBit c := (Finset.mem_filter.mp hc_mem).2
    have hgt_eq : ∀ c' < h, c < c' → x.val.testBit c' = y.val.testBit c' := by
      intro c' hc' hcc'
      by_contra hneq
      have hc'mem : c' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc', hneq⟩
      have hle := Finset.le_max' S c' hc'mem
      omega
    have hnx := (nameN_spec hgap base x).2
    have hny := (nameN_spec hgap base y).2
    have hsite : ((k - h + c : ℕ) : ZMod k) - ((gap * r : ℕ) : ZMod k) = ((lo + c : ℕ) : ZMod k) := by
      have h1 : k - h + c = lo + c + gap * r := by dsimp [lo]; omega
      rw [h1, Nat.cast_add, add_sub_cancel_right]
    have hagree : ∀ δ < w,
        flp ((lo + c : ℕ) : ZMod k) (toW k (nameN k r h gap base x))
            (((k - h + c : ℕ) : ZMod k) - ((gap * r : ℕ) : ZMod k) + (δ : ZMod k)) =
        toW k (nameN k r h gap base y)
            (((k - h + c : ℕ) : ZMod k) - ((gap * r : ℕ) : ZMod k) + (δ : ZMod k)) := by
      intro δ hδ
      rw [hsite]
      have hpt_eq : ((lo + c : ℕ) : ZMod k) + (δ : ZMod k) = ((lo + c + δ : ℕ) : ZMod k) := by
        push_cast; ring
      rw [hpt_eq]
      rcases δ with _ | δ'
      · simp only [Nat.add_zero, flp_self]
        dsimp only [toW]
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by dsimp [lo]; omega)]
        rw [hnx (lo + c) (by dsimp [lo]; omega), hny (lo + c) (by dsimp [lo]; omega),
          if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
        cases hx : x.val.testBit c <;> cases hy : y.val.testBit c
        · exact absurd (hx.trans hy.symm) hc_diff
        · decide
        · decide
        · exact absurd (hx.trans hy.symm) hc_diff
      · have hne_piv : ((lo + c + (δ' + 1) : ℕ) : ZMod k) ≠ ((lo + c : ℕ) : ZMod k) :=
          (natCast_ne (lo + c) (lo + c + (δ' + 1)) (by omega) (by omega)).symm
        rw [flp_ne hne_piv]
        dsimp only [toW]
        set pos := ((lo + c + (δ' + 1) : ℕ) : ZMod k).val
        have hpos_lt : pos < k := ZMod.val_lt _
        rw [hnx pos hpos_lt, hny pos hpos_lt]
        by_cases hwin : lo ≤ pos ∧ pos < lo + h
        · rw [if_pos hwin, if_pos hwin]
          have hpos_gt : c < pos - lo := by
            have hmod : pos = (lo + c + (δ' + 1)) % k := by
              dsimp only [pos]; rw [ZMod.val_natCast]
            by_cases hwrap : lo + c + (δ' + 1) < k
            · rw [Nat.mod_eq_of_lt hwrap] at hmod; omega
            · have hle2 : lo + c + (δ' + 1) < 2 * k := by dsimp [lo]; omega
              have hsub2 : (lo + c + (δ' + 1)) % k = lo + c + (δ' + 1) - k := by
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
              rw [hsub2] at hmod
              dsimp [lo] at hmod hwin
              omega
          rw [hgt_eq (pos - lo) (by omega) hpos_gt]
        · rw [if_neg hwin, if_neg hwin]
    have heq1 : F (flp ((lo + c : ℕ) : ZMod k) (toW k (nameN k r h gap base x)))
        ((k - h + c : ℕ) : ZMod k) =
        F (toW k (nameN k r h gap base y)) ((k - h + c : ℕ) : ZMod k) :=
      dep_congr_set hF ((k - h + c : ℕ) : ZMod k) _ _ hagree
    have heq2 : F (flp ((lo + c : ℕ) : ZMod k) (toW k (nameN k r h gap base x)))
        ((k - h + c : ℕ) : ZMod k) =
        F (toW k (nameN k r h gap base x)) ((k - h + c : ℕ) : ZMod k) + 1 := by
      rw [← hsite]
      exact hP ((k - h + c : ℕ) : ZMod k) (toW k (nameN k r h gap base x))
    have hGx : (G x).val.testBit c = (G y).val.testBit c := by rw [hxy]
    dsimp only [G] at hGx
    rw [(pack_foldl_spec _ h).2 c, if_pos hc_lt, (pack_foldl_spec _ h).2 c, if_pos hc_lt] at hGx
    have hval_eq : F (toW k (nameN k r h gap base x)) ((k - h + c : ℕ) : ZMod k) =
        F (toW k (nameN k r h gap base y)) ((k - h + c : ℕ) : ZMod k) := by
      set ha := F (toW k (nameN k r h gap base x)) ((k - h + c : ℕ) : ZMod k)
      set hb := F (toW k (nameN k r h gap base y)) ((k - h + c : ℕ) : ZMod k)
      rcases zmod2_eq_zero_or_one ha with h0 | h0 <;> rcases zmod2_eq_zero_or_one hb with h1 | h1
      · exact h0.trans h1.symm
      · rw [h0, h1] at hGx; exact absurd hGx (by decide)
      · rw [h0, h1] at hGx; exact absurd hGx (by decide)
      · exact h0.trans h1.symm
    exact zmod2_ne_add_one _ (hval_eq.trans (heq1.symm.trans heq2))
  have hG_bij := Finite.injective_iff_bijective.mp hG_inj
  obtain ⟨w0, hw0⟩ := hG_bij.2 tgt
  refine ⟨w0, (hG_iff w0).mp hw0, fun w1 hw1 => hG_inj (((hG_iff w1).mpr hw1).trans hw0.symm)⟩

lemma card_pos_ge_unused {k h a v : ℕ} [NeZero k] (hvk : h + v ≤ k)
    {F1 F2 : (ZMod k → ZMod 2) → ZMod k → ZMod 2}
    (hF1 : Dep F1 a (v + 1)) (hF2 : Dep F2 a (v + 1))
    (t1 t2 : ℕ → ZMod 2)
    (key0 : ZMod k → ZMod 2)
    (hk1 : ∀ c < h, F1 key0 ((k - h + c : ℕ) : ZMod k) = t1 c)
    (hk2 : ∀ c < h, F2 key0 ((k - h + c : ℕ) : ZMod k) = t2 c) :
    2 ^ (k - (h + v)) ≤
      Nat.card {key : ZMod k → ZMod 2 //
        (∀ c < h, F1 key ((k - h + c : ℕ) : ZMod k) = t1 c) ∧
        (∀ c < h, F2 key ((k - h + c : ℕ) : ZMod k) = t2 c)} := by
  let s := k - (h + v)
  let pos : Fin s → ZMod k := fun j =>
    ((k - h : ℕ) : ZMod k) - (a : ZMod k) + ((h + v + j.val : ℕ) : ZMod k)
  let phi : (Fin s → ZMod 2) → (ZMod k → ZMod 2) := fun m i =>
    key0 i + ∑ j : Fin s, if i = pos j then m j else 0
  have hpos_inj : Function.Injective pos := by
    intro j1 j2 heq
    have h1 : ((h + v + j1.val : ℕ) : ZMod k) = ((h + v + j2.val : ℕ) : ZMod k) := add_left_cancel heq
    apply Fin.ext
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact natCast_ne (h + v + j1.val) (h + v + j2.val) (by omega)
        (by have := j2.isLt; omega) h1
    · exact natCast_ne (h + v + j2.val) (h + v + j1.val) (by omega)
        (by have := j1.isLt; omega) h1.symm
  have hphi_inj : Function.Injective phi := by
    intro m1 m2 heq
    funext j0
    have h0 := congrFun heq (pos j0)
    simp only [phi] at h0
    have h1 : (∑ j : Fin s, if pos j0 = pos j then m1 j else 0) = m1 j0 := by
      rw [Finset.sum_eq_single j0]
      · simp
      · intro j _ hne; simp [show pos j0 ≠ pos j from fun h => hne (hpos_inj h).symm]
      · intro h; exact absurd (Finset.mem_univ j0) h
    have h2 : (∑ j : Fin s, if pos j0 = pos j then m2 j else 0) = m2 j0 := by
      rw [Finset.sum_eq_single j0]
      · simp
      · intro j _ hne; simp [show pos j0 ≠ pos j from fun h => hne (hpos_inj h).symm]
      · intro h; exact absurd (Finset.mem_univ j0) h
    rw [h1, h2] at h0
    exact add_left_cancel h0
  have hphi_agree : ∀ (m : Fin s → ZMod 2) (c : ℕ), c < h → ∀ δ < v + 1,
      phi m (((k - h + c : ℕ) : ZMod k) - (a : ZMod k) + (δ : ZMod k)) =
      key0 (((k - h + c : ℕ) : ZMod k) - (a : ZMod k) + (δ : ZMod k)) := by
    intro m c hc δ hδ
    dsimp only [phi]
    have hsum0 : (∑ j : Fin s, if ((k - h + c : ℕ) : ZMod k) - (a : ZMod k) + (δ : ZMod k) = pos j
        then m j else 0) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg]
      intro heq
      have hcast : ((c + δ : ℕ) : ZMod k) = ((h + v + j.val : ℕ) : ZMod k) := by
        dsimp only [pos] at heq
        push_cast at heq ⊢
        linear_combination heq
      exact natCast_ne (c + δ) (h + v + j.val) (by omega)
        (by have := j.isLt; omega) hcast
    rw [hsum0, add_zero]
  have hphi_mem : ∀ m : Fin s → ZMod 2,
      (∀ c < h, F1 (phi m) ((k - h + c : ℕ) : ZMod k) = t1 c) ∧
      (∀ c < h, F2 (phi m) ((k - h + c : ℕ) : ZMod k) = t2 c) := by
    intro m
    refine ⟨fun c hc => (dep_congr_set hF1 _ (phi m) key0 (hphi_agree m c hc)).trans (hk1 c hc),
            fun c hc => (dep_congr_set hF2 _ (phi m) key0 (hphi_agree m c hc)).trans (hk2 c hc)⟩
  let Tgt := {key : ZMod k → ZMod 2 //
    (∀ c < h, F1 key ((k - h + c : ℕ) : ZMod k) = t1 c) ∧
    (∀ c < h, F2 key ((k - h + c : ℕ) : ZMod k) = t2 c)}
  have hcard_le : Nat.card (Fin s → ZMod 2) ≤ Nat.card Tgt :=
    Nat.card_le_card_of_injective
      (fun m : Fin s → ZMod 2 => (⟨phi m, hphi_mem m⟩ : Tgt))
      (fun m1 m2 heq => hphi_inj (congrArg Subtype.val heq))
  have hcard_dom : Nat.card (Fin s → ZMod 2) = 2 ^ s := by
    rw [Nat.card_eq_fintype_card]; simp [Fintype.card_pi, ZMod.card]
  rwa [hcard_dom] at hcard_le

end CipherPivots

section HallAndMatching

lemma pad_to_regular {α : Type*} [Fintype α] [DecidableEq α] (L : ℕ) :
    ∀ (D : ℕ) (w : α → α → ℕ),
      (∀ u, ∑ v, w u v ≤ L) →
      (∀ v, ∑ u, w u v ≤ L) →
      Fintype.card α * L - (∑ u, ∑ v, w u v) = D →
      ∃ w' : α → α → ℕ, (∀ u v, w u v ≤ w' u v) ∧
        (∀ u, ∑ v, w' u v = L) ∧ (∀ v, ∑ u, w' u v = L)
  | 0, w, hrow, hcol, hD => by
    have hsum_le : (∑ u : α, ∑ v : α, w u v) ≤ Fintype.card α * L := by
      calc ∑ u : α, ∑ v : α, w u v ≤ ∑ _u : α, L := Finset.sum_le_sum fun u _ => hrow u
        _ = Fintype.card α * L := by simp
    have hsum_eq : (∑ u : α, ∑ v : α, w u v) = Fintype.card α * L := by omega
    have hrow_eq : ∀ u : α, ∑ v, w u v = L := by
      have h := (Finset.sum_eq_sum_iff_of_le (fun u (_ : u ∈ Finset.univ) => hrow u)).mp
        (by rw [hsum_eq]; simp)
      exact fun u => h u (Finset.mem_univ u)
    have hcol_eq : ∀ v : α, ∑ u, w u v = L := by
      have hsum_col : (∑ v : α, ∑ u : α, w u v) = ∑ _v : α, L := by
        rw [Finset.sum_comm, hsum_eq]; simp
      have h := (Finset.sum_eq_sum_iff_of_le (fun v (_ : v ∈ Finset.univ) => hcol v)).mp hsum_col
      exact fun v => h v (Finset.mem_univ v)
    exact ⟨w, fun _ _ => le_rfl, hrow_eq, hcol_eq⟩
  | D + 1, w, hrow, hcol, hD => by
    have hlt : (∑ u : α, ∑ v : α, w u v) < Fintype.card α * L := by omega
    have hex_u : ∃ u0 : α, ∑ v, w u0 v < L := by
      by_contra hall
      push_neg at hall
      have hge : Fintype.card α * L ≤ ∑ u : α, ∑ v : α, w u v := by
        calc Fintype.card α * L = ∑ _u : α, L := by simp
          _ ≤ ∑ u : α, ∑ v : α, w u v := Finset.sum_le_sum fun u _ => hall u
      omega
    have hex_v : ∃ v0 : α, ∑ u, w u v0 < L := by
      by_contra hall
      push_neg at hall
      have hge : Fintype.card α * L ≤ ∑ u : α, ∑ v : α, w u v := by
        rw [Finset.sum_comm]
        calc Fintype.card α * L = ∑ _v : α, L := by simp
          _ ≤ ∑ v : α, ∑ u : α, w u v := Finset.sum_le_sum fun v _ => hall v
      omega
    obtain ⟨u0, hu0⟩ := hex_u
    obtain ⟨v0, hv0⟩ := hex_v
    let w1 : α → α → ℕ := fun u v => w u v + if u = u0 ∧ v = v0 then 1 else 0
    have hrow1 : ∀ u, ∑ v, w1 u v ≤ L := by
      intro u
      dsimp only [w1]
      rw [Finset.sum_add_distrib]
      by_cases hu : u = u0
      · subst hu
        simp only [true_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        omega
      · simp only [hu, false_and, ↓reduceIte, Finset.sum_const_zero, add_zero]
        exact hrow u
    have hcol1 : ∀ v, ∑ u, w1 u v ≤ L := by
      intro v
      dsimp only [w1]
      rw [Finset.sum_add_distrib]
      by_cases hv : v = v0
      · subst hv
        simp only [and_true, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        omega
      · simp only [hv, and_false, ↓reduceIte, Finset.sum_const_zero, add_zero]
        exact hcol v
    have hsum1 : (∑ u : α, ∑ v : α, w1 u v) = (∑ u : α, ∑ v : α, w u v) + 1 := by
      dsimp only [w1]
      simp_rw [Finset.sum_add_distrib]
      congr 1
      have hinner : ∀ u : α, (∑ v : α, if u = u0 ∧ v = v0 then 1 else 0) =
          if u = u0 then 1 else 0 := by
        intro u
        by_cases hu : u = u0
        · subst hu; simp
        · simp [hu]
      simp_rw [hinner]
      simp
    obtain ⟨w', hle', hrow', hcol'⟩ := pad_to_regular L D w1 hrow1 hcol1 (by omega)
    exact ⟨w', fun u v => le_trans (Nat.le_add_right _ _) (hle' u v), hrow', hcol'⟩

lemma exists_perm_pos_of_regular {α : Type*} [Fintype α] [DecidableEq α] {d : ℕ}
    (hd : 0 < d) (w : α → α → ℕ)
    (hrow : ∀ u, ∑ v, w u v = d) (hcol : ∀ v, ∑ u, w u v = d) :
    ∃ π : Equiv.Perm α, ∀ u, 0 < w u (π u) := by
  let adj (u : α) : Finset α := Finset.univ.filter fun v => 0 < w u v
  have hall : ∀ S : Finset α, S.card ≤ (S.biUnion adj).card := by
    intro S
    have hrowS (u : α) : ∑ v ∈ adj u, w u v = d :=
      (Finset.sum_subset (Finset.subset_univ _) fun v _ hv =>
        Nat.eq_zero_of_not_pos fun hpos => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hpos⟩)).trans
        (hrow u)
    have hle : S.card * d ≤ (S.biUnion adj).card * d := by
      calc S.card * d = ∑ u ∈ S, ∑ v ∈ adj u, w u v :=
            (Finset.sum_const_nat fun u _ => hrowS u).symm
        _ ≤ ∑ u ∈ S, ∑ v ∈ S.biUnion adj, w u v :=
            Finset.sum_le_sum fun u hu => Finset.sum_le_sum_of_subset (Finset.subset_biUnion_of_mem adj hu)
        _ ≤ ∑ u ∈ Finset.univ, ∑ v ∈ S.biUnion adj, w u v :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = ∑ v ∈ S.biUnion adj, ∑ u ∈ Finset.univ, w u v := Finset.sum_comm
        _ = (S.biUnion adj).card * d := Finset.sum_const_nat fun v _ => hcol v
    exact Nat.le_of_mul_le_mul_right hle hd
  obtain ⟨f, hinj, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
    fun u => (Finset.mem_filter.mp (hmem u)).2⟩

lemma decompose_regular {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (d : ℕ) (w : α → α → ℕ),
      (∀ u, ∑ v, w u v = d) → (∀ v, ∑ u, w u v = d) →
      ∃ p : Fin d → Equiv.Perm α, ∀ u v, w u v = ∑ t : Fin d, if p t u = v then 1 else 0
  | 0, w, hrow, _ => ⟨Fin.elim0, fun u v => by
      have h0 : w u v ≤ 0 := hrow u ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
      exact (Nat.le_zero.mp h0).trans (by simp only [Finset.univ_eq_empty, Finset.sum_empty])⟩
  | d + 1, w, hrow, hcol => by
    obtain ⟨π, hπ⟩ := exists_perm_pos_of_regular (Nat.succ_pos d) w hrow hcol
    let m (u v : α) : ℕ := if π u = v then 1 else 0
    have hle (u v : α) : m u v ≤ w u v := by
      by_cases h : π u = v
      · rw [← h]; simp only [m, ↓reduceIte]; exact hπ u
      · simp only [m, h, ↓reduceIte]; exact Nat.zero_le _
    have hm_row (u : α) : ∑ v, m u v = 1 := by
      simp only [m, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    have hm_col (v : α) : ∑ u, m u v = 1 := by
      have heq : (fun u => m u v) = fun u => if u = π.symm v then 1 else 0 :=
        funext fun u => if_congr (π.eq_symm_apply.symm) rfl rfl
      rw [heq]; simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hrow' (u : α) : ∑ v, (w u v - m u v) = d := by
      rw [Finset.sum_tsub_distrib _ fun v _ => hle u v, hrow u, hm_row u, Nat.add_sub_cancel]
    have hcol' (v : α) : ∑ u, (w u v - m u v) = d := by
      rw [Finset.sum_tsub_distrib _ fun u _ => hle u v, hcol v, hm_col v, Nat.add_sub_cancel]
    obtain ⟨p, hp⟩ := decompose_regular d (fun u v => w u v - m u v) hrow' hcol'
    refine ⟨Fin.cons π p, fun u v => ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hp u v]
    exact (Nat.add_sub_of_le (hle u v)).symm

lemma extract_matching {α : Type*} [Fintype α] [DecidableEq α]
    (L : ℕ) (hL : 0 < L) (keys : α → α → ℕ) (accept : α → α → Bool)
    (hrow : ∀ x, ∑ y, keys x y ≤ L) (hcol : ∀ y, ∑ x, keys x y ≤ L) :
    let H := ∑ x : α, ∑ y : α, if accept x y then keys x y else 0
    let m := (H + L - 1) / L
    ∃ (f g : Fin m → α), Function.Injective f ∧ Function.Injective g ∧
      ∀ i : Fin m, accept (f i) (g i) = true ∧ 0 < keys (f i) (g i) := by
  intro H m
  let wAcc : α → α → ℕ := fun x y => if accept x y then keys x y else 0
  have hrowA : ∀ x, ∑ y, wAcc x y ≤ L := fun x =>
    le_trans (Finset.sum_le_sum fun y _ => by dsimp [wAcc]; split_ifs <;> omega) (hrow x)
  have hcolA : ∀ y, ∑ x, wAcc x y ≤ L := fun y =>
    le_trans (Finset.sum_le_sum fun x _ => by dsimp [wAcc]; split_ifs <;> omega) (hcol y)
  obtain ⟨wPad, hlePad, hrowPad, hcolPad⟩ := pad_to_regular L
    (Fintype.card α * L - ∑ x, ∑ y, wAcc x y) wAcc hrowA hcolA rfl
  obtain ⟨π, hπ⟩ := decompose_regular L wPad hrowPad hcolPad
  let good : Fin L → Finset α := fun t =>
    Finset.univ.filter fun x => accept x (π t x) = true ∧ 0 < keys x (π t x)
  have hsum_good : H ≤ ∑ t : Fin L, (good t).card := by
    have hrew : (∑ t : Fin L, (good t).card) =
        ∑ x : α, ∑ y : α, if accept x y = true ∧ 0 < keys x y then wPad x y else 0 := by
      have h1 : ∀ t : Fin L, (good t).card =
          ∑ x : α, ∑ y : α, if accept x y = true ∧ 0 < keys x y then (if π t x = y then 1 else 0) else 0 := by
        intro t
        dsimp only [good]
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single (π t x)]
        · simp
        · intro y _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp_rw [h1]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hcond : accept x y = true ∧ 0 < keys x y
      · simp only [hcond, ↓reduceIte]
        exact (hπ x y).symm
      · simp only [hcond, ↓reduceIte, Finset.sum_const_zero]
    rw [hrew]
    refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
    by_cases ha : accept x y = true
    · by_cases hk : 0 < keys x y
      · simp only [ha, hk, and_self, ↓reduceIte]
        have hle := hlePad x y
        simp only [wAcc, ha, ↓reduceIte] at hle
        exact hle
      · have hk0 : keys x y = 0 := by omega
        simp [ha, hk0]
    · simp [ha]
  have hex_t : ∃ t0 : Fin L, m ≤ (good t0).card := by
    by_contra hall
    push_neg at hall
    have hlt : ∀ t : Fin L, (good t).card + 1 ≤ m := fun t => hall t
    have hsum_lt : (∑ t : Fin L, (good t).card) + L ≤ L * m := by
      have h1 : ∑ t : Fin L, ((good t).card + 1) ≤ ∑ _t : Fin L, m :=
        Finset.sum_le_sum fun t _ => hlt t
      rw [Finset.sum_add_distrib] at h1
      simpa using h1
    have hceil : H ≤ L * m := by omega
    have hmlt : L * m ≤ H + L - 1 := by
      dsimp only [m]
      exact Nat.mul_div_le (H + L - 1) L
    omega
  obtain ⟨t0, ht0⟩ := hex_t
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq ht0
  let e : Fin m ≃ S := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hScard])).symm
  let f : Fin m → α := fun i => (e i).val
  let g : Fin m → α := fun i => π t0 (f i)
  have hf_inj : Function.Injective f := fun i j hij => e.injective (Subtype.ext hij)
  have hg_inj : Function.Injective g := (π t0).injective.comp hf_inj
  refine ⟨f, g, hf_inj, hg_inj, fun i => ?_⟩
  exact (Finset.mem_filter.mp (hSsub (e i).property)).2

end HallAndMatching

section AnchoredRankBound

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

lemma foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

lemma wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  conv_lhs => unfold wiresOf
  rw [List.foldl_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  change (gs2.foldl _ (wiresOf x gs1)).getD k false = (wiresOf x gs1).getD k false
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

lemma depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  conv_lhs => unfold depthsOf
  rw [List.foldl_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  change (gs2.foldl _ (depthsOf w gs1)).getD k 0 = (depthsOf w gs1).getD k 0
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

lemma wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

lemma wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ gs[idx].inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      gs[idx].op.eval (gs[idx].inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop hidx,
      List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, List.length_singleton, hlen1]
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  conv_lhs => unfold wiresOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  change (wiresOf x (gs.take idx) ++
    [gs[idx].op.eval (gs[idx].inputs.map fun i => (wiresOf x (gs.take idx)).getD i false)]).getD
      (x.length + idx) false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

lemma depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ gs[idx].inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      (gs[idx].inputs.map fun a => (depthsOf w gs).getD a 0).foldr max 0 + (nlGate gs[idx]).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.append_assoc, List.singleton_append, List.getElem_cons_drop hidx,
      List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, List.length_singleton, hlen1]
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  conv_lhs => unfold depthsOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  change (depthsOf w (gs.take idx) ++
    [(gs[idx].inputs.map fun a => (depthsOf w (gs.take idx)).getD a 0).foldr max 0 +
      (nlGate gs[idx]).toNat]).getD (w + idx) 0 = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

lemma anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

lemma anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

lemma anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j; simp only [anchor, Matrix.zero_apply, zmod2_add_self, zero_add]

lemma anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

lemma anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j; simp only [anchor, Matrix.add_apply]; ring

lemma anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j; simp only [anchor, Matrix.smul_apply, smul_eq_mul]; ring

lemma rank_add_le {n m : ℕ} (A B : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  let S1 : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range A.mulVecLin
  let S2 : Submodule (ZMod 2) (Fin n → ZMod 2) := LinearMap.range B.mulVecLin
  have hrange : LinearMap.range (A + B).mulVecLin ≤ S1 ⊔ S2 := by
    rintro _ ⟨x, rfl⟩
    have hmul : (A + B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by
      simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
    rw [hmul]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq S1 S2
  have hmono := Submodule.finrank_mono hrange
  change (A + B).rank ≤ Module.finrank (ZMod 2) ↥(S1 ⊔ S2) at hmono
  change Module.finrank (ZMod 2) ↥(S1 ⊔ S2) + Module.finrank (ZMod 2) ↥(S1 ⊓ S2) =
    A.rank + B.rank at hsup
  omega

lemma rank_vecMulVec_le_one {n m : ℕ} (a : Fin n → ZMod 2) (b : Fin m → ZMod 2) :
    (Matrix.vecMulVec a b).rank ≤ 1 := by
  let P : Matrix (Fin n) (Fin 1) (ZMod 2) := Matrix.of fun i _ => a i
  let Q : Matrix (Fin 1) (Fin m) (ZMod 2) := Matrix.of fun _ j => b j
  have hPQ : Matrix.vecMulVec a b = P * Q := by
    ext i j; simp [P, Q, Matrix.mul_apply, Matrix.vecMulVec_apply]
  rw [hPQ]
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ ≤ Module.finrank (ZMod 2) (Fin 1 → ZMod 2) := LinearMap.finrank_range_le P.mulVecLin
    _ = 1 := Module.finrank_fin_fun (ZMod 2)

lemma rank_le_two_add_anchor {n m : ℕ} (u : Fin n) (v : Fin m)
    (M : Matrix (Fin n) (Fin m) (ZMod 2)) :
    M.rank ≤ 2 + (anchor u v (fun i j => M i j)).rank := by
  let R1 := Matrix.vecMulVec (fun i => M i v) (fun _ : Fin m => (1 : ZMod 2))
  let R2 := Matrix.vecMulVec (fun _ : Fin n => (1 : ZMod 2)) (fun j => M u j + M u v)
  have heq : M = anchor u v (fun i j => M i j) + (R1 + R2) := by
    ext i j
    simp only [anchor, R1, R2, Matrix.add_apply, Matrix.vecMulVec_apply, mul_one, one_mul]
    have h : M i j + M i v + M u j + M u v + (M i v + (M u j + M u v)) =
        M i j + ((M i v + M i v) + (M u j + M u j) + (M u v + M u v)) := by ring
    have ha1 : M i v + M i v = 0 := zmod2_add_self (M i v)
    have ha2 : M u j + M u j = 0 := zmod2_add_self (M u j)
    have ha3 : M u v + M u v = 0 := zmod2_add_self (M u v)
    rw [h, ha1, ha2, ha3, zero_add, zero_add, add_zero]
  conv_lhs => rw [heq]
  have h1 := rank_add_le (anchor u v (fun i j => M i j)) (R1 + R2)
  have h2 := rank_add_le R1 R2
  have h3 : R1.rank ≤ 1 := rank_vecMulVec_le_one (fun i => M i v) (fun _ : Fin m => (1 : ZMod 2))
  have h4 : R2.rank ≤ 1 := rank_vecMulVec_le_one (fun _ : Fin n => (1 : ZMod 2)) (fun j => M u j + M u v)
  omega

def mon {n m : ℕ} {K : Type*} (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    (S T : Finset K) : Fin n → Fin m → ZMod 2 :=
  fun i j => (∏ x ∈ S, α x i) * (∏ y ∈ T, β y j)

def PolyDeg {n m : ℕ} {K : Type*} (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) (D : ℕ) :
    Submodule (ZMod 2) (Fin n → Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) {f | ∃ S T : Finset K, S.card + T.card ≤ D ∧ f = mon α β S T}

lemma prod_mul_prod_union {K : Type*} [DecidableEq K] (f : K → ZMod 2) (S1 S2 : Finset K) :
    (∏ x ∈ S1, f x) * (∏ x ∈ S2, f x) = ∏ x ∈ S1 ∪ S2, f x := by
  induction S1 using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_assoc, ih, Finset.insert_union]
    by_cases hmem : a ∈ s ∪ S2
    · rw [Finset.insert_eq_of_mem hmem, ← Finset.mul_prod_erase _ _ hmem, ← mul_assoc,
        zmod2_mul_self]
    · rw [Finset.prod_insert hmem]

lemma polyDeg_mono {n m : ℕ} {K : Type*} (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    {D1 D2 : ℕ} (hD : D1 ≤ D2) {f : Fin n → Fin m → ZMod 2} (hf : f ∈ PolyDeg α β D1) :
    f ∈ PolyDeg α β D2 := by
  unfold PolyDeg at hf ⊢
  refine Submodule.span_mono ?_ hf
  rintro g ⟨S, T, hST, hEq⟩
  exact ⟨S, T, le_trans hST hD, hEq⟩

lemma polyDeg_mul {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    {D1 D2 : ℕ} {f g : Fin n → Fin m → ZMod 2}
    (hf : f ∈ PolyDeg α β D1) (hg : g ∈ PolyDeg α β D2) :
    (fun i j => f i j * g i j) ∈ PolyDeg α β (D1 + D2) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨S1, T1, h1, rfl⟩
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨S2, T2, h2, rfl⟩
      refine Submodule.subset_span ⟨S1 ∪ S2, T1 ∪ T2, ?_, ?_⟩
      · have hc1 := Finset.card_union_le S1 S2
        have hc2 := Finset.card_union_le T1 T2
        omega
      · funext i j
        dsimp only [mon]
        calc
          (∏ x ∈ S1, α x i) * (∏ y ∈ T1, β y j) * ((∏ x ∈ S2, α x i) * (∏ y ∈ T2, β y j))
            = ((∏ x ∈ S1, α x i) * (∏ x ∈ S2, α x i)) * ((∏ y ∈ T1, β y j) * (∏ y ∈ T2, β y j)) := by ring
          _ = (∏ x ∈ S1 ∪ S2, α x i) * (∏ y ∈ T1 ∪ T2, β y j) := by
              rw [prod_mul_prod_union, prod_mul_prod_union]
    · have : (fun i j => mon α β S1 T1 i j * (0 : Fin n → Fin m → ZMod 2) i j) = 0 := by
        funext i j; simp
      rw [this]; exact Submodule.zero_mem _
    · intro g1 g2 _ _ ih1 ih2
      have : (fun i j => mon α β S1 T1 i j * (g1 + g2) i j) =
          (fun i j => mon α β S1 T1 i j * g1 i j) + (fun i j => mon α β S1 T1 i j * g2 i j) := by
        funext i j; simp [mul_add]
      rw [this]; exact Submodule.add_mem _ ih1 ih2
    · intro c g1 _ ih
      have : (fun i j => mon α β S1 T1 i j * (c • g1) i j) =
          c • (fun i j => mon α β S1 T1 i j * g1 i j) := by
        funext i j; simp; ring
      rw [this]; exact Submodule.smul_mem _ c ih
  · have : (fun i j => (0 : Fin n → Fin m → ZMod 2) i j * g i j) = 0 := by funext i j; simp
    rw [this]; exact Submodule.zero_mem _
  · intro f1 f2 _ _ ih1 ih2
    have : (fun i j => (f1 + f2) i j * g i j) =
        (fun i j => f1 i j * g i j) + (fun i j => f2 i j * g i j) := by
      funext i j; simp [add_mul]
    rw [this]; exact Submodule.add_mem _ ih1 ih2
  · intro c f1 _ ih
    have : (fun i j => (c • f1) i j * g i j) = c • (fun i j => f1 i j * g i j) := by
      funext i j; simp; ring
    rw [this]; exact Submodule.smul_mem _ c ih

lemma polyDeg_const {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) (D : ℕ) (c : ZMod 2) :
    (fun _ _ => c) ∈ PolyDeg α β D := by
  let oneFn : Fin n → Fin m → ZMod 2 := fun _ _ => 1
  have h1 : oneFn = mon α β ∅ ∅ := by funext i j; simp [oneFn, mon]
  have hm : oneFn ∈ PolyDeg α β D := by rw [h1]; exact Submodule.subset_span ⟨∅, ∅, by simp, rfl⟩
  have : (fun (_ : Fin n) (_ : Fin m) => c) = c • oneFn := by funext i j; simp [oneFn]
  rw [this]; exact Submodule.smul_mem _ c hm

lemma polyDeg_alpha {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) {D : ℕ} (hD : 1 ≤ D) (x : K) :
    (fun i (_ : Fin m) => α x i) ∈ PolyDeg α β D := by
  apply Submodule.subset_span
  refine ⟨{x}, ∅, by simp [hD], ?_⟩
  funext i j; simp [mon]

lemma polyDeg_beta {n m : ℕ} {K : Type*} [DecidableEq K]
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2) {D : ℕ} (hD : 1 ≤ D) (y : K) :
    (fun (_ : Fin n) j => β y j) ∈ PolyDeg α β D := by
  apply Submodule.subset_span
  refine ⟨∅, {y}, by simp [hD], ?_⟩
  funext i j; simp [mon]

lemma rank_anchor_polyDeg {n m : ℕ} {K : Type*} [Fintype K] [DecidableEq K]
    (u : Fin n) (v : Fin m)
    (α : K → Fin n → ZMod 2) (β : K → Fin m → ZMod 2)
    (hα0 : ∀ x, α x u = 0) (hβ0 : ∀ y, β y v = 0)
    (b : ℕ) {f : Fin n → Fin m → ZMod 2} (hf : f ∈ PolyDeg α β (2 * b)) :
    (anchor u v f).rank ≤
      (∑ j ∈ Finset.range b, Nat.choose (Fintype.card K) (j + 1)) +
      (∑ j ∈ Finset.range (b - 1), Nat.choose (Fintype.card K) (j + 1)) := by
  let F1 : Finset (Finset K) := Finset.univ.powerset.filter (fun S => 1 ≤ S.card ∧ S.card ≤ b)
  let F2 : Finset (Finset K) := Finset.univ.powerset.filter (fun T => 1 ≤ T.card ∧ T.card ≤ b - 1)
  have hF1_card : F1.card = ∑ j ∈ Finset.range b, Nat.choose (Fintype.card K) (j + 1) := by
    have hmaps : ∀ S ∈ F1, S.card - 1 ∈ Finset.range b := by
      intro S hS; rw [Finset.mem_filter] at hS; rw [Finset.mem_range]; omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have heq : F1.filter (fun S => S.card - 1 = j) =
        (Finset.univ : Finset K).powersetCard (j + 1) := by
      ext S
      simp only [F1, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      omega
    rw [heq, Finset.card_powersetCard, Finset.card_univ]
  have hF2_card : F2.card = ∑ j ∈ Finset.range (b - 1), Nat.choose (Fintype.card K) (j + 1) := by
    have hmaps : ∀ T ∈ F2, T.card - 1 ∈ Finset.range (b - 1) := by
      intro T hT; rw [Finset.mem_filter] at hT; rw [Finset.mem_range]; omega
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    have heq : F2.filter (fun T => T.card - 1 = j) =
        (Finset.univ : Finset K).powersetCard (j + 1) := by
      ext T
      simp only [F2, Finset.mem_filter, Finset.mem_powerset, Finset.mem_powersetCard,
        Finset.subset_univ, true_and]
      omega
    rw [heq, Finset.card_powersetCard, Finset.card_univ]
  have hsplit : ∃ (A1 A2 : Matrix (Fin n) (Fin m) (ZMod 2)),
      anchor u v f = A1 + A2 ∧
      (∃ Q1 : Matrix F1 (Fin m) (ZMod 2),
        A1 = Matrix.of (fun (i : Fin n) (S : F1) => ∏ x ∈ S.val, α x i) * Q1) ∧
      (∃ P2 : Matrix (Fin n) F2 (ZMod 2),
        A2 = P2 * Matrix.of (fun (T : F2) (j : Fin m) => ∏ y ∈ T.val, β y j)) := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨S, T, hST, rfl⟩
      by_cases hS0 : S.card = 0
      · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
        subst hSe
        have hzero : anchor u v (mon α β ∅ T) = 0 := by
          have : mon α β ∅ T = fun i j => (0 : ZMod 2) + (∏ y ∈ T, β y j) := by
            funext i j; simp [mon]
          rw [this, anchor_split]
        exact ⟨0, 0, by simp [hzero], ⟨0, by simp⟩, ⟨0, by simp⟩⟩
      · by_cases hT0 : T.card = 0
        · have hTe : T = ∅ := Finset.card_eq_zero.mp hT0
          subst hTe
          have hzero : anchor u v (mon α β S ∅) = 0 := by
            have : mon α β S ∅ = fun i j => (∏ x ∈ S, α x i) + (0 : ZMod 2) := by
              funext i j; simp [mon]
            rw [this, anchor_split]
          exact ⟨0, 0, by simp [hzero], ⟨0, by simp⟩, ⟨0, by simp⟩⟩
        · have hSpos : 1 ≤ S.card := by omega
          have hTpos : 1 ≤ T.card := by omega
          obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
          obtain ⟨y0, hy0⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
          have hanch : anchor u v (mon α β S T) = mon α β S T := by
            ext i j
            simp only [anchor, mon]
            have hpu : (∏ x ∈ S, α x u) = 0 := Finset.prod_eq_zero hx0 (hα0 x0)
            have hpv : (∏ y ∈ T, β y v) = 0 := Finset.prod_eq_zero hy0 (hβ0 y0)
            simp [hpu, hpv]
          by_cases hSb : S.card ≤ b
          · have hSmem : S ∈ F1 :=
              Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hSpos, hSb⟩
            refine ⟨Matrix.of (mon α β S T), 0, by rw [hanch]; ext i j; simp,
              ⟨Matrix.of fun S' j => if S'.val = S then ∏ y ∈ T, β y j else 0, ?_⟩,
              ⟨0, by simp⟩⟩
            ext i j
            rw [Matrix.mul_apply]
            simp only [Matrix.of_apply, mon]
            rw [Finset.sum_eq_single (⟨S, hSmem⟩ : F1)]
            · simp
            · intro S' _ hne
              have : S'.val ≠ S := fun h => hne (Subtype.ext h)
              simp [this]
            · intro h; exact absurd (Finset.mem_univ _) h
          · have hTb : T.card ≤ b - 1 := by omega
            have hTmem : T ∈ F2 :=
              Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ T), hTpos, hTb⟩
            refine ⟨0, Matrix.of (mon α β S T), by rw [hanch]; ext i j; simp, ⟨0, by simp⟩,
              ⟨Matrix.of fun i T' => if T'.val = T then ∏ x ∈ S, α x i else 0, ?_⟩⟩
            ext i j
            rw [Matrix.mul_apply]
            simp only [Matrix.of_apply, mon]
            rw [Finset.sum_eq_single (⟨T, hTmem⟩ : F2)]
            · simp
            · intro T' _ hne
              have : T'.val ≠ T := fun h => hne (Subtype.ext h)
              simp [this]
            · intro h; exact absurd (Finset.mem_univ _) h
    · have : anchor u v (0 : Fin n → Fin m → ZMod 2) = 0 := anchor_const u v 0
      exact ⟨0, 0, by simp [this], ⟨0, by simp⟩, ⟨0, by simp⟩⟩
    · intro f1 f2 _ _ ih1 ih2
      obtain ⟨A1, A2, ha, ⟨Q1, hQ1⟩, ⟨P2, hP2⟩⟩ := ih1
      obtain ⟨B1, B2, hb, ⟨Q1', hQ1'⟩, ⟨P2', hP2'⟩⟩ := ih2
      refine ⟨A1 + B1, A2 + B2, ?_, ⟨Q1 + Q1', ?_⟩, ⟨P2 + P2', ?_⟩⟩
      · change anchor u v (fun i j => f1 i j + f2 i j) = _
        rw [anchor_add, ha, hb]; abel
      · rw [Matrix.mul_add, hQ1, hQ1']
      · rw [Matrix.add_mul, hP2, hP2']
    · intro c f1 _ ih
      obtain ⟨A1, A2, ha, ⟨Q1, hQ1⟩, ⟨P2, hP2⟩⟩ := ih
      refine ⟨c • A1, c • A2, ?_, ⟨c • Q1, ?_⟩, ⟨c • P2, ?_⟩⟩
      · change anchor u v (fun i j => c * f1 i j) = _
        rw [anchor_smul, ha, smul_add]
      · rw [Matrix.mul_smul, hQ1]
      · rw [Matrix.smul_mul, hP2]
  obtain ⟨A1, A2, hsum, ⟨Q1, hQ1⟩, ⟨P2, hP2⟩⟩ := hsplit
  have hr1 : A1.rank ≤ F1.card := by
    rw [hQ1]
    calc (Matrix.of (fun (i : Fin n) (S : F1) => ∏ x ∈ S.val, α x i) * Q1).rank
        ≤ (Matrix.of (fun (i : Fin n) (S : F1) => ∏ x ∈ S.val, α x i)).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Module.finrank (ZMod 2) (F1 → ZMod 2) := LinearMap.finrank_range_le _
      _ = F1.card := by rw [Module.finrank_pi]; simp
  have hr2 : A2.rank ≤ F2.card := by
    rw [hP2]
    calc (P2 * Matrix.of (fun (T : F2) (j : Fin m) => ∏ y ∈ T.val, β y j)).rank
        ≤ P2.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Module.finrank (ZMod 2) (F2 → ZMod 2) := LinearMap.finrank_range_le _
      _ = F2.card := by rw [Module.finrank_pi]; simp
  rw [hsum, ← hF1_card, ← hF2_card]
  exact le_trans (rank_add_le A1 A2) (Nat.add_le_add hr1 hr2)

lemma card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by simp
        rw [h1, Fin.sum_univ_succ]
        congr 1; simp
      simpa using hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

lemma separate_encoding_rank_bound {n m w v d : ℕ}
    (leftE : Fin n → Fin w → Bool) (rightE : Fin m → Fin v → Bool)
    (u0 : Fin n) (v0 : Fin m) (C : Circuit)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hrb : ReadsBack (w + v) C)
    (hdep : (depthsOf (w + v) C.gates).getD C.output 0 ≤ d + 1) :
    let t := C.gates.countP nlGate
    let M : Matrix (Fin n) (Fin m) (ZMod 2) :=
      fun i j => b2z (C.eval (List.ofFn (leftE i) ++ List.ofFn (rightE j)))
    M.rank ≤
      2 + (∑ j ∈ Finset.range (2 ^ d), Nat.choose (2 * t) (j + 1)) +
      (∑ j ∈ Finset.range (2 ^ d - 1), Nat.choose (2 * t) (j + 1)) := by
  intro t M
  let inp : Fin n → Fin m → List Bool := fun i j => List.ofFn (leftE i) ++ List.ofFn (rightE j)
  have hinp_len : ∀ i j, (inp i j).length = w + v := fun i j => by simp [inp]
  let val : ℕ → Fin n → Fin m → ZMod 2 := fun k i j => b2z ((wiresOf (inp i j) C.gates).getD k false)
  let dep : ℕ → ℕ := fun k => (depthsOf (w + v) C.gates).getD k 0
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate C.gates[idx.val] = true)
  have hNL_card : NL.card = t := card_filter_fin_eq_countP C.gates nlGate
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ C.gates[idx].inputs, a < w + v + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (i : Fin n) (j : Fin m),
      val (w + v + idx) i j =
        b2z (C.gates[idx].op.eval (C.gates[idx].inputs.map fun a =>
          (wiresOf (inp i j) C.gates).getD a false)) := by
    intro idx hidx i j
    unfold val
    have h := wiresOf_getD_gate (inp i j) C.gates hidx (by
      intro a ha; rw [hinp_len]; exact hrb' idx hidx a ha)
    rw [hinp_len] at h
    rw [h]
  have hdep_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      dep (w + v + idx) =
        (C.gates[idx].inputs.map dep).foldr max 0 + (nlGate C.gates[idx]).toNat := by
    intro idx hidx
    exact depthsOf_getD_gate (w + v) C.gates hidx (hrb' idx hidx)
  have hdecomp_wire : ∀ wire : ℕ,
      ∃ (rw0 : Fin n → ZMod 2) (sw0 : Fin m → ZMod 2) (cw : NL → ZMod 2),
        (∀ p : NL, cw p ≠ 0 → w + v + p.val.val ≤ wire ∧ dep (w + v + p.val.val) ≤ dep wire) ∧
        ∀ i j, val wire i j = rw0 i + sw0 j + ∑ p : NL, cw p * val (w + v + p.val.val) i j := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      by_cases hw_in : wire < w + v
      · by_cases hw_l : wire < w
        · refine ⟨fun i => b2z (leftE i ⟨wire, hw_l⟩), fun _ => 0, fun _ => 0, by simp, fun i j => ?_⟩
          simp only [val, zero_mul, Finset.sum_const_zero, add_zero]
          rw [wiresOf_getD_input _ _ (by rw [hinp_len]; exact hw_in)]
          dsimp only [inp]
          rw [List.getD_append _ _ _ _ (by simp [hw_l]), List.getD_eq_getElem _ _ (by simp [hw_l]),
            List.getElem_ofFn]
        · refine ⟨fun _ => 0, fun j => b2z (rightE j ⟨wire - w, by omega⟩), fun _ => 0, by simp, fun i j => ?_⟩
          simp only [val, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
          rw [wiresOf_getD_input _ _ (by rw [hinp_len]; exact hw_in)]
          dsimp only [inp]
          rw [List.getD_append_right _ _ _ _ (by simp; omega)]
          simp only [List.length_ofFn]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
      · by_cases hw_g : wire < w + v + C.gates.length
        · let idx : Fin C.gates.length := ⟨wire - (w + v), by omega⟩
          have hwire_eq : wire = w + v + idx.val := by dsimp [idx]; omega
          rw [hwire_eq]
          let g := C.gates[idx.val]
          by_cases hnl : nlGate g = true
          · let p0 : NL := ⟨idx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl⟩⟩
            refine ⟨fun _ => 0, fun _ => 0, fun p => if p = p0 then 1 else 0, ?_, fun i j => ?_⟩
            · intro p hp
              have hp_eq : p = p0 := by_contra fun hne => hp (if_neg hne)
              subst hp_eq; exact ⟨le_rfl, le_rfl⟩
            · simp only [zero_add]
              rw [Finset.sum_eq_single p0]
              · simp [p0]
              · intro p _ hne; simp [hne]
              · intro h; exact absurd (Finset.mem_univ p0) h
          · have hnlf : nlGate g = false := Bool.eq_false_iff.mpr hnl
            have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
            have hdg := hdep_gate idx.val idx.isLt
            cases hg_in : g.inputs with
            | nil =>
              refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun _ => 0, by simp, fun i j => ?_⟩
              simp only [zero_mul, Finset.sum_const_zero, add_zero]
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in]; simp
            | cons a rest =>
              cases rest with
              | nil =>
                have ha_lt : a < w + v + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
                have ha_d : dep a ≤ dep (w + v + idx.val) := by
                  change dep (w + v + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
                  rw [hg_in] at hdg; simp at hdg; omega
                obtain ⟨ra, sa, ca, hca_supp, hca_eq⟩ := ih a (by omega)
                let c0 := b2z (g.op.eval [false])
                let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
                refine ⟨fun i => c0 + c1 * ra i, fun j => c1 * sa j, fun p => c1 * ca p, ?_, fun i j => ?_⟩
                · intro p hp
                  have hne : ca p ≠ 0 := fun h => hp (by simp [h])
                  have hs := hca_supp p hne
                  exact ⟨by omega, by omega⟩
                · rw [hval_gate idx.val idx.isLt i j]
                  change b2z (g.op.eval (g.inputs.map _)) = _
                  rw [hg_in, List.map_cons, List.map_nil]
                  have hanf := anf_one (fun x => g.op.eval [x])
                    ((wiresOf (inp i j) C.gates).getD a false)
                  change b2z (g.op.eval [_]) = c0 + c1 * val a i j at hanf
                  rw [hanf, hca_eq i j, mul_add, mul_add, Finset.mul_sum]
                  have hsm : ∑ p : NL, c1 * (ca p * val (w + v + p.val.val) i j) =
                      ∑ p : NL, c1 * ca p * val (w + v + p.val.val) i j :=
                    Finset.sum_congr rfl fun p _ => by ring
                  rw [hsm]; ring
              | cons b rest2 =>
                cases rest2 with
                | nil =>
                  have ha_lt : a < w + v + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
                  have hb_lt : b < w + v + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
                  have hab_d : dep a ≤ dep (w + v + idx.val) ∧ dep b ≤ dep (w + v + idx.val) := by
                    change dep (w + v + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
                    rw [hg_in] at hdg
                    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
                    omega
                  obtain ⟨ra, sa, ca, hca_supp, hca_eq⟩ := ih a (by omega)
                  obtain ⟨rb, sb, cb, hcb_supp, hcb_eq⟩ := ih b (by omega)
                  have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                      (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
                    unfold nlGate at hnlf; rw [hg_in] at hnlf; simpa using hnlf
                  let c0 := b2z (g.op.eval [false, false])
                  let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
                  let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
                  refine ⟨fun i => c0 + c1 * ra i + c2 * rb i,
                    fun j => c1 * sa j + c2 * sb j,
                    fun p => c1 * ca p + c2 * cb p, ?_, fun i j => ?_⟩
                  · intro p hp
                    by_cases h1 : ca p ≠ 0
                    · have hs := hca_supp p h1; exact ⟨by omega, by omega⟩
                    · push_neg at h1
                      have h2 : cb p ≠ 0 := fun h => hp (by simp [h1, h])
                      have hs := hcb_supp p h2; exact ⟨by omega, by omega⟩
                  · rw [hval_gate idx.val idx.isLt i j]
                    change b2z (g.op.eval (g.inputs.map _)) = _
                    rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
                    have hanf := anf_two (fun x y => g.op.eval [x, y])
                      ((wiresOf (inp i j) C.gates).getD a false)
                      ((wiresOf (inp i j) C.gates).getD b false)
                    rw [hxor] at hanf
                    have hbf : b2z false = 0 := rfl
                    change b2z (g.op.eval [_, _]) =
                      c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
                    rw [hbf, zero_mul, add_zero] at hanf
                    rw [hanf, hca_eq i j, hcb_eq i j]
                    have hsm : ∑ p : NL, (c1 * ca p + c2 * cb p) * val (w + v + p.val.val) i j =
                        c1 * (∑ p : NL, ca p * val (w + v + p.val.val) i j) +
                        c2 * (∑ p : NL, cb p * val (w + v + p.val.val) i j) := by
                      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                      refine Finset.sum_congr rfl fun p _ => by ring
                    rw [hsm]; ring
                | cons _ _ =>
                  rw [hg_in] at hgl; simp at hgl
        · refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, by simp, fun i j => ?_⟩
          simp only [val, zero_mul, Finset.sum_const_zero, add_zero]
          have hge : (wiresOf (inp i j) C.gates).length ≤ wire := by
            rw [wiresOf_length, hinp_len]; omega
          rw [List.getD_eq_default _ _ hge]; rfl
  have hNL_inputs : ∀ p : NL, ∃ a b : ℕ,
      C.gates[p.val.val].inputs = [a, b] ∧
      a < w + v + p.val.val ∧ b < w + v + p.val.val ∧
      dep a + 1 ≤ dep (w + v + p.val.val) ∧ dep b + 1 ≤ dep (w + v + p.val.val) := by
    intro p
    have hnl : nlGate C.gates[p.val.val] = true := (Finset.mem_filter.mp p.property).2
    have hlen2 : C.gates[p.val.val].inputs.length = 2 := by
      unfold nlGate at hnl
      have h1 := (Bool.and_eq_true _ _).mp hnl
      exact beq_iff_eq.mp h1.1
    obtain ⟨a, b, hab⟩ : ∃ a b, C.gates[p.val.val].inputs = [a, b] := by
      cases h : C.gates[p.val.val].inputs with
      | nil => rw [h] at hlen2; simp at hlen2
      | cons a l =>
        cases l with
        | nil => rw [h] at hlen2; simp at hlen2
        | cons b l2 =>
          cases l2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => rw [h] at hlen2; simp at hlen2
    have ha := hrb' p.val.val p.val.isLt a (by rw [hab]; simp)
    have hb := hrb' p.val.val p.val.isLt b (by rw [hab]; simp)
    have hdg := hdep_gate p.val.val p.val.isLt
    rw [hab, hnl] at hdg
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdg
    exact ⟨a, b, hab, ha, hb, by omega, by omega⟩
  choose in1 in2 hin_eq hin1_lt hin2_lt hin1_d hin2_d using hNL_inputs
  choose rw1 sw1 cw1 hcw1_supp hcw1_eq using fun p : NL => hdecomp_wire (in1 p)
  choose rw2 sw2 cw2 hcw2_supp hcw2_eq using fun p : NL => hdecomp_wire (in2 p)
  let K := NL ⊕ NL
  let α : K → Fin n → ZMod 2 := fun x i =>
    match x with
    | Sum.inl p => rw1 p i + rw1 p u0
    | Sum.inr p => rw2 p i + rw2 p u0
  let β : K → Fin m → ZMod 2 := fun y j =>
    match y with
    | Sum.inl p => sw1 p j + sw1 p v0
    | Sum.inr p => sw2 p j + sw2 p v0
  have hα0 : ∀ x : K, α x u0 = 0 := by rintro (p | p) <;> simp [α, zmod2_add_self]
  have hβ0 : ∀ y : K, β y v0 = 0 := by rintro (p | p) <;> simp [β, zmod2_add_self]
  have hNL_poly : ∀ m_idx : ℕ, ∀ p : NL, p.val.val = m_idx →
      val (w + v + p.val.val) ∈ PolyDeg α β (2 ^ dep (w + v + p.val.val)) := by
    intro m_idx
    induction m_idx using Nat.strong_induction_on with
    | ind m_idx ih =>
      intro p hp_eq
      have hdp_pos : 1 ≤ dep (w + v + p.val.val) := by have := hin1_d p; omega
      have hpow_pos : 1 ≤ 2 ^ (dep (w + v + p.val.val) - 1) := Nat.one_le_two_pow
      have h1_in : val (in1 p) ∈ PolyDeg α β (2 ^ (dep (w + v + p.val.val) - 1)) := by
        have hfun : val (in1 p) =
            (fun _ _ => rw1 p u0 + sw1 p v0) +
            (fun i _ => α (Sum.inl p) i) +
            (fun _ j => β (Sum.inl p) j) +
            ∑ q : NL, cw1 p q • val (w + v + q.val.val) := by
          funext i j
          rw [hcw1_eq p i j]
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, α, β]
          have h2 : rw1 p i + sw1 p j =
              (rw1 p u0 + sw1 p v0) + (rw1 p i + rw1 p u0) + (sw1 p j + sw1 p v0) := by
            have : (rw1 p u0 + sw1 p v0) + (rw1 p i + rw1 p u0) + (sw1 p j + sw1 p v0) =
                rw1 p i + sw1 p j + ((rw1 p u0 + rw1 p u0) + (sw1 p v0 + sw1 p v0)) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
          rw [h2]
        rw [hfun]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (polyDeg_const α β _ _) (polyDeg_alpha α β hpow_pos (Sum.inl p)))
          (polyDeg_beta α β hpow_pos (Sum.inl p))) ?_
        apply Submodule.sum_mem
        intro q _
        by_cases hq0 : cw1 p q = 0
        · rw [hq0, zero_smul]; exact Submodule.zero_mem _
        · apply Submodule.smul_mem
          have hsupp := hcw1_supp p q hq0
          have hqlt : q.val.val < m_idx := by have := hin1_lt p; omega
          have hqd : dep (w + v + q.val.val) ≤ dep (w + v + p.val.val) - 1 := by
            have := hin1_d p; omega
          exact polyDeg_mono α β (Nat.pow_le_pow_right (by omega) hqd) (ih q.val.val hqlt q rfl)
      have h2_in : val (in2 p) ∈ PolyDeg α β (2 ^ (dep (w + v + p.val.val) - 1)) := by
        have hfun : val (in2 p) =
            (fun _ _ => rw2 p u0 + sw2 p v0) +
            (fun i _ => α (Sum.inr p) i) +
            (fun _ j => β (Sum.inr p) j) +
            ∑ q : NL, cw2 p q • val (w + v + q.val.val) := by
          funext i j
          rw [hcw2_eq p i j]
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, α, β]
          have h2 : rw2 p i + sw2 p j =
              (rw2 p u0 + sw2 p v0) + (rw2 p i + rw2 p u0) + (sw2 p j + sw2 p v0) := by
            have : (rw2 p u0 + sw2 p v0) + (rw2 p i + rw2 p u0) + (sw2 p j + sw2 p v0) =
                rw2 p i + sw2 p j + ((rw2 p u0 + rw2 p u0) + (sw2 p v0 + sw2 p v0)) := by ring
            rw [this, zmod2_add_self, zmod2_add_self, add_zero, add_zero]
          rw [h2]
        rw [hfun]
        refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
          (polyDeg_const α β _ _) (polyDeg_alpha α β hpow_pos (Sum.inr p)))
          (polyDeg_beta α β hpow_pos (Sum.inr p))) ?_
        apply Submodule.sum_mem
        intro q _
        by_cases hq0 : cw2 p q = 0
        · rw [hq0, zero_smul]; exact Submodule.zero_mem _
        · apply Submodule.smul_mem
          have hsupp := hcw2_supp p q hq0
          have hqlt : q.val.val < m_idx := by have := hin2_lt p; omega
          have hqd : dep (w + v + q.val.val) ≤ dep (w + v + p.val.val) - 1 := by
            have := hin2_d p; omega
          exact polyDeg_mono α β (Nat.pow_le_pow_right (by omega) hqd) (ih q.val.val hqlt q rfl)
      let g := C.gates[p.val.val]
      have hnl : nlGate g = true := (Finset.mem_filter.mp p.property).2
      have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
        unfold nlGate at hnl
        exact ((Bool.and_eq_true _ _).mp hnl).2
      let c0 := b2z (g.op.eval [false, false])
      let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
      let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
      have hfun : val (w + v + p.val.val) =
          (fun _ _ => c0) + c1 • val (in1 p) + c2 • val (in2 p) +
          (fun i j => val (in1 p) i j * val (in2 p) i j) := by
        funext i j
        rw [hval_gate p.val.val p.val.isLt i j]
        change b2z (g.op.eval (g.inputs.map _)) = _
        rw [hin_eq p, List.map_cons, List.map_cons, List.map_nil]
        have hanf := anf_two (fun x y => g.op.eval [x, y])
          ((wiresOf (inp i j) C.gates).getD (in1 p) false)
          ((wiresOf (inp i j) C.gates).getD (in2 p) false)
        rw [hxor] at hanf
        have hbt : b2z true = 1 := rfl
        change b2z (g.op.eval [_, _]) =
          c0 + c1 * val (in1 p) i j + c2 * val (in2 p) i j +
          b2z true * (val (in1 p) i j * val (in2 p) i j) at hanf
        rw [hbt, one_mul] at hanf
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hanf
      have h2eq : 2 ^ (dep (w + v + p.val.val) - 1) + 2 ^ (dep (w + v + p.val.val) - 1) =
          2 ^ dep (w + v + p.val.val) := by
        have hsucc : dep (w + v + p.val.val) = (dep (w + v + p.val.val) - 1) + 1 := by omega
        conv_rhs => rw [hsucc, pow_succ]
        omega
      have hle_half : 2 ^ (dep (w + v + p.val.val) - 1) ≤ 2 ^ dep (w + v + p.val.val) := by omega
      rw [hfun]
      refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
        (polyDeg_const α β _ _)
        (Submodule.smul_mem _ _ (polyDeg_mono α β hle_half h1_in)))
        (Submodule.smul_mem _ _ (polyDeg_mono α β hle_half h2_in))) ?_
      rw [← h2eq]
      exact polyDeg_mul α β h1_in h2_in
  obtain ⟨rout, sout, cout, hcout_supp, hcout_eq⟩ := hdecomp_wire C.output
  let f_poly : Fin n → Fin m → ZMod 2 := fun i j =>
    ∑ p : NL, cout p * val (w + v + p.val.val) i j
  have hf_in : f_poly ∈ PolyDeg α β (2 * 2 ^ d) := by
    have hfun : f_poly = ∑ p : NL, cout p • val (w + v + p.val.val) := by
      funext i j; simp [f_poly]
    rw [hfun]
    apply Submodule.sum_mem
    intro p _
    by_cases hp0 : cout p = 0
    · rw [hp0, zero_smul]; exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      have hdp : dep (w + v + p.val.val) ≤ d + 1 :=
        le_trans (hcout_supp p hp0).2 hdep
      have hpow : 2 ^ dep (w + v + p.val.val) ≤ 2 * 2 ^ d := by
        calc 2 ^ dep (w + v + p.val.val) ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) hdp
          _ = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
      exact polyDeg_mono α β hpow (hNL_poly p.val.val p rfl)
  have hAeq : anchor u0 v0 (fun i j => M i j) = anchor u0 v0 f_poly := by
    have h1 : (fun i j => M i j) = fun i j => (rout i + sout j) + f_poly i j := by
      funext i j
      exact hcout_eq i j
    rw [h1, anchor_add, anchor_split, zero_add]
  have hKcard : Fintype.card K = 2 * t := by
    simp only [K, Fintype.card_sum, Fintype.card_coe, hNL_card]
    omega
  have hanch_rk := rank_anchor_polyDeg u0 v0 α β hα0 hβ0 (2 ^ d) hf_in
  rw [hKcard, ← hAeq] at hanch_rk
  have hundo := rank_le_two_add_anchor u0 v0 M
  omega

end AnchoredRankBound

section BalancedSupport

def massOn {n : ℕ} (G : Fin n → Fin n → Bool) (U : Finset (Fin n)) (i : Fin n) : ℚ :=
  ∑ b ∈ U, if G i b then (1 : ℚ) else 0

def scoreOn {n : ℕ} (G : Fin n → Fin n → Bool) (U : Finset (Fin n)) : ℚ :=
  ∑ i ∈ U, (1 : ℚ) / massOn G U i

def dropOn {n : ℕ} (G : Fin n → Fin n → Bool) (U : Finset (Fin n)) (x : Fin n) : Finset (Fin n) :=
  U.filter (fun y => G y x = false)

noncomputable def rkOn {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) (U : Finset (Fin n)) : ℕ :=
  (M.submatrix (Subtype.val : ↥U → Fin n) (Subtype.val : ↥U → Fin n)).rank

lemma massOn_pos {n : ℕ} (G : Fin n → Fin n → Bool) (hdiag : ∀ i, G i i = true)
    {U : Finset (Fin n)} {i : Fin n} (hi : i ∈ U) : 0 < massOn G U i := by
  refine Finset.sum_pos' (fun b _ => ?_) ⟨i, hi, ?_⟩
  · cases G i b <;> simp only [Bool.false_eq_true, ↓reduceIte, le_refl, zero_le_one]
  · simp only [hdiag i, ↓reduceIte, zero_lt_one]

lemma massOn_le_of_subset {n : ℕ} (G : Fin n → Fin n → Bool)
    {V U : Finset (Fin n)} (hVU : V ⊆ U) (i : Fin n) :
    massOn G V i ≤ massOn G U i :=
  Finset.sum_le_sum_of_subset_of_nonneg hVU fun b _ _ => by
    cases G i b <;> simp only [Bool.false_eq_true, ↓reduceIte, le_refl, zero_le_one]

lemma dropOn_ssubset {n : ℕ} (G : Fin n → Fin n → Bool)
    (hdiag : ∀ i, G i i = true) {U : Finset (Fin n)} {x : Fin n} (hx : x ∈ U) :
    dropOn G U x ⊂ U :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ U, fun h => by
    have hmem : x ∈ dropOn G U x := h.symm ▸ hx
    have hfx : G x x = false := (Finset.mem_filter.mp hmem).2
    rw [hdiag x] at hfx
    exact Bool.noConfusion hfx⟩

lemma rkOn_univ {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2)) :
    rkOn M Finset.univ = M.rank :=
  Matrix.rank_submatrix M (Equiv.subtypeUnivEquiv Finset.mem_univ)
    (Equiv.subtypeUnivEquiv Finset.mem_univ)

lemma rkOn_drop_succ_le {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (G : Fin n → Fin n → Bool) (hsupp : ∀ i j, G i j = true ↔ M i j ≠ 0)
    (hdiag : ∀ i, G i i = true) {U : Finset (Fin n)} {x : Fin n} (hx : x ∈ U) :
    rkOn M (dropOn G U x) + 1 ≤ rkOn M U := by
  let U' : Finset (Fin n) := dropOn G U x
  let V : Finset (Fin n) := insert x U'
  have hVU : V ⊆ U := Finset.insert_subset_iff.mpr ⟨hx, Finset.filter_subset _ U⟩
  have hsub : rkOn M V ≤ rkOn M U :=
    Matrix.rank_submatrix_le (M.submatrix (Subtype.val : ↥U → Fin n) Subtype.val)
      (fun v : ↥V => (⟨v.1, hVU v.2⟩ : ↥U)) (fun v : ↥V => (⟨v.1, hVU v.2⟩ : ↥U))
  let A : Matrix ↥V ↥V (ZMod 2) := M.submatrix Subtype.val Subtype.val
  let B : Matrix ↥U' ↥U' (ZMod 2) := M.submatrix Subtype.val Subtype.val
  let x0 : ↥V := ⟨x, Finset.mem_insert_self x U'⟩
  let π : (↥V → ZMod 2) →ₗ[ZMod 2] (↥U' → ZMod 2) :=
    { toFun := fun v u => v ⟨u.1, Finset.mem_insert_of_mem u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let S_U' : Submodule (ZMod 2) (↥V → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range fun u : ↥U' => A.row ⟨u.1, Finset.mem_insert_of_mem u.2⟩)
  let S_V : Submodule (ZMod 2) (↥V → ZMod 2) := Submodule.span (ZMod 2) (Set.range A.row)
  have hzero : ∀ v ∈ S_U', v x0 = 0 := fun v hv => by
    refine Submodule.span_induction ?_ rfl
      (fun _ _ _ _ ha hb => by simp only [Pi.add_apply, ha, hb, add_zero])
      (fun a _ _ hb => by simp only [Pi.smul_apply, hb, smul_zero]) hv
    rintro _ ⟨u, rfl⟩
    by_contra hne
    have ht : G u.1 x = true := (hsupp u.1 x).mpr hne
    rw [(Finset.mem_filter.mp u.2).2] at ht
    exact Bool.noConfusion ht
  have hinj : Function.Injective (π.comp S_U'.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply Subtype.ext
    funext a
    by_cases hax : a = x0
    · exact hax ▸ hzero v.1 v.2
    · have haU' : a.1 ∈ U' := (Finset.mem_insert.mp a.2).resolve_left fun h => hax (Subtype.ext h)
      exact congrFun hv ⟨a.1, haU'⟩
  have hmap : LinearMap.range (π.comp S_U'.subtype) = Submodule.span (ZMod 2) (Set.range B.row) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_span, ← Set.range_comp]
    rfl
  have hB_eq : rkOn M U' = Module.finrank (ZMod 2) S_U' := by
    change B.rank = Module.finrank (ZMod 2) S_U'
    rw [Matrix.rank_eq_finrank_span_row B, ← hmap, LinearMap.finrank_range_of_inj hinj]
  have hle_sub : S_U' ≤ S_V := Submodule.span_mono <| by
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u.1, Finset.mem_insert_of_mem u.2⟩, rfl⟩
  have hlt_sub : S_U' < S_V := lt_of_le_of_ne hle_sub fun heq => by
    have hx_mem : A.row x0 ∈ S_V := Submodule.subset_span ⟨x0, rfl⟩
    exact (hsupp x x).mp (hdiag x) (hzero _ (heq ▸ hx_mem))
  have hlt_rk : Module.finrank (ZMod 2) S_U' < rkOn M V := by
    change Module.finrank (ZMod 2) S_U' < A.rank
    rw [Matrix.rank_eq_finrank_span_row A]
    exact Submodule.finrank_lt_finrank_of_lt hlt_sub
  exact le_trans (hB_eq ▸ Nat.succ_le_of_lt hlt_rk) hsub

lemma card_mul_scoreOn_eq {n : ℕ} (G : Fin n → Fin n → Bool)
    (hdiag : ∀ i, G i i = true) (U : Finset (Fin n)) :
    (U.card : ℚ) * scoreOn G U =
      ∑ x ∈ U, ((∑ y ∈ dropOn G U x, (1 : ℚ) / massOn G U y) + 1) := by
  have hinner :
      (∑ x ∈ U, ∑ y ∈ dropOn G U x, (1 : ℚ) / massOn G U y) =
        (U.card : ℚ) * scoreOn G U - (U.card : ℚ) := by
    calc
      (∑ x ∈ U, ∑ y ∈ dropOn G U x, (1 : ℚ) / massOn G U y)
          = ∑ x ∈ U, ∑ y ∈ U, if G y x = false then (1 : ℚ) / massOn G U y else 0 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [dropOn, Finset.sum_filter]
      _ = ∑ y ∈ U, ∑ x ∈ U, if G y x = false then (1 : ℚ) / massOn G U y else 0 :=
            Finset.sum_comm
      _ = ∑ y ∈ U, ((U.card : ℚ) * ((1 : ℚ) / massOn G U y) - 1) := by
            refine Finset.sum_congr rfl fun y hy => ?_
            have hpart : (∑ x ∈ U, if G y x = false then (1 : ℚ) else 0) +
                massOn G U y = (U.card : ℚ) := by
              rw [massOn, ← Finset.sum_add_distrib]
              have h1 : (∑ x ∈ U, ((if G y x = false then (1 : ℚ) else 0) +
                  if G y x = true then (1 : ℚ) else 0)) = ∑ _x ∈ U, (1 : ℚ) := by
                refine Finset.sum_congr rfl fun x _ => ?_
                cases G y x <;> simp
              rw [h1]; simp
            have hne : massOn G U y ≠ 0 := ne_of_gt (massOn_pos G hdiag hy)
            calc
              (∑ x ∈ U, if G y x = false then (1 : ℚ) / massOn G U y else 0)
                  = (∑ x ∈ U, if G y x = false then (1 : ℚ) else 0) * ((1 : ℚ) / massOn G U y) := by
                    rw [Finset.sum_mul]
                    refine Finset.sum_congr rfl fun x _ => ?_
                    cases G y x <;> simp
              _ = ((U.card : ℚ) - massOn G U y) * ((1 : ℚ) / massOn G U y) := by
                    rw [eq_sub_of_add_eq hpart]
              _ = (U.card : ℚ) * ((1 : ℚ) / massOn G U y) - 1 := by
                    rw [sub_mul, mul_one_div_cancel hne]
      _ = (U.card : ℚ) * scoreOn G U - (U.card : ℚ) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum, scoreOn]; simp
  symm
  calc
    (∑ x ∈ U, ((∑ y ∈ dropOn G U x, (1 : ℚ) / massOn G U y) + 1))
        = (∑ x ∈ U, ∑ y ∈ dropOn G U x, (1 : ℚ) / massOn G U y) + (U.card : ℚ) := by
          rw [Finset.sum_add_distrib]; simp
    _ = ((U.card : ℚ) * scoreOn G U - (U.card : ℚ)) + (U.card : ℚ) := by rw [hinner]
    _ = (U.card : ℚ) * scoreOn G U := sub_add_cancel _ _

lemma scoreOn_le_rkOn {n : ℕ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (G : Fin n → Fin n → Bool) (hsupp : ∀ i j, G i j = true ↔ M i j ≠ 0)
    (hdiag : ∀ i, G i i = true) (U : Finset (Fin n)) :
    scoreOn G U ≤ (rkOn M U : ℚ) := by
  induction U using Finset.strongInduction with
  | H U ih =>
    by_cases hU : U = ∅
    · subst hU; simp only [scoreOn, Finset.sum_empty, Nat.cast_nonneg]
    · have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
      have hcard_pos : (0 : ℚ) < (U.card : ℚ) := Nat.cast_pos.mpr hne.card_pos
      have hmul : (U.card : ℚ) * scoreOn G U ≤ (U.card : ℚ) * (rkOn M U : ℚ) := by
        rw [card_mul_scoreOn_eq G hdiag U]
        have hrhs : (U.card : ℚ) * (rkOn M U : ℚ) = ∑ _x ∈ U, (rkOn M U : ℚ) := by simp
        rw [hrhs]
        refine Finset.sum_le_sum fun x hx => ?_
        have hdrop : (∑ y ∈ dropOn G U x, (1 : ℚ) / massOn G U y) ≤ scoreOn G (dropOn G U x) :=
          Finset.sum_le_sum fun y hy =>
            div_le_div_of_nonneg_left zero_le_one (massOn_pos G hdiag hy)
              (massOn_le_of_subset G (Finset.filter_subset _ U) y)
        have hih := ih (dropOn G U x) (dropOn_ssubset G hdiag hx)
        have hrk : (rkOn M (dropOn G U x) : ℚ) + 1 ≤ (rkOn M U : ℚ) := by
          have h := Nat.cast_le (α := ℚ).mpr (rkOn_drop_succ_le M G hsupp hdiag hx)
          rw [Nat.cast_add, Nat.cast_one] at h
          exact h
        linarith
      exact le_of_mul_le_mul_left hmul hcard_pos

lemma massOn_univ_eq_card {m : ℕ} (G : Fin m → Fin m → Bool) :
    ∀ i : Fin m, massOn G Finset.univ i = ((Finset.univ.filter fun j : Fin m => G i j = true).card : ℚ) := by
  intro i
  have h1 : ∀ s : Finset (Fin m),
      (∑ b ∈ s, if G i b then (1 : ℚ) else 0) = ((s.filter fun j => G i j = true).card : ℚ) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.filter_cons]
      have hna : a ∉ s.filter (fun j => G i j = true) := fun h => ha (Finset.mem_filter.mp h).1
      cases hga : G i a
      · simp [ih]
      · simp [ih, Finset.card_insert_of_notMem hna, add_comm]
  exact h1 Finset.univ

lemma quad_step_rat (z d : ℕ) (hd : 0 < d) :
    (2 * (z : ℚ) + 1) ≤ (d : ℚ) + ((z : ℚ) * ((z : ℚ) + 1)) * ((1 : ℚ) / (d : ℚ)) := by
  have hd_pos : (0 : ℚ) < (d : ℚ) := Nat.cast_pos.mpr hd
  have hquad_int : (2 * (z : ℤ) + 1) * (d : ℤ) ≤
      (d : ℤ) * (d : ℤ) + (z : ℤ) * ((z : ℤ) + 1) := by
    have hcases : (d : ℤ) ≤ z ∨ (z : ℤ) + 1 ≤ d := by omega
    have hprod : 0 ≤ ((d : ℤ) - z) * ((d : ℤ) - (z + 1)) := by
      rcases hcases with hle | hge
      · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
      · exact mul_nonneg (by omega) (by omega)
    have hexp : ((d : ℤ) - z) * ((d : ℤ) - (z + 1)) =
        (d : ℤ) * (d : ℤ) + (z : ℤ) * ((z : ℤ) + 1) - (2 * (z : ℤ) + 1) * (d : ℤ) := by
      ring
    exact sub_nonneg.mp (hexp ▸ hprod)
  have hquad_q : (2 * (z : ℚ) + 1) * (d : ℚ) ≤
      (d : ℚ) * (d : ℚ) + (z : ℚ) * ((z : ℚ) + 1) := by
    have hcast := Int.cast_le (R := ℚ).mpr hquad_int
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one, Int.cast_natCast] using hcast
  have hmul : (2 * (z : ℚ) + 1) * (d : ℚ) ≤
      ((d : ℚ) + ((z : ℚ) * ((z : ℚ) + 1)) * ((1 : ℚ) / (d : ℚ))) * (d : ℚ) := by
    conv_rhs =>
      rw [add_mul, mul_assoc ((z : ℚ) * ((z : ℚ) + 1)), one_div_mul_cancel (ne_of_gt hd_pos), mul_one]
    exact hquad_q
  exact le_of_mul_le_mul_right hmul hd_pos

lemma sum_deg_bound_rat {m p : ℕ} (G : Fin m → Fin m → Bool)
    (hdiag : ∀ i, G i i = true) (hscore : scoreOn G Finset.univ ≤ (p : ℚ)) :
    (m : ℚ) * (2 * ((m / p : ℕ) : ℚ) + 1) ≤
      ((∑ i : Fin m, (Finset.univ.filter fun j : Fin m => G i j = true).card : ℕ) : ℚ) +
        (((m / p : ℕ) : ℚ) * (((m / p : ℕ) : ℚ) + 1)) * (p : ℚ) := by
  set z := m / p
  let deg : Fin m → ℕ := fun i => (Finset.univ.filter fun j : Fin m => G i j = true).card
  have hdeg_pos : ∀ i : Fin m, 0 < deg i := fun i =>
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hdiag i⟩⟩
  have h1 : (∑ _i : Fin m, (2 * (z : ℚ) + 1)) ≤
      ∑ i : Fin m, ((deg i : ℚ) + ((z : ℚ) * ((z : ℚ) + 1)) * ((1 : ℚ) / (deg i : ℚ))) :=
    Finset.sum_le_sum fun i _ => quad_step_rat z (deg i) (hdeg_pos i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have hsc : (∑ i : Fin m, (1 : ℚ) / (deg i : ℚ)) = scoreOn G Finset.univ := by
    dsimp only [scoreOn]
    exact Finset.sum_congr rfl fun i _ => by rw [massOn_univ_eq_card G i]
  rw [hsc] at h1
  have hzz_nonneg : (0 : ℚ) ≤ (z : ℚ) * ((z : ℚ) + 1) :=
    mul_nonneg (Nat.cast_nonneg z) (add_nonneg (Nat.cast_nonneg z) zero_le_one)
  have h2 : ((z : ℚ) * ((z : ℚ) + 1)) * scoreOn G Finset.univ ≤
      ((z : ℚ) * ((z : ℚ) + 1)) * (p : ℚ) :=
    mul_le_mul_of_nonneg_left hscore hzz_nonneg
  have hcast_sum : (∑ i : Fin m, (deg i : ℚ)) = ((∑ i : Fin m, deg i : ℕ) : ℚ) := by
    have h : ∀ s : Finset (Fin m), (∑ i ∈ s, (deg i : ℚ)) = ((∑ i ∈ s, deg i : ℕ) : ℚ) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => simp
      | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Nat.cast_add, ih]
    exact h Finset.univ
  rw [hcast_sum] at h1
  exact le_trans h1 (add_le_add le_rfl h2)

lemma sum_deg_eq_card {m : ℕ} (G : Fin m → Fin m → Bool) :
    (∑ i : Fin m, (Finset.univ.filter fun j : Fin m => G i j = true).card) =
      (Finset.univ.filter fun ij : Fin m × Fin m => G ij.1 ij.2 = true).card := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => Finset.card_filter _ _

lemma balanced_from_rat {m p : ℕ} (hp : 0 < p) (S : ℕ)
    (hbound_q : (m : ℚ) * (2 * ((m / p : ℕ) : ℚ) + 1) ≤
      (S : ℚ) + (((m / p : ℕ) : ℚ) * (((m / p : ℕ) : ℚ) + 1)) * (p : ℚ)) :
    (p - m % p) * (m / p) ^ 2 + (m % p) * (m / p + 1) ^ 2 ≤ S := by
  set z := m / p
  set rem := m % p
  have hrem_le : rem ≤ p := Nat.le_of_lt (Nat.mod_lt m hp)
  have hm_eq : m = p * z + rem := (Nat.div_add_mod m p).symm
  have hcast : (((p - rem) * z ^ 2 + rem * (z + 1) ^ 2 : ℕ) : ℚ) ≤ (S : ℚ) := by
    have hpr : ((p - rem : ℕ) : ℚ) = (p : ℚ) - (rem : ℚ) := Nat.cast_sub hrem_le
    have hmq : (m : ℚ) = (p : ℚ) * (z : ℚ) + (rem : ℚ) := by
      have h := congrArg (Nat.cast (R := ℚ)) hm_eq
      simpa only [Nat.cast_add, Nat.cast_mul] using h
    have hid : ((p : ℚ) - (rem : ℚ)) * (z : ℚ) ^ 2 + (rem : ℚ) * ((z : ℚ) + 1) ^ 2 =
        (m : ℚ) * (2 * (z : ℚ) + 1) - ((z : ℚ) * ((z : ℚ) + 1)) * (p : ℚ) := by
      rw [hmq]; ring
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow,
      Nat.cast_add, Nat.cast_one, hpr, hid]
    exact sub_le_iff_le_add.mpr hbound_q
  exact (Nat.cast_le (α := ℚ)).mp hcast

lemma balanced_support_bound {m p : ℕ} (hp : 0 < p)
    (G : Fin m → Fin m → Bool) (hdiag : ∀ i, G i i = true)
    (hrk : (Matrix.of fun i j => b2z (G i j)).rank ≤ p) :
    let z := m / p
    let rem := m % p
    (p - rem) * z ^ 2 + rem * (z + 1) ^ 2 ≤
      (Finset.univ.filter fun ij : Fin m × Fin m => G ij.1 ij.2 = true).card := by
  let M : Matrix (Fin m) (Fin m) (ZMod 2) := Matrix.of fun i j => b2z (G i j)
  have hsupp : ∀ i j, G i j = true ↔ M i j ≠ 0 := by
    intro i j; dsimp only [M, Matrix.of_apply, b2z]; cases G i j <;> simp
  have hscore : scoreOn G Finset.univ ≤ (p : ℚ) := by
    have h1 := scoreOn_le_rkOn M G hsupp hdiag Finset.univ
    rw [rkOn_univ] at h1
    exact le_trans h1 (Nat.cast_le.mpr hrk)
  have hrat := sum_deg_bound_rat G hdiag hscore
  rw [sum_deg_eq_card G] at hrat
  exact balanced_from_rat hp _ hrat

end BalancedSupport

section MainAssembly

lemma cipher_bounds (k r h : ℕ) (hh : 0 < h)
    (hk : h + (if r = 0 then 2 else if r = 1 then 7 else 7 * r - 2) ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (a c : Fin (2 ^ h)) (rowBase colBase : Fin (2 ^ k)) :
    let X := Fin (2 ^ h)
    let keys := fun (x y : X) => (Finset.univ.filter (fun key : Fin (2 ^ k) =>
      runN k r masks false key.val (nameN k r h 1 rowBase x) >>> (k - h) = a.val ∧
      runN k r masks true key.val (nameN k r h 2 colBase y) >>> (k - h) = c.val)).card
    let u := if r = 2 then 4 * (h / 15) + min 4 (h % 15)
      else if r = 3 then 2 * (h / 13) + min 2 (h % 13) else h
    let load := 2 ^ (k - u)
    let b := if r = 0 then 2 else if r = 1 then 7 else 7 * r - 2
    let degree := min (2 ^ h) (2 ^ (if r = 2 then 11 else b))
    (∀ x : X, ∑ y : X, keys x y ≤ load) ∧
    (∀ y : X, ∑ x : X, keys x y ≤ load) ∧
    ((∀ x : X, (Finset.univ.filter fun y : X => 0 < keys x y).card ≤ degree) ∨
     (∀ y : X, (Finset.univ.filter fun x : X => 0 < keys x y).card ≤ degree)) := by
  intro X keys u load b degree
  have hk3 : 2 < k := by
    have hb2 : 2 ≤ b := by dsimp [b]; split_ifs <;> omega
    omega
  have : NeZero k := ⟨by omega⟩
  have hrow_gap : 1 * r + h ≤ k := by split_ifs at hk <;> omega
  have hcol_gap : 2 * r + h ≤ k := by split_ifs at hk <;> omega
  have hrow_hw : (4 * r + 1) + h ≤ k + 1 := by split_ifs at hk <;> omega
  have hcol_hw : (6 * r + 1) + h ≤ k + 1 := by split_ifs at hk <;> omega
  let cr : ℕ → ZMod k → ZMod 2 := fun j => toW k (masks j).val
  let cc : ℕ → ZMod k → ZMod 2 := fun j => toW k (masks (r + j)).val
  let tgtA : ℕ → ZMod 2 := fun j => b2z (a.val.testBit j)
  let tgtC : ℕ → ZMod 2 := fun j => b2z (c.val.testBit j)
  let RPred : X → (ZMod k → ZMod 2) → Prop := fun x keyW =>
    ∀ j < h, rowSt cr (toW k (nameN k r h 1 rowBase x)) keyW r ((k - h + j : ℕ) : ZMod k) = tgtA j
  let CPred : X → (ZMod k → ZMod 2) → Prop := fun y keyW =>
    ∀ j < h, colSt cc (toW k (nameN k r h 2 colBase y)) keyW r ((k - h + j : ℕ) : ZMod k) = tgtC j
  have hR_iff : ∀ (x : X) (key : Fin (2 ^ k)),
      runN k r masks false key.val (nameN k r h 1 rowBase x) >>> (k - h) = a.val ↔
        RPred x (toW k key.val) := by
    intro x key
    have hn := (nameN_spec hrow_gap rowBase x).1
    have hout := runN_lt (r := r) masks false key.val (nameN k r h 1 rowBase x) hn
    rw [shr_eq_iff_win (by omega) _ hout a, toW_runN_false (by omega) r masks key.val _ key.isLt hn]
  have hC_iff : ∀ (y : X) (key : Fin (2 ^ k)),
      runN k r masks true key.val (nameN k r h 2 colBase y) >>> (k - h) = c.val ↔
        CPred y (toW k key.val) := by
    intro y key
    have hn := (nameN_spec hcol_gap colBase y).1
    have hout := runN_lt (r := r) masks true key.val (nameN k r h 2 colBase y) hn
    rw [shr_eq_iff_win (by omega) _ hout c, toW_runN_true hk3 r masks key.val _ key.isLt hn]
  have hkeys_eq : ∀ x y : X,
      keys x y = Nat.card {keyW : ZMod k → ZMod 2 // RPred x keyW ∧ CPred y keyW} := by
    intro x y
    dsimp only [keys]
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine Finset.card_nbij' (fun key => toW k key.val) (fun keyW => fromW k keyW) ?_ ?_ ?_ ?_
    · intro key hmem
      rcases Finset.mem_filter.mp hmem with ⟨_, hr1, hc1⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hR_iff x key).mp hr1, (hC_iff y key).mp hc1⟩
    · intro keyW hmem
      rcases Finset.mem_filter.mp hmem with ⟨_, hr1, hc1⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (hR_iff x (fromW k keyW)).mpr (by rw [toW_fromW]; exact hr1)
      · exact (hC_iff y (fromW k keyW)).mpr (by rw [toW_fromW]; exact hc1)
    · intro key _; exact fromW_toW k key
    · intro keyW _; exact toW_fromW k keyW
  have huniq_row : ∀ keyW : ZMod k → ZMod 2, ∃! x : X, RPred x keyW := fun keyW =>
    unique_slice_of_dep_piv hrow_gap hrow_hw rowBase (fun u => rowSt cr u keyW r)
      (by simpa using row_name_dep cr keyW r) (by simpa using row_name_piv cr keyW r (by omega)) a
  have huniq_col : ∀ keyW : ZMod k → ZMod 2, ∃! y : X, CPred y keyW := fun keyW =>
    unique_slice_of_dep_piv hcol_gap hcol_hw colBase (fun v => colSt cc v keyW r)
      (col_name_dep cc keyW r) (col_name_piv cc keyW r (by omega)) c
  have hrow_sum : ∀ x : X, (∑ y : X, keys x y) = Nat.card {keyW : ZMod k → ZMod 2 // RPred x keyW} := by
    intro x
    classical
    simp_rw [hkeys_eq]
    have h1 : ∀ y : X, Nat.card {keyW : ZMod k → ZMod 2 // RPred x keyW ∧ CPred y keyW} =
        ∑ keyW : ZMod k → ZMod 2, if RPred x keyW ∧ CPred y keyW then 1 else 0 := fun y => by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ keyW : ZMod k → ZMod 2,
        (∑ y : X, if RPred x keyW ∧ CPred y keyW then 1 else 0) = if RPred x keyW then 1 else 0 := by
      intro keyW
      by_cases hr : RPred x keyW
      · obtain ⟨y0, hy0, hyu⟩ := huniq_col keyW
        rw [if_pos hr, Finset.sum_eq_single y0]
        · simp [hr, hy0]
        · intro y _ hne; simp [show ¬ CPred y keyW from fun h => hne (hyu y h)]
        · intro h; exact absurd (Finset.mem_univ y0) h
      · simp [hr]
    simp_rw [h2, ← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have hcol_sum : ∀ y : X, (∑ x : X, keys x y) = Nat.card {keyW : ZMod k → ZMod 2 // CPred y keyW} := by
    intro y
    classical
    simp_rw [hkeys_eq]
    have h1 : ∀ x : X, Nat.card {keyW : ZMod k → ZMod 2 // RPred x keyW ∧ CPred y keyW} =
        ∑ keyW : ZMod k → ZMod 2, if RPred x keyW ∧ CPred y keyW then 1 else 0 := fun x => by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ keyW : ZMod k → ZMod 2,
        (∑ x : X, if RPred x keyW ∧ CPred y keyW then 1 else 0) = if CPred y keyW then 1 else 0 := by
      intro keyW
      by_cases hc : CPred y keyW
      · obtain ⟨x0, hx0, hxu⟩ := huniq_row keyW
        rw [if_pos hc, Finset.sum_eq_single x0]
        · simp [hc, hx0]
        · intro x _ hne; simp [show ¬ RPred x keyW from fun h => hne (hxu x h)]
        · intro h; exact absurd (Finset.mem_univ x0) h
      · simp [hc]
    simp_rw [h2, ← Finset.card_filter, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  let v := if r = 2 then 11 else b
  have hvk : h + v ≤ k := by dsimp [v, b]; split_ifs at hk ⊢ <;> omega
  have hunused : ∀ x y : X, 0 < keys x y → 2 ^ (k - (h + v)) ≤ keys x y := by
    intro x y hpos
    rw [hkeys_eq x y] at hpos ⊢
    obtain ⟨key0, hkey0R, hkey0C⟩ : ∃ keyW : ZMod k → ZMod 2, RPred x keyW ∧ CPred y keyW := by
      classical
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hpos
      obtain ⟨kw, hkw⟩ := Finset.card_pos.mp hpos
      exact ⟨kw, (Finset.mem_filter.mp hkw).2⟩
    by_cases hr0 : r = 0
    · subst hr0
      have hv2 : v = 2 := rfl
      rw [hv2]
      exact card_pos_ge_unused (by omega)
        (dep_weaken (row_key_dep cr _ 0) 3 3 (by omega) (by omega))
        (dep_weaken (col_key_dep cc _ 0) 3 3 (by omega) (by omega))
        tgtA tgtC key0 hkey0R hkey0C
    · by_cases hr1 : r = 1
      · subst hr1
        have hv7 : v = 7 := rfl
        rw [hv7]
        exact card_pos_ge_unused (by omega)
          (dep_weaken (row_key_dep cr _ 1) 5 8 (by omega) (by omega))
          (dep_weaken (col_key_dep cc _ 1) 5 8 (by omega) (by omega))
          tgtA tgtC key0 hkey0R hkey0C
      · by_cases hr2 : r = 2
        · subst hr2
          have hv11 : v = 11 := rfl
          rw [hv11]
          have hk12 : h + 12 ≤ k := by simpa using hk
          exact card_pos_ge_unused (by omega)
            (dep_weaken (row_key_dep cr _ 2) 6 12 (by omega) (by omega))
            (col_key_dep_two_sharp cc _ (by omega))
            tgtA tgtC key0 hkey0R hkey0C
        · have hr3 : 3 ≤ r := by omega
          have hv_big : v = 7 * r - 2 := by
            dsimp [v, b]
            rw [if_neg hr2, if_neg hr0, if_neg hr1]
          rw [hv_big]
          exact card_pos_ge_unused (by omega)
            (dep_weaken (row_key_dep cr _ r) (3 * r + 1) (7 * r - 2 + 1)
              (by omega) (by omega))
            (dep_weaken (col_key_dep cc _ r) (3 * r + 1) (7 * r - 2 + 1)
              (by omega) (by omega))
            tgtA tgtC key0 hkey0R hkey0C
  have hdeg_of_row_reg : (∀ x : X, ∑ y : X, keys x y = 2 ^ (k - h)) →
      ∀ x : X, (Finset.univ.filter fun y : X => 0 < keys x y).card ≤ degree := by
    intro hreg x
    refine le_min ?_ ?_
    · calc (Finset.univ.filter fun y : X => 0 < keys x y).card
          ≤ (Finset.univ : Finset X).card := Finset.card_filter_le _ _
        _ = 2 ^ h := by simp [X]
    · have hmul : (Finset.univ.filter fun y : X => 0 < keys x y).card * 2 ^ (k - (h + v)) ≤
          2 ^ v * 2 ^ (k - (h + v)) := by
        calc (Finset.univ.filter fun y : X => 0 < keys x y).card * 2 ^ (k - (h + v))
            = ∑ _y ∈ Finset.univ.filter (fun y : X => 0 < keys x y), 2 ^ (k - (h + v)) := by simp
          _ ≤ ∑ y ∈ Finset.univ.filter (fun y : X => 0 < keys x y), keys x y :=
              Finset.sum_le_sum fun y hy => hunused x y (Finset.mem_filter.mp hy).2
          _ ≤ ∑ y : X, keys x y := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ = 2 ^ (k - h) := hreg x
          _ = 2 ^ v * 2 ^ (k - (h + v)) := by rw [← pow_add]; congr 1; omega
      exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)
  have hdeg_of_col_reg : (∀ y : X, ∑ x : X, keys x y = 2 ^ (k - h)) →
      ∀ y : X, (Finset.univ.filter fun x : X => 0 < keys x y).card ≤ degree := by
    intro hreg y
    refine le_min ?_ ?_
    · calc (Finset.univ.filter fun x : X => 0 < keys x y).card
          ≤ (Finset.univ : Finset X).card := Finset.card_filter_le _ _
        _ = 2 ^ h := by simp [X]
    · have hmul : (Finset.univ.filter fun x : X => 0 < keys x y).card * 2 ^ (k - (h + v)) ≤
          2 ^ v * 2 ^ (k - (h + v)) := by
        calc (Finset.univ.filter fun x : X => 0 < keys x y).card * 2 ^ (k - (h + v))
            = ∑ _x ∈ Finset.univ.filter (fun x : X => 0 < keys x y), 2 ^ (k - (h + v)) := by simp
          _ ≤ ∑ x ∈ Finset.univ.filter (fun x : X => 0 < keys x y), keys x y :=
              Finset.sum_le_sum fun x hx => hunused x y (Finset.mem_filter.mp hx).2
          _ ≤ ∑ x : X, keys x y := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ = 2 ^ (k - h) := hreg y
          _ = 2 ^ v * 2 ^ (k - (h + v)) := by rw [← pow_add]; congr 1; omega
      exact Nat.le_of_mul_le_mul_right hmul (Nat.two_pow_pos _)
  by_cases hr0 : r = 0
  · subst hr0
    have hk2 : h + 2 ≤ k := by simpa using hk
    have hu : u = h := rfl
    have hrm : ∀ x : X, ∑ y : X, keys x y = 2 ^ (k - h) := fun x => by
      rw [hrow_sum x]
      exact card_win_eq_of_dep_piv (row_key_dep cr _ 0) (row_key_piv_zero cr _)
        (by omega) (by omega) tgtA
    have hcm : ∀ y : X, ∑ x : X, keys x y = 2 ^ (k - h) := fun y => by
      rw [hcol_sum y]
      exact card_win_eq_of_dep_piv (col_key_dep cc _ 0) (col_key_piv_zero cc _)
        (by omega) (by omega) tgtC
    exact ⟨fun x => by rw [hrm x]; dsimp [load]; rw [hu],
           fun y => by rw [hcm y]; dsimp [load]; rw [hu],
           Or.inl (hdeg_of_row_reg hrm)⟩
  · by_cases hr1 : r = 1
    · subst hr1
      have hk7 : h + 7 ≤ k := by simpa using hk
      have hu : u = h := rfl
      have hrm : ∀ x : X, ∑ y : X, keys x y = 2 ^ (k - h) := fun x => by
        rw [hrow_sum x]
        exact card_win_eq_of_dep_piv (row_key_dep cr _ 1)
          (row_key_piv_one cr _ (by omega)) (by omega) (by omega) tgtA
      have hcm : ∀ y : X, ∑ x : X, keys x y = 2 ^ (k - h) := fun y => by
        rw [hcol_sum y]
        exact card_win_eq_of_dep_piv (col_key_dep cc _ 1)
          (col_key_piv_one cc _ (by omega)) (by omega) (by omega) tgtC
      exact ⟨fun x => by rw [hrm x]; dsimp [load]; rw [hu],
             fun y => by rw [hcm y]; dsimp [load]; rw [hu],
             Or.inl (hdeg_of_row_reg hrm)⟩
    · by_cases hr2 : r = 2
      · subst hr2
        have hk12 : h + 12 ≤ k := by simpa using hk
        have hu_le : u ≤ h := by dsimp [u]; omega
        have hrm : ∀ x : X, ∑ y : X, keys x y = 2 ^ (k - h) := fun x => by
          rw [hrow_sum x]
          exact card_win_eq_of_dep_piv (row_key_dep cr _ 2)
            (row_key_piv_two cr _ (by omega)) (by omega) (by omega) tgtA
        have hcm : ∀ y : X, ∑ x : X, keys x y ≤ load := fun y => by
          rw [hcol_sum y]
          exact card_win_le_col2 hh hk12 cc _ tgtC
        exact ⟨fun x => by
                 rw [hrm x]
                 exact Nat.pow_le_pow_right (by omega) (by omega),
               hcm, Or.inl (hdeg_of_row_reg hrm)⟩
      · by_cases hr3 : r = 3
        · subst hr3
          have hk19 : h + 19 ≤ k := by simpa using hk
          have hu_le : u ≤ h := by dsimp [u]; omega
          have hcm : ∀ y : X, ∑ x : X, keys x y = 2 ^ (k - h) := fun y => by
            rw [hcol_sum y]
            exact card_win_eq_of_dep_piv (col_key_dep cc _ 3)
              (col_key_piv_big cc _ 2 (by omega) (by omega))
              (by omega) (by omega) tgtC
          have hrm : ∀ x : X, ∑ y : X, keys x y ≤ load := fun x => by
            rw [hrow_sum x]
            exact card_win_le_row3 hh hk19 cr _ tgtA
          exact ⟨hrm,
                 fun y => by
                   rw [hcm y]
                   exact Nat.pow_le_pow_right (by omega) (by omega),
                 Or.inr (hdeg_of_col_reg hcm)⟩
        · have hr4 : 4 ≤ r := by omega
          have hkr : h + (7 * r - 2) ≤ k := by
            rw [if_neg hr0, if_neg hr1] at hk; exact hk
          have hu : u = h := by dsimp [u]; rw [if_neg hr2, if_neg hr3]
          have hr_succ : (r - 1) + 1 = r := by omega
          have hrm : ∀ x : X, ∑ y : X, keys x y = 2 ^ (k - h) := fun x => by
            rw [hrow_sum x]
            have hdepR : Dep (fun key => rowSt cr (toW k (nameN k r h 1 rowBase x)) key r)
                (2 * (r - 1)) (5 * r - 2) :=
              dep_weaken (row_key_dep cr _ r) (2 * (r - 1)) (5 * r - 2) (by omega) (by omega)
            have hpivR : Piv (fun key => rowSt cr (toW k (nameN k r h 1 rowBase x)) key r)
                (2 * (r - 1)) := by
              rw [← hr_succ]
              exact row_key_piv_big cr _ (r - 1) (by omega) (by omega)
            exact card_win_eq_of_dep_piv hdepR hpivR (by omega) (by omega) tgtA
          have hcm : ∀ y : X, ∑ x : X, keys x y = 2 ^ (k - h) := fun y => by
            rw [hcol_sum y]
            have hdepC : Dep (fun key => colSt cc (toW k (nameN k r h 2 colBase y)) key r)
                (3 * r + 1) (7 * r - 1) :=
              dep_weaken (col_key_dep cc _ r) (3 * r + 1) (7 * r - 1) (by omega) (by omega)
            have hpivC : Piv (fun key => colSt cc (toW k (nameN k r h 2 colBase y)) key r)
                (3 * r + 1) := by
              have h3 : 3 * ((r - 1) + 1) + 1 = 3 * r + 1 := by omega
              rw [← h3, ← hr_succ]
              exact col_key_piv_big cc _ (r - 1) (by omega) (by omega)
            exact card_win_eq_of_dep_piv hdepC hpivC (by omega) (by omega) tgtC
          exact ⟨fun x => by rw [hrm x]; dsimp [load]; rw [hu],
                 fun y => by rw [hcm y]; dsimp [load]; rw [hu],
                 Or.inl (hdeg_of_row_reg hrm)⟩

lemma main_proof (k r h : ℕ) (hh : 0 < h)
    (hk : h + (if r = 0 then 2 else if r = 1 then 7 else 7 * r - 2) ≤ k)
    (masks : ℕ → Fin (2 ^ k)) (a c : Fin (2 ^ h)) (rowBase colBase : Fin (2 ^ k))
    (w v d : ℕ) (left : Fin (2 ^ h) → Fin w → Bool) (right : Fin (2 ^ h) → Fin v → Bool)
    (C : Circuit)
    (hlen : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2)
    (hrb : ReadsBack (w + v) C)
    (hdep : (depthsOf (w + v) C.gates).getD C.output 0 ≤ d + 1) :
    let X := Fin (2 ^ h)
    let keys := fun (x y : X) => (Finset.univ.filter (fun key : Fin (2 ^ k) =>
      runN k r masks false key.val (nameN k r h 1 rowBase x) >>> (k - h) = a.val ∧
      runN k r masks true key.val (nameN k r h 2 colBase y) >>> (k - h) = c.val)).card
    let accept := fun (x y : X) => C.eval (List.ofFn (left x) ++ List.ofFn (right y))
    let H := ∑ x : X, ∑ y : X, if accept x y then keys x y else 0
    let E := (Finset.univ.filter (fun xy : X × X =>
      accept xy.1 xy.2 = true ∧ keys xy.1 xy.2 = 0)).card
    let u := if r = 2 then 4 * (h / 15) + min 4 (h % 15)
      else if r = 3 then 2 * (h / 13) + min 2 (h % 13) else h
    let load := 2 ^ (k - u)
    let m := (H + load - 1) / load
    let t := C.gates.countP nlGate
    let p := 2 + (Finset.range (2 ^ d)).sum (fun j => Nat.choose (2 * t) (j + 1)) +
      (Finset.range (2 ^ d - 1)).sum (fun j => Nat.choose (2 * t) (j + 1))
    let z := m / p
    let rem := m % p
    let b := if r = 0 then 2 else if r = 1 then 7 else 7 * r - 2
    let degree := min (2 ^ h) (2 ^ (if r = 2 then 11 else b))
    (p - rem) * z ^ 2 + rem * (z + 1) ^ 2 ≤ E + m * degree := by
  intro X keys accept H E u load m t p z rem b degree
  by_cases hm0 : m = 0
  · have hz0 : z = 0 := by dsimp [z]; rw [hm0]; simp
    have hrem0 : rem = 0 := by dsimp [rem]; rw [hm0]; simp
    rw [hz0, hrem0]
    simp
  · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
    have hp_pos : 0 < p := by dsimp [p]; omega
    obtain ⟨hrow, hcol, hdeg⟩ := cipher_bounds k r h hh hk masks a c rowBase colBase
    obtain ⟨f, g, hf_inj, hg_inj, hmatch⟩ :=
      extract_matching load (Nat.two_pow_pos _) keys accept hrow hcol
    let G : Fin m → Fin m → Bool := fun i j => accept (f i) (g j)
    have hdiag : ∀ i : Fin m, G i i = true := fun i => (hmatch i).1
    let i0 : Fin m := ⟨0, hm_pos⟩
    have hrk : (Matrix.of fun i j => b2z (G i j)).rank ≤ p :=
      separate_encoding_rank_bound (fun i => left (f i)) (fun j => right (g j)) i0 i0 C hlen hrb hdep
    have hbal := balanced_support_bound hp_pos G hdiag hrk
    have hones_le : (Finset.univ.filter fun ij : Fin m × Fin m => G ij.1 ij.2 = true).card ≤
        E + m * degree := by
      let S := Finset.univ.filter fun ij : Fin m × Fin m => G ij.1 ij.2 = true
      let S0 := S.filter fun ij => keys (f ij.1) (g ij.2) = 0
      let S1 := S.filter fun ij => 0 < keys (f ij.1) (g ij.2)
      have hpart : S.card = S0.card + S1.card := by
        have huS : S0 ∪ S1 = S := by
          ext ij
          simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h
            by_cases hk0 : keys (f ij.1) (g ij.2) = 0
            · exact Or.inl ⟨h, hk0⟩
            · exact Or.inr ⟨h, Nat.pos_of_ne_zero hk0⟩
        have hdS : Disjoint S0 S1 :=
          Finset.disjoint_left.mpr fun ij h0 h1 => by
            have := (Finset.mem_filter.mp h0).2
            have := (Finset.mem_filter.mp h1).2
            omega
        rw [← huS, Finset.card_union_of_disjoint hdS]
      have hS0_le : S0.card ≤ E := by
        refine Finset.card_le_card_of_injOn (fun ij => (f ij.1, g ij.2)) ?_ ?_
        · intro ij hij
          rcases Finset.mem_filter.mp hij with ⟨hS, hk0⟩
          have hG := (Finset.mem_filter.mp hS).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG, hk0⟩
        · intro ij1 _ ij2 _ heq
          exact Prod.ext (hf_inj (congrArg Prod.fst heq)) (hg_inj (congrArg Prod.snd heq))
      have hS1_le : S1.card ≤ m * degree := by
        rcases hdeg with hdegR | hdegC
        · calc S1.card
              ≤ (Finset.univ.filter fun ij : Fin m × Fin m => 0 < keys (f ij.1) (g ij.2)).card :=
                Finset.card_le_card fun ij hij =>
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2⟩
            _ = ∑ i : Fin m, (Finset.univ.filter fun j : Fin m => 0 < keys (f i) (g j)).card := by
                rw [Finset.card_filter, Fintype.sum_prod_type]
                exact Finset.sum_congr rfl fun i _ => (Finset.card_filter _ _).symm
            _ ≤ ∑ _i : Fin m, degree := Finset.sum_le_sum fun i _ => by
                calc (Finset.univ.filter fun j : Fin m => 0 < keys (f i) (g j)).card
                    ≤ (Finset.univ.filter fun y : X => 0 < keys (f i) y).card :=
                      Finset.card_le_card_of_injOn g
                        (fun j hj => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩)
                        (fun j1 _ j2 _ h => hg_inj h)
                  _ ≤ degree := hdegR (f i)
            _ = m * degree := by simp
        · calc S1.card
              ≤ (Finset.univ.filter fun ij : Fin m × Fin m => 0 < keys (f ij.1) (g ij.2)).card :=
                Finset.card_le_card fun ij hij =>
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hij).2⟩
            _ = ∑ j : Fin m, (Finset.univ.filter fun i : Fin m => 0 < keys (f i) (g j)).card := by
                rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
                exact Finset.sum_congr rfl fun j _ => (Finset.card_filter _ _).symm
            _ ≤ ∑ _j : Fin m, degree := Finset.sum_le_sum fun j _ => by
                calc (Finset.univ.filter fun i : Fin m => 0 < keys (f i) (g j)).card
                    ≤ (Finset.univ.filter fun x : X => 0 < keys x (g j)).card :=
                      Finset.card_le_card_of_injOn f
                        (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩)
                        (fun i1 _ i2 _ h => hf_inj h)
                  _ ≤ degree := hdegC (g j)
            _ = m * degree := by simp
      change S.card ≤ E + m * degree
      omega
    exact le_trans hbal hones_le

end MainAssembly

end PEqualNP.Outside.L_meta_32021

theorem PEqualNP.Outside.L_meta_32021 : ∀ k r h : ℕ, 0 < h →
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
  let u := if r = 2 then 4*(h/15) + min 4 (h % 15)
    else if r = 3 then 2*(h/13) + min 2 (h % 13) else h
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
  ∀ (masks : ℕ → Fin (2^k)) (a c : Fin (2^h)) (rowBase colBase : Fin (2^k)),
    let X := Fin (2^h)
    let keys := fun (x y : X) => (Finset.univ.filter (fun key : Fin (2^k) =>
      run masks false key.val (name 1 rowBase x) >>> (k-h) = a.val ∧
      run masks true key.val (name 2 colBase y) >>> (k-h) = c.val)).card
    ∀ (w v d : ℕ) (left : X → Fin w → Bool) (right : X → Fin v → Bool)
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2) →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (w+v) C →
      ((C.gates.foldl (fun (ds : List ℕ) gate =>
        ds ++ [(gate.inputs.map (fun j => ds.getD j 0)).foldr max 0 + (nonlinear gate).toNat])
        (List.replicate (w+v) 0)).getD C.output 0) ≤ d+1 →
      let accept := fun (x y : X) => C.eval (List.ofFn (left x) ++ List.ofFn (right y))
      let H := ∑ x : X, ∑ y : X, if accept x y then keys x y else 0
      let E := (Finset.univ.filter (fun xy : X × X =>
        accept xy.1 xy.2 = true ∧ keys xy.1 xy.2 = 0)).card
      let load := 2^(k-u)
      let m := (H+load-1)/load
      let t := C.gates.countP nonlinear
      let p := 2 + (Finset.range (2^d)).sum (fun j => Nat.choose (2*t) (j+1)) +
        (Finset.range (2^d-1)).sum (fun j => Nat.choose (2*t) (j+1))
      let z := m/p
      let rem := m % p
      let degree := min (2^h) (2^(if r = 2 then 11 else b))
      (p-rem)*z^2 + rem*(z+1)^2 ≤ E + m*degree := by
  intro k r h hh b hk rot chi run name u nonlinear masks a c rowBase colBase X keys
    w v d left right C hlen hrb hdep
  exact PEqualNP.Outside.L_meta_32021.main_proof k r h hh hk masks a c rowBase colBase
    w v d left right C hlen hrb hdep
