import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25838_aux

-- Signature window and lift helpers adapted from commit 74a5059cc09594a6916f6f4f83652aa8b2fc359f,
-- lean/PEqualNP/Outside/L_meta_25837.lean.
namespace Signature

abbrev F := ZMod 2

def turn {k : ℕ} (dist : ℕ) (word : ZMod k → F) (site : ZMod k) : F :=
  word (site - (dist : ZMod k))

def mix {k : ℕ} (dist : ℕ) (word : ZMod k → F) (site : ZMod k) : F :=
  word (site - (dist : ZMod k)) + word site + word (site + (dist : ZMod k))

def chi {k : ℕ} (word : ZMod k → F) (site : ZMod k) : F :=
  word site + (1 + word (site + 1)) * word (site + 2)

-- Basic ZMod 2 helpers
lemma z2_add_self (a : F) : a + a = 0 := by revert a; decide
lemma z2_eq_iff (a b : F) : a = b ↔ a + b = 0 := by revert a b; decide
lemma z2_add_cancel (a b : F) : a + b + b = a := by revert a b; decide
lemma z2_add_cancel_left (a b : F) : a + (a + b) = b := by revert a b; decide

-- Basic ZMod k cast arithmetic helpers
lemma natCast_sub_of_le {k : ℕ} [NeZero k] {a b : ℕ} (hab : b ≤ a) :
    ((a : ℕ) : ZMod k) - ((b : ℕ) : ZMod k) = ((a - b : ℕ) : ZMod k) := by
  symm
  apply eq_sub_of_add_eq
  rw [← Nat.cast_add, Nat.sub_add_cancel hab]

lemma natCast_sub_wrap {k : ℕ} [NeZero k] {a b : ℕ} (hba : b ≤ k + a) :
    ((a : ℕ) : ZMod k) - ((b : ℕ) : ZMod k) = ((k + a - b : ℕ) : ZMod k) := by
  symm
  apply eq_sub_of_add_eq
  rw [← Nat.cast_add, Nat.sub_add_cancel hba, Nat.cast_add, ZMod.natCast_self, zero_add]

lemma natCast_eq_iff_lt {k : ℕ} [NeZero k] {a b : ℕ} (ha : a < k) (hb : b < k) :
    ((a : ℕ) : ZMod k) = ((b : ℕ) : ZMod k) ↔ a = b := by
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] at hv
  · rintro rfl; rfl

lemma val_sub_nat {k : ℕ} [NeZero k] (s : ZMod k) (m : ℕ) (hm : m ≤ s.val) :
    (s - ((m : ℕ) : ZMod k)).val = s.val - m := by
  have hk : s.val < k := ZMod.val_lt s
  conv_lhs => rw [← ZMod.natCast_zmod_val s]
  rw [natCast_sub_of_le hm, ZMod.val_natCast_of_lt (by omega)]

lemma val_sub_nat_wrap {k : ℕ} [NeZero k] (s : ZMod k) (m : ℕ) (h1 : s.val < m) (h2 : m ≤ k + s.val) :
    (s - ((m : ℕ) : ZMod k)).val = k + s.val - m := by
  conv_lhs => rw [← ZMod.natCast_zmod_val s]
  rw [natCast_sub_wrap h2, ZMod.val_natCast_of_lt (by omega)]

lemma val_of_sub_four {k : ℕ} [NeZero k] {s : ZMod k} (hs : 4 ≤ s.val) :
    (s - ((4 : ℕ) : ZMod k)).val = s.val - 4 :=
  val_sub_nat s 4 hs

lemma val_one_zmod {k : ℕ} [NeZero k] (hk2 : 2 ≤ k) : (1 : ZMod k).val = 1 := by
  rw [← Nat.cast_one, ZMod.val_natCast_of_lt (by omega)]

-- Linearity of turn and mix
lemma turn_add {k : ℕ} (d : ℕ) (u v : ZMod k → F) :
    turn d (u + v) = turn d u + turn d v := by
  funext s; rfl

lemma mix_add {k : ℕ} (d : ℕ) (u v : ZMod k → F) :
    mix d (u + v) = mix d u + mix d v := by
  funext s; simp only [mix, Pi.add_apply]; ring

-- Window S = {s : ZMod k | lo ≤ s.val ∨ s = 0 ∨ s = 1}
def inWin {k : ℕ} (lo : ℕ) (s : ZMod k) : Prop :=
  lo ≤ s.val ∨ s = 0 ∨ s = 1

lemma succ_inWin {k : ℕ} [NeZero k] {lo : ℕ} (hlo : 2 ≤ lo) {s : ZMod k} (hs : lo ≤ s.val) :
    inWin lo (s + 1) := by
  have hk : s.val < k := ZMod.val_lt s
  by_cases hlast : s.val + 1 = k
  · right; left
    have h1 : s + 1 = ((s.val + 1 : ℕ) : ZMod k) := by rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [h1, hlast, ZMod.natCast_self]
  · left
    have h1 : s + 1 = ((s.val + 1 : ℕ) : ZMod k) := by rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
    rw [h1, ZMod.val_natCast_of_lt (by omega)]; omega

lemma succ2_inWin {k : ℕ} [NeZero k] {lo : ℕ} (hlo : 2 ≤ lo) {s : ZMod k} (hs : lo ≤ s.val) :
    inWin lo (s + 2) := by
  have hk : s.val < k := ZMod.val_lt s
  have h1 : s + 2 = ((s.val + 2 : ℕ) : ZMod k) := by rw [Nat.cast_add, ZMod.natCast_zmod_val]; rfl
  by_cases h1k : s.val + 1 = k
  · right; right
    rw [h1, show s.val + 2 = k + 1 by omega, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
  · by_cases h2k : s.val + 2 = k
    · right; left
      rw [h1, h2k, ZMod.natCast_self]
    · left
      rw [h1, ZMod.val_natCast_of_lt (by omega)]; omega

lemma chi_congr_win {k : ℕ} [NeZero k] {lo : ℕ} (hlo : 2 ≤ lo) {X Y : ZMod k → F}
    (hXY : ∀ t, inWin lo t → X t = Y t) {s : ZMod k} (hs : lo ≤ s.val) :
    chi X s = chi Y s := by
  unfold chi
  rw [hXY s (Or.inl hs), hXY (s + 1) (succ_inWin hlo hs), hXY (s + 2) (succ2_inWin hlo hs)]

-- Surjectivity of mix 1 on inWin lo (for lo = k - h, 5 <= h, h + 7 <= k)
def rec1 {k : ℕ} (X : ZMod k → F) : ℕ → F
  | 0 => 0
  | 1 => 0
  | n + 2 => X ((k + 1 - n : ℕ) : ZMod k) + rec1 X (n + 1) + rec1 X n

lemma surj_mix1 {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k) (X : ZMod k → F) :
    ∃ u : ZMod k → F, ∀ s : ZMod k, inWin (k - h) s → mix 1 u s = X s := by
  set lo := k - h
  have hlo : 7 ≤ lo := by omega
  let u : ZMod k → F := fun s =>
    if s.val = 0 then rec1 X 2
    else if lo - 1 ≤ s.val then rec1 X (k + 2 - s.val)
    else 0
  have hu : ∀ t : ℕ, t ≤ h + 3 → u ((k + 2 - t : ℕ) : ZMod k) = rec1 X t := by
    intro t ht
    match t with
    | 0 =>
      have hval : ((k + 2 - 0 : ℕ) : ZMod k).val = 2 := by
        rw [Nat.sub_zero, Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ZMod.val_natCast_of_lt (by omega)
      simp only [u, hval, if_neg (by omega : ¬(2 = 0)), if_neg (by omega : ¬(lo - 1 ≤ 2))]; rfl
    | 1 =>
      have hval : ((k + 2 - 1 : ℕ) : ZMod k).val = 1 := by
        rw [show k + 2 - 1 = k + 1 by omega, Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ZMod.val_natCast_of_lt (by omega)
      simp only [u, hval, if_neg (by omega : ¬(1 = 0)), if_neg (by omega : ¬(lo - 1 ≤ 1))]; rfl
    | 2 =>
      have hval : ((k + 2 - 2 : ℕ) : ZMod k).val = 0 := by
        rw [show k + 2 - 2 = k by omega, ZMod.natCast_self, ZMod.val_zero]
      simp only [u, hval, ↓reduceIte]
    | t + 3 =>
      have hlt : k + 2 - (t + 3) < k := by omega
      have hval : ((k + 2 - (t + 3) : ℕ) : ZMod k).val = k + 2 - (t + 3) :=
        ZMod.val_natCast_of_lt hlt
      simp only [u, hval]
      have hne0 : k + 2 - (t + 3) ≠ 0 := by omega
      have hge : lo - 1 ≤ k + 2 - (t + 3) := by omega
      rw [if_neg hne0, if_pos hge]
      congr 1; omega
  refine ⟨u, fun s hs => ?_⟩
  have hstep : ∀ n : ℕ, n ≤ h + 1 → mix 1 u ((k + 1 - n : ℕ) : ZMod k) = X ((k + 1 - n : ℕ) : ZMod k) := by
    intro n hn
    unfold mix
    have hm1 : ((k + 1 - n : ℕ) : ZMod k) - ((1 : ℕ) : ZMod k) = ((k + 2 - (n + 2) : ℕ) : ZMod k) := by
      rw [natCast_sub_of_le (by omega)]; congr 1; omega
    have hp0 : ((k + 1 - n : ℕ) : ZMod k) = ((k + 2 - (n + 1) : ℕ) : ZMod k) := by congr 1; omega
    have hp1 : ((k + 1 - n : ℕ) : ZMod k) + ((1 : ℕ) : ZMod k) = ((k + 2 - n : ℕ) : ZMod k) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [hm1, hp1, hp0, hu (n + 2) (by omega), hu (n + 1) (by omega), hu n (by omega)]
    rw [← hp0]
    simp only [rec1]
    have hcan : ∀ p q r : F, p + q + r + q + r = p := by decide
    exact hcan _ _ _
  rcases hs with hge | rfl | rfl
  · have hlt : s.val < k := ZMod.val_lt s
    have hseq : s = ((k + 1 - (k + 1 - s.val) : ℕ) : ZMod k) := by
      rw [show k + 1 - (k + 1 - s.val) = s.val by omega, ZMod.natCast_zmod_val]
    rw [hseq]; exact hstep (k + 1 - s.val) (by omega)
  · have h0 : (0 : ZMod k) = ((k + 1 - 1 : ℕ) : ZMod k) := by
      rw [show k + 1 - 1 = k by omega, ZMod.natCast_self]
    rw [h0]; exact hstep 1 (by omega)
  · have h1 : (1 : ZMod k) = ((k + 1 - 0 : ℕ) : ZMod k) := by
      rw [Nat.sub_zero, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rw [h1]; exact hstep 0 (by omega)

-- Surjectivity of mix 2 on inWin lo
def rec2 {k : ℕ} (Y : ZMod k → F) : ℕ → F
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | n + 4 => Y ((k + 1 - n : ℕ) : ZMod k) + rec2 Y (n + 2) + rec2 Y n

lemma surj_mix2 {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k) (Y : ZMod k → F) :
    ∃ v : ZMod k → F, ∀ s : ZMod k, inWin (k - h) s → mix 2 v s = Y s := by
  set lo := k - h
  have hlo : 7 ≤ lo := by omega
  let v : ZMod k → F := fun s =>
    if lo - 2 ≤ s.val then rec2 Y (k + 3 - s.val) else 0
  have hv : ∀ t : ℕ, t ≤ h + 5 → v ((k + 3 - t : ℕ) : ZMod k) = rec2 Y t := by
    intro t ht
    match t with
    | 0 =>
      have hval : ((k + 3 - 0 : ℕ) : ZMod k).val = 3 := by
        rw [Nat.sub_zero, Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ZMod.val_natCast_of_lt (by omega)
      simp only [v, hval]; split_ifs <;> try omega
      rfl
    | 1 =>
      have hval : ((k + 3 - 1 : ℕ) : ZMod k).val = 2 := by
        rw [show k + 3 - 1 = k + 2 by omega, Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ZMod.val_natCast_of_lt (by omega)
      simp only [v, hval]; split_ifs <;> try omega
      rfl
    | 2 =>
      have hval : ((k + 3 - 2 : ℕ) : ZMod k).val = 1 := by
        rw [show k + 3 - 2 = k + 1 by omega, Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ZMod.val_natCast_of_lt (by omega)
      simp only [v, hval]; split_ifs <;> try omega
      rfl
    | 3 =>
      have hval : ((k + 3 - 3 : ℕ) : ZMod k).val = 0 := by
        rw [show k + 3 - 3 = k by omega, ZMod.natCast_self, ZMod.val_zero]
      simp only [v, hval]; split_ifs <;> try omega
      rfl
    | t + 4 =>
      have hlt : k + 3 - (t + 4) < k := by omega
      have hval : ((k + 3 - (t + 4) : ℕ) : ZMod k).val = k + 3 - (t + 4) :=
        ZMod.val_natCast_of_lt hlt
      simp only [v, hval]
      have hge : lo - 2 ≤ k + 3 - (t + 4) := by omega
      rw [if_pos hge]
      congr 1; omega
  refine ⟨v, fun s hs => ?_⟩
  have hstep : ∀ n : ℕ, n ≤ h + 1 → mix 2 v ((k + 1 - n : ℕ) : ZMod k) = Y ((k + 1 - n : ℕ) : ZMod k) := by
    intro n hn
    unfold mix
    have hm2 : ((k + 1 - n : ℕ) : ZMod k) - ((2 : ℕ) : ZMod k) = ((k + 3 - (n + 4) : ℕ) : ZMod k) := by
      rw [natCast_sub_of_le (by omega)]; congr 1; omega
    have hp0 : ((k + 1 - n : ℕ) : ZMod k) = ((k + 3 - (n + 2) : ℕ) : ZMod k) := by congr 1; omega
    have hp2 : ((k + 1 - n : ℕ) : ZMod k) + ((2 : ℕ) : ZMod k) = ((k + 3 - n : ℕ) : ZMod k) := by
      rw [← Nat.cast_add]; congr 1; omega
    rw [hm2, hp2, hp0, hv (n + 4) (by omega), hv (n + 2) (by omega), hv n (by omega)]
    rw [← hp0]
    simp only [rec2]
    have hcan : ∀ p q r : F, p + q + r + q + r = p := by decide
    exact hcan _ _ _
  rcases hs with hge | rfl | rfl
  · have hlt : s.val < k := ZMod.val_lt s
    have hseq : s = ((k + 1 - (k + 1 - s.val) : ℕ) : ZMod k) := by
      rw [show k + 1 - (k + 1 - s.val) = s.val by omega, ZMod.natCast_zmod_val]
    rw [hseq]; exact hstep (k + 1 - s.val) (by omega)
  · have h0 : (0 : ZMod k) = ((k + 1 - 1 : ℕ) : ZMod k) := by
      rw [show k + 1 - 1 = k by omega, ZMod.natCast_self]
    rw [h0]; exact hstep 1 (by omega)
  · have h1 : (1 : ZMod k) = ((k + 1 - 0 : ℕ) : ZMod k) := by
      rw [Nat.sub_zero, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    rw [h1]; exact hstep 0 (by omega)

-- Chi inversion on [lo .. k-1]
def chiRec {k : ℕ} (rhs : ZMod k → F) : ℕ → F
  | 0 => 0
  | 1 => 0
  | n + 2 => rhs ((k - 1 - n : ℕ) : ZMod k) + (1 + chiRec rhs (n + 1)) * chiRec rhs n

lemma natCast_add_one {k : ℕ} (a : ℕ) : ((a : ℕ) : ZMod k) + 1 = ((a + 1 : ℕ) : ZMod k) := by
  rw [Nat.cast_add, Nat.cast_one]

lemma natCast_add_two {k : ℕ} (a : ℕ) : ((a : ℕ) : ZMod k) + 2 = ((a + 2 : ℕ) : ZMod k) := by
  rw [Nat.cast_add, Nat.cast_ofNat]

lemma exists_chi_eq {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k) (rhs : ZMod k → F) :
    ∃ X : ZMod k → F, ∀ s : ZMod k, k - h ≤ s.val → chi X s = rhs s := by
  set lo := k - h
  let X : ZMod k → F := fun s =>
    if lo ≤ s.val then chiRec rhs (k + 1 - s.val) else 0
  have hX : ∀ t : ℕ, t ≤ h + 1 → X ((k + 1 - t : ℕ) : ZMod k) = chiRec rhs t := by
    intro t ht
    match t with
    | 0 =>
      have hval : ((k + 1 - 0 : ℕ) : ZMod k).val = 1 := by
        rw [Nat.sub_zero, Nat.cast_add, ZMod.natCast_self, zero_add]
        exact ZMod.val_natCast_of_lt (by omega)
      simp only [X, hval]; split_ifs <;> try omega
      rfl
    | 1 =>
      have hval : ((k + 1 - 1 : ℕ) : ZMod k).val = 0 := by
        rw [show k + 1 - 1 = k by omega, ZMod.natCast_self, ZMod.val_zero]
      simp only [X, hval]; split_ifs <;> try omega
      rfl
    | t + 2 =>
      have hlt : k + 1 - (t + 2) < k := by omega
      have hval : ((k + 1 - (t + 2) : ℕ) : ZMod k).val = k + 1 - (t + 2) :=
        ZMod.val_natCast_of_lt hlt
      simp only [X, hval]
      have hge : lo ≤ k + 1 - (t + 2) := by omega
      rw [if_pos hge]
      congr 1; omega
  refine ⟨X, fun s hs => ?_⟩
  have hlt : s.val < k := ZMod.val_lt s
  set n := k - 1 - s.val
  have hn : n < h := by omega
  have hs0 : s = ((k - 1 - n : ℕ) : ZMod k) := by
    rw [show k - 1 - n = s.val by omega, ZMod.natCast_zmod_val]
  have hp0 : s = ((k + 1 - (n + 2) : ℕ) : ZMod k) := by rw [hs0]; congr 1; omega
  have hp1 : s + 1 = ((k + 1 - (n + 1) : ℕ) : ZMod k) := by
    rw [hp0, natCast_add_one]; congr 1; omega
  have hp2 : s + 2 = ((k + 1 - n : ℕ) : ZMod k) := by
    rw [hp0, natCast_add_two]; congr 1; omega
  unfold chi
  rw [hp1, hp2, hp0, hX (n + 2) (by omega), hX (n + 1) (by omega), hX n (by omega)]
  rw [← hp0, hs0]
  simp only [chiRec]
  rw [z2_add_cancel]

-- Differential of chi: if chi (X + Δ) s + chi X s = c for all X, then Δ (s+1) = 0, Δ (s+2) = 0, Δ s = c
lemma chi_diff_const {k : ℕ} [NeZero k] (hk3 : 3 ≤ k) (Δ : ZMod k → F) (s : ZMod k) (c : F)
    (hconst : ∀ X : ZMod k → F, chi (X + Δ) s + chi X s = c) :
    Δ (s + 1) = 0 ∧ Δ (s + 2) = 0 ∧ Δ s = c := by
  have hdiff : ∀ X : ZMod k → F,
      Δ s + Δ (s + 1) * X (s + 2) + Δ (s + 2) * (1 + X (s + 1)) + Δ (s + 1) * Δ (s + 2) = c := by
    intro X
    have h := hconst X
    simp only [chi, Pi.add_apply] at h
    -- Expand in ZMod 2
    have hform : ∀ a b e da db de : F,
        a + da + (1 + (b + db)) * (e + de) + (a + (1 + b) * e) =
          da + db * e + de * (1 + b) + db * de := by decide
    rw [← hform]
    exact h
  have h12 : s + 1 ≠ s + 2 := by
    intro h
    have h10 : ((1 : ℕ) : ZMod k) = ((2 : ℕ) : ZMod k) := by
      simpa using add_left_cancel h
    rw [natCast_eq_iff_lt (by omega) (by omega)] at h10; omega
  have h0 := hdiff 0
  simp only [Pi.zero_apply, mul_zero, add_zero, mul_one] at h0
  have hX2 := hdiff (fun t => if t = s + 2 then 1 else 0)
  simp only [↓reduceIte, if_neg h12, add_zero, mul_one] at hX2
  have hX1 := hdiff (fun t => if t = s + 1 then 1 else 0)
  simp only [↓reduceIte, if_neg h12.symm, mul_zero, add_zero] at hX1
  have hd1 : Δ (s + 1) = 0 := by
    have heq := h0.trans hX2.symm
    have : ∀ a b e : F, a + e + b * e = a + b + e + b * e → b = 0 := by decide
    exact this _ _ _ heq
  have hd2 : Δ (s + 2) = 0 := by
    have heq := h0.trans hX1.symm
    have : ∀ a b e : F, a + e + b * e = a + e * (1 + 1) + b * e → e = 0 := by decide
    exact this _ _ _ heq
  have hd0 : Δ s = c := by
    rw [hd1, hd2] at h0; simpa using h0
  exact ⟨hd1, hd2, hd0⟩

lemma chi_diff_of_zero {k : ℕ} (X Δ : ZMod k → F) (s : ZMod k)
    (h1 : Δ (s + 1) = 0) (h2 : Δ (s + 2) = 0) :
    chi (X + Δ) s = chi X s + Δ s := by
  simp only [chi, Pi.add_apply, h1, h2, add_zero]
  ring

-- Signature definition matching the theorem statement
def signature {k : ℕ} (h : ℕ) (u v : ZMod k → F) :
    (Fin h → F) × (Fin (h - 1) → F) × F :=
  let lo := k - h
  let x := mix 1 u
  let y := mix 2 v
  ((fun j : Fin h => x ((lo + j.val : ℕ) : ZMod k)),
   (fun j : Fin (h - 1) => if j.val = 0 then y 0 else y ((lo + 1 + j.val : ℕ) : ZMod k)),
   x 0 + y 1)


-- Exact characterization of `lifts a b d`
def goodP {k : ℕ} (h : ℕ) (rowConst colConst u v key : ZMod k → F) : Prop :=
  let lo := k - h
  let row := chi (mix 1 (turn 1 key + u)) + key + rowConst
  let col := chi (mix 2 (turn 3 key + v)) + turn 4 key + colConst
  ∀ site : ZMod k, lo ≤ site.val → row site = 0 ∧ col site = 0

def liftsP {k : ℕ} (h : ℕ) (rowConst colConst a b d : ZMod k → F) : Prop :=
  ∀ u v key : ZMod k → F, goodP h rowConst colConst u v key ↔
    goodP h rowConst colConst (u + a) (v + b) (key + d)

lemma liftsP_iff_deltas {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k)
    (rowConst colConst a b d : ZMod k → F) :
    liftsP h rowConst colConst a b d ↔
      (∀ s : ZMod k, k - h ≤ s.val →
        mix 1 (turn 1 d + a) (s + 1) = 0 ∧
        mix 1 (turn 1 d + a) (s + 2) = 0 ∧
        mix 1 (turn 1 d + a) s = d s ∧
        mix 2 (turn 3 d + b) (s + 1) = 0 ∧
        mix 2 (turn 3 d + b) (s + 2) = 0 ∧
        mix 2 (turn 3 d + b) s = d (s - 4)) := by
  set lo := k - h
  set Δx := mix 1 (turn 1 d + a)
  set Δy := mix 2 (turn 3 d + b)
  constructor
  · intro hL
    have hRow : ∀ (X : ZMod k → F) (s : ZMod k), lo ≤ s.val → chi (X + Δx) s + chi X s = d s := by
      intro X s hs
      let key : ZMod k → F := fun t => if lo ≤ t.val then chi X t + rowConst t else 0
      obtain ⟨Y, hY⟩ := exists_chi_eq hh hk (fun t => key (t - 4) + colConst t)
      obtain ⟨u, hu⟩ := surj_mix1 hh hk (X + mix 1 (turn 1 key))
      obtain ⟨v, hv⟩ := surj_mix2 hh hk (Y + mix 2 (turn 3 key))
      have hXu : ∀ t, inWin lo t → mix 1 (turn 1 key + u) t = X t := by
        intro t ht
        rw [mix_add, Pi.add_apply, hu t ht, Pi.add_apply, add_comm (mix 1 (turn 1 key) t),
            z2_add_cancel]
      have hYv : ∀ t, inWin lo t → mix 2 (turn 3 key + v) t = Y t := by
        intro t ht
        rw [mix_add, Pi.add_apply, hv t ht, Pi.add_apply, add_comm (mix 2 (turn 3 key) t),
            z2_add_cancel]
      have hgood : goodP h rowConst colConst u v key := by
        intro t ht
        constructor
        · simp only [Pi.add_apply, chi_congr_win (by omega : 2 ≤ lo) hXu ht]
          have ht' : lo ≤ t.val := ht
          simp only [key, if_pos ht']
          have : ∀ p q : F, p + (p + q) + q = 0 := by decide
          exact this _ _
        · simp only [Pi.add_apply, turn, chi_congr_win (by omega : 2 ≤ lo) hYv ht, hY t ht]
          have : ∀ p q : F, p + q + p + q = 0 := by decide
          exact this _ _
      have hgood' := (hL u v key).mp hgood
      have hr := (hgood' s hs).1
      have hXu' : ∀ t, inWin lo t → mix 1 (turn 1 (key + d) + (u + a)) t = (X + Δx) t := by
        intro t ht
        have heq : turn 1 (key + d) + (u + a) = (turn 1 key + u) + (turn 1 d + a) := by
          funext z; simp only [turn, Pi.add_apply]; ring
        rw [heq, mix_add, Pi.add_apply, Pi.add_apply, hXu t ht]
      simp only [Pi.add_apply, chi_congr_win (by omega : 2 ≤ lo) hXu' hs] at hr
      simp only [key, if_pos hs] at hr
      have : ∀ p q r c : F, p + (q + c + r) + c = 0 → p + q = r := by decide
      exact this _ _ _ _ hr
    have hCol : ∀ (Y : ZMod k → F) (s : ZMod k), lo ≤ s.val → chi (Y + Δy) s + chi Y s = d (s - 4) := by
      intro Y s hs
      let key : ZMod k → F := fun t =>
        if lo - 4 ≤ t.val ∧ t.val < k - 4 then chi Y (t + 4) + colConst (t + 4) else 0
      obtain ⟨X, hX⟩ := exists_chi_eq hh hk (fun t => key t + rowConst t)
      obtain ⟨u, hu⟩ := surj_mix1 hh hk (X + mix 1 (turn 1 key))
      obtain ⟨v, hv⟩ := surj_mix2 hh hk (Y + mix 2 (turn 3 key))
      have hXu : ∀ t, inWin lo t → mix 1 (turn 1 key + u) t = X t := by
        intro t ht
        rw [mix_add, Pi.add_apply, hu t ht, Pi.add_apply, add_comm (mix 1 (turn 1 key) t),
            z2_add_cancel]
      have hYv : ∀ t, inWin lo t → mix 2 (turn 3 key + v) t = Y t := by
        intro t ht
        rw [mix_add, Pi.add_apply, hv t ht, Pi.add_apply, add_comm (mix 2 (turn 3 key) t),
            z2_add_cancel]
      have hkey4 : ∀ t : ZMod k, lo ≤ t.val → key (t - ((4 : ℕ) : ZMod k)) = chi Y t + colConst t := by
        intro t ht
        have hlt : t.val < k := ZMod.val_lt t
        have hv4 : (t - ((4 : ℕ) : ZMod k)).val = t.val - 4 := val_of_sub_four (by omega)
        simp only [key, hv4, show lo - 4 ≤ t.val - 4 ∧ t.val - 4 < k - 4 by omega, and_self, ↓reduceIte]
        rw [Nat.cast_ofNat, sub_add_cancel]
      have hgood : goodP h rowConst colConst u v key := by
        intro t ht
        constructor
        · simp only [Pi.add_apply, chi_congr_win (by omega : 2 ≤ lo) hXu ht, hX t ht]
          have : ∀ p q : F, p + q + p + q = 0 := by decide
          exact this _ _
        · simp only [Pi.add_apply, turn, chi_congr_win (by omega : 2 ≤ lo) hYv ht, hkey4 t ht]
          have : ∀ p q : F, p + (p + q) + q = 0 := by decide
          exact this _ _
      have hgood' := (hL u v key).mp hgood
      have hc := (hgood' s hs).2
      have hYv' : ∀ t, inWin lo t → mix 2 (turn 3 (key + d) + (v + b)) t = (Y + Δy) t := by
        intro t ht
        have heq : turn 3 (key + d) + (v + b) = (turn 3 key + v) + (turn 3 d + b) := by
          funext z; simp only [turn, Pi.add_apply]; ring
        rw [heq, mix_add, Pi.add_apply, Pi.add_apply, hYv t ht]
      simp only [Pi.add_apply, turn, chi_congr_win (by omega : 2 ≤ lo) hYv' hs] at hc
      rw [hkey4 s hs] at hc
      have : ∀ p q r c : F, p + (q + c + r) + c = 0 → p + q = r := by decide
      exact this _ _ _ _ hc
    intro s hs
    obtain ⟨h1, h2, h3⟩ := chi_diff_const (by omega) Δx s (d s) (fun X => hRow X s hs)
    obtain ⟨h4, h5, h6⟩ := chi_diff_const (by omega) Δy s (d (s - 4)) (fun Y => hCol Y s hs)
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · intro hcond u v key
    have heq : ∀ s : ZMod k, lo ≤ s.val →
        (chi (mix 1 (turn 1 (key + d) + (u + a))) s + (key + d) s + rowConst s =
         chi (mix 1 (turn 1 key + u)) s + key s + rowConst s) ∧
        (chi (mix 2 (turn 3 (key + d) + (v + b))) s + turn 4 (key + d) s + colConst s =
         chi (mix 2 (turn 3 key + v)) s + turn 4 key s + colConst s) := by
      intro s hs
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcond s hs
      have hmx : mix 1 (turn 1 (key + d) + (u + a)) = mix 1 (turn 1 key + u) + Δx := by
        rw [← mix_add]; congr 1; funext z; simp only [turn, Pi.add_apply]; ring
      have hmy : mix 2 (turn 3 (key + d) + (v + b)) = mix 2 (turn 3 key + v) + Δy := by
        rw [← mix_add]; congr 1; funext z; simp only [turn, Pi.add_apply]; ring
      constructor
      · rw [hmx, chi_diff_of_zero _ _ s h1 h2, h3]
        simp only [Pi.add_apply]
        have : ∀ p q r c : F, p + r + (q + r) + c = p + q + c := by decide
        exact this _ _ _ _
      · rw [hmy, chi_diff_of_zero _ _ s h4 h5, h6]
        simp only [turn, Pi.add_apply]
        have : ∀ p q r c : F, p + r + (q + r) + c = p + q + c := by decide
        exact this _ _ _ _
    constructor <;> intro hg s hs
    · obtain ⟨h1, h2⟩ := hg s hs
      obtain ⟨e1, e2⟩ := heq s hs
      simp only [Pi.add_apply] at e1 e2 ⊢
      exact ⟨e1.trans h1, e2.trans h2⟩
    · obtain ⟨h1, h2⟩ := hg s hs
      obtain ⟨e1, e2⟩ := heq s hs
      simp only [Pi.add_apply] at e1 e2 ⊢
      exact ⟨e1.symm.trans h1, e2.symm.trans h2⟩

-- Explicit coordinate-wise equivalence for liftsP h rowConst colConst a b d
lemma liftsP_iff_coords {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k)
    (rowConst colConst a b d : ZMod k → F) :
    liftsP h rowConst colConst a b d ↔
      (signature h a b = (0, 0, 0) ∧
       (∀ t : ZMod k, k - h - 3 ≤ t.val → d t = 0) ∧
       d 0 = mix 1 a 0 ∧
       d 1 = mix 1 a 0 + mix 1 a 1 ∧
       d ((k - h - 4 : ℕ) : ZMod k) = mix 2 b ((k - h + 1 : ℕ) : ZMod k) ∧
       d ((k - h - 5 : ℕ) : ZMod k) = mix 2 b ((k - h : ℕ) : ZMod k) + mix 2 b ((k - h + 1 : ℕ) : ZMod k)) := by
  set lo := k - h
  have hlo : 7 ≤ lo := by omega
  rw [liftsP_iff_deltas hh hk]
  -- Helper: evaluate mix 1 (turn 1 d) and mix 2 (turn 3 d) when d vanishes on [lo-3 .. k-1]
  have eval_m1 : ∀ (hd0 : ∀ t : ZMod k, lo - 3 ≤ t.val → d t = 0),
      (∀ t : ZMod k, lo ≤ t.val → mix 1 (turn 1 d) t = 0) ∧
      mix 1 (turn 1 d) 0 = d 0 ∧
      mix 1 (turn 1 d) 1 = d 0 + d 1 := by
    intro hd0
    have hm : ∀ s : ZMod k, mix 1 (turn 1 d) s = d (s - ((2 : ℕ) : ZMod k)) + d (s - ((1 : ℕ) : ZMod k)) + d s := by
      intro s; simp only [mix, turn, Nat.cast_one, Nat.cast_ofNat]
      have h1 : s - 1 - 1 = s - 2 := by ring
      have h2 : s + 1 - 1 = s := by ring
      rw [h1, h2]
    refine ⟨fun t ht => ?_, ?_, ?_⟩
    · rw [hm]
      have htm2 := val_sub_nat t 2 (by omega)
      have htm1 := val_sub_nat t 1 (by omega)
      rw [hd0 _ (by omega), hd0 _ (by omega), hd0 t (by omega)]; decide
    · rw [hm]
      have hk2 := val_sub_nat_wrap (0 : ZMod k) 2 (by rw [ZMod.val_zero]; omega) (by rw [ZMod.val_zero]; omega)
      have hk1 := val_sub_nat_wrap (0 : ZMod k) 1 (by rw [ZMod.val_zero]; omega) (by rw [ZMod.val_zero]; omega)
      rw [ZMod.val_zero] at hk2 hk1
      rw [hd0 _ (by omega), hd0 _ (by omega), zero_add, zero_add]
    · rw [hm]
      have hv1 : (1 : ZMod k).val = 1 := val_one_zmod (by omega)
      have hk1 := val_sub_nat_wrap (1 : ZMod k) 2 (by omega) (by omega)
      rw [hd0 _ (by omega), zero_add, Nat.cast_one, sub_self]
  have eval_m2 : ∀ (hd0 : ∀ t : ZMod k, lo - 3 ≤ t.val → d t = 0),
      mix 2 (turn 3 d) ((lo : ℕ) : ZMod k) = d ((lo - 5 : ℕ) : ZMod k) ∧
      mix 2 (turn 3 d) ((lo + 1 : ℕ) : ZMod k) = d ((lo - 4 : ℕ) : ZMod k) ∧
      (∀ t : ZMod k, lo + 2 ≤ t.val → mix 2 (turn 3 d) t = 0) ∧
      mix 2 (turn 3 d) 0 = 0 ∧
      mix 2 (turn 3 d) 1 = d 0 := by
    intro hd0
    have hm : ∀ s : ZMod k, mix 2 (turn 3 d) s =
        d (s - ((5 : ℕ) : ZMod k)) + d (s - ((3 : ℕ) : ZMod k)) + d (s - ((1 : ℕ) : ZMod k)) := by
      intro s; simp only [mix, turn, Nat.cast_one, Nat.cast_ofNat]
      have h1 : s - 2 - 3 = s - 5 := by ring
      have h3 : s + 2 - 3 = s - 1 := by ring
      rw [h1, h3]
    refine ⟨?_, ?_, fun t ht => ?_, ?_, ?_⟩
    · rw [hm]
      have hlv : ((lo : ℕ) : ZMod k).val = lo := ZMod.val_natCast_of_lt (by omega)
      have h5 : ((lo : ℕ) : ZMod k) - ((5 : ℕ) : ZMod k) = ((lo - 5 : ℕ) : ZMod k) :=
        natCast_sub_of_le (by omega)
      have h3 := val_sub_nat ((lo : ℕ) : ZMod k) 3 (by omega)
      have h1 := val_sub_nat ((lo : ℕ) : ZMod k) 1 (by omega)
      rw [h5, hd0 (((lo : ℕ) : ZMod k) - ((3 : ℕ) : ZMod k)) (by omega),
          hd0 (((lo : ℕ) : ZMod k) - ((1 : ℕ) : ZMod k)) (by omega), add_zero, add_zero]
    · rw [hm]
      have hlv : ((lo + 1 : ℕ) : ZMod k).val = lo + 1 := ZMod.val_natCast_of_lt (by omega)
      have h5 : ((lo + 1 : ℕ) : ZMod k) - ((5 : ℕ) : ZMod k) = ((lo - 4 : ℕ) : ZMod k) := by
        rw [natCast_sub_of_le (by omega), show lo + 1 - 5 = lo - 4 by omega]
      have h3 := val_sub_nat ((lo + 1 : ℕ) : ZMod k) 3 (by omega)
      have h1 := val_sub_nat ((lo + 1 : ℕ) : ZMod k) 1 (by omega)
      rw [h5, hd0 (((lo + 1 : ℕ) : ZMod k) - ((3 : ℕ) : ZMod k)) (by omega),
          hd0 (((lo + 1 : ℕ) : ZMod k) - ((1 : ℕ) : ZMod k)) (by omega), add_zero, add_zero]
    · rw [hm]
      have h5 := val_sub_nat t 5 (by omega)
      have h3 := val_sub_nat t 3 (by omega)
      have h1 := val_sub_nat t 1 (by omega)
      rw [hd0 _ (by omega), hd0 _ (by omega), hd0 _ (by omega)]; decide
    · rw [hm]
      have h5 := val_sub_nat_wrap (0 : ZMod k) 5 (by rw [ZMod.val_zero]; omega) (by rw [ZMod.val_zero]; omega)
      have h3 := val_sub_nat_wrap (0 : ZMod k) 3 (by rw [ZMod.val_zero]; omega) (by rw [ZMod.val_zero]; omega)
      have h1 := val_sub_nat_wrap (0 : ZMod k) 1 (by rw [ZMod.val_zero]; omega) (by rw [ZMod.val_zero]; omega)
      rw [ZMod.val_zero] at h5 h3 h1
      rw [hd0 _ (by omega), hd0 _ (by omega), hd0 _ (by omega)]; decide
    · rw [hm]
      have hv1 : (1 : ZMod k).val = 1 := val_one_zmod (by omega)
      have h5 := val_sub_nat_wrap (1 : ZMod k) 5 (by omega) (by omega)
      have h3 := val_sub_nat_wrap (1 : ZMod k) 3 (by omega) (by omega)
      rw [hd0 _ (by omega), hd0 _ (by omega), Nat.cast_one, sub_self, zero_add, zero_add]
  -- Now prove both directions
  constructor
  · intro hcond
    -- First deduce Δx(t)=0 and Δy(t)=0 on [lo+1..k-1] ∪ {0, 1}!
    have hΔx_zero : ∀ t : ZMod k, (lo + 1 ≤ t.val ∨ t = 0 ∨ t = 1) → mix 1 (turn 1 d + a) t = 0 := by
      intro t ht
      rcases ht with hge | rfl | rfl
      · have hlt : t.val < k := ZMod.val_lt t
        have hprev : lo ≤ (t - 1).val := by
          have hv := val_sub_nat t 1 (by omega)
          rw [Nat.cast_one] at hv; omega
        have := (hcond (t - 1) hprev).1
        rwa [sub_add_cancel] at this
      · have hprev : lo ≤ ((k - 1 : ℕ) : ZMod k).val := by
          rw [ZMod.val_natCast_of_lt (by omega)]; omega
        have := (hcond ((k - 1 : ℕ) : ZMod k) hprev).1
        have h0 : ((k - 1 : ℕ) : ZMod k) + 1 = 0 := by
          rw [natCast_add_one, show k - 1 + 1 = k by omega, ZMod.natCast_self]
        rwa [h0] at this
      · have hprev : lo ≤ ((k - 1 : ℕ) : ZMod k).val := by
          rw [ZMod.val_natCast_of_lt (by omega)]; omega
        have := (hcond ((k - 1 : ℕ) : ZMod k) hprev).2.1
        have h1 : ((k - 1 : ℕ) : ZMod k) + 2 = 1 := by
          rw [natCast_add_two, show k - 1 + 2 = k + 1 by omega, Nat.cast_add,
              ZMod.natCast_self, zero_add, Nat.cast_one]
        rwa [h1] at this
    have hΔy_zero : ∀ t : ZMod k, (lo + 1 ≤ t.val ∨ t = 0 ∨ t = 1) → mix 2 (turn 3 d + b) t = 0 := by
      intro t ht
      rcases ht with hge | rfl | rfl
      · have hlt : t.val < k := ZMod.val_lt t
        have hprev : lo ≤ (t - 1).val := by
          have hv := val_sub_nat t 1 (by omega)
          rw [Nat.cast_one] at hv; omega
        have := (hcond (t - 1) hprev).2.2.2.1
        rwa [sub_add_cancel] at this
      · have hprev : lo ≤ ((k - 1 : ℕ) : ZMod k).val := by
          rw [ZMod.val_natCast_of_lt (by omega)]; omega
        have := (hcond ((k - 1 : ℕ) : ZMod k) hprev).2.2.2.1
        have h0 : ((k - 1 : ℕ) : ZMod k) + 1 = 0 := by
          rw [natCast_add_one, show k - 1 + 1 = k by omega, ZMod.natCast_self]
        rwa [h0] at this
      · have hprev : lo ≤ ((k - 1 : ℕ) : ZMod k).val := by
          rw [ZMod.val_natCast_of_lt (by omega)]; omega
        have := (hcond ((k - 1 : ℕ) : ZMod k) hprev).2.2.2.2.1
        have h1 : ((k - 1 : ℕ) : ZMod k) + 2 = 1 := by
          rw [natCast_add_two, show k - 1 + 2 = k + 1 by omega, Nat.cast_add,
              ZMod.natCast_self, zero_add, Nat.cast_one]
        rwa [h1] at this
    -- Deduce d(t) = 0 for all t with lo - 3 ≤ t.val!
    have hd0 : ∀ t : ZMod k, lo - 3 ≤ t.val → d t = 0 := by
      intro t ht
      have hlt : t.val < k := ZMod.val_lt t
      by_cases hhi : lo + 1 ≤ t.val
      · rw [← (hcond t (by omega)).2.2.1]; exact hΔx_zero t (Or.inl hhi)
      · -- lo - 3 ≤ t.val ≤ lo, so t + 4 has val in [lo + 1 .. lo + 4] ⊆ [lo + 1 .. k - 1]!
        have hv4 : (t + 4).val = t.val + 4 := by
          have h1 : t + 4 = ((t.val + 4 : ℕ) : ZMod k) := by rw [Nat.cast_add, ZMod.natCast_zmod_val]; rfl
          rw [h1, ZMod.val_natCast_of_lt (by omega)]
        have h := (hcond (t + 4) (by omega)).2.2.2.2.2
        rw [add_sub_cancel_right] at h
        rw [← h]; exact hΔy_zero (t + 4) (Or.inl (by omega))
    -- Now use eval_m1 and eval_m2!
    obtain ⟨hm1_lo, hm1_0, hm1_1⟩ := eval_m1 hd0
    obtain ⟨hm2_lo, hm2_lo1, hm2_lo2, hm2_0, hm2_1⟩ := eval_m2 hd0
    have hΔx_lo : mix 1 (turn 1 d + a) ((lo : ℕ) : ZMod k) = 0 := by
      have hlo_val : ((lo : ℕ) : ZMod k).val = lo := ZMod.val_natCast_of_lt (by omega)
      rw [(hcond _ (by omega)).2.2.1, hd0 _ (by omega)]
    have hax : ∀ t : ZMod k, lo ≤ t.val → mix 1 a t = 0 := by
      intro t ht
      have h0 : mix 1 (turn 1 d + a) t = 0 := by
        by_cases h1 : lo + 1 ≤ t.val
        · exact hΔx_zero t (Or.inl h1)
        · have htlo : t = ((lo : ℕ) : ZMod k) := by
            rw [← ZMod.natCast_zmod_val t]; congr 1; omega
          rwa [htlo]
      rw [mix_add, Pi.add_apply, hm1_lo t ht, zero_add] at h0
      exact h0
    have hd_at_0 : d 0 = mix 1 a 0 := by
      have h0 := hΔx_zero 0 (Or.inr (Or.inl rfl))
      rw [mix_add, Pi.add_apply, hm1_0] at h0
      exact (z2_eq_iff _ _).mpr h0
    have hd_at_1 : d 1 = mix 1 a 0 + mix 1 a 1 := by
      have h1 := hΔx_zero 1 (Or.inr (Or.inr rfl))
      rw [mix_add, Pi.add_apply, hm1_1, hd_at_0] at h1
      have : ∀ x y z : F, x + z + y = 0 → z = x + y := by decide
      exact this _ _ _ h1
    have hd_at_l4 : d ((lo - 4 : ℕ) : ZMod k) = mix 2 b ((lo + 1 : ℕ) : ZMod k) := by
      have h1 := hΔy_zero ((lo + 1 : ℕ) : ZMod k) (Or.inl (by rw [ZMod.val_natCast_of_lt (by omega)]))
      rw [mix_add, Pi.add_apply, hm2_lo1] at h1
      exact (z2_eq_iff _ _).mpr h1
    have hd_at_l5 : d ((lo - 5 : ℕ) : ZMod k) = mix 2 b ((lo : ℕ) : ZMod k) + mix 2 b ((lo + 1 : ℕ) : ZMod k) := by
      have hlo_val : ((lo : ℕ) : ZMod k).val = lo := ZMod.val_natCast_of_lt (by omega)
      have h1 := (hcond ((lo : ℕ) : ZMod k) (by omega)).2.2.2.2.2
      rw [mix_add, Pi.add_apply, hm2_lo, show ((lo : ℕ) : ZMod k) - 4 = ((lo - 4 : ℕ) : ZMod k) from by rw [← Nat.cast_ofNat]; exact natCast_sub_of_le (by omega), hd_at_l4] at h1
      have : ∀ x y z : F, x + y = z → x = y + z := by decide
      exact this _ _ _ h1
    have hby0 : mix 2 b 0 = 0 := by
      have h0 := hΔy_zero 0 (Or.inr (Or.inl rfl))
      rwa [mix_add, Pi.add_apply, hm2_0, zero_add] at h0
    have hby2 : ∀ t : ZMod k, lo + 2 ≤ t.val → mix 2 b t = 0 := by
      intro t ht
      have h0 := hΔy_zero t (Or.inl (by omega))
      rwa [mix_add, Pi.add_apply, hm2_lo2 t ht, zero_add] at h0
    have hcross : mix 1 a 0 + mix 2 b 1 = 0 := by
      have h1 := hΔy_zero 1 (Or.inr (Or.inr rfl))
      rwa [mix_add, Pi.add_apply, hm2_1, hd_at_0] at h1
    refine ⟨?_, hd0, hd_at_0, hd_at_1, hd_at_l4, hd_at_l5⟩
    unfold signature
    dsimp only
    refine Prod.ext ?_ (Prod.ext ?_ hcross)
    · dsimp only; funext j
      exact hax _ (by rw [ZMod.val_natCast_of_lt (by have := j.isLt; omega)]; omega)
    · dsimp only; funext j
      by_cases hj0 : j.val = 0
      · rw [if_pos hj0]; exact hby0
      · rw [if_neg hj0]
        exact hby2 _ (by rw [ZMod.val_natCast_of_lt (by have := j.isLt; omega)]; omega)
  · rintro ⟨hsig, hd0, hd_at_0, hd_at_1, hd_at_l4, hd_at_l5⟩
    obtain ⟨hm1_lo, hm1_0, hm1_1⟩ := eval_m1 hd0
    obtain ⟨hm2_lo, hm2_lo1, hm2_lo2, hm2_0, hm2_1⟩ := eval_m2 hd0
    have hsig1 : ∀ j : Fin h, mix 1 a ((lo + j.val : ℕ) : ZMod k) = 0 := fun j =>
      congrFun (congrArg Prod.fst hsig) j
    have hsig2 : ∀ j : Fin (h - 1), (if j.val = 0 then mix 2 b 0 else mix 2 b ((lo + 1 + j.val : ℕ) : ZMod k)) = 0 :=
      fun j => congrFun (congrArg (fun p => p.2.1) hsig) j
    have hsig3 : mix 1 a 0 + mix 2 b 1 = 0 := congrArg (fun p => p.2.2) hsig
    have hax : ∀ t : ZMod k, lo ≤ t.val → mix 1 a t = 0 := by
      intro t ht
      have hlt : t.val < k := ZMod.val_lt t
      have h := hsig1 ⟨t.val - lo, by omega⟩
      have heq : ((lo + (t.val - lo) : ℕ) : ZMod k) = t := by
        rw [Nat.add_sub_of_le ht, ZMod.natCast_zmod_val]
      rwa [heq] at h
    have hby0 : mix 2 b 0 = 0 := by
      have h := hsig2 ⟨0, by omega⟩; simpa using h
    have hby2 : ∀ t : ZMod k, lo + 2 ≤ t.val → mix 2 b t = 0 := by
      intro t ht
      have hlt : t.val < k := ZMod.val_lt t
      have h := hsig2 ⟨t.val - (lo + 1), by omega⟩
      have hne : t.val - (lo + 1) ≠ 0 := by omega
      rw [if_neg hne] at h
      have heq : ((lo + 1 + (t.val - (lo + 1)) : ℕ) : ZMod k) = t := by
        rw [show lo + 1 + (t.val - (lo + 1)) = t.val by omega, ZMod.natCast_zmod_val]
      rwa [heq] at h
    have hΔx_zero : ∀ t : ZMod k, inWin lo t → mix 1 (turn 1 d + a) t = 0 := by
      intro t ht
      rw [mix_add, Pi.add_apply]
      rcases ht with hge | rfl | rfl
      · rw [hm1_lo t hge, hax t hge, add_zero]
      · rw [hm1_0, hd_at_0, z2_add_self]
      · rw [hm1_1, hd_at_0, hd_at_1]
        have : ∀ x y : F, x + (x + y) + y = 0 := by decide
        exact this _ _
    have hΔy_zero : ∀ t : ZMod k, (lo + 1 ≤ t.val ∨ t = 0 ∨ t = 1) → mix 2 (turn 3 d + b) t = 0 := by
      intro t ht
      rw [mix_add, Pi.add_apply]
      rcases ht with hge | rfl | rfl
      · by_cases h2 : lo + 2 ≤ t.val
        · rw [hm2_lo2 t h2, hby2 t h2, add_zero]
        · have ht1 : t = ((lo + 1 : ℕ) : ZMod k) := by
            rw [← ZMod.natCast_zmod_val t]; congr 1; omega
          rw [ht1, hm2_lo1, hd_at_l4, z2_add_self]
      · rw [hm2_0, hby0, add_zero]
      · rw [hm2_1, hd_at_0, hsig3]
    intro s hs
    have hs1 : lo + 1 ≤ (s + 1).val ∨ s + 1 = 0 ∨ s + 1 = 1 := by
      rcases succ_inWin (by omega : 2 ≤ lo) hs with hge | h0 | h1
      · left
        have hlt : s.val < k := ZMod.val_lt s
        have hne : s.val + 1 ≠ k := by
          intro hlast
          have : (s + 1).val = 0 := by
            have : s + 1 = 0 := by
              rw [← ZMod.natCast_zmod_val s, Nat.cast_one.symm,
                  ← Nat.cast_add, hlast, ZMod.natCast_self]
            rw [this, ZMod.val_zero]
          omega
        have hv : (s + 1).val = s.val + 1 := by
          conv_lhs => rw [← ZMod.natCast_zmod_val s, ← Nat.cast_one]
          rw [← Nat.cast_add, ZMod.val_natCast_of_lt (by omega)]
        omega
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr h1)
    have hs2 : lo + 1 ≤ (s + 2).val ∨ s + 2 = 0 ∨ s + 2 = 1 := by
      rcases succ2_inWin (by omega : 2 ≤ lo) hs with hge | h0 | h1
      · left
        have hlt : s.val < k := ZMod.val_lt s
        by_cases h1k : s.val + 1 = k
        · exfalso
          have : (s + 2).val = 1 := by
            conv_lhs => rw [← ZMod.natCast_zmod_val s]
            rw [natCast_add_two, show s.val + 2 = k + 1 by omega, Nat.cast_add,
                ZMod.natCast_self, zero_add, ZMod.val_natCast_of_lt (by omega)]
          omega
        · by_cases h2k : s.val + 2 = k
          · exfalso
            have : (s + 2).val = 0 := by
              conv_lhs => rw [← ZMod.natCast_zmod_val s]
              rw [natCast_add_two, h2k, ZMod.natCast_self, ZMod.val_zero]
            omega
          · have hv : (s + 2).val = s.val + 2 := by
              conv_lhs => rw [← ZMod.natCast_zmod_val s]
              rw [natCast_add_two, ZMod.val_natCast_of_lt (by omega)]
            have hslo : lo ≤ s.val := hs
            omega
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr h1)
    refine ⟨hΔx_zero (s + 1) (succ_inWin (by omega) hs),
            hΔx_zero (s + 2) (succ2_inWin (by omega) hs),
            by rw [hΔx_zero s (Or.inl hs), hd0 s (by omega)],
            hΔy_zero (s + 1) hs1,
            hΔy_zero (s + 2) hs2, ?_⟩
    by_cases hsl : lo + 1 ≤ s.val
    · have hv4 : (s - 4).val = s.val - 4 := by simpa using val_of_sub_four (s := s) (by omega)
      rw [hΔy_zero s (Or.inl hsl), hd0 (s - 4) (by omega)]
    · have hseq : s = ((lo : ℕ) : ZMod k) := by rw [← ZMod.natCast_zmod_val s]; congr 1; omega
      rw [hseq, mix_add, Pi.add_apply, hm2_lo, hd_at_l5,
          show ((lo : ℕ) : ZMod k) - 4 = ((lo - 4 : ℕ) : ZMod k) from by rw [← Nat.cast_ofNat]; exact natCast_sub_of_le (by omega),
          hd_at_l4]
      have : ∀ x y : F, (x + y) + x = y := by decide
      exact this _ _

lemma signature_add_eq_zero_iff {k : ℕ} (h : ℕ) (u v u' v' : ZMod k → F) :
    signature h (u' + u) (v' + v) = (0, 0, 0) ↔ signature h u v = signature h u' v' := by
  unfold signature
  simp only [mix_add, Pi.add_apply, Prod.mk.injEq, funext_iff, Pi.zero_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => ((z2_eq_iff _ _).mpr (h1 j)).symm, fun j => ?_, ?_⟩
    · have hj := h2 j
      split_ifs at hj ⊢
      · exact ((z2_eq_iff _ _).mpr hj).symm
      · exact ((z2_eq_iff _ _).mpr hj).symm
    · have : ∀ a1 a2 b1 b2 : F, a2 + a1 + (b2 + b1) = 0 → a1 + b1 = a2 + b2 := by decide
      exact this _ _ _ _ h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j => (z2_eq_iff _ _).mp (h1 j).symm, fun j => ?_, ?_⟩
    · have hj := h2 j
      split_ifs at hj ⊢
      · exact (z2_eq_iff _ _).mp hj.symm
      · exact (z2_eq_iff _ _).mp hj.symm
    · have : ∀ a1 a2 b1 b2 : F, a1 + b1 = a2 + b2 → a2 + a1 + (b2 + b1) = 0 := by decide
      exact this _ _ _ _ h3

-- Count solutions d
lemma card_lifts {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k)
    (rowConst colConst u v u' v' : ZMod k → F) :
    (signature h u v = signature h u' v' →
      Nat.card {offset : ZMod k → F // liftsP h rowConst colConst (u' + u) (v' + v) offset} = 2 ^ (k - h - 7)) ∧
    (signature h u v ≠ signature h u' v' →
      Nat.card {offset : ZMod k → F // liftsP h rowConst colConst (u' + u) (v' + v) offset} = 0) := by
  classical
  set lo := k - h
  set a := u' + u
  set b := v' + v
  constructor
  · intro heq
    have hsig0 : signature h a b = (0, 0, 0) := (signature_add_eq_zero_iff h u v u' v').mpr heq
    let Free := {t : ZMod k // 2 ≤ t.val ∧ t.val ≤ lo - 6}
    let forced : ZMod k → F := fun t =>
      if t.val = 0 then mix 1 a 0
      else if t.val = 1 then mix 1 a 0 + mix 1 a 1
      else if t.val = lo - 4 then mix 2 b ((lo + 1 : ℕ) : ZMod k)
      else if t.val = lo - 5 then mix 2 b ((lo : ℕ) : ZMod k) + mix 2 b ((lo + 1 : ℕ) : ZMod k)
      else 0
    have hval0 : (0 : ZMod k).val = 0 := ZMod.val_zero
    have hval1 : (1 : ZMod k).val = 1 := val_one_zmod (by omega)
    have hvall4 : ((lo - 4 : ℕ) : ZMod k).val = lo - 4 := ZMod.val_natCast_of_lt (by omega)
    have hvall5 : ((lo - 5 : ℕ) : ZMod k).val = lo - 5 := ZMod.val_natCast_of_lt (by omega)
    let equiv : {d : ZMod k → F // liftsP h rowConst colConst a b d} ≃ (Free → F) :=
      { toFun := fun ⟨d, _⟩ ⟨t, _⟩ => d t
        invFun := fun f =>
          ⟨fun t => if ht : 2 ≤ t.val ∧ t.val ≤ lo - 6 then f ⟨t, ht⟩ else forced t, by
            rw [liftsP_iff_coords hh hk]
            refine ⟨hsig0, fun t ht => ?_, ?_, ?_, ?_, ?_⟩
            · have ht' : lo - 3 ≤ t.val := ht
              rw [dif_neg (by omega)]; simp only [forced]
              rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
            · rw [dif_neg (by rw [hval0]; omega)]; simp only [forced]; rw [if_pos hval0]
            · rw [dif_neg (by rw [hval1]; omega)]; simp only [forced]
              rw [if_neg (by rw [hval1]; omega), if_pos hval1]
            · have hv4 : ((k - h - 4 : ℕ) : ZMod k).val = lo - 4 := hvall4
              rw [dif_neg (by rw [hv4]; omega)]; simp only [forced]
              rw [if_neg (by rw [hv4]; omega), if_neg (by rw [hv4]; omega), if_pos hv4]
            · have hv5 : ((k - h - 5 : ℕ) : ZMod k).val = lo - 5 := hvall5
              rw [dif_neg (by rw [hv5]; omega)]; simp only [forced]
              rw [if_neg (by rw [hv5]; omega), if_neg (by rw [hv5]; omega),
                  if_neg (by rw [hv5]; omega), if_pos hv5]⟩
        left_inv := fun ⟨d, hd⟩ => by
          rw [liftsP_iff_coords hh hk] at hd
          obtain ⟨_, hd0, h0, h1, hl4, hl5⟩ := hd
          apply Subtype.ext; funext t; dsimp only
          by_cases ht : 2 ≤ t.val ∧ t.val ≤ lo - 6
          · rw [dif_pos ht]
          · rw [dif_neg ht]
            simp only [forced]
            by_cases hv0 : t.val = 0
            · have : t = 0 := by rw [← ZMod.natCast_zmod_val t, hv0, Nat.cast_zero]
              rw [if_pos hv0, this, h0]
            · rw [if_neg hv0]
              by_cases hv1 : t.val = 1
              · have : t = 1 := by rw [← ZMod.natCast_zmod_val t, hv1, Nat.cast_one]
                rw [if_pos hv1, this, h1]
              · rw [if_neg hv1]
                by_cases hvl4 : t.val = lo - 4
                · have : t = ((k - h - 4 : ℕ) : ZMod k) := by rw [← ZMod.natCast_zmod_val t, hvl4]
                  rw [if_pos hvl4, this, hl4]
                · rw [if_neg hvl4]
                  by_cases hvl5 : t.val = lo - 5
                  · have : t = ((k - h - 5 : ℕ) : ZMod k) := by rw [← ZMod.natCast_zmod_val t, hvl5]
                    rw [if_pos hvl5, this, hl5]
                  · rw [if_neg hvl5]
                    exact (hd0 t (by have : lo = k - h := rfl; omega)).symm
        right_inv := fun f => by
          funext ⟨t, ht⟩; simp [ht] }
    have hcardFree : Fintype.card Free = lo - 7 := by
      have hset : (Finset.univ.filter (fun t : ZMod k => 2 ≤ t.val ∧ t.val ≤ lo - 6)) =
          (Finset.Ico 2 (lo - 5)).image (fun n : ℕ => (n : ZMod k)) := by
        ext t
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_Ico]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨t.val, ⟨h1, by omega⟩, ZMod.natCast_zmod_val t⟩
        · rintro ⟨n, ⟨h1, h2⟩, rfl⟩
          rw [ZMod.val_natCast_of_lt (by omega)]; omega
      have h1 : Fintype.card Free = (Finset.univ.filter (fun t : ZMod k => 2 ≤ t.val ∧ t.val ≤ lo - 6)).card :=
        Fintype.card_subtype _
      rw [h1, hset, Finset.card_image_of_injOn]
      · rw [Nat.card_Ico]; omega
      · intro x hx y hy hxy
        simp only [Finset.mem_coe, Finset.mem_Ico] at hx hy
        exact (natCast_eq_iff_lt (by omega) (by omega)).mp hxy
    rw [Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, hcardFree]
  · intro hne
    have hEmpty : IsEmpty {d : ZMod k → F // liftsP h rowConst colConst a b d} := by
      refine ⟨fun ⟨d, hd⟩ => ?_⟩
      rw [liftsP_iff_coords hh hk] at hd
      exact hne ((signature_add_eq_zero_iff h u v u' v').mp hd.1)
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]

end Signature

namespace L25838
open Signature

abbrev Sig (h : ℕ) := (Fin h → F) × (Fin (h-1) → F) × F

def repX {k h : ℕ} [NeZero k] (hk : h ≤ k) (p : Sig h) (s : ZMod k) : F :=
  if hs : k-h ≤ s.val then p.1 ⟨s.val-(k-h), by have := ZMod.val_lt s; omega⟩ else 0

def repY {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h ≤ k) (p : Sig h) (s : ZMod k) : F :=
  if s.val = 0 then p.2.1 ⟨0, by omega⟩ else
  if s.val = 1 then p.2.2 else
  if hs : k-h+2 ≤ s.val then p.2.1 ⟨s.val-(k-h+1), by have := ZMod.val_lt s; omega⟩ else 0

def mixedGood {k : ℕ} (h : ℕ) (rc cc x y key : ZMod k → F) : Prop :=
  ∀ s : ZMod k, k-h ≤ s.val →
    chi (mix 1 (turn 1 key) + x) s + key s + rc s = 0 ∧
    chi (mix 2 (turn 3 key) + y) s + turn 4 key s + cc s = 0

lemma good_mixed {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h+7 ≤ k)
    (rc cc u v x y : ZMod k → F)
    (hx : ∀ s, inWin (k-h) s → mix 1 u s = x s)
    (hy : ∀ s, inWin (k-h) s → mix 2 v s = y s) (key : ZMod k → F) :
    goodP h rc cc u v key ↔ mixedGood h rc cc x y key := by
  unfold goodP mixedGood
  simp only [Pi.add_apply, mix_add]
  refine forall_congr' fun s => imp_congr_right fun hs => ?_
  have hx' : ∀ t, inWin (k-h) t → (mix 1 (turn 1 key) + mix 1 u) t = (mix 1 (turn 1 key) + x) t :=
    fun t ht => by simp [hx t ht]
  have hy' : ∀ t, inWin (k-h) t → (mix 2 (turn 3 key) + mix 2 v) t = (mix 2 (turn 3 key) + y) t :=
    fun t ht => by simp [hy t ht]
  rw [chi_congr_win (by omega : 2 ≤ k-h) hx' hs, chi_congr_win (by omega : 2 ≤ k-h) hy' hs]

lemma repSig {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h+7 ≤ k) (p : Sig h) :
    ∃ u v : ZMod k → F, signature h u v = p ∧
      (∀ s, inWin (k-h) s → mix 1 u s = repX (by omega : h ≤ k) p s) ∧
      (∀ s, inWin (k-h) s → mix 2 v s = repY hh (by omega : h ≤ k) p s) := by
  let lo := k-h
  let X : ZMod k → F := repX (by omega : h ≤ k) p
  let Y : ZMod k → F := repY hh (by omega : h ≤ k) p
  obtain ⟨u, hu⟩ := surj_mix1 hh hk X
  obtain ⟨v, hv⟩ := surj_mix2 hh hk Y
  refine ⟨u,v,?_,hu,hv⟩
  have hv1 : (1 : ZMod k).val = 1 := val_one_zmod (by omega)
  apply Prod.ext
  · funext j
    change mix 1 u ((lo+j.val : ℕ) : ZMod k) = p.1 j
    have hj := j.isLt
    have hvj : ((lo+j.val : ℕ) : ZMod k).val = lo+j.val := ZMod.val_natCast_of_lt (by omega)
    rw [hu _ (Or.inl (by rw [hvj]; omega))]
    simp only [X, repX, hvj, dif_pos (by omega : k-h ≤ lo+j.val)]
    congr 1
    exact Fin.ext (by simp [lo])
  · apply Prod.ext
    · funext j
      change (if j.val = 0 then mix 2 v 0 else mix 2 v ((lo+1+j.val : ℕ) : ZMod k)) = p.2.1 j
      by_cases hj : j.val = 0
      · rw [if_pos hj, hv _ (Or.inr (Or.inl rfl))]
        simp only [Y, repY, ZMod.val_zero, if_true]
        exact congrArg p.2.1 (Fin.ext hj.symm)
      · have hlt := j.isLt
        have hvj : ((lo+1+j.val : ℕ) : ZMod k).val = lo+1+j.val := ZMod.val_natCast_of_lt (by omega)
        rw [if_neg hj, hv _ (Or.inl (by rw [hvj]; omega))]
        simp only [Y, repY, hvj, if_neg (by omega : lo+1+j.val ≠ 0), if_neg (by omega : lo+1+j.val ≠ 1), dif_pos (by omega : k-h+2 ≤ lo+1+j.val)]
        congr 1
        exact Fin.ext (by simp [lo])
    · change mix 1 u 0 + mix 2 v 1 = p.2.2
      rw [hu _ (Or.inr (Or.inl rfl)), hv _ (Or.inr (Or.inr rfl))]
      simp [X, Y, repX, repY, hv1, show ¬ k-h ≤ 0 by omega]

lemma normEquiv {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h+7 ≤ k) (rc cc u v : ZMod k → F) :
    let p := signature h u v
    Nonempty ({key // goodP h rc cc u v key} ≃
      {key // mixedGood h rc cc (repX (by omega : h ≤ k) p) (repY hh (by omega : h ≤ k) p) key}) := by
  classical
  intro p
  obtain ⟨u',v',hs,hx,hy⟩ := repSig hh hk p
  have hc := (card_lifts hh hk rc cc u v u' v').1 hs.symm
  have hn : Nonempty {d : ZMod k → F // liftsP h rc cc (u'+u) (v'+v) d} := by
    refine (Nat.card_pos_iff.mp ?_).1
    rw [hc]
    positivity
  let d := Classical.choice hn
  have ht (key : ZMod k → F) : goodP h rc cc u v key ↔ goodP h rc cc u' v' (key+d.1) := by
    have H := d.2 u v key
    have hu : u+(u'+u) = u' := by funext s; simp [Pi.add_apply, add_comm (u' s) (u s), z2_add_cancel_left]
    have hv : v+(v'+v) = v' := by funext s; simp [Pi.add_apply, add_comm (v' s) (v s), z2_add_cancel_left]
    rwa [hu,hv] at H
  have hg (key : ZMod k → F) := (ht key).trans (good_mixed hh hk rc cc u' v' _ _ hx hy _)
  have invol (key : ZMod k → F) : key+d.1+d.1 = key := by funext s; exact z2_add_cancel _ _
  exact ⟨{
    toFun := fun key => ⟨key.1+d.1, (hg key.1).mp key.2⟩
    invFun := fun key => ⟨key.1+d.1, (hg (key.1+d.1)).mpr (by rw [invol]; exact key.2)⟩
    left_inv := fun key => Subtype.ext (invol key.1)
    right_inv := fun key => Subtype.ext (invol key.1) }⟩

end L25838

namespace L25838
open Signature

private def bit (x : F) : Bool := decide (x = 1)
private def fromBit (x : Bool) : F := if x then 1 else 0
private lemma from_bit (x : F) : fromBit (bit x) = x := by revert x; decide
private lemma bit_from (x : Bool) : bit (fromBit x) = x := by cases x <;> rfl
private lemma bit_add (x y : F) : bit (x+y) = xor (bit x) (bit y) := by revert x y; decide
private lemma bit_mul (x y : F) : bit (x*y) = (bit x && bit y) := by revert x y; decide
private lemma bit_not (x : F) : bit (1+x) = !bit x := by revert x; decide
private lemma zero_bit (x : F) : (!bit x) = true ↔ x = 0 := by revert x; decide

private def inputList {h : ℕ} (p : Sig h) : List Bool :=
  List.ofFn (fun i => bit (p.1 i)) ++ List.ofFn (fun j => bit (p.2.1 j)) ++ [bit p.2.2]

private lemma inputLen {h : ℕ} (hh : 5 ≤ h) (p : Sig h) : (inputList p).length = 2*h := by
  simp [inputList]; omega

private def inputSig (h : ℕ) (l : List Bool) : Sig h :=
  (fun i => fromBit (l.getD i.val false), fun j => fromBit (l.getD (h+j.val) false),
    fromBit (l.getD (h+(h-1)) false))

private lemma input_round {h : ℕ} (hh : 5 ≤ h) (p : Sig h) : inputSig h (inputList p) = p := by
  unfold inputSig inputList
  apply Prod.ext
  · funext i
    dsimp only
    rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simpa using i.isLt)]
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt), List.getElem_ofFn]
    exact from_bit _
  · apply Prod.ext
    · funext j
      dsimp only
      rw [List.getD_append _ _ _ _ (by simpa using Nat.add_lt_add_left j.isLt h), List.getD_append_right _ _ _ _ (by simp)]
      rw [show h+j.val-(List.ofFn (fun i => bit (p.1 i))).length = j.val by simp]
      rw [List.getD_eq_getElem _ _ (by simpa using j.isLt), List.getElem_ofFn]
      exact from_bit _
    · dsimp only
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp [from_bit]

end L25838
namespace KeyFlags

abbrev F := ZMod 2
abbrev Word (k : ℕ) := ZMod k → F
abbrev Seed := Fin 4 → F

def pos (k i : ℕ) : ZMod k := ((1 - (i : ℤ) : ℤ) : ZMod k)

def turn {k : ℕ} (d : ℕ) (w : Word k) (s : ZMod k) : F := w (s - d)
def mix {k : ℕ} (d : ℕ) (w : Word k) (s : ZMod k) : F :=
  w (s - d) + w s + w (s + d)
def chi {k : ℕ} (w : Word k) (s : ZMod k) : F :=
  w s + (1 + w (s + 1)) * w (s + 2)
def row {k : ℕ} (x rc key : Word k) (s : ZMod k) : F :=
  chi (mix 1 (turn 1 key) + x) s + key s + rc s
def col {k : ℕ} (y cc key : Word k) (s : ZMod k) : F :=
  chi (mix 2 (turn 3 key) + y) s + turn 4 key s + cc s

def goodMixed {k : ℕ} (h : ℕ) (u rc v cc key : Word k) : Prop :=
  ∀ s : ZMod k, k - h ≤ s.val →
    chi (mix 1 (turn 1 key + u)) s + key s + rc s = 0 ∧
    chi (mix 2 (turn 3 key + v)) s + turn 4 key s + cc s = 0

def good {k : ℕ} (h : ℕ) (x rc y cc key : Word k) : Prop :=
  ∀ s : ZMod k, k - h ≤ s.val → row x rc key s = 0 ∧ col y cc key s = 0

lemma mix_add {k : ℕ} (d : ℕ) (a b : Word k) : mix d (a + b) = mix d a + mix d b := by
  funext s
  simp only [mix, Pi.add_apply]
  ring

lemma goodMixed_iff {k : ℕ} (h : ℕ) (u rc v cc key : Word k) :
    goodMixed h u rc v cc key ↔ good h (mix 1 u) rc (mix 2 v) cc key := by
  simp only [goodMixed, good, row, col, mix_add]

def rowBit {k : ℕ} (u rc : Word k) (i : ℕ) (prev : ℕ → F) : F :=
  let s := pos k (i - 2)
  let m1 := prev (i-1) + prev (i-2) + prev (i-3) + u (s+1)
  let m2 := prev (i-2) + prev (i-3) + prev (i-4) + u (s+2)
  prev (i-1) + prev (i-2) + u s + (1+m1)*m2 + prev (i-2) + rc s

def colBit {k : ℕ} (v cc : Word k) (i : ℕ) (prev : ℕ → F) : F :=
  let s := pos k (i - 5)
  let m1 := prev (i-1) + prev (i-3) + prev (i-5) + v (s+1)
  let m2 := prev (i-2) + prev (i-4) + prev (i-6) + v (s+2)
  prev (i-2) + prev (i-4) + v s + (1+m1)*m2 + prev (i-1) + cc s

def keyBit {k : ℕ} (h : ℕ) (u rc v cc : Word k) (seed : Seed) (i : ℕ) : F :=
  if hi : i < 4 then seed ⟨i, hi⟩
  else if i < h + 4 then
    rowBit u rc i (fun j => if _hj : j < i then keyBit h u rc v cc seed j else 0)
  else if i < h + 7 then
    colBit v cc i (fun j => if _hj : j < i then keyBit h u rc v cc seed j else 0)
  else 0
termination_by i

def rawKey {k : ℕ} (h : ℕ) (u rc v cc : Word k) (seed : Seed) : Word k :=
  fun s => keyBit h u rc v cc seed (1 - s).val

def keySeed {k : ℕ} (key : Word k) : Seed := fun j => key (pos k j.val)

def passive {k : ℕ} (h : ℕ) (s : ZMod k) : Prop := h + 7 ≤ (1 - s).val

lemma pos_nat {k i : ℕ} : pos k i = 1 - (i : ZMod k) := by simp [pos]

lemma pos_val {k : ℕ} [NeZero k] (s : ZMod k) : pos k (1-s).val = s := by
  rw [pos_nat, ZMod.natCast_zmod_val]; ring

lemma val_pos {k i : ℕ} [NeZero k] (hi : i < k) : (1 - pos k i).val = i := by
  have e : 1 - pos k i = (i : ZMod k) := by rw [pos_nat]; ring
  rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

lemma raw_at {k h : ℕ} [NeZero k] (u rc v cc : Word k) (seed : Seed) {i : ℕ} (hi : i < k) :
    rawKey h u rc v cc seed (pos k i) = keyBit h u rc v cc seed i := by
  simp [rawKey, val_pos hi]

lemma pos_shift {k i a b : ℕ} (ha : a ≤ i) (hb : b ≤ i) :
    pos k (i-a) = pos k (i-b) + (a : ZMod k) - (b : ZMod k) := by
  simp only [pos, Int.ofNat_sub ha, Int.ofNat_sub hb, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  ring

lemma row_eq {k : ℕ} (u rc key : Word k) (i : ℕ) (hi : 4 ≤ i) :
    row u rc key (pos k (i-2)) = key (pos k i) + rowBit u rc i (fun j => key (pos k j)) := by
  have p0 := pos_shift (k := k) (a := 0) (b := 2) (i := i) (by omega) (by omega)
  have p1 := pos_shift (k := k) (a := 1) (b := 2) (i := i) (by omega) (by omega)
  have p3 := pos_shift (k := k) (a := 3) (b := 2) (i := i) (by omega) (by omega)
  have p4 := pos_shift (k := k) (a := 4) (b := 2) (i := i) (by omega) (by omega)
  simp only [Nat.sub_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at p0 p1 p3 p4
  simp only [row, chi, mix, turn, Pi.add_apply, rowBit, p0, p1, p3, p4, Nat.cast_one]
  ring_nf

lemma col_eq {k : ℕ} (v cc key : Word k) (i : ℕ) (hi : 6 ≤ i) :
    col v cc key (pos k (i-5)) = key (pos k i) + colBit v cc i (fun j => key (pos k j)) := by
  have p0 := pos_shift (k := k) (a := 0) (b := 5) (i := i) (by omega) (by omega)
  have p1 := pos_shift (k := k) (a := 1) (b := 5) (i := i) (by omega) (by omega)
  have p2 := pos_shift (k := k) (a := 2) (b := 5) (i := i) (by omega) (by omega)
  have p3 := pos_shift (k := k) (a := 3) (b := 5) (i := i) (by omega) (by omega)
  have p4 := pos_shift (k := k) (a := 4) (b := 5) (i := i) (by omega) (by omega)
  have p6 := pos_shift (k := k) (a := 6) (b := 5) (i := i) (by omega) (by omega)
  simp only [Nat.sub_zero, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one] at p0 p1 p2 p3 p4 p6
  simp only [col, chi, mix, turn, Pi.add_apply, colBit, p0, p1, p2, p3, p4, p6, Nat.cast_ofNat]
  ring_nf

lemma rowBit_congr {k : ℕ} (x rc : Word k) {i : ℕ} (hi : 4 ≤ i) (a b : ℕ → F)
    (e : ∀ j < i, a j = b j) : rowBit x rc i a = rowBit x rc i b := by
  simp [rowBit, e (i-1) (by omega), e (i-2) (by omega), e (i-3) (by omega), e (i-4) (by omega)]

lemma colBit_congr {k : ℕ} (y cc : Word k) {i : ℕ} (hi : 6 ≤ i) (a b : ℕ → F)
    (e : ∀ j < i, a j = b j) : colBit y cc i a = colBit y cc i b := by
  simp [colBit, e (i-1) (by omega), e (i-2) (by omega), e (i-3) (by omega),
    e (i-4) (by omega), e (i-5) (by omega), e (i-6) (by omega)]

lemma keyBit_row {k h i : ℕ} (x rc y cc : Word k) (seed : Seed)
    (hi : 4 ≤ i) (hr : i < h + 4) :
    keyBit h x rc y cc seed i = rowBit x rc i (keyBit h x rc y cc seed) := by
  conv_lhs => rw [keyBit]
  rw [dite_eq_right (by omega : ¬ i < 4), ite_eq_left hr]
  apply rowBit_congr x rc hi
  intro j hj
  simp [hj]

lemma keyBit_col {k h i : ℕ} (x rc y cc : Word k) (seed : Seed)
    (hi : 6 ≤ i) (hr : h + 4 ≤ i) (hc : i < h + 7) :
    keyBit h x rc y cc seed i = colBit y cc i (keyBit h x rc y cc seed) := by
  conv_lhs => rw [keyBit]
  rw [dite_eq_right (by omega : ¬ i < 4), ite_eq_right (by omega : ¬ i < h + 4), ite_eq_left hc]
  apply colBit_congr y cc hi
  intro j hj
  simp [hj]

lemma keyBit_seed {k h : ℕ} (x rc y cc : Word k) (seed : Seed) (i : Fin 4) :
    keyBit h x rc y cc seed i = seed i := by
  rw [keyBit, dite_eq_left i.isLt]

lemma pivot_site {k : ℕ} [NeZero k] {h j : ℕ} (hk : h + 7 ≤ k)
    (h2 : 2 ≤ j) (hh : j ≤ h + 1) : k - h ≤ (pos k j).val := by
  have he : ((pos k j).val : ℤ) = (k : ℤ) + 1 - j := by
    unfold pos
    rw [ZMod.val_intCast]
    have hm : (1 - (j : ℤ) + k) % (k : ℤ) = (1 - (j : ℤ)) % (k : ℤ) := by simp
    rw [← hm, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  omega

lemma site_index {k : ℕ} [NeZero k] {h : ℕ} (hk : h + 7 ≤ k) (s : ZMod k)
    (hs : k - h ≤ s.val) : ∃ j : ℕ, 2 ≤ j ∧ j ≤ h + 1 ∧ pos k j = s := by
  have hv := ZMod.val_lt s
  refine ⟨k + 1 - s.val, by omega, by omega, ?_⟩
  rw [pos_nat, Nat.cast_sub (by omega : s.val ≤ k + 1), Nat.cast_add,
    Nat.cast_one, ZMod.natCast_self, zero_add, ZMod.natCast_zmod_val]
  ring

private lemma add_zero_iff_eq (a b : F) : a + b = 0 ↔ a = b := by
  revert a b
  decide

lemma keyBit_agree {k h : ℕ} [NeZero k] (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (x rc y cc key : Word k) (hg : good h x rc y cc key)
    (i : ℕ) (hi : i < h + 7) :
    key (pos k i) = keyBit h x rc y cc (keySeed key) i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hseed : i < 4
    · exact (keyBit_seed x rc y cc (keySeed key) ⟨i, hseed⟩).symm
    by_cases hr : i < h + 4
    · rw [keyBit_row x rc y cc _ (by omega) hr]
      have hg' := (hg (pos k (i-2)) (pivot_site hk (by omega) (by omega))).1
      rw [row_eq x rc key i (by omega), add_zero_iff_eq] at hg'
      rw [hg']
      exact rowBit_congr x rc (by omega) _ _ (fun j hj => ih j hj (by omega))
    · rw [keyBit_col x rc y cc _ (by omega) (by omega) hi]
      have hg' := (hg (pos k (i-5)) (pivot_site hk (by omega) (by omega))).2
      rw [col_eq y cc key i (by omega), add_zero_iff_eq] at hg'
      rw [hg']
      exact colBit_congr y cc (by omega) _ _ (fun j hj => ih j hj (by omega))

lemma raw_row {k h i : ℕ} [NeZero k] (x rc y cc : Word k) (seed : Seed)
    (hi : 4 ≤ i) (hik : i < k) :
    row x rc (rawKey h x rc y cc seed) (pos k (i-2)) =
      keyBit h x rc y cc seed i + rowBit x rc i (keyBit h x rc y cc seed) := by
  rw [row_eq x rc _ i hi, raw_at x rc y cc seed hik]
  rw [rowBit_congr x rc hi _ _ (fun j hj => raw_at x rc y cc seed (by omega))]

lemma raw_col {k h i : ℕ} [NeZero k] (x rc y cc : Word k) (seed : Seed)
    (hi : 6 ≤ i) (hik : i < k) :
    col y cc (rawKey h x rc y cc seed) (pos k (i-5)) =
      keyBit h x rc y cc seed i + colBit y cc i (keyBit h x rc y cc seed) := by
  rw [col_eq y cc _ i hi, raw_at x rc y cc seed hik]
  rw [colBit_congr y cc hi _ _ (fun j hj => raw_at x rc y cc seed (by omega))]

lemma good_raw_iff {k h : ℕ} [NeZero k] (hk : h + 7 ≤ k)
    (x rc y cc : Word k) (seed : Seed) :
    good h x rc y cc (rawKey h x rc y cc seed) ↔
      ∀ i : ℕ, 7 ≤ i → i < h + 4 →
        keyBit h x rc y cc seed i = colBit y cc i (keyBit h x rc y cc seed) := by
  constructor
  · intro hg i hi hu
    have he := (hg (pos k (i-5)) (pivot_site hk (by omega) (by omega))).2
    rwa [raw_col x rc y cc seed (by omega) (by omega), add_zero_iff_eq] at he
  · intro hg s hs
    obtain ⟨j, hj, hu, rfl⟩ := site_index hk s hs
    have er : j + 2 - 2 = j := by omega
    have ec : j + 5 - 5 = j := by omega
    have fr := raw_row (h := h) (i := j+2) x rc y cc seed (by omega) (by omega)
    have fc := raw_col (h := h) (i := j+5) x rc y cc seed (by omega) (by omega)
    rw [er] at fr
    rw [ec] at fc
    rw [fr, fc, add_zero_iff_eq, add_zero_iff_eq]
    refine ⟨keyBit_row x rc y cc seed (by omega) (by omega), ?_⟩
    by_cases hi : j + 5 < h + 4
    · exact hg (j+5) (by omega) hi
    · exact keyBit_col x rc y cc seed (by omega) (by omega) (by omega)

lemma good_congr {k h : ℕ} [NeZero k] (hk : h + 7 ≤ k)
    (x rc y cc a b : Word k) (e : ∀ i < h + 7, a (pos k i) = b (pos k i)) :
    good h x rc y cc a ↔ good h x rc y cc b := by
  apply forall_congr'
  intro s
  apply imp_congr_right
  intro hs
  obtain ⟨j, hj, hu, rfl⟩ := site_index hk s hs
  have er : j + 2 - 2 = j := by omega
  have ec : j + 5 - 5 = j := by omega
  have r (w : Word k) := row_eq x rc w (j+2) (by omega)
  have c (w : Word k) := col_eq y cc w (j+5) (by omega)
  simp only [er] at r
  simp only [ec] at c
  simp only [r, c, e (j+2) (by omega), e (j+5) (by omega),
    rowBit_congr x rc (by omega : 4 ≤ j+2) _ _ (fun i hi => e i (by omega)),
    colBit_congr y cc (by omega : 6 ≤ j+5) _ _ (fun i hi => e i (by omega))]

lemma raw_seed {k h : ℕ} [NeZero k] (hk : h + 7 ≤ k) (x rc y cc : Word k)
    (seed : Seed) : keySeed (rawKey h x rc y cc seed) = seed := by
  funext i
  have := i.isLt
  exact (raw_at x rc y cc seed (by omega)).trans (keyBit_seed x rc y cc seed i)

noncomputable def seedFiberEquiv {k h : ℕ} [NeZero k] (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (x rc y cc : Word k) (seed : Seed) (hg : good h x rc y cc (rawKey h x rc y cc seed)) :
    {key // good h x rc y cc key ∧ keySeed key = seed} ≃ ({s : ZMod k // passive h s} → F) := by
  classical
  refine
    { toFun := fun a s => a.1 s.1
      invFun := fun f => ⟨fun s => if hs : passive h s then f ⟨s, hs⟩ else rawKey h x rc y cc seed s, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have e (i : ℕ) (hi : i < h + 7) : ¬ passive h (pos k i) := by
      simp only [passive, val_pos (by omega : i < k)]
      omega
    refine ⟨(good_congr hk x rc y cc _ _ (fun i hi => dite_eq_right (e i hi))).mpr hg, ?_⟩
    funext i
    have := i.isLt
    exact (dite_eq_right (e i (by omega))).trans (congrFun (raw_seed hk x rc y cc seed) i)
  · intro a
    apply Subtype.ext
    funext s
    by_cases hs : passive h s
    · simp only [dite_eq_left hs]
    · simp only [dite_eq_right hs]
      let i := (1-s).val
      have hi : i < h + 7 := Nat.lt_of_not_ge hs
      rw [← pos_val s, raw_at x rc y cc seed (by omega : i < k)]
      have ha := keyBit_agree h5 hk x rc y cc a.1 a.2.1 i hi
      rw [a.2.2] at ha
      exact ha.symm
  · intro f
    funext s
    exact dite_eq_left s.2

def passiveEquiv {k h : ℕ} [NeZero k] (hk : h + 7 ≤ k) :
    {s : ZMod k // passive h s} ≃ Fin (k - h - 7) where
  toFun s := ⟨(1-s.1).val - (h+7), by
    have hv := ZMod.val_lt (1-s.1)
    have hs := s.2
    unfold passive at hs
    omega⟩
  invFun i := ⟨pos k (h+7+i), by
    have hi := i.isLt
    simp only [passive, val_pos (by omega : h+7+i.val < k)]
    omega⟩
  left_inv s := by
    apply Subtype.ext
    have hs := s.2
    unfold passive at hs
    change pos k (h+7+((1-s.1).val - (h+7))) = s.1
    rw [show h+7+((1-s.1).val - (h+7)) = (1-s.1).val by omega, pos_val]
  right_inv i := by
    apply Fin.ext
    have hi := i.isLt
    change (1-pos k (h+7+i.val)).val - (h+7) = i.val
    rw [val_pos (by omega : h+7+i.val < k)]
    omega

lemma seeded_count {k h : ℕ} [NeZero k] (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (x rc y cc : Word k) (seed : Seed)
    [Decidable (good h x rc y cc (rawKey h x rc y cc seed))] :
    Nat.card {key // good h x rc y cc key ∧ keySeed key = seed} =
      if good h x rc y cc (rawKey h x rc y cc seed) then 2 ^ (k - h - 7) else 0 := by
  split_ifs with hg
  · rw [Nat.card_congr (seedFiberEquiv h5 hk x rc y cc seed hg), Nat.card_fun,
      Nat.card_zmod, Nat.card_congr (passiveEquiv hk), Nat.card_fin]
  · apply Nat.card_eq_zero.mpr
    left
    constructor
    intro a
    apply hg
    apply (good_congr hk x rc y cc a.1 _ ?_).mp a.2.1
    intro i hi
    rw [raw_at x rc y cc seed (by omega)]
    simpa only [a.2.2] using keyBit_agree h5 hk x rc y cc a.1 a.2.1 i hi

lemma good_raw_iff_flags {k h : ℕ} [NeZero k] (hk : h + 7 ≤ k)
    (x rc y cc : Word k) (seed : Seed) :
    good h x rc y cc (rawKey h x rc y cc seed) ↔
      ∀ t : ℕ, t < h → keyBit h x rc y cc seed (t+7) +
        colBit y cc (t+7) (keyBit h x rc y cc seed) = 0 := by
  rw [good_raw_iff hk]
  constructor
  · intro hg t ht
    rw [add_zero_iff_eq]
    by_cases hi : t + 7 < h + 4
    · exact hg (t+7) (by omega) hi
    · exact keyBit_col x rc y cc seed (by omega) (by omega) (by omega)
  · intro hg i hi hu
    have he := hg (i-7) (by omega)
    rwa [show i-7+7 = i by omega, add_zero_iff_eq] at he

lemma raw_good_of_good {k h : ℕ} [NeZero k] (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (x rc y cc key : Word k) (hg : good h x rc y cc key) :
    good h x rc y cc (rawKey h x rc y cc (keySeed key)) := by
  apply (good_congr hk x rc y cc key _ ?_).mp hg
  intro i hi
  rw [raw_at x rc y cc _ (by omega)]
  exact keyBit_agree h5 hk x rc y cc key hg i hi

noncomputable def allFiberEquiv {k h : ℕ} [NeZero k] (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (x rc y cc : Word k) :
    {key // good h x rc y cc key} ≃
      {seed // good h x rc y cc (rawKey h x rc y cc seed)} × ({s : ZMod k // passive h s} → F) := by
  let e (s : {seed // good h x rc y cc (rawKey h x rc y cc seed)}) :=
    seedFiberEquiv h5 hk x rc y cc s.1 s.2
  refine
    { toFun := fun a => ⟨⟨keySeed a.1, raw_good_of_good h5 hk x rc y cc a.1 a.2⟩, fun s => a.1 s.1⟩
      invFun := fun p => ⟨((e p.1).symm p.2).1, ((e p.1).symm p.2).2.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro a
    apply Subtype.ext
    let s := (⟨keySeed a.1, raw_good_of_good h5 hk x rc y cc a.1 a.2⟩ :
      {seed // good h x rc y cc (rawKey h x rc y cc seed)})
    change ((e s).symm (fun j => a.1 j.1)).1 = a.1
    exact congrArg Subtype.val ((e s).symm_apply_apply ⟨a.1, a.2, rfl⟩)
  · intro p
    apply Prod.ext
    · exact Subtype.ext (((e p.1).symm p.2).2.2)
    · exact (e p.1).apply_symm_apply p.2

lemma good_count {k h : ℕ} [NeZero k] (h5 : 5 ≤ h) (hk : h + 7 ≤ k)
    (x rc y cc : Word k) [DecidablePred (fun seed => good h x rc y cc (rawKey h x rc y cc seed))] :
    Nat.card {key // good h x rc y cc key} =
      2 ^ (k-h-7) * (Finset.univ.filter (fun seed => good h x rc y cc (rawKey h x rc y cc seed))).card := by
  classical
  rw [Nat.card_congr (allFiberEquiv h5 hk x rc y cc), Nat.card_prod, Nat.card_fun,
    Nat.card_zmod, Nat.card_congr (passiveEquiv hk), Nat.card_fin, Nat.mul_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end KeyFlags

namespace CircuitBackend

open PEqualNP.CircuitLowerBounds (Circuit Gate GateOp)
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

-- The wire preservation and readback arguments are adapted from
-- lean/PEqualNP/Outside/L_clb_050.lean at 74a5059cc09594a6916f6f4f83652aa8b2fc359f.
-- Arrays make append inexpensive; the public circuit has the prescribed list of gates.
structure Builder (n : ℕ) where
  gates : Array Gate
  fan : FanInTwo ⟨gates.toList, 0⟩
  back : ReadsBack n ⟨gates.toList, 0⟩

variable {n : ℕ}

namespace Builder

def empty (n : ℕ) : Builder n :=
  ⟨#[], by simp [FanInTwo], by simp [ReadsBack]⟩

def size (b : Builder n) : ℕ := b.gates.size

def circuit (b : Builder n) (out : ℕ) : Circuit := ⟨b.gates.toList, out⟩

@[simp] theorem circuit_size (b : Builder n) (out : ℕ) : (b.circuit out).size = b.size := by
  simp [circuit, size, Circuit.size]

@[simp] theorem empty_size (n : ℕ) : (empty n).size = 0 := rfl

theorem fanInTwo (b : Builder n) (out : ℕ) : FanInTwo (b.circuit out) := b.fan

theorem readsBack (b : Builder n) (out : ℕ) : ReadsBack n (b.circuit out) := b.back

def read (b : Builder n) (x : List Bool) (i : ℕ) : Bool :=
  ((b.circuit 0).wires x).getD i false

@[simp] theorem circuit_eval (b : Builder n) (out : ℕ) (x : List Bool) :
    (b.circuit out).eval x = b.read x out := rfl

end Builder

private def evalGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl evalGate x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp [ih, evalGate]; omega

private theorem fold_read (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl evalGate x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [evalGate]; omega)]
    exact List.getD_append _ _ _ _ hi

def Extends (b c : Builder n) : Prop := ∃ gs : List Gate, c.gates.toList = b.gates.toList ++ gs

namespace Extends

theorem refl (b : Builder n) : Extends b b := ⟨[], by simp⟩

theorem trans {b c d : Builder n} (h : Extends b c) (h' : Extends c d) : Extends b d := by
  obtain ⟨gs, h⟩ := h
  obtain ⟨gs', h'⟩ := h'
  exact ⟨gs ++ gs', by rw [h', h, List.append_assoc]⟩

theorem size_le {b c : Builder n} (h : Extends b c) : b.size ≤ c.size := by
  obtain ⟨gs, h⟩ := h
  have he := congrArg List.length h
  simp at he
  unfold Builder.size
  omega

theorem bound {b c : Builder n} (h : Extends b c) {i : ℕ} (hi : i < n + b.size) :
    i < n + c.size := lt_of_lt_of_le hi (Nat.add_le_add_left h.size_le n)

theorem eval_eq {b c : Builder n} (h : Extends b c) (x : List Bool) (hx : x.length = n)
    {i : ℕ} (hi : i < n + b.size) : c.read x i = b.read x i := by
  obtain ⟨gs, h⟩ := h
  change (c.gates.toList.foldl evalGate x).getD i false =
    (b.gates.toList.foldl evalGate x).getD i false
  rw [h, List.foldl_append]
  exact fold_read gs _ i (by simpa only [fold_length, Array.length_toList, hx, Builder.size] using hi)

end Extends

/-- A bounded wire together with the Boolean function it computes. -/
structure Wire (b : Builder n) (f : List Bool → Bool) where
  index : ℕ
  bound : index < n + b.size
  eval_eq : ∀ x, x.length = n → b.read x index = f x

namespace Wire

variable {b c : Builder n} {f g : List Bool → Bool}

def fin (w : Wire b f) : Fin (n + b.size) := ⟨w.index, w.bound⟩

def raw (b : Builder n) (i : Fin (n + b.size)) : Wire b (fun x => b.read x i) :=
  ⟨i, i.isLt, fun _ _ => rfl⟩

def lift (w : Wire b f) (h : Extends b c) : Wire c f :=
  ⟨w.index, h.bound w.bound, fun x hx => (h.eval_eq x hx w.bound).trans (w.eval_eq x hx)⟩

def congr (w : Wire b f) (h : ∀ x, x.length = n → f x = g x) : Wire b g :=
  ⟨w.index, w.bound, fun x hx => (w.eval_eq x hx).trans (h x hx)⟩

@[simp] theorem lift_index (w : Wire b f) (h : Extends b c) : (w.lift h).index = w.index := rfl

@[simp] theorem congr_index (w : Wire b f) (h : ∀ x, x.length = n → f x = g x) :
    (w.congr h).index = w.index := rfl

@[simp] theorem fin_val (w : Wire b f) : w.fin.val = w.index := rfl

end Wire

def Builder.input (b : Builder n) (i : Fin n) : Wire b (fun x => x.getD i false) :=
  ⟨i, by have := i.isLt; omega, fun x hx => fold_read b.gates.toList x i (hx ▸ i.isLt)⟩

/-- A builder extension with a gate budget and an indexed result (e.g. a wire or loop invariant). -/
structure Advance (b : Builder n) (cost : ℕ) (A : Builder n → Type*) where
  next : Builder n
  extension : Extends b next
  cost_le : next.size ≤ b.size + cost
  value : A next

abbrev Result (b : Builder n) (cost : ℕ) (f : List Bool → Bool) :=
  Advance b cost (fun c => Wire c f)

namespace Advance

variable {b : Builder n} {a d : ℕ} {A : Builder n → Type*} {B : Builder n → Type*}

def pure (value : A b) : Advance b 0 A := ⟨b, Extends.refl b, by simp, value⟩

def map (r : Advance b a A) (f : ∀ c, A c → B c) : Advance b a B :=
  ⟨r.next, r.extension, r.cost_le, f r.next r.value⟩

def replace (r : Advance b a A) (value : B r.next) : Advance b a B :=
  ⟨r.next, r.extension, r.cost_le, value⟩

def weaken (r : Advance b a A) (h : a ≤ d) : Advance b d A :=
  ⟨r.next, r.extension, r.cost_le.trans (Nat.add_le_add_left h _), r.value⟩

def seq (r : Advance b a A) (s : Advance r.next d B) : Advance b (a + d) B :=
  ⟨s.next, r.extension.trans s.extension,
    by have h := r.cost_le; have h' := s.cost_le; omega, s.value⟩

def bind (r : Advance b a A) (step : ∀ c, A c → Advance c d B) : Advance b (a + d) B :=
  r.seq (step r.next r.value)

def wire {f : List Bool → Bool} (r : Result b a f) : Wire r.next f := r.value

/-- Iterations run in ascending order, at most `cost` gates each. -/
def loop (m cost : ℕ) {S : ℕ → Builder n → Type*}
    (step : ∀ (i : Fin m) c, S i.val c → Advance c cost (S (i.val + 1)))
    (b : Builder n) (init : S 0 b) : Advance b (m * cost) (S m) :=
  go 0 (Nat.zero_le m) ⟨b, Extends.refl b, by simp, init⟩
where
  go (i : ℕ) (hi : i ≤ m) (r : Advance b (i * cost) (S i)) : Advance b (m * cost) (S m) :=
    if h : i < m then
      let s := step ⟨i, h⟩ r.next r.value
      go (i + 1) (by omega) ⟨s.next, r.extension.trans s.extension,
        by rw [Nat.succ_mul]; have h₁ := r.cost_le; have h₂ := s.cost_le; omega, s.value⟩
    else by
      have he : i = m := by omega
      subst i
      exact r
  termination_by m - i
  decreasing_by omega

def relabel {b : Builder n} {a : ℕ} {f g : List Bool → Bool}
    (r : Result b a f) (h : ∀ x, x.length = n → f x = g x) : Result b a g :=
  r.map fun _ w => w.congr h

end Advance

private def Builder.push (b : Builder n) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ i ∈ ins, i < n + b.size) : Builder n where
  gates := b.gates.push ⟨op, ins⟩
  fan := by
    intro g hg
    change g ∈ (b.gates.push ⟨op, ins⟩).toList at hg
    rw [Array.toList_push, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact b.fan g hg
    · exact ⟨hop, hlen⟩
  back := by
    intro j hj i hi
    change j < (b.gates.push ⟨op, ins⟩).toList.length at hj
    change i ∈ ((b.gates.push ⟨op, ins⟩).toList.getD j ⟨GateOp.or, []⟩).inputs at hi
    rw [Array.toList_push] at hj hi
    by_cases hj' : j < b.gates.toList.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact b.back j hj' i hi
    · have he : j = b.gates.toList.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      simpa [Builder.size] using hins i hi

/-- Append one allowed gate and certify both the new wire and the preservation of old wires. -/
def addGate (b : Builder n) (op : GateOp) (ins : List ℕ)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : ins.length ≤ 2) (hins : ∀ i ∈ ins, i < n + b.size) :
    Result b 1 (fun x => op.eval (ins.map (b.read x))) :=
  let c := b.push op ins hop hlen hins
  have hs : c.size = b.size + 1 := by simp [c, Builder.push, Builder.size]
  ⟨c, ⟨[⟨op, ins⟩], Array.toList_push⟩, hs.le,
    ⟨n + b.size, by omega, fun x hx => by
      change ((b.gates.push ⟨op, ins⟩).toList.foldl evalGate x).getD (n + b.size) false = _
      rw [Array.toList_push, List.foldl_append, List.foldl_cons, List.foldl_nil]
      let w := b.gates.toList.foldl evalGate x
      change (w ++ [op.eval (ins.map fun i => w.getD i false)]).getD (n + b.size) false = _
      have hw : w.length = n + b.size := by
        simp only [w, fold_length, hx, Array.length_toList, Builder.size]
      rw [← hw, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      rfl⟩⟩

@[simp] theorem addGate_size (b : Builder n) (op : GateOp) (ins : List ℕ) (hop hlen hins) :
    (addGate b op ins hop hlen hins).next.size = b.size + 1 := by
  simp [addGate, Builder.push, Builder.size]

@[simp] theorem addGate_index (b : Builder n) (op : GateOp) (ins : List ℕ) (hop hlen hins) :
    (addGate b op ins hop hlen hins).wire.index = n + b.size := rfl

variable {b : Builder n} {f g : List Bool → Bool}

def mkFalse (b : Builder n) : Result b 1 (fun _ => false) :=
  addGate b .or [] (by simp) (by simp) (by simp)

def mkTrue (b : Builder n) : Result b 1 (fun _ => true) :=
  addGate b .and [] (by simp) (by simp) (by simp)

def mkNot (w : Wire b f) : Result b 1 (fun x => !(f x)) :=
  (addGate b .not [w.index] (by simp) (by simp)
    (by simpa using w.bound)).relabel fun x hx => by
      change (!(b.read x w.index)) = !(f x)
      rw [w.eval_eq x hx]

private theorem binary_bound (u : Wire b f) (v : Wire b g) :
    ∀ i ∈ [u.index, v.index], i < n + b.size := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact u.bound
  · exact v.bound

def mkAnd (u : Wire b f) (v : Wire b g) : Result b 1 (fun x => f x && g x) :=
  (addGate b .and [u.index, v.index] (by simp) (by simp) (binary_bound u v)).relabel fun x hx => by
    simp [GateOp.eval, u.eval_eq x hx, v.eval_eq x hx]

def mkOr (u : Wire b f) (v : Wire b g) : Result b 1 (fun x => f x || g x) :=
  (addGate b .or [u.index, v.index] (by simp) (by simp) (binary_bound u v)).relabel fun x hx => by
    simp [GateOp.eval, u.eval_eq x hx, v.eval_eq x hx]

def mkXor (u : Wire b f) (v : Wire b g) : Result b 4 (fun x => Bool.xor (f x) (g x)) :=
  let p := mkOr u v
  let q := mkAnd (u.lift p.extension) (v.lift p.extension)
  let r := mkNot q.wire
  let s := mkAnd (p.wire.lift (q.extension.trans r.extension)) r.wire
  (((p.seq q).seq r).seq s).relabel fun x _ => by cases f x <;> cases g x <;> rfl

/-- Boolean expressions over a caller-chosen set of wire leaves. -/
inductive Expr (α : Type*) where
  | var : α → Expr α
  | bit : Bool → Expr α
  | not : Expr α → Expr α
  | and : Expr α → Expr α → Expr α
  | or : Expr α → Expr α → Expr α
  | xor : Expr α → Expr α → Expr α

namespace Expr

variable {α : Type*}

def eval (env : α → Bool) : Expr α → Bool
  | .var a => env a
  | .bit t => t
  | .not e => !(e.eval env)
  | .and l r => l.eval env && r.eval env
  | .or l r => l.eval env || r.eval env
  | .xor l r => Bool.xor (l.eval env) (r.eval env)

def cost : Expr α → ℕ
  | .var _ => 0
  | .bit _ => 1
  | .not e => e.cost + 1
  | .and l r | .or l r => l.cost + r.cost + 1
  | .xor l r => l.cost + r.cost + 4

private def compileFrom {σ : α → List Bool → Bool} {base : Builder n}
    (env : ∀ i, Wire base (σ i)) :
    (e : Expr α) → {b : Builder n} → Extends base b →
      Result b e.cost (fun x => e.eval (fun i => σ i x))
  | .var i, _, h => Advance.pure ((env i).lift h)
  | .bit false, b, _ => mkFalse b
  | .bit true, b, _ => mkTrue b
  | .not e, _, h =>
    let p := compileFrom env e h
    p.seq (mkNot p.wire)
  | .and l r, _, h =>
    let p := compileFrom env l h
    let q := compileFrom env r (h.trans p.extension)
    (p.seq q).seq (mkAnd (p.wire.lift q.extension) q.wire)
  | .or l r, _, h =>
    let p := compileFrom env l h
    let q := compileFrom env r (h.trans p.extension)
    (p.seq q).seq (mkOr (p.wire.lift q.extension) q.wire)
  | .xor l r, _, h =>
    let p := compileFrom env l h
    let q := compileFrom env r (h.trans p.extension)
    (p.seq q).seq (mkXor (p.wire.lift q.extension) q.wire)

/-- Compile an expression from certified leaves; repeated references to a leaf share its wire. -/
def compile {σ : α → List Bool → Bool} (e : Expr α) {b : Builder n}
    (env : ∀ i, Wire b (σ i)) : Result b e.cost (fun x => e.eval (fun i => σ i x)) :=
  compileFrom env e (Extends.refl b)

end Expr

end CircuitBackend

namespace L25838
open CircuitBackend
open Signature

private def rowExpr (rc : Bool) : Expr (ℕ ⊕ Fin 3) :=
  let p (i : ℕ) := Expr.var (Sum.inl i)
  let x (i : Fin 3) := Expr.var (Sum.inr i)
  let m1 := Expr.xor (.xor (.xor (p 1) (p 2)) (p 3)) (x 1)
  let m2 := Expr.xor (.xor (.xor (p 2) (p 3)) (p 4)) (x 2)
  .xor (.xor (.xor (.xor (.xor (p 1) (p 2)) (x 0)) (.and (.not m1) m2)) (p 2)) (.bit rc)

private def colExpr (cc : Bool) : Expr (ℕ ⊕ Fin 3) :=
  let p (i : ℕ) := Expr.var (Sum.inl i)
  let y (i : Fin 3) := Expr.var (Sum.inr i)
  let m1 := Expr.xor (.xor (.xor (p 1) (p 3)) (p 5)) (y 1)
  let m2 := Expr.xor (.xor (.xor (p 2) (p 4)) (p 6)) (y 2)
  .xor (.xor (.xor (.xor (.xor (p 2) (p 4)) (y 0)) (.and (.not m1) m2)) (p 1)) (.bit cc)

private def checkExpr (cc : Bool) : Expr (ℕ ⊕ Fin 3) :=
  .not (.xor (.var (Sum.inl 0)) (colExpr cc))

private lemma row_cost (rc : Bool) : (rowExpr rc).cost ≤ 50 := by cases rc <;> decide
private lemma col_cost (cc : Bool) : (colExpr cc).cost ≤ 50 := by cases cc <;> decide
private lemma check_cost (cc : Bool) : (checkExpr cc).cost ≤ 54 := by cases cc <;> decide

private lemma row_eval {k : ℕ} (u rc : ZMod k → F) (i : ℕ) (prev : ℕ → F) :
    (rowExpr (bit (rc (KeyFlags.pos k (i-2))))).eval
      (Sum.elim (fun j => bit (prev (i-j))) (fun j => bit (u (KeyFlags.pos k (i-2) + (j.val : ZMod k))))) =
      bit (KeyFlags.rowBit u rc i prev) := by
  simp [rowExpr, KeyFlags.rowBit, Expr.eval, bit_add, bit_mul, show bit 1 = true from rfl]

private lemma col_eval {k : ℕ} (v cc : ZMod k → F) (i : ℕ) (prev : ℕ → F) :
    (colExpr (bit (cc (KeyFlags.pos k (i-5))))).eval
      (Sum.elim (fun j => bit (prev (i-j))) (fun j => bit (v (KeyFlags.pos k (i-5) + (j.val : ZMod k))))) =
      bit (KeyFlags.colBit v cc i prev) := by
  simp [colExpr, KeyFlags.colBit, Expr.eval, bit_add, bit_mul, show bit 1 = true from rfl]

private lemma check_eval {k : ℕ} (v cc : ZMod k → F) (i : ℕ) (prev : ℕ → F) :
    (checkExpr (bit (cc (KeyFlags.pos k (i-5))))).eval
      (Sum.elim (fun j => bit (prev (i-j))) (fun j => bit (v (KeyFlags.pos k (i-5) + (j.val : ZMod k))))) =
      decide (prev i + KeyFlags.colBit v cc i prev = 0) := by
  simp only [checkExpr, Expr.eval, Sum.elim_inl, Nat.sub_zero]
  change (!xor (bit (prev i)) ((colExpr _).eval _)) = _
  rw [col_eval, ← bit_add]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact zero_bit _
end L25838

namespace L25838
open CircuitBackend
open scoped Classical
open Signature

private def xWire {k h : ℕ} [NeZero k] (hk : h ≤ k) {b : Builder (2*h)}
    (z : Wire b (fun _ => false)) (s : ZMod k) : Wire b (fun l => bit (repX hk (inputSig h l) s)) := by
  by_cases hs : k-h ≤ s.val
  · let i : Fin (2*h) := ⟨s.val-(k-h), by have := ZMod.val_lt s; omega⟩
    exact (b.input i).congr (fun l _ => by simp [repX, hs, inputSig, i, bit_from])
  · exact z.congr (fun _ _ => by simp [repX, hs]; rfl)

private def yWire {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h ≤ k) {b : Builder (2*h)}
    (z : Wire b (fun _ => false)) (s : ZMod k) : Wire b (fun l => bit (repY hh hk (inputSig h l) s)) := by
  by_cases h0 : s.val = 0
  · exact (b.input ⟨h, by omega⟩).congr (fun l _ => by simp [repY, h0, inputSig, bit_from])
  by_cases h1 : s.val = 1
  · exact (b.input ⟨h+(h-1), by omega⟩).congr (fun l _ => by simp [repY, h0, h1, inputSig, bit_from])
  by_cases hs : k-h+2 ≤ s.val
  · let i : Fin (2*h) := ⟨h+(s.val-(k-h+1)), by have := ZMod.val_lt s; omega⟩
    exact (b.input i).congr (fun l _ => by simp [repY, h0, h1, hs, inputSig, i, bit_from])
  · exact z.congr (fun _ _ => by simp [repY, h0, h1, hs]; rfl)

variable {k h : ℕ} [NeZero k]

private def getX (hk : h ≤ k) (l : List Bool) := repX hk (inputSig h l)
private def getY (hh : 5 ≤ h) (hk : h ≤ k) (l : List Bool) := repY hh hk (inputSig h l)

private def keyFn (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F) (seed : KeyFlags.Seed)
    (l : List Bool) := KeyFlags.keyBit h (getX hk l) rc (getY hh hk l) cc seed

private structure KeyState (K : List Bool → ℕ → F) (i : ℕ) (b : Builder (2*h)) where
  zero : Wire b (fun _ => false)
  keys : ∀ j : Fin i, Wire b (fun l => bit (K l j.val))

private def prevWire {K : List Bool → ℕ → F} {i : ℕ} {b : Builder (2*h)}
    (st : KeyState K i b) (j : ℕ) : Wire b (fun l => bit (if j < i then K l j else 0)) := by
  by_cases hj : j < i
  · exact (st.keys ⟨j,hj⟩).congr (fun _ _ => by simp [hj])
  · exact st.zero.congr (fun _ _ => by simp [hj]; rfl)

private lemma sumEnv {α β γ δ : Type*} (a : α → γ → δ) (b : β → γ → δ) (l : γ) :
    (fun r => (Sum.elim a b r) l) =
      Sum.elim (fun i => a i l) (fun i => b i l) := by
  funext r; cases r <;> rfl

set_option maxHeartbeats 1000000 in
private def pivot (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F) (seed : KeyFlags.Seed)
    (i : Fin (h+7)) (b : Builder (2*h)) (st : KeyState (keyFn hh hk rc cc seed) i.val b) :
    Result b 50 (fun l => bit (keyFn hh hk rc cc seed l i.val)) := by
  let K := keyFn hh hk rc cc seed
  let j := i.val
  have hi : j < h+7 := i.isLt
  by_cases hseed : j < 4
  · let e : Expr (ℕ ⊕ Fin 3) := .bit (bit (seed ⟨j,hseed⟩))
    let r := e.compile (fun _ => st.zero)
    refine (r.relabel (g := fun l => bit (K l j)) (fun l _ => ?_)).weaken (by change 1 ≤ 50; decide)
    change bit (seed ⟨j,hseed⟩) = bit (K l j)
    exact congrArg bit (KeyFlags.keyBit_seed _ _ _ _ _ ⟨j,hseed⟩).symm
  · by_cases hrow : j < h+4
    · let s := KeyFlags.pos k (j-2)
      let env : ∀ r : ℕ ⊕ Fin 3, Wire b (r.elim
          (fun d l => bit (if j-d < j then K l (j-d) else 0))
          (fun t l => bit (getX hk l (s+(t.val : ZMod k))))) :=
        fun r => match r with
          | .inl d => prevWire st (j-d)
          | .inr t => xWire hk st.zero (s+(t.val : ZMod k))
      let r := (rowExpr (bit (rc s))).compile env
      refine (r.relabel (g := fun l => bit (K l j)) (fun l _ => ?_)).weaken (row_cost (bit (rc s)))
      rw [sumEnv, row_eval (getX hk l) rc j (fun d => if d < j then K l d else 0)]
      apply congrArg bit
      symm
      change KeyFlags.keyBit h (getX hk l) rc (getY hh hk l) cc seed j = _
      conv_lhs => rw [KeyFlags.keyBit]
      simp only [dite_eq_right hseed, ite_eq_left hrow]
      congr 1
    · let s := KeyFlags.pos k (j-5)
      let env : ∀ r : ℕ ⊕ Fin 3, Wire b (r.elim
          (fun d l => bit (if j-d < j then K l (j-d) else 0))
          (fun t l => bit (getY hh hk l (s+(t.val : ZMod k))))) :=
        fun r => match r with
          | .inl d => prevWire st (j-d)
          | .inr t => yWire hh hk st.zero (s+(t.val : ZMod k))
      let r := (colExpr (bit (cc s))).compile env
      refine (r.relabel (g := fun l => bit (K l j)) (fun l _ => ?_)).weaken (col_cost (bit (cc s)))
      rw [sumEnv, col_eval (getY hh hk l) cc j (fun d => if d < j then K l d else 0)]
      apply congrArg bit
      symm
      change KeyFlags.keyBit h (getX hk l) rc (getY hh hk l) cc seed j = _
      conv_lhs => rw [KeyFlags.keyBit]
      simp only [dite_eq_right hseed, ite_eq_right hrow, ite_eq_left hi]
      congr 1

private def buildKeys (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F) (seed : KeyFlags.Seed)
    (b : Builder (2*h)) (z : Wire b (fun _ => false)) :
    Advance b ((h+7)*50) (KeyState (keyFn hh hk rc cc seed) (h+7)) :=
  Advance.loop (h+7) 50 (fun i c st => by
    let r := pivot hh hk rc cc seed i c st
    exact r.replace ⟨st.zero.lift r.extension, fun j => by
      by_cases hj : j.val < i.val
      · exact (st.keys ⟨j,hj⟩).lift r.extension
      · have he : j.val = i.val := by have := j.isLt; omega
        exact r.wire.congr (fun _ _ => by rw [he])⟩) b ⟨z, fun j => Fin.elim0 j⟩

private def colPass (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F) (seed : KeyFlags.Seed)
    (l : List Bool) (t : ℕ) : Prop :=
  let K := keyFn hh hk rc cc seed l
  K (t+7) + KeyFlags.colBit (getY hh hk l) cc (t+7) K = 0

private noncomputable def prefixPass (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F)
    (seed : KeyFlags.Seed) (t : ℕ) (l : List Bool) : Bool := by
  classical exact decide (∀ j < t, colPass hh hk rc cc seed l j)

set_option maxHeartbeats 600000 in
private noncomputable def checkWire (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F) (seed : KeyFlags.Seed)
    (t : Fin h) {b : Builder (2*h)} (st : KeyState (keyFn hh hk rc cc seed) (h+7) b) :
    Result b 54 (fun l => decide (colPass hh hk rc cc seed l t.val)) := by
  let K := keyFn hh hk rc cc seed
  let j := t.val+7
  let s := KeyFlags.pos k (j-5)
  have hj : j < h+7 := by have := t.isLt; omega
  let env : ∀ r : ℕ ⊕ Fin 3, Wire b (r.elim
      (fun d l => bit (K l (j-d))) (fun i l => bit (getY hh hk l (s+(i.val : ZMod k))))) :=
    fun r => match r with
      | .inl d => st.keys ⟨j-d, by omega⟩
      | .inr i => yWire hh hk st.zero (s+(i.val : ZMod k))
  let r := (checkExpr (bit (cc s))).compile env
  refine (r.relabel (g := fun l => decide (colPass hh hk rc cc seed l t.val)) (fun l _ => ?_)).weaken
    (check_cost (bit (cc s)))
  rw [sumEnv]
  rw [check_eval (getY hh hk l) cc j (K l)]
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq, decide_eq_true_eq]
  rfl

private noncomputable def buildFlag (hh : 5 ≤ h) (hk : h ≤ k) (rc cc : ZMod k → F)
    (seed : KeyFlags.Seed) (b : Builder (2*h)) (z : Wire b (fun _ => false)) :
    Result b ((h+7)*50+1+h*55) (prefixPass hh hk rc cc seed h) := by
  classical
  let keys := buildKeys hh hk rc cc seed b z
  let init := (mkTrue keys.next).relabel (g := prefixPass hh hk rc cc seed 0) (fun l _ => by simp [prefixPass])
  let r := Advance.loop h 55 (S := fun t c => KeyState (keyFn hh hk rc cc seed) (h+7) c ×
      Wire c (prefixPass hh hk rc cc seed t)) (fun t c st => by
    let q := checkWire hh hk rc cc seed t st.1
    let a := mkAnd (st.2.lift q.extension) q.wire
    let ra := q.seq (a.relabel (g := prefixPass hh hk rc cc seed (t.val+1)) (fun l _ => by
      apply Bool.eq_iff_iff.mpr
      rw [Bool.and_eq_true]
      simp only [prefixPass, decide_eq_true_eq]
      constructor
      · rintro ⟨hp, ht⟩ j hj
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hl | he
        · exact hp _ hl
        · simpa [he] using ht
      · intro hp
        exact ⟨fun j hj => hp j (by omega), hp _ (by omega)⟩))
    exact ra.replace ⟨⟨st.1.zero.lift ra.extension, fun j => (st.1.keys j).lift ra.extension⟩,ra.wire⟩)
    init.next ⟨⟨keys.value.zero.lift init.extension, fun j => (keys.value.keys j).lift init.extension⟩,init.wire⟩
  exact ((keys.seq init).seq r).map (fun _ p => p.2)

end L25838

namespace L25838
open CircuitBackend

private def binVal (p : Fin 5 → Bool) : ℕ := ∑ i : Fin 5, if p i then 2^i.val else 0

private def carryExpr : ℕ → Expr (Option (Fin 5))
  | 0 => .var none
  | i+1 => .and (carryExpr i) (.var (some (Fin.ofNat 5 i)))

private def bumpExpr (i : Fin 5) : Expr (Option (Fin 5)) :=
  .xor (.var (some i)) (carryExpr i.val)

private def bump (b : Bool) (p : Fin 5 → Bool) (i : Fin 5) : Bool :=
  (bumpExpr i).eval (fun r => r.elim b p)

private lemma bump_correct : ∀ (b : Bool) (p : Fin 5 → Bool), binVal p < 31 →
    binVal (bump b p) = binVal p + b.toNat := by decide

private lemma bump_cost (i : Fin 5) : (bumpExpr i).cost ≤ 8 := by
  fin_cases i <;> decide

private def nonzeroExpr : Expr (Fin 5) :=
  .or (.or (.or (.or (.var 0) (.var 1)) (.var 2)) (.var 3)) (.var 4)

private lemma nonzero_correct : ∀ p : Fin 5 → Bool, nonzeroExpr.eval p = true ↔ 0 < binVal p := by decide

end L25838

namespace L25838
open CircuitBackend
open scoped Classical
open Signature

private noncomputable def seeds : Fin 16 ≃ KeyFlags.Seed :=
  (finCongr (by simp [KeyFlags.Seed, Fintype.card_fun, ZMod.card] : 16 = Fintype.card KeyFlags.Seed)).trans
    (Fintype.equivFin KeyFlags.Seed).symm

private noncomputable def seedAt (i : ℕ) : KeyFlags.Seed := seeds (Fin.ofNat 16 i)

private noncomputable def countPrefix {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h ≤ k)
    (rc cc : ZMod k → F) (t : ℕ) (l : List Bool) : ℕ :=
  ∑ i ∈ Finset.range t, (prefixPass hh hk rc cc (seedAt i) h l).toNat

private lemma countPrefix_le {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h ≤ k)
    (rc cc : ZMod k → F) (t : ℕ) (l : List Bool) : countPrefix hh hk rc cc t l ≤ t := by
  unfold countPrefix
  calc
    _ ≤ ∑ _i ∈ Finset.range t, 1 := Finset.sum_le_sum (fun i _ => by cases prefixPass hh hk rc cc (seedAt i) h l <;> decide)
    _ = t := by simp

private structure Digits {n : ℕ} (f : List Bool → ℕ) (b : Builder n) where
  values : List Bool → Fin 5 → Bool
  wires : ∀ i, Wire b (fun l => values l i)
  correct : ∀ l, binVal (values l) = f l

private def liftDigits {n : ℕ} {b c : Builder n} {f : List Bool → ℕ} (d : Digits f b) (e : Extends b c) : Digits f c :=
  ⟨d.values, fun i => (d.wires i).lift e, d.correct⟩

private def plusFlag {n : ℕ} {b : Builder n} {f : List Bool → ℕ} {p : List Bool → Bool}
    (d : Digits f b) (flag : Wire b p) (bound : ∀ l, f l < 31) :
    Advance b 40 (Digits (fun l => f l + (p l).toNat)) := by
  let next (l : List Bool) := bump (p l) (d.values l)
  let r := Advance.loop 5 8
      (S := fun j c => PLift (Extends b c) × (∀ i : Fin 5, i.val < j → Wire c (fun l => next l i)))
      (fun j c st => by
        let i : Fin 5 := j
        let env : ∀ o : Option (Fin 5), Wire c (o.elim p (fun i l => d.values l i)) :=
          fun o => match o with
            | none => flag.lift st.1.down
            | some i => (d.wires i).lift st.1.down
        let q := ((bumpExpr i).compile env).relabel (g := fun l => next l i) (fun l _ => by
          unfold next bump
          congr 1
          funext a; cases a <;> rfl)
        exact (q.weaken (bump_cost i)).replace ⟨⟨st.1.down.trans q.extension⟩, fun t ht => by
          by_cases ht' : t.val < j.val
          · exact (st.2 t ht').lift q.extension
          · have he : t = i := Fin.ext (by omega)
            subst t
            exact q.wire⟩)
      b ⟨⟨Extends.refl b⟩, fun i hi => (Nat.not_lt_zero i.val hi).elim⟩
  exact r.map (fun _ st => ⟨next, fun i => st.2 i i.isLt, fun l => by
    change binVal (bump (p l) (d.values l)) = _
    rw [bump_correct _ _ (by rw [d.correct]; exact bound l), d.correct]⟩)

private def appendCount {n : ℕ} {f : List Bool → ℕ} {p : List Bool → Bool}
    {a : ℕ} {b : Builder n} (flag : Result b a p) (z : Wire b (fun _ => false))
    (d : Digits f b) (bound : ∀ l, f l < 31) (g : List Bool → ℕ)
    (hg : ∀ l, f l + (p l).toNat = g l) :
    Advance b (a+40) (fun c => Wire c (fun _ => false) × Digits g c) := by
  let a := plusFlag (liftDigits d flag.extension) flag.wire bound
  let r := flag.seq a
  exact r.replace ⟨z.lift r.extension, ⟨a.value.values,a.value.wires,fun l => (a.value.correct l).trans (hg l)⟩⟩

private noncomputable def appendOutput {n : ℕ} {f : List Bool → ℕ} {b : Builder n}
    (d : Digits f b) : Advance b 4
      (fun c => Digits f c × Wire c (fun l => decide (0 < f l))) := by
  let out := (nonzeroExpr.compile d.wires).relabel
    (g := fun l => decide (0 < f l)) (fun l _ => by
      rw [Bool.eq_iff_iff, nonzero_correct, d.correct, decide_eq_true_eq])
  exact out.replace ⟨liftDigits d out.extension,out.wire⟩

set_option maxHeartbeats 600000 in
private noncomputable def countCircuit {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h ≤ k)
    (rc cc : ZMod k → F) :
    Advance (Builder.empty (2*h)) (1+16*(((h+7)*50+1+h*55)+40)+4)
      (fun b => Digits (countPrefix hh hk rc cc 16) b ×
        Wire b (fun l => decide (0 < countPrefix hh hk rc cc 16 l))) := by
  let init := mkFalse (Builder.empty (2*h))
  let m := ((h+7)*50+1+h*55)+40
  let r := Advance.loop 16 m
      (S := fun t b => Wire b (fun _ => false) × Digits (countPrefix hh hk rc cc t) b)
      (fun t b st => by
        exact appendCount (buildFlag hh hk rc cc (seedAt t.val) b st.1) st.1 st.2
          (fun l => lt_of_le_of_lt (countPrefix_le hh hk rc cc t.val l) (by have := t.isLt; omega))
          (countPrefix hh hk rc cc (t.val+1)) (fun l => by
            simp only [countPrefix, Finset.sum_range_succ]))
      init.next ⟨init.wire, ⟨fun _ _ => false, fun _ => init.wire, by simp [binVal, countPrefix]⟩⟩
  exact (init.seq r).seq (appendOutput r.value.2)

private lemma countPrefix_card {k h : ℕ} [NeZero k] (hh : 5 ≤ h) (hk : h+7 ≤ k)
    (rc cc : ZMod k → F) (l : List Bool) : countPrefix hh (by omega) rc cc 16 l =
      (Finset.univ.filter (fun seed => KeyFlags.good h (getX (by omega : h ≤ k) l) rc
        (getY hh (by omega : h ≤ k) l) cc
        (KeyFlags.rawKey h (getX (by omega : h ≤ k) l) rc (getY hh (by omega : h ≤ k) l) cc seed))).card := by
  classical
  unfold countPrefix
  let f (seed : KeyFlags.Seed) := (prefixPass hh (by omega : h ≤ k) rc cc seed h l).toNat
  change (∑ i ∈ Finset.range 16, f (seedAt i)) = _
  rw [← Fin.sum_univ_eq_sum_range (fun i => f (seedAt i))]
  have he (i : Fin 16) : seedAt i.val = seeds i := by simp [seedAt, Fin.ofNat_eq_cast]
  simp only [he]
  rw [Equiv.sum_comp seeds f]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro seed _
  have hf := (KeyFlags.good_raw_iff_flags hk (getX (by omega : h ≤ k) l) rc
    (getY hh (by omega : h ≤ k) l) cc seed)
  unfold f prefixPass
  split
  · rename_i hp
    change (decide _).toNat = true.toNat
    apply congrArg Bool.toNat
    exact decide_eq_true (hf.mp hp)
  · rename_i hp
    change (decide _).toNat = false.toNat
    apply congrArg Bool.toNat
    exact decide_eq_false (fun hp' => hp (hf.mpr hp'))

end L25838

end PEqualNP.Outside.L_meta_25838_aux

open PEqualNP.Outside.L_meta_25838_aux in
open scoped Classical in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_25838 :
∀ (k : ℕ) [NeZero k] (h : ℕ), 5 ≤ h → h + 7 ≤ k →
  let I := ZMod k
  let W := I → ZMod 2
  let lo := k - h
  let turn := fun (dist : ℕ) (word : W) (site : I) => word (site - (dist : I))
  let mix := fun (dist : ℕ) (word : W) (site : I) =>
    word (site - (dist : I)) + word site + word (site + (dist : I))
  let chi := fun (word : W) (site : I) =>
    word site + (1 + word (site+1)) * word (site+2)
  let tested := fun site : I => lo ≤ site.val
  ∀ (rowConst colConst : W),
    let good := fun (u v key : W) =>
      let row := chi (mix 1 (turn 1 key + u)) + key + rowConst
      let col := chi (mix 2 (turn 3 key + v)) + turn 4 key + colConst
      ∀ site : I, tested site → row site = 0 ∧ col site = 0
    let signature := fun (u v : W) =>
      let x := mix 1 u
      let y := mix 2 v
      ((fun j : Fin h => x ((lo+j.val : ℕ) : I)),
       (fun j : Fin (h-1) => if j.val = 0 then y 0 else y ((lo+1+j.val : ℕ) : I)),
       x 0 + y 1)
    let count := fun (u v : W) => ((Finset.univ : Finset W).filter (good u v)).card
    let arity := 2*h
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (digit : Fin 5 → Fin (arity + C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack arity C ∧
      C.output < arity + C.size ∧ C.size ≤ 4096*(h+1) ∧
      ∀ u v : W,
        let sig := signature u v
        let input := (List.ofFn (fun i : Fin h => decide (sig.1 i = 1))) ++
          (List.ofFn (fun j : Fin (h-1) => decide (sig.2.1 j = 1))) ++ [decide (sig.2.2 = 1)]
        let answer := ∑ j : Fin 5,
          if (C.wires input).getD (digit j).val false then 2^j.val else 0
        (C.eval input = true ↔ ∃ key : W, good u v key) ∧
          answer ≤ 16 ∧ count u v = 2^(lo-7) * answer
 := by
  classical
  intro k _ h hh hk I W lo turn mix chi tested rc cc good signature count arity
  obtain ⟨b, _, hz, ⟨d, out⟩⟩ := L25838.countCircuit hh (by omega : h ≤ k) rc cc
  let C := b.circuit out.index
  let digit : Fin 5 → Fin (arity + C.size) := fun j =>
    ⟨(d.wires j).index, by simpa [arity, C] using (d.wires j).bound⟩
  refine ⟨C,digit,b.fanInTwo _,b.readsBack _,?_,?_,?_⟩
  · change out.index < 2*h + b.size
    exact out.bound
  · simp only [CircuitBackend.Builder.empty_size, zero_add] at hz
    have hs : b.size ≤ 1+16*(((h+7)*50+1+h*55)+40)+4 := hz
    rw [show C.size = b.size from b.circuit_size out.index]
    change b.size ≤ 4096*(h+1)
    apply hs.trans
    clear * - hh
    omega
  · intro u v sig input answer
    let p := Signature.signature h u v
    have hi : input = L25838.inputList p := rfl
    have hlen : input.length = 2*h := hi ▸ L25838.inputLen hh p
    have hin : L25838.inputSig h input = p := hi ▸ L25838.input_round hh p
    let N := L25838.countPrefix hh (by omega : h ≤ k) rc cc 16 input
    have ha : answer = N := by
      calc
        answer = L25838.binVal (d.values input) := by
          unfold answer L25838.binVal
          apply Finset.sum_congr rfl
          intro j _
          change (if b.read input (d.wires j).index then 2^j.val else 0) = _
          rw [(d.wires j).eval_eq input hlen]
        _ = N := d.correct input
    have heval : C.eval input = decide (0 < N) := out.eval_eq input hlen
    obtain ⟨equiv⟩ := L25838.normEquiv hh hk rc cc u v
    have hcount : Nat.card {key // good u v key} = 2^(lo-7)*N := by
      have he := Nat.card_congr equiv
      change Nat.card {key // good u v key} = Nat.card {key // KeyFlags.good h
        (L25838.repX (by omega : h ≤ k) p) rc (L25838.repY hh (by omega : h ≤ k) p) cc key} at he
      rw [he, KeyFlags.good_count hh hk]
      congr 1
      symm
      have hs := L25838.countPrefix_card hh hk rc cc input
      simpa only [N, L25838.getX, L25838.getY, hin] using hs
    refine ⟨?_,?_,?_⟩
    · rw [heval, decide_eq_true_eq]
      have hn : 0 < Nat.card {key // good u v key} ↔ ∃ key, good u v key := by
        rw [Nat.card_pos_iff]
        constructor
        · rintro ⟨⟨⟨key,hkey⟩⟩,_⟩
          exact ⟨key,hkey⟩
        · rintro ⟨key,hkey⟩
          exact ⟨⟨⟨key,hkey⟩⟩,inferInstance⟩
      rw [← hn, hcount, Nat.mul_pos_iff_of_pos_left (by positivity)]
    · rw [ha]
      exact L25838.countPrefix_le hh (by omega) rc cc 16 input
    · rw [ha, ← hcount, Nat.card_eq_fintype_card, Fintype.card_subtype]
