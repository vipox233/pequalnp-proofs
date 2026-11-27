import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25837_aux

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

lemma signature_surj {k : ℕ} [NeZero k] {h : ℕ} (hh : 5 ≤ h) (hk : h + 7 ≤ k) :
    Function.Surjective (fun nm : (ZMod k → F) × (ZMod k → F) => signature h nm.1 nm.2) := by
  rintro ⟨p1, p2, p3⟩
  set lo := k - h
  let X : ZMod k → F := fun s =>
    if hs : lo ≤ s.val then p1 ⟨s.val - lo, by have := ZMod.val_lt s; omega⟩
    else if s.val = 0 then p3
    else 0
  let Y : ZMod k → F := fun s =>
    if s.val = 0 then p2 ⟨0, by omega⟩
    else if hs : lo + 2 ≤ s.val then p2 ⟨s.val - (lo + 1), by have := ZMod.val_lt s; omega⟩
    else 0
  obtain ⟨u, hu⟩ := surj_mix1 hh hk X
  obtain ⟨v, hv⟩ := surj_mix2 hh hk Y
  refine ⟨(u, v), ?_⟩
  unfold signature
  dsimp only
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · dsimp only; funext j
    have hlt : lo + j.val < k := by have := j.isLt; omega
    have hval : ((lo + j.val : ℕ) : ZMod k).val = lo + j.val := ZMod.val_natCast_of_lt hlt
    rw [hu ((lo + j.val : ℕ) : ZMod k) (Or.inl (by rw [hval]; omega))]
    dsimp only [X]
    rw [dif_pos (by rw [hval]; omega)]
    congr 1; apply Fin.ext; dsimp only; rw [hval]; omega
  · dsimp only; funext j
    by_cases hj0 : j.val = 0
    · rw [if_pos hj0, hv 0 (Or.inr (Or.inl rfl))]
      dsimp only [Y]
      rw [if_pos ZMod.val_zero]
      congr 1; exact Fin.ext hj0.symm
    · rw [if_neg hj0]
      have hlt : lo + 1 + j.val < k := by have := j.isLt; omega
      have hval : ((lo + 1 + j.val : ℕ) : ZMod k).val = lo + 1 + j.val := ZMod.val_natCast_of_lt hlt
      rw [hv ((lo + 1 + j.val : ℕ) : ZMod k) (Or.inl (by rw [hval]; omega))]
      dsimp only [Y]
      rw [if_neg (by rw [hval]; omega), dif_pos (by rw [hval]; omega)]
      congr 1; apply Fin.ext; dsimp only; rw [hval]; omega
  · dsimp only
    rw [hu 0 (Or.inr (Or.inl rfl)), hv 1 (Or.inr (Or.inr rfl))]
    dsimp only [X, Y]
    have h1val : (1 : ZMod k).val = 1 := val_one_zmod (by omega)
    have h0lt : ¬ (lo ≤ (0 : ZMod k).val) := by rw [ZMod.val_zero]; omega
    have h1ne0 : (1 : ZMod k).val ≠ 0 := by rw [h1val]; omega
    have h1lt : ¬ (lo + 2 ≤ (1 : ZMod k).val) := by rw [h1val]; omega
    rw [dif_neg h0lt, if_pos ZMod.val_zero, if_neg h1ne0, dif_neg h1lt, add_zero]

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

end PEqualNP.Outside.L_meta_25837_aux

theorem PEqualNP.Outside.L_meta_25837 :
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
        let lifts := fun (a b d : W) => ∀ u v key : W,
          good u v key ↔ good (u+a) (v+b) (key+d)
        let signature := fun (u v : W) =>
          let x := mix 1 u
          let y := mix 2 v
          ((fun j : Fin h => x ((lo+j.val : ℕ) : I)),
           (fun j : Fin (h-1) => if j.val = 0 then y 0 else y ((lo+1+j.val : ℕ) : I)),
           x 0 + y 1)
        Function.Surjective (fun nm : W × W => signature nm.1 nm.2) ∧
          ∀ u v u' v' : W,
            let num := Nat.card {offset : W // lifts (u'+u) (v'+v) offset}
            (signature u v = signature u' v' → num = 2^(lo-7)) ∧
            (signature u v ≠ signature u' v' → num = 0) := by
  intro k _ h hh hk I W lo turn mix chi tested rowConst colConst good lifts signature
  exact ⟨PEqualNP.Outside.L_meta_25837_aux.signature_surj hh hk,
         fun u v u' v' => PEqualNP.Outside.L_meta_25837_aux.card_lifts hh hk rowConst colConst u v u' v'⟩
