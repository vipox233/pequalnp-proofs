import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32574_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

abbrev F2 := ZMod 2

def b2z (b : Bool) : F2 := if b then 1 else 0

@[simp] lemma b2z_false : b2z false = 0 := rfl
@[simp] lemma b2z_true : b2z true = 1 := rfl

lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> rfl

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> rfl

lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> rfl

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp_all [b2z]

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma f2_sub_eq_add (x y : F2) : x - y = x + y := by
  fin_cases x <;> fin_cases y <;> rfl

lemma foldl_xor_b2z {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    b2z (l.foldl (fun acc x => xor acc (f x)) init) =
      b2z init + (l.map (fun x => b2z (f x))).sum := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, b2z_xor]
    ring

lemma finRange_sum_b2z (n : ℕ) (f : Fin n → Bool) :
    b2z ((List.finRange n).foldl (fun acc j => xor acc (f j)) false) =
      ∑ j : Fin n, b2z (f j) := by
  rw [foldl_xor_b2z, b2z_false, zero_add]
  have h1 : (List.finRange n).map (fun x => b2z (f x)) = List.ofFn (fun x : Fin n => b2z (f x)) := by
    apply List.ext_getElem <;> simp
  rw [h1, List.sum_ofFn]

lemma range_sum_b2z (n : ℕ) (f : ℕ → Bool) :
    b2z ((List.range n).foldl (fun acc i => xor acc (f i)) false) =
      ∑ i : Fin n, b2z (f i.val) := by
  rw [foldl_xor_b2z, b2z_false, zero_add]
  have h1 : (List.range n).map (fun i => b2z (f i)) = List.ofFn (fun i : Fin n => b2z (f i.val)) := by
    apply List.ext_getElem <;> simp
  rw [h1, List.sum_ofFn]

def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def stateFn (k r : ℕ) (col : Bool) (w u : ℕ) (c : Fin r → Fin (2 ^ k)) : ℕ :=
  let g := if col then 2 else 1
  (List.finRange r).foldl (fun x j =>
    stepFn k (x ^^^ rotFn k g x ^^^ rotFn k (k - g) x) ^^^
      rotFn k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
    (rotFn k (if col then 3 else 1) w ^^^ u)

def parityFn (k mask x : ℕ) : Bool :=
  (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false

def delayFn (r : ℕ) (col : Bool) : ℕ := if col then 3 * r + 1 else 2 * r - 2
def reachFn (r : ℕ) (col : Bool) : ℕ := if col then 7 * r - 2 else 5 * r - 3

lemma rotFn_lt (k s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.pow_pos (by decide))

lemma rotFn_testBit {k : ℕ} (hk : 0 < k) (s word : ℕ) (hw : word < 2 ^ k) {i : ℕ} (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hs0 : s % k = 0
  · simp only [hs0, Nat.zero_le, decide_true, Bool.true_and, Nat.sub_zero]
    have hge : k ≤ k + i := Nat.le_add_right k i
    have hf : word.testBit (k + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) hge))
    rw [hf, Bool.or_false]
    apply congrArg word.testBit
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · by_cases hsi : s % k ≤ i
    · simp only [decide_eq_true hsi, Bool.true_and]
      have hge : k ≤ k - s % k + i := by omega
      have hf : word.testBit (k - s % k + i) = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) hge))
      rw [hf, Bool.or_false]
      apply congrArg word.testBit
      have heq : i + k - s % k = (i - s % k) + k := by omega
      rw [heq, Nat.add_mod_right]
      exact (Nat.mod_eq_of_lt (by omega)).symm
    · simp only [decide_eq_false (by omega : ¬ (s % k ≤ i)), Bool.false_and, Bool.false_or]
      apply congrArg word.testBit
      have hlt : i + k - s % k < k := by omega
      have heq : k - s % k + i = i + k - s % k := by omega
      rw [heq]
      exact (Nat.mod_eq_of_lt hlt).symm

lemma foldl_stepFn_prefix (k word m : ℕ) :
    let val := (List.range m).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
    val < 2 ^ m ∧ ∀ j < m,
      val.testBit j = xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases ih with ⟨ih_lt, ih_bit⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := (List.range m).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
    set b := xor (word.testBit m) (!(word.testBit ((m + 1) % k)) && word.testBit ((m + 2) % k))
    have hb_lt : b.toNat <<< m < 2 ^ (m + 1) := by
      cases b <;> simp [Nat.shiftLeft_eq, Nat.pow_succ]
    have hprev_lt : prev < 2 ^ (m + 1) :=
      lt_of_lt_of_le ih_lt (Nat.pow_le_pow_right (by decide) (Nat.le_succ m))
    refine ⟨Nat.or_lt_two_pow hprev_lt hb_lt, ?_⟩
    intro j hj
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hjm : j = m
    · subst hjm
      have hf : prev.testBit j = false := Nat.testBit_lt_two_pow ih_lt
      rw [hf, Bool.false_or]
      simp only [le_refl, decide_true, Bool.true_and, Nat.sub_self, Nat.testBit_zero]
      by_cases hb : (word.testBit j ^^ !word.testBit ((j + 1) % k) && word.testBit ((j + 2) % k)) = true
      · simp [b, hb]
      · simp [b, hb]
    · have hjlt : j < m := by omega
      rw [ih_bit j hjlt]
      simp only [decide_eq_false (by omega : ¬ (m ≤ j)), Bool.false_and, Bool.or_false]

lemma stepFn_lt (k word : ℕ) : stepFn k word < 2 ^ k :=
  (foldl_stepFn_prefix k word k).1

lemma stepFn_testBit {k word j : ℕ} (hj : j < k) :
    (stepFn k word).testBit j =
      xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k)) :=
  (foldl_stepFn_prefix k word k).2 j hj

def statePrefix (k r : ℕ) (col : Bool) (w u : ℕ) (c : Fin r → Fin (2 ^ k)) (t : ℕ) : ℕ :=
  let g := if col then 2 else 1
  ((List.finRange r).take t).foldl (fun x j =>
    stepFn k (x ^^^ rotFn k g x ^^^ rotFn k (k - g) x) ^^^
      rotFn k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w ^^^ (c j).val)
    (rotFn k (if col then 3 else 1) w ^^^ u)

lemma statePrefix_zero (k r : ℕ) (col : Bool) (w u : ℕ) (c : Fin r → Fin (2 ^ k)) :
    statePrefix k r col w u c 0 = rotFn k (if col then 3 else 1) w ^^^ u := by
  simp [statePrefix]

lemma take_succ_finRange (r t : ℕ) (ht : t < r) :
    (List.finRange r).take (t + 1) = (List.finRange r).take t ++ [⟨t, ht⟩] := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left ht, Nat.min_eq_left (Nat.le_of_lt ht)]
  · intro i hi1 hi2
    simp only [List.length_take, List.length_finRange] at hi1
    by_cases hit : i < t
    · rw [List.getElem_append_left (by simp [List.length_take]; omega)]
      simp [List.getElem_take]
    · have hieq : i = t := by
        simp only [List.length_append, List.length_take, List.length_finRange,
          List.length_singleton] at hi2
        omega
      subst hieq
      rw [List.getElem_append_right (by simp [List.length_take])]
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt ht)]

lemma statePrefix_succ (k r : ℕ) (col : Bool) (w u : ℕ) (c : Fin r → Fin (2 ^ k))
    (t : ℕ) (ht : t < r) :
    let g := if col then 2 else 1
    let x := statePrefix k r col w u c t
    statePrefix k r col w u c (t + 1) =
      stepFn k (x ^^^ rotFn k g x ^^^ rotFn k (k - g) x) ^^^
        rotFn k (if col then 3 * (t + 1) + 1 else 2 * t) w ^^^ (c ⟨t, ht⟩).val := by
  unfold statePrefix
  rw [take_succ_finRange r t ht, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma statePrefix_eq_stateFn (k r : ℕ) (col : Bool) (w u : ℕ) (c : Fin r → Fin (2 ^ k)) :
    statePrefix k r col w u c r = stateFn k r col w u c := by
  unfold statePrefix stateFn
  rw [show (List.finRange r).take r = List.finRange r by simp]

lemma statePrefix_lt (k r : ℕ) (col : Bool) (w u : ℕ) (hu : u < 2 ^ k)
    (c : Fin r → Fin (2 ^ k)) (t : ℕ) (ht : t ≤ r) :
    statePrefix k r col w u c t < 2 ^ k := by
  induction t with
  | zero =>
    rw [statePrefix_zero]
    exact Nat.xor_lt_two_pow (rotFn_lt k _ w) hu
  | succ t ih =>
    rw [statePrefix_succ k r col w u c t ht]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k _ w)) (c ⟨t, ht⟩).isLt

lemma rot_neg_g_testBit {k g : ℕ} (hg0 : 0 < g) (hgk : g < k) {x : ℕ} (hx : x < 2 ^ k)
    {b : ℕ} (hb : b < k) :
    (rotFn k (k - g) x).testBit b = x.testBit ((b + g) % k) := by
  have hk : 0 < k := lt_trans hg0 hgk
  rw [rotFn_testBit hk (k - g) x hx hb]
  congr 1
  have hmod : (k - g) % k = k - g := Nat.mod_eq_of_lt (by omega)
  rw [hmod]
  have heq : b + k - (k - g) = b + g := by omega
  rw [heq]

lemma mod_add2_eq {k a x : ℕ} :
    (a % k + x) % k = (a + x) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma mod_add_eq {k a x y : ℕ} :
    (a % k + x + y) % k = (a + x + y) % k := by
  simp only [Nat.add_mod, Nat.mod_mod]

lemma reach_ge_17 {r : ℕ} (hr : 4 ≤ r) (col : Bool) : 17 ≤ reachFn r col := by
  cases col <;> simp [reachFn] <;> omega

lemma g_lt_k_of_reach {k r : ℕ} (hr : 4 ≤ r) (col : Bool) (hkr : reachFn r col < k) :
    (if col then 2 else 1) < k := by
  have h17 := reach_ge_17 hr col
  cases col <;> simp <;> omega

lemma mixStep_congr {k : ℕ} (col : Bool) (hk : 2 < k) {x1 x2 : ℕ} (hx1 : x1 < 2 ^ k) (hx2 : x2 < 2 ^ k)
    {a : ℕ} (ha : a < k)
    (hagree : ∀ δ ≤ 2 * (if col then 2 else 1) + 2,
      x1.testBit ((a + k - (if col then 2 else 1) + δ) % k) =
      x2.testBit ((a + k - (if col then 2 else 1) + δ) % k)) :
    (stepFn k (x1 ^^^ rotFn k (if col then 2 else 1) x1 ^^^ rotFn k (k - (if col then 2 else 1)) x1)).testBit a =
    (stepFn k (x2 ^^^ rotFn k (if col then 2 else 1) x2 ^^^ rotFn k (k - (if col then 2 else 1)) x2)).testBit a := by
  set g := if col then 2 else 1
  have hg0 : 0 < g := by cases col <;> decide
  have hgk : g < k := by cases col <;> dsimp [g] <;> omega
  have hk0 : 0 < k := by omega
  have h_y : ∀ d ≤ 2,
      let b := (a + d) % k
      (x1 ^^^ rotFn k g x1 ^^^ rotFn k (k - g) x1).testBit b =
      (x2 ^^^ rotFn k g x2 ^^^ rotFn k (k - g) x2).testBit b := by
    intro d hd b
    have hb : b < k := Nat.mod_lt _ hk0
    simp only [Nat.testBit_xor]
    rw [rotFn_testBit hk0 g x1 hx1 hb, rotFn_testBit hk0 g x2 hx2 hb,
      rot_neg_g_testBit hg0 hgk hx1 hb, rot_neg_g_testBit hg0 hgk hx2 hb]
    have h0 : x1.testBit b = x2.testBit b := by
      have h1 := hagree (g + d) (by omega)
      have heq : (a + k - g + (g + d)) % k = b := by
        have : a + k - g + (g + d) = a + d + k := by omega
        rw [this, Nat.add_mod_right]
      rwa [heq] at h1
    have h1 : x1.testBit ((b + k - g % k) % k) = x2.testBit ((b + k - g % k) % k) := by
      have h2 := hagree d (by omega)
      have hgm : g % k = g := Nat.mod_eq_of_lt hgk
      rw [hgm]
      have heq : (b + k - g) % k = (a + k - g + d) % k := by
        have hba : (a + d) % k + k - g = (a + d) % k + (k - g) := by omega
        have haa : a + k - g + d = a + d + (k - g) := by omega
        rw [hba, haa]
        exact mod_add2_eq
      rwa [heq]
    have h2 : x1.testBit ((b + g) % k) = x2.testBit ((b + g) % k) := by
      have h3 := hagree (2 * g + d) (by omega)
      have heq : (b + g) % k = (a + k - g + (2 * g + d)) % k := by
        have haa : a + k - g + (2 * g + d) = a + d + g + k := by omega
        rw [haa, Nat.add_mod_right]
        exact mod_add2_eq
      rwa [heq]
    rw [h0, h1, h2]
  rw [stepFn_testBit ha, stepFn_testBit ha]
  have hy0 := h_y 0 (by decide)
  have hy1 := h_y 1 (by decide)
  have hy2 := h_y 2 (by decide)
  have ha0 : (a + 0) % k = a := by simp [Nat.mod_eq_of_lt ha]
  rw [ha0] at hy0
  rw [hy0, hy1, hy2]

lemma statePrefix_congr {k r : ℕ} (hr : 4 ≤ r) (col : Bool) (hkr : reachFn r col < k)
    (cut p : ℕ)
    (w1 w2 u : ℕ) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hu : u < 2 ^ k)
    (c : Fin r → Fin (2 ^ k))
    (hagree : ∀ δ, 1 ≤ δ → δ ≤ reachFn r col →
      w1.testBit ((cut + p + δ) % k) = w2.testBit ((cut + p + δ) % k)) :
    ∀ t, t < r →
      let g := if col then 2 else 1
      ∀ δ ≤ (r - t) * (2 * g + 2),
        let b := (cut + p + delayFn r col + δ - (r - t) * g) % k
        (statePrefix k r col w1 u c t).testBit b =
        (statePrefix k r col w2 u c t).testBit b := by
  have h17 : 17 ≤ reachFn r col := reach_ge_17 hr col
  have hk0 : 0 < k := by omega
  have hk2 : 2 < k := by omega
  intro t
  induction t with
  | zero =>
    intro _ht g δ hδ b
    rw [statePrefix_zero, statePrefix_zero, Nat.testBit_xor, Nat.testBit_xor]
    have hb : b < k := Nat.mod_lt _ hk0
    rw [rotFn_testBit hk0 _ w1 hw1 hb, rotFn_testBit hk0 _ w2 hw2 hb]
    have hshift : (if col then 3 else 1) % k = if col then 3 else 1 := by
      apply Nat.mod_eq_of_lt
      cases col <;> simp <;> omega
    rw [hshift]
    cases col
    · simp only [Bool.false_eq_true, ↓reduceIte] at hδ ⊢
      have hg1 : g = 1 := rfl
      have hd0 : delayFn r false = 2 * r - 2 := rfl
      have hr0 : reachFn r false = 5 * r - 3 := rfl
      rw [hg1] at hδ
      set d := delayFn r false + δ - r * 1 - 1
      have hd1 : 1 ≤ d := by simp only [d, hd0]; omega
      have hd2 : d ≤ reachFn r false := by simp only [d, hd0, hr0] at hδ ⊢; omega
      have heq : (b + k - 1) % k = (cut + p + d) % k := by
        dsimp only [b]
        rw [hg1, hd0, Nat.sub_zero]
        have hsub : (cut + p + (2 * r - 2) + δ - r * 1) % k + k - 1 =
            (cut + p + (2 * r - 2) + δ - r * 1) % k + (k - 1) := by omega
        have heq2 : cut + p + (2 * r - 2) + δ - r * 1 + (k - 1) =
            cut + p + d + k := by
          simp only [d, hd0]; omega
        rw [hsub, mod_add2_eq, heq2, Nat.add_mod_right]
      rw [heq, hagree d hd1 hd2]
    · simp only [↓reduceIte] at hδ ⊢
      have hg2 : g = 2 := rfl
      have hd1 : delayFn r true = 3 * r + 1 := rfl
      have hr1 : reachFn r true = 7 * r - 2 := rfl
      rw [hg2] at hδ
      set d := delayFn r true + δ - r * 2 - 3
      have hdl : 1 ≤ d := by simp only [d, hd1]; omega
      have hdu : d ≤ reachFn r true := by simp only [d, hd1, hr1] at hδ ⊢; omega
      have heq : (b + k - 3) % k = (cut + p + d) % k := by
        dsimp only [b]
        rw [hg2, hd1, Nat.sub_zero]
        have hsub : (cut + p + (3 * r + 1) + δ - r * 2) % k + k - 3 =
            (cut + p + (3 * r + 1) + δ - r * 2) % k + (k - 3) := by omega
        have heq2 : cut + p + (3 * r + 1) + δ - r * 2 + (k - 3) =
            cut + p + d + k := by
          simp only [d, hd1]; omega
        rw [hsub, mod_add2_eq, heq2, Nat.add_mod_right]
      rw [heq, hagree d hdl hdu]
  | succ t ih =>
    intro ht g δ hδ b
    have ht0 : t < r := by omega
    rw [statePrefix_succ k r col w1 u c t ht0, statePrefix_succ k r col w2 u c t ht0]
    simp only [Nat.testBit_xor]
    have hb : b < k := Nat.mod_lt _ hk0
    have hstep :
        (stepFn k (statePrefix k r col w1 u c t ^^^
          rotFn k g (statePrefix k r col w1 u c t) ^^^
          rotFn k (k - g) (statePrefix k r col w1 u c t))).testBit b =
        (stepFn k (statePrefix k r col w2 u c t ^^^
          rotFn k g (statePrefix k r col w2 u c t) ^^^
          rotFn k (k - g) (statePrefix k r col w2 u c t))).testBit b := by
      apply mixStep_congr col hk2 (statePrefix_lt k r col w1 u hu c t (by omega))
        (statePrefix_lt k r col w2 u hu c t (by omega)) hb
      intro δ' hδ'
      have hδ1 : δ + δ' ≤ (r - t) * (2 * (if col then 2 else 1) + 2) := by
        have h1 : (r - t) * (2 * (if col then 2 else 1) + 2) =
            (r - (t + 1)) * (2 * (if col then 2 else 1) + 2) + (2 * (if col then 2 else 1) + 2) := by
          rw [show r - t = (r - (t + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
        have h2 : δ ≤ (r - (t + 1)) * (2 * (if col then 2 else 1) + 2) := hδ
        omega
      have hih := ih ht0 (δ + δ') hδ1
      have heq : (b + k - g + δ') % k =
          (cut + p + delayFn r col + (δ + δ') - (r - t) * g) % k := by
        have hge : (r - t) * g ≤ delayFn r col := by
          cases col <;> simp only [delayFn, g, Bool.false_eq_true, ↓reduceIte] <;> omega
        have hge2 : g ≤ k := by
          cases col <;> simp only [g, Bool.false_eq_true, ↓reduceIte] <;> omega
        have hsub : b + k - g + δ' = b + (k - g) + δ' := by omega
        dsimp only [b] at hsub ⊢
        rw [hsub, mod_add_eq]
        have heq_num : cut + p + delayFn r col + δ - (r - (t + 1)) * g + (k - g) + δ' =
            cut + p + delayFn r col + (δ + δ') - (r - t) * g + k := by
          have hmul : (r - t) * g = (r - (t + 1)) * g + g := by
            rw [show r - t = (r - (t + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
          omega
        rw [heq_num, Nat.add_mod_right]
      rwa [heq]
    have hrot :
        (rotFn k (if col then 3 * (t + 1) + 1 else 2 * t) w1).testBit b =
        (rotFn k (if col then 3 * (t + 1) + 1 else 2 * t) w2).testBit b := by
      rw [rotFn_testBit hk0 _ w1 hw1 hb, rotFn_testBit hk0 _ w2 hw2 hb]
      set s := if col then 3 * (t + 1) + 1 else 2 * t
      have hs_lt : s < k := by
        cases col <;> simp only [s, Bool.false_eq_true, ↓reduceIte] <;>
          simp only [reachFn, Bool.false_eq_true, ↓reduceIte] at hkr <;> omega
      rw [Nat.mod_eq_of_lt hs_lt]
      have hd_ge : (r - (t + 1)) * g + s < delayFn r col := by
        cases col <;> simp only [delayFn, s, g, Bool.false_eq_true, ↓reduceIte] <;> omega
      have hd_le : delayFn r col + δ - (r - (t + 1)) * g - s ≤ reachFn r col := by
        cases col <;> simp only [delayFn, reachFn, s, g, Bool.false_eq_true, ↓reduceIte] at hδ ⊢ <;> omega
      set d := delayFn r col + δ - (r - (t + 1)) * g - s
      have hd1 : 1 ≤ d := by omega
      have heq : (b + k - s) % k = (cut + p + d) % k := by
        dsimp only [b]
        have hsub : (cut + p + delayFn r col + δ - (r - (t + 1)) * g) % k + k - s =
            (cut + p + delayFn r col + δ - (r - (t + 1)) * g) % k + (k - s) := by omega
        have heq2 : cut + p + delayFn r col + δ - (r - (t + 1)) * g + (k - s) =
            cut + p + d + k := by omega
        rw [hsub, mod_add2_eq, heq2, Nat.add_mod_right]
      rw [heq, hagree d hd1 hd_le]
    rw [hstep, hrot]

lemma stateFn_pivot_congr {k r : ℕ} (hr : 4 ≤ r) (col : Bool) (hkr : reachFn r col < k)
    (cut p : ℕ)
    (w1 w2 u : ℕ) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hu : u < 2 ^ k)
    (c : Fin r → Fin (2 ^ k))
    (hagree : ∀ δ, 1 ≤ δ → δ ≤ reachFn r col →
      w1.testBit ((cut + p + δ) % k) = w2.testBit ((cut + p + δ) % k)) :
    let a := (cut + p + delayFn r col) % k
    xor ((stateFn k r col w1 u c).testBit a) (w1.testBit ((cut + p) % k)) =
    xor ((stateFn k r col w2 u c).testBit a) (w2.testBit ((cut + p) % k)) := by
  intro a
  have h17 : 17 ≤ reachFn r col := reach_ge_17 hr col
  have hk0 : 0 < k := by omega
  have hk2 : 2 < k := by omega
  have ha : a < k := Nat.mod_lt _ hk0
  have hrm1 : r - 1 < r := by omega
  rw [← statePrefix_eq_stateFn, ← statePrefix_eq_stateFn]
  have hr_eq : r = (r - 1) + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ r)).symm
  have hsp1 : statePrefix k r col w1 u c r = statePrefix k r col w1 u c ((r - 1) + 1) := by rw [← hr_eq]
  have hsp2 : statePrefix k r col w2 u c r = statePrefix k r col w2 u c ((r - 1) + 1) := by rw [← hr_eq]
  rw [hsp1, hsp2, statePrefix_succ k r col w1 u c (r - 1) hrm1,
    statePrefix_succ k r col w2 u c (r - 1) hrm1]
  simp only [Nat.testBit_xor]
  have hrot_eq : ∀ w, w < 2 ^ k →
      (rotFn k (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) w).testBit a =
      w.testBit ((cut + p) % k) := by
    intro w hw
    rw [rotFn_testBit hk0 _ w hw ha]
    have hs_eq : (if col then 3 * (r - 1 + 1) + 1 else 2 * (r - 1)) = delayFn r col := by
      cases col <;> simp [delayFn] <;> omega
    rw [hs_eq]
    have hdl : delayFn r col < k := by
      cases col <;> simp only [delayFn, reachFn, Bool.false_eq_true, ↓reduceIte] at hkr ⊢ <;> omega
    rw [Nat.mod_eq_of_lt hdl]
    congr 1
    dsimp only [a]
    have hsub : (cut + p + delayFn r col) % k + k - delayFn r col =
        (cut + p + delayFn r col) % k + (k - delayFn r col) := by omega
    have heq2 : cut + p + delayFn r col + (k - delayFn r col) = cut + p + k := by omega
    rw [hsub, mod_add2_eq, heq2, Nat.add_mod_right]
  rw [hrot_eq w1 hw1, hrot_eq w2 hw2]
  have hstep :
      (stepFn k (statePrefix k r col w1 u c (r - 1) ^^^
        rotFn k (if col then 2 else 1) (statePrefix k r col w1 u c (r - 1)) ^^^
        rotFn k (k - (if col then 2 else 1)) (statePrefix k r col w1 u c (r - 1)))).testBit a =
      (stepFn k (statePrefix k r col w2 u c (r - 1) ^^^
        rotFn k (if col then 2 else 1) (statePrefix k r col w2 u c (r - 1)) ^^^
        rotFn k (k - (if col then 2 else 1)) (statePrefix k r col w2 u c (r - 1)))).testBit a := by
    apply mixStep_congr col hk2 (statePrefix_lt k r col w1 u hu c (r - 1) (by omega))
      (statePrefix_lt k r col w2 u hu c (r - 1) (by omega)) ha
    intro δ hδ
    have hc := statePrefix_congr hr col hkr cut p w1 w2 u hw1 hw2 hu c hagree (r - 1) hrm1 δ (by
      rw [show r - (r - 1) = 1 by omega, Nat.one_mul]; exact hδ)
    have h1 : r - (r - 1) = 1 := by omega
    rw [h1, Nat.one_mul] at hc
    have heq : (a + k - (if col then 2 else 1) + δ) % k =
        (cut + p + delayFn r col + δ - (if col then 2 else 1)) % k := by
      have hg_lt : (if col then 2 else 1) < k := g_lt_k_of_reach hr col hkr
      have hdl_ge : (if col then 2 else 1) ≤ delayFn r col := by
        cases col <;> simp only [delayFn, Bool.false_eq_true, ↓reduceIte] <;> omega
      dsimp only [a]
      have hsub : (cut + p + delayFn r col) % k + k - (if col then 2 else 1) + δ =
          (cut + p + delayFn r col) % k + (k - (if col then 2 else 1)) + δ := by omega
      have heq2 : cut + p + delayFn r col + (k - (if col then 2 else 1)) + δ =
          cut + p + delayFn r col + δ - (if col then 2 else 1) + k := by omega
      rw [hsub, mod_add_eq, heq2, Nat.add_mod_right]
    rwa [heq]
  rw [hstep]
  cases ((stepFn k (statePrefix k r col w2 u c (r - 1) ^^^
    rotFn k (if col then 2 else 1) (statePrefix k r col w2 u c (r - 1)) ^^^
    rotFn k (k - (if col then 2 else 1)) (statePrefix k r col w2 u c (r - 1)))).testBit a) <;>
    cases ((c ⟨r - 1, hrm1⟩).val.testBit a) <;>
    cases (w1.testBit ((cut + p) % k)) <;>
    cases (w2.testBit ((cut + p) % k)) <;>
    decide

def coefFn (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut : Fin k) (col : Bool) (p : Fin k)
    (l : Fin m → Bool) : Bool :=
  (List.finRange m).foldl (fun acc j => xor acc ((l j) &&
    ((if col then B j else A j).val.testBit ((cut.val + p.val + delayFn r col) % k)))) false

def availableFn (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut i : Fin k) : Prop :=
  ∃ l : Fin m → Bool,
    (∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
      coefFn k r m A B cut col p l = false) ∧
    xor (coefFn k r m A B cut false i l) (coefFn k r m A B cut true i l) = true

def fFn (k r m : ℕ) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (w : ℕ) (j : Fin m) : Bool :=
  xor (parityFn k (A j).val (stateFn k r false w u cr))
      (parityFn k (B j).val (stateFn k r true w v cc))

def zeroBelow (k cut i w : ℕ) : ℕ :=
  (List.range k).foldl (fun acc b =>
    if (b + k - cut % k) % k ≤ i then acc else acc ||| ((w.testBit b).toNat <<< b)) 0

lemma zeroBelow_prefix (k cut i w m : ℕ) :
    let val := (List.range m).foldl (fun acc b =>
      if (b + k - cut % k) % k ≤ i then acc else acc ||| ((w.testBit b).toNat <<< b)) 0
    val < 2 ^ m ∧ ∀ b < m,
      val.testBit b = if (b + k - cut % k) % k ≤ i then false else w.testBit b := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases ih with ⟨ih_lt, ih_bit⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := (List.range m).foldl (fun acc b =>
      if (b + k - cut % k) % k ≤ i then acc else acc ||| ((w.testBit b).toNat <<< b)) 0
    by_cases hcond : (m + k - cut % k) % k ≤ i
    · simp only [hcond, ↓reduceIte]
      refine ⟨lt_of_lt_of_le ih_lt (Nat.pow_le_pow_right (by decide) (Nat.le_succ m)), ?_⟩
      intro b hb
      by_cases hbm : b = m
      · subst hbm
        simp only [hcond, ↓reduceIte]
        exact Nat.testBit_lt_two_pow ih_lt
      · have hblt : b < m := by omega
        exact ih_bit b hblt
    · simp only [hcond, ↓reduceIte]
      have hb_lt : (w.testBit m).toNat <<< m < 2 ^ (m + 1) := by
        cases (w.testBit m) <;> simp [Nat.shiftLeft_eq, Nat.pow_succ]
      have hprev_lt : prev < 2 ^ (m + 1) :=
        lt_of_lt_of_le ih_lt (Nat.pow_le_pow_right (by decide) (Nat.le_succ m))
      refine ⟨Nat.or_lt_two_pow hprev_lt hb_lt, ?_⟩
      intro b hb
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hbm : b = m
      · subst hbm
        simp only [hcond, ↓reduceIte]
        have hf : prev.testBit b = false := Nat.testBit_lt_two_pow ih_lt
        rw [hf, Bool.false_or]
        simp only [le_refl, decide_true, Bool.true_and, Nat.sub_self, Nat.testBit_zero]
        cases (w.testBit b) <;> rfl
      · have hblt : b < m := by omega
        rw [ih_bit b hblt]
        simp only [decide_eq_false (by omega : ¬ (m ≤ b)), Bool.false_and, Bool.or_false]

lemma zeroBelow_lt (k cut i w : ℕ) : zeroBelow k cut i w < 2 ^ k :=
  (zeroBelow_prefix k cut i w k).1

lemma zeroBelow_testBit {k cut i w b : ℕ} (hb : b < k) :
    (zeroBelow k cut i w).testBit b = if (b + k - cut % k) % k ≤ i then false else w.testBit b :=
  (zeroBelow_prefix k cut i w k).2 b hb

lemma zeroBelow_shift_testBit {k : ℕ} (hk : 0 < k) (cut i q w : ℕ) (hq : q < k) :
    (zeroBelow k cut i w).testBit ((cut + q) % k) =
      if q ≤ i then false else w.testBit ((cut + q) % k) := by
  have hb : (cut + q) % k < k := Nat.mod_lt _ hk
  rw [zeroBelow_testBit hb]
  have hcm : cut % k < k := Nat.mod_lt _ hk
  have heq : ((cut + q) % k + k - cut % k) % k = q := by
    have h1 : (cut + q) % k = (cut % k + q) % k := by rw [Nat.add_mod, Nat.mod_eq_of_lt hq]
    rw [h1]
    by_cases hlt : cut % k + q < k
    · rw [Nat.mod_eq_of_lt hlt]
      have h2 : cut % k + q + k - cut % k = q + k := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hq]
    · have hge : k ≤ cut % k + q := by omega
      have hlt2 : cut % k + q - k < k := by omega
      have hmod : (cut % k + q) % k = cut % k + q - k := by
        rw [← Nat.mod_eq_of_lt hlt2, ← Nat.add_mod_right (cut % k + q - k) k]
        congr 1; omega
      rw [hmod]
      have h2 : cut % k + q - k + k - cut % k = q := by omega
      rw [h2, Nat.mod_eq_of_lt hq]
  rw [heq]

lemma zeroBelow_eq_of_agree {k : ℕ} (hk : 0 < k) (cut i w1 w2 : ℕ)
    (h : ∀ q, i < q → q < k → w1.testBit ((cut + q) % k) = w2.testBit ((cut + q) % k)) :
    zeroBelow k cut i w1 = zeroBelow k cut i w2 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hbk : b < k
  · rw [zeroBelow_testBit hbk, zeroBelow_testBit hbk]
    split_ifs with hle
    · rfl
    · set q := (b + k - cut % k) % k
      have hq_lt : q < k := Nat.mod_lt _ hk
      have hq_gt : i < q := by omega
      have hcm : cut % k < k := Nat.mod_lt _ hk
      have hbe : (cut + q) % k = b := by
        dsimp only [q]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsub : b + k - cut % k = b + (k - cut % k) := by omega
        rw [hsub, ← Nat.add_assoc, show cut + b + (k - cut % k) = b + (cut + k - cut % k) by omega]
        have hck : cut = k * (cut / k) + cut % k := (Nat.div_add_mod cut k).symm
        have hdiv : cut + k - cut % k = k * (cut / k + 1) := by
          calc cut + k - cut % k = (k * (cut / k) + cut % k) + k - cut % k := by rw [← hck]
            _ = k * (cut / k) + k + cut % k - cut % k := by ring
            _ = k * (cut / k) + k := Nat.add_sub_cancel _ _
            _ = k * (cut / k + 1) := by ring
        rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbk]
      rw [← hbe]
      exact h q hq_gt hq_lt
  · have h1 : zeroBelow k cut i w1 < 2 ^ k := zeroBelow_lt k cut i w1
    have h2 : zeroBelow k cut i w2 < 2 ^ k := zeroBelow_lt k cut i w2
    have hk_le : k ≤ b := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hk_le)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hk_le))]

def shiftAddEquiv {k : ℕ} (hk : 0 < k) (s : ℕ) : Fin k ≃ Fin k where
  toFun p := ⟨(s + p.val) % k, Nat.mod_lt _ hk⟩
  invFun a := ⟨(a.val + k - s % k) % k, Nat.mod_lt _ hk⟩
  left_inv p := by
    apply Fin.ext
    dsimp only
    have hsm : s % k < k := Nat.mod_lt _ hk
    have hpm : (s + p.val) % k = (s % k + p.val) % k := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt p.isLt]
    rw [hpm]
    by_cases hlt : s % k + p.val < k
    · rw [Nat.mod_eq_of_lt hlt]
      have h1 : s % k + p.val + k - s % k = p.val + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
    · have hlt2 : s % k + p.val - k < k := by omega
      have hmod : (s % k + p.val) % k = s % k + p.val - k := by
        rw [← Nat.mod_eq_of_lt hlt2, ← Nat.add_mod_right (s % k + p.val - k) k]
        congr 1; omega
      rw [hmod]
      have h1 : s % k + p.val - k + k - s % k = p.val := by omega
      rw [h1, Nat.mod_eq_of_lt p.isLt]
  right_inv a := by
    apply Fin.ext
    dsimp only
    have hsm : s % k < k := Nat.mod_lt _ hk
    have hsub : a.val + k - s % k = a.val + (k - s % k) := by omega
    rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hck : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
    have hdiv : s + (a.val + (k - s % k)) = a.val + k * (s / k + 1) := by
      calc s + (a.val + (k - s % k)) = (k * (s / k) + s % k) + (a.val + (k - s % k)) := by rw [← hck]
        _ = a.val + (k * (s / k) + (s % k + (k - s % k))) := by ring
        _ = a.val + (k * (s / k) + k) := by rw [Nat.add_sub_of_le (le_of_lt hsm)]
        _ = a.val + k * (s / k + 1) := by ring
    rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]

lemma linear_combo_fFn {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (cut : Fin k) (l : Fin m → Bool) (w : ℕ) :
    b2z ((List.finRange m).foldl (fun acc j => xor acc (l j && fFn k r m u v cr cc A B w j)) false) =
      ∑ col : Bool, ∑ p : Fin k,
        b2z (coefFn k r m A B cut col p l) *
          b2z ((stateFn k r col w (if col then v else u) (if col then cc else cr)).testBit
            ((cut.val + p.val + delayFn r col) % k)) := by
  rw [finRange_sum_b2z]
  have hterm : ∀ j : Fin m,
      b2z (l j && fFn k r m u v cr cc A B w j) =
        b2z (l j) * (∑ i : Fin k, b2z ((A j).val.testBit i.val) * b2z ((stateFn k r false w u cr).testBit i.val)) +
        b2z (l j) * (∑ i : Fin k, b2z ((B j).val.testBit i.val) * b2z ((stateFn k r true w v cc).testBit i.val)) := by
    intro j
    rw [b2z_and]
    unfold fFn parityFn
    rw [b2z_xor, range_sum_b2z, range_sum_b2z]
    have h1 : ∀ mask x : ℕ, (∑ i : Fin k, b2z (mask.testBit i.val && x.testBit i.val)) =
        ∑ i : Fin k, b2z (mask.testBit i.val) * b2z (x.testBit i.val) := by
      intro mask x; refine Finset.sum_congr rfl fun i _ => b2z_and _ _
    rw [h1, h1]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.mul_sum]
  conv_lhs =>
    arg 1; rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; rw [Finset.sum_comm]
  conv_rhs => rw [Fintype.sum_bool, add_comm]
  congr 1
  · rw [← Equiv.sum_comp (shiftAddEquiv hk (cut.val + delayFn r false))]
    refine Finset.sum_congr rfl fun p _ => ?_
    have heq : (cut.val + delayFn r false + p.val) % k = (cut.val + p.val + delayFn r false) % k := by
      congr 1; ring
    dsimp only [shiftAddEquiv, Equiv.coe_fn_mk]
    rw [heq]
    unfold coefFn
    rw [finRange_sum_b2z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Bool.false_eq_true, ↓reduceIte, b2z_and]
    ring
  · rw [← Equiv.sum_comp (shiftAddEquiv hk (cut.val + delayFn r true))]
    refine Finset.sum_congr rfl fun p _ => ?_
    have heq : (cut.val + delayFn r true + p.val) % k = (cut.val + p.val + delayFn r true) % k := by
      congr 1; ring
    dsimp only [shiftAddEquiv, Equiv.coe_fn_mk]
    rw [heq]
    unfold coefFn
    rw [finRange_sum_b2z, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [↓reduceIte, b2z_and]
    ring

lemma available_pivot_eq {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (u v : ℕ) (hu : u < 2 ^ k) (hv : v < 2 ^ k)
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (cut i : Fin k) (l : Fin m → Bool)
    (hnull : ∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
      coefFn k r m A B cut col p l = false)
    (hpiv : xor (coefFn k r m A B cut false i l) (coefFn k r m A B cut true i l) = true)
    (w : ℕ) (hw : w < 2 ^ k) :
    let w0 := zeroBelow k cut.val i.val w
    xor ((List.finRange m).foldl (fun acc j => xor acc (l j && fFn k r m u v cr cc A B w j)) false)
        ((List.finRange m).foldl (fun acc j => xor acc (l j && fFn k r m u v cr cc A B w0 j)) false) =
      w.testBit ((cut.val + i.val) % k) := by
  intro w0
  apply b2z_inj
  rw [b2z_xor, linear_combo_fFn hk u v cr cc A B cut l w,
    linear_combo_fFn hk u v cr cc A B cut l w0]
  have hw0 : w0 < 2 ^ k := zeroBelow_lt k cut.val i.val w
  have hcol : ∀ col : Bool,
      (∑ p : Fin k, b2z (coefFn k r m A B cut col p l) *
        b2z ((stateFn k r col w (if col then v else u) (if col then cc else cr)).testBit
          ((cut.val + p.val + delayFn r col) % k))) +
      (∑ p : Fin k, b2z (coefFn k r m A B cut col p l) *
        b2z ((stateFn k r col w0 (if col then v else u) (if col then cc else cr)).testBit
          ((cut.val + p.val + delayFn r col) % k))) =
      b2z (coefFn k r m A B cut col i l) * b2z (w.testBit ((cut.val + i.val) % k)) := by
    intro col
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ p : Fin k,
        b2z (coefFn k r m A B cut col p l) *
          b2z ((stateFn k r col w (if col then v else u) (if col then cc else cr)).testBit
            ((cut.val + p.val + delayFn r col) % k)) +
        b2z (coefFn k r m A B cut col p l) *
          b2z ((stateFn k r col w0 (if col then v else u) (if col then cc else cr)).testBit
            ((cut.val + p.val + delayFn r col) % k)) =
        if p = i then b2z (coefFn k r m A B cut col i l) * b2z (w.testBit ((cut.val + i.val) % k)) else 0 := by
      intro p
      by_cases hc : coefFn k r m A B cut col p l = false
      · by_cases hpi : p = i
        · subst hpi; simp [hc]
        · simp [hc, hpi]
      · have hct : coefFn k r m A B cut col p l = true := by
          cases h : coefFn k r m A B cut col p l <;> simp_all
        have hnot : ¬ (k ≤ p.val + reachFn r col ∨ p < i) := fun hbad => by
          have := hnull col p hbad; simp_all
        have hpr : p.val + reachFn r col < k := by omega
        have hip : i ≤ p := by
          by_contra hlt
          exact hnot (Or.inr (not_le.mp hlt))
        have hkr : reachFn r col < k := by omega
        have hagree : ∀ δ, 1 ≤ δ → δ ≤ reachFn r col →
            w.testBit ((cut.val + p.val + δ) % k) = w0.testBit ((cut.val + p.val + δ) % k) := by
          intro δ hδ1 hδ2
          have hq : p.val + δ < k := by omega
          have heq : (cut.val + p.val + δ) % k = (cut.val + (p.val + δ)) % k := by congr 1; ring
          rw [heq, zeroBelow_shift_testBit hk cut.val i.val (p.val + δ) w hq]
          have hgt : ¬ (p.val + δ ≤ i.val) := by
            have : i.val ≤ p.val := hip
            omega
          simp [hgt]
        have hucol : (if col then v else u) < 2 ^ k := by cases col <;> assumption
        have hpiv_congr := stateFn_pivot_congr hr col hkr cut.val p.val w w0
          (if col then v else u) hw hw0 hucol (if col then cc else cr) hagree
        have hpiv_z := congrArg b2z hpiv_congr
        rw [b2z_xor, b2z_xor] at hpiv_z
        have hsum_eq :
            b2z ((stateFn k r col w (if col then v else u) (if col then cc else cr)).testBit
              ((cut.val + p.val + delayFn r col) % k)) +
            b2z ((stateFn k r col w0 (if col then v else u) (if col then cc else cr)).testBit
              ((cut.val + p.val + delayFn r col) % k)) =
            b2z (w.testBit ((cut.val + p.val) % k)) + b2z (w0.testBit ((cut.val + p.val) % k)) := by
          have hswap : ∀ a b c d : F2, a + c = b + d → a + b = c + d := by
            intro a b c d h
            fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> revert h <;> decide
          exact hswap _ _ _ _ hpiv_z
        rw [← mul_add, hsum_eq]
        by_cases hpi : p = i
        · subst hpi
          simp only [↓reduceIte]
          rw [zeroBelow_shift_testBit hk cut.val p.val p.val w p.isLt]
          simp [hct]
        · simp only [hpi, ↓reduceIte]
          have hgt : i.val < p.val := lt_of_le_of_ne hip (fun h => hpi (Fin.ext h.symm))
          rw [zeroBelow_shift_testBit hk cut.val i.val p.val w p.isLt]
          simp [show ¬ (p.val ≤ i.val) by omega, f2_add_self]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Fintype.sum_bool, Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hcomb :
      ((∑ p : Fin k, b2z (coefFn k r m A B cut true p l) *
        b2z ((stateFn k r true w v cc).testBit ((cut.val + p.val + delayFn r true) % k))) +
      (∑ p : Fin k, b2z (coefFn k r m A B cut false p l) *
        b2z ((stateFn k r false w u cr).testBit ((cut.val + p.val + delayFn r false) % k)))) +
      ((∑ p : Fin k, b2z (coefFn k r m A B cut true p l) *
        b2z ((stateFn k r true w0 v cc).testBit ((cut.val + p.val + delayFn r true) % k))) +
      (∑ p : Fin k, b2z (coefFn k r m A B cut false p l) *
        b2z ((stateFn k r false w0 u cr).testBit ((cut.val + p.val + delayFn r false) % k)))) =
      ((∑ p : Fin k, b2z (coefFn k r m A B cut false p l) *
        b2z ((stateFn k r false w u cr).testBit ((cut.val + p.val + delayFn r false) % k))) +
      (∑ p : Fin k, b2z (coefFn k r m A B cut false p l) *
        b2z ((stateFn k r false w0 u cr).testBit ((cut.val + p.val + delayFn r false) % k)))) +
      ((∑ p : Fin k, b2z (coefFn k r m A B cut true p l) *
        b2z ((stateFn k r true w v cc).testBit ((cut.val + p.val + delayFn r true) % k))) +
      (∑ p : Fin k, b2z (coefFn k r m A B cut true p l) *
        b2z ((stateFn k r true w0 v cc).testBit ((cut.val + p.val + delayFn r true) % k)))) := by ring
  rw [hcomb]
  have hf := hcol false
  have ht := hcol true
  simp only [Bool.false_eq_true, ↓reduceIte] at hf ht
  rw [hf, ht, ← add_mul, ← b2z_xor, hpiv, b2z_true, one_mul]

abbrev Basis (m : ℕ) := Fin m → Fin m → Bool

def initBasis (m : ℕ) : Basis m := fun a b => decide (a = b)

def dotBool {m : ℕ} (r v : Fin m → Bool) : Bool :=
  (List.finRange m).foldl (fun acc j => xor acc (r j && v j)) false

lemma dotBool_b2z {m : ℕ} (r v : Fin m → Bool) :
    b2z (dotBool r v) = ∑ j : Fin m, b2z (r j) * b2z (v j) := by
  unfold dotBool
  rw [finRange_sum_b2z]
  refine Finset.sum_congr rfl fun j _ => b2z_and _ _

def prefScanAux {m : ℕ} (d : Fin m → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => prefScanAux d n || (if h : n < m then d ⟨n, h⟩ else false)

lemma prefScanAux_spec {m : ℕ} (d : Fin m → Bool) :
    ∀ n ≤ m, prefScanAux d n = true ↔ ∃ c' : Fin m, c'.val < n ∧ d c' = true := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [prefScanAux]
  | succ n ih =>
    intro hn
    have hn' : n < m := by omega
    simp only [prefScanAux, hn', ↓reduceDIte, Bool.or_eq_true]
    rw [ih (by omega)]
    constructor
    · rintro (⟨c', hc1, hc2⟩ | hd)
      · exact ⟨c', Nat.lt_succ_of_lt hc1, hc2⟩
      · exact ⟨⟨n, hn'⟩, Nat.lt_succ_self n, hd⟩
    · rintro ⟨c', hc1, hc2⟩
      by_cases hcn : c'.val < n
      · exact Or.inl ⟨c', hcn, hc2⟩
      · have hceq : c' = ⟨n, hn'⟩ := Fin.ext (by dsimp only; omega)
        subst hceq
        exact Or.inr hc2

def nullStep {m : ℕ} (B : Basis m) (r : Fin m → Bool) : Basis m :=
  let d : Fin m → Bool := fun c => dotBool r (B c)
  let pref : Fin m → Bool := fun c => prefScanAux d c.val
  let isPiv : Fin m → Bool := fun c => d c && !pref c
  let pivVec : Fin m → Bool := fun j =>
    (List.finRange m).foldl (fun acc c => xor acc (isPiv c && B c j)) false
  fun c j => (!isPiv c) && xor (B c j) (d c && pref c && pivVec j)

def SpanEq {m : ℕ} (S : Set (Fin m → F2)) (B : Basis m) : Prop :=
  ∀ x : Fin m → F2, x ∈ S ↔ ∃ α : Fin m → F2, x = fun j => ∑ c : Fin m, α c * b2z (B c j)

lemma spanEq_initBasis (m : ℕ) : SpanEq (Set.univ : Set (Fin m → F2)) (initBasis m) := by
  intro x
  simp only [Set.mem_univ, true_iff]
  refine ⟨x, ?_⟩
  ext j
  have hterm : ∀ c : Fin m, x c * b2z (initBasis m c j) = if c = j then x j else 0 := by
    intro c
    by_cases hcj : c = j
    · subst hcj; simp [initBasis]
    · simp [initBasis, hcj]
  simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma nullStep_spec {m : ℕ} (S : Set (Fin m → F2)) (B : Basis m) (r : Fin m → Bool)
    (hS : SpanEq S B) :
    SpanEq {x ∈ S | ∑ j : Fin m, b2z (r j) * x j = 0} (nullStep B r) := by
  set d : Fin m → Bool := fun c => dotBool r (B c)
  set pref : Fin m → Bool := fun c => prefScanAux d c.val
  set isPiv : Fin m → Bool := fun c => d c && !pref c
  set pivVec : Fin m → Bool := fun j =>
    (List.finRange m).foldl (fun acc c => xor acc (isPiv c && B c j)) false
  have hnull_eq : ∀ c j, nullStep B r c j = ((!isPiv c) && xor (B c j) (d c && pref c && pivVec j)) := by
    intro c j; rfl
  by_cases hall : ∀ c : Fin m, d c = false
  · have hpref : ∀ c : Fin m, pref c = false := by
      intro c
      cases hp : pref c with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨c', _, hc'⟩ := (prefScanAux_spec d c.val (le_of_lt c.isLt)).mp hp
        rw [hall c'] at hc'
        cases hc'
    have hispiv : ∀ c : Fin m, isPiv c = false := fun c => by simp [isPiv, hall c]
    have hstep : nullStep B r = B := by
      ext c j
      rw [hnull_eq, hispiv c, hpref c, hall c]
      simp
    rw [hstep]
    intro x
    rw [Set.mem_setOf_eq, hS x]
    constructor
    · rintro ⟨⟨α, rfl⟩, _⟩
      exact ⟨α, rfl⟩
    · rintro ⟨α, rfl⟩
      refine ⟨⟨α, rfl⟩, ?_⟩
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      have h0 : ∀ c : Fin m, (∑ j : Fin m, b2z (r j) * (α c * b2z (B c j))) = 0 := by
        intro c
        calc ∑ j : Fin m, b2z (r j) * (α c * b2z (B c j))
            = α c * ∑ j : Fin m, b2z (r j) * b2z (B c j) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
          _ = α c * b2z (d c) := by rw [← dotBool_b2z]
          _ = 0 := by rw [hall c]; simp
      simp [h0]
  · push_neg at hall
    have hex : ∃ n : ℕ, ∃ h : n < m, d ⟨n, h⟩ = true := by
      rcases hall with ⟨c, hc⟩
      have hct : d c = true := by cases h : d c <;> simp_all
      exact ⟨c.val, c.isLt, hct⟩
    classical
    let pval := Nat.find hex
    have hp_spec : ∃ h : pval < m, d ⟨pval, h⟩ = true := Nat.find_spec hex
    have hp_lt : pval < m := hp_spec.1
    let p : Fin m := ⟨pval, hp_lt⟩
    have hdp : d p = true := hp_spec.2
    have hmin : ∀ c : Fin m, c < p → d c = false := by
      intro c hcp
      by_contra hne
      have hct : d c = true := by cases h : d c <;> simp_all
      have hle : pval ≤ c.val := Nat.find_min' hex ⟨c.isLt, hct⟩
      have : c.val < pval := hcp
      omega
    have hpref_iff : ∀ c : Fin m, pref c = true ↔ p < c := by
      intro c
      change prefScanAux d c.val = true ↔ p < c
      rw [prefScanAux_spec d c.val (le_of_lt c.isLt)]
      constructor
      · rintro ⟨c', hc1, hc2⟩
        have hnot : ¬ (c' < p) := fun hlt => by rw [hmin c' hlt] at hc2; cases hc2
        have hle : p.val ≤ c'.val := by
          by_contra h
          exact hnot (not_le.mp h)
        exact lt_of_le_of_lt hle hc1
      · intro hpc
        exact ⟨p, hpc, hdp⟩
    have hispiv_iff : ∀ c : Fin m, isPiv c = decide (c = p) := by
      intro c
      by_cases hcp : c = p
      · have hpf : pref p = false := by
          cases hp : pref p with
          | false => rfl
          | true => exfalso; exact (lt_irrefl p) ((hpref_iff p).mp hp)
        rw [hcp]
        simp [isPiv, hdp, hpf]
      · simp only [decide_eq_false hcp]
        by_cases hlt : c < p
        · simp [isPiv, hmin c hlt]
        · have hgt : p < c := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hcp)
          have hpt : pref c = true := (hpref_iff c).mpr hgt
          simp [isPiv, hpt]
    have hpivVec : ∀ j : Fin m, pivVec j = B p j := by
      intro j
      apply b2z_inj
      dsimp only [pivVec]
      rw [finRange_sum_b2z]
      have hterm : ∀ c : Fin m, b2z (isPiv c && B c j) = if c = p then b2z (B p j) else 0 := by
        intro c
        rw [b2z_and, hispiv_iff c]
        by_cases hcp : c = p
        · subst hcp; simp
        · simp [hcp]
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hcol_b2z : ∀ c j : Fin m,
        b2z (nullStep B r c j) =
          if c = p then 0
          else if p < c then b2z (B c j) + b2z (d c) * b2z (B p j)
          else b2z (B c j) := by
      intro c j
      rw [hnull_eq, hispiv_iff c, hpivVec j]
      by_cases hcp : c = p
      · subst hcp; simp
      · simp only [decide_eq_false hcp, Bool.not_false, Bool.true_and, hcp, ↓reduceIte]
        by_cases hpc : p < c
        · have hpt : pref c = true := (hpref_iff c).mpr hpc
          simp only [hpc, ↓reduceIte, hpt, Bool.and_true, b2z_xor, b2z_and,
            decide_false, Bool.not_false, b2z_true, one_mul]
        · have hpf : pref c = false := by
            cases hp : pref c with
            | false => rfl
            | true => exfalso; exact hpc ((hpref_iff c).mp hp)
          simp [hpc, hpf]
    have hBasis_mem : ∀ c : Fin m,
        (fun j => b2z (nullStep B r c j)) ∈ {x ∈ S | ∑ j : Fin m, b2z (r j) * x j = 0} := by
      intro c
      rw [Set.mem_setOf_eq, hS]
      constructor
      · by_cases hcp : c = p
        · refine ⟨0, ?_⟩; ext j; rw [hcol_b2z c j]; simp [hcp]
        · by_cases hpc : p < c
          · refine ⟨fun a => if a = c then 1 else if a = p then b2z (d c) else 0, ?_⟩
            ext j
            have hne : p ≠ c := ne_of_lt hpc
            have hsum : (∑ a : Fin m, (if a = c then 1 else if a = p then b2z (d c) else 0) * b2z (B a j)) =
                b2z (B c j) + b2z (d c) * b2z (B p j) := by
              have hterm : ∀ a : Fin m,
                  (if a = c then (1 : F2) else if a = p then b2z (d c) else 0) * b2z (B a j) =
                  (if a = c then b2z (B c j) else 0) + (if a = p then b2z (d c) * b2z (B p j) else 0) := by
                intro a
                by_cases hac : a = c
                · subst hac; simp [hne.symm]
                · by_cases hap : a = p
                  · subst hap; simp [hac]
                  · simp [hac, hap]
              simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
            rw [hsum, hcol_b2z c j]
            simp [hcp, hpc]
          · refine ⟨fun a => if a = c then 1 else 0, ?_⟩
            ext j
            have hterm : ∀ a : Fin m, (if a = c then (1 : F2) else 0) * b2z (B a j) =
                if a = c then b2z (B c j) else 0 := fun a => by
              split_ifs with h
              · subst h; simp
              · simp
            simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hcol_b2z c j, hcp, hpc, ↓reduceIte]
      · simp_rw [hcol_b2z c]
        by_cases hcp : c = p
        · simp [hcp]
        · by_cases hpc : p < c
          · simp only [hcp, ↓reduceIte, hpc, mul_add, Finset.sum_add_distrib]
            have hd_c : ∑ j : Fin m, b2z (r j) * b2z (B c j) = b2z (d c) := (dotBool_b2z r (B c)).symm
            have hd_p : ∑ j : Fin m, b2z (r j) * (b2z (d c) * b2z (B p j)) = b2z (d c) * b2z (d p) := by
              calc ∑ j : Fin m, b2z (r j) * (b2z (d c) * b2z (B p j))
                  = b2z (d c) * ∑ j : Fin m, b2z (r j) * b2z (B p j) := by
                      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
                _ = b2z (d c) * b2z (d p) := by rw [← dotBool_b2z]
            rw [hd_c, hd_p, hdp, b2z_true, mul_one, f2_add_self]
          · simp only [hcp, ↓reduceIte, hpc]
            have hlt : c < p := lt_of_le_of_ne (not_lt.mp hpc) hcp
            rw [← dotBool_b2z]
            change b2z (d c) = 0
            rw [hmin c hlt, b2z_false]
    intro x
    constructor
    · rintro ⟨hxS, hrx⟩
      obtain ⟨α, rfl⟩ := (hS x).mp hxS
      have hsum0 : ∑ c : Fin m, α c * b2z (d c) = 0 := by
        calc ∑ c : Fin m, α c * b2z (d c)
            = ∑ c : Fin m, α c * ∑ j : Fin m, b2z (r j) * b2z (B c j) := by
                refine Finset.sum_congr rfl fun c _ => ?_; rw [dotBool_b2z]
          _ = ∑ c : Fin m, ∑ j : Fin m, b2z (r j) * (α c * b2z (B c j)) := by
                refine Finset.sum_congr rfl fun c _ => ?_
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j : Fin m, b2z (r j) * ∑ c : Fin m, α c * b2z (B c j) := by
                rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
          _ = 0 := hrx
      have hαp : α p = ∑ c : Fin m, (if p < c then α c * b2z (d c) else 0) := by
        have hsplit : ∑ c : Fin m, α c * b2z (d c) =
            α p * b2z (d p) + ∑ c : Fin m, if c = p then 0 else α c * b2z (d c) := by
          have := Finset.add_sum_erase Finset.univ (fun c : Fin m => α c * b2z (d c)) (Finset.mem_univ p)
          rw [← this]
          congr 1
          have herase : Finset.univ.erase p = Finset.univ.filter (· ≠ p) := by
            ext c; simp [Finset.mem_erase]
          rw [herase, Finset.sum_filter]
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases hcp : c = p <;> simp [hcp]
        rw [hsplit, hdp, b2z_true, mul_one] at hsum0
        have hrem : (∑ c : Fin m, if c = p then 0 else α c * b2z (d c)) =
            ∑ c : Fin m, if p < c then α c * b2z (d c) else 0 := by
          refine Finset.sum_congr rfl fun c _ => ?_
          by_cases hcp : c = p
          · subst hcp; simp
          · by_cases hpc : p < c
            · simp [hcp, hpc]
            · have hlt : c < p := lt_of_le_of_ne (not_lt.mp hpc) hcp
              simp [hcp, hpc, show d c = false from hmin c hlt]
        rw [hrem] at hsum0
        have hadd := congrArg (· + α p) hsum0
        have h1 : α p + (∑ c : Fin m, if p < c then α c * b2z (d c) else 0) + α p =
            (α p + α p) + ∑ c : Fin m, if p < c then α c * b2z (d c) else 0 := by ring
        rw [h1, f2_add_self, zero_add, zero_add] at hadd
        exact hadd.symm
      refine ⟨fun c => if c = p then 0 else α c, ?_⟩
      ext j
      have hterm : ∀ c : Fin m, (if c = p then (0 : F2) else α c) * b2z (nullStep B r c j) =
          (if c = p then 0 else α c * b2z (B c j)) +
          (if p < c then α c * b2z (d c) else 0) * b2z (B p j) := by
        intro c
        rw [hcol_b2z c j]
        by_cases hcp : c = p
        · subst hcp; simp
        · by_cases hpc : p < c
          · simp only [hcp, ↓reduceIte, hpc]
            ring
          · simp [hcp, hpc]
      simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, ← hαp]
      have hsplit : ∑ c : Fin m, α c * b2z (B c j) =
          (∑ c : Fin m, if c = p then 0 else α c * b2z (B c j)) + α p * b2z (B p j) := by
        have := Finset.add_sum_erase Finset.univ (fun c : Fin m => α c * b2z (B c j)) (Finset.mem_univ p)
        rw [← this, add_comm]
        congr 1
        have herase : Finset.univ.erase p = Finset.univ.filter (· ≠ p) := by
          ext c; simp [Finset.mem_erase]
        rw [herase, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hcp : c = p <;> simp [hcp]
      exact hsplit
    · rintro ⟨α, rfl⟩
      have hmem : ∀ c : Fin m,
          (fun j => α c * b2z (nullStep B r c j)) ∈ {x ∈ S | ∑ j : Fin m, b2z (r j) * x j = 0} := by
        intro c
        obtain ⟨hcS, hcr⟩ := hBasis_mem c
        change (fun j => b2z (nullStep B r c j)) ∈ S at hcS
        rw [hS] at hcS
        rw [Set.mem_setOf_eq, hS]
        obtain ⟨β, hβ⟩ := hcS
        refine ⟨⟨fun a => α c * β a, ?_⟩, ?_⟩
        · ext j; have := congrFun hβ j; rw [this, Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
        · calc ∑ j : Fin m, b2z (r j) * (α c * b2z (nullStep B r c j))
              = α c * ∑ j : Fin m, b2z (r j) * b2z (nullStep B r c j) := by
                  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
            _ = α c * 0 := by rw [hcr]
            _ = 0 := mul_zero _
      have hS_add : ∀ s : Finset (Fin m),
          (fun j => ∑ c ∈ s, α c * b2z (nullStep B r c j)) ∈ {x ∈ S | ∑ j : Fin m, b2z (r j) * x j = 0} := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Set.mem_setOf_eq, hS]
          exact ⟨⟨0, by ext j; simp⟩, by simp⟩
        | @insert a s ha ih =>
          rw [Set.mem_setOf_eq, hS] at ih ⊢
          obtain ⟨⟨β, hβ⟩, hbr⟩ := ih
          have hma := hmem a
          rw [Set.mem_setOf_eq, hS] at hma
          obtain ⟨⟨γ, hγ⟩, hgr⟩ := hma
          refine ⟨⟨fun x => γ x + β x, ?_⟩, ?_⟩
          · ext j
            simp only [Finset.sum_insert ha]
            have h1 := congrFun hγ j
            have h2 := congrFun hβ j
            rw [h1, h2]
            simp_rw [add_mul, Finset.sum_add_distrib]
          · simp_rw [Finset.sum_insert ha, mul_add, Finset.sum_add_distrib, hgr, hbr, add_zero]
      have hfin := hS_add Finset.univ
      rw [Set.mem_setOf_eq, hS] at hfin
      rw [Set.mem_setOf_eq, hS]
      exact hfin

lemma foldl_nullStep_spec {m : ℕ} {α : Type*} (l : List α) (row : α → Fin m → Bool)
    (S : Set (Fin m → F2)) (B : Basis m) (hS : SpanEq S B) :
    SpanEq {x ∈ S | ∀ a ∈ l, ∑ j : Fin m, b2z (row a j) * x j = 0}
      (l.foldl (fun B' a => nullStep B' (row a)) B) := by
  induction l generalizing S B with
  | nil =>
    simp only [List.foldl_nil, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
      Set.setOf_true, Set.mem_univ, and_true]
    exact hS
  | cons a t ih =>
    simp only [List.foldl_cons]
    have h1 := nullStep_spec S B (row a) hS
    have h2 := ih {x ∈ S | ∑ j : Fin m, b2z (row a j) * x j = 0} (nullStep B (row a)) h1
    have hset : {x ∈ {x ∈ S | ∑ j : Fin m, b2z (row a j) * x j = 0} |
        ∀ b ∈ t, ∑ j : Fin m, b2z (row b j) * x j = 0} =
        {x ∈ S | ∀ b ∈ a :: t, ∑ j : Fin m, b2z (row b j) * x j = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, List.mem_cons]
      constructor
      · rintro ⟨⟨hxS, ha⟩, ht⟩
        refine ⟨hxS, ?_⟩
        rintro b (rfl | hbt)
        · exact ha
        · exact ht b hbt
      · rintro ⟨hxS, hall⟩
        exact ⟨⟨hxS, hall a (Or.inl rfl)⟩, fun b hb => hall b (Or.inr hb)⟩
    rwa [hset] at h2

def rowVec (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut : Fin k) (col : Bool) (p : Fin k) :
    Fin m → Bool :=
  fun j => (if col then B j else A j).val.testBit ((cut.val + p.val + delayFn r col) % k)

lemma coefFn_eq_dotBool (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut : Fin k)
    (col : Bool) (p : Fin k) (l : Fin m → Bool) :
    coefFn k r m A B cut col p l = dotBool l (rowVec k r m A B cut col p) := rfl

def allColP (k : ℕ) : List (Bool × Fin k) :=
  ([false, true] : List Bool).flatMap fun col => (List.finRange k).map fun p => (col, p)

def condPairs (k r : ℕ) (i : Fin k) : List (Bool × Fin k) :=
  (allColP k).filter fun cp => decide (k ≤ cp.2.val + reachFn r cp.1 ∨ cp.2 < i)

lemma mem_condPairs {k r : ℕ} (i : Fin k) (col : Bool) (p : Fin k) :
    (col, p) ∈ condPairs k r i ↔ (k ≤ p.val + reachFn r col ∨ p < i) := by
  simp only [condPairs, allColP, List.mem_filter, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨⟨col, ?_, p, rfl⟩, h⟩
    cases col <;> simp

def solveCutI (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut i : Fin k) :
    Bool × (Fin m → Bool) :=
  let B_final := (condPairs k r i).foldl
    (fun Bf cp => nullStep Bf (rowVec k r m A B cut cp.1 cp.2)) (initBasis m)
  let v : Fin m → Bool := fun j =>
    xor (rowVec k r m A B cut false i j) (rowVec k r m A B cut true i j)
  let e : Fin m → Bool := fun c => dotBool v (B_final c)
  let pref : Fin m → Bool := fun c => prefScanAux e c.val
  let first : Fin m → Bool := fun c => e c && !pref c
  let avail := (List.finRange m).any e
  let wit : Fin m → Bool := fun j =>
    (List.finRange m).foldl (fun acc c => xor acc (first c && B_final c j)) false
  (avail, wit)

lemma solveCutI_spec (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut i : Fin k) :
    ((solveCutI k r m A B cut i).1 = true ↔ availableFn k r m A B cut i) ∧
    ((solveCutI k r m A B cut i).1 = true →
      (∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
        coefFn k r m A B cut col p (solveCutI k r m A B cut i).2 = false) ∧
      xor (coefFn k r m A B cut false i (solveCutI k r m A B cut i).2)
          (coefFn k r m A B cut true i (solveCutI k r m A B cut i).2) = true) := by
  set B_final := (condPairs k r i).foldl
    (fun Bf cp => nullStep Bf (rowVec k r m A B cut cp.1 cp.2)) (initBasis m)
  set v : Fin m → Bool := fun j =>
    xor (rowVec k r m A B cut false i j) (rowVec k r m A B cut true i j)
  set e : Fin m → Bool := fun c => dotBool v (B_final c)
  set pref : Fin m → Bool := fun c => prefScanAux e c.val
  set first : Fin m → Bool := fun c => e c && !pref c
  set avail := (List.finRange m).any e
  set wit : Fin m → Bool := fun j =>
    (List.finRange m).foldl (fun acc c => xor acc (first c && B_final c j)) false
  have hS := foldl_nullStep_spec (condPairs k r i) (fun cp => rowVec k r m A B cut cp.1 cp.2)
    Set.univ (initBasis m) (spanEq_initBasis m)
  have hset : {x ∈ (Set.univ : Set (Fin m → F2)) |
      ∀ cp ∈ condPairs k r i, ∑ j : Fin m, b2z (rowVec k r m A B cut cp.1 cp.2 j) * x j = 0} =
      {x : Fin m → F2 | ∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
        ∑ j : Fin m, b2z (rowVec k r m A B cut col p j) * x j = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
    constructor
    · intro h col p hp
      exact h (col, p) ((mem_condPairs i col p).mpr hp)
    · intro h cp hcp
      exact h cp.1 cp.2 ((mem_condPairs i cp.1 cp.2).mp hcp)
  rw [hset] at hS
  have hl_null : ∀ (l : Fin m → Bool),
      (∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
        coefFn k r m A B cut col p l = false) ↔
      (fun j => b2z (l j)) ∈ {x : Fin m → F2 | ∀ (col : Bool) (p : Fin k),
        (k ≤ p.val + reachFn r col ∨ p < i) →
        ∑ j : Fin m, b2z (rowVec k r m A B cut col p j) * x j = 0} := by
    intro l
    simp only [Set.mem_setOf_eq]
    refine forall₃_congr fun col p _ => ?_
    rw [coefFn_eq_dotBool]
    constructor
    · intro h
      have h' : dotBool (rowVec k r m A B cut col p) l = false := by
        apply b2z_inj
        rw [dotBool_b2z]
        simp_rw [mul_comm (b2z (rowVec k r m A B cut col p _))]
        have hl' := congrArg b2z h
        rw [dotBool_b2z] at hl'
        rw [hl', b2z_false]
      rw [← dotBool_b2z, h', b2z_false]
    · intro h
      apply b2z_inj
      rw [dotBool_b2z, b2z_false]
      simp_rw [mul_comm (b2z (l _))]
      exact h
  have hl_piv : ∀ (l : Fin m → Bool),
      xor (coefFn k r m A B cut false i l) (coefFn k r m A B cut true i l) = true ↔
      ∑ j : Fin m, b2z (v j) * b2z (l j) = 1 := by
    intro l
    have hsum : ∑ j : Fin m, b2z (v j) * b2z (l j) =
        b2z (xor (coefFn k r m A B cut false i l) (coefFn k r m A B cut true i l)) := by
      rw [b2z_xor, coefFn_eq_dotBool, coefFn_eq_dotBool, dotBool_b2z, dotBool_b2z,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      dsimp only [v]
      rw [b2z_xor]
      ring
    rw [hsum]
    cases (xor (coefFn k r m A B cut false i l) (coefFn k r m A B cut true i l)) <;> decide
  have hav_eq : (solveCutI k r m A B cut i).1 = avail := rfl
  have hwit_eq : (solveCutI k r m A B cut i).2 = wit := rfl
  have hav_iff : avail = true ↔ ∃ c : Fin m, e c = true := by
    simp [avail]
  have hwit_ex : (∃ c : Fin m, e c = true) → ∃ p : Fin m, e p = true ∧ ∀ j : Fin m, wit j = B_final p j := by
    rintro ⟨c, hc⟩
    have hex : ∃ n : ℕ, ∃ h : n < m, e ⟨n, h⟩ = true := ⟨c.val, c.isLt, hc⟩
    classical
    let pval := Nat.find hex
    have hp_spec := Nat.find_spec hex
    let p : Fin m := ⟨pval, hp_spec.1⟩
    have hep : e p = true := hp_spec.2
    have hmin : ∀ c' : Fin m, c' < p → e c' = false := by
      intro c' hc'
      by_contra hne
      have hct : e c' = true := by cases h : e c' <;> simp_all
      have hle := Nat.find_min' hex ⟨c'.isLt, hct⟩
      have : c'.val < pval := hc'
      omega
    have hpref_iff : ∀ c' : Fin m, pref c' = true ↔ p < c' := by
      intro c'
      change prefScanAux e c'.val = true ↔ p < c'
      rw [prefScanAux_spec e c'.val (le_of_lt c'.isLt)]
      constructor
      · rintro ⟨c'', hc1, hc2⟩
        have hnot : ¬ (c'' < p) := fun hlt => by rw [hmin c'' hlt] at hc2; cases hc2
        have hle : p.val ≤ c''.val := by by_contra h; exact hnot (not_le.mp h)
        exact lt_of_le_of_lt hle hc1
      · intro hpc
        exact ⟨p, hpc, hep⟩
    have hfirst_iff : ∀ c' : Fin m, first c' = decide (c' = p) := by
      intro c'
      by_cases hcp : c' = p
      · have hpf : pref p = false := by
          cases hp : pref p with
          | false => rfl
          | true => exfalso; exact lt_irrefl p ((hpref_iff p).mp hp)
        rw [hcp]
        simp [first, hep, hpf]
      · simp only [decide_eq_false hcp]
        by_cases hlt : c' < p
        · simp [first, hmin c' hlt]
        · have hgt : p < c' := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hcp)
          simp [first, (hpref_iff c').mpr hgt]
    refine ⟨p, hep, fun j => ?_⟩
    apply b2z_inj
    dsimp only [wit]
    rw [finRange_sum_b2z]
    have hterm : ∀ c' : Fin m, b2z (first c' && B_final c' j) =
        if c' = p then b2z (B_final p j) else 0 := by
      intro c'
      rw [b2z_and, hfirst_iff c']
      by_cases hcp : c' = p
      · subst hcp; simp
      · simp [hcp]
    simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hB_eq : B_final = (condPairs k r i).foldl
      (fun Bf cp => nullStep Bf (rowVec k r m A B cut cp.1 cp.2)) (initBasis m) := rfl
  have hwit_ok : ∀ p : Fin m, e p = true → (∀ j : Fin m, wit j = B_final p j) →
      (∀ (col : Bool) (p' : Fin k), (k ≤ p'.val + reachFn r col ∨ p' < i) →
        coefFn k r m A B cut col p' wit = false) ∧
      xor (coefFn k r m A B cut false i wit) (coefFn k r m A B cut true i wit) = true := by
    intro p hep hwit_val
    refine ⟨?_, ?_⟩
    · rw [hl_null, hS]
      refine ⟨fun c' => if c' = p then 1 else 0, ?_⟩
      ext j
      rw [hwit_val j, ← hB_eq]
      have hterm : ∀ c' : Fin m, (if c' = p then (1 : F2) else 0) * b2z (B_final c' j) =
          if c' = p then b2z (B_final p j) else 0 := fun c' => by
        split_ifs with h
        · subst h; simp
        · simp
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · rw [hl_piv]
      calc ∑ j : Fin m, b2z (v j) * b2z (wit j)
          = ∑ j : Fin m, b2z (v j) * b2z (B_final p j) := by
              refine Finset.sum_congr rfl fun j _ => by rw [hwit_val j]
        _ = b2z (e p) := (dotBool_b2z v (B_final p)).symm
        _ = 1 := by rw [hep]; rfl
  have h1 : avail = true ↔ availableFn k r m A B cut i := by
    rw [hav_iff]
    constructor
    · intro hex
      obtain ⟨p, hep, hwit_val⟩ := hwit_ex hex
      exact ⟨wit, hwit_ok p hep hwit_val⟩
    · rintro ⟨l, hl1, hl2⟩
      have hl_mem := (hl_null l).mp hl1
      obtain ⟨α, hα⟩ := (hS _).mp hl_mem
      have hsum1 : ∑ c : Fin m, α c * b2z (e c) = 1 := by
        calc ∑ c : Fin m, α c * b2z (e c)
            = ∑ c : Fin m, α c * ∑ j : Fin m, b2z (v j) * b2z (B_final c j) := by
                refine Finset.sum_congr rfl fun c _ => ?_; rw [dotBool_b2z]
          _ = ∑ c : Fin m, ∑ j : Fin m, b2z (v j) * (α c * b2z (B_final c j)) := by
                refine Finset.sum_congr rfl fun c _ => ?_
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ j : Fin m, b2z (v j) * ∑ c : Fin m, α c * b2z (B_final c j) := by
                rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
          _ = ∑ j : Fin m, b2z (v j) * b2z (l j) := by
                refine Finset.sum_congr rfl fun j _ => ?_
                have h := congrFun hα j
                simp_rw [← hB_eq] at h
                rw [h]
          _ = 1 := (hl_piv l).mp hl2
      by_contra hnone
      push_neg at hnone
      have he0 : ∀ c : Fin m, e c = false := fun c => by
        cases h : e c <;> simp_all
      have hsum0 : ∑ c : Fin m, α c * b2z (e c) = 0 := by simp [he0]
      rw [hsum0] at hsum1
      exact zero_ne_one hsum1
  refine ⟨by rw [hav_eq]; exact h1, ?_⟩
  intro hav
  rw [hav_eq, hav_iff] at hav
  obtain ⟨p, hep, hwit_val⟩ := hwit_ex hav
  rw [hwit_eq]
  exact hwit_ok p hep hwit_val

def availTab (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut i : Fin k) : Bool :=
  (solveCutI k r m A B cut i).1

def witTab (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut i : Fin k) : Fin m → Bool :=
  (solveCutI k r m A B cut i).2

def cutCount (k r m : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut : Fin k) : ℕ :=
  ((List.finRange k).filter (availTab k r m A B cut)).length

def cutPass (k r m q : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut : Fin k) : Bool :=
  decide (q ≤ cutCount k r m A B cut)

def passBool (k r m q : ℕ) (A B : Fin m → Fin (2 ^ k)) : Bool :=
  (List.finRange k).any (cutPass k r m q A B)

lemma finRange_filter_length_eq_card {n : ℕ} (P : Fin n → Bool) :
    ((List.finRange n).filter P).length =
      ((Finset.univ : Finset (Fin n)).filter (fun x => P x = true)).card := by
  have h1 : (Finset.univ : Finset (Fin n)).filter (fun x => P x = true) =
      ((List.finRange n).filter P).toFinset := by
    ext x
    simp
  rw [h1, List.toFinset_card_of_nodup ((List.nodup_finRange n).filter P)]

open Classical in
open Classical in
lemma passBool_iff (k r m q : ℕ) (A B : Fin m → Fin (2 ^ k)) :
    passBool k r m q A B = true ↔
      ∃ cut : Fin k, q ≤ ((Finset.univ : Finset (Fin k)).filter (availableFn k r m A B cut)).card := by
  unfold passBool cutPass cutCount
  simp only [List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq]
  refine exists_congr fun cut => ?_
  rw [finRange_filter_length_eq_card]
  have hcard : ((Finset.univ : Finset (Fin k)).filter (fun i => availTab k r m A B cut i = true)).card =
      ((Finset.univ : Finset (Fin k)).filter (availableFn k r m A B cut)).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (solveCutI_spec k r m A B cut i).1
  rw [hcard]

def firstCut (k r m q : ℕ) (A B : Fin m → Fin (2 ^ k)) (cut : Fin k) : Bool :=
  cutPass k r m q A B cut && !prefScanAux (cutPass k r m q A B) cut.val

lemma firstCut_spec {k r m q : ℕ} (A B : Fin m → Fin (2 ^ k))
    (hp : passBool k r m q A B = true) :
    ∃ cutS : Fin k, cutPass k r m q A B cutS = true ∧
      ∀ cut : Fin k, firstCut k r m q A B cut = decide (cut = cutS) := by
  unfold passBool at hp
  simp only [List.any_eq_true, List.mem_finRange, true_and] at hp
  obtain ⟨c, hc⟩ := hp
  have hex : ∃ n : ℕ, ∃ h : n < k, cutPass k r m q A B ⟨n, h⟩ = true := ⟨c.val, c.isLt, hc⟩
  classical
  let pval := Nat.find hex
  have hp_spec := Nat.find_spec hex
  let p : Fin k := ⟨pval, hp_spec.1⟩
  have hdp : cutPass k r m q A B p = true := hp_spec.2
  have hmin : ∀ cut : Fin k, cut < p → cutPass k r m q A B cut = false := by
    intro cut hlt
    by_contra hne
    have hct : cutPass k r m q A B cut = true := by cases h : cutPass k r m q A B cut <;> simp_all
    have hle := Nat.find_min' hex ⟨cut.isLt, hct⟩
    have : cut.val < pval := hlt
    omega
  refine ⟨p, hdp, fun cut => ?_⟩
  have hpref : ∀ c' : Fin k, prefScanAux (cutPass k r m q A B) c'.val = true ↔ p < c' := by
    intro c'
    rw [prefScanAux_spec _ c'.val (le_of_lt c'.isLt)]
    constructor
    · rintro ⟨c'', hc1, hc2⟩
      have hnot : ¬ (c'' < p) := fun hlt => by rw [hmin c'' hlt] at hc2; cases hc2
      have hle : p.val ≤ c''.val := by by_contra h; exact hnot (not_le.mp h)
      exact lt_of_le_of_lt hle hc1
    · intro hpc
      exact ⟨p, hpc, hdp⟩
  by_cases hcp : cut = p
  · have hpf : prefScanAux (cutPass k r m q A B) p.val = false := by
      cases hp' : prefScanAux (cutPass k r m q A B) p.val with
      | false => rfl
      | true => exfalso; exact lt_irrefl p ((hpref p).mp hp')
    rw [hcp]
    simp [firstCut, hdp, hpf]
  · simp only [decide_eq_false hcp]
    by_cases hlt : cut < p
    · simp [firstCut, hmin cut hlt]
    · have hgt : p < cut := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hcp)
      simp [firstCut, (hpref cut).mpr hgt]

def pivSel {k : ℕ} (q : ℕ) (avail : Fin k → Bool) (i : Fin k) : Bool :=
  avail i && decide (((List.finRange k).take i.val |>.filter avail).length < q)

lemma pivSel_le_avail {k : ℕ} (q : ℕ) (avail : Fin k → Bool) (i : Fin k) :
    pivSel q avail i = true → avail i = true := by
  simp only [pivSel, Bool.and_eq_true]
  exact And.left

lemma pivSel_prefix_card {k : ℕ} (q : ℕ) (avail : Fin k → Bool) :
    ∀ t ≤ k,
      ((List.finRange k).take t |>.filter (pivSel q avail)).length =
        min q (((List.finRange k).take t |>.filter avail).length) := by
  intro t
  induction t with
  | zero =>
    intro _
    simp
  | succ t ih =>
    intro ht
    have ht0 : t < k := by omega
    rw [take_succ_finRange k t ht0, List.filter_append, List.filter_append,
      List.length_append, List.length_append]
    have hih := ih (by omega)
    rw [hih]
    set i : Fin k := ⟨t, ht0⟩
    by_cases ha : avail i = true
    · have hp_iff : pivSel q avail i = true ↔
          ((List.finRange k).take t |>.filter avail).length < q := by
        simp [pivSel, ha, i]
      by_cases hlt : ((List.finRange k).take t |>.filter avail).length < q
      · have hp : pivSel q avail i = true := hp_iff.mpr hlt
        simp [ha, hp]
        omega
      · have hp : pivSel q avail i = false := by
          cases h : pivSel q avail i with
          | false => rfl
          | true => exfalso; exact hlt (hp_iff.mp h)
        simp [ha, hp]
        omega
    · have haf : avail i = false := by cases h : avail i <;> simp_all
      have hpf : pivSel q avail i = false := by simp [pivSel, haf]
      simp [haf, hpf]

lemma pivSel_card {k : ℕ} (q : ℕ) (avail : Fin k → Bool)
    (hq : q ≤ ((List.finRange k).filter avail).length) :
    ((List.finRange k).filter (pivSel q avail)).length = q := by
  have h := pivSel_prefix_card q avail k (le_refl k)
  rw [List.take_of_length_le (by simp)] at h
  rw [h, Nat.min_eq_left hq]

def freeCountBefore {k : ℕ} (piv : Fin k → Bool) (i : Fin k) : ℕ :=
  ((List.finRange k).take i.val |>.filter (fun j => !piv j)).length

lemma take_split_filter_length {k : ℕ} (P : Fin k → Bool) :
    ∀ t ≤ k,
      ((List.finRange k).take t |>.filter P).length +
      ((List.finRange k).take t |>.filter (fun j => !P j)).length = t := by
  intro t
  induction t with
  | zero => intro _; simp
  | succ t ih =>
    intro ht
    have ht0 : t < k := by omega
    rw [take_succ_finRange k t ht0, List.filter_append, List.filter_append,
      List.length_append, List.length_append]
    have hih := ih (by omega)
    cases h : P ⟨t, ht0⟩ <;> simp [h] <;> omega

lemma freeCount_total {k q : ℕ} (piv : Fin k → Bool)
    (hp : ((List.finRange k).filter piv).length = q) :
    ((List.finRange k).filter (fun j => !piv j)).length = k - q := by
  have h := take_split_filter_length piv k (le_refl k)
  rw [List.take_of_length_le (by simp)] at h
  omega

lemma freeCountBefore_mono {k : ℕ} (piv : Fin k → Bool) {i1 i2 : Fin k}
    (hlt : i1 < i2) (hi1 : piv i1 = false) :
    freeCountBefore piv i1 < freeCountBefore piv i2 := by
  unfold freeCountBefore
  have h1 : (List.finRange k).take i1.val ++ [i1] = (List.finRange k).take (i1.val + 1) := by
    rw [take_succ_finRange k i1.val i1.isLt]
  have h2 : ∃ rest, (List.finRange k).take i2.val = (List.finRange k).take (i1.val + 1) ++ rest := by
    refine ⟨((List.finRange k).take i2.val).drop (i1.val + 1), ?_⟩
    have hpre : (List.finRange k).take (i1.val + 1) = ((List.finRange k).take i2.val).take (i1.val + 1) := by
      rw [List.take_take, Nat.min_eq_left (by exact hlt)]
    rw [hpre, List.take_append_drop]
  rcases h2 with ⟨rest, hr⟩
  rw [hr, ← h1, List.filter_append, List.filter_append, List.length_append, List.length_append]
  simp only [List.filter_cons, hi1, Bool.not_false, ↓reduceIte, List.filter_nil, List.length_singleton]
  omega

lemma freeCountBefore_lt {k q : ℕ} (piv : Fin k → Bool)
    (hp : ((List.finRange k).filter piv).length = q) {i : Fin k} (hi : piv i = false) :
    freeCountBefore piv i < k - q := by
  have htot := freeCount_total piv hp
  have h2 : ∃ rest, List.finRange k = (List.finRange k).take (i.val + 1) ++ rest := by
    refine ⟨(List.finRange k).drop (i.val + 1), (List.take_append_drop _ _).symm⟩
  rcases h2 with ⟨rest, hr⟩
  have hlen : ((List.finRange k).take (i.val + 1) |>.filter (fun j => !piv j)).length ≤
      ((List.finRange k).filter (fun j => !piv j)).length := by
    conv_rhs => rw [hr]
    rw [List.filter_append, List.length_append]
    omega
  rw [take_succ_finRange k i.val i.isLt, List.filter_append, List.length_append] at hlen
  simp only [List.filter_cons, hi, Bool.not_false, ↓reduceIte, List.filter_nil, List.length_singleton] at hlen
  change freeCountBefore piv i + 1 ≤ _ at hlen
  omega

noncomputable def freeEquiv {k q : ℕ} (piv : Fin k → Bool)
    (hp : ((List.finRange k).filter piv).length = q) :
    {i : Fin k // piv i = false} ≃ Fin (k - q) := by
  refine Equiv.ofBijective
    (fun x => ⟨freeCountBefore piv x.1, freeCountBefore_lt piv hp x.2⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)
  · intro x y hxy
    have hval : freeCountBefore piv x.1 = freeCountBefore piv y.1 := congrArg Fin.val hxy
    apply Subtype.ext
    rcases lt_trichotomy x.1 y.1 with h1 | h2 | h3
    · exfalso; have := freeCountBefore_mono piv h1 x.2; omega
    · exact h2
    · exfalso; have := freeCountBefore_mono piv h3 y.2; omega
  · have h1 : Fintype.card {i : Fin k // piv i = false} =
        ((Finset.univ : Finset (Fin k)).filter (fun i => (!piv i) = true)).card := by
      rw [Fintype.card_subtype]
      apply congrArg Finset.card
      ext i
      simp
    rw [h1, ← finRange_filter_length_eq_card, freeCount_total piv hp, Fintype.card_fin]

def zToW {k : ℕ} (hk : 0 < k) (cut : Fin k) (z : Fin k → Bool) : ℕ :=
  (List.range k).foldl (fun acc b =>
    acc ||| ((z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩).toNat <<< b)) 0

lemma zToW_prefix {k : ℕ} (hk : 0 < k) (cut : Fin k) (z : Fin k → Bool) (m : ℕ) :
    let val := (List.range m).foldl (fun acc b =>
      acc ||| ((z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩).toNat <<< b)) 0
    val < 2 ^ m ∧ ∀ b < m,
      val.testBit b = z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases ih with ⟨ih_lt, ih_bit⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set prev := (List.range m).foldl (fun acc b =>
      acc ||| ((z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩).toNat <<< b)) 0
    set bit := z ⟨(m + k - cut.val) % k, Nat.mod_lt _ hk⟩
    have hb_lt : bit.toNat <<< m < 2 ^ (m + 1) := by
      cases bit <;> simp [Nat.shiftLeft_eq, Nat.pow_succ]
    have hprev_lt : prev < 2 ^ (m + 1) :=
      lt_of_lt_of_le ih_lt (Nat.pow_le_pow_right (by decide) (Nat.le_succ m))
    refine ⟨Nat.or_lt_two_pow hprev_lt hb_lt, ?_⟩
    intro b hb
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hbm : b = m
    · subst hbm
      have hf : prev.testBit b = false := Nat.testBit_lt_two_pow ih_lt
      rw [hf, Bool.false_or]
      simp only [le_refl, decide_true, Bool.true_and, Nat.sub_self, Nat.testBit_zero]
      by_cases hbt : z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩ = true
      · simp [bit, hbt]
      · simp [bit, hbt]
    · have hblt : b < m := by omega
      rw [ih_bit b hblt]
      simp only [decide_eq_false (by omega : ¬ (m ≤ b)), Bool.false_and, Bool.or_false]

lemma zToW_lt {k : ℕ} (hk : 0 < k) (cut : Fin k) (z : Fin k → Bool) :
    zToW hk cut z < 2 ^ k :=
  (zToW_prefix hk cut z k).1

lemma zToW_testBit {k : ℕ} (hk : 0 < k) (cut : Fin k) (z : Fin k → Bool) {b : ℕ} (hb : b < k) :
    (zToW hk cut z).testBit b = z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩ :=
  (zToW_prefix hk cut z k).2 b hb

lemma zToW_shift_testBit {k : ℕ} (hk : 0 < k) (cut : Fin k) (z : Fin k → Bool) (i : Fin k) :
    (zToW hk cut z).testBit ((cut.val + i.val) % k) = z i := by
  rw [zToW_testBit hk cut z (Nat.mod_lt _ hk)]
  congr 1
  apply Fin.ext
  dsimp only
  have heq : (cut.val + i.val) % k = (cut.val % k + i.val) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]
  rw [Nat.mod_eq_of_lt cut.isLt] at heq
  rw [heq]
  by_cases hlt : cut.val + i.val < k
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : cut.val + i.val + k - cut.val = i.val + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  · have hlt2 : cut.val + i.val - k < k := by omega
    have hmod : (cut.val + i.val) % k = cut.val + i.val - k := by
      rw [← Nat.mod_eq_of_lt hlt2, ← Nat.add_mod_right (cut.val + i.val - k) k]
      congr 1; omega
    rw [hmod]
    have h1 : cut.val + i.val - k + k - cut.val = i.val := by omega
    rw [h1, Nat.mod_eq_of_lt i.isLt]

def reconstructStep {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free : Fin k → Bool)
    (s : ℕ) (z : Fin k → Bool) : Fin k → Bool :=
  if hs : s < k then
    let i : Fin k := ⟨k - 1 - s, by omega⟩
    let w0 := zToW hk cut z
    let z_piv := xor (dotBool (wit i) y) (dotBool (wit i) (fFn k r m u v cr cc A B w0))
    let z_new := if piv i then z_piv else f_free i
    fun p => if p = i then z_new else z p
  else z

def reconstructZ {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free : Fin k → Bool) : Fin k → Bool :=
  (List.range k).foldl (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z)
    (fun _ => false)

def freeAssign (k q : ℕ) (piv : Fin k → Bool) (a : Fin (k - q) → Bool) (i : Fin k) : Bool :=
  if h : freeCountBefore piv i < k - q then a ⟨freeCountBefore piv i, h⟩ else false

def reconstructW {k r m q : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (a : Fin (k - q) → Bool) : Fin (2 ^ k) :=
  ⟨zToW hk cut (reconstructZ hk u v cr cc A B y cut piv wit (freeAssign k q piv a)),
    zToW_lt hk cut _⟩

lemma reconstructPrefix_zero {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free : Fin k → Bool)
    (t : ℕ) (ht : t ≤ k) :
    let zt := (List.range t).foldl
      (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z) (fun _ => false)
    ∀ p : Fin k, p.val < k - t → zt p = false := by
  induction t with
  | zero =>
    intro _ p _
    rfl
  | succ t ih =>
    intro zt p hp
    have ht0 : t < k := by omega
    have hprev := ih (by omega) p (by omega)
    have hzt : zt = reconstructStep hk u v cr cc A B y cut piv wit f_free t
        ((List.range t).foldl (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z)
          (fun _ => false)) := by
      dsimp only [zt]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hzt]
    unfold reconstructStep
    simp only [ht0, ↓reduceDIte]
    have hne : p ≠ ⟨k - 1 - t, by omega⟩ := by
      intro heq
      have := congrArg Fin.val heq
      dsimp only at this
      omega
    simp only [hne, ↓reduceIte]
    exact hprev

lemma reconstructPrefix_stable {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free : Fin k → Bool)
    (t1 t2 : ℕ) (h12 : t1 ≤ t2) (ht2 : t2 ≤ k) :
    let z1 := (List.range t1).foldl
      (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z) (fun _ => false)
    let z2 := (List.range t2).foldl
      (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z) (fun _ => false)
    ∀ p : Fin k, k - t1 ≤ p.val → z2 p = z1 p := by
  induction t2 with
  | zero =>
    intro z1 z2 p _
    have h0 : t1 = 0 := by omega
    subst h0
    rfl
  | succ t2 ih =>
    intro z1 z2 p hp
    by_cases heq : t1 = t2 + 1
    · subst heq; rfl
    · have h12' : t1 ≤ t2 := by omega
      have hih := ih h12' (by omega) p hp
      have hz2 : z2 = reconstructStep hk u v cr cc A B y cut piv wit f_free t2
          ((List.range t2).foldl (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z)
            (fun _ => false)) := by
        dsimp only [z2]
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hz2]
      unfold reconstructStep
      have ht2lt : t2 < k := by omega
      simp only [ht2lt, ↓reduceDIte]
      have hne : p ≠ ⟨k - 1 - t2, by omega⟩ := by
        intro hpe
        have := congrArg Fin.val hpe
        dsimp only at this
        omega
      simp only [hne, ↓reduceIte]
      exact hih

lemma reconstructZ_free {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free : Fin k → Bool)
    (p : Fin k) (hp : piv p = false) :
    reconstructZ hk u v cr cc A B y cut piv wit f_free p = f_free p := by
  have ht1 : k - p.val ≤ k := Nat.sub_le k p.val
  have hstab := reconstructPrefix_stable hk u v cr cc A B y cut piv wit f_free
    (k - p.val) k ht1 (le_refl k) p (by omega)
  change reconstructZ hk u v cr cc A B y cut piv wit f_free p = _ at hstab
  rw [hstab]
  have heq : k - p.val = (k - 1 - p.val) + 1 := by have := p.isLt; omega
  rw [heq, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  unfold reconstructStep
  have hlt : k - 1 - p.val < k := by have := p.isLt; omega
  simp only [hlt, ↓reduceDIte]
  have hpeq : (⟨k - 1 - (k - 1 - p.val), by omega⟩ : Fin k) = p := by
    apply Fin.ext; dsimp only; have := p.isLt; omega
  rw [hpeq]
  simp [hp]

lemma reconstructPrefix_exact {k r m : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (u v : ℕ) (hu : u < 2 ^ k) (hv : v < 2 ^ k)
    (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool)
    (hwit : ∀ i : Fin k, piv i = true →
      (∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
        coefFn k r m A B cut col p (wit i) = false) ∧
      xor (coefFn k r m A B cut false i (wit i)) (coefFn k r m A B cut true i (wit i)) = true)
    (w : Fin (2 ^ k)) (hw_sol : ∀ j : Fin m, fFn k r m u v cr cc A B w.val j = y j)
    (f_free : Fin k → Bool)
    (hfree : ∀ i : Fin k, piv i = false → f_free i = w.val.testBit ((cut.val + i.val) % k)) :
    ∀ t ≤ k,
      let zt := (List.range t).foldl
        (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z) (fun _ => false)
      ∀ p : Fin k, k - t ≤ p.val → zt p = w.val.testBit ((cut.val + p.val) % k) := by
  intro t
  induction t with
  | zero =>
    intro _ zt p hp
    exfalso
    have := p.isLt
    omega
  | succ t ih =>
    intro ht zt p hp
    have ht0 : t < k := by omega
    set zprev := (List.range t).foldl
      (fun z s => reconstructStep hk u v cr cc A B y cut piv wit f_free s z) (fun _ => false)
    have hih := ih (by omega)
    have hzt : zt = reconstructStep hk u v cr cc A B y cut piv wit f_free t zprev := by
      dsimp only [zt]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hzt]
    unfold reconstructStep
    simp only [ht0, ↓reduceDIte]
    set i : Fin k := ⟨k - 1 - t, by omega⟩
    by_cases hpi : p = i
    · rw [hpi]
      simp only [↓reduceIte]
      by_cases hpiv : piv i = true
      · simp only [hpiv, ↓reduceIte]
        have hw0_eq : zToW hk cut zprev = zeroBelow k cut.val i.val w.val := by
          apply Nat.eq_of_testBit_eq
          intro b
          by_cases hbk : b < k
          · have hshift : ∃ q : Fin k, b = (cut.val + q.val) % k := by
              let e := shiftAddEquiv hk cut.val
              refine ⟨e.symm ⟨b, hbk⟩, ?_⟩
              have hr := e.apply_symm_apply ⟨b, hbk⟩
              exact (congrArg Fin.val hr).symm
            rcases hshift with ⟨q, rfl⟩
            rw [zToW_shift_testBit hk cut zprev q, zeroBelow_shift_testBit hk cut.val i.val q.val w.val q.isLt]
            by_cases hqi : q.val ≤ i.val
            · simp only [hqi, ↓reduceIte]
              exact reconstructPrefix_zero hk u v cr cc A B y cut piv wit f_free t (by omega) q (by dsimp [i] at hqi; omega)
            · simp only [hqi, ↓reduceIte]
              exact hih q (by dsimp [i] at hqi; omega)
          · have h1 := zToW_lt hk cut zprev
            have h2 := zeroBelow_lt k cut.val i.val w.val
            have hk_le : k ≤ b := by omega
            rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hk_le)),
                Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hk_le))]
        rw [hw0_eq]
        have hdot_y : dotBool (wit i) y =
            (List.finRange m).foldl (fun acc j => xor acc (wit i j && fFn k r m u v cr cc A B w.val j)) false := by
          unfold dotBool
          congr 1
          ext acc j
          rw [hw_sol j]
        have hdot_w0 : dotBool (wit i) (fFn k r m u v cr cc A B (zeroBelow k cut.val i.val w.val)) =
            (List.finRange m).foldl (fun acc j => xor acc (wit i j && fFn k r m u v cr cc A B (zeroBelow k cut.val i.val w.val) j)) false := rfl
        rw [hdot_y, hdot_w0]
        obtain ⟨hnull, hpiv_ok⟩ := hwit i hpiv
        exact available_pivot_eq hk hr u v hu hv cr cc A B cut i (wit i) hnull hpiv_ok w.val w.isLt
      · have hpf : piv i = false := by cases h : piv i <;> simp_all
        simp only [hpf, Bool.false_eq_true, ↓reduceIte]
        exact hfree i hpf
    · simp only [hpi, ↓reduceIte]
      have hgt : k - t ≤ p.val := by
        have hne_val : p.val ≠ i.val := fun h => hpi (Fin.ext h)
        dsimp only [i] at hne_val
        omega
      exact hih p hgt

lemma hits_le_and_eq_of_pass {k r m q : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (y : Fin m → Bool)
    (hp : passBool k r m q A B = true) :
    ∃ (cutS : Fin k),
      (∀ cut : Fin k, firstCut k r m q A B cut = decide (cut = cutS)) ∧
      ((List.finRange k).filter (pivSel q (availTab k r m A B cutS))).length = q ∧
      (Nat.card {w : Fin (2 ^ k) // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B w.val j = y j} ≤ 2 ^ (k - q)) ∧
      (Nat.card {w : Fin (2 ^ k) // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B w.val j = y j} =
        ((Finset.univ : Finset (Fin (k - q) → Bool)).filter (fun a =>
          decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
            (reconstructW hk u.val v.val cr cc A B y cutS (pivSel q (availTab k r m A B cutS)) (witTab k r m A B cutS) a).val j = y j) = true)).card) := by
  obtain ⟨cutS, hcutS, hfc_spec⟩ := firstCut_spec A B hp
  set avail := availTab k r m A B cutS
  set piv := pivSel q avail
  set wit := witTab k r m A B cutS
  have hcnt : q ≤ ((List.finRange k).filter avail).length := by
    unfold cutPass cutCount at hcutS
    exact decide_eq_true_eq.mp hcutS
  have hpiv_card : ((List.finRange k).filter piv).length = q := pivSel_card q avail hcnt
  have hwit_ok : ∀ i : Fin k, piv i = true →
      (∀ (col : Bool) (p : Fin k), (k ≤ p.val + reachFn r col ∨ p < i) →
        coefFn k r m A B cutS col p (wit i) = false) ∧
      xor (coefFn k r m A B cutS false i (wit i)) (coefFn k r m A B cutS true i (wit i)) = true := by
    intro i hi
    have hai : avail i = true := pivSel_le_avail q avail i hi
    exact (solveCutI_spec k r m A B cutS i).2 hai
  have hpiv_avail : ∀ i : Fin k, piv i = true → availableFn k r m A B cutS i := by
    intro i hi
    exact ⟨wit i, hwit_ok i hi⟩
  let recW : (Fin (k - q) → Bool) → Fin (2 ^ k) :=
    reconstructW hk u.val v.val cr cc A B y cutS piv wit
  let feq := freeEquiv piv hpiv_card
  have hrec_inj : Function.Injective recW := by
    intro a1 a2 heq
    ext d
    set x := feq.symm d
    have hx_free : piv x.1 = false := x.2
    have hbit := congrArg (fun w : Fin (2 ^ k) => w.val.testBit ((cutS.val + x.1.val) % k)) heq
    dsimp only [recW, reconstructW] at hbit
    rw [zToW_shift_testBit hk cutS _ x.1, zToW_shift_testBit hk cutS _ x.1,
      reconstructZ_free hk u.val v.val cr cc A B y cutS piv wit _ x.1 hx_free,
      reconstructZ_free hk u.val v.val cr cc A B y cutS piv wit _ x.1 hx_free] at hbit
    unfold freeAssign at hbit
    have hlt := freeCountBefore_lt piv hpiv_card hx_free
    simp only [hlt, ↓reduceDIte] at hbit
    have hd_eq : (⟨freeCountBefore piv x.1, hlt⟩ : Fin (k - q)) = d := feq.apply_symm_apply d
    rwa [hd_eq] at hbit
  have hrec_surj : ∀ w : Fin (2 ^ k),
      (∀ j : Fin m, fFn k r m u.val v.val cr cc A B w.val j = y j) →
      ∃ a : Fin (k - q) → Bool, recW a = w := by
    intro w hw_sol
    let a : Fin (k - q) → Bool := fun d => w.val.testBit ((cutS.val + (feq.symm d).1.val) % k)
    refine ⟨a, ?_⟩
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hbk : b < k
    · have hshift : ∃ p : Fin k, b = (cutS.val + p.val) % k := by
        let e := shiftAddEquiv hk cutS.val
        refine ⟨e.symm ⟨b, hbk⟩, ?_⟩
        exact (congrArg Fin.val (e.apply_symm_apply ⟨b, hbk⟩)).symm
      rcases hshift with ⟨p, rfl⟩
      dsimp only [recW, reconstructW]
      rw [zToW_shift_testBit hk cutS _ p]
      have hfree_ok : ∀ i : Fin k, piv i = false →
          freeAssign k q piv a i = w.val.testBit ((cutS.val + i.val) % k) := by
        intro i hi
        unfold freeAssign
        have hlt := freeCountBefore_lt piv hpiv_card hi
        simp only [hlt, ↓reduceDIte]
        have heq_sub : feq.symm ⟨freeCountBefore piv i, hlt⟩ = ⟨i, hi⟩ :=
          feq.symm_apply_apply ⟨i, hi⟩
        dsimp only [a]
        rw [heq_sub]
      exact reconstructPrefix_exact hk hr u.val v.val u.isLt v.isLt cr cc A B y cutS piv wit
        hwit_ok w hw_sol (freeAssign k q piv a) hfree_ok k (le_refl k) p (by simp)
    · have h1 := (recW a).isLt
      have h2 := w.isLt
      have hk_le : k ≤ b := by omega
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) hk_le)),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) hk_le))]
  have heqv : {a : Fin (k - q) → Bool // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B (recW a).val j = y j} ≃
      {w : Fin (2 ^ k) // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B w.val j = y j} := by
    refine Equiv.ofBijective (fun a => ⟨recW a.1, a.2⟩) ⟨?_, ?_⟩
    · intro a1 a2 h
      apply Subtype.ext
      exact hrec_inj (congrArg Subtype.val h)
    · rintro ⟨w, hw⟩
      obtain ⟨a, rfl⟩ := hrec_surj w hw
      exact ⟨⟨a, hw⟩, rfl⟩
  have hcard_eq : Nat.card {w : Fin (2 ^ k) // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B w.val j = y j} =
      Fintype.card {a : Fin (k - q) → Bool // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B (recW a).val j = y j} := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr heqv.symm
  refine ⟨cutS, hfc_spec, hpiv_card, ?_, ?_⟩
  · rw [hcard_eq]
    calc Fintype.card {a : Fin (k - q) → Bool // _}
        ≤ Fintype.card (Fin (k - q) → Bool) := Fintype.card_subtype_le _
      _ = 2 ^ (k - q) := by simp
  · rw [hcard_eq, Fintype.card_subtype]
    apply congrArg Finset.card
    ext a
    simp [recW, wit, piv, avail]

section CircuitBuilder

def GoodGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def GoodGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧ ∀ g ∈ gs, GoodGate g

def evalGates (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

def wireVal (gs : List Gate) (xs : List Bool) (w : ℕ) : Bool :=
  (evalGates gs xs).getD w false

def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ extra, gs2 = gs1 ++ extra

lemma extends_refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma extends_trans {gs1 gs2 gs3 : List Gate} (h1 : Extends gs1 gs2) (h2 : Extends gs2 gs3) :
    Extends gs1 gs3 := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

lemma extends_length {gs1 gs2 : List Gate} (h : Extends gs1 gs2) : gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl⟩
  simp

lemma evalGates_nil (xs : List Bool) : evalGates [] xs = xs := rfl

lemma evalGates_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    evalGates (g :: gs) xs =
      evalGates gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]) := rfl

lemma evalGates_append (gs1 gs2 : List Gate) (xs : List Bool) :
    evalGates (gs1 ++ gs2) xs = evalGates gs2 (evalGates gs1 xs) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_length (gs : List Gate) (xs : List Bool) :
    (evalGates gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp
    omega

lemma evalGates_getD_lt (gs : List Gate) (xs : List Bool) {i : ℕ} (hi : i < xs.length) :
    (evalGates gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wireVal_extends {n : ℕ} {gs1 gs2 : List Gate} (h : Extends gs1 gs2)
    {xs : List Bool} (hxs : xs.length = n) {w : ℕ} (hw : w < n + gs1.length) :
    wireVal gs2 xs w = wireVal gs1 xs w := by
  rcases h with ⟨extra, rfl⟩
  unfold wireVal
  rw [evalGates_append, evalGates_getD_lt]
  rw [evalGates_length, hxs]
  exact hw

lemma listVal_extends {n : ℕ} {gs1 gs2 : List Gate} (h : Extends gs1 gs2)
    {xs : List Bool} (hxs : xs.length = n) {ws : List ℕ} (hws : ∀ w ∈ ws, w < n + gs1.length) :
    ws.map (wireVal gs2 xs) = ws.map (wireVal gs1 xs) := by
  apply List.map_congr_left
  intro w hw
  exact wireVal_extends h hxs (hws w hw)

lemma wireVal_push {n : ℕ} (gs : List Gate) (g : Gate) {xs : List Bool} (hxs : xs.length = n) :
    wireVal (gs ++ [g]) xs (n + gs.length) =
      g.op.eval (g.inputs.map fun i => wireVal gs xs i) := by
  unfold wireVal
  rw [evalGates_append, evalGates_cons, evalGates_nil]
  have hlen : (evalGates gs xs).length = n + gs.length := by rw [evalGates_length, hxs]
  simp [List.getD_eq_getElem?_getD, ← hlen]

lemma goodGates_nil (n : ℕ) : GoodGates n [] := by
  refine ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩

lemma goodGates_push {n : ℕ} {gs : List Gate} {g : Gate} (hgs : GoodGates n gs)
    (hg : GoodGate g) (hin : ∀ i ∈ g.inputs, i < n + gs.length) :
    GoodGates n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.1 j hlt i hi
    · have hj_eq : j = gs.length := by omega
      subst hj_eq
      have hget : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgs.2 g' h
    · exact hg

lemma goodGates_fanInTwo {n : ℕ} {gs : List Gate} {out : ℕ} (h : GoodGates n gs) :
    FanInTwo ⟨gs, out⟩ := fun g hg => h.2 g hg

lemma goodGates_readsBack {n : ℕ} {gs : List Gate} {out : ℕ} (h : GoodGates n gs) :
    ReadsBack n ⟨gs, out⟩ := h.1

def gFalse (n : ℕ) (gs : List Gate) : List Gate × ℕ := (gs ++ [⟨.or, []⟩], n + gs.length)
def gTrue (n : ℕ) (gs : List Gate) : List Gate × ℕ := (gs ++ [⟨.and, []⟩], n + gs.length)
def gNot (n : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ := (gs ++ [⟨.not, [a]⟩], n + gs.length)
def gAnd (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ := (gs ++ [⟨.and, [a, b]⟩], n + gs.length)
def gOr (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ := (gs ++ [⟨.or, [a, b]⟩], n + gs.length)

def gXor (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := gOr n gs a b
  let r2 := gAnd n r1.1 a b
  let r3 := gNot n r2.1 r2.2
  gAnd n r3.1 r1.2 r3.2

def gEq (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := gXor n gs a b
  gNot n r1.1 r1.2

def gMux (n : ℕ) (gs : List Gate) (s a b : ℕ) : List Gate × ℕ :=
  let ns := gNot n gs s
  let t1 := gAnd n ns.1 s a
  let t2 := gAnd n t1.1 ns.2 b
  gOr n t2.1 t1.2 t2.2

lemma gFalse_spec {n : ℕ} {gs : List Gate} (hgs : GoodGates n gs) :
    let r := gFalse n gs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = false := by
  refine ⟨⟨[⟨.or, []⟩], rfl⟩, ?_, by simp [gFalse], by simp [gFalse], ?_⟩
  · refine goodGates_push hgs ⟨by simp, by simp⟩ (by simp)
  · intro xs hxs; simp only [gFalse]; rw [wireVal_push gs _ hxs]; simp [GateOp.eval]

lemma gTrue_spec {n : ℕ} {gs : List Gate} (hgs : GoodGates n gs) :
    let r := gTrue n gs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = true := by
  refine ⟨⟨[⟨.and, []⟩], rfl⟩, ?_, by simp [gTrue], by simp [gTrue], ?_⟩
  · refine goodGates_push hgs ⟨by simp, by simp⟩ (by simp)
  · intro xs hxs; simp only [gTrue]; rw [wireVal_push gs _ hxs]; simp [GateOp.eval]

lemma gNot_spec {n : ℕ} {gs : List Gate} {a : ℕ} (hgs : GoodGates n gs) (ha : a < n + gs.length) :
    let r := gNot n gs a
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = !(wireVal gs xs a) := by
  refine ⟨⟨[⟨.not, [a]⟩], rfl⟩, ?_, by simp [gNot], by simp [gNot], ?_⟩
  · refine goodGates_push hgs ⟨by simp, by simp⟩ ?_
    intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact ha
  · intro xs hxs; simp only [gNot]; rw [wireVal_push gs _ hxs]; simp [GateOp.eval]

lemma gAnd_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := gAnd n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = (wireVal gs xs a && wireVal gs xs b) := by
  refine ⟨⟨[⟨.and, [a, b]⟩], rfl⟩, ?_, by simp [gAnd], by simp [gAnd], ?_⟩
  · refine goodGates_push hgs ⟨by simp, by simp⟩ ?_
    intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro xs hxs; simp only [gAnd]; rw [wireVal_push gs _ hxs]; simp [GateOp.eval]

lemma gOr_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := gOr n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = (wireVal gs xs a || wireVal gs xs b) := by
  refine ⟨⟨[⟨.or, [a, b]⟩], rfl⟩, ?_, by simp [gOr], by simp [gOr], ?_⟩
  · refine goodGates_push hgs ⟨by simp, by simp⟩ ?_
    intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro xs hxs; simp only [gOr]; rw [wireVal_push gs _ hxs]; simp [GateOp.eval]

lemma gXor_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := gXor n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 4 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = xor (wireVal gs xs a) (wireVal gs xs b) := by
  dsimp only [gXor]
  have s1 := gOr_spec hgs ha hb
  have s2 := gAnd_spec s1.2.1 (lt_of_lt_of_le ha (by omega)) (lt_of_lt_of_le hb (by omega))
  have s3 := gNot_spec s2.2.1 s2.2.2.2.1
  have s4 := gAnd_spec s3.2.1 (lt_of_lt_of_le s1.2.2.2.1 (by omega)) s3.2.2.2.1
  refine ⟨extends_trans s1.1 (extends_trans s2.1 (extends_trans s3.1 s4.1)),
    s4.2.1, by omega, s4.2.2.2.1, fun xs hxs => ?_⟩
  rw [s4.2.2.2.2 xs hxs, s3.2.2.2.2 xs hxs, s2.2.2.2.2 xs hxs,
    wireVal_extends (extends_trans s2.1 s3.1) hxs s1.2.2.2.1,
    s1.2.2.2.2 xs hxs, wireVal_extends s1.1 hxs ha, wireVal_extends s1.1 hxs hb]
  cases wireVal gs xs a <;> cases wireVal gs xs b <;> rfl

lemma gEq_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := gEq n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 5 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → wireVal r.1 xs r.2 = decide (wireVal gs xs a = wireVal gs xs b) := by
  dsimp only [gEq]
  have s1 := gXor_spec hgs ha hb
  have s2 := gNot_spec s1.2.1 s1.2.2.2.1
  refine ⟨extends_trans s1.1 s2.1, s2.2.1, by omega, s2.2.2.2.1, fun xs hxs => ?_⟩
  rw [s2.2.2.2.2 xs hxs, s1.2.2.2.2 xs hxs]
  cases wireVal gs xs a <;> cases wireVal gs xs b <;> rfl

lemma gMux_spec {n : ℕ} {gs : List Gate} {s a b : ℕ} (hgs : GoodGates n gs)
    (hs : s < n + gs.length) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := gMux n gs s a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 4 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        wireVal r.1 xs r.2 = if wireVal gs xs s then wireVal gs xs a else wireVal gs xs b := by
  dsimp only [gMux]
  have s1 := gNot_spec hgs hs
  have s2 := gAnd_spec s1.2.1 (lt_of_lt_of_le hs (by omega)) (lt_of_lt_of_le ha (by omega))
  have s3 := gAnd_spec s2.2.1 (lt_of_lt_of_le s1.2.2.2.1 (by omega)) (lt_of_lt_of_le hb (by omega))
  have s4 := gOr_spec s3.2.1 (lt_of_lt_of_le s2.2.2.2.1 (by omega)) s3.2.2.2.1
  refine ⟨extends_trans s1.1 (extends_trans s2.1 (extends_trans s3.1 s4.1)),
    s4.2.1, by omega, s4.2.2.2.1, fun xs hxs => ?_⟩
  rw [s4.2.2.2.2 xs hxs, s3.2.2.2.2 xs hxs,
    wireVal_extends s3.1 hxs s2.2.2.2.1, s2.2.2.2.2 xs hxs,
    wireVal_extends s2.1 hxs s1.2.2.2.1, s1.2.2.2.2 xs hxs,
    wireVal_extends s1.1 hxs hs, wireVal_extends s1.1 hxs ha,
    wireVal_extends (extends_trans s1.1 s2.1) hxs hb]
  cases wireVal gs xs s <;> cases wireVal gs xs a <;> cases wireVal gs xs b <;> rfl

def gDotAux (n : ℕ) (gs : List Gate) (acc : ℕ) : List (ℕ × ℕ) → List Gate × ℕ
  | [] => (gs, acc)
  | (a, b) :: rest =>
    let p := gAnd n gs a b
    let x := gXor n p.1 acc p.2
    gDotAux n x.1 x.2 rest

def gDot (n wFalse : ℕ) (gs : List Gate) (xs ys : List ℕ) : List Gate × ℕ :=
  gDotAux n gs wFalse (xs.zip ys)

lemma gDotAux_spec {n : ℕ} {gs : List Gate} {acc : ℕ} (ps : List (ℕ × ℕ))
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length)
    (hps : ∀ ab ∈ ps, ab.1 < n + gs.length ∧ ab.2 < n + gs.length) :
    let r := gDotAux n gs acc ps
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 5 * ps.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        wireVal r.1 xs r.2 = ps.foldl (fun v ab => xor v (wireVal gs xs ab.1 && wireVal gs xs ab.2)) (wireVal gs xs acc) := by
  induction ps generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gDotAux], hacc, fun xs _ => rfl⟩
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    have hab := hps (a, b) (by simp)
    have ha : a < n + gs.length := hab.1
    have hb : b < n + gs.length := hab.2
    dsimp only [gDotAux]
    have s1 := gAnd_spec hgs ha hb
    have s2 := gXor_spec s1.2.1 (lt_of_lt_of_le hacc (by omega)) s1.2.2.2.1
    have h12 : Extends gs (gXor n (gAnd n gs a b).1 acc (gAnd n gs a b).2).1 :=
      extends_trans s1.1 s2.1
    have ih' := ih s2.2.1 s2.2.2.2.1 (fun xy hxy => by
      have h := hps xy (by simp [hxy])
      have hlen1 : (gAnd n gs a b).1.length = gs.length + 1 := s1.2.2.1
      have hlen2 : (gXor n (gAnd n gs a b).1 acc (gAnd n gs a b).2).1.length = (gAnd n gs a b).1.length + 4 := s2.2.2.1
      exact ⟨lt_of_lt_of_le h.1 (by omega), lt_of_lt_of_le h.2 (by omega)⟩)
    refine ⟨extends_trans h12 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, fun xs hxs => ?_⟩
    · have hlen1 : (gAnd n gs a b).1.length = gs.length + 1 := s1.2.2.1
      have hlen2 : (gXor n (gAnd n gs a b).1 acc (gAnd n gs a b).2).1.length = (gAnd n gs a b).1.length + 4 := s2.2.2.1
      have hlen3 := ih'.2.2.1
      simp only [List.length_cons]
      omega
    · rw [ih'.2.2.2.2 xs hxs, List.foldl_cons]
      have hfold : ∀ (l : List (ℕ × ℕ)) (v : Bool),
          (∀ xy ∈ l, xy.1 < n + gs.length ∧ xy.2 < n + gs.length) →
          l.foldl (fun w xy => xor w (wireVal (gXor n (gAnd n gs a b).1 acc (gAnd n gs a b).2).1 xs xy.1 &&
            wireVal (gXor n (gAnd n gs a b).1 acc (gAnd n gs a b).2).1 xs xy.2)) v =
          l.foldl (fun w xy => xor w (wireVal gs xs xy.1 && wireVal gs xs xy.2)) v := by
        intro l v hl
        induction l generalizing v with
        | nil => rfl
        | cons xy t iht =>
          have hxy := hl xy (by simp)
          simp only [List.foldl_cons]
          rw [wireVal_extends h12 hxs hxy.1, wireVal_extends h12 hxs hxy.2]
          exact iht _ (fun z hz => hl z (by simp [hz]))
      rw [hfold rest _ (fun xy hxy => hps xy (by simp [hxy]))]
      congr 1
      rw [s2.2.2.2.2 xs hxs, wireVal_extends s1.1 hxs hacc, s1.2.2.2.2 xs hxs]

lemma gDot_spec {n wFalse : ℕ} {gs : List Gate} (xs ys : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hxs_ok : ∀ w ∈ xs, w < n + gs.length) (hys_ok : ∀ w ∈ ys, w < n + gs.length) :
    let r := gDot n wFalse gs xs ys
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 5 * xs.length ∧ r.2 < n + r.1.length ∧
      ∀ (inp : List Bool) (m : ℕ) (f1 f2 : Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        xs.map (wireVal gs inp) = List.ofFn f1 →
        ys.map (wireVal gs inp) = List.ofFn f2 →
        wireVal r.1 inp r.2 = dotBool f1 f2 := by
  dsimp only [gDot]
  have hps : ∀ ab ∈ xs.zip ys, ab.1 < n + gs.length ∧ ab.2 < n + gs.length := by
    intro ab hab
    have h1 := List.of_mem_zip hab
    exact ⟨hxs_ok ab.1 h1.1, hys_ok ab.2 h1.2⟩
  have s := gDotAux_spec (xs.zip ys) hgs hwf hps
  refine ⟨s.1, s.2.1, ?_, s.2.2.2.1, ?_⟩
  · have hzl : (xs.zip ys).length ≤ xs.length := by simp
    omega
  · intro inp m f1 f2 hinp hwf_val hf1 hf2
    rw [s.2.2.2.2 inp hinp, hwf_val]
    have hlen1 : xs.length = m := by simpa using congrArg List.length hf1
    have hlen2 : ys.length = m := by simpa using congrArg List.length hf2
    unfold dotBool
    have hzip : xs.zip ys = (List.finRange m).map (fun j => (xs[j.val]'(by omega), ys[j.val]'(by omega))) := by
      apply List.ext_getElem
      · simp [hlen1, hlen2]
      · intro i hi1 hi2
        simp [List.getElem_zip]
    rw [hzip, List.foldl_map]
    congr 1
    ext acc j
    have hv1 : wireVal gs inp (xs[j.val]'(by omega)) = f1 j := by
      have := congrArg (fun l : List Bool => l[j.val]?) hf1
      simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j.val < xs.length),
        List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this
    have hv2 : wireVal gs inp (ys[j.val]'(by omega)) = f2 j := by
      have := congrArg (fun l : List Bool => l[j.val]?) hf2
      simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j.val < ys.length),
        List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this
    rw [hv1, hv2]

def gVecXorAux (n : ℕ) (gs : List Gate) : List (ℕ × ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | (a, b) :: rest =>
    let r1 := gXor n gs a b
    let r2 := gVecXorAux n r1.1 rest
    (r2.1, r1.2 :: r2.2)

def gVecXor (n : ℕ) (gs : List Gate) (xs ys : List ℕ) : List Gate × List ℕ :=
  gVecXorAux n gs (xs.zip ys)

lemma gVecXorAux_spec {n : ℕ} {gs : List Gate} (ps : List (ℕ × ℕ))
    (hgs : GoodGates n gs) (hps : ∀ ab ∈ ps, ab.1 < n + gs.length ∧ ab.2 < n + gs.length) :
    let r := gVecXorAux n gs ps
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 4 * ps.length ∧
      r.2.length = ps.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        r.2.map (wireVal r.1 inp) = ps.map (fun ab => xor (wireVal gs inp ab.1) (wireVal gs inp ab.2)) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gVecXorAux], by simp [gVecXorAux], by simp [gVecXorAux], fun _ _ => rfl⟩
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    have hab := hps (a, b) (by simp)
    have ha : a < n + gs.length := hab.1
    have hb : b < n + gs.length := hab.2
    dsimp only [gVecXorAux]
    have s1 := gXor_spec hgs ha hb
    have ih' := ih s1.2.1 (fun xy hxy => by
      have h := hps xy (by simp [hxy])
      have h1 : (gXor n gs a b).1.length = gs.length + 4 := s1.2.2.1
      exact ⟨lt_of_lt_of_le h.1 (by omega), lt_of_lt_of_le h.2 (by omega)⟩)
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, ?_, ?_, ?_, ?_⟩
    · have h1 := s1.2.2.1
      have h2 := ih'.2.2.1
      simp only [List.length_cons]
      omega
    · simp [ih'.2.2.2.1]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le s1.2.2.2.1 (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp s1.2.2.2.1, s1.2.2.2.2 inp hinp, ih'.2.2.2.2.2 inp hinp]
      congr 1
      apply List.map_congr_left
      intro xy hxy
      have h := hps xy (by simp [hxy])
      rw [wireVal_extends s1.1 hinp h.1, wireVal_extends s1.1 hinp h.2]

lemma gVecXor_spec {n : ℕ} {gs : List Gate} (xs ys : List ℕ)
    (hgs : GoodGates n gs) (hxs : ∀ w ∈ xs, w < n + gs.length) (hys : ∀ w ∈ ys, w < n + gs.length) :
    let r := gVecXor n gs xs ys
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 4 * xs.length ∧
      r.2.length = min xs.length ys.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ (inp : List Bool) (m : ℕ) (f1 f2 : Fin m → Bool),
        inp.length = n → xs.map (wireVal gs inp) = List.ofFn f1 → ys.map (wireVal gs inp) = List.ofFn f2 →
        r.2.map (wireVal r.1 inp) = List.ofFn (fun j => xor (f1 j) (f2 j)) := by
  dsimp only [gVecXor]
  have hps : ∀ ab ∈ xs.zip ys, ab.1 < n + gs.length ∧ ab.2 < n + gs.length := by
    intro ab hab; have h := List.of_mem_zip hab; exact ⟨hxs ab.1 h.1, hys ab.2 h.2⟩
  have s := gVecXorAux_spec (xs.zip ys) hgs hps
  refine ⟨s.1, s.2.1, ?_, ?_, s.2.2.2.2.1, ?_⟩
  · have hzl : (xs.zip ys).length ≤ xs.length := by simp
    omega
  · simp [s.2.2.2.1]
  · intro inp m f1 f2 hinp hf1 hf2
    rw [s.2.2.2.2.2 inp hinp]
    have hlen1 : xs.length = m := by simpa using congrArg List.length hf1
    have hlen2 : ys.length = m := by simpa using congrArg List.length hf2
    have hzip : xs.zip ys = (List.finRange m).map (fun j => (xs[j.val]'(by omega), ys[j.val]'(by omega))) := by
      apply List.ext_getElem <;> simp [hlen1, hlen2, List.getElem_zip]
    rw [hzip, List.map_map]
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_finRange] at hi1
      simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, Function.comp_apply,
        List.getElem_ofFn]
      have hv1 : wireVal gs inp (xs[i]'(by omega)) = f1 ⟨i, hi1⟩ := by
        have := congrArg (fun l : List Bool => l[i]?) hf1
        simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : i < xs.length),
          List.getElem?_ofFn, hi1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        exact this
      have hv2 : wireVal gs inp (ys[i]'(by omega)) = f2 ⟨i, hi1⟩ := by
        have := congrArg (fun l : List Bool => l[i]?) hf2
        simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : i < ys.length),
          List.getElem?_ofFn, hi1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        exact this
      rw [hv1, hv2]

def gOrListAux (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | x :: rest =>
    let r1 := gOr n gs acc x
    gOrListAux n r1.1 r1.2 rest

def gOrList (n wFalse : ℕ) (gs : List Gate) (xs : List ℕ) : List Gate × ℕ :=
  gOrListAux n gs wFalse xs

lemma gOrListAux_spec {n : ℕ} {gs : List Gate} {acc : ℕ} (xs : List ℕ)
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gOrListAux n gs acc xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧ r.2 < n + r.1.length ∧
      ∀ inp : List Bool, inp.length = n →
        wireVal r.1 inp r.2 = xs.foldl (fun b w => b || wireVal gs inp w) (wireVal gs inp acc) := by
  induction xs generalizing gs acc with
  | nil => refine ⟨extends_refl gs, hgs, by simp [gOrListAux], hacc, fun _ _ => rfl⟩
  | cons x rest ih =>
    have hx := hxs x (by simp)
    dsimp only [gOrListAux]
    have s1 := gOr_spec hgs hacc hx
    have ih' := ih s1.2.1 s1.2.2.2.1 (fun w hw => lt_of_lt_of_le (hxs w (by simp [hw])) (by omega))
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, by simp [ih'.2.2.1, s1.2.2.1]; omega, ih'.2.2.2.1, fun inp hinp => ?_⟩
    rw [ih'.2.2.2.2 inp hinp, List.foldl_cons, s1.2.2.2.2 inp hinp]
    have hfold : ∀ (l : List ℕ) (b : Bool), (∀ w ∈ l, w < n + gs.length) →
        l.foldl (fun v w => v || wireVal (gOr n gs acc x).1 inp w) b =
        l.foldl (fun v w => v || wireVal gs inp w) b := by
      intro l b hl
      induction l generalizing b with
      | nil => rfl
      | cons w t iht =>
        simp only [List.foldl_cons]
        rw [wireVal_extends s1.1 hinp (hl w (by simp))]
        exact iht _ (fun z hz => hl z (by simp [hz]))
    exact hfold rest _ (fun w hw => hxs w (by simp [hw]))

lemma gOrList_spec {n wFalse : ℕ} {gs : List Gate} (xs : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gOrList n wFalse gs xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧ r.2 < n + r.1.length ∧
      ∀ (inp : List Bool) (m : ℕ) (f : Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        xs.map (wireVal gs inp) = List.ofFn f →
        wireVal r.1 inp r.2 = (List.finRange m).any f := by
  dsimp only [gOrList]
  have s := gOrListAux_spec xs hgs hwf hxs
  refine ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, fun inp m f hinp hwf_val hf => ?_⟩
  rw [s.2.2.2.2 inp hinp, hwf_val]
  have hlen : xs.length = m := by simpa using congrArg List.length hf
  have h1 : xs.foldl (fun b w => b || wireVal gs inp w) false = (xs.map (wireVal gs inp)).any id := by
    clear hf hlen
    have : ∀ (l : List ℕ) (b : Bool),
        l.foldl (fun acc w => acc || wireVal gs inp w) b = (b || (l.map (wireVal gs inp)).any id) := by
      intro l
      induction l with
      | nil => intro b; simp
      | cons w t iht => intro b; simp only [List.foldl_cons, List.map_cons, List.any_cons, id_eq]; rw [iht]; cases b <;> cases wireVal gs inp w <;> rfl
    rw [this xs false, Bool.false_or]
  rw [h1, hf]
  have hany : (List.ofFn f).any id = (List.finRange m).any f := by
    have hof : List.ofFn f = (List.finRange m).map f := by
      apply List.ext_getElem <;> simp
    rw [hof, List.any_map]
    rfl
  exact hany

def gAndListAux (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | x :: rest =>
    let r1 := gAnd n gs acc x
    gAndListAux n r1.1 r1.2 rest

def gAndList (n wTrue : ℕ) (gs : List Gate) (xs : List ℕ) : List Gate × ℕ :=
  gAndListAux n gs wTrue xs

lemma gAndListAux_spec {n : ℕ} {gs : List Gate} {acc : ℕ} (xs : List ℕ)
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gAndListAux n gs acc xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧ r.2 < n + r.1.length ∧
      ∀ inp : List Bool, inp.length = n →
        wireVal r.1 inp r.2 = xs.foldl (fun b w => b && wireVal gs inp w) (wireVal gs inp acc) := by
  induction xs generalizing gs acc with
  | nil => refine ⟨extends_refl gs, hgs, by simp [gAndListAux], hacc, fun _ _ => rfl⟩
  | cons x rest ih =>
    have hx := hxs x (by simp)
    dsimp only [gAndListAux]
    have s1 := gAnd_spec hgs hacc hx
    have ih' := ih s1.2.1 s1.2.2.2.1 (fun w hw => lt_of_lt_of_le (hxs w (by simp [hw])) (by omega))
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, by simp [ih'.2.2.1, s1.2.2.1]; omega, ih'.2.2.2.1, fun inp hinp => ?_⟩
    rw [ih'.2.2.2.2 inp hinp, List.foldl_cons, s1.2.2.2.2 inp hinp]
    have hfold : ∀ (l : List ℕ) (b : Bool), (∀ w ∈ l, w < n + gs.length) →
        l.foldl (fun v w => v && wireVal (gAnd n gs acc x).1 inp w) b =
        l.foldl (fun v w => v && wireVal gs inp w) b := by
      intro l b hl
      induction l generalizing b with
      | nil => rfl
      | cons w t iht =>
        simp only [List.foldl_cons]
        rw [wireVal_extends s1.1 hinp (hl w (by simp))]
        exact iht _ (fun z hz => hl z (by simp [hz]))
    exact hfold rest _ (fun w hw => hxs w (by simp [hw]))

lemma gAndList_spec {n wTrue : ℕ} {gs : List Gate} (xs : List ℕ)
    (hgs : GoodGates n gs) (hwt : wTrue < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gAndList n wTrue gs xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧ r.2 < n + r.1.length ∧
      ∀ (inp : List Bool) (m : ℕ) (f : Fin m → Bool),
        inp.length = n → wireVal gs inp wTrue = true →
        xs.map (wireVal gs inp) = List.ofFn f →
        wireVal r.1 inp r.2 = decide (∀ j : Fin m, f j = true) := by
  dsimp only [gAndList]
  have s := gAndListAux_spec xs hgs hwt hxs
  refine ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, fun inp m f hinp hwt_val hf => ?_⟩
  rw [s.2.2.2.2 inp hinp, hwt_val]
  have h1 : xs.foldl (fun b w => b && wireVal gs inp w) true = (xs.map (wireVal gs inp)).all id := by
    clear hf
    have : ∀ (l : List ℕ) (b : Bool),
        l.foldl (fun acc w => acc && wireVal gs inp w) b = (b && (l.map (wireVal gs inp)).all id) := by
      intro l
      induction l with
      | nil => intro b; simp
      | cons w t iht => intro b; simp only [List.foldl_cons, List.map_cons, List.all_cons, id_eq]; rw [iht]; cases b <;> cases wireVal gs inp w <;> rfl
    rw [this xs true, Bool.true_and]
  rw [h1, hf]
  have hall : (List.ofFn f).all id = decide (∀ j : Fin m, f j = true) := by
    have hof : List.ofFn f = (List.finRange m).map f := by
      apply List.ext_getElem <;> simp
    rw [hof, List.all_map]
    apply Bool.eq_iff_iff.mpr
    simp
  exact hall

def gPrefScanAux (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | x :: rest =>
    let r1 := gOr n gs acc x
    let r2 := gPrefScanAux n r1.1 r1.2 rest
    (r2.1, acc :: r2.2)

def gPrefScan (n wFalse : ℕ) (gs : List Gate) (xs : List ℕ) : List Gate × List ℕ :=
  gPrefScanAux n gs wFalse xs

def prefScanList (b : Bool) : List Bool → List Bool
  | [] => []
  | x :: rest => b :: prefScanList (b || x) rest

lemma prefScanList_length (b : Bool) (l : List Bool) : (prefScanList b l).length = l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons _ _ ih => simp [prefScanList, ih]

lemma prefScanList_ofFn {m : ℕ} (f : Fin m → Bool) :
    ∀ (t : ℕ) (ht : t ≤ m),
      prefScanList (prefScanAux f t) ((List.finRange m).drop t |>.map f) =
        ((List.finRange m).drop t).map (fun c => prefScanAux f c.val) := by
  have hlen : ∀ s t : ℕ, t ≤ m → s ≤ m → t + s = m →
      prefScanList (prefScanAux f t) ((List.finRange m).drop t |>.map f) =
        ((List.finRange m).drop t).map (fun c => prefScanAux f c.val) := by
    intro s
    induction s with
    | zero =>
      intro t _ _ hts
      have htm : t = m := by omega
      subst htm
      rw [List.drop_of_length_le (by simp)]
      rfl
    | succ s ih =>
      intro t ht hs hts
      have htm : t < m := by omega
      have hdrop : (List.finRange m).drop t = ⟨t, htm⟩ :: (List.finRange m).drop (t + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; exact htm)]
        simp
      rw [hdrop, List.map_cons, List.map_cons, prefScanList]
      congr 1
      have hpref : (prefScanAux f t || f ⟨t, htm⟩) = prefScanAux f (t + 1) := by
        simp [prefScanAux, htm]
      rw [hpref]
      exact ih (t + 1) (by omega) (by omega) (by omega)
  intro t ht
  exact hlen (m - t) t ht (by omega) (by omega)

lemma prefScanList_ofFn_zero {m : ℕ} (f : Fin m → Bool) :
    prefScanList false (List.ofFn f) = List.ofFn (fun c : Fin m => prefScanAux f c.val) := by
  have h := prefScanList_ofFn f 0 (Nat.zero_le m)
  simp only [prefScanAux, List.drop_zero] at h
  have hof1 : List.ofFn f = (List.finRange m).map f := by apply List.ext_getElem <;> simp
  have hof2 : List.ofFn (fun c : Fin m => prefScanAux f c.val) =
      (List.finRange m).map (fun c => prefScanAux f c.val) := by apply List.ext_getElem <;> simp
  rw [hof1, hof2]
  exact h

lemma gPrefScanAux_spec {n : ℕ} {gs : List Gate} {acc : ℕ} (xs : List ℕ)
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gPrefScanAux n gs acc xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧
      r.2.length = xs.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        r.2.map (wireVal r.1 inp) = prefScanList (wireVal gs inp acc) (xs.map (wireVal gs inp)) := by
  induction xs generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gPrefScanAux], by simp [gPrefScanAux], by simp [gPrefScanAux],
      fun _ _ => rfl⟩
  | cons x rest ih =>
    have hx := hxs x (by simp)
    dsimp only [gPrefScanAux]
    have s1 := gOr_spec hgs hacc hx
    have ih' := ih s1.2.1 s1.2.2.2.1 (fun w hw => by have h1 := s1.2.2.1; exact lt_of_lt_of_le (hxs w (by simp [hw])) (by omega))
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, ?_, by simp [ih'.2.2.2.1], ?_, ?_⟩
    · have h1 := s1.2.2.1; have h2 := ih'.2.2.1; simp only [List.length_cons]; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le hacc (by have := extends_length s1.1; have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons, prefScanList]
      rw [wireVal_extends (extends_trans s1.1 ih'.1) hinp hacc, ih'.2.2.2.2.2 inp hinp,
        s1.2.2.2.2 inp hinp]
      congr 2
      apply List.map_congr_left
      intro w hw
      exact wireVal_extends s1.1 hinp (hxs w (by simp [hw]))

lemma gPrefScan_spec {n wFalse : ℕ} {gs : List Gate} (xs : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gPrefScan n wFalse gs xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧
      r.2.length = xs.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ (inp : List Bool) (m : ℕ) (f : Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        xs.map (wireVal gs inp) = List.ofFn f →
        r.2.map (wireVal r.1 inp) = List.ofFn (fun c : Fin m => prefScanAux f c.val) := by
  dsimp only [gPrefScan]
  have s := gPrefScanAux_spec xs hgs hwf hxs
  refine ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, fun inp m f hinp hwf_val hf => ?_⟩
  rw [s.2.2.2.2.2 inp hinp, hwf_val, hf]
  exact prefScanList_ofFn_zero f

def gAndNotAux (n : ℕ) (gs : List Gate) : List (ℕ × ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | (a, b) :: rest =>
    let nb := gNot n gs b
    let c := gAnd n nb.1 a nb.2
    let r2 := gAndNotAux n c.1 rest
    (r2.1, c.2 :: r2.2)

lemma gAndNotAux_spec {n : ℕ} {gs : List Gate} (ps : List (ℕ × ℕ))
    (hgs : GoodGates n gs) (hps : ∀ ab ∈ ps, ab.1 < n + gs.length ∧ ab.2 < n + gs.length) :
    let r := gAndNotAux n gs ps
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 2 * ps.length ∧
      r.2.length = ps.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        r.2.map (wireVal r.1 inp) = ps.map (fun ab => wireVal gs inp ab.1 && !wireVal gs inp ab.2) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gAndNotAux], by simp [gAndNotAux], by simp [gAndNotAux],
      fun _ _ => rfl⟩
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    have hab := hps (a, b) (by simp)
    have ha : a < n + gs.length := hab.1
    have hb : b < n + gs.length := hab.2
    dsimp only [gAndNotAux]
    have s1 := gNot_spec hgs hb
    have s2 := gAnd_spec s1.2.1 (lt_of_lt_of_le ha (by have := s1.2.2.1; omega)) s1.2.2.2.1
    have h12 : Extends gs (gAnd n (gNot n gs b).1 a (gNot n gs b).2).1 :=
      extends_trans s1.1 s2.1
    have ih' := ih s2.2.1 (fun xy hxy => by
      have h := hps xy (by simp [hxy])
      have h1 := s1.2.2.1; have h2 := s2.2.2.1
      exact ⟨lt_of_lt_of_le h.1 (by omega), lt_of_lt_of_le h.2 (by omega)⟩)
    refine ⟨extends_trans h12 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 := s1.2.2.1; have h2 := s2.2.2.1; have h3 := ih'.2.2.1; simp only [List.length_cons]; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le s2.2.2.2.1 (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp s2.2.2.2.1, s2.2.2.2.2 inp hinp,
        wireVal_extends s1.1 hinp ha, s1.2.2.2.2 inp hinp, ih'.2.2.2.2.2 inp hinp]
      congr 1
      apply List.map_congr_left
      intro xy hxy
      have h := hps xy (by simp [hxy])
      rw [wireVal_extends h12 hinp h.1, wireVal_extends h12 hinp h.2]

def gFirst (n wFalse : ℕ) (gs : List Gate) (xs : List ℕ) : List Gate × List ℕ :=
  let p := gPrefScan n wFalse gs xs
  gAndNotAux n p.1 (xs.zip p.2)

lemma gFirst_spec {n wFalse : ℕ} {gs : List Gate} (xs : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gFirst n wFalse gs xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 3 * xs.length ∧
      r.2.length = xs.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ (inp : List Bool) (m : ℕ) (f : Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        xs.map (wireVal gs inp) = List.ofFn f →
        r.2.map (wireVal r.1 inp) = List.ofFn (fun c : Fin m => f c && !prefScanAux f c.val) := by
  dsimp only [gFirst]
  have sp := gPrefScan_spec xs hgs hwf hxs
  have hps : ∀ ab ∈ xs.zip (gPrefScan n wFalse gs xs).2,
      ab.1 < n + (gPrefScan n wFalse gs xs).1.length ∧
      ab.2 < n + (gPrefScan n wFalse gs xs).1.length := by
    intro ab hab
    have hmem := List.of_mem_zip hab
    have h1 := sp.2.2.1
    exact ⟨lt_of_lt_of_le (hxs ab.1 hmem.1) (by omega), sp.2.2.2.2.1 ab.2 hmem.2⟩
  have sa := gAndNotAux_spec (xs.zip (gPrefScan n wFalse gs xs).2) sp.2.1 hps
  refine ⟨extends_trans sp.1 sa.1, sa.2.1, ?_, ?_, sa.2.2.2.2.1, ?_⟩
  · have hzl : (xs.zip (gPrefScan n wFalse gs xs).2).length ≤ xs.length := by simp
    have h1 := sp.2.2.1; have h2 := sa.2.2.1; omega
  · simp [sa.2.2.2.1, sp.2.2.2.1]
  · intro inp m f hinp hwf_val hf
    rw [sa.2.2.2.2.2 inp hinp]
    have hpf := sp.2.2.2.2.2 inp m f hinp hwf_val hf
    have hlen1 : xs.length = m := by simpa using congrArg List.length hf
    have hlen2 : (gPrefScan n wFalse gs xs).2.length = m := by rw [sp.2.2.2.1, hlen1]
    have hzip : xs.zip (gPrefScan n wFalse gs xs).2 =
        (List.finRange m).map (fun c => (xs[c.val]'(by omega), (gPrefScan n wFalse gs xs).2[c.val]'(by omega))) := by
      apply List.ext_getElem <;> simp [hlen1, hlen2, List.getElem_zip]
    rw [hzip, List.map_map]
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_finRange] at hi1
      simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, Function.comp_apply,
        List.getElem_ofFn]
      have hv1 : wireVal (gPrefScan n wFalse gs xs).1 inp (xs[i]'(by omega)) = f ⟨i, hi1⟩ := by
        rw [wireVal_extends sp.1 hinp (hxs _ (List.getElem_mem _))]
        have := congrArg (fun l : List Bool => l[i]?) hf
        simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : i < xs.length),
          List.getElem?_ofFn, hi1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        exact this
      have hv2 : wireVal (gPrefScan n wFalse gs xs).1 inp
          ((gPrefScan n wFalse gs xs).2[i]'(by omega)) = prefScanAux f i := by
        have := congrArg (fun l : List Bool => l[i]?) hpf
        simp only [List.getElem?_map,
          List.getElem?_eq_getElem (by omega : i < (gPrefScan n wFalse gs xs).2.length),
          List.getElem?_ofFn, hi1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        exact this
      rw [hv1, hv2]

def gSelectMatAux (n wFalse : ℕ) (gs : List Gate) (sel : List ℕ) (rows : List (List ℕ)) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | j :: rest =>
    let col := rows.map (fun r => r.getD j wFalse)
    let d := gDot n wFalse gs sel col
    let r2 := gSelectMatAux n wFalse d.1 sel rows rest
    (r2.1, d.2 :: r2.2)

def gSelectMat (n wFalse : ℕ) (gs : List Gate) (sel : List ℕ) (rows : List (List ℕ)) (M : ℕ) :
    List Gate × List ℕ :=
  gSelectMatAux n wFalse gs sel rows (List.range M)

lemma gSelectMatAux_spec {n wFalse : ℕ} {gs : List Gate} (sel : List ℕ) (rows : List (List ℕ))
    (js : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hsel : ∀ w ∈ sel, w < n + gs.length)
    (hrows : ∀ r ∈ rows, ∀ w ∈ r, w < n + gs.length) :
    let res := gSelectMatAux n wFalse gs sel rows js
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * sel.length * js.length ∧
      res.2.length = js.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (L : ℕ) (fs : Fin L → Bool) (mat : Fin L → ℕ → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        sel.map (wireVal gs inp) = List.ofFn fs →
        rows.length = L →
        (∀ c : Fin L, ∀ j ∈ js, wireVal gs inp ((rows.getD c.val []).getD j wFalse) = mat c j) →
        res.2.map (wireVal res.1 inp) = js.map (fun j => dotBool fs (fun c => mat c j)) := by
  induction js generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gSelectMatAux], by simp [gSelectMatAux],
      by simp [gSelectMatAux], fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | cons j rest ih =>
    dsimp only [gSelectMatAux]
    have hcol : ∀ w ∈ rows.map (fun r => r.getD j wFalse), w < n + gs.length := by
      intro w hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨r, hr, rfl⟩
      by_cases hjr : j < r.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some]
        exact hrows r hr _ (List.getElem_mem hjr)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
        exact hwf
    have sd := gDot_spec sel (rows.map (fun r => r.getD j wFalse)) hgs hwf hsel hcol
    have hle1 : gs.length ≤ (gDot n wFalse gs sel (rows.map (fun r => r.getD j wFalse))).1.length :=
      extends_length sd.1
    have ih' := ih sd.2.1 (lt_of_lt_of_le hwf (by omega))
      (fun w hw => lt_of_lt_of_le (hsel w hw) (by omega))
      (fun r hr w hw => lt_of_lt_of_le (hrows r hr w hw) (by omega))
    refine ⟨extends_trans sd.1 ih'.1, ih'.2.1, ?_, ?_, ?_, ?_⟩
    · have h1 := sd.2.2.1; have h2 := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · exact congrArg (· + 1) ih'.2.2.2.1
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sd.2.2.2.1 (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp L fs mat hinp hwf_val hfs hlenL hmat
      simp only [List.map_cons]
      have hcol_val : (rows.map (fun r => r.getD j wFalse)).map (wireVal gs inp) =
          List.ofFn (fun c : Fin L => mat c j) := by
        apply List.ext_getElem
        · simp [hlenL]
        · intro i hi1 hi2
          simp only [List.length_map, hlenL] at hi1
          simp only [List.getElem_map, List.getElem_ofFn]
          have hget : rows[i]'(by omega) = rows.getD i [] := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < rows.length)]
          rw [hget]
          exact hmat ⟨i, hi1⟩ j (by simp)
      have hd_val : wireVal (gDot n wFalse gs sel (rows.map (fun r => r.getD j wFalse))).1 inp
          (gDot n wFalse gs sel (rows.map (fun r => r.getD j wFalse))).2 = dotBool fs (fun c => mat c j) :=
        sd.2.2.2.2 inp L fs (fun c => mat c j) hinp hwf_val hfs hcol_val
      rw [wireVal_extends ih'.1 hinp sd.2.2.2.1, hd_val]
      congr 1
      apply ih'.2.2.2.2.2 inp L fs mat hinp (by rw [wireVal_extends sd.1 hinp hwf, hwf_val])
      · rw [listVal_extends sd.1 hinp hsel, hfs]
      · exact hlenL
      · intro c j' hj'
        have hmem : ((rows.getD c.val []).getD j' wFalse) < n + gs.length := by
          have hrc : rows.getD c.val [] = rows[c.val]'(by omega) := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : c.val < rows.length)]
          rw [hrc]
          by_cases hjr : j' < (rows[c.val]'(by omega)).length
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjr, Option.getD_some]
            exact hrows _ (List.getElem_mem _) _ (List.getElem_mem hjr)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
            exact hwf
        rw [wireVal_extends sd.1 hinp hmem]
        exact hmat c j' (by simp [hj'])

lemma gSelectMat_spec {n wFalse : ℕ} {gs : List Gate} (sel : List ℕ) (rows : List (List ℕ)) (M : ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hsel : ∀ w ∈ sel, w < n + gs.length)
    (hrows : ∀ r ∈ rows, ∀ w ∈ r, w < n + gs.length) :
    let res := gSelectMat n wFalse gs sel rows M
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * sel.length * M ∧
      res.2.length = M ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (L : ℕ) (fs : Fin L → Bool) (B : Fin L → Fin M → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        sel.map (wireVal gs inp) = List.ofFn fs →
        rows.length = L →
        (∀ c : Fin L, (rows.getD c.val []).map (wireVal gs inp) = List.ofFn (B c)) →
        res.2.map (wireVal res.1 inp) =
          List.ofFn (fun j : Fin M => dotBool fs (fun c => B c j)) := by
  dsimp only [gSelectMat]
  have s := gSelectMatAux_spec sel rows (List.range M) hgs hwf hsel hrows
  refine ⟨s.1, s.2.1, ?_, ?_, s.2.2.2.2.1, ?_⟩
  · simpa using s.2.2.1
  · simpa using s.2.2.2.1
  · intro inp L fs B hinp hwf_val hfs hlenL hB
    let mat : Fin L → ℕ → Bool := fun c j => if h : j < M then B c ⟨j, h⟩ else false
    have hmat : ∀ c : Fin L, ∀ j ∈ List.range M,
        wireVal gs inp ((rows.getD c.val []).getD j wFalse) = mat c j := by
      intro c j hj
      simp only [List.mem_range] at hj
      dsimp only [mat]
      simp only [hj, ↓reduceDIte]
      have hBc := hB c
      have hlen_r : (rows.getD c.val []).length = M := by simpa using congrArg List.length hBc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      have := congrArg (fun l : List Bool => l[j]?) hBc
      simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j < (rows.getD c.val []).length),
        List.getElem?_ofFn, hj, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this
    have hs := s.2.2.2.2.2 inp L fs mat hinp hwf_val hfs hlenL hmat
    rw [hs]
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.length_map, List.length_range] at hi1
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      congr 1
      ext c
      simp [mat, hi1]

def gMapDot (n wFalse : ℕ) (gs : List Gate) (row : List ℕ) :
    List (List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | b :: rest =>
    let d := gDot n wFalse gs row b
    let r2 := gMapDot n wFalse d.1 row rest
    (r2.1, d.2 :: r2.2)

lemma gMapDot_spec {n wFalse : ℕ} {gs : List Gate} (row : List ℕ) (basis : List (List ℕ))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hrow : ∀ w ∈ row, w < n + gs.length)
    (hbasis : ∀ b ∈ basis, ∀ w ∈ b, w < n + gs.length) :
    let res := gMapDot n wFalse gs row basis
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * row.length * basis.length ∧
      res.2.length = basis.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (m L : ℕ) (fr : Fin m → Bool) (B : Fin L → Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        row.map (wireVal gs inp) = List.ofFn fr →
        basis.length = L →
        (∀ c : Fin L, (basis.getD c.val []).map (wireVal gs inp) = List.ofFn (B c)) →
        res.2.map (wireVal res.1 inp) = List.ofFn (fun c : Fin L => dotBool fr (B c)) := by
  induction basis generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gMapDot], by simp [gMapDot], by simp [gMapDot], ?_⟩
    intro inp m L fr B _ _ _ hlen _
    have hL : L = 0 := by simpa using hlen.symm
    subst hL
    simp [gMapDot]
  | cons b rest ih =>
    dsimp only [gMapDot]
    have hb : ∀ w ∈ b, w < n + gs.length := hbasis b (by simp)
    have sd := gDot_spec row b hgs hwf hrow hb
    have hle1 : gs.length ≤ (gDot n wFalse gs row b).1.length := extends_length sd.1
    have ih' := ih sd.2.1 (lt_of_lt_of_le hwf (by omega))
      (fun w hw => lt_of_lt_of_le (hrow w hw) (by omega))
      (fun r hr w hw => lt_of_lt_of_le (hbasis r (by simp [hr]) w hw) (by omega))
    refine ⟨extends_trans sd.1 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 := sd.2.2.1; have h2 := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sd.2.2.2.1 (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp m L fr B hinp hwf_val hfr hlenL hB
      rcases L with _ | L
      · simp at hlenL
      · have hlen_rest : rest.length = L := by simpa using hlenL
        have hB0 : b.map (wireVal gs inp) = List.ofFn (B 0) := by
          simpa using hB 0
        have hd_val : wireVal (gDot n wFalse gs row b).1 inp (gDot n wFalse gs row b).2 =
            dotBool fr (B 0) :=
          sd.2.2.2.2 inp m fr (B 0) hinp hwf_val hfr hB0
        have hih_val := ih'.2.2.2.2.2 inp m L fr (fun c => B c.succ) hinp
          (by rw [wireVal_extends sd.1 hinp hwf, hwf_val])
          (by rw [listVal_extends sd.1 hinp hrow, hfr])
          hlen_rest
          (fun c => by
            have hmem : ∀ w ∈ rest.getD c.val [], w < n + gs.length := by
              have hrc : rest.getD c.val [] = rest[c.val]'(by omega) := by
                simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : c.val < rest.length)]
              rw [hrc]
              exact hbasis _ (by simp [List.getElem_mem])
            rw [listVal_extends sd.1 hinp hmem]
            have hBc := hB c.succ
            simpa [List.getD_eq_getElem?_getD] using hBc)
        simp only [List.map_cons]
        rw [wireVal_extends ih'.1 hinp sd.2.2.2.1, hd_val, hih_val]
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          cases i with
          | zero => simp
          | succ i => simp

def gNullUpdateRowAux (n : ℕ) (gs : List Gate) (np dp : ℕ) : List (ℕ × ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | (bij, pj) :: rest =>
    let t1 := gAnd n gs dp pj
    let t2 := gXor n t1.1 bij t1.2
    let t3 := gAnd n t2.1 np t2.2
    let r2 := gNullUpdateRowAux n t3.1 np dp rest
    (r2.1, t3.2 :: r2.2)

lemma gNullUpdateRowAux_spec {n : ℕ} {gs : List Gate} {np dp : ℕ} (ps : List (ℕ × ℕ))
    (hgs : GoodGates n gs) (hnp : np < n + gs.length) (hdp : dp < n + gs.length)
    (hps : ∀ ab ∈ ps, ab.1 < n + gs.length ∧ ab.2 < n + gs.length) :
    let res := gNullUpdateRowAux n gs np dp ps
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length = gs.length + 6 * ps.length ∧
      res.2.length = ps.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        res.2.map (wireVal res.1 inp) =
          ps.map (fun ab => wireVal gs inp np && xor (wireVal gs inp ab.1) (wireVal gs inp dp && wireVal gs inp ab.2)) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gNullUpdateRowAux], by simp [gNullUpdateRowAux],
      by simp [gNullUpdateRowAux], fun _ _ => rfl⟩
  | cons ab rest ih =>
    rcases ab with ⟨bij, pj⟩
    have hab := hps (bij, pj) (by simp)
    have hbij : bij < n + gs.length := hab.1
    have hpj : pj < n + gs.length := hab.2
    dsimp only [gNullUpdateRowAux]
    have s1 := gAnd_spec hgs hdp hpj
    have h1 : (gAnd n gs dp pj).1.length = gs.length + 1 := s1.2.2.1
    have s2 := gXor_spec s1.2.1 (lt_of_lt_of_le hbij (by omega)) s1.2.2.2.1
    have h2 : (gXor n (gAnd n gs dp pj).1 bij (gAnd n gs dp pj).2).1.length = (gAnd n gs dp pj).1.length + 4 := s2.2.2.1
    have s3 := gAnd_spec s2.2.1 (lt_of_lt_of_le hnp (by omega)) s2.2.2.2.1
    have h3 : (gAnd n (gXor n (gAnd n gs dp pj).1 bij (gAnd n gs dp pj).2).1 np (gXor n (gAnd n gs dp pj).1 bij (gAnd n gs dp pj).2).2).1.length =
      (gXor n (gAnd n gs dp pj).1 bij (gAnd n gs dp pj).2).1.length + 1 := s3.2.2.1
    have h13 : Extends gs (gAnd n (gXor n (gAnd n gs dp pj).1 bij (gAnd n gs dp pj).2).1 np (gXor n (gAnd n gs dp pj).1 bij (gAnd n gs dp pj).2).2).1 :=
      extends_trans s1.1 (extends_trans s2.1 s3.1)
    have ih' := ih s3.2.1 (lt_of_lt_of_le hnp (by omega)) (lt_of_lt_of_le hdp (by omega))
      (fun xy hxy => by
        have h := hps xy (by simp [hxy])
        exact ⟨lt_of_lt_of_le h.1 (by omega), lt_of_lt_of_le h.2 (by omega)⟩)
    refine ⟨extends_trans h13 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h4 := ih'.2.2.1; simp only [List.length_cons]; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le s3.2.2.2.1 (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp s3.2.2.2.1, s3.2.2.2.2 inp hinp,
        wireVal_extends (extends_trans s1.1 s2.1) hinp hnp,
        s2.2.2.2.2 inp hinp, wireVal_extends s1.1 hinp hbij, s1.2.2.2.2 inp hinp, ih'.2.2.2.2.2 inp hinp]
      congr 1
      apply List.map_congr_left
      intro xy hxy
      have h := hps xy (by simp [hxy])
      rw [wireVal_extends h13 hinp h.1, wireVal_extends h13 hinp h.2,
        wireVal_extends h13 hinp hnp, wireVal_extends h13 hinp hdp]

def gNullUpdateMatAux (n : ℕ) (gs : List Gate) (pivVec : List ℕ) :
    List (List ℕ × ℕ × ℕ × ℕ) → List Gate × List (List ℕ)
  | [] => (gs, [])
  | (b, dc, pc, ipc) :: rest =>
    let np := gNot n gs ipc
    let dp := gAnd n np.1 dc pc
    let row := gNullUpdateRowAux n dp.1 np.2 dp.2 (b.zip pivVec)
    let r2 := gNullUpdateMatAux n row.1 pivVec rest
    (r2.1, row.2 :: r2.2)

lemma gNullUpdateMatAux_spec {n : ℕ} {gs : List Gate} (pivVec : List ℕ)
    (rows : List (List ℕ × ℕ × ℕ × ℕ))
    (hgs : GoodGates n gs) (hpv : ∀ w ∈ pivVec, w < n + gs.length)
    (hrows : ∀ x ∈ rows, (∀ w ∈ x.1, w < n + gs.length) ∧
      x.2.1 < n + gs.length ∧ x.2.2.1 < n + gs.length ∧ x.2.2.2 < n + gs.length) :
    let res := gNullUpdateMatAux n gs pivVec rows
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (6 * pivVec.length + 2) * rows.length ∧
      res.2.length = rows.length ∧
      (∀ r ∈ res.2, ∀ w ∈ r, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (m : ℕ) (pv : Fin m → Bool),
        inp.length = n → pivVec.map (wireVal gs inp) = List.ofFn pv →
        ∀ (c : ℕ) (hc : c < rows.length) (bc : Fin m → Bool),
            (rows[c]'hc).1.map (wireVal gs inp) = List.ofFn bc →
            (res.2.getD c []).map (wireVal res.1 inp) = List.ofFn (fun j : Fin m =>
              !(wireVal gs inp (rows[c]'hc).2.2.2) &&
                xor (bc j) (wireVal gs inp (rows[c]'hc).2.1 &&
                  wireVal gs inp (rows[c]'hc).2.2.1 && pv j)) := by
  induction rows generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gNullUpdateMatAux], by simp [gNullUpdateMatAux],
      by simp [gNullUpdateMatAux], fun _ _ _ _ _ c hc => by simp at hc⟩
  | cons x rest ih =>
    rcases x with ⟨b, dc, pc, ipc⟩
    have hx := hrows (b, dc, pc, ipc) (by simp)
    have hb : ∀ w ∈ b, w < n + gs.length := hx.1
    have hdc : dc < n + gs.length := hx.2.1
    have hpc : pc < n + gs.length := hx.2.2.1
    have hipc : ipc < n + gs.length := hx.2.2.2
    dsimp only [gNullUpdateMatAux]
    have s1 := gNot_spec hgs hipc
    have h1 : (gNot n gs ipc).1.length = gs.length + 1 := s1.2.2.1
    have s2 := gAnd_spec s1.2.1 (lt_of_lt_of_le hdc (by omega)) (lt_of_lt_of_le hpc (by omega))
    have h2 : (gAnd n (gNot n gs ipc).1 dc pc).1.length = (gNot n gs ipc).1.length + 1 := s2.2.2.1
    have h12 : Extends gs (gAnd n (gNot n gs ipc).1 dc pc).1 := extends_trans s1.1 s2.1
    have hps : ∀ ab ∈ b.zip pivVec, ab.1 < n + (gAnd n (gNot n gs ipc).1 dc pc).1.length ∧
        ab.2 < n + (gAnd n (gNot n gs ipc).1 dc pc).1.length := by
      intro ab hab
      have hm := List.of_mem_zip hab
      exact ⟨lt_of_lt_of_le (hb ab.1 hm.1) (by omega), lt_of_lt_of_le (hpv ab.2 hm.2) (by omega)⟩
    have s3 := gNullUpdateRowAux_spec (b.zip pivVec) s2.2.1
      (lt_of_lt_of_le s1.2.2.2.1 (by omega)) s2.2.2.2.1 hps
    have h3 : (gNullUpdateRowAux n (gAnd n (gNot n gs ipc).1 dc pc).1 (gNot n gs ipc).2
        (gAnd n (gNot n gs ipc).1 dc pc).2 (b.zip pivVec)).1.length =
        (gAnd n (gNot n gs ipc).1 dc pc).1.length + 6 * (b.zip pivVec).length := s3.2.2.1
    have h13 : Extends gs (gNullUpdateRowAux n (gAnd n (gNot n gs ipc).1 dc pc).1 (gNot n gs ipc).2
        (gAnd n (gNot n gs ipc).1 dc pc).2 (b.zip pivVec)).1 := extends_trans h12 s3.1
    have hle13 : gs.length ≤ (gNullUpdateRowAux n (gAnd n (gNot n gs ipc).1 dc pc).1 (gNot n gs ipc).2
        (gAnd n (gNot n gs ipc).1 dc pc).2 (b.zip pivVec)).1.length := extends_length h13
    have ih' := ih s3.2.1 (fun w hw => lt_of_lt_of_le (hpv w hw) (by omega))
      (fun y hy => have h := hrows y (by simp [hy]);
        ⟨fun w hw => lt_of_lt_of_le (h.1 w hw) (by omega),
         lt_of_lt_of_le h.2.1 (by omega),
         lt_of_lt_of_le h.2.2.1 (by omega),
         lt_of_lt_of_le h.2.2.2 (by omega)⟩)
    refine ⟨extends_trans h13 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have hzl : (b.zip pivVec).length ≤ pivVec.length := by simp
      have h4 := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro r hr w hw
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact lt_of_lt_of_le (s3.2.2.2.2.1 w hw) (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 r hr w hw
    · intro inp m pv hinp hpv_val c hc bc hbc
      cases c with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [listVal_extends ih'.1 hinp s3.2.2.2.2.1, s3.2.2.2.2.2 inp hinp]
        have hlen1 : b.length = m := by simpa using congrArg List.length hbc
        have hlen2 : pivVec.length = m := by simpa using congrArg List.length hpv_val
        have hzip : b.zip pivVec =
            (List.finRange m).map (fun j => (b[j.val]'(by omega), pivVec[j.val]'(by omega))) := by
          apply List.ext_getElem <;> simp [hlen1, hlen2, List.getElem_zip]
        rw [hzip, List.map_map]
        have hof : List.ofFn (fun j : Fin m =>
            !(wireVal gs inp ipc) && xor (bc j) (wireVal gs inp dc && wireVal gs inp pc && pv j)) =
            (List.finRange m).map (fun j : Fin m =>
            !(wireVal gs inp ipc) && xor (bc j) (wireVal gs inp dc && wireVal gs inp pc && pv j)) := by
          apply List.ext_getElem <;> simp
        rw [hof]
        apply List.map_congr_left
        intro j _
        dsimp only [Function.comp_apply]
        rw [wireVal_extends s2.1 hinp s1.2.2.2.1, s1.2.2.2.2 inp hinp,
          s2.2.2.2.2 inp hinp, wireVal_extends s1.1 hinp hdc, wireVal_extends s1.1 hinp hpc]
        have hv1 : wireVal (gAnd n (gNot n gs ipc).1 dc pc).1 inp (b[j.val]'(by omega)) = bc j := by
          rw [wireVal_extends h12 hinp (hb _ (List.getElem_mem _))]
          have hbc0 := hbc
          simp only [List.getElem_cons_zero] at hbc0
          have := congrArg (fun l : List Bool => l[j.val]?) hbc0
          simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j.val < b.length),
            List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
          simpa using this
        have hv2 : wireVal (gAnd n (gNot n gs ipc).1 dc pc).1 inp (pivVec[j.val]'(by omega)) = pv j := by
          rw [wireVal_extends h12 hinp (hpv _ (List.getElem_mem _))]
          have := congrArg (fun l : List Bool => l[j.val]?) hpv_val
          simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j.val < pivVec.length),
            List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
          simpa using this
        rw [hv1, hv2, Bool.and_assoc]
      | succ c =>
        have hc' : c < rest.length := by simpa using hc
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hmem_c : ∀ w ∈ (rest[c]'hc').1, w < n + gs.length :=
          (hrows _ (List.mem_cons_of_mem _ (List.getElem_mem hc'))).1
        have hih := ih'.2.2.2.2.2 inp m pv hinp
          (by rw [listVal_extends h13 hinp hpv, hpv_val]) c hc' bc
          (by rw [listVal_extends h13 hinp hmem_c]; exact hbc)
        rw [hih]
        have h_c_mem := (hrows _ (List.mem_cons_of_mem _ (List.getElem_mem hc'))).2
        rw [wireVal_extends h13 hinp h_c_mem.1, wireVal_extends h13 hinp h_c_mem.2.1,
          wireVal_extends h13 hinp h_c_mem.2.2]

def gNullStep (n wFalse : ℕ) (gs : List Gate) (m : ℕ) (basis : List (List ℕ)) (row : List ℕ) :
    List Gate × List (List ℕ) :=
  let d := gMapDot n wFalse gs row basis
  let pref := gPrefScan n wFalse d.1 d.2
  let isPiv := gAndNotAux n pref.1 (d.2.zip pref.2)
  let pivVec := gSelectMat n wFalse isPiv.1 isPiv.2 basis m
  let packed := (basis.zip (d.2.zip (pref.2.zip isPiv.2)))
  gNullUpdateMatAux n pivVec.1 pivVec.2 packed

lemma gNullStep_spec {n wFalse : ℕ} {gs : List Gate} (m : ℕ) (basis : List (List ℕ)) (row : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hblen : basis.length = m)
    (hbasis : ∀ b ∈ basis, ∀ w ∈ b, w < n + gs.length)
    (hrow : ∀ w ∈ row, w < n + gs.length) :
    let res := gNullStep n wFalse gs m basis row
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 17 * m * m + 5 * m + 5 * row.length * m ∧
      res.2.length = m ∧
      (∀ b ∈ res.2, ∀ w ∈ b, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (B : Basis m) (r : Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        row.map (wireVal gs inp) = List.ofFn r →
        (∀ c : Fin m, (basis.getD c.val []).map (wireVal gs inp) = List.ofFn (B c)) →
        ∀ c : Fin m, (res.2.getD c.val []).map (wireVal res.1 inp) = List.ofFn (nullStep B r c) := by
  dsimp only [gNullStep]
  let d := gMapDot n wFalse gs row basis
  let pref := gPrefScan n wFalse d.1 d.2
  let isPiv := gAndNotAux n pref.1 (d.2.zip pref.2)
  let pivVec := gSelectMat n wFalse isPiv.1 isPiv.2 basis m
  have sd := gMapDot_spec row basis hgs hwf hrow hbasis
  have hle1 : gs.length ≤ d.1.length := extends_length sd.1
  have sp := gPrefScan_spec d.2 sd.2.1
    (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n)) sd.2.2.2.2.1
  have hle2 : d.1.length ≤ pref.1.length := extends_length sp.1
  have hle12 : gs.length ≤ pref.1.length := Nat.le_trans hle1 hle2
  have hps : ∀ ab ∈ d.2.zip pref.2, ab.1 < n + pref.1.length ∧ ab.2 < n + pref.1.length := by
    intro ab hab
    have hm := List.of_mem_zip hab
    exact ⟨lt_of_lt_of_le (sd.2.2.2.2.1 ab.1 hm.1) (Nat.add_le_add_left hle2 n),
           sp.2.2.2.2.1 ab.2 hm.2⟩
  have si := gAndNotAux_spec (d.2.zip pref.2) sp.2.1 hps
  have hle3 : pref.1.length ≤ isPiv.1.length := extends_length si.1
  have hlen13 : Extends gs isPiv.1 := extends_trans sd.1 (extends_trans sp.1 si.1)
  have hle_all3 : gs.length ≤ isPiv.1.length := extends_length hlen13
  have spv := gSelectMat_spec isPiv.2 basis m si.2.1
    (lt_of_lt_of_le hwf (Nat.add_le_add_left hle_all3 n)) si.2.2.2.2.1
    (fun r hr w hw => lt_of_lt_of_le (hbasis r hr w hw) (Nat.add_le_add_left hle_all3 n))
  have hle4 : isPiv.1.length ≤ pivVec.1.length := extends_length spv.1
  have hlen14 : Extends gs pivVec.1 := extends_trans hlen13 spv.1
  have hle_all4 : gs.length ≤ pivVec.1.length := extends_length hlen14
  have hle234 : d.1.length ≤ pivVec.1.length := Nat.le_trans hle2 (Nat.le_trans hle3 hle4)
  have hle34 : pref.1.length ≤ pivVec.1.length := Nat.le_trans hle3 hle4
  let packed := basis.zip (d.2.zip (pref.2.zip isPiv.2))
  have hpacked_mem : ∀ x ∈ packed,
      (∀ w ∈ x.1, w < n + pivVec.1.length) ∧
      x.2.1 < n + pivVec.1.length ∧
      x.2.2.1 < n + pivVec.1.length ∧
      x.2.2.2 < n + pivVec.1.length := by
    intro x hx
    have hm1 := List.of_mem_zip hx
    have hm2 := List.of_mem_zip hm1.2
    have hm3 := List.of_mem_zip hm2.2
    exact ⟨fun w hw => lt_of_lt_of_le (hbasis x.1 hm1.1 w hw) (Nat.add_le_add_left hle_all4 n),
      lt_of_lt_of_le (sd.2.2.2.2.1 x.2.1 hm2.1) (Nat.add_le_add_left hle234 n),
      lt_of_lt_of_le (sp.2.2.2.2.1 x.2.2.1 hm3.1) (Nat.add_le_add_left hle34 n),
      lt_of_lt_of_le (si.2.2.2.2.1 x.2.2.2 hm3.2) (Nat.add_le_add_left hle4 n)⟩
  have su := gNullUpdateMatAux_spec pivVec.2 packed spv.2.1 spv.2.2.2.2.1 hpacked_mem
  have hd_len : d.2.length = m := by rw [sd.2.2.2.1, hblen]
  have hp_len : pref.2.length = m := by rw [sp.2.2.2.1, hd_len]
  have hi_len : isPiv.2.length = m := by rw [si.2.2.2.1]; simp [hd_len, hp_len]
  have hpack_len : packed.length = m := by simp [packed, hblen, hd_len, hp_len, hi_len]
  refine ⟨extends_trans hlen14 su.1, su.2.1, ?_, ?_, su.2.2.2.2.1, ?_⟩
  · have h1 := sd.2.2.1
    have h2 := sp.2.2.1
    have h3 := si.2.2.1
    have h4 := spv.2.2.1
    have h5 := su.2.2.1
    have hzp : (d.2.zip pref.2).length ≤ m := by simp [hd_len]
    have hpv_len := spv.2.2.2.1
    change d.1.length ≤ gs.length + 5 * row.length * basis.length at h1
    change pref.1.length = d.1.length + d.2.length at h2
    change isPiv.1.length = pref.1.length + 2 * (d.2.zip pref.2).length at h3
    change pivVec.1.length ≤ isPiv.1.length + 5 * isPiv.2.length * m at h4
    change (gNullUpdateMatAux n pivVec.1 pivVec.2 packed).1.length ≤
      pivVec.1.length + (6 * pivVec.2.length + 2) * packed.length at h5
    rw [hblen] at h1
    rw [hd_len] at h2
    rw [hi_len] at h4
    rw [hpv_len, hpack_len] at h5
    nlinarith
  · rw [su.2.2.2.1, hpack_len]
  · intro inp B r hinp hwf_val hr_val hB c
    let d_f : Fin m → Bool := fun c' => dotBool r (B c')
    let pref_f : Fin m → Bool := fun c' => prefScanAux d_f c'.val
    let isPiv_f : Fin m → Bool := fun c' => d_f c' && !pref_f c'
    let pivVec_f : Fin m → Bool := fun j => dotBool isPiv_f (fun c' => B c' j)
    have hd_val : d.2.map (wireVal d.1 inp) = List.ofFn d_f :=
      sd.2.2.2.2.2 inp m m r B hinp hwf_val hr_val hblen hB
    have hp_val : pref.2.map (wireVal pref.1 inp) = List.ofFn pref_f :=
      sp.2.2.2.2.2 inp m d_f hinp (by rw [wireVal_extends sd.1 hinp hwf, hwf_val]) hd_val
    have hi_val : isPiv.2.map (wireVal isPiv.1 inp) = List.ofFn isPiv_f := by
      rw [si.2.2.2.2.2 inp hinp]
      have hzip : d.2.zip pref.2 = (List.finRange m).map (fun c' =>
          (d.2[c'.val]'(by rw [hd_len]; exact c'.isLt),
           pref.2[c'.val]'(by rw [hp_len]; exact c'.isLt))) := by
        apply List.ext_getElem <;> simp [hd_len, hp_len, List.getElem_zip]
      rw [hzip, List.map_map]
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        simp only [List.length_map, List.length_finRange] at hi1
        simp only [List.getElem_map, List.getElem_finRange, Fin.val_cast, Function.comp_apply,
          List.getElem_ofFn]
        have hid : i < d.2.length := by rw [hd_len]; exact hi1
        have hip : i < pref.2.length := by rw [hp_len]; exact hi1
        have hv1 : wireVal pref.1 inp (d.2[i]'hid) = d_f ⟨i, hi1⟩ := by
          rw [wireVal_extends sp.1 hinp (sd.2.2.2.2.1 _ (List.getElem_mem hid))]
          have := congrArg (fun l : List Bool => l[i]?) hd_val
          simp only [List.getElem?_map, List.getElem?_eq_getElem hid,
            List.getElem?_ofFn, hi1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
          exact this
        have hv2 : wireVal pref.1 inp (pref.2[i]'hip) = pref_f ⟨i, hi1⟩ := by
          have := congrArg (fun l : List Bool => l[i]?) hp_val
          simp only [List.getElem?_map, List.getElem?_eq_getElem hip,
            List.getElem?_ofFn, hi1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
          exact this
        rw [hv1, hv2]
    have hpv_val : pivVec.2.map (wireVal pivVec.1 inp) = List.ofFn pivVec_f := by
      refine spv.2.2.2.2.2 inp m isPiv_f B hinp ?_ hi_val hblen (fun c' => ?_)
      · rw [wireVal_extends hlen13 hinp hwf, hwf_val]
      · have hc'b : c'.val < basis.length := by rw [hblen]; exact c'.isLt
        have hmem_c : ∀ w ∈ basis.getD c'.val [], w < n + gs.length := by
          have hrc : basis.getD c'.val [] = basis[c'.val]'hc'b := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc'b]
          rw [hrc]
          exact hbasis _ (List.getElem_mem hc'b)
        rw [listVal_extends hlen13 hinp hmem_c, hB c']
    have hcb : c.val < basis.length := by rw [hblen]; exact c.isLt
    have hcd : c.val < d.2.length := by rw [hd_len]; exact c.isLt
    have hcp : c.val < pref.2.length := by rw [hp_len]; exact c.isLt
    have hci : c.val < isPiv.2.length := by rw [hi_len]; exact c.isLt
    have hcpk : c.val < packed.length := by rw [hpack_len]; exact c.isLt
    have hget : packed[c.val]'hcpk =
        (basis[c.val]'hcb, (d.2[c.val]'hcd, (pref.2[c.val]'hcp, isPiv.2[c.val]'hci))) := by
      simp [packed, List.getElem_zip]
    have hsu := su.2.2.2.2.2 inp m pivVec_f hinp hpv_val c.val hcpk (B c) (by
      rw [hget]
      have hmem_c : ∀ w ∈ basis[c.val]'hcb, w < n + gs.length := hbasis _ (List.getElem_mem hcb)
      rw [listVal_extends hlen14 hinp hmem_c]
      have hrc : basis[c.val]'hcb = basis.getD c.val [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcb]
      rw [hrc, hB c])
    rw [hsu]
    congr 1
    ext j
    rw [hget]
    dsimp only
    have hd_c : wireVal pivVec.1 inp (d.2[c.val]'hcd) = d_f c := by
      rw [wireVal_extends (extends_trans sp.1 (extends_trans si.1 spv.1)) hinp
        (sd.2.2.2.2.1 _ (List.getElem_mem hcd))]
      have := congrArg (fun l : List Bool => l[c.val]?) hd_val
      simp only [List.getElem?_map, List.getElem?_eq_getElem hcd,
        List.getElem?_ofFn, c.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this
    have hp_c : wireVal pivVec.1 inp (pref.2[c.val]'hcp) = pref_f c := by
      rw [wireVal_extends (extends_trans si.1 spv.1) hinp (sp.2.2.2.2.1 _ (List.getElem_mem hcp))]
      have := congrArg (fun l : List Bool => l[c.val]?) hp_val
      simp only [List.getElem?_map, List.getElem?_eq_getElem hcp,
        List.getElem?_ofFn, c.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this
    have hi_c : wireVal pivVec.1 inp (isPiv.2[c.val]'hci) = isPiv_f c := by
      rw [wireVal_extends spv.1 hinp (si.2.2.2.2.1 _ (List.getElem_mem hci))]
      have := congrArg (fun l : List Bool => l[c.val]?) hi_val
      simp only [List.getElem?_map, List.getElem?_eq_getElem hci,
        List.getElem?_ofFn, c.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this
    rw [hd_c, hp_c, hi_c]
    rfl

def gVecEqAux (n : ℕ) (gs : List Gate) : List (ℕ × ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | (a, b) :: rest =>
    let r1 := gEq n gs a b
    let r2 := gVecEqAux n r1.1 rest
    (r2.1, r1.2 :: r2.2)

def gVecEq (n wTrue : ℕ) (gs : List Gate) (xs ys : List ℕ) : List Gate × ℕ :=
  let v := gVecEqAux n gs (xs.zip ys)
  gAndList n wTrue v.1 v.2

lemma gVecEqAux_spec {n : ℕ} {gs : List Gate} (ps : List (ℕ × ℕ))
    (hgs : GoodGates n gs) (hps : ∀ ab ∈ ps, ab.1 < n + gs.length ∧ ab.2 < n + gs.length) :
    let r := gVecEqAux n gs ps
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 5 * ps.length ∧
      r.2.length = ps.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        r.2.map (wireVal r.1 inp) = ps.map (fun ab => decide (wireVal gs inp ab.1 = wireVal gs inp ab.2)) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gVecEqAux], by simp [gVecEqAux], by simp [gVecEqAux], fun _ _ => rfl⟩
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    have hab := hps (a, b) (by simp)
    dsimp only [gVecEqAux]
    have s1 := gEq_spec hgs hab.1 hab.2
    have hle1 : gs.length ≤ (gEq n gs a b).1.length := extends_length s1.1
    have ih' := ih s1.2.1 (fun xy hxy => by
      have h := hps xy (by simp [hxy])
      exact ⟨lt_of_lt_of_le h.1 (Nat.add_le_add_left hle1 n),
             lt_of_lt_of_le h.2 (Nat.add_le_add_left hle1 n)⟩)
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, ?_, by simp [ih'.2.2.2.1], ?_, ?_⟩
    · have h1 : (gEq n gs a b).1.length = gs.length + 5 := s1.2.2.1
      have h2 : (gVecEqAux n (gEq n gs a b).1 rest).1.length = (gEq n gs a b).1.length + 5 * rest.length := ih'.2.2.1
      rw [h2, h1]; simp only [List.length_cons]; ring
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le s1.2.2.2.1 (Nat.add_le_add_left (extends_length ih'.1) n)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp s1.2.2.2.1, s1.2.2.2.2 inp hinp, ih'.2.2.2.2.2 inp hinp]
      congr 1
      apply List.map_congr_left
      intro xy hxy
      have h := hps xy (by simp [hxy])
      rw [wireVal_extends s1.1 hinp h.1, wireVal_extends s1.1 hinp h.2]

lemma gVecEq_spec {n wTrue : ℕ} {gs : List Gate} (xs ys : List ℕ)
    (hgs : GoodGates n gs) (hwt : wTrue < n + gs.length)
    (hxs : ∀ w ∈ xs, w < n + gs.length) (hys : ∀ w ∈ ys, w < n + gs.length) :
    let r := gVecEq n wTrue gs xs ys
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 6 * xs.length ∧ r.2 < n + r.1.length ∧
      ∀ (inp : List Bool) (m : ℕ) (f1 f2 : Fin m → Bool),
        inp.length = n → wireVal gs inp wTrue = true →
        xs.map (wireVal gs inp) = List.ofFn f1 → ys.map (wireVal gs inp) = List.ofFn f2 →
        wireVal r.1 inp r.2 = decide (∀ j : Fin m, f1 j = f2 j) := by
  dsimp only [gVecEq]
  have hps : ∀ ab ∈ xs.zip ys, ab.1 < n + gs.length ∧ ab.2 < n + gs.length := by
    intro ab hab; have h := List.of_mem_zip hab; exact ⟨hxs ab.1 h.1, hys ab.2 h.2⟩
  have sv := gVecEqAux_spec (xs.zip ys) hgs hps
  have hle1 : gs.length ≤ (gVecEqAux n gs (xs.zip ys)).1.length := extends_length sv.1
  have sa := gAndList_spec (gVecEqAux n gs (xs.zip ys)).2 sv.2.1
    (lt_of_lt_of_le hwt (by omega)) sv.2.2.2.2.1
  refine ⟨extends_trans sv.1 sa.1, sa.2.1, ?_, sa.2.2.2.1, ?_⟩
  · have hzl : (xs.zip ys).length ≤ xs.length := by simp
    have h1 := sv.2.2.1; have h2 := sa.2.2.1; have h3 := sv.2.2.2.1
    omega
  · intro inp m f1 f2 hinp hwt_val hf1 hf2
    have hlen1 : xs.length = m := by simpa using congrArg List.length hf1
    have hlen2 : ys.length = m := by simpa using congrArg List.length hf2
    have hzip : xs.zip ys = (List.finRange m).map (fun j => (xs[j.val]'(by omega), ys[j.val]'(by omega))) := by
      apply List.ext_getElem <;> simp [hlen1, hlen2, List.getElem_zip]
    have hv_val : (gVecEqAux n gs (xs.zip ys)).2.map (wireVal (gVecEqAux n gs (xs.zip ys)).1 inp) =
        List.ofFn (fun j : Fin m => decide (f1 j = f2 j)) := by
      rw [sv.2.2.2.2.2 inp hinp, hzip, List.map_map]
      have hof : List.ofFn (fun j : Fin m => decide (f1 j = f2 j)) =
          (List.finRange m).map (fun j : Fin m => decide (f1 j = f2 j)) := by
        apply List.ext_getElem <;> simp
      rw [hof]
      apply List.map_congr_left
      intro j _
      dsimp only [Function.comp_apply]
      have hv1 : wireVal gs inp (xs[j.val]'(by omega)) = f1 j := by
        have := congrArg (fun l : List Bool => l[j.val]?) hf1
        simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j.val < xs.length),
          List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa using this
      have hv2 : wireVal gs inp (ys[j.val]'(by omega)) = f2 j := by
        have := congrArg (fun l : List Bool => l[j.val]?) hf2
        simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j.val < ys.length),
          List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa using this
      rw [hv1, hv2]
    have hs := sa.2.2.2.2 inp m (fun j => decide (f1 j = f2 j)) hinp
      (by rw [wireVal_extends sv.1 hinp hwt, hwt_val]) hv_val
    rw [hs]
    apply Bool.eq_iff_iff.mpr
    simp

def gNotList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | x :: rest =>
    let r1 := gNot n gs x
    let r2 := gNotList n r1.1 rest
    (r2.1, r1.2 :: r2.2)

lemma gNotList_spec {n : ℕ} {gs : List Gate} (xs : List ℕ)
    (hgs : GoodGates n gs) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let r := gNotList n gs xs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + xs.length ∧
      r.2.length = xs.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        r.2.map (wireVal r.1 inp) = xs.map (fun w => !(wireVal gs inp w)) := by
  induction xs generalizing gs with
  | nil => refine ⟨extends_refl gs, hgs, by simp [gNotList], by simp [gNotList], by simp [gNotList], fun _ _ => rfl⟩
  | cons x rest ih =>
    have hx := hxs x (by simp)
    dsimp only [gNotList]
    have s1 := gNot_spec hgs hx
    have ih' := ih s1.2.1 (fun w hw => by have h1 := s1.2.2.1; exact lt_of_lt_of_le (hxs w (by simp [hw])) (by omega))
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, ?_, by simp [ih'.2.2.2.1], ?_, ?_⟩
    · have h1 := s1.2.2.1; have h2 := ih'.2.2.1; simp only [List.length_cons]; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le s1.2.2.2.1 (by have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp s1.2.2.2.1, s1.2.2.2.2 inp hinp, ih'.2.2.2.2.2 inp hinp]
      congr 1
      apply List.map_congr_left
      intro w hw
      rw [wireVal_extends s1.1 hinp (hxs w (by simp [hw]))]

def bitsVal : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsVal bs

lemma bitsVal_lt (l : List Bool) : bitsVal l < 2 ^ l.length := by
  induction l with
  | nil => simp [bitsVal]
  | cons b bs ih =>
    simp only [bitsVal, List.length_cons, Nat.pow_succ']
    cases b <;> simp <;> omega

lemma bitsVal_range_testBit (n x : ℕ) :
    bitsVal ((List.range n).map (fun i => x.testBit i)) = x % 2 ^ n := by
  induction n generalizing x with
  | zero => simp [bitsVal, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [bitsVal]
    have hdiv : (List.range n).map ((fun i => x.testBit i) ∘ Nat.succ) =
        (List.range n).map (fun i => (x / 2).testBit i) := by
      apply List.map_congr_left
      intro i _
      exact Nat.testBit_succ x i
    rw [hdiv, ih (x / 2)]
    have hbit0 : (x.testBit 0).toNat = x % 2 := by
      rw [Nat.testBit_zero]
      cases Nat.mod_two_eq_zero_or_one x with
      | inl h => simp [h]
      | inr h => simp [h]
    rw [hbit0, Nat.pow_succ']
    have hlt : x % 2 + 2 * ((x / 2) % 2 ^ n) < 2 * 2 ^ n := by
      have : x % 2 < 2 := Nat.mod_lt x (by decide)
      have : (x / 2) % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.pow_pos (by decide))
      omega
    have heq : x = (x % 2 + 2 * ((x / 2) % 2 ^ n)) + 2 * 2 ^ n * ((x / 2) / 2 ^ n) := by
      nlinarith [Nat.div_add_mod x 2, Nat.div_add_mod (x / 2) (2 ^ n)]
    conv_rhs => rw [heq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

def constBitsWires (B wFalse wTrue x : ℕ) : List ℕ :=
  (List.range B).map (fun i => if x.testBit i then wTrue else wFalse)

lemma constBitsWires_length (B wFalse wTrue x : ℕ) :
    (constBitsWires B wFalse wTrue x).length = B := by
  simp [constBitsWires]

lemma constBitsWires_mem {B wFalse wTrue x M : ℕ} (hwf : wFalse < M) (hwt : wTrue < M) :
    ∀ w ∈ constBitsWires B wFalse wTrue x, w < M := by
  intro w hw
  simp only [constBitsWires, List.mem_map, List.mem_range] at hw
  rcases hw with ⟨i, _, rfl⟩
  split_ifs <;> assumption

lemma constBitsWires_bitsVal {B wFalse wTrue x : ℕ} (gs : List Gate) (inp : List Bool)
    (hwf : wireVal gs inp wFalse = false) (hwt : wireVal gs inp wTrue = true)
    (hx : x < 2 ^ B) :
    bitsVal ((constBitsWires B wFalse wTrue x).map (wireVal gs inp)) = x := by
  have hmap : (constBitsWires B wFalse wTrue x).map (wireVal gs inp) =
      (List.range B).map (fun i => x.testBit i) := by
    simp only [constBitsWires, List.map_map]
    apply List.map_congr_left
    intro i _
    cases h : x.testBit i <;> simp [h, hwf, hwt]
  rw [hmap, bitsVal_range_testBit, Nat.mod_eq_of_lt hx]

def gIncAux (n : ℕ) (gs : List Gate) (c : ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | x :: rest =>
    let s := gXor n gs x c
    let c' := gAnd n s.1 x c
    let r2 := gIncAux n c'.1 c'.2 rest
    (r2.1, s.2 :: r2.2)

lemma gIncAux_spec {n : ℕ} {gs : List Gate} {c : ℕ} (acc : List ℕ)
    (hgs : GoodGates n gs) (hc : c < n + gs.length) (hacc : ∀ w ∈ acc, w < n + gs.length) :
    let r := gIncAux n gs c acc
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 5 * acc.length ∧
      r.2.length = acc.length ∧ (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        bitsVal (r.2.map (wireVal r.1 inp)) =
          (bitsVal (acc.map (wireVal gs inp)) + (wireVal gs inp c).toNat) % 2 ^ acc.length := by
  induction acc generalizing gs c with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gIncAux], by simp [gIncAux], by simp [gIncAux], ?_⟩
    intro inp _
    simp [gIncAux, bitsVal, Nat.mod_one]
  | cons x rest ih =>
    have hx := hacc x (by simp)
    dsimp only [gIncAux]
    have s1 := gXor_spec hgs hx hc
    have s2 := gAnd_spec s1.2.1 (lt_of_lt_of_le hx (by have := s1.2.2.1; omega))
      (lt_of_lt_of_le hc (by have := s1.2.2.1; omega))
    have h12 : Extends gs (gAnd n (gXor n gs x c).1 x c).1 := extends_trans s1.1 s2.1
    have ih' := ih s2.2.1 s2.2.2.2.1 (fun w hw => by
      have h1 := s1.2.2.1; have h2 := s2.2.2.1
      exact lt_of_lt_of_le (hacc w (by simp [hw])) (by omega))
    refine ⟨extends_trans h12 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 := s1.2.2.1; have h2 := s2.2.2.1; have h3 := ih'.2.2.1; simp only [List.length_cons]; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le s1.2.2.2.1 (by have := extends_length s2.1; have := extends_length ih'.1; omega)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp
      simp only [List.map_cons, bitsVal, List.length_cons]
      rw [wireVal_extends (extends_trans s2.1 ih'.1) hinp s1.2.2.2.1, s1.2.2.2.2 inp hinp,
        ih'.2.2.2.2.2 inp hinp, s2.2.2.2.2 inp hinp, wireVal_extends s1.1 hinp hx, wireVal_extends s1.1 hinp hc]
      have hrest : rest.map (wireVal (gAnd n (gXor n gs x c).1 x c).1 inp) = rest.map (wireVal gs inp) :=
        listVal_extends h12 hinp (fun w hw => hacc w (by simp [hw]))
      rw [hrest]
      set X := wireVal gs inp x
      set C := wireVal gs inp c
      set V := bitsVal (rest.map (wireVal gs inp))
      set L := rest.length
      have hsc : (xor X C).toNat + 2 * (X && C).toNat = X.toNat + C.toNat := by
        cases X <;> cases C <;> decide
      have hpow : 2 ^ (L + 1) = 2 * 2 ^ L := Nat.pow_succ'
      have hdiv : (V + (X && C).toNat) = 2 ^ L * ((V + (X && C).toNat) / 2 ^ L) +
          (V + (X && C).toNat) % 2 ^ L := (Nat.div_add_mod _ _).symm
      have hlt : (xor X C).toNat + 2 * ((V + (X && C).toNat) % 2 ^ L) < 2 * 2 ^ L := by
        have h1 : (xor X C).toNat ≤ 1 := by cases (xor X C) <;> decide
        have h2 : (V + (X && C).toNat) % 2 ^ L < 2 ^ L := Nat.mod_lt _ (Nat.pow_pos (by decide))
        omega
      have hmod_eq : (X.toNat + 2 * V + C.toNat) =
          ((xor X C).toNat + 2 * ((V + (X && C).toNat) % 2 ^ L)) +
            2 * 2 ^ L * ((V + (X && C).toNat) / 2 ^ L) := by
        calc X.toNat + 2 * V + C.toNat
            = (X.toNat + C.toNat) + 2 * V := by ring
          _ = ((xor X C).toNat + 2 * (X && C).toNat) + 2 * V := by rw [hsc]
          _ = (xor X C).toNat + 2 * (V + (X && C).toNat) := by ring
          _ = (xor X C).toNat + 2 * (2 ^ L * ((V + (X && C).toNat) / 2 ^ L) +
                (V + (X && C).toNat) % 2 ^ L) := by rw [← hdiv]
          _ = ((xor X C).toNat + 2 * ((V + (X && C).toNat) % 2 ^ L)) +
                2 * 2 ^ L * ((V + (X && C).toNat) / 2 ^ L) := by ring
      rw [hpow]
      conv_rhs => rw [hmod_eq]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

def gCmpAux (n : ℕ) (gs : List Gate) (acc : ℕ) : List (ℕ × ℕ) → List Gate × ℕ
  | [] => (gs, acc)
  | (x, y) :: rest =>
    let nx := gNot n gs x
    let yo := gOr n nx.1 y acc
    let t1 := gAnd n yo.1 nx.2 yo.2
    let t2 := gAnd n t1.1 y acc
    let nxt := gOr n t2.1 t1.2 t2.2
    gCmpAux n nxt.1 nxt.2 rest

def gCmpBits (n : ℕ) (gs : List Gate) (init : ℕ) (xs ys : List ℕ) : List Gate × ℕ :=
  gCmpAux n gs init (xs.zip ys)

lemma gCmpAux_spec {n : ℕ} {gs : List Gate} {acc : ℕ} (ps : List (ℕ × ℕ))
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length)
    (hps : ∀ ab ∈ ps, ab.1 < n + gs.length ∧ ab.2 < n + gs.length) :
    let r := gCmpAux n gs acc ps
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 5 * ps.length ∧ r.2 < n + r.1.length ∧
      ∀ inp : List Bool, inp.length = n →
        let xs := ps.map (fun ab => wireVal gs inp ab.1)
        let ys := ps.map (fun ab => wireVal gs inp ab.2)
        wireVal r.1 inp r.2 =
          decide (bitsVal xs < bitsVal ys ∨ (bitsVal xs = bitsVal ys ∧ wireVal gs inp acc = true)) := by
  induction ps generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gCmpAux], hacc, ?_⟩
    intro inp _
    simp [gCmpAux, bitsVal]
  | cons ab rest ih =>
    rcases ab with ⟨x, y⟩
    have hxy := hps (x, y) (by simp)
    have hx : x < n + gs.length := hxy.1
    have hy : y < n + gs.length := hxy.2
    dsimp only [gCmpAux]
    set r1 := gNot n gs x
    set r2 := gOr n r1.1 y acc
    set r3 := gAnd n r2.1 r1.2 r2.2
    set r4 := gAnd n r3.1 y acc
    set r5 := gOr n r4.1 r3.2 r4.2
    have s1 := gNot_spec hgs hx
    have hle1 : gs.length ≤ r1.1.length := extends_length s1.1
    have s2 := gOr_spec s1.2.1 (lt_of_lt_of_le hy (Nat.add_le_add_left hle1 n))
      (lt_of_lt_of_le hacc (Nat.add_le_add_left hle1 n))
    have hle2 : r1.1.length ≤ r2.1.length := extends_length s2.1
    have hle12 : gs.length ≤ r2.1.length := le_trans hle1 hle2
    have s3 := gAnd_spec s2.2.1 (lt_of_lt_of_le s1.2.2.2.1 (Nat.add_le_add_left hle2 n)) s2.2.2.2.1
    have hle3 : r2.1.length ≤ r3.1.length := extends_length s3.1
    have hle13 : gs.length ≤ r3.1.length := le_trans hle12 hle3
    have s4 := gAnd_spec s3.2.1 (lt_of_lt_of_le hy (Nat.add_le_add_left hle13 n))
      (lt_of_lt_of_le hacc (Nat.add_le_add_left hle13 n))
    have hle4 : r3.1.length ≤ r4.1.length := extends_length s4.1
    have s5 := gOr_spec s4.2.1 (lt_of_lt_of_le s3.2.2.2.1 (Nat.add_le_add_left hle4 n)) s4.2.2.2.1
    have h15 : Extends gs r5.1 :=
      extends_trans s1.1 (extends_trans s2.1 (extends_trans s3.1 (extends_trans s4.1 s5.1)))
    have hlen15 : r5.1.length = gs.length + 5 := by
      have h1 : r1.1.length = gs.length + 1 := s1.2.2.1
      have h2 : r2.1.length = r1.1.length + 1 := s2.2.2.1
      have h3 : r3.1.length = r2.1.length + 1 := s3.2.2.1
      have h4 : r4.1.length = r3.1.length + 1 := s4.2.2.1
      have h5 : r5.1.length = r4.1.length + 1 := s5.2.2.1
      omega
    have ih' := ih s5.2.1 s5.2.2.2.1 (fun uv huv => by
      have h := hps uv (by simp [huv])
      exact ⟨lt_of_lt_of_le h.1 (by omega), lt_of_lt_of_le h.2 (by omega)⟩)
    refine ⟨extends_trans h15 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ?_⟩
    · have h6 : (gCmpAux n r5.1 r5.2 rest).1.length = r5.1.length + 5 * rest.length := ih'.2.2.1
      rw [h6, hlen15]; simp only [List.length_cons]; ring
    · intro inp hinp
      rw [ih'.2.2.2.2 inp hinp]
      have hxs : rest.map (fun ab => wireVal r5.1 inp ab.1) = rest.map (fun ab => wireVal gs inp ab.1) := by
        apply List.map_congr_left
        intro uv huv
        exact wireVal_extends h15 hinp (hps uv (by simp [huv])).1
      have hys : rest.map (fun ab => wireVal r5.1 inp ab.2) = rest.map (fun ab => wireVal gs inp ab.2) := by
        apply List.map_congr_left
        intro uv huv
        exact wireVal_extends h15 hinp (hps uv (by simp [huv])).2
      rw [hxs, hys]
      have hnxt : wireVal r5.1 inp r5.2 =
          ((!(wireVal gs inp x) && (wireVal gs inp y || wireVal gs inp acc)) ||
            (wireVal gs inp y && wireVal gs inp acc)) := by
        rw [s5.2.2.2.2 inp hinp, wireVal_extends s4.1 hinp s3.2.2.2.1, s3.2.2.2.2 inp hinp,
          wireVal_extends s2.1 hinp s1.2.2.2.1, s1.2.2.2.2 inp hinp, s2.2.2.2.2 inp hinp,
          wireVal_extends s1.1 hinp hy, wireVal_extends s1.1 hinp hacc, s4.2.2.2.2 inp hinp,
          wireVal_extends (extends_trans s1.1 (extends_trans s2.1 s3.1)) hinp hy,
          wireVal_extends (extends_trans s1.1 (extends_trans s2.1 s3.1)) hinp hacc]
      rw [hnxt]
      simp only [List.map_cons, bitsVal]
      set X := bitsVal (rest.map (fun ab => wireVal gs inp ab.1))
      set Y := bitsVal (rest.map (fun ab => wireVal gs inp ab.2))
      set bx := wireVal gs inp x
      set by_ := wireVal gs inp y
      set ba := wireVal gs inp acc
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      rcases lt_trichotomy X Y with hXY | hXY | hXY
      · have h1 : bx.toNat + 2 * X < by_.toNat + 2 * Y := by
          cases bx <;> cases by_ <;> simp <;> omega
        simp [hXY, h1]
      · rw [hXY]
        cases bx <;> cases by_ <;> cases ba <;> simp <;> omega
      · have h1 : ¬ (bx.toNat + 2 * X < by_.toNat + 2 * Y) := by
          cases bx <;> cases by_ <;> simp <;> omega
        have h2 : bx.toNat + 2 * X ≠ by_.toNat + 2 * Y := by
          cases bx <;> cases by_ <;> simp <;> omega
        simp [h1, h2, show ¬ (X < Y) by omega, show X ≠ Y by omega]

lemma gCmpBits_spec {n : ℕ} {gs : List Gate} {init : ℕ} (xs ys : List ℕ)
    (hgs : GoodGates n gs) (hinit : init < n + gs.length)
    (hxs : ∀ w ∈ xs, w < n + gs.length) (hys : ∀ w ∈ ys, w < n + gs.length) :
    let r := gCmpBits n gs init xs ys
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 5 * xs.length ∧ r.2 < n + r.1.length ∧
      ∀ inp : List Bool, inp.length = n → xs.length = ys.length →
        wireVal r.1 inp r.2 =
          decide (bitsVal (xs.map (wireVal gs inp)) < bitsVal (ys.map (wireVal gs inp)) ∨
            (bitsVal (xs.map (wireVal gs inp)) = bitsVal (ys.map (wireVal gs inp)) ∧
              wireVal gs inp init = true)) := by
  dsimp only [gCmpBits]
  have hps : ∀ ab ∈ xs.zip ys, ab.1 < n + gs.length ∧ ab.2 < n + gs.length := by
    intro ab hab; have h := List.of_mem_zip hab; exact ⟨hxs ab.1 h.1, hys ab.2 h.2⟩
  have s := gCmpAux_spec (xs.zip ys) hgs hinit hps
  refine ⟨s.1, s.2.1, ?_, s.2.2.2.1, ?_⟩
  · have hzl : (xs.zip ys).length ≤ xs.length := by simp
    omega
  · intro inp hinp hlen
    rw [s.2.2.2.2 inp hinp]
    have hm1 : (xs.zip ys).map (fun ab => wireVal gs inp ab.1) = xs.map (wireVal gs inp) := by
      have : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (le_of_eq hlen)
      conv_rhs => rw [← this, List.map_map]
      apply List.map_congr_left
      intro ab _; rfl
    have hm2 : (xs.zip ys).map (fun ab => wireVal gs inp ab.2) = ys.map (wireVal gs inp) := by
      have : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (le_of_eq hlen.symm)
      conv_rhs => rw [← this, List.map_map]
      apply List.map_congr_left
      intro ab _; rfl
    rw [hm1, hm2]

def gPrefixPopcount (n : ℕ) (gs : List Gate) (acc : List ℕ) :
    List ℕ → List Gate × (List ℕ × List (List ℕ))
  | [] => (gs, (acc, []))
  | x :: rest =>
    let s := gIncAux n gs x acc
    let r2 := gPrefixPopcount n s.1 s.2 rest
    (r2.1, (r2.2.1, acc :: r2.2.2))

lemma gPrefixPopcount_spec {n B : ℕ} {gs : List Gate} (acc : List ℕ) (xs : List ℕ)
    (hgs : GoodGates n gs) (hlenB : acc.length = B)
    (hacc : ∀ w ∈ acc, w < n + gs.length) (hxs : ∀ w ∈ xs, w < n + gs.length) :
    let res := gPrefixPopcount n gs acc xs
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length = gs.length + 5 * B * xs.length ∧
      res.2.1.length = B ∧ (∀ w ∈ res.2.1, w < n + res.1.length) ∧
      res.2.2.length = xs.length ∧ (∀ r ∈ res.2.2, r.length = B ∧ ∀ w ∈ r, w < n + res.1.length) ∧
      ∀ inp : List Bool, inp.length = n →
        bitsVal (acc.map (wireVal gs inp)) + xs.length < 2 ^ B →
        bitsVal (res.2.1.map (wireVal res.1 inp)) =
          bitsVal (acc.map (wireVal gs inp)) + (xs.map (wireVal gs inp)).count true ∧
        ∀ i (hi : i < xs.length),
          bitsVal ((res.2.2.getD i []).map (wireVal res.1 inp)) =
            bitsVal (acc.map (wireVal gs inp)) + ((xs.take i).map (wireVal gs inp)).count true := by
  induction xs generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gPrefixPopcount], hlenB, hacc,
      by simp [gPrefixPopcount], by simp [gPrefixPopcount], ?_⟩
    intro inp _ _
    refine ⟨by simp [gPrefixPopcount], fun i hi => by simp at hi⟩
  | cons x rest ih =>
    have hx := hxs x (by simp)
    dsimp only [gPrefixPopcount]
    have s1 := gIncAux_spec acc hgs hx hacc
    have h1 : (gIncAux n gs x acc).1.length = gs.length + 5 * acc.length := s1.2.2.1
    have h2 : (gIncAux n gs x acc).2.length = B := s1.2.2.2.1.trans hlenB
    have ih' := ih (gIncAux n gs x acc).2 s1.2.1 h2 s1.2.2.2.2.1
      (fun w hw => lt_of_lt_of_le (hxs w (by simp [hw])) (by omega))
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ih'.2.2.2.2.1,
      by simp [ih'.2.2.2.2.2.1], ?_, ?_⟩
    · have h3 := ih'.2.2.1; simp only [List.length_cons]; rw [hlenB] at h1; nlinarith
    · intro r hr
      simp only [List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨hlenB, fun w hw => lt_of_lt_of_le (hacc w hw)
          (by have := extends_length (extends_trans s1.1 ih'.1); omega)⟩
      · exact ih'.2.2.2.2.2.2.1 r hr
    · intro inp hinp hbound
      have hV1 : bitsVal ((gIncAux n gs x acc).2.map (wireVal (gIncAux n gs x acc).1 inp)) =
          bitsVal (acc.map (wireVal gs inp)) + (wireVal gs inp x).toNat := by
        rw [s1.2.2.2.2.2 inp hinp, hlenB]
        apply Nat.mod_eq_of_lt
        have : (wireVal gs inp x).toNat ≤ 1 := by cases (wireVal gs inp x) <;> decide
        simp only [List.length_cons] at hbound
        omega
      have hbound2 : bitsVal ((gIncAux n gs x acc).2.map (wireVal (gIncAux n gs x acc).1 inp)) +
          rest.length < 2 ^ B := by
        rw [hV1]
        have : (wireVal gs inp x).toNat ≤ 1 := by cases (wireVal gs inp x) <;> decide
        simp only [List.length_cons] at hbound
        omega
      have hih := ih'.2.2.2.2.2.2.2 inp hinp hbound2
      have hrest_map : rest.map (wireVal (gIncAux n gs x acc).1 inp) = rest.map (wireVal gs inp) :=
        listVal_extends s1.1 hinp (fun w hw => hxs w (by simp [hw]))
      refine ⟨?_, ?_⟩
      · rw [hih.1, hV1, hrest_map]
        simp only [List.map_cons, List.count_cons]
        cases (wireVal gs inp x) <;> simp <;> omega
      · intro i hi
        cases i with
        | zero =>
          simp only [List.getD_cons_zero, List.take_zero, List.map_nil, List.count_nil, Nat.add_zero]
          exact congrArg bitsVal (listVal_extends (extends_trans s1.1 ih'.1) hinp hacc)
        | succ i =>
          have hi' : i < rest.length := by simpa using hi
          simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.count_cons]
          rw [hih.2 i hi', hV1]
          have htake_map : (rest.take i).map (wireVal (gIncAux n gs x acc).1 inp) =
              (rest.take i).map (wireVal gs inp) :=
            listVal_extends s1.1 hinp (fun w hw => hxs w (by simp [List.mem_of_mem_take hw]))
          rw [htake_map]
          cases (wireVal gs inp x) <;> simp <;> omega

def bitsFn (n x : ℕ) : List Bool := (List.range n).map (fun i => x.testBit i)

def bankFn (k m : ℕ) (A : Fin m → Fin (2 ^ k)) : List Bool :=
  (List.finRange m).flatMap (fun j => bitsFn k (A j).val)

def schedFn (k r : ℕ) (c : Fin r → Fin (2 ^ k)) : List Bool :=
  (List.finRange r).flatMap (fun j => bitsFn k (c j).val)

def mkInp (k r m : ℕ) (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) : List Bool :=
  bitsFn k u.val ++ bitsFn k v.val ++ schedFn k r cr ++ schedFn k r cc ++
    bankFn k m A ++ bankFn k m B ++ List.ofFn y ++ bitsFn (k + 1) t.val

lemma bitsFn_length (n x : ℕ) : (bitsFn n x).length = n := by simp [bitsFn]

lemma flatMap_const_length {α : Type*} (l : List α) (f : α → List Bool) (k : ℕ)
    (hf : ∀ a ∈ l, (f a).length = k) : (l.flatMap f).length = l.length * k := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hf a (by simp), ih (fun x hx => hf x (by simp [hx]))]
    ring

lemma bankFn_length (k m : ℕ) (A : Fin m → Fin (2 ^ k)) : (bankFn k m A).length = m * k := by
  unfold bankFn
  rw [flatMap_const_length _ _ k (fun j _ => bitsFn_length k (A j).val), List.length_finRange]

lemma schedFn_length (k r : ℕ) (c : Fin r → Fin (2 ^ k)) : (schedFn k r c).length = r * k := by
  unfold schedFn
  rw [flatMap_const_length _ _ k (fun j _ => bitsFn_length k (c j).val), List.length_finRange]

lemma mkInp_length (k r m : ℕ) (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) :
    (mkInp k r m u v cr cc A B y t).length = 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  unfold mkInp
  simp only [List.length_append, bitsFn_length, schedFn_length, bankFn_length, List.length_ofFn]
  ring

lemma getD_append_left {α : Type*} (l1 l2 : List α) (d : α) {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (d : α) {i : ℕ} (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma finRange_flatMap_getD {L k : ℕ} (f : Fin L → List Bool) (hf : ∀ j, (f j).length = k)
    (j : Fin L) {i : ℕ} (hi : i < k) :
    ((List.finRange L).flatMap f).getD (j.val * k + i) false = (f j).getD i false := by
  induction L with
  | zero => exact j.elim0
  | succ L ih =>
    rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hlenL : ((List.finRange L).map Fin.castSucc |>.flatMap f).length = L * k := by
      rw [flatMap_const_length _ _ k (fun x _ => hf x), List.length_map, List.length_finRange]
    by_cases hj : j.val < L
    · have hlt : j.val * k + i < L * k := by
        have h1 : (j.val + 1) * k ≤ L * k := Nat.mul_le_mul_right k hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega
      rw [getD_append_left _ _ false (by rw [hlenL]; exact hlt)]
      rw [List.flatMap_map]
      exact ih (fun x => f x.castSucc) (fun x => hf x.castSucc) ⟨j.val, hj⟩
    · have hjeq : j = Fin.last L := Fin.ext (by have := j.isLt; dsimp [Fin.last]; omega)
      subst hjeq
      have hge : L * k ≤ (Fin.last L).val * k + i := by simp [Fin.last]
      rw [getD_append_right _ _ false (by rw [hlenL]; exact hge)]
      simp [hlenL, Fin.last]

lemma bitsFn_getD (n x i : ℕ) (hi : i < n) :
    (bitsFn n x).getD i false = x.testBit i := by
  simp [bitsFn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

lemma wireVal_input {n : ℕ} {gs : List Gate} (hgs : GoodGates n gs) {inp : List Bool}
    (hinp : inp.length = n) {w : ℕ} (hw : w < n) :
    wireVal gs inp w = inp.getD w false := by
  unfold wireVal
  rw [evalGates_getD_lt gs inp (by rw [hinp]; exact hw)]

def uWires (k : ℕ) : List ℕ := List.range k
def vWires (k : ℕ) : List ℕ := (List.range k).map (k + ·)
def crWires (k : ℕ) (j : Fin r) : List ℕ := (List.range k).map (2 * k + j.val * k + ·)
def ccWires (k r : ℕ) (j : Fin r) : List ℕ := (List.range k).map (2 * k + r * k + j.val * k + ·)
def aWires (k r : ℕ) (j : Fin m) : List ℕ := (List.range k).map (2 * k + 2 * r * k + j.val * k + ·)
def bWires (k r m : ℕ) (j : Fin m) : List ℕ := (List.range k).map (2 * k + 2 * r * k + m * k + j.val * k + ·)
def yWires (k r m : ℕ) : List ℕ := (List.finRange m).map (fun j => 2 * k + 2 * r * k + 2 * m * k + j.val)
def tWires (k r m : ℕ) : List ℕ := (List.range (k + 1)).map (fun i => 2 * k + 2 * r * k + 2 * m * k + m + i)

lemma uWires_mem (k : ℕ) {w : ℕ} (hw : w ∈ uWires k) : w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [uWires, List.mem_range] at hw; omega
lemma vWires_mem (k : ℕ) {w : ℕ} (hw : w ∈ vWires k) : w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [vWires, List.mem_map, List.mem_range] at hw; rcases hw with ⟨i, hi, rfl⟩; omega
lemma crWires_mem {k r : ℕ} (j : Fin r) {w : ℕ} (hw : w ∈ crWires k j) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [crWires, List.mem_map, List.mem_range] at hw; rcases hw with ⟨i, hi, rfl⟩
  have : (j.val + 1) * k ≤ r * k := Nat.mul_le_mul_right k j.isLt
  nlinarith
lemma ccWires_mem {k r : ℕ} (j : Fin r) {w : ℕ} (hw : w ∈ ccWires k r j) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [ccWires, List.mem_map, List.mem_range] at hw; rcases hw with ⟨i, hi, rfl⟩
  have : (j.val + 1) * k ≤ r * k := Nat.mul_le_mul_right k j.isLt
  nlinarith
lemma aWires_mem {k r m : ℕ} (j : Fin m) {w : ℕ} (hw : w ∈ aWires k r j) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [aWires, List.mem_map, List.mem_range] at hw; rcases hw with ⟨i, hi, rfl⟩
  have : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k j.isLt
  nlinarith
lemma bWires_mem {k r m : ℕ} (j : Fin m) {w : ℕ} (hw : w ∈ bWires k r m j) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [bWires, List.mem_map, List.mem_range] at hw; rcases hw with ⟨i, hi, rfl⟩
  have : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k j.isLt
  nlinarith
lemma yWires_mem (k r m : ℕ) {w : ℕ} (hw : w ∈ yWires k r m) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [yWires, List.mem_map, List.mem_finRange] at hw; rcases hw with ⟨j, _, rfl⟩; omega
lemma tWires_mem (k r m : ℕ) {w : ℕ} (hw : w ∈ tWires k r m) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [tWires, List.mem_map, List.mem_range] at hw; rcases hw with ⟨i, hi, rfl⟩; omega

lemma mkInp_getD_u {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) {i : ℕ} (hi : i < k) :
    (mkInp k r m u v cr cc A B y t).getD i false = u.val.testBit i := by
  unfold mkInp
  simp only [List.append_assoc]
  rw [getD_append_left _ _ false (by rw [bitsFn_length]; exact hi), bitsFn_getD k u.val i hi]

lemma mkInp_getD_v {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) {i : ℕ} (hi : i < k) :
    (mkInp k r m u v cr cc A B y t).getD (k + i) false = v.val.testBit i := by
  unfold mkInp
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length,
    show k + i - k = i by omega, getD_append_left _ _ false (by rw [bitsFn_length]; exact hi),
    bitsFn_getD k v.val i hi]

lemma mkInp_getD_cr {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    (j : Fin r) {i : ℕ} (hi : i < k) :
    (mkInp k r m u v cr cc A B y t).getD (2 * k + j.val * k + i) false = (cr j).val.testBit i := by
  unfold mkInp
  have hlt : j.val * k + i < r * k := by
    have : (j.val + 1) * k ≤ r * k := Nat.mul_le_mul_right k j.isLt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [show 2 * k + j.val * k + i - k - k = j.val * k + i by omega]
  rw [getD_append_left _ _ false (by rw [schedFn_length]; exact hlt)]
  unfold schedFn
  rw [finRange_flatMap_getD _ (fun _ => bitsFn_length _ _) j hi, bitsFn_getD k (cr j).val i hi]

lemma mkInp_getD_cc {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    (j : Fin r) {i : ℕ} (hi : i < k) :
    (mkInp k r m u v cr cc A B y t).getD (2 * k + r * k + j.val * k + i) false = (cc j).val.testBit i := by
  unfold mkInp
  have hlt : j.val * k + i < r * k := by
    have : (j.val + 1) * k ≤ r * k := Nat.mul_le_mul_right k j.isLt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [show 2 * k + r * k + j.val * k + i - k - k - r * k = j.val * k + i by omega]
  rw [getD_append_left _ _ false (by rw [schedFn_length]; exact hlt)]
  unfold schedFn
  rw [finRange_flatMap_getD _ (fun _ => bitsFn_length _ _) j hi, bitsFn_getD k (cc j).val i hi]

lemma mkInp_getD_A {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    (j : Fin m) {i : ℕ} (hi : i < k) :
    (mkInp k r m u v cr cc A B y t).getD (2 * k + 2 * r * k + j.val * k + i) false = (A j).val.testBit i := by
  unfold mkInp
  have hlt : j.val * k + i < m * k := by
    have : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k j.isLt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have h2r : 2 * r * k = r * k + r * k := by ring
  have h2m : 2 * m * k = m * k + m * k := by ring
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [show 2 * k + 2 * r * k + j.val * k + i - k - k - r * k - r * k = j.val * k + i by omega]
  rw [getD_append_left _ _ false (by rw [bankFn_length]; exact hlt)]
  unfold bankFn
  rw [finRange_flatMap_getD _ (fun _ => bitsFn_length _ _) j hi, bitsFn_getD k (A j).val i hi]

lemma mkInp_getD_B {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    (j : Fin m) {i : ℕ} (hi : i < k) :
    (mkInp k r m u v cr cc A B y t).getD (2 * k + 2 * r * k + m * k + j.val * k + i) false = (B j).val.testBit i := by
  unfold mkInp
  have hlt : j.val * k + i < m * k := by
    have : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k j.isLt
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have h2r : 2 * r * k = r * k + r * k := by ring
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [bankFn_length]; omega), bankFn_length]
  rw [show 2 * k + 2 * r * k + m * k + j.val * k + i - k - k - r * k - r * k - m * k = j.val * k + i by omega]
  rw [getD_append_left _ _ false (by rw [bankFn_length]; exact hlt)]
  unfold bankFn
  rw [finRange_flatMap_getD _ (fun _ => bitsFn_length _ _) j hi, bitsFn_getD k (B j).val i hi]

lemma mkInp_getD_y {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    (j : Fin m) :
    (mkInp k r m u v cr cc A B y t).getD (2 * k + 2 * r * k + 2 * m * k + j.val) false = y j := by
  unfold mkInp
  have h2r : 2 * r * k = r * k + r * k := by ring
  have h2m : 2 * m * k = m * k + m * k := by ring
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [bankFn_length]; omega), bankFn_length]
  rw [getD_append_right _ _ false (by rw [bankFn_length]; omega), bankFn_length]
  rw [show 2 * k + 2 * r * k + 2 * m * k + j.val - k - k - r * k - r * k - m * k - m * k = j.val by omega]
  rw [getD_append_left _ _ false (by simp [j.isLt])]
  simp [List.getD_eq_getElem?_getD, j.isLt]

lemma mkInp_getD_t {k r m : ℕ} (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (t : Fin (2 ^ (k + 1)))
    {i : ℕ} (hi : i < k + 1) :
    (mkInp k r m u v cr cc A B y t).getD (2 * k + 2 * r * k + 2 * m * k + m + i) false = t.val.testBit i := by
  unfold mkInp
  have h2r : 2 * r * k = r * k + r * k := by ring
  have h2m : 2 * m * k = m * k + m * k := by ring
  simp only [List.append_assoc]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [bitsFn_length]; omega), bitsFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [schedFn_length]; omega), schedFn_length]
  rw [getD_append_right _ _ false (by rw [bankFn_length]; omega), bankFn_length]
  rw [getD_append_right _ _ false (by rw [bankFn_length]; omega), bankFn_length]
  rw [getD_append_right _ _ false (by simp; omega), List.length_ofFn]
  rw [show 2 * k + 2 * r * k + 2 * m * k + m + i - k - k - r * k - r * k - m * k - m * k - m = i by omega]
  exact bitsFn_getD (k + 1) t.val i hi

def rowVecWires (k r m : ℕ) (cut : Fin k) (col : Bool) (p : Fin k) : List ℕ :=
  let bit := (cut.val + p.val + delayFn r col) % k
  let base := if col then 2 * k + 2 * r * k + m * k else 2 * k + 2 * r * k
  (List.finRange m).map (fun j => base + j.val * k + bit)

lemma rowVecWires_length (k r m : ℕ) (cut : Fin k) (col : Bool) (p : Fin k) :
    (rowVecWires k r m cut col p).length = m := by
  simp [rowVecWires]

lemma rowVecWires_mem {k r m : ℕ} (hk : 0 < k) (cut : Fin k) (col : Bool) (p : Fin k)
    {w : ℕ} (hw : w ∈ rowVecWires k r m cut col p) :
    w < 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) := by
  simp only [rowVecWires, List.mem_map, List.mem_finRange] at hw
  rcases hw with ⟨j, _, rfl⟩
  have hbit : (cut.val + p.val + delayFn r col) % k < k := Nat.mod_lt _ hk
  have hjk : (j.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k j.isLt
  cases col <;> simp <;> nlinarith

lemma rowVecWires_map {k r m : ℕ} (hk : 0 < k) {gs : List Gate}
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
    (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (cut : Fin k) (col : Bool) (p : Fin k) :
    (rowVecWires k r m cut col p).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
      List.ofFn (rowVec k r m A B cut col p) := by
  set inp := mkInp k r m u v cr cc A B y t
  have hinp : inp.length = 2 * k + 2 * r * k + 2 * m * k + m + (k + 1) :=
    mkInp_length k r m u v cr cc A B y t
  have hbit : (cut.val + p.val + delayFn r col) % k < k := Nat.mod_lt _ hk
  have hof : List.ofFn (rowVec k r m A B cut col p) =
      (List.finRange m).map (rowVec k r m A B cut col p) := by
    apply List.ext_getElem <;> simp
  rw [hof]
  unfold rowVecWires
  rw [List.map_map]
  apply List.map_congr_left
  intro j _
  dsimp only [Function.comp_apply, rowVec]
  have hw : (if col then 2 * k + 2 * r * k + m * k else 2 * k + 2 * r * k) +
      j.val * k + (cut.val + p.val + delayFn r col) % k <
      2 * k + 2 * r * k + 2 * m * k + m + (k + 1) :=
    rowVecWires_mem hk cut col p (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  rw [wireVal_input hgs hinp hw]
  cases col
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact mkInp_getD_A u v cr cc A B y t j hbit
  · simp only [↓reduceIte]
    exact mkInp_getD_B u v cr cc A B y t j hbit

def initBasisWires (m wFalse wTrue : ℕ) : List (List ℕ) :=
  (List.finRange m).map fun a => (List.finRange m).map fun b => if a = b then wTrue else wFalse

lemma initBasisWires_length (m wFalse wTrue : ℕ) :
    (initBasisWires m wFalse wTrue).length = m := by
  simp [initBasisWires]

lemma initBasisWires_mem {m wFalse wTrue M : ℕ} (hwf : wFalse < M) (hwt : wTrue < M) :
    ∀ r ∈ initBasisWires m wFalse wTrue, ∀ w ∈ r, w < M := by
  intro r hr w hw
  simp only [initBasisWires, List.mem_map, List.mem_finRange] at hr
  rcases hr with ⟨a, _, rfl⟩
  simp only [List.mem_map, List.mem_finRange] at hw
  rcases hw with ⟨b, _, rfl⟩
  split_ifs <;> assumption

lemma initBasisWires_map {m wFalse wTrue : ℕ} (gs : List Gate) (inp : List Bool)
    (hwf : wireVal gs inp wFalse = false) (hwt : wireVal gs inp wTrue = true) (c : Fin m) :
    ((initBasisWires m wFalse wTrue).getD c.val []).map (wireVal gs inp) =
      List.ofFn (initBasis m c) := by
  have hrc : (initBasisWires m wFalse wTrue).getD c.val [] =
      (List.finRange m).map (fun b => if c = b then wTrue else wFalse) := by
    simp [initBasisWires, List.getD_eq_getElem?_getD, c.isLt]
  rw [hrc, List.map_map]
  have hof : List.ofFn (initBasis m c) = (List.finRange m).map (initBasis m c) := by
    apply List.ext_getElem <;> simp
  rw [hof]
  apply List.map_congr_left
  intro b _
  dsimp only [Function.comp_apply, initBasis]
  by_cases hcb : c = b <;> simp [hcb, hwf, hwt]

def gNullStepLoop (n wFalse : ℕ) (gs : List Gate) (m : ℕ) (basis : List (List ℕ)) :
    List (List ℕ) → List Gate × List (List ℕ)
  | [] => (gs, basis)
  | row :: rest =>
    let s := gNullStep n wFalse gs m basis row
    gNullStepLoop n wFalse s.1 m s.2 rest

lemma gNullStepLoop_spec {n wFalse : ℕ} {gs : List Gate} {m : ℕ} (basis : List (List ℕ))
    (rows : List (List ℕ))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hblen : basis.length = m) (hbasis : ∀ b ∈ basis, ∀ w ∈ b, w < n + gs.length)
    (hrows : ∀ r ∈ rows, r.length = m ∧ ∀ w ∈ r, w < n + gs.length) :
    let res := gNullStepLoop n wFalse gs m basis rows
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (22 * m * m + 5 * m) * rows.length ∧
      res.2.length = m ∧ (∀ b ∈ res.2, ∀ w ∈ b, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (B : Basis m) (rowFuns : List (Fin m → Bool)),
        inp.length = n → wireVal gs inp wFalse = false →
        (∀ c : Fin m, (basis.getD c.val []).map (wireVal gs inp) = List.ofFn (B c)) →
        rows.length = rowFuns.length →
        (∀ (k : ℕ) (hk1 : k < rows.length) (hk2 : k < rowFuns.length),
          (rows[k]'hk1).map (wireVal gs inp) = List.ofFn (rowFuns[k]'hk2)) →
        ∀ c : Fin m, (res.2.getD c.val []).map (wireVal res.1 inp) =
          List.ofFn (rowFuns.foldl nullStep B c) := by
  induction rows generalizing gs basis with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gNullStepLoop], hblen, hbasis, ?_⟩
    intro inp B rowFuns _ _ hB hlen _ c
    have hrf : rowFuns = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst hrf
    exact hB c
  | cons row rest ih =>
    have hrow := hrows row (by simp)
    dsimp only [gNullStepLoop]
    have s1 := gNullStep_spec m basis row hgs hwf hblen hbasis hrow.2
    have hle1 : gs.length ≤ (gNullStep n wFalse gs m basis row).1.length := extends_length s1.1
    have ih' := ih (gNullStep n wFalse gs m basis row).2 s1.2.1
      (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      s1.2.2.2.1 s1.2.2.2.2.1
      (fun r hr => have h := hrows r (by simp [hr]); ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
    refine ⟨extends_trans s1.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ih'.2.2.2.2.1, ?_⟩
    · have h1 : (gNullStep n wFalse gs m basis row).1.length ≤
          gs.length + 17 * m * m + 5 * m + 5 * row.length * m := s1.2.2.1
      have h2 : (gNullStepLoop n wFalse (gNullStep n wFalse gs m basis row).1 m
          (gNullStep n wFalse gs m basis row).2 rest).1.length ≤
          (gNullStep n wFalse gs m basis row).1.length + (22 * m * m + 5 * m) * rest.length := ih'.2.2.1
      rw [hrow.1] at h1
      simp only [List.length_cons]
      nlinarith
    · intro inp B rowFuns hinp hwf_val hB hlen hrows_eq c
      rcases rowFuns with _ | ⟨rf, rfs⟩
      · simp at hlen
      · simp only [List.foldl_cons]
        have hrf0 : row.map (wireVal gs inp) = List.ofFn rf :=
          hrows_eq 0 (by simp) (by simp)
        have hstep := s1.2.2.2.2.2 inp B rf hinp hwf_val hrf0 hB
        have hlen' : rest.length = rfs.length := by simpa using hlen
        refine ih'.2.2.2.2.2 inp (nullStep B rf) rfs hinp
          (by rw [wireVal_extends s1.1 hinp hwf, hwf_val]) hstep hlen' ?_ c
        intro idx h1 h2
        have hmem := (hrows (rest[idx]'h1) (by simp [List.getElem_mem])).2
        rw [listVal_extends s1.1 hinp hmem]
        exact hrows_eq (idx + 1) (by simp [h1]) (by simp [h2])

lemma condPairs_length (k r : ℕ) (i : Fin k) : (condPairs k r i).length ≤ 2 * k := by
  unfold condPairs
  calc ((allColP k).filter _).length ≤ (allColP k).length := List.length_filter_le _ _
    _ = 2 * k := by
      unfold allColP
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
        List.length_map, List.length_finRange]
      omega

def gSolveCutI (k r m n wFalse wTrue : ℕ) (gs : List Gate) (cut i : Fin k) :
    List Gate × (ℕ × List ℕ) :=
  let basis0 := initBasisWires m wFalse wTrue
  let rows := (condPairs k r i).map (fun cp => rowVecWires k r m cut cp.1 cp.2)
  let bRes := gNullStepLoop n wFalse gs m basis0 rows
  let vW := gVecXor n bRes.1 (rowVecWires k r m cut false i) (rowVecWires k r m cut true i)
  let eW := gMapDot n wFalse vW.1 vW.2 bRes.2
  let fW := gFirst n wFalse eW.1 eW.2
  let avW := gOrList n wFalse fW.1 eW.2
  let witW := gSelectMat n wFalse avW.1 fW.2 bRes.2 m
  (witW.1, (avW.2, witW.2))

lemma getD_mem_of_lt {α : Type*} (l : List (List α)) {i : ℕ} (hi : i < l.length) :
    l.getD i [] ∈ l := by
  have h : l.getD i [] = l[i]'hi := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rw [h]
  exact List.getElem_mem hi

lemma gSolveCutI_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse wTrue : ℕ}
    (cut i : Fin k)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwt : wTrue < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gSolveCutI k r m n wFalse wTrue gs cut i
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m ∧
      res.2.1 < n + res.1.length ∧
      res.2.2.length = m ∧ (∀ w ∈ res.2.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        wireVal gs (mkInp k r m u v cr cc A B y t) wTrue = true →
        wireVal res.1 (mkInp k r m u v cr cc A B y t) res.2.1 = availTab k r m A B cut i ∧
        res.2.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (witTab k r m A B cut i) := by
  intro n
  dsimp only [gSolveCutI]
  set basis0 := initBasisWires m wFalse wTrue
  set rows := (condPairs k r i).map (fun cp => rowVecWires k r m cut cp.1 cp.2)
  set bRes := gNullStepLoop n wFalse gs m basis0 rows
  set vW := gVecXor n bRes.1 (rowVecWires k r m cut false i) (rowVecWires k r m cut true i)
  set eW := gMapDot n wFalse vW.1 vW.2 bRes.2
  set fW := gFirst n wFalse eW.1 eW.2
  set avW := gOrList n wFalse fW.1 eW.2
  set witW := gSelectMat n wFalse avW.1 fW.2 bRes.2 m
  have hrows_ok : ∀ rw ∈ rows, rw.length = m ∧ ∀ w ∈ rw, w < n + gs.length := by
    intro rw hrw
    simp only [rows, List.mem_map] at hrw
    rcases hrw with ⟨cp, _, rfl⟩
    exact ⟨rowVecWires_length k r m cut cp.1 cp.2,
      fun w hw => lt_of_lt_of_le (rowVecWires_mem hk cut cp.1 cp.2 hw) (Nat.le_add_right n gs.length)⟩
  have sb := gNullStepLoop_spec basis0 rows hgs hwf (initBasisWires_length m wFalse wTrue)
    (initBasisWires_mem hwf hwt) hrows_ok
  have hle1 : gs.length ≤ bRes.1.length := extends_length sb.1
  have hrF : ∀ w ∈ rowVecWires k r m cut false i, w < n + bRes.1.length :=
    fun w hw => lt_of_lt_of_le (rowVecWires_mem hk cut false i hw) (by omega)
  have hrT : ∀ w ∈ rowVecWires k r m cut true i, w < n + bRes.1.length :=
    fun w hw => lt_of_lt_of_le (rowVecWires_mem hk cut true i hw) (by omega)
  have sv := gVecXor_spec (rowVecWires k r m cut false i) (rowVecWires k r m cut true i) sb.2.1 hrF hrT
  have hle2 : bRes.1.length ≤ vW.1.length := extends_length sv.1
  have hle12 : gs.length ≤ vW.1.length := le_trans hle1 hle2
  have se := gMapDot_spec vW.2 bRes.2 sv.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
    sv.2.2.2.2.1 (fun b hb w hw => lt_of_lt_of_le (sb.2.2.2.2.1 b hb w hw) (Nat.add_le_add_left hle2 n))
  have hle3 : vW.1.length ≤ eW.1.length := extends_length se.1
  have hle13 : gs.length ≤ eW.1.length := le_trans hle12 hle3
  have sf := gFirst_spec eW.2 se.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle13 n)) se.2.2.2.2.1
  have hle4 : eW.1.length ≤ fW.1.length := extends_length sf.1
  have hle14 : gs.length ≤ fW.1.length := le_trans hle13 hle4
  have sav := gOrList_spec eW.2 sf.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle14 n))
    (fun w hw => lt_of_lt_of_le (se.2.2.2.2.1 w hw) (Nat.add_le_add_left hle4 n))
  have hle5 : fW.1.length ≤ avW.1.length := extends_length sav.1
  have hle15 : gs.length ≤ avW.1.length := le_trans hle14 hle5
  have hle25 : bRes.1.length ≤ avW.1.length := le_trans hle2 (le_trans hle3 (le_trans hle4 hle5))
  have sw := gSelectMat_spec fW.2 bRes.2 m sav.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle15 n))
    (fun w hw => lt_of_lt_of_le (sf.2.2.2.2.1 w hw) (Nat.add_le_add_left hle5 n))
    (fun b hb w hw => lt_of_lt_of_le (sb.2.2.2.2.1 b hb w hw) (Nat.add_le_add_left hle25 n))
  have hext_all : Extends gs witW.1 :=
    extends_trans sb.1 (extends_trans sv.1 (extends_trans se.1 (extends_trans sf.1 (extends_trans sav.1 sw.1))))
  refine ⟨hext_all, sw.2.1, ?_, lt_of_lt_of_le sav.2.2.2.1 (Nat.add_le_add_left (extends_length sw.1) n),
    sw.2.2.2.1, sw.2.2.2.2.1, ?_⟩
  · have h1 := sb.2.2.1
    have h2 := sv.2.2.1
    have h3 := se.2.2.1
    have h4 := sf.2.2.1
    have h5 := sav.2.2.1
    have h6 := sw.2.2.1
    have hcl := condPairs_length k r i
    have hrlen : rows.length ≤ 2 * k := by simp [rows, hcl]
    have hrl1 : (rowVecWires k r m cut false i).length = m := rowVecWires_length k r m cut false i
    have hvlen : vW.2.length = m := by rw [sv.2.2.2.1, hrl1, rowVecWires_length]; simp
    have helen : eW.2.length = m := by rw [se.2.2.2.1, sb.2.2.2.1]
    have hflen : fW.2.length = m := by rw [sf.2.2.2.1, helen]
    change bRes.1.length ≤ gs.length + (22 * m * m + 5 * m) * rows.length at h1
    change vW.1.length ≤ bRes.1.length + 4 * (rowVecWires k r m cut false i).length at h2
    change eW.1.length ≤ vW.1.length + 5 * vW.2.length * bRes.2.length at h3
    change fW.1.length ≤ eW.1.length + 3 * eW.2.length at h4
    change avW.1.length = fW.1.length + eW.2.length at h5
    change witW.1.length ≤ avW.1.length + 5 * fW.2.length * m at h6
    rw [hrl1] at h2
    rw [hvlen, sb.2.2.2.1] at h3
    rw [helen] at h4 h5
    rw [hflen] at h6
    have hmul : (22 * m * m + 5 * m) * rows.length ≤ (22 * m * m + 5 * m) * (2 * k) :=
      Nat.mul_le_mul_left _ hrlen
    nlinarith
  · intro u v cr cc A B y t hwf_val hwt_val
    set inp := mkInp k r m u v cr cc A B y t
    have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
    let rowFuns := (condPairs k r i).map (fun cp => rowVec k r m A B cut cp.1 cp.2)
    have hB_final : ∀ c : Fin m, (bRes.2.getD c.val []).map (wireVal bRes.1 inp) =
        List.ofFn (rowFuns.foldl nullStep (initBasis m) c) := by
      refine sb.2.2.2.2.2 inp (initBasis m) rowFuns hinp hwf_val
        (fun c => initBasisWires_map gs inp hwf_val hwt_val c) (by simp [rows, rowFuns]) ?_
      intro idx h1 h2
      simp only [rows, rowFuns, List.getElem_map]
      exact rowVecWires_map hk hgs u v cr cc A B y t cut _ _
    set B_final := (condPairs k r i).foldl
      (fun Bf cp => nullStep Bf (rowVec k r m A B cut cp.1 cp.2)) (initBasis m)
    have hBf_eq : rowFuns.foldl nullStep (initBasis m) = B_final := by
      simp only [rowFuns, B_final, List.foldl_map]
    rw [hBf_eq] at hB_final
    let v_f : Fin m → Bool := fun j => xor (rowVec k r m A B cut false i j) (rowVec k r m A B cut true i j)
    let e_f : Fin m → Bool := fun c => dotBool v_f (B_final c)
    let first_f : Fin m → Bool := fun c => e_f c && !prefScanAux e_f c.val
    have hv_val : vW.2.map (wireVal vW.1 inp) = List.ofFn v_f := by
      refine sv.2.2.2.2.2 inp m (rowVec k r m A B cut false i) (rowVec k r m A B cut true i) hinp ?_ ?_
      · rw [listVal_extends sb.1 hinp (fun w hw => lt_of_lt_of_le (rowVecWires_mem hk cut false i hw) (Nat.le_add_right n gs.length))]
        exact rowVecWires_map hk hgs u v cr cc A B y t cut false i
      · rw [listVal_extends sb.1 hinp (fun w hw => lt_of_lt_of_le (rowVecWires_mem hk cut true i hw) (Nat.le_add_right n gs.length))]
        exact rowVecWires_map hk hgs u v cr cc A B y t cut true i
    have he_val : eW.2.map (wireVal eW.1 inp) = List.ofFn e_f := by
      refine se.2.2.2.2.2 inp m m v_f B_final hinp
        (by rw [wireVal_extends (extends_trans sb.1 sv.1) hinp hwf, hwf_val])
        hv_val sb.2.2.2.1 (fun c => ?_)
      have hbc := sb.2.2.2.2.1 (bRes.2.getD c.val [])
        (getD_mem_of_lt bRes.2 (by rw [sb.2.2.2.1]; exact c.isLt))
      rw [listVal_extends sv.1 hinp hbc, hB_final c]
    have hf_val : fW.2.map (wireVal fW.1 inp) = List.ofFn first_f :=
      sf.2.2.2.2.2 inp m e_f hinp
        (by rw [wireVal_extends (extends_trans sb.1 (extends_trans sv.1 se.1)) hinp hwf, hwf_val])
        he_val
    have hav_val : wireVal avW.1 inp avW.2 = (List.finRange m).any e_f := by
      refine sav.2.2.2.2 inp m e_f hinp
        (by rw [wireVal_extends (extends_trans sb.1 (extends_trans sv.1 (extends_trans se.1 sf.1))) hinp hwf, hwf_val])
        ?_
      rw [listVal_extends sf.1 hinp se.2.2.2.2.1, he_val]
    have hw_val : witW.2.map (wireVal witW.1 inp) =
        List.ofFn (fun j : Fin m => dotBool first_f (fun c => B_final c j)) := by
      refine sw.2.2.2.2.2 inp m first_f B_final hinp
        (by rw [wireVal_extends (extends_trans sb.1 (extends_trans sv.1 (extends_trans se.1 (extends_trans sf.1 sav.1)))) hinp hwf, hwf_val])
        ?_ sb.2.2.2.1 (fun c => ?_)
      · rw [listVal_extends sav.1 hinp sf.2.2.2.2.1, hf_val]
      · have hbc := sb.2.2.2.2.1 (bRes.2.getD c.val [])
          (getD_mem_of_lt bRes.2 (by rw [sb.2.2.2.1]; exact c.isLt))
        rw [listVal_extends (extends_trans sv.1 (extends_trans se.1 (extends_trans sf.1 sav.1))) hinp hbc,
          hB_final c]
    refine ⟨?_, ?_⟩
    · rw [wireVal_extends sw.1 hinp sav.2.2.2.1, hav_val]
      rfl
    · rw [hw_val]
      rfl

def gSolveCutILoop (k r m n wFalse wTrue : ℕ) (gs : List Gate) (cut : Fin k) :
    List (Fin k) → List Gate × (List ℕ × List (List ℕ))
  | [] => (gs, ([], []))
  | i :: rest =>
    let s := gSolveCutI k r m n wFalse wTrue gs cut i
    let r2 := gSolveCutILoop k r m n wFalse wTrue s.1 cut rest
    (r2.1, (s.2.1 :: r2.2.1, s.2.2 :: r2.2.2))

lemma gSolveCutILoop_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse wTrue : ℕ}
    (cut : Fin k) (is : List (Fin k))
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwt : wTrue < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gSolveCutILoop k r m n wFalse wTrue gs cut is
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) * is.length ∧
      res.2.1.length = is.length ∧ (∀ w ∈ res.2.1, w < n + res.1.length) ∧
      res.2.2.length = is.length ∧ (∀ rw ∈ res.2.2, rw.length = m ∧ ∀ w ∈ rw, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        wireVal gs (mkInp k r m u v cr cc A B y t) wTrue = true →
        res.2.1.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          is.map (availTab k r m A B cut) ∧
        ∀ idx (hi : idx < is.length),
          (res.2.2.getD idx []).map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
            List.ofFn (witTab k r m A B cut (is[idx]'hi)) := by
  intro n
  induction is generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gSolveCutILoop], by simp [gSolveCutILoop],
      by simp [gSolveCutILoop], by simp [gSolveCutILoop], by simp [gSolveCutILoop], ?_⟩
    intro u v cr cc A B y t _ _
    exact ⟨rfl, fun idx hi => by simp at hi⟩
  | cons i rest ih =>
    dsimp only [gSolveCutILoop]
    set s := gSolveCutI k r m n wFalse wTrue gs cut i
    have ss := gSolveCutI_spec hk cut i hgs hwf hwt
    have hle1 : gs.length ≤ s.1.length := extends_length ss.1
    have ih' := ih ss.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (lt_of_lt_of_le hwt (Nat.add_le_add_left hle1 n))
    have hle2 : s.1.length ≤ (gSolveCutILoop k r m n wFalse wTrue s.1 cut rest).1.length :=
      extends_length ih'.1
    refine ⟨extends_trans ss.1 ih'.1, ih'.2.1, ?_,
      congrArg (· + 1) ih'.2.2.2.1, ?_,
      congrArg (· + 1) ih'.2.2.2.2.2.1, ?_, ?_⟩
    · have h1 : s.1.length ≤ gs.length + 2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m := ss.2.2.1
      have h2 : (gSolveCutILoop k r m n wFalse wTrue s.1 cut rest).1.length ≤
          s.1.length + (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) * rest.length := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le ss.2.2.2.1 (Nat.add_le_add_left hle2 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro rw hrw
      simp only [List.mem_cons] at hrw
      rcases hrw with rfl | hrw
      · exact ⟨ss.2.2.2.2.1, fun w hw => lt_of_lt_of_le (ss.2.2.2.2.2.1 w hw) (Nat.add_le_add_left hle2 n)⟩
      · exact ih'.2.2.2.2.2.2.1 rw hrw
    · intro u v cr cc A B y t hwf_val hwt_val
      set inp := mkInp k r m u v cr cc A B y t
      have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
      have hs_val := ss.2.2.2.2.2.2 u v cr cc A B y t hwf_val hwt_val
      have hih_val := ih'.2.2.2.2.2.2.2 u v cr cc A B y t
        (by rw [wireVal_extends ss.1 hinp hwf, hwf_val])
        (by rw [wireVal_extends ss.1 hinp hwt, hwt_val])
      refine ⟨?_, ?_⟩
      · simp only [List.map_cons]
        rw [wireVal_extends ih'.1 hinp ss.2.2.2.1, hs_val.1, hih_val.1]
      · intro idx hi
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          rw [listVal_extends ih'.1 hinp ss.2.2.2.2.2.1, hs_val.2]
        | succ idx =>
          have hi' : idx < rest.length := by simpa using hi
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          exact hih_val.2 idx hi'

def gPivSelLoop (n wFalse : ℕ) (gs : List Gate) (qBits : List ℕ) :
    List (ℕ × List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | (av, pref) :: rest =>
    let ltq := gCmpBits n gs wFalse pref qBits
    let p := gAnd n ltq.1 av ltq.2
    let r2 := gPivSelLoop n wFalse p.1 qBits rest
    (r2.1, p.2 :: r2.2)

lemma gPivSelLoop_spec {n wFalse : ℕ} {gs : List Gate} (qBits : List ℕ)
    (ps : List (ℕ × List ℕ))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hq : ∀ w ∈ qBits, w < n + gs.length)
    (hps : ∀ ap ∈ ps, ap.1 < n + gs.length ∧ ap.2.length = qBits.length ∧ ∀ w ∈ ap.2, w < n + gs.length) :
    let res := gPivSelLoop n wFalse gs qBits ps
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (5 * qBits.length + 1) * ps.length ∧
      res.2.length = ps.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ inp : List Bool, inp.length = n → wireVal gs inp wFalse = false →
        res.2.map (wireVal res.1 inp) = ps.map (fun ap =>
          wireVal gs inp ap.1 &&
            decide (bitsVal (ap.2.map (wireVal gs inp)) < bitsVal (qBits.map (wireVal gs inp)))) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gPivSelLoop], by simp [gPivSelLoop],
      by simp [gPivSelLoop], fun _ _ _ => rfl⟩
  | cons ap rest ih =>
    rcases ap with ⟨av, pref⟩
    have hap := hps (av, pref) (by simp)
    dsimp only [gPivSelLoop]
    set ltq := gCmpBits n gs wFalse pref qBits
    set p := gAnd n ltq.1 av ltq.2
    have sc := gCmpBits_spec pref qBits hgs hwf hap.2.2 hq
    have hle1 : gs.length ≤ ltq.1.length := extends_length sc.1
    have sa := gAnd_spec sc.2.1 (lt_of_lt_of_le hap.1 (Nat.add_le_add_left hle1 n)) sc.2.2.2.1
    have h12 : Extends gs p.1 := extends_trans sc.1 sa.1
    have hle12 : gs.length ≤ p.1.length := extends_length h12
    have ih' := ih sa.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
      (fun w hw => lt_of_lt_of_le (hq w hw) (Nat.add_le_add_left hle12 n))
      (fun xy hxy => have h := hps xy (by simp [hxy]);
        ⟨lt_of_lt_of_le h.1 (Nat.add_le_add_left hle12 n), h.2.1,
         fun w hw => lt_of_lt_of_le (h.2.2 w hw) (Nat.add_le_add_left hle12 n)⟩)
    have hle3 : p.1.length ≤ (gPivSelLoop n wFalse p.1 qBits rest).1.length := extends_length ih'.1
    refine ⟨extends_trans h12 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : ltq.1.length ≤ gs.length + 5 * pref.length := sc.2.2.1
      have h2 : p.1.length = ltq.1.length + 1 := sa.2.2.1
      have h3 : (gPivSelLoop n wFalse p.1 qBits rest).1.length ≤
          p.1.length + (5 * qBits.length + 1) * rest.length := ih'.2.2.1
      rw [hap.2.1] at h1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sa.2.2.2.1 (Nat.add_le_add_left hle3 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp hwf_val
      simp only [List.map_cons]
      have hp_val : wireVal p.1 inp p.2 =
          (wireVal gs inp av &&
            decide (bitsVal (pref.map (wireVal gs inp)) < bitsVal (qBits.map (wireVal gs inp)))) := by
        rw [sa.2.2.2.2 inp hinp, wireVal_extends sc.1 hinp hap.1, sc.2.2.2.2 inp hinp hap.2.1, hwf_val]
        simp
      rw [wireVal_extends ih'.1 hinp sa.2.2.2.1, hp_val,
        ih'.2.2.2.2.2 inp hinp (by rw [wireVal_extends h12 hinp hwf, hwf_val])]
      congr 1
      apply List.map_congr_left
      intro xy hxy
      have h := hps xy (by simp [hxy])
      rw [wireVal_extends h12 hinp h.1, listVal_extends h12 hinp h.2.2, listVal_extends h12 hinp hq]

lemma lt_two_pow_succ (k : ℕ) : k < 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [Nat.pow_succ']; omega

lemma bitsVal_replicate_false (B : ℕ) : bitsVal (List.replicate B false) = 0 := by
  induction B with
  | zero => simp [bitsVal]
  | succ B ih => simp [List.replicate_succ, bitsVal, ih]

lemma count_true_ofFn {k : ℕ} (f : Fin k → Bool) :
    (List.ofFn f).count true = ((List.finRange k).filter f).length := by
  have hof : List.ofFn f = (List.finRange k).map f := by apply List.ext_getElem <;> simp
  rw [hof]
  clear hof
  induction (List.finRange k) with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.filter_cons, List.count_cons]
    cases ha : f a <;> simp [ha, ih]

lemma count_true_take_ofFn {k : ℕ} (f : Fin k → Bool) (i : ℕ) :
    ((List.ofFn f).take i).count true = (((List.finRange k).take i).filter f).length := by
  have hof : List.ofFn f = (List.finRange k).map f := by apply List.ext_getElem <;> simp
  rw [hof, ← List.map_take]
  induction ((List.finRange k).take i) with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.filter_cons, List.count_cons]
    cases ha : f a <;> simp [ha, ih]

def gSolveCut (k r m q n wFalse wTrue : ℕ) (gs : List Gate) (cut : Fin k) :
    List Gate × (ℕ × List ℕ × List (List ℕ)) :=
  let il := gSolveCutILoop k r m n wFalse wTrue gs cut (List.finRange k)
  let pop := gPrefixPopcount n il.1 (List.replicate (k + 1) wFalse) il.2.1
  let qBits := constBitsWires (k + 1) wFalse wTrue q
  let cp := gCmpBits n pop.1 wTrue qBits pop.2.1
  let pivs := gPivSelLoop n wFalse cp.1 qBits (il.2.1.zip pop.2.2)
  (pivs.1, (cp.2, pivs.2, il.2.2))

lemma gSolveCut_spec {k r m q : ℕ} (hk : 0 < k) (hqk : q ≤ k)
    {gs : List Gate} {wFalse wTrue : ℕ} (cut : Fin k)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwt : wTrue < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gSolveCut k r m q n wFalse wTrue gs cut
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) +
        10 * k * (k + 1) + 5 * (k + 1) + k ∧
      res.2.1 < n + res.1.length ∧
      res.2.2.1.length = k ∧ (∀ w ∈ res.2.2.1, w < n + res.1.length) ∧
      res.2.2.2.length = k ∧ (∀ rw ∈ res.2.2.2, rw.length = m ∧ ∀ w ∈ rw, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        wireVal gs (mkInp k r m u v cr cc A B y t) wTrue = true →
        wireVal res.1 (mkInp k r m u v cr cc A B y t) res.2.1 = cutPass k r m q A B cut ∧
        res.2.2.1.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (pivSel q (availTab k r m A B cut)) ∧
        ∀ i : Fin k, (res.2.2.2.getD i.val []).map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (witTab k r m A B cut i) := by
  intro n
  dsimp only [gSolveCut]
  set il := gSolveCutILoop k r m n wFalse wTrue gs cut (List.finRange k)
  set pop := gPrefixPopcount n il.1 (List.replicate (k + 1) wFalse) il.2.1
  set qBits := constBitsWires (k + 1) wFalse wTrue q
  set cp := gCmpBits n pop.1 wTrue qBits pop.2.1
  set pivs := gPivSelLoop n wFalse cp.1 qBits (il.2.1.zip pop.2.2)
  have sil := gSolveCutILoop_spec hk cut (List.finRange k) hgs hwf hwt
  have hle1 : gs.length ≤ il.1.length := extends_length sil.1
  have hrep_len : (List.replicate (k + 1) wFalse).length = k + 1 := List.length_replicate
  have hrep_mem : ∀ w ∈ List.replicate (k + 1) wFalse, w < n + il.1.length := by
    intro w hw; rw [List.mem_replicate] at hw; rcases hw with ⟨_, rfl⟩
    exact lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n)
  have spop := gPrefixPopcount_spec (List.replicate (k + 1) wFalse) il.2.1 sil.2.1 hrep_len hrep_mem sil.2.2.2.2.1
  have hle2 : il.1.length ≤ pop.1.length := extends_length spop.1
  have hle12 : gs.length ≤ pop.1.length := le_trans hle1 hle2
  have hq_mem : ∀ w ∈ qBits, w < n + pop.1.length :=
    constBitsWires_mem (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
      (lt_of_lt_of_le hwt (Nat.add_le_add_left hle12 n))
  have scp := gCmpBits_spec qBits pop.2.1 spop.2.1
    (lt_of_lt_of_le hwt (Nat.add_le_add_left hle12 n)) hq_mem spop.2.2.2.2.1
  have hle3 : pop.1.length ≤ cp.1.length := extends_length scp.1
  have hle13 : gs.length ≤ cp.1.length := le_trans hle12 hle3
  have hle23 : il.1.length ≤ cp.1.length := le_trans hle2 hle3
  have hil_len : il.2.1.length = k := by rw [sil.2.2.2.1, List.length_finRange]
  have hpop_len : pop.2.2.length = k := by rw [spop.2.2.2.2.2.1, hil_len]
  have hps_mem : ∀ ap ∈ il.2.1.zip pop.2.2,
      ap.1 < n + cp.1.length ∧ ap.2.length = qBits.length ∧ ∀ w ∈ ap.2, w < n + cp.1.length := by
    intro ap hap
    have hm := List.of_mem_zip hap
    have hpref := spop.2.2.2.2.2.2.1 ap.2 hm.2
    exact ⟨lt_of_lt_of_le (sil.2.2.2.2.1 ap.1 hm.1) (Nat.add_le_add_left hle23 n),
      by rw [hpref.1, constBitsWires_length],
      fun w hw => lt_of_lt_of_le (hpref.2 w hw) (Nat.add_le_add_left hle3 n)⟩
  have spivs := gPivSelLoop_spec qBits (il.2.1.zip pop.2.2) scp.2.1
    (lt_of_lt_of_le hwf (Nat.add_le_add_left hle13 n))
    (fun w hw => lt_of_lt_of_le (hq_mem w hw) (Nat.add_le_add_left hle3 n))
    hps_mem
  have hle4 : cp.1.length ≤ pivs.1.length := extends_length spivs.1
  have hle24 : il.1.length ≤ pivs.1.length := le_trans hle23 hle4
  have hext_all : Extends gs pivs.1 :=
    extends_trans sil.1 (extends_trans spop.1 (extends_trans scp.1 spivs.1))
  refine ⟨hext_all, spivs.2.1, ?_, lt_of_lt_of_le scp.2.2.2.1 (Nat.add_le_add_left hle4 n),
    ?_, spivs.2.2.2.2.1, ?_, ?_, ?_⟩
  · have h1 := sil.2.2.1
    have h2 := spop.2.2.1
    have h3 := scp.2.2.1
    have h4 := spivs.2.2.1
    change il.1.length ≤ gs.length + (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) * (List.finRange k).length at h1
    change pop.1.length = il.1.length + 5 * (k + 1) * il.2.1.length at h2
    change cp.1.length ≤ pop.1.length + 5 * qBits.length at h3
    change pivs.1.length ≤ cp.1.length + (5 * qBits.length + 1) * (il.2.1.zip pop.2.2).length at h4
    have hzl : (il.2.1.zip pop.2.2).length ≤ k := by simp [hil_len]
    rw [List.length_finRange] at h1
    rw [hil_len] at h2
    rw [constBitsWires_length] at h3 h4
    have h4' : pivs.1.length ≤ cp.1.length + (5 * (k + 1) + 1) * k :=
      le_trans h4 (Nat.add_le_add_left (Nat.mul_le_mul_left _ hzl) _)
    nlinarith
  · rw [spivs.2.2.2.1]; simp [hil_len, hpop_len]
  · rw [sil.2.2.2.2.2.1, List.length_finRange]
  · intro rw hrw
    have h := sil.2.2.2.2.2.2.1 rw hrw
    exact ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle24 n)⟩
  · intro u v cr cc A B y t hwf_val hwt_val
    set inp := mkInp k r m u v cr cc A B y t
    have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
    have hwf1 : wireVal il.1 inp wFalse = false := by rw [wireVal_extends sil.1 hinp hwf, hwf_val]
    have hwt1 : wireVal il.1 inp wTrue = true := by rw [wireVal_extends sil.1 hinp hwt, hwt_val]
    have hwf2 : wireVal pop.1 inp wFalse = false := by rw [wireVal_extends spop.1 hinp (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n)), hwf1]
    have hwt2 : wireVal pop.1 inp wTrue = true := by rw [wireVal_extends spop.1 hinp (lt_of_lt_of_le hwt (Nat.add_le_add_left hle1 n)), hwt1]
    have hwf3 : wireVal cp.1 inp wFalse = false := by rw [wireVal_extends scp.1 hinp (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n)), hwf2]
    have hwt3 : wireVal cp.1 inp wTrue = true := by rw [wireVal_extends scp.1 hinp (lt_of_lt_of_le hwt (Nat.add_le_add_left hle12 n)), hwt2]
    have hsil := sil.2.2.2.2.2.2.2 u v cr cc A B y t hwf_val hwt_val
    have hof_avail : (List.finRange k).map (availTab k r m A B cut) =
        List.ofFn (availTab k r m A B cut) := by
      apply List.ext_getElem <;> simp
    have hil_map : il.2.1.map (wireVal il.1 inp) = List.ofFn (availTab k r m A B cut) := by
      rw [hsil.1, hof_avail]
    have hacc_val : bitsVal ((List.replicate (k + 1) wFalse).map (wireVal il.1 inp)) = 0 := by
      have hm : (List.replicate (k + 1) wFalse).map (wireVal il.1 inp) = List.replicate (k + 1) false := by
        simp [List.map_replicate, hwf1]
      rw [hm, bitsVal_replicate_false]
    have hbound : bitsVal ((List.replicate (k + 1) wFalse).map (wireVal il.1 inp)) + il.2.1.length < 2 ^ (k + 1) := by
      rw [hacc_val, hil_len, Nat.zero_add]; exact lt_two_pow_succ k
    have hspop := spop.2.2.2.2.2.2.2 inp hinp hbound
    rw [hacc_val, Nat.zero_add, hil_map] at hspop
    have hq_val : bitsVal (qBits.map (wireVal pop.1 inp)) = q :=
      constBitsWires_bitsVal pop.1 inp hwf2 hwt2 (lt_of_le_of_lt hqk (lt_two_pow_succ k))
    have hcp_val : wireVal cp.1 inp cp.2 = cutPass k r m q A B cut := by
      have hlen_qp : qBits.length = pop.2.1.length := by
        dsimp only [qBits]; rw [constBitsWires_length, spop.2.2.2.1]
      rw [scp.2.2.2.2 inp hinp hlen_qp, hq_val, hwt2, hspop.1]
      simp only [count_true_ofFn, cutPass, cutCount]
      apply Bool.eq_iff_iff.mpr
      simp [Nat.le_iff_lt_or_eq, or_comm]
    refine ⟨?_, ?_, ?_⟩
    · rw [wireVal_extends spivs.1 hinp scp.2.2.2.1, hcp_val]
    · rw [spivs.2.2.2.2.2 inp hinp hwf3]
      have hzip : il.2.1.zip pop.2.2 = (List.finRange k).map (fun i =>
          (il.2.1[i.val]'(by rw [hil_len]; exact i.isLt),
           pop.2.2[i.val]'(by rw [hpop_len]; exact i.isLt))) := by
        apply List.ext_getElem <;> simp [hil_len, hpop_len, List.getElem_zip]
      rw [hzip, List.map_map]
      have hof : List.ofFn (pivSel q (availTab k r m A B cut)) =
          (List.finRange k).map (pivSel q (availTab k r m A B cut)) := by
        apply List.ext_getElem <;> simp
      rw [hof]
      apply List.map_congr_left
      intro i _
      dsimp only [Function.comp_apply, pivSel]
      have hiv : wireVal cp.1 inp (il.2.1[i.val]'(by rw [hil_len]; exact i.isLt)) =
          availTab k r m A B cut i := by
        rw [wireVal_extends (extends_trans spop.1 scp.1) hinp (sil.2.2.2.2.1 _ (List.getElem_mem _))]
        have := congrArg (fun l : List Bool => l[i.val]?) hil_map
        simp only [List.getElem?_map, List.getElem?_eq_getElem (by rw [hil_len]; exact i.isLt),
          List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa using this
      have hpv : bitsVal ((pop.2.2[i.val]'(by rw [hpop_len]; exact i.isLt)).map (wireVal cp.1 inp)) =
          ((List.finRange k).take i.val |>.filter (availTab k r m A B cut)).length := by
        have hmem_p := spop.2.2.2.2.2.2.1 (pop.2.2[i.val]'(by rw [hpop_len]; exact i.isLt)) (List.getElem_mem _)
        rw [listVal_extends scp.1 hinp hmem_p.2]
        have hrc : pop.2.2[i.val]'(by rw [hpop_len]; exact i.isLt) = pop.2.2.getD i.val [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hpop_len]; exact i.isLt)]
        rw [hrc, hspop.2 i.val (by rw [hil_len]; exact i.isLt), List.map_take, hil_map,
          count_true_take_ofFn, Nat.zero_add]
      have hqv : bitsVal (qBits.map (wireVal cp.1 inp)) = q := by
        rw [listVal_extends scp.1 hinp hq_mem, hq_val]
      rw [hiv, hpv, hqv]
    · intro i
      have hmem_w := (sil.2.2.2.2.2.2.1 (il.2.2.getD i.val [])
        (getD_mem_of_lt il.2.2 (by rw [sil.2.2.2.2.2.1, List.length_finRange]; exact i.isLt))).2
      rw [listVal_extends (extends_trans spop.1 (extends_trans scp.1 spivs.1)) hinp hmem_w]
      have h1 := hsil.2 i.val (by simp)
      simpa using h1

def gSolveCutLoop (k r m q n wFalse wTrue : ℕ) (gs : List Gate) :
    List (Fin k) → List Gate × (List ℕ × List (List ℕ) × List (List (List ℕ)))
  | [] => (gs, ([], [], []))
  | cut :: rest =>
    let s := gSolveCut k r m q n wFalse wTrue gs cut
    let r2 := gSolveCutLoop k r m q n wFalse wTrue s.1 rest
    (r2.1, (s.2.1 :: r2.2.1, s.2.2.1 :: r2.2.2.1, s.2.2.2 :: r2.2.2.2))

lemma gSolveCutLoop_spec {k r m q : ℕ} (hk : 0 < k) (hqk : q ≤ k)
    {gs : List Gate} {wFalse wTrue : ℕ} (cuts : List (Fin k))
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwt : wTrue < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gSolveCutLoop k r m q n wFalse wTrue gs cuts
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) +
        10 * k * (k + 1) + 5 * (k + 1) + k) * cuts.length ∧
      res.2.1.length = cuts.length ∧ (∀ w ∈ res.2.1, w < n + res.1.length) ∧
      res.2.2.1.length = cuts.length ∧ (∀ r ∈ res.2.2.1, r.length = k ∧ ∀ w ∈ r, w < n + res.1.length) ∧
      res.2.2.2.length = cuts.length ∧
        (∀ wm ∈ res.2.2.2, wm.length = k ∧ ∀ rw ∈ wm, rw.length = m ∧ ∀ w ∈ rw, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        wireVal gs (mkInp k r m u v cr cc A B y t) wTrue = true →
        res.2.1.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          cuts.map (cutPass k r m q A B) ∧
        (∀ idx (hi : idx < cuts.length),
          (res.2.2.1.getD idx []).map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
            List.ofFn (pivSel q (availTab k r m A B (cuts[idx]'hi)))) ∧
        ∀ idx (hi : idx < cuts.length) (i : Fin k),
          ((res.2.2.2.getD idx []).getD i.val []).map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
            List.ofFn (witTab k r m A B (cuts[idx]'hi) i) := by
  intro n
  induction cuts generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gSolveCutLoop], by simp [gSolveCutLoop],
      by simp [gSolveCutLoop], by simp [gSolveCutLoop], by simp [gSolveCutLoop],
      by simp [gSolveCutLoop], by simp [gSolveCutLoop], ?_⟩
    intro u v cr cc A B y t _ _
    exact ⟨rfl, fun idx hi => by simp at hi, fun idx hi => by simp at hi⟩
  | cons cut rest ih =>
    dsimp only [gSolveCutLoop]
    set s := gSolveCut k r m q n wFalse wTrue gs cut
    have ss := gSolveCut_spec hk hqk cut hgs hwf hwt
    have hle1 : gs.length ≤ s.1.length := extends_length ss.1
    have ih' := ih ss.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (lt_of_lt_of_le hwt (Nat.add_le_add_left hle1 n))
    have hle2 : s.1.length ≤ (gSolveCutLoop k r m q n wFalse wTrue s.1 rest).1.length :=
      extends_length ih'.1
    refine ⟨extends_trans ss.1 ih'.1, ih'.2.1, ?_,
      congrArg (· + 1) ih'.2.2.2.1, ?_,
      congrArg (· + 1) ih'.2.2.2.2.2.1, ?_,
      congrArg (· + 1) ih'.2.2.2.2.2.2.2.1, ?_, ?_⟩
    · have h1 := ss.2.2.1; have h2 := ih'.2.2.1
      change s.1.length ≤ _ at h1
      change (gSolveCutLoop k r m q n wFalse wTrue s.1 rest).1.length ≤ _ at h2
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le ss.2.2.2.1 (Nat.add_le_add_left hle2 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro r hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨ss.2.2.2.2.1, fun w h => lt_of_lt_of_le (ss.2.2.2.2.2.1 w h) (Nat.add_le_add_left hle2 n)⟩
      · exact ih'.2.2.2.2.2.2.1 r hw
    · intro wm hwm
      simp only [List.mem_cons] at hwm
      rcases hwm with rfl | hwm
      · exact ⟨ss.2.2.2.2.2.2.1, fun rw hrw =>
          have h := ss.2.2.2.2.2.2.2.1 rw hrw
          ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle2 n)⟩⟩
      · exact ih'.2.2.2.2.2.2.2.2.1 wm hwm
    · intro u v cr cc A B y t hwf_val hwt_val
      set inp := mkInp k r m u v cr cc A B y t
      have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
      have hs := ss.2.2.2.2.2.2.2.2 u v cr cc A B y t hwf_val hwt_val
      have hih := ih'.2.2.2.2.2.2.2.2.2 u v cr cc A B y t
        (by rw [wireVal_extends ss.1 hinp hwf, hwf_val])
        (by rw [wireVal_extends ss.1 hinp hwt, hwt_val])
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.map_cons]
        rw [wireVal_extends ih'.1 hinp ss.2.2.2.1, hs.1, hih.1]
      · intro idx hi
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          rw [listVal_extends ih'.1 hinp ss.2.2.2.2.2.1, hs.2.1]
        | succ idx =>
          have hi' : idx < rest.length := by simpa using hi
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          exact hih.2.1 idx hi'
      · intro idx hi i
        cases idx with
        | zero =>
          simp only [List.getD_cons_zero, List.getElem_cons_zero]
          have hmem_w := (ss.2.2.2.2.2.2.2.1 (s.2.2.2.getD i.val [])
            (getD_mem_of_lt s.2.2.2 (by rw [ss.2.2.2.2.2.2.1]; exact i.isLt))).2
          rw [listVal_extends ih'.1 hinp hmem_w, hs.2.2 i]
        | succ idx =>
          have hi' : idx < rest.length := by simpa using hi
          simp only [List.getD_cons_succ, List.getElem_cons_succ]
          exact hih.2.2 idx hi' i

lemma list_eq_ofFn_getD {α : Type*} (l : List α) {B : ℕ} (h : l.length = B) (d : α) :
    l = List.ofFn (fun j : Fin B => l.getD j.val d) := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi1 hi2
    simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some]

lemma bitsVal_inj {l1 l2 : List Bool} (hlen : l1.length = l2.length)
    (h : bitsVal l1 = bitsVal l2) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp at hlen ⊢
  | cons a t1 ih =>
    cases l2 with
    | nil => simp at hlen
    | cons b t2 =>
      simp only [bitsVal] at h
      have hab : a = b := by
        cases a <;> cases b <;> (try rfl) <;>
          simp only [Bool.toNat_false, Bool.toNat_true] at h <;> omega
      subst hab
      congr 1
      apply ih (by simpa using hlen)
      omega

lemma dotBool_oneHot {m : ℕ} (c0 : Fin m) (f : Fin m → Bool) :
    dotBool (fun c => decide (c = c0)) f = f c0 := by
  apply b2z_inj
  rw [dotBool_b2z]
  have hterm : ∀ c : Fin m, b2z (decide (c = c0)) * b2z (f c) = if c = c0 then b2z (f c0) else 0 := by
    intro c; by_cases h : c = c0 <;> simp [h]
  simp [hterm]

def gSelectWitLoop {k : ℕ} (n wFalse m : ℕ) (gs : List Gate) (fcW : List ℕ)
    (witMats : List (List (List ℕ))) : List (Fin k) → List Gate × List (List ℕ)
  | [] => (gs, [])
  | i :: rest =>
    let rows := witMats.map (fun wm => wm.getD i.val [])
    let s := gSelectMat n wFalse gs fcW rows m
    let r2 := gSelectWitLoop n wFalse m s.1 fcW witMats rest
    (r2.1, s.2 :: r2.2)

lemma gSelectWitLoop_spec {k : ℕ} (n wFalse m : ℕ) {gs : List Gate} (fcW : List ℕ)
    (witMats : List (List (List ℕ))) (is : List (Fin k))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hfc : ∀ w ∈ fcW, w < n + gs.length)
    (hwm : ∀ wm ∈ witMats, wm.length = k ∧ ∀ rw ∈ wm, rw.length = m ∧ ∀ w ∈ rw, w < n + gs.length) :
    let res := gSelectWitLoop n wFalse m gs fcW witMats is
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * fcW.length * m * is.length ∧
      res.2.length = is.length ∧ (∀ rw ∈ res.2, rw.length = m ∧ ∀ w ∈ rw, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (L : ℕ) (fs : Fin L → Bool) (W : Fin L → Fin k → Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        fcW.map (wireVal gs inp) = List.ofFn fs →
        witMats.length = L →
        (∀ (c : Fin L) (i : Fin k), ((witMats.getD c.val []).getD i.val []).map (wireVal gs inp) =
          List.ofFn (W c i)) →
        ∀ idx (hi : idx < is.length),
          (res.2.getD idx []).map (wireVal res.1 inp) =
            List.ofFn (fun j : Fin m => dotBool fs (fun c => W c (is[idx]'hi) j)) := by
  induction is generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gSelectWitLoop], by simp [gSelectWitLoop],
      by simp [gSelectWitLoop], fun _ _ _ _ _ _ _ _ _ idx hi => by simp at hi⟩
  | cons i rest ih =>
    dsimp only [gSelectWitLoop]
    set rows := witMats.map (fun wm => wm.getD i.val [])
    set s := gSelectMat n wFalse gs fcW rows m
    have hrows_mem : ∀ rw ∈ rows, ∀ w ∈ rw, w < n + gs.length := by
      intro rw hrw w hw
      simp only [rows, List.mem_map] at hrw
      rcases hrw with ⟨wm, hwm_mem, rfl⟩
      have h := hwm wm hwm_mem
      exact (h.2 _ (getD_mem_of_lt wm (by rw [h.1]; exact i.isLt))).2 w hw
    have ss := gSelectMat_spec fcW rows m hgs hwf hfc hrows_mem
    have hle1 : gs.length ≤ s.1.length := extends_length ss.1
    have ih' := ih ss.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hfc w hw) (Nat.add_le_add_left hle1 n))
      (fun wm hwm_mem => have h := hwm wm hwm_mem;
        ⟨h.1, fun rw hrw => have h' := h.2 rw hrw;
          ⟨h'.1, fun w hw => lt_of_lt_of_le (h'.2 w hw) (Nat.add_le_add_left hle1 n)⟩⟩)
    have hle2 : s.1.length ≤ (gSelectWitLoop n wFalse m s.1 fcW witMats rest).1.length :=
      extends_length ih'.1
    refine ⟨extends_trans ss.1 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : s.1.length ≤ gs.length + 5 * fcW.length * m := ss.2.2.1
      have h2 : (gSelectWitLoop n wFalse m s.1 fcW witMats rest).1.length ≤
          s.1.length + 5 * fcW.length * m * rest.length := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro rw hrw
      simp only [List.mem_cons] at hrw
      rcases hrw with rfl | hrw
      · exact ⟨ss.2.2.2.1, fun w hw => lt_of_lt_of_le (ss.2.2.2.2.1 w hw) (Nat.add_le_add_left hle2 n)⟩
      · exact ih'.2.2.2.2.1 rw hrw
    · intro inp L fs W hinp hwf_val hfs hlenL hW idx hi
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [listVal_extends ih'.1 hinp ss.2.2.2.2.1]
        refine ss.2.2.2.2.2 inp L fs (fun c j => W c i j) hinp hwf_val hfs (by simp [rows, hlenL]) ?_
        intro c
        have hc_lt : c.val < witMats.length := by rw [hlenL]; exact c.isLt
        have hrc : rows.getD c.val [] = (witMats.getD c.val []).getD i.val [] := by
          simp [rows, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc_lt]
        rw [hrc]
        exact hW c i
      | succ idx =>
        have hi' : idx < rest.length := by simpa using hi
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        refine ih'.2.2.2.2.2 inp L fs W hinp
          (by rw [wireVal_extends ss.1 hinp hwf, hwf_val])
          (by rw [listVal_extends ss.1 hinp hfc, hfs]) hlenL (fun c i' => ?_) idx hi'
        have hc_lt : c.val < witMats.length := by rw [hlenL]; exact c.isLt
        have h1 := hwm (witMats.getD c.val []) (getD_mem_of_lt witMats hc_lt)
        have h2 := (h1.2 _ (getD_mem_of_lt _ (by rw [h1.1]; exact i'.isLt))).2
        rw [listVal_extends ss.1 hinp h2, hW c i']

def gFreeOneHotRow (n wFalse wTrue B : ℕ) (gs : List Gate) (npiv : ℕ) (pref : List ℕ) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | d :: rest =>
    let dBits := constBitsWires B wFalse wTrue d
    let eq := gVecEq n wTrue gs pref dBits
    let res := gAnd n eq.1 npiv eq.2
    let r2 := gFreeOneHotRow n wFalse wTrue B res.1 npiv pref rest
    (r2.1, res.2 :: r2.2)

lemma gFreeOneHotRow_spec {n wFalse wTrue B : ℕ} {gs : List Gate} (npiv : ℕ) (pref : List ℕ)
    (ds : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length) (hwt : wTrue < n + gs.length)
    (hnp : npiv < n + gs.length) (hplen : pref.length = B) (hp : ∀ w ∈ pref, w < n + gs.length)
    (hds : ∀ d ∈ ds, d < 2 ^ B) :
    let res := gFreeOneHotRow n wFalse wTrue B gs npiv pref ds
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (6 * B + 1) * ds.length ∧
      res.2.length = ds.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ inp : List Bool, inp.length = n → wireVal gs inp wFalse = false → wireVal gs inp wTrue = true →
        res.2.map (wireVal res.1 inp) = ds.map (fun d =>
          wireVal gs inp npiv && decide (bitsVal (pref.map (wireVal gs inp)) = d)) := by
  induction ds generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gFreeOneHotRow], by simp [gFreeOneHotRow],
      by simp [gFreeOneHotRow], fun _ _ _ _ => rfl⟩
  | cons d rest ih =>
    have hd : d < 2 ^ B := hds d (by simp)
    dsimp only [gFreeOneHotRow]
    set dBits := constBitsWires B wFalse wTrue d
    set eq := gVecEq n wTrue gs pref dBits
    set res := gAnd n eq.1 npiv eq.2
    have hd_mem : ∀ w ∈ dBits, w < n + gs.length := constBitsWires_mem hwf hwt
    have seq := gVecEq_spec pref dBits hgs hwt hp hd_mem
    have hle1 : gs.length ≤ eq.1.length := extends_length seq.1
    have sres := gAnd_spec seq.2.1 (lt_of_lt_of_le hnp (Nat.add_le_add_left hle1 n)) seq.2.2.2.1
    have h12 : Extends gs res.1 := extends_trans seq.1 sres.1
    have hle12 : gs.length ≤ res.1.length := extends_length h12
    have ih' := ih sres.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
      (lt_of_lt_of_le hwt (Nat.add_le_add_left hle12 n))
      (lt_of_lt_of_le hnp (Nat.add_le_add_left hle12 n))
      (fun w hw => lt_of_lt_of_le (hp w hw) (Nat.add_le_add_left hle12 n))
      (fun x hx => hds x (by simp [hx]))
    have hle3 : res.1.length ≤ (gFreeOneHotRow n wFalse wTrue B res.1 npiv pref rest).1.length :=
      extends_length ih'.1
    refine ⟨extends_trans h12 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : eq.1.length ≤ gs.length + 6 * pref.length := seq.2.2.1
      have h2 : res.1.length = eq.1.length + 1 := sres.2.2.1
      have h3 : (gFreeOneHotRow n wFalse wTrue B res.1 npiv pref rest).1.length ≤
          res.1.length + (6 * B + 1) * rest.length := ih'.2.2.1
      rw [hplen] at h1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sres.2.2.2.1 (Nat.add_le_add_left hle3 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp hinp hwf_val hwt_val
      simp only [List.map_cons]
      have hres_val : wireVal res.1 inp res.2 =
          (wireVal gs inp npiv && decide (bitsVal (pref.map (wireVal gs inp)) = d)) := by
        let f1 : Fin B → Bool := fun j => (pref.map (wireVal gs inp)).getD j.val false
        let f2 : Fin B → Bool := fun j => (dBits.map (wireVal gs inp)).getD j.val false
        have hf1 : pref.map (wireVal gs inp) = List.ofFn f1 :=
          list_eq_ofFn_getD (pref.map (wireVal gs inp)) (by simp [hplen]) false
        have hf2 : dBits.map (wireVal gs inp) = List.ofFn f2 :=
          list_eq_ofFn_getD (dBits.map (wireVal gs inp)) (by simp [dBits, constBitsWires_length]) false
        have heq_val := seq.2.2.2.2 inp B f1 f2 hinp hwt_val hf1 hf2
        have hd_val : bitsVal (dBits.map (wireVal gs inp)) = d :=
          constBitsWires_bitsVal gs inp hwf_val hwt_val hd
        have heq_iff : (∀ j : Fin B, f1 j = f2 j) ↔ bitsVal (pref.map (wireVal gs inp)) = d := by
          rw [← hd_val, hf1, hf2]
          constructor
          · intro h; congr 2; ext j; exact h j
          · intro h j
            have hinj := bitsVal_inj (by simp) h
            have := congrArg (fun l : List Bool => l[j.val]?) hinj
            simp only [List.getElem?_ofFn, j.isLt, ↓reduceDIte, Option.some.injEq] at this
            exact this
        rw [sres.2.2.2.2 inp hinp, wireVal_extends seq.1 hinp hnp, heq_val]
        congr 1
        exact Bool.eq_iff_iff.mpr (by simpa using heq_iff)
      rw [wireVal_extends ih'.1 hinp sres.2.2.2.1, hres_val,
        ih'.2.2.2.2.2 inp hinp (by rw [wireVal_extends h12 hinp hwf, hwf_val])
          (by rw [wireVal_extends h12 hinp hwt, hwt_val])]
      congr 1
      apply List.map_congr_left
      intro x _
      rw [wireVal_extends h12 hinp hnp, listVal_extends h12 hinp hp]

def gFreeOneHotLoop (n wFalse wTrue B : ℕ) (gs : List Gate) (dList : List ℕ) :
    List (ℕ × List ℕ) → List Gate × List (List ℕ)
  | [] => (gs, [])
  | (npiv, pref) :: rest =>
    let row := gFreeOneHotRow n wFalse wTrue B gs npiv pref dList
    let r2 := gFreeOneHotLoop n wFalse wTrue B row.1 dList rest
    (r2.1, row.2 :: r2.2)

lemma gFreeOneHotLoop_spec {n wFalse wTrue B : ℕ} {gs : List Gate} (dList : List ℕ)
    (ps : List (ℕ × List ℕ))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length) (hwt : wTrue < n + gs.length)
    (hds : ∀ d ∈ dList, d < 2 ^ B)
    (hps : ∀ ap ∈ ps, ap.1 < n + gs.length ∧ ap.2.length = B ∧ ∀ w ∈ ap.2, w < n + gs.length) :
    let res := gFreeOneHotLoop n wFalse wTrue B gs dList ps
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (6 * B + 1) * dList.length * ps.length ∧
      res.2.length = ps.length ∧ (∀ rw ∈ res.2, rw.length = dList.length ∧ ∀ w ∈ rw, w < n + res.1.length) ∧
      ∀ inp : List Bool, inp.length = n → wireVal gs inp wFalse = false → wireVal gs inp wTrue = true →
        ∀ idx (hi : idx < ps.length),
          (res.2.getD idx []).map (wireVal res.1 inp) = dList.map (fun d =>
            wireVal gs inp (ps[idx]'hi).1 &&
              decide (bitsVal ((ps[idx]'hi).2.map (wireVal gs inp)) = d)) := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gFreeOneHotLoop], by simp [gFreeOneHotLoop],
      by simp [gFreeOneHotLoop], fun _ _ _ _ idx hi => by simp at hi⟩
  | cons ap rest ih =>
    rcases ap with ⟨npiv, pref⟩
    have hap := hps (npiv, pref) (by simp)
    dsimp only [gFreeOneHotLoop]
    set row := gFreeOneHotRow n wFalse wTrue B gs npiv pref dList
    have srow := gFreeOneHotRow_spec npiv pref dList hgs hwf hwt hap.1 hap.2.1 hap.2.2 hds
    have hle1 : gs.length ≤ row.1.length := extends_length srow.1
    have ih' := ih srow.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (lt_of_lt_of_le hwt (Nat.add_le_add_left hle1 n))
      (fun xy hxy => have h := hps xy (by simp [hxy]);
        ⟨lt_of_lt_of_le h.1 (Nat.add_le_add_left hle1 n), h.2.1,
         fun w hw => lt_of_lt_of_le (h.2.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
    have hle2 : row.1.length ≤ (gFreeOneHotLoop n wFalse wTrue B row.1 dList rest).1.length :=
      extends_length ih'.1
    refine ⟨extends_trans srow.1 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : row.1.length ≤ gs.length + (6 * B + 1) * dList.length := srow.2.2.1
      have h2 : (gFreeOneHotLoop n wFalse wTrue B row.1 dList rest).1.length ≤
          row.1.length + (6 * B + 1) * dList.length * rest.length := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro rw hrw
      simp only [List.mem_cons] at hrw
      rcases hrw with rfl | hrw
      · exact ⟨srow.2.2.2.1, fun w hw => lt_of_lt_of_le (srow.2.2.2.2.1 w hw) (Nat.add_le_add_left hle2 n)⟩
      · exact ih'.2.2.2.2.1 rw hrw
    · intro inp hinp hwf_val hwt_val idx hi
      cases idx with
      | zero =>
        simp only [List.getD_cons_zero, List.getElem_cons_zero]
        rw [listVal_extends ih'.1 hinp srow.2.2.2.2.1]
        exact srow.2.2.2.2.2 inp hinp hwf_val hwt_val
      | succ idx =>
        have hi' : idx < rest.length := by simpa using hi
        simp only [List.getD_cons_succ, List.getElem_cons_succ]
        have hmem := hps (rest[idx]'hi') (by simp [List.getElem_mem])
        rw [ih'.2.2.2.2.2 inp hinp (by rw [wireVal_extends srow.1 hinp hwf, hwf_val])
          (by rw [wireVal_extends srow.1 hinp hwt, hwt_val]) idx hi',
          wireVal_extends srow.1 hinp hmem.1, listVal_extends srow.1 hinp hmem.2.2]

def gFreeOneHot (k q n wFalse wTrue : ℕ) (gs : List Gate) (pivW : List ℕ) :
    List Gate × List (List ℕ) :=
  let npiv := gNotList n gs pivW
  let pop := gPrefixPopcount n npiv.1 (List.replicate (k + 1) wFalse) npiv.2
  gFreeOneHotLoop n wFalse wTrue (k + 1) pop.1 (List.range (k - q)) (npiv.2.zip pop.2.2)

lemma gFreeOneHot_spec {k q n wFalse wTrue : ℕ} {gs : List Gate} (pivW : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length) (hwt : wTrue < n + gs.length)
    (hpiv_len : pivW.length = k) (hpiv_mem : ∀ w ∈ pivW, w < n + gs.length) :
    let res := gFreeOneHot k q n wFalse wTrue gs pivW
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + k + 5 * (k + 1) * k + (6 * (k + 1) + 1) * (k - q) * k ∧
      res.2.length = k ∧ (∀ rw ∈ res.2, rw.length = k - q ∧ ∀ w ∈ rw, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (piv : Fin k → Bool),
        inp.length = n → wireVal gs inp wFalse = false → wireVal gs inp wTrue = true →
        pivW.map (wireVal gs inp) = List.ofFn piv →
        ∀ i : Fin k, ((res.2.getD i.val []).map (wireVal res.1 inp)) =
          List.ofFn (fun d : Fin (k - q) => !piv i && decide (freeCountBefore piv i = d.val)) := by
  dsimp only [gFreeOneHot]
  set npiv := gNotList n gs pivW
  set pop := gPrefixPopcount n npiv.1 (List.replicate (k + 1) wFalse) npiv.2
  have sn := gNotList_spec pivW hgs hpiv_mem
  have hle1 : gs.length ≤ npiv.1.length := extends_length sn.1
  have hrep_len : (List.replicate (k + 1) wFalse).length = k + 1 := List.length_replicate
  have hrep_mem : ∀ w ∈ List.replicate (k + 1) wFalse, w < n + npiv.1.length := by
    intro w hw; rw [List.mem_replicate] at hw; rcases hw with ⟨_, rfl⟩
    exact lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n)
  have spop := gPrefixPopcount_spec (List.replicate (k + 1) wFalse) npiv.2 sn.2.1 hrep_len hrep_mem sn.2.2.2.2.1
  have hle2 : npiv.1.length ≤ pop.1.length := extends_length spop.1
  have hle12 : gs.length ≤ pop.1.length := le_trans hle1 hle2
  have hnlen : npiv.2.length = k := by rw [sn.2.2.2.1, hpiv_len]
  have hplen : pop.2.2.length = k := by rw [spop.2.2.2.2.2.1, hnlen]
  have hds : ∀ d ∈ List.range (k - q), d < 2 ^ (k + 1) := by
    intro d hd; simp only [List.mem_range] at hd
    exact lt_of_lt_of_le (by omega : d < k + 1) (lt_of_lt_of_le (lt_two_pow_succ k) (by omega))
  have hps_mem : ∀ ap ∈ npiv.2.zip pop.2.2,
      ap.1 < n + pop.1.length ∧ ap.2.length = k + 1 ∧ ∀ w ∈ ap.2, w < n + pop.1.length := by
    intro ap hap
    have hm := List.of_mem_zip hap
    have hp := spop.2.2.2.2.2.2.1 ap.2 hm.2
    exact ⟨lt_of_lt_of_le (sn.2.2.2.2.1 ap.1 hm.1) (Nat.add_le_add_left hle2 n), hp.1, hp.2⟩
  have sloop := gFreeOneHotLoop_spec (List.range (k - q)) (npiv.2.zip pop.2.2) spop.2.1
    (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
    (lt_of_lt_of_le hwt (Nat.add_le_add_left hle12 n)) hds hps_mem
  refine ⟨extends_trans sn.1 (extends_trans spop.1 sloop.1), sloop.2.1, ?_, ?_, ?_, ?_⟩
  · have h1 : npiv.1.length = gs.length + pivW.length := sn.2.2.1
    have h2 : pop.1.length = npiv.1.length + 5 * (k + 1) * npiv.2.length := spop.2.2.1
    have h3 : (gFreeOneHotLoop n wFalse wTrue (k + 1) pop.1 (List.range (k - q)) (npiv.2.zip pop.2.2)).1.length ≤
        pop.1.length + (6 * (k + 1) + 1) * (List.range (k - q)).length * (npiv.2.zip pop.2.2).length := sloop.2.2.1
    have hzl : (npiv.2.zip pop.2.2).length ≤ k := by simp [hnlen]
    rw [hpiv_len] at h1
    rw [hnlen] at h2
    rw [List.length_range] at h3
    have h3' : (gFreeOneHotLoop n wFalse wTrue (k + 1) pop.1 (List.range (k - q))
        (npiv.2.zip pop.2.2)).1.length ≤ pop.1.length + (6 * (k + 1) + 1) * (k - q) * k :=
      le_trans h3 (Nat.add_le_add_left (Nat.mul_le_mul_left _ hzl) _)
    omega
  · rw [sloop.2.2.2.1]; simp [hnlen, hplen]
  · intro rw hrw
    have h := sloop.2.2.2.2.1 rw hrw
    simpa [List.length_range] using h
  · intro inp piv hinp hwf_val hwt_val hpiv_val i
    have hwf1 : wireVal npiv.1 inp wFalse = false := by rw [wireVal_extends sn.1 hinp hwf, hwf_val]
    have hwf2 : wireVal pop.1 inp wFalse = false := by rw [wireVal_extends spop.1 hinp (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n)), hwf1]
    have hwt2 : wireVal pop.1 inp wTrue = true := by rw [wireVal_extends (extends_trans sn.1 spop.1) hinp hwt, hwt_val]
    have hnp_val : npiv.2.map (wireVal npiv.1 inp) = List.ofFn (fun j : Fin k => !piv j) := by
      rw [sn.2.2.2.2.2 inp hinp]
      have hof : List.ofFn (fun j : Fin k => !piv j) = (List.ofFn piv).map (fun b => !b) := by
        apply List.ext_getElem <;> simp
      rw [hof, ← hpiv_val, List.map_map]
      rfl
    have hacc_val : bitsVal ((List.replicate (k + 1) wFalse).map (wireVal npiv.1 inp)) = 0 := by
      have hm : (List.replicate (k + 1) wFalse).map (wireVal npiv.1 inp) = List.replicate (k + 1) false := by
        simp [List.map_replicate, hwf1]
      rw [hm, bitsVal_replicate_false]
    have hbound : bitsVal ((List.replicate (k + 1) wFalse).map (wireVal npiv.1 inp)) + npiv.2.length < 2 ^ (k + 1) := by
      rw [hacc_val, hnlen, Nat.zero_add]; exact lt_two_pow_succ k
    have hspop := spop.2.2.2.2.2.2.2 inp hinp hbound
    rw [hacc_val, Nat.zero_add, hnp_val] at hspop
    have hzip_len : i.val < (npiv.2.zip pop.2.2).length := by simp [hnlen, hplen, i.isLt]
    have hrow := sloop.2.2.2.2.2 inp hinp hwf2 hwt2 i.val hzip_len
    rw [hrow]
    have hget : (npiv.2.zip pop.2.2)[i.val]'hzip_len =
        (npiv.2[i.val]'(by rw [hnlen]; exact i.isLt), pop.2.2[i.val]'(by rw [hplen]; exact i.isLt)) := by
      simp [List.getElem_zip]
    rw [hget]
    dsimp only
    have hn_i : wireVal pop.1 inp (npiv.2[i.val]'(by rw [hnlen]; exact i.isLt)) = !piv i := by
      rw [wireVal_extends spop.1 hinp (sn.2.2.2.2.1 _ (List.getElem_mem _))]
      have := congrArg (fun l : List Bool => l[i.val]?) hnp_val
      simp only [List.getElem?_map, List.getElem?_eq_getElem (by rw [hnlen]; exact i.isLt),
        List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      simpa using this
    have hp_i : bitsVal ((pop.2.2[i.val]'(by rw [hplen]; exact i.isLt)).map (wireVal pop.1 inp)) =
        freeCountBefore piv i := by
      have hrc : pop.2.2[i.val]'(by rw [hplen]; exact i.isLt) = pop.2.2.getD i.val [] := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hplen]; exact i.isLt)]
      rw [hrc, hspop.2 i.val (by rw [hnlen]; exact i.isLt)]
      have htake : (npiv.2.take i.val).map (wireVal npiv.1 inp) =
          (List.ofFn (fun j : Fin k => !piv j)).take i.val := by
        rw [List.map_take, hnp_val]
      rw [htake, count_true_take_ofFn, Nat.zero_add]
      rfl
    rw [hn_i, hp_i]
    apply List.ext_getElem <;> simp

def gWitDotY (n wFalse : ℕ) (gs : List Gate) (yW : List ℕ) :
    List (List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | w :: rest =>
    let d := gDot n wFalse gs w yW
    let r2 := gWitDotY n wFalse d.1 yW rest
    (r2.1, d.2 :: r2.2)

lemma gWitDotY_spec {n wFalse : ℕ} {gs : List Gate} (yW : List ℕ) (ws : List (List ℕ))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hy : ∀ w ∈ yW, w < n + gs.length)
    (hws : ∀ rw ∈ ws, rw.length = yW.length ∧ ∀ w ∈ rw, w < n + gs.length) :
    let res := gWitDotY n wFalse gs yW ws
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * yW.length * ws.length ∧
      res.2.length = ws.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (m k : ℕ) (y : Fin m → Bool) (wit : Fin k → Fin m → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        yW.map (wireVal gs inp) = List.ofFn y →
        ws.length = k →
        (∀ i : Fin k, (ws.getD i.val []).map (wireVal gs inp) = List.ofFn (wit i)) →
        res.2.map (wireVal res.1 inp) = List.ofFn (fun i : Fin k => dotBool (wit i) y) := by
  induction ws generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gWitDotY], by simp [gWitDotY], by simp [gWitDotY], ?_⟩
    intro inp m k y wit _ _ _ hlen _
    have hk0 : k = 0 := by simpa using hlen.symm
    subst hk0
    simp [gWitDotY]
  | cons rw rest ih =>
    have hrw := hws rw (by simp)
    dsimp only [gWitDotY]
    set d := gDot n wFalse gs rw yW
    have sd := gDot_spec rw yW hgs hwf hrw.2 hy
    have hle1 : gs.length ≤ d.1.length := extends_length sd.1
    have ih' := ih sd.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hy w hw) (Nat.add_le_add_left hle1 n))
      (fun rw' hrw' => have h := hws rw' (by simp [hrw']);
        ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
    have hle2 : d.1.length ≤ (gWitDotY n wFalse d.1 yW rest).1.length := extends_length ih'.1
    refine ⟨extends_trans sd.1 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : d.1.length ≤ gs.length + 5 * rw.length := sd.2.2.1
      have h2 : (gWitDotY n wFalse d.1 yW rest).1.length ≤ d.1.length + 5 * yW.length * rest.length := ih'.2.2.1
      rw [hrw.1] at h1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sd.2.2.2.1 (Nat.add_le_add_left hle2 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp m k y wit hinp hwf_val hy_val hlen hwit
      rcases k with _ | k
      · simp at hlen
      · have hlen' : rest.length = k := by simpa using hlen
        have hd_val : wireVal d.1 inp d.2 = dotBool (wit 0) y :=
          sd.2.2.2.2 inp m (wit 0) y hinp hwf_val (by simpa using hwit 0) hy_val
        have hih_val := ih'.2.2.2.2.2 inp m k y (fun i => wit i.succ) hinp
          (by rw [wireVal_extends sd.1 hinp hwf, hwf_val])
          (by rw [listVal_extends sd.1 hinp hy, hy_val]) hlen' (fun i => by
            have hmem := (hws _ (List.mem_cons_of_mem _ (getD_mem_of_lt rest (by rw [hlen']; exact i.isLt)))).2
            rw [listVal_extends sd.1 hinp hmem]
            simpa [List.getD_cons_succ] using hwit i.succ)
        simp only [List.map_cons]
        rw [wireVal_extends ih'.1 hinp sd.2.2.2.1, hd_val, hih_val]
        apply List.ext_getElem
        · simp
        · intro i hi1 hi2
          cases i with
          | zero => simp
          | succ i => simp

lemma any_filter_oneHot_free {k q : ℕ} (piv : Fin k → Bool)
    (hp : ((List.finRange k).filter piv).length = q) (a : Fin (k - q) → Bool)
    (i : Fin k) (hi : piv i = false) :
    ((List.finRange (k - q)).filter a).any (fun d => !piv i && decide (freeCountBefore piv i = d.val)) =
      freeAssign k q piv a i := by
  have hlt := freeCountBefore_lt piv hp hi
  unfold freeAssign
  simp only [hlt, ↓reduceDIte, hi, Bool.not_false, Bool.true_and]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨d, had, hd⟩
    have heq : (⟨freeCountBefore piv i, hlt⟩ : Fin (k - q)) = d := Fin.ext hd
    rw [heq]; exact had
  · intro ha
    exact ⟨⟨freeCountBefore piv i, hlt⟩, ha, rfl⟩

lemma any_filter_piv_true {k q : ℕ} (piv : Fin k → Bool) (a : Fin (k - q) → Bool)
    (i : Fin k) (hi : piv i = true) :
    ((List.finRange (k - q)).filter a).any (fun d => !piv i && decide (freeCountBefore piv i = d.val)) =
      false := by
  simp [hi]

def gFreeAssignRow (k q n wFalse : ℕ) (gs : List Gate) (a : Fin (k - q) → Bool)
    (row : List ℕ) : List Gate × ℕ :=
  let sel := ((List.finRange (k - q)).filter a).map (fun d => row.getD d.val wFalse)
  gOrList n wFalse gs sel

lemma gFreeAssignRow_spec {k q n wFalse : ℕ} {gs : List Gate} (a : Fin (k - q) → Bool) (row : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hlen : row.length = k - q) (hrow : ∀ w ∈ row, w < n + gs.length) :
    let res := gFreeAssignRow k q n wFalse gs a row
    Extends gs res.1 ∧ GoodGates n res.1 ∧ res.1.length ≤ gs.length + (k - q) ∧
      res.2 < n + res.1.length ∧
      ∀ (inp : List Bool) (f : Fin (k - q) → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        row.map (wireVal gs inp) = List.ofFn f →
        wireVal res.1 inp res.2 = ((List.finRange (k - q)).filter a).any f := by
  dsimp only [gFreeAssignRow]
  set sel := ((List.finRange (k - q)).filter a).map (fun d => row.getD d.val wFalse)
  have hsel_mem : ∀ w ∈ sel, w < n + gs.length := by
    intro w hw
    simp only [sel, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
    rcases hw with ⟨d, _, rfl⟩
    have hlt : d.val < row.length := by rw [hlen]; exact d.isLt
    have hrc : row.getD d.val wFalse = row[d.val]'hlt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [hrc]; exact hrow _ (List.getElem_mem hlt)
  have so := gOrList_spec sel hgs hwf hsel_mem
  refine ⟨so.1, so.2.1, ?_, so.2.2.2.1, ?_⟩
  · have hlen_sel : sel.length ≤ k - q := by
      calc sel.length = ((List.finRange (k - q)).filter a).length := by simp [sel]
        _ ≤ (List.finRange (k - q)).length := List.length_filter_le _ _
        _ = k - q := List.length_finRange
    have h1 := so.2.2.1
    omega
  · intro inp f hinp hwf_val hf
    set fil := (List.finRange (k - q)).filter a
    let f' : Fin fil.length → Bool := fun idx => f (fil[idx.val]'idx.isLt)
    have hsel_map : sel.map (wireVal gs inp) = List.ofFn f' := by
      apply List.ext_getElem
      · simp [sel, fil]
      · intro idx h1 h2
        simp only [sel, List.map_map, List.length_map] at h1
        simp only [List.getElem_map, Function.comp_apply, List.getElem_ofFn, f']
        have hlt : (fil[idx]'h1).val < row.length := by rw [hlen]; exact (fil[idx]'h1).isLt
        have hrc : row.getD (fil[idx]'h1).val wFalse = row[(fil[idx]'h1).val]'hlt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        dsimp only [sel]
        rw [List.getElem_map, hrc]
        have := congrArg (fun l : List Bool => l[(fil[idx]'h1).val]?) hf
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
          (fil[idx]'h1).isLt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa using this
    rw [so.2.2.2.2 inp fil.length f' hinp hwf_val hsel_map]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_finRange, true_and, f']
    constructor
    · rintro ⟨idx, hidx⟩
      exact ⟨fil[idx.val]'idx.isLt, List.getElem_mem _, hidx⟩
    · rintro ⟨d, hd, hfd⟩
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hd
      exact ⟨⟨idx, hidx⟩, hfd⟩

def gFreeAssign (k q n wFalse : ℕ) (gs : List Gate) (a : Fin (k - q) → Bool) :
    List (List ℕ) → List Gate × List ℕ
  | [] => (gs, [])
  | row :: rest =>
    let s := gFreeAssignRow k q n wFalse gs a row
    let r2 := gFreeAssign k q n wFalse s.1 a rest
    (r2.1, s.2 :: r2.2)

lemma gFreeAssign_spec {k q n wFalse : ℕ} {gs : List Gate} (a : Fin (k - q) → Bool)
    (rows : List (List ℕ))
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hrows : ∀ rw ∈ rows, rw.length = k - q ∧ ∀ w ∈ rw, w < n + gs.length) :
    let res := gFreeAssign k q n wFalse gs a rows
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (k - q) * rows.length ∧
      res.2.length = rows.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (F : ℕ → Fin (k - q) → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        (∀ idx (hi : idx < rows.length), (rows[idx]'hi).map (wireVal gs inp) = List.ofFn (F idx)) →
        res.2.map (wireVal res.1 inp) =
          (List.range rows.length).map (fun idx => ((List.finRange (k - q)).filter a).any (F idx)) := by
  induction rows generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gFreeAssign], by simp [gFreeAssign],
      by simp [gFreeAssign], fun _ _ _ _ _ => rfl⟩
  | cons row rest ih =>
    have hrow := hrows row (by simp)
    dsimp only [gFreeAssign]
    set s := gFreeAssignRow k q n wFalse gs a row
    have ss := gFreeAssignRow_spec a row hgs hwf hrow.1 hrow.2
    have hle1 : gs.length ≤ s.1.length := extends_length ss.1
    have ih' := ih ss.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (fun rw hrw => have h := hrows rw (by simp [hrw]);
        ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
    have hle2 : s.1.length ≤ (gFreeAssign k q n wFalse s.1 a rest).1.length := extends_length ih'.1
    refine ⟨extends_trans ss.1 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : s.1.length ≤ gs.length + (k - q) := ss.2.2.1
      have h2 : (gFreeAssign k q n wFalse s.1 a rest).1.length ≤
          s.1.length + (k - q) * rest.length := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le ss.2.2.2.1 (Nat.add_le_add_left hle2 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp F hinp hwf_val hF
      simp only [List.map_cons, List.length_cons, List.range_succ_eq_map]
      rw [wireVal_extends ih'.1 hinp ss.2.2.2.1,
        ss.2.2.2.2 inp (F 0) hinp hwf_val (hF 0 (by simp))]
      have hih := ih'.2.2.2.2.2 inp (fun idx => F (idx + 1)) hinp
        (by rw [wireVal_extends ss.1 hinp hwf, hwf_val]) (fun idx hi => by
          have hmem := (hrows (rest[idx]'hi) (by simp [List.getElem_mem])).2
          rw [listVal_extends ss.1 hinp hmem]
          exact hF (idx + 1) (by simp [hi]))
      rw [hih, List.map_map]
      rfl

def gZToWAux (k n wFalse : ℕ) (gs : List Gate) (fcW zW : List ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | b :: rest =>
    let col := (List.finRange k).map (fun cut => zW.getD ((b + k - cut.val) % k) wFalse)
    let d := gDot n wFalse gs fcW col
    let r2 := gZToWAux k n wFalse d.1 fcW zW rest
    (r2.1, d.2 :: r2.2)

def gZToW (k n wFalse : ℕ) (gs : List Gate) (fcW zW : List ℕ) : List Gate × List ℕ :=
  gZToWAux k n wFalse gs fcW zW (List.range k)

lemma gZToWAux_spec {k n wFalse : ℕ} {gs : List Gate} (hk : 0 < k) (fcW zW : List ℕ) (bs : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hfc : ∀ w ∈ fcW, w < n + gs.length) (hzlen : zW.length = k)
    (hz : ∀ w ∈ zW, w < n + gs.length) :
    let res := gZToWAux k n wFalse gs fcW zW bs
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * fcW.length * bs.length ∧
      res.2.length = bs.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (cutS : Fin k) (z : Fin k → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        fcW.map (wireVal gs inp) = List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        zW.map (wireVal gs inp) = List.ofFn z →
        res.2.map (wireVal res.1 inp) = bs.map (fun b => z ⟨(b + k - cutS.val) % k, Nat.mod_lt _ hk⟩) := by
  induction bs generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gZToWAux], by simp [gZToWAux], by simp [gZToWAux],
      fun _ _ _ _ _ _ _ => rfl⟩
  | cons b rest ih =>
    dsimp only [gZToWAux]
    set col := (List.finRange k).map (fun cut => zW.getD ((b + k - cut.val) % k) wFalse)
    set d := gDot n wFalse gs fcW col
    have hcol_mem : ∀ w ∈ col, w < n + gs.length := by
      intro w hw
      simp only [col, List.mem_map, List.mem_finRange] at hw
      rcases hw with ⟨cut, _, rfl⟩
      have hlt : (b + k - cut.val) % k < zW.length := by rw [hzlen]; exact Nat.mod_lt _ hk
      have hrc : zW.getD ((b + k - cut.val) % k) wFalse = zW[(b + k - cut.val) % k]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      rw [hrc]; exact hz _ (List.getElem_mem hlt)
    have sd := gDot_spec fcW col hgs hwf hfc hcol_mem
    have hle1 : gs.length ≤ d.1.length := extends_length sd.1
    have ih' := ih sd.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hfc w hw) (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hz w hw) (Nat.add_le_add_left hle1 n))
    have hle2 : d.1.length ≤ (gZToWAux k n wFalse d.1 fcW zW rest).1.length := extends_length ih'.1
    refine ⟨extends_trans sd.1 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : d.1.length ≤ gs.length + 5 * fcW.length := sd.2.2.1
      have h2 : (gZToWAux k n wFalse d.1 fcW zW rest).1.length ≤
          d.1.length + 5 * fcW.length * rest.length := ih'.2.2.1
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sd.2.2.2.1 (Nat.add_le_add_left hle2 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro inp cutS z hinp hwf_val hfc_val hz_val
      simp only [List.map_cons]
      have hcol_val : col.map (wireVal gs inp) =
          List.ofFn (fun cut : Fin k => z ⟨(b + k - cut.val) % k, Nat.mod_lt _ hk⟩) := by
        apply List.ext_getElem
        · simp [col]
        · intro idx h1 h2
          simp only [col, List.length_map, List.length_finRange] at h1
          simp only [col, List.map_map, List.getElem_map, List.getElem_finRange, Fin.val_cast,
            Function.comp_apply, List.getElem_ofFn]
          have hlt : (b + k - idx) % k < zW.length := by rw [hzlen]; exact Nat.mod_lt _ hk
          have hrc : zW.getD ((b + k - idx) % k) wFalse = zW[(b + k - idx) % k]'hlt := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
          rw [hrc]
          have := congrArg (fun l : List Bool => l[(b + k - idx) % k]?) hz_val
          simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
            Nat.mod_lt _ hk, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
          exact this
      have hd_val : wireVal d.1 inp d.2 = z ⟨(b + k - cutS.val) % k, Nat.mod_lt _ hk⟩ := by
        rw [sd.2.2.2.2 inp k (fun cut => decide (cut = cutS)) _ hinp hwf_val hfc_val hcol_val,
          dotBool_oneHot]
      rw [wireVal_extends ih'.1 hinp sd.2.2.2.1, hd_val,
        ih'.2.2.2.2.2 inp cutS z hinp (by rw [wireVal_extends sd.1 hinp hwf, hwf_val])
          (by rw [listVal_extends sd.1 hinp hfc, hfc_val])
          (by rw [listVal_extends sd.1 hinp hz, hz_val])]

lemma gZToW_spec {k n wFalse : ℕ} {gs : List Gate} (hk : 0 < k) (fcW zW : List ℕ)
    (hgs : GoodGates n gs) (hwf : wFalse < n + gs.length)
    (hfc : ∀ w ∈ fcW, w < n + gs.length) (hzlen : zW.length = k)
    (hz : ∀ w ∈ zW, w < n + gs.length) :
    let res := gZToW k n wFalse gs fcW zW
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * fcW.length * k ∧
      res.2.length = k ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (inp : List Bool) (cutS : Fin k) (z : Fin k → Bool),
        inp.length = n → wireVal gs inp wFalse = false →
        fcW.map (wireVal gs inp) = List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        zW.map (wireVal gs inp) = List.ofFn z →
        res.2.map (wireVal res.1 inp) =
          List.ofFn (fun b : Fin k => (zToW hk cutS z).testBit b.val) := by
  dsimp only [gZToW]
  have s := gZToWAux_spec hk fcW zW (List.range k) hgs hwf hfc hzlen hz
  refine ⟨s.1, s.2.1, by simpa using s.2.2.1, by simpa using s.2.2.2.1, s.2.2.2.2.1, ?_⟩
  intro inp cutS z hinp hwf_val hfc_val hz_val
  rw [s.2.2.2.2.2 inp cutS z hinp hwf_val hfc_val hz_val]
  apply List.ext_getElem <;> simp [zToW_testBit hk cutS z]

def rotWires (k s : ℕ) (w : List ℕ) : List ℕ :=
  (List.range k).map (fun i => w.getD ((i + k - s % k) % k) 0)

lemma rotWires_length (k s : ℕ) (w : List ℕ) : (rotWires k s w).length = k := by
  simp [rotWires]

lemma rotWires_mem {k s M : ℕ} (hk : 0 < k) {w : List ℕ} (hwlen : w.length = k)
    (hw : ∀ x ∈ w, x < M) : ∀ x ∈ rotWires k s w, x < M := by
  intro x hx
  simp only [rotWires, List.mem_map, List.mem_range] at hx
  rcases hx with ⟨i, _, rfl⟩
  have hlt : (i + k - s % k) % k < w.length := by rw [hwlen]; exact Nat.mod_lt _ hk
  have hrc : w.getD ((i + k - s % k) % k) 0 = w[(i + k - s % k) % k]'hlt := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  rw [hrc]; exact hw _ (List.getElem_mem hlt)

lemma rotWires_map {k s : ℕ} (hk : 0 < k) (gs : List Gate) (inp : List Bool)
    (w : List ℕ) (hwlen : w.length = k) (word : ℕ) (hword : word < 2 ^ k)
    (hw : w.map (wireVal gs inp) = List.ofFn (fun i : Fin k => word.testBit i.val)) :
    (rotWires k s w).map (wireVal gs inp) = List.ofFn (fun i : Fin k => (rotFn k s word).testBit i.val) := by
  apply List.ext_getElem
  · simp [rotWires]
  · intro i h1 h2
    simp only [rotWires, List.length_map, List.length_range] at h1
    simp only [rotWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
      List.getElem_ofFn, rotFn_testBit hk s word hword h1]
    have hlt : (i + k - s % k) % k < w.length := by rw [hwlen]; exact Nat.mod_lt _ hk
    have hrc : w.getD ((i + k - s % k) % k) 0 = w[(i + k - s % k) % k]'hlt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    rw [hrc]
    have := congrArg (fun l : List Bool => l[(i + k - s % k) % k]?) hw
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
      Nat.mod_lt _ hk, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
    exact this

def gStepAux (k n : ℕ) (gs : List Gate) (w : List ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, [])
  | i :: rest =>
    let a0 := w.getD i 0
    let a1 := w.getD ((i + 1) % k) 0
    let a2 := w.getD ((i + 2) % k) 0
    let na1 := gNot n gs a1
    let t1 := gAnd n na1.1 na1.2 a2
    let xr := gXor n t1.1 a0 t1.2
    let r2 := gStepAux k n xr.1 w rest
    (r2.1, xr.2 :: r2.2)

def gStep (k n : ℕ) (gs : List Gate) (w : List ℕ) : List Gate × List ℕ :=
  gStepAux k n gs w (List.range k)

lemma gStepAux_spec {k n : ℕ} {gs : List Gate} (hk : 0 < k) (w : List ℕ) (is : List ℕ)
    (hgs : GoodGates n gs) (hwlen : w.length = k) (hw : ∀ x ∈ w, x < n + gs.length)
    (his : ∀ i ∈ is, i < k) :
    let res := gStepAux k n gs w is
    Extends gs res.1 ∧ GoodGates n res.1 ∧ res.1.length = gs.length + 6 * is.length ∧
      res.2.length = is.length ∧ (∀ x ∈ res.2, x < n + res.1.length) ∧
      ∀ (inp : List Bool) (word : ℕ), inp.length = n →
        w.map (wireVal gs inp) = List.ofFn (fun i : Fin k => word.testBit i.val) →
        res.2.map (wireVal res.1 inp) = is.map (fun i => (stepFn k word).testBit i) := by
  induction is generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gStepAux], by simp [gStepAux], by simp [gStepAux],
      fun _ _ _ _ => rfl⟩
  | cons i rest ih =>
    have hi : i < k := his i (by simp)
    dsimp only [gStepAux]
    have hget : ∀ idx, idx < k → w.getD idx 0 < n + gs.length := by
      intro idx hidx
      have hlt : idx < w.length := by rw [hwlen]; exact hidx
      have hrc : w.getD idx 0 = w[idx]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      rw [hrc]; exact hw _ (List.getElem_mem hlt)
    set a0 := w.getD i 0
    set a1 := w.getD ((i + 1) % k) 0
    set a2 := w.getD ((i + 2) % k) 0
    set na1 := gNot n gs a1
    set t1 := gAnd n na1.1 na1.2 a2
    set xr := gXor n t1.1 a0 t1.2
    have ha0 := hget i hi
    have ha1 := hget ((i + 1) % k) (Nat.mod_lt _ hk)
    have ha2 := hget ((i + 2) % k) (Nat.mod_lt _ hk)
    have s1 := gNot_spec hgs ha1
    have hle1 : gs.length ≤ na1.1.length := extends_length s1.1
    have s2 := gAnd_spec s1.2.1 s1.2.2.2.1 (lt_of_lt_of_le ha2 (Nat.add_le_add_left hle1 n))
    have hle2 : na1.1.length ≤ t1.1.length := extends_length s2.1
    have hle12 : gs.length ≤ t1.1.length := le_trans hle1 hle2
    have s3 := gXor_spec s2.2.1 (lt_of_lt_of_le ha0 (Nat.add_le_add_left hle12 n)) s2.2.2.2.1
    have h13 : Extends gs xr.1 := extends_trans s1.1 (extends_trans s2.1 s3.1)
    have hle13 : gs.length ≤ xr.1.length := extends_length h13
    have ih' := ih s3.2.1 (fun x hx => lt_of_lt_of_le (hw x hx) (Nat.add_le_add_left hle13 n))
      (fun j hj => his j (by simp [hj]))
    have hle4 : xr.1.length ≤ (gStepAux k n xr.1 w rest).1.length := extends_length ih'.1
    refine ⟨extends_trans h13 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : na1.1.length = gs.length + 1 := s1.2.2.1
      have h2 : t1.1.length = na1.1.length + 1 := s2.2.2.1
      have h3 : xr.1.length = t1.1.length + 4 := s3.2.2.1
      have h4 : (gStepAux k n xr.1 w rest).1.length = xr.1.length + 6 * rest.length := ih'.2.2.1
      simp only [List.length_cons]
      omega
    · intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact lt_of_lt_of_le s3.2.2.2.1 (Nat.add_le_add_left hle4 n)
      · exact ih'.2.2.2.2.1 x hx
    · intro inp word hinp hwm
      have hval_get : ∀ idx (hidx : idx < k), wireVal gs inp (w.getD idx 0) = word.testBit idx := by
        intro idx hidx
        have hlt : idx < w.length := by rw [hwlen]; exact hidx
        have hrc : w.getD idx 0 = w[idx]'hlt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hrc]
        have := congrArg (fun l : List Bool => l[idx]?) hwm
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
          hidx, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        exact this
      have hxr_val : wireVal xr.1 inp xr.2 = (stepFn k word).testBit i := by
        rw [s3.2.2.2.2 inp hinp, wireVal_extends (extends_trans s1.1 s2.1) hinp ha0,
          s2.2.2.2.2 inp hinp, s1.2.2.2.2 inp hinp,
          wireVal_extends s1.1 hinp ha2, hval_get i hi, hval_get ((i + 1) % k) (Nat.mod_lt _ hk),
          hval_get ((i + 2) % k) (Nat.mod_lt _ hk), stepFn_testBit hi]
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp s3.2.2.2.1, hxr_val,
        ih'.2.2.2.2.2 inp word hinp (by rw [listVal_extends h13 hinp hw, hwm])]

lemma gStep_spec {k n : ℕ} {gs : List Gate} (hk : 0 < k) (w : List ℕ)
    (hgs : GoodGates n gs) (hwlen : w.length = k) (hw : ∀ x ∈ w, x < n + gs.length) :
    let res := gStep k n gs w
    Extends gs res.1 ∧ GoodGates n res.1 ∧ res.1.length = gs.length + 6 * k ∧
      res.2.length = k ∧ (∀ x ∈ res.2, x < n + res.1.length) ∧
      ∀ (inp : List Bool) (word : ℕ), inp.length = n →
        w.map (wireVal gs inp) = List.ofFn (fun i : Fin k => word.testBit i.val) →
        res.2.map (wireVal res.1 inp) = List.ofFn (fun i : Fin k => (stepFn k word).testBit i.val) := by
  dsimp only [gStep]
  have s := gStepAux_spec hk w (List.range k) hgs hwlen hw (fun i hi => List.mem_range.mp hi)
  refine ⟨s.1, s.2.1, by simpa using s.2.2.1, by simpa using s.2.2.2.1, s.2.2.2.2.1, ?_⟩
  intro inp word hinp hwm
  rw [s.2.2.2.2.2 inp word hinp hwm]
  apply List.ext_getElem <;> simp

def gStateLoop {r : ℕ} (k n : ℕ) (gs : List Gate) (col : Bool) (w : List ℕ) (cW : List (List ℕ))
    (xW : List ℕ) : List (Fin r) → List Gate × List ℕ
  | [] => (gs, xW)
  | j :: rest =>
    let g := if col then 2 else 1
    let t1 := gVecXor n gs xW (rotWires k g xW)
    let t2 := gVecXor n t1.1 t1.2 (rotWires k (k - g) xW)
    let st := gStep k n t2.1 t2.2
    let rw := rotWires k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w
    let t3 := gVecXor n st.1 st.2 rw
    let t4 := gVecXor n t3.1 t3.2 (cW.getD j.val [])
    gStateLoop k n t4.1 col w cW t4.2 rest

lemma gStateLoop_spec {r : ℕ} {k n : ℕ} {gs : List Gate} (hk : 0 < k) (col : Bool)
    (w : List ℕ) (cW : List (List ℕ)) (xW : List ℕ) (js : List (Fin r))
    (hgs : GoodGates n gs) (hwlen : w.length = k) (hw : ∀ x ∈ w, x < n + gs.length)
    (hcWlen : cW.length = r) (hcW : ∀ rw ∈ cW, rw.length = k ∧ ∀ x ∈ rw, x < n + gs.length)
    (hxWlen : xW.length = k) (hxW : ∀ x ∈ xW, x < n + gs.length) :
    let res := gStateLoop k n gs col w cW xW js
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 22 * k * js.length ∧
      res.2.length = k ∧ (∀ x ∈ res.2, x < n + res.1.length) ∧
      ∀ (inp : List Bool) (word x0 : ℕ) (c : Fin r → Fin (2 ^ k)),
        inp.length = n → word < 2 ^ k → x0 < 2 ^ k →
        w.map (wireVal gs inp) = List.ofFn (fun i : Fin k => word.testBit i.val) →
        xW.map (wireVal gs inp) = List.ofFn (fun i : Fin k => x0.testBit i.val) →
        (∀ j : Fin r, (cW.getD j.val []).map (wireVal gs inp) =
          List.ofFn (fun i : Fin k => (c j).val.testBit i.val)) →
        let g := if col then 2 else 1
        let xF := js.foldl (fun x j =>
          stepFn k (x ^^^ rotFn k g x ^^^ rotFn k (k - g) x) ^^^
            rotFn k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) word ^^^ (c j).val) x0
        res.2.map (wireVal res.1 inp) = List.ofFn (fun i : Fin k => xF.testBit i.val) := by
  induction js generalizing gs xW with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gStateLoop], hxWlen, hxW, ?_⟩
    intro inp word x0 c _ _ _ _ hxW_val _
    exact hxW_val
  | cons j rest ih =>
    dsimp only [gStateLoop]
    set g := if col then 2 else 1
    set t1 := gVecXor n gs xW (rotWires k g xW)
    set t2 := gVecXor n t1.1 t1.2 (rotWires k (k - g) xW)
    set st := gStep k n t2.1 t2.2
    set rw := rotWires k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) w
    set t3 := gVecXor n st.1 st.2 rw
    set t4 := gVecXor n t3.1 t3.2 (cW.getD j.val [])
    have s1 := gVecXor_spec xW (rotWires k g xW) hgs hxW (rotWires_mem hk hxWlen hxW)
    have hle1 : gs.length ≤ t1.1.length := extends_length s1.1
    have ht1len : t1.2.length = k := by rw [s1.2.2.2.1, hxWlen, rotWires_length]; simp
    have s2 := gVecXor_spec t1.2 (rotWires k (k - g) xW) s1.2.1 s1.2.2.2.2.1
      (rotWires_mem hk hxWlen (fun x hx => lt_of_lt_of_le (hxW x hx) (Nat.add_le_add_left hle1 n)))
    have hle2 : t1.1.length ≤ t2.1.length := extends_length s2.1
    have hle12 : gs.length ≤ t2.1.length := le_trans hle1 hle2
    have ht2len : t2.2.length = k := by rw [s2.2.2.2.1, ht1len, rotWires_length]; simp
    have s3 := gStep_spec hk t2.2 s2.2.1 ht2len s2.2.2.2.2.1
    have hle3 : t2.1.length ≤ st.1.length := extends_length s3.1
    have hle13 : gs.length ≤ st.1.length := le_trans hle12 hle3
    have hrw_mem : ∀ x ∈ rw, x < n + st.1.length :=
      rotWires_mem hk hwlen (fun x hx => lt_of_lt_of_le (hw x hx) (Nat.add_le_add_left hle13 n))
    have s4 := gVecXor_spec st.2 rw s3.2.1 s3.2.2.2.2.1 hrw_mem
    have hle4 : st.1.length ≤ t3.1.length := extends_length s4.1
    have hle14 : gs.length ≤ t3.1.length := le_trans hle13 hle4
    have ht3len : t3.2.length = k := by rw [s4.2.2.2.1, s3.2.2.2.1, rotWires_length]; simp
    have hcj := hcW _ (getD_mem_of_lt cW (by rw [hcWlen]; exact j.isLt))
    have hcj_mem : ∀ x ∈ cW.getD j.val [], x < n + t3.1.length :=
      fun x hx => lt_of_lt_of_le (hcj.2 x hx) (Nat.add_le_add_left hle14 n)
    have s5 := gVecXor_spec t3.2 (cW.getD j.val []) s4.2.1 s4.2.2.2.2.1 hcj_mem
    have hle5 : t3.1.length ≤ t4.1.length := extends_length s5.1
    have h15 : Extends gs t4.1 :=
      extends_trans s1.1 (extends_trans s2.1 (extends_trans s3.1 (extends_trans s4.1 s5.1)))
    have hle15 : gs.length ≤ t4.1.length := extends_length h15
    have ht4len : t4.2.length = k := by rw [s5.2.2.2.1, ht3len, hcj.1]; simp
    have ih' := ih t4.2 s5.2.1 (fun x hx => lt_of_lt_of_le (hw x hx) (Nat.add_le_add_left hle15 n))
      (fun r' hr' => have h := hcW r' hr';
        ⟨h.1, fun x hx => lt_of_lt_of_le (h.2 x hx) (Nat.add_le_add_left hle15 n)⟩)
      ht4len s5.2.2.2.2.1
    refine ⟨extends_trans h15 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ih'.2.2.2.2.1, ?_⟩
    · have h1 : t1.1.length ≤ gs.length + 4 * xW.length := s1.2.2.1
      have h2 : t2.1.length ≤ t1.1.length + 4 * t1.2.length := s2.2.2.1
      have h3 : st.1.length = t2.1.length + 6 * k := s3.2.2.1
      have h4 : t3.1.length ≤ st.1.length + 4 * st.2.length := s4.2.2.1
      have h5 : t4.1.length ≤ t3.1.length + 4 * t3.2.length := s5.2.2.1
      have h6 : (gStateLoop k n t4.1 col w cW t4.2 rest).1.length ≤
          t4.1.length + 22 * k * rest.length := ih'.2.2.1
      rw [hxWlen] at h1; rw [ht1len] at h2; rw [s3.2.2.2.1] at h4; rw [ht3len] at h5
      simp only [List.length_cons]
      nlinarith
    · intro inp word x0 c hinp hword hx0 hw_val hxW_val hcW_val
      have ht1_val : t1.2.map (wireVal t1.1 inp) =
          List.ofFn (fun i : Fin k => (x0 ^^^ rotFn k g x0).testBit i.val) := by
        rw [s1.2.2.2.2.2 inp k (fun i => x0.testBit i.val) (fun i => (rotFn k g x0).testBit i.val)
          hinp hxW_val (rotWires_map hk gs inp xW hxWlen x0 hx0 hxW_val)]
        apply List.ext_getElem <;> simp [Nat.testBit_xor]
      have ht2_val : t2.2.map (wireVal t2.1 inp) =
          List.ofFn (fun i : Fin k => (x0 ^^^ rotFn k g x0 ^^^ rotFn k (k - g) x0).testBit i.val) := by
        rw [s2.2.2.2.2.2 inp k _ (fun i => (rotFn k (k - g) x0).testBit i.val) hinp ht1_val
          (by rw [listVal_extends s1.1 hinp (rotWires_mem hk hxWlen hxW)]
              exact rotWires_map hk gs inp xW hxWlen x0 hx0 hxW_val)]
        apply List.ext_getElem <;> simp [Nat.testBit_xor]
      have hst_val : st.2.map (wireVal st.1 inp) =
          List.ofFn (fun i : Fin k => (stepFn k (x0 ^^^ rotFn k g x0 ^^^ rotFn k (k - g) x0)).testBit i.val) :=
        s3.2.2.2.2.2 inp (x0 ^^^ rotFn k g x0 ^^^ rotFn k (k - g) x0) hinp ht2_val
      have hrw_val : rw.map (wireVal st.1 inp) =
          List.ofFn (fun i : Fin k => (rotFn k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) word).testBit i.val) := by
        rw [listVal_extends (extends_trans s1.1 (extends_trans s2.1 s3.1)) hinp
          (rotWires_mem hk hwlen hw)]
        exact rotWires_map hk gs inp w hwlen word hword hw_val
      have ht3_val : t3.2.map (wireVal t3.1 inp) =
          List.ofFn (fun i : Fin k =>
            (stepFn k (x0 ^^^ rotFn k g x0 ^^^ rotFn k (k - g) x0) ^^^
              rotFn k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) word).testBit i.val) := by
        rw [s4.2.2.2.2.2 inp k _ _ hinp hst_val hrw_val]
        apply List.ext_getElem <;> simp [Nat.testBit_xor]
      set x1 := stepFn k (x0 ^^^ rotFn k g x0 ^^^ rotFn k (k - g) x0) ^^^
        rotFn k (if col then 3 * (j.val + 1) + 1 else 2 * j.val) word ^^^ (c j).val
      have hx1 : x1 < 2 ^ k :=
        Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k _ word)) (c j).isLt
      have ht4_val : t4.2.map (wireVal t4.1 inp) = List.ofFn (fun i : Fin k => x1.testBit i.val) := by
        rw [s5.2.2.2.2.2 inp k _ (fun i => (c j).val.testBit i.val) hinp ht3_val
          (by rw [listVal_extends (extends_trans s1.1 (extends_trans s2.1 (extends_trans s3.1 s4.1))) hinp hcj.2]
              exact hcW_val j)]
        apply List.ext_getElem <;> simp [x1, Nat.testBit_xor]
      simp only [List.foldl_cons]
      refine ih'.2.2.2.2.2 inp word x1 c hinp hword hx1
        (by rw [listVal_extends h15 hinp hw, hw_val]) ht4_val (fun j' => ?_)
      have hcj' := hcW _ (getD_mem_of_lt cW (by rw [hcWlen]; exact j'.isLt))
      rw [listVal_extends h15 hinp hcj'.2, hcW_val j']

def gState (k r n : ℕ) (gs : List Gate) (col : Bool) (w u : List ℕ) (cW : List (List ℕ)) :
    List Gate × List ℕ :=
  let init := gVecXor n gs (rotWires k (if col then 3 else 1) w) u
  gStateLoop k n init.1 col w cW init.2 (List.finRange r)

lemma gState_spec {k r n : ℕ} {gs : List Gate} (hk : 0 < k) (col : Bool)
    (w u : List ℕ) (cW : List (List ℕ))
    (hgs : GoodGates n gs) (hwlen : w.length = k) (hw : ∀ x ∈ w, x < n + gs.length)
    (hulen : u.length = k) (hu : ∀ x ∈ u, x < n + gs.length)
    (hcWlen : cW.length = r) (hcW : ∀ rw ∈ cW, rw.length = k ∧ ∀ x ∈ rw, x < n + gs.length) :
    let res := gState k r n gs col w u cW
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 4 * k + 22 * r * k ∧
      res.2.length = k ∧ (∀ x ∈ res.2, x < n + res.1.length) ∧
      ∀ (inp : List Bool) (word : ℕ) (uv : Fin (2 ^ k)) (c : Fin r → Fin (2 ^ k)),
        inp.length = n → word < 2 ^ k →
        w.map (wireVal gs inp) = List.ofFn (fun i : Fin k => word.testBit i.val) →
        u.map (wireVal gs inp) = List.ofFn (fun i : Fin k => uv.val.testBit i.val) →
        (∀ j : Fin r, (cW.getD j.val []).map (wireVal gs inp) =
          List.ofFn (fun i : Fin k => (c j).val.testBit i.val)) →
        res.2.map (wireVal res.1 inp) =
          List.ofFn (fun i : Fin k => (stateFn k r col word uv.val c).testBit i.val) := by
  dsimp only [gState]
  set init := gVecXor n gs (rotWires k (if col then 3 else 1) w) u
  have si := gVecXor_spec (rotWires k (if col then 3 else 1) w) u hgs (rotWires_mem hk hwlen hw) hu
  have hle1 : gs.length ≤ init.1.length := extends_length si.1
  have hilen : init.2.length = k := by rw [si.2.2.2.1, rotWires_length, hulen]; simp
  have sl := gStateLoop_spec hk col w cW init.2 (List.finRange r) si.2.1 hwlen
    (fun x hx => lt_of_lt_of_le (hw x hx) (Nat.add_le_add_left hle1 n))
    hcWlen (fun rw hrw => have h := hcW rw hrw;
      ⟨h.1, fun x hx => lt_of_lt_of_le (h.2 x hx) (Nat.add_le_add_left hle1 n)⟩)
    hilen si.2.2.2.2.1
  refine ⟨extends_trans si.1 sl.1, sl.2.1, ?_, sl.2.2.2.1, sl.2.2.2.2.1, ?_⟩
  · have h1 : init.1.length ≤ gs.length + 4 * (rotWires k (if col then 3 else 1) w).length := si.2.2.1
    have h2 : (gStateLoop k n init.1 col w cW init.2 (List.finRange r)).1.length ≤
        init.1.length + 22 * k * (List.finRange r).length := sl.2.2.1
    rw [rotWires_length] at h1
    rw [List.length_finRange] at h2
    nlinarith
  · intro inp word uv c hinp hword hw_val hu_val hcW_val
    set x0 := rotFn k (if col then 3 else 1) word ^^^ uv.val
    have hx0 : x0 < 2 ^ k := Nat.xor_lt_two_pow (rotFn_lt k _ word) uv.isLt
    have hinit_val : init.2.map (wireVal init.1 inp) = List.ofFn (fun i : Fin k => x0.testBit i.val) := by
      rw [si.2.2.2.2.2 inp k _ _ hinp (rotWires_map hk gs inp w hwlen word hword hw_val) hu_val]
      apply List.ext_getElem <;> simp [x0, Nat.testBit_xor]
    refine sl.2.2.2.2.2 inp word x0 c hinp hword hx0
      (by rw [listVal_extends si.1 hinp hw, hw_val]) hinit_val (fun j => ?_)
    have hcj := hcW _ (getD_mem_of_lt cW (by rw [hcWlen]; exact j.isLt))
    rw [listVal_extends si.1 hinp hcj.2, hcW_val j]

lemma dotBool_testBit_eq_parityFn (k mask x : ℕ) :
    dotBool (fun i : Fin k => mask.testBit i.val) (fun i : Fin k => x.testBit i.val) =
      parityFn k mask x := by
  unfold dotBool parityFn
  have hr : List.range k = (List.finRange k).map Fin.val := by
    apply List.ext_getElem <;> simp
  rw [hr, List.foldl_map]

def gParityLoop (k r m n wFalse : ℕ) (gs : List Gate) (stF stT : List ℕ) :
    List (Fin m) → List Gate × List ℕ
  | [] => (gs, [])
  | j :: rest =>
    let pA := gDot n wFalse gs (aWires k r j) stF
    let pB := gDot n wFalse pA.1 (bWires k r m j) stT
    let x := gXor n pB.1 pA.2 pB.2
    let r2 := gParityLoop k r m n wFalse x.1 stF stT rest
    (r2.1, x.2 :: r2.2)

lemma gParityLoop_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse : ℕ}
    (stF stT : List ℕ) (js : List (Fin m))
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hstFlen : stF.length = k) (hstF : ∀ w ∈ stF, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hstTlen : stT.length = k) (hstT : ∀ w ∈ stT, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gParityLoop k r m n wFalse gs stF stT js
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (10 * k + 4) * js.length ∧
      res.2.length = js.length ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (word : ℕ),
        let inp := mkInp k r m u v cr cc A B y t
        wireVal gs inp wFalse = false →
        stF.map (wireVal gs inp) = List.ofFn (fun i : Fin k => (stateFn k r false word u.val cr).testBit i.val) →
        stT.map (wireVal gs inp) = List.ofFn (fun i : Fin k => (stateFn k r true word v.val cc).testBit i.val) →
        res.2.map (wireVal res.1 inp) = js.map (fFn k r m u.val v.val cr cc A B word) := by
  intro n
  induction js generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gParityLoop], by simp [gParityLoop], by simp [gParityLoop],
      fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | cons j rest ih =>
    dsimp only [gParityLoop]
    set pA := gDot n wFalse gs (aWires k r j) stF
    set pB := gDot n wFalse pA.1 (bWires k r m j) stT
    set x := gXor n pB.1 pA.2 pB.2
    have ha_mem : ∀ w ∈ aWires k r j, w < n + gs.length :=
      fun w hw => lt_of_lt_of_le (aWires_mem j hw) (Nat.le_add_right n gs.length)
    have sA := gDot_spec (aWires k r j) stF hgs hwf ha_mem hstF
    have hle1 : gs.length ≤ pA.1.length := extends_length sA.1
    have hb_mem : ∀ w ∈ bWires k r m j, w < n + pA.1.length :=
      fun w hw => lt_of_lt_of_le (bWires_mem j hw) (by omega)
    have sB := gDot_spec (bWires k r m j) stT sA.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      hb_mem (fun w hw => lt_of_lt_of_le (hstT w hw) (Nat.add_le_add_left hle1 n))
    have hle2 : pA.1.length ≤ pB.1.length := extends_length sB.1
    have sx := gXor_spec sB.2.1 (lt_of_lt_of_le sA.2.2.2.1 (Nat.add_le_add_left hle2 n)) sB.2.2.2.1
    have h13 : Extends gs x.1 := extends_trans sA.1 (extends_trans sB.1 sx.1)
    have hle13 : gs.length ≤ x.1.length := extends_length h13
    have ih' := ih sx.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle13 n))
      (fun w hw => lt_of_lt_of_le (hstF w hw) (Nat.add_le_add_left hle13 n))
      (fun w hw => lt_of_lt_of_le (hstT w hw) (Nat.add_le_add_left hle13 n))
    have hle4 : x.1.length ≤ (gParityLoop k r m n wFalse x.1 stF stT rest).1.length :=
      extends_length ih'.1
    refine ⟨extends_trans h13 ih'.1, ih'.2.1, ?_, congrArg (· + 1) ih'.2.2.2.1, ?_, ?_⟩
    · have h1 : pA.1.length ≤ gs.length + 5 * (aWires k r j).length := sA.2.2.1
      have h2 : pB.1.length ≤ pA.1.length + 5 * (bWires k r m j).length := sB.2.2.1
      have h3 : x.1.length = pB.1.length + 4 := sx.2.2.1
      have h4 : (gParityLoop k r m n wFalse x.1 stF stT rest).1.length ≤
          x.1.length + (10 * k + 4) * rest.length := ih'.2.2.1
      have halen : (aWires k r j).length = k := by simp [aWires]
      have hblen : (bWires k r m j).length = k := by simp [bWires]
      rw [halen] at h1; rw [hblen] at h2
      simp only [List.length_cons]
      nlinarith
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact lt_of_lt_of_le sx.2.2.2.1 (Nat.add_le_add_left hle4 n)
      · exact ih'.2.2.2.2.1 w hw
    · intro u v cr cc A B y t word hwf_val hstF_val hstT_val
      set inp := mkInp k r m u v cr cc A B y t
      have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
      have ha_val : (aWires k r j).map (wireVal gs inp) = List.ofFn (fun i : Fin k => (A j).val.testBit i.val) := by
        apply List.ext_getElem
        · simp [aWires]
        · intro i h1 h2
          simp only [aWires, List.length_map, List.length_range] at h1
          simp only [aWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
            List.getElem_ofFn]
          rw [wireVal_input hgs hinp (aWires_mem j (by simp [aWires, h1]))]
          exact mkInp_getD_A u v cr cc A B y t j h1
      have hb_val : (bWires k r m j).map (wireVal pA.1 inp) = List.ofFn (fun i : Fin k => (B j).val.testBit i.val) := by
        rw [listVal_extends sA.1 hinp (fun w hw => lt_of_lt_of_le (bWires_mem j hw) (Nat.le_add_right n gs.length))]
        apply List.ext_getElem
        · simp [bWires]
        · intro i h1 h2
          simp only [bWires, List.length_map, List.length_range] at h1
          simp only [bWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
            List.getElem_ofFn]
          rw [wireVal_input hgs hinp (bWires_mem j (by simp [bWires, h1]))]
          exact mkInp_getD_B u v cr cc A B y t j h1
      have hpA_val : wireVal pA.1 inp pA.2 = parityFn k (A j).val (stateFn k r false word u.val cr) := by
        rw [sA.2.2.2.2 inp k _ _ hinp hwf_val ha_val hstF_val, dotBool_testBit_eq_parityFn]
      have hpB_val : wireVal pB.1 inp pB.2 = parityFn k (B j).val (stateFn k r true word v.val cc) := by
        refine (sB.2.2.2.2 inp k _ _ hinp (by rw [wireVal_extends sA.1 hinp hwf, hwf_val]) hb_val
          (by rw [listVal_extends sA.1 hinp hstT, hstT_val])).trans (dotBool_testBit_eq_parityFn _ _ _)
      have hx_val : wireVal x.1 inp x.2 = fFn k r m u.val v.val cr cc A B word j := by
        rw [sx.2.2.2.2 inp hinp, wireVal_extends sB.1 hinp sA.2.2.2.1, hpA_val, hpB_val]
        rfl
      simp only [List.map_cons]
      rw [wireVal_extends ih'.1 hinp sx.2.2.2.1, hx_val,
        ih'.2.2.2.2.2 u v cr cc A B y t word
          (by rw [wireVal_extends h13 hinp hwf, hwf_val])
          (by rw [listVal_extends h13 hinp hstF, hstF_val])
          (by rw [listVal_extends h13 hinp hstT, hstT_val])]

def gFFn (k r m n wFalse : ℕ) (gs : List Gate) (w : List ℕ) : List Gate × List ℕ :=
  let crList := (List.finRange r).map (crWires k)
  let ccList := (List.finRange r).map (ccWires k r)
  let stF := gState k r n gs false w (uWires k) crList
  let stT := gState k r n stF.1 true w (vWires k) ccList
  gParityLoop k r m n wFalse stT.1 stF.2 stT.2 (List.finRange m)

lemma gFFn_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse : ℕ} (w : List ℕ)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwlen : w.length = k) (hw : ∀ x ∈ w, x < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gFFn k r m n wFalse gs w
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 8 * k + 44 * r * k + (10 * k + 4) * m ∧
      res.2.length = m ∧ (∀ x ∈ res.2, x < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (word : ℕ),
        word < 2 ^ k → wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        w.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun i : Fin k => word.testBit i.val) →
        res.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fFn k r m u.val v.val cr cc A B word) := by
  intro n
  dsimp only [gFFn]
  set crList := (List.finRange r).map (crWires k)
  set ccList := (List.finRange r).map (ccWires k r)
  set stF := gState k r n gs false w (uWires k) crList
  set stT := gState k r n stF.1 true w (vWires k) ccList
  have hulen : (uWires k).length = k := by simp [uWires]
  have hvlen : (vWires k).length = k := by simp [vWires]
  have hu_mem : ∀ x ∈ uWires k, x < n + gs.length :=
    fun x hx => lt_of_lt_of_le (uWires_mem k hx) (Nat.le_add_right n gs.length)
  have hv_mem : ∀ x ∈ vWires k, x < n + gs.length :=
    fun x hx => lt_of_lt_of_le (vWires_mem k hx) (Nat.le_add_right n gs.length)
  have hcrlen : crList.length = r := by simp [crList]
  have hcclen : ccList.length = r := by simp [ccList]
  have hcr_mem : ∀ rw ∈ crList, rw.length = k ∧ ∀ x ∈ rw, x < n + gs.length := by
    intro rw hrw; simp only [crList, List.mem_map, List.mem_finRange] at hrw
    rcases hrw with ⟨j, _, rfl⟩
    exact ⟨by simp [crWires], fun x hx => lt_of_lt_of_le (crWires_mem j hx) (Nat.le_add_right n gs.length)⟩
  have hcc_mem : ∀ rw ∈ ccList, rw.length = k ∧ ∀ x ∈ rw, x < n + gs.length := by
    intro rw hrw; simp only [ccList, List.mem_map, List.mem_finRange] at hrw
    rcases hrw with ⟨j, _, rfl⟩
    exact ⟨by simp [ccWires], fun x hx => lt_of_lt_of_le (ccWires_mem j hx) (Nat.le_add_right n gs.length)⟩
  have sF := gState_spec hk false w (uWires k) crList hgs hwlen hw hulen hu_mem hcrlen hcr_mem
  have hle1 : gs.length ≤ stF.1.length := extends_length sF.1
  have sT := gState_spec hk true w (vWires k) ccList sF.2.1 hwlen
    (fun x hx => lt_of_lt_of_le (hw x hx) (Nat.add_le_add_left hle1 n))
    hvlen (fun x hx => lt_of_lt_of_le (hv_mem x hx) (Nat.add_le_add_left hle1 n))
    hcclen (fun rw hrw => have h := hcc_mem rw hrw;
      ⟨h.1, fun x hx => lt_of_lt_of_le (h.2 x hx) (Nat.add_le_add_left hle1 n)⟩)
  have hle2 : stF.1.length ≤ stT.1.length := extends_length sT.1
  have hle12 : gs.length ≤ stT.1.length := le_trans hle1 hle2
  have sP := gParityLoop_spec hk stF.2 stT.2 (List.finRange m) sT.2.1
    (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
    sF.2.2.2.1 (fun x hx => lt_of_lt_of_le (sF.2.2.2.2.1 x hx) (Nat.add_le_add_left hle2 n))
    sT.2.2.2.1 sT.2.2.2.2.1
  refine ⟨extends_trans sF.1 (extends_trans sT.1 sP.1), sP.2.1, ?_,
    by rw [sP.2.2.2.1, List.length_finRange], sP.2.2.2.2.1, ?_⟩
  · have h1 : stF.1.length ≤ gs.length + 4 * k + 22 * r * k := sF.2.2.1
    have h2 : stT.1.length ≤ stF.1.length + 4 * k + 22 * r * k := sT.2.2.1
    have h3 : (gParityLoop k r m n wFalse stT.1 stF.2 stT.2 (List.finRange m)).1.length ≤
        stT.1.length + (10 * k + 4) * (List.finRange m).length := sP.2.2.1
    rw [List.length_finRange] at h3
    have h44 : 22 * r * k + 22 * r * k = 44 * r * k := by ring
    omega
  · intro u v cr cc A B y t word hword hwf_val hw_val
    set inp := mkInp k r m u v cr cc A B y t
    have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
    have hu_val : (uWires k).map (wireVal gs inp) = List.ofFn (fun i : Fin k => u.val.testBit i.val) := by
      apply List.ext_getElem
      · simp [uWires]
      · intro i h1 h2
        simp only [uWires, List.length_map, List.length_range] at h1
        simp only [uWires, List.map_map, List.getElem_map, List.getElem_range, List.getElem_ofFn]
        rw [wireVal_input hgs hinp (uWires_mem k (by simp [uWires, h1]))]
        exact mkInp_getD_u u v cr cc A B y t h1
    have hv_val : (vWires k).map (wireVal stF.1 inp) = List.ofFn (fun i : Fin k => v.val.testBit i.val) := by
      rw [listVal_extends sF.1 hinp hv_mem]
      apply List.ext_getElem
      · simp [vWires]
      · intro i h1 h2
        simp only [vWires, List.length_map, List.length_range] at h1
        simp only [vWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
          List.getElem_ofFn]
        rw [wireVal_input hgs hinp (vWires_mem k (by simp [vWires, h1]))]
        exact mkInp_getD_v u v cr cc A B y t h1
    have hcr_val : ∀ j : Fin r, (crList.getD j.val []).map (wireVal gs inp) =
        List.ofFn (fun i : Fin k => (cr j).val.testBit i.val) := by
      intro j
      have hrc : crList.getD j.val [] = crWires k j := by
        simp [crList, List.getD_eq_getElem?_getD, j.isLt]
      rw [hrc]
      apply List.ext_getElem
      · simp [crWires]
      · intro i h1 h2
        simp only [crWires, List.length_map, List.length_range] at h1
        simp only [crWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
          List.getElem_ofFn]
        rw [wireVal_input hgs hinp (crWires_mem j (by simp [crWires, h1]))]
        exact mkInp_getD_cr u v cr cc A B y t j h1
    have hcc_val : ∀ j : Fin r, (ccList.getD j.val []).map (wireVal stF.1 inp) =
        List.ofFn (fun i : Fin k => (cc j).val.testBit i.val) := by
      intro j
      have hrc : ccList.getD j.val [] = ccWires k r j := by
        simp [ccList, List.getD_eq_getElem?_getD, j.isLt]
      rw [hrc, listVal_extends sF.1 hinp (fun x hx => lt_of_lt_of_le (ccWires_mem j hx) (Nat.le_add_right n gs.length))]
      apply List.ext_getElem
      · simp [ccWires]
      · intro i h1 h2
        simp only [ccWires, List.length_map, List.length_range] at h1
        simp only [ccWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
          List.getElem_ofFn]
        rw [wireVal_input hgs hinp (ccWires_mem j (by simp [ccWires, h1]))]
        exact mkInp_getD_cc u v cr cc A B y t j h1
    have hsF_val := sF.2.2.2.2.2 inp word u cr hinp hword hw_val hu_val hcr_val
    have hsT_val := sT.2.2.2.2.2 inp word v cc hinp hword
      (by rw [listVal_extends sF.1 hinp hw, hw_val]) hv_val hcc_val
    have hsP_val := sP.2.2.2.2.2 u v cr cc A B y t word
      (by rw [wireVal_extends (extends_trans sF.1 sT.1) hinp hwf, hwf_val])
      (by rw [listVal_extends sT.1 hinp sF.2.2.2.2.1, hsF_val]) hsT_val
    have hof : (List.finRange m).map (fFn k r m u.val v.val cr cc A B word) =
        List.ofFn (fFn k r m u.val v.val cr cc A B word) := by
      apply List.ext_getElem <;> simp
    rw [hsP_val, hof]

lemma list_set_map_ofFn {α β : Type*} {k : ℕ} (zs : List α) (f : α → β) (g : Fin k → β)
    (hlen : zs.length = k) (hm : zs.map f = List.ofFn g) (i : Fin k) (v : α) :
    (zs.set i.val v).map f = List.ofFn (fun p : Fin k => if p = i then f v else g p) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro idx h1 h2
    simp only [List.length_map, List.length_set, hlen] at h1
    simp only [List.getElem_map, List.getElem_set, List.getElem_ofFn]
    by_cases heq : i.val = idx
    · subst heq
      simp
    · have hne : (⟨idx, h1⟩ : Fin k) ≠ i := fun h => heq (congrArg Fin.val h).symm
      simp only [heq, ↓reduceIte, hne]
      have := congrArg (fun l : List β => l[idx]?) hm
      simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : idx < zs.length),
        List.getElem?_ofFn, h1, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
      exact this

lemma reconstructStep_congr_free {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f1 f2 : Fin k → Bool)
    (hfree : ∀ i : Fin k, piv i = false → f1 i = f2 i) (s : ℕ) (z : Fin k → Bool) :
    reconstructStep hk u v cr cc A B y cut piv wit f1 s z =
      reconstructStep hk u v cr cc A B y cut piv wit f2 s z := by
  unfold reconstructStep
  split_ifs with hs
  · ext p
    set i : Fin k := ⟨k - 1 - s, by omega⟩
    by_cases hp : p = i
    · rw [hp]
      simp only [↓reduceIte]
      cases hpi : piv i <;> simp [hpi, hfree i]
    · simp [hp]
  · rfl

lemma reconstructZ_congr_free {k r m : ℕ} (hk : 0 < k) (u v : ℕ) (cr cc : Fin r → Fin (2 ^ k))
    (A B : Fin m → Fin (2 ^ k)) (y : Fin m → Bool) (cut : Fin k)
    (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f1 f2 : Fin k → Bool)
    (hfree : ∀ i : Fin k, piv i = false → f1 i = f2 i) :
    reconstructZ hk u v cr cc A B y cut piv wit f1 =
      reconstructZ hk u v cr cc A B y cut piv wit f2 := by
  unfold reconstructZ
  induction (List.range k) using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs s ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, reconstructStep_congr_free hk u v cr cc A B y cut piv wit f1 f2 hfree]

def gReconstructStep (k r m n wFalse : ℕ) (gs : List Gate)
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY fFreeW zW : List ℕ) (s : ℕ) :
    List Gate × List ℕ :=
  if _hs : s < k then
    let i := k - 1 - s
    let w0 := gZToW k n wFalse gs fcW zW
    let fw0 := gFFn k r m n wFalse w0.1 w0.2
    let dwit := gDot n wFalse fw0.1 (witW.getD i []) fw0.2
    let zpiv := gXor n dwit.1 (witDotY.getD i wFalse) dwit.2
    let znew := gMux n zpiv.1 (pivW.getD i wFalse) zpiv.2 (fFreeW.getD i wFalse)
    (znew.1, zW.set i znew.2)
  else (gs, zW)

lemma gReconstructStep_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse : ℕ}
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY fFreeW zW : List ℕ) (s : ℕ)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfclen : fcW.length = k)
    (hfc : ∀ w ∈ fcW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hpivlen : pivW.length = k)
    (hpiv : ∀ w ∈ pivW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwitlen : witW.length = k)
    (hwit : ∀ rw ∈ witW, rw.length = m ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwdy_len : witDotY.length = k)
    (hwdy : ∀ w ∈ witDotY, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hff_len : fFreeW.length = k)
    (hff : ∀ w ∈ fFreeW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hz_len : zW.length = k)
    (hz : ∀ w ∈ zW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gReconstructStep k r m n wFalse gs fcW pivW witW witDotY fFreeW zW s
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + 5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8 ∧
      res.2.length = k ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (cutS : Fin k)
        (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free z0 : Fin k → Bool),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        fcW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        pivW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn piv →
        (∀ i : Fin k, (witW.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (wit i)) →
        witDotY.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun i : Fin k => dotBool (wit i) y) →
        fFreeW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn f_free →
        zW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn z0 →
        res.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (reconstructStep hk u.val v.val cr cc A B y cutS piv wit f_free s z0) := by
  intro n
  dsimp only [gReconstructStep]
  by_cases hs : s < k
  · simp only [hs, ↓reduceDIte]
    set iVal := k - 1 - s
    have hi_lt : iVal < k := by omega
    let i : Fin k := ⟨iVal, hi_lt⟩
    set w0 := gZToW k n wFalse gs fcW zW
    set fw0 := gFFn k r m n wFalse w0.1 w0.2
    set dwit := gDot n wFalse fw0.1 (witW.getD iVal []) fw0.2
    set zpiv := gXor n dwit.1 (witDotY.getD iVal wFalse) dwit.2
    set znew := gMux n zpiv.1 (pivW.getD iVal wFalse) zpiv.2 (fFreeW.getD iVal wFalse)
    have sw0 := gZToW_spec hk fcW zW hgs hwf hfc hz_len hz
    have hle1 : gs.length ≤ w0.1.length := extends_length sw0.1
    have sfw0 := gFFn_spec hk w0.2 sw0.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      sw0.2.2.2.1 sw0.2.2.2.2.1
    have hle2 : w0.1.length ≤ fw0.1.length := extends_length sfw0.1
    have hle12 : gs.length ≤ fw0.1.length := le_trans hle1 hle2
    have hwit_i := hwit _ (getD_mem_of_lt witW (by rw [hwitlen]; exact hi_lt))
    have hwi_mem : ∀ w ∈ witW.getD iVal [], w < n + fw0.1.length :=
      fun w hw => lt_of_lt_of_le (hwit_i.2 w hw) (Nat.add_le_add_left hle12 n)
    have sdw := gDot_spec (witW.getD iVal []) fw0.2 sfw0.2.1
      (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n)) hwi_mem sfw0.2.2.2.2.1
    have hle3 : fw0.1.length ≤ dwit.1.length := extends_length sdw.1
    have h13 : Extends gs dwit.1 := extends_trans sw0.1 (extends_trans sfw0.1 sdw.1)
    have hle13 : gs.length ≤ dwit.1.length := extends_length h13
    have hwdy_i : witDotY.getD iVal wFalse < n + gs.length := by
      have hlt : iVal < witDotY.length := by rw [hwdy_len]; exact hi_lt
      have hrc : witDotY.getD iVal wFalse = witDotY[iVal]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      rw [hrc]; exact hwdy _ (List.getElem_mem hlt)
    have szp := gXor_spec sdw.2.1 (lt_of_lt_of_le hwdy_i (Nat.add_le_add_left hle13 n)) sdw.2.2.2.1
    have hle4 : dwit.1.length ≤ zpiv.1.length := extends_length szp.1
    have h14 : Extends gs zpiv.1 := extends_trans h13 szp.1
    have hle14 : gs.length ≤ zpiv.1.length := extends_length h14
    have hpiv_i : pivW.getD iVal wFalse < n + gs.length := by
      have hlt : iVal < pivW.length := by rw [hpivlen]; exact hi_lt
      have hrc : pivW.getD iVal wFalse = pivW[iVal]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      rw [hrc]; exact hpiv _ (List.getElem_mem hlt)
    have hff_i : fFreeW.getD iVal wFalse < n + gs.length := by
      have hlt : iVal < fFreeW.length := by rw [hff_len]; exact hi_lt
      have hrc : fFreeW.getD iVal wFalse = fFreeW[iVal]'hlt := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      rw [hrc]; exact hff _ (List.getElem_mem hlt)
    have szn := gMux_spec szp.2.1 (lt_of_lt_of_le hpiv_i (Nat.add_le_add_left hle14 n))
      szp.2.2.2.1 (lt_of_lt_of_le hff_i (Nat.add_le_add_left hle14 n))
    have hle5 : zpiv.1.length ≤ znew.1.length := extends_length szn.1
    have h15 : Extends gs znew.1 := extends_trans h14 szn.1
    have hle15 : gs.length ≤ znew.1.length := extends_length h15
    refine ⟨h15, szn.2.1, ?_, by simp [hz_len], ?_, ?_⟩
    · have h1 : w0.1.length ≤ gs.length + 5 * fcW.length * k := sw0.2.2.1
      have h2 : fw0.1.length ≤ w0.1.length + 8 * k + 44 * r * k + (10 * k + 4) * m := sfw0.2.2.1
      have h3 : dwit.1.length ≤ fw0.1.length + 5 * (witW.getD iVal []).length := sdw.2.2.1
      have h4 : zpiv.1.length = dwit.1.length + 4 := szp.2.2.1
      have h5 : znew.1.length = zpiv.1.length + 4 := szn.2.2.1
      rw [hfclen] at h1
      rw [hwit_i.1] at h3
      omega
    · intro w hw
      obtain ⟨idx, hidx, rfl⟩ := List.mem_iff_getElem.mp hw
      simp only [List.length_set] at hidx
      rw [List.getElem_set]
      split_ifs
      · exact szn.2.2.2.1
      · exact lt_of_lt_of_le (hz _ (List.getElem_mem hidx)) (Nat.add_le_add_left hle15 n)
    · intro u v cr cc A B y t cutS piv wit f_free z0 hwf_val hfc_val hpiv_val hwit_val hwdy_val hff_val hz_val
      set inp := mkInp k r m u v cr cc A B y t
      have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
      have hw0_val := sw0.2.2.2.2.2 inp cutS z0 hinp hwf_val hfc_val hz_val
      have hfw0_val := sfw0.2.2.2.2.2 u v cr cc A B y t (zToW hk cutS z0)
        (zToW_lt hk cutS z0) (by rw [wireVal_extends sw0.1 hinp hwf, hwf_val]) hw0_val
      have hdw_val : wireVal dwit.1 inp dwit.2 =
          dotBool (wit i) (fFn k r m u.val v.val cr cc A B (zToW hk cutS z0)) := by
        refine sdw.2.2.2.2 inp m (wit i) _ hinp
          (by rw [wireVal_extends (extends_trans sw0.1 sfw0.1) hinp hwf, hwf_val])
          (by rw [listVal_extends (extends_trans sw0.1 sfw0.1) hinp hwit_i.2]; exact hwit_val i)
          hfw0_val
      have hwdy_val_i : wireVal dwit.1 inp (witDotY.getD iVal wFalse) = dotBool (wit i) y := by
        rw [wireVal_extends h13 hinp hwdy_i]
        have hlt : iVal < witDotY.length := by rw [hwdy_len]; exact hi_lt
        have hrc : witDotY.getD iVal wFalse = witDotY[iVal]'hlt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hrc]
        have := congrArg (fun l : List Bool => l[iVal]?) hwdy_val
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
          hi_lt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa [i] using this
      have hzp_val : wireVal zpiv.1 inp zpiv.2 =
          xor (dotBool (wit i) y) (dotBool (wit i) (fFn k r m u.val v.val cr cc A B (zToW hk cutS z0))) := by
        rw [szp.2.2.2.2 inp hinp, hwdy_val_i, hdw_val]
      have hpiv_val_i : wireVal zpiv.1 inp (pivW.getD iVal wFalse) = piv i := by
        rw [wireVal_extends h14 hinp hpiv_i]
        have hlt : iVal < pivW.length := by rw [hpivlen]; exact hi_lt
        have hrc : pivW.getD iVal wFalse = pivW[iVal]'hlt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hrc]
        have := congrArg (fun l : List Bool => l[iVal]?) hpiv_val
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
          hi_lt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa [i] using this
      have hff_val_i : wireVal zpiv.1 inp (fFreeW.getD iVal wFalse) = f_free i := by
        rw [wireVal_extends h14 hinp hff_i]
        have hlt : iVal < fFreeW.length := by rw [hff_len]; exact hi_lt
        have hrc : fFreeW.getD iVal wFalse = fFreeW[iVal]'hlt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
        rw [hrc]
        have := congrArg (fun l : List Bool => l[iVal]?) hff_val
        simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, List.getElem?_ofFn,
          hi_lt, ↓reduceDIte, Option.map_some, Option.some.injEq] at this
        simpa [i] using this
      have hzn_val : wireVal znew.1 inp znew.2 =
          if piv i then xor (dotBool (wit i) y)
            (dotBool (wit i) (fFn k r m u.val v.val cr cc A B (zToW hk cutS z0)))
          else f_free i := by
        rw [szn.2.2.2.2 inp hinp, hpiv_val_i, hzp_val, hff_val_i]
      have hz_ext : zW.map (wireVal znew.1 inp) = List.ofFn z0 := by
        rw [listVal_extends h15 hinp hz, hz_val]
      rw [list_set_map_ofFn zW (wireVal znew.1 inp) z0 hz_len hz_ext i znew.2, hzn_val]
      congr 1
      ext p
      unfold reconstructStep
      simp only [hs, ↓reduceDIte]
      rfl
  · simp only [hs, ↓reduceDIte]
    refine ⟨extends_refl gs, hgs, by omega, hz_len, hz, ?_⟩
    intro u v cr cc A B y t cutS piv wit f_free z0 _ _ _ _ _ _ hz_val
    rw [hz_val]
    congr 1
    ext p
    unfold reconstructStep
    simp [hs]

def gReconstructZLoop (k r m n wFalse : ℕ) (gs : List Gate)
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY fFreeW zW : List ℕ) :
    List ℕ → List Gate × List ℕ
  | [] => (gs, zW)
  | s :: rest =>
    let st := gReconstructStep k r m n wFalse gs fcW pivW witW witDotY fFreeW zW s
    gReconstructZLoop k r m n wFalse st.1 fcW pivW witW witDotY fFreeW st.2 rest

lemma gReconstructZLoop_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse : ℕ}
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY fFreeW zW : List ℕ) (ss : List ℕ)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfclen : fcW.length = k)
    (hfc : ∀ w ∈ fcW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hpivlen : pivW.length = k)
    (hpiv : ∀ w ∈ pivW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwitlen : witW.length = k)
    (hwit : ∀ rw ∈ witW, rw.length = m ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwdy_len : witDotY.length = k)
    (hwdy : ∀ w ∈ witDotY, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hff_len : fFreeW.length = k)
    (hff : ∀ w ∈ fFreeW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hz_len : zW.length = k)
    (hz : ∀ w ∈ zW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gReconstructZLoop k r m n wFalse gs fcW pivW witW witDotY fFreeW zW ss
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * ss.length ∧
      res.2.length = k ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (cutS : Fin k)
        (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free z0 : Fin k → Bool),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        fcW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        pivW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn piv →
        (∀ i : Fin k, (witW.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (wit i)) →
        witDotY.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun i : Fin k => dotBool (wit i) y) →
        fFreeW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn f_free →
        zW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn z0 →
        res.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (ss.foldl (fun z s => reconstructStep hk u.val v.val cr cc A B y cutS piv wit f_free s z) z0) := by
  intro n
  induction ss generalizing gs zW with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gReconstructZLoop], hz_len, hz, ?_⟩
    intro u v cr cc A B y t cutS piv wit f_free z0 _ _ _ _ _ _ hz_val
    exact hz_val
  | cons s rest ih =>
    dsimp only [gReconstructZLoop]
    set st := gReconstructStep k r m n wFalse gs fcW pivW witW witDotY fFreeW zW s
    have sst := gReconstructStep_spec hk fcW pivW witW witDotY fFreeW zW s hgs hwf
      hfclen hfc hpivlen hpiv hwitlen hwit hwdy_len hwdy hff_len hff hz_len hz
    have hle1 : gs.length ≤ st.1.length := extends_length sst.1
    have ih' := ih st.2 sst.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hfc w hw) (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hpiv w hw) (Nat.add_le_add_left hle1 n))
      (fun rw hrw => have h := hwit rw hrw; ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
      (fun w hw => lt_of_lt_of_le (hwdy w hw) (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hff w hw) (Nat.add_le_add_left hle1 n))
      sst.2.2.2.1 sst.2.2.2.2.1
    refine ⟨extends_trans sst.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ih'.2.2.2.2.1, ?_⟩
    · have h1 := sst.2.2.1; have h2 := ih'.2.2.1
      change st.1.length ≤ _ at h1
      change (gReconstructZLoop k r m n wFalse st.1 fcW pivW witW witDotY fFreeW st.2 rest).1.length ≤ _ at h2
      simp only [List.length_cons]
      nlinarith
    · intro u v cr cc A B y t cutS piv wit f_free z0 hwf_val hfc_val hpiv_val hwit_val hwdy_val hff_val hz_val
      set inp := mkInp k r m u v cr cc A B y t
      have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
      have hst_val := sst.2.2.2.2.2 u v cr cc A B y t cutS piv wit f_free z0
        hwf_val hfc_val hpiv_val hwit_val hwdy_val hff_val hz_val
      simp only [List.foldl_cons]
      refine ih'.2.2.2.2.2 u v cr cc A B y t cutS piv wit f_free _
        (by rw [wireVal_extends sst.1 hinp hwf, hwf_val])
        (by rw [listVal_extends sst.1 hinp hfc, hfc_val])
        (by rw [listVal_extends sst.1 hinp hpiv, hpiv_val])
        (fun i => by
          have hmem := (hwit _ (getD_mem_of_lt witW (by rw [hwitlen]; exact i.isLt))).2
          rw [listVal_extends sst.1 hinp hmem, hwit_val i])
        (by rw [listVal_extends sst.1 hinp hwdy, hwdy_val])
        (by rw [listVal_extends sst.1 hinp hff, hff_val])
        hst_val

def gReconstructW (k r m n wFalse : ℕ) (gs : List Gate)
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY fFreeW : List ℕ) : List Gate × List ℕ :=
  let zl := gReconstructZLoop k r m n wFalse gs fcW pivW witW witDotY fFreeW
    (List.replicate k wFalse) (List.range k)
  gZToW k n wFalse zl.1 fcW zl.2

lemma gReconstructW_spec {k r m : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse : ℕ}
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY fFreeW : List ℕ)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfclen : fcW.length = k)
    (hfc : ∀ w ∈ fcW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hpivlen : pivW.length = k)
    (hpiv : ∀ w ∈ pivW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwitlen : witW.length = k)
    (hwit : ∀ rw ∈ witW, rw.length = m ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwdy_len : witDotY.length = k)
    (hwdy : ∀ w ∈ witDotY, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hff_len : fFreeW.length = k)
    (hff : ∀ w ∈ fFreeW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gReconstructW k r m n wFalse gs fcW pivW witW witDotY fFreeW
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length +
        (5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k ∧
      res.2.length = k ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (cutS : Fin k)
        (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool) (f_free : Fin k → Bool),
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        fcW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        pivW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn piv →
        (∀ i : Fin k, (witW.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (wit i)) →
        witDotY.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun i : Fin k => dotBool (wit i) y) →
        fFreeW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn f_free →
        res.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun b : Fin k =>
            (zToW hk cutS (reconstructZ hk u.val v.val cr cc A B y cutS piv wit f_free)).testBit b.val) := by
  intro n
  dsimp only [gReconstructW]
  set zl := gReconstructZLoop k r m n wFalse gs fcW pivW witW witDotY fFreeW
    (List.replicate k wFalse) (List.range k)
  have hrep_len : (List.replicate k wFalse).length = k := List.length_replicate
  have hrep_mem : ∀ w ∈ List.replicate k wFalse, w < n + gs.length := by
    intro w hw; rw [List.mem_replicate] at hw; rcases hw with ⟨_, rfl⟩; exact hwf
  have szl := gReconstructZLoop_spec hk fcW pivW witW witDotY fFreeW (List.replicate k wFalse)
    (List.range k) hgs hwf hfclen hfc hpivlen hpiv hwitlen hwit hwdy_len hwdy hff_len hff
    hrep_len hrep_mem
  have hle1 : gs.length ≤ zl.1.length := extends_length szl.1
  have sz := gZToW_spec hk fcW zl.2 szl.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
    (fun w hw => lt_of_lt_of_le (hfc w hw) (Nat.add_le_add_left hle1 n)) szl.2.2.2.1 szl.2.2.2.2.1
  refine ⟨extends_trans szl.1 sz.1, sz.2.1, ?_, sz.2.2.2.1, sz.2.2.2.2.1, ?_⟩
  · have h1 := szl.2.2.1; have h2 := sz.2.2.1
    change zl.1.length ≤ _ at h1
    change (gZToW k n wFalse zl.1 fcW zl.2).1.length ≤ zl.1.length + 5 * fcW.length * k at h2
    rw [List.length_range] at h1
    rw [hfclen] at h2
    omega
  · intro u v cr cc A B y t cutS piv wit f_free hwf_val hfc_val hpiv_val hwit_val hwdy_val hff_val
    set inp := mkInp k r m u v cr cc A B y t
    have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
    have hz0_val : (List.replicate k wFalse).map (wireVal gs inp) = List.ofFn (fun _ : Fin k => false) := by
      apply List.ext_getElem <;> simp [hwf_val]
    have hzl_val := szl.2.2.2.2.2 u v cr cc A B y t cutS piv wit f_free (fun _ => false)
      hwf_val hfc_val hpiv_val hwit_val hwdy_val hff_val hz0_val
    exact sz.2.2.2.2.2 inp cutS (reconstructZ hk u.val v.val cr cc A B y cutS piv wit f_free)
      hinp (by rw [wireVal_extends szl.1 hinp hwf, hwf_val])
      (by rw [listVal_extends szl.1 hinp hfc, hfc_val]) hzl_val

def bitsToFun (m idx : ℕ) : Fin m → Bool := fun d => idx.testBit d.val

lemma bitsToFun_bij (m : ℕ) : Function.Bijective (fun idx : Fin (2 ^ m) => bitsToFun m idx.val) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
  intro i1 i2 h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < m
  · exact congrFun h ⟨b, hb⟩
  · have hk : m ≤ b := by omega
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i1.isLt (Nat.pow_le_pow_right (by decide) hk)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le i2.isLt (Nat.pow_le_pow_right (by decide) hk))]

lemma card_filter_eq_range_filter {m : ℕ} (P : (Fin m → Bool) → Bool) :
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun a => P a = true)).card =
      ((List.range (2 ^ m)).filter (fun idx => P (bitsToFun m idx))).length := by
  have h1 : ((Finset.univ : Finset (Fin m → Bool)).filter (fun a => P a = true)).card =
      ((Finset.univ : Finset (Fin (2 ^ m))).filter (fun idx => P (bitsToFun m idx.val) = true)).card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    refine Fintype.card_congr ?_
    let e := Equiv.ofBijective _ (bitsToFun_bij m)
    refine Equiv.subtypeEquiv e.symm ?_
    intro a
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [show bitsToFun m (e.symm a).val = a from e.apply_symm_apply a]
  rw [h1, ← finRange_filter_length_eq_card]
  have hr : List.range (2 ^ m) = (List.finRange (2 ^ m)).map Fin.val := by
    apply List.ext_getElem <;> simp
  rw [hr, List.filter_map, List.length_map]
  rfl

def gEvalOneA (k r m q n wFalse wTrue : ℕ) (gs : List Gate)
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY : List ℕ) (freeOH : List (List ℕ))
    (hitsAcc : List ℕ) (idx : ℕ) : List Gate × List ℕ :=
  let a := bitsToFun (k - q) idx
  let ff := gFreeAssign k q n wFalse gs a freeOH
  let rw := gReconstructW k r m n wFalse ff.1 fcW pivW witW witDotY ff.2
  let fval := gFFn k r m n wFalse rw.1 rw.2
  let eq := gVecEq n wTrue fval.1 fval.2 (yWires k r m)
  gIncAux n eq.1 eq.2 hitsAcc

lemma gEvalOneA_spec {k r m q : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse wTrue : ℕ}
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY : List ℕ) (freeOH : List (List ℕ))
    (hitsAcc : List ℕ) (idx : ℕ)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwt : wTrue < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfclen : fcW.length = k)
    (hfc : ∀ w ∈ fcW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hpivlen : pivW.length = k)
    (hpiv : ∀ w ∈ pivW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwitlen : witW.length = k)
    (hwit : ∀ rw ∈ witW, rw.length = m ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwdy_len : witDotY.length = k)
    (hwdy : ∀ w ∈ witDotY, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfohlen : freeOH.length = k)
    (hfoh : ∀ rw ∈ freeOH, rw.length = k - q ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hacc_len : hitsAcc.length = k + 1)
    (hacc : ∀ w ∈ hitsAcc, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gEvalOneA k r m q n wFalse wTrue gs fcW pivW witW witDotY freeOH hitsAcc idx
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + (k - q) * k +
        ((5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k) +
        (8 * k + 44 * r * k + (10 * k + 4) * m) + 6 * m + 5 * (k + 1) ∧
      res.2.length = k + 1 ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (cutS : Fin k)
        (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool),
        ((List.finRange k).filter piv).length = q →
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        wireVal gs (mkInp k r m u v cr cc A B y t) wTrue = true →
        fcW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        pivW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn piv →
        (∀ i : Fin k, (witW.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (wit i)) →
        witDotY.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun i : Fin k => dotBool (wit i) y) →
        (∀ i : Fin k, (freeOH.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun d : Fin (k - q) => !piv i && decide (freeCountBefore piv i = d.val))) →
        bitsVal (res.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t))) =
          (bitsVal (hitsAcc.map (wireVal gs (mkInp k r m u v cr cc A B y t))) +
            (decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
              (reconstructW hk u.val v.val cr cc A B y cutS piv wit (bitsToFun (k - q) idx)).val j = y j)).toNat) %
            2 ^ (k + 1) := by
  intro n
  dsimp only [gEvalOneA]
  set a := bitsToFun (k - q) idx
  set ff := gFreeAssign k q n wFalse gs a freeOH
  set rw := gReconstructW k r m n wFalse ff.1 fcW pivW witW witDotY ff.2
  set fval := gFFn k r m n wFalse rw.1 rw.2
  set eq := gVecEq n wTrue fval.1 fval.2 (yWires k r m)
  have sff := gFreeAssign_spec a freeOH hgs hwf hfoh
  have hle1 : gs.length ≤ ff.1.length := extends_length sff.1
  have hff_len : ff.2.length = k := by rw [sff.2.2.2.1, hfohlen]
  have srw := gReconstructW_spec hk fcW pivW witW witDotY ff.2 sff.2.1
    (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
    hfclen (fun w hw => lt_of_lt_of_le (hfc w hw) (Nat.add_le_add_left hle1 n))
    hpivlen (fun w hw => lt_of_lt_of_le (hpiv w hw) (Nat.add_le_add_left hle1 n))
    hwitlen (fun r' hr' => have h := hwit r' hr'; ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
    hwdy_len (fun w hw => lt_of_lt_of_le (hwdy w hw) (Nat.add_le_add_left hle1 n))
    hff_len sff.2.2.2.2.1
  have hle2 : ff.1.length ≤ rw.1.length := extends_length srw.1
  have hle12 : gs.length ≤ rw.1.length := le_trans hle1 hle2
  have sfval := gFFn_spec hk rw.2 srw.2.1 (lt_of_lt_of_le hwf (Nat.add_le_add_left hle12 n))
    srw.2.2.2.1 srw.2.2.2.2.1
  have hle3 : rw.1.length ≤ fval.1.length := extends_length sfval.1
  have hle13 : gs.length ≤ fval.1.length := le_trans hle12 hle3
  have hy_mem : ∀ w ∈ yWires k r m, w < n + fval.1.length :=
    fun w hw => lt_of_lt_of_le (yWires_mem k r m hw) (Nat.le_add_right n fval.1.length)
  have seq := gVecEq_spec fval.2 (yWires k r m) sfval.2.1
    (lt_of_lt_of_le hwt (Nat.add_le_add_left hle13 n)) sfval.2.2.2.2.1 hy_mem
  have hle4 : fval.1.length ≤ eq.1.length := extends_length seq.1
  have hle14 : gs.length ≤ eq.1.length := le_trans hle13 hle4
  have sinc := gIncAux_spec hitsAcc seq.2.1 seq.2.2.2.1
    (fun w hw => lt_of_lt_of_le (hacc w hw) (Nat.add_le_add_left hle14 n))
  have hext_all : Extends gs (gIncAux n eq.1 eq.2 hitsAcc).1 :=
    extends_trans sff.1 (extends_trans srw.1 (extends_trans sfval.1 (extends_trans seq.1 sinc.1)))
  refine ⟨hext_all, sinc.2.1, ?_, by rw [sinc.2.2.2.1, hacc_len], sinc.2.2.2.2.1, ?_⟩
  · have h1 := sff.2.2.1
    have h2 := srw.2.2.1
    have h3 := sfval.2.2.1
    have h4 := seq.2.2.1
    have h5 := sinc.2.2.1
    change ff.1.length ≤ gs.length + (k - q) * freeOH.length at h1
    change rw.1.length ≤ _ at h2
    change fval.1.length ≤ _ at h3
    change eq.1.length ≤ fval.1.length + 6 * fval.2.length at h4
    change (gIncAux n eq.1 eq.2 hitsAcc).1.length = eq.1.length + 5 * hitsAcc.length at h5
    rw [hfohlen] at h1
    rw [sfval.2.2.2.1] at h4
    rw [hacc_len] at h5
    linarith
  · intro u v cr cc A B y t cutS piv wit hpiv_card hwf_val hwt_val hfc_val hpiv_val hwit_val hwdy_val hfoh_val
    set inp := mkInp k r m u v cr cc A B y t
    have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
    let f_free_eff : Fin k → Bool := fun i => if piv i then false else freeAssign k q piv a i
    let F : ℕ → Fin (k - q) → Bool := fun idx d =>
      if h : idx < k then !piv ⟨idx, h⟩ && decide (freeCountBefore piv ⟨idx, h⟩ = d.val) else false
    have hff_val : ff.2.map (wireVal ff.1 inp) = List.ofFn f_free_eff := by
      have hsff_map := sff.2.2.2.2.2 inp F hinp hwf_val (fun idx hi => by
        have hrc : freeOH[idx]'hi = freeOH.getD idx [] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        rw [hrc]
        have hi' : idx < k := by rw [← hfohlen]; exact hi
        convert hfoh_val ⟨idx, hi'⟩ using 2
        ext d
        simp [F, hi'])
      rw [hsff_map, hfohlen]
      apply List.ext_getElem
      · simp
      · intro idx h1 h2
        simp only [List.length_map, List.length_range] at h1
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, f_free_eff, F, h1, ↓reduceDIte]
        cases hpi : piv ⟨idx, h1⟩ with
        | true => simp [any_filter_piv_true piv a ⟨idx, h1⟩ hpi]
        | false =>
          have hfree := any_filter_oneHot_free piv hpiv_card a ⟨idx, h1⟩ hpi
          simp only [hpi] at hfree
          simpa using hfree
    have hrw_val : rw.2.map (wireVal rw.1 inp) =
        List.ofFn (fun b : Fin k =>
          (zToW hk cutS (reconstructZ hk u.val v.val cr cc A B y cutS piv wit f_free_eff)).testBit b.val) := by
      refine srw.2.2.2.2.2 u v cr cc A B y t cutS piv wit f_free_eff
        (by rw [wireVal_extends sff.1 hinp hwf, hwf_val])
        (by rw [listVal_extends sff.1 hinp hfc, hfc_val])
        (by rw [listVal_extends sff.1 hinp hpiv, hpiv_val])
        (fun i => by
          have hmem := (hwit _ (getD_mem_of_lt witW (by rw [hwitlen]; exact i.isLt))).2
          rw [listVal_extends sff.1 hinp hmem, hwit_val i])
        (by rw [listVal_extends sff.1 hinp hwdy, hwdy_val])
        hff_val
    have hcongr : reconstructZ hk u.val v.val cr cc A B y cutS piv wit f_free_eff =
        reconstructZ hk u.val v.val cr cc A B y cutS piv wit (freeAssign k q piv a) := by
      refine reconstructZ_congr_free hk u.val v.val cr cc A B y cutS piv wit f_free_eff _ (fun i hi => ?_)
      simp [f_free_eff, hi]
    rw [hcongr] at hrw_val
    have hrec_lt : (reconstructW hk u.val v.val cr cc A B y cutS piv wit a).val < 2 ^ k :=
      (reconstructW hk u.val v.val cr cc A B y cutS piv wit a).isLt
    have hfval_val : fval.2.map (wireVal fval.1 inp) =
        List.ofFn (fFn k r m u.val v.val cr cc A B (reconstructW hk u.val v.val cr cc A B y cutS piv wit a).val) := by
      refine sfval.2.2.2.2.2 u v cr cc A B y t
        (reconstructW hk u.val v.val cr cc A B y cutS piv wit a).val hrec_lt
        (by rw [wireVal_extends (extends_trans sff.1 srw.1) hinp hwf, hwf_val])
        hrw_val
    have hy_val : (yWires k r m).map (wireVal fval.1 inp) = List.ofFn y := by
      have h13_ext : Extends gs fval.1 := extends_trans sff.1 (extends_trans srw.1 sfval.1)
      have hy_mem0 : ∀ w ∈ yWires k r m, w < n + gs.length :=
        fun w hw => lt_of_lt_of_le (yWires_mem k r m hw) (Nat.le_add_right n gs.length)
      rw [listVal_extends h13_ext hinp hy_mem0]
      apply List.ext_getElem
      · simp [yWires]
      · intro j h1 h2
        simp only [yWires, List.length_map, List.length_finRange] at h1
        simp only [yWires, List.map_map, List.getElem_map, List.getElem_finRange, Fin.val_cast,
          Function.comp_apply, List.getElem_ofFn]
        rw [wireVal_input hgs hinp (yWires_mem k r m (List.mem_map.mpr ⟨⟨j, h1⟩, List.mem_finRange _, rfl⟩))]
        exact mkInp_getD_y u v cr cc A B y t ⟨j, h1⟩
    have h13_ext : Extends gs fval.1 := extends_trans sff.1 (extends_trans srw.1 sfval.1)
    have h14_ext : Extends gs eq.1 := extends_trans h13_ext seq.1
    have heq_val : wireVal eq.1 inp eq.2 =
        decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
          (reconstructW hk u.val v.val cr cc A B y cutS piv wit a).val j = y j) := by
      exact seq.2.2.2.2 inp m _ y hinp
        (by rw [wireVal_extends h13_ext hinp hwt, hwt_val]) hfval_val hy_val
    rw [sinc.2.2.2.2.2 inp hinp, hacc_len, heq_val, listVal_extends h14_ext hinp hacc]

def gEvalHitsLoop (k r m q n wFalse wTrue : ℕ) (gs : List Gate)
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY : List ℕ) (freeOH : List (List ℕ))
    (hitsAcc : List ℕ) : List ℕ → List Gate × List ℕ
  | [] => (gs, hitsAcc)
  | idx :: rest =>
    let s := gEvalOneA k r m q n wFalse wTrue gs fcW pivW witW witDotY freeOH hitsAcc idx
    gEvalHitsLoop k r m q n wFalse wTrue s.1 fcW pivW witW witDotY freeOH s.2 rest

lemma gEvalHitsLoop_spec {k r m q : ℕ} (hk : 0 < k) {gs : List Gate} {wFalse wTrue : ℕ}
    (fcW pivW : List ℕ) (witW : List (List ℕ)) (witDotY : List ℕ) (freeOH : List (List ℕ))
    (hitsAcc : List ℕ) (idxs : List ℕ)
    (hgs : GoodGates (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) gs)
    (hwf : wFalse < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwt : wTrue < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfclen : fcW.length = k)
    (hfc : ∀ w ∈ fcW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hpivlen : pivW.length = k)
    (hpiv : ∀ w ∈ pivW, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwitlen : witW.length = k)
    (hwit : ∀ rw ∈ witW, rw.length = m ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hwdy_len : witDotY.length = k)
    (hwdy : ∀ w ∈ witDotY, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hfohlen : freeOH.length = k)
    (hfoh : ∀ rw ∈ freeOH, rw.length = k - q ∧ ∀ w ∈ rw, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length)
    (hacc_len : hitsAcc.length = k + 1)
    (hacc : ∀ w ∈ hitsAcc, w < (2 * k + 2 * r * k + 2 * m * k + m + (k + 1)) + gs.length) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let res := gEvalHitsLoop k r m q n wFalse wTrue gs fcW pivW witW witDotY freeOH hitsAcc idxs
    Extends gs res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ gs.length + ((k - q) * k +
        ((5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k) +
        (8 * k + 44 * r * k + (10 * k + 4) * m) + 6 * m + 5 * (k + 1)) * idxs.length ∧
      res.2.length = k + 1 ∧ (∀ w ∈ res.2, w < n + res.1.length) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))) (cutS : Fin k)
        (piv : Fin k → Bool) (wit : Fin k → Fin m → Bool),
        ((List.finRange k).filter piv).length = q →
        wireVal gs (mkInp k r m u v cr cc A B y t) wFalse = false →
        wireVal gs (mkInp k r m u v cr cc A B y t) wTrue = true →
        fcW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun cut : Fin k => decide (cut = cutS)) →
        pivW.map (wireVal gs (mkInp k r m u v cr cc A B y t)) = List.ofFn piv →
        (∀ i : Fin k, (witW.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (wit i)) →
        witDotY.map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun i : Fin k => dotBool (wit i) y) →
        (∀ i : Fin k, (freeOH.getD i.val []).map (wireVal gs (mkInp k r m u v cr cc A B y t)) =
          List.ofFn (fun d : Fin (k - q) => !piv i && decide (freeCountBefore piv i = d.val))) →
        bitsVal (hitsAcc.map (wireVal gs (mkInp k r m u v cr cc A B y t))) + idxs.length < 2 ^ (k + 1) →
        bitsVal (res.2.map (wireVal res.1 (mkInp k r m u v cr cc A B y t))) =
          bitsVal (hitsAcc.map (wireVal gs (mkInp k r m u v cr cc A B y t))) +
            (idxs.filter (fun idx => decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
              (reconstructW hk u.val v.val cr cc A B y cutS piv wit (bitsToFun (k - q) idx)).val j = y j))).length := by
  intro n
  induction idxs generalizing gs hitsAcc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [gEvalHitsLoop], hacc_len, hacc, ?_⟩
    intro u v cr cc A B y t cutS piv wit _ _ _ _ _ _ _ _ _
    simp [gEvalHitsLoop]
  | cons idx rest ih =>
    dsimp only [gEvalHitsLoop]
    set s := gEvalOneA k r m q n wFalse wTrue gs fcW pivW witW witDotY freeOH hitsAcc idx
    have ss := gEvalOneA_spec hk fcW pivW witW witDotY freeOH hitsAcc idx
      hgs hwf hwt hfclen hfc hpivlen hpiv hwitlen hwit hwdy_len hwdy hfohlen hfoh hacc_len hacc
    have hle1 : gs.length ≤ s.1.length := extends_length ss.1
    have ih' := ih s.2 ss.2.1
      (lt_of_lt_of_le hwf (Nat.add_le_add_left hle1 n))
      (lt_of_lt_of_le hwt (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hfc w hw) (Nat.add_le_add_left hle1 n))
      (fun w hw => lt_of_lt_of_le (hpiv w hw) (Nat.add_le_add_left hle1 n))
      (fun r' hr' => have h := hwit r' hr'; ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
      (fun w hw => lt_of_lt_of_le (hwdy w hw) (Nat.add_le_add_left hle1 n))
      (fun r' hr' => have h := hfoh r' hr'; ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hle1 n)⟩)
      ss.2.2.2.1 ss.2.2.2.2.1
    refine ⟨extends_trans ss.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ih'.2.2.2.2.1, ?_⟩
    · have h1 := ss.2.2.1; have h2 := ih'.2.2.1
      change s.1.length ≤ _ at h1
      change (gEvalHitsLoop k r m q n wFalse wTrue s.1 fcW pivW witW witDotY freeOH s.2 rest).1.length ≤ _ at h2
      simp only [List.length_cons]
      nlinarith
    · intro u v cr cc A B y t cutS piv wit hpiv_card hwf_val hwt_val hfc_val hpiv_val hwit_val hwdy_val hfoh_val hbound
      set inp := mkInp k r m u v cr cc A B y t
      have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
      have hs_val := ss.2.2.2.2.2 u v cr cc A B y t cutS piv wit hpiv_card
        hwf_val hwt_val hfc_val hpiv_val hwit_val hwdy_val hfoh_val
      rw [show mkInp k r m u v cr cc A B y t = inp from rfl] at hs_val
      have hs_no_mod : bitsVal (s.2.map (wireVal s.1 inp)) =
          bitsVal (hitsAcc.map (wireVal gs inp)) +
            (decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
              (reconstructW hk u.val v.val cr cc A B y cutS piv wit (bitsToFun (k - q) idx)).val j = y j)).toNat := by
        rw [hs_val]
        apply Nat.mod_eq_of_lt
        have hle_one : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
        have hle_d := hle_one (decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
          (reconstructW hk u.val v.val cr cc A B y cutS piv wit (bitsToFun (k - q) idx)).val j = y j))
        simp only [List.length_cons] at hbound
        omega
      have hbound2 : bitsVal (s.2.map (wireVal s.1 inp)) + rest.length < 2 ^ (k + 1) := by
        rw [hs_no_mod]
        have hle_one : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide
        have hle_d := hle_one (decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
          (reconstructW hk u.val v.val cr cc A B y cutS piv wit (bitsToFun (k - q) idx)).val j = y j))
        simp only [List.length_cons] at hbound
        omega
      have hih_val := ih'.2.2.2.2.2 u v cr cc A B y t cutS piv wit hpiv_card
        (by rw [wireVal_extends ss.1 hinp hwf, hwf_val])
        (by rw [wireVal_extends ss.1 hinp hwt, hwt_val])
        (by rw [listVal_extends ss.1 hinp hfc, hfc_val])
        (by rw [listVal_extends ss.1 hinp hpiv, hpiv_val])
        (fun i => by
          have hmem := (hwit _ (getD_mem_of_lt witW (by rw [hwitlen]; exact i.isLt))).2
          rw [listVal_extends ss.1 hinp hmem, hwit_val i])
        (by rw [listVal_extends ss.1 hinp hwdy, hwdy_val])
        (fun i => by
          have hmem := (hfoh _ (getD_mem_of_lt freeOH (by rw [hfohlen]; exact i.isLt))).2
          rw [listVal_extends ss.1 hinp hmem, hfoh_val i])
        hbound2
      rw [hih_val, hs_no_mod, List.filter_cons]
      cases hdec : decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
          (reconstructW hk u.val v.val cr cc A B y cutS piv wit (bitsToFun (k - q) idx)).val j = y j) <;>
        simp [hdec] <;> omega

def buildCircuit (k r m q : ℕ) : Circuit :=
  let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
  let g0 := gFalse n []
  let wFalse := g0.2
  let g1 := gTrue n g0.1
  let wTrue := g1.2
  let cuts := gSolveCutLoop k r m q n wFalse wTrue g1.1 (List.finRange k)
  let passW := gOrList n wFalse cuts.1 cuts.2.1
  let fcW := gFirst n wFalse passW.1 cuts.2.1
  let pivW := gSelectMat n wFalse fcW.1 fcW.2 cuts.2.2.1 k
  let witW := gSelectWitLoop n wFalse m pivW.1 fcW.2 cuts.2.2.2 (List.finRange k)
  let freeOH := gFreeOneHot k q n wFalse wTrue witW.1 pivW.2
  let witDotY := gWitDotY n wFalse freeOH.1 (yWires k r m) witW.2
  let hits0 := List.replicate (k + 1) wFalse
  let loop := gEvalHitsLoop k r m q n wFalse wTrue witDotY.1 fcW.2 pivW.2 witW.2 witDotY.2 freeOH.2
    hits0 (List.range (2 ^ (k - q)))
  let tleq := gCmpBits n loop.1 wTrue (tWires k r m) loop.2
  let out := gAnd n tleq.1 passW.2 tleq.2
  ⟨out.1, out.2⟩

lemma buildCircuit_size_bound (k r m q outLen : ℕ) (hqk : q ≤ k)
    (hout : outLen ≤
      2 + (k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) +
            10 * k * (k + 1) + 5 * (k + 1) + k) * k +
      k + 3 * k + 5 * k * k + 5 * k * m * k +
      (k + 5 * (k + 1) * k + (6 * (k + 1) + 1) * (k - q) * k) + 5 * m * k +
      ((k - q) * k + ((5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k) +
        (8 * k + 44 * r * k + (10 * k + 4) * m) + 6 * m + 5 * (k + 1)) * 2 ^ (k - q) +
      5 * (k + 1) + 1) :
    outLen ≤ 2 ^ 26 * (k + r + m + 3) ^ 10 * 2 ^ (k - q) := by
  set S := k + r + m + 3
  have hkS : k ≤ S := by omega
  have hrS : r ≤ S := by omega
  have hmS : m ≤ S := by omega
  have hk1S : k + 1 ≤ S := by omega
  have hkqS : k - q ≤ S := by omega
  have h1S : 1 ≤ S := by omega
  have hm2 : m * m ≤ S * S := Nat.mul_le_mul hmS hmS
  have hk2 : k * k ≤ S * S := Nat.mul_le_mul hkS hkS
  have hrk : r * k ≤ S * S := Nat.mul_le_mul hrS hkS
  have hkm : k * m ≤ S * S := Nat.mul_le_mul hkS hmS
  have hkk1 : k * (k + 1) ≤ S * S := Nat.mul_le_mul hkS hk1S
  have hkqk : (k - q) * k ≤ S * S := Nat.mul_le_mul hkqS hkS
  have hk1kqk : (k + 1) * (k - q) * k ≤ S * S * S :=
    Nat.mul_le_mul (Nat.mul_le_mul hk1S hkqS) hkS
  have hkmk : k * m * k ≤ S * S * S := Nat.mul_le_mul hkm hkS
  have hk1k : (k + 1) * k ≤ S * S := Nat.mul_le_mul hk1S hkS
  have hS12 : S ≤ S * S := Nat.le_mul_of_pos_right S h1S
  have hS23 : S * S ≤ S * S * S := Nat.le_mul_of_pos_right (S * S) h1S
  have hS34 : S * S * S ≤ S * S * S * S := Nat.le_mul_of_pos_right (S * S * S) h1S
  have hS45 : S * S * S * S ≤ S * S * S * S * S := Nat.le_mul_of_pos_right _ h1S
  have h1S2 : 1 ≤ S * S := le_trans h1S hS12
  have h1S3 : 1 ≤ S * S * S := le_trans h1S2 hS23
  have h1S4 : 1 ≤ S * S * S * S := le_trans h1S3 hS34
  have h1S5 : 1 ≤ S * S * S * S * S := le_trans h1S4 hS45
  have hinner1 : 2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m ≤ 72 * (S * S * S) := by
    have h1 : 22 * m * m + 5 * m ≤ 27 * (S * S) := by linarith
    have h2 : 2 * k * (22 * m * m + 5 * m) ≤ 2 * S * (27 * (S * S)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hkS) h1
    have h54 : 2 * S * (27 * (S * S)) = 54 * (S * S * S) := by ring
    linarith
  have hcut_b : k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) + 10 * k * (k + 1) +
      5 * (k + 1) + k ≤ 88 * (S * S * S * S) := by
    have h1 : k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) ≤ S * (72 * (S * S * S)) :=
      Nat.mul_le_mul hkS hinner1
    have h72 : S * (72 * (S * S * S)) = 72 * (S * S * S * S) := by ring
    have h10 : 10 * k * (k + 1) = 10 * (k * (k + 1)) := by ring
    linarith
  have hcuts_b : (k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) +
      10 * k * (k + 1) + 5 * (k + 1) + k) * k ≤ 88 * (S * S * S * S * S) := by
    have h2 := Nat.mul_le_mul hcut_b hkS
    have h88 : 88 * (S * S * S * S) * S = 88 * (S * S * S * S * S) := by ring
    linarith
  have hfoh_b : (6 * (k + 1) + 1) * (k - q) * k ≤ 7 * (S * S * S) := by
    have heq : (6 * (k + 1) + 1) * (k - q) * k = 6 * ((k + 1) * (k - q) * k) + (k - q) * k := by ring
    linarith
  have honeA_b : (k - q) * k +
      ((5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k) +
      (8 * k + 44 * r * k + (10 * k + 4) * m) + 6 * m + 5 * (k + 1) ≤ 160 * (S * S * S * S * S) := by
    have hexp1 : (10 * k + 4) * m = 10 * (k * m) + 4 * m := by ring
    have h44 : 44 * r * k = 44 * (r * k) := by ring
    have h5kk : 5 * k * k = 5 * (k * k) := by ring
    have h1 : 5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8 ≤ 80 * (S * S) := by
      rw [hexp1, h44, h5kk]; linarith
    have h2 : (5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k ≤ 80 * (S * S) * S :=
      Nat.mul_le_mul h1 hkS
    have h80 : 80 * (S * S) * S = 80 * (S * S * S) := by ring
    have hexp2 : (k - q) * k +
        ((5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k) +
        (8 * k + 44 * r * k + (10 * k + 4) * m) + 6 * m + 5 * (k + 1) =
        (k - q) * k + (5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k +
        5 * (k * k) + 8 * k + 44 * (r * k) + 10 * (k * m) + 10 * m + 5 * (k + 1) := by ring
    rw [hexp2]
    linarith
  have hpow_ge : 1 ≤ 2 ^ (k - q) := Nat.one_le_pow _ _ (by decide)
  have hpre_b : 2 + 88 * (S * S * S * S * S) + k + 3 * k + 5 * k * k + 5 * k * m * k +
      (k + 5 * (k + 1) * k + (6 * (k + 1) + 1) * (k - q) * k) + 5 * m * k + 5 * (k + 1) + 1 ≤
      136 * (S * S * S * S * S) := by
    have h5kk : 5 * k * k = 5 * (k * k) := by ring
    have h5kmk : 5 * k * m * k = 5 * (k * m * k) := by ring
    have h5k1k : 5 * (k + 1) * k = 5 * ((k + 1) * k) := by ring
    have h5mk : 5 * m * k = 5 * (m * k) := by ring
    have hmk : m * k ≤ S * S := Nat.mul_le_mul hmS hkS
    rw [h5kk, h5kmk, h5k1k, h5mk]
    linarith
  have hpre_mul : 2 + 88 * (S * S * S * S * S) + k + 3 * k + 5 * k * k + 5 * k * m * k +
      (k + 5 * (k + 1) * k + (6 * (k + 1) + 1) * (k - q) * k) + 5 * m * k + 5 * (k + 1) + 1 ≤
      136 * (S * S * S * S * S) * 2 ^ (k - q) :=
    le_trans hpre_b (Nat.le_mul_of_pos_right _ hpow_ge)
  have hloop_mul := Nat.mul_le_mul_right (2 ^ (k - q)) honeA_b
  have hS5_eq : S * S * S * S * S = S ^ 5 := by ring
  have hS5_10 : S ^ 5 ≤ S ^ 10 := Nat.pow_le_pow_right h1S (by decide)
  have htot : outLen ≤ 296 * S ^ 5 * 2 ^ (k - q) := by
    rw [← hS5_eq]
    linarith
  calc outLen ≤ 296 * S ^ 5 * 2 ^ (k - q) := htot
    _ ≤ 2 ^ 26 * S ^ 10 * 2 ^ (k - q) := by
        apply Nat.mul_le_mul_right
        calc 296 * S ^ 5 ≤ 2 ^ 26 * S ^ 5 := Nat.mul_le_mul_right _ (by decide)
          _ ≤ 2 ^ 26 * S ^ 10 := Nat.mul_le_mul_left _ hS5_10

lemma buildCircuit_spec {k r m q : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (hqk : q ≤ k) :
    let n := 2 * k + 2 * r * k + 2 * m * k + m + (k + 1)
    let C := buildCircuit k r m q
    FanInTwo C ∧ ReadsBack n C ∧ C.size ≤ 2 ^ 26 * (k + r + m + 3) ^ 10 * 2 ^ (k - q) ∧
      ∀ (u v : Fin (2 ^ k)) (cr cc : Fin r → Fin (2 ^ k)) (A B : Fin m → Fin (2 ^ k))
        (y : Fin m → Bool) (t : Fin (2 ^ (k + 1))),
        let hits := Nat.card {w : Fin (2 ^ k) // ∀ j : Fin m, fFn k r m u.val v.val cr cc A B w.val j = y j}
        (passBool k r m q A B = true → hits ≤ 2 ^ (k - q)) ∧
        C.eval (mkInp k r m u v cr cc A B y t) = decide (passBool k r m q A B = true ∧ t.val ≤ hits) := by
  intro n C
  dsimp only [C, buildCircuit]
  set g0 := gFalse n []
  set wFalse := g0.2
  set g1 := gTrue n g0.1
  set wTrue := g1.2
  set cuts := gSolveCutLoop k r m q n wFalse wTrue g1.1 (List.finRange k)
  set passW := gOrList n wFalse cuts.1 cuts.2.1
  set fcW := gFirst n wFalse passW.1 cuts.2.1
  set pivW := gSelectMat n wFalse fcW.1 fcW.2 cuts.2.2.1 k
  set witW := gSelectWitLoop n wFalse m pivW.1 fcW.2 cuts.2.2.2 (List.finRange k)
  set freeOH := gFreeOneHot k q n wFalse wTrue witW.1 pivW.2
  set witDotY := gWitDotY n wFalse freeOH.1 (yWires k r m) witW.2
  set hits0 := List.replicate (k + 1) wFalse
  set loop := gEvalHitsLoop k r m q n wFalse wTrue witDotY.1 fcW.2 pivW.2 witW.2 witDotY.2 freeOH.2
    hits0 (List.range (2 ^ (k - q)))
  set tleq := gCmpBits n loop.1 wTrue (tWires k r m) loop.2
  set out := gAnd n tleq.1 passW.2 tleq.2
  have s0 := gFalse_spec (goodGates_nil n)
  have hwf0 : wFalse < n + g0.1.length := s0.2.2.2.1
  have s1 := gTrue_spec s0.2.1
  have hle01 : g0.1.length ≤ g1.1.length := extends_length s1.1
  have hwf1 : wFalse < n + g1.1.length := lt_of_lt_of_le hwf0 (Nat.add_le_add_left hle01 n)
  have hwt1 : wTrue < n + g1.1.length := s1.2.2.2.1
  have sc := gSolveCutLoop_spec hk hqk (List.finRange k) s1.2.1 hwf1 hwt1
  have hle1c : g1.1.length ≤ cuts.1.length := extends_length sc.1
  have hwfc : wFalse < n + cuts.1.length := lt_of_lt_of_le hwf1 (Nat.add_le_add_left hle1c n)
  have hwtc : wTrue < n + cuts.1.length := lt_of_lt_of_le hwt1 (Nat.add_le_add_left hle1c n)
  have hcutlen : cuts.2.1.length = k := by rw [sc.2.2.2.1, List.length_finRange]
  have sp := gOrList_spec cuts.2.1 sc.2.1 hwfc sc.2.2.2.2.1
  have hlecp : cuts.1.length ≤ passW.1.length := extends_length sp.1
  have hwfp : wFalse < n + passW.1.length := lt_of_lt_of_le hwfc (Nat.add_le_add_left hlecp n)
  have hwtp : wTrue < n + passW.1.length := lt_of_lt_of_le hwtc (Nat.add_le_add_left hlecp n)
  have sfc := gFirst_spec cuts.2.1 sp.2.1 hwfp
    (fun w hw => lt_of_lt_of_le (sc.2.2.2.2.1 w hw) (Nat.add_le_add_left hlecp n))
  have hlepfc : passW.1.length ≤ fcW.1.length := extends_length sfc.1
  have hlecfc : cuts.1.length ≤ fcW.1.length := le_trans hlecp hlepfc
  have hwffc : wFalse < n + fcW.1.length := lt_of_lt_of_le hwfp (Nat.add_le_add_left hlepfc n)
  have hwtfc : wTrue < n + fcW.1.length := lt_of_lt_of_le hwtp (Nat.add_le_add_left hlepfc n)
  have hfc_len : fcW.2.length = k := by rw [sfc.2.2.2.1, hcutlen]
  have spiv := gSelectMat_spec fcW.2 cuts.2.2.1 k sfc.2.1 hwffc sfc.2.2.2.2.1
    (fun r' hr' w hw => lt_of_lt_of_le ((sc.2.2.2.2.2.2.1 r' hr').2 w hw) (Nat.add_le_add_left hlecfc n))
  have hlefcp : fcW.1.length ≤ pivW.1.length := extends_length spiv.1
  have hlecpiv : cuts.1.length ≤ pivW.1.length := le_trans hlecfc hlefcp
  have hwfpiv : wFalse < n + pivW.1.length := lt_of_lt_of_le hwffc (Nat.add_le_add_left hlefcp n)
  have hwtpiv : wTrue < n + pivW.1.length := lt_of_lt_of_le hwtfc (Nat.add_le_add_left hlefcp n)
  have swit := gSelectWitLoop_spec n wFalse m fcW.2 cuts.2.2.2 (List.finRange k) spiv.2.1 hwfpiv
    (fun w hw => lt_of_lt_of_le (sfc.2.2.2.2.1 w hw) (Nat.add_le_add_left hlefcp n))
    (fun wm hwm => have h := sc.2.2.2.2.2.2.2.2.1 wm hwm;
      ⟨h.1, fun rw hrw => have h' := h.2 rw hrw;
        ⟨h'.1, fun w hw => lt_of_lt_of_le (h'.2 w hw) (Nat.add_le_add_left hlecpiv n)⟩⟩)
  have hlepivw : pivW.1.length ≤ witW.1.length := extends_length swit.1
  have hlefcw : fcW.1.length ≤ witW.1.length := le_trans hlefcp hlepivw
  have hwfw : wFalse < n + witW.1.length := lt_of_lt_of_le hwfpiv (Nat.add_le_add_left hlepivw n)
  have hwtw : wTrue < n + witW.1.length := lt_of_lt_of_le hwtpiv (Nat.add_le_add_left hlepivw n)
  have hwit_len : witW.2.length = k := by rw [swit.2.2.2.1, List.length_finRange]
  have sfoh := gFreeOneHot_spec (q := q) pivW.2 swit.2.1 hwfw hwtw spiv.2.2.2.1
    (fun w hw => lt_of_lt_of_le (spiv.2.2.2.2.1 w hw) (Nat.add_le_add_left hlepivw n))
  have hlewfoh : witW.1.length ≤ freeOH.1.length := extends_length sfoh.1
  have hwffoh : wFalse < n + freeOH.1.length := lt_of_lt_of_le hwfw (Nat.add_le_add_left hlewfoh n)
  have hwtfoh : wTrue < n + freeOH.1.length := lt_of_lt_of_le hwtw (Nat.add_le_add_left hlewfoh n)
  have hy_mem_foh : ∀ w ∈ yWires k r m, w < n + freeOH.1.length :=
    fun w hw => lt_of_lt_of_le (yWires_mem k r m hw) (Nat.le_add_right n freeOH.1.length)
  have hylen : (yWires k r m).length = m := by simp [yWires]
  have swdy := gWitDotY_spec (yWires k r m) witW.2 sfoh.2.1 hwffoh hy_mem_foh
    (fun rw hrw => have h := swit.2.2.2.2.1 rw hrw;
      ⟨by rw [h.1, hylen], fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hlewfoh n)⟩)
  have hlefohwdy : freeOH.1.length ≤ witDotY.1.length := extends_length swdy.1
  have hlewwdy : witW.1.length ≤ witDotY.1.length := le_trans hlewfoh hlefohwdy
  have hlepivwdy : pivW.1.length ≤ witDotY.1.length := le_trans hlepivw hlewwdy
  have hlefcwdy : fcW.1.length ≤ witDotY.1.length := le_trans hlefcp hlepivwdy
  have hwfwdy : wFalse < n + witDotY.1.length := lt_of_lt_of_le hwffoh (Nat.add_le_add_left hlefohwdy n)
  have hwtwdy : wTrue < n + witDotY.1.length := lt_of_lt_of_le hwtfoh (Nat.add_le_add_left hlefohwdy n)
  have hwdy_len : witDotY.2.length = k := by rw [swdy.2.2.2.1, hwit_len]
  have hhits0_len : hits0.length = k + 1 := List.length_replicate
  have hhits0_mem : ∀ w ∈ hits0, w < n + witDotY.1.length := by
    intro w hw; rw [List.mem_replicate] at hw; rcases hw with ⟨_, rfl⟩; exact hwfwdy
  have sloop := gEvalHitsLoop_spec hk fcW.2 pivW.2 witW.2 witDotY.2 freeOH.2 hits0 (List.range (2 ^ (k - q)))
    swdy.2.1 hwfwdy hwtwdy hfc_len (fun w hw => lt_of_lt_of_le (sfc.2.2.2.2.1 w hw) (Nat.add_le_add_left hlefcwdy n))
    spiv.2.2.2.1 (fun w hw => lt_of_lt_of_le (spiv.2.2.2.2.1 w hw) (Nat.add_le_add_left hlepivwdy n))
    hwit_len (fun rw hrw => have h := swit.2.2.2.2.1 rw hrw;
      ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hlewwdy n)⟩)
    hwdy_len swdy.2.2.2.2.1 sfoh.2.2.2.1
    (fun rw hrw => have h := sfoh.2.2.2.2.1 rw hrw;
      ⟨h.1, fun w hw => lt_of_lt_of_le (h.2 w hw) (Nat.add_le_add_left hlefohwdy n)⟩)
    hhits0_len hhits0_mem
  have hlewdyl : witDotY.1.length ≤ loop.1.length := extends_length sloop.1
  have hlepl : passW.1.length ≤ loop.1.length :=
    le_trans hlepfc (le_trans hlefcwdy hlewdyl)
  have hwtl : wTrue < n + loop.1.length := lt_of_lt_of_le hwtwdy (Nat.add_le_add_left hlewdyl n)
  have ht_mem : ∀ w ∈ tWires k r m, w < n + loop.1.length :=
    fun w hw => lt_of_lt_of_le (tWires_mem k r m hw) (Nat.le_add_right n loop.1.length)
  have stleq := gCmpBits_spec (tWires k r m) loop.2 sloop.2.1 hwtl ht_mem sloop.2.2.2.2.1
  have hlelt : loop.1.length ≤ tleq.1.length := extends_length stleq.1
  have hlept : passW.1.length ≤ tleq.1.length := le_trans hlepl hlelt
  have sout := gAnd_spec stleq.2.1 (lt_of_lt_of_le sp.2.2.2.1 (Nat.add_le_add_left hlept n)) stleq.2.2.2.1
  refine ⟨goodGates_fanInTwo sout.2.1, goodGates_readsBack sout.2.1, ?_, ?_⟩
  · have hg0l : g0.1.length = 1 := by simp [g0, gFalse]
    have hg1l : g1.1.length = 2 := by have := s1.2.2.1; change g1.1.length = g0.1.length + 1 at this; omega
    have hcuts_l : cuts.1.length ≤ 2 + (k * (2 * k * (22 * m * m + 5 * m) + 10 * m * m + 8 * m) +
        10 * k * (k + 1) + 5 * (k + 1) + k) * k := by
      have hc := sc.2.2.1
      change cuts.1.length ≤ g1.1.length + _ * (List.finRange k).length at hc
      rw [List.length_finRange, hg1l] at hc
      exact hc
    have hpass_l : passW.1.length ≤ cuts.1.length + k := by
      have h := sp.2.2.1
      change passW.1.length = cuts.1.length + cuts.2.1.length at h
      rw [hcutlen] at h; omega
    have hfc_l : fcW.1.length ≤ passW.1.length + 3 * k := by
      have h := sfc.2.2.1
      change fcW.1.length ≤ passW.1.length + 3 * cuts.2.1.length at h
      rw [hcutlen] at h; omega
    have hpiv_l : pivW.1.length ≤ fcW.1.length + 5 * k * k := by
      have h := spiv.2.2.1
      change pivW.1.length ≤ fcW.1.length + 5 * fcW.2.length * k at h
      rw [hfc_len] at h; omega
    have hwit_l : witW.1.length ≤ pivW.1.length + 5 * k * m * k := by
      have h := swit.2.2.1
      change witW.1.length ≤ pivW.1.length + 5 * fcW.2.length * m * (List.finRange k).length at h
      rw [hfc_len, List.length_finRange] at h; exact h
    have hfoh_l : freeOH.1.length ≤ witW.1.length + k + 5 * (k + 1) * k + (6 * (k + 1) + 1) * (k - q) * k :=
      sfoh.2.2.1
    have hwdy_l : witDotY.1.length ≤ freeOH.1.length + 5 * m * k := by
      have h := swdy.2.2.1
      change witDotY.1.length ≤ freeOH.1.length + 5 * (yWires k r m).length * witW.2.length at h
      rw [hylen, hwit_len] at h; omega
    have hloop_l : loop.1.length ≤ witDotY.1.length +
        ((k - q) * k + ((5 * k * k + 8 * k + 44 * r * k + (10 * k + 4) * m + 5 * m + 8) * k + 5 * k * k) +
          (8 * k + 44 * r * k + (10 * k + 4) * m) + 6 * m + 5 * (k + 1)) * 2 ^ (k - q) := by
      have h := sloop.2.2.1
      change loop.1.length ≤ witDotY.1.length + _ * (List.range (2 ^ (k - q))).length at h
      rw [List.length_range] at h
      exact h
    have htleq_l : tleq.1.length ≤ loop.1.length + 5 * (k + 1) := by
      have h := stleq.2.2.1
      change tleq.1.length ≤ loop.1.length + 5 * (tWires k r m).length at h
      have htlen : (tWires k r m).length = k + 1 := by simp [tWires]
      rw [htlen] at h; omega
    have hout_l : out.1.length = tleq.1.length + 1 := sout.2.2.1
    change out.1.length ≤ _
    exact buildCircuit_size_bound k r m q out.1.length hqk (by linarith)
  · intro u v cr cc A B y t
    set inp := mkInp k r m u v cr cc A B y t
    have hinp : inp.length = n := mkInp_length k r m u v cr cc A B y t
    have hwf_val0 : wireVal g0.1 inp wFalse = false := s0.2.2.2.2 inp hinp
    have hwf_val1 : wireVal g1.1 inp wFalse = false := by rw [wireVal_extends s1.1 hinp hwf0, hwf_val0]
    have hwt_val1 : wireVal g1.1 inp wTrue = true := s1.2.2.2.2 inp hinp
    have hwf_valc : wireVal cuts.1 inp wFalse = false := by rw [wireVal_extends sc.1 hinp hwf1, hwf_val1]
    have hwt_valc : wireVal cuts.1 inp wTrue = true := by rw [wireVal_extends sc.1 hinp hwt1, hwt_val1]
    have hsc_val := sc.2.2.2.2.2.2.2.2.2 u v cr cc A B y t hwf_val1 hwt_val1
    have hcut_map : cuts.2.1.map (wireVal cuts.1 inp) = List.ofFn (cutPass k r m q A B) := by
      rw [hsc_val.1]
      apply List.ext_getElem <;> simp
    have hpass_val : wireVal passW.1 inp passW.2 = passBool k r m q A B := by
      rw [sp.2.2.2.2 inp k (cutPass k r m q A B) hinp hwf_valc hcut_map]
      rfl
    have hpass_out : wireVal out.1 inp passW.2 = passBool k r m q A B := by
      rw [wireVal_extends (extends_trans sfc.1 (extends_trans spiv.1 (extends_trans swit.1
        (extends_trans sfoh.1 (extends_trans swdy.1 (extends_trans sloop.1 (extends_trans stleq.1 sout.1))))))) hinp sp.2.2.2.1,
        hpass_val]
    have heval_eq : (⟨out.1, out.2⟩ : Circuit).eval inp = wireVal out.1 inp out.2 := rfl
    have hout_val : wireVal out.1 inp out.2 =
        (passBool k r m q A B && wireVal tleq.1 inp tleq.2) := by
      rw [sout.2.2.2.2 inp hinp,
        wireVal_extends (extends_trans sfc.1 (extends_trans spiv.1 (extends_trans swit.1
          (extends_trans sfoh.1 (extends_trans swdy.1 (extends_trans sloop.1 stleq.1)))))) hinp sp.2.2.2.1,
        hpass_val]
    by_cases hp : passBool k r m q A B = true
    · obtain ⟨cutS, hfc_spec, hpiv_card, hle_bound, hcard_eq⟩ :=
        hits_le_and_eq_of_pass hk hr u v cr cc A B y hp
      refine ⟨fun _ => hle_bound, ?_⟩
      rw [heval_eq, hout_val, hp, Bool.true_and]
      have hwf_valp : wireVal passW.1 inp wFalse = false := by rw [wireVal_extends sp.1 hinp hwfc, hwf_valc]
      have hwf_valfc : wireVal fcW.1 inp wFalse = false := by rw [wireVal_extends sfc.1 hinp hwfp, hwf_valp]
      have hwf_valpiv : wireVal pivW.1 inp wFalse = false := by rw [wireVal_extends spiv.1 hinp hwffc, hwf_valfc]
      have hwf_valw : wireVal witW.1 inp wFalse = false := by rw [wireVal_extends swit.1 hinp hwfpiv, hwf_valpiv]
      have hwt_valw : wireVal witW.1 inp wTrue = true := by
        rw [wireVal_extends (extends_trans sc.1 (extends_trans sp.1 (extends_trans sfc.1
          (extends_trans spiv.1 swit.1)))) hinp hwt1, hwt_val1]
      have hwf_valfoh : wireVal freeOH.1 inp wFalse = false := by rw [wireVal_extends sfoh.1 hinp hwfw, hwf_valw]
      have hwt_valfoh : wireVal freeOH.1 inp wTrue = true := by
        rw [wireVal_extends (extends_trans sc.1 (extends_trans sp.1 (extends_trans sfc.1
          (extends_trans spiv.1 (extends_trans swit.1 sfoh.1))))) hinp hwt1, hwt_val1]
      have hwf_valwdy : wireVal witDotY.1 inp wFalse = false := by rw [wireVal_extends swdy.1 hinp hwffoh, hwf_valfoh]
      have hwt_valwdy : wireVal witDotY.1 inp wTrue = true := by rw [wireVal_extends swdy.1 hinp hwtfoh, hwt_valfoh]
      have hfc_val : fcW.2.map (wireVal fcW.1 inp) = List.ofFn (fun cut : Fin k => decide (cut = cutS)) := by
        rw [sfc.2.2.2.2.2 inp k (cutPass k r m q A B) hinp hwf_valp
          (by rw [listVal_extends sp.1 hinp sc.2.2.2.2.1, hcut_map])]
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.length_ofFn] at h1
          simp only [List.getElem_ofFn]
          exact hfc_spec ⟨i, h1⟩
      set piv := pivSel q (availTab k r m A B cutS)
      set wit := witTab k r m A B cutS
      have hpiv_val : pivW.2.map (wireVal pivW.1 inp) = List.ofFn piv := by
        refine (spiv.2.2.2.2.2 inp k (fun cut => decide (cut = cutS))
          (fun c => pivSel q (availTab k r m A B c)) hinp hwf_valfc hfc_val
          (by rw [sc.2.2.2.2.2.1, List.length_finRange]) (fun cut => ?_)).trans ?_
        · have hmem := (sc.2.2.2.2.2.2.1 _ (getD_mem_of_lt cuts.2.2.1 (by rw [sc.2.2.2.2.2.1, List.length_finRange]; exact cut.isLt))).2
          rw [listVal_extends (extends_trans sp.1 sfc.1) hinp hmem]
          simpa using hsc_val.2.1 cut.val (by simp)
        · apply List.ext_getElem
          · simp
          · intro j h1 h2
            simp only [List.length_ofFn] at h1
            simp only [List.getElem_ofFn, dotBool_oneHot]
            rfl
      have hwit_val : ∀ i : Fin k, (witW.2.getD i.val []).map (wireVal witW.1 inp) = List.ofFn (wit i) := by
        intro i
        have hi_lt : i.val < (List.finRange k).length := by simp [i.isLt]
        refine (swit.2.2.2.2.2 inp k (fun cut => decide (cut = cutS))
          (fun c i' => witTab k r m A B c i') hinp hwf_valpiv
          (by rw [listVal_extends spiv.1 hinp sfc.2.2.2.2.1, hfc_val])
          (by rw [sc.2.2.2.2.2.2.2.1, List.length_finRange]) (fun c i' => ?_) i.val hi_lt).trans ?_
        · have hm1 := sc.2.2.2.2.2.2.2.2.1 _ (getD_mem_of_lt cuts.2.2.2 (by rw [sc.2.2.2.2.2.2.2.1, List.length_finRange]; exact c.isLt))
          have hm2 := (hm1.2 _ (getD_mem_of_lt _ (by rw [hm1.1]; exact i'.isLt))).2
          rw [listVal_extends (extends_trans sp.1 (extends_trans sfc.1 spiv.1)) hinp hm2]
          simpa using hsc_val.2.2 c.val (by simp) i'
        · apply List.ext_getElem
          · simp
          · intro j h1 h2
            simp only [List.length_ofFn] at h1
            simp only [List.getElem_ofFn, List.getElem_finRange, Fin.cast_mk, Fin.eta, dotBool_oneHot]
            rfl
      have hfoh_val : ∀ i : Fin k, (freeOH.2.getD i.val []).map (wireVal freeOH.1 inp) =
          List.ofFn (fun d : Fin (k - q) => !piv i && decide (freeCountBefore piv i = d.val)) :=
        sfoh.2.2.2.2.2 inp piv hinp hwf_valw hwt_valw
          (by rw [listVal_extends swit.1 hinp spiv.2.2.2.2.1, hpiv_val])
      have hy_mem_w : ∀ w ∈ yWires k r m, w < n + witW.1.length :=
        fun w hw => lt_of_lt_of_le (yWires_mem k r m hw) (Nat.le_add_right n witW.1.length)
      have hwdy_val : witDotY.2.map (wireVal witDotY.1 inp) = List.ofFn (fun i : Fin k => dotBool (wit i) y) := by
        refine swdy.2.2.2.2.2 inp m k y wit hinp hwf_valfoh ?_ hwit_len (fun i => ?_)
        · rw [listVal_extends sfoh.1 hinp hy_mem_w]
          apply List.ext_getElem
          · simp [yWires]
          · intro j h1 h2
            simp only [yWires, List.length_map, List.length_finRange] at h1
            simp only [yWires, List.map_map, List.getElem_map, List.getElem_finRange, Fin.val_cast,
              Function.comp_apply, List.getElem_ofFn]
            have hyj : 2 * k + 2 * r * k + 2 * m * k + j ∈ yWires k r m := by
              simp only [yWires, List.mem_map, List.mem_finRange, true_and]
              exact ⟨⟨j, h1⟩, rfl⟩
            rw [wireVal_input swit.2.1 hinp (yWires_mem k r m hyj)]
            exact mkInp_getD_y u v cr cc A B y t ⟨j, h1⟩
        · have hmem := (swit.2.2.2.2.1 _ (getD_mem_of_lt witW.2 (by rw [hwit_len]; exact i.isLt))).2
          have hex : (witW.2.getD i.val []).map (wireVal freeOH.1 inp) =
              (witW.2.getD i.val []).map (wireVal witW.1 inp) :=
            listVal_extends sfoh.1 hinp hmem
          rw [hex, hwit_val i]
      have hhits0_val : bitsVal (hits0.map (wireVal witDotY.1 inp)) = 0 := by
        have hm : hits0.map (wireVal witDotY.1 inp) = List.replicate (k + 1) false := by
          simp [hits0, List.map_replicate, hwf_valwdy]
        rw [hm, bitsVal_replicate_false]
      have hbound_loop : bitsVal (hits0.map (wireVal witDotY.1 inp)) + (List.range (2 ^ (k - q))).length < 2 ^ (k + 1) := by
        rw [hhits0_val, List.length_range, Nat.zero_add]
        have hpow1 : 2 ^ (k - q) ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (Nat.sub_le k q)
        have hpow2 : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)
        exact lt_of_le_of_lt hpow1 hpow2
      have hloop_val := sloop.2.2.2.2.2 u v cr cc A B y t cutS piv wit hpiv_card hwf_valwdy hwt_valwdy
        (by rw [listVal_extends (extends_trans spiv.1 (extends_trans swit.1 (extends_trans sfoh.1 swdy.1))) hinp
          sfc.2.2.2.2.1, hfc_val])
        (by rw [listVal_extends (extends_trans swit.1 (extends_trans sfoh.1 swdy.1)) hinp spiv.2.2.2.2.1, hpiv_val])
        (fun i => by
          have hmem := (swit.2.2.2.2.1 _ (getD_mem_of_lt witW.2 (by rw [hwit_len]; exact i.isLt))).2
          rw [listVal_extends (extends_trans sfoh.1 swdy.1) hinp hmem, hwit_val i])
        hwdy_val
        (fun i => by
          have hmem := (sfoh.2.2.2.2.1 _ (getD_mem_of_lt freeOH.2 (by rw [sfoh.2.2.2.1]; exact i.isLt))).2
          rw [listVal_extends swdy.1 hinp hmem, hfoh_val i])
        hbound_loop
      have hcf := card_filter_eq_range_filter (fun a : Fin (k - q) → Bool =>
        decide (∀ j : Fin m, fFn k r m u.val v.val cr cc A B
          (reconstructW hk u.val v.val cr cc A B y cutS piv wit a).val j = y j))
      rw [hhits0_val, Nat.zero_add, ← hcf, ← hcard_eq] at hloop_val
      have ht_val : bitsVal ((tWires k r m).map (wireVal loop.1 inp)) = t.val := by
        have hm : (tWires k r m).map (wireVal loop.1 inp) = bitsFn (k + 1) t.val := by
          apply List.ext_getElem
          · simp [tWires, bitsFn]
          · intro j h1 h2
            simp only [tWires, List.length_map, List.length_range] at h1
            simp only [tWires, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply,
              bitsFn]
            rw [wireVal_input sloop.2.1 hinp (tWires_mem k r m (List.mem_map.mpr ⟨j, List.mem_range.mpr h1, rfl⟩))]
            exact mkInp_getD_t u v cr cc A B y t h1
        rw [hm, bitsFn, bitsVal_range_testBit, Nat.mod_eq_of_lt t.isLt]
      have hwt_vall : wireVal loop.1 inp wTrue = true := by
        rw [wireVal_extends sloop.1 hinp hwtwdy, hwt_valwdy]
      have htlen_eq : (tWires k r m).length = loop.2.length := by
        rw [sloop.2.2.2.1]; simp [tWires]
      have hstleq := stleq.2.2.2.2 inp hinp htlen_eq
      rw [hstleq, ht_val, hloop_val, hwt_vall]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, true_and, and_true, Nat.le_iff_lt_or_eq]
    · have hpf : passBool k r m q A B = false := Bool.eq_false_iff.mpr hp
      refine ⟨fun h => by simp only [hpf, Bool.false_eq_true] at h, ?_⟩
      rw [heval_eq, hout_val, hpf]
      simp only [Bool.false_and, Bool.false_eq_true, false_and, decide_false]

lemma passBool_iff_anyDec (k r m q : ℕ) (A B : Fin m → Fin (2 ^ k))
    (inst : ∀ cut, DecidablePred (availableFn k r m A B cut)) :
    passBool k r m q A B = true ↔
      ∃ cut : Fin k, q ≤ (@Finset.filter (Fin k) (availableFn k r m A B cut) (inst cut) Finset.univ).card := by
  rw [passBool_iff]
  refine exists_congr fun cut => ?_
  have hfeq : (@Finset.filter (Fin k) (availableFn k r m A B cut) (fun _ => Classical.propDecidable _) Finset.univ) =
      (@Finset.filter (Fin k) (availableFn k r m A B cut) (inst cut) Finset.univ) := by
    ext i; simp
  rw [hfeq]

end CircuitBuilder

end PEqualNP.Outside.L_meta_32574_aux

theorem PEqualNP.Outside.L_meta_32574 : (∀ (k r m q : Nat), 0 < k → 4 ≤ r → q ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let state := fun (col : Bool) (w u : Nat) (c : Fin r → Fin (2^k)) =>
    let g := if col then 2 else 1
    (List.finRange r).foldl (fun x j =>
      step (x ^^^ rot g x ^^^ rot (k-g) x) ^^^
        rot (if col then 3*(j.val+1)+1 else 2*j.val) w ^^^ (c j).val)
      (rot (if col then 3 else 1) w ^^^ u)
  let parity := fun (mask x : Nat) =>
    (List.range k).foldl (fun b i => xor b (mask.testBit i && x.testBit i)) false
  let bits := fun (n x : Nat) => (List.range n).map (fun i => x.testBit i)
  let bank := fun (A : Fin m → Fin (2^k)) =>
    (List.finRange m).flatMap (fun j => bits k (A j).val)
  let sched := fun (c : Fin r → Fin (2^k)) =>
    (List.finRange r).flatMap (fun j => bits k (c j).val)
  let delay := fun col : Bool => if col then 3*r+1 else 2*r-2
  let reach := fun col : Bool => if col then 7*r-2 else 5*r-3
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2*k+2*r*k+2*m*k+m+(k+1)) C ∧
    C.size ≤ 2^26 * (k+r+m+3)^10 * 2^(k-q) ∧
    ∀ (u v : Fin (2^k)) (cr cc : Fin r → Fin (2^k)) (A B : Fin m → Fin (2^k))
      (y : Fin m → Bool) (t : Fin (2^(k+1))),
      let coef := fun (cut : Fin k) (col : Bool) (p : Fin k) (l : Fin m → Bool) =>
        (List.finRange m).foldl (fun acc j => xor acc ((l j) &&
          ((if col then B j else A j).val.testBit ((cut.val+p.val+delay col) % k)))) false
      let available := fun (cut i : Fin k) => ∃ l : Fin m → Bool,
        (∀ (col : Bool) (p : Fin k), (k ≤ p.val+reach col ∨ p < i) →
          coef cut col p l = false) ∧ xor (coef cut false i l) (coef cut true i l) = true
      let pass := ∃ cut : Fin k, q ≤ ((Finset.univ : Finset (Fin k)).filter (available cut)).card
      let f := fun (w : Nat) (j : Fin m) =>
        xor (parity (A j).val (state false w u.val cr)) (parity (B j).val (state true w v.val cc))
      let hits := Nat.card {w : Fin (2^k) // ∀ j, f w.val j = y j}
      (pass → hits ≤ 2^(k-q)) ∧
      C.eval (bits k u.val ++ bits k v.val ++ sched cr ++ sched cc ++ bank A ++ bank B ++
        List.ofFn y ++ bits (k+1) t.val) = decide (pass ∧ t.val ≤ hits)) := by
  intro k r m q hk hr hqk
  dsimp only
  obtain ⟨hfan, hrb, hsize, hspec⟩ := PEqualNP.Outside.L_meta_32574_aux.buildCircuit_spec hk hr hqk
  refine ⟨PEqualNP.Outside.L_meta_32574_aux.buildCircuit k r m q, hfan, hrb, hsize, ?_⟩
  intro u v cr cc A B y t
  have hs := hspec u v cr cc A B y t
  refine ⟨fun hp => hs.1 (((PEqualNP.Outside.L_meta_32574_aux.passBool_iff_anyDec k r m q A B _).symm).mp hp), ?_⟩
  have hs2 : (PEqualNP.Outside.L_meta_32574_aux.buildCircuit k r m q).eval
      ((List.range k).map (fun i => u.val.testBit i) ++
        (List.range k).map (fun i => v.val.testBit i) ++
        (List.finRange r).flatMap (fun j => (List.range k).map (fun i => (cr j).val.testBit i)) ++
        (List.finRange r).flatMap (fun j => (List.range k).map (fun i => (cc j).val.testBit i)) ++
        (List.finRange m).flatMap (fun j => (List.range k).map (fun i => (A j).val.testBit i)) ++
        (List.finRange m).flatMap (fun j => (List.range k).map (fun i => (B j).val.testBit i)) ++
        List.ofFn y ++ (List.range (k + 1)).map (fun i => t.val.testBit i)) =
      decide (PEqualNP.Outside.L_meta_32574_aux.passBool k r m q A B = true ∧
        t.val ≤ Nat.card {w : Fin (2 ^ k) // ∀ j : Fin m,
          PEqualNP.Outside.L_meta_32574_aux.fFn k r m u.val v.val cr cc A B w.val j = y j}) := hs.2
  rw [hs2]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact and_congr_left' (PEqualNP.Outside.L_meta_32574_aux.passBool_iff_anyDec k r m q A B _)
