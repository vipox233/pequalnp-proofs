import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_963

open scoped BigOperators

section Helpers

noncomputable def clamp012 (x : ℝ) : ℝ := max 0 (min (1 / 2) x)

lemma clamp012_nonneg (x : ℝ) : 0 ≤ clamp012 x := le_max_left _ _

lemma clamp012_le_half (x : ℝ) : clamp012 x ≤ 1 / 2 :=
  max_le (by norm_num) (min_le_left _ _)

lemma lt_iff_lt_clamp {t x : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    t < x ↔ t < clamp012 x := by
  unfold clamp012
  constructor
  · intro h
    exact lt_max_of_lt_right (lt_min ht1 h)
  · intro h
    rcases lt_max_iff.mp h with h0 | h1
    · linarith
    · exact (lt_min_iff.mp h1).2

lemma gt_iff_gt_clamp {t x : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    x < t ↔ clamp012 x < t := by
  unfold clamp012
  constructor
  · intro h
    exact max_lt ht0 (lt_of_le_of_lt (min_le_right _ _) h)
  · intro h
    have h1 := (max_lt_iff.mp h).2
    rcases min_lt_iff.mp h1 with h12 | hx
    · linarith
    · exact hx

noncomputable def R (a t : ℝ) : ℝ :=
  (if t < a then (1 / 2 : ℝ) else 0) +
  (if 1 - a < t then (1 / 2 : ℝ) else 0) +
  (if t < a - 1 then (1 / 2 : ℝ) else 0) +
  (if 2 - a < t then (1 / 2 : ℝ) else 0)

lemma R_eval_sum_identity {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) :
    clamp012 a + (1 / 2 - clamp012 (1 - a)) + clamp012 (a - 1) + (1 / 2 - clamp012 (2 - a)) = a := by
  unfold clamp012
  by_cases h1 : a ≤ 1 / 2
  · have hm1 : min (1 / 2) a = a := min_eq_right h1
    have hm2 : min (1 / 2) (1 - a) = 1 / 2 := min_eq_left (by linarith)
    have hm3 : min (1 / 2) (a - 1) = a - 1 := min_eq_right (by linarith)
    have hm4 : min (1 / 2) (2 - a) = 1 / 2 := min_eq_left (by linarith)
    rw [hm1, hm2, hm3, hm4, max_eq_right ha0,
      max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2),
      max_eq_left (by linarith : a - 1 ≤ 0)]
    ring
  · by_cases h2 : a ≤ 1
    · have hm1 : min (1 / 2) a = 1 / 2 := min_eq_left (by linarith)
      have hm2 : min (1 / 2) (1 - a) = 1 - a := min_eq_right (by linarith)
      have hm3 : min (1 / 2) (a - 1) = a - 1 := min_eq_right (by linarith)
      have hm4 : min (1 / 2) (2 - a) = 1 / 2 := min_eq_left (by linarith)
      rw [hm1, hm2, hm3, hm4,
        max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2),
        max_eq_right (by linarith : 0 ≤ 1 - a),
        max_eq_left (by linarith : a - 1 ≤ 0)]
      ring
    · by_cases h3 : a ≤ 3 / 2
      · have hm1 : min (1 / 2) a = 1 / 2 := min_eq_left (by linarith)
        have hm2 : min (1 / 2) (1 - a) = 1 - a := min_eq_right (by linarith)
        have hm3 : min (1 / 2) (a - 1) = a - 1 := min_eq_right (by linarith)
        have hm4 : min (1 / 2) (2 - a) = 1 / 2 := min_eq_left (by linarith)
        rw [hm1, hm2, hm3, hm4,
          max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2),
          max_eq_left (by linarith : 1 - a ≤ 0),
          max_eq_right (by linarith : 0 ≤ a - 1)]
        ring
      · have hm1 : min (1 / 2) a = 1 / 2 := min_eq_left (by linarith)
        have hm2 : min (1 / 2) (1 - a) = 1 - a := min_eq_right (by linarith)
        have hm3 : min (1 / 2) (a - 1) = 1 / 2 := min_eq_left (by linarith)
        have hm4 : min (1 / 2) (2 - a) = 2 - a := min_eq_right (by linarith)
        rw [hm1, hm2, hm3, hm4,
          max_eq_right (by norm_num : (0 : ℝ) ≤ 1 / 2),
          max_eq_left (by linarith : 1 - a ≤ 0),
          max_eq_right (by linarith : 0 ≤ 2 - a)]
        ring

lemma R_eq_sum_clamped {a t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    R a t =
      (if t < clamp012 a then (1 / 2 : ℝ) else 0) +
      (if clamp012 (1 - a) < t then (1 / 2 : ℝ) else 0) +
      (if t < clamp012 (a - 1) then (1 / 2 : ℝ) else 0) +
      (if clamp012 (2 - a) < t then (1 / 2 : ℝ) else 0) := by
  unfold R
  have h1 : (if t < a then (1 / 2 : ℝ) else 0) = if t < clamp012 a then 1 / 2 else 0 :=
    if_congr (lt_iff_lt_clamp ht0 ht1) rfl rfl
  have h2 : (if 1 - a < t then (1 / 2 : ℝ) else 0) = if clamp012 (1 - a) < t then 1 / 2 else 0 :=
    if_congr (gt_iff_gt_clamp ht0 ht1) rfl rfl
  have h3 : (if t < a - 1 then (1 / 2 : ℝ) else 0) = if t < clamp012 (a - 1) then 1 / 2 else 0 :=
    if_congr (lt_iff_lt_clamp ht0 ht1) rfl rfl
  have h4 : (if 2 - a < t then (1 / 2 : ℝ) else 0) = if clamp012 (2 - a) < t then 1 / 2 else 0 :=
    if_congr (gt_iff_gt_clamp ht0 ht1) rfl rfl
  rw [h1, h2, h3, h4]

lemma R_cases {a t : ℝ} (ht0 : 0 < t) (ht1 : t < 1 / 2) :
    (a < t → R a t = 0) ∧
    (t < a ∧ a < 1 - t → R a t = 1 / 2) ∧
    (1 - t < a ∧ a < 1 + t → R a t = 1) ∧
    (1 + t < a ∧ a < 2 - t → R a t = 3 / 2) ∧
    (2 - t < a → R a t = 2) ∧
    (1 - t < a → 1 ≤ R a t) ∧
    (1 + t < a → 3 / 2 ≤ R a t) ∧
    (t < a → 1 / 2 ≤ R a t) := by
  unfold R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;> split_ifs <;> linarith

lemma getD_eq_getElem_of_lt {L : List ℝ} {k : ℕ} (hk : k < L.length) :
    L.getD k 0 = L[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]

lemma sum_sub_eq_last_sub_first (L : List ℝ) (hL : 1 ≤ L.length) :
    ∑ i : Fin (L.length - 1), (L.getD (i.val + 1) 0 - L.getD i.val 0) =
      L.getD (L.length - 1) 0 - L.getD 0 0 := by
  induction L with
  | nil => simp at hL
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b t' =>
      change ∑ i : Fin (t'.length + 1),
        ((a :: b :: t').getD (i.val + 1) 0 - (a :: b :: t').getD i.val 0) =
        (a :: b :: t').getD (t'.length + 1) 0 - (a :: b :: t').getD 0 0
      rw [Fin.sum_univ_succ]
      have ih' := ih (by simp)
      simp only [List.length_cons, Nat.add_sub_cancel] at ih'
      have h0 : (a :: b :: t').getD 0 0 = a := rfl
      have h1 : (a :: b :: t').getD 1 0 = b := rfl
      have hstep : ∀ i : Fin t'.length,
          (a :: b :: t').getD (i.val + 1 + 1) 0 - (a :: b :: t').getD (i.val + 1) 0 =
          (b :: t').getD (i.val + 1) 0 - (b :: t').getD i.val 0 := fun _ => rfl
      simp only [Fin.val_zero, Fin.val_succ, h0, h1, hstep]
      erw [ih']
      have hb0 : (b :: t').getD 0 0 = b := rfl
      have hlast : (a :: b :: t').getD (t'.length + 1) 0 = (b :: t').getD t'.length 0 := rfl
      rw [hb0, hlast]
      ring

lemma sum_lt_of_sorted_aux (L : List ℝ) (hsort : L.Pairwise (· < ·))
    (c : ℝ) (hc : c ∈ L) :
    ∑ i : Fin (L.length - 1),
      (L.getD (i.val + 1) 0 - L.getD i.val 0) *
        (if (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < c then (1 : ℝ) else 0) =
      c - L.getD 0 0 := by
  induction L with
  | nil => simp at hc
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.mem_singleton] at hc
      subst c
      simp
    | cons b t' =>
      have hsort_tail : (b :: t').Pairwise (· < ·) := (List.pairwise_cons.mp hsort).2
      have hab : a < b := (List.pairwise_cons.mp hsort).1 b (by simp)
      change ∑ i : Fin (t'.length + 1),
        ((a :: b :: t').getD (i.val + 1) 0 - (a :: b :: t').getD i.val 0) *
          (if ((a :: b :: t').getD i.val 0 + (a :: b :: t').getD (i.val + 1) 0) / 2 < c then 1 else 0) =
        c - (a :: b :: t').getD 0 0
      rw [Fin.sum_univ_succ]
      have hfirst0 : (a :: b :: t').getD 0 0 = a := rfl
      have hfirst1 : (a :: b :: t').getD 1 0 = b := rfl
      have hstep : ∀ i : Fin t'.length,
          ((a :: b :: t').getD (i.val + 1 + 1) 0 - (a :: b :: t').getD (i.val + 1) 0) *
            (if ((a :: b :: t').getD (i.val + 1) 0 + (a :: b :: t').getD (i.val + 1 + 1) 0) / 2 < c then (1 : ℝ) else 0) =
          ((b :: t').getD (i.val + 1) 0 - (b :: t').getD i.val 0) *
            (if ((b :: t').getD i.val 0 + (b :: t').getD (i.val + 1) 0) / 2 < c then (1 : ℝ) else 0) :=
        fun _ => rfl
      simp only [Fin.val_zero, Fin.val_succ, hfirst0, hfirst1, hstep]
      rcases List.mem_cons.mp hc with rfl | hct
      · have hneg : ¬ ((c + b) / 2 < c) := by linarith
        have hzero : ∀ i : Fin t'.length,
            ((b :: t').getD (i.val + 1) 0 - (b :: t').getD i.val 0) *
              (if ((b :: t').getD i.val 0 + (b :: t').getD (i.val + 1) 0) / 2 < c then (1 : ℝ) else 0) = 0 := by
          intro i
          have h1 : b ≤ (b :: t').getD i.val 0 := by
            rcases Nat.eq_zero_or_pos i.val with hi | hi
            · simp [hi]
            · rw [getD_eq_getElem_of_lt (by simp)]
              obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
              simp only [hk, List.getElem_cons_succ]
              exact le_of_lt ((List.pairwise_cons.mp hsort_tail).1 _ (List.getElem_mem (by omega)))
          have h2 : b < (b :: t').getD (i.val + 1) 0 := by
            rw [getD_eq_getElem_of_lt (by simp)]
            exact (List.pairwise_cons.mp hsort_tail).1 _ (List.getElem_mem i.isLt)
          have hlt : ¬ (((b :: t').getD i.val 0 + (b :: t').getD (i.val + 1) 0) / 2 < c) := by linarith
          simp only [hlt, ↓reduceIte, mul_zero]
        simp only [hneg, ↓reduceIte, mul_zero, zero_add]
        rw [sub_self]
        exact Finset.sum_eq_zero (fun i _ => hzero i)
      · have hb_le_c : b ≤ c := by
          rcases List.mem_cons.mp hct with rfl | hct'
          · exact le_rfl
          · exact le_of_lt ((List.pairwise_cons.mp hsort_tail).1 c hct')
        have hpos : (a + b) / 2 < c := by linarith
        simp only [hpos, ↓reduceIte, mul_one]
        have ih' := ih hsort_tail hct
        simp only [List.length_cons] at ih'
        erw [ih']
        have hb0 : (b :: t').getD 0 0 = b := rfl
        rw [hb0]
        ring

lemma sum_lt_of_sorted (L : List ℝ) (hsort : L.Pairwise (· < ·)) (h0 : L.head? = some 0)
    (c : ℝ) (hc : c ∈ L) :
    ∑ i : Fin (L.length - 1),
      (L.getD (i.val + 1) 0 - L.getD i.val 0) *
        (if (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < c then (1 : ℝ) else 0) = c := by
  have hL0 : L.getD 0 0 = 0 := by
    cases L with
    | nil => simp at hc
    | cons a t => simp only [List.head?_cons, Option.some.injEq] at h0; simpa using h0
  rw [sum_lt_of_sorted_aux L hsort c hc, hL0, sub_zero]

lemma sum_gt_of_sorted (L : List ℝ) (hsort : L.Pairwise (· < ·)) (h0 : L.head? = some 0)
    (hlast : L.getLast? = some (1 / 2)) (c : ℝ) (hc : c ∈ L) :
    ∑ i : Fin (L.length - 1),
      (L.getD (i.val + 1) 0 - L.getD i.val 0) *
        (if c < (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 then (1 : ℝ) else 0) =
      1 / 2 - c := by
  have hlen : 1 ≤ L.length := by
    cases L with
    | nil => simp at hc
    | cons _ _ => simp
  have hL0 : L.getD 0 0 = 0 := by
    cases L with
    | nil => simp at h0
    | cons a t => simp only [List.head?_cons, Option.some.injEq] at h0; simpa using h0
  have hLlast : L.getD (L.length - 1) 0 = 1 / 2 := by
    rw [List.getLast?_eq_getElem?] at hlast
    have hlt : L.length - 1 < L.length := Nat.sub_lt hlen Nat.one_pos
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hlast
    rw [getD_eq_getElem_of_lt hlt, hlast]
  have htot := sum_sub_eq_last_sub_first L hlen
  rw [hL0, hLlast] at htot
  have hlt := sum_lt_of_sorted L hsort h0 c hc
  have hne : ∀ i : Fin (L.length - 1),
      (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 ≠ c := by
    intro i heq
    rw [getD_eq_getElem_of_lt (by omega), getD_eq_getElem_of_lt (by omega)] at heq
    have hstep : L[i.val] < L[i.val + 1] :=
      List.pairwise_iff_getElem.mp hsort i.val (i.val + 1) (by omega) (by omega) (by omega)
    have ha : L[i.val] < c := by linarith
    have hb : c < L[i.val + 1] := by linarith
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.mp hc
    rcases lt_trichotomy k i.val with hki | rfl | hki
    · have := List.pairwise_iff_getElem.mp hsort k i.val hk (by omega) hki; linarith
    · linarith
    · have hge : i.val + 1 ≤ k := hki
      rcases eq_or_lt_of_le hge with rfl | hlt_k
      · linarith
      · have := List.pairwise_iff_getElem.mp hsort (i.val + 1) k (by omega) hk hlt_k; linarith
  have hsplit : ∀ i : Fin (L.length - 1),
      (L.getD (i.val + 1) 0 - L.getD i.val 0) *
        (if c < (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 then (1 : ℝ) else 0) +
      (L.getD (i.val + 1) 0 - L.getD i.val 0) *
        (if (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < c then (1 : ℝ) else 0) =
      L.getD (i.val + 1) 0 - L.getD i.val 0 := by
    intro i
    rcases lt_or_gt_of_ne (hne i) with h1 | h2
    · have h1' : ¬ (c < (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2) := by linarith
      simp only [h1, h1', ↓reduceIte]; ring
    · have h2' : ¬ ((L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < c) := by linarith
      simp only [h2, h2', ↓reduceIte]; ring
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hsplit i)
  rw [Finset.sum_add_distrib, htot, hlt] at hsum
  linarith

lemma sum_R_eq (L : List ℝ) (hsort : L.Pairwise (· < ·)) (h0 : L.head? = some 0)
    (hlast : L.getLast? = some (1 / 2))
    {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (hc1 : clamp012 a ∈ L) (hc2 : clamp012 (1 - a) ∈ L)
    (hc3 : clamp012 (a - 1) ∈ L) (hc4 : clamp012 (2 - a) ∈ L) :
    ∑ i : Fin (L.length - 1),
      (2 * (L.getD (i.val + 1) 0 - L.getD i.val 0)) *
        R a ((L.getD i.val 0 + L.getD (i.val + 1) 0) / 2) = a := by
  have hlen : 1 ≤ L.length := by
    cases L with
    | nil => simp at hc1
    | cons _ _ => simp
  have hL0 : L.getD 0 0 = 0 := by
    cases L with
    | nil => simp at h0
    | cons x t => simp only [List.head?_cons, Option.some.injEq] at h0; simpa using h0
  have hLlast : L.getD (L.length - 1) 0 = 1 / 2 := by
    rw [List.getLast?_eq_getElem?] at hlast
    have hlt : L.length - 1 < L.length := Nat.sub_lt hlen Nat.one_pos
    rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hlast
    rw [getD_eq_getElem_of_lt hlt, hlast]
  have ht_bounds : ∀ i : Fin (L.length - 1),
      0 < (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 ∧
      (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < 1 / 2 := by
    intro i
    have hstep : L.getD i.val 0 < L.getD (i.val + 1) 0 := by
      rw [getD_eq_getElem_of_lt (by omega), getD_eq_getElem_of_lt (by omega)]
      exact List.pairwise_iff_getElem.mp hsort i.val (i.val + 1) (by omega) (by omega) (by omega)
    have hlo : 0 ≤ L.getD i.val 0 := by
      rcases Nat.eq_zero_or_pos i.val with h | h
      · rw [h, hL0]
      · rw [getD_eq_getElem_of_lt (by omega)]
        rw [getD_eq_getElem_of_lt (by omega)] at hL0
        have := List.pairwise_iff_getElem.mp hsort 0 i.val (by omega) (by omega) h
        linarith
    have hhi : L.getD (i.val + 1) 0 ≤ 1 / 2 := by
      rcases eq_or_lt_of_le (show i.val + 1 ≤ L.length - 1 by omega) with h | h
      · rw [h, hLlast]
      · rw [getD_eq_getElem_of_lt (by omega)]
        rw [getD_eq_getElem_of_lt (by omega)] at hLlast
        have := List.pairwise_iff_getElem.mp hsort (i.val + 1) (L.length - 1) (by omega) (by omega) h
        linarith
    constructor <;> linarith
  have hrw : ∀ i : Fin (L.length - 1),
      (2 * (L.getD (i.val + 1) 0 - L.getD i.val 0)) *
        R a ((L.getD i.val 0 + L.getD (i.val + 1) 0) / 2) =
      (L.getD (i.val + 1) 0 - L.getD i.val 0) * (if (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < clamp012 a then 1 else 0) +
      (L.getD (i.val + 1) 0 - L.getD i.val 0) * (if clamp012 (1 - a) < (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 then 1 else 0) +
      (L.getD (i.val + 1) 0 - L.getD i.val 0) * (if (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 < clamp012 (a - 1) then 1 else 0) +
      (L.getD (i.val + 1) 0 - L.getD i.val 0) * (if clamp012 (2 - a) < (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2 then 1 else 0) := by
    intro i
    obtain ⟨ht0, ht1⟩ := ht_bounds i
    rw [R_eq_sum_clamped ht0 ht1]
    split_ifs <;> ring
  simp_rw [hrw, Finset.sum_add_distrib]
  rw [sum_lt_of_sorted L hsort h0 _ hc1,
      sum_gt_of_sorted L hsort h0 hlast _ hc2,
      sum_lt_of_sorted L hsort h0 _ hc3,
      sum_gt_of_sorted L hsort h0 hlast _ hc4]
  exact R_eval_sum_identity ha0 ha2

end Helpers

end PEqualNP.Outside.L_lib_963

open PEqualNP.Outside.L_lib_963 in
theorem PEqualNP.Outside.L_lib_963 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let V := Fin n
      let nbr := fun (I : Finset V) =>
        (Finset.univ : Finset V).filter (fun v => ∃ u ∈ I, G.Adj u v)
      let indep := fun (I : Finset V) => ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v
      let block := fun (y : V → ℝ) => (∀ u, 0 ≤ y u) ∧
        (∀ u v, u ≠ v → 1 ≤ y u + y v) ∧ ∀ u v, G.Adj u v → 2 ≤ y u + y v
      let option := fun (x : V → ℝ) =>
        (∃ I : Finset V, indep I ∧ ∀ u,
          x u = if u ∈ I then 1/2 else if u ∈ nbr I then 3/2 else 1) ∨
        ∃ v : V, ∀ u, x u = if u = v then 0 else if G.Adj v u then 2 else 1
      (∀ x : V → ℝ, option x → block x) ∧
      ∀ y : V → ℝ, block y ↔
        ∃ (m : ℕ) (w : Fin m → ℝ) (x : Fin m → V → ℝ),
          (∀ i, 0 ≤ w i ∧ option (x i)) ∧ (∑ i, w i) = 1 ∧
          ∀ u, (∑ i, w i * x i u) ≤ y u := by
  intro n G _ V nbr indep block option
  have h_opt_block : ∀ x : V → ℝ, option x → block x := by
    rintro x (⟨I, hI, hx⟩ | ⟨v0, hx⟩)
    · refine ⟨fun u => ?_, fun u v huv => ?_, fun u v huv => ?_⟩
      · rw [hx u]
        split_ifs <;> norm_num
      · rw [hx u, hx v]
        split_ifs <;> norm_num
      · rw [hx u, hx v]
        by_cases hu : u ∈ I
        · have hv : v ∉ I := fun hv => hI u hu v hv huv
          have hvn : v ∈ nbr I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, u, hu, huv⟩
          simp only [hu, hv, hvn, ↓reduceIte]
          norm_num
        · by_cases hv : v ∈ I
          · have hun : u ∈ nbr I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, v, hv, huv.symm⟩
            simp only [hu, hv, hun, ↓reduceIte]
            norm_num
          · simp only [hu, hv, ↓reduceIte]
            split_ifs <;> norm_num
    · refine ⟨fun u => ?_, fun u v huv => ?_, fun u v huv => ?_⟩
      · rw [hx u]
        split_ifs <;> norm_num
      · rw [hx u, hx v]
        by_cases hu : u = v0 <;> by_cases hv : v = v0
        · exact (huv (hu.trans hv.symm)).elim
        · simp only [hu, hv, ↓reduceIte]; split_ifs <;> norm_num
        · simp only [hu, hv, ↓reduceIte]; split_ifs <;> norm_num
        · simp only [hu, hv, ↓reduceIte]; split_ifs <;> norm_num
      · rw [hx u, hx v]
        by_cases hu : u = v0
        · subst u
          simp only [↓reduceIte, huv.ne.symm, huv]
          norm_num
        · by_cases hv : v = v0
          · subst v
            simp only [hu, ↓reduceIte, huv.symm]
            norm_num
          · simp only [hu, hv, ↓reduceIte]
            split_ifs <;> norm_num
  refine ⟨h_opt_block, fun y => ⟨?_, ?_⟩⟩
  · intro hy
    classical
    let z : V → ℝ := fun u => min (y u) 2
    have hz_nonneg : ∀ u, 0 ≤ z u := fun u => le_min (hy.1 u) (by norm_num)
    have hz_le_two : ∀ u, z u ≤ 2 := fun u => min_le_right _ _
    have hz_le_y : ∀ u, z u ≤ y u := fun u => min_le_left _ _
    have hz_pair : ∀ u v, u ≠ v → 1 ≤ z u + z v := by
      intro u v huv
      have h1 := hy.2.1 u v huv
      have h2 := hy.1 u
      have h3 := hy.1 v
      simp only [z]
      rcases le_total (y u) 2 with hu | hu <;> rcases le_total (y v) 2 with hv | hv
      · rw [min_eq_left hu, min_eq_left hv]; exact h1
      · rw [min_eq_left hu, min_eq_right hv]; linarith
      · rw [min_eq_right hu, min_eq_left hv]; linarith
      · rw [min_eq_right hu, min_eq_right hv]; norm_num
    have hz_adj : ∀ u v, G.Adj u v → 2 ≤ z u + z v := by
      intro u v huv
      have h1 := hy.2.2 u v huv
      have h2 := hy.1 u
      have h3 := hy.1 v
      simp only [z]
      rcases le_total (y u) 2 with hu | hu <;> rcases le_total (y v) 2 with hv | hv
      · rw [min_eq_left hu, min_eq_left hv]; exact h1
      · rw [min_eq_left hu, min_eq_right hv]; linarith
      · rw [min_eq_right hu, min_eq_left hv]; linarith
      · rw [min_eq_right hu, min_eq_right hv]; norm_num
    let S : Finset ℝ :=
      insert (0 : ℝ) (insert (1 / 2 : ℝ)
        ((Finset.univ : Finset V).biUnion fun u =>
          {clamp012 (z u), clamp012 (1 - z u), clamp012 (z u - 1), clamp012 (2 - z u)}))
    let L : List ℝ := S.sort (· ≤ ·)
    have hsort : L.Pairwise (· < ·) := by
      have hs := S.pairwise_sort (· ≤ ·)
      have hnd := S.sort_nodup (· ≤ ·)
      rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      have hle := List.pairwise_iff_getElem.mp hs i j hi hj hij
      have hne : L[i] ≠ L[j] := fun heq => by
        have := (List.nodup_iff_injective_getElem.mp hnd) (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) heq
        exact absurd (congrArg Fin.val this) (Nat.ne_of_lt hij)
      exact lt_of_le_of_ne hle hne
    have hS0 : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
    have hS12 : (1 / 2 : ℝ) ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hS_bounds : ∀ c ∈ S, 0 ≤ c ∧ c ≤ 1 / 2 := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · norm_num
      · rcases Finset.mem_insert.mp hc with rfl | hc
        · norm_num
        · obtain ⟨u, _, hcu⟩ := Finset.mem_biUnion.mp hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hcu
          rcases hcu with rfl | rfl | rfl | rfl <;>
            exact ⟨clamp012_nonneg _, clamp012_le_half _⟩
    have hL_mem : ∀ c, c ∈ L ↔ c ∈ S := fun c => Finset.mem_sort _
    have hL_ne : L ≠ [] := by
      intro h
      have : (0 : ℝ) ∈ L := (hL_mem 0).mpr hS0
      rw [h] at this
      simp at this
    have h0 : L.head? = some 0 := by
      cases hL : L with
      | nil => exact (hL_ne hL).elim
      | cons a t =>
        simp only [List.head?_cons, Option.some.injEq]
        have ha_mem : a ∈ L := by rw [hL]; simp
        have h0_mem : (0 : ℝ) ∈ L := (hL_mem 0).mpr hS0
        have ha_ge : 0 ≤ a := (hS_bounds a ((hL_mem a).mp ha_mem)).1
        rw [hL] at h0_mem
        rcases List.mem_cons.mp h0_mem with h0a | h0t
        · exact h0a.symm
        · have hsort' : (a :: t).Pairwise (· < ·) := hL ▸ hsort
          have halt : a < 0 := (List.pairwise_cons.mp hsort').1 0 h0t
          linarith
    have hlast : L.getLast? = some (1 / 2) := by
      rw [List.getLast?_eq_getElem?]
      have hlen : 0 < L.length := List.length_pos_of_ne_nil hL_ne
      have hlt : L.length - 1 < L.length := Nat.sub_lt hlen Nat.one_pos
      rw [List.getElem?_eq_getElem hlt, Option.some.injEq]
      have hlast_mem : L[L.length - 1] ∈ L := List.getElem_mem hlt
      have hlast_le : L[L.length - 1] ≤ 1 / 2 := (hS_bounds _ ((hL_mem _).mp hlast_mem)).2
      have h12_mem : (1 / 2 : ℝ) ∈ L := (hL_mem (1 / 2)).mpr hS12
      obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp h12_mem
      rcases eq_or_lt_of_le (Nat.le_pred_of_lt hk) with hk_eq | hk_lt
      · rw [← hkeq]
        congr 1
        rw [← Nat.pred_eq_sub_one, hk_eq]
      · have := List.pairwise_iff_getElem.mp hsort k (L.length - 1) hk hlt hk_lt
        linarith
    have hL_len : 2 ≤ L.length := by
      have h0L : (0 : ℝ) ∈ L := (hL_mem 0).mpr hS0
      have h12L : (1 / 2 : ℝ) ∈ L := (hL_mem (1 / 2)).mpr hS12
      cases hL : L with
      | nil => rw [hL] at h0L; simp at h0L
      | cons a t =>
        cases ht : t with
        | nil =>
          rw [hL, ht] at h0L h12L
          simp only [List.mem_singleton] at h0L h12L
          linarith
        | cons b t' => simp
    let m := L.length - 1
    let w : Fin m → ℝ := fun i => 2 * (L.getD (i.val + 1) 0 - L.getD i.val 0)
    let t : Fin m → ℝ := fun i => (L.getD i.val 0 + L.getD (i.val + 1) 0) / 2
    have hw_nonneg : ∀ i, 0 ≤ w i := by
      intro i
      dsimp only [w]
      rw [getD_eq_getElem_of_lt (by omega), getD_eq_getElem_of_lt (by omega)]
      have hstep : L[i.val] < L[i.val + 1] :=
        List.pairwise_iff_getElem.mp hsort i.val (i.val + 1) (by omega) (by omega) (by omega)
      linarith
    have ht_bounds : ∀ i, 0 < t i ∧ t i < 1 / 2 := by
      intro i
      dsimp only [t]
      have hstep : L.getD i.val 0 < L.getD (i.val + 1) 0 := by
        rw [getD_eq_getElem_of_lt (by omega), getD_eq_getElem_of_lt (by omega)]
        exact List.pairwise_iff_getElem.mp hsort i.val (i.val + 1) (by omega) (by omega) (by omega)
      have hL0 : L.getD 0 0 = 0 := by
        cases hL : L with
        | nil => exact (hL_ne hL).elim
        | cons a _ => simp only [hL, List.head?_cons, Option.some.injEq] at h0; simpa using h0
      have hLlast : L.getD (L.length - 1) 0 = 1 / 2 := by
        rw [List.getLast?_eq_getElem?] at hlast
        have hlt : L.length - 1 < L.length := Nat.sub_lt (by omega) Nat.one_pos
        rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hlast
        rw [getD_eq_getElem_of_lt hlt, hlast]
      have hlo : 0 ≤ L.getD i.val 0 := by
        rcases Nat.eq_zero_or_pos i.val with h | h
        · rw [h, hL0]
        · rw [getD_eq_getElem_of_lt (by omega)]
          rw [getD_eq_getElem_of_lt (by omega)] at hL0
          have := List.pairwise_iff_getElem.mp hsort 0 i.val (by omega) (by omega) h
          linarith
      have hhi : L.getD (i.val + 1) 0 ≤ 1 / 2 := by
        rcases eq_or_lt_of_le (show i.val + 1 ≤ L.length - 1 by omega) with h | h
        · rw [h, hLlast]
        · rw [getD_eq_getElem_of_lt (by omega)]
          rw [getD_eq_getElem_of_lt (by omega)] at hLlast
          have := List.pairwise_iff_getElem.mp hsort (i.val + 1) (L.length - 1) (by omega) (by omega) h
          linarith
      constructor <;> linarith
    have ht_not_mem : ∀ i, t i ∉ L := by
      intro i hmem
      obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hmem
      have hstep : L[i.val] < L[i.val + 1] :=
        List.pairwise_iff_getElem.mp hsort i.val (i.val + 1) (by omega) (by omega) (by omega)
      have hteq : t i = (L[i.val] + L[i.val + 1]) / 2 := by
        dsimp only [t]
        rw [getD_eq_getElem_of_lt (by omega), getD_eq_getElem_of_lt (by omega)]
      rcases lt_trichotomy k i.val with hki | rfl | hki
      · have := List.pairwise_iff_getElem.mp hsort k i.val hk (by omega) hki; linarith
      · linarith
      · rcases eq_or_lt_of_le (show i.val + 1 ≤ k by omega) with rfl | hlt_k
        · linarith
        · have := List.pairwise_iff_getElem.mp hsort (i.val + 1) k (by omega) hk hlt_k; linarith
    have hz_ne_breaks : ∀ (i : Fin m) (u : V),
        z u ≠ t i ∧ z u ≠ 1 - t i ∧ z u ≠ 1 + t i ∧ z u ≠ 2 - t i := by
      intro i u
      obtain ⟨ht0, ht1⟩ := ht_bounds i
      have hne := ht_not_mem i
      have hmemS : ∀ c, c ∈ ({clamp012 (z u), clamp012 (1 - z u), clamp012 (z u - 1), clamp012 (2 - z u)} : Finset ℝ) → c ∈ L := by
        intro c hc
        exact (hL_mem c).mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hc⟩)))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro heq; apply hne; apply hmemS
        have hc : clamp012 (z u) = t i := by
          unfold clamp012; rw [heq, min_eq_right (by linarith), max_eq_right (by linarith)]
        rw [← hc]; simp
      · intro heq; apply hne; apply hmemS
        have hc : clamp012 (1 - z u) = t i := by
          unfold clamp012; rw [show 1 - z u = t i by linarith, min_eq_right (by linarith), max_eq_right (by linarith)]
        rw [← hc]; simp
      · intro heq; apply hne; apply hmemS
        have hc : clamp012 (z u - 1) = t i := by
          unfold clamp012; rw [show z u - 1 = t i by linarith, min_eq_right (by linarith), max_eq_right (by linarith)]
        rw [← hc]; simp
      · intro heq; apply hne; apply hmemS
        have hc : clamp012 (2 - z u) = t i := by
          unfold clamp012; rw [show 2 - z u = t i by linarith, min_eq_right (by linarith), max_eq_right (by linarith)]
        rw [← hc]; simp
    let x : Fin m → V → ℝ := fun i =>
      if h : ∃ v0 : V, z v0 < t i then
        let v0 := Classical.choose h
        fun u => if u = v0 then 0 else if G.Adj v0 u then 2 else 1
      else
        let I : Finset V := Finset.univ.filter (fun u => z u < 1 - t i)
        fun u => if u ∈ I then 1 / 2 else if u ∈ nbr I then 3 / 2 else 1
    refine ⟨m, w, x, fun i => ⟨hw_nonneg i, ?_⟩, ?_, fun u => ?_⟩
    · dsimp only [x]
      split_ifs with h
      · exact Or.inr ⟨Classical.choose h, fun _ => rfl⟩
      · refine Or.inl ⟨Finset.univ.filter (fun u => z u < 1 - t i), ?_, fun _ => rfl⟩
        intro u hu v hv huv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
        have := hz_adj u v huv
        have := (ht_bounds i).1
        linarith
    · have htot := sum_sub_eq_last_sub_first L (by omega)
      have hL0 : L.getD 0 0 = 0 := by
        cases hL : L with
        | nil => exact (hL_ne hL).elim
        | cons a _ => simp only [hL, List.head?_cons, Option.some.injEq] at h0; simpa using h0
      have hLlast : L.getD (L.length - 1) 0 = 1 / 2 := by
        rw [List.getLast?_eq_getElem?] at hlast
        have hlt : L.length - 1 < L.length := Nat.sub_lt (by omega) Nat.one_pos
        rw [List.getElem?_eq_getElem hlt, Option.some.injEq] at hlast
        rw [getD_eq_getElem_of_lt hlt, hlast]
      rw [hL0, hLlast] at htot
      dsimp only [w]
      rw [← Finset.mul_sum, htot]
      norm_num
    · have hle_R : ∀ i : Fin m, x i u ≤ R (z u) (t i) := by
        intro i
        obtain ⟨ht0, ht1⟩ := ht_bounds i
        obtain ⟨hne1, hne2, hne3, hne4⟩ := hz_ne_breaks i u
        have hRc := R_cases ht0 ht1 (a := z u)
        dsimp only [x]
        split_ifs with h
        · have hv0 : z (Classical.choose h) < t i := Classical.choose_spec h
          dsimp only
          split_ifs with hu0 hadj
          · unfold R; split_ifs <;> norm_num
          · have h2 := hz_adj _ u hadj
            exact le_of_eq (hRc.2.2.2.2.1 (by linarith)).symm
          · have h1 := hz_pair _ u (fun heq => hu0 heq.symm)
            exact hRc.2.2.2.2.2.1 (by linarith)
        · push Not at h
          have hzu_ge : t i < z u := lt_of_le_of_ne (h u) (Ne.symm hne1)
          dsimp only
          split_ifs with huI hunbr
          · have hzu_lt : z u < 1 - t i := (Finset.mem_filter.mp huI).2
            exact le_of_eq (hRc.2.1 ⟨hzu_ge, hzu_lt⟩).symm
          · obtain ⟨v, hvI, huv⟩ := (Finset.mem_filter.mp hunbr).2
            have hzv_lt : z v < 1 - t i := (Finset.mem_filter.mp hvI).2
            have hadj := hz_adj v u huv
            exact hRc.2.2.2.2.2.2.1 (by linarith)
          · have hzu_nlt : ¬ (z u < 1 - t i) := fun hc => huI (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
            have hzu_gt : 1 - t i < z u := lt_of_le_of_ne (not_lt.mp hzu_nlt) hne2.symm
            exact hRc.2.2.2.2.2.1 hzu_gt
      calc ∑ i : Fin m, w i * x i u
          ≤ ∑ i : Fin m, w i * R (z u) (t i) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle_R i) (hw_nonneg i)
        _ = z u := by
            have hmemS : ∀ c, c ∈ ({clamp012 (z u), clamp012 (1 - z u), clamp012 (z u - 1), clamp012 (2 - z u)} : Finset ℝ) → c ∈ L :=
              fun c hc => (hL_mem c).mpr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hc⟩)))
            exact sum_R_eq L hsort h0 hlast (hz_nonneg u) (hz_le_two u)
              (hmemS _ (by simp)) (hmemS _ (by simp)) (hmemS _ (by simp)) (hmemS _ (by simp))
        _ ≤ y u := hz_le_y u
  · rintro ⟨m, w, x, hwx, hw1, hle⟩
    have hxb : ∀ i, block (x i) := fun i => h_opt_block (x i) (hwx i).2
    refine ⟨fun u => ?_, fun u v huv => ?_, fun u v huv => ?_⟩
    · have h0 : (0 : ℝ) ≤ ∑ i, w i * x i u :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hwx i).1 ((hxb i).1 u)
      linarith [hle u]
    · have h1 : ∑ i, w i * (1 : ℝ) ≤ ∑ i, w i * (x i u + x i v) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left ((hxb i).2.1 u v huv) (hwx i).1
      rw [← Finset.sum_mul, hw1, one_mul] at h1
      have h2 : ∑ i, w i * (x i u + x i v) =
          (∑ i, w i * x i u) + (∑ i, w i * x i v) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      linarith [hle u, hle v]
    · have h1 : ∑ i, w i * (2 : ℝ) ≤ ∑ i, w i * (x i u + x i v) :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left ((hxb i).2.2 u v huv) (hwx i).1
      rw [← Finset.sum_mul, hw1, one_mul] at h1
      have h2 : ∑ i, w i * (x i u + x i v) =
          (∑ i, w i * x i u) + (∑ i, w i * x i v) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      linarith [hle u, hle v]
