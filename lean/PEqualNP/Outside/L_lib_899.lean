import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_899

open Finset

section foldl
variable {ι : Type} (c : ι → Prop) [DecidablePred c] (r : ι → ℚ)

theorem foldl_cases (L : List ι) (b : ℚ) :
    L.foldl (fun best i => if c i then best else max best (r i)) b = b ∨
    ∃ i ∈ L, ¬ c i ∧ L.foldl (fun best i => if c i then best else max best (r i)) b = r i := by
  induction L generalizing b with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons]
    rcases ih (if c x then b else max b (r x)) with h | ⟨i, hi, hci, h⟩
    · by_cases hx : c x
      · left; rw [h, if_pos hx]
      · rw [if_neg hx] at h ⊢
        rcases max_choice b (r x) with h2 | h2
        · left; rw [h, h2]
        · right; exact ⟨x, by simp, hx, by rw [h, h2]⟩
    · right; exact ⟨i, List.mem_cons_of_mem _ hi, hci, h⟩

theorem le_foldl (L : List ι) (b : ℚ) :
    b ≤ L.foldl (fun best i => if c i then best else max best (r i)) b ∧
    ∀ i ∈ L, ¬ c i → r i ≤ L.foldl (fun best i => if c i then best else max best (r i)) b := by
  induction L generalizing b with
  | nil => simp
  | cons x L ih =>
    rw [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (if c x then b else max b (r x))
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ h1
      split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · intro i hi hci
      rcases List.mem_cons.1 hi with rfl | hi
      · refine le_trans ?_ h1
        rw [if_neg hci]; exact le_max_right _ _
      · exact h2 i hi hci

theorem foldl_le (L : List ι) (b B : ℚ) (hb : b ≤ B) (hr : ∀ i ∈ L, ¬ c i → r i ≤ B) :
    L.foldl (fun best i => if c i then best else max best (r i)) b ≤ B := by
  rcases foldl_cases c r L b with h | ⟨i, hi, hci, h⟩
  · rw [h]; exact hb
  · rw [h]; exact hr i hi hci

end foldl

section defs
variable {n m : ℕ} (M : Fin n → Fin m → ℕ) (w : Fin m → ℕ)

def colv (j : Fin m) : ℚ :=
  (List.finRange n).foldl (fun (best : ℚ) i =>
      let other := ∑ a : Fin m, if a = j then 0 else M i a * w a
      if M i j = 0 then best else max best ((w j : ℚ) / ((w j : ℚ) + other))) 0

def scoreF : ℚ := ∑ j : Fin m, colv M w j

def other (i : Fin n) (j : Fin m) : ℕ := ∑ a : Fin m, if a = j then 0 else M i a * w a

def rat (i : Fin n) (j : Fin m) : ℚ := (w j : ℚ) / ((w j : ℚ) + (other M w i j : ℚ))

def pivP (p : Equiv.Perm (Fin m)) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => ∃ i : Fin n,
      0 < M i j ∧ ∀ a : Fin m, p a < p j → M i a = 0)).card

def den (i : Fin n) (C : Finset (Fin m)) : ℕ := ∑ a ∈ C.filter (fun a => M i a ≠ 0), w a

def pv (f : Fin m → ℕ) (C : Finset (Fin m)) (R : Finset (Fin n)) : ℕ :=
  (C.filter (fun j => ∃ i ∈ R, M i j ≠ 0 ∧ ∀ a ∈ C, f a < f j → M i a = 0)).card

theorem colv_cases (j : Fin m) :
    colv M w j = 0 ∨ ∃ i, M i j ≠ 0 ∧ colv M w j = rat M w i j := by
  rcases foldl_cases (fun i => M i j = 0) (fun i => rat M w i j) (List.finRange n) 0 with
    h | ⟨i, -, hi, h⟩
  · left; exact h
  · right; exact ⟨i, hi, h⟩

theorem colv_ge (j : Fin m) (i : Fin n) (hi : M i j ≠ 0) : rat M w i j ≤ colv M w j :=
  (le_foldl (fun i => M i j = 0) (fun i => rat M w i j) (List.finRange n) 0).2 i
    (List.mem_finRange i) hi

theorem colv_nonneg (j : Fin m) : 0 ≤ colv M w j :=
  (le_foldl (fun i => M i j = 0) (fun i => rat M w i j) (List.finRange n) 0).1

theorem colv_le (j : Fin m) (B : ℚ) (hB : 0 ≤ B) (h : ∀ i, M i j ≠ 0 → rat M w i j ≤ B) :
    colv M w j ≤ B :=
  foldl_le (fun i => M i j = 0) (fun i => rat M w i j) (List.finRange n) 0 B hB
    (fun i _ hi => h i hi)

end defs

section partC
variable {n m : ℕ} (M : Fin n → Fin m → ℕ) (w : Fin m → ℕ)

theorem den_erase (i : Fin n) (c : Fin m) (C : Finset (Fin m)) (h : M i c = 0) :
    den M w i (C.erase c) = den M w i C := by
  unfold den; congr 1; ext a; simp only [mem_filter, mem_erase]; constructor
  · rintro ⟨⟨_, ha⟩, h2⟩; exact ⟨ha, h2⟩
  · rintro ⟨ha, h2⟩; exact ⟨⟨fun e => h2 (by subst e; exact h), ha⟩, h2⟩

theorem w_le_den (i : Fin n) (j : Fin m) (C : Finset (Fin m)) (hj : j ∈ C) (hij : M i j ≠ 0) :
    w j ≤ den M w i C :=
  single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_filter.2 ⟨hj, hij⟩)

theorem per_j (hw : ∀ j, 0 < w j) (C : Finset (Fin m)) (i : Fin n) (j : Fin m) (hj : j ∈ C)
    (hij : M i j ≠ 0) :
    ∑ c ∈ C, ((w c : ℚ) / (∑ a ∈ C, (w a : ℚ))) * ((if c = j then (1:ℚ) else 0) +
      (if j ≠ c ∧ M i c = 0 then (w j : ℚ) / (den M w i (C.erase c) : ℚ) else 0))
      = (w j : ℚ) / (den M w i C : ℚ) := by
  have hd : (w j : ℚ) ≤ (den M w i C : ℚ) := by exact_mod_cast w_le_den M w i j C hj hij
  have hwj : (0:ℚ) < w j := by exact_mod_cast hw j
  have hd0 : (0:ℚ) < (den M w i C : ℚ) := lt_of_lt_of_le hwj hd
  have hsplit : (∑ a ∈ C, (w a : ℚ)) = (den M w i C : ℚ) +
      ∑ c ∈ C.filter (fun c => j ≠ c ∧ M i c = 0), (w c : ℚ) := by
    rw [← sum_filter_add_sum_filter_not C (fun a => M i a ≠ 0)]
    unfold den; push_cast
    congr 1
    apply sum_congr _ (fun _ _ => rfl)
    apply filter_congr
    intro c _
    constructor
    · intro h
      have h' : M i c = 0 := not_not.1 h
      exact ⟨fun e => hij (by subst e; exact h'), h'⟩
    · rintro ⟨_, h⟩; exact not_not.2 h
  set S := ∑ c ∈ C.filter (fun c => j ≠ c ∧ M i c = 0), (w c : ℚ) with hS
  set d := (den M w i C : ℚ) with hddef
  have hS0 : 0 ≤ S := sum_nonneg (fun _ _ => by positivity)
  calc ∑ c ∈ C, ((w c : ℚ) / (∑ a ∈ C, (w a : ℚ))) * ((if c = j then (1:ℚ) else 0) +
      (if j ≠ c ∧ M i c = 0 then (w j : ℚ) / (den M w i (C.erase c) : ℚ) else 0))
      = ∑ c ∈ C, (((w c : ℚ) / (d + S)) * (if c = j then (1:ℚ) else 0) +
        (if j ≠ c ∧ M i c = 0 then (w c : ℚ) * ((w j : ℚ) / d / (d + S)) else 0)) := by
        refine sum_congr rfl fun c _ => ?_
        rw [hsplit]
        by_cases h1 : j ≠ c ∧ M i c = 0
        · rw [if_pos h1, if_pos h1, den_erase M w i c C h1.2, ← hddef]
          ring
        · rw [if_neg h1, if_neg h1]; ring
    _ = (w j : ℚ) / (d + S) + S * ((w j : ℚ) / d / (d + S)) := by
        rw [sum_add_distrib, ← sum_filter, ← sum_mul, ← hS]
        congr 1
        simp [hj]
    _ = (w j : ℚ) / d := by
        first
          | (field_simp; ring)
          | field_simp

theorem mainC (hw : ∀ j, 0 < w j) : ∀ (C : Finset (Fin m)) (R : Finset (Fin n))
    (T : Finset (Fin m)) (g : Fin m → Fin n),
    T ⊆ C → (∀ j ∈ T, g j ∈ R ∧ M (g j) j ≠ 0) →
    ∃ f : Fin m → ℕ, Function.Injective f ∧
      ∑ j ∈ T, (w j : ℚ) / (den M w (g j) C : ℚ) ≤ (pv M f C R : ℚ) := by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
  intro R T g hTC hT
  rcases C.eq_empty_or_nonempty with hCe | hC
  · subst hCe
    refine ⟨fun a => a.val, Fin.val_injective, ?_⟩
    rw [subset_empty.1 hTC]; simp
  have hW : (0:ℚ) < ∑ a ∈ C, (w a : ℚ) := by
    obtain ⟨c, hc⟩ := hC
    exact lt_of_lt_of_le (by exact_mod_cast hw c)
      (single_le_sum (f := fun a => (w a : ℚ)) (fun a _ => by positivity) hc)
  let Q : Fin m → ℚ := fun c => ∑ j ∈ T, ((if c = j then (1:ℚ) else 0) +
      (if j ≠ c ∧ M (g j) c = 0 then (w j : ℚ) / (den M w (g j) (C.erase c) : ℚ) else 0))
  obtain ⟨c, hc, hcmax⟩ := exists_max_image C Q hC
  have key : ∑ j ∈ T, (w j : ℚ) / (den M w (g j) C : ℚ) ≤ Q c := by
    calc ∑ j ∈ T, (w j : ℚ) / (den M w (g j) C : ℚ)
        = ∑ j ∈ T, ∑ c ∈ C, ((w c : ℚ) / (∑ a ∈ C, (w a : ℚ))) * ((if c = j then (1:ℚ) else 0) +
          (if j ≠ c ∧ M (g j) c = 0 then (w j : ℚ) / (den M w (g j) (C.erase c) : ℚ)
            else 0)) := by
          refine sum_congr rfl fun j hj => ?_
          exact (per_j M w hw C (g j) j (hTC hj) (hT j hj).2).symm
      _ = ∑ c ∈ C, ((w c : ℚ) / (∑ a ∈ C, (w a : ℚ))) * Q c := by
          rw [sum_comm]; refine sum_congr rfl fun c _ => ?_; rw [mul_sum]
      _ ≤ ∑ c' ∈ C, ((w c' : ℚ) / (∑ a ∈ C, (w a : ℚ))) * Q c :=
          sum_le_sum fun c' hc' => mul_le_mul_of_nonneg_left (hcmax c' hc') (by positivity)
      _ = Q c := by rw [← sum_mul, ← sum_div, div_self hW.ne', one_mul]
  obtain ⟨f0, hf0inj, hf0⟩ := ih (C.erase c) (erase_ssubset hc) (R.filter (fun i => M i c = 0))
    (T.filter (fun j => j ≠ c ∧ M (g j) c = 0)) g
    (fun j hj => by
      simp only [mem_filter] at hj
      exact mem_erase.2 ⟨hj.2.1, hTC hj.1⟩)
    (fun j hj => by
      simp only [mem_filter] at hj
      exact ⟨mem_filter.2 ⟨(hT j hj.1).1, hj.2.2⟩, (hT j hj.1).2⟩)
  have hQ : Q c = (if c ∈ T then (1:ℚ) else 0) +
      ∑ j ∈ T.filter (fun j => j ≠ c ∧ M (g j) c = 0),
        (w j : ℚ) / (den M w (g j) (C.erase c) : ℚ) := by
    simp only [Q]
    rw [sum_add_distrib, sum_filter]
    congr 1
    simp
  let f : Fin m → ℕ := fun a => if a = c then 0 else f0 a + 1
  have hfinj : Function.Injective f := by
    intro a b h
    simp only [f] at h
    by_cases ha : a = c <;> by_cases hb : b = c
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at h; omega
    · rw [if_neg ha, if_pos hb] at h; omega
    · rw [if_neg ha, if_neg hb] at h; exact hf0inj (by omega)
  have hsub : (C.erase c).filter (fun j => ∃ i ∈ R.filter (fun i => M i c = 0), M i j ≠ 0 ∧
      ∀ a ∈ C.erase c, f0 a < f0 j → M i a = 0) ⊆
      (C.filter (fun j => ∃ i ∈ R, M i j ≠ 0 ∧ ∀ a ∈ C, f a < f j → M i a = 0)).erase c := by
    intro j hj
    simp only [mem_filter, mem_erase] at hj ⊢
    obtain ⟨⟨hjc, hjC⟩, i, ⟨hiR, hic⟩, hij, hall⟩ := hj
    refine ⟨hjc, hjC, i, hiR, hij, fun a ha hlt => ?_⟩
    by_cases hac : a = c
    · subst hac; exact hic
    · apply hall a ⟨hac, ha⟩
      simp only [f, if_neg hac, if_neg hjc] at hlt
      omega
  have hcard := card_le_card hsub
  refine ⟨f, hfinj, le_trans key ?_⟩
  rw [hQ]
  by_cases hcT : c ∈ T
  · rw [if_pos hcT]
    have hcmem : c ∈ C.filter (fun j => ∃ i ∈ R, M i j ≠ 0 ∧ ∀ a ∈ C, f a < f j → M i a = 0) := by
      refine mem_filter.2 ⟨hc, g c, (hT c hcT).1, (hT c hcT).2, fun a _ hlt => ?_⟩
      simp only [f, if_pos rfl] at hlt
      omega
    rw [card_erase_of_mem hcmem] at hcard
    have hpos := card_pos.2 ⟨c, hcmem⟩
    have : 1 + pv M f0 (C.erase c) (R.filter (fun i => M i c = 0)) ≤ pv M f C R := by
      unfold pv; omega
    have : (1:ℚ) + (pv M f0 (C.erase c) (R.filter (fun i => M i c = 0)) : ℚ) ≤ (pv M f C R : ℚ) := by
      exact_mod_cast this
    linarith
  · rw [if_neg hcT, zero_add]
    have : pv M f0 (C.erase c) (R.filter (fun i => M i c = 0)) ≤ pv M f C R := by
      unfold pv; exact hcard.trans (card_erase_le)
    have : (pv M f0 (C.erase c) (R.filter (fun i => M i c = 0)) : ℚ) ≤ (pv M f C R : ℚ) := by
      exact_mod_cast this
    linarith

theorem perm_of_inj (f : Fin m → ℕ) (hf : Function.Injective f) :
    ∃ p : Equiv.Perm (Fin m), ∀ a b, p a < p b ↔ f a < f b := by
  refine ⟨(Tuple.sort f).symm, fun a b => ?_⟩
  have hmono := Tuple.monotone_sort f
  have key : ∀ x y : Fin m, (Tuple.sort f).symm x ≤ (Tuple.sort f).symm y → f x ≤ f y := by
    intro x y h
    have := hmono h
    simpa using this
  constructor
  · intro h
    refine lt_of_le_of_ne (key a b h.le) (fun e => ?_)
    have := hf e; subst this; exact lt_irrefl _ h
  · intro h
    by_contra h'
    exact absurd (key b a (not_lt.1 h')) (not_le.2 h)

theorem pivP_eq (p : Equiv.Perm (Fin m)) (f : Fin m → ℕ) (hpf : ∀ a b, p a < p b ↔ f a < f b) :
    pivP M p = pv M f univ univ := by
  unfold pivP pv; congr 1; ext j; simp [hpf, Nat.pos_iff_ne_zero]

theorem den_le_other (i : Fin n) (j : Fin m) (hij : M i j ≠ 0) :
    den M w i univ ≤ w j + other M w i j := by
  unfold den other
  rw [sum_filter]
  calc ∑ a, (if M i a ≠ 0 then w a else 0)
      ≤ ∑ a, ((if a = j then w a else 0) + (if a = j then 0 else M i a * w a)) := by
        refine sum_le_sum fun a _ => ?_
        by_cases haj : a = j
        · subst haj; by_cases h : M i a = 0 <;> simp [h]
        · rw [if_neg haj, if_neg haj, zero_add]
          split_ifs with h
          · exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
          · exact Nat.zero_le _
    _ = w j + ∑ a, (if a = j then 0 else M i a * w a) := by
        rw [sum_add_distrib]; simp

theorem rat_le_den (hw : ∀ j, 0 < w j) (i : Fin n) (j : Fin m) (hij : M i j ≠ 0) :
    rat M w i j ≤ (w j : ℚ) / (den M w i univ : ℚ) := by
  unfold rat
  have h1 : (w j : ℚ) ≤ (den M w i univ : ℚ) := by
    exact_mod_cast w_le_den M w i j univ (mem_univ j) hij
  have h2 : (den M w i univ : ℚ) ≤ (w j : ℚ) + (other M w i j : ℚ) := by
    exact_mod_cast den_le_other M w i j hij
  have hwj : (0:ℚ) < w j := by exact_mod_cast hw j
  exact div_le_div_of_nonneg_left hwj.le (lt_of_lt_of_le hwj h1) h2

theorem score_le (hw : ∀ j, 0 < w j) : ∃ p : Equiv.Perm (Fin m), scoreF M w ≤ (pivP M p : ℚ) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, ?_⟩
    have : scoreF M w = 0 := by simp [scoreF, colv]
    rw [this]; positivity
  have hc : ∀ j, ∃ i, colv M w j ≠ 0 → (M i j ≠ 0 ∧ colv M w j = rat M w i j) := by
    intro j
    rcases colv_cases M w j with h | ⟨i, hi, h⟩
    · exact ⟨⟨0, hn⟩, fun h' => absurd h h'⟩
    · exact ⟨i, fun _ => ⟨hi, h⟩⟩
  choose g hg using hc
  obtain ⟨f, hf, hle⟩ := mainC M w hw univ univ (univ.filter (fun j => colv M w j ≠ 0)) g
    (subset_univ _) (fun j hj => ⟨mem_univ _, (hg j (mem_filter.1 hj).2).1⟩)
  obtain ⟨p, hp⟩ := perm_of_inj f hf
  refine ⟨p, ?_⟩
  rw [pivP_eq M p f hp]
  refine le_trans ?_ hle
  unfold scoreF
  rw [← sum_filter_ne_zero]
  refine sum_le_sum fun j hj => ?_
  rw [(hg j (mem_filter.1 hj).2).2]
  exact rat_le_den M w hw (g j) j (hg j (mem_filter.1 hj).2).1

end partC

section partA
variable {n m : ℕ} (M : Fin n → Fin m → ℕ)

def geo (b : ℕ) (p : Equiv.Perm (Fin m)) (j : Fin m) : ℕ := b ^ (m - 1 - (p j).val)

theorem gsum (b K : ℕ) (hb : 1 ≤ b) : (b - 1) * ∑ k ∈ range K, b ^ k + 1 = b ^ K := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ, mul_add, add_right_comm, ih, pow_succ]; ring

theorem later_lt (b : ℕ) (hb : 1 ≤ b) (p : Equiv.Perm (Fin m)) (j : Fin m) :
    (b - 1) * ∑ a ∈ univ.filter (fun a => p j < p a), geo b p a < geo b p j := by
  have hinj : Set.InjOn (fun a : Fin m => m - 1 - (p a).val)
      ↑(univ.filter (fun a => p j < p a)) := by
    intro a ha a' ha' h
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, Fin.lt_def] at ha ha'
    have h1 := (p a).isLt
    have h2 := (p a').isLt
    simp only at h
    exact p.injective (Fin.ext (by omega))
  have himg := sum_image (f := fun k => b ^ k) hinj
  unfold geo
  rw [← himg]
  have hsub : (univ.filter (fun a => p j < p a)).image (fun a : Fin m => m - 1 - (p a).val) ⊆
      range (m - 1 - (p j).val) := by
    intro k hk
    simp only [mem_image, mem_filter, mem_univ, true_and, Fin.lt_def] at hk
    obtain ⟨a, ha, rfl⟩ := hk
    have h1 := (p a).isLt
    simp only [mem_range]
    omega
  have h3 := gsum b (m - 1 - (p j).val) hb
  calc (b - 1) * ∑ k ∈ (univ.filter (fun a => p j < p a)).image
        (fun a : Fin m => m - 1 - (p a).val), b ^ k
      ≤ (b - 1) * ∑ k ∈ range (m - 1 - (p j).val), b ^ k :=
        Nat.mul_le_mul_left _ (sum_le_sum_of_subset hsub)
    _ < b ^ (m - 1 - (p j).val) := by omega

theorem other_piv (D : ℕ) (hM : ∀ i j, M i j ≤ D) (b : ℕ) (hb : 1 ≤ b) (p : Equiv.Perm (Fin m))
    (i : Fin n) (j : Fin m) (hz : ∀ a, p a < p j → M i a = 0) :
    (b - 1) * other M (geo b p) i j ≤ D * geo b p j := by
  have h1 : other M (geo b p) i j ≤ D * ∑ a ∈ univ.filter (fun a => p j < p a), geo b p a := by
    unfold other; rw [mul_sum, sum_filter]
    refine sum_le_sum fun a _ => ?_
    by_cases haj : a = j
    · simp [haj]
    · rw [if_neg haj]
      rcases lt_trichotomy (p a) (p j) with h | h | h
      · rw [hz a h]; simp
      · exact absurd (p.injective h) haj
      · rw [if_pos h]; exact Nat.mul_le_mul_right _ (hM i a)
  calc (b - 1) * other M (geo b p) i j
      ≤ (b - 1) * (D * ∑ a ∈ univ.filter (fun a => p j < p a), geo b p a) :=
        Nat.mul_le_mul_left _ h1
    _ = D * ((b - 1) * ∑ a ∈ univ.filter (fun a => p j < p a), geo b p a) := by ring
    _ ≤ D * geo b p j := Nat.mul_le_mul_left _ (later_lt b hb p j).le

theorem other_nonpiv (b : ℕ) (hb : 1 ≤ b) (p : Equiv.Perm (Fin m)) (i : Fin n) (j a : Fin m)
    (ha : p a < p j) (hMa : M i a ≠ 0) : b * geo b p j ≤ other M (geo b p) i j := by
  have haj : a ≠ j := fun h => by rw [h] at ha; exact lt_irrefl _ ha
  have hlt : (p a).val < (p j).val := ha
  have h1 := (p j).isLt
  calc b * geo b p j = b ^ (m - 1 - (p j).val + 1) := by unfold geo; ring
    _ ≤ geo b p a := Nat.pow_le_pow_right hb (by omega)
    _ ≤ M i a * geo b p a := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hMa)
    _ = (if a = j then 0 else M i a * geo b p a) := by rw [if_neg haj]
    _ ≤ other M (geo b p) i j := by
        unfold other
        exact single_le_sum (f := fun a => if a = j then 0 else M i a * geo b p a)
          (fun _ _ => Nat.zero_le _) (mem_univ a)

theorem r1 (W O B D : ℚ) (hW : 0 < W) (hO : 0 ≤ O) (hB : 0 < B - 1) (h : (B - 1) * O ≤ D * W) :
    1 - D / (B - 1) ≤ W / (W + O) := by
  have hWO : (0:ℚ) < W + O := by linarith
  have e : O / (W + O) = 1 - W / (W + O) := by
    rw [eq_sub_iff_add_eq, ← add_div, add_comm O W, div_self hWO.ne']
  have h2 : O / (W + O) ≤ O / W := div_le_div_of_nonneg_left hO hW (by linarith)
  have h3 : O / W ≤ D / (B - 1) := by rw [div_le_div_iff₀ hW hB]; linarith
  linarith

theorem r2 (W O B : ℚ) (hW : 0 < W) (hB : 0 < B) (h : B * W ≤ O) : W / (W + O) ≤ 1 / (B + 1) := by
  rw [div_le_div_iff₀ (by nlinarith) (by linarith)]; linarith

theorem claim1 (D : ℕ) (hM : ∀ i j, M i j ≤ D) (b : ℕ) (hb1 : 2 * m * D + 1 < b)
    (hb2 : 2 * m < b + 1) (p : Equiv.Perm (Fin m)) :
    |scoreF M (geo b p) - (pivP M p : ℚ)| < 1 / 2 := by
  have hb : 1 ≤ b := by omega
  have hbq : (2 * m * D + 1 : ℚ) < b := by exact_mod_cast hb1
  have hbq2 : (2 * m : ℚ) < b + 1 := by exact_mod_cast hb2
  have hb0 : (0:ℚ) < (b:ℚ) - 1 := by
    have : (1:ℚ) < b := by
      have : 1 < b := by omega
      exact_mod_cast this
    linarith
  have hbc : ((b - 1 : ℕ) : ℚ) = (b:ℚ) - 1 := by rw [Nat.cast_sub hb]; simp
  have hx : (0:ℚ) ≤ (D:ℚ) / ((b:ℚ) - 1) := div_nonneg (by positivity) hb0.le
  have hy : (0:ℚ) ≤ 1 / ((b:ℚ) + 1) := by positivity
  have hterm : ∀ j, -((D:ℚ) / ((b:ℚ) - 1)) ≤ colv M (geo b p) j -
      (if (∃ i, 0 < M i j ∧ ∀ a, p a < p j → M i a = 0) then (1:ℚ) else 0) ∧
      colv M (geo b p) j -
      (if (∃ i, 0 < M i j ∧ ∀ a, p a < p j → M i a = 0) then (1:ℚ) else 0)
        ≤ 1 / ((b:ℚ) + 1) := by
    intro j
    have hW : (0:ℚ) < (geo b p j : ℚ) := by
      unfold geo; exact_mod_cast pow_pos hb _
    by_cases hP : ∃ i, 0 < M i j ∧ ∀ a, p a < p j → M i a = 0
    · rw [if_pos hP]
      obtain ⟨i, hi, hz⟩ := hP
      have hr := colv_ge M (geo b p) j i hi.ne'
      have hle1 : colv M (geo b p) j ≤ 1 := by
        refine colv_le M (geo b p) j 1 zero_le_one (fun i' _ => ?_)
        unfold rat
        exact (div_le_one (by positivity)).2 (by simp)
      have hO := other_piv M D hM b hb p i j hz
      have hOq : ((b:ℚ) - 1) * (other M (geo b p) i j : ℚ) ≤ (D:ℚ) * (geo b p j : ℚ) := by
        rw [← hbc]; exact_mod_cast hO
      have := r1 (geo b p j : ℚ) (other M (geo b p) i j : ℚ) b D hW (by positivity) hb0 hOq
      have hrr : rat M (geo b p) i j = (geo b p j : ℚ) / ((geo b p j : ℚ) +
          (other M (geo b p) i j : ℚ)) := rfl
      constructor <;> linarith
    · rw [if_neg hP]
      push_neg at hP
      have h0 := colv_nonneg M (geo b p) j
      have hle : colv M (geo b p) j ≤ 1 / ((b:ℚ) + 1) := by
        refine colv_le M (geo b p) j _ hy (fun i hi => ?_)
        obtain ⟨a, ha, hMa⟩ := hP i (Nat.pos_of_ne_zero hi)
        have h1 := other_nonpiv M b hb p i j a ha hMa
        have h1q : (b:ℚ) * (geo b p j : ℚ) ≤ (other M (geo b p) i j : ℚ) := by exact_mod_cast h1
        exact r2 _ _ _ hW (by linarith) h1q
      constructor <;> linarith
  have hpiv : (pivP M p : ℚ) = ∑ j, (if (∃ i, 0 < M i j ∧ ∀ a, p a < p j → M i a = 0)
      then (1:ℚ) else 0) := by
    unfold pivP; rw [card_filter]; push_cast; rfl
  rw [hpiv]; unfold scoreF; rw [← sum_sub_distrib]
  have hup := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin m))) => (hterm j).2)
  have hlo := sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin m))) => (hterm j).1)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hup hlo
  have hmx : (m:ℚ) * ((D:ℚ) / ((b:ℚ) - 1)) < 1 / 2 := by
    rw [← mul_div_assoc, div_lt_iff₀ hb0]; nlinarith
  have hmy : (m:ℚ) * (1 / ((b:ℚ) + 1)) < 1 / 2 := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; nlinarith
  rw [abs_lt]; constructor <;> nlinarith

end partA

section partB
variable {n m : ℕ} (M : Fin n → Fin m → ℕ)

theorem tri_fwd (s : ℕ) (row : Fin s ↪ Fin n) (col : Fin s ↪ Fin m)
    (hdiag : ∀ i, 0 < M (row i) (col i)) (hlow : ∀ i j, j < i → M (row i) (col j) = 0) :
    ∃ p : Equiv.Perm (Fin m), s ≤ pivP M p := by
  classical
  let f : Fin m → ℕ := fun a => if h : ∃ t, col t = a then (Classical.choose h).val else s + a.val
  have hf1 : ∀ t, f (col t) = t.val := by
    intro t
    have h : ∃ t', col t' = col t := ⟨t, rfl⟩
    simp only [f, dif_pos h]
    rw [col.injective (Classical.choose_spec h)]
  have hf2 : ∀ a, (¬ ∃ t, col t = a) → f a = s + a.val := by
    intro a h; simp only [f, dif_neg h]
  have hfinj : Function.Injective f := by
    intro a b h
    by_cases ha : ∃ t, col t = a <;> by_cases hb : ∃ t, col t = b
    · obtain ⟨t, rfl⟩ := ha; obtain ⟨t', rfl⟩ := hb
      rw [hf1, hf1] at h; rw [Fin.ext h]
    · obtain ⟨t, rfl⟩ := ha; rw [hf1, hf2 b hb] at h; have := t.isLt; omega
    · obtain ⟨t, rfl⟩ := hb; rw [hf1, hf2 a ha] at h; have := t.isLt; omega
    · rw [hf2 a ha, hf2 b hb] at h; exact Fin.ext (by omega)
  obtain ⟨p, hp⟩ := perm_of_inj f hfinj
  refine ⟨p, ?_⟩
  rw [pivP_eq M p f hp]
  have hsub : univ.image col ⊆ univ.filter (fun j => ∃ i ∈ (univ : Finset (Fin n)), M i j ≠ 0 ∧
      ∀ a ∈ (univ : Finset (Fin m)), f a < f j → M i a = 0) := by
    intro x hx
    simp only [mem_image, mem_univ, true_and] at hx
    obtain ⟨t, rfl⟩ := hx
    refine mem_filter.2 ⟨mem_univ _, row t, mem_univ _, (hdiag t).ne', fun a _ hlt => ?_⟩
    rw [hf1] at hlt
    by_cases ha : ∃ t', col t' = a
    · obtain ⟨t', rfl⟩ := ha
      rw [hf1] at hlt
      exact hlow t t' hlt
    · rw [hf2 a ha] at hlt; omega
  have := card_le_card hsub
  rw [card_image_of_injective _ col.injective, card_univ, Fintype.card_fin] at this
  exact this

theorem tri_bwd (s : ℕ) (p : Equiv.Perm (Fin m)) (hs : s ≤ pivP M p) :
    ∃ (row : Fin s ↪ Fin n) (col : Fin s ↪ Fin m),
      (∀ i, 0 < M (row i) (col i)) ∧ ∀ i j, j < i → M (row i) (col j) = 0 := by
  classical
  set P := univ.filter (fun j : Fin m => ∃ i : Fin n,
      0 < M i j ∧ ∀ a : Fin m, p a < p j → M i a = 0) with hP
  have hcard : s ≤ (P.map p.toEmbedding).card := by rw [card_map]; exact hs
  obtain ⟨Q, hQ, hQc⟩ := exists_subset_card_eq hcard
  let e := Q.orderEmbOfFin hQc
  let colf : Fin s → Fin m := fun t => p.symm (e t)
  have hcolinj : Function.Injective colf := by
    intro t t' h
    exact e.injective (p.symm.injective h)
  have hpc : ∀ t, p (colf t) = e t := fun t => by simp [colf]
  have hmem : ∀ t, ∃ i : Fin n, 0 < M i (colf t) ∧ ∀ a : Fin m, p a < p (colf t) → M i a = 0 := by
    intro t
    have h1 : e t ∈ P.map p.toEmbedding := hQ (Q.orderEmbOfFin_mem hQc t)
    rw [mem_map] at h1
    obtain ⟨a, ha, hae⟩ := h1
    have : a = colf t := by simp only [colf, ← hae]; simp
    rw [← this]
    exact (mem_filter.1 ha).2
  choose r hr using hmem
  have hlow : ∀ t t', t' < t → M (r t) (colf t') = 0 := by
    intro t t' h
    apply (hr t).2
    rw [hpc, hpc]
    exact e.strictMono h
  have hrinj : Function.Injective r := by
    intro t t' h
    rcases lt_trichotomy t t' with h1 | h1 | h1
    · have := hlow t' t h1; rw [← h] at this; exact absurd this (hr t).1.ne'
    · exact h1
    · have := hlow t t' h1; rw [h] at this; exact absurd this (hr t').1.ne'
  exact ⟨⟨r, hrinj⟩, ⟨colf, hcolinj⟩, fun t => (hr t).1, hlow⟩

end partB

end PEqualNP.Outside.L_lib_899

open PEqualNP.Outside.L_lib_899 in
theorem PEqualNP.Outside.L_lib_899 : ∀ (n m D : ℕ) (M : Fin n → Fin m → ℕ), (∀ i j, M i j ≤ D) →
  let triangular := fun s : ℕ =>
    ∃ (row : Fin s ↪ Fin n) (col : Fin s ↪ Fin m),
      (∀ i, 0 < M (row i) (col i)) ∧ ∀ i j, j < i → M (row i) (col j) = 0
  let piv := fun p : Equiv.Perm (Fin m) =>
    (Finset.univ.filter (fun j : Fin m => ∃ i : Fin n,
      0 < M i j ∧ ∀ a : Fin m, p a < p j → M i a = 0)).card
  let score := fun w : Fin m → ℕ =>
    ∑ j : Fin m, (List.finRange n).foldl (fun (best : ℚ) i =>
      let other := ∑ a : Fin m, if a = j then 0 else M i a * w a
      if M i j = 0 then best else max best ((w j : ℚ) / ((w j : ℚ) + other))) 0
  let base := 2+2*m*(D+1)
  (∀ p : Equiv.Perm (Fin m),
    |score (fun j => base^(m-1-(p j).val)) - (piv p : ℚ)| < (1/2 : ℚ)) ∧
  ∀ s : ℕ,
    (triangular s ↔ ∃ p : Equiv.Perm (Fin m), s ≤ piv p) ∧
    (triangular s ↔ ∃ w : Fin m → ℕ, (∀ j, 0 < w j) ∧ (s : ℚ)-1 < score w) := by
  intro n m D M hM triangular piv score base
  have htri : ∀ s, triangular s ↔ ∃ p : Equiv.Perm (Fin m), s ≤ piv p := by
    intro s
    constructor
    · rintro ⟨row, col, h1, h2⟩
      exact tri_fwd M s row col h1 h2
    · rintro ⟨p, hp⟩
      exact tri_bwd M s p hp
  have hb1 : 2 * m * D + 1 < base := by
    show 2 * m * D + 1 < 2 + 2 * m * (D + 1)
    nlinarith
  have hb2 : 2 * m < base + 1 := by
    show 2 * m < 2 + 2 * m * (D + 1) + 1
    nlinarith
  have h1 : ∀ p : Equiv.Perm (Fin m),
      |score (fun j => base ^ (m - 1 - (p j).val)) - (piv p : ℚ)| < (1 / 2 : ℚ) :=
    fun p => claim1 M D hM base hb1 hb2 p
  refine ⟨h1, fun s => ⟨htri s, ?_⟩⟩
  rw [htri s]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨fun j => base ^ (m - 1 - (p j).val), fun j => pow_pos (by omega) _, ?_⟩
    have h2 := (abs_lt.1 (h1 p)).1
    have h3 : (s : ℚ) ≤ (piv p : ℚ) := by exact_mod_cast hp
    linarith
  · rintro ⟨w, hw, hlt⟩
    obtain ⟨p, hp⟩ := score_le M w hw
    refine ⟨p, ?_⟩
    have h2 : (s : ℚ) - 1 < (pivP M p : ℚ) := lt_of_lt_of_le hlt hp
    have h3 : s < pivP M p + 1 := by
      have : (s : ℚ) < (pivP M p : ℚ) + 1 := by linarith
      exact_mod_cast this
    show s ≤ pivP M p
    omega
