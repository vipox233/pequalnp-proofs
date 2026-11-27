import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25575_aux

def mv (mode letter : Nat) : Nat × Nat :=
    let near := letter.testBit 0
    let far := letter.testBit 1
    let hit := letter.testBit 2
    let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
      ((mode == 3) && near)
    let diagonal := !hit && (((mode == 1) && !near && !far) ||
      (mode == 2) || (mode == 3))
    (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
      hit.toNat + (aligned && hit).toNat)

def stepF (code : Nat) (st : Nat × Nat) (digitPos : Nat) : Nat × Nat :=
  let result := mv st.1 ((code >>> (3 * digitPos)) % 8)
  (result.1, st.2 + result.2)

def summ (code length : Nat) : Nat × Nat :=
  (List.range length).foldl (stepF code) (0, 0)

def step (st : Nat × Nat) (l : Nat) : Nat × Nat :=
  ((mv st.1 l).1, st.2 + (mv st.1 l).2)

theorem foldl_congr_range {β : Type} (f g : β → Nat → β) (b : β) :
    ∀ n, (∀ st, ∀ i < n, f st i = g st i) →
      (List.range n).foldl f b = (List.range n).foldl g b := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      ih (fun st i hi => h st i (by omega))]
    simp [h _ n (by omega)]

theorem digit_low (c l n i : Nat) (_hc : c < 8 ^ n) (hi : i < n) :
    ((c + 8 ^ n * l) >>> (3 * i)) % 8 = (c >>> (3 * i)) % 8 := by
  simp only [Nat.shiftRight_eq_div_pow]
  have h8 : 8 ^ n = 2 ^ (3 * i) * 8 ^ (n - i) := by
    rw [pow_mul, show (2:Nat) ^ 3 = 8 by norm_num, ← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (3 * i) := by positivity
  rw [h8, mul_assoc, Nat.add_mul_div_left _ _ hpos]
  have : 8 ^ (n - i) = 8 * 8 ^ (n - i - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [this, mul_assoc, Nat.add_mul_mod_self_left]

theorem digit_top (c l n : Nat) (hc : c < 8 ^ n) (hl : l < 8) :
    ((c + 8 ^ n * l) >>> (3 * n)) % 8 = l := by
  simp only [Nat.shiftRight_eq_div_pow]
  have h8 : 2 ^ (3 * n) = 8 ^ n := by
    rw [pow_mul]; norm_num
  rw [h8, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hc]
  omega

theorem summ_succ (c l n : Nat) (hc : c < 8 ^ n) (hl : l < 8) :
    summ (c + 8 ^ n * l) (n + 1) = step (summ c n) l := by
  unfold summ
  rw [List.range_succ, List.foldl_append,
    foldl_congr_range (stepF (c + 8 ^ n * l)) (stepF c) _ n (by
      intro st i hi; simp only [stepF, digit_low c l n i hc hi])]
  simp [stepF, step, digit_top c l n hc hl]

theorem sum_range_mul {M : Type} [AddCommMonoid M] (g : Nat → M) (a : Nat) :
    ∀ b, ∑ x ∈ Finset.range (a * b), g x = ∑ l ∈ Finset.range b, ∑ c ∈ Finset.range a, g (c + a * l) := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, ← ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl; intro c _; rw [add_comm]

theorem sum_summ_succ {M : Type} [AddCommMonoid M] (f : Nat × Nat → M) (n : Nat) :
    ∑ c ∈ Finset.range (8 ^ (n + 1)), f (summ c (n + 1)) =
      ∑ c ∈ Finset.range (8 ^ n), ∑ l ∈ Finset.range 8, f (step (summ c n) l) := by
  rw [pow_succ, sum_range_mul, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c hc
  apply Finset.sum_congr rfl; intro l hl
  rw [summ_succ c l n (Finset.mem_range.1 hc) (Finset.mem_range.1 hl)]

theorem mv_0_0 : mv 0 0 = (1, 0) := by decide
theorem mv_0_1 : mv 0 1 = (1, 0) := by decide
theorem mv_0_2 : mv 0 2 = (1, 0) := by decide
theorem mv_0_3 : mv 0 3 = (1, 0) := by decide
theorem mv_0_4 : mv 0 4 = (1, 1) := by decide
theorem mv_0_5 : mv 0 5 = (1, 1) := by decide
theorem mv_0_6 : mv 0 6 = (1, 1) := by decide
theorem mv_0_7 : mv 0 7 = (1, 1) := by decide
theorem mv_1_0 : mv 1 0 = (3, 0) := by decide
theorem mv_1_1 : mv 1 1 = (1, 0) := by decide
theorem mv_1_2 : mv 1 2 = (1, 0) := by decide
theorem mv_1_3 : mv 1 3 = (2, 0) := by decide
theorem mv_1_4 : mv 1 4 = (1, 1) := by decide
theorem mv_1_5 : mv 1 5 = (1, 1) := by decide
theorem mv_1_6 : mv 1 6 = (1, 1) := by decide
theorem mv_1_7 : mv 1 7 = (0, 2) := by decide
theorem mv_2_0 : mv 2 0 = (3, 0) := by decide
theorem mv_2_1 : mv 2 1 = (3, 0) := by decide
theorem mv_2_2 : mv 2 2 = (2, 0) := by decide
theorem mv_2_3 : mv 2 3 = (2, 0) := by decide
theorem mv_2_4 : mv 2 4 = (1, 1) := by decide
theorem mv_2_5 : mv 2 5 = (1, 1) := by decide
theorem mv_2_6 : mv 2 6 = (0, 2) := by decide
theorem mv_2_7 : mv 2 7 = (0, 2) := by decide
theorem mv_3_0 : mv 3 0 = (3, 0) := by decide
theorem mv_3_1 : mv 3 1 = (2, 0) := by decide
theorem mv_3_2 : mv 3 2 = (3, 0) := by decide
theorem mv_3_3 : mv 3 3 = (2, 0) := by decide
theorem mv_3_4 : mv 3 4 = (1, 1) := by decide
theorem mv_3_5 : mv 3 5 = (0, 2) := by decide
theorem mv_3_6 : mv 3 6 = (1, 1) := by decide
theorem mv_3_7 : mv 3 7 = (0, 2) := by decide

theorem mv_big (m l : Nat) (hm : 4 ≤ m) : mv m l = mv 0 l := by
  have h1 : (m == 1) = false := by simp; omega
  have h2 : (m == 2) = false := by simp; omega
  have h3 : (m == 3) = false := by simp; omega
  simp [mv, h1, h2, h3]

theorem mv_snd_le (m l : Nat) : (mv m l).2 ≤ 2 := by
  have h1 := Bool.toNat_le (l.testBit 2)
  have h2 := Bool.toNat_le ((((m == 1) && l.testBit 0 && l.testBit 1) || ((m == 2) && l.testBit 1) ||
      ((m == 3) && l.testBit 0)) && l.testBit 2)
  simp only [mv]; omega

def Φ (m : Nat) : Nat := if m = 1 then 2 else if m = 2 ∨ m = 3 then 4 else 0

theorem Φ_big (m : Nat) (hm : 4 ≤ m) : Φ m = 0 := by
  unfold Φ; split_ifs <;> omega

theorem pot_closed (m : Nat) :
    ∑ l ∈ Finset.range 8, (14 * (mv m l).2 + Φ (mv m l).1) = 8 * (Φ m + 9) := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h | h | h
  all_goals try (subst h; simp [Finset.sum_range_succ, mv_0_0, mv_0_1, mv_0_2, mv_0_3, mv_0_4, mv_0_5, mv_0_6, mv_0_7, mv_1_0, mv_1_1, mv_1_2, mv_1_3, mv_1_4, mv_1_5, mv_1_6, mv_1_7, mv_2_0, mv_2_1, mv_2_2, mv_2_3, mv_2_4, mv_2_5, mv_2_6, mv_2_7, mv_3_0, mv_3_1, mv_3_2, mv_3_3, mv_3_4, mv_3_5, mv_3_6, mv_3_7, Φ])
  rw [Finset.sum_congr rfl (fun l _ => by rw [mv_big m l h])]
  rw [Φ_big m h]
  simp [Finset.sum_range_succ, mv_0_0, mv_0_1, mv_0_2, mv_0_3, mv_0_4, mv_0_5, mv_0_6, mv_0_7, mv_1_0, mv_1_1, mv_1_2, mv_1_3, mv_1_4, mv_1_5, mv_1_6, mv_1_7, mv_2_0, mv_2_1, mv_2_2, mv_2_3, mv_2_4, mv_2_5, mv_2_6, mv_2_7, mv_3_0, mv_3_1, mv_3_2, mv_3_3, mv_3_4, mv_3_5, mv_3_6, mv_3_7, Φ]

theorem pot_step (st : Nat × Nat) :
    ∑ l ∈ Finset.range 8, (14 * (step st l).2 + Φ (step st l).1) = 8 * (14 * st.2 + Φ st.1) + 72 := by
  have := pot_closed st.1
  simp only [step, mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul] at *
  omega

theorem pot_sum (n : Nat) :
    ∑ c ∈ Finset.range (8 ^ n), (14 * (summ c n).2 + Φ (summ c n).1) = 9 * n * 8 ^ n := by
  induction n with
  | zero => simp [summ, Φ]
  | succ n ih =>
    rw [sum_summ_succ (fun st => 14 * st.2 + Φ st.1) n]
    calc _ = ∑ c ∈ Finset.range (8 ^ n), (8 * (14 * (summ c n).2 + Φ (summ c n).1) + 72) :=
          Finset.sum_congr rfl (fun c _ => pot_step _)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ih]
          simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
          ring

theorem gain_le (c n : Nat) : (summ c n).2 ≤ 2 * n := by
  have key : ∀ (L : List Nat) (st : Nat × Nat), (L.foldl (stepF c) st).2 ≤ st.2 + 2 * L.length := by
    intro L
    induction L with
    | nil => intro st; simp
    | cons x L ih =>
      intro st
      simp only [List.foldl_cons, List.length_cons]
      have h1 := ih (stepF c st x)
      have h2 := mv_snd_le st.1 ((c >>> (3 * x)) % 8)
      simp only [stepF] at h1 ⊢
      omega
  have := key (List.range n) (0, 0)
  simpa [summ] using this

noncomputable def φ (m : Nat) : ℝ := (Φ m : ℝ) / 14

noncomputable def ψ (a : ℝ) (st : Nat × Nat) : ℝ := (1 - a) ^ st.2 * (1 - a * φ st.1)

theorem tilt_closed (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (m : Nat) :
    ∑ l ∈ Finset.range 8, (1 - a) ^ (mv m l).2 * (1 - a * φ (mv m l).1) ≤
      8 * (1 - 9 * a / 14 + 2 * a ^ 2) * (1 - a * φ m) := by
  rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with h | h | h | h | h
  all_goals try (subst h; simp [Finset.sum_range_succ, mv_0_0, mv_0_1, mv_0_2, mv_0_3, mv_0_4, mv_0_5, mv_0_6, mv_0_7, mv_1_0, mv_1_1, mv_1_2, mv_1_3, mv_1_4, mv_1_5, mv_1_6, mv_1_7, mv_2_0, mv_2_1, mv_2_2, mv_2_3, mv_2_4, mv_2_5, mv_2_6, mv_2_7, mv_3_0, mv_3_1, mv_3_2, mv_3_3, mv_3_4, mv_3_5, mv_3_6, mv_3_7, φ, Φ]; nlinarith [sq_nonneg a, mul_nonneg ha0 (sq_nonneg a)])
  rw [Finset.sum_congr rfl (fun l _ => by rw [mv_big m l h])]
  have : φ m = 0 := by simp [φ, Φ_big m h]
  rw [this]
  simp [Finset.sum_range_succ, mv_0_0, mv_0_1, mv_0_2, mv_0_3, mv_0_4, mv_0_5, mv_0_6, mv_0_7, mv_1_0, mv_1_1, mv_1_2, mv_1_3, mv_1_4, mv_1_5, mv_1_6, mv_1_7, mv_2_0, mv_2_1, mv_2_2, mv_2_3, mv_2_4, mv_2_5, mv_2_6, mv_2_7, mv_3_0, mv_3_1, mv_3_2, mv_3_3, mv_3_4, mv_3_5, mv_3_6, mv_3_7, φ, Φ]; nlinarith [sq_nonneg a]

theorem tilt_step (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (st : Nat × Nat) :
    ∑ l ∈ Finset.range 8, ψ a (step st l) ≤ 8 * (1 - 9 * a / 14 + 2 * a ^ 2) * ψ a st := by
  have hθ : 0 ≤ (1 - a) ^ st.2 := pow_nonneg (by linarith) _
  have := mul_le_mul_of_nonneg_left (tilt_closed a ha0 ha1 st.1) hθ
  simp only [ψ, step, pow_add]
  rw [show ∑ l ∈ Finset.range 8, (1 - a) ^ st.2 * (1 - a) ^ (mv st.1 l).2 * (1 - a * φ (mv st.1 l).1)
      = (1 - a) ^ st.2 * ∑ l ∈ Finset.range 8, (1 - a) ^ (mv st.1 l).2 * (1 - a * φ (mv st.1 l).1) by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring]
  linarith

theorem tilt_sum (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (n : Nat) :
    ∑ c ∈ Finset.range (8 ^ n), ψ a (summ c n) ≤ (8 * (1 - 9 * a / 14 + 2 * a ^ 2)) ^ n := by
  have hρ : 0 ≤ 8 * (1 - 9 * a / 14 + 2 * a ^ 2) := by nlinarith
  induction n with
  | zero => simp [summ, ψ, φ, Φ]
  | succ n ih =>
    rw [sum_summ_succ (ψ a) n, pow_succ]
    calc _ ≤ ∑ c ∈ Finset.range (8 ^ n), 8 * (1 - 9 * a / 14 + 2 * a ^ 2) * ψ a (summ c n) :=
          Finset.sum_le_sum (fun c _ => tilt_step a ha0 ha1 _)
      _ = 8 * (1 - 9 * a / 14 + 2 * a ^ 2) * ∑ c ∈ Finset.range (8 ^ n), ψ a (summ c n) := by
          rw [Finset.mul_sum]
      _ ≤ 8 * (1 - 9 * a / 14 + 2 * a ^ 2) * (8 * (1 - 9 * a / 14 + 2 * a ^ 2)) ^ n :=
          mul_le_mul_of_nonneg_left ih hρ
      _ = _ := by ring

theorem list_sum_range (h : Nat → Nat) :
    ∀ N, ((List.range N).map h).sum = ∑ c ∈ Finset.range N, h c := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

def price (n depth : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun codeWord => 2 ^ (2 * n - ((summ codeWord n).2 - depth)))).sum

theorem Φ_le (m : Nat) : Φ m ≤ 4 := by unfold Φ; split_ifs <;> omega

theorem term_le (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (n G d : Nat) (hG : G ≤ 2 * n) :
    (2:ℝ) ^ (2 * n - (G - d)) ≤ 2 ^ (2 * n) * ((1 - a) ^ G / (1 - a) ^ d) := by
  have hθ : 0 < 1 - a := by linarith
  by_cases hGd : d ≤ G
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hGd
    have hk : d + k - d = k := by omega
    rw [hk, pow_add, mul_div_cancel_left₀ _ (pow_ne_zero _ hθ.ne')]
    have e : (2:ℝ) ^ (2 * n) = 2 ^ (2 * n - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
    rw [e, mul_assoc, ← mul_pow]
    have : (1:ℝ) ≤ (2 * (1 - a)) ^ k := one_le_pow₀ (by linarith)
    have h2 : (0:ℝ) < 2 ^ (2 * n - k) := by positivity
    nlinarith
  · have hk : G - d = 0 := by omega
    rw [hk, Nat.sub_zero]
    have : (1 - a) ^ d ≤ (1 - a) ^ G := pow_le_pow_of_le_one hθ.le (by linarith) (by omega)
    have h1 : 1 ≤ (1 - a) ^ G / (1 - a) ^ d := by
      rw [one_le_div (by positivity)]; exact this
    have h2 : (0:ℝ) < 2 ^ (2 * n) := by positivity
    nlinarith

theorem price_upper (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (n d : Nat) :
    (price n d : ℝ) ≤ 2 ^ (5 * n) * (7 / 6) * ((1 - 9 * a / 14 + 2 * a ^ 2) ^ n / (1 - a) ^ d) := by
  have hθ : 0 < 1 - a := by linarith
  have hd : 0 < (1 - a) ^ d := pow_pos hθ d
  unfold price
  rw [list_sum_range, Nat.cast_sum]
  push_cast
  have h1 : ∀ c ∈ Finset.range (8 ^ n), (2:ℝ) ^ (2 * n - ((summ c n).2 - d)) ≤
      2 ^ (2 * n) / (1 - a) ^ d * ((7 / 6) * ψ a (summ c n)) := by
    intro c _
    have t := term_le a ha0 ha1 n (summ c n).2 d (gain_le c n)
    have hΦ : (Φ (summ c n).1 : ℝ) ≤ 4 := by exact_mod_cast Φ_le _
    have hΦ0 : (0:ℝ) ≤ Φ (summ c n).1 := by positivity
    have hφ : φ (summ c n).1 ≤ 2 / 7 := by unfold φ; linarith
    have hφ0 : 0 ≤ φ (summ c n).1 := by unfold φ; positivity
    have hp : 0 ≤ (1 - a) ^ (summ c n).2 := pow_nonneg hθ.le _
    have hk : 1 ≤ 7 / 6 * (1 - a * φ (summ c n).1) := by nlinarith
    have : (1 - a) ^ (summ c n).2 ≤ 7 / 6 * ψ a (summ c n) := by
      unfold ψ; nlinarith [mul_le_mul_of_nonneg_left hk hp]
    calc _ ≤ 2 ^ (2 * n) * ((1 - a) ^ (summ c n).2 / (1 - a) ^ d) := t
      _ = 2 ^ (2 * n) / (1 - a) ^ d * (1 - a) ^ (summ c n).2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (by positivity)
  have hρ : 0 ≤ 8 * (1 - 9 * a / 14 + 2 * a ^ 2) := by nlinarith
  calc _ ≤ ∑ c ∈ Finset.range (8 ^ n), 2 ^ (2 * n) / (1 - a) ^ d * ((7 / 6) * ψ a (summ c n)) :=
        Finset.sum_le_sum h1
    _ = 2 ^ (2 * n) / (1 - a) ^ d * (7 / 6) * ∑ c ∈ Finset.range (8 ^ n), ψ a (summ c n) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro c _; ring
    _ ≤ 2 ^ (2 * n) / (1 - a) ^ d * (7 / 6) * (8 * (1 - 9 * a / 14 + 2 * a ^ 2)) ^ n :=
        mul_le_mul_of_nonneg_left (tilt_sum a ha0 ha1 n) (by positivity)
    _ = _ := by
        rw [mul_pow, show (2:ℝ) ^ (5 * n) = 2 ^ (2 * n) * 8 ^ n by
          rw [show 5 * n = 2 * n + 3 * n by ring, pow_add,
            show (2:ℝ) ^ (3 * n) = 8 ^ n by rw [pow_mul]; norm_num]]
        field_simp

theorem price_lower (n d : Nat) (hd : 9 * n < 14 * (d + 1)) :
    8 ^ n * 2 ^ (2 * n) ≤ 14 * (d + 1) * price n d := by
  set k := ((Finset.range (8 ^ n)).filter (fun c => (summ c n).2 ≤ d)).card
  set k' := ((Finset.range (8 ^ n)).filter (fun c => ¬ (summ c n).2 ≤ d)).card
  have hsplit : k + k' = 8 ^ n := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have hpot : 14 * ∑ c ∈ Finset.range (8 ^ n), (summ c n).2 ≤ 9 * n * 8 ^ n := by
    have := pot_sum n
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at this
    omega
  have hmark : k' * (d + 1) ≤ ∑ c ∈ Finset.range (8 ^ n), (summ c n).2 := by
    calc k' * (d + 1) = k' • (d + 1) := by rw [smul_eq_mul]
      _ ≤ ∑ c ∈ (Finset.range (8 ^ n)).filter (fun c => ¬ (summ c n).2 ≤ d), (summ c n).2 :=
          Finset.card_nsmul_le_sum _ _ _ (fun c hc => by
            have := (Finset.mem_filter.1 hc).2; omega)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hprice : k * 2 ^ (2 * n) ≤ price n d := by
    unfold price
    rw [list_sum_range]
    calc k * 2 ^ (2 * n) = ∑ c ∈ (Finset.range (8 ^ n)).filter (fun c => (summ c n).2 ≤ d), 2 ^ (2 * n) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ = ∑ c ∈ (Finset.range (8 ^ n)).filter (fun c => (summ c n).2 ≤ d), 2 ^ (2 * n - ((summ c n).2 - d)) := by
          apply Finset.sum_congr rfl; intro c hc
          have := (Finset.mem_filter.1 hc).2
          rw [show (summ c n).2 - d = 0 by omega, Nat.sub_zero]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have hN : 8 ^ n ≤ 14 * (d + 1) * k := by
    have e : 14 * (d + 1) * 8 ^ n = 14 * (d + 1) * k + 14 * (d + 1) * k' := by rw [← hsplit]; ring
    have h91 : (9 * n + 1) * 8 ^ n ≤ 14 * (d + 1) * 8 ^ n := Nat.mul_le_mul_right _ hd
    nlinarith
  calc 8 ^ n * 2 ^ (2 * n) ≤ 14 * (d + 1) * k * 2 ^ (2 * n) := Nat.mul_le_mul_right _ hN
    _ = 14 * (d + 1) * (k * 2 ^ (2 * n)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hprice

theorem rho_lt (p q : Nat) (hq : 0 < q) (hpq : 14 * p < 9 * q) (a : ℝ) (ha_def : a = 1 / (56 * (q:ℝ) ^ 2)) :
    (1 - 9 * a / 14 + 2 * a ^ 2) ^ q < (1 - a) ^ p := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
  have ha0 : 0 < a := by rw [ha_def]; positivity
  have haq : a * (q:ℝ) ^ 2 = 1 / 56 := by rw [ha_def]; field_simp
  have hq2 : (q:ℝ) ≤ (q:ℝ) ^ 2 := by nlinarith
  have ha1 : a ≤ 1 / 56 := by nlinarith
  have hp14 : (14:ℝ) * p + 1 ≤ 9 * q := by exact_mod_cast hpq
  have hpq' : (p:ℝ) ≤ q := by linarith
  have hp0 : (0:ℝ) ≤ p := by positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 9 * a / 14 - 2 * a ^ 2 := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; nlinarith
  have hb1 : b ≤ 9 * a / 14 := by rw [hb]; nlinarith
  have hρb : 1 - 9 * a / 14 + 2 * a ^ 2 = 1 - b := by rw [hb]; ring
  rw [hρb]
  have hθp : 1 - p * a ≤ (1 - a) ^ p := by
    have := one_add_mul_le_pow (show (-2:ℝ) ≤ -a by linarith) p
    simpa [sub_eq_add_neg, mul_neg] using this
  have hbq : 1 + q * b ≤ (1 + b) ^ q := one_add_mul_le_pow (by linarith) q
  have hprod : (1 - b) ^ q * (1 + b) ^ q ≤ 1 := by
    rw [← mul_pow]; apply pow_le_one₀ (by nlinarith) (by nlinarith)
  have hρq0 : 0 ≤ (1 - b) ^ q := pow_nonneg (by linarith) q
  have h1 : (1 - b) ^ q * (1 + q * b) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hbq hρq0) hprod
  have s1 : 14 * (p * a) ≤ (9 * q - 1) * a := by nlinarith
  have s2 : q * a ≤ 1 / 56 := by nlinarith
  have s3' : (p:ℝ) * q * a * b ≤ q * q * a * b :=
    by nlinarith [mul_le_mul_of_nonneg_right hpq' (show 0 ≤ (q:ℝ) * a * b by positivity)]
  have s3 : (p:ℝ) * q * a * b ≤ 9 * a / 784 := by
    have : (q:ℝ) * q * a * b = b / 56 := by
      rw [show (q:ℝ) * q * a * b = (a * q ^ 2) * b by ring, haq]; ring
    nlinarith
  have s4 : (q:ℝ) * a ^ 2 ≤ a / 56 := by nlinarith [mul_le_mul_of_nonneg_left s2 ha0.le]
  have expand : (1 - p * a) * (1 + q * b) = 1 + 9 * (q * a) / 14 - 2 * (q * a ^ 2) - p * a - p * q * a * b := by
    rw [hb]; ring
  have h2 : 1 < (1 - p * a) * (1 + q * b) := by rw [expand]; nlinarith
  have h3 : 0 < 1 + q * b := by positivity
  have : (1 - b) ^ q < 1 - p * a := by
    by_contra hc; push Not at hc
    have := mul_le_mul_of_nonneg_right hc h3.le
    linarith
  linarith

set_option maxHeartbeats 2000000 in
theorem main (p q : Nat) (hq : 0 < q) :
    (∃ (period start : Nat), 0 < period ∧ ∀ n : Nat, start ≤ n →
        price n (p * n / q) ≤ 2 ^ (5 * n - n / period)) ↔ 14 * p < 9 * q := by
  constructor
  · rintro ⟨P, st, hP, hbd⟩
    by_contra hpq
    push Not at hpq
    set c := 14 * (p * P + 1) with hc
    set j := st + 2 * c + 1 with hj
    have hj2 : j < 2 ^ j := Nat.lt_two_pow_self
    set m := 2 * j with hm
    set n := P * m with hn
    have hmn : m ≤ n := Nat.le_mul_of_pos_left m hP
    have hstn : st ≤ n := by omega
    have hnP : n / P = m := by rw [hn, Nat.mul_div_cancel_left _ hP]
    set d := p * n / q with hd
    have hdlt : p * n < (d + 1) * q := by
      have := Nat.lt_div_mul_add (a := p * n) hq
      rw [add_mul, one_mul]; exact this
    have h9 : 9 * n < 14 * (d + 1) := by
      have h1 : 9 * q * n ≤ 14 * p * n := Nat.mul_le_mul_right _ hpq
      have h2 : 9 * n * q < 14 * (d + 1) * q := by nlinarith
      exact Nat.lt_of_mul_lt_mul_right h2
    have hlow := price_lower n d h9
    have hup := hbd n hstn
    rw [hnP] at hup
    have e5 : 8 ^ n * 2 ^ (2 * n) = 2 ^ (5 * n - m) * 2 ^ m := by
      rw [show (8:ℕ) ^ n = 2 ^ (3 * n) by rw [show (8:ℕ) = 2 ^ 3 by rfl, ← pow_mul], ← pow_add,
        ← pow_add]
      congr 1; omega
    have hpow : 2 ^ (5 * n - m) * 2 ^ m ≤ 2 ^ (5 * n - m) * (14 * (d + 1)) := by
      calc _ = 8 ^ n * 2 ^ (2 * n) := e5.symm
        _ ≤ 14 * (d + 1) * price n d := hlow
        _ ≤ 14 * (d + 1) * 2 ^ (5 * n - m) := Nat.mul_le_mul_left _ hup
        _ = _ := by ring
    have h2m : 2 ^ m ≤ 14 * (d + 1) := Nat.le_of_mul_le_mul_left hpow (by positivity)
    have hdpn : d ≤ p * n := Nat.div_le_self _ _
    have hm1 : 1 ≤ m := by omega
    have h3 : 14 * (d + 1) ≤ c * m := by
      have : 14 * (p * n + 1) ≤ c * m := by rw [hc, hn]; nlinarith
      omega
    have h4 : 2 ^ m = 2 ^ j * 2 ^ j := by rw [hm, two_mul, pow_add]
    have h5 : 2 * c < 2 ^ j := by omega
    have : c * m < 2 ^ m := by
      rw [h4, hm]; nlinarith
    omega
  · intro hpq
    set a : ℝ := 1 / (56 * (q:ℝ) ^ 2) with ha_def
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
    have ha0 : 0 < a := by rw [ha_def]; positivity
    have ha1 : a ≤ 1 / 2 := by
      rw [ha_def, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hμ := rho_lt p q hq hpq a ha_def
    set ρ : ℝ := 1 - 9 * a / 14 + 2 * a ^ 2 with hρ_def
    set θ : ℝ := 1 - a with hθ_def
    have hθ0 : 0 < θ := by rw [hθ_def]; linarith
    have hθ1 : θ ≤ 1 := by rw [hθ_def]; linarith
    have hρ0 : 0 ≤ ρ := by rw [hρ_def]; nlinarith
    have hθp : 0 < θ ^ p := pow_pos hθ0 p
    set μ : ℝ := ρ ^ q / θ ^ p with hμ_def
    have hμ0 : 0 ≤ μ := by positivity
    have hμ1 : μ < 1 := by rw [hμ_def, div_lt_one hθp]; exact hμ
    obtain ⟨P0, hP0⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < 1 / 4 ^ q by positivity) hμ1
    set P := P0 + 1 with hP_def
    have hμP : μ ^ P ≤ 1 / 4 ^ q :=
      le_trans (pow_le_pow_of_le_one hμ0 hμ1.le (by omega)) hP0.le
    refine ⟨P, P, by omega, fun n hn => ?_⟩
    set m := n / P with hm_def
    have hm1 : 1 ≤ m := Nat.div_pos hn (by omega)
    have hPm : P * m ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n P
    have hmn : m ≤ n := Nat.div_le_self n P
    set d := p * n / q with hd_def
    have hdq : d * q ≤ p * n := Nat.div_mul_le_self _ _
    have hup := price_upper a ha0.le ha1 n d
    rw [← hρ_def, ← hθ_def] at hup

    have hθd : 0 < θ ^ d := pow_pos hθ0 d
    set X : ℝ := ρ ^ n / θ ^ d with hX_def
    have hX0 : 0 ≤ X := by positivity
    have hXq : X ^ q ≤ μ ^ n := by
      rw [hX_def, hμ_def, div_pow, div_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul,
        mul_comm n q]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact pow_le_pow_of_le_one hθ0.le hθ1 (by nlinarith [hdq])
    have hμn : μ ^ n ≤ (1 / 4 ^ q) ^ m := by
      calc μ ^ n ≤ μ ^ (P * m) := pow_le_pow_of_le_one hμ0 hμ1.le hPm
        _ = (μ ^ P) ^ m := pow_mul _ _ _
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hμP m
    set Y : ℝ := 7 / 6 * X * 2 ^ m with hY_def
    have hY0 : 0 ≤ Y := by positivity
    have hYq : Y ^ q ≤ 1 := by
      have e : ((4:ℝ) ^ q) ^ m = ((2:ℝ) ^ m) ^ q * ((2:ℝ) ^ m) ^ q := by
        rw [← mul_pow, ← mul_pow, ← pow_mul, ← pow_mul, mul_comm q m]; norm_num
      have h76 : (7 / 6 : ℝ) ≤ 2 ^ m := by
        have : (2:ℝ) ≤ 2 ^ m := by
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm1
        linarith
      have hZ : (7 / 6 : ℝ) ^ q ≤ ((2:ℝ) ^ m) ^ q := pow_le_pow_left₀ (by norm_num) h76 q
      have hZ0 : (0:ℝ) < ((2:ℝ) ^ m) ^ q := by positivity
      calc Y ^ q = (7 / 6) ^ q * X ^ q * ((2:ℝ) ^ m) ^ q := by rw [hY_def, mul_pow, mul_pow]
        _ ≤ (7 / 6) ^ q * (1 / 4 ^ q) ^ m * ((2:ℝ) ^ m) ^ q := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_trans hXq hμn) (by positivity)) (by positivity)
        _ = (7 / 6) ^ q / ((2:ℝ) ^ m) ^ q := by
            rw [one_div, inv_pow, e]; field_simp
        _ ≤ 1 := div_le_one_of_le₀ hZ hZ0.le
    have hY1 : Y ≤ 1 := (pow_le_one_iff_of_nonneg hY0 hq.ne').1 hYq
    have hgoal : (price n d : ℝ) ≤ (2:ℝ) ^ (5 * n - m) := by
      have e : (2:ℝ) ^ (5 * n - m) = 2 ^ (5 * n) / 2 ^ m := by
        rw [eq_div_iff (by positivity), ← pow_add]; congr 1; omega
      rw [e, le_div_iff₀ (by positivity)]
      calc (price n d : ℝ) * 2 ^ m ≤ 2 ^ (5 * n) * (7 / 6) * X * 2 ^ m :=
            mul_le_mul_of_nonneg_right hup (by positivity)
        _ = 2 ^ (5 * n) * Y := by rw [hY_def]; ring
        _ ≤ 2 ^ (5 * n) * 1 := mul_le_mul_of_nonneg_left hY1 (by positivity)
        _ = _ := by ring
    exact_mod_cast hgoal

end PEqualNP.Outside.L_meta_25575_aux

theorem PEqualNP.Outside.L_meta_25575 : let move := fun (mode letter : Nat) =>
    let near := letter.testBit 0
    let far := letter.testBit 1
    let hit := letter.testBit 2
    let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
      ((mode == 3) && near)
    let diagonal := !hit && (((mode == 1) && !near && !far) ||
      (mode == 2) || (mode == 3))
    (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (0, 0)
  let price := fun (n depth : Nat) =>
    ((List.range (8 ^ n)).map (fun codeWord =>
      2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum
  ∀ (p q : Nat), 0 < q →
    ((∃ (period start : Nat), 0 < period ∧
        ∀ n : Nat, start ≤ n →
          price n (p * n / q) ≤ 2 ^ (5 * n - n / period)) ↔ 14 * p < 9 * q) := by
  exact fun p q hq => PEqualNP.Outside.L_meta_25575_aux.main p q hq
