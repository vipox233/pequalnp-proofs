import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_974

def sg (b : Bool) : ℚ := if b then 1 else -1

def clip (t : ℚ) : ℚ := if t ≤ -1 then -1 else if 1 ≤ t then 1 else t

theorem sg_mul_self (b : Bool) : sg b * sg b = 1 := by
  cases b <;> simp [sg]

theorem sg_not (b : Bool) : sg (!b) = - sg b := by
  cases b <;> simp [sg]

theorem clip_neg (t : ℚ) : clip (-t) = - clip t := by
  unfold clip
  split_ifs <;> linarith

theorem clip_sg (b : Bool) (t : ℚ) : sg b * clip t = clip (sg b * t) := by
  cases b <;> simp [sg, clip_neg]

theorem clip_le (t : ℚ) : clip t ≤ 1 := by
  unfold clip
  split_ifs <;> linarith

theorem le_clip (t : ℚ) : -1 ≤ clip t := by
  unfold clip
  split_ifs <;> linarith

theorem pw (w ζ : ℚ) (hw : 0 ≤ w) :
    2 * min w (1/2) * (1 - 4 * ζ^2) ≤ clip (w + ζ) + clip (w - ζ) := by
  have hm : 0 ≤ min w (1/2) := le_min hw (by norm_num)
  by_cases hz : ζ^2 ≤ 1/4
  · have h1 : ζ ≤ 1/2 := by nlinarith
    have h2 : -(1/2) ≤ ζ := by nlinarith
    have h3 : 2 * min w (1/2) ≤ clip (w + ζ) + clip (w - ζ) := by
      unfold clip
      rcases le_total w (1/2) with h | h
      · rw [min_eq_left h]
        split_ifs <;> linarith
      · rw [min_eq_right h]
        split_ifs <;> linarith
    nlinarith [mul_nonneg hm (sq_nonneg ζ)]
  · have h3 : 0 ≤ clip (w + ζ) + clip (w - ζ) := by
      unfold clip
      split_ifs <;> linarith
    have h4 : 0 ≤ min w (1/2) * (4 * ζ^2 - 1) := mul_nonneg hm (by linarith [not_le.1 hz])
    nlinarith

def flipAt {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun σ := Function.update σ i (!σ i)
  invFun σ := Function.update σ i (!σ i)
  left_inv σ := by simp
  right_inv σ := by simp

theorem flipAt_self {n : ℕ} (i : Fin n) (σ : Fin n → Bool) : flipAt i σ i = !σ i := by
  simp [flipAt]

theorem flipAt_ne {n : ℕ} (i j : Fin n) (h : j ≠ i) (σ : Fin n → Bool) :
    flipAt i σ j = σ j := by
  simp [flipAt, Function.update_of_ne h]

theorem sign_cross {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    ∑ σ : Fin n → Bool, sg (σ i) * sg (σ j) = 0 := by
  have h1 := Equiv.sum_comp (flipAt i) (fun σ : Fin n → Bool => sg (σ i) * sg (σ j))
  have h2 : ∀ σ : Fin n → Bool,
      sg (flipAt i σ i) * sg (flipAt i σ j) = - (sg (σ i) * sg (σ j)) := by
    intro σ
    rw [flipAt_self, flipAt_ne i j hij.symm, sg_not]
    ring
  simp only [h2, Finset.sum_neg_distrib] at h1
  linarith

theorem parseval {n : ℕ} (u : Fin n → ℚ) :
    ∑ σ : Fin n → Bool, (∑ i, u i * sg (σ i))^2 = 2^n * ∑ i, (u i)^2 := by
  have h1 : ∀ σ : Fin n → Bool, (∑ i, u i * sg (σ i))^2
      = ∑ i, ∑ j, (u i * u j) * (sg (σ i) * sg (σ j)) := by
    intro σ
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ i : Fin n, ∑ σ : Fin n → Bool, ∑ j, (u i * u j) * (sg (σ i) * sg (σ j))
      = 2^n * (u i)^2 := by
    intro i
    rw [Finset.sum_comm, Finset.sum_eq_single i]
    · simp only [sg_mul_self, mul_one]
      simp
      ring
    · intro j _ hji
      rw [← Finset.mul_sum, sign_cross i j (Ne.symm hji), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [h2]
  rw [Finset.mul_sum]

def shiftAt {n H : ℕ} [NeZero H] (i : Fin n) (c : Fin H) :
    (Fin n → Fin H) ≃ (Fin n → Fin H) where
  toFun h := Function.update h i (h i + c)
  invFun h := Function.update h i (h i - c)
  left_inv h := by simp
  right_inv h := by simp

theorem collide {n H : ℕ} [NeZero H] (x x' : Fin n) (hne : x' ≠ x) :
    (∑ h : Fin n → Fin H, if h x' = h x then (1:ℚ) else 0) * H = (H:ℚ)^n := by
  have key : ∀ c : Fin H, (∑ h : Fin n → Fin H, if h x' + c = h x then (1:ℚ) else 0)
      = ∑ h : Fin n → Fin H, if h x' = h x then (1:ℚ) else 0 := by
    intro c
    rw [← Equiv.sum_comp (shiftAt x' c)
      (fun h : Fin n → Fin H => if h x' = h x then (1:ℚ) else 0)]
    apply Finset.sum_congr rfl
    intro h _
    simp [shiftAt, Function.update_of_ne hne.symm]
  have h1 : (∑ h : Fin n → Fin H, if h x' = h x then (1:ℚ) else 0) * H
      = ∑ c : Fin H, ∑ h : Fin n → Fin H, if h x' + c = h x then (1:ℚ) else 0 := by
    simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h1, Finset.sum_comm]
  have h2 : ∀ h : Fin n → Fin H, (∑ c : Fin H, if h x' + c = h x then (1:ℚ) else 0) = 1 := by
    intro h
    rw [Finset.sum_eq_single (h x - h x')]
    · simp
    · intro c _ hc
      have hne' : ¬ (h x' + c = h x) := by
        intro h'
        apply hc
        rw [← h']
        abel
      simp [hne']
    · intro hh
      exact absurd (Finset.mem_univ _) hh
  simp only [h2]
  simp

def T {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (h : Fin n → Fin H) (σ : Fin n → Bool)
    (β : Fin H) : ℚ :=
  ∑ x', if h x' = β then sg (σ x') * sg (t x') * v x' else 0

def uc {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n) (h : Fin n → Fin H)
    (x' : Fin n) : ℚ :=
  if x' ≠ x ∧ h x' = h x then sg (t x') * v x' else 0

theorem T_split {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n)
    (h : Fin n → Fin H) (σ : Fin n → Bool) :
    T v t h σ (h x) = sg (σ x) * sg (t x) * v x + ∑ x', uc v t x h x' * sg (σ x') := by
  unfold T
  have h1 : ∀ x' : Fin n, (if h x' = h x then sg (σ x') * sg (t x') * v x' else 0)
      = (if x' = x then sg (σ x) * sg (t x) * v x else 0) + uc v t x h x' * sg (σ x') := by
    intro x'
    unfold uc
    by_cases hx : x' = x
    · subst hx
      simp
    · by_cases hh : h x' = h x
      · simp [hx, hh]
        ring
      · simp [hx, hh]
  simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem A_eq {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n)
    (h : Fin n → Fin H) (σ : Fin n → Bool) :
    sg (σ x) * sg (t x) * clip (T v t h σ (h x))
      = clip (v x + sg (σ x) * sg (t x) * ∑ x', uc v t x h x' * sg (σ x')) := by
  rw [mul_assoc, clip_sg, clip_sg, T_split]
  congr 1
  have h1 := sg_mul_self (σ x)
  have h2 := sg_mul_self (t x)
  linear_combination (v x * sg (t x) * sg (t x)) * h1 + v x * h2

theorem Z_flip {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n)
    (h : Fin n → Fin H) (σ : Fin n → Bool) :
    ∑ x', uc v t x h x' * sg (flipAt x σ x') = ∑ x', uc v t x h x' * sg (σ x') := by
  apply Finset.sum_congr rfl
  intro x' _
  by_cases hx : x' = x
  · subst hx
    simp [uc]
  · rw [flipAt_ne x x' hx]

theorem sigma_bound {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n)
    (h : Fin n → Fin H) (hv : 0 ≤ v x) :
    min (v x) (1/2) * (2^n - 4 * (2^n * ∑ x', (uc v t x h x')^2))
      ≤ ∑ σ : Fin n → Bool, sg (σ x) * sg (t x) * clip (T v t h σ (h x)) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : (Fin n → Bool) → ℚ, ∀ σ, Z σ = ∑ x', uc v t x h x' * sg (σ x') :=
    ⟨_, fun _ => rfl⟩
  have hA : ∀ σ : Fin n → Bool, sg (σ x) * sg (t x) * clip (T v t h σ (h x))
      = clip (v x + sg (σ x) * sg (t x) * Z σ) := by
    intro σ
    rw [hZ]
    exact A_eq v t x h σ
  simp only [hA]
  have hflip : ∑ σ : Fin n → Bool, clip (v x + sg (σ x) * sg (t x) * Z σ)
      = ∑ σ : Fin n → Bool, clip (v x - sg (σ x) * sg (t x) * Z σ) := by
    rw [← Equiv.sum_comp (flipAt x)]
    apply Finset.sum_congr rfl
    intro σ _
    have h1 : Z (flipAt x σ) = Z σ := by
      rw [hZ, hZ]
      exact Z_flip v t x h σ
    rw [h1, flipAt_self, sg_not]
    congr 1
    ring
  have hpw : ∀ σ : Fin n → Bool, 2 * min (v x) (1/2) * (1 - 4 * (Z σ)^2)
      ≤ clip (v x + sg (σ x) * sg (t x) * Z σ) + clip (v x - sg (σ x) * sg (t x) * Z σ) := by
    intro σ
    have h1 := pw (v x) (sg (σ x) * sg (t x) * Z σ) hv
    have h2 : (sg (σ x) * sg (t x) * Z σ)^2 = (Z σ)^2 := by
      have a := sg_mul_self (σ x)
      have b := sg_mul_self (t x)
      linear_combination (Z σ)^2 * sg (t x) * sg (t x) * a + (Z σ)^2 * b
    rw [h2] at h1
    exact h1
  have hsum := Finset.sum_le_sum
    (fun σ (_ : σ ∈ (Finset.univ : Finset (Fin n → Bool))) => hpw σ)
  rw [Finset.sum_add_distrib, ← hflip] at hsum
  have hpar := parseval (uc v t x h)
  have hl : ∑ σ : Fin n → Bool, 2 * min (v x) (1/2) * (1 - 4 * (Z σ)^2)
      = 2 * min (v x) (1/2) * (2^n - 4 * (2^n * ∑ x', (uc v t x h x')^2)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [hZ]
    rw [hpar]
    simp
  rw [hl] at hsum
  linarith

theorem u_sum {n H : ℕ} [NeZero H] (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n) :
    (∑ h : Fin n → Fin H, ∑ x', (uc v t x h x')^2) * H ≤ (∑ x', (v x')^2) * (H:ℚ)^n := by
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro x' _
  by_cases hx : x' = x
  · have h0 : ∀ h : Fin n → Fin H, (uc v t x h x')^2 = 0 := by
      intro h
      simp [uc, hx]
    simp only [h0, Finset.sum_const_zero, zero_mul]
    positivity
  · have h1 : ∀ h : Fin n → Fin H,
        (uc v t x h x')^2 = (v x')^2 * (if h x' = h x then 1 else 0) := by
      intro h
      unfold uc
      by_cases hh : h x' = h x
      · simp only [hx, hh, ne_eq, not_false_eq_true, and_self, ite_true]
        have h2 := sg_mul_self (t x')
        linear_combination (v x')^2 * h2
      · simp [hh]
    simp only [h1, ← Finset.mul_sum]
    rw [mul_assoc, collide x x' hx]

theorem bias {n H : ℕ} (v : Fin n → ℚ) (t : Fin n → Bool) (x : Fin n)
    (hv : ∀ x', 0 ≤ v x') (hH : 0 < H) (hsum : 16 * ∑ x', (v x')^2 ≤ H) :
    3/4 * min (v x) (1/2) * ((H:ℚ)^n * 2^n)
      ≤ ∑ h : Fin n → Fin H, ∑ σ : Fin n → Bool,
          sg (σ x) * sg (t x) * clip (T v t h σ (h x)) := by
  have : NeZero H := ⟨hH.ne'⟩
  have hm : 0 ≤ min (v x) (1/2) := le_min (hv x) (by norm_num)
  have h1 := Finset.sum_le_sum
    (fun h (_ : h ∈ (Finset.univ : Finset (Fin n → Fin H))) => sigma_bound v t x h (hv x))
  refine le_trans ?_ h1
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h2 := u_sum (H := H) v t x
  have hHq : (0:ℚ) < H := by exact_mod_cast hH
  have hHn : (0:ℚ) ≤ (H:ℚ)^n := by positivity
  have h3 : ∑ h : Fin n → Fin H, ∑ x', (uc v t x h x')^2 ≤ (H:ℚ)^n / 16 := by
    have h4 : (∑ x', (v x')^2) * (H:ℚ)^n ≤ (H/16) * (H:ℚ)^n :=
      mul_le_mul_of_nonneg_right (by linarith) hHn
    have h5 : (∑ h : Fin n → Fin H, ∑ x', (uc v t x h x')^2) * H ≤ (H:ℚ)^n / 16 * H := by
      nlinarith
    exact le_of_mul_le_mul_right h5 hHq
  have h6 : (∑ _h : Fin n → Fin H, (2:ℚ)^n) = (H:ℚ)^n * 2^n := by simp
  rw [h6]
  have hp : (0:ℚ) ≤ 2^n := by positivity
  nlinarith [mul_nonneg (mul_nonneg hm hp) (sub_nonneg.2 h3)]

def IsInt (q : ℚ) : Prop := ∃ i : ℤ, (i : ℚ) = q

theorem isInt_add {a b : ℚ} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact ⟨i + j, by push_cast; ring⟩

theorem isInt_mul {a b : ℚ} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  exact ⟨i * j, by push_cast; ring⟩

theorem isInt_sg (b : Bool) : IsInt (sg b) := by
  cases b
  · exact ⟨-1, by simp [sg]⟩
  · exact ⟨1, by simp [sg]⟩

theorem isInt_nat (m : ℕ) : IsInt (m : ℚ) := ⟨m, by simp⟩

theorem isInt_sum {ι : Type} (s : Finset ι) (f : ι → ℚ) (h : ∀ i, IsInt (f i)) :
    IsInt (∑ i ∈ s, f i) :=
  Finset.sum_induction f IsInt (fun _ _ => isInt_add) ⟨0, by simp⟩ (fun i _ => h i)

theorem isInt_T {n H : ℕ} (Dn : ℕ) (v : Fin n → ℚ) (t : Fin n → Bool) (h : Fin n → Fin H)
    (σ : Fin n → Bool) (β : Fin H) (hv : ∀ x', IsInt (Dn * v x')) :
    IsInt (Dn * T v t h σ β) := by
  unfold T
  rw [Finset.mul_sum]
  apply isInt_sum
  intro x'
  split_ifs
  · have h1 : (Dn : ℚ) * (sg (σ x') * sg (t x') * v x') = sg (σ x') * sg (t x') * (Dn * v x') := by
      ring
    rw [h1]
    exact isInt_mul (isInt_mul (isInt_sg _) (isInt_sg _)) (hv x')
  · exact ⟨0, by simp⟩

theorem isInt_clip (Dn : ℕ) (t : ℚ) (h : IsInt (Dn * t)) : IsInt (Dn * clip t) := by
  unfold clip
  split_ifs
  · exact ⟨-(Dn : ℤ), by push_cast; ring⟩
  · exact ⟨(Dn : ℤ), by push_cast; ring⟩
  · exact h

theorem count_lt (N : ℕ) (θ : ℚ) (hint : IsInt θ) (h0 : 0 ≤ θ) (h1 : θ ≤ N) :
    ((Finset.univ.filter (fun r : Fin N => (r.val : ℚ) < θ)).card : ℚ) = θ := by
  obtain ⟨i, rfl⟩ := hint
  have hi : 0 ≤ i := by exact_mod_cast h0
  lift i to ℕ using hi
  have hj : i ≤ N := by exact_mod_cast h1
  have h2 : (Finset.univ.filter (fun r : Fin N => (r.val : ℚ) < ((i : ℤ) : ℚ)))
      = Finset.univ.filter (fun r : Fin N => r.val < i) := by
    ext r
    simp
  rw [h2, Fin.card_filter_val_lt, min_eq_right hj]
  simp

theorem count_not_lt (N : ℕ) (θ : ℚ) (hint : IsInt θ) (h0 : 0 ≤ θ) (h1 : θ ≤ N) :
    ((Finset.univ.filter (fun r : Fin N => ¬ (r.val : ℚ) < θ)).card : ℚ) = N - θ := by
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin N))) (fun r : Fin N => (r.val : ℚ) < θ)
  have h3 := count_lt N θ hint h0 h1
  have h4 : (((Finset.univ.filter (fun r : Fin N => (r.val : ℚ) < θ)).card
      + (Finset.univ.filter (fun r : Fin N => ¬ (r.val : ℚ) < θ)).card : ℕ) : ℚ) = N := by
    rw [h2]
    simp
  push_cast at h4
  linarith

theorem common_den {n k : ℕ} (w : Fin n → Fin k → ℚ) :
    ∃ Dn : ℕ, 0 < Dn ∧ ∀ x y, IsInt (Dn * w x y) := by
  refine ⟨∏ p : Fin n × Fin k, (w p.1 p.2).den,
    Finset.prod_pos (fun p _ => Rat.den_pos _), ?_⟩
  intro x y
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun p : Fin n × Fin k => (w p.1 p.2).den)
    (Finset.mem_univ (x, y))
  refine ⟨c * (w x y).num, ?_⟩
  rw [hc]
  push_cast
  have h1 := Rat.mul_den_eq_num (w x y)
  linear_combination (-(c : ℚ)) * h1

noncomputable def rd {n k H : ℕ} (truth : Fin n → Fin k → Bool) (w : Fin n → Fin k → ℚ)
    (D : Fin k → Finset (Fin n)) (Dn : ℕ) (h : Fin n → Fin H) (σ : Fin n → Bool)
    (r : Fin (2 * Dn)) (msg : Fin H × Bool) (y : Fin k) : Bool :=
  if hL : ∃ x', (D y).filter (fun x'' => h x'' = msg.1) = {x'} then
    truth (Classical.choose hL) y
  else decide ((r.val : ℚ) < Dn + Dn * (sg msg.2 *
    clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ msg.1)))

theorem cnt_free {n k H : ℕ} (truth : Fin n → Fin k → Bool) (w : Fin n → Fin k → ℚ)
    (D : Fin k → Finset (Fin n)) (Dn : ℕ) (hDn : ∀ x y, IsInt (Dn * w x y))
    (h : Fin n → Fin H) (σ : Fin n → Bool) (x : Fin n) (y : Fin k)
    (hno : ¬ ∃ x', (D y).filter (fun x'' => h x'' = h x) = {x'}) :
    ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
      rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ)
      = Dn + Dn * (sg (σ x) * sg (truth x y) *
          clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ (h x))) := by
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ (h x)) :=
    ⟨_, rfl⟩
  have hrd : ∀ r : Fin (2 * Dn), rd truth w D Dn h σ r (h x, σ x) y
      = decide ((r.val : ℚ) < Dn + Dn * (sg (σ x) * c)) := by
    intro r
    unfold rd
    rw [dite_eq_right_of_eq_false (eq_false hno), hc]
  have hint : IsInt ((Dn : ℚ) + Dn * (sg (σ x) * c)) := by
    have h1 : (Dn : ℚ) * (sg (σ x) * c) = sg (σ x) * (Dn * c) := by ring
    rw [h1, hc]
    exact isInt_add (isInt_nat Dn) (isInt_mul (isInt_sg _)
      (isInt_clip Dn _ (isInt_T Dn _ _ h σ (h x) (fun x' => hDn x' y))))
  have hb1 : -1 ≤ sg (σ x) * c := by
    rw [hc, clip_sg]
    exact le_clip _
  have hb2 : sg (σ x) * c ≤ 1 := by
    rw [hc, clip_sg]
    exact clip_le _
  have hD0 : (0 : ℚ) ≤ Dn := Nat.cast_nonneg Dn
  have h0 : (0 : ℚ) ≤ Dn + Dn * (sg (σ x) * c) := by nlinarith
  have h1 : (Dn : ℚ) + Dn * (sg (σ x) * c) ≤ ((2 * Dn : ℕ) : ℚ) := by
    push_cast
    nlinarith
  simp only [hrd]
  rw [← hc]
  cases htr : truth x y
  · have h2 : (Finset.univ.filter (fun r : Fin (2 * Dn) =>
        decide ((r.val : ℚ) < Dn + Dn * (sg (σ x) * c)) = false))
        = Finset.univ.filter (fun r : Fin (2 * Dn) => ¬ (r.val : ℚ) < Dn + Dn * (sg (σ x) * c)) := by
      ext r
      simp
    rw [h2, count_not_lt _ _ hint h0 h1]
    simp [sg]
    ring
  · have h2 : (Finset.univ.filter (fun r : Fin (2 * Dn) =>
        decide ((r.val : ℚ) < Dn + Dn * (sg (σ x) * c)) = true))
        = Finset.univ.filter (fun r : Fin (2 * Dn) => (r.val : ℚ) < Dn + Dn * (sg (σ x) * c)) := by
      ext r
      simp
    rw [h2, count_lt _ _ hint h0 h1]
    simp [sg]

theorem cnt_over {n k H : ℕ} (truth : Fin n → Fin k → Bool) (w : Fin n → Fin k → ℚ)
    (D : Fin k → Finset (Fin n)) (Dn : ℕ)
    (h : Fin n → Fin H) (σ : Fin n → Bool) (x : Fin n) (y : Fin k)
    (hov : (D y).filter (fun x'' => h x'' = h x) = {x}) :
    ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
      rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) = 2 * Dn := by
  have hex : ∃ x', (D y).filter (fun x'' => h x'' = h x) = {x'} := ⟨x, hov⟩
  have hch : Classical.choose hex = x := by
    have h1 := Classical.choose_spec hex
    exact (Finset.singleton_injective (hov.symm.trans h1)).symm
  have hrd : ∀ r : Fin (2 * Dn), rd truth w D Dn h σ r (h x, σ x) y = truth x y := by
    intro r
    unfold rd
    rw [dite_eq_left_of_eq_true (eq_true hex), hch]
  simp [hrd]

theorem cnt_lower_out {n k H : ℕ} (truth : Fin n → Fin k → Bool) (w : Fin n → Fin k → ℚ)
    (D : Fin k → Finset (Fin n)) (Dn : ℕ) (hDn : ∀ x y, IsInt (Dn * w x y))
    (h : Fin n → Fin H) (σ : Fin n → Bool) (x : Fin n) (y : Fin k) :
    (Dn : ℚ) + Dn * (sg (σ x) * sg (truth x y) *
          clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ (h x)))
        - 2 * Dn * (∑ x' ∈ D y, if h x' = h x then (1 : ℚ) else 0)
      ≤ ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
          rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) := by
  have hD0 : (0 : ℚ) ≤ Dn := Nat.cast_nonneg Dn
  have hcol0 : (0 : ℚ) ≤ ∑ x' ∈ D y, if h x' = h x then (1 : ℚ) else 0 :=
    Finset.sum_nonneg (fun x' _ => by split_ifs <;> norm_num)
  by_cases hov : ∃ x', (D y).filter (fun x'' => h x'' = h x) = {x'}
  · obtain ⟨x0, hx0⟩ := hov
    have hmem : x0 ∈ (D y).filter (fun x'' => h x'' = h x) := by
      rw [hx0]
      exact Finset.mem_singleton_self x0
    rw [Finset.mem_filter] at hmem
    have hcol1 : (1 : ℚ) ≤ ∑ x' ∈ D y, if h x' = h x then (1 : ℚ) else 0 := by
      have h1 := Finset.single_le_sum (f := fun x' => if h x' = h x then (1 : ℚ) else 0)
        (fun x' _ => by split_ifs <;> norm_num) hmem.1
      simp only [hmem.2, ite_true] at h1
      exact h1
    have hA : sg (σ x) * sg (truth x y) *
        clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ (h x)) ≤ 1 := by
      rw [mul_assoc, clip_sg, clip_sg]
      exact clip_le _
    have hcnt : (0 : ℚ) ≤ ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
          rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) := Nat.cast_nonneg _
    nlinarith
  · rw [cnt_free truth w D Dn hDn h σ x y hov]
    nlinarith

theorem cnt_lower_in {n k H : ℕ} (truth : Fin n → Fin k → Bool) (w : Fin n → Fin k → ℚ)
    (D : Fin k → Finset (Fin n)) (Dn : ℕ)
    (h : Fin n → Fin H) (σ : Fin n → Bool) (x : Fin n) (y : Fin k) (hx : x ∈ D y) :
    2 * (Dn : ℚ) * (1 - ∑ x' ∈ (D y).erase x, if h x' = h x then (1 : ℚ) else 0)
      ≤ ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
          rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) := by
  have hD0 : (0 : ℚ) ≤ Dn := Nat.cast_nonneg Dn
  have hcol0 : (0 : ℚ) ≤ ∑ x' ∈ (D y).erase x, if h x' = h x then (1 : ℚ) else 0 :=
    Finset.sum_nonneg (fun x' _ => by split_ifs <;> norm_num)
  by_cases hov : (D y).filter (fun x'' => h x'' = h x) = {x}
  · rw [cnt_over truth w D Dn h σ x y hov]
    nlinarith
  · have hex : ∃ x0 ∈ (D y).erase x, h x0 = h x := by
      by_contra hcon
      apply hov
      ext a
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hha⟩
        by_contra hax
        exact hcon ⟨a, Finset.mem_erase.2 ⟨hax, ha⟩, hha⟩
      · rintro rfl
        exact ⟨hx, rfl⟩
    obtain ⟨x0, hx0, hh0⟩ := hex
    have hcol1 : (1 : ℚ) ≤ ∑ x' ∈ (D y).erase x, if h x' = h x then (1 : ℚ) else 0 := by
      have h1 := Finset.single_le_sum (f := fun x' => if h x' = h x then (1 : ℚ) else 0)
        (fun x' _ => by split_ifs <;> norm_num) hx0
      simp only [hh0, ite_true] at h1
      exact h1
    have hcnt : (0 : ℚ) ≤ ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
          rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) := Nat.cast_nonneg _
    nlinarith

theorem col_sum {n H : ℕ} [NeZero H] (x : Fin n) (S : Finset (Fin n))
    (hS : ∀ x' ∈ S, x' ≠ x) :
    (∑ h : Fin n → Fin H, ∑ x' ∈ S, if h x' = h x then (1 : ℚ) else 0) * H
      = S.card * (H : ℚ)^n := by
  rw [Finset.sum_comm, Finset.sum_mul, Finset.sum_congr rfl (fun x' hx' => collide x x' (hS x' hx'))]
  simp

theorem sum_const_sigma {n : ℕ} (c : ℚ) : ∑ _σ : Fin n → Bool, c = 2^n * c := by simp

theorem sum_const_h {n H : ℕ} (c : ℚ) : ∑ _h : Fin n → Fin H, c = (H:ℚ)^n * c := by simp

theorem main (n k H : ℕ) (hH : 0 < H) (truth : Fin n → Fin k → Bool)
    (w : Fin n → Fin k → ℚ) (D : Fin k → Finset (Fin n)) (hw : ∀ x y, 0 ≤ w x y)
    (hs : ∀ y, 16 * (∑ x : Fin n, (w x y)^2) ≤ (H : ℚ)) :
    ∃ (z : ℕ) (send : Fin z → Fin n → Fin (2 * H))
      (read : Fin z → Fin (2 * H) → Fin k → Bool),
      0 < z ∧ ∀ x y,
        (1 + (if x ∈ D y then 1 else (3/4 : ℚ) * min (w x y) (1/2))
            - 2 * ((D y).card : ℚ) / (H : ℚ)) * (z : ℚ)
          ≤ 2 * (((Finset.univ : Finset (Fin z)).filter
              (fun seed => read seed (send seed x) y = truth x y)).card : ℚ) := by
  classical
  have hNZ : NeZero H := ⟨hH.ne'⟩
  obtain ⟨Dn, hDpos, hDn⟩ := common_den w
  have hcardΩ : Fintype.card ((Fin n → Fin H) × (Fin n → Bool) × Fin (2 * Dn))
      = H^n * (2^n * (2 * Dn)) := by simp
  obtain ⟨z, hz⟩ : ∃ z : ℕ, Fintype.card ((Fin n → Fin H) × (Fin n → Bool) × Fin (2 * Dn)) = z :=
    ⟨_, rfl⟩
  let e : ((Fin n → Fin H) × (Fin n → Bool) × Fin (2 * Dn)) ≃ Fin z := Fintype.equivFinOfCardEq hz
  let em : Fin H × Bool ≃ Fin (2 * H) := Fintype.equivFinOfCardEq (by simp [mul_comm])
  have hzN : z = H^n * (2^n * (2 * Dn)) := hz.symm.trans hcardΩ
  refine ⟨z, fun seed x => em ((e.symm seed).1 x, (e.symm seed).2.1 x),
    fun seed msg y => rd truth w D Dn (e.symm seed).1 (e.symm seed).2.1 (e.symm seed).2.2
      (em.symm msg) y, ?_, ?_⟩
  · rw [hzN]
    positivity
  intro x y
  have hhits : ((Finset.univ.filter (fun seed : Fin z =>
      rd truth w D Dn (e.symm seed).1 (e.symm seed).2.1 (e.symm seed).2.2
        (em.symm (em ((e.symm seed).1 x, (e.symm seed).2.1 x))) y = truth x y)).card : ℚ)
      = ∑ h : Fin n → Fin H, ∑ σ : Fin n → Bool,
          ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
            rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) := by
    rw [Finset.natCast_card_filter]
    refine (Fintype.sum_equiv e.symm _
      (fun ω : (Fin n → Fin H) × (Fin n → Bool) × Fin (2 * Dn) =>
        if rd truth w D Dn ω.1 ω.2.1 ω.2.2 (ω.1 x, ω.2.1 x) y = truth x y then (1:ℚ) else 0)
      (fun seed => ?_)).trans ?_
    · simp only [Equiv.symm_apply_apply]
    · rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun h _ => ?_)
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      rw [Finset.natCast_card_filter]
  have hP : (z : ℚ) = (H:ℚ)^n * 2^n * (2 * Dn) := by
    rw [hzN]
    push_cast
    ring
  have hHq : (0:ℚ) < H := by exact_mod_cast hH
  have hD0 : (0:ℚ) ≤ Dn := Nat.cast_nonneg Dn
  have h2n : (0:ℚ) ≤ 2^n := by positivity
  have goal' : (1 + (if x ∈ D y then 1 else (3/4 : ℚ) * min (w x y) (1/2))
            - 2 * ((D y).card : ℚ) / (H : ℚ)) * (z : ℚ)
          ≤ 2 * ∑ h : Fin n → Fin H, ∑ σ : Fin n → Bool,
          ((Finset.univ.filter (fun r : Fin (2 * Dn) =>
            rd truth w D Dn h σ r (h x, σ x) y = truth x y)).card : ℚ) := by
    by_cases hx : x ∈ D y
    · simp only [hx, ↓reduceIte]
      have h1 := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin n → Fin H))) =>
        Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Fin n → Bool))) =>
          cnt_lower_in truth w D Dn h σ x y hx))
      have h2 : ∑ h : Fin n → Fin H, ∑ _σ : Fin n → Bool,
          2 * (Dn : ℚ) * (1 - ∑ x' ∈ (D y).erase x, if h x' = h x then (1 : ℚ) else 0)
          = 2 * Dn * 2^n * ((H:ℚ)^n
            - ∑ h : Fin n → Fin H, ∑ x' ∈ (D y).erase x, if h x' = h x then (1 : ℚ) else 0) := by
        simp only [sum_const_sigma]
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_const_h]
        ring
      have hc := col_sum (H := H) x ((D y).erase x) (fun x' hx' => (Finset.mem_erase.1 hx').1)
      have hcard : (((D y).erase x).card : ℚ) ≤ ((D y).card : ℚ) := by
        exact_mod_cast Finset.card_erase_le
      have hC' : (∑ h : Fin n → Fin H, ∑ x' ∈ (D y).erase x, if h x' = h x then (1 : ℚ) else 0)
          ≤ ((D y).card : ℚ) * (H:ℚ)^n / H := by
        rw [le_div_iff₀ hHq, hc]
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      have e1 : (1 + 1 - 2 * ((D y).card : ℚ) / H) * ((H:ℚ)^n * 2^n * (2 * Dn))
          = 4 * Dn * 2^n * (H:ℚ)^n - 4 * Dn * 2^n * (((D y).card : ℚ) * (H:ℚ)^n / H) := by
        ring
      rw [hP, e1]
      have h4 : (0:ℚ) ≤ 4 * Dn * 2^n := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hC' h4, h1, h2]
    · simp only [hx, ↓reduceIte]
      have h1 := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin n → Fin H))) =>
        Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Fin n → Bool))) =>
          cnt_lower_out truth w D Dn hDn h σ x y))
      have h2 : ∑ h : Fin n → Fin H, ∑ σ : Fin n → Bool,
          ((Dn : ℚ) + Dn * (sg (σ x) * sg (truth x y) *
              clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ (h x)))
            - 2 * Dn * (∑ x' ∈ D y, if h x' = h x then (1 : ℚ) else 0))
          = Dn * ((H:ℚ)^n * 2^n)
            + Dn * (∑ h : Fin n → Fin H, ∑ σ : Fin n → Bool, sg (σ x) * sg (truth x y) *
              clip (T (fun x' => w x' y) (fun x' => truth x' y) h σ (h x)))
            - 2 * Dn * 2^n * (∑ h : Fin n → Fin H, ∑ x' ∈ D y,
                if h x' = h x then (1 : ℚ) else 0) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_const_sigma,
          sum_const_h, ← Finset.mul_sum]
        ring
      have hb := bias (H := H) (fun x' => w x' y) (fun x' => truth x' y) x
        (fun x' => hw x' y) hH (hs y)
      have hc := col_sum (H := H) x (D y) (fun x' hx' => by
        rintro rfl
        exact hx hx')
      have hC : (∑ h : Fin n → Fin H, ∑ x' ∈ D y, if h x' = h x then (1 : ℚ) else 0)
          = ((D y).card : ℚ) * (H:ℚ)^n / H := by
        rw [eq_div_iff hHq.ne', hc]
      have e1 : (1 + 3/4 * min (w x y) (1/2) - 2 * ((D y).card : ℚ) / H)
            * ((H:ℚ)^n * 2^n * (2 * Dn))
          = 2 * Dn * ((H:ℚ)^n * 2^n) + 2 * Dn * (3/4 * min (w x y) (1/2) * ((H:ℚ)^n * 2^n))
            - 4 * Dn * 2^n * (((D y).card : ℚ) * (H:ℚ)^n / H) := by
        ring
      rw [hP, e1]
      have hb' := mul_le_mul_of_nonneg_left hb hD0
      rw [hC] at h2
      nlinarith [hb', h1, h2]
  rw [← hhits] at goal'
  exact goal'

end PEqualNP.Outside.L_lib_974

theorem PEqualNP.Outside.L_lib_974 : (∀ (n k H : Nat), 0 < H →
  ∀ (truth : Fin n → Fin k → Bool) (w : Fin n → Fin k → ℚ)
    (D : Fin k → Finset (Fin n)),
    (∀ x y, 0 ≤ w x y) →
    (∀ y, 16*(∑ x : Fin n, (w x y)^2) ≤ (H : ℚ)) →
    ∃ (z : Nat) (send : Fin z → Fin n → Fin (2*H))
      (read : Fin z → Fin (2*H) → Fin k → Bool),
      0 < z ∧ ∀ x y,
        let reward : ℚ := if x ∈ D y then 1 else (3/4 : ℚ)*min (w x y) (1/2)
        let hits := ((Finset.univ : Finset (Fin z)).filter
          (fun seed => read seed (send seed x) y = truth x y)).card
        (1+reward-2*((D y).card : ℚ)/(H : ℚ))*(z : ℚ) ≤ 2*(hits : ℚ)) := by
  intro n k H hH truth w D hw hs
  obtain ⟨z, send, read, hz, hmain⟩ := PEqualNP.Outside.L_lib_974.main n k H hH truth w D hw hs
  exact ⟨z, send, read, hz, fun x y => hmain x y⟩
