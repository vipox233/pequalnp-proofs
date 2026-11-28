import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1053_aux

open Finset

variable {t : ℕ}

abbrev Ed (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}

def vF (k : Fin 3) : ℤ := if k = 0 then 0 else if k = 1 then 1 else -1

theorem vF0 : vF 0 = 0 := rfl
theorem vF1 : vF 1 = 1 := rfl
theorem vF2 : vF 2 = -1 := rfl

def Fm (a : Ed t → ℤ) (x : Fin t → ℤ) : ℤ := ∑ e : Ed t, a e * x e.val.1 * x e.val.2

def Am (a : Ed t → ℤ) (m n : Fin t) : ℤ :=
  ∑ e : Ed t, ((if e.val.1 = m ∧ e.val.2 = n then a e else 0) +
    (if e.val.2 = m ∧ e.val.1 = n then a e else 0))

def Lf (a : Ed t → ℤ) (m : Fin t) (x : Fin t → ℤ) : ℤ := ∑ n, Am a m n * x n

theorem Am_symm (a : Ed t → ℤ) (m n : Fin t) : Am a m n = Am a n m := by
  unfold Am
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [add_comm]
  congr 1
  · by_cases h1 : e.val.2 = m <;> by_cases h2 : e.val.1 = n <;> simp [h1, h2]
  · by_cases h1 : e.val.1 = m <;> by_cases h2 : e.val.2 = n <;> simp [h1, h2]

theorem Am_diag (a : Ed t → ℤ) (m : Fin t) : Am a m m = 0 := by
  unfold Am
  refine Finset.sum_eq_zero (fun e _ => ?_)
  have h := e.prop
  rw [if_neg, if_neg, add_zero]
  · rintro ⟨h1, h2⟩; rw [h1, h2] at h; exact lt_irrefl _ h
  · rintro ⟨h1, h2⟩; rw [h1, h2] at h; exact lt_irrefl _ h

theorem Lf_eq (a : Ed t → ℤ) (m : Fin t) (x : Fin t → ℤ) :
    Lf a m x = ∑ e : Ed t, ((if e.val.1 = m then a e * x e.val.2 else 0) +
      (if e.val.2 = m then a e * x e.val.1 else 0)) := by
  unfold Lf Am
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · by_cases h : e.val.1 = m
    · simp [h, ite_mul]
    · simp [h]
  · by_cases h : e.val.2 = m
    · simp [h, ite_mul]
    · simp [h]

theorem Fm_update (a : Ed t → ℤ) (x : Fin t → ℤ) (k : Fin t) (s : ℤ) :
    Fm a (Function.update x k s) = Fm a (Function.update x k 0) + s * Lf a k x := by
  rw [Lf_eq, Finset.mul_sum]
  unfold Fm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.prop
  by_cases h1 : e.val.1 = k
  · have h2 : e.val.2 ≠ k := fun h => hne (h1.trans h.symm)
    simp [Function.update_apply, h1, h2]
    ring
  · by_cases h2 : e.val.2 = k
    · simp [Function.update_apply, h1, h2]
      ring
    · simp [Function.update_apply, h1, h2]

theorem Lf_update (a : Ed t → ℤ) (m : Fin t) (x : Fin t → ℤ) (k : Fin t) (s : ℤ) :
    Lf a m (Function.update x k s) = Lf a m x + Am a m k * (s - x k) := by
  unfold Lf
  have : ∀ n, Am a m n * Function.update x k s n =
      Am a m n * x n + if n = k then Am a m n * (s - x k) else 0 := by
    intro n
    by_cases h : n = k
    · subst h; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun n _ => this n), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem Fm2 (a : Ed t → ℤ) (x : Fin t → ℤ) : 2 * Fm a x = ∑ m, x m * Lf a m x := by
  simp_rw [Lf_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold Fm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  ring

theorem Fm_slice (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (x : Fin t → ℤ) (hi : x i = 0)
    (hj : x j = 0) (s r : ℤ) :
    Fm a (Function.update (Function.update x i s) j r) =
      Fm a x + s * Lf a i x + r * Lf a j x + Am a i j * s * r := by
  rw [Fm_update a (Function.update x i s) j r]
  have e1 : Function.update (Function.update x i s) j 0 = Function.update x i s := by
    rw [Function.update_eq_self_iff, Function.update_of_ne hij.symm, hj]
  have e2 : Function.update x i 0 = x := by
    rw [Function.update_eq_self_iff, hi]
  rw [e1, Fm_update a x i s, Lf_update, e2, Am_symm a j i, hi]
  ring

theorem upd_base {α : Type} {i j : Fin t} (hij : i ≠ j) (y : Fin t → α) (z s r : α) :
    Function.update (Function.update y i s) j r =
      Function.update (Function.update (Function.update (Function.update y i z) j z) i s) j r := by
  funext m
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem Fm_slice' (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (y : Fin t → ℤ) (s r : ℤ) :
    Fm a (Function.update (Function.update y i s) j r) =
      Fm a (Function.update (Function.update y i 0) j 0)
      + s * Lf a i (Function.update (Function.update y i 0) j 0)
      + r * Lf a j (Function.update (Function.update y i 0) j 0) + Am a i j * s * r := by
  rw [upd_base hij y 0 s r]
  apply Fm_slice a hij
  · rw [Function.update_of_ne hij, Function.update_self]
  · rw [Function.update_self]


def X (p : Fin t → Fin 3) : Fin t → ℤ := fun k => vF (p k)

def absV (y : Fin t → ℤ) : Fin t → ℤ := fun k => |y k|

def cnt (a : Ed t → ℤ) : ℕ :=
  ((Finset.univ : Finset (Fin t → Fin 3)).filter
    (fun p => Fm a (X p) ≠ 0 ∨ Fm a (absV (X p)) ≠ 0)).card

def Pr (a : Ed t → ℤ) (p : Fin t → Fin 3) : Prop := Fm a (X p) ≠ 0 ∨ Fm a (absV (X p)) ≠ 0

instance (a : Ed t → ℤ) : DecidablePred (Pr a) := fun p => by unfold Pr; infer_instance

theorem cnt_eq (a : Ed t → ℤ) : cnt a = ∑ p, if Pr a p then 1 else 0 := by
  unfold cnt Pr
  rw [Finset.card_filter]

def sc (a : Ed t → ℤ) (i j : Fin t) (q : Fin t → Fin 3) : ℕ :=
  ∑ u : Fin 3, ∑ v : Fin 3, if Pr a (Function.update (Function.update q i u) j v) then 1 else 0

theorem avg1 (k : Fin t) (F : (Fin t → Fin 3) → ℕ) :
    ∑ p, ∑ w : Fin 3, F (Function.update p k w) = 3 * ∑ p, F p := by
  let e : (Fin t → Fin 3) × Fin 3 ≃ (Fin t → Fin 3) × Fin 3 :=
    { toFun := fun pw => (Function.update pw.1 k pw.2, pw.1 k)
      invFun := fun pw => (Function.update pw.1 k pw.2, pw.1 k)
      left_inv := fun pw => by simp
      right_inv := fun pw => by simp }
  have h1 : ∑ p, ∑ w : Fin 3, F (Function.update p k w) =
      ∑ pw : (Fin t → Fin 3) × Fin 3, F (e pw).1 := by
    rw [Fintype.sum_prod_type]; rfl
  rw [h1, Equiv.sum_comp e (fun pw => F pw.1), Fintype.sum_prod_type, Finset.mul_sum]
  simp [mul_comm]

theorem avg2 (i j : Fin t) (F : (Fin t → Fin 3) → ℕ) :
    ∑ p, ∑ u : Fin 3, ∑ v : Fin 3, F (Function.update (Function.update p i u) j v) =
      9 * ∑ p, F p := by
  have h1 := avg1 i (fun q => ∑ v : Fin 3, F (Function.update q j v))
  have h2 := avg1 j F
  rw [h1, h2]; ring

theorem card_mask : Fintype.card (Fin t → Fin 3) = 3 ^ t := by
  simp

theorem sum_const_mask (c : ℕ) : ∑ _p : Fin t → Fin 3, c = c * 3 ^ t := by
  simp [Finset.sum_const, Finset.card_univ, mul_comm]

theorem sum9aux : ∀ w0 z0 : Fin 3,
    37 = ∑ w : Fin 3, ∑ z : Fin 3, (4 + if w = w0 ∧ z = z0 then 1 else 0) := by
  decide

theorem sum9 (f : Fin 3 → Fin 3 → ℕ) (h4 : ∀ w z, 4 ≤ f w z) (w0 z0 : Fin 3)
    (h5 : 5 ≤ f w0 z0) : 37 ≤ ∑ w, ∑ z, f w z := by
  calc 37 = ∑ w : Fin 3, ∑ z : Fin 3, (4 + if w = w0 ∧ z = z0 then 1 else 0) := by
        exact sum9aux w0 z0
    _ ≤ ∑ w, ∑ z, f w z := by
        refine Finset.sum_le_sum (fun w _ => Finset.sum_le_sum (fun z _ => ?_))
        split_ifs with h
        · obtain ⟨rfl, rfl⟩ := h; exact h5
        · simpa using h4 w z

theorem X_upd (q : Fin t → Fin 3) (k : Fin t) (w : Fin 3) :
    X (Function.update q k w) = Function.update (X q) k (vF w) := by
  show vF ∘ (Function.update q k w) = Function.update (vF ∘ q) k (vF w)
  exact Function.comp_update _ _ _ _

theorem absV_upd (y : Fin t → ℤ) (k : Fin t) (s : ℤ) :
    absV (Function.update y k s) = Function.update (absV y) k |s| := by
  show (fun x => |x|) ∘ (Function.update y k s) = Function.update ((fun x => |x|) ∘ y) k |s|
  exact Function.comp_update _ _ _ _

def R3 (s q : ℤ) : ℕ := ∑ v : Fin 3, if s * vF v + q ≠ 0 then 1 else 0

theorem R3_lb (s q : ℤ) : 2 ≤ R3 s q ∨ s = 0 := by
  unfold R3
  rw [Fin.sum_univ_three, vF0, vF1, vF2]
  simp only [mul_zero, zero_add, mul_one, mul_neg]
  split_ifs <;> omega

theorem R3_zero (s q : ℤ) : s = 0 → q ≠ 0 → 3 ≤ R3 s q := by
  intro hs hq
  subst hs
  unfold R3
  rw [Fin.sum_univ_three]
  simp [hq]

def N3 (A b c d : ℤ) : ℕ := ∑ u : Fin 3, R3 (A * vF u + c) (b * vF u + d)

theorem N3_eq (A b c d : ℤ) :
    N3 A b c d = R3 c d + R3 (A + c) (b + d) + R3 (-A + c) (-b + d) := by
  unfold N3
  rw [Fin.sum_univ_three, vF0, vF1, vF2]
  simp only [mul_zero, zero_add, mul_one, mul_neg]

theorem N3_ge4 {A : ℤ} (hA : A ≠ 0) (b c d : ℤ) : 4 ≤ N3 A b c d := by
  rw [N3_eq]
  have h1 := R3_lb c d
  have h2 := R3_lb (A + c) (b + d)
  have h3 := R3_lb (-A + c) (-b + d)
  omega

theorem N3_le4 {A : ℤ} (hA : A ≠ 0) (b c d : ℤ) (h : N3 A b c d ≤ 4) :
    (c = 0 ∧ d = 0) ∨ (c = -A ∧ d = -b) ∨ (c = A ∧ d = b) := by
  rw [N3_eq] at h
  have h1 := R3_lb c d
  have h2 := R3_lb (A + c) (b + d)
  have h3 := R3_lb (-A + c) (-b + d)
  have z1 := R3_zero c d
  have z2 := R3_zero (A + c) (b + d)
  have z3 := R3_zero (-A + c) (-b + d)
  omega

def B0 (i j : Fin t) (q : Fin t → Fin 3) : Fin t → ℤ :=
  Function.update (Function.update (X q) i 0) j 0

theorem sc_ge (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (q : Fin t → Fin 3) :
    N3 (Am a i j) (Lf a i (B0 i j q)) (Lf a j (B0 i j q)) (Fm a (B0 i j q)) ≤ sc a i j q := by
  unfold N3 sc R3
  refine Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => ?_))
  have hF : Fm a (X (Function.update (Function.update q i u) j v)) =
      (Am a i j * vF u + Lf a j (B0 i j q)) * vF v + (Lf a i (B0 i j q) * vF u + Fm a (B0 i j q)) := by
    rw [X_upd, X_upd, Fm_slice' a hij]
    unfold B0
    ring
  split_ifs with h1 h2
  · exact le_refl _
  · exfalso; apply h2; unfold Pr; left; rw [hF]; exact h1
  · exact Nat.zero_le _
  · exact le_refl _

theorem sc_ge4 (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0)
    (q : Fin t → Fin 3) : 4 ≤ sc a i j q :=
  le_trans (N3_ge4 hA _ _ _) (sc_ge a hij q)

def Crit (a : Ed t → ℤ) (i j : Fin t) (Y : Fin t → ℤ) : Prop :=
  (Lf a j Y ≠ 0 ∧ Lf a j Y ≠ Am a i j ∧ Lf a j Y ≠ -Am a i j) ∨
    Am a i j * Fm a Y ≠ Lf a i Y * Lf a j Y

theorem sc_ge5 (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0)
    (q : Fin t → Fin 3) (h : Crit a i j (B0 i j q)) : 5 ≤ sc a i j q := by
  by_contra hlt
  rw [not_le] at hlt
  have := N3_le4 hA _ _ _ (le_trans (sc_ge a hij q) (by omega))
  unfold Crit at h
  rcases this with ⟨hc, hd⟩ | ⟨hc, hd⟩ | ⟨hc, hd⟩
  · rcases h with h | h
    · exact h.1 hc
    · apply h; rw [hc, hd]; ring
  · rcases h with h | h
    · exact h.2.2 hc
    · apply h; rw [hc, hd]; ring
  · rcases h with h | h
    · exact h.2.1 hc
    · apply h; rw [hc, hd]; ring

theorem low_bound (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) :
    4 * 3 ^ t ≤ 9 * cnt a := by
  have h := avg2 i j (fun p => if Pr a p then 1 else 0)
  rw [cnt_eq, ← h, ← sum_const_mask]
  exact Finset.sum_le_sum (fun q _ => sc_ge4 a hij hA q)

theorem cube_bound (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) (m n : Fin t)
    (h : ∀ p, ∃ w z, 5 ≤ sc a i j (Function.update (Function.update p m w) n z)) :
    37 * 3 ^ t ≤ 81 * cnt a := by
  have h1 := avg2 i j (fun p => if Pr a p then 1 else 0)
  have h2 := avg2 m n (sc a i j)
  have e81 : 81 * cnt a = ∑ p, ∑ w : Fin 3, ∑ z : Fin 3,
      sc a i j (Function.update (Function.update p m w) n z) := by
    rw [h2, cnt_eq]
    unfold sc
    rw [h1]; ring
  rw [e81, ← sum_const_mask]
  refine Finset.sum_le_sum (fun p _ => ?_)
  obtain ⟨w, z, hwz⟩ := h p
  exact sum9 _ (fun w z => sc_ge4 a hij hA _) w z hwz

theorem Kbound {A : ℤ} (hA : A ≠ 0) (β β' : ℤ) :
    5 ≤ ∑ u : Fin 3, ∑ v : Fin 3,
      (if (vF u + 1) * (A * vF v + β) ≠ 0 ∨ (|vF u| + 1) * (A * |vF v| + β') ≠ 0 then 1 else 0) := by
  simp only [Fin.sum_univ_three, vF0, vF1, vF2]
  norm_num
  split_ifs <;> omega
theorem pick1 (A C γ : ℤ) (h0 : γ ≠ 0) (h1 : γ ≠ A) (h2 : γ ≠ -A) :
    ∃ z : Fin 3, C + γ * vF z ≠ 0 ∧ C + γ * vF z ≠ A ∧ C + γ * vF z ≠ -A := by
  by_contra H
  simp only [not_exists] at H
  have e0 := H 0
  have e1 := H 1
  have e2 := H 2
  simp only [vF0, vF1, vF2, mul_zero, add_zero, mul_one, mul_neg] at e0 e1 e2
  omega
theorem pick2 (A C γ δ : ℤ) (hA : A ≠ 0) (hγ : γ = A ∨ γ = -A) (hδ : δ = A ∨ δ = -A) :
    ∃ w z : Fin 3, C + γ * vF w + δ * vF z ≠ 0 ∧ C + γ * vF w + δ * vF z ≠ A ∧
      C + γ * vF w + δ * vF z ≠ -A := by
  by_contra H
  simp only [not_exists] at H
  have e11 := H 1 1
  have e12 := H 1 2
  have e21 := H 2 1
  have e22 := H 2 2
  simp only [vF1, vF2, mul_one, mul_neg] at e11 e12 e21 e22
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;> omega
theorem pick3 (A D L B C β γ : ℤ) (h : β * γ ≠ 0) :
    ∃ z : Fin 3, A * (D + vF z * L) ≠ (B + β * vF z) * (C + γ * vF z) := by
  by_contra H
  simp only [not_exists, not_not] at H
  have e0 := H 0
  have e1 := H 1
  have e2 := H 2
  simp only [vF0, vF1, vF2] at e0 e1 e2
  apply h
  have : 2 * (β * γ) = 0 := by linear_combination 2 * e0 - e1 - e2
  linarith
theorem pick4 (A D Lm Ln K B C βm βn γm γn : ℤ) (h : A * K ≠ βm * γn + βn * γm) :
    ∃ w z : Fin 3, A * (D + Lm * vF w + Ln * vF z + K * vF w * vF z) ≠
      (B + βm * vF w + βn * vF z) * (C + γm * vF w + γn * vF z) := by
  by_contra H
  simp only [not_exists, not_not] at H
  have e11 := H 1 1
  have e12 := H 1 2
  have e21 := H 2 1
  have e22 := H 2 2
  simp only [vF1, vF2] at e11 e12 e21 e22
  apply h
  have : 4 * (A * K - (βm * γn + βn * γm)) = 0 := by
    linear_combination e11 - e12 - e21 + e22
  linarith
theorem count4 : ∀ g g' : Fin 3, (∑ u : Fin 3, ∑ v : Fin 3,
    (if (vF u - vF g) * (vF v - vF g') ≠ 0 ∨ (|vF u| - |vF g|) * (|vF v| - |vF g'|) ≠ 0
      then 1 else 0) : ℕ) = 4 := by
  decide

theorem B0_upd {i j m : Fin t} (hmi : m ≠ i) (hmj : m ≠ j) (q : Fin t → Fin 3) (w : Fin 3) :
    B0 i j (Function.update q m w) = Function.update (B0 i j q) m (vF w) := by
  unfold B0
  rw [X_upd]
  funext k
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem cube_crit (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) (m n : Fin t)
    (hmi : m ≠ i) (hmj : m ≠ j) (hni : n ≠ i) (hnj : n ≠ j)
    (h : ∀ Y : Fin t → ℤ, ∃ w z : Fin 3,
      Crit a i j (Function.update (Function.update Y m (vF w)) n (vF z))) :
    37 * 3 ^ t ≤ 81 * cnt a := by
  apply cube_bound a hij hA m n
  intro p
  obtain ⟨w, z, hc⟩ := h (B0 i j p)
  refine ⟨w, z, sc_ge5 a hij hA _ ?_⟩
  rw [B0_upd hni hnj, B0_upd hmi hmj]
  exact hc

theorem Lf_upd2 (a : Ed t → ℤ) (k : Fin t) (Y : Fin t → ℤ) {m n : Fin t} (hmn : m ≠ n)
    (s r : ℤ) : Lf a k (Function.update (Function.update Y m s) n r) =
      Lf a k Y - Am a k m * Y m - Am a k n * Y n + Am a k m * s + Am a k n * r := by
  rw [Lf_update, Lf_update, Function.update_of_ne hmn.symm]
  ring

theorem bad1 (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) {m : Fin t}
    (hmi : m ≠ i) (hmj : m ≠ j) (h0 : Am a j m ≠ 0) (h1 : Am a j m ≠ Am a i j)
    (h2 : Am a j m ≠ -Am a i j) : 37 * 3 ^ t ≤ 81 * cnt a := by
  apply cube_crit a hij hA m m hmi hmj hmi hmj
  intro Y
  obtain ⟨z, hz⟩ := pick1 (Am a i j) (Lf a j Y - Am a j m * Y m) (Am a j m) h0 h1 h2
  refine ⟨0, z, Or.inl ?_⟩
  rw [Function.update_idem, Lf_update]
  have : Lf a j Y + Am a j m * (vF z - Y m) = Lf a j Y - Am a j m * Y m + Am a j m * vF z := by
    ring
  rw [this]; exact hz

theorem bad2 (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) {m n : Fin t}
    (hmi : m ≠ i) (hmj : m ≠ j) (hni : n ≠ i) (hnj : n ≠ j) (hmn : m ≠ n)
    (hm : Am a j m = Am a i j ∨ Am a j m = -Am a i j)
    (hn : Am a j n = Am a i j ∨ Am a j n = -Am a i j) : 37 * 3 ^ t ≤ 81 * cnt a := by
  apply cube_crit a hij hA m n hmi hmj hni hnj
  intro Y
  obtain ⟨w, z, hwz⟩ := pick2 (Am a i j) (Lf a j Y - Am a j m * Y m - Am a j n * Y n)
    (Am a j m) (Am a j n) hA hm hn
  refine ⟨w, z, Or.inl ?_⟩
  rw [Lf_upd2 a j Y hmn]
  exact hwz

theorem bad3d (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) {m : Fin t}
    (hmi : m ≠ i) (hmj : m ≠ j) (h : Am a i m * Am a j m ≠ 0) : 37 * 3 ^ t ≤ 81 * cnt a := by
  apply cube_crit a hij hA m m hmi hmj hmi hmj
  intro Y
  obtain ⟨z, hz⟩ := pick3 (Am a i j) (Fm a (Function.update Y m 0)) (Lf a m Y)
    (Lf a i Y - Am a i m * Y m) (Lf a j Y - Am a j m * Y m) (Am a i m) (Am a j m) h
  refine ⟨0, z, Or.inr ?_⟩
  rw [Function.update_idem, Fm_update, Lf_update, Lf_update]
  intro heq
  apply hz
  linear_combination heq

theorem bad3o (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) {m n : Fin t}
    (hmi : m ≠ i) (hmj : m ≠ j) (hni : n ≠ i) (hnj : n ≠ j) (hmn : m ≠ n)
    (h : Am a i j * Am a m n ≠ Am a i m * Am a j n + Am a i n * Am a j m) :
    37 * 3 ^ t ≤ 81 * cnt a := by
  apply cube_crit a hij hA m n hmi hmj hni hnj
  intro Y
  obtain ⟨w, z, hwz⟩ := pick4 (Am a i j) (Fm a (Function.update (Function.update Y m 0) n 0))
    (Lf a m (Function.update (Function.update Y m 0) n 0))
    (Lf a n (Function.update (Function.update Y m 0) n 0)) (Am a m n)
    (Lf a i Y - Am a i m * Y m - Am a i n * Y n) (Lf a j Y - Am a j m * Y m - Am a j n * Y n)
    (Am a i m) (Am a i n) (Am a j m) (Am a j n) h
  refine ⟨w, z, Or.inr ?_⟩
  rw [Fm_slice' a hmn, Lf_upd2 a i Y hmn, Lf_upd2 a j Y hmn]
  intro heq
  apply hwz
  linear_combination heq

theorem key_det (a : Ed t → ℤ) {i j : Fin t}
    (h3 : ∀ m n, m ≠ i → m ≠ j → n ≠ i → n ≠ j →
      Am a i j * Am a m n = Am a i m * Am a j n + Am a i n * Am a j m)
    (y : Fin t → ℤ) (hi : y i = 0) (hj : y j = 0) :
    Am a i j * Fm a y = Lf a i y * Lf a j y := by
  have e1 : ∀ m n, Am a i j * (y m * (Am a m n * y n)) =
      (Am a i m * y m) * (Am a j n * y n) + (Am a i n * y n) * (Am a j m * y m) := by
    intro m n
    by_cases hm : m = i
    · rw [hm, hi]; ring
    by_cases hm' : m = j
    · rw [hm', hj]; ring
    by_cases hn : n = i
    · rw [hn, hi]; ring
    by_cases hn' : n = j
    · rw [hn', hj]; ring
    have := h3 m n hm hm' hn hn'
    linear_combination (y m * y n) * this
  have s0 : Am a i j * Fm a y * 2 = ∑ m, ∑ n, Am a i j * (y m * (Am a m n * y n)) := by
    rw [mul_assoc, mul_comm (Fm a y) 2, Fm2, Finset.mul_sum]
    unfold Lf
    simp_rw [Finset.mul_sum]
  have s3 : ∑ m, ∑ n, Am a i j * (y m * (Am a m n * y n)) =
      ∑ m, ∑ n, (Am a i m * y m) * (Am a j n * y n) +
        ∑ m, ∑ n, (Am a i n * y n) * (Am a j m * y m) := by
    simp_rw [e1, Finset.sum_add_distrib]
  have s1 : ∑ m, ∑ n, (Am a i m * y m) * (Am a j n * y n) = Lf a i y * Lf a j y := by
    unfold Lf; rw [Finset.sum_mul_sum]
  have s2 : ∑ m, ∑ n, (Am a i n * y n) * (Am a j m * y m) = Lf a i y * Lf a j y := by
    unfold Lf; rw [Finset.sum_comm, Finset.sum_mul_sum]
  linarith [s0, s3, s1, s2]

theorem FT (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j)
    (h3 : ∀ m n, m ≠ i → m ≠ j → n ≠ i → n ≠ j →
      Am a i j * Am a m n = Am a i m * Am a j n + Am a i n * Am a j m)
    (y : Fin t → ℤ) :
    Am a i j * Fm a y = (Am a i j * y i + Lf a j (Function.update (Function.update y i 0) j 0)) *
      (Am a i j * y j + Lf a i (Function.update (Function.update y i 0) j 0)) := by
  have hy : Fm a y = Fm a (Function.update (Function.update y i (y i)) j (y j)) := by
    rw [Function.update_eq_self, Function.update_eq_self]
  have k := key_det a h3 (Function.update (Function.update y i 0) j 0)
    (by rw [Function.update_of_ne hij, Function.update_self]) (Function.update_self _ _ _)
  rw [hy, Fm_slice' a hij]
  linear_combination k

theorem Lf_zero (a : Ed t → ℤ) {i j : Fin t} (hz : ∀ n, n ≠ i → n ≠ j → Am a j n = 0)
    (y : Fin t → ℤ) (hi : y i = 0) : Lf a j y = 0 := by
  unfold Lf
  refine Finset.sum_eq_zero (fun n _ => ?_)
  by_cases hni : n = i
  · rw [hni, hi, mul_zero]
  by_cases hnj : n = j
  · rw [hnj, Am_diag, zero_mul]
  rw [hz n hni hnj, zero_mul]

theorem Lf_one (a : Ed t → ℤ) {i j l : Fin t}
    (hz : ∀ n, n ≠ i → n ≠ j → n ≠ l → Am a j n = 0)
    (y : Fin t → ℤ) (hi : y i = 0) : Lf a j y = Am a j l * y l := by
  unfold Lf
  rw [Finset.sum_eq_single l]
  · intro n _ hnl
    by_cases hni : n = i
    · rw [hni, hi, mul_zero]
    by_cases hnj : n = j
    · rw [hnj, Am_diag, zero_mul]
    rw [hz n hni hnj hnl, zero_mul]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem upd4 {α : Type} {i j : Fin t} (y : Fin t → α) (s r s' r' : α) :
    Function.update (Function.update (Function.update (Function.update y i s) j r) i s') j r' =
      Function.update (Function.update y i s') j r' := by
  funext m
  simp only [Function.update_apply]
  split_ifs <;> simp_all

theorem bad4 (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0)
    (h3 : ∀ m n, m ≠ i → m ≠ j → n ≠ i → n ≠ j →
      Am a i j * Am a m n = Am a i m * Am a j n + Am a i n * Am a j m) {l : Fin t}
    (hli : l ≠ i) (hlj : l ≠ j) (hjl : Am a j l = Am a i j)
    (hz : ∀ n, n ≠ i → n ≠ j → n ≠ l → Am a j n = 0) : 37 * 3 ^ t ≤ 81 * cnt a := by
  have hc : ∀ y : Fin t → ℤ,
      Lf a j (Function.update (Function.update y i 0) j 0) = Am a i j * y l := by
    intro y
    rw [Lf_one a hz _ (by rw [Function.update_of_ne hij, Function.update_self]), hjl,
      Function.update_of_ne hlj, Function.update_of_ne hli]
  have hF : ∀ y : Fin t → ℤ, Fm a y = (y i + y l) *
      (Am a i j * y j + Lf a i (Function.update (Function.update y i 0) j 0)) := by
    intro y
    have := FT a hij h3 y
    rw [hc] at this
    apply mul_left_cancel₀ hA
    rw [this]; ring
  apply cube_bound a hij hA l l
  intro p
  refine ⟨1, 1, ?_⟩
  rw [Function.update_idem]
  have xl : X (Function.update p l 1) l = 1 := by
    unfold X; rw [Function.update_self]; rfl
  have hq : ∀ u v : Fin 3,
      (Pr a (Function.update (Function.update (Function.update p l 1) i u) j v) ↔
      ((vF u + 1) * (Am a i j * vF v + Lf a i (B0 i j (Function.update p l 1))) ≠ 0 ∨
        (|vF u| + 1) * (Am a i j * |vF v| + Lf a i (absV (B0 i j (Function.update p l 1)))) ≠ 0)) := by
    intro u v
    unfold Pr
    rw [X_upd, X_upd, absV_upd, absV_upd, hF, hF, upd4, upd4]
    have hB : absV (B0 i j (Function.update p l 1)) = Function.update (Function.update
        (absV (X (Function.update p l 1))) i 0) j 0 := by
      unfold B0; rw [absV_upd, absV_upd, abs_zero]
    rw [hB]
    unfold B0
    simp only [Function.update_self, Function.update_of_ne hij, Function.update_of_ne hli,
      Function.update_of_ne hlj, xl]
    have xl' : absV (X (Function.update p l 1)) l = 1 := by
      unfold absV; rw [xl]; rfl
    rw [xl']
  unfold sc
  simp only [hq]
  exact Kbound hA _ _


theorem elim_upd (q : Fin t → Fin 3) {i k : Fin t} (j : Option (Fin t))
    (hj : ∀ j', j = some j' → j' ≠ i ∧ j' ≠ k) (u v : Fin 3) :
    j.elim 0 (X (Function.update (Function.update q i u) k v)) = j.elim 0 (X q) ∧
    j.elim 0 (absV (X (Function.update (Function.update q i u) k v))) = |j.elim 0 (X q)| ∧
    ∃ g : Fin 3, j.elim 0 (X q) = vF g := by
  cases j with
  | none => exact ⟨rfl, by simp, 0, rfl⟩
  | some j' =>
    obtain ⟨h1, h2⟩ := hj j' rfl
    refine ⟨?_, ?_, q j', rfl⟩
    · simp only [Option.elim]
      unfold X
      rw [Function.update_of_ne h2, Function.update_of_ne h1]
    · simp only [Option.elim]
      unfold absV X
      rw [Function.update_of_ne h2, Function.update_of_ne h1]

theorem simple_le (a : Ed t → ℤ) (c : ℤ) (hc : c ≠ 0) (i k : Fin t) (j l : Option (Fin t))
    (hik : i ≠ k) (hj : ∀ j', j = some j' → j' ≠ i ∧ j' ≠ k)
    (hl : ∀ l', l = some l' → l' ≠ i ∧ l' ≠ k)
    (hF : ∀ x : Fin t → ℤ, Fm a x = c * (x i - j.elim 0 x) * (x k - l.elim 0 x)) :
    9 * cnt a ≤ 4 * 3 ^ t := by
  have h1 := avg2 i k (fun p => if Pr a p then 1 else 0)
  rw [cnt_eq, ← h1, ← sum_const_mask]
  refine Finset.sum_le_sum (fun q _ => ?_)
  obtain ⟨_, _, g, hg⟩ := elim_upd q j hj 0 0
  obtain ⟨_, _, g', hg'⟩ := elim_upd q l hl 0 0
  rw [← count4 g g']
  apply le_of_eq
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
  obtain ⟨ej, ej', _⟩ := elim_upd q j hj u v
  obtain ⟨el, el', _⟩ := elim_upd q l hl u v
  have xi : X (Function.update (Function.update q i u) k v) i = vF u := by
    unfold X; rw [Function.update_of_ne hik, Function.update_self]
  have xk : X (Function.update (Function.update q i u) k v) k = vF v := by
    unfold X; rw [Function.update_self]
  have hiff : Pr a (Function.update (Function.update q i u) k v) ↔
      ((vF u - vF g) * (vF v - vF g') ≠ 0 ∨ (|vF u| - |vF g|) * (|vF v| - |vF g'|) ≠ 0) := by
    unfold Pr
    rw [hF, hF, ej, el, ej', el', hg, hg']
    have ai : absV (X (Function.update (Function.update q i u) k v)) i = |vF u| := by
      unfold absV; rw [xi]
    have ak : absV (X (Function.update (Function.update q i u) k v)) k = |vF v| := by
      unfold absV; rw [xk]
    rw [xi, xk, ai, ak, mul_assoc, mul_assoc]
    simp only [ne_eq, mul_eq_zero, hc, false_or]
  exact if_congr hiff rfl rfl

def Simple (a : Ed t → ℤ) : Prop :=
  ∃ (c : ℤ) (i k : Fin t) (j l : Option (Fin t)),
    c ≠ 0 ∧ j ≠ some i ∧ l ≠ some k ∧
    Disjoint (insert i (j.elim (∅ : Finset (Fin t)) (fun v => ({v} : Finset (Fin t)))))
      (insert k (l.elim (∅ : Finset (Fin t)) (fun v => ({v} : Finset (Fin t))))) ∧
    ∀ x : Fin t → ℤ, Fm a x = c * (x i - j.elim 0 x) * (x k - l.elim 0 x)

theorem simple_le' (a : Ed t → ℤ) (hs : Simple a) : 9 * cnt a ≤ 4 * 3 ^ t := by
  obtain ⟨c, i, k, j, l, hc, hji, hlk, hd, hF⟩ := hs
  have hik : i ≠ k := by
    intro h
    have hk : i ∈ insert k (l.elim (∅ : Finset (Fin t)) (fun v => ({v} : Finset (Fin t)))) := by
      rw [h]; exact Finset.mem_insert_self k _
    exact Finset.disjoint_left.mp hd (Finset.mem_insert_self i _) hk
  have hj' : ∀ j', j = some j' → j' ≠ i ∧ j' ≠ k := by
    rintro j' rfl
    refine ⟨fun h => hji (h ▸ rfl), fun h => ?_⟩
    have hk : k ∈ insert i ((some j').elim (∅ : Finset (Fin t)) (fun v => ({v} : Finset (Fin t)))) := by
      simp [h]
    exact Finset.disjoint_left.mp hd hk (Finset.mem_insert_self k _)
  have hl' : ∀ l', l = some l' → l' ≠ i ∧ l' ≠ k := by
    rintro l' rfl
    refine ⟨fun h => ?_, fun h => hlk (h ▸ rfl)⟩
    have hk : i ∈ insert k ((some l').elim (∅ : Finset (Fin t)) (fun v => ({v} : Finset (Fin t)))) := by
      simp [h]
    exact Finset.disjoint_left.mp hd (Finset.mem_insert_self i _) hk
  exact simple_le a c hc i k j l hik hj' hl' hF

theorem side (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0)
    (hlt : 81 * cnt a < 37 * 3 ^ t)
    (h3 : ∀ m n, m ≠ i → m ≠ j → n ≠ i → n ≠ j →
      Am a i j * Am a m n = Am a i m * Am a j n + Am a i n * Am a j m) :
    (∀ n, n ≠ i → n ≠ j → Am a j n = 0) ∨
    (∃ l, l ≠ i ∧ l ≠ j ∧ Am a j l = -Am a i j ∧
      ∀ n, n ≠ i → n ≠ j → n ≠ l → Am a j n = 0) := by
  by_cases hall : ∀ n, n ≠ i → n ≠ j → Am a j n = 0
  · exact Or.inl hall
  right
  simp only [not_forall] at hall
  obtain ⟨l, hli, hlj, hl0⟩ := hall
  have hmag : ∀ m, m ≠ i → m ≠ j → Am a j m ≠ 0 →
      Am a j m = Am a i j ∨ Am a j m = -Am a i j := by
    intro m hmi hmj hm0
    by_contra H
    simp only [not_or] at H
    exact absurd (bad1 a hij hA hmi hmj hm0 H.1 H.2) (not_le.mpr hlt)
  have huniq : ∀ n, n ≠ i → n ≠ j → n ≠ l → Am a j n = 0 := by
    intro n hni hnj hnl
    by_contra hn0
    exact absurd (bad2 a hij hA hli hlj hni hnj (Ne.symm hnl) (hmag l hli hlj hl0)
      (hmag n hni hnj hn0)) (not_le.mpr hlt)
  rcases hmag l hli hlj hl0 with hpos | hneg
  · exact absurd (bad4 a hij hA h3 hli hlj hpos huniq) (not_le.mpr hlt)
  · exact ⟨l, hli, hlj, hneg, huniq⟩

theorem gap (a : Ed t → ℤ) {i j : Fin t} (hij : i ≠ j) (hA : Am a i j ≠ 0) (hns : ¬ Simple a) :
    37 * 3 ^ t ≤ 81 * cnt a := by
  by_contra hlt
  rw [not_le] at hlt
  have h3 : ∀ m n, m ≠ i → m ≠ j → n ≠ i → n ≠ j →
      Am a i j * Am a m n = Am a i m * Am a j n + Am a i n * Am a j m := by
    intro m n hmi hmj hni hnj
    by_cases hmn : m = n
    · rw [← hmn, Am_diag, mul_zero]
      by_contra H
      have : Am a i m * Am a j m ≠ 0 := by
        intro h0; apply H; linear_combination -2 * h0
      exact absurd (bad3d a hij hA hmi hmj this) (not_le.mpr hlt)
    · by_contra H
      exact absurd (bad3o a hij hA hmi hmj hni hnj hmn H) (not_le.mpr hlt)
  have h3' : ∀ m n, m ≠ j → m ≠ i → n ≠ j → n ≠ i →
      Am a j i * Am a m n = Am a j m * Am a i n + Am a j n * Am a i m := by
    intro m n hmj hmi hnj hni
    rw [Am_symm a j i]
    linear_combination h3 m n hmi hmj hni hnj
  have hA' : Am a j i ≠ 0 := by rw [Am_symm]; exact hA
  have sj := side a hij hA hlt h3
  have si := side a hij.symm hA' hlt h3'
  rw [Am_symm a j i] at si
  apply hns
  have hft := FT a hij h3
  have y0i : ∀ y : Fin t → ℤ, Function.update (Function.update y i 0) j 0 i = 0 := fun y => by
    rw [Function.update_of_ne hij, Function.update_self]
  have y0j : ∀ y : Fin t → ℤ, Function.update (Function.update y i 0) j 0 j = 0 := fun y =>
    Function.update_self _ _ _
  have y0k : ∀ y : Fin t → ℤ, ∀ k, k ≠ i → k ≠ j →
      Function.update (Function.update y i 0) j 0 k = y k := fun y k h1 h2 => by
    rw [Function.update_of_ne h2, Function.update_of_ne h1]
  rcases sj with hj0 | ⟨l, hli, hlj, hjl, hjz⟩ <;> rcases si with hi0 | ⟨k, hkj, hki, hik, hiz⟩
  · refine ⟨Am a i j, i, j, none, none, hA, by simp, by simp, by simp [hij], fun x => ?_⟩
    have := hft x
    rw [Lf_zero a hj0 _ (y0i x), Lf_zero a hi0 _ (y0j x)] at this
    apply mul_left_cancel₀ hA
    simp only [Option.elim]
    rw [this]; ring
  · refine ⟨Am a i j, i, j, none, some k, hA, by simp, by simp [hkj], by simp [hij, hki, hij.symm, hki.symm],
      fun x => ?_⟩
    have := hft x
    rw [Lf_zero a hj0 _ (y0i x), Lf_one a hiz _ (y0j x), hik, y0k x k hki hkj] at this
    apply mul_left_cancel₀ hA
    simp only [Option.elim]
    rw [this]; ring
  · refine ⟨Am a i j, i, j, some l, none, hA, by simp [hli], by simp, by simp [hij, hlj, hij.symm, hlj.symm],
      fun x => ?_⟩
    have := hft x
    rw [Lf_one a hjz _ (y0i x), Lf_zero a hi0 _ (y0j x), hjl, y0k x l hli hlj] at this
    apply mul_left_cancel₀ hA
    simp only [Option.elim]
    rw [this]; ring
  · have hkl : k ≠ l := by
      intro hkl
      rw [← hkl] at hjl
      have := h3 k k hki hkj hki hkj
      rw [Am_diag, mul_zero, hik, hjl] at this
      have h2 : Am a i j * Am a i j = 0 := by linarith
      exact hA (mul_self_eq_zero.mp h2)
    refine ⟨Am a i j, i, j, some l, some k, hA, by simp [hli], by simp [hkj],
      by simp [hij, hlj, hki, hkl, hij.symm, hlj.symm, hki.symm, hkl.symm], fun x => ?_⟩
    have := hft x
    rw [Lf_one a hjz _ (y0i x), Lf_one a hiz _ (y0j x), hjl, hik, y0k x l hli hlj,
      y0k x k hki hkj] at this
    apply mul_left_cancel₀ hA
    simp only [Option.elim]
    rw [this]; ring

theorem Am_edge (a : Ed t → ℤ) (e0 : Ed t) : Am a e0.val.1 e0.val.2 = a e0 := by
  unfold Am
  have hlt := e0.prop
  rw [Finset.sum_eq_single e0]
  · rw [if_pos ⟨rfl, rfl⟩, if_neg, add_zero]
    rintro ⟨h1, _⟩
    rw [h1] at hlt
    exact lt_irrefl _ hlt
  · intro e _ hne
    have he := e.prop
    rw [if_neg, if_neg, add_zero]
    · rintro ⟨h1, h2⟩
      rw [h1, h2] at he
      exact lt_asymm he hlt
    · rintro ⟨h1, h2⟩
      exact hne (Subtype.ext (Prod.ext h1 h2))
  · intro h; exact absurd (Finset.mem_univ e0) h

theorem main (a : Ed t → ℤ) (ha : ∃ e, a e ≠ 0) :
    4 * 3 ^ t ≤ 9 * cnt a ∧ (9 * cnt a = 4 * 3 ^ t ↔ Simple a) ∧
      (¬ Simple a → 37 * 3 ^ t ≤ 81 * cnt a) := by
  obtain ⟨e0, he0⟩ := ha
  have hij : e0.val.1 ≠ e0.val.2 := ne_of_lt e0.prop
  have hA0 : Am a e0.val.1 e0.val.2 ≠ 0 := by rw [Am_edge]; exact he0
  have low := low_bound a hij hA0
  have hgap := fun h => gap a hij hA0 h
  have hpos : 0 < 3 ^ t := by positivity
  refine ⟨low, ⟨fun heq => ?_, fun hs => le_antisymm (simple_le' a hs) low⟩, hgap⟩
  by_contra hns
  have := hgap hns
  omega

end PEqualNP.Outside.L_lib_1053_aux

theorem PEqualNP.Outside.L_lib_1053 : (∀ t : ℕ,
  let T := Fin t
  let E := {p : T × T // p.1 < p.2}
  let Mask := T → Fin 3
  let val := fun (p : Mask) (i : T) => if p i = 0 then (0 : ℤ) else if p i = 1 then 1 else -1
  ∀ a : E → ℤ, (∃ e, a e ≠ 0) →
    let form := fun (x : T → ℤ) => ∑ e : E, a e * x e.val.1 * x e.val.2
    let count := ((Finset.univ : Finset Mask).filter (fun p =>
      form (val p) ≠ 0 ∨ form (fun i => |val p i|) ≠ 0)).card
    let supp := fun (i : T) (j : Option T) => insert i (j.elim (∅ : Finset T) (fun v => ({v} : Finset T)))
    let factor := fun (x : T → ℤ) (i : T) (j : Option T) => x i - j.elim 0 x
    let simple := ∃ (c : ℤ) (i k : T) (j l : Option T),
      c ≠ 0 ∧ j ≠ some i ∧ l ≠ some k ∧ Disjoint (supp i j) (supp k l) ∧
      ∀ x : T → ℤ, form x = c * factor x i j * factor x k l
    4*3^t ≤ 9*count ∧
      (9*count = 4*3^t ↔ simple) ∧ (¬simple → 37*3^t ≤ 81*count)) := by
  intro t T E Mask val a ha form count supp factor simple
  exact PEqualNP.Outside.L_lib_1053_aux.main a ha
