import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1069_aux

private def sgnB (b : Bool) : ℝ := if b then 1 else -1

private lemma sgnB_mul_self (b : Bool) : sgnB b * sgnB b = 1 := by
  cases b <;> norm_num [sgnB]

private lemma sgnB_not (b : Bool) : sgnB (!b) = -sgnB b := by
  cases b <;> norm_num [sgnB]

private lemma abs_sgnB (b : Bool) : |sgnB b| = 1 := by
  cases b <;> norm_num [sgnB]

private noncomputable def avg {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  ((Fintype.card α : ℝ))⁻¹ * ∑ a : α, f a

private lemma avg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avg (fun _ : α => c) = c := by
  unfold avg
  have hpos : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpos, one_mul]

private lemma avg_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun a => f a + g a) = avg f + avg g := by
  unfold avg
  rw [Finset.sum_add_distrib, mul_add]

private lemma avg_sub {α : Type*} [Fintype α] (f g : α → ℝ) :
    avg (fun a => f a - g a) = avg f - avg g := by
  unfold avg
  rw [Finset.sum_sub_distrib, mul_sub]

private lemma avg_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avg (fun a => c * f a) = c * avg f := by
  unfold avg
  rw [← Finset.mul_sum]
  ring

private lemma avg_div {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    avg (fun a => f a / c) = avg f / c := by
  have h : (fun a => f a / c) = (fun a => c⁻¹ * f a) := by
    funext a; rw [div_eq_inv_mul]
  rw [h, avg_const_mul, div_eq_inv_mul]

private lemma avg_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : α → ι → ℝ) :
    avg (fun a => ∑ i ∈ s, f a i) = ∑ i ∈ s, avg (fun a => f a i) := by
  unfold avg
  rw [Finset.sum_comm, Finset.mul_sum]

private lemma avg_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    avg f ≤ avg g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h a) (by positivity)

private lemma avg_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ avg f := by
  unfold avg
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => h a)

private lemma exists_le_avg {α : Type*} [Fintype α] [Nonempty α] (f : α → ℝ) :
    ∃ a : α, f a ≤ avg f := by
  by_contra h
  push Not at h
  have hpos : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : ∑ _ : α, avg f < ∑ a : α, f a :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => h a
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  unfold avg at hsum
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hsum
  exact lt_irrefl _ hsum

private lemma avg_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    avg (fun a => f (e a)) = avg f := by
  unfold avg
  rw [Fintype.card_congr e, Equiv.sum_comp e f]

private lemma avg_prod {α β : Type*} [Fintype α] [Fintype β] (f : α × β → ℝ) :
    avg f = avg (fun a => avg (fun b => f (a, b))) := by
  unfold avg
  rw [Fintype.card_prod, Nat.cast_mul, mul_inv, Fintype.sum_prod_type]
  rw [← Finset.mul_sum, mul_assoc]

private lemma avg_prod_comm {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    avg (fun a => avg (fun b => f a b)) = avg (fun b => avg (fun a => f a b)) := by
  unfold avg
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  ring

private lemma avg_bool (f : Bool → ℝ) : avg f = (f true + f false) / 2 := by
  unfold avg
  rw [Fintype.card_bool, Fintype.sum_bool]
  norm_num
  ring

private lemma avg_mul_sq_le {α : Type*} [Fintype α] (f g : α → ℝ) :
    (avg (fun a => f a * g a)) ^ 2 ≤ avg (fun a => (f a) ^ 2) * avg (fun a => (g a) ^ 2) := by
  unfold avg
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α) f g
  have hinv : 0 ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc (((Fintype.card α : ℝ))⁻¹ * ∑ a : α, f a * g a) ^ 2
      = ((Fintype.card α : ℝ)⁻¹) ^ 2 * (∑ a : α, f a * g a) ^ 2 := by ring
    _ ≤ ((Fintype.card α : ℝ)⁻¹) ^ 2 * ((∑ a : α, f a ^ 2) * (∑ a : α, g a ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs hinv
    _ = ((Fintype.card α : ℝ)⁻¹ * ∑ a : α, f a ^ 2) *
        ((Fintype.card α : ℝ)⁻¹ * ∑ a : α, g a ^ 2) := by ring

private lemma avg_pi_prod {d : ℕ} (g : Fin d → Bool → ℝ) :
    avg (fun ε : Fin d → Bool => ∏ i : Fin d, g i (ε i)) =
      ∏ i : Fin d, avg (fun b : Bool => g i b) := by
  unfold avg
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  simp only [Nat.cast_pow, Nat.cast_ofNat, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  congr 1
  exact (Fintype.prod_sum g).symm

private def consBoolEquiv (t : ℕ) : Bool × (Fin t → Bool) ≃ (Fin (t + 1) → Bool) where
  toFun p := Fin.cons (α := fun _ => Bool) p.1 p.2
  invFun σ := (σ 0, fun i => σ i.succ)
  left_inv p := by
    apply Prod.ext
    · simp
    · ext i; simp
  right_inv σ := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro i; simp

private lemma avg_deg1_fourth : ∀ (t : ℕ) (c0 : ℝ) (c : Fin t → ℝ),
    let L : (Fin t → Bool) → ℝ := fun σ => c0 + ∑ j : Fin t, c j * sgnB (σ j)
    avg (fun σ => (L σ) ^ 4) ≤ 3 * (avg (fun σ => (L σ) ^ 2)) ^ 2 := by
  intro t
  induction t with
  | zero =>
    intro c0 c
    dsimp only
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [avg_const, avg_const]
    nlinarith [sq_nonneg (c0 ^ 2)]
  | succ t ih =>
    intro c0 c
    dsimp only
    let A : (Fin t → Bool) → ℝ := fun σ => c0 + ∑ j : Fin t, c j.succ * sgnB (σ j)
    let b0 : ℝ := c 0
    have hsplit : ∀ (b : Bool) (σ : Fin t → Bool),
        c0 + ∑ j : Fin (t + 1), c j * sgnB (consBoolEquiv t (b, σ) j) =
          A σ + b0 * sgnB b := by
      intro b σ
      rw [Fin.sum_univ_succ]
      simp only [consBoolEquiv, Equiv.coe_fn_mk, A, b0, Fin.cons_zero, Fin.cons_succ]
      ring
    have h4 : avg (fun σ : Fin (t + 1) → Bool => (c0 + ∑ j, c j * sgnB (σ j)) ^ 4) =
        avg (fun σ => (A σ) ^ 4) + 6 * b0 ^ 2 * avg (fun σ => (A σ) ^ 2) + b0 ^ 4 := by
      rw [← avg_equiv (consBoolEquiv t), avg_prod]
      have h1 : ∀ b : Bool,
          avg (fun σ => (c0 + ∑ j, c j * sgnB (consBoolEquiv t (b, σ) j)) ^ 4) =
          avg (fun σ => (A σ + b0 * sgnB b) ^ 4) := by
        intro b; congr 1; funext σ; rw [hsplit]
      simp_rw [h1]
      rw [avg_bool, ← avg_add, ← avg_div]
      have hpt : ∀ σ, ((A σ + b0 * sgnB true) ^ 4 + (A σ + b0 * sgnB false) ^ 4) / 2 =
          (A σ) ^ 4 + 6 * b0 ^ 2 * (A σ) ^ 2 + b0 ^ 4 := by
        intro σ; simp [sgnB]; ring
      simp_rw [hpt]
      rw [avg_add, avg_add, avg_const_mul, avg_const]
    have h2 : avg (fun σ : Fin (t + 1) → Bool => (c0 + ∑ j, c j * sgnB (σ j)) ^ 2) =
        avg (fun σ => (A σ) ^ 2) + b0 ^ 2 := by
      rw [← avg_equiv (consBoolEquiv t), avg_prod]
      have h1 : ∀ b : Bool,
          avg (fun σ => (c0 + ∑ j, c j * sgnB (consBoolEquiv t (b, σ) j)) ^ 2) =
          avg (fun σ => (A σ + b0 * sgnB b) ^ 2) := by
        intro b; congr 1; funext σ; rw [hsplit]
      simp_rw [h1]
      rw [avg_bool, ← avg_add, ← avg_div]
      have hpt : ∀ σ, ((A σ + b0 * sgnB true) ^ 2 + (A σ + b0 * sgnB false) ^ 2) / 2 =
          (A σ) ^ 2 + b0 ^ 2 := by
        intro σ; simp [sgnB]; ring
      simp_rw [hpt]
      rw [avg_add, avg_const]
    rw [h4, h2]
    have hih := ih c0 (fun j => c j.succ)
    dsimp only at hih
    have hb4 : 0 ≤ b0 ^ 4 := by positivity
    nlinarith

private lemma avg_deg2_fourth : ∀ (t : ℕ) (c0 : ℝ) (c : Fin t → ℝ) (w : Fin t → Fin t → ℝ),
    let Q : (Fin t → Bool) → ℝ := fun σ =>
      c0 + ∑ j : Fin t, c j * sgnB (σ j) +
        ∑ i : Fin t, ∑ j : Fin t, if i < j then w i j * sgnB (σ i) * sgnB (σ j) else 0
    avg (fun σ => (Q σ) ^ 4) ≤ 81 * (avg (fun σ => (Q σ) ^ 2)) ^ 2 := by
  intro t
  induction t with
  | zero =>
    intro c0 c w
    dsimp only
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    rw [avg_const, avg_const]
    nlinarith [sq_nonneg (c0 ^ 2)]
  | succ t ih =>
    intro c0 c w
    dsimp only
    let A : (Fin t → Bool) → ℝ := fun σ =>
      c0 + ∑ j : Fin t, c j.succ * sgnB (σ j) +
        ∑ i : Fin t, ∑ j : Fin t,
          if i < j then w i.succ j.succ * sgnB (σ i) * sgnB (σ j) else 0
    let B : (Fin t → Bool) → ℝ := fun σ =>
      c 0 + ∑ j : Fin t, w 0 j.succ * sgnB (σ j)
    have hsplit : ∀ (b : Bool) (σ : Fin t → Bool),
        c0 + ∑ j : Fin (t + 1), c j * sgnB (consBoolEquiv t (b, σ) j) +
          ∑ i : Fin (t + 1), ∑ j : Fin (t + 1),
            (if i < j then
              w i j * sgnB (consBoolEquiv t (b, σ) i) *
                sgnB (consBoolEquiv t (b, σ) j)
            else 0) =
        A σ + B σ * sgnB b := by
      intro b σ
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      have hrow0 : (∑ j : Fin (t + 1),
          if (0 : Fin (t + 1)) < j then
            w 0 j * sgnB (consBoolEquiv t (b, σ) 0) *
              sgnB (consBoolEquiv t (b, σ) j)
          else 0) = (∑ j : Fin t, w 0 j.succ * sgnB (σ j)) * sgnB b := by
        rw [Fin.sum_univ_succ]
        simp only [consBoolEquiv, Equiv.coe_fn_mk, lt_self_iff_false, ↓reduceIte, Fin.succ_pos,
          Fin.cons_zero, Fin.cons_succ, zero_add, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have hrows : ∀ i : Fin t,
          (∑ j : Fin (t + 1),
            if i.succ < j then
              w i.succ j * sgnB (consBoolEquiv t (b, σ) i.succ) *
                sgnB (consBoolEquiv t (b, σ) j)
            else 0) =
          ∑ j : Fin t, if i < j then w i.succ j.succ * sgnB (σ i) * sgnB (σ j) else 0 := by
        intro i
        rw [Fin.sum_univ_succ]
        have hnot0 : ¬ i.succ < (0 : Fin (t + 1)) := by simp
        simp only [consBoolEquiv, Equiv.coe_fn_mk, hnot0, ↓reduceIte, zero_add,
          Fin.succ_lt_succ_iff, Fin.cons_succ]
      rw [hrow0]
      simp_rw [hrows]
      simp only [consBoolEquiv, Equiv.coe_fn_mk, A, B, Fin.cons_zero, Fin.cons_succ]
      ring
    have h4 : avg (fun σ : Fin (t + 1) → Bool =>
        (c0 + ∑ j, c j * sgnB (σ j) +
          ∑ i, ∑ j, if i < j then w i j * sgnB (σ i) * sgnB (σ j) else 0) ^ 4) =
        avg (fun σ => (A σ) ^ 4) + 6 * avg (fun σ => (A σ) ^ 2 * (B σ) ^ 2) +
          avg (fun σ => (B σ) ^ 4) := by
      rw [← avg_equiv (consBoolEquiv t), avg_prod]
      have h1 : ∀ b : Bool,
          avg (fun σ => (c0 + ∑ j, c j * sgnB (consBoolEquiv t (b, σ) j) +
            ∑ i, ∑ j, if i < j then w i j * sgnB (consBoolEquiv t (b, σ) i) *
              sgnB (consBoolEquiv t (b, σ) j) else 0) ^ 4) =
          avg (fun σ => (A σ + B σ * sgnB b) ^ 4) := by
        intro b; congr 1; funext σ; rw [hsplit]
      simp_rw [h1]
      rw [avg_bool, ← avg_add, ← avg_div]
      have hpt : ∀ σ, ((A σ + B σ * sgnB true) ^ 4 + (A σ + B σ * sgnB false) ^ 4) / 2 =
          (A σ) ^ 4 + 6 * ((A σ) ^ 2 * (B σ) ^ 2) + (B σ) ^ 4 := by
        intro σ; simp [sgnB]; ring
      simp_rw [hpt]
      rw [avg_add, avg_add, avg_const_mul]
    have h2 : avg (fun σ : Fin (t + 1) → Bool =>
        (c0 + ∑ j, c j * sgnB (σ j) +
          ∑ i, ∑ j, if i < j then w i j * sgnB (σ i) * sgnB (σ j) else 0) ^ 2) =
        avg (fun σ => (A σ) ^ 2) + avg (fun σ => (B σ) ^ 2) := by
      rw [← avg_equiv (consBoolEquiv t), avg_prod]
      have h1 : ∀ b : Bool,
          avg (fun σ => (c0 + ∑ j, c j * sgnB (consBoolEquiv t (b, σ) j) +
            ∑ i, ∑ j, if i < j then w i j * sgnB (consBoolEquiv t (b, σ) i) *
              sgnB (consBoolEquiv t (b, σ) j) else 0) ^ 2) =
          avg (fun σ => (A σ + B σ * sgnB b) ^ 2) := by
        intro b; congr 1; funext σ; rw [hsplit]
      simp_rw [h1]
      rw [avg_bool, ← avg_add, ← avg_div]
      have hpt : ∀ σ, ((A σ + B σ * sgnB true) ^ 2 + (A σ + B σ * sgnB false) ^ 2) / 2 =
          (A σ) ^ 2 + (B σ) ^ 2 := by
        intro σ; simp [sgnB]; ring
      simp_rw [hpt]
      rw [avg_add]
    rw [h4, h2]
    have hA4 : avg (fun σ => (A σ) ^ 4) ≤ 81 * (avg (fun σ => (A σ) ^ 2)) ^ 2 :=
      ih c0 (fun j => c j.succ) (fun i j => w i.succ j.succ)
    have hB4 : avg (fun σ => (B σ) ^ 4) ≤ 3 * (avg (fun σ => (B σ) ^ 2)) ^ 2 :=
      avg_deg1_fourth t (c 0) (fun j => w 0 j.succ)
    have hA2_nn : 0 ≤ avg (fun σ => (A σ) ^ 2) := avg_nonneg fun σ => sq_nonneg _
    have hB2_nn : 0 ≤ avg (fun σ => (B σ) ^ 2) := avg_nonneg fun σ => sq_nonneg _
    have hAB_nn : 0 ≤ avg (fun σ => (A σ) ^ 2 * (B σ) ^ 2) :=
      avg_nonneg fun σ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hcs : (avg (fun σ => (A σ) ^ 2 * (B σ) ^ 2)) ^ 2 ≤
        avg (fun σ => (A σ) ^ 4) * avg (fun σ => (B σ) ^ 4) := by
      have h := avg_mul_sq_le (fun σ => (A σ) ^ 2) (fun σ => (B σ) ^ 2)
      have hpowA : ∀ σ, ((A σ) ^ 2) ^ 2 = (A σ) ^ 4 := fun σ => by ring
      have hpowB : ∀ σ, ((B σ) ^ 2) ^ 2 = (B σ) ^ 4 := fun σ => by ring
      simp_rw [hpowA, hpowB] at h
      exact h
    have hAB_le : avg (fun σ => (A σ) ^ 2 * (B σ) ^ 2) ≤
        27 * avg (fun σ => (A σ) ^ 2) * avg (fun σ => (B σ) ^ 2) := by
      have h27_nn : 0 ≤ 27 * avg (fun σ => (A σ) ^ 2) * avg (fun σ => (B σ) ^ 2) := by positivity
      have hsq : (avg (fun σ => (A σ) ^ 2 * (B σ) ^ 2)) ^ 2 ≤
          (27 * avg (fun σ => (A σ) ^ 2) * avg (fun σ => (B σ) ^ 2)) ^ 2 := by
        have hB4' : avg (fun σ => (B σ) ^ 4) ≤ 9 * (avg (fun σ => (B σ) ^ 2)) ^ 2 := by
          nlinarith [sq_nonneg (avg (fun σ => (B σ) ^ 2))]
        have hB4_nn : 0 ≤ avg (fun σ => (B σ) ^ 4) := avg_nonneg fun σ => by positivity
        calc (avg (fun σ => (A σ) ^ 2 * (B σ) ^ 2)) ^ 2
            ≤ avg (fun σ => (A σ) ^ 4) * avg (fun σ => (B σ) ^ 4) := hcs
          _ ≤ (81 * (avg (fun σ => (A σ) ^ 2)) ^ 2) * (9 * (avg (fun σ => (B σ) ^ 2)) ^ 2) :=
              mul_le_mul hA4 hB4' hB4_nn (by positivity)
          _ = (27 * avg (fun σ => (A σ) ^ 2) * avg (fun σ => (B σ) ^ 2)) ^ 2 := by ring
      nlinarith
    nlinarith [sq_nonneg (avg (fun σ => (B σ) ^ 2))]

private def Edge (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}

private instance (t : ℕ) : Fintype (Edge t) := Subtype.fintype _
private instance (t : ℕ) : DecidableEq (Edge t) :=
  inferInstanceAs (DecidableEq {p : Fin t × Fin t // p.1 < p.2})

private def edgeChar {t : ℕ} (e : Edge t) (σ : Fin t → Bool) : ℝ :=
  sgnB (σ e.val.1) * sgnB (σ e.val.2)

private lemma abs_edgeChar {t : ℕ} (e : Edge t) (σ : Fin t → Bool) : |edgeChar e σ| = 1 := by
  simp [edgeChar, abs_mul, abs_sgnB]

private lemma edgeChar_ortho {t : ℕ} (e₁ e₂ : Edge t) :
    avg (fun σ : Fin t → Bool => edgeChar e₁ σ * edgeChar e₂ σ) =
      if e₁ = e₂ then 1 else 0 := by
  by_cases h : e₁ = e₂
  · subst h
    simp only [↓reduceIte]
    have h1 : ∀ σ : Fin t → Bool, edgeChar e₁ σ * edgeChar e₁ σ = 1 := by
      intro σ
      unfold edgeChar
      calc sgnB (σ e₁.val.1) * sgnB (σ e₁.val.2) * (sgnB (σ e₁.val.1) * sgnB (σ e₁.val.2))
          = (sgnB (σ e₁.val.1) * sgnB (σ e₁.val.1)) * (sgnB (σ e₁.val.2) * sgnB (σ e₁.val.2)) := by ring
        _ = 1 * 1 := by rw [sgnB_mul_self, sgnB_mul_self]
        _ = 1 := one_mul 1
    simp_rw [h1]
    exact avg_const 1
  · simp only [h, ↓reduceIte]
    have hex : ∃ u : Fin t,
        ((u = e₁.val.1 ∨ u = e₁.val.2) ∧ u ≠ e₂.val.1 ∧ u ≠ e₂.val.2) ∨
        ((u = e₂.val.1 ∨ u = e₂.val.2) ∧ u ≠ e₁.val.1 ∧ u ≠ e₁.val.2) := by
      have h1lt := e₁.property
      have h2lt := e₂.property
      by_cases h11 : e₁.val.1 = e₂.val.1
      · by_cases h22 : e₁.val.2 = e₂.val.2
        · exfalso; exact h (Subtype.ext (Prod.ext h11 h22))
        · exact ⟨e₁.val.2, Or.inl ⟨Or.inr rfl, ne_of_gt (h11 ▸ h1lt), h22⟩⟩
      · by_cases h12 : e₁.val.1 = e₂.val.2
        · exact ⟨e₂.val.1, Or.inr ⟨Or.inl rfl, Ne.symm h11, ne_of_lt (lt_trans h2lt (h12 ▸ h1lt))⟩⟩
        · exact ⟨e₁.val.1, Or.inl ⟨Or.inl rfl, h11, h12⟩⟩
    obtain ⟨u, hu⟩ := hex
    let flip : (Fin t → Bool) ≃ (Fin t → Bool) :=
      { toFun := fun σ => Function.update σ u (!(σ u))
        invFun := fun σ => Function.update σ u (!(σ u))
        left_inv := fun σ => by
          ext j
          by_cases hj : j = u
          · subst hj; simp
          · simp [hj]
        right_inv := fun σ => by
          ext j
          by_cases hj : j = u
          · subst hj; simp
          · simp [hj] }
    have hneg : ∀ σ : Fin t → Bool,
        edgeChar e₁ (flip σ) * edgeChar e₂ (flip σ) = -(edgeChar e₁ σ * edgeChar e₂ σ) := by
      intro σ
      have hne1 : e₁.val.1 ≠ e₁.val.2 := ne_of_lt e₁.property
      have hne2 : e₂.val.1 ≠ e₂.val.2 := ne_of_lt e₂.property
      unfold edgeChar flip
      dsimp only [Equiv.coe_fn_mk]
      rcases hu with ⟨h1 | h1, h2a, h2b⟩ | ⟨h2 | h2, h1a, h1b⟩
      · subst h1
        simp only [Function.update_self, Function.update_of_ne hne1.symm,
          Function.update_of_ne h2a.symm, Function.update_of_ne h2b.symm, sgnB_not]
        ring
      · subst h1
        simp only [Function.update_self, Function.update_of_ne hne1,
          Function.update_of_ne h2a.symm, Function.update_of_ne h2b.symm, sgnB_not]
        ring
      · subst h2
        simp only [Function.update_self, Function.update_of_ne hne2.symm,
          Function.update_of_ne h1a.symm, Function.update_of_ne h1b.symm, sgnB_not]
        ring
      · subst h2
        simp only [Function.update_self, Function.update_of_ne hne2,
          Function.update_of_ne h1a.symm, Function.update_of_ne h1b.symm, sgnB_not]
        ring
    have heq := avg_equiv flip (fun σ => edgeChar e₁ σ * edgeChar e₂ σ)
    simp_rw [hneg] at heq
    have hneg_avg : avg (fun σ => -(edgeChar e₁ σ * edgeChar e₂ σ)) =
        -avg (fun σ => edgeChar e₁ σ * edgeChar e₂ σ) := by
      have := avg_const_mul (-1 : ℝ) (fun σ => edgeChar e₁ σ * edgeChar e₂ σ)
      simpa using this
    rw [hneg_avg] at heq
    linarith

private def quadForm {t : ℕ} (v : Edge t → ℝ) (σ : Fin t → Bool) : ℝ :=
  ∑ e : Edge t, v e * edgeChar e σ

private lemma quadForm_second_moment {t : ℕ} (v : Edge t → ℝ) :
    avg (fun σ : Fin t → Bool => (quadForm v σ) ^ 2) = ∑ e : Edge t, (v e) ^ 2 := by
  have hsq : ∀ σ : Fin t → Bool,
      (quadForm v σ) ^ 2 =
        ∑ e₁ : Edge t, ∑ e₂ : Edge t, (v e₁ * v e₂) * (edgeChar e₁ σ * edgeChar e₂ σ) := by
    intro σ
    rw [quadForm, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e₂ _ => by ring
  simp_rw [hsq]
  rw [avg_sum]
  refine Finset.sum_congr rfl fun e₁ _ => ?_
  rw [avg_sum]
  simp_rw [avg_const_mul, edgeChar_ortho]
  simp [sq]

private lemma quadForm_fourth_moment {t : ℕ} (v : Edge t → ℝ) :
    avg (fun σ : Fin t → Bool => (quadForm v σ) ^ 4) ≤ 81 * (∑ e : Edge t, (v e) ^ 2) ^ 2 := by
  let w : Fin t → Fin t → ℝ := fun i j => if h : i < j then v ⟨(i, j), h⟩ else 0
  have hQ : ∀ σ : Fin t → Bool,
      quadForm v σ = 0 + ∑ j : Fin t, (0 : ℝ) * sgnB (σ j) +
        ∑ i : Fin t, ∑ j : Fin t, if i < j then w i j * sgnB (σ i) * sgnB (σ j) else 0 := by
    intro σ
    simp only [zero_mul, Finset.sum_const_zero, add_zero, zero_add, quadForm, edgeChar]
    rw [← Fintype.sum_prod_type', ← Finset.sum_filter]
    refine Finset.sum_bij (fun e _ => e.val) ?_ ?_ ?_ ?_
    · intro e _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property⟩
    · intro e₁ _ e₂ _ h
      exact Subtype.ext h
    · intro p hp
      exact ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, Finset.mem_univ _, rfl⟩
    · rintro ⟨⟨i, j⟩, hij⟩ _
      simp only [w, hij, ↓reduceDIte]
      ring
  have h4 := avg_deg2_fourth t 0 (fun _ => 0) w
  dsimp only at h4
  simp_rw [← hQ] at h4
  rw [quadForm_second_moment] at h4
  exact h4

private lemma quadForm_abs_ge {t : ℕ} (v : Edge t → ℝ) (hnorm : ∑ e : Edge t, (v e) ^ 2 = 1) :
    (1 : ℝ) / 9 ≤ avg (fun σ : Fin t → Bool => |quadForm v σ|) := by
  have h2 : avg (fun σ : Fin t → Bool => (quadForm v σ) ^ 2) = 1 := by
    rw [quadForm_second_moment, hnorm]
  have h4 : avg (fun σ : Fin t → Bool => (quadForm v σ) ^ 4) ≤ 81 := by
    have := quadForm_fourth_moment v
    rw [hnorm, one_pow, mul_one] at this
    exact this
  have hcs1 : (avg (fun σ => (quadForm v σ) ^ 2)) ^ 2 ≤
      avg (fun σ => |quadForm v σ|) * avg (fun σ => |quadForm v σ| ^ 3) := by
    have h := avg_mul_sq_le (fun σ => Real.sqrt |quadForm v σ|)
      (fun σ => Real.sqrt |quadForm v σ| * |quadForm v σ|)
    have hl : ∀ σ, Real.sqrt |quadForm v σ| * (Real.sqrt |quadForm v σ| * |quadForm v σ|) =
        (quadForm v σ) ^ 2 := by
      intro σ
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _), ← sq, sq_abs]
    have hr1 : ∀ σ, (Real.sqrt |quadForm v σ|) ^ 2 = |quadForm v σ| :=
      fun σ => Real.sq_sqrt (abs_nonneg _)
    have hr2 : ∀ σ, (Real.sqrt |quadForm v σ| * |quadForm v σ|) ^ 2 = |quadForm v σ| ^ 3 := by
      intro σ
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
      ring
    simp_rw [hl, hr1, hr2] at h
    exact h
  have hcs2 : (avg (fun σ => |quadForm v σ| ^ 3)) ^ 2 ≤
      avg (fun σ => (quadForm v σ) ^ 2) * avg (fun σ => (quadForm v σ) ^ 4) := by
    have h := avg_mul_sq_le (fun σ => |quadForm v σ|) (fun σ => (quadForm v σ) ^ 2)
    have hl : ∀ σ, |quadForm v σ| * (quadForm v σ) ^ 2 = |quadForm v σ| ^ 3 := by
      intro σ; rw [← sq_abs (quadForm v σ)]; ring
    have hr1 : ∀ σ, |quadForm v σ| ^ 2 = (quadForm v σ) ^ 2 := fun σ => sq_abs _
    have hr2 : ∀ σ, ((quadForm v σ) ^ 2) ^ 2 = (quadForm v σ) ^ 4 := fun σ => by ring
    simp_rw [hl, hr1, hr2] at h
    exact h
  rw [h2] at hcs1 hcs2
  have h1_nn : 0 ≤ avg (fun σ => |quadForm v σ|) := avg_nonneg fun σ => abs_nonneg _
  have h3_nn : 0 ≤ avg (fun σ => |quadForm v σ| ^ 3) := avg_nonneg fun σ => by positivity
  have hprod : 1 ≤ (avg (fun σ => |quadForm v σ|)) ^ 2 * 81 := by
    have hsq1 : (1 : ℝ) ≤ (avg (fun σ => |quadForm v σ|)) ^ 2 * (avg (fun σ => |quadForm v σ| ^ 3)) ^ 2 := by
      have : (1 : ℝ) ≤ avg (fun σ => |quadForm v σ|) * avg (fun σ => |quadForm v σ| ^ 3) := by
        simpa using hcs1
      nlinarith
    have hsq2 : (avg (fun σ => |quadForm v σ| ^ 3)) ^ 2 ≤ 81 := by linarith
    nlinarith [sq_nonneg (avg (fun σ => |quadForm v σ|))]
  nlinarith

private lemma quadForm_excess_le {t : ℕ} (v : Edge t → ℝ) (hnorm : ∑ e : Edge t, (v e) ^ 2 = 1) :
    avg (fun σ : Fin t → Bool => max (0 : ℝ) (|quadForm v σ| - 10)) ≤ 81 / 4000 := by
  have hpt : ∀ x : ℝ, 0 ≤ x → 4000 * max (0 : ℝ) (x - 10) ≤ x ^ 4 := by
    intro x hx
    by_cases h10 : x ≤ 10
    · rw [max_eq_left (by linarith), mul_zero]
      positivity
    · rw [max_eq_right (by linarith)]
      set u : ℝ := x - 10
      have hu : 0 ≤ u := by linarith
      have hx_eq : x = 10 + u := by ring
      rw [hx_eq]
      have : (10 + u) ^ 4 - 4000 * u = 10000 + 600 * u ^ 2 + 40 * u ^ 3 + u ^ 4 := by ring
      nlinarith [sq_nonneg u, pow_nonneg hu 3, pow_nonneg hu 4]
  have havg : 4000 * avg (fun σ : Fin t → Bool => max (0 : ℝ) (|quadForm v σ| - 10)) ≤
      avg (fun σ : Fin t → Bool => (quadForm v σ) ^ 4) := by
    rw [← avg_const_mul]
    refine avg_mono fun σ => ?_
    have h := hpt |quadForm v σ| (abs_nonneg _)
    have h4 : |quadForm v σ| ^ 4 = (quadForm v σ) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    linarith
  have h4 := quadForm_fourth_moment v
  rw [hnorm, one_pow, mul_one] at h4
  linarith

private lemma one_step_contraction {ι : Type*} {S : Set ι} (hS : S.Nonempty)
    (h x : ι → ℝ) (φ : ℝ → ℝ) (hlip : ∀ u w, |φ u - φ w| ≤ |u - w|)
    {M : ℝ} (hMh : ∀ v ∈ S, |h v| ≤ M) (hMx : ∀ v ∈ S, |x v| ≤ M) :
    sSup ((fun v => h v + φ (x v)) '' S) + sSup ((fun v => h v - φ (x v)) '' S) ≤
      sSup ((fun v => h v + x v) '' S) + sSup ((fun v => h v - x v) '' S) := by
  have hbdd_px : BddAbove ((fun v => h v + x v) '' S) := by
    refine ⟨M + M, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    linarith [(abs_le.mp (hMh v hv)).2, (abs_le.mp (hMx v hv)).2]
  have hbdd_mx : BddAbove ((fun v => h v - x v) '' S) := by
    refine ⟨M + M, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    linarith [(abs_le.mp (hMh v hv)).2, (abs_le.mp (hMx v hv)).1]
  rw [← le_sub_iff_add_le]
  apply csSup_le (hS.image _)
  rintro _ ⟨u, hu, rfl⟩
  rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
  apply csSup_le (hS.image _)
  rintro _ ⟨w, hw, rfl⟩
  rw [le_sub_iff_add_le, add_comm]
  have hlip_uw : φ (x u) - φ (x w) ≤ |x u - x w| :=
    (le_abs_self _).trans (hlip (x u) (x w))
  have hpu : h u + x u ≤ sSup ((fun v => h v + x v) '' S) := le_csSup hbdd_px ⟨u, hu, rfl⟩
  have hpw : h w + x w ≤ sSup ((fun v => h v + x v) '' S) := le_csSup hbdd_px ⟨w, hw, rfl⟩
  have hmu : h u - x u ≤ sSup ((fun v => h v - x v) '' S) := le_csSup hbdd_mx ⟨u, hu, rfl⟩
  have hmw : h w - x w ≤ sSup ((fun v => h v - x v) '' S) := le_csSup hbdd_mx ⟨w, hw, rfl⟩
  by_cases hle : x w ≤ x u
  · rw [abs_of_nonneg (by linarith)] at hlip_uw
    linarith
  · rw [abs_of_neg (by linarith)] at hlip_uw
    linarith

private lemma rademacher_contraction {ι : Type*} {d : ℕ} {S : Set ι} (hS : S.Nonempty)
    (a : ι → Fin d → ℝ) (φ : ℝ → ℝ) (hlip : ∀ u w, |φ u - φ w| ≤ |u - w|) (hφ0 : φ 0 = 0)
    {M : ℝ} (hM_nn : 0 ≤ M) (hM : ∀ v ∈ S, ∀ i : Fin d, |a v i| ≤ M) :
    avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (a v i)) '' S)) ≤
      avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * a v i) '' S)) := by
  have hφ_le : ∀ v ∈ S, ∀ i : Fin d, |φ (a v i)| ≤ M := by
    intro v hv i
    have h := hlip (a v i) 0
    rw [hφ0, sub_zero, sub_zero] at h
    exact h.trans (hM v hv i)
  let term : ℕ → Fin d → ι → ℝ := fun m i v => if i.val < m then a v i else φ (a v i)
  have hterm_le : ∀ m i, ∀ v ∈ S, |term m i v| ≤ M := by
    intro m i v hv
    dsimp only [term]
    split_ifs
    · exact hM v hv i
    · exact hφ_le v hv i
  have hstep : ∀ m : ℕ, m ≤ d →
      avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * term 0 i v) '' S)) ≤
        avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * term m i v) '' S)) := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ m ih =>
      intro hm
      have hlt : m < d := hm
      refine (ih (Nat.le_of_lt hlt)).trans ?_
      let idx : Fin d := ⟨m, hlt⟩
      let e : Bool × ({j : Fin d // j ≠ idx} → Bool) ≃ (Fin d → Bool) :=
        (Equiv.piSplitAt idx (fun _ : Fin d => Bool)).symm
      rw [← avg_equiv e, avg_prod, avg_prod_comm]
      conv_rhs => rw [← avg_equiv e, avg_prod, avg_prod_comm]
      refine avg_mono fun rest => ?_
      rw [avg_bool, avg_bool]
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
      let h : ι → ℝ := fun v =>
        ∑ j ∈ Finset.univ.erase idx, sgnB (e (true, rest) j) * term m j v
      have he_eq_ne : ∀ (b : Bool) (j : Fin d), j ≠ idx → e (b, rest) j = e (true, rest) j := by
        intro b j hj
        simp [e, Equiv.piSplitAt, hj]
      have he_eq_self : ∀ b : Bool, e (b, rest) idx = b := by
        intro b
        simp [e, Equiv.piSplitAt]
      have hterm_ne : ∀ (j : Fin d), j ≠ idx → ∀ v, term (m + 1) j v = term m j v := by
        intro j hj v
        have hjne : j.val ≠ m := fun h => hj (Fin.ext h)
        dsimp only [term]
        have hiff : j.val < m + 1 ↔ j.val < m := by omega
        simp [hiff]
      have hsum_m : ∀ (b : Bool) (v : ι),
          ∑ i : Fin d, sgnB (e (b, rest) i) * term m i v = h v + sgnB b * φ (a v idx) := by
        intro b v
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx)]
        rw [he_eq_self b]
        have hidx_m : term m idx v = φ (a v idx) := by simp [term, idx]
        rw [hidx_m, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [he_eq_ne b j (Finset.ne_of_mem_erase hj)]
      have hsum_m1 : ∀ (b : Bool) (v : ι),
          ∑ i : Fin d, sgnB (e (b, rest) i) * term (m + 1) i v = h v + sgnB b * a v idx := by
        intro b v
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ idx)]
        rw [he_eq_self b]
        have hidx_m1 : term (m + 1) idx v = a v idx := by simp [term, idx]
        rw [hidx_m1, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [he_eq_ne b j (Finset.ne_of_mem_erase hj), hterm_ne j (Finset.ne_of_mem_erase hj)]
      simp_rw [hsum_m, hsum_m1, sgnB]
      simp only [↓reduceIte, Bool.false_eq_true, one_mul, neg_one_mul, ← sub_eq_add_neg]
      have hMh : ∀ v ∈ S, |h v| ≤ (d : ℝ) * M := by
        intro v hv
        calc |h v| ≤ ∑ j ∈ Finset.univ.erase idx, |sgnB (e (true, rest) j) * term m j v| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.univ.erase idx, M := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [abs_mul, abs_sgnB, one_mul]
              exact hterm_le m j v hv
          _ = ((Finset.univ.erase idx).card : ℝ) * M := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (d : ℝ) * M := by
              apply mul_le_mul_of_nonneg_right _ hM_nn
              have : (Finset.univ.erase idx).card ≤ d := by
                calc (Finset.univ.erase idx).card ≤ (Finset.univ : Finset (Fin d)).card :=
                      Finset.card_le_card (Finset.erase_subset _ _)
                  _ = d := Fintype.card_fin d
              exact_mod_cast this
      have hM_big : M ≤ (d : ℝ) * M := by
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
        nlinarith
      exact one_step_contraction hS h (fun v => a v idx) φ hlip
        hMh (fun v hv => (hM v hv idx).trans hM_big)
  have hfinal := hstep d le_rfl
  have h0_eq : ∀ i v, term 0 i v = φ (a v i) := fun i v => by simp [term]
  have hd_eq : ∀ i v, term d i v = a v i := fun i v => by simp [term, i.isLt]
  simp_rw [h0_eq, hd_eq] at hfinal
  exact hfinal

private lemma rademacher_max_bound {t d : ℕ} (ht : 2 ≤ t) (hd : 0 < d)
    (X : Fin d → Fin t → Bool) :
    avg (fun ε : Fin d → Bool =>
      (Finset.univ : Finset (Edge t)).sup'
        (Finset.univ_nonempty_iff.mpr ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩⟩)
        (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|)) ≤
      Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ)) := by
  have hE_univ_ne : (Finset.univ : Finset (Edge t)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩⟩
  set L : ℕ := 3 * (1 + Nat.log 2 t)
  have hL_pos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by positivity
    exact_mod_cast this
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  let lam : ℝ := Real.sqrt (2 * (L : ℝ) / (d : ℝ))
  have hlam_pos : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam_sq : lam ^ 2 = 2 * (L : ℝ) / (d : ℝ) := Real.sq_sqrt (by positivity)
  have hexp_edge : ∀ (e : Edge t) (s : ℝ), |s| = 1 →
      avg (fun ε : Fin d → Bool =>
        Real.exp (s * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i))) ≤
      Real.exp ((d : ℝ) * lam ^ 2 / 2) := by
    intro e s hs
    have hprod : ∀ ε : Fin d → Bool,
        Real.exp (s * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)) =
        ∏ i : Fin d, Real.exp (s * lam * sgnB (ε i) * edgeChar e (X i)) := by
      intro ε
      rw [Finset.mul_sum, Real.exp_sum]
      refine Finset.prod_congr rfl fun i _ => by ring_nf
    simp_rw [hprod]
    rw [avg_pi_prod (fun i b => Real.exp (s * lam * sgnB b * edgeChar e (X i)))]
    have hfactor : ∀ i : Fin d,
        avg (fun b : Bool => Real.exp (s * lam * sgnB b * edgeChar e (X i))) ≤
        Real.exp (lam ^ 2 / 2) := by
      intro i
      rw [avg_bool]
      set c : ℝ := s * edgeChar e (X i)
      have hc_abs : |c| = 1 := by simp [c, abs_mul, hs, abs_edgeChar]
      have hc_sq : c ^ 2 = 1 := by rw [← sq_abs, hc_abs, one_pow]
      have h1 : s * lam * sgnB true * edgeChar e (X i) = c * lam := by simp [sgnB, c]; ring
      have h2 : s * lam * sgnB false * edgeChar e (X i) = -(c * lam) := by simp [sgnB, c]; ring
      rw [h1, h2, ← Real.cosh_eq]
      calc Real.cosh (c * lam) ≤ Real.exp ((c * lam) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
        _ = Real.exp (lam ^ 2 / 2) := by rw [mul_pow, hc_sq, one_mul]
    calc ∏ i : Fin d, avg (fun b : Bool => Real.exp (s * lam * sgnB b * edgeChar e (X i)))
        ≤ ∏ _i : Fin d, Real.exp (lam ^ 2 / 2) := by
          have hgen : ∀ s0 : Finset (Fin d),
              ∏ i ∈ s0, avg (fun b : Bool => Real.exp (s * lam * sgnB b * edgeChar e (X i))) ≤
              ∏ _i ∈ s0, Real.exp (lam ^ 2 / 2) := by
            intro s0
            induction s0 using Finset.cons_induction with
            | empty => simp
            | cons a s' ha ih =>
              rw [Finset.prod_cons, Finset.prod_cons]
              exact mul_le_mul (hfactor a) ih
                (Finset.prod_nonneg fun i _ => avg_nonneg fun b => le_of_lt (Real.exp_pos _))
                (le_of_lt (Real.exp_pos _))
          exact hgen Finset.univ
      _ = Real.exp ((d : ℝ) * lam ^ 2 / 2) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
          congr 1; ring
  let Mfun : (Fin d → Bool) → ℝ := fun ε =>
    (Finset.univ : Finset (Edge t)).sup' hE_univ_ne
      (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|)
  have hexp_max : avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε)) ≤
      (2 * (Fintype.card (Edge t) : ℝ)) * Real.exp ((d : ℝ) * lam ^ 2 / 2) := by
    have hpt : ∀ ε : Fin d → Bool,
        Real.exp (lam * Mfun ε) ≤
        ∑ e : Edge t, (Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)) +
          Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i))) := by
      intro ε
      obtain ⟨e₀, _, he₀⟩ := Finset.exists_mem_eq_sup' hE_univ_ne
        (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|)
      have hterm : Real.exp (lam * Mfun ε) ≤
          Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e₀ (X i)) +
          Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e₀ (X i)) := by
        dsimp only [Mfun]
        rw [he₀]
        set S0 : ℝ := ∑ i : Fin d, sgnB (ε i) * edgeChar e₀ (X i)
        by_cases hS0 : 0 ≤ S0
        · rw [abs_of_nonneg hS0, show lam * S0 = 1 * lam * S0 by ring]
          have : 0 ≤ Real.exp ((-1) * lam * S0) := le_of_lt (Real.exp_pos _)
          linarith
        · rw [abs_of_neg (lt_of_not_ge hS0), show lam * -S0 = (-1) * lam * S0 by ring]
          have : 0 ≤ Real.exp (1 * lam * S0) := le_of_lt (Real.exp_pos _)
          linarith
      exact hterm.trans (Finset.single_le_sum (fun e _ => add_nonneg
        (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))) (Finset.mem_univ e₀))
    have havg_sum_eq :
        avg (fun ε : Fin d → Bool => ∑ e : Edge t,
          (Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)) +
           Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)))) =
        ∑ e : Edge t,
          (avg (fun ε : Fin d → Bool => Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i))) +
           avg (fun ε : Fin d → Bool => Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)))) := by
      rw [avg_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      exact avg_add
        (fun ε : Fin d → Bool => Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)))
        (fun ε : Fin d → Bool => Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)))
    calc avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε))
        ≤ avg (fun ε : Fin d → Bool => ∑ e : Edge t,
            (Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)) +
             Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)))) :=
          avg_mono hpt
      _ = ∑ e : Edge t,
            (avg (fun ε : Fin d → Bool => Real.exp (1 * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i))) +
             avg (fun ε : Fin d → Bool => Real.exp ((-1) * lam * ∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)))) :=
          havg_sum_eq
      _ ≤ ∑ _e : Edge t, (Real.exp ((d : ℝ) * lam ^ 2 / 2) + Real.exp ((d : ℝ) * lam ^ 2 / 2)) := by
          refine Finset.sum_le_sum fun e _ => add_le_add
            (hexp_edge e 1 (by norm_num)) (hexp_edge e (-1) (by norm_num))
      _ = (2 * (Fintype.card (Edge t) : ℝ)) * Real.exp ((d : ℝ) * lam ^ 2 / 2) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have h2E_le : 2 * (Fintype.card (Edge t) : ℝ) ≤ Real.exp (L : ℝ) := by
    have hcard_le : Fintype.card (Edge t) ≤ t * t := by
      have h1 : Fintype.card (Edge t) ≤ Fintype.card (Fin t × Fin t) :=
        Fintype.card_subtype_le _
      simpa [Fintype.card_prod, Fintype.card_fin] using h1
    have ht_lt : t < 2 ^ (1 + Nat.log 2 t) := by
      rw [add_comm]
      exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) t
    have hnat : 2 * Fintype.card (Edge t) ≤ 2 ^ L := by
      have h1 : 2 * Fintype.card (Edge t) ≤ 2 * (t * t) := Nat.mul_le_mul_left 2 hcard_le
      have h2 : t * t ≤ 2 ^ (1 + Nat.log 2 t) * 2 ^ (1 + Nat.log 2 t) :=
        Nat.mul_le_mul (Nat.le_of_lt ht_lt) (Nat.le_of_lt ht_lt)
      have h3 : 2 * (2 ^ (1 + Nat.log 2 t) * 2 ^ (1 + Nat.log 2 t)) ≤ 2 ^ L := by
        rw [← pow_add, ← pow_succ']
        apply Nat.pow_le_pow_right (by norm_num)
        dsimp only [L]
        omega
      exact h1.trans ((Nat.mul_le_mul_left 2 h2).trans h3)
    have hreal : (2 * (Fintype.card (Edge t) : ℝ)) ≤ (2 : ℝ) ^ L := by exact_mod_cast hnat
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc 2 * (Fintype.card (Edge t) : ℝ) ≤ (2 : ℝ) ^ L := hreal
      _ ≤ (Real.exp 1) ^ L := pow_le_pow_left₀ (by norm_num) h2e L
      _ = Real.exp (L : ℝ) := by rw [← Real.exp_nat_mul, mul_one]
  have hexp_tot : avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε)) ≤
      Real.exp ((L : ℝ) + (d : ℝ) * lam ^ 2 / 2) := by
    rw [Real.exp_add]
    exact hexp_max.trans (mul_le_mul_of_nonneg_right h2E_le (le_of_lt (Real.exp_pos _)))
  set μ : ℝ := (L : ℝ) + (d : ℝ) * lam ^ 2 / 2
  have hlin : avg (fun ε : Fin d → Bool => lam * Mfun ε - μ + 1) ≤ 1 := by
    have h1 : avg (fun ε : Fin d → Bool => lam * Mfun ε - μ + 1) ≤
        avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε - μ)) :=
      avg_mono fun ε => Real.add_one_le_exp _
    have h2 : avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε - μ)) =
        (Real.exp μ)⁻¹ * avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε)) := by
      have hpt : ∀ ε, Real.exp (lam * Mfun ε - μ) = (Real.exp μ)⁻¹ * Real.exp (lam * Mfun ε) := by
        intro ε; rw [Real.exp_sub, div_eq_inv_mul]
      simp_rw [hpt]
      exact avg_const_mul _ _
    rw [h2] at h1
    have h3 : (Real.exp μ)⁻¹ * avg (fun ε : Fin d → Bool => Real.exp (lam * Mfun ε)) ≤
        (Real.exp μ)⁻¹ * Real.exp μ :=
      mul_le_mul_of_nonneg_left hexp_tot (inv_nonneg.mpr (le_of_lt (Real.exp_pos _)))
    rw [inv_mul_cancel₀ (ne_of_gt (Real.exp_pos _))] at h3
    exact h1.trans h3
  rw [avg_add, avg_sub, avg_const_mul, avg_const, avg_const] at hlin
  have hlam_avg : lam * avg Mfun ≤ 2 * (L : ℝ) := by
    have hμ : μ = 2 * (L : ℝ) := by
      dsimp only [μ]
      rw [hlam_sq]
      field_simp
      ring
    linarith
  have hrhs : lam * Real.sqrt (2 * (d : ℝ) * (L : ℝ)) = 2 * (L : ℝ) := by
    dsimp only [lam]
    rw [← Real.sqrt_mul (by positivity)]
    have hEq : 2 * (L : ℝ) / (d : ℝ) * (2 * (d : ℝ) * (L : ℝ)) = (2 * (L : ℝ)) ^ 2 := by
      field_simp
    rw [hEq, Real.sqrt_sq (by positivity)]
  have hle : lam * avg Mfun ≤ lam * Real.sqrt (2 * (d : ℝ) * (L : ℝ)) := by
    rw [hrhs]; exact hlam_avg
  exact le_of_mul_le_mul_left hle hlam_pos

private lemma empirical_symmetrization {t k d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hlip : ∀ u w, |φ u - φ w| ≤ |u - w|) (hφ0 : φ 0 = 0) :
    let B : Set (Edge t → ℝ) := {v | ∑ e : Edge t, |v e| ≤ 2 * Real.sqrt (k : ℝ)}
    avg (fun X : Fin d → Fin t → Bool =>
      sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (X i))) -
        avg (fun σ => φ (quadForm v σ))|) '' B)) ≤
    2 * (d : ℝ)⁻¹ * avg (fun X : Fin d → Fin t → Bool =>
      avg (fun ε : Fin d → Bool =>
        sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))) := by
  intro B
  have hB_ne : B.Nonempty := ⟨0, by simp [B]⟩
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set R : ℝ := 2 * Real.sqrt (k : ℝ)
  have hφ_le : ∀ v ∈ B, ∀ σ : Fin t → Bool, |φ (quadForm v σ)| ≤ R := by
    intro v hv σ
    have h := hlip (quadForm v σ) 0
    rw [hφ0, sub_zero, sub_zero] at h
    calc |φ (quadForm v σ)| ≤ |quadForm v σ| := h
      _ ≤ ∑ e : Edge t, |v e * edgeChar e σ| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ e : Edge t, |v e| := Finset.sum_congr rfl fun e _ => by rw [abs_mul, abs_edgeChar, mul_one]
      _ ≤ R := hv
  have hsym1 : ∀ X : Fin d → Fin t → Bool,
      sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (X i))) -
        avg (fun σ => φ (quadForm v σ))|) '' B) ≤
      avg (fun X' : Fin d → Fin t → Bool =>
        sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (X i)) - φ (quadForm v (X' i)))|) '' B)) := by
    intro X
    apply csSup_le (hB_ne.image _)
    rintro _ ⟨v, hv, rfl⟩
    dsimp only
    have hexp_eq : avg (fun σ => φ (quadForm v σ)) =
        avg (fun X' : Fin d → Fin t → Bool => (d : ℝ)⁻¹ * ∑ i : Fin d, φ (quadForm v (X' i))) := by
      rw [avg_const_mul, avg_sum]
      have hcoord : ∀ i : Fin d, avg (fun X' : Fin d → Fin t → Bool => φ (quadForm v (X' i))) =
          avg (fun σ => φ (quadForm v σ)) := by
        intro i
        let e : (Fin t → Bool) × ({j : Fin d // j ≠ i} → Fin t → Bool) ≃ (Fin d → Fin t → Bool) :=
          (Equiv.piSplitAt i (fun _ : Fin d => Fin t → Bool)).symm
        rw [← avg_equiv e, avg_prod]
        have h1 : ∀ σ, avg (fun rest : {j : Fin d // j ≠ i} → Fin t → Bool =>
            φ (quadForm v (e (σ, rest) i))) = φ (quadForm v σ) := by
          intro σ
          have h2 : ∀ rest, e (σ, rest) i = σ := fun rest => by simp [e, Equiv.piSplitAt]
          simp_rw [h2]
          exact avg_const _
        simp_rw [h1]
      simp_rw [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hd_pos), one_mul]
    have hdiff : (d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (X i))) - avg (fun σ => φ (quadForm v σ)) =
        avg (fun X' : Fin d → Fin t → Bool =>
          (d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (X i)) - φ (quadForm v (X' i)))) := by
      rw [hexp_eq, ← avg_const (α := Fin d → Fin t → Bool) ((d : ℝ)⁻¹ * ∑ i : Fin d, φ (quadForm v (X i))),
        ← avg_sub]
      congr 1; funext X'
      rw [Finset.sum_sub_distrib, mul_sub]
    rw [hdiff]
    have habs_avg : |avg (fun X' : Fin d → Fin t → Bool =>
        (d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (X i)) - φ (quadForm v (X' i))))| ≤
        avg (fun X' : Fin d → Fin t → Bool =>
          |(d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (X i)) - φ (quadForm v (X' i)))|) := by
      unfold avg
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    refine habs_avg.trans (avg_mono fun X' => ?_)
    apply le_csSup
    · refine ⟨2 * R, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      dsimp only
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hd_pos))]
      calc (d : ℝ)⁻¹ * |∑ i : Fin d, (φ (quadForm u (X i)) - φ (quadForm u (X' i)))|
          ≤ (d : ℝ)⁻¹ * ∑ i : Fin d, |φ (quadForm u (X i)) - φ (quadForm u (X' i))| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (d : ℝ)⁻¹ * ∑ _i : Fin d, (2 * R) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by positivity)
            calc |φ (quadForm u (X i)) - φ (quadForm u (X' i))|
                ≤ |φ (quadForm u (X i))| + |φ (quadForm u (X' i))| := abs_sub _ _
              _ ≤ R + R := add_le_add (hφ_le u hu _) (hφ_le u hu _)
              _ = 2 * R := by ring
        _ = 2 * R := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hd_pos), one_mul]
    · exact ⟨v, hv, rfl⟩
  have h1 : avg (fun X : Fin d → Fin t → Bool =>
        sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (X i))) -
          avg (fun σ => φ (quadForm v σ))|) '' B)) ≤
      avg (fun p : (Fin d → Fin t → Bool) × (Fin d → Fin t → Bool) =>
        sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (p.1 i)) - φ (quadForm v (p.2 i)))|) '' B)) := by
    rw [avg_prod]
    exact avg_mono hsym1
  have hswap : ∀ ε : Fin d → Bool,
      avg (fun p : (Fin d → Fin t → Bool) × (Fin d → Fin t → Bool) =>
        sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (p.1 i)) - φ (quadForm v (p.2 i)))|) '' B)) =
      avg (fun p : (Fin d → Fin t → Bool) × (Fin d → Fin t → Bool) =>
        sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, sgnB (ε i) * (φ (quadForm v (p.1 i)) - φ (quadForm v (p.2 i)))|) '' B)) := by
    intro ε
    let sw : ((Fin d → Fin t → Bool) × (Fin d → Fin t → Bool)) ≃
        ((Fin d → Fin t → Bool) × (Fin d → Fin t → Bool)) :=
      { toFun := fun p => (fun i => if ε i then p.1 i else p.2 i, fun i => if ε i then p.2 i else p.1 i)
        invFun := fun p => (fun i => if ε i then p.1 i else p.2 i, fun i => if ε i then p.2 i else p.1 i)
        left_inv := fun ⟨X, X'⟩ => by
          apply Prod.ext <;> (ext i j; cases hε : ε i <;> simp [hε])
        right_inv := fun ⟨X, X'⟩ => by
          apply Prod.ext <;> (ext i j; cases hε : ε i <;> simp [hε]) }
    rw [← avg_equiv sw]
    congr 1; funext ⟨X, X'⟩
    congr 1
    apply Set.image_congr
    intro v _
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    cases hε : ε i <;> simp [sw, sgnB, hε]
  have htri : ∀ (ε : Fin d → Bool) (X X' : Fin d → Fin t → Bool),
      sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, sgnB (ε i) * (φ (quadForm v (X i)) - φ (quadForm v (X' i)))|) '' B) ≤
      (d : ℝ)⁻¹ * sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B) +
      (d : ℝ)⁻¹ * sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X' i))|) '' B) := by
    intro ε X X'
    have hbdd : ∀ Y : Fin d → Fin t → Bool,
        BddAbove ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (Y i))|) '' B) := by
      intro Y
      refine ⟨(d : ℝ) * R, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      dsimp only
      calc |∑ i : Fin d, sgnB (ε i) * φ (quadForm u (Y i))|
          ≤ ∑ i : Fin d, |sgnB (ε i) * φ (quadForm u (Y i))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin d, R := Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_sgnB, one_mul]; exact hφ_le u hu _
        _ = (d : ℝ) * R := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    apply csSup_le (hB_ne.image _)
    rintro _ ⟨v, hv, rfl⟩
    dsimp only
    have hsp : ∑ i : Fin d, sgnB (ε i) * (φ (quadForm v (X i)) - φ (quadForm v (X' i))) =
        (∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) -
        (∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X' i))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsp, abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hd_pos))]
    have hle1 : |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))| ≤
        sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B) :=
      le_csSup (hbdd X) ⟨v, hv, rfl⟩
    have hle2 : |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X' i))| ≤
        sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X' i))|) '' B) :=
      le_csSup (hbdd X') ⟨v, hv, rfl⟩
    have hsub := abs_sub (∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i)))
      (∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X' i)))
    have hd_inv_nn : 0 ≤ (d : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hd_pos)
    calc (d : ℝ)⁻¹ * |(∑ i, sgnB (ε i) * φ (quadForm v (X i))) -
          (∑ i, sgnB (ε i) * φ (quadForm v (X' i)))|
        ≤ (d : ℝ)⁻¹ * (|∑ i, sgnB (ε i) * φ (quadForm v (X i))| +
          |∑ i, sgnB (ε i) * φ (quadForm v (X' i))|) := mul_le_mul_of_nonneg_left hsub hd_inv_nn
      _ ≤ (d : ℝ)⁻¹ * (sSup ((fun v => |∑ i, sgnB (ε i) * φ (quadForm v (X i))|) '' B) +
          sSup ((fun v => |∑ i, sgnB (ε i) * φ (quadForm v (X' i))|) '' B)) :=
          mul_le_mul_of_nonneg_left (add_le_add hle1 hle2) hd_inv_nn
      _ = _ := by ring
  have havg_ε :
      avg (fun p : (Fin d → Fin t → Bool) × (Fin d → Fin t → Bool) =>
        sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (p.1 i)) - φ (quadForm v (p.2 i)))|) '' B)) ≤
      avg (fun ε : Fin d → Bool =>
        2 * (d : ℝ)⁻¹ * avg (fun X : Fin d → Fin t → Bool =>
          sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))) := by
    rw [← avg_const (α := Fin d → Bool) (avg (fun p : (Fin d → Fin t → Bool) × (Fin d → Fin t → Bool) =>
      sSup ((fun v => |(d : ℝ)⁻¹ * ∑ i : Fin d, (φ (quadForm v (p.1 i)) - φ (quadForm v (p.2 i)))|) '' B)))]
    refine avg_mono fun ε => ?_
    rw [hswap ε]
    have hle := avg_mono fun p : (Fin d → Fin t → Bool) × (Fin d → Fin t → Bool) => htri ε p.1 p.2
    refine hle.trans (le_of_eq ?_)
    rw [avg_add, avg_prod, avg_prod]
    have hA : avg (fun X : Fin d → Fin t → Bool => avg (fun _X' : Fin d → Fin t → Bool =>
        (d : ℝ)⁻¹ * sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))) =
        (d : ℝ)⁻¹ * avg (fun X : Fin d → Fin t → Bool =>
          sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B)) := by
      simp_rw [avg_const]
      exact avg_const_mul _ _
    have hB : avg (fun _X : Fin d → Fin t → Bool => avg (fun X' : Fin d → Fin t → Bool =>
        (d : ℝ)⁻¹ * sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X' i))|) '' B))) =
        (d : ℝ)⁻¹ * avg (fun X : Fin d → Fin t → Bool =>
          sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B)) := by
      rw [avg_const, avg_const_mul]
    rw [hA, hB]; ring
  refine (h1.trans havg_ε).trans (le_of_eq ?_)
  rw [avg_const_mul, avg_prod_comm]

private lemma rademacher_sup_bound {t k d : ℕ} (ht : 2 ≤ t) (hd : 0 < d)
    (φ : ℝ → ℝ) (hlip : ∀ u w, |φ u - φ w| ≤ |u - w|) (hφ0 : φ 0 = 0)
    (X : Fin d → Fin t → Bool) :
    let B : Set (Edge t → ℝ) := {v | ∑ e : Edge t, |v e| ≤ 2 * Real.sqrt (k : ℝ)}
    avg (fun ε : Fin d → Bool =>
      sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B)) ≤
    2 * (2 * Real.sqrt (k : ℝ)) * Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ)) := by
  intro B
  have hB_ne : B.Nonempty := ⟨0, by simp [B]⟩
  set R : ℝ := 2 * Real.sqrt (k : ℝ)
  have hR_nn : 0 ≤ R := by positivity
  have hQ_le : ∀ v ∈ B, ∀ σ : Fin t → Bool, |quadForm v σ| ≤ R := by
    intro v hv σ
    calc |quadForm v σ| ≤ ∑ e : Edge t, |v e * edgeChar e σ| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ e : Edge t, |v e| := Finset.sum_congr rfl fun e _ => by rw [abs_mul, abs_edgeChar, mul_one]
      _ ≤ R := hv
  have hφ_le : ∀ v ∈ B, ∀ σ : Fin t → Bool, |φ (quadForm v σ)| ≤ R := by
    intro v hv σ
    have h := hlip (quadForm v σ) 0
    rw [hφ0, sub_zero, sub_zero] at h
    exact h.trans (hQ_le v hv σ)
  have hdrop : avg (fun ε : Fin d → Bool =>
      sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B)) ≤
      2 * avg (fun ε : Fin d → Bool =>
        sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B)) := by
    have hpt : ∀ ε : Fin d → Bool,
        sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B) ≤
        sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B) +
        sSup ((fun v => ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i))) '' B) := by
      intro ε
      have hbdd : ∀ ε' : Fin d → Bool,
          BddAbove ((fun v => ∑ i : Fin d, sgnB (ε' i) * φ (quadForm v (X i))) '' B) := by
        intro ε'
        refine ⟨(d : ℝ) * R, ?_⟩
        rintro _ ⟨u, hu, rfl⟩
        dsimp only
        calc ∑ i : Fin d, sgnB (ε' i) * φ (quadForm u (X i))
            ≤ ∑ i : Fin d, |sgnB (ε' i) * φ (quadForm u (X i))| :=
              Finset.sum_le_sum fun i _ => le_abs_self _
          _ ≤ ∑ _i : Fin d, R := Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_sgnB, one_mul]; exact hφ_le u hu _
          _ = (d : ℝ) * R := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h0_nn : ∀ ε' : Fin d → Bool,
          0 ≤ sSup ((fun v => ∑ i : Fin d, sgnB (ε' i) * φ (quadForm v (X i))) '' B) := by
        intro ε'
        have h0 : ∑ i : Fin d, sgnB (ε' i) * φ (quadForm (0 : Edge t → ℝ) (X i)) = 0 := by
          simp [quadForm, hφ0]
        rw [← h0]
        exact le_csSup (hbdd ε') ⟨0, by simp [B], rfl⟩
      apply csSup_le (hB_ne.image _)
      rintro _ ⟨v, hv, rfl⟩
      dsimp only
      have hneg_sum : ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i)) =
          -(∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) := by
        simp_rw [sgnB_not, neg_mul, Finset.sum_neg_distrib]
      have hp : ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i)) ≤
          sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B) :=
        le_csSup (hbdd ε) ⟨v, hv, rfl⟩
      have hm : -(∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) ≤
          sSup ((fun v => ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i))) '' B) := by
        rw [← hneg_sum]
        exact le_csSup (hbdd (fun i => !(ε i))) ⟨v, hv, rfl⟩
      have h1 := h0_nn ε
      have h2 := h0_nn (fun i => !(ε i))
      rw [abs_le]
      constructor <;> linarith
    have hneg_equiv : avg (fun ε : Fin d → Bool =>
        sSup ((fun v => ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i))) '' B)) =
        avg (fun ε : Fin d → Bool =>
          sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B)) := by
      let negE : (Fin d → Bool) ≃ (Fin d → Bool) :=
        { toFun := fun ε i => !(ε i)
          invFun := fun ε i => !(ε i)
          left_inv := fun ε => by ext i; simp
          right_inv := fun ε => by ext i; simp }
      exact avg_equiv negE
        (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B))
    calc avg (fun ε : Fin d → Bool => sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))
        ≤ avg (fun ε : Fin d → Bool =>
            sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B) +
            sSup ((fun v => ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i))) '' B)) :=
          avg_mono hpt
      _ = avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B)) +
          avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i))) '' B)) :=
          avg_add
            (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B))
            (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (!(ε i)) * φ (quadForm v (X i))) '' B))
      _ = 2 * avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B)) := by
          rw [hneg_equiv]; ring
  have hcont : avg (fun ε : Fin d → Bool =>
      sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B)) ≤
      avg (fun ε : Fin d → Bool =>
        sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * quadForm v (X i)) '' B)) :=
    rademacher_contraction hB_ne (fun v i => quadForm v (X i)) φ hlip hφ0 hR_nn
      (fun v hv i => hQ_le v hv (X i))
  have hE_univ_ne : (Finset.univ : Finset (Edge t)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩⟩
  have hholder : ∀ ε : Fin d → Bool,
      sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * quadForm v (X i)) '' B) ≤
      R * (Finset.univ : Finset (Edge t)).sup' hE_univ_ne
        (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|) := by
    intro ε
    apply csSup_le (hB_ne.image _)
    rintro _ ⟨v, hv, rfl⟩
    dsimp only
    set Mε : ℝ := (Finset.univ : Finset (Edge t)).sup' hE_univ_ne
      (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|)
    have hMε_nn : 0 ≤ Mε := by
      obtain ⟨e₀, he₀⟩ := hE_univ_ne
      exact le_trans (abs_nonneg _)
        (Finset.le_sup' (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|) he₀)
    have hswap_sum : ∑ i : Fin d, sgnB (ε i) * quadForm v (X i) =
        ∑ e : Edge t, v e * (∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)) := by
      simp only [quadForm, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hswap_sum]
    calc ∑ e : Edge t, v e * (∑ i : Fin d, sgnB (ε i) * edgeChar e (X i))
        ≤ ∑ e : Edge t, |v e * (∑ i : Fin d, sgnB (ε i) * edgeChar e (X i))| :=
          Finset.sum_le_sum fun e _ => le_abs_self _
      _ = ∑ e : Edge t, |v e| * |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)| :=
          Finset.sum_congr rfl fun e _ => abs_mul _ _
      _ ≤ ∑ e : Edge t, |v e| * Mε :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|) (Finset.mem_univ e))
            (abs_nonneg _)
      _ = (∑ e : Edge t, |v e|) * Mε := (Finset.sum_mul _ _ _).symm
      _ ≤ R * Mε := mul_le_mul_of_nonneg_right hv hMε_nn
  calc avg (fun ε : Fin d → Bool => sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))
      ≤ 2 * avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))) '' B)) := hdrop
    _ ≤ 2 * avg (fun ε : Fin d → Bool => sSup ((fun v => ∑ i : Fin d, sgnB (ε i) * quadForm v (X i)) '' B)) :=
        mul_le_mul_of_nonneg_left hcont (by norm_num)
    _ ≤ 2 * avg (fun ε : Fin d → Bool => R * (Finset.univ : Finset (Edge t)).sup' hE_univ_ne
          (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|)) :=
        mul_le_mul_of_nonneg_left (avg_mono hholder) (by norm_num)
    _ = 2 * R * avg (fun ε : Fin d → Bool => (Finset.univ : Finset (Edge t)).sup' hE_univ_ne
          (fun e => |∑ i : Fin d, sgnB (ε i) * edgeChar e (X i)|)) := by
        rw [avg_const_mul]; ring
    _ ≤ 2 * R * Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ)) :=
        mul_le_mul_of_nonneg_left (rademacher_max_bound ht hd X) (by positivity)

private lemma empirical_dev_bound {t k d : ℕ} (ht : 2 ≤ t) (hd : 0 < d)
    (φ : ℝ → ℝ) (hlip : ∀ u w, |φ u - φ w| ≤ |u - w|) (hφ0 : φ 0 = 0) :
    let B : Set (Edge t → ℝ) := {v | ∑ e : Edge t, |v e| ≤ 2 * Real.sqrt (k : ℝ)}
    avg (fun X : Fin d → Fin t → Bool =>
      sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (X i))) -
        avg (fun σ => φ (quadForm v σ))|) '' B)) ≤
    8 * Real.sqrt (2 * (k : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ) / (d : ℝ)) := by
  intro B
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsym := empirical_symmetrization (t := t) (k := k) hd φ hlip hφ0
  have havg_inner : avg (fun X : Fin d → Fin t → Bool => avg (fun ε : Fin d → Bool =>
        sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))) ≤
      2 * (2 * Real.sqrt (k : ℝ)) * Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ)) := by
    calc avg (fun X : Fin d → Fin t → Bool => avg (fun ε : Fin d → Bool =>
            sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B)))
        ≤ avg (fun _X : Fin d → Fin t → Bool =>
            2 * (2 * Real.sqrt (k : ℝ)) * Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ))) :=
          avg_mono fun X => rademacher_sup_bound ht hd φ hlip hφ0 X
      _ = 2 * (2 * Real.sqrt (k : ℝ)) * Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ)) := avg_const _
  calc avg (fun X : Fin d → Fin t → Bool =>
          sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (X i))) -
            avg (fun σ => φ (quadForm v σ))|) '' B))
      ≤ 2 * (d : ℝ)⁻¹ * avg (fun X : Fin d → Fin t → Bool => avg (fun ε : Fin d → Bool =>
          sSup ((fun v => |∑ i : Fin d, sgnB (ε i) * φ (quadForm v (X i))|) '' B))) := hsym
    _ ≤ 2 * (d : ℝ)⁻¹ * (2 * (2 * Real.sqrt (k : ℝ)) * Real.sqrt (2 * (d : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ))) :=
        mul_le_mul_of_nonneg_left havg_inner (by positivity)
    _ = 8 * Real.sqrt (2 * (k : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ) / (d : ℝ)) := by
        set Lr : ℝ := ((3 * (1 + Nat.log 2 t) : ℕ) : ℝ)
        have hLr_nn : 0 ≤ Lr := by positivity
        have hk_r : (0 : ℝ) ≤ (k : ℝ) := by positivity
        have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
        have hsqrt_d : (d : ℝ)⁻¹ = Real.sqrt ((d : ℝ)⁻¹ ^ 2) := by
          rw [Real.sqrt_sq (inv_nonneg.mpr (le_of_lt hd_pos))]
        calc 2 * (d : ℝ)⁻¹ * (2 * (2 * Real.sqrt (k : ℝ)) * Real.sqrt (2 * (d : ℝ) * Lr))
            = 8 * ((d : ℝ)⁻¹ * (Real.sqrt (k : ℝ) * Real.sqrt (2 * (d : ℝ) * Lr))) := by ring
          _ = 8 * (Real.sqrt ((d : ℝ)⁻¹ ^ 2) * Real.sqrt ((k : ℝ) * (2 * (d : ℝ) * Lr))) := by
              rw [← hsqrt_d, ← Real.sqrt_mul hk_r]
          _ = 8 * Real.sqrt ((d : ℝ)⁻¹ ^ 2 * ((k : ℝ) * (2 * (d : ℝ) * Lr))) := by
              rw [← Real.sqrt_mul (sq_nonneg _)]
          _ = 8 * Real.sqrt (2 * (k : ℝ) * Lr / (d : ℝ)) := by
              congr 2; field_simp

private lemma main_theorem :
    ∃ C : ℕ, 0 < C ∧ ∀ (t k : ℕ), 2 ≤ t → 0 < k →
      let T := Fin t
      let E := {p : T × T // p.1 < p.2}
      ∃ (d : ℕ) (pin : Fin d → T → Bool),
        0 < d ∧ d ≤ C * k * (1 + Nat.log 2 t) ∧
        ∀ (v : E → ℝ) (S : Finset (Fin d)),
          let norm := Real.sqrt (∑ e : E, (v e) ^ 2)
          let sgn := fun (i : Fin d) (j : T) => if pin i j then (1 : ℝ) else -1
          let a := fun i => |∑ e : E, v e * sgn i e.val.1 * sgn i e.val.2|
          (∑ e : E, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * norm →
          400 * S.card ≤ d →
          (d : ℝ) * norm + 256 * (∑ i ∈ S, a i) ≤ 128 * (∑ i, a i) := by
  refine ⟨500000000, by norm_num, fun t k ht hk => ?_⟩
  let d : ℕ := 500000000 * k * (1 + Nat.log 2 t)
  have hd_pos_nat : 0 < d := by positivity
  have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos_nat
  let B : Set (Edge t → ℝ) := {v | ∑ e : Edge t, |v e| ≤ 2 * Real.sqrt (k : ℝ)}
  let φ₁ : ℝ → ℝ := fun x => |x|
  let φ₂ : ℝ → ℝ := fun x => max (0 : ℝ) (|x| - 10)
  have hlip₁ : ∀ u w, |φ₁ u - φ₁ w| ≤ |u - w| := fun u w => abs_abs_sub_abs_le_abs_sub u w
  have hlip₂ : ∀ u w, |φ₂ u - φ₂ w| ≤ |u - w| := by
    intro u w
    have hmax : ∀ a b : ℝ, |max (0 : ℝ) a - max (0 : ℝ) b| ≤ |a - b| := by
      intro a b
      rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
      · rw [max_eq_right ha, max_eq_right hb]
      · rw [max_eq_right ha, max_eq_left hb, sub_zero, abs_of_nonneg ha, abs_of_nonneg (by linarith)]
        linarith
      · rw [max_eq_left ha, max_eq_right hb, zero_sub, abs_neg, abs_of_nonneg hb,
          abs_of_nonpos (by linarith)]
        linarith
      · rw [max_eq_left ha, max_eq_left hb, sub_self, abs_zero]
        exact abs_nonneg _
    have h1 : |max (0 : ℝ) (|u| - 10) - max (0 : ℝ) (|w| - 10)| ≤ |(|u| - 10) - (|w| - 10)| :=
      hmax _ _
    have h2 : |(|u| - 10) - (|w| - 10)| = |(|u| - |w|)| := by ring_nf
    rw [h2] at h1
    exact h1.trans (abs_abs_sub_abs_le_abs_sub u w)
  have hφ₁0 : φ₁ 0 = 0 := by simp [φ₁]
  have hφ₂0 : φ₂ 0 = 0 := by norm_num [φ₂]
  let Z₁ : (Fin d → Fin t → Bool) → ℝ := fun X =>
    sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ₁ (quadForm v (X i))) -
      avg (fun σ => φ₁ (quadForm v σ))|) '' B)
  let Z₂ : (Fin d → Fin t → Bool) → ℝ := fun X =>
    sSup ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ₂ (quadForm v (X i))) -
      avg (fun σ => φ₂ (quadForm v σ))|) '' B)
  have hZ₁_le : avg Z₁ ≤ 8 * Real.sqrt (2 * (k : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ) / (d : ℝ)) :=
    empirical_dev_bound ht hd_pos_nat φ₁ hlip₁ hφ₁0
  have hZ₂_le : avg Z₂ ≤ 8 * Real.sqrt (2 * (k : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ) / (d : ℝ)) :=
    empirical_dev_bound ht hd_pos_nat φ₂ hlip₂ hφ₂0
  have hsqrt_le : 16 * Real.sqrt (2 * (k : ℝ) * (3 * (1 + Nat.log 2 t) : ℕ) / (d : ℝ)) ≤ 1 / 512 := by
    have hratio : 2 * (k : ℝ) * ((3 * (1 + Nat.log 2 t) : ℕ) : ℝ) / (d : ℝ) = 6 / 500000000 := by
      dsimp only [d]
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk)
      have hlog0 : (1 + (Nat.log 2 t : ℝ)) ≠ 0 := by positivity
      field_simp
      ring
    rw [hratio]
    have hsq : (16 * Real.sqrt (6 / 500000000)) ^ 2 ≤ ((1 : ℝ) / 512) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    nlinarith [Real.sqrt_nonneg (6 / 500000000 : ℝ)]
  have havg_sum : avg (fun X => Z₁ X + Z₂ X) ≤ 1 / 512 := by
    rw [avg_add]
    linarith
  obtain ⟨pin, hpin⟩ := exists_le_avg (fun X => Z₁ X + Z₂ X)
  have hpin_le : Z₁ pin + Z₂ pin ≤ 1 / 512 := hpin.trans havg_sum
  have hbdd_Z : ∀ (φ : ℝ → ℝ), (∀ u w, |φ u - φ w| ≤ |u - w|) → φ 0 = 0 →
      BddAbove ((fun v => |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (pin i))) -
        avg (fun σ => φ (quadForm v σ))|) '' B) := by
    intro φ hlip h0
    refine ⟨4 * Real.sqrt (k : ℝ), ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    dsimp only
    have hφ_b : ∀ σ, |φ (quadForm v σ)| ≤ 2 * Real.sqrt (k : ℝ) := by
      intro σ
      have h1 := hlip (quadForm v σ) 0
      rw [h0, sub_zero, sub_zero] at h1
      calc |φ (quadForm v σ)| ≤ |quadForm v σ| := h1
        _ ≤ ∑ e : Edge t, |v e * edgeChar e σ| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ e : Edge t, |v e| := Finset.sum_congr rfl fun e _ => by rw [abs_mul, abs_edgeChar, mul_one]
        _ ≤ 2 * Real.sqrt (k : ℝ) := hv
    have h1 : |(d : ℝ)⁻¹ * ∑ i : Fin d, φ (quadForm v (pin i))| ≤ 2 * Real.sqrt (k : ℝ) := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hd_pos))]
      calc (d : ℝ)⁻¹ * |∑ i : Fin d, φ (quadForm v (pin i))|
          ≤ (d : ℝ)⁻¹ * ∑ i : Fin d, |φ (quadForm v (pin i))| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (d : ℝ)⁻¹ * ∑ _i : Fin d, (2 * Real.sqrt (k : ℝ)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hφ_b _) (by positivity)
        _ = 2 * Real.sqrt (k : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hd_pos), one_mul]
    have h2 : |avg (fun σ => φ (quadForm v σ))| ≤ 2 * Real.sqrt (k : ℝ) := by
      unfold avg
      rw [abs_mul, abs_of_nonneg (by positivity)]
      calc ((Fintype.card (Fin t → Bool) : ℝ))⁻¹ * |∑ σ, φ (quadForm v σ)|
          ≤ ((Fintype.card (Fin t → Bool) : ℝ))⁻¹ * ∑ σ, |φ (quadForm v σ)| :=
            mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ ((Fintype.card (Fin t → Bool) : ℝ))⁻¹ * ∑ _σ : Fin t → Bool, (2 * Real.sqrt (k : ℝ)) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hφ_b σ) (by positivity)
        _ = 2 * Real.sqrt (k : ℝ) := avg_const _
    calc |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (pin i))) - avg (fun σ => φ (quadForm v σ))|
        ≤ |(d : ℝ)⁻¹ * (∑ i : Fin d, φ (quadForm v (pin i)))| + |avg (fun σ => φ (quadForm v σ))| :=
          abs_sub _ _
      _ ≤ 2 * Real.sqrt (k : ℝ) + 2 * Real.sqrt (k : ℝ) := add_le_add h1 h2
      _ = 4 * Real.sqrt (k : ℝ) := by ring
  have hZ₁_nn : 0 ≤ Z₁ pin :=
    le_trans (abs_nonneg _) (le_csSup (hbdd_Z φ₁ hlip₁ hφ₁0) ⟨0, by simp [B], rfl⟩)
  have hZ₂_nn : 0 ≤ Z₂ pin :=
    le_trans (abs_nonneg _) (le_csSup (hbdd_Z φ₂ hlip₂ hφ₂0) ⟨0, by simp [B], rfl⟩)
  have hZ₁_pin : Z₁ pin ≤ 1 / 512 := by linarith
  have hZ₂_pin : Z₂ pin ≤ 1 / 512 := by linarith
  refine ⟨d, pin, hd_pos_nat, le_rfl, fun v S hv_cone hS_card => ?_⟩
  dsimp only
  set norm : ℝ := Real.sqrt (∑ e : Edge t, (v e) ^ 2)
  have ha_eq : ∀ i : Fin d,
      |∑ e : Edge t, v e * (if pin i e.val.1 = true then (1 : ℝ) else -1) *
        (if pin i e.val.2 = true then (1 : ℝ) else -1)| = |quadForm v (pin i)| := by
    intro i
    congr 1
    refine Finset.sum_congr rfl fun e _ => by simp only [edgeChar, sgnB]; ring
  have hgoal_eq :
      ((d : ℝ) * norm + 256 * ∑ i ∈ S, |quadForm v (pin i)| ≤
        128 * ∑ i : Fin d, |quadForm v (pin i)|) →
      (d : ℝ) * norm + 256 * ∑ i ∈ S,
        |∑ e : Edge t, v e * (if pin i e.val.1 = true then (1 : ℝ) else -1) *
          (if pin i e.val.2 = true then (1 : ℝ) else -1)| ≤
      128 * ∑ i : Fin d,
        |∑ e : Edge t, v e * (if pin i e.val.1 = true then (1 : ℝ) else -1) *
          (if pin i e.val.2 = true then (1 : ℝ) else -1)| := by
    intro h
    simpa only [ha_eq] using h
  apply hgoal_eq
  by_cases hnorm0 : norm = 0
  · have hsum0 : ∑ e : Edge t, (v e) ^ 2 = 0 := by
      have hsq : norm ^ 2 = ∑ e : Edge t, (v e) ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg fun e _ => sq_nonneg _)
      rw [hnorm0, zero_pow (by norm_num)] at hsq
      exact hsq.symm
    have hv0 : ∀ e : Edge t, v e = 0 := by
      intro e
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun e' _ => sq_nonneg (v e'))).mp hsum0 e (Finset.mem_univ e)
      exact sq_eq_zero_iff.mp h
    have hQ0 : ∀ i, |quadForm v (pin i)| = 0 := fun i => by simp [quadForm, hv0]
    simp only [hnorm0, hQ0, Finset.sum_const_zero, mul_zero, add_zero, le_refl]
  · have hnorm_pos : 0 < norm := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hnorm0)
    let u : Edge t → ℝ := fun e => norm⁻¹ * v e
    have hu_norm : ∑ e : Edge t, (u e) ^ 2 = 1 := by
      have hsq : ∑ e : Edge t, (v e) ^ 2 = norm ^ 2 :=
        (Real.sq_sqrt (Finset.sum_nonneg fun e _ => sq_nonneg _)).symm
      calc ∑ e : Edge t, (norm⁻¹ * v e) ^ 2
          = (norm⁻¹) ^ 2 * ∑ e : Edge t, (v e) ^ 2 := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun e _ => by ring
        _ = (norm⁻¹) ^ 2 * norm ^ 2 := by rw [hsq]
        _ = 1 := by field_simp
    have hu_B : u ∈ B := by
      show ∑ e : Edge t, |norm⁻¹ * v e| ≤ 2 * Real.sqrt (k : ℝ)
      have h1 : ∑ e : Edge t, |norm⁻¹ * v e| = norm⁻¹ * ∑ e : Edge t, |v e| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => by
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hnorm_pos))]
      rw [h1]
      calc norm⁻¹ * ∑ e : Edge t, |v e|
          ≤ norm⁻¹ * (2 * Real.sqrt (k : ℝ) * norm) :=
            mul_le_mul_of_nonneg_left hv_cone (inv_nonneg.mpr (le_of_lt hnorm_pos))
        _ = 2 * Real.sqrt (k : ℝ) := by field_simp
    have hdev₁ : |(d : ℝ)⁻¹ * (∑ i : Fin d, |quadForm u (pin i)|) -
        avg (fun σ => |quadForm u σ|)| ≤ 1 / 512 :=
      (le_csSup (hbdd_Z φ₁ hlip₁ hφ₁0) ⟨u, hu_B, rfl⟩).trans hZ₁_pin
    have hdev₂ : |(d : ℝ)⁻¹ * (∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10)) -
        avg (fun σ => max (0 : ℝ) (|quadForm u σ| - 10))| ≤ 1 / 512 :=
      (le_csSup (hbdd_Z φ₂ hlip₂ hφ₂0) ⟨u, hu_B, rfl⟩).trans hZ₂_pin
    have hmean_ge : (1 : ℝ) / 9 - 1 / 512 ≤ (d : ℝ)⁻¹ * ∑ i : Fin d, |quadForm u (pin i)| := by
      have h1 := (abs_le.mp hdev₁).1
      have h2 := quadForm_abs_ge u hu_norm
      linarith
    have hexcess_le : (d : ℝ)⁻¹ * ∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10) ≤
        81 / 4000 + 1 / 512 := by
      have h1 := (abs_le.mp hdev₂).2
      have h2 := quadForm_excess_le u hu_norm
      linarith
    have hS_le : (d : ℝ)⁻¹ * ∑ i ∈ S, |quadForm u (pin i)| ≤ 10 / 400 + (81 / 4000 + 1 / 512) := by
      have hpt : ∀ i ∈ S, |quadForm u (pin i)| ≤ 10 + max (0 : ℝ) (|quadForm u (pin i)| - 10) := by
        intro i _
        have := le_max_right (0 : ℝ) (|quadForm u (pin i)| - 10)
        linarith
      have hsumS : ∑ i ∈ S, |quadForm u (pin i)| ≤
          10 * (S.card : ℝ) + ∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10) := by
        calc ∑ i ∈ S, |quadForm u (pin i)|
            ≤ ∑ i ∈ S, (10 + max (0 : ℝ) (|quadForm u (pin i)| - 10)) := Finset.sum_le_sum hpt
          _ = 10 * (S.card : ℝ) + ∑ i ∈ S, max (0 : ℝ) (|quadForm u (pin i)| - 10) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
          _ ≤ 10 * (S.card : ℝ) + ∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10) := by
              have hle_univ : ∑ i ∈ S, max (0 : ℝ) (|quadForm u (pin i)| - 10) ≤
                  ∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10) :=
                Finset.sum_le_univ_sum_of_nonneg fun i => le_max_left (0 : ℝ) _
              linarith
      have hS_ratio : (d : ℝ)⁻¹ * (10 * (S.card : ℝ)) ≤ 10 / 400 := by
        have hSc : (400 : ℝ) * (S.card : ℝ) ≤ (d : ℝ) := by exact_mod_cast hS_card
        rw [inv_mul_eq_div, div_le_div_iff₀ hd_pos (by norm_num : (0 : ℝ) < 400)]
        linarith
      calc (d : ℝ)⁻¹ * ∑ i ∈ S, |quadForm u (pin i)|
          ≤ (d : ℝ)⁻¹ * (10 * (S.card : ℝ) + ∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10)) :=
            mul_le_mul_of_nonneg_left hsumS (by positivity)
        _ = (d : ℝ)⁻¹ * (10 * (S.card : ℝ)) +
            (d : ℝ)⁻¹ * ∑ i : Fin d, max (0 : ℝ) (|quadForm u (pin i)| - 10) := by ring
        _ ≤ 10 / 400 + (81 / 4000 + 1 / 512) := add_le_add hS_ratio hexcess_le
    have hunit : (1 : ℝ) + 256 * ((d : ℝ)⁻¹ * ∑ i ∈ S, |quadForm u (pin i)|) ≤
        128 * ((d : ℝ)⁻¹ * ∑ i : Fin d, |quadForm u (pin i)|) := by
      linarith
    have hscale : ∀ i : Fin d, |quadForm v (pin i)| = norm * |quadForm u (pin i)| := by
      intro i
      have hq : quadForm v (pin i) = norm * quadForm u (pin i) := by
        simp only [quadForm, u, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        have hne : norm ≠ 0 := ne_of_gt hnorm_pos
        field_simp
      rw [hq, abs_mul, abs_of_pos hnorm_pos]
    simp_rw [hscale, ← Finset.mul_sum]
    have hmul := mul_le_mul_of_nonneg_left hunit (mul_nonneg (le_of_lt hd_pos) (le_of_lt hnorm_pos))
    have hL : (d : ℝ) * norm * (1 + 256 * ((d : ℝ)⁻¹ * ∑ i ∈ S, |quadForm u (pin i)|)) =
        (d : ℝ) * norm + 256 * (norm * ∑ i ∈ S, |quadForm u (pin i)|) := by
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
      field_simp
    have hR : (d : ℝ) * norm * (128 * ((d : ℝ)⁻¹ * ∑ i : Fin d, |quadForm u (pin i)|)) =
        128 * (norm * ∑ i : Fin d, |quadForm u (pin i)|) := by
      have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
      field_simp
    linarith

end PEqualNP.Outside.L_lib_1069_aux

theorem PEqualNP.Outside.L_lib_1069 : (∃ C : ℕ, 0 < C ∧ ∀ (t k : ℕ), 2 ≤ t → 0 < k →
  let T := Fin t
  let E := {p : T × T // p.1 < p.2}
  ∃ (d : ℕ) (pin : Fin d → T → Bool),
    0 < d ∧ d ≤ C*k*(1+Nat.log 2 t) ∧
    ∀ (v : E → ℝ) (S : Finset (Fin d)),
      let norm := Real.sqrt (∑ e : E, (v e)^2)
      let sgn := fun (i : Fin d) (j : T) => if pin i j then (1 : ℝ) else -1
      let a := fun i => |∑ e : E, v e * sgn i e.val.1 * sgn i e.val.2|
      (∑ e : E, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * norm →
      400*S.card ≤ d →
      (d : ℝ)*norm + 256*(∑ i ∈ S, a i) ≤ 128*(∑ i, a i)) :=
  PEqualNP.Outside.L_lib_1069_aux.main_theorem
