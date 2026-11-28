import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_464_aux

open PEqualNP.CircuitLowerBounds

-- ===================== shared interface definitions =====================

-- The pairs of the hidden graph.
abbrev Pr (t : ℕ) := {p : Fin t × Fin t // p.1 < p.2}

-- +1 when the pin does not separate the pair, -1 when it does.
def chi {t : ℕ} (pin : Fin t → Bool) (e : Pr t) : ℤ :=
  if pin e.val.1 = pin e.val.2 then 1 else -1

-- Number of pairs of `G` separated by the pin.
def cutc {t : ℕ} (pin : Fin t → Bool) (G : Finset (Pr t)) : ℕ :=
  (G.filter (fun e => pin e.val.1 ≠ pin e.val.2)).card

-- The value of a fully pinned read with `m` pairs of which `c` are separated.
def val (t k m c : ℕ) : ℕ := 2 ^ ((t+1)*k - 2*m) * 5 ^ (m - c) * 3 ^ c

def tailF (t : ℕ) : Fin 3 × Fin t → Option (Fin t × Bool) :=
  fun e => if e.1 = 0 then some (e.2,false) else (none : Option (Fin t × Bool))

def headF (t : ℕ) : Fin 3 × Fin t → Option (Fin t × Bool) :=
  fun e => some (e.2,decide (e.1 ≠ 1))

def weightF (t : ℕ) : Option (Pr t) → Fin 3 × Fin t → Bool → ℕ :=
  fun (g : Option (Pr t)) (e : Fin 3 × Fin t) (diff : Bool) =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)

def obsF (t : ℕ) : Option (Pr t) → (Fin t → Fin 3) → ℕ :=
  fun (g : Option (Pr t)) (p : Fin t → Fin 3) =>
    ∑ x : Option (Fin t × Bool) → Bool,
      if (∀ i : Fin t, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tailF t e) ≠ x (headF t e))).card = 2*t then
      ∏ e : Fin 3 × Fin t, weightF t g e (xor (x (tailF t e)) (x (headF t e))) else 0

def readF (t k : ℕ) : Finset (Pr t) → (Fin t → Bool) → ℕ :=
  fun (G : Finset (Pr t)) (pin : Fin t → Bool) =>
    let p : Fin t → Fin 3 := fun i => if pin i then 2 else 1
    (obsF t none p)^(k-G.card) * ∏ e ∈ G, obsF t (some e) p

-- ===================== batch with the trimmed probe margin (copied from the checked L_lib_1069) =====================


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

private lemma batch_margin :
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

-- ===================== read algebra =====================

private def xr {t : ℕ} (pin : Fin t → Bool) (r : Bool) : Option (Fin t × Bool) → Bool :=
  fun v => v.elim r (fun q => cond q.2 (!(pin q.1)) (pin q.1))

private lemma xr_good {t : ℕ} (pin : Fin t → Bool) (r : Bool) (i : Fin t) :
    xr pin r (some (i, true)) = !(xr pin r (some (i, false))) := rfl

private lemma tailF_0 {t : ℕ} (i : Fin t) : tailF t ((0 : Fin 3), i) = some (i, false) := rfl
private lemma tailF_1 {t : ℕ} (i : Fin t) : tailF t ((1 : Fin 3), i) = none := rfl
private lemma tailF_2 {t : ℕ} (i : Fin t) : tailF t ((2 : Fin 3), i) = none := rfl
private lemma headF_0 {t : ℕ} (i : Fin t) : headF t ((0 : Fin 3), i) = some (i, true) := rfl
private lemma headF_1 {t : ℕ} (i : Fin t) : headF t ((1 : Fin 3), i) = some (i, false) := rfl
private lemma headF_2 {t : ℕ} (i : Fin t) : headF t ((2 : Fin 3), i) = some (i, true) := rfl

private lemma weight_0 {t : ℕ} (g : Option (Pr t)) (i : Fin t) (d : Bool) :
    weightF t g ((0 : Fin 3), i) d = d.toNat := by
  simp [weightF]

private lemma weight_2 {t : ℕ} (g : Option (Pr t)) (i : Fin t) (d : Bool) :
    weightF t g ((2 : Fin 3), i) d = 1 := by
  simp [weightF]

private lemma weight_none {t : ℕ} (i : Fin t) (d : Bool) :
    weightF t none ((1 : Fin 3), i) d = 2 := by
  simp [weightF]

private lemma weight_some {t : ℕ} (e : Pr t) (i : Fin t) (d : Bool) :
    weightF t (some e) ((1 : Fin 3), i) d =
      if e.val.1 = i ∨ e.val.2 = i then (if d then 1 else 3) else 2 := by
  simp [weightF]

private lemma pin_cond (a b : Bool)
    (h : (if a then 2 else 1 : Fin 3) = 0 ∨
      (if a then 2 else 1 : Fin 3) = (if b then 2 else 1)) : b = a := by
  revert h
  cases a <;> cases b <;> decide

private lemma prod_zero_of_bad {t : ℕ} (g : Option (Pr t)) (x : Option (Fin t × Bool) → Bool)
    (i0 : Fin t) (h : x (some (i0, false)) = x (some (i0, true))) :
    ∏ e : Fin 3 × Fin t, weightF t g e (xor (x (tailF t e)) (x (headF t e))) = 0 := by
  refine Finset.prod_eq_zero (Finset.mem_univ ((0 : Fin 3), i0)) ?_
  rw [tailF_0, headF_0, h, weight_0]
  simp

private lemma card_good {t : ℕ} (x : Option (Fin t × Bool) → Bool)
    (hx : ∀ i : Fin t, x (some (i, true)) = !(x (some (i, false)))) :
    (Finset.univ.filter (fun e : Fin 3 × Fin t => x (tailF t e) ≠ x (headF t e))).card = 2 * t := by
  rw [Finset.card_filter, Fintype.sum_prod_type_right]
  have heach : ∀ i : Fin t,
      (∑ k : Fin 3, if x (tailF t (k, i)) ≠ x (headF t (k, i)) then 1 else 0) = 2 := by
    intro i
    rw [Fin.sum_univ_three, tailF_0, tailF_1, tailF_2, headF_0, headF_1, headF_2, hx i]
    cases x none <;> cases x (some (i, false)) <;> decide
  rw [Finset.sum_congr rfl (fun i _ => heach i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_comm]

private lemma prod_good {t : ℕ} (g : Option (Pr t)) (x : Option (Fin t × Bool) → Bool)
    (hx : ∀ i : Fin t, x (some (i, true)) = !(x (some (i, false)))) :
    ∏ e : Fin 3 × Fin t, weightF t g e (xor (x (tailF t e)) (x (headF t e))) =
      ∏ i : Fin t, weightF t g ((1 : Fin 3), i) (xor (x none) (x (some (i, false)))) := by
  rw [Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Fin.prod_univ_three, tailF_0, tailF_1, tailF_2, headF_0, headF_1, headF_2, hx i,
    weight_0, weight_2]
  cases x (some (i, false)) <;> simp

private lemma obs_pinned {t : ℕ} (g : Option (Pr t)) (pin : Fin t → Bool) :
    obsF t g (fun i => if pin i then 2 else 1) =
      ∑ r : Bool, ∏ i : Fin t, weightF t g ((1 : Fin 3), i) (xor r (pin i)) := by
  unfold obsF
  refine (Fintype.sum_eq_add (xr pin true) (xr pin false) ?_ ?_).trans ?_
  · intro h
    have h2 : true = false := congrFun h none
    exact Bool.noConfusion h2
  · rintro x ⟨hx1, hx2⟩
    split_ifs with hc
    · by_contra hne
      have hpin : ∀ i : Fin t, x (some (i, false)) = pin i :=
        fun i => pin_cond (pin i) (x (some (i, false))) (hc.1 i)
      have hgood : ∀ i : Fin t, x (some (i, true)) = !(pin i) := by
        intro i
        by_contra hb
        apply hne
        apply prod_zero_of_bad g x i
        rw [hpin i]
        revert hb
        cases x (some (i, true)) <;> cases pin i <;> simp
      have hxeq : x = xr pin (x none) := by
        funext v
        rcases v with _ | ⟨i, b⟩
        · rfl
        · cases b
          · exact hpin i
          · exact hgood i
      cases hr : x none
      · rw [hr] at hxeq
        exact hx2 hxeq
      · rw [hr] at hxeq
        exact hx1 hxeq
    · rfl
  · rw [Fintype.sum_bool]
    congr 1
    · split_ifs with hc
      · exact prod_good g _ (xr_good pin true)
      · exact absurd ⟨fun i => Or.inr rfl, card_good _ (xr_good pin true)⟩ hc
    · split_ifs with hc
      · exact prod_good g _ (xr_good pin false)
      · exact absurd ⟨fun i => Or.inr rfl, card_good _ (xr_good pin false)⟩ hc

private lemma obs_none {t : ℕ} (pin : Fin t → Bool) :
    obsF t none (fun i => if pin i then 2 else 1) = 2 ^ (t + 1) := by
  rw [obs_pinned, Fintype.sum_bool]
  simp only [weight_none, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private lemma prod_two_special {t : ℕ} (a b : Fin t) (hab : a ≠ b) (f : Fin t → ℕ) :
    ∏ i : Fin t, (if a = i ∨ b = i then f i else 2) = 2 ^ (t - 2) * (f a * f b) := by
  have hb : b ∈ (Finset.univ : Finset (Fin t)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ _ hb]
  have hrest : ∏ i ∈ ((Finset.univ : Finset (Fin t)).erase a).erase b,
      (if a = i ∨ b = i then f i else 2) = 2 ^ (t - 2) := by
    have hc : ∀ i ∈ ((Finset.univ : Finset (Fin t)).erase a).erase b,
        (if a = i ∨ b = i then f i else 2) = 2 := by
      intro i hi
      have h1 : i ≠ b := (Finset.mem_erase.mp hi).1
      have h2 : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      have hne : ¬ (a = i ∨ b = i) := by
        rintro (h | h)
        · exact h2 h.symm
        · exact h1 h.symm
      simp only [hne, ↓reduceIte]
    have ht2 : t - 1 - 1 = t - 2 := by omega
    rw [Finset.prod_congr rfl hc, Finset.prod_const, Finset.card_erase_of_mem hb,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin, ht2]
  rw [hrest]
  simp only [true_or, or_true, ↓reduceIte]
  ring

private lemma obs_some {t : ℕ} (pin : Fin t → Bool) (e : Pr t) :
    obsF t (some e) (fun i => if pin i then 2 else 1) =
      2 ^ (t - 2) * (if pin e.val.1 = pin e.val.2 then 10 else 6) := by
  rw [obs_pinned, Fintype.sum_bool]
  simp only [weight_some]
  rw [prod_two_special e.val.1 e.val.2 (ne_of_lt e.property),
    prod_two_special e.val.1 e.val.2 (ne_of_lt e.property)]
  cases pin e.val.1 <;> cases pin e.val.2 <;> simp <;> ring

private lemma prod_cut {t : ℕ} (pin : Fin t → Bool) (G : Finset (Pr t)) :
    ∏ e ∈ G, (if pin e.val.1 = pin e.val.2 then 10 else 6 : ℕ) =
      10 ^ (G.card - cutc pin G) * 6 ^ (cutc pin G) := by
  have hsum := Finset.card_filter_add_card_filter_not (s := G)
    (fun e : Pr t => pin e.val.1 = pin e.val.2)
  have h1 : (G.filter (fun e : Pr t => ¬ pin e.val.1 = pin e.val.2)).card = cutc pin G := rfl
  have h2 : (G.filter (fun e : Pr t => pin e.val.1 = pin e.val.2)).card =
      G.card - cutc pin G := by
    rw [h1] at hsum
    omega
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, h1, h2]

private lemma arith (t k m c : ℕ) (ht : 2 ≤ t) (hc : c ≤ m) (hm : m ≤ k) :
    (2 ^ (t + 1)) ^ (k - m) * ((2 ^ (t - 2)) ^ m * (10 ^ (m - c) * 6 ^ c)) = val t k m c := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
  unfold val
  have h1 : 2 + s - 2 = s := by omega
  have h2 : c + d + j - (c + d) = j := by omega
  have h3 : c + d - c = d := by omega
  have h4 : (2 + s + 1) * (c + d + j) - 2 * (c + d) = (s + 3) * j + s * (c + d) + d + c :=
    Nat.sub_eq_of_eq_add (by ring)
  have e10 : (10 : ℕ) ^ d = 2 ^ d * 5 ^ d := by
    rw [← mul_pow]
    norm_num
  have e6 : (6 : ℕ) ^ c = 2 ^ c * 3 ^ c := by
    rw [← mul_pow]
    norm_num
  have p1 : ((2 : ℕ) ^ (2 + s + 1)) ^ j = 2 ^ ((s + 3) * j) := by
    rw [← pow_mul]
    congr 1
    ring
  have p2 : ((2 : ℕ) ^ s) ^ (c + d) = 2 ^ (s * (c + d)) := by
    rw [← pow_mul]
  rw [h1, h2, h3, h4, e10, e6, p1, p2, pow_add, pow_add, pow_add]
  generalize (2 : ℕ) ^ ((s + 3) * j) = X
  generalize (2 : ℕ) ^ (s * (c + d)) = Y
  ring

theorem readF_eq (t k : ℕ) (ht : 2 ≤ t) (G : Finset (Pr t)) (hG : G.card ≤ k)
    (pin : Fin t → Bool) : readF t k G pin = val t k G.card (cutc pin G) := by
  unfold readF
  dsimp only
  rw [obs_none, Finset.prod_congr rfl (fun e _ => obs_some pin e), Finset.prod_mul_distrib,
    Finset.prod_const, prod_cut]
  exact arith t k G.card (cutc pin G) ht (Finset.card_filter_le _ _) hG

theorem cutc_le {t : ℕ} (pin : Fin t → Bool) (G : Finset (Pr t)) : cutc pin G ≤ G.card := by
  unfold cutc
  exact Finset.card_filter_le _ _

theorem val_lt (t k m c : ℕ) (ht : 2 ≤ t) (hc : c ≤ m) (hm : m ≤ k) :
    val t k m c < 2 ^ (k*(t+2)+1) := by
  unfold val
  have h5 : (5 : ℕ) ^ (m - c) ≤ 8 ^ (m - c) := Nat.pow_le_pow_left (by norm_num) _
  have h3 : (3 : ℕ) ^ c ≤ 8 ^ c := Nat.pow_le_pow_left (by norm_num) _
  have h8 : (8 : ℕ) ^ (m - c) * 8 ^ c = 2 ^ (3 * m) := by
    rw [← pow_add, Nat.sub_add_cancel hc, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have hle : 2 ^ ((t+1)*k - 2*m) * 5 ^ (m - c) * 3 ^ c ≤
      2 ^ ((t+1)*k - 2*m) * (8 ^ (m - c) * 8 ^ c) := by
    rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h5 h3)
  rw [h8, ← pow_add] at hle
  refine lt_of_le_of_lt hle (Nat.pow_lt_pow_right (by norm_num) ?_)
  have e1 : (t + 1) * k = t * k + k := by ring
  have e2 : k * (t + 2) = t * k + 2 * k := by ring
  have e3 : 2 * k ≤ t * k := Nat.mul_le_mul_right k ht
  rw [e1, e2]
  omega

private lemma val_fact3 (A B C : ℕ) : (2 ^ A * 5 ^ B * 3 ^ C).factorization 3 = C := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization]
  simp

private lemma val_fact5 (A B C : ℕ) : (2 ^ A * 5 ^ B * 3 ^ C).factorization 5 = B := by
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow,
    Nat.prime_two.factorization, Nat.prime_three.factorization, Nat.prime_five.factorization]
  simp

theorem val_inj (t k m c m' c' : ℕ) (ht : 2 ≤ t) (hc : c ≤ m) (hm : m ≤ k)
    (hc' : c' ≤ m') (hm' : m' ≤ k) (h : val t k m c = val t k m' c') : m = m' ∧ c = c' := by
  have _hspare := And.intro ht (And.intro hm hm')
  unfold val at h
  have h3 := congrArg (fun n : ℕ => n.factorization 3) h
  have h5 := congrArg (fun n : ℕ => n.factorization 5) h
  simp only [val_fact3, val_fact5] at h3 h5
  omega

theorem sum_chi_eq {t : ℕ} (pin : Fin t → Bool) (G : Finset (Pr t)) :
    ∑ e ∈ G, chi pin e = (G.card : ℤ) - 2 * (cutc pin G : ℤ) := by
  have h : ∀ e ∈ G, chi pin e =
      1 - 2 * (if pin e.val.1 ≠ pin e.val.2 then (1 : ℤ) else 0) := by
    intro e _
    unfold chi
    by_cases hh : pin e.val.1 = pin e.val.2 <;> simp [hh]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.sum_boole]
  simp [cutc]

-- ===================== conditional gradient on the Huber fit =====================

-- Number of steps of the conditional gradient run.
def Sbig (k : ℕ) : ℕ := 2 ^ 42 * k ^ 4

-- How often pair `e` was selected during the first `s` steps.
def cntOf {t : ℕ} (sel : ℕ → Pr t) (s : ℕ) (e : Pr t) : ℕ :=
  ((Finset.range s).filter (fun j => sel j = e)).card

-- The residual of probe `i` after `s` steps, scaled by `s`.
def resid {t d : ℕ} (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (m : ℕ)
    (sel : ℕ → Pr t) (s : ℕ) (i : Fin d) : ℤ :=
  (s : ℤ) * q i - (m : ℤ) * ∑ e : Pr t, chi (batch i) e * (cntOf sel s e : ℤ)

-- The Huber slope (smoothing 1/512), scaled by `s`.
def clampZ (R : ℤ) (s : ℕ) : ℤ := max (-(s : ℤ)) (min (s : ℤ) (512 * R))

-- The score of pair `e` at step `s`; the step selects a pair of largest score.
def score {t d : ℕ} (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (m : ℕ)
    (sel : ℕ → Pr t) (s : ℕ) (e : Pr t) : ℤ :=
  ∑ i : Fin d, clampZ (resid batch q m sel s i) s * chi (batch i) e


-- ---------- helper A proofs ----------

-- Huber slope and Huber function (smoothing 1/512)
def fwSl (r : ℝ) : ℝ := max (-1) (min 1 (512 * r))

noncomputable def fwHub (r : ℝ) : ℝ := fwSl r * r - (fwSl r)^2 / 1024

theorem fwSl_bounds (r : ℝ) : -1 ≤ fwSl r ∧ fwSl r ≤ 1 := by
  unfold fwSl
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem fwSl_opt (r c : ℝ) (h1 : -1 ≤ c) (h2 : c ≤ 1) :
    (c - fwSl r) * (512 * r - fwSl r) ≤ 0 := by
  unfold fwSl
  rcases le_or_gt (512 * r) (-1) with h | h
  · rw [min_eq_right (by linarith), max_eq_left h]
    nlinarith
  · rcases le_or_gt (512 * r) 1 with h' | h'
    · rw [min_eq_right h', max_eq_right h.le]
      nlinarith
    · rw [min_eq_left h'.le, max_eq_right (by norm_num)]
      nlinarith

theorem fwHub_var (r c : ℝ) (h1 : -1 ≤ c) (h2 : c ≤ 1) :
    c * r - c^2 / 1024 ≤ fwHub r := by
  unfold fwHub
  nlinarith [fwSl_opt r c h1 h2, sq_nonneg (fwSl r - c)]

theorem fwHub_nonneg (r : ℝ) : 0 ≤ fwHub r := by
  have := fwHub_var r 0 (by norm_num) (by norm_num)
  linarith

theorem fwHub_ge_abs (r : ℝ) : |r| - 1/1024 ≤ fwHub r := by
  have h1 := fwHub_var r 1 (by norm_num) (by norm_num)
  have h2 := fwHub_var r (-1) (by norm_num) (by norm_num)
  rcases abs_cases r with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith

theorem fwHub_le_abs (r : ℝ) : fwHub r ≤ |r| := by
  obtain ⟨h1, h2⟩ := fwSl_bounds r
  unfold fwHub
  rcases abs_cases r with ⟨h, h0⟩ | ⟨h, h0⟩ <;> rw [h] <;> nlinarith [sq_nonneg (fwSl r)]

theorem fwHub_lower (a b : ℝ) : fwHub a + fwSl a * (b - a) ≤ fwHub b := by
  obtain ⟨h1, h2⟩ := fwSl_bounds a
  have h := fwHub_var b (fwSl a) h1 h2
  unfold fwHub at h ⊢
  linarith

theorem fwHub_upper (a b : ℝ) :
    fwHub b ≤ fwHub a + fwSl a * (b - a) + 256 * (b - a)^2 := by
  obtain ⟨h1, h2⟩ := fwSl_bounds b
  unfold fwHub
  nlinarith [fwSl_opt a (fwSl b) h1 h2, sq_nonneg (16 * (b - a) - (fwSl b - fwSl a) / 32)]

theorem fw_clamp_cast (R : ℤ) (s : ℕ) (hs : 0 < s) :
    ((clampZ R s : ℤ) : ℝ) = (s : ℝ) * fwSl ((R : ℝ) / (s : ℝ)) := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have e : (s : ℝ) * (512 * ((R : ℝ) / (s : ℝ))) = 512 * (R : ℝ) := by
    field_simp
  unfold clampZ fwSl
  push_cast
  rw [mul_max_of_nonneg _ _ hsR.le, mul_min_of_nonneg _ _ hsR.le, mul_neg, mul_one, e]

-- residuals and the smoothed fit, for a real matrix c
def fwR {d : ℕ} {E : Type} [Fintype E] (c : Fin d → E → ℝ) (q : Fin d → ℝ) (z : E → ℝ)
    (i : Fin d) : ℝ :=
  q i - ∑ e, c i e * z e

noncomputable def fwF {d : ℕ} {E : Type} [Fintype E] (c : Fin d → E → ℝ) (q : Fin d → ℝ) (z : E → ℝ) : ℝ :=
  ∑ i, fwHub (fwR c q z i)

theorem fw_sum_ind {E : Type} [Fintype E] [DecidableEq E] (G : Finset E) :
    ∑ e, (if e ∈ G then (1 : ℝ) else 0) = (G.card : ℝ) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem fw_sum_mul_ind {E : Type} [Fintype E] [DecidableEq E] (G : Finset E) (c : E → ℝ) :
    ∑ e, c e * (if e ∈ G then (1 : ℝ) else 0) = ∑ e ∈ G, c e := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem fw_abs_dot {E : Type} [Fintype E] (c z : E → ℝ) (M : ℝ)
    (hc : ∀ e, |c e| ≤ 1) (hz0 : ∀ e, 0 ≤ z e) (hzs : ∑ e, z e = M) :
    |∑ e, c e * z e| ≤ M := by
  calc |∑ e, c e * z e| ≤ ∑ e, |c e * z e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, z e := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul, abs_of_nonneg (hz0 e)]
        calc |c e| * z e ≤ 1 * z e := mul_le_mul_of_nonneg_right (hc e) (hz0 e)
          _ = z e := one_mul _
    _ = M := hzs

theorem fw_step {d : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (c : Fin d → E → ℝ) (hc : ∀ i e, |c i e| ≤ 1) (q : Fin d → ℝ)
    (z x z' : E → ℝ) (M γ : ℝ) (hγ : 0 ≤ γ) (e₀ : E)
    (hz0 : ∀ e, 0 ≤ z e) (hzs : ∑ e, z e = M)
    (hx0 : ∀ e, 0 ≤ x e) (hxs : ∑ e, x e = M)
    (hmax : ∀ e, ∑ i, fwSl (fwR c q z i) * c i e ≤ ∑ i, fwSl (fwR c q z i) * c i e₀)
    (hz' : ∀ e, z' e = z e + γ * (M * (if e = e₀ then 1 else 0) - z e)) :
    fwF c q z' - fwF c q x ≤
      (1 - γ) * (fwF c q z - fwF c q x) + 1024 * γ^2 * (d : ℝ) * M^2 := by
  have hM : 0 ≤ M := by
    rw [← hzs]
    exact Finset.sum_nonneg (fun e _ => hz0 e)
  obtain ⟨g, hg⟩ : ∃ g : Fin d → ℝ, ∀ i, g i = fwSl (fwR c q z i) := ⟨_, fun _ => rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin d → ℝ, ∀ i, δ i = M * c i e₀ - ∑ e, c i e * z e :=
    ⟨_, fun _ => rfl⟩
  simp only [← hg] at hmax
  have hr' : ∀ i, fwR c q z' i = fwR c q z i - γ * δ i := by
    intro i
    have h1 : ∀ e, c i e * z' e
        = c i e * z e + γ * M * (if e = e₀ then c i e else 0) - γ * (c i e * z e) := by
      intro e
      rw [hz' e]
      split_ifs <;> ring
    have h2 : ∑ e, c i e * z' e
        = ∑ e, c i e * z e + γ * M * c i e₀ - γ * ∑ e, c i e * z e := by
      simp only [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [fwR]
    rw [h2, hδ i]
    ring
  have hδb : ∀ i, (δ i)^2 ≤ 4 * M^2 := by
    intro i
    have h1 := fw_abs_dot (c i) z M (hc i) hz0 hzs
    have h2 : |M * c i e₀| ≤ M := by
      rw [abs_mul, abs_of_nonneg hM]
      calc M * |c i e₀| ≤ M * 1 := mul_le_mul_of_nonneg_left (hc i e₀) hM
        _ = M := mul_one _
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    have h3 : -(2 * M) ≤ δ i := by rw [hδ i]; linarith
    have h4 : δ i ≤ 2 * M := by rw [hδ i]; linarith
    nlinarith
  have hpt : ∀ i, fwHub (fwR c q z' i)
      ≤ fwHub (fwR c q z i) - γ * (g i * δ i) + 1024 * γ^2 * M^2 := by
    intro i
    have hb : fwR c q z' i - fwR c q z i = -(γ * δ i) := by rw [hr' i]; ring
    have h3 := fwHub_upper (fwR c q z i) (fwR c q z' i)
    rw [hb, ← hg i] at h3
    have h4 : γ^2 * (δ i)^2 ≤ γ^2 * (4 * M^2) :=
      mul_le_mul_of_nonneg_left (hδb i) (sq_nonneg γ)
    nlinarith
  have hsum : fwF c q z' ≤ fwF c q z - γ * ∑ i, g i * δ i + 1024 * γ^2 * (d : ℝ) * M^2 := by
    unfold fwF
    calc ∑ i, fwHub (fwR c q z' i)
        ≤ ∑ i, (fwHub (fwR c q z i) - γ * (g i * δ i) + 1024 * γ^2 * M^2) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = ∑ i, fwHub (fwR c q z i) - γ * ∑ i, g i * δ i + 1024 * γ^2 * (d : ℝ) * M^2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hW : ∑ i, g i * (∑ e, c i e * x e) ≤ M * ∑ i, g i * c i e₀ := by
    have h1 : ∑ i, g i * (∑ e, c i e * x e) = ∑ e, x e * ∑ i, g i * c i e := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h1, ← hxs, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_left (hmax e) (hx0 e)
  have hH2 : ∑ i, g i * (fwR c q x i - fwR c q z i) ≤ fwF c q x - fwF c q z := by
    unfold fwF
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    have := fwHub_lower (fwR c q z i) (fwR c q x i)
    rw [hg i]
    linarith
  have hid : ∑ i, g i * (fwR c q x i - fwR c q z i)
      = -(∑ i, g i * (∑ e, c i e * x e)) + ∑ i, g i * (∑ e, c i e * z e) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [fwR]
    ring
  have hid2 : ∑ i, g i * δ i
      = M * ∑ i, g i * c i e₀ - ∑ i, g i * (∑ e, c i e * z e) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hδ i]
    ring
  have h6 : -(∑ i, g i * δ i) ≤ fwF c q x - fwF c q z := by linarith
  have h7 := mul_le_mul_of_nonneg_left h6 hγ
  nlinarith

theorem fw_cone {E : Type} [Fintype E] [DecidableEq E] (G : Finset E) (k : ℕ) (hG : G.card ≤ k)
    (z x v : E → ℝ) (hz0 : ∀ e, 0 ≤ z e) (hzs : ∑ e, z e = (G.card : ℝ))
    (hx : ∀ e, x e = if e ∈ G then 1 else 0) (hv : ∀ e, v e = z e - x e) :
    ∑ e, |v e| ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e, (v e)^2) := by
  have hsv : ∑ e, v e = 0 := by
    simp only [hv, hx, Finset.sum_sub_distrib, hzs, fw_sum_ind, sub_self]
  have hle : ∀ e, |v e| - v e ≤ 2 * (if e ∈ G then |v e| else 0) := by
    intro e
    by_cases he : e ∈ G
    · simp only [he, ↓reduceIte]
      have := neg_abs_le (v e)
      linarith
    · simp only [he, ↓reduceIte]
      have h0 : 0 ≤ v e := by
        rw [hv e, hx e]
        simp only [he, ↓reduceIte]
        have := hz0 e
        linarith
      rw [abs_of_nonneg h0]
      linarith
  have h1 : ∑ e, |v e| ≤ 2 * ∑ e ∈ G, |v e| := by
    have h := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hle e)
    rw [Finset.sum_sub_distrib, hsv, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter] at h
    linarith
  have h2 : (∑ e ∈ G, |v e|)^2 ≤ (k : ℝ) * ∑ e, (v e)^2 := by
    have hcs := sq_sum_le_card_mul_sum_sq (s := G) (f := fun e => |v e|)
    have h3 : ∑ e ∈ G, |v e|^2 ≤ ∑ e, (v e)^2 := by
      simp only [sq_abs]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
        (fun e _ _ => sq_nonneg _)
    have hk : (G.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hG
    have h5 : 0 ≤ ∑ e ∈ G, |v e|^2 := Finset.sum_nonneg (fun e _ => sq_nonneg _)
    calc (∑ e ∈ G, |v e|)^2 ≤ (G.card : ℝ) * ∑ e ∈ G, |v e|^2 := hcs
      _ ≤ (k : ℝ) * ∑ e, (v e)^2 := mul_le_mul hk h3 h5 (Nat.cast_nonneg k)
  have h6 : ∑ e ∈ G, |v e| ≤ Real.sqrt (k : ℝ) * Real.sqrt (∑ e, (v e)^2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg k)]
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h2)
  linarith

theorem fw_sharp {d : ℕ} {E : Type} [Fintype E] [DecidableEq E]
    (c : Fin d → E → ℝ) (q : Fin d → ℝ) (k : ℕ) (S : Finset (Fin d))
    (hmargin : ∀ (v : E → ℝ),
      (∑ e, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e, (v e)^2) →
      (d : ℝ) * Real.sqrt (∑ e, (v e)^2) + 256 * (∑ i ∈ S, |∑ e, v e * c i e|) ≤
        128 * (∑ i, |∑ e, v e * c i e|))
    (G : Finset E) (hG : G.card ≤ k)
    (hgood : ∀ i, i ∉ S → q i = ∑ e ∈ G, c i e)
    (z x v : E → ℝ) (hz0 : ∀ e, 0 ≤ z e) (hzs : ∑ e, z e = (G.card : ℝ))
    (hx : ∀ e, x e = if e ∈ G then 1 else 0) (hv : ∀ e, v e = z e - x e) :
    (d : ℝ) * Real.sqrt (∑ e, (v e)^2)
      ≤ 128 * (∑ i, |fwR c q z i| - ∑ i, |fwR c q x i|) := by
  have hcone := fw_cone G k hG z x v hz0 hzs hx hv
  have hm := hmargin v hcone
  have hrx : ∀ i, fwR c q x i = q i - ∑ e ∈ G, c i e := by
    intro i
    simp only [fwR, hx]
    rw [fw_sum_mul_ind]
  have hrz : ∀ i, fwR c q z i = fwR c q x i - ∑ e, v e * c i e := by
    intro i
    have h : ∑ e, v e * c i e = ∑ e, c i e * z e - ∑ e, c i e * x e := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro e _
      rw [hv e]
      ring
    simp only [fwR]
    rw [h]
    ring
  have hpt : ∀ i, |∑ e, v e * c i e| - 2 * (if i ∈ S then |∑ e, v e * c i e| else 0)
      ≤ |fwR c q z i| - |fwR c q x i| := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      rw [hrz i]
      have := abs_sub_abs_le_abs_sub (fwR c q x i) (∑ e, v e * c i e)
      linarith
    · simp only [hi, ↓reduceIte]
      rw [hrz i, hrx i, hgood i hi]
      simp
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem,
    Finset.univ_inter] at hs
  linarith

theorem fw_close {d : ℕ} {E : Type} [Fintype E] [DecidableEq E] (hd : 0 < d)
    (c : Fin d → E → ℝ) (q : Fin d → ℝ) (k : ℕ) (S : Finset (Fin d))
    (hmargin : ∀ (v : E → ℝ),
      (∑ e, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e, (v e)^2) →
      (d : ℝ) * Real.sqrt (∑ e, (v e)^2) + 256 * (∑ i ∈ S, |∑ e, v e * c i e|) ≤
        128 * (∑ i, |∑ e, v e * c i e|))
    (G : Finset E) (hG : G.card ≤ k)
    (hgood : ∀ i, i ∉ S → q i = ∑ e ∈ G, c i e)
    (z x : E → ℝ) (hz0 : ∀ e, 0 ≤ z e) (hzs : ∑ e, z e = (G.card : ℝ))
    (hx : ∀ e, x e = if e ∈ G then 1 else 0)
    (hH : fwF c q z - fwF c q x < 3 * (d : ℝ) / 1024) :
    ∀ e, |z e - x e| < 1 / 2 := by
  obtain ⟨v, hv⟩ : ∃ v : E → ℝ, ∀ e, v e = z e - x e := ⟨fun e => z e - x e, fun _ => rfl⟩
  have hs := fw_sharp c q k S hmargin G hG hgood z x v hz0 hzs hx hv
  have h1 : ∑ i, |fwR c q z i| - (d : ℝ) / 1024 ≤ fwF c q z := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      fwHub_ge_abs (fwR c q z i))
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at h
    unfold fwF
    linarith
  have h2 : fwF c q x ≤ ∑ i, |fwR c q x i| :=
    Finset.sum_le_sum (fun i _ => fwHub_le_abs _)
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hQ : Real.sqrt (∑ e, (v e)^2) < 1 / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have := mul_le_mul_of_nonneg_left hcon hD.le
    linarith
  intro e
  rw [← hv e]
  have h3 : (v e)^2 ≤ ∑ e, (v e)^2 :=
    Finset.single_le_sum (f := fun e => (v e)^2) (fun e _ => sq_nonneg _) (Finset.mem_univ e)
  have := Real.abs_le_sqrt h3
  linarith

-- ---------- the concrete run ----------

def fwC {t d : ℕ} (batch : Fin d → Fin t → Bool) (i : Fin d) (e : Pr t) : ℝ :=
  ((chi (batch i) e : ℤ) : ℝ)

def fwQ {d : ℕ} (q : Fin d → ℤ) (i : Fin d) : ℝ := ((q i : ℤ) : ℝ)

noncomputable def fwZ {t : ℕ} (m : ℕ) (sel : ℕ → Pr t) (s : ℕ) (e : Pr t) : ℝ :=
  (m : ℝ) * (cntOf sel s e : ℝ) / (s : ℝ)

def fwX {t : ℕ} (G : Finset (Pr t)) (e : Pr t) : ℝ := if e ∈ G then 1 else 0

noncomputable def fwH {t d : ℕ} (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (G : Finset (Pr t))
    (sel : ℕ → Pr t) (s : ℕ) : ℝ :=
  fwF (fwC batch) (fwQ q) (fwZ G.card sel s) - fwF (fwC batch) (fwQ q) (fwX G)

theorem fw_chi_abs {t d : ℕ} (batch : Fin d → Fin t → Bool) :
    ∀ i e, |fwC batch i e| ≤ 1 := by
  intro i e
  unfold fwC chi
  split_ifs <;> simp

theorem fw_chi_prod {t : ℕ} (pin : Fin t → Bool) (e : Pr t) :
    (if pin e.val.1 then (1 : ℝ) else -1) * (if pin e.val.2 then (1 : ℝ) else -1)
      = ((chi pin e : ℤ) : ℝ) := by
  unfold chi
  cases h1 : pin e.val.1 <;> cases h2 : pin e.val.2 <;> simp

theorem fw_cnt_succ {t : ℕ} (sel : ℕ → Pr t) (s : ℕ) (e : Pr t) :
    cntOf sel (s + 1) e = cntOf sel s e + (if sel s = e then 1 else 0) := by
  unfold cntOf
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

theorem fw_cnt_sum {t : ℕ} (sel : ℕ → Pr t) (s : ℕ) : ∑ e, cntOf sel s e = s := by
  induction s with
  | zero => simp [cntOf]
  | succ s ih =>
    simp only [fw_cnt_succ, Finset.sum_add_distrib, ih, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte]

theorem fw_Z_nonneg {t : ℕ} (m : ℕ) (sel : ℕ → Pr t) (s : ℕ) (e : Pr t) :
    0 ≤ fwZ m sel s e := by
  unfold fwZ
  positivity

theorem fw_Z_sum {t : ℕ} (m : ℕ) (sel : ℕ → Pr t) (s : ℕ) (hs : 1 ≤ s) :
    ∑ e, fwZ m sel s e = (m : ℝ) := by
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [fwZ]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum, fw_cnt_sum, mul_div_assoc,
    div_self hsR, mul_one]

theorem fw_Z_succ {t : ℕ} (m : ℕ) (sel : ℕ → Pr t) (s : ℕ) (hs : 1 ≤ s) (e : Pr t) :
    fwZ m sel (s + 1) e = fwZ m sel s e +
      (1 / ((s : ℝ) + 1)) * ((m : ℝ) * (if e = sel s then 1 else 0) - fwZ m sel s e) := by
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs1 : (s : ℝ) + 1 ≠ 0 := by positivity
  simp only [fwZ, fw_cnt_succ]
  by_cases h : sel s = e
  · simp only [h, eq_self, ↓reduceIte]
    push_cast
    field_simp
    ring
  · have h' : ¬ e = sel s := fun h' => h h'.symm
    simp only [h, h', ↓reduceIte]
    push_cast
    field_simp
    ring

theorem fw_X_sum {t : ℕ} (G : Finset (Pr t)) : ∑ e, fwX G e = (G.card : ℝ) := by
  simp only [fwX]
  exact fw_sum_ind G

theorem fw_X_nonneg {t : ℕ} (G : Finset (Pr t)) (e : Pr t) : 0 ≤ fwX G e := by
  unfold fwX
  split_ifs <;> norm_num

theorem fw_resid_cast {t d : ℕ} (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (m : ℕ)
    (sel : ℕ → Pr t) (s : ℕ) (hs : 1 ≤ s) (i : Fin d) :
    ((resid batch q m sel s i : ℤ) : ℝ)
      = (s : ℝ) * fwR (fwC batch) (fwQ q) (fwZ m sel s) i := by
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : ∑ e, fwC batch i e * fwZ m sel s e
      = (m : ℝ) * (∑ e, fwC batch i e * (cntOf sel s e : ℝ)) / (s : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e _
    simp only [fwZ]
    ring
  have e1 : ((resid batch q m sel s i : ℤ) : ℝ)
      = (s : ℝ) * (q i : ℝ) - (m : ℝ) * ∑ e, fwC batch i e * (cntOf sel s e : ℝ) := by
    simp only [resid, fwC]
    push_cast
    rfl
  rw [e1]
  simp only [fwR, fwQ]
  rw [h]
  field_simp

theorem fw_score_cast {t d : ℕ} (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (m : ℕ)
    (sel : ℕ → Pr t) (s : ℕ) (hs : 1 ≤ s) (e : Pr t) :
    ((score batch q m sel s e : ℤ) : ℝ)
      = (s : ℝ) * ∑ i, fwSl (fwR (fwC batch) (fwQ q) (fwZ m sel s) i) * fwC batch i e := by
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold score
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fw_clamp_cast _ _ hs, fw_resid_cast batch q m sel s hs i, mul_div_cancel_left₀ _ hsR,
    mul_assoc]
  rfl

theorem fw_H_step {t k d : ℕ} (batch : Fin d → Fin t → Bool) (G : Finset (Pr t))
    (q : Fin d → ℤ) (sel : ℕ → Pr t)
    (hsel : ∀ s, s < Sbig k → ∀ e,
      score batch q G.card sel s e ≤ score batch q G.card sel s (sel s))
    (s : ℕ) (hs1 : 1 ≤ s) (hs : s < Sbig k) :
    ((s : ℝ) + 1) * fwH batch q G sel (s + 1)
      ≤ (s : ℝ) * fwH batch q G sel s
        + 1024 * (d : ℝ) * (G.card : ℝ)^2 * (1 / ((s : ℝ) + 1)) := by
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs1
  have hp : (0 : ℝ) < (s : ℝ) + 1 := by linarith
  have hmax : ∀ e, ∑ i, fwSl (fwR (fwC batch) (fwQ q) (fwZ G.card sel s) i) * fwC batch i e
      ≤ ∑ i, fwSl (fwR (fwC batch) (fwQ q) (fwZ G.card sel s) i) * fwC batch i (sel s) := by
    intro e
    have h := hsel s hs e
    have h2 : ((score batch q G.card sel s e : ℤ) : ℝ)
        ≤ ((score batch q G.card sel s (sel s) : ℤ) : ℝ) := by exact_mod_cast h
    rw [fw_score_cast batch q G.card sel s hs1, fw_score_cast batch q G.card sel s hs1] at h2
    exact le_of_mul_le_mul_left h2 hsR
  have hstep := fw_step (fwC batch) (fw_chi_abs batch) (fwQ q) (fwZ G.card sel s) (fwX G)
    (fwZ G.card sel (s + 1)) (G.card : ℝ) (1 / ((s : ℝ) + 1)) (by positivity) (sel s)
    (fw_Z_nonneg G.card sel s) (fw_Z_sum G.card sel s hs1) (fw_X_nonneg G) (fw_X_sum G) hmax
    (fw_Z_succ G.card sel s hs1)
  have hmul := mul_le_mul_of_nonneg_left hstep hp.le
  unfold fwH
  have e1 : ((s : ℝ) + 1) * (1 - 1 / ((s : ℝ) + 1)) = (s : ℝ) := by
    field_simp
    ring
  have e2 : ((s : ℝ) + 1) * (1 / ((s : ℝ) + 1))^2 = 1 / ((s : ℝ) + 1) := by
    field_simp
  have e3 : ((s : ℝ) + 1) * ((1 - 1 / ((s : ℝ) + 1)) *
        (fwF (fwC batch) (fwQ q) (fwZ G.card sel s) - fwF (fwC batch) (fwQ q) (fwX G)) +
        1024 * (1 / ((s : ℝ) + 1))^2 * (d : ℝ) * (G.card : ℝ)^2)
      = (s : ℝ) * (fwF (fwC batch) (fwQ q) (fwZ G.card sel s) - fwF (fwC batch) (fwQ q) (fwX G))
        + 1024 * (d : ℝ) * (G.card : ℝ)^2 * (1 / ((s : ℝ) + 1)) := by
    rw [mul_add, ← mul_assoc, e1]
    have : ((s : ℝ) + 1) * (1024 * (1 / ((s : ℝ) + 1))^2 * (d : ℝ) * (G.card : ℝ)^2)
        = 1024 * (d : ℝ) * (G.card : ℝ)^2 * (((s : ℝ) + 1) * (1 / ((s : ℝ) + 1))^2) := by ring
    rw [this, e2]
  rw [e3] at hmul
  exact hmul

theorem fw_log_step (n : ℕ) (hn : 1 ≤ n) :
    1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hn0 hn1)
  rw [Real.log_div hn0.ne' hn1.ne'] at h
  have e : (n : ℝ) / ((n : ℝ) + 1) = 1 - 1 / ((n : ℝ) + 1) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self hn1.ne']
  rw [e] at h
  linarith

theorem fw_H_one {t k d : ℕ} (batch : Fin d → Fin t → Bool) (G : Finset (Pr t))
    (hG : G.card ≤ k) (q : Fin d → ℤ) (hq : ∀ i, |q i| ≤ (k : ℤ)) (sel : ℕ → Pr t) :
    fwH batch q G sel 1 ≤ 2 * (d : ℝ) * (k : ℝ) := by
  unfold fwH
  have h0 : 0 ≤ fwF (fwC batch) (fwQ q) (fwX G) :=
    Finset.sum_nonneg (fun i _ => fwHub_nonneg _)
  have hk : (G.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hG
  have h1 : fwF (fwC batch) (fwQ q) (fwZ G.card sel 1) ≤ ∑ i : Fin d, (2 * (k : ℝ)) := by
    apply Finset.sum_le_sum
    intro i _
    have ha := fwHub_le_abs (fwR (fwC batch) (fwQ q) (fwZ G.card sel 1) i)
    have hb := fw_abs_dot (fwC batch i) (fwZ G.card sel 1) (G.card : ℝ) (fw_chi_abs batch i)
      (fw_Z_nonneg G.card sel 1) (fw_Z_sum G.card sel 1 le_rfl)
    have hc : |fwQ q i| ≤ (k : ℝ) := by
      unfold fwQ
      exact_mod_cast hq i
    have hd : |fwR (fwC batch) (fwQ q) (fwZ G.card sel 1) i|
        ≤ |fwQ q i| + |∑ e, fwC batch i e * fwZ G.card sel 1 e| := by
      unfold fwR
      exact abs_sub _ _
    linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  linarith

theorem fw_H_bound {t k d : ℕ} (batch : Fin d → Fin t → Bool) (G : Finset (Pr t))
    (hG : G.card ≤ k) (q : Fin d → ℤ) (hq : ∀ i, |q i| ≤ (k : ℤ)) (sel : ℕ → Pr t)
    (hsel : ∀ s, s < Sbig k → ∀ e,
      score batch q G.card sel s e ≤ score batch q G.card sel s (sel s)) :
    ∀ n : ℕ, n + 1 ≤ Sbig k →
      ((n : ℝ) + 1) * fwH batch q G sel (n + 1)
        ≤ 2 * (d : ℝ) * (k : ℝ)
          + 1024 * (d : ℝ) * (G.card : ℝ)^2 * Real.log ((n : ℝ) + 1) := by
  intro n
  induction n with
  | zero =>
    intro _
    have h := fw_H_one batch G hG q hq sel
    simp only [Nat.cast_zero, zero_add, one_mul, Real.log_one, mul_zero, add_zero]
    exact h
  | succ n ih =>
    intro hle
    have ih' := ih (by omega)
    have hstep := fw_H_step batch G q sel hsel (n + 1) (by omega) (by omega)
    have hlog := fw_log_step (n + 1) (by omega)
    have hC : 0 ≤ 1024 * (d : ℝ) * (G.card : ℝ)^2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hlog hC
    push_cast at hstep hmul ⊢
    linarith

theorem fw_numeric (k d m : ℕ) (hk : 0 < k) (hd : 0 < d) (hm : m ≤ k) (H : ℝ)
    (hb : ((Sbig k : ℕ) : ℝ) * H
      ≤ 2 * (d : ℝ) * (k : ℝ) + 1024 * (d : ℝ) * (m : ℝ)^2 * Real.log ((Sbig k : ℕ) : ℝ)) :
    H < 3 * (d : ℝ) / 1024 := by
  have hK : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hD : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hM : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 2097152 * (k : ℝ)^2 := ⟨_, rfl⟩
  have hY1 : 1 ≤ Y := by rw [hY]; nlinarith
  have hY0 : 0 < Y := by linarith
  have hS : ((Sbig k : ℕ) : ℝ) = Y^2 := by
    rw [hY]
    unfold Sbig
    push_cast
    ring
  rw [hS] at hb
  have hlog : Real.log (Y^2) ≤ 2 * Y := by
    have h := Real.log_le_sub_one_of_pos hY0
    rw [Real.log_pow]
    push_cast
    linarith
  have hlog0 : 0 ≤ Real.log (Y^2) := Real.log_nonneg (by nlinarith)
  have hM2 : (m : ℝ)^2 ≤ (k : ℝ)^2 := by nlinarith
  have hk2 : (0 : ℝ) ≤ (k : ℝ)^2 := sq_nonneg _
  have h1 : (m : ℝ)^2 * Real.log (Y^2) ≤ (k : ℝ)^2 * (2 * Y) :=
    mul_le_mul hM2 hlog hlog0 hk2
  have h2 : (k : ℝ) ≤ (k : ℝ)^2 * Y := by nlinarith
  have h1' := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1024 * (d : ℝ))
  have h2' := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * (d : ℝ))
  have h3 : Y^2 * H ≤ 2050 * ((d : ℝ) * ((k : ℝ)^2 * Y)) := by linarith
  have h4 : Y^2 * (3 * (d : ℝ) / 1024) = 6144 * ((d : ℝ) * ((k : ℝ)^2 * Y)) := by
    rw [hY]
    ring
  have h5 : 0 < (d : ℝ) * ((k : ℝ)^2 * Y) :=
    mul_pos hD (mul_pos (by nlinarith) hY0)
  have h6 : Y^2 * H < Y^2 * (3 * (d : ℝ) / 1024) := by
    rw [h4]
    linarith
  exact lt_of_mul_lt_mul_left h6 (sq_nonneg Y)

theorem fw_decodes {t k d : ℕ} (hk : 0 < k) (hd : 0 < d) (batch : Fin d → Fin t → Bool)
    (hmargin : ∀ (v : Pr t → ℝ) (S : Finset (Fin d)),
      (∑ e : Pr t, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) →
      400 * S.card ≤ d →
      (d : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) +
        256 * (∑ i ∈ S, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|) ≤
        128 * (∑ i, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|))
    (G : Finset (Pr t)) (hG : G.card ≤ k)
    (q : Fin d → ℤ) (hq : ∀ i, |q i| ≤ (k : ℤ))
    (S : Finset (Fin d)) (hS : 400 * S.card ≤ d)
    (hgood : ∀ i, i ∉ S → q i = ∑ e ∈ G, chi (batch i) e)
    (sel : ℕ → Pr t)
    (hsel : ∀ s, s < Sbig k → ∀ e, score batch q G.card sel s e ≤ score batch q G.card sel s (sel s)) :
    ∀ e, (Sbig k ≤ 2 * G.card * cntOf sel (Sbig k) e ↔ e ∈ G) := by
  have hSpos : 0 < Sbig k := by
    unfold Sbig
    positivity
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Sbig k = n + 1 := ⟨Sbig k - 1, by omega⟩
  have hb := fw_H_bound batch G hG q hq sel hsel n (by omega)
  have hcastS : ((Sbig k : ℕ) : ℝ) = (n : ℝ) + 1 := by
    rw [hn]
    push_cast
    ring
  rw [← hn, ← hcastS] at hb
  have hH : fwH batch q G sel (Sbig k) < 3 * (d : ℝ) / 1024 :=
    fw_numeric k d G.card hk hd hG _ hb
  have hm' : ∀ (v : Pr t → ℝ),
      (∑ e, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e, (v e)^2) →
      (d : ℝ) * Real.sqrt (∑ e, (v e)^2) + 256 * (∑ i ∈ S, |∑ e, v e * fwC batch i e|) ≤
        128 * (∑ i, |∑ e, v e * fwC batch i e|) := by
    intro v hv
    have h := hmargin v S hv hS
    have e1 : ∀ (i : Fin d) (e : Pr t),
        v e * (if batch i e.val.1 then (1 : ℝ) else -1) * (if batch i e.val.2 then (1 : ℝ) else -1)
          = v e * fwC batch i e := by
      intro i e
      rw [mul_assoc, fw_chi_prod]
      rfl
    simp only [e1] at h
    exact h
  have hgood' : ∀ i, i ∉ S → fwQ q i = ∑ e ∈ G, fwC batch i e := by
    intro i hi
    unfold fwQ fwC
    rw [hgood i hi, Int.cast_sum]
  have hclose := fw_close hd (fwC batch) (fwQ q) k S hm' G hG hgood'
    (fwZ G.card sel (Sbig k)) (fwX G) (fw_Z_nonneg G.card sel (Sbig k))
    (fw_Z_sum G.card sel (Sbig k) hSpos) (fun _ => rfl) hH
  intro e
  have hSR : (0 : ℝ) < ((Sbig k : ℕ) : ℝ) := by exact_mod_cast hSpos
  have h := hclose e
  simp only [fwZ, fwX] at h
  by_cases he : e ∈ G
  · simp only [he, ↓reduceIte] at h
    have h1 := (abs_lt.mp h).1
    have h2 : (1 : ℝ) / 2
        < (G.card : ℝ) * (cntOf sel (Sbig k) e : ℝ) / ((Sbig k : ℕ) : ℝ) := by linarith
    rw [lt_div_iff₀ hSR] at h2
    have h3 : ((Sbig k : ℕ) : ℝ) < ((2 * G.card * cntOf sel (Sbig k) e : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : Sbig k < 2 * G.card * cntOf sel (Sbig k) e := by exact_mod_cast h3
    exact iff_of_true h4.le he
  · simp only [he, ↓reduceIte] at h
    have h1 := (abs_lt.mp h).2
    have h2 : (G.card : ℝ) * (cntOf sel (Sbig k) e : ℝ) / ((Sbig k : ℕ) : ℝ)
        < 1 / 2 := by linarith
    rw [div_lt_iff₀ hSR] at h2
    have h3 : ((2 * G.card * cntOf sel (Sbig k) e : ℕ) : ℝ) < ((Sbig k : ℕ) : ℝ) := by
      push_cast
      linarith
    have h4 : 2 * G.card * cntOf sel (Sbig k) e < Sbig k := by exact_mod_cast h3
    exact iff_of_false (not_le.mpr h4) he


-- ===================== circuit framework =====================

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl stepW x

theorem wires_eq_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (stepW x g) := rfl

theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run_cons, ih]
    simp [stepW]
    omega

theorem run_append (gs hs : List Gate) (x : List Bool) :
    run (gs ++ hs) x = run hs (run gs x) := by
  simp [run, List.foldl_append]

theorem run_prefix (hs : List Gate) (w : List Bool) : w <+: run hs w := by
  induction hs generalizing w with
  | nil => exact List.prefix_refl _
  | cons g hs ih =>
    rw [run_cons]
    exact (List.prefix_append w _).trans (ih (stepW w g))

def vl (x : List Bool) (gs : List Gate) (i : ℕ) : Bool := (run gs x).getD i false

theorem vl_mono {x : List Bool} {gs gs' : List Gate} (h : gs <+: gs') {i : ℕ}
    (hi : i < x.length + gs.length) : vl x gs' i = vl x gs i := by
  obtain ⟨e, rfl⟩ := h
  unfold vl
  rw [run_append]
  obtain ⟨l, hl⟩ := run_prefix e (run gs x)
  rw [← hl]
  have hlen : i < (run gs x).length := by rw [run_length]; exact hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]

theorem vl_new (x : List Bool) (gs : List Gate) (g : Gate) :
    vl x (gs ++ [g]) (x.length + gs.length) = g.op.eval (g.inputs.map (vl x gs)) := by
  unfold vl
  rw [run_append]
  have h1 : run [g] (run gs x) = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := rfl
  rw [h1]
  have hlen : (run gs x).length = x.length + gs.length := run_length gs x
  simp [List.getD_eq_getElem?_getD, ← hlen]

theorem vl_new' {n : ℕ} {x : List Bool} (hx : x.length = n) (gs : List Gate) (g : Gate) :
    vl x (gs ++ [g]) (n + gs.length) = g.op.eval (g.inputs.map (vl x gs)) := by
  subst hx
  exact vl_new x gs g

theorem vl_input (x : List Bool) (gs : List Gate) {i : ℕ} (hi : i < x.length) :
    vl x gs i = x.getD i false := by
  have h := vl_mono (x := x) (gs := []) (gs' := gs) (List.nil_prefix) (i := i) (by simpa using hi)
  rw [h]
  rfl

-- gate shape and reads-back, per gate
def GateOK (n j : ℕ) (g : Gate) : Prop :=
  (((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧ ∀ i ∈ g.inputs, i < n + j

def WF (n : ℕ) (gs : List Gate) : Prop := ∀ j (h : j < gs.length), GateOK n j gs[j]

theorem WF_snoc {n : ℕ} {gs : List Gate} (h : WF n gs) {g : Gate} (hg : GateOK n gs.length g) :
    WF n (gs ++ [g]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]
    exact h j hlt
  · have hj' : j = gs.length := by
      simp at hj
      omega
    subst hj'
    simpa using hg

-- builder state: gates so far, well formed, over n > 0 inputs
structure St (n : ℕ) where
  gs : List Gate
  wf : WF n gs
  npos : 0 < n

def St.le {n : ℕ} (s s' : St n) : Prop := s.gs <+: s'.gs

theorem St.le_refl {n : ℕ} (s : St n) : s.le s := List.prefix_refl _

theorem St.le_trans {n : ℕ} {a b c : St n} (h1 : a.le b) (h2 : b.le c) : a.le c :=
  List.IsPrefix.trans h1 h2

theorem St.le_len {n : ℕ} {a b : St n} (h : a.le b) : a.gs.length ≤ b.gs.length :=
  List.IsPrefix.length_le h

def cl (n : ℕ) (gs : List Gate) (i : ℕ) : ℕ := min i (n + gs.length - 1)

theorem cl_lt {n : ℕ} (hn : 0 < n) (gs : List Gate) (i : ℕ) : cl n gs i < n + gs.length := by
  unfold cl
  omega

theorem cl_eq {n : ℕ} {gs : List Gate} {i : ℕ} (h : i < n + gs.length) : cl n gs i = i := by
  unfold cl
  omega

def gNot {n : ℕ} (s : St n) (a : ℕ) : ℕ × St n :=
  (n + s.gs.length,
    ⟨s.gs ++ [⟨GateOp.not, [cl n s.gs a]⟩],
      WF_snoc s.wf ⟨Or.inr ⟨rfl, rfl⟩, by
        intro i hi
        simp at hi
        subst hi
        exact cl_lt s.npos _ _⟩, s.npos⟩)

def gAnd {n : ℕ} (s : St n) (a b : ℕ) : ℕ × St n :=
  (n + s.gs.length,
    ⟨s.gs ++ [⟨GateOp.and, [cl n s.gs a, cl n s.gs b]⟩],
      WF_snoc s.wf ⟨Or.inl ⟨Or.inl rfl, rfl⟩, by
        intro i hi
        simp at hi
        rcases hi with hi | hi <;> subst hi <;> exact cl_lt s.npos _ _⟩, s.npos⟩)

def gOr {n : ℕ} (s : St n) (a b : ℕ) : ℕ × St n :=
  (n + s.gs.length,
    ⟨s.gs ++ [⟨GateOp.or, [cl n s.gs a, cl n s.gs b]⟩],
      WF_snoc s.wf ⟨Or.inl ⟨Or.inr rfl, rfl⟩, by
        intro i hi
        simp at hi
        rcases hi with hi | hi <;> subst hi <;> exact cl_lt s.npos _ _⟩, s.npos⟩)

-- wire i exists in state s and carries value v on input x
def Has {n : ℕ} (x : List Bool) (s : St n) (i : ℕ) (v : Bool) : Prop :=
  i < n + s.gs.length ∧ vl x s.gs i = v

structure Base (n : ℕ) (x : List Bool) : Prop where
  len : x.length = n
  two : 2 ≤ n
  h0 : x.getD 0 false = false
  h1 : x.getD 1 false = true

theorem Has.mono {n : ℕ} {x : List Bool} (hb : Base n x) {s s' : St n} {i : ℕ} {v : Bool}
    (h : Has x s i v) (hle : s.le s') : Has x s' i v := by
  refine ⟨lt_of_lt_of_le h.1 (Nat.add_le_add_left (St.le_len hle) n), ?_⟩
  rw [vl_mono hle (by rw [hb.len]; exact h.1)]
  exact h.2

theorem has_self {n : ℕ} {x : List Bool} {s : St n} {i : ℕ} (h : i < n + s.gs.length) :
    Has x s i (vl x s.gs i) := ⟨h, rfl⟩

theorem has_false {n : ℕ} {x : List Bool} (hb : Base n x) (s : St n) : Has x s 0 false := by
  refine ⟨by have := hb.two; omega, ?_⟩
  rw [vl_input x s.gs (by rw [hb.len]; have := hb.two; omega)]
  exact hb.h0

theorem has_true {n : ℕ} {x : List Bool} (hb : Base n x) (s : St n) : Has x s 1 true := by
  refine ⟨by have := hb.two; omega, ?_⟩
  rw [vl_input x s.gs (by rw [hb.len]; have := hb.two; omega)]
  exact hb.h1

theorem gNot_le {n : ℕ} (s : St n) (a : ℕ) : s.le (gNot s a).2 := List.prefix_append _ _
theorem gAnd_le {n : ℕ} (s : St n) (a b : ℕ) : s.le (gAnd s a b).2 := List.prefix_append _ _
theorem gOr_le {n : ℕ} (s : St n) (a b : ℕ) : s.le (gOr s a b).2 := List.prefix_append _ _

theorem gNot_len {n : ℕ} (s : St n) (a : ℕ) : (gNot s a).2.gs.length = s.gs.length + 1 := by
  simp [gNot]
theorem gAnd_len {n : ℕ} (s : St n) (a b : ℕ) : (gAnd s a b).2.gs.length = s.gs.length + 1 := by
  simp [gAnd]
theorem gOr_len {n : ℕ} (s : St n) (a b : ℕ) : (gOr s a b).2.gs.length = s.gs.length + 1 := by
  simp [gOr]

theorem gNot_spec {n : ℕ} {x : List Bool} (hb : Base n x) {s : St n} {a : ℕ} {va : Bool}
    (ha : Has x s a va) : Has x (gNot s a).2 (gNot s a).1 (!va) := by
  refine ⟨by simp [gNot], ?_⟩
  show vl x (s.gs ++ [_]) (n + s.gs.length) = _
  rw [vl_new' hb.len, cl_eq ha.1]
  simp [GateOp.eval, ha.2]

theorem gAnd_spec {n : ℕ} {x : List Bool} (hb : Base n x) {s : St n} {a b : ℕ} {va vb : Bool}
    (ha : Has x s a va) (hb' : Has x s b vb) : Has x (gAnd s a b).2 (gAnd s a b).1 (va && vb) := by
  refine ⟨by simp [gAnd], ?_⟩
  show vl x (s.gs ++ [_]) (n + s.gs.length) = _
  rw [vl_new' hb.len, cl_eq ha.1, cl_eq hb'.1]
  simp [GateOp.eval, ha.2, hb'.2]

theorem gOr_spec {n : ℕ} {x : List Bool} (hb : Base n x) {s : St n} {a b : ℕ} {va vb : Bool}
    (ha : Has x s a va) (hb' : Has x s b vb) : Has x (gOr s a b).2 (gOr s a b).1 (va || vb) := by
  refine ⟨by simp [gOr], ?_⟩
  show vl x (s.gs ++ [_]) (n + s.gs.length) = _
  rw [vl_new' hb.len, cl_eq ha.1, cl_eq hb'.1]
  simp [GateOp.eval, ha.2, hb'.2]

-- ===================== list gadgets =====================

def Valid {n : ℕ} (s : St n) (l : List ℕ) : Prop := ∀ a ∈ l, a < n + s.gs.length

theorem Valid.mono {n : ℕ} {s s' : St n} {l : List ℕ} (h : Valid s l) (hle : s.le s') :
    Valid s' l := fun a ha =>
  lt_of_lt_of_le (h a ha) (Nat.add_le_add_left (St.le_len hle) n)

def cntB {n : ℕ} (x : List Bool) (s : St n) (l : List ℕ) : ℕ := l.countP (fun a => vl x s.gs a)

theorem cntB_mono {n : ℕ} {x : List Bool} (hb : Base n x) {s s' : St n} {l : List ℕ}
    (h : Valid s l) (hle : s.le s') : cntB x s' l = cntB x s l := by
  unfold cntB
  apply List.countP_congr
  intro a ha
  rw [vl_mono hle (by rw [hb.len]; exact h a ha)]

theorem cntB_le {n : ℕ} (x : List Bool) (s : St n) (l : List ℕ) : cntB x s l ≤ l.length :=
  List.countP_le_length

theorem cntB_cons {n : ℕ} (x : List Bool) (s : St n) (a : ℕ) (l : List ℕ) :
    cntB x s (a :: l) = cntB x s l + (vl x s.gs a).toNat := by
  unfold cntB
  rw [List.countP_cons]
  cases vl x s.gs a <;> simp

theorem cntB_append {n : ℕ} (x : List Bool) (s : St n) (l l' : List ℕ) :
    cntB x s (l ++ l') = cntB x s l + cntB x s l' := by
  unfold cntB
  rw [List.countP_append]

def mapG {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) : St n → List α → List ℕ × St n
  | s, [] => ([], s)
  | s, a :: l => ((f s a).1 :: (mapG f (f s a).2 l).1, (mapG f (f s a).2 l).2)

theorem mapG_spec {n : ℕ} {x : List Bool} (hb : Base n x) {α : Type} (f : St n → α → ℕ × St n)
    (F : α → Bool) (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) :
    ∀ (l : List α) (s : St n),
      (∀ s', s.le s' → ∀ a ∈ l, Has x (f s' a).2 (f s' a).1 (F a)) →
      s.le (mapG f s l).2 ∧ (mapG f s l).1.length = l.length ∧
      Valid (mapG f s l).2 (mapG f s l).1 ∧
      cntB x (mapG f s l).2 (mapG f s l).1 = l.countP F ∧
      ∀ j (hj : j < l.length), Has x (mapG f s l).2 ((mapG f s l).1.getD j 0) (F l[j]) := by
  intro l
  induction l with
  | nil =>
    intro s _
    refine ⟨St.le_refl s, rfl, ?_, rfl, ?_⟩
    · intro a ha
      simp [mapG] at ha
    · intro j hj
      simp at hj
  | cons a l ih =>
    intro s hf
    have h1 : Has x (f s a).2 (f s a).1 (F a) := hf s (St.le_refl s) a (by simp)
    have ih' := ih (f s a).2 (fun s' hs' a' ha' =>
      hf s' (St.le_trans (hle s a) hs') a' (by simp [ha']))
    obtain ⟨ile, ilen, ival, icnt, ipt⟩ := ih'
    have h1' : Has x (mapG f (f s a).2 l).2 (f s a).1 (F a) := h1.mono hb ile
    refine ⟨St.le_trans (hle s a) ile, by simp [mapG, ilen], ?_, ?_, ?_⟩
    · intro b hbm
      simp only [mapG, List.mem_cons] at hbm
      rcases hbm with rfl | hbm
      · exact h1'.1
      · exact ival b hbm
    · show cntB x (mapG f (f s a).2 l).2 ((f s a).1 :: (mapG f (f s a).2 l).1) = _
      rw [cntB_cons, icnt, h1'.2, List.countP_cons]
      cases F a <;> simp
    · intro j hj
      cases j with
      | zero => simpa [mapG] using h1'
      | succ j =>
        have := ipt j (by simpa using hj)
        simpa [mapG] using this

theorem mapG_len {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) (c : ℕ)
    (hc : ∀ (s : St n) (a : α), (f s a).2.gs.length ≤ s.gs.length + c) :
    ∀ (l : List α) (s : St n), (mapG f s l).2.gs.length ≤ s.gs.length + l.length * c := by
  intro l
  induction l with
  | nil => intro s; simp [mapG]
  | cons a l ih =>
    intro s
    have h1 := hc s a
    have h2 := ih (f s a).2
    simp only [mapG, List.length_cons]
    have : (l.length + 1) * c = l.length * c + c := by ring
    omega

theorem mapG_outlen {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) :
    ∀ (l : List α) (s : St n), (mapG f s l).1.length = l.length := by
  intro l
  induction l with
  | nil => intro s; rfl
  | cons a l ih => intro s; simp [mapG, ih]

-- big AND / OR
def gAndL {n : ℕ} (s : St n) : List ℕ → ℕ × St n
  | [] => (1, s)
  | a :: l => gAnd (gAndL s l).2 a (gAndL s l).1

def gOrL {n : ℕ} (s : St n) : List ℕ → ℕ × St n
  | [] => (0, s)
  | a :: l => gOr (gOrL s l).2 a (gOrL s l).1

theorem gAndL_le {n : ℕ} (s : St n) (l : List ℕ) : s.le (gAndL s l).2 := by
  induction l with
  | nil => exact St.le_refl s
  | cons a l ih => exact St.le_trans ih (gAnd_le _ _ _)

theorem gOrL_le {n : ℕ} (s : St n) (l : List ℕ) : s.le (gOrL s l).2 := by
  induction l with
  | nil => exact St.le_refl s
  | cons a l ih => exact St.le_trans ih (gOr_le _ _ _)

theorem gAndL_len {n : ℕ} (s : St n) (l : List ℕ) :
    (gAndL s l).2.gs.length = s.gs.length + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [gAndL, gAnd_len, ih, List.length_cons]; omega

theorem gOrL_len {n : ℕ} (s : St n) (l : List ℕ) :
    (gOrL s l).2.gs.length = s.gs.length + l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [gOrL, gOr_len, ih, List.length_cons]; omega

theorem gAndL_spec {n : ℕ} {x : List Bool} (hb : Base n x) (s : St n) (F : ℕ → Bool) (l : List ℕ)
    (h : ∀ a ∈ l, Has x s a (F a)) : Has x (gAndL s l).2 (gAndL s l).1 (l.all F) := by
  induction l with
  | nil => simpa [gAndL] using has_true hb s
  | cons a l ih =>
    have ih' := ih (fun b hb' => h b (by simp [hb']))
    have ha : Has x (gAndL s l).2 a (F a) := (h a (by simp)).mono hb (gAndL_le s l)
    simpa [gAndL] using gAnd_spec hb ha ih'

theorem gOrL_spec {n : ℕ} {x : List Bool} (hb : Base n x) (s : St n) (F : ℕ → Bool) (l : List ℕ)
    (h : ∀ a ∈ l, Has x s a (F a)) : Has x (gOrL s l).2 (gOrL s l).1 (l.any F) := by
  induction l with
  | nil => simpa [gOrL] using has_false hb s
  | cons a l ih =>
    have ih' := ih (fun b hb' => h b (by simp [hb']))
    have ha : Has x (gOrL s l).2 a (F a) := (h a (by simp)).mono hb (gOrL_le s l)
    simpa [gOrL] using gOr_spec hb ha ih'

-- NOT of every wire of a list
def gNotL {n : ℕ} (s : St n) (l : List ℕ) : List ℕ × St n := mapG gNot s l

theorem gNotL_spec {n : ℕ} {x : List Bool} (hb : Base n x) (s : St n) (l : List ℕ)
    (h : Valid s l) :
    s.le (gNotL s l).2 ∧ (gNotL s l).1.length = l.length ∧ Valid (gNotL s l).2 (gNotL s l).1 ∧
      cntB x (gNotL s l).2 (gNotL s l).1 = l.length - cntB x s l := by
  have key := mapG_spec hb gNot (fun a => !vl x s.gs a) gNot_le l s (by
    intro s' hs' a ha
    exact gNot_spec hb ((has_self (h a ha)).mono hb hs'))
  obtain ⟨kle, klen, kval, kcnt, _⟩ := key
  refine ⟨kle, klen, kval, ?_⟩
  show cntB x (mapG gNot s l).2 (mapG gNot s l).1 = _
  rw [kcnt]
  unfold cntB
  have := List.length_eq_countP_add_countP (fun a => vl x s.gs a) (l := l)
  have h2 : List.countP (fun a => !vl x s.gs a) l = List.countP (fun a => ¬ (vl x s.gs a = true)) l := by
    apply List.countP_congr
    intro a _
    simp
  rw [h2]
  omega

theorem gNotL_len {n : ℕ} (s : St n) (l : List ℕ) :
    (gNotL s l).2.gs.length ≤ s.gs.length + l.length := by
  have := mapG_len (n := n) gNot 1 (fun s a => by rw [gNot_len]) l s
  simpa [gNotL] using this

-- thermometer of a count
def pick (th : List ℕ) (θ : ℕ) : ℕ := if θ = 0 then 1 else th.getD (θ - 1) 0

def Therm {n : ℕ} (x : List Bool) (s : St n) (th : List ℕ) (c : ℕ) : Prop :=
  ∀ θ, Has x s (pick th θ) (decide (θ ≤ c))

def rowF {n : ℕ} (a : ℕ) (th : List ℕ) (s : St n) (j : ℕ) : ℕ × St n :=
  gOr (gAnd s a (pick th j)).2 (pick th (j+1)) (gAnd s a (pick th j)).1

def gCount {n : ℕ} (s : St n) : List ℕ → List ℕ × St n
  | [] => ([], s)
  | a :: l => mapG (rowF a (gCount s l).1) (gCount s l).2 (List.range ((gCount s l).1.length + 1))

theorem rowF_le {n : ℕ} (a : ℕ) (th : List ℕ) (s : St n) (j : ℕ) : s.le (rowF a th s j).2 :=
  St.le_trans (gAnd_le _ _ _) (gOr_le _ _ _)

theorem gCount_spec {n : ℕ} {x : List Bool} (hb : Base n x) :
    ∀ (l : List ℕ) (s : St n), Valid s l →
      s.le (gCount s l).2 ∧ (gCount s l).1.length = l.length ∧
      Therm x (gCount s l).2 (gCount s l).1 (cntB x s l) := by
  intro l
  induction l with
  | nil =>
    intro s _
    refine ⟨St.le_refl s, rfl, ?_⟩
    intro θ
    by_cases h0 : θ = 0
    · subst h0
      simpa [pick, cntB, gCount] using has_true hb s
    · have : decide (θ ≤ cntB x s []) = false := by simp [cntB]; omega
      rw [this]
      simpa [pick, h0, gCount] using has_false hb s
  | cons a l ih =>
    intro s hv
    have hvl : Valid s l := fun b hb' => hv b (by simp [hb'])
    obtain ⟨ile, ilen, ith⟩ := ih s hvl
    have ha : Has x s a (vl x s.gs a) := has_self (hv a (by simp))
    have key := mapG_spec hb (rowF a (gCount s l).1)
      (fun j => decide (j + 1 ≤ cntB x s l + (vl x s.gs a).toNat)) (rowF_le a (gCount s l).1)
      (List.range ((gCount s l).1.length + 1)) (gCount s l).2 (by
        intro s' hs' j _
        have ha' : Has x s' a (vl x s.gs a) := ha.mono hb (St.le_trans ile hs')
        have hj : Has x s' (pick (gCount s l).1 j) (decide (j ≤ cntB x s l)) := (ith j).mono hb hs'
        have hj1 : Has x s' (pick (gCount s l).1 (j+1)) (decide (j + 1 ≤ cntB x s l)) :=
          (ith (j+1)).mono hb hs'
        have h1 := gAnd_spec hb ha' hj
        have h2 := gOr_spec hb (hj1.mono hb (gAnd_le _ _ _)) h1
        have hval : (decide (j + 1 ≤ cntB x s l) || (vl x s.gs a && decide (j ≤ cntB x s l))) =
            decide (j + 1 ≤ cntB x s l + (vl x s.gs a).toNat) := by
          cases vl x s.gs a <;> simp <;> omega
        rw [← hval]
        exact h2)
    obtain ⟨kle, klen, _, _, kpt⟩ := key
    have hlen : (gCount s (a :: l)).1.length = (a :: l).length := by
      show (mapG _ _ _).1.length = _
      rw [klen]
      simp [ilen]
    refine ⟨St.le_trans ile kle, hlen, ?_⟩
    intro θ
    rw [cntB_cons]
    by_cases h0 : θ = 0
    · subst h0
      simpa [pick] using has_true hb (gCount s (a :: l)).2
    · obtain ⟨j, rfl⟩ : ∃ j, θ = j + 1 := ⟨θ - 1, by omega⟩
      by_cases hj : j < (gCount s l).1.length + 1
      · have := kpt j (by simpa using hj)
        simpa [pick, gCount] using this
      · have hfalse : decide (j + 1 ≤ cntB x s l + (vl x s.gs a).toNat) = false := by
          have h1 := cntB_le x s l
          have h2 : (vl x s.gs a).toNat ≤ 1 := by cases vl x s.gs a <;> simp
          simp
          omega
        rw [hfalse]
        have hd : (gCount s (a :: l)).1.getD j 0 = 0 := by
          apply List.getD_eq_default
          rw [hlen]
          simp
          omega
        have hp : pick (gCount s (a :: l)).1 (j + 1) = 0 := by
          unfold pick
          rw [if_neg (by omega)]
          exact hd
        rw [hp]
        exact has_false hb (gCount s (a :: l)).2

theorem gCount_outlen {n : ℕ} (s : St n) (l : List ℕ) : (gCount s l).1.length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (mapG _ _ _).1.length = _
    rw [mapG_outlen]
    simp [ih]

theorem rowF_len {n : ℕ} (a : ℕ) (th : List ℕ) (s : St n) (j : ℕ) :
    (rowF a th s j).2.gs.length ≤ s.gs.length + 2 := by
  simp [rowF, gOr_len, gAnd_len]

theorem gCount_len {n : ℕ} (s : St n) (l : List ℕ) :
    (gCount s l).2.gs.length ≤ s.gs.length + 2 * (l.length * l.length + l.length) := by
  induction l with
  | nil => simp [gCount]
  | cons a l ih =>
    have h := mapG_len (rowF a (gCount s l).1) 2 (rowF_len a (gCount s l).1)
      (List.range ((gCount s l).1.length + 1)) (gCount s l).2
    rw [List.length_range, gCount_outlen] at h
    show (mapG (rowF a (gCount s l).1) (gCount s l).2
      (List.range ((gCount s l).1.length + 1))).2.gs.length ≤ _
    rw [gCount_outlen]
    simp only [List.length_cons]
    nlinarith [ih, h]

-- compare the counts of two bags
def gGe {n : ℕ} (s : St n) (A B : List ℕ) : ℕ × St n :=
  (pick (gCount (gNotL s B).2 (A ++ (gNotL s B).1)).1 B.length,
    (gCount (gNotL s B).2 (A ++ (gNotL s B).1)).2)

theorem gGe_spec {n : ℕ} {x : List Bool} (hb : Base n x) (s : St n) (A B : List ℕ)
    (hA : Valid s A) (hB : Valid s B) :
    s.le (gGe s A B).2 ∧ Has x (gGe s A B).2 (gGe s A B).1 (decide (cntB x s B ≤ cntB x s A)) := by
  obtain ⟨nle, nlen, nval, ncnt⟩ := gNotL_spec hb s B hB
  have hv : Valid (gNotL s B).2 (A ++ (gNotL s B).1) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hA.mono nle a ha
    · exact nval a ha
  obtain ⟨cle, _, cth⟩ := gCount_spec hb (A ++ (gNotL s B).1) (gNotL s B).2 hv
  refine ⟨St.le_trans nle cle, ?_⟩
  have h := cth B.length
  have hcnt : cntB x (gNotL s B).2 (A ++ (gNotL s B).1) = cntB x s A + (B.length - cntB x s B) := by
    rw [cntB_append, ncnt, cntB_mono hb hA nle]
  have hB' := cntB_le x s B
  have hdec : decide (B.length ≤ cntB x (gNotL s B).2 (A ++ (gNotL s B).1)) =
      decide (cntB x s B ≤ cntB x s A) := by
    rw [hcnt]
    apply decide_eq_decide.mpr
    omega
  rw [← hdec]
  exact h

theorem gGe_len {n : ℕ} (s : St n) (A B : List ℕ) :
    (gGe s A B).2.gs.length ≤ s.gs.length + B.length +
      2 * ((A.length + B.length) * (A.length + B.length) + (A.length + B.length)) := by
  have h1 := gNotL_len s B
  have h2 := gCount_len (gNotL s B).2 (A ++ (gNotL s B).1)
  have h3 : (gNotL s B).1.length = B.length := mapG_outlen _ _ _
  rw [List.length_append, h3] at h2
  show (gCount _ _).2.gs.length ≤ _
  omega

-- ===================== more bag lemmas, loops with function-valued results =====================

theorem Valid_append {n : ℕ} {s : St n} {l l' : List ℕ} (h : Valid s l) (h' : Valid s l') :
    Valid s (l ++ l') := by
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact h a ha
  · exact h' a ha

theorem Valid_flatMap {n : ℕ} {s : St n} {α : Type} (l : List α) (g : α → List ℕ)
    (h : ∀ a ∈ l, Valid s (g a)) : Valid s (l.flatMap g) := by
  intro b hb
  obtain ⟨a, ha, hba⟩ := List.mem_flatMap.mp hb
  exact h a ha b hba

theorem Valid_repflat {n : ℕ} {s : St n} (m : ℕ) {l : List ℕ} (h : Valid s l) :
    Valid s (List.replicate m l).flatten := by
  intro b hb
  obtain ⟨l', hl', hbl⟩ := List.mem_flatten.mp hb
  rw [List.eq_of_mem_replicate hl'] at hbl
  exact h b hbl

theorem Valid_replicate {n : ℕ} {s : St n} (m : ℕ) {a : ℕ} (h : a < n + s.gs.length) :
    Valid s (List.replicate m a) := by
  intro b hb
  rw [List.eq_of_mem_replicate hb]
  exact h

theorem cntB_nil {n : ℕ} (x : List Bool) (s : St n) : cntB x s [] = 0 := rfl

theorem cntB_repflat {n : ℕ} (x : List Bool) (s : St n) (m : ℕ) (l : List ℕ) :
    cntB x s (List.replicate m l).flatten = m * cntB x s l := by
  induction m with
  | zero => simp [cntB]
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, cntB_append, ih]
    ring

theorem cntB_replicate {n : ℕ} (x : List Bool) (s : St n) (m : ℕ) (a : ℕ) :
    cntB x s (List.replicate m a) = m * (vl x s.gs a).toNat := by
  induction m with
  | zero => simp [cntB]
  | succ m ih =>
    rw [List.replicate_succ, cntB_cons, ih]
    ring

theorem cntB_flatMap {n : ℕ} (x : List Bool) (s : St n) {α : Type} (l : List α) (g : α → List ℕ) :
    cntB x s (l.flatMap g) = (l.map (fun a => cntB x s (g a))).sum := by
  induction l with
  | nil => simp [cntB]
  | cons a l ih =>
    rw [List.flatMap_cons, cntB_append, ih]
    simp

theorem mapG_all {n : ℕ} {x : List Bool} (hb : Base n x) {α : Type} (f : St n → α → ℕ × St n)
    (F : α → Bool) (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) :
    ∀ (l : List α) (s : St n),
      (∀ s', s.le s' → ∀ a ∈ l, Has x (f s' a).2 (f s' a).1 (F a)) →
      (mapG f s l).1.all (fun o => vl x (mapG f s l).2.gs o) = l.all F ∧
      (mapG f s l).1.any (fun o => vl x (mapG f s l).2.gs o) = l.any F := by
  intro l
  induction l with
  | nil => intro s _; simp [mapG]
  | cons a l ih =>
    intro s hf
    have h1 : Has x (f s a).2 (f s a).1 (F a) := hf s (St.le_refl s) a (by simp)
    have hf' : ∀ s', (f s a).2.le s' → ∀ a' ∈ l, Has x (f s' a').2 (f s' a').1 (F a') :=
      fun s' hs' a' ha' => hf s' (St.le_trans (hle s a) hs') a' (by simp [ha'])
    obtain ⟨iall, iany⟩ := ih (f s a).2 hf'
    obtain ⟨ile, _⟩ := mapG_spec hb f F hle l (f s a).2 hf'
    have h1' : Has x (mapG f (f s a).2 l).2 (f s a).1 (F a) := h1.mono hb ile
    constructor
    · show ((f s a).1 :: (mapG f (f s a).2 l).1).all (fun o => vl x (mapG f (f s a).2 l).2.gs o) = _
      rw [List.all_cons, List.all_cons, iall, h1'.2]
    · show ((f s a).1 :: (mapG f (f s a).2 l).1).any (fun o => vl x (mapG f (f s a).2 l).2.gs o) = _
      rw [List.any_cons, List.any_cons, iany, h1'.2]

-- AND over the results of a mapped gadget
def gAllG {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) (s : St n) (l : List α) : ℕ × St n :=
  gAndL (mapG f s l).2 (mapG f s l).1

def gAnyG {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) (s : St n) (l : List α) : ℕ × St n :=
  gOrL (mapG f s l).2 (mapG f s l).1

theorem gAllG_spec {n : ℕ} {x : List Bool} (hb : Base n x) {α : Type} (f : St n → α → ℕ × St n)
    (F : α → Bool) (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) (l : List α) (s : St n)
    (hf : ∀ s', s.le s' → ∀ a ∈ l, Has x (f s' a).2 (f s' a).1 (F a)) :
    s.le (gAllG f s l).2 ∧ Has x (gAllG f s l).2 (gAllG f s l).1 (l.all F) := by
  obtain ⟨mle, _, mval, _, _⟩ := mapG_spec hb f F hle l s hf
  obtain ⟨mall, _⟩ := mapG_all hb f F hle l s hf
  refine ⟨St.le_trans mle (gAndL_le _ _), ?_⟩
  have := gAndL_spec hb (mapG f s l).2 (fun o => vl x (mapG f s l).2.gs o) (mapG f s l).1
    (fun a ha => has_self (mval a ha))
  rw [mall] at this
  exact this

theorem gAnyG_spec {n : ℕ} {x : List Bool} (hb : Base n x) {α : Type} (f : St n → α → ℕ × St n)
    (F : α → Bool) (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) (l : List α) (s : St n)
    (hf : ∀ s', s.le s' → ∀ a ∈ l, Has x (f s' a).2 (f s' a).1 (F a)) :
    s.le (gAnyG f s l).2 ∧ Has x (gAnyG f s l).2 (gAnyG f s l).1 (l.any F) := by
  obtain ⟨mle, _, mval, _, _⟩ := mapG_spec hb f F hle l s hf
  obtain ⟨_, many⟩ := mapG_all hb f F hle l s hf
  refine ⟨St.le_trans mle (gOrL_le _ _), ?_⟩
  have := gOrL_spec hb (mapG f s l).2 (fun o => vl x (mapG f s l).2.gs o) (mapG f s l).1
    (fun a ha => has_self (mval a ha))
  rw [many] at this
  exact this

theorem gAllG_len {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) (c : ℕ)
    (hc : ∀ (s : St n) (a : α), (f s a).2.gs.length ≤ s.gs.length + c) (s : St n) (l : List α) :
    (gAllG f s l).2.gs.length ≤ s.gs.length + l.length * (c + 1) := by
  have h1 := mapG_len f c hc l s
  have h2 := gAndL_len (mapG f s l).2 (mapG f s l).1
  rw [mapG_outlen] at h2
  show (gAndL _ _).2.gs.length ≤ _
  rw [h2]
  have : l.length * (c + 1) = l.length * c + l.length := by ring
  omega

theorem gAnyG_len {n : ℕ} {α : Type} (f : St n → α → ℕ × St n) (c : ℕ)
    (hc : ∀ (s : St n) (a : α), (f s a).2.gs.length ≤ s.gs.length + c) (s : St n) (l : List α) :
    (gAnyG f s l).2.gs.length ≤ s.gs.length + l.length * (c + 1) := by
  have h1 := mapG_len f c hc l s
  have h2 := gOrL_len (mapG f s l).2 (mapG f s l).1
  rw [mapG_outlen] at h2
  show (gOrL _ _).2.gs.length ≤ _
  rw [h2]
  have : l.length * (c + 1) = l.length * c + l.length := by ring
  omega

-- loop over a list, collecting the results as a function
def forG {n : ℕ} {α β : Type} [DecidableEq α] (f : St n → α → β × St n) (dflt : β) :
    St n → List α → (α → β) × St n
  | s, [] => (fun _ => dflt, s)
  | s, a :: l =>
    (fun a' => if a' = a then (f s a).1 else (forG f dflt (f s a).2 l).1 a',
      (forG f dflt (f s a).2 l).2)

theorem forG_spec {n : ℕ} {α β : Type} [DecidableEq α] (f : St n → α → β × St n) (dflt : β)
    (R : α → β → St n → Prop)
    (hR : ∀ (a : α) (b : β) (s s' : St n), R a b s → s.le s' → R a b s')
    (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) :
    ∀ (l : List α) (s : St n),
      (∀ s', s.le s' → ∀ a ∈ l, R a (f s' a).1 (f s' a).2) →
      s.le (forG f dflt s l).2 ∧ ∀ a ∈ l, R a ((forG f dflt s l).1 a) (forG f dflt s l).2 := by
  intro l
  induction l with
  | nil =>
    intro s _
    exact ⟨St.le_refl s, fun a ha => by simp at ha⟩
  | cons a l ih =>
    intro s hf
    have h1 := hf s (St.le_refl s) a (by simp)
    obtain ⟨ile, ipt⟩ := ih (f s a).2 (fun s' hs' a' ha' =>
      hf s' (St.le_trans (hle s a) hs') a' (by simp [ha']))
    refine ⟨St.le_trans (hle s a) ile, ?_⟩
    intro a' ha'
    show R a' (if a' = a then (f s a).1 else (forG f dflt (f s a).2 l).1 a') (forG f dflt (f s a).2 l).2
    by_cases hEq : a' = a
    · rw [if_pos hEq, hEq]
      exact hR _ _ _ _ h1 ile
    · rw [if_neg hEq]
      rcases List.mem_cons.mp ha' with h | h
      · exact absurd h hEq
      · exact ipt a' h

theorem forG_len {n : ℕ} {α β : Type} [DecidableEq α] (f : St n → α → β × St n) (dflt : β) (c : ℕ)
    (hc : ∀ (s : St n) (a : α), (f s a).2.gs.length ≤ s.gs.length + c) :
    ∀ (l : List α) (s : St n), (forG f dflt s l).2.gs.length ≤ s.gs.length + l.length * c := by
  intro l
  induction l with
  | nil => intro s; simp [forG]
  | cons a l ih =>
    intro s
    have h1 := hc s a
    have h2 := ih (f s a).2
    simp only [forG, List.length_cons]
    have : (l.length + 1) * c = l.length * c + c := by ring
    omega

theorem has_cnt {n : ℕ} {x : List Bool} {s : St n} {i : ℕ} {v : Bool} (h : Has x s i v) :
    (vl x s.gs i).toNat = v.toNat := by rw [h.2]

-- unconditional extension facts
theorem mapG_le {n : ℕ} {α : Type} (f : St n → α → ℕ × St n)
    (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) :
    ∀ (l : List α) (s : St n), s.le (mapG f s l).2 := by
  intro l
  induction l with
  | nil => intro s; exact St.le_refl s
  | cons a l ih => intro s; exact St.le_trans (hle s a) (ih (f s a).2)

theorem forG_le {n : ℕ} {α β : Type} [DecidableEq α] (f : St n → α → β × St n) (dflt : β)
    (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) :
    ∀ (l : List α) (s : St n), s.le (forG f dflt s l).2 := by
  intro l
  induction l with
  | nil => intro s; exact St.le_refl s
  | cons a l ih => intro s; exact St.le_trans (hle s a) (ih (f s a).2)

theorem gNotL_le {n : ℕ} (s : St n) (l : List ℕ) : s.le (gNotL s l).2 := mapG_le gNot gNot_le l s

theorem gCount_le {n : ℕ} (s : St n) (l : List ℕ) : s.le (gCount s l).2 := by
  induction l with
  | nil => exact St.le_refl s
  | cons a l ih => exact St.le_trans ih (mapG_le _ (rowF_le a _) _ _)

theorem gGe_le {n : ℕ} (s : St n) (A B : List ℕ) : s.le (gGe s A B).2 :=
  St.le_trans (gNotL_le s B) (gCount_le _ _)

theorem gAllG_le {n : ℕ} {α : Type} (f : St n → α → ℕ × St n)
    (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) (s : St n) (l : List α) :
    s.le (gAllG f s l).2 := St.le_trans (mapG_le f hle l s) (gAndL_le _ _)

theorem gAnyG_le {n : ℕ} {α : Type} (f : St n → α → ℕ × St n)
    (hle : ∀ (s : St n) (a : α), St.le s (f s a).2) (s : St n) (l : List α) :
    s.le (gAnyG f s l).2 := St.le_trans (mapG_le f hle l s) (gOrL_le _ _)
-- ===================== decoder core =====================

noncomputable def pairsL (t : ℕ) : List (Pr t) := (Finset.univ : Finset (Pr t)).toList
noncomputable def probes (d : ℕ) : List (Fin d) := (Finset.univ : Finset (Fin d)).toList

theorem mem_pairsL {t : ℕ} (e : Pr t) : e ∈ pairsL t := by simp [pairsL]
theorem mem_probes {d : ℕ} (i : Fin d) : i ∈ probes d := by simp [probes]

theorem cntB_flatMap_univ {n : ℕ} {α : Type} [Fintype α] (x : List Bool) (s : St n)
    (g : α → List ℕ) :
    cntB x s ((Finset.univ : Finset α).toList.flatMap g) = ∑ a : α, cntB x s (g a) := by
  rw [cntB_flatMap, Finset.sum_map_toList]

theorem cntB_map_has {n : ℕ} {x : List Bool} {s : St n} {α : Type} (l : List α) (w : α → ℕ)
    (F : α → Bool) (h : ∀ c ∈ l, Has x s (w c) (F c)) : cntB x s (l.map w) = l.countP F := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, cntB_cons, ih (fun c hc => h c (by simp [hc])), (h a (by simp)).2,
      List.countP_cons]
    cases F a <;> simp

theorem countP_range_thr (A Bv : ℕ) : ∀ N : ℕ,
    (List.range N).countP (fun c => decide (c + 1 + A ≤ Bv)) = min N (Bv - A) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.countP_append, ih]
    by_cases h : N + 1 + A ≤ Bv
    · simp [h]
      omega
    · simp [h]
      omega

theorem clamp_id (a b l stp : ℕ) (hbl : b ≤ l) :
    ((min (2 * stp) (512 * (a + (l - b)) + stp - 512 * l) : ℕ) : ℤ) =
      clampZ ((a : ℤ) - (b : ℤ)) stp + (stp : ℤ) := by
  unfold clampZ
  omega

def LL : ℕ := 512

theorem len_repflat (m : ℕ) (l : List ℕ) : (List.replicate m l).flatten.length = m * l.length := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
    ring

noncomputable def posBag {t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb : Fin d → List ℕ) (B : Pr t → List ℕ)
    (mu stp : ℕ) (i : Fin d) : List ℕ :=
  (List.replicate stp (Pb i)).flatten ++
    (List.replicate mu ((Finset.univ : Finset (Pr t)).toList.flatMap
      (fun e => if chi (batch i) e = 1 then [] else B e))).flatten

noncomputable def negBag {t d : ℕ} (batch : Fin d → Fin t → Bool) (Qb : Fin d → List ℕ) (B : Pr t → List ℕ)
    (mu stp : ℕ) (i : Fin d) : List ℕ :=
  (List.replicate stp (Qb i)).flatten ++
    (List.replicate mu ((Finset.univ : Finset (Pr t)).toList.flatMap
      (fun e => if chi (batch i) e = 1 then B e else []))).flatten

def uStep {n : ℕ} (pos neg : List ℕ) (stp : ℕ) (s : St n) : List ℕ × St n :=
  ((List.range (2 * stp)).map (fun c => pick
      (gCount (gNotL s neg).2
        ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1)).1
      (c + 1 + 512 * neg.length)),
    (gCount (gNotL s neg).2
      ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1)).2)

theorem uStep_spec {n : ℕ} {x : List Bool} (hb : Base n x) (pos neg : List ℕ) (stp : ℕ) (s : St n)
    (hpos : Valid s pos) (hneg : Valid s neg) :
    s.le (uStep pos neg stp s).2 ∧ (uStep pos neg stp s).1.length = 2 * stp ∧
      Valid (uStep pos neg stp s).2 (uStep pos neg stp s).1 ∧
      ((cntB x (uStep pos neg stp s).2 (uStep pos neg stp s).1 : ℕ) : ℤ) =
        clampZ ((cntB x s pos : ℤ) - (cntB x s neg : ℤ)) stp + (stp : ℤ) := by
  obtain ⟨nle, nlen, nval, ncnt⟩ := gNotL_spec hb s neg hneg
  have hbag : Valid (gNotL s neg).2
      ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1) := by
    apply Valid_append
    · exact Valid_repflat 512 (Valid_append (hpos.mono nle) nval)
    · exact Valid_replicate stp (has_true hb _).1
  obtain ⟨cle, _, cth⟩ := gCount_spec hb _ (gNotL s neg).2 hbag
  have hcnt : cntB x (gNotL s neg).2
      ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1) =
      512 * (cntB x s pos + (neg.length - cntB x s neg)) + stp := by
    rw [cntB_append, cntB_repflat, cntB_append, ncnt, cntB_mono hb hpos nle, cntB_replicate,
      (has_true hb _).2]
    show LL * _ + stp * 1 = _
    have hLL : LL = 512 := rfl
    rw [hLL]
    omega
  have hall : ∀ c ∈ List.range (2 * stp), Has x (uStep pos neg stp s).2
      (pick (gCount (gNotL s neg).2
        ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1)).1
        (c + 1 + 512 * neg.length))
      (decide (c + 1 + 512 * neg.length ≤ 512 * (cntB x s pos + (neg.length - cntB x s neg)) + stp)) := by
    intro c _
    have := cth (c + 1 + 512 * neg.length)
    rw [hcnt] at this
    exact this
  refine ⟨St.le_trans nle cle, by
    show ((List.range (2 * stp)).map _).length = _
    rw [List.length_map, List.length_range], ?_, ?_⟩
  · intro a ha
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ha
    exact (hall c hc).1
  · show ((cntB x (uStep pos neg stp s).2 ((List.range (2 * stp)).map _) : ℕ) : ℤ) = _
    rw [cntB_map_has _ _ _ hall, countP_range_thr]
    exact clamp_id _ _ _ _ (cntB_le x s neg)

theorem uStep_len {n : ℕ} (pos neg : List ℕ) (stp : ℕ) (s : St n) :
    (uStep pos neg stp s).2.gs.length ≤ s.gs.length + neg.length +
      2 * ((512 * (pos.length + neg.length) + stp) * (512 * (pos.length + neg.length) + stp) +
        (512 * (pos.length + neg.length) + stp)) := by
  have h1 := gNotL_len s neg
  have h2 := gCount_len (gNotL s neg).2
    ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1)
  have h3 : (gNotL s neg).1.length = neg.length := mapG_outlen _ _ _
  have h4 : ((List.replicate LL (pos ++ (gNotL s neg).1)).flatten ++ List.replicate stp 1).length =
      512 * (pos.length + neg.length) + stp := by
    rw [List.length_append, len_repflat, List.length_append, h3, List.length_replicate]
    rfl
  rw [h4] at h2
  show (gCount _ _).2.gs.length ≤ _
  omega

theorem uStep_le {n : ℕ} (pos neg : List ℕ) (stp : ℕ) (s : St n) : s.le (uStep pos neg stp s).2 :=
  St.le_trans (gNotL_le s neg) (gCount_le _ _)

-- ---------- stages of one conditional gradient step ----------

noncomputable def stU {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) : (Fin d → List ℕ) × St n :=
  forG (fun s i => uStep (posBag batch Pb B mu stp i) (negBag batch Qb B mu stp i) stp s) [] s
    (probes d)

theorem stU_spec {n t d : ℕ} {x : List Bool} (hb : Base n x) (batch : Fin d → Fin t → Bool)
    (Pb Qb : Fin d → List ℕ) (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n)
    (hpos : ∀ i, Valid s (posBag batch Pb B mu stp i))
    (hneg : ∀ i, Valid s (negBag batch Qb B mu stp i)) :
    s.le (stU batch Pb Qb B mu stp s).2 ∧ ∀ i,
      ((stU batch Pb Qb B mu stp s).1 i).length = 2 * stp ∧
      Valid (stU batch Pb Qb B mu stp s).2 ((stU batch Pb Qb B mu stp s).1 i) ∧
      ((cntB x (stU batch Pb Qb B mu stp s).2 ((stU batch Pb Qb B mu stp s).1 i) : ℕ) : ℤ) =
        clampZ ((cntB x s (posBag batch Pb B mu stp i) : ℤ) -
          (cntB x s (negBag batch Qb B mu stp i) : ℤ)) stp + (stp : ℤ) := by
  have key := forG_spec
    (fun s i => uStep (posBag batch Pb B mu stp i) (negBag batch Qb B mu stp i) stp s) []
    (fun i u s' => u.length = 2 * stp ∧ Valid s' u ∧ ((cntB x s' u : ℕ) : ℤ) =
      clampZ ((cntB x s (posBag batch Pb B mu stp i) : ℤ) -
          (cntB x s (negBag batch Qb B mu stp i) : ℤ)) stp + (stp : ℤ))
    (by
      rintro i u s1 s2 ⟨h1, h2, h3⟩ hle
      exact ⟨h1, h2.mono hle, by rw [cntB_mono hb h2 hle]; exact h3⟩)
    (fun s i => uStep_le _ _ _ s) (probes d) s (by
      intro s' hs' i _
      obtain ⟨_, h2, h3, h4⟩ := uStep_spec hb (posBag batch Pb B mu stp i)
        (negBag batch Qb B mu stp i) stp s' ((hpos i).mono hs') ((hneg i).mono hs')
      rw [cntB_mono hb (hpos i) hs', cntB_mono hb (hneg i) hs'] at h4
      exact ⟨h2, h3, h4⟩)
  exact ⟨key.1, fun i => key.2 i (mem_probes i)⟩

noncomputable def stN {n d : ℕ} (u : Fin d → List ℕ) (s : St n) : (Fin d → List ℕ) × St n :=
  forG (fun s i => gNotL s (u i)) [] s (probes d)

theorem stN_spec {n d : ℕ} {x : List Bool} (hb : Base n x) (u : Fin d → List ℕ) (s : St n)
    (hu : ∀ i, Valid s (u i)) :
    s.le (stN u s).2 ∧ ∀ i, Valid (stN u s).2 ((stN u s).1 i) ∧
      cntB x (stN u s).2 ((stN u s).1 i) = (u i).length - cntB x s (u i) := by
  have key := forG_spec (fun s i => gNotL s (u i)) []
    (fun i v s' => Valid s' v ∧ cntB x s' v = (u i).length - cntB x s (u i))
    (by
      rintro i v s1 s2 ⟨h2, h3⟩ hle
      exact ⟨h2.mono hle, by rw [cntB_mono hb h2 hle]; exact h3⟩)
    (fun s i => gNotL_le s _) (probes d) s (by
      intro s' hs' i _
      obtain ⟨_, _, h3, h4⟩ := gNotL_spec hb s' (u i) ((hu i).mono hs')
      rw [cntB_mono hb (hu i) hs'] at h4
      exact ⟨h3, h4⟩)
  exact ⟨key.1, fun i => key.2 i (mem_probes i)⟩

noncomputable def ubag {t d : ℕ} (batch : Fin d → Fin t → Bool) (u nu : Fin d → List ℕ)
    (e : Pr t) : List ℕ :=
  (Finset.univ : Finset (Fin d)).toList.flatMap (fun i => if chi (batch i) e = 1 then u i else nu i)

noncomputable def stI {n t : ℕ} (U : Pr t → List ℕ) (s : St n) : (Pr t → ℕ) × St n :=
  forG (fun s e => gAllG (fun s e' => gGe s (U e) (U e')) s (pairsL t)) 0 s (pairsL t)

theorem stI_spec {n t : ℕ} {x : List Bool} (hb : Base n x) (U : Pr t → List ℕ) (s : St n)
    (hU : ∀ e, Valid s (U e)) :
    s.le (stI U s).2 ∧ ∀ e, Has x (stI U s).2 ((stI U s).1 e)
      (decide (∀ e', cntB x s (U e') ≤ cntB x s (U e))) := by
  have key := forG_spec (fun s e => gAllG (fun s e' => gGe s (U e) (U e')) s (pairsL t)) 0
    (fun e w s' => Has x s' w (decide (∀ e', cntB x s (U e') ≤ cntB x s (U e))))
    (fun e w s1 s2 h hle => h.mono hb hle)
    (fun s e => gAllG_le _ (fun s e' => gGe_le s _ _) s _) (pairsL t) s (by
      intro s' hs' e _
      have h := (gAllG_spec hb (fun s e' => gGe s (U e) (U e'))
        (fun e' => decide (cntB x s (U e') ≤ cntB x s (U e)))
        (fun s e' => gGe_le s _ _) (pairsL t) s' (by
          intro s2 hs2 e' _
          have h2 := (gGe_spec hb s2 (U e) (U e') ((hU e).mono (St.le_trans hs' hs2))
            ((hU e').mono (St.le_trans hs' hs2))).2
          rw [cntB_mono hb (hU e) (St.le_trans hs' hs2),
            cntB_mono hb (hU e') (St.le_trans hs' hs2)] at h2
          exact h2)).2
      have hall : (pairsL t).all (fun e' => decide (cntB x s (U e') ≤ cntB x s (U e))) =
          decide (∀ e', cntB x s (U e') ≤ cntB x s (U e)) := by
        rw [Bool.eq_iff_iff]
        simp [pairsL]
      rw [← hall]
      exact h)
  exact ⟨key.1, fun e => key.2 e (mem_pairsL e)⟩

noncomputable def stX {n t : ℕ} (isw : Pr t → ℕ) (s : St n) : (Pr t → ℕ) × St n :=
  forG (fun s e => gNot s (isw e)) 0 s (pairsL t)

theorem stX_spec {n t : ℕ} {x : List Bool} (hb : Base n x) (isw : Pr t → ℕ) (v : Pr t → Bool)
    (s : St n) (hv : ∀ e, Has x s (isw e) (v e)) :
    s.le (stX isw s).2 ∧ ∀ e, Has x (stX isw s).2 ((stX isw s).1 e) (!v e) := by
  have key := forG_spec (fun s e => gNot s (isw e)) 0
    (fun e w s' => Has x s' w (!v e))
    (fun e w s1 s2 h hle => h.mono hb hle)
    (fun s e => gNot_le s _) (pairsL t) s (by
      intro s' hs' e _
      exact gNot_spec hb ((hv e).mono hb hs'))
  exact ⟨key.1, fun e => key.2 e (mem_pairsL e)⟩

noncomputable def codeP {t : ℕ} (e : Pr t) : ℕ := (finProdFinEquiv e.val).val

theorem codeP_inj {t : ℕ} : Function.Injective (codeP (t := t)) := by
  intro a b h
  apply Subtype.val_injective
  apply finProdFinEquiv.injective
  exact Fin.val_injective h

noncomputable def stS {n t : ℕ} (isw nisw : Pr t → ℕ) (s : St n) : (Pr t → ℕ) × St n :=
  forG (fun s e => gAndL s (isw e ::
    ((pairsL t).filter (fun e' => decide (codeP e' < codeP e))).map nisw)) 0 s (pairsL t)

theorem stS_spec {n t : ℕ} {x : List Bool} (hb : Base n x) (isw nisw : Pr t → ℕ)
    (v : Pr t → Bool) (s : St n) (hv : ∀ e, Has x s (isw e) (v e))
    (hnv : ∀ e, Has x s (nisw e) (!v e)) :
    s.le (stS isw nisw s).2 ∧ ∀ e, Has x (stS isw nisw s).2 ((stS isw nisw s).1 e)
      (decide (v e = true ∧ ∀ e', codeP e' < codeP e → v e' = false)) := by
  have key := forG_spec (fun s e => gAndL s (isw e ::
      ((pairsL t).filter (fun e' => decide (codeP e' < codeP e))).map nisw)) 0
    (fun e w s' => Has x s' w (decide (v e = true ∧ ∀ e', codeP e' < codeP e → v e' = false)))
    (fun e w s1 s2 h hle => h.mono hb hle)
    (fun s e => gAndL_le s _) (pairsL t) s (by
      intro s' hs' e _
      have h := gAndL_spec hb s' (fun a => vl x s'.gs a) (isw e ::
        ((pairsL t).filter (fun e' => decide (codeP e' < codeP e))).map nisw) (by
          intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact has_self ((hv e).mono hb hs').1
          · obtain ⟨e', _, rfl⟩ := List.mem_map.mp ha
            exact has_self ((hnv e').mono hb hs').1)
      have hval : (isw e :: ((pairsL t).filter (fun e' => decide (codeP e' < codeP e))).map nisw).all
          (fun a => vl x s'.gs a) =
          decide (v e = true ∧ ∀ e', codeP e' < codeP e → v e' = false) := by
        rw [Bool.eq_iff_iff]
        simp only [List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true,
          List.mem_filter, decide_eq_true_eq, Function.comp]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨by rw [← ((hv e).mono hb hs').2]; exact h1, ?_⟩
          intro e' he'
          have := h2 e' ⟨mem_pairsL e', he'⟩
          rw [((hnv e').mono hb hs').2] at this
          simpa using this
        · rintro ⟨h1, h2⟩
          refine ⟨by rw [((hv e).mono hb hs').2]; exact h1, ?_⟩
          intro e' he'
          rw [((hnv e').mono hb hs').2, h2 e' he'.2]
          rfl
      rw [← hval]
      exact h)
  exact ⟨key.1, fun e => key.2 e (mem_pairsL e)⟩

-- ---------- pure facts about the selection sequence ----------

theorem cntOf_succ {t : ℕ} (sel : ℕ → Pr t) (s : ℕ) (e : Pr t) :
    cntOf sel (s + 1) e = cntOf sel s e + (if sel s = e then 1 else 0) := by
  unfold cntOf
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : sel s = e
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg h, if_neg h]
    rfl

theorem cntOf_congr {t : ℕ} (sel sel' : ℕ → Pr t) (s : ℕ) (h : ∀ j, j < s → sel j = sel' j)
    (e : Pr t) : cntOf sel s e = cntOf sel' s e := by
  unfold cntOf
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

theorem score_congr {t d : ℕ} (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (m : ℕ)
    (sel sel' : ℕ → Pr t) (s : ℕ) (h : ∀ j, j < s → sel j = sel' j) (e : Pr t) :
    score batch q m sel s e = score batch q m sel' s e := by
  have hc : ∀ e, cntOf sel s e = cntOf sel' s e := cntOf_congr sel sel' s h
  simp only [score, resid, hc]

theorem exists_estar {t : ℕ} [Nonempty (Pr t)] (sc : Pr t → ℤ) :
    ∃ es : Pr t, (∀ e', sc e' ≤ sc es) ∧
      ∀ e, ((∀ e', sc e' ≤ sc e) ∧ ∀ e', codeP e' < codeP e → ¬ (∀ e'', sc e'' ≤ sc e')) ↔ e = es := by
  obtain ⟨e0, _, he0⟩ := Finset.exists_max_image (Finset.univ : Finset (Pr t)) sc
    Finset.univ_nonempty
  have hne : ((Finset.univ : Finset (Pr t)).filter (fun e => ∀ e', sc e' ≤ sc e)).Nonempty :=
    ⟨e0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun e' => he0 e' (Finset.mem_univ _)⟩
  obtain ⟨es, hes, hmin⟩ := Finset.exists_min_image _ (codeP (t := t)) hne
  have hes' : ∀ e', sc e' ≤ sc es := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hes
  refine ⟨es, hes', ?_⟩
  intro e
  constructor
  · rintro ⟨h1, h2⟩
    have h3 : codeP es ≤ codeP e := hmin e (by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h1)
    have h4 : ¬ codeP es < codeP e := fun hlt => h2 es hlt hes'
    exact codeP_inj (le_antisymm (not_lt.mp h4) h3)
  · rintro rfl
    refine ⟨hes', ?_⟩
    intro e' hlt hmax
    have := hmin e' (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hmax)
    omega

theorem rho_eq {n t d : ℕ} (x : List Bool) (s : St n) (batch : Fin d → Fin t → Bool)
    (Pb Qb : Fin d → List ℕ) (B : Pr t → List ℕ) (mu stp : ℕ) (i : Fin d) (sel : ℕ → Pr t)
    (q : Fin d → ℤ) (hq : (cntB x s (Pb i) : ℤ) - (cntB x s (Qb i) : ℤ) = q i)
    (hB : ∀ e, cntB x s (B e) = cntOf sel stp e) :
    (cntB x s (posBag batch Pb B mu stp i) : ℤ) - (cntB x s (negBag batch Qb B mu stp i) : ℤ) =
      resid batch q mu sel stp i := by
  have h1 : ∀ e : Pr t,
      ((cntB x s (if chi (batch i) e = 1 then [] else B e) : ℕ) : ℤ) -
        ((cntB x s (if chi (batch i) e = 1 then B e else []) : ℕ) : ℤ) =
        - (chi (batch i) e * (cntOf sel stp e : ℤ)) := by
    intro e
    by_cases hc : chi (batch i) e = 1
    · rw [if_pos hc, if_pos hc, hc, cntB_nil, hB]
      simp
    · have hc' : chi (batch i) e = -1 := by
        unfold chi at hc ⊢
        split_ifs at hc ⊢ with h
        · exact absurd rfl hc
        · rfl
      rw [if_neg hc, if_neg hc, hc', cntB_nil, hB]
      simp
  have h2 : (∑ e : Pr t, ((cntB x s (if chi (batch i) e = 1 then [] else B e) : ℕ) : ℤ)) -
      (∑ e : Pr t, ((cntB x s (if chi (batch i) e = 1 then B e else []) : ℕ) : ℤ)) =
      - ∑ e : Pr t, chi (batch i) e * (cntOf sel stp e : ℤ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun e _ => h1 e)
  unfold posBag negBag resid
  rw [cntB_append, cntB_append, cntB_repflat, cntB_repflat, cntB_repflat, cntB_repflat,
    cntB_flatMap_univ, cntB_flatMap_univ]
  push_cast
  linear_combination (stp : ℤ) * hq + (mu : ℤ) * h2

theorem ubag_cnt {n t d : ℕ} (x : List Bool) (s : St n) (batch : Fin d → Fin t → Bool)
    (u nu : Fin d → List ℕ) (stp : ℕ) (c : Fin d → ℤ) (e : Pr t)
    (hu : ∀ i, ((cntB x s (u i) : ℕ) : ℤ) = c i + (stp : ℤ))
    (hnu : ∀ i, cntB x s (nu i) = 2 * stp - cntB x s (u i))
    (hle : ∀ i, cntB x s (u i) ≤ 2 * stp) :
    ((cntB x s (ubag batch u nu e) : ℕ) : ℤ) =
      (∑ i : Fin d, c i * chi (batch i) e) + (d : ℤ) * (stp : ℤ) := by
  unfold ubag
  rw [cntB_flatMap_univ]
  push_cast
  have h1 : ∀ i : Fin d, ((cntB x s (if chi (batch i) e = 1 then u i else nu i) : ℕ) : ℤ) =
      c i * chi (batch i) e + (stp : ℤ) := by
    intro i
    by_cases hc : chi (batch i) e = 1
    · rw [if_pos hc, hc, hu i]
      ring
    · have hc' : chi (batch i) e = -1 := by
        unfold chi at hc ⊢
        split_ifs at hc ⊢ with h
        · exact absurd rfl hc
        · rfl
      rw [if_neg hc, hc', hnu i]
      have := hu i
      have := hle i
      push_cast [Nat.cast_sub (hle i)]
      linarith
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
  simp

-- ---------- one conditional gradient step and its invariant ----------

noncomputable def stAll {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) : (Pr t → ℕ) × St n :=
  let ru := stU batch Pb Qb B mu stp s
  let rn := stN ru.1 ru.2
  let ri := stI (ubag batch ru.1 rn.1) rn.2
  let rx := stX ri.1 ri.2
  stS ri.1 rx.1 rx.2

noncomputable def iterStep {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (mu stp : ℕ) (s : St n) (B : Pr t → List ℕ) : (Pr t → List ℕ) × St n :=
  (fun e => B e ++ [(stAll batch Pb Qb B mu stp s).1 e], (stAll batch Pb Qb B mu stp s).2)

def Inv {n t d : ℕ} (x : List Bool) (batch : Fin d → Fin t → Bool) (q : Fin d → ℤ) (mu stp : ℕ)
    (s : St n) (B : Pr t → List ℕ) : Prop :=
  (∀ e, (B e).length = stp ∧ Valid s (B e)) ∧
  ∃ sel : ℕ → Pr t, (∀ e, cntB x s (B e) = cntOf sel stp e) ∧
    ∀ j, j < stp → ∀ e, score batch q mu sel j e ≤ score batch q mu sel j (sel j)

theorem stAll_spec {n t d : ℕ} {x : List Bool} (hb : Base n x) [Nonempty (Pr t)]
    (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ) (q : Fin d → ℤ) (mu stp : ℕ)
    (s : St n) (B : Pr t → List ℕ) (sel : ℕ → Pr t)
    (hP : ∀ i, Valid s (Pb i)) (hQ : ∀ i, Valid s (Qb i))
    (hq : ∀ i, (cntB x s (Pb i) : ℤ) - (cntB x s (Qb i) : ℤ) = q i)
    (hB : ∀ e, Valid s (B e)) (hcnt : ∀ e, cntB x s (B e) = cntOf sel stp e) :
    s.le (stAll batch Pb Qb B mu stp s).2 ∧
      ∃ es : Pr t, (∀ e', score batch q mu sel stp e' ≤ score batch q mu sel stp es) ∧
        ∀ e, Has x (stAll batch Pb Qb B mu stp s).2 ((stAll batch Pb Qb B mu stp s).1 e)
          (decide (e = es)) := by
  have hpos : ∀ i, Valid s (posBag batch Pb B mu stp i) := fun i =>
    Valid_append (Valid_repflat _ (hP i)) (Valid_repflat _ (Valid_flatMap _ _ (fun e _ => by
      split_ifs
      · intro a ha
        simp at ha
      · exact hB e)))
  have hneg : ∀ i, Valid s (negBag batch Qb B mu stp i) := fun i =>
    Valid_append (Valid_repflat _ (hQ i)) (Valid_repflat _ (Valid_flatMap _ _ (fun e _ => by
      split_ifs
      · exact hB e
      · intro a ha
        simp at ha)))
  have hU := stU_spec hb batch Pb Qb B mu stp s hpos hneg
  have hrho : ∀ i, (cntB x s (posBag batch Pb B mu stp i) : ℤ) -
      (cntB x s (negBag batch Qb B mu stp i) : ℤ) = resid batch q mu sel stp i :=
    fun i => rho_eq x s batch Pb Qb B mu stp i sel q (hq i) hcnt
  have hN := stN_spec hb (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2
    (fun i => (hU.2 i).2.1)
  have hu : ∀ i, ((cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
      ((stU batch Pb Qb B mu stp s).1 i) : ℕ) : ℤ) =
      clampZ (resid batch q mu sel stp i) stp + (stp : ℤ) := by
    intro i
    rw [cntB_mono hb (hU.2 i).2.1 hN.1, (hU.2 i).2.2, hrho i]
  have hle : ∀ i, cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
      ((stU batch Pb Qb B mu stp s).1 i) ≤ 2 * stp := by
    intro i
    have := cntB_le x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
      ((stU batch Pb Qb B mu stp s).1 i)
    rw [(hU.2 i).1] at this
    exact this
  have hnu : ∀ i, cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
      ((stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1 i) =
      2 * stp - cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
        ((stU batch Pb Qb B mu stp s).1 i) := by
    intro i
    rw [(hN.2 i).2, (hU.2 i).1, cntB_mono hb (hU.2 i).2.1 hN.1]
  have hUc : ∀ e, ((cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
      (ubag batch (stU batch Pb Qb B mu stp s).1
        (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1 e) : ℕ) : ℤ) =
      score batch q mu sel stp e + (d : ℤ) * (stp : ℤ) := fun e =>
    ubag_cnt x _ batch _ _ stp (fun i => clampZ (resid batch q mu sel stp i) stp) e hu hnu hle
  have hUv : ∀ e, Valid (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
      (ubag batch (stU batch Pb Qb B mu stp s).1
        (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1 e) := fun e =>
    Valid_flatMap _ _ (fun i _ => by
      split_ifs
      · exact (hU.2 i).2.1.mono hN.1
      · exact (hN.2 i).1)
  have hI := stI_spec hb _ _ hUv
  have hI' : ∀ e, Has x (stI (ubag batch (stU batch Pb Qb B mu stp s).1
        (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
        (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).2
      ((stI (ubag batch (stU batch Pb Qb B mu stp s).1
        (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
        (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).1 e)
      (decide (∀ e', score batch q mu sel stp e' ≤ score batch q mu sel stp e)) := by
    intro e
    have h := hI.2 e
    have hd : decide (∀ e', cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
        (ubag batch (stU batch Pb Qb B mu stp s).1
          (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1 e') ≤
        cntB x (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2
        (ubag batch (stU batch Pb Qb B mu stp s).1
          (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1 e)) =
        decide (∀ e', score batch q mu sel stp e' ≤ score batch q mu sel stp e) := by
      apply decide_eq_decide.mpr
      apply forall_congr'
      intro e'
      rw [← Int.ofNat_le, hUc e', hUc e]
      constructor <;> intro h <;> linarith
    rw [hd] at h
    exact h
  have hX := stX_spec hb _ _ _ hI'
  have hS := stS_spec hb _ _ _ _ (fun e => (hI' e).mono hb hX.1) hX.2
  obtain ⟨es, hes, huniq⟩ := exists_estar (fun e => score batch q mu sel stp e)
  refine ⟨St.le_trans hU.1 (St.le_trans hN.1 (St.le_trans hI.1 (St.le_trans hX.1 hS.1))),
    es, hes, ?_⟩
  intro e
  have h := hS.2 e
  have hd : decide (decide (∀ e', score batch q mu sel stp e' ≤ score batch q mu sel stp e) = true ∧
      ∀ e', codeP e' < codeP e →
        decide (∀ e'', score batch q mu sel stp e'' ≤ score batch q mu sel stp e') = false) =
      decide (e = es) := by
    apply decide_eq_decide.mpr
    rw [← huniq e]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  rw [hd] at h
  exact h

theorem iterStep_le {n t d : ℕ} {x : List Bool} (hb : Base n x) [Nonempty (Pr t)]
    (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ) (q : Fin d → ℤ) (mu stp : ℕ)
    (s : St n) (B : Pr t → List ℕ)
    (hP : ∀ i, Valid s (Pb i)) (hQ : ∀ i, Valid s (Qb i))
    (hq : ∀ i, (cntB x s (Pb i) : ℤ) - (cntB x s (Qb i) : ℤ) = q i)
    (hinv : Inv x batch q mu stp s B) :
    s.le (iterStep batch Pb Qb mu stp s B).2 ∧
      Inv x batch q mu (stp + 1) (iterStep batch Pb Qb mu stp s B).2
        (iterStep batch Pb Qb mu stp s B).1 := by
  obtain ⟨hB, sel, hcnt, hmax⟩ := hinv
  obtain ⟨hle, es, hes, hsel⟩ := stAll_spec hb batch Pb Qb q mu stp s B sel hP hQ hq
    (fun e => (hB e).2) hcnt
  refine ⟨hle, ?_, fun j => if j = stp then es else sel j, ?_, ?_⟩
  · intro e
    refine ⟨?_, ?_⟩
    · show (B e ++ [_]).length = stp + 1
      rw [List.length_append, (hB e).1]
      rfl
    · show Valid (stAll batch Pb Qb B mu stp s).2 (B e ++ [(stAll batch Pb Qb B mu stp s).1 e])
      apply Valid_append ((hB e).2.mono hle)
      intro a ha
      rw [List.mem_singleton] at ha
      rw [ha]
      exact (hsel e).1
  · intro e
    show cntB x (stAll batch Pb Qb B mu stp s).2 (B e ++ [(stAll batch Pb Qb B mu stp s).1 e]) = _
    rw [cntB_append, cntB_mono hb (hB e).2 hle, hcnt e, cntB_cons, cntB_nil, (hsel e).2,
      cntOf_succ, cntOf_congr (fun j => if j = stp then es else sel j) sel stp
        (fun j hj => by rw [if_neg (Nat.ne_of_lt hj)])]
    simp only [if_true, zero_add]
    by_cases he : e = es
    · subst he
      simp
    · have he' : ¬ es = e := fun h => he h.symm
      simp [he, he']
  · intro j hj e
    have hagree : ∀ i, i < j → (fun j => if j = stp then es else sel j) i = sel i := by
      intro i hi
      show (if i = stp then es else sel i) = sel i
      rw [if_neg (by omega)]
    rw [score_congr batch q mu _ sel j hagree e, score_congr batch q mu _ sel j hagree _]
    by_cases hjs : j = stp
    · subst hjs
      simp only [if_true]
      exact hes e
    · simp only [if_neg hjs]
      exact hmax j (by omega) e

noncomputable def iter {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (mu : ℕ) (s : St n) : ℕ → (Pr t → List ℕ) × St n
  | 0 => (fun _ => [], s)
  | j + 1 => iterStep batch Pb Qb mu j (iter batch Pb Qb mu s j).2 (iter batch Pb Qb mu s j).1

theorem iter_spec {n t d : ℕ} {x : List Bool} (hb : Base n x) [Nonempty (Pr t)]
    (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ) (q : Fin d → ℤ) (mu : ℕ)
    (s : St n) (hP : ∀ i, Valid s (Pb i)) (hQ : ∀ i, Valid s (Qb i))
    (hq : ∀ i, (cntB x s (Pb i) : ℤ) - (cntB x s (Qb i) : ℤ) = q i) :
    ∀ j, s.le (iter batch Pb Qb mu s j).2 ∧
      Inv x batch q mu j (iter batch Pb Qb mu s j).2 (iter batch Pb Qb mu s j).1 := by
  intro j
  induction j with
  | zero =>
    refine ⟨St.le_refl s, ?_, fun _ => Classical.arbitrary _, ?_, ?_⟩
    · intro e
      refine ⟨rfl, ?_⟩
      intro a ha
      simp [iter] at ha
    · intro e
      show cntB x s [] = _
      simp [cntB_nil, cntOf]
    · intro j hj
      omega
  | succ j ih =>
    obtain ⟨ile, iinv⟩ := ih
    have h := iterStep_le hb batch Pb Qb q mu j (iter batch Pb Qb mu s j).2
      (iter batch Pb Qb mu s j).1 (fun i => (hP i).mono ile) (fun i => (hQ i).mono ile)
      (fun i => by rw [cntB_mono hb (hP i) ile, cntB_mono hb (hQ i) ile]; exact hq i) iinv
    exact ⟨St.le_trans ile h.1, h.2⟩

-- the decoder for a fixed mass mu: run S steps, then round at one half
noncomputable def decMu {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (S mu : ℕ) (s : St n) : (Pr t → ℕ) × St n :=
  forG (fun s' e => (pick (gCount s'
      (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten).1 S,
    (gCount s' (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten).2)) 0
    (iter batch Pb Qb mu s S).2 (pairsL t)

theorem stU_le' {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) : s.le (stU batch Pb Qb B mu stp s).2 := by
  unfold stU
  exact forG_le _ _ (fun s i => uStep_le _ _ _ s) _ _

theorem stN_le' {n d : ℕ} (u : Fin d → List ℕ) (s : St n) : s.le (stN u s).2 := by
  unfold stN
  exact forG_le _ _ (fun s i => gNotL_le s _) _ _

theorem stI_le' {n t : ℕ} (U : Pr t → List ℕ) (s : St n) : s.le (stI U s).2 := by
  unfold stI
  exact forG_le _ _ (fun s e => gAllG_le _ (fun s e' => gGe_le s _ _) s _) _ _

theorem stX_le' {n t : ℕ} (isw : Pr t → ℕ) (s : St n) : s.le (stX isw s).2 := by
  unfold stX
  exact forG_le _ _ (fun s e => gNot_le s _) _ _

theorem stS_le' {n t : ℕ} (isw nisw : Pr t → ℕ) (s : St n) : s.le (stS isw nisw s).2 := by
  unfold stS
  exact forG_le _ _ (fun s e => gAndL_le s _) _ _

theorem stAll_le' {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) : s.le (stAll batch Pb Qb B mu stp s).2 :=
  St.le_trans (stU_le' batch Pb Qb B mu stp s) (St.le_trans (stN_le' _ _)
    (St.le_trans (stI_le' _ _) (St.le_trans (stX_le' _ _) (stS_le' _ _ _))))

theorem iter_le' {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (mu : ℕ) (s : St n) : ∀ j, s.le (iter (t := t) batch Pb Qb mu s j).2 := by
  intro j
  induction j with
  | zero => exact St.le_refl s
  | succ j ih => exact St.le_trans ih (stAll_le' batch Pb Qb _ mu j _)

theorem decMu_le' {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (S mu : ℕ) (s : St n) : s.le (decMu (t := t) batch Pb Qb S mu s).2 :=
  St.le_trans (iter_le' batch Pb Qb mu s S)
    (forG_le (fun s' e => (pick (gCount s'
      (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten).1 S,
    (gCount s' (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten).2)) 0
      (fun s' e => gCount_le s' _) _ _)

theorem decMu_spec {n t d : ℕ} {x : List Bool} (hb : Base n x) [Nonempty (Pr t)]
    (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ) (q : Fin d → ℤ) (S mu : ℕ)
    (s : St n) (hP : ∀ i, Valid s (Pb i)) (hQ : ∀ i, Valid s (Qb i))
    (hq : ∀ i, (cntB x s (Pb i) : ℤ) - (cntB x s (Qb i) : ℤ) = q i) :
    ∃ sel : ℕ → Pr t,
      (∀ j, j < S → ∀ e, score batch q mu sel j e ≤ score batch q mu sel j (sel j)) ∧
      ∀ e, Has x (decMu batch Pb Qb S mu s).2 ((decMu batch Pb Qb S mu s).1 e)
        (decide (S ≤ 2 * mu * cntOf sel S e)) := by
  obtain ⟨ile, hB, sel, hcnt, hmax⟩ := iter_spec hb batch Pb Qb q mu s hP hQ hq S
  refine ⟨sel, hmax, ?_⟩
  have key := forG_spec (fun s' e => (pick (gCount s'
      (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten).1 S,
    (gCount s' (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten).2)) 0
    (fun e w s' => Has x s' w (decide (S ≤ 2 * mu * cntOf sel S e)))
    (fun e w s1 s2 h hle => h.mono hb hle)
    (fun s' e => gCount_le s' _) (pairsL t) (iter batch Pb Qb mu s S).2 (by
      intro s' hs' e _
      have hv : Valid s' (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten :=
        Valid_repflat _ ((hB e).2.mono hs')
      obtain ⟨_, _, hth⟩ := gCount_spec hb _ s' hv
      have h := hth S
      rw [cntB_repflat, cntB_mono hb (hB e).2 hs', hcnt e] at h
      exact h)
  exact fun e => key.2 e (mem_pairsL e)
-- ===================== front end: reading the legal values =====================

def Wof (t k : ℕ) : ℕ := k*(t+2)+1

theorem flat_getD (W : ℕ) : ∀ (d : ℕ) (f : Fin d → Fin W → Bool) (i : Fin d) (j : Fin W),
    ((List.ofFn (fun i : Fin d => List.ofFn (fun j : Fin W => f i j))).flatten).getD
      (i.val * W + j.val) false = f i j := by
  intro d
  induction d with
  | zero => intro f i; exact i.elim0
  | succ d ih =>
    intro f i j
    rw [List.ofFn_succ, List.flatten_cons]
    have hlen : (List.ofFn (fun j : Fin W => f 0 j)).length = W := List.length_ofFn
    cases i using Fin.cases with
    | zero =>
      have hj : j.val < (List.ofFn (fun j : Fin W => f 0 j)).length := by rw [hlen]; exact j.isLt
      simp only [Fin.val_zero, zero_mul, zero_add]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
      simp
    | succ i =>
      have hidx : i.succ.val * W + j.val =
          (List.ofFn (fun j : Fin W => f 0 j)).length + (i.val * W + j.val) := by
        rw [hlen, Fin.val_succ]
        ring
      rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
      exact ih (fun i => f i.succ) i j

theorem flat_length (W : ℕ) : ∀ (d : ℕ) (f : Fin d → Fin W → Bool),
    ((List.ofFn (fun i : Fin d => List.ofFn (fun j : Fin W => f i j))).flatten).length = d * W := by
  intro d
  induction d with
  | zero => intro f; simp
  | succ d ih =>
    intro f
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      ih (fun i => f i.succ)]
    ring

theorem bits_all (a b W : ℕ) :
    (List.range W).all (fun j => decide (a.testBit j = b.testBit j)) =
      decide (a % 2 ^ W = b % 2 ^ W) := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < W
    · simp [hj, h j hj]
    · simp [hj]
  · intro h j hj
    have h1 : (a % 2 ^ W).testBit j = (b % 2 ^ W).testBit j := by rw [h]
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow] at h1
    simpa [hj] using h1

def litF {n : ℕ} (base v : ℕ) (s : St n) (j : ℕ) : ℕ × St n :=
  if v.testBit j then (base + j, s) else gNot s (base + j)

theorem litF_le {n : ℕ} (base v : ℕ) (s : St n) (j : ℕ) : s.le (litF base v s j).2 := by
  unfold litF
  split_ifs
  · exact St.le_refl s
  · exact gNot_le s _

def gEq {n : ℕ} (base v W : ℕ) (s : St n) : ℕ × St n := gAllG (litF base v) s (List.range W)

theorem gEq_le {n : ℕ} (base v W : ℕ) (s : St n) : s.le (gEq base v W s).2 :=
  gAllG_le _ (litF_le base v) s _

theorem gEq_spec {n : ℕ} {x : List Bool} (hb : Base n x) (base v W yv : ℕ) (s : St n)
    (hin : ∀ j, j < W → base + j < n ∧ x.getD (base + j) false = yv.testBit j) :
    Has x (gEq base v W s).2 (gEq base v W s).1 (decide (yv % 2 ^ W = v % 2 ^ W)) := by
  have h := (gAllG_spec hb (litF base v) (fun j => decide (yv.testBit j = v.testBit j))
    (litF_le base v) (List.range W) s (by
      intro s' _ j hj
      obtain ⟨h1, h2⟩ := hin j (List.mem_range.mp hj)
      have hw : Has x s' (base + j) (yv.testBit j) := by
        refine ⟨by omega, ?_⟩
        rw [vl_input x s'.gs (by rw [hb.len]; exact h1), h2]
      unfold litF
      by_cases hv : v.testBit j = true
      · rw [if_pos hv, hv]
        have : decide (yv.testBit j = true) = yv.testBit j := by cases yv.testBit j <;> rfl
        rw [this]
        exact hw
      · rw [if_neg hv]
        have hv' : v.testBit j = false := by simpa using hv
        rw [hv']
        have : decide (yv.testBit j = false) = !yv.testBit j := by cases yv.testBit j <;> rfl
        rw [this]
        exact gNot_spec hb hw)).2
  rw [bits_all] at h
  exact h

def legalS (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (k+1) ×ˢ Finset.range (k+1)).filter (fun p => p.2 ≤ p.1)

theorem mem_legalS {k : ℕ} {a : ℕ × ℕ} : a ∈ legalS k ↔ a.1 ≤ k ∧ a.2 ≤ a.1 := by
  unfold legalS
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem cntB_flatMap_toList {n : ℕ} {α : Type} (x : List Bool) (s : St n) (S : Finset α)
    (g : α → List ℕ) : cntB x s (S.toList.flatMap g) = ∑ a ∈ S, cntB x s (g a) := by
  rw [cntB_flatMap, Finset.sum_map_toList]

theorem cntB_map_toList {n : ℕ} {α : Type} (x : List Bool) (s : St n) (S : Finset α)
    (w : α → ℕ) : cntB x s (S.toList.map w) = ∑ c ∈ S, (vl x s.gs (w c)).toNat := by
  have h : ∀ l : List α, cntB x s (l.map w) = (l.map (fun c => (vl x s.gs (w c)).toNat)).sum := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, cntB_cons, ih, List.map_cons, List.sum_cons]
      ring
  rw [h, Finset.sum_map_toList]

theorem sum_one_hot_le {α : Type} (S : Finset α) (E : α → Bool) (w : α → ℕ) (K : ℕ)
    (huniq : ∀ a ∈ S, ∀ b ∈ S, E a = true → E b = true → a = b) (hw : ∀ a ∈ S, w a ≤ K) :
    ∑ a ∈ S, w a * (E a).toNat ≤ K := by
  classical
  by_cases h : ∃ a0 ∈ S, E a0 = true
  · obtain ⟨a0, ha0, hE0⟩ := h
    rw [Finset.sum_eq_single a0]
    · rw [hE0]
      simpa using hw a0 ha0
    · intro b hbS hne
      have : E b = false := by
        by_contra hc
        exact hne (huniq b hbS a0 ha0 (by simpa using hc) hE0)
      rw [this]
      simp
    · intro hna
      exact absurd ha0 hna
  · have : ∀ a ∈ S, w a * (E a).toNat = 0 := by
      intro a ha
      have : E a = false := by
        by_contra hc
        exact h ⟨a, ha, by simpa using hc⟩
      rw [this]
      simp
    rw [Finset.sum_eq_zero this]
    exact Nat.zero_le _

theorem sum_one_hot_eq {α : Type} [DecidableEq α] (S : Finset α) (E : α → Bool) (w : α → ℕ)
    (a0 : α) (ha0 : a0 ∈ S) (hE : ∀ a ∈ S, E a = decide (a = a0)) :
    ∑ a ∈ S, w a * (E a).toNat = w a0 := by
  rw [Finset.sum_eq_single a0]
  · rw [hE a0 ha0]
    simp
  · intro b hbS hne
    rw [hE b hbS]
    simp [hne]
  · intro hna
    exact absurd ha0 hna

noncomputable def PbOf {d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (i : Fin d) : List ℕ :=
  (legalS k).toList.flatMap (fun a => List.replicate (a.1 - a.2) (eqw (i, a)))

noncomputable def QbOf {d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (i : Fin d) : List ℕ :=
  (legalS k).toList.flatMap (fun a => List.replicate a.2 (eqw (i, a)))

noncomputable def VbOf {d : ℕ} (eqw : Fin d × ℕ × ℕ → ℕ) (mu : ℕ) : List ℕ :=
  (Finset.univ : Finset (Fin d)).toList.flatMap
    (fun i => (Finset.range (mu+1)).toList.map (fun c => eqw (i, mu, c)))

theorem PbOf_cnt {n d : ℕ} (x : List Bool) (s : St n) (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ)
    (i : Fin d) : cntB x s (PbOf k eqw i) =
      ∑ a ∈ legalS k, (a.1 - a.2) * (vl x s.gs (eqw (i, a))).toNat := by
  unfold PbOf
  rw [cntB_flatMap_toList]
  exact Finset.sum_congr rfl (fun a _ => cntB_replicate x s _ _)

theorem QbOf_cnt {n d : ℕ} (x : List Bool) (s : St n) (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ)
    (i : Fin d) : cntB x s (QbOf k eqw i) =
      ∑ a ∈ legalS k, a.2 * (vl x s.gs (eqw (i, a))).toNat := by
  unfold QbOf
  rw [cntB_flatMap_toList]
  exact Finset.sum_congr rfl (fun a _ => cntB_replicate x s _ _)

theorem VbOf_cnt {n d : ℕ} (x : List Bool) (s : St n) (eqw : Fin d × ℕ × ℕ → ℕ) (mu : ℕ) :
    cntB x s (VbOf eqw mu) =
      ∑ i : Fin d, ∑ c ∈ Finset.range (mu+1), (vl x s.gs (eqw (i, mu, c))).toNat := by
  unfold VbOf
  rw [cntB_flatMap_toList]
  exact Finset.sum_congr rfl (fun i _ => cntB_map_toList x s _ _)

theorem PbOf_valid {n d : ℕ} {s : St n} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (i : Fin d)
    (h : ∀ a, a ∈ legalS k → eqw (i, a) < n + s.gs.length) : Valid s (PbOf k eqw i) :=
  Valid_flatMap _ _ (fun a ha => Valid_replicate _ (h a (Finset.mem_toList.mp ha)))

theorem QbOf_valid {n d : ℕ} {s : St n} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (i : Fin d)
    (h : ∀ a, a ∈ legalS k → eqw (i, a) < n + s.gs.length) : Valid s (QbOf k eqw i) :=
  Valid_flatMap _ _ (fun a ha => Valid_replicate _ (h a (Finset.mem_toList.mp ha)))

theorem VbOf_valid {n d : ℕ} {s : St n} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (mu : ℕ) (hmu : mu ≤ k)
    (h : ∀ (i : Fin d) a, a ∈ legalS k → eqw (i, a) < n + s.gs.length) : Valid s (VbOf eqw mu) :=
  Valid_flatMap _ _ (fun i _ => by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    have hc' := Finset.mem_range.mp (Finset.mem_toList.mp hc)
    exact h i (mu, c) (mem_legalS.mpr ⟨hmu, by simp only; omega⟩))
-- ===================== the four tables of the decoder =====================

noncomputable def eqTab (t k d : ℕ) (s : St (2 + d * Wof t k)) :
    (Fin d × ℕ × ℕ → ℕ) × St (2 + d * Wof t k) :=
  forG (fun s a => gEq (2 + a.1.val * Wof t k) (val t k a.2.1 a.2.2) (Wof t k) s) 0 s
    ((Finset.univ ×ˢ legalS k : Finset (Fin d × ℕ × ℕ)).toList)

theorem eqTab_spec {t k d : ℕ} {x : List Bool} (hb : Base (2 + d * Wof t k) x) (y : Fin d → ℕ)
    (hin : ∀ (i : Fin d) (j : ℕ), j < Wof t k →
      x.getD (2 + i.val * Wof t k + j) false = (y i).testBit j)
    (s : St (2 + d * Wof t k)) :
    s.le (eqTab t k d s).2 ∧ ∀ (i : Fin d) (a : ℕ × ℕ), a ∈ legalS k →
      Has x (eqTab t k d s).2 ((eqTab t k d s).1 (i, a))
        (decide (y i % 2 ^ Wof t k = val t k a.1 a.2 % 2 ^ Wof t k)) := by
  have key := forG_spec
    (fun s (a : Fin d × ℕ × ℕ) => gEq (2 + a.1.val * Wof t k) (val t k a.2.1 a.2.2) (Wof t k) s) 0
    (fun (p : Fin d × ℕ × ℕ) w s' => Has x s' w
      (decide (y p.1 % 2 ^ Wof t k = val t k p.2.1 p.2.2 % 2 ^ Wof t k)))
    (fun p w s1 s2 h hle => h.mono hb hle)
    (fun s a => gEq_le _ _ _ s) ((Finset.univ ×ˢ legalS k : Finset (Fin d × ℕ × ℕ)).toList) s (by
      intro s' _ p _
      apply gEq_spec hb
      intro j hj
      refine ⟨?_, by rw [Nat.add_assoc]; rw [← Nat.add_assoc]; exact hin p.1 j hj⟩
      have h1 : (p.1.val + 1) * Wof t k ≤ d * Wof t k := Nat.mul_le_mul_right _ p.1.isLt
      have h2 : (p.1.val + 1) * Wof t k = p.1.val * Wof t k + Wof t k := by ring
      omega)
  refine ⟨key.1, fun i a ha => key.2 (i, a) ?_⟩
  rw [Finset.mem_toList, Finset.mem_product]
  exact ⟨Finset.mem_univ _, ha⟩

noncomputable def majTab {n d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (s : St n) :
    (ℕ → ℕ) × St n :=
  forG (fun s mu => (pick (gCount s (VbOf eqw mu)).1 (d / 2 + 1), (gCount s (VbOf eqw mu)).2)) 0 s
    (Finset.range (k+1)).toList

theorem majTab_le {n d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (s : St n) :
    s.le (majTab k eqw s).2 := by
  unfold majTab
  exact forG_le (fun s mu => (pick (gCount s (VbOf eqw mu)).1 (d / 2 + 1),
    (gCount s (VbOf eqw mu)).2)) 0 (fun s mu => gCount_le s _) _ _

theorem majTab_spec {n d : ℕ} {x : List Bool} (hb : Base n x) (k : ℕ)
    (eqw : Fin d × ℕ × ℕ → ℕ) (s : St n) (hV : ∀ mu, mu ≤ k → Valid s (VbOf eqw mu)) :
    ∀ mu, mu ≤ k → Has x (majTab k eqw s).2 ((majTab k eqw s).1 mu)
      (decide (d / 2 + 1 ≤ cntB x s (VbOf eqw mu))) := by
  have key := forG_spec
    (fun s mu => (pick (gCount s (VbOf eqw mu)).1 (d / 2 + 1), (gCount s (VbOf eqw mu)).2)) 0
    (fun mu w s' => Has x s' w (decide (d / 2 + 1 ≤ cntB x s (VbOf eqw mu))))
    (fun p w s1 s2 h hle => h.mono hb hle)
    (fun s mu => gCount_le s _) (Finset.range (k+1)).toList s (by
      intro s' hs' mu hmu
      have hmu' : mu ≤ k := by
        have := Finset.mem_range.mp (Finset.mem_toList.mp hmu)
        omega
      obtain ⟨_, _, hth⟩ := gCount_spec hb (VbOf eqw mu) s' ((hV mu hmu').mono hs')
      have h := hth (d / 2 + 1)
      rw [cntB_mono hb (hV mu hmu') hs'] at h
      exact h)
  intro mu hmu
  exact key.2 mu (by rw [Finset.mem_toList, Finset.mem_range]; omega)

noncomputable def decTab {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (k : ℕ) (s : St n) : (ℕ → Pr t → ℕ) × St n :=
  forG (fun s mu => decMu batch Pb Qb (Sbig k) mu s) (fun _ => 0) s (Finset.range (k+1)).toList

theorem decTab_le {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (k : ℕ) (s : St n) : s.le (decTab (t := t) batch Pb Qb k s).2 := by
  unfold decTab
  exact forG_le _ _ (fun s mu => decMu_le' batch Pb Qb _ mu s) _ _

theorem decTab_spec {n t d : ℕ} {x : List Bool} (hb : Base n x) [Nonempty (Pr t)]
    (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ) (q : Fin d → ℤ) (k : ℕ)
    (s : St n) (hP : ∀ i, Valid s (Pb i)) (hQ : ∀ i, Valid s (Qb i))
    (hq : ∀ i, (cntB x s (Pb i) : ℤ) - (cntB x s (Qb i) : ℤ) = q i) :
    ∀ mu, mu ≤ k → ∃ sel : ℕ → Pr t,
      (∀ j, j < Sbig k → ∀ e, score batch q mu sel j e ≤ score batch q mu sel j (sel j)) ∧
      ∀ e, Has x (decTab batch Pb Qb k s).2 ((decTab batch Pb Qb k s).1 mu e)
        (decide (Sbig k ≤ 2 * mu * cntOf sel (Sbig k) e)) := by
  have key := forG_spec (fun s mu => decMu (t := t) batch Pb Qb (Sbig k) mu s) (fun _ => 0)
    (fun mu o s' => ∃ sel : ℕ → Pr t,
      (∀ j, j < Sbig k → ∀ e, score batch q mu sel j e ≤ score batch q mu sel j (sel j)) ∧
      ∀ e, Has x s' (o e) (decide (Sbig k ≤ 2 * mu * cntOf sel (Sbig k) e)))
    (by
      rintro mu o s1 s2 ⟨sel, h1, h2⟩ hle
      exact ⟨sel, h1, fun e => (h2 e).mono hb hle⟩)
    (fun s mu => decMu_le' batch Pb Qb _ mu s) (Finset.range (k+1)).toList s (by
      intro s' hs' mu _
      exact decMu_spec hb batch Pb Qb q (Sbig k) mu s' (fun i => (hP i).mono hs')
        (fun i => (hQ i).mono hs')
        (fun i => by rw [cntB_mono hb (hP i) hs', cntB_mono hb (hQ i) hs']; exact hq i))
  intro mu hmu
  exact key.2 mu (by rw [Finset.mem_toList, Finset.mem_range]; omega)

noncomputable def muxTab {n t : ℕ} (k : ℕ) (Mw : ℕ → ℕ) (ow : ℕ → Pr t → ℕ) (s : St n) :
    (Pr t → ℕ) × St n :=
  forG (fun s e => gAnyG (fun s mu => gAnd s (Mw mu) (ow mu e)) s (Finset.range (k+1)).toList) 0 s
    (pairsL t)

theorem muxTab_le {n t : ℕ} (k : ℕ) (Mw : ℕ → ℕ) (ow : ℕ → Pr t → ℕ) (s : St n) :
    s.le (muxTab k Mw ow s).2 := by
  unfold muxTab
  exact forG_le _ _ (fun s e => gAnyG_le _ (fun s mu => gAnd_le s _ _) s _) _ _

theorem muxTab_spec {n t : ℕ} {x : List Bool} (hb : Base n x) (k m : ℕ) (hm : m ≤ k)
    (Mw : ℕ → ℕ) (ow : ℕ → Pr t → ℕ) (s : St n)
    (hM : ∀ mu, mu ≤ k → Has x s (Mw mu) (decide (mu = m)))
    (ho : ∀ mu, mu ≤ k → ∀ e, ow mu e < n + s.gs.length) :
    ∀ e, Has x (muxTab k Mw ow s).2 ((muxTab k Mw ow s).1 e) (vl x s.gs (ow m e)) := by
  have key := forG_spec
    (fun s e => gAnyG (fun s mu => gAnd s (Mw mu) (ow mu e)) s (Finset.range (k+1)).toList) 0
    (fun e w s' => Has x s' w (vl x s.gs (ow m e)))
    (fun p w s1 s2 h hle => h.mono hb hle)
    (fun s e => gAnyG_le _ (fun s mu => gAnd_le s _ _) s _) (pairsL t) s (by
      intro s' hs' e _
      have h := (gAnyG_spec hb (fun s mu => gAnd s (Mw mu) (ow mu e))
        (fun mu => decide (mu = m) && vl x s.gs (ow mu e))
        (fun s mu => gAnd_le s _ _) (Finset.range (k+1)).toList s' (by
          intro s2 hs2 mu hmu
          have hmu' : mu ≤ k := by
            have := Finset.mem_range.mp (Finset.mem_toList.mp hmu)
            omega
          exact gAnd_spec hb ((hM mu hmu').mono hb (St.le_trans hs' hs2))
            ((has_self (ho mu hmu' e)).mono hb (St.le_trans hs' hs2)))).2
      have hany : (Finset.range (k+1)).toList.any
          (fun mu => decide (mu = m) && vl x s.gs (ow mu e)) = vl x s.gs (ow m e) := by
        rw [Bool.eq_iff_iff]
        simp only [List.any_eq_true, Finset.mem_toList, Finset.mem_range, Bool.and_eq_true,
          decide_eq_true_eq]
        constructor
        · rintro ⟨mu, _, hmu2, hv⟩
          rw [← hmu2]
          exact hv
        · intro hv
          exact ⟨m, by omega, rfl, hv⟩
      rw [← hany]
      exact h)
  exact fun e => key.2 e (mem_pairsL e)

noncomputable def decAll (t k d : ℕ) (batch : Fin d → Fin t → Bool) (s : St (2 + d * Wof t k)) :
    (Pr t → ℕ) × St (2 + d * Wof t k) :=
  muxTab k (majTab k (eqTab t k d s).1 (eqTab t k d s).2).1
    (decTab batch (PbOf k (eqTab t k d s).1) (QbOf k (eqTab t k d s).1) k
      (majTab k (eqTab t k d s).1 (eqTab t k d s).2).2).1
    (decTab batch (PbOf k (eqTab t k d s).1) (QbOf k (eqTab t k d s).1) k
      (majTab k (eqTab t k d s).1 (eqTab t k d s).2).2).2
-- ===================== the decoder recovers the graph =====================

theorem pr_nonempty {t : ℕ} (ht : 2 ≤ t) : Nonempty (Pr t) :=
  ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp [Fin.lt_def]⟩⟩

theorem sum_ind_mem {d : ℕ} (Sb : Finset (Fin d)) :
    ∑ i : Fin d, (if i ∈ Sb then 1 else 0) = Sb.card := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one]

theorem sum_ind_not_mem {d : ℕ} (Sb : Finset (Fin d)) :
    ∑ i : Fin d, (if i ∈ Sb then 0 else 1) + Sb.card = d := by
  rw [← sum_ind_mem Sb, ← Finset.sum_add_distrib]
  have : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      ((if i ∈ Sb then 0 else 1) + (if i ∈ Sb then 1 else 0) : ℕ) = 1 := by
    intro i _
    split_ifs <;> rfl
  rw [Finset.sum_congr rfl this]
  simp

theorem decCore_spec {t k d : ℕ} (ht : 2 ≤ t) (hk : 0 < k) (hd : 0 < d)
    (batch : Fin d → Fin t → Bool)
    (hmargin : ∀ (v : Pr t → ℝ) (S : Finset (Fin d)),
      (∑ e : Pr t, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) →
      400 * S.card ≤ d →
      (d : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) +
        256 * (∑ i ∈ S, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|) ≤
        128 * (∑ i, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|))
    (G : Finset (Pr t)) (hG : G.card ≤ k) (y : Fin d → ℕ)
    (hy : 400 * (Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))).card ≤ d)
    {n : ℕ} (x : List Bool) (hb : Base n x) (eqw : Fin d × ℕ × ℕ → ℕ) (sE : St n)
    (hE : ∀ (i : Fin d) (a : ℕ × ℕ), a ∈ legalS k → Has x sE (eqw (i, a))
      (decide (y i % 2 ^ Wof t k = val t k a.1 a.2 % 2 ^ Wof t k))) :
    ∀ e, Has x
      (muxTab k (majTab k eqw sE).1
        (decTab batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2).1
        (decTab batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2).2).2
      ((muxTab k (majTab k eqw sE).1
        (decTab batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2).1
        (decTab batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2).2).1 e)
      (decide (e ∈ G)) := by
  haveI := pr_nonempty ht
  have hmod : ∀ a : ℕ × ℕ, a ∈ legalS k → val t k a.1 a.2 % 2 ^ Wof t k = val t k a.1 a.2 := by
    intro a ha
    have h := mem_legalS.mp ha
    exact Nat.mod_eq_of_lt (val_lt t k a.1 a.2 ht h.2 h.1)
  have hcm : ∀ i, cutc (batch i) G ≤ G.card := fun i => cutc_le (batch i) G
  have hml : ∀ i, (G.card, cutc (batch i) G) ∈ legalS k := fun i => mem_legalS.mpr ⟨hG, hcm i⟩
  have hgoodY : ∀ i, i ∉ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)) →
      y i = val t k G.card (cutc (batch i) G) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    rw [hi, readF_eq t k ht G hG]
  have huniq : ∀ i : Fin d, ∀ a ∈ legalS k, ∀ b ∈ legalS k,
      decide (y i % 2 ^ Wof t k = val t k a.1 a.2 % 2 ^ Wof t k) = true →
      decide (y i % 2 ^ Wof t k = val t k b.1 b.2 % 2 ^ Wof t k) = true → a = b := by
    intro i a ha b hb' h1 h2
    rw [decide_eq_true_eq, hmod a ha] at h1
    rw [decide_eq_true_eq, hmod b hb'] at h2
    have ha' := mem_legalS.mp ha
    have hb'' := mem_legalS.mp hb'
    obtain ⟨e1, e2⟩ := val_inj t k a.1 a.2 b.1 b.2 ht ha'.2 ha'.1 hb''.2 hb''.1 (h1.symm.trans h2)
    exact Prod.ext e1 e2
  have hgoodE : ∀ i, i ∉ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)) →
      ∀ a ∈ legalS k, decide (y i % 2 ^ Wof t k = val t k a.1 a.2 % 2 ^ Wof t k) =
        decide (a = (G.card, cutc (batch i) G)) := by
    intro i hi a ha
    apply decide_eq_decide.mpr
    rw [hgoodY i hi, hmod a ha, hmod _ (hml i)]
    have ha' := mem_legalS.mp ha
    constructor
    · intro h
      obtain ⟨e1, e2⟩ := val_inj t k a.1 a.2 _ _ ht ha'.2 ha'.1 (hcm i) hG h.symm
      exact Prod.ext e1 e2
    · intro h
      rw [h]
  have hPv : ∀ i, Valid sE (PbOf k eqw i) := fun i => PbOf_valid k eqw i (fun a ha => (hE i a ha).1)
  have hQv : ∀ i, Valid sE (QbOf k eqw i) := fun i => QbOf_valid k eqw i (fun a ha => (hE i a ha).1)
  have hVv : ∀ mu, mu ≤ k → Valid sE (VbOf eqw mu) := fun mu hmu =>
    VbOf_valid k eqw mu hmu (fun i a ha => (hE i a ha).1)
  have hPc : ∀ i, cntB x sE (PbOf k eqw i) = ∑ a ∈ legalS k, (a.1 - a.2) *
      (decide (y i % 2 ^ Wof t k = val t k a.1 a.2 % 2 ^ Wof t k)).toNat := by
    intro i
    rw [PbOf_cnt]
    exact Finset.sum_congr rfl (fun a ha => by rw [(hE i a ha).2])
  have hQc : ∀ i, cntB x sE (QbOf k eqw i) = ∑ a ∈ legalS k, a.2 *
      (decide (y i % 2 ^ Wof t k = val t k a.1 a.2 % 2 ^ Wof t k)).toNat := by
    intro i
    rw [QbOf_cnt]
    exact Finset.sum_congr rfl (fun a ha => by rw [(hE i a ha).2])
  have hPle : ∀ i, cntB x sE (PbOf k eqw i) ≤ k := by
    intro i
    rw [hPc]
    exact sum_one_hot_le _ _ _ k (huniq i) (fun a ha => by have := mem_legalS.mp ha; omega)
  have hQle : ∀ i, cntB x sE (QbOf k eqw i) ≤ k := by
    intro i
    rw [hQc]
    exact sum_one_hot_le _ _ _ k (huniq i) (fun a ha => by have := mem_legalS.mp ha; omega)
  have hPg : ∀ i, i ∉ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)) →
      cntB x sE (PbOf k eqw i) = G.card - cutc (batch i) G := by
    intro i hi
    rw [hPc]
    exact sum_one_hot_eq _ _ (fun a => a.1 - a.2) _ (hml i) (hgoodE i hi)
  have hQg : ∀ i, i ∉ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)) →
      cntB x sE (QbOf k eqw i) = cutc (batch i) G := by
    intro i hi
    rw [hQc]
    exact sum_one_hot_eq _ _ (fun a => a.2) _ (hml i) (hgoodE i hi)
  have hqabs : ∀ i, |((cntB x sE (PbOf k eqw i) : ℤ) - (cntB x sE (QbOf k eqw i) : ℤ))| ≤ (k : ℤ) := by
    intro i
    have h1 := hPle i
    have h2 := hQle i
    rw [abs_le]
    constructor <;> omega
  have hqgood : ∀ i, i ∉ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)) →
      ((cntB x sE (PbOf k eqw i) : ℤ) - (cntB x sE (QbOf k eqw i) : ℤ)) =
        ∑ e ∈ G, chi (batch i) e := by
    intro i hi
    rw [sum_chi_eq, hPg i hi, hQg i hi]
    have := hcm i
    omega
  -- majority
  have hMval : ∀ mu, mu ≤ k → decide (d / 2 + 1 ≤ cntB x sE (VbOf eqw mu)) = decide (mu = G.card) := by
    intro mu hmu
    have hVc : cntB x sE (VbOf eqw mu) = ∑ i : Fin d, ∑ c ∈ Finset.range (mu+1),
        (decide (y i % 2 ^ Wof t k = val t k mu c % 2 ^ Wof t k)).toNat := by
      rw [VbOf_cnt]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c hc => ?_))
      have hc' := Finset.mem_range.mp hc
      rw [(hE i (mu, c) (mem_legalS.mpr ⟨hmu, by simp only; omega⟩)).2]
    have hcard := sum_ind_not_mem (Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)))
    apply decide_eq_decide.mpr
    by_cases hmm : mu = G.card
    · subst hmm
      have hlow : ∑ i : Fin d, (if i ∈ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))
          then 0 else 1) ≤ cntB x sE (VbOf eqw G.card) := by
        rw [hVc]
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))
        · rw [if_pos hi]
          exact Nat.zero_le _
        · rw [if_neg hi]
          have h1 := Finset.single_le_sum (f := fun c =>
            (decide (y i % 2 ^ Wof t k = val t k G.card c % 2 ^ Wof t k)).toNat)
            (fun c _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le (hcm i)))
          have h2 := hgoodE i hi _ (hml i)
          simp only [decide_true] at h2
          rw [h2] at h1
          exact h1
      constructor
      · intro _
        rfl
      · intro _
        omega
    · have hup : cntB x sE (VbOf eqw mu) ≤ ∑ i : Fin d,
          (if i ∈ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i)) then 1 else 0) := by
        rw [hVc]
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))
        · rw [if_pos hi]
          have h1 := sum_one_hot_le (Finset.range (mu+1))
            (fun c => decide (y i % 2 ^ Wof t k = val t k mu c % 2 ^ Wof t k)) (fun _ => 1) 1
            (by
              intro c hc c' hc' h1 h2
              have hc1 := Finset.mem_range.mp hc
              have hc2 := Finset.mem_range.mp hc'
              have := huniq i (mu, c) (mem_legalS.mpr ⟨hmu, by simp only; omega⟩) (mu, c')
                (mem_legalS.mpr ⟨hmu, by simp only; omega⟩) h1 h2
              exact (Prod.mk.inj this).2)
            (fun _ _ => le_refl 1)
          simpa using h1
        · rw [if_neg hi]
          apply Nat.le_of_eq
          apply Finset.sum_eq_zero
          intro c hc
          have hc' := Finset.mem_range.mp hc
          have h2 := hgoodE i hi (mu, c) (mem_legalS.mpr ⟨hmu, by simp only; omega⟩)
          have h3 : decide ((mu, c) = (G.card, cutc (batch i) G)) = false := by
            simp [hmm]
          rw [h2, h3]
          rfl
      rw [sum_ind_mem] at hup
      constructor
      · intro h
        omega
      · intro h
        exact absurd h hmm
  have hM : ∀ mu, mu ≤ k → Has x (majTab k eqw sE).2 ((majTab k eqw sE).1 mu)
      (decide (mu = G.card)) := by
    intro mu hmu
    have h := majTab_spec hb k eqw sE hVv mu hmu
    rw [hMval mu hmu] at h
    exact h
  have hMle := majTab_le (d := d) k eqw sE
  have hD := decTab_spec hb batch (PbOf k eqw) (QbOf k eqw)
    (fun i => (cntB x sE (PbOf k eqw i) : ℤ) - (cntB x sE (QbOf k eqw i) : ℤ)) k
    (majTab k eqw sE).2 (fun i => (hPv i).mono hMle) (fun i => (hQv i).mono hMle)
    (fun i => by rw [cntB_mono hb (hPv i) hMle, cntB_mono hb (hQv i) hMle])
  have hDle := decTab_le (t := t) batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2
  obtain ⟨sel, hmax, hHas⟩ := hD G.card hG
  have hfw := fw_decodes hk hd batch hmargin G hG
    (fun i => (cntB x sE (PbOf k eqw i) : ℤ) - (cntB x sE (QbOf k eqw i) : ℤ)) hqabs
    (Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))) hy hqgood sel hmax
  have hmux := muxTab_spec hb k G.card hG (majTab k eqw sE).1
    (decTab batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2).1
    (decTab batch (PbOf k eqw) (QbOf k eqw) k (majTab k eqw sE).2).2
    (fun mu hmu => (hM mu hmu).mono hb hDle)
    (fun mu hmu e => by
      obtain ⟨sel', _, hH⟩ := hD mu hmu
      exact (hH e).1)
  intro e
  have h := hmux e
  rw [(hHas e).2, decide_eq_decide.mpr (hfw e)] at h
  exact h

theorem decAll_spec {t k d : ℕ} (ht : 2 ≤ t) (hk : 0 < k) (hd : 0 < d)
    (batch : Fin d → Fin t → Bool)
    (hmargin : ∀ (v : Pr t → ℝ) (S : Finset (Fin d)),
      (∑ e : Pr t, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) →
      400 * S.card ≤ d →
      (d : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) +
        256 * (∑ i ∈ S, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|) ≤
        128 * (∑ i, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|))
    (G : Finset (Pr t)) (hG : G.card ≤ k) (y : Fin d → ℕ)
    (hy : 400 * (Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))).card ≤ d)
    (x : List Bool) (hb : Base (2 + d * Wof t k) x)
    (hin : ∀ (i : Fin d) (j : ℕ), j < Wof t k →
      x.getD (2 + i.val * Wof t k + j) false = (y i).testBit j)
    (s : St (2 + d * Wof t k)) :
    ∀ e, Has x (decAll t k d batch s).2 ((decAll t k d batch s).1 e) (decide (e ∈ G)) :=
  decCore_spec ht hk hd batch hmargin G hG y hy x hb _ _ (eqTab_spec hb y hin s).2
-- ===================== size bookkeeping =====================

def Aof (C : ℕ) : ℕ := 28 * (C + 25)

theorem pz_mono {Z a p r : ℕ} (hZ : 2 ≤ Z) (ha : a ≤ Z ^ p) (h : p ≤ r) : a ≤ Z ^ r :=
  le_trans ha (Nat.pow_le_pow_right (by omega) h)

theorem pz_mul {Z a b p q r : ℕ} (hZ : 2 ≤ Z) (ha : a ≤ Z ^ p) (hb : b ≤ Z ^ q) (h : p + q ≤ r) :
    a * b ≤ Z ^ r :=
  le_trans (Nat.mul_le_mul ha hb) (by rw [← pow_add]; exact Nat.pow_le_pow_right (by omega) h)

theorem pz_add {Z a b p q r : ℕ} (hZ : 2 ≤ Z) (ha : a ≤ Z ^ p) (hb : b ≤ Z ^ q)
    (hp : p + 1 ≤ r) (hq : q + 1 ≤ r) : a + b ≤ Z ^ r := by
  have h1 : a ≤ Z ^ (r - 1) := pz_mono hZ ha (by omega)
  have h2 : b ≤ Z ^ (r - 1) := pz_mono hZ hb (by omega)
  have h3 : Z ^ r = Z * Z ^ (r - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [h3]
  calc a + b ≤ Z ^ (r - 1) + Z ^ (r - 1) := Nat.add_le_add h1 h2
    _ = 2 * Z ^ (r - 1) := by ring
    _ ≤ Z * Z ^ (r - 1) := Nat.mul_le_mul_right _ hZ

theorem pz_one {Z a : ℕ} (ha : a ≤ Z) : a ≤ Z ^ 1 := by simpa using ha

theorem forG_len' {n : ℕ} {α β : Type} [DecidableEq α] (f : St n → α → β × St n) (dflt : β)
    (c : ℕ) : ∀ (l : List α) (s : St n),
      (∀ (s : St n) (a : α), a ∈ l → (f s a).2.gs.length ≤ s.gs.length + c) →
      (forG f dflt s l).2.gs.length ≤ s.gs.length + l.length * c := by
  intro l
  induction l with
  | nil => intro s _; simp [forG]
  | cons a l ih =>
    intro s hc
    have h1 := hc s a (by simp)
    have h2 := ih (f s a).2 (fun s' a' ha' => hc s' a' (by simp [ha']))
    simp only [forG, List.length_cons]
    have : (l.length + 1) * c = l.length * c + c := by ring
    omega

theorem len_flatMap_le {α : Type} (l : List α) (g : α → List ℕ) (T : ℕ)
    (h : ∀ a ∈ l, (g a).length ≤ T) : (l.flatMap g).length ≤ l.length * T := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    have : (l.length + 1) * T = l.length * T + T := by ring
    omega

theorem uStep_outlen {n : ℕ} (pos neg : List ℕ) (stp : ℕ) (s : St n) :
    (uStep pos neg stp s).1.length = 2 * stp := by
  show ((List.range (2 * stp)).map _).length = _
  rw [List.length_map, List.length_range]

theorem stU_outlen {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) (i : Fin d) :
    ((stU batch Pb Qb B mu stp s).1 i).length = 2 * stp := by
  have key := forG_spec
    (fun s i => uStep (posBag batch Pb B mu stp i) (negBag batch Qb B mu stp i) stp s) []
    (fun (_ : Fin d) (u : List ℕ) (_ : St n) => u.length = 2 * stp)
    (fun _ _ _ _ h _ => h) (fun s i => uStep_le _ _ _ s) (probes d) s
    (fun s' _ i _ => uStep_outlen _ _ _ s')
  exact key.2 i (mem_probes i)

theorem stN_outlen {n d : ℕ} (u : Fin d → List ℕ) (s : St n) (i : Fin d) :
    ((stN u s).1 i).length = (u i).length := by
  have key := forG_spec (fun s i => gNotL s (u i)) []
    (fun (i : Fin d) (v : List ℕ) (_ : St n) => v.length = (u i).length)
    (fun _ _ _ _ h _ => h) (fun s i => gNotL_le s _) (probes d) s
    (fun s' _ i _ => mapG_outlen _ _ _)
  exact key.2 i (mem_probes i)

theorem posBag_len {t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (i : Fin d) (Z : ℕ) (hZ : 2 ≤ Z)
    (hN : (pairsL t).length ≤ Z) (hP : (Pb i).length ≤ Z) (hmu : mu ≤ Z) (hstp : stp ≤ Z)
    (hB : ∀ e, (B e).length ≤ Z) : (posBag batch Pb B mu stp i).length ≤ Z ^ 4 := by
  unfold posBag
  rw [List.length_append, len_repflat, len_repflat]
  have h1 : ((Finset.univ : Finset (Pr t)).toList.flatMap
      (fun e => if chi (batch i) e = 1 then [] else B e)).length ≤ (pairsL t).length * Z :=
    len_flatMap_le _ _ Z (fun e _ => by
      split_ifs
      · simp
      · exact hB e)
  exact pz_add hZ (pz_mul hZ (pz_one hstp) (pz_one hP) (le_refl 2))
    (pz_mul hZ (pz_one hmu) (le_trans h1 (pz_mul hZ (pz_one hN) (pz_one (le_refl Z)) (le_refl 2)))
      (le_refl 3)) (by norm_num) (by norm_num)

theorem negBag_len {t d : ℕ} (batch : Fin d → Fin t → Bool) (Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (i : Fin d) (Z : ℕ) (hZ : 2 ≤ Z)
    (hN : (pairsL t).length ≤ Z) (hQ : (Qb i).length ≤ Z) (hmu : mu ≤ Z) (hstp : stp ≤ Z)
    (hB : ∀ e, (B e).length ≤ Z) : (negBag batch Qb B mu stp i).length ≤ Z ^ 4 := by
  unfold negBag
  rw [List.length_append, len_repflat, len_repflat]
  have h1 : ((Finset.univ : Finset (Pr t)).toList.flatMap
      (fun e => if chi (batch i) e = 1 then B e else [])).length ≤ (pairsL t).length * Z :=
    len_flatMap_le _ _ Z (fun e _ => by
      split_ifs
      · exact hB e
      · simp)
  exact pz_add hZ (pz_mul hZ (pz_one hstp) (pz_one hQ) (le_refl 2))
    (pz_mul hZ (pz_one hmu) (le_trans h1 (pz_mul hZ (pz_one hN) (pz_one (le_refl Z)) (le_refl 2)))
      (le_refl 3)) (by norm_num) (by norm_num)

theorem uStep_len' {n : ℕ} (pos neg : List ℕ) (stp : ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z)
    (h512 : 512 ≤ Z) (hpos : pos.length ≤ Z ^ 4) (hneg : neg.length ≤ Z ^ 4) (hstp : stp ≤ Z) :
    (uStep pos neg stp s).2.gs.length ≤ s.gs.length + Z ^ 17 := by
  have h := uStep_len pos neg stp s
  have ha : 512 * (pos.length + neg.length) + stp ≤ Z ^ 7 :=
    pz_add hZ (pz_mul hZ (pz_one h512) (pz_add hZ hpos hneg (le_refl 5) (le_refl 5)) (le_refl 6))
      (pz_one hstp) (by norm_num) (by norm_num)
  have hb : 2 * ((512 * (pos.length + neg.length) + stp) * (512 * (pos.length + neg.length) + stp) +
      (512 * (pos.length + neg.length) + stp)) ≤ Z ^ 16 :=
    pz_mul hZ (pz_one hZ) (pz_add hZ (pz_mul hZ ha ha (le_refl 14)) ha (le_refl 15) (by norm_num))
      (by norm_num)
  have hc : neg.length + 2 * ((512 * (pos.length + neg.length) + stp) *
      (512 * (pos.length + neg.length) + stp) + (512 * (pos.length + neg.length) + stp)) ≤ Z ^ 17 :=
    pz_add hZ hneg hb (by norm_num) (le_refl 17)
  omega

theorem stU_len {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z) (h512 : 512 ≤ Z)
    (hd : (probes d).length ≤ Z) (hN : (pairsL t).length ≤ Z)
    (hP : ∀ i, (Pb i).length ≤ Z) (hQ : ∀ i, (Qb i).length ≤ Z) (hmu : mu ≤ Z) (hstp : stp ≤ Z)
    (hB : ∀ e, (B e).length ≤ Z) :
    (stU batch Pb Qb B mu stp s).2.gs.length ≤ s.gs.length + Z ^ 18 := by
  have h : (stU batch Pb Qb B mu stp s).2.gs.length ≤ s.gs.length + (probes d).length * Z ^ 17 := by
    unfold stU
    exact forG_len _ _ (Z ^ 17) (fun s i => uStep_len' _ _ stp s Z hZ h512
      (posBag_len batch Pb B mu stp i Z hZ hN (hP i) hmu hstp hB)
      (negBag_len batch Qb B mu stp i Z hZ hN (hQ i) hmu hstp hB) hstp) _ _
  have h2 : (probes d).length * Z ^ 17 ≤ Z ^ 18 := pz_mul hZ (pz_one hd) (le_refl _) (by norm_num)
  omega

theorem stN_len {n d : ℕ} (u : Fin d → List ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z)
    (hd : (probes d).length ≤ Z) (hu : ∀ i, (u i).length ≤ Z ^ 2) :
    (stN u s).2.gs.length ≤ s.gs.length + Z ^ 3 := by
  have h : (stN u s).2.gs.length ≤ s.gs.length + (probes d).length * Z ^ 2 := by
    unfold stN
    exact forG_len _ _ (Z ^ 2) (fun s i => le_trans (gNotL_len s (u i))
      (Nat.add_le_add_left (hu i) _)) _ _
  have h2 : (probes d).length * Z ^ 2 ≤ Z ^ 3 := pz_mul hZ (pz_one hd) (le_refl _) (by norm_num)
  omega

theorem gGe_len' {n : ℕ} (s : St n) (A B : List ℕ) (Z : ℕ) (hZ : 2 ≤ Z)
    (hA : A.length ≤ Z ^ 3) (hB : B.length ≤ Z ^ 3) :
    (gGe s A B).2.gs.length ≤ s.gs.length + Z ^ 11 := by
  have h := gGe_len s A B
  have hab : A.length + B.length ≤ Z ^ 4 := pz_add hZ hA hB (le_refl 4) (le_refl 4)
  have h2 : 2 * ((A.length + B.length) * (A.length + B.length) + (A.length + B.length)) ≤ Z ^ 10 :=
    pz_mul hZ (pz_one hZ) (pz_add hZ (pz_mul hZ hab hab (le_refl 8)) hab (le_refl 9) (by norm_num))
      (by norm_num)
  have h3 : B.length + 2 * ((A.length + B.length) * (A.length + B.length) + (A.length + B.length)) ≤
      Z ^ 11 := pz_add hZ hB h2 (by norm_num) (le_refl 11)
  omega

theorem stI_len {n t : ℕ} (U : Pr t → List ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z)
    (hN : (pairsL t).length ≤ Z) (hU : ∀ e, (U e).length ≤ Z ^ 3) :
    (stI U s).2.gs.length ≤ s.gs.length + Z ^ 14 := by
  have h : (stI U s).2.gs.length ≤
      s.gs.length + (pairsL t).length * ((pairsL t).length * (Z ^ 11 + 1)) := by
    unfold stI
    exact forG_len _ _ _ (fun s e => gAllG_len _ (Z ^ 11)
      (fun s e' => gGe_len' s (U e) (U e') Z hZ (hU e) (hU e')) s _) _ _
  have h1 : Z ^ 11 + 1 ≤ Z ^ 12 :=
    pz_add hZ (le_refl _) (pz_one (show 1 ≤ Z by omega)) (le_refl 12) (by norm_num)
  have h2 : (pairsL t).length * ((pairsL t).length * (Z ^ 11 + 1)) ≤ Z ^ 14 :=
    pz_mul hZ (pz_one hN) (pz_mul hZ (pz_one hN) h1 (le_refl 13)) (le_refl 14)
  omega

theorem stX_len {n t : ℕ} (isw : Pr t → ℕ) (s : St n) (Z : ℕ) (hN : (pairsL t).length ≤ Z) :
    (stX isw s).2.gs.length ≤ s.gs.length + Z := by
  have h : (stX isw s).2.gs.length ≤ s.gs.length + (pairsL t).length * 1 := by
    unfold stX
    exact forG_len _ _ 1 (fun s e => by rw [gNot_len]) _ _
  omega

theorem stS_len {n t : ℕ} (isw nisw : Pr t → ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z)
    (hN : (pairsL t).length ≤ Z) :
    (stS isw nisw s).2.gs.length ≤ s.gs.length + Z ^ 3 := by
  have h : (stS isw nisw s).2.gs.length ≤
      s.gs.length + (pairsL t).length * ((pairsL t).length + 1) := by
    unfold stS
    exact forG_len _ _ _ (fun s e => by
      rw [gAndL_len, List.length_cons, List.length_map]
      have := List.length_filter_le (fun e' => decide (codeP e' < codeP e)) (pairsL t)
      omega) _ _
  have h1 : (pairsL t).length + 1 ≤ Z ^ 2 :=
    pz_add hZ (pz_one hN) (pz_one (show 1 ≤ Z by omega)) (le_refl 2) (le_refl 2)
  have h2 : (pairsL t).length * ((pairsL t).length + 1) ≤ Z ^ 3 :=
    pz_mul hZ (pz_one hN) h1 (le_refl 3)
  omega

theorem ubag_len {t d : ℕ} (batch : Fin d → Fin t → Bool) (u nu : Fin d → List ℕ) (e : Pr t)
    (Z : ℕ) (hZ : 2 ≤ Z) (hd : (probes d).length ≤ Z) (hu : ∀ i, (u i).length ≤ Z ^ 2)
    (hnu : ∀ i, (nu i).length ≤ Z ^ 2) : (ubag batch u nu e).length ≤ Z ^ 3 := by
  have h : (ubag batch u nu e).length ≤ (probes d).length * Z ^ 2 :=
    len_flatMap_le (probes d) _ _ (fun i _ => by
      split_ifs
      · exact hu i
      · exact hnu i)
  exact le_trans h (pz_mul hZ (pz_one hd) (le_refl _) (by norm_num))

theorem stAll_len {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (B : Pr t → List ℕ) (mu stp : ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z) (h512 : 512 ≤ Z)
    (hd : (probes d).length ≤ Z) (hN : (pairsL t).length ≤ Z)
    (hP : ∀ i, (Pb i).length ≤ Z) (hQ : ∀ i, (Qb i).length ≤ Z) (hmu : mu ≤ Z) (hstp : stp ≤ Z)
    (hB : ∀ e, (B e).length ≤ Z) :
    (stAll batch Pb Qb B mu stp s).2.gs.length ≤ s.gs.length + Z ^ 22 := by
  have h2s : 2 * stp ≤ Z ^ 2 := pz_mul hZ (pz_one hZ) (pz_one hstp) (le_refl 2)
  have hu : ∀ i, ((stU batch Pb Qb B mu stp s).1 i).length ≤ Z ^ 2 := fun i => by
    rw [stU_outlen]
    exact h2s
  have hnu : ∀ i, ((stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1 i).length ≤
      Z ^ 2 := fun i => by
    rw [stN_outlen, stU_outlen]
    exact h2s
  have h1 := stU_len batch Pb Qb B mu stp s Z hZ h512 hd hN hP hQ hmu hstp hB
  have h2 := stN_len (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2 Z hZ hd hu
  have h3 := stI_len (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2 Z hZ hN
    (fun e => ubag_len batch _ _ e Z hZ hd hu hnu)
  have h4 := stX_len (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).1
    (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).2 Z hN
  have h5 := stS_len (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).1
    (stX (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).1
    (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).2).1
    (stX (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).1
    (stI (ubag batch (stU batch Pb Qb B mu stp s).1
      (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).1)
    (stN (stU batch Pb Qb B mu stp s).1 (stU batch Pb Qb B mu stp s).2).2).2).2 Z hZ hN
  have hsum : Z ^ 18 + Z ^ 3 + Z ^ 14 + Z + Z ^ 3 ≤ Z ^ 22 :=
    pz_add hZ (pz_add hZ (pz_add hZ (pz_add hZ (le_refl (Z ^ 18)) (le_refl (Z ^ 3)) (le_refl 19)
      (by norm_num)) (le_refl (Z ^ 14)) (le_refl 20) (by norm_num)) (pz_one (le_refl Z))
      (le_refl 21) (by norm_num)) (le_refl (Z ^ 3)) (le_refl 22) (by norm_num)
  show (stS _ _ _).2.gs.length ≤ _
  omega

theorem iter_outlen {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (mu : ℕ) (s : St n) : ∀ (j : ℕ) (e : Pr t), ((iter batch Pb Qb mu s j).1 e).length = j := by
  intro j
  induction j with
  | zero => intro e; rfl
  | succ j ih =>
    intro e
    show ((iter batch Pb Qb mu s j).1 e ++ [_]).length = j + 1
    rw [List.length_append, ih e]
    rfl

theorem iter_len {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (mu : ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z) (h512 : 512 ≤ Z)
    (hd : (probes d).length ≤ Z) (hN : (pairsL t).length ≤ Z)
    (hP : ∀ i, (Pb i).length ≤ Z) (hQ : ∀ i, (Qb i).length ≤ Z) (hmu : mu ≤ Z) :
    ∀ j, j ≤ Z → (iter (t := t) batch Pb Qb mu s j).2.gs.length ≤ s.gs.length + j * Z ^ 22 := by
  intro j
  induction j with
  | zero => intro _; simp [iter]
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 := stAll_len batch Pb Qb (iter batch Pb Qb mu s j).1 mu j (iter batch Pb Qb mu s j).2
      Z hZ h512 hd hN hP hQ hmu (by omega) (fun e => by rw [iter_outlen]; omega)
    show (stAll batch Pb Qb (iter batch Pb Qb mu s j).1 mu j (iter batch Pb Qb mu s j).2).2.gs.length ≤ _
    have : (j + 1) * Z ^ 22 = j * Z ^ 22 + Z ^ 22 := by ring
    omega

theorem decMu_len {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (S mu : ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z) (h512 : 512 ≤ Z)
    (hd : (probes d).length ≤ Z) (hN : (pairsL t).length ≤ Z)
    (hP : ∀ i, (Pb i).length ≤ Z) (hQ : ∀ i, (Qb i).length ≤ Z) (hmu : mu ≤ Z) (hS : S ≤ Z) :
    (decMu (t := t) batch Pb Qb S mu s).2.gs.length ≤ s.gs.length + Z ^ 24 := by
  have h1 := iter_len (t := t) batch Pb Qb mu s Z hZ h512 hd hN hP hQ hmu S hS
  have h1' : S * Z ^ 22 ≤ Z ^ 23 := pz_mul hZ (pz_one hS) (le_refl _) (by norm_num)
  have hL : ∀ e : Pr t, (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten.length ≤
      Z ^ 3 := by
    intro e
    rw [len_repflat, iter_outlen]
    exact pz_mul hZ (pz_mul hZ (pz_one hZ) (pz_one hmu) (le_refl 2)) (pz_one hS) (le_refl 3)
  have h2 : (decMu (t := t) batch Pb Qb S mu s).2.gs.length ≤
      (iter (t := t) batch Pb Qb mu s S).2.gs.length + (pairsL t).length * Z ^ 8 := by
    unfold decMu
    exact forG_len _ _ (Z ^ 8) (fun s' e => by
      have hc := gCount_len s' (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten
      have hl := hL e
      have hb : 2 * ((List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten.length *
          (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten.length +
          (List.replicate (2 * mu) ((iter batch Pb Qb mu s S).1 e)).flatten.length) ≤ Z ^ 8 :=
        pz_mul hZ (pz_one hZ) (pz_add hZ (pz_mul hZ hl hl (le_refl 6)) hl (le_refl 7) (by norm_num))
          (by norm_num)
      exact le_trans hc (Nat.add_le_add_left hb _)) _ _
  have h2' : (pairsL t).length * Z ^ 8 ≤ Z ^ 9 := pz_mul hZ (pz_one hN) (le_refl _) (by norm_num)
  have hsum : Z ^ 23 + Z ^ 9 ≤ Z ^ 24 := pz_add hZ (le_refl _) (le_refl _) (le_refl 24) (by norm_num)
  omega

theorem range_toList_len (m : ℕ) : (Finset.range m).toList.length = m := by
  rw [Finset.length_toList, Finset.card_range]

theorem decTab_len {n t d : ℕ} (batch : Fin d → Fin t → Bool) (Pb Qb : Fin d → List ℕ)
    (k : ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z) (h512 : 512 ≤ Z)
    (hd : (probes d).length ≤ Z) (hN : (pairsL t).length ≤ Z)
    (hP : ∀ i, (Pb i).length ≤ Z) (hQ : ∀ i, (Qb i).length ≤ Z) (hk : k + 1 ≤ Z)
    (hS : Sbig k ≤ Z) :
    (decTab (t := t) batch Pb Qb k s).2.gs.length ≤ s.gs.length + Z ^ 25 := by
  have h : (decTab (t := t) batch Pb Qb k s).2.gs.length ≤
      s.gs.length + (Finset.range (k+1)).toList.length * Z ^ 24 := by
    unfold decTab
    exact forG_len' _ _ (Z ^ 24) _ s (fun s' mu hmu => by
      have hmu' := Finset.mem_range.mp (Finset.mem_toList.mp hmu)
      exact decMu_len batch Pb Qb (Sbig k) mu s' Z hZ h512 hd hN hP hQ (by omega) hS)
  rw [range_toList_len] at h
  have h2 : (k + 1) * Z ^ 24 ≤ Z ^ 25 := pz_mul hZ (pz_one hk) (le_refl _) (by norm_num)
  omega

theorem litF_len {n : ℕ} (base v : ℕ) (s : St n) (j : ℕ) :
    (litF base v s j).2.gs.length ≤ s.gs.length + 1 := by
  unfold litF
  split_ifs
  · exact Nat.le_succ _
  · rw [gNot_len]

theorem legalS_card (k : ℕ) : (legalS k).card ≤ (k + 1) * (k + 1) := by
  unfold legalS
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_range]

theorem eqTab_len (t k d : ℕ) (s : St (2 + d * Wof t k)) (Z : ℕ) (hZ : 2 ≤ Z)
    (hd : d ≤ Z) (hk : k + 1 ≤ Z) (hW : Wof t k ≤ Z) :
    (eqTab t k d s).2.gs.length ≤ s.gs.length + Z ^ 5 := by
  have h : (eqTab t k d s).2.gs.length ≤ s.gs.length +
      ((Finset.univ ×ˢ legalS k : Finset (Fin d × ℕ × ℕ)).toList).length * (Wof t k * (1 + 1)) := by
    unfold eqTab
    exact forG_len _ _ _ (fun s a => by
      have := gAllG_len (litF (2 + a.1.val * Wof t k) (val t k a.2.1 a.2.2)) 1
        (litF_len _ _) s (List.range (Wof t k))
      rw [List.length_range] at this
      exact this) _ _
  have hl : ((Finset.univ ×ˢ legalS k : Finset (Fin d × ℕ × ℕ)).toList).length ≤ Z ^ 3 := by
    rw [Finset.length_toList, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    exact pz_mul hZ (pz_one hd) (le_trans (legalS_card k)
      (pz_mul hZ (pz_one hk) (pz_one hk) (le_refl 2))) (le_refl 3)
  have h2 : ((Finset.univ ×ˢ legalS k : Finset (Fin d × ℕ × ℕ)).toList).length *
      (Wof t k * (1 + 1)) ≤ Z ^ 5 :=
    pz_mul hZ hl (pz_mul hZ (pz_one hW) (pz_one hZ) (le_refl 2)) (le_refl 5)
  omega

theorem probes_len (d : ℕ) : (probes d).length = d := by
  unfold probes
  rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]

theorem VbOf_len {d : ℕ} (eqw : Fin d × ℕ × ℕ → ℕ) (mu : ℕ) :
    (VbOf eqw mu).length ≤ d * (mu + 1) := by
  have h : (VbOf eqw mu).length ≤ (probes d).length * (mu + 1) :=
    len_flatMap_le (probes d) _ _ (fun i _ => by
      rw [List.length_map, range_toList_len])
  rw [probes_len] at h
  exact h

theorem majTab_len {n d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (s : St n) (Z : ℕ) (hZ : 2 ≤ Z)
    (hd : d ≤ Z) (hk : k + 1 ≤ Z) :
    (majTab k eqw s).2.gs.length ≤ s.gs.length + Z ^ 7 := by
  have h : (majTab k eqw s).2.gs.length ≤
      s.gs.length + (Finset.range (k+1)).toList.length * Z ^ 6 := by
    unfold majTab
    exact forG_len' _ _ (Z ^ 6) _ s (fun s' mu hmu => by
      have hmu' := Finset.mem_range.mp (Finset.mem_toList.mp hmu)
      have hc := gCount_len s' (VbOf eqw mu)
      have hl : (VbOf eqw mu).length ≤ Z ^ 2 :=
        le_trans (VbOf_len eqw mu) (pz_mul hZ (pz_one hd) (pz_one (by omega)) (le_refl 2))
      have hb : 2 * ((VbOf eqw mu).length * (VbOf eqw mu).length + (VbOf eqw mu).length) ≤ Z ^ 6 :=
        pz_mul hZ (pz_one hZ) (pz_add hZ (pz_mul hZ hl hl (le_refl 4)) hl (le_refl 5) (by norm_num))
          (by norm_num)
      exact le_trans hc (Nat.add_le_add_left hb _))
  rw [range_toList_len] at h
  have h2 : (k + 1) * Z ^ 6 ≤ Z ^ 7 := pz_mul hZ (pz_one hk) (le_refl _) (by norm_num)
  omega

theorem muxTab_len {n t : ℕ} (k : ℕ) (Mw : ℕ → ℕ) (ow : ℕ → Pr t → ℕ) (s : St n) (Z : ℕ)
    (hZ : 2 ≤ Z) (hN : (pairsL t).length ≤ Z) (hk : k + 1 ≤ Z) :
    (muxTab k Mw ow s).2.gs.length ≤ s.gs.length + Z ^ 3 := by
  have h : (muxTab k Mw ow s).2.gs.length ≤
      s.gs.length + (pairsL t).length * ((k + 1) * (1 + 1)) := by
    unfold muxTab
    exact forG_len _ _ _ (fun s e => by
      have := gAnyG_len (fun s mu => gAnd s (Mw mu) (ow mu e)) 1
        (fun s mu => by rw [gAnd_len]) s (Finset.range (k+1)).toList
      rw [range_toList_len] at this
      exact this) _ _
  have h2 : (pairsL t).length * ((k + 1) * (1 + 1)) ≤ Z ^ 3 :=
    pz_mul hZ (pz_one hN) (pz_mul hZ (pz_one hk) (pz_one hZ) (le_refl 2)) (le_refl 3)
  omega

theorem PbOf_len {d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (i : Fin d) :
    (PbOf k eqw i).length ≤ (k + 1) * (k + 1) * k := by
  have h : (PbOf k eqw i).length ≤ (legalS k).toList.length * k :=
    len_flatMap_le _ _ _ (fun a ha => by
      rw [List.length_replicate]
      have := mem_legalS.mp (Finset.mem_toList.mp ha)
      omega)
  rw [Finset.length_toList] at h
  exact le_trans h (Nat.mul_le_mul_right _ (legalS_card k))

theorem QbOf_len {d : ℕ} (k : ℕ) (eqw : Fin d × ℕ × ℕ → ℕ) (i : Fin d) :
    (QbOf k eqw i).length ≤ (k + 1) * (k + 1) * k := by
  have h : (QbOf k eqw i).length ≤ (legalS k).toList.length * k :=
    len_flatMap_le _ _ _ (fun a ha => by
      rw [List.length_replicate]
      have := mem_legalS.mp (Finset.mem_toList.mp ha)
      omega)
  rw [Finset.length_toList] at h
  exact le_trans h (Nat.mul_le_mul_right _ (legalS_card k))

theorem decAll_len (t k d : ℕ) (batch : Fin d → Fin t → Bool) (s : St (2 + d * Wof t k))
    (Z : ℕ) (hZ : 2 ≤ Z) (h512 : 512 ≤ Z) (hd : d ≤ Z) (hN : (pairsL t).length ≤ Z)
    (hk : k + 1 ≤ Z) (hW : Wof t k ≤ Z) (hS : Sbig k ≤ Z) (hLP : (k + 1) * (k + 1) * k ≤ Z) :
    (decAll t k d batch s).2.gs.length ≤ s.gs.length + Z ^ 28 := by
  have h1 := eqTab_len t k d s Z hZ hd hk hW
  have h2 := majTab_len k (eqTab t k d s).1 (eqTab t k d s).2 Z hZ hd hk
  have h3 := decTab_len (t := t) batch (PbOf k (eqTab t k d s).1) (QbOf k (eqTab t k d s).1) k
    (majTab k (eqTab t k d s).1 (eqTab t k d s).2).2 Z hZ h512 (by rw [probes_len]; exact hd) hN
    (fun i => le_trans (PbOf_len k _ i) hLP) (fun i => le_trans (QbOf_len k _ i) hLP) hk hS
  have h4 := muxTab_len k (majTab k (eqTab t k d s).1 (eqTab t k d s).2).1
    (decTab batch (PbOf k (eqTab t k d s).1) (QbOf k (eqTab t k d s).1) k
      (majTab k (eqTab t k d s).1 (eqTab t k d s).2).2).1
    (decTab batch (PbOf k (eqTab t k d s).1) (QbOf k (eqTab t k d s).1) k
      (majTab k (eqTab t k d s).1 (eqTab t k d s).2).2).2 Z hZ hN hk
  have hsum : Z ^ 5 + Z ^ 7 + Z ^ 25 + Z ^ 3 ≤ Z ^ 28 :=
    pz_add hZ (pz_add hZ (pz_add hZ (le_refl (Z ^ 5)) (le_refl (Z ^ 7)) (by norm_num) (le_refl 8))
      (le_refl (Z ^ 25)) (by norm_num) (le_refl 26)) (le_refl (Z ^ 3)) (by norm_num) (by norm_num)
  show (muxTab _ _ _ _).2.gs.length ≤ _
  omega

theorem pairsL_len (t : ℕ) : (pairsL t).length ≤ t * t := by
  unfold pairsL
  rw [Finset.length_toList, Finset.card_univ]
  have h := Fintype.card_subtype_le (fun p : Fin t × Fin t => p.1 < p.2)
  rw [Fintype.card_prod, Fintype.card_fin] at h
  exact h

theorem Wof_le_sq (t k : ℕ) : k*(t+2)+1 ≤ (t+k+2)*(t+k+2) := by nlinarith

theorem decAll_size (t k d : ℕ) (ht : 2 ≤ t) (hk : 0 < k) (batch : Fin d → Fin t → Bool)
    (C : ℕ) (hdC : d ≤ C * k * (1 + Nat.log 2 t)) (s : St (2 + d * Wof t k))
    (hs : s.gs = []) :
    (decAll t k d batch s).2.gs.length ≤ (t+k+2)^(Aof C) := by
  have hX4 : 4 ≤ t + k + 2 := by omega
  have hXpos : 0 < t + k + 2 := by omega
  have hZdef : ∀ a p : ℕ, a ≤ (t+k+2)^p → p ≤ 25 → a ≤ (C+1) * (t+k+2)^25 := by
    intro a p ha hp
    calc a ≤ (t+k+2)^p := ha
      _ ≤ (t+k+2)^25 := Nat.pow_le_pow_right hXpos hp
      _ ≤ (C+1) * (t+k+2)^25 := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : ∀ p : ℕ, 4^p ≤ (t+k+2)^p := fun p => Nat.pow_le_pow_left hX4 p
  have hZ2 : 2 ≤ (C+1) * (t+k+2)^25 := hZdef 2 1 (by rw [pow_one]; omega) (by norm_num)
  have h512 : 512 ≤ (C+1) * (t+k+2)^25 :=
    hZdef 512 5 (le_trans (by norm_num) (h4 5)) (by norm_num)
  have hk1 : k + 1 ≤ (C+1) * (t+k+2)^25 := hZdef (k+1) 1 (by rw [pow_one]; omega) (by norm_num)
  have hW : Wof t k ≤ (C+1) * (t+k+2)^25 := hZdef _ 2 (by
    unfold Wof
    calc k*(t+2)+1 ≤ (t+k+2)*(t+k+2) := Wof_le_sq t k
      _ = (t+k+2)^2 := (sq _).symm) (by norm_num)
  have hS : Sbig k ≤ (C+1) * (t+k+2)^25 := hZdef _ 25 (by
    unfold Sbig
    calc 2^42 * k^4 = 4^21 * k^4 := by norm_num
      _ ≤ (t+k+2)^21 * (t+k+2)^4 :=
          Nat.mul_le_mul (h4 21) (Nat.pow_le_pow_left (by omega) 4)
      _ = (t+k+2)^25 := by rw [← pow_add]) (le_refl 25)
  have hLP : (k+1)*(k+1)*k ≤ (C+1) * (t+k+2)^25 := hZdef _ 3 (by
    calc (k+1)*(k+1)*k ≤ (t+k+2)*(t+k+2)*(t+k+2) :=
          Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = (t+k+2)^3 := by ring) (by norm_num)
  have hN : (pairsL t).length ≤ (C+1) * (t+k+2)^25 := hZdef _ 2 (by
    calc (pairsL t).length ≤ t * t := pairsL_len t
      _ ≤ (t+k+2)*(t+k+2) := Nat.mul_le_mul (by omega) (by omega)
      _ = (t+k+2)^2 := (sq _).symm) (by norm_num)
  have hd : d ≤ (C+1) * (t+k+2)^25 := by
    have hlog : Nat.log 2 t ≤ t := Nat.log_le_self 2 t
    calc d ≤ C * k * (1 + Nat.log 2 t) := hdC
      _ ≤ C * (t+k+2) * (t+k+2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = C * (t+k+2)^2 := by ring
      _ ≤ C * (t+k+2)^25 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hXpos (by norm_num))
      _ ≤ (C+1) * (t+k+2)^25 := Nat.mul_le_mul_right _ (by omega)
  have hlen := decAll_len t k d batch s _ hZ2 h512 hd hN hk1 hW hS hLP
  rw [hs] at hlen
  simp only [List.length_nil, zero_add] at hlen
  refine le_trans hlen ?_
  have hC : C + 1 ≤ (t+k+2)^C :=
    le_trans (Nat.succ_le_of_lt Nat.lt_two_pow_self) (Nat.pow_le_pow_left (by omega) C)
  calc ((C+1) * (t+k+2)^25)^28 ≤ ((t+k+2)^C * (t+k+2)^25)^28 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hC) 28
    _ = (t+k+2)^(Aof C) := by
        unfold Aof
        rw [← pow_add, ← pow_mul, Nat.mul_comm]
-- ===================== decoder (statement used by the main theorem) =====================

theorem WF_nil (n : ℕ) : WF n [] := by
  intro j h
  simp at h

theorem WF_readsBack {n : ℕ} {gs : List Gate} (h : WF n gs) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs, 0⟩ := by
  intro j hj i hi
  have hj' : j < gs.length := hj
  have hg : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨gs, 0⟩ j = gs[j] := by
    show gs.getD j _ = gs[j]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']
    rfl
  rw [hg] at hi
  exact (h j hj').2 i hi

theorem WF_shape {n : ℕ} {gs : List Gate} (h : WF n gs) :
    ∀ gate ∈ gs, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1) := by
  intro gate hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact (h j hj).1

theorem input_base (d W : ℕ) (f : Fin d → Fin W → Bool) :
    Base (2 + d * W) ([false,true] ++
      (List.ofFn (fun i : Fin d => List.ofFn (fun j : Fin W => f i j))).flatten) := by
  refine ⟨?_, by omega, rfl, rfl⟩
  rw [List.length_append, flat_length]
  rfl

theorem input_getD (d W : ℕ) (f : Fin d → Fin W → Bool) (i : Fin d) (j : ℕ) (hj : j < W) :
    ([false,true] ++ (List.ofFn (fun i : Fin d => List.ofFn (fun j : Fin W => f i j))).flatten).getD
      (2 + i.val * W + j) false = f i ⟨j, hj⟩ := by
  have h := flat_getD W d f i ⟨j, hj⟩
  rw [← h]
  have h2 : 2 + i.val * W + j = ([false,true] : List Bool).length + (i.val * W + j) := by
    simp
    omega
  rw [h2, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]

theorem decoder_exists (t k d : ℕ) (ht : 2 ≤ t) (hk : 0 < k) (hd : 0 < d)
    (batch : Fin d → Fin t → Bool)
    (hmargin : ∀ (v : Pr t → ℝ) (S : Finset (Fin d)),
      (∑ e : Pr t, |v e|) ≤ 2 * Real.sqrt (k : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) →
      400 * S.card ≤ d →
      (d : ℝ) * Real.sqrt (∑ e : Pr t, (v e)^2) +
        256 * (∑ i ∈ S, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|) ≤
        128 * (∑ i, |∑ e : Pr t, v e * (if batch i e.val.1 then (1 : ℝ) else -1) *
          (if batch i e.val.2 then (1 : ℝ) else -1)|))
    (C : ℕ) (hdC : d ≤ C * k * (1 + Nat.log 2 t)) :
    ∃ (g : PEqualNP.CircuitLowerBounds.Circuit)
      (edge : Pr t → Fin (2 + d * (k*(t+2)+1) + g.size)),
      g.size ≤ (t+k+2)^(Aof C) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (2 + d * (k*(t+2)+1)) g ∧
      (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
        (gate.op = .not ∧ gate.inputs.length = 1)) ∧
      ∀ (G : Finset (Pr t)), G.card ≤ k → ∀ (y : Fin d → ℕ),
        400 * (Finset.univ.filter (fun i => y i ≠ readF t k G (batch i))).card ≤ d →
        ∀ e : Pr t, (g.wires ([false,true] ++ (List.ofFn (fun i : Fin d =>
          List.ofFn (fun j : Fin (k*(t+2)+1) => (y i).testBit j.val))).flatten)).getD
            (edge e).val false = decide (e ∈ G) := by
  have hn : 0 < 2 + d * Wof t k := by omega
  have hres : ∃ r : (Pr t → ℕ) × St (2 + d * Wof t k),
      r = decAll t k d batch ⟨[], WF_nil _, hn⟩ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ := hres
  refine ⟨⟨r.2.gs, 0⟩, fun e => ⟨min (r.1 e) (2 + d * (k*(t+2)+1) + r.2.gs.length - 1),
    lt_of_le_of_lt (Nat.min_le_right _ _) (by
      show 2 + d * (k*(t+2)+1) + r.2.gs.length - 1 < 2 + d * (k*(t+2)+1) + r.2.gs.length
      omega)⟩, ?_, ?_, ?_, ?_⟩
  · show r.2.gs.length ≤ _
    rw [hr]
    exact decAll_size t k d ht hk batch C hdC _ rfl
  · exact WF_readsBack r.2.wf
  · exact WF_shape r.2.wf
  · intro G hG y hy e
    have hb := input_base d (Wof t k) (fun i j => (y i).testBit j.val)
    have hin : ∀ (i : Fin d) (j : ℕ), j < Wof t k →
        ([false,true] ++ (List.ofFn (fun i : Fin d =>
          List.ofFn (fun j : Fin (Wof t k) => (y i).testBit j.val))).flatten).getD
          (2 + i.val * Wof t k + j) false = (y i).testBit j := fun i j hj =>
      input_getD d (Wof t k) (fun i j => (y i).testBit j.val) i j hj
    have h := decAll_spec ht hk hd batch hmargin G hG y hy _ hb hin ⟨[], WF_nil _, hn⟩ e
    rw [← hr] at h
    have hlt : r.1 e < 2 + d * (k*(t+2)+1) + r.2.gs.length := h.1
    have hmin : min (r.1 e) (2 + d * (k*(t+2)+1) + r.2.gs.length - 1) = r.1 e := by omega
    show (run r.2.gs _).getD (min (r.1 e) (2 + d * (k*(t+2)+1) + r.2.gs.length - 1)) false = _
    rw [hmin]
    exact h.2

end PEqualNP.Outside.L_pcx_464_aux

theorem PEqualNP.Outside.L_pcx_464 : ∃ C A : ℕ, 0 < C ∧ ∀ t k : ℕ, 2 ≤ t → 0 < k →
  let T := Fin t
  let V := Option (T × Bool)
  let Pair := {p : T × T // p.1 < p.2}
  let E := Fin 3 × T
  let Mask := T → Fin 3
  let tail := fun e : E => if e.1 = 0 then some (e.2,false) else (none : V)
  let head := fun e : E => some (e.2,decide (e.1 ≠ 1))
  let weight := fun (g : Option Pair) (e : E) (diff : Bool) =>
    if e.1 = 0 then diff.toNat else if e.1 = 2 then 1 else
    if g.elim false (fun p => decide (p.val.1 = e.2 ∨ p.val.2 = e.2)) then
      (if diff then 1 else 3) else (2 : ℕ)
  let obs := fun (g : Option Pair) (p : Mask) =>
    ∑ x : V → Bool, if (∀ i : T, p i = 0 ∨ p i = (if x (some (i,false)) then 2 else 1)) ∧
      (Finset.univ.filter (fun e : E => x (tail e) ≠ x (head e))).card = 2*t then
      ∏ e : E, weight g e (xor (x (tail e)) (x (head e))) else 0
  let Pool := Finset Pair

  let read := fun (G : Pool) (pin : T → Bool) =>
    let p : Mask := fun i => if pin i then 2 else 1
    (obs none p)^(k-G.card) * ∏ e ∈ G, obs (some e) p
  let W := k*(t+2)+1
  ∃ (d : ℕ) (batch : Fin d → T → Bool) (g : PEqualNP.CircuitLowerBounds.Circuit)
    (edge : Pair → Fin (2+d*W+g.size)),
    0 < d ∧ d ≤ C*k*(1+Nat.log 2 t) ∧ g.size ≤ (t+k+2)^A ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+d*W) g ∧
    (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
      (gate.op = .not ∧ gate.inputs.length = 1)) ∧
    ∀ (G : Pool), G.card ≤ k →
      (∀ i, read G (batch i) < 2^W) ∧
      ∀ (y : Fin d → ℕ),
        400*(Finset.univ.filter (fun i => y i ≠ read G (batch i))).card ≤ d →
        let bits := (List.ofFn (fun i : Fin d => List.ofFn (fun j : Fin W =>
          (y i).testBit j.val))).flatten
        ∀ e : Pair, (g.wires ([false,true] ++ bits)).getD (edge e).val false = decide (e ∈ G) := by
  obtain ⟨C, hC, hbm⟩ := PEqualNP.Outside.L_pcx_464_aux.batch_margin
  refine ⟨C, PEqualNP.Outside.L_pcx_464_aux.Aof C, hC, ?_⟩
  intro t k ht hk
  obtain ⟨d, batch, hd, hdC, hm⟩ := hbm t k ht hk
  obtain ⟨g, edge, hsize, hrb, hshape, hdec⟩ :=
    PEqualNP.Outside.L_pcx_464_aux.decoder_exists t k d ht hk hd batch hm C hdC
  dsimp only
  refine ⟨d, batch, g, edge, hd, hdC, hsize, hrb, hshape, ?_⟩
  intro G hG
  refine ⟨fun i => ?_, fun y hy => hdec G hG y hy⟩
  have h1 := PEqualNP.Outside.L_pcx_464_aux.readF_eq t k ht G hG (batch i)
  have h2 := PEqualNP.Outside.L_pcx_464_aux.val_lt t k G.card
    (PEqualNP.Outside.L_pcx_464_aux.cutc (batch i) G) ht
    (PEqualNP.Outside.L_pcx_464_aux.cutc_le (batch i) G) hG
  rw [← h1] at h2
  exact h2
