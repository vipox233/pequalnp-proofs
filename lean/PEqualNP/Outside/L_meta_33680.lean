import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33680

section Part1
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def indR (b : Bool) : ℝ := if b then 1 else 0

def areaR (C : F → F → Bool) : ℝ := ∑ x, ∑ y, indR (C x y)

def interR (C T : F → F → Bool) : ℝ := ∑ x, ∑ y, indR (C x y) * indR (T x y)

def lineR (C : F → F → Bool) (a b : F) : ℝ := ∑ x, indR (C x (a * x + b))

lemma sum_shift_b (g : F → ℝ) (c : F) : ∑ b, g (c + b) = ∑ y, g y :=
  Fintype.sum_equiv (Equiv.addLeft c) _ _ (fun _ => rfl)

lemma sum_b_lineR (C : F → F → Bool) (a : F) : ∑ b, lineR C a b = areaR C := by
  unfold lineR areaR
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun x _ => sum_shift_b (fun y => indR (C x y)) (a * x))

lemma card_filter_R (s : Finset F) (p : F → Bool) :
    ((s.filter (fun x => p x)).card : ℝ) = ∑ x ∈ s, indR (p x) := by
  rw [Finset.card_filter]; push_cast; rfl

lemma row_sum (T : F → F → Bool) (t : ℕ) (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (x : F) : ∑ y, indR (T x y) = t := by
  rw [← card_filter_R, hrow]

lemma col_sum (T : F → F → Bool) (t : ℕ) (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
    (y : F) : ∑ x, indR (T x y) = t := by
  rw [← card_filter_R, hcol]

lemma key_cell (T : F → F → Bool) (t : ℕ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) (x y : F) :
    ∑ a ∈ (Finset.univ : Finset F).erase 0, lineR T a (y - a * x) =
      (Fintype.card F : ℝ) * indR (T x y) + ((Fintype.card F : ℝ) - 2) * t := by
  unfold lineR
  rw [Finset.sum_comm]

  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have h1 : ∑ a ∈ (Finset.univ : Finset F).erase 0, indR (T x (a * x + (y - a * x))) =
      ((Fintype.card F : ℝ) - 1) * indR (T x y) := by
    simp only [add_sub_cancel, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, nsmul_eq_mul]
    rw [Nat.cast_sub Fintype.card_pos]; simp
  have h2 : ∀ x' ∈ (Finset.univ : Finset F).erase x,
      ∑ a ∈ (Finset.univ : Finset F).erase 0, indR (T x' (a * x' + (y - a * x))) =
        t - indR (T x' y) := by
    intro x' hx'
    have hd : x' - x ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hx')
    have hbij : ∑ a ∈ (Finset.univ : Finset F).erase 0, indR (T x' (a * x' + (y - a * x))) =
        ∑ y' ∈ (Finset.univ : Finset F).erase y, indR (T x' y') := by
      apply Finset.sum_nbij' (fun a => y + a * (x' - x)) (fun y' => (y' - y) / (x' - x))
      · intro a ha
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at ha ⊢
        intro h; apply ha
        have : a * (x' - x) = 0 := by linear_combination h
        exact (mul_eq_zero.mp this).resolve_right hd
      · intro y' hy'
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hy' ⊢
        exact div_ne_zero (sub_ne_zero.mpr hy') hd
      · intro a _; field_simp; ring
      · intro y' _; field_simp; ring
      · intro a _; congr 2; ring
    rw [hbij]
    have := row_sum T t hrow x'
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ y)] at this
    linarith
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul]
  have hc := col_sum T t hcol y
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x)] at hc
  rw [Nat.cast_sub Fintype.card_pos]
  push_cast
  linarith

lemma inter_line (C : F → F → Bool) (a b : F) :
    interR C (fun x y => decide (y = a * x + b)) = lineR C a b := by
  unfold interR lineR
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (a * x + b)]
  · simp [indR]
  · intro y _ hy; simp [indR, hy]
  · simp

lemma sum_n_line (T C : F → F → Bool) (t : ℕ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) :
    ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b, lineR T a b * lineR C a b =
      (Fintype.card F : ℝ) * interR C T + ((Fintype.card F : ℝ) - 2) * t * areaR C := by
  have step : ∀ a, ∑ b, lineR T a b * lineR C a b =
      ∑ x, ∑ y, lineR T a (y - a * x) * indR (C x y) := by
    intro a
    simp only [lineR, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← sum_shift_b (fun y => (∑ x', indR (T x' (a * x' + (y - a * x)))) * indR (C x y)) (a * x)]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [add_sub_cancel_left]
  simp only [step]
  rw [Finset.sum_comm]
  simp only [areaR, interR, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.sum_mul, key_cell T t hrow hcol x y]
  ring

lemma part1_one (T C : F → F → Bool) (t : ℕ) (low : F → ℝ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) :
    ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b,
      (lineR T a b - low a) * (areaR C / (Fintype.card F) - lineR C a b) =
      t * areaR C - (Fintype.card F) * interR C T := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsumT : ∀ a, ∑ b, lineR T a b = (Fintype.card F) * t := by
    intro a; rw [sum_b_lineR]; unfold areaR
    simp only [row_sum T t hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have expand : ∀ a, ∑ b, (lineR T a b - low a) * (areaR C / (Fintype.card F) - lineR C a b) =
      (Fintype.card F) * t * (areaR C / (Fintype.card F)) - ∑ b, lineR T a b * lineR C a b := by
    intro a
    have e1 : ∑ b, (lineR T a b - low a) * (areaR C / (Fintype.card F) - lineR C a b) =
        ∑ b, lineR T a b * (areaR C / (Fintype.card F)) - ∑ b, lineR T a b * lineR C a b -
        ∑ _b : F, low a * (areaR C / (Fintype.card F)) + ∑ b, low a * lineR C a b := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [e1, ← Finset.sum_mul, hsumT,
      show ∑ b, low a * lineR C a b = low a * ∑ b, lineR C a b from (Finset.mul_sum _ _ _).symm,
      sum_b_lineR]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun a _ => expand a), Finset.sum_sub_distrib, sum_n_line T C t hrow hcol,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, nsmul_eq_mul,
    Nat.cast_sub Fintype.card_pos]
  field_simp
  push_cast
  ring

end Part1

section Part3
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def cnt (β : F → F) (z : F × F) : ℕ :=
  (((Finset.univ : Finset F).erase 0).filter (fun a => decide (z.2 = a * z.1 + β a))).card

def mu (β : F → F) (z : F × F) : ℕ :=
  Fintype.card F - cnt β z + (if z.1 = 0 then Fintype.card F - 1 else 0)

lemma cnt_le (β : F → F) (z : F × F) : cnt β z ≤ Fintype.card F - 1 := by
  unfold cnt
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

lemma mu_real (β : F → F) (z : F × F) :
    (mu β z : ℝ) = Fintype.card F - cnt β z + (if z.1 = 0 then (Fintype.card F : ℝ) - 1 else 0) := by
  have h1 := cnt_le β z
  have hq : 1 ≤ Fintype.card F := Fintype.card_pos
  unfold mu
  rw [Nat.cast_add, Nat.cast_sub (by omega)]
  split_ifs <;> simp [Nat.cast_sub hq]

lemma line_count (a a' b b' : F) (ha : a' ≠ a) :
    ∑ x : F, indR (decide (a * x + b = a' * x + b')) = 1 := by
  have hd : a - a' ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  rw [Finset.sum_eq_single ((b' - b) / (a - a'))]
  · simp only [indR]; rw [if_pos]; simp only [decide_eq_true_eq]; field_simp; ring
  · intro x _ hx
    simp only [indR, decide_eq_true_eq]
    rw [if_neg]; intro h; apply hx
    field_simp; linear_combination h
  · simp

lemma cnt_line (β : F → F) (a b : F) (ha : a ≠ 0) :
    ∑ x : F, (cnt β (x, a * x + b) : ℝ) =
      ((Fintype.card F : ℝ) - 2) + (Fintype.card F) * indR (decide (b = β a)) := by
  simp only [cnt, card_filter_R]
  rw [Finset.sum_comm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩)]
  have h1 : ∑ x : F, indR (decide (a * x + b = a * x + β a)) =
      (Fintype.card F) * indR (decide (b = β a)) := by
    simp only [add_right_inj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∀ a' ∈ ((Finset.univ : Finset F).erase 0).erase a,
      ∑ x : F, indR (decide (a * x + b = a' * x + β a')) = 1 :=
    fun a' ha' => line_count a a' b (β a') (Finset.ne_of_mem_erase ha')
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ a⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have h2le : 2 ≤ Fintype.card F := Fintype.one_lt_card
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma mu_line (β : F → F) (a b : F) (ha : a ≠ 0) :
    ∑ x : F, (mu β (x, a * x + b) : ℝ) =
      (Fintype.card F : ℝ) ^ 2 + 1 - (Fintype.card F) * indR (decide (b = β a)) := by
  simp only [mu_real, Finset.sum_add_distrib, Finset.sum_sub_distrib, cnt_line β a b ha]
  rw [Finset.sum_ite_eq' Finset.univ (0 : F) (fun _ => (Fintype.card F : ℝ) - 1)]
  simp only [Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma mu_total (β : F → F) : ∑ z : F × F, mu β z = Fintype.card F ^ 3 := by
  have h : (∑ z : F × F, (mu β z : ℝ)) = (Fintype.card F : ℝ) ^ 3 := by
    rw [Fintype.sum_prod_type]
    have : ∀ x : F, ∑ y : F, (mu β (x, y) : ℝ) = ∑ b : F, (mu β (x, 1 * x + b) : ℝ) := by
      intro x
      exact (Fintype.sum_equiv (Equiv.addLeft (1 * x)) _ _ (fun _ => rfl)).symm
    rw [Finset.sum_congr rfl (fun x _ => this x), Finset.sum_comm]
    simp only [mu_line β 1 _ one_ne_zero]
    have hs : ∑ b : F, indR (decide (b = β 1)) = 1 := by simp [indR]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  exact_mod_cast h

end Part3

lemma single_eval {q : ℕ} (u v x y : Fin q) :
    (⟨[⟨.or, [x.val, q + y.val]⟩], q + q⟩ : PEqualNP.CircuitLowerBounds.Circuit).eval
      (PEqualNP.Represents.oneEach u v) = (decide (x = u) || decide (y = v)) := by
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    List.foldl_cons, List.foldl_nil, PEqualNP.Represents.oneEach]
  have hlen : (List.ofFn (fun i : Fin q => decide (i = u)) ++ List.ofFn (fun j : Fin q => decide (j = v))).length = q + q := by
    simp
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_append_right (by simp : (List.ofFn (fun i : Fin q => decide (i = u)) ++
    List.ofFn (fun j : Fin q => decide (j = v))).length ≤ q + q), hlen, Nat.sub_self,
    List.getElem_singleton, List.map_cons, List.map_nil, PEqualNP.CircuitLowerBounds.GateOp.eval,
    List.any_cons, List.any_nil, Bool.or_false, id]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp)]
  rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]
  simp

section Part4
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def ExR {m : ℕ} (tabs : Fin m → F → F → Bool) (w : Fin m → ℝ) (d : ℕ) (B : F → F → Bool) : ℝ :=
  ∑ i, w i * ((((Finset.univ : Finset (F × F)).filter (fun z => tabs i z.1 z.2 ≠ B z.1 z.2)).card : ℝ) -
    (Fintype.card F : ℝ) * (d : ℝ) - (1 - 2 * (d : ℝ) / (Fintype.card F : ℝ)) *
    (((Finset.univ : Finset (F × F)).filter (fun z => tabs i z.1 z.2)).card : ℝ))

lemma areaN_eq (A : F → F → Bool) :
    (((Finset.univ : Finset (F × F)).filter (fun z => A z.1 z.2)).card : ℝ) = areaR A := by
  rw [Finset.card_filter]; push_cast
  rw [Fintype.sum_prod_type]; rfl

lemma lossN_eq (A B : F → F → Bool) :
    (((Finset.univ : Finset (F × F)).filter (fun z => A z.1 z.2 ≠ B z.1 z.2)).card : ℝ) =
      areaR A + areaR B - 2 * interR A B := by
  rw [Finset.card_filter]; push_cast
  rw [Fintype.sum_prod_type]
  simp only [areaR, interR, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  cases A x y <;> cases B x y <;> simp [indR] <;> norm_num

lemma area_reg (T : F → F → Bool) (t : ℕ) (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t) :
    areaR T = (Fintype.card F) * t := by
  unfold areaR; simp [row_sum T t hrow, Finset.card_univ]

lemma area_line (a b : F) : areaR (fun x y => decide (y = a * x + b)) = Fintype.card F := by
  unfold areaR
  have : ∀ x : F, ∑ y : F, indR (decide (y = a * x + b)) = 1 := by
    intro x; simp [indR]
  simp [this, Finset.card_univ]

lemma ExR_T {m : ℕ} (tabs : Fin m → F → F → Bool) (w : Fin m → ℝ) (T : F → F → Bool) (t : ℕ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t) :
    ExR tabs w t T = ∑ i, w i * (2 * t / (Fintype.card F) * areaR (tabs i) - 2 * interR (tabs i) T) := by
  unfold ExR
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [lossN_eq, areaN_eq, area_reg T t hrow]; ring

lemma ExR_line {m : ℕ} (tabs : Fin m → F → F → Bool) (w : Fin m → ℝ) (a b : F) :
    ExR tabs w 1 (fun x y => decide (y = a * x + b)) =
      ∑ i, w i * (2 * (areaR (tabs i) / (Fintype.card F) - lineR (tabs i) a b)) := by
  unfold ExR
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hl := lossN_eq (tabs i) (fun x y => decide (y = a * x + b))
  beta_reduce
  beta_reduce at hl
  rw [hl, areaN_eq, area_line, inter_line]; push_cast; ring

def nF (T : F → F → Bool) (a b : F) : ℕ := (Finset.univ.filter (fun x => T x (a * x + b))).card

def lowF (T : F → F → Bool) (a : F) : ℕ := Finset.univ.inf' Finset.univ_nonempty (nF T a)

lemma nN_eq (T : F → F → Bool) (a b : F) : (nF T a b : ℝ) = lineR T a b := by
  unfold nF; rw [card_filter_R]; rfl

lemma low_le_n (T : F → F → Bool) (a b : F) : lowF T a ≤ nF T a b :=
  Finset.inf'_le _ (Finset.mem_univ b)

lemma part1_E {m : ℕ} (tabs : Fin m → F → F → Bool) (w : Fin m → ℝ) (T : F → F → Bool) (t : ℕ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) :
    ExR tabs w t T = (∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b,
      ((nF T a b - lowF T a : ℕ) : ℝ) * ExR tabs w 1 (fun x y => decide (y = a * x + b))) /
      (Fintype.card F) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hcast : ∀ a b, ((nF T a b - lowF T a : ℕ) : ℝ) = lineR T a b - (lowF T a : ℝ) := by
    intro a b; rw [Nat.cast_sub (low_le_n T a b), nN_eq]
  simp only [hcast, ExR_line, ExR_T tabs w T t hrow]
  simp only [Finset.mul_sum]
  have swap : ∀ (f : F → F → Fin m → ℝ), ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b, ∑ i, f a b i =
      ∑ i, ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b, f a b i := by
    intro f
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  rw [swap, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h := part1_one T (tabs i) t (fun a => (lowF T a : ℝ)) hrow hcol
  have e : ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b,
      (lineR T a b - (lowF T a : ℝ)) * (w i * (2 * (areaR (tabs i) / (Fintype.card F) - lineR (tabs i) a b))) =
      (w i * 2) * ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b,
        (lineR T a b - (lowF T a : ℝ)) * (areaR (tabs i) / (Fintype.card F) - lineR (tabs i) a b) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _ => ?_); ring
  rw [e, h]
  field_simp

lemma sum_n (T : F → F → Bool) (t : ℕ) (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (a : F) : ∑ b, (nF T a b : ℝ) = (Fintype.card F) * t := by
  simp only [nN_eq]; rw [sum_b_lineR, area_reg T t hrow]

lemma low_le (T : F → F → Bool) (t : ℕ) (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (a : F) : lowF T a ≤ t := by
  have hle : ∀ b ∈ (Finset.univ : Finset F), (lowF T a : ℝ) ≤ (nF T a b : ℝ) :=
    fun b _ => by exact_mod_cast low_le_n T a b
  have := Finset.sum_le_sum hle
  rw [sum_n T t hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have : (lowF T a : ℝ) ≤ t := le_of_mul_le_mul_left this hq
  exact_mod_cast this

lemma sum_nlow (T : F → F → Bool) (t : ℕ) (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (a : F) : ∑ b, ((nF T a b - lowF T a : ℕ) : ℝ) = (Fintype.card F) * ((t - lowF T a : ℕ) : ℝ) := by
  rw [Nat.cast_sub (low_le T t hrow a)]
  rw [Finset.sum_congr rfl (fun b _ => Nat.cast_sub (low_le_n T a b))]
  rw [Finset.sum_sub_distrib, sum_n T t hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma part2_E {m : ℕ} (tabs : Fin m → F → F → Bool) (w : Fin m → ℝ) (T : F → F → Bool) (t : ℕ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) (h : ℝ)
    (hb : ∀ a ∈ (Finset.univ : Finset F).erase 0, ∀ b,
      ExR tabs w 1 (fun x y => decide (y = a * x + b)) ≤ h) :
    ExR tabs w t T ≤ ((∑ a ∈ (Finset.univ : Finset F).erase 0, (t - lowF T a) : ℕ) : ℝ) * h := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [part1_E tabs w T t hrow hcol, div_le_iff₀ hq]
  calc _ ≤ ∑ a ∈ (Finset.univ : Finset F).erase 0, ∑ b, ((nF T a b - lowF T a : ℕ) : ℝ) * h := by
        refine Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b _ => ?_))
        exact mul_le_mul_of_nonneg_left (hb a ha b) (Nat.cast_nonneg _)
    _ = _ := by
        simp only [← Finset.sum_mul, sum_nlow T t hrow]
        push_cast
        rw [← Finset.mul_sum]
        ring

end Part4

section Part5
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

def crossT (z : F × F) : F → F → Bool := fun x y => decide (z.1 = x) || decide (z.2 = y)

lemma area_cross (z : F × F) : areaR (crossT z) = 2 * (Fintype.card F : ℝ) - 1 := by
  unfold areaR crossT
  have : ∀ x : F, ∑ y : F, indR (decide (z.1 = x) || decide (z.2 = y)) =
      if z.1 = x then (Fintype.card F : ℝ) else 1 := by
    intro x
    by_cases hx : z.1 = x
    · simp [hx, indR, Finset.card_univ]
    · simp [hx, indR]
  simp only [this]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ z.1), if_pos rfl]
  rw [Finset.sum_congr rfl (fun x hx => if_neg (Ne.symm (Finset.ne_of_mem_erase hx)))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    nsmul_eq_mul, mul_one, Nat.cast_sub Fintype.card_pos]
  push_cast; ring

lemma line_cross (z : F × F) (a b : F) (ha : a ≠ 0) :
    lineR (crossT z) a b = 2 - indR (decide (z.2 = a * z.1 + b)) := by
  unfold lineR crossT
  set xs := (z.2 - b) / a
  have h2 : ∀ x : F, (z.2 = a * x + b) ↔ (x = xs) := by
    intro x
    constructor
    · intro h; simp only [xs]; field_simp; linear_combination -h
    · intro h; rw [h]; simp only [xs]; field_simp; ring
  have e : ∀ x : F, indR (decide (z.1 = x) || decide (z.2 = a * x + b)) =
      if x ∈ ({z.1, xs} : Finset F) then 1 else 0 := by
    intro x
    simp only [indR, Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true, decide_eq_true_eq, h2 x,
      eq_comm (a := z.1)]
  simp only [e]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  by_cases hz : z.1 = xs
  · rw [hz, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton]
    have : z.2 = a * xs + b := (h2 xs).mpr rfl
    simp [indR, this]; norm_num
  · rw [Finset.card_pair hz]
    have : ¬ z.2 = a * z.1 + b := fun h => hz ((h2 z.1).mp h)
    simp [indR, this]

end Part5

section Part6
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

lemma getD_sum (g : F × F → ℝ) (d : F × F) :
    ∀ l : List (F × F), ∑ i ∈ Finset.range l.length, g (l.getD i d) = (l.map g).sum
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← getD_sum g d l]
    simp [add_comm]

noncomputable def zl (β : F → F) : List (F × F) :=
  (Finset.univ : Finset (F × F)).toList.flatMap (fun z => List.replicate (mu β z) z)

lemma flat_len (β : F → F) : ∀ l : List (F × F),
    (l.flatMap (fun z => List.replicate (mu β z) z)).length = (l.map (mu β)).sum
  | [] => by simp
  | a :: l => by simp [List.flatMap_cons, flat_len β l]

lemma flat_sum (β : F → F) (g : F × F → ℝ) : ∀ l : List (F × F),
    ((l.flatMap (fun z => List.replicate (mu β z) z)).map g).sum =
      (l.map (fun z => (mu β z : ℝ) * g z)).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_replicate,
      List.sum_replicate, nsmul_eq_mul, List.map_cons, List.sum_cons, flat_sum β g l]

lemma zl_length (β : F → F) : (zl β).length = Fintype.card F ^ 3 := by
  rw [← mu_total β, zl, flat_len, Finset.sum_map_toList]

lemma sum_enum (β : F → F) (g : F × F → ℝ) :
    ∑ i : Fin (Fintype.card F ^ 3), g ((zl β).getD i.val (0, 0)) = ∑ z, (mu β z : ℝ) * g z := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g ((zl β).getD i (0, 0))), ← zl_length β, getD_sum, zl,
    flat_sum, Finset.sum_map_toList]

lemma mu_sum_line (β : F → F) (a b : F) (ha : a ≠ 0) :
    ∑ z : F × F, (mu β z : ℝ) * indR (decide (z.2 = a * z.1 + b)) =
      (Fintype.card F : ℝ) ^ 2 + 1 - (Fintype.card F) * indR (decide (b = β a)) := by
  rw [Fintype.sum_prod_type, ← mu_line β a b ha]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_eq_single (a * x + b)]
  · simp [indR]
  · intro y _ hy; simp [indR, hy]
  · simp

lemma part3 (e : F ≃ Fin (Fintype.card F)) (T : F → F → Bool) (t : ℕ)
    (hrow : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (hcol : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) :
    ∃ D : Fin (Fintype.card F ^ 3) → PEqualNP.CircuitLowerBounds.Circuit,
      (∀ i, ∃ x y, D i = (⟨[⟨.or, [(e x).val, Fintype.card F + (e y).val]⟩],
        Fintype.card F + Fintype.card F⟩ : PEqualNP.CircuitLowerBounds.Circuit)) ∧
      (∀ a ∈ (Finset.univ : Finset F).erase 0, ∀ b,
        ExR (fun i x y => (D i).eval (PEqualNP.Represents.oneEach (e x) (e y)))
          (fun _ => 1 / (Fintype.card F : ℝ) ^ 3) 1 (fun x y => decide (y = a * x + b)) ≤
          2 / (Fintype.card F : ℝ) ^ 3) ∧
      (∃ a ∈ (Finset.univ : Finset F).erase 0, ∃ b,
        ExR (fun i x y => (D i).eval (PEqualNP.Represents.oneEach (e x) (e y)))
          (fun _ => 1 / (Fintype.card F : ℝ) ^ 3) 1 (fun x y => decide (y = a * x + b)) =
          2 / (Fintype.card F : ℝ) ^ 3) ∧
      ExR (fun i x y => (D i).eval (PEqualNP.Represents.oneEach (e x) (e y)))
          (fun _ => 1 / (Fintype.card F : ℝ) ^ 3) t T =
        ((∑ a ∈ (Finset.univ : Finset F).erase 0, (t - lowF T a) : ℕ) : ℝ) *
          (2 / (Fintype.card F : ℝ) ^ 3) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hβ : ∀ a, ∃ b, nF T a b = lowF T a := fun a => by
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (nF T a)
    exact ⟨b, hb.symm⟩
  choose β hβ using hβ
  let D : Fin (Fintype.card F ^ 3) → PEqualNP.CircuitLowerBounds.Circuit := fun i =>
    ⟨[⟨.or, [(e ((zl β).getD i.val (0, 0)).1).val,
      Fintype.card F + (e ((zl β).getD i.val (0, 0)).2).val]⟩], Fintype.card F + Fintype.card F⟩
  have htab : (fun i x y => (D i).eval (PEqualNP.Represents.oneEach (e x) (e y))) =
      fun i => crossT ((zl β).getD i.val (0, 0)) := by
    funext i x y
    simp only [D, crossT]
    rw [single_eval]
    simp [e.injective.eq_iff]
  refine ⟨D, fun i => ⟨_, _, rfl⟩, ?_⟩
  rw [htab]
  have hE1 : ∀ a ∈ (Finset.univ : Finset F).erase 0, ∀ b,
      ExR (fun i : Fin (Fintype.card F ^ 3) => crossT ((zl β).getD i.val (0, 0)))
        (fun _ => 1 / (Fintype.card F : ℝ) ^ 3) 1
        (fun x y => decide (y = a * x + b)) =
        2 / (Fintype.card F : ℝ) ^ 3 * (1 - (Fintype.card F) * indR (decide (b = β a))) := by
    intro a ha b
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    rw [ExR_line]
    simp only [area_cross, line_cross _ a b ha0]
    rw [sum_enum β (fun z => 1 / (Fintype.card F : ℝ) ^ 3 * (2 * ((2 * (Fintype.card F : ℝ) - 1) /
      (Fintype.card F) - (2 - indR (decide (z.2 = a * z.1 + b))))))]
    have htot : ∑ z : F × F, (mu β z : ℝ) = (Fintype.card F : ℝ) ^ 3 := by exact_mod_cast mu_total β
    have hline := mu_sum_line β a b ha0
    have expand : ∑ z : F × F, (mu β z : ℝ) * (1 / (Fintype.card F : ℝ) ^ 3 *
        (2 * ((2 * (Fintype.card F : ℝ) - 1) / (Fintype.card F) - (2 - indR (decide (z.2 = a * z.1 + b)))))) =
        1 / (Fintype.card F : ℝ) ^ 3 * 2 * (((2 * (Fintype.card F : ℝ) - 1) / (Fintype.card F) - 2) *
          ∑ z : F × F, (mu β z : ℝ) + ∑ z : F × F, (mu β z : ℝ) * indR (decide (z.2 = a * z.1 + b))) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_); ring
    rw [expand, htot, hline]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b
    rw [hE1 a ha b]
    have : 0 ≤ (Fintype.card F : ℝ) * indR (decide (b = β a)) :=
      mul_nonneg hq.le (by unfold indR; split_ifs <;> norm_num)
    have h2 : 0 < 2 / (Fintype.card F : ℝ) ^ 3 := by positivity
    nlinarith
  · refine ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩, β 1 + 1, ?_⟩
    rw [hE1 1 (Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩)]
    have : ¬ (β 1 + 1 = β 1) := by intro h; exact one_ne_zero (by linear_combination h)
    simp [indR, this]
  · rw [part1_E _ _ T t hrow hcol]
    have hterm : ∀ a ∈ (Finset.univ : Finset F).erase 0, ∀ b,
        ((nF T a b - lowF T a : ℕ) : ℝ) * ExR (fun i : Fin (Fintype.card F ^ 3) =>
          crossT ((zl β).getD i.val (0, 0)))
          (fun _ => 1 / (Fintype.card F : ℝ) ^ 3) 1 (fun x y => decide (y = a * x + b)) =
        ((nF T a b - lowF T a : ℕ) : ℝ) * (2 / (Fintype.card F : ℝ) ^ 3) := by
      intro a ha b
      rw [hE1 a ha b]
      by_cases hb : b = β a
      · subst hb; rw [hβ a, Nat.sub_self]; simp
      · simp [indR, hb]
    rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b _ => hterm a ha b))]
    simp only [← Finset.sum_mul, sum_nlow T t hrow]
    push_cast
    rw [← Finset.mul_sum]
    field_simp

end Part6

end PEqualNP.Outside.L_meta_33680

theorem PEqualNP.Outside.L_meta_33680 : (∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
  let q := Fintype.card F
  ∀ e : F ≃ Fin q,
    let G := F → F → Bool
    let Circ := PEqualNP.CircuitLowerBounds.Circuit
    let line := fun (a b x y : F) => decide (y = a*x+b)
    let tab := fun (C : Circ) (x y : F) => C.eval (PEqualNP.Represents.oneEach (e x) (e y))
    let cells := (Finset.univ : Finset (F × F))
    let area := fun (C : Circ) => (cells.filter (fun z => tab C z.1 z.2)).card
    let loss := fun (C : Circ) (T : G) => (cells.filter (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
    let excess := fun {m : ℕ} (D : Fin m → Circ) (w : Fin m → ℝ) (d : ℕ) (T : G) =>
      ∑ i, w i * ((loss (D i) T : ℝ) - (q : ℝ)*(d : ℝ) - (1-2*(d : ℝ)/(q : ℝ))*(area (D i) : ℝ))
    let single := fun (x y : F) => (⟨[⟨.or, [(e x).val, q+(e y).val]⟩], q+q⟩ : Circ)
    ∀ (t : ℕ) (T : G),
      (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) →
      (∀ y, (Finset.univ.filter (fun x => T x y)).card = t) →
      let n := fun (a b : F) => (Finset.univ.filter (fun x => T x (a*x+b))).card
      let low := fun (a : F) => Finset.univ.inf' Finset.univ_nonempty (n a)
      let slopes := (Finset.univ : Finset F).erase 0
      let K := ∑ a ∈ slopes, (t-low a)
      (∀ (m : ℕ) (D : Fin m → Circ) (w : Fin m → ℝ),
        (∀ i, 0 ≤ w i) → (∑ i, w i) = 1 →
        let E := excess D w
        E t T = (∑ a ∈ slopes, ∑ b, ((n a b - low a : ℕ) : ℝ)*E 1 (line a b))/(q : ℝ) ∧
        ∀ h : ℝ, 0 ≤ h → (∀ a ∈ slopes, ∀ b, E 1 (line a b) ≤ h) → E t T ≤ (K : ℝ)*h) ∧
      ∃ D : Fin (q^3) → Circ, (∀ i, ∃ x y, D i = single x y) ∧
        let E := excess D (fun _ => 1/(q : ℝ)^3)
        let h := 2/(q : ℝ)^3
        (∀ a ∈ slopes, ∀ b, E 1 (line a b) ≤ h) ∧
        (∃ a ∈ slopes, ∃ b, E 1 (line a b) = h) ∧ E t T = (K : ℝ)*h) := by
  intro F _ _ _ q e G Circ line tab cells area loss excess single t T hrow hcol n low slopes K
  exact ⟨fun m D w _ _ => ⟨PEqualNP.Outside.L_meta_33680.part1_E (fun i => tab (D i)) w T t hrow hcol,
    fun h _ hb => PEqualNP.Outside.L_meta_33680.part2_E (fun i => tab (D i)) w T t hrow hcol h hb⟩,
    PEqualNP.Outside.L_meta_33680.part3 e T t hrow hcol⟩
