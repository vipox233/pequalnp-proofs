import Mathlib

namespace PEqualNP.Outside.L_lib_635_aux

def sg (v : Bool) : ℤ := if v then -1 else 1

theorem sg_sq (v : Bool) : sg v * sg v = 1 := by cases v <;> simp [sg]

theorem lemA (N m : ℕ) (H : Fin N → Fin N → Bool)
    (horth : ∀ a b, (∑ y : Fin N, sg (H a y) * sg (H b y)) = if a = b then (N : ℤ) else 0)
    (row : Fin N → Fin m) (Q : Fin N → Bool) (p p' : Fin m) :
    ∑ y : Fin N, (∑ x : Fin N, if row x = p then sg (Q x) * sg (H x y) else 0) *
      (∑ x : Fin N, if row x = p' then sg (Q x) * sg (H x y) else 0) =
    if p = p' then (N : ℤ) * ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card else 0 := by
  have e : ∀ (q : Fin m) (x y : Fin N), (if row x = q then sg (Q x) * sg (H x y) else 0) =
      (if row x = q then sg (Q x) else 0) * sg (H x y) := by
    intro q x y; split_ifs <;> simp
  simp only [e]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have e2 : ∀ x : Fin N, ∑ y : Fin N, ∑ x' : Fin N, (if row x = p then sg (Q x) else 0) * sg (H x y) *
      ((if row x' = p' then sg (Q x') else 0) * sg (H x' y)) =
      (if row x = p then sg (Q x) else 0) * (if row x = p' then sg (Q x) else 0) * N := by
    intro x
    rw [Finset.sum_comm]
    have e3 : ∀ x' : Fin N, ∑ y : Fin N, (if row x = p then sg (Q x) else 0) * sg (H x y) *
        ((if row x' = p' then sg (Q x') else 0) * sg (H x' y)) =
        (if row x = p then sg (Q x) else 0) * (if row x' = p' then sg (Q x') else 0) *
          (if x = x' then (N : ℤ) else 0) := by
      intro x'
      rw [← horth x x', Finset.mul_sum]
      refine Finset.sum_congr rfl (fun y _ => ?_)
      ring
    rw [Finset.sum_congr rfl (fun x' _ => e3 x')]
    simp
  rw [Finset.sum_congr rfl (fun x _ => e2 x)]
  by_cases hpp : p = p'
  · subst hpp
    rw [if_pos rfl, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    split_ifs <;> simp [sg_sq]
  · rw [if_neg hpp]
    apply Finset.sum_eq_zero
    intro x _
    split_ifs with h1 h2 <;> simp_all

theorem lemB (N m : ℕ) (H : Fin N → Fin N → Bool) (row col : Fin N → Fin m) (Q R : Fin N → Bool)
    (D : Fin m → Fin m → Bool) :
    ∑ p : Fin m, ∑ y : Fin N, (∑ x : Fin N, if row x = p then sg (Q x) * sg (H x y) else 0) *
      (sg (R y) * sg (D p (col y))) =
    ∑ x : Fin N, ∑ y : Fin N, sg (H x y) * sg (Q x) * sg (R y) * sg (D (row x) (col y)) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, y]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  ring

theorem sqexp (a h : ℤ) (u v : Bool) :
    (a - h * sg u * sg v)^2 = a*a - 2*h*(a*(sg u * sg v)) + h^2 := by
  have h1 := sg_sq u
  have h2 := sg_sq v
  linear_combination h^2 * (sg v * sg v) * h1 + h^2 * h2

theorem part1 (m h : ℕ) (H : Fin (m*h^2) → Fin (m*h^2) → Bool)
    (horth : ∀ a b, (∑ y : Fin (m*h^2), sg (H a y) * sg (H b y)) = if a = b then ((m*h^2 : ℕ) : ℤ) else 0)
    (row col : Fin (m*h^2) → Fin m) (Q R : Fin (m*h^2) → Bool) (D : Fin m → Fin m → Bool) :
    (∑ p : Fin m, ∑ y : Fin (m*h^2),
      ((∑ x : Fin (m*h^2), if row x = p then sg (Q x) * sg (H x y) else 0) -
        (h : ℤ) * sg (R y) * sg (D p (col y)))^2) +
      2*(h : ℤ) * (∑ x : Fin (m*h^2), ∑ y : Fin (m*h^2),
        sg (H x y) * sg (Q x) * sg (R y) * sg (D (row x) (col y))) = 2*((m*h^2 : ℕ) : ℤ)^2 := by
  simp only [sqexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← lemB]
  simp only [← Finset.mul_sum]
  simp only [lemA (m*h^2) m H horth row Q, if_true]
  have hc : ∑ p : Fin m, (((Finset.univ : Finset (Fin (m*h^2))).filter (fun x => row x = p)).card : ℤ) =
      ((m*h^2 : ℕ) : ℤ) := by
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)]
    simp
  rw [← Finset.mul_sum, hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

theorem colsum (N m : ℕ) (col : Fin N → Fin m) (f : Fin m → ℤ) :
    ∑ y : Fin N, f (col y) =
      ∑ v : Fin m, (((Finset.univ : Finset (Fin N)).filter (fun y => col y = v)).card : ℤ) * f v := by
  rw [← Finset.sum_fiberwise' Finset.univ col f]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

theorem matpart (m : ℕ) (N : ℚ) (hN : N ≠ 0) (c : Fin m → ℚ) (M : Matrix (Fin m) (Fin m) ℚ)
    (h : M * Matrix.diagonal c * M.transpose = N • 1) :
    Matrix.diagonal c * (M.transpose * M) = N • 1 := by
  have h1 : M * (N⁻¹ • (Matrix.diagonal c * M.transpose)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, inv_mul_cancel₀ hN, one_smul]
  have h2 := mul_eq_one_comm.mp h1
  rw [Matrix.smul_mul] at h2
  have h3 := congrArg (fun A => N • A) h2
  simp only [smul_smul, mul_inv_cancel₀ hN, one_smul] at h3
  rw [← Matrix.mul_assoc]
  exact h3

theorem main (m h : ℕ) (hm : 0 < m) (hh : 0 < h) (H : Fin (m*h^2) → Fin (m*h^2) → Bool)
    (horth : ∀ a b, (∑ y : Fin (m*h^2), sg (H a y) * sg (H b y)) = if a = b then ((m*h^2 : ℕ) : ℤ) else 0)
    (row col : Fin (m*h^2) → Fin m) (Q R : Fin (m*h^2) → Bool) (D : Fin m → Fin m → Bool)
    (hC : (h : ℤ) * (∑ x : Fin (m*h^2), ∑ y : Fin (m*h^2),
        sg (H x y) * sg (Q x) * sg (R y) * sg (D (row x) (col y))) = ((m*h^2 : ℕ) : ℤ)^2) :
    (∀ p, ((Finset.univ : Finset (Fin (m*h^2))).filter (fun x => row x = p)).card = h^2 ∧
          ((Finset.univ : Finset (Fin (m*h^2))).filter (fun y => col y = p)).card = h^2) ∧
      ∀ a b, (∑ v : Fin m, sg (D a v) * sg (D b v)) = if a = b then (m : ℤ) else 0 := by
  have P := part1 m h H horth row col Q R D
  have hz : ∑ p : Fin m, ∑ y : Fin (m*h^2),
      ((∑ x : Fin (m*h^2), if row x = p then sg (Q x) * sg (H x y) else 0) -
        (h : ℤ) * sg (R y) * sg (D p (col y)))^2 = 0 := by linarith
  have hS : ∀ p y, (∑ x : Fin (m*h^2), if row x = p then sg (Q x) * sg (H x y) else 0) =
      (h : ℤ) * sg (R y) * sg (D p (col y)) := by
    intro p y
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Finset.sum_nonneg
      (fun y _ => sq_nonneg _))).mp hz p (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg _)).mp h1 y (Finset.mem_univ _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  have hNpos : (0 : ℤ) < ((m*h^2 : ℕ) : ℤ) := by positivity
  have hpp : ∀ p p', ∑ y : Fin (m*h^2), sg (D p (col y)) * sg (D p' (col y)) * (h : ℤ)^2 =
      if p = p' then ((m*h^2 : ℕ) : ℤ) *
        ((Finset.univ : Finset (Fin (m*h^2))).filter (fun x => row x = p)).card else 0 := by
    intro p p'
    rw [← lemA (m*h^2) m H horth row Q p p']
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [hS, hS]
    have := sg_sq (R y)
    linear_combination (-(h : ℤ)^2 * sg (D p (col y)) * sg (D p' (col y))) * this
  have hrow : ∀ p, ((Finset.univ : Finset (Fin (m*h^2))).filter (fun x => row x = p)).card = h^2 := by
    intro p
    have e := hpp p p
    rw [if_pos rfl] at e
    simp only [sg_sq, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e
    have : (((Finset.univ : Finset (Fin (m*h^2))).filter (fun x => row x = p)).card : ℤ) = (h : ℤ)^2 := by
      have hN0 : ((m*h^2 : ℕ) : ℤ) ≠ 0 := ne_of_gt hNpos
      have := mul_left_cancel₀ hN0 e.symm
      exact this
    exact_mod_cast this
  have hDD : ∀ a b, ∑ y : Fin (m*h^2), sg (D a (col y)) * sg (D b (col y)) =
      if a = b then ((m*h^2 : ℕ) : ℤ) else 0 := by
    intro a b
    have e := hpp a b
    rw [← Finset.sum_mul] at e
    have hh2 : (h : ℤ)^2 ≠ 0 := by positivity
    by_cases hab : a = b
    · subst hab
      simp [sg_sq]
    · rw [if_neg hab] at e ⊢
      exact (mul_eq_zero.mp e).resolve_right hh2
  set c : Fin m → ℕ := fun v => ((Finset.univ : Finset (Fin (m*h^2))).filter (fun y => col y = v)).card
    with hc
  have hDC : ∀ a b, ∑ v : Fin m, (c v : ℤ) * (sg (D a v) * sg (D b v)) =
      if a = b then ((m*h^2 : ℕ) : ℤ) else 0 := by
    intro a b
    rw [← hDD a b, colsum (m*h^2) m col (fun v => sg (D a v) * sg (D b v))]
  let M : Matrix (Fin m) (Fin m) ℚ := Matrix.of (fun a v => (sg (D a v) : ℚ))
  have hMat : M * Matrix.diagonal (fun v => (c v : ℚ)) * M.transpose = ((m*h^2 : ℕ) : ℚ) • 1 := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, M]
    have e := congrArg (fun z : ℤ => (z : ℚ)) (hDC a b)
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast] at e
    rw [Finset.sum_congr rfl (fun v _ => show (sg (D a v) : ℚ) * (c v : ℚ) * (sg (D b v) : ℚ) =
      (c v : ℚ) * ((sg (D a v) : ℚ) * (sg (D b v) : ℚ)) by ring), e]
    split_ifs <;> simp
  have hN : ((m*h^2 : ℕ) : ℚ) ≠ 0 := by positivity
  have hmp := matpart m _ hN _ M hMat
  have hcol : ∀ v, c v = h^2 := by
    intro v
    have e := congrFun (congrFun hmp v) v
    rw [Matrix.diagonal_mul, Matrix.mul_apply] at e
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, if_true,
      smul_eq_mul, mul_one, M] at e
    have hs : ∀ a, (sg (D a v) : ℚ) * (sg (D a v) : ℚ) = 1 := by
      intro a; exact_mod_cast sg_sq (D a v)
    simp only [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at e
    have hm0 : (m : ℚ) ≠ 0 := by positivity
    have : (c v : ℚ) = (h : ℚ)^2 := by
      apply mul_right_cancel₀ hm0
      rw [e]; push_cast; ring
    exact_mod_cast this
  refine ⟨fun p => ⟨hrow p, hcol p⟩, fun a b => ?_⟩
  have e := hDC a b
  simp only [hcol] at e
  rw [← Finset.mul_sum] at e
  have hh2 : ((h^2 : ℕ) : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hh2
  rw [e]
  split_ifs <;> push_cast <;> ring

end PEqualNP.Outside.L_lib_635_aux

theorem PEqualNP.Outside.L_lib_635 : ∀ m h : ℕ, 0 < m → 0 < h →
  let N := m*h^2
  let sign := fun (v : Bool) => if v then (-1 : ℤ) else 1
  ∀ (H : Fin N → Fin N → Bool),
  (∀ a b, (∑ y : Fin N, sign (H a y) * sign (H b y)) =
    if a = b then (N : ℤ) else 0) →
  ∀ (row col : Fin N → Fin m) (Q R : Fin N → Bool) (D : Fin m → Fin m → Bool),
    let corr := ∑ x : Fin N, ∑ y : Fin N,
      sign (H x y) * sign (Q x) * sign (R y) * sign (D (row x) (col y))
    let S := fun (p : Fin m) (v : Fin N) =>
      ∑ x : Fin N, if row x = p then sign (Q x) * sign (H x v) else 0
    ((∑ p : Fin m, ∑ y : Fin N,
      (S p y - (h : ℤ) * sign (R y) * sign (D p (col y)))^2) +
      2*(h : ℤ)*corr = 2*(N : ℤ)^2) ∧
    ((h : ℤ)*corr = (N : ℤ)^2 →
      (∀ p, ((Finset.univ : Finset (Fin N)).filter (fun x => row x = p)).card = h^2 ∧
            ((Finset.univ : Finset (Fin N)).filter (fun y => col y = p)).card = h^2) ∧
      ∀ a b, (∑ v : Fin m, sign (D a v)*sign (D b v)) =
        if a = b then (m : ℤ) else 0) := by
  intro m h hm hh N sign H horth row col Q R D corr S
  exact ⟨PEqualNP.Outside.L_lib_635_aux.part1 m h H horth row col Q R D,
    fun hC => PEqualNP.Outside.L_lib_635_aux.main m h hm hh H horth row col Q R D hC⟩
