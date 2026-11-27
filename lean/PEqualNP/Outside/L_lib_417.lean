import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_417_aux

theorem s_add (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (b c : ZMod 2) :
    s (b + c) = s b * s c := by
  rw [hs, hs, hs]
  fin_cases b <;> fin_cases c <;> decide

theorem char_sum (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (n : ℕ)
    (z : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, s (dotProduct a z) = if z = 0 then (2 : ℤ) ^ n else 0 := by
  split_ifs with hz
  · subst hz
    simp only [dotProduct_zero, hs, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    have hzi : z i = 1 := by
      have h2 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      exact h2 _ hi
    let e : Fin n → ZMod 2 := Pi.single i 1
    have hez : dotProduct e z = 1 := by
      simp only [e, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, hzi]
    have key : ∀ a : Fin n → ZMod 2, s (dotProduct (a + e) z) = - s (dotProduct a z) := by
      intro a
      rw [add_dotProduct, s_add s hs, hez, hs 1]
      simp
    have h := Fintype.sum_equiv (Equiv.addRight e) (fun a => s (dotProduct (a + e) z))
      (fun a => s (dotProduct a z)) (fun a => rfl)
    simp only [key, Finset.sum_neg_distrib] at h
    linarith

theorem ortho (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (n : ℕ)
    (x y : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, s (dotProduct a x) * s (dotProduct a y) =
      if x = y then (2 : ℤ) ^ n else 0 := by
  have h1 : ∀ a : Fin n → ZMod 2, s (dotProduct a x) * s (dotProduct a y) = s (dotProduct a (x + y)) := by
    intro a
    rw [dotProduct_add, s_add s hs]
  simp only [h1]
  rw [char_sum s hs n (x + y)]
  have h2 : ∀ t u : ZMod 2, t + u = 0 ↔ t = u := by decide
  have h3 : (x + y = 0) ↔ (x = y) := by
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h2]
  simp only [h3]

end PEqualNP.Outside.L_lib_417_aux

open PEqualNP.Outside.L_lib_417_aux in
theorem PEqualNP.Outside.L_lib_417 : (∀ n : ℕ,
  let V := Fin n → ZMod 2
  let sign := fun (b : ZMod 2) => if b = 0 then (1 : ℤ) else -1
  let W := fun (h : V → ℤ) (a : V) => ∑ x : V, h x * sign (dotProduct a x)
  ∀ f g : V → ℤ,
    (∀ y : V, W (W f) y = (2:ℤ)^n * f y) ∧
    (∑ u : V, W f u * W g u) = (2:ℤ)^n * ∑ v : V, f v * g v) := by
  intro n V sign W f g
  have hs : ∀ b, sign b = if b = 0 then 1 else -1 := fun b => rfl
  have P1 : ∀ y : V, W (W f) y = (2:ℤ)^n * f y := by
    intro y
    show ∑ a : V, (∑ x : V, f x * sign (dotProduct a x)) * sign (dotProduct y a) = _
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have inner : ∀ x : V, ∑ a : V, f x * sign (dotProduct a x) * sign (dotProduct y a) =
        f x * (if x = y then (2:ℤ)^n else 0) := by
      intro x
      rw [← ortho sign hs n x y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [dotProduct_comm y a]
      ring
    simp only [inner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  refine ⟨P1, ?_⟩
  calc ∑ u : V, W f u * W g u
      = ∑ u : V, ∑ v : V, W f u * (g v * sign (dotProduct u v)) := by
        apply Finset.sum_congr rfl
        intro u _
        exact Finset.mul_sum _ _ _
    _ = ∑ v : V, g v * ∑ u : V, W f u * sign (dotProduct v u) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [dotProduct_comm v u]
        ring
    _ = ∑ v : V, g v * W (W f) v := rfl
    _ = ∑ v : V, g v * ((2:ℤ)^n * f v) := by simp only [P1]
    _ = (2:ℤ)^n * ∑ v : V, f v * g v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v _
        ring
