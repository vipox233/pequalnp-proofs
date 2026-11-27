import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Dual

namespace PEqualNP.Outside.L_lib_448

def sign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

lemma sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  have hadd : ∀ u v : ZMod 2, u + v = 0 ↔ (u = 0 ↔ v = 0) := by decide
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [sign, hadd, ha, hb]

lemma abs_sign (a : ZMod 2) : |sign a| = 1 := by
  unfold sign
  split <;> simp

lemma sum_translate {m : Nat} (j : Fin m) (f : (Fin m → ZMod 2) → ℝ) :
    (∑ k, f (k + (Pi.single j 1 : Fin m → ZMod 2))) = ∑ k, f k :=
  Equiv.sum_comp (Equiv.addRight (Pi.single j 1 : Fin m → ZMod 2)) f

lemma flip_sign {m : Nat} (x k : Fin m → ZMod 2) (j : Fin m) (hj : x j ≠ 0) :
    sign (dotProduct (k + Pi.single j 1) x) = -sign (dotProduct k x) := by
  rw [add_dotProduct, single_one_dotProduct, sign_add]
  have hj' : sign (x j) = -1 := by simp [sign, hj]
  rw [hj', mul_neg_one]

lemma orthogonality {m : Nat} (x : Fin m → ZMod 2) :
    (∑ k : Fin m → ZMod 2, sign (dotProduct k x)) = if x = 0 then (2 : ℝ)^m else 0 := by
  by_cases hx : x = 0
  · subst x
    simp [sign, ZMod.card]
  simp only [hx, ↓reduceIte]
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    exact hx (funext h)
  have h := sum_translate j (fun k => sign (dotProduct k x))
  simp only [flip_sign x _ j hj, Finset.sum_neg_distrib] at h
  exact CharZero.neg_eq_self_iff.mp h

lemma pullback {n m : Nat}
    (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2))
    (hA : Function.Surjective A) {k : Fin m → ZMod 2} (hk : k ≠ 0) :
    ∃ c : Fin n → ZMod 2, c ≠ 0 ∧ ∀ x, dotProduct c x = dotProduct k (A x) := by
  let dual := dotProductEquiv (ZMod 2) (Fin m)
  obtain ⟨c, hc⟩ := (dotProductEquiv (ZMod 2) (Fin n)).surjective ((dual k).comp A)
  have heval (x) : dotProduct c x = dotProduct k (A x) := DFunLike.congr_fun hc x
  refine ⟨c, ?_, heval⟩
  intro hc0
  apply hk
  funext j
  obtain ⟨x, hx⟩ := hA (Pi.single j 1)
  simpa [hc0, hx] using (heval x).symm

end PEqualNP.Outside.L_lib_448

open PEqualNP.Outside.L_lib_448

theorem PEqualNP.Outside.L_lib_448 : (∀ (n m d : Nat) (sample : Fin d → (Fin n → ZMod 2))
    (A : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2)) (E : ℝ),
  Function.Surjective A → 0 ≤ E →
  (∀ c : Fin n → ZMod 2, c ≠ 0 →
    |∑ s : Fin d, (if (∑ j : Fin n, c j * sample s j) = 0 then (1 : ℝ) else -1)| ≤ E) →
  ∀ b : Fin m → ZMod 2,
    |(2:ℝ)^m * ((Finset.univ.filter (fun s : Fin d => A (sample s) = b)).card : ℝ) -
      (d : ℝ)| ≤ ((2:ℝ)^m-1)*E) := by
  classical
  intro n m d sample A E hA _ hbias b
  let coeff (k : Fin m → ZMod 2) := ∑ s, sign (dotProduct k (A (sample s) - b))
  have htotal : (∑ k, coeff k) =
      (2 : ℝ)^m * ((Finset.univ.filter (fun s : Fin d => A (sample s) = b)).card : ℝ) := by
    unfold coeff
    rw [Finset.sum_comm]
    simp_rw [orthogonality, sub_eq_zero]
    rw [← Finset.sum_boole, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hs : A (sample s) = b <;> simp [hs]
  have hzero : coeff 0 = d := by simp [coeff, sign]
  have hbound (k : Fin m → ZMod 2) (hk : k ≠ 0) : |coeff k| ≤ E := by
    obtain ⟨c, hc, heval⟩ := pullback A hA hk
    have hsub : ∀ a b : ZMod 2, a - b = a + b := by decide
    simp only [coeff, dotProduct_sub, hsub, sign_add, ← heval, ← Finset.sum_mul,
      abs_mul, abs_sign, mul_one]
    exact hbias c hc
  let nonzero := (Finset.univ : Finset (Fin m → ZMod 2)).erase 0
  have hrest : (∑ k ∈ nonzero, coeff k) + coeff 0 = ∑ k, coeff k :=
    Finset.sum_erase_add _ _ (Finset.mem_univ _)
  have hcard : (nonzero.card : ℝ) = (2 : ℝ)^m - 1 := by
    simp only [nonzero, Finset.card_erase_of_mem (Finset.mem_univ _)]
    rw [Nat.cast_sub (Finset.card_pos.mpr ⟨0, Finset.mem_univ _⟩)]
    simp [ZMod.card]
  rw [← htotal, ← hrest, hzero, add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ nonzero, |coeff k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ nonzero, E := Finset.sum_le_sum fun k hk => hbound k (Finset.ne_of_mem_erase hk)
    _ = _ := by simp [hcard]
