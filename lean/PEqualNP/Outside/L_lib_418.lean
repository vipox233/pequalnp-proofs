import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_418_aux

theorem s_add (s : ZMod 2 → ℤ) (hs : ∀ v, s v = if v = 0 then 1 else -1) (v w : ZMod 2) :
    s (v + w) = s v * s w := by
  rw [hs, hs v, hs w]
  revert v w
  decide

theorem s_sum {ι : Type*} (s : ZMod 2 → ℤ) (hs : ∀ v, s v = if v = 0 then 1 else -1)
    (S : Finset ι) (f : ι → ZMod 2) : s (∑ i ∈ S, f i) = ∏ i ∈ S, s (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [hs]
  | insert j S hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, s_add s hs, ih]

theorem s_one_dim (s : ZMod 2 → ℤ) (hs : ∀ v, s v = if v = 0 then 1 else -1) (x : ZMod 2) :
    ∑ t : ZMod 2, s (t * x) = if x = 0 then 2 else 0 := by
  simp only [hs]
  revert x
  decide

theorem orth (s : ZMod 2 → ℤ) (hs : ∀ v, s v = if v = 0 then 1 else -1) (m : ℕ)
    (w : Fin m → ZMod 2) :
    ∑ b : Fin m → ZMod 2, s (dotProduct b w) = if w = 0 then 2 ^ m else 0 := by
  classical
  have h1 : ∀ b : Fin m → ZMod 2, s (dotProduct b w) = ∏ i, s (b i * w i) := by
    intro b
    exact s_sum s hs Finset.univ (fun i => b i * w i)
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun i t => s (t * w i))]
  simp_rw [s_one_dim s hs]
  by_cases hw : w = 0
  · subst hw
    simp
  · simp only [hw, ↓reduceIte]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
    simp only [Pi.zero_apply] at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem add_eq_zero_iff' (m : ℕ) (x y : Fin m → ZMod 2) : x + y = 0 ↔ x = y := by
  rw [add_eq_zero_iff_neg_eq]
  have : -x = x := funext fun i => ZMod.neg_eq_self_mod_two (x i)
  rw [this]

theorem main (n m k : ℕ) (s : ZMod 2 → ℤ) (hs : ∀ v, s v = if v = 0 then 1 else -1)
    (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (G : (Fin m → ZMod 2) → (Fin k → ZMod 2))
    (a : Fin n → ZMod 2) (c : Fin k → ZMod 2) :
    (2:ℤ)^m * (∑ x : Fin n → ZMod 2, s (dotProduct a x + dotProduct c (G (F x)))) =
      ∑ b : Fin m → ZMod 2, (∑ u : Fin n → ZMod 2, s (dotProduct a u + dotProduct b (F u))) *
        ∑ v : Fin m → ZMod 2, s (dotProduct b v + dotProduct c (G v)) := by
  classical
  have key : ∀ (b : Fin m → ZMod 2) (u : Fin n → ZMod 2) (v : Fin m → ZMod 2),
      s (dotProduct a u + dotProduct b (F u)) * s (dotProduct b v + dotProduct c (G v)) =
        s (dotProduct a u + dotProduct c (G v)) * s (dotProduct b (F u + v)) := by
    intro b u v
    rw [dotProduct_add]
    simp only [s_add s hs]
    ring
  calc (2:ℤ)^m * (∑ x : Fin n → ZMod 2, s (dotProduct a x + dotProduct c (G (F x))))
      = ∑ u : Fin n → ZMod 2, ∑ v : Fin m → ZMod 2,
          s (dotProduct a u + dotProduct c (G v)) * (if F u = v then (2:ℤ)^m else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        ring
    _ = ∑ u : Fin n → ZMod 2, ∑ v : Fin m → ZMod 2,
          s (dotProduct a u + dotProduct c (G v)) *
            ∑ b : Fin m → ZMod 2, s (dotProduct b (F u + v)) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        simp only [orth s hs, add_eq_zero_iff']
    _ = ∑ u : Fin n → ZMod 2, ∑ b : Fin m → ZMod 2, ∑ v : Fin m → ZMod 2,
          s (dotProduct a u + dotProduct b (F u)) * s (dotProduct b v + dotProduct c (G v)) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp_rw [key, Finset.mul_sum]
        exact Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]

end PEqualNP.Outside.L_lib_418_aux

theorem PEqualNP.Outside.L_lib_418 : (∀ n m k : ℕ,
  let X := Fin n → ZMod 2
  let Y := Fin m → ZMod 2
  let Z := Fin k → ZMod 2
  let s := fun (v : ZMod 2) => if v = 0 then (1 : ℤ) else -1
  ∀ (F : X → Y) (G : Y → Z) (a : X) (c : Z),
    (2:ℤ)^m * (∑ x : X, s (dotProduct a x + dotProduct c (G (F x)))) =
      ∑ b : Y, (∑ u : X, s (dotProduct a u + dotProduct b (F u))) *
        ∑ v : Y, s (dotProduct b v + dotProduct c (G v))) := by
  intro n m k X Y Z s F G a c
  exact PEqualNP.Outside.L_lib_418_aux.main n m k s (fun _ => rfl) F G a c
