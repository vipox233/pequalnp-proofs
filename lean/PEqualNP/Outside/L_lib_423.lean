import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_423

def sgn (bit : ZMod 2) : ℤ := if bit = 0 then 1 else -1

lemma sgn_add (p q : ZMod 2) : sgn (p + q) = sgn p * sgn q := by
  fin_cases p <;> fin_cases q <;> decide

lemma sum_sgn_dot {k : ℕ} (w : Fin k → ZMod 2) :
    (∑ b : Fin k → ZMod 2, sgn (dotProduct b w)) = if w = 0 then (2:ℤ)^k else 0 := by
  split_ifs with hw
  · subst hw
    simp [sgn]
  · obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; exact hw (funext fun j => not_not.mp fun hj => h ⟨j, hj⟩)
    have hi1 : w i = 1 := by
      have key : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      exact key _ hi
    set S := ∑ b : Fin k → ZMod 2, sgn (dotProduct b w) with hS
    have : S = -S := by
      calc S = ∑ b : Fin k → ZMod 2, sgn (dotProduct (b + Pi.single i 1) w) :=
            (Fintype.sum_equiv (Equiv.addRight (Pi.single i 1)) _ _ (fun _ => rfl)).symm
        _ = ∑ b : Fin k → ZMod 2, -sgn (dotProduct b w) := by
            refine Finset.sum_congr rfl (fun b _ => ?_)
            rw [add_dotProduct, sgn_add, single_dotProduct, hi1]
            simp [sgn]
        _ = -S := by rw [Finset.sum_neg_distrib]
    omega

end PEqualNP.Outside.L_lib_423

theorem PEqualNP.Outside.L_lib_423 : (∀ r k : ℕ,
  let P := Fin r → ZMod 2
  let T := Fin k → ZMod 2
  let sign := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ (h : P → T → ℤ) (a : P),
    (∑ b : T, (∑ x : P, ∑ y : T, h x y * sign (dotProduct a x + dotProduct b y))^2) =
      (2:ℤ)^k * ∑ u : P, ∑ v : P, ∑ y : T,
        h u y * h v y * sign (dotProduct a (u+v))) := by
  intro r k P T sign h a
  change (∑ b : T, (∑ x : P, ∑ y : T, h x y * L_lib_423.sgn (dotProduct a x + dotProduct b y))^2) =
      (2:ℤ)^k * ∑ u : P, ∑ v : P, ∑ y : T, h u y * h v y * L_lib_423.sgn (dotProduct a (u+v))
  calc (∑ b : T, (∑ x : P, ∑ y : T, h x y * L_lib_423.sgn (dotProduct a x + dotProduct b y))^2)
      = ∑ b : T, ∑ x : P, ∑ u : P, ∑ y : T, ∑ z : T,
          h x y * h u z * L_lib_423.sgn (dotProduct a (x + u)) * L_lib_423.sgn (dotProduct b (y + z)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun u _ => ?_))
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))
        rw [dotProduct_add, dotProduct_add, L_lib_423.sgn_add, L_lib_423.sgn_add, L_lib_423.sgn_add, L_lib_423.sgn_add]
        ring
    _ = ∑ x : P, ∑ u : P, ∑ y : T, ∑ z : T,
          h x y * h u z * L_lib_423.sgn (dotProduct a (x + u)) * ∑ b : T, L_lib_423.sgn (dotProduct b (y + z)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun z _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ x : P, ∑ u : P, ∑ y : T, ∑ z : T,
          (if y = z then h x y * h u z * L_lib_423.sgn (dotProduct a (x + u)) * (2:ℤ)^k else 0) := by
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun u _ =>
          Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun z _ => ?_))))
        rw [L_lib_423.sum_sgn_dot]
        have hz : -z = z := funext fun j => ZMod.neg_eq_self_mod_two (z j)
        have hiff : (y + z = 0) ↔ y = z := by rw [add_eq_zero_iff_eq_neg, hz]
        by_cases hyz : y = z
        · rw [if_pos (hiff.mpr hyz), if_pos hyz]
        · rw [if_neg (mt hiff.mp hyz), if_neg hyz, mul_zero]
    _ = (2:ℤ)^k * ∑ u : P, ∑ v : P, ∑ y : T, h u y * h v y * L_lib_423.sgn (dotProduct a (u+v)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun y _ => ?_)
        rw [Finset.sum_ite_eq]
        simp only [Finset.mem_univ, ite_true]
        ring
