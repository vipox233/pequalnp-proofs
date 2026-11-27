import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_419_aux

private def sgn (bit : ZMod 2) : ℤ := if bit = 0 then 1 else -1

private lemma sgn_add (u v : ZMod 2) : sgn (u + v) = sgn u * sgn v := by
  fin_cases u <;> fin_cases v <;> decide

private lemma add_self_zmod2 {n : ℕ} (x d : Fin n → ZMod 2) : x + (x + d) = d := by
  funext i
  change x i + (x i + d i) = d i
  have h0 : x i + x i = 0 := by
    generalize x i = u
    fin_cases u <;> decide
  rw [← add_assoc, h0, zero_add]

end PEqualNP.Outside.L_lib_419_aux

theorem PEqualNP.Outside.L_lib_419 : (∀ n m : ℕ,
  let X := Fin n → ZMod 2
  let Y := Fin m → ZMod 2
  let s := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ F : X → Y,
    let count := fun (d : X) (e : Y) =>
      ((Finset.univ.filter (fun x : X => F (x+d) + F x = e)).card : ℤ)
    ∀ (a : X) (b : Y),
      (∑ d : X, ∑ e : Y, count d e * s (dotProduct a d + dotProduct b e)) =
        (∑ x : X, s (dotProduct a x + dotProduct b (F x)))^2) := by
  intro n m X Y s F count a b
  have hs : ∀ u v : ZMod 2, s (u + v) = s u * s v := PEqualNP.Outside.L_lib_419_aux.sgn_add
  have h1 : ∀ d : X,
      (∑ e : Y, count d e * s (dotProduct a d + dotProduct b e)) =
        ∑ x : X, s (dotProduct a d + dotProduct b (F (x + d) + F x)) := by
    intro d
    calc
      ∑ e : Y, count d e * s (dotProduct a d + dotProduct b e)
          = ∑ e : Y, ∑ x : X,
              if F (x + d) + F x = e then s (dotProduct a d + dotProduct b e) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro e _
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = ∑ x : X, ∑ e : Y,
              if F (x + d) + F x = e then s (dotProduct a d + dotProduct b e) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ x : X, s (dotProduct a d + dotProduct b (F (x + d) + F x)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ x : X,
      (∑ d : X, s (dotProduct a d + dotProduct b (F (x + d) + F x))) =
        ∑ y : X, s (dotProduct a (x + y) + dotProduct b (F y + F x)) := by
    intro x
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ ?_
    intro d
    change s (dotProduct a d + dotProduct b (F (x + d) + F x)) =
      s (dotProduct a (x + (x + d)) + dotProduct b (F (x + d) + F x))
    rw [PEqualNP.Outside.L_lib_419_aux.add_self_zmod2]
  simp_rw [h2]
  have h3 : ∀ x y : X,
      s (dotProduct a (x + y) + dotProduct b (F y + F x)) =
        s (dotProduct a x + dotProduct b (F x)) * s (dotProduct a y + dotProduct b (F y)) := by
    intro x y
    rw [dotProduct_add, dotProduct_add]
    have hcomm : dotProduct a x + dotProduct a y + (dotProduct b (F y) + dotProduct b (F x)) =
        (dotProduct a x + dotProduct b (F x)) + (dotProduct a y + dotProduct b (F y)) := by ring
    rw [hcomm, hs]
  simp_rw [h3, ← Finset.mul_sum, ← Finset.sum_mul, sq]
