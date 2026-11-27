import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_421_aux

def sg (bit : ZMod 2) : ℤ := if bit = 0 then 1 else -1

theorem sg_add (u t : ZMod 2) : sg (u + t) = sg u * sg t := by
  unfold sg; revert u t; decide

theorem sg_add_one (u : ZMod 2) : sg (u + 1) = - sg u := by
  rw [sg_add]; unfold sg; revert u; decide

theorem sum_char (m : ℕ) (c : Fin m → ZMod 2) :
    (∑ x : Fin m → ZMod 2, sg (dotProduct x c)) = if c = 0 then (2:ℤ) ^ m else 0 := by
  split_ifs with h
  · subst h
    simp [sg]
  · obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra hne
      exact h (funext fun j => by_contra fun hj => hne ⟨j, hj⟩)
    have hci : c i = 1 := by
      revert hi; generalize c i = z; revert z; decide

    have key : ∀ x : Fin m → ZMod 2,
        sg (dotProduct (x + Pi.single i 1) c) = - sg (dotProduct x c) := by
      intro x
      rw [add_dotProduct, single_dotProduct, one_mul, hci, sg_add_one]
    have hS : (∑ x : Fin m → ZMod 2, sg (dotProduct x c)) =
        ∑ x : Fin m → ZMod 2, sg (dotProduct (x + Pi.single i 1) c) :=
      (Equiv.sum_comp (Equiv.addRight (Pi.single i 1)) (fun x => sg (dotProduct x c))).symm
    simp only [key, Finset.sum_neg_distrib] at hS
    linarith

end PEqualNP.Outside.L_lib_421_aux

open PEqualNP.Outside.L_lib_421_aux in
theorem PEqualNP.Outside.L_lib_421 : (∀ m n : ℕ,
  let X := Fin m → ZMod 2
  let Y := Fin n → ZMod 2
  let s := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ (π : Y → X) (g : Y → ZMod 2) (a : X) (b : Y),
    (∑ x : X, ∑ y : Y, s (dotProduct x (π y) + g y + dotProduct a x + dotProduct b y)) =
      (2:ℤ)^m * ∑ y : Y, if π y = a then s (g y + dotProduct b y) else 0) := by
  intro m n X Y s π g a b
  show (∑ x : Fin m → ZMod 2, ∑ y : Fin n → ZMod 2,
      sg (dotProduct x (π y) + g y + dotProduct a x + dotProduct b y)) =
      (2:ℤ)^m * ∑ y : Fin n → ZMod 2, if π y = a then sg (g y + dotProduct b y) else 0
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)

  have hx : ∀ x : Fin m → ZMod 2,
      sg (dotProduct x (π y) + g y + dotProduct a x + dotProduct b y) =
        sg (dotProduct x (π y + a)) * sg (g y + dotProduct b y) := by
    intro x
    rw [← sg_add, dotProduct_add, dotProduct_comm a x]
    ring_nf
  rw [Finset.sum_congr rfl (fun x _ => hx x), ← Finset.sum_mul, sum_char]

  have haa : ∀ v : Fin m → ZMod 2, v + v = 0 := by
    intro v
    funext i
    show v i + v i = 0
    generalize v i = q
    revert q
    decide
  have e : (π y + a = 0) ↔ (π y = a) := by
    constructor
    · intro h3
      calc π y = π y + a + a := by rw [add_assoc, haa, add_zero]
        _ = a := by rw [h3, zero_add]
    · intro h3
      rw [h3, haa]
  by_cases h : π y = a
  · rw [if_pos (e.mpr h), if_pos h]
  · have h2 : ¬ (π y + a = 0) := fun h3 => h (e.mp h3)
    rw [if_neg h2, if_neg h]
    ring
