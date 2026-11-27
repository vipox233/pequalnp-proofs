import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25499

theorem abs_term (u v : Bool) :
    |((if u then (-1 : ℤ) else 1) + (if v then (-1 : ℤ) else 1))| =
      (if u = v then (2 : ℤ) else 0) := by
  cases u <;> cases v <;> norm_num

theorem shift_sum {k b : ℕ} (g : BitVec k → ℤ) (d : BitVec k) (s : BitVec b) :
    (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s ^^^ d.setWidth b)).sum g =
      (Finset.univ.filter (fun key : BitVec k => key.setWidth b = s)).sum
        (fun x => g (x ^^^ d)) := by
  symm
  refine Finset.sum_nbij' (fun x => x ^^^ d) (fun x => x ^^^ d) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [BitVec.setWidth_xor, ha]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [BitVec.setWidth_xor, ha, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro a _
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro a _
    simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · intro a _
    rfl

theorem main_aux : ∀ (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b),
  let slice := fun label : BitVec b =>
    Finset.univ.filter (fun key : BitVec k => key.setWidth b = label)
  let bias := fun t : BitVec b =>
    (slice t).sum (fun word => if f word then (-1 : ℤ) else 1)
  let agreements := (slice s).filter (fun x => f x = f (x ^^^ d))
  (bias s + bias (s ^^^ d.setWidth b)).natAbs ≤ 2 * agreements.card := by
  intro k b f d s slice bias agreements
  have hsh : bias (s ^^^ d.setWidth b) =
      (slice s).sum (fun x => if f (x ^^^ d) then (-1 : ℤ) else 1) :=
    shift_sum (fun word => if f word then (-1 : ℤ) else 1) d s
  have hsum : bias s + bias (s ^^^ d.setWidth b) =
      (slice s).sum (fun x => (if f x then (-1 : ℤ) else 1) +
        (if f (x ^^^ d) then (-1 : ℤ) else 1)) := by
    rw [hsh, Finset.sum_add_distrib]
  have hc : agreements.card = ((slice s).filter (fun x => f x = f (x ^^^ d))).card := rfl
  have hle : |bias s + bias (s ^^^ d.setWidth b)| ≤ ((2 * agreements.card : ℕ) : ℤ) := by
    rw [hsum]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    simp only [abs_term]
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [hc]
    push_cast
    ring
  have h2 : ((bias s + bias (s ^^^ d.setWidth b)).natAbs : ℤ) ≤
      ((2 * agreements.card : ℕ) : ℤ) := by
    rw [Int.natCast_natAbs]
    exact hle
  exact_mod_cast h2

end PEqualNP.Outside.L_meta_25499

theorem PEqualNP.Outside.L_meta_25499 : ∀ (k b : ℕ) (f : BitVec k → Bool) (d : BitVec k) (s : BitVec b),
  let slice := fun label : BitVec b =>
    Finset.univ.filter (fun key : BitVec k => key.setWidth b = label)
  let bias := fun t : BitVec b =>
    (slice t).sum (fun word => if f word then (-1 : ℤ) else 1)
  let agreements := (slice s).filter (fun x => f x = f (x ^^^ d))
  (bias s + bias (s ^^^ d.setWidth b)).natAbs ≤ 2 * agreements.card :=
  PEqualNP.Outside.L_meta_25499.main_aux
