import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_391

def sg (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

lemma sg_add : ∀ x y : ZMod 2, sg (x + y) = sg x * sg y := by decide

lemma abs_sg : ∀ x : ZMod 2, |sg x| = 1 := by decide

lemma ne_zero_one : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

lemma sum_sg {V : Type} [AddCommGroup V] [Fintype V] (f : V →+ ZMod 2) [Decidable (f = 0)] :
    ∑ v, sg (f v) = if f = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with h
  · simp [h, sg]
  · have hw : ∃ w, f w ≠ 0 := by
      by_contra hc
      apply h
      ext v
      by_contra hv
      exact hc ⟨v, by simpa using hv⟩
    obtain ⟨w, hw⟩ := hw
    have e : ∑ v, sg (f (v + w)) = ∑ v, sg (f v) :=
      Equiv.sum_comp (Equiv.addRight w) (fun v => sg (f v))
    simp only [map_add, sg_add, ← Finset.sum_mul, ne_zero_one _ hw] at e
    have m : sg 1 = -1 := by decide
    rw [m] at e
    omega

def dot (n : ℕ) (c : Fin n → ZMod 2) : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  ∑ i, c i • LinearMap.proj i

lemma dot_apply (n : ℕ) (c w : Fin n → ZMod 2) : dot n c w = ∑ i, c i * w i := by
  simp [dot, LinearMap.sum_apply]

lemma dot_single (n : ℕ) (c : Fin n → ZMod 2) (i : Fin n) : dot n c (Pi.single i 1) = c i := by
  rw [dot_apply]
  simp [Pi.single_apply]

lemma dot_single' (n : ℕ) (w : Fin n → ZMod 2) (i : Fin n) : dot n (Pi.single i 1) w = w i := by
  rw [dot_apply]
  simp [Pi.single_apply]

lemma orth (n : ℕ) (w : Fin n → ZMod 2) :
    ∑ c, sg (dot n c w) = if w = 0 then (2 : ℤ) ^ n else 0 := by
  classical
  let f : (Fin n → ZMod 2) →+ ZMod 2 := AddMonoidHom.mk' (fun c => dot n c w)
    (fun x y => by simp [dot_apply, add_mul, Finset.sum_add_distrib])
  have hf : f = 0 ↔ w = 0 := by
    constructor
    · intro h
      funext i
      have : f (Pi.single i 1) = 0 := by rw [h]; rfl
      have e : f (Pi.single i 1) = w i := dot_single' n w i
      rw [e] at this
      simpa using this
    · intro h
      refine AddMonoidHom.ext fun c => ?_
      show dot n c w = 0
      rw [h, map_zero]
  have key : ∑ c, sg (dot n c w) = ∑ c, sg (f c) := rfl
  rw [key, sum_sg f]
  by_cases h : w = 0
  · rw [if_pos h, if_pos (hf.2 h)]; simp
  · rw [if_neg h, if_neg (fun e => h (hf.1 e))]

end PEqualNP.Outside.L_lib_391

open PEqualNP.Outside.L_lib_391 in
theorem PEqualNP.Outside.L_lib_391 : (∀ (d t : ℕ),
  let H := Fin d → ZMod 2
  let T := Fin t → ZMod 2
  ∀ B : H →ₗ[ZMod 2] H →ₗ[ZMod 2] T,
    (∀ chi : T →ₗ[ZMod 2] ZMod 2, chi ≠ 0 →
      ∀ u : H, (∀ v : H, chi (B u v) = 0) → u = 0) →
    ∀ (q : ℕ) (Q : (H × H) →ₗ[ZMod 2] (Fin q → ZMod 2)) (s : Fin q → ZMod 2) (b : T),
      let A := Finset.univ.filter (fun z : H × H => Q z = s)
      let C := A.filter (fun point => B point.1 point.2 = b)
      |(2 : ℤ) ^ t * (C.card : ℤ) - (A.card : ℤ)| ≤ ((2 : ℤ) ^ t - 1) * 2 ^ d) := by
  intro d t H T B hB q Q s b A C
  have step1 : (2 : ℤ) ^ t * (C.card : ℤ) = ∑ c : T, ∑ z ∈ A, sg (dot t c (B z.1 z.2 - b)) := by
    rw [Finset.sum_comm]
    simp only [T, orth, sub_eq_zero]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have zero : ∑ z ∈ A, sg (dot t 0 (B z.1 z.2 - b)) = (A.card : ℤ) := by
    have : dot t 0 = 0 := by simp [dot]
    simp [this, sg]
  have step2 : (2 : ℤ) ^ t * (C.card : ℤ) - (A.card : ℤ)
      = ∑ c ∈ (Finset.univ : Finset T).erase 0, ∑ z ∈ A, sg (dot t c (B z.1 z.2 - b)) := by
    rw [step1, ← Finset.sum_erase_add (Finset.univ : Finset T) _ (Finset.mem_univ 0), zero]
    ring
  have bound : ∀ c : T, c ≠ 0 → |∑ z ∈ A, sg (dot t c (B z.1 z.2 - b))| ≤ (2 : ℤ) ^ d := by
    intro c hc
    set chi := dot t c with hchi
    have chine : chi ≠ 0 := by
      intro h
      apply hc
      funext i
      have e := dot_single t c i
      rw [← hchi, h] at e
      rw [Pi.zero_apply]
      simpa using e.symm
    set W : ℤ := ∑ z ∈ A, sg (chi (B z.1 z.2)) with hW
    have factor : ∑ z ∈ A, sg (chi (B z.1 z.2 - b)) = W * sg (-(chi b)) := by
      rw [hW, Finset.sum_mul]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [map_sub, sub_eq_add_neg, sg_add]
    rw [factor, abs_mul, abs_sg, mul_one]
    let β : H →ₗ[ZMod 2] H →ₗ[ZMod 2] ZMod 2 := B.compr₂ chi
    have inj : Function.Injective β := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      apply hB chi chine u
      intro v
      have := LinearMap.congr_fun hu v
      simpa [β] using this
    have surj : Function.Surjective β :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (Subspace.dual_finrank_eq (K := ZMod 2) (V := H)).symm).1 inj
    have Zb : ∀ a : Fin q → ZMod 2,
        |∑ z : H × H, sg (chi (B z.1 z.2) + dot q a (Q z))| = (2 : ℤ) ^ d := by
      intro a
      let L : (H × H) →ₗ[ZMod 2] ZMod 2 := (dot q a).comp Q
      let L1 : H →ₗ[ZMod 2] ZMod 2 := L.comp (LinearMap.inl (ZMod 2) H H)
      let L2 : H →ₗ[ZMod 2] ZMod 2 := L.comp (LinearMap.inr (ZMod 2) H H)
      obtain ⟨u0, hu0⟩ := surj L2
      have char2 : ∀ g h : H →ₗ[ZMod 2] ZMod 2, g + h = 0 ↔ g = h := by
        intro g h
        have two : ∀ x y : ZMod 2, x + y = 0 ↔ x = y := by decide
        constructor
        · intro e
          refine LinearMap.ext fun v => ?_
          exact (two _ _).1 (by simpa using LinearMap.congr_fun e v)
        · intro e
          refine LinearMap.ext fun v => ?_
          simpa using (two (g v) (h v)).2 (by rw [e])
      have inner : ∀ u : H, ∑ v : H, sg (chi (B u v) + L (u, v))
          = if u = u0 then sg (L1 u) * (2 : ℤ) ^ d else 0 := by
        intro u
        classical
        have split : ∀ v : H, sg (chi (B u v) + L (u, v)) = sg (L1 u) * sg ((β u + L2) v) := by
          intro v
          rw [← sg_add]
          congr 1
          have : L (u, v) = L1 u + L2 v := by
            show L (u, v) = L (u, 0) + L (0, v)
            rw [← map_add]; simp
          rw [this]
          show chi (B u v) + (L1 u + L2 v) = L1 u + (chi (B u v) + L2 v)
          ring
        simp only [split, ← Finset.mul_sum]
        have s2 := sum_sg (β u + L2).toAddMonoidHom
        have s3 : ∑ v : H, sg ((β u + L2) v) = ∑ v : H, sg ((β u + L2).toAddMonoidHom v) := rfl
        rw [s3, s2]
        have iff : (β u + L2).toAddMonoidHom = 0 ↔ u = u0 := by
          constructor
          · intro e
            have e' : β u + L2 = 0 := by
              refine LinearMap.ext fun v => ?_
              exact DFunLike.congr_fun e v
            apply inj
            rw [hu0]
            exact (char2 _ _).1 e'
          · intro e
            have e' : β u + L2 = 0 := (char2 _ _).2 (by rw [e, hu0])
            rw [e']; rfl
        have card : (Fintype.card H : ℤ) = (2 : ℤ) ^ d := by simp [H]
        by_cases h : u = u0
        · rw [if_pos h, if_pos (iff.2 h), card]
        · rw [if_neg h, if_neg (fun e => h (iff.1 e)), mul_zero]
      have total : ∑ z : H × H, sg (chi (B z.1 z.2) + dot q a (Q z)) = sg (L1 u0) * (2 : ℤ) ^ d := by
        rw [Fintype.sum_prod_type]
        have : ∀ u : H, ∑ v : H, sg (chi (B u v) + dot q a (Q (u, v)))
            = if u = u0 then sg (L1 u) * (2 : ℤ) ^ d else 0 := fun u => inner u
        simp only [this]
        rw [Finset.sum_ite_eq' Finset.univ u0 (fun u => sg (L1 u) * (2 : ℤ) ^ d)]
        simp
      rw [total, abs_mul, abs_sg, one_mul, abs_of_nonneg (by positivity)]
    have expand : (2 : ℤ) ^ q * W
        = ∑ a : Fin q → ZMod 2, sg (-(dot q a s)) * ∑ z : H × H, sg (chi (B z.1 z.2) + dot q a (Q z)) := by
      have l : (2 : ℤ) ^ q * W = ∑ z : H × H, sg (chi (B z.1 z.2)) * ∑ a, sg (dot q a (Q z - s)) := by
        simp only [orth, sub_eq_zero, mul_ite, mul_zero]
        rw [← Finset.sum_filter, hW, Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
      rw [l]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun z _ => ?_
      rw [map_sub, sub_eq_add_neg, sg_add, sg_add]
      ring
    have final : (2 : ℤ) ^ q * |W| ≤ (2 : ℤ) ^ q * (2 : ℤ) ^ d := by
      have e : (2 : ℤ) ^ q * |W| = |(2 : ℤ) ^ q * W| := by
        rw [abs_mul, abs_of_nonneg (show (0 : ℤ) ≤ 2 ^ q by positivity)]
      rw [e, expand]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      simp only [abs_mul, abs_sg, one_mul, Zb]
      simp
    exact le_of_mul_le_mul_left final (by positivity)
  rw [step2]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ ((2 : ℤ) ^ d) (fun c hc => bound c (Finset.mem_erase.1 hc).1)).trans ?_
  have card : ((Finset.univ : Finset T).erase 0).card = 2 ^ t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp [T]
  rw [card, nsmul_eq_mul, Nat.cast_sub (Nat.one_le_two_pow)]
  push_cast
  exact le_refl _
