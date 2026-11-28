import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_399_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

structure Trunc2 (D1 D2 : ℕ) (R : Type*) where
  coeff : Fin D1 → Fin D2 → R

namespace Trunc2

variable {D1 D2 : ℕ} {R : Type*}

lemma ext {f g : Trunc2 D1 D2 R} (h : ∀ i j, f.coeff i j = g.coeff i j) : f = g := by
  cases f; cases g; congr; funext i j; exact h i j

section RingInst
variable [CommRing R]

def tZero : Trunc2 D1 D2 R := ⟨fun _ _ => 0⟩
def tOne : Trunc2 D1 D2 R := ⟨fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0⟩
def tAdd (f g : Trunc2 D1 D2 R) : Trunc2 D1 D2 R := ⟨fun i j => f.coeff i j + g.coeff i j⟩
def tNeg (f : Trunc2 D1 D2 R) : Trunc2 D1 D2 R := ⟨fun i j => -f.coeff i j⟩
def tSub (f g : Trunc2 D1 D2 R) : Trunc2 D1 D2 R := ⟨fun i j => f.coeff i j - g.coeff i j⟩
def tMul (f g : Trunc2 D1 D2 R) : Trunc2 D1 D2 R :=
  ⟨fun i j => ∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
    if i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val then f.coeff i1 j1 * g.coeff i2 j2 else 0⟩

lemma tMul_assoc (f g h : Trunc2 D1 D2 R) : tMul (tMul f g) h = tMul f (tMul g h) := by
  apply ext; intro i j
  dsimp only [tMul]
  have hL :
      (∑ i12 : Fin D1, ∑ i3 : Fin D1, ∑ j12 : Fin D2, ∑ j3 : Fin D2,
        if i12.val + i3.val = i.val ∧ j12.val + j3.val = j.val then
          (∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
            if i1.val + i2.val = i12.val ∧ j1.val + j2.val = j12.val then
              f.coeff i1 j1 * g.coeff i2 j2 else 0) * h.coeff i3 j3
        else 0) =
      ∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ i3 : Fin D1,
        ∑ j1 : Fin D2, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
          if i1.val + i2.val + i3.val = i.val ∧ j1.val + j2.val + j3.val = j.val then
            f.coeff i1 j1 * g.coeff i2 j2 * h.coeff i3 j3
          else 0 := by
    have hstep1 : ∀ (i12 i3 : Fin D1) (j12 j3 : Fin D2),
        (if i12.val + i3.val = i.val ∧ j12.val + j3.val = j.val then
          (∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
            if i1.val + i2.val = i12.val ∧ j1.val + j2.val = j12.val then
              f.coeff i1 j1 * g.coeff i2 j2 else 0) * h.coeff i3 j3
        else 0) =
        ∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
          if (i12.val + i3.val = i.val ∧ j12.val + j3.val = j.val) ∧
             (i1.val + i2.val = i12.val ∧ j1.val + j2.val = j12.val) then
            f.coeff i1 j1 * g.coeff i2 j2 * h.coeff i3 j3
          else 0 := by
      intro i12 i3 j12 j3
      by_cases hc : i12.val + i3.val = i.val ∧ j12.val + j3.val = j.val
      · simp only [hc, true_and, ↓reduceIte, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
          Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
        split_ifs <;> ring
      · simp [hc]
    simp_rw [hstep1]
    trans (∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ i3 : Fin D1,
        ∑ j1 : Fin D2, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
          ∑ i12 : Fin D1, ∑ j12 : Fin D2,
            if (i12.val + i3.val = i.val ∧ j12.val + j3.val = j.val) ∧
               (i1.val + i2.val = i12.val ∧ j1.val + j2.val = j12.val) then
              f.coeff i1 j1 * g.coeff i2 j2 * h.coeff i3 j3
            else 0)
    · let e1 : (Fin D1 × Fin D1 × Fin D2 × Fin D2 × Fin D1 × Fin D1 × Fin D2 × Fin D2) ≃
          (Fin D1 × Fin D1 × Fin D1 × Fin D2 × Fin D2 × Fin D2 × Fin D1 × Fin D2) :=
        { toFun := fun ⟨i12, i3, j12, j3, i1, i2, j1, j2⟩ => (i1, i2, i3, j1, j2, j3, i12, j12)
          invFun := fun ⟨i1, i2, i3, j1, j2, j3, i12, j12⟩ => (i12, i3, j12, j3, i1, i2, j1, j2)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have heq := Fintype.sum_equiv e1
        (fun x => if (x.1.val + x.2.1.val = i.val ∧ x.2.2.1.val + x.2.2.2.1.val = j.val) ∧
            (x.2.2.2.2.1.val + x.2.2.2.2.2.1.val = x.1.val ∧ x.2.2.2.2.2.2.1.val + x.2.2.2.2.2.2.2.val = x.2.2.1.val) then
          f.coeff x.2.2.2.2.1 x.2.2.2.2.2.2.1 * g.coeff x.2.2.2.2.2.1 x.2.2.2.2.2.2.2 * h.coeff x.2.1 x.2.2.2.1
        else 0)
        (fun y => if (y.2.2.2.2.2.2.1.val + y.2.2.1.val = i.val ∧ y.2.2.2.2.2.2.2.val + y.2.2.2.2.2.1.val = j.val) ∧
            (y.1.val + y.2.1.val = y.2.2.2.2.2.2.1.val ∧ y.2.2.2.1.val + y.2.2.2.2.1.val = y.2.2.2.2.2.2.2.val) then
          f.coeff y.1 y.2.2.2.1 * g.coeff y.2.1 y.2.2.2.2.1 * h.coeff y.2.2.1 y.2.2.2.2.2.1
        else 0)
        (fun _ => rfl)
      simpa only [Fintype.sum_prod_type] using heq
    · refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
        Finset.sum_congr rfl fun i3 _ => Finset.sum_congr rfl fun j1 _ =>
        Finset.sum_congr rfl fun j2 _ => Finset.sum_congr rfl fun j3 _ => ?_
      by_cases hsum : i1.val + i2.val + i3.val = i.val ∧ j1.val + j2.val + j3.val = j.val
      · have hi12 : i1.val + i2.val < D1 := by have := i.isLt; omega
        have hj12 : j1.val + j2.val < D2 := by have := j.isLt; omega
        rw [Finset.sum_eq_single ⟨i1.val + i2.val, hi12⟩]
        · rw [Finset.sum_eq_single ⟨j1.val + j2.val, hj12⟩]
          · simp [hsum]
          · intro j12 _ hne
            have : j1.val + j2.val ≠ j12.val := fun h => hne (Fin.ext h.symm)
            simp [this]
          · intro h0; exact absurd (Finset.mem_univ _) h0
        · intro i12 _ hne
          refine Finset.sum_eq_zero fun j12 _ => ?_
          have : i1.val + i2.val ≠ i12.val := fun h => hne (Fin.ext h.symm)
          simp [this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · rw [if_neg hsum]
        refine Finset.sum_eq_zero fun i12 _ => Finset.sum_eq_zero fun j12 _ => ?_
        split_ifs with hc
        · exfalso; apply hsum; omega
        · rfl
  have hR :
      (∑ i1 : Fin D1, ∑ i23 : Fin D1, ∑ j1 : Fin D2, ∑ j23 : Fin D2,
        if i1.val + i23.val = i.val ∧ j1.val + j23.val = j.val then
          f.coeff i1 j1 * (∑ i2 : Fin D1, ∑ i3 : Fin D1, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
            if i2.val + i3.val = i23.val ∧ j2.val + j3.val = j23.val then
              g.coeff i2 j2 * h.coeff i3 j3 else 0)
        else 0) =
      ∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ i3 : Fin D1,
        ∑ j1 : Fin D2, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
          if i1.val + i2.val + i3.val = i.val ∧ j1.val + j2.val + j3.val = j.val then
            f.coeff i1 j1 * g.coeff i2 j2 * h.coeff i3 j3
          else 0 := by
    have hstep1 : ∀ (i1 i23 : Fin D1) (j1 j23 : Fin D2),
        (if i1.val + i23.val = i.val ∧ j1.val + j23.val = j.val then
          f.coeff i1 j1 * (∑ i2 : Fin D1, ∑ i3 : Fin D1, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
            if i2.val + i3.val = i23.val ∧ j2.val + j3.val = j23.val then
              g.coeff i2 j2 * h.coeff i3 j3 else 0)
        else 0) =
        ∑ i2 : Fin D1, ∑ i3 : Fin D1, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
          if (i1.val + i23.val = i.val ∧ j1.val + j23.val = j.val) ∧
             (i2.val + i3.val = i23.val ∧ j2.val + j3.val = j23.val) then
            f.coeff i1 j1 * g.coeff i2 j2 * h.coeff i3 j3
          else 0 := by
      intro i1 i23 j1 j23
      by_cases hc : i1.val + i23.val = i.val ∧ j1.val + j23.val = j.val
      · simp only [hc, true_and, ↓reduceIte, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i2 _ => Finset.sum_congr rfl fun i3 _ =>
          Finset.sum_congr rfl fun j2 _ => Finset.sum_congr rfl fun j3 _ => ?_
        split_ifs <;> ring
      · simp [hc]
    simp_rw [hstep1]
    trans (∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ i3 : Fin D1,
        ∑ j1 : Fin D2, ∑ j2 : Fin D2, ∑ j3 : Fin D2,
          ∑ i23 : Fin D1, ∑ j23 : Fin D2,
            if (i1.val + i23.val = i.val ∧ j1.val + j23.val = j.val) ∧
               (i2.val + i3.val = i23.val ∧ j2.val + j3.val = j23.val) then
              f.coeff i1 j1 * g.coeff i2 j2 * h.coeff i3 j3
            else 0)
    · let e2 : (Fin D1 × Fin D1 × Fin D2 × Fin D2 × Fin D1 × Fin D1 × Fin D2 × Fin D2) ≃
          (Fin D1 × Fin D1 × Fin D1 × Fin D2 × Fin D2 × Fin D2 × Fin D1 × Fin D2) :=
        { toFun := fun ⟨i1, i23, j1, j23, i2, i3, j2, j3⟩ => (i1, i2, i3, j1, j2, j3, i23, j23)
          invFun := fun ⟨i1, i2, i3, j1, j2, j3, i23, j23⟩ => (i1, i23, j1, j23, i2, i3, j2, j3)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have heq := Fintype.sum_equiv e2
        (fun x => if (x.1.val + x.2.1.val = i.val ∧ x.2.2.1.val + x.2.2.2.1.val = j.val) ∧
            (x.2.2.2.2.1.val + x.2.2.2.2.2.1.val = x.2.1.val ∧ x.2.2.2.2.2.2.1.val + x.2.2.2.2.2.2.2.val = x.2.2.2.1.val) then
          f.coeff x.1 x.2.2.1 * g.coeff x.2.2.2.2.1 x.2.2.2.2.2.2.1 * h.coeff x.2.2.2.2.2.1 x.2.2.2.2.2.2.2
        else 0)
        (fun y => if (y.1.val + y.2.2.2.2.2.2.1.val = i.val ∧ y.2.2.2.1.val + y.2.2.2.2.2.2.2.val = j.val) ∧
            (y.2.1.val + y.2.2.1.val = y.2.2.2.2.2.2.1.val ∧ y.2.2.2.2.1.val + y.2.2.2.2.2.1.val = y.2.2.2.2.2.2.2.val) then
          f.coeff y.1 y.2.2.2.1 * g.coeff y.2.1 y.2.2.2.2.1 * h.coeff y.2.2.1 y.2.2.2.2.2.1
        else 0)
        (fun _ => rfl)
      simpa only [Fintype.sum_prod_type] using heq
    · refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
        Finset.sum_congr rfl fun i3 _ => Finset.sum_congr rfl fun j1 _ =>
        Finset.sum_congr rfl fun j2 _ => Finset.sum_congr rfl fun j3 _ => ?_
      by_cases hsum : i1.val + i2.val + i3.val = i.val ∧ j1.val + j2.val + j3.val = j.val
      · have hi23 : i2.val + i3.val < D1 := by have := i.isLt; omega
        have hj23 : j2.val + j3.val < D2 := by have := j.isLt; omega
        rw [Finset.sum_eq_single ⟨i2.val + i3.val, hi23⟩]
        · rw [Finset.sum_eq_single ⟨j2.val + j3.val, hj23⟩]
          · simp [hsum, ← Nat.add_assoc]
          · intro j23 _ hne
            have : j2.val + j3.val ≠ j23.val := fun h => hne (Fin.ext h.symm)
            simp [this]
          · intro h0; exact absurd (Finset.mem_univ _) h0
        · intro i23 _ hne
          refine Finset.sum_eq_zero fun j23 _ => ?_
          have : i2.val + i3.val ≠ i23.val := fun h => hne (Fin.ext h.symm)
          simp [this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · rw [if_neg hsum]
        refine Finset.sum_eq_zero fun i23 _ => Finset.sum_eq_zero fun j23 _ => ?_
        split_ifs with hc
        · exfalso; apply hsum; omega
        · rfl
  exact hL.trans hR.symm

lemma tMul_comm (f g : Trunc2 D1 D2 R) : tMul f g = tMul g f := by
  apply ext; intro i j
  dsimp only [tMul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i2 _ => Finset.sum_congr rfl fun i1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j2 _ => Finset.sum_congr rfl fun j1 _ => ?_
  have heq : (i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val) ↔
      (i2.val + i1.val = i.val ∧ j2.val + j1.val = j.val) := by
    rw [Nat.add_comm i1.val, Nat.add_comm j1.val]
  by_cases hc : i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val
  · rw [if_pos hc, if_pos (heq.mp hc), mul_comm]
  · rw [if_neg hc, if_neg (mt heq.mpr hc)]

lemma tOne_mul (f : Trunc2 D1 D2 R) : tMul tOne f = f := by
  apply ext; intro i j
  dsimp only [tMul, tOne]
  have h01 : 0 < D1 := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h02 : 0 < D2 := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  rw [Finset.sum_eq_single ⟨0, h01⟩]
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single ⟨0, h02⟩]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro j2 _ hne
          have : j2.val ≠ j.val := fun h => hne (Fin.ext h)
          simp [this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · intro j1 _ hne
        refine Finset.sum_eq_zero fun j2 _ => ?_
        have : j1.val ≠ 0 := fun h => hne (Fin.ext h)
        simp [this]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · intro i2 _ hne
      refine Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
      have : i2.val ≠ i.val := fun h => hne (Fin.ext h)
      simp [this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · intro i1 _ hne
    refine Finset.sum_eq_zero fun i2 _ => Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
    have : i1.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma tLeft_distrib (f g h : Trunc2 D1 D2 R) : tMul f (tAdd g h) = tAdd (tMul f g) (tMul f h) := by
  apply ext; intro i j
  dsimp only [tMul, tAdd]
  simp_rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
    Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
  split_ifs <;> ring

instance instZero : Zero (Trunc2 D1 D2 R) := ⟨tZero⟩
instance instOne : One (Trunc2 D1 D2 R) := ⟨tOne⟩
instance instAdd : Add (Trunc2 D1 D2 R) := ⟨tAdd⟩
instance instNeg : Neg (Trunc2 D1 D2 R) := ⟨tNeg⟩
instance instSub : Sub (Trunc2 D1 D2 R) := ⟨tSub⟩
instance instMul : Mul (Trunc2 D1 D2 R) := ⟨tMul⟩

instance instCommRing : CommRing (Trunc2 D1 D2 R) :=
  { zero := tZero, one := tOne, add := tAdd, neg := tNeg, sub := tSub, mul := tMul,
    nsmul := fun n f => ⟨fun i j => n • f.coeff i j⟩,
    zsmul := fun z f => ⟨fun i j => z • f.coeff i j⟩,
    nsmul_zero := fun f => ext fun i j => zero_nsmul _,
    nsmul_succ := fun n f => ext fun i j => succ_nsmul _ _,
    zsmul_zero' := fun f => ext fun i j => zero_zsmul _,
    zsmul_succ' := fun n f => ext fun i j => by
      change (Int.ofNat (n + 1)) • f.coeff i j = (Int.ofNat n) • f.coeff i j + f.coeff i j
      rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul],
    zsmul_neg' := fun n f => ext fun i j => by
      change (Int.negSucc n) • f.coeff i j = -((Int.ofNat (n + 1)) • f.coeff i j)
      rw [negSucc_zsmul, Int.ofNat_eq_natCast, natCast_zsmul],
    zero_add := fun f => ext fun i j => zero_add _, add_assoc := fun f g h => ext fun i j => add_assoc _ _ _,
    neg_add_cancel := fun f => ext fun i j => neg_add_cancel _, add_zero := fun f => ext fun i j => add_zero _,
    sub_eq_add_neg := fun f g => ext fun i j => sub_eq_add_neg _ _, add_comm := fun f g => ext fun i j => add_comm _ _,
    mul_assoc := tMul_assoc,
    one_mul := tOne_mul,
    mul_one := fun f => (tMul_comm f tOne).trans (tOne_mul f),
    zero_mul := fun f => ext fun i j => by change (tMul tZero f).coeff i j = 0; simp [tMul, tZero],
    mul_zero := fun f => ext fun i j => by change (tMul f tZero).coeff i j = 0; simp [tMul, tZero],
    left_distrib := tLeft_distrib,
    right_distrib := fun f g h => by
      change tMul (tAdd f g) h = tAdd (tMul f h) (tMul g h)
      rw [tMul_comm, tLeft_distrib, tMul_comm, tMul_comm h],
    mul_comm := tMul_comm }

lemma coeff_zero (i : Fin D1) (j : Fin D2) : (0 : Trunc2 D1 D2 R).coeff i j = 0 := rfl
lemma coeff_one (i : Fin D1) (j : Fin D2) :
    (1 : Trunc2 D1 D2 R).coeff i j = if i.val = 0 ∧ j.val = 0 then 1 else 0 := rfl
lemma coeff_add (f g : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    (f + g).coeff i j = f.coeff i j + g.coeff i j := rfl
lemma coeff_sub (f g : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    (f - g).coeff i j = f.coeff i j - g.coeff i j := rfl
lemma coeff_neg (f : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    (-f).coeff i j = -f.coeff i j := rfl
lemma coeff_mul (f g : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    (f * g).coeff i j =
      ∑ i1 : Fin D1, ∑ i2 : Fin D1, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
        if i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val then f.coeff i1 j1 * g.coeff i2 j2 else 0 := rfl

lemma coeff_sum {ι : Type*} (s : Finset ι) (f : ι → Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    (∑ x ∈ s, f x).coeff i j = ∑ x ∈ s, (f x).coeff i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

def constC (c : R) : Trunc2 D1 D2 R := ⟨fun i j => if i.val = 0 ∧ j.val = 0 then c else 0⟩

lemma constC_mul (c : R) (f : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    (constC c * f).coeff i j = c * f.coeff i j := by
  rw [coeff_mul]
  have h01 : 0 < D1 := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h02 : 0 < D2 := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  rw [Finset.sum_eq_single ⟨0, h01⟩]
  · rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single ⟨0, h02⟩]
      · rw [Finset.sum_eq_single j]
        · simp [constC]
        · intro j2 _ hne
          have : j2.val ≠ j.val := fun h => hne (Fin.ext h)
          simp [this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · intro j1 _ hne
        refine Finset.sum_eq_zero fun j2 _ => ?_
        have : j1.val ≠ 0 := fun h => hne (Fin.ext h)
        simp [constC, this]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · intro i2 _ hne
      refine Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
      have : i2.val ≠ i.val := fun h => hne (Fin.ext h)
      simp [this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · intro i1 _ hne
    refine Finset.sum_eq_zero fun i2 _ => Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
    have : i1.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [constC, this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma coeff_natCast (m : ℕ) (i : Fin D1) (j : Fin D2) :
    (m : Trunc2 D1 D2 R).coeff i j = if i.val = 0 ∧ j.val = 0 then (m : R) else 0 := by
  induction m with
  | zero => simp [coeff_zero]
  | succ m ih =>
    rw [Nat.cast_succ, Nat.cast_succ, coeff_add, ih, coeff_one]
    split_ifs <;> simp

lemma coeff_intCast (m : ℤ) (i : Fin D1) (j : Fin D2) :
    (m : Trunc2 D1 D2 R).coeff i j = if i.val = 0 ∧ j.val = 0 then (m : R) else 0 := by
  cases m with
  | ofNat k => simpa using coeff_natCast (D1 := D1) (D2 := D2) (R := R) k i j
  | negSucc k =>
    simp only [Int.cast_negSucc, coeff_neg, coeff_add, coeff_natCast, coeff_one]
    split_ifs <;> ring

lemma natCast_mul_coeff (m : ℕ) (f : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    ((m : Trunc2 D1 D2 R) * f).coeff i j = (m : R) * f.coeff i j := by
  have h : (m : Trunc2 D1 D2 R) = constC (m : R) := ext fun a b => coeff_natCast m a b
  rw [h, constC_mul]

lemma intCast_mul_coeff (m : ℤ) (f : Trunc2 D1 D2 R) (i : Fin D1) (j : Fin D2) :
    ((m : Trunc2 D1 D2 R) * f).coeff i j = (m : R) * f.coeff i j := by
  have h : (m : Trunc2 D1 D2 R) = constC (m : R) := ext fun a b => coeff_intCast m a b
  rw [h, constC_mul]

def monom (a b : ℕ) : Trunc2 D1 D2 R := ⟨fun i j => if i.val = a ∧ j.val = b then 1 else 0⟩

lemma monom_zero : (monom 0 0 : Trunc2 D1 D2 R) = 1 := rfl

lemma monom_eq_zero_of_ge (a b : ℕ) (h : D1 ≤ a ∨ D2 ≤ b) : (monom a b : Trunc2 D1 D2 R) = 0 := by
  apply ext; intro i j
  simp only [monom, coeff_zero]
  split_ifs with hc
  · exfalso; rcases h with h1 | h2 <;> [exact absurd i.isLt (by omega); exact absurd j.isLt (by omega)]
  · rfl

lemma monom_mul (a1 b1 a2 b2 : ℕ) :
    (monom a1 b1 : Trunc2 D1 D2 R) * monom a2 b2 = monom (a1 + a2) (b1 + b2) := by
  apply ext; intro i j
  rw [coeff_mul]
  dsimp only [monom]
  by_cases hc : i.val = a1 + a2 ∧ j.val = b1 + b2
  · rw [if_pos hc]
    have ha1 : a1 < D1 := by have := i.isLt; omega
    have ha2 : a2 < D1 := by have := i.isLt; omega
    have hb1 : b1 < D2 := by have := j.isLt; omega
    have hb2 : b2 < D2 := by have := j.isLt; omega
    rw [Finset.sum_eq_single ⟨a1, ha1⟩]
    · rw [Finset.sum_eq_single ⟨a2, ha2⟩]
      · rw [Finset.sum_eq_single ⟨b1, hb1⟩]
        · rw [Finset.sum_eq_single ⟨b2, hb2⟩]
          · simp [hc]
          · intro j2 _ hne
            have : j2.val ≠ b2 := fun h => hne (Fin.ext h)
            simp [this]
          · intro h0; exact absurd (Finset.mem_univ _) h0
        · intro j1 _ hne
          refine Finset.sum_eq_zero fun j2 _ => ?_
          have : j1.val ≠ b1 := fun h => hne (Fin.ext h)
          simp [this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · intro i2 _ hne
        refine Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
        have : i2.val ≠ a2 := fun h => hne (Fin.ext h)
        simp [this]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · intro i1 _ hne
      refine Finset.sum_eq_zero fun i2 _ => Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
      have : i1.val ≠ a1 := fun h => hne (Fin.ext h)
      simp [this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ =>
      Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
    split_ifs with h1 h2 h3
    · exfalso; apply hc; omega
    · simp
    · simp
    · simp
    · rfl

lemma monom_pow (a b k : ℕ) : (monom a b : Trunc2 D1 D2 R) ^ k = monom (k * a) (k * b) := by
  induction k with
  | zero => simp [monom_zero]
  | succ k ih =>
    rw [pow_succ, ih, monom_mul]
    congr 1 <;> ring

def X1 : Trunc2 D1 D2 R := monom 1 0
def X2 : Trunc2 D1 D2 R := monom 0 1

lemma X1_pow_mul_X2_pow (a b : ℕ) :
    (X1 : Trunc2 D1 D2 R) ^ a * X2 ^ b = monom a b := by
  simp [X1, X2, monom_pow, monom_mul]

def mapHom {S : Type*} [CommRing S] (φ : R →+* S) : Trunc2 D1 D2 R →+* Trunc2 D1 D2 S where
  toFun f := ⟨fun i j => φ (f.coeff i j)⟩
  map_one' := ext fun i j => by simp only [coeff_one]; split_ifs <;> simp
  map_mul' f g := ext fun i j => by
    simp only [coeff_mul, map_sum]
    refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
      Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
    split_ifs <;> simp
  map_zero' := ext fun i j => by simp [coeff_zero]
  map_add' f g := ext fun i j => by simp [coeff_add]

lemma mapHom_monom {S : Type*} [CommRing S] (φ : R →+* S) (a b : ℕ) :
    mapHom (D1 := D1) (D2 := D2) φ (monom a b) = monom a b := by
  apply ext; intro i j
  simp only [mapHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, monom]
  split_ifs <;> simp

lemma pow_coeff_eq_zero_of_lt (f : Trunc2 D1 D2 R)
    (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0) :
    ∀ k (i : Fin D1) (j : Fin D2), i.val + j.val < k → (f ^ k).coeff i j = 0 := by
  intro k
  induction k with
  | zero => intro i j h; omega
  | succ k ih =>
    intro i j hij
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ =>
      Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
    split_ifs with h
    · by_cases h0 : i2.val + j2.val = 0
      · rw [hf i2 j2 h0, mul_zero]
      · rw [ih i1 j1 (by omega), zero_mul]
    · rfl

lemma pow_eq_zero_of_zero_const (f : Trunc2 D1 D2 R)
    (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0) :
    f ^ (D1 + D2) = 0 := by
  apply ext; intro i j
  exact pow_coeff_eq_zero_of_lt f hf (D1 + D2) i j (by have := i.isLt; have := j.isLt; omega)

def invOneSub (f : Trunc2 D1 D2 R) : Trunc2 D1 D2 R :=
  ∑ k ∈ Finset.range (D1 + D2), f ^ k

def invOneAdd (f : Trunc2 D1 D2 R) : Trunc2 D1 D2 R :=
  ∑ k ∈ Finset.range (D1 + D2), (-f) ^ k

lemma one_sub_mul_invOneSub (f : Trunc2 D1 D2 R)
    (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0) :
    (1 - f) * invOneSub f = 1 := by
  unfold invOneSub
  have h := geom_sum_mul_neg f (D1 + D2)
  rw [mul_comm, h, pow_eq_zero_of_zero_const f hf, sub_zero]

lemma one_add_mul_invOneAdd (f : Trunc2 D1 D2 R)
    (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0) :
    (1 + f) * invOneAdd f = 1 := by
  have hneg : ∀ i j, i.val + j.val = 0 → (-f).coeff i j = 0 := fun i j h => by
    rw [coeff_neg, hf i j h, neg_zero]
  have h := one_sub_mul_invOneSub (-f) hneg
  simpa [sub_neg_eq_add, invOneAdd, invOneSub] using h

def zpowOneSub (f : Trunc2 D1 D2 R) (c : ℤ) : Trunc2 D1 D2 R :=
  if 0 ≤ c then (1 - f) ^ c.toNat else (invOneSub f) ^ (-c).toNat

lemma zpowOneSub_zero (f : Trunc2 D1 D2 R) : zpowOneSub f 0 = 1 := by
  simp [zpowOneSub]

lemma zpowOneSub_one (f : Trunc2 D1 D2 R) : zpowOneSub f 1 = 1 - f := by
  simp [zpowOneSub]

lemma zpowOneSub_neg_one (f : Trunc2 D1 D2 R) : zpowOneSub f (-1) = invOneSub f := by
  simp [zpowOneSub]

lemma zpowOneSub_neg (f : Trunc2 D1 D2 R) (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0) (c : ℤ) :
    zpowOneSub f c * zpowOneSub f (-c) = 1 := by
  have hinv := one_sub_mul_invOneSub f hf
  by_cases h0 : c = 0
  · subst h0; simp [zpowOneSub]
  · by_cases hpos : 0 ≤ c
    · have hneg : ¬ (0 ≤ -c) := by omega
      simp only [zpowOneSub, hpos, ↓reduceIte, hneg, neg_neg]
      rw [← mul_pow, hinv, one_pow]
    · have hneg : 0 ≤ -c := by omega
      simp only [zpowOneSub, hpos, ↓reduceIte, hneg]
      rw [mul_comm, ← mul_pow, hinv, one_pow]

lemma zpowOneSub_add (f : Trunc2 D1 D2 R) (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0)
    (a b : ℤ) :
    zpowOneSub f (a + b) = zpowOneSub f a * zpowOneSub f b := by
  have hinv := one_sub_mul_invOneSub f hf
  have hcancel : ∀ m k : ℕ, (1 - f) ^ m * (invOneSub f) ^ k =
      if k ≤ m then (1 - f) ^ (m - k) else (invOneSub f) ^ (k - m) := by
    intro m k
    by_cases hkm : k ≤ m
    · rw [if_pos hkm]
      have hm : m = (m - k) + k := by omega
      conv_lhs => rw [hm, pow_add, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
    · rw [if_neg hkm]
      have hk : k = m + (k - m) := by omega
      conv_lhs => rw [hk, pow_add, ← mul_assoc, ← mul_pow, hinv, one_pow, one_mul]
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · have hab : 0 ≤ a + b := by omega
    simp only [zpowOneSub, ha, hb, hab, ↓reduceIte]
    rw [← pow_add]; congr 1; omega
  · simp only [zpowOneSub, ha, hb, ↓reduceIte, hcancel]
    by_cases hab : 0 ≤ a + b
    · have hle : (-b).toNat ≤ a.toNat := by omega
      simp only [hab, hle, ↓reduceIte]; congr 1; omega
    · have hlt : ¬ ((-b).toNat ≤ a.toNat) := by omega
      simp only [hab, hlt, ↓reduceIte]; congr 1; omega
  · simp only [zpowOneSub, ha, hb, ↓reduceIte]
    rw [mul_comm, hcancel]
    by_cases hab : 0 ≤ a + b
    · have hle : (-a).toNat ≤ b.toNat := by omega
      simp only [hab, hle, ↓reduceIte]; congr 1; omega
    · have hlt : ¬ ((-a).toNat ≤ b.toNat) := by omega
      simp only [hab, hlt, ↓reduceIte]; congr 1; omega
  · have hab : ¬ (0 ≤ a + b) := by omega
    simp only [zpowOneSub, ha, hb, hab, ↓reduceIte]
    rw [← pow_add]; congr 1; omega

lemma one_add_eq_zpowOneSub (f : Trunc2 D1 D2 R)
    (hf : ∀ i j, i.val + j.val = 0 → f.coeff i j = 0) :
    1 + f = zpowOneSub f (-1) * zpowOneSub (f ^ 2) 1 := by
  rw [zpowOneSub_neg_one, zpowOneSub_one]
  have h1 : (1 - f) * (1 + f) = 1 - f ^ 2 := by ring
  calc 1 + f = 1 * (1 + f) := (one_mul _).symm
    _ = (invOneSub f * (1 - f)) * (1 + f) := by rw [mul_comm (invOneSub f), one_sub_mul_invOneSub f hf]
    _ = invOneSub f * ((1 - f) * (1 + f)) := by rw [mul_assoc]
    _ = invOneSub f * (1 - f ^ 2) := by rw [h1]

lemma zpowOneSub_mapHom {S : Type*} [CommRing S] (φ : R →+* S) (f : Trunc2 D1 D2 R) (c : ℤ) :
    mapHom φ (zpowOneSub f c) = zpowOneSub (mapHom φ f) c := by
  unfold zpowOneSub invOneSub
  split_ifs <;> simp [map_pow, map_sub, map_sum]

end RingInst

end Trunc2

def hist {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r b : Fin (n + 1)) : ℕ :=
  ((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
    (∀ v, p v = none ∨ p v = some (x v)) ∧
    (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
    (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card

def profile {n : ℕ} (H : Fin (n + 1) → Fin (n + 1) → ℕ) (h : ℕ) (s : Fin (2 * n + 1)) : ℕ :=
  ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), if r.val + b.val = s.val then Nat.choose r.val h * H r b else 0

def freeCount {n : ℕ} (p : Bool × Fin n → Option Bool) : ℕ :=
  (Finset.univ.filter (fun v : Bool × Fin n => p v = none)).card

section ArcFactor

def sgnR {R : Type*} [CommRing R] (b : Bool) : R := if b then -1 else 1

lemma sgnR_mul_self {R : Type*} [CommRing R] (b : Bool) : sgnR (R := R) b * sgnR b = 1 := by
  cases b <;> simp [sgnR]

lemma one_add_sgnR_mul {R : Type*} [CommRing R] (a b : Bool) (u : R) :
    1 + u * sgnR a * sgnR b = if a ≠ b then 1 - u else 1 + u := by
  cases a <;> cases b <;> simp [sgnR] <;> ring

def nextE {n : ℕ} (σ : Equiv.Perm (Fin n)) : Bool × Fin n ≃ Bool × Fin n where
  toFun e := match e.1 with
    | false => (true, e.2)
    | true => (false, σ e.2)
  invFun e := match e.1 with
    | true => (false, e.2)
    | false => (true, σ.symm e.2)
  left_inv e := by rcases e with ⟨b, i⟩; cases b <;> simp
  right_inv e := by rcases e with ⟨b, i⟩; cases b <;> simp

def headV {n : ℕ} (σ : Equiv.Perm (Fin n)) : Bool × Fin n ≃ Bool × Fin n where
  toFun e := match e.1 with
    | false => (false, e.2)
    | true => (true, σ e.2)
  invFun v := match v.1 with
    | false => (false, v.2)
    | true => (true, σ.symm v.2)
  left_inv e := by rcases e with ⟨b, i⟩; cases b <;> simp
  right_inv v := by rcases v with ⟨b, i⟩; cases b <;> simp

def epsVR {R : Type*} [CommRing R] {n : ℕ} (p : Bool × Fin n → Option Bool) (v : Bool × Fin n) : R :=
  match p v with
  | none => 1
  | some b => sgnR b

lemma epsVR_sq {R : Type*} [CommRing R] {n : ℕ} (p : Bool × Fin n → Option Bool) (v : Bool × Fin n) :
    epsVR (R := R) p v = 1 ∨ epsVR (R := R) p v = -1 := by
  unfold epsVR
  cases p v with
  | none => left; rfl
  | some b => cases b <;> simp [sgnR]

def qE {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e : Bool × Fin n) : Option Bool :=
  p (headV σ e)

def epsER {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (e : Bool × Fin n) : R :=
  epsVR p (headV σ e)

def edgeWR {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (u v : R) (e : Bool × Fin n) : R :=
  (if e.1 then v else u) * epsER σ p e * epsER σ p ((nextE σ).symm e)

def rawPoly {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (u v : R) : R :=
  ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), (hist σ p r b : R) *
    (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
    (1 - v) ^ b.val * (1 + v) ^ (n - b.val)

lemma prod_bool_iteR {R : Type*} [CommRing R] (u : R) {n : ℕ} (P : Fin n → Prop) [DecidablePred P] :
    (∏ i : Fin n, if P i then 1 - u else 1 + u) =
      (1 - u) ^ (Finset.univ.filter P).card *
      (1 + u) ^ (n - (Finset.univ.filter P).card) := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  congr 2
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) P
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

lemma term_eq_prod_edgesR {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : Bool × Fin n → Bool) (u v : R) :
    (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
    (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
    ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
    (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card)) =
    ∏ e : Bool × Fin n,
      (1 + (if e.1 then v else u) * sgnR (x (headV σ e)) * sgnR (x (headV σ ((nextE σ).symm e)))) := by
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  have hfalse :
      ∏ i : Fin n, (1 + (if false then v else u) *
        sgnR (x (headV σ (false, i))) * sgnR (x (headV σ ((nextE σ).symm (false, i))))) =
      (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
      (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) := by
    rw [← prod_bool_iteR]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Bool.false_eq_true, ↓reduceIte, headV, nextE, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      Equiv.apply_symm_apply]
    exact one_add_sgnR_mul (x (false, i)) (x (true, i)) u
  have htrue :
      ∏ i : Fin n, (1 + (if true then v else u) *
        sgnR (x (headV σ (true, i))) * sgnR (x (headV σ ((nextE σ).symm (true, i))))) =
      (1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
      (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card) := by
    rw [← prod_bool_iteR]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [↓reduceIte, headV, nextE, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [one_add_sgnR_mul (x (true, σ i)) (x (false, i)) v]
    have hne : (x (true, σ i) ≠ x (false, i)) ↔ (x (false, i) ≠ x (true, σ i)) := ne_comm
    simp only [hne]
  rw [htrue, hfalse, mul_comm]

lemma rawPoly_eq_sum_compat {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (u v : R) :
    rawPoly σ p u v =
      ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
        (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
        ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
        (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card)) := by
  unfold rawPoly hist
  have hstep : ∀ r b : Fin (n + 1),
      (((Finset.univ : Finset (Bool × Fin n → Bool)).filter (fun x =>
        (∀ w, p w = none ∨ p w = some (x w)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)).card : R) *
      (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
      (1 - v) ^ b.val * (1 + v) ^ (n - b.val) =
      ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        if (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
           (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val then
          (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
          (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
          ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
          (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card))
        else 0 := by
    intro r b
    rw [← Finset.sum_filter, Finset.filter_filter]
    have hconst : ∀ x ∈ (Finset.univ.filter (fun x : Bool × Fin n → Bool =>
        (∀ w, p w = none ∨ p w = some (x w)) ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
        (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val)),
        (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
        (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
        ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
        (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card)) =
        (1 - u) ^ r.val * (1 + u) ^ (n - r.val) *
        ((1 - v) ^ b.val * (1 + v) ^ (n - b.val)) := by
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      rw [hx'.2.1, hx'.2.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    ring
  simp_rw [hstep]
  rw [Finset.sum_comm]
  have hswap2 : ∀ r : Fin (n + 1),
      (∑ b : Fin (n + 1), ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        if (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
           (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val then
          (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
          (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
          ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
          (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card))
        else 0) =
      ∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        ∑ b : Fin (n + 1),
          if (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card = r.val ∧
             (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card = b.val then
            (1 - u) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card *
            (1 + u) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card) *
            ((1 - v) ^ (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card *
            (1 + v) ^ (n - (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card))
          else 0 := fun _ => Finset.sum_comm
  rw [Finset.sum_comm]
  simp_rw [hswap2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  set rx := (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, i))).card
  set bx := (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, σ i))).card
  have hrx : rx < n + 1 := Nat.lt_succ_of_le (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _)
  have hbx : bx < n + 1 := Nat.lt_succ_of_le (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _)
  rw [Finset.sum_eq_single ⟨rx, hrx⟩]
  · rw [Finset.sum_eq_single ⟨bx, hbx⟩]
    · simp
    · intro b _ hne
      have : bx ≠ b.val := fun h => hne (Fin.ext h.symm)
      simp [this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · intro r _ hne
    refine Finset.sum_eq_zero fun b _ => ?_
    have : rx ≠ r.val := fun h => hne (Fin.ext h.symm)
    simp [this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma prod_one_add_eq_sum_boolR {α : Type*} [Fintype α] [DecidableEq α]
    {R : Type*} [CommRing R] (f : α → R) :
    (∏ a : α, (1 + f a)) = ∑ S : α → Bool, ∏ a : α, if S a then f a else 1 := by
  have h : (∏ a : α, (1 + f a)) = ∏ a : α, ∑ b : Bool, if b then f a else 1 := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fintype.sum_bool]
    simp [add_comm]
  rw [h, Fintype.prod_sum]

lemma prod_ite_sgnR_mul {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S x : Bool × Fin n → Bool) :
    (∏ e : Bool × Fin n, if S e then sgnR (R := R) (x (headV σ e)) *
      sgnR (x (headV σ ((nextE σ).symm e))) else 1) =
    ∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgnR (R := R) (x (headV σ e)) else 1 := by
  have h1 :
      (∏ e : Bool × Fin n, if S e then sgnR (R := R) (x (headV σ e)) *
        sgnR (x (headV σ ((nextE σ).symm e))) else 1) =
      (∏ e : Bool × Fin n, if S e then sgnR (R := R) (x (headV σ e)) else 1) *
      (∏ e : Bool × Fin n, if S e then sgnR (R := R) (x (headV σ ((nextE σ).symm e))) else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    cases S e <;> simp
  have h2 :
      (∏ e : Bool × Fin n, if S e then sgnR (R := R) (x (headV σ ((nextE σ).symm e))) else 1) =
      ∏ e : Bool × Fin n, if S (nextE σ e) then sgnR (R := R) (x (headV σ e)) else 1 :=
    Fintype.prod_equiv (nextE σ).symm _ _ fun e => by simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  cases S e <;> cases S (nextE σ e) <;> simp [sgnR_mul_self]

lemma prod_ite_epsR_mul {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (S : Bool × Fin n → Bool) :
    (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsER (R := R) σ p e else 1) =
    ∏ e : Bool × Fin n, if S e then epsER (R := R) σ p e * epsER σ p ((nextE σ).symm e) else 1 := by
  have h1 :
      (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsER (R := R) σ p e else 1) =
      (∏ e : Bool × Fin n, if S e then epsER (R := R) σ p e else 1) *
      (∏ e : Bool × Fin n, if S (nextE σ e) then epsER (R := R) σ p e else 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    have hsq : epsER (R := R) σ p e * epsER σ p e = 1 := by
      rcases epsVR_sq (R := R) p (headV σ e) with h | h <;> simp [epsER, h]
    cases S e <;> cases S (nextE σ e) <;> simp [hsq]
  have h2 :
      (∏ e : Bool × Fin n, if S (nextE σ e) then epsER (R := R) σ p e else 1) =
      ∏ e : Bool × Fin n, if S e then epsER (R := R) σ p ((nextE σ).symm e) else 1 :=
    Fintype.prod_equiv (nextE σ) _ _ fun e => by simp
  rw [h1, h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e _ => ?_
  cases S e <;> simp

lemma compat_filter_eq_piFinset {n : ℕ} (p : Bool × Fin n → Option Bool) :
    Finset.univ.filter (fun x : Bool × Fin n → Bool => ∀ w, p w = none ∨ p w = some (x w)) =
    Fintype.piFinset (fun w : Bool × Fin n => match p w with | none => Finset.univ | some b => {b}) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · intro hx w
    cases hw : p w with
    | none => exact Finset.mem_univ _
    | some b =>
      rcases hx w with h | h
      · rw [hw] at h; cases h
      · rw [hw] at h
        have hbx : b = x w := Option.some.inj h
        simp [hbx]
  · intro hx w
    have hw := hx w
    cases hp : p w with
    | none => left; rfl
    | some b =>
      rw [hp] at hw
      right
      simp only [Finset.mem_singleton] at hw
      rw [hw]

lemma sum_compat_prod_sgnR {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (S : Bool × Fin n → Bool) :
    (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
        ∀ w, p w = none ∨ p w = some (x w)),
      ∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgnR (R := R) (x (headV σ e)) else 1) =
    if ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e then
      (2 : R) ^ freeCount p *
      (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then epsER (R := R) σ p e else 1)
    else 0 := by
  rw [compat_filter_eq_piFinset]
  have hreidx : ∀ x : Bool × Fin n → Bool,
      (∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgnR (R := R) (x (headV σ e)) else 1) =
      ∏ w : Bool × Fin n,
        if S ((headV σ).symm w) ≠ S (nextE σ ((headV σ).symm w)) then sgnR (x w) else 1 :=
    fun x => Fintype.prod_equiv (headV σ) _ _ fun e => by simp
  simp_rw [hreidx]
  rw [(Finset.prod_univ_sum
    (fun w : Bool × Fin n => match p w with | none => Finset.univ | some b => {b})
    (fun w b => if S ((headV σ).symm w) ≠ S (nextE σ ((headV σ).symm w)) then sgnR (R := R) b else 1)).symm]
  have hback :
      (∏ w : Bool × Fin n, ∑ b ∈ (match p w with | none => Finset.univ | some c => {c}),
        if S ((headV σ).symm w) ≠ S (nextE σ ((headV σ).symm w)) then sgnR (R := R) b else 1) =
      ∏ e : Bool × Fin n, ∑ b ∈ (match qE σ p e with | none => Finset.univ | some c => {c}),
        if S e ≠ S (nextE σ e) then sgnR (R := R) b else 1 :=
    Fintype.prod_equiv (headV σ).symm _ _ fun w => by simp [qE]
  rw [hback]
  by_cases hval : ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e
  · rw [if_pos hval]
    have hfactor : ∀ e : Bool × Fin n,
        (∑ b ∈ (match qE σ p e with | none => Finset.univ | some c => {c}),
          if S e ≠ S (nextE σ e) then sgnR (R := R) b else 1) =
        (if qE σ p e = none then (2 : R) else 1) *
        (if S e ≠ S (nextE σ e) then epsER (R := R) σ p e else 1) := by
      intro e
      cases hq : qE σ p e with
      | none =>
        have heq : S (nextE σ e) = S e := hval e hq
        have hne : ¬ (S e ≠ S (nextE σ e)) := by simp [heq]
        simp only [hne, ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
          nsmul_eq_mul, mul_one, Nat.cast_ofNat]
      | some c =>
        simp only [Finset.sum_singleton, reduceCtorEq, ↓reduceIte, one_mul, epsER, epsVR]
        change (if S e ≠ S (nextE σ e) then sgnR (R := R) c else 1) =
          if S e ≠ S (nextE σ e) then (match qE σ p e with | none => 1 | some b => sgnR (R := R) b) else 1
        rw [hq]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    congr 1
    unfold freeCount
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_of_bijective (f := fun x : {e : Bool × Fin n // qE σ p e = none} =>
        (⟨headV σ x.1, x.2⟩ : {w : Bool × Fin n // p w = none}))
      ⟨fun a b hab => Subtype.ext ((headV σ).injective (congrArg Subtype.val hab)),
       fun y => ⟨⟨(headV σ).symm y.1, by simp [qE, y.2]⟩, Subtype.ext (by simp)⟩⟩
  · rw [if_neg hval]
    have hex : ∃ e0 : Bool × Fin n, qE σ p e0 = none ∧ S (nextE σ e0) ≠ S e0 := by
      by_contra hall
      apply hval
      intro e hq
      by_contra hne
      exact hall ⟨e, hq, hne⟩
    obtain ⟨e0, hq0, hne0⟩ := hex
    refine Finset.prod_eq_zero (Finset.mem_univ e0) ?_
    rw [hq0]
    have hne' : S e0 ≠ S (nextE σ e0) := Ne.symm hne0
    rw [Fintype.sum_bool, if_pos hne', if_pos hne']
    simp [sgnR]

lemma rawPoly_eq_edgeSumR {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (u v : R) :
    rawPoly σ p u v =
      (2 : R) ^ freeCount p *
      ∑ S ∈ Finset.univ.filter (fun S : Bool × Fin n → Bool =>
        ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e),
        ∏ e : Bool × Fin n, if S e then edgeWR σ p u v e else 1 := by
  rw [rawPoly_eq_sum_compat]
  simp_rw [term_eq_prod_edgesR, prod_one_add_eq_sum_boolR]
  rw [Finset.sum_comm]
  have hpull : ∀ S : Bool × Fin n → Bool,
      (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        ∏ e : Bool × Fin n,
          if S e then (if e.1 then v else u) * sgnR (R := R) (x (headV σ e)) *
            sgnR (x (headV σ ((nextE σ).symm e)))
          else 1) =
      (∏ e : Bool × Fin n, if S e then (if e.1 then v else u) else 1) *
      (∑ x ∈ Finset.univ.filter (fun x : Bool × Fin n → Bool =>
          ∀ w, p w = none ∨ p w = some (x w)),
        ∏ e : Bool × Fin n, if S e ≠ S (nextE σ e) then sgnR (R := R) (x (headV σ e)) else 1) := by
    intro S
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← prod_ite_sgnR_mul, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    cases S e <;> simp [mul_assoc]
  simp_rw [hpull, sum_compat_prod_sgnR]
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases hval : ∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e
  · rw [if_pos hval, if_pos hval]
    rw [prod_ite_epsR_mul, ← mul_assoc, mul_comm _ ((2 : R) ^ freeCount p), mul_assoc]
    congr 1
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    cases S e <;> simp [edgeWR, mul_assoc]
  · rw [if_neg hval, if_neg hval, mul_zero]

lemma sum_valid_eq_prodR {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {R : Type*} [CommRing R]
    (cls : α → β) (hsurj : Function.Surjective cls) (W : α → R)
    (P : (α → Bool) → Prop) [DecidablePred P]
    (hP : ∀ S : α → Bool, P S ↔ ∀ x y, cls x = cls y → S x = S y) :
    (∑ S ∈ Finset.univ.filter P, ∏ x : α, if S x then W x else 1) =
    ∏ b : β, (1 + ∏ x ∈ Finset.univ.filter (fun x => cls x = b), W x) := by
  rw [prod_one_add_eq_sum_boolR]
  symm
  refine Finset.sum_bij (fun T _ => fun x => T (cls x)) ?_ ?_ ?_ ?_
  · intro T _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP]
    intro x y hxy; rw [hxy]
  · intro T1 _ T2 _ h
    funext b
    obtain ⟨x, rfl⟩ := hsurj b
    exact congrFun h x
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hP] at hS
    refine ⟨fun b => S (hsurj b).choose, Finset.mem_univ _, ?_⟩
    funext x
    exact hS _ _ (hsurj (cls x)).choose_spec
  · intro T _
    have hfib : (∏ x : α, if T (cls x) then W x else 1) =
        ∏ b : β, ∏ x ∈ Finset.univ.filter (fun x : α => cls x = b),
          if T (cls x) then W x else 1 :=
      (Finset.prod_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    rw [hfib]
    refine Finset.prod_congr rfl fun b _ => ?_
    cases hTb : T b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine (Finset.prod_eq_one fun x hx => ?_).symm
      rw [Finset.mem_filter] at hx
      simp [hx.2, hTb]
    · simp only [↓reduceIte]
      refine (Finset.prod_congr rfl fun x hx => ?_).symm
      rw [Finset.mem_filter] at hx
      simp [hx.2, hTb]

def ArcStep {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e1 e2 : Bool × Fin n) : Prop :=
  qE σ p e1 = none ∧ e2 = nextE σ e1

lemma arcStep_right_unique {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x y1 y2 : Bool × Fin n} (h1 : ArcStep σ p x y1) (h2 : ArcStep σ p x y2) : y1 = y2 :=
  h1.2.trans h2.2.symm

lemma arcStep_left_unique {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x1 x2 y : Bool × Fin n} (h1 : ArcStep σ p x1 y) (h2 : ArcStep σ p x2 y) : x1 = x2 :=
  (nextE σ).injective (h1.2.symm.trans h2.2)

lemma reach_linear_out {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {a x y : Bool × Fin n}
    (hx : Relation.ReflTransGen (ArcStep σ p) a x)
    (hy : Relation.ReflTransGen (ArcStep σ p) a y) :
    Relation.ReflTransGen (ArcStep σ p) x y ∨ Relation.ReflTransGen (ArcStep σ p) y x := by
  induction hx using Relation.ReflTransGen.head_induction_on generalizing y with
  | refl => left; exact hy
  | @head a' b hab hbx ih =>
    rcases Relation.ReflTransGen.cases_head hy with rfl | ⟨c, hac, hcy⟩
    · right; exact Relation.ReflTransGen.head hab hbx
    · have hbc : b = c := arcStep_right_unique hab hac
      subst hbc
      exact ih hcy

lemma reach_linear_in {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {a x y : Bool × Fin n}
    (hx : Relation.ReflTransGen (ArcStep σ p) x a)
    (hy : Relation.ReflTransGen (ArcStep σ p) y a) :
    Relation.ReflTransGen (ArcStep σ p) x y ∨ Relation.ReflTransGen (ArcStep σ p) y x := by
  induction hx generalizing y with
  | refl => right; exact hy
  | @tail b a' hxb hba ih =>
    rcases Relation.ReflTransGen.cases_tail hy with rfl | ⟨c, hyc, hca⟩
    · left; exact Relation.ReflTransGen.tail hxb hba
    · have hbc : b = c := arcStep_left_unique hba hca
      subst hbc
      exact ih hyc

lemma eqv_imp_reach_or {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x y : Bool × Fin n} (h : Relation.EqvGen (ArcStep σ p) x y) :
    Relation.ReflTransGen (ArcStep σ p) x y ∨ Relation.ReflTransGen (ArcStep σ p) y x := by
  induction h with
  | rel a b hab => left; exact Relation.ReflTransGen.single hab
  | refl a => left; exact Relation.ReflTransGen.refl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 =>
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · left; exact h1.trans h2
    · exact reach_linear_in h1 h2
    · exact reach_linear_out h1 h2
    · right; exact h2.trans h1

lemma stop_unique {n : ℕ} {σ : Equiv.Perm (Fin n)} {p : Bool × Fin n → Option Bool}
    {x y : Bool × Fin n} (heqv : Relation.EqvGen (ArcStep σ p) x y)
    (hx : qE σ p x ≠ none) (hy : qE σ p y ≠ none) : x = y := by
  rcases eqv_imp_reach_or heqv with h | h
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hxb, _⟩
    · rfl
    · exact absurd hxb.1 hx
  · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hyb, _⟩
    · rfl
    · exact absurd hyb.1 hy

lemma valid_iff_eqv_const {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (S : Bool × Fin n → Bool) :
    (∀ e : Bool × Fin n, qE σ p e = none → S (nextE σ e) = S e) ↔
    (∀ x y : Bool × Fin n, Relation.EqvGen (ArcStep σ p) x y → S x = S y) := by
  constructor
  · intro h x y hxy
    induction hxy with
    | rel a b hab => rw [hab.2]; exact (h a hab.1).symm
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h e hq
    exact (h e (nextE σ e) (Relation.EqvGen.rel e (nextE σ e) ⟨hq, rfl⟩)).symm

noncomputable def arcClass {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e : Bool × Fin n) : Finset (Bool × Fin n) :=
  @Finset.filter _ (fun e' => Relation.EqvGen (ArcStep σ p) e e') (Classical.decPred _) Finset.univ

noncomputable def arcClasses {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    Finset (Finset (Bool × Fin n)) :=
  Finset.univ.image (arcClass σ p)

def arcRed {n : ℕ} (c : Finset (Bool × Fin n)) : ℕ :=
  (c.filter (fun e => e.1 = false)).card

def arcBlue {n : ℕ} (c : Finset (Bool × Fin n)) : ℕ :=
  (c.filter (fun e => e.1 = true)).card

def arcLen {n : ℕ} (c : Finset (Bool × Fin n)) : ℕ :=
  arcRed c + arcBlue c

lemma arcLen_eq_card {n : ℕ} (c : Finset (Bool × Fin n)) : arcLen c = c.card := by
  unfold arcLen arcRed arcBlue
  have h := Finset.card_filter_add_card_filter_not (s := c) (fun e : Bool × Fin n => e.1 = false)
  have heq : c.filter (fun e => ¬ e.1 = false) = c.filter (fun e => e.1 = true) := by
    ext e; cases e.1 <;> simp
  rw [heq] at h
  exact h

def arcSignZ {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (c : Finset (Bool × Fin n)) : ℤ :=
  ∏ e ∈ c, (epsER (R := ℤ) σ p e * epsER (R := ℤ) σ p ((nextE σ).symm e))

lemma arcSignZ_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (c : Finset (Bool × Fin n)) :
    arcSignZ σ p c = 1 ∨ arcSignZ σ p c = -1 := by
  unfold arcSignZ
  induction c using Finset.induction_on with
  | empty => left; simp
  | @insert e s he ih =>
    rw [Finset.prod_insert he]
    have h1 : epsER (R := ℤ) σ p e * epsER (R := ℤ) σ p ((nextE σ).symm e) = 1 ∨
        epsER (R := ℤ) σ p e * epsER (R := ℤ) σ p ((nextE σ).symm e) = -1 := by
      rcases epsVR_sq (R := ℤ) p (headV σ e) with ha | ha <;>
        rcases epsVR_sq (R := ℤ) p (headV σ ((nextE σ).symm e)) with hb | hb <;>
        simp [epsER, ha, hb]
    rcases h1 with h1 | h1 <;> rcases ih with ih | ih <;> simp [h1, ih]

lemma arcClass_props {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e0 : Bool × Fin n) :
    let c := arcClass σ p e0
    0 < arcLen c ∧ arcRed c ≤ arcBlue c + 1 ∧ arcBlue c ≤ arcRed c + 1 := by
  classical
  intro c
  have hmem0 : e0 ∈ c := by simp [c, arcClass, Relation.EqvGen.refl]
  have hpos : 0 < arcLen c := by rw [arcLen_eq_card]; exact Finset.card_pos.mpr ⟨e0, hmem0⟩
  have hstop_le : (c.filter (fun e => qE σ p e ≠ none)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    simp only [Finset.mem_filter, c, arcClass, Finset.mem_univ, true_and] at hx hy
    exact stop_unique (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hx.1) hy.1) hx.2 hy.2
  have hbound : ∀ col : Bool,
      (c.filter (fun e => e.1 = col)).card ≤ (c.filter (fun e => e.1 = !col)).card + 1 := by
    intro col
    set s := c.filter (fun e => e.1 = col)
    have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun e => qE σ p e = none)
    have hneg_le : (s.filter (fun e => ¬ qE σ p e = none)).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) hstop_le
      intro e he
      simp only [Finset.mem_filter, s] at he ⊢
      exact ⟨he.1.1, he.2⟩
    have hgo_le : (s.filter (fun e => qE σ p e = none)).card ≤
        (c.filter (fun e => e.1 = !col)).card := by
      have hinj : ((s.filter (fun e => qE σ p e = none)).image (nextE σ)).card =
          (s.filter (fun e => qE σ p e = none)).card :=
        Finset.card_image_of_injective _ (nextE σ).injective
      rw [← hinj]
      refine Finset.card_le_card ?_
      intro e' he'
      rw [Finset.mem_image] at he'
      obtain ⟨e, he, rfl⟩ := he'
      simp only [Finset.mem_filter, s, c, arcClass, Finset.mem_univ, true_and] at he ⊢
      refine ⟨Relation.EqvGen.trans _ _ _ he.1.1 (Relation.EqvGen.rel e (nextE σ e) ⟨he.2, rfl⟩), ?_⟩
      rcases e with ⟨eb, ei⟩
      cases eb <;> simp [nextE] at he ⊢ <;> simp [he.1.2]
    omega
  refine ⟨hpos, ?_, ?_⟩
  · simpa [arcRed, arcBlue] using hbound false
  · simpa [arcRed, arcBlue] using hbound true

lemma arcClasses_sum_card {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ∑ c ∈ arcClasses σ p, c.card = 2 * n := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (f := arcClass σ p) (s := Finset.univ)
    (t := arcClasses σ p) (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ e))
  have htot : (Finset.univ : Finset (Bool × Fin n)).card = 2 * n := by simp
  rw [htot] at hfib
  rw [hfib]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hc
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hrel
    have hrel' : Relation.EqvGen (ArcStep σ p) e0 e := (Finset.mem_filter.mp hrel).2
    ext z
    simp only [arcClass, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Relation.EqvGen.trans _ _ _ hrel' h,
      fun h => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hrel') h⟩
  · intro heq
    have hmem : e ∈ arcClass σ p e := by simp [arcClass, Relation.EqvGen.refl]
    rw [heq] at hmem
    exact hmem

lemma arcClasses_card_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    (arcClasses σ p).card ≤ 2 * n := by
  have hsum := arcClasses_sum_card σ p
  have hge : ∑ _c ∈ arcClasses σ p, 1 ≤ ∑ c ∈ arcClasses σ p, c.card := by
    refine Finset.sum_le_sum fun c hc => ?_
    obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hc
    have hp := (arcClass_props σ p e0).1
    rw [arcLen_eq_card] at hp
    exact hp
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hge
  omega

lemma arcClass_mem_len_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (c : Finset (Bool × Fin n)) (hc : c ∈ arcClasses σ p) :
    1 ≤ arcLen c ∧ arcLen c ≤ 2 * n ∧ arcRed c ≤ arcBlue c + 1 ∧ arcBlue c ≤ arcRed c + 1 := by
  obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hpos, h1, h2⟩ := arcClass_props σ p e0
  have hle : (arcClass σ p e0).card ≤ 2 * n := by
    calc (arcClass σ p e0).card ≤ (Finset.univ : Finset (Bool × Fin n)).card := Finset.card_le_univ _
      _ = 2 * n := by simp
  rw [arcLen_eq_card] at hpos ⊢
  exact ⟨hpos, hle, h1, h2⟩

lemma intCast_epsER {R : Type*} [CommRing R] {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (e : Bool × Fin n) :
    ((epsER (R := ℤ) σ p e : ℤ) : R) = epsER (R := R) σ p e := by
  unfold epsER epsVR
  cases p (headV σ e) with
  | none => simp
  | some b => cases b <;> simp [sgnR]

lemma rawPoly_eq_arcProd {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (u v : R) :
    rawPoly σ p u v =
      (2 : R) ^ freeCount p *
      ∏ c ∈ arcClasses σ p,
        (1 + (arcSignZ σ p c : R) * u ^ arcRed c * v ^ arcBlue c) := by
  classical
  rw [rawPoly_eq_edgeSumR]
  congr 1
  let clsSub : Bool × Fin n → {c : Finset (Bool × Fin n) // c ∈ arcClasses σ p} :=
    fun e => ⟨arcClass σ p e, Finset.mem_image_of_mem _ (Finset.mem_univ e)⟩
  have hsurj : Function.Surjective clsSub := by
    rintro ⟨c, hc⟩
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hc
    exact ⟨e, rfl⟩
  have hcls_iff : ∀ x y, clsSub x = clsSub y ↔ Relation.EqvGen (ArcStep σ p) x y := by
    intro x y
    constructor
    · intro h
      have hx : y ∈ arcClass σ p y := by simp [arcClass, Relation.EqvGen.refl]
      have h' : arcClass σ p x = arcClass σ p y := congrArg Subtype.val h
      rw [← h'] at hx
      exact (Finset.mem_filter.mp hx).2
    · intro h
      apply Subtype.ext
      ext z
      simp only [clsSub, arcClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun hxz => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) hxz,
        fun hyz => Relation.EqvGen.trans _ _ _ h hyz⟩
  have hfib : ∀ c : {c : Finset (Bool × Fin n) // c ∈ arcClasses σ p},
      Finset.univ.filter (fun x => clsSub x = c) = c.1 := by
    rintro ⟨c, hc⟩
    obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hc
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change clsSub x = clsSub e0 ↔ x ∈ arcClass σ p e0
    rw [hcls_iff]
    simp only [arcClass, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => Relation.EqvGen.symm _ _ h, fun h => Relation.EqvGen.symm _ _ h⟩
  rw [sum_valid_eq_prodR clsSub hsurj (edgeWR σ p u v) _ (fun S => by
    simp only [hcls_iff]; exact valid_iff_eqv_const σ p S)]
  rw [← Finset.prod_attach (arcClasses σ p)]
  change (∏ c : {c // c ∈ arcClasses σ p}, _) =
    ∏ c : {c // c ∈ arcClasses σ p}, _
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [hfib c]
  congr 1
  have hsplit : (∏ e ∈ c.1, edgeWR σ p u v e) =
      (∏ e ∈ c.1, if e.1 then v else u) *
      (∏ e ∈ c.1, (epsER (R := R) σ p e * epsER σ p ((nextE σ).symm e))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    simp [edgeWR, mul_assoc]
  have huv : (∏ e ∈ c.1, if e.1 then v else u) = u ^ arcRed c.1 * v ^ arcBlue c.1 := by
    have hf : c.1.filter (fun e => ¬ e.1 = true) = c.1.filter (fun e => e.1 = false) := by
      ext e; cases e.1 <;> simp
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, mul_comm, hf]
    rfl
  have hsg : (∏ e ∈ c.1, (epsER (R := R) σ p e * epsER σ p ((nextE σ).symm e))) =
      (arcSignZ σ p c.1 : R) := by
    unfold arcSignZ
    rw [Int.cast_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [Int.cast_mul, intCast_epsER, intCast_epsER]
  rw [hsplit, huv, hsg]
  ring

lemma sum_hist_eq_twoPow {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), hist σ p r b = 2 ^ freeCount p := by
  have h := rawPoly_eq_arcProd (R := ℤ) σ p 0 0
  have hL : rawPoly (R := ℤ) σ p 0 0 =
      ((∑ r : Fin (n + 1), ∑ b : Fin (n + 1), hist σ p r b : ℕ) : ℤ) := by
    unfold rawPoly
    simp [Nat.cast_sum]
  have hR : (∏ c ∈ arcClasses σ p,
      (1 + (arcSignZ σ p c : ℤ) * (0 : ℤ) ^ arcRed c * (0 : ℤ) ^ arcBlue c)) = 1 := by
    refine Finset.prod_eq_one fun c hc => ?_
    have hlen := (arcClass_mem_len_le σ p c hc).1
    unfold arcLen at hlen
    by_cases hr : arcRed c = 0
    · have hb : arcBlue c ≠ 0 := by omega
      simp [zero_pow hb]
    · simp [zero_pow hr]
  simp only [Int.cast_id] at h
  rw [hL, hR, mul_one] at h
  exact_mod_cast h

lemma sum_profile_zero_eq_twoPow {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ∑ s : Fin (2 * n + 1), profile (hist σ p) 0 s = 2 ^ freeCount p := by
  rw [← sum_hist_eq_twoPow σ p]
  unfold profile
  simp only [Nat.choose_zero_right, one_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hlt : r.val + b.val < 2 * n + 1 := by have := r.isLt; have := b.isLt; omega
  rw [Finset.sum_eq_single ⟨r.val + b.val, hlt⟩]
  · simp
  · intro s _ hne
    have : r.val + b.val ≠ s.val := fun h => hne (Fin.ext h.symm)
    simp [this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

end ArcFactor

noncomputable section KrawAndAlgebra

def krawPoly (deg s : ℕ) : Polynomial ℤ :=
  (1 - Polynomial.X) ^ s * (1 + Polynomial.X) ^ (deg - s)

def krawCoeff (deg s d : ℕ) : ℤ :=
  (krawPoly deg s).coeff d

lemma krawPoly_natDegree_le {deg s : ℕ} (hs : s ≤ deg) :
    (krawPoly deg s).natDegree ≤ deg := by
  unfold krawPoly
  have h1 : ((1 - Polynomial.X : Polynomial ℤ) ^ s).natDegree ≤ s := by
    calc ((1 - Polynomial.X : Polynomial ℤ) ^ s).natDegree
        ≤ s * (1 - Polynomial.X : Polynomial ℤ).natDegree := Polynomial.natDegree_pow_le
      _ ≤ s * 1 := Nat.mul_le_mul_left _ (by
          calc (1 - Polynomial.X : Polynomial ℤ).natDegree
              ≤ max (1 : Polynomial ℤ).natDegree Polynomial.X.natDegree := Polynomial.natDegree_sub_le _ _
            _ ≤ 1 := by simp)
      _ = s := Nat.mul_one _
  have h2 : ((1 + Polynomial.X : Polynomial ℤ) ^ (deg - s)).natDegree ≤ deg - s := by
    calc ((1 + Polynomial.X : Polynomial ℤ) ^ (deg - s)).natDegree
        ≤ (deg - s) * (1 + Polynomial.X : Polynomial ℤ).natDegree := Polynomial.natDegree_pow_le
      _ ≤ (deg - s) * 1 := Nat.mul_le_mul_left _ (by
          calc (1 + Polynomial.X : Polynomial ℤ).natDegree
              ≤ max (1 : Polynomial ℤ).natDegree Polynomial.X.natDegree := Polynomial.natDegree_add_le _ _
            _ ≤ 1 := by simp)
      _ = deg - s := Nat.mul_one _
  calc ((1 - Polynomial.X : Polynomial ℤ) ^ s * (1 + Polynomial.X) ^ (deg - s)).natDegree
      ≤ ((1 - Polynomial.X : Polynomial ℤ) ^ s).natDegree +
          ((1 + Polynomial.X : Polynomial ℤ) ^ (deg - s)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ s + (deg - s) := Nat.add_le_add h1 h2
    _ = deg := Nat.add_sub_of_le hs

lemma krawCoeff_sum {R : Type*} [CommRing R] {deg s : ℕ} (hs : s ≤ deg) (x : R) :
    ∑ d : Fin (deg + 1), (krawCoeff deg s d.val : R) * x ^ d.val =
      (1 - x) ^ s * (1 + x) ^ (deg - s) := by
  have hdeg : (krawPoly deg s).natDegree < deg + 1 := Nat.lt_succ_of_le (krawPoly_natDegree_le hs)
  have hev := Polynomial.eval₂_eq_sum_range' (f := Int.castRingHom R) (x := x) hdeg
  rw [← Fin.sum_univ_eq_sum_range] at hev
  have hlhs : Polynomial.eval₂ (Int.castRingHom R) x (krawPoly deg s) =
      (1 - x) ^ s * (1 + x) ^ (deg - s) := by
    simp [krawPoly, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X]
  rw [hlhs] at hev
  simpa [krawCoeff] using hev.symm

def homog (d : ℕ) (p A B : Polynomial ℤ) : Polynomial ℤ :=
  ∑ i : Fin (d + 1), Polynomial.C (p.coeff i.val) * A ^ i.val * B ^ (d - i.val)

lemma homog_mul {a b : ℕ} {p q : Polynomial ℤ} (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b)
    (A B : Polynomial ℤ) :
    homog (a + b) (p * q) A B = homog a p A B * homog b q A B := by
  unfold homog
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  have h1 : ∀ k : Fin (a + b + 1),
      Polynomial.C ((p * q).coeff k.val) * A ^ k.val * B ^ (a + b - k.val) =
      ∑ i : Fin (a + 1), ∑ j : Fin (b + 1),
        if i.val + j.val = k.val then
          Polynomial.C (p.coeff i.val) * A ^ i.val * B ^ (a - i.val) *
            (Polynomial.C (q.coeff j.val) * A ^ j.val * B ^ (b - j.val))
        else 0 := by
    intro k
    rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => p.coeff x * q.coeff y)]
    have hcoeff : (∑ x ∈ Finset.range (k.val + 1), p.coeff x * q.coeff (k.val - x)) =
        ∑ i : Fin (a + 1), ∑ j : Fin (b + 1), if i.val + j.val = k.val then p.coeff i.val * q.coeff j.val else 0 := by
      have hinner : ∀ i : Fin (a + 1),
          (∑ j : Fin (b + 1), if i.val + j.val = k.val then p.coeff i.val * q.coeff j.val else 0) =
          if i.val ≤ k.val then p.coeff i.val * q.coeff (k.val - i.val) else 0 := by
        intro i
        by_cases hik : i.val ≤ k.val
        · rw [if_pos hik]
          by_cases hkb : k.val - i.val < b + 1
          · rw [Finset.sum_eq_single ⟨k.val - i.val, hkb⟩]
            · simp [Nat.add_sub_of_le hik]
            · intro j _ hne
              have : i.val + j.val ≠ k.val := fun h => hne (Fin.ext (by dsimp only; omega))
              simp [this]
            · intro h0; exact absurd (Finset.mem_univ _) h0
          · have hq0 : q.coeff (k.val - i.val) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq (by omega))
            rw [hq0, mul_zero]
            refine Finset.sum_eq_zero fun j _ => ?_
            have : i.val + j.val ≠ k.val := by have := j.isLt; omega
            simp [this]
        · rw [if_neg hik]
          refine Finset.sum_eq_zero fun j _ => ?_
          have : i.val + j.val ≠ k.val := by omega
          simp [this]
      simp_rw [hinner]
      have hfin : (∑ i : Fin (a + 1), if i.val ≤ k.val then p.coeff i.val * q.coeff (k.val - i.val) else 0) =
          ∑ x ∈ Finset.range (a + 1), if x ≤ k.val then p.coeff x * q.coeff (k.val - x) else 0 :=
        Fin.sum_univ_eq_sum_range (fun x => if x ≤ k.val then p.coeff x * q.coeff (k.val - x) else 0) (a + 1)
      rw [hfin, ← Finset.sum_filter]
      have hflt : (Finset.range (a + 1)).filter (· ≤ k.val) = Finset.range (min (a + 1) (k.val + 1)) := by
        ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
      rw [hflt]
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.min_le_right _ _)) fun x hx hnot => ?_
      simp only [Finset.mem_range] at hx hnot
      have hgt : p.natDegree < x := lt_of_le_of_lt hp (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
    rw [hcoeff, map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · have hexp1 : i.val + j.val = k.val := hij
      have hexp2 : a + b - (i.val + j.val) = (a - i.val) + (b - j.val) := by
        have := i.isLt; have := j.isLt; omega
      rw [map_mul, ← hexp1, hexp2, pow_add, pow_add]
      ring
    · simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hlt : i.val + j.val < a + b + 1 := by have := i.isLt; have := j.isLt; omega
  rw [Finset.sum_eq_single ⟨i.val + j.val, hlt⟩]
  · simp
  · intro k _ hne
    have : i.val + j.val ≠ k.val := fun h => hne (Fin.ext h.symm)
    simp [this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma homog_one_sub_X (A B : Polynomial ℤ) : homog 1 (1 - Polynomial.X) A B = B - A := by
  unfold homog
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, mul_one, one_mul,
    Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_X_zero,
    Polynomial.coeff_one, Polynomial.coeff_X]
  simp; ring

lemma homog_one_add_X (A B : Polynomial ℤ) : homog 1 (1 + Polynomial.X) A B = B + A := by
  unfold homog
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, mul_one,
    Polynomial.coeff_add, Polynomial.coeff_one_zero, Polynomial.coeff_X_zero,
    Polynomial.coeff_one, Polynomial.coeff_X]
  simp

lemma homog_pow {p : Polynomial ℤ} (hp : p.natDegree ≤ 1) (k : ℕ) (A B : Polynomial ℤ) :
    homog k (p ^ k) A B = (homog 1 p A B) ^ k := by
  induction k with
  | zero => simp [homog]
  | succ k ih =>
    have hpk : (p ^ k).natDegree ≤ k := by
      calc (p ^ k).natDegree ≤ k * p.natDegree := Polynomial.natDegree_pow_le
        _ ≤ k * 1 := Nat.mul_le_mul_left _ hp
        _ = k := Nat.mul_one _
    rw [pow_succ, pow_succ, homog_mul hpk hp, ih]

lemma homog_krawPoly {n s : ℕ} (hs : s ≤ n) (A B : Polynomial ℤ) :
    homog n (krawPoly n s) A B = (B - A) ^ s * (B + A) ^ (n - s) := by
  have h1 : (1 - Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
    calc (1 - Polynomial.X : Polynomial ℤ).natDegree
        ≤ max (1 : Polynomial ℤ).natDegree Polynomial.X.natDegree := Polynomial.natDegree_sub_le _ _
      _ ≤ 1 := by simp
  have h2 : (1 + Polynomial.X : Polynomial ℤ).natDegree ≤ 1 := by
    calc (1 + Polynomial.X : Polynomial ℤ).natDegree
        ≤ max (1 : Polynomial ℤ).natDegree Polynomial.X.natDegree := Polynomial.natDegree_add_le _ _
      _ ≤ 1 := by simp
  have hp1 : ((1 - Polynomial.X : Polynomial ℤ) ^ s).natDegree ≤ s := by
    calc ((1 - Polynomial.X : Polynomial ℤ) ^ s).natDegree ≤ s * _ := Polynomial.natDegree_pow_le
      _ ≤ s * 1 := Nat.mul_le_mul_left _ h1
      _ = s := Nat.mul_one _
  have hp2 : ((1 + Polynomial.X : Polynomial ℤ) ^ (n - s)).natDegree ≤ n - s := by
    calc ((1 + Polynomial.X : Polynomial ℤ) ^ (n - s)).natDegree ≤ (n - s) * _ := Polynomial.natDegree_pow_le
      _ ≤ (n - s) * 1 := Nat.mul_le_mul_left _ h2
      _ = n - s := Nat.mul_one _
  have hn : s + (n - s) = n := Nat.add_sub_of_le hs
  rw [← hn]
  unfold krawPoly
  rw [Nat.add_sub_cancel_left]
  rw [homog_mul hp1 hp2, homog_pow h1, homog_pow h2, homog_one_sub_X, homog_one_add_X]

lemma kraw_involution (n : ℕ) (r r' : Fin (n + 1)) :
    ∑ i : Fin (n + 1), krawCoeff n i.val r.val * krawCoeff n r'.val i.val =
      if r = r' then (2 : ℤ) ^ n else 0 := by
  have hhom := homog_krawPoly (Nat.le_of_lt_succ r'.isLt) (1 - Polynomial.X) (1 + Polynomial.X)
  have hBA1 : (1 + Polynomial.X : Polynomial ℤ) - (1 - Polynomial.X) = Polynomial.C 2 * Polynomial.X := by
    simp; ring
  have hBA2 : (1 + Polynomial.X : Polynomial ℤ) + (1 - Polynomial.X) = Polynomial.C 2 := by
    simp; ring
  rw [hBA1, hBA2] at hhom
  have hrhs : (Polynomial.C (2 : ℤ) * Polynomial.X) ^ r'.val * (Polynomial.C (2 : ℤ)) ^ (n - r'.val) =
      Polynomial.C ((2 : ℤ) ^ n) * Polynomial.X ^ r'.val := by
    rw [mul_pow, ← map_pow, ← map_pow]
    have hpow : Polynomial.C ((2 : ℤ) ^ r'.val) * Polynomial.C ((2 : ℤ) ^ (n - r'.val)) =
        Polynomial.C ((2 : ℤ) ^ n) := by
      rw [← map_mul, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ r'.isLt)]
    calc Polynomial.C ((2 : ℤ) ^ r'.val) * Polynomial.X ^ r'.val * Polynomial.C ((2 : ℤ) ^ (n - r'.val))
        = (Polynomial.C ((2 : ℤ) ^ r'.val) * Polynomial.C ((2 : ℤ) ^ (n - r'.val))) * Polynomial.X ^ r'.val := by ring
      _ = Polynomial.C ((2 : ℤ) ^ n) * Polynomial.X ^ r'.val := by rw [hpow]
  rw [hrhs] at hhom
  have hcoeff := congrArg (fun p : Polynomial ℤ => Polynomial.lcoeff ℤ r.val p) hhom
  simp only [homog, map_sum, Polynomial.lcoeff_apply, mul_assoc, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow] at hcoeff
  have hLHS : (∑ i : Fin (n + 1), krawCoeff n i.val r.val * krawCoeff n r'.val i.val) =
      ∑ i : Fin (n + 1), (krawPoly n r'.val).coeff i.val *
        (((1 - Polynomial.X : Polynomial ℤ) ^ i.val) * (1 + Polynomial.X) ^ (n - i.val)).coeff r.val := by
    refine Finset.sum_congr rfl fun i _ => by rw [mul_comm]; rfl
  rw [hLHS, hcoeff]
  by_cases hrr : r = r'
  · subst hrr; simp
  · have hne : r.val ≠ r'.val := fun h => hrr (Fin.ext h)
    simp [hrr, hne]

lemma rawPoly_uv_coeff {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (i j : Fin (n + 1)) :
    (rawPoly σ p (Trunc2.X1 : Trunc2 (n + 1) (n + 1) R) Trunc2.X2).coeff i j =
      ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
        (hist σ p r b : R) * (krawCoeff n r.val i.val : R) * (krawCoeff n b.val j.val : R) := by
  unfold rawPoly
  rw [Trunc2.coeff_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Trunc2.coeff_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 := krawCoeff_sum (R := Trunc2 (n + 1) (n + 1) R) (Nat.le_of_lt_succ r.isLt) Trunc2.X1
  have h2 := krawCoeff_sum (R := Trunc2 (n + 1) (n + 1) R) (Nat.le_of_lt_succ b.isLt) Trunc2.X2
  have hgrp :
      (hist σ p r b : Trunc2 (n + 1) (n + 1) R) *
        (1 - Trunc2.X1) ^ r.val * (1 + Trunc2.X1) ^ (n - r.val) *
        (1 - Trunc2.X2) ^ b.val * (1 + Trunc2.X2) ^ (n - b.val) =
      (hist σ p r b : Trunc2 (n + 1) (n + 1) R) *
        (((1 - Trunc2.X1) ^ r.val * (1 + Trunc2.X1) ^ (n - r.val)) *
         ((1 - Trunc2.X2) ^ b.val * (1 + Trunc2.X2) ^ (n - b.val))) := by ring
  rw [hgrp, ← h1, ← h2]
  have hprod :
      ((hist σ p r b : Trunc2 (n + 1) (n + 1) R) *
        ((∑ d1 : Fin (n + 1), (krawCoeff n r.val d1.val : Trunc2 (n + 1) (n + 1) R) * Trunc2.X1 ^ d1.val) *
         (∑ d2 : Fin (n + 1), (krawCoeff n b.val d2.val : Trunc2 (n + 1) (n + 1) R) * Trunc2.X2 ^ d2.val))) =
      ∑ d1 : Fin (n + 1), ∑ d2 : Fin (n + 1),
        (hist σ p r b : Trunc2 (n + 1) (n + 1) R) *
          (krawCoeff n r.val d1.val : Trunc2 (n + 1) (n + 1) R) *
          (krawCoeff n b.val d2.val : Trunc2 (n + 1) (n + 1) R) * Trunc2.monom d1.val d2.val := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d1 _ => Finset.sum_congr rfl fun d2 _ => ?_
    rw [← Trunc2.X1_pow_mul_X2_pow]
    ring
  rw [hprod, Trunc2.coeff_sum]
  rw [Finset.sum_eq_single i]
  · rw [Trunc2.coeff_sum, Finset.sum_eq_single j]
    · rw [mul_assoc, mul_assoc, Trunc2.natCast_mul_coeff, Trunc2.intCast_mul_coeff,
        Trunc2.intCast_mul_coeff]
      simp [Trunc2.monom, mul_assoc]
    · intro d2 _ hne
      rw [mul_assoc, mul_assoc, Trunc2.natCast_mul_coeff, Trunc2.intCast_mul_coeff,
        Trunc2.intCast_mul_coeff]
      have : j.val ≠ d2.val := fun h => hne (Fin.ext h.symm)
      simp [Trunc2.monom, this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · intro d1 _ hne
    rw [Trunc2.coeff_sum]
    refine Finset.sum_eq_zero fun d2 _ => ?_
    rw [mul_assoc, mul_assoc, Trunc2.natCast_mul_coeff, Trunc2.intCast_mul_coeff,
      Trunc2.intCast_mul_coeff]
    have : i.val ≠ d1.val := fun h => hne (Fin.ext h.symm)
    simp [Trunc2.monom, this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

noncomputable def arcProdUV {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) : Trunc2 (n + 1) (n + 1) R :=
  ∏ c ∈ arcClasses σ p,
    (1 + (arcSignZ σ p c : Trunc2 (n + 1) (n + 1) R) * Trunc2.X1 ^ arcRed c * Trunc2.X2 ^ arcBlue c)

lemma inv_kraw_arcProdUV {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r0 b0 : Fin (n + 1)) :
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      krawCoeff n i.val r0.val * krawCoeff n j.val b0.val *
        (arcProdUV (R := ℤ) σ p).coeff i j =
      (2 : ℤ) ^ (2 * n - freeCount p) * (hist σ p r0 b0 : ℤ) := by
  have hfree : freeCount p ≤ 2 * n := by
    unfold freeCount
    calc (Finset.univ.filter (fun v : Bool × Fin n => p v = none)).card
        ≤ (Finset.univ : Finset (Bool × Fin n)).card := Finset.card_filter_le _ _
      _ = 2 * n := by simp
  have h2ne : ((2 : ℤ) ^ freeCount p) ≠ 0 := by positivity
  apply mul_left_cancel₀ h2ne
  have hmul : (2 : ℤ) ^ freeCount p *
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        krawCoeff n i.val r0.val * krawCoeff n j.val b0.val * (arcProdUV (R := ℤ) σ p).coeff i j) =
      ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        krawCoeff n i.val r0.val * krawCoeff n j.val b0.val *
          ((rawPoly σ p (Trunc2.X1 : Trunc2 (n + 1) (n + 1) ℤ) Trunc2.X2).coeff i j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hraw := rawPoly_eq_arcProd (R := Trunc2 (n + 1) (n + 1) ℤ) σ p Trunc2.X1 Trunc2.X2
    have h2pow : ((2 : Trunc2 (n + 1) (n + 1) ℤ) ^ freeCount p) =
        (((2 ^ freeCount p : ℕ) : Trunc2 (n + 1) (n + 1) ℤ)) := by simp
    have hcoeff : (rawPoly σ p (Trunc2.X1 : Trunc2 (n + 1) (n + 1) ℤ) Trunc2.X2).coeff i j =
        (2 : ℤ) ^ freeCount p * (arcProdUV (R := ℤ) σ p).coeff i j := by
      rw [hraw]
      change ((2 : Trunc2 (n + 1) (n + 1) ℤ) ^ freeCount p * arcProdUV (R := ℤ) σ p).coeff i j = _
      rw [h2pow, Trunc2.natCast_mul_coeff]
      simp
    rw [hcoeff]; ring
  rw [hmul]
  simp_rw [rawPoly_uv_coeff, Int.cast_id]
  have hreord :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        krawCoeff n i.val r0.val * krawCoeff n j.val b0.val *
          (∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
            (hist σ p r b : ℤ) * krawCoeff n r.val i.val * krawCoeff n b.val j.val)) =
      ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
        (hist σ p r b : ℤ) *
          (∑ i : Fin (n + 1), krawCoeff n i.val r0.val * krawCoeff n r.val i.val) *
          (∑ j : Fin (n + 1), krawCoeff n j.val b0.val * krawCoeff n b.val j.val) := by
    have h1 : ∀ i j : Fin (n + 1),
        krawCoeff n i.val r0.val * krawCoeff n j.val b0.val *
          (∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
            (hist σ p r b : ℤ) * krawCoeff n r.val i.val * krawCoeff n b.val j.val) =
        ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
          (hist σ p r b : ℤ) * (krawCoeff n i.val r0.val * krawCoeff n r.val i.val) *
            (krawCoeff n j.val b0.val * krawCoeff n b.val j.val) := by
      intro i j
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring
    simp_rw [h1]
    have h2 : ∀ r b : Fin (n + 1),
        (hist σ p r b : ℤ) *
          (∑ i : Fin (n + 1), krawCoeff n i.val r0.val * krawCoeff n r.val i.val) *
          (∑ j : Fin (n + 1), krawCoeff n j.val b0.val * krawCoeff n b.val j.val) =
        ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          (hist σ p r b : ℤ) * (krawCoeff n i.val r0.val * krawCoeff n r.val i.val) *
            (krawCoeff n j.val b0.val * krawCoeff n b.val j.val) := by
      intro r b
      rw [Finset.mul_sum (a := (hist σ p r b : ℤ)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    simp_rw [h2]
    let e : (Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) ≃
        (Fin (n + 1) × Fin (n + 1) × Fin (n + 1) × Fin (n + 1)) :=
      { toFun := fun ⟨i, j, r, b⟩ => (r, b, i, j)
        invFun := fun ⟨r, b, i, j⟩ => (i, j, r, b)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have heq := Fintype.sum_equiv e
      (fun x => (hist σ p x.2.2.1 x.2.2.2 : ℤ) *
        (krawCoeff n x.1.val r0.val * krawCoeff n x.2.2.1.val x.1.val) *
        (krawCoeff n x.2.1.val b0.val * krawCoeff n x.2.2.2.val x.2.1.val))
      (fun y => (hist σ p y.1 y.2.1 : ℤ) *
        (krawCoeff n y.2.2.1.val r0.val * krawCoeff n y.1.val y.2.2.1.val) *
        (krawCoeff n y.2.2.2.val b0.val * krawCoeff n y.2.1.val y.2.2.2.val))
      (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using heq
  rw [hreord]
  simp_rw [kraw_involution]
  rw [Finset.sum_eq_single r0]
  · rw [Finset.sum_eq_single b0]
    · simp only [↓reduceIte]
      have hpow : (2 : ℤ) ^ freeCount p * (2 : ℤ) ^ (2 * n - freeCount p) = (2 : ℤ) ^ n * (2 : ℤ) ^ n := by
        rw [← pow_add, ← pow_add, Nat.add_sub_of_le hfree, two_mul]
      calc (hist σ p r0 b0 : ℤ) * (2 : ℤ) ^ n * (2 : ℤ) ^ n
          = ((2 : ℤ) ^ n * (2 : ℤ) ^ n) * (hist σ p r0 b0 : ℤ) := by ring
        _ = ((2 : ℤ) ^ freeCount p * (2 : ℤ) ^ (2 * n - freeCount p)) * (hist σ p r0 b0 : ℤ) := by rw [hpow]
        _ = (2 : ℤ) ^ freeCount p * ((2 : ℤ) ^ (2 * n - freeCount p) * (hist σ p r0 b0 : ℤ)) := by ring
    · intro b _ hne
      have hne' : b0 ≠ b := fun h => hne h.symm
      simp [hne']
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · intro r _ hne
    refine Finset.sum_eq_zero fun b _ => ?_
    have hne' : r0 ≠ r := fun h => hne h.symm
    simp [hne']
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma hist_le_twoPow_freeCount {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (r b : Fin (n + 1)) :
    hist σ p r b ≤ 2 ^ freeCount p := by
  rw [← sum_hist_eq_twoPow σ p]
  calc hist σ p r b ≤ ∑ b' : Fin (n + 1), hist σ p r b' :=
        Finset.single_le_sum (f := fun b' => hist σ p r b') (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    _ ≤ ∑ r' : Fin (n + 1), ∑ b' : Fin (n + 1), hist σ p r' b' :=
        Finset.single_le_sum (f := fun r' => ∑ b' : Fin (n + 1), hist σ p r' b') (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)

lemma shiftRight_zmod_eq {B f M : ℕ} (hf : f ≤ M) (x : ℤ) :
    ((((((2 : ℤ) ^ f * x : ℤ) : ZMod (2 ^ (B + M))).val / 2 ^ f : ℕ) : ZMod (2 ^ B))) =
      (x : ZMod (2 ^ B)) := by
  have hpos : 0 < 2 ^ (B + M) := by positivity
  haveI : NeZero (2 ^ (B + M)) := ⟨Nat.ne_of_gt hpos⟩
  set q : ℕ := ((((2 : ℤ) ^ f * x : ℤ) : ZMod (2 ^ (B + M)))).val
  have hq_cast : ((q : ℤ) : ZMod (2 ^ (B + M))) = ((2 : ℤ) ^ f * x : ℤ) := by
    simp [q]
  have hdvd : ((2 ^ (B + M) : ℕ) : ℤ) ∣ (q : ℤ) - (2 : ℤ) ^ f * x := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hq_cast, sub_self]
  have h2f_dvd_pow : (2 : ℤ) ^ f ∣ ((2 ^ (B + M) : ℕ) : ℤ) := by
    push_cast
    exact pow_dvd_pow (2 : ℤ) (by omega)
  have h2f_dvd_q : (2 : ℤ) ^ f ∣ (q : ℤ) := by
    obtain ⟨k, hk⟩ := dvd_trans h2f_dvd_pow hdvd
    exact ⟨x + k, by linarith⟩
  have h2f_dvd_q_nat : 2 ^ f ∣ q := by exact_mod_cast h2f_dvd_q
  have hq_eq : (q : ℤ) = (2 : ℤ) ^ f * ((q / 2 ^ f : ℕ) : ℤ) := by
    have := Nat.mul_div_cancel' h2f_dvd_q_nat
    exact_mod_cast this.symm
  have hpow_split : ((2 ^ (B + M) : ℕ) : ℤ) = (2 : ℤ) ^ f * (2 : ℤ) ^ (B + (M - f)) := by
    push_cast
    rw [← pow_add]
    congr 1; omega
  rw [hq_eq, hpow_split] at hdvd
  have hmul_sub : (2 : ℤ) ^ f * ((q / 2 ^ f : ℕ) : ℤ) - (2 : ℤ) ^ f * x =
      (2 : ℤ) ^ f * (((q / 2 ^ f : ℕ) : ℤ) - x) := by ring
  rw [hmul_sub] at hdvd
  have hdvd2 : (2 : ℤ) ^ (B + (M - f)) ∣ ((q / 2 ^ f : ℕ) : ℤ) - x :=
    (mul_dvd_mul_iff_left (by positivity : (2 : ℤ) ^ f ≠ 0)).mp hdvd
  have hdvdB : ((2 ^ B : ℕ) : ℤ) ∣ ((q / 2 ^ f : ℕ) : ℤ) - x := by
    refine dvd_trans ?_ hdvd2
    push_cast
    exact pow_dvd_pow (2 : ℤ) (by omega)
  have hzero : ((((q / 2 ^ f : ℕ) : ℤ) - x : ℤ) : ZMod (2 ^ B)) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvdB
  rw [Int.cast_sub, sub_eq_zero] at hzero
  exact_mod_cast hzero

def Q_from_profile {n : ℕ} (prof : Fin 3 → Fin (2 * n + 1) → ℕ) : Trunc2 3 (2 * n + 1) ℤ :=
  ⟨fun h d =>
    match h.val with
    | 0 => ∑ s : Fin (2 * n + 1), (prof 0 s : ℤ) * krawCoeff (2 * n) s.val d.val
    | 1 =>
      if hd : 1 ≤ d.val then
        (∑ s : Fin (2 * n + 1), if s.val < 2 * n then
            ((n : ℤ) * (prof 0 s : ℤ) - (prof 1 s : ℤ)) * krawCoeff (2 * n - 1) s.val (d.val - 1)
          else 0) -
        (∑ s : Fin (2 * n + 1), if 1 ≤ s.val then
            (prof 1 s : ℤ) * krawCoeff (2 * n - 1) (s.val - 1) (d.val - 1)
          else 0)
      else 0
    | _ =>
      if hd : 2 ≤ d.val then
        (∑ s : Fin (2 * n + 1), if s.val + 2 ≤ 2 * n then
            ((Nat.choose n 2 : ℤ) * (prof 0 s : ℤ) - ((n - 1 : ℕ) : ℤ) * (prof 1 s : ℤ) + (prof 2 s : ℤ)) *
              krawCoeff (2 * n - 2) s.val (d.val - 2)
          else 0) +
        (∑ s : Fin (2 * n + 1), if 1 ≤ s.val ∧ s.val + 1 ≤ 2 * n then
            (-((n - 1 : ℕ) : ℤ) * (prof 1 s : ℤ) + 2 * (prof 2 s : ℤ)) *
              krawCoeff (2 * n - 2) (s.val - 1) (d.val - 2)
          else 0) +
        (∑ s : Fin (2 * n + 1), if 2 ≤ s.val then
            (prof 2 s : ℤ) * krawCoeff (2 * n - 2) (s.val - 2) (d.val - 2)
          else 0)
      else 0⟩

lemma Q_from_profile_row01_eq {n : ℕ} (prof1 prof2 : Fin 3 → Fin (2 * n + 1) → ℕ)
    (h0 : prof1 0 = prof2 0) (h1 : prof1 1 = prof2 1) (h : Fin 3) (hh : h.val < 2) (d : Fin (2 * n + 1)) :
    (Q_from_profile prof1).coeff h d = (Q_from_profile prof2).coeff h d := by
  have hc : h.val = 0 ∨ h.val = 1 := by omega
  rcases hc with hval | hval
  · simp [Q_from_profile, hval, h0]
  · simp [Q_from_profile, hval, h0, h1]

lemma trunc2_X1_pow_three {D2 : ℕ} {R : Type*} [CommRing R] :
    (Trunc2.X1 : Trunc2 3 D2 R) ^ 3 = 0 := by
  rw [show (Trunc2.X1 : Trunc2 3 D2 R) ^ 3 = Trunc2.monom 3 0 by
    simp [Trunc2.X1, Trunc2.monom_pow]]
  exact Trunc2.monom_eq_zero_of_ge 3 0 (Or.inl (le_refl 3))

lemma pow_add_nil3 {A : Type*} [CommRing A] {x : A} (hx : x ^ 3 = 0) (a b : A) (k : ℕ) :
    (a + x * b) ^ k =
      a ^ k + (k : A) * a ^ (k - 1) * b * x + (Nat.choose k 2 : A) * a ^ (k - 2) * b ^ 2 * x ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    cases k with
    | zero =>
      have hc12 : Nat.choose 1 2 = 0 := by decide
      rw [hc12]; simp; ring
    | succ m =>
      have hm1 : (m + 1) - 1 = m := by omega
      have hm2 : (m + 1 + 1) - 1 = m + 1 := by omega
      have hm3 : (m + 1 + 1) - 2 = m := by omega
      have hch : Nat.choose (m + 2) 2 = Nat.choose (m + 1) 2 + (m + 1) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
      cases m with
      | zero =>
        have hc12 : Nat.choose 1 2 = 0 := by decide
        have hc22 : Nat.choose 2 2 = 1 := by decide
        rw [hc12, hc22]; simp; ring
      | succ m' =>
        have hsub : m' + 1 + 1 - 2 = m' := by omega
        rw [hm1, hm2, hm3, hch, hsub]
        have hEq :
            (a ^ (m' + 1 + 1) + ((m' + 1 + 1 : ℕ) : A) * a ^ (m' + 1) * b * x +
              (Nat.choose (m' + 1 + 1) 2 : A) * a ^ m' * b ^ 2 * x ^ 2) * (a + x * b) =
            a ^ (m' + 1 + 1 + 1) + ((m' + 1 + 1 + 1 : ℕ) : A) * a ^ (m' + 1 + 1) * b * x +
            ((Nat.choose (m' + 1 + 1) 2 + (m' + 1 + 1) : ℕ) : A) * a ^ (m' + 1) * b ^ 2 * x ^ 2 +
            (Nat.choose (m' + 1 + 1) 2 : A) * a ^ m' * b ^ 3 * x ^ 3 := by
          push_cast; ring
        rw [hx, mul_zero, add_zero] at hEq
        exact hEq

lemma trunc2_pow_add_X1 {D2 : ℕ} {R : Type*} [CommRing R] (a b : Trunc2 3 D2 R) (k : ℕ) :
    (a + Trunc2.X1 * b) ^ k =
      a ^ k + (k : Trunc2 3 D2 R) * a ^ (k - 1) * b * Trunc2.X1 +
      (Nat.choose k 2 : Trunc2 3 D2 R) * a ^ (k - 2) * b ^ 2 * Trunc2.X1 ^ 2 :=
  pow_add_nil3 trunc2_X1_pow_three a b k

lemma trunc2_1_add_X1_pow {D2 : ℕ} {R : Type*} [CommRing R] (r : ℕ) :
    (1 + (Trunc2.X1 : Trunc2 3 D2 R)) ^ r =
      1 + (r : Trunc2 3 D2 R) * Trunc2.X1 + (Nat.choose r 2 : Trunc2 3 D2 R) * Trunc2.X1 ^ 2 := by
  have h := trunc2_pow_add_X1 (1 : Trunc2 3 D2 R) 1 r
  simpa using h

lemma trunc2_X2_mul_1_add_X1_coeff {D2 : ℕ} {R : Type*} [CommRing R] (l r : ℕ) (h : Fin 3) (d : Fin D2) :
    ((Trunc2.X2 : Trunc2 3 D2 R) ^ l * (1 + Trunc2.X1) ^ r).coeff h d =
      if d.val = l then (Nat.choose r h.val : R) else 0 := by
  rw [trunc2_1_add_X1_pow]
  have h0 : (Trunc2.X2 : Trunc2 3 D2 R) ^ l * 1 = Trunc2.monom 0 l := by
    rw [mul_one, ← Trunc2.X1_pow_mul_X2_pow 0 l, pow_zero, one_mul]
  have h1 : (Trunc2.X2 : Trunc2 3 D2 R) ^ l * ((r : Trunc2 3 D2 R) * Trunc2.X1) =
      (r : Trunc2 3 D2 R) * Trunc2.monom 1 l := by
    rw [← Trunc2.X1_pow_mul_X2_pow 1 l, pow_one]; ring
  have h2 : (Trunc2.X2 : Trunc2 3 D2 R) ^ l * ((Nat.choose r 2 : Trunc2 3 D2 R) * Trunc2.X1 ^ 2) =
      (Nat.choose r 2 : Trunc2 3 D2 R) * Trunc2.monom 2 l := by
    rw [← Trunc2.X1_pow_mul_X2_pow 2 l]; ring
  rw [mul_add, mul_add, h0, h1, h2, Trunc2.coeff_add, Trunc2.coeff_add,
    Trunc2.natCast_mul_coeff, Trunc2.natCast_mul_coeff]
  fin_cases h <;> simp [Trunc2.monom, Nat.choose_zero_right, Nat.choose_one_right]

lemma choose_sub_two (n r : ℕ) (hr : r ≤ n) :
    ((Nat.choose (n - r) 2 : ℕ) : ℤ) =
      (Nat.choose n 2 : ℤ) - ((n - 1 : ℕ) : ℤ) * (r : ℤ) + (Nat.choose r 2 : ℤ) := by
  have hmul : ∀ m : ℕ, 2 * ((Nat.choose m 2 : ℕ) : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
    intro m
    have := Nat.choose_two_right m
    have h2 : 2 * Nat.choose m 2 = m * (m - 1) := by
      rw [this]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
    cases m with
    | zero => simp
    | succ m =>
      have : (2 * Nat.choose (m + 1) 2 : ℕ) = (m + 1) * m := h2
      have hcast : ((2 * Nat.choose (m + 1) 2 : ℕ) : ℤ) = (((m + 1) * m : ℕ) : ℤ) := by exact_mod_cast this
      push_cast at hcast ⊢
      linarith
  have h2 := hmul (n - r)
  have h2n := hmul n
  have h2r := hmul r
  have hnr : ((n - r : ℕ) : ℤ) = (n : ℤ) - (r : ℤ) := Nat.cast_sub hr
  rw [hnr] at h2
  cases n with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0; simp
  | succ n' =>
    have hn1 : ((n' + 1 - 1 : ℕ) : ℤ) = (n' : ℤ) := by simp
    rw [hn1]
    push_cast at h2 h2n
    linarith

lemma mul_sub_eq_choose (n r : ℕ) (hr : r ≤ n) :
    ((r : ℤ) * ((n - r : ℕ) : ℤ)) =
      ((n - 1 : ℕ) : ℤ) * (r : ℤ) - 2 * (Nat.choose r 2 : ℤ) := by
  have h2r : 2 * ((Nat.choose r 2 : ℕ) : ℤ) = (r : ℤ) * ((r : ℤ) - 1) := by
    have := Nat.choose_two_right r
    have h2 : 2 * Nat.choose r 2 = r * (r - 1) := by
      rw [this]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
    cases r with
    | zero => simp
    | succ r =>
      have hcast : ((2 * Nat.choose (r + 1) 2 : ℕ) : ℤ) = (((r + 1) * r : ℕ) : ℤ) := by exact_mod_cast h2
      push_cast at hcast ⊢
      linarith
  have hnr : ((n - r : ℕ) : ℤ) = (n : ℤ) - (r : ℤ) := Nat.cast_sub hr
  rw [hnr]
  cases n with
  | zero =>
    have hr0 : r = 0 := by omega
    subst hr0; simp
  | succ n' =>
    have hn1 : ((n' + 1 - 1 : ℕ) : ℤ) = (n' : ℤ) := by simp
    rw [hn1]
    push_cast
    linarith

lemma kraw_term_X2_coeff {D2 : ℕ} {R : Type*} [CommRing R] {deg s : ℕ} (hs : s ≤ deg)
    (hdeg : deg < D2) (h : Fin 3) (d : Fin D2) :
    (((1 - (Trunc2.X2 : Trunc2 3 D2 R)) ^ s * (1 + Trunc2.X2) ^ (deg - s))).coeff h d =
      if h.val = 0 then (krawCoeff deg s d.val : R) else 0 := by
  rw [← krawCoeff_sum hs (Trunc2.X2 : Trunc2 3 D2 R), Trunc2.coeff_sum]
  by_cases hd : d.val < deg + 1
  · rw [Finset.sum_eq_single ⟨d.val, hd⟩]
    · rw [Trunc2.intCast_mul_coeff, show (Trunc2.X2 : Trunc2 3 D2 R) ^ d.val = Trunc2.monom 0 d.val by
        simp [Trunc2.X2, Trunc2.monom_pow]]
      simp [Trunc2.monom]
    · intro k _ hne
      rw [Trunc2.intCast_mul_coeff, show (Trunc2.X2 : Trunc2 3 D2 R) ^ k.val = Trunc2.monom 0 k.val by
        simp [Trunc2.X2, Trunc2.monom_pow]]
      have : d.val ≠ k.val := fun h' => hne (Fin.ext h'.symm)
      simp [Trunc2.monom, this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · have hkc : krawCoeff deg s d.val = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (krawPoly_natDegree_le hs) (by omega))
    have hRHS : (if h.val = 0 then (krawCoeff deg s d.val : R) else 0) = 0 := by simp [hkc]
    rw [hRHS]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Trunc2.intCast_mul_coeff, show (Trunc2.X2 : Trunc2 3 D2 R) ^ k.val = Trunc2.monom 0 k.val by
      simp [Trunc2.X2, Trunc2.monom_pow]]
    have : d.val ≠ k.val := by have := k.isLt; omega
    simp [Trunc2.monom, this]

lemma mul_monom_coeff {D1 D2 : ℕ} {R : Type*} [CommRing R] (f : Trunc2 D1 D2 R) (a b : ℕ)
    (i : Fin D1) (j : Fin D2) :
    (f * Trunc2.monom a b).coeff i j =
      if ha : a ≤ i.val then
        if hb : b ≤ j.val then f.coeff ⟨i.val - a, by omega⟩ ⟨j.val - b, by omega⟩ else 0
      else 0 := by
  rw [Trunc2.coeff_mul]
  by_cases ha : a ≤ i.val
  · by_cases hb : b ≤ j.val
    · simp only [ha, hb, ↓reduceDIte]
      have ha' : a < D1 := by have := i.isLt; omega
      have hb' : b < D2 := by have := j.isLt; omega
      rw [Finset.sum_eq_single ⟨i.val - a, by omega⟩]
      · rw [Finset.sum_eq_single ⟨a, ha'⟩]
        · rw [Finset.sum_eq_single ⟨j.val - b, by omega⟩]
          · rw [Finset.sum_eq_single ⟨b, hb'⟩]
            · simp [Trunc2.monom, Nat.sub_add_cancel ha, Nat.sub_add_cancel hb]
            · intro j2 _ hne
              have : j2.val ≠ b := fun h => hne (Fin.ext h)
              simp [Trunc2.monom, this]
            · intro h0; exact absurd (Finset.mem_univ _) h0
          · intro j1 _ hne
            refine Finset.sum_eq_zero fun j2 _ => ?_
            split_ifs with hc
            · simp only [Trunc2.monom]
              split_ifs with hm
              · exfalso; apply hne; exact Fin.ext (by dsimp only; omega)
              · simp
            · rfl
          · intro h0; exact absurd (Finset.mem_univ _) h0
        · intro i2 _ hne
          refine Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
          have : i2.val ≠ a := fun h => hne (Fin.ext h)
          simp [Trunc2.monom, this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · intro i1 _ hne
        refine Finset.sum_eq_zero fun i2 _ => Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
        split_ifs with hc
        · simp only [Trunc2.monom]
          split_ifs with hm
          · exfalso; apply hne; exact Fin.ext (by dsimp only; omega)
          · simp
        · rfl
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · simp only [ha, hb, ↓reduceDIte]
      refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ =>
        Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
      split_ifs with hc
      · simp only [Trunc2.monom]
        split_ifs with hm
        · exfalso; apply hb; omega
        · simp
      · rfl
  · simp only [ha, ↓reduceDIte]
    refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ =>
      Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
    split_ifs with hc
    · simp only [Trunc2.monom]
      split_ifs with hm
      · exfalso; apply ha; omega
      · simp
    · rfl

lemma single_zt_term_coeff {n : ℕ} (r b : Fin (n + 1)) (h : Fin 3) (d : Fin (2 * n + 1)) :
    let U : Trunc2 3 (2 * n + 1) ℤ := Trunc2.X2 * (1 + Trunc2.X1)
    let V : Trunc2 3 (2 * n + 1) ℤ := Trunc2.X2
    ((1 - U) ^ r.val * (1 + U) ^ (n - r.val) * (1 - V) ^ b.val * (1 + V) ^ (n - b.val)).coeff h d =
    let s := r.val + b.val
    match h.val with
    | 0 => krawCoeff (2 * n) s d.val
    | 1 =>
      if 1 ≤ d.val then
        (if s < 2 * n then ((n : ℤ) - (r.val : ℤ)) * krawCoeff (2 * n - 1) s (d.val - 1) else 0) -
        (if 1 ≤ s then (r.val : ℤ) * krawCoeff (2 * n - 1) (s - 1) (d.val - 1) else 0)
      else 0
    | _ =>
      if 2 ≤ d.val then
        (if s + 2 ≤ 2 * n then
          ((Nat.choose n 2 : ℤ) - ((n - 1 : ℕ) : ℤ) * (r.val : ℤ) + (Nat.choose r.val 2 : ℤ)) *
            krawCoeff (2 * n - 2) s (d.val - 2)
        else 0) +
        (if 1 ≤ s ∧ s + 1 ≤ 2 * n then
          (-((n - 1 : ℕ) : ℤ) * (r.val : ℤ) + 2 * (Nat.choose r.val 2 : ℤ)) *
            krawCoeff (2 * n - 2) (s - 1) (d.val - 2)
        else 0) +
        (if 2 ≤ s then (Nat.choose r.val 2 : ℤ) * krawCoeff (2 * n - 2) (s - 2) (d.val - 2) else 0)
      else 0 := by
  intro U V
  set A : Trunc2 3 (2 * n + 1) ℤ := 1 - Trunc2.X2
  set B : Trunc2 3 (2 * n + 1) ℤ := 1 + Trunc2.X2
  have h1U : 1 - U = A + Trunc2.X1 * (-Trunc2.X2) := by dsimp only [U, A]; ring
  have h2U : 1 + U = B + Trunc2.X1 * Trunc2.X2 := by dsimp only [U, B]; ring
  have hX3 : (Trunc2.X1 : Trunc2 3 (2 * n + 1) ℤ) ^ 3 = 0 := trunc2_X1_pow_three
  have hpow1 := trunc2_pow_add_X1 A (-Trunc2.X2) r.val
  have hpow2 := trunc2_pow_add_X1 B Trunc2.X2 (n - r.val)
  have hterm :
      (1 - U) ^ r.val * (1 + U) ^ (n - r.val) * (1 - V) ^ b.val * (1 + V) ^ (n - b.val) =
      (A ^ (r.val + b.val) * B ^ (2 * n - (r.val + b.val))) +
      (((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val + b.val) * B ^ (2 * n - 1 - (r.val + b.val))) -
       (r.val : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val + b.val - 1) * B ^ (2 * n - (r.val + b.val)))) *
        Trunc2.monom 1 1 +
      (((Nat.choose (n - r.val) 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val + b.val) * B ^ (2 * n - 2 - (r.val + b.val))) -
       ((r.val : Trunc2 3 (2 * n + 1) ℤ) * ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ)) *
         (A ^ (r.val + b.val - 1) * B ^ (2 * n - 1 - (r.val + b.val))) +
       ((Nat.choose r.val 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val + b.val - 2) * B ^ (2 * n - (r.val + b.val)))) *
        Trunc2.monom 2 2 := by
    rw [h1U, h2U, hpow1, hpow2]
    have hV1 : 1 - V = A := rfl
    have hV2 : 1 + V = B := rfl
    rw [hV1, hV2]
    have hrle : r.val ≤ n := Nat.le_of_lt_succ r.isLt
    have hble : b.val ≤ n := Nat.le_of_lt_succ b.isLt
    have hm11 : (Trunc2.X1 : Trunc2 3 (2 * n + 1) ℤ) * Trunc2.X2 = Trunc2.monom 1 1 := by
      rw [← Trunc2.X1_pow_mul_X2_pow 1 1, pow_one, pow_one]
    have hm22 : (Trunc2.X1 : Trunc2 3 (2 * n + 1) ℤ) ^ 2 * Trunc2.X2 ^ 2 = Trunc2.monom 2 2 := by
      rw [← Trunc2.X1_pow_mul_X2_pow 2 2]
    have hA0 : A ^ r.val * A ^ b.val = A ^ (r.val + b.val) := (pow_add A r.val b.val).symm
    have hB0 : B ^ (n - r.val) * B ^ (n - b.val) = B ^ (2 * n - (r.val + b.val)) := by
      rw [← pow_add]; congr 1; omega
    have hB1 : ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (B ^ (n - r.val - 1) * B ^ (n - b.val)) =
        ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * B ^ (2 * n - 1 - (r.val + b.val)) := by
      by_cases hnr : n - r.val = 0
      · simp [hnr]
      · rw [← pow_add]; congr 2; omega
    have hA1 : (r.val : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val - 1) * A ^ b.val) =
        (r.val : Trunc2 3 (2 * n + 1) ℤ) * A ^ (r.val + b.val - 1) := by
      by_cases hr0 : r.val = 0
      · simp [hr0]
      · rw [← pow_add]; congr 2; omega
    have hB2 : ((Nat.choose (n - r.val) 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (B ^ (n - r.val - 2) * B ^ (n - b.val)) =
        ((Nat.choose (n - r.val) 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * B ^ (2 * n - 2 - (r.val + b.val)) := by
      by_cases hnr : n - r.val < 2
      · rw [Nat.choose_eq_zero_of_lt hnr]; simp
      · rw [← pow_add]; congr 2; omega
    have hA2 : ((Nat.choose r.val 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val - 2) * A ^ b.val) =
        ((Nat.choose r.val 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * A ^ (r.val + b.val - 2) := by
      by_cases hr2 : r.val < 2
      · rw [Nat.choose_eq_zero_of_lt hr2]; simp
      · rw [← pow_add]; congr 2; omega
    have hAB11 : ((r.val : Trunc2 3 (2 * n + 1) ℤ) * ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ)) *
        ((A ^ (r.val - 1) * A ^ b.val) * (B ^ (n - r.val - 1) * B ^ (n - b.val))) =
        ((r.val : Trunc2 3 (2 * n + 1) ℤ) * ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ)) *
        (A ^ (r.val + b.val - 1) * B ^ (2 * n - 1 - (r.val + b.val))) := by
      by_cases hr0 : r.val = 0
      · simp [hr0]
      · by_cases hnr : n - r.val = 0
        · simp [hnr]
        · rw [← pow_add, ← pow_add]; congr 2 <;> [congr 1; congr 1] <;> omega
    have hexpand :
        (A ^ r.val + (r.val : Trunc2 3 (2 * n + 1) ℤ) * A ^ (r.val - 1) * (-Trunc2.X2) * Trunc2.X1 +
          (Nat.choose r.val 2 : Trunc2 3 (2 * n + 1) ℤ) * A ^ (r.val - 2) * (-Trunc2.X2) ^ 2 * Trunc2.X1 ^ 2) *
        (B ^ (n - r.val) + ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * B ^ (n - r.val - 1) * Trunc2.X2 * Trunc2.X1 +
          (Nat.choose (n - r.val) 2 : Trunc2 3 (2 * n + 1) ℤ) * B ^ (n - r.val - 2) * Trunc2.X2 ^ 2 * Trunc2.X1 ^ 2) *
        A ^ b.val * B ^ (n - b.val) =
        (A ^ r.val * A ^ b.val) * (B ^ (n - r.val) * B ^ (n - b.val)) +
        (((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (B ^ (n - r.val - 1) * B ^ (n - b.val)) * (A ^ r.val * A ^ b.val) -
         (r.val : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val - 1) * A ^ b.val) * (B ^ (n - r.val) * B ^ (n - b.val))) *
          (Trunc2.X1 * Trunc2.X2) +
        (((Nat.choose (n - r.val) 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (B ^ (n - r.val - 2) * B ^ (n - b.val)) * (A ^ r.val * A ^ b.val) -
         ((r.val : Trunc2 3 (2 * n + 1) ℤ) * ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ)) *
           ((A ^ (r.val - 1) * A ^ b.val) * (B ^ (n - r.val - 1) * B ^ (n - b.val))) +
         ((Nat.choose r.val 2 : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val - 2) * A ^ b.val) * (B ^ (n - r.val) * B ^ (n - b.val))) *
          (Trunc2.X1 ^ 2 * Trunc2.X2 ^ 2) +
        (Trunc2.X1 ^ 3) * (
          (r.val : Trunc2 3 (2 * n + 1) ℤ) * (Nat.choose (n - r.val) 2 : Trunc2 3 (2 * n + 1) ℤ) *
            A ^ (r.val - 1) * A ^ b.val * B ^ (n - r.val - 2) * B ^ (n - b.val) * (-Trunc2.X2) * Trunc2.X2 ^ 2 +
          (Nat.choose r.val 2 : Trunc2 3 (2 * n + 1) ℤ) * ((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) *
            A ^ (r.val - 2) * A ^ b.val * B ^ (n - r.val - 1) * B ^ (n - b.val) * Trunc2.X2 ^ 3 +
          (Nat.choose r.val 2 : Trunc2 3 (2 * n + 1) ℤ) * (Nat.choose (n - r.val) 2 : Trunc2 3 (2 * n + 1) ℤ) *
            A ^ (r.val - 2) * A ^ b.val * B ^ (n - r.val - 2) * B ^ (n - b.val) * Trunc2.X2 ^ 4 * Trunc2.X1) := by
      ring
    rw [hexpand, hX3, zero_mul, add_zero, hm11, hm22, hA0, hB0, hB1, hA1, hB2, hA2, hAB11]
    ring
  rw [hterm]
  have hrle : r.val ≤ n := Nat.le_of_lt_succ r.isLt
  have hble : b.val ≤ n := Nat.le_of_lt_succ b.isLt
  have h0k := kraw_term_X2_coeff (D2 := 2 * n + 1) (R := ℤ) (deg := 2 * n) (s := r.val + b.val) (by omega) (by omega)
  fin_cases h
  · simp only [Fin.zero_eta, Fin.val_zero, Trunc2.coeff_add, mul_monom_coeff,
      show ¬ (1 ≤ (0 : ℕ)) by omega, show ¬ (2 ≤ (0 : ℕ)) by omega, ↓reduceDIte, add_zero]
    simpa [A, B] using h0k ⟨0, by omega⟩ d
  · simp only [Fin.mk_one, Fin.val_one, Trunc2.coeff_add, mul_monom_coeff,
      show (1 ≤ (1 : ℕ)) by omega, show ¬ (2 ≤ (1 : ℕ)) by omega, ↓reduceDIte, add_zero]
    have h0k1 : (A ^ (r.val + b.val) * B ^ (2 * n - (r.val + b.val))).coeff 1 d = 0 := by
      dsimp only [A, B]
      rw [show (1 : Fin 3) = ⟨1, by omega⟩ from rfl, h0k ⟨1, by omega⟩ d]
      simp
    rw [h0k1, zero_add]
    by_cases hd : 1 ≤ d.val
    · rw [dif_pos hd, if_pos hd]
      rw [Trunc2.coeff_sub, Trunc2.natCast_mul_coeff, Trunc2.natCast_mul_coeff]
      congr 1
      · by_cases hs : r.val + b.val < 2 * n
        · rw [if_pos hs, kraw_term_X2_coeff (by omega) (by omega)]
          simp [Nat.cast_sub hrle]
        · have hrn : r.val = n := by omega
          rw [if_neg hs, hrn]; simp
      · by_cases hs : 1 ≤ r.val + b.val
        · have hexp : 2 * n - (r.val + b.val) = (2 * n - 1) - (r.val + b.val - 1) := by omega
          rw [if_pos hs, hexp, kraw_term_X2_coeff (by omega) (by omega)]
          simp
        · have hr0 : r.val = 0 := by omega
          rw [if_neg hs, hr0]; simp
    · rw [dif_neg hd, if_neg hd]
  · simp only [Fin.val_two, Trunc2.coeff_add, mul_monom_coeff,
      show (1 ≤ (2 : ℕ)) by omega, show (2 ≤ (2 : ℕ)) by omega, ↓reduceDIte]
    have h0k2 : (A ^ (r.val + b.val) * B ^ (2 * n - (r.val + b.val))).coeff ⟨2, by omega⟩ d = 0 := by
      dsimp only [A, B]
      rw [h0k ⟨2, by omega⟩ d]
      simp
    rw [h0k2, zero_add]
    have hmid0 :
        (if hb : 1 ≤ d.val then
          (((n - r.val : ℕ) : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val + b.val) * B ^ (2 * n - 1 - (r.val + b.val))) -
           (r.val : Trunc2 3 (2 * n + 1) ℤ) * (A ^ (r.val + b.val - 1) * B ^ (2 * n - (r.val + b.val)))).coeff
            ⟨2 - 1, by omega⟩ ⟨d.val - 1, by omega⟩
        else 0) = 0 := by
      split_ifs with hd1
      · rw [Trunc2.coeff_sub, Trunc2.natCast_mul_coeff, Trunc2.natCast_mul_coeff]
        have h1 : ((n - r.val : ℕ) : ℤ) * (A ^ (r.val + b.val) * B ^ (2 * n - 1 - (r.val + b.val))).coeff ⟨1, by omega⟩ ⟨d.val - 1, by omega⟩ = 0 := by
          by_cases hs : r.val + b.val ≤ 2 * n - 1
          · rw [kraw_term_X2_coeff hs (by omega)]; simp
          · have : n - r.val = 0 := by omega
            simp [this]
        have h2 : (r.val : ℤ) * (A ^ (r.val + b.val - 1) * B ^ (2 * n - (r.val + b.val))).coeff ⟨1, by omega⟩ ⟨d.val - 1, by omega⟩ = 0 := by
          by_cases hs : 1 ≤ r.val + b.val
          · have : 2 * n - (r.val + b.val) = (2 * n - 1) - (r.val + b.val - 1) := by omega
            rw [this, kraw_term_X2_coeff (by omega) (by omega)]; simp
          · have : r.val = 0 := by omega
            simp [this]
        rw [show (⟨2 - 1, _⟩ : Fin 3) = ⟨1, by omega⟩ from rfl, h1, h2, sub_self]
      · rfl
    rw [hmid0, zero_add]
    by_cases hd : 2 ≤ d.val
    · rw [dif_pos hd, if_pos hd]
      rw [Trunc2.coeff_sub, Trunc2.natCast_mul_coeff,
        mul_assoc, Trunc2.natCast_mul_coeff, Trunc2.natCast_mul_coeff, Trunc2.natCast_mul_coeff]
      have hterm1 :
          ((Nat.choose (n - r.val) 2 : ℕ) : ℤ) *
            (A ^ (r.val + b.val) * B ^ (2 * n - 2 - (r.val + b.val))).coeff ⟨2 - 2, by omega⟩ ⟨d.val - 2, by omega⟩ =
          if r.val + b.val + 2 ≤ 2 * n then
            ((Nat.choose n 2 : ℤ) - ((n - 1 : ℕ) : ℤ) * (r.val : ℤ) + (Nat.choose r.val 2 : ℤ)) *
              krawCoeff (2 * n - 2) (r.val + b.val) (d.val - 2)
          else 0 := by
        by_cases hs : r.val + b.val + 2 ≤ 2 * n
        · rw [if_pos hs, kraw_term_X2_coeff (by omega) (by omega)]
          simp [choose_sub_two n r.val hrle]
        · have hlt : n - r.val < 2 := by omega
          rw [if_neg hs, Nat.choose_eq_zero_of_lt hlt]; simp
      have hterm2 :
          -((r.val : ℤ) * (((n - r.val : ℕ) : ℤ) *
            (A ^ (r.val + b.val - 1) * B ^ (2 * n - 1 - (r.val + b.val))).coeff ⟨2 - 2, by omega⟩ ⟨d.val - 2, by omega⟩)) =
          if 1 ≤ r.val + b.val ∧ r.val + b.val + 1 ≤ 2 * n then
            (-((n - 1 : ℕ) : ℤ) * (r.val : ℤ) + 2 * (Nat.choose r.val 2 : ℤ)) *
              krawCoeff (2 * n - 2) (r.val + b.val - 1) (d.val - 2)
          else 0 := by
        by_cases hs : 1 ≤ r.val + b.val ∧ r.val + b.val + 1 ≤ 2 * n
        · rw [if_pos hs]
          have hexp : 2 * n - 1 - (r.val + b.val) = (2 * n - 2) - (r.val + b.val - 1) := by omega
          rw [hexp, kraw_term_X2_coeff (by omega) (by omega)]
          simp only [Nat.sub_self, ↓reduceIte, Int.cast_id]
          have hmr := mul_sub_eq_choose n r.val hrle
          calc -((r.val : ℤ) * (((n - r.val : ℕ) : ℤ) * krawCoeff (2 * n - 2) (r.val + b.val - 1) (d.val - 2)))
              = -(((r.val : ℤ) * ((n - r.val : ℕ) : ℤ)) * krawCoeff (2 * n - 2) (r.val + b.val - 1) (d.val - 2)) := by ring
            _ = -((((n - 1 : ℕ) : ℤ) * (r.val : ℤ) - 2 * (Nat.choose r.val 2 : ℤ)) *
                  krawCoeff (2 * n - 2) (r.val + b.val - 1) (d.val - 2)) := by rw [hmr]
            _ = (-((n - 1 : ℕ) : ℤ) * (r.val : ℤ) + 2 * (Nat.choose r.val 2 : ℤ)) *
                  krawCoeff (2 * n - 2) (r.val + b.val - 1) (d.val - 2) := by ring
        · rw [if_neg hs]
          have hzero : r.val = 0 ∨ n - r.val = 0 := by omega
          rcases hzero with h0 | h0 <;> simp [h0]
      have hterm3 :
          ((Nat.choose r.val 2 : ℕ) : ℤ) *
            (A ^ (r.val + b.val - 2) * B ^ (2 * n - (r.val + b.val))).coeff ⟨2 - 2, by omega⟩ ⟨d.val - 2, by omega⟩ =
          if 2 ≤ r.val + b.val then (Nat.choose r.val 2 : ℤ) * krawCoeff (2 * n - 2) (r.val + b.val - 2) (d.val - 2) else 0 := by
        by_cases hs : 2 ≤ r.val + b.val
        · rw [if_pos hs]
          have hexp : 2 * n - (r.val + b.val) = (2 * n - 2) - (r.val + b.val - 2) := by omega
          rw [hexp, kraw_term_X2_coeff (by omega) (by omega)]
          simp
        · have hlt : r.val < 2 := by omega
          rw [if_neg hs, Nat.choose_eq_zero_of_lt hlt]; simp
      rw [sub_eq_add_neg, hterm1, hterm2, hterm3]
    · rw [dif_neg hd, if_neg hd]

lemma sum_by_total {n : ℕ} (H : Fin (n + 1) → Fin (n + 1) → ℕ) (f : Fin (2 * n + 1) → ℤ) (h : ℕ) :
    (∑ s : Fin (2 * n + 1), (profile H h s : ℤ) * f s) =
      ∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
        (H r b : ℤ) * (Nat.choose r.val h : ℤ) * f ⟨r.val + b.val, by have := r.isLt; have := b.isLt; omega⟩ := by
  unfold profile
  simp_rw [Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hlt : r.val + b.val < 2 * n + 1 := by have := r.isLt; have := b.isLt; omega
  rw [Finset.sum_eq_single ⟨r.val + b.val, hlt⟩]
  · simp [mul_comm, mul_left_comm, mul_assoc]
  · intro s _ hne
    have : r.val + b.val ≠ s.val := fun h' => hne (Fin.ext h'.symm)
    simp [this]
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma rawPoly_zt_eq_Q_from_profile {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    rawPoly σ p (Trunc2.X2 * (1 + Trunc2.X1) : Trunc2 3 (2 * n + 1) ℤ) Trunc2.X2 =
      Q_from_profile (fun h s => profile (hist σ p) h.val s) := by
  apply Trunc2.ext; intro h d
  unfold rawPoly
  rw [Trunc2.coeff_sum]
  simp_rw [Trunc2.coeff_sum, mul_assoc, Trunc2.natCast_mul_coeff]
  have hpt : ∀ r b : Fin (n + 1),
      ((1 - (Trunc2.X2 * (1 + Trunc2.X1) : Trunc2 3 (2 * n + 1) ℤ)) ^ r.val *
       ((1 + Trunc2.X2 * (1 + Trunc2.X1)) ^ (n - r.val) *
        ((1 - Trunc2.X2) ^ b.val * (1 + Trunc2.X2) ^ (n - b.val)))).coeff h d =
      ((1 - (Trunc2.X2 * (1 + Trunc2.X1) : Trunc2 3 (2 * n + 1) ℤ)) ^ r.val *
       (1 + Trunc2.X2 * (1 + Trunc2.X1)) ^ (n - r.val) *
       (1 - Trunc2.X2) ^ b.val * (1 + Trunc2.X2) ^ (n - b.val)).coeff h d := by
    intro r b; congr 1; ring
  simp_rw [hpt, single_zt_term_coeff]
  fin_cases h
  · simp only [Q_from_profile, Fin.zero_eta, Fin.val_zero]
    rw [sum_by_total (hist σ p) (fun s => krawCoeff (2 * n) s.val d.val) 0]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
    simp [Nat.choose_zero_right]
  · simp only [Q_from_profile, Fin.mk_one, Fin.val_zero, Fin.val_one]
    by_cases hd : 1 ≤ d.val
    · simp only [hd, ↓reduceDIte, ↓reduceIte]
      have hA :
          (∑ s : Fin (2 * n + 1), if s.val < 2 * n then
            ((n : ℤ) * (profile (hist σ p) 0 s : ℤ) - (profile (hist σ p) 1 s : ℤ)) *
              krawCoeff (2 * n - 1) s.val (d.val - 1)
          else 0) =
          (n : ℤ) * (∑ s : Fin (2 * n + 1), (profile (hist σ p) 0 s : ℤ) *
            (if s.val < 2 * n then krawCoeff (2 * n - 1) s.val (d.val - 1) else 0)) -
          (∑ s : Fin (2 * n + 1), (profile (hist σ p) 1 s : ℤ) *
            (if s.val < 2 * n then krawCoeff (2 * n - 1) s.val (d.val - 1) else 0)) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
      have hB :
          (∑ s : Fin (2 * n + 1), if 1 ≤ s.val then
            (profile (hist σ p) 1 s : ℤ) * krawCoeff (2 * n - 1) (s.val - 1) (d.val - 1)
          else 0) =
          ∑ s : Fin (2 * n + 1), (profile (hist σ p) 1 s : ℤ) *
            (if 1 ≤ s.val then krawCoeff (2 * n - 1) (s.val - 1) (d.val - 1) else 0) := by
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
      rw [hA, hB, sum_by_total, sum_by_total, sum_by_total]
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, mul_one]
      split_ifs <;> ring
    · simp [hd]
  · simp only [Q_from_profile, Fin.val_zero, Fin.val_one, Fin.val_two]
    by_cases hd : 2 ≤ d.val
    · simp only [hd, ↓reduceDIte, ↓reduceIte]
      have h1 :
          (∑ s : Fin (2 * n + 1), if s.val + 2 ≤ 2 * n then
            ((Nat.choose n 2 : ℤ) * (profile (hist σ p) 0 s : ℤ) -
             ((n - 1 : ℕ) : ℤ) * (profile (hist σ p) 1 s : ℤ) + (profile (hist σ p) 2 s : ℤ)) *
              krawCoeff (2 * n - 2) s.val (d.val - 2)
          else 0) =
          (Nat.choose n 2 : ℤ) * (∑ s : Fin (2 * n + 1), (profile (hist σ p) 0 s : ℤ) *
            (if s.val + 2 ≤ 2 * n then krawCoeff (2 * n - 2) s.val (d.val - 2) else 0)) -
          ((n - 1 : ℕ) : ℤ) * (∑ s : Fin (2 * n + 1), (profile (hist σ p) 1 s : ℤ) *
            (if s.val + 2 ≤ 2 * n then krawCoeff (2 * n - 2) s.val (d.val - 2) else 0)) +
          (∑ s : Fin (2 * n + 1), (profile (hist σ p) 2 s : ℤ) *
            (if s.val + 2 ≤ 2 * n then krawCoeff (2 * n - 2) s.val (d.val - 2) else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
      have h2 :
          (∑ s : Fin (2 * n + 1), if 1 ≤ s.val ∧ s.val + 1 ≤ 2 * n then
            (-((n - 1 : ℕ) : ℤ) * (profile (hist σ p) 1 s : ℤ) + 2 * (profile (hist σ p) 2 s : ℤ)) *
              krawCoeff (2 * n - 2) (s.val - 1) (d.val - 2)
          else 0) =
          -((n - 1 : ℕ) : ℤ) * (∑ s : Fin (2 * n + 1), (profile (hist σ p) 1 s : ℤ) *
            (if 1 ≤ s.val ∧ s.val + 1 ≤ 2 * n then krawCoeff (2 * n - 2) (s.val - 1) (d.val - 2) else 0)) +
          2 * (∑ s : Fin (2 * n + 1), (profile (hist σ p) 2 s : ℤ) *
            (if 1 ≤ s.val ∧ s.val + 1 ≤ 2 * n then krawCoeff (2 * n - 2) (s.val - 1) (d.val - 2) else 0)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
      have h3 :
          (∑ s : Fin (2 * n + 1), if 2 ≤ s.val then
            (profile (hist σ p) 2 s : ℤ) * krawCoeff (2 * n - 2) (s.val - 2) (d.val - 2)
          else 0) =
          ∑ s : Fin (2 * n + 1), (profile (hist σ p) 2 s : ℤ) *
            (if 2 ≤ s.val then krawCoeff (2 * n - 2) (s.val - 2) (d.val - 2) else 0) := by
        refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
      rw [h1, h2, h3, sum_by_total, sum_by_total, sum_by_total, sum_by_total, sum_by_total, sum_by_total]
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun b _ => ?_
      simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, mul_one]
      split_ifs <;> ring
    · simp [hd]

def arcCountPlus {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) : ℕ :=
  ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = 1)).card

def arcCountMinus {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) : ℕ :=
  ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = -1)).card

def arcCountAll {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) : ℕ :=
  ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r)).card

lemma arcCountPlus_add_minus {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    arcCountPlus σ p l r + arcCountMinus σ p l r = arcCountAll σ p l r := by
  unfold arcCountPlus arcCountMinus arcCountAll
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext c
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hc, hl, hr, _⟩ | ⟨hc, hl, hr, _⟩) <;> exact ⟨hc, hl, hr⟩
    · rintro ⟨hc, hl, hr⟩
      rcases arcSignZ_pm σ p c with hs | hs
      · exact Or.inl ⟨hc, hl, hr, hs⟩
      · exact Or.inr ⟨hc, hl, hr, hs⟩
  · rw [Finset.disjoint_left]
    intro c h1 h2
    have s1 := (Finset.mem_filter.mp h1).2.2.2
    have s2 := (Finset.mem_filter.mp h2).2.2.2
    omega

lemma arcCountAll_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    arcCountAll σ p l r ≤ 2 * n :=
  le_trans (Finset.card_filter_le _ _) (arcClasses_card_le σ p)

def cTarget {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) : ℤ :=
  (arcCountMinus σ p l r : ℤ) - (arcCountPlus σ p l r : ℤ) +
    if l % 2 = 0 ∧ r % 2 = 0 then (arcCountPlus σ p (l / 2) (r / 2) : ℤ) else 0

lemma cTarget_bounds {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    -(2 * n : ℤ) ≤ cTarget σ p l r ∧ cTarget σ p l r ≤ 2 * n := by
  unfold cTarget
  have h1 : arcCountPlus σ p l r + arcCountMinus σ p l r ≤ 2 * n := by
    rw [arcCountPlus_add_minus]; exact arcCountAll_le σ p l r
  have h2 : arcCountPlus σ p (l / 2) (r / 2) ≤ 2 * n := by
    have := arcCountPlus_add_minus σ p (l / 2) (r / 2)
    have := arcCountAll_le σ p (l / 2) (r / 2)
    omega
  have h3 : arcCountMinus σ p l r + (if l % 2 = 0 ∧ r % 2 = 0 then arcCountPlus σ p (l / 2) (r / 2) else 0) ≤ 2 * n := by
    split_ifs with hev
    · by_cases hl0 : l = 0
      · subst hl0
        have hm0 : arcCountMinus σ p 0 r = 0 := by
          unfold arcCountMinus
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro c hc h; have := (arcClass_mem_len_le σ p c hc).1; omega
        rw [hm0]; omega
      · have hdisj : Disjoint
            ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = -1))
            ((arcClasses σ p).filter (fun c => arcLen c = l / 2 ∧ arcRed c = r / 2 ∧ arcSignZ σ p c = 1)) := by
          rw [Finset.disjoint_left]
          intro c h1' h2'
          have l1 := (Finset.mem_filter.mp h1').2.1
          have l2 := (Finset.mem_filter.mp h2').2.1
          omega
        have hu := Finset.card_union_of_disjoint hdisj
        have hsub : ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = -1)) ∪
            ((arcClasses σ p).filter (fun c => arcLen c = l / 2 ∧ arcRed c = r / 2 ∧ arcSignZ σ p c = 1)) ⊆
            arcClasses σ p := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hc := le_trans (Finset.card_le_card hsub) (arcClasses_card_le σ p)
        unfold arcCountMinus arcCountPlus
        omega
    · omega
  split_ifs at h3 ⊢ <;> omega

def primR (l : ℕ) : List ℕ :=
  if l % 2 = 1 then [l / 2, l / 2 + 1] else [l / 2]

def allowedR (l : ℕ) : List ℕ :=
  if l % 2 = 1 then [l / 2, l / 2 + 1]
  else if l % 4 = 0 then [l / 2]
  else [l / 2 - 1, l / 2, l / 2 + 1]

lemma mem_primR_of_arc {l r b : ℕ} (hl : l = r + b) (h1 : r ≤ b + 1) (h2 : b ≤ r + 1) :
    r ∈ primR l := by
  unfold primR
  split_ifs with hodd <;> simp <;> omega

lemma mem_allowedR_of_prim {l r : ℕ} (hr : r ∈ primR l) : r ∈ allowedR l := by
  unfold primR at hr
  unfold allowedR
  split_ifs at hr ⊢ <;> simp_all

lemma mem_allowedR_of_double {l r : ℕ} (hpos : 1 ≤ l) (hr : r ∈ primR l) :
    2 * r ∈ allowedR (2 * l) := by
  unfold primR at hr
  unfold allowedR
  have hev : ¬ (2 * l % 2 = 1) := by omega
  simp only [hev, ↓reduceIte]
  split_ifs at hr with hodd
  · have h4 : ¬ (2 * l % 4 = 0) := by omega
    simp only [h4, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    rcases hr with rfl | rfl <;> omega
  · have h4 : 2 * l % 4 = 0 := by omega
    simp only [h4, ↓reduceIte, List.mem_singleton] at hr ⊢
    omega

lemma arcCountPlus_eq_zero_of_not_prim {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) {l r : ℕ} (hnot : r ∉ primR l) :
    arcCountPlus σ p l r = 0 := by
  unfold arcCountPlus
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc h
  have hp := arcClass_mem_len_le σ p c hc
  have hlr : l = r + arcBlue c := by unfold arcLen at h; omega
  exact hnot (mem_primR_of_arc hlr (by rw [← h.2.1]; exact hp.2.2.1) (by rw [← h.2.1]; exact hp.2.2.2))

lemma arcCountMinus_eq_zero_of_not_prim {n : ℕ} (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) {l r : ℕ} (hnot : r ∉ primR l) :
    arcCountMinus σ p l r = 0 := by
  unfold arcCountMinus
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro c hc h
  have hp := arcClass_mem_len_le σ p c hc
  have hlr : l = r + arcBlue c := by unfold arcLen at h; omega
  exact hnot (mem_primR_of_arc hlr (by rw [← h.2.1]; exact hp.2.2.1) (by rw [← h.2.1]; exact hp.2.2.2))

lemma arcProd_eq_pm {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (u v : R) :
    (∏ c ∈ arcClasses σ p, (1 + (arcSignZ σ p c : R) * u ^ arcRed c * v ^ arcBlue c)) =
    ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset,
      (1 + u ^ r * v ^ (l - r)) ^ arcCountPlus σ p l r *
      (1 - u ^ r * v ^ (l - r)) ^ arcCountMinus σ p l r := by
  let key : Finset (Bool × Fin n) → ℕ × ℕ := fun c => (arcLen c, arcRed c)
  let S : Finset (ℕ × ℕ) := (Finset.Icc 1 (2 * n)).biUnion fun l => (primR l).toFinset.image fun r => (l, r)
  have hmaps : ∀ c ∈ arcClasses σ p, key c ∈ S := by
    intro c hc
    have hp := arcClass_mem_len_le σ p c hc
    rw [Finset.mem_biUnion]
    refine ⟨arcLen c, Finset.mem_Icc.mpr ⟨hp.1, hp.2.1⟩, ?_⟩
    rw [Finset.mem_image]
    exact ⟨arcRed c, List.mem_toFinset.mpr (mem_primR_of_arc rfl hp.2.2.1 hp.2.2.2), rfl⟩
  rw [← Finset.prod_fiberwise_of_maps_to hmaps]
  have hS_prod : ∀ f : ℕ × ℕ → R,
      (∏ x ∈ S, f x) = ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset, f (l, r) := by
    intro f
    rw [Finset.prod_biUnion]
    · refine Finset.prod_congr rfl fun l _ => ?_
      exact Finset.prod_image fun r1 _ r2 _ h => (Prod.mk.inj h).2
    · intro l1 _ l2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨r2, _, h2⟩ := Finset.mem_image.mp hx2
      exact hne (Prod.mk.inj h2).1.symm
  rw [hS_prod]
  refine Finset.prod_congr rfl fun l _ => Finset.prod_congr rfl fun r _ => ?_
  set fib := (arcClasses σ p).filter (fun c => key c = (l, r))
  have hfib_split : fib =
      ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = 1)) ∪
      ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = -1)) := by
    ext c
    simp only [fib, key, Prod.mk.injEq, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hc, hl, hr⟩
      rcases arcSignZ_pm σ p c with hs | hs
      · exact Or.inl ⟨hc, hl, hr, hs⟩
      · exact Or.inr ⟨hc, hl, hr, hs⟩
    · rintro (⟨hc, hl, hr, _⟩ | ⟨hc, hl, hr, _⟩) <;> exact ⟨hc, hl, hr⟩
  have hdisj : Disjoint
      ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = 1))
      ((arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = -1)) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    have s1 := (Finset.mem_filter.mp h1).2.2.2
    have s2 := (Finset.mem_filter.mp h2).2.2.2
    omega
  rw [hfib_split, Finset.prod_union hdisj]
  congr 1
  · have h1 : ∀ c ∈ (arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = 1),
        (1 + (arcSignZ σ p c : R) * u ^ arcRed c * v ^ arcBlue c) = 1 + u ^ r * v ^ (l - r) := by
      intro c hc
      obtain ⟨_, hl, hr, hs⟩ := Finset.mem_filter.mp hc
      have hb : arcBlue c = l - r := by unfold arcLen at hl; omega
      rw [hr, hb, hs]; simp
    rw [Finset.prod_congr rfl h1, Finset.prod_const]; rfl
  · have h2 : ∀ c ∈ (arcClasses σ p).filter (fun c => arcLen c = l ∧ arcRed c = r ∧ arcSignZ σ p c = -1),
        (1 + (arcSignZ σ p c : R) * u ^ arcRed c * v ^ arcBlue c) = 1 - u ^ r * v ^ (l - r) := by
      intro c hc
      obtain ⟨_, hl, hr, hs⟩ := Finset.mem_filter.mp hc
      have hb : arcBlue c = l - r := by unfold arcLen at hl; omega
      rw [hr, hb, hs]; simp [sub_eq_add_neg]
    rw [Finset.prod_congr rfl h2, Finset.prod_const]; rfl

lemma arcProd_eq_cTarget {D1 D2 : ℕ} {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (u v : Trunc2 D1 D2 R)
    (hzero : ∀ l r, 1 ≤ l → r ∈ primR l →
      ∀ i j, i.val + j.val = 0 → (u ^ r * v ^ (l - r)).coeff i j = 0)
    (htrunc : ∀ l r, 1 ≤ l → l ≤ 2 * n → r ∈ primR l → 2 * n < 2 * l →
      (u ^ r * v ^ (l - r)) ^ 2 = 0) :
    (∏ c ∈ arcClasses σ p, (1 + (arcSignZ σ p c : Trunc2 D1 D2 R) * u ^ arcRed c * v ^ arcBlue c)) =
    ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
      Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (cTarget σ p l r) := by
  rw [arcProd_eq_pm]
  have hzero_all : ∀ l r, 1 ≤ l → r ∈ allowedR l →
      ∀ i j, i.val + j.val = 0 → (u ^ r * v ^ (l - r)).coeff i j = 0 := by
    intro l r hl hr i j hij
    by_cases hp : r ∈ primR l
    · exact hzero l r hl hp i j hij
    · have hev : l % 2 = 0 ∧ r % 2 = 0 := by
        unfold primR at hp; unfold allowedR at hr
        split_ifs at hp hr <;> simp_all <;> omega
      have hp2 : r / 2 ∈ primR (l / 2) := by
        unfold primR at hp ⊢; unfold allowedR at hr
        split_ifs at hp hr ⊢ <;> simp_all <;> omega
      have hsq : u ^ r * v ^ (l - r) = (u ^ (r / 2) * v ^ (l / 2 - r / 2)) ^ 2 := by
        have hlr : u ^ r * v ^ (l - r) = u ^ (2 * (r / 2)) * v ^ (2 * (l / 2 - r / 2)) := by
          congr 1 <;> congr 1 <;> omega
        rw [hlr, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2, mul_comm 2]
      rw [hsq]
      exact Trunc2.pow_coeff_eq_zero_of_lt _ (hzero (l / 2) (r / 2) (by omega) hp2) 2 i j (by omega)
  have hsplit_c :
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (cTarget σ p l r)) =
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (arcCountMinus σ p l r : ℤ)) *
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (-(arcCountPlus σ p l r : ℤ))) *
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r))
          (if l % 2 = 0 ∧ r % 2 = 0 then (arcCountPlus σ p (l / 2) (r / 2) : ℤ) else 0)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hz := hzero_all l r (Finset.mem_Icc.mp hl).1 (List.mem_toFinset.mp hr)
    unfold cTarget
    rw [sub_eq_add_neg, Trunc2.zpowOneSub_add _ hz, Trunc2.zpowOneSub_add _ hz]
  rw [hsplit_c]
  have hA :
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (arcCountMinus σ p l r : ℤ)) =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset,
        (1 - u ^ r * v ^ (l - r)) ^ arcCountMinus σ p l r := by
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← Finset.prod_subset (s₁ := (primR l).toFinset)]
    · refine Finset.prod_congr rfl fun r _ => ?_
      simp [Trunc2.zpowOneSub]
    · intro r hr; exact List.mem_toFinset.mpr (mem_allowedR_of_prim (List.mem_toFinset.mp hr))
    · intro r _ hnot
      rw [arcCountMinus_eq_zero_of_not_prim σ p (fun h => hnot (List.mem_toFinset.mpr h))]
      simp [Trunc2.zpowOneSub]
  have hB :
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (-(arcCountPlus σ p l r : ℤ))) =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset,
        (Trunc2.zpowOneSub (u ^ r * v ^ (l - r)) (-1)) ^ arcCountPlus σ p l r := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [← Finset.prod_subset (s₁ := (primR l).toFinset)]
    · refine Finset.prod_congr rfl fun r _ => ?_
      by_cases h0 : arcCountPlus σ p l r = 0
      · simp [h0, Trunc2.zpowOneSub]
      · have hneg : ¬ (0 ≤ -(arcCountPlus σ p l r : ℤ)) := by omega
        simp [Trunc2.zpowOneSub, hneg, h0]
    · intro r hr; exact List.mem_toFinset.mpr (mem_allowedR_of_prim (List.mem_toFinset.mp hr))
    · intro r _ hnot
      rw [arcCountPlus_eq_zero_of_not_prim σ p (fun h => hnot (List.mem_toFinset.mpr h))]
      simp [Trunc2.zpowOneSub]
  have hC :
      (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (u ^ r * v ^ (l - r))
          (if l % 2 = 0 ∧ r % 2 = 0 then (arcCountPlus σ p (l / 2) (r / 2) : ℤ) else 0)) =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset,
        (Trunc2.zpowOneSub ((u ^ r * v ^ (l - r)) ^ 2) 1) ^ arcCountPlus σ p l r := by
    let S1 : Finset (ℕ × ℕ) := (Finset.Icc 1 (2 * n)).biUnion fun l => (allowedR l).toFinset.image fun r => (l, r)
    let S2 : Finset (ℕ × ℕ) := (Finset.Icc 1 (2 * n)).biUnion fun l => (primR l).toFinset.image fun r => (l, r)
    have hL1 : ∀ f : ℕ × ℕ → Trunc2 D1 D2 R,
        (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset, f (l, r)) = ∏ x ∈ S1, f x := by
      intro f
      rw [Finset.prod_biUnion]
      · refine Finset.prod_congr rfl fun l _ => (Finset.prod_image fun r1 _ r2 _ h => (Prod.mk.inj h).2).symm
      · intro l1 _ l2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨r2, _, h2⟩ := Finset.mem_image.mp hx2
        exact hne (Prod.mk.inj h2).1.symm
    have hL2 : ∀ f : ℕ × ℕ → Trunc2 D1 D2 R,
        (∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset, f (l, r)) = ∏ x ∈ S2, f x := by
      intro f
      rw [Finset.prod_biUnion]
      · refine Finset.prod_congr rfl fun l _ => (Finset.prod_image fun r1 _ r2 _ h => (Prod.mk.inj h).2).symm
      · intro l1 _ l2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨r1, _, rfl⟩ := Finset.mem_image.mp hx1
        obtain ⟨r2, _, h2⟩ := Finset.mem_image.mp hx2
        exact hne (Prod.mk.inj h2).1.symm
    rw [hL1 (fun x => Trunc2.zpowOneSub (u ^ x.2 * v ^ (x.1 - x.2))
          (if x.1 % 2 = 0 ∧ x.2 % 2 = 0 then (arcCountPlus σ p (x.1 / 2) (x.2 / 2) : ℤ) else 0)),
        hL2 (fun x => (Trunc2.zpowOneSub ((u ^ x.2 * v ^ (x.1 - x.2)) ^ 2) 1) ^ arcCountPlus σ p x.1 x.2)]
    let S2small := S2.filter (fun x => 2 * x.1 ≤ 2 * n)
    have hR_filt : (∏ x ∈ S2, (Trunc2.zpowOneSub ((u ^ x.2 * v ^ (x.1 - x.2)) ^ 2) 1) ^ arcCountPlus σ p x.1 x.2) =
        ∏ x ∈ S2small, (Trunc2.zpowOneSub ((u ^ x.2 * v ^ (x.1 - x.2)) ^ 2) 1) ^ arcCountPlus σ p x.1 x.2 := by
      symm
      refine Finset.prod_subset (Finset.filter_subset _ _) fun x hx hnot => ?_
      simp only [S2small, Finset.mem_filter] at hnot
      have hgt : 2 * n < 2 * x.1 := by
        have hle : ¬ (2 * x.1 ≤ 2 * n) := fun h => hnot ⟨hx, h⟩
        omega
      obtain ⟨l, hl, hx'⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx'
      have hl' := Finset.mem_Icc.mp hl
      rw [htrunc l r hl'.1 hl'.2 (List.mem_toFinset.mp hr) hgt]
      simp [Trunc2.zpowOneSub]
    rw [hR_filt]
    let S1img := S2small.image (fun x => (2 * x.1, 2 * x.2))
    have hS1sub : S1img ⊆ S1 := by
      intro y hy
      obtain ⟨⟨l, r⟩, hx, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hx2, hle⟩ := Finset.mem_filter.mp hx
      obtain ⟨l', hl', hx'⟩ := Finset.mem_biUnion.mp hx2
      obtain ⟨r', hr', heq⟩ := Finset.mem_image.mp hx'
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      have hl1 := Finset.mem_Icc.mp hl'
      rw [Finset.mem_biUnion]
      refine ⟨2 * l', Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
      rw [Finset.mem_image]
      exact ⟨2 * r', List.mem_toFinset.mpr (mem_allowedR_of_double hl1.1 (List.mem_toFinset.mp hr')), rfl⟩
    rw [← Finset.prod_subset hS1sub]
    · rw [Finset.prod_image]
      · refine Finset.prod_congr rfl fun x hx => ?_
        have h1 : (2 * x.1) % 2 = 0 ∧ (2 * x.2) % 2 = 0 := ⟨by omega, by omega⟩
        simp only [h1, and_self, ↓reduceIte, Nat.mul_div_right _ (by omega : 0 < 2)]
        have hsq : u ^ (2 * x.2) * v ^ (2 * x.1 - 2 * x.2) = (u ^ x.2 * v ^ (x.1 - x.2)) ^ 2 := by
          have hs : 2 * x.1 - 2 * x.2 = 2 * (x.1 - x.2) := by omega
          rw [hs, mul_pow, ← pow_mul, ← pow_mul, mul_comm 2, mul_comm 2]
        rw [hsq]
        simp [Trunc2.zpowOneSub]
      · intro x1 _ x2 _ heq
        obtain ⟨h1, h2⟩ := Prod.mk.inj heq
        exact Prod.ext (by omega) (by omega)
    · intro y hy hnot
      by_cases hev : y.1 % 2 = 0 ∧ y.2 % 2 = 0
      · by_cases hp2 : y.2 / 2 ∈ primR (y.1 / 2)
        · exfalso; apply hnot
          obtain ⟨l, hl, hy'⟩ := Finset.mem_biUnion.mp hy
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy'
          have hl' := Finset.mem_Icc.mp hl
          rw [Finset.mem_image]
          refine ⟨(l / 2, r / 2), Finset.mem_filter.mpr ⟨?_, by omega⟩, Prod.ext (by omega) (by omega)⟩
          rw [Finset.mem_biUnion]
          refine ⟨l / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [Finset.mem_image]
          exact ⟨r / 2, List.mem_toFinset.mpr hp2, rfl⟩
        · rw [if_pos hev, arcCountPlus_eq_zero_of_not_prim σ p hp2]
          simp [Trunc2.zpowOneSub]
      · rw [if_neg hev, Trunc2.zpowOneSub_zero]
  rw [hA, hB, hC]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hz := hzero l r (Finset.mem_Icc.mp hl).1 (List.mem_toFinset.mp hr)
  have h1p := Trunc2.one_add_eq_zpowOneSub (u ^ r * v ^ (l - r)) hz
  rw [h1p, mul_pow]
  ring

lemma tail_coeff_zero_lt {D2 : ℕ} {R : Type*} [CommRing R] {l : ℕ} (hl : 1 ≤ l) (hD : l < D2)
    {f g : Trunc2 3 D2 R}
    (hf0 : ∀ h : Fin 3, f.coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0)
    (hfl : ∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → f.coeff h d = 0)
    (hg0 : ∀ h : Fin 3, g.coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0)
    (hgl : ∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → g.coeff h d = 0) :
    (∀ h : Fin 3, (f * g).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
    (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (f * g).coeff h d = 0) ∧
    (∀ h : Fin 3, (f * g).coeff h ⟨l, hD⟩ = f.coeff h ⟨l, hD⟩ + g.coeff h ⟨l, hD⟩) := by
  have h0D : 0 < D2 := by omega
  have hzero_d0 : ∀ (h : Fin 3) (d : Fin D2), d.val ≤ l →
      (f * g).coeff h d =
        (if d.val = 0 then (if h.val = 0 then 1 else 0)
         else if d.val < l then 0
         else f.coeff h d + g.coeff h d) := by
    intro h d hdl
    rw [Trunc2.coeff_mul]
    have hinner : ∀ j1 j2 : Fin D2,
        (∑ i1 : Fin 3, ∑ i2 : Fin 3,
          if i1.val + i2.val = h.val ∧ j1.val + j2.val = d.val then f.coeff i1 j1 * g.coeff i2 j2 else 0) =
        if j1.val + j2.val = d.val then
          if j1.val = 0 then g.coeff h j2
          else if j2.val = 0 then f.coeff h j1
          else 0
        else 0 := by
      intro j1 j2
      by_cases hj : j1.val + j2.val = d.val
      · simp only [hj, and_true, ↓reduceIte]
        by_cases hj1 : j1.val = 0
        · rw [if_pos hj1]
          have hj1eq : j1 = ⟨0, h0D⟩ := Fin.ext hj1
          rw [hj1eq]
          rw [Finset.sum_eq_single ⟨0, by omega⟩]
          · rw [Finset.sum_eq_single h]
            · simp [hf0]
            · intro i2 _ hne
              have : i2.val ≠ h.val := fun h' => hne (Fin.ext h')
              simp [this]
            · intro h0; exact absurd (Finset.mem_univ _) h0
          · intro i1 _ hne
            refine Finset.sum_eq_zero fun i2 _ => ?_
            have hi1 : i1.val ≠ 0 := fun h' => hne (Fin.ext h')
            simp [hf0, hi1]
          · intro h0; exact absurd (Finset.mem_univ _) h0
        · rw [if_neg hj1]
          by_cases hj2 : j2.val = 0
          · rw [if_pos hj2]
            have hj2eq : j2 = ⟨0, h0D⟩ := Fin.ext hj2
            rw [hj2eq]
            rw [Finset.sum_eq_single h]
            · rw [Finset.sum_eq_single ⟨0, by omega⟩]
              · simp [hg0]
              · intro i2 _ hne
                have hi2 : i2.val ≠ 0 := fun h' => hne (Fin.ext h')
                simp [hg0, hi2]
              · intro h0; exact absurd (Finset.mem_univ _) h0
            · intro i1 _ hne
              refine Finset.sum_eq_zero fun i2 _ => ?_
              split_ifs with hi
              · have hi2 : i2.val ≠ 0 := fun h' => hne (Fin.ext (by omega))
                simp [hg0, hi2]
              · rfl
            · intro h0; exact absurd (Finset.mem_univ _) h0
          · rw [if_neg hj2]
            refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ => ?_
            split_ifs
            · rw [hfl i1 j1 (by omega) (by omega), zero_mul]
            · rfl
      · simp [hj]
    have hswap :
        (∑ i1 : Fin 3, ∑ i2 : Fin 3, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
          if i1.val + i2.val = h.val ∧ j1.val + j2.val = d.val then f.coeff i1 j1 * g.coeff i2 j2 else 0) =
        ∑ j1 : Fin D2, ∑ j2 : Fin D2, ∑ i1 : Fin 3, ∑ i2 : Fin 3,
          if i1.val + i2.val = h.val ∧ j1.val + j2.val = d.val then f.coeff i1 j1 * g.coeff i2 j2 else 0 := by
      let e : (Fin 3 × Fin 3 × Fin D2 × Fin D2) ≃ (Fin D2 × Fin D2 × Fin 3 × Fin 3) :=
        { toFun := fun ⟨i1, i2, j1, j2⟩ => (j1, j2, i1, i2)
          invFun := fun ⟨j1, j2, i1, i2⟩ => (i1, i2, j1, j2)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have heq := Fintype.sum_equiv e
        (fun x => if x.1.val + x.2.1.val = h.val ∧ x.2.2.1.val + x.2.2.2.val = d.val then
          f.coeff x.1 x.2.2.1 * g.coeff x.2.1 x.2.2.2 else 0)
        (fun y => if y.2.2.1.val + y.2.2.2.val = h.val ∧ y.1.val + y.2.1.val = d.val then
          f.coeff y.2.2.1 y.1 * g.coeff y.2.2.2 y.2.1 else 0)
        (fun _ => rfl)
      simpa only [Fintype.sum_prod_type] using heq
    rw [hswap]
    simp_rw [hinner]
    by_cases hd0 : d.val = 0
    · rw [if_pos hd0]
      rw [Finset.sum_eq_single ⟨0, h0D⟩]
      · rw [Finset.sum_eq_single ⟨0, h0D⟩]
        · simp [hd0, hg0]
        · intro j2 _ hne
          have : j2.val ≠ 0 := fun h' => hne (Fin.ext h')
          simp [hd0, this]
        · intro h0; exact absurd (Finset.mem_univ _) h0
      · intro j1 _ hne
        refine Finset.sum_eq_zero fun j2 _ => ?_
        have : j1.val + j2.val ≠ d.val := by have : j1.val ≠ 0 := fun h' => hne (Fin.ext h'); omega
        simp [this]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · rw [if_neg hd0]
      have hsum2 : (∑ j1 : Fin D2, ∑ j2 : Fin D2,
          if j1.val + j2.val = d.val then
            if j1.val = 0 then g.coeff h j2 else if j2.val = 0 then f.coeff h j1 else 0
          else 0) = g.coeff h d + f.coeff h d := by
        have hne0d : (⟨0, h0D⟩ : Fin D2) ≠ d := fun h' => hd0 (congrArg Fin.val h').symm
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ⟨0, h0D⟩)]
        have hdmem : d ∈ (Finset.univ : Finset (Fin D2)).erase ⟨0, h0D⟩ :=
          Finset.mem_erase.mpr ⟨hne0d.symm, Finset.mem_univ d⟩
        rw [← Finset.add_sum_erase _ _ hdmem]
        have hrest : (∑ j1 ∈ ((Finset.univ : Finset (Fin D2)).erase ⟨0, h0D⟩).erase d,
            ∑ j2 : Fin D2,
              if j1.val + j2.val = d.val then
                if j1.val = 0 then g.coeff h j2 else if j2.val = 0 then f.coeff h j1 else 0
              else 0) = 0 := by
          refine Finset.sum_eq_zero fun j1 hj1 => Finset.sum_eq_zero fun j2 _ => ?_
          rw [Finset.mem_erase, Finset.mem_erase] at hj1
          have h1 : j1.val ≠ d.val := fun h' => hj1.1 (Fin.ext h')
          have h2 : j1.val ≠ 0 := fun h' => hj1.2.1 (Fin.ext h')
          by_cases hs : j1.val + j2.val = d.val
          · by_cases hj2 : j2.val = 0
            · exfalso; apply h1; omega
            · simp [hs, h2, hj2]
          · simp [hs]
        rw [hrest, add_zero]
        congr 1
        · rw [Finset.sum_eq_single d]
          · simp
          · intro j2 _ hne
            have : j2.val ≠ d.val := fun h' => hne (Fin.ext h')
            simp [this]
          · intro h0; exact absurd (Finset.mem_univ _) h0
        · rw [Finset.sum_eq_single ⟨0, h0D⟩]
          · simp [hd0]
          · intro j2 _ hne
            have hneq : d.val + j2.val ≠ d.val := by have : j2.val ≠ 0 := fun h' => hne (Fin.ext h'); omega
            rw [if_neg hneq]
          · intro h0; exact absurd (Finset.mem_univ _) h0
      rw [hsum2, add_comm]
      split_ifs with hlt
      · rw [hfl h d (by omega) hlt, hgl h d (by omega) hlt, add_zero]
      · rfl
  refine ⟨fun h => ?_, fun h d h1 h2 => ?_, fun h => ?_⟩
  · have := hzero_d0 h ⟨0, h0D⟩ (Nat.zero_le l)
    simpa using this
  · have := hzero_d0 h d (by omega)
    have hne : d.val ≠ 0 := by omega
    simpa [hne, h2] using this
  · have := hzero_d0 h ⟨l, hD⟩ (le_refl l)
    have hne : l ≠ 0 := by omega
    have hnlt : ¬ (l < l) := lt_irrefl l
    simpa [hne, hnlt] using this

lemma tail_coeff_pow_ge {D2 : ℕ} {R : Type*} [CommRing R] {l : ℕ} (hl : 1 ≤ l) (hD : l < D2)
    {f : Trunc2 3 D2 R}
    (hf0 : ∀ h : Fin 3, f.coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0)
    (hfl : ∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → f.coeff h d = 0)
    (k : ℕ) :
    (∀ h : Fin 3, (f ^ k).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
    (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (f ^ k).coeff h d = 0) ∧
    (∀ h : Fin 3, (f ^ k).coeff h ⟨l, hD⟩ = (k : R) * f.coeff h ⟨l, hD⟩) := by
  induction k with
  | zero =>
    refine ⟨fun h => by simp [Trunc2.coeff_one], fun h d h1 _ => by simp [Trunc2.coeff_one, Nat.ne_of_gt h1],
      fun h => by simp [Trunc2.coeff_one, show l ≠ 0 by omega]⟩
  | succ k ih =>
    rw [pow_succ]
    obtain ⟨h1, h2, h3⟩ := tail_coeff_zero_lt hl hD ih.1 ih.2.1 hf0 hfl
    refine ⟨h1, h2, fun h => ?_⟩
    rw [h3 h, ih.2.2 h, Nat.cast_succ, add_mul, one_mul]

lemma tail_coeff_finset_prod {ι : Type*} {D2 : ℕ} {R : Type*} [CommRing R] {l : ℕ}
    (hl : 1 ≤ l) (hD : l < D2) (s : Finset ι) (F : ι → Trunc2 3 D2 R)
    (hF0 : ∀ a ∈ s, ∀ h : Fin 3, (F a).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0)
    (hFl : ∀ a ∈ s, ∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (F a).coeff h d = 0) :
    (∀ h : Fin 3, (∏ a ∈ s, F a).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
    (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (∏ a ∈ s, F a).coeff h d = 0) ∧
    (∀ h : Fin 3, (∏ a ∈ s, F a).coeff h ⟨l, hD⟩ = ∑ a ∈ s, (F a).coeff h ⟨l, hD⟩) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun h => by simp [Trunc2.coeff_one], fun h d h1 _ => by simp [Trunc2.coeff_one, Nat.ne_of_gt h1],
      fun h => by simp [Trunc2.coeff_one, show l ≠ 0 by omega]⟩
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ih' := ih (fun x hx => hF0 x (Finset.mem_insert_of_mem hx))
      (fun x hx => hFl x (Finset.mem_insert_of_mem hx))
    obtain ⟨h1, h2, h3⟩ := tail_coeff_zero_lt hl hD (hF0 a (Finset.mem_insert_self a s))
      (hFl a (Finset.mem_insert_self a s)) ih'.1 ih'.2.1
    refine ⟨h1, h2, fun h => ?_⟩
    rw [h3 h, ih'.2.2 h, Finset.sum_insert ha]

lemma tail_coeff_zpowOneSub_zt {D2 : ℕ} {R : Type*} [CommRing R] {l l' r : ℕ}
    (hl : 1 ≤ l) (hll' : l ≤ l') (hD : l < D2) (c : ℤ) :
    let f : Trunc2 3 D2 R := Trunc2.X2 ^ l' * (1 + Trunc2.X1) ^ r
    let g := Trunc2.zpowOneSub f c
    (∀ h : Fin 3, g.coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
    (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → g.coeff h d = 0) ∧
    (∀ h : Fin 3, g.coeff h ⟨l, hD⟩ = if l' = l then -(c : R) * (Nat.choose r h.val : R) else 0) := by
  intro f g
  have hf_coeff : ∀ (h : Fin 3) (d : Fin D2), f.coeff h d = if d.val = l' then (Nat.choose r h.val : R) else 0 :=
    trunc2_X2_mul_1_add_X1_coeff l' r
  have hf_pow_lt : ∀ k : ℕ, 1 ≤ k → ∀ (h : Fin 3) (d : Fin D2), d.val < k * l' → (f ^ k).coeff h d = 0 := by
    intro k
    induction k with
    | zero => intro h0; omega
    | succ k ih =>
      intro _ h d hd
      cases k with
      | zero =>
        rw [pow_one, hf_coeff]
        have : d.val ≠ l' := by omega
        simp [this]
      | succ k' =>
        rw [pow_succ, Trunc2.coeff_mul]
        refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ =>
          Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
        split_ifs with hc
        · by_cases hj2 : j2.val = l'
          · rw [ih (by omega) i1 j1 (by nlinarith), zero_mul]
          · rw [hf_coeff i2 j2, if_neg hj2, mul_zero]
        · rfl
  have h1sub :
      (∀ h : Fin 3, (1 - f).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
      (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (1 - f).coeff h d = 0) ∧
      (∀ h : Fin 3, (1 - f).coeff h ⟨l, hD⟩ = if l' = l then -(Nat.choose r h.val : R) else 0) := by
    refine ⟨fun h => ?_, fun h d h1 h2 => ?_, fun h => ?_⟩
    · rw [Trunc2.coeff_sub, Trunc2.coeff_one, hf_coeff]
      have : (0 : ℕ) ≠ l' := by omega
      simp [this]
    · rw [Trunc2.coeff_sub, Trunc2.coeff_one, hf_coeff]
      have h1' : d.val ≠ 0 := by omega
      have h2' : d.val ≠ l' := by omega
      simp [h1', h2']
    · rw [Trunc2.coeff_sub, Trunc2.coeff_one, hf_coeff]
      have h0 : l ≠ 0 := by omega
      by_cases he : l' = l
      · subst he; simp [h0]
      · have hne : l ≠ l' := fun h' => he h'.symm
        simp [h0, he, hne]
  have hinv :
      (∀ h : Fin 3, (Trunc2.invOneSub f).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
      (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (Trunc2.invOneSub f).coeff h d = 0) ∧
      (∀ h : Fin 3, (Trunc2.invOneSub f).coeff h ⟨l, hD⟩ = if l' = l then (Nat.choose r h.val : R) else 0) := by
    unfold Trunc2.invOneSub
    refine ⟨fun h => ?_, fun h d h1 h2 => ?_, fun h => ?_⟩
    · rw [Trunc2.coeff_sum, Finset.sum_eq_single 0]
      · simp [Trunc2.coeff_one]
      · intro k _ hne; exact hf_pow_lt k (by omega) h ⟨0, by omega⟩ (Nat.mul_pos (by omega) (by omega))
      · intro h0; exfalso; apply h0; exact Finset.mem_range.mpr (by omega)
    · rw [Trunc2.coeff_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      cases k with
      | zero => simp [Trunc2.coeff_one, Nat.ne_of_gt h1]
      | succ k' => exact hf_pow_lt (k' + 1) (by omega) h d (by nlinarith)
    · rw [Trunc2.coeff_sum]
      have h1in : 1 ∈ Finset.range (3 + D2) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single 1]
      · rw [pow_one, hf_coeff]
        by_cases he : l' = l
        · subst he; simp
        · have hne : l ≠ l' := fun h' => he h'.symm
          simp [he, hne]
      · intro k _ hne
        cases k with
        | zero => simp [Trunc2.coeff_one, show l ≠ 0 by omega]
        | succ k' =>
          have hk2 : 2 ≤ k' + 1 := by omega
          exact hf_pow_lt (k' + 1) (by omega) h ⟨l, hD⟩ (by nlinarith)
      · intro h0; exact absurd h1in h0
  dsimp only [g, Trunc2.zpowOneSub]
  by_cases hc : 0 ≤ c
  · rw [if_pos hc]
    obtain ⟨a1, a2, a3⟩ := tail_coeff_pow_ge hl hD h1sub.1 h1sub.2.1 c.toNat
    refine ⟨a1, a2, fun h => ?_⟩
    rw [a3 h, h1sub.2.2 h]
    have hcn : (c.toNat : R) = (c : R) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hc]
    rw [hcn]
    split_ifs <;> ring
  · rw [if_neg hc]
    obtain ⟨a1, a2, a3⟩ := tail_coeff_pow_ge hl hD hinv.1 hinv.2.1 (-c).toNat
    refine ⟨a1, a2, fun h => ?_⟩
    rw [a3 h, hinv.2.2 h]
    have hcn : ((-c).toNat : R) = -(c : R) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
    rw [hcn]
    split_ifs <;> ring

lemma tail_coeff_ratio_zt {D2 : ℕ} {R : Type*} [CommRing R] {l l' r : ℕ}
    (hl : 1 ≤ l) (hll' : l ≤ l') (hD : l < D2) (k : ℕ) :
    let f : Trunc2 3 D2 R := Trunc2.X2 ^ l' * (1 + Trunc2.X1) ^ r
    let g := ((1 - f) * Trunc2.invOneAdd f) ^ k
    (∀ h : Fin 3, g.coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
    (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → g.coeff h d = 0) ∧
    (∀ h : Fin 3, g.coeff h ⟨l, hD⟩ = if l' = l then -(2 * (k : R) * (Nat.choose r h.val : R)) else 0) := by
  intro f g
  have h1sub := tail_coeff_zpowOneSub_zt (D2 := D2) (R := R) (r := r) hl hll' hD 1
  simp only [Trunc2.zpowOneSub_one, Int.cast_one, neg_one_mul] at h1sub
  have hf_coeff : ∀ (h : Fin 3) (d : Fin D2), f.coeff h d = if d.val = l' then (Nat.choose r h.val : R) else 0 :=
    trunc2_X2_mul_1_add_X1_coeff l' r
  have hf_pow_lt : ∀ m : ℕ, 1 ≤ m → ∀ (h : Fin 3) (d : Fin D2), d.val < m * l' → ((-f) ^ m).coeff h d = 0 := by
    intro m hm h d hd
    rw [neg_pow]
    have hneg : ∀ (a : Trunc2 3 D2 R) (j : ℕ), ((-1 : Trunc2 3 D2 R) ^ j * a).coeff h d = (-1 : R) ^ j * a.coeff h d := by
      intro a j
      have : (-1 : Trunc2 3 D2 R) ^ j = (((-1 : ℤ) ^ j : ℤ) : Trunc2 3 D2 R) := by simp
      rw [this, Trunc2.intCast_mul_coeff]; simp
    rw [hneg]
    have hfm : (f ^ m).coeff h d = 0 := by
      clear hneg
      induction m generalizing h d with
      | zero => omega
      | succ m ih =>
        cases m with
        | zero =>
          rw [pow_one, hf_coeff]
          have : d.val ≠ l' := by omega
          simp [this]
        | succ m' =>
          rw [pow_succ, Trunc2.coeff_mul]
          refine Finset.sum_eq_zero fun i1 _ => Finset.sum_eq_zero fun i2 _ =>
            Finset.sum_eq_zero fun j1 _ => Finset.sum_eq_zero fun j2 _ => ?_
          split_ifs with hc
          · by_cases hj2 : j2.val = l'
            · rw [ih (by omega) i1 j1 (by nlinarith), zero_mul]
            · rw [hf_coeff i2 j2, if_neg hj2, mul_zero]
          · rfl
    rw [hfm, mul_zero]
  have hinvA :
      (∀ h : Fin 3, (Trunc2.invOneAdd f).coeff h ⟨0, by omega⟩ = if h.val = 0 then 1 else 0) ∧
      (∀ (h : Fin 3) (d : Fin D2), 0 < d.val → d.val < l → (Trunc2.invOneAdd f).coeff h d = 0) ∧
      (∀ h : Fin 3, (Trunc2.invOneAdd f).coeff h ⟨l, hD⟩ = if l' = l then -(Nat.choose r h.val : R) else 0) := by
    unfold Trunc2.invOneAdd
    refine ⟨fun h => ?_, fun h d h1 h2 => ?_, fun h => ?_⟩
    · rw [Trunc2.coeff_sum, Finset.sum_eq_single 0]
      · simp [Trunc2.coeff_one]
      · intro m _ hne; exact hf_pow_lt m (by omega) h ⟨0, by omega⟩ (Nat.mul_pos (by omega) (by omega))
      · intro h0; exfalso; apply h0; exact Finset.mem_range.mpr (by omega)
    · rw [Trunc2.coeff_sum]
      refine Finset.sum_eq_zero fun m _ => ?_
      cases m with
      | zero => simp [Trunc2.coeff_one, Nat.ne_of_gt h1]
      | succ m' => exact hf_pow_lt (m' + 1) (by omega) h d (by nlinarith)
    · rw [Trunc2.coeff_sum]
      have h1in : 1 ∈ Finset.range (3 + D2) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single 1]
      · rw [pow_one, Trunc2.coeff_neg, hf_coeff]
        by_cases he : l' = l
        · subst he; simp
        · have hne : l ≠ l' := fun h' => he h'.symm
          simp [he, hne]
      · intro m _ hne
        cases m with
        | zero => simp [Trunc2.coeff_one, show l ≠ 0 by omega]
        | succ m' =>
          have hm2 : 2 ≤ m' + 1 := by omega
          exact hf_pow_lt (m' + 1) (by omega) h ⟨l, hD⟩ (by nlinarith)
      · intro h0; exact absurd h1in h0
  obtain ⟨r1, r2, r3⟩ := tail_coeff_zero_lt hl hD h1sub.1 h1sub.2.1 hinvA.1 hinvA.2.1
  obtain ⟨p1, p2, p3⟩ := tail_coeff_pow_ge hl hD r1 r2 k
  refine ⟨p1, p2, fun h => ?_⟩
  rw [p3 h, r3 h, h1sub.2.2 h, hinvA.2.2 h]
  split_ifs <;> ring

lemma solve_false_odd {R : Type*} [CommRing R] (m c0 c1 : R) :
    let d0 := c0 + c1
    let d1 := (m : R) * c0 + (m + 1) * c1
    d1 - m * d0 = c1 ∧ d0 - (d1 - m * d0) = c0 := by
  intro d0 d1; constructor <;> ring

lemma solve_false_2mod4 {R : Type*} [CommRing R] (m : ℕ) (hm : 1 ≤ m) (cm1 c0 cp1 : R) :
    let d0 := cm1 + c0 + cp1
    let d1 := ((m - 1 : ℕ) : R) * cm1 + (m : R) * c0 + ((m + 1 : ℕ) : R) * cp1
    let d2 := (Nat.choose (m - 1) 2 : R) * cm1 + (Nat.choose m 2 : R) * c0 + (Nat.choose (m + 1) 2 : R) * cp1
    let diff := d1 - (m : R) * d0
    let cm1' := d2 - (Nat.choose m 2 : R) * d0 - (m : R) * diff
    let cp1' := cm1' + diff
    let c0' := d0 - cm1' - cp1'
    cm1' = cm1 ∧ c0' = c0 ∧ cp1' = cp1 := by
  intro d0 d1 d2 diff cm1' cp1' c0'
  have hm1 : ((m - 1 : ℕ) : R) = (m : R) - 1 := by
    cases m with
    | zero => omega
    | succ m' => simp
  have hch_sub : (Nat.choose (m - 1) 2 : R) = (Nat.choose m 2 : R) - ((m : R) - 1) := by
    cases m with
    | zero => omega
    | succ m' =>
      have h : Nat.choose (m' + 1) 2 = Nat.choose m' 2 + m' := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
      have h' : (Nat.choose (m' + 1) 2 : R) = (Nat.choose m' 2 : R) + (m' : R) := by rw [h, Nat.cast_add]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      rw [h']; ring
  have hch_add : (Nat.choose (m + 1) 2 : R) = (Nat.choose m 2 : R) + (m : R) := by
    have h : Nat.choose (m + 1) 2 = Nat.choose m 2 + m := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]
    rw [h, Nat.cast_add]
  have hdiff : diff = cp1 - cm1 := by
    dsimp only [diff, d1, d0]
    rw [hm1]; push_cast; ring
  have hcm1 : cm1' = cm1 := by
    dsimp only [cm1', d2, d0]
    rw [hdiff, hch_sub, hch_add]; ring
  have hcp1 : cp1' = cp1 := by
    dsimp only [cp1']; rw [hcm1, hdiff]; ring
  have hc0 : c0' = c0 := by
    dsimp only [c0', d0]; rw [hcm1, hcp1]; ring
  exact ⟨hcm1, hc0, hcp1⟩

lemma decode_signed_zmod {B : ℕ} (hB : 2 ≤ B) (c : ℤ) (hc : -(2 ^ (B - 1) : ℤ) < c ∧ c < 2 ^ (B - 1)) :
    let z : ZMod (2 ^ B) := (c : ZMod (2 ^ B))
    z.val.testBit (B - 1) = decide (c < 0) ∧
    (if c < 0 then (-z).val else z.val) = c.natAbs ∧
    c.natAbs < 2 ^ (B - 1) := by
  have hposB : 0 < 2 ^ B := by positivity
  haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
  have h2pow : 2 ^ B = 2 ^ (B - 1) + 2 ^ (B - 1) := by
    have : B = (B - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ, mul_two]
  intro z
  have habs_int : (c.natAbs : ℤ) < (2 ^ (B - 1) : ℤ) := by omega
  have habs : c.natAbs < 2 ^ (B - 1) := by exact_mod_cast habs_int
  by_cases hneg : c < 0
  · have hzval : z.val = 2 ^ B - c.natAbs := by
      have hc_eq : c = -((c.natAbs : ℕ) : ℤ) := by omega
      have hcast : ((2 ^ B - c.natAbs : ℕ) : ZMod (2 ^ B)) = z := by
        have hle : c.natAbs ≤ 2 ^ B := by omega
        rw [Nat.cast_sub hle]
        conv_rhs => dsimp only [z]; rw [hc_eq, Int.cast_neg, Int.cast_natCast]
        simp
      rw [← hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hbit : z.val.testBit (B - 1) = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : z.val / 2 ^ (B - 1) = 1 := by
        rw [hzval]
        have h1 : 2 ^ (B - 1) ≤ 2 ^ B - c.natAbs := by omega
        have h2 : 2 ^ B - c.natAbs < 2 * 2 ^ (B - 1) := by omega
        exact Nat.div_eq_of_lt_le (by simpa using h1) h2
      simp [hdiv]
    have hnegval : (-z).val = c.natAbs := by
      have hc_eq : -c = (c.natAbs : ℤ) := by omega
      have : -z = ((c.natAbs : ℕ) : ZMod (2 ^ B)) := by
        conv_lhs => dsimp only [z]; rw [← Int.cast_neg, hc_eq, Int.cast_natCast]
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by simp [hbit, hneg], by simp [hneg, hnegval], habs⟩
  · have hzval : z.val = c.natAbs := by
      have hc_eq : c = (c.natAbs : ℤ) := by omega
      have : z = ((c.natAbs : ℕ) : ZMod (2 ^ B)) := by
        conv_lhs => dsimp only [z]; rw [hc_eq, Int.cast_natCast]
      rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hbit : z.val.testBit (B - 1) = false := by
      rw [hzval, Nat.testBit_eq_false_of_lt habs]
    exact ⟨by simp [hbit, hneg], by simp [hneg, hzval], habs⟩

section GraphClosure

def edgeEquiv (n : ℕ) : Fin (2 * n) ≃ Bool × Fin n where
  toFun e := if h : e.val < n then (false, ⟨e.val, h⟩) else (true, ⟨e.val - n, by omega⟩)
  invFun e := if e.1 then ⟨n + e.2.val, by have := e.2.isLt; omega⟩ else ⟨e.2.val, by have := e.2.isLt; omega⟩
  left_inv e := by
    by_cases h : e.val < n
    · simp [h]
    · simp only [h, ↓reduceDIte, ↓reduceIte]
      exact Fin.ext (by dsimp only; omega)
  right_inv e := by
    rcases e with ⟨b, i⟩
    cases b
    · simp [i.isLt]
    · have h1 : ¬ (n + i.val < n) := by omega
      simp [h1]

def adjMat {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e1 e2 : Bool × Fin n) : Bool :=
  decide (e1 = e2 ∨ (qE σ p e1 = none ∧ e2 = nextE σ e1) ∨ (qE σ p e2 = none ∧ e1 = nextE σ e2))

def IsAdjChain {α : Type*} (R : α → α → Prop) (L : List α) : Prop :=
  ∀ k (hk : k + 1 < L.length), R L[k] L[k + 1]

def matMulBool {α : Type*} [Fintype α] (A B : α → α → Bool) (u v : α) : Bool :=
  decide (∃ w : α, A u w = true ∧ B w v = true)

def matPowBool {α : Type*} [Fintype α] (A : α → α → Bool) : ℕ → α → α → Bool
  | 0, u, v => A u v
  | k + 1, u, v => matMulBool (matPowBool A k) A u v

lemma matPowBool_sound {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    ∀ k e1 e2, matPowBool (adjMat σ p) k e1 e2 = true → Relation.EqvGen (ArcStep σ p) e1 e2 := by
  intro k
  induction k with
  | zero =>
    intro e1 e2 h
    simp only [matPowBool, adjMat, decide_eq_true_eq] at h
    rcases h with rfl | h | h
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h)
  | succ k ih =>
    intro e1 e2 h
    simp only [matPowBool, matMulBool, decide_eq_true_eq] at h
    obtain ⟨w, h1, h2⟩ := h
    refine Relation.EqvGen.trans _ w _ (ih e1 w h1) ?_
    simp only [adjMat, decide_eq_true_eq] at h2
    rcases h2 with rfl | h2 | h2
    · exact Relation.EqvGen.refl _
    · exact Relation.EqvGen.rel _ _ h2
    · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h2)

lemma matPowBool_mono {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (k : ℕ) (e1 e2 : Bool × Fin n) (h : matPowBool (adjMat σ p) k e1 e2 = true) :
    matPowBool (adjMat σ p) (k + 1) e1 e2 = true := by
  simp only [matPowBool, matMulBool, decide_eq_true_eq]
  exact ⟨e2, h, by simp [adjMat]⟩

lemma matPowBool_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    {k1 k2 : ℕ} (hk : k1 ≤ k2) (e1 e2 : Bool × Fin n)
    (h : matPowBool (adjMat σ p) k1 e1 e2 = true) :
    matPowBool (adjMat σ p) k2 e1 e2 = true := by
  induction hk with
  | refl => exact h
  | step _ ih => exact matPowBool_mono σ p _ e1 e2 ih

lemma matPowBool_complete_list {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (L : List (Bool × Fin n)) (hne : L ≠ [])
    (hchain : IsAdjChain (fun a b => adjMat σ p a b = true) L) :
    matPowBool (adjMat σ p) (L.length - 1) (L.head hne) (L.getLast hne) = true := by
  induction L with
  | nil => exact absurd rfl hne
  | cons a rest ih =>
    cases rest with
    | nil => simp [matPowBool, adjMat]
    | cons b rest' =>
      have hne' : b :: rest' ≠ [] := List.cons_ne_nil _ _
      have hab : adjMat σ p a b = true := hchain 0 (by simp)
      have hch' : IsAdjChain (fun x y => adjMat σ p x y = true) (b :: rest') :=
        fun k hk => hchain (k + 1) (by simpa using hk)
      have hih := ih hne' hch'
      simp only [List.head_cons, List.getLast_cons hne', List.length_cons, Nat.add_sub_cancel] at hih ⊢
      have hstep : ∀ k x y z, adjMat σ p x y = true → matPowBool (adjMat σ p) k y z = true →
          matPowBool (adjMat σ p) (k + 1) x z = true := by
        intro k
        induction k with
        | zero =>
          intro x y z h1 h2
          change matMulBool (adjMat σ p) (adjMat σ p) x z = true
          unfold matMulBool; rw [decide_eq_true_eq]
          exact ⟨y, h1, h2⟩
        | succ k ihk =>
          intro x y z h1 h2
          change matMulBool (matPowBool (adjMat σ p) k) (adjMat σ p) y z = true at h2
          unfold matMulBool at h2; rw [decide_eq_true_eq] at h2
          obtain ⟨w, hw1, hw2⟩ := h2
          change matMulBool (matPowBool (adjMat σ p) (k + 1)) (adjMat σ p) x z = true
          unfold matMulBool; rw [decide_eq_true_eq]
          exact ⟨w, ihk x y w h1 hw1, hw2⟩
      exact hstep _ a b _ hab hih

lemma exists_short_chain {α : Type*} [Fintype α] [DecidableEq α] (R : α → α → Prop)
    {a b : α} (L : List α) (hne : L ≠ []) (hhead : L.head hne = a) (hlast : L.getLast hne = b)
    (hchain : IsAdjChain R L) :
    ∃ L' : List α, ∃ hne' : L' ≠ [], L'.head hne' = a ∧ L'.getLast hne' = b ∧
      IsAdjChain R L' ∧ L'.length ≤ Fintype.card α := by
  induction hlen : L.length using Nat.strong_induction_on generalizing L with
  | _ m ih =>
    by_cases hnodup : L.Nodup
    · refine ⟨L, hne, hhead, hlast, hchain, ?_⟩
      have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnodup
      rw [← h1]
      exact Finset.card_le_univ _
    · rw [List.nodup_iff_injective_get] at hnodup
      have hex : ∃ i j : Fin L.length, i.val < j.val ∧ L.get i = L.get j := by
        by_contra hno
        apply hnodup
        intro i j hij
        by_contra hne_ij
        rcases lt_or_gt_of_ne (fun h => hne_ij (Fin.ext h)) with hlt | hgt
        · exact hno ⟨i, j, hlt, hij⟩
        · exact hno ⟨j, i, hgt, hij.symm⟩
      obtain ⟨i, j, hij, hget⟩ := hex
      let L2 := L.take i.val ++ L.drop j.val
      have hL2_ne : L2 ≠ [] := by
        intro h0
        have : (L.drop j.val).length = 0 := by
          have := congrArg List.length h0
          simp [L2] at this; omega
        simp at this; have := j.isLt; omega
      have hL2_len : L2.length < m := by
        simp [L2, hlen]; have := j.isLt; omega
      have hL2_head : L2.head hL2_ne = a := by
        cases hi : i.val with
        | zero =>
          have htake : L.take 0 = [] := rfl
          have hd_ne : L.drop j.val ≠ [] := by
            intro h0; have := congrArg List.length h0; simp at this; have := j.isLt; omega
          have hhead_drop : (L.drop j.val).head hd_ne = L.get j := by
            simp [List.head_drop]
          have hhead0 : L.head hne = L.get i := by
            cases L with
            | nil => exact absurd rfl hne
            | cons x xs => simp [hi]
          simp only [L2, hi, htake, List.nil_append]
          rw [hhead_drop, ← hget, ← hhead0, hhead]
        | succ k =>
          have htake_ne : L.take (k + 1) ≠ [] := by
            intro h0
            have hlt : (L.take (k + 1)).length = 0 := congrArg List.length h0
            rw [List.length_take] at hlt
            have := i.isLt; omega
          have h1 : (L.take i.val ++ L.drop j.val).head hL2_ne =
              (L.take i.val).head (by rw [hi]; exact htake_ne) :=
            List.head_append_of_ne_nil (by rw [hi]; exact htake_ne)
          have h2 : (L.take i.val).head (by rw [hi]; exact htake_ne) = L.head hne := by
            cases L with
            | nil => exact absurd rfl hne
            | cons x xs => simp [hi]
          exact h1.trans (h2.trans hhead)
      have hL2_last : L2.getLast hL2_ne = b := by
        have hd_ne : L.drop j.val ≠ [] := by
          intro h0; have := congrArg List.length h0; simp at this; have := j.isLt; omega
        have h1 : L2.getLast hL2_ne = (L.drop j.val).getLast hd_ne :=
          List.getLast_append_of_ne_nil _ hd_ne
        have h2 : (L.drop j.val).getLast hd_ne = L.getLast hne := by
          have := List.getLast_drop hd_ne
          simpa using this
        rw [h1, h2, hlast]
      have hL2_chain : IsAdjChain R L2 := by
        intro k hk
        have hk_len : k + 1 < (L.take i.val).length + (L.drop j.val).length := by simpa [L2] using hk
        have htake_len : (L.take i.val).length = i.val := List.length_take_of_le (le_of_lt i.isLt)
        by_cases h1 : k + 1 < i.val
        · have hk1 : k < (L.take i.val).length := by omega
          have hk2 : k + 1 < (L.take i.val).length := by omega
          simp only [L2, List.getElem_append_left hk1, List.getElem_append_left hk2, List.getElem_take]
          exact hchain k (by have := i.isLt; omega)
        · by_cases h2 : k < i.val
          · have hkeq : k + 1 = i.val := by omega
            have hk1 : k < (L.take i.val).length := by omega
            have hk2 : ¬ (k + 1 < (L.take i.val).length) := by omega
            have hl1 : L2[k] = L[k] := by
              simp only [L2, List.getElem_append_left hk1, List.getElem_take]
            have hl2 : L2[k + 1] = L[j.val] := by
              simp only [L2, List.getElem_append_right (Nat.le_of_not_lt hk2), htake_len, List.getElem_drop]
              congr 1; omega
            rw [hl1, hl2]
            have hget_eq : L[j.val] = L[i.val] := by simpa using hget.symm
            rw [hget_eq]
            have hl3 : L[i.val] = L[k + 1] := by congr 1; exact hkeq.symm
            rw [hl3]
            exact hchain k (by have := i.isLt; omega)
          · have hk1 : ¬ (k < (L.take i.val).length) := by omega
            have hk2 : ¬ (k + 1 < (L.take i.val).length) := by omega
            simp only [L2, List.getElem_append_right (Nat.le_of_not_lt hk1),
              List.getElem_append_right (Nat.le_of_not_lt hk2), htake_len, List.getElem_drop]
            have hlt1 : j.val + (k + 1 - i.val) < L.length := by simp [htake_len] at hk_len; omega
            have hlt2 : (j.val + (k - i.val)) + 1 < L.length := by omega
            have hidx : L[j.val + (k + 1 - i.val)]'hlt1 = L[(j.val + (k - i.val)) + 1]'hlt2 := by
              congr 1; omega
            rw [hidx]
            exact hchain (j.val + (k - i.val)) hlt2
      exact ih L2.length hL2_len L2 hL2_ne hL2_head hL2_last hL2_chain rfl

lemma eqvGen_iff_matPowBool {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (e1 e2 : Bool × Fin n) :
    matPowBool (adjMat σ p) (2 * n) e1 e2 = true ↔ Relation.EqvGen (ArcStep σ p) e1 e2 := by
  constructor
  · exact matPowBool_sound σ p (2 * n) e1 e2
  · intro heqv
    have hchain : ∃ L : List (Bool × Fin n), ∃ hne : L ≠ [],
        L.head hne = e1 ∧ L.getLast hne = e2 ∧ IsAdjChain (fun a b => adjMat σ p a b = true) L := by
      induction heqv with
      | refl a =>
        exact ⟨[a], List.cons_ne_nil _ _, rfl, rfl, fun k hk => by simp at hk⟩
      | rel a b hab =>
        refine ⟨[a, b], List.cons_ne_nil _ _, rfl, rfl, fun k hk => ?_⟩
        simp only [List.length_cons, List.length_nil] at hk
        have hk0 : k = 0 := by omega
        subst hk0
        simp [adjMat, hab.1, hab.2]
      | symm a b _ ih =>
        obtain ⟨L, hne, hh, hl, hch⟩ := ih
        have hrev_ne : L.reverse ≠ [] := by simpa using hne
        refine ⟨L.reverse, hrev_ne, ?_, ?_, ?_⟩
        · rw [List.head_reverse]; exact hl
        · rw [List.getLast_reverse]; exact hh
        · intro k hk
          rw [List.length_reverse] at hk
          rw [List.getElem_reverse, List.getElem_reverse]
          have hstep := hch (L.length - 2 - k) (by omega)
          have hi1 : L.length - 1 - k = (L.length - 2 - k) + 1 := by omega
          have hi2 : L.length - 1 - (k + 1) = L.length - 2 - k := by omega
          simp only [hi1, hi2]
          simp only [adjMat, decide_eq_true_eq] at hstep ⊢
          rcases hstep with heq | h | h
          · exact Or.inl heq.symm
          · exact Or.inr (Or.inr h)
          · exact Or.inr (Or.inl h)
      | trans a b c _ _ ih1 ih2 =>
        obtain ⟨L1, hne1, hh1, hl1, hch1⟩ := ih1
        obtain ⟨L2, hne2, hh2, hl2, hch2⟩ := ih2
        cases L2 with
        | nil => exact absurd rfl hne2
        | cons x xs =>
          have hxb : x = b := hh2
          subst hxb
          have happ_ne : L1 ++ xs ≠ [] := List.append_ne_nil_of_left_ne_nil hne1 _
          refine ⟨L1 ++ xs, happ_ne, ?_, ?_, ?_⟩
          · rw [List.head_append_of_ne_nil hne1]; exact hh1
          · cases xs with
            | nil => simpa using hl1.trans hl2
            | cons y ys =>
              rw [List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)]
              simpa using hl2
          · intro k hk
            rw [List.length_append] at hk
            by_cases h1 : k + 1 < L1.length
            · rw [List.getElem_append_left (by omega), List.getElem_append_left h1]
              exact hch1 k h1
            · by_cases h2 : k < L1.length
              · have hkeq : k + 1 = L1.length := by omega
                rw [List.getElem_append_left h2, List.getElem_append_right (by omega)]
                have hlast_eq : L1[k] = x := by
                  have hgl := List.getLast_eq_getElem hne1
                  have hkidx : k = L1.length - 1 := by omega
                  simp only [hkidx, ← hgl, hl1]
                rw [hlast_eq]
                have hxs0 : xs[k + 1 - L1.length]'(by omega) = (x :: xs)[1]'(by simp; omega) := by
                  have : k + 1 - L1.length = 0 := by omega
                  simp [this]
                rw [hxs0]
                exact hch2 0 (by simp; omega)
              · rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
                have hidx : k + 1 - L1.length = (k - L1.length) + 1 := by omega
                have h1' : xs[k - L1.length]'(by omega) = (x :: xs)[(k - L1.length) + 1]'(by simp; omega) := rfl
                have h2' : xs[k + 1 - L1.length]'(by omega) = (x :: xs)[((k - L1.length) + 1) + 1]'(by simp; omega) := by
                  simp [hidx]
                rw [h1', h2']
                exact hch2 ((k - L1.length) + 1) (by simp; omega)
    obtain ⟨L, hne, hh, hl, hch⟩ := hchain
    obtain ⟨L', hne', hh', hl', hch', hlen'⟩ := exists_short_chain _ L hne hh hl hch
    have hpow := matPowBool_complete_list σ p L' hne' hch'
    rw [hh', hl'] at hpow
    have hcard : Fintype.card (Bool × Fin n) = 2 * n := by simp
    rw [hcard] at hlen'
    exact matPowBool_le σ p (by omega) e1 e2 hpow

lemma arcCountAll_eq_repCard {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    arcCountAll σ p l r =
      ((Finset.univ : Finset (Fin (2 * n))).filter (fun e =>
        (∀ e' : Fin (2 * n), e'.val < e.val → matPowBool (adjMat σ p) (2 * n) (edgeEquiv n e) (edgeEquiv n e') = false) ∧
        ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' =>
          matPowBool (adjMat σ p) (2 * n) (edgeEquiv n e) (edgeEquiv n e') = true)).card = l ∧
        ((Finset.univ : Finset (Fin n)).filter (fun i =>
          matPowBool (adjMat σ p) (2 * n) (edgeEquiv n e) (false, i) = true)).card = r)).card := by
  classical
  unfold arcCountAll
  symm
  refine Finset.card_bij (fun e _ => arcClass σ p (edgeEquiv n e)) ?_ ?_ ?_
  · intro e he
    obtain ⟨_, hmin, hlen, hred⟩ := Finset.mem_filter.mp he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_, ?_⟩
    · rw [arcLen_eq_card, ← hlen]
      refine Finset.card_bij (fun e' _ => (edgeEquiv n).symm e') ?_ ?_ ?_
      · intro e' he'
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [Equiv.apply_symm_apply, eqvGen_iff_matPowBool]
        exact (Finset.mem_filter.mp he').2
      · intro a _ b _ hab; exact (edgeEquiv n).symm.injective hab
      · intro e' he'
        refine ⟨edgeEquiv n e', ?_, (edgeEquiv n).symm_apply_apply e'⟩
        rw [arcClass, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (eqvGen_iff_matPowBool σ p _ _).mp (Finset.mem_filter.mp he').2⟩
    · rw [← hred]
      unfold arcRed
      refine Finset.card_bij (fun e' _ => e'.2) ?_ ?_ ?_
      · intro e' he'
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he'
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hpair : (false, e'.2) = e' := Prod.ext he2.symm rfl
        rw [hpair, eqvGen_iff_matPowBool]
        exact (Finset.mem_filter.mp he1).2
      · intro a ha b hb hab
        exact Prod.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm) hab
      · intro i hi
        refine ⟨(false, i), ?_, rfl⟩
        rw [Finset.mem_filter, arcClass, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, (eqvGen_iff_matPowBool σ p _ _).mp (Finset.mem_filter.mp hi).2⟩, rfl⟩
  · intro e1 he1 e2 he2 heq
    have hmin1 := (Finset.mem_filter.mp he1).2.1
    have hmin2 := (Finset.mem_filter.mp he2).2.1
    have hrel : Relation.EqvGen (ArcStep σ p) (edgeEquiv n e1) (edgeEquiv n e2) := by
      have hm : edgeEquiv n e2 ∈ arcClass σ p (edgeEquiv n e2) := by simp [arcClass, Relation.EqvGen.refl]
      rw [← heq] at hm
      exact (Finset.mem_filter.mp hm).2
    have hmat12 : matPowBool (adjMat σ p) (2 * n) (edgeEquiv n e1) (edgeEquiv n e2) = true :=
      (eqvGen_iff_matPowBool σ p _ _).mpr hrel
    have hmat21 : matPowBool (adjMat σ p) (2 * n) (edgeEquiv n e2) (edgeEquiv n e1) = true :=
      (eqvGen_iff_matPowBool σ p _ _).mpr (Relation.EqvGen.symm _ _ hrel)
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
    · have := hmin2 e1 hlt
      rw [hmat21] at this; cases this
    · have := hmin1 e2 hgt
      rw [hmat12] at this; cases this
  · intro c hc
    obtain ⟨hc_mem, hlen, hred⟩ := Finset.mem_filter.mp hc
    obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hc_mem
    let S : Finset (Fin (2 * n)) := Finset.univ.filter (fun e' =>
      Relation.EqvGen (ArcStep σ p) e0 (edgeEquiv n e'))
    have hSne : S.Nonempty := ⟨(edgeEquiv n).symm e0, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by rw [Equiv.apply_symm_apply]; exact Relation.EqvGen.refl _⟩⟩
    let emin := S.min' hSne
    have hemin_mem : emin ∈ S := Finset.min'_mem S hSne
    have hemin_rel : Relation.EqvGen (ArcStep σ p) e0 (edgeEquiv n emin) := (Finset.mem_filter.mp hemin_mem).2
    have hcls_eq : arcClass σ p (edgeEquiv n emin) = arcClass σ p e0 := by
      ext z
      simp only [arcClass, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => Relation.EqvGen.trans _ _ _ hemin_rel h,
        fun h => Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hemin_rel) h⟩
    refine ⟨emin, ?_, hcls_eq⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
    · intro e' hlt
      by_contra hnot
      have htrue : matPowBool (adjMat σ p) (2 * n) (edgeEquiv n emin) (edgeEquiv n e') = true := by
        cases h : matPowBool (adjMat σ p) (2 * n) (edgeEquiv n emin) (edgeEquiv n e')
        · exact absurd h hnot
        · rfl
      have hrel' := (eqvGen_iff_matPowBool σ p _ _).mp htrue
      have he'S : e' ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.EqvGen.trans _ _ _ hemin_rel hrel'⟩
      have hle := Finset.min'_le S e' he'S
      have hle_val : emin.val ≤ e'.val := hle
      omega
    · rw [← hlen, ← hcls_eq, arcLen_eq_card]
      refine Finset.card_bij (fun e' _ => edgeEquiv n e') ?_ ?_ ?_
      · intro e' he'
        rw [arcClass, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (eqvGen_iff_matPowBool σ p _ _).mp (Finset.mem_filter.mp he').2⟩
      · intro a _ b _ hab; exact (edgeEquiv n).injective hab
      · intro e' he'
        refine ⟨(edgeEquiv n).symm e', ?_, (edgeEquiv n).apply_symm_apply e'⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [Equiv.apply_symm_apply, eqvGen_iff_matPowBool]
        exact (Finset.mem_filter.mp he').2
    · rw [← hred, ← hcls_eq]
      unfold arcRed
      refine Finset.card_bij (fun i _ => (false, i)) ?_ ?_ ?_
      · intro i hi
        rw [Finset.mem_filter, arcClass, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, (eqvGen_iff_matPowBool σ p _ _).mp (Finset.mem_filter.mp hi).2⟩, rfl⟩
      · intro a _ b _ hab; exact (Prod.mk.inj hab).2
      · intro e' he'
        obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he'
        have hpair : (false, e'.2) = e' := Prod.ext he2.symm rfl
        refine ⟨e'.2, ?_, hpair⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hpair, eqvGen_iff_matPowBool]
        exact (Finset.mem_filter.mp he1).2

end GraphClosure

end KrawAndAlgebra

section CircuitBuilder

abbrev Gate := PEqualNP.CircuitLowerBounds.Gate
abbrev GateOp := PEqualNP.CircuitLowerBounds.GateOp
abbrev Circuit := PEqualNP.CircuitLowerBounds.Circuit

def GoodGate (gate : Gate) : Prop :=
  ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
  (gate.op = .not ∧ gate.inputs.length = 1)

def ValidCircuit (N0 : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, GoodGate g) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < N0 + j)

def Extends (gs1 gs2 : List Gate) : Prop := ∃ ext, gs2 = gs1 ++ ext

def evalWires (gs : List Gate) (xs : List Bool) : List Bool :=
  (Circuit.mk gs 0).wires xs

def wireAt (gs : List Gate) (xs : List Bool) (w : ℕ) : Bool :=
  (evalWires gs xs).getD w false

lemma Extends.refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma Extends.trans {gs1 gs2 gs3 : List Gate} (h1 : Extends gs1 gs2) (h2 : Extends gs2 gs3) :
    Extends gs1 gs3 := by
  rcases h1 with ⟨e1, rfl⟩
  rcases h2 with ⟨e2, rfl⟩
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

lemma Extends.length_le {gs1 gs2 : List Gate} (h : Extends gs1 gs2) : gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl⟩; simp

lemma validCircuit_nil (N0 : ℕ) : ValidCircuit N0 [] := by
  refine ⟨fun _ h => by simp at h, fun j hj => by simp at hj⟩

lemma validCircuit_snoc {N0 : ℕ} {gs : List Gate} {g : Gate}
    (hgs : ValidCircuit N0 gs) (hg : GoodGate g) (hin : ∀ i ∈ g.inputs, i < N0 + gs.length) :
    ValidCircuit N0 (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgs.1 g' h
    · exact hg
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨.or, []⟩ = gs.getD j ⟨.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : (gs ++ [g]).getD gs.length ⟨.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi

lemma validCircuit_to_readsBack {N0 : ℕ} {gs : List Gate} (h : ValidCircuit N0 gs) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N0 (Circuit.mk gs 0) :=
  h.2

lemma evalWires_nil (xs : List Bool) : evalWires [] xs = xs := rfl

lemma evalWires_append (gs1 gs2 : List Gate) (xs : List Bool) :
    evalWires (gs1 ++ gs2) xs = evalWires gs2 (evalWires gs1 xs) := by
  unfold evalWires PEqualNP.CircuitLowerBounds.Circuit.wires
  exact List.foldl_append

lemma evalWires_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    evalWires (gs ++ [g]) xs =
      evalWires gs xs ++ [g.op.eval (g.inputs.map fun i => wireAt gs xs i)] := by
  rw [evalWires_append]
  rfl

lemma evalWires_length (gs : List Gate) (xs : List Bool) :
    (evalWires gs xs).length = xs.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [evalWires_nil]
  | append_singleton gs g ih =>
    rw [evalWires_snoc, List.length_append, List.length_singleton, ih]
    simp [Nat.add_assoc]

lemma evalWires_prefix_exists (gs1 gs2 : List Gate) (xs : List Bool) :
    ∃ suf, evalWires (gs1 ++ gs2) xs = evalWires gs1 xs ++ suf := by
  induction gs2 using List.reverseRecOn with
  | nil => exact ⟨[], by simp⟩
  | append_singleton gs2 g ih =>
    obtain ⟨suf, hsuf⟩ := ih
    rw [← List.append_assoc, evalWires_snoc, hsuf, List.append_assoc]
    exact ⟨_, rfl⟩

lemma wireAt_extends {gs1 gs2 : List Gate} {xs : List Bool} {w : ℕ}
    (hext : Extends gs1 gs2) (hw : w < xs.length + gs1.length) :
    wireAt gs2 xs w = wireAt gs1 xs w := by
  rcases hext with ⟨ext, rfl⟩
  obtain ⟨suf, hsuf⟩ := evalWires_prefix_exists gs1 ext xs
  unfold wireAt
  rw [hsuf]
  have hlt : w < (evalWires gs1 xs).length := by rw [evalWires_length]; exact hw
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]

lemma wireAt_input (gs : List Gate) (xs : List Bool) {w : ℕ} (hw : w < xs.length) :
    wireAt gs xs w = xs.getD w false := by
  have hext : Extends [] gs := ⟨gs, rfl⟩
  have h := wireAt_extends hext (xs := xs) (w := w) (by simpa using hw)
  simpa [wireAt, evalWires_nil] using h

lemma wireAt_snoc_self (gs : List Gate) (g : Gate) (xs : List Bool) :
    wireAt (gs ++ [g]) xs (xs.length + gs.length) =
      g.op.eval (g.inputs.map fun i => wireAt gs xs i) := by
  unfold wireAt
  rw [evalWires_snoc]
  have hlen : (evalWires gs xs).length = xs.length + gs.length := evalWires_length gs xs
  rw [← hlen]
  simp [List.getD_eq_getElem?_getD, wireAt]

def cEmit (N0 : ℕ) (g : Gate) (gs : List Gate) : List Gate × ℕ :=
  (gs ++ [g], N0 + gs.length)

def cNot (N0 : ℕ) (w : ℕ) (gs : List Gate) : List Gate × ℕ :=
  cEmit N0 ⟨.not, [w]⟩ gs

def cAnd (N0 : ℕ) (u v : ℕ) (gs : List Gate) : List Gate × ℕ :=
  cEmit N0 ⟨.and, [u, v]⟩ gs

def cOr (N0 : ℕ) (u v : ℕ) (gs : List Gate) : List Gate × ℕ :=
  cEmit N0 ⟨.or, [u, v]⟩ gs

lemma cNot_spec {N0 : ℕ} {gs : List Gate} (w : ℕ)
    (hgs : ValidCircuit N0 gs) (hw : w < N0 + gs.length) :
    let r := cNot N0 w gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 → wireAt r.1 xs r.2 = !(wireAt gs xs w) := by
  refine ⟨validCircuit_snoc hgs (Or.inr ⟨rfl, rfl⟩) (fun i hi => by simp at hi; subst hi; exact hw),
    ⟨[⟨.not, [w]⟩], rfl⟩, by simp [cNot, cEmit], by simp [cNot, cEmit], ?_⟩
  intro xs hlen
  dsimp only [cNot, cEmit]
  rw [← hlen, wireAt_snoc_self]
  rfl

lemma cAnd_spec {N0 : ℕ} {gs : List Gate} (u v : ℕ)
    (hgs : ValidCircuit N0 gs) (hu : u < N0 + gs.length) (hv : v < N0 + gs.length) :
    let r := cAnd N0 u v gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 → wireAt r.1 xs r.2 = (wireAt gs xs u && wireAt gs xs v) := by
  refine ⟨validCircuit_snoc hgs (Or.inl ⟨Or.inl rfl, rfl⟩)
      (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> assumption),
    ⟨[⟨.and, [u, v]⟩], rfl⟩, by simp [cAnd, cEmit], by simp [cAnd, cEmit], ?_⟩
  intro xs hlen
  dsimp only [cAnd, cEmit]
  rw [← hlen, wireAt_snoc_self]
  simp [PEqualNP.CircuitLowerBounds.GateOp.eval]

lemma cOr_spec {N0 : ℕ} {gs : List Gate} (u v : ℕ)
    (hgs : ValidCircuit N0 gs) (hu : u < N0 + gs.length) (hv : v < N0 + gs.length) :
    let r := cOr N0 u v gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 → wireAt r.1 xs r.2 = (wireAt gs xs u || wireAt gs xs v) := by
  refine ⟨validCircuit_snoc hgs (Or.inl ⟨Or.inr rfl, rfl⟩)
      (fun i hi => by simp at hi; rcases hi with rfl | rfl <;> assumption),
    ⟨[⟨.or, [u, v]⟩], rfl⟩, by simp [cOr, cEmit], by simp [cOr, cEmit], ?_⟩
  intro xs hlen
  dsimp only [cOr, cEmit]
  rw [← hlen, wireAt_snoc_self]
  simp [PEqualNP.CircuitLowerBounds.GateOp.eval]

def cXor (N0 : ℕ) (u v : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let (gs1, nu) := cNot N0 u gs
  let (gs2, nv) := cNot N0 v gs1
  let (gs3, a1) := cAnd N0 u nv gs2
  let (gs4, a2) := cAnd N0 nu v gs3
  cOr N0 a1 a2 gs4

lemma cXor_spec {N0 : ℕ} {gs : List Gate} (u v : ℕ)
    (hgs : ValidCircuit N0 gs) (hu : u < N0 + gs.length) (hv : v < N0 + gs.length) :
    let r := cXor N0 u v gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 5 ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 → wireAt r.1 xs r.2 = xor (wireAt gs xs u) (wireAt gs xs v) := by
  dsimp only [cXor]
  set r1 := cNot N0 u gs with hr1
  set r2 := cNot N0 v r1.1 with hr2
  set r3 := cAnd N0 u r2.2 r2.1 with hr3
  set r4 := cAnd N0 r1.2 v r3.1 with hr4
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNot_spec u hgs hu
  rw [← hr1] at v1 e1 l1 w1 f1
  obtain ⟨v2, e2, l2, w2, f2⟩ := cNot_spec v v1 (by omega)
  rw [← hr2] at v2 e2 l2 w2 f2
  obtain ⟨v3, e3, l3, w3, f3⟩ := cAnd_spec u r2.2 v2 (by omega) w2
  rw [← hr3] at v3 e3 l3 w3 f3
  obtain ⟨v4, e4, l4, w4, f4⟩ := cAnd_spec r1.2 v v3 (by omega) (by omega)
  rw [← hr4] at v4 e4 l4 w4 f4
  obtain ⟨v5, e5, l5, w5, f5⟩ := cOr_spec r3.2 r4.2 v4 (by omega) w4
  refine ⟨v5, e1.trans (e2.trans (e3.trans (e4.trans e5))), by omega, w5, fun xs hlen => ?_⟩
  rw [f5 xs hlen,
    wireAt_extends e4 (w := r3.2) (by omega), f3 xs hlen,
    wireAt_extends (e1.trans e2) (w := u) (by omega), f2 xs hlen, wireAt_extends e1 (w := v) (by omega),
    f4 xs hlen, wireAt_extends (e2.trans e3) (w := r1.2) (by omega), f1 xs hlen,
    wireAt_extends (e1.trans (e2.trans e3)) (w := v) (by omega)]
  cases wireAt gs xs u <;> cases wireAt gs xs v <;> rfl

def cMux (N0 : ℕ) (s t f : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let (gs1, ns) := cNot N0 s gs
  let (gs2, a1) := cAnd N0 s t gs1
  let (gs3, a2) := cAnd N0 ns f gs2
  cOr N0 a1 a2 gs3

lemma cMux_spec {N0 : ℕ} {gs : List Gate} (s t f : ℕ)
    (hgs : ValidCircuit N0 gs) (hs : s < N0 + gs.length)
    (ht : t < N0 + gs.length) (hf : f < N0 + gs.length) :
    let r := cMux N0 s t f gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 4 ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 →
      wireAt r.1 xs r.2 = if wireAt gs xs s then wireAt gs xs t else wireAt gs xs f := by
  dsimp only [cMux]
  set r1 := cNot N0 s gs with hr1
  set r2 := cAnd N0 s t r1.1 with hr2
  set r3 := cAnd N0 r1.2 f r2.1 with hr3
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNot_spec s hgs hs
  rw [← hr1] at v1 e1 l1 w1 f1
  obtain ⟨v2, e2, l2, w2, f2⟩ := cAnd_spec s t v1 (by omega) (by omega)
  rw [← hr2] at v2 e2 l2 w2 f2
  obtain ⟨v3, e3, l3, w3, f3⟩ := cAnd_spec r1.2 f v2 (by omega) (by omega)
  rw [← hr3] at v3 e3 l3 w3 f3
  obtain ⟨v4, e4, l4, w4, f4⟩ := cOr_spec r2.2 r3.2 v3 (by omega) w3
  refine ⟨v4, e1.trans (e2.trans (e3.trans e4)), by omega, w4, fun xs hlen => ?_⟩
  rw [f4 xs hlen, wireAt_extends e3 (w := r2.2) (by omega), f2 xs hlen,
    wireAt_extends e1 (w := s) (by omega), wireAt_extends e1 (w := t) (by omega),
    f3 xs hlen, wireAt_extends e2 (w := r1.2) (by omega), f1 xs hlen,
    wireAt_extends (e1.trans e2) (w := f) (by omega)]
  cases wireAt gs xs s <;> cases wireAt gs xs t <;> cases wireAt gs xs f <;> rfl

def cEqBit (N0 : ℕ) (u v : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let (gs1, x) := cXor N0 u v gs
  cNot N0 x gs1

lemma cEqBit_spec {N0 : ℕ} {gs : List Gate} (u v : ℕ)
    (hgs : ValidCircuit N0 gs) (hu : u < N0 + gs.length) (hv : v < N0 + gs.length) :
    let r := cEqBit N0 u v gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 6 ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 → wireAt r.1 xs r.2 = (wireAt gs xs u == wireAt gs xs v) := by
  dsimp only [cEqBit]
  set r1 := cXor N0 u v gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cXor_spec u v hgs hu hv
  rw [← hr1] at v1 e1 l1 w1 f1
  obtain ⟨v2, e2, l2, w2, f2⟩ := cNot_spec r1.2 v1 w1
  refine ⟨v2, e1.trans e2, by omega, w2, fun xs hlen => ?_⟩
  rw [f2 xs hlen, f1 xs hlen]
  cases wireAt gs xs u <;> cases wireAt gs xs v <;> rfl

def cFullAdder (N0 : ℕ) (a b cin : ℕ) (gs : List Gate) : List Gate × ℕ × ℕ :=
  let (gs1, ab) := cXor N0 a b gs
  let (gs2, s) := cXor N0 ab cin gs1
  let (gs3, c1) := cAnd N0 a b gs2
  let (gs4, c2) := cAnd N0 ab cin gs3
  let (gs5, cout) := cOr N0 c1 c2 gs4
  (gs5, s, cout)

lemma cFullAdder_spec {N0 : ℕ} {gs : List Gate} (a b cin : ℕ)
    (hgs : ValidCircuit N0 gs) (ha : a < N0 + gs.length)
    (hb : b < N0 + gs.length) (hc : cin < N0 + gs.length) :
    let r := cFullAdder N0 a b cin gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 13 ∧
    r.2.1 < N0 + r.1.length ∧ r.2.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 →
      (wireAt r.1 xs r.2.1).toNat + 2 * (wireAt r.1 xs r.2.2).toNat =
        (wireAt gs xs a).toNat + (wireAt gs xs b).toNat + (wireAt gs xs cin).toNat := by
  dsimp only [cFullAdder]
  set r1 := cXor N0 a b gs with hr1
  set r2 := cXor N0 r1.2 cin r1.1 with hr2
  set r3 := cAnd N0 a b r2.1 with hr3
  set r4 := cAnd N0 r1.2 cin r3.1 with hr4
  obtain ⟨v1, e1, l1, w1, f1⟩ := cXor_spec a b hgs ha hb
  rw [← hr1] at v1 e1 l1 w1 f1
  have e1len := e1.length_le
  obtain ⟨v2, e2, l2, w2, f2⟩ := cXor_spec r1.2 cin v1 w1 (by omega)
  rw [← hr2] at v2 e2 l2 w2 f2
  have e2len := e2.length_le
  obtain ⟨v3, e3, l3, w3, f3⟩ := cAnd_spec a b v2 (by omega) (by omega)
  rw [← hr3] at v3 e3 l3 w3 f3
  have e3len := e3.length_le
  obtain ⟨v4, e4, l4, w4, f4⟩ := cAnd_spec r1.2 cin v3 (by omega) (by omega)
  rw [← hr4] at v4 e4 l4 w4 f4
  have e4len := e4.length_le
  obtain ⟨v5, e5, l5, w5, f5⟩ := cOr_spec r3.2 r4.2 v4 (by omega) w4
  have e5len := e5.length_le
  refine ⟨v5, e1.trans (e2.trans (e3.trans (e4.trans e5))), by omega, by omega, w5, fun xs hlen => ?_⟩
  rw [wireAt_extends (e3.trans (e4.trans e5)) (w := r2.2) (by omega), f2 xs hlen, f1 xs hlen,
    wireAt_extends e1 (w := cin) (by omega),
    f5 xs hlen, wireAt_extends e4 (w := r3.2) (by omega), f3 xs hlen,
    wireAt_extends (e1.trans e2) (w := a) (by omega), wireAt_extends (e1.trans e2) (w := b) (by omega),
    f4 xs hlen, wireAt_extends (e2.trans e3) (w := r1.2) (by omega), f1 xs hlen,
    wireAt_extends (e1.trans (e2.trans e3)) (w := cin) (by omega)]
  cases wireAt gs xs a <;> cases wireAt gs xs b <;> cases wireAt gs xs cin <;> rfl

def cBuildFin {α : Type*} : (k : ℕ) → (Fin k → List Gate → List Gate × α) → List Gate → List Gate × (Fin k → α)
  | 0, _, gs => (gs, fun i => Fin.elim0 i)
  | k + 1, f, gs =>
    let r1 := cBuildFin k (fun i => f i.castSucc) gs
    let r2 := f (Fin.last k) r1.1
    (r2.1, Fin.snoc r1.2 r2.2)

lemma cBuildFin_spec {α : Type*} {N0 : ℕ} (k cost : ℕ)
    (f : Fin k → List Gate → List Gate × α)
    (P : List Gate → Fin k → α → Prop)
    (hmono : ∀ gs1 gs2 i a, Extends gs1 gs2 → P gs1 i a → P gs2 i a)
    (gs : List Gate) (hgs : ValidCircuit N0 gs)
    (hstep : ∀ (i : Fin k) (g : List Gate), ValidCircuit N0 g → Extends gs g →
      let r := f i g
      ValidCircuit N0 r.1 ∧ Extends g r.1 ∧ r.1.length ≤ g.length + cost ∧ P r.1 i r.2) :
    let r := cBuildFin k f gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k * cost ∧
    ∀ i : Fin k, P r.1 i (r.2 i) := by
  induction k generalizing gs with
  | zero =>
    exact ⟨hgs, Extends.refl gs, by simp [cBuildFin], fun i => Fin.elim0 i⟩
  | succ k ih =>
    dsimp only [cBuildFin]
    obtain ⟨v1, e1, l1, hp1⟩ := ih (fun i => f i.castSucc) (fun g i a => P g i.castSucc a)
      (fun g1 g2 i a he h => hmono g1 g2 i.castSucc a he h)
      gs hgs (fun i g hg he => hstep i.castSucc g hg he)
    obtain ⟨v2, e2, l2, hp2⟩ := hstep (Fin.last k) _ v1 e1
    refine ⟨v2, e1.trans e2, ?_, fun i => ?_⟩
    · have : (k + 1) * cost = k * cost + cost := Nat.succ_mul k cost
      omega
    · refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.snoc_last]; exact hp2
      · intro j; simp only [Fin.snoc_castSucc]; exact hmono _ _ j.castSucc _ e2 (hp1 j)

def cFoldFin {α : Type*} : (k : ℕ) → (Fin k → α → List Gate → List Gate × α) → α → List Gate → List Gate × α
  | 0, _, init, gs => (gs, init)
  | k + 1, f, init, gs =>
    let r1 := cFoldFin k (fun i => f i.castSucc) init gs
    f (Fin.last k) r1.2 r1.1

lemma cFoldFin_spec {α : Type*} {N0 : ℕ} (k cost : ℕ)
    (f : Fin k → α → List Gate → List Gate × α)
    (P : (m : ℕ) → m ≤ k → List Gate → α → Prop)
    (init : α) (gs : List Gate) (hgs : ValidCircuit N0 gs)
    (hinit : P 0 (Nat.zero_le k) gs init)
    (hstep : ∀ (i : Fin k) (gs1 : List Gate) (a : α),
      ValidCircuit N0 gs1 → Extends gs gs1 → P i.val (le_of_lt i.isLt) gs1 a →
      let r := f i a gs1
      ValidCircuit N0 r.1 ∧ Extends gs1 r.1 ∧ r.1.length ≤ gs1.length + cost ∧
      P (i.val + 1) i.isLt r.1 r.2) :
    let r := cFoldFin k f init gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k * cost ∧
    P k (le_refl k) r.1 r.2 := by
  induction k generalizing init gs with
  | zero =>
    exact ⟨hgs, Extends.refl gs, by simp [cFoldFin], hinit⟩
  | succ k ih =>
    dsimp only [cFoldFin]
    obtain ⟨v1, e1, l1, hp1⟩ := ih (fun i => f i.castSucc)
      (fun m hm g a => P m (Nat.le_succ_of_le hm) g a)
      init gs hgs hinit (fun i gs1 a hv he hp => hstep i.castSucc gs1 a hv he hp)
    obtain ⟨v2, e2, l2, hp2⟩ := hstep (Fin.last k) _ _ v1 e1 hp1
    refine ⟨v2, e1.trans e2, ?_, hp2⟩
    have : (k + 1) * cost = k * cost + cost := Nat.succ_mul k cost
    omega

def HasConsts (xs : List Bool) (N0 : ℕ) : Prop :=
  xs.length = N0 ∧ 2 ≤ N0 ∧ xs.getD 0 false = false ∧ xs.getD 1 false = true

lemma wireAt_zero {gs : List Gate} {xs : List Bool} {N0 : ℕ} (hc : HasConsts xs N0) :
    wireAt gs xs 0 = false := by
  have h1 := hc.1; have h2 := hc.2.1
  rw [wireAt_input gs xs (by omega), hc.2.2.1]

lemma wireAt_one {gs : List Gate} {xs : List Bool} {N0 : ℕ} (hc : HasConsts xs N0) :
    wireAt gs xs 1 = true := by
  have h1 := hc.1; have h2 := hc.2.1
  rw [wireAt_input gs xs (by omega), hc.2.2.2]

def cAndFin (N0 : ℕ) (k : ℕ) (w : Fin k → ℕ) (gs : List Gate) : List Gate × ℕ :=
  cFoldFin k (fun i acc g => cAnd N0 acc (w i) g) 1 gs

lemma cAndFin_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {k : ℕ} {w : Fin k → ℕ}
    (hgs : ValidCircuit N0 gs) (hw : ∀ i : Fin k, w i < N0 + gs.length) :
    let r := cAndFin N0 k w gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      (wireAt r.1 xs r.2 = true ↔ ∀ i : Fin k, wireAt gs xs (w i) = true) := by
  dsimp only [cAndFin]
  have h := cFoldFin_spec (N0 := N0) k 1 (fun i acc g => cAnd N0 acc (w i) g)
    (fun m _ g acc => acc < N0 + g.length ∧
      ∀ xs, HasConsts xs N0 → (wireAt g xs acc = true ↔ ∀ i : Fin k, i.val < m → wireAt gs xs (w i) = true))
    1 gs hgs
    ⟨by omega, fun xs hc => by simp [wireAt_one hc]⟩
    (fun i gs1 acc hv he ⟨hacc, hsem⟩ => by
      have helen := he.length_le
      obtain ⟨v1, e1, l1, w1, f1⟩ := cAnd_spec acc (w i) hv hacc (by have := hw i; omega)
      refine ⟨v1, e1, by omega, w1, fun xs hc => ?_⟩
      have hlen := hc.1
      rw [f1 xs hlen, wireAt_extends he (w := w i) (by rw [hlen]; exact hw i), Bool.and_eq_true, hsem xs hc]
      constructor
      · rintro ⟨hprev, hcur⟩ j hj
        by_cases hlt : j.val < i.val
        · exact hprev j hlt
        · have heq : j = i := Fin.ext (by omega)
          subst heq; exact hcur
      · intro hall
        exact ⟨fun j hj => hall j (by omega), hall i (by omega)⟩)
  refine ⟨h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc]
  exact ⟨fun hp i => hp i i.isLt, fun hp i _ => hp i⟩

def cOrFin (N0 : ℕ) (k : ℕ) (w : Fin k → ℕ) (gs : List Gate) : List Gate × ℕ :=
  cFoldFin k (fun i acc g => cOr N0 acc (w i) g) 0 gs

lemma cOrFin_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {k : ℕ} {w : Fin k → ℕ}
    (hgs : ValidCircuit N0 gs) (hw : ∀ i : Fin k, w i < N0 + gs.length) :
    let r := cOrFin N0 k w gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      (wireAt r.1 xs r.2 = true ↔ ∃ i : Fin k, wireAt gs xs (w i) = true) := by
  dsimp only [cOrFin]
  have h := cFoldFin_spec (N0 := N0) k 1 (fun i acc g => cOr N0 acc (w i) g)
    (fun m _ g acc => acc < N0 + g.length ∧
      ∀ xs, HasConsts xs N0 → (wireAt g xs acc = true ↔ ∃ i : Fin k, i.val < m ∧ wireAt gs xs (w i) = true))
    0 gs hgs
    ⟨by omega, fun xs hc => by simp [wireAt_zero hc]⟩
    (fun i gs1 acc hv he ⟨hacc, hsem⟩ => by
      have helen := he.length_le
      obtain ⟨v1, e1, l1, w1, f1⟩ := cOr_spec acc (w i) hv hacc (by have := hw i; omega)
      refine ⟨v1, e1, by omega, w1, fun xs hc => ?_⟩
      have hlen := hc.1
      rw [f1 xs hlen, wireAt_extends he (w := w i) (by rw [hlen]; exact hw i), Bool.or_eq_true, hsem xs hc]
      constructor
      · rintro (⟨j, hlt, hj⟩ | hcur)
        · exact ⟨j, by omega, hj⟩
        · exact ⟨i, by omega, hcur⟩
      · rintro ⟨j, hj, hval⟩
        by_cases hlt : j.val < i.val
        · exact Or.inl ⟨j, hlt, hval⟩
        · have heq : j = i := Fin.ext (by omega)
          subst heq; exact Or.inr hval)
  refine ⟨h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc]
  exact ⟨fun ⟨i, _, hi⟩ => ⟨i, hi⟩, fun ⟨i, hi⟩ => ⟨i, i.isLt, hi⟩⟩

abbrev Word (B : ℕ) := Fin B → ℕ

def ValidWord (N0 : ℕ) (gs : List Gate) {B : ℕ} (w : Word B) : Prop :=
  ∀ i : Fin B, w i < N0 + gs.length

lemma ValidWord.extends {N0 : ℕ} {gs1 gs2 : List Gate} {B : ℕ} {w : Word B}
    (hw : ValidWord N0 gs1 w) (he : Extends gs1 gs2) : ValidWord N0 gs2 w :=
  fun i => lt_of_lt_of_le (hw i) (Nat.add_le_add_left he.length_le N0)

def wordNat (gs : List Gate) (xs : List Bool) {B : ℕ} (w : Word B) : ℕ :=
  ∑ i : Fin B, (wireAt gs xs (w i)).toNat * 2 ^ i.val

def wordZMod (gs : List Gate) (xs : List Bool) {B : ℕ} (w : Word B) : ZMod (2 ^ B) :=
  (wordNat gs xs w : ZMod (2 ^ B))

lemma wordNat_extends {N0 : ℕ} {gs1 gs2 : List Gate} {xs : List Bool} {B : ℕ} {w : Word B}
    (he : Extends gs1 gs2) (hlen : xs.length = N0) (hw : ValidWord N0 gs1 w) :
    wordNat gs2 xs w = wordNat gs1 xs w := by
  unfold wordNat
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wireAt_extends he (by rw [hlen]; exact hw i)]

lemma wordZMod_extends {N0 : ℕ} {gs1 gs2 : List Gate} {xs : List Bool} {B : ℕ} {w : Word B}
    (he : Extends gs1 gs2) (hlen : xs.length = N0) (hw : ValidWord N0 gs1 w) :
    wordZMod gs2 xs w = wordZMod gs1 xs w := by
  unfold wordZMod
  rw [wordNat_extends he hlen hw]

lemma wordNat_lt (gs : List Gate) (xs : List Bool) {B : ℕ} (w : Word B) :
    wordNat gs xs w < 2 ^ B := by
  unfold wordNat
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Fin.sum_univ_castSucc]
    have h1 : (∑ i : Fin B, (wireAt gs xs (w i.castSucc)).toNat * 2 ^ i.castSucc.val) < 2 ^ B :=
      ih (fun i => w i.castSucc)
    have h2 : (wireAt gs xs (w (Fin.last B))).toNat ≤ 1 := by cases wireAt gs xs (w (Fin.last B)) <;> simp
    have hpow : 2 ^ (B + 1) = 2 ^ B + 2 ^ B := by rw [pow_succ, mul_two]
    have hlast : (wireAt gs xs (w (Fin.last B))).toNat * 2 ^ (Fin.last B).val ≤ 2 ^ B := by
      simp only [Fin.val_last]
      calc (wireAt gs xs (w (Fin.last B))).toNat * 2 ^ B ≤ 1 * 2 ^ B := Nat.mul_le_mul_right _ h2
        _ = 2 ^ B := one_mul _
    omega

lemma wordZMod_val (gs : List Gate) (xs : List Bool) {B : ℕ} (w : Word B) :
    (wordZMod gs xs w).val = wordNat gs xs w := by
  have hpos : 0 < 2 ^ B := by positivity
  haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hpos⟩
  unfold wordZMod
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (wordNat_lt gs xs w)]

lemma wordNat_succ (gs : List Gate) (xs : List Bool) {B : ℕ} (w : Word (B + 1)) :
    wordNat gs xs w = (wireAt gs xs (w 0)).toNat + 2 * wordNat gs xs (fun i => w i.succ) := by
  unfold wordNat
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => by ring

lemma wordNat_testBit (gs : List Gate) (xs : List Bool) {B : ℕ} (w : Word B) (k : ℕ) :
    (wordNat gs xs w).testBit k = if h : k < B then wireAt gs xs (w ⟨k, h⟩) else false := by
  induction B generalizing k with
  | zero =>
    simp [wordNat]
  | succ B ih =>
    rw [wordNat_succ]
    cases k with
    | zero =>
      simp only [Nat.zero_lt_succ, ↓reduceDIte]
      change ((wireAt gs xs (w 0)).toNat + 2 * wordNat gs xs (fun i => w i.succ)).testBit 0 = wireAt gs xs (w 0)
      cases h0 : wireAt gs xs (w 0) <;> simp [Nat.testBit_zero]
    | succ k =>
      have htb : ((wireAt gs xs (w 0)).toNat + 2 * wordNat gs xs (fun i => w i.succ)).testBit (k + 1) =
          (wordNat gs xs (fun i => w i.succ)).testBit k := by
        rw [Nat.testBit_succ]
        congr 1
        cases wireAt gs xs (w 0) <;> simp <;> omega
      rw [htb, ih (fun i => w i.succ) k]
      by_cases hk : k < B
      · have hk1 : k + 1 < B + 1 := by omega
        simp [hk, hk1]
      · have hk1 : ¬ (k + 1 < B + 1) := by omega
        simp [hk, hk1]

def cZeroWord (B : ℕ) : Word B := fun _ => 0

def cConstWord (B : ℕ) (v : ℕ) : Word B :=
  fun i => if v.testBit i.val then 1 else 0

def cBitWord (B : ℕ) (w : ℕ) : Word B :=
  fun i => if i.val = 0 then w else 0

def cShiftLeft (B : ℕ) (j : ℕ) (a : Word B) : Word B :=
  fun i => if h : j ≤ i.val then a ⟨i.val - j, by omega⟩ else 0

def cShiftRightResize (B1 B2 : ℕ) (j : ℕ) (a : Word B1) : Word B2 :=
  fun i => if h : i.val + j < B1 then a ⟨i.val + j, h⟩ else 0

lemma validWord_cZeroWord {N0 : ℕ} (hN : 2 ≤ N0) (gs : List Gate) (B : ℕ) :
    ValidWord N0 gs (cZeroWord B) := fun _ => by simp [cZeroWord]; omega

lemma wordNat_cZeroWord {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0) (B : ℕ) :
    wordNat gs xs (cZeroWord B) = 0 := by
  simp [wordNat, cZeroWord, wireAt_zero hc]

lemma wordZMod_cZeroWord {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0) (B : ℕ) :
    wordZMod gs xs (cZeroWord B) = 0 := by
  simp [wordZMod, wordNat_cZeroWord hc]

lemma validWord_cConstWord {N0 : ℕ} (hN : 2 ≤ N0) (gs : List Gate) (B v : ℕ) :
    ValidWord N0 gs (cConstWord B v) := fun i => by
  unfold cConstWord; split_ifs <;> omega

lemma wordNat_cConstWord {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0) (B v : ℕ) :
    wordNat gs xs (cConstWord B v) = v % 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [wordNat_testBit, Nat.testBit_mod_two_pow]
  by_cases hk : k < B
  · simp only [hk, ↓reduceDIte, decide_true, Bool.true_and, cConstWord]
    cases hv : v.testBit k <;> simp [wireAt_zero hc, wireAt_one hc]
  · simp [hk]

lemma wordZMod_cConstWord {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0) (B v : ℕ) :
    wordZMod gs xs (cConstWord B v) = (v : ZMod (2 ^ B)) := by
  unfold wordZMod
  rw [wordNat_cConstWord hc]
  have hpos : 0 < 2 ^ B := by positivity
  haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hpos⟩
  exact ZMod.natCast_mod v (2 ^ B)

lemma validWord_cBitWord {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} (B : ℕ) {w : ℕ} (hw : w < N0 + gs.length) :
    ValidWord N0 gs (cBitWord B w) := fun i => by
  unfold cBitWord; split_ifs <;> omega

lemma wordNat_cBitWord {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0)
    {B : ℕ} (hB : 1 ≤ B) (w : ℕ) :
    wordNat gs xs (cBitWord B w) = (wireAt gs xs w).toNat := by
  unfold wordNat
  rw [Finset.sum_eq_single ⟨0, hB⟩]
  · simp [cBitWord]
  · intro i _ hne
    have : i.val ≠ 0 := fun h => hne (Fin.ext h)
    simp [cBitWord, this, wireAt_zero hc]
  · intro h0; exact absurd (Finset.mem_univ _) h0

lemma validWord_cShiftLeft {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B : ℕ} (j : ℕ)
    {a : Word B} (ha : ValidWord N0 gs a) :
    ValidWord N0 gs (cShiftLeft B j a) := fun i => by
  unfold cShiftLeft
  split_ifs with h
  · exact ha _
  · omega

lemma wordNat_cShiftLeft {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0)
    {B : ℕ} (j : ℕ) (a : Word B) :
    wordNat gs xs (cShiftLeft B j a) = (wordNat gs xs a * 2 ^ j) % 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [wordNat_testBit, Nat.testBit_mod_two_pow, mul_comm (wordNat gs xs a), Nat.testBit_two_pow_mul]
  by_cases hk : k < B
  · simp only [hk, ↓reduceDIte, decide_true, Bool.true_and, cShiftLeft]
    by_cases hj : j ≤ k
    · simp only [hj, ↓reduceDIte, decide_true, Bool.true_and]
      rw [wordNat_testBit, dif_pos (by omega)]
    · simp [hj, wireAt_zero hc]
  · simp [hk]

lemma wordZMod_cShiftLeft {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0)
    {B : ℕ} (j : ℕ) (a : Word B) :
    wordZMod gs xs (cShiftLeft B j a) = (2 : ZMod (2 ^ B)) ^ j * wordZMod gs xs a := by
  have hpos : 0 < 2 ^ B := by positivity
  haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hpos⟩
  unfold wordZMod
  rw [wordNat_cShiftLeft hc, ZMod.natCast_mod]
  push_cast; ring

lemma validWord_cShiftRightResize {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B1 B2 : ℕ} (j : ℕ)
    {a : Word B1} (ha : ValidWord N0 gs a) :
    ValidWord N0 gs (cShiftRightResize B1 B2 j a) := fun i => by
  unfold cShiftRightResize
  split_ifs with h
  · exact ha _
  · omega

lemma wordNat_cShiftRightResize {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0)
    {B1 B2 : ℕ} (j : ℕ) (a : Word B1) :
    wordNat gs xs (cShiftRightResize B1 B2 j a) = (wordNat gs xs a / 2 ^ j) % 2 ^ B2 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [wordNat_testBit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hk : k < B2
  · simp only [hk, ↓reduceDIte, decide_true, Bool.true_and, cShiftRightResize]
    rw [wordNat_testBit]
    have hcomm : j + k = k + j := Nat.add_comm j k
    by_cases h1 : k + j < B1
    · rw [dif_pos h1, dif_pos (by omega)]
    · rw [dif_neg h1, dif_neg (by omega), wireAt_zero hc]
  · simp [hk]

def cNotWord (N0 B : ℕ) (a : Word B) (gs : List Gate) : List Gate × Word B :=
  cBuildFin B (fun i g => cNot N0 (a i) g) gs

lemma sum_two_pow_fin (B : ℕ) : (∑ i : Fin B, 2 ^ i.val) + 1 = 2 ^ B := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Fin.sum_univ_castSucc, Fin.val_last, pow_succ, mul_two]
    have : (∑ x : Fin B, 2 ^ x.castSucc.val) = ∑ x : Fin B, 2 ^ x.val := rfl
    rw [this]; omega

lemma cNotWord_spec {N0 : ℕ} {gs : List Gate} {B : ℕ} {a : Word B}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) :
    let r := cNotWord N0 B a gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + B ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, xs.length = N0 →
      wordNat r.1 xs r.2 + wordNat gs xs a + 1 = 2 ^ B := by
  dsimp only [cNotWord]
  have h := cBuildFin_spec (N0 := N0) B 1 (fun i g => cNot N0 (a i) g)
    (fun g i w => w < N0 + g.length ∧ ∀ xs, xs.length = N0 → wireAt g xs w = !(wireAt gs xs (a i)))
    (fun g1 g2 i w he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
      fun xs hlen => by rw [wireAt_extends he (by omega), hf xs hlen]⟩)
    gs hgs
    (fun i g hg he => by
      have helen := he.length_le
      obtain ⟨v1, e1, l1, w1, f1⟩ := cNot_spec (a i) hg (by have := ha i; omega)
      exact ⟨v1, e1, by omega, w1, fun xs hlen => by
        rw [f1 xs hlen, wireAt_extends he (by have := ha i; omega)]⟩)
  refine ⟨h.1, h.2.1, by simpa using h.2.2.1, fun i => (h.2.2.2 i).1, fun xs hlen => ?_⟩
  unfold wordNat
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ i : Fin B,
      (wireAt (cBuildFin B (fun i g => cNot N0 (a i) g) gs).1 xs ((cBuildFin B (fun i g => cNot N0 (a i) g) gs).2 i)).toNat * 2 ^ i.val +
      (wireAt gs xs (a i)).toNat * 2 ^ i.val = 2 ^ i.val := by
    intro i
    rw [(h.2.2.2 i).2 xs hlen]
    cases wireAt gs xs (a i) <;> simp
  simp_rw [hterm]
  exact sum_two_pow_fin B

def cMuxWord (N0 B : ℕ) (s : ℕ) (t f : Word B) (gs : List Gate) : List Gate × Word B :=
  cBuildFin B (fun i g => cMux N0 s (t i) (f i) g) gs

lemma cMuxWord_spec {N0 : ℕ} {gs : List Gate} {B : ℕ} {s : ℕ} {t f : Word B}
    (hgs : ValidCircuit N0 gs) (hs : s < N0 + gs.length)
    (ht : ValidWord N0 gs t) (hf : ValidWord N0 gs f) :
    let r := cMuxWord N0 B s t f gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 4 * B ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, xs.length = N0 →
      wordNat r.1 xs r.2 = if wireAt gs xs s then wordNat gs xs t else wordNat gs xs f := by
  dsimp only [cMuxWord]
  have h := cBuildFin_spec (N0 := N0) B 4 (fun i g => cMux N0 s (t i) (f i) g)
    (fun g i w => w < N0 + g.length ∧
      ∀ xs, xs.length = N0 →
        wireAt g xs w = if wireAt gs xs s then wireAt gs xs (t i) else wireAt gs xs (f i))
    (fun g1 g2 i w he ⟨hw, hf'⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
      fun xs hlen => by rw [wireAt_extends he (by omega), hf' xs hlen]⟩)
    gs hgs
    (fun i g hg he => by
      have helen := he.length_le
      obtain ⟨v1, e1, l1, w1, f1⟩ := cMux_spec s (t i) (f i) hg (by omega) (by have := ht i; omega) (by have := hf i; omega)
      exact ⟨v1, e1, l1, w1, fun xs hlen => by
        rw [f1 xs hlen, wireAt_extends he (by omega),
          wireAt_extends he (by have := ht i; omega),
          wireAt_extends he (by have := hf i; omega)]⟩)
  refine ⟨h.1, h.2.1, by have := h.2.2.1; nlinarith, fun i => (h.2.2.2 i).1, fun xs hlen => ?_⟩
  unfold wordNat
  cases hsel : wireAt gs xs s
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(h.2.2.2 i).2 xs hlen, hsel]; rfl
  · simp only [↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(h.2.2.2 i).2 xs hlen, hsel]; rfl

def cAddCin (N0 : ℕ) : (B : ℕ) → Word B → Word B → ℕ → List Gate → List Gate × Word B × ℕ
  | 0, _, _, cin, gs => (gs, fun i => Fin.elim0 i, cin)
  | B + 1, a, b, cin, gs =>
    let (gs1, s0, c1) := cFullAdder N0 (a 0) (b 0) cin gs
    let (gs2, sRest, cout) := cAddCin N0 B (fun i => a i.succ) (fun i => b i.succ) c1 gs1
    (gs2, Fin.cons s0 sRest, cout)

lemma cAddCin_spec {N0 : ℕ} (B : ℕ) {gs : List Gate} {a b : Word B} {cin : ℕ}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) (hb : ValidWord N0 gs b)
    (hc : cin < N0 + gs.length) :
    let r := cAddCin N0 B a b cin gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 13 * B ∧
    ValidWord N0 r.1 r.2.1 ∧ r.2.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, xs.length = N0 →
      wordNat r.1 xs r.2.1 + 2 ^ B * (wireAt r.1 xs r.2.2).toNat =
        wordNat gs xs a + wordNat gs xs b + (wireAt gs xs cin).toNat := by
  induction B generalizing gs cin with
  | zero =>
    exact ⟨hgs, Extends.refl gs, by simp [cAddCin], fun i => Fin.elim0 i, hc,
      fun xs _ => by simp [cAddCin, wordNat]⟩
  | succ B ih =>
    dsimp only [cAddCin]
    set r1 := cFullAdder N0 (a 0) (b 0) cin gs with hr1
    obtain ⟨v1, e1, l1, ws0, wc1, ff⟩ := cFullAdder_spec (a 0) (b 0) cin hgs (ha 0) (hb 0) hc
    rw [← hr1] at v1 e1 l1 ws0 wc1 ff
    have e1len : gs.length ≤ r1.1.length := e1.length_le
    have ha' : ValidWord N0 r1.1 (fun i : Fin B => a i.succ) :=
      fun i => (ha.extends e1) i.succ
    have hb' : ValidWord N0 r1.1 (fun i : Fin B => b i.succ) :=
      fun i => (hb.extends e1) i.succ
    obtain ⟨v2, e2, l2, wsR, wco, f2⟩ := ih v1 ha' hb' wc1
    have e2len := e2.length_le
    refine ⟨v2, e1.trans e2, by nlinarith, ?_, wco, fun xs hlen => ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        exact lt_of_lt_of_le ws0 (Nat.add_le_add_left e2len N0)
      · intro j; simp only [Fin.cons_succ]; exact wsR j
    · rw [wordNat_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [wireAt_extends e2 (w := r1.2.1) (by rw [hlen]; exact ws0)]
      have hrec := f2 xs hlen
      have ha_eq : wordNat r1.1 xs (fun i => a i.succ) =
          wordNat gs xs (fun i => a i.succ) :=
        wordNat_extends e1 hlen (fun i => ha i.succ)
      have hb_eq : wordNat r1.1 xs (fun i => b i.succ) =
          wordNat gs xs (fun i => b i.succ) :=
        wordNat_extends e1 hlen (fun i => hb i.succ)
      rw [ha_eq, hb_eq] at hrec
      have hfa := ff xs hlen
      rw [wordNat_succ gs xs a, wordNat_succ gs xs b, pow_succ]
      linarith

def cAdd (N0 B : ℕ) (a b : Word B) (gs : List Gate) : List Gate × Word B :=
  let r := cAddCin N0 B a b 0 gs
  (r.1, r.2.1)

lemma cAdd_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B : ℕ} {a b : Word B}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) (hb : ValidWord N0 gs b) :
    let r := cAdd N0 B a b gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 13 * B ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = wordZMod gs xs a + wordZMod gs xs b := by
  dsimp only [cAdd]
  obtain ⟨v1, e1, l1, w1, _, f1⟩ := cAddCin_spec B (cin := 0) hgs ha hb (by omega)
  refine ⟨v1, e1, l1, w1, fun xs hc => ?_⟩
  have hnat := f1 xs hc.1
  rw [wireAt_zero hc] at hnat
  simp only [Bool.toNat_false, add_zero] at hnat
  have hcast := congrArg (Nat.cast (R := ZMod (2 ^ B))) hnat
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero] at hcast
  exact hcast

def cNeg (N0 B : ℕ) (a : Word B) (gs : List Gate) : List Gate × Word B :=
  let (gs1, na) := cNotWord N0 B a gs
  let r := cAddCin N0 B na (cZeroWord B) 1 gs1
  (r.1, r.2.1)

lemma cNeg_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B : ℕ} {a : Word B}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) :
    let r := cNeg N0 B a gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 14 * B ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = -(wordZMod gs xs a) := by
  dsimp only [cNeg]
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNotWord_spec hgs ha
  obtain ⟨v2, e2, l2, w2, _, f2⟩ := cAddCin_spec B (cin := 1) v1 w1 (validWord_cZeroWord hN _ B) (by omega)
  refine ⟨v2, e1.trans e2, by omega, w2, fun xs hc => ?_⟩
  have hnat := f2 xs hc.1
  rw [wordNat_cZeroWord hc, add_zero, wireAt_one hc] at hnat
  simp only [Bool.toNat_true] at hnat
  have hcast := congrArg (Nat.cast (R := ZMod (2 ^ B))) hnat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self, zero_mul, add_zero] at hcast
  have hnot := congrArg (Nat.cast (R := ZMod (2 ^ B))) (f1 xs hc.1)
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at hnot
  unfold wordZMod at *
  rw [hcast]
  linear_combination hnot

def cSub (N0 B : ℕ) (a b : Word B) (gs : List Gate) : List Gate × Word B :=
  let (gs1, nb) := cNotWord N0 B b gs
  let r := cAddCin N0 B a nb 1 gs1
  (r.1, r.2.1)

lemma cSub_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B : ℕ} {a b : Word B}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) (hb : ValidWord N0 gs b) :
    let r := cSub N0 B a b gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 14 * B ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = wordZMod gs xs a - wordZMod gs xs b := by
  dsimp only [cSub]
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNotWord_spec hgs hb
  obtain ⟨v2, e2, l2, w2, _, f2⟩ := cAddCin_spec B (cin := 1) v1 (ha.extends e1) w1 (by omega)
  refine ⟨v2, e1.trans e2, by omega, w2, fun xs hc => ?_⟩
  have hnat := f2 xs hc.1
  rw [wordNat_extends e1 hc.1 ha, wireAt_one hc] at hnat
  simp only [Bool.toNat_true] at hnat
  have hcast := congrArg (Nat.cast (R := ZMod (2 ^ B))) hnat
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_self, zero_mul, add_zero] at hcast
  have hnot := congrArg (Nat.cast (R := ZMod (2 ^ B))) (f1 xs hc.1)
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at hnot
  unfold wordZMod at *
  rw [hcast]
  linear_combination hnot

def cEqWord (N0 B : ℕ) (a b : Word B) (gs : List Gate) : List Gate × ℕ :=
  let (gs1, eqs) := cBuildFin B (fun i g => cEqBit N0 (a i) (b i) g) gs
  cAndFin N0 B eqs gs1

lemma cEqWord_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B : ℕ} {a b : Word B}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) (hb : ValidWord N0 gs b) :
    let r := cEqWord N0 B a b gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 7 * B ∧
    r.2 < N0 + r.1.length ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      (wireAt r.1 xs r.2 = true ↔ wordNat gs xs a = wordNat gs xs b) := by
  dsimp only [cEqWord]
  have h1 := cBuildFin_spec (N0 := N0) B 6 (fun i g => cEqBit N0 (a i) (b i) g)
    (fun g i w => w < N0 + g.length ∧
      ∀ xs, xs.length = N0 → wireAt g xs w = (wireAt gs xs (a i) == wireAt gs xs (b i)))
    (fun g1 g2 i w he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
      fun xs hlen => by rw [wireAt_extends he (by omega), hf xs hlen]⟩)
    gs hgs
    (fun i g hg he => by
      have helen := he.length_le
      obtain ⟨v1, e1, l1, w1, f1⟩ := cEqBit_spec (a i) (b i) hg (by have := ha i; omega) (by have := hb i; omega)
      exact ⟨v1, e1, l1, w1, fun xs hlen => by
        rw [f1 xs hlen, wireAt_extends he (by have := ha i; omega),
          wireAt_extends he (by have := hb i; omega)]⟩)
  obtain ⟨v2, e2, l2, w2, f2⟩ := cAndFin_spec hN h1.1 (fun i => (h1.2.2.2 i).1)
  refine ⟨v2, h1.2.1.trans e2, by have := h1.2.2.1; nlinarith, w2, fun xs hc => ?_⟩
  rw [f2 xs hc]
  constructor
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro k
    rw [wordNat_testBit, wordNat_testBit]
    by_cases hk : k < B
    · simp only [hk, ↓reduceDIte]
      have hi := hall ⟨k, hk⟩
      rw [(h1.2.2.2 ⟨k, hk⟩).2 xs hc.1, beq_iff_eq] at hi
      exact hi
    · simp [hk]
  · intro heq i
    rw [(h1.2.2.2 i).2 xs hc.1, beq_iff_eq]
    have htb := congrArg (fun m => m.testBit i.val) heq
    rw [wordNat_testBit, wordNat_testBit, dif_pos i.isLt, dif_pos i.isLt] at htb
    exact htb

lemma sum_testBit_two_pow (B v : ℕ) :
    (∑ j : Fin B, (v.testBit j.val).toNat * 2 ^ j.val) = v % 2 ^ B := by
  apply Nat.eq_of_testBit_eq
  intro k
  have h1 : ∀ B' : ℕ, ∀ w : Fin B' → Bool,
      (∑ j : Fin B', (w j).toNat * 2 ^ j.val).testBit k = if h : k < B' then w ⟨k, h⟩ else false := by
    intro B' w
    induction B' generalizing k with
    | zero => simp
    | succ B' ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      have hmul : (∑ i : Fin B', (w i.succ).toNat * (2 ^ i.val * 2)) =
          2 * ∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [hmul]
      cases k with
      | zero =>
        simp only [Nat.zero_lt_succ, ↓reduceDIte]
        change ((w 0).toNat + 2 * ∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val).testBit 0 = w 0
        cases h0 : w 0 <;> simp [Nat.testBit_zero]
      | succ k =>
        have htb : ((w 0).toNat + 2 * ∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val).testBit (k + 1) =
            (∑ i : Fin B', (w i.succ).toNat * 2 ^ i.val).testBit k := by
          rw [Nat.testBit_succ]; congr 1; cases w 0 <;> simp <;> omega
        rw [htb, ih k (fun i => w i.succ)]
        by_cases hk : k < B'
        · simp [hk, show k + 1 < B' + 1 by omega]
        · simp [hk, show ¬ (k + 1 < B' + 1) by omega]
  rw [h1 B (fun j => v.testBit j.val), Nat.testBit_mod_two_pow]
  by_cases hk : k < B <;> simp [hk]

def cMulConst (N0 B : ℕ) (c : ZMod (2 ^ B)) (a : Word B) (gs : List Gate) : List Gate × Word B :=
  cFoldFin B
    (fun j acc g =>
      if c.val.testBit j.val then cAdd N0 B acc (cShiftLeft B j.val a) g else (g, acc))
    (cZeroWord B) gs

lemma cMulConst_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B : ℕ}
    (c : ZMod (2 ^ B)) {a : Word B}
    (hgs : ValidCircuit N0 gs) (ha : ValidWord N0 gs a) :
    let r := cMulConst N0 B c a gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 13 * B * B ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = c * wordZMod gs xs a := by
  dsimp only [cMulConst]
  have hpos : 0 < 2 ^ B := by positivity
  haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hpos⟩
  have h := cFoldFin_spec (N0 := N0) B (13 * B)
    (fun j acc g =>
      if c.val.testBit j.val then cAdd N0 B acc (cShiftLeft B j.val a) g else (g, acc))
    (fun m _ g acc => ValidWord N0 g acc ∧
      ∀ xs, HasConsts xs N0 →
        wordZMod g xs acc =
          (∑ j : Fin B, if j.val < m ∧ c.val.testBit j.val then (2 : ZMod (2 ^ B)) ^ j.val else 0) *
            wordZMod gs xs a)
    (cZeroWord B) gs hgs
    ⟨validWord_cZeroWord hN gs B, fun xs hc => by simp [wordZMod_cZeroWord hc]⟩
    (fun i gs1 acc hv he ⟨hacc, hsem⟩ => by
      have ha1 : ValidWord N0 gs1 a := ha.extends he
      have hsh : ValidWord N0 gs1 (cShiftLeft B i.val a) := validWord_cShiftLeft hN i.val ha1
      cases hbit : c.val.testBit i.val
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨hv, Extends.refl gs1, by omega, hacc, fun xs hc => ?_⟩
        rw [hsem xs hc]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hji : j = i
        · subst hji; simp [hbit]
        · have : j.val ≠ i.val := fun h' => hji (Fin.ext h')
          have : j.val < i.val + 1 ↔ j.val < i.val := by omega
          simp [this]
      · simp only [↓reduceIte]
        obtain ⟨v1, e1, l1, w1, f1⟩ := cAdd_spec hN hv hacc hsh
        refine ⟨v1, e1, l1, w1, fun xs hc => ?_⟩
        rw [f1 xs hc, hsem xs hc, wordZMod_cShiftLeft hc, wordZMod_extends he hc.1 ha]
        rw [← add_mul]
        congr 1
        have hsplit :
            (∑ j : Fin B, if j.val < i.val + 1 ∧ c.val.testBit j.val = true then (2 : ZMod (2 ^ B)) ^ j.val else 0) =
            (∑ j : Fin B, if j.val < i.val ∧ c.val.testBit j.val = true then (2 : ZMod (2 ^ B)) ^ j.val else 0) +
            (2 : ZMod (2 ^ B)) ^ i.val := by
          have hadd : (2 : ZMod (2 ^ B)) ^ i.val =
              ∑ j : Fin B, if j = i then (2 : ZMod (2 ^ B)) ^ j.val else 0 := by simp
          rw [hadd, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hji : j = i
          · subst hji; simp [hbit]
          · have : j.val ≠ i.val := fun h' => hji (Fin.ext h')
            have : j.val < i.val + 1 ↔ j.val < i.val := by omega
            simp [hji, this]
        exact hsplit.symm)
  refine ⟨h.1, h.2.1, by have := h.2.2.1; nlinarith, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc]
  congr 1
  have hsum : (∑ j : Fin B, if j.val < B ∧ c.val.testBit j.val = true then (2 : ZMod (2 ^ B)) ^ j.val else 0) =
      ((∑ j : Fin B, (c.val.testBit j.val).toNat * 2 ^ j.val : ℕ) : ZMod (2 ^ B)) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [j.isLt, true_and]
    cases c.val.testBit j.val <;> simp
  rw [hsum, sum_testBit_two_pow, Nat.mod_eq_of_lt c.val_lt, ZMod.natCast_zmod_val]

def cSumFinWords (N0 B k : ℕ) (ws : Fin k → Word B) (gs : List Gate) : List Gate × Word B :=
  cFoldFin k (fun i acc g => cAdd N0 B acc (ws i) g) (cZeroWord B) gs

lemma cSumFinWords_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B k : ℕ}
    {ws : Fin k → Word B} (hgs : ValidCircuit N0 gs) (hws : ∀ i : Fin k, ValidWord N0 gs (ws i)) :
    let r := cSumFinWords N0 B k ws gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k * (13 * B) ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = ∑ i : Fin k, wordZMod gs xs (ws i) := by
  dsimp only [cSumFinWords]
  have h := cFoldFin_spec (N0 := N0) k (13 * B) (fun i acc g => cAdd N0 B acc (ws i) g)
    (fun m _ g acc => ValidWord N0 g acc ∧
      ∀ xs, HasConsts xs N0 →
        wordZMod g xs acc = ∑ i : Fin k, if i.val < m then wordZMod gs xs (ws i) else 0)
    (cZeroWord B) gs hgs
    ⟨validWord_cZeroWord hN gs B, fun xs hc => by simp [wordZMod_cZeroWord hc]⟩
    (fun i gs1 acc hv he ⟨hacc, hsem⟩ => by
      obtain ⟨v1, e1, l1, w1, f1⟩ := cAdd_spec hN hv hacc ((hws i).extends he)
      refine ⟨v1, e1, l1, w1, fun xs hc => ?_⟩
      rw [f1 xs hc, hsem xs hc, wordZMod_extends he hc.1 (hws i)]
      have hadd : wordZMod gs xs (ws i) = ∑ j : Fin k, if j = i then wordZMod gs xs (ws j) else 0 := by simp
      rw [hadd, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : j = i
      · subst hji; simp
      · have : j.val ≠ i.val := fun h' => hji (Fin.ext h')
        have : j.val < i.val + 1 ↔ j.val < i.val := by omega
        simp [hji, this])
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc]
  refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]

def cLinComb (N0 B k : ℕ) (coeffs : Fin k → ZMod (2 ^ B)) (ws : Fin k → Word B)
    (gs : List Gate) : List Gate × Word B :=
  cFoldFin k
    (fun i acc g =>
      let (g1, prod) := cMulConst N0 B (coeffs i) (ws i) g
      cAdd N0 B acc prod g1)
    (cZeroWord B) gs

lemma cLinComb_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B k : ℕ}
    (coeffs : Fin k → ZMod (2 ^ B)) {ws : Fin k → Word B}
    (hgs : ValidCircuit N0 gs) (hws : ∀ i : Fin k, ValidWord N0 gs (ws i)) :
    let r := cLinComb N0 B k coeffs ws gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k * (13 * B * B + 13 * B) ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = ∑ i : Fin k, coeffs i * wordZMod gs xs (ws i) := by
  dsimp only [cLinComb]
  have h := cFoldFin_spec (N0 := N0) k (13 * B * B + 13 * B)
    (fun i acc g =>
      let (g1, prod) := cMulConst N0 B (coeffs i) (ws i) g
      cAdd N0 B acc prod g1)
    (fun m _ g acc => ValidWord N0 g acc ∧
      ∀ xs, HasConsts xs N0 →
        wordZMod g xs acc = ∑ i : Fin k, if i.val < m then coeffs i * wordZMod gs xs (ws i) else 0)
    (cZeroWord B) gs hgs
    ⟨validWord_cZeroWord hN gs B, fun xs hc => by simp [wordZMod_cZeroWord hc]⟩
    (fun i gs1 acc hv he ⟨hacc, hsem⟩ => by
      obtain ⟨v1, e1, l1, w1, f1⟩ := cMulConst_spec hN (coeffs i) hv ((hws i).extends he)
      obtain ⟨v2, e2, l2, w2, f2⟩ := cAdd_spec hN v1 (hacc.extends e1) w1
      refine ⟨v2, e1.trans e2, by linarith, w2, fun xs hc => ?_⟩
      rw [f2 xs hc, wordZMod_extends e1 hc.1 hacc, hsem xs hc, f1 xs hc, wordZMod_extends he hc.1 (hws i)]
      have hadd : coeffs i * wordZMod gs xs (ws i) =
          ∑ j : Fin k, if j = i then coeffs j * wordZMod gs xs (ws j) else 0 := by simp
      rw [hadd, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hji : j = i
      · subst hji; simp
      · have : j.val ≠ i.val := fun h' => hji (Fin.ext h')
        have : j.val < i.val + 1 ↔ j.val < i.val := by omega
        simp [hji, this])
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc]
  refine Finset.sum_congr rfl fun i _ => by simp [i.isLt]

def cOneHotShiftRight (N0 B1 B2 M : ℕ) (sel : Fin M → ℕ) (a : Word B1)
    (gs : List Gate) : List Gate × Word B2 :=
  cFoldFin M
    (fun k acc g => cMuxWord N0 B2 (sel k) (cShiftRightResize B1 B2 k.val a) acc g)
    (cZeroWord B2) gs

lemma cOneHotShiftRight_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {B1 B2 M : ℕ}
    {sel : Fin M → ℕ} {a : Word B1}
    (hgs : ValidCircuit N0 gs) (hsel : ∀ k : Fin M, sel k < N0 + gs.length)
    (ha : ValidWord N0 gs a) :
    let r := cOneHotShiftRight N0 B1 B2 M sel a gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + M * (4 * B2) ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ (k0 : Fin M),
      (∀ k : Fin M, wireAt gs xs (sel k) = decide (k = k0)) →
      wordNat r.1 xs r.2 = (wordNat gs xs a / 2 ^ k0.val) % 2 ^ B2 := by
  dsimp only [cOneHotShiftRight]
  have h := cFoldFin_spec (N0 := N0) M (4 * B2)
    (fun k acc g => cMuxWord N0 B2 (sel k) (cShiftRightResize B1 B2 k.val a) acc g)
    (fun m _ g acc => ValidWord N0 g acc ∧
      ∀ (xs : List Bool), HasConsts xs N0 → ∀ (k0 : Fin M),
        (∀ k : Fin M, wireAt gs xs (sel k) = decide (k = k0)) →
        wordNat g xs acc = if k0.val < m then (wordNat gs xs a / 2 ^ k0.val) % 2 ^ B2 else 0)
    (cZeroWord B2) gs hgs
    ⟨validWord_cZeroWord hN gs B2, fun xs hc _ _ => by simp [wordNat_cZeroWord hc]⟩
    (fun k gs1 acc hv he ⟨hacc, hsem⟩ => by
      have helen := he.length_le
      have hsh : ValidWord N0 gs1 (cShiftRightResize B1 B2 k.val a) :=
        validWord_cShiftRightResize hN k.val (ha.extends he)
      obtain ⟨v1, e1, l1, w1, f1⟩ := cMuxWord_spec (s := sel k) hv (by have := hsel k; omega) hsh hacc
      refine ⟨v1, e1, l1, w1, fun xs hc k0 hoh => ?_⟩
      rw [f1 xs hc.1, wireAt_extends he (w := sel k) (by rw [hc.1]; exact hsel k), hoh k,
        wordNat_cShiftRightResize hc, wordNat_extends he hc.1 ha, hsem xs hc k0 hoh]
      by_cases hkk : k = k0
      · subst hkk; simp
      · have : k0.val ≠ k.val := fun h' => hkk (Fin.ext h'.symm)
        have : k0.val < k.val + 1 ↔ k0.val < k.val := by omega
        simp [hkk, this])
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun xs hc k0 hoh => ?_⟩
  rw [h.2.2.2.2 xs hc k0 hoh, if_pos k0.isLt]

end CircuitBuilder

noncomputable section Trunc2Circuit

abbrev Trunc2Wire (D1 D2 B : ℕ) := Fin D1 → Fin D2 → Word B

def ValidTrunc2 (N0 : ℕ) (gs : List Gate) {D1 D2 B : ℕ} (P : Trunc2Wire D1 D2 B) : Prop :=
  ∀ (i : Fin D1) (j : Fin D2), ValidWord N0 gs (P i j)

lemma ValidTrunc2.extends {N0 : ℕ} {gs1 gs2 : List Gate} {D1 D2 B : ℕ} {P : Trunc2Wire D1 D2 B}
    (hP : ValidTrunc2 N0 gs1 P) (he : Extends gs1 gs2) : ValidTrunc2 N0 gs2 P :=
  fun i j => (hP i j).extends he

def trunc2Val (gs : List Gate) (xs : List Bool) {D1 D2 B : ℕ} (P : Trunc2Wire D1 D2 B) :
    Trunc2 D1 D2 (ZMod (2 ^ B)) :=
  ⟨fun i j => wordZMod gs xs (P i j)⟩

lemma trunc2Val_extends {N0 : ℕ} {gs1 gs2 : List Gate} {xs : List Bool} {D1 D2 B : ℕ}
    {P : Trunc2Wire D1 D2 B} (he : Extends gs1 gs2) (hlen : xs.length = N0)
    (hP : ValidTrunc2 N0 gs1 P) :
    trunc2Val gs2 xs P = trunc2Val gs1 xs P := by
  apply Trunc2.ext; intro i j
  exact wordZMod_extends he hlen (hP i j)

def cTrunc2One (D1 D2 B : ℕ) : Trunc2Wire D1 D2 B :=
  fun i j => if i.val = 0 ∧ j.val = 0 then cConstWord B 1 else cZeroWord B

lemma validTrunc2_cTrunc2One {N0 : ℕ} (hN : 2 ≤ N0) (gs : List Gate) (D1 D2 B : ℕ) :
    ValidTrunc2 N0 gs (cTrunc2One D1 D2 B) := by
  intro i j; unfold cTrunc2One
  split_ifs
  · exact validWord_cConstWord hN gs B 1
  · exact validWord_cZeroWord hN gs B

lemma trunc2Val_cTrunc2One {N0 : ℕ} {gs : List Gate} {xs : List Bool} (hc : HasConsts xs N0)
    (D1 D2 B : ℕ) :
    trunc2Val gs xs (cTrunc2One D1 D2 B) = 1 := by
  apply Trunc2.ext; intro i j
  change wordZMod gs xs (cTrunc2One D1 D2 B i j) = (1 : Trunc2 D1 D2 (ZMod (2 ^ B))).coeff i j
  rw [Trunc2.coeff_one]; unfold cTrunc2One
  split_ifs
  · rw [wordZMod_cConstWord hc]; simp
  · exact wordZMod_cZeroWord hc B

def cTrunc2Mux (N0 D1 D2 B : ℕ) (s : ℕ) (P1 P2 : Trunc2Wire D1 D2 B) (gs : List Gate) :
    List Gate × Trunc2Wire D1 D2 B :=
  cBuildFin D1 (fun i g1 => cBuildFin D2 (fun j g2 => cMuxWord N0 B s (P1 i j) (P2 i j) g2) g1) gs

lemma cTrunc2Mux_spec {N0 : ℕ} {gs : List Gate} {D1 D2 B s : ℕ}
    {P1 P2 : Trunc2Wire D1 D2 B}
    (hgs : ValidCircuit N0 gs) (hs : s < N0 + gs.length)
    (hP1 : ValidTrunc2 N0 gs P1) (hP2 : ValidTrunc2 N0 gs P2) :
    let r := cTrunc2Mux N0 D1 D2 B s P1 P2 gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + D1 * (D2 * (4 * B)) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ xs : List Bool, xs.length = N0 →
      trunc2Val r.1 xs r.2 = if wireAt gs xs s then trunc2Val gs xs P1 else trunc2Val gs xs P2 := by
  dsimp only [cTrunc2Mux]
  have h := cBuildFin_spec (N0 := N0) D1 (D2 * (4 * B))
    (fun i g1 => cBuildFin D2 (fun j g2 => cMuxWord N0 B s (P1 i j) (P2 i j) g2) g1)
    (fun g i row => (∀ j : Fin D2, ValidWord N0 g (row j)) ∧
      ∀ xs, xs.length = N0 → ∀ j : Fin D2,
        wordZMod g xs (row j) = if wireAt gs xs s then wordZMod gs xs (P1 i j) else wordZMod gs xs (P2 i j))
    (fun g1 g2 i row he ⟨hv, hf⟩ => ⟨fun j => (hv j).extends he, fun xs hlen j => by
      rw [wordZMod_extends he hlen (hv j), hf xs hlen j]⟩)
    gs hgs
    (fun i g1 hg1 he1 => by
      have h2 := cBuildFin_spec (N0 := N0) D2 (4 * B)
        (fun j g2 => cMuxWord N0 B s (P1 i j) (P2 i j) g2)
        (fun g j w => ValidWord N0 g w ∧
          ∀ xs, xs.length = N0 →
            wordZMod g xs w = if wireAt gs xs s then wordZMod gs xs (P1 i j) else wordZMod gs xs (P2 i j))
        (fun g2 g3 j w he ⟨hv, hf⟩ => ⟨hv.extends he, fun xs hlen => by
          rw [wordZMod_extends he hlen hv, hf xs hlen]⟩)
        g1 hg1
        (fun j g2 hg2 he2 => by
          have he12 : Extends gs g2 := he1.trans he2
          have helen := he12.length_le
          obtain ⟨v1, e1, l1, w1, f1⟩ := cMuxWord_spec (s := s) hg2 (by omega) ((hP1 i j).extends he12) ((hP2 i j).extends he12)
          refine ⟨v1, e1, l1, w1, fun xs hlen => ?_⟩
          unfold wordZMod
          rw [f1 xs hlen, wireAt_extends he12 (w := s) (by rw [hlen]; exact hs),
            wordNat_extends he12 hlen (hP1 i j), wordNat_extends he12 hlen (hP2 i j)]
          split_ifs <;> rfl)
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun j => (h2.2.2.2 j).1, fun xs hlen j => (h2.2.2.2 j).2 xs hlen⟩)
  refine ⟨h.1, h.2.1, h.2.2.1, fun i j => (h.2.2.2 i).1 j, fun xs hlen => ?_⟩
  apply Trunc2.ext; intro i j
  change wordZMod _ xs _ = _
  rw [(h.2.2.2 i).2 xs hlen j]
  split_ifs <;> rfl

lemma trunc2_coeff_mul_sub {D1 D2 : ℕ} {R : Type*} [CommRing R] (C A : Trunc2 D1 D2 R)
    (i : Fin D1) (j : Fin D2) :
    (C * A).coeff i j =
      ∑ i1 : Fin D1, ∑ j1 : Fin D2,
        if h : i1.val ≤ i.val ∧ j1.val ≤ j.val then
          C.coeff i1 j1 * A.coeff ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩
        else 0 := by
  rw [Trunc2.coeff_mul]
  refine Finset.sum_congr rfl fun i1 _ => ?_
  have hswap :
      (∑ i2 : Fin D1, ∑ j1 : Fin D2, ∑ j2 : Fin D2,
        if i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val then C.coeff i1 j1 * A.coeff i2 j2 else 0) =
      ∑ j1 : Fin D2, ∑ i2 : Fin D1, ∑ j2 : Fin D2,
        if i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val then C.coeff i1 j1 * A.coeff i2 j2 else 0 :=
    Finset.sum_comm
  rw [hswap]
  refine Finset.sum_congr rfl fun j1 _ => ?_
  by_cases h : i1.val ≤ i.val ∧ j1.val ≤ j.val
  · rw [dif_pos h]
    have hi2 : i.val - i1.val < D1 := by have := i.isLt; omega
    have hj2 : j.val - j1.val < D2 := by have := j.isLt; omega
    rw [Finset.sum_eq_single ⟨i.val - i1.val, hi2⟩]
    · rw [Finset.sum_eq_single ⟨j.val - j1.val, hj2⟩]
      · simp [Nat.add_sub_of_le h.1, Nat.add_sub_of_le h.2]
      · intro j2 _ hne
        have : j1.val + j2.val ≠ j.val := by have : j2.val ≠ j.val - j1.val := fun h' => hne (Fin.ext h'); omega
        simp [this]
      · intro h0; exact absurd (Finset.mem_univ _) h0
    · intro i2 _ hne
      refine Finset.sum_eq_zero fun j2 _ => ?_
      have : i1.val + i2.val ≠ i.val := by have : i2.val ≠ i.val - i1.val := fun h' => hne (Fin.ext h'); omega
      simp [this]
    · intro h0; exact absurd (Finset.mem_univ _) h0
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun i2 _ => Finset.sum_eq_zero fun j2 _ => ?_
    have : ¬ (i1.val + i2.val = i.val ∧ j1.val + j2.val = j.val) := by omega
    simp [this]

def cTrunc2MulEntry (N0 D1 D2 B : ℕ) (C : Trunc2 D1 D2 (ZMod (2 ^ B)))
    (A : Trunc2Wire D1 D2 B) (i : Fin D1) (j : Fin D2) (gs : List Gate) : List Gate × Word B :=
  cFoldFin D1 (fun i1 acc1 g1 =>
    if h1 : i1.val ≤ i.val then
      cFoldFin D2 (fun j1 acc2 g2 =>
        if h2 : j1.val ≤ j.val then
          let (g3, prod) := cMulConst N0 B (C.coeff i1 j1)
            (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩) g2
          cAdd N0 B acc2 prod g3
        else (g2, acc2)) acc1 g1
    else (g1, acc1)) (cZeroWord B) gs

lemma cTrunc2MulEntry_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {D1 D2 B : ℕ}
    (C : Trunc2 D1 D2 (ZMod (2 ^ B))) {A : Trunc2Wire D1 D2 B}
    (i : Fin D1) (j : Fin D2) (hgs : ValidCircuit N0 gs) (hA : ValidTrunc2 N0 gs A) :
    let r := cTrunc2MulEntry N0 D1 D2 B C A i j gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + D1 * (D2 * (13 * B * B + 13 * B)) ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      wordZMod r.1 xs r.2 = (C * trunc2Val gs xs A).coeff i j := by
  dsimp only [cTrunc2MulEntry]
  have h := cFoldFin_spec (N0 := N0) D1 (D2 * (13 * B * B + 13 * B))
    (fun i1 acc1 g1 =>
      if h1 : i1.val ≤ i.val then
        cFoldFin D2 (fun j1 acc2 g2 =>
          if h2 : j1.val ≤ j.val then
            let (g3, prod) := cMulConst N0 B (C.coeff i1 j1)
              (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩) g2
            cAdd N0 B acc2 prod g3
          else (g2, acc2)) acc1 g1
      else (g1, acc1))
    (fun m1 _ g acc1 => ValidWord N0 g acc1 ∧
      ∀ xs, HasConsts xs N0 →
        wordZMod g xs acc1 =
          ∑ i1 : Fin D1, if i1.val < m1 then
            ∑ j1 : Fin D2,
              if hh : i1.val ≤ i.val ∧ j1.val ≤ j.val then
                C.coeff i1 j1 * wordZMod gs xs (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩)
              else 0
          else 0)
    (cZeroWord B) gs hgs
    ⟨validWord_cZeroWord hN gs B, fun xs hc => by simp [wordZMod_cZeroWord hc]⟩
    (fun i1 gs1 acc1 hv1 he1 ⟨hacc1, hsem1⟩ => by
      by_cases h1 : i1.val ≤ i.val
      · simp only [h1, ↓reduceDIte]
        have h2 := cFoldFin_spec (N0 := N0) D2 (13 * B * B + 13 * B)
          (fun j1 acc2 g2 =>
            if h2 : j1.val ≤ j.val then
              let (g3, prod) := cMulConst N0 B (C.coeff i1 j1)
                (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩) g2
              cAdd N0 B acc2 prod g3
            else (g2, acc2))
          (fun m2 _ g acc2 => ValidWord N0 g acc2 ∧
            ∀ xs, HasConsts xs N0 →
              wordZMod g xs acc2 = wordZMod gs1 xs acc1 +
                ∑ j1 : Fin D2, if j1.val < m2 then
                  if h2 : j1.val ≤ j.val then
                    C.coeff i1 j1 * wordZMod gs xs (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩)
                  else 0
                else 0)
          acc1 gs1 hv1
          ⟨hacc1, fun xs _ => by simp⟩
          (fun j1 gs2 acc2 hv2 he2 ⟨hacc2, hsem2⟩ => by
            by_cases h2 : j1.val ≤ j.val
            · simp only [h2, ↓reduceDIte]
              have he12 : Extends gs gs2 := he1.trans he2
              obtain ⟨v3, e3, l3, w3, f3⟩ := cMulConst_spec hN (C.coeff i1 j1) hv2
                ((hA ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩).extends he12)
              obtain ⟨v4, e4, l4, w4, f4⟩ := cAdd_spec hN v3 (hacc2.extends e3) w3
              refine ⟨v4, e3.trans e4, by linarith, w4, fun xs hc => ?_⟩
              rw [f4 xs hc, wordZMod_extends e3 hc.1 hacc2, hsem2 xs hc, f3 xs hc,
                wordZMod_extends he12 hc.1 (hA _ _), add_assoc]
              congr 1
              have hadd : C.coeff i1 j1 * wordZMod gs xs (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩) =
                  ∑ j' : Fin D2, if j' = j1 then
                    if h2' : j'.val ≤ j.val then
                      C.coeff i1 j' * wordZMod gs xs (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j'.val, by omega⟩)
                    else 0
                  else 0 := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, h2, ↓reduceDIte]
              rw [hadd, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun j' _ => ?_
              by_cases hj' : j' = j1
              · subst hj'; simp
              · have : j'.val ≠ j1.val := fun h' => hj' (Fin.ext h')
                have : j'.val < j1.val + 1 ↔ j'.val < j1.val := by omega
                simp [hj', this]
            · simp only [h2, ↓reduceDIte]
              refine ⟨hv2, Extends.refl gs2, by omega, hacc2, fun xs hc => ?_⟩
              rw [hsem2 xs hc]
              congr 1
              refine Finset.sum_congr rfl fun j' _ => ?_
              by_cases hj' : j' = j1
              · subst hj'; simp [h2]
              · have : j'.val ≠ j1.val := fun h' => hj' (Fin.ext h')
                have : j'.val < j1.val + 1 ↔ j'.val < j1.val := by omega
                simp [this])
        refine ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, fun xs hc => ?_⟩
        rw [h2.2.2.2.2 xs hc, hsem1 xs hc]
        have hadd : (∑ j1 : Fin D2, if j1.val < D2 then
              if h2 : j1.val ≤ j.val then
                C.coeff i1 j1 * wordZMod gs xs (A ⟨i.val - i1.val, by omega⟩ ⟨j.val - j1.val, by omega⟩)
              else 0
            else 0) =
            ∑ i' : Fin D1, if i' = i1 then
              ∑ j1 : Fin D2,
                if hh : i'.val ≤ i.val ∧ j1.val ≤ j.val then
                  C.coeff i' j1 * wordZMod gs xs (A ⟨i.val - i'.val, by omega⟩ ⟨j.val - j1.val, by omega⟩)
                else 0
            else 0 := by
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          refine Finset.sum_congr rfl fun j1 _ => by simp [j1.isLt, h1]
        rw [hadd, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases hi' : i' = i1
        · subst hi'; simp
        · have : i'.val ≠ i1.val := fun h' => hi' (Fin.ext h')
          have : i'.val < i1.val + 1 ↔ i'.val < i1.val := by omega
          simp [hi', this]
      · simp only [h1, ↓reduceDIte]
        refine ⟨hv1, Extends.refl gs1, by omega, hacc1, fun xs hc => ?_⟩
        rw [hsem1 xs hc]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases hi' : i' = i1
        · subst hi'; simp [h1]
        · have : i'.val ≠ i1.val := fun h' => hi' (Fin.ext h')
          have : i'.val < i1.val + 1 ↔ i'.val < i1.val := by omega
          simp [this])
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc, trunc2_coeff_mul_sub]
  refine Finset.sum_congr rfl fun i1 _ => by simp [i1.isLt]; rfl

def cTrunc2MulConst (N0 D1 D2 B : ℕ) (C : Trunc2 D1 D2 (ZMod (2 ^ B)))
    (A : Trunc2Wire D1 D2 B) (gs : List Gate) : List Gate × Trunc2Wire D1 D2 B :=
  cBuildFin D1 (fun i g1 => cBuildFin D2 (fun j g2 => cTrunc2MulEntry N0 D1 D2 B C A i j g2) g1) gs

lemma cTrunc2MulConst_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {D1 D2 B : ℕ}
    (C : Trunc2 D1 D2 (ZMod (2 ^ B))) {A : Trunc2Wire D1 D2 B}
    (hgs : ValidCircuit N0 gs) (hA : ValidTrunc2 N0 gs A) :
    let r := cTrunc2MulConst N0 D1 D2 B C A gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + D1 * (D2 * (D1 * (D2 * (13 * B * B + 13 * B)))) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      trunc2Val r.1 xs r.2 = C * trunc2Val gs xs A := by
  dsimp only [cTrunc2MulConst]
  have h := cBuildFin_spec (N0 := N0) D1 (D2 * (D1 * (D2 * (13 * B * B + 13 * B))))
    (fun i g1 => cBuildFin D2 (fun j g2 => cTrunc2MulEntry N0 D1 D2 B C A i j g2) g1)
    (fun g i row => (∀ j : Fin D2, ValidWord N0 g (row j)) ∧
      ∀ xs, HasConsts xs N0 → ∀ j : Fin D2, wordZMod g xs (row j) = (C * trunc2Val gs xs A).coeff i j)
    (fun g1 g2 i row he ⟨hv, hf⟩ => ⟨fun j => (hv j).extends he, fun xs hc j => by
      rw [wordZMod_extends he hc.1 (hv j), hf xs hc j]⟩)
    gs hgs
    (fun i g1 hg1 he1 => by
      have h2 := cBuildFin_spec (N0 := N0) D2 (D1 * (D2 * (13 * B * B + 13 * B)))
        (fun j g2 => cTrunc2MulEntry N0 D1 D2 B C A i j g2)
        (fun g j w => ValidWord N0 g w ∧
          ∀ xs, HasConsts xs N0 → wordZMod g xs w = (C * trunc2Val gs xs A).coeff i j)
        (fun g2 g3 j w he ⟨hv, hf⟩ => ⟨hv.extends he, fun xs hc => by
          rw [wordZMod_extends he hc.1 hv, hf xs hc]⟩)
        g1 hg1
        (fun j g2 hg2 he2 => by
          have he12 : Extends gs g2 := he1.trans he2
          obtain ⟨v1, e1, l1, w1, f1⟩ := cTrunc2MulEntry_spec hN C i j hg2 (hA.extends he12)
          refine ⟨v1, e1, l1, w1, fun xs hc => ?_⟩
          rw [f1 xs hc, trunc2Val_extends he12 hc.1 hA])
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun j => (h2.2.2.2 j).1, fun xs hc j => (h2.2.2.2 j).2 xs hc⟩)
  refine ⟨h.1, h.2.1, h.2.2.1, fun i j => (h.2.2.2 i).1 j, fun xs hc => ?_⟩
  apply Trunc2.ext; intro i j
  exact (h.2.2.2 i).2 xs hc j

def cTrunc2MulPowConst (N0 D1 D2 B K : ℕ) (base : Trunc2 D1 D2 (ZMod (2 ^ B)))
    (expBits : Word K) (A : Trunc2Wire D1 D2 B) (gs : List Gate) : List Gate × Trunc2Wire D1 D2 B :=
  cFoldFin K (fun k acc g =>
    let (g1, prod) := cTrunc2MulConst N0 D1 D2 B (base ^ (2 ^ k.val)) acc g
    cTrunc2Mux N0 D1 D2 B (expBits k) prod acc g1) A gs

lemma cTrunc2MulPowConst_spec {N0 : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {D1 D2 B K : ℕ}
    (base : Trunc2 D1 D2 (ZMod (2 ^ B))) {expBits : Word K} {A : Trunc2Wire D1 D2 B}
    (hgs : ValidCircuit N0 gs) (hexp : ValidWord N0 gs expBits) (hA : ValidTrunc2 N0 gs A) :
    let r := cTrunc2MulPowConst N0 D1 D2 B K base expBits A gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + K * (D1 * (D2 * (D1 * (D2 * (13 * B * B + 13 * B)))) + D1 * (D2 * (4 * B))) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ xs : List Bool, HasConsts xs N0 →
      trunc2Val r.1 xs r.2 = base ^ (wordNat gs xs expBits) * trunc2Val gs xs A := by
  dsimp only [cTrunc2MulPowConst]
  have h := cFoldFin_spec (N0 := N0) K
    (D1 * (D2 * (D1 * (D2 * (13 * B * B + 13 * B)))) + D1 * (D2 * (4 * B)))
    (fun k acc g =>
      let (g1, prod) := cTrunc2MulConst N0 D1 D2 B (base ^ (2 ^ k.val)) acc g
      cTrunc2Mux N0 D1 D2 B (expBits k) prod acc g1)
    (fun m _ g acc => ValidTrunc2 N0 g acc ∧
      ∀ xs, HasConsts xs N0 →
        trunc2Val g xs acc =
          base ^ (∑ k : Fin K, if k.val < m then (wireAt gs xs (expBits k)).toNat * 2 ^ k.val else 0) *
            trunc2Val gs xs A)
    A gs hgs
    ⟨hA, fun xs _ => by simp⟩
    (fun k gs1 acc hv1 he1 ⟨hacc, hsem⟩ => by
      obtain ⟨v1, e1, l1, w1, f1⟩ := cTrunc2MulConst_spec hN (base ^ (2 ^ k.val)) hv1 hacc
      have he12 : Extends gs (cTrunc2MulConst N0 D1 D2 B (base ^ (2 ^ k.val)) acc gs1).1 := he1.trans e1
      have hsel : expBits k < N0 + (cTrunc2MulConst N0 D1 D2 B (base ^ (2 ^ k.val)) acc gs1).1.length :=
        lt_of_lt_of_le (hexp k) (Nat.add_le_add_left he12.length_le N0)
      obtain ⟨v2, e2, l2, w2, f2⟩ := cTrunc2Mux_spec v1 hsel w1 (hacc.extends e1)
      refine ⟨v2, e1.trans e2, by linarith, w2, fun xs hc => ?_⟩
      rw [f2 xs hc.1, wireAt_extends he12 (w := expBits k) (by rw [hc.1]; exact hexp k),
        f1 xs hc, trunc2Val_extends e1 hc.1 hacc, hsem xs hc]
      have hsum_step :
          (∑ j : Fin K, if j.val < k.val + 1 then (wireAt gs xs (expBits j)).toNat * 2 ^ j.val else 0) =
          (∑ j : Fin K, if j.val < k.val then (wireAt gs xs (expBits j)).toNat * 2 ^ j.val else 0) +
          (wireAt gs xs (expBits k)).toNat * 2 ^ k.val := by
        have hadd : (wireAt gs xs (expBits k)).toNat * 2 ^ k.val =
            ∑ j : Fin K, if j = k then (wireAt gs xs (expBits j)).toNat * 2 ^ j.val else 0 := by simp
        rw [hadd, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hjk : j = k
        · subst hjk; simp
        · have : j.val ≠ k.val := fun h' => hjk (Fin.ext h')
          have : j.val < k.val + 1 ↔ j.val < k.val := by omega
          simp [hjk, this]
      rw [hsum_step, pow_add]
      cases wireAt gs xs (expBits k)
      · simp
      · simp only [↓reduceIte, Bool.toNat_true, one_mul]
        ring)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun xs hc => ?_⟩
  rw [h.2.2.2.2 xs hc]
  congr 2
  unfold wordNat
  refine Finset.sum_congr rfl fun k _ => by simp [k.isLt]

lemma trunc2_mul_congr_lt {D1 D2 : ℕ} {R : Type*} [CommRing R] (k : ℕ)
    (C A B : Trunc2 D1 D2 R)
    (hAB : ∀ (i : Fin D1), i.val < k → ∀ j : Fin D2, A.coeff i j = B.coeff i j) :
    ∀ (i : Fin D1), i.val < k → ∀ j : Fin D2, (C * A).coeff i j = (C * B).coeff i j := by
  intro i hi j
  rw [Trunc2.coeff_mul, Trunc2.coeff_mul]
  refine Finset.sum_congr rfl fun i1 _ => Finset.sum_congr rfl fun i2 _ =>
    Finset.sum_congr rfl fun j1 _ => Finset.sum_congr rfl fun j2 _ => ?_
  split_ifs with hc
  · rw [hAB i2 (by omega) j2]
  · rfl

def cDecodeSignedStep (N0 D2Z D1U D2U B K : ℕ) (hB : 2 ≤ B)
    (f_zt : Trunc2 3 D2Z (ZMod (2 ^ B))) (f_uv : Trunc2 D1U D2U (ZMod (2 ^ B)))
    (cWord : Word B) (R : Trunc2Wire 3 D2Z B) (Puv : Trunc2Wire D1U D2U B)
    (gs : List Gate) : List Gate × Trunc2Wire 3 D2Z B × Trunc2Wire D1U D2U B :=
  let isNeg := cWord ⟨B - 1, by omega⟩
  let (g1, negC) := cNeg N0 B cWord gs
  let (g2, absW) := cMuxWord N0 B isNeg negC cWord g1
  let (g3, posW) := cMuxWord N0 B isNeg (cZeroWord B) absW g2
  let (g4, negW) := cMuxWord N0 B isNeg absW (cZeroWord B) g3
  let posK := cShiftRightResize B K 0 posW
  let negK := cShiftRightResize B K 0 negW
  let (g5, R1) := cTrunc2MulPowConst N0 3 D2Z B K (Trunc2.invOneSub f_zt) posK R g4
  let (g6, R2) := cTrunc2MulPowConst N0 3 D2Z B K (1 - f_zt) negK R1 g5
  let (g7, P1) := cTrunc2MulPowConst N0 D1U D2U B K (1 - f_uv) posK Puv g6
  let (g8, P2) := cTrunc2MulPowConst N0 D1U D2U B K (Trunc2.invOneSub f_uv) negK P1 g7
  (g8, R2, P2)

lemma cDecodeSignedStep_spec {N0 D2Z D1U D2U B K : ℕ} (hN : 2 ≤ N0) (hB : 2 ≤ B)
    (f_zt : Trunc2 3 D2Z (ZMod (2 ^ B))) (f_uv : Trunc2 D1U D2U (ZMod (2 ^ B)))
    {cWord : Word B} {R : Trunc2Wire 3 D2Z B} {Puv : Trunc2Wire D1U D2U B} {gs : List Gate}
    (hgs : ValidCircuit N0 gs) (hcw : ValidWord N0 gs cWord)
    (hR : ValidTrunc2 N0 gs R) (hP : ValidTrunc2 N0 gs Puv) :
    let costZT := K * (3 * (D2Z * (3 * (D2Z * (13 * B * B + 13 * B)))) + 3 * (D2Z * (4 * B)))
    let costUV := K * (D1U * (D2U * (D1U * (D2U * (13 * B * B + 13 * B)))) + D1U * (D2U * (4 * B)))
    let r := cDecodeSignedStep N0 D2Z D1U D2U B K hB f_zt f_uv cWord R Puv gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 26 * B + 2 * costZT + 2 * costUV ∧
    ValidTrunc2 N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ (c : ℤ),
      wordZMod gs xs cWord = (c : ZMod (2 ^ B)) →
      -(2 ^ (B - 1) : ℤ) < c → c < 2 ^ (B - 1) → c.natAbs < 2 ^ K →
      trunc2Val r.1 xs r.2.1 = Trunc2.zpowOneSub f_zt (-c) * trunc2Val gs xs R ∧
      trunc2Val r.1 xs r.2.2 = Trunc2.zpowOneSub f_uv c * trunc2Val gs xs Puv := by
  intro costZT costUV
  dsimp only [cDecodeSignedStep]
  set isNeg := cWord ⟨B - 1, by omega⟩
  set r1 := cNeg N0 B cWord gs with hr1
  set r2 := cMuxWord N0 B isNeg r1.2 cWord r1.1 with hr2
  set r3 := cMuxWord N0 B isNeg (cZeroWord B) r2.2 r2.1 with hr3
  set r4 := cMuxWord N0 B isNeg r2.2 (cZeroWord B) r3.1 with hr4
  set posK := cShiftRightResize B K 0 r3.2
  set negK := cShiftRightResize B K 0 r4.2
  set r5 := cTrunc2MulPowConst N0 3 D2Z B K (Trunc2.invOneSub f_zt) posK R r4.1 with hr5
  set r6 := cTrunc2MulPowConst N0 3 D2Z B K (1 - f_zt) negK r5.2 r5.1 with hr6
  set r7 := cTrunc2MulPowConst N0 D1U D2U B K (1 - f_uv) posK Puv r6.1 with hr7
  set r8 := cTrunc2MulPowConst N0 D1U D2U B K (Trunc2.invOneSub f_uv) negK r7.2 r7.1 with hr8
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNeg_spec hN hgs hcw
  rw [← hr1] at v1 e1 l1 w1 f1
  have his1 : isNeg < N0 + r1.1.length := lt_of_lt_of_le (hcw _) (Nat.add_le_add_left e1.length_le N0)
  obtain ⟨v2, e2, l2, w2, f2⟩ := cMuxWord_spec v1 his1 w1 (hcw.extends e1)
  rw [← hr2] at v2 e2 l2 w2 f2
  have his2 : isNeg < N0 + r2.1.length := lt_of_lt_of_le his1 (Nat.add_le_add_left e2.length_le N0)
  obtain ⟨v3, e3, l3, w3, f3⟩ := cMuxWord_spec v2 his2 (validWord_cZeroWord hN r2.1 B) w2
  rw [← hr3] at v3 e3 l3 w3 f3
  have his3 : isNeg < N0 + r3.1.length := lt_of_lt_of_le his2 (Nat.add_le_add_left e3.length_le N0)
  obtain ⟨v4, e4, l4, w4, f4⟩ := cMuxWord_spec v3 his3 (w2.extends e3) (validWord_cZeroWord hN r3.1 B)
  rw [← hr4] at v4 e4 l4 w4 f4
  have e14 : Extends gs r4.1 := e1.trans (e2.trans (e3.trans e4))
  have hposK : ValidWord N0 r4.1 posK := validWord_cShiftRightResize hN 0 (w3.extends e4)
  have hnegK : ValidWord N0 r4.1 negK := validWord_cShiftRightResize hN 0 w4
  obtain ⟨v5, e5, l5, w5, f5⟩ := cTrunc2MulPowConst_spec hN (Trunc2.invOneSub f_zt) v4 hposK (hR.extends e14)
  rw [← hr5] at v5 e5 l5 w5 f5
  obtain ⟨v6, e6, l6, w6, f6⟩ := cTrunc2MulPowConst_spec hN (1 - f_zt) v5 (hnegK.extends e5) w5
  rw [← hr6] at v6 e6 l6 w6 f6
  obtain ⟨v7, e7, l7, w7, f7⟩ := cTrunc2MulPowConst_spec hN (1 - f_uv) v6 (hposK.extends (e5.trans e6)) (hP.extends (e14.trans (e5.trans e6)))
  rw [← hr7] at v7 e7 l7 w7 f7
  obtain ⟨v8, e8, l8, w8, f8⟩ := cTrunc2MulPowConst_spec hN (Trunc2.invOneSub f_uv) v7 (hnegK.extends (e5.trans (e6.trans e7))) w7
  rw [← hr8] at v8 e8 l8 w8 f8
  refine ⟨v8, e14.trans (e5.trans (e6.trans (e7.trans e8))), by dsimp only [costZT, costUV]; linarith,
    w6.extends (e7.trans e8), w8, fun xs hc c hcwVal hcl hcu hca => ?_⟩
  obtain ⟨hbit, habs, _⟩ := decode_signed_zmod hB c ⟨hcl, hcu⟩
  have hzval : (wordZMod gs xs cWord).val = wordNat gs xs cWord := wordZMod_val gs xs cWord
  have hisNeg_val : wireAt gs xs isNeg = decide (c < 0) := by
    have htb := wordNat_testBit gs xs cWord (B - 1)
    rw [dif_pos (by omega)] at htb
    rw [← htb, ← hzval, hcwVal]
    exact hbit
  have hnegC_nat : wordNat r1.1 xs r1.2 = (-(c : ZMod (2 ^ B))).val := by
    rw [← wordZMod_val, f1 xs hc, hcwVal]
  have habs_nat : wordNat r2.1 xs r2.2 = c.natAbs := by
    rw [f2 xs hc.1, wireAt_extends e1 (w := isNeg) (by rw [hc.1]; exact hcw _), hisNeg_val,
      wordNat_extends e1 hc.1 hcw, hnegC_nat, ← hzval, hcwVal]
    by_cases hneg : c < 0
    · simp only [hneg, decide_true, ↓reduceIte] at habs ⊢; exact habs
    · simp only [hneg, decide_false, Bool.false_eq_true, ↓reduceIte] at habs ⊢; exact habs
  have hpos_nat : wordNat r4.1 xs posK = if c < 0 then 0 else c.natAbs := by
    rw [wordNat_cShiftRightResize hc, pow_zero, Nat.div_one, wordNat_extends e4 hc.1 w3,
      f3 xs hc.1, wireAt_extends (e1.trans e2) (w := isNeg) (by rw [hc.1]; exact hcw _),
      hisNeg_val, wordNat_cZeroWord hc, habs_nat]
    by_cases hneg : c < 0
    · simp [hneg]
    · simp [hneg, Nat.mod_eq_of_lt hca]
  have hneg_nat : wordNat r4.1 xs negK = if c < 0 then c.natAbs else 0 := by
    rw [wordNat_cShiftRightResize hc, pow_zero, Nat.div_one,
      f4 xs hc.1, wireAt_extends (e1.trans (e2.trans e3)) (w := isNeg) (by rw [hc.1]; exact hcw _),
      hisNeg_val, wordNat_extends e3 hc.1 w2, wordNat_cZeroWord hc, habs_nat]
    by_cases hneg : c < 0
    · simp [hneg, Nat.mod_eq_of_lt hca]
    · simp [hneg]
  have hR_val : trunc2Val r8.1 xs r6.2 =
      (1 - f_zt) ^ (if c < 0 then c.natAbs else 0) *
      (Trunc2.invOneSub f_zt) ^ (if c < 0 then 0 else c.natAbs) * trunc2Val gs xs R := by
    rw [trunc2Val_extends (e7.trans e8) hc.1 w6, f6 xs hc, f5 xs hc,
      wordNat_extends e5 hc.1 hnegK, hneg_nat, hpos_nat, trunc2Val_extends e14 hc.1 hR, mul_assoc]
  have hP_val : trunc2Val r8.1 xs r8.2 =
      (Trunc2.invOneSub f_uv) ^ (if c < 0 then c.natAbs else 0) *
      (1 - f_uv) ^ (if c < 0 then 0 else c.natAbs) * trunc2Val gs xs Puv := by
    rw [f8 xs hc, f7 xs hc, wordNat_extends (e5.trans (e6.trans e7)) hc.1 hnegK,
      wordNat_extends (e5.trans e6) hc.1 hposK, hneg_nat, hpos_nat,
      trunc2Val_extends (e14.trans (e5.trans e6)) hc.1 hP, mul_assoc]
  rw [hR_val, hP_val]
  unfold Trunc2.zpowOneSub
  by_cases hneg : c < 0
  · have hpos_neg : 0 ≤ -c := by omega
    have hnot_pos : ¬ (0 ≤ c) := by omega
    have hto : (-c).toNat = c.natAbs := by omega
    simp only [hneg, hpos_neg, hnot_pos, ↓reduceIte, pow_zero, mul_one, one_mul, hto, and_self]
  · by_cases hz : c = 0
    · subst hz; simp
    · have hpos_c : 0 ≤ c := by omega
      have hnot_neg : ¬ (0 ≤ -c) := by omega
      have hto : c.toNat = c.natAbs := by omega
      have hto2 : (-(-c)).toNat = c.natAbs := by omega
      simp only [hneg, hpos_c, hnot_neg, ↓reduceIte, pow_zero, one_mul, hto, hto2, and_self]

end Trunc2Circuit

section GraphClosureCircuit

def cArcStepWire (N0 n : ℕ) (perm : Fin n → Fin n → ℕ) (mask0 mask1 : Fin n → ℕ)
    (u v : Fin (2 * n)) (gs : List Gate) : List Gate × ℕ :=
  if hu : u.val < n then
    if v.val = n + u.val then cNot N0 (mask0 ⟨u.val, hu⟩) gs else (gs, 0)
  else
    if hv : v.val < n then
      let (g1, nm) := cNot N0 (mask1 ⟨v.val, hv⟩) gs
      cAnd N0 (perm ⟨u.val - n, by omega⟩ ⟨v.val, hv⟩) nm g1
    else (gs, 0)

lemma cArcStepWire_spec {N0 n : ℕ} (hN : 2 ≤ N0) {gs : List Gate}
    {perm : Fin n → Fin n → ℕ} {mask0 mask1 : Fin n → ℕ}
    (u v : Fin (2 * n)) (hgs : ValidCircuit N0 gs)
    (hperm : ∀ i j, perm i j < N0 + gs.length)
    (hm0 : ∀ i, mask0 i < N0 + gs.length) (hm1 : ∀ i, mask1 i < N0 + gs.length) :
    let r := cArcStepWire N0 n perm mask0 mask1 u v gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 2 ∧
    r.2 < N0 + r.1.length ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ i j, wireAt gs xs (perm i j) = decide (σ i = j)) →
      (∀ i, wireAt gs xs (mask0 i) = (p (false, i)).isSome) →
      (∀ i, wireAt gs xs (mask1 i) = (p (true, i)).isSome) →
      wireAt r.1 xs r.2 = decide (qE σ p (edgeEquiv n u) = none ∧ edgeEquiv n v = nextE σ (edgeEquiv n u)) := by
  dsimp only [cArcStepWire]
  by_cases hu : u.val < n
  · simp only [hu, ↓reduceDIte]
    by_cases hv : v.val = n + u.val
    · simp only [hv, ↓reduceIte]
      obtain ⟨v1, e1, l1, w1, f1⟩ := cNot_spec (mask0 ⟨u.val, hu⟩) hgs (hm0 ⟨u.val, hu⟩)
      refine ⟨v1, e1, by omega, w1, fun xs hc σ p _ hpm0 _ => ?_⟩
      rw [f1 xs hc.1, hpm0 ⟨u.val, hu⟩]
      have hvu : ¬ (v.val < n) := by omega
      have hsub : v.val - n = u.val := by omega
      simp only [edgeEquiv, Equiv.coe_fn_mk, hu, hvu, ↓reduceDIte, qE, headV, nextE]
      cases hp : p (false, ⟨u.val, hu⟩) <;> simp [Fin.ext_iff, hsub]
    · simp only [hv, ↓reduceIte]
      refine ⟨hgs, Extends.refl gs, by omega, by omega, fun xs hc σ p _ _ _ => ?_⟩
      rw [wireAt_zero hc]
      simp only [edgeEquiv, Equiv.coe_fn_mk, hu, ↓reduceDIte, nextE]
      by_cases hvn : v.val < n
      · simp [hvn]
      · have hne : v.val - n ≠ u.val := by omega
        simp [hvn, Fin.ext_iff, hne]
  · simp only [hu, ↓reduceDIte]
    by_cases hv : v.val < n
    · simp only [hv, ↓reduceDIte]
      set r1 := cNot N0 (mask1 ⟨v.val, hv⟩) gs with hr1
      obtain ⟨v1, e1, l1, w1, f1⟩ := cNot_spec (mask1 ⟨v.val, hv⟩) hgs (hm1 ⟨v.val, hv⟩)
      rw [← hr1] at v1 e1 l1 w1 f1
      have hp1 : perm ⟨u.val - n, by omega⟩ ⟨v.val, hv⟩ < N0 + r1.1.length := by
        have := hperm ⟨u.val - n, by omega⟩ ⟨v.val, hv⟩; omega
      obtain ⟨v2, e2, l2, w2, f2⟩ := cAnd_spec (perm ⟨u.val - n, by omega⟩ ⟨v.val, hv⟩) r1.2 v1 hp1 w1
      refine ⟨v2, e1.trans e2, by omega, w2, fun xs hc σ p hpp _ hpm1 => ?_⟩
      rw [f2 xs hc.1, wireAt_extends e1 (w := perm ⟨u.val - n, by omega⟩ ⟨v.val, hv⟩)
        (by rw [hc.1]; exact hperm _ _), hpp, f1 xs hc.1, hpm1]
      simp only [edgeEquiv, Equiv.coe_fn_mk, hu, hv, ↓reduceDIte, qE, headV, nextE]
      by_cases hsig : σ ⟨u.val - n, by omega⟩ = ⟨v.val, hv⟩
      · rw [hsig]
        cases hp : p (true, ⟨v.val, hv⟩) <;> simp
      · have hne : (⟨v.val, hv⟩ : Fin n) ≠ σ ⟨u.val - n, by omega⟩ := fun h => hsig h.symm
        simp [hsig, hne]
    · simp only [hv, ↓reduceDIte]
      refine ⟨hgs, Extends.refl gs, by omega, by omega, fun xs hc σ p _ _ _ => ?_⟩
      rw [wireAt_zero hc]
      simp [edgeEquiv, hu, hv, nextE]

def cAdjMat (N0 n : ℕ) (perm : Fin n → Fin n → ℕ) (mask0 mask1 : Fin n → ℕ) (gs : List Gate) :
    List Gate × (Fin (2 * n) → Fin (2 * n) → ℕ) :=
  cBuildFin (2 * n) (fun u g1 =>
    cBuildFin (2 * n) (fun v g2 =>
      if u = v then (g2, 1)
      else
        let (g3, a) := cArcStepWire N0 n perm mask0 mask1 u v g2
        let (g4, b) := cArcStepWire N0 n perm mask0 mask1 v u g3
        cOr N0 a b g4) g1) gs

lemma cAdjMat_spec {N0 n : ℕ} (hN : 2 ≤ N0) {gs : List Gate}
    {perm : Fin n → Fin n → ℕ} {mask0 mask1 : Fin n → ℕ}
    (hgs : ValidCircuit N0 gs)
    (hperm : ∀ i j, perm i j < N0 + gs.length)
    (hm0 : ∀ i, mask0 i < N0 + gs.length) (hm1 : ∀ i, mask1 i < N0 + gs.length) :
    let r := cAdjMat N0 n perm mask0 mask1 gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + (2 * n) * ((2 * n) * 5) ∧
    (∀ u v, r.2 u v < N0 + r.1.length) ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ i j, wireAt gs xs (perm i j) = decide (σ i = j)) →
      (∀ i, wireAt gs xs (mask0 i) = (p (false, i)).isSome) →
      (∀ i, wireAt gs xs (mask1 i) = (p (true, i)).isSome) →
      ∀ u v : Fin (2 * n), wireAt r.1 xs (r.2 u v) = adjMat σ p (edgeEquiv n u) (edgeEquiv n v) := by
  dsimp only [cAdjMat]
  have h := cBuildFin_spec (N0 := N0) (2 * n) ((2 * n) * 5)
    (fun u g1 => cBuildFin (2 * n) (fun v g2 =>
      if u = v then (g2, 1)
      else
        let (g3, a) := cArcStepWire N0 n perm mask0 mask1 u v g2
        let (g4, b) := cArcStepWire N0 n perm mask0 mask1 v u g3
        cOr N0 a b g4) g1)
    (fun g u row => (∀ v, row v < N0 + g.length) ∧
      ∀ xs, HasConsts xs N0 → ∀ σ p,
        (∀ i j, wireAt gs xs (perm i j) = decide (σ i = j)) →
        (∀ i, wireAt gs xs (mask0 i) = (p (false, i)).isSome) →
        (∀ i, wireAt gs xs (mask1 i) = (p (true, i)).isSome) →
        ∀ v, wireAt g xs (row v) = adjMat σ p (edgeEquiv n u) (edgeEquiv n v))
    (fun g1 g2 u row he ⟨hw, hf⟩ => ⟨fun v => lt_of_lt_of_le (hw v) (Nat.add_le_add_left he.length_le N0),
      fun xs hc σ p hp hm0' hm1' v => by
        rw [wireAt_extends he (w := row v) (by rw [hc.1]; exact hw v), hf xs hc σ p hp hm0' hm1' v]⟩)
    gs hgs
    (fun u g1 hg1 he1 => by
      have h2 := cBuildFin_spec (N0 := N0) (2 * n) 5
        (fun v g2 =>
          if u = v then (g2, 1)
          else
            let (g3, a) := cArcStepWire N0 n perm mask0 mask1 u v g2
            let (g4, b) := cArcStepWire N0 n perm mask0 mask1 v u g3
            cOr N0 a b g4)
        (fun g v w => w < N0 + g.length ∧
          ∀ xs, HasConsts xs N0 → ∀ σ p,
            (∀ i j, wireAt gs xs (perm i j) = decide (σ i = j)) →
            (∀ i, wireAt gs xs (mask0 i) = (p (false, i)).isSome) →
            (∀ i, wireAt gs xs (mask1 i) = (p (true, i)).isSome) →
            wireAt g xs w = adjMat σ p (edgeEquiv n u) (edgeEquiv n v))
        (fun g2 g3 v w he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
          fun xs hc σ p hp hm0' hm1' => by
            rw [wireAt_extends he (w := w) (by rw [hc.1]; exact hw), hf xs hc σ p hp hm0' hm1']⟩)
        g1 hg1
        (fun v g2 hg2 he2 => by
          by_cases huv : u = v
          · subst huv
            simp only [↓reduceIte]
            refine ⟨hg2, Extends.refl g2, by omega, by omega, fun xs hc σ p _ _ _ => ?_⟩
            rw [wireAt_one hc]; simp [adjMat]
          · simp only [huv, ↓reduceIte]
            have he12 : Extends gs g2 := he1.trans he2
            have helen := he12.length_le
            set r1 := cArcStepWire N0 n perm mask0 mask1 u v g2 with hr1
            obtain ⟨v1, e1, l1, w1, f1⟩ := cArcStepWire_spec (perm := perm) (mask0 := mask0) (mask1 := mask1) hN u v hg2
              (fun i j => by have := hperm i j; omega) (fun i => by have := hm0 i; omega) (fun i => by have := hm1 i; omega)
            rw [← hr1] at v1 e1 l1 w1 f1
            have he13 : Extends gs r1.1 := he12.trans e1
            have helen3 := he13.length_le
            set r2 := cArcStepWire N0 n perm mask0 mask1 v u r1.1 with hr2
            obtain ⟨v2, e2, l2, w2, f2⟩ := cArcStepWire_spec (perm := perm) (mask0 := mask0) (mask1 := mask1) hN v u v1
              (fun i j => by have := hperm i j; omega) (fun i => by have := hm0 i; omega) (fun i => by have := hm1 i; omega)
            rw [← hr2] at v2 e2 l2 w2 f2
            have hw1' : r1.2 < N0 + r2.1.length := lt_of_lt_of_le w1 (Nat.add_le_add_left e2.length_le N0)
            obtain ⟨v3, e3, l3, w3, f3⟩ := cOr_spec r1.2 r2.2 v2 hw1' w2
            refine ⟨v3, e1.trans (e2.trans e3), by omega, w3, fun xs hc σ p hpp hpm0 hpm1 => ?_⟩
            rw [f3 xs hc.1, wireAt_extends e2 (w := r1.2) (by rw [hc.1]; exact w1),
              f1 xs hc σ p (fun i j => by rw [wireAt_extends he12 (w := perm i j) (by rw [hc.1]; exact hperm i j), hpp])
                (fun i => by rw [wireAt_extends he12 (w := mask0 i) (by rw [hc.1]; exact hm0 i), hpm0])
                (fun i => by rw [wireAt_extends he12 (w := mask1 i) (by rw [hc.1]; exact hm1 i), hpm1]),
              f2 xs hc σ p (fun i j => by rw [wireAt_extends he13 (w := perm i j) (by rw [hc.1]; exact hperm i j), hpp])
                (fun i => by rw [wireAt_extends he13 (w := mask0 i) (by rw [hc.1]; exact hm0 i), hpm0])
                (fun i => by rw [wireAt_extends he13 (w := mask1 i) (by rw [hc.1]; exact hm1 i), hpm1])]
            have hne : edgeEquiv n u ≠ edgeEquiv n v := fun h' => huv ((edgeEquiv n).injective h')
            unfold adjMat
            simp only [hne, false_or]
            apply Bool.eq_iff_iff.mpr; simp)
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun v => (h2.2.2.2 v).1, fun xs hc σ p hpp hpm0 hpm1 v => (h2.2.2.2 v).2 xs hc σ p hpp hpm0 hpm1⟩)
  exact ⟨h.1, h.2.1, h.2.2.1, fun u v => (h.2.2.2 u).1 v, fun xs hc σ p hpp hpm0 hpm1 u v => (h.2.2.2 u).2 xs hc σ p hpp hpm0 hpm1 v⟩

def cMatMulBool (N0 m : ℕ) (A B : Fin m → Fin m → ℕ) (gs : List Gate) :
    List Gate × (Fin m → Fin m → ℕ) :=
  cBuildFin m (fun u g1 =>
    cBuildFin m (fun v g2 =>
      let (g3, prods) := cBuildFin m (fun w g => cAnd N0 (A u w) (B w v) g) g2
      cOrFin N0 m prods g3) g1) gs

lemma cMatMulBool_spec {N0 m : ℕ} (hN : 2 ≤ N0) {gs : List Gate} {A B : Fin m → Fin m → ℕ}
    (hgs : ValidCircuit N0 gs) (hA : ∀ u v, A u v < N0 + gs.length)
    (hB : ∀ u v, B u v < N0 + gs.length) :
    let r := cMatMulBool N0 m A B gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + m * (m * (2 * m)) ∧
    (∀ u v, r.2 u v < N0 + r.1.length) ∧
    ∀ xs : List Bool, HasConsts xs N0 → ∀ u v : Fin m,
      wireAt r.1 xs (r.2 u v) = decide (∃ w : Fin m, wireAt gs xs (A u w) = true ∧ wireAt gs xs (B w v) = true) := by
  dsimp only [cMatMulBool]
  have h := cBuildFin_spec (N0 := N0) m (m * (2 * m))
    (fun u g1 => cBuildFin m (fun v g2 =>
      let (g3, prods) := cBuildFin m (fun w g => cAnd N0 (A u w) (B w v) g) g2
      cOrFin N0 m prods g3) g1)
    (fun g u row => (∀ v, row v < N0 + g.length) ∧
      ∀ xs, HasConsts xs N0 → ∀ v,
        wireAt g xs (row v) = decide (∃ w : Fin m, wireAt gs xs (A u w) = true ∧ wireAt gs xs (B w v) = true))
    (fun g1 g2 u row he ⟨hw, hf⟩ => ⟨fun v => lt_of_lt_of_le (hw v) (Nat.add_le_add_left he.length_le N0),
      fun xs hc v => by rw [wireAt_extends he (w := row v) (by rw [hc.1]; exact hw v), hf xs hc v]⟩)
    gs hgs
    (fun u g1 hg1 he1 => by
      have h2 := cBuildFin_spec (N0 := N0) m (2 * m)
        (fun v g2 =>
          let (g3, prods) := cBuildFin m (fun w g => cAnd N0 (A u w) (B w v) g) g2
          cOrFin N0 m prods g3)
        (fun g v rwire => rwire < N0 + g.length ∧
          ∀ xs, HasConsts xs N0 →
            wireAt g xs rwire = decide (∃ w : Fin m, wireAt gs xs (A u w) = true ∧ wireAt gs xs (B w v) = true))
        (fun g2 g3 v rwire he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
          fun xs hc => by rw [wireAt_extends he (w := rwire) (by rw [hc.1]; exact hw), hf xs hc]⟩)
        g1 hg1
        (fun v g2 hg2 he2 => by
          have he12 : Extends gs g2 := he1.trans he2
          have h3 := cBuildFin_spec (N0 := N0) m 1 (fun w g => cAnd N0 (A u w) (B w v) g)
            (fun g w pwire => pwire < N0 + g.length ∧
              ∀ xs, xs.length = N0 → wireAt g xs pwire = (wireAt gs xs (A u w) && wireAt gs xs (B w v)))
            (fun g3 g4 w pwire he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
              fun xs hlen => by rw [wireAt_extends he (w := pwire) (by rw [hlen]; exact hw), hf xs hlen]⟩)
            g2 hg2
            (fun w g3 hg3 he3 => by
              have he13 := he12.trans he3
              have helen := he13.length_le
              obtain ⟨v1, e1, l1, w1, f1⟩ := cAnd_spec (A u w) (B w v) hg3
                (by have := hA u w; omega) (by have := hB w v; omega)
              refine ⟨v1, e1, by omega, w1, fun xs hlen => ?_⟩
              rw [f1 xs hlen, wireAt_extends he13 (w := A u w) (by rw [hlen]; exact hA u w),
                wireAt_extends he13 (w := B w v) (by rw [hlen]; exact hB w v)])
          obtain ⟨v4, e4, l4, w4, f4⟩ := cOrFin_spec hN h3.1 (fun w => (h3.2.2.2 w).1)
          refine ⟨v4, h3.2.1.trans e4, by have := h3.2.2.1; linarith, w4, fun xs hc => ?_⟩
          apply Bool.eq_iff_iff.mpr
          rw [f4 xs hc, decide_eq_true_eq]
          constructor
          · rintro ⟨w, hw⟩
            rw [(h3.2.2.2 w).2 xs hc.1, Bool.and_eq_true] at hw
            exact ⟨w, hw⟩
          · rintro ⟨w, hw⟩
            refine ⟨w, ?_⟩
            rw [(h3.2.2.2 w).2 xs hc.1, Bool.and_eq_true]
            exact hw)
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun v => (h2.2.2.2 v).1, fun xs hc v => (h2.2.2.2 v).2 xs hc⟩)
  exact ⟨h.1, h.2.1, h.2.2.1, fun u v => (h.2.2.2 u).1 v, fun xs hc u v => (h.2.2.2 u).2 xs hc v⟩

def cMatPowBool (N0 m k : ℕ) (A : Fin m → Fin m → ℕ) (gs : List Gate) :
    List Gate × (Fin m → Fin m → ℕ) :=
  cFoldFin k (fun _ acc g => cMatMulBool N0 m acc A g) A gs

lemma cMatPowBool_spec {N0 n : ℕ} (hN : 2 ≤ N0) (k : ℕ) {gs : List Gate}
    {A : Fin (2 * n) → Fin (2 * n) → ℕ}
    (hgs : ValidCircuit N0 gs) (hA : ∀ u v, A u v < N0 + gs.length) :
    let r := cMatPowBool N0 (2 * n) k A gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + k * ((2 * n) * ((2 * n) * (2 * (2 * n)))) ∧
    (∀ u v, r.2 u v < N0 + r.1.length) ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ u v : Fin (2 * n), wireAt gs xs (A u v) = adjMat σ p (edgeEquiv n u) (edgeEquiv n v)) →
      ∀ u v : Fin (2 * n), wireAt r.1 xs (r.2 u v) = matPowBool (adjMat σ p) k (edgeEquiv n u) (edgeEquiv n v) := by
  dsimp only [cMatPowBool]
  have h := cFoldFin_spec (N0 := N0) k ((2 * n) * ((2 * n) * (2 * (2 * n))))
    (fun _ acc g => cMatMulBool N0 (2 * n) acc A g)
    (fun m _ g acc => (∀ u v, acc u v < N0 + g.length) ∧
      ∀ xs, HasConsts xs N0 → ∀ σ p,
        (∀ u v, wireAt gs xs (A u v) = adjMat σ p (edgeEquiv n u) (edgeEquiv n v)) →
        ∀ u v, wireAt g xs (acc u v) = matPowBool (adjMat σ p) m (edgeEquiv n u) (edgeEquiv n v))
    A gs hgs
    ⟨hA, fun xs _ σ p hAeq u v => hAeq u v⟩
    (fun i gs1 acc hv1 he1 ⟨hacc, hsem⟩ => by
      have helen := he1.length_le
      obtain ⟨v1, e1, l1, w1, f1⟩ := cMatMulBool_spec (B := A) hN hv1 hacc (fun u v => by have := hA u v; omega)
      refine ⟨v1, e1, l1, w1, fun xs hc σ p hAeq u v => ?_⟩
      rw [f1 xs hc u v]
      change decide (∃ w : Fin (2 * n), _) = matMulBool (matPowBool (adjMat σ p) i.val) (adjMat σ p) (edgeEquiv n u) (edgeEquiv n v)
      unfold matMulBool
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · rintro ⟨w, hw1, hw2⟩
        rw [hsem xs hc σ p hAeq u w] at hw1
        rw [wireAt_extends he1 (w := A w v) (by rw [hc.1]; exact hA w v), hAeq w v] at hw2
        exact ⟨edgeEquiv n w, hw1, hw2⟩
      · rintro ⟨w, hw1, hw2⟩
        refine ⟨(edgeEquiv n).symm w, ?_, ?_⟩
        · rw [hsem xs hc σ p hAeq u ((edgeEquiv n).symm w), Equiv.apply_symm_apply]; exact hw1
        · rw [wireAt_extends he1 (w := A ((edgeEquiv n).symm w) v) (by rw [hc.1]; exact hA _ _),
            hAeq, Equiv.apply_symm_apply]; exact hw2)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

def cBuildArcCounts (N0 n B : ℕ) (perm : Fin n → Fin n → ℕ) (mask0 mask1 : Fin n → ℕ)
    (gs : List Gate) : List Gate × (Fin (2 * n + 1) → Fin (n + 1) → Word B) :=
  let (g1, adj) := cAdjMat N0 n perm mask0 mask1 gs
  let (g2, E) := cMatPowBool N0 (2 * n) (2 * n) adj g1
  let (g3, isRep) := cBuildFin (2 * n) (fun e g =>
    let (ga, nots) := cBuildFin (2 * n) (fun e' g' =>
      if e'.val < e.val then cNot N0 (E e e') g' else (g', 1)) g
    cAndFin N0 (2 * n) nots ga) g2
  let (g4, lenW) := cBuildFin (2 * n) (fun e g =>
    cSumFinWords N0 B (2 * n) (fun e' => cBitWord B (E e e')) g) g3
  let (g5, redW) := cBuildFin (2 * n) (fun e g =>
    cSumFinWords N0 B n (fun i => cBitWord B (E e ⟨i.val, by omega⟩)) g) g4
  cBuildFin (2 * n + 1) (fun l ga =>
    cBuildFin (n + 1) (fun r gb =>
      let (gc, hits) := cBuildFin (2 * n) (fun e g =>
        let (gd, eqL) := cEqWord N0 B (lenW e) (cConstWord B l.val) g
        let (ge, eqR) := cEqWord N0 B (redW e) (cConstWord B r.val) gd
        let (gf, eqLR) := cAnd N0 eqL eqR ge
        cAnd N0 (isRep e) eqLR gf) gb
      cSumFinWords N0 B (2 * n) (fun e => cBitWord B (hits e)) gc) ga) g5

lemma cBuildArcCounts_spec {N0 n B : ℕ} (hN : 2 ≤ N0) (hB : 1 ≤ B) (h2n : 2 * n < 2 ^ B)
    {gs : List Gate} {perm : Fin n → Fin n → ℕ} {mask0 mask1 : Fin n → ℕ}
    (hgs : ValidCircuit N0 gs)
    (hperm : ∀ i j, perm i j < N0 + gs.length)
    (hm0 : ∀ i, mask0 i < N0 + gs.length) (hm1 : ∀ i, mask1 i < N0 + gs.length) :
    let cost := (2 * n) * ((2 * n) * 5) +
      (2 * n) * ((2 * n) * ((2 * n) * (2 * (2 * n)))) +
      (2 * n) * (2 * n + 2 * n) +
      (2 * n) * ((2 * n) * (13 * B)) +
      (2 * n) * (n * (13 * B)) +
      (2 * n + 1) * ((n + 1) * ((2 * n) * (7 * B + 7 * B + 2) + (2 * n) * (13 * B)))
    let r := cBuildArcCounts N0 n B perm mask0 mask1 gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + cost ∧
    (∀ l r', ValidWord N0 r.1 (r.2 l r')) ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ i j, wireAt gs xs (perm i j) = decide (σ i = j)) →
      (∀ i, wireAt gs xs (mask0 i) = (p (false, i)).isSome) →
      (∀ i, wireAt gs xs (mask1 i) = (p (true, i)).isSome) →
      ∀ (l : Fin (2 * n + 1)) (r' : Fin (n + 1)),
        wordNat r.1 xs (r.2 l r') = arcCountAll σ p l.val r'.val := by
  intro cost
  dsimp only [cBuildArcCounts]
  set r1 := cAdjMat N0 n perm mask0 mask1 gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cAdjMat_spec hN hgs hperm hm0 hm1
  rw [← hr1] at v1 e1 l1 w1 f1
  set r2 := cMatPowBool N0 (2 * n) (2 * n) r1.2 r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cMatPowBool_spec hN (2 * n) v1 w1
  rw [← hr2] at v2 e2 l2 w2 f2
  set r3 := cBuildFin (2 * n) (fun e g =>
    let (ga, nots) := cBuildFin (2 * n) (fun e' g' =>
      if e'.val < e.val then cNot N0 (r2.2 e e') g' else (g', 1)) g
    cAndFin N0 (2 * n) nots ga) r2.1 with hr3
  have h3 := cBuildFin_spec (N0 := N0) (2 * n) (2 * n + 2 * n)
    (fun e g =>
      let (ga, nots) := cBuildFin (2 * n) (fun e' g' =>
        if e'.val < e.val then cNot N0 (r2.2 e e') g' else (g', 1)) g
      cAndFin N0 (2 * n) nots ga)
    (fun g e w => w < N0 + g.length ∧
      ∀ xs, HasConsts xs N0 →
        (wireAt g xs w = true ↔ ∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false))
    (fun g1 g2 e w he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
      fun xs hc => by rw [wireAt_extends he (w := w) (by rw [hc.1]; exact hw), hf xs hc]⟩)
    r2.1 v2
    (fun e g hg he => by
      have ha := cBuildFin_spec (N0 := N0) (2 * n) 1
        (fun e' g' => if e'.val < e.val then cNot N0 (r2.2 e e') g' else (g', 1))
        (fun g' e' w' => w' < N0 + g'.length ∧
          ∀ xs, HasConsts xs N0 →
            (wireAt g' xs w' = true ↔ (e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false)))
        (fun g1 g2 e' w' he' ⟨hw', hf'⟩ => ⟨lt_of_lt_of_le hw' (Nat.add_le_add_left he'.length_le N0),
          fun xs hc => by rw [wireAt_extends he' (w := w') (by rw [hc.1]; exact hw'), hf' xs hc]⟩)
        g hg
        (fun e' g' hg' he' => by
          have heall := he.trans he'
          have helen := heall.length_le
          by_cases hlt : e'.val < e.val
          · simp only [hlt, ↓reduceIte]
            obtain ⟨va, ea, la, wa, fa⟩ := cNot_spec (r2.2 e e') hg' (by have := w2 e e'; omega)
            refine ⟨va, ea, by omega, wa, fun xs hc => ?_⟩
            rw [fa xs hc.1, wireAt_extends heall (w := r2.2 e e') (by rw [hc.1]; exact w2 e e')]
            cases wireAt r2.1 xs (r2.2 e e') <;> simp [hlt]
          · simp only [hlt, ↓reduceIte]
            refine ⟨hg', Extends.refl g', by omega, by omega, fun xs hc => ?_⟩
            rw [wireAt_one hc]; simp [hlt])
      obtain ⟨vb, eb, lb, wb, fb⟩ := cAndFin_spec hN ha.1 (fun e' => (ha.2.2.2 e').1)
      refine ⟨vb, ha.2.1.trans eb, by have := ha.2.2.1; linarith, wb, fun xs hc => ?_⟩
      rw [fb xs hc]
      constructor
      · intro hall e' hlt; exact ((ha.2.2.2 e').2 xs hc).mp (hall e') hlt
      · intro hall e'; exact ((ha.2.2.2 e').2 xs hc).mpr (hall e'))
  rw [← hr3] at h3
  set r4 := cBuildFin (2 * n) (fun e g =>
    cSumFinWords N0 B (2 * n) (fun e' => cBitWord B (r2.2 e e')) g) r3.1 with hr4
  have h4 := cBuildFin_spec (N0 := N0) (2 * n) ((2 * n) * (13 * B))
    (fun e g => cSumFinWords N0 B (2 * n) (fun e' => cBitWord B (r2.2 e e')) g)
    (fun g e w => ValidWord N0 g w ∧
      ∀ xs, HasConsts xs N0 →
        wordNat g xs w = ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card)
    (fun g1 g2 e w he ⟨hw, hf⟩ => ⟨hw.extends he, fun xs hc => by rw [wordNat_extends he hc.1 hw, hf xs hc]⟩)
    r3.1 h3.1
    (fun e g hg he => by
      have he2 : Extends r2.1 g := h3.2.1.trans he
      have helen := he2.length_le
      obtain ⟨va, ea, la, wa, fa⟩ := cSumFinWords_spec hN hg
        (fun e' => validWord_cBitWord hN B (w := r2.2 e e') (by have := w2 e e'; omega))
      refine ⟨va, ea, la, wa, fun xs hc => ?_⟩
      have hz := fa xs hc
      have hsum : (∑ e' : Fin (2 * n), wordZMod g xs (cBitWord B (r2.2 e e'))) =
          ((((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card : ℕ) : ZMod (2 ^ B)) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun e' _ => ?_
        unfold wordZMod
        rw [wordNat_cBitWord hc hB, wireAt_extends he2 (w := r2.2 e e') (by rw [hc.1]; exact w2 e e')]
        cases wireAt r2.1 xs (r2.2 e e') <;> simp
      rw [hsum] at hz
      have hcard_lt : ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card < 2 ^ B :=
        lt_of_le_of_lt (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (2 * n))) _) h2n
      have hposB : 0 < 2 ^ B := by positivity
      haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
      have hval := congrArg ZMod.val hz
      rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt hcard_lt] at hval
      exact hval)
  rw [← hr4] at h4
  set r5 := cBuildFin (2 * n) (fun e g =>
    cSumFinWords N0 B n (fun i => cBitWord B (r2.2 e ⟨i.val, by omega⟩)) g) r4.1 with hr5
  have h5 := cBuildFin_spec (N0 := N0) (2 * n) (n * (13 * B))
    (fun e g => cSumFinWords N0 B n (fun i => cBitWord B (r2.2 e ⟨i.val, by omega⟩)) g)
    (fun g e w => ValidWord N0 g w ∧
      ∀ xs, HasConsts xs N0 →
        wordNat g xs w = ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card)
    (fun g1 g2 e w he ⟨hw, hf⟩ => ⟨hw.extends he, fun xs hc => by rw [wordNat_extends he hc.1 hw, hf xs hc]⟩)
    r4.1 h4.1
    (fun e g hg he => by
      have he2 : Extends r2.1 g := h3.2.1.trans (h4.2.1.trans he)
      have helen := he2.length_le
      obtain ⟨va, ea, la, wa, fa⟩ := cSumFinWords_spec hN hg
        (fun (i : Fin n) => validWord_cBitWord hN B (w := r2.2 e ⟨i.val, by have := i.isLt; omega⟩) (by have := w2 e ⟨i.val, by have := i.isLt; omega⟩; omega))
      refine ⟨va, ea, la, wa, fun xs hc => ?_⟩
      have hz := fa xs hc
      have hsum : (∑ i : Fin n, wordZMod g xs (cBitWord B (r2.2 e ⟨i.val, by omega⟩))) =
          ((((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card : ℕ) : ZMod (2 ^ B)) := by
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold wordZMod
        rw [wordNat_cBitWord hc hB, wireAt_extends he2 (w := r2.2 e ⟨i.val, by omega⟩) (by rw [hc.1]; exact w2 e _)]
        cases wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) <;> simp
      rw [hsum] at hz
      have hcard_lt : ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card < 2 ^ B := by
        have hle : ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card ≤ n := by
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin n)) _
        omega
      have hposB : 0 < 2 ^ B := by positivity
      haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
      have hval := congrArg ZMod.val hz
      rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt hcard_lt] at hval
      exact hval)
  rw [← hr5] at h5
  have h6 := cBuildFin_spec (N0 := N0) (2 * n + 1) ((n + 1) * ((2 * n) * (7 * B + 7 * B + 2) + (2 * n) * (13 * B)))
    (fun l ga => cBuildFin (n + 1) (fun r' gb =>
      let (gc, hits) := cBuildFin (2 * n) (fun e g =>
        let (gd, eqL) := cEqWord N0 B (r4.2 e) (cConstWord B l.val) g
        let (ge, eqR) := cEqWord N0 B (r5.2 e) (cConstWord B r'.val) gd
        let (gf, eqLR) := cAnd N0 eqL eqR ge
        cAnd N0 (r3.2 e) eqLR gf) gb
      cSumFinWords N0 B (2 * n) (fun e => cBitWord B (hits e)) gc) ga)
    (fun g l row => (∀ r' : Fin (n + 1), ValidWord N0 g (row r')) ∧
      ∀ xs, HasConsts xs N0 → ∀ r' : Fin (n + 1),
        wordNat g xs (row r') =
          ((Finset.univ : Finset (Fin (2 * n))).filter (fun e =>
            (∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false) ∧
            ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card = l.val ∧
            ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card = r'.val)).card)
    (fun g1 g2 l row he ⟨hw, hf⟩ => ⟨fun r' => (hw r').extends he, fun xs hc r' => by
      rw [wordNat_extends he hc.1 (hw r'), hf xs hc r']⟩)
    r5.1 h5.1
    (fun l ga hga hea => by
      have h7 := cBuildFin_spec (N0 := N0) (n + 1) ((2 * n) * (7 * B + 7 * B + 2) + (2 * n) * (13 * B))
        (fun r' gb =>
          let (gc, hits) := cBuildFin (2 * n) (fun e g =>
            let (gd, eqL) := cEqWord N0 B (r4.2 e) (cConstWord B l.val) g
            let (ge, eqR) := cEqWord N0 B (r5.2 e) (cConstWord B r'.val) gd
            let (gf, eqLR) := cAnd N0 eqL eqR ge
            cAnd N0 (r3.2 e) eqLR gf) gb
          cSumFinWords N0 B (2 * n) (fun e => cBitWord B (hits e)) gc)
        (fun g r' w => ValidWord N0 g w ∧
          ∀ xs, HasConsts xs N0 →
            wordNat g xs w =
              ((Finset.univ : Finset (Fin (2 * n))).filter (fun e =>
                (∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false) ∧
                ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card = l.val ∧
                ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card = r'.val)).card)
        (fun g1 g2 r' w he ⟨hw, hf⟩ => ⟨hw.extends he, fun xs hc => by rw [wordNat_extends he hc.1 hw, hf xs hc]⟩)
        ga hga
        (fun r' gb hgb heb => by
          have he5b : Extends r5.1 gb := hea.trans heb
          have he4b : Extends r4.1 gb := h5.2.1.trans he5b
          have he3b : Extends r3.1 gb := h4.2.1.trans he4b
          set rhits := cBuildFin (2 * n)
            (fun e g =>
              let (gd, eqL) := cEqWord N0 B (r4.2 e) (cConstWord B l.val) g
              let (ge, eqR) := cEqWord N0 B (r5.2 e) (cConstWord B r'.val) gd
              let (gf, eqLR) := cAnd N0 eqL eqR ge
              cAnd N0 (r3.2 e) eqLR gf) gb with hrhits
          have hhits := cBuildFin_spec (N0 := N0) (2 * n) (7 * B + 7 * B + 2)
            (fun e g =>
              let (gd, eqL) := cEqWord N0 B (r4.2 e) (cConstWord B l.val) g
              let (ge, eqR) := cEqWord N0 B (r5.2 e) (cConstWord B r'.val) gd
              let (gf, eqLR) := cAnd N0 eqL eqR ge
              cAnd N0 (r3.2 e) eqLR gf)
            (fun g e w => w < N0 + g.length ∧
              ∀ xs, HasConsts xs N0 →
                (wireAt g xs w = true ↔
                  (∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false) ∧
                  ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card = l.val ∧
                  ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card = r'.val))
            (fun g1 g2 e w he ⟨hw, hf⟩ => ⟨lt_of_lt_of_le hw (Nat.add_le_add_left he.length_le N0),
              fun xs hc => by rw [wireAt_extends he (w := w) (by rw [hc.1]; exact hw), hf xs hc]⟩)
            gb hgb
            (fun e g hg he => by
              have he4g := he4b.trans he
              have he5g := he5b.trans he
              have he3g := he3b.trans he
              set rd := cEqWord N0 B (r4.2 e) (cConstWord B l.val) g with hrd
              obtain ⟨vd, ed, ld, wd, fd⟩ := cEqWord_spec hN hg ((h4.2.2.2 e).1.extends he4g) (validWord_cConstWord hN g B l.val)
              rw [← hrd] at vd ed ld wd fd
              set re := cEqWord N0 B (r5.2 e) (cConstWord B r'.val) rd.1 with hre
              obtain ⟨ve, ee, le, we, fe⟩ := cEqWord_spec hN vd ((h5.2.2.2 e).1.extends (he5g.trans ed)) (validWord_cConstWord hN rd.1 B r'.val)
              rw [← hre] at ve ee le we fe
              have hwd' : rd.2 < N0 + re.1.length := lt_of_lt_of_le wd (Nat.add_le_add_left ee.length_le N0)
              set rf := cAnd N0 rd.2 re.2 re.1 with hrf
              obtain ⟨vf, ef, lf, wf, ff⟩ := cAnd_spec rd.2 re.2 ve hwd' we
              rw [← hrf] at vf ef lf wf ff
              have hrep_lt : r3.2 e < N0 + rf.1.length :=
                lt_of_lt_of_le (h3.2.2.2 e).1 (Nat.add_le_add_left (he3g.trans (ed.trans (ee.trans ef))).length_le N0)
              obtain ⟨vg, eg, lg, wg, fg⟩ := cAnd_spec (r3.2 e) rf.2 vf hrep_lt wf
              refine ⟨vg, ed.trans (ee.trans (ef.trans eg)), by linarith, wg, fun xs hc => ?_⟩
              rw [fg xs hc.1, Bool.and_eq_true,
                wireAt_extends (he3g.trans (ed.trans (ee.trans ef))) (w := r3.2 e) (by rw [hc.1]; exact (h3.2.2.2 e).1),
                (h3.2.2.2 e).2 xs hc, ff xs hc.1, Bool.and_eq_true,
                wireAt_extends ee (w := rd.2) (by rw [hc.1]; exact wd), fd xs hc, fe xs hc,
                wordNat_extends he4g hc.1 (h4.2.2.2 e).1, (h4.2.2.2 e).2 xs hc,
                wordNat_extends (he5g.trans ed) hc.1 (h5.2.2.2 e).1, (h5.2.2.2 e).2 xs hc,
                wordNat_cConstWord hc, wordNat_cConstWord hc,
                Nat.mod_eq_of_lt (by have := l.isLt; omega),
                Nat.mod_eq_of_lt (by have := r'.isLt; omega)])
          rw [← hrhits] at hhits
          obtain ⟨vs, es, ls, ws, fs⟩ := cSumFinWords_spec hN hhits.1
            (fun e => validWord_cBitWord hN B (w := rhits.2 e) (hhits.2.2.2 e).1)
          refine ⟨vs, hhits.2.1.trans es, by have := hhits.2.2.1; linarith, ws, fun xs hc => ?_⟩
          have hz := fs xs hc
          have hsum : (∑ e : Fin (2 * n), wordZMod rhits.1 xs (cBitWord B (rhits.2 e))) =
              ((((Finset.univ : Finset (Fin (2 * n))).filter (fun e =>
                (∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false) ∧
                ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card = l.val ∧
                ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card = r'.val)).card : ℕ) : ZMod (2 ^ B)) := by
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl fun e _ => ?_
            unfold wordZMod
            rw [wordNat_cBitWord hc hB]
            by_cases hp :
                (∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false) ∧
                ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card = l.val ∧
                ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card = r'.val
            · rw [if_pos hp, ((hhits.2.2.2 e).2 xs hc).mpr hp]; simp
            · rw [if_neg hp]
              cases hval : wireAt rhits.1 xs (rhits.2 e)
              · simp
              · exact absurd (((hhits.2.2.2 e).2 xs hc).mp hval) hp
          rw [hsum] at hz
          have hcard_lt : ((Finset.univ : Finset (Fin (2 * n))).filter (fun e =>
              (∀ e' : Fin (2 * n), e'.val < e.val → wireAt r2.1 xs (r2.2 e e') = false) ∧
              ((Finset.univ : Finset (Fin (2 * n))).filter (fun e' => wireAt r2.1 xs (r2.2 e e') = true)).card = l.val ∧
              ((Finset.univ : Finset (Fin n)).filter (fun i => wireAt r2.1 xs (r2.2 e ⟨i.val, by omega⟩) = true)).card = r'.val)).card < 2 ^ B :=
            lt_of_le_of_lt (by simpa using Finset.card_filter_le (Finset.univ : Finset (Fin (2 * n))) _) h2n
          have hposB : 0 < 2 ^ B := by positivity
          haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
          have hval := congrArg ZMod.val hz
          rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt hcard_lt] at hval
          exact hval)
      exact ⟨h7.1, h7.2.1, h7.2.2.1, fun r' => (h7.2.2.2 r').1, fun xs hc r' => (h7.2.2.2 r').2 xs hc⟩)
  refine ⟨h6.1, e1.trans (e2.trans (h3.2.1.trans (h4.2.1.trans (h5.2.1.trans h6.2.1)))),
    by dsimp only [cost]; have := h3.2.2.1; have := h4.2.2.1; have := h5.2.2.1; have := h6.2.2.1; linarith,
    fun l r' => (h6.2.2.2 l).1 r', fun xs hc σ p hpp hpm0 hpm1 l r' => ?_⟩
  rw [(h6.2.2.2 l).2 xs hc r', arcCountAll_eq_repCard]
  have hE : ∀ u v : Fin (2 * n), wireAt r2.1 xs (r2.2 u v) = matPowBool (adjMat σ p) (2 * n) (edgeEquiv n u) (edgeEquiv n v) :=
    f2 xs hc σ p (f1 xs hc σ p hpp hpm0 hpm1)
  congr 1; ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hred_eq : ∀ i : Fin n, edgeEquiv n ⟨i.val, by omega⟩ = (false, i) := fun i => by
    simp [edgeEquiv, i.isLt]
  simp_rw [hE, hred_eq]

end GraphClosureCircuit

noncomputable section MainAssembly

lemma freeCount_le {n : ℕ} (p : Bool × Fin n → Option Bool) : freeCount p ≤ 2 * n := by
  unfold freeCount
  calc (Finset.univ.filter (fun v : Bool × Fin n => p v = none)).card
      ≤ (Finset.univ : Finset (Bool × Fin n)).card := Finset.card_filter_le _ _
    _ = 2 * n := by simp

lemma choose_le_two_pow_self (m h : ℕ) : Nat.choose m h ≤ 2 ^ m := by
  by_cases hm : h ≤ m
  · rw [← Nat.sum_range_choose m]
    exact Finset.single_le_sum (f := fun k => Nat.choose m k) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    exact Nat.zero_le _

lemma profile_lt_two_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (h : ℕ) (s : Fin (2 * n + 1)) :
    profile (hist σ p) h s < 2 ^ (4 * n + 3) := by
  unfold profile
  have hle1 : (∑ r : Fin (n + 1), ∑ b : Fin (n + 1),
      if r.val + b.val = s.val then Nat.choose r.val h * hist σ p r b else 0) ≤
      ∑ r : Fin (n + 1), ∑ b : Fin (n + 1), 2 ^ n * hist σ p r b := by
    refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun b _ => ?_
    split_ifs
    · refine Nat.mul_le_mul_right _ ?_
      exact le_trans (choose_le_two_pow_self r.val h) (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ r.isLt))
    · exact Nat.zero_le _
  have hsum : (∑ r : Fin (n + 1), ∑ b : Fin (n + 1), 2 ^ n * hist σ p r b) = 2 ^ n * 2 ^ freeCount p := by
    simp_rw [← Finset.mul_sum]
    rw [sum_hist_eq_twoPow σ p]
  have hle2 : 2 ^ n * 2 ^ freeCount p ≤ 2 ^ (3 * n) := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by have := freeCount_le p; omega)
  have hlt : 2 ^ (3 * n) < 2 ^ (4 * n + 3) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

lemma flatten_ofFn_eq_len {α : Type*} :
    ∀ (A B : ℕ) (L : Fin A → List α), (∀ a, (L a).length = B) → (List.ofFn L).flatten.length = A * B
  | 0, _, _, _ => by simp
  | A + 1, B, L, hL => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hL 0,
      flatten_ofFn_eq_len A B (fun a => L a.succ) (fun a => hL a.succ)]
    ring

lemma flatten_ofFn_eq_getD {α : Type*} (d : α) :
    ∀ (A B : ℕ) (L : Fin A → List α), (∀ a, (L a).length = B) →
      ∀ (a : Fin A) {b : ℕ}, b < B →
        (List.ofFn L).flatten.getD (a.val * B + b) d = (L a).getD b d
  | 0, _, _, _, a, _, _ => Fin.elim0 a
  | A + 1, B, L, hL, a, b, hb => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ ?_ a
    · simp only [Fin.val_zero, zero_mul, zero_add]
      have hlen : b < (L 0).length := by rw [hL 0]; exact hb
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlen]
    · intro a'
      have hge : (L 0).length ≤ a'.succ.val * B + b := by
        rw [hL 0, Fin.val_succ, Nat.succ_mul]; omega
      have hsub : a'.succ.val * B + b - (L 0).length = a'.val * B + b := by
        rw [hL 0, Fin.val_succ, Nat.succ_mul]; omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hsub]
      simpa only [List.getD_eq_getElem?_getD] using
        flatten_ofFn_eq_getD d A B (fun x => L x.succ) (fun x => hL x.succ) a' hb

def N_in (n : ℕ) (known : Bool) : ℕ :=
  2 + (if known then n * n + 2 * n else 0) + (if known then 2 else 3) * (2 * n + 1) * (4 * n + 3)

def cbOff (n : ℕ) (known : Bool) : ℕ :=
  2 + if known then n * n + 2 * n else 0

def permBits {n : ℕ} (σ : Equiv.Perm (Fin n)) : List Bool :=
  (List.ofFn (fun i : Fin n => List.ofFn (fun j : Fin n => decide (σ i = j)))).flatten

def maskBits {n : ℕ} (p : Bool × Fin n → Option Bool) : List Bool :=
  (List.ofFn (fun i : Fin n => (p (false, i)).isSome)) ++
    List.ofFn (fun i : Fin n => (p (true, i)).isSome)

def countBitsFn {n : ℕ} (k : ℕ) (H : Fin (n + 1) → Fin (n + 1) → ℕ) : List Bool :=
  (List.ofFn (fun h : Fin k => (List.ofFn (fun s : Fin (2 * n + 1) =>
    List.ofFn (fun i : Fin (4 * n + 3) => (profile H h.val s).testBit i.val))).flatten)).flatten

def inputBits {n : ℕ} (known : Bool) (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) : List Bool :=
  [false, true] ++ (if known then permBits σ ++ maskBits p else []) ++
    countBitsFn (if known then 2 else 3) (hist σ p)

lemma permBits_len {n : ℕ} (σ : Equiv.Perm (Fin n)) : (permBits σ).length = n * n :=
  flatten_ofFn_eq_len n n _ (fun _ => by simp)

lemma maskBits_len {n : ℕ} (p : Bool × Fin n → Option Bool) : (maskBits p).length = 2 * n := by
  unfold maskBits; simp; ring

lemma countBitsFn_len {n : ℕ} (k : ℕ) (H : Fin (n + 1) → Fin (n + 1) → ℕ) :
    (countBitsFn k H).length = k * (2 * n + 1) * (4 * n + 3) := by
  unfold countBitsFn
  rw [flatten_ofFn_eq_len k ((2 * n + 1) * (4 * n + 3)) _ (fun _ =>
    flatten_ofFn_eq_len (2 * n + 1) (4 * n + 3) _ (fun _ => by simp))]
  ring

lemma inputBits_hasConsts {n : ℕ} (known : Bool) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) :
    HasConsts (inputBits known σ p) (N_in n known) := by
  refine ⟨?_, by unfold N_in; omega, by simp [inputBits], by simp [inputBits]⟩
  unfold inputBits N_in
  rw [List.length_append, List.length_append, countBitsFn_len]
  cases known
  · simp
  · simp [permBits_len, maskBits_len]

def permW (n : ℕ) (i j : Fin n) : ℕ := 2 + i.val * n + j.val
def mask0W (n : ℕ) (i : Fin n) : ℕ := 2 + n * n + i.val
def mask1W (n : ℕ) (i : Fin n) : ℕ := 2 + n * n + n + i.val

def profW (n B0 : ℕ) (known : Bool) (h : Fin 3) (s : Fin (2 * n + 1)) : Word B0 :=
  if h.val < (if known then 2 else 3) then
    fun i => if i.val < 4 * n + 3 then
      cbOff n known + h.val * ((2 * n + 1) * (4 * n + 3)) + s.val * (4 * n + 3) + i.val
    else 0
  else cZeroWord B0

lemma permW_lt (n : ℕ) (i j : Fin n) : permW n i j < N_in n true := by
  unfold permW N_in
  simp only [↓reduceIte]
  have h1 : i.val * n + j.val < n * n := by
    have hi : i.val + 1 ≤ n := i.isLt
    have hj := j.isLt
    nlinarith
  omega

lemma mask0W_lt (n : ℕ) (i : Fin n) : mask0W n i < N_in n true := by
  unfold mask0W N_in; simp only [↓reduceIte]; have := i.isLt; omega

lemma mask1W_lt (n : ℕ) (i : Fin n) : mask1W n i < N_in n true := by
  unfold mask1W N_in; simp only [↓reduceIte]; have := i.isLt; omega

lemma profW_valid (n B0 : ℕ) (known : Bool) (h : Fin 3) (s : Fin (2 * n + 1)) :
    ValidWord (N_in n known) [] (profW n B0 known h s) := by
  intro i
  unfold profW
  by_cases hh : h.val < (if known then 2 else 3)
  · simp only [hh, ↓reduceIte]
    by_cases hi : i.val < 4 * n + 3
    · simp only [hi, ↓reduceIte, List.length_nil, add_zero]
      unfold cbOff N_in
      set k := if known then 2 else 3
      have h1 : s.val * (4 * n + 3) + i.val < (2 * n + 1) * (4 * n + 3) := by
        have hs : s.val + 1 ≤ 2 * n + 1 := s.isLt
        have hm := Nat.mul_le_mul_right (4 * n + 3) hs
        linarith
      have h2 : h.val * ((2 * n + 1) * (4 * n + 3)) + (s.val * (4 * n + 3) + i.val) <
          k * ((2 * n + 1) * (4 * n + 3)) := by
        have hh' : h.val + 1 ≤ k := hh
        have hm := Nat.mul_le_mul_right ((2 * n + 1) * (4 * n + 3)) hh'
        linarith
      have hmul : k * (2 * n + 1) * (4 * n + 3) = k * ((2 * n + 1) * (4 * n + 3)) := Nat.mul_assoc _ _ _
      omega
    · simp only [hi, ↓reduceIte, List.length_nil, add_zero]; unfold N_in; omega
  · simp only [hh, ↓reduceIte, cZeroWord, List.length_nil, add_zero]; unfold N_in; omega

lemma wireAt_permW {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (i j : Fin n) :
    wireAt [] (inputBits true σ p) (permW n i j) = decide (σ i = j) := by
  unfold wireAt evalWires PEqualNP.CircuitLowerBounds.Circuit.wires inputBits permW
  simp only [List.foldl_nil, ↓reduceIte]
  have h1 : i.val * n + j.val < (permBits σ).length := by
    rw [permBits_len]; have hi : i.val + 1 ≤ n := i.isLt; have hj := j.isLt; nlinarith
  have hpref : ([false, true] ++ (permBits σ ++ maskBits p) ++ countBitsFn 2 (hist σ p)).getD (2 + i.val * n + j.val) false =
      (permBits σ).getD (i.val * n + j.val) false := by
    have hlt : 2 + i.val * n + j.val < ([false, true] ++ (permBits σ ++ maskBits p)).length := by
      simp only [List.length_append, List.length_cons, List.length_nil, permBits_len, maskBits_len]
      rw [permBits_len] at h1; omega
    have hge : ([false, true] : List Bool).length ≤ 2 + i.val * n + j.val := by simp; omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_append_right hge]
    have hsub : 2 + i.val * n + j.val - ([false, true] : List Bool).length = i.val * n + j.val := by simp; omega
    rw [hsub, List.getElem?_append_left h1, List.getD_eq_getElem?_getD]
  rw [hpref]
  unfold permBits
  rw [flatten_ofFn_eq_getD false n n _ (fun _ => by simp) i j.isLt]
  simp [List.getD_eq_getElem?_getD, j.isLt]

lemma wireAt_mask0W {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (i : Fin n) :
    wireAt [] (inputBits true σ p) (mask0W n i) = (p (false, i)).isSome := by
  unfold wireAt evalWires PEqualNP.CircuitLowerBounds.Circuit.wires inputBits mask0W
  simp only [List.foldl_nil, ↓reduceIte]
  have hlenp := permBits_len σ
  have hlenm := maskBits_len p
  have hlt1 : 2 + n * n + i.val < ([false, true] ++ (permBits σ ++ maskBits p)).length := by
    simp [hlenp, hlenm]; have := i.isLt; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
    List.getElem?_append_right (show ([false, true] : List Bool).length ≤ 2 + n * n + i.val by simp; omega),
    List.length_cons, List.length_nil]
  have hsub1 : 2 + n * n + i.val - (0 + 1 + 1) = n * n + i.val := by omega
  rw [hsub1, List.getElem?_append_right (by rw [hlenp]; omega), hlenp, Nat.add_sub_cancel_left]
  unfold maskBits
  rw [List.getElem?_append_left (by simp [i.isLt])]
  simp [i.isLt]

lemma wireAt_mask1W {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (i : Fin n) :
    wireAt [] (inputBits true σ p) (mask1W n i) = (p (true, i)).isSome := by
  unfold wireAt evalWires PEqualNP.CircuitLowerBounds.Circuit.wires inputBits mask1W
  simp only [List.foldl_nil, ↓reduceIte]
  have hlenp := permBits_len σ
  have hlenm := maskBits_len p
  have hlt1 : 2 + n * n + n + i.val < ([false, true] ++ (permBits σ ++ maskBits p)).length := by
    simp [hlenp, hlenm]; have := i.isLt; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt1,
    List.getElem?_append_right (show ([false, true] : List Bool).length ≤ 2 + n * n + n + i.val by simp; omega),
    List.length_cons, List.length_nil]
  have hsub1 : 2 + n * n + n + i.val - (0 + 1 + 1) = n * n + (n + i.val) := by omega
  rw [hsub1, List.getElem?_append_right (by rw [hlenp]; omega), hlenp, Nat.add_sub_cancel_left]
  unfold maskBits
  rw [List.getElem?_append_right (by simp)]
  simp [i.isLt]

lemma wordNat_profW {n B0 : ℕ} (hB0 : 4 * n + 3 ≤ B0) (known : Bool)
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (h : Fin 3) (s : Fin (2 * n + 1)) :
    wordNat [] (inputBits known σ p) (profW n B0 known h s) =
      if h.val < (if known then 2 else 3) then profile (hist σ p) h.val s else 0 := by
  have hc := inputBits_hasConsts known σ p
  by_cases hh : h.val < (if known then 2 else 3)
  · rw [if_pos hh]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [wordNat_testBit]
    by_cases hk1 : k < 4 * n + 3
    · have hk2 : k < B0 := by omega
      rw [dif_pos hk2]
      unfold profW
      simp only [hh, hk1, ↓reduceIte]
      unfold wireAt evalWires PEqualNP.CircuitLowerBounds.Circuit.wires inputBits
      simp only [List.foldl_nil]
      have hpref_len : ([false, true] ++ if known then permBits σ ++ maskBits p else []).length = cbOff n known := by
        unfold cbOff
        cases known
        · simp
        · simp [permBits_len, maskBits_len]; ring
      have hge : ([false, true] ++ if known then permBits σ ++ maskBits p else []).length ≤
          cbOff n known + h.val * ((2 * n + 1) * (4 * n + 3)) + s.val * (4 * n + 3) + k := by
        rw [hpref_len]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hpref_len]
      have hsub : cbOff n known + h.val * ((2 * n + 1) * (4 * n + 3)) + s.val * (4 * n + 3) + k - cbOff n known =
          h.val * ((2 * n + 1) * (4 * n + 3)) + (s.val * (4 * n + 3) + k) := by omega
      rw [hsub]
      change (countBitsFn (if known then 2 else 3) (hist σ p)).getD
          (h.val * ((2 * n + 1) * (4 * n + 3)) + (s.val * (4 * n + 3) + k)) false = _
      unfold countBitsFn
      have hlt_inner : s.val * (4 * n + 3) + k < (2 * n + 1) * (4 * n + 3) := by
        have hs : s.val + 1 ≤ 2 * n + 1 := s.isLt
        have hm := Nat.mul_le_mul_right (4 * n + 3) hs
        linarith
      rw [flatten_ofFn_eq_getD false (if known then 2 else 3) ((2 * n + 1) * (4 * n + 3)) _
        (fun _ => flatten_ofFn_eq_len (2 * n + 1) (4 * n + 3) _ (fun _ => by simp)) ⟨h.val, hh⟩ hlt_inner]
      rw [flatten_ofFn_eq_getD false (2 * n + 1) (4 * n + 3) _ (fun _ => by simp) s hk1]
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hk1]
      rfl
    · have htb_zero : (profile (hist σ p) h.val s).testBit k = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (profile_lt_two_pow σ p h.val s)
          (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [htb_zero]
      by_cases hk2 : k < B0
      · rw [dif_pos hk2]
        unfold profW
        simp only [hh, hk1, ↓reduceIte]
        exact wireAt_zero hc
      · rw [dif_neg hk2]
  · rw [if_neg hh]
    unfold profW
    simp only [hh, ↓reduceIte]
    exact wordNat_cZeroWord hc B0

def qWeight (n : ℕ) (h : Fin 3) (d : Fin (2 * n + 1)) (k : Fin 3) (s : Fin (2 * n + 1)) : ℤ :=
  match h.val, k.val with
  | 0, 0 => krawCoeff (2 * n) s.val d.val
  | 1, 0 => if 1 ≤ d.val ∧ s.val < 2 * n then (n : ℤ) * krawCoeff (2 * n - 1) s.val (d.val - 1) else 0
  | 1, 1 =>
    if 1 ≤ d.val then
      -(if s.val < 2 * n then krawCoeff (2 * n - 1) s.val (d.val - 1) else 0) -
      (if 1 ≤ s.val then krawCoeff (2 * n - 1) (s.val - 1) (d.val - 1) else 0)
    else 0
  | 2, 0 =>
    if 2 ≤ d.val ∧ s.val + 2 ≤ 2 * n then (Nat.choose n 2 : ℤ) * krawCoeff (2 * n - 2) s.val (d.val - 2) else 0
  | 2, 1 =>
    if 2 ≤ d.val then
      -((n - 1 : ℕ) : ℤ) * (if s.val + 2 ≤ 2 * n then krawCoeff (2 * n - 2) s.val (d.val - 2) else 0) -
      ((n - 1 : ℕ) : ℤ) * (if 1 ≤ s.val ∧ s.val + 1 ≤ 2 * n then krawCoeff (2 * n - 2) (s.val - 1) (d.val - 2) else 0)
    else 0
  | 2, 2 =>
    if 2 ≤ d.val then
      (if s.val + 2 ≤ 2 * n then krawCoeff (2 * n - 2) s.val (d.val - 2) else 0) +
      2 * (if 1 ≤ s.val ∧ s.val + 1 ≤ 2 * n then krawCoeff (2 * n - 2) (s.val - 1) (d.val - 2) else 0) +
      (if 2 ≤ s.val then krawCoeff (2 * n - 2) (s.val - 2) (d.val - 2) else 0)
    else 0
  | _, _ => 0

lemma Q_from_profile_eq_sum_qWeight {n : ℕ} (prof : Fin 3 → Fin (2 * n + 1) → ℕ)
    (h : Fin 3) (d : Fin (2 * n + 1)) :
    (Q_from_profile prof).coeff h d =
      (∑ s : Fin (2 * n + 1), qWeight n h d 0 s * (prof 0 s : ℤ)) +
      (∑ s : Fin (2 * n + 1), qWeight n h d 1 s * (prof 1 s : ℤ)) +
      (∑ s : Fin (2 * n + 1), qWeight n h d 2 s * (prof 2 s : ℤ)) := by
  fin_cases h
  · simp only [Q_from_profile, qWeight, Fin.zero_eta, Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun s _ => by ring
  · simp only [Q_from_profile, qWeight, Fin.mk_one, Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, Finset.sum_const_zero, add_zero]
    by_cases hd : 1 ≤ d.val
    · simp only [hd, true_and, ↓reduceDIte, ↓reduceIte]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
    · simp [hd]
  · simp only [Q_from_profile, qWeight, Fin.val_zero, Fin.val_one, Fin.val_two]
    by_cases hd : 2 ≤ d.val
    · simp only [hd, true_and, ↓reduceDIte, ↓reduceIte]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => by split_ifs <;> ring
    · simp [hd]

def arcProdZT {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) : Trunc2 3 (2 * n + 1) R :=
  ∏ c ∈ arcClasses σ p,
    (1 + (arcSignZ σ p c : Trunc2 3 (2 * n + 1) R) *
      (Trunc2.X2 * (1 + Trunc2.X1)) ^ arcRed c * Trunc2.X2 ^ arcBlue c)

lemma arcProdZT_mapHom {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    Trunc2.mapHom (Int.castRingHom (ZMod (2 ^ B))) (arcProdZT (R := ℤ) σ p) =
      arcProdZT (R := ZMod (2 ^ B)) σ p := by
  unfold arcProdZT
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [map_add, map_one, map_mul, map_pow, map_intCast, Trunc2.X1, Trunc2.X2, Trunc2.mapHom_monom]

lemma arcProdUV_mapHom {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    Trunc2.mapHom (Int.castRingHom (ZMod (2 ^ B))) (arcProdUV (R := ℤ) σ p) =
      arcProdUV (R := ZMod (2 ^ B)) σ p := by
  unfold arcProdUV
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [map_add, map_one, map_mul, map_pow, map_intCast, Trunc2.X1, Trunc2.X2, Trunc2.mapHom_monom]

lemma shiftRight_zmod_eq' {B B0 f M : ℕ} (hB0 : B0 = B + M) (hf : f ≤ M) (x : ℤ) :
    (((((2 : ℤ) ^ f * x : ℤ) : ZMod (2 ^ B0)).val / 2 ^ f : ℕ) : ZMod (2 ^ B)) = (x : ZMod (2 ^ B)) := by
  subst hB0
  exact shiftRight_zmod_eq hf x

def cStage1TwoPow (n B0 : ℕ) (known : Bool) : List Gate × Word B0 :=
  cSumFinWords (N_in n known) B0 (2 * n + 1) (fun s => profW n B0 known 0 s) []

lemma cStage1TwoPow_spec (n B0 : ℕ) (hB0 : B0 = 4 * n + 10) (known : Bool) :
    let N0 := N_in n known
    let r := cStage1TwoPow n B0 known
    ValidCircuit N0 r.1 ∧ r.1.length ≤ (2 * n + 1) * (13 * B0) ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
      wireAt r.1 (inputBits known σ p) (r.2 ⟨k.val, by omega⟩) =
        decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩) := by
  intro N0
  dsimp only [cStage1TwoPow]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  obtain ⟨v1, e1, l1, w1, f1⟩ := cSumFinWords_spec hN (validCircuit_nil N0) (fun s => profW_valid n B0 known 0 s)
  refine ⟨v1, by simpa using l1, w1, fun σ p k => ?_⟩
  have hc := inputBits_hasConsts known σ p
  have hz := f1 (inputBits known σ p) hc
  have hsum : (∑ s : Fin (2 * n + 1), wordZMod [] (inputBits known σ p) (profW n B0 known 0 s)) =
      ((2 ^ freeCount p : ℕ) : ZMod (2 ^ B0)) := by
    rw [← sum_profile_zero_eq_twoPow σ p, Nat.cast_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold wordZMod; rw [wordNat_profW (by omega : 4 * n + 3 ≤ B0)]
    have h0lt : (0 : Fin 3).val < (if known then 2 else 3) := by cases known <;> simp
    rw [if_pos h0lt]; rfl
  rw [hsum] at hz
  have hlt2 : 2 ^ freeCount p < 2 ^ B0 := Nat.pow_lt_pow_right (by omega) (by have := freeCount_le p; omega)
  have hposB0 : 0 < 2 ^ B0 := by positivity
  haveI : NeZero (2 ^ B0) := ⟨Nat.ne_of_gt hposB0⟩
  have hnat : wordNat (cSumFinWords (N_in n known) B0 (2 * n + 1) (fun s => profW n B0 known 0 s) []).1 (inputBits known σ p)
      (cSumFinWords (N_in n known) B0 (2 * n + 1) (fun s => profW n B0 known 0 s) []).2 = 2 ^ freeCount p := by
    have hval := congrArg ZMod.val hz
    rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt hlt2] at hval
    exact hval
  have htb := wordNat_testBit (cSumFinWords (N_in n known) B0 (2 * n + 1) (fun s => profW n B0 known 0 s) []).1
    (inputBits known σ p) (cSumFinWords (N_in n known) B0 (2 * n + 1) (fun s => profW n B0 known 0 s) []).2 k.val
  rw [dif_pos (by omega), hnat, Nat.testBit_two_pow] at htb
  rw [← htb]
  by_cases hkeq : k = ⟨freeCount p, by have := freeCount_le p; omega⟩
  · subst hkeq; simp
  · have : freeCount p ≠ k.val := fun h' => hkeq (Fin.ext h'.symm)
    simp [hkeq, this]

def cStage1QEntry (n B0 : ℕ) (known : Bool) (h : Fin 3) (d : Fin (2 * n + 1)) (gs : List Gate) :
    List Gate × Word B0 :=
  let N0 := N_in n known
  let (gc, s0) := cLinComb N0 B0 (2 * n + 1) (fun s => (qWeight n h d 0 s : ZMod (2 ^ B0))) (fun s => profW n B0 known 0 s) gs
  let (gd, s1) := cLinComb N0 B0 (2 * n + 1) (fun s => (qWeight n h d 1 s : ZMod (2 ^ B0))) (fun s => profW n B0 known 1 s) gc
  let (ge, s2) := cLinComb N0 B0 (2 * n + 1) (fun s => (qWeight n h d 2 s : ZMod (2 ^ B0))) (fun s => profW n B0 known 2 s) gd
  let (gf, s01) := cAdd N0 B0 s0 s1 ge
  cAdd N0 B0 s01 s2 gf

lemma cStage1QEntry_spec (n B0 : ℕ) (hB0 : 4 * n + 3 ≤ B0) (known : Bool) (h : Fin 3) (d : Fin (2 * n + 1))
    {gs : List Gate} (hgs : ValidCircuit (N_in n known) gs) :
    let N0 := N_in n known
    let r := cStage1QEntry n B0 known h d gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 3 * ((2 * n + 1) * (13 * B0 * B0 + 13 * B0)) + 2 * (13 * B0) ∧
    ValidWord N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      wordZMod r.1 (inputBits known σ p) r.2 =
        ((Q_from_profile (fun k s => if k.val < (if known then 2 else 3) then profile (hist σ p) k.val s else 0)).coeff h d : ZMod (2 ^ B0)) := by
  intro N0
  dsimp only [cStage1QEntry]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have he0 : Extends [] gs := ⟨gs, rfl⟩
  set rc := cLinComb N0 B0 (2 * n + 1) (fun s => (qWeight n h d 0 s : ZMod (2 ^ B0))) (fun s => profW n B0 known 0 s) gs with hrc
  obtain ⟨vc, ec, lc, wc, fc⟩ := cLinComb_spec hN (fun s => (qWeight n h d 0 s : ZMod (2 ^ B0))) hgs
    (fun s => (profW_valid n B0 known 0 s).extends he0)
  rw [← hrc] at vc ec lc wc fc
  set rd := cLinComb N0 B0 (2 * n + 1) (fun s => (qWeight n h d 1 s : ZMod (2 ^ B0))) (fun s => profW n B0 known 1 s) rc.1 with hrd
  obtain ⟨vd, ed, ld, wd, fd⟩ := cLinComb_spec hN (fun s => (qWeight n h d 1 s : ZMod (2 ^ B0))) vc
    (fun s => (profW_valid n B0 known 1 s).extends (he0.trans ec))
  rw [← hrd] at vd ed ld wd fd
  set re := cLinComb N0 B0 (2 * n + 1) (fun s => (qWeight n h d 2 s : ZMod (2 ^ B0))) (fun s => profW n B0 known 2 s) rd.1 with hre
  obtain ⟨ve, ee, le, we, fe⟩ := cLinComb_spec hN (fun s => (qWeight n h d 2 s : ZMod (2 ^ B0))) vd
    (fun s => (profW_valid n B0 known 2 s).extends (he0.trans (ec.trans ed)))
  rw [← hre] at ve ee le we fe
  set rf := cAdd N0 B0 rc.2 rd.2 re.1 with hrf
  obtain ⟨vf, ef, lf, wf, ff⟩ := cAdd_spec hN ve (wc.extends (ed.trans ee)) (wd.extends ee)
  rw [← hrf] at vf ef lf wf ff
  obtain ⟨vg, eg, lg, wg, fg⟩ := cAdd_spec hN vf wf (we.extends ef)
  refine ⟨vg, ec.trans (ed.trans (ee.trans (ef.trans eg))), by linarith, wg, fun σ p => ?_⟩
  have hc := inputBits_hasConsts known σ p
  rw [fg _ hc, ff _ hc, wordZMod_extends (ed.trans ee) hc.1 wc, fc _ hc,
    wordZMod_extends ee hc.1 wd, fd _ hc, wordZMod_extends ef hc.1 we, fe _ hc]
  rw [Q_from_profile_eq_sum_qWeight]
  simp only [Int.cast_add, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  congr 1; congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [wordZMod_extends he0 hc.1 (profW_valid n B0 known 0 s)]
    unfold wordZMod; rw [wordNat_profW hB0]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [wordZMod_extends (he0.trans ec) hc.1 (profW_valid n B0 known 1 s)]
    unfold wordZMod; rw [wordNat_profW hB0]
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [wordZMod_extends (he0.trans (ec.trans ed)) hc.1 (profW_valid n B0 known 2 s)]
    unfold wordZMod; rw [wordNat_profW hB0]

def cStage1Q (n B0 : ℕ) (known : Bool) (gs : List Gate) :
    List Gate × Trunc2Wire 3 (2 * n + 1) B0 :=
  cBuildFin 3 (fun h ga => cBuildFin (2 * n + 1) (fun d gb => cStage1QEntry n B0 known h d gb) ga) gs

lemma cStage1Q_spec (n B0 : ℕ) (hB0 : 4 * n + 3 ≤ B0) (known : Bool) {gs : List Gate} (hgs : ValidCircuit (N_in n known) gs) :
    let N0 := N_in n known
    let r := cStage1Q n B0 known gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B0 * B0 + 13 * B0)) + 2 * (13 * B0))) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (h : Fin 3) (d : Fin (2 * n + 1)),
      wordZMod r.1 (inputBits known σ p) (r.2 h d) =
        ((Q_from_profile (fun k s => if k.val < (if known then 2 else 3) then profile (hist σ p) k.val s else 0)).coeff h d : ZMod (2 ^ B0)) := by
  intro N0
  dsimp only [cStage1Q]
  have h := cBuildFin_spec (N0 := N0) 3 ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B0 * B0 + 13 * B0)) + 2 * (13 * B0)))
    (fun h ga => cBuildFin (2 * n + 1) (fun d gb => cStage1QEntry n B0 known h d gb) ga)
    (fun g h row => (∀ d : Fin (2 * n + 1), ValidWord N0 g (row d)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (d : Fin (2 * n + 1)),
        wordZMod g (inputBits known σ p) (row d) =
          ((Q_from_profile (fun k s => if k.val < (if known then 2 else 3) then profile (hist σ p) k.val s else 0)).coeff h d : ZMod (2 ^ B0)))
    (fun g1 g2 h row he ⟨hw, hf⟩ => ⟨fun d => (hw d).extends he, fun σ p d => by
      rw [wordZMod_extends he (inputBits_hasConsts known σ p).1 (hw d), hf σ p d]⟩)
    gs hgs
    (fun h ga hga _ => by
      have h2 := cBuildFin_spec (N0 := N0) (2 * n + 1) (3 * ((2 * n + 1) * (13 * B0 * B0 + 13 * B0)) + 2 * (13 * B0))
        (fun d gb => cStage1QEntry n B0 known h d gb)
        (fun g d w => ValidWord N0 g w ∧
          ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
            wordZMod g (inputBits known σ p) w =
              ((Q_from_profile (fun k s => if k.val < (if known then 2 else 3) then profile (hist σ p) k.val s else 0)).coeff h d : ZMod (2 ^ B0)))
        (fun g1 g2 d w he ⟨hw, hf⟩ => ⟨hw.extends he, fun σ p => by
          rw [wordZMod_extends he (inputBits_hasConsts known σ p).1 hw, hf σ p]⟩)
        ga hga
        (fun d gb hgb _ => by
          obtain ⟨v1, e1, l1, w1, f1⟩ := cStage1QEntry_spec n B0 hB0 known h d hgb
          exact ⟨v1, e1, by linarith, w1, f1⟩)
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun d => (h2.2.2.2 d).1, fun σ p d => (h2.2.2.2 d).2 σ p⟩)
  exact ⟨h.1, h.2.1, h.2.2.1, fun i j => (h.2.2.2 i).1 j, fun σ p i j => (h.2.2.2 i).2 σ p j⟩

def cStage1Shift (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (known : Bool) (twoPowF : Word B0)
    (Q : Trunc2Wire 3 (2 * n + 1) B0) (gs : List Gate) :
    List Gate × Trunc2Wire 3 (2 * n + 1) B :=
  cBuildFin 3 (fun h ga =>
    cBuildFin (2 * n + 1) (fun d gb =>
      cOneHotShiftRight (N_in n known) B0 B (2 * n + 1)
        (fun k => twoPowF ⟨k.val, by omega⟩) (Q h d) gb) ga) gs

lemma cStage1Shift_spec (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (hB : B = 2 * n + 10) (hB0 : B0 = 4 * n + 10)
    (known : Bool) {gs : List Gate}
    {twoPowF : Word B0} {Q : Trunc2Wire 3 (2 * n + 1) B0}
    (hgs : ValidCircuit (N_in n known) gs)
    (htp : ValidWord (N_in n known) gs twoPowF) (hQ : ValidTrunc2 (N_in n known) gs Q)
    (htp_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
      wireAt gs (inputBits known σ p) (twoPowF ⟨k.val, by omega⟩) =
        decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩))
    (hQ_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (h : Fin 3) (d : Fin (2 * n + 1)),
      wordZMod gs (inputBits known σ p) (Q h d) =
        ((Q_from_profile (fun k s => if k.val < (if known then 2 else 3) then profile (hist σ p) k.val s else 0)).coeff h d : ZMod (2 ^ B0))) :
    let N0 := N_in n known
    let r := cStage1Shift n B B0 hB0_ge known twoPowF Q gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 3 * ((2 * n + 1) * ((2 * n + 1) * (4 * B))) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (h : Fin 3),
      (known = false ∨ h.val < 2) → ∀ d : Fin (2 * n + 1),
        (trunc2Val r.1 (inputBits known σ p) r.2).coeff h d = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d := by
  intro N0
  dsimp only [cStage1Shift]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have h3 := cBuildFin_spec (N0 := N0) 3 ((2 * n + 1) * ((2 * n + 1) * (4 * B)))
    (fun h ga => cBuildFin (2 * n + 1) (fun d gb =>
      cOneHotShiftRight N0 B0 B (2 * n + 1) (fun k => twoPowF ⟨k.val, by omega⟩) (Q h d) gb) ga)
    (fun g h row => (∀ d : Fin (2 * n + 1), ValidWord N0 g (row d)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
        (known = false ∨ h.val < 2) → ∀ d : Fin (2 * n + 1),
          wordZMod g (inputBits known σ p) (row d) = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d)
    (fun g1 g2 h row he ⟨hw, hf⟩ => ⟨fun d => (hw d).extends he, fun σ p hok d => by
      rw [wordZMod_extends he (inputBits_hasConsts known σ p).1 (hw d), hf σ p hok d]⟩)
    gs hgs
    (fun h ga hga hea => by
      have h3b := cBuildFin_spec (N0 := N0) (2 * n + 1) ((2 * n + 1) * (4 * B))
        (fun d gb =>
          cOneHotShiftRight N0 B0 B (2 * n + 1) (fun k => twoPowF ⟨k.val, by omega⟩) (Q h d) gb)
        (fun g d w => ValidWord N0 g w ∧
          ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
            (known = false ∨ h.val < 2) →
              wordZMod g (inputBits known σ p) w = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d)
        (fun g1 g2 d w he ⟨hw, hf⟩ => ⟨hw.extends he, fun σ p hok => by
          rw [wordZMod_extends he (inputBits_hasConsts known σ p).1 hw, hf σ p hok]⟩)
        ga hga
        (fun d gb hgb heb => by
          have hegb : Extends gs gb := hea.trans heb
          have hsel : ∀ k : Fin (2 * n + 1), twoPowF ⟨k.val, by omega⟩ < N0 + gb.length :=
            fun k => (htp.extends hegb) ⟨k.val, by omega⟩
          obtain ⟨v3, e3, l3, w3, f3⟩ := cOneHotShiftRight_spec hN hgb hsel ((hQ h d).extends hegb)
          refine ⟨v3, e3, l3, w3, fun σ p hok => ?_⟩
          have hc := inputBits_hasConsts known σ p
          have hoh : ∀ k : Fin (2 * n + 1), wireAt gb (inputBits known σ p) (twoPowF ⟨k.val, by omega⟩) =
              decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩) := fun k => by
            rw [wireAt_extends hegb (w := twoPowF ⟨k.val, by omega⟩) (by rw [hc.1]; exact htp _)]
            exact htp_sem σ p k
          have hnat := f3 (inputBits known σ p) hc ⟨freeCount p, by have := freeCount_le p; omega⟩ hoh
          unfold wordZMod
          rw [hnat]
          have hposB : 0 < 2 ^ B := by positivity
          haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
          rw [ZMod.natCast_mod, wordNat_extends hegb hc.1 (hQ h d), ← wordZMod_val, hQ_sem σ p h d]
          have hqeq : (Q_from_profile (fun k s => if k.val < (if known then 2 else 3) then profile (hist σ p) k.val s else 0)).coeff h d =
              (Q_from_profile (fun k s => profile (hist σ p) k.val s)).coeff h d := by
            rcases hok with rfl | hh2
            · congr 2; funext k s; simp [k.isLt]
            · exact Q_from_profile_row01_eq _ _
                (by funext s; cases known <;> simp)
                (by funext s; cases known <;> simp) h hh2 d
          rw [hqeq, ← rawPoly_zt_eq_Q_from_profile, rawPoly_eq_arcProd]
          have h2p : ((2 : Trunc2 3 (2 * n + 1) ℤ) ^ freeCount p) = (((2 ^ freeCount p : ℕ) : Trunc2 3 (2 * n + 1) ℤ)) := by simp
          have hcoeff : ((2 : Trunc2 3 (2 * n + 1) ℤ) ^ freeCount p * arcProdZT (R := ℤ) σ p).coeff h d =
              (2 : ℤ) ^ freeCount p * (arcProdZT (R := ℤ) σ p).coeff h d := by
            rw [h2p, Trunc2.natCast_mul_coeff]; simp
          change ((((((2 : Trunc2 3 (2 * n + 1) ℤ) ^ freeCount p * arcProdZT (R := ℤ) σ p).coeff h d : ℤ) : ZMod (2 ^ B0)).val / 2 ^ freeCount p : ℕ) : ZMod (2 ^ B)) = _
          rw [hcoeff, shiftRight_zmod_eq' (show B0 = B + 2 * n by omega) (freeCount_le p) ((arcProdZT (R := ℤ) σ p).coeff h d)]
          exact congrArg (fun P => P.coeff h d) (arcProdZT_mapHom (B := B) σ p))
      exact ⟨h3b.1, h3b.2.1, h3b.2.2.1, fun d => (h3b.2.2.2 d).1, fun σ p hok d => (h3b.2.2.2 d).2 σ p hok⟩)
  exact ⟨h3.1, h3.2.1, h3.2.2.1, fun i j => (h3.2.2.2 i).1 j, fun σ p h hok d => (h3.2.2.2 h).2 σ p hok d⟩

def cStage1 (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (known : Bool) :
    List Gate × Word B0 × Trunc2Wire 3 (2 * n + 1) B :=
  let (g1, twoPowF) := cStage1TwoPow n B0 known
  let (g2, Q) := cStage1Q n B0 known g1
  let (g3, F_zt) := cStage1Shift n B B0 hB0_ge known twoPowF Q g2
  (g3, twoPowF, F_zt)

lemma cStage1_spec (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (hB : B = 2 * n + 10) (hB0 : B0 = 4 * n + 10) (known : Bool) :
    let N0 := N_in n known
    let cost1 := (2 * n + 1) * (13 * B0) +
      3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B0 * B0 + 13 * B0)) + 2 * (13 * B0))) +
      3 * ((2 * n + 1) * ((2 * n + 1) * (4 * B)))
    let r := cStage1 n B B0 hB0_ge known
    ValidCircuit N0 r.1 ∧ r.1.length ≤ cost1 ∧
    ValidWord N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      let xs := inputBits known σ p
      (∀ k : Fin (2 * n + 1),
        wireAt r.1 xs (r.2.1 ⟨k.val, by omega⟩) =
          decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩)) ∧
      (∀ h : Fin 3, (known = false ∨ h.val < 2) → ∀ d : Fin (2 * n + 1),
        (trunc2Val r.1 xs r.2.2).coeff h d = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d) := by
  intro N0 cost1
  dsimp only [cStage1]
  set r1 := cStage1TwoPow n B0 known with hr1
  obtain ⟨v1, l1, w1, f1⟩ := cStage1TwoPow_spec n B0 hB0 known
  rw [← hr1] at v1 l1 w1 f1
  set r2 := cStage1Q n B0 known r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cStage1Q_spec n B0 (by omega) known v1
  rw [← hr2] at v2 e2 l2 w2 f2
  have htp2 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
      wireAt r2.1 (inputBits known σ p) (r1.2 ⟨k.val, by omega⟩) =
        decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩) := fun σ p k => by
    rw [wireAt_extends e2 (w := r1.2 ⟨k.val, by omega⟩) (by rw [(inputBits_hasConsts known σ p).1]; exact w1 _)]
    exact f1 σ p k
  obtain ⟨v3, e3, l3, w3, f3⟩ := cStage1Shift_spec n B B0 hB0_ge hB hB0 known v2 (w1.extends e2) w2 htp2 f2
  refine ⟨v3, by dsimp only [cost1] at *; linarith, w1.extends (e2.trans e3), w3, fun σ p => ⟨fun k => ?_, f3 σ p⟩⟩
  rw [wireAt_extends (e2.trans e3) (w := r1.2 ⟨k.val, by omega⟩) (by rw [(inputBits_hasConsts known σ p).1]; exact w1 _)]
  exact f1 σ p k

def fZT (n B l r : ℕ) : Trunc2 3 (2 * n + 1) (ZMod (2 ^ B)) :=
  Trunc2.X2 ^ l * (1 + Trunc2.X1) ^ r

def fUV (n B l r : ℕ) : Trunc2 (n + 1) (n + 1) (ZMod (2 ^ B)) :=
  Trunc2.X1 ^ r * Trunc2.X2 ^ (l - r)

lemma r_le_l_of_primR {l r : ℕ} (hl : 1 ≤ l) (hr : r ∈ primR l) : r ≤ l := by
  unfold primR at hr
  split_ifs at hr <;> simp at hr <;> omega

lemma r_le_l_of_allowedR {l r : ℕ} (hl : 1 ≤ l) (hr : r ∈ allowedR l) : r ≤ l := by
  unfold allowedR at hr
  split_ifs at hr <;> simp at hr <;> omega

lemma r_le_n_of_primR {n l r : ℕ} (hl : l ≤ 2 * n) (hr : r ∈ primR l) : r ≤ n := by
  unfold primR at hr
  split_ifs at hr <;> simp at hr <;> omega

lemma zt_monom_eq {n B l r : ℕ} (hrl : r ≤ l) :
    (Trunc2.X2 * (1 + Trunc2.X1) : Trunc2 3 (2 * n + 1) (ZMod (2 ^ B))) ^ r * Trunc2.X2 ^ (l - r) =
      fZT n B l r := by
  unfold fZT
  rw [mul_pow, mul_comm ((Trunc2.X2 : Trunc2 3 (2 * n + 1) (ZMod (2 ^ B))) ^ r), mul_assoc,
    ← pow_add, Nat.add_sub_of_le hrl, mul_comm ((1 + Trunc2.X1) ^ r)]

lemma fZT_zero_const {n B l r : ℕ} (hl : 1 ≤ l) :
    ∀ i j, i.val + j.val = 0 → (fZT n B l r).coeff i j = 0 := by
  intro i j hij
  unfold fZT
  rw [trunc2_X2_mul_1_add_X1_coeff]
  have : j.val ≠ l := by omega
  simp [this]

lemma fUV_zero_const {n B l r : ℕ} (hl : 1 ≤ l) (hrl : r ≤ l) :
    ∀ i j, i.val + j.val = 0 → (fUV n B l r).coeff i j = 0 := by
  intro i j hij
  unfold fUV
  rw [Trunc2.X1_pow_mul_X2_pow]
  simp only [Trunc2.monom]
  have : ¬ (i.val = r ∧ j.val = l - r) := by omega
  simp [this]

lemma arcProdZT_eq_cTarget {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    arcProdZT (R := ZMod (2 ^ B)) σ p =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (fZT n B l r) (cTarget σ p l r) := by
  unfold arcProdZT
  rw [arcProd_eq_cTarget]
  · refine Finset.prod_congr rfl fun l hl => Finset.prod_congr rfl fun r hr => ?_
    rw [zt_monom_eq (r_le_l_of_allowedR (Finset.mem_Icc.mp hl).1 (List.mem_toFinset.mp hr))]
  · intro l r hl hr
    rw [zt_monom_eq (r_le_l_of_primR hl hr)]
    exact fZT_zero_const hl
  · intro l r hl _ hr h2l
    rw [zt_monom_eq (r_le_l_of_primR hl hr)]
    unfold fZT
    rw [mul_pow, ← pow_mul, show (Trunc2.X2 : Trunc2 3 (2 * n + 1) (ZMod (2 ^ B))) ^ (l * 2) = Trunc2.monom 0 (l * 2) by
      simp [Trunc2.X2, Trunc2.monom_pow], Trunc2.monom_eq_zero_of_ge 0 (l * 2) (Or.inr (by omega)), zero_mul]

lemma arcProdUV_eq_cTarget {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    arcProdUV (R := ZMod (2 ^ B)) σ p =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (allowedR l).toFinset,
        Trunc2.zpowOneSub (fUV n B l r) (cTarget σ p l r) := by
  unfold arcProdUV
  rw [arcProd_eq_cTarget]
  · rfl
  · intro l r hl hr
    exact fUV_zero_const hl (r_le_l_of_primR hl hr)
  · intro l r hl _ hr h2l
    have hrl := r_le_l_of_primR hl hr
    change (fUV n B l r) ^ 2 = 0
    unfold fUV
    rw [Trunc2.X1_pow_mul_X2_pow, Trunc2.monom_pow]
    refine Trunc2.monom_eq_zero_of_ge _ _ ?_
    by_cases h1 : n + 1 ≤ 2 * r
    · exact Or.inl h1
    · exact Or.inr (by omega)

def tailZT_false (n B : ℕ) (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : ℕ) :
    Trunc2 3 (2 * n + 1) (ZMod (2 ^ B)) :=
  ∏ l ∈ Finset.Icc (k + 1) (2 * n), ∏ r ∈ (allowedR l).toFinset,
    Trunc2.zpowOneSub (fZT n B l r) (cTarget σ p l r)

def prefUV_false (n B : ℕ) (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : ℕ) :
    Trunc2 (n + 1) (n + 1) (ZMod (2 ^ B)) :=
  ∏ l ∈ Finset.Icc 1 k, ∏ r ∈ (allowedR l).toFinset,
    Trunc2.zpowOneSub (fUV n B l r) (cTarget σ p l r)

lemma tailZT_false_coeff {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (idx : Fin (2 * n)) (h : Fin 3) :
    let l := idx.val + 1
    (tailZT_false n B σ p idx.val).coeff h ⟨l, by omega⟩ =
      ∑ r ∈ (allowedR l).toFinset, -(cTarget σ p l r : ZMod (2 ^ B)) * (Nat.choose r h.val : ZMod (2 ^ B)) := by
  intro l
  unfold tailZT_false
  have houter := tail_coeff_finset_prod (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (l := l) (by omega) (by omega)
    (Finset.Icc l (2 * n))
    (fun l' => ∏ r ∈ (allowedR l').toFinset, Trunc2.zpowOneSub (fZT n B l' r) (cTarget σ p l' r))
    (fun l' hl' => (tail_coeff_finset_prod (by omega) (by omega) (allowedR l').toFinset
      (fun r => Trunc2.zpowOneSub (fZT n B l' r) (cTarget σ p l' r))
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).1)
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).2.1)).1)
    (fun l' hl' => (tail_coeff_finset_prod (by omega) (by omega) (allowedR l').toFinset
      (fun r => Trunc2.zpowOneSub (fZT n B l' r) (cTarget σ p l' r))
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).1)
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).2.1)).2.1)
  rw [houter.2.2 h]
  have hmem : l ∈ Finset.Icc l (2 * n) := Finset.mem_Icc.mpr ⟨le_refl l, idx.isLt⟩
  rw [Finset.sum_eq_single l]
  · have hinner := tail_coeff_finset_prod (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (l := l) (by omega) (by omega)
      (allowedR l).toFinset (fun r => Trunc2.zpowOneSub (fZT n B l r) (cTarget σ p l r))
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (le_refl l) (by omega) _).1)
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (le_refl l) (by omega) _).2.1)
    rw [hinner.2.2 h]
    refine Finset.sum_congr rfl fun r _ => ?_
    simpa [fZT] using (tail_coeff_zpowOneSub_zt (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (r := r) (by omega) (le_refl l) (by omega) (cTarget σ p l r)).2.2 h
  · intro l' hl' hne
    have hinner := tail_coeff_finset_prod (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (l := l) (by omega) (by omega)
      (allowedR l').toFinset (fun r => Trunc2.zpowOneSub (fZT n B l' r) (cTarget σ p l' r))
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).1)
      (fun r _ => (tail_coeff_zpowOneSub_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).2.1)
    rw [hinner.2.2 h]
    refine Finset.sum_eq_zero fun r _ => ?_
    simpa [fZT, hne] using (tail_coeff_zpowOneSub_zt (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (r := r) (by omega) (Finset.mem_Icc.mp hl').1 (by omega) (cTarget σ p l' r)).2.2 h
  · intro h0; exact absurd hmem h0

lemma tailZT_false_peel {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (idx : Fin (2 * n)) :
    let l := idx.val + 1
    (∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fZT n B l r) (-cTarget σ p l r)) *
      tailZT_false n B σ p idx.val = tailZT_false n B σ p (idx.val + 1) := by
  intro l
  unfold tailZT_false
  have hsplit : Finset.Icc l (2 * n) = insert l (Finset.Icc (l + 1) (2 * n)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : l ∉ Finset.Icc (l + 1) (2 * n) := by simp
  rw [hsplit, Finset.prod_insert hnot, ← mul_assoc, ← Finset.prod_mul_distrib]
  have hone : (∏ r ∈ (allowedR l).toFinset,
      Trunc2.zpowOneSub (fZT n B l r) (-cTarget σ p l r) *
      Trunc2.zpowOneSub (fZT n B l r) (cTarget σ p l r)) = 1 := by
    refine Finset.prod_eq_one fun r _ => ?_
    rw [← Trunc2.zpowOneSub_add _ (fZT_zero_const (by omega)), neg_add_cancel, Trunc2.zpowOneSub_zero]
  rw [hone, one_mul]

lemma prefUV_false_step {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (idx : Fin (2 * n)) :
    let l := idx.val + 1
    (∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fUV n B l r) (cTarget σ p l r)) *
      prefUV_false n B σ p idx.val = prefUV_false n B σ p (idx.val + 1) := by
  intro l
  unfold prefUV_false
  have hsplit : Finset.Icc 1 l = insert l (Finset.Icc 1 idx.val) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : l ∉ Finset.Icc 1 idx.val := by simp [l]
  rw [hsplit, Finset.prod_insert hnot]

lemma natAbs_cTarget_lt_two_pow_K {n : ℕ} (hn : 1 ≤ n) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    (cTarget σ p l r).natAbs < 2 ^ (n + 2) := by
  obtain ⟨h1, h2⟩ := cTarget_bounds σ p l r
  have ha : (cTarget σ p l r).natAbs ≤ 2 * n := by omega
  have hlt : n < 2 ^ n := Nat.lt_two_pow_self
  have hpow : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; ring
  omega

lemma cTarget_in_signed_range {n B : ℕ} (hB : B = 2 * n + 10) (σ : Equiv.Perm (Fin n))
    (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    -(2 ^ (B - 1) : ℤ) < cTarget σ p l r ∧ cTarget σ p l r < 2 ^ (B - 1) := by
  obtain ⟨h1, h2⟩ := cTarget_bounds σ p l r
  have hlt : 2 * n < 2 ^ (2 * n) := Nat.lt_two_pow_self
  have hle : 2 ^ (2 * n) ≤ 2 ^ (2 * n + 9) := Nat.pow_le_pow_right (by omega) (by omega)
  have hcast : ((2 * n : ℕ) : ℤ) < ((2 ^ (2 * n + 9) : ℕ) : ℤ) := by exact_mod_cast (lt_of_lt_of_le hlt hle)
  have hsub : B - 1 = 2 * n + 9 := by omega
  rw [hsub]
  push_cast at hcast
  omega

def costZT_step (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  (n + 2) * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B * B + 13 * B)))) + 3 * ((2 * n + 1) * (4 * B)))

def costUV_step (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  (n + 2) * ((n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) + (n + 1) * ((n + 1) * (4 * B)))

def costStepFalse (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  3 * (14 * B) + 6 * (13 * B * B + 14 * B) + 3 * (26 * B + 2 * costZT_step n + 2 * costUV_step n)

def cFalseStepOdd (n B l : ℕ) (hB_ge : 2 ≤ B) (d0 d1 : Word B)
    (R : Trunc2Wire 3 (2 * n + 1) B) (Puv : Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) :
    List Gate × (Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B) :=
  let N0 := N_in n false
  let K := n + 2
  let m := l / 2
  let (g4, md0) := cMulConst N0 B (m : ZMod (2 ^ B)) d0 gs
  let (g5, c1) := cSub N0 B d1 md0 g4
  let (g6, c0) := cSub N0 B d0 c1 g5
  let (g7, R1, P1) := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l m) (fUV n B l m) c0 R Puv g6
  cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l (m + 1)) (fUV n B l (m + 1)) c1 R1 P1 g7

lemma cFalseStepOdd_spec (n B : ℕ) (hn : 1 ≤ n) (hB_ge : 2 ≤ B) (hB : B = 2 * n + 10)
    (idx : Fin (2 * n)) (hodd : (idx.val + 1) % 2 = 1)
    {d0 d1 : Word B}
    {R : Trunc2Wire 3 (2 * n + 1) B} {Puv : Trunc2Wire (n + 1) (n + 1) B}
    {gs : List Gate} (hgs : ValidCircuit (N_in n false) gs)
    (hd0 : ValidWord (N_in n false) gs d0) (hd1 : ValidWord (N_in n false) gs d1)
    (hR : ValidTrunc2 (N_in n false) gs R) (hP : ValidTrunc2 (N_in n false) gs Puv) :
    let N0 := N_in n false
    let l := idx.val + 1
    let r := cFalseStepOdd n B l hB_ge d0 d1 R Puv gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 13 * B * B + 2 * (14 * B) + 2 * (26 * B + 2 * costZT_step n + 2 * costUV_step n) ∧
    ValidTrunc2 N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      wordZMod gs (inputBits false σ p) d0 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 0 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) →
      wordZMod gs (inputBits false σ p) d1 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 1 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) →
      trunc2Val gs (inputBits false σ p) R = tailZT_false n B σ p idx.val →
      trunc2Val gs (inputBits false σ p) Puv = prefUV_false n B σ p idx.val →
      trunc2Val r.1 (inputBits false σ p) r.2.1 = tailZT_false n B σ p (idx.val + 1) ∧
      trunc2Val r.1 (inputBits false σ p) r.2.2 = prefUV_false n B σ p (idx.val + 1) := by
  intro N0 l
  dsimp only [cFalseStepOdd]
  set K := n + 2
  set m := l / 2
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  set r4 := cMulConst N0 B (m : ZMod (2 ^ B)) d0 gs with hr4
  obtain ⟨v4, e4, l4, w4, f4⟩ := cMulConst_spec hN (m : ZMod (2 ^ B)) hgs hd0
  rw [← hr4] at v4 e4 l4 w4 f4
  set r5 := cSub N0 B d1 r4.2 r4.1 with hr5
  obtain ⟨v5, e5, l5, w5, f5⟩ := cSub_spec hN v4 (hd1.extends e4) w4
  rw [← hr5] at v5 e5 l5 w5 f5
  set r6 := cSub N0 B d0 r5.2 r5.1 with hr6
  obtain ⟨v6, e6, l6, w6, f6⟩ := cSub_spec hN v5 (hd0.extends (e4.trans e5)) w5
  rw [← hr6] at v6 e6 l6 w6 f6
  have e46 : Extends gs r6.1 := e4.trans (e5.trans e6)
  set r7 := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l m) (fUV n B l m) r6.2 R Puv r6.1 with hr7
  obtain ⟨v7, e7, l7, w7R, w7P, f7⟩ := cDecodeSignedStep_spec hN hB_ge
    (fZT n B l m) (fUV n B l m) v6 w6 (hR.extends e46) (hP.extends e46)
  rw [← hr7] at v7 e7 l7 w7R w7P f7
  obtain ⟨v8, e8, l8, w8R, w8P, f8⟩ := cDecodeSignedStep_spec hN hB_ge
    (fZT n B l (m + 1)) (fUV n B l (m + 1)) v7 (w5.extends (e6.trans e7)) w7R w7P
  have hcostZT : K * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B * B + 13 * B)))) + 3 * ((2 * n + 1) * (4 * B))) = costZT_step n := by
    unfold costZT_step; dsimp only [K]; rw [hB]
  have hcostUV : K * ((n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) + (n + 1) * ((n + 1) * (4 * B))) = costUV_step n := by
    unfold costUV_step; dsimp only [K]; rw [hB]
  refine ⟨v8, e46.trans (e7.trans e8), by linarith,
    w8R, w8P, fun σ p hd0v hd1v hReq hPeq => ?_⟩
  have hc := inputBits_hasConsts false σ p
  have hall : (allowedR l).toFinset = {m, m + 1} := by ext x; simp [allowedR, l, hodd, m]
  have hne : m ≠ m + 1 := by omega
  rw [hall, Finset.sum_pair hne] at hd0v hd1v
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul, Nat.cast_add] at hd0v hd1v
  have hsol := solve_false_odd (m : ZMod (2 ^ B)) (cTarget σ p l m : ZMod (2 ^ B)) (cTarget σ p l (m + 1) : ZMod (2 ^ B))
  have hc1_val : wordZMod r5.1 (inputBits false σ p) r5.2 = (cTarget σ p l (m + 1) : ZMod (2 ^ B)) := by
    rw [f5 _ hc, wordZMod_extends e4 hc.1 hd1, f4 _ hc, hd0v, hd1v]
    exact hsol.1
  have hc0_val : wordZMod r6.1 (inputBits false σ p) r6.2 = (cTarget σ p l m : ZMod (2 ^ B)) := by
    rw [f6 _ hc, wordZMod_extends (e4.trans e5) hc.1 hd0, hc1_val, hd0v]
    ring
  obtain ⟨hb0l, hb0u⟩ := cTarget_in_signed_range hB σ p l m
  obtain ⟨hb1l, hb1u⟩ := cTarget_in_signed_range hB σ p l (m + 1)
  obtain ⟨hR7, hP7⟩ := f7 _ hc (cTarget σ p l m) hc0_val hb0l hb0u (natAbs_cTarget_lt_two_pow_K hn σ p l m)
  obtain ⟨hR8, hP8⟩ := f8 _ hc (cTarget σ p l (m + 1))
    (by rw [wordZMod_extends (e6.trans e7) hc.1 w5, hc1_val]) hb1l hb1u (natAbs_cTarget_lt_two_pow_K hn σ p l (m + 1))
  rw [trunc2Val_extends e46 hc.1 hR, hReq] at hR7
  rw [trunc2Val_extends e46 hc.1 hP, hPeq] at hP7
  rw [hR7] at hR8; rw [hP7] at hP8
  rw [hR8, hP8, ← mul_assoc, ← mul_assoc]
  have hprodR : Trunc2.zpowOneSub (fZT n B l (m + 1)) (-cTarget σ p l (m + 1)) *
      Trunc2.zpowOneSub (fZT n B l m) (-cTarget σ p l m) =
      ∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fZT n B l r) (-cTarget σ p l r) := by
    rw [hall, Finset.prod_pair hne]; ring
  have hprodP : Trunc2.zpowOneSub (fUV n B l (m + 1)) (cTarget σ p l (m + 1)) *
      Trunc2.zpowOneSub (fUV n B l m) (cTarget σ p l m) =
      ∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fUV n B l r) (cTarget σ p l r) := by
    rw [hall, Finset.prod_pair hne]; ring
  rw [hprodR, hprodP]
  exact ⟨tailZT_false_peel σ p idx, prefUV_false_step σ p idx⟩

def cFalseStep2Mod4 (n B l : ℕ) (hB_ge : 2 ≤ B) (d0 d1 d2 : Word B)
    (R : Trunc2Wire 3 (2 * n + 1) B) (Puv : Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) :
    List Gate × (Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B) :=
  let N0 := N_in n false
  let K := n + 2
  let m := l / 2
  let r4 := cMulConst N0 B (m : ZMod (2 ^ B)) d0 gs
  let r5 := cSub N0 B d1 r4.2 r4.1
  let r6 := cMulConst N0 B (Nat.choose m 2 : ZMod (2 ^ B)) d0 r5.1
  let r7 := cSub N0 B d2 r6.2 r6.1
  let r8 := cMulConst N0 B (m : ZMod (2 ^ B)) r5.2 r7.1
  let r9 := cSub N0 B r7.2 r8.2 r8.1
  let r10 := cAdd N0 B r9.2 r5.2 r9.1
  let r11 := cSub N0 B d0 r9.2 r10.1
  let r12 := cSub N0 B r11.2 r10.2 r11.1
  let r13 := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l (m - 1)) (fUV n B l (m - 1)) r9.2 R Puv r12.1
  let r14 := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l m) (fUV n B l m) r12.2 r13.2.1 r13.2.2 r13.1
  cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l (m + 1)) (fUV n B l (m + 1)) r10.2 r14.2.1 r14.2.2 r14.1

lemma cFalseStep2Mod4_spec (n B : ℕ) (hn : 1 ≤ n) (hB_ge : 2 ≤ B) (hB : B = 2 * n + 10)
    (idx : Fin (2 * n))
    (hodd : ¬ (idx.val + 1) % 2 = 1) (h4 : ¬ (idx.val + 1) % 4 = 0)
    {d0 d1 d2 : Word B}
    {R : Trunc2Wire 3 (2 * n + 1) B} {Puv : Trunc2Wire (n + 1) (n + 1) B}
    {gs : List Gate} (hgs : ValidCircuit (N_in n false) gs)
    (hd0 : ValidWord (N_in n false) gs d0) (hd1 : ValidWord (N_in n false) gs d1)
    (hd2 : ValidWord (N_in n false) gs d2)
    (hR : ValidTrunc2 (N_in n false) gs R) (hP : ValidTrunc2 (N_in n false) gs Puv) :
    let N0 := N_in n false
    let l := idx.val + 1
    let r := cFalseStep2Mod4 n B l hB_ge d0 d1 d2 R Puv gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 6 * (13 * B * B + 14 * B) + 3 * (26 * B + 2 * costZT_step n + 2 * costUV_step n) ∧
    ValidTrunc2 N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      wordZMod gs (inputBits false σ p) d0 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 0 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) →
      wordZMod gs (inputBits false σ p) d1 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 1 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) →
      wordZMod gs (inputBits false σ p) d2 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 2 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) →
      trunc2Val gs (inputBits false σ p) R = tailZT_false n B σ p idx.val →
      trunc2Val gs (inputBits false σ p) Puv = prefUV_false n B σ p idx.val →
      trunc2Val r.1 (inputBits false σ p) r.2.1 = tailZT_false n B σ p (idx.val + 1) ∧
      trunc2Val r.1 (inputBits false σ p) r.2.2 = prefUV_false n B σ p (idx.val + 1) := by
  intro N0 l
  set K := n + 2
  set m := l / 2
  have hm1 : 1 ≤ m := by omega
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  set r4 := cMulConst N0 B (m : ZMod (2 ^ B)) d0 gs with hr4
  obtain ⟨v4, e4, l4, w4, f4⟩ := cMulConst_spec hN (m : ZMod (2 ^ B)) hgs hd0
  rw [← hr4] at v4 e4 l4 w4 f4
  set r5 := cSub N0 B d1 r4.2 r4.1 with hr5
  obtain ⟨v5, e5, l5, w5, f5⟩ := cSub_spec hN v4 (hd1.extends e4) w4
  rw [← hr5] at v5 e5 l5 w5 f5
  set r6 := cMulConst N0 B (Nat.choose m 2 : ZMod (2 ^ B)) d0 r5.1 with hr6
  obtain ⟨v6, e6, l6, w6, f6⟩ := cMulConst_spec hN (Nat.choose m 2 : ZMod (2 ^ B)) v5 (hd0.extends (e4.trans e5))
  rw [← hr6] at v6 e6 l6 w6 f6
  set r7 := cSub N0 B d2 r6.2 r6.1 with hr7
  obtain ⟨v7, e7, l7, w7, f7⟩ := cSub_spec hN v6 (hd2.extends (e4.trans (e5.trans e6))) w6
  rw [← hr7] at v7 e7 l7 w7 f7
  set r8 := cMulConst N0 B (m : ZMod (2 ^ B)) r5.2 r7.1 with hr8
  obtain ⟨v8, e8, l8, w8, f8⟩ := cMulConst_spec hN (m : ZMod (2 ^ B)) v7 (w5.extends (e6.trans e7))
  rw [← hr8] at v8 e8 l8 w8 f8
  set r9 := cSub N0 B r7.2 r8.2 r8.1 with hr9
  obtain ⟨v9, e9, l9, w9, f9⟩ := cSub_spec hN v8 (w7.extends e8) w8
  rw [← hr9] at v9 e9 l9 w9 f9
  set r10 := cAdd N0 B r9.2 r5.2 r9.1 with hr10
  obtain ⟨v10, e10, l10, w10, f10⟩ := cAdd_spec hN v9 w9 (w5.extends (e6.trans (e7.trans (e8.trans e9))))
  rw [← hr10] at v10 e10 l10 w10 f10
  set r11 := cSub N0 B d0 r9.2 r10.1 with hr11
  obtain ⟨v11, e11, l11, w11, f11⟩ := cSub_spec hN v10
    (hd0.extends (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans e10)))))))
    (w9.extends e10)
  rw [← hr11] at v11 e11 l11 w11 f11
  set r12 := cSub N0 B r11.2 r10.2 r11.1 with hr12
  obtain ⟨v12, e12, l12, w12, f12⟩ := cSub_spec hN v11 w11 (w10.extends e11)
  rw [← hr12] at v12 e12 l12 w12 f12
  have e412 : Extends gs r12.1 := e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans (e10.trans (e11.trans e12)))))))
  set r13 := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l (m - 1)) (fUV n B l (m - 1)) r9.2 R Puv r12.1 with hr13
  obtain ⟨v13, e13', l13, w13R, w13P, f13⟩ := cDecodeSignedStep_spec hN hB_ge
    (fZT n B l (m - 1)) (fUV n B l (m - 1)) v12 (w9.extends (e10.trans (e11.trans e12)))
    (hR.extends e412) (hP.extends e412)
  rw [← hr13] at v13 e13' l13 w13R w13P f13
  set r14 := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l m) (fUV n B l m) r12.2 r13.2.1 r13.2.2 r13.1 with hr14
  obtain ⟨v14, e14, l14, w14R, w14P, f14⟩ := cDecodeSignedStep_spec hN hB_ge
    (fZT n B l m) (fUV n B l m) v13 (w12.extends e13') w13R w13P
  rw [← hr14] at v14 e14 l14 w14R w14P f14
  set r15 := cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B K hB_ge
    (fZT n B l (m + 1)) (fUV n B l (m + 1)) r10.2 r14.2.1 r14.2.2 r14.1 with hr15
  obtain ⟨v15, e15, l15, w15R, w15P, f15⟩ := cDecodeSignedStep_spec hN hB_ge
    (fZT n B l (m + 1)) (fUV n B l (m + 1)) v14
    (w10.extends (e11.trans (e12.trans (e13'.trans e14)))) w14R w14P
  rw [← hr15] at v15 e15 l15 w15R w15P f15
  have hcostZT : K * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B * B + 13 * B)))) + 3 * ((2 * n + 1) * (4 * B))) = costZT_step n := by
    unfold costZT_step; dsimp only [K]; rw [hB]
  have hcostUV : K * ((n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) + (n + 1) * ((n + 1) * (4 * B))) = costUV_step n := by
    unfold costUV_step; dsimp only [K]; rw [hB]
  have hres : cFalseStep2Mod4 n B l hB_ge d0 d1 d2 R Puv gs = r15 := rfl
  dsimp only
  rw [hres]
  refine ⟨v15, e412.trans (e13'.trans (e14.trans e15)),
    by rw [hcostZT, hcostUV] at l13 l14 l15; omega, w15R, w15P,
    fun σ p hd0v hd1v hd2v hReq hPeq => ?_⟩
  have hc := inputBits_hasConsts false σ p
  have hall : (allowedR l).toFinset = {m - 1, m, m + 1} := by ext x; simp [allowedR, l, hodd, h4, m]
  have hne1 : m - 1 ∉ ({m, m + 1} : Finset ℕ) := by simp; omega
  have hne2 : m ≠ m + 1 := by omega
  rw [hall, Finset.sum_insert hne1, Finset.sum_pair hne2] at hd0v hd1v hd2v
  simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul] at hd0v hd1v
  have hsol := solve_false_2mod4 (R := ZMod (2 ^ B)) m hm1
    (cTarget σ p l (m - 1) : ZMod (2 ^ B)) (cTarget σ p l m : ZMod (2 ^ B)) (cTarget σ p l (m + 1) : ZMod (2 ^ B))
  have hd0' : wordZMod gs (inputBits false σ p) d0 =
      (cTarget σ p l (m - 1) : ZMod (2 ^ B)) + (cTarget σ p l m : ZMod (2 ^ B)) + (cTarget σ p l (m + 1) : ZMod (2 ^ B)) := by
    rw [hd0v]; ring
  have hd1' : wordZMod gs (inputBits false σ p) d1 =
      ((m - 1 : ℕ) : ZMod (2 ^ B)) * (cTarget σ p l (m - 1) : ZMod (2 ^ B)) +
      (m : ZMod (2 ^ B)) * (cTarget σ p l m : ZMod (2 ^ B)) +
      ((m + 1 : ℕ) : ZMod (2 ^ B)) * (cTarget σ p l (m + 1) : ZMod (2 ^ B)) := by
    rw [hd1v]; ring
  have hd2' : wordZMod gs (inputBits false σ p) d2 =
      (Nat.choose (m - 1) 2 : ZMod (2 ^ B)) * (cTarget σ p l (m - 1) : ZMod (2 ^ B)) +
      (Nat.choose m 2 : ZMod (2 ^ B)) * (cTarget σ p l m : ZMod (2 ^ B)) +
      (Nat.choose (m + 1) 2 : ZMod (2 ^ B)) * (cTarget σ p l (m + 1) : ZMod (2 ^ B)) := by
    rw [hd2v]; ring
  have hdiff_val : wordZMod r5.1 (inputBits false σ p) r5.2 =
      wordZMod gs (inputBits false σ p) d1 - (m : ZMod (2 ^ B)) * wordZMod gs (inputBits false σ p) d0 := by
    rw [f5 _ hc, wordZMod_extends e4 hc.1 hd1, f4 _ hc]
  have hcm1_val : wordZMod r9.1 (inputBits false σ p) r9.2 = (cTarget σ p l (m - 1) : ZMod (2 ^ B)) := by
    rw [f9 _ hc, wordZMod_extends e8 hc.1 w7, f7 _ hc,
      wordZMod_extends (e4.trans (e5.trans e6)) hc.1 hd2, f6 _ hc,
      wordZMod_extends (e4.trans e5) hc.1 hd0,
      f8 _ hc, wordZMod_extends (e6.trans e7) hc.1 w5, hdiff_val, hd0', hd1', hd2']
    exact hsol.1
  have hcp1_val : wordZMod r10.1 (inputBits false σ p) r10.2 = (cTarget σ p l (m + 1) : ZMod (2 ^ B)) := by
    rw [f10 _ hc, hcm1_val, wordZMod_extends (e6.trans (e7.trans (e8.trans e9))) hc.1 w5, hdiff_val]
    have hstep : (cTarget σ p l (m - 1) : ZMod (2 ^ B)) =
        wordZMod gs (inputBits false σ p) d2 -
        (Nat.choose m 2 : ZMod (2 ^ B)) * wordZMod gs (inputBits false σ p) d0 -
        (m : ZMod (2 ^ B)) * (wordZMod gs (inputBits false σ p) d1 -
          (m : ZMod (2 ^ B)) * wordZMod gs (inputBits false σ p) d0) := by
      rw [hd0', hd1', hd2']; exact hsol.1.symm
    rw [hstep, hd0', hd1', hd2']
    exact hsol.2.2
  have hc0_val : wordZMod r12.1 (inputBits false σ p) r12.2 = (cTarget σ p l m : ZMod (2 ^ B)) := by
    rw [f12 _ hc, f11 _ hc,
      wordZMod_extends (e4.trans (e5.trans (e6.trans (e7.trans (e8.trans (e9.trans e10)))))) hc.1 hd0,
      wordZMod_extends e10 hc.1 w9, wordZMod_extends e11 hc.1 w10, hcm1_val, hcp1_val, hd0']
    ring
  obtain ⟨hbl1, hbu1⟩ := cTarget_in_signed_range hB σ p l (m - 1)
  obtain ⟨hbl2, hbu2⟩ := cTarget_in_signed_range hB σ p l m
  obtain ⟨hbl3, hbu3⟩ := cTarget_in_signed_range hB σ p l (m + 1)
  obtain ⟨hR13, hP13⟩ := f13 _ hc (cTarget σ p l (m - 1))
    (by rw [wordZMod_extends (e10.trans (e11.trans e12)) hc.1 w9, hcm1_val])
    hbl1 hbu1 (natAbs_cTarget_lt_two_pow_K hn σ p l (m - 1))
  obtain ⟨hR14, hP14⟩ := f14 _ hc (cTarget σ p l m)
    (by rw [wordZMod_extends e13' hc.1 w12, hc0_val])
    hbl2 hbu2 (natAbs_cTarget_lt_two_pow_K hn σ p l m)
  obtain ⟨hR15, hP15⟩ := f15 _ hc (cTarget σ p l (m + 1))
    (by rw [wordZMod_extends (e11.trans (e12.trans (e13'.trans e14))) hc.1 w10, hcp1_val])
    hbl3 hbu3 (natAbs_cTarget_lt_two_pow_K hn σ p l (m + 1))
  rw [trunc2Val_extends e412 hc.1 hR, hReq] at hR13
  rw [trunc2Val_extends e412 hc.1 hP, hPeq] at hP13
  rw [hR13] at hR14; rw [hP13] at hP14
  rw [hR14] at hR15; rw [hP14] at hP15
  rw [hR15, hP15, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc]
  have hprodR : Trunc2.zpowOneSub (fZT n B l (m + 1)) (-cTarget σ p l (m + 1)) *
      Trunc2.zpowOneSub (fZT n B l m) (-cTarget σ p l m) *
      Trunc2.zpowOneSub (fZT n B l (m - 1)) (-cTarget σ p l (m - 1)) =
      ∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fZT n B l r) (-cTarget σ p l r) := by
    rw [hall, Finset.prod_insert hne1, Finset.prod_pair hne2]; ring
  have hprodP : Trunc2.zpowOneSub (fUV n B l (m + 1)) (cTarget σ p l (m + 1)) *
      Trunc2.zpowOneSub (fUV n B l m) (cTarget σ p l m) *
      Trunc2.zpowOneSub (fUV n B l (m - 1)) (cTarget σ p l (m - 1)) =
      ∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fUV n B l r) (cTarget σ p l r) := by
    rw [hall, Finset.prod_insert hne1, Finset.prod_pair hne2]; ring
  rw [hprodR, hprodP]
  exact ⟨tailZT_false_peel σ p idx, prefUV_false_step σ p idx⟩

def cStage2FalseStep (n B : ℕ) (hB_ge : 2 ≤ B) (idx : Fin (2 * n))
    (st : Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) :
    List Gate × (Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B) :=
  let N0 := N_in n false
  let l := idx.val + 1
  let (g1, d0) := cNeg N0 B (st.1 0 ⟨l, by omega⟩) gs
  let (g2, d1) := cNeg N0 B (st.1 1 ⟨l, by omega⟩) g1
  let (g3, d2) := cNeg N0 B (st.1 2 ⟨l, by omega⟩) g2
  if l % 2 = 1 then cFalseStepOdd n B l hB_ge d0 d1 st.1 st.2 g3
  else if l % 4 = 0 then
    cDecodeSignedStep N0 (2 * n + 1) (n + 1) (n + 1) B (n + 2) hB_ge
      (fZT n B l (l / 2)) (fUV n B l (l / 2)) d0 st.1 st.2 g3
  else cFalseStep2Mod4 n B l hB_ge d0 d1 d2 st.1 st.2 g3

lemma cStage2FalseStep_spec (n B : ℕ) (hn : 1 ≤ n) (hB_ge : 2 ≤ B) (hB : B = 2 * n + 10)
    (idx : Fin (2 * n))
    {st : Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B}
    {gs : List Gate} (hgs : ValidCircuit (N_in n false) gs)
    (hR : ValidTrunc2 (N_in n false) gs st.1) (hP : ValidTrunc2 (N_in n false) gs st.2) :
    let N0 := N_in n false
    let r := cStage2FalseStep n B hB_ge idx st gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + costStepFalse n ∧
    ValidTrunc2 N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      trunc2Val gs (inputBits false σ p) st.1 = tailZT_false n B σ p idx.val →
      trunc2Val gs (inputBits false σ p) st.2 = prefUV_false n B σ p idx.val →
      trunc2Val r.1 (inputBits false σ p) r.2.1 = tailZT_false n B σ p (idx.val + 1) ∧
      trunc2Val r.1 (inputBits false σ p) r.2.2 = prefUV_false n B σ p (idx.val + 1) := by
  intro N0
  dsimp only [cStage2FalseStep]
  set l := idx.val + 1
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have hcostStep : 3 * (14 * B) + 6 * (13 * B * B + 14 * B) + 3 * (26 * B + 2 * costZT_step n + 2 * costUV_step n) = costStepFalse n := by
    unfold costStepFalse; rw [hB]
  set r1 := cNeg N0 B (st.1 0 ⟨l, by omega⟩) gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNeg_spec hN hgs (hR 0 ⟨l, by omega⟩)
  rw [← hr1] at v1 e1 l1 w1 f1
  set r2 := cNeg N0 B (st.1 1 ⟨l, by omega⟩) r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cNeg_spec hN v1 ((hR 1 ⟨l, by omega⟩).extends e1)
  rw [← hr2] at v2 e2 l2 w2 f2
  set r3 := cNeg N0 B (st.1 2 ⟨l, by omega⟩) r2.1 with hr3
  obtain ⟨v3, e3, l3, w3, f3⟩ := cNeg_spec hN v2 ((hR 2 ⟨l, by omega⟩).extends (e1.trans e2))
  rw [← hr3] at v3 e3 l3 w3 f3
  have e13 : Extends gs r3.1 := e1.trans (e2.trans e3)
  have hd_val : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      trunc2Val gs (inputBits false σ p) st.1 = tailZT_false n B σ p idx.val →
      wordZMod r3.1 (inputBits false σ p) r1.2 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 0 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) ∧
      wordZMod r3.1 (inputBits false σ p) r2.2 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 1 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) ∧
      wordZMod r3.1 (inputBits false σ p) r3.2 =
        (∑ r' ∈ (allowedR l).toFinset, (Nat.choose r' 2 : ZMod (2 ^ B)) * (cTarget σ p l r' : ZMod (2 ^ B))) := by
    intro σ p hReq
    have hc := inputBits_hasConsts false σ p
    have hcoeff : ∀ h : Fin 3, wordZMod gs (inputBits false σ p) (st.1 h ⟨l, by omega⟩) =
        ∑ r' ∈ (allowedR l).toFinset, -(cTarget σ p l r' : ZMod (2 ^ B)) * (Nat.choose r' h.val : ZMod (2 ^ B)) := by
      intro h
      have := congrArg (fun P => P.coeff h ⟨l, by omega⟩) hReq
      rw [tailZT_false_coeff] at this
      exact this
    refine ⟨?_, ?_, ?_⟩
    · rw [wordZMod_extends (e2.trans e3) hc.1 w1, f1 _ hc, hcoeff 0, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r' _ => by simp
    · rw [wordZMod_extends e3 hc.1 w2, f2 _ hc, wordZMod_extends e1 hc.1 (hR 1 _), hcoeff 1, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r' _ => by simp; ring
    · rw [f3 _ hc, wordZMod_extends (e1.trans e2) hc.1 (hR 2 _), hcoeff 2, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r' _ => by simp; ring
  split_ifs with hodd h4
  · obtain ⟨v4, e4, l4, w4R, w4P, f4⟩ := cFalseStepOdd_spec n B hn hB_ge hB idx hodd v3
      (w1.extends (e2.trans e3)) (w2.extends e3) (hR.extends e13) (hP.extends e13)
    refine ⟨v4, e13.trans e4, by omega, w4R, w4P,
      fun σ p hReq hPeq => ?_⟩
    have hc := inputBits_hasConsts false σ p
    obtain ⟨hd0, hd1, _⟩ := hd_val σ p hReq
    exact f4 σ p hd0 hd1 (by rw [trunc2Val_extends e13 hc.1 hR, hReq]) (by rw [trunc2Val_extends e13 hc.1 hP, hPeq])
  · obtain ⟨v4, e4, l4, w4R, w4P, f4⟩ := cDecodeSignedStep_spec hN hB_ge
      (fZT n B l (l / 2)) (fUV n B l (l / 2)) v3 (w1.extends (e2.trans e3)) (hR.extends e13) (hP.extends e13)
    have hcostZT : (n + 2) * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B * B + 13 * B)))) + 3 * ((2 * n + 1) * (4 * B))) = costZT_step n := by
      unfold costZT_step; rw [hB]
    have hcostUV : (n + 2) * ((n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) + (n + 1) * ((n + 1) * (4 * B))) = costUV_step n := by
      unfold costUV_step; rw [hB]
    refine ⟨v4, e13.trans e4, by rw [hcostZT, hcostUV] at l4; dsimp only [N0, l] at l4; omega, w4R, w4P,
      fun σ p hReq hPeq => ?_⟩
    have hc := inputBits_hasConsts false σ p
    have hall : (allowedR l).toFinset = {l / 2} := by ext x; simp [allowedR, l, hodd, h4]
    obtain ⟨hd0, _, _⟩ := hd_val σ p hReq
    rw [hall, Finset.sum_singleton] at hd0
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at hd0
    obtain ⟨hb0l, hb0u⟩ := cTarget_in_signed_range hB σ p l (l / 2)
    obtain ⟨hR4, hP4⟩ := f4 _ hc (cTarget σ p l (l / 2)) hd0 hb0l hb0u (natAbs_cTarget_lt_two_pow_K hn σ p l (l / 2))
    rw [trunc2Val_extends e13 hc.1 hR, hReq] at hR4
    rw [trunc2Val_extends e13 hc.1 hP, hPeq] at hP4
    rw [hR4, hP4]
    have hprodR : Trunc2.zpowOneSub (fZT n B l (l / 2)) (-cTarget σ p l (l / 2)) =
        ∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fZT n B l r) (-cTarget σ p l r) := by
      rw [hall, Finset.prod_singleton]
    have hprodP : Trunc2.zpowOneSub (fUV n B l (l / 2)) (cTarget σ p l (l / 2)) =
        ∏ r ∈ (allowedR l).toFinset, Trunc2.zpowOneSub (fUV n B l r) (cTarget σ p l r) := by
      rw [hall, Finset.prod_singleton]
    rw [hprodR, hprodP]
    exact ⟨tailZT_false_peel σ p idx, prefUV_false_step σ p idx⟩
  · obtain ⟨v4, e4, l4, w4R, w4P, f4⟩ := cFalseStep2Mod4_spec n B hn hB_ge hB idx hodd h4 v3
      (w1.extends (e2.trans e3)) (w2.extends e3) w3 (hR.extends e13) (hP.extends e13)
    refine ⟨v4, e13.trans e4, by omega, w4R, w4P,
      fun σ p hReq hPeq => ?_⟩
    have hc := inputBits_hasConsts false σ p
    obtain ⟨hd0, hd1, hd2⟩ := hd_val σ p hReq
    exact f4 σ p hd0 hd1 hd2 (by rw [trunc2Val_extends e13 hc.1 hR, hReq]) (by rw [trunc2Val_extends e13 hc.1 hP, hPeq])

def cStage2False (n B : ℕ) (hB_ge : 2 ≤ B) (F_zt : Trunc2Wire 3 (2 * n + 1) B) (gs : List Gate) :
    List Gate × Trunc2Wire (n + 1) (n + 1) B :=
  let r := cFoldFin (2 * n) (cStage2FalseStep n B hB_ge) (F_zt, cTrunc2One (n + 1) (n + 1) B) gs
  (r.1, r.2.2)

lemma cStage2False_spec (n B : ℕ) (hn : 1 ≤ n) (hB_ge : 2 ≤ B) (hB : B = 2 * n + 10)
    {F_zt : Trunc2Wire 3 (2 * n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n false) gs) (hF : ValidTrunc2 (N_in n false) gs F_zt)
    (hF_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      trunc2Val gs (inputBits false σ p) F_zt = arcProdZT (R := ZMod (2 ^ B)) σ p) :
    let N0 := N_in n false
    let r := cStage2False n B hB_ge F_zt gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + (2 * n) * costStepFalse n ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      trunc2Val r.1 (inputBits false σ p) r.2 = arcProdUV (R := ZMod (2 ^ B)) σ p := by
  intro N0
  dsimp only [cStage2False]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have h := cFoldFin_spec (N0 := N0) (2 * n) (costStepFalse n) (cStage2FalseStep n B hB_ge)
    (fun k _ g st => ValidTrunc2 N0 g st.1 ∧ ValidTrunc2 N0 g st.2 ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
        trunc2Val g (inputBits false σ p) st.1 = tailZT_false n B σ p k ∧
        trunc2Val g (inputBits false σ p) st.2 = prefUV_false n B σ p k)
    (F_zt, cTrunc2One (n + 1) (n + 1) B) gs hgs
    ⟨hF, validTrunc2_cTrunc2One hN gs (n + 1) (n + 1) B, fun σ p =>
      ⟨by rw [hF_sem σ p, arcProdZT_eq_cTarget]; rfl,
       by rw [trunc2Val_cTrunc2One (inputBits_hasConsts false σ p)]; simp [prefUV_false]⟩⟩
    (fun idx gs1 st hv _ ⟨hR1, hP1, hsem⟩ => by
      obtain ⟨v1, e1, l1, w1R, w1P, f1⟩ := cStage2FalseStep_spec n B hn hB_ge hB idx hv hR1 hP1
      exact ⟨v1, e1, l1, w1R, w1P, fun σ p => f1 σ p (hsem σ p).1 (hsem σ p).2⟩)
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, fun σ p => ?_⟩
  rw [(h.2.2.2.2.2 σ p).2, arcProdUV_eq_cTarget]; rfl

lemma arcProdZT_eq_pm {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    arcProdZT (R := ZMod (2 ^ B)) σ p =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset,
        (1 + fZT n B l r) ^ arcCountPlus σ p l r * (1 - fZT n B l r) ^ arcCountMinus σ p l r := by
  unfold arcProdZT
  rw [arcProd_eq_pm]
  refine Finset.prod_congr rfl fun l hl => Finset.prod_congr rfl fun r hr => ?_
  rw [zt_monom_eq (r_le_l_of_primR (Finset.mem_Icc.mp hl).1 (List.mem_toFinset.mp hr))]

lemma arcProdUV_eq_pm {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) :
    arcProdUV (R := ZMod (2 ^ B)) σ p =
      ∏ l ∈ Finset.Icc 1 (2 * n), ∏ r ∈ (primR l).toFinset,
        (1 + fUV n B l r) ^ arcCountPlus σ p l r * (1 - fUV n B l r) ^ arcCountMinus σ p l r := by
  unfold arcProdUV
  rw [arcProd_eq_pm]; rfl

lemma arcCountAll_lt_two_pow_K {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (l r : ℕ) :
    arcCountAll σ p l r < 2 ^ (n + 2) := by
  have h1 := arcCountAll_le σ p l r
  have h2 : n < 2 ^ n := Nat.lt_two_pow_self
  have hpow : 2 ^ (n + 2) = 4 * 2 ^ n := by rw [pow_add]; ring
  omega

lemma two_mul_nat_lt_two_pow_B {n B : ℕ} (hB : B = 2 * n + 10) (e : ℕ) (he : e ≤ 4 * n * n) :
    2 * e < 2 ^ B := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : n * n < 2 ^ (2 * n) := by
    have : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by rw [← pow_add, two_mul]
    rw [this]; exact Nat.mul_lt_mul'' h1 h1
  have h3 : 2 ^ B = 1024 * 2 ^ (2 * n) := by rw [hB, pow_add]; ring
  have h4 : 4 * n * n = 4 * (n * n) := by ring
  omega

def tailZT_true (n B : ℕ) (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : ℕ) :
    Trunc2 3 (2 * n + 1) (ZMod (2 ^ B)) :=
  ∏ l ∈ Finset.Icc (k + 1) (2 * n), ∏ r ∈ (primR l).toFinset,
    ((1 - fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) ^ arcCountMinus σ p l r

def prefUV_true (n B : ℕ) (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : ℕ) :
    Trunc2 (n + 1) (n + 1) (ZMod (2 ^ B)) :=
  ∏ l ∈ Finset.Icc 1 k, ∏ r ∈ (primR l).toFinset,
    (1 + fUV n B l r) ^ arcCountPlus σ p l r * (1 - fUV n B l r) ^ arcCountMinus σ p l r

lemma tailZT_true_coeff {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (idx : Fin (2 * n)) (h : Fin 3) :
    let l := idx.val + 1
    (tailZT_true n B σ p idx.val).coeff h ⟨l, by omega⟩ =
      ∑ r ∈ (primR l).toFinset,
        -(2 * (arcCountMinus σ p l r : ZMod (2 ^ B)) * (Nat.choose r h.val : ZMod (2 ^ B))) := by
  intro l
  unfold tailZT_true
  have houter := tail_coeff_finset_prod (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (l := l) (by omega) (by omega)
    (Finset.Icc l (2 * n))
    (fun l' => ∏ r ∈ (primR l').toFinset, ((1 - fZT n B l' r) * Trunc2.invOneAdd (fZT n B l' r)) ^ arcCountMinus σ p l' r)
    (fun l' hl' => (tail_coeff_finset_prod (by omega) (by omega) (primR l').toFinset
      (fun r => ((1 - fZT n B l' r) * Trunc2.invOneAdd (fZT n B l' r)) ^ arcCountMinus σ p l' r)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).1)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).2.1)).1)
    (fun l' hl' => (tail_coeff_finset_prod (by omega) (by omega) (primR l').toFinset
      (fun r => ((1 - fZT n B l' r) * Trunc2.invOneAdd (fZT n B l' r)) ^ arcCountMinus σ p l' r)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).1)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).2.1)).2.1)
  rw [houter.2.2 h]
  have hmem : l ∈ Finset.Icc l (2 * n) := Finset.mem_Icc.mpr ⟨le_refl l, idx.isLt⟩
  rw [Finset.sum_eq_single l]
  · have hinner := tail_coeff_finset_prod (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (l := l) (by omega) (by omega)
      (primR l).toFinset (fun r => ((1 - fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) ^ arcCountMinus σ p l r)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (le_refl l) (by omega) _).1)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (le_refl l) (by omega) _).2.1)
    rw [hinner.2.2 h]
    refine Finset.sum_congr rfl fun r _ => ?_
    simpa [fZT] using (tail_coeff_ratio_zt (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (r := r) (by omega) (le_refl l) (by omega) (arcCountMinus σ p l r)).2.2 h
  · intro l' hl' hne
    have hinner := tail_coeff_finset_prod (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (l := l) (by omega) (by omega)
      (primR l').toFinset (fun r => ((1 - fZT n B l' r) * Trunc2.invOneAdd (fZT n B l' r)) ^ arcCountMinus σ p l' r)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).1)
      (fun r _ => (tail_coeff_ratio_zt (by omega) (Finset.mem_Icc.mp hl').1 (by omega) _).2.1)
    rw [hinner.2.2 h]
    refine Finset.sum_eq_zero fun r _ => ?_
    simpa [fZT, hne] using (tail_coeff_ratio_zt (D2 := 2 * n + 1) (R := ZMod (2 ^ B)) (r := r) (by omega) (Finset.mem_Icc.mp hl').1 (by omega) (arcCountMinus σ p l' r)).2.2 h
  · intro h0; exact absurd hmem h0

lemma tailZT_true_peel {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (idx : Fin (2 * n)) :
    let l := idx.val + 1
    (∏ r ∈ (primR l).toFinset, ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r)) ^ arcCountMinus σ p l r) *
      tailZT_true n B σ p idx.val = tailZT_true n B σ p (idx.val + 1) := by
  intro l
  unfold tailZT_true
  have hsplit : Finset.Icc l (2 * n) = insert l (Finset.Icc (l + 1) (2 * n)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : l ∉ Finset.Icc (l + 1) (2 * n) := by simp
  rw [hsplit, Finset.prod_insert hnot, ← mul_assoc, ← Finset.prod_mul_distrib]
  have hone : (∏ r ∈ (primR l).toFinset,
      ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r)) ^ arcCountMinus σ p l r *
      ((1 - fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) ^ arcCountMinus σ p l r) = 1 := by
    refine Finset.prod_eq_one fun r _ => ?_
    rw [← mul_pow]
    have h1 : ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r)) *
        ((1 - fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) =
        ((1 + fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) *
        ((1 - fZT n B l r) * Trunc2.invOneSub (fZT n B l r)) := by ring
    rw [h1, Trunc2.one_add_mul_invOneAdd _ (fZT_zero_const (by omega)),
      Trunc2.one_sub_mul_invOneSub _ (fZT_zero_const (by omega)), one_mul, one_pow]
  rw [hone, one_mul]

lemma prefUV_true_step {n B : ℕ} (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool)
    (idx : Fin (2 * n)) :
    let l := idx.val + 1
    (∏ r ∈ (primR l).toFinset,
      (1 + fUV n B l r) ^ arcCountPlus σ p l r * (1 - fUV n B l r) ^ arcCountMinus σ p l r) *
      prefUV_true n B σ p idx.val = prefUV_true n B σ p (idx.val + 1) := by
  intro l
  unfold prefUV_true
  have hsplit : Finset.Icc 1 l = insert l (Finset.Icc 1 idx.val) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : l ∉ Finset.Icc 1 idx.val := by simp [l]
  rw [hsplit, Finset.prod_insert hnot]

def cTrueDivBaseStep (n B : ℕ) (A : Fin (2 * n + 1) → Fin (n + 1) → Word B)
    (idx : Fin (2 * n)) (S : Trunc2Wire 3 (2 * n + 1) B) (gs : List Gate) :
    List Gate × Trunc2Wire 3 (2 * n + 1) B :=
  let N0 := N_in n true
  let K := n + 2
  let l := idx.val + 1
  let m := l / 2
  if hodd : l % 2 = 1 then
    let a0 := cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m, by omega⟩)
    let a1 := cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m + 1, by omega⟩)
    let (g1, S1) := cTrunc2MulPowConst N0 3 (2 * n + 1) B K (Trunc2.invOneAdd (fZT n B l m)) a0 S gs
    cTrunc2MulPowConst N0 3 (2 * n + 1) B K (Trunc2.invOneAdd (fZT n B l (m + 1))) a1 S1 g1
  else
    let a0 := cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m, by omega⟩)
    cTrunc2MulPowConst N0 3 (2 * n + 1) B K (Trunc2.invOneAdd (fZT n B l m)) a0 S gs

lemma cTrueDivBaseStep_spec (n B : ℕ) (hB : B = 2 * n + 10)
    {A : Fin (2 * n + 1) → Fin (n + 1) → Word B}
    (idx : Fin (2 * n)) {S : Trunc2Wire 3 (2 * n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n true) gs)
    (hA : ∀ l r, ValidWord (N_in n true) gs (A l r))
    (hS : ValidTrunc2 (N_in n true) gs S) :
    let N0 := N_in n true
    let l := idx.val + 1
    let r := cTrueDivBaseStep n B A idx S gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 2 * costZT_step n ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ l' r', wordNat gs (inputBits true σ p) (A l' r') = arcCountAll σ p l'.val r'.val) →
      trunc2Val r.1 (inputBits true σ p) r.2 =
        (∏ r' ∈ (primR l).toFinset, (Trunc2.invOneAdd (fZT n B l r')) ^ arcCountAll σ p l r') *
          trunc2Val gs (inputBits true σ p) S := by
  intro N0 l
  dsimp only [cTrueDivBaseStep]
  set K := n + 2
  set m := l / 2
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have hcostZT : K * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B * B + 13 * B)))) + 3 * ((2 * n + 1) * (4 * B))) = costZT_step n := by
    unfold costZT_step; dsimp only [K]; rw [hB]
  split_ifs with hodd
  · have ha0 : ValidWord N0 gs (cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m, by omega⟩)) :=
      validWord_cShiftRightResize hN 0 (hA _ _)
    have ha1 : ValidWord N0 gs (cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m + 1, by omega⟩)) :=
      validWord_cShiftRightResize hN 0 (hA _ _)
    set r1 := cTrunc2MulPowConst N0 3 (2 * n + 1) B K (Trunc2.invOneAdd (fZT n B l m))
      (cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m, by omega⟩)) S gs with hr1
    obtain ⟨v1, e1, l1, w1, f1⟩ := cTrunc2MulPowConst_spec hN (Trunc2.invOneAdd (fZT n B l m)) hgs ha0 hS
    rw [← hr1] at v1 e1 l1 w1 f1
    obtain ⟨v2, e2, l2, w2, f2⟩ := cTrunc2MulPowConst_spec hN (Trunc2.invOneAdd (fZT n B l (m + 1))) v1 (ha1.extends e1) w1
    refine ⟨v2, e1.trans e2, by linarith, w2, fun σ p hAval => ?_⟩
    have hc := inputBits_hasConsts true σ p
    rw [f2 _ hc, f1 _ hc, wordNat_extends e1 hc.1 ha1,
      wordNat_cShiftRightResize hc, wordNat_cShiftRightResize hc,
      pow_zero, Nat.div_one, Nat.div_one, hAval, hAval,
      Nat.mod_eq_of_lt (arcCountAll_lt_two_pow_K σ p l m),
      Nat.mod_eq_of_lt (arcCountAll_lt_two_pow_K σ p l (m + 1)), ← mul_assoc]
    have hodd' : l % 2 = 1 := hodd
    have hpr : (primR l).toFinset = {m, m + 1} := by ext x; simp [primR, hodd', m]
    rw [hpr, Finset.prod_pair (by omega : m ≠ m + 1), mul_comm ((Trunc2.invOneAdd (fZT n B l (m + 1))) ^ _)]
  · have ha0 : ValidWord N0 gs (cShiftRightResize B K 0 (A ⟨l, by omega⟩ ⟨m, by omega⟩)) :=
      validWord_cShiftRightResize hN 0 (hA _ _)
    obtain ⟨v1, e1, l1, w1, f1⟩ := cTrunc2MulPowConst_spec hN (Trunc2.invOneAdd (fZT n B l m)) hgs ha0 hS
    refine ⟨v1, e1, by linarith, w1, fun σ p hAval => ?_⟩
    have hc := inputBits_hasConsts true σ p
    rw [f1 _ hc, wordNat_cShiftRightResize hc, pow_zero, Nat.div_one, hAval,
      Nat.mod_eq_of_lt (arcCountAll_lt_two_pow_K σ p l m)]
    have hodd' : ¬ l % 2 = 1 := hodd
    have hpr : (primR l).toFinset = {m} := by ext x; simp [primR, hodd', m]
    rw [hpr, Finset.prod_singleton]

def cTrueDivBase (n B : ℕ) (A : Fin (2 * n + 1) → Fin (n + 1) → Word B)
    (F_zt : Trunc2Wire 3 (2 * n + 1) B) (gs : List Gate) :
    List Gate × Trunc2Wire 3 (2 * n + 1) B :=
  cFoldFin (2 * n) (cTrueDivBaseStep n B A) F_zt gs

lemma cTrueDivBase_spec (n B : ℕ) (hB : B = 2 * n + 10)
    {A : Fin (2 * n + 1) → Fin (n + 1) → Word B}
    {F_zt : Trunc2Wire 3 (2 * n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n true) gs)
    (hA : ∀ l r, ValidWord (N_in n true) gs (A l r))
    (hF : ValidTrunc2 (N_in n true) gs F_zt) :
    let N0 := N_in n true
    let r := cTrueDivBase n B A F_zt gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + (2 * n) * (2 * costZT_step n) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ l' r', wordNat gs (inputBits true σ p) (A l' r') = arcCountAll σ p l'.val r'.val) →
      (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val gs (inputBits true σ p) F_zt).coeff h d = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d) →
      ∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val r.1 (inputBits true σ p) r.2).coeff h d = (tailZT_true n B σ p 0).coeff h d := by
  intro N0
  dsimp only [cTrueDivBase]
  have hfold := cFoldFin_spec (N0 := N0) (2 * n) (2 * costZT_step n) (cTrueDivBaseStep n B A)
    (fun k _ g S => ValidTrunc2 N0 g S ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
        (∀ l' r', wordNat gs (inputBits true σ p) (A l' r') = arcCountAll σ p l'.val r'.val) →
        trunc2Val g (inputBits true σ p) S =
          (∏ l ∈ Finset.Icc 1 k, ∏ r' ∈ (primR l).toFinset, (Trunc2.invOneAdd (fZT n B l r')) ^ arcCountAll σ p l r') *
            trunc2Val gs (inputBits true σ p) F_zt)
    F_zt gs hgs
    ⟨hF, fun _ _ _ => by simp⟩
    (fun idx gs1 S hv he ⟨hS1, hsem⟩ => by
      obtain ⟨v1, e1, l1, w1, f1⟩ := cTrueDivBaseStep_spec n B hB idx hv (fun l r => (hA l r).extends he) hS1
      refine ⟨v1, e1, l1, w1, fun σ p hAval => ?_⟩
      rw [f1 σ p (fun l' r' => by rw [wordNat_extends he (inputBits_hasConsts true σ p).1 (hA l' r'), hAval]),
        hsem σ p hAval, ← mul_assoc]
      congr 1
      have hsplit : Finset.Icc 1 (idx.val + 1) = insert (idx.val + 1) (Finset.Icc 1 idx.val) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : idx.val + 1 ∉ Finset.Icc 1 idx.val := by simp
      rw [hsplit, Finset.prod_insert hnot])
  refine ⟨hfold.1, hfold.2.1, hfold.2.2.1, hfold.2.2.2.1, fun σ p hAval hF01 h hh2 d => ?_⟩
  rw [hfold.2.2.2.2 σ p hAval]
  rw [trunc2_mul_congr_lt 2 _ _ (arcProdZT (R := ZMod (2 ^ B)) σ p) hF01 h hh2 d]
  congr 2
  rw [arcProdZT_eq_pm, ← Finset.prod_mul_distrib]
  unfold tailZT_true
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [← arcCountPlus_add_minus σ p l r, pow_add]
  have h1 : (Trunc2.invOneAdd (fZT n B l r)) ^ arcCountPlus σ p l r *
      (Trunc2.invOneAdd (fZT n B l r)) ^ arcCountMinus σ p l r *
      ((1 + fZT n B l r) ^ arcCountPlus σ p l r * (1 - fZT n B l r) ^ arcCountMinus σ p l r) =
      ((1 + fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) ^ arcCountPlus σ p l r *
      ((1 - fZT n B l r) * Trunc2.invOneAdd (fZT n B l r)) ^ arcCountMinus σ p l r := by
    rw [mul_pow, mul_pow]; ring
  rw [h1, Trunc2.one_add_mul_invOneAdd _ (fZT_zero_const (Finset.mem_Icc.mp hl).1), one_pow, one_mul]

def cTrueUpdateOne (n B l r : ℕ) (nmW A_lr : Word B)
    (S : Trunc2Wire 3 (2 * n + 1) B) (Puv : Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) :
    List Gate × (Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B) :=
  let N0 := N_in n true
  let K := n + 2
  let r1 := cSub N0 B A_lr nmW gs
  let nmK := cShiftRightResize B K 0 nmW
  let npK := cShiftRightResize B K 0 r1.2
  let r2 := cTrunc2MulPowConst N0 3 (2 * n + 1) B K ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r)) nmK S r1.1
  let r3 := cTrunc2MulPowConst N0 (n + 1) (n + 1) B K (1 + fUV n B l r) npK Puv r2.1
  let r4 := cTrunc2MulPowConst N0 (n + 1) (n + 1) B K (1 - fUV n B l r) nmK r3.2 r3.1
  (r4.1, r2.2, r4.2)

lemma cTrueUpdateOne_spec (n B l r : ℕ) (hB : B = 2 * n + 10) {nmW A_lr : Word B}
    {S : Trunc2Wire 3 (2 * n + 1) B} {Puv : Trunc2Wire (n + 1) (n + 1) B}
    {gs : List Gate} (hgs : ValidCircuit (N_in n true) gs)
    (hnm : ValidWord (N_in n true) gs nmW) (hAlr : ValidWord (N_in n true) gs A_lr)
    (hS : ValidTrunc2 (N_in n true) gs S) (hP : ValidTrunc2 (N_in n true) gs Puv) :
    let N0 := N_in n true
    let res := cTrueUpdateOne n B l r nmW A_lr S Puv gs
    ValidCircuit N0 res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 14 * B + costZT_step n + 2 * costUV_step n ∧
    ValidTrunc2 N0 res.1 res.2.1 ∧ ValidTrunc2 N0 res.1 res.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      wordZMod gs (inputBits true σ p) nmW = (arcCountMinus σ p l r : ZMod (2 ^ B)) →
      wordNat gs (inputBits true σ p) A_lr = arcCountAll σ p l r →
      trunc2Val res.1 (inputBits true σ p) res.2.1 =
        ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r)) ^ arcCountMinus σ p l r *
          trunc2Val gs (inputBits true σ p) S ∧
      trunc2Val res.1 (inputBits true σ p) res.2.2 =
        ((1 + fUV n B l r) ^ arcCountPlus σ p l r * (1 - fUV n B l r) ^ arcCountMinus σ p l r) *
          trunc2Val gs (inputBits true σ p) Puv := by
  intro N0
  dsimp only [cTrueUpdateOne]
  set K := n + 2
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have hcostZT : K * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B * B + 13 * B)))) + 3 * ((2 * n + 1) * (4 * B))) = costZT_step n := by
    unfold costZT_step; dsimp only [K]; rw [hB]
  have hcostUV : K * ((n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) + (n + 1) * ((n + 1) * (4 * B))) = costUV_step n := by
    unfold costUV_step; dsimp only [K]; rw [hB]
  set r1 := cSub N0 B A_lr nmW gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cSub_spec hN hgs hAlr hnm
  rw [← hr1] at v1 e1 l1 w1 f1
  have hnmK : ValidWord N0 r1.1 (cShiftRightResize B K 0 nmW) := validWord_cShiftRightResize hN 0 (hnm.extends e1)
  have hnpK : ValidWord N0 r1.1 (cShiftRightResize B K 0 r1.2) := validWord_cShiftRightResize hN 0 w1
  set r2 := cTrunc2MulPowConst N0 3 (2 * n + 1) B K ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r))
    (cShiftRightResize B K 0 nmW) S r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cTrunc2MulPowConst_spec hN ((1 + fZT n B l r) * Trunc2.invOneSub (fZT n B l r))
    v1 hnmK (hS.extends e1)
  rw [← hr2] at v2 e2 l2 w2 f2
  set r3 := cTrunc2MulPowConst N0 (n + 1) (n + 1) B K (1 + fUV n B l r)
    (cShiftRightResize B K 0 r1.2) Puv r2.1 with hr3
  obtain ⟨v3, e3, l3, w3, f3⟩ := cTrunc2MulPowConst_spec hN (1 + fUV n B l r)
    v2 (hnpK.extends e2) (hP.extends (e1.trans e2))
  rw [← hr3] at v3 e3 l3 w3 f3
  obtain ⟨v4, e4, l4, w4, f4⟩ := cTrunc2MulPowConst_spec hN (1 - fUV n B l r)
    v3 (hnmK.extends (e2.trans e3)) w3
  refine ⟨v4, e1.trans (e2.trans (e3.trans e4)),
    by linarith,
    w2.extends (e3.trans e4), w4, fun σ p hnmZ hAnat => ?_⟩
  have hc := inputBits_hasConsts true σ p
  have hposB : 0 < 2 ^ B := by positivity
  haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
  have hltK := arcCountAll_lt_two_pow_K σ p l r
  have hltK' : arcCountAll σ p l r < 2 ^ K := hltK
  have hpm := arcCountPlus_add_minus σ p l r
  have hltB : 2 ^ K ≤ 2 ^ B := Nat.pow_le_pow_right (by omega) (by omega)
  have hnmNat : wordNat gs (inputBits true σ p) nmW = arcCountMinus σ p l r := by
    have hval := congrArg ZMod.val hnmZ
    rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hval
    exact hval
  have hnpNat : wordNat r1.1 (inputBits true σ p) r1.2 = arcCountPlus σ p l r := by
    have hz : wordZMod r1.1 (inputBits true σ p) r1.2 = (arcCountPlus σ p l r : ZMod (2 ^ B)) := by
      rw [f1 _ hc, hnmZ]
      unfold wordZMod; rw [hAnat, ← hpm, Nat.cast_add]; ring
    have hval := congrArg ZMod.val hz
    rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hval
    exact hval
  have hnmK_val : wordNat r1.1 (inputBits true σ p) (cShiftRightResize B K 0 nmW) = arcCountMinus σ p l r := by
    rw [wordNat_cShiftRightResize hc, pow_zero, Nat.div_one, wordNat_extends e1 hc.1 hnm, hnmNat,
      Nat.mod_eq_of_lt (by omega)]
  have hnpK_val : wordNat r1.1 (inputBits true σ p) (cShiftRightResize B K 0 r1.2) = arcCountPlus σ p l r := by
    rw [wordNat_cShiftRightResize hc, pow_zero, Nat.div_one, hnpNat, Nat.mod_eq_of_lt (by omega)]
  constructor
  · rw [trunc2Val_extends (e3.trans e4) hc.1 w2, f2 _ hc, hnmK_val, trunc2Val_extends e1 hc.1 hS]
  · rw [f4 _ hc, f3 _ hc, wordNat_extends (e2.trans e3) hc.1 hnmK, wordNat_extends e2 hc.1 hnpK,
      hnmK_val, hnpK_val, trunc2Val_extends (e1.trans e2) hc.1 hP]
    ring

def costStepTrue (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  2 * (14 * B) + 13 * B * B + 2 * (14 * B) + 2 * (14 * B + costZT_step n + 2 * costUV_step n)

def cTrueStepOdd (n B l : ℕ) (e0 e1w A0 A1 : Word B)
    (S : Trunc2Wire 3 (2 * n + 1) B) (Puv : Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) :
    List Gate × (Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B) :=
  let N0 := N_in n true
  let m := l / 2
  let r3 := cMulConst N0 B (m : ZMod (2 ^ B)) e0 gs
  let r4 := cSub N0 B e1w r3.2 r3.1
  let r5 := cSub N0 B e0 r4.2 r4.1
  let r6 := cTrueUpdateOne n B l m r5.2 A0 S Puv r5.1
  cTrueUpdateOne n B l (m + 1) r4.2 A1 r6.2.1 r6.2.2 r6.1

lemma cTrueStepOdd_spec (n B l : ℕ) (hB : B = 2 * n + 10)
    (idx : Fin (2 * n)) (hl : l = idx.val + 1) (hodd : l % 2 = 1)
    {e0 e1w A0 A1 : Word B}
    {S : Trunc2Wire 3 (2 * n + 1) B} {Puv : Trunc2Wire (n + 1) (n + 1) B}
    {gs : List Gate} (hgs : ValidCircuit (N_in n true) gs)
    (he0w : ValidWord (N_in n true) gs e0) (he1w : ValidWord (N_in n true) gs e1w)
    (hA0 : ValidWord (N_in n true) gs A0) (hA1 : ValidWord (N_in n true) gs A1)
    (hS : ValidTrunc2 (N_in n true) gs S) (hP : ValidTrunc2 (N_in n true) gs Puv) :
    let N0 := N_in n true
    let m := l / 2
    let r := cTrueStepOdd n B l e0 e1w A0 A1 S Puv gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + 13 * B * B + 2 * (14 * B) + 2 * (14 * B + costZT_step n + 2 * costUV_step n) ∧
    ValidTrunc2 N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      wordZMod gs (inputBits true σ p) e0 = ((∑ r' ∈ (primR l).toFinset, arcCountMinus σ p l r' : ℕ) : ZMod (2 ^ B)) →
      wordZMod gs (inputBits true σ p) e1w = ((∑ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r' : ℕ) : ZMod (2 ^ B)) →
      wordNat gs (inputBits true σ p) A0 = arcCountAll σ p l m →
      wordNat gs (inputBits true σ p) A1 = arcCountAll σ p l (m + 1) →
      (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val gs (inputBits true σ p) S).coeff h d = (tailZT_true n B σ p idx.val).coeff h d) →
      trunc2Val gs (inputBits true σ p) Puv = prefUV_true n B σ p idx.val →
      (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val r.1 (inputBits true σ p) r.2.1).coeff h d = (tailZT_true n B σ p (idx.val + 1)).coeff h d) ∧
      trunc2Val r.1 (inputBits true σ p) r.2.2 = prefUV_true n B σ p (idx.val + 1) := by
  intro N0 m
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  set r3 := cMulConst N0 B (m : ZMod (2 ^ B)) e0 gs with hr3
  obtain ⟨v3, e3, l3, w3, f3⟩ := cMulConst_spec hN (m : ZMod (2 ^ B)) hgs he0w
  rw [← hr3] at v3 e3 l3 w3 f3
  set r4 := cSub N0 B e1w r3.2 r3.1 with hr4
  obtain ⟨v4, e4, l4, w4, f4⟩ := cSub_spec hN v3 (he1w.extends e3) w3
  rw [← hr4] at v4 e4 l4 w4 f4
  set r5 := cSub N0 B e0 r4.2 r4.1 with hr5
  obtain ⟨v5, e5, l5, w5, f5⟩ := cSub_spec hN v4 (he0w.extends (e3.trans e4)) w4
  rw [← hr5] at v5 e5 l5 w5 f5
  have e35 : Extends gs r5.1 := e3.trans (e4.trans e5)
  set r6 := cTrueUpdateOne n B l m r5.2 A0 S Puv r5.1 with hr6
  obtain ⟨v6, e6, l6, w6S, w6P, f6⟩ := cTrueUpdateOne_spec n B l m hB v5 w5
    (hA0.extends e35) (hS.extends e35) (hP.extends e35)
  rw [← hr6] at v6 e6 l6 w6S w6P f6
  set r7 := cTrueUpdateOne n B l (m + 1) r4.2 A1 r6.2.1 r6.2.2 r6.1 with hr7
  obtain ⟨v7, e7, l7, w7S, w7P, f7⟩ := cTrueUpdateOne_spec n B l (m + 1) hB v6
    (w4.extends (e5.trans e6)) (hA1.extends (e35.trans e6)) w6S w6P
  rw [← hr7] at v7 e7 l7 w7S w7P f7
  have hres : cTrueStepOdd n B l e0 e1w A0 A1 S Puv gs = r7 := rfl
  dsimp only
  rw [hres]
  refine ⟨v7, e35.trans (e6.trans e7), by omega, w7S, w7P, fun σ p he0v he1v hA0v hA1v hS01 hPeq => ?_⟩
  have hc := inputBits_hasConsts true σ p
  have hpr : (primR l).toFinset = {m, m + 1} := by ext x; simp [primR, hodd, m]
  have hne : m ≠ m + 1 := by omega
  rw [hpr, Finset.sum_pair hne, Nat.cast_add] at he0v he1v
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at he1v
  have hsol := solve_false_odd (m : ZMod (2 ^ B)) (arcCountMinus σ p l m : ZMod (2 ^ B)) (arcCountMinus σ p l (m + 1) : ZMod (2 ^ B))
  have hnm1 : wordZMod r4.1 (inputBits true σ p) r4.2 = (arcCountMinus σ p l (m + 1) : ZMod (2 ^ B)) := by
    rw [f4 _ hc, wordZMod_extends e3 hc.1 he1w, f3 _ hc, he0v, he1v]; exact hsol.1
  have hnm0 : wordZMod r5.1 (inputBits true σ p) r5.2 = (arcCountMinus σ p l m : ZMod (2 ^ B)) := by
    rw [f5 _ hc, wordZMod_extends (e3.trans e4) hc.1 he0w, hnm1, he0v]; ring
  obtain ⟨hS6, hP6⟩ := f6 σ p hnm0 (by rw [wordNat_extends e35 hc.1 hA0, hA0v])
  obtain ⟨hS7, hP7⟩ := f7 σ p (by rw [wordZMod_extends (e5.trans e6) hc.1 w4, hnm1])
    (by rw [wordNat_extends (e35.trans e6) hc.1 hA1, hA1v])
  rw [trunc2Val_extends e35 hc.1 hS] at hS6
  rw [trunc2Val_extends e35 hc.1 hP, hPeq] at hP6
  rw [hS6] at hS7; rw [hP6] at hP7
  have hprodS : ((1 + fZT n B l (m + 1)) * Trunc2.invOneSub (fZT n B l (m + 1))) ^ arcCountMinus σ p l (m + 1) *
      ((1 + fZT n B l m) * Trunc2.invOneSub (fZT n B l m)) ^ arcCountMinus σ p l m =
      ∏ r' ∈ (primR l).toFinset, ((1 + fZT n B l r') * Trunc2.invOneSub (fZT n B l r')) ^ arcCountMinus σ p l r' := by
    rw [hpr, Finset.prod_pair hne]; ring
  have hprodP : ((1 + fUV n B l (m + 1)) ^ arcCountPlus σ p l (m + 1) * (1 - fUV n B l (m + 1)) ^ arcCountMinus σ p l (m + 1)) *
      ((1 + fUV n B l m) ^ arcCountPlus σ p l m * (1 - fUV n B l m) ^ arcCountMinus σ p l m) =
      ∏ r' ∈ (primR l).toFinset, (1 + fUV n B l r') ^ arcCountPlus σ p l r' * (1 - fUV n B l r') ^ arcCountMinus σ p l r' := by
    rw [hpr, Finset.prod_pair hne]; ring
  constructor
  · intro h hh2 d
    rw [hS7, ← mul_assoc, hprodS]
    rw [trunc2_mul_congr_lt 2 _ _ (tailZT_true n B σ p idx.val) hS01 h hh2 d, hl, tailZT_true_peel]
  · rw [hP7, ← mul_assoc, hprodP, hl, prefUV_true_step]

def cStage2TrueStep (n B : ℕ) (A : Fin (2 * n + 1) → Fin (n + 1) → Word B)
    (idx : Fin (2 * n))
    (st : Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) :
    List Gate × (Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B) :=
  let N0 := N_in n true
  let l := idx.val + 1
  let m := l / 2
  let r1 := cNeg N0 B (st.1 0 ⟨l, by omega⟩) gs
  let r2 := cNeg N0 B (st.1 1 ⟨l, by omega⟩) r1.1
  let e0 := cShiftRightResize B B 1 r1.2
  let e1 := cShiftRightResize B B 1 r2.2
  if hodd : l % 2 = 1 then
    cTrueStepOdd n B l e0 e1 (A ⟨l, by omega⟩ ⟨m, by omega⟩) (A ⟨l, by omega⟩ ⟨m + 1, by omega⟩) st.1 st.2 r2.1
  else
    cTrueUpdateOne n B l m e0 (A ⟨l, by omega⟩ ⟨m, by omega⟩) st.1 st.2 r2.1

lemma cStage2TrueStep_spec (n B : ℕ) (hB : B = 2 * n + 10)
    {A : Fin (2 * n + 1) → Fin (n + 1) → Word B}
    (idx : Fin (2 * n))
    {st : Trunc2Wire 3 (2 * n + 1) B × Trunc2Wire (n + 1) (n + 1) B}
    {gs : List Gate} (hgs : ValidCircuit (N_in n true) gs)
    (hA : ∀ l r, ValidWord (N_in n true) gs (A l r))
    (hS : ValidTrunc2 (N_in n true) gs st.1) (hP : ValidTrunc2 (N_in n true) gs st.2) :
    let N0 := N_in n true
    let r := cStage2TrueStep n B A idx st gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + costStepTrue n ∧
    ValidTrunc2 N0 r.1 r.2.1 ∧ ValidTrunc2 N0 r.1 r.2.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ l' r', wordNat gs (inputBits true σ p) (A l' r') = arcCountAll σ p l'.val r'.val) →
      (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val gs (inputBits true σ p) st.1).coeff h d = (tailZT_true n B σ p idx.val).coeff h d) →
      trunc2Val gs (inputBits true σ p) st.2 = prefUV_true n B σ p idx.val →
      (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val r.1 (inputBits true σ p) r.2.1).coeff h d = (tailZT_true n B σ p (idx.val + 1)).coeff h d) ∧
      trunc2Val r.1 (inputBits true σ p) r.2.2 = prefUV_true n B σ p (idx.val + 1) := by
  intro N0
  set l := idx.val + 1
  set m := l / 2
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have hcostStep : 2 * (14 * B) + 13 * B * B + 2 * (14 * B) + 2 * (14 * B + costZT_step n + 2 * costUV_step n) = costStepTrue n := by
    unfold costStepTrue; rw [hB]
  set r1 := cNeg N0 B (st.1 0 ⟨l, by omega⟩) gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cNeg_spec hN hgs (hS 0 ⟨l, by omega⟩)
  rw [← hr1] at v1 e1 l1 w1 f1
  set r2 := cNeg N0 B (st.1 1 ⟨l, by omega⟩) r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cNeg_spec hN v1 ((hS 1 ⟨l, by omega⟩).extends e1)
  rw [← hr2] at v2 e2 l2 w2 f2
  have e12 : Extends gs r2.1 := e1.trans e2
  set e0 := cShiftRightResize B B 1 r1.2
  set e1w := cShiftRightResize B B 1 r2.2
  have he0w : ValidWord N0 r2.1 e0 := validWord_cShiftRightResize hN 1 (w1.extends e2)
  have he1w : ValidWord N0 r2.1 e1w := validWord_cShiftRightResize hN 1 w2
  have he_vals : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val gs (inputBits true σ p) st.1).coeff h d = (tailZT_true n B σ p idx.val).coeff h d) →
      wordZMod r2.1 (inputBits true σ p) e0 =
        ((∑ r' ∈ (primR l).toFinset, arcCountMinus σ p l r' : ℕ) : ZMod (2 ^ B)) ∧
      wordZMod r2.1 (inputBits true σ p) e1w =
        ((∑ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r' : ℕ) : ZMod (2 ^ B)) := by
    intro σ p hS01
    have hc := inputBits_hasConsts true σ p
    have hposB : 0 < 2 ^ B := by positivity
    haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
    have hcard : (primR l).toFinset.card ≤ 2 :=
      le_trans (List.toFinset_card_le _) (by unfold primR; split_ifs <;> simp)
    have hle0 : (∑ r' ∈ (primR l).toFinset, arcCountMinus σ p l r') ≤ 4 * n * n := by
      have h1 : ∀ r' ∈ (primR l).toFinset, arcCountMinus σ p l r' ≤ 2 * n := fun r' _ => by
        have := arcCountPlus_add_minus σ p l r'; have := arcCountAll_le σ p l r'; omega
      calc (∑ r' ∈ (primR l).toFinset, arcCountMinus σ p l r')
          ≤ ∑ _r' ∈ (primR l).toFinset, 2 * n := Finset.sum_le_sum h1
        _ = (primR l).toFinset.card * (2 * n) := by simp
        _ ≤ 2 * (2 * n) := Nat.mul_le_mul_right _ hcard
        _ ≤ 4 * n * n := by nlinarith [show 1 ≤ n by have := idx.isLt; omega]
    have hle1 : (∑ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r') ≤ 4 * n * n := by
      have h1 : ∀ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r' ≤ n * (2 * n) := fun r' hr' => by
        have hrm := r_le_n_of_primR (n := n) (by omega) (List.mem_toFinset.mp hr')
        have hcm : arcCountMinus σ p l r' ≤ 2 * n := by
          have := arcCountPlus_add_minus σ p l r'; have := arcCountAll_le σ p l r'; omega
        exact Nat.mul_le_mul hrm hcm
      calc (∑ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r')
          ≤ ∑ _r' ∈ (primR l).toFinset, n * (2 * n) := Finset.sum_le_sum h1
        _ = (primR l).toFinset.card * (n * (2 * n)) := by simp
        _ ≤ 2 * (n * (2 * n)) := Nat.mul_le_mul_right _ hcard
        _ = 4 * n * n := by ring
    have hz0 : wordZMod r1.1 (inputBits true σ p) r1.2 =
        ((2 * (∑ r' ∈ (primR l).toFinset, arcCountMinus σ p l r') : ℕ) : ZMod (2 ^ B)) := by
      rw [f1 _ hc]
      have hc0 := hS01 0 (by decide) ⟨l, by omega⟩
      rw [tailZT_true_coeff] at hc0
      change -(trunc2Val gs (inputBits true σ p) st.1).coeff 0 ⟨l, by omega⟩ = _
      rw [hc0, ← Finset.sum_neg_distrib, Nat.cast_mul, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => by simp; ring
    have hz1 : wordZMod r2.1 (inputBits true σ p) r2.2 =
        ((2 * (∑ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r') : ℕ) : ZMod (2 ^ B)) := by
      rw [f2 _ hc, wordZMod_extends e1 hc.1 (hS 1 _)]
      have hc1 := hS01 1 (by decide) ⟨l, by omega⟩
      rw [tailZT_true_coeff] at hc1
      change -(trunc2Val gs (inputBits true σ p) st.1).coeff 1 ⟨l, by omega⟩ = _
      rw [hc1, ← Finset.sum_neg_distrib, Nat.cast_mul, Nat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r' _ => by simp; ring
    have hn0 : wordNat r1.1 (inputBits true σ p) r1.2 = 2 * (∑ r' ∈ (primR l).toFinset, arcCountMinus σ p l r') := by
      have hv := congrArg ZMod.val hz0
      rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt (two_mul_nat_lt_two_pow_B hB _ hle0)] at hv
      exact hv
    have hn1 : wordNat r2.1 (inputBits true σ p) r2.2 = 2 * (∑ r' ∈ (primR l).toFinset, r' * arcCountMinus σ p l r') := by
      have hv := congrArg ZMod.val hz1
      rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt (two_mul_nat_lt_two_pow_B hB _ hle1)] at hv
      exact hv
    constructor
    · unfold wordZMod
      rw [wordNat_cShiftRightResize hc, pow_one, wordNat_extends e2 hc.1 w1, hn0,
        Nat.mul_div_right _ (by omega : 0 < 2), ZMod.natCast_mod]
    · unfold wordZMod
      rw [wordNat_cShiftRightResize hc, pow_one, hn1,
        Nat.mul_div_right _ (by omega : 0 < 2), ZMod.natCast_mod]
  by_cases hodd : l % 2 = 1
  · have hres : cStage2TrueStep n B A idx st gs =
        cTrueStepOdd n B l e0 e1w (A ⟨l, by omega⟩ ⟨m, by omega⟩) (A ⟨l, by omega⟩ ⟨m + 1, by omega⟩) st.1 st.2 r2.1 := by
      unfold cStage2TrueStep
      exact dif_pos hodd
    dsimp only
    rw [hres]
    obtain ⟨v3, e3, l3, w3S, w3P, f3⟩ := cTrueStepOdd_spec n B l hB idx rfl hodd v2 he0w he1w
      ((hA ⟨l, by omega⟩ ⟨m, by omega⟩).extends e12)
      ((hA ⟨l, by omega⟩ ⟨m + 1, by omega⟩).extends e12)
      (hS.extends e12) (hP.extends e12)
    refine ⟨v3, e12.trans e3, by omega, w3S, w3P, fun σ p hAval hS01 hPeq => ?_⟩
    have hc := inputBits_hasConsts true σ p
    obtain ⟨he0v, he1v⟩ := he_vals σ p hS01
    exact f3 σ p he0v he1v
      (by rw [wordNat_extends e12 hc.1 (hA _ _), hAval])
      (by rw [wordNat_extends e12 hc.1 (hA _ _), hAval])
      (fun h hh2 d => by rw [trunc2Val_extends e12 hc.1 hS, hS01 h hh2 d])
      (by rw [trunc2Val_extends e12 hc.1 hP, hPeq])
  · have hres : cStage2TrueStep n B A idx st gs =
        cTrueUpdateOne n B l m e0 (A ⟨l, by omega⟩ ⟨m, by omega⟩) st.1 st.2 r2.1 := by
      unfold cStage2TrueStep
      exact dif_neg hodd
    dsimp only
    rw [hres]
    obtain ⟨v3, e3, l3, w3S, w3P, f3⟩ := cTrueUpdateOne_spec n B l m hB v2 he0w
      ((hA ⟨l, by omega⟩ ⟨m, by omega⟩).extends e12) (hS.extends e12) (hP.extends e12)
    refine ⟨v3, e12.trans e3, by omega,
      w3S, w3P, fun σ p hAval hS01 hPeq => ?_⟩
    have hc := inputBits_hasConsts true σ p
    obtain ⟨he0v, _⟩ := he_vals σ p hS01
    have hpr : (primR l).toFinset = {m} := by ext x; simp [primR, hodd, m]
    rw [hpr, Finset.sum_singleton] at he0v
    obtain ⟨hS3, hP3⟩ := f3 σ p he0v (by rw [wordNat_extends e12 hc.1 (hA _ _), hAval])
    rw [trunc2Val_extends e12 hc.1 hS] at hS3
    rw [trunc2Val_extends e12 hc.1 hP, hPeq] at hP3
    have hprodS : ((1 + fZT n B l m) * Trunc2.invOneSub (fZT n B l m)) ^ arcCountMinus σ p l m =
        ∏ r' ∈ (primR l).toFinset, ((1 + fZT n B l r') * Trunc2.invOneSub (fZT n B l r')) ^ arcCountMinus σ p l r' := by
      rw [hpr, Finset.prod_singleton]
    have hprodP : (1 + fUV n B l m) ^ arcCountPlus σ p l m * (1 - fUV n B l m) ^ arcCountMinus σ p l m =
        ∏ r' ∈ (primR l).toFinset, (1 + fUV n B l r') ^ arcCountPlus σ p l r' * (1 - fUV n B l r') ^ arcCountMinus σ p l r' := by
      rw [hpr, Finset.prod_singleton]
    constructor
    · intro h hh2 d
      rw [hS3, hprodS, trunc2_mul_congr_lt 2 _ _ (tailZT_true n B σ p idx.val) hS01 h hh2 d, tailZT_true_peel]
    · rw [hP3, hprodP, prefUV_true_step]

def costStage2True (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  (2 * n) * ((2 * n) * 5) +
    (2 * n) * ((2 * n) * ((2 * n) * (2 * (2 * n)))) +
    (2 * n) * (2 * n + 2 * n) +
    (2 * n) * ((2 * n) * (13 * B)) +
    (2 * n) * (n * (13 * B)) +
    (2 * n + 1) * ((n + 1) * ((2 * n) * (7 * B + 7 * B + 2) + (2 * n) * (13 * B))) +
    (2 * n) * (2 * costZT_step n) +
    (2 * n) * costStepTrue n

def cStage2True (n B : ℕ) (F_zt : Trunc2Wire 3 (2 * n + 1) B) (gs : List Gate) :
    List Gate × Trunc2Wire (n + 1) (n + 1) B :=
  let N0 := N_in n true
  let (g1, A) := cBuildArcCounts N0 n B (permW n) (mask0W n) (mask1W n) gs
  let (g2, S0) := cTrueDivBase n B A F_zt g1
  let r := cFoldFin (2 * n) (cStage2TrueStep n B A) (S0, cTrunc2One (n + 1) (n + 1) B) g2
  (r.1, r.2.2)

lemma cStage2True_spec (n B : ℕ) (hB : B = 2 * n + 10)
    {F_zt : Trunc2Wire 3 (2 * n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n true) gs) (hF : ValidTrunc2 (N_in n true) gs F_zt)
    (hF_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (h : Fin 3),
      h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val gs (inputBits true σ p) F_zt).coeff h d = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d) :
    let N0 := N_in n true
    let r := cStage2True n B F_zt gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + costStage2True n ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      trunc2Val r.1 (inputBits true σ p) r.2 = arcProdUV (R := ZMod (2 ^ B)) σ p := by
  intro N0
  dsimp only [cStage2True]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have h2nB : 2 * n < 2 ^ B := lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right (by omega) (by omega))
  set r1 := cBuildArcCounts N0 n B (permW n) (mask0W n) (mask1W n) gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cBuildArcCounts_spec hN (by omega) h2nB hgs
    (fun i j => lt_of_lt_of_le (permW_lt n i j) (Nat.le_add_right _ _))
    (fun i => lt_of_lt_of_le (mask0W_lt n i) (Nat.le_add_right _ _))
    (fun i => lt_of_lt_of_le (mask1W_lt n i) (Nat.le_add_right _ _))
  rw [← hr1] at v1 e1 l1 w1 f1
  have hA1_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) l' r',
      wordNat r1.1 (inputBits true σ p) (r1.2 l' r') = arcCountAll σ p l'.val r'.val := by
    intro σ p l' r'
    have hc := inputBits_hasConsts true σ p
    have he0 : Extends [] gs := ⟨gs, rfl⟩
    exact f1 _ hc σ p
      (fun i j => by rw [wireAt_extends he0 (w := permW n i j) (by rw [hc.1]; exact permW_lt n i j), wireAt_permW])
      (fun i => by rw [wireAt_extends he0 (w := mask0W n i) (by rw [hc.1]; exact mask0W_lt n i), wireAt_mask0W])
      (fun i => by rw [wireAt_extends he0 (w := mask1W n i) (by rw [hc.1]; exact mask1W_lt n i), wireAt_mask1W]) l' r'
  set r2 := cTrueDivBase n B r1.2 F_zt r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cTrueDivBase_spec n B hB v1 w1 (hF.extends e1)
  rw [← hr2] at v2 e2 l2 w2 f2
  have hS0_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (h : Fin 3),
      h.val < 2 → ∀ d : Fin (2 * n + 1),
        (trunc2Val r2.1 (inputBits true σ p) r2.2).coeff h d = (tailZT_true n B σ p 0).coeff h d := by
    intro σ p h hh2 d
    exact f2 σ p (hA1_sem σ p) (fun h' hh2' d' => by
      rw [trunc2Val_extends e1 (inputBits_hasConsts true σ p).1 hF, hF_sem σ p h' hh2' d']) h hh2 d
  have h3 := cFoldFin_spec (N0 := N0) (2 * n) (costStepTrue n) (cStage2TrueStep n B r1.2)
    (fun k _ g st => ValidTrunc2 N0 g st.1 ∧ ValidTrunc2 N0 g st.2 ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
        (∀ h : Fin 3, h.val < 2 → ∀ d : Fin (2 * n + 1),
          (trunc2Val g (inputBits true σ p) st.1).coeff h d = (tailZT_true n B σ p k).coeff h d) ∧
        trunc2Val g (inputBits true σ p) st.2 = prefUV_true n B σ p k)
    (r2.2, cTrunc2One (n + 1) (n + 1) B) r2.1 v2
    ⟨w2, validTrunc2_cTrunc2One hN r2.1 (n + 1) (n + 1) B, fun σ p =>
      ⟨hS0_sem σ p, by rw [trunc2Val_cTrunc2One (inputBits_hasConsts true σ p)]; simp [prefUV_true]⟩⟩
    (fun idx gs1 st hv he ⟨hS1, hP1, hsem⟩ => by
      obtain ⟨va, ea, la, waS, waP, fa⟩ := cStage2TrueStep_spec n B hB idx hv
        (fun l' r' => (w1 l' r').extends (e2.trans he)) hS1 hP1
      exact ⟨va, ea, la, waS, waP, fun σ p =>
        fa σ p (fun l' r' => by
          rw [wordNat_extends (e2.trans he) (inputBits_hasConsts true σ p).1 (w1 l' r'), hA1_sem σ p])
          (hsem σ p).1 (hsem σ p).2⟩)
  have hcostS2T :
      (2 * n) * ((2 * n) * 5) +
      (2 * n) * ((2 * n) * ((2 * n) * (2 * (2 * n)))) +
      (2 * n) * (2 * n + 2 * n) +
      (2 * n) * ((2 * n) * (13 * B)) +
      (2 * n) * (n * (13 * B)) +
      (2 * n + 1) * ((n + 1) * ((2 * n) * (7 * B + 7 * B + 2) + (2 * n) * (13 * B))) +
      (2 * n) * (2 * costZT_step n) +
      (2 * n) * costStepTrue n = costStage2True n := by
    unfold costStage2True; rw [hB]
  refine ⟨h3.1, e1.trans (e2.trans h3.2.1),
    by have := h3.2.2.1; linarith,
    h3.2.2.2.2.1, fun σ p => ?_⟩
  rw [(h3.2.2.2.2.2 σ p).2, arcProdUV_eq_pm]; rfl

def cStage3Tmp (n B : ℕ) (known : Bool) (Puv : Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) : List Gate × Trunc2Wire (n + 1) (n + 1) B :=
  let N0 := N_in n known
  cBuildFin (n + 1) (fun r0 ga =>
    cBuildFin (n + 1) (fun j gb =>
      cLinComb N0 B (n + 1) (fun i => (krawCoeff n i.val r0.val : ZMod (2 ^ B))) (fun i => Puv i j) gb) ga) gs

lemma cStage3Tmp_spec (n B : ℕ) (known : Bool)
    {Puv : Trunc2Wire (n + 1) (n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n known) gs) (hP : ValidTrunc2 (N_in n known) gs Puv) :
    let N0 := N_in n known
    let r := cStage3Tmp n B known Puv gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + (n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B))) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ r0 j : Fin (n + 1),
      wordZMod r.1 xs (r.2 r0 j) =
        ∑ i : Fin (n + 1), (krawCoeff n i.val r0.val : ZMod (2 ^ B)) * wordZMod gs xs (Puv i j) := by
  intro N0
  dsimp only [cStage3Tmp]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have h := cBuildFin_spec (N0 := N0) (n + 1) ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))
    (fun r0 ga => cBuildFin (n + 1) (fun j gb =>
      cLinComb N0 B (n + 1) (fun i => (krawCoeff n i.val r0.val : ZMod (2 ^ B))) (fun i => Puv i j) gb) ga)
    (fun g r0 row => (∀ j : Fin (n + 1), ValidWord N0 g (row j)) ∧
      ∀ xs, HasConsts xs N0 → ∀ j : Fin (n + 1),
        wordZMod g xs (row j) = ∑ i : Fin (n + 1), (krawCoeff n i.val r0.val : ZMod (2 ^ B)) * wordZMod gs xs (Puv i j))
    (fun g1 g2 r0 row he ⟨hw, hf⟩ => ⟨fun j => (hw j).extends he, fun xs hc j => by
      rw [wordZMod_extends he hc.1 (hw j), hf xs hc j]⟩)
    gs hgs
    (fun r0 ga hga hea => by
      have h2 := cBuildFin_spec (N0 := N0) (n + 1) ((n + 1) * (13 * B * B + 13 * B))
        (fun j gb => cLinComb N0 B (n + 1) (fun i => (krawCoeff n i.val r0.val : ZMod (2 ^ B))) (fun i => Puv i j) gb)
        (fun g j w => ValidWord N0 g w ∧
          ∀ xs, HasConsts xs N0 →
            wordZMod g xs w = ∑ i : Fin (n + 1), (krawCoeff n i.val r0.val : ZMod (2 ^ B)) * wordZMod gs xs (Puv i j))
        (fun g1 g2 j w he ⟨hw, hf⟩ => ⟨hw.extends he, fun xs hc => by
          rw [wordZMod_extends he hc.1 hw, hf xs hc]⟩)
        ga hga
        (fun j gb hgb heb => by
          have hegb := hea.trans heb
          obtain ⟨v1, e1, l1, w1, f1⟩ := cLinComb_spec hN
            (fun i => (krawCoeff n i.val r0.val : ZMod (2 ^ B))) hgb (fun i => (hP i j).extends hegb)
          refine ⟨v1, e1, l1, w1, fun xs hc => ?_⟩
          rw [f1 xs hc]
          refine Finset.sum_congr rfl fun i _ => by rw [wordZMod_extends hegb hc.1 (hP i j)])
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun j => (h2.2.2.2 j).1, fun xs hc j => (h2.2.2.2 j).2 xs hc⟩)
  exact ⟨h.1, h.2.1, h.2.2.1, fun i j => (h.2.2.2 i).1 j, fun xs hc r0 j => (h.2.2.2 r0).2 xs hc j⟩

def cStage3M (n B : ℕ) (known : Bool) (tmp : Trunc2Wire (n + 1) (n + 1) B)
    (gs : List Gate) : List Gate × Trunc2Wire (n + 1) (n + 1) B :=
  let N0 := N_in n known
  cBuildFin (n + 1) (fun r0 ga =>
    cBuildFin (n + 1) (fun b0 gb =>
      cLinComb N0 B (n + 1) (fun j => (krawCoeff n j.val b0.val : ZMod (2 ^ B))) (fun j => tmp r0 j) gb) ga) gs

lemma cStage3M_spec (n B : ℕ) (known : Bool)
    {tmp : Trunc2Wire (n + 1) (n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n known) gs) (hT : ValidTrunc2 (N_in n known) gs tmp) :
    let N0 := N_in n known
    let r := cStage3M n B known tmp gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + (n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B))) ∧
    ValidTrunc2 N0 r.1 r.2 ∧
    ∀ (xs : List Bool), HasConsts xs N0 → ∀ r0 b0 : Fin (n + 1),
      wordZMod r.1 xs (r.2 r0 b0) =
        ∑ j : Fin (n + 1), (krawCoeff n j.val b0.val : ZMod (2 ^ B)) * wordZMod gs xs (tmp r0 j) := by
  intro N0
  dsimp only [cStage3M]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have h := cBuildFin_spec (N0 := N0) (n + 1) ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))
    (fun r0 ga => cBuildFin (n + 1) (fun b0 gb =>
      cLinComb N0 B (n + 1) (fun j => (krawCoeff n j.val b0.val : ZMod (2 ^ B))) (fun j => tmp r0 j) gb) ga)
    (fun g r0 row => (∀ b0 : Fin (n + 1), ValidWord N0 g (row b0)) ∧
      ∀ xs, HasConsts xs N0 → ∀ b0 : Fin (n + 1),
        wordZMod g xs (row b0) = ∑ j : Fin (n + 1), (krawCoeff n j.val b0.val : ZMod (2 ^ B)) * wordZMod gs xs (tmp r0 j))
    (fun g1 g2 r0 row he ⟨hw, hf⟩ => ⟨fun b0 => (hw b0).extends he, fun xs hc b0 => by
      rw [wordZMod_extends he hc.1 (hw b0), hf xs hc b0]⟩)
    gs hgs
    (fun r0 ga hga hea => by
      have h2 := cBuildFin_spec (N0 := N0) (n + 1) ((n + 1) * (13 * B * B + 13 * B))
        (fun b0 gb => cLinComb N0 B (n + 1) (fun j => (krawCoeff n j.val b0.val : ZMod (2 ^ B))) (fun j => tmp r0 j) gb)
        (fun g b0 w => ValidWord N0 g w ∧
          ∀ xs, HasConsts xs N0 →
            wordZMod g xs w = ∑ j : Fin (n + 1), (krawCoeff n j.val b0.val : ZMod (2 ^ B)) * wordZMod gs xs (tmp r0 j))
        (fun g1 g2 b0 w he ⟨hw, hf⟩ => ⟨hw.extends he, fun xs hc => by
          rw [wordZMod_extends he hc.1 hw, hf xs hc]⟩)
        ga hga
        (fun b0 gb hgb heb => by
          have hegb := hea.trans heb
          obtain ⟨v1, e1, l1, w1, f1⟩ := cLinComb_spec hN
            (fun j => (krawCoeff n j.val b0.val : ZMod (2 ^ B))) hgb (fun j => (hT r0 j).extends hegb)
          refine ⟨v1, e1, l1, w1, fun xs hc => ?_⟩
          rw [f1 xs hc]
          refine Finset.sum_congr rfl fun j _ => by rw [wordZMod_extends hegb hc.1 (hT r0 j)])
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun b0 => (h2.2.2.2 b0).1, fun xs hc b0 => (h2.2.2.2 b0).2 xs hc⟩)
  exact ⟨h.1, h.2.1, h.2.2.1, fun i j => (h.2.2.2 i).1 j, fun xs hc r0 b0 => (h.2.2.2 r0).2 xs hc b0⟩

def cStage3Shift (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (known : Bool) (twoPowF : Word B0)
    (M : Trunc2Wire (n + 1) (n + 1) B) (gs : List Gate) :
    List Gate × (Fin (n + 1) → Fin (n + 1) → Word (2 * n + 1)) :=
  let N0 := N_in n known
  cBuildFin (n + 1) (fun r0 ga =>
    cBuildFin (n + 1) (fun b0 gb =>
      cOneHotShiftRight N0 B (2 * n + 1) (2 * n + 1)
        (fun k => twoPowF ⟨2 * n - k.val, by omega⟩) (M r0 b0) gb) ga) gs

lemma cStage3Shift_spec (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (known : Bool)
    {twoPowF : Word B0} {M : Trunc2Wire (n + 1) (n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n known) gs)
    (htp : ValidWord (N_in n known) gs twoPowF) (hM : ValidTrunc2 (N_in n known) gs M)
    (htp_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
      wireAt gs (inputBits known σ p) (twoPowF ⟨k.val, by omega⟩) =
        decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩))
    (hM_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r0 b0 : Fin (n + 1)),
      wordNat gs (inputBits known σ p) (M r0 b0) = 2 ^ (2 * n - freeCount p) * hist σ p r0 b0) :
    let N0 := N_in n known
    let r := cStage3Shift n B B0 hB0_ge known twoPowF M gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧
    r.1.length ≤ gs.length + (n + 1) * ((n + 1) * ((2 * n + 1) * (4 * (2 * n + 1)))) ∧
    (∀ r0 b0, ValidWord N0 r.1 (r.2 r0 b0)) ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r0 b0 : Fin (n + 1)),
      wordNat r.1 (inputBits known σ p) (r.2 r0 b0) = hist σ p r0 b0 := by
  intro N0
  dsimp only [cStage3Shift]
  have hN : 2 ≤ N0 := by unfold N0 N_in; omega
  have h := cBuildFin_spec (N0 := N0) (n + 1) ((n + 1) * ((2 * n + 1) * (4 * (2 * n + 1))))
    (fun r0 ga => cBuildFin (n + 1) (fun b0 gb =>
      cOneHotShiftRight N0 B (2 * n + 1) (2 * n + 1)
        (fun k => twoPowF ⟨2 * n - k.val, by omega⟩) (M r0 b0) gb) ga)
    (fun g r0 row => (∀ b0 : Fin (n + 1), ValidWord N0 g (row b0)) ∧
      ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (b0 : Fin (n + 1)),
        wordNat g (inputBits known σ p) (row b0) = hist σ p r0 b0)
    (fun g1 g2 r0 row he ⟨hw, hf⟩ => ⟨fun b0 => (hw b0).extends he, fun σ p b0 => by
      rw [wordNat_extends he (inputBits_hasConsts known σ p).1 (hw b0), hf σ p b0]⟩)
    gs hgs
    (fun r0 ga hga hea => by
      have h2 := cBuildFin_spec (N0 := N0) (n + 1) ((2 * n + 1) * (4 * (2 * n + 1)))
        (fun b0 gb =>
          cOneHotShiftRight N0 B (2 * n + 1) (2 * n + 1)
            (fun k => twoPowF ⟨2 * n - k.val, by omega⟩) (M r0 b0) gb)
        (fun g b0 w => ValidWord N0 g w ∧
          ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
            wordNat g (inputBits known σ p) w = hist σ p r0 b0)
        (fun g1 g2 b0 w he ⟨hw, hf⟩ => ⟨hw.extends he, fun σ p => by
          rw [wordNat_extends he (inputBits_hasConsts known σ p).1 hw, hf σ p]⟩)
        ga hga
        (fun b0 gb hgb heb => by
          have hegb := hea.trans heb
          have hsel : ∀ k : Fin (2 * n + 1), twoPowF ⟨2 * n - k.val, by omega⟩ < N0 + gb.length :=
            fun k => (htp.extends hegb) ⟨2 * n - k.val, by omega⟩
          obtain ⟨v1, e1, l1, w1, f1⟩ := cOneHotShiftRight_spec hN hgb hsel ((hM r0 b0).extends hegb)
          refine ⟨v1, e1, l1, w1, fun σ p => ?_⟩
          have hc := inputBits_hasConsts known σ p
          have hfree := freeCount_le p
          have hoh : ∀ k : Fin (2 * n + 1),
              wireAt gb (inputBits known σ p) (twoPowF ⟨2 * n - k.val, by omega⟩) =
                decide (k = ⟨2 * n - freeCount p, by omega⟩) := fun k => by
            rw [wireAt_extends hegb (w := twoPowF ⟨2 * n - k.val, by omega⟩) (by rw [hc.1]; exact htp _)]
            have h1 := htp_sem σ p ⟨2 * n - k.val, by omega⟩
            change wireAt gs (inputBits known σ p) (twoPowF ⟨2 * n - k.val, by omega⟩) = _
            rw [h1]
            apply Bool.eq_iff_iff.mpr
            simp only [decide_eq_true_eq, Fin.ext_iff]
            have := k.isLt; omega
          have hnat := f1 (inputBits known σ p) hc ⟨2 * n - freeCount p, by omega⟩ hoh
          rw [hnat, wordNat_extends hegb hc.1 (hM r0 b0), hM_sem σ p r0 b0,
            Nat.mul_div_right _ (by positivity : 0 < 2 ^ (2 * n - freeCount p))]
          have hlt : hist σ p r0 b0 < 2 ^ (2 * n + 1) :=
            lt_of_le_of_lt (hist_le_twoPow_freeCount σ p r0 b0) (Nat.pow_lt_pow_right (by omega) (by omega))
          exact Nat.mod_eq_of_lt hlt)
      exact ⟨h2.1, h2.2.1, h2.2.2.1, fun b0 => (h2.2.2.2 b0).1, fun σ p b0 => (h2.2.2.2 b0).2 σ p⟩)
  exact ⟨h.1, h.2.1, h.2.2.1, fun r0 b0 => (h.2.2.2 r0).1 b0, fun σ p r0 b0 => (h.2.2.2 r0).2 σ p b0⟩

def costStage3 (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  2 * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) +
    (n + 1) * ((n + 1) * ((2 * n + 1) * (4 * (2 * n + 1))))

def cStage3 (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (known : Bool) (twoPowF : Word B0)
    (Puv : Trunc2Wire (n + 1) (n + 1) B) (gs : List Gate) :
    List Gate × (Fin (n + 1) → Fin (n + 1) → Word (2 * n + 1)) :=
  let (g1, tmp) := cStage3Tmp n B known Puv gs
  let (g2, M) := cStage3M n B known tmp g1
  cStage3Shift n B B0 hB0_ge known twoPowF M g2

lemma cStage3_spec (n B B0 : ℕ) (hB0_ge : 2 * n + 1 ≤ B0) (hB : B = 2 * n + 10) (known : Bool)
    {twoPowF : Word B0} {Puv : Trunc2Wire (n + 1) (n + 1) B} {gs : List Gate}
    (hgs : ValidCircuit (N_in n known) gs)
    (htp : ValidWord (N_in n known) gs twoPowF) (hP : ValidTrunc2 (N_in n known) gs Puv)
    (htp_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
      wireAt gs (inputBits known σ p) (twoPowF ⟨k.val, by omega⟩) =
        decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩))
    (hP_sem : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
      trunc2Val gs (inputBits known σ p) Puv = arcProdUV (R := ZMod (2 ^ B)) σ p) :
    let N0 := N_in n known
    let r := cStage3 n B B0 hB0_ge known twoPowF Puv gs
    ValidCircuit N0 r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + costStage3 n ∧
    (∀ r0 b0, ValidWord N0 r.1 (r.2 r0 b0)) ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r0 b0 : Fin (n + 1)),
      wordNat r.1 (inputBits known σ p) (r.2 r0 b0) = hist σ p r0 b0 := by
  intro N0
  dsimp only [cStage3]
  set r1 := cStage3Tmp n B known Puv gs with hr1
  obtain ⟨v1, e1, l1, w1, f1⟩ := cStage3Tmp_spec n B known (Puv := Puv) hgs hP
  rw [← hr1] at v1 e1 l1 w1 f1
  set r2 := cStage3M n B known r1.2 r1.1 with hr2
  obtain ⟨v2, e2, l2, w2, f2⟩ := cStage3M_spec n B known (tmp := r1.2) v1 w1
  rw [← hr2] at v2 e2 l2 w2 f2
  have htp2 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
      wireAt r2.1 (inputBits known σ p) (twoPowF ⟨k.val, by omega⟩) =
        decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩) := fun σ p k => by
    rw [wireAt_extends (e1.trans e2) (w := twoPowF ⟨k.val, by omega⟩) (by rw [(inputBits_hasConsts known σ p).1]; exact htp _)]
    exact htp_sem σ p k
  have hM2 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r0 b0 : Fin (n + 1)),
      wordNat r2.1 (inputBits known σ p) (r2.2 r0 b0) = 2 ^ (2 * n - freeCount p) * hist σ p r0 b0 := by
    intro σ p r0 b0
    have hc := inputBits_hasConsts known σ p
    have hz : wordZMod r2.1 (inputBits known σ p) (r2.2 r0 b0) =
        ((2 ^ (2 * n - freeCount p) * hist σ p r0 b0 : ℕ) : ZMod (2 ^ B)) := by
      rw [f2 _ hc r0 b0]
      simp_rw [f1 _ hc r0, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hcast := congrArg (Int.cast (R := ZMod (2 ^ B))) (inv_kraw_arcProdUV σ p r0 b0)
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at hcast
      have hLHS :
          (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            (krawCoeff n j.val b0.val : ZMod (2 ^ B)) *
              ((krawCoeff n i.val r0.val : ZMod (2 ^ B)) * wordZMod gs (inputBits known σ p) (Puv i j))) =
          ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            (krawCoeff n i.val r0.val : ZMod (2 ^ B)) * (krawCoeff n j.val b0.val : ZMod (2 ^ B)) *
              ((arcProdUV (R := ℤ) σ p).coeff i j : ZMod (2 ^ B)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        have hPij : wordZMod gs (inputBits known σ p) (Puv i j) =
            ((arcProdUV (R := ℤ) σ p).coeff i j : ZMod (2 ^ B)) := by
          have h1 := congrArg (fun P => P.coeff i j) (hP_sem σ p)
          have h2 := congrArg (fun P => P.coeff i j) (arcProdUV_mapHom (B := B) σ p)
          exact h1.trans h2.symm
        rw [hPij]; ring
      rw [hLHS, hcast]
      push_cast; ring
    have hlt : 2 ^ (2 * n - freeCount p) * hist σ p r0 b0 < 2 ^ B := by
      have h1 : 2 ^ (2 * n - freeCount p) * hist σ p r0 b0 ≤ 2 ^ (2 * n - freeCount p) * 2 ^ freeCount p :=
        Nat.mul_le_mul_left _ (hist_le_twoPow_freeCount σ p r0 b0)
      have h2 : 2 ^ (2 * n - freeCount p) * 2 ^ freeCount p = 2 ^ (2 * n) := by
        rw [← pow_add, Nat.sub_add_cancel (freeCount_le p)]
      have h3 : 2 ^ (2 * n) < 2 ^ B := Nat.pow_lt_pow_right (by omega) (by omega)
      omega
    have hposB : 0 < 2 ^ B := by positivity
    haveI : NeZero (2 ^ B) := ⟨Nat.ne_of_gt hposB⟩
    have hv := congrArg ZMod.val hz
    rw [wordZMod_val, ZMod.val_natCast, Nat.mod_eq_of_lt hlt] at hv
    exact hv
  obtain ⟨v3, e3, l3, w3, f3⟩ := cStage3Shift_spec n B B0 hB0_ge known (twoPowF := twoPowF) (M := r2.2) v2 (htp.extends (e1.trans e2)) w2 htp2 hM2
  have hcostS3 :
      2 * ((n + 1) * ((n + 1) * ((n + 1) * (13 * B * B + 13 * B)))) +
      (n + 1) * ((n + 1) * ((2 * n + 1) * (4 * (2 * n + 1)))) = costStage3 n := by
    unfold costStage3; rw [hB]
  exact ⟨v3, e1.trans (e2.trans e3), by linarith, w3, f3⟩

def costStage1 (n : ℕ) : ℕ :=
  let B := 2 * n + 10
  let B0 := 4 * n + 10
  (2 * n + 1) * (13 * B0) +
    3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * B0 * B0 + 13 * B0)) + 2 * (13 * B0))) +
    3 * ((2 * n + 1) * ((2 * n + 1) * (4 * B)))

lemma total_cost_le_pow25 {n : ℕ} (hn : 1 ≤ n) :
    costStage1 n + (2 * n) * costStepFalse n + costStage3 n ≤ (n + 2) ^ 25 ∧
    costStage1 n + costStage2True n + costStage3 n ≤ (n + 2) ^ 25 := by
  set M := n + 2
  have hM3 : 3 ≤ M := by omega
  have hB : 2 * n + 10 ≤ 5 * M := by omega
  have hB0 : 4 * n + 10 ≤ 5 * M := by omega
  have h2n1 : 2 * n + 1 ≤ 2 * M := by omega
  have h2n : 2 * n ≤ 2 * M := by omega
  have hn1 : n + 1 ≤ M := by omega
  have hM1 : 1 ≤ M := by omega
  have hM_le_sq : M ≤ M ^ 2 := by nlinarith
  have hM_le_3 : M ^ 2 ≤ M ^ 3 := by nlinarith
  have hM_le_4 : M ^ 3 ≤ M ^ 4 := by nlinarith
  have hM_le_5 : M ^ 4 ≤ M ^ 5 := by nlinarith
  have hM_le_6 : M ^ 5 ≤ M ^ 6 := by nlinarith
  have hM_le_7 : M ^ 6 ≤ M ^ 7 := by nlinarith
  have hM_le_8 : M ^ 7 ≤ M ^ 8 := by nlinarith
  have hBB : 13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10) ≤ 400 * M ^ 2 := by nlinarith
  have hBB0 : 13 * (4 * n + 10) * (4 * n + 10) + 13 * (4 * n + 10) ≤ 400 * M ^ 2 := by nlinarith
  have hZT : costZT_step n ≤ 15000 * M ^ 5 := by
    unfold costZT_step
    have h1 : (2 * n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10)) ≤ (2 * M) * (400 * M ^ 2) :=
      Nat.mul_le_mul h2n1 hBB
    have h2 : 3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) ≤
        3 * ((2 * M) * (3 * ((2 * M) * (400 * M ^ 2)))) :=
      Nat.mul_le_mul_left 3 (Nat.mul_le_mul h2n1 (Nat.mul_le_mul_left 3 h1))
    have h3 : 3 * ((2 * n + 1) * (4 * (2 * n + 10))) ≤ 3 * ((2 * M) * (4 * (5 * M))) :=
      Nat.mul_le_mul_left 3 (Nat.mul_le_mul h2n1 (Nat.mul_le_mul_left 4 hB))
    have h4 : 3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) +
        3 * ((2 * n + 1) * (4 * (2 * n + 10))) ≤ 15000 * M ^ 4 := by
      have : M ^ 2 ≤ M ^ 4 := le_trans hM_le_3 hM_le_4
      linarith [h2, h3]
    calc M * (3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) +
          3 * ((2 * n + 1) * (4 * (2 * n + 10))))
        ≤ M * (15000 * M ^ 4) := Nat.mul_le_mul_left M h4
      _ = 15000 * M ^ 5 := by ring
  have hUV : costUV_step n ≤ 500 * M ^ 7 := by
    unfold costUV_step
    have h1 : (n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10)) ≤ M * (400 * M ^ 2) :=
      Nat.mul_le_mul hn1 hBB
    have h2 : (n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) ≤
        M * (M * (M * (M * (400 * M ^ 2)))) :=
      Nat.mul_le_mul hn1 (Nat.mul_le_mul hn1 (Nat.mul_le_mul hn1 h1))
    have h3 : (n + 1) * ((n + 1) * (4 * (2 * n + 10))) ≤ M * (M * (4 * (5 * M))) :=
      Nat.mul_le_mul hn1 (Nat.mul_le_mul hn1 (Nat.mul_le_mul_left 4 hB))
    have h4 : (n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) +
        (n + 1) * ((n + 1) * (4 * (2 * n + 10))) ≤ 500 * M ^ 6 := by
      have : M ^ 3 ≤ M ^ 6 := le_trans hM_le_4 (le_trans hM_le_5 hM_le_6)
      linarith [h2, h3]
    calc M * ((n + 1) * ((n + 1) * ((n + 1) * ((n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) +
          (n + 1) * ((n + 1) * (4 * (2 * n + 10))))
        ≤ M * (500 * M ^ 6) := Nat.mul_le_mul_left M h4
      _ = 500 * M ^ 7 := by ring
  have hS1 : costStage1 n ≤ 20000 * M ^ 4 := by
    unfold costStage1
    have h1 : (2 * n + 1) * (13 * (4 * n + 10)) ≤ (2 * M) * (13 * (5 * M)) :=
      Nat.mul_le_mul h2n1 (Nat.mul_le_mul_left 13 hB0)
    have h2 : (2 * n + 1) * (13 * (4 * n + 10) * (4 * n + 10) + 13 * (4 * n + 10)) ≤ (2 * M) * (400 * M ^ 2) :=
      Nat.mul_le_mul h2n1 hBB0
    have h3 : 3 * ((2 * n + 1) * (3 * ((2 * n + 1) * (13 * (4 * n + 10) * (4 * n + 10) + 13 * (4 * n + 10))) + 2 * (13 * (4 * n + 10)))) ≤
        3 * ((2 * M) * (3 * ((2 * M) * (400 * M ^ 2)) + 2 * (13 * (5 * M)))) :=
      Nat.mul_le_mul_left 3 (Nat.mul_le_mul h2n1 (Nat.add_le_add (Nat.mul_le_mul_left 3 h2) (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 13 hB0))))
    have h4 : 3 * ((2 * n + 1) * ((2 * n + 1) * (4 * (2 * n + 10)))) ≤ 3 * ((2 * M) * ((2 * M) * (4 * (5 * M)))) :=
      Nat.mul_le_mul_left 3 (Nat.mul_le_mul h2n1 (Nat.mul_le_mul h2n1 (Nat.mul_le_mul_left 4 hB)))
    have : M ^ 2 ≤ M ^ 4 := le_trans hM_le_3 hM_le_4
    linarith [h1, h3, h4]
  have hS3 : costStage3 n ≤ 1000 * M ^ 5 := by
    unfold costStage3
    have h1 : 2 * ((n + 1) * ((n + 1) * ((n + 1) * (13 * (2 * n + 10) * (2 * n + 10) + 13 * (2 * n + 10))))) ≤
        2 * (M * (M * (M * (400 * M ^ 2)))) :=
      Nat.mul_le_mul_left 2 (Nat.mul_le_mul hn1 (Nat.mul_le_mul hn1 (Nat.mul_le_mul hn1 hBB)))
    have h2 : (n + 1) * ((n + 1) * ((2 * n + 1) * (4 * (2 * n + 1)))) ≤ M * (M * ((2 * M) * (4 * (2 * M)))) :=
      Nat.mul_le_mul hn1 (Nat.mul_le_mul hn1 (Nat.mul_le_mul h2n1 (Nat.mul_le_mul_left 4 h2n1)))
    linarith [h1, h2, hM_le_5]
  have hSF : (2 * n) * costStepFalse n ≤ 300000 * M ^ 8 := by
    have hstep : costStepFalse n ≤ 150000 * M ^ 7 := by
      unfold costStepFalse
      have hM17 : M ≤ M ^ 7 := le_trans hM_le_sq (le_trans hM_le_3 (le_trans hM_le_4 (le_trans hM_le_5 (le_trans hM_le_6 hM_le_7))))
      have hM27 : M ^ 2 ≤ M ^ 7 := le_trans hM_le_3 (le_trans hM_le_4 (le_trans hM_le_5 (le_trans hM_le_6 hM_le_7)))
      have hM57 : M ^ 5 ≤ M ^ 7 := le_trans hM_le_6 hM_le_7
      have hlin : 13 * (2 * n + 10) * (2 * n + 10) + 14 * (2 * n + 10) ≤ 400 * M ^ 2 := by nlinarith
      linarith [hB, hZT, hUV, hlin, hM17, hM27, hM57]
    calc (2 * n) * costStepFalse n ≤ (2 * M) * (150000 * M ^ 7) := Nat.mul_le_mul h2n hstep
      _ = 300000 * M ^ 8 := by ring
  have hST : costStage2True n ≤ 300000 * M ^ 8 := by
    unfold costStage2True
    have hM28 : M ^ 2 ≤ M ^ 8 := le_trans hM_le_3 (le_trans hM_le_4 (le_trans hM_le_5 (le_trans hM_le_6 (le_trans hM_le_7 hM_le_8))))
    have hM38 : M ^ 3 ≤ M ^ 8 := le_trans hM_le_4 (le_trans hM_le_5 (le_trans hM_le_6 (le_trans hM_le_7 hM_le_8)))
    have hM48 : M ^ 4 ≤ M ^ 8 := le_trans hM_le_5 (le_trans hM_le_6 (le_trans hM_le_7 hM_le_8))
    have hM68 : M ^ 6 ≤ M ^ 8 := le_trans hM_le_7 hM_le_8
    have h1 : (2 * n) * ((2 * n) * 5) ≤ 20 * M ^ 2 := by
      calc (2 * n) * ((2 * n) * 5) ≤ (2 * M) * ((2 * M) * 5) := Nat.mul_le_mul h2n (Nat.mul_le_mul h2n (le_refl 5))
        _ = 20 * M ^ 2 := by ring
    have h2 : (2 * n) * ((2 * n) * ((2 * n) * (2 * (2 * n)))) ≤ 32 * M ^ 4 := by
      calc (2 * n) * ((2 * n) * ((2 * n) * (2 * (2 * n))))
          ≤ (2 * M) * ((2 * M) * ((2 * M) * (2 * (2 * M)))) :=
            Nat.mul_le_mul h2n (Nat.mul_le_mul h2n (Nat.mul_le_mul h2n (Nat.mul_le_mul_left 2 h2n)))
        _ = 32 * M ^ 4 := by ring
    have h3 : (2 * n) * (2 * n + 2 * n) ≤ 8 * M ^ 2 := by
      calc (2 * n) * (2 * n + 2 * n) ≤ (2 * M) * (2 * M + 2 * M) := Nat.mul_le_mul h2n (Nat.add_le_add h2n h2n)
        _ = 8 * M ^ 2 := by ring
    have h4 : (2 * n) * ((2 * n) * (13 * (2 * n + 10))) ≤ 260 * M ^ 3 := by
      calc (2 * n) * ((2 * n) * (13 * (2 * n + 10))) ≤ (2 * M) * ((2 * M) * (13 * (5 * M))) :=
            Nat.mul_le_mul h2n (Nat.mul_le_mul h2n (Nat.mul_le_mul_left 13 hB))
        _ = 260 * M ^ 3 := by ring
    have h5 : (2 * n) * (n * (13 * (2 * n + 10))) ≤ 130 * M ^ 3 := by
      calc (2 * n) * (n * (13 * (2 * n + 10))) ≤ (2 * M) * (M * (13 * (5 * M))) :=
            Nat.mul_le_mul h2n (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left 13 hB))
        _ = 130 * M ^ 3 := by ring
    have h6a : (2 * n) * (7 * (2 * n + 10) + 7 * (2 * n + 10) + 2) + (2 * n) * (13 * (2 * n + 10)) ≤ 274 * M ^ 2 := by
      have h6a1 : (2 * n) * (7 * (2 * n + 10) + 7 * (2 * n + 10) + 2) ≤ (2 * M) * (7 * (5 * M) + 7 * (5 * M) + 2 * M) :=
        Nat.mul_le_mul h2n (by omega)
      have h6a2 : (2 * n) * (13 * (2 * n + 10)) ≤ (2 * M) * (13 * (5 * M)) :=
        Nat.mul_le_mul h2n (Nat.mul_le_mul_left 13 hB)
      calc (2 * n) * (7 * (2 * n + 10) + 7 * (2 * n + 10) + 2) + (2 * n) * (13 * (2 * n + 10))
          ≤ (2 * M) * (7 * (5 * M) + 7 * (5 * M) + 2 * M) + (2 * M) * (13 * (5 * M)) := Nat.add_le_add h6a1 h6a2
        _ = 274 * M ^ 2 := by ring
    have h6 : (2 * n + 1) * ((n + 1) * ((2 * n) * (7 * (2 * n + 10) + 7 * (2 * n + 10) + 2) + (2 * n) * (13 * (2 * n + 10)))) ≤ 548 * M ^ 4 := by
      calc (2 * n + 1) * ((n + 1) * ((2 * n) * (7 * (2 * n + 10) + 7 * (2 * n + 10) + 2) + (2 * n) * (13 * (2 * n + 10))))
          ≤ (2 * M) * (M * (274 * M ^ 2)) := Nat.mul_le_mul h2n1 (Nat.mul_le_mul hn1 h6a)
        _ = 548 * M ^ 4 := by ring
    have h7 : (2 * n) * (2 * costZT_step n) ≤ 60000 * M ^ 6 := by
      calc (2 * n) * (2 * costZT_step n) ≤ (2 * M) * (2 * (15000 * M ^ 5)) := Nat.mul_le_mul h2n (Nat.mul_le_mul_left 2 hZT)
        _ = 60000 * M ^ 6 := by ring
    have hstepT : costStepTrue n ≤ 40000 * M ^ 7 := by
      unfold costStepTrue
      have hM17 : M ≤ M ^ 7 := le_trans hM_le_sq (le_trans hM_le_3 (le_trans hM_le_4 (le_trans hM_le_5 (le_trans hM_le_6 hM_le_7))))
      have hM27 : M ^ 2 ≤ M ^ 7 := le_trans hM_le_3 (le_trans hM_le_4 (le_trans hM_le_5 (le_trans hM_le_6 hM_le_7)))
      have hM57 : M ^ 5 ≤ M ^ 7 := le_trans hM_le_6 hM_le_7
      have hsq : 13 * (2 * n + 10) * (2 * n + 10) ≤ 400 * M ^ 2 := le_trans (Nat.le_add_right _ _) hBB
      linarith only [hB, hZT, hUV, hsq, hM17, hM27, hM57]
    have h8 : (2 * n) * costStepTrue n ≤ 80000 * M ^ 8 := by
      calc (2 * n) * costStepTrue n ≤ (2 * M) * (40000 * M ^ 7) := Nat.mul_le_mul h2n hstepT
        _ = 80000 * M ^ 8 := by ring
    calc _ ≤ 20 * M ^ 2 + 32 * M ^ 4 + 8 * M ^ 2 + 260 * M ^ 3 + 130 * M ^ 3 + 548 * M ^ 4 + 60000 * M ^ 6 + 80000 * M ^ 8 :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1 h2) h3) h4) h5) h6) h7) h8
      _ ≤ 300000 * M ^ 8 := by omega
  have h17 : 1000000 ≤ M ^ 17 :=
    le_trans (by norm_num : 1000000 ≤ 3 ^ 17) (Nat.pow_le_pow_left hM3 17)
  have hbig : 1000000 * M ^ 8 ≤ M ^ 25 := by
    calc 1000000 * M ^ 8 ≤ M ^ 17 * M ^ 8 := Nat.mul_le_mul_right _ h17
      _ = M ^ 25 := by rw [← pow_add]
  have hM48 : M ^ 4 ≤ M ^ 8 := le_trans hM_le_5 (le_trans hM_le_6 (le_trans hM_le_7 hM_le_8))
  have hM58 : M ^ 5 ≤ M ^ 8 := le_trans hM_le_6 (le_trans hM_le_7 hM_le_8)
  constructor <;> omega

def buildFull (n B B0 : ℕ) (hB_ge : 2 ≤ B) (hB0_ge : 2 * n + 1 ≤ B0) (known : Bool) :
    List Gate × (Fin (n + 1) → Fin (n + 1) → Word (2 * n + 1)) :=
  let (g1, twoPowF, F_zt) := cStage1 n B B0 hB0_ge known
  match known with
  | false =>
    let (g2, Puv) := cStage2False n B hB_ge F_zt g1
    cStage3 n B B0 hB0_ge false twoPowF Puv g2
  | true =>
    let (g2, Puv) := cStage2True n B F_zt g1
    cStage3 n B B0 hB0_ge true twoPowF Puv g2

lemma buildFull_spec (n B B0 : ℕ) (hn : 1 ≤ n) (hB_ge : 2 ≤ B) (hB0_ge : 2 * n + 1 ≤ B0)
    (hB : B = 2 * n + 10) (hB0 : B0 = 4 * n + 10) (known : Bool) :
    let N0 := N_in n known
    let r := buildFull n B B0 hB_ge hB0_ge known
    ValidCircuit N0 r.1 ∧ r.1.length ≤ (n + 2) ^ 25 ∧
    (∀ r0 b0, ValidWord N0 r.1 (r.2 r0 b0)) ∧
    ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (r0 b0 : Fin (n + 1)),
      wordNat r.1 (inputBits known σ p) (r.2 r0 b0) = hist σ p r0 b0 := by
  intro N0
  dsimp only [buildFull]
  obtain ⟨hbF, hbT⟩ := total_cost_le_pow25 hn
  cases known
  · set r1 := cStage1 n B B0 hB0_ge false with hr1
    obtain ⟨v1, l1, w1tp, w1F, f1⟩ := cStage1_spec n B B0 hB0_ge hB hB0 false
    rw [← hr1] at v1 l1 w1tp w1F f1
    set r2 := cStage2False n B hB_ge r1.2.2 r1.1 with hr2
    have hF1 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool),
        trunc2Val r1.1 (inputBits false σ p) r1.2.2 = arcProdZT (R := ZMod (2 ^ B)) σ p :=
      fun σ p => Trunc2.ext fun h d => (f1 σ p).2 h (Or.inl rfl) d
    obtain ⟨v2, e2, l2, w2, f2⟩ := cStage2False_spec n B hn hB_ge hB (F_zt := r1.2.2) v1 w1F hF1
    rw [← hr2] at v2 e2 l2 w2 f2
    have htp2 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
        wireAt r2.1 (inputBits false σ p) (r1.2.1 ⟨k.val, by omega⟩) =
          decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩) := fun σ p k => by
      rw [wireAt_extends e2 (w := r1.2.1 ⟨k.val, by omega⟩) (by rw [(inputBits_hasConsts false σ p).1]; exact w1tp _)]
      exact (f1 σ p).1 k
    obtain ⟨v3, e3, l3, w3, f3⟩ := cStage3_spec n B B0 hB0_ge hB false (twoPowF := r1.2.1) (Puv := r2.2) v2 (w1tp.extends e2) w2 htp2 f2
    refine ⟨v3, ?_, w3, f3⟩
    have l1' : r1.1.length ≤ costStage1 n := by unfold costStage1; rw [← hB, ← hB0]; exact l1
    linarith
  · set r1 := cStage1 n B B0 hB0_ge true with hr1
    obtain ⟨v1, l1, w1tp, w1F, f1⟩ := cStage1_spec n B B0 hB0_ge hB hB0 true
    rw [← hr1] at v1 l1 w1tp w1F f1
    set r2 := cStage2True n B r1.2.2 r1.1 with hr2
    have hF1 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (h : Fin 3),
        h.val < 2 → ∀ d : Fin (2 * n + 1),
          (trunc2Val r1.1 (inputBits true σ p) r1.2.2).coeff h d = (arcProdZT (R := ZMod (2 ^ B)) σ p).coeff h d :=
      fun σ p h hh2 d => (f1 σ p).2 h (Or.inr hh2) d
    obtain ⟨v2, e2, l2, w2, f2⟩ := cStage2True_spec n B hB (F_zt := r1.2.2) v1 w1F hF1
    rw [← hr2] at v2 e2 l2 w2 f2
    have htp2 : ∀ (σ : Equiv.Perm (Fin n)) (p : Bool × Fin n → Option Bool) (k : Fin (2 * n + 1)),
        wireAt r2.1 (inputBits true σ p) (r1.2.1 ⟨k.val, by omega⟩) =
          decide (k = ⟨freeCount p, by have := freeCount_le p; omega⟩) := fun σ p k => by
      rw [wireAt_extends e2 (w := r1.2.1 ⟨k.val, by omega⟩) (by rw [(inputBits_hasConsts true σ p).1]; exact w1tp _)]
      exact (f1 σ p).1 k
    obtain ⟨v3, e3, l3, w3, f3⟩ := cStage3_spec n B B0 hB0_ge hB true (twoPowF := r1.2.1) (Puv := r2.2) v2 (w1tp.extends e2) w2 htp2 f2
    refine ⟨v3, ?_, w3, f3⟩
    have l1' : r1.1.length ≤ costStage1 n := by unfold costStage1; rw [← hB, ← hB0]; exact l1
    linarith

end MainAssembly

end PEqualNP.Outside.L_pcx_399_aux

theorem PEqualNP.Outside.L_pcx_399 :
  ∃ C : ℕ, 0 < C ∧ ∀ t : ℕ,
    let n := t+1
    let I := Fin n
    let J := Fin (n+1)
    let V := Bool × I
    let P := V → Option Bool
    let S := Fin (2*n+1)
    let W := Fin (4*n+3)
    let hist := fun (σ : Equiv.Perm I) (p : P) (r b : J) =>
      ((Finset.univ : Finset (V → Bool)).filter (fun x =>
        (∀ v, p v = none ∨ p v = some (x v)) ∧
        (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,i))).card = r.val ∧
        (Finset.univ.filter (fun i : I => x (false,i) ≠ x (true,σ i))).card = b.val)).card
    let profile := fun (H : J → J → ℕ) (h : ℕ) (s : S) =>
      ∑ r : J, ∑ b : J, if r.val+b.val = s.val then Nat.choose r.val h * H r b else 0
    let countBits := fun (k : ℕ) (H : J → J → ℕ) =>
      (List.ofFn (fun h : Fin k => (List.ofFn (fun s : S =>
        List.ofFn (fun i : W => (profile H h.val s).testBit i.val))).flatten)).flatten
    let N := fun (known : Bool) => 2 + (if known then n*n+2*n else 0) +
      (if known then 2 else 3)*(2*n+1)*(4*n+3)
    ∀ known : Bool,
      ∃ (g : PEqualNP.CircuitLowerBounds.Circuit) (out : J → J → S → Fin (N known+g.size)),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N known) g ∧ g.size ≤ (n+2)^C ∧
        (∀ gate ∈ g.gates, ((gate.op = .and ∨ gate.op = .or) ∧ gate.inputs.length = 2) ∨
          (gate.op = .not ∧ gate.inputs.length = 1)) ∧
        ∀ (σ : Equiv.Perm I) (p : P),
          let perm := (List.ofFn (fun i : I => List.ofFn (fun j : I => decide (σ i = j)))).flatten
          let mask := (List.ofFn (fun i : I => (p (false,i)).isSome)) ++
            List.ofFn (fun i : I => (p (true,i)).isSome)
          let H := hist σ p
          let ws := g.wires ([false,true] ++ (if known then perm ++ mask else []) ++
            countBits (if known then 2 else 3) H)
          ∀ r b : J, (∑ i : S, (ws.getD (out r b i).val false).toNat * 2^i.val) = H r b := by
  refine ⟨25, by omega, fun t => ?_⟩
  dsimp only
  intro known
  obtain ⟨hv, hlen, hout, hsem⟩ := PEqualNP.Outside.L_pcx_399_aux.buildFull_spec (t + 1) (2 * (t + 1) + 10) (4 * (t + 1) + 10) (by omega) (by omega) (by omega) rfl rfl known
  refine ⟨PEqualNP.CircuitLowerBounds.Circuit.mk (PEqualNP.Outside.L_pcx_399_aux.buildFull (t + 1) (2 * (t + 1) + 10) (4 * (t + 1) + 10) (by omega) (by omega) known).1 0,
    fun r b i => ⟨(PEqualNP.Outside.L_pcx_399_aux.buildFull (t + 1) (2 * (t + 1) + 10) (4 * (t + 1) + 10) (by omega) (by omega) known).2 r b i, hout r b i⟩,
    PEqualNP.Outside.L_pcx_399_aux.validCircuit_to_readsBack hv,
    hlen, hv.1, fun σ p r b => hsem σ p r b⟩
