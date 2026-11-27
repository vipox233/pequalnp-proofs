import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_435_aux

private def sgn (b : ZMod 2) : ℚ := if b = 0 then 1 else -1

private lemma sgn_zero : sgn 0 = 1 := rfl

private lemma sgn_one : sgn 1 = -1 := by
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  simp [sgn, h10]

private lemma sgn_add (u v : ZMod 2) : sgn (u + v) = sgn u * sgn v := by
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have h10 : (1 : ZMod 2) ≠ 0 := by decide
  have hu : u = 0 ∨ u = 1 := by
    rcases u with ⟨u, hu⟩
    interval_cases u
    · left; rfl
    · right; rfl
  have hv : v = 0 ∨ v = 1 := by
    rcases v with ⟨v, hv⟩
    interval_cases v
    · left; rfl
    · right; rfl
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> simp [sgn, h11, h10]

private def dot2 {n : ℕ} (s v : Fin n → ZMod 2) : ZMod 2 :=
  (Finset.univ : Finset (Fin n)).sum (fun i => s i * v i)

private lemma dot2_comm {n : ℕ} (s v : Fin n → ZMod 2) : dot2 s v = dot2 v s := by
  unfold dot2
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

private lemma dot2_add_right {n : ℕ} (s x y : Fin n → ZMod 2) :
    dot2 s (x + y) = dot2 s x + dot2 s y := by
  unfold dot2
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  change s i * (x i + y i) = s i * x i + s i * y i
  ring

private lemma dot2_add_left {n : ℕ} (s t x : Fin n → ZMod 2) :
    dot2 (s + t) x = dot2 s x + dot2 t x := by
  rw [dot2_comm, dot2_add_right, dot2_comm x s, dot2_comm x t]

private lemma add_self_zmod2 {n : ℕ} (x y : Fin n → ZMod 2) : x + (x + y) = y := by
  funext i
  change x i + (x i + y i) = y i
  have h0 : x i + x i = 0 := by
    generalize x i = u
    fin_cases u <;> decide
  rw [← add_assoc, h0, zero_add]

private lemma add_eq_zero_iff {n : ℕ} (s t : Fin n → ZMod 2) : s + t = 0 ↔ s = t := by
  constructor
  · intro h
    have h1 : s + (s + t) = s + 0 := congrArg (fun z => s + z) h
    rw [add_self_zmod2, add_zero] at h1
    exact h1.symm
  · intro h
    subst h
    funext i
    change s i + s i = 0
    generalize s i = u
    fin_cases u <;> decide

private def hadMat (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℚ :=
  fun x s => sgn (dot2 s x)

private lemma sum_sgn_dot2_ne {n : ℕ} (u : Fin n → ZMod 2) (hu : u ≠ 0) :
    (∑ x : Fin n → ZMod 2, sgn (dot2 u x)) = 0 := by
  have hex : ∃ j : Fin n, u j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu
    funext j
    exact h j
  rcases hex with ⟨j, hj⟩
  have huj : u j = 1 := by
    generalize u j = z at hj ⊢
    fin_cases z
    · exact False.elim (hj rfl)
    · rfl
  let e : Fin n → ZMod 2 := Pi.single j (1 : ZMod 2)
  have hdot : dot2 u e = 1 := by
    unfold dot2
    rw [Finset.sum_eq_single j]
    · simp [e, huj]
    · intro i _ hij
      simp [e, Pi.single_eq_of_ne hij]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ j))
  have hshift :
      (∑ x : Fin n → ZMod 2, sgn (dot2 u (x + e))) =
        ∑ x : Fin n → ZMod 2, sgn (dot2 u x) := by
    refine Fintype.sum_equiv (Equiv.addRight e) _ _ ?_
    intro x
    rfl
  have hneg :
      (∑ x : Fin n → ZMod 2, sgn (dot2 u (x + e))) =
        -(∑ x : Fin n → ZMod 2, sgn (dot2 u x)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [dot2_add_right, hdot, sgn_add, sgn_one]
    ring
  linarith

private lemma hadMat_mul_self (n : ℕ) :
    hadMat n * hadMat n = ((2 : ℚ) ^ n) • (1 : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℚ) := by
  ext s t
  simp only [Matrix.mul_apply, hadMat, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hterm : ∀ x : Fin n → ZMod 2, sgn (dot2 x s) * sgn (dot2 t x) = sgn (dot2 (s + t) x) := by
    intro x
    rw [dot2_comm x s, dot2_add_left, sgn_add]
  simp_rw [hterm]
  by_cases hst : s = t
  · subst hst
    have hzero : s + s = 0 := (add_eq_zero_iff s s).mpr rfl
    rw [hzero]
    have hdot0 : ∀ x : Fin n → ZMod 2, dot2 (0 : Fin n → ZMod 2) x = 0 := by
      intro x
      unfold dot2
      simp
    simp only [hdot0, sgn_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ↓reduceIte]
    have hcard : Fintype.card (Fin n → ZMod 2) = 2 ^ n := by
      simp [Fintype.card_pi, ZMod.card]
    rw [hcard]
    push_cast
    rfl
  · simp only [hst, ↓reduceIte, mul_zero]
    exact sum_sgn_dot2_ne (s + t) (fun h => hst ((add_eq_zero_iff s t).mp h))

private def hadInv (n : ℕ) : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℚ :=
  (((2 : ℚ) ^ n)⁻¹) • hadMat n

private lemma hadMat_mul_hadInv (n : ℕ) : hadMat n * hadInv n = 1 := by
  unfold hadInv
  rw [Matrix.mul_smul, hadMat_mul_self, smul_smul]
  have hne : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [inv_mul_cancel₀ hne, one_smul]

private lemma hadInv_mul_hadMat (n : ℕ) : hadInv n * hadMat n = 1 := by
  unfold hadInv
  rw [Matrix.smul_mul, hadMat_mul_self, smul_smul]
  have hne : (2 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  rw [inv_mul_cancel₀ hne, one_smul]

private def xorMat (n : ℕ) (f : (Fin n → ZMod 2) → ℚ) :
    Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℚ :=
  fun x y => f (x + y)

private lemma xor_mul_hadMat (n : ℕ) (f : (Fin n → ZMod 2) → ℚ) :
    xorMat n f * hadMat n =
      hadMat n * Matrix.diagonal (fun s =>
        (Finset.univ : Finset (Fin n → ZMod 2)).sum (fun v =>
          if (Finset.univ : Finset (Fin n)).sum (fun i => s i * v i) = 0
          then f v else -f v)) := by
  ext x s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, hadMat, xorMat]
  have h1 :
      (∑ y : Fin n → ZMod 2, f (x + y) * sgn (dot2 s y)) =
        ∑ v : Fin n → ZMod 2, f v * sgn (dot2 s (x + v)) := by
    refine Fintype.sum_equiv (Equiv.addLeft x) _ _ ?_
    intro y
    change f (x + y) * sgn (dot2 s y) = f (x + y) * sgn (dot2 s (x + (x + y)))
    rw [add_self_zmod2]
  rw [h1]
  have h2 :
      (∑ v : Fin n → ZMod 2, f v * sgn (dot2 s (x + v))) =
        sgn (dot2 s x) * ∑ v : Fin n → ZMod 2, f v * sgn (dot2 s v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro v _
    rw [dot2_add_right, sgn_add]
    ring
  rw [h2]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro v _
  unfold sgn dot2
  split_ifs <;> ring

private def hadEquiv (n : ℕ) : ((Fin n → ZMod 2) → ℚ) ≃ₗ[ℚ] ((Fin n → ZMod 2) → ℚ) :=
  LinearEquiv.ofLinear (hadMat n).mulVecLin (hadInv n).mulVecLin
    (by
      apply LinearMap.ext
      intro v
      funext x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, hadMat_mul_hadInv, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro v
      funext x
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, hadInv_mul_hadMat, Matrix.one_mulVec])

private lemma diag_range_finrank {α : Type*} [Fintype α] [DecidableEq α] (w : α → ℚ) :
    Module.finrank ℚ (LinearMap.range (Matrix.diagonal w).mulVecLin) =
      ((Finset.univ : Finset α).filter (fun a => w a ≠ 0)).card := by
  let S := {a : α // w a ≠ 0}
  let toFun : LinearMap.range (Matrix.diagonal w).mulVecLin →ₗ[ℚ] (S → ℚ) :=
    { toFun := fun y a => y.1 a.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let invFun : (S → ℚ) →ₗ[ℚ] LinearMap.range (Matrix.diagonal w).mulVecLin :=
    { toFun := fun u =>
        ⟨fun a => if h : w a ≠ 0 then u ⟨a, h⟩ else 0, by
          refine ⟨fun a => if h : w a ≠ 0 then (w a)⁻¹ * u ⟨a, h⟩ else 0, ?_⟩
          funext a
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal]
          by_cases h : w a ≠ 0
          · simp [h]
          · simp only [h, ↓reduceDIte]
            have h0 : w a = 0 := not_not.mp h
            simp [h0]⟩
      map_add' := fun u v => by
        apply Subtype.ext
        funext a
        change (if h : w a ≠ 0 then u ⟨a, h⟩ + v ⟨a, h⟩ else 0) =
          (if h : w a ≠ 0 then u ⟨a, h⟩ else 0) + (if h : w a ≠ 0 then v ⟨a, h⟩ else 0)
        split_ifs <;> ring
      map_smul' := fun c u => by
        apply Subtype.ext
        funext a
        change (if h : w a ≠ 0 then c * u ⟨a, h⟩ else 0) =
          c * (if h : w a ≠ 0 then u ⟨a, h⟩ else 0)
        split_ifs <;> ring }
  have e : LinearMap.range (Matrix.diagonal w).mulVecLin ≃ₗ[ℚ] (S → ℚ) :=
    LinearEquiv.ofLinear toFun invFun
      (by
        apply LinearMap.ext
        intro u
        funext a
        simp [toFun, invFun, a.2])
      (by
        apply LinearMap.ext
        intro y
        apply Subtype.ext
        funext a
        rcases y with ⟨v, x, hx⟩
        change (if h : w a ≠ 0 then v a else 0) = v a
        by_cases h : w a ≠ 0
        · simp [h]
        · simp only [h, ↓reduceDIte]
          have h0 : w a = 0 := not_not.mp h
          have hva : v a = w a * x a := by
            have := congrFun hx a
            simpa [Matrix.mulVecLin_apply, Matrix.mulVec_diagonal] using this.symm
          rw [hva, h0, zero_mul])
  rw [e.finrank_eq, Module.finrank_pi, Fintype.card_subtype]

end PEqualNP.Outside.L_lib_435_aux

theorem PEqualNP.Outside.L_lib_435 : (∀ (n : ℕ) (f : (Fin n → ZMod 2) → ℚ),
  let X : Matrix (Fin n → ZMod 2) (Fin n → ZMod 2) ℚ :=
    fun x y => f (x + y)
  let walsh := fun s : Fin n → ZMod 2 =>
    (Finset.univ : Finset (Fin n → ZMod 2)).sum (fun v =>
      if (Finset.univ : Finset (Fin n)).sum (fun i => s i * v i) = 0
      then f v else -f v)
  X.rank = ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun a => walsh a ≠ 0)).card) := by
  intro n f X walsh
  have hX : X = PEqualNP.Outside.L_lib_435_aux.hadMat n * Matrix.diagonal walsh *
      PEqualNP.Outside.L_lib_435_aux.hadInv n := by
    have hmul := PEqualNP.Outside.L_lib_435_aux.xor_mul_hadMat n f
    calc
      X = X * 1 := (Matrix.mul_one X).symm
      _ = X * (PEqualNP.Outside.L_lib_435_aux.hadMat n * PEqualNP.Outside.L_lib_435_aux.hadInv n) := by
        rw [PEqualNP.Outside.L_lib_435_aux.hadMat_mul_hadInv]
      _ = (X * PEqualNP.Outside.L_lib_435_aux.hadMat n) * PEqualNP.Outside.L_lib_435_aux.hadInv n := by
        rw [Matrix.mul_assoc]
      _ = PEqualNP.Outside.L_lib_435_aux.hadMat n * Matrix.diagonal walsh *
            PEqualNP.Outside.L_lib_435_aux.hadInv n := by
        change (PEqualNP.Outside.L_lib_435_aux.xorMat n f * PEqualNP.Outside.L_lib_435_aux.hadMat n) *
          PEqualNP.Outside.L_lib_435_aux.hadInv n = _
        rw [hmul]
  rw [Matrix.rank, hX]
  let e := PEqualNP.Outside.L_lib_435_aux.hadEquiv n
  have hlin :
      (PEqualNP.Outside.L_lib_435_aux.hadMat n * Matrix.diagonal walsh *
          PEqualNP.Outside.L_lib_435_aux.hadInv n).mulVecLin =
        e.toLinearMap.comp ((Matrix.diagonal walsh).mulVecLin.comp e.symm.toLinearMap) := by
    apply LinearMap.ext
    intro v
    funext x
    simp [e, PEqualNP.Outside.L_lib_435_aux.hadEquiv, Matrix.mulVec_mulVec]
  rw [hlin, LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top _ e.symm.range,
    LinearEquiv.finrank_map_eq, PEqualNP.Outside.L_lib_435_aux.diag_range_finrank]
