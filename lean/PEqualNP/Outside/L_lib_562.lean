import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_562_aux


open Finset Module

section Onb

variable {X : Type*} [Fintype X]

theorem exists_onb (V : Submodule ℝ (X → ℝ)) :
    ∃ (k : ℕ) (e : Fin k → (X → ℝ)), k = finrank ℝ V ∧ (∀ i, e i ∈ V) ∧
      (∀ i j, ∑ x, e i x * e j x = if i = j then 1 else 0) ∧
      (∀ q ∈ V, ∀ x, q x = ∑ i, (∑ z, e i z * q z) * e i x) := by
  classical
  let L : (X → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ X := (WithLp.linearEquiv 2 ℝ (X → ℝ)).symm
  let V' : Submodule ℝ (EuclideanSpace ℝ X) := V.map (L : (X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ X)
  have hfin : finrank ℝ V' = finrank ℝ V := LinearEquiv.finrank_map_eq L V
  let b := stdOrthonormalBasis ℝ V'
  have hin : ∀ (u v : EuclideanSpace ℝ X), inner ℝ u v = ∑ x, u.ofLp x * v.ofLp x := by
    intro u v
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  refine ⟨finrank ℝ V', fun i => ((b i : V') : EuclideanSpace ℝ X).ofLp, hfin, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨q, hq, hq2⟩ := (b i).2
    have : ((b i : V') : EuclideanSpace ℝ X).ofLp = q := by rw [← hq2]; rfl
    show ((b i : V') : EuclideanSpace ℝ X).ofLp ∈ V
    rw [this]
    exact hq
  · intro i j
    have h := (orthonormal_iff_ite.mp b.orthonormal) i j
    rw [Submodule.coe_inner, hin] at h
    exact h
  · intro q hq x
    have hq' : L q ∈ V' := ⟨q, hq, rfl⟩
    have h := b.sum_repr' ⟨L q, hq'⟩
    have h2 := congrArg (fun v : V' => (v : EuclideanSpace ℝ X).ofLp x) h
    simp only [Submodule.coe_sum, Submodule.coe_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Submodule.coe_inner, hin] at h2
    exact h2.symm

theorem exists_onb' (V : Submodule ℝ (X → ℝ)) :
    ∃ (k : ℕ) (e : Fin k → (X → ℝ)), k = finrank ℝ V ∧ (∀ i, e i ∈ V) ∧
      (∀ i j, ∑ x, e i x * e j x = if i = j then 1 else 0) ∧
      (∀ q ∈ V, ∀ x, q x = ∑ i, (∑ z, e i z * q z) * e i x) ∧
      (∀ q ∈ V, ∑ i, (∑ z, e i z * q z) ^ 2 = ∑ z, q z ^ 2) := by
  obtain ⟨k, e, hk, he, ho, hx⟩ := exists_onb V
  refine ⟨k, e, hk, he, ho, hx, ?_⟩
  intro q hq
  calc ∑ i, (∑ z, e i z * q z) ^ 2
      = ∑ i, ∑ x, (∑ z, e i z * q z) * e i x * q x := by
        apply sum_congr rfl
        intro i _
        rw [sq, mul_sum]
        apply sum_congr rfl
        intros
        ring
    _ = ∑ x, (∑ i, (∑ z, e i z * q z) * e i x) * q x := by
        rw [sum_comm]
        apply sum_congr rfl
        intro x _
        rw [sum_mul]
    _ = ∑ x, q x ^ 2 := by
        apply sum_congr rfl
        intro x _
        rw [← hx q hq x, sq]

theorem lev_exists (V : Submodule ℝ (X → ℝ)) :
    ∃ s : X → ℝ, (∀ x, 0 ≤ s x) ∧ (∀ q ∈ V, ∀ x, q x ^ 2 ≤ s x * ∑ z, q z ^ 2) ∧
      (∀ x, ∃ q ∈ V, q x = s x ∧ ∑ z, q z ^ 2 = s x) ∧ ∑ x, s x = finrank ℝ V := by
  classical
  obtain ⟨k, e, hk, he, ho, hx, hpars⟩ := exists_onb' V
  refine ⟨fun x => ∑ i, e i x ^ 2, fun x => sum_nonneg fun i _ => sq_nonneg _, ?_, ?_, ?_⟩
  · intro q hq x
    rw [hx q hq x, ← hpars q hq, mul_comm]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  · intro x
    have hmem : (∑ i, e i x • e i) ∈ V :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
    have hcoef : ∀ i, ∑ z, e i z * (∑ j, e j x • e j) z = e i x := by
      intro i
      have : ∀ z, e i z * (∑ j, e j x • e j) z = ∑ j, e j x * (e i z * e j z) := by
        intro z
        rw [Finset.sum_apply, mul_sum]
        apply sum_congr rfl
        intro j _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      simp_rw [this]
      rw [sum_comm]
      simp_rw [← mul_sum, ho]
      simp
    refine ⟨∑ i, e i x • e i, hmem, ?_, ?_⟩
    · rw [Finset.sum_apply]
      apply sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · rw [← hpars _ hmem]
      simp_rw [hcoef]
  · rw [sum_comm]
    have : ∀ i, ∑ x, e i x ^ 2 = 1 := by
      intro i
      have := ho i i
      simp only [ite_true] at this
      rw [← this]
      apply sum_congr rfl
      intros
      ring
    simp_rw [this]
    simp [hk]

theorem final_ineq {Y : Type*} [Fintype Y] [Nonempty Y] [DecidableEq X] (A : X → Y → ℝ)
    (hA : ∀ x y, A x y = 1 ∨ A x y = -1)
    (hO : ∀ x x', ∑ y, A x y * A x' y = if x = x' then (Fintype.card Y : ℝ) else 0)
    (V : Submodule ℝ (X → ℝ)) (q : Y → X → ℝ) (hq : ∀ y, q y ∈ V)
    (hne : ∀ y, 0 < ∑ z, q y z ^ 2) (hsign : ∀ y x, 0 ≤ A x y * q y x)
    (c : ℝ) (hc : ∀ p ∈ V, ∀ x, p x ^ 2 ≤ c * ∑ z, p z ^ 2) :
    1 ≤ c * finrank ℝ V := by
  obtain ⟨k, e, hk, he, ho, hx, hpars⟩ := exists_onb' V
  have hN : (0 : ℝ) < Fintype.card Y := by exact_mod_cast Fintype.card_pos
  have hy : ∀ y, 1 ≤ c * ∑ i, (∑ x, A x y * e i x) ^ 2 := by
    intro y
    set n2 := ∑ z, q y z ^ 2 with hn2
    have hn2pos : 0 < n2 := hne y
    set S := ∑ x, A x y * q y x with hS
    have hSabs : S = ∑ x, |q y x| := by
      apply sum_congr rfl
      intro x _
      have h1 := hsign y x
      rcases hA x y with h | h
      · rw [h, one_mul] at h1 ⊢
        exact (abs_of_nonneg h1).symm
      · rw [h] at h1 ⊢
        rw [abs_of_nonpos (by linarith)]
        ring
    have hcn : 0 ≤ c * n2 := by
      by_contra hneg
      replace hneg := not_le.mp hneg
      have : n2 ≤ ∑ x : X, c * n2 := sum_le_sum fun x _ => hc (q y) (hq y) x
      have h2 : ∑ x : X, c * n2 ≤ 0 := sum_nonpos fun x _ => hneg.le
      linarith
    have hmu : ∀ x, |q y x| ≤ Real.sqrt (c * n2) := fun x =>
      Real.abs_le_sqrt (hc (q y) (hq y) x)
    have h1 : n2 ≤ Real.sqrt (c * n2) * S := by
      rw [hSabs, mul_sum]
      apply sum_le_sum
      intro x _
      rw [← sq_abs, sq]
      exact mul_le_mul_of_nonneg_right (hmu x) (abs_nonneg _)
    have hS0 : 0 ≤ S := by rw [hSabs]; exact sum_nonneg fun x _ => abs_nonneg _
    have h2 : S = ∑ i, (∑ z, e i z * q y z) * (∑ x, A x y * e i x) := by
      rw [hS]
      have : ∀ x, A x y * q y x = ∑ i, (∑ z, e i z * q y z) * (A x y * e i x) := by
        intro x
        rw [hx (q y) (hq y) x, mul_sum]
        apply sum_congr rfl
        intros
        ring
      simp_rw [this]
      rw [sum_comm]
      simp_rw [← mul_sum]
    have h3 : S ^ 2 ≤ n2 * ∑ i, (∑ x, A x y * e i x) ^ 2 := by
      rw [h2, hn2, ← hpars (q y) (hq y)]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h4 : n2 ^ 2 ≤ c * n2 * S ^ 2 := by
      have := mul_self_le_mul_self hn2pos.le h1
      have hsq : Real.sqrt (c * n2) * Real.sqrt (c * n2) = c * n2 := Real.mul_self_sqrt hcn
      calc n2 ^ 2 = n2 * n2 := sq n2
        _ ≤ Real.sqrt (c * n2) * S * (Real.sqrt (c * n2) * S) := this
        _ = (Real.sqrt (c * n2) * Real.sqrt (c * n2)) * S ^ 2 := by ring
        _ = c * n2 * S ^ 2 := by rw [hsq]
    have h5 : n2 ^ 2 * 1 ≤ n2 ^ 2 * (c * ∑ i, (∑ x, A x y * e i x) ^ 2) := by
      calc n2 ^ 2 * 1 ≤ c * n2 * S ^ 2 := by linarith
        _ ≤ c * n2 * (n2 * ∑ i, (∑ x, A x y * e i x) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 hcn
        _ = _ := by ring
    exact le_of_mul_le_mul_left h5 (by positivity)
  have hcol : ∀ i, ∑ y, (∑ x, A x y * e i x) ^ 2 = Fintype.card Y := by
    intro i
    have : ∀ y, (∑ x, A x y * e i x) ^ 2 =
        ∑ x, ∑ x', e i x * e i x' * (A x y * A x' y) := by
      intro y
      rw [sq, sum_mul_sum]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intros
      ring
    simp_rw [this]
    rw [sum_comm]
    have h2 : ∀ x, ∑ y, ∑ x', e i x * e i x' * (A x y * A x' y) =
        e i x * e i x * Fintype.card Y := by
      intro x
      rw [sum_comm]
      simp_rw [← mul_sum, hO]
      simp
    simp_rw [h2]
    rw [← sum_mul, ho i i]
    simp
  have hsum : ∑ _y : Y, (1 : ℝ) ≤ ∑ y, c * ∑ i, (∑ x, A x y * e i x) ^ 2 :=
    sum_le_sum fun y _ => hy y
  rw [← mul_sum, sum_comm] at hsum
  simp_rw [hcol] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fin] at hsum
  rw [← hk]
  have : (Fintype.card Y : ℝ) * 1 ≤ Fintype.card Y * (c * k) := by linarith
  exact le_of_mul_le_mul_left this hN

end Onb

section Weighted

variable {X : Type*} [Fintype X] [DecidableEq X]

def dmap (d : X → ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun p := fun x => d x * p x
  map_add' p q := by funext x; simp [mul_add]
  map_smul' c p := by funext x; simp [mul_left_comm]

omit [Fintype X] [DecidableEq X] in
theorem dmap_apply (d : X → ℝ) (p : X → ℝ) (x : X) : dmap d p x = d x * p x := rfl

noncomputable def rk (W : Submodule ℝ (X → ℝ)) (T : Finset X) : ℕ :=
  finrank ℝ (W.map (dmap (fun x => if x ∈ T then 1 else 0)))

theorem finrank_scaled (W : Submodule ℝ (X → ℝ)) (T : Finset X) (d : X → ℝ)
    (hd : ∀ x ∈ T, d x ≠ 0) :
    finrank ℝ (W.map (dmap (fun x => if x ∈ T then d x else 0))) = rk W T := by
  let d' : X → ℝ := fun x => if x ∈ T then d x else 1
  have hd' : ∀ x, d' x ≠ 0 := by
    intro x
    by_cases hx : x ∈ T
    · simp only [d', hx, ↓reduceIte]; exact hd x hx
    · simp only [d', hx, ↓reduceIte]; exact one_ne_zero
  let E : (X → ℝ) ≃ₗ[ℝ] (X → ℝ) := LinearEquiv.ofLinearMap (dmap d') (dmap (fun x => (d' x)⁻¹))
    (by ext p x; simp [dmap_apply, hd' x]) (by ext p x; simp [dmap_apply, hd' x])
  have hcomp : dmap (fun x => if x ∈ T then d x else 0) =
      (E : (X → ℝ) →ₗ[ℝ] (X → ℝ)) ∘ₗ dmap (fun x => if x ∈ T then 1 else 0) := by
    ext p x
    by_cases hx : x ∈ T <;> simp [E, d', hx, dmap_apply]
  rw [hcomp, Submodule.map_comp]
  exact LinearEquiv.finrank_map_eq E _

theorem rk_mono (W : Submodule ℝ (X → ℝ)) {T' T : Finset X} (h : T' ⊆ T) :
    rk W T' ≤ rk W T := by
  have hcomp : dmap (fun x => if x ∈ T' then (1 : ℝ) else 0) =
      dmap (fun x => if x ∈ T' then (1 : ℝ) else 0) ∘ₗ dmap (fun x => if x ∈ T then 1 else 0) := by
    ext p x
    by_cases hx : x ∈ T'
    · simp [dmap_apply, hx, h hx]
    · simp [dmap_apply, hx]
  unfold rk
  rw [hcomp, Submodule.map_comp]
  exact Submodule.finrank_map_le _ _

theorem rk_le (W : Submodule ℝ (X → ℝ)) (T : Finset X) : rk W T ≤ finrank ℝ W :=
  Submodule.finrank_map_le _ _

theorem sum_scaled_sq (T : Finset X) (w : X → ℝ) (hw : ∀ x ∈ T, 0 < w x) (p : X → ℝ) :
    ∑ z, (dmap (fun x => if x ∈ T then Real.sqrt (w x) else 0) p) z ^ 2 =
      ∑ z ∈ T, w z * p z ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun z => z ∈ T)]
  have h1 : ∑ z ∈ univ.filter (fun z => ¬ z ∈ T),
      (dmap (fun x => if x ∈ T then Real.sqrt (w x) else 0) p) z ^ 2 = 0 := by
    apply sum_eq_zero
    intro z hz
    simp [dmap_apply, (mem_filter.mp hz).2]
  have h2 : univ.filter (fun z => z ∈ T) = T := by ext z; simp
  rw [h1, add_zero, h2]
  apply sum_congr rfl
  intro z hz
  simp only [dmap_apply, hz, ↓reduceIte, mul_pow, Real.sq_sqrt (hw z hz).le]

theorem lev_T (W : Submodule ℝ (X → ℝ)) (T : Finset X) (w : X → ℝ) (hw : ∀ x ∈ T, 0 < w x) :
    ∃ s : X → ℝ, (∀ x, 0 ≤ s x) ∧
      (∀ p ∈ W, ∀ x ∈ T, w x * p x ^ 2 ≤ s x * ∑ z ∈ T, w z * p z ^ 2) ∧
      (∀ x ∈ T, (∃ p ∈ W, p x ≠ 0) →
        ∃ p ∈ W, p x ≠ 0 ∧ w x * p x ^ 2 = s x * ∑ z ∈ T, w z * p z ^ 2) ∧
      ∑ x ∈ T, s x = rk W T := by
  set d : X → ℝ := fun x => if x ∈ T then Real.sqrt (w x) else 0 with hd
  obtain ⟨s, hs0, hsa, hsb, hsc⟩ := lev_exists (W.map (dmap d))
  have hda : ∀ p ∈ W, ∀ x ∈ T, w x * p x ^ 2 ≤ s x * ∑ z ∈ T, w z * p z ^ 2 := by
    intro p hp x hx
    have h := hsa (dmap d p) ⟨p, hp, rfl⟩ x
    rw [sum_scaled_sq T w hw p] at h
    simpa only [dmap_apply, hd, hx, ↓reduceIte, mul_pow, Real.sq_sqrt (hw x hx).le] using h
  refine ⟨s, hs0, hda, ?_, ?_⟩
  · intro x hx ⟨p0, hp0, hp0x⟩
    obtain ⟨q, ⟨p, hp, rfl⟩, hq1, hq2⟩ := hsb x
    have hspos : s x ≠ 0 := by
      intro h0
      have h := hda p0 hp0 x hx
      rw [h0, zero_mul] at h
      have : 0 < w x * p0 x ^ 2 := mul_pos (hw x hx) (by positivity)
      linarith
    have hq1' : Real.sqrt (w x) * p x = s x := by
      simpa only [dmap_apply, hd, hx, ↓reduceIte] using hq1
    refine ⟨p, hp, ?_, ?_⟩
    · intro h0
      rw [h0, mul_zero] at hq1'
      exact hspos hq1'.symm
    · rw [sum_scaled_sq T w hw p] at hq2
      rw [hq2, ← hq1']
      have h := Real.mul_self_sqrt (hw x hx).le
      linear_combination (-(p x) ^ 2) * h
  · have hoff : ∀ x, x ∉ T → s x = 0 := by
      intro x hx
      obtain ⟨q, ⟨p, hp, rfl⟩, hq1, hq2⟩ := hsb x
      simpa only [dmap_apply, hd, hx, ↓reduceIte, zero_mul, eq_comm] using hq1
    have : ∑ x ∈ T, s x = ∑ x, s x := by
      apply sum_subset (subset_univ T)
      intro x _ hx
      exact hoff x hx
    rw [this, hsc]
    norm_cast
    exact finrank_scaled W T (fun x => Real.sqrt (w x))
      (fun x hx => (Real.sqrt_pos.mpr (hw x hx)).ne')

theorem final_T {Y : Type*} [Fintype Y] [Nonempty Y] (A : X → Y → ℝ)
    (hA : ∀ x y, A x y = 1 ∨ A x y = -1)
    (hO : ∀ x x', ∑ y, A x y * A x' y = if x = x' then (Fintype.card Y : ℝ) else 0)
    (W : Submodule ℝ (X → ℝ)) (P : Y → X → ℝ) (hP : ∀ y, P y ∈ W)
    (T : Finset X) (hT : T.Nonempty) (hs : ∀ y, ∀ x ∈ T, 0 < A x y * P y x)
    (w : X → ℝ) (hw : ∀ x ∈ T, 0 < w x) (c : ℝ)
    (hc : ∀ p ∈ W, ∀ x ∈ T, w x * p x ^ 2 ≤ c * ∑ z ∈ T, w z * p z ^ 2) :
    1 ≤ c * rk W T := by
  set d : X → ℝ := fun x => if x ∈ T then Real.sqrt (w x) else 0 with hd
  have hfr := finrank_scaled W T (fun x => Real.sqrt (w x))
      (fun x hx => (Real.sqrt_pos.mpr (hw x hx)).ne')
  rw [← hfr]
  obtain ⟨x0, hx0⟩ := hT
  refine final_ineq A hA hO (W.map (dmap d)) (fun y => dmap d (P y)) (fun y => ⟨P y, hP y, rfl⟩)
    ?_ ?_ c ?_
  · intro y
    rw [sum_scaled_sq T w hw]
    apply sum_pos
    · intro z hz
      have : P y z ≠ 0 := by
        intro h0
        have := hs y z hz
        rw [h0, mul_zero] at this
        exact lt_irrefl _ this
      exact mul_pos (hw z hz) (by positivity)
    · exact ⟨x0, hx0⟩
  · intro y x
    by_cases hx : x ∈ T
    · simp only [dmap_apply, hd, hx, ↓reduceIte]
      have := (hs y x hx).le
      have h2 := Real.sqrt_nonneg (w x)
      calc (0 : ℝ) ≤ Real.sqrt (w x) * (A x y * P y x) := mul_nonneg h2 this
        _ = _ := by ring
    · simp [dmap_apply, hd, hx]
  · rintro q ⟨p, hp, rfl⟩ x
    rw [sum_scaled_sq T w hw]
    by_cases hx : x ∈ T
    · simpa only [dmap_apply, hd, hx, ↓reduceIte, mul_pow, Real.sq_sqrt (hw x hx).le] using hc p hp x hx
    · have h0 := hc p hp x0 hx0
      have : 0 ≤ w x0 * p x0 ^ 2 := mul_nonneg (hw x0 hx0).le (sq_nonneg _)
      simp only [dmap_apply, hd, hx, ↓reduceIte, zero_mul]
      rw [zero_pow two_ne_zero]
      linarith

theorem lift_bound (W : Submodule ℝ (X → ℝ)) (T : Finset X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ W, ∃ p' ∈ W, (∀ x ∈ T, p' x = p x) ∧
      ∑ z, p' z ^ 2 ≤ K * ∑ z ∈ T, p z ^ 2 := by
  let f : W →ₗ[ℝ] (X → ℝ) := (dmap (fun x => if x ∈ T then 1 else 0)).comp W.subtype
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let G : LinearMap.range f →L[ℝ] W := LinearMap.toContinuousLinearMap g
  refine ⟨Fintype.card X * ‖G‖ ^ 2, by positivity, ?_⟩
  intro p hp
  let r : LinearMap.range f := ⟨f ⟨p, hp⟩, LinearMap.mem_range_self _ _⟩
  have hQ : 0 ≤ ∑ z ∈ T, p z ^ 2 := sum_nonneg fun z _ => sq_nonneg _
  refine ⟨(g r : W), (g r).2, ?_, ?_⟩
  · intro x hx
    have h1 : f.rangeRestrict (g r) = r := by
      exact LinearMap.congr_fun hg r
    have h2 : f (g r) = f ⟨p, hp⟩ := congrArg Subtype.val h1
    have h3 := congrFun h2 x
    simpa [f, dmap_apply, hx] using h3
  · have hb : ‖g r‖ ≤ ‖G‖ * ‖r‖ := G.le_opNorm r
    have hr : ‖r‖ ≤ Real.sqrt (∑ z ∈ T, p z ^ 2) := by
      show ‖(f ⟨p, hp⟩ : X → ℝ)‖ ≤ _
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro z
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      by_cases hz : z ∈ T
      · simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, dmap_apply, hz, ↓reduceIte,
          one_mul]
        exact single_le_sum (f := fun z => p z ^ 2) (fun i _ => sq_nonneg _) hz
      · simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, dmap_apply, hz, ↓reduceIte,
          zero_mul]
        rw [zero_pow two_ne_zero]
        exact hQ
    have hgr : ‖g r‖ ^ 2 ≤ ‖G‖ ^ 2 * ∑ z ∈ T, p z ^ 2 := by
      have h1 : ‖g r‖ ≤ ‖G‖ * Real.sqrt (∑ z ∈ T, p z ^ 2) :=
        hb.trans (mul_le_mul_of_nonneg_left hr (by positivity))
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rwa [mul_pow, Real.sq_sqrt hQ] at h2
    have hz : ∀ z, ((g r : W) : X → ℝ) z ^ 2 ≤ ‖G‖ ^ 2 * ∑ z ∈ T, p z ^ 2 := by
      intro z
      have h1 : ‖((g r : W) : X → ℝ) z‖ ≤ ‖((g r : W) : X → ℝ)‖ := norm_le_pi_norm _ z
      have h2 : ‖((g r : W) : X → ℝ)‖ = ‖g r‖ := rfl
      rw [h2, Real.norm_eq_abs] at h1
      calc ((g r : W) : X → ℝ) z ^ 2 = |((g r : W) : X → ℝ) z| ^ 2 := (sq_abs _).symm
        _ ≤ ‖g r‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        _ ≤ _ := hgr
    calc ∑ z, ((g r : W) : X → ℝ) z ^ 2 ≤ ∑ _z : X, ‖G‖ ^ 2 * ∑ z ∈ T, p z ^ 2 :=
          sum_le_sum fun z _ => hz z
      _ = Fintype.card X * ‖G‖ ^ 2 * ∑ z ∈ T, p z ^ 2 := by
          simp only [sum_const, card_univ, nsmul_eq_mul]
          ring

theorem balanced_fp (W : Submodule ℝ (X → ℝ)) (T : Finset X) (hT : T.Nonempty)
    (hne : ∀ x ∈ T, ∃ p ∈ W, p x ≠ 0) (m : ℕ) :
    0 < rk W T ∧ ∃ θ : X → ℝ, (∀ x ∈ T, 0 < θ x) ∧ ∑ x ∈ T, θ x = T.card ∧
      ∀ p ∈ W, ∀ x ∈ T, ((θ x)⁻¹) ^ m * p x ^ 2 ≤
        (rk W T / T.card) * θ x * ∑ z ∈ T, ((θ z)⁻¹) ^ m * p z ^ 2 := by
  have hlev := fun (w : {w : X → ℝ // ∀ x ∈ T, 0 < w x}) => lev_T W T w.1 w.2
  choose S hS0 hSa hSb hSc using hlev
  have hQpos : ∀ (w : {w : X → ℝ // ∀ x ∈ T, 0 < w x}) (p : X → ℝ) (x : X), x ∈ T → p x ≠ 0 →
      0 < w.1 x * p x ^ 2 ∧ w.1 x * p x ^ 2 ≤ ∑ z ∈ T, w.1 z * p z ^ 2 := by
    intro w p x hx hpx
    exact ⟨mul_pos (w.2 x hx) (by positivity),
      single_le_sum (f := fun z => w.1 z * p z ^ 2)
        (fun z hz => mul_nonneg (w.2 z hz).le (sq_nonneg _)) hx⟩
  have hSpos : ∀ w, ∀ x ∈ T, 0 < S w x := by
    intro w x hx
    obtain ⟨p, hp, hpx, heq⟩ := hSb w x hx (hne x hx)
    obtain ⟨h1, h2⟩ := hQpos w p x hx hpx
    rcases (hS0 w x).lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at heq
      linarith
  have hSle : ∀ w, ∀ x ∈ T, S w x ≤ 1 := by
    intro w x hx
    obtain ⟨p, hp, hpx, heq⟩ := hSb w x hx (hne x hx)
    obtain ⟨h1, h2⟩ := hQpos w p x hx hpx
    by_contra hgt
    replace hgt := not_le.mp hgt
    have hQ : 0 < ∑ z ∈ T, w.1 z * p z ^ 2 := lt_of_lt_of_le h1 h2
    have : (∑ z ∈ T, w.1 z * p z ^ 2) < S w x * ∑ z ∈ T, w.1 z * p z ^ 2 := by
      nlinarith
    linarith
  have hrk : (0 : ℝ) < rk W T := by
    let w1 : {w : X → ℝ // ∀ x ∈ T, 0 < w x} := ⟨fun _ => 1, fun _ _ => one_pos⟩
    rw [← hSc w1]
    exact sum_pos (fun x hx => hSpos w1 x hx) hT
  have hmono : ∀ w w' : {w : X → ℝ // ∀ x ∈ T, 0 < w x}, (∀ x ∈ T, w.1 x ≤ w'.1 x) →
      ∀ x ∈ T, w.1 x / S w x ≤ w'.1 x / S w' x := by
    intro w w' hww x hx
    obtain ⟨p, hp, hpx, heq⟩ := hSb w' x hx (hne x hx)
    have h1 := hSa w p hp x hx
    have hQQ : ∑ z ∈ T, w.1 z * p z ^ 2 ≤ ∑ z ∈ T, w'.1 z * p z ^ 2 :=
      sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hww z hz) (sq_nonneg _)
    have h2 : w.1 x * p x ^ 2 ≤ S w x * ∑ z ∈ T, w'.1 z * p z ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left hQQ (hS0 w x))
    rw [div_le_div_iff₀ (hSpos w x hx) (hSpos w' x hx)]
    have hp2 : 0 < p x ^ 2 := by positivity
    apply le_of_mul_le_mul_right _ hp2
    calc w.1 x * S w' x * p x ^ 2 = (w.1 x * p x ^ 2) * S w' x := by ring
      _ ≤ (S w x * ∑ z ∈ T, w'.1 z * p z ^ 2) * S w' x :=
          mul_le_mul_of_nonneg_right h2 (hS0 w' x)
      _ = S w x * (S w' x * ∑ z ∈ T, w'.1 z * p z ^ 2) := by ring
      _ = S w x * (w'.1 x * p x ^ 2) := by rw [heq]
      _ = w'.1 x * S w x * p x ^ 2 := by ring
  have hσ : ∃ σ : ℝ, 0 < σ ∧ ∀ (b : ℝ) (hb : 0 < b), ∀ x ∈ T,
      σ ≤ S ⟨fun _ => b, fun _ _ => hb⟩ x := by
    choose! p0 hp0W hp0x using hne
    let σf : X → ℝ := fun x => p0 x x ^ 2 / ∑ z ∈ T, p0 x z ^ 2
    obtain ⟨x0, hx0, hmin⟩ := T.exists_min_image σf hT
    have hpos : ∀ x ∈ T, 0 < ∑ z ∈ T, p0 x z ^ 2 := fun x hx =>
      lt_of_lt_of_le (by have := hp0x x hx; positivity)
        (single_le_sum (f := fun z => p0 x z ^ 2) (fun z _ => sq_nonneg _) hx)
    refine ⟨σf x0, div_pos (by have := hp0x x0 hx0; positivity) (hpos x0 hx0), ?_⟩
    intro b hb x hx
    refine (hmin x hx).trans ?_
    have h := hSa ⟨fun _ => b, fun _ _ => hb⟩ (p0 x) (hp0W x hx) x hx
    simp only at h
    rw [← mul_sum] at h
    show p0 x x ^ 2 / ∑ z ∈ T, p0 x z ^ 2 ≤ _
    rw [div_le_iff₀ (hpos x hx)]
    have h' : b * p0 x x ^ 2 ≤ b * (S ⟨fun _ => b, fun _ _ => hb⟩ x * ∑ z ∈ T, p0 x z ^ 2) := by
      linarith [h]
    exact le_of_mul_le_mul_left h' hb
  obtain ⟨σ, hσpos, hσ⟩ := hσ
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = rk W T / T.card := ⟨_, rfl⟩
  rw [← hκ]
  have hκpos : 0 < κ := by rw [hκ]; exact div_pos hrk hcard
  have hκcard : κ * (T.card : ℝ) = rk W T := by rw [hκ]; field_simp
  have he : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hσ1 : σ ≤ 1 := by
    obtain ⟨x, hx⟩ := hT
    exact (hσ 1 one_pos x hx).trans (hSle _ x hx)
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = κ / σ := ⟨_, rfl⟩
  have hbσ : κ = b * σ := by rw [hbdef]; field_simp
  have hab : κ ≤ b := by
    rw [hbdef, le_div_iff₀ hσpos]
    nlinarith
  have hbpos : 0 < b := hκpos.trans_le hab
  let Sf : (X → ℝ) → X → ℝ := fun v x =>
    if h : ∀ x ∈ T, 0 < v x ^ m then S ⟨fun x => v x ^ m, h⟩ x else 1
  let Γ : (X → ℝ) → X → ℝ := fun v x => (κ * v x ^ m / Sf v x) ^ (((m + 1 : ℕ) : ℝ)⁻¹)
  have hbox : ∀ v : X → ℝ, (∀ x, κ ≤ v x) → ∀ x ∈ T, 0 < v x ^ m :=
    fun v hv x _ => pow_pos (hκpos.trans_le (hv x)) m
  have hSf : ∀ v (hv : ∀ x, κ ≤ v x), Sf v = S ⟨fun x => v x ^ m, hbox v hv⟩ := by
    intro v hv
    funext x
    simp only [Sf]
    rw [dite_eq_left_of_eq_true (eq_true (hbox v hv))]
  have hΓmono : ∀ v v' : X → ℝ, (∀ x, κ ≤ v x) → (∀ x, v x ≤ v' x) →
      ∀ x ∈ T, Γ v x ≤ Γ v' x := by
    intro v v' hv hvv x hx
    have hv' : ∀ x, κ ≤ v' x := fun x => (hv x).trans (hvv x)
    simp only [Γ]
    rw [hSf v hv, hSf v' hv']
    apply Real.rpow_le_rpow
    · exact div_nonneg (mul_nonneg hκpos.le (pow_nonneg (hκpos.le.trans (hv x)) m)) (hS0 _ x)
    · have := hmono ⟨fun x => v x ^ m, hbox v hv⟩ ⟨fun x => v' x ^ m, hbox v' hv'⟩
        (fun z _ => pow_le_pow_left₀ (hκpos.le.trans (hv z)) (hvv z) m) x hx
      simp only at this
      rw [mul_div_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left this hκpos.le
    · exact he
  have hΓa : ∀ x ∈ T, κ ≤ Γ (fun _ => κ) x := by
    intro x hx
    have hv : ∀ x : X, κ ≤ (fun _ : X => κ) x := fun _ => le_rfl
    simp only [Γ]
    rw [hSf _ hv]
    have h1 : κ ^ (m + 1) ≤
        κ * κ ^ m / S ⟨fun x => (fun _ : X => κ) x ^ m, hbox _ hv⟩ x := by
      rw [le_div_iff₀ (hSpos _ x hx)]
      have := hSle ⟨fun x => (fun _ : X => κ) x ^ m, hbox _ hv⟩ x hx
      have hpw : 0 ≤ κ ^ (m + 1) := pow_nonneg hκpos.le _
      calc κ ^ (m + 1) * S ⟨fun x => (fun _ : X => κ) x ^ m, hbox _ hv⟩ x
          ≤ κ ^ (m + 1) * 1 := mul_le_mul_of_nonneg_left this hpw
        _ = κ * κ ^ m := by rw [pow_succ]; ring
    calc κ = (κ ^ (m + 1)) ^ (((m + 1 : ℕ) : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast hκpos.le (Nat.succ_ne_zero m)).symm
      _ ≤ _ := Real.rpow_le_rpow (pow_nonneg hκpos.le _) h1 he
  have hΓb : ∀ x ∈ T, Γ (fun _ => b) x ≤ b := by
    intro x hx
    have hv : ∀ x : X, κ ≤ (fun _ : X => b) x := fun _ => hab
    simp only [Γ]
    rw [hSf _ hv]
    have hs : σ ≤ S ⟨fun x => (fun _ : X => b) x ^ m, hbox _ hv⟩ x :=
      hσ (b ^ m) (pow_pos hbpos m) x hx
    have h1 : κ * b ^ m / S ⟨fun x => (fun _ : X => b) x ^ m, hbox _ hv⟩ x ≤ b ^ (m + 1) := by
      rw [div_le_iff₀ (hSpos _ x hx)]
      calc κ * b ^ m = b ^ (m + 1) * σ := by rw [hbσ, pow_succ]; ring
        _ ≤ b ^ (m + 1) * S ⟨fun x => (fun _ : X => b) x ^ m, hbox _ hv⟩ x :=
            mul_le_mul_of_nonneg_left hs (pow_nonneg hbpos.le _)
    calc _ ≤ (b ^ (m + 1)) ^ (((m + 1 : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (div_nonneg (mul_nonneg hκpos.le (pow_nonneg hbpos.le _)) (hS0 _ x))
            h1 he
      _ = b := Real.pow_rpow_inv_natCast hbpos.le (Nat.succ_ne_zero m)
  let 𝒜 : Set (X → ℝ) := {v | (∀ x, κ ≤ v x ∧ v x ≤ b) ∧ ∀ x ∈ T, v x ≤ Γ v x}
  have hconst : (fun _ : X => κ) ∈ 𝒜 := ⟨fun _ => ⟨le_rfl, hab⟩, hΓa⟩
  let vs : X → ℝ := fun x => sSup ((fun v : X → ℝ => v x) '' 𝒜)
  have hbdd : ∀ x, BddAbove ((fun v : X → ℝ => v x) '' 𝒜) := fun x =>
    ⟨b, by rintro _ ⟨v, hv, rfl⟩; exact (hv.1 x).2⟩
  have hnen : ∀ x, ((fun v : X → ℝ => v x) '' 𝒜).Nonempty := fun x => ⟨κ, _, hconst, rfl⟩
  have hle : ∀ v ∈ 𝒜, ∀ x, v x ≤ vs x := fun v hv x => le_csSup (hbdd x) ⟨v, hv, rfl⟩
  have hvs1 : ∀ x, κ ≤ vs x := fun x => hle _ hconst x
  have hvs2 : ∀ x, vs x ≤ b := fun x =>
    csSup_le (hnen x) (by rintro _ ⟨v, hv, rfl⟩; exact (hv.1 x).2)
  have hΓbox : ∀ v : X → ℝ, (∀ x, κ ≤ v x ∧ v x ≤ b) → ∀ x ∈ T, κ ≤ Γ v x ∧ Γ v x ≤ b := by
    intro v hv x hx
    exact ⟨(hΓa x hx).trans (hΓmono _ v (fun _ => le_rfl) (fun z => (hv z).1) x hx),
      (hΓmono v _ (fun z => (hv z).1) (fun z => (hv z).2) x hx).trans (hΓb x hx)⟩
  have hpost : ∀ x ∈ T, vs x ≤ Γ vs x := by
    intro x hx
    show sSup ((fun v : X → ℝ => v x) '' 𝒜) ≤ _
    apply csSup_le (hnen x)
    rintro _ ⟨v, hv, rfl⟩
    exact (hv.2 x hx).trans (hΓmono v vs (fun z => (hv.1 z).1) (hle v hv) x hx)
  let v1 : X → ℝ := fun x => if x ∈ T then Γ vs x else vs x
  have hv1T : ∀ x ∈ T, v1 x = Γ vs x := fun x hx => by simp only [v1, hx, ↓reduceIte]
  have hv1ge : ∀ x, vs x ≤ v1 x := by
    intro x
    by_cases hx : x ∈ T
    · rw [hv1T x hx]; exact hpost x hx
    · simp only [v1, hx, ↓reduceIte, le_refl]
  have hv1box : ∀ x, κ ≤ v1 x ∧ v1 x ≤ b := by
    intro x
    by_cases hx : x ∈ T
    · rw [hv1T x hx]; exact hΓbox vs (fun z => ⟨hvs1 z, hvs2 z⟩) x hx
    · simp only [v1, hx, ↓reduceIte]; exact ⟨hvs1 x, hvs2 x⟩
  have hv1A : v1 ∈ 𝒜 := by
    refine ⟨hv1box, ?_⟩
    intro x hx
    rw [hv1T x hx]
    exact hΓmono vs v1 hvs1 hv1ge x hx
  have hfix : ∀ x ∈ T, Γ vs x = vs x := by
    intro x hx
    refine le_antisymm ?_ (hpost x hx)
    rw [← hv1T x hx]
    exact hle v1 hv1A x
  have hSeq : ∀ x ∈ T, S ⟨fun x => vs x ^ m, hbox vs hvs1⟩ x = κ / vs x := by
    intro x hx
    have h := hfix x hx
    simp only [Γ] at h
    rw [hSf vs hvs1] at h
    have hvpos : 0 < vs x := hκpos.trans_le (hvs1 x)
    have hS := hSpos ⟨fun x => vs x ^ m, hbox vs hvs1⟩ x hx
    have hpm : 0 < vs x ^ m := pow_pos hvpos m
    have h2 : ((κ * vs x ^ m / S ⟨fun x => vs x ^ m, hbox vs hvs1⟩ x) ^
        (((m + 1 : ℕ) : ℝ)⁻¹)) ^ (m + 1) = vs x ^ (m + 1) := by rw [h]
    rw [Real.rpow_inv_natCast_pow (div_nonneg (mul_nonneg hκpos.le hpm.le) hS.le)
      (Nat.succ_ne_zero m)] at h2
    rw [div_eq_iff hS.ne'] at h2
    rw [eq_div_iff hvpos.ne']
    apply mul_left_cancel₀ hpm.ne'
    rw [pow_succ] at h2
    linear_combination -h2
  refine ⟨by exact_mod_cast hrk, fun x => (vs x)⁻¹, ?_, ?_, ?_⟩
  · intro x _
    exact inv_pos.mpr (hκpos.trans_le (hvs1 x))
  · have h := hSc ⟨fun x => vs x ^ m, hbox vs hvs1⟩
    rw [sum_congr rfl hSeq] at h
    have hdiv : ∀ x ∈ T, κ / vs x = κ * (vs x)⁻¹ := fun _ _ => div_eq_mul_inv _ _
    rw [sum_congr rfl hdiv, ← mul_sum] at h
    have h2 := hκcard
    apply mul_left_cancel₀ hκpos.ne'
    rw [h, h2]
  · intro p hp x hx
    have h := hSa ⟨fun x => vs x ^ m, hbox vs hvs1⟩ p hp x hx
    rw [hSeq x hx, div_eq_mul_inv] at h
    simp only [inv_inv]
    exact h

theorem signrank_core {Y : Type*} [Fintype Y] [Nonempty Y] (A : X → Y → ℝ)
    (hA : ∀ x y, A x y = 1 ∨ A x y = -1)
    (hO : ∀ x x', ∑ y, A x y * A x' y = if x = x' then (Fintype.card Y : ℝ) else 0)
    (W : Submodule ℝ (X → ℝ)) (P : Y → X → ℝ) (hP : ∀ y, P y ∈ W)
    (hs : ∀ y x, 0 < A x y * P y x) (T : Finset X) : T.card ≤ rk W T ^ 2 := by
  induction T using Finset.strongInduction with
  | H T ih =>
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  have y0 : Y := Classical.arbitrary Y
  have hPne : ∀ y x, P y x ≠ 0 := by
    intro y x h0
    have := hs y x
    rw [h0, mul_zero] at this
    exact lt_irrefl _ this
  have hne : ∀ S : Finset X, ∀ x ∈ S, ∃ p ∈ W, p x ≠ 0 :=
    fun S x _ => ⟨P y0, hP y0, hPne y0 x⟩
  choose Kf hKf0 hKf using fun T' : Finset X => lift_bound W T'
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ∑ T' ∈ T.powerset, Kf T' := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact sum_nonneg fun T' _ => hKf0 T'
  have hKle : ∀ T', T' ⊆ T → Kf T' ≤ K := by
    intro T' h
    rw [hKdef]
    exact single_le_sum (f := Kf) (fun i _ => hKf0 i) (mem_powerset.mpr h)
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = T.card := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = rk W T := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hT.card_pos
  have hk1 : 1 ≤ k := by rw [hk]; exact_mod_cast (balanced_fp W T hT (hne T) 0).1
  have hnpos : 0 < n := by linarith
  have hkpos : 0 < k := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (2 * n * k ^ 2) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηeq : η * (2 * n * k ^ 2) = 1 := by rw [hη]; field_simp
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (1 + n * η) / (1 + n * η + η) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by positivity)]; linarith
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = η / (2 * n) := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hμη : μ * (2 * n) = η := by rw [hμ]; field_simp
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hμpos (by linarith : (0 : ℝ) < K + 1)) hρ1
  have hKρ : K * ρ ^ m ≤ μ := by
    have h1 : ρ ^ m * (K + 1) < μ := (lt_div_iff₀ (by linarith)).mp hm
    have h2 : 0 ≤ ρ ^ m := pow_nonneg hρ0 m
    nlinarith
  obtain ⟨-, θ, hθpos, hθsum, hθ⟩ := balanced_fp W T hT (hne T) m
  rw [← hn, ← hk] at hθ
  rw [← hn] at hθsum
  obtain ⟨xmin, hxmin, hmin⟩ := T.exists_min_image θ hT
  have hθmin1 : θ xmin ≤ 1 := by
    have h1 : ∑ _x ∈ T, θ xmin ≤ ∑ x ∈ T, θ x := sum_le_sum fun x hx => hmin x hx
    rw [sum_const, nsmul_eq_mul, hθsum, ← hn] at h1
    have : n * θ xmin ≤ n * 1 := by linarith
    exact le_of_mul_le_mul_left this hnpos
  have hwpos : ∀ x ∈ T, 0 < ((θ x)⁻¹) ^ m := fun x hx => pow_pos (inv_pos.mpr (hθpos x hx)) m
  have hQ0 : ∀ (S : Finset X) (p : X → ℝ), S ⊆ T → 0 ≤ ∑ z ∈ S, ((θ z)⁻¹) ^ m * p z ^ 2 :=
    fun S p hS => sum_nonneg fun z hz => mul_nonneg (hwpos z (hS hz)).le (sq_nonneg _)
  have hfinish : n ≤ k ^ 2 + 1 / 2 → T.card ≤ rk W T ^ 2 := by
    intro h
    by_contra hcon
    have h2 : rk W T ^ 2 + 1 ≤ T.card := by omega
    have h3 : k ^ 2 + 1 ≤ n := by rw [hn, hk]; exact_mod_cast h2
    linarith
  by_cases hcase : ∀ x ∈ T, θ x < θ xmin + n * η
  · apply hfinish
    have hfin := final_T A hA hO W P hP T hT (fun y x _ => hs y x) (fun x => ((θ x)⁻¹) ^ m) hwpos
      (k / n * (1 + n * η)) (by
        intro p hp x hx
        refine (hθ p hp x hx).trans ?_
        apply mul_le_mul_of_nonneg_right _ (hQ0 T p subset_rfl)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hcase x hx
        linarith)
    rw [← hk] at hfin
    have h1 : n ≤ k ^ 2 * (1 + n * η) := by
      have : n * 1 ≤ n * (k / n * (1 + n * η) * k) := mul_le_mul_of_nonneg_left hfin hnpos.le
      calc n = n * 1 := (mul_one n).symm
        _ ≤ n * (k / n * (1 + n * η) * k) := this
        _ = k ^ 2 * (1 + n * η) := by field_simp
    have h2 : k ^ 2 * (n * η) = 1 / 2 := by linear_combination (1 / 2) * hηeq
    linarith
  · simp only [not_forall, not_lt] at hcase
    obtain ⟨xmax, hxmax, hmax⟩ := hcase
    let Tj : ℕ → Finset X := fun j => T.filter (fun x => θ x < θ xmin + j * η)
    have hTjmem : ∀ j x, x ∈ Tj j ↔ x ∈ T ∧ θ x < θ xmin + j * η := fun j x => mem_filter
    have hTjmono : ∀ j, Tj j ⊆ Tj (j + 1) := by
      intro j x hx
      rw [hTjmem] at hx ⊢
      refine ⟨hx.1, hx.2.trans_le ?_⟩
      push_cast
      linarith
    have hgap : ∃ j : ℕ, 1 ≤ j ∧ j < T.card ∧ Tj j = Tj (j + 1) := by
      by_contra hno
      have hno' : ∀ j : ℕ, 1 ≤ j → j < T.card → Tj j ≠ Tj (j + 1) :=
        fun j h1 h2 h3 => hno ⟨j, h1, h2, h3⟩
      have hcardj : ∀ j : ℕ, 1 ≤ j → j ≤ T.card → j ≤ (Tj j).card := by
        intro j hj
        induction j, hj using Nat.le_induction with
        | base =>
          intro _
          apply Finset.card_pos.mpr
          refine ⟨xmin, (hTjmem 1 xmin).mpr ⟨hxmin, ?_⟩⟩
          push_cast
          linarith
        | succ j hj ihj =>
          intro hle
          have h1 := ihj (by omega)
          have h2 : (Tj j).card < (Tj (j + 1)).card :=
            Finset.card_lt_card ((hTjmono j).ssubset_of_ne (hno' j hj (by omega)))
          omega
      have h1 := hcardj T.card hT.card_pos le_rfl
      have h2 : Tj T.card ⊆ T.erase xmax := by
        intro x hx
        rw [hTjmem] at hx
        rw [mem_erase]
        refine ⟨?_, hx.1⟩
        rintro rfl
        rw [← hn] at hx
        linarith [hx.2]
      have h3 := Finset.card_le_card h2
      rw [Finset.card_erase_of_mem hxmax] at h3
      have := hT.card_pos
      omega
    obtain ⟨j, hj1, hjn, hjeq⟩ := hgap
    have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
    have hjn' : (j : ℝ) + 1 ≤ n := by rw [hn]; exact_mod_cast hjn
    have hjη : (j : ℝ) * η ≤ n * η := mul_le_mul_of_nonneg_right (by linarith) hηpos.le
    have hjη1 : η ≤ (j : ℝ) * η := by
      have := mul_le_mul_of_nonneg_right hj1' hηpos.le
      linarith
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = θ xmin + j * η := ⟨_, rfl⟩
    obtain ⟨T', hT'⟩ : ∃ T' : Finset X, T' = Tj j := ⟨_, rfl⟩
    have hT'sub : T' ⊆ T := by rw [hT']; exact filter_subset _ _
    have hin : ∀ x ∈ T', θ x < a := by
      intro x hx
      rw [hT', hTjmem] at hx
      rw [ha]
      exact hx.2
    have hout : ∀ x ∈ T, x ∉ T' → a + η ≤ θ x := by
      intro x hx hx'
      rw [hT', hjeq, hTjmem] at hx'
      have h1 : ¬ θ x < θ xmin + ((j + 1 : ℕ) : ℝ) * η := fun h => hx' ⟨hx, h⟩
      push_cast at h1
      rw [ha]
      linarith [not_lt.mp h1]
    have hxminT' : xmin ∈ T' := by
      rw [hT', hTjmem]
      exact ⟨hxmin, by linarith⟩
    have hxmaxT' : xmax ∉ T' := fun h => by
      have := hin xmax h
      rw [ha] at this
      linarith
    have hss : T' ⊂ T := hT'sub.ssubset_of_ne (fun h => hxmaxT' (h ▸ hxmax))
    have hapos : 0 < a := by
      have := hθpos xmin hxmin
      rw [ha]
      linarith
    have ha1 : a ≤ 1 + n * η := by rw [ha]; linarith
    have hih := ih T' hss
    obtain ⟨n', hn'⟩ : ∃ n' : ℝ, n' = T'.card := ⟨_, rfl⟩
    obtain ⟨j', hj'⟩ : ∃ j' : ℝ, j' = rk W T' := ⟨_, rfl⟩
    have hn'1 : 1 ≤ n' := by
      rw [hn']
      exact_mod_cast Finset.card_pos.mpr ⟨xmin, hxminT'⟩
    have hn'n : n' + 1 ≤ n := by
      rw [hn', hn]
      exact_mod_cast Finset.card_lt_card hss
    have hih' : n' ≤ j' ^ 2 := by rw [hn', hj']; exact_mod_cast hih
    have hj'k : j' ≤ k := by rw [hj', hk]; exact_mod_cast rk_mono W hT'sub
    have hj'0 : 0 ≤ j' := by rw [hj']; exact Nat.cast_nonneg _
    have hj'pos : 0 < j' := by
      rcases hj'0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hih'
        norm_num at hih'
        linarith
    have hwin : ∀ x ∈ T', (a⁻¹) ^ m ≤ ((θ x)⁻¹) ^ m := fun x hx =>
      pow_le_pow_left₀ (inv_nonneg.mpr hapos.le)
        (inv_anti₀ (hθpos x (hT'sub hx)) (hin x hx).le) m
    have hwout : ∀ x ∈ T \ T', ((θ x)⁻¹) ^ m ≤ ((a + η)⁻¹) ^ m := by
      intro x hx
      rw [mem_sdiff] at hx
      exact pow_le_pow_left₀ (inv_nonneg.mpr (hθpos x hx.1).le)
        (inv_anti₀ (by linarith) (hout x hx.1 hx.2)) m
    have hratio : ((a + η)⁻¹) ^ m * a ^ m ≤ ρ ^ m := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [hρ, inv_mul_eq_div, div_le_div_iff₀ (by linarith) (by positivity)]
      nlinarith
    have hdom : ∀ p ∈ W, ∀ x ∈ T', ((θ x)⁻¹) ^ m * p x ^ 2 ≤
        k / n * θ x * (1 + K * ρ ^ m) * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 := by
      intro p hp x hx
      obtain ⟨p', hp', hpeq, hpb⟩ := hKf T' p hp
      have h1 := hθ p' hp' x (hT'sub hx)
      rw [hpeq x hx] at h1
      have hsplit : ∑ z ∈ T, ((θ z)⁻¹) ^ m * p' z ^ 2 =
          ∑ z ∈ T \ T', ((θ z)⁻¹) ^ m * p' z ^ 2 + ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 := by
        rw [← sum_sdiff hT'sub]
        congr 1
        exact sum_congr rfl fun z hz => by rw [hpeq z hz]
      have hQ' := hQ0 T' p hT'sub
      have hamp : 0 < a ^ m := pow_pos hapos m
      have hP2 : ∑ z ∈ T', p z ^ 2 ≤ a ^ m * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 := by
        rw [mul_sum]
        apply sum_le_sum
        intro z hz
        have := hwin z hz
        calc p z ^ 2 = a ^ m * ((a⁻¹) ^ m * p z ^ 2) := by
              rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hapos.ne', one_pow, one_mul]
          _ ≤ a ^ m * (((θ z)⁻¹) ^ m * p z ^ 2) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this (sq_nonneg _)) hamp.le
      have hc0 : 0 ≤ ((a + η)⁻¹) ^ m := pow_nonneg (inv_nonneg.mpr (by linarith)) m
      have hout2 : ∑ z ∈ T \ T', ((θ z)⁻¹) ^ m * p' z ^ 2 ≤
          K * ρ ^ m * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 := by
        calc ∑ z ∈ T \ T', ((θ z)⁻¹) ^ m * p' z ^ 2
            ≤ ∑ z ∈ T \ T', ((a + η)⁻¹) ^ m * p' z ^ 2 :=
              sum_le_sum fun z hz => mul_le_mul_of_nonneg_right (hwout z hz) (sq_nonneg _)
          _ = ((a + η)⁻¹) ^ m * ∑ z ∈ T \ T', p' z ^ 2 := by rw [mul_sum]
          _ ≤ ((a + η)⁻¹) ^ m * ∑ z, p' z ^ 2 :=
              mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg (subset_univ _)
                fun _ _ _ => sq_nonneg _) hc0
          _ ≤ ((a + η)⁻¹) ^ m * (K * ∑ z ∈ T', p z ^ 2) :=
              mul_le_mul_of_nonneg_left (hpb.trans (mul_le_mul_of_nonneg_right (hKle T' hT'sub)
                (sum_nonneg fun _ _ => sq_nonneg _))) hc0
          _ ≤ ((a + η)⁻¹) ^ m * (K * (a ^ m * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP2 hK0) hc0
          _ = K * (((a + η)⁻¹) ^ m * a ^ m) * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 := by ring
          _ ≤ K * ρ ^ m * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hK0) hQ'
      rw [hsplit] at h1
      have hcoef : 0 ≤ k / n * θ x := mul_nonneg (by positivity) (hθpos x (hT'sub hx)).le
      calc ((θ x)⁻¹) ^ m * p x ^ 2
          ≤ k / n * θ x * (∑ z ∈ T \ T', ((θ z)⁻¹) ^ m * p' z ^ 2 +
              ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2) := h1
        _ ≤ k / n * θ x * (K * ρ ^ m * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 +
              ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hcoef
        _ = _ := by ring
    obtain ⟨s, hs0, -, hsb, hsc⟩ := lev_T W T' (fun x => ((θ x)⁻¹) ^ m)
      (fun x hx => hwpos x (hT'sub hx))
    have hsle : ∀ x ∈ T', s x ≤ k / n * θ x * (1 + K * ρ ^ m) := by
      intro x hx
      obtain ⟨p, hp, hpx, heq⟩ := hsb x hx (hne T' x hx)
      have hd := hdom p hp x hx
      rw [heq] at hd
      have hQpos : 0 < ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 :=
        lt_of_lt_of_le (mul_pos (hwpos x (hT'sub hx)) (by positivity))
          (single_le_sum (f := fun z => ((θ z)⁻¹) ^ m * p z ^ 2)
            (fun z hz => mul_nonneg (hwpos z (hT'sub hz)).le (sq_nonneg _)) hx)
      exact le_of_mul_le_mul_right hd hQpos
    have hrk' : j' ≤ k / n * (1 + K * ρ ^ m) * ∑ x ∈ T', θ x := by
      rw [hj', ← hsc, mul_sum]
      exact sum_le_sum fun x hx => (hsle x hx).trans_eq (by ring)
    have hsumsplit : ∑ x ∈ T \ T', θ x + ∑ x ∈ T', θ x = n := by
      rw [sum_sdiff hT'sub, hθsum]
    have hcardsplit : ((T \ T').card : ℝ) + n' = n := by
      rw [hn', hn]
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hT'sub
    have hmargin : ∑ x ∈ T', θ x ≤ n' * (1 - μ) := by
      have hμ1 : n' * μ ≤ η / 2 := by
        have : n' * μ ≤ n * μ := mul_le_mul_of_nonneg_right (by linarith) hμpos.le
        linarith
      by_cases hcs : a + η / 2 ≤ 1
      · have h1 : ∑ x ∈ T', θ x ≤ ∑ _x ∈ T', a := sum_le_sum fun x hx => (hin x hx).le
        rw [sum_const, nsmul_eq_mul, ← hn'] at h1
        have h2 : n' * a ≤ n' * (1 - η / 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have h3 : η / 2 ≤ n' * (η / 2) := by
          have := mul_le_mul_of_nonneg_right hn'1 (by linarith : (0 : ℝ) ≤ η / 2)
          linarith
        linarith
      · replace hcs := not_le.mp hcs
        have h1 : ∑ _x ∈ T \ T', (a + η) ≤ ∑ x ∈ T \ T', θ x :=
          sum_le_sum fun x hx => hout x (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2
        rw [sum_const, nsmul_eq_mul] at h1
        have hc1 : (1 : ℝ) ≤ ((T \ T').card : ℝ) := by linarith
        have h2 : ((T \ T').card : ℝ) * (1 + η / 2) ≤ ((T \ T').card : ℝ) * (a + η) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        have h3 : η / 2 ≤ ((T \ T').card : ℝ) * (η / 2) := by
          have := mul_le_mul_of_nonneg_right hc1 (by linarith : (0 : ℝ) ≤ η / 2)
          linarith
        linarith
    have hkey : j' * n ≤ k * n' := by
      have h1 : j' ≤ k / n * (1 + μ) * (n' * (1 - μ)) :=
        hrk'.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hmargin
          (sum_nonneg fun x hx => (hθpos x (hT'sub hx)).le) (by positivity))
      have h2 : k / n * (1 + μ) * (n' * (1 - μ)) ≤ k / n * n' := by
        have hc : 0 ≤ k / n * n' := by positivity
        have : k / n * (1 + μ) * (n' * (1 - μ)) = k / n * n' - k / n * n' * μ ^ 2 := by ring
        rw [this]
        have : 0 ≤ k / n * n' * μ ^ 2 := by positivity
        linarith
      have h3 : j' * n ≤ k / n * n' * n := mul_le_mul_of_nonneg_right (h1.trans h2) hnpos.le
      calc j' * n ≤ k / n * n' * n := h3
        _ = k * n' := by field_simp
    apply hfinish
    have h1 : j' * n ≤ j' * (k * j') := by
      have : k * n' ≤ k * j' ^ 2 := mul_le_mul_of_nonneg_left hih' hkpos.le
      calc j' * n ≤ k * n' := hkey
        _ ≤ k * j' ^ 2 := this
        _ = j' * (k * j') := by ring
    have h2 : n ≤ k * j' := le_of_mul_le_mul_left h1 hj'pos
    have h3 : k * j' ≤ k * k := mul_le_mul_of_nonneg_left hj'k hkpos.le
    have h4 : k * k = k ^ 2 := by ring
    linarith

end Weighted


private theorem main_aux : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
    (∀ i j, H i j = 1 ∨ H i j = -1) →
    (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
    ∀ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 < H i j * A i j) → n ≤ A.rank^2 := by
  intro n H hn hH_pm hH_orth A hsign
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let W : Submodule ℝ (Fin n → ℝ) := LinearMap.range A.mulVecLin
  let P : Fin n → Fin n → ℝ := fun j i => A i j
  have hO : ∀ x x' : Fin n, ∑ y : Fin n, H x y * H x' y =
      if x = x' then (Fintype.card (Fin n) : ℝ) else 0 := by
    intro x x'
    simpa [Fintype.card_fin] using hH_orth x x'
  have hP : ∀ j : Fin n, P j ∈ W := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [P, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hs : ∀ j i : Fin n, 0 < H i j * P j i := fun j i => hsign i j
  have hcore := signrank_core H hH_pm hO W P hP hs Finset.univ
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [hcard] at hcore
  have hfr : finrank ℝ W = A.rank := rfl
  calc n ≤ rk W Finset.univ ^ 2 := hcore
    _ ≤ (finrank ℝ W) ^ 2 := Nat.pow_le_pow_left (rk_le W _) 2
    _ = A.rank ^ 2 := by rw [hfr]

end PEqualNP.Outside.L_lib_562_aux

theorem PEqualNP.Outside.L_lib_562 : (∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 < H i j * A i j) → n ≤ A.rank^2) :=
  PEqualNP.Outside.L_lib_562_aux.main_aux
