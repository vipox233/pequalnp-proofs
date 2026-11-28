import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1264_aux

open Finset Module

def ipSign (m : ℕ) (x y : Fin m → Bool) : ℤ :=
  (-1) ^ (univ.filter (fun i : Fin m => x i = true ∧ y i = true)).card

theorem ipSign_eq_prod (m : ℕ) (x y : Fin m → Bool) :
    ipSign m x y = ∏ i : Fin m, (if x i = true ∧ y i = true then (-1 : ℤ) else 1) := by
  unfold ipSign
  rw [Finset.prod_ite]
  simp

theorem ipSign_comm (m : ℕ) (x y : Fin m → Bool) : ipSign m x y = ipSign m y x := by
  unfold ipSign
  congr 2
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact and_comm

theorem ipSign_eq_ite (m : ℕ) (x y : Fin m → Bool) :
    ipSign m x y =
      if (univ.filter (fun i : Fin m => x i = true ∧ y i = true)).card % 2 = 1 then -1 else 1 := by
  unfold ipSign
  split_ifs with h
  · exact Odd.neg_one_pow (Nat.odd_iff.mpr h)
  · exact Even.neg_one_pow (Nat.even_iff.mpr (by omega))

theorem ipSign_orth (m : ℕ) (y y' : Fin m → Bool) :
    ∑ x : Fin m → Bool, ipSign m x y * ipSign m x y' = if y = y' then (2 : ℤ) ^ m else 0 := by
  have h1 : ∀ x : Fin m → Bool, ipSign m x y * ipSign m x y' =
      ∏ i : Fin m, ((if x i = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if x i = true ∧ y' i = true then (-1 : ℤ) else 1)) := by
    intro x
    rw [ipSign_eq_prod, ipSign_eq_prod, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin m => (univ : Finset Bool))
    (fun (i : Fin m) (b : Bool) => (if b = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if b = true ∧ y' i = true then (-1 : ℤ) else 1))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∀ i : Fin m, (∑ b : Bool, (if b = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if b = true ∧ y' i = true then (-1 : ℤ) else 1)) = if y i = y' i then 2 else 0 := by
    intro i
    cases y i <;> cases y' i <;> simp
  simp_rw [h3]
  rw [Finset.prod_ite_zero]
  by_cases h : y = y'
  · subst h; simp
  · have : ¬ ∀ i ∈ (univ : Finset (Fin m)), y i = y' i :=
      fun hh => h (funext fun i => hh i (mem_univ i))
    rw [if_neg this, if_neg h]

lemma ipSign_orth_real (m : ℕ) (x x' : Fin m → Bool) :
    ∑ y : Fin m → Bool, (-(ipSign m x y : ℝ)) * (-(ipSign m x' y : ℝ)) =
      if x = x' then (2 : ℝ) ^ m else 0 := by
  have h1 := ipSign_orth m x x'
  have h2 : ∑ y : Fin m → Bool, (-(ipSign m x y : ℝ)) * (-(ipSign m x' y : ℝ)) =
      ((∑ y : Fin m → Bool, ipSign m y x * ipSign m y x' : ℤ) : ℝ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro y _
    rw [ipSign_comm m x y, ipSign_comm m x' y]
    ring
  rw [h2, h1]
  split_ifs <;> simp

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

theorem final_ineq_sub {Y : Type*} [Fintype Y] [Nonempty Y] [DecidableEq X] (H : X → Y → ℝ)
    (hH : ∀ x y, H x y = 1 ∨ H x y = -1)
    (N : ℝ) (hOp : ∀ e : X → ℝ, ∑ y : Y, (∑ x : X, H x y * e x) ^ 2 ≤ N * ∑ x : X, e x ^ 2)
    (V : Submodule ℝ (X → ℝ)) (q : Y → X → ℝ) (hq : ∀ y, q y ∈ V)
    (hne : ∀ y, 0 < ∑ z, q y z ^ 2)
    (k : ℕ) (herr : ∀ y, (Finset.univ.filter (fun x => H x y * q y x < 0)).card ≤ k)
    (c : ℝ) (hc : ∀ p ∈ V, ∀ x, p x ^ 2 ≤ c * ∑ z, p z ^ 2)
    (h12kc : 2 * (k : ℝ) * c ≤ 1) :
    (Fintype.card Y : ℝ) * (1 - 2 * (k : ℝ) * c) ^ 2 ≤ c * (N * finrank ℝ V) := by
  classical
  obtain ⟨r, e, hr, he, ho, hx, hpars⟩ := exists_onb' V
  have hc0 : 0 ≤ c := by
    have y0 : Y := Classical.arbitrary Y
    have hn2pos : 0 < ∑ z, q y0 z ^ 2 := hne y0
    by_contra hneg
    replace hneg := not_le.mp hneg
    have h1 : ∑ z, q y0 z ^ 2 ≤ ∑ _x : X, c * ∑ z, q y0 z ^ 2 :=
      sum_le_sum fun x _ => hc (q y0) (hq y0) x
    have h2 : ∑ _x : X, c * ∑ z, q y0 z ^ 2 ≤ 0 :=
      sum_nonpos fun _ _ => mul_nonpos_of_nonpos_of_nonneg hneg.le hn2pos.le
    linarith
  have hy : ∀ y, (1 - 2 * (k : ℝ) * c) ^ 2 ≤ c * ∑ i, (∑ x, H x y * e i x) ^ 2 := by
    intro y
    set n2 := ∑ z, q y z ^ 2 with hn2
    have hn2pos : 0 < n2 := hne y
    set S := ∑ x, H x y * q y x with hS
    set B := Finset.univ.filter (fun x => H x y * q y x < 0) with hBdef
    have hBcard : B.card ≤ k := by
      have htmp := herr y
      convert htmp using 2
    have hSsplit : S = (∑ x, |q y x|) - 2 * ∑ x ∈ B, |q y x| := by
      have hterm : ∀ x : X, H x y * q y x = |q y x| - (if x ∈ B then 2 * |q y x| else 0) := by
        intro x
        by_cases hxb : x ∈ B
        · have hlt : H x y * q y x < 0 := (Finset.mem_filter.mp hxb).2
          rw [if_pos hxb]
          rcases hH x y with h | h
          · rw [h, one_mul] at hlt ⊢
            rw [abs_of_neg hlt]
            ring
          · rw [h] at hlt ⊢
            rw [abs_of_pos (by linarith)]
            ring
        · have hge : 0 ≤ H x y * q y x := by
            by_contra hlt
            push_neg at hlt
            exact hxb (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hlt⟩)
          rw [if_neg hxb, sub_zero]
          rcases hH x y with h | h
          · rw [h, one_mul] at hge ⊢
            exact (abs_of_nonneg hge).symm
          · rw [h] at hge ⊢
            rw [abs_of_nonpos (by linarith)]
            ring
      rw [hS]
      simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
    have hcn : 0 ≤ c * n2 := mul_nonneg hc0 hn2pos.le
    have hmu : ∀ x, |q y x| ≤ Real.sqrt (c * n2) := fun x =>
      Real.abs_le_sqrt (hc (q y) (hq y) x)
    have h1 : n2 ≤ Real.sqrt (c * n2) * ∑ x, |q y x| := by
      rw [mul_sum]
      apply sum_le_sum
      intro x _
      rw [← sq_abs, sq]
      exact mul_le_mul_of_nonneg_right (hmu x) (abs_nonneg _)
    have hBsum : ∑ x ∈ B, |q y x| ≤ (k : ℝ) * Real.sqrt (c * n2) := by
      calc ∑ x ∈ B, |q y x| ≤ ∑ _x ∈ B, Real.sqrt (c * n2) := sum_le_sum fun x _ => hmu x
        _ = (B.card : ℝ) * Real.sqrt (c * n2) := by simp
        _ ≤ (k : ℝ) * Real.sqrt (c * n2) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hBcard) (Real.sqrt_nonneg _)
    have hB2 : 2 * Real.sqrt (c * n2) * ∑ x ∈ B, |q y x| ≤ 2 * (k : ℝ) * c * n2 := by
      have hsq : Real.sqrt (c * n2) * Real.sqrt (c * n2) = c * n2 := Real.mul_self_sqrt hcn
      calc 2 * Real.sqrt (c * n2) * ∑ x ∈ B, |q y x|
          ≤ 2 * Real.sqrt (c * n2) * ((k : ℝ) * Real.sqrt (c * n2)) :=
            mul_le_mul_of_nonneg_left hBsum (by positivity)
        _ = 2 * (k : ℝ) * (Real.sqrt (c * n2) * Real.sqrt (c * n2)) := by ring
        _ = 2 * (k : ℝ) * c * n2 := by rw [hsq]; ring
    have h1' : (1 - 2 * (k : ℝ) * c) * n2 ≤ Real.sqrt (c * n2) * S := by
      rw [hSsplit, mul_sub]
      linarith
    have h2 : S = ∑ i, (∑ z, e i z * q y z) * (∑ x, H x y * e i x) := by
      rw [hS]
      have : ∀ x, H x y * q y x = ∑ i, (∑ z, e i z * q y z) * (H x y * e i x) := by
        intro x
        rw [hx (q y) (hq y) x, mul_sum]
        apply sum_congr rfl
        intros
        ring
      simp_rw [this]
      rw [sum_comm]
      simp_rw [← mul_sum]
    have h3 : S ^ 2 ≤ n2 * ∑ i, (∑ x, H x y * e i x) ^ 2 := by
      rw [h2, hn2, ← hpars (q y) (hq y)]
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h4 : (1 - 2 * (k : ℝ) * c) ^ 2 * n2 ^ 2 ≤ c * n2 * S ^ 2 := by
      have hnn : 0 ≤ (1 - 2 * (k : ℝ) * c) * n2 := mul_nonneg (by linarith) hn2pos.le
      have hms := mul_self_le_mul_self hnn h1'
      have hsq : Real.sqrt (c * n2) * Real.sqrt (c * n2) = c * n2 := Real.mul_self_sqrt hcn
      calc (1 - 2 * (k : ℝ) * c) ^ 2 * n2 ^ 2
          = ((1 - 2 * (k : ℝ) * c) * n2) * ((1 - 2 * (k : ℝ) * c) * n2) := by ring
        _ ≤ Real.sqrt (c * n2) * S * (Real.sqrt (c * n2) * S) := hms
        _ = (Real.sqrt (c * n2) * Real.sqrt (c * n2)) * S ^ 2 := by ring
        _ = c * n2 * S ^ 2 := by rw [hsq]
    have h5 : n2 ^ 2 * (1 - 2 * (k : ℝ) * c) ^ 2 ≤ n2 ^ 2 * (c * ∑ i, (∑ x, H x y * e i x) ^ 2) := by
      calc n2 ^ 2 * (1 - 2 * (k : ℝ) * c) ^ 2 ≤ c * n2 * S ^ 2 := by linarith
        _ ≤ c * n2 * (n2 * ∑ i, (∑ x, H x y * e i x) ^ 2) :=
            mul_le_mul_of_nonneg_left h3 hcn
        _ = _ := by ring
    exact le_of_mul_le_mul_left h5 (by positivity)
  have hcol : ∀ i, ∑ y : Y, (∑ x, H x y * e i x) ^ 2 ≤ N := by
    intro i
    have h1 := hOp (e i)
    have h2 : ∑ x, e i x ^ 2 = 1 := by
      have := ho i i
      simp only [ite_true] at this
      rw [← this]
      apply sum_congr rfl
      intros
      ring
    rw [h2, mul_one] at h1
    exact h1
  have hsum : ∑ _y : Y, (1 - 2 * (k : ℝ) * c) ^ 2 ≤ ∑ y : Y, c * ∑ i, (∑ x, H x y * e i x) ^ 2 :=
    sum_le_sum fun y _ => hy y
  rw [← mul_sum, sum_comm] at hsum
  have hbound : ∑ i : Fin r, ∑ y : Y, (∑ x, H x y * e i x) ^ 2 ≤ ∑ _i : Fin r, N :=
    sum_le_sum fun i _ => hcol i
  have hsum2 : (Fintype.card Y : ℝ) * (1 - 2 * (k : ℝ) * c) ^ 2 ≤ c * ((r : ℝ) * N) := by
    calc (Fintype.card Y : ℝ) * (1 - 2 * (k : ℝ) * c) ^ 2
        = ∑ _y : Y, (1 - 2 * (k : ℝ) * c) ^ 2 := by simp
      _ ≤ c * ∑ i : Fin r, ∑ y : Y, (∑ x, H x y * e i x) ^ 2 := hsum
      _ ≤ c * ∑ _i : Fin r, N := mul_le_mul_of_nonneg_left hbound hc0
      _ = c * ((r : ℝ) * N) := by simp
  rw [← hr]
  linarith

end Onb

section Weighted

variable {X : Type*} [Fintype X] [DecidableEq X]

def dmap {X : Type*} (d : X → ℝ) : (X → ℝ) →ₗ[ℝ] (X → ℝ) where
  toFun p := fun x => d x * p x
  map_add' p q := by funext x; simp [mul_add]
  map_smul' c p := by funext x; simp [mul_left_comm]

@[simp] theorem dmap_apply {X : Type*} (d : X → ℝ) (p : X → ℝ) (x : X) :
    dmap d p x = d x * p x := rfl

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
    (by ext p x; simp [hd' x]) (by ext p x; simp [hd' x])
  have hcomp : dmap (fun x => if x ∈ T then d x else 0) =
      (E : (X → ℝ) →ₗ[ℝ] (X → ℝ)) ∘ₗ dmap (fun x => if x ∈ T then 1 else 0) := by
    ext p x
    by_cases hx : x ∈ T <;> simp [E, d', hx]
  rw [hcomp, Submodule.map_comp]
  exact LinearEquiv.finrank_map_eq E _

theorem rk_mono (W : Submodule ℝ (X → ℝ)) {T' T : Finset X} (h : T' ⊆ T) :
    rk W T' ≤ rk W T := by
  have hcomp : dmap (fun x => if x ∈ T' then (1 : ℝ) else 0) =
      dmap (fun x => if x ∈ T' then (1 : ℝ) else 0) ∘ₗ dmap (fun x => if x ∈ T then 1 else 0) := by
    ext p x
    by_cases hx : x ∈ T'
    · simp [hx, h hx]
    · simp [hx]
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
    simp [(mem_filter.mp hz).2]
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

theorem final_T_sub {Y : Type*} [Fintype Y] [Nonempty Y] (H : X → Y → ℝ)
    (hH : ∀ x y, H x y = 1 ∨ H x y = -1)
    (N : ℝ) (hOp : ∀ e : X → ℝ, ∑ y : Y, (∑ x : X, H x y * e x) ^ 2 ≤ N * ∑ x : X, e x ^ 2)
    (W : Submodule ℝ (X → ℝ)) (P : Y → X → ℝ) (hP : ∀ y, P y ∈ W)
    (T : Finset X) (hT : T.Nonempty) (hPne : ∀ y, ∀ x ∈ T, P y x ≠ 0)
    (k : ℕ) (herr : ∀ y, (Finset.univ.filter (fun x => H x y * P y x < 0)).card ≤ k)
    (w : X → ℝ) (hw : ∀ x ∈ T, 0 < w x) (c : ℝ)
    (hc : ∀ p ∈ W, ∀ x ∈ T, w x * p x ^ 2 ≤ c * ∑ z ∈ T, w z * p z ^ 2)
    (h12kc : 2 * (k : ℝ) * c ≤ 1) :
    (Fintype.card Y : ℝ) * (1 - 2 * (k : ℝ) * c) ^ 2 ≤ c * (N * rk W T) := by
  classical
  set d : X → ℝ := fun x => if x ∈ T then Real.sqrt (w x) else 0 with hd
  have hfr := finrank_scaled W T (fun x => Real.sqrt (w x))
      (fun x hx => (Real.sqrt_pos.mpr (hw x hx)).ne')
  rw [← hfr]
  obtain ⟨x0, hx0⟩ := hT
  refine final_ineq_sub H hH N hOp (W.map (dmap d)) (fun y => dmap d (P y)) (fun y => ⟨P y, hP y, rfl⟩)
    ?_ k ?_ c ?_ h12kc
  · intro y
    rw [sum_scaled_sq T w hw]
    apply sum_pos
    · intro z hz
      have : P y z ≠ 0 := hPne y z hz
      exact mul_pos (hw z hz) (by positivity)
    · exact ⟨x0, hx0⟩
  · intro y
    refine (Finset.card_le_card ?_).trans (herr y)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxt : x ∈ T
    · simp only [dmap_apply, hd, hxt, ↓reduceIte] at hx
      have hspos : 0 < Real.sqrt (w x) := Real.sqrt_pos.mpr (hw x hxt)
      have hmul : Real.sqrt (w x) * (H x y * P y x) < 0 := by linarith
      nlinarith
    · simp only [dmap_apply, hd, hxt, ↓reduceIte, zero_mul, mul_zero] at hx
      exact absurd hx (lt_irrefl 0)
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
    simpa [f, hx] using h3
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

set_option maxHeartbeats 800000 in
theorem signrank_core_sub {Y : Type*} [Fintype Y] [Nonempty Y] (H : X → Y → ℝ)
    (hH : ∀ x y, H x y = 1 ∨ H x y = -1)
    (N_nat : ℕ) (hNpos_nat : 0 < N_nat) (hYle : Fintype.card Y ≤ N_nat)
    (hOp : ∀ e : X → ℝ, ∑ y : Y, (∑ x : X, H x y * e x) ^ 2 ≤ (N_nat : ℝ) * ∑ x : X, e x ^ 2)
    (W : Submodule ℝ (X → ℝ)) (P : Y → X → ℝ) (hP : ∀ y, P y ∈ W)
    (hPne : ∀ y x, P y x ≠ 0)
    (k : ℕ) (herr : ∀ y, (Finset.univ.filter (fun x => H x y * P y x < 0)).card ≤ k)
    (T : Finset X) : T.card * Fintype.card Y ≤ N_nat * ((2 * k + 1) * rk W T) ^ 2 := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simp
  have y0 : Y := Classical.arbitrary Y
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
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = rk W T := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (2 * k + 1 : ℕ) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Fintype.card Y := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = N_nat := ⟨_, rfl⟩
  have hCeq : C = 2 * (k : ℝ) + 1 := by rw [hC]; push_cast; ring
  have hC1 : 1 ≤ C := by rw [hCeq]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hCpos : 0 < C := by linarith
  have hn1 : 1 ≤ n := by rw [hn]; exact_mod_cast hT.card_pos
  have hr1 : 1 ≤ r := by rw [hr]; exact_mod_cast (balanced_fp W T hT (hne T) 0).1
  have ht1 : 1 ≤ t := by rw [ht]; exact_mod_cast Fintype.card_pos (α := Y)
  have hN1 : 1 ≤ N := by rw [hN]; exact_mod_cast hNpos_nat
  have htN : t ≤ N := by rw [ht, hN]; exact_mod_cast hYle
  have hnpos : 0 < n := by linarith
  have hrpos : 0 < r := by linarith
  have htpos : 0 < t := by linarith
  have hNpos : 0 < N := by linarith
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 1 / (4 * n * N * C ^ 2 * r ^ 2) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  have hηeq : η * (4 * n * N * C ^ 2 * r ^ 2) = 1 := by rw [hη]; field_simp
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
  rw [← hn, ← hr] at hθ
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
  have hfinish : n * t ≤ N * C ^ 2 * r ^ 2 + 1 / 2 →
      T.card * Fintype.card Y ≤ N_nat * ((2 * k + 1) * rk W T) ^ 2 := by
    intro h
    by_contra hcon
    have h2 : N_nat * ((2 * k + 1) * rk W T) ^ 2 + 1 ≤ T.card * Fintype.card Y := by omega
    have h3 : N * C ^ 2 * r ^ 2 + 1 ≤ n * t := by
      have hcast : ((N_nat * ((2 * k + 1) * rk W T) ^ 2 + 1 : ℕ) : ℝ) ≤
          ((T.card * Fintype.card Y : ℕ) : ℝ) := by exact_mod_cast h2
      rw [hn, hr, hC, ht, hN]
      push_cast at hcast ⊢
      linarith
    linarith
  by_cases hcase : ∀ x ∈ T, θ x < θ xmin + n * η
  · by_contra hcon
    have h2 : N_nat * ((2 * k + 1) * rk W T) ^ 2 + 1 ≤ T.card * Fintype.card Y := by omega
    have hnt_big : N * C ^ 2 * r ^ 2 + 1 ≤ n * t := by
      have hcast : ((N_nat * ((2 * k + 1) * rk W T) ^ 2 + 1 : ℕ) : ℝ) ≤
          ((T.card * Fintype.card Y : ℕ) : ℝ) := by exact_mod_cast h2
      rw [hn, hr, hC, ht, hN]
      push_cast at hcast ⊢
      linarith
    have hn_big_nat : ((2 * k + 1) * rk W T) ^ 2 + 1 ≤ T.card := by
      have hlt : N_nat * ((2 * k + 1) * rk W T) ^ 2 < T.card * N_nat := by
        calc N_nat * ((2 * k + 1) * rk W T) ^ 2
            < T.card * Fintype.card Y := by omega
          _ ≤ T.card * N_nat := Nat.mul_le_mul_left T.card hYle
      have hlt2 : N_nat * ((2 * k + 1) * rk W T) ^ 2 < N_nat * T.card := by
        simpa [Nat.mul_comm] using hlt
      have hlt3 := Nat.lt_of_mul_lt_mul_left hlt2
      omega
    have hn_big : C ^ 2 * r ^ 2 + 1 ≤ n := by
      have hcast : (((((2 * k + 1) * rk W T) ^ 2 + 1 : ℕ) : ℝ)) ≤ (T.card : ℝ) := by
        exact_mod_cast hn_big_nat
      rw [hn, hr, hC]
      push_cast at hcast ⊢
      linarith
    set c : ℝ := r / n * (1 + n * η) with hcdef
    have hcpos : 0 < c := by rw [hcdef]; positivity
    have hcrN : c * r * N * n * C ^ 2 = N * C ^ 2 * r ^ 2 + 1 / 4 := by
      rw [hcdef]
      have hstep : r / n * (1 + n * η) * r * N * n * C ^ 2 =
          N * C ^ 2 * r ^ 2 + (1 / 4) * (η * (4 * n * N * C ^ 2 * r ^ 2)) := by
        field_simp
      rw [hstep, hηeq]
      ring
    have hcr_lt : c * r < 1 / C ^ 2 := by
      have h1 : (c * r * C ^ 2) * (N * n) = N * C ^ 2 * r ^ 2 + 1 / 4 := by linarith
      have h2' : N * C ^ 2 * r ^ 2 + 1 / 4 < N * n := by
        have : N * (C ^ 2 * r ^ 2 + 1) ≤ N * n := mul_le_mul_of_nonneg_left hn_big hNpos.le
        linarith
      have h3 : (c * r * C ^ 2) * (N * n) < 1 * (N * n) := by linarith
      have h4 : c * r * C ^ 2 < 1 := lt_of_mul_lt_mul_right h3 (by positivity)
      rw [lt_div_iff₀ (by positivity)]
      exact h4
    have hc_lt : c < 1 / C ^ 2 := by
      have : c ≤ c * r := by nlinarith
      linarith
    have h1C2 : 1 / C ^ 2 ≤ 1 / C := by
      rw [div_le_div_iff₀ (by positivity) hCpos]
      nlinarith
    have h2kc : 2 * (k : ℝ) * c ≤ 1 - 1 / C := by
      have hk_nn : (0 : ℝ) ≤ 2 * (k : ℝ) := by positivity
      have h1 : 2 * (k : ℝ) * c ≤ 2 * (k : ℝ) * (1 / C) :=
        mul_le_mul_of_nonneg_left (hc_lt.le.trans h1C2) hk_nn
      have h2' : 2 * (k : ℝ) * (1 / C) = 1 - 1 / C := by
        have : 2 * (k : ℝ) = C - 1 := by linarith
        rw [this]
        field_simp
      linarith
    have h12kc : 2 * (k : ℝ) * c ≤ 1 := by
      have : (0 : ℝ) < 1 / C := by positivity
      linarith
    have hfin := final_T_sub H hH (N_nat : ℝ) hOp W P hP T hT (fun y x _ => hPne y x) k herr
      (fun x => ((θ x)⁻¹) ^ m) hwpos c (by
        intro p hp x hx
        refine (hθ p hp x hx).trans ?_
        apply mul_le_mul_of_nonneg_right _ (hQ0 T p subset_rfl)
        rw [hcdef]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := hcase x hx
        linarith) h12kc
    rw [← hr, ← ht, ← hN] at hfin
    have hsq_ge : 1 / C ^ 2 ≤ (1 - 2 * (k : ℝ) * c) ^ 2 := by
      have hge : 1 / C ≤ 1 - 2 * (k : ℝ) * c := by linarith
      have hsq := pow_le_pow_left₀ (by positivity) hge 2
      simpa [one_div, inv_pow] using hsq
    have ht_le : t * (1 / C ^ 2) ≤ c * (N * r) :=
      (mul_le_mul_of_nonneg_left hsq_ge htpos.le).trans hfin
    have hnt_le : n * t ≤ N * C ^ 2 * r ^ 2 + 1 / 4 := by
      have hm1 := mul_le_mul_of_nonneg_left ht_le (show (0 : ℝ) ≤ n * C ^ 2 by positivity)
      have hlhs : n * C ^ 2 * (t * (1 / C ^ 2)) = n * t := by field_simp
      have hrhs : n * C ^ 2 * (c * (N * r)) = c * r * N * n * C ^ 2 := by ring
      linarith
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
    have hih' : n' * t ≤ N * C ^ 2 * j' ^ 2 := by
      have hcast : ((T'.card * Fintype.card Y : ℕ) : ℝ) ≤
          ((N_nat * ((2 * k + 1) * rk W T') ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast hih
      rw [hn', hj', hC, ht, hN]
      push_cast at hcast ⊢
      linarith
    have hj'r : j' ≤ r := by rw [hj', hr]; exact_mod_cast rk_mono W hT'sub
    have hj'0 : 0 ≤ j' := by rw [hj']; exact Nat.cast_nonneg _
    have hj'pos : 0 < j' := by
      rcases hj'0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hih'
        have : 1 ≤ n' * t := by nlinarith
        nlinarith
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
        r / n * θ x * (1 + K * ρ ^ m) * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 := by
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
      have hcoef : 0 ≤ r / n * θ x := mul_nonneg (by positivity) (hθpos x (hT'sub hx)).le
      calc ((θ x)⁻¹) ^ m * p x ^ 2
          ≤ r / n * θ x * (∑ z ∈ T \ T', ((θ z)⁻¹) ^ m * p' z ^ 2 +
              ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2) := h1
        _ ≤ r / n * θ x * (K * ρ ^ m * ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 +
              ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2) :=
            mul_le_mul_of_nonneg_left (by linarith) hcoef
        _ = _ := by ring
    obtain ⟨s, hs0, -, hsb, hsc⟩ := lev_T W T' (fun x => ((θ x)⁻¹) ^ m)
      (fun x hx => hwpos x (hT'sub hx))
    have hsle : ∀ x ∈ T', s x ≤ r / n * θ x * (1 + K * ρ ^ m) := by
      intro x hx
      obtain ⟨p, hp, hpx, heq⟩ := hsb x hx (hne T' x hx)
      have hd := hdom p hp x hx
      rw [heq] at hd
      have hQpos : 0 < ∑ z ∈ T', ((θ z)⁻¹) ^ m * p z ^ 2 :=
        lt_of_lt_of_le (mul_pos (hwpos x (hT'sub hx)) (by positivity))
          (single_le_sum (f := fun z => ((θ z)⁻¹) ^ m * p z ^ 2)
            (fun z hz => mul_nonneg (hwpos z (hT'sub hz)).le (sq_nonneg _)) hx)
      exact le_of_mul_le_mul_right hd hQpos
    have hrk' : j' ≤ r / n * (1 + K * ρ ^ m) * ∑ x ∈ T', θ x := by
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
    have hkey : j' * n ≤ r * n' := by
      have h1 : j' ≤ r / n * (1 + μ) * (n' * (1 - μ)) :=
        hrk'.trans (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hmargin
          (sum_nonneg fun x hx => (hθpos x (hT'sub hx)).le) (by positivity))
      have h2 : r / n * (1 + μ) * (n' * (1 - μ)) ≤ r / n * n' := by
        have hc : 0 ≤ r / n * n' := by positivity
        have : r / n * (1 + μ) * (n' * (1 - μ)) = r / n * n' - r / n * n' * μ ^ 2 := by ring
        rw [this]
        have : 0 ≤ r / n * n' * μ ^ 2 := by positivity
        linarith
      have h3 : j' * n ≤ r / n * n' * n := mul_le_mul_of_nonneg_right (h1.trans h2) hnpos.le
      calc j' * n ≤ r / n * n' * n := h3
        _ = r * n' := by field_simp
    apply hfinish
    have h1 : j' * (n * t) ≤ j' * (N * C ^ 2 * r * j') := by
      have hkeyt : j' * (n * t) ≤ r * (n' * t) := by
        have := mul_le_mul_of_nonneg_right hkey htpos.le
        linarith
      have h2 : r * (n' * t) ≤ r * (N * C ^ 2 * j' ^ 2) := mul_le_mul_of_nonneg_left hih' hrpos.le
      calc j' * (n * t) ≤ r * (n' * t) := hkeyt
        _ ≤ r * (N * C ^ 2 * j' ^ 2) := h2
        _ = j' * (N * C ^ 2 * r * j') := by ring
    have h2 : n * t ≤ N * C ^ 2 * r * j' := le_of_mul_le_mul_left h1 hj'pos
    have h3 : N * C ^ 2 * r * j' ≤ N * C ^ 2 * r * r :=
      mul_le_mul_of_nonneg_left hj'r (by positivity)
    have h4 : N * C ^ 2 * r * r = N * C ^ 2 * r ^ 2 := by ring
    linarith

end Weighted

lemma sum_univ_congr_fintype {α β : Type*} [AddCommMonoid β] {ft1 ft2 : Fintype α} (f : α → β) :
    ∑ x ∈ @Finset.univ α ft1, f x = ∑ x ∈ @Finset.univ α ft2, f x := by
  rw [Subsingleton.elim ft1 ft2]

lemma card_filter_univ_eq {α : Type*} {ft1 ft2 : Fintype α} (p q : α → Prop)
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ x, p x ↔ q x) :
    (@Finset.filter α p dp (@Finset.univ α ft1)).card =
    (@Finset.filter α q dq (@Finset.univ α ft2)).card := by
  have hf : ft1 = ft2 := Subsingleton.elim ft1 ft2
  subst hf
  have hpq : p = q := funext fun x => propext (h x)
  subst hpq
  exact congrArg (fun d => (@Finset.filter α p d (@Finset.univ α ft1)).card) (Subsingleton.elim dp dq)

lemma ipSign_op_bound (m : ℕ) (good : Finset (Fin m → Bool)) (e : (Fin m → Bool) → ℝ) :
    ∑ y : {g // g ∈ good}, (∑ x : Fin m → Bool, (-(ipSign m x y.1 : ℝ)) * e x) ^ 2 ≤
      ((2 ^ m : ℕ) : ℝ) * ∑ x : Fin m → Bool, e x ^ 2 := by
  have h1 : ∑ y : {g // g ∈ good}, (∑ x : Fin m → Bool, (-(ipSign m x y.1 : ℝ)) * e x) ^ 2 =
      ∑ g ∈ good, (∑ x : Fin m → Bool, (-(ipSign m x g : ℝ)) * e x) ^ 2 := by
    exact Finset.sum_coe_sort good (fun g => (∑ x : Fin m → Bool, (-(ipSign m x g : ℝ)) * e x) ^ 2)
  rw [h1]
  have h2 : ∑ g ∈ good, (∑ x : Fin m → Bool, (-(ipSign m x g : ℝ)) * e x) ^ 2 ≤
      ∑ g : Fin m → Bool, (∑ x : Fin m → Bool, (-(ipSign m x g : ℝ)) * e x) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good) (fun _ _ _ => sq_nonneg _)
  refine h2.trans_eq ?_
  have hexp : ∀ g : Fin m → Bool, (∑ x : Fin m → Bool, (-(ipSign m x g : ℝ)) * e x) ^ 2 =
      ∑ x : Fin m → Bool, ∑ x' : Fin m → Bool,
        e x * e x' * ((-(ipSign m x g : ℝ)) * (-(ipSign m x' g : ℝ))) := by
    intro g
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => by ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hinner : ∀ x : Fin m → Bool,
      ∑ g : Fin m → Bool, ∑ x' : Fin m → Bool,
        e x * e x' * ((-(ipSign m x g : ℝ)) * (-(ipSign m x' g : ℝ))) =
      ((2 ^ m : ℕ) : ℝ) * e x ^ 2 := by
    intro x
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ipSign_orth_real]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    push_cast
    ring
  simp_rw [hinner, ← Finset.mul_sum]

theorem main :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m k : Nat) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ),
      (∀ f g, A f g ≠ 0) →
      let words := (Finset.univ : Finset (Fin m → Bool))
      let odd := fun (f g : Fin m → Bool) =>
        ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
      let mistakes := fun g => (words.filter (fun f => ¬ ((0 < A f g) ↔ odd f g))).card
      (words.filter (fun g => mistakes g ≤ k)).card ≤ ((2*k+1)*A.rank)^2 := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro m k A hAne
  dsimp only []
  let X := Fin m → Bool
  let odd : X → X → Prop := fun f g =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
  let good : Finset X := (Finset.univ : Finset X).filter (fun g =>
    ((Finset.univ : Finset X).filter (fun f => ¬ ((0 < A f g) ↔ odd f g))).card ≤ k)
  rcases good.eq_empty_or_nonempty with hemp | hgood_ne
  · show good.card ≤ ((2 * k + 1) * A.rank) ^ 2
    rw [hemp]
    exact Nat.zero_le _
  haveI : Nonempty {g // g ∈ good} := ⟨⟨hgood_ne.choose, hgood_ne.choose_spec⟩⟩
  let Y := {g // g ∈ good}
  let H : X → Y → ℝ := fun f y => -(ipSign m f y.1 : ℝ)
  have hH_eq : ∀ f : X, ∀ y : Y, H f y = if odd f y.1 then 1 else -1 := by
    intro f y
    dsimp only [H]
    rw [ipSign_eq_ite]
    split_ifs with h1 h2 h2
    · norm_num
    · exfalso
      apply h2
      dsimp only [odd]
      exact Eq.subst (motive := fun n => n % 2 = 1)
        (card_filter_univ_eq _ _ (fun i => (iff_of_eq (Bool.and_eq_true (f i) (y.1 i))).symm)) h1
    · exfalso
      apply h1
      dsimp only [odd] at h2
      exact Eq.subst (motive := fun n => n % 2 = 1)
        (card_filter_univ_eq _ _ (fun i => iff_of_eq (Bool.and_eq_true (f i) (y.1 i)))) h2
    · norm_num
  have hH : ∀ x y, H x y = 1 ∨ H x y = -1 := by
    intro x y
    rw [hH_eq]
    split_ifs
    · left; rfl
    · right; rfl
  have hOp : ∀ e : X → ℝ, ∑ y : Y, (∑ x : X, H x y * e x) ^ 2 ≤ ((2 ^ m : ℕ) : ℝ) * ∑ x : X, e x ^ 2 := by
    intro e
    have hb := ipSign_op_bound m good e
    convert hb using 1
    · refine Finset.sum_congr (congrArg (@Finset.univ Y) (Subsingleton.elim _ _)) fun y _ => ?_
      exact congrArg (fun v : ℝ => v ^ 2) (sum_univ_congr_fintype _)
    · exact congrArg (fun v : ℝ => ((2 ^ m : ℕ) : ℝ) * v) (sum_univ_congr_fintype _)
  let W : Submodule ℝ (X → ℝ) := LinearMap.range A.mulVecLin
  let P : Y → X → ℝ := fun y f => A f y.1
  have hP : ∀ y : Y, P y ∈ W := by
    intro y
    refine ⟨Pi.single y.1 (1 : ℝ), ?_⟩
    funext f
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, P]
    rw [Finset.sum_eq_single y.1]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · intro hmem
      exact absurd (Finset.mem_univ y.1) hmem
  have hPne : ∀ y x, P y x ≠ 0 := fun y x => hAne x y.1
  have herr : ∀ y : Y, (Finset.univ.filter (fun x => H x y * P y x < 0)).card ≤ k := by
    intro y
    have hyk : ((Finset.univ : Finset X).filter (fun f => ¬ ((0 < A f y.1) ↔ odd f y.1))).card ≤ k :=
      (Finset.mem_filter.mp y.2).2
    have heq : (Finset.univ.filter (fun x => H x y * P y x < 0)).card =
        ((Finset.univ : Finset X).filter (fun f => ¬ ((0 < A f y.1) ↔ odd f y.1))).card := by
      refine card_filter_univ_eq _ _ (fun f => ?_)
      rw [hH_eq f y]
      dsimp only [P]
      have hne0 := hAne f y.1
      by_cases ho : odd f y.1
      · rw [if_pos ho, one_mul]
        constructor
        · intro hlt hiff
          have := hiff.mpr ho
          linarith
        · intro hnot
          have hnp : ¬ (0 < A f y.1) := fun hp => hnot ⟨fun _ => ho, fun _ => hp⟩
          exact lt_of_le_of_ne (not_lt.mp hnp) hne0
      · rw [if_neg ho]
        constructor
        · intro hlt hiff
          exact ho (hiff.mp (by linarith))
        · intro hnot
          have hp : 0 < A f y.1 := by
            by_contra hnp
            exact hnot ⟨fun h => absurd h hnp, fun h => absurd h ho⟩
          linarith
    rw [heq]
    exact hyk
  have hYcard : Fintype.card Y = good.card := Fintype.card_coe good
  have hYle : Fintype.card Y ≤ 2 ^ m := by
    rw [hYcard]
    have hsub : good.card ≤ (Finset.univ : Finset X).card := Finset.card_le_card (Finset.subset_univ good)
    have hcardX : (Finset.univ : Finset X).card = 2 ^ m := by
      simp [X]
    exact hsub.trans_eq hcardX
  have hcore := signrank_core_sub H hH (2 ^ m) (Nat.two_pow_pos m) hYle hOp W P hP hPne k herr Finset.univ
  have hcardX : (Finset.univ : Finset X).card = 2 ^ m := by simp [X]
  rw [hcardX, hYcard] at hcore
  have hcancel : good.card ≤ ((2 * k + 1) * rk W Finset.univ) ^ 2 :=
    Nat.le_of_mul_le_mul_left hcore (Nat.two_pow_pos m)
  have hrk_le : rk W Finset.univ ≤ A.rank := by
    exact rk_le W Finset.univ
  exact hcancel.trans (Nat.pow_le_pow_left (Nat.mul_le_mul_left (2 * k + 1) hrk_le) 2)

end PEqualNP.Outside.L_lib_1264_aux

theorem PEqualNP.Outside.L_lib_1264 : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m k : Nat) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ),
  (∀ f g, A f g ≠ 0) →
  let words := (Finset.univ : Finset (Fin m → Bool))
  let odd := fun (f g : Fin m → Bool) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
  let mistakes := fun g => (words.filter (fun f => ¬ ((0 < A f g) ↔ odd f g))).card
  (words.filter (fun g => mistakes g ≤ k)).card ≤ ((2*k+1)*A.rank)^2 :=
  PEqualNP.Outside.L_lib_1264_aux.main
