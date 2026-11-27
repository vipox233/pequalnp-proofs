import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_707

open scoped BigOperators Matrix

abbrev signedMat {n : ℕ} (s : Fin n × Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if s (i, j) then -A i j else A i j

lemma signedMat_invol {n : ℕ} (s : Fin n × Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℝ) :
    signedMat s (signedMat s A) = A := by
  ext i j
  simp only [signedMat, Matrix.of_apply]
  cases s (i, j) <;> simp

lemma signedMat_sq {n : ℕ} (s : Fin n × Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : (signedMat s A i j) ^ 2 = (A i j) ^ 2 := by
  simp only [signedMat, Matrix.of_apply]
  cases s (i, j) <;> simp

lemma permanent_signedMat_sq {n : ℕ} (s : Fin n × Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.permanent (Matrix.of fun i j => (signedMat s A i j) ^ 2) =
      Matrix.permanent (Matrix.of fun i j => (A i j) ^ 2) := by
  congr 1
  ext i j
  exact signedMat_sq s A i j

lemma permanent_eq_row_perm {α : Type*} [Fintype α] [DecidableEq α] (M : Matrix α α ℝ) :
    M.permanent = ∑ σ : Equiv.Perm α, ∏ i : α, M i (σ i) := by
  unfold Matrix.permanent
  rw [← Equiv.sum_comp (Equiv.inv (Equiv.Perm α))]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Equiv.prod_comp σ]
  apply Finset.prod_congr rfl
  intro i _
  simp

lemma permanent_one {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) ℝ).permanent = 1 := by
  unfold Matrix.permanent
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp [Matrix.one_apply]
  · intro σ _ hσ
    have hex : ∃ i : Fin n, σ i ≠ i := by
      by_contra hall
      push Not at hall
      exact hσ (Equiv.ext hall)
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  · intro h; exact absurd (Finset.mem_univ _) h

lemma det_signedMat_one_sq {n : ℕ} (s : Fin n × Fin n → Bool) :
    (Matrix.det (signedMat s (1 : Matrix (Fin n) (Fin n) ℝ))) ^ 2 = 1 := by
  have hdiag : signedMat s (1 : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal (fun i => if s (i, i) then (-1 : ℝ) else 1) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp only [signedMat, Matrix.of_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    · simp [signedMat, Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h]
  rw [hdiag, Matrix.det_diagonal, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  cases s (i, i) <;> simp

lemma total_weight_lower_bound {n p t : ℕ}
    (signs : Fin t → Fin n × Fin n → Bool) (w : Fin t → ℝ)
    (hgood1 : ((p : ℝ) - 1) * Matrix.permanent (Matrix.of fun i j => ((1 : Matrix (Fin n) (Fin n) ℝ) i j) ^ 2) ≤
      (p : ℝ) * ∑ h : Fin t, w h * (Matrix.det (signedMat (signs h) 1)) ^ 2) :
    (p : ℝ) - 1 ≤ (p : ℝ) * ∑ h ∈ Finset.univ.filter (fun h : Fin t => w h ≠ 0), w h := by
  have hsq1 : (Matrix.of fun i j : Fin n => ((1 : Matrix (Fin n) (Fin n) ℝ) i j) ^ 2) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [hsq1, permanent_one, mul_one] at hgood1
  have hest : (∑ h : Fin t, w h * (Matrix.det (signedMat (signs h) 1)) ^ 2) =
      ∑ h ∈ Finset.univ.filter (fun h : Fin t => w h ≠ 0), w h := by
    trans (∑ h : Fin t, w h)
    · apply Finset.sum_congr rfl
      intro h _
      rw [det_signedMat_one_sq, mul_one]
    · symm
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h _
      by_cases hw : w h = 0 <;> simp [hw]
  rw [hest] at hgood1
  exact hgood1

lemma prod_add_bool {α : Type*} [Fintype α] [DecidableEq α] (f g : α → ℝ) :
    (∏ i : α, (f i + g i)) =
      ∑ mask : α → Bool, ∏ i : α, if mask i then f i else g i := by
  have h := Fintype.prod_sum (fun (i : α) (b : Bool) => if b then f i else g i)
  convert h using 1
  apply Finset.prod_congr rfl
  intro i _
  simp

lemma det_add_rows {n : ℕ} (u v : Fin n → Fin n → ℝ) :
    Matrix.det (Matrix.of fun i j => u i j + v i j) =
      ∑ mask : Fin n → Bool, Matrix.det (Matrix.of fun i j => if mask i then u i j else v i j) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (∏ i : Fin n, (u (σ i) i + v (σ i) i)) =
        ∑ mask : Fin n → Bool, ∏ i : Fin n, if mask (σ i) then u (σ i) i else v (σ i) i := by
    intro σ
    rw [← Equiv.prod_comp σ⁻¹]
    have h1 : (∏ i : Fin n, (u (σ (σ⁻¹ i)) (σ⁻¹ i) + v (σ (σ⁻¹ i)) (σ⁻¹ i))) =
        ∏ i : Fin n, (u i (σ⁻¹ i) + v i (σ⁻¹ i)) := by
      apply Finset.prod_congr rfl; intro i _; simp
    rw [h1, prod_add_bool]
    apply Finset.sum_congr rfl
    intro mask _
    rw [← Equiv.prod_comp σ]
    apply Finset.prod_congr rfl
    intro i _
    simp
  simp_rw [hterm, Finset.smul_sum]
  rw [Finset.sum_comm]

lemma det_row_scale {n : ℕ} (c : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.det (Matrix.of fun i j => c i * A i j) = (∏ i : Fin n, c i) * Matrix.det A := by
  simp only [Matrix.det_apply, Matrix.of_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ c]
  simp only [Units.smul_def, zsmul_eq_mul]
  ring

lemma indiv_weight_direct {n p t : ℕ}
    (signs : Fin t → Fin n × Fin n → Bool) (w : Fin t → ℝ) (hw : ∀ h, 0 ≤ w h)
    (W : Matrix (Fin n) (Fin n) ℝ) (h : Fin t)
    (hgood : (p : ℝ) * (∑ h' : Fin t, w h' * (Matrix.det (signedMat (signs h') (signedMat (signs h) W))) ^ 2) ≤
      ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (signedMat (signs h) W i j) ^ 2)) :
    (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
      ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
  have hsingle : w h * (Matrix.det W) ^ 2 ≤
      ∑ h' : Fin t, w h' * (Matrix.det (signedMat (signs h') (signedMat (signs h) W))) ^ 2 := by
    have heq : w h * (Matrix.det W) ^ 2 =
        w h * (Matrix.det (signedMat (signs h) (signedMat (signs h) W))) ^ 2 := by
      rw [signedMat_invol]
    rw [heq]
    exact Finset.single_le_sum
      (f := fun h' => w h' * (Matrix.det (signedMat (signs h') (signedMat (signs h) W))) ^ 2)
      (fun h' _ => mul_nonneg (hw h') (sq_nonneg _)) (Finset.mem_univ h)
  have h1 : (p : ℝ) * (w h * (Matrix.det W) ^ 2) ≤
      (p : ℝ) * ∑ h' : Fin t, w h' * (Matrix.det (signedMat (signs h') (signedMat (signs h) W))) ^ 2 :=
    mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg p)
  rw [permanent_signedMat_sq] at hgood
  linarith

lemma indiv_weight_masked {n p t : ℕ}
    (signs : Fin t → Fin n × Fin n → Bool) (w : Fin t → ℝ) (hw : ∀ h, 0 ≤ w h)
    (W : Matrix (Fin n) (Fin n) ℝ) (h : Fin t)
    (hgoodM : ∀ mask : Fin n → Bool,
      let B := signedMat (signs h) W
      let M : Matrix (Fin n) (Fin n) ℝ :=
        Matrix.of fun i j => if mask i then max (B i j) 0 else max (-B i j) 0
      (p : ℝ) * (∑ h' : Fin t, w h' * (Matrix.det (signedMat (signs h') M)) ^ 2) ≤
        ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (M i j) ^ 2)) :
    (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
      (2 : ℝ) ^ n * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
  let B : Matrix (Fin n) (Fin n) ℝ := signedMat (signs h) W
  let Bp : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => max (B i j) 0
  let Bn : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => max (-B i j) 0
  let M : (Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ :=
    fun mask => Matrix.of fun i j => if mask i then Bp i j else Bn i j
  have hW_split : W = Matrix.of fun i j => signedMat (signs h) Bp i j + (-signedMat (signs h) Bn i j) := by
    ext i j
    have hB : B i j = Bp i j - Bn i j := by
      simp only [Bp, Bn, Matrix.of_apply]
      rcases le_total 0 (B i j) with h0 | h0
      · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    have hinv : W i j = signedMat (signs h) B i j := by
      have := congrFun (congrFun (signedMat_invol (signs h) W) i) j
      exact this.symm
    rw [hinv]
    simp only [signedMat, Matrix.of_apply]
    cases signs h (i, j) <;> simp [hB] <;> ring
  have hdet_sum : Matrix.det W =
      ∑ mask : Fin n → Bool,
        (∏ i : Fin n, if mask i then (1 : ℝ) else -1) * Matrix.det (signedMat (signs h) (M mask)) := by
    rw [hW_split]
    rw [det_add_rows (fun i j => signedMat (signs h) Bp i j) (fun i j => -signedMat (signs h) Bn i j)]
    apply Finset.sum_congr rfl
    intro mask _
    have hmat : (Matrix.of fun i j => if mask i then signedMat (signs h) Bp i j else -signedMat (signs h) Bn i j) =
        Matrix.of fun i j => (if mask i then (1 : ℝ) else -1) * signedMat (signs h) (M mask) i j := by
      ext i j
      simp only [M, signedMat, Matrix.of_apply]
      cases mask i <;> cases signs h (i, j) <;> simp
    rw [hmat, det_row_scale]
  have hcs : (Matrix.det W) ^ 2 ≤
      (2 : ℝ) ^ n * ∑ mask : Fin n → Bool, (Matrix.det (signedMat (signs h) (M mask))) ^ 2 := by
    rw [hdet_sum]
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → Bool))
      (fun mask => ∏ i : Fin n, if mask i then (1 : ℝ) else -1)
      (fun mask => Matrix.det (signedMat (signs h) (M mask)))
    have hc1 : (∑ mask : Fin n → Bool, (∏ i : Fin n, if mask i then (1 : ℝ) else -1) ^ 2) =
        (2 : ℝ) ^ n := by
      have hsq : ∀ mask : Fin n → Bool,
          (∏ i : Fin n, if mask i then (1 : ℝ) else -1) ^ 2 = 1 := by
        intro mask
        rw [← Finset.prod_pow]
        apply Finset.prod_eq_one
        intro i _
        cases mask i <;> norm_num
      simp_rw [hsq, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [hc1] at h1
    exact h1
  have hperm_sum : (∑ mask : Fin n → Bool, Matrix.permanent (Matrix.of fun i j => (M mask i j) ^ 2)) =
      Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
    rw [← permanent_signedMat_sq (signs h) W]
    simp_rw [permanent_eq_row_perm, Matrix.of_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    have hrow_sq : ∀ i : Fin n, (B i (σ i)) ^ 2 = (Bp i (σ i)) ^ 2 + (Bn i (σ i)) ^ 2 := by
      intro i
      simp only [Bp, Bn, Matrix.of_apply]
      rcases le_total 0 (B i (σ i)) with h0 | h0
      · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
      · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
    have hprod : (∏ i : Fin n, (B i (σ i)) ^ 2) =
        ∑ mask : Fin n → Bool, ∏ i : Fin n, (M mask i (σ i)) ^ 2 := by
      simp_rw [hrow_sq, prod_add_bool]
      apply Finset.sum_congr rfl
      intro mask _
      apply Finset.prod_congr rfl
      intro i _
      simp only [M, Matrix.of_apply]
      cases mask i <;> simp
    exact hprod.symm
  have hsum_bound :
      (p : ℝ) * w h * ∑ mask : Fin n → Bool, (Matrix.det (signedMat (signs h) (M mask))) ^ 2 ≤
        ((p : ℝ) + 1) * ∑ mask : Fin n → Bool, Matrix.permanent (Matrix.of fun i j => (M mask i j) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro mask _
    have hsingle : w h * (Matrix.det (signedMat (signs h) (M mask))) ^ 2 ≤
        ∑ h' : Fin t, w h' * (Matrix.det (signedMat (signs h') (M mask))) ^ 2 :=
      Finset.single_le_sum
        (f := fun h' => w h' * (Matrix.det (signedMat (signs h') (M mask))) ^ 2)
        (fun h' _ => mul_nonneg (hw h') (sq_nonneg _)) (Finset.mem_univ h)
    have hm : (p : ℝ) * (∑ h' : Fin t, w h' * (Matrix.det (signedMat (signs h') (M mask))) ^ 2) ≤
        ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (M mask i j) ^ 2) := hgoodM mask
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have h1 := mul_le_mul_of_nonneg_left hsingle hp0
    linarith
  have hpw0 : (0 : ℝ) ≤ (p : ℝ) * w h := mul_nonneg (Nat.cast_nonneg p) (hw h)
  have hstep1 : (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
      (2 : ℝ) ^ n * ((p : ℝ) * w h * ∑ mask : Fin n → Bool, (Matrix.det (signedMat (signs h) (M mask))) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hcs hpw0
    linarith
  have hstep2 : (2 : ℝ) ^ n * ((p : ℝ) * w h * ∑ mask : Fin n → Bool, (Matrix.det (signedMat (signs h) (M mask))) ^ 2) ≤
      (2 : ℝ) ^ n * (((p : ℝ) + 1) * ∑ mask : Fin n → Bool, Matrix.permanent (Matrix.of fun i j => (M mask i j) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsum_bound (by positivity)
  rw [hperm_sum] at hstep2
  calc (p : ℝ) * w h * (Matrix.det W) ^ 2
      ≤ (2 : ℝ) ^ n * ((p : ℝ) * w h * ∑ mask : Fin n → Bool, (Matrix.det (signedMat (signs h) (M mask))) ^ 2) := hstep1
    _ ≤ (2 : ℝ) ^ n * (((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2)) := hstep2
    _ = (2 : ℝ) ^ n * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by ring

lemma reduce_from_witness {n p t K R : ℕ} (hp : 2 ≤ p)
    (w : Fin t → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hdet : Matrix.det W ≠ 0)
    (htot : (p : ℝ) - 1 ≤ (p : ℝ) * ∑ h ∈ Finset.univ.filter (fun h : Fin t => w h ≠ 0), w h)
    (hindiv : ∀ h : Fin t, (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
      (K : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2))
    (hwit : (n : ℝ) ^ n * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) ≤
      (R : ℝ) * (n.factorial : ℝ) * (Matrix.det W) ^ 2) :
    (p - 1) * n ^ n ≤ (p + 1) * K * R * n.factorial *
      (Finset.univ.filter (fun h : Fin t => w h ≠ 0)).card := by
  let S := Finset.univ.filter (fun h : Fin t => w h ≠ 0)
  have hd2_pos : (0 : ℝ) < (Matrix.det W) ^ 2 := sq_pos_of_ne_zero hdet
  have hnn_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ n := by positivity
  have h1 : ((p : ℝ) - 1) * ((n : ℝ) ^ n * (Matrix.det W) ^ 2) ≤
      ((p : ℝ) * ∑ h ∈ S, w h) * ((n : ℝ) ^ n * (Matrix.det W) ^ 2) :=
    mul_le_mul_of_nonneg_right htot (mul_nonneg hnn_nonneg hd2_pos.le)
  have h2 : ((p : ℝ) * ∑ h ∈ S, w h) * ((n : ℝ) ^ n * (Matrix.det W) ^ 2) =
      (n : ℝ) ^ n * ∑ h ∈ S, (p : ℝ) * w h * (Matrix.det W) ^ 2 := by
    rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    ring
  have h3 : (∑ h ∈ S, (p : ℝ) * w h * (Matrix.det W) ^ 2) ≤
      (S.card : ℝ) * ((K : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2)) := by
    calc (∑ h ∈ S, (p : ℝ) * w h * (Matrix.det W) ^ 2)
        ≤ ∑ _h ∈ S, ((K : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2)) :=
          Finset.sum_le_sum (fun h _ => hindiv h)
      _ = (S.card : ℝ) * ((K : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2)) := by
          simp [nsmul_eq_mul]
  have h4 : ((p : ℝ) - 1) * (n : ℝ) ^ n * (Matrix.det W) ^ 2 ≤
      (((p : ℝ) + 1) * (K : ℝ) * (R : ℝ) * (n.factorial : ℝ) * (S.card : ℝ)) * (Matrix.det W) ^ 2 := by
    have h3' := mul_le_mul_of_nonneg_left h3 hnn_nonneg
    have hcoeff : (0 : ℝ) ≤ (S.card : ℝ) * (K : ℝ) * ((p : ℝ) + 1) := by positivity
    have h5 := mul_le_mul_of_nonneg_left hwit hcoeff
    linarith
  have hfinal : ((p : ℝ) - 1) * (n : ℝ) ^ n ≤
      ((p : ℝ) + 1) * (K : ℝ) * (R : ℝ) * (n.factorial : ℝ) * (S.card : ℝ) :=
    le_of_mul_le_mul_right h4 hd2_pos
  have hp1 : 1 ≤ p := by omega
  have hcast : (((p - 1) * n ^ n : ℕ) : ℝ) ≤
      (((p + 1) * K * R * n.factorial * S.card : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hp1]
    exact hfinal
  exact_mod_cast hcast

/-! ### Permanent helpers and Binomial Max-Term Inequality -/

lemma permanent_all_ones {m : ℕ} :
    Matrix.permanent (Matrix.of fun _ _ : Fin m => (1 : ℝ)) = (m.factorial : ℝ) := by
  simp [Matrix.permanent, Fintype.card_perm]

lemma permanent_reindex_self {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (M : Matrix α α ℝ) :
    (M.reindex e e).permanent = M.permanent := by
  unfold Matrix.permanent
  let conj : Equiv.Perm α ≃ Equiv.Perm β :=
    { toFun := fun σ => e.symm.trans (σ.trans e)
      invFun := fun τ => e.trans (τ.trans e.symm)
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext y; simp }
  rw [← Equiv.sum_comp conj]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Equiv.prod_comp e]
  apply Finset.prod_congr rfl
  intro i _
  simp [conj]

lemma permanent_fromBlocks_zero {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Matrix α α ℝ) (B : Matrix β β ℝ) :
    (Matrix.fromBlocks A 0 0 B).permanent = A.permanent * B.permanent := by
  let M := Matrix.fromBlocks A (0 : Matrix α β ℝ) (0 : Matrix β α ℝ) B
  let Φ : Equiv.Perm α × Equiv.Perm β → Equiv.Perm (α ⊕ β) :=
    fun p => Equiv.sumCongr p.1 p.2
  have hΦ_inj : Function.Injective Φ := by
    rintro ⟨σ₁, σ₂⟩ ⟨τ₁, τ₂⟩ h
    ext x
    · have := Equiv.congr_fun h (Sum.inl x)
      simpa [Φ] using this
    · have := Equiv.congr_fun h (Sum.inr x)
      simpa [Φ] using this
  have hzero : ∀ σ : Equiv.Perm (α ⊕ β), σ ∉ Finset.univ.image Φ →
      (∏ x : α ⊕ β, M (σ x) x) = 0 := by
    intro σ hnot
    by_cases hL : ∀ a : α, ∃ a' : α, σ (Sum.inl a) = Sum.inl a'
    · by_cases hR : ∀ b : β, ∃ b' : β, σ (Sum.inr b) = Sum.inr b'
      · exfalso
        choose f hf using hL
        choose g hg using hR
        have hf_inj : Function.Injective f := by
          intro a₁ a₂ heq
          have : σ (Sum.inl a₁) = σ (Sum.inl a₂) := by rw [hf, hf, heq]
          exact Sum.inl.inj (σ.injective this)
        have hg_inj : Function.Injective g := by
          intro b₁ b₂ heq
          have : σ (Sum.inr b₁) = σ (Sum.inr b₂) := by rw [hg, hg, heq]
          exact Sum.inr.inj (σ.injective this)
        let σ₁ : Equiv.Perm α := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
        let σ₂ : Equiv.Perm β := Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg_inj)
        apply hnot
        refine Finset.mem_image.mpr ⟨(σ₁, σ₂), Finset.mem_univ _, ?_⟩
        ext x
        cases x with
        | inl a => simp [Φ, σ₁, hf]
        | inr b => simp [Φ, σ₂, hg]
      · push Not at hR
        rcases hR with ⟨b, hb⟩
        cases hσb : σ (Sum.inr b) with
        | inl a =>
          exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inr b)) (by simp [M, hσb])
        | inr b' => exact absurd hσb (hb b')
    · push Not at hL
      rcases hL with ⟨a, ha⟩
      cases hσa : σ (Sum.inl a) with
      | inr b =>
        exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl a)) (by simp [M, hσa])
      | inl a' => exact absurd hσa (ha a')
  unfold Matrix.permanent
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image Φ)) (fun σ _ hnot => hzero σ hnot)]
  rw [Finset.sum_image (fun p _ q _ h => hΦ_inj h)]
  have hprod : ∀ p : Equiv.Perm α × Equiv.Perm β,
      (∏ x : α ⊕ β, M (Φ p x) x) = (∏ a : α, A (p.1 a) a) * (∏ b : β, B (p.2 b) b) := by
    intro p
    rw [Fintype.prod_sum_type]
    simp [M, Φ]
  simp_rw [hprod]
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum]

lemma permanent_smul {α : Type*} [Fintype α] [DecidableEq α] (c : ℝ) (M : Matrix α α ℝ) :
    (c • M).permanent = c ^ Fintype.card α * M.permanent := by
  unfold Matrix.permanent
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ]

lemma binom_max_term (a b : ℕ) :
    (a + b) ^ (a + b) * (a.factorial * b.factorial) ≤
      (a + b + 1) * (a + b).factorial * (a ^ a * b ^ b) := by
  let T : ℕ → ℕ := fun j => (a + b).choose j * a ^ j * b ^ (a + b - j)
  have hstep_inc : ∀ j < a, T j ≤ T (j + 1) := by
    intro j hj
    have hch : (j + 1) * (a + b).choose (j + 1) = (a + b - j) * (a + b).choose j := by
      have := Nat.choose_succ_right_eq (a + b) j
      linarith
    have hsub : a + b - j = (a + b - (j + 1)) + 1 := by omega
    have hmul : (j + 1) * T j ≤ (j + 1) * T (j + 1) := by
      have hl : (j + 1) * T j =
          ((j + 1) * b) * ((a + b).choose j * a ^ j * b ^ (a + b - (j + 1))) := by
        simp only [T]
        rw [hsub, pow_succ]
        ring
      have hr : (j + 1) * T (j + 1) =
          ((a + b - j) * a) * ((a + b).choose j * a ^ j * b ^ (a + b - (j + 1))) := by
        simp only [T]
        calc (j + 1) * ((a + b).choose (j + 1) * a ^ (j + 1) * b ^ (a + b - (j + 1)))
            = ((j + 1) * (a + b).choose (j + 1)) * (a * a ^ j) * b ^ (a + b - (j + 1)) := by
                rw [pow_succ]; ring
          _ = ((a + b - j) * (a + b).choose j) * (a * a ^ j) * b ^ (a + b - (j + 1)) := by
                rw [hch]
          _ = ((a + b - j) * a) * ((a + b).choose j * a ^ j * b ^ (a + b - (j + 1))) := by ring
      rw [hl, hr]
      apply Nat.mul_le_mul_right
      have hba : (j + 1) * b ≤ (a + b - j) * a := by
        zify [show j ≤ a + b by omega]
        nlinarith
      exact hba
    exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos j)
  have hstep_dec : ∀ j, a ≤ j → j < a + b → T (j + 1) ≤ T j := by
    intro j hja hjb
    have hch : (j + 1) * (a + b).choose (j + 1) = (a + b - j) * (a + b).choose j := by
      have := Nat.choose_succ_right_eq (a + b) j
      linarith
    have hsub : a + b - j = (a + b - (j + 1)) + 1 := by omega
    have hmul : (j + 1) * T (j + 1) ≤ (j + 1) * T j := by
      have hl : (j + 1) * T j =
          ((j + 1) * b) * ((a + b).choose j * a ^ j * b ^ (a + b - (j + 1))) := by
        simp only [T]
        rw [hsub, pow_succ]
        ring
      have hr : (j + 1) * T (j + 1) =
          ((a + b - j) * a) * ((a + b).choose j * a ^ j * b ^ (a + b - (j + 1))) := by
        simp only [T]
        calc (j + 1) * ((a + b).choose (j + 1) * a ^ (j + 1) * b ^ (a + b - (j + 1)))
            = ((j + 1) * (a + b).choose (j + 1)) * (a * a ^ j) * b ^ (a + b - (j + 1)) := by
                rw [pow_succ]; ring
          _ = ((a + b - j) * (a + b).choose j) * (a * a ^ j) * b ^ (a + b - (j + 1)) := by
                rw [hch]
          _ = ((a + b - j) * a) * ((a + b).choose j * a ^ j * b ^ (a + b - (j + 1))) := by ring
      rw [hl, hr]
      apply Nat.mul_le_mul_right
      have hab : (a + b - j) * a ≤ (j + 1) * b := by
        zify [show j ≤ a + b by omega]
        nlinarith
      exact hab
    exact Nat.le_of_mul_le_mul_left hmul (Nat.succ_pos j)
  have hle_Ta : ∀ j ≤ a + b, T j ≤ T a := by
    intro j hj
    rcases le_total j a with hja | haj
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hja
      have hinc : ∀ k, j + k ≤ a → T j ≤ T (j + k) := by
        intro k hk
        induction k with
        | zero => simp
        | succ k ih =>
          exact le_trans (ih (by omega)) (hstep_inc (j + k) (by omega))
      have := hinc d (by omega)
      simpa [← hd] using this
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le haj
      subst hd
      induction d with
      | zero => simp
      | succ d ih =>
        exact le_trans (hstep_dec (a + d) (by omega) (by omega)) (ih (by omega) (by omega))
  have hsum : (a + b) ^ (a + b) = ∑ j ∈ Finset.range (a + b + 1), T j := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp only [T, Nat.cast_id]
    ring
  have hbound : (a + b) ^ (a + b) ≤ (a + b + 1) * T a := by
    rw [hsum]
    calc (∑ j ∈ Finset.range (a + b + 1), T j)
        ≤ ∑ _j ∈ Finset.range (a + b + 1), T a :=
          Finset.sum_le_sum (fun j hj => hle_Ta j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)))
      _ = (a + b + 1) * T a := by simp
  have hTa : T a * (a.factorial * b.factorial) = (a + b).factorial * (a ^ a * b ^ b) := by
    simp only [T, Nat.add_sub_cancel_left]
    have hch := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
    rw [Nat.add_sub_cancel_left] at hch
    calc (a + b).choose a * a ^ a * b ^ b * (a.factorial * b.factorial)
        = ((a + b).choose a * a.factorial * b.factorial) * (a ^ a * b ^ b) := by ring
      _ = (a + b).factorial * (a ^ a * b ^ b) := by rw [hch]
  calc (a + b) ^ (a + b) * (a.factorial * b.factorial)
      ≤ ((a + b + 1) * T a) * (a.factorial * b.factorial) :=
        Nat.mul_le_mul_right _ hbound
    _ = (a + b + 1) * (T a * (a.factorial * b.factorial)) := by ring
    _ = (a + b + 1) * (a + b).factorial * (a ^ a * b ^ b) := by rw [hTa]; ring

/-! ### Dyadic Sylvester Hadamard Witness (Clauses 3 and 4) -/

lemma sylvester_exists (k : ℕ) :
    ∃ H : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ,
      (∀ i j, H i j = -1 ∨ H i j = 1) ∧
      H * H.transpose = ((2 ^ k : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) := by
  induction k with
  | zero =>
    refine ⟨Matrix.of fun _ _ => 1, fun _ _ => Or.inr rfl, ?_⟩
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply]
  | succ k ih =>
    rcases ih with ⟨H, hH_ent, hH_orth⟩
    let B : Matrix (Fin (2 ^ k) ⊕ Fin (2 ^ k)) (Fin (2 ^ k) ⊕ Fin (2 ^ k)) ℝ :=
      Matrix.fromBlocks H H H (-H)
    let e : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
      finSumFinEquiv.trans (finCongr (by ring))
    refine ⟨B.reindex e e, ?_, ?_⟩
    · intro i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, B]
      cases e.symm i with
      | inl a =>
        cases e.symm j with
        | inl b => exact hH_ent a b
        | inr b => exact hH_ent a b
      | inr a =>
        cases e.symm j with
        | inl b => exact hH_ent a b
        | inr b =>
          rcases hH_ent a b with h1 | h1
          · right; simp [h1]
          · left; simp [h1]
    · have hB_orth : B * B.transpose = ((2 ^ (k + 1) : ℕ) : ℝ) • 1 := by
        have hBt : B.transpose = Matrix.fromBlocks H.transpose H.transpose H.transpose (-H.transpose) := by
          simp [B, Matrix.fromBlocks_transpose]
        rw [hBt, Matrix.fromBlocks_multiply]
        have hsum : H * H.transpose + H * H.transpose =
            ((2 ^ (k + 1) : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) := by
          rw [hH_orth]
          ext i j
          by_cases h : i = j
          · simp [h, pow_succ]; ring
          · simp [h]
        have hdiff : H * H.transpose + H * -H.transpose = 0 := by
          rw [Matrix.mul_neg, add_neg_cancel]
        have hdiff2 : H * H.transpose + -H * H.transpose = 0 := by
          rw [Matrix.neg_mul, add_neg_cancel]
        have hneg : H * H.transpose + -H * -H.transpose =
            ((2 ^ (k + 1) : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ) := by
          rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
          exact hsum
        rw [hsum, hdiff, hdiff2, hneg]
        ext i j
        cases i <;> cases j <;> simp [Matrix.one_apply]
      have hmul : B.reindex e e * (B.reindex e e).transpose = (B * B.transpose).reindex e e := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
        exact Equiv.sum_comp e.symm (fun k => B (e.symm i) k * B (e.symm j) k)
      rw [hmul, hB_orth]
      ext i j
      by_cases h : i = j
      · subst h; simp
      · have hne : e.symm i ≠ e.symm j := fun hc => h (e.symm.injective hc)
        simp [h, hne]

lemma sylvester_witness (k : ℕ) :
    ∃ H : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ,
      (∀ i j, H i j = -1 ∨ H i j = 0 ∨ H i j = 1) ∧
      Matrix.det H ≠ 0 ∧
      ((2 ^ k : ℕ) : ℝ) ^ (2 ^ k) * Matrix.permanent (Matrix.of fun i j => (H i j) ^ 2) =
        ((2 ^ k).factorial : ℝ) * (Matrix.det H) ^ 2 := by
  rcases sylvester_exists k with ⟨H, hH_ent, hH_orth⟩
  have hdet_sq : (Matrix.det H) ^ 2 = ((2 ^ k : ℕ) : ℝ) ^ (2 ^ k) := by
    calc (Matrix.det H) ^ 2 = Matrix.det H * Matrix.det H.transpose := by
            rw [Matrix.det_transpose, sq]
      _ = Matrix.det (H * H.transpose) := (Matrix.det_mul H H.transpose).symm
      _ = Matrix.det (((2 ^ k : ℕ) : ℝ) • (1 : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℝ)) := by
            rw [hH_orth]
      _ = ((2 ^ k : ℕ) : ℝ) ^ (2 ^ k) := by
            rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  have hdet_ne : Matrix.det H ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hdet_sq
    have hpos : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) ^ (2 ^ k) := by positivity
    linarith
  have hperm : Matrix.permanent (Matrix.of fun i j => (H i j) ^ 2) = ((2 ^ k).factorial : ℝ) := by
    have hsq : (Matrix.of fun i j => (H i j) ^ 2) = Matrix.of fun _ _ => (1 : ℝ) := by
      ext i j
      simp only [Matrix.of_apply]
      rcases hH_ent i j with h1 | h1 <;> simp [h1]
    rw [hsq, permanent_all_ones]
  refine ⟨H, fun i j => ?_, hdet_ne, ?_⟩
  · rcases hH_ent i j with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inr h1)
  · rw [hperm, hdet_sq]
    ring

lemma dyadic_witness_strong : ∀ n : ℕ, 1 ≤ n →
    ∃ W : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, W i j = -1 ∨ W i j = 0 ∨ W i j = 1) ∧
      Matrix.det W ≠ 0 ∧
      (n : ℝ) ^ n * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) ≤
        (((if n = 2 ^ Nat.log2 n then 1 else (n + 1) ^ Nat.log2 n : ℕ)) : ℝ) *
          (n.factorial : ℝ) * (Matrix.det W) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    let k := Nat.log2 n
    let a := 2 ^ k
    have ha_le : a ≤ n := Nat.log2_self_le (by omega)
    have hn_lt : n < 2 ^ (k + 1) := (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self k)
    by_cases heq : n = a
    · rcases sylvester_witness k with ⟨H, hH_ent, hH_det, hH_eq⟩
      let e0 : Fin (2 ^ k) ≃ Fin n := finCongr heq.symm
      let H' : Matrix (Fin n) (Fin n) ℝ := H.reindex e0 e0
      have hH'_det : Matrix.det H' = Matrix.det H := by simp [H']
      have hH'_perm : Matrix.permanent (Matrix.of fun i j => (H' i j) ^ 2) =
          Matrix.permanent (Matrix.of fun i j => (H i j) ^ 2) := by
        have hsq : (Matrix.of fun i j => (H' i j) ^ 2) =
            (Matrix.of fun i j => (H i j) ^ 2).reindex e0 e0 := by
          ext i j; simp [H']
        rw [hsq, permanent_reindex_self]
      refine ⟨H', fun i j => hH_ent (e0.symm i) (e0.symm j), by rw [hH'_det]; exact hH_det, ?_⟩
      have hite : (if n = 2 ^ Nat.log2 n then 1 else (n + 1) ^ Nat.log2 n) = 1 :=
        ite_eq_left_iff.mpr (fun hc => absurd heq hc)
      rw [hite, Nat.cast_one, one_mul, hH'_perm, hH'_det, heq]
      exact hH_eq.le
    · let b := n - a
      have hb_pos : 1 ≤ b := by omega
      have hb_lt : b < n := by omega
      have hb_lt_a : b < 2 ^ k := by
        have : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
      have hlog_b : Nat.log2 b < k := (Nat.log2_lt (by omega)).mpr hb_lt_a
      rcases sylvester_witness k with ⟨A, hA_ent, hA_det, hA_eq⟩
      rcases ih b hb_lt hb_pos with ⟨B, hB_ent, hB_det, hB_le⟩
      have hab : a + b = n := by omega
      let e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr hab)
      let C : Matrix (Fin n) (Fin n) ℝ := (Matrix.fromBlocks A 0 0 B).reindex e e
      have hC_ent : ∀ i j, C i j = -1 ∨ C i j = 0 ∨ C i j = 1 := by
        intro i j
        simp only [C, Matrix.reindex_apply, Matrix.submatrix_apply]
        cases e.symm i with
        | inl i1 =>
          cases e.symm j with
          | inl j1 => exact hA_ent i1 j1
          | inr j2 => exact Or.inr (Or.inl rfl)
        | inr i2 =>
          cases e.symm j with
          | inl j1 => exact Or.inr (Or.inl rfl)
          | inr j2 => exact hB_ent i2 j2
      have hC_det : Matrix.det C = Matrix.det A * Matrix.det B := by
        simp only [C, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₁₂]
      have hC_det_ne : Matrix.det C ≠ 0 := by
        rw [hC_det]; exact mul_ne_zero hA_det hB_det
      have hC_perm : Matrix.permanent (Matrix.of fun i j => (C i j) ^ 2) =
          Matrix.permanent (Matrix.of fun i j => (A i j) ^ 2) *
            Matrix.permanent (Matrix.of fun i j => (B i j) ^ 2) := by
        have hsq : (Matrix.of fun i j => (C i j) ^ 2) =
            (Matrix.fromBlocks (Matrix.of fun i j => (A i j) ^ 2) 0 0
              (Matrix.of fun i j => (B i j) ^ 2)).reindex e e := by
          ext i j
          simp only [C, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
          cases e.symm i <;> cases e.symm j <;> simp
        rw [hsq, permanent_reindex_self, permanent_fromBlocks_zero]
      have hB_le' : (b : ℝ) ^ b * Matrix.permanent (Matrix.of fun i j => (B i j) ^ 2) ≤
          (((b + 1 : ℕ) : ℝ) ^ Nat.log2 b) * (b.factorial : ℝ) * (Matrix.det B) ^ 2 := by
        refine le_trans hB_le ?_
        apply mul_le_mul_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right
          · split_ifs
            · exact_mod_cast (Nat.one_le_pow (Nat.log2 b) (b + 1) (by omega))
            · norm_cast
          · exact Nat.cast_nonneg _
        · exact sq_nonneg _
      have hfac_pos : (0 : ℝ) < (a.factorial : ℝ) * (b.factorial : ℝ) :=
        mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos a)) (Nat.cast_pos.mpr (Nat.factorial_pos b))
      have hbin : ((a + b : ℕ) : ℝ) ^ (a + b) * ((a.factorial : ℝ) * (b.factorial : ℝ)) ≤
          ((a + b + 1 : ℕ) : ℝ) * ((a + b).factorial : ℝ) * ((a : ℝ) ^ a * (b : ℝ) ^ b) := by
        exact_mod_cast binom_max_term a b
      rw [hab] at hbin
      have hPA_nn : (0 : ℝ) ≤ Matrix.permanent (Matrix.of fun i j => (A i j) ^ 2) := by
        unfold Matrix.permanent
        exact Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      have hPB_nn : (0 : ℝ) ≤ Matrix.permanent (Matrix.of fun i j => (B i j) ^ 2) := by
        unfold Matrix.permanent
        exact Finset.sum_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))
      have hstep : ((n : ℝ) ^ n * Matrix.permanent (Matrix.of fun i j => (C i j) ^ 2)) *
          ((a.factorial : ℝ) * (b.factorial : ℝ)) ≤
          (((n + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) ^ Nat.log2 b * (n.factorial : ℝ) *
            (Matrix.det C) ^ 2) * ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
        calc ((n : ℝ) ^ n * Matrix.permanent (Matrix.of fun i j => (C i j) ^ 2)) *
              ((a.factorial : ℝ) * (b.factorial : ℝ))
            = ((n : ℝ) ^ n * ((a.factorial : ℝ) * (b.factorial : ℝ))) *
                (Matrix.permanent (Matrix.of fun i j => (A i j) ^ 2) *
                  Matrix.permanent (Matrix.of fun i j => (B i j) ^ 2)) := by rw [hC_perm]; ring
          _ ≤ (((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) * ((a : ℝ) ^ a * (b : ℝ) ^ b)) *
                (Matrix.permanent (Matrix.of fun i j => (A i j) ^ 2) *
                  Matrix.permanent (Matrix.of fun i j => (B i j) ^ 2)) :=
                mul_le_mul_of_nonneg_right hbin (mul_nonneg hPA_nn hPB_nn)
          _ = ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) *
                (((a : ℝ) ^ a * Matrix.permanent (Matrix.of fun i j => (A i j) ^ 2)) *
                  ((b : ℝ) ^ b * Matrix.permanent (Matrix.of fun i j => (B i j) ^ 2))) := by ring
          _ ≤ ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) *
                (((a.factorial : ℝ) * (Matrix.det A) ^ 2) *
                  (((b + 1 : ℕ) : ℝ) ^ Nat.log2 b * (b.factorial : ℝ) * (Matrix.det B) ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                rw [hA_eq]
                exact mul_le_mul_of_nonneg_left hB_le' (by positivity)
          _ = (((n + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) ^ Nat.log2 b * (n.factorial : ℝ) *
                (Matrix.det C) ^ 2) * ((a.factorial : ℝ) * (b.factorial : ℝ)) := by
                rw [hC_det]; ring
      have hcancel := le_of_mul_le_mul_right hstep hfac_pos
      have hpow_le : ((n + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) ^ Nat.log2 b ≤
          (((n + 1) ^ k : ℕ) : ℝ) := by
        have hnat : (n + 1) * (b + 1) ^ Nat.log2 b ≤ (n + 1) ^ k := by
          calc (n + 1) * (b + 1) ^ Nat.log2 b
              ≤ (n + 1) * (n + 1) ^ Nat.log2 b :=
                Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
            _ = (n + 1) ^ (Nat.log2 b + 1) := by rw [pow_succ']
            _ ≤ (n + 1) ^ k := Nat.pow_le_pow_right (by omega) hlog_b
        exact_mod_cast hnat
      refine ⟨C, hC_ent, hC_det_ne, ?_⟩
      have hite : (if n = 2 ^ Nat.log2 n then 1 else (n + 1) ^ Nat.log2 n) = (n + 1) ^ k :=
        ite_eq_right_iff.mpr (fun hc => absurd hc heq)
      rw [hite]
      refine le_trans hcancel ?_
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right hpow_le (Nat.cast_nonneg _)

lemma dyadic_witness (n : ℕ) (hn : 1 ≤ n) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, W i j = -1 ∨ W i j = 0 ∨ W i j = 1) ∧
      Matrix.det W ≠ 0 ∧
      (n : ℝ) ^ n * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) ≤
        (((if n = 2 ^ Nat.log2 n then 1 else (n + 1) ^ (Nat.log2 n + 1) : ℕ)) : ℝ) *
          (n.factorial : ℝ) * (Matrix.det W) ^ 2 := by
  rcases dyadic_witness_strong n hn with ⟨W, hW_ent, hW_det, hW_le⟩
  refine ⟨W, hW_ent, hW_det, le_trans hW_le ?_⟩
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  split_ifs
  · exact le_rfl
  · exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (Nat.le_succ (Nat.log2 n))

/-! ### Real Orthogonal Witness (Clauses 1 and 2, zero extra imports) -/

lemma sum_inv_factorial_le_three : ∀ N : ℕ,
    ∑ j ∈ Finset.range (N + 1), (1 / (j.factorial : ℝ)) ≤ 3 := by
  have hstrong : ∀ N : ℕ, 1 ≤ N →
      ∑ j ∈ Finset.range (N + 1), (1 / (j.factorial : ℝ)) ≤ 3 - (1 / 2 : ℝ) ^ (N - 1) := by
    intro N hN
    induction N with
    | zero => omega
    | succ N ih =>
      rcases eq_or_lt_of_le (Nat.zero_le N) with rfl | hNpos
      · norm_num [Finset.sum_range_succ]
      · have ih' := ih hNpos
        rw [Finset.sum_range_succ]
        have hpow_fac : (2 : ℕ) ^ N ≤ (N + 1).factorial := by
          clear ih ih' hN hNpos
          induction N with
          | zero => simp
          | succ m ihm =>
            rw [pow_succ, Nat.factorial_succ]
            have h2 : 2 ≤ m + 2 := by omega
            have := Nat.mul_le_mul h2 ihm
            linarith
        have hinv : (1 / ((N + 1).factorial : ℝ)) ≤ (1 / 2 : ℝ) ^ N := by
          rw [one_div_pow]
          exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hpow_fac)
        have hsub : (1 / 2 : ℝ) ^ (N - 1) = (1 / 2 : ℝ) ^ N + (1 / 2 : ℝ) ^ N := by
          have hN1 : N = (N - 1) + 1 := by omega
          conv_rhs => rw [hN1, pow_succ]
          ring
        have hNsub : N + 1 - 1 = N := by omega
        rw [hNsub]
        linarith
  intro N
  rcases eq_or_lt_of_le (Nat.zero_le N) with rfl | hpos
  · norm_num
  · have h := hstrong N hpos
    have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (N - 1) := by positivity
    linarith

lemma succ_pow_le_three_mul_pow (k : ℕ) (hk : 1 ≤ k) :
    ((k + 1 : ℕ) : ℝ) ^ k ≤ 3 * (k : ℝ) ^ k := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
  have hexp : ((k + 1 : ℕ) : ℝ) ^ k =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (k : ℝ) ^ (k - j) := by
    rw [Nat.cast_add, Nat.cast_one, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp [mul_comm]
  rw [hexp]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (k.choose j : ℝ) * (k : ℝ) ^ (k - j) ≤ (k : ℝ) ^ k * (1 / (j.factorial : ℝ)) := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hdesc : k.choose j * j.factorial ≤ k ^ j := by
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
      exact Nat.descFactorial_le_pow k j
    have hdescR : (k.choose j : ℝ) * (j.factorial : ℝ) ≤ (k : ℝ) ^ j := by
      exact_mod_cast hdesc
    have hfac_pos : (0 : ℝ) < (j.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos j)
    have hmul : (k.choose j : ℝ) * (k : ℝ) ^ (k - j) * (j.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      calc (k.choose j : ℝ) * (k : ℝ) ^ (k - j) * (j.factorial : ℝ)
          = ((k.choose j : ℝ) * (j.factorial : ℝ)) * (k : ℝ) ^ (k - j) := by ring
        _ ≤ (k : ℝ) ^ j * (k : ℝ) ^ (k - j) :=
            mul_le_mul_of_nonneg_right hdescR (by positivity)
        _ = (k : ℝ) ^ (j + (k - j)) := (pow_add _ _ _).symm
        _ = (k : ℝ) ^ k := by rw [Nat.add_sub_of_le hjk]
    rw [mul_one_div, le_div_iff₀ hfac_pos]
    exact hmul
  calc (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (k : ℝ) ^ (k - j))
      ≤ ∑ j ∈ Finset.range (k + 1), (k : ℝ) ^ k * (1 / (j.factorial : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = (k : ℝ) ^ k * ∑ j ∈ Finset.range (k + 1), (1 / (j.factorial : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ (k : ℝ) ^ k * 3 :=
        mul_le_mul_of_nonneg_left (sum_inv_factorial_le_three k) (by positivity)
    _ = 3 * (k : ℝ) ^ k := by ring

lemma perm_pair_bound {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (m : ℕ) (S : Finset α), S.card = 2 * m →
    ∀ (u v : Fin m → α → ℝ),
      (∀ j c, 0 ≤ u j c) → (∀ j c, 0 ≤ v j c) → (∀ j c, u j c + v j c = 1) →
      (∑ f ∈ (Finset.univ : Finset (Fin m × Bool → α)).filter
          (fun f => Function.Injective f ∧ ∀ x, f x ∈ S),
        ∏ j : Fin m, u j (f (j, false)) * v j (f (j, true))) ≤ (m.factorial : ℝ) ^ 2 := by
  intro m
  induction m with
  | zero =>
    intro S _ u v _ _ _
    have hcard : ((Finset.univ : Finset (Fin 0 × Bool → α)).filter
        (fun f => Function.Injective f ∧ ∀ x, f x ∈ S)).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro f _ g _
      funext x
      exact Fin.elim0 x.1
    have hsum : (∑ f ∈ (Finset.univ : Finset (Fin 0 × Bool → α)).filter
        (fun f => Function.Injective f ∧ ∀ x, f x ∈ S),
        ∏ j : Fin 0, u j (f (j, false)) * v j (f (j, true))) =
        (((Finset.univ : Finset (Fin 0 × Bool → α)).filter
          (fun f => Function.Injective f ∧ ∀ x, f x ∈ S)).card : ℝ) := by
      simp
    rw [hsum]
    have : (((Finset.univ : Finset (Fin 0 × Bool → α)).filter
        (fun f => Function.Injective f ∧ ∀ x, f x ∈ S)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    simpa using this
  | succ m ih =>
    intro S hS u v hu hv huv
    let F : Finset (Fin (m + 1) × Bool → α) :=
      Finset.univ.filter (fun f => Function.Injective f ∧ ∀ x, f x ∈ S)
    let pairs : Finset (Σ _ : α, α) := S.sigma (fun c₁ => S.erase c₁)
    let subF (p : Σ _ : α, α) : Finset (Fin m × Bool → α) :=
      Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ (S.erase p.1).erase p.2)
    let T : Finset (Σ p : (Σ _ : α, α), (Fin m × Bool → α)) := pairs.sigma subF
    let extFun (c₁ c₂ : α) (g : Fin m × Bool → α) : Fin (m + 1) × Bool → α :=
      fun x => Fin.lastCases (if x.2 then c₂ else c₁) (fun j => g (j, x.2)) x.1
    have hbij : (∑ f ∈ F, ∏ j : Fin (m + 1), u j (f (j, false)) * v j (f (j, true))) =
        ∑ q ∈ T, ∏ j : Fin (m + 1), u j (extFun q.1.1 q.1.2 q.2 (j, false)) *
          v j (extFun q.1.1 q.1.2 q.2 (j, true)) := by
      symm
      refine Finset.sum_bij (fun q _ => extFun q.1.1 q.1.2 q.2) ?_ ?_ ?_ ?_
      · intro q hq
        simp only [T, pairs, subF, Finset.mem_sigma, Finset.mem_erase, Finset.mem_filter,
          Finset.mem_univ, true_and] at hq
        rcases hq with ⟨⟨hc₁S, hc₂ne, hc₂S⟩, hg_inj, hg_mem⟩
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro x y hxy
          rcases x with ⟨i, b₁⟩
          rcases y with ⟨j, b₂⟩
          induction i using Fin.lastCases with
          | last =>
            induction j using Fin.lastCases with
            | last =>
              simp only [extFun, Fin.lastCases_last] at hxy
              cases b₁ <;> cases b₂ <;> simp at hxy
              · rfl
              · exact absurd hxy.symm hc₂ne
              · exact absurd hxy hc₂ne
              · rfl
            | cast j' =>
              simp only [extFun, Fin.lastCases_last, Fin.lastCases_castSucc] at hxy
              have hmem := hg_mem (j', b₂)
              cases b₁
              · exact absurd hxy.symm hmem.2.1
              · exact absurd hxy.symm hmem.1
          | cast i' =>
            induction j using Fin.lastCases with
            | last =>
              simp only [extFun, Fin.lastCases_last, Fin.lastCases_castSucc] at hxy
              have hmem := hg_mem (i', b₁)
              cases b₂
              · exact absurd hxy hmem.2.1
              · exact absurd hxy hmem.1
            | cast j' =>
              simp only [extFun, Fin.lastCases_castSucc] at hxy
              have := hg_inj hxy
              cases this
              rfl
        · intro x
          rcases x with ⟨i, b⟩
          refine Fin.lastCases ?_ ?_ i
          · simp only [extFun, Fin.lastCases_last]
            cases b <;> simp [hc₁S, hc₂S]
          · intro j'
            simp only [extFun, Fin.lastCases_castSucc]
            exact (hg_mem (j', b)).2.2
      · intro q₁ _ q₂ _ h
        rcases q₁ with ⟨⟨c₁, c₂⟩, g₁⟩
        rcases q₂ with ⟨⟨d₁, d₂⟩, g₂⟩
        have h1 : c₁ = d₁ := by
          have := congrFun h (Fin.last m, false)
          simpa [extFun] using this
        have h2 : c₂ = d₂ := by
          have := congrFun h (Fin.last m, true)
          simpa [extFun] using this
        have h3 : g₁ = g₂ := by
          funext x
          have := congrFun h (x.1.castSucc, x.2)
          simpa [extFun] using this
        subst h1; subst h2; subst h3; rfl
      · intro f hf
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        rcases hf with ⟨hf_inj, hf_mem⟩
        let c₁ := f (Fin.last m, false)
        let c₂ := f (Fin.last m, true)
        let g : Fin m × Bool → α := fun x => f (x.1.castSucc, x.2)
        refine ⟨⟨⟨c₁, c₂⟩, g⟩, ?_, ?_⟩
        · simp only [T, pairs, subF, Finset.mem_sigma, Finset.mem_erase, Finset.mem_filter,
            Finset.mem_univ, true_and]
          refine ⟨⟨hf_mem _, ?_, hf_mem _⟩, ?_, ?_⟩
          · intro heq
            have := hf_inj heq
            simp at this
          · intro x y hxy
            have hpair := Prod.mk.inj (hf_inj hxy)
            exact Prod.ext (Fin.castSucc_injective m hpair.1) hpair.2
          · intro x
            refine ⟨?_, ?_, hf_mem _⟩
            · intro heq
              have := congrArg Prod.fst (hf_inj heq)
              exact Fin.castSucc_ne_last x.1 this
            · intro heq
              have := congrArg Prod.fst (hf_inj heq)
              exact Fin.castSucc_ne_last x.1 this
        · funext x
          rcases x with ⟨i, b⟩
          refine Fin.lastCases ?_ ?_ i
          · cases b <;> simp [extFun, c₁, c₂]
          · intro j'
            simp [extFun, g]
      · intro q _
        rfl
    rw [hbij]
    rw [Finset.sum_sigma]
    have hsplit : ∀ p ∈ pairs,
        (∑ g ∈ subF p, ∏ j : Fin (m + 1),
          u j (extFun p.1 p.2 g (j, false)) * v j (extFun p.1 p.2 g (j, true))) ≤
        (u (Fin.last m) p.1 * v (Fin.last m) p.2) * (m.factorial : ℝ) ^ 2 := by
      intro p hp
      simp only [pairs, Finset.mem_sigma, Finset.mem_erase] at hp
      rcases hp with ⟨hc₁S, hc₂ne, hc₂S⟩
      have hcard' : ((S.erase p.1).erase p.2).card = 2 * m := by
        have h1 : (S.erase p.1).card = S.card - 1 := Finset.card_erase_of_mem hc₁S
        have hp2 : p.2 ∈ S.erase p.1 := Finset.mem_erase.mpr ⟨hc₂ne, hc₂S⟩
        have h2 : ((S.erase p.1).erase p.2).card = (S.erase p.1).card - 1 :=
          Finset.card_erase_of_mem hp2
        omega
      have hterm : ∀ g ∈ subF p,
          (∏ j : Fin (m + 1), u j (extFun p.1 p.2 g (j, false)) *
            v j (extFun p.1 p.2 g (j, true))) =
          (u (Fin.last m) p.1 * v (Fin.last m) p.2) *
            (∏ j : Fin m, u j.castSucc (g (j, false)) * v j.castSucc (g (j, true))) := by
        intro g _
        rw [Fin.prod_univ_castSucc]
        simp only [extFun, Fin.lastCases_last, Fin.lastCases_castSucc, Bool.false_eq_true,
          ↓reduceIte]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hu _ _) (hv _ _))
      exact ih ((S.erase p.1).erase p.2) hcard' (fun j => u j.castSucc) (fun j => v j.castSucc)
        (fun j c => hu j.castSucc c) (fun j c => hv j.castSucc c) (fun j c => huv j.castSucc c)
    have hsum1 : (∑ p ∈ pairs, ∑ g ∈ subF p,
        ∏ j : Fin (m + 1), u j (extFun p.1 p.2 g (j, false)) *
          v j (extFun p.1 p.2 g (j, true))) ≤
        (∑ p ∈ pairs, u (Fin.last m) p.1 * v (Fin.last m) p.2) * (m.factorial : ℝ) ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hsplit
    have hpair_le : (∑ p ∈ pairs, u (Fin.last m) p.1 * v (Fin.last m) p.2) ≤
        ((m + 1 : ℕ) : ℝ) ^ 2 := by
      have h1 : (∑ p ∈ pairs, u (Fin.last m) p.1 * v (Fin.last m) p.2) =
          ∑ c₁ ∈ S, ∑ c₂ ∈ S.erase c₁, u (Fin.last m) c₁ * v (Fin.last m) c₂ := by
        rw [Finset.sum_sigma]
      rw [h1]
      have h2 : (∑ c₁ ∈ S, ∑ c₂ ∈ S.erase c₁, u (Fin.last m) c₁ * v (Fin.last m) c₂) ≤
          ∑ c₁ ∈ S, ∑ c₂ ∈ S, u (Fin.last m) c₁ * v (Fin.last m) c₂ := by
        apply Finset.sum_le_sum
        intro c₁ _
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset c₁ S)
          (fun c₂ _ _ => mul_nonneg (hu _ _) (hv _ _))
      have h3 : (∑ c₁ ∈ S, ∑ c₂ ∈ S, u (Fin.last m) c₁ * v (Fin.last m) c₂) =
          (∑ c₁ ∈ S, u (Fin.last m) c₁) * (∑ c₂ ∈ S, v (Fin.last m) c₂) := by
        rw [Finset.sum_mul_sum]
      have hUV : (∑ c ∈ S, u (Fin.last m) c) + (∑ c ∈ S, v (Fin.last m) c) =
          2 * ((m + 1 : ℕ) : ℝ) := by
        rw [← Finset.sum_add_distrib]
        have : ∀ c ∈ S, u (Fin.last m) c + v (Fin.last m) c = 1 := fun c _ => huv _ c
        rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one, hS]
        push_cast; ring
      have hamgm : (∑ c₁ ∈ S, u (Fin.last m) c₁) * (∑ c₂ ∈ S, v (Fin.last m) c₂) ≤
          ((m + 1 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((∑ c ∈ S, u (Fin.last m) c) - (∑ c ∈ S, v (Fin.last m) c))]
      linarith
    calc (∑ p ∈ pairs, ∑ g ∈ subF p, ∏ j : Fin (m + 1),
            u j (extFun p.1 p.2 g (j, false)) * v j (extFun p.1 p.2 g (j, true)))
        ≤ (∑ p ∈ pairs, u (Fin.last m) p.1 * v (Fin.last m) p.2) * (m.factorial : ℝ) ^ 2 := hsum1
      _ ≤ ((m + 1 : ℕ) : ℝ) ^ 2 * (m.factorial : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hpair_le (sq_nonneg _)
      _ = ((m + 1).factorial : ℝ) ^ 2 := by
          rw [Nat.factorial_succ, Nat.cast_mul]; ring

lemma permanent_pair_matrix_le {m : ℕ} (A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ)
    (hnn : ∀ r c, 0 ≤ A r c)
    (hsum : ∀ (j : Fin m) (c : Fin m × Bool), A (j, false) c + A (j, true) c = 1) :
    A.permanent ≤ (m.factorial : ℝ) ^ 2 := by
  rw [permanent_eq_row_perm]
  let F : Finset (Fin m × Bool → Fin m × Bool) :=
    Finset.univ.filter (fun f => Function.Injective f ∧ ∀ x, f x ∈ (Finset.univ : Finset (Fin m × Bool)))
  have hbij : (∑ σ : Equiv.Perm (Fin m × Bool), ∏ x : Fin m × Bool, A x (σ x)) =
      ∑ f ∈ F, ∏ j : Fin m, A (j, false) (f (j, false)) * A (j, true) (f (j, true)) := by
    refine Finset.sum_nbij (fun σ : Equiv.Perm (Fin m × Bool) => (σ : Fin m × Bool → Fin m × Bool)) ?_ ?_ ?_ ?_
    · intro σ _
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨σ.injective, fun _ => trivial⟩
    · intro σ₁ _ σ₂ _ h
      exact Equiv.ext (congrFun h)
    · intro f hf
      rw [Finset.mem_coe, Finset.mem_filter] at hf
      exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf.2.1),
        Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
    · intro σ _
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro j _
      simp [mul_comm]
  rw [hbij]
  have hcard : (Finset.univ : Finset (Fin m × Bool)).card = 2 * m := by
    simp [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, mul_comm]
  exact perm_pair_bound m Finset.univ hcard
    (fun j c => A (j, false) c) (fun j c => A (j, true) c)
    (fun j c => hnn (j, false) c) (fun j c => hnn (j, true) c) hsum

/-! ### Algebraic Primitive Root of Unity in ℂ (via unit semicircle + sSup, zero trig imports) -/

lemma complex_normSq_pow (z : ℂ) (k : ℕ) :
    Complex.normSq (z ^ k) = (Complex.normSq z) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Complex.normSq_mul, ih]

lemma complex_mul_star_eq_one {z : ℂ} (hz : Complex.normSq z = 1) :
    z * star z = 1 := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.one_re]
    have h : z.re * z.re + z.im * z.im = 1 := by simpa [Complex.normSq_apply] using hz
    linarith
  · simp [Complex.mul_im, mul_comm]

lemma complex_sum_geom_eq_zero {z : ℂ} {m : ℕ} (hz1 : z ≠ 1) (hzm : z ^ m = 1) :
    (∑ k ∈ Finset.range m, z ^ k) = 0 := by
  have hmul : ∀ n : ℕ, (z - 1) * (∑ k ∈ Finset.range n, z ^ k) = z ^ n - 1 := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hm := hmul m
  rw [hzm, sub_self] at hm
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hz1)

noncomputable def circlePath (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

lemma circlePath_normSq (t : ℝ) : Complex.normSq (circlePath t) = 1 := by
  have hden : 1 + t ^ 2 ≠ 0 := by positivity
  simp only [circlePath, Complex.normSq_apply]
  field_simp [hden]
  ring

lemma circlePath_continuous : Continuous circlePath := by
  have hden : ∀ t : ℝ, 1 + t ^ 2 ≠ 0 := fun t => by positivity
  have hre : Continuous (fun t : ℝ => (1 - t ^ 2) / (1 + t ^ 2)) :=
    (continuous_const.sub (continuous_id.pow 2)).div
      (continuous_const.add (continuous_id.pow 2)) hden
  have him : Continuous (fun t : ℝ => 2 * t / (1 + t ^ 2)) :=
    (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) hden
  have hpath : circlePath = fun t =>
      (((1 - t ^ 2) / (1 + t ^ 2) : ℝ) : ℂ) + (((2 * t / (1 + t ^ 2) : ℝ) : ℂ) * Complex.I) := by
    funext t
    apply Complex.ext <;>
      simp only [circlePath, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] <;> ring
  rw [hpath]
  exact (Complex.continuous_ofReal.comp hre).add
    ((Complex.continuous_ofReal.comp him).mul continuous_const)

lemma exists_prim_root (m : ℕ) (hm : 1 ≤ m) :
    ∃ ζ : ℂ, Complex.normSq ζ = 1 ∧ ζ ^ m = 1 ∧ ∀ d : ℕ, 1 ≤ d → d < m → ζ ^ d ≠ 1 := by
  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨1, by simp, by simp, fun d h1 h2 => by omega⟩
  by_cases hm2 : m = 2
  · subst hm2
    refine ⟨-1, by simp, by norm_num, fun d h1 h2 => ?_⟩
    have hd : d = 1 := by omega
    subst hd
    norm_num
  have hm3 : 3 ≤ m := by omega
  let A : Set ℝ :=
    {t : ℝ | 0 ≤ t ∧ ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ k : ℕ, 1 ≤ k → k ≤ m → 0 ≤ ((circlePath s) ^ k).im}
  have h0A : (0 : ℝ) ∈ A := by
    refine ⟨le_rfl, fun s hs k _ _ => ?_⟩
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    have hc0 : circlePath 0 = 1 := by
      apply Complex.ext <;> simp [circlePath]
    simp [hc0]
  have hbdd : BddAbove A := by
    refine ⟨1, fun t ht => ?_⟩
    by_contra hgt
    push Not at hgt
    have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨by norm_num, hgt.le⟩
    have hc1 : circlePath 1 = Complex.I := by
      apply Complex.ext <;> norm_num [circlePath]
    have h3 := ht.2 1 h1mem 3 (by omega) hm3
    rw [hc1] at h3
    have hI3 : (Complex.I ^ 3).im = -1 := by
      have : Complex.I ^ 3 = -Complex.I := by
        calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
          _ = -1 * Complex.I := by rw [Complex.I_sq]
          _ = -Complex.I := by ring
      rw [this]
      simp
    linarith
  rcases Real.exists_isLUB ⟨0, h0A⟩ hbdd with ⟨t₀, ht₀⟩
  have hepsA : (1 / (4 * (m : ℝ))) ∈ A := by
    have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
    refine ⟨by positivity, fun s hs k hk1 hkm => ?_⟩
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 / (4 * (m : ℝ)) := hs.2
    have hden_ge : 1 ≤ 1 + s ^ 2 := by nlinarith
    have hden_pos : 0 < 1 + s ^ 2 := by linarith
    have hs_le1 : s ≤ 1 / 4 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have : 4 ≤ 4 * (m : ℝ) := by linarith
      exact le_trans hs1 (one_div_le_one_div_of_le (by norm_num) this)
    let x := (circlePath s).re
    let y := (circlePath s).im
    have hy0 : 0 ≤ y := by
      simp only [y, circlePath]; positivity
    have hy_le : y ≤ 2 * s := by
      simp only [y, circlePath]
      rw [div_le_iff₀ hden_pos]
      nlinarith
    have h1mx_nn : 0 ≤ 1 - x := by
      simp only [x, circlePath]
      rw [sub_nonneg, div_le_one hden_pos]
      nlinarith
    have h1mx_le : 1 - x ≤ s := by
      simp only [x, circlePath]
      have heq : 1 - (1 - s ^ 2) / (1 + s ^ 2) = 2 * s ^ 2 / (1 + s ^ 2) := by
        field_simp [hden_pos.ne']; ring
      rw [heq, div_le_iff₀ hden_pos]
      nlinarith
    have hre_ge : ∀ j ≤ m, 1 - (j : ℝ) * (3 * s) ≤ ((circlePath s) ^ j).re := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ihj =>
        intro hj
        have hprev := ihj (by omega)
        have hnsq : Complex.normSq ((circlePath s) ^ j) = 1 := by
          rw [complex_normSq_pow, circlePath_normSq, one_pow]
        have ha_le : ((circlePath s) ^ j).re ≤ 1 := by
          have : ((circlePath s) ^ j).re ^ 2 ≤ 1 := by
            have := Complex.normSq_apply ((circlePath s) ^ j)
            nlinarith
          nlinarith
        have hb_le : ((circlePath s) ^ j).im ≤ 1 := by
          have : ((circlePath s) ^ j).im ^ 2 ≤ 1 := by
            have := Complex.normSq_apply ((circlePath s) ^ j)
            nlinarith
          nlinarith
        have hstep : ((circlePath s) ^ (j + 1)).re =
            ((circlePath s) ^ j).re * x - ((circlePath s) ^ j).im * y := by
          rw [pow_succ, Complex.mul_re]
        rw [hstep]
        have h1 : ((circlePath s) ^ j).re * (1 - x) ≤ 1 - x := by nlinarith
        have h2 : ((circlePath s) ^ j).im * y ≤ y := by nlinarith
        push_cast
        nlinarith
    have hre_pos : ∀ j ≤ m, 0 ≤ ((circlePath s) ^ j).re := by
      intro j hj
      have h1 := hre_ge j hj
      have hj_le : (j : ℝ) ≤ (m : ℝ) := by exact_mod_cast hj
      have hms : (m : ℝ) * s ≤ 1 / 4 := by
        have := mul_le_mul_of_nonneg_left hs1 hm_pos.le
        have hmul : (m : ℝ) * (1 / (4 * (m : ℝ))) = 1 / 4 := by field_simp [hm_pos.ne']
        linarith
      nlinarith
    have hx0 : 0 ≤ x := by
      have := hre_pos 1 (by omega)
      simpa [x] using this
    have him_nn : ∀ j ≤ m, 0 ≤ ((circlePath s) ^ j).im := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ihj =>
        intro hj
        have hb := ihj (by omega)
        have ha := hre_pos j (by omega)
        rw [pow_succ, Complex.mul_im]
        exact add_nonneg (mul_nonneg ha hy0) (mul_nonneg hb hx0)
    exact him_nn k hkm
  have ht₀_pos : 0 < t₀ := lt_of_lt_of_le (by positivity) (ht₀.1 hepsA)
  have ht₀_A : t₀ ∈ A := by
    refine ⟨ht₀_pos.le, fun s hs k hk1 hkm => ?_⟩
    by_cases hlt : s < t₀
    · have hex : ∃ a ∈ A, s < a := by
        by_contra hno
        push Not at hno
        have : t₀ ≤ s := ht₀.2 hno
        linarith
      rcases hex with ⟨a, haA, hsa⟩
      exact haA.2 s ⟨hs.1, hsa.le⟩ k hk1 hkm
    · have hst : s = t₀ := le_antisymm hs.2 (le_of_not_gt hlt)
      subst s
      by_contra hneg
      push Not at hneg
      let f : ℝ → ℝ := fun u => ((circlePath u) ^ k).im
      have hf_cont : Continuous f :=
        Complex.continuous_im.comp ((continuous_pow k).comp circlePath_continuous)
      rcases Metric.continuous_iff.mp hf_cont t₀ (-f t₀) (by linarith) with ⟨δ, hδ_pos, hδ⟩
      have hlt_t₀ : t₀ - δ < t₀ := by linarith
      have hex : ∃ a ∈ A, t₀ - δ < a := by
        by_contra hno
        push Not at hno
        have : t₀ ≤ t₀ - δ := ht₀.2 hno
        linarith
      rcases hex with ⟨a, haA, hda⟩
      have hat₀ : a ≤ t₀ := ht₀.1 haA
      have hdist : dist a t₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith
      have hfa := hδ a hdist
      rw [Real.dist_eq, abs_lt] at hfa
      have hfa_nn : 0 ≤ f a := haA.2 a ⟨haA.1, le_rfl⟩ k hk1 hkm
      linarith
  have hc_im_pos : 0 < (circlePath t₀).im := by
    simp only [circlePath]
    positivity
  have hnot_one : ∀ k : ℕ, 1 ≤ k → k ≤ m → (circlePath t₀) ^ k ≠ 1 := by
    intro k hk1 hkm heq
    by_cases hk1' : k = 1
    · subst hk1'
      simp only [pow_one] at heq
      have := congrArg Complex.im heq
      simp at this
      linarith
    · have hkm1_ge : 1 ≤ k - 1 := by omega
      have hkm1_le : k - 1 ≤ m := by omega
      have hmul : (circlePath t₀) ^ (k - 1) * circlePath t₀ = 1 := by
        rw [← pow_succ, show k - 1 + 1 = k by omega, heq]
      have hst : (circlePath t₀) ^ (k - 1) = star (circlePath t₀) := by
        have hinv := complex_mul_star_eq_one (circlePath_normSq t₀)
        calc (circlePath t₀) ^ (k - 1)
            = (circlePath t₀) ^ (k - 1) * (circlePath t₀ * star (circlePath t₀)) := by
                rw [hinv, mul_one]
          _ = ((circlePath t₀) ^ (k - 1) * circlePath t₀) * star (circlePath t₀) := by ring
          _ = star (circlePath t₀) := by rw [hmul, one_mul]
      have him_neg : ((circlePath t₀) ^ (k - 1)).im < 0 := by
        rw [hst]
        simp only [Complex.star_def, Complex.conj_im]
        linarith
      have him_nn := ht₀_A.2 t₀ ⟨ht₀_pos.le, le_rfl⟩ (k - 1) hkm1_ge hkm1_le
      linarith
  have hstrict : ∀ k : ℕ, 1 ≤ k → k < m → 0 < ((circlePath t₀) ^ k).im := by
    intro k hk1 hkm
    have hnn := ht₀_A.2 t₀ ⟨ht₀_pos.le, le_rfl⟩ k hk1 hkm.le
    rcases lt_or_eq_of_le hnn with hpos | hzero
    · exact hpos
    · exfalso
      have hnsq : Complex.normSq ((circlePath t₀) ^ k) = 1 := by
        rw [complex_normSq_pow, circlePath_normSq, one_pow]
      have hre_sq : ((circlePath t₀) ^ k).re ^ 2 = 1 := by
        have := Complex.normSq_apply ((circlePath t₀) ^ k)
        rw [← hzero] at this
        nlinarith
      have hre_cases : ((circlePath t₀) ^ k).re = 1 ∨ ((circlePath t₀) ^ k).re = -1 := by
        have : (((circlePath t₀) ^ k).re - 1) * (((circlePath t₀) ^ k).re + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp this with h1 | h2
        · left; linarith
        · right; linarith
      rcases hre_cases with h1 | hm1'
      · apply hnot_one k hk1 hkm.le
        apply Complex.ext
        · simpa using h1
        · simpa using hzero.symm
      · have hneg1 : (circlePath t₀) ^ k = -1 := by
          apply Complex.ext
          · simpa using hm1'
          · simpa using hzero.symm
        have hnext : ((circlePath t₀) ^ (k + 1)).im < 0 := by
          rw [pow_succ, hneg1, neg_one_mul, Complex.neg_im]
          linarith
        have hnext_nn := ht₀_A.2 t₀ ⟨ht₀_pos.le, le_rfl⟩ (k + 1) (by omega) (by omega)
        linarith
  have hm_im_zero : ((circlePath t₀) ^ m).im = 0 := by
    have hnn := ht₀_A.2 t₀ ⟨ht₀_pos.le, le_rfl⟩ m (by omega) le_rfl
    rcases lt_or_eq_of_le hnn with hpos | hzero
    · exfalso
      have hall_pos : ∀ k ∈ Finset.Icc 1 m, 0 < ((circlePath t₀) ^ k).im := by
        intro k hk
        rw [Finset.mem_Icc] at hk
        rcases eq_or_lt_of_le hk.2 with rfl | hlt
        · exact hpos
        · exact hstrict k hk.1 hlt
      have hex_delta : ∀ k ∈ Finset.Icc 1 m,
          ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, dist u t₀ < δ → 0 ≤ ((circlePath u) ^ k).im := by
        intro k hk
        have hk_pos := hall_pos k hk
        let f : ℝ → ℝ := fun u => ((circlePath u) ^ k).im
        have hf_cont : Continuous f :=
          Complex.continuous_im.comp ((continuous_pow k).comp circlePath_continuous)
        rcases Metric.continuous_iff.mp hf_cont t₀ (f t₀) hk_pos with ⟨δ, hδ_pos, hδ⟩
        refine ⟨δ, hδ_pos, fun u hu => ?_⟩
        have hdu := hδ u hu
        rw [Real.dist_eq, abs_lt] at hdu
        linarith
      choose δ_fn hδ_spec using hex_delta
      let S_idx := Finset.Icc 1 m
      have hS_ne : S_idx.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hm⟩⟩
      have hImg_ne : (S_idx.attach.image (fun x => δ_fn x.1 x.2)).Nonempty :=
        Finset.Nonempty.image (Finset.Nonempty.attach hS_ne) _
      let δ₀ := (S_idx.attach.image (fun x => δ_fn x.1 x.2)).min' hImg_ne
      have hδ₀_pos : 0 < δ₀ := by
        have hmem := Finset.min'_mem (S_idx.attach.image (fun x => δ_fn x.1 x.2)) hImg_ne
        rcases Finset.mem_image.mp hmem with ⟨x, _, hx⟩
        dsimp only [δ₀]
        rw [← hx]
        exact (hδ_spec x.1 x.2).1
      have hδ₀_le : ∀ k (hk : k ∈ S_idx), δ₀ ≤ δ_fn k hk := fun k hk =>
        Finset.min'_le _ _ (Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_attach _ _, rfl⟩)
      have hstepA : t₀ + δ₀ / 2 ∈ A := by
        refine ⟨by linarith, fun s hs k hk1 hkm => ?_⟩
        by_cases hst : s ≤ t₀
        · exact ht₀_A.2 s ⟨hs.1, hst⟩ k hk1 hkm
        · have hkS : k ∈ S_idx := Finset.mem_Icc.mpr ⟨hk1, hkm⟩
          have hdist : dist s t₀ < δ_fn k hkS := by
            have hle := hδ₀_le k hkS
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hs.2]
          exact (hδ_spec k hkS).2 s hdist
      have hle_t₀ := ht₀.1 hstepA
      linarith
    · exact hzero.symm
  have hwm : (circlePath t₀) ^ m = -1 := by
    have hnsq : Complex.normSq ((circlePath t₀) ^ m) = 1 := by
      rw [complex_normSq_pow, circlePath_normSq, one_pow]
    have hre_sq : ((circlePath t₀) ^ m).re ^ 2 = 1 := by
      have := Complex.normSq_apply ((circlePath t₀) ^ m)
      rw [hm_im_zero] at this
      nlinarith
    have hre_cases : ((circlePath t₀) ^ m).re = 1 ∨ ((circlePath t₀) ^ m).re = -1 := by
      have : (((circlePath t₀) ^ m).re - 1) * (((circlePath t₀) ^ m).re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h2
      · left; linarith
      · right; linarith
    rcases hre_cases with h1 | hm1'
    · exfalso
      apply hnot_one m (by omega) le_rfl
      apply Complex.ext
      · simpa using h1
      · simpa using hm_im_zero
    · apply Complex.ext
      · simpa using hm1'
      · simpa using hm_im_zero
  refine ⟨(circlePath t₀) ^ 2, ?_, ?_, ?_⟩
  · rw [complex_normSq_pow, circlePath_normSq, one_pow]
  · rw [← pow_mul, mul_comm, pow_mul, hwm]
    norm_num
  · intro d hd1 hdm hzd
    rw [← pow_mul, mul_comm, pow_mul] at hzd
    have hsq1 : ((circlePath t₀) ^ d - 1) * ((circlePath t₀) ^ d + 1) = 0 := by
      have : ((circlePath t₀) ^ d) ^ 2 = 1 := hzd
      linear_combination this
    rcases mul_eq_zero.mp hsq1 with h1 | h2
    · have h1' : (circlePath t₀) ^ d = 1 := sub_eq_zero.mp h1
      have him0 : ((circlePath t₀) ^ d).im = 0 := by rw [h1']; simp
      have hpos := hstrict d hd1 hdm
      linarith
    · have h2' : (circlePath t₀) ^ d = -1 := eq_neg_of_add_eq_zero_left h2
      have him0 : ((circlePath t₀) ^ d).im = 0 := by rw [h2']; simp
      have hpos := hstrict d hd1 hdm
      linarith

lemma real_witness_even (m : ℕ) (hm : 1 ≤ m) :
    ∃ Q : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ,
      Matrix.det Q ≠ 0 ∧
      ((2 * m : ℕ) : ℝ) ^ (2 * m) * Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2) ≤
        ((2 * m + 1 : ℕ) : ℝ) * ((2 * m).factorial : ℝ) * (Matrix.det Q) ^ 2 := by
  rcases exists_prim_root m hm with ⟨ζ, hζ_nsq, hζ_m, hζ_prim⟩
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
  let c : ℝ := (Real.sqrt (m : ℝ))⁻¹
  have hc_sq : c ^ 2 = (m : ℝ)⁻¹ := by
    simp only [c, inv_pow, Real.sq_sqrt hm_pos.le]
  let U : Fin m → Fin m → ℂ := fun j k => (c : ℂ) * ζ ^ ((j : ℕ) * (k : ℕ))
  have hU_orth : ∀ j₁ j₂ : Fin m,
      (∑ k : Fin m, U j₁ k * star (U j₂ k)) = if j₁ = j₂ then 1 else 0 := by
    intro j₁ j₂
    have hζ_star : ζ * star ζ = 1 := complex_mul_star_eq_one hζ_nsq
    have hterm : ∀ k : Fin m,
        U j₁ k * star (U j₂ k) = ((m : ℂ)⁻¹) * (ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (star ζ) ^ ((j₂ : ℕ) * (k : ℕ))) := by
      intro k
      simp only [U, star_mul, star_pow, Complex.star_def, Complex.conj_ofReal]
      have hcc : (c : ℂ) * (c : ℂ) = (m : ℂ)⁻¹ := by
        rw [← Complex.ofReal_mul, ← sq, hc_sq, Complex.ofReal_inv, Complex.ofReal_natCast]
      calc (c : ℂ) * ζ ^ ((j₁ : ℕ) * (k : ℕ)) * ((starRingEnd ℂ) ζ ^ ((j₂ : ℕ) * (k : ℕ)) * (c : ℂ))
          = ((c : ℂ) * (c : ℂ)) * (ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (starRingEnd ℂ) ζ ^ ((j₂ : ℕ) * (k : ℕ))) := by ring
        _ = (m : ℂ)⁻¹ * (ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (starRingEnd ℂ) ζ ^ ((j₂ : ℕ) * (k : ℕ))) := by rw [hcc]
    simp_rw [hterm, ← Finset.mul_sum]
    by_cases heq : j₁ = j₂
    · subst heq
      have h1 : ∀ k : Fin m, ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (star ζ) ^ ((j₁ : ℕ) * (k : ℕ)) = 1 := by
        intro k
        rw [← mul_pow, hζ_star, one_pow]
      simp_rw [h1]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        ↓reduceIte]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
    · have hite : (if j₁ = j₂ then (1 : ℂ) else 0) = 0 :=
        ite_eq_right_iff.mpr (fun hc => absurd hc heq)
      rw [hite]
      have hsum0 : (∑ k : Fin m, ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (star ζ) ^ ((j₂ : ℕ) * (k : ℕ))) = 0 := by
        rcases lt_or_gt_of_ne (fun h => heq (Fin.ext h)) with hlt | hgt
        · let d := (j₂ : ℕ) - (j₁ : ℕ)
          have hd1 : 1 ≤ d := by omega
          have hdm : d < m := by omega
          have hpow_k : ∀ k : Fin m,
              ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (star ζ) ^ ((j₂ : ℕ) * (k : ℕ)) = ((star ζ) ^ d) ^ (k : ℕ) := by
            intro k
            have hadd : (j₂ : ℕ) * (k : ℕ) = (j₁ : ℕ) * (k : ℕ) + d * (k : ℕ) := by
              have : (j₂ : ℕ) = (j₁ : ℕ) + d := by omega
              rw [this, add_mul]
            rw [hadd, pow_add, ← mul_assoc, ← mul_pow, hζ_star, one_pow, one_mul, pow_mul]
          simp_rw [hpow_k]
          rw [Fin.sum_univ_eq_sum_range (fun k => ((star ζ) ^ d) ^ k) m]
          apply complex_sum_geom_eq_zero
          · intro h1
            have h1' : ζ ^ d = 1 := by
              have := congrArg star h1
              simpa [star_pow] using this
            exact hζ_prim d hd1 hdm h1'
          · rw [← pow_mul, mul_comm, pow_mul, ← star_pow, hζ_m, star_one, one_pow]
        · let d := (j₁ : ℕ) - (j₂ : ℕ)
          have hd1 : 1 ≤ d := by omega
          have hdm : d < m := by omega
          have hpow_k : ∀ k : Fin m,
              ζ ^ ((j₁ : ℕ) * (k : ℕ)) * (star ζ) ^ ((j₂ : ℕ) * (k : ℕ)) = (ζ ^ d) ^ (k : ℕ) := by
            intro k
            have hadd : (j₁ : ℕ) * (k : ℕ) = d * (k : ℕ) + (j₂ : ℕ) * (k : ℕ) := by
              have : (j₁ : ℕ) = d + (j₂ : ℕ) := by omega
              rw [this, add_mul]
            rw [hadd, pow_add, mul_assoc, ← mul_pow, hζ_star, one_pow, mul_one, pow_mul]
          simp_rw [hpow_k]
          rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ d) ^ k) m]
          apply complex_sum_geom_eq_zero
          · exact hζ_prim d hd1 hdm
          · rw [← pow_mul, mul_comm, pow_mul, hζ_m, one_pow]
      rw [hsum0, mul_zero]
  let Q₀ : Matrix (Fin m × Bool) (Fin m × Bool) ℝ := Matrix.of fun r s =>
    match r.2, s.2 with
    | false, false => (U r.1 s.1).re
    | false, true  => -(U r.1 s.1).im
    | true,  false => (U r.1 s.1).im
    | true,  true  => (U r.1 s.1).re
  have hQ₀_orth : Q₀ * Q₀.transpose = 1 := by
    ext ⟨j₁, b₁⟩ ⟨j₂, b₂⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have hre_sum : (∑ k : Fin m, ((U j₁ k).re * (U j₂ k).re + (U j₁ k).im * (U j₂ k).im)) =
        if j₁ = j₂ then 1 else 0 := by
      have h := congrArg Complex.re (hU_orth j₁ j₂)
      rw [Complex.re_sum] at h
      have hterm : ∀ k : Fin m,
          (U j₁ k * star (U j₂ k)).re = (U j₁ k).re * (U j₂ k).re + (U j₁ k).im * (U j₂ k).im := by
        intro k
        simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
        ring
      simp_rw [hterm] at h
      rw [h]
      split_ifs <;> simp
    have him_sum : (∑ k : Fin m, ((U j₁ k).im * (U j₂ k).re - (U j₁ k).re * (U j₂ k).im)) = 0 := by
      have h := congrArg Complex.im (hU_orth j₁ j₂)
      rw [Complex.im_sum] at h
      have hterm : ∀ k : Fin m,
          (U j₁ k * star (U j₂ k)).im = (U j₁ k).im * (U j₂ k).re - (U j₁ k).re * (U j₂ k).im := by
        intro k
        simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
        ring
      simp_rw [hterm] at h
      rw [h]
      split_ifs <;> simp
    cases b₁ <;> cases b₂
    · simp only [Fintype.sum_bool, Matrix.transpose_apply, Q₀, Matrix.of_apply, Matrix.one_apply,
        Prod.mk.injEq, and_true]
      convert hre_sum using 1
      apply Finset.sum_congr rfl; intro k _; ring
    · simp only [Fintype.sum_bool, Matrix.transpose_apply, Q₀, Matrix.of_apply, Matrix.one_apply,
        Prod.mk.injEq, Bool.false_eq_true, and_false, ↓reduceIte]
      have : (∑ k : Fin m, (-(U j₁ k).im * (U j₂ k).re + (U j₁ k).re * (U j₂ k).im)) =
          -(∑ k : Fin m, ((U j₁ k).im * (U j₂ k).re - (U j₁ k).re * (U j₂ k).im)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro k _; ring
      rw [this, him_sum, neg_zero]
    · simp only [Fintype.sum_bool, Matrix.transpose_apply, Q₀, Matrix.of_apply, Matrix.one_apply,
        Prod.mk.injEq, Bool.true_eq_false, and_false, ↓reduceIte]
      convert him_sum using 1
      apply Finset.sum_congr rfl; intro k _; ring
    · simp only [Fintype.sum_bool, Matrix.transpose_apply, Q₀, Matrix.of_apply, Matrix.one_apply,
        Prod.mk.injEq, and_true]
      exact hre_sum
  have hQ₀_det_sq : (Matrix.det Q₀) ^ 2 = 1 := by
    calc (Matrix.det Q₀) ^ 2 = Matrix.det Q₀ * Matrix.det Q₀.transpose := by
            rw [Matrix.det_transpose, sq]
      _ = Matrix.det (Q₀ * Q₀.transpose) := (Matrix.det_mul Q₀ Q₀.transpose).symm
      _ = 1 := by rw [hQ₀_orth, Matrix.det_one]
  let A : Matrix (Fin m × Bool) (Fin m × Bool) ℝ :=
    (m : ℝ) • Matrix.of (fun r s => (Q₀ r s) ^ 2)
  have hA_perm_le : A.permanent ≤ (m.factorial : ℝ) ^ 2 := by
    apply permanent_pair_matrix_le A
    · intro r s
      simp only [A, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
      exact mul_nonneg hm_pos.le (sq_nonneg _)
    · intro j ⟨k, b⟩
      have hU_nsq : (U j k).re ^ 2 + (U j k).im ^ 2 = (m : ℝ)⁻¹ := by
        have h1 : Complex.normSq (U j k) = (m : ℝ)⁻¹ := by
          simp only [U, Complex.normSq_mul, Complex.normSq_ofReal, complex_normSq_pow, hζ_nsq,
            one_pow, mul_one, ← sq, hc_sq]
        have h2 := Complex.normSq_apply (U j k)
        linarith
      simp only [A, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Q₀]
      cases b
      · calc (m : ℝ) * (U j k).re ^ 2 + (m : ℝ) * (U j k).im ^ 2
            = (m : ℝ) * ((U j k).re ^ 2 + (U j k).im ^ 2) := by ring
          _ = (m : ℝ) * (m : ℝ)⁻¹ := by rw [hU_nsq]
          _ = 1 := mul_inv_cancel₀ hm_pos.ne'
      · calc (m : ℝ) * (-(U j k).im) ^ 2 + (m : ℝ) * (U j k).re ^ 2
            = (m : ℝ) * ((U j k).re ^ 2 + (U j k).im ^ 2) := by ring
          _ = (m : ℝ) * (m : ℝ)⁻¹ := by rw [hU_nsq]
          _ = 1 := mul_inv_cancel₀ hm_pos.ne'
  have hA_perm_eq : A.permanent = (m : ℝ) ^ (2 * m) * Matrix.permanent (Matrix.of fun r s => (Q₀ r s) ^ 2) := by
    simp only [A, permanent_smul, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
  have hQ₀_perm : ((2 * m : ℕ) : ℝ) ^ (2 * m) * Matrix.permanent (Matrix.of fun r s => (Q₀ r s) ^ 2) ≤
      ((2 * m + 1 : ℕ) : ℝ) * ((2 * m).factorial : ℝ) := by
    have h1 : (m : ℝ) ^ (2 * m) * Matrix.permanent (Matrix.of fun r s => (Q₀ r s) ^ 2) ≤
        (m.factorial : ℝ) ^ 2 := by linarith
    have h2 : ((2 * m : ℕ) : ℝ) ^ (2 * m) * Matrix.permanent (Matrix.of fun r s => (Q₀ r s) ^ 2) ≤
        (2 : ℝ) ^ (2 * m) * (m.factorial : ℝ) ^ 2 := by
      have hsplit : ((2 * m : ℕ) : ℝ) ^ (2 * m) = (2 : ℝ) ^ (2 * m) * (m : ℝ) ^ (2 * m) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow]
      rw [hsplit, mul_assoc]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have hbin : ((2 * m : ℕ) : ℝ) ^ (2 * m) * ((m.factorial : ℝ) * (m.factorial : ℝ)) ≤
        ((2 * m + 1 : ℕ) : ℝ) * ((2 * m).factorial : ℝ) * ((m : ℝ) ^ m * (m : ℝ) ^ m) := by
      have hb := binom_max_term m m
      have h2m : m + m = 2 * m := by ring
      rw [h2m] at hb
      exact_mod_cast hb
    have hbin2 : (2 : ℝ) ^ (2 * m) * (m.factorial : ℝ) ^ 2 * (m : ℝ) ^ (2 * m) ≤
        ((2 * m + 1 : ℕ) : ℝ) * ((2 * m).factorial : ℝ) * (m : ℝ) ^ (2 * m) := by
      have hl : ((2 * m : ℕ) : ℝ) ^ (2 * m) * ((m.factorial : ℝ) * (m.factorial : ℝ)) =
          (2 : ℝ) ^ (2 * m) * (m.factorial : ℝ) ^ 2 * (m : ℝ) ^ (2 * m) := by
        rw [Nat.cast_mul, Nat.cast_ofNat, mul_pow]; ring
      have hr : ((m : ℝ) ^ m * (m : ℝ) ^ m) = (m : ℝ) ^ (2 * m) := by
        rw [← pow_add, show m + m = 2 * m by ring]
      rw [hl, hr] at hbin
      exact hbin
    have hbin3 : (2 : ℝ) ^ (2 * m) * (m.factorial : ℝ) ^ 2 ≤
        ((2 * m + 1 : ℕ) : ℝ) * ((2 * m).factorial : ℝ) :=
      le_of_mul_le_mul_right hbin2 (by positivity)
    exact le_trans h2 hbin3
  let eb : Bool ≃ Fin 2 :=
    { toFun := fun b => if b then 1 else 0
      invFun := fun i => i.1 = 1
      left_inv := fun b => by cases b <;> decide
      right_inv := fun i => by fin_cases i <;> decide }
  let e : Fin m × Bool ≃ Fin (2 * m) :=
    (Equiv.prodCongr (Equiv.refl (Fin m)) eb).trans
      (finProdFinEquiv.trans (finCongr (by ring : m * 2 = 2 * m)))
  let Q : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ := Q₀.reindex e e
  have hQ_det_sq : (Matrix.det Q) ^ 2 = 1 := by
    simp only [Q, Matrix.det_reindex_self, hQ₀_det_sq]
  have hQ_det_ne : Matrix.det Q ≠ 0 := by
    intro h0; rw [h0] at hQ_det_sq; norm_num at hQ_det_sq
  have hQ_perm : Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2) =
      Matrix.permanent (Matrix.of fun r s => (Q₀ r s) ^ 2) := by
    have hsq : (Matrix.of fun i j => (Q i j) ^ 2) =
        (Matrix.of fun r s => (Q₀ r s) ^ 2).reindex e e := by
      ext i j; simp [Q]
    rw [hsq, permanent_reindex_self]
  refine ⟨Q, hQ_det_ne, ?_⟩
  rw [hQ_perm, hQ_det_sq, mul_one]
  exact hQ₀_perm

lemma real_witness (n : ℕ) (hn : 2 ≤ n) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ,
      Matrix.det W ≠ 0 ∧
      (n : ℝ) ^ n * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) ≤
        ((3 * (n + 1) : ℕ) : ℝ) * (n.factorial : ℝ) * (Matrix.det W) ^ 2 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm_eq : n = 2 * m := by omega
    subst hm_eq
    have hm1 : 1 ≤ m := by omega
    rcases real_witness_even m hm1 with ⟨Q, hQ_det, hQ_le⟩
    refine ⟨Q, hQ_det, le_trans hQ_le ?_⟩
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    have : 2 * m + 1 ≤ 3 * (2 * m + 1) := by omega
    exact_mod_cast this
  · subst hm
    have hm1 : 1 ≤ m := by omega
    let k := 2 * m
    have hk1 : 1 ≤ k := by omega
    rcases real_witness_even m hm1 with ⟨Q, hQ_det, hQ_le⟩
    let e : Fin k ⊕ Fin 1 ≃ Fin (2 * m + 1) := finSumFinEquiv
    let W : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ :=
      (Matrix.fromBlocks Q 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).reindex e e
    have hW_det : Matrix.det W = Matrix.det Q := by
      simp [W]
    have hW_det_ne : Matrix.det W ≠ 0 := by rw [hW_det]; exact hQ_det
    have hW_perm : Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) =
        Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2) := by
      have hsq : (Matrix.of fun i j => (W i j) ^ 2) =
          (Matrix.fromBlocks (Matrix.of fun i j => (Q i j) ^ 2) 0 0
            (1 : Matrix (Fin 1) (Fin 1) ℝ)).reindex e e := by
        ext i j
        simp only [W, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
        cases e.symm i with
        | inl i1 =>
          cases e.symm j with
          | inl j1 => simp
          | inr j2 => simp
        | inr i2 =>
          cases e.symm j with
          | inl j1 => simp
          | inr j2 =>
            fin_cases i2; fin_cases j2; simp
      rw [hsq, permanent_reindex_self, permanent_fromBlocks_zero, permanent_one, mul_one]
    have hQ_le' : (k : ℝ) ^ k * Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2) ≤
        ((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2 := by
      have hfac : ((k + 1 : ℕ) : ℝ) * (k.factorial : ℝ) = ((k + 1).factorial : ℝ) := by
        rw [Nat.factorial_succ, Nat.cast_mul]
      simpa only [k, ← hfac] using hQ_le
    have hpow3 : ((k + 1 : ℕ) : ℝ) ^ k ≤ 3 * (k : ℝ) ^ k :=
      succ_pow_le_three_mul_pow k hk1
    have hk_pos : (0 : ℝ) < (k : ℝ) ^ k := by positivity
    have hstep : (((k + 1 : ℕ) : ℝ) ^ (k + 1) * Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2)) *
        (k : ℝ) ^ k ≤
        (((3 * (k + 1 + 1) : ℕ) : ℝ) * ((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2) * (k : ℝ) ^ k := by
      calc (((k + 1 : ℕ) : ℝ) ^ (k + 1) * Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2)) *
            (k : ℝ) ^ k
          = ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
              ((k : ℝ) ^ k * Matrix.permanent (Matrix.of fun i j => (Q i j) ^ 2)) := by ring
        _ ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2) :=
              mul_le_mul_of_nonneg_left hQ_le' (by positivity)
        _ = (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ k) *
              (((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2) := by rw [pow_succ']
        _ ≤ (((k + 1 : ℕ) : ℝ) * (3 * (k : ℝ) ^ k)) *
              (((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              exact mul_le_mul_of_nonneg_left hpow3 (by positivity)
        _ ≤ (((3 * (k + 1 + 1) : ℕ) : ℝ) * (k : ℝ) ^ k) *
              (((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have h3le : ((k + 1 : ℕ) : ℝ) * 3 ≤ ((3 * (k + 1 + 1) : ℕ) : ℝ) := by
                push_cast; linarith
              nlinarith
        _ = (((3 * (k + 1 + 1) : ℕ) : ℝ) * ((k + 1).factorial : ℝ) * (Matrix.det Q) ^ 2) *
              (k : ℝ) ^ k := by ring
    refine ⟨W, hW_det_ne, ?_⟩
    rw [hW_perm, hW_det]
    simpa only [k, Nat.cast_add, Nat.cast_one] using le_of_mul_le_mul_right hstep hk_pos

end PEqualNP.Outside.L_lib_707

theorem PEqualNP.Outside.L_lib_707 :
    ∀ (n p t : ℕ), 2 ≤ n → 2 ≤ p →
  let I := Fin n
  ∀ (signs : Fin t → I × I → Bool) (w : Fin t → ℝ), (∀ h, 0 ≤ w h) →
    let P := fun A : Matrix I I ℝ => Matrix.permanent (fun i j => (A i j)^2)
    let est := fun A : Matrix I I ℝ => ∑ h : Fin t, w h * (Matrix.det
      (fun i j => if signs h (i,j) then -A i j else A i j : Matrix I I ℝ))^2
    let good := fun A : Matrix I I ℝ =>
      ((p : ℝ)-1)*P A ≤ (p : ℝ)*est A ∧ (p : ℝ)*est A ≤ ((p : ℝ)+1)*P A
    let count := (Finset.univ.filter (fun h : Fin t => w h ≠ 0)).card
    let loss := (n+1)^(Nat.log2 n+1)
    let bpen := if n = 2^(Nat.log2 n) then 1 else loss
    ((∀ A : Matrix I I ℝ, good A) → (p-1)*n^n ≤ (p+1)*3*(n+1)*n.factorial*count) ∧
    ((∀ A : Matrix I I ℝ, (∀ i j, 0 ≤ A i j) → good A) →
      (p-1)*n^n ≤ (p+1)*2^n*3*(n+1)*n.factorial*count) ∧
    ((∀ A : Matrix I I ℝ, (∀ i j, A i j = -1 ∨ A i j = 0 ∨ A i j = 1) → good A) →
      (p-1)*n^n ≤ (p+1)*bpen*n.factorial*count) ∧
    ((∀ A : Matrix I I ℝ, (∀ i j, A i j = 0 ∨ A i j = 1) → good A) →
      (p-1)*n^n ≤ (p+1)*2^n*bpen*n.factorial*count) := by
  intro n p t hn hp I signs w hw P est good count loss bpen
  have h1_bin : ∀ i j : Fin n,
      (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 ∨ (1 : Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
    intro i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have h1_tern : ∀ i j : Fin n,
      (1 : Matrix (Fin n) (Fin n) ℝ) i j = -1 ∨ (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 ∨
        (1 : Matrix (Fin n) (Fin n) ℝ) i j = 1 := by
    intro i j
    rcases h1_bin i j with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have h1_nn : ∀ i j : Fin n, 0 ≤ (1 : Matrix (Fin n) (Fin n) ℝ) i j := by
    intro i j
    rcases h1_bin i j with h | h <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hall
    have htot := PEqualNP.Outside.L_lib_707.total_weight_lower_bound signs w (hall 1).1
    rcases PEqualNP.Outside.L_lib_707.real_witness n hn with ⟨W, hW_det, hW_le⟩
    have hindiv : ∀ h : Fin t, (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
        ((1 : ℕ) : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
      intro h
      rw [Nat.cast_one, one_mul]
      exact PEqualNP.Outside.L_lib_707.indiv_weight_direct signs w hw W h
        (hall (PEqualNP.Outside.L_lib_707.signedMat (signs h) W)).2
    have hres := PEqualNP.Outside.L_lib_707.reduce_from_witness hp w W hW_det htot hindiv hW_le
    simpa only [mul_one, mul_assoc] using hres
  · intro hnn
    have htot := PEqualNP.Outside.L_lib_707.total_weight_lower_bound signs w (hnn 1 h1_nn).1
    rcases PEqualNP.Outside.L_lib_707.real_witness n hn with ⟨W, hW_det, hW_le⟩
    have hindiv : ∀ h : Fin t, (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
        ((2 ^ n : ℕ) : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
      intro h
      rw [Nat.cast_pow, Nat.cast_ofNat]
      refine PEqualNP.Outside.L_lib_707.indiv_weight_masked signs w hw W h (fun mask => ?_)
      apply (hnn _ ?_).2
      intro i j
      simp only [Matrix.of_apply]
      cases mask i <;> simp
    have hres := PEqualNP.Outside.L_lib_707.reduce_from_witness hp w W hW_det htot hindiv hW_le
    simpa only [mul_assoc] using hres
  · intro htern
    have htot := PEqualNP.Outside.L_lib_707.total_weight_lower_bound signs w (htern 1 h1_tern).1
    rcases PEqualNP.Outside.L_lib_707.dyadic_witness n (by omega) with ⟨W, hW_ent, hW_det, hW_le⟩
    have hindiv : ∀ h : Fin t, (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
        ((1 : ℕ) : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
      intro h
      rw [Nat.cast_one, one_mul]
      refine PEqualNP.Outside.L_lib_707.indiv_weight_direct signs w hw W h ?_
      apply (htern _ ?_).2
      intro i j
      simp only [PEqualNP.Outside.L_lib_707.signedMat, Matrix.of_apply]
      cases signs h (i, j)
      · exact hW_ent i j
      · rcases hW_ent i j with h1 | h0 | h1
        · exact Or.inr (Or.inr (by simp [h1]))
        · exact Or.inr (Or.inl (by simp [h0]))
        · exact Or.inl (by simp [h1])
    have hres := PEqualNP.Outside.L_lib_707.reduce_from_witness hp w W hW_det htot hindiv hW_le
    simpa only [mul_one, mul_assoc] using hres
  · intro hbin
    have htot := PEqualNP.Outside.L_lib_707.total_weight_lower_bound signs w (hbin 1 h1_bin).1
    rcases PEqualNP.Outside.L_lib_707.dyadic_witness n (by omega) with ⟨W, hW_ent, hW_det, hW_le⟩
    have hindiv : ∀ h : Fin t, (p : ℝ) * w h * (Matrix.det W) ^ 2 ≤
        ((2 ^ n : ℕ) : ℝ) * ((p : ℝ) + 1) * Matrix.permanent (Matrix.of fun i j => (W i j) ^ 2) := by
      intro h
      rw [Nat.cast_pow, Nat.cast_ofNat]
      refine PEqualNP.Outside.L_lib_707.indiv_weight_masked signs w hw W h (fun mask => ?_)
      apply (hbin _ ?_).2
      intro i j
      simp only [Matrix.of_apply]
      have hB : (if signs h (i, j) then -W i j else W i j) = -1 ∨
          (if signs h (i, j) then -W i j else W i j) = 0 ∨
          (if signs h (i, j) then -W i j else W i j) = 1 := by
        cases signs h (i, j)
        · simpa using hW_ent i j
        · rcases hW_ent i j with h1 | h0 | h1
          · exact Or.inr (Or.inr (by simp [h1]))
          · exact Or.inr (Or.inl (by simp [h0]))
          · exact Or.inl (by simp [h1])
      cases mask i
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hB with hval | hval | hval <;> rw [hval] <;> norm_num
      · simp only [↓reduceIte]
        rcases hB with hval | hval | hval <;> rw [hval] <;> norm_num
    have hres := PEqualNP.Outside.L_lib_707.reduce_from_witness hp w W hW_det htot hindiv hW_le
    simpa only [mul_assoc] using hres
