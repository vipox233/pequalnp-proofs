import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_1071
def ch (x : ZMod 2) : ℤ := if x = 0 then 1 else -1
theorem ch_add (x y : ZMod 2) : ch (x + y) = ch x * ch y := by
  revert x y; decide
theorem z2 (x : ZMod 2) : x ≠ 0 → x = 1 := by revert x; decide
theorem zadd (x : ZMod 2) : x + x = 0 := by revert x; decide
theorem ch_one_add (x : ZMod 2) : ch (x + 1) = - ch x := by revert x; decide
noncomputable def gS (m n : ℕ) (f : ℕ → ZMod 2 → ℤ) (Y : Matrix (Fin m) (Fin n) (ZMod 2)) : ℤ :=
  ∑ A : Matrix (Fin m) (Fin n) (ZMod 2), f A.rank (∑ i, ∑ j, A i j * Y i j)
theorem gS_sub (m n : ℕ) (f : ℕ → ZMod 2 → ℤ) (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (Y : Matrix (Fin m) (Fin n) (ZMod 2)) : gS m n f (Y.submatrix σ τ) = gS m n f Y := by
  unfold gS
  refine Fintype.sum_bijective (fun A => A.submatrix σ.symm τ.symm) ?_ _ _ ?_
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun A => A.submatrix σ τ, ?_, ?_⟩
    · intro A; ext i j; simp
    · intro A; ext i j; simp
  · intro A
    simp only [Matrix.rank_submatrix, Matrix.submatrix_apply]
    congr 1
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    conv_rhs => rw [← Equiv.sum_comp τ]
    simp
open Matrix in
theorem tr_eq {m n : ℕ} (A Y : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∑ i, ∑ j, A i j * Y i j) = Matrix.trace (Aᵀ * Y) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm
open Matrix in
theorem gS_mul (m n : ℕ) (f : ℕ → ZMod 2 → ℤ) (P : Matrix (Fin m) (Fin m) (ZMod 2))
    (Q : Matrix (Fin n) (Fin n) (ZMod 2)) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (Y : Matrix (Fin m) (Fin n) (ZMod 2)) : gS m n f (P * Y * Q) = gS m n f Y := by
  unfold gS
  have hP' : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have hQ' : IsUnit Qᵀ.det := by rwa [Matrix.det_transpose]
  refine Fintype.sum_bijective (fun A => Pᵀ * A * Qᵀ) ?_ _ _ ?_
  · refine Function.bijective_iff_has_inverse.mpr ⟨fun A => Pᵀ⁻¹ * A * Qᵀ⁻¹, ?_, ?_⟩
    · intro A
      show Pᵀ⁻¹ * (Pᵀ * A * Qᵀ) * Qᵀ⁻¹ = A
      rw [show Pᵀ⁻¹ * (Pᵀ * A * Qᵀ) * Qᵀ⁻¹ = (Pᵀ⁻¹ * Pᵀ) * A * (Qᵀ * Qᵀ⁻¹) by
        simp only [Matrix.mul_assoc], Matrix.nonsing_inv_mul _ hP', Matrix.mul_nonsing_inv _ hQ',
        Matrix.one_mul, Matrix.mul_one]
    · intro A
      show Pᵀ * (Pᵀ⁻¹ * A * Qᵀ⁻¹) * Qᵀ = A
      rw [show Pᵀ * (Pᵀ⁻¹ * A * Qᵀ⁻¹) * Qᵀ = (Pᵀ * Pᵀ⁻¹) * A * (Qᵀ⁻¹ * Qᵀ) by
        simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hP', Matrix.nonsing_inv_mul _ hQ',
        Matrix.one_mul, Matrix.mul_one]
  · intro A
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hQ', Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP',
      tr_eq, tr_eq]
    congr 1
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.mul_assoc Q, Matrix.trace_mul_comm Q]
    simp only [Matrix.mul_assoc]
theorem rk0 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (h : A.rank = 0) : A = 0 := by
  rw [Matrix.rank_eq_finrank_span_row, Submodule.finrank_eq_zero, Submodule.span_eq_bot] at h
  ext i j
  have := h (A.row i) ⟨i, rfl⟩
  exact congrFun this j
open Classical in
theorem rk_cons {m n : ℕ} (v : Fin n → ZMod 2) (R : Fin m → Fin n → ZMod 2) :
    (Matrix.of (Fin.cons v R : Fin (m+1) → Fin n → ZMod 2)).rank =
      if v ∈ Submodule.span (ZMod 2) (Set.range R) then (Matrix.of R).rank
      else (Matrix.of R).rank + 1 := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, Matrix.row_of,
    Matrix.row_of, Fin.range_cons]
  split_ifs with h
  · rw [Submodule.span_insert_eq_span h]
  · rw [Submodule.span_insert]
    have h0 : v ≠ 0 := fun h0 => h (h0 ▸ Submodule.zero_mem _)
    have key := Submodule.finrank_sup_add_finrank_inf_eq ((ZMod 2) ∙ v)
      (Submodule.span (ZMod 2) (Set.range R))
    have hinf : ((ZMod 2) ∙ v) ⊓ Submodule.span (ZMod 2) (Set.range R) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hx
      obtain ⟨⟨c, rfl⟩, h2⟩ := hx
      by_cases hc : c = 0
      · simp [hc]
      · exact absurd ((Submodule.smul_mem_iff _ hc).mp h2) h
    rw [hinf, finrank_bot, finrank_span_singleton h0] at key
    omega
theorem span_col0 {m n : ℕ} (R : Fin m → Fin (n+1) → ZMod 2) (h : ∀ i, R i 0 = 0)
    (w : Fin (n+1) → ZMod 2) (hw : w ∈ Submodule.span (ZMod 2) (Set.range R)) : w 0 = 0 := by
  have : Submodule.span (ZMod 2) (Set.range R) ≤
      LinearMap.ker (LinearMap.proj 0 : (Fin (n+1) → ZMod 2) →ₗ[ZMod 2] ZMod 2) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simp [h i]
  simpa using this hw
open Matrix in
theorem rk_cons0 {m n : ℕ} (X : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (Matrix.of (fun i => Fin.cons 0 (X i)) : Matrix (Fin m) (Fin (n+1)) (ZMod 2)).rank = X.rank := by
  rw [← Matrix.rank_transpose]
  have : (Matrix.of (fun i => Fin.cons 0 (X i)) : Matrix (Fin m) (Fin (n+1)) (ZMod 2))ᵀ =
      Matrix.of (Fin.cons 0 (fun j i => X i j) : Fin (n+1) → Fin m → ZMod 2) := by
    ext j i
    refine Fin.cases ?_ (fun j => ?_) j <;> simp
  rw [this, rk_cons, ite_eq_left (Submodule.zero_mem _)]
  exact Matrix.rank_transpose X
def blk {m n : ℕ} (d : Fin n → ZMod 2) (X : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2) :=
  Matrix.of (Fin.cons (Fin.cons 1 d) (fun i => Fin.cons 0 (X i)))
theorem blk_rank {m n : ℕ} (d : Fin n → ZMod 2) (X : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (blk d X).rank = X.rank + 1 := by
  unfold blk
  have hn : (Fin.cons 1 d : Fin (n+1) → ZMod 2) ∉
      Submodule.span (ZMod 2) (Set.range (fun i => (Fin.cons 0 (X i) : Fin (n+1) → ZMod 2))) := by
    intro hmem
    have := span_col0 (fun i => (Fin.cons 0 (X i) : Fin (n+1) → ZMod 2)) (fun i => by simp) _ hmem
    simp at this
  rw [rk_cons, ite_eq_right hn, rk_cons0]
theorem sum_neg_inv {α : Type*} [Fintype α] (g : α → ℤ) (e : α ≃ α) (h : ∀ x, g (e x) = - g x) :
    ∑ x, g x = 0 := by
  have h1 : ∑ x, g (e x) = ∑ x, g x := Equiv.sum_comp e g
  simp only [h, Finset.sum_neg_distrib] at h1
  linarith
open Classical in
theorem inS (m n r : ℕ) (R : Fin m → Fin (n+1) → ZMod 2) :
    (∑ v : Fin (n+1) → ZMod 2,
      if (Matrix.of (Fin.cons v R : Fin (m+1) → Fin (n+1) → ZMod 2)).rank ≤ r then ch (v 0) else 0) =
      if (Matrix.of R).rank = r ∧ ∀ i, R i 0 = 0 then 2^r else 0 := by
  simp only [rk_cons]
  obtain ⟨k, hk⟩ : ∃ k, (Matrix.of R).rank = k := ⟨_, rfl⟩
  rw [hk]
  rcases lt_trichotomy k r with hkr | rfl | hkr
  · rw [ite_eq_right (fun h => by omega)]
    have : ∀ v : Fin (n+1) → ZMod 2, (if (if v ∈ Submodule.span (ZMod 2) (Set.range R) then k
        else k + 1) ≤ r then ch (v 0) else 0) = ch (v 0) := by
      intro v
      split_ifs <;> first | rfl | omega
    simp only [this]
    refine sum_neg_inv _ (Equiv.addRight (Pi.single 0 1)) (fun v => ?_)
    simp [ch_one_add]
  · have e1 : ∀ v : Fin (n+1) → ZMod 2, (if (if v ∈ Submodule.span (ZMod 2) (Set.range R) then k
        else k + 1) ≤ k then ch (v 0) else 0) =
        if v ∈ Submodule.span (ZMod 2) (Set.range R) then ch (v 0) else 0 := by
      intro v
      split_ifs <;> first | rfl | omega
    by_cases hc : ∀ i, R i 0 = 0
    · rw [ite_eq_left ⟨rfl, hc⟩]
      simp only [e1]
      have e2 : ∀ v : Fin (n+1) → ZMod 2,
          (if v ∈ Submodule.span (ZMod 2) (Set.range R) then ch (v 0) else 0) =
          if v ∈ Submodule.span (ZMod 2) (Set.range R) then 1 else 0 := by
        intro v
        split_ifs with hv
        · rw [span_col0 R hc v hv]; rfl
        · rfl
      simp only [e2]
      rw [Finset.sum_boole]
      have hcard : (Finset.univ.filter
          (fun v => v ∈ Submodule.span (ZMod 2) (Set.range R))).card = 2 ^ k := by
        have : Module.Finite (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range R)) :=
          Module.Finite.span_of_finite _ (Set.finite_range R)
        rw [← Nat.subtype_card (p := fun v => v ∈ Submodule.span (ZMod 2) (Set.range R)) _
          (fun x => by simp), Module.natCard_eq_pow_finrank (K := ZMod 2),
          Nat.card_zmod, ← hk, Matrix.rank_eq_finrank_span_row, Matrix.row_of]
      rw [hcard]
      push_cast
      rfl
    · rw [ite_eq_right (fun h => hc h.2)]
      simp only [e1]
      obtain ⟨i, hi⟩ := not_forall.mp hc
      have hRi : R i ∈ Submodule.span (ZMod 2) (Set.range R) := Submodule.subset_span ⟨i, rfl⟩
      refine sum_neg_inv _ (Equiv.addRight (R i)) (fun v => ?_)
      simp only [Equiv.coe_addRight, Submodule.add_mem_iff_left _ hRi, Pi.add_apply, z2 _ hi,
        ch_one_add]
      split_ifs <;> simp
  · rw [ite_eq_right (fun h => by omega)]
    refine Finset.sum_eq_zero (fun v _ => ?_)
    apply ite_eq_right
    split_ifs <;> omega
theorem pair_cons {m n : ℕ} (v : Fin (n+1) → ZMod 2) (R : Fin m → Fin (n+1) → ZMod 2)
    (Y1 : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∑ i, ∑ j, (Matrix.of (Fin.cons v R : Fin (m+1) → Fin (n+1) → ZMod 2)) i j * (blk 0 Y1) i j) =
      v 0 + ∑ i, ∑ j, R i j.succ * Y1 i j := by
  simp [blk, Fin.sum_univ_succ]
theorem sum_split {m n : ℕ} (G : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2) → ℤ) :
    ∑ A, G A = ∑ R : Fin m → Fin (n+1) → ZMod 2, ∑ v : Fin (n+1) → ZMod 2,
      G (Matrix.of (Fin.cons v R : Fin (m+1) → Fin (n+1) → ZMod 2)) := by
  rw [← Equiv.sum_comp ((Fin.consEquiv fun _ => Fin (n+1) → ZMod 2).trans Matrix.of),
    Fintype.sum_prod_type, Finset.sum_comm]
  rfl
theorem red2 (m n r : ℕ) (Y1 : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (∑ R : Fin m → Fin (n+1) → ZMod 2, (if (Matrix.of R).rank = r ∧ ∀ i, R i 0 = 0 then (2:ℤ)^r
      else 0) * ch (∑ i, ∑ j, R i j.succ * Y1 i j)) =
      2^r * ∑ C : Matrix (Fin m) (Fin n) (ZMod 2),
        if C.rank = r then ch (∑ i, ∑ j, C i j * Y1 i j) else 0 := by
  rw [Finset.mul_sum]
  symm
  refine Fintype.sum_of_injective (fun C : Matrix (Fin m) (Fin n) (ZMod 2) =>
    fun i => (Fin.cons 0 (C i) : Fin (n+1) → ZMod 2)) ?_ _ _ ?_ ?_
  · intro C C' h
    ext i j
    have := congrFun (congrFun h i) j.succ
    simpa using this
  · intro R hR
    have hn : ¬((Matrix.of R).rank = r ∧ ∀ i, R i 0 = 0) := by
      rintro ⟨_, h0⟩
      apply hR
      refine ⟨Matrix.of fun i j => R i j.succ, ?_⟩
      funext i
      refine funext (fun j => Fin.cases ?_ (fun j => ?_) j)
      · simp [h0 i]
      · simp
    rw [ite_eq_right hn, zero_mul]
  · intro C
    have := rk_cons0 C
    simp only [this, Fin.cons_zero, Fin.cons_succ, implies_true, and_true]
    split_ifs <;> simp
noncomputable def bl (m n r : ℕ) (Y : Matrix (Fin m) (Fin n) (ZMod 2)) : ℤ :=
  gS m n (fun k x => if k ≤ r then ch x else 0) Y
noncomputable def ly (m n r : ℕ) (Z : Matrix (Fin m) (Fin n) (ZMod 2)) : ℤ :=
  gS m n (fun k x => if k = r then ch x else 0) Z
theorem red (m n r : ℕ) (Y1 : Matrix (Fin m) (Fin n) (ZMod 2)) :
    bl (m+1) (n+1) r (blk 0 Y1) = 2^r * ly m n r Y1 := by
  unfold bl ly gS
  rw [sum_split, ← red2]
  refine Finset.sum_congr rfl (fun R _ => ?_)
  simp only [pair_cons, ch_add]
  rw [← inS m n r R, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  split_ifs <;> simp
theorem ly_eq (m n r : ℕ) (Z : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ly m n r Z = bl m n r Z - (if r = 0 then 0 else bl m n (r-1) Z) := by
  unfold ly bl gS
  beta_reduce
  split_ifs with hr
  · subst hr
    rw [sub_zero]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    simp only [Nat.le_zero]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    split_ifs <;> omega
def rowc {m n : ℕ} (Y : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2)) :
    Matrix (Fin (m+1)) (Fin (m+1)) (ZMod 2) :=
  Matrix.of fun p k => if p = k then 1 else if k = 0 then Y p 0 else 0
def colc {m n : ℕ} (Y : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2)) :
    Matrix (Fin (n+1)) (Fin (n+1)) (ZMod 2) :=
  Matrix.of fun k q => if k = q then 1 else if k = 0 then Y 0 q else 0
theorem rowc_det {m n : ℕ} (Y : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2)) :
    IsUnit (rowc Y).det := by
  have h : (rowc Y).IsLowerTriangular := by
    intro p k hpk
    have hpk' : p < k := OrderDual.toDual_lt_toDual.mp hpk
    have hk : k ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero p hpk'
    simp [rowc, ne_of_lt hpk', hk]
  rw [Matrix.det_of_isLowerTriangular _ h]
  simp [rowc]
theorem colc_det {m n : ℕ} (Y : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2)) :
    IsUnit (colc Y).det := by
  have h : (colc Y).IsUpperTriangular := by
    intro k q hkq
    have hkq' : q < k := hkq
    have hk : k ≠ 0 := by
      rintro rfl
      exact Fin.not_lt_zero q hkq'
    simp [colc, ne_of_gt hkq', hk]
  rw [Matrix.det_of_isUpperTriangular h]
  simp [colc]
theorem zne {k : ℕ} (x : Fin k) : (0 : Fin (k+1)) ≠ x.succ := (Fin.succ_ne_zero x).symm
theorem clear_eq {m n : ℕ} (Y : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2)) (h00 : Y 0 0 = 1) :
    rowc Y * Y * colc Y =
      blk 0 (Matrix.of fun p q => Y p.succ q.succ + Y p.succ 0 * Y 0 q.succ) := by
  have hPY : ∀ p l, (rowc Y * Y) p l = Y p l + (if p = 0 then 0 else Y p 0 * Y 0 l) := by
    intro p l
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun p => ?_) p
    · simp [rowc, zne]
    · simp [rowc, Fin.succ_ne_zero]
      ring
  ext p q
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [hPY]
  refine Fin.cases ?_ (fun p => ?_) p <;> refine Fin.cases ?_ (fun q => ?_) q
  · simp [colc, blk, h00]
  · simp [colc, blk, h00, zadd, zne]
  · simp [colc, blk, h00, zadd, Fin.succ_ne_zero]
  · simp [colc, blk, h00, zadd, Fin.succ_ne_zero]
theorem step (m n : ℕ) (Y : Matrix (Fin (m+1)) (Fin (n+1)) (ZMod 2)) (hY : Y ≠ 0) :
    ∃ Y1 : Matrix (Fin m) (Fin n) (ZMod 2),
      (∀ f, gS (m+1) (n+1) f Y = gS (m+1) (n+1) f (blk 0 Y1)) ∧ Y.rank = Y1.rank + 1 := by
  obtain ⟨i, j, hij⟩ : ∃ i j, Y i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hY (Matrix.ext fun i j => by simp [h])
  set Y2 := Y.submatrix (Equiv.swap 0 i) (Equiv.swap 0 j) with hY2
  have h00 : Y2 0 0 = 1 := by
    rw [hY2, Matrix.submatrix_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
    exact z2 _ hij
  refine ⟨Matrix.of fun p q => Y2 p.succ q.succ + Y2 p.succ 0 * Y2 0 q.succ, ?_, ?_⟩
  · intro f
    rw [← clear_eq Y2 h00, gS_mul _ _ f _ _ (rowc_det Y2) (colc_det Y2), hY2, gS_sub]
  · rw [← blk_rank 0, ← clear_eq Y2 h00,
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ (colc_det Y2),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (rowc_det Y2), hY2, Matrix.rank_submatrix]
theorem DR (k : ℕ) : ∀ (m n : ℕ) (Y Y' : Matrix (Fin m) (Fin n) (ZMod 2)), Y.rank = k →
    Y'.rank = k → ∀ r, bl m n r Y = bl m n r Y' := by
  induction k with
  | zero =>
    intro m n Y Y' h h' r
    rw [rk0 Y h, rk0 Y' h']
  | succ k ih =>
    intro m n Y Y' h h' r
    obtain _ | m := m
    · have := Matrix.rank_le_height Y
      omega
    obtain _ | n := n
    · have := Matrix.rank_le_width Y
      omega
    have hY : Y ≠ 0 := by
      rintro rfl
      simp at h
    have hY' : Y' ≠ 0 := by
      rintro rfl
      simp at h'
    obtain ⟨Y1, hf, hr⟩ := step m n Y hY
    obtain ⟨Y1', hf', hr'⟩ := step m n Y' hY'
    have e : ∀ s, bl m n s Y1 = bl m n s Y1' := ih m n Y1 Y1' (by omega) (by omega)
    unfold bl
    rw [hf, hf']
    show bl (m+1) (n+1) r (blk 0 Y1) = bl (m+1) (n+1) r (blk 0 Y1')
    rw [red, red, ly_eq, ly_eq, e, e]
theorem DRly (m n r : ℕ) (Z Z' : Matrix (Fin m) (Fin n) (ZMod 2)) (h : Z.rank = Z'.rank) :
    ly m n r Z = ly m n r Z' := by
  rw [ly_eq, ly_eq, DR _ m n Z Z' rfl h.symm, DR _ m n Z Z' rfl h.symm]
def J (m n r : ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  Matrix.of fun i j => if (i : ℕ) = j ∧ (i : ℕ) < r then 1 else 0
theorem J_succ (m n r : ℕ) : J (m+1) (n+1) (r+1) = blk 0 (J m n r) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> simp [J, blk]
theorem J_rank (r : ℕ) : ∀ m n, r ≤ m → r ≤ n → (J m n r).rank = r := by
  induction r with
  | zero =>
    intro m n _ _
    have : J m n 0 = 0 := by
      ext i j
      simp [J]
    rw [this, Matrix.rank_zero]
  | succ r ih =>
    intro m n hm hn
    obtain _ | m := m
    · omega
    obtain _ | n := n
    · omega
    rw [J_succ, blk_rank, ih m n (by omega) (by omega)]
theorem blk_single {m n : ℕ} (X : Matrix (Fin m) (Fin (n+1)) (ZMod 2)) (x : Fin (m+1))
    (y : Fin (n+1+1)) :
    blk (Pi.single 0 1) X x y = blk 0 X x y + if x = 0 ∧ y = Fin.succ 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun x => ?_) x <;> refine Fin.cases ?_ (fun y => ?_) y
  · simp [blk]
  · simp only [blk, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, Fin.succ_inj, Pi.single_apply,
      Pi.zero_apply, true_and, zero_add]
  · simp [blk, Fin.succ_ne_zero]
  · simp [blk, Fin.succ_ne_zero]
theorem sum_unit {a b : ℕ} (Z : Matrix (Fin a) (Fin b) (ZMod 2)) (i : Fin a) (j : Fin b) :
    (∑ p, ∑ q, (if p = i ∧ q = j then (1 : ZMod 2) else 0) * Z p q) = Z i j := by
  simp [ite_and]
theorem EXb (a b r : ℕ) (hr : 0 < r) (ha : r ≤ a) (hb : r ≤ b) (hb2 : 2 ≤ b)
    (Z : Matrix (Fin a) (Fin b) (ZMod 2)) (hZ : Z ≠ 0) :
    ∃ C1 C2 : Matrix (Fin a) (Fin b) (ZMod 2), C1.rank = r ∧ C2.rank = r ∧
      (∑ i, ∑ j, C1 i j * Z i j) ≠ ∑ i, ∑ j, C2 i j * Z i j := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 + 1 := ⟨b - 2, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨i, j, hij⟩ : ∃ i j, Z i j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hZ (Matrix.ext fun i j => by simp [h])
  have hX : (J a (b+1) r).rank = r := J_rank r a (b+1) (by omega) (by omega)
  refine ⟨(blk 0 (J a (b+1) r)).submatrix (Equiv.swap i 0) (Equiv.swap j (Fin.succ 0)),
    (blk (Pi.single 0 1) (J a (b+1) r)).submatrix (Equiv.swap i 0) (Equiv.swap j (Fin.succ 0)),
    ?_, ?_, ?_⟩
  · rw [Matrix.rank_submatrix, blk_rank, hX]
  · rw [Matrix.rank_submatrix, blk_rank, hX]
  · intro h
    have key : (∑ p, ∑ q, ((blk (Pi.single 0 1) (J a (b+1) r)).submatrix (Equiv.swap i 0)
        (Equiv.swap j (Fin.succ 0))) p q * Z p q) =
        (∑ p, ∑ q, ((blk 0 (J a (b+1) r)).submatrix (Equiv.swap i 0)
        (Equiv.swap j (Fin.succ 0))) p q * Z p q) + Z i j := by
      simp only [Matrix.submatrix_apply, blk_single, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [← sum_unit Z i j]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      congr 1
      simp [Equiv.swap_apply_eq_iff]
    rw [key] at h
    apply hij
    simpa using h
open Matrix in
theorem EX (a b r : ℕ) (hr : 0 < r) (hrab : r ≤ min a b) (hab : 1 < max a b)
    (Z : Matrix (Fin a) (Fin b) (ZMod 2)) (hZ : Z ≠ 0) :
    ∃ C1 C2 : Matrix (Fin a) (Fin b) (ZMod 2), C1.rank = r ∧ C2.rank = r ∧
      (∑ i, ∑ j, C1 i j * Z i j) ≠ ∑ i, ∑ j, C2 i j * Z i j := by
  by_cases hb : 2 ≤ b
  · exact EXb a b r hr (by omega) (by omega) hb Z hZ
  · have ha : 2 ≤ a := by omega
    have hZt : Zᵀ ≠ 0 := by
      intro h
      apply hZ
      rw [← Matrix.transpose_transpose Z, h, Matrix.transpose_zero]
    obtain ⟨C1, C2, h1, h2, h3⟩ := EXb b a r hr (by omega) (by omega) ha Zᵀ hZt
    have e : ∀ C : Matrix (Fin b) (Fin a) (ZMod 2),
        (∑ i, ∑ j, Cᵀ i j * Z i j) = ∑ i, ∑ j, C i j * Zᵀ i j := by
      intro C
      simp only [Matrix.transpose_apply]
      exact Finset.sum_comm
    refine ⟨C1ᵀ, C2ᵀ, by rw [Matrix.rank_transpose, h1], by rw [Matrix.rank_transpose, h2], ?_⟩
    rw [e, e]
    exact h3
theorem ch_le (x : ZMod 2) : ch x ≤ 1 := by
  unfold ch
  split_ifs <;> norm_num
theorem ch_ge (x : ZMod 2) : -1 ≤ ch x := by
  unfold ch
  split_ifs <;> norm_num
theorem zz (x y : ZMod 2) : x ≠ y → (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by
  revert x y
  decide
theorem ly_le (m n r : ℕ) (Z : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ly m n r Z ≤ ∑ C : Matrix (Fin m) (Fin n) (ZMod 2), if C.rank = r then 1 else 0 := by
  unfold ly gS
  refine Finset.sum_le_sum (fun C _ => ?_)
  beta_reduce
  split_ifs
  · exact ch_le _
  · exact le_refl _
theorem ly_ge (m n r : ℕ) (Z : Matrix (Fin m) (Fin n) (ZMod 2)) :
    -(∑ C : Matrix (Fin m) (Fin n) (ZMod 2), if C.rank = r then (1:ℤ) else 0) ≤ ly m n r Z := by
  unfold ly gS
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum (fun C _ => ?_)
  beta_reduce
  split_ifs
  · exact ch_ge _
  · simp
theorem ly_zero (m n r : ℕ) :
    ly m n r 0 = ∑ C : Matrix (Fin m) (Fin n) (ZMod 2), if C.rank = r then 1 else 0 := by
  unfold ly gS
  refine Finset.sum_congr rfl (fun C _ => ?_)
  simp [ch]
theorem ly_strict (a b r : ℕ) (hr : 0 < r) (hrab : r ≤ min a b) (hab : 1 < max a b)
    (Z : Matrix (Fin a) (Fin b) (ZMod 2)) (hZ : Z ≠ 0) :
    ly a b r Z < (∑ C : Matrix (Fin a) (Fin b) (ZMod 2), if C.rank = r then 1 else 0) ∧
    -(∑ C : Matrix (Fin a) (Fin b) (ZMod 2), if C.rank = r then (1:ℤ) else 0) < ly a b r Z := by
  obtain ⟨C1, C2, h1, h2, h3⟩ := EX a b r hr hrab hab Z hZ
  obtain ⟨Cp, Cn, hp, hn, hp0, hn1⟩ : ∃ Cp Cn : Matrix (Fin a) (Fin b) (ZMod 2), Cp.rank = r ∧
      Cn.rank = r ∧ (∑ i, ∑ j, Cp i j * Z i j) = 0 ∧ (∑ i, ∑ j, Cn i j * Z i j) = 1 := by
    rcases zz _ _ h3 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨C1, C2, h1, h2, e1, e2⟩
    · exact ⟨C2, C1, h2, h1, e2, e1⟩
  unfold ly gS
  constructor
  · refine Finset.sum_lt_sum (fun C _ => ?_) ⟨Cn, Finset.mem_univ _, ?_⟩
    · beta_reduce
      split_ifs
      · exact ch_le _
      · exact le_refl _
    · beta_reduce
      rw [ite_eq_left hn, ite_eq_left hn, hn1]
      decide
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_lt_sum (fun C _ => ?_) ⟨Cp, Finset.mem_univ _, ?_⟩
    · beta_reduce
      split_ifs
      · exact ch_ge _
      · simp
    · beta_reduce
      rw [ite_eq_left hp, ite_eq_left hp, hp0]
      decide
theorem cardeq (a b r : ℕ) :
    ((Nat.card {C : Matrix (Fin a) (Fin b) (ZMod 2) // C.rank = r} : ℕ) : ℤ) =
      ∑ C : Matrix (Fin a) (Fin b) (ZMod 2), if C.rank = r then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.natCast_card_filter]
theorem fin2 (r : ℕ) (L : ℤ) (N k : ℕ) (hl : L ≤ N) (hg : -(N:ℤ) ≤ L) (heq : k = 0 → L = N)
    (hlt : k ≠ 0 → L < N ∧ -(N:ℤ) < L) :
    ((2:ℤ)^r * L).natAbs ≤ 2^r * N ∧ (((2:ℤ)^r * L).natAbs = 2^r * N ↔ k + 1 = 1) := by
  have e : ((2:ℤ)^r * L).natAbs = 2^r * L.natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    rfl
  rw [e]
  have hpos : 0 < 2^r := by positivity
  refine ⟨Nat.mul_le_mul_left _ (by omega), ?_⟩
  rw [Nat.mul_left_cancel_iff hpos]
  constructor
  · intro h
    by_contra hk
    have := hlt (by omega)
    omega
  · intro hk
    have := heq (by omega)
    omega
end PEqualNP.Outside.L_lib_1071
theorem PEqualNP.Outside.L_lib_1071 : ∀ (a b r : ℕ),
  let F := ZMod 2
  let M := Matrix (Fin (a+1)) (Fin (b+1)) F
  let D := Matrix (Fin a) (Fin b) F
  let ball := fun (Y : M) => ∑ A : M, if Matrix.rank A ≤ r then
    (if (∑ i, ∑ j, A i j * Y i j) = 0 then (1 : ℤ) else -1) else 0
  let layer := fun (Z : D) => ∑ C : D, if Matrix.rank C = r then
    (if (∑ i, ∑ j, C i j * Z i j) = 0 then (1 : ℤ) else -1) else 0
  let cap := 2^r * Nat.card {C : D // Matrix.rank C = r}
  ∀ Y : M, Y ≠ 0 →
    (∀ Z : D, Matrix.rank Y = Matrix.rank Z + 1 → ball Y = (2 : ℤ)^r * layer Z) ∧
    (0 < r → r ≤ min a b → 1 < max a b →
      (ball Y).natAbs ≤ cap ∧ ((ball Y).natAbs = cap ↔ Matrix.rank Y = 1)) := by
  intro a b r F M D ball layer cap Y hY
  have hb : ball Y = PEqualNP.Outside.L_lib_1071.bl (a+1) (b+1) r Y := rfl
  have hl : ∀ Z : D, layer Z = PEqualNP.Outside.L_lib_1071.ly a b r Z := fun Z => rfl
  have hcap : cap = 2^r * Nat.card {C : Matrix (Fin a) (Fin b) (ZMod 2) // C.rank = r} := rfl
  obtain ⟨Y1, hf, hr1⟩ := PEqualNP.Outside.L_lib_1071.step a b Y hY
  have hball : ball Y = 2^r * PEqualNP.Outside.L_lib_1071.ly a b r Y1 := by
    rw [hb]
    unfold PEqualNP.Outside.L_lib_1071.bl
    rw [hf]
    exact PEqualNP.Outside.L_lib_1071.red a b r Y1
  refine ⟨fun Z hZ => ?_, fun h1 h2 h3 => ?_⟩
  · rw [hball, hl, PEqualNP.Outside.L_lib_1071.DRly a b r Y1 Z (by omega)]
  · rw [hball, hcap, hr1]
    have hc := PEqualNP.Outside.L_lib_1071.cardeq a b r
    refine PEqualNP.Outside.L_lib_1071.fin2 r _ _ (Matrix.rank Y1) ?_ ?_ ?_ ?_
    · rw [hc]
      exact PEqualNP.Outside.L_lib_1071.ly_le a b r Y1
    · rw [hc]
      exact PEqualNP.Outside.L_lib_1071.ly_ge a b r Y1
    · intro hk
      rw [hc, PEqualNP.Outside.L_lib_1071.rk0 Y1 hk]
      exact PEqualNP.Outside.L_lib_1071.ly_zero a b r
    · intro hk
      have hY1 : Y1 ≠ 0 := by
        rintro rfl
        simp at hk
      rw [hc]
      exact PEqualNP.Outside.L_lib_1071.ly_strict a b r h1 h2 h3 Y1 hY1
