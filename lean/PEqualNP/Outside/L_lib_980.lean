import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_lib_980_aux

private lemma mul_two_pow_le_four_pow (m : ℕ) : m * 2 ^ m ≤ m * 4 ^ m := by
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by decide) m

private lemma extract_one_block {n m : ℕ} (hm : 0 < m)
    (s : (Fin n × Fin n) → Bool)
    (R C : Finset (Fin n)) (hR : m * 2 ^ m ≤ R.card) (hC : m ≤ C.card) :
    ∃ (R0 C0 : Finset (Fin n)) (pat : Fin n → Bool),
      R0 ⊆ R ∧ C0 ⊆ C ∧ R0.card = m ∧ C0.card = m ∧
      ∀ i ∈ R0, ∀ j ∈ C0, s (i, j) = pat j := by
  rcases Finset.exists_subset_card_eq hC with ⟨C0, hC0_sub, hC0_card⟩
  let f : Fin n → (C0 → Bool) := fun i j => s (i, j.1)
  have hmaps : ∀ i ∈ R, f i ∈ (Finset.univ : Finset (C0 → Bool)) := fun _ _ => Finset.mem_univ _
  have hcard_cod : (Finset.univ : Finset (C0 → Bool)).card = 2 ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hC0_card]
  have hlt : (Finset.univ : Finset (C0 → Bool)).card * (m - 1) < R.card := by
    rw [hcard_cod]
    have hpow : 0 < 2 ^ m := Nat.two_pow_pos m
    have h1 : 2 ^ m * (m - 1) < m * 2 ^ m := by
      rw [mul_comm]
      exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hm Nat.zero_lt_one) hpow
    exact lt_of_lt_of_le h1 hR
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hlt with ⟨p, _, hp_card⟩
  have hge : m ≤ (R.filter (fun i => f i = p)).card := by omega
  rcases Finset.exists_subset_card_eq hge with ⟨R0, hR0_sub, hR0_card⟩
  let pat : Fin n → Bool := fun j => if hj : j ∈ C0 then p ⟨j, hj⟩ else false
  refine ⟨R0, C0, pat, hR0_sub.trans (Finset.filter_subset _ R), hC0_sub, hR0_card, hC0_card, ?_⟩
  intro i hi j hj
  have hfi : f i = p := (Finset.mem_filter.mp (hR0_sub hi)).2
  have h1 : s (i, j) = p ⟨j, hj⟩ := congrFun hfi ⟨j, hj⟩
  simpa [pat, hj] using h1

private lemma extract_blocks {n m : ℕ} (hm : 0 < m)
    (s : (Fin n × Fin n) → Bool) :
    ∀ (j : ℕ) (R C : Finset (Fin n)),
      j * m + m * 4 ^ m ≤ R.card → j * m + m * 4 ^ m ≤ C.card →
      ∃ (rows cols : Fin j → Finset (Fin n)) (pat : Fin j → Fin n → Bool),
        (∀ t, rows t ⊆ R) ∧ (∀ t, cols t ⊆ C) ∧
        (∀ t, (rows t).card = m) ∧ (∀ t, (cols t).card = m) ∧
        (∀ t1 t2, t1 ≠ t2 → Disjoint (rows t1) (rows t2)) ∧
        (∀ t1 t2, t1 ≠ t2 → Disjoint (cols t1) (cols t2)) ∧
        (∀ t, ∀ i ∈ rows t, ∀ c ∈ cols t, s (i, c) = pat t c) := by
  intro j
  induction j with
  | zero =>
    intro R C _ _
    exact ⟨Fin.elim0, Fin.elim0, Fin.elim0,
      fun t => Fin.elim0 t, fun t => Fin.elim0 t,
      fun t => Fin.elim0 t, fun t => Fin.elim0 t,
      fun t => Fin.elim0 t, fun t => Fin.elim0 t,
      fun t => Fin.elim0 t⟩
  | succ j ih =>
    intro R C hR hC
    have hR1 : m * 2 ^ m ≤ R.card := le_trans (mul_two_pow_le_four_pow m) (by omega)
    have hC1 : m ≤ C.card := by
      have : 1 ≤ 4 ^ m := Nat.one_le_pow m 4 (by decide)
      nlinarith
    rcases extract_one_block hm s R C hR1 hC1 with
      ⟨R0, C0, pat0, hR0_sub, hC0_sub, hR0_card, hC0_card, hpat0⟩
    have hR' : j * m + m * 4 ^ m ≤ (R \ R0).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hR0_sub, hR0_card]
      have : (j + 1) * m = j * m + m := Nat.succ_mul j m
      omega
    have hC' : j * m + m * 4 ^ m ≤ (C \ C0).card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hC0_sub, hC0_card]
      have : (j + 1) * m = j * m + m := Nat.succ_mul j m
      omega
    rcases ih (R \ R0) (C \ C0) hR' hC' with
      ⟨rows, cols, pat, hrows_sub, hcols_sub, hrows_card, hcols_card, hrows_disj, hcols_disj, hpat⟩
    let rows' : Fin (j + 1) → Finset (Fin n) := Fin.cons R0 rows
    let cols' : Fin (j + 1) → Finset (Fin n) := Fin.cons C0 cols
    let pat' : Fin (j + 1) → Fin n → Bool := Fin.cons pat0 pat
    refine ⟨rows', cols', pat', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t
      refine Fin.cases hR0_sub (fun t' => (hrows_sub t').trans Finset.sdiff_subset) t
    · intro t
      refine Fin.cases hC0_sub (fun t' => (hcols_sub t').trans Finset.sdiff_subset) t
    · intro t
      refine Fin.cases hR0_card hrows_card t
    · intro t
      refine Fin.cases hC0_card hcols_card t
    · intro t1 t2
      refine Fin.cases ?_ ?_ t1
      · refine Fin.cases (fun h => absurd rfl h) (fun t2' _ => ?_) t2
        exact Disjoint.mono_right (hrows_sub t2') Finset.disjoint_sdiff
      · intro t1'
        refine Fin.cases (fun _ => ?_) (fun t2' h => ?_) t2
        · exact Disjoint.mono_left (hrows_sub t1') Finset.sdiff_disjoint
        · exact hrows_disj t1' t2' (fun heq => h (congrArg Fin.succ heq))
    · intro t1 t2
      refine Fin.cases ?_ ?_ t1
      · refine Fin.cases (fun h => absurd rfl h) (fun t2' _ => ?_) t2
        exact Disjoint.mono_right (hcols_sub t2') Finset.disjoint_sdiff
      · intro t1'
        refine Fin.cases (fun _ => ?_) (fun t2' h => ?_) t2
        · exact Disjoint.mono_left (hcols_sub t1') Finset.sdiff_disjoint
        · exact hcols_disj t1' t2' (fun heq => h (congrArg Fin.succ heq))
    · intro t
      refine Fin.cases hpat0 hpat t

private lemma permanent_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix β β ℝ) :
    (M.submatrix e e).permanent = M.permanent := by
  simp only [Matrix.permanent, Matrix.submatrix_apply]
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ ?_
  intro σ
  refine Fintype.prod_equiv e _ _ ?_
  intro i
  simp [Equiv.permCongr_apply]

private lemma permanent_block_H_id (k m r : ℕ) (H : Matrix (Fin m) (Fin m) ℝ) :
    Matrix.permanent (fun x y : (Fin k × Fin m) ⊕ Fin r => match x, y with
      | Sum.inl (t1, a), Sum.inl (t2, b) => if t1 = t2 then H a b else 0
      | Sum.inr u, Sum.inr v => if u = v then 1 else 0
      | _, _ => 0) = H.permanent ^ k := by
  let B0 : Matrix ((Fin k × Fin m) ⊕ Fin r) ((Fin k × Fin m) ⊕ Fin r) ℝ :=
    fun x y => match x, y with
      | Sum.inl (t1, a), Sum.inl (t2, b) => if t1 = t2 then H a b else 0
      | Sum.inr u, Sum.inr v => if u = v then 1 else 0
      | _, _ => 0
  change B0.permanent = H.permanent ^ k
  let α := (Fin k × Fin m) ⊕ Fin r
  let embed : (Fin k → Equiv.Perm (Fin m)) → Equiv.Perm α := fun σ =>
    Equiv.sumCongr
      { toFun := fun p => (p.1, σ p.1 p.2)
        invFun := fun p => (p.1, (σ p.1).symm p.2)
        left_inv := fun ⟨t, a⟩ => by simp
        right_inv := fun ⟨t, a⟩ => by simp }
      (Equiv.refl (Fin r))
  have hembed_inj : Function.Injective embed := by
    intro σ1 σ2 h
    funext t
    apply Equiv.ext
    intro a
    have h1 := congrArg (fun (e : Equiv.Perm α) => e (Sum.inl (t, a))) h
    change Sum.inl (t, σ1 t a) = Sum.inl (t, σ2 t a) at h1
    exact (Prod.mk.inj (Sum.inl.inj h1)).2
  have hprod_eq : ∀ σ : Fin k → Equiv.Perm (Fin m),
      ∏ x : α, B0 (embed σ x) x = ∏ t : Fin k, ∏ a : Fin m, H (σ t a) a := by
    intro σ
    rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
    have h1 : (∏ x : Fin k, ∏ y : Fin m, B0 (embed σ (Sum.inl (x, y))) (Sum.inl (x, y))) =
        ∏ t : Fin k, ∏ a : Fin m, H (σ t a) a := by
      congr 1; ext t; congr 1; ext a
      change B0 (Sum.inl (t, σ t a)) (Sum.inl (t, a)) = H (σ t a) a
      simp [B0]
    have h2 : (∏ z : Fin r, B0 (embed σ (Sum.inr z)) (Sum.inr z)) = 1 := by
      apply Finset.prod_eq_one
      intro z _
      change B0 (Sum.inr z) (Sum.inr z) = 1
      simp [B0]
    rw [h1, h2, mul_one]
  have hzero_outside : ∀ τ : Equiv.Perm α,
      τ ∉ Set.range embed → ∏ x : α, B0 (τ x) x = 0 := by
    intro τ hnot
    by_contra hne
    have hall : ∀ x : α, B0 (τ x) x ≠ 0 := fun x =>
      Finset.prod_ne_zero_iff.mp hne x (Finset.mem_univ x)
    have hinr : ∀ z : Fin r, τ (Sum.inr z) = Sum.inr z := by
      intro z
      have hz := hall (Sum.inr z)
      cases hτ : τ (Sum.inr z) with
      | inl p => simp [B0, hτ] at hz
      | inr w =>
        simp only [B0, hτ, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] at hz
        rw [hz]
    have hinl : ∀ (t : Fin k) (a : Fin m), ∃ b : Fin m, τ (Sum.inl (t, a)) = Sum.inl (t, b) := by
      intro t a
      have ha := hall (Sum.inl (t, a))
      cases hτ : τ (Sum.inl (t, a)) with
      | inr w => simp [B0, hτ] at ha
      | inl p =>
        rcases p with ⟨t', b⟩
        simp only [B0, hτ] at ha
        have ht : t' = t := by
          by_contra hne'
          simp [hne'] at ha
        subst ht
        exact ⟨b, rfl⟩
    let σ : Fin k → Equiv.Perm (Fin m) := fun t =>
      let fn : Fin m → Fin m := fun a => Classical.choose (hinl t a)
      have hfn : ∀ a, τ (Sum.inl (t, a)) = Sum.inl (t, fn a) := fun a =>
        Classical.choose_spec (hinl t a)
      have hinj : Function.Injective fn := by
        intro a1 a2 heq
        have h1 : τ (Sum.inl (t, a1)) = τ (Sum.inl (t, a2)) := by rw [hfn a1, hfn a2, heq]
        have h2 := τ.injective h1
        exact (Prod.mk.inj (Sum.inl.inj h2)).2
      Equiv.ofBijective fn ((Fintype.bijective_iff_injective_and_card fn).mpr ⟨hinj, rfl⟩)
    apply hnot
    refine ⟨σ, ?_⟩
    apply Equiv.ext
    intro x
    cases x with
    | inr z => exact (hinr z).symm
    | inl p =>
      rcases p with ⟨t, a⟩
      exact (Classical.choose_spec (hinl t a)).symm
  rw [Matrix.permanent]
  have hsum_eq : ∑ τ : Equiv.Perm α, ∏ x : α, B0 (τ x) x =
      ∑ σ : Fin k → Equiv.Perm (Fin m), ∏ x : α, B0 (embed σ x) x := by
    symm
    refine Finset.sum_bij_ne_zero (fun σ _ _ => embed σ) ?_ ?_ ?_ ?_
    · intro _ _ _; exact Finset.mem_univ _
    · intro σ1 _ _ σ2 _ _ h; exact hembed_inj h
    · intro τ _ hne
      have hmem : τ ∈ Set.range embed := by
        by_contra hnot
        exact hne (hzero_outside τ hnot)
      rcases hmem with ⟨σ, rfl⟩
      exact ⟨σ, Finset.mem_univ _, hne, rfl⟩
    · intro _ _ _; rfl
  rw [hsum_eq]
  simp_rw [hprod_eq]
  have hps : (∑ x : Fin k → Equiv.Perm (Fin m), ∏ t : Fin k, ∏ a : Fin m, H (x t a) a) =
      ∏ _t : Fin k, ∑ τ : Equiv.Perm (Fin m), ∏ a : Fin m, H (τ a) a :=
    (Fintype.prod_sum (fun (_ : Fin k) (τ : Equiv.Perm (Fin m)) => ∏ a : Fin m, H (τ a) a)).symm
  rw [hps]
  simp [Matrix.permanent]

private lemma build_perm_from_blocks {n k m r : ℕ} (hkm : k * m + r = n)
    (sets : Fin k → Finset (Fin n))
    (hcard : ∀ t, (sets t).card = m)
    (hdisj : ∀ t1 t2, t1 ≠ t2 → Disjoint (sets t1) (sets t2)) :
    ∃ e : ((Fin k × Fin m) ⊕ Fin r) ≃ Fin n,
      ∀ t a, e (Sum.inl (t, a)) ∈ sets t := by
  let U : Finset (Fin n) := Finset.univ.biUnion sets
  have hUcard : U.card = k * m := by
    rw [Finset.card_biUnion (fun t1 _ t2 _ h => hdisj t1 t2 h)]
    simp [hcard]
  let R : Finset (Fin n) := Finset.univ \ U
  have hRcard : R.card = r := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hUcard]
    omega
  let eBlock : ∀ t : Fin k, Fin m ≃ {x : Fin n // x ∈ sets t} := fun t =>
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hcard t])
  let eRem : Fin r ≃ {x : Fin n // x ∈ R} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_coe, hRcard])
  let fn : ((Fin k × Fin m) ⊕ Fin r) → Fin n := fun x =>
    match x with
    | Sum.inl (t, a) => (eBlock t a).1
    | Sum.inr z => (eRem z).1
  have hinj : Function.Injective fn := by
    intro x y h
    cases x with
    | inl p1 =>
      rcases p1 with ⟨t1, a1⟩
      cases y with
      | inl p2 =>
        rcases p2 with ⟨t2, a2⟩
        dsimp only [fn] at h
        have ht : t1 = t2 := by
          by_contra hne
          have hmem1 : (eBlock t1 a1).1 ∈ sets t1 := (eBlock t1 a1).2
          have hmem2 : (eBlock t1 a1).1 ∈ sets t2 := h ▸ (eBlock t2 a2).2
          exact Finset.disjoint_left.mp (hdisj t1 t2 hne) hmem1 hmem2
        subst ht
        have ha : a1 = a2 := (eBlock t1).injective (Subtype.ext h)
        rw [ha]
      | inr z2 =>
        dsimp only [fn] at h
        exfalso
        have h1 : (eRem z2).1 ∈ U := Finset.mem_biUnion.mpr ⟨t1, Finset.mem_univ _, h ▸ (eBlock t1 a1).2⟩
        have h2 : (eRem z2).1 ∉ U := (Finset.mem_sdiff.mp (eRem z2).2).2
        exact h2 h1
    | inr z1 =>
      cases y with
      | inl p2 =>
        rcases p2 with ⟨t2, a2⟩
        dsimp only [fn] at h
        exfalso
        have h1 : (eRem z1).1 ∈ U := Finset.mem_biUnion.mpr ⟨t2, Finset.mem_univ _, h.symm ▸ (eBlock t2 a2).2⟩
        have h2 : (eRem z1).1 ∉ U := (Finset.mem_sdiff.mp (eRem z1).2).2
        exact h2 h1
      | inr z2 =>
        dsimp only [fn] at h
        rw [(eRem).injective (Subtype.ext h)]
  have hcard_eq : Fintype.card ((Fin k × Fin m) ⊕ Fin r) = Fintype.card (Fin n) := by
    simp [hkm]
  let e : ((Fin k × Fin m) ⊕ Fin r) ≃ Fin n :=
    Equiv.ofBijective fn ((Fintype.bijective_iff_injective_and_card fn).mpr ⟨hinj, hcard_eq⟩)
  exact ⟨e, fun t a => (eBlock t a).2⟩

private lemma det_sq_signed_block {k m r : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (pat : Fin k → Fin m → Bool) (tailSign : Fin r → Bool) :
    Matrix.det (fun x y : (Fin k × Fin m) ⊕ Fin r => match x, y with
      | Sum.inl (t1, a), Sum.inl (t2, b) =>
          if t1 = t2 then (if pat t1 b then -H a b else H a b) else 0
      | Sum.inr u, Sum.inr v =>
          if u = v then (if tailSign u then -1 else 1) else 0
      | _, _ => 0) ^ 2 = (H.det ^ 2) ^ k := by
  let M0 : Matrix ((Fin k × Fin m) ⊕ Fin r) ((Fin k × Fin m) ⊕ Fin r) ℝ :=
    fun x y => match x, y with
      | Sum.inl (t1, a), Sum.inl (t2, b) =>
          if t1 = t2 then (if pat t1 b then -H a b else H a b) else 0
      | Sum.inr u, Sum.inr v =>
          if u = v then (if tailSign u then -1 else 1) else 0
      | _, _ => 0
  change M0.det ^ 2 = (H.det ^ 2) ^ k
  let B : Fin k → Matrix (Fin m) (Fin m) ℝ := fun t a b =>
    if pat t b then -H a b else H a b
  let UL : Matrix (Fin k × Fin m) (Fin k × Fin m) ℝ :=
    (Matrix.blockDiagonal B).submatrix (Equiv.prodComm (Fin k) (Fin m)) (Equiv.prodComm (Fin k) (Fin m))
  let LR : Matrix (Fin r) (Fin r) ℝ :=
    Matrix.diagonal (fun u : Fin r => if tailSign u then (-1 : ℝ) else 1)
  have hM0 : M0 = Matrix.fromBlocks UL 0 0 LR := by
    ext x y
    cases x with
    | inl p1 =>
      rcases p1 with ⟨t1, a⟩
      cases y with
      | inl p2 =>
        rcases p2 with ⟨t2, b⟩
        rw [Matrix.fromBlocks_apply₁₁]
        dsimp only [UL]
        rw [Matrix.submatrix_apply, Equiv.prodComm_apply, Equiv.prodComm_apply,
          Prod.swap_prod_mk, Prod.swap_prod_mk, Matrix.blockDiagonal_apply]
      | inr v => simp [M0]
    | inr u =>
      cases y with
      | inl p2 => simp [M0]
      | inr v =>
        simp only [M0, Matrix.fromBlocks_apply₂₂, LR, Matrix.diagonal_apply]
  have hdetM0 : M0.det = UL.det * LR.det := by
    rw [hM0, Matrix.det_fromBlocks_zero₂₁]
  have hdetUL : UL.det = ∏ t : Fin k, (B t).det := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_blockDiagonal]
  have hdetB_sq : ∀ t : Fin k, (B t).det ^ 2 = H.det ^ 2 := by
    intro t
    let D : Matrix (Fin m) (Fin m) ℝ :=
      Matrix.diagonal (fun b : Fin m => if pat t b then (-1 : ℝ) else 1)
    have hBt : B t = H * D := by
      ext a b
      simp only [B, D, Matrix.mul_diagonal]
      by_cases h : pat t b = true <;> simp [h]
    rw [hBt, Matrix.det_mul, Matrix.det_diagonal, mul_pow]
    have hprod_sq : (∏ b : Fin m, (if pat t b then (-1 : ℝ) else 1)) ^ 2 = 1 := by
      rw [← Finset.prod_pow]
      apply Finset.prod_eq_one
      intro b _
      by_cases h : pat t b = true <;> simp [h]
    rw [hprod_sq, mul_one]
  have hdetLR_sq : LR.det ^ 2 = 1 := by
    rw [Matrix.det_diagonal, ← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro u _
    by_cases h : tailSign u = true <;> simp [h]
  rw [hdetM0, mul_pow, hdetLR_sq, mul_one, hdetUL, ← Finset.prod_pow]
  simp only [hdetB_sq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private lemma det_sq_submatrix_equivs {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e1 e2 : β ≃ α) (M : Matrix α α ℝ) :
    M.det ^ 2 = (M.submatrix e1 e2).det ^ 2 := by
  let π : Equiv.Perm α := e1.symm.trans e2
  have h1 : M.submatrix e1 e2 = (M.submatrix id π).submatrix e1 e1 := by
    ext i j
    simp [Matrix.submatrix_apply, π]
  rw [h1, Matrix.det_submatrix_equiv_self]
  have h2 : (M.submatrix id π).det = (Equiv.Perm.sign π : ℝ) * M.det := by
    rw [← Matrix.det_transpose]
    have htr : (M.submatrix id π).transpose = M.transpose.submatrix π id := rfl
    rw [htr, Matrix.det_permute, Matrix.det_transpose]
  rw [h2, mul_pow]
  have hsign_sq : ((Equiv.Perm.sign π : ℝ)) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [hsign_sq, one_mul]

end PEqualNP.Outside.L_lib_980_aux

theorem PEqualNP.Outside.L_lib_980 : (∀ (m d k n : ℕ), 0 < m → 0 < d → k*m + m*4^m ≤ n →
  let J := Fin m
  let I := Fin n
  let binary := fun (A : Matrix J J ℝ) => ∀ i j, A i j = 0 ∨ A i j = 1
  ∀ H : Matrix J J ℝ, binary H →
    (∀ i, ((Finset.univ : Finset J).filter (fun j => H i j = 1)).card ≤ d) →
    (∀ j, ((Finset.univ : Finset J).filter (fun i => H i j = 1)).card ≤ d) →
    ∃ B : Matrix I I ℝ, (∀ i j, B i j = 0 ∨ B i j = 1) ∧
      (∀ i, ((Finset.univ : Finset I).filter (fun j => B i j = 1)).card ≤ d) ∧
      (∀ j, ((Finset.univ : Finset I).filter (fun i => B i j = 1)).card ≤ d) ∧
      B.permanent = H.permanent^k ∧
      ∀ s : I × I → Bool, ∃ u v : Equiv.Perm I,
        let A : Matrix I I ℝ := fun i j => B (u i) (v j)
        (Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix I I ℝ))^2 =
          (H.det^2)^k) := by
  intro m d k n hm hd hbound J I binary H hbin hrow hcol
  let r : ℕ := n - k * m
  have hkm : k * m + r = n := by omega
  let E : Fin n ≃ ((Fin k × Fin m) ⊕ Fin r) :=
    ((Equiv.sumCongr (finProdFinEquiv (m := k) (n := m)) (Equiv.refl (Fin r))).trans
      (finSumFinEquiv.trans (finCongr hkm))).symm
  let B0 : Matrix ((Fin k × Fin m) ⊕ Fin r) ((Fin k × Fin m) ⊕ Fin r) ℝ :=
    fun x y => match x, y with
      | Sum.inl (t1, a), Sum.inl (t2, b) => if t1 = t2 then H a b else 0
      | Sum.inr u, Sum.inr v => if u = v then 1 else 0
      | _, _ => 0
  let B : Matrix (Fin n) (Fin n) ℝ := B0.submatrix E E
  refine ⟨B, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    simp only [B, Matrix.submatrix_apply]
    cases E i with
    | inl p1 =>
      cases E j with
      | inl p2 =>
        dsimp only [B0]
        split_ifs
        · exact hbin p1.2 p2.2
        · exact Or.inl rfl
      | inr _ => exact Or.inl rfl
    | inr u =>
      cases E j with
      | inl _ => exact Or.inl rfl
      | inr v =>
        dsimp only [B0]
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
  · intro i
    have hcard_eq : ((Finset.univ : Finset (Fin n)).filter (fun j => B i j = 1)).card =
        ((Finset.univ : Finset ((Fin k × Fin m) ⊕ Fin r)).filter (fun y => B0 (E i) y = 1)).card := by
      refine Finset.card_bij (fun j _ => E j) ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
      · intro j1 _ j2 _ h; exact E.injective h
      · intro y hy
        refine ⟨E.symm y, ?_, E.apply_symm_apply y⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          change B0 (E i) (E (E.symm y)) = 1
          rw [E.apply_symm_apply]
          exact (Finset.mem_filter.mp hy).2⟩
    rw [hcard_eq]
    cases hEi : E i with
    | inl p =>
      rcases p with ⟨t, a⟩
      have hcard_inl : ((Finset.univ : Finset ((Fin k × Fin m) ⊕ Fin r)).filter
          (fun y => B0 (Sum.inl (t, a)) y = 1)).card =
          ((Finset.univ : Finset (Fin m)).filter (fun b => H a b = 1)).card := by
        refine Finset.card_bij (fun y hy => match y with | Sum.inl (_, b) => b | Sum.inr _ => ⟨0, hm⟩) ?_ ?_ ?_
        · intro y hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
          cases y with
          | inl q =>
            simp only [B0] at hy
            split_ifs at hy with ht
            · exact hy
            · norm_num at hy
          | inr _ => simp [B0] at hy
        · intro y1 hy1 y2 hy2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2
          cases y1 with
          | inr _ => simp [B0] at hy1
          | inl q1 =>
            cases y2 with
            | inr _ => simp [B0] at hy2
            | inl q2 =>
              simp only [B0] at hy1 hy2
              have ht1 : t = q1.1 := by by_contra h; simp [h] at hy1
              have ht2 : t = q2.1 := by by_contra h; simp [h] at hy2
              congr 1
              exact Prod.ext (ht1.symm.trans ht2) heq
        · intro b hb
          refine ⟨Sum.inl (t, b), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, B0, ↓reduceIte] at hb ⊢
          exact hb
      rw [hcard_inl]
      exact hrow a
    | inr u =>
      have hsub : (Finset.univ : Finset ((Fin k × Fin m) ⊕ Fin r)).filter
          (fun y => B0 (Sum.inr u) y = 1) ⊆ {Sum.inr u} := by
        intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        cases y with
        | inl _ => simp [B0] at hy
        | inr v =>
          simp only [B0] at hy
          have huv : u = v := by by_contra h; simp [h] at hy
          subst huv
          exact Finset.mem_singleton_self _
      exact (Finset.card_le_card hsub).trans (by simp; omega)
  · intro j
    have hcard_eq : ((Finset.univ : Finset (Fin n)).filter (fun i => B i j = 1)).card =
        ((Finset.univ : Finset ((Fin k × Fin m) ⊕ Fin r)).filter (fun x => B0 x (E j) = 1)).card := by
      refine Finset.card_bij (fun i _ => E i) ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · intro i1 _ i2 _ h; exact E.injective h
      · intro x hx
        refine ⟨E.symm x, ?_, E.apply_symm_apply x⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
          change B0 (E (E.symm x)) (E j) = 1
          rw [E.apply_symm_apply]
          exact (Finset.mem_filter.mp hx).2⟩
    rw [hcard_eq]
    cases hEj : E j with
    | inl p =>
      rcases p with ⟨t, b⟩
      have hcard_inl : ((Finset.univ : Finset ((Fin k × Fin m) ⊕ Fin r)).filter
          (fun x => B0 x (Sum.inl (t, b)) = 1)).card =
          ((Finset.univ : Finset (Fin m)).filter (fun a => H a b = 1)).card := by
        refine Finset.card_bij (fun x hx => match x with | Sum.inl (_, a) => a | Sum.inr _ => ⟨0, hm⟩) ?_ ?_ ?_
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          cases x with
          | inl q =>
            simp only [B0] at hx
            split_ifs at hx with ht
            · exact hx
            · norm_num at hx
          | inr _ => simp [B0] at hx
        · intro x1 hx1 x2 hx2 heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
          cases x1 with
          | inr _ => simp [B0] at hx1
          | inl q1 =>
            cases x2 with
            | inr _ => simp [B0] at hx2
            | inl q2 =>
              simp only [B0] at hx1 hx2
              have ht1 : q1.1 = t := by by_contra h; simp [h] at hx1
              have ht2 : q2.1 = t := by by_contra h; simp [h] at hx2
              congr 1
              exact Prod.ext (ht1.trans ht2.symm) heq
        · intro a ha
          refine ⟨Sum.inl (t, a), ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, B0, ↓reduceIte] at ha ⊢
          exact ha
      rw [hcard_inl]
      exact hcol b
    | inr v =>
      have hsub : (Finset.univ : Finset ((Fin k × Fin m) ⊕ Fin r)).filter
          (fun x => B0 x (Sum.inr v) = 1) ⊆ {Sum.inr v} := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        cases x with
        | inl _ => simp [B0] at hx
        | inr u =>
          simp only [B0] at hx
          have huv : u = v := by by_contra h; simp [h] at hx
          subst huv
          exact Finset.mem_singleton_self _
      exact (Finset.card_le_card hsub).trans (by simp; omega)
  · rw [PEqualNP.Outside.L_lib_980_aux.permanent_submatrix_equiv E B0]
    convert PEqualNP.Outside.L_lib_980_aux.permanent_block_H_id k m r H using 1
    congr 1
    ext x y
    cases x <;> cases y <;> rfl
  · intro s
    rcases PEqualNP.Outside.L_lib_980_aux.extract_blocks hm s k Finset.univ Finset.univ
        (by simpa using hbound) (by simpa using hbound) with
      ⟨rows, cols, pat, _, _, hrows_card, hcols_card, hrows_disj, hcols_disj, hpat⟩
    rcases PEqualNP.Outside.L_lib_980_aux.build_perm_from_blocks hkm rows hrows_card hrows_disj with
      ⟨uInv, huInv⟩
    rcases PEqualNP.Outside.L_lib_980_aux.build_perm_from_blocks hkm cols hcols_card hcols_disj with
      ⟨vInv, hvInv⟩
    let u : Equiv.Perm (Fin n) := uInv.symm.trans E.symm
    let v : Equiv.Perm (Fin n) := vInv.symm.trans E.symm
    refine ⟨u, v, ?_⟩
    let M : Matrix (Fin n) (Fin n) ℝ :=
      fun i j => if s (i, j) then -B (u i) (v j) else B (u i) (v j)
    change M.det ^ 2 = (H.det ^ 2) ^ k
    rw [PEqualNP.Outside.L_lib_980_aux.det_sq_submatrix_equivs uInv vInv M]
    let pat' : Fin k → Fin m → Bool := fun t b => pat t (vInv (Sum.inl (t, b)))
    let tailSign : Fin r → Bool := fun z => s (uInv (Sum.inr z), vInv (Sum.inr z))
    have hMsub : M.submatrix uInv vInv =
        (fun x y => match x, y with
          | Sum.inl (t1, a), Sum.inl (t2, b) =>
              if t1 = t2 then (if pat' t1 b then -H a b else H a b) else 0
          | Sum.inr z1, Sum.inr z2 =>
              if z1 = z2 then (if tailSign z1 then -1 else 1) else 0
          | _, _ => 0) := by
      ext x y
      change M (uInv x) (vInv y) = _
      dsimp only [M, B, u, v]
      rw [Matrix.submatrix_apply, Equiv.trans_apply, Equiv.trans_apply,
        Equiv.symm_apply_apply, Equiv.symm_apply_apply,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      cases x with
      | inl p1 =>
        rcases p1 with ⟨t1, a⟩
        cases y with
        | inl p2 =>
          rcases p2 with ⟨t2, b⟩
          dsimp only [B0]
          by_cases ht : t1 = t2
          · subst ht
            have hs := hpat t1 (uInv (Sum.inl (t1, a))) (huInv t1 a)
              (vInv (Sum.inl (t1, b))) (hvInv t1 b)
            simp [pat', hs]
          · simp [ht]
        | inr z2 => simp [B0]
      | inr z1 =>
        cases y with
        | inl p2 => simp [B0]
        | inr z2 =>
          dsimp only [B0, tailSign]
          by_cases hz : z1 = z2
          · subst hz; simp
          · simp [hz]
    rw [hMsub]
    convert PEqualNP.Outside.L_lib_980_aux.det_sq_signed_block H pat' tailSign using 2
    congr 1
    ext x y
    cases x <;> cases y <;> rfl
