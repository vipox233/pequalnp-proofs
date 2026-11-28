import Mathlib

namespace PEqualNP.Outside.L_lib_1078_aux

open AlgebraicIndependent

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem trdeg_contra {N : ℕ} (t : Fin N → L) (ht : AlgebraicIndependent F t) (B : Set L)
    (hB : B.encard < N) (hcl : ∀ h, t h ∈ (matroid F L).closure B) : False := by
  have hind : (matroid F L).Indep (Set.range t) := by
    rw [matroid_indep_iff]
    exact ht.to_subtype_range
  have h1 : (Set.range t).encard = N := by
    rw [ht.injective.encard_range]
    simp
  have h2 := hind.encard_le_eRk_of_subset (X := (matroid F L).closure B)
    (by rintro _ ⟨h, rfl⟩; exact hcl h)
  rw [Matroid.eRk_closure_eq] at h2
  have h3 := (matroid F L).eRk_le_encard B
  have : (N : ℕ∞) < N := by
    calc (N : ℕ∞) = (Set.range t).encard := h1.symm
      _ ≤ _ := h2
      _ ≤ _ := h3
      _ < N := hB
  exact lt_irrefl _ this

theorem mem_closure_of_isAlgebraic (s : Set L) (z : L)
    (hz : IsAlgebraic (Algebra.adjoin F s) z) : z ∈ (matroid F L).closure s := by
  rw [matroid_closure_eq]
  exact (Subalgebra.mem_algebraicClosure _ _).2 hz

theorem mem_closure_of_pow (s : Set L) (z : L) (M : ℕ) (hM : 0 < M)
    (hz : z ^ M ∈ IntermediateField.adjoin F s) : z ∈ (matroid F L).closure s := by
  apply mem_closure_of_isAlgebraic
  rw [← IntermediateField.isAlgebraic_adjoin_iff]
  refine ⟨Polynomial.X ^ M - Polynomial.C ⟨z ^ M, hz⟩, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero hM _
  · simp

def mu {κ : Type*} [Fintype κ] (z : κ → L) (v : κ → ℤ) : L := ∏ s, z s ^ v s

theorem mu_zero {κ : Type*} [Fintype κ] (z : κ → L) : mu z 0 = 1 := by
  simp [mu]

theorem mu_add {κ : Type*} [Fintype κ] (z : κ → L) (hz : ∀ s, z s ≠ 0) (v w : κ → ℤ) :
    mu z (v + w) = mu z v * mu z w := by
  unfold mu
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Pi.add_apply, zpow_add₀ (hz s)]

theorem mu_smul {κ : Type*} [Fintype κ] (z : κ → L) (n : ℤ) (v : κ → ℤ) :
    mu z (n • v) = mu z v ^ n := by
  unfold mu
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]

theorem mu_sum {κ ι : Type*} [Fintype κ] (z : κ → L) (hz : ∀ s, z s ≠ 0) (S : Finset ι)
    (f : ι → κ → ℤ) : mu z (∑ l ∈ S, f l) = ∏ l ∈ S, mu z (f l) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mu_zero]
  | insert l S hl ih => rw [Finset.sum_insert hl, Finset.prod_insert hl, mu_add z hz, ih]

theorem exists_clear_denom {κ : Type*} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∃ n : κ → ℤ, ∀ l, (n l : ℚ) = q l * M := by
  refine ⟨∏ l, (q l).den, Finset.prod_pos fun l _ => (q l).den_pos, fun l =>
    (q l).num * (((∏ l, (q l).den) / (q l).den : ℕ) : ℤ), fun l => ?_⟩
  have hd : (q l).den ∣ ∏ l, (q l).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ l)
  have hd0 : ((q l).den : ℚ) ≠ 0 := by exact_mod_cast (q l).den_nz
  have hq : q l = (q l).num / (q l).den := (Rat.num_div_den _).symm
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hd hd0]
  calc ((q l).num : ℚ) * (((∏ l, (q l).den : ℕ) : ℚ) / ((q l).den : ℚ))
      = ((q l).num / (q l).den) * ((∏ l, (q l).den : ℕ) : ℚ) := by ring
    _ = q l * ((∏ l, (q l).den : ℕ) : ℚ) := by rw [← hq]

theorem lattice_closure {κ ι : Type*} [Fintype κ] [Fintype ι] (z : κ → L) (hz : ∀ s, z s ≠ 0)
    (e : ι → κ → ℤ) :
    ∃ B : Set L, B.encard ≤ Module.finrank ℚ
        (Submodule.span ℚ (Set.range (fun i s => (e i s : ℚ)))) ∧
      ∀ i, mu z (e i) ∈ (matroid F L).closure B := by
  obtain ⟨κ', a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ (fun i s => (e i s : ℚ))
  have : Finite κ' := Finite.of_injective a ha
  have := Fintype.ofFinite κ'
  refine ⟨Set.range (fun l => mu z (e (a l))), ?_, fun i => ?_⟩
  · rw [← hspan, finrank_span_eq_card hli]
    calc (Set.range (fun l => mu z (e (a l)))).encard ≤ (Set.univ : Set κ').encard := by
          rw [← Set.image_univ]; exact Set.encard_image_le _ _
      _ = _ := by simp
  · have hmem : (fun s => (e i s : ℚ)) ∈ Submodule.span ℚ (Set.range
        ((fun i s => (e i s : ℚ)) ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span (Set.mem_range_self i)
    obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hmem
    obtain ⟨M, hM, n, hn⟩ := exists_clear_denom q
    have hint : (M : ℤ) • e i = ∑ l, n l • e (a l) := by
      funext s
      apply Int.cast_injective (α := ℚ)
      have := congrFun hq s
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul] at this
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Int.cast_mul, Int.cast_sum,
        Int.cast_natCast, hn]
      rw [← this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    apply mem_closure_of_pow _ _ M hM
    rw [← zpow_natCast, ← mu_smul, hint, mu_sum z hz]
    refine IntermediateField.prod_mem _ fun l _ => ?_
    rw [mu_smul]
    exact zpow_mem (IntermediateField.subset_adjoin _ _ (Set.mem_range_self l)) _

def incL (p : ℕ) : (Fin p → ℚ) →ₗ[ℚ] (Fin p ⊕ Fin p → ℚ) where
  toFun v := Sum.elim v 0
  map_add' v w := by funext s; cases s <;> simp
  map_smul' c v := by funext s; cases s <;> simp

def incR (p : ℕ) : (Fin p → ℚ) →ₗ[ℚ] (Fin p ⊕ Fin p → ℚ) where
  toFun v := Sum.elim 0 v
  map_add' v w := by funext s; cases s <;> simp
  map_smul' c v := by funext s; cases s <;> simp

def sumF (p : ℕ) : (Fin p ⊕ Fin p → ℚ) →ₗ[ℚ] ℚ where
  toFun v := ∑ s, v s
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

theorem sumF_incL (p : ℕ) (v : Fin p → ℚ) : sumF p (incL p v) = ∑ i, v i := by
  simp [sumF, incL, Fintype.sum_sum_type]

theorem sumF_incR (p : ℕ) (v : Fin p → ℚ) : sumF p (incR p v) = ∑ i, v i := by
  simp [sumF, incR, Fintype.sum_sum_type]

def expVec {p m : ℕ} (a : Fin m → Fin p → ℕ) (j0 : Fin m) : Fin m ⊕ Fin m → (Fin p ⊕ Fin p → ℤ)
  | Sum.inl j => Sum.elim (fun i => (a j i : ℤ) - a j0 i) 0
  | Sum.inr j => Sum.elim (fun i => -(a j0 i : ℤ)) (fun i => (a j i : ℤ))

theorem expVec_cast_inl {p m : ℕ} (a : Fin m → Fin p → ℕ) (j0 j : Fin m) :
    (fun s => (expVec a j0 (Sum.inl j) s : ℚ)) =
      incL p (fun i => (a j i : ℚ)) - incL p (fun i => (a j0 i : ℚ)) := by
  funext s; cases s <;> simp [expVec, incL]

theorem expVec_cast_inr {p m : ℕ} (a : Fin m → Fin p → ℕ) (j0 j : Fin m) :
    (fun s => (expVec a j0 (Sum.inr j) s : ℚ)) =
      incR p (fun i => (a j i : ℚ)) - incL p (fun i => (a j0 i : ℚ)) := by
  funext s; cases s <;> simp [expVec, incL, incR]

theorem finrank_expVec_lt {p m k : ℕ} (a : Fin m → Fin p → ℕ) (hk : 0 < k)
    (hdeg : ∀ j, (∑ i : Fin p, a j i) = k) (j0 : Fin m) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (fun ι s => (expVec a j0 ι s : ℚ)))) <
      2 * Module.finrank ℚ (Submodule.span ℚ (Set.range
        (fun j : Fin m => fun i : Fin p => (a j i : ℚ)))) := by
  set V := Submodule.span ℚ (Set.range (fun j : Fin m => fun i : Fin p => (a j i : ℚ))) with hV
  set S := Submodule.span ℚ (Set.range (fun ι s => (expVec a j0 ι s : ℚ))) with hS
  set W2 := V.map (incL p) ⊔ V.map (incR p) with hW2
  have hA : ∀ j, (fun i : Fin p => (a j i : ℚ)) ∈ V := fun j =>
    Submodule.subset_span (Set.mem_range_self j)
  have hsum : ∀ j, ∑ i : Fin p, (a j i : ℚ) = k := by
    intro j; rw [← hdeg j]; push_cast; rfl
  have hSW : S ≤ W2 := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨ι, rfl⟩
    cases ι with
    | inl j =>
      show (fun s => (expVec a j0 (Sum.inl j) s : ℚ)) ∈ W2
      rw [expVec_cast_inl]
      exact W2.sub_mem (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hA j)))
        (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hA j0)))
    | inr j =>
      show (fun s => (expVec a j0 (Sum.inr j) s : ℚ)) ∈ W2
      rw [expVec_cast_inr]
      exact W2.sub_mem (Submodule.mem_sup_right (Submodule.mem_map_of_mem (hA j)))
        (Submodule.mem_sup_left (Submodule.mem_map_of_mem (hA j0)))
  have hSker : S ≤ LinearMap.ker (sumF p) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨ι, rfl⟩
    cases ι with
    | inl j =>
      show (fun s => (expVec a j0 (Sum.inl j) s : ℚ)) ∈ LinearMap.ker (sumF p)
      rw [LinearMap.mem_ker]
      rw [expVec_cast_inl, map_sub, sumF_incL, sumF_incL, hsum, hsum, sub_self]
    | inr j =>
      show (fun s => (expVec a j0 (Sum.inr j) s : ℚ)) ∈ LinearMap.ker (sumF p)
      rw [LinearMap.mem_ker]
      rw [expVec_cast_inr, map_sub, sumF_incR, sumF_incL, hsum, hsum, sub_self]
  have hlt : S < W2 := by
    rw [IsConcreteLE.lt_iff_le_and_exists]
    refine ⟨hSW, incL p (fun i => (a j0 i : ℚ)),
      Submodule.mem_sup_left (Submodule.mem_map_of_mem (hA j0)), fun hmem => ?_⟩
    have := hSker hmem
    rw [LinearMap.mem_ker, sumF_incL, hsum] at this
    exact hk.ne' (by exact_mod_cast this)
  calc Module.finrank ℚ S < Module.finrank ℚ W2 := Submodule.finrank_lt_finrank_of_lt hlt
    _ ≤ Module.finrank ℚ (V.map (incL p)) + Module.finrank ℚ (V.map (incR p)) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ Module.finrank ℚ V + Module.finrank ℚ V :=
      Nat.add_le_add (Submodule.finrank_map_le _ _) (Submodule.finrank_map_le _ _)
    _ = 2 * Module.finrank ℚ V := by ring

section core

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

def wmon {p m : ℕ} (a : Fin m → Fin p → ℕ) (x : Fin p → L) (j : Fin m) : L := ∏ i, x i ^ a j i

open Classical in
noncomputable def nzv {p : ℕ} (x : Fin p → L) : Fin p → L := fun i => if x i = 0 then 1 else x i

theorem nzv_ne {p : ℕ} (x : Fin p → L) (i : Fin p) : nzv x i ≠ 0 := by
  unfold nzv; split_ifs with h
  · exact one_ne_zero
  · exact h

noncomputable def pmon {p m : ℕ} (a : Fin m → Fin p → ℕ) (x : Fin p → L) (j : Fin m) : L :=
  ∏ i, nzv x i ^ (a j i : ℤ)

theorem wmon_eq_pmon {p m : ℕ} (a : Fin m → Fin p → ℕ) (x : Fin p → L) (j : Fin m)
    (hw : wmon a x j ≠ 0) : wmon a x j = pmon a x j := by
  unfold wmon pmon
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_natCast]
  unfold nzv
  split_ifs with h
  · have : a j i = 0 := by
      by_contra hne
      apply hw
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; exact zero_pow hne)
    rw [this, h]; simp
  · rfl

theorem pmon_ne {p m : ℕ} (a : Fin m → Fin p → ℕ) (x : Fin p → L) (j : Fin m) :
    pmon a x j ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (nzv_ne x i)

theorem mu_expVec_inl {p m : ℕ} (a : Fin m → Fin p → ℕ) (j0 j : Fin m) (x y : Fin p → L) :
    mu (Sum.elim (nzv x) (nzv y)) (expVec a j0 (Sum.inl j)) = pmon a x j / pmon a x j0 := by
  unfold mu pmon
  rw [Fintype.prod_sum_type, ← Finset.prod_div_distrib]
  simp only [expVec, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero,
    Finset.prod_const_one, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [zpow_sub₀ (nzv_ne x i)]

theorem mu_expVec_inr {p m : ℕ} (a : Fin m → Fin p → ℕ) (j0 j : Fin m) (x y : Fin p → L) :
    mu (Sum.elim (nzv x) (nzv y)) (expVec a j0 (Sum.inr j)) = pmon a y j / pmon a x j0 := by
  unfold mu pmon
  rw [Fintype.prod_sum_type, div_eq_mul_inv, mul_comm, ← Finset.prod_inv_distrib]
  simp only [expVec, Sum.elim_inl, Sum.elim_inr, zpow_neg]

theorem core {p m k N : ℕ} (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → F)
    (hk : 0 < k) (hdeg : ∀ j, (∑ i : Fin p, a j i) = k) (hcode : Function.Injective code)
    (hc : ∀ j, c j ≠ 0)
    (hN : 2 * Module.finrank ℚ (Submodule.span ℚ (Set.range
        (fun j : Fin m => fun i : Fin p => (a j i : ℚ)))) ≤ N)
    (t : Fin N → L) (ht : AlgebraicIndependent F t) (x y : Fin p → L)
    (heq : ∀ h, ∑ j, algebraMap F L (c j) * (wmon a x j - wmon a y j) * t h ^ code j = 0)
    (j0 : Fin m) (hne : wmon a x j0 ≠ wmon a y j0) (hx0 : wmon a x j0 ≠ 0) : False := by
  classical
  set z : Fin p ⊕ Fin p → L := Sum.elim (nzv x) (nzv y) with hz
  have hz0 : ∀ s, z s ≠ 0 := by
    intro s; cases s with
    | inl i => exact nzv_ne x i
    | inr i => exact nzv_ne y i
  obtain ⟨B, hBcard, hBcl⟩ := lattice_closure (F := F) z hz0 (expVec a j0)
  have hlt := finrank_expVec_lt a hk hdeg j0
  set u0 := wmon a x j0 with hu0
  set ρx : Fin m → L := fun j => wmon a x j / u0 with hρx
  set ρy : Fin m → L := fun j => wmon a y j / u0 with hρy
  have hu0p : u0 = pmon a x j0 := wmon_eq_pmon a x j0 hx0
  have h0cl : (0 : L) ∈ (matroid F L).closure B :=
    mem_closure_of_isAlgebraic _ _ isAlgebraic_zero
  have hρxcl : ∀ j, ρx j ∈ (matroid F L).closure B := by
    intro j
    by_cases hw : wmon a x j = 0
    · simp only [hρx, hw, zero_div]; exact h0cl
    · have := hBcl (Sum.inl j)
      rw [mu_expVec_inl] at this
      simp only [hρx]
      rw [wmon_eq_pmon a x j hw, hu0p]
      exact this
  have hρycl : ∀ j, ρy j ∈ (matroid F L).closure B := by
    intro j
    by_cases hw : wmon a y j = 0
    · simp only [hρy, hw, zero_div]; exact h0cl
    · have := hBcl (Sum.inr j)
      rw [mu_expVec_inr] at this
      simp only [hρy]
      rw [wmon_eq_pmon a y j hw, hu0p]
      exact this
  set C : Set L := Set.range ρx ∪ Set.range ρy with hC
  have hCB : C ⊆ (matroid F L).closure B := by
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact hρxcl j
    · exact hρycl j
  have htC : ∀ h, t h ∈ (matroid F L).closure C := by
    intro h
    apply mem_closure_of_isAlgebraic
    set S := Algebra.adjoin F C
    have hxS : ∀ j, ρx j ∈ S := fun j =>
      Algebra.subset_adjoin (Or.inl (Set.mem_range_self j))
    have hyS : ∀ j, ρy j ∈ S := fun j =>
      Algebra.subset_adjoin (Or.inr (Set.mem_range_self j))
    let coef : Fin m → S := fun j => algebraMap F S (c j) * (⟨ρx j, hxS j⟩ - ⟨ρy j, hyS j⟩)
    have hcoef : ∀ j, (coef j : L) = algebraMap F L (c j) * (ρx j - ρy j) := by
      intro j; rfl
    refine ⟨∑ j, Polynomial.C (coef j) * Polynomial.X ^ code j, ?_, ?_⟩
    · intro hP
      have := congrArg (fun P : Polynomial S => P.coeff (code j0)) hP
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single j0] at this
      · simp only [ite_true] at this
        have h2 := congrArg (fun s : S => (s : L)) this
        simp only [hcoef, ZeroMemClass.coe_zero] at h2
        rcases mul_eq_zero.1 h2 with h3 | h3
        · exact hc j0 ((map_eq_zero_iff _ (algebraMap F L).injective).1 h3)
        · apply hne
          have h4 : (wmon a x j0 - wmon a y j0) / u0 = 0 := by
            rw [sub_div]; exact h3
          rcases div_eq_zero_iff.1 h4 with h5 | h5
          · exact sub_eq_zero.1 h5
          · exact absurd h5 hx0
      · intro j _ hj
        exact ite_eq_right_iff.2 (fun h => absurd (hcode h).symm hj)
      · intro hj; exact absurd (Finset.mem_univ j0) hj
    · rw [map_sum]
      simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      have : ∀ j, (algebraMap S L (coef j)) * t h ^ code j =
          (algebraMap F L (c j) * (wmon a x j - wmon a y j) * t h ^ code j) / u0 := by
        intro j
        rw [show algebraMap S L (coef j) = (coef j : L) from rfl, hcoef]
        simp only [hρx, hρy]
        field_simp
      rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_div, heq h, zero_div]
  have htB : ∀ h, t h ∈ (matroid F L).closure B := fun h =>
    Matroid.closure_subset_closure_of_subset_closure hCB (htC h)
  refine trdeg_contra t ht B ?_ htB
  calc B.encard ≤ _ := hBcard
    _ < (N : ℕ∞) := by exact_mod_cast lt_of_lt_of_le hlt hN

theorem core' {p m k N : ℕ} (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → F)
    (hk : 0 < k) (hdeg : ∀ j, (∑ i : Fin p, a j i) = k) (hcode : Function.Injective code)
    (hc : ∀ j, c j ≠ 0)
    (hN : 2 * Module.finrank ℚ (Submodule.span ℚ (Set.range
        (fun j : Fin m => fun i : Fin p => (a j i : ℚ)))) ≤ N)
    (t : Fin N → L) (ht : AlgebraicIndependent F t) (x y : Fin p → L)
    (heq : ∀ h, ∑ j, algebraMap F L (c j) * (wmon a x j - wmon a y j) * t h ^ code j = 0)
    (j0 : Fin m) (hne : wmon a x j0 ≠ wmon a y j0) : False := by
  by_cases hx0 : wmon a x j0 = 0
  · refine core a code c hk hdeg hcode hc hN t ht y x ?_ j0 (Ne.symm hne) ?_
    · intro h
      have := heq h
      rw [← neg_eq_zero, ← Finset.sum_neg_distrib] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    · rw [hx0] at hne; exact Ne.symm hne
  · exact core a code c hk hdeg hcode hc hN t ht x y heq j0 hne hx0

end core

section reduction

open MvPolynomial

variable {p m N : ℕ}

noncomputable def wX (a : Fin m → Fin p → ℕ) (j : Fin m) :
    MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m)) (MvPolynomial (Fin N) ℂ) :=
  ∏ i, (X (Sum.inl i)) ^ (a j i)

noncomputable def wY (a : Fin m → Fin p → ℕ) (j : Fin m) :
    MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m)) (MvPolynomial (Fin N) ℂ) :=
  ∏ i, (X (Sum.inr (Sum.inl i))) ^ (a j i)

noncomputable def fgen (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → ℂ) (h : Fin N) :
    MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m)) (MvPolynomial (Fin N) ℂ) :=
  ∑ j, C (C (c j)) * (wX a j - wY a j) * (C (X h)) ^ (code j)

noncomputable def ggen (a : Fin m → Fin p → ℕ) :
    MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m)) (MvPolynomial (Fin N) ℂ) :=
  ∑ j, (wX (N := N) a j - wY a j) * X (Sum.inr (Sum.inr j)) - 1

noncomputable def Igen (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → ℂ) :
    Ideal (MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m)) (MvPolynomial (Fin N) ℂ)) :=
  Ideal.span (Set.range (fgen a code c) ∪ {ggen a})

theorem phi_wX {R : Type*} [Field R] (φ : MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m))
    (MvPolynomial (Fin N) ℂ) →+* R) (a : Fin m → Fin p → ℕ) (j : Fin m) :
    φ (wX a j) = wmon a (fun i => φ (X (Sum.inl i))) j := by
  simp [wX, wmon]

theorem phi_wY {R : Type*} [Field R] (φ : MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m))
    (MvPolynomial (Fin N) ℂ) →+* R) (a : Fin m → Fin p → ℕ) (j : Fin m) :
    φ (wY a j) = wmon a (fun i => φ (X (Sum.inr (Sum.inl i)))) j := by
  simp [wY, wmon]

universe uA uB in
theorem exists_field_hom {A' : Type uA} {Bt : Type uB} [CommRing A'] [IsDomain A'] [CommRing Bt]
    (f : A' →+* Bt) (I : Ideal Bt) (h0 : ∀ a, a ≠ 0 → f a ∉ I) :
    ∃ (L : Type uB) (_ : Field L) (φ : Bt →+* L), (∀ b ∈ I, φ b = 0) ∧
      ∀ a, a ≠ 0 → φ (f a) ≠ 0 := by
  obtain ⟨P, hP, hIP, hdisj⟩ := Ideal.exists_le_prime_disjoint I
      ((nonZeroDivisors A').map f.toMonoidHom) (by
    rw [Set.disjoint_left]
    intro b hb hbS
    obtain ⟨q, hq, rfl⟩ := Submonoid.mem_map.1 hbS
    exact h0 q (nonZeroDivisors.ne_zero hq) hb)
  refine ⟨FractionRing (Bt ⧸ P), inferInstance,
    (algebraMap (Bt ⧸ P) (FractionRing (Bt ⧸ P))).comp (Ideal.Quotient.mk P), ?_, ?_⟩
  · intro b hb
    simp only [RingHom.comp_apply]
    rw [(Ideal.Quotient.eq_zero_iff_mem).2 (hIP hb), map_zero]
  intro a ha hφ
  have hnot : f a ∉ P := fun h => Set.disjoint_left.1 hdisj h
    (Submonoid.mem_map.2 ⟨a, mem_nonZeroDivisors_of_ne_zero ha, rfl⟩)
  apply hnot
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (IsFractionRing.injective (Bt ⧸ P) (FractionRing (Bt ⧸ P))) (by rw [map_zero]; exact hφ)

theorem exists_cert {k : ℕ} (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → ℂ)
    (hk : 0 < k) (hdeg : ∀ j, (∑ i : Fin p, a j i) = k) (hcode : Function.Injective code)
    (hc : ∀ j, c j ≠ 0)
    (hN : 2 * Module.finrank ℚ (Submodule.span ℚ (Set.range
        (fun j : Fin m => fun i : Fin p => (a j i : ℚ)))) ≤ N) :
    ∃ q : MvPolynomial (Fin N) ℂ, q ≠ 0 ∧ C q ∈ Igen a code c := by
  by_contra hcon
  push Not at hcon
  set I := Igen (N := N) a code c with hI
  obtain ⟨L, hL, φ, hφI, hφ0⟩ := exists_field_hom C I hcon
  let ψ : MvPolynomial (Fin N) ℂ →+* L := φ.comp C
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    by_contra hq0
    exact hφ0 q hq0 hq
  let _ : Algebra ℂ L := (ψ.comp C).toAlgebra
  let ψA : MvPolynomial (Fin N) ℂ →ₐ[ℂ] L :=
    { ψ with commutes' := fun r => by rw [MvPolynomial.algebraMap_eq]; rfl }
  have ht : AlgebraicIndependent ℂ (fun h : Fin N => ψ (X h)) :=
    (MvPolynomial.algebraicIndependent_X (Fin N) ℂ).map' (f := ψA) hψ
  have hf : ∀ h, φ (fgen a code c h) = 0 := fun h =>
    hφI _ (Ideal.subset_span (Or.inl (Set.mem_range_self h)))
  have hg : φ (ggen a) = 0 := hφI _ (Ideal.subset_span (Or.inr rfl))
  set x : Fin p → L := fun i => φ (X (Sum.inl i))
  set y : Fin p → L := fun i => φ (X (Sum.inr (Sum.inl i)))
  have heq : ∀ h, ∑ j, algebraMap ℂ L (c j) * (wmon a x j - wmon a y j) *
      (fun h : Fin N => ψ (X h)) h ^ code j = 0 := by
    intro h
    rw [← hf h]
    simp only [fgen, map_sum, map_mul, map_sub, map_pow, phi_wX, phi_wY]
    rfl
  have hex : ∃ j0, wmon a x j0 ≠ wmon a y j0 := by
    by_contra hall
    push Not at hall
    apply one_ne_zero (α := L)
    have := hg
    simp only [ggen, map_sub, map_sum, map_mul, phi_wX, phi_wY, map_one] at this
    rw [sub_eq_zero] at this
    rw [← this]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hall j, sub_self, zero_mul]
  obtain ⟨j0, hj0⟩ := hex
  exact core' a code c hk hdeg hcode hc hN _ ht x y heq j0 hj0

theorem final_step (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → ℂ)
    (q : MvPolynomial (Fin N) ℂ) (hq : C q ∈ Igen a code c) (t : Fin N → ℂ)
    (ht : MvPolynomial.eval t q ≠ 0) (x y : Fin p → ℂ)
    (hcol : ∀ h, ∑ j, c j * wmon a x j * t h ^ code j = ∑ j, c j * wmon a y j * t h ^ code j)
    (j : Fin m) : wmon a x j = wmon a y j := by
  classical
  by_contra hj
  set s : Fin m → ℂ := fun j' => if j' = j then (wmon a x j - wmon a y j)⁻¹ else 0 with hs
  let θ : MvPolynomial (Fin p ⊕ (Fin p ⊕ Fin m)) (MvPolynomial (Fin N) ℂ) →+* ℂ :=
    MvPolynomial.eval₂Hom (MvPolynomial.eval t) (Sum.elim x (Sum.elim y s))
  have hθX : ∀ i, θ (X (Sum.inl i)) = x i := fun i => by simp [θ]
  have hθY : ∀ i, θ (X (Sum.inr (Sum.inl i))) = y i := fun i => by simp [θ]
  have hθS : ∀ j', θ (X (Sum.inr (Sum.inr j'))) = s j' := fun j' => by simp [θ]
  have hθC : ∀ r : MvPolynomial (Fin N) ℂ, θ (C r) = MvPolynomial.eval t r := fun r => by
    simp [θ]
  have hθwX : ∀ j', θ (wX a j') = wmon a x j' := by
    intro j'; rw [phi_wX]; simp only [hθX]
  have hθwY : ∀ j', θ (wY a j') = wmon a y j' := by
    intro j'; rw [phi_wY]; simp only [hθY]
  have hI : Igen (N := N) a code c ≤ RingHom.ker θ := by
    rw [Igen, Ideal.span_le]
    rintro _ (⟨h, rfl⟩ | hg)
    · rw [SetLike.mem_coe, RingHom.mem_ker]
      simp only [fgen, map_sum, map_mul, map_sub, map_pow, hθwX, hθwY, hθC,
        MvPolynomial.eval_C, MvPolynomial.eval_X]
      rw [← sub_eq_zero.2 (hcol h), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j' _ => ?_
      ring
    · rw [Set.mem_singleton_iff] at hg
      rw [hg, SetLike.mem_coe, RingHom.mem_ker]
      simp only [ggen, map_sum, map_mul, map_sub, map_one, hθwX, hθwY, hθS]
      rw [Finset.sum_eq_single j]
      · simp only [hs, ↓reduceIte]
        rw [mul_inv_cancel₀ (sub_ne_zero.2 hj), sub_self]
      · intro j' _ hj'
        simp only [hs, hj', ↓reduceIte, mul_zero]
      · intro hj'; exact absurd (Finset.mem_univ j) hj'
  apply ht
  rw [← hθC]
  exact hI hq

end reduction

section kronecker

theorem digits_inj (D : ℕ) (hD : 0 < D) : ∀ (N : ℕ) (f g : Fin N → ℕ), (∀ h, f h < D) →
    (∀ h, g h < D) → ∑ h, f h * D ^ h.val = ∑ h, g h * D ^ h.val → f = g := by
  intro N
  induction N with
  | zero => intro f g _ _ _; funext h; exact h.elim0
  | succ N ih =>
    intro f g hf hg he
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at he
    have e1 : ∀ u : Fin (N + 1) → ℕ, ∑ h : Fin N, u h.succ * D ^ (h.succ).val =
        D * ∑ h : Fin N, u h.succ * D ^ h.val := by
      intro u
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [e1, e1] at he
    simp only [Fin.val_zero, pow_zero, mul_one] at he
    have h0 : f 0 = g 0 := by
      have := congrArg (· % D) he
      simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0), Nat.mod_eq_of_lt (hg 0)] at this
      exact this
    have ht : ∑ h : Fin N, f h.succ * D ^ h.val = ∑ h : Fin N, g h.succ * D ^ h.val := by
      rw [h0] at he
      exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel he)
    have := ih (fun h => f h.succ) (fun h => g h.succ) (fun h => hf _) (fun h => hg _) ht
    funext h
    exact Fin.cases h0 (fun i => congrFun this i) h

theorem kron {N : ℕ} (P : MvPolynomial (Fin N) ℂ) (hP : P ≠ 0) :
    ∃ (powers : Fin N → ℕ) (g : Polynomial ℂ), g ≠ 0 ∧
      ∀ z : ℂ, Polynomial.eval z g = MvPolynomial.eval (fun h => z ^ powers h) P := by
  classical
  set D := P.totalDegree + 1 with hD
  have hlt : ∀ α ∈ P.support, ∀ h, α h < D := by
    intro α hα h
    have h1 := MvPolynomial.monomial_le_degreeOf h hα
    have h2 := MvPolynomial.degreeOf_le_totalDegree P h
    omega
  let s : (Fin N →₀ ℕ) → ℕ := fun α => ∑ h, α h * D ^ h.val
  refine ⟨fun h => D ^ h.val,
    ∑ α ∈ P.support, Polynomial.C (P.coeff α) * Polynomial.X ^ (s α), ?_, ?_⟩
  · obtain ⟨α0, hα0⟩ := MvPolynomial.ne_zero_iff.mp hP
    have hα0s : α0 ∈ P.support := MvPolynomial.mem_support_iff.mpr hα0
    intro hg
    have := congrArg (fun r : Polynomial ℂ => r.coeff (s α0)) hg
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single α0] at this
    · simp only [↓reduceIte] at this
      exact hα0 this
    · intro β hβ hne
      have hs : s α0 ≠ s β := by
        intro heq
        apply hne
        have := digits_inj D (by omega) N (fun h => β h) (fun h => α0 h) (hlt β hβ) (hlt α0 hα0s)
          heq.symm
        ext h
        exact congrFun this h
      simp [hs]
    · intro h
      exact absurd hα0s h
  · intro z
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun α _ => ?_
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    rw [Finset.prod_congr rfl (fun h _ => (pow_mul z (D ^ h.val) (α h)).symm),
      Finset.prod_pow_eq_pow_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    ring

end kronecker

section matching

theorem modh (x c n : ℕ) (hc : c < n) : (x * n + c) % n = c := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

variable (n : ℕ) (H : Fin n → Fin n → Bool)

abbrev Sp : Type := {π : Equiv.Perm (Fin n) // ∀ j, H (π j) j = true}

noncomputable def perm (j : Fin (Fintype.card (Sp n H))) : Equiv.Perm (Fin n) :=
  ((Fintype.equivFin (Sp n H)).symm j).val

theorem perm_supp (j : Fin (Fintype.card (Sp n H))) (c : Fin n) : H (perm n H j c) c = true :=
  ((Fintype.equivFin (Sp n H)).symm j).property c

def ed : Fin (n * n) ≃ Fin n × Fin n := finProdFinEquiv.symm

noncomputable def aa (j : Fin (Fintype.card (Sp n H))) (i : Fin (n * n)) : ℕ :=
  if perm n H j (ed n i).2 = (ed n i).1 then 1 else 0

noncomputable def code (j : Fin (Fintype.card (Sp n H))) : ℕ :=
  ∑ c : Fin n, 2 ^ ((perm n H j c).val * n + c.val)

noncomputable def cc (j : Fin (Fintype.card (Sp n H))) : ℂ :=
  ((Equiv.Perm.sign (perm n H j) : ℤ) : ℂ)

def flat (A : Fin n → Fin n → ℂ) : Fin (n * n) → ℂ := fun i => A (ed n i).1 (ed n i).2

theorem wmon_flat (A : Fin n → Fin n → ℂ) (j : Fin (Fintype.card (Sp n H))) :
    wmon (aa n H) (flat n A) j = ∏ c, A (perm n H j c) c := by
  classical
  unfold wmon aa flat
  rw [Fintype.prod_equiv (ed n) _
    (fun e => A e.1 e.2 ^ (if perm n H j e.2 = e.1 then 1 else 0)) (fun i => rfl)]
  rw [Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun c _ => ?_
  simp only [pow_ite, pow_one, pow_zero]
  rw [Finset.prod_ite_eq]
  simp

theorem hdeg (j : Fin (Fintype.card (Sp n H))) : ∑ i, aa n H j i = n := by
  classical
  unfold aa
  rw [Fintype.sum_equiv (ed n) _ (fun e => if perm n H j e.2 = e.1 then 1 else 0) (fun i => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp

theorem hcode (hn : 0 < n) : Function.Injective (code n H) := by
  classical
  intro j j' hjj
  let f := fun (k : Fin (Fintype.card (Sp n H))) (c : Fin n) => (perm n H k c).val * n + c.val
  have finj : ∀ k, Function.Injective (f k) := by
    intro k c c' h
    have hm := congrArg (· % n) h
    simp only [f, modh _ _ _ c.isLt, modh _ _ _ c'.isLt] at hm
    exact Fin.ext hm
  have img : ∀ k, code n H k = ∑ x ∈ Finset.univ.image (f k), 2 ^ x := by
    intro k
    rw [Finset.sum_image (fun a _ b _ h => finj k h)]
    rfl
  have hs : Finset.univ.image (f j) = Finset.univ.image (f j') := by
    rw [img, img] at hjj
    have := congrArg (fun t : ℕ => t.bitIndices.toFinset) hjj
    simp only [Finset.toFinset_bitIndices_sum_two_pow] at this
    exact this
  have hp : perm n H j = perm n H j' := by
    ext c
    have hmem : f j c ∈ Finset.univ.image (f j') := by
      rw [← hs]; exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    obtain ⟨c', _, hc'⟩ := Finset.mem_image.mp hmem
    have hcc : c' = c := by
      have hm := congrArg (· % n) hc'
      simp only [f, modh _ _ _ c.isLt, modh _ _ _ c'.isLt] at hm
      exact Fin.ext hm
    subst hcc
    simp only [f, Nat.add_right_cancel_iff] at hc'
    exact (Nat.eq_of_mul_eq_mul_right hn hc').symm
  have : (Fintype.equivFin (Sp n H)).symm j = (Fintype.equivFin (Sp n H)).symm j' :=
    Subtype.ext hp
  exact (Fintype.equivFin (Sp n H)).symm.injective this

theorem hcc (j : Fin (Fintype.card (Sp n H))) : cc n H j ≠ 0 := by
  unfold cc
  rcases Int.units_eq_one_or (Equiv.Perm.sign (perm n H j)) with h | h <;> simp [h]

theorem det_expand (A : Fin n → Fin n → ℂ) (hA : ∀ i j, H i j = false → A i j = 0)
    (z : ℂ) (P : ℕ) :
    Matrix.det (fun i j => A i j * z ^ (P * 2 ^ (i.val * n + j.val)) : Matrix (Fin n) (Fin n) ℂ) =
      ∑ j, cc n H j * wmon (aa n H) (flat n A) j * (z ^ P) ^ code n H j := by
  classical
  refine (Matrix.det_apply' _).trans ?_
  have term : ∀ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, (A (σ i) i * z ^ (P * 2 ^ ((σ i).val * n + i.val))) =
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, A (σ i) i) *
        (z ^ P) ^ (∑ i, 2 ^ ((σ i).val * n + i.val)) := by
    intro σ
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finset.mul_sum, pow_mul]
    ring
  simp only [term]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun σ : Equiv.Perm (Fin n) => ∀ j, H (σ j) j = true)]
  have zero : ∑ σ : {σ : Equiv.Perm (Fin n) // ¬ ∀ j, H (σ j) j = true},
      ((Equiv.Perm.sign σ.val : ℤ) : ℂ) * (∏ i, A (σ.val i) i) *
        (z ^ P) ^ (∑ i, 2 ^ ((σ.val i).val * n + i.val)) = 0 := by
    refine Finset.sum_eq_zero fun σ _ => ?_
    obtain ⟨c, hc⟩ := not_forall.mp σ.property
    have : A (σ.val c) c = 0 := hA _ _ (by simpa using hc)
    rw [Finset.prod_eq_zero (f := fun i => A (σ.val i) i) (Finset.mem_univ c) this]
    ring
  rw [zero, add_zero]
  rw [← Equiv.sum_comp (Fintype.equivFin (Sp n H)).symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wmon_flat]
  rfl

end matching

theorem main : ∀ (n : ℕ) (H : Fin n → Fin n → Bool),
  let I := Fin n
  let E := I × I
  let V := Submodule.span ℚ {v : E → ℚ | ∃ π : Equiv.Perm I, (∀ j, H (π j) j = true) ∧
    v = fun e => if π e.2 = e.1 then (1 : ℚ) else 0}
  let d := Module.finrank ℚ V
  let edge := fun (i j : I) => 2^(i.val*n+j.val)
  ∃ (powers : Fin (2*d) → ℕ) (bad : Finset ℂ),
    (∀ z : ℂ, z ∉ bad → ∃ read : (Fin (2*d) → ℂ) → Equiv.Perm I → ℂ,
      ∀ A : Matrix I I ℂ, (∀ i j, H i j = false → A i j = 0) →
        ∀ π : Equiv.Perm I,
        read (fun h => Matrix.det (fun i j => A i j * z^(powers h * edge i j) : Matrix I I ℂ)) π =
          ∏ j : I, A (π j) j) ∧
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ ζ : ℂ, IsPrimitiveRoot ζ q → ζ ∉ bad := by
  intro n H I E V d edge
  classical
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun _ => 0, ∅, fun z _ => ⟨fun _ _ => 1, fun A _ π => by simp⟩, 0,
      fun q _ ζ _ => by simp⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hd : Module.finrank ℚ (Submodule.span ℚ (Set.range
      (fun j : Fin (Fintype.card (Sp n H)) => fun i : Fin (n * n) => (aa n H j i : ℚ)))) = d := by
    let Lq : (Fin n × Fin n → ℚ) ≃ₗ[ℚ] (Fin (n * n) → ℚ) := LinearEquiv.funCongrLeft ℚ ℚ (ed n)
    have hmap : Submodule.span ℚ (Set.range
        (fun j : Fin (Fintype.card (Sp n H)) => fun i : Fin (n * n) => (aa n H j i : ℚ))) =
        V.map (Lq : (Fin n × Fin n → ℚ) →ₗ[ℚ] (Fin (n * n) → ℚ)) := by
      rw [Submodule.map_span]
      congr 1
      ext w
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨fun e => if perm n H j e.2 = e.1 then (1 : ℚ) else 0,
          ⟨perm n H j, perm_supp n H j, rfl⟩, ?_⟩
        funext i
        simp [Lq, LinearEquiv.funCongrLeft, aa]
      · rintro ⟨v, ⟨π, hπ, rfl⟩, rfl⟩
        refine ⟨(Fintype.equivFin (Sp n H)) ⟨π, hπ⟩, ?_⟩
        have hp : perm n H ((Fintype.equivFin (Sp n H)) ⟨π, hπ⟩) = π := by
          show ((Fintype.equivFin (Sp n H)).symm ((Fintype.equivFin (Sp n H)) ⟨π, hπ⟩)).val = π
          rw [Equiv.symm_apply_apply]
        funext i
        simp [Lq, LinearEquiv.funCongrLeft, aa, hp]
    rw [hmap, LinearEquiv.finrank_map_eq]
  obtain ⟨cert, hcert0, hcertI⟩ := exists_cert (N := 2 * d) (k := n) (aa n H) (code n H) (cc n H)
    hn0 (hdeg n H) (hcode n H hn0) (hcc n H) (by rw [hd])
  obtain ⟨powers, g, hg0, hgev⟩ := kron cert hcert0
  refine ⟨powers, g.roots.toFinset, ?_, ?_⟩
  · intro z hz
    have hev : MvPolynomial.eval (fun h => z ^ powers h) cert ≠ 0 := by
      rw [← hgev]
      intro h0
      apply hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      exact h0
    let fitsP := fun (A : Matrix I I ℂ) => ∀ i j, H i j = false → A i j = 0
    let Q := fun (A : Matrix I I ℂ) (h : Fin (2 * d)) =>
      Matrix.det (fun i j => A i j * z ^ (powers h * edge i j) : Matrix I I ℂ)
    refine ⟨fun y π => if hA : ∃ A', fitsP A' ∧ Q A' = y then
      ∏ j : I, (Classical.choose hA) (π j) j else 0, ?_⟩
    intro A hA π
    have hex : ∃ A', fitsP A' ∧ Q A' = Q A := ⟨A, hA, rfl⟩
    show (if hA : ∃ A', fitsP A' ∧ Q A' = Q A then
      ∏ j : I, (Classical.choose hA) (π j) j else 0) = _
    rw [dite_cond_eq_true (eq_true hex)]
    obtain ⟨hfit', hQ'⟩ := Classical.choose_spec hex
    set A' := Classical.choose hex
    have hw : ∀ j, wmon (aa n H) (flat n A') j = wmon (aa n H) (flat n A) j := by
      intro j
      refine final_step (aa n H) (code n H) (cc n H) cert hcertI (fun h => z ^ powers h) hev
        (flat n A') (flat n A) ?_ j
      intro h
      have e := congrFun hQ' h
      simp only [Q, edge] at e
      rw [det_expand n H A' hfit', det_expand n H A hA] at e
      exact e
    by_cases hπ : ∀ j, H (π j) j = true
    · have hp : perm n H ((Fintype.equivFin (Sp n H)) ⟨π, hπ⟩) = π := by
        show ((Fintype.equivFin (Sp n H)).symm ((Fintype.equivFin (Sp n H)) ⟨π, hπ⟩)).val = π
        rw [Equiv.symm_apply_apply]
      have e1 := wmon_flat n H A' ((Fintype.equivFin (Sp n H)) ⟨π, hπ⟩)
      have e2 := wmon_flat n H A ((Fintype.equivFin (Sp n H)) ⟨π, hπ⟩)
      rw [hp] at e1 e2
      exact e1.symm.trans ((hw _).trans e2)
    · obtain ⟨c, hc⟩ := not_forall.mp hπ
      have hf : H (π c) c = false := by simpa using hc
      rw [Finset.prod_eq_zero (f := fun j => A' (π j) j) (Finset.mem_univ c) (hfit' _ _ hf),
        Finset.prod_eq_zero (f := fun j => A (π j) j) (Finset.mem_univ c) (hA _ _ hf)]
  · refine ⟨g.roots.toFinset.sup orderOf + 1, fun q hq ζ hζ hmem => ?_⟩
    have h1 := hζ.eq_orderOf
    have h2 := Finset.le_sup (f := orderOf) hmem
    omega

end PEqualNP.Outside.L_lib_1078_aux

theorem PEqualNP.Outside.L_lib_1078 : ∀ (n : ℕ) (H : Fin n → Fin n → Bool),
  let I := Fin n
  let E := I × I
  let V := Submodule.span ℚ {v : E → ℚ | ∃ π : Equiv.Perm I, (∀ j, H (π j) j = true) ∧
    v = fun e => if π e.2 = e.1 then (1 : ℚ) else 0}
  let d := Module.finrank ℚ V
  let edge := fun (i j : I) => 2^(i.val*n+j.val)
  ∃ (powers : Fin (2*d) → ℕ) (bad : Finset ℂ),
    (∀ z : ℂ, z ∉ bad → ∃ read : (Fin (2*d) → ℂ) → Equiv.Perm I → ℂ,
      ∀ A : Matrix I I ℂ, (∀ i j, H i j = false → A i j = 0) →
        ∀ π : Equiv.Perm I,
        read (fun h => Matrix.det (fun i j => A i j * z^(powers h * edge i j) : Matrix I I ℂ)) π =
          ∏ j : I, A (π j) j) ∧
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ ζ : ℂ, IsPrimitiveRoot ζ q → ζ ∉ bad := by
  exact PEqualNP.Outside.L_lib_1078_aux.main
