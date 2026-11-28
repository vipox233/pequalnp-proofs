import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1077_aux

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

end PEqualNP.Outside.L_lib_1077_aux

theorem PEqualNP.Outside.L_lib_1077 : (∀ (p m k : ℕ) (a : Fin m → Fin p → ℕ) (code : Fin m → ℕ) (c : Fin m → ℂ),
  0 < k → (∀ j, (∑ i : Fin p, a j i) = k) → Function.Injective code → (∀ j, c j ≠ 0) →
  let V := Submodule.span ℚ (Set.range (fun j : Fin m => fun i : Fin p => (a j i : ℚ)))
  let d := Module.finrank ℚ V
  let w := fun (x : Fin p → ℂ) (j : Fin m) => ∏ i : Fin p, (x i)^(a j i)
  let evalAt := fun (x : Fin p → ℂ) (z : ℂ) => ∑ j : Fin m, c j * w x j * z^(code j)
  ∃ cert : MvPolynomial (Fin (2*d)) ℂ, cert ≠ 0 ∧
    ∀ t : Fin (2*d) → ℂ, MvPolynomial.eval t cert ≠ 0 →
      ∀ x y : Fin p → ℂ,
        (∀ h : Fin (2*d), evalAt x (t h) = evalAt y (t h)) → ∀ j : Fin m, w x j = w y j) := by
  intro p m k a code c hk hdeg hcode hc V d w evalAt
  obtain ⟨q, hq0, hqI⟩ := PEqualNP.Outside.L_lib_1077_aux.exists_cert (N := 2 * d) a code c hk
    hdeg hcode hc le_rfl
  exact ⟨q, hq0, fun t ht x y hcol j =>
    PEqualNP.Outside.L_lib_1077_aux.final_step a code c q hqI t ht x y hcol j⟩
