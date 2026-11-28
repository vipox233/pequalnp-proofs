import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.SpecificLimits.Basic

namespace PEqualNP.Outside.L_lib_1091_aux

open MvPolynomial

noncomputable section

private lemma exists_separating_fin_rat {ι : Type*} [Nonempty ι] {W : Type*}
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]
    (φ : ι → (W →ₗ[ℚ] ℚ))
    (hsep : ∀ w : W, (∀ i : ι, φ i w = 0) → w = 0) :
    ∀ (k : ℕ) (S : Submodule ℚ W), Module.finrank ℚ S ≤ k →
      ∃ idx : Fin k → ι, ∀ w ∈ S, (∀ h : Fin k, φ (idx h) w = 0) → w = 0 := by
  intro k
  induction k with
  | zero =>
    intro S hS
    refine ⟨Fin.elim0, fun w hw _ => ?_⟩
    have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero hS)
    rw [hbot, Submodule.mem_bot] at hw
    exact hw
  | succ k ih =>
    intro S hS
    by_cases hbot : S = ⊥
    · refine ⟨fun _ => Classical.arbitrary ι, fun w hw _ => ?_⟩
      rw [hbot, Submodule.mem_bot] at hw
      exact hw
    · rcases Submodule.exists_mem_ne_zero_of_ne_bot hbot with ⟨w0, hw0S, hw0_ne⟩
      have hex_i : ∃ i0 : ι, φ i0 w0 ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hw0_ne (hsep w0 hall)
      rcases hex_i with ⟨i0, hi0⟩
      let f0 : S →ₗ[ℚ] ℚ := (φ i0).domRestrict S
      have hker_le : Module.finrank ℚ (LinearMap.ker f0) ≤ k := by
        have hkn := LinearMap.finrank_range_add_finrank_ker f0
        have hrg_pos : 0 < Module.finrank ℚ (LinearMap.range f0) := by
          have hne : LinearMap.range f0 ≠ ⊥ := by
            intro hb
            have hm : f0 ⟨w0, hw0S⟩ ∈ (⊥ : Submodule ℚ ℚ) := hb ▸ ⟨⟨w0, hw0S⟩, rfl⟩
            rw [Submodule.mem_bot] at hm
            exact hi0 hm
          by_contra h0
          exact hne (Submodule.finrank_eq_zero.mp (by omega))
        omega
      let S' : Submodule ℚ W := (LinearMap.ker f0).map S.subtype
      have hS'_rk : Module.finrank ℚ S' ≤ k :=
        (Submodule.finrank_map_le S.subtype (LinearMap.ker f0)).trans hker_le
      rcases ih S' hS'_rk with ⟨idx', hidx'⟩
      refine ⟨Fin.cons i0 idx', fun w hwS hvan => ?_⟩
      have hw0 : φ i0 w = 0 := by
        have h := hvan 0
        simpa using h
      have hwS' : w ∈ S' := ⟨⟨w, hwS⟩, hw0, rfl⟩
      exact hidx' w hwS' fun h => by
        have hv := hvan h.succ
        simpa using hv

private lemma exists_clear_denom_rat {κ : Type*} [Fintype κ] (q : κ → ℚ) :
    ∃ M : ℕ, 0 < M ∧ ∃ c : κ → ℤ, ∀ l, (c l : ℚ) = q l * M := by
  refine ⟨∏ l, (q l).den, Finset.prod_pos fun l _ => (q l).den_pos, fun l =>
    (q l).num * (((∏ l, (q l).den) / (q l).den : ℕ) : ℤ), fun l => ?_⟩
  have hd : (q l).den ∣ ∏ l, (q l).den := Finset.dvd_prod_of_mem _ (Finset.mem_univ l)
  have hd0 : ((q l).den : ℚ) ≠ 0 := by exact_mod_cast (q l).den_nz
  have hq : q l = (q l).num / (q l).den := (Rat.num_div_den _).symm
  rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div hd hd0]
  calc ((q l).num : ℚ) * (((∏ l, (q l).den : ℕ) : ℚ) / ((q l).den : ℚ))
      = ((q l).num / (q l).den) * ((∏ l, (q l).den : ℕ) : ℚ) := by ring
    _ = q l * ((∏ l, (q l).den : ℕ) : ℚ) := by rw [← hq]

private lemma totalDegree_sub_homogeneousComponent_lt {σ : Type*} (φ : MvPolynomial σ ℂ)
    {m : ℕ} (hm : φ.totalDegree ≤ m) (hm0 : 0 < m) :
    (φ - homogeneousComponent m φ).totalDegree < m := by
  rw [totalDegree, Finset.sup_lt_iff (by simpa using hm0)]
  intro s hs
  rw [mem_support_iff, coeff_sub, coeff_homogeneousComponent] at hs
  have hdeg : (s.sum fun _ e => e) = s.degree := rfl
  rw [hdeg]
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with hlt | heq
  · apply hs
    have : φ.coeff s = 0 := coeff_eq_zero_of_totalDegree_lt (by
      have : s.degree = ∑ i ∈ s.support, s i := rfl
      omega)
    simp [this]
  · apply hs
    simp [heq.symm]

private lemma exists_sep_fin {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : Finset (σ → ℂ)) (y : σ → ℂ) :
    ∃ p : MvPolynomial σ ℂ, eval y p = 1 ∧ ∀ x ∈ T, x ≠ y → eval x p = 0 := by
  classical
  have h : ∀ z : σ → ℂ, ∃ q : MvPolynomial σ ℂ,
      z ≠ y → eval y q = 1 ∧ eval z q = 0 := by
    intro z
    by_cases hz : z = y
    · exact ⟨0, fun h => absurd hz h⟩
    · obtain ⟨j, hj⟩ := Function.ne_iff.1 hz
      refine ⟨C ((y j - z j)⁻¹) * (X j - C (z j)), fun _ => ⟨?_, ?_⟩⟩
      · simp only [map_mul, map_sub, eval_C, eval_X]
        exact inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hj))
      · simp
  choose q hq using h
  refine ⟨∏ z ∈ T.erase y, q z, ?_, fun x hx hxy => ?_⟩
  · rw [map_prod]
    exact Finset.prod_eq_one fun z hz => (hq z (Finset.ne_of_mem_erase hz)).1
  · rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hxy, hx⟩) (hq x hxy).2

private def simplexFinset (d T : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range (T + 1)).filter fun a => ∑ i, a i ≤ T

private lemma mem_simplexFinset {d T : ℕ} {a : Fin d → ℕ} :
    a ∈ simplexFinset d T ↔ ∑ i, a i ≤ T := by
  unfold simplexFinset
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [Finset.mem_range]
  have h1 : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (f := fun j => a j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

private lemma simplexFinset_card_mul_factorial (d : ℕ) :
    ∀ T : ℕ, (simplexFinset d T).card * d.factorial = ∏ j : Fin d, (T + j.val + 1) := by
  induction d with
  | zero =>
    intro T
    have h1 : simplexFinset 0 T = {Fin.elim0} := by
      ext a
      simp only [mem_simplexFinset, Fin.sum_univ_zero, Nat.zero_le, Finset.mem_singleton, true_iff]
      funext i
      exact Fin.elim0 i
    rw [h1]
    simp
  | succ d ih =>
    intro T
    have hbij : (simplexFinset (d + 1) T).card =
        ∑ t ∈ Finset.range (T + 1), (simplexFinset d t).card := by
      have hbi : simplexFinset (d + 1) T =
          (Finset.range (T + 1)).biUnion fun t =>
            (simplexFinset d t).image fun b => Fin.cons (T - t) b := by
        ext a
        simp only [mem_simplexFinset, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
        constructor
        · intro ha
          rw [Fin.sum_univ_succ] at ha
          refine ⟨T - a 0, by omega, Fin.tail a, ?_, ?_⟩
          · have : ∑ i : Fin d, Fin.tail a i = ∑ i : Fin d, a i.succ := rfl
            omega
          · funext i
            refine Fin.cases ?_ (fun j => rfl) i
            simp only [Fin.cons_zero]
            omega
        · rintro ⟨t, ht, b, hb, rfl⟩
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          omega
      rw [hbi, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun t _ => Finset.card_image_of_injective _ ?_
        intro b1 b2 h
        funext i
        have := congrFun h i.succ
        simpa using this
      · intro t1 ht1 t2 ht2 hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        rcases Finset.mem_image.mp ha1 with ⟨b1, _, rfl⟩
        rcases Finset.mem_image.mp ha2 with ⟨b2, _, h2⟩
        have h0 := congrFun h2 0
        simp only [Fin.cons_zero] at h0
        have ht1' := Finset.mem_range.mp ht1
        have ht2' := Finset.mem_range.mp ht2
        omega
    rw [hbij, Nat.factorial_succ, Finset.sum_mul]
    have hstep : ∀ t : ℕ,
        (simplexFinset d t).card * ((d + 1) * d.factorial) =
          (∏ j : Fin (d + 1), (t + 1 + j.val)) - (∏ j : Fin (d + 1), (t + j.val)) := by
      intro t
      have h1 : (simplexFinset d t).card * ((d + 1) * d.factorial) =
          (d + 1) * ((simplexFinset d t).card * d.factorial) := by ring
      rw [h1, ih t]
      have hA : ∏ j : Fin (d + 1), (t + 1 + j.val) =
          (∏ j : Fin d, (t + j.val + 1)) * (t + 1 + d) := by
        rw [Fin.prod_univ_castSucc]
        congr 1
        refine Finset.prod_congr rfl fun j _ => by simp only [Fin.val_castSucc]; omega
      have hB : ∏ j : Fin (d + 1), (t + j.val) =
          t * (∏ j : Fin d, (t + j.val + 1)) := by
        rw [Fin.prod_univ_succ]
        simp [Fin.val_succ, add_assoc]
      rw [hA, hB]
      have : (∏ j : Fin d, (t + j.val + 1)) * (t + 1 + d) =
          t * (∏ j : Fin d, (t + j.val + 1)) + (d + 1) * (∏ j : Fin d, (t + j.val + 1)) := by
        ring
      omega
    have htele : ∀ N : ℕ,
        ∑ t ∈ Finset.range N,
          ((∏ j : Fin (d + 1), (t + 1 + j.val)) - (∏ j : Fin (d + 1), (t + j.val))) =
        ∏ j : Fin (d + 1), (N + j.val) := by
      intro N
      induction N with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, zero_add]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (d + 1))) rfl
      | succ N ihN =>
        rw [Finset.sum_range_succ, ihN]
        have hle : ∏ j : Fin (d + 1), (N + j.val) ≤ ∏ j : Fin (d + 1), (N + 1 + j.val) :=
          Finset.prod_le_prod fun j _ => by omega
        omega
    calc ∑ t ∈ Finset.range (T + 1), (simplexFinset d t).card * ((d + 1) * d.factorial)
        = ∑ t ∈ Finset.range (T + 1),
            ((∏ j : Fin (d + 1), (t + 1 + j.val)) - (∏ j : Fin (d + 1), (t + j.val))) :=
          Finset.sum_congr rfl fun t _ => hstep t
      _ = ∏ j : Fin (d + 1), (T + 1 + j.val) := htele (T + 1)
      _ = ∏ j : Fin (d + 1), (T + j.val + 1) :=
          Finset.prod_congr rfl fun j _ => by omega

private lemma finrank_restrictTotalDegree_le_simplex (d T : ℕ) :
    Module.finrank ℂ (restrictTotalDegree (Fin d) ℂ T) ≤ (simplexFinset d T).card := by
  classical
  let gens : Finset (MvPolynomial (Fin d) ℂ) :=
    (simplexFinset d T).image fun a => monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℂ)
  have hle : restrictTotalDegree (Fin d) ℂ T ≤ Submodule.span ℂ (gens : Set (MvPolynomial (Fin d) ℂ)) := by
    intro p hp
    rw [mem_restrictTotalDegree] at hp
    rw [p.as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsd : s.degree ≤ T := (le_totalDegree hs).trans hp
    have hsm : monomial s (p.coeff s) = p.coeff s • monomial s (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hsm]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp only [gens, Finset.coe_image, Set.mem_image, Finset.mem_coe]
    refine ⟨⇑s, mem_simplexFinset.mpr ?_, by simp⟩
    rw [← Finsupp.degree_eq_sum]
    exact hsd
  have h1 : Module.finrank ℂ (restrictTotalDegree (Fin d) ℂ T) ≤
      Module.finrank ℂ (Submodule.span ℂ (gens : Set (MvPolynomial (Fin d) ℂ))) :=
    Submodule.finrank_mono hle
  have h2 : Module.finrank ℂ (Submodule.span ℂ (gens : Set (MvPolynomial (Fin d) ℂ))) ≤ gens.card :=
    finrank_span_finset_le_card gens
  exact h1.trans (h2.trans Finset.card_image_le)

private lemma nat_le_pow_of_asymptotic (m n d C : ℕ)
    (h : ∀ K : ℕ, m * (K + 1) ^ d ≤ (n * K + C + d) ^ d) : m ≤ n ^ d := by
  have hR : (m : ℝ) ≤ (n : ℝ) ^ d := by
    have hbound : ∀ K : ℕ, (m : ℝ) ≤ ((n : ℝ) + ((C + d : ℝ) - n) / ((K : ℝ) + 1)) ^ d := by
      intro K
      have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hKpow : (0 : ℝ) < ((K : ℝ) + 1) ^ d := pow_pos hKpos d
      have h1 : (m : ℝ) * ((K : ℝ) + 1) ^ d ≤ ((n : ℝ) * K + C + d) ^ d := by
        exact_mod_cast h K
      have h2 : (m : ℝ) ≤ ((n : ℝ) * K + C + d) ^ d / ((K : ℝ) + 1) ^ d :=
        (le_div_iff₀ hKpow).mpr h1
      rw [← div_pow] at h2
      have h3 : ((n : ℝ) * K + C + d) / ((K : ℝ) + 1) =
          (n : ℝ) + ((C + d : ℝ) - n) / ((K : ℝ) + 1) := by
        field_simp
        ring
      rwa [h3] at h2
    have ht0 : Filter.Tendsto (fun K : ℕ => (1 : ℝ) / ((K : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht1 : Filter.Tendsto (fun K : ℕ => ((C + d : ℝ) - n) / ((K : ℝ) + 1))
        Filter.atTop (nhds 0) := by
      have := (tendsto_const_nhds (x := (C + d : ℝ) - n)).mul ht0
      simp only [mul_zero] at this
      exact this.congr fun K => by ring
    have ht2 : Filter.Tendsto (fun K : ℕ => ((n : ℝ) + ((C + d : ℝ) - n) / ((K : ℝ) + 1)) ^ d)
        Filter.atTop (nhds ((n : ℝ) ^ d)) := by
      have := ((tendsto_const_nhds (x := (n : ℝ))).add ht1).pow d
      simpa using this
    exact ge_of_tendsto ht2 (Filter.Eventually.of_forall hbound)
  exact_mod_cast hR

private def chainIdeal (d i : ℕ) : Ideal (MvPolynomial (Fin d) ℂ) :=
  Ideal.span (MvPolynomial.X '' {j : Fin d | j.val < i})

private lemma chainIdeal_isPrime (d i : ℕ) : (chainIdeal d i).IsPrime :=
  span_X_image_isPrime _

private lemma chainIdeal_lt (d i : ℕ) (hi : i < d) :
    chainIdeal d i < chainIdeal d (i + 1) := by
  refine lt_of_le_of_ne ?_ ?_
  · refine Ideal.span_mono (Set.image_mono ?_)
    intro j hj
    simp only [Set.mem_ofPred_eq] at hj ⊢
    omega
  · intro h
    have hmem : (X ⟨i, hi⟩ : MvPolynomial (Fin d) ℂ) ∈ chainIdeal d (i + 1) :=
      Ideal.subset_span ⟨⟨i, hi⟩, by simp, rfl⟩
    rw [← h, chainIdeal, mem_ideal_span_X_image] at hmem
    obtain ⟨j, hj, hne⟩ := hmem (Finsupp.single ⟨i, hi⟩ 1) (by simp [support_X])
    simp only [Set.mem_ofPred_eq] at hj
    rw [Finsupp.single_apply] at hne
    split_ifs at hne with hij
    · subst hij; simp at hj
    · exact hne rfl

private lemma le_height_chainIdeal (d i : ℕ) (hi : i ≤ d) :
    (i : ℕ∞) ≤ (chainIdeal d i).height := by
  induction i with
  | zero => simp
  | succ k ih =>
    haveI := chainIdeal_isPrime d k
    haveI := chainIdeal_isPrime d (k + 1)
    calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (chainIdeal d k).height + 1 := by gcongr; exact ih (by omega)
      _ ≤ (chainIdeal d (k + 1)).height :=
        Ideal.height_add_one_le_of_lt_of_isPrime (chainIdeal_lt d k (by omega))

private lemma le_height_m0_complex (d : ℕ) :
    (d : ℕ∞) ≤ (Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ))).height := by
  have heq : chainIdeal d d = Ideal.span (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) := by
    rw [chainIdeal, ← Set.image_univ]
    congr 2
    ext j
    simp
  rw [← heq]
  exact le_height_chainIdeal d d le_rfl

private lemma prime_homogeneous_of_minimalPrime_of_homogeneous {σ : Type*} [Fintype σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (hI : ∀ f ∈ I, ∀ m, homogeneousComponent m f ∈ I)
    (P : Ideal (MvPolynomial σ ℂ)) (hP : P ∈ I.minimalPrimes) :
    ∀ f ∈ P, ∀ m, homogeneousComponent m f ∈ P := by
  haveI : P.IsPrime := hP.isPrime
  let θ : MvPolynomial σ ℂ →ₐ[ℂ] Polynomial (MvPolynomial σ ℂ ⧸ P) :=
    MvPolynomial.aeval fun s =>
      Polynomial.C (Ideal.Quotient.mk P (X s)) * Polynomial.X
  have hθ_mon : ∀ (e : σ →₀ ℕ) (c : ℂ),
      θ (monomial e c) =
        Polynomial.C (Ideal.Quotient.mk P (monomial e c)) * Polynomial.X ^ e.degree := by
    intro e c
    rw [monomial_eq, map_mul, map_mul, map_mul]
    have hθC : θ (C c) = Polynomial.C (Ideal.Quotient.mk P (C c)) := by
      simp only [θ, aeval_C]
      rfl
    have hprod : θ (e.prod fun s k => X s ^ k) =
        Polynomial.C (Ideal.Quotient.mk P (e.prod fun s k => X s ^ k)) * Polynomial.X ^ e.degree := by
      rw [Finsupp.prod, map_prod, map_prod, map_prod]
      have hterm : ∀ x ∈ e.support,
          θ (X x ^ e x) = Polynomial.C (Ideal.Quotient.mk P (X x ^ e x)) * Polynomial.X ^ e x := by
        intro x _
        dsimp only [θ]
        rw [map_pow, aeval_X, map_pow, map_pow]
        ring
      rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rfl
    rw [hθC, hprod]
    ring
  have hθ_hom : ∀ (m : ℕ) (g : MvPolynomial σ ℂ), g.IsHomogeneous m →
      θ g = Polynomial.C (Ideal.Quotient.mk P g) * Polynomial.X ^ m := by
    intro m g hg
    rw [g.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hθ_mon]
    have hm : e.degree = m := by
      have := hg (mem_support_iff.mp he)
      rwa [Finsupp.degree_eq_weight_one]
    rw [hm]
  have hθ_coeff : ∀ (f : MvPolynomial σ ℂ) (m : ℕ),
      (θ f).coeff m = Ideal.Quotient.mk P (homogeneousComponent m f) := by
    intro f m
    have hf : f = ∑ k ∈ Finset.range (max (f.totalDegree + 1) (m + 1)),
        homogeneousComponent k f := by
      calc f = ∑ k ∈ Finset.range (f.totalDegree + 1), homogeneousComponent k f :=
            (sum_homogeneousComponent f).symm
        _ = ∑ k ∈ Finset.range (max (f.totalDegree + 1) (m + 1)), homogeneousComponent k f :=
            Finset.sum_subset (Finset.range_mono (le_max_left _ _)) fun k hk hkn => by
              rw [Finset.mem_range] at hk hkn
              exact homogeneousComponent_eq_zero k f (by omega)
    conv_lhs => rw [hf]
    rw [map_sum, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single m]
    · rw [hθ_hom m _ (homogeneousComponent_isHomogeneous m f), Polynomial.coeff_C_mul_X_pow]
      simp
    · intro k _ hkm
      rw [hθ_hom k _ (homogeneousComponent_isHomogeneous k f), Polynomial.coeff_C_mul_X_pow]
      simp [hkm.symm]
    · intro hm'
      exact absurd (Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self m) (le_max_right _ _))) hm'
  let Pstar : Ideal (MvPolynomial σ ℂ) := RingHom.ker θ.toRingHom
  have hPstar_mem : ∀ f, f ∈ Pstar ↔ ∀ m, homogeneousComponent m f ∈ P := by
    intro f
    simp only [Pstar, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [Polynomial.ext_iff]
    simp only [hθ_coeff, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
  haveI : Pstar.IsPrime := RingHom.ker_isPrime θ.toRingHom
  have hIPstar : I ≤ Pstar := fun f hf => (hPstar_mem f).mpr fun m => hP.le (hI f hf m)
  have hPstarP : Pstar ≤ P := by
    intro f hf
    rw [← sum_homogeneousComponent f]
    exact Ideal.sum_mem P fun m _ => (hPstar_mem f).mp hf m
  have heq : Pstar = P := le_antisymm hPstarP (hP.2 ⟨inferInstance, hIPstar⟩ hPstarP)
  intro f hf m
  rw [← heq] at hf
  exact (hPstar_mem f).mp hf m

private lemma homogeneous_prime_le_m0 {σ : Type*} [Fintype σ]
    (P : Ideal (MvPolynomial σ ℂ)) [P.IsPrime]
    (hPhom : ∀ f ∈ P, ∀ m, homogeneousComponent m f ∈ P) :
    P ≤ Ideal.span (Set.range (X : σ → MvPolynomial σ ℂ)) := by
  intro f hf
  have h0 : homogeneousComponent 0 f ∈ P := hPhom f hf 0
  rw [homogeneousComponent_zero] at h0
  have hc0 : constantCoeff f = 0 := by
    by_contra hne
    have hu : IsUnit (C (constantCoeff f) : MvPolynomial σ ℂ) := (IsUnit.mk0 _ hne).map C
    exact Ideal.IsPrime.ne_top' (Ideal.eq_top_of_isUnit_mem P h0 hu)
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro m hm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mem_support_iff, ← constantCoeff_eq] at hm
    exact hm hc0
  obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hm0
  exact ⟨s, Set.mem_univ _, hs⟩

private lemma height_le_height_under_of_isIntegral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (P : Ideal B) [P.IsPrime] :
    P.height ≤ (P.under A).height := by
  rw [show P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum B) from
        PrimeSpectrum.height_eq_orderHeight ⟨P, inferInstance⟩,
      show (P.under A).height = Order.height (⟨P.under A, inferInstance⟩ : PrimeSpectrum A) from
        PrimeSpectrum.height_eq_orderHeight ⟨P.under A, inferInstance⟩]
  rw [Order.height, Order.height]
  refine iSup_le fun l => iSup_le fun hl => ?_
  let f : PrimeSpectrum B → PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B)
  have hstrict : StrictMono f := fun Q1 Q2 hlt => by
    change Q1.asIdeal.under A < Q2.asIdeal.under A
    exact Ideal.IsIntegral.under_lt_under hlt
  let l' : LTSeries (PrimeSpectrum A) := l.map f hstrict
  have hlast : l'.last ≤ ⟨P.under A, inferInstance⟩ := by
    change l.last.asIdeal.under A ≤ P.under A
    exact Ideal.comap_mono hl
  have hlen : (l.length : ℕ∞) = (l'.length : ℕ∞) := by simp [l']
  rw [hlen]
  exact le_iSup₂_of_le l' hlast le_rfl

private lemma height_comap_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (P : Ideal B) [P.IsPrime] :
    P.height ≤ (P.comap e.toRingHom).height := by
  haveI : (P.comap e.toRingHom).IsPrime := Ideal.comap_isPrime e.toRingHom P
  rw [show P.height = Order.height (⟨P, inferInstance⟩ : PrimeSpectrum B) from
        PrimeSpectrum.height_eq_orderHeight ⟨P, inferInstance⟩,
      show (P.comap e.toRingHom).height =
          Order.height (⟨P.comap e.toRingHom, inferInstance⟩ : PrimeSpectrum A) from
        PrimeSpectrum.height_eq_orderHeight ⟨P.comap e.toRingHom, inferInstance⟩]
  rw [Order.height, Order.height]
  refine iSup_le fun l => iSup_le fun hl => ?_
  let f : PrimeSpectrum B → PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom
  have hstrict : StrictMono f := fun Q1 Q2 hlt => by
    change Q1.asIdeal.comap e.toRingHom < Q2.asIdeal.comap e.toRingHom
    refine lt_of_le_of_ne (Ideal.comap_mono hlt.le) fun heq => hlt.ne ?_
    ext x
    have hx := Ideal.ext_iff.mp heq (e.symm x)
    simp only [Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply] at hx
    exact hx
  let l' : LTSeries (PrimeSpectrum A) := l.map f hstrict
  have hlast : l'.last ≤ ⟨P.comap e.toRingHom, inferInstance⟩ := by
    change l.last.asIdeal.comap e.toRingHom ≤ P.comap e.toRingHom
    exact Ideal.comap_mono hl
  have hlen : (l.length : ℕ∞) = (l'.length : ℕ∞) := by simp [l']
  rw [hlen]
  exact le_iSup₂_of_le l' hlast le_rfl

private lemma height_eq_of_algHom_integral_inj {d : ℕ} {B : Type*} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [Algebra ℂ B]
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] B) (hg_inj : Function.Injective g) (hg_int : g.IsIntegral)
    (mB : Ideal B) [mB.IsMaximal] :
    mB.height = (d : ℕ∞) := by
  let A := MvPolynomial (Fin d) ℂ
  letI : Algebra A B := g.toRingHom.toAlgebra
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hg_inj
  haveI : Algebra.IsIntegral A B := ⟨hg_int⟩
  haveI : IsIntegrallyClosed A := inferInstance
  haveI : Algebra.HasGoingDown A B := inferInstance
  let mA : Ideal A := mB.under A
  haveI : mA.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal mB
  haveI : mB.LiesOver mA := ⟨rfl⟩
  have hup1 : mB.height ≤ mA.height := height_le_height_under_of_isIntegral mB
  have hup2 : mA.height ≤ (d : ℕ∞) := by
    have h1 : (mA.height : WithBot ℕ∞) ≤ ringKrullDim A := Ideal.height_le_ringKrullDim_of_isPrime
    have h2 : ringKrullDim A = (d : WithBot ℕ∞) := by
      dsimp only [A]
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field ℂ, zero_add]
      simp
    rw [h2] at h1
    exact WithBot.coe_le_coe.mp h1
  have hlo1 : (d : ℕ∞) ≤ mA.height := by
    obtain ⟨x0, hx0⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ
      (inferInstance : mA.IsMaximal)
    let Tfwd : A →ₐ[ℂ] A := MvPolynomial.aeval fun r => X r + C (x0 r)
    let Tbwd : A →ₐ[ℂ] A := MvPolynomial.aeval fun r => X r - C (x0 r)
    have hfb : Tfwd.comp Tbwd = AlgHom.id ℂ A := by
      apply MvPolynomial.algHom_ext
      intro r
      dsimp only [A, Tfwd, Tbwd]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, map_sub, aeval_C,
        MvPolynomial.algebraMap_eq]
      ring
    have hbf : Tbwd.comp Tfwd = AlgHom.id ℂ A := by
      apply MvPolynomial.algHom_ext
      intro r
      dsimp only [A, Tfwd, Tbwd]
      simp only [AlgHom.comp_apply, AlgHom.id_apply, aeval_X, map_add, aeval_C,
        MvPolynomial.algebraMap_eq]
      ring
    let eT : A ≃+* A := (AlgEquiv.ofAlgHom Tfwd Tbwd hfb hbf).toRingEquiv
    let m0 : Ideal A := Ideal.span (Set.range (X : Fin d → A))
    haveI : m0.IsPrime := MvPolynomial.isPrime_idealOfVars (Fin d) ℂ
    have hcomap : m0.comap eT.toRingHom = mA := by
      ext p
      rw [Ideal.mem_comap, hx0, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval]
      have hev : eval 0 (eT p) = eval x0 p := by
        change eval 0 (Tfwd p) = eval x0 p
        dsimp only [Tfwd]
        rw [← aeval_eq_eval, ← aeval_eq_eval]
        have hcomp : (aeval (0 : Fin d → ℂ)).comp (aeval fun r => X r + C (x0 r)) = aeval x0 := by
          apply MvPolynomial.algHom_ext; intro r; simp
        exact AlgHom.congr_fun hcomp p
      rw [← hev]
      change eT p ∈ Ideal.span (Set.range X) ↔ eval 0 (eT p) = 0
      rw [eval_zero, ← Set.image_univ, mem_ideal_span_X_image]
      constructor
      · intro h
        rw [constantCoeff_eq]
        by_contra hc
        obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.mpr hc)
        exact hi rfl
      · intro h m hm
        have hm0 : m ≠ 0 := by
          rintro rfl
          rw [mem_support_iff, ← constantCoeff_eq] at hm
          exact hm h
        obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
        exact ⟨i, Set.mem_univ _, hi⟩
    have hge : m0.height ≤ mA.height := by
      rw [← hcomap]
      exact height_comap_ringEquiv eT m0
    exact (le_height_m0_complex d).trans hge
  have hlo2 : mA.height ≤ mB.height := by
    have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown mA mB
    rw [hgd]
    exact le_self_add
  exact le_antisymm (hup1.trans hup2) (hlo1.trans hlo2)

private lemma trdeg_eq_of_algHom_integral_inj {s : ℕ} {B : Type} [CommRing B] [IsDomain B]
    [Algebra ℂ B]
    (g : MvPolynomial (Fin s) ℂ →ₐ[ℂ] B) (hg_inj : Function.Injective g) (hg_int : g.IsIntegral) :
    Algebra.trdeg ℂ B = (s : Cardinal) := by
  have hge : (s : Cardinal) ≤ Algebra.trdeg ℂ B := by
    have h1 := trdeg_le_of_injective g hg_inj
    rw [MvPolynomial.trdeg_of_isDomain] at h1
    simpa using h1
  have hle : Algebra.trdeg ℂ B ≤ (s : Cardinal) := by
    let x : Fin s → B := fun r => g (X r)
    have hrange : Algebra.adjoin ℂ (Set.range x) = g.range := by
      have hg_eq : g = MvPolynomial.aeval x := by
        apply MvPolynomial.algHom_ext; intro r; simp [x]
      rw [hg_eq, Algebra.adjoin_range_eq_range_aeval]
    haveI : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range x)) B := by
      let φR : MvPolynomial (Fin s) ℂ →+* Algebra.adjoin ℂ (Set.range x) :=
        { toFun := fun q => ⟨g q, by rw [hrange]; exact AlgHom.mem_range_self g q⟩
          map_one' := Subtype.ext (map_one g)
          map_mul' := fun a b => Subtype.ext (map_mul g a b)
          map_zero' := Subtype.ext (map_zero g)
          map_add' := fun a b => Subtype.ext (map_add g a b) }
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hp_mon, hp_eval⟩ := hg_int b
      refine ⟨p.map φR, hp_mon.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range x)) B).comp φR = g.toRingHom := by
        apply RingHom.ext
        intro a
        rfl
      rw [hcomp]
      exact hp_eval
    haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) B := inferInstance
    have h1 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℂ (Set.range x)
    calc Algebra.trdeg ℂ B ≤ Cardinal.mk (Set.range x) := h1
      _ ≤ Cardinal.mk (Fin s) := Cardinal.mk_range_le
      _ = (s : Cardinal) := by simp
  exact le_antisymm hle hge

private lemma trdeg_ge_of_alg_X {d : ℕ} (B : Subalgebra ℂ (MvPolynomial (Fin d) ℂ))
    (halg_X : ∀ r : Fin d, IsAlgebraic B (X r : MvPolynomial (Fin d) ℂ)) :
    (d : Cardinal) ≤ Algebra.trdeg ℂ B := by
  have hmem : ∀ p : MvPolynomial (Fin d) ℂ,
      p ∈ Subalgebra.algebraicClosure B (MvPolynomial (Fin d) ℂ) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h1 : (C c : MvPolynomial (Fin d) ℂ) =
          algebraMap B (MvPolynomial (Fin d) ℂ) (algebraMap ℂ B c) := rfl
      rw [h1]
      exact Subalgebra.algebraMap_mem _ _
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p r hp => exact Subalgebra.mul_mem _ hp (by rw [Subalgebra.mem_algebraicClosure]; exact halg_X r)
  have : Algebra.IsAlgebraic B (MvPolynomial (Fin d) ℂ) :=
    ⟨fun p => by have hp := hmem p; rwa [Subalgebra.mem_algebraicClosure] at hp⟩
  have hadd := trdeg_add_eq (A := MvPolynomial (Fin d) ℂ) ℂ B
  have hzero : Algebra.trdeg B (MvPolynomial (Fin d) ℂ) = 0 := trdeg_eq_zero
  have hmv : Algebra.trdeg ℂ (MvPolynomial (Fin d) ℂ) = (d : Cardinal) := by
    rw [MvPolynomial.trdeg_of_isDomain]
    simp
  rw [hzero, add_zero, hmv] at hadd
  exact hadd.ge

set_option maxHeartbeats 600000 in
private lemma stage2_fiber_bound {σ : Type} [Fintype σ] [DecidableEq σ] {d n : ℕ}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ)
    (hΦ_deg : ∀ P, (Φ P).totalDegree ≤ n * P.totalDegree)
    (h𝔭_hom : ∀ P ∈ RingHom.ker Φ.toRingHom, ∀ m, homogeneousComponent m P ∈ RingHom.ker Φ.toRingHom)
    (htrdeg : Algebra.trdeg ℂ Φ.range = (d : Cardinal))
    (L : Fin d → MvPolynomial σ ℂ)
    (hLhom : ∀ h : Fin d, (L h).IsHomogeneous 1)
    (hLzero : ∀ ω : σ → ℂ, ω ∈ zeroLocus ℂ (RingHom.ker Φ.toRingHom) →
      (∀ h : Fin d, aeval ω (L h) = 0) → ω = 0) :
    AlgebraicIndependent ℂ (fun h : Fin d => Φ.rangeRestrict (L h)) ∧
      (MvPolynomial.aeval (fun h : Fin d => Φ.rangeRestrict (L h)) :
        MvPolynomial (Fin d) ℂ →ₐ[ℂ] Φ.range).IsIntegral ∧
      ∀ (y : Fin d → ℂ) (T : Finset (σ → ℂ)),
        (∀ ω ∈ T, ω ∈ zeroLocus ℂ (RingHom.ker Φ.toRingHom) ∧ ∀ h : Fin d, aeval ω (L h) = y h) →
        T.card ≤ n ^ d := by
  classical
  let 𝔭 : Ideal (MvPolynomial σ ℂ) := RingHom.ker Φ.toRingHom
  let I0 : Ideal (MvPolynomial σ ℂ) := 𝔭 ⊔ Ideal.span (Set.range L)
  have hpow : ∀ s : σ, ∃ N : ℕ, (X s : MvPolynomial σ ℂ) ^ N ∈ I0 := by
    intro s
    have hmem : (X s : MvPolynomial σ ℂ) ∈ vanishingIdeal ℂ (zeroLocus ℂ I0 : Set (σ → ℂ)) := by
      rw [mem_vanishingIdeal_iff]
      intro ω hω
      have hω0 : ω = 0 := hLzero ω
        (fun p hp => hω p (Ideal.mem_sup_left hp))
        (fun h => hω (L h) (Ideal.mem_sup_right (Ideal.subset_span ⟨h, rfl⟩)))
      simp [hω0]
    rw [vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  choose Npow hNpow using hpow
  let D0 : ℕ := ∑ s : σ, Npow s + 2
  have hD0_mon : ∀ (e : σ →₀ ℕ) (c : ℂ), D0 ≤ e.degree → monomial e c ∈ I0 := by
    intro e c he
    have hex : ∃ s : σ, Npow s ≤ e s := by
      by_contra hcon
      push Not at hcon
      have h1 : e.degree ≤ ∑ s : σ, Npow s := by
        rw [Finsupp.degree_eq_sum]
        exact Finset.sum_le_sum fun s _ => (hcon s).le
      omega
    obtain ⟨s, hs⟩ := hex
    have hle : Finsupp.single s (Npow s) ≤ e := by
      rw [Finsupp.single_le_iff]; exact hs
    have he' : e = (e - Finsupp.single s (Npow s)) + Finsupp.single s (Npow s) :=
      (tsub_add_cancel_of_le hle).symm
    rw [he', ← mul_one c, ← monomial_mul_monomial, ← X_pow_eq_monomial]
    exact Ideal.mul_mem_left _ _ (hNpow s)
  have hhom_decomp : ∀ {D : ℕ}, D0 ≤ D → ∀ p : MvPolynomial σ ℂ, p.IsHomogeneous D →
      ∃ (p0 : MvPolynomial σ ℂ) (a : Fin d → MvPolynomial σ ℂ),
        p0 ∈ 𝔭 ∧ (∀ h : Fin d, (a h).IsHomogeneous (D - 1)) ∧
        p = p0 + ∑ h : Fin d, a h * L h := by
    intro D hD p hp
    have hpI0 : p ∈ I0 := by
      rw [p.as_sum]
      refine Ideal.sum_mem _ fun e he => hD0_mon e _ ?_
      have h := hp (mem_support_iff.mp he)
      rw [Finsupp.degree_eq_weight_one]
      exact h.symm ▸ hD
    rw [Submodule.mem_sup] at hpI0
    obtain ⟨q0, hq0, q1, hq1, hqeq⟩ := hpI0
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq1
    refine ⟨homogeneousComponent D q0, fun h => homogeneousComponent (D - 1) (c h),
      h𝔭_hom q0 hq0 D, fun h => homogeneousComponent_isHomogeneous _ _, ?_⟩
    have hpD : homogeneousComponent D p = p := (homogeneousComponent_of_mem hp).trans (by simp)
    rw [← hpD, ← hqeq, map_add, ← hc, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    exact weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right (hLhom h) (by omega)
  let ℓ : Fin d → Φ.range := fun h => Φ.rangeRestrict (L h)
  let gL : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Φ.range := MvPolynomial.aeval ℓ
  letI : Algebra (MvPolynomial (Fin d) ℂ) Φ.range := gL.toRingHom.toAlgebra
  let smallMons : Finset (σ → ℕ) :=
    (Fintype.piFinset fun _ : σ => Finset.range D0).filter fun a => ∑ s, a s < D0
  let genSet : Finset Φ.range :=
    smallMons.image fun a => Φ.rangeRestrict (monomial (Finsupp.equivFunOnFinite.symm a) 1)
  have hspan_top : Submodule.span (MvPolynomial (Fin d) ℂ) (genSet : Set Φ.range) = ⊤ := by
    rw [eq_top_iff]
    suffices hAll : ∀ P : MvPolynomial σ ℂ,
        Φ.rangeRestrict P ∈ Submodule.span (MvPolynomial (Fin d) ℂ) (genSet : Set Φ.range) by
      intro x _
      obtain ⟨P, hP⟩ := x.2
      have hx : x = Φ.rangeRestrict P := Subtype.ext hP.symm
      rw [hx]
      exact hAll P
    intro P
    induction hdeg : P.totalDegree using Nat.strong_induction_on generalizing P with
    | _ D ih =>
    by_cases hlt : D < D0
    · have hPsum : Φ.rangeRestrict P =
          ∑ e ∈ P.support, P.coeff e • Φ.rangeRestrict (monomial e 1) := by
        apply Subtype.ext
        change Φ P = Φ.range.val (∑ e ∈ P.support, P.coeff e • Φ.rangeRestrict (monomial e 1))
        rw [map_sum]
        conv_lhs => rw [P.as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [map_smul]
        change Φ (monomial e (P.coeff e)) = P.coeff e • Φ (monomial e 1)
        rw [show monomial e (P.coeff e) = P.coeff e • monomial e (1 : ℂ) by
          rw [smul_monomial, smul_eq_mul, mul_one], map_smul]
      rw [hPsum]
      refine Submodule.sum_mem _ fun e he => ?_
      have hsmul : P.coeff e • Φ.rangeRestrict (monomial e 1) =
          (C (P.coeff e) : MvPolynomial (Fin d) ℂ) • Φ.rangeRestrict (monomial e 1) := by
        rw [Algebra.smul_def, Algebra.smul_def]
        change algebraMap ℂ Φ.range (P.coeff e) * Φ.rangeRestrict (monomial e 1) =
          gL (C (P.coeff e)) * Φ.rangeRestrict (monomial e 1)
        rw [show gL (C (P.coeff e)) = algebraMap ℂ Φ.range (P.coeff e) from aeval_C _ _]
      rw [hsmul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      simp only [genSet, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      refine ⟨⇑e, ?_, by simp⟩
      simp only [smallMons, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
      have hedeg : ∑ s : σ, e s < D0 := by
        rw [← Finsupp.degree_eq_sum]
        have hed : e.degree ≤ P.totalDegree := le_totalDegree he
        omega
      refine ⟨fun s => ?_, hedeg⟩
      have h1 : e s ≤ ∑ t : σ, e t :=
        Finset.single_le_sum (f := fun t => e t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
      omega
    · push Not at hlt
      have hDpos : 0 < D := by omega
      obtain ⟨p0, a, hp0, ha, hdecomp⟩ :=
        hhom_decomp hlt (homogeneousComponent D P) (homogeneousComponent_isHomogeneous D P)
      let P' := P - homogeneousComponent D P
      have hP'deg : P'.totalDegree < D :=
        totalDegree_sub_homogeneousComponent_lt P hdeg.le hDpos
      have hmemP' := ih _ hP'deg P' rfl
      have hPeq : Φ.rangeRestrict P =
          Φ.rangeRestrict P' +
            ∑ h : Fin d, (X h : MvPolynomial (Fin d) ℂ) • Φ.rangeRestrict (a h) := by
        apply Subtype.ext
        change Φ P = Φ.range.val (Φ.rangeRestrict P' +
          ∑ h : Fin d, (X h : MvPolynomial (Fin d) ℂ) • Φ.rangeRestrict (a h))
        rw [map_add, map_sum]
        have hPsplit : P = P' + homogeneousComponent D P := by dsimp only [P']; ring
        conv_lhs => rw [hPsplit, hdecomp]
        rw [map_add, map_add, show Φ p0 = 0 from hp0, zero_add, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Algebra.smul_def]
        change Φ (a h * L h) = Φ.range.val (gL (X h) * Φ.rangeRestrict (a h))
        simp only [gL, aeval_X, ℓ, map_mul]
        change Φ (a h) * Φ (L h) = Φ (L h) * Φ (a h)
        rw [mul_comm]
      rw [hPeq]
      refine Submodule.add_mem _ hmemP' (Submodule.sum_mem _ fun h _ => ?_)
      refine Submodule.smul_mem _ _ (ih _ ?_ (a h) rfl)
      have := (ha h).totalDegree_le
      omega
  have : Module.Finite (MvPolynomial (Fin d) ℂ) Φ.range := ⟨⟨genSet, hspan_top⟩⟩
  have : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) Φ.range := inferInstance
  have hgL_int : gL.IsIntegral := fun b =>
    Algebra.IsIntegral.isIntegral (R := MvPolynomial (Fin d) ℂ) b
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range ℓ)) Φ.range := by
    have hrange : Algebra.adjoin ℂ (Set.range ℓ) = gL.range :=
      Algebra.adjoin_range_eq_range_aeval ℂ ℓ
    let φR : MvPolynomial (Fin d) ℂ →+* Algebra.adjoin ℂ (Set.range ℓ) :=
      { toFun := fun q => ⟨gL q, by rw [hrange]; exact AlgHom.mem_range_self gL q⟩
        map_one' := Subtype.ext (map_one gL)
        map_mul' := fun x y => Subtype.ext (map_mul gL x y)
        map_zero' := Subtype.ext (map_zero gL)
        map_add' := fun x y => Subtype.ext (map_add gL x y) }
    refine ⟨fun b => ?_⟩
    obtain ⟨p, hp_mon, hp_eval⟩ := hgL_int b
    refine ⟨p.map φR, (hp_mon.map φR).ne_zero, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap (Algebra.adjoin ℂ (Set.range ℓ)) Φ.range).comp φR = gL.toRingHom := by
      apply RingHom.ext; intro a; rfl
    rw [hcomp]
    exact hp_eval
  have hindep : AlgebraicIndependent ℂ ℓ := by
    refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℂ ℓ ?_).1
    rw [htrdeg]
    simp
  have hgL_inj : Function.Injective gL := hindep
  refine ⟨hindep, hgL_int, fun y T hT => ?_⟩
  by_cases hTempty : T = ∅
  · simp [hTempty]
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) Φ.range :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hgL_inj
  haveI : IsIntegrallyClosed (MvPolynomial (Fin d) ℂ) := inferInstance
  let ψ : (σ → ℂ) → (Φ.range →ₐ[ℂ] ℂ) := fun ω =>
    if hω : ω ∈ zeroLocus ℂ 𝔭 then
      (Ideal.Quotient.liftₐ 𝔭 (MvPolynomial.aeval ω) fun p hp => hω p hp).comp
        (Ideal.quotientKerEquivRange Φ).symm.toAlgHom
    else AlgHom.comp (MvPolynomial.aeval (0 : Fin d → ℂ)) Φ.range.val
  have hψ_apply : ∀ (ω : σ → ℂ), ω ∈ zeroLocus ℂ 𝔭 → ∀ P : MvPolynomial σ ℂ,
      ψ ω (Φ.rangeRestrict P) = aeval ω P := by
    intro ω hω P
    dsimp only [ψ]
    rw [dif_pos hω]
    change (Ideal.Quotient.liftₐ 𝔭 (MvPolynomial.aeval ω) fun p hp => hω p hp)
      ((Ideal.quotientKerEquivRange Φ).symm (Φ.rangeRestrict P)) = aeval ω P
    have hsymm : (Ideal.quotientKerEquivRange Φ).symm (Φ.rangeRestrict P) =
        Ideal.Quotient.mk 𝔭 P :=
      (Ideal.quotientKerEquivRange Φ).injective (AlgEquiv.apply_symm_apply _ _)
    rw [hsymm]
    rfl
  have hψ_on_A : ∀ (ω : σ → ℂ), ω ∈ T → ∀ p : MvPolynomial (Fin d) ℂ,
      ψ ω (algebraMap (MvPolynomial (Fin d) ℂ) Φ.range p) = MvPolynomial.aeval y p := by
    intro ω hω p
    have hcomp : (ψ ω).comp gL = MvPolynomial.aeval y := by
      apply MvPolynomial.algHom_ext
      intro h
      simp only [AlgHom.comp_apply, gL, aeval_X, ℓ]
      rw [hψ_apply ω (hT ω hω).1 (L h), (hT ω hω).2 h]
    exact AlgHom.congr_fun hcomp p
  let eT : T ≃ Fin T.card := Fintype.equivFinOfCardEq (Fintype.card_coe T)
  have hsepT : ∀ ω : T, ∃ p : MvPolynomial σ ℂ,
      aeval ω.1 p = 1 ∧ ∀ ω' ∈ T, ω' ≠ ω.1 → aeval ω' p = 0 :=
    fun ω => by
      obtain ⟨p, h1, h2⟩ := exists_sep_fin T ω.1
      exact ⟨p, by simpa [aeval_eq_eval] using h1, fun ω' hω' hne => by
        simpa [aeval_eq_eval] using h2 ω' hω' hne⟩
  choose pSep hpSep using hsepT
  let p_b : MvPolynomial σ ℂ := ∑ ω : T, C (((eT ω).val : ℕ) : ℂ) * pSep ω
  let b : Φ.range := Φ.rangeRestrict p_b
  have hψ_b : ∀ ω : T, ψ ω.1 b = ((eT ω).val : ℂ) := by
    intro ω
    rw [hψ_apply ω.1 (hT ω.1 ω.2).1 p_b]
    simp only [p_b, map_sum, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finset.sum_eq_single ω]
    · rw [(hpSep ω).1, mul_one]
    · intro ω' _ hne
      have hne' : ω.1 ≠ ω'.1 := fun h => hne (Subtype.ext h.symm)
      rw [(hpSep ω').2 ω.1 ω.2 hne', mul_zero]
    · intro h; exact (h (Finset.mem_univ ω)).elim
  let f : Polynomial (MvPolynomial (Fin d) ℂ) := minpoly (MvPolynomial (Fin d) ℂ) b
  let m : ℕ := f.natDegree
  have hb_int : IsIntegral (MvPolynomial (Fin d) ℂ) b := Algebra.IsIntegral.isIntegral b
  have hf_mon : f.Monic := minpoly.monic hb_int
  let fC : Polynomial ℂ := f.map (MvPolynomial.aeval y).toRingHom
  have hfC_mon : fC.Monic := hf_mon.map _
  have hfC_ne : fC ≠ 0 := hfC_mon.ne_zero
  have hfC_deg : fC.natDegree = m := hf_mon.natDegree_map _
  have hT_le_m : T.card ≤ m := by
    have hinj : Function.Injective (fun ω : T => ψ ω.1 b) := by
      intro ω1 ω2 hEq
      dsimp only at hEq
      rw [hψ_b ω1, hψ_b ω2] at hEq
      have hval : (eT ω1).val = (eT ω2).val := Nat.cast_injective hEq
      exact eT.injective (Fin.ext hval)
    have hroot : ∀ ω : T, ψ ω.1 b ∈ fC.roots.toFinset := by
      intro ω
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hfC_ne, Polynomial.IsRoot]
      have h1 : Polynomial.aeval b f = 0 := minpoly.aeval _ b
      have h2 := congrArg (ψ ω.1) h1
      rw [map_zero] at h2
      have h3 : fC.eval (ψ ω.1 b) = ψ ω.1 (Polynomial.aeval b f) := by
        dsimp only [fC]
        rw [Polynomial.eval_map, Polynomial.aeval_def]
        change Polynomial.eval₂ (MvPolynomial.aeval y).toRingHom ((ψ ω.1).toRingHom b) f =
          (ψ ω.1).toRingHom (Polynomial.eval₂ (algebraMap (MvPolynomial (Fin d) ℂ) Φ.range) b f)
        rw [Polynomial.hom_eval₂]
        congr 1
        apply RingHom.ext
        intro p
        exact (hψ_on_A ω.1 ω.2 p).symm
      rw [h3, h2]
    calc T.card = Fintype.card T := (Fintype.card_coe T).symm
      _ = (Finset.univ.image fun ω : T => ψ ω.1 b).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ fC.roots.toFinset.card := Finset.card_le_card fun z hz => by
          rcases Finset.mem_image.mp hz with ⟨ω, _, rfl⟩
          exact hroot ω
      _ ≤ fC.roots.card := Multiset.toFinset_card_le _
      _ ≤ fC.natDegree := Polynomial.card_roots' fC
      _ = m := hfC_deg
  have hpow_li : LinearIndependent (MvPolynomial (Fin d) ℂ) (fun j : Fin m => b ^ j.val) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    let Q : Polynomial (MvPolynomial (Fin d) ℂ) := ∑ i : Fin m, Polynomial.C (g i) * Polynomial.X ^ i.val
    have hQ_ev : Polynomial.aeval b Q = 0 := by
      simp only [Q, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, map_pow]
      simpa [Algebra.smul_def] using hg
    have hdvd : f ∣ Q := minpoly.isIntegrallyClosed_dvd hb_int hQ_ev
    have hQ0 : Q = 0 := by
      by_contra hne
      have hle : f.natDegree ≤ Q.natDegree := Polynomial.natDegree_le_of_dvd hdvd hne
      have hlt : Q.natDegree < m := by
        by_cases hm0 : m = 0
        · exfalso
          apply hne
          dsimp only [Q]
          rw [Finset.sum_eq_zero]
          intro i _; exact Fin.elim0 (hm0 ▸ i)
        · have hle_m1 : Q.natDegree ≤ m - 1 := by
            refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
            have h1 := Polynomial.natDegree_C_mul_X_pow_le (g i) i.val
            omega
          omega
      omega
    have hc := congrArg (fun p : Polynomial (MvPolynomial (Fin d) ℂ) => p.coeff j.val) hQ0
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa using hc
    · intro i _ hij
      simp [Fin.val_ne_of_ne hij.symm]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  let Edeg : ℕ := p_b.totalDegree
  have hcount_K : ∀ K : ℕ, m * (simplexFinset d K).card ≤
      (simplexFinset d (n * K + n * m * Edeg)).card := by
    intro K
    let v : Fin m × simplexFinset d K → MvPolynomial (Fin d) ℂ := fun p =>
      (algebraMap (MvPolynomial (Fin d) ℂ) Φ.range
        (monomial (Finsupp.equivFunOnFinite.symm p.2.1) 1) * b ^ p.1.val).1
    have hv_li : LinearIndependent ℂ v := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      let g : Fin m → MvPolynomial (Fin d) ℂ := fun j =>
        ∑ a : simplexFinset d K, monomial (Finsupp.equivFunOnFinite.symm a.1) (c (j, a))
      have hsum0 : ∑ j : Fin m, g j • b ^ j.val = 0 := by
        apply Subtype.ext
        change Φ.range.val (∑ j : Fin m, g j • b ^ j.val) = 0
        rw [map_sum]
        have hrew : (∑ j : Fin m, Φ.range.val (g j • b ^ j.val)) =
            ∑ p : Fin m × simplexFinset d K, c p • v p := by
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl fun j _ => ?_
          dsimp only [g, v]
          rw [Algebra.smul_def, map_sum, Finset.sum_mul, map_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          have hmon : monomial (Finsupp.equivFunOnFinite.symm a.1) (c (j, a)) =
              c (j, a) • monomial (Finsupp.equivFunOnFinite.symm a.1) (1 : ℂ) := by
            rw [smul_monomial, smul_eq_mul, mul_one]
          rw [hmon]
          change Φ.range.val (gL (c (j, a) • monomial (Finsupp.equivFunOnFinite.symm a.1) 1) * b ^ j.val) =
            c (j, a) • Φ.range.val (gL (monomial (Finsupp.equivFunOnFinite.symm a.1) 1) * b ^ j.val)
          rw [map_smul, smul_mul_assoc, map_smul]
        rw [hrew, hc]
      have hg0 := Fintype.linearIndependent_iff.mp hpow_li g hsum0
      intro p
      have hcoeff := congrArg (fun f : MvPolynomial (Fin d) ℂ =>
        f.coeff (Finsupp.equivFunOnFinite.symm p.2.1)) (hg0 p.1)
      change (g p.1).coeff (Finsupp.equivFunOnFinite.symm p.2.1) = 0 at hcoeff
      simp only [g, coeff_sum, coeff_monomial] at hcoeff
      rw [Finset.sum_eq_single p.2] at hcoeff
      · simpa using hcoeff
      · intro a _ hap
        have hne : Finsupp.equivFunOnFinite.symm a.1 ≠ Finsupp.equivFunOnFinite.symm p.2.1 :=
          fun h => hap (Subtype.ext (Finsupp.equivFunOnFinite.symm.injective h))
        simp [hne]
      · intro hp; exact absurd (Finset.mem_univ p.2) hp
    have hv_mem : ∀ p : Fin m × simplexFinset d K,
        v p ∈ restrictTotalDegree (Fin d) ℂ (n * K + n * m * Edeg) := by
      intro p
      rw [mem_restrictTotalDegree]
      let Q : MvPolynomial σ ℂ := (∏ r : Fin d, (L r) ^ (p.2.1 r)) * p_b ^ p.1.val
      have hvQ : v p = Φ Q := by
        dsimp only [v, Q]
        change Φ.range.val (gL (monomial (Finsupp.equivFunOnFinite.symm p.2.1) 1) * b ^ p.1.val) = _
        rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_mul, map_mul, map_pow, map_pow,
          map_prod, map_prod, map_prod]
        congr 1
        rw [Finset.prod_subset (Finset.subset_univ _) fun r _ hr => by
          rw [Finsupp.notMem_support_iff] at hr
          simp [hr]]
        refine Finset.prod_congr rfl fun r _ => ?_
        simp only [gL, map_pow, aeval_X, ℓ, Finsupp.coe_equivFunOnFinite_symm]
        rfl
      rw [hvQ]
      have hQdeg : Q.totalDegree ≤ K + m * Edeg := by
        dsimp only [Q]
        calc ((∏ r : Fin d, (L r) ^ (p.2.1 r)) * p_b ^ p.1.val).totalDegree
            ≤ (∏ r : Fin d, (L r) ^ (p.2.1 r)).totalDegree + (p_b ^ p.1.val).totalDegree :=
              totalDegree_mul _ _
          _ ≤ (∑ r : Fin d, ((L r) ^ (p.2.1 r)).totalDegree) + p.1.val * Edeg :=
              Nat.add_le_add (totalDegree_finsetProd _ _) (totalDegree_pow _ _)
          _ ≤ (∑ r : Fin d, p.2.1 r * (L r).totalDegree) + m * Edeg :=
              Nat.add_le_add
                (Finset.sum_le_sum fun r _ => totalDegree_pow _ _)
                (Nat.mul_le_mul_right Edeg p.1.isLt.le)
          _ ≤ (∑ r : Fin d, p.2.1 r * 1) + m * Edeg :=
              Nat.add_le_add
                (Finset.sum_le_sum fun r _ => Nat.mul_le_mul_left _ (hLhom r).totalDegree_le)
                le_rfl
          _ = (∑ r : Fin d, p.2.1 r) + m * Edeg := by simp
          _ ≤ K + m * Edeg := Nat.add_le_add_right (mem_simplexFinset.mp p.2.2) _
      calc (Φ Q).totalDegree ≤ n * Q.totalDegree := hΦ_deg Q
        _ ≤ n * (K + m * Edeg) := Nat.mul_le_mul_left n hQdeg
        _ = n * K + n * m * Edeg := by ring
    let vSub : Fin m × simplexFinset d K → restrictTotalDegree (Fin d) ℂ (n * K + n * m * Edeg) :=
      fun p => ⟨v p, hv_mem p⟩
    have hvSub_li : LinearIndependent ℂ vSub :=
      hv_li.of_comp (restrictTotalDegree (Fin d) ℂ (n * K + n * m * Edeg)).subtype
    have hcard_le : Fintype.card (Fin m × simplexFinset d K) ≤
        Module.finrank ℂ (restrictTotalDegree (Fin d) ℂ (n * K + n * m * Edeg)) :=
      hvSub_li.fintype_card_le_finrank
    have h1 : Fintype.card (Fin m × simplexFinset d K) = m * (simplexFinset d K).card := by
      simp [Fintype.card_prod]
    rw [← h1]
    exact hcard_le.trans (finrank_restrictTotalDegree_le_simplex d _)
  have hm_le : m ≤ n ^ d := by
    refine nat_le_pow_of_asymptotic m n d (n * m * Edeg) fun K => ?_
    have h1 := Nat.mul_le_mul_right d.factorial (hcount_K K)
    rw [mul_assoc, simplexFinset_card_mul_factorial, simplexFinset_card_mul_factorial] at h1
    have hlo : (K + 1) ^ d ≤ ∏ j : Fin d, (K + j.val + 1) := by
      rw [show (K + 1) ^ d = ∏ _j : Fin d, (K + 1) by simp]
      exact Finset.prod_le_prod fun j _ => by omega
    have hhi : ∏ j : Fin d, (n * K + n * m * Edeg + j.val + 1) ≤
        (n * K + n * m * Edeg + d) ^ d := by
      rw [show (n * K + n * m * Edeg + d) ^ d = ∏ _j : Fin d, (n * K + n * m * Edeg + d) by simp]
      exact Finset.prod_le_prod fun j _ => by have := j.isLt; omega
    calc m * (K + 1) ^ d ≤ m * ∏ j : Fin d, (K + j.val + 1) := Nat.mul_le_mul_left m hlo
      _ ≤ ∏ j : Fin d, (n * K + n * m * Edeg + j.val + 1) := h1
      _ ≤ (n * K + n * m * Edeg + d) ^ d := hhi
  exact hT_le_m.trans hm_le

private lemma quot_mB_height {σ : Type} [Fintype σ] {d : ℕ}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ)
    (h𝔭_hom : ∀ P ∈ RingHom.ker Φ.toRingHom, ∀ m, homogeneousComponent m P ∈ RingHom.ker Φ.toRingHom)
    (htrdeg : Algebra.trdeg ℂ Φ.range = (d : Cardinal)) :
    (Ideal.span (Set.range fun s : σ =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (X s))).IsMaximal ∧
    (Ideal.span (Set.range fun s : σ =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (X s))).height = (d : ℕ∞) := by
  let 𝔭 : Ideal (MvPolynomial σ ℂ) := RingHom.ker Φ.toRingHom
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime Φ.toRingHom
  let Bq := MvPolynomial σ ℂ ⧸ 𝔭
  let mkB : MvPolynomial σ ℂ →ₐ[ℂ] Bq := Ideal.Quotient.mkₐ ℂ 𝔭
  have hmkB_surj : Function.Surjective mkB := Ideal.Quotient.mk_surjective
  let eB : Bq ≃ₐ[ℂ] Φ.range := Ideal.quotientKerEquivRange Φ
  haveI : IsDomain Bq := Ideal.Quotient.isDomain 𝔭
  haveI : IsNoetherianRing Bq := Ideal.Quotient.isNoetherianRing 𝔭
  have htrdeg_Bq : Algebra.trdeg ℂ Bq = (d : Cardinal) := by
    have h1 := trdeg_le_of_injective eB.toAlgHom eB.injective
    have h2 := trdeg_le_of_injective eB.symm.toAlgHom eB.symm.injective
    rw [htrdeg] at h1 h2
    exact le_antisymm h1 h2
  let m0 : Ideal (MvPolynomial σ ℂ) := Ideal.span (Set.range (X : σ → MvPolynomial σ ℂ))
  let mB : Ideal Bq := Ideal.span (Set.range fun s : σ => Ideal.Quotient.mk 𝔭 (X s))
  have hm0_ker : m0 = RingHom.ker (MvPolynomial.eval (0 : σ → ℂ)) := by
    ext p
    rw [RingHom.mem_ker, eval_zero]
    dsimp only [m0]
    rw [← Set.image_univ, mem_ideal_span_X_image]
    constructor
    · intro h
      rw [constantCoeff_eq]
      by_contra hc
      obtain ⟨i, -, hi⟩ := h 0 (mem_support_iff.mpr hc)
      exact hi rfl
    · intro h e he
      have he0 : e ≠ 0 := by
        rintro rfl
        rw [mem_support_iff, ← constantCoeff_eq] at he
        exact he h
      obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he0
      exact ⟨i, Set.mem_univ _, hi⟩
  have hmB_comap : mB.comap mkB.toRingHom = m0 := by
    have hker_le : 𝔭 ≤ m0 := homogeneous_prime_le_m0 𝔭 h𝔭_hom
    have hmap : m0.map mkB.toRingHom = mB := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    rw [← hmap]
    exact (Ideal.comap_map_of_surjective _ hmkB_surj m0).trans
      (sup_eq_left.mpr (by
        rw [← RingHom.ker_eq_comap_bot]
        exact fun p hp => hker_le (Ideal.Quotient.eq_zero_iff_mem.mp hp)))
  have hmB_max : mB.IsMaximal := by
    let ev0B : Bq →+* ℂ :=
      Ideal.Quotient.lift 𝔭 (MvPolynomial.eval (0 : σ → ℂ)) fun p hp => by
        have hm0p : p ∈ m0 := homogeneous_prime_le_m0 𝔭 h𝔭_hom hp
        rw [hm0_ker] at hm0p
        exact hm0p
    have hmB_ker : mB = RingHom.ker ev0B := by
      ext x
      obtain ⟨p, rfl⟩ := hmkB_surj x
      have h1 : mkB p ∈ mB ↔ p ∈ m0 := by
        rw [← hmB_comap]
        rfl
      rw [h1, hm0_ker, RingHom.mem_ker, RingHom.mem_ker]
      rfl
    rw [hmB_ker]
    exact RingHom.ker_isMaximal_of_surjective ev0B fun c =>
      ⟨mkB (C c), by change MvPolynomial.eval (0 : σ → ℂ) (C c) = c; exact eval_C c⟩
  have : Algebra.FiniteType ℂ Bq := Algebra.FiniteType.of_surjective mkB hmkB_surj
  obtain ⟨s, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg ℂ Bq
  have hs_eq : s = d := by
    have h1 := trdeg_eq_of_algHom_integral_inj g hg_inj hg_int
    rw [htrdeg_Bq] at h1
    exact Nat.cast_injective h1.symm
  subst hs_eq
  exact ⟨hmB_max, height_eq_of_algHom_integral_inj g hg_inj hg_int mB⟩

private lemma quot_minPrime_le_mB {σ : Type} [Fintype σ] {d k : ℕ}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ)
    (h𝔭_hom : ∀ P ∈ RingHom.ker Φ.toRingHom, ∀ m, homogeneousComponent m P ∈ RingHom.ker Φ.toRingHom)
    (L : Fin k → MvPolynomial σ ℂ) (hL : ∀ i, (L i).IsHomogeneous 1)
    (Q : Ideal (MvPolynomial σ ℂ ⧸ RingHom.ker Φ.toRingHom))
    (hQ : Q ∈ (Ideal.span (Set.range fun i =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (L i))).minimalPrimes) :
    Q ≤ Ideal.span (Set.range fun s : σ =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (X s)) := by
  let 𝔭 : Ideal (MvPolynomial σ ℂ) := RingHom.ker Φ.toRingHom
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime Φ.toRingHom
  let mkB : MvPolynomial σ ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ 𝔭) := Ideal.Quotient.mkₐ ℂ 𝔭
  have hmkB_surj : Function.Surjective mkB := Ideal.Quotient.mk_surjective
  let m0 : Ideal (MvPolynomial σ ℂ) := Ideal.span (Set.range (X : σ → MvPolynomial σ ℂ))
  let mB : Ideal (MvPolynomial σ ℂ ⧸ 𝔭) :=
    Ideal.span (Set.range fun s : σ => Ideal.Quotient.mk 𝔭 (X s))
  have hmB_comap : mB.comap mkB.toRingHom = m0 := by
    have hker_le : 𝔭 ≤ m0 := homogeneous_prime_le_m0 𝔭 h𝔭_hom
    have hmap : m0.map mkB.toRingHom = mB := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [← hmap]
    exact (Ideal.comap_map_of_surjective _ hmkB_surj m0).trans
      (sup_eq_left.mpr (by
        rw [← RingHom.ker_eq_comap_bot]
        exact fun p hp => hker_le (Ideal.Quotient.eq_zero_iff_mem.mp hp)))
  let J : Ideal (MvPolynomial σ ℂ) := 𝔭 ⊔ Ideal.span (Set.range L)
  have hJhom : ∀ f ∈ J, ∀ m, homogeneousComponent m f ∈ J := by
    intro f hf m
    rw [Submodule.mem_sup] at hf
    obtain ⟨p0, hp0, q1, hq1, rfl⟩ := hf
    rw [map_add]
    refine Ideal.add_mem J (Ideal.mem_sup_left (h𝔭_hom p0 hp0 m)) (Ideal.mem_sup_right ?_)
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq1
    rw [← hc, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hm0 : m = 0
    · subst hm0
      have hL0 : constantCoeff (L i) = 0 := by
        have := (hL i).coeff_eq_zero (d := 0) (by simp)
        rwa [constantCoeff_eq]
      rw [homogeneousComponent_zero, ← constantCoeff_eq, map_mul, hL0, mul_zero, map_zero]
      exact Ideal.zero_mem _
    · change weightedHomogeneousComponent 1 m (c i * L i) ∈ Ideal.span (Set.range L)
      rw [weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right (hL i) (by omega)]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  let QR : Ideal (MvPolynomial σ ℂ) := Q.comap mkB.toRingHom
  haveI : Q.IsPrime := hQ.isPrime
  haveI : QR.IsPrime := Ideal.comap_isPrime mkB.toRingHom Q
  have hQR_min : QR ∈ J.minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun P ⟨hPprime, hJP⟩ hPQR => ?_⟩
    · refine sup_le ?_ (Ideal.span_le.mpr ?_)
      · intro p hp
        change mkB p ∈ Q
        rw [show mkB p = 0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hp]
        exact Q.zero_mem
      · rintro _ ⟨i, rfl⟩
        exact hQ.le (Ideal.subset_span ⟨i, rfl⟩)
    · have hkerP : RingHom.ker mkB.toRingHom ≤ P :=
        fun p hp => hJP (Ideal.mem_sup_left (Ideal.Quotient.eq_zero_iff_mem.mp hp))
      let PB := P.map mkB.toRingHom
      haveI : PB.IsPrime := Ideal.map_isPrime_of_surjective hmkB_surj hkerP
      have hIB_le : Ideal.span (Set.range fun i => Ideal.Quotient.mk 𝔭 (L i)) ≤ PB := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact Ideal.mem_map_of_mem _ (hJP (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)))
      have hPB_le_Q : PB ≤ Q := by
        rw [Ideal.map_le_iff_le_comap]
        exact hPQR
      have hQ_le_PB : Q ≤ PB := hQ.2 ⟨inferInstance, hIB_le⟩ hPB_le_Q
      intro x hx
      have hxPB : mkB x ∈ PB := hQ_le_PB hx
      have hcom : PB.comap mkB.toRingHom = P :=
        (Ideal.comap_map_of_surjective _ hmkB_surj P).trans
          (sup_eq_left.mpr (by rw [← RingHom.ker_eq_comap_bot]; exact hkerP))
      rw [← hcom]
      exact hxPB
  have hQR_hom := prime_homogeneous_of_minimalPrime_of_homogeneous J hJhom QR hQR_min
  have hQR_le_m0 : QR ≤ m0 := homogeneous_prime_le_m0 QR hQR_hom
  intro x hx
  obtain ⟨p, rfl⟩ := hmkB_surj x
  have hp : p ∈ QR := hx
  have hpm0 : p ∈ m0 := hQR_le_m0 hp
  rw [← hmB_comap] at hpm0
  exact hpm0

private lemma quot_zeroLocus_eq_zero {σ : Type} [Fintype σ] {d : ℕ}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ)
    (h𝔭_hom : ∀ P ∈ RingHom.ker Φ.toRingHom, ∀ m, homogeneousComponent m P ∈ RingHom.ker Φ.toRingHom)
    (htrdeg : Algebra.trdeg ℂ Φ.range = (d : Cardinal))
    (L : Fin d → MvPolynomial σ ℂ) (hL : ∀ h : Fin d, (L h).IsHomogeneous 1)
    (hLht : ∀ P ∈ (Ideal.span (Set.range fun h : Fin d =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (L h))).minimalPrimes, (d : ℕ∞) ≤ P.height) :
    ∀ ω : σ → ℂ, ω ∈ zeroLocus ℂ (RingHom.ker Φ.toRingHom) →
      (∀ h : Fin d, aeval ω (L h) = 0) → ω = 0 := by
  intro ω hωp hωL
  let 𝔭 : Ideal (MvPolynomial σ ℂ) := RingHom.ker Φ.toRingHom
  let mkB : MvPolynomial σ ℂ →ₐ[ℂ] (MvPolynomial σ ℂ ⧸ 𝔭) := Ideal.Quotient.mkₐ ℂ 𝔭
  have hmkB_surj : Function.Surjective mkB := Ideal.Quotient.mk_surjective
  let mB : Ideal (MvPolynomial σ ℂ ⧸ 𝔭) :=
    Ideal.span (Set.range fun s : σ => Ideal.Quotient.mk 𝔭 (X s))
  obtain ⟨hmB_max, hmB_height⟩ := quot_mB_height Φ h𝔭_hom htrdeg
  have : mB.IsPrime := hmB_max.isPrime
  let Ifull : Ideal (MvPolynomial σ ℂ ⧸ 𝔭) :=
    Ideal.span (Set.range fun h : Fin d => Ideal.Quotient.mk 𝔭 (L h))
  have hmin_eq : ∀ P ∈ Ifull.minimalPrimes, P = mB := by
    intro P hP
    have : P.IsPrime := hP.isPrime
    have hPle : P ≤ mB := quot_minPrime_le_mB Φ h𝔭_hom L hL P hP
    have hPge : mB.height ≤ P.height := by rw [hmB_height]; exact hLht P hP
    have : P.FiniteHeight := ⟨Or.inr (by
      have : P.height ≤ (d : ℕ∞) := by rw [← hmB_height]; exact Ideal.height_mono hPle
      exact ne_top_of_le_ne_top (ENat.coe_ne_top d) this)⟩
    exact eq_of_le_of_not_lt hPle fun hlt =>
      not_le.mpr (Ideal.height_strict_mono_of_isPrime hlt) hPge
  have hmB_le_rad : mB ≤ Ifull.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hIfP, hPprime⟩ => ?_
    have := hPprime
    obtain ⟨Q, hQmin, hQleP⟩ := Ideal.exists_minimalPrimes_le hIfP
    rw [← hmin_eq Q hQmin]
    exact hQleP
  funext s
  have hX_rad : mkB (X s) ∈ Ifull.radical := hmB_le_rad (Ideal.subset_span ⟨s, rfl⟩)
  obtain ⟨N, hN⟩ := hX_rad
  have hXN : (X s : MvPolynomial σ ℂ) ^ N ∈ 𝔭 ⊔ Ideal.span (Set.range L) := by
    have hmap : (Ideal.span (Set.range L)).map mkB.toRingHom = Ifull := by
      rw [Ideal.map_span, ← Set.range_comp]; rfl
    rw [← hmap] at hN
    have hcom : ((Ideal.span (Set.range L)).map mkB.toRingHom).comap mkB.toRingHom =
        Ideal.span (Set.range L) ⊔ 𝔭 := by
      rw [Ideal.comap_map_of_surjective mkB.toRingHom hmkB_surj]
      congr 1
      ext p
      exact Ideal.Quotient.eq_zero_iff_mem
    have hm' : (X s : MvPolynomial σ ℂ) ^ N ∈
        ((Ideal.span (Set.range L)).map mkB.toRingHom).comap mkB.toRingHom := by
      rw [Ideal.mem_comap, map_pow]
      exact hN
    rw [hcom, sup_comm] at hm'
    exact hm'
  have h0 : aeval ω ((X s : MvPolynomial σ ℂ) ^ N) = 0 := by
    rw [Submodule.mem_sup] at hXN
    obtain ⟨p0, hp0, q1, hq1, heq⟩ := hXN
    rw [← heq, map_add, hωp p0 hp0, zero_add]
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hq1
    rw [← hc, map_sum]
    exact Finset.sum_eq_zero fun h _ => by rw [map_mul, hωL h, mul_zero]
  rw [map_pow, aeval_X] at h0
  by_contra hne
  exact pow_ne_zero N hne h0

set_option maxHeartbeats 600000 in
private lemma stage3_comp_bound {σ : Type} [Fintype σ] [DecidableEq σ] {d n k : ℕ}
    (Φ : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ)
    (hΦ_deg : ∀ P, (Φ P).totalDegree ≤ n * P.totalDegree)
    (h𝔭_hom : ∀ P ∈ RingHom.ker Φ.toRingHom, ∀ m, homogeneousComponent m P ∈ RingHom.ker Φ.toRingHom)
    (htrdeg : Algebra.trdeg ℂ Φ.range = (d : Cardinal))
    (hk : k < d) (L : Fin k → MvPolynomial σ ℂ) (hL : ∀ i : Fin k, (L i).IsHomogeneous 1)
    (hLht : ∀ Q ∈ (Ideal.span (Set.range fun i : Fin k =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (L i))).minimalPrimes, (k : ℕ∞) ≤ Q.height) :
    (Ideal.span (Set.range fun i : Fin k =>
      Ideal.Quotient.mk (RingHom.ker Φ.toRingHom) (L i))).minimalPrimes.ncard ≤ n ^ d := by
  classical
  let 𝔭 : Ideal (MvPolynomial σ ℂ) := RingHom.ker Φ.toRingHom
  haveI : 𝔭.IsPrime := RingHom.ker_isPrime Φ.toRingHom
  let Bq := MvPolynomial σ ℂ ⧸ 𝔭
  let mkB : MvPolynomial σ ℂ →ₐ[ℂ] Bq := Ideal.Quotient.mkₐ ℂ 𝔭
  have hmkB_surj : Function.Surjective mkB := Ideal.Quotient.mk_surjective
  let eB : Bq ≃ₐ[ℂ] Φ.range := Ideal.quotientKerEquivRange Φ
  haveI : IsDomain Bq := Ideal.Quotient.isDomain 𝔭
  haveI : IsNoetherianRing Bq := Ideal.Quotient.isNoetherianRing 𝔭
  let mB : Ideal Bq := Ideal.span (Set.range fun s : σ => Ideal.Quotient.mk 𝔭 (X s))
  have hmB_height : mB.height = (d : ℕ∞) := (quot_mB_height Φ h𝔭_hom htrdeg).2
  have hB1_avoid : ∀ (Sfin : Finset (Ideal Bq)), (∀ Q ∈ Sfin, Q < mB) →
      ∃ L1 : MvPolynomial σ ℂ, L1.IsHomogeneous 1 ∧ ∀ Q ∈ Sfin, mkB L1 ∉ Q := by
    intro Sfin hSfin
    let R1 : Submodule ℂ (MvPolynomial σ ℂ) := Submodule.span ℂ (Set.range (X : σ → MvPolynomial σ ℂ))
    have hR1_hom : ∀ f ∈ R1, f.IsHomogeneous 1 := by
      intro f hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        rcases hx with ⟨s, rfl⟩
        exact isHomogeneous_X ℂ s
      | zero => exact isHomogeneous_zero σ ℂ 1
      | add x y _ _ hx hy => exact hx.add hy
      | smul c x _ hx =>
        rw [smul_eq_C_mul]
        simpa using (isHomogeneous_C σ c).mul hx
    let subQ : Sfin → Submodule ℂ R1 := fun Q =>
      (Q.1.restrictScalars ℂ).comap (mkB.toLinearMap.comp R1.subtype)
    have hsubQ_ne_top : ∀ Q : Sfin, subQ Q ≠ ⊤ := by
      intro Q htop
      have hmB_le : mB ≤ Q.1 := by
        rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        have hmem : (⟨X s, Submodule.subset_span ⟨s, rfl⟩⟩ : R1) ∈ subQ Q := by
          rw [htop]; trivial
        exact hmem
      exact not_le_of_gt (hSfin Q.1 Q.2) hmB_le
    obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top subQ hsubQ_ne_top
    refine ⟨v.1, hR1_hom v.1 v.2, fun Q hQ hmem => hv ⟨Q, hQ⟩ hmem⟩
  have hext : ∀ (j : ℕ) (hkj : k ≤ j), j ≤ d →
      ∃ (Hext : Fin j → MvPolynomial σ ℂ),
        (∀ i : Fin k, Hext ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkj⟩ = L i) ∧
        (∀ r : Fin j, (Hext r).IsHomogeneous 1) ∧
        (∀ Q ∈ (Ideal.span (Set.range fun r => Ideal.Quotient.mk 𝔭 (Hext r))).minimalPrimes,
          (j : ℕ∞) ≤ Q.height) := by
    intro j hkj hjd
    induction j with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      exact ⟨L, fun i => Fin.elim0 i, hL, hLht⟩
    | succ j ih =>
      by_cases hkeq : k = j + 1
      · subst hkeq
        exact ⟨L, fun i => rfl, hL, hLht⟩
      · obtain ⟨Hprev, hHprev_eq, hHprev_hom, hHprev_ht⟩ := ih (by omega) (by omega)
        let Iprev : Ideal Bq := Ideal.span (Set.range fun r : Fin j => Ideal.Quotient.mk 𝔭 (Hprev r))
        have hfin : Iprev.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing Bq Iprev
        have hlt_mB : ∀ Q ∈ hfin.toFinset, Q < mB := by
          intro Q hQ
          rw [Set.Finite.mem_toFinset] at hQ
          have hle_mB : Q ≤ mB := quot_minPrime_le_mB Φ h𝔭_hom Hprev hHprev_hom Q hQ
          have hQht : Q.height ≤ (j : ℕ∞) := by
            have hspan_eq : Iprev =
                Ideal.span ((Finset.univ.image fun r : Fin j => Ideal.Quotient.mk 𝔭 (Hprev r)) : Set Bq) := by
              simp [Iprev]
            rw [hspan_eq] at hQ
            have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQ
            have h2 : (Finset.univ.image fun r : Fin j => Ideal.Quotient.mk 𝔭 (Hprev r)).card ≤ j :=
              Finset.card_image_le.trans (by simp)
            exact h1.trans (by exact_mod_cast h2)
          refine lt_of_le_of_ne hle_mB fun heq => ?_
          rw [heq, hmB_height] at hQht
          have : d ≤ j := by exact_mod_cast hQht
          omega
        obtain ⟨Lnext, hLnext_hom, hLnext_avoid⟩ := hB1_avoid hfin.toFinset hlt_mB
        let Hcur : Fin (j + 1) → MvPolynomial σ ℂ := Fin.snoc Hprev Lnext
        refine ⟨Hcur, ?_, ?_, ?_⟩
        · intro i
          dsimp only [Hcur]
          have hi : i.val < j := by omega
          have : (⟨i.val, by omega⟩ : Fin (j + 1)) = Fin.castSucc ⟨i.val, hi⟩ := rfl
          rw [this, Fin.snoc_castSucc]
          exact hHprev_eq i
        · intro r
          refine Fin.lastCases ?_ (fun r' => ?_) r
          · simpa [Hcur] using hLnext_hom
          · simpa [Hcur] using hHprev_hom r'
        · intro P hP
          haveI : P.IsPrime := hP.isPrime
          have hIprev_le : Iprev ≤ P := by
            rw [Ideal.span_le]
            rintro _ ⟨r, rfl⟩
            exact hP.le (Ideal.subset_span ⟨r.castSucc, by simp [Hcur]⟩)
          obtain ⟨Q, hQmin, hQleP⟩ := Ideal.exists_minimalPrimes_le hIprev_le
          haveI : Q.IsPrime := hQmin.isPrime
          have hLmem : mkB Lnext ∈ P :=
            hP.le (Ideal.subset_span ⟨Fin.last j, by simp [Hcur]; rfl⟩)
          have hLnotQ : mkB Lnext ∉ Q := hLnext_avoid Q (hfin.mem_toFinset.mpr hQmin)
          have hQltP : Q < P := lt_of_le_of_ne hQleP fun heq => hLnotQ (heq ▸ hLmem)
          have hQge := hHprev_ht Q hQmin
          calc ((j + 1 : ℕ) : ℕ∞) = (j : ℕ∞) + 1 := by push_cast; rfl
            _ ≤ Q.height + 1 := by gcongr
            _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hQltP
  obtain ⟨Hfull, hHfull_eq, hHfull_hom, hHfull_ht⟩ := hext d hk.le le_rfl
  have hHfull_zero := quot_zeroLocus_eq_zero Φ h𝔭_hom htrdeg Hfull hHfull_hom hHfull_ht
  obtain ⟨hH_indep, hH_int_range, hH_fiber⟩ :=
    stage2_fiber_bound Φ hΦ_deg h𝔭_hom htrdeg Hfull hHfull_hom hHfull_zero
  let gH : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Bq := MvPolynomial.aeval fun r => mkB (Hfull r)
  have hgH_eq : eB.toAlgHom.comp gH =
      MvPolynomial.aeval (fun r : Fin d => Φ.rangeRestrict (Hfull r)) := by
    apply MvPolynomial.algHom_ext
    intro r
    simp only [AlgHom.comp_apply, gH, aeval_X]
    rfl
  have hgH_inj : Function.Injective gH := by
    intro p1 p2 hEq
    have h1 := congrArg eB hEq
    change (eB.toAlgHom.comp gH) p1 = (eB.toAlgHom.comp gH) p2 at h1
    rw [hgH_eq] at h1
    exact hH_indep h1
  have hgH_int : gH.IsIntegral := by
    intro b
    obtain ⟨f, hf_mon, hf_ev⟩ := hH_int_range (eB b)
    refine ⟨f, hf_mon, ?_⟩
    apply eB.injective
    change eB.toRingHom (Polynomial.eval₂ gH.toRingHom b f) = eB.toRingHom 0
    rw [map_zero, ← hf_ev, Polynomial.hom_eval₂]
    congr 1
    apply RingHom.ext
    intro p
    exact AlgHom.congr_fun hgH_eq p
  letI : Algebra (MvPolynomial (Fin d) ℂ) Bq := gH.toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) Bq :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hgH_inj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) Bq := ⟨hgH_int⟩
  haveI : IsIntegrallyClosed (MvPolynomial (Fin d) ℂ) := inferInstance
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin d) ℂ) Bq := inferInstance
  let Ik : Ideal Bq := Ideal.span (Set.range fun i : Fin k => Ideal.Quotient.mk 𝔭 (L i))
  have hSk_fin : Ik.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing Bq Ik
  let Sk := hSk_fin.toFinset
  let pk : Ideal (MvPolynomial (Fin d) ℂ) := chainIdeal d k
  haveI : pk.IsPrime := chainIdeal_isPrime d k
  have hunder_eq : ∀ Q ∈ Sk, Q.under (MvPolynomial (Fin d) ℂ) = pk := by
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    haveI : Q.IsPrime := hQ.isPrime
    haveI : Q.LiesOver (Q.under (MvPolynomial (Fin d) ℂ)) := ⟨rfl⟩
    have hpk_le : pk ≤ Q.under (MvPolynomial (Fin d) ℂ) := by
      dsimp only [pk]
      rw [chainIdeal, Ideal.span_le]
      rintro _ ⟨r, hr, rfl⟩
      change gH (X r) ∈ Q
      simp only [gH, aeval_X]
      have hr' : r = ⟨(⟨r.val, hr⟩ : Fin k).val, by omega⟩ := rfl
      rw [hr', hHfull_eq ⟨r.val, hr⟩]
      exact hQ.le (Ideal.subset_span ⟨⟨r.val, hr⟩, rfl⟩)
    have hQht : Q.height ≤ (k : ℕ∞) := by
      have hsp : Ik =
          Ideal.span ((Finset.univ.image fun i : Fin k => Ideal.Quotient.mk 𝔭 (L i)) : Set Bq) := by
        simp [Ik]
      rw [hsp] at hQ
      have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQ
      have h2 : (Finset.univ.image fun i : Fin k => Ideal.Quotient.mk 𝔭 (L i)).card ≤ k :=
        Finset.card_image_le.trans (by simp)
      exact h1.trans (by exact_mod_cast h2)
    have hunder_le : (Q.under (MvPolynomial (Fin d) ℂ)).height ≤ (k : ℕ∞) := by
      have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
        (Q.under (MvPolynomial (Fin d) ℂ)) Q
      have h1 : (Q.under (MvPolynomial (Fin d) ℂ)).height ≤ Q.height := by rw [hgd]; exact le_self_add
      exact h1.trans hQht
    have hpk_ge : (k : ℕ∞) ≤ pk.height := le_height_chainIdeal d k hk.le
    have : pk.FiniteHeight := ⟨Or.inr (ne_top_of_le_ne_top
      (ENat.coe_ne_top k) ((Ideal.height_mono hpk_le).trans hunder_le))⟩
    exact (eq_of_le_of_not_lt hpk_le fun hlt =>
      not_le.mpr (Ideal.height_strict_mono_of_isPrime hlt) (hunder_le.trans hpk_ge)).symm
  let pairs := (Sk ×ˢ Sk).filter fun p => p.1 ≠ p.2
  have hpair_sep : ∀ p : Ideal Bq × Ideal Bq,
      ∃ f : MvPolynomial (Fin d) ℂ, p ∈ pairs → f ∈ (p.1 ⊔ p.2).under (MvPolynomial (Fin d) ℂ) ∧ f ∉ pk := by
    intro p
    by_cases hp : p ∈ pairs
    · have hp1 : p.1 ∈ Sk := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
      have hp2 : p.2 ∈ Sk := (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
      have hne : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
      have hp1m : p.1 ∈ Ik.minimalPrimes := hSk_fin.mem_toFinset.mp hp1
      have hp2m : p.2 ∈ Ik.minimalPrimes := hSk_fin.mem_toFinset.mp hp2
      haveI : p.1.IsPrime := hp1m.isPrime
      have hlt : p.1 < p.1 ⊔ p.2 := by
        refine lt_of_le_of_ne le_sup_left fun heq => hne ?_
        have h21 : p.2 ≤ p.1 := le_sup_right.trans heq.symm.le
        exact le_antisymm (hp1m.2 ⟨hp2m.isPrime, hp2m.le⟩ h21) h21
      have hlt_u : p.1.under (MvPolynomial (Fin d) ℂ) < (p.1 ⊔ p.2).under (MvPolynomial (Fin d) ℂ) :=
        Ideal.IsIntegral.under_lt_under hlt
      rw [hunder_eq p.1 hp1] at hlt_u
      have hex : ∃ f, f ∈ (p.1 ⊔ p.2).under (MvPolynomial (Fin d) ℂ) ∧ f ∉ pk := by
        by_contra hall
        push Not at hall
        exact not_le_of_gt hlt_u fun f hf => hall f hf
      obtain ⟨f, hf1, hf2⟩ := hex
      exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose fSep hfSep using hpair_sep
  let projK : MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin (d - k)) ℂ :=
    MvPolynomial.aeval fun r : Fin d =>
      if hr : r.val < k then 0 else X ⟨r.val - k, by omega⟩
  have hprojK_ne : ∀ f : MvPolynomial (Fin d) ℂ, f ∉ pk → projK f ≠ 0 := by
    intro f hf
    dsimp only [pk] at hf
    rw [chainIdeal, mem_ideal_span_X_image] at hf
    push Not at hf
    obtain ⟨s, hs_supp, hs_zero⟩ := hf
    let s' : Fin (d - k) →₀ ℕ :=
      Finsupp.equivFunOnFinite.symm fun j : Fin (d - k) => s ⟨k + j.val, by omega⟩
    intro h0
    have hcoeff := congrArg (fun p : MvPolynomial (Fin (d - k)) ℂ => p.coeff s') h0
    change (projK f).coeff s' = 0 at hcoeff
    have hproj_mon : ∀ (t : Fin d →₀ ℕ) (c : ℂ),
        projK (monomial t c) =
          if ∀ r : Fin d, r.val < k → t r = 0 then
            monomial (Finsupp.equivFunOnFinite.symm fun j : Fin (d - k) => t ⟨k + j.val, by omega⟩) c
          else 0 := by
      intro t c
      rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
      have hprojC : projK (C c) = C c := by
        dsimp only [projK]
        rw [aeval_C, MvPolynomial.algebraMap_eq]
      rw [hprojC]
      split_ifs with ht
      · rw [monomial_eq]
        congr 1
        rw [Finset.prod_subset (Finset.subset_univ _) fun r _ hr => by
          rw [Finsupp.notMem_support_iff] at hr; simp [hr]]
        conv_rhs =>
          rw [Finsupp.prod, Finset.prod_subset (Finset.subset_univ _) fun j _ hj => by
            rw [Finsupp.notMem_support_iff] at hj; simp [hj]]
        have hlow : ∀ r : Fin d, r.val < k → projK (X r ^ t r) = 1 := fun r hr => by
          rw [ht r hr, pow_zero, map_one]
        let eSub : Fin (d - k) ↪ Fin d := ⟨fun j => ⟨k + j.val, by omega⟩, fun j1 j2 h =>
          Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)⟩
        have hsplit : (Finset.univ : Finset (Fin d)) =
            (Finset.univ.map eSub) ∪ (Finset.univ.filter fun r : Fin d => r.val < k) := by
          ext r
          simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
            true_and, true_iff]
          by_cases hr : r.val < k
          · exact Or.inr hr
          · refine Or.inl ⟨⟨r.val - k, by omega⟩, Fin.ext ?_⟩
            change k + (r.val - k) = r.val
            omega
        have hdisj : Disjoint (Finset.univ.map eSub)
            (Finset.univ.filter fun r : Fin d => r.val < k) := by
          rw [Finset.disjoint_left]
          intro r hr1 hr2
          rcases Finset.mem_map.mp hr1 with ⟨j, _, rfl⟩
          have hlt := (Finset.mem_filter.mp hr2).2
          change k + j.val < k at hlt
          omega
        rw [hsplit, Finset.prod_union hdisj,
          Finset.prod_eq_one (fun r hr => hlow r (Finset.mem_filter.mp hr).2), mul_one,
          Finset.prod_map]
        refine Finset.prod_congr rfl fun j _ => ?_
        have hge : ¬ (eSub j).val < k := by
          change ¬ k + j.val < k
          omega
        simp only [map_pow, projK, aeval_X, hge, ↓reduceDIte,
          Finsupp.coe_equivFunOnFinite_symm]
        congr 2
        ext
        change (k + j.val) - k = j.val
        omega
      · push Not at ht
        obtain ⟨r0, hr0, ht0⟩ := ht
        have hr0_supp : r0 ∈ t.support := Finsupp.mem_support_iff.mpr ht0
        rw [Finset.prod_eq_zero hr0_supp, mul_zero]
        simp [projK, hr0, zero_pow ht0]
    have hcalc : (projK f).coeff s' = f.coeff s := by
      conv_lhs => rw [f.as_sum]
      rw [map_sum, coeff_sum]
      rw [Finset.sum_eq_single s]
      · rw [hproj_mon]
        have hs0 : ∀ r : Fin d, r.val < k → s r = 0 := fun r hr => hs_zero r hr
        rw [if_pos hs0, coeff_monomial, if_pos rfl]
      · intro t _ hts
        rw [hproj_mon]
        split_ifs with ht
        · rw [coeff_monomial, if_neg]
          intro heq
          apply hts
          ext r
          by_cases hr : r.val < k
          · rw [ht r hr, hs_zero r hr]
          · have h1 := congrFun (congrArg DFunLike.coe heq) ⟨r.val - k, by omega⟩
            simp only [s', Finsupp.coe_equivFunOnFinite_symm] at h1
            have hrlt := r.isLt
            have hr_eq : (⟨k + (r.val - k), by omega⟩ : Fin d) = r := Fin.ext (by dsimp only; omega)
            rwa [hr_eq] at h1
        · exact rfl
      · intro hns; exact absurd hs_supp hns
    rw [hcalc] at hcoeff
    exact (mem_support_iff.mp hs_supp) hcoeff
  let G : MvPolynomial (Fin (d - k)) ℂ := ∏ p ∈ pairs, projK (fSep p)
  have hG_ne : G ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => hprojK_ne (fSep p) (hfSep p hp).2
  have hz_ex : ∃ z : Fin (d - k) → ℂ, eval z G ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hG_ne (MvPolynomial.funext fun z => by rw [hall z, map_zero])
  obtain ⟨z, hz⟩ := hz_ex
  let y : Fin d → ℂ := fun r => if hr : r.val < k then 0 else z ⟨r.val - k, by omega⟩
  have heval_y_proj : ∀ f : MvPolynomial (Fin d) ℂ, eval y f = eval z (projK f) := by
    intro f
    have hcomp : (aeval z).comp projK = aeval y := by
      apply MvPolynomial.algHom_ext
      intro r
      simp only [AlgHom.comp_apply, projK, aeval_X, y]
      split_ifs <;> simp
    simpa [aeval_eq_eval] using (AlgHom.congr_fun hcomp f).symm
  have hfSep_nz : ∀ p ∈ pairs, eval y (fSep p) ≠ 0 := by
    intro p hp h0
    apply hz
    rw [map_prod]
    refine Finset.prod_eq_zero hp ?_
    rwa [← heval_y_proj]
  let qy : Ideal (MvPolynomial (Fin d) ℂ) := RingHom.ker (MvPolynomial.eval y)
  haveI hqy_max : qy.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, by simp⟩
  have hpk_le_qy : pk ≤ qy := by
    dsimp only [pk]
    rw [chainIdeal, Ideal.span_le]
    rintro _ ⟨r, hr, rfl⟩
    change r.val < k at hr
    simp [qy, y, hr]
  have hlift : ∀ Q : Ideal Bq, Q ∈ Sk →
      ∃ ω : σ → ℂ, (ω ∈ zeroLocus ℂ 𝔭 ∧ ∀ r : Fin d, aeval ω (Hfull r) = y r) ∧
        ∃ M : Ideal Bq, Q ≤ M ∧ M.under (MvPolynomial (Fin d) ℂ) = qy ∧
          M.comap mkB.toRingHom = vanishingIdeal ℂ {ω} := by
    intro Q hQ
    haveI : Q.IsPrime := (hSk_fin.mem_toFinset.mp hQ).isPrime
    have hQle : Q.under (MvPolynomial (Fin d) ℂ) ≤ qy := (hunder_eq Q hQ).symm ▸ hpk_le_qy
    obtain ⟨M, hQM, hMprime, hMu⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime qy Q hQle
    haveI := hMprime
    haveI hMmax : M.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under M (hMu.symm ▸ hqy_max)
    let MR : Ideal (MvPolynomial σ ℂ) := M.comap mkB.toRingHom
    have hMR_max : MR.IsMaximal := by
      rw [Ideal.isMaximal_iff]
      refine ⟨fun h1 => hMmax.ne_top (by rw [Ideal.eq_top_iff_one]; simpa [MR] using h1),
        fun J x hMRJ hx hJ => ?_⟩
      have hMlt : M < J.map mkB.toRingHom := lt_of_le_of_ne
        (fun b hb => by obtain ⟨p, rfl⟩ := hmkB_surj b; exact Ideal.mem_map_of_mem _ (hMRJ hb))
        (fun heq => hx (by change mkB x ∈ M; rw [heq]; exact Ideal.mem_map_of_mem _ hJ))
      have hJtop : J.map mkB.toRingHom = ⊤ := by
        by_contra hnt
        exact hMlt.ne (hMmax.eq_of_le hnt hMlt.le)
      have h1map : (1 : Bq) ∈ J.map mkB.toRingHom := by rw [hJtop]; trivial
      have h1com : (1 : MvPolynomial σ ℂ) ∈ (J.map mkB.toRingHom).comap mkB.toRingHom := by
        simpa [Ideal.mem_comap] using h1map
      have hkerJ : RingHom.ker mkB.toRingHom ≤ J := fun p hp =>
        hMRJ (by change mkB p ∈ M; rw [show mkB p = 0 from hp]; exact M.zero_mem)
      rw [Ideal.comap_map_of_surjective mkB.toRingHom hmkB_surj,
        sup_eq_left.mpr (by rw [← RingHom.ker_eq_comap_bot]; exact hkerJ)] at h1com
      exact h1com
    obtain ⟨ω, hω⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hMR_max
    refine ⟨ω, ⟨?_, ?_⟩, M, hQM, hMu, hω⟩
    · intro p hp
      have hpMR : p ∈ MR := by
        change mkB p ∈ M
        rw [show mkB p = 0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hp]
        exact M.zero_mem
      rw [hω, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hpMR
      exact hpMR
    · intro r
      have hXr : (X r - C (y r) : MvPolynomial (Fin d) ℂ) ∈ qy := by simp [qy]
      rw [← hMu] at hXr
      have hHr : Hfull r - C (y r) ∈ MR := by
        change mkB (Hfull r - C (y r)) ∈ M
        have h1 : gH (X r - C (y r)) = mkB (Hfull r - C (y r)) := by
          dsimp only [gH]
          rw [map_sub, map_sub, aeval_X, aeval_C, ← MvPolynomial.algebraMap_eq, mkB.commutes]
        rw [← h1]
        exact hXr
      rw [hω, MvPolynomial.mem_vanishingIdeal_singleton_iff, map_sub, aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at hHr
      exact hHr
  choose ωLift hωLift_fib MLift hMLift using fun Q : Sk => hlift Q.1 Q.2
  have hω_inj : Function.Injective ωLift := by
    intro Q1 Q2 hEq
    by_contra hne
    have hne1 : Q1.1 ≠ Q2.1 := fun h => hne (Subtype.ext h)
    have hMcom : (MLift Q1).comap mkB.toRingHom = (MLift Q2).comap mkB.toRingHom := by
      rw [(hMLift Q1).2.2, (hMLift Q2).2.2, hEq]
    have hMeq : MLift Q1 = MLift Q2 := by
      ext b
      obtain ⟨p, rfl⟩ := hmkB_surj b
      exact Ideal.ext_iff.mp hMcom p
    have hsup_le : Q1.1 ⊔ Q2.1 ≤ MLift Q1 := sup_le (hMLift Q1).1 (hMeq ▸ (hMLift Q2).1)
    have hpair_mem : (Q1.1, Q2.1) ∈ pairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Q1.2, Q2.2⟩, hne1⟩
    have hf_in : fSep (Q1.1, Q2.1) ∈ (Q1.1 ⊔ Q2.1).under (MvPolynomial (Fin d) ℂ) :=
      (hfSep _ hpair_mem).1
    have hf_qy : fSep (Q1.1, Q2.1) ∈ qy := by
      rw [← (hMLift Q1).2.1]
      exact hsup_le hf_in
    exact hfSep_nz _ hpair_mem hf_qy
  let Tfib : Finset (σ → ℂ) := Finset.univ.image ωLift
  have hTfib_card : Tfib.card = Sk.card := by
    rw [Finset.card_image_of_injective _ hω_inj, Finset.card_univ, Fintype.card_coe]
  have hTfib_le : Tfib.card ≤ n ^ d := by
    refine hH_fiber y Tfib fun ω hω => ?_
    rcases Finset.mem_image.mp hω with ⟨Q, _, rfl⟩
    exact hωLift_fib Q
  rw [Set.ncard_eq_toFinset_card _ hSk_fin]
  exact hTfib_card ▸ hTfib_le

set_option maxHeartbeats 600000 in
private lemma main_1091 (n q : ℕ) (H : Fin n → Fin n → Bool) (ζ : ℂ)
    (hn : 0 < n) (hζ : IsPrimitiveRoot ζ q) :
    let I := Fin n
    let E := I × I
    let V := Submodule.span ℚ {v : E → ℚ | ∃ σ : Equiv.Perm I, (∀ j, H (σ j) j = true) ∧
      v = fun e => if σ e.2 = e.1 then (1 : ℚ) else 0}
    let d := Module.finrank ℚ V
    let W := Equiv.Perm I → ℂ
    let S := E → Fin q
    let fits := fun (A : Matrix I I ℂ) => ∀ i j, H i j = false → A i j = 0
    let w := fun (A : Matrix I I ℂ) (π : Equiv.Perm I) => ∏ j : I, A (π j) j
    let evalM := fun (s : S) (A : Matrix I I ℂ) =>
      Matrix.det (fun i j => A i j * ζ ^ (s (i, j)).val : Matrix I I ℂ)
    n * n ^ d < q →
    ∃ (front : Fin d → S) (candidates : (Fin d → ℂ) → Finset W),
      (∀ y, (candidates y).card ≤ n ^ d) ∧
      ∀ A : Matrix I I ℂ, fits A → w A ∈ candidates (fun h => evalM (front h) A) := by
  classical
  intro I E V d W S fits w evalM hq_bound
  let Live : Finset (Equiv.Perm I) :=
    Finset.univ.filter fun σ => ∀ j : I, H (σ j) j = true
  by_cases hLive_empty : Live = ∅
  · have hVbot : V = ⊥ := by
      have hset : {v : E → ℚ | ∃ σ : Equiv.Perm I, (∀ j, H (σ j) j = true) ∧
          v = fun e => if σ e.2 = e.1 then (1 : ℚ) else 0} = ∅ := by
        ext v
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
        intro σ hσ
        have hm : σ ∈ Live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ.1⟩
        rw [hLive_empty] at hm
        exact Finset.notMem_empty _ hm
      dsimp only [V]
      rw [hset, Submodule.span_empty]
    have hd0 : d = 0 := by
      dsimp only [d]
      rw [hVbot, finrank_bot]
    refine ⟨fun h => False.elim (by have := h.isLt; omega), fun _ => {(0 : W)}, ?_, ?_⟩
    · intro y
      simp [hd0]
    · intro A hA
      rw [Finset.mem_singleton]
      funext π
      have hnot : ¬ ∀ j : I, H (π j) j = true := by
        intro hall
        have hm : π ∈ Live := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩
        rw [hLive_empty] at hm
        exact Finset.notMem_empty _ hm
      push Not at hnot
      obtain ⟨j0, hj0⟩ := hnot
      exact Finset.prod_eq_zero (Finset.mem_univ j0) (hA (π j0) j0 (Bool.eq_false_iff.mpr hj0))
  have hLive_ne : Live.Nonempty := Finset.nonempty_iff_ne_empty.mpr hLive_empty
  haveI : Nonempty E := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  let vQ : Equiv.Perm I → E → ℚ := fun σ e => if σ e.2 = e.1 then 1 else 0
  let vN : Equiv.Perm I → E → ℕ := fun σ e => if σ e.2 = e.1 then 1 else 0
  have hvN_cast : ∀ σ e, (vN σ e : ℚ) = vQ σ e := fun σ e => by
    dsimp only [vN, vQ]; split_ifs <;> simp
  have hvN_sum : ∀ σ : Equiv.Perm I, ∑ e : E, vN σ e = n := by
    intro σ
    rw [Fintype.sum_prod_type_right]
    have hcol : ∀ j : I, ∑ i : I, vN σ (i, j) = 1 := by
      intro j
      rw [Finset.sum_eq_single (σ j)]
      · simp [vN]
      · intro i _ hne; simp [vN, hne.symm]
      · intro h; exact (h (Finset.mem_univ _)).elim
    simp [hcol, I]
  have hq_pos : 0 < q := by
    have : 1 ≤ n * n ^ d := Nat.mul_pos hn (Nat.pos_of_ne_zero (pow_ne_zero d hn.ne'))
    omega
  let coordProj : E → (V →ₗ[ℚ] ℚ) := fun e =>
    { toFun := fun u => u.1 e
      map_add' := fun u1 u2 => rfl
      map_smul' := fun c u => rfl }
  have hcoord_sep : ∀ u : V, (∀ e : E, coordProj e u = 0) → u = 0 := by
    intro u hu
    apply Subtype.ext
    funext e
    exact hu e
  have htop_rk : Module.finrank ℚ (⊤ : Submodule ℚ V) ≤ d := by
    rw [finrank_top]
  obtain ⟨chart, hchart⟩ := exists_separating_fin_rat coordProj hcoord_sep d ⊤ htop_rk
  let projMap : V →ₗ[ℚ] (Fin d → ℚ) :=
    { toFun := fun u r => u.1 (chart r)
      map_add' := fun u1 u2 => rfl
      map_smul' := fun c u => rfl }
  have hproj_inj : Function.Injective projMap := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    exact hchart u Submodule.mem_top fun r => congrFun hu r
  have hproj_bij : Function.Bijective projMap := by
    refine ⟨hproj_inj, ?_⟩
    have hfr : Module.finrank ℚ V = Module.finrank ℚ (Fin d → ℚ) := by
      simp [d]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hproj_inj
  let projEquiv : V ≃ₗ[ℚ] (Fin d → ℚ) := LinearEquiv.ofBijective projMap hproj_bij
  let uBasis : Fin d → V := fun r => projEquiv.symm (Pi.single r 1)
  have huBasis_chart : ∀ r s : Fin d, (uBasis r).1 (chart s) = if s = r then 1 else 0 := by
    intro r s
    have h1 : projEquiv (uBasis r) = Pi.single r 1 := projEquiv.apply_symm_apply _
    have h2 := congrFun h1 s
    simpa [projEquiv, projMap, Pi.single_apply] using h2
  have hchart_inj : Function.Injective chart := by
    intro r1 r2 hEq
    by_contra hne
    have h1 := huBasis_chart r1 r1
    have h2 := huBasis_chart r1 r2
    rw [hEq] at h1
    split_ifs at h1 with h1eq
    · split_ifs at h2 with h2eq
      · exact hne h2eq.symm
      · rw [h1] at h2
        exact one_ne_zero h2
    · exact h1eq rfl
  have hV_zero_of_H_false : ∀ (u : V) (e : E), H e.1 e.2 = false → u.1 e = 0 := by
    rintro ⟨u, hu⟩ e he
    dsimp only
    induction hu using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨σ, hσ, rfl⟩
      by_cases hhit : σ e.2 = e.1
      · have ht := hσ e.2
        rw [hhit, he] at ht
        cases ht
      · simp [hhit]
    | zero => rfl
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  have hchart_H : ∀ r : Fin d, H (chart r).1 (chart r).2 = true := by
    intro r
    by_contra hnt
    have hf : H (chart r).1 (chart r).2 = false := Bool.eq_false_iff.mpr hnt
    have h0 := hV_zero_of_H_false (uBasis r) (chart r) hf
    have h1 := huBasis_chart r r
    simp [h0] at h1
  let matChart : (Fin d → ℂ) → Matrix I I ℂ := fun t i j =>
    if h : ∃ r : Fin d, chart r = (i, j) then t (Classical.choose h)
    else if H i j then 1 else 0
  have hmatChart_fits : ∀ t, fits (matChart t) := by
    intro t i j hij
    dsimp only [matChart]
    split_ifs with h hH
    · obtain ⟨r, hr⟩ := h
      have hH' := hchart_H r
      rw [hr, hij] at hH'
      cases hH'
    · rw [hij] at hH
      cases hH
    · rfl
  have hmatChart_w : ∀ (t : Fin d → ℂ) (σ : Live),
      w (matChart t) σ.1 = ∏ r : Fin d, (t r) ^ (vN σ.1 (chart r)) := by
    intro t σ
    have hσH : ∀ j, H (σ.1 j) j = true := (Finset.mem_filter.mp σ.2).2
    let fE : E → ℂ := fun e => if σ.1 e.2 = e.1 then matChart t e.1 e.2 else 1
    have hw_eq : w (matChart t) σ.1 = ∏ e : E, fE e := by
      dsimp only [w]
      rw [Fintype.prod_prod_type_right]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Finset.prod_eq_single (σ.1 j)]
      · simp [fE]
      · intro i _ hne; simp [fE, hne.symm]
      · intro h; exact (h (Finset.mem_univ _)).elim
    rw [hw_eq]
    have hsplit : ∏ e : E, fE e =
        (∏ e ∈ Finset.univ.image chart, fE e) *
          (∏ e ∈ Finset.univ \ Finset.univ.image chart, fE e) := by
      have hc : (Finset.univ.image chart)ᶜ = Finset.univ \ Finset.univ.image chart := by
        ext e; simp
      rw [← hc, Finset.prod_mul_prod_compl]
    rw [hsplit]
    have hrest : ∏ e ∈ Finset.univ \ Finset.univ.image chart, fE e = 1 := by
      refine Finset.prod_eq_one fun e he => ?_
      have hnot : ¬ ∃ r : Fin d, chart r = (e.1, e.2) := by
        rintro ⟨r, hr⟩
        exact (Finset.mem_sdiff.mp he).2 (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩)
      dsimp only [fE]
      split_ifs with hhit
      · dsimp only [matChart]
        simp only [hnot, ↓reduceDIte]
        have := hσH e.2
        rw [hhit] at this
        simp [this]
      · rfl
    rw [hrest, mul_one, Finset.prod_image (fun r1 _ r2 _ h => hchart_inj h)]
    refine Finset.prod_congr rfl fun r _ => ?_
    dsimp only [fE, vN]
    split_ifs with hhit
    · dsimp only [matChart]
      have hex : ∃ r' : Fin d, chart r' = ((chart r).1, (chart r).2) := ⟨r, rfl⟩
      simp only [hex, ↓reduceDIte, pow_one]
      have hch : Classical.choose hex = r := hchart_inj (Classical.choose_spec hex)
      rw [hch]
    · simp
  let Φ_alg : MvPolynomial Live ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
    MvPolynomial.aeval fun σ : Live =>
      ∏ r : Fin d, (X r : MvPolynomial (Fin d) ℂ) ^ (vN σ.1 (chart r))
  let 𝔭 : Ideal (MvPolynomial Live ℂ) := RingHom.ker Φ_alg.toRingHom
  haveI h𝔭_prime : 𝔭.IsPrime := RingHom.ker_isPrime Φ_alg.toRingHom
  have hΦ_X_deg : ∀ σ : Live, (Φ_alg (X σ)).totalDegree ≤ n := by
    intro σ
    dsimp only [Φ_alg]
    rw [aeval_X]
    calc (∏ r : Fin d, (X r : MvPolynomial (Fin d) ℂ) ^ (vN σ.1 (chart r))).totalDegree
        ≤ ∑ r : Fin d, ((X r : MvPolynomial (Fin d) ℂ) ^ (vN σ.1 (chart r))).totalDegree :=
          totalDegree_finsetProd _ _
      _ ≤ ∑ r : Fin d, vN σ.1 (chart r) := by
          refine Finset.sum_le_sum fun r _ => ?_
          rw [totalDegree_X_pow]
      _ = ∑ e ∈ Finset.univ.image chart, vN σ.1 e := by
          rw [Finset.sum_image (fun r1 _ r2 _ h => hchart_inj h)]
      _ ≤ ∑ e : E, vN σ.1 e := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = n := hvN_sum σ.1
  have hΦ_deg : ∀ P : MvPolynomial Live ℂ, (Φ_alg P).totalDegree ≤ n * P.totalDegree := by
    intro P
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    refine (totalDegree_finsetSum_le fun s hs => ?_)
    rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
    have hC : Φ_alg (C (P.coeff s)) = C (P.coeff s) := by
      dsimp only [Φ_alg]
      rw [aeval_C, MvPolynomial.algebraMap_eq]
    rw [hC]
    calc (C (P.coeff s) * ∏ σ ∈ s.support, Φ_alg (X σ ^ s σ)).totalDegree
        ≤ (C (P.coeff s)).totalDegree + (∏ σ ∈ s.support, Φ_alg (X σ ^ s σ)).totalDegree :=
          totalDegree_mul _ _
      _ = (∏ σ ∈ s.support, Φ_alg (X σ) ^ s σ).totalDegree := by
          simp [totalDegree_C]
      _ ≤ ∑ σ ∈ s.support, (Φ_alg (X σ) ^ s σ).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ σ ∈ s.support, s σ * (Φ_alg (X σ)).totalDegree :=
          Finset.sum_le_sum fun σ _ => totalDegree_pow _ _
      _ ≤ ∑ σ ∈ s.support, s σ * n :=
          Finset.sum_le_sum fun σ _ => Nat.mul_le_mul_left _ (hΦ_X_deg σ)
      _ = (∑ σ ∈ s.support, s σ) * n := (Finset.sum_mul _ _ _).symm
      _ = n * s.degree := by rw [mul_comm]; rfl
      _ ≤ n * P.totalDegree := Nat.mul_le_mul_left n (le_totalDegree hs)
  have hΦ_eval_matChart : ∀ (t : Fin d → ℂ) (P : MvPolynomial Live ℂ),
      aeval (fun σ : Live => w (matChart t) σ.1) P = eval t (Φ_alg P) := by
    intro t P
    have hcomp : aeval (fun σ : Live => w (matChart t) σ.1) = (aeval t).comp Φ_alg := by
      apply MvPolynomial.algHom_ext
      intro σ
      simp only [aeval_X, AlgHom.comp_apply, Φ_alg, map_prod, map_pow, hmatChart_w]
    rw [AlgHom.congr_fun hcomp P]
    simp [aeval_eq_eval]
  have h_dense_torus : ∀ A : Matrix I I ℂ, fits A →
      (∀ i j, H i j = true → A i j ≠ 0) →
      ∃ t : Fin d → ℂ, ∀ σ : Live, w A σ.1 = w (matChart t) σ.1 := by
    intro A _ hAnz
    let α : E → ℂ := fun e => if H e.1 e.2 then Complex.log (A e.1 e.2) else 0
    let β : Fin d → ℂ := fun r => ∑ e : E, ((uBasis r).1 e : ℂ) * α e
    refine ⟨fun r => Complex.exp (β r), fun σ => ?_⟩
    have hv_mem : vQ σ.1 ∈ V :=
      Submodule.subset_span ⟨σ.1, (Finset.mem_filter.mp σ.2).2, rfl⟩
    have hv_decomp : (⟨vQ σ.1, hv_mem⟩ : V) = ∑ r : Fin d, vQ σ.1 (chart r) • uBasis r := by
      apply projEquiv.injective
      ext s
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single s]
      · have h1 : projEquiv (uBasis s) s = 1 := by
          simpa [projEquiv, projMap] using huBasis_chart s s
        rw [h1, mul_one]
        rfl
      · intro r _ hrs
        have h1 : projEquiv (uBasis r) s = 0 := by
          simpa [projEquiv, projMap, hrs.symm] using huBasis_chart r s
        rw [h1, mul_zero]
      · intro hs; exact (hs (Finset.mem_univ s)).elim
    have hsum_eq : ∑ j : I, α (σ.1 j, j) = ∑ r : Fin d, (vN σ.1 (chart r) : ℂ) * β r := by
      have h1 : ∑ j : I, α (σ.1 j, j) = ∑ e : E, (vQ σ.1 e : ℂ) * α e := by
        rw [Fintype.sum_prod_type_right]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (σ.1 j)]
        · simp [vQ]
        · intro i _ hne; simp [vQ, hne.symm]
        · intro h; exact (h (Finset.mem_univ _)).elim
      rw [h1]
      have h2 : ∀ e : E, (vQ σ.1 e : ℂ) = ∑ r : Fin d, (vN σ.1 (chart r) : ℂ) * ((uBasis r).1 e : ℂ) := by
        intro e
        have he := congrFun (congrArg Subtype.val hv_decomp) e
        simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul] at he
        have heC := congrArg (fun x : ℚ => (x : ℂ)) he
        push_cast at heC
        rw [heC]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← hvN_cast]
        push_cast
        rfl
      simp_rw [h2, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      dsimp only [β]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => by ring
    have hσH : ∀ j : I, H (σ.1 j) j = true := (Finset.mem_filter.mp σ.2).2
    have hwA : w A σ.1 = Complex.exp (∑ j : I, α (σ.1 j, j)) := by
      rw [Complex.exp_sum]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only [α]
      simp only [hσH j, ↓reduceIte, Complex.exp_log (hAnz _ _ (hσH j))]
    rw [hwA, hsum_eq, Complex.exp_sum, hmatChart_w (fun r => Complex.exp (β r)) σ]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [Complex.exp_nat_mul]
  have h_image_locus : ∀ A : Matrix I I ℂ, fits A →
      (fun σ : Live => w A σ.1) ∈ zeroLocus ℂ 𝔭 := by
    intro A hA P hP
    let polyE : I → I → Polynomial ℂ := fun i j =>
      if H i j = false then 0
      else if A i j = 0 then Polynomial.X
      else Polynomial.C (A i j)
    let Q : Polynomial ℂ :=
      MvPolynomial.aeval (fun σ : Live => ∏ j : I, polyE (σ.1 j) j) P
    have hQ_eval : ∀ z : ℂ,
        Q.eval z = aeval (fun σ : Live => w (fun i j => (polyE i j).eval z) σ.1) P := by
      intro z
      have hcomp : (Polynomial.aeval z).comp
          (MvPolynomial.aeval (fun σ : Live => ∏ j : I, polyE (σ.1 j) j)) =
          MvPolynomial.aeval (fun σ : Live => w (fun i j => (polyE i j).eval z) σ.1) := by
        apply MvPolynomial.algHom_ext
        intro σ
        simp only [AlgHom.comp_apply, aeval_X, map_prod, w]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Polynomial.coe_aeval_eq_eval]
      have h1 := AlgHom.congr_fun hcomp P
      dsimp only [Q]
      rw [← h1, AlgHom.comp_apply, Polynomial.coe_aeval_eq_eval]
    have hQ_zero_nat : ∀ k : ℕ, Q.eval ((k : ℂ) + 1) = 0 := by
      intro k
      let B : Matrix I I ℂ := fun i j => (polyE i j).eval ((k : ℂ) + 1)
      have hB_fits : fits B := fun i j hij => by simp [B, polyE, hij]
      have hB_nz : ∀ i j, H i j = true → B i j ≠ 0 := by
        intro i j hij
        dsimp only [B, polyE]
        rw [hij]
        simp only [Bool.true_eq_false, ↓reduceIte]
        split_ifs with h0
        · simp only [Polynomial.eval_X]
          exact Nat.cast_add_one_ne_zero k
        · simpa using h0
      obtain ⟨t, ht⟩ := h_dense_torus B hB_fits hB_nz
      rw [hQ_eval]
      have hfun : (fun σ : Live => w B σ.1) = (fun σ : Live => w (matChart t) σ.1) :=
        funext ht
      rw [hfun, hΦ_eval_matChart t P]
      have hP0 : Φ_alg P = 0 := hP
      rw [hP0, map_zero]
    have hQ0 : Q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      have hsub : Set.range (fun k : ℕ => (k : ℂ) + 1) ⊆ {z : ℂ | Q.IsRoot z} := by
        rintro _ ⟨k, rfl⟩
        exact hQ_zero_nat k
      refine Set.Infinite.mono hsub (Set.infinite_range_of_injective fun k1 k2 h => ?_)
      have h1 : (k1 : ℂ) = (k2 : ℂ) := add_right_cancel h
      exact Nat.cast_injective h1
    have hQ_at0 : Q.eval 0 = 0 := by rw [hQ0, Polynomial.eval_zero]
    rw [hQ_eval] at hQ_at0
    have hA_eq : (fun i j => (polyE i j).eval 0) = A := by
      ext i j
      dsimp only [polyE]
      cases hH : H i j
      · simp [hA i j hH]
      · simp only [Bool.true_eq_false, ↓reduceIte]
        split_ifs with h0
        · simp [h0]
        · simp
    rwa [hA_eq] at hQ_at0
  have h𝔭_hom : ∀ P ∈ 𝔭, ∀ m, homogeneousComponent m P ∈ 𝔭 := by
    intro P hP m
    change Φ_alg (homogeneousComponent m P) = 0
    apply MvPolynomial.funext
    intro t
    rw [map_zero]
    let Q : Polynomial ℂ :=
      ∑ k ∈ Finset.range (P.totalDegree + 1),
        Polynomial.C (eval t (Φ_alg (homogeneousComponent k P))) * Polynomial.X ^ k
    have hQ_eval : ∀ lam : ℂ, Q.eval lam = 0 := by
      intro lam
      obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq lam hn
      let A := c • matChart t
      have hA_fits : fits A := fun i j hij => by
        simp [A, hmatChart_fits t i j hij]
      have hAw : (fun σ : Live => w A σ.1) = lam • (fun σ : Live => w (matChart t) σ.1) := by
        funext σ
        simp only [Pi.smul_apply, smul_eq_mul, w, A, Matrix.smul_apply]
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hc]
      have hzero := h_image_locus A hA_fits P hP
      rw [hAw] at hzero
      have hdecomp : aeval (lam • (fun σ : Live => w (matChart t) σ.1)) P = Q.eval lam := by
        conv_lhs => rw [← sum_homogeneousComponent P]
        rw [map_sum]
        dsimp only [Q]
        rw [Polynomial.eval_finsetSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [aeval_eq_eval, (homogeneousComponent_isHomogeneous k P).eval_smul,
          ← aeval_eq_eval, hΦ_eval_matChart t, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
      rw [← hdecomp]
      exact hzero
    have hQ0 : Q = 0 := Polynomial.funext fun lam => by rw [hQ_eval lam, Polynomial.eval_zero]
    by_cases hm : m < P.totalDegree + 1
    · have hcoeff := congrArg (fun f : Polynomial ℂ => f.coeff m) hQ0
      simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
        Polynomial.coeff_zero] at hcoeff
      rw [Finset.sum_eq_single m] at hcoeff
      · simpa using hcoeff
      · intro k _ hkm; simp [hkm.symm]
      · intro hnm; exact absurd (Finset.mem_range.mpr hm) hnm
    · rw [homogeneousComponent_eq_zero m P (by omega), map_zero, map_zero]
  have htrdeg_range : Algebra.trdeg ℂ Φ_alg.range = (d : Cardinal) := by
    have hle : Algebra.trdeg ℂ Φ_alg.range ≤ (d : Cardinal) := by
      have h1 := trdeg_le_of_injective Φ_alg.range.val Subtype.val_injective
      rw [MvPolynomial.trdeg_of_isDomain] at h1
      simpa using h1
    have halg_X : ∀ r : Fin d, IsAlgebraic Φ_alg.range (X r : MvPolynomial (Fin d) ℂ) := by
      intro r
      have hu_mem : (uBasis r).1 ∈ Submodule.span ℚ (Set.range fun σ : Live => vQ σ.1) := by
        have hsub : {v : E → ℚ | ∃ σ : Equiv.Perm I, (∀ j, H (σ j) j = true) ∧
            v = fun e => if σ e.2 = e.1 then (1 : ℚ) else 0} ⊆
            Set.range (fun σ : Live => vQ σ.1) := by
          rintro v ⟨σ, hσ, rfl⟩
          exact ⟨⟨σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ⟩⟩, rfl⟩
        exact Submodule.span_mono hsub (uBasis r).2
      obtain ⟨qcoef, hqcoef⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hu_mem
      obtain ⟨M, hMpos, c, hc⟩ := exists_clear_denom_rat qcoef
      let cPos : Live → ℕ := fun σ => (c σ).toNat
      let cNeg : Live → ℕ := fun σ => (-c σ).toNat
      have hc_split : ∀ σ : Live, (c σ : ℤ) = (cPos σ : ℤ) - (cNeg σ : ℤ) := fun σ => by
        dsimp only [cPos, cNeg]
        omega
      have hexp_eq : ∀ s : Fin d,
          (if s = r then M else 0) + ∑ σ : Live, cNeg σ * vN σ.1 (chart s) =
            ∑ σ : Live, cPos σ * vN σ.1 (chart s) := by
        intro s
        have h1 := congrFun hqcoef (chart s)
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
        rw [huBasis_chart r s] at h1
        have h2 : ((if s = r then (1 : ℚ) else 0) * M) =
            ∑ σ : Live, (c σ : ℚ) * vQ σ.1 (chart s) := by
          rw [← h1, Finset.sum_mul]
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [hc σ]
          ring
        have h3 : (if s = r then (M : ℤ) else 0) =
            ∑ σ : Live, c σ * (vN σ.1 (chart s) : ℤ) := by
          apply Int.cast_injective (α := ℚ)
          push_cast
          convert h2 using 1
          · split_ifs <;> simp
          · refine Finset.sum_congr rfl fun σ _ => by rw [hvN_cast]
        have h4 : (((if s = r then M else 0) + ∑ σ : Live, cNeg σ * vN σ.1 (chart s) : ℕ) : ℤ) =
            ((∑ σ : Live, cPos σ * vN σ.1 (chart s) : ℕ) : ℤ) := by
          push_cast
          rw [h3]
          simp_rw [hc_split, sub_mul, Finset.sum_sub_distrib]
          ring
        exact Int.ofNat.inj h4
      let Ppos : MvPolynomial (Fin d) ℂ := ∏ σ : Live, (Φ_alg (X σ)) ^ (cPos σ)
      let Pneg : MvPolynomial (Fin d) ℂ := ∏ σ : Live, (Φ_alg (X σ)) ^ (cNeg σ)
      have hPpos_mem : Ppos ∈ Φ_alg.range :=
        Subalgebra.prod_mem Φ_alg.range fun σ _ =>
          Subalgebra.pow_mem Φ_alg.range (AlgHom.mem_range_self Φ_alg (X σ)) _
      have hPneg_mem : Pneg ∈ Φ_alg.range :=
        Subalgebra.prod_mem Φ_alg.range fun σ _ =>
          Subalgebra.pow_mem Φ_alg.range (AlgHom.mem_range_self Φ_alg (X σ)) _
      have hPneg_ne : Pneg ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun σ _ => pow_ne_zero _ ?_
        dsimp only [Φ_alg]
        rw [aeval_X]
        exact Finset.prod_ne_zero_iff.mpr fun s _ => pow_ne_zero _ (X_ne_zero s)
      have hrel : (X r : MvPolynomial (Fin d) ℂ) ^ M * Pneg = Ppos := by
        have hprod_pos : Ppos = ∏ s : Fin d, (X s : MvPolynomial (Fin d) ℂ) ^
            (∑ σ : Live, cPos σ * vN σ.1 (chart s)) := by
          dsimp only [Ppos, Φ_alg]
          simp only [aeval_X]
          simp_rw [← Finset.prod_pow]
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_congr rfl fun σ _ => by rw [← pow_mul, mul_comm]
        have hprod_neg : Pneg = ∏ s : Fin d, (X s : MvPolynomial (Fin d) ℂ) ^
            (∑ σ : Live, cNeg σ * vN σ.1 (chart s)) := by
          dsimp only [Pneg, Φ_alg]
          simp only [aeval_X]
          simp_rw [← Finset.prod_pow]
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun s _ => ?_
          rw [← Finset.prod_pow_eq_pow_sum]
          refine Finset.prod_congr rfl fun σ _ => by rw [← pow_mul, mul_comm]
        have hXr : (X r : MvPolynomial (Fin d) ℂ) ^ M =
            ∏ s : Fin d, (X s : MvPolynomial (Fin d) ℂ) ^ (if s = r then M else 0) := by
          rw [Finset.prod_eq_single r]
          · simp
          · intro s _ hs; simp [hs]
          · intro h; exact (h (Finset.mem_univ r)).elim
        rw [hXr, hprod_neg, hprod_pos, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [← pow_add, hexp_eq s]
      refine ⟨Polynomial.C ⟨Pneg, hPneg_mem⟩ * Polynomial.X ^ M - Polynomial.C ⟨Ppos, hPpos_mem⟩,
        ?_, ?_⟩
      · intro h0
        have hcM := congrArg (fun f : Polynomial Φ_alg.range => f.coeff M) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C,
          Polynomial.coeff_zero, ↓reduceIte, hMpos.ne', sub_zero] at hcM
        exact hPneg_ne (congrArg Subtype.val hcM)
      · simp only [map_sub, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
        change Pneg * (X r : MvPolynomial (Fin d) ℂ) ^ M - Ppos = 0
        rw [mul_comm, hrel, sub_self]
    exact le_antisymm hle (trdeg_ge_of_alg_X Φ_alg.range halg_X)
  let Bq := MvPolynomial Live ℂ ⧸ 𝔭
  let mkB : MvPolynomial Live ℂ →ₐ[ℂ] Bq := Ideal.Quotient.mkₐ ℂ 𝔭
  haveI : IsNoetherianRing Bq := Ideal.Quotient.isNoetherianRing 𝔭
  let mB : Ideal Bq := Ideal.span (Set.range fun σ : Live => Ideal.Quotient.mk 𝔭 (X σ))
  have hmB_height : mB.height = (d : ℕ∞) := (quot_mB_height Φ_alg h𝔭_hom htrdeg_range).2
  let phaseForm : S → MvPolynomial Live ℂ := fun s =>
    ∑ σ : Live, C (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) * ζ ^ (∑ j : I, (s (σ.1 j, j)).val)) * X σ
  have hphase_hom : ∀ s : S, (phaseForm s).IsHomogeneous 1 := fun s => by
    dsimp only [phaseForm]
    refine Finset.sum_induction _ (fun p : MvPolynomial Live ℂ => p.IsHomogeneous 1)
      (fun _ _ ha hb => ha.add hb) (isHomogeneous_zero Live ℂ 1) fun σ _ => ?_
    simpa using (isHomogeneous_C Live (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) *
      ζ ^ (∑ j : I, (s (σ.1 j, j)).val))).mul (isHomogeneous_X ℂ σ)
  have hevalM_eq : ∀ (s : S) (A : Matrix I I ℂ), fits A →
      evalM s A = aeval (fun σ : Live => w A σ.1) (phaseForm s) := by
    intro s A hA
    let M : Matrix I I ℂ := fun i j => A i j * ζ ^ (s (i, j)).val
    change Matrix.det M = aeval (fun σ : Live => w A σ.1) (phaseForm s)
    dsimp only [phaseForm]
    rw [Matrix.det_apply', map_sum]
    dsimp only [M]
    have hsplit : ∑ σ : Equiv.Perm I,
        (Equiv.Perm.sign σ : ℂ) * ∏ j : I, (A (σ j) j * ζ ^ (s (σ j, j)).val) =
        ∑ σ ∈ Live, (Equiv.Perm.sign σ : ℂ) * ∏ j : I, (A (σ j) j * ζ ^ (s (σ j, j)).val) := by
      rw [← Finset.sum_sdiff (Finset.subset_univ Live)]
      have hz : ∑ σ ∈ Finset.univ \ Live,
          (Equiv.Perm.sign σ : ℂ) * ∏ j : I, (A (σ j) j * ζ ^ (s (σ j, j)).val) = 0 := by
        refine Finset.sum_eq_zero fun σ hσ => ?_
        have hnot : ¬ ∀ j : I, H (σ j) j = true := by
          have := (Finset.mem_sdiff.mp hσ).2
          simpa [Live] using this
        push Not at hnot
        obtain ⟨j0, hj0⟩ := hnot
        have hA0 : A (σ j0) j0 = 0 := hA (σ j0) j0 (Bool.eq_false_iff.mpr hj0)
        rw [Finset.prod_eq_zero (Finset.mem_univ j0) (by rw [hA0, zero_mul]), mul_zero]
      rw [hz, zero_add]
    rw [hsplit, ← Finset.sum_attach Live]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, aeval_X, w,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    ring
  have hSZ_bad : ∀ (ω : Live → ℂ), ω ≠ 0 →
      ((Finset.univ : Finset S).filter fun s => aeval ω (phaseForm s) = 0).card * q ≤
        n * q ^ (n * n) := by
    intro ω hω
    let Fω : MvPolynomial E ℂ :=
      ∑ σ : Live, C (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) * ω σ) * ∏ j : I, X (σ.1 j, j)
    have hFω_ne : Fω ≠ 0 := by
      obtain ⟨σ0, hσ0⟩ := Function.ne_iff.mp hω
      let e0 : E →₀ ℕ := Finsupp.equivFunOnFinite.symm (vN σ0.1)
      intro h0
      have hc := congrArg (fun p : MvPolynomial E ℂ => p.coeff e0) h0
      change Fω.coeff e0 = 0 at hc
      have hterm : ∀ σ : Live,
          (C (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) * ω σ) * ∏ j : I, (X (σ.1 j, j) : MvPolynomial E ℂ)) =
            monomial (Finsupp.equivFunOnFinite.symm (vN σ.1))
              (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) * ω σ) := by
        intro σ
        rw [monomial_eq]
        congr 1
        conv_rhs =>
          rw [Finsupp.prod, Finset.prod_subset (Finset.subset_univ _) fun e _ he => by
            rw [Finsupp.notMem_support_iff] at he; simp [he]]
        rw [Fintype.prod_prod_type_right]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [Finset.prod_eq_single (σ.1 j)]
        · simp [vN, Finsupp.coe_equivFunOnFinite_symm]
        · intro i _ hne; simp [vN, hne.symm, Finsupp.coe_equivFunOnFinite_symm]
        · intro h; exact (h (Finset.mem_univ _)).elim
      simp only [Fω, coeff_sum] at hc
      simp_rw [hterm, coeff_monomial] at hc
      rw [Finset.sum_eq_single σ0] at hc
      · simp only [e0, ↓reduceIte] at hc
        rcases mul_eq_zero.mp hc with hsgn | hω0
        · rcases Int.units_eq_one_or (Equiv.Perm.sign σ0.1) with h1 | h1 <;>
            simp [h1] at hsgn
        · exact hσ0 hω0
      · intro σ _ hne
        rw [if_neg]
        intro hEq
        apply hne
        apply Subtype.ext
        apply Equiv.ext
        intro j
        have h1 := congrFun (congrArg DFunLike.coe hEq) (σ.1 j, j)
        simp only [e0, Finsupp.coe_equivFunOnFinite_symm, vN, ↓reduceIte] at h1
        split_ifs at h1 with hhit
        exact hhit.symm
      · intro h; exact absurd (Finset.mem_univ σ0) h
    have hFω_deg : Fω.totalDegree ≤ n := by
      refine totalDegree_finsetSum_le fun σ _ => ?_
      calc (C (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) * ω σ) * ∏ j : I, (X (σ.1 j, j) : MvPolynomial E ℂ)).totalDegree
          ≤ (C (((Equiv.Perm.sign σ.1 : ℤ) : ℂ) * ω σ)).totalDegree +
              (∏ j : I, (X (σ.1 j, j) : MvPolynomial E ℂ)).totalDegree := totalDegree_mul _ _
        _ ≤ 0 + ∑ j : I, (X (σ.1 j, j) : MvPolynomial E ℂ).totalDegree := by
            rw [totalDegree_C]
            exact Nat.add_le_add_left (totalDegree_finsetProd _ _) 0
        _ = n := by simp [I]
    let eE : E ≃ Fin (n * n) := Fintype.equivFinOfCardEq (by simp [E, I])
    let Ffin : MvPolynomial (Fin (n * n)) ℂ := MvPolynomial.rename eE Fω
    have hFfin_ne : Ffin ≠ 0 :=
      fun h => hFω_ne (MvPolynomial.rename_injective eE eE.injective (by simpa [Ffin] using h))
    have hFfin_deg : Ffin.totalDegree ≤ n := (totalDegree_rename_le eE Fω).trans hFω_deg
    let Zset : Finset ℂ := Finset.univ.image fun k : Fin q => ζ ^ k.val
    have hζ_inj : Function.Injective (fun k : Fin q => ζ ^ k.val) :=
      fun k1 k2 h => Fin.ext (hζ.pow_inj k1.isLt k2.isLt h)
    have hZset_card : Zset.card = q := by
      rw [Finset.card_image_of_injective _ hζ_inj, Finset.card_univ, Fintype.card_fin]
    have hSZ := MvPolynomial.schwartz_zippel_totalDegree hFfin_ne Zset
    rw [hZset_card] at hSZ
    let toGrid : S → (Fin (n * n) → ℂ) := fun s idx => ζ ^ (s (eE.symm idx)).val
    have htoGrid_inj : Function.Injective toGrid := by
      intro s1 s2 hEq
      funext e
      have h1 := congrFun hEq (eE e)
      simp only [toGrid, Equiv.symm_apply_apply] at h1
      exact hζ_inj h1
    have htoGrid_eval : ∀ s : S, eval (toGrid s) Ffin = aeval ω (phaseForm s) := by
      intro s
      dsimp only [Ffin, Fω, phaseForm]
      rw [eval_rename, map_sum, map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [map_mul, eval_C, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, aeval_X,
        map_prod, eval_X, Function.comp_apply, toGrid, Equiv.symm_apply_apply,
        Finset.prod_pow_eq_pow_sum]
      ring
    have hcard_le : ((Finset.univ : Finset S).filter fun s => aeval ω (phaseForm s) = 0).card ≤
        ((Fintype.piFinset fun _ : Fin (n * n) => Zset).filter fun f => eval f Ffin = 0).card := by
      refine Finset.card_le_card_of_injOn toGrid (fun s hs => ?_) (fun s1 _ s2 _ h => htoGrid_inj h)
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset] at hs ⊢
      refine ⟨fun idx => Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
      rw [htoGrid_eval s, hs]
    have hSZ_nn : (((Finset.univ : Finset S).filter fun s => aeval ω (phaseForm s) = 0).card : NNRat) /
        ((q : NNRat) ^ (n * n)) ≤ (n : NNRat) / (q : NNRat) := by
      have h1 : (((Finset.univ : Finset S).filter fun s => aeval ω (phaseForm s) = 0).card : NNRat) /
          ((q : NNRat) ^ (n * n)) ≤
          (((Fintype.piFinset fun _ : Fin (n * n) => Zset).filter fun f => eval f Ffin = 0).card : NNRat) /
            ((q : NNRat) ^ (n * n)) := by
        gcongr
      have h2 : (Ffin.totalDegree : NNRat) / (q : NNRat) ≤ (n : NNRat) / (q : NNRat) := by
        gcongr
      exact h1.trans (hSZ.trans h2)
    have hq_nn : (0 : NNRat) < (q : NNRat) := by exact_mod_cast hq_pos
    have hqpow_nn : (0 : NNRat) < (q : NNRat) ^ (n * n) := pow_pos hq_nn _
    rw [div_le_div_iff₀ hqpow_nn hq_nn] at hSZ_nn
    exact_mod_cast hSZ_nn
  have hfront_ind : ∀ k : ℕ, k ≤ d →
      ∃ frontK : Fin k → S,
        ∀ Q ∈ (Ideal.span (Set.range fun i : Fin k =>
          Ideal.Quotient.mk 𝔭 (phaseForm (frontK i)))).minimalPrimes, (k : ℕ∞) ≤ Q.height := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨Fin.elim0, fun Q _ => by simp⟩
    | succ k ih =>
      obtain ⟨frontPrev, hprev⟩ := ih (by omega)
      let Iprev : Ideal Bq :=
        Ideal.span (Set.range fun i : Fin k => Ideal.Quotient.mk 𝔭 (phaseForm (frontPrev i)))
      have hfin : Iprev.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing Bq Iprev
      let Sk := hfin.toFinset
      have hSk_card : Sk.card ≤ n ^ d := by
        rw [← Set.ncard_eq_toFinset_card _ hfin]
        exact stage3_comp_bound Φ_alg hΦ_deg h𝔭_hom htrdeg_range (by omega)
          (fun i => phaseForm (frontPrev i)) (fun i => hphase_hom _) hprev
      have hex_pt : ∀ Q ∈ Sk, ∃ ω : Live → ℂ, ω ≠ 0 ∧ ω ∈ zeroLocus ℂ (Q.comap mkB.toRingHom) := by
        intro Q hQ
        have hQm : Q ∈ Iprev.minimalPrimes := hfin.mem_toFinset.mp hQ
        haveI : Q.IsPrime := hQm.isPrime
        have hQle : Q ≤ mB := quot_minPrime_le_mB Φ_alg h𝔭_hom (fun i => phaseForm (frontPrev i))
          (fun i => hphase_hom _) Q hQm
        have hQht : Q.height ≤ (k : ℕ∞) := by
          have hsp : Iprev = Ideal.span ((Finset.univ.image fun i : Fin k =>
              Ideal.Quotient.mk 𝔭 (phaseForm (frontPrev i))) : Set Bq) := by
            simp [Iprev]
          rw [hsp] at hQm
          have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hQm
          have h2 : (Finset.univ.image fun i : Fin k =>
              Ideal.Quotient.mk 𝔭 (phaseForm (frontPrev i))).card ≤ k :=
            Finset.card_image_le.trans (by simp)
          exact h1.trans (by exact_mod_cast h2)
        have hQlt : Q < mB := lt_of_le_of_ne hQle fun heq => by
          rw [heq, hmB_height] at hQht
          have : d ≤ k := by exact_mod_cast hQht
          omega
        have hXnot : ∃ σ : Live, mkB (X σ) ∉ Q := by
          by_contra hall
          push Not at hall
          apply hQlt.ne
          refine le_antisymm hQle (Ideal.span_le.mpr ?_)
          rintro _ ⟨σ, rfl⟩
          exact hall σ
        obtain ⟨σ0, hσ0⟩ := hXnot
        let QR : Ideal (MvPolynomial Live ℂ) := Q.comap mkB.toRingHom
        haveI : QR.IsPrime := Ideal.comap_isPrime mkB.toRingHom Q
        have hXnotQR : (X σ0 : MvPolynomial Live ℂ) ∉ QR := hσ0
        rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) QR,
          mem_vanishingIdeal_iff] at hXnotQR
        push Not at hXnotQR
        obtain ⟨ω, hωloc, hωne⟩ := hXnotQR
        refine ⟨ω, fun h0 => hωne (by simp [h0]), hωloc⟩
      choose ωQ hωQ_ne hωQ_loc using fun Q : Sk => hex_pt Q.1 Q.2
      let Bad : Finset S := Sk.attach.biUnion fun Q =>
        Finset.univ.filter fun s : S => aeval (ωQ Q) (phaseForm s) = 0
      have hBad_lt : Bad.card < (Finset.univ : Finset S).card := by
        have h1 : Bad.card * q ≤ Sk.card * (n * q ^ (n * n)) := by
          calc Bad.card * q
              ≤ (∑ Q ∈ Sk.attach, ((Finset.univ : Finset S).filter fun s =>
                  aeval (ωQ Q) (phaseForm s) = 0).card) * q :=
                Nat.mul_le_mul_right q Finset.card_biUnion_le
            _ = ∑ Q ∈ Sk.attach, ((Finset.univ : Finset S).filter fun s =>
                  aeval (ωQ Q) (phaseForm s) = 0).card * q := Finset.sum_mul _ _ _
            _ ≤ ∑ _Q ∈ Sk.attach, (n * q ^ (n * n)) :=
                Finset.sum_le_sum fun Q _ => hSZ_bad (ωQ Q) (hωQ_ne Q)
            _ = Sk.card * (n * q ^ (n * n)) := by simp
        have h2 : Sk.card * (n * q ^ (n * n)) < (Finset.univ : Finset S).card * q := by
          have hcardS : (Finset.univ : Finset S).card = q ^ (n * n) := by
            simp [S, E, I]
          rw [hcardS]
          calc Sk.card * (n * q ^ (n * n))
              ≤ n ^ d * (n * q ^ (n * n)) := Nat.mul_le_mul_right _ hSk_card
            _ = (n * n ^ d) * q ^ (n * n) := by ring
            _ < q * q ^ (n * n) := Nat.mul_lt_mul_of_pos_right hq_bound (pow_pos hq_pos _)
            _ = q ^ (n * n) * q := by ring
        exact Nat.lt_of_mul_lt_mul_right (h1.trans_lt h2)
      obtain ⟨sNext, _, hsNext_notBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hBad_lt
      let frontCur : Fin (k + 1) → S := Fin.snoc frontPrev sNext
      refine ⟨frontCur, fun P hP => ?_⟩
      haveI : P.IsPrime := hP.isPrime
      have hIprev_le : Iprev ≤ P := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hP.le (Ideal.subset_span ⟨i.castSucc, by simp [frontCur]⟩)
      obtain ⟨Q, hQmin, hQleP⟩ := Ideal.exists_minimalPrimes_le hIprev_le
      haveI : Q.IsPrime := hQmin.isPrime
      have hQSk : Q ∈ Sk := hfin.mem_toFinset.mpr hQmin
      have hmemP : mkB (phaseForm sNext) ∈ P :=
        hP.le (Ideal.subset_span ⟨Fin.last k, by simp [frontCur]; rfl⟩)
      have hnotQ : mkB (phaseForm sNext) ∉ Q := by
        intro hmemQ
        apply hsNext_notBad
        refine Finset.mem_biUnion.mpr ⟨⟨Q, hQSk⟩, Finset.mem_attach _ _, ?_⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact hωQ_loc ⟨Q, hQSk⟩ (phaseForm sNext) hmemQ
      have hQltP : Q < P := lt_of_le_of_ne hQleP fun heq => hnotQ (heq ▸ hmemP)
      calc ((k + 1 : ℕ) : ℕ∞) = (k : ℕ∞) + 1 := by push_cast; rfl
        _ ≤ Q.height + 1 := by gcongr; exact hprev Q hQmin
        _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hQltP
  obtain ⟨front, hfront⟩ := hfront_ind d le_rfl
  let Lfront : Fin d → MvPolynomial Live ℂ := fun h => phaseForm (front h)
  have hLfront_zero := quot_zeroLocus_eq_zero Φ_alg h𝔭_hom htrdeg_range Lfront
    (fun h => hphase_hom _) hfront
  obtain ⟨_, _, hfiber_bound⟩ := stage2_fiber_bound Φ_alg hΦ_deg h𝔭_hom htrdeg_range
    Lfront (fun h => hphase_hom _) hLfront_zero
  let Fy : (Fin d → ℂ) → Set (Live → ℂ) := fun y =>
    {ω : Live → ℂ | ω ∈ zeroLocus ℂ 𝔭 ∧ ∀ h : Fin d, aeval ω (Lfront h) = y h}
  have hFy_fin : ∀ y : Fin d → ℂ, (Fy y).Finite := by
    intro y
    by_contra hinf
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (n ^ d + 1)
    have hle := hfiber_bound y T fun ω hω => hTsub hω
    omega
  let extW : (Live → ℂ) → W := fun ω π => if h : π ∈ Live then ω ⟨π, h⟩ else 0
  let candidates : (Fin d → ℂ) → Finset W := fun y => (hFy_fin y).toFinset.image extW
  refine ⟨front, candidates, ?_, ?_⟩
  · intro y
    refine Finset.card_image_le.trans ?_
    exact hfiber_bound y (hFy_fin y).toFinset fun ω hω => (hFy_fin y).mem_toFinset.mp hω
  · intro A hA
    dsimp only [candidates]
    refine Finset.mem_image.mpr ⟨fun σ : Live => w A σ.1, ?_, ?_⟩
    · rw [(hFy_fin _).mem_toFinset]
      refine ⟨h_image_locus A hA, fun h => ?_⟩
      exact (hevalM_eq (front h) A hA).symm
    · funext π
      dsimp only [extW]
      split_ifs with hπ
      · rfl
      · have hnot : ¬ ∀ j : I, H (π j) j = true := by simpa [Live] using hπ
        push Not at hnot
        obtain ⟨j0, hj0⟩ := hnot
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ j0) (hA (π j0) j0 (Bool.eq_false_iff.mpr hj0))

end

end PEqualNP.Outside.L_lib_1091_aux

theorem PEqualNP.Outside.L_lib_1091 : (∀ (n q : ℕ) (H : Fin n → Fin n → Bool) (ζ : ℂ), 0 < n → IsPrimitiveRoot ζ q →
  let I := Fin n
  let E := I × I
  let V := Submodule.span ℚ {v : E → ℚ | ∃ σ : Equiv.Perm I, (∀ j, H (σ j) j = true) ∧
    v = fun e => if σ e.2 = e.1 then (1 : ℚ) else 0}
  let d := Module.finrank ℚ V
  let W := Equiv.Perm I → ℂ
  let S := E → Fin q
  let fits := fun (A : Matrix I I ℂ) => ∀ i j, H i j = false → A i j = 0
  let w := fun (A : Matrix I I ℂ) (π : Equiv.Perm I) => ∏ j : I, A (π j) j
  let eval := fun (s : S) (A : Matrix I I ℂ) =>
    Matrix.det (fun i j => A i j * ζ ^ (s (i,j)).val : Matrix I I ℂ)
  n * n ^ d < q →
  ∃ (front : Fin d → S) (candidates : (Fin d → ℂ) → Finset W),
    (∀ y, (candidates y).card ≤ n ^ d) ∧
    ∀ A : Matrix I I ℂ, fits A → w A ∈ candidates (fun h => eval (front h) A)) := by
  intro n q H ζ hn hζ I E V d W S fits w eval hq
  exact PEqualNP.Outside.L_lib_1091_aux.main_1091 n q H ζ hn hζ hq
