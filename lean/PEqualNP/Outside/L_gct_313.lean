import PEqualNP.Defs
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.CardEmbedding

namespace PEqualNP.Outside.L_gct_313
section SourceSubalgFinite

namespace FromGct.Helpers.Kneser

namespace Fin

open scoped Classical in

theorem levelSet_indicator_mem {K ι : Type*} [Field K] [Fintype ι]
    (A : Subalgebra K (ι → K)) {x : ι → K} (hx : x ∈ A) (c : K) :
    Set.indicator {j | x j = c} (1 : ι → K) ∈ A := by
  have key : Set.indicator {j | x j = c} (1 : ι → K)
      = ∏ μ ∈ (Finset.univ.image x).erase c,
          ((c - μ)⁻¹ • (x - algebraMap K (ι → K) μ)) := by
    funext j
    rw [Finset.prod_apply]
    by_cases h : x j = c
    · rw [Set.indicator_of_mem (by exact h)]
      symm
      apply Finset.prod_eq_one
      intro μ hμ
      have hne : c - μ ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hμ).symm
      simp [h, hne]
    · rw [Set.indicator_of_notMem (by exact h)]
      symm
      apply Finset.prod_eq_zero (i := x j)
      · exact Finset.mem_erase.mpr ⟨h, Finset.mem_image_of_mem x (Finset.mem_univ j)⟩
      · simp
  rw [key]
  exact A.prod_mem fun μ _ => A.smul_mem (A.sub_mem hx (A.algebraMap_mem μ)) _

open scoped Classical in

theorem eq_sum_levelSet_indicator {K ι : Type*} [Field K] [Fintype ι] (x : ι → K) :
    x = ∑ c ∈ Finset.univ.image x, c • Set.indicator {j | x j = c} (1 : ι → K) := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single (x j)]
  · simp
  · intro c _ hc
    have : j ∉ {j | x j = c} := fun h => hc (Eq.symm h)
    simp [Set.indicator_of_notMem this]
  · intro h
    exact absurd (Finset.mem_image_of_mem x (Finset.mem_univ j)) h

def indicatorSets {K ι : Type*} [Field K] (A : Subalgebra K (ι → K)) : Set (Set ι) :=
  {S | Set.indicator S (1 : ι → K) ∈ A}

theorem le_of_indicatorSets_subset {K ι : Type*} [Field K] [Fintype ι]
    {A B : Subalgebra K (ι → K)} (h : indicatorSets A ⊆ indicatorSets B) : A ≤ B := by
  classical
  intro x hx
  rw [eq_sum_levelSet_indicator x]
  exact B.sum_mem fun c _ => B.smul_mem (h (levelSet_indicator_mem A hx c)) c

theorem indicatorSets_injective {K ι : Type*} [Field K] [Fintype ι] :
    Function.Injective (indicatorSets : Subalgebra K (ι → K) → Set (Set ι)) :=
  fun _ _ h => le_antisymm (le_of_indicatorSets_subset h.le) (le_of_indicatorSets_subset h.ge)

theorem finite_subalgebra_pi (K ι : Type*) [Field K] [Fintype ι] :
    Finite (Subalgebra K (ι → K)) :=
  Finite.of_injective _ indicatorSets_injective

end Fin

theorem finite_subalgebra (n : ℕ) : Finite (Subalgebra ℂ (Fin n → ℂ)) :=
  Fin.finite_subalgebra_pi ℂ (Fin n)

end FromGct.Helpers.Kneser
end SourceSubalgFinite

section SourceETransform

namespace FromGct.Helpers.Kneser

namespace ETr

open Module

variable {n : ℕ}

theorem mulLeft_injective {e : Fin n → ℂ} (he : IsUnit e) :
    Function.Injective (LinearMap.mulLeft ℂ e) := by
  obtain ⟨u, rfl⟩ := he
  intro a b h
  have h' : (u : Fin n → ℂ) * a = u * b := h
  have := congrArg (fun z => ((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * z) h'
  simpa using this

theorem mulLeft_surjective {e : Fin n → ℂ} (he : IsUnit e) :
    Function.Surjective (LinearMap.mulLeft ℂ e) := by
  obtain ⟨u, rfl⟩ := he
  intro b
  exact ⟨((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * b, by simp⟩

theorem finrank_map_mulLeft {e : Fin n → ℂ} (he : IsUnit e) (S : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S.map (LinearMap.mulLeft ℂ e)) = finrank ℂ S :=
  (Submodule.equivMapOfInjective _ (mulLeft_injective he) S).finrank_eq.symm

theorem finrank_comap_mulLeft {e : Fin n → ℂ} (he : IsUnit e) (S : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S.comap (LinearMap.mulLeft ℂ e)) = finrank ℂ S := by
  rw [← finrank_map_mulLeft he (S.comap (LinearMap.mulLeft ℂ e)),
    Submodule.map_comap_eq_of_surjective (mulLeft_surjective he)]

theorem le_span_units (T : Submodule ℂ (Fin n → ℂ)) (h1 : (1 : Fin n → ℂ) ∈ T) :
    T ≤ Submodule.span ℂ {e | e ∈ T ∧ IsUnit e} := by
  intro v hv
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (insert (0 : ℂ) (Finset.univ.image (fun i => - v i)))
  have hc0 : c ≠ 0 := fun h => hc (by simp [h])
  have hci : ∀ i, v i + c ≠ 0 := by
    intro i h
    apply hc
    have : c = - v i := by linear_combination h
    rw [this]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hu1 : IsUnit (c • (1 : Fin n → ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    simpa using hc0
  have hu2 : IsUnit (v + c • (1 : Fin n → ℂ)) := by
    rw [Pi.isUnit_iff]
    intro i
    simpa using hci i
  have hv' : v = (v + c • (1 : Fin n → ℂ)) - c • (1 : Fin n → ℂ) := by simp
  rw [hv']
  exact Submodule.sub_mem _
    (Submodule.subset_span ⟨T.add_mem hv (T.smul_mem c h1), hu2⟩)
    (Submodule.subset_span ⟨T.smul_mem c h1, hu1⟩)

theorem core_stable (S T : Submodule ℂ (Fin n → ℂ)) (hS : (1 : Fin n → ℂ) ∈ S)
    (hT : (1 : Fin n → ℂ) ∈ T)
    (hA : ∀ e ∈ T, IsUnit e → S ≤ T.comap (LinearMap.mulLeft ℂ e)) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) := by
  have hST : ∀ s ∈ S, ∀ t ∈ T, s * t ∈ T := by
    intro s hs t ht
    have hle : Submodule.span ℂ {e | e ∈ T ∧ IsUnit e} ≤ T.comap (LinearMap.mulLeft ℂ s) := by
      rw [Submodule.span_le]
      rintro e ⟨heT, heu⟩
      have := hA e heT heu hs
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at this
      simpa [mul_comm] using this
    have := hle (le_span_units T hT ht)
    simpa using this
  refine ⟨Algebra.adjoin ℂ (S : Set (Fin n → ℂ)), T, ?_, le_rfl, ?_, ?_⟩
  · intro h hh
    induction hh using Algebra.adjoin_induction with
    | mem x hx => exact fun v hv => hST x hx v hv
    | algebraMap r =>
      intro v hv
      rw [← Algebra.smul_def]
      exact T.smul_mem r hv
    | add x y _ _ ihx ihy =>
      intro v hv
      rw [add_mul]
      exact T.add_mem (ihx v hv) (ihy v hv)
    | mul x y _ _ ihx ihy =>
      intro v hv
      rw [mul_assoc]
      exact ihx _ (ihy v hv)
  · intro t ht
    have := Submodule.mul_mem_mul hS ht
    simpa using this
  · have hle : S ≤ Subalgebra.toSubmodule (Algebra.adjoin ℂ (S : Set (Fin n → ℂ))) :=
      fun s hs => Algebra.subset_adjoin hs
    have := Submodule.finrank_mono hle
    omega

theorem finrank_transform (S T : Submodule ℂ (Fin n → ℂ)) {e : Fin n → ℂ} (he : IsUnit e) :
    finrank ℂ (S ⊓ T.comap (LinearMap.mulLeft ℂ e) : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊔ S.map (LinearMap.mulLeft ℂ e) : Submodule ℂ (Fin n → ℂ)) =
    finrank ℂ S + finrank ℂ T := by
  have hinf : T ⊓ S.map (LinearMap.mulLeft ℂ e) =
      (S ⊓ T.comap (LinearMap.mulLeft ℂ e)).map (LinearMap.mulLeft ℂ e) := by
    ext y
    simp only [Submodule.mem_inf, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨hy, s, hs, rfl⟩
      exact ⟨s, ⟨hs, hy⟩, rfl⟩
    · rintro ⟨s, ⟨hs, hy⟩, rfl⟩
      exact ⟨hy, s, hs, rfl⟩
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T (S.map (LinearMap.mulLeft ℂ e))
  rw [hinf, finrank_map_mulLeft he, finrank_map_mulLeft he] at h1
  omega

theorem transform_mul_le (S T : Submodule ℂ (Fin n → ℂ)) (e : Fin n → ℂ) :
    (S ⊓ T.comap (LinearMap.mulLeft ℂ e)) * (T ⊔ S.map (LinearMap.mulLeft ℂ e)) ≤ S * T := by
  rw [Submodule.mul_le]
  intro s hs m hm
  have hmem : T ⊔ S.map (LinearMap.mulLeft ℂ e) ≤ (S * T).comap (LinearMap.mulLeft ℂ s) := by
    refine sup_le ?_ ?_
    · intro t ht
      exact Submodule.mul_mem_mul hs.1 ht
    · rintro _ ⟨s0, hs0, rfl⟩
      have h2 : e * s ∈ T := hs.2
      have := Submodule.mul_mem_mul hs0 h2
      simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have heq : s * (e * s0) = s0 * (e * s) := by ring
      rw [heq]
      exact this
  exact hmem hm

theorem core (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (hS : (1 : Fin n → ℂ) ∈ S)
    (hT : (1 : Fin n → ℂ) ∈ T) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) := by
  suffices key : ∀ k : ℕ, ∀ S T : Submodule ℂ (Fin n → ℂ), finrank ℂ S = k →
      (1 : Fin n → ℂ) ∈ S → (1 : Fin n → ℂ) ∈ T →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ T ≤ V ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H) from
    key _ S T rfl hS hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro S T hk hS hT
    by_cases hA : ∀ e ∈ T, IsUnit e → S ≤ T.comap (LinearMap.mulLeft ℂ e)
    · exact core_stable S T hS hT hA
    · push Not at hA
      obtain ⟨e, heT, heu, hne⟩ := hA
      have hlt : S ⊓ T.comap (LinearMap.mulLeft ℂ e) < S := inf_lt_left.mpr hne
      have hdim := Submodule.finrank_lt_finrank_of_lt hlt
      have h1S : (1 : Fin n → ℂ) ∈ S ⊓ T.comap (LinearMap.mulLeft ℂ e) := by
        refine ⟨hS, ?_⟩
        simpa using heT
      have h1T : (1 : Fin n → ℂ) ∈ T ⊔ S.map (LinearMap.mulLeft ℂ e) :=
        (le_sup_left : T ≤ _) hT
      obtain ⟨H, V, hHV, hTV, hVle, hfin⟩ :=
        ih _ (hk ▸ hdim) (S ⊓ T.comap (LinearMap.mulLeft ℂ e))
          (T ⊔ S.map (LinearMap.mulLeft ℂ e)) rfl h1S h1T
      refine ⟨H, V, hHV, le_trans le_sup_left hTV, le_trans hVle (transform_mul_le S T e), ?_⟩
      have := finrank_transform S T heu
      omega

end ETr

open Module in

theorem etransform (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ)
    (hx : x ∈ S) (hxu : IsUnit x) (hT : ∃ t ∈ T, IsUnit t) :
    ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      Module.finrank ℂ S + Module.finrank ℂ T ≤
        Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H) := by
  obtain ⟨t, ht, htu⟩ := hT
  have h1S : (1 : Fin n → ℂ) ∈ S.comap (LinearMap.mulLeft ℂ x) := by simpa using hx
  have h1T : (1 : Fin n → ℂ) ∈ T.comap (LinearMap.mulLeft ℂ t) := by simpa using ht
  obtain ⟨H, V0, hHV, hTV, hVle, hfin⟩ := ETr.core n _ _ h1S h1T
  have hxt : IsUnit (x * t) := hxu.mul htu
  refine ⟨H, V0.map (LinearMap.mulLeft ℂ (x * t)), ?_, ?_, ?_, ?_⟩
  · rintro h hh _ ⟨v, hv, rfl⟩
    refine ⟨h * v, hHV h hh v hv, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    ring
  · intro t' ht'
    obtain ⟨u, rfl⟩ := htu
    refine ⟨((u⁻¹ : (Fin n → ℂ)ˣ) : Fin n → ℂ) * t', hTV ?_, ?_⟩
    · simpa using ht'
    · simp only [LinearMap.mulLeft_apply]
      rw [mul_assoc, Units.mul_inv_cancel_left]
  · rw [Submodule.map_le_iff_le_comap]
    refine le_trans hVle ?_
    rw [Submodule.mul_le]
    intro s0 hs0 t0 ht0
    have h1 : x * s0 ∈ S := hs0
    have h2 : t * t0 ∈ T := ht0
    have := Submodule.mul_mem_mul h1 h2
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply]
    have heq : x * t * (s0 * t0) = x * s0 * (t * t0) := by ring
    rw [heq]
    exact this
  · rw [ETr.finrank_map_mulLeft hxt, ← ETr.finrank_comap_mulLeft hxu S,
      ← ETr.finrank_comap_mulLeft htu T]
    exact hfin

end FromGct.Helpers.Kneser
end SourceETransform

section SourceAssembly

namespace FromGct.Helpers.Kneser

open Module

namespace Asm

theorem exists_isUnit_of_support {n : ℕ} (U : Submodule ℂ (Fin n → ℂ))
    (hU : ∀ i, ∃ u ∈ U, u i ≠ 0) : ∃ u ∈ U, IsUnit u := by
  by_contra hno
  push Not at hno
  let P : Fin n → Submodule ℂ U := fun i =>
    (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap U.subtype
  have hcov : ⋃ i, (P i : Set U) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    have h1 := hno u.1 u.2
    rw [Pi.isUnit_iff] at h1
    push Not at h1
    obtain ⟨i, hi⟩ := h1
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have h0 : u.1 i = 0 := by
      by_contra hne
      exact hi (isUnit_iff_ne_zero.2 hne)
    show U.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    rw [LinearMap.mem_ker]
    exact h0
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  obtain ⟨u, hu, hui⟩ := hU i
  have hmem : (⟨u, hu⟩ : U) ∈ P i := by
    rw [hi]
    exact Submodule.mem_top
  have h0 : U.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) := hmem
  rw [LinearMap.mem_ker] at h0
  exact hui h0

theorem full_of {n : ℕ} (hfin : Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H))
    (S T : Submodule ℂ (Fin n → ℂ)) (hS0 : S ≠ ⊥) (hS : ∀ i, ∃ s ∈ S, s i ≠ 0)
    (hT : ∃ t ∈ T, IsUnit t) :
    ∃ H : Subalgebra ℂ (Fin n → ℂ), (∀ h ∈ H, ∀ v ∈ S * T, h * v ∈ S * T) ∧
      finrank ℂ S + finrank ℂ T ≤
        finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) +
          finrank ℂ (Subalgebra.toSubmodule H) := by

  let G : Subalgebra ℂ (Fin n → ℂ) → Set (Fin n → ℂ) := fun H =>
    {x | x ∈ S ∧ ∃ V : Submodule ℂ (Fin n → ℂ),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H)}
  let P : Fin n ⊕ Subalgebra ℂ (Fin n → ℂ) → Submodule ℂ S := fun j =>
    Sum.elim
      (fun i => (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap S.subtype)
      (fun H => (Submodule.span ℂ (G H)).comap S.subtype) j
  have hcov : ⋃ j, (P j : Set S) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    by_cases hu : IsUnit u.1
    · obtain ⟨H, V, h1, h2, h3, h4⟩ := hetr S T u.1 u.2 hu hT
      refine Set.mem_iUnion.2 ⟨Sum.inr H, ?_⟩
      show S.subtype u ∈ Submodule.span ℂ (G H)
      exact Submodule.subset_span ⟨u.2, V, h1, h2, h3, h4⟩
    · rw [Pi.isUnit_iff] at hu
      push Not at hu
      obtain ⟨i, hi⟩ := hu
      refine Set.mem_iUnion.2 ⟨Sum.inl i, ?_⟩
      have h0 : u.1 i = 0 := by
        by_contra hne
        exact hi (isUnit_iff_ne_zero.2 hne)
      show S.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
      rw [LinearMap.mem_ker]
      exact h0
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  rcases j with i | H
  · exfalso
    obtain ⟨u, hu, hui⟩ := hS i
    have hmem : (⟨u, hu⟩ : S) ∈ P (Sum.inl i) := by
      rw [hj]
      exact Submodule.mem_top
    have h0 : S.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) :=
      hmem
    rw [LinearMap.mem_ker] at h0
    exact hui h0
  · have hspan : S ≤ Submodule.span ℂ (G H) := by
      intro s hs
      have hmem : (⟨s, hs⟩ : S) ∈ P (Sum.inr H) := by
        rw [hj]
        exact Submodule.mem_top
      exact hmem

    let M : Submodule ℂ (Fin n → ℂ) :=
      sSup {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T}
    have hM_le : M ≤ S * T := sSup_le fun V hV => hV.2
    have hM_stab : ∀ h ∈ H, ∀ v ∈ M, h * v ∈ M := by
      intro h hh
      have hle : M ≤ M.comap (LinearMap.mulLeft ℂ h) := by
        refine sSup_le fun V hV v hv => ?_
        show (LinearMap.mulLeft ℂ h) v ∈ M
        rw [LinearMap.mulLeft_apply]
        exact (le_sSup hV : V ≤ M) (hV.1 h hh v hv)
      intro v hv
      have h1 := hle hv
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
      exact h1
    have hST_le : S * T ≤ M := by
      rw [Submodule.mul_le]
      intro s hs t ht
      have hle : Submodule.span ℂ (G H) ≤ M.comap (LinearMap.mulRight ℂ t) := by
        rw [Submodule.span_le]
        rintro x ⟨_, V, h1, h2, h3, _⟩
        show (LinearMap.mulRight ℂ t) x ∈ M
        rw [LinearMap.mulRight_apply]
        exact (le_sSup (show V ∈ {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T} from
          ⟨h1, h3⟩) : V ≤ M) (h2 t ht)
      have h1 := hle (hspan hs)
      rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h1
      exact h1
    have hne : (G H).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hS0
      rw [eq_bot_iff]
      intro s hs
      have h1 := hspan hs
      rw [hemp, Submodule.span_empty] at h1
      exact h1
    obtain ⟨x, _, V, _, _, h3, h4⟩ := hne
    have hVle : finrank ℂ V ≤ finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) :=
      Submodule.finrank_mono h3
    refine ⟨H, fun h hh v hv => hM_le (hM_stab h hh v (hST_le hv)), ?_⟩
    omega

def offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) :=
  { carrier := {x | ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0}, add_mem' := by
      intro a b ha hb i h1 h2
      simp [ha i h1 h2, hb i h1 h2]
    zero_mem' := by
      intro i _ _
      rfl
    smul_mem' := by
      intro c a ha i h1 h2
      simp [ha i h1 h2] }

theorem mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ} :
    x ∈ offSupp S T ↔ ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0 :=
  Iff.rfl

theorem mul_mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ offSupp S T) (a : Fin n → ℂ) : a * x ∈ offSupp S T := by
  intro i h1 h2
  simp [hx i h1 h2]

theorem mul_apply_eq_zero {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ}
    (hv : v ∈ S * T) (i : Fin n) (hi : ¬((∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0))) :
    v i = 0 := by
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    by_contra hne
    rw [Pi.mul_apply] at hne
    exact hi ⟨⟨s, hs, left_ne_zero_of_mul hne⟩, ⟨t, ht, right_ne_zero_of_mul hne⟩⟩
  · intro a b ha hb
    simp [ha, hb]

theorem support_sup_offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ S ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ s ∈ S, s i ≠ 0
  · obtain ⟨s, hs, hsi⟩ := hK
    exact ⟨s, (le_sup_left : S ≤ S ⊔ offSupp S T) hs, hsi⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ S ⊔ offSupp S T) ?_, by simp⟩
    intro j h1 _
    by_cases hji : j = i
    · subst hji
      exact absurd h1 hK
    · simp [hji]

theorem support_sup_offSupp' {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ T ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ t ∈ T, t i ≠ 0
  · obtain ⟨t, ht, hti⟩ := hK
    exact ⟨t, (le_sup_left : T ≤ T ⊔ offSupp S T) ht, hti⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ T ⊔ offSupp S T) ?_, by simp⟩
    intro j _ h2
    by_cases hji : j = i
    · subst hji
      exact absurd h2 hK
    · simp [hji]

theorem sup_mul_sup_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    (S ⊔ offSupp S T) * (T ⊔ offSupp S T) ≤ S * T ⊔ offSupp S T := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.1 hb
  have h1 : s * t ∈ S * T := Submodule.mul_mem_mul hs ht
  have h2 : s * w' + w * t + w * w' ∈ offSupp S T := by
    refine Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_offSupp hw' s) ?_)
      (mul_mem_offSupp hw' w)
    rw [mul_comm]
    exact mul_mem_offSupp hw t
  have h3 : (s + w) * (t + w') = s * t + (s * w' + w * t + w * w') := by ring
  rw [h3]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

theorem finrank_inf_offSupp_add_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) ≤ finrank ℂ (offSupp S T) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ offSupp S T) (T ⊓ offSupp S T)
  have h2 : (S ⊓ offSupp S T) ⊓ (T ⊓ offSupp S T) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxS, hxW⟩, ⟨hxT, _⟩⟩
    rw [Submodule.mem_bot]
    funext i
    by_contra hne
    exact hne (hxW i ⟨x, hxS, hne⟩ ⟨x, hxT, hne⟩)
  have h3 : finrank ℂ ((S ⊓ offSupp S T) ⊔ (T ⊓ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (offSupp S T) :=
    Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
  rw [h2, finrank_bot] at h1
  omega

end Asm

open Asm in

theorem kneser_of
    (hfin : ∀ n : ℕ, Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        Module.finrank ℂ S + Module.finrank ℂ T ≤
          Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H)) :
    ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St := by
  intro n S T St hS _ hSt
  have hS' : S ⊔ offSupp S T ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff, ← h]
    exact le_sup_left
  obtain ⟨H, hH, hdim⟩ := full_of (hfin n) (hetr n) (S ⊔ offSupp S T) (T ⊔ offSupp S T) hS'
    (support_sup_offSupp S T) (exists_isUnit_of_support _ (support_sup_offSupp' S T))

  have hHSt : Subalgebra.toSubmodule H ≤ St := by
    intro h hh
    rw [hSt]
    intro v hv
    have hv' : v ∈ (S ⊔ offSupp S T) * (T ⊔ offSupp S T) :=
      (Submodule.mul_le.2 fun s hs t ht =>
        Submodule.mul_mem_mul (Submodule.mem_sup_left hs) (Submodule.mem_sup_left ht)) hv
    obtain ⟨a, ha, w, hw, hsum⟩ :=
      Submodule.mem_sup.1 (sup_mul_sup_le S T (hH h ((Subalgebra.mem_toSubmodule _).1 hh) v hv'))
    have hw0 : w = 0 := by
      funext i
      by_cases hK : (∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0)
      · exact hw i hK.1 hK.2
      · have e1 : a i + w i = h i * v i := by
          rw [← Pi.add_apply, hsum, Pi.mul_apply]
        rw [mul_apply_eq_zero ha i hK, mul_apply_eq_zero hv i hK] at e1
        simpa using e1
    rw [hw0, add_zero] at hsum
    rw [← hsum]
    exact ha
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq S (offSupp S T)
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq T (offSupp S T)
  have d3 := finrank_inf_offSupp_add_le S T
  have d4 : finrank ℂ ((S ⊔ offSupp S T) * (T ⊔ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) + finrank ℂ (offSupp S T) :=
    (Submodule.finrank_mono (sup_mul_sup_le S T)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have d5 : finrank ℂ (Subalgebra.toSubmodule H) ≤ finrank ℂ St := Submodule.finrank_mono hHSt
  omega

end FromGct.Helpers.Kneser
end SourceAssembly

section SourceL065

theorem FromGct.L065 : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ → (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) → Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St :=
  FromGct.Helpers.Kneser.kneser_of FromGct.Helpers.Kneser.finite_subalgebra
    FromGct.Helpers.Kneser.etransform
end SourceL065

section SourceFermatFromKneser

namespace FromGct.Helpers

open Module Finset

section General

variable {ι : Type} [Fintype ι]

def FermatIso (W : Submodule ℂ (ι → ℂ)) : Prop :=
  (∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0) ∧
    (∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∑ i, u i * v i * z i = 0)

def KneserFor (ι : Type) [Fintype ι] : Prop :=
  ∀ S T St : Submodule ℂ (ι → ℂ), S ≠ ⊥ → T ≠ ⊥ →
    (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ (S * T) + finrank ℂ St

def stab (V : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  { carrier := {x | ∀ v ∈ V, x * v ∈ V}, add_mem' := fun {a b} ha hb v hv => by rw [add_mul]; exact V.add_mem (ha v hv) (hb v hv)
    zero_mem' := fun v _ => by rw [zero_mul]; exact V.zero_mem
    smul_mem' := fun c x hx v hv => by rw [smul_mul_assoc]; exact V.smul_mem c (hx v hv) }

omit [Fintype ι] in
theorem mem_stab {V : Submodule ℂ (ι → ℂ)} {x : ι → ℂ} : x ∈ stab V ↔ ∀ v ∈ V, x * v ∈ V :=
  Iff.rfl

omit [Fintype ι] in
theorem one_mem_stab (V : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ stab V := fun v hv => by
  rwa [one_mul]

omit [Fintype ι] in
theorem mul_mem_stab {V : Submodule ℂ (ι → ℂ)} {x y : ι → ℂ} (hx : x ∈ stab V)
    (hy : y ∈ stab V) : x * y ∈ stab V := fun v hv => by
  rw [mul_assoc]; exact hx _ (hy v hv)

noncomputable def dotDual : (ι → ℂ) →ₗ[ℂ] Module.Dual ℂ (ι → ℂ) :=
  LinearMap.mk₂ ℂ (fun v z => ∑ i, v i * z i)
    (fun a b z => by simp only [Pi.add_apply, add_mul, sum_add_distrib])
    (fun c a z => by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum])
    (fun v a b => by simp only [Pi.add_apply, mul_add, sum_add_distrib])
    (fun c v a => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
      exact sum_congr rfl fun i _ => by ring)

theorem dotDual_apply (v z : ι → ℂ) : dotDual v z = ∑ i, v i * z i := rfl

theorem dotDual_injective : Function.Injective (dotDual (ι := ι)) := by
  classical
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  funext j
  have h := LinearMap.congr_fun hv (Pi.single j 1)
  rw [dotDual_apply] at h
  simpa [Pi.single_apply] using h

theorem perp_bound (V W : Submodule ℂ (ι → ℂ)) (h : ∀ v ∈ V, ∀ z ∈ W, ∑ i, v i * z i = 0) :
    finrank ℂ V + finrank ℂ W ≤ Fintype.card ι := by
  have hle : V.map dotDual ≤ W.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : finrank ℂ (V.map dotDual) = finrank ℂ V :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ dotDual_injective V)).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have e3 := Submodule.finrank_mono hle
  rw [Module.finrank_fintype_fun_eq_card] at e2
  omega

theorem exists_indicator {V : Submodule ℂ (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ stab V) (i : ι) :
    ∃ e ∈ stab V, ∀ k, e k = if x k = x i then 1 else 0 := by
  classical
  refine ⟨∏ c ∈ (univ.image x).erase (x i), (x i - c)⁻¹ • (x - c • 1), ?_, ?_⟩
  · refine Finset.prod_induction _ (· ∈ stab V) (fun a b ha hb => mul_mem_stab ha hb)
      (one_mem_stab V) fun c _ => ?_
    exact (stab V).smul_mem _ ((stab V).sub_mem hx ((stab V).smul_mem _ (one_mem_stab V)))
  · intro k
    rw [Finset.prod_apply]
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    split_ifs with hk
    · refine Finset.prod_eq_one fun c hc => ?_
      have hc' : c ≠ x i := (Finset.mem_erase.1 hc).1
      rw [hk]
      exact inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hc'))
    · refine Finset.prod_eq_zero (i := x k) ?_ (by rw [sub_self, mul_zero])
      exact Finset.mem_erase.2 ⟨hk, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩

noncomputable def restr (p : ι → ℂ) : (ι → ℂ) →ₗ[ℂ] ({k // p k = 1} → ℂ) :=
  LinearMap.funLeft ℂ ℂ Subtype.val

omit [Fintype ι] in
theorem restr_apply (p u : ι → ℂ) (k : {k // p k = 1}) : restr p u k = u k := rfl

theorem sum_restr (p : ι → ℂ) (hp : ∀ k, p k = 0 ∨ p k = 1) (f : ι → ℂ) :
    ∑ k : {k // p k = 1}, f k = ∑ k, p k * f k := by
  classical
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => p k = 1) (fun k => p k * f k)]
  have h2 : ∑ k : {k // ¬ p k = 1}, p k * f k = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hp k with h | h
    · rw [h, zero_mul]
    · exact absurd h k.2
  rw [h2, add_zero]
  exact Finset.sum_congr rfl fun k _ => by rw [k.2, one_mul]

noncomputable def vSpan (W : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  (W ⊔ Submodule.span ℂ {1}) * W

omit [Fintype ι] in
theorem le_vSpan (W : Submodule ℂ (ι → ℂ)) {u : ι → ℂ} (hu : u ∈ W) : u ∈ vSpan W := by
  have := Submodule.mul_mem_mul
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self (1 : ι → ℂ)) :
      (1 : ι → ℂ) ∈ W ⊔ Submodule.span ℂ {1}) hu
  rwa [one_mul] at this

omit [Fintype ι] in
theorem mul_mem_vSpan (W : Submodule ℂ (ι → ℂ)) {u v : ι → ℂ} (hu : u ∈ W) (hv : v ∈ W) :
    u * v ∈ vSpan W :=
  Submodule.mul_mem_mul (Submodule.mem_sup_left hu) hv

theorem vSpan_perp {W : Submodule ℂ (ι → ℂ)} (hW : FermatIso W) :
    ∀ v ∈ vSpan W, ∀ z ∈ W, ∑ i, v i * z i = 0 := by
  intro v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro m hm n hn z hz
    obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 hm
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have h1 := hW.2 y hy n hn z hz
    have h2 := hW.1 n hn z hz
    calc ∑ i, ((y + c • 1) * n) i * z i
        = ∑ i, y i * n i * z i + c * ∑ i, n i * z i := by
          rw [mul_sum, ← sum_add_distrib]
          refine sum_congr rfl fun i _ => ?_
          simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
          ring
      _ = 0 := by rw [h1, h2, mul_zero, add_zero]
  · intro a b ha hb z hz
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]

theorem restr_iso {W : Submodule ℂ (ι → ℂ)} (hW : FermatIso W) {p : ι → ℂ}
    (hp : p ∈ stab (vSpan W)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    FermatIso (W.map (restr p)) := by
  have hperp := vSpan_perp hW
  constructor
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k)]
    have := hperp _ (hp _ (le_vSpan W hu)) v hv
    simpa only [Pi.mul_apply, mul_assoc] using this
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨z, hz, rfl⟩
    simp only [restr_apply]
    rw [sum_restr p hp01 (fun k => u k * v k * z k)]
    have := hperp _ (hp _ (mul_mem_vSpan W hu hv)) z hz
    simpa only [Pi.mul_apply, mul_assoc] using this

theorem finrank_split (W : Submodule ℂ (ι → ℂ)) (e f : ι → ℂ) (hef : ∀ k, e k = 1 ∨ f k = 1) :
    finrank ℂ W ≤ finrank ℂ (W.map (restr e)) + finrank ℂ (W.map (restr f)) := by
  let R := (restr e).prod (restr f)
  have hR : Function.Injective R := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    funext k
    rcases hef k with h | h
    · have := congr_fun (congr_arg Prod.fst hu) ⟨k, h⟩
      simpa [R, restr_apply] using this
    · have := congr_fun (congr_arg Prod.snd hu) ⟨k, h⟩
      simpa [R, restr_apply] using this
  have e1 : finrank ℂ (W.map R) = finrank ℂ W :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hR W)).symm
  let A := {k // e k = 1} → ℂ
  let B := {k // f k = 1} → ℂ
  have hle : W.map R ≤ (W.map (restr e)).map (LinearMap.inl ℂ A B) ⊔
      (W.map (restr f)).map (LinearMap.inr ℂ A B) := by
    rintro _ ⟨u, hu, rfl⟩
    have : R u = LinearMap.inl ℂ A B (restr e u) + LinearMap.inr ℂ A B (restr f u) := by
      simp [R]
    rw [this]
    exact Submodule.add_mem_sup ⟨_, ⟨u, hu, rfl⟩, rfl⟩ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    ((W.map (restr e)).map (LinearMap.inl ℂ A B)) ((W.map (restr f)).map (LinearMap.inr ℂ A B))
  have h3 := Submodule.finrank_map_le (LinearMap.inl ℂ A B) (W.map (restr e))
  have h4 := Submodule.finrank_map_le (LinearMap.inr ℂ A B) (W.map (restr f))
  rw [← e1]
  exact h1.trans (h2.trans (add_le_add h3 h4))

end General

theorem kneserFor_of_fin
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St)
    (ι : Type) [Fintype ι] : KneserFor ι := by
  intro S T St hS hT hSt
  let Φ : (ι → ℂ) ≃ₐ[ℂ] (Fin (Fintype.card ι) → ℂ) :=
    AlgEquiv.piCongrLeft' ℂ (fun _ => ℂ) (Fintype.equivFin ι)
  have hfr : ∀ X : Submodule ℂ (ι → ℂ),
      finrank ℂ (X.map Φ.toLinearMap) = finrank ℂ X := fun X =>
    LinearEquiv.finrank_map_eq Φ.toLinearEquiv X
  have hne : ∀ X : Submodule ℂ (ι → ℂ), X ≠ ⊥ → X.map Φ.toLinearMap ≠ ⊥ := by
    intro X hX h
    apply hX
    rw [← Submodule.finrank_eq_zero, ← hfr X, h, finrank_bot]
  have hmul := Submodule.map_mul S T Φ.toAlgHom
  have key := hK _ (S.map Φ.toLinearMap) (T.map Φ.toLinearMap) (St.map Φ.toLinearMap)
    (hne S hS) (hne T hT) ?_
  · rw [hfr, hfr, hfr] at key
    erw [← hmul, hfr] at key
    exact key
  · intro x
    have hmul' : (S * T).map Φ.toLinearMap =
        S.map Φ.toLinearMap * T.map Φ.toLinearMap := hmul
    rw [← hmul']
    constructor
    · rintro ⟨y, hy, rfl⟩ _ ⟨w, hw, rfl⟩
      refine ⟨y * w, (hSt y).1 hy w hw, ?_⟩
      simp
    · intro h
      refine ⟨Φ.symm x, (hSt _).2 fun w hw => ?_, by simp⟩
      obtain ⟨w', hw', he⟩ := h (Φ w) ⟨w, hw, rfl⟩
      have : w' = Φ.symm x * w := by
        apply Φ.injective
        simp only [AlgEquiv.toLinearMap_apply] at he
        rw [he, map_mul, AlgEquiv.apply_symm_apply]
      rw [← this]
      exact hw'

theorem fermat_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), FermatIso W → 3 * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  have hone : (1 : ι → ℂ) ∉ W := by
    intro h
    have := hW.1 1 h 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  set V := vSpan W with hVdef
  by_cases hconst : ∀ x ∈ stab V, ∀ j k, x j = x k
  ·
    have hSt : finrank ℂ (stab V) ≤ 1 := by
      have : stab V ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x hx i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hU : finrank ℂ ↥(W ⊔ Submodule.span ℂ {(1 : ι → ℂ)}) = finrank ℂ W + 1 := by
      have hinf : W ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxW, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := W.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hUne : W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} ≠ ⊥ := by
      intro h
      have : (1 : ι → ℂ) ∈ W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} :=
        Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      rw [h, Submodule.mem_bot] at this
      exact one_ne_zero this
    have hk := hK ι _ W (stab V) hUne hW0 (fun x => Iff.rfl)
    have hp := perp_bound V W (vSpan_perp hW)
    change _ + _ ≤ finrank ℂ V + _ at hk
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab V := (stab V).sub_mem (one_mem_stab V) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_iso hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_iso hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    omega

theorem fermat_of_kneser
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) :
    ∀ (M : ℕ) (W : Submodule ℂ (Fin M → ℂ)), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) →
      (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → 3 * Module.finrank ℂ W ≤ M := by
  intro M W h2 h3
  have hQ : ∀ u ∈ W, ∀ v ∈ W, ∑ i, u i * v i = 0 := by
    intro u hu v hv
    have key : ∑ i, (2 : ℂ) * (u i * v i) =
        (∑ i, (u + v) i ^ 2) - (∑ i, u i ^ 2) - (∑ i, v i ^ 2) := by
      simp only [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h2 _ (W.add_mem hu hv), h2 u hu, h2 v hv, ← mul_sum] at key
    simpa using key
  have hC : ∀ u ∈ W, ∀ v ∈ W, ∀ z ∈ W, ∑ i, u i * v i * z i = 0 := by
    intro u hu v hv z hz
    have key : ∑ i, (6 : ℂ) * (u i * v i * z i) =
        (∑ i, (u + v + z) i ^ 3) - (∑ i, (u + v) i ^ 3) - (∑ i, (u + z) i ^ 3)
          - (∑ i, (v + z) i ^ 3) + (∑ i, u i ^ 3) + (∑ i, v i ^ 3) + (∑ i, z i ^ 3) := by
      simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.add_apply]; ring
    rw [h3 _ (W.add_mem (W.add_mem hu hv) hz), h3 _ (W.add_mem hu hv), h3 _ (W.add_mem hu hz),
      h3 _ (W.add_mem hv hz), h3 u hu, h3 v hv, h3 z hz, ← mul_sum] at key
    have h6 : (6 : ℂ) ≠ 0 := by norm_num
    simpa [h6] using key
  have := fermat_general (kneserFor_of_fin hK) M (Fin M) (Fintype.card_fin M) W ⟨hQ, hC⟩
  exact this

end FromGct.Helpers
end SourceFermatFromKneser

section SourceFermatIterated

namespace FromGct.Helpers.FermatIter

open Module Finset FromGct.Helpers

section General

variable {ι : Type} [Fintype ι]

noncomputable def vChain (W : Submodule ℂ (ι → ℂ)) (a : ℕ) : Submodule ℂ (ι → ℂ) :=
  (W + 1) ^ a * W

def perp (W : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) :=
  { carrier := {v | ∀ z ∈ W, ∑ i, v i * z i = 0}, add_mem' := fun {a b} ha hb z hz => by
      simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]
    zero_mem' := fun z _ => by simp
    smul_mem' := fun c x hx z hz => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, hx z hz, mul_zero] }

theorem mem_perp {W : Submodule ℂ (ι → ℂ)} {v : ι → ℂ} :
    v ∈ perp W ↔ ∀ z ∈ W, ∑ i, v i * z i = 0 := Iff.rfl

theorem polar_step (W : Submodule ℂ (ι → ℂ)) (c : ι → ℂ) (n : ℕ)
    (h : ∀ x ∈ W, ∑ i, x i ^ (n + 1) * c i = 0) :
    ∀ x ∈ W, ∀ y ∈ W, ∑ i, x i ^ n * (y i * c i) = 0 := by
  intro x hx y hy
  let q : Polynomial ℂ := ∑ i, Polynomial.C (c i) *
    (Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) ^ (n + 1)
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have := h (x + t • y) (W.add_mem hx (W.smul_mem t hy))
    simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← this]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd : Polynomial.eval 0 (Polynomial.derivative q) = 0 := by
    rw [hq]; simp
  have hd2 : Polynomial.eval 0 (Polynomial.derivative q) =
      ((n : ℂ) + 1) * ∑ i, x i ^ n * (y i * c i) := by
    simp only [q, Polynomial.derivative_sum, Polynomial.eval_finsetSum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp [Polynomial.derivative_pow]
    ring
  rw [hd2] at hd
  exact (mul_eq_zero.1 hd).resolve_left (Nat.cast_add_one_ne_zero n)

theorem pow_perp (W : Submodule ℂ (ι → ℂ)) (k : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ r n : ℕ, 2 ≤ n + r → n + r ≤ k → ∀ c ∈ W ^ r, ∀ x ∈ W, ∑ i, x i ^ n * c i = 0 := by
  intro r
  induction r with
  | zero =>
    intro n h2 hk c hc x hx
    rw [pow_zero, Submodule.one_eq_span] at hc
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hc
    have := h n h2 hk x hx
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, ← sum_mul, this, zero_mul]
  | succ r ih =>
    intro n h2 hk c hc
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro c' hc' y hy x hx
      have := polar_step W c' n (ih (n + 1) (by omega) (by omega) c' hc') x hx y hy
      refine (sum_congr rfl fun i _ => ?_).trans this
      rw [Pi.mul_apply, mul_comm (c' i)]
    · intro a b ha hb x hx
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha x hx, hb x hx, add_zero]

theorem chain_le_perp (W : Submodule ℂ (ι → ℂ)) (k : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ a b : ℕ, 1 ≤ b → a + b + 1 ≤ k → (W + 1) ^ a * W ^ b ≤ perp W := by
  intro a
  induction a with
  | zero =>
    intro b hb hk v hv z hz
    rw [pow_zero, one_mul] at hv
    have := pow_perp W k h b 1 (by omega) (by omega) v hv z hz
    refine (sum_congr rfl fun i _ => ?_).trans this
    rw [pow_one, mul_comm]
  | succ a ih =>
    intro b hb hk
    have e : (W + 1) ^ (a + 1) * W ^ b = (W + 1) ^ a * W ^ (b + 1) + (W + 1) ^ a * W ^ b := by
      ring
    rw [e, Submodule.add_eq_sup]
    exact sup_le (ih (b + 1) (by omega) (by omega)) (ih b hb (by omega))

theorem vChain_perp_of_psum (W : Submodule ℂ (ι → ℂ)) (a : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ a + 2 → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0 := by
  intro v hv
  have := chain_le_perp W (a + 2) h a 1 le_rfl le_rfl
  rw [pow_one] at this
  exact this hv

omit [Fintype ι] in
theorem one_mem_add_one (W : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ W + 1 :=
  Submodule.one_le.1 (le_sup_right : (1 : Submodule ℂ (ι → ℂ)) ≤ W ⊔ 1)

omit [Fintype ι] in
theorem vChain_zero (W : Submodule ℂ (ι → ℂ)) : vChain W 0 = W := by
  unfold vChain; rw [pow_zero, one_mul]

omit [Fintype ι] in
theorem vChain_succ (W : Submodule ℂ (ι → ℂ)) (a : ℕ) :
    vChain W (a + 1) = (W + 1) * vChain W a := by
  unfold vChain; rw [pow_succ', mul_assoc]

omit [Fintype ι] in
theorem le_vChain (W : Submodule ℂ (ι → ℂ)) (a : ℕ) : W ≤ vChain W a := by
  induction a with
  | zero => rw [vChain_zero]
  | succ a ih =>
    intro u hu
    rw [vChain_succ]
    have := Submodule.mul_mem_mul (one_mem_add_one W) (ih hu)
    rwa [one_mul] at this

omit [Fintype ι] in

theorem stab_le_stab_mul (S X : Submodule ℂ (ι → ℂ)) : stab X ≤ stab (S * X) := by
  intro x hx v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    rw [mul_left_comm]
    exact Submodule.mul_mem_mul hs (hx t ht)
  · intro a b ha hb
    rw [mul_add]
    exact Submodule.add_mem _ ha hb

omit [Fintype ι] in
theorem stab_vChain_mono (W : Submodule ℂ (ι → ℂ)) {a b : ℕ} (h : a ≤ b) :
    stab (vChain W a) ≤ stab (vChain W b) := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [vChain_succ]
    exact ih.trans (stab_le_stab_mul _ _)

noncomputable def restrAlg (p : ι → ℂ) : (ι → ℂ) →ₐ[ℂ] ({k // p k = 1} → ℂ) where
  toFun u k := u k
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype ι] in
theorem restrAlg_toLinearMap (p : ι → ℂ) : (restrAlg p).toLinearMap = restr p := rfl

omit [Fintype ι] in

theorem vChain_map (W : Submodule ℂ (ι → ℂ)) (p : ι → ℂ) (a : ℕ) :
    vChain (W.map (restr p)) a = (vChain W a).map (restr p) := by
  unfold vChain
  rw [← restrAlg_toLinearMap, Submodule.map_mul, Submodule.map_pow]
  simp only [Submodule.add_eq_sup, Submodule.map_sup, Submodule.map_one]

theorem restr_perp {W : Submodule ℂ (ι → ℂ)} {a : ℕ}
    (hW : ∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0) {p : ι → ℂ}
    (hp : p ∈ stab (vChain W a)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    ∀ v ∈ vChain (W.map (restr p)) a, ∀ z ∈ W.map (restr p), ∑ i, v i * z i = 0 := by
  intro v hv z hz
  rw [vChain_map] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨z, hz, rfl⟩ := hz
  simp only [restr_apply]
  rw [sum_restr p hp01 (fun k => v k * z k)]
  have := hW _ (hp _ hv) z hz
  simpa only [Pi.mul_apply, mul_assoc] using this

end General

theorem fermat_iter_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) (a : ℕ) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), (∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0) →
        (a + 2) * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; simp
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  have hone : (1 : ι → ℂ) ∉ W := by
    intro h
    have := hW 1 (le_vChain W a h) 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  by_cases hconst : ∀ x ∈ stab (vChain W a), ∀ j k, x j = x k
  ·
    have hSt : ∀ b, b ≤ a → finrank ℂ (stab (vChain W b)) ≤ 1 := by
      intro b hb
      have : stab (vChain W b) ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x (stab_vChain_mono W hb hx) i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hS : W + 1 = W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} := by
      rw [Submodule.add_eq_sup, Submodule.one_eq_span]
    have hU : finrank ℂ ↥(W + 1) = finrank ℂ W + 1 := by
      rw [hS]
      have hinf : W ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxW, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := W.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hUne : W + 1 ≠ ⊥ := by
      intro h
      have := one_mem_add_one W
      rw [h, Submodule.mem_bot] at this
      exact one_ne_zero this
    have hVne : ∀ b, vChain W b ≠ ⊥ := by
      intro b h
      apply hW0
      rw [eq_bot_iff, ← h]
      exact le_vChain W b
    have grow : ∀ b, b ≤ a → (b + 1) * finrank ℂ W ≤ finrank ℂ (vChain W b) := by
      intro b
      induction b with
      | zero => intro _; rw [vChain_zero]; simp
      | succ b ih =>
        intro hb
        have ih' := ih (by omega)
        have hk := hK ι (W + 1) (vChain W b) (stab ((W + 1) * vChain W b)) hUne (hVne b)
          (fun x => Iff.rfl)
        rw [← vChain_succ] at hk
        have hs := hSt (b + 1) hb
        have e : (b + 1 + 1) * finrank ℂ W = (b + 1) * finrank ℂ W + finrank ℂ W := by ring
        rw [e]
        omega
    have hg := grow a le_rfl
    have hp := perp_bound (vChain W a) W hW
    have e : (a + 2) * finrank ℂ W = (a + 1) * finrank ℂ W + finrank ℂ W := by ring
    rw [e]
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab (vChain W a) :=
      (stab (vChain W a)).sub_mem (one_mem_stab (vChain W a)) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_perp hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_perp hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    calc (a + 2) * finrank ℂ W
        ≤ (a + 2) * (finrank ℂ (W.map (restr e)) + finrank ℂ (W.map (restr f))) :=
          Nat.mul_le_mul_left _ h3
      _ = (a + 2) * finrank ℂ (W.map (restr e)) + (a + 2) * finrank ℂ (W.map (restr f)) :=
          Nat.mul_add _ _ _
      _ ≤ n := by omega

theorem fermat_iter_of_kneser
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) :
    ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k →
      (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M := by
  intro M k W hk h
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 2 := ⟨k - 2, by omega⟩
  exact fermat_iter_general (kneserFor_of_fin hK) a M (Fin M) (Fintype.card_fin M) W
    (vChain_perp_of_psum W a h)

end FromGct.Helpers.FermatIter
end SourceFermatIterated

section SourceL067

theorem FromGct.L067 : ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k → (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M :=
  FromGct.Helpers.FermatIter.fermat_iter_of_kneser FromGct.L065
end SourceL067

section SourceLgct306
namespace Moments
open scoped BigOperators
variable {n : Nat}
abbrev Vec (n : Nat) := Fin n → ℂ
abbrev Mat (n : Nat) := Fin 4 → Fin n → ℂ
def dot (a b : Vec n) : ℂ := ∑ j, a j * b j
def mult3 (n : Nat) : ℂ := ((n-3 : Nat) : ℂ)
def mult2 (n : Nat) : ℂ := ((n-2 : Nat) : ℂ) * mult3 n
noncomputable def e0 (n : Nat) : ℂ := ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)

noncomputable def e1 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3))

noncomputable def e2 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
     X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3))

noncomputable def e3 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n,
    (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
     X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3))

noncomputable def e4 (X : Mat n) : ℂ :=
  ∑ f : Fin 4 ↪ Fin n, X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)

lemma poly_expand (X : Mat n) (t : ℂ) :
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) =
      e0 n + t * e1 X + t ^ 2 * e2 X + t ^ 3 * e3 X + t ^ 4 * e4 X := by
  have hterm : ∀ f : Fin 4 ↪ Fin n,
      (∏ i : Fin 4, (1 + (t • X) i (f i))) =
        (1 : ℂ) +
        t * (X 0 (f 0) + X 1 (f 1) + X 2 (f 2) + X 3 (f 3)) +
        t ^ 2 * (X 0 (f 0) * X 1 (f 1) + X 0 (f 0) * X 2 (f 2) + X 0 (f 0) * X 3 (f 3) +
          X 1 (f 1) * X 2 (f 2) + X 1 (f 1) * X 3 (f 3) + X 2 (f 2) * X 3 (f 3)) +
        t ^ 3 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) + X 0 (f 0) * X 1 (f 1) * X 3 (f 3) +
          X 0 (f 0) * X 2 (f 2) * X 3 (f 3) + X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) +
        t ^ 4 * (X 0 (f 0) * X 1 (f 1) * X 2 (f 2) * X 3 (f 3)) := by
    intro f
    rw [Fin.prod_univ_four]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

lemma coeffs_zero_of_const (X : Mat n)
    (h : ∀ t : ℂ, (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + (t • X) i (f i))) = e0 n) :
    e2 X = 0 ∧ e3 X = 0 ∧ e4 X = 0 := by
  have h0 := h 0; rw [poly_expand] at h0
  have h1 := h 1; rw [poly_expand] at h1
  have hm1 := h (-1); rw [poly_expand] at hm1
  have h2 := h 2; rw [poly_expand] at h2
  have hm2 := h (-2); rw [poly_expand] at hm2
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (16 * h1 + 16 * hm1 - h2 - hm2 - 30 * h0) / 24
  · linear_combination (h2 - hm2 - 2 * h1 + 2 * hm1) / 12
  · linear_combination (h2 + hm2 - 4 * h1 - 4 * hm1 + 6 * h0) / 24

def validTuple (t : Fin n × Fin n × Fin n × Fin n) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2.1 ∧ t.1 ≠ t.2.2.2 ∧
  t.2.1 ≠ t.2.2.1 ∧ t.2.1 ≠ t.2.2.2 ∧ t.2.2.1 ≠ t.2.2.2

instance : DecidablePred (validTuple (n:=n)) := fun t => by
  unfold validTuple; infer_instance

lemma sum_emb_eq_nested (g : Fin n → Fin n → Fin n → Fin n → ℂ) :
    (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 := by
  have h1 : (∑ f : Fin 4 ↪ Fin n, g (f 0) (f 1) (f 2) (f 3)) =
      ∑ t ∈ Finset.univ.filter validTuple, g t.1 t.2.1 t.2.2.1 t.2.2.2 := by
    refine Finset.sum_nbij (fun f => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
    · intro f _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, validTuple]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> have := f.injective h <;> omega
    · intro f1 _ f2 _ h
      have h0 : f1 0 = f2 0 := congrArg Prod.fst h
      have h1' : f1 1 = f2 1 := congrArg (fun p => p.2.1) h
      have h2' : f1 2 = f2 2 := congrArg (fun p => p.2.2.1) h
      have h3' : f1 3 = f2 3 := congrArg (fun p => p.2.2.2) h
      exact DFunLike.ext f1 f2 fun i => by fin_cases i <;> assumption
    · intro t ht
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, validTuple] at ht
      rcases t with ⟨j0, j1, j2, j3⟩
      rcases ht with ⟨h01, h02, h03, h12, h13, h23⟩
      refine ⟨⟨![j0, j1, j2, j3], ?_⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [Ne.symm]
    · intro f _
      rfl
  rw [h1]
  rw [Finset.sum_filter]
  simp_rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j0 _ => ?_
  have hf1 : ∀ x : Fin n, (∑ j2 : Fin n, ∑ j3 : Fin n,
      if validTuple (j0, x, j2, j3) then g j0 x j2 j3 else 0) =
      if x ∈ Finset.univ.erase j0 then
        ∑ j2 ∈ (Finset.univ.erase j0).erase x,
          ∑ j3 ∈ ((Finset.univ.erase j0).erase x).erase j2, g j0 x j2 j3
      else 0 := by
    intro j1
    by_cases h01 : j0 = j1
    · subst h01
      simp [validTuple]
    · have hm1 : j1 ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨Ne.symm h01, Finset.mem_univ _⟩
      rw [if_pos hm1]
      trans ∑ j2 : Fin n, if j2 ∈ (Finset.univ.erase j0).erase j1 then
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, g j0 j1 j2 j3 else 0
      · refine Finset.sum_congr rfl fun j2 _ => ?_
        by_cases h2 : j2 ∈ (Finset.univ.erase j0).erase j1
        · rw [if_pos h2]
          have h02 : j0 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase h2))
          have h12 : j1 ≠ j2 := Ne.symm (Finset.ne_of_mem_erase h2)
          rw [← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext j3
          simp [validTuple, h01, h02, h12]; exact ⟨fun ⟨a, b, c⟩ => ⟨Ne.symm c, Ne.symm b, Ne.symm a⟩, fun ⟨c, b, a⟩ => ⟨Ne.symm a, Ne.symm b, Ne.symm c⟩⟩
        · rw [if_neg h2]
          have h2' : j0 = j2 ∨ j1 = j2 := by
            simp only [Finset.mem_erase, Finset.mem_univ, and_true, not_and, not_not] at h2
            by_cases h12 : j2 = j1
            · exact Or.inr h12.symm
            · exact Or.inl (h2 h12).symm
          apply Finset.sum_eq_zero
          intro j3 _
          rcases h2' with rfl | rfl <;> simp [validTuple]
      · rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext j2; simp
  simp_rw [hf1]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext j1; simp

lemma sum_emb_01 (a b : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1)) = -(mult2 n) * dot a b := by
  rw [sum_emb_eq_nested (fun j0 j1 _ _ => a j0 * b j1)]
  have hinner : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) = (mult2 n) * (a j0 * b j1) := by
    intro j0 j1 hj1
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    have hstep : ∀ j2 ∈ ((Finset.univ : Finset (Fin n)).erase j0).erase j1,
        (∑ j3 ∈ (((Finset.univ : Finset (Fin n)).erase j0).erase j1).erase j2, a j0 * b j1) =
          (mult3 n) * (a j0 * b j1) := by
      intro j2 hj2
      rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
      simp [mult3, nsmul_eq_mul, Nat.sub_sub]
    rw [Finset.sum_congr rfl hstep, Finset.sum_const, hcard2]
    simp [mult2,mult3,nsmul_eq_mul,mul_assoc]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => hinner j0 j1 hj1
  rw [h1]
  have h2 : ∀ j0 : Fin n, (∑ j1 ∈ Finset.univ.erase j0, (mult2 n) * (a j0 * b j1)) = -(mult2 n) * (a j0 * b j0) := by
    intro j0
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h2, ← Finset.mul_sum]
  rfl

lemma sum_emb_pair_eq (i1 i2 : Fin 4) (hi : i1 ≠ i2) (a b : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) = -(mult2 n) * dot a b := by
  have hswap : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 := by
    have he : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 := ⟨Equiv.swap 0 i1, by simp⟩
    rcases he with ⟨σ1, hσ1⟩
    have hne : σ1.symm i2 ≠ 0 := by
      intro h
      have := congrArg σ1 h
      rw [Equiv.apply_symm_apply, hσ1] at this
      exact hi this.symm
    refine ⟨σ1 * Equiv.swap 1 (σ1.symm i2), ?_, ?_⟩
    · simp only [Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) hne.symm, hσ1]
    · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
  rcases hswap with ⟨σ, hσ0, hσ1⟩
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1]
  rw [hbij]
  exact sum_emb_01 a b ha hb

lemma e2_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) (hc : ∀ j, ∑ i, X i j = 0) :
    e2 X = (mult2 n / 2) * (dot (X 0) (X 0) + dot (X 1) (X 1) + dot (X 2) (X 2) + dot (X 3) (X 3)) := by
  unfold e2
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_pair_eq 0 1 (by decide) (X 0) (X 1) (hr 0) (hr 1),
      sum_emb_pair_eq 0 2 (by decide) (X 0) (X 2) (hr 0) (hr 2),
      sum_emb_pair_eq 0 3 (by decide) (X 0) (X 3) (hr 0) (hr 3),
      sum_emb_pair_eq 1 2 (by decide) (X 1) (X 2) (hr 1) (hr 2),
      sum_emb_pair_eq 1 3 (by decide) (X 1) (X 3) (hr 1) (hr 3),
      sum_emb_pair_eq 2 3 (by decide) (X 2) (X 3) (hr 2) (hr 3)]
  have hsq : ∑ j : Fin n, (X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj := hc j
    rw [Fin.sum_univ_four] at hj
    rw [hj]; ring
  unfold dot
  have hcomb : ∑ j : Fin n,
      ((X 0 j + X 1 j + X 2 j + X 3 j) ^ 2 -
       (X 0 j * X 0 j + X 1 j * X 1 j + X 2 j * X 2 j + X 3 j * X 3 j) -
       2 * (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j +
            X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) = 0 := by
    apply Finset.sum_eq_zero; intro j _; ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hcomb
  linear_combination (mult2 n / 2) * hcomb - (mult2 n / 2) * hsq

lemma sum_emb_012 (a b c : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2)) = (2 * mult3 n) * ∑ j, a j * b j * c j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 _ => a j0 * b j1 * c j2)]
  have hstep3 : ∀ (j0 : Fin n) (j1 : Fin n) (j2 : Fin n),
      j1 ∈ Finset.univ.erase j0 → j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
        (mult3 n) * (a j0 * b j1 * c j2) := by
    intro j0 j1 j2 hj1 hj2
    have hcard1 : ((Finset.univ : Finset (Fin n)).erase j0).card = n-1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _)]; simp
    have hcard2 : (((Finset.univ : Finset (Fin n)).erase j0).erase j1).card = n-2 := by
      rw [Finset.card_erase_of_mem hj1, hcard1]
      omega
    rw [Finset.sum_const, Finset.card_erase_of_mem hj2, hcard2]
    simp [mult3,nsmul_eq_mul,Nat.sub_sub]
  have h1 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ _j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => hstep3 j0 j1 j2 hj1 hj2
  rw [h1]
  have h2 : ∀ (j0 : Fin n) (j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2)) =
        (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) := by
    intro j0 j1 hj1
    have : ∀ j2, (mult3 n) * (a j0 * b j1 * c j2) = ((mult3 n) * a j0 * b j1) * c j2 := fun _ => by ring
    simp_rw [this, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc]
    ring
  have h3 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, (mult3 n) * (a j0 * b j1 * c j2)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [h3]
  have h4 : ∀ j0 : Fin n,
      (∑ j1 ∈ Finset.univ.erase j0, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1))) =
        (2 * mult3 n) * (a j0 * b j0 * c j0) - (mult3 n) * a j0 * (∑ j1, b j1 * c j1) := by
    intro j0
    have hsplit : ∀ j1, (mult3 n) * (a j0 * b j1 * (- c j0 - c j1)) =
        (-(mult3 n) * a j0 * c j0) * b j1 - ((mult3 n) * a j0) * (b j1 * c j1) := fun _ => by ring
    simp_rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb]
    ring
  simp_rw [h4, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [ha]; ring

lemma sum_emb_triple_eq (i1 i2 i3 : Fin 4) (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3)
    (a b c : Vec n) (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2) * c (f i3)) = (2 * mult3 n) * ∑ j, a j * b j * c j := by
  have hperm : ∃ σ : Equiv.Perm (Fin 4), σ 0 = i1 ∧ σ 1 = i2 ∧ σ 2 = i3 := by
    have hi4 : ∃ i4 : Fin 4, i4 ≠ i1 ∧ i4 ≠ i2 ∧ i4 ≠ i3 := by
      fin_cases i1 <;> fin_cases i2 <;> fin_cases i3 <;> simp_all <;> decide
    rcases hi4 with ⟨i4, h41, h42, h43⟩
    have hinj : Function.Injective ![i1, i2, i3, i4] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [Ne.symm]
    refine ⟨Equiv.ofBijective ![i1, i2, i3, i4] (Finite.injective_iff_bijective.mp hinj), rfl, rfl, rfl⟩
  rcases hperm with ⟨σ, hσ0, hσ1, hσ2⟩
  have hbij : (∑ f : Fin 4 ↪ Fin n, a (f i1) * b (f i2) * c (f i3)) =
      ∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2) := by
    refine Finset.sum_nbij (fun f => σ.toEmbedding.trans f) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro f1 _ f2 _ h
      exact DFunLike.ext f1 f2 fun x => by
        have := DFunLike.congr_fun h (σ.symm x)
        simpa using this
    · intro f _
      refine ⟨σ.symm.toEmbedding.trans f, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      exact DFunLike.ext _ _ fun x => by simp
    · intro f _
      simp [hσ0, hσ1, hσ2]
  rw [hbij]
  exact sum_emb_012 a b c ha hb hc

lemma e3_eq (X : Mat n) (hr : ∀ i, ∑ j, X i j = 0) :
    e3 X = (2 * mult3 n) * ∑ j, (X 0 j * X 1 j * X 2 j + X 0 j * X 1 j * X 3 j +
      X 0 j * X 2 j * X 3 j + X 1 j * X 2 j * X 3 j) := by
  unfold e3
  simp_rw [Finset.sum_add_distrib]
  rw [sum_emb_triple_eq 0 1 2 (by decide) (by decide) (by decide) (X 0) (X 1) (X 2) (hr 0) (hr 1) (hr 2),
      sum_emb_triple_eq 0 1 3 (by decide) (by decide) (by decide) (X 0) (X 1) (X 3) (hr 0) (hr 1) (hr 3),
      sum_emb_triple_eq 0 2 3 (by decide) (by decide) (by decide) (X 0) (X 2) (X 3) (hr 0) (hr 2) (hr 3),
      sum_emb_triple_eq 1 2 3 (by decide) (by decide) (by decide) (X 1) (X 2) (X 3) (hr 1) (hr 2) (hr 3)]
  ring

lemma e4_eq (a b c d : Vec n)
    (ha : ∑ j, a j = 0) (hb : ∑ j, b j = 0) (hc : ∑ j, c j = 0) (hd : ∑ j, d j = 0) :
    (∑ f : Fin 4 ↪ Fin n, a (f 0) * b (f 1) * c (f 2) * d (f 3)) =
      dot a b * dot c d + dot a c * dot b d + dot a d * dot b c -
        6 * ∑ j, a j * b j * c j * d j := by
  rw [sum_emb_eq_nested (fun j0 j1 j2 j3 => a j0 * b j1 * c j2 * d j3)]
  have h3 : ∀ (j0 j1 j2 : Fin n), j1 ∈ Finset.univ.erase j0 →
      j2 ∈ (Finset.univ.erase j0).erase j1 →
      (∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
        a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) := by
    intro j0 j1 j2 hj1 hj2
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub hj2, Finset.sum_erase_eq_sub hj1,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0), hd]
    ring
  have hs3 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1,
        ∑ j3 ∈ ((Finset.univ.erase j0).erase j1).erase j2, a j0 * b j1 * c j2 * d j3) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) :=
    Finset.sum_congr rfl fun j0 _ =>
      Finset.sum_congr rfl fun j1 hj1 =>
        Finset.sum_congr rfl fun j2 hj2 => h3 j0 j1 j2 hj1 hj2
  rw [hs3]
  have h2 : ∀ (j0 j1 : Fin n), j1 ∈ Finset.univ.erase j0 →
      (∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) := by
    intro j0 j1 hj1
    have hsp : ∀ j2, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2) =
        (a j0 * b j1 * (- d j0 - d j1)) * c j2 - (a j0 * b j1) * (c j2 * d j2) := fun _ => by ring
    simp_rw [hsp, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0), hc,
        Finset.sum_erase_eq_sub hj1, Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  have hs2 : (∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
      ∑ j2 ∈ (Finset.univ.erase j0).erase j1, a j0 * b j1 * c j2 * (- d j0 - d j1 - d j2)) =
      ∑ j0 : Fin n, ∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) :=
    Finset.sum_congr rfl fun j0 _ => Finset.sum_congr rfl fun j1 hj1 => h2 j0 j1 hj1
  rw [hs2]
  have h1 : ∀ j0 : Fin n,
      (∑ j1 ∈ Finset.univ.erase j0,
        a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1)) =
        a j0 * (dot b c * d j0 + dot b d * c j0 + b j0 * dot c d +
          2 * (∑ j1, b j1 * c j1 * d j1) - 6 * b j0 * c j0 * d j0) := by
    intro j0
    have hsp : ∀ j1, a j0 * b j1 * ((d j0 + d j1) * (c j0 + c j1) - dot c d + c j0 * d j0 + c j1 * d j1) =
        (a j0 * (2 * c j0 * d j0 - dot c d)) * b j1 +
        (a j0 * d j0) * (b j1 * c j1) +
        (a j0 * c j0) * (b j1 * d j1) +
        (2 * a j0) * (b j1 * c j1 * d j1) := fun _ => by ring
    simp_rw [hsp, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ j0), hb,
        Finset.sum_erase_eq_sub (Finset.mem_univ j0),
        Finset.sum_erase_eq_sub (Finset.mem_univ j0),
        Finset.sum_erase_eq_sub (Finset.mem_univ j0)]
    unfold dot; ring
  simp_rw [h1]
  have h0sp : ∀ j0, a j0 * (dot b c * d j0 + dot b d * c j0 + b j0 * dot c d +
      2 * (∑ j1, b j1 * c j1 * d j1) - 6 * b j0 * c j0 * d j0) =
      dot b c * (a j0 * d j0) + dot b d * (a j0 * c j0) + dot c d * (a j0 * b j0) +
      (2 * ∑ j1, b j1 * c j1 * d j1) * a j0 - 6 * (a j0 * b j0 * c j0 * d j0) := fun _ => by ring
  simp_rw [h0sp, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ha]
  unfold dot; ring

end Moments

namespace Moments
open scoped BigOperators
variable {n : Nat}

def Level (L : Submodule ℂ (Mat n)) :=
  ∀ X ∈ L, (∀ i, (∑ j, X i j)=0) ∧ (∀ j, (∑ i, X i j)=0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1+X i (f i))) = e0 n

def sqSum (X : Mat n) : ℂ := ∑ j, ((X 0 j)^2 + (X 1 j)^2 + (X 2 j)^2 + (X 3 j)^2)
def cubeSum (X : Mat n) : ℂ := ∑ j, ((X 0 j)^3 + (X 1 j)^3 + (X 2 j)^3 + (X 3 j)^3)
def ringProd (X : Mat n) : ℂ := ∑ j, X 0 j * X 1 j * X 2 j * X 3 j
def pairs (X : Mat n) : ℂ := dot (X 0) (X 1) * dot (X 2) (X 3) +
  dot (X 0) (X 2) * dot (X 1) (X 3) + dot (X 0) (X 3) * dot (X 1) (X 2)

theorem forms (hn : 4≤n) {L : Submodule ℂ (Mat n)} (valid : Level L) {X : Mat n} (mem : X∈L) :
    sqSum X=0 ∧ cubeSum X=0 ∧ pairs X=6*ringProd X := by
  obtain ⟨row,col,_⟩ := valid X mem
  obtain ⟨q,c,k⟩ := coeffs_zero_of_const X (fun t => (valid _ (L.smul_mem t mem)).2.2)
  have nz : mult3 n ≠ 0 := by unfold mult3; exact_mod_cast (show n-3≠0 by omega)
  have nz2 : mult2 n ≠ 0 := by unfold mult2; exact mul_ne_zero (by exact_mod_cast (show n-2≠0 by omega)) nz
  rw [e2_eq X row col] at q
  rw [e3_eq X row] at c
  have sqz := (mul_eq_zero.mp q).resolve_left (div_ne_zero nz2 (by norm_num))
  have cub := (mul_eq_zero.mp c).resolve_left (mul_ne_zero (by norm_num) nz)
  refine ⟨?_,?_,?_⟩
  · simpa [dot,sqSum,Finset.sum_add_distrib,pow_two] using sqz
  · have point (j : Fin n) :
        (X 0 j)^3+(X 1 j)^3+(X 2 j)^3+(X 3 j)^3 =
        3*(X 0 j*X 1 j*X 2 j+X 0 j*X 1 j*X 3 j+X 0 j*X 2 j*X 3 j+X 1 j*X 2 j*X 3 j) := by
      have h := col j
      rw [Fin.sum_univ_four] at h
      linear_combination ((X 0 j)^2+(X 1 j)^2+(X 2 j)^2+(X 3 j)^2 -
        (X 0 j * X 1 j + X 0 j * X 2 j + X 0 j * X 3 j + X 1 j * X 2 j + X 1 j * X 3 j + X 2 j * X 3 j)) * h
    simp only [cubeSum,point,← Finset.mul_sum,cub,mul_zero]
  · change (∑ f : Fin 4 ↪ Fin n, X 0 (f 0)*X 1 (f 1)*X 2 (f 2)*X 3 (f 3)) = 0 at k
    rw [e4_eq (X 0) (X 1) (X 2) (X 3) (row 0) (row 1) (row 2) (row 3)] at k
    exact sub_eq_zero.mp k

end Moments
end SourceLgct306

section SourceLgct309

namespace RankModel.PivotCore

variable {K S W : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S]

structure Pivot (K S W : Type*) [Field K] [AddCommGroup S] [Module K S] where
  p : S →ₗ[K] K
  q : S →ₗ[K] K
  a : S →ₗ[K] K
  b : S →ₗ[K] K
  c : S →ₗ[K] K
  d : S →ₗ[K] K
  u : W → S →ₗ[K] K
  v : W → S →ₗ[K] K
  quad : ∀ s w, p s * u w s + q s * v w s = 0
  cubic : ∀ s w, p s * (a s * u w s + b s * v w s) +
    q s * (c s * u w s + d s * v w s) = 0

namespace Pivot

def det3 (a b u c d v p q z : K) : K :=
  a * (d*z-v*q) - b * (c*z-v*p) + u * (c*q-d*p)

theorem detData (a b u c d v p q z : K)
    (h : det3 a b u c d v p q z = 0)
    (hp : det3 (1+a) b u c (1+d) v p q z = 0)
    (hm : det3 (1-a) (-b) (-u) (-c) (1-d) (-v) (-p) (-q) (-z) = 0) :
    z = 0 ∧ p*u+q*v = 0 ∧
      p*(a*u+b*v)+q*(c*u+d*v) = 0 := by
  simp only [det3] at h hp hm
  have h₂ : (2:K) ≠ 0 := (OfNat.ofNat_ne_zero 2)
  have e : (2:K)*z = 0 := by
    linear_combination hp - hm - 2*h
  have hz : z = 0 := (mul_eq_zero.mp e).resolve_left h₂
  rw [hz] at h hp hm
  have e' : (2:K)*(p*u+q*v) = 0 := by
    linear_combination -hp - hm
  have hq : p*u+q*v = 0 := (mul_eq_zero.mp e').resolve_left h₂
  refine ⟨hz,hq,?_⟩
  linear_combination h + (a+d)*hq

variable (P : Pivot K S W)

theorem polar (x y : S) (w : W) :
    P.p x * P.u w y + P.q x * P.v w y +
      (P.p y * P.u w x + P.q y * P.v w x) = 0 := by
  have hh := P.quad (x+y) w
  simp only [map_add] at hh
  linear_combination hh - P.quad x w - P.quad y w

theorem inLine {p q x y : K} (hn : p ≠ 0 ∨ q ≠ 0) (hh : p*y=q*x) :
    ∃ t : K, x=t*p ∧ y=t*q := by
  by_cases hp : p=0
  · have hq : q≠0 := hn.resolve_left (fun e => e hp)
    have hqx : q*x=0 := by simpa [hp] using hh.symm
    have hx : x=0 := (mul_eq_zero.mp hqx).resolve_left hq
    refine ⟨y/q, by simp [hx,hp], ?_⟩
    exact (div_mul_cancel₀ y hq).symm
  · refine ⟨x/p, (div_mul_cancel₀ x hp).symm, ?_⟩
    have h₀ : (x/p*q-y)*p = 0 := by
      linear_combination q * (div_mul_cancel₀ x hp) - hh
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h₀).resolve_right hp)).symm

private theorem hasBoth (F G : S →ₗ[K] K)
    (hf : ∃ x, F x ≠ 0) (hg : ∃ x, G x ≠ 0) :
    ∃ x, F x ≠ 0 ∧ G x ≠ 0 := by
  obtain ⟨x,hx⟩ := hf
  obtain ⟨y,hy⟩ := hg
  by_cases hGx : G x = 0
  · by_cases hFy : F y = 0
    · exact ⟨x+y, by simpa [map_add,hFy] using hx, by simpa [map_add,hGx] using hy⟩
    · exact ⟨y,hFy,hy⟩
  · exact ⟨x,hx,hGx⟩

theorem vanishesOffTwo (F G H : S →ₗ[K] K)
    (hf : ∃ x, F x ≠ 0) (hg : ∃ x, G x ≠ 0)
    (h : ∀ x, F x ≠ 0 → G x ≠ 0 → H x = 0) :
    ∀ x, H x = 0 := by
  obtain ⟨y,hfY,hgY⟩ := hasBoth F G hf hg
  have hy : H y = 0 := h y hfY hgY
  have prod : ∀ x, H x ≠ 0 → F x * G x = 0 := by
    intro x hx
    by_cases hxF : F x = 0
    · simp [hxF]
    by_cases hxG : G x = 0
    · simp [hxG]
    exact (hx (h x hxF hxG)).elim
  intro x
  by_contra hx
  have hx0 := prod x hx
  have hxp := prod (x+y) (by simpa [map_add,hy] using hx)
  have hxm := prod (x-y) (by simpa [map_sub,hy] using hx)
  simp only [map_add,map_sub] at hxp hxm
  have hz : (2:K) * (F y * G y) = 0 := by
    linear_combination hxp + hxm - 2 * hx0
  exact (mul_ne_zero ((OfNat.ofNat_ne_zero 2)) (mul_ne_zero hfY hgY)) hz

def PureImage : Prop := ∀ x, P.p x = 0 ∧ P.q x = 0
def PureKernel : Prop := ∀ x w, P.u w x = 0 ∧ P.v w x = 0

def form (z : S) : S →ₗ[K] K :=
  P.p z • (P.q z • P.a - P.p z • P.b) +
    P.q z • (P.q z • P.c - P.p z • P.d)

theorem form_apply (z x : S) :
    P.form z x = P.p z * (P.a x * P.q z - P.b x * P.p z) +
      P.q z * (P.c x * P.q z - P.d x * P.p z) := by
  simp only [form,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  ring1

def Mixed : Prop := ∃ z, (P.p z ≠ 0 ∨ P.q z ≠ 0) ∧
    (∀ x, P.p z * P.q x = P.q z * P.p x) ∧
    (∀ x w, P.p z * P.u w x + P.q z * P.v w x = 0) ∧
    (∀ x, P.form z x = 0)

private theorem oneDirection (z : S) (hz : P.p z ≠ 0 ∨ P.q z ≠ 0)
    (line : ∀ x, P.p z * P.q x = P.q z * P.p x)
    (hC : ¬ P.PureKernel) : P.Mixed := by
  classical
  have bline : ∀ x, ∃ t : K, P.p x=t*P.p z ∧ P.q x=t*P.q z :=
    fun x => inLine hz (line x)
  have orth : ∀ x w, P.p z * P.u w x + P.q z * P.v w x = 0 := by
    intro x w
    obtain ⟨t,hp,hq⟩ := bline x
    have hh := P.polar z x w
    rw [hp,hq] at hh
    linear_combination hh - t * P.quad z w
  have cline : ∀ x w, ∃ t : K, P.u w x=t*P.q z ∧ P.v w x=t*(-P.p z) := by
    intro x w
    apply inLine
    · rcases hz with hz|hz
      · exact Or.inr (neg_ne_zero.mpr hz)
      · exact Or.inl hz
    · linear_combination orth x w
  have hc : ∃ w, (∃ x, P.u w x ≠ 0) ∨ (∃ x, P.v w x ≠ 0) := by
    classical
    by_contra h
    apply hC
    intro x w
    exact ⟨by by_contra e; exact h ⟨w, Or.inl ⟨x,e⟩⟩,
      by by_contra e; exact h ⟨w, Or.inr ⟨x,e⟩⟩⟩
  obtain ⟨w,hw⟩ := hc
  let F : S →ₗ[K] K := if P.p z = 0 then P.q else P.p
  let G : S →ₗ[K] K := if ∃ x, P.u w x ≠ 0 then P.u w else P.v w
  have hf : ∃ x, F x ≠ 0 := by
    refine ⟨z,?_⟩
    rcases eq_or_ne (P.p z) 0 with h|h
    · simpa [F,h] using hz.resolve_left (fun e => e h)
    · simpa [F,h] using h
  have hg : ∃ x, G x ≠ 0 := by
    by_cases h : ∃ x, P.u w x ≠ 0
    · simpa [G,h] using h
    · simpa [G,h] using hw.resolve_left h
  refine ⟨z,hz,line,orth,vanishesOffTwo F G (P.form z) hf hg ?_⟩
  intro x hFx hGx
  obtain ⟨r,hp,hq⟩ := bline x
  obtain ⟨t,hu,hv⟩ := cline x w
  have hr : r ≠ 0 := by
    intro h
    have e₀ : P.p x = 0 := by simp [hp,h]
    have e₁ : P.q x = 0 := by simp [hq,h]
    apply hFx
    by_cases hF : P.p z = 0 <;> simp [F,hF,e₀,e₁]
  have ht : t ≠ 0 := by
    intro h
    have e₀ : P.u w x = 0 := by simp [hu,h]
    have e₁ : P.v w x = 0 := by simp [hv,h]
    apply hGx
    by_cases hG : ∃ u, P.u w u ≠ 0 <;> simp [G,hG,e₀,e₁]
  have hpv := P.cubic x w
  rw [hp,hq,hu,hv] at hpv
  have hz' : (r*t)*P.form z x = 0 := by
    rw [P.form_apply]
    linear_combination hpv
  exact (mul_eq_zero.mp hz').resolve_left (mul_ne_zero hr ht)

def Faithful : Prop := ∀ x, P.p x = 0 → P.q x = 0 →
    P.a x = 0 → P.b x = 0 → P.c x = 0 → P.d x = 0 →
    (∀ w, P.u w x = 0 ∧ P.v w x = 0) → x = 0

def Small : Prop := ∀ x, P.p x = 0 → P.q x = 0 → P.a x = 0 → x = 0

private theorem twoDirections (x₀ x₁ : S)
    (hp₀ : P.p x₀ = 1) (hq₀ : P.q x₀ = 0)
    (hp₁ : P.p x₁ = 0) (hq₁ : P.q x₁ = 1)
    (hf : P.Faithful) (hC : ¬ P.PureKernel) :
    P.Small := by
  have onKernel : ∀ x, P.p x=0 → P.q x=0 → ∀ w, P.u w x=0 ∧ P.v w x=0 := by
    intro x hp hq w
    constructor
    · simpa [hp,hq,hp₀,hq₀] using P.polar x x₀ w
    · simpa [hp,hq,hp₁,hq₁] using P.polar x x₁ w
  have sy : ∀ w, P.u w x₁ = -(P.v w x₀) := by
    intro w
    have h := P.polar x₀ x₁ w
    simp only [hp₀,hq₀,hp₁,hq₁, one_mul,zero_mul,add_zero,zero_add] at h
    linear_combination h
  have xu : ∀ w, P.u w x₀ = 0 := by
    intro w
    simpa [hp₀,hq₀] using P.quad x₀ w
  have xv : ∀ w, P.v w x₁ = 0 := by
    intro w
    simpa [hp₁,hq₁] using P.quad x₁ w
  have express : ∀ x w, P.u w x = -P.q x * P.v w x₀ ∧ P.v w x = P.p x * P.v w x₀ := by
    intro x w
    have h := P.polar x x₀ w
    have h' := P.polar x x₁ w
    simp only [hp₀,hq₀,xu w, one_mul,zero_mul,add_zero,zero_add] at h
    simp only [hp₁,hq₁,xv w,sy w,one_mul,zero_mul,add_zero,zero_add] at h'
    refine ⟨?_,?_⟩
    · linear_combination h
    · linear_combination h'
  have hn : ∃ w, P.v w x₀ ≠ 0 := by
    classical
    by_contra hh
    apply hC
    intro x w
    have hz : P.v w x₀ = 0 := by
      by_contra hz'
      exact hh ⟨w,hz'⟩
    have h := express x w
    simpa [hz] using h
  obtain ⟨w,hw⟩ := hn
  have reduced : ∀ x, P.p x * (-P.a x * P.q x + P.b x * P.p x) +
      P.q x * (-P.c x * P.q x + P.d x * P.p x) = 0 := by
    intro x
    have h := P.cubic x w
    rw [(express x w).1,(express x w).2] at h
    have hz : (P.p x * (-P.a x * P.q x + P.b x * P.p x) +
      P.q x * (-P.c x * P.q x + P.d x * P.p x)) * P.v w x₀ = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hz).resolve_right hw
  intro x hp hq ha
  have hx₀ := reduced (x₀+x)
  have hx₁ := reduced (x₁+x)
  have h₀ := reduced x₀
  have h₁ := reduced x₁
  simp only [map_add,hp,hq,hp₀,hq₀,hp₁,hq₁, add_zero, mul_one,zero_mul,mul_zero,
    one_mul,zero_add,neg_zero] at hx₀ hx₁ h₀ h₁
  have hb : P.b x = 0 := by linear_combination hx₀ - h₀
  have hc : P.c x = 0 := by linear_combination h₁ - hx₁
  have hxy := reduced (x₀+x₁+x)
  have hy := reduced (x₀+x₁)
  simp only [map_add,hp,hq,hp₀,hq₀,hp₁,hq₁,ha,hb,hc, add_zero,zero_add,
    mul_one,zero_mul,mul_zero,one_mul,neg_zero] at hxy hy
  have hd : P.d x = 0 := by linear_combination hxy - hy
  exact hf x hp hq ha hb hc hd (onKernel x hp hq)

theorem classify (hf : P.Faithful) :
    P.PureImage ∨ P.PureKernel ∨ P.Mixed ∨ P.Small := by
  classical
  by_cases hB : P.PureImage
  · exact Or.inl hB
  by_cases hC : P.PureKernel
  · exact Or.inr (Or.inl hC)
  have hZ : ∃ z, P.p z ≠ 0 ∨ P.q z ≠ 0 := by
    by_contra h
    apply hB
    intro z
    exact ⟨by by_contra h'; exact h ⟨z,Or.inl h'⟩,
      by by_contra h'; exact h ⟨z,Or.inr h'⟩⟩
  obtain ⟨z,hz⟩ := hZ
  by_cases hLine : ∀ x, P.p z * P.q x = P.q z * P.p x
  · exact Or.inr (Or.inr (Or.inl (P.oneDirection z hz hLine hC)))
  obtain ⟨y,hy⟩ := not_forall.mp hLine
  let Δ := P.p z * P.q y - P.q z * P.p y
  have hΔ : Δ ≠ 0 := sub_ne_zero.mpr hy
  let x₀ := Δ⁻¹ • (P.q y • z - P.q z • y)
  let x₁ := Δ⁻¹ • (P.p z • y - P.p y • z)
  have hp₀ : P.p x₀ = 1 := by
    simp only [x₀,map_sub,map_smul,smul_eq_mul]
    rw [show P.q y * P.p z - P.q z * P.p y = Δ by unfold Δ; ring1]
    exact inv_mul_cancel₀ hΔ
  have hq₀ : P.q x₀ = 0 := by
    simp only [x₀,map_sub,map_smul,smul_eq_mul]
    ring1
  have hp₁ : P.p x₁ = 0 := by
    simp only [x₁,map_sub,map_smul,smul_eq_mul]
    ring1
  have hq₁ : P.q x₁ = 1 := by
    simp only [x₁,map_sub,map_smul,smul_eq_mul]
    rw [show P.p z * P.q y - P.p y * P.q z = Δ by unfold Δ; ring1]
    exact inv_mul_cancel₀ hΔ
  exact Or.inr (Or.inr (Or.inr (P.twoDirections x₀ x₁ hp₀ hq₀ hp₁ hq₁ hf hC)))

end Pivot
end RankModel.PivotCore

open Module
open scoped BigOperators

namespace RankModel.PivotCore

variable {K S D : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S] [AddCommGroup D] [Module K D]

abbrev Target (K : Type*) := Fin 3 → K

def evalSlot (T : S →ₗ[K] D →ₗ[K] Target K) (i : Fin 3) (x : D) : S →ₗ[K] K where
  toFun s := T s x i
  map_add' s t := by simp only [map_add,LinearMap.add_apply,Pi.add_apply]
  map_smul' r s := by simp only [map_smul,LinearMap.smul_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]

@[simp] theorem evalSlot_apply (T : S →ₗ[K] D →ₗ[K] Target K)
    (i : Fin 3) (x : D) (s : S) : evalSlot T i x s = T s x i := rfl

def coord (T : D →ₗ[K] Target K) (i : Fin 3) : D →ₗ[K] K :=
  (LinearMap.proj i).comp T

@[simp] theorem coord_apply (T : D →ₗ[K] Target K) (i : Fin 3) (x : D) :
    coord T i x = T x i := rfl

theorem cutDet (A : D →ₗ[K] Target K) (hA : finrank K (LinearMap.range A) ≤ 2)
    (cols : Fin 3 → D) : (Matrix.of fun (i j : Fin 3) => A (cols j) i).det = 0 := by
  classical
  let M : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => A (cols j) i
  change M.det = 0
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.range A := by
    rintro _ ⟨x,rfl⟩
    refine ⟨∑ j, x j • cols j, ?_⟩
    ext i
    simp only [map_sum,map_smul,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,
      Finset.sum_apply,Pi.smul_apply,smul_eq_mul,M,Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hr : M.rank ≤ 2 := (Submodule.finrank_mono hle).trans hA
  by_contra hd
  have h3 := Matrix.rank_of_det_ne_zero hd
  rw [Fintype.card_fin] at h3
  omega

structure Normalized (K S D : Type*) [Field K] [AddCommGroup S] [Module K S]
    [AddCommGroup D] [Module K D] where
  T : S →ₗ[K] D →ₗ[K] Target K
  faithful : Function.Injective T
  rank : ∀ s, finrank K (LinearMap.range (T s)) ≤ 2
  center : D
  vanishes : ∀ s, T s center = 0
  chosen : S
  x0 : D
  x1 : D
  at0 : T chosen x0 = ![1,0,0]
  at1 : T chosen x1 = ![0,1,0]
  at2 : ∀ x, T chosen x 2 = 0

variable {V : Type*} [AddCommGroup V] [Module K V]

def FixedImage (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ a b : V, LinearIndependent K ![a,b] ∧
    ∀ s, ∃ f g : D →ₗ[K] K, f center = 0 ∧ g center = 0 ∧
      ∀ x, T s x = f x • a + g x • b

def FixedKernel (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ f g : D →ₗ[K] K, f center = 0 ∧ g center = 0 ∧ LinearIndependent K ![f,g] ∧
    ∀ s, ∃ a b : V, ∀ x, T s x = f x • a + g x • b

def FixedLine (T : S →ₗ[K] D →ₗ[K] V) (center : D) : Prop :=
  ∃ (a : V) (b : D →ₗ[K] K), a ≠ 0 ∧ b ≠ 0 ∧ b center = 0 ∧
    ∀ s, ∃ (f : D →ₗ[K] K) (y : V), f center = 0 ∧
      ∀ x, T s x = f x • a + b x • y

def ThreeShapes (T : S →ₗ[K] D →ₗ[K] V) (center : D) :=
  FixedImage T center ∨ FixedKernel T center ∨ FixedLine T center

theorem fixedLine_of_restrict (T : S →ₗ[K] D →ₗ[K] V) {center : D}
    (hCenter : ∀ s, T s center = 0)
    (a : V) (b : D →ₗ[K] K) (e : V →ₗ[K] K) (v : D)
    (ha : e a = 1) (hb : b v = 1) (hzero : b center = 0)
    (h : ∀ s x, b x = 0 → ∃ t : K, T s x = t • a) :
    FixedLine T center := by
  have hane : a ≠ 0 := by intro hz; simp [hz] at ha
  have hbne : b ≠ 0 := by intro hz; simp [hz] at hb
  refine ⟨a,b,hane,hbne,hzero,?_⟩
  intro s
  let M : D →ₗ[K] V := T s - b.smulRight (T s v)
  refine ⟨e.comp M, T s v, ?_, ?_⟩
  · simp [M,hCenter s,hzero,LinearMap.smulRight_apply]
  intro x
  let w := x - b x • v
  have hw : b w = 0 := by simp [w,hb,map_sub,map_smul,smul_eq_mul]
  obtain ⟨t,ht⟩ := h s w hw
  have hM : M x = t • a := by
    simpa [M,w,map_sub,map_smul,LinearMap.smulRight_apply] using ht
  change T s x = e (M x) • a + b x • T s v
  rw [hM, map_smul, ha, smul_eq_mul, mul_one, ← hM]
  simp [M,LinearMap.smulRight_apply]

namespace Normalized

variable (N : Normalized K S D)

abbrev Tail := LinearMap.ker (N.T N.chosen)
abbrev r0 := coord (N.T N.chosen) 0
abbrev r1 := coord (N.T N.chosen) 1

def tailPart (x : D) : N.Tail := ⟨x - N.r0 x • N.x0 - N.r1 x • N.x1, by
  rw [LinearMap.mem_ker]
  ext i
  fin_cases i <;>
    simp [r0,r1,map_sub,map_smul,Pi.sub_apply,smul_eq_mul,N.at0,N.at1,N.at2,
      Matrix.vecHead,Matrix.vecTail,Fin.succ_zero_eq_one]⟩

theorem split (x : D) : x = N.r0 x • N.x0 + N.r1 x • N.x1 + (N.tailPart x : D) := by
  change x = _ + _ + (x - _ - _)
  abel

theorem cutStencil (s : S) (w : N.Tail) :
    N.T s (w : D) 2 = 0 ∧
    N.T s N.x0 2 * N.T s (w : D) 0 + N.T s N.x1 2 * N.T s (w : D) 1 = 0 ∧
    N.T s N.x0 2 * (N.T s N.x0 0 * N.T s (w : D) 0 + N.T s N.x1 0 * N.T s (w : D) 1) +
    N.T s N.x1 2 * (N.T s N.x0 1 * N.T s (w : D) 0 + N.T s N.x1 1 * N.T s (w : D) 1) = 0 := by
  let cols : Fin 3 → D := ![N.x0,N.x1,(w : D)]
  let a := N.T s N.x0 0
  let b := N.T s N.x1 0
  let u := N.T s (w : D) 0
  let c := N.T s N.x0 1
  let d := N.T s N.x1 1
  let v := N.T s (w : D) 1
  let p := N.T s N.x0 2
  let q := N.T s N.x1 2
  let z := N.T s (w : D) 2
  have unfoldDet (t : S) :
      (Matrix.of fun (i j : Fin 3) => N.T t (cols j) i).det =
      Pivot.det3 (N.T t N.x0 0) (N.T t N.x1 0) (N.T t (w : D) 0)
        (N.T t N.x0 1) (N.T t N.x1 1) (N.T t (w : D) 1)
        (N.T t N.x0 2) (N.T t N.x1 2) (N.T t (w : D) 2) := by
    rw [Matrix.det_fin_three]
    simp only [cols,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      Pivot.det3]
    ring1
  have h (t : S) := (unfoldDet t).symm.trans (cutDet (N.T t) (N.rank t) cols)
  have hw : N.T N.chosen (w : D) = 0 := w.property
  have hp := h (N.chosen+s)
  have hm := h (N.chosen-s)
  simp only [map_add,LinearMap.add_apply,Pi.add_apply,N.at0,N.at1,hw,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,zero_add] at hp
  simp only [map_sub,LinearMap.sub_apply,Pi.sub_apply,N.at0,N.at1,hw,Pi.zero_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,zero_sub] at hm
  exact Pivot.detData a b u c d v p q z (h s) hp hm

def pivot : Pivot K S N.Tail where
  p := evalSlot N.T 2 N.x0
  q := evalSlot N.T 2 N.x1
  a := evalSlot N.T 0 N.x0
  b := evalSlot N.T 0 N.x1
  c := evalSlot N.T 1 N.x0
  d := evalSlot N.T 1 N.x1
  u w := evalSlot N.T 0 w
  v w := evalSlot N.T 1 w
  quad s w := (N.cutStencil s w).2.1
  cubic s w := (N.cutStencil s w).2.2

theorem pivot_faithful : N.pivot.Faithful := by
  intro s hp hq ha hb hc hd ht
  apply N.faithful
  rw [map_zero]
  ext x i
  have h0 : N.T s N.x0 = 0 := by
    ext i
    fin_cases i
    · exact ha
    · exact hc
    · exact hp
  have h1 : N.T s N.x1 = 0 := by
    ext i
    fin_cases i
    · exact hb
    · exact hd
    · exact hq
  have hTail (w : N.Tail) : N.T s w = 0 := by
    ext i
    fin_cases i
    · exact (ht w).1
    · exact (ht w).2
    · exact (N.cutStencil s w).1
  rw [N.split x]
  simp only [map_add,map_smul,h0,h1,hTail,smul_zero,add_zero,LinearMap.zero_apply]

theorem splitValues (s : S) (x : D) :
    N.T s x = N.r0 x • N.T s N.x0 + N.r1 x • N.T s N.x1 + N.T s (N.tailPart x : D) := by
  conv_lhs => rw [N.split x]
  simp only [map_add,map_smul]

theorem r00 : N.r0 N.x0 = 1 := by simp [r0,N.at0]
theorem r01 : N.r0 N.x1 = 0 := by simp [r0,N.at1]
theorem r10 : N.r1 N.x0 = 0 := by simp [r1,N.at0]
theorem r11 : N.r1 N.x1 = 1 := by simp [r1,N.at1]

theorem pImage (hh : N.pivot.PureImage) : FixedImage N.T N.center := by
  let a : Target K := ![1,0,0]
  let b : Target K := ![0,1,0]
  refine ⟨a,b,?_,?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro h; have e := congrFun h 1
      simp [b] at e
    · intro c h; have e := congrFun h 0
      simp [a,b,Pi.smul_apply] at e
  intro s
  refine ⟨coord (N.T s) 0,coord (N.T s) 1, by simp [N.vanishes],by simp [N.vanishes],?_⟩
  intro x
  have hx : N.T s x 2 = 0 := by
    have h₀ : N.T s N.x0 2 = 0 := (hh s).1
    have h₁ : N.T s N.x1 2 = 0 := (hh s).2
    rw [N.splitValues s x]
    simp [h₀,h₁,(N.cutStencil s (N.tailPart x)).1]
  ext i
  fin_cases i <;> simp [a,b,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hx,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]

theorem pKernel (hh : N.pivot.PureKernel) : FixedKernel N.T N.center := by
  refine ⟨N.r0,N.r1,by simp [r0,N.vanishes],by simp [r1,N.vanishes],?_,?_⟩
  · rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    constructor
    · intro h; have e := DFunLike.congr_fun h N.x1; simp [N.r11] at e
    · intro c h; have e := DFunLike.congr_fun h N.x0
      simp [N.r10,N.r00,LinearMap.smul_apply] at e
  intro s
  refine ⟨N.T s N.x0,N.T s N.x1,?_⟩
  intro x
  rw [N.splitValues s x]
  have ht : N.T s (N.tailPart x : D) = 0 := by
    ext i
    fin_cases i
    · exact (hh s (N.tailPart x)).1
    · exact (hh s (N.tailPart x)).2
    · exact (N.cutStencil s (N.tailPart x)).1
  rw [ht,add_zero]

theorem pMixed (hh : N.pivot.Mixed) : FixedLine N.T N.center := by
  obtain ⟨z,hz,hline,horth,hform⟩ := hh
  let p := N.pivot.p z
  let q := N.pivot.q z
  let a : Target K := ![q,-p,0]
  let b : D →ₗ[K] K := p • N.r0 + q • N.r1
  have hb (x : D) : b x = p*N.r0 x+q*N.r1 x := by
    simp only [b,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
  have center : b N.center = 0 := by simp [hb,r0,r1,N.vanishes]
  have hR : ∀ s x, b x = 0 → ∃ t : K, N.T s x = t • a := by
    intro s x hx
    have hne : q ≠ 0 ∨ -p ≠ 0 := by
      rcases hz with h|h
      · exact Or.inr (neg_ne_zero.mpr h)
      · exact Or.inl h
    obtain ⟨v,hv₀,hv₁⟩ := Pivot.inLine hne (show q*N.r1 x=(-p)*N.r0 x by
      rw [hb] at hx
      linear_combination hx)
    have h02 : N.T s x 2 = 0 := by
      rw [N.splitValues s x]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,(N.cutStencil s (N.tailPart x)).1,
        hv₀,hv₁,add_zero]
      have e : p * N.T s N.x1 2 = q * N.T s N.x0 2 := hline s
      linear_combination -v*e
    have ho : p*N.T s x 0+q*N.T s x 1=0 := by
      rw [N.splitValues s x]
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hv₀,hv₁]
      have h₁ : p*N.T s (N.tailPart x : D) 0+q*N.T s (N.tailPart x : D) 1=0 :=
        horth s (N.tailPart x)
      have h₂ := hform s
      rw [Pivot.form_apply] at h₂
      change p*(N.T s N.x0 0*q - N.T s N.x1 0*p) +
        q*(N.T s N.x0 1*q - N.T s N.x1 1*p) = 0 at h₂
      linear_combination h₁ + v*h₂
    obtain ⟨t,h₀,h₁⟩ := Pivot.inLine hne (show q*N.T s x 1=(-p)*N.T s x 0 by
      linear_combination ho)
    refine ⟨t,?_⟩
    ext i
    fin_cases i <;> simp [a,h₀,h₁,h02,Pi.smul_apply,smul_eq_mul,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  obtain ⟨e,he⟩ : ∃ e : Target K →ₗ[K] K, e a = 1 := by
    rcases hz with h|h
    · refine ⟨(-p)⁻¹ • LinearMap.proj 1,?_⟩
      change (-p)⁻¹ * (-p) = 1
      exact inv_mul_cancel₀ (neg_ne_zero.mpr (show p ≠ 0 from h))
    · refine ⟨q⁻¹ • LinearMap.proj 0,?_⟩
      change q⁻¹ * q = 1
      exact inv_mul_cancel₀ (show q ≠ 0 from h)
  obtain ⟨v,hv⟩ : ∃ v : D, b v = 1 := by
    rcases hz with h|h
    · refine ⟨p⁻¹ • N.x0,?_⟩
      have h0 : b N.x0 = p := by simp [hb,N.r00,N.r10]
      rw [map_smul,h0,smul_eq_mul,inv_mul_cancel₀ h]
    · refine ⟨q⁻¹ • N.x1,?_⟩
      have h1 : b N.x1 = q := by simp [hb,N.r01,N.r11]
      rw [map_smul,h1,smul_eq_mul,inv_mul_cancel₀ h]
  exact fixedLine_of_restrict N.T N.vanishes a b e v he hv center hR

theorem classification (hLarge : 3 < finrank K S) : ThreeShapes N.T N.center := by
  rcases N.pivot.classify N.pivot_faithful with hi|hk|hm|hs
  · exact Or.inl (N.pImage hi)
  · exact Or.inr (Or.inl (N.pKernel hk))
  · exact Or.inr (Or.inr (N.pMixed hm))
  let f := N.pivot.p.prod (N.pivot.q.prod N.pivot.a)
  have h : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun s h => ?_
    exact hs s (congrArg Prod.fst h) (congrArg (fun p => p.2.1) h)
      (congrArg (fun p => p.2.2) h)
  have hf : finrank K S ≤ 3 := by simpa using f.finrank_le_finrank_of_injective h
  omega

end Normalized
end RankModel.PivotCore

open Module
open scoped BigOperators

namespace RankModel.PivotCore

variable {K S D V : Type*} [Field K] [CharZero K]
variable [AddCommGroup S] [Module K S] [AddCommGroup D] [Module K D]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem rankOneLaw (T : D →ₗ[K] V) (h : finrank K (LinearMap.range T) ≤ 1)
    (e : V →ₗ[K] K) (x v : D) : e (T x) • T v = e (T v) • T x := by
  obtain ⟨a,ha⟩ := finrank_le_one_iff.mp h
  obtain ⟨p,hp⟩ := ha ⟨T x,⟨x,rfl⟩⟩
  obtain ⟨q,hq⟩ := ha ⟨T v,⟨v,rfl⟩⟩
  have ep : p • (a : V) = T x := congrArg Subtype.val hp
  have eq : q • (a : V) = T v := congrArg Subtype.val hq
  simp only [← ep,← eq,map_smul,smul_eq_mul,smul_smul]
  congr 1 <;> ring1

theorem rankOneLine (T : S →ₗ[K] D →ₗ[K] V) (hT : Function.Injective T) (center : D)
    (hcenter : ∀ s, T s center = 0) (hsmall : ∀ s, finrank K (LinearMap.range (T s)) ≤ 1)
    (hLarge : 3 < finrank K S) :
    FixedLine T center := by
  classical
  have hex : ∃ (s : S) (v : D), T s v ≠ 0 := by
    by_contra h
    have hz : ∀ s, T s = 0 := by
      intro s
      ext v
      by_contra hv
      exact h ⟨s,v,hv⟩
    letI : Subsingleton S := ⟨fun a b => hT ((hz a).trans (hz b).symm)⟩
    have hz : finrank K S = 0 := Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨m,v,hv⟩ := hex
  let a := T m v
  obtain ⟨e,he⟩ := Module.Projective.exists_dual_eq_one K hv
  change e a = 1 at he
  let b := e.comp (T m)
  have hBV : b v = 1 := he
  have hBZ : b center = 0 := by simp [b,hcenter]
  refine fixedLine_of_restrict T hcenter a b e v he hBV hBZ ?_
  intro s x hx
  have hMx : T m x = 0 := by
    have h := rankOneLaw (T m) (hsmall m) e x v
    change b x • a = e a • T m x at h
    simpa [hx,he] using h.symm
  have h := rankOneLaw (T (m+s)) (hsmall (m+s)) e x v
  have he' : e (T m v) = 1 := he
  simp only [map_add,LinearMap.add_apply,hMx,zero_add,he',add_smul,smul_add,one_smul] at h
  have hr := rankOneLaw (T s) (hsmall s) e x v
  rw [hr] at h
  exact ⟨e (T s x),(add_right_cancel h).symm⟩

def post (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V) :
    S →ₗ[K] D →ₗ[K] Target K where
  toFun s := E.toLinearMap.comp (T s)
  map_add' s t := by ext x i; simp only [map_add,LinearMap.add_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Pi.add_apply]
  map_smul' c s := by ext x i; simp only [map_smul,LinearMap.smul_apply,LinearMap.comp_apply,
    LinearEquiv.coe_coe,Pi.smul_apply,RingHom.id_apply]

@[simp] theorem post_eval (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V)
    (s : S) (x : D) : post E T s x = E (T s x) := rfl

theorem ofPost (E : V ≃ₗ[K] Target K) (T : S →ₗ[K] D →ₗ[K] V) (center : D)
    (h : ThreeShapes (post E T) center) : ThreeShapes T center := by
  rcases h with h|h|h
  · obtain ⟨a,b,hi,h⟩ := h
    refine Or.inl ⟨E.symm a,E.symm b,?_,?_⟩
    · have h' := hi.map' E.symm.toLinearMap (LinearMap.ker_eq_bot.mpr E.symm.injective)
      convert h' using 1
      ext i
      fin_cases i <;> rfl
    intro s
    obtain ⟨f,g,hf,hg,h⟩ := h s
    refine ⟨f,g,hf,hg,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)
  · obtain ⟨f,g,hf,hg,hi,h⟩ := h
    refine Or.inr (Or.inl ⟨f,g,hf,hg,hi,?_⟩)
    intro s
    obtain ⟨a,b,h⟩ := h s
    refine ⟨E.symm a,E.symm b,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)
  · obtain ⟨a,b,ha,hb,hb0,h⟩ := h
    refine Or.inr (Or.inr ⟨E.symm a,b,?_,hb,hb0,?_⟩)
    · intro hz
      exact ha (E.symm.injective (hz.trans (map_zero E.symm).symm))
    intro s
    obtain ⟨f,y,hf,h⟩ := h s
    refine ⟨f,E.symm y,hf,?_⟩
    intro x
    simpa only [post_eval,LinearEquiv.symm_apply_apply,map_add,map_smul] using
      congrArg E.symm (h x)

theorem classifySpace (T : S →ₗ[K] D →ₗ[K] V) (hT : Function.Injective T)
    (center : D) (hcenter : ∀ s, T s center = 0)
    (hrank : ∀ s, finrank K (LinearMap.range (T s)) ≤ 2)
    (hV : finrank K V = 3) (hS : 3 < finrank K S) : ThreeShapes T center := by
  classical
  by_cases hm : ∃ m, finrank K (LinearMap.range (T m)) = 2
  · obtain ⟨m,hm⟩ := hm
    let R := LinearMap.range (T m)
    have hR : finrank K R = 2 := hm
    obtain ⟨f,hf⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := R) (n := 2) hR.ge
    let f' : Fin 2 → V := fun i => (f i : V)
    have hf' : LinearIndependent K f' := hf.map' R.subtype R.ker_subtype
    obtain ⟨b,hb⟩ := exists_linearIndependent_snoc_of_lt_finrank hf' (by omega : 2 < finrank K V)
    let B : Basis (Fin 3) K V := basisOfLinearIndependentOfCardEqFinrank hb (by simp [hV])
    have hB (i : Fin 2) : B (Fin.castSucc i) = f' i := by
      simp [B,basisOfLinearIndependentOfCardEqFinrank,Fin.snoc_castSucc]
    have hspan : Submodule.span K (Set.range f') = R := by
      apply Submodule.eq_of_le_of_finrank_eq
      · apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        exact (f i).property
      · rw [finrank_span_eq_card hf',hR,Fintype.card_fin]
    obtain ⟨v0,hv0⟩ := (f 0).property
    obtain ⟨v1,hv1⟩ := (f 1).property
    have hb0 : T m v0 = B 0 := hv0.trans (hB 0).symm
    have hb1 : T m v1 = B 1 := hv1.trans (hB 1).symm
    let E : V ≃ₗ[K] Target K := B.equivFun
    let U := post E T
    have hU : Function.Injective U := by
      intro x y hxy
      apply hT
      ext z
      apply E.injective
      exact congrArg (fun F : D →ₗ[K] Target K => F z) hxy
    have hUr (s : S) : finrank K (LinearMap.range (U s)) ≤ 2 := by
      change finrank K (LinearMap.range (E.toLinearMap.comp (T s))) ≤ 2
      rw [LinearMap.range_comp,LinearEquiv.finrank_map_eq]
      exact hrank s
    have hU0 : U m v0 = ![1,0,0] := by
      rw [show U m v0 = B.equivFun (T m v0) from rfl,hb0]
      ext i
      fin_cases i <;> exact B.equivFun_self _ _
    have hU1 : U m v1 = ![0,1,0] := by
      rw [show U m v1 = B.equivFun (T m v1) from rfl,hb1]
      ext i
      fin_cases i <;> exact B.equivFun_self _ _
    have hU2 (x : D) : U m x 2 = 0 := by
      have hle : Submodule.span K (Set.range f') ≤ LinearMap.ker (B.coord 2) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change B.coord 2 (f' i) = 0
        rw [← hB i, Basis.coord_apply, Basis.repr_self_apply]
        fin_cases i <;> simp
      have hm' : T m x ∈ Submodule.span K (Set.range f') := by
        rw [hspan]
        exact ⟨x,rfl⟩
      exact hle hm'
    let N : Normalized K S D :=
      ⟨U,hU,hUr,center,by intro s; simp [U,hcenter],m,v0,v1,hU0,hU1,hU2⟩
    exact ofPost E T center (N.classification hS)
  · have hr : ∀ s, finrank K (LinearMap.range (T s)) ≤ 1 := by
      intro s
      have h := hrank s
      have hs : finrank K (LinearMap.range (T s)) ≠ 2 := fun e => hm ⟨s,e⟩
      omega
    exact Or.inr (Or.inr (rankOneLine T hT center hcenter hr hS))

end RankModel.PivotCore

namespace RankModel.Form
open scoped BigOperators
open LinearMap Module

abbrev Pairing (E : Type*) [AddCommGroup E] [Module ℂ E] :=
  E →ₗ[ℂ] E →ₗ[ℂ] ℂ

def Symmetric {E : Type*} [AddCommGroup E] [Module ℂ E] (B : Pairing E) : Prop :=
  ∀ x y, B x y = B y x

def Regular {E : Type*} [AddCommGroup E] [Module ℂ E] (B : Pairing E) : Prop :=
  ∀ x, (∀ y, B x y = 0) → x = 0

section General
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]

theorem polar_zero (B : Pairing E) (symm : Symmetric B)
    (W : Submodule ℂ E) (hq : ∀ x ∈ W, B x x = 0)
    (x y : E) (hx : x ∈ W) (hy : y ∈ W) : B x y = 0 := by
  have h := hq (x+y) (W.add_mem hx hy)
  simp only [map_add,LinearMap.add_apply,hq x hx,hq y hy,symm y x,zero_add,add_zero] at h
  have e : (2 : ℂ)*B x y = 0 := by simpa only [two_mul] using h
  exact (mul_eq_zero.mp e).resolve_left two_ne_zero

theorem isotropic_bound (B : Pairing E) (symm : Symmetric B)
    (W : Submodule ℂ E) (hq : ∀ x ∈ W, B x x = 0) :
    2 * finrank ℂ W ≤ finrank ℂ E + finrank ℂ B.ker := by
  let f := B.comp W.subtype
  have into : f.range ≤ W.dualAnnihilator := by
    rintro _ ⟨x,rfl⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro y hy
    exact polar_zero B symm W hq x.val y x.prop hy
  have ann := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  have rel := Submodule.finrank_mono into
  have dim := f.finrank_range_add_finrank_ker
  have eq : f.ker.map W.subtype = W ⊓ B.ker := by
    dsimp only [f]
    rw [LinearMap.ker_comp,Submodule.map_comap_subtype]
  have le := Submodule.finrank_mono (inf_le_right : W ⊓ B.ker ≤ B.ker)
  rw [←eq,Submodule.finrank_map_subtype_eq] at le
  calc
    2 * finrank ℂ W = finrank ℂ W + finrank ℂ W := by rw [two_mul]
    _ = finrank ℂ W + (finrank ℂ f.range + finrank ℂ f.ker) :=
      congrArg (fun d : Nat => finrank ℂ W + d) dim.symm
    _ ≤ finrank ℂ W + (finrank ℂ W.dualAnnihilator + finrank ℂ B.ker) :=
      Nat.add_le_add_left (Nat.add_le_add rel le) _
    _ = finrank ℂ E + finrank ℂ B.ker :=
      (Nat.add_assoc _ _ _).symm.trans (congrArg (fun d : Nat => d + finrank ℂ B.ker) ann)

theorem regular_ker (B : Pairing E) (nd : Regular B) : B.ker = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply nd
  intro y
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp hx) y

theorem isotropic_bound_nd (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (W : Submodule ℂ E)
    (hq : ∀ x ∈ W, B x x = 0) : 2 * finrank ℂ W ≤ finrank ℂ E := by
  have q := isotropic_bound B symm W hq
  rwa [regular_ker B nd,finrank_bot,add_zero] at q

noncomputable def diag (B : Pairing E) (a b : ℂ) :
    Pairing (E × E) :=
  a • B.compl₁₂ (LinearMap.fst ℂ E E) (LinearMap.fst ℂ E E) +
    b • B.compl₁₂ (LinearMap.snd ℂ E E) (LinearMap.snd ℂ E E)

theorem diag_apply (B : Pairing E) (a b : ℂ) (x y : E × E) :
    diag B a b x y = a * B x.1 y.1 + b * B x.2 y.2 := rfl

theorem diag_symm (B : Pairing E) (hs : Symmetric B) (a b : ℂ) :
    Symmetric (diag B a b) := by
  intro x y
  rw [diag_apply,diag_apply,hs x.1 y.1,hs x.2 y.2]

theorem fst_zero_of_ker (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (ha : a ≠ 0) (z : E × E) (hz : z ∈ (diag B a b).ker) : z.1 = 0 := by
  change diag B a b z = 0 at hz
  apply nd
  intro y
  have h := LinearMap.congr_fun hz (y,0)
  rw [diag_apply] at h
  simpa [ha] using h

theorem snd_zero_of_ker (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (hb : b ≠ 0) (z : E × E) (hz : z ∈ (diag B a b).ker) : z.2 = 0 := by
  change diag B a b z = 0 at hz
  apply nd
  intro y
  have h := LinearMap.congr_fun hz (0,y)
  rw [diag_apply] at h
  simpa [hb] using h

theorem diag_ker_bound (B : Pairing E) (nd : Regular B)
    (a b : ℂ) (ha : a ≠ 0) :
    finrank ℂ (diag B a b).ker ≤ finrank ℂ E := by
  let K := (diag B a b).ker
  let pr : K →ₗ[ℂ] E := (LinearMap.snd ℂ E E).comp K.subtype
  have inj : Function.Injective pr := by
    intro u v e
    apply Subtype.ext
    apply Prod.ext
    · exact (fst_zero_of_ker B nd a b ha u.val u.prop).trans
        (fst_zero_of_ker B nd a b ha v.val v.prop).symm
    · exact e
  exact LinearMap.finrank_le_finrank_of_injective inj

theorem diag_isotropic_bound (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (a b : ℂ) (ha : a ≠ 0)
    (L : Submodule ℂ (E × E))
    (hq : ∀ z ∈ L, a * B z.1 z.1 + b * B z.2 z.2 = 0) :
    2 * finrank ℂ L ≤ 3 * finrank ℂ E := by
  have h := isotropic_bound (diag B a b) (diag_symm B symm a b) L (by
    intro z hz
    rw [diag_apply]
    exact hq z hz)
  have r := diag_ker_bound B nd a b ha
  rw [Module.finrank_prod] at h
  omega

theorem diag_isotropic_bound_regular (B : Pairing E) (symm : Symmetric B)
    (nd : Regular B) (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (L : Submodule ℂ (E × E))
    (hq : ∀ z ∈ L, a * B z.1 z.1 + b * B z.2 z.2 = 0) :
    finrank ℂ L ≤ finrank ℂ E := by
  have ker : (diag B a b).ker = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    exact Prod.ext (fst_zero_of_ker B nd a b ha z hz) (snd_zero_of_ker B nd a b hb z hz)
  have h := isotropic_bound (diag B a b) (diag_symm B symm a b) L (by
    intro z hz
    rw [diag_apply]
    exact hq z hz)
  rw [ker,finrank_bot,add_zero,Module.finrank_prod] at h
  omega
end General

noncomputable def dots (n : Nat) : Pairing (Fin n → ℂ) :=
  dotProductBilin ℂ ℂ

theorem dots_eval (n : Nat) (x y : Fin n → ℂ) :
    dots n x y = ∑ i, x i * y i := rfl

theorem dots_symm (n : Nat) : Symmetric (dots n) := by
  intro x y
  change dotProduct x y = dotProduct y x
  exact dotProduct_comm x y

theorem dots_regular (n : Nat) : Regular (dots n) := by
  intro x h
  funext i
  have z := h (Pi.single i (1 : ℂ))
  change dotProduct x (Pi.single i 1) = 0 at z
  rwa [dotProduct_single_one] at z

def ones (n : Nat) : Fin n → ℂ := fun _ => 1

noncomputable def sumLin (n : Nat) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  ∑ i : Fin n, LinearMap.proj i

theorem sumLin_eval (n : Nat) (x : Fin n → ℂ) : sumLin n x = ∑ i, x i := by
  simp [sumLin]

noncomputable def centered (n : Nat) : Submodule ℂ (Fin n → ℂ) := (sumLin n).ker

theorem centered_mem (n : Nat) (x : Fin n → ℂ) :
    x ∈ centered n ↔ ∑ i, x i = 0 := by
  rw [centered,LinearMap.mem_ker,sumLin_eval]

theorem sum_ones (n : Nat) : sumLin n (ones n) = (n : ℂ) := by
  simp [sumLin_eval,ones]

theorem centered_rank (n : Nat) (h : 0 < n) : finrank ℂ (centered n) = n - 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)
  have onto : Function.Surjective (sumLin n) := by
    intro x
    refine ⟨(x/(n : ℂ)) • ones n,?_⟩
    rw [map_smul,sum_ones,smul_eq_mul]
    exact div_mul_cancel₀ x hn
  have d := (sumLin n).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto,finrank_top,finrank_self,Module.finrank_pi,Fintype.card_fin] at d
  change 1 + finrank ℂ (centered n) = n at d
  omega

noncomputable def centerDot (n : Nat) : Pairing (centered n) :=
  (dots n).compl₁₂ (centered n).subtype (centered n).subtype

theorem centerDot_symm (n : Nat) : Symmetric (centerDot n) :=
  fun x y => dots_symm n x.val y.val

theorem centerDot_regular (n : Nat) (h : 0 < n) : Regular (centerDot n) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h)
  intro x orth
  apply Subtype.ext
  apply dots_regular n
  intro y
  let a := sumLin n y/(n : ℂ)
  let y' := y-a • ones n
  have ok : y' ∈ centered n := by
    change sumLin n (y-a • ones n) = 0
    rw [map_sub,map_smul,sum_ones,smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (sumLin n y) hn).symm
  have base : dots n x.val y' = 0 := orth ⟨y',ok⟩
  have ref : dots n x.val (ones n) = 0 := by
    simpa [dots_eval,ones] using (centered_mem n x.val).mp x.prop
  have e : y = y' + a • ones n := (sub_add_cancel y (a • ones n)).symm
  calc
    dots n x.val y = dots n x.val (y' + a • ones n) := congrArg (dots n x.val) e
    _ = 0 := by rw [map_add,map_smul,base,ref,smul_zero,zero_add]

end RankModel.Form

namespace RankModel.Form
open LinearMap Module

abbrev Mat (m n : Nat) := Matrix (Fin m) (Fin n) ℂ
abbrev Vec (n : Nat) := Fin n → ℂ

noncomputable def outer (a : Vec m) (x : Vec n) : Mat m n :=
  Matrix.vecMulVec a x

noncomputable def alongColumn (a : Vec m) : Vec n →ₗ[ℂ] Mat m n :=
  (vecMulVecBilin ℂ ℂ : Vec m →ₗ[ℂ] Vec n →ₗ[ℂ] Mat m n) a

noncomputable def alongRow (b : Vec n) : Vec m →ₗ[ℂ] Mat m n :=
  (vecMulVecBilin ℂ ℂ : Vec m →ₗ[ℂ] Vec n →ₗ[ℂ] Mat m n).flip b

theorem alongColumn_eval (a : Vec m) (x : Vec n) : alongColumn a x = outer a x := rfl
theorem alongRow_eval (b : Vec n) (y : Vec m) : alongRow b y = outer y b := rfl
theorem outer_apply (a : Vec m) (x : Vec n) (i : Fin m) (j : Fin n) :
    outer a x i j = a i * x j := rfl

theorem column_injective (a : Vec m) (ha : a ≠ 0) :
    Function.Injective (alongColumn (n := n) a) := by
  classical
  have useful : ∃ i, a i ≠ 0 := by
    by_contra z
    apply ha
    funext i
    exact Classical.byContradiction (fun fi => z ⟨i,fi⟩)
  obtain ⟨i,hi⟩ := useful
  intro x y h
  funext j
  have e := congrArg (fun A : Mat m n => A i j) h
  change a i * x j = a i * y j at e
  exact mul_left_cancel₀ hi e

noncomputable def fiber (L : Submodule ℂ (Mat m n)) (a : Vec m) :
    Submodule ℂ (Vec n) := L.comap (alongColumn a)

theorem fiber_exact (L : Submodule ℂ (Mat m n)) (a : Vec m) :
    (fiber L a).map (alongColumn a) = L ⊓ (alongColumn a).range := by
  ext A
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨hx,⟨x,rfl⟩⟩
  · rintro ⟨hh,⟨x,he⟩⟩
    exact ⟨x,by change alongColumn a x ∈ L; rw [he]; exact hh,he⟩

theorem fiber_dimension (L : Submodule ℂ (Mat m n)) (a : Vec m) (ha : a ≠ 0) :
    finrank ℂ (fiber L a) = finrank ℂ (L ⊓ (alongColumn a).range : Submodule ℂ (Mat m n)) := by
  rw [← fiber_exact L a]
  exact (Submodule.equivMapOfInjective _ (column_injective a ha) _).finrank_eq

theorem dim_compressed {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (L C R : Submodule ℂ E) (ls : L ≤ C ⊔ R)
    (r : finrank ℂ R ≤ 3) (h : 1 ≤ finrank ℂ (C ⊓ R : Submodule ℂ E)) :
    finrank ℂ L ≤ finrank ℂ (L ⊓ C : Submodule ℂ E) + 2 := by
  have t : L ⊔ C ≤ C ⊔ R := sup_le ls le_sup_left
  have f := Submodule.finrank_mono t
  have s := Submodule.finrank_sup_add_finrank_inf_eq L C
  have q := Submodule.finrank_sup_add_finrank_inf_eq C R
  omega

theorem mixed_first {n : Nat} (n5 : 5 ≤ n) (L : Submodule ℂ (Mat 4 n))
    (a : centered 4) (ha : (a : Vec 4) ≠ 0) (b : Vec n)
    (contains : ∀ X ∈ L, ∃ x : Vec n, ∃ y : centered 4,
      X = outer a.val x + outer y.val b) :
    ∃ (u : Vec 4) (K : Submodule ℂ (Vec n)), u ≠ 0 ∧
      2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
      ∀ x ∈ K, (fun i j => u i * x j) ∈ L := by
  let C : Submodule ℂ (Mat 4 n) := (alongColumn a.val).range
  let R : Submodule ℂ (Mat 4 n) := ((alongRow b).comp (centered 4).subtype).range
  let K := fiber L a.val
  have clear : finrank ℂ K = finrank ℂ (L ⊓ C : Submodule ℂ (Mat 4 n)) :=
    fiber_dimension L a.val ha
  refine ⟨a.val,K,ha,?_,?_⟩
  · by_cases bz : b = 0
    · have good : L ≤ C := by
        intro X hx
        obtain ⟨x,y,h⟩ := contains X hx
        refine ⟨x,?_⟩
        rw [alongColumn_eval,h,bz]
        simp [outer]
      have e : L ⊓ C = L := inf_eq_left.mpr good
      rw [e] at clear
      omega
    · have range_dim : finrank ℂ R ≤ 3 := by
        let f : centered 4 →ₗ[ℂ] Mat 4 n := (alongRow b).comp (centered 4).subtype
        calc
          finrank ℂ R ≤ finrank ℂ R + finrank ℂ f.ker := Nat.le_add_right _ _
          _ = finrank ℂ (centered 4) :=
            LinearMap.finrank_range_add_finrank_ker (K := ℂ)
              (V := ↥(centered 4)) (V₂ := Mat 4 n) f
          _ = 3 := centered_rank 4 (by decide)
      have cap : L ≤ C ⊔ R := by
        intro X hx
        obtain ⟨x,y,h⟩ := contains X hx
        rw [h]
        exact Submodule.add_mem_sup (show outer a.val x ∈ C from ⟨x,rfl⟩)
          (show outer y.val b ∈ R from ⟨y,rfl⟩)
      have joint : outer a.val b ∈ C ⊓ R := ⟨⟨b,rfl⟩,⟨a,rfl⟩⟩
      have nz : outer a.val b ≠ 0 := by
        intro eq
        apply bz
        apply column_injective a.val ha
        change outer a.val b = alongColumn a.val 0
        rw [map_zero,eq]
      have line : ℂ ∙ outer a.val b ≤ C ⊓ R :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr joint
      have bound := Submodule.finrank_mono line
      rw [finrank_span_singleton nz] at bound
      have d := dim_compressed L C R cap range_dim bound
      omega
  · intro x hx
    exact hx

end RankModel.Form

namespace RankModel.Form
open LinearMap Module
open scoped BigOperators

noncomputable def qMat (X : Mat m n) : ℂ := ∑ i, ∑ j, (X i j)^2

theorem q_two_columns (a b : Vec m) (x y : Vec n) (ort : dots m a b = 0) :
    qMat (outer a x + outer b y) =
      dots m a a * dots n x x + dots m b b * dots n y y := by
  calc
    _ = ∑ i, ((a i*a i)*dots n x x + (b i*b i)*dots n y y +
        (a i*b i)*(2*dots n x y)) := by
      unfold qMat
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = ∑ j, ((a i*a i)*(x j*x j) + (b i*b i)*(y j*y j) +
            (a i*b i)*(2*(x j*y j))) := by
          apply Finset.sum_congr rfl
          intro j _
          change (a i*x j + b i*y j)^2 = _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib,dots_eval,← Finset.mul_sum]
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.sum_mul,← dots_eval,ort,zero_mul,add_zero]

theorem q_transpose (X : Mat m n) : qMat X.transpose = qMat X := by
  unfold qMat
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

theorem q_two_rows (a b : Vec n) (x y : Vec m) (ort : dots n a b = 0) :
    qMat (outer x a + outer y b) = dots n a a * dots m x x + dots n b b * dots m y y := by
  have flip : (outer x a + outer y b).transpose = outer a x + outer b y := by
    ext i j
    change x j*a i + y j*b i = a i*x j + b i*y j
    rw [mul_comm (x j),mul_comm (y j)]
  rw [← q_transpose (outer x a + outer y b),flip]
  exact q_two_columns a b x y ort

noncomputable def cols (a b : Vec m) : centered n × centered n →ₗ[ℂ] Mat m n :=
  ((alongColumn a).comp (centered n).subtype).comp (LinearMap.fst ℂ _ _) +
    ((alongColumn b).comp (centered n).subtype).comp (LinearMap.snd ℂ _ _)

noncomputable def rows (a b : Vec n) : centered m × centered m →ₗ[ℂ] Mat m n :=
  ((alongRow a).comp (centered m).subtype).comp (LinearMap.fst ℂ _ _) +
    ((alongRow b).comp (centered m).subtype).comp (LinearMap.snd ℂ _ _)

theorem cols_eval (a b : Vec m) (x y : centered n) :
    cols a b (x,y) = outer a x.val + outer b y.val := rfl

theorem rows_eval (a b : Vec n) (x y : centered m) :
    rows a b (x,y) = outer x.val a + outer y.val b := rfl

theorem comap_bound {E V : Type*} [AddCommGroup E] [AddCommGroup V]
    [Module ℂ E] [Module ℂ V] [FiniteDimensional ℂ E]
    (f : E →ₗ[ℂ] V) (L : Submodule ℂ V)
    (onto : ∀ x ∈ L, ∃ z, f z = x) :
    finrank ℂ L ≤ finrank ℂ (L.comap f) := by
  have e : (L.comap f).map f = L := by
    ext x; constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hx
      obtain ⟨z,hz⟩ := onto x hx
      exact ⟨z,by change f z ∈ L; rw [hz]; exact hx,hz⟩
  have d := Submodule.finrank_map_le f (L.comap f)
  rwa [e] at d

theorem q_cols_comap (L : Submodule ℂ (Mat m n)) (a b : Vec m)
    (ort : dots m a b = 0) (hq : ∀ X ∈ L, qMat X = 0) :
    ∀ z ∈ L.comap (cols a b), dots m a a * centerDot n z.1 z.1 +
      dots m b b * centerDot n z.2 z.2 = 0 := by
  rintro ⟨x,y⟩ hz
  have h := hq _ (show cols a b (x,y) ∈ L from hz)
  rw [cols_eval,q_two_columns a b _ _ ort] at h
  exact h

theorem q_rows_comap (L : Submodule ℂ (Mat m n)) (a b : Vec n)
    (ort : dots n a b = 0) (hq : ∀ X ∈ L, qMat X = 0) :
    ∀ z ∈ L.comap (rows a b), dots n a a * centerDot m z.1 z.1 +
      dots n b b * centerDot m z.2 z.2 = 0 := by
  rintro ⟨x,y⟩ hz
  have h := hq _ (show rows a b (x,y) ∈ L from hz)
  rw [rows_eval,q_two_rows a b _ _ ort] at h
  exact h

theorem regular_columns_impossible {n : Nat} (n0 : 0 < n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L) (a b : Vec 4)
    (ort : dots 4 a b = 0) (ap : dots 4 a a ≠ 0) (bp : dots 4 b b ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered n, X = outer a x.val + outer b y.val)
    (hq : ∀ X ∈ L, qMat X = 0) : False := by
  have big := comap_bound (cols a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have d := diag_isotropic_bound_regular (centerDot n) (centerDot_symm n)
    (centerDot_regular n n0) _ _ ap bp _ (q_cols_comap L a b ort hq)
  rw [centered_rank n n0] at d
  omega

theorem nonisotropic_rows_impossible {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L) (a b : Vec n)
    (ort : dots n a b = 0) (ap : dots n a a ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered 4, X = outer x.val a + outer y.val b)
    (hq : ∀ X ∈ L, qMat X = 0) : False := by
  have big := comap_bound (rows a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have d := diag_isotropic_bound (centerDot 4) (centerDot_symm 4)
    (centerDot_regular 4 (by decide)) _ _ ap _ (q_rows_comap L a b ort hq)
  rw [centered_rank 4 (by decide)] at d
  omega

theorem radical_columns_first {n : Nat} (n0 : 0 < n)
    (L : Submodule ℂ (Mat 4 n)) (a b : Vec 4) (anz : a ≠ 0)
    (ort : dots 4 a b = 0) (null : dots 4 a a = 0) (bp : dots 4 b b ≠ 0)
    (coords : ∀ X ∈ L, ∃ x y : centered n, X = outer a x.val + outer b y.val)
    (hq : ∀ X ∈ L, qMat X = 0) :
    ∃ (u : Vec 4) (K : Submodule ℂ (Vec n)), u ≠ 0 ∧
      2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
      ∀ x ∈ K, (fun i j => u i * x j) ∈ L := by
  let S := L.comap (cols a b)
  let f : S →ₗ[ℂ] centered n := (LinearMap.snd ℂ _ _).comp S.subtype
  let K := fiber L a
  have big : finrank ℂ L ≤ finrank ℂ S := comap_bound (cols a b) L (by
    intro X hx
    obtain ⟨x,y,e⟩ := coords X hx
    exact ⟨(x,y),e.symm⟩)
  have fit : ∀ z ∈ f.range, centerDot n z z = 0 := by
    rintro y ⟨z,rfl⟩
    have h := q_cols_comap L a b ort hq z.val z.prop
    rw [null,zero_mul,zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left bp
  have d := isotropic_bound_nd (centerDot n) (centerDot_symm n)
    (centerDot_regular n n0) f.range fit
  rw [centered_rank n n0] at d
  have ker_second (z : f.ker) : z.val.val.2 = 0 := LinearMap.mem_ker.mp z.prop
  let first : f.ker →ₗ[ℂ] Vec n :=
    (centered n).subtype.comp ((LinearMap.fst ℂ _ _).comp (S.subtype.comp f.ker.subtype))
  have hfirst (z : f.ker) : first z ∈ K := by
    have hs : cols a b z.val.val ∈ L := z.val.prop
    have eq : z.val.val = (z.val.val.1,0) := Prod.ext rfl (ker_second z)
    rw [eq,cols_eval] at hs
    change outer a z.val.val.1.val ∈ L
    have hs' : outer a z.val.val.1.val + outer b (0 : Vec n) ∈ L := hs
    simpa [outer] using hs'
  let g : f.ker →ₗ[ℂ] K := first.codRestrict K hfirst
  have gi : Function.Injective g := by
    intro z t ge
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      have e := congrArg (fun x : K => x.val) ge
      change z.val.val.1.val = t.val.val.1.val at e
      exact e
    · rw [ker_second z,ker_second t]
  have kcap := LinearMap.finrank_le_finrank_of_injective gi
  have rn := LinearMap.finrank_range_add_finrank_ker (K := ℂ)
    (V := ↥S) (V₂ := ↥(centered n)) f
  refine ⟨a,K,anz,by omega,?_⟩
  intro x hx
  exact hx

end RankModel.Form

namespace RankModel.Form
open scoped BigOperators
open LinearMap Module

theorem orthogonal_span_two {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (B : Pairing E) (A : Submodule ℂ E)
    (sm : finrank ℂ A ≤ 2) (b : E) (hb : b ∈ A) (nb : B b b ≠ 0) :
    ∃ a ∈ A, B b a = 0 ∧
      ∀ x ∈ A, ∃ c d : ℂ, x = c • a + d • b := by
  let b' : A := ⟨b,hb⟩
  let f : A →ₗ[ℂ] ℂ := (B b).domRestrict A
  let D := f.ker
  have t : f b' = B b b := rfl
  have surj : Function.Surjective f := by
    intro y
    refine ⟨(y / B b b) • b',?_⟩
    rw [map_smul,t,smul_eq_mul]
    exact div_mul_cancel₀ y nb
  have dim := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,finrank_self] at dim
  have small : finrank ℂ D ≤ 1 := by change finrank ℂ f.ker ≤ 1; omega
  obtain ⟨a',aSpan⟩ := finrank_le_one_iff.mp small
  let a : E := a'.val.val
  have porth : B b a = 0 := LinearMap.mem_ker.mp a'.prop
  refine ⟨a,a'.val.prop,porth,?_⟩
  intro x hx
  let x' : A := ⟨x,hx⟩
  let d := f x' / B b b
  have kh : x' - d • b' ∈ D := by
    change f (x' - d • b') = 0
    rw [map_sub,map_smul,t,smul_eq_mul]
    exact sub_eq_zero.mpr (div_mul_cancel₀ (f x') nb).symm
  obtain ⟨c,cv⟩ := aSpan ⟨x' - d • b',kh⟩
  have cve : c • a'.val = x' - d • b' := congrArg Subtype.val cv
  refine ⟨c,d,?_⟩
  have xy : c • a'.val + d • b' = x' := by rw [cve,sub_add_cancel]
  exact (congrArg Subtype.val xy).symm

end RankModel.Form

namespace RankModel.Form
open scoped BigOperators
open LinearMap Module

def First {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ (a : Vec 4) (K : Submodule ℂ (Vec n)), a ≠ 0 ∧
    2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n ∧
    (∀ x ∈ K, (fun i j => a i * x j) ∈ L)

def Second {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ U : Submodule ℂ (Vec n), finrank ℂ U = 2 ∧
    (∀ u ∈ U, (∑ j, u j) = 0 ∧ (∑ j, (u j)^2) = 0) ∧
    (∀ X ∈ L, ∀ i, X i ∈ U)

def ColCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ a b : centered 4, LinearIndependent ℂ ![a,b] ∧
    ∀ X ∈ L, ∃ x y : centered n, X = outer a.val x.val + outer b.val y.val

def RowCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ a b : centered n, LinearIndependent ℂ ![a,b] ∧
    ∀ X ∈ L, ∃ x y : centered 4, X = outer x.val a.val + outer y.val b.val

def MixedCompression {n : Nat} (L : Submodule ℂ (Mat 4 n)) : Prop :=
  ∃ (a : centered 4) (b : centered n), a.val ≠ 0 ∧
    ∀ X ∈ L, ∃ x : centered n, ∃ y : centered 4, X = outer a.val x.val + outer y.val b.val

theorem spanTwo_finrank {E : Type*} [AddCommGroup E] [Module ℂ E] {a b : E}
    (lin : LinearIndependent ℂ ![a,b]) :
    finrank ℂ (Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E))) = 2 := by
  rw [finrank_span_eq_card lin,Fintype.card_fin]

theorem spanTwo_left {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    a ∈ Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E)) :=
  Submodule.subset_span ⟨0,rfl⟩

theorem spanTwo_right {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E) :
    b ∈ Submodule.span ℂ (Set.range (![a,b] : Fin 2 → E)) :=
  Submodule.subset_span ⟨1,rfl⟩

theorem change_columns {m n : Nat} (a b p q : centered m)
    (c d e f : ℂ) (ha : a = c • p + d • q) (hb : b = e • p + f • q)
    (x y : centered n) :
    outer a.val x.val + outer b.val y.val =
      outer p.val (c • x + e • y : centered n).val +
      outer q.val (d • x + f • y : centered n).val := by
  apply Matrix.ext
  intro i j
  have ai := congrArg (fun z : centered m => z.val i) ha
  have bi := congrArg (fun z : centered m => z.val i) hb
  change a.val i = c*p.val i + d*q.val i at ai
  change b.val i = e*p.val i + f*q.val i at bi
  change a.val i*x.val j + b.val i*y.val j =
    p.val i*(c*x.val j + e*y.val j) + q.val i*(d*x.val j + f*y.val j)
  rw [ai,bi]
  ring

theorem change_rows {m n : Nat} (a b p q : centered n)
    (c d e f : ℂ) (ha : a = c • p + d • q) (hb : b = e • p + f • q)
    (x y : centered m) :
    outer x.val a.val + outer y.val b.val =
      outer (c • x + e • y : centered m).val p.val +
      outer (d • x + f • y : centered m).val q.val := by
  apply Matrix.ext
  intro i j
  have aj := congrArg (fun z : centered n => z.val j) ha
  have bj := congrArg (fun z : centered n => z.val j) hb
  change a.val j = c*p.val j + d*q.val j at aj
  change b.val j = e*p.val j + f*q.val j at bj
  change x.val i*a.val j + y.val i*b.val j =
    (c*x.val i + e*y.val i)*p.val j + (d*x.val i + f*y.val i)*q.val j
  rw [aj,bj]
  ring

theorem generators_independent_direction {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (A : Submodule ℂ E) (dim : finrank ℂ A = 2)
    (p q : E) (qq : q ≠ 0) (sp : ∀ x ∈ A, ∃ c d : ℂ, x = c • p + d • q) :
    p ≠ 0 := by
  intro p0
  have small : A ≤ ℂ ∙ q := by
    intro x hx
    obtain ⟨_c,d,ex⟩ := sp x hx
    apply Submodule.mem_span_singleton.mpr
    exact ⟨d,by simpa [p0] using ex.symm⟩
  have nu := Submodule.finrank_mono small
  rw [dim,finrank_span_singleton qq] at nu
  omega

theorem column_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, qMat X = 0) (covered : ColCompression L) :
    First L := by
  obtain ⟨a,b,li,coords⟩ := covered
  let A := Submodule.span ℂ (Set.range (![a,b] : Fin 2 → centered 4))
  have dim : finrank ℂ A = 2 := spanTwo_finrank li
  have qExists : ∃ q ∈ A, centerDot 4 q q ≠ 0 := by
    classical
    by_contra no
    have zero : ∀ q ∈ A, centerDot 4 q q = 0 := by
      intro q hn
      exact Classical.byContradiction (fun hz => no ⟨q,hn,hz⟩)
    have cap := isotropic_bound_nd (centerDot 4) (centerDot_symm 4)
      (centerDot_regular 4 (by decide)) A zero
    rw [dim,centered_rank 4 (by decide)] at cap
    omega
  obtain ⟨q,qA,qN⟩ := qExists
  obtain ⟨p,_,ort,sp⟩ := orthogonal_span_two (centerDot 4) A (by omega) q qA qN
  obtain ⟨c,d,ha⟩ := sp a (spanTwo_left a b)
  obtain ⟨e,f,hb⟩ := sp b (spanTwo_right a b)
  have qnz : q ≠ 0 := by intro bz; apply qN; simp [bz]
  have pnz := generators_independent_direction A dim p q qnz sp
  have pv : p.val ≠ 0 := fun z => pnz (Subtype.ext z)
  have ort' : dots 4 p.val q.val = 0 := (dots_symm 4 p.val q.val).trans ort
  have newCoords (X : Mat 4 n) (inL : X ∈ L) :
      ∃ x y : centered n, X = outer p.val x.val + outer q.val y.val := by
    obtain ⟨x,y,h⟩ := coords X inL
    exact ⟨c • x + e • y,d • x + f • y,h.trans (change_columns a b p q c d e f ha hb x y)⟩
  by_cases hz : dots 4 p.val p.val = 0
  · exact radical_columns_first (by omega) L p.val q.val pv ort' hz qN newCoords hq
  · exact False.elim (regular_columns_impossible (by omega) L large p.val q.val ort' hz qN newCoords hq)

theorem row_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, qMat X = 0) (covered : RowCompression L) :
    Second L := by
  classical
  obtain ⟨a,b,li,coords⟩ := covered
  let A := Submodule.span ℂ (Set.range (![a,b] : Fin 2 → centered n))
  have dim : finrank ℂ A = 2 := spanTwo_finrank li
  let U := A.map (centered n).subtype
  by_cases qExists : ∃ q ∈ A, centerDot n q q ≠ 0
  · obtain ⟨q,qA,qN⟩ := qExists
    obtain ⟨p,_,ort,sp⟩ := orthogonal_span_two (centerDot n) A (by omega) q qA qN
    obtain ⟨c,d,ha⟩ := sp a (spanTwo_left a b)
    obtain ⟨e,f,hb⟩ := sp b (spanTwo_right a b)
    have newCoords (X : Mat 4 n) (inL : X ∈ L) :
        ∃ x y : centered 4, X = outer x.val q.val + outer y.val p.val := by
      obtain ⟨x,y,h⟩ := coords X inL
      refine ⟨d • x + f • y,c • x + e • y,?_⟩
      exact h.trans ((change_rows a b p q c d e f ha hb x y).trans (add_comm _ _))
    exact False.elim (nonisotropic_rows_impossible n5 L large q.val p.val ort qN newCoords hq)
  · have zero : ∀ q ∈ A, centerDot n q q = 0 := by
      intro q hn
      exact Classical.byContradiction (fun hz => qExists ⟨q,hn,hz⟩)
    have size : finrank ℂ U = 2 := by
      simpa only [U,Submodule.finrank_map_subtype_eq] using dim
    refine ⟨U,size,?_,?_⟩
    · rintro _ ⟨x,hx,rfl⟩
      refine ⟨(centered_mem n x.val).mp x.prop,?_⟩
      have d := zero x hx
      change dots n x.val x.val = 0 at d
      change (∑ j, (x.val j)^2) = 0
      simpa only [dots_eval,pow_two] using d
    · intro X inL i
      obtain ⟨x,y,showX⟩ := coords X inL
      let z : centered n := x.val i • a + y.val i • b
      have zA : z ∈ A := A.add_mem (A.smul_mem _ (spanTwo_left a b)) (A.smul_mem _ (spanTwo_right a b))
      refine ⟨z,zA,?_⟩
      funext j
      rw [showX]
      rfl

theorem mixed_finish {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (covered : MixedCompression L) : First L := by
  obtain ⟨a,b,az,coords⟩ := covered
  apply mixed_first n5 L a az b.val
  intro X inL
  obtain ⟨x,y,h⟩ := coords X inL
  exact ⟨x.val,y,h⟩

theorem postcompression {n : Nat} (n5 : 5 ≤ n)
    (L : Submodule ℂ (Mat 4 n)) (large : n ≤ finrank ℂ L)
    (hq : ∀ X ∈ L, (∑ i, ∑ j, (X i j)^2) = 0)
    (shape : ColCompression L ∨ RowCompression L ∨ MixedCompression L) :
    First L ∨ Second L := by
  rcases shape with cols|rows|mixed
  · exact Or.inl (column_finish n5 L large hq cols)
  · exact Or.inr (row_finish n5 L large hq rows)
  · exact Or.inl (mixed_finish n5 L mixed)

end RankModel.Form

open Module
open scoped BigOperators

namespace RankModel.Bridge
open RankModel.PivotCore
open RankModel.Form

abbrev Domain (n : Nat) := Fin n → ℂ

noncomputable def act {n : Nat} (L : Submodule ℂ (Mat 4 n))
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) :
    L →ₗ[ℂ] Domain n →ₗ[ℂ] centered 4 where
  toFun X := LinearMap.codRestrict (centered 4) X.val.mulVecLin (by
    intro v
    rw [centered_mem]
    simp only [Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul,hcols X.val X.prop,zero_mul]
    simp)
  map_add' X Y := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (X.val+Y.val).mulVecLin v = X.val.mulVecLin v+Y.val.mulVecLin v
    rw [Matrix.mulVecLin_add,LinearMap.add_apply]
  map_smul' r X := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change (r • X.val).mulVecLin v = r • X.val.mulVecLin v
    exact Matrix.smul_mulVec r X.val v

theorem act_coe {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    {hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0} (X : L) (v : Domain n) :
    (act L hcols X v).val = X.val.mulVecLin v := rfl

theorem act_single {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    {hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0} (X : L) (i : Fin 4) (j : Fin n) :
    (act L hcols X (Pi.single j 1)).val i = X.val i j := by
  rw [act_coe,Matrix.mulVecLin_apply,Matrix.mulVec_single_one]
  rfl

theorem act_inj {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) : Function.Injective (act L hcols) := by
  intro X Y h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  simpa only [act_single] using
    congrArg (fun F : Domain n →ₗ[ℂ] centered 4 => (F (Pi.single j 1)).val i) h

theorem act_center {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hrows : ∀ X ∈ L, ∀ i, (∑ j, X i j) = 0)
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) (X : L) :
    act L hcols X (ones n) = 0 := by
  apply Subtype.ext
  funext i
  simp [act_coe,ones,Matrix.mulVecLin_apply,Matrix.mulVec,dotProduct,hrows X.val X.prop i]

theorem act_rank {n : Nat} {L : Submodule ℂ (Mat 4 n)}
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) (X : L) :
    Module.finrank ℂ (LinearMap.range (act L hcols X)) = X.val.rank := by
  change _ = finrank ℂ (LinearMap.range X.val.mulVecLin)
  have h : (centered 4).subtype.comp (act L hcols X) = X.val.mulVecLin := rfl
  rw [← h,LinearMap.range_comp,Submodule.finrank_map_subtype_eq]

noncomputable def asProfile {n : Nat} (f : Domain n →ₗ[ℂ] ℂ) (hf : f (ones n) = 0) : centered n := by
  let e := dotProductEquiv ℂ (Fin n)
  refine ⟨e.symm f,?_⟩
  rw [centered_mem]
  have h : e (e.symm f) (ones n) = 0 := by rw [e.apply_symm_apply,hf]
  change dotProduct (e.symm f) (ones n) = 0 at h
  simpa [dotProduct,ones] using h

theorem asProfile_single {n : Nat} (f : Domain n →ₗ[ℂ] ℂ) (hf : f (ones n) = 0)
    (j : Fin n) :
    (asProfile f hf).val j = f (Pi.single j 1) := by
  have h := LinearEquiv.apply_symm_apply (dotProductEquiv ℂ (Fin n)) f
  have hx := LinearMap.congr_fun h (Pi.single j 1)
  change dotProduct (asProfile f hf).val (Pi.single j 1) = _ at hx
  rwa [dotProduct_single_one] at hx

theorem independentProfiles {n : Nat} {f g : Domain n →ₗ[ℂ] ℂ}
    (hf : f (ones n) = 0) (hg : g (ones n) = 0)
    (h : LinearIndependent ℂ ![f,g]) :
    LinearIndependent ℂ ![asProfile f hf,asProfile g hg] := by
  let e := (dotProductEquiv ℂ (Fin n)).symm
  have h' := h.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  apply LinearIndependent.of_comp (centered n).subtype
  convert h' using 1
  funext i
  fin_cases i <;> rfl

theorem shapes {n : Nat} (L : Submodule ℂ (Mat 4 n))
    (hc : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0)
    (h : ThreeShapes (act L hc) (ones n)) :
    ColCompression L ∨ RowCompression L ∨ MixedCompression L := by
  rcases h with h|h|h
  · obtain ⟨a,b,hab,h⟩ := h
    refine Or.inl ⟨a,b,hab,?_⟩
    intro X hX
    obtain ⟨f,g,hf,hg,h⟩ := h ⟨X,hX⟩
    refine ⟨asProfile f hf,asProfile g hg,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e
  · obtain ⟨f,g,hf,hg,hi,h⟩ := h
    refine Or.inr (Or.inl ⟨asProfile f hf,asProfile g hg,independentProfiles hf hg hi,?_⟩)
    intro X hX
    obtain ⟨a,b,h⟩ := h ⟨X,hX⟩
    refine ⟨a,b,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e
  · obtain ⟨a,b,ha,_,hb,h⟩ := h
    refine Or.inr (Or.inr ⟨a,asProfile b hb,?_,?_⟩)
    · intro hz
      exact ha (Subtype.ext hz)
    intro X hX
    obtain ⟨f,y,hf,h⟩ := h ⟨X,hX⟩
    refine ⟨asProfile f hf,y,?_⟩
    apply Matrix.ext
    intro i j
    have e := congrArg (fun z : centered 4 => z.val i) (h (Pi.single j 1))
    simpa [act_single,outer,Matrix.vecMulVec_apply,asProfile_single,smul_eq_mul,mul_comm] using e

theorem bridge {n : Nat} (n5 : 5 ≤ n) (L : Submodule ℂ (Mat 4 n))
    (large : n ≤ finrank ℂ L)
    (hrows : ∀ X ∈ L, ∀ i, (∑ j, X i j) = 0)
    (hcols : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0)
    (hquad : ∀ X ∈ L, (∑ i, ∑ j, (X i j)^2) = 0)
    (hr : ∀ X ∈ L, X.rank ≤ 2) : First L ∨ Second L := by
  apply postcompression n5 L large hquad
  apply shapes L hcols
  apply classifySpace (act L hcols) (act_inj hcols) (ones n) (act_center hrows hcols)
  · intro X
    rw [act_rank hcols X]
    exact hr X.val X.prop
  · simpa using centered_rank 4 (by decide)
  · omega

end RankModel.Bridge
end SourceLgct309

section SourceLgct312
namespace FixedRow

open Finset

noncomputable def D (n m : ℕ) (g : Fin m → Fin n → ℂ) : ℂ :=
  ∑ f : Fin m ↪ Fin n, ∏ k, g k (f k)

lemma D_zero (n : ℕ) (g : Fin 0 → Fin n → ℂ) : D n 0 g = 1 := by
  simp [D]

lemma sum_not_range {n m : ℕ} (f : Fin m ↪ Fin n) (h : Fin n → ℂ) :
    ∑ i : {i // i ∉ Set.range f}, h i = (∑ i, h i) - ∑ k, h (f k) := by
  rw [eq_sub_iff_add_eq]
  have h1 : ∑ i : {i // i ∉ Set.range f}, h i =
      ∑ i ∈ univ.filter (fun i => i ∉ Set.range f), h i :=
    (Finset.sum_subtype _ (fun i => by simp) h).symm
  have h2 : ∑ k, h (f k) = ∑ i ∈ univ.filter (fun i => i ∈ Set.range f), h i := by
    have : univ.filter (fun i => i ∈ Set.range f) = univ.map f := by
      ext i; simp
    rw [this, Finset.sum_map]
  rw [h1, h2, add_comm]
  exact Finset.sum_filter_add_sum_filter_not _ _ _

lemma prod_update {m n : ℕ} (t : Fin m → Fin n → ℂ) (g0 : Fin n → ℂ) (f : Fin m → Fin n)
    (k0 : Fin m) :
    ∏ k, (Function.update t k0 (t k0 * g0)) k (f k) = (∏ k, t k (f k)) * g0 (f k0) := by
  have : ∀ k, (Function.update t k0 (t k0 * g0)) k (f k) =
      t k (f k) * (if k = k0 then g0 (f k0) else 1) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp
    · simp [hk]
  simp_rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

lemma D_succ (n m : ℕ) (g : Fin (m + 1) → Fin n → ℂ) :
    D n (m + 1) g = (∑ i, g 0 i) * D n m (Fin.tail g) -
      ∑ k : Fin m, D n m (Function.update (Fin.tail g) k (Fin.tail g k * g 0)) := by
  unfold D
  rw [← (Equiv.embeddingFinSucc m (Fin n)).symm.sum_comp, Fintype.sum_sigma]
  simp only [Equiv.coe_embeddingFinSucc_symm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [prod_update]
  have inner : ∀ f : Fin m ↪ Fin n, ∑ i : {i // i ∉ Set.range f}, g 0 i * ∏ k, g k.succ (f k)
      = (∏ k, Fin.tail g k (f k)) * ((∑ i, g 0 i) - ∑ k, g 0 (f k)) := by
    intro f
    rw [← Finset.sum_mul, sum_not_range, mul_comm]; rfl
  simp_rw [inner]
  rw [Finset.sum_comm (f := fun k (f : Fin m ↪ Fin n) => (∏ k, Fin.tail g k (f k)) * g 0 (f k))]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro f _; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring

lemma D_one (n : ℕ) (g : Fin 1 → Fin n → ℂ) : D n 1 g = ∑ i, g 0 i := by
  rw [D_succ, D_zero]; simp

lemma D_two (n : ℕ) (g : Fin 2 → Fin n → ℂ) :
    D n 2 g = (∑ i, g 0 i) * (∑ i, g 1 i) - ∑ i, g 1 i * g 0 i := by
  rw [D_succ, D_one]; simp [D_one, Fin.tail]

lemma msum {n : ℕ} (x : Fin n → ℂ) (c0 c1 c2 c3 c4 : ℂ) :
    ∑ j, (c0 + c1 * x j + c2 * x j ^ 2 + c3 * x j ^ 3 + c4 * x j ^ 4) =
      c0 * n + c1 * (∑ j, x j) + c2 * (∑ j, x j ^ 2) + c3 * (∑ j, x j ^ 3) +
        c4 * (∑ j, x j ^ 4) := by
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma L1 {n : ℕ} (x : Fin n → ℂ) (u : ℂ) :
    ∑ j, (1 + u * x j) = n + u * (∑ j, x j) := by
  have := msum x 1 u 0 0 0
  simp only [zero_mul, add_zero, one_mul] at this
  rw [← this]

lemma L2 {n : ℕ} (x : Fin n → ℂ) (u v : ℂ) :
    ∑ j, (1 + u * x j) * (1 + v * x j) =
      n + (u + v) * (∑ j, x j) + u * v * (∑ j, x j ^ 2) := by
  rw [Finset.sum_congr rfl (fun j _ => show (1 + u * x j) * (1 + v * x j) =
    1 + (u + v) * x j + u * v * x j ^ 2 + 0 * x j ^ 3 + 0 * x j ^ 4 by ring), msum]
  ring

lemma L3 {n : ℕ} (x : Fin n → ℂ) (u v w : ℂ) :
    ∑ j, (1 + u * x j) * ((1 + v * x j) * (1 + w * x j)) =
      n + (u + v + w) * (∑ j, x j) + (u * v + u * w + v * w) * (∑ j, x j ^ 2) +
        u * v * w * (∑ j, x j ^ 3) := by
  rw [Finset.sum_congr rfl (fun j _ => show (1 + u * x j) * ((1 + v * x j) * (1 + w * x j)) =
    1 + (u + v + w) * x j + (u * v + u * w + v * w) * x j ^ 2 + u * v * w * x j ^ 3 +
      0 * x j ^ 4 by ring), msum]
  ring

lemma L4 {n : ℕ} (x : Fin n → ℂ) (u v w z : ℂ) :
    ∑ j, (1 + u * x j) * ((1 + v * x j) * ((1 + w * x j) * (1 + z * x j))) =
      n + (u + v + w + z) * (∑ j, x j) +
        (u * v + u * w + u * z + v * w + v * z + w * z) * (∑ j, x j ^ 2) +
        (u * v * w + u * v * z + u * w * z + v * w * z) * (∑ j, x j ^ 3) +
        u * v * w * z * (∑ j, x j ^ 4) := by
  rw [Finset.sum_congr rfl (fun j _ => show
    (1 + u * x j) * ((1 + v * x j) * ((1 + w * x j) * (1 + z * x j))) =
    1 + (u + v + w + z) * x j + (u * v + u * w + u * z + v * w + v * z + w * z) * x j ^ 2 +
      (u * v * w + u * v * z + u * w * z + v * w * z) * x j ^ 3 + u * v * w * z * x j ^ 4
      by ring), msum]
  ring

def E2 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 * a 2 + a 1 * a 3 + a 2 * a 3
def E3 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 * a 2 + a 0 * a 1 * a 3 + a 0 * a 2 * a 3 + a 1 * a 2 * a 3
def E4 (a : Fin 4 → ℂ) : ℂ := a 0 * a 1 * a 2 * a 3

lemma F_closed (n : ℕ) (a : Fin 4 → ℂ) (x : Fin n → ℂ) (hx : ∑ j, x j = 0) :
    ∑ f : Fin 4 ↪ Fin n, ∏ i, (1 + a i * x (f i)) =
      (n : ℂ) * (n - 1) * (n - 2) * (n - 3) - E2 a * ((n - 2) * (n - 3)) * (∑ j, x j ^ 2) +
        2 * E3 a * (n - 3) * (∑ j, x j ^ 3) +
        E4 a * (3 * (∑ j, x j ^ 2) ^ 2 - 6 * (∑ j, x j ^ 4)) := by
  change D n 4 (fun k j => 1 + a k * x j) = _
  simp [D_succ, D_zero, Fin.sum_univ_succ, Fin.tail, Function.update_apply]
  simp only [mul_assoc, L1, L2, L3, L4, hx, E2, E3, E4]
  ring

lemma iso_core {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0) :
    Module.finrank ℂ K + Module.finrank ℂ K ≤ Module.finrank ℂ W +
      Module.finrank ℂ (LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K)) := by
  set T := W.subtype.dualMap ∘ₗ β.domRestrict K with hT
  set K' : Submodule ℂ W := K.comap W.subtype with hK'
  have hK'r : Module.finrank ℂ K' = Module.finrank ℂ K :=
    (Submodule.comapSubtypeEquivOfLe hKW).finrank_eq
  have hrange : LinearMap.range T ≤ K'.dualAnnihilator := by
    rintro φ ⟨y, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    simp only [hT, LinearMap.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
      LinearMap.domRestrict_apply]
    exact hiso y y.2 w hw
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq K'
  have h2 := LinearMap.finrank_range_add_finrank_ker T
  have h3 := Submodule.finrank_mono hrange
  omega

lemma iso_bound0 {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0)
    (hrad : ∀ y ∈ K, (∀ z ∈ W, β y z = 0) → y = 0) :
    2 * Module.finrank ℂ K ≤ Module.finrank ℂ W := by
  have h := iso_core W K hKW β hiso
  have : LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have : (y : Fin n → ℂ) = 0 := by
      apply hrad y y.2
      intro z hz
      have := LinearMap.congr_fun hy ⟨z, hz⟩
      simpa using this
    exact Subtype.ext this
  rw [this, finrank_bot] at h
  omega

lemma iso_bound1 {n : ℕ} (W K : Submodule ℂ (Fin n → ℂ)) (hKW : K ≤ W)
    (β : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hiso : ∀ y ∈ K, ∀ z ∈ K, β y z = 0) (ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hrad : ∀ y ∈ K, (∀ z ∈ W, β y z = 0) → ψ y = 0 → y = 0) :
    2 * Module.finrank ℂ K ≤ Module.finrank ℂ W + 1 := by
  have h := iso_core W K hKW β hiso
  set R := LinearMap.ker (W.subtype.dualMap ∘ₗ β.domRestrict K)
  set L : R →ₗ[ℂ] ℂ := ψ ∘ₗ K.subtype ∘ₗ R.subtype with hL
  have hker : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro y hy
    have hy0 : ((y : K) : Fin n → ℂ) = 0 := by
      apply hrad _ (y : K).2
      · intro z hz
        have := LinearMap.congr_fun (LinearMap.mem_ker.mp y.2) ⟨z, hz⟩
        rw [LinearMap.comp_apply, LinearMap.dualMap_apply, LinearMap.domRestrict_apply] at this
        simpa using this
      · simpa [hL] using hy
    exact Subtype.ext (Subtype.ext hy0)
  have h4 := LinearMap.finrank_range_add_finrank_ker (K := ℂ) (V := R) L
  rw [hker, finrank_bot] at h4
  have h5 := Submodule.finrank_le (LinearMap.range L)
  rw [Module.finrank_self] at h5
  omega

lemma generic {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) {ι : Type} (s : Finset ι)
    (g : ι → MvPolynomial (Fin n) ℂ)
    (h : ∀ m ∈ s, ∃ x ∈ K, MvPolynomial.eval x (g m) ≠ 0) :
    ∃ x ∈ K, ∀ m ∈ s, MvPolynomial.eval x (g m) ≠ 0 := by
  set b := Module.finBasis ℂ K
  set k := Module.finrank ℂ K
  let v : Fin n → MvPolynomial (Fin k) ℂ :=
    fun i => ∑ l, MvPolynomial.C ((b l : Fin n → ℂ) i) * MvPolynomial.X l
  let pt : (Fin k → ℂ) → (Fin n → ℂ) := fun c => ∑ l, c l • (b l : Fin n → ℂ)
  have hpt : ∀ c, pt c ∈ K := fun c =>
    Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (b l).2)
  have key : ∀ (c : Fin k → ℂ) (p : MvPolynomial (Fin n) ℂ),
      MvPolynomial.eval c (MvPolynomial.aeval v p) = MvPolynomial.eval (pt c) p := by
    intro c p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp =>
      simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X]
      congr 1
      simp [v, pt, Finset.sum_apply, mul_comm]
  have hne : ∀ m ∈ s, MvPolynomial.aeval v (g m) ≠ 0 := by
    intro m hm hz
    obtain ⟨x, hx, hxne⟩ := h m hm
    have hxe : pt (b.repr ⟨x, hx⟩) = x := by
      have h1 := b.sum_repr ⟨x, hx⟩
      calc pt (b.repr ⟨x, hx⟩) = ((∑ l, b.repr ⟨x, hx⟩ l • b l : K) : Fin n → ℂ) := by
            simp only [pt, Submodule.coe_sum, Submodule.coe_smul]
        _ = x := by rw [h1]
    apply hxne
    rw [← hxe, ← key, hz, map_zero]
  have hP : ∏ m ∈ s, MvPolynomial.aeval v (g m) ≠ 0 := Finset.prod_ne_zero_iff.mpr hne
  obtain ⟨c, hc⟩ : ∃ c, MvPolynomial.eval c (∏ m ∈ s, MvPolynomial.aeval v (g m)) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hP (MvPolynomial.funext (fun c => by simpa using hall c))
  refine ⟨pt c, hpt c, fun m hm => ?_⟩
  rw [map_prod] at hc
  rw [← key]
  exact (Finset.prod_ne_zero_iff.mp hc) m hm

def pw {n : ℕ} (r : ℕ) (x : Fin n → ℂ) : ℂ := ∑ j, x j ^ r

lemma N_closed (n : ℕ) :
    ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ) = (n : ℂ) * (n - 1) * (n - 2) * (n - 3) := by
  have := F_closed n 0 0 (by simp)
  simpa [E2, E3, E4] using this

lemma pw_smul {n : ℕ} (r : ℕ) (t : ℂ) (x : Fin n → ℂ) : pw r (t • x) = t ^ r * pw r x := by
  simp [pw, Finset.mul_sum, mul_pow]

lemma coeffs {n : ℕ} (hn : 4 ≤ n) (a : Fin 4 → ℂ) (x : Fin n → ℂ)
    (hx : ∀ t : ℂ, ∑ j, (t • x) j = 0 ∧
      ∑ f : Fin 4 ↪ Fin n, ∏ i, (1 + a i * (t • x) (f i)) = ∑ _f : Fin 4 ↪ Fin n, (1 : ℂ)) :
    E2 a * pw 2 x = 0 ∧ E3 a * pw 3 x = 0 ∧ E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) = 0 := by
  have key : ∀ t : ℂ, -(E2 a * (((n : ℂ) - 2) * ((n : ℂ) - 3)) * pw 2 x) * t ^ 2 +
      2 * E3 a * ((n : ℂ) - 3) * pw 3 x * t ^ 3 +
      E4 a * (3 * pw 2 x ^ 2 - 6 * pw 4 x) * t ^ 4 = 0 := by
    intro t
    obtain ⟨h1, h2⟩ := hx t
    rw [F_closed n a _ h1, N_closed] at h2
    have e2 := pw_smul 2 t x
    have e3 := pw_smul 3 t x
    have e4 := pw_smul 4 t x
    simp only [pw] at e2 e3 e4
    rw [e2, e3, e4] at h2
    simp only [pw]
    linear_combination h2
  have k1 := key 1
  have k2 := key (-1)
  have k3 := key 2
  have hn2 : (n : ℂ) - 2 ≠ 0 := by
    intro h
    have : (n : ℂ) = 2 := by linear_combination h
    norm_cast at this; omega
  have hn3 : (n : ℂ) - 3 ≠ 0 := by
    intro h
    have : (n : ℂ) = 3 := by linear_combination h
    norm_cast at this; omega
  refine ⟨?_, ?_, ?_⟩
  · have hA : (E2 a * pw 2 x) * (((n : ℂ) - 2) * ((n : ℂ) - 3)) = 0 := by
      linear_combination -(k1 + k2 / 3 - k3 / 12)
    exact (mul_eq_zero.mp hA).resolve_right (mul_ne_zero hn2 hn3)
  · have hB : (E3 a * pw 3 x) * (2 * ((n : ℂ) - 3)) = 0 := by
      linear_combination (k1 - k2) / 2
    exact (mul_eq_zero.mp hB).resolve_right (mul_ne_zero two_ne_zero hn3)
  · linear_combination -k1 / 2 + k2 / 6 + k3 / 12

lemma some_E (a : Fin 4 → ℂ) (ha : a ≠ 0) (hs : ∑ i, a i = 0) :
    E2 a ≠ 0 ∨ E3 a ≠ 0 ∨ E4 a ≠ 0 := by
  by_contra h
  simp only [not_or, not_not] at h
  obtain ⟨h2, h3, h4⟩ := h
  simp only [E2, E3, E4] at h2 h3 h4
  rw [Fin.sum_univ_four] at hs
  apply ha
  have z0 : a 0 ^ 4 = 0 := by
    linear_combination (a 0) ^ 3 * hs - (a 0) ^ 2 * h2 + (a 0) * h3 - h4
  have z1 : a 1 ^ 4 = 0 := by
    linear_combination (a 1) ^ 3 * hs - (a 1) ^ 2 * h2 + (a 1) * h3 - h4
  have z2 : a 2 ^ 4 = 0 := by
    linear_combination (a 2) ^ 3 * hs - (a 2) ^ 2 * h2 + (a 2) * h3 - h4
  have z3 : a 3 ^ 4 = 0 := by
    linear_combination (a 3) ^ 3 * hs - (a 3) ^ 2 * h2 + (a 3) * h3 - h4
  funext i
  fin_cases i
  · exact pow_eq_zero_iff (by norm_num) |>.mp z0
  · exact pow_eq_zero_iff (by norm_num) |>.mp z1
  · exact pow_eq_zero_iff (by norm_num) |>.mp z2
  · exact pow_eq_zero_iff (by norm_num) |>.mp z3

def Bf {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun y z => ∑ j, w j * y j * z j + κ * (∑ j, u j * y j) * (∑ j, u j * z j))
    (fun m₁ m₂ z => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring)
    (fun c m z => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ∑ j, w j * (c * m j) * z j = c * ∑ j, w j * m j * z j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ j, u j * (c * m j) = c * ∑ j, u j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2]; ring)
    (fun y n₁ n₂ => by
      simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]; ring)
    (fun c y m => by
      simp only [Pi.smul_apply, smul_eq_mul]
      have e1 : ∑ j, w j * y j * (c * m j) = c * ∑ j, w j * y j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      have e2 : ∑ j, u j * (c * m j) = c * ∑ j, u j * m j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1, e2]; ring)

lemma Bf_apply {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) (y z : Fin n → ℂ) :
    Bf w u κ y z = ∑ j, w j * y j * z j + κ * (∑ j, u j * y j) * (∑ j, u j * z j) := rfl

lemma Bf_single {n : ℕ} (w u : Fin n → ℂ) (κ : ℂ) (y : Fin n → ℂ) (i : Fin n) :
    Bf w u κ y (Pi.single i 1) = w i * y i + κ * (∑ j, u j * y j) * u i := by
  rw [Bf_apply]
  simp [Pi.single_apply]

lemma p2_add {n : ℕ} (x y : Fin n → ℂ) :
    pw 2 (x + y) = pw 2 x + 2 * (∑ j, x j * y j) + pw 2 y := by
  simp only [pw, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

lemma p2_sub {n : ℕ} (x y : Fin n → ℂ) :
    pw 2 (x - y) = pw 2 x - 2 * (∑ j, x j * y j) + pw 2 y := by
  simp only [pw, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def sumL (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun z := ∑ j, z j
  map_add' y z := by simp [Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.mul_sum]

lemma finrank_sumL_ker {n : ℕ} (hn : 1 ≤ n) :
    Module.finrank ℂ (LinearMap.ker (sumL n)) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (sumL n)
  have hr : LinearMap.range (sumL n) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨Pi.single ⟨0, by omega⟩ c, ?_⟩
    simp [sumL]
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
  omega

lemma case2 {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) (hq : ∀ x ∈ K, pw 2 x = 0) :
    2 * Module.finrank ℂ K ≤ n := by
  have h := iso_bound0 ⊤ K le_top (Bf (fun _ => 1) 0 0)
    (fun y hy z hz => by
      have e := p2_add y z
      rw [hq _ (K.add_mem hy hz), hq y hy, hq z hz] at e
      rw [Bf_apply]
      simp only [one_mul, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      linear_combination -e / 2)
    (fun y _ hy => by
      funext i
      have := hy (Pi.single i 1) trivial
      rw [Bf_single] at this
      simpa using this)
  rwa [finrank_top, Module.finrank_fin_fun] at h

lemma case3 {n : ℕ} (K : Submodule ℂ (Fin n → ℂ)) (hq : ∀ x ∈ K, pw 3 x = 0) :
    2 * Module.finrank ℂ K ≤ n := by
  classical
  obtain ⟨x, hxK, hx⟩ := generic K (univ.filter (fun j => ∃ u ∈ K, u j ≠ 0))
    (fun j => MvPolynomial.X j) (fun j hj => by simpa using (Finset.mem_filter.mp hj).2)
  have hx' : ∀ j, (∃ u ∈ K, u j ≠ 0) → x j ≠ 0 := fun j hj => by
    simpa using hx j (Finset.mem_filter.mpr ⟨mem_univ _, hj⟩)
  have h := iso_bound0 ⊤ K le_top (Bf x 0 0)
    (fun y hy z hz => by
      have pol : 6 * ∑ j, x j * y j * z j = pw 3 (x + y + z) - pw 3 (x + y) - pw 3 (x + z)
          - pw 3 (y + z) + pw 3 x + pw 3 y + pw 3 z := by
        simp only [pw, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [hq _ (K.add_mem (K.add_mem hxK hy) hz), hq _ (K.add_mem hxK hy),
        hq _ (K.add_mem hxK hz), hq _ (K.add_mem hy hz), hq x hxK, hq y hy, hq z hz] at pol
      rw [Bf_apply]
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
      linear_combination pol / 6)
    (fun y hyK hy => by
      funext i
      have := hy (Pi.single i 1) trivial
      rw [Bf_single] at this
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero] at this
      by_contra hyi
      have h' : x i = 0 ∨ y i = 0 := by simpa using this
      exact hx' i ⟨y, hyK, hyi⟩ (h'.resolve_right hyi))
  rwa [finrank_top, Module.finrank_fin_fun] at h

lemma case4 {n : ℕ} (hn : 4 ≤ n) (K : Submodule ℂ (Fin n → ℂ))
    (hK0 : ∀ x ∈ K, ∑ j, x j = 0) (hq : ∀ x ∈ K, pw 2 x ^ 2 = 2 * pw 4 x) :
    2 * Module.finrank ℂ K ≤ n := by
  classical

  let g : Bool × Fin n → MvPolynomial (Fin n) ℂ := fun m =>
    cond m.1 ((∑ i, MvPolynomial.X i ^ 2) - MvPolynomial.C 6 * MvPolynomial.X m.2 ^ 2)
      (MvPolynomial.X m.2)
  obtain ⟨x, hxK, hx⟩ := generic K (univ.filter (fun m => ∃ u ∈ K, MvPolynomial.eval u (g m) ≠ 0))
    g (fun m hm => (Finset.mem_filter.mp hm).2)
  have G0 : ∀ j, (∃ u ∈ K, u j ≠ 0) → x j ≠ 0 := fun j ⟨u, hu, huj⟩ => by
    have := hx (false, j) (Finset.mem_filter.mpr ⟨mem_univ _, ⟨u, hu, by simpa [g] using huj⟩⟩)
    simpa [g] using this
  have G1 : ∀ j, (∃ u ∈ K, pw 2 u - 6 * u j ^ 2 ≠ 0) → pw 2 x - 6 * x j ^ 2 ≠ 0 :=
    fun j ⟨u, hu, huj⟩ => by
      have := hx (true, j) (Finset.mem_filter.mpr ⟨mem_univ _, ⟨u, hu, by simpa [g, pw] using huj⟩⟩)
      simpa [g, pw] using this
  set P := pw 2 x with hP
  set d : Fin n → ℂ := fun j => P - 6 * x j ^ 2 with hd

  have quad : ∀ w ∈ K, 4 * (∑ j, x j * w j) ^ 2 + 2 * P * pw 2 w
      - 12 * ∑ j, x j ^ 2 * w j ^ 2 = 0 := by
    intro w hw
    have h1 := hq _ (K.add_mem hxK hw)
    have h2 := hq _ (K.sub_mem hxK hw)
    have h3 := hq x hxK
    have h4 := hq w hw
    rw [p2_add] at h1
    rw [p2_sub] at h2
    have e4 : pw 4 (x + w) + pw 4 (x - w) = 2 * pw 4 x + 12 * (∑ j, x j ^ 2 * w j ^ 2)
        + 2 * pw 4 w := by
      simp only [pw, Pi.add_apply, Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    linear_combination (h1 + h2) / 2 - h3 - h4 + e4

  have hiso : ∀ y ∈ K, ∀ z ∈ K, Bf d x 2 y z = 0 := by
    intro y hy z hz
    have q1 := quad _ (K.add_mem hy hz)
    have q2 := quad y hy
    have q3 := quad z hz
    rw [p2_add] at q1
    have ex : ∑ j, x j * (y + z) j = (∑ j, x j * y j) + ∑ j, x j * z j := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have es : ∑ j, x j ^ 2 * (y + z) j ^ 2 = (∑ j, x j ^ 2 * y j ^ 2) +
        2 * (∑ j, x j ^ 2 * y j * z j) + ∑ j, x j ^ 2 * z j ^ 2 := by
      simp only [Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have ed : ∑ j, d j * y j * z j = P * (∑ j, y j * z j) - 6 * ∑ j, x j ^ 2 * y j * z j := by
      simp only [hd, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [ex, es] at q1
    rw [Bf_apply, ed]
    linear_combination (q1 - q2 - q3) / 4

  have L0 : ∀ y ∈ K, (∀ j, d j * y j = 0) → ∑ j, x j * y j = 0 → y = 0 := by
    intro y hy hdy hxy
    funext j
    by_cases hj : d j = 0
    · by_cases ha : ∃ u ∈ K, u j ≠ 0
      · have hx0 := G0 j ha
        have hz : ∀ u ∈ K, pw 2 u - 6 * u j ^ 2 = 0 := by
          intro u hu
          by_contra hne
          exact G1 j ⟨u, hu, hne⟩ hj
        have e1 := hz _ (K.add_mem hxK hy)
        have e2 := hz x hxK
        have e3 := hz y hy
        rw [p2_add] at e1
        simp only [Pi.add_apply] at e1
        have : x j * y j = 0 := by
          linear_combination (-(e1 - e2 - e3) + 2 * hxy) / 12
        simpa [hx0] using this
      · push Not at ha
        exact ha y hy
    · exact (mul_eq_zero.mp (hdy j)).resolve_left hj

  set W := LinearMap.ker (sumL n) with hW
  have hKW : K ≤ W := fun y hy => by simpa [hW, sumL] using hK0 y hy
  have hsingle : ∀ i j : Fin n, Pi.single i (1 : ℂ) - Pi.single j 1 ∈ W := by
    intro i j
    simp [hW, sumL, Finset.sum_sub_distrib]
  have hv : ∀ y : Fin n → ℂ, (∀ z ∈ W, Bf d x 2 y z = 0) → ∀ i j : Fin n,
      d i * y i + 2 * (∑ l, x l * y l) * x i = d j * y j + 2 * (∑ l, x l * y l) * x j := by
    intro y hy i j
    have := hy _ (hsingle i j)
    rw [map_sub, Bf_single, Bf_single] at this
    linear_combination this
  have hW1 : Module.finrank ℂ W = n - 1 := finrank_sumL_ker (by omega)

  suffices H : ∃ ψ : (Fin n → ℂ) →ₗ[ℂ] ℂ,
      ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) → ψ y = 0 → y = 0 by
    obtain ⟨ψ, hψ⟩ := H
    have := iso_bound1 W K hKW (Bf d x 2) hiso ψ hψ
    omega
  let cL : (Fin n → ℂ) →ₗ[ℂ] ℂ := (Bf x 0 0).flip (fun _ => 1)
  have hcL : ∀ y, cL y = ∑ l, x l * y l := by
    intro y
    simp [cL, Bf_apply]
  by_cases hA : ∃ i1, d i1 = 0
  · obtain ⟨i1, hi1⟩ := hA
    refine ⟨cL, fun y hyK hy hc => ?_⟩
    rw [hcL] at hc
    apply L0 y hyK _ hc
    intro j
    have := hv y hy j i1
    rw [hi1, hc] at this
    linear_combination this
  · push Not at hA
    set i0 : Fin n := ⟨0, by omega⟩
    set A := ∑ i, 1 / d i
    set Bc := ∑ i, x i / d i
    set C := ∑ i, x i ^ 2 / d i
    have hId : P * A - 6 * C = n := by
      have : ∑ i, d i / d i = n := by
        rw [Finset.sum_congr rfl (fun i _ => div_self (hA i))]
        simp
      rw [← this]
      simp only [A, C, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => by
        have := hA i; field_simp; simp only [hd])

    have rel : ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) →
        (∀ i, y i = (Bf d x 2 y (Pi.single i0 1) - 2 * (∑ l, x l * y l) * x i) / d i) ∧
        (∑ l, x l * y l) * (1 + 2 * C) = Bf d x 2 y (Pi.single i0 1) * Bc ∧
        Bf d x 2 y (Pi.single i0 1) * A = 2 * (∑ l, x l * y l) * Bc := by
      intro y hyK hy
      set c := ∑ l, x l * y l with hc
      set μ := Bf d x 2 y (Pi.single i0 1) with hμ
      have hμ' : μ = d i0 * y i0 + 2 * c * x i0 := by rw [hμ, Bf_single]
      have yform : ∀ i, y i = (μ - 2 * c * x i) / d i := by
        intro i
        rw [eq_div_iff (hA i)]
        have := hv y hy i i0
        rw [hμ']
        linear_combination this
      refine ⟨yform, ?_, ?_⟩
      · have : (∑ l, x l * y l) = μ * Bc - 2 * c * C := by
          conv_lhs => rw [Finset.sum_congr rfl (fun i _ => by rw [yform i])]
          simp only [Bc, C, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by
            have := hA i; field_simp)
        linear_combination this
      · have hs := hK0 y hyK
        have : ∑ i, y i = μ * A - 2 * c * Bc := by
          conv_lhs => rw [Finset.sum_congr rfl (fun i _ => by rw [yform i])]
          simp only [A, Bc, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by
            have := hA i; field_simp)
        linear_combination hs - this
    have finish : ∀ y ∈ K, (∀ z ∈ W, Bf d x 2 y z = 0) → ∑ l, x l * y l = 0 →
        Bf d x 2 y (Pi.single i0 1) = 0 → y = 0 := by
      intro y hyK hy hc hμ
      apply L0 y hyK _ hc
      intro j
      have := hv y hy j i0
      rw [Bf_single] at hμ
      rw [hc] at this hμ
      linear_combination this + hμ
    by_cases hBC : Bc ≠ 0 ∨ 1 + 2 * C ≠ 0
    · refine ⟨(Bf d x 2).flip (Pi.single i0 1), fun y hyK hy hμ => ?_⟩
      rw [LinearMap.flip_apply] at hμ
      obtain ⟨-, r1, r2⟩ := rel y hyK hy
      rw [hμ] at r1 r2
      apply finish y hyK hy _ hμ
      rcases hBC with hb | hb
      · have : 2 * (∑ l, x l * y l) * Bc = 0 := by linear_combination -r2
        have := (mul_eq_zero.mp this).resolve_right hb
        simpa using this
      · have : (∑ l, x l * y l) * (1 + 2 * C) = 0 := by linear_combination r1
        exact (mul_eq_zero.mp this).resolve_right hb
    · simp only [not_or, not_not] at hBC
      obtain ⟨hb, hcc⟩ := hBC
      refine ⟨cL, fun y hyK hy hc => ?_⟩
      rw [hcL] at hc
      obtain ⟨-, -, r2⟩ := rel y hyK hy
      rw [hc] at r2
      apply finish y hyK hy hc
      by_cases hA0 : A = 0
      · exfalso
        rw [hA0] at hId
        have h3 : (n : ℂ) = 3 := by linear_combination -hId - 3 * hcc
        norm_cast at h3
        omega
      · have : Bf d x 2 y (Pi.single i0 1) * A = 0 := by linear_combination r2
        exact (mul_eq_zero.mp this).resolve_right hA0

end FixedRow
end SourceLgct312

end PEqualNP.Outside.L_gct_313

namespace PEqualNP.Outside.L_gct_313
open Module

lemma rowEq {x y : Fin 4 → ℂ} (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0)
    (h : ∀ i : Fin 3, x i.castSucc = y i.castSucc) : x = y := by
  have h0 : x 0 = y 0 := h 0
  have h1 : x 1 = y 1 := h 1
  have h2 : x 2 = y 2 := h 2
  rw [Fin.sum_univ_four] at hx hy
  funext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · change x 3 = y 3
    linear_combination hx - hy - h0 - h1 - h2

noncomputable def readThree {n : ℕ} (L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ))
    (U : Submodule ℂ (Fin n → ℂ)) (H : ∀ X ∈ L, ∀ i, X i ∈ U) :
    L →ₗ[ℂ] Fin 3 → U where
  toFun X i := ⟨X.val i.castSucc,H _ X.prop _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma read_inj {n : ℕ} {L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ)} {U : Submodule ℂ (Fin n → ℂ)}
    {H : ∀ X ∈ L, ∀ i, X i ∈ U} (hc : ∀ X ∈ L, ∀ j, (∑ i, X i j) = 0) :
    Function.Injective (readThree L U H) := by
  intro X Y eq
  apply Subtype.ext
  funext i j
  refine congrFun (rowEq (x := fun r => X.val r j) (y := fun r => Y.val r j) (hc _ X.prop j) (hc _ Y.prop j) ?_) i
  intro r
  exact congrArg (fun u : U => u.val j) (congrFun eq r)

lemma firstImpossible {n : ℕ} (hn : 6 ≤ n) {L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ)}
    (large : n ≤ finrank ℂ L) (valid : Moments.Level L) (h : RankModel.Form.First L) : False := by
  obtain ⟨a,K,ha,hsize,hK⟩ := h
  change 2 * finrank ℂ L + 1 ≤ 2 * finrank ℂ K + n at hsize
  have hdim : 0 < finrank ℂ K := by omega
  obtain ⟨x,hx,hx0⟩ : ∃ x ∈ K, x ≠ 0 := by
    obtain ⟨w,hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hdim
    exact ⟨w.val,w.prop,fun e => hw (Subtype.ext e)⟩
  obtain ⟨j,hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra! h
    exact hx0 (funext h)
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra! h
    exact ha (funext h)
  have cs := (valid _ (hK x hx)).2.1 j
  change (∑ i, a i * x j) = 0 at cs
  rw [← Finset.sum_mul] at cs
  have hsa := (mul_eq_zero.mp cs).resolve_right hj
  have hs (w) (hw : w ∈ K) : (∑ j, w j) = 0 := by
    have z := (valid _ (hK w hw)).1 i
    change (∑ j, a i * w j) = 0 at z
    rw [← Finset.mul_sum] at z
    exact (mul_eq_zero.mp z).resolve_left hi
  have test (w) (hw : w ∈ K) := FixedRow.coeffs (by omega : 4 ≤ n) a w (fun t =>
    ⟨hs _ (K.smul_mem t hw),(valid _ (hK _ (K.smul_mem t hw))).2.2⟩)
  have bound : 2 * finrank ℂ K ≤ n := by
    rcases FixedRow.some_E a ha hsa with h2 | h3 | h4
    · exact FixedRow.case2 K (fun w hw => (mul_eq_zero.mp (test w hw).1).resolve_left h2)
    · exact FixedRow.case3 K (fun w hw => (mul_eq_zero.mp (test w hw).2.1).resolve_left h3)
    · apply FixedRow.case4 (by omega) K hs
      intro w hw
      have e := (mul_eq_zero.mp (test w hw).2.2).resolve_left h4
      linear_combination e / 3
  omega

lemma secondImpossible {n : ℕ} (hn : 6 ≤ n) {L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ)}
    (large : n ≤ finrank ℂ L) (valid : Moments.Level L) (h : RankModel.Form.Second L) : False := by
  classical
  obtain ⟨U,dimU,hu,hrows⟩ := h
  let D := readThree L U hrows
  have inj : Function.Injective D := read_inj (fun X hX => (valid X hX).2.1)
  have dim3 : finrank ℂ (Fin 3 → U) = 6 := by simp [Module.finrank_pi_fintype,dimU]
  have bound := LinearMap.finrank_le_finrank_of_injective inj
  rw [dim3] at bound
  have sur : Function.Surjective D := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj inj,dim3]
    omega
  let a : Fin 4 → ℂ := ![1,1,1,-3]
  have sumA : ∑ i, a i = 0 := by norm_num [Fin.sum_univ_four,a]
  have allU (w : Fin n → ℂ) (hw : w ∈ U) : (fun i j => a i * w j) ∈ L := by
    obtain ⟨X,eqX⟩ := sur (fun _ => (⟨w,hw⟩ : U))
    have he (r : Fin 3) : X.val r.castSucc = w := congrArg Subtype.val (congrFun eqX r)
    have same : X.val = fun i j => a i * w j := by
      funext i j
      apply congrFun (rowEq (x := fun r => X.val r j) (y := fun r => a r * w j) ((valid _ X.prop).2.1 j) _ _) i
      · rw [← Finset.sum_mul,sumA,zero_mul]
      · intro r
        rw [he]
        fin_cases r <;> simp [a]
    exact same ▸ X.prop
  have powers (w : Fin n → ℂ) (hw : w ∈ U) := FixedRow.coeffs (by omega : 4 ≤ n) a w (fun t =>
    ⟨(hu _ (U.smul_mem t hw)).1,(valid _ (allU _ (U.smul_mem t hw))).2.2⟩)
  have e2 : FixedRow.E2 a = -6 := by norm_num [FixedRow.E2,a]
  have e3 : FixedRow.E3 a = -8 := by norm_num [FixedRow.E3,a]
  have e4 : FixedRow.E4 a = -3 := by norm_num [FixedRow.E4,a]
  have small := FromGct.L067 n 4 U (by decide) (by
    intro j lo hi w hw
    obtain ⟨h2,h3,h4⟩ := powers w hw
    rw [e2] at h2
    rw [e3] at h3
    rw [e4] at h4
    have z2 : FixedRow.pw 2 w = 0 := (mul_eq_zero.mp h2).resolve_left (by norm_num)
    have z3 : FixedRow.pw 3 w = 0 := (mul_eq_zero.mp h3).resolve_left (by norm_num)
    have z4 : FixedRow.pw 4 w = 0 := by rw [z2] at h4; linear_combination h4 / 18
    rcases (show j = 2 ∨ j = 3 ∨ j = 4 by omega) with rfl | rfl | rfl
    · exact z2
    · exact z3
    · exact z4)
  rw [dimU] at small
  omega

lemma finish {n : ℕ} (hn : 6 ≤ n) (L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ))
    (valid : Moments.Level L) (large : n ≤ finrank ℂ L) : ∃ X ∈ L, X.rank = 3 := by
  classical
  have cols := fun X hX => (valid X hX).2.1
  by_contra none
  have ranks (X : Matrix (Fin 4) (Fin n) ℂ) (hX : X ∈ L) : X.rank ≤ 2 := by
    have upper := (LinearMap.range (RankModel.Bridge.act L cols (⟨X,hX⟩ : L))).finrank_le
    rw [RankModel.Bridge.act_rank cols,RankModel.Form.centered_rank 4 (by decide)] at upper
    have cap : X.rank ≤ 3 := upper
    have miss : X.rank ≠ 3 := fun e => none ⟨X,hX,e⟩
    omega
  have quad (X : Matrix (Fin 4) (Fin n) ℂ) (hX : X ∈ L) : (∑ i, ∑ j, (X i j)^2) = 0 := by
    rw [Finset.sum_comm]
    simpa only [Fin.sum_univ_four,Moments.sqSum] using (Moments.forms (by omega : 4 ≤ n) valid hX).1
  rcases RankModel.Bridge.bridge (by omega : 5 ≤ n) L large (fun X hX => (valid X hX).1) cols quad ranks with h | h
  · exact firstImpossible hn large valid h
  · exact secondImpossible hn large valid h

end PEqualNP.Outside.L_gct_313

theorem PEqualNP.Outside.L_gct_313 : (∀ (n : ℕ), 6 ≤ n → ∀ L : Submodule ℂ (Matrix (Fin 4) (Fin n) ℂ),
  (∀ X ∈ L, (∀ i, (∑ j, X i j) = 0) ∧ (∀ j, (∑ i, X i j) = 0) ∧
    (∑ f : Fin 4 ↪ Fin n, ∏ i : Fin 4, (1 + X i (f i))) =
      (∑ _f : Fin 4 ↪ Fin n, (1 : ℂ))) →
  n ≤ Module.finrank ℂ L →
  ∃ X ∈ L, X.rank = 3) := by
  intro n hn L valid large
  exact PEqualNP.Outside.L_gct_313.finish hn L valid large
