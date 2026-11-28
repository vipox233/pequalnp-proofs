import Mathlib

namespace PEqualNP.Outside.L_lib_1092_aux

open MvPolynomial

abbrev Poly (α : Type) := MvPolynomial α ℂ

noncomputable def points {G E : Type} (m : G → Poly E) : Set (G → ℂ) :=
  zeroLocus ℂ (RingHom.ker (aeval (R := ℂ) m))

lemma component_aeval {G E : Type} {n : ℕ} (hn : n ≠ 0) (m : G → Poly E)
    (hm : ∀ j, (m j).IsHomogeneous n) (r : ℕ) (p : Poly G) :
    homogeneousComponent (n * r) (aeval m p) = aeval m (homogeneousComponent r p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
      have h : (monomial a c : Poly G).IsHomogeneous a.degree :=
        isHomogeneous_monomial c rfl
      rw [homogeneousComponent_of_mem h, homogeneousComponent_of_mem (h.aeval m hm)]
      by_cases e : r = a.degree
      · simp [e]
      · rw [if_neg e, if_neg (fun he => e (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) he)),
          map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

lemma points_smul {G E : Type} {n : ℕ} (hn : n ≠ 0) (m : G → Poly E)
    (hm : ∀ j, (m j).IsHomogeneous n) {z : G → ℂ} (hz : z ∈ points m) (c : ℂ) :
    c • z ∈ points m := by
  classical
  intro p hp
  have hp' : aeval m p = 0 := hp
  rw [← sum_homogeneousComponent p, map_sum]
  apply Finset.sum_eq_zero
  intro r _
  have hr : homogeneousComponent r p ∈ RingHom.ker (aeval m) := by
    change aeval m (homogeneousComponent r p) = 0
    rw [← component_aeval hn m hm, hp', map_zero]
  have hz' : aeval z (homogeneousComponent r p) = 0 := hz _ hr
  rw [(homogeneousComponent_isHomogeneous r p).aeval_smul, hz', smul_zero]

lemma eval_generators_mem_points {G E : Type} (m : G → Poly E) (a : E → ℂ) :
    (fun j => eval a (m j)) ∈ points m := by
  intro p hp
  have hp' : aeval m p = 0 := hp
  change aeval (fun j => aeval a (m j)) p = 0
  rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply, hp', map_zero]

def separatingZero {G E T : Type} (m : G → Poly E) (f : T → Poly G) : Prop :=
  ∀ z ∈ points m, (∀ j, aeval z (f j) = 0) → z = 0

lemma shrink_zero_forms {G E : Type} (m : G → Poly E) {k : ℕ}
    (f : Fin (k + 1) → Poly G) (hf : ∀ j, (f j).IsHomogeneous 1)
    (hz : separatingZero m f)
    (hrel : ∃ p : Poly (Fin (k + 1)), p ≠ 0 ∧
      (∃ r, p.IsHomogeneous r) ∧ aeval (fun j => aeval m (f j)) p = 0) :
    ∃ g : Fin k → Poly G, (∀ j, (g j).IsHomogeneous 1) ∧ separatingZero m g := by
  classical
  obtain ⟨p, hp, ⟨r, hr⟩, hp0⟩ := hrel
  have hv : ∃ v : Fin (k + 1) → ℂ, eval v p ≠ 0 := by
    by_contra! h
    apply hp
    apply MvPolynomial.funext_set (s := fun _ => Set.univ) (fun _ => Set.infinite_univ)
    intro x _
    simp [h]
  obtain ⟨v, hv⟩ := hv
  by_cases hV : v = 0
  · -- A nonzero value at the origin would be a nonzero constant relation.
    by_cases hr0 : r = 0
    · subst r
      have hC := homogeneousComponent_eq_self hr
      rw [homogeneousComponent_zero] at hC
      rw [← hC, aeval_C, algebraMap_eq, MvPolynomial.C_eq_zero] at hp0
      exact (hp (hC ▸ (show C (p.coeff 0) = 0 by rw [hp0, map_zero]))).elim
    · have h := hr.eval_smul (0 : ℂ) v
      have he : (0 : ℂ) • v = v := by rw [zero_smul, hV]
      rw [he, zero_pow hr0, zero_mul] at h
      exact (hv h).elim
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hV (funext h)
  refine ⟨fun j => f (i.succAbove j) - C (v (i.succAbove j) / v i) * f i,
    fun j => (hf _).sub ((hf _).C_mul _), ?_⟩
  intro z hz' hg
  have hline : (fun j => aeval z (f j)) = (aeval z (f i) / v i) • v := by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · simp [div_mul_cancel₀ _ hi]
    · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hji
      have ha := hg a
      simp only [map_sub, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
        sub_eq_zero] at ha
      simpa [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm,
        mul_assoc] using ha
  have hpz : eval (fun j => aeval z (f j)) p = 0 := by
    have hmem : aeval f p ∈ RingHom.ker (aeval m) := by
      change aeval m (aeval f p) = 0
      rwa [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    have h := hz' _ hmem
    change aeval (fun j => aeval z (f j)) p = 0
    simpa only [← MvPolynomial.comp_aeval, AlgHom.comp_apply] using h
  rw [hline, hr.eval_smul, mul_eq_zero] at hpz
  have hc : aeval z (f i) = 0 :=
    (div_eq_zero_iff.mp (eq_zero_of_pow_eq_zero (hpz.resolve_right hv))).resolve_right hi
  apply hz z hz'
  intro j
  have hj := congrFun hline j
  simpa [hc] using hj

noncomputable abbrev presented {G E : Type} (m : G → Poly E) : Subalgebra ℂ (Poly E) :=
  (aeval (R := ℂ) m).range

noncomputable def normalMap {G E T : Type} (m : G → Poly E) (f : T → Poly G) :
    Poly T →ₐ[ℂ] presented m :=
  aeval (fun j => (aeval m).rangeRestrict (f j))

lemma normal_finite {G E T : Type} [Finite G] [Fintype T] {n : ℕ}
    (hn : n ≠ 0) (m : G → Poly E) (hm : ∀ j, (m j).IsHomogeneous n)
    (f : T → Poly G) (hf : ∀ j, (f j).IsHomogeneous 1) (hz : separatingZero m f) :
    letI : Algebra (Poly T) (presented m) := (normalMap m f).toRingHom.toAlgebra
    Module.Finite (Poly T) (presented m) := by
  classical
  let L : Poly G →ₐ[ℂ] presented m := (aeval m).rangeRestrict
  let b := normalMap m f
  letI : Algebra (Poly T) (presented m) := b.toRingHom.toAlgebra
  let I : Ideal (Poly G) := RingHom.ker (aeval (R := ℂ) m)
  let J : Ideal (Poly G) := I ⊔ Ideal.span (Set.range f)
  have hX (i : G) : X i ∈ J.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ) J]
    intro z hz'
    have hzI : z ∈ points m := fun p hp => hz' p (Ideal.mem_sup_left hp)
    have hzF (j : T) : aeval z (f j) = 0 :=
      hz' _ (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_range_self j)))
    rw [hz z hzI hzF, aeval_X]
    rfl
  obtain ⟨N, hN⟩ := J.exists_radical_pow_le_of_fg J.radical.fg_of_isNoetherianRing
  let U : Set (G →₀ ℕ) := {a | a.degree ≤ N}
  let S : Set (presented m) := (fun a : G →₀ ℕ => L (monomial a 1)) '' U
  let W : Submodule (Poly T) (presented m) := Submodule.span _ S
  have hmon (a : G →₀ ℕ) (c : ℂ) (ha : N ≤ a.degree) : monomial a c ∈ J := by
    have hx : (∏ i ∈ a.support, (X i : Poly G) ^ a i) ∈ J.radical ^ a.degree := by
      rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Ideal.prod_mem_prod (fun i _ => Ideal.pow_mem_pow (hX i) _)
    rw [monomial_eq]
    exact J.mul_mem_left _ (hN (Ideal.pow_le_pow_right ha hx))
  have hhom : ∀ k : ℕ, ∀ p : Poly G, p.IsHomogeneous k → L p ∈ W := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro p hp
      by_cases hk : k ≤ N
      · rw [← p.support_sum_monomial_coeff, map_sum]
        apply W.sum_mem
        intro a ha
        have hdeg : a.degree = k := by
          rw [Finsupp.degree_eq_weight_one]
          exact hp (mem_support_iff.mp ha)
        have hu : L (monomial a 1) ∈ W :=
          Submodule.subset_span ⟨a, show a.degree ≤ N from hdeg.trans_le hk, rfl⟩
        have hs := W.smul_mem (C (p.coeff a) : Poly T) hu
        change b (C (p.coeff a)) * L (monomial a 1) ∈ W at hs
        have he (c : ℂ) : b (C c) = L (C c) := by
          exact (MvPolynomial.algHom_C b c).trans (MvPolynomial.algHom_C L c).symm
        rwa [he, ← map_mul, C_mul_monomial, mul_one] at hs
      · have hkp : 1 ≤ k := by omega
        have hpJ : p ∈ J := by
          rw [← p.support_sum_monomial_coeff]
          apply J.sum_mem
          intro a ha
          have hdeg : a.degree = k := by
            rw [Finsupp.degree_eq_weight_one]
            exact hp (mem_support_iff.mp ha)
          exact hmon a _ ((Nat.le_of_lt (Nat.lt_of_not_ge hk)).trans_eq hdeg.symm)
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hpJ
        obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv
        have hdecomp : p = homogeneousComponent k u +
            ∑ i, homogeneousComponent (k - 1) (c i) * f i := by
          have he := congrArg (homogeneousComponent k) huv
          rw [homogeneousComponent_eq_self hp, map_add, ← hc, map_sum] at he
          refine he.symm.trans (congrArg (homogeneousComponent k u + ·) ?_)
          apply Finset.sum_congr rfl
          intro i _
          exact weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right (hf i) hkp
        have hu0 : L (homogeneousComponent k u) = 0 := by
          apply Subtype.ext
          change aeval m (homogeneousComponent k u) = 0
          change aeval m u = 0 at hu
          rw [← component_aeval hn m hm, hu, map_zero]
        rw [hdecomp, map_add, hu0, zero_add, map_sum]
        apply W.sum_mem
        intro i _
        have hi := W.smul_mem (X i : Poly T) (ih (k - 1) (by omega)
          (homogeneousComponent (k - 1) (c i)) (homogeneousComponent_isHomogeneous _ _))
        change b (X i) * L (homogeneousComponent (k - 1) (c i)) ∈ W at hi
        rw [show b (X i) = L (f i) from aeval_X _ _, ← map_mul, mul_comm] at hi
        exact hi
  have hW : W = ⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro x
    obtain ⟨p, rfl⟩ := (aeval m).rangeRestrict_surjective x
    change L p ∈ W
    rw [← sum_homogeneousComponent p, map_sum]
    exact W.sum_mem fun i _ => hhom i _ (homogeneousComponent_isHomogeneous _ _)
  exact Module.finite_def.mpr (hW ▸ Submodule.fg_def.mpr
    ⟨S, (Finsupp.finite_of_degree_le N).image _, rfl⟩)

lemma normal_injective {G E : Type} [Finite G] {n d : ℕ}
    (hn : n ≠ 0) (m : G → Poly E) (hm : ∀ j, (m j).IsHomogeneous n)
    (hd : (d : Cardinal) ≤ Algebra.trdeg ℂ (presented m))
    (f : Fin d → Poly G) (hf : ∀ j, (f j).IsHomogeneous 1) (hz : separatingZero m f) :
    Function.Injective (normalMap m f) := by
  let x : Fin d → presented m := fun j => (aeval m).rangeRestrict (f j)
  let b := normalMap m f
  letI : Algebra (Poly (Fin d)) (presented m) := b.toRingHom.toAlgebra
  let B := Algebra.adjoin ℂ (Set.range x)
  have hB : b.range = B := MvPolynomial.aeval_range x
  let b' : Poly (Fin d) →ₐ[ℂ] B := b.codRestrict B (fun t => hB ▸ (b.rangeRestrict t).property)
  letI : Algebra (Poly (Fin d)) B := b'.toRingHom.toAlgebra
  letI : IsScalarTower (Poly (Fin d)) B (presented m) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Module.Finite (Poly (Fin d)) (presented m) := normal_finite hn m hm f hf hz
  letI : Algebra.IsAlgebraic B (presented m) :=
    ⟨fun z => (IsIntegral.of_finite (Poly (Fin d)) z).tower_top.isAlgebraic⟩
  letI : FaithfulSMul ℂ (presented m) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  have ht := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℂ x (by simpa using hd)
  exact algebraicIndependent_iff_injective_aeval.mp ht.1

lemma initial_zero_forms {G E : Type} [Fintype G] {n d : ℕ}
    (hn : n ≠ 0) (m : G → Poly E) (hm : ∀ j, (m j).IsHomogeneous n)
    (hd : Algebra.trdeg ℂ (presented m) ≤ (d : Cardinal)) :
    ∃ f : Fin d → Poly G, (∀ j, (f j).IsHomogeneous 1) ∧ separatingZero m f := by
  classical
  let good (k : ℕ) := ∃ f : Fin k → Poly G, (∀ j, (f j).IsHomogeneous 1) ∧ separatingZero m f
  have hstep (k : ℕ) (hk : d ≤ k) (hf : good (k + 1)) : good k := by
    obtain ⟨f, hh, hz⟩ := hf
    apply shrink_zero_forms m f hh hz
    let x : Fin (k + 1) → presented m := fun j => (aeval m).rangeRestrict (f j)
    have hdep : ¬ AlgebraicIndependent ℂ x := by
      intro hi
      have hb : (↑(k + 1) : Cardinal.{0}) ≤ ↑d := by
        simpa using hi.cardinalMk_le_trdeg.trans hd
      exact (Nat.not_succ_le_self k) ((by exact_mod_cast hb : k + 1 ≤ d).trans hk)
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero] at hdep
    push_neg at hdep
    obtain ⟨p, hp0, hp⟩ := hdep
    obtain ⟨r, hr⟩ : ∃ r, homogeneousComponent r p ≠ 0 := by
      by_contra! he
      exact hp (by rw [← sum_homogeneousComponent p]; simp [he])
    refine ⟨homogeneousComponent r p, hr, ⟨r, homogeneousComponent_isHomogeneous _ _⟩, ?_⟩
    let y : Fin (k + 1) → Poly E := fun j => aeval m (f j)
    have hhy (j) : (y j).IsHomogeneous n := by simpa only [mul_one] using (hh j).aeval m hm
    have hx0 : aeval y p = 0 := by
      have hcomp : (presented m).val.comp (aeval x) = aeval y := by
        apply MvPolynomial.algHom_ext
        intro i
        rw [AlgHom.comp_apply, aeval_X, aeval_X]
        rfl
      rw [← hcomp, AlgHom.comp_apply, hp0, map_zero]
    change aeval y (homogeneousComponent r p) = 0
    rw [← component_aeval hn y hhy, hx0, map_zero]
  have hreduce (k : ℕ) (hk : d ≤ k) : good k → good d := by
    induction k, hk using Nat.le_induction with
    | base => exact id
    | succ k hk ih => exact fun h => ih (hstep k hk h)
  apply hreduce (d + Fintype.card G) (Nat.le_add_right _ _)
  let e := Fintype.equivFin G
  refine ⟨Fin.addCases (fun _ : Fin d => 0) (fun j : Fin (Fintype.card G) => X (e.symm j)),
    ?_, ?_⟩
  · intro j
    induction j using Fin.addCases <;> simp [isHomogeneous_zero, isHomogeneous_X]
  · intro z _ hz
    funext j
    have hh := hz (Fin.natAdd d (e j))
    simpa only [Fin.addCases_right, e.symm_apply_apply, aeval_X, Pi.zero_apply] using hh


open MvPolynomial

-- The finite-grid transfer and denominator clearing below are adapted from
-- lean/PEqualNP/Outside/L_lib_552.lean at 78e3e76d72650de484b81008d5e708c7d564ea23.
-- Here the variables are renamed along a finite-type equivalence, and powers of a
-- primitive root give the injective parametrization of the grid.
open scoped Classical in
theorem grid_bad_count {E : Type*} [Fintype E] {q : ℕ} {ζ : ℂ}
    (p : MvPolynomial E ℂ) (hp : p ≠ 0) (hζ : IsPrimitiveRoot ζ q) (hq : 0 < q) :
    ((Finset.univ : Finset (E → Fin q)).filter
      (fun s => eval (fun i => ζ ^ (s i).val) p = 0)).card * q
        ≤ p.totalDegree * Fintype.card (E → Fin q) := by
  let e : E ≃ Fin (Fintype.card E) := Fintype.equivFin E
  let g : Fin q → ℂ := fun a => ζ ^ a.val
  let S : Finset ℂ := Finset.univ.image g
  let P : MvPolynomial (Fin (Fintype.card E)) ℂ := rename e p
  have hg : Function.Injective g := by
    intro a b hab
    exact Fin.ext (hζ.pow_inj a.isLt b.isLt hab)
  have hS : S.card = q := by
    change (Finset.univ.image g).card = q
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  have hP : P ≠ 0 := by
    intro h
    exact hp ((rename_eq_zero_iff_of_injective p e.injective).mp h)
  have hcard : ((Finset.univ : Finset (E → Fin q)).filter
      (fun s => eval (fun i => ζ ^ (s i).val) p = 0)).card ≤
      ((Fintype.piFinset fun _ : Fin (Fintype.card E) => S).filter
        (fun f => eval f P = 0)).card := by
    apply Finset.card_le_card_of_injOn (fun s j => g (s (e.symm j)))
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_univ,
        true_and, Fintype.mem_piFinset] at hs ⊢
      refine ⟨fun j => Finset.mem_image.mpr ⟨s (e.symm j), Finset.mem_univ _, rfl⟩, ?_⟩
      change eval (fun j => g (s (e.symm j))) (rename e p) = 0
      rw [eval_rename]
      simpa only [Function.comp_def, Equiv.symm_apply_apply, g] using hs
    · intro s _ t _ hst
      funext i
      apply hg
      simpa only [Equiv.symm_apply_apply] using congrFun hst (e i)
  have hSZ := schwartz_zippel_totalDegree hP S
  have hpos : (0 : NNRat) < S.card := by
    rw [hS]
    exact_mod_cast hq
  rw [div_le_div_iff₀ (pow_pos hpos _) hpos] at hSZ
  have hSZ' : ((Fintype.piFinset fun _ : Fin (Fintype.card E) => S).filter
      (fun f => eval f P = 0)).card * S.card ≤ P.totalDegree * S.card ^ Fintype.card E := by
    exact_mod_cast hSZ
  rw [hS] at hSZ'
  rw [Fintype.card_fun, Fintype.card_fin]
  exact (Nat.mul_le_mul_right q hcard).trans
    (hSZ'.trans (Nat.mul_le_mul_right _ (totalDegree_rename_le e p)))

open scoped Classical in
theorem grid_simultaneous_avoidance {E ι : Type*} [Fintype E] {q : ℕ} {ζ : ℂ}
    (T : Finset ι) (p : ι → MvPolynomial E ℂ) (hp : ∀ i ∈ T, p i ≠ 0)
    (hζ : IsPrimitiveRoot ζ q) (hq : 0 < q) (hdeg : (∑ i ∈ T, (p i).totalDegree) < q) :
    ∃ s : E → Fin q, ∀ i ∈ T, eval (fun e => ζ ^ (s e).val) (p i) ≠ 0 := by
  let P := ∏ i ∈ T, p i
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr hp
  have hPdeg : P.totalDegree < q := (totalDegree_finsetProd T p).trans_lt hdeg
  have hex : ∃ s : E → Fin q, eval (fun e => ζ ^ (s e).val) P ≠ 0 := by
    by_contra hn
    have hall (s : E → Fin q) : eval (fun e => ζ ^ (s e).val) P = 0 := by
      by_contra hs
      exact hn ⟨s, hs⟩
    have hfilter : (Finset.univ : Finset (E → Fin q)).filter
        (fun s => eval (fun e => ζ ^ (s e).val) P = 0) = Finset.univ :=
      Finset.filter_eq_self.mpr fun s _ => hall s
    have hb := grid_bad_count P hP hζ hq
    rw [hfilter, Finset.card_univ] at hb
    have hpos : 0 < Fintype.card (E → Fin q) := by
      rw [Fintype.card_fun, Fintype.card_fin]
      exact pow_pos hq _
    exact (not_le_of_gt hPdeg) (Nat.le_of_mul_le_mul_right
      ((Nat.mul_comm q (Fintype.card (E → Fin q))).trans_le hb) hpos)
  obtain ⟨s, hs⟩ := hex
  have hprod : (∏ i ∈ T, eval (fun e => ζ ^ (s e).val) (p i)) ≠ 0 := by
    simpa only [P, map_prod] using hs
  exact ⟨s, Finset.prod_ne_zero_iff.mp hprod⟩


open scoped BigOperators

/-- A subspace of a finite coordinate space is separated by exactly its dimension many
coordinates, with no repetitions. -/
theorem toric_coordinates {E : Type*} [Fintype E] (V : Submodule ℚ (E → ℚ)) :
    ∃ a : Fin (Module.finrank ℚ V) ↪ E,
      Function.Injective (fun x : V => fun i => (x : E → ℚ) (a i)) := by
  classical
  let b := (Pi.basisFun ℚ E).dualBasis
  let r := V.subtype.dualMap
  let v : E → Module.Dual ℚ V := r ∘ b
  have hv (i : E) (x : V) : v i x = (x : E → ℚ) i := by
    change (V.subtype.dualMap ((Pi.basisFun ℚ E).dualBasis i)) x = _
    rw [LinearMap.dualMap_apply, Module.Basis.dualBasis_apply, Pi.basisFun_repr]
    rfl
  have hall : Submodule.span ℚ (Set.range v) = ⊤ := by
    change Submodule.span ℚ (Set.range (r ∘ b)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (LinearMap.dualMap_surjective_of_injective V.injective_subtype)
  obtain ⟨ι, a, ha, hs, hi⟩ := exists_linearIndependent' ℚ v
  letI : Finite ι := Finite.of_injective a ha
  letI : Fintype ι := Fintype.ofFinite ι
  have hs' : Submodule.span ℚ (Set.range (v ∘ a)) = ⊤ := hs.trans hall
  let c : Module.Basis ι ℚ (Module.Dual ℚ V) := Module.Basis.mk hi (ge_of_eq hs')
  have hc : Fintype.card ι = Module.finrank ℚ V := by
    simpa using (Module.finrank_eq_card_basis c).symm
  let e : ι ≃ Fin (Module.finrank ℚ V) := Fintype.equivFinOfCardEq hc
  refine ⟨e.symm.toEmbedding.trans ⟨a, ha⟩, ?_⟩
  intro x y hxy
  have hspan (f : Module.Dual ℚ V) : f x = f y := by
    have hf : f ∈ Submodule.span ℚ (Set.range (v ∘ a)) := by
      simp only [hs', Submodule.mem_top]
    refine Submodule.span_induction (p := fun g _ => g x = g y) ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨i, rfl⟩
      have h := congrFun hxy (e i)
      change (x : E → ℚ) (a (e.symm (e i))) = (y : E → ℚ) (a (e.symm (e i))) at h
      simpa only [Function.comp_apply, hv, Equiv.symm_apply_apply] using h
    · simp
    · intro p q _ _ hp hq
      simp only [LinearMap.add_apply, hp, hq]
    · intro t p _ hp
      simp only [LinearMap.smul_apply, hp]
  apply Subtype.ext
  funext i
  simpa only [hv] using hspan (v i)

/-- Regard a natural exponent vector as a rational vector. -/
def toricRat {E : Type*} (x : E →₀ ℕ) : E → ℚ := fun e => (x e : ℚ)

/-- Nonnegative integral vectors of mass at most `N` in a `d`-dimensional subspace
inject into multisets of size `N` on `d+1` symbols; the extra symbol records slack. -/
theorem toric_card_le_choose {E T : Type*} [Fintype E] (V : Submodule ℚ (E → ℚ))
    (N : ℕ) (u : T → E →₀ ℕ) (hu : Function.Injective u)
    (hV : ∀ x, toricRat (u x) ∈ V) (hN : ∀ x, ∑ i, u x i ≤ N) :
    Finite T ∧ Nat.card T ≤ Nat.choose (N + Module.finrank ℚ V) (Module.finrank ℚ V) := by
  classical
  obtain ⟨a, ha⟩ := toric_coordinates V
  let d := Module.finrank ℚ V
  let p (x : T) (i : Fin d) := u x (a i)
  have hp (x : T) : ∑ i, p x i ≤ N := by
    calc
      ∑ i, p x i = ∑ j ∈ Finset.univ.map a, u x j := by
        rw [Finset.sum_map]
      _ ≤ ∑ j, u x j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ ≤ N := hN x
  let padded (x : T) : {f : Fin (d + 1) → ℕ // ∑ i, f i = N} :=
    ⟨Fin.cons (N - ∑ i, p x i) (p x), by
      rw [Fin.sum_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ]
      exact Nat.sub_add_cancel (hp x)⟩
  have hinj : Function.Injective padded := by
    intro x y h
    apply hu
    have he : (⟨toricRat (u x), hV x⟩ : V) = ⟨toricRat (u y), hV y⟩ := by
      apply ha
      funext i
      have hh := congrFun (congrArg Subtype.val h) i.succ
      have hh' : p x i = p y i := by simpa [padded] using hh
      exact congrArg (fun t : ℕ => (t : ℚ)) hh'
    ext j
    have hh : (u x j : ℚ) = (u y j : ℚ) := congrFun (congrArg Subtype.val he) j
    exact_mod_cast hh
  let m := (Sym.equivNatSumOfFintype (Fin (d + 1)) N).symm
  have hm : Function.Injective (m ∘ padded) := m.injective.comp hinj
  refine ⟨Finite.of_injective _ hm, ?_⟩
  calc
    Nat.card T ≤ Nat.card (Sym (Fin (d + 1)) N) :=
      Nat.card_le_card_of_injective _ hm
    _ = Nat.choose (N + d) d := by
      rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_choose, Fintype.card_fin]
      rw [show d + 1 + N - 1 = N + d by omega, Nat.choose_symm_add]

/-- The allowed permutations for the support pattern `H`. -/
abbrev ToricLive {n : ℕ} (H : Fin n → Fin n → Bool) :=
  {π : Equiv.Perm (Fin n) // ∀ j, H (π j) j = true}

/-- Exponent of the determinant monomial indexed by a permutation. -/
noncomputable def toricExponent {n : ℕ} (π : Equiv.Perm (Fin n)) : (Fin n × Fin n) →₀ ℕ :=
  ∑ j : Fin n, Finsupp.single (π j, j) 1

@[simp] theorem toricExponent_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin n × Fin n) :
    toricExponent π e = if π e.2 = e.1 then 1 else 0 := by
  classical
  rw [toricExponent, Finset.sum_apply', Finset.sum_eq_single e.2]
  · have hpair : (π e.2, e.2) = e ↔ π e.2 = e.1 := by
      cases e
      simp
    simp only [Finsupp.single_apply, hpair]
  · intro j _ hj
    have hne : (π j, j) ≠ e := fun h => hj (congrArg Prod.snd h)
    simp [Finsupp.single_apply, hne, Ne.symm hne]
  · simp

/-- The subspace `V` in the posted statement. -/
def toricSpace {n : ℕ} (H : Fin n → Fin n → Bool) :
    Submodule ℚ (Fin n × Fin n → ℚ) :=
  Submodule.span ℚ {v | ∃ π : Equiv.Perm (Fin n), (∀ j, H (π j) j = true) ∧
    v = fun e => if π e.2 = e.1 then (1 : ℚ) else 0}

theorem toricExponent_mem_space {n : ℕ} {H : Fin n → Fin n → Bool} (π : ToricLive H) :
    toricRat (toricExponent π.val) ∈ toricSpace H := by
  apply Submodule.subset_span
  refine ⟨π.val, π.property, ?_⟩
  funext e
  simp only [toricRat, toricExponent_apply]
  split <;> simp

theorem toricExponent_mass {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∑ e, toricExponent π e = n := by
  rw [← Finsupp.degree_eq_sum, toricExponent, map_sum]
  simp


open MvPolynomial

noncomputable def exponentMap {G E : Type} (a : G → E →₀ ℕ) : (G →₀ ℕ) →+ E →₀ ℕ :=
  Finsupp.liftAddHom fun i =>
    { toFun := fun k => k • a i
      map_zero' := zero_nsmul _
      map_add' := fun j k => add_nsmul _ j k }

lemma exponentMap_apply {G E : Type} (a : G → E →₀ ℕ) (x : G →₀ ℕ) :
    exponentMap a x = ∑ i ∈ x.support, x i • a i := rfl

lemma exponentMap_single {G E : Type} (a : G → E →₀ ℕ) (i : G) :
    exponentMap a (Finsupp.single i 1) = a i := by
  unfold exponentMap
  rw [Finsupp.liftAddHom_apply_single]
  exact one_nsmul _

noncomputable def mapExponents {G E : Type} (a : (G →₀ ℕ) →+ E →₀ ℕ) : Poly G →ₐ[ℂ] Poly E :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ a

lemma mapExponents_monomial {G E : Type} (a : (G →₀ ℕ) →+ E →₀ ℕ) (x : G →₀ ℕ) (c : ℂ) :
    mapExponents a (monomial x c) = monomial (a x) c :=
  AddMonoidAlgebra.mapDomain_single

lemma aeval_monomial_generators {G E : Type} (a : G → E →₀ ℕ) :
    aeval (R := ℂ) (fun i => monomial (a i) 1) = mapExponents (exponentMap a) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [aeval_X, X, mapExponents_monomial, exponentMap_single]

open scoped Classical in
lemma coeff_mapExponents {G E : Type} (a : (G →₀ ℕ) →+ E →₀ ℕ) (p : Poly G) (v : E →₀ ℕ) :
    (mapExponents a p).coeff v = ∑ x ∈ p.support, if a x = v then p.coeff x else 0 := by
  classical
  conv_lhs => rw [← p.support_sum_monomial_coeff, map_sum, coeff_sum]
  simp only [mapExponents_monomial, coeff_monomial]

lemma mapExponents_ne_zero {G E : Type} (a : (G →₀ ℕ) →+ E →₀ ℕ) (p : Poly G) (hp : p ≠ 0)
    (ha : Set.InjOn a (↑p.support : Set (G →₀ ℕ))) : mapExponents a p ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ := exists_coeff_ne_zero hp
  have hs := mem_support_iff.mpr hx
  intro h
  have hv : (mapExponents a p).coeff (a x) = p.coeff x := by
    rw [coeff_mapExponents, Finset.sum_eq_single x, if_pos rfl]
    · intro y hy hyx
      exact if_neg (fun e => hyx (ha hy hs e))
    · exact fun hn => (hn hs).elim
  exact hx (by simpa only [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using hv.symm)

noncomputable def toricM {n : ℕ} (H : Fin n → Fin n → Bool) : ToricLive H → Poly (Fin n × Fin n) :=
  fun j => monomial (toricExponent j.val) 1

lemma toric_gen_homogeneous {n : ℕ} (H : Fin n → Fin n → Bool) (j : ToricLive H) :
    (toricM H j).IsHomogeneous n :=
  isHomogeneous_monomial _ ((Finsupp.degree_eq_sum _).trans (toricExponent_mass j.val))

lemma toric_exp_mem {n : ℕ} (H : Fin n → Fin n → Bool) (x : ToricLive H →₀ ℕ) :
    toricRat (exponentMap (fun j : ToricLive H => toricExponent j.val) x) ∈ toricSpace H := by
  classical
  rw [exponentMap_apply]
  have hr : toricRat (∑ i ∈ x.support, x i • toricExponent i.val) =
      ∑ i ∈ x.support, (x i : ℚ) • toricRat (toricExponent i.val) := by
    ext e
    simp [toricRat, Finset.sum_apply', Finset.sum_apply, smul_eq_mul, nsmul_eq_mul]
  rw [hr]
  exact (toricSpace H).sum_mem fun i _ => (toricSpace H).smul_mem _ (toricExponent_mem_space i)

lemma toric_exp_degree {n : ℕ} (H : Fin n → Fin n → Bool) (x : ToricLive H →₀ ℕ) :
    (exponentMap (fun j : ToricLive H => toricExponent j.val) x).degree = n * x.degree := by
  classical
  rw [exponentMap_apply, map_sum, Finsupp.degree_apply x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_nsmul, Finsupp.degree_eq_sum, toricExponent_mass]
  exact Nat.mul_comm _ _

lemma toric_support_mem {n : ℕ} (H : Fin n → Fin n → Bool) (p : Poly (ToricLive H))
    {v : (Fin n × Fin n) →₀ ℕ} (hv : v ∈ (aeval (toricM H) p).support) :
    toricRat v ∈ toricSpace H ∧ v.degree ≤ n * p.totalDegree := by
  classical
  let a := exponentMap (fun j : ToricLive H => toricExponent j.val)
  change v ∈ (aeval (fun j : ToricLive H => monomial (toricExponent j.val) 1) p).support at hv
  rw [aeval_monomial_generators] at hv
  have hv' := mem_support_iff.mp hv
  rw [coeff_mapExponents] at hv'
  obtain ⟨x, hx, he⟩ : ∃ x ∈ p.support, a x = v := by
    by_contra! h
    exact hv' (Finset.sum_eq_zero fun i hi => if_neg (h i hi))
  subst v
  exact ⟨toric_exp_mem H x, (toric_exp_degree H x).trans_le (Nat.mul_le_mul_left _ (le_totalDegree hx))⟩

lemma toric_trdeg {n : ℕ} (H : Fin n → Fin n → Bool) :
    Algebra.trdeg ℂ (presented (toricM H)) = Module.finrank ℚ (toricSpace H) := by
  classical
  let V := toricSpace H
  let d := Module.finrank ℚ V
  let m := toricM H
  change Algebra.trdeg ℂ (presented m) = (d : Cardinal)
  apply le_antisymm
  · obtain ⟨a, ha⟩ := toric_coordinates V
    let p := Finsupp.comapDomain.addMonoidHom (M := ℕ) a.injective
    let f : presented m →ₐ[ℂ] Poly (Fin d) :=
      (mapExponents p).comp (presented m).val
    have hfi : Function.Injective f := by
      apply (injective_iff_map_eq_zero f).2
      intro s hs
      obtain ⟨r, hr⟩ := (aeval m).rangeRestrict_surjective s
      subst s
      apply Subtype.ext
      change aeval m r = 0
      by_contra hz
      apply mapExponents_ne_zero p _ hz _ hs
      intro x hx y hy hxy
      have ex := (toric_support_mem H r hx).1
      have ey := (toric_support_mem H r hy).1
      have hV : (⟨toricRat x, ex⟩ : V) = ⟨toricRat y, ey⟩ := ha (funext fun j => by
        have hj := congrArg (fun w : Fin d →₀ ℕ => w j) hxy
        exact congrArg (fun l : ℕ => (l : ℚ)) hj)
      ext i
      have hi := congrFun (congrArg Subtype.val hV) i
      change (x i : ℚ) = (y i : ℚ) at hi
      exact_mod_cast hi
    simpa [MvPolynomial.trdeg_of_isDomain] using trdeg_le_of_injective f hfi
  · let v : ToricLive H → (Fin n × Fin n → ℚ) := fun j => toricRat (toricExponent j.val)
    have hv : Submodule.span ℚ (Set.range v) = V := by
      congr 1
      ext r
      change (∃ j : ToricLive H, toricRat (toricExponent j.val) = r) ↔ _
      constructor
      · rintro ⟨j, rfl⟩
        refine ⟨j.val, j.property, ?_⟩
        funext e
        simp only [toricRat, toricExponent_apply]
        split <;> simp
      · rintro ⟨j, hj, rfl⟩
        refine ⟨⟨j, hj⟩, ?_⟩
        funext e
        simp only [toricRat, toricExponent_apply]
        split <;> simp
    obtain ⟨ι, g, hg, hspan, hli⟩ := exists_linearIndependent' ℚ v
    letI : Finite ι := Finite.of_injective g hg
    letI : Fintype ι := Fintype.ofFinite ι
    have hι : Fintype.card ι = d := by
      change Fintype.card ι = Module.finrank ℚ V
      rw [← hv, ← hspan]
      exact (Module.finrank_eq_card_basis (Module.Basis.span hli)).symm
    let g' : Fin d → ToricLive H := g ∘ (Fintype.equivFinOfCardEq hι).symm
    have hli' : LinearIndependent ℚ (v ∘ g') := hli.comp _ (Equiv.injective _)
    let a : Fin d → (Fin n × Fin n) →₀ ℕ := fun i => toricExponent (g' i).val
    have hE : Function.Injective (exponentMap a) := by
      intro x y he
      have h (z : Fin d →₀ ℕ) : toricRat (exponentMap a z) =
          ∑ i, (z i : ℚ) • (v ∘ g') i := by
        rw [exponentMap_apply, ← Finset.sum_subset (Finset.subset_univ z.support)]
        · ext e
          simp [toricRat, a, v, Finset.sum_apply', Finset.sum_apply, smul_eq_mul, nsmul_eq_mul]
        · intro i _ hi
          simp [Finsupp.notMem_support_iff.mp hi]
      have he' := congrArg toricRat he
      rw [h, h] at he'
      have hs : ∑ i, ((x i : ℚ) - y i) • (v ∘ g') i = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, he', sub_self]
      have h0 := (linearIndependent_iff'.mp hli') Finset.univ _ hs
      ext i
      exact_mod_cast (sub_eq_zero.mp (h0 i (Finset.mem_univ i)))
    let x : Fin d → presented m := fun i => (aeval m).rangeRestrict (X (g' i))
    have hiba : AlgebraicIndependent ℂ x := by
      rw [algebraicIndependent_iff_injective_aeval]
      apply (injective_iff_map_eq_zero (aeval (R := ℂ) x)).2
      intro p hp
      have hcomp : (presented m).val.comp (aeval x) = aeval (fun i => monomial (a i) (1 : ℂ)) := by
        apply MvPolynomial.algHom_ext
        intro i
        rw [AlgHom.comp_apply, aeval_X, aeval_X]
        change aeval m (X (g' i)) = _
        rw [aeval_X]
        rfl
      have hp0 := congrArg (fun q : presented m => (q : Poly (Fin n × Fin n))) hp
      change ((presented m).val.comp (aeval x)) p = 0 at hp0
      rw [hcomp, aeval_monomial_generators] at hp0
      by_contra hn
      exact mapExponents_ne_zero _ _ hn hE.injOn hp0
    simpa using hiba.cardinalMk_le_trdeg

lemma toric_filtered_growth {n : ℕ} (H : Fin n → Fin n → Bool) (k : ℕ) :
    Module.finrank ℂ ((restrictTotalDegree (ToricLive H) ℂ k).map
      (aeval (toricM H)).toLinearMap) ≤ (n * k + Module.finrank ℚ (toricSpace H)).choose
        (Module.finrank ℚ (toricSpace H)) := by
  classical
  let S : Set ((Fin n × Fin n) →₀ ℕ) :=
    {a | toricRat a ∈ toricSpace H ∧ a.degree ≤ n * k}
  have hs := toric_card_le_choose (toricSpace H) (n*k) (fun a : S => a.val)
    Subtype.val_injective (fun a => a.property.1)
    (fun a => (Finsupp.degree_eq_sum a.val).symm.trans_le a.property.2)
  letI : Finite S := hs.1
  letI : Fintype S := Fintype.ofFinite S
  let b := basisRestrictSupport ℂ S
  letI : FiniteDimensional ℂ (restrictSupport ℂ S) :=
    FiniteDimensional.of_finite_basis b (Set.toFinite S)
  have hle : (restrictTotalDegree (ToricLive H) ℂ k).map (aeval (toricM H)).toLinearMap
      ≤ restrictSupport ℂ S := by
    rintro p ⟨r, hr, rfl⟩
    exact (mem_restrictSupport_iff (R := ℂ)).mpr fun a ha => by
      have := toric_support_mem H r ha
      exact ⟨this.1, this.2.trans (Nat.mul_le_mul_left n ((mem_restrictTotalDegree _ k r).mp hr))⟩
  exact (Submodule.finrank_mono hle).trans
    ((Module.finrank_eq_card_basis b).trans_le (by simpa only [Nat.card_eq_fintype_card] using hs.2))


open MvPolynomial
open scoped BigOperators

variable {n q d : ℕ} {H : Fin n → Fin n → Bool} {ζ : ℂ}

private abbrev probeSign (π : Equiv.Perm (Fin n)) : ℂ :=
  ((Equiv.Perm.sign π : ℤ) : ℂ)

noncomputable abbrev probeGenerator (π : ToricLive H) : Poly (Fin n × Fin n) :=
  toricM H π

noncomputable def probePoly (u : ToricLive H → ℂ) : Poly (Fin n × Fin n) :=
  ∑ π : ToricLive H, monomial (toricExponent π.val) (probeSign π.val * u π)

private lemma probeExponent_injective : Function.Injective
    (fun π : ToricLive H => toricExponent π.val) := by
  intro σ π h
  apply Subtype.ext
  apply Equiv.ext
  intro j
  have hj := DFunLike.congr_fun h (σ.val j, j)
  by_contra hne
  have hn' : π.val j ≠ σ.val j := Ne.symm hne
  simp [toricExponent_apply, hn'] at hj

private lemma coeff_probePoly (u : ToricLive H → ℂ) (π : ToricLive H) :
    (probePoly u).coeff (toricExponent π.val) = probeSign π.val * u π := by
  classical
  rw [probePoly, coeff_sum, Finset.sum_eq_single π]
  · simp
  · intro σ _ hσ
    rw [coeff_monomial, if_neg (fun h => hσ (probeExponent_injective h))]
  · simp

lemma probePoly_injective : Function.Injective (probePoly (H := H)) := by
  intro u v h
  funext π
  have hπ := congrArg (fun p : Poly (Fin n × Fin n) => p.coeff (toricExponent π.val)) h
  simp only [coeff_probePoly] at hπ
  have hs : probeSign π.val ≠ 0 := by
    change ((Equiv.Perm.sign π.val : ℤ) : ℂ) ≠ 0
    exact_mod_cast (Units.ne_zero (Equiv.Perm.sign π.val))
  exact mul_left_cancel₀ hs hπ

lemma probePoly_totalDegree (u : ToricLive H → ℂ) : (probePoly u).totalDegree ≤ n := by
  classical
  rw [probePoly]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le_iff.mpr ?_)
  intro π _
  calc
    _ ≤ (toricExponent π.val).degree := totalDegree_monomial_le _ _
    _ = n := by rw [Finsupp.degree_eq_sum, toricExponent_mass]

private lemma eval_probeMonomial (a : Fin n × Fin n → ℂ)
    (π : Equiv.Perm (Fin n)) (c : ℂ) :
    eval a (monomial (toricExponent π) c) = c * ∏ j : Fin n, a (π j, j) := by
  rw [toricExponent, monomial_sum_index]
  change eval a (C c * ∏ j : Fin n, (X (π j, j) : Poly (Fin n × Fin n))) = _
  simp only [map_mul, eval_C, map_prod, eval_X]

lemma eval_probeGenerator (a : Fin n × Fin n → ℂ) (π : ToricLive H) :
    eval a (probeGenerator π) = ∏ j : Fin n, a (π.val j, j) := by
  rw [probeGenerator, toricM, eval_probeMonomial, one_mul]

noncomputable def probeForm (ζ : ℂ) (s : Fin n × Fin n → Fin q) : Poly (ToricLive H) :=
  ∑ π : ToricLive H, C (probeSign π.val * ∏ j : Fin n, ζ ^ (s (π.val j, j)).val) * X π

lemma probeForm_homogeneous (s : Fin n × Fin n → Fin q) :
    (probeForm (H := H) ζ s).IsHomogeneous 1 := by
  rw [probeForm]
  exact IsHomogeneous.sum _ _ _ fun π _ => isHomogeneous_C_mul_X _ π

lemma aeval_probeForm (u : ToricLive H → ℂ) (s : Fin n × Fin n → Fin q) :
    aeval u (probeForm ζ s) = eval (fun e => ζ ^ (s e).val) (probePoly u) := by
  simp only [probeForm, probePoly, map_sum, map_mul, aeval_C, Algebra.algebraMap_self,
    RingHom.id_apply, aeval_X, eval_probeMonomial]
  apply Finset.sum_congr rfl
  intro π _
  ring

private lemma probe_prod_zero (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, H i j = false → A i j = 0) (π : Equiv.Perm (Fin n))
    (hπ : ¬ ∀ j, H (π j) j = true) (b : Fin n → ℂ) :
    (∏ j : Fin n, A (π j) j * b j) = 0 := by
  classical
  obtain ⟨j, hj⟩ := not_forall.mp hπ
  have hfalse : H (π j) j = false := by
    cases h : H (π j) j <;> simp_all
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hA _ _ hfalse, zero_mul])

lemma eval_probePoly_det (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, H i j = false → A i j = 0) (a : Fin n × Fin n → ℂ) :
    eval a (probePoly (H := H) (fun π => ∏ j : Fin n, A (π.val j) j)) =
      Matrix.det (fun i j => A i j * a (i, j) : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  simp only [probePoly, map_sum, eval_probeMonomial]
  let f (π : Equiv.Perm (Fin n)) : ℂ := probeSign π * ∏ j : Fin n, A (π j) j * a (π j, j)
  calc
    _ = ∑ π : ToricLive H, f π.val := by
      apply Finset.sum_congr rfl
      intro π _
      simp only [f, Finset.prod_mul_distrib, mul_assoc]
    _ = ∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ j, H (π j) j = true), f π := by
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    _ = ∑ π : Equiv.Perm (Fin n), f π := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro π hπ hnot
      have hh : ¬ ∀ j, H (π j) j = true := fun hp => hnot (Finset.mem_filter.mpr ⟨hπ, hp⟩)
      exact mul_eq_zero_of_right _ (probe_prod_zero A hA π hh (fun j => a (π j, j)))
    _ = _ := (Matrix.det_apply'
      (fun i j => A i j * a (i, j) : Matrix (Fin n) (Fin n) ℂ)).symm

lemma aeval_probeForm_det (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, H i j = false → A i j = 0) (s : Fin n × Fin n → Fin q) :
    aeval (fun π : ToricLive H => ∏ j : Fin n, A (π.val j) j) (probeForm ζ s) =
      Matrix.det (fun i j => A i j * ζ ^ (s (i, j)).val : Matrix (Fin n) (Fin n) ℂ) := by
  rw [aeval_probeForm, eval_probePoly_det A hA]

private lemma probe_separate_finite (hζ : IsPrimitiveRoot ζ q)
    (hq : n * (n ^ d) ^ 2 < q) (F : Set (ToricLive H → ℂ))
    (hF : F.Finite) (hcard : F.ncard ≤ n ^ d) :
    ∃ s : Fin n × Fin n → Fin q, Set.InjOn
      (fun u => eval (fun e => ζ ^ (s e).val) (probePoly u)) F := by
  classical
  let U := hF.toFinset
  let T := (U.product U).filter (fun uv => uv.1 ≠ uv.2)
  let p := fun uv : (ToricLive H → ℂ) × (ToricLive H → ℂ) => probePoly uv.1 - probePoly uv.2
  have hP : ∀ i ∈ T, p i ≠ 0 := by
    intro i hi he
    exact (Finset.mem_filter.mp hi).2 (probePoly_injective (sub_eq_zero.mp he))
  have hU : U.card ≤ n ^ d := by
    simpa only [U, ← Set.ncard_eq_toFinset_card F hF] using hcard
  have hT : T.card ≤ (n ^ d) ^ 2 := by
    calc
      _ ≤ (U.product U).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = U.card * U.card := Finset.card_product U U
      _ ≤ _ := by rw [pow_two]; exact Nat.mul_le_mul hU hU
  have hd : (∑ i ∈ T, (p i).totalDegree) < q := by
    calc
      _ ≤ ∑ _i ∈ T, n := Finset.sum_le_sum (fun i _ =>
        (totalDegree_sub _ _).trans (max_le (probePoly_totalDegree i.1) (probePoly_totalDegree i.2)))
      _ = n * T.card := (Finset.sum_const_nat (s := T) (fun _ _ => rfl)).trans (Nat.mul_comm _ _)
      _ < _ := (Nat.mul_le_mul_left n hT).trans_lt hq
  obtain ⟨s, hs⟩ := grid_simultaneous_avoidance T p hP hζ (Nat.zero_lt_of_lt hq) hd
  refine ⟨s, ?_⟩
  intro u hu v hv he
  by_contra hne
  have hmem : (u, v) ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hF.mem_toFinset.mpr hu, hF.mem_toFinset.mpr hv⟩, hne⟩
  exact hs (u, v) hmem (by simp only [p, map_sub, he, sub_self])

/-- Any front giving bounded fibers on the live monomial variety admits a single adaptive
last determinant query and a decoder for all permutation products. -/
theorem determinant_decoder (hζ : IsPrimitiveRoot ζ q) (hq : n * (n ^ d) ^ 2 < q)
    (front : Fin d → (Fin n × Fin n → Fin q))
    (hf : ∀ y : Fin d → ℂ,
      let F := {u : ToricLive H → ℂ | u ∈ points (probeGenerator (H := H)) ∧
        ∀ j, aeval u (probeForm ζ (front j)) = y j}
      F.Finite ∧ F.ncard ≤ n ^ d) :
    ∃ (last : (Fin d → ℂ) → (Fin n × Fin n → Fin q))
      (read : (Fin d → ℂ) → ℂ → Equiv.Perm (Fin n) → ℂ),
      ∀ A : Matrix (Fin n) (Fin n) ℂ, (∀ i j, H i j = false → A i j = 0) →
        let evalDet := fun s : Fin n × Fin n → Fin q =>
          Matrix.det (fun i j => A i j * ζ ^ (s (i, j)).val : Matrix (Fin n) (Fin n) ℂ)
        let y := fun j => evalDet (front j)
        read y (evalDet (last y)) = fun π => ∏ j : Fin n, A (π j) j := by
  classical
  let F := fun y : Fin d → ℂ => {u : ToricLive H → ℂ | u ∈ points (probeGenerator (H := H)) ∧
    ∀ j, aeval u (probeForm ζ (front j)) = y j}
  have hsep : ∀ y, ∃ s : Fin n × Fin n → Fin q, Set.InjOn
      (fun u => eval (fun e => ζ ^ (s e).val) (probePoly u)) (F y) := fun y =>
    probe_separate_finite hζ hq (F y) (hf y).1 (hf y).2
  choose last hlast using hsep
  let agrees (y : Fin d → ℂ) (r : ℂ) (u : ToricLive H → ℂ) :=
    u ∈ F y ∧ eval (fun e => ζ ^ (last y e).val) (probePoly u) = r
  let readLive (y : Fin d → ℂ) (r : ℂ) : ToricLive H → ℂ :=
    if h : ∃ u, agrees y r u then Classical.choose h else 0
  refine ⟨last, fun y r π => if hπ : ∀ j, H (π j) j = true then readLive y r ⟨π, hπ⟩ else 0, ?_⟩
  intro A hA
  dsimp only
  let u : ToricLive H → ℂ := fun π => ∏ j : Fin n, A (π.val j) j
  let detA := fun s : Fin n × Fin n → Fin q =>
    Matrix.det (fun i j => A i j * ζ ^ (s (i, j)).val : Matrix (Fin n) (Fin n) ℂ)
  let y : Fin d → ℂ := fun j => detA (front j)
  let r := detA (last y)
  have hu : u ∈ F y := by
    constructor
    · have hm := eval_generators_mem_points (probeGenerator (H := H)) (fun e => A e.1 e.2)
      simpa only [eval_probeGenerator, u] using hm
    · intro j
      exact aeval_probeForm_det A hA (front j)
  have hv : agrees y r u := ⟨hu, eval_probePoly_det A hA _⟩
  have hex : ∃ v, agrees y r v := ⟨u, hv⟩
  have hread : readLive y r = u := by
    change (if h : ∃ v, agrees y r v then Classical.choose h else 0) = u
    rw [dif_pos hex]
    have hc := Classical.choose_spec hex
    exact hlast y hc.1 hu (hc.2.trans hv.2.symm)
  funext π
  change (if hπ : ∀ j, H (π j) j = true then readLive y r ⟨π, hπ⟩ else 0) = _
  split
  · rw [hread]
  · rename_i hπ
    simpa only [mul_one] using (probe_prod_zero A hA π hπ (fun _ => 1)).symm


open MvPolynomial
open scoped BigOperators Topology

private abbrev FiberPoly (G : Type) := MvPolynomial G ℂ
private noncomputable abbrev FiberRange {G E : Type} (m : G → FiberPoly E) :
    Subalgebra ℂ (FiberPoly E) := (aeval (R := ℂ) m).range

noncomputable abbrev fiberBase {G E : Type} {d : ℕ}
    (m : G → FiberPoly E) (f : Fin d → FiberPoly G) : FiberPoly (Fin d) →ₐ[ℂ] FiberRange m :=
  aeval (R := ℂ) (fun i => (aeval (R := ℂ) m).rangeRestrict (f i))

/-- The affine fiber of the selected polynomial functions on the image variety. -/
noncomputable def growthFiber {G E : Type} {d : ℕ} (m : G → FiberPoly E) (f : Fin d → FiberPoly G)
    (y : Fin d → ℂ) : Set (G → ℂ) :=
  {z | z ∈ zeroLocus ℂ (RingHom.ker (aeval (R := ℂ) m).toRingHom) ∧
    ∀ i, aeval (R := ℂ) z (f i) = y i}

private lemma fiber_limit_bound (a n d c : ℕ)
    (h : ∀ k : ℕ, a * (k + d).choose d ≤ (n * (k + c) + d).choose d) : a ≤ n ^ d := by
  have haux (k : ℕ) : a * k ^ d ≤ (n * (k + c) + d) ^ d := by
    have hlow := Nat.pow_sub_le_descFactorial (k + d) d
    rw [show k + d + 1 - d = k + 1 by omega] at hlow
    calc
      a * k ^ d ≤ a * (k + 1) ^ d := Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega) _)
      _ ≤ a * (k + d).descFactorial d := Nat.mul_le_mul_left _ hlow
      _ = d.factorial * (a * (k + d).choose d) := by
        rw [Nat.descFactorial_eq_factorial_mul_choose]; ac_rfl
      _ ≤ d.factorial * (n * (k + c) + d).choose d := Nat.mul_le_mul_left _ (h k)
      _ = (n * (k + c) + d).descFactorial d :=
        (Nat.descFactorial_eq_factorial_mul_choose _ _).symm
      _ ≤ (n * (k + c) + d) ^ d := Nat.descFactorial_le_pow _ _
  have ht : Filter.Tendsto (fun k : ℕ => ((n : ℝ) + ((n : ℝ) * c + d) / k) ^ d)
      Filter.atTop (𝓝 ((n : ℝ) ^ d)) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds (x := (n : ℝ))).add
        (tendsto_const_div_atTop_nhds_zero_nat ((n : ℝ) * c + d))).pow d
  have hreal : (a : ℝ) ≤ (n : ℝ) ^ d := by
    apply ge_of_tendsto ht
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hmul : ((n : ℝ) + ((n : ℝ) * c + d) / k) * k = (n : ℝ) * (k + c) + d := by
      field_simp [ne_of_gt hk']; ring
    refine le_of_mul_le_mul_right ?_ (pow_pos hk' d)
    rw [← mul_pow, hmul]
    exact_mod_cast haux k
  exact_mod_cast hreal

set_option maxHeartbeats 1200000 in
private lemma fiber_separator {ι G : Type} [Fintype ι] [Finite G]
    (z : ι → G → ℂ) (hz : Function.Injective z) :
    ∃ h : FiberPoly G, Function.Injective (fun i => aeval (R := ℂ) (z i) h) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let D (i j : ι) : FiberPoly G := ∑ g, C (z i g - z j g) * X g
  have hD (i j : ι) (hij : i ≠ j) : D i j ≠ 0 := by
    obtain ⟨g, hg⟩ : ∃ g, z i g ≠ z j g := by
      by_contra! h
      exact hij (hz (funext h))
    intro h
    have hh : eval (Pi.single g (1 : ℂ)) (D i j) = eval (Pi.single g (1 : ℂ)) 0 :=
      congrArg (eval (Pi.single g (1 : ℂ))) h
    simp only [D, map_sum, map_mul, eval_C, eval_X, map_zero] at hh
    rw [Finset.sum_eq_single g] at hh
    · exact (sub_ne_zero.mpr hg) (by simpa using hh)
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  let s : Finset (ι × ι) := Finset.univ.filter fun p => p.1 ≠ p.2
  let P : FiberPoly G := ∏ p ∈ s, D p.1 p.2
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact hD p.1 p.2 (Finset.mem_filter.mp hp).2
  obtain ⟨t, ht⟩ : ∃ t : G → ℂ, eval t P ≠ 0 := by
    by_contra! hh
    apply hP
    apply MvPolynomial.funext_set (s := fun _ => Set.univ) (fun _ => Set.infinite_univ)
    intro x _
    simpa using hh x
  refine ⟨∑ g, C (t g) * X g, ?_⟩
  intro i j he
  by_contra hij
  apply ht
  have hDij : eval t (D i j) = 0 := by
    have hh : (∑ g, t g * z i g) = ∑ g, t g * z j g := by
      simpa only [MvPolynomial.aeval_eq_eval, map_sum, map_mul, eval_C, eval_X] using he
    simp only [D, map_sum, map_mul, eval_C, eval_X, sub_mul, Finset.sum_sub_distrib]
    simpa only [mul_comm] using sub_eq_zero.mpr hh
  have hpij : (i, j) ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  rw [show P = ∏ p ∈ s, D p.1 p.2 from rfl, map_prod]
  exact Finset.prod_eq_zero hpij hDij

private noncomputable def fiberPointEval {G E : Type} (m : G → FiberPoly E)
    {z : G → ℂ} (hz : z ∈ zeroLocus ℂ (RingHom.ker (aeval (R := ℂ) m).toRingHom)) :
    FiberRange m →+* ℂ :=
  (aeval (R := ℂ) m).rangeRestrict.toRingHom.liftOfSurjective
    (aeval (R := ℂ) m).rangeRestrict_surjective
    ⟨(aeval (R := ℂ) z).toRingHom, fun p hp => hz p (by
      change aeval (R := ℂ) m p = 0
      change (aeval (R := ℂ) m).rangeRestrict p = 0 at hp
      exact congrArg Subtype.val hp)⟩

private lemma fiberPointEval_apply {G E : Type} (m : G → FiberPoly E)
    {z : G → ℂ} (hz : z ∈ zeroLocus ℂ (RingHom.ker (aeval (R := ℂ) m).toRingHom))
    (p : FiberPoly G) :
    fiberPointEval m hz ((aeval (R := ℂ) m).rangeRestrict p) = aeval (R := ℂ) z p :=
  RingHom.liftOfSurjective_comp_apply _ _ _ _

private lemma fiberPointEval_comp_base {G E : Type} {d : ℕ} (m : G → FiberPoly E)
    (f : Fin d → FiberPoly G) {y : Fin d → ℂ} {z : G → ℂ} (hz : z ∈ growthFiber m f y) :
    (fiberPointEval m hz.1).comp (fiberBase m f).toRingHom = (aeval (R := ℂ) y).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change fiberPointEval m hz.1 (fiberBase m f (C c)) = aeval (R := ℂ) y (C c)
    rw [show fiberBase m f (C c) = (aeval (R := ℂ) m).rangeRestrict (C c) by
      simpa only [MvPolynomial.algebraMap_eq] using
        ((fiberBase m f).commutes c).trans
          ((aeval (R := ℂ) m).rangeRestrict.commutes c).symm]
    rw [fiberPointEval_apply, MvPolynomial.aeval_C, MvPolynomial.aeval_C]
  · intro i
    change fiberPointEval m hz.1 (fiberBase m f (X i)) = aeval (R := ℂ) y (X i)
    rw [show fiberBase m f (X i) = (aeval (R := ℂ) m).rangeRestrict (f i) from
      aeval_X _ _, fiberPointEval_apply, MvPolynomial.aeval_X]
    exact hz.2 i

private lemma fiber_powers_independent {B R : Type} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [CommRing R] [IsDomain R] [Algebra B R] [Module.IsTorsionFree B R]
    {w : R} (hw : IsIntegral B w) :
    LinearIndependent B (fun i : Fin (minpoly B w).natDegree => w ^ (i : ℕ)) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  let q : Polynomial B := ∑ j, Polynomial.C (g j) * Polynomial.X ^ (j : ℕ)
  have hq : Polynomial.aeval w q = 0 := by
    simpa only [q, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Algebra.smul_def] using hg
  have hdeg : q.degree < (minpoly B w).degree := by
    rw [Polynomial.degree_eq_natDegree (minpoly.monic hw).ne_zero]
    exact Polynomial.degree_sum_fin_lt g
  have hzero : q = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt (minpoly.isIntegrallyClosed_dvd hw hq) hdeg
  have hi := congrArg (Polynomial.lcoeff B (i : ℕ)) hzero
  simpa only [q, Polynomial.C_mul_X_pow_eq_monomial, map_sum, Polynomial.lcoeff_apply,
    Polynomial.coeff_monomial, Finsupp.single_apply, Fin.val_eq_val,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero] using hi

private lemma fiber_products_independent {B R ι κ : Type} [CommRing B] [CommRing R]
    [Algebra ℂ B] [Algebra ℂ R] [Algebra B R] [Fintype ι] [Fintype κ]
    (b : B →ₐ[ℂ] R) (hb : algebraMap B R = b.toRingHom) (v : ι → R) (w : κ → B)
    (hv : LinearIndependent B v) (hw : LinearIndependent ℂ w) :
    LinearIndependent ℂ (fun ij : ι × κ => b (w ij.2) * v ij.1) := by
  classical
  refine Fintype.linearIndependent_iff.mpr fun g hg ij => ?_
  have hre (i : ι) : (∑ j, g (i, j) • w j) • v i =
      ∑ j, g (i, j) • (b (w j) * v i) := by
    rw [Algebra.smul_def, hb]
    change b (∑ j, g (i, j) • w j) * v i = _
    simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
  have hzero : (∑ i, (∑ j, g (i, j) • w j) • v i) = 0 := by
    simp_rw [hre]
    rwa [Fintype.sum_prod_type] at hg
  exact Fintype.linearIndependent_iff.mp hw _
    (Fintype.linearIndependent_iff.mp hv _ hzero ij.1) ij.2

private noncomputable def fiberExponent (d k : ℕ) (s : Sym (Fin (d + 1)) k) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (Sym.equivNatSumOfFintype (Fin (d + 1)) k s).1 i.succ)

private lemma fiberExponent_degree (d k : ℕ) (s : Sym (Fin (d + 1)) k) :
    (fiberExponent d k s).degree ≤ k := by
  have hs := (Sym.equivNatSumOfFintype (Fin (d + 1)) k s).2
  rw [Fin.sum_univ_succ] at hs
  rw [Finsupp.degree_eq_sum]
  change ∑ i : Fin d, (Sym.equivNatSumOfFintype (Fin (d + 1)) k s).1 i.succ ≤ k
  omega

private lemma fiberExponent_injective (d k : ℕ) : Function.Injective (fiberExponent d k) := by
  intro s t hst
  let e := Sym.equivNatSumOfFintype (Fin (d + 1)) k
  have htail (i : Fin d) : (e s).1 i.succ = (e t).1 i.succ :=
    congrArg (fun a : Fin d →₀ ℕ => a i) hst
  have hsum : (∑ i : Fin d, (e s).1 i.succ) = ∑ i : Fin d, (e t).1 i.succ :=
    Finset.sum_congr rfl (fun i _ => htail i)
  have hs := (e s).2
  have ht := (e t).2
  rw [Fin.sum_univ_succ] at hs ht
  apply e.injective
  apply Subtype.ext
  funext i
  exact Fin.cases (by omega) htail i

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
private lemma fiber_fintype_bound {G E ι : Type} [Finite G] [Fintype ι] {n d : ℕ}
    (m : G → FiberPoly E) (f : Fin d → FiberPoly G) (hf : ∀ i, (f i).IsHomogeneous 1)
    (hb : Function.Injective (fiberBase m f))
    (hfinite : letI : Algebra (FiberPoly (Fin d)) (FiberRange m) :=
      (fiberBase m f).toRingHom.toAlgebra
      Module.Finite (FiberPoly (Fin d)) (FiberRange m))
    (hgrowth : ∀ k : ℕ, Module.finrank ℂ
      ((restrictTotalDegree G ℂ k).map (aeval m).toLinearMap) ≤ (n * k + d).choose d)
    (y : Fin d → ℂ) (z : ι → G → ℂ) (hz : Function.Injective z)
    (hF : ∀ i, z i ∈ growthFiber m f y) : Fintype.card ι ≤ n ^ d := by
  classical
  let B := FiberPoly (Fin d)
  let R := FiberRange m
  let b : B →ₐ[ℂ] R := fiberBase m f
  let r : FiberPoly G →ₐ[ℂ] R := (aeval m).rangeRestrict
  letI : Algebra B R := b.toRingHom.toAlgebra
  letI : Module.Finite B R := hfinite
  letI : Module.IsTorsionFree B R := Module.isTorsionFree_iff_algebraMap_injective.mpr hb
  obtain ⟨h, hh⟩ := fiber_separator z hz
  let w : R := r h
  let p := minpoly B w
  let a := p.natDegree
  have hw : IsIntegral B w := IsIntegral.of_finite B w
  have hp : p.Monic := minpoly.monic hw
  let pY := p.map (aeval y).toRingHom
  have hroot (i : ι) : pY.IsRoot (aeval (z i) h) := by
    let e := fiberPointEval m (hF i).1
    have he : e.comp (algebraMap B R) = (aeval y).toRingHom :=
      fiberPointEval_comp_base m f (hF i)
    have hval : e w = aeval (z i) h := fiberPointEval_apply m (hF i).1 h
    rw [← hval, Polynomial.IsRoot, show pY = p.map (aeval y).toRingHom from rfl,
      Polynomial.eval_map, ← he, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
      minpoly.aeval, map_zero]
  have hcard : Fintype.card ι ≤ a := by
    let s : Finset ℂ := Finset.univ.image (fun i => aeval (z i) h)
    have hs : s.card = Fintype.card ι := by
      rw [show s = Finset.univ.image (fun i => aeval (z i) h) from rfl,
        Finset.card_image_of_injective _ hh, Finset.card_univ]
    rw [← hs]
    apply le_trans (Polynomial.card_le_degree_of_subset_roots (p := pY) (Z := s) ?_)
      Polynomial.natDegree_map_le
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (show x ∈ s from hx)
    exact (Polynomial.mem_roots ((hp.map (aeval y).toRingHom).ne_zero)).mpr (hroot i)
  refine hcard.trans (fiber_limit_bound a n d (a * h.totalDegree) fun k => ?_)
  let U := Sym (Fin (d + 1)) k
  let u (s : U) : B := monomial (fiberExponent d k s) 1
  have hu : LinearIndependent ℂ u :=
    ((basisMonomials (Fin d) ℂ).linearIndependent.comp _ (fiberExponent_injective d k))
  let v (i : Fin a) : R := w ^ (i : ℕ)
  have hv : LinearIndependent B v := fiber_powers_independent hw
  let g (ij : Fin a × U) : R := b (u ij.2) * v ij.1
  have hg : LinearIndependent ℂ g := fiber_products_independent b rfl v u hv hu
  let M := (restrictTotalDegree G ℂ (k + a * h.totalDegree)).map (aeval m).toLinearMap
  have hmem (ij : Fin a × U) : (g ij : FiberPoly E) ∈ M := by
    have hd : (aeval f (u ij.2)).totalDegree ≤ k := by
      have hhom : (u ij.2).IsHomogeneous (fiberExponent d k ij.2).degree :=
        isHomogeneous_monomial 1 rfl
      exact (hhom.aeval f hf).totalDegree_le.trans (by
        simpa only [one_mul] using fiberExponent_degree d k ij.2)
    refine ⟨aeval f (u ij.2) * h ^ (ij.1 : ℕ), ?_, ?_⟩
    · apply (mem_restrictTotalDegree _ _ _).mpr
      exact (totalDegree_mul _ _).trans (Nat.add_le_add hd ((totalDegree_pow _ _).trans
        (Nat.mul_le_mul_right _ (Nat.le_of_lt ij.1.isLt))))
    · have hb' : r (aeval f (u ij.2)) = b (u ij.2) :=
        MvPolynomial.comp_aeval_apply f r (u ij.2)
      have hEq : r (aeval f (u ij.2) * h ^ (ij.1 : ℕ)) = g ij := by
        rw [map_mul, map_pow, hb']
      exact congrArg Subtype.val hEq
  let gM (ij : Fin a × U) : M := ⟨g ij, hmem ij⟩
  have hlin : LinearIndependent ℂ gM := by
    apply LinearIndependent.of_comp M.subtype
    exact hg.map' (Subalgebra.val (aeval m).range).toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hU : Fintype.card U = (k + d).choose d := by
    change Fintype.card (Sym (Fin (d + 1)) k) = (k + d).choose d
    rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    rw [show d + 1 + k - 1 = k + d by omega, Nat.choose_symm_add]
  have hdim := hlin.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin, hU] at hdim
  exact hdim.trans (hgrowth _)

/-- A finite linear normalization, with the indicated filtered dimension bound, has at most
`n ^ d` geometric points in each fiber. -/
theorem fiber_card_bound {G E : Type} [Finite G] {n d : ℕ}
    (m : G → FiberPoly E) (f : Fin d → FiberPoly G) (hf : ∀ i, (f i).IsHomogeneous 1)
    (hb : Function.Injective (fiberBase m f))
    (hfinite : letI : Algebra (FiberPoly (Fin d)) (FiberRange m) :=
      (fiberBase m f).toRingHom.toAlgebra
      Module.Finite (FiberPoly (Fin d)) (FiberRange m))
    (hgrowth : ∀ k : ℕ, Module.finrank ℂ
      ((restrictTotalDegree G ℂ k).map (aeval m).toLinearMap) ≤ (n * k + d).choose d)
    (y : Fin d → ℂ) : (growthFiber m f y).Finite ∧ Nat.card (growthFiber m f y) ≤ n ^ d := by
  classical
  let S := growthFiber m f y
  by_cases hs : S.Finite
  · letI := hs.fintype
    refine ⟨hs, ?_⟩
    rw [Nat.card_eq_fintype_card]
    exact fiber_fintype_bound m f hf hb hfinite hgrowth y Subtype.val
      Subtype.val_injective (fun z : S => z.property)
  · obtain ⟨s, hsS, hsc⟩ := Set.Infinite.exists_subset_card_eq hs (n ^ d + 1)
    have h := fiber_fintype_bound m f hf hb hfinite hgrowth y (fun z : s => z.val)
      Subtype.val_injective (fun z => hsS z.property)
    rw [Fintype.card_coe, hsc] at h
    omega


open MvPolynomial

lemma replace_front_form {G E S : Type} {n d : ℕ} (hn : n ≠ 0)
    (m : G → Poly E) (hm : ∀ j, (m j).IsHomogeneous n)
    (f : Fin d → Poly G) (hf : ∀ j, (f j).IsHomogeneous 1) (hz : separatingZero m f)
    (j : Fin d) (p : S → Poly G) (hp : ∀ s, (p s).IsHomogeneous 1)
    (havoid : ∃ s, ∀ z ∈ growthFiber m f (fun i => if i = j then 1 else 0),
      aeval z (p s) ≠ 0) :
    ∃ s, separatingZero m (Function.update f j (p s)) := by
  classical
  obtain ⟨s, hs⟩ := havoid
  refine ⟨s, ?_⟩
  intro u hu he
  by_contra hne
  have hother (i : Fin d) (hi : i ≠ j) : aeval u (f i) = 0 := by
    simpa only [Function.update_of_ne hi] using he i
  have hj : aeval u (f j) ≠ 0 := by
    intro h
    apply hne (hz u hu _)
    intro i
    rcases eq_or_ne i j with rfl | hi
    · exact h
    · exact hother _ hi
  let c : ℂ := (aeval u (f j))⁻¹
  have hc : c * aeval u (f j) = 1 := inv_mul_cancel₀ hj
  have hF : c • u ∈ growthFiber m f (fun i => if i = j then 1 else 0) := by
    refine ⟨points_smul hn m hm hu c, ?_⟩
    intro i
    rw [(hf i).aeval_smul, pow_one, smul_eq_mul]
    rcases eq_or_ne i j with rfl | h
    · simpa using hc
    · simp only [hother _ h, mul_zero, if_neg h]
  apply hs _ hF
  rw [(hp s).aeval_smul, pow_one]
  have h := he j
  rw [Function.update_self] at h
  rw [h, smul_zero]

lemma phase_front {n q : ℕ} (hn : 0 < n) (H : Fin n → Fin n → Bool) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ q)
    (hq : n * (n ^ Module.finrank ℚ (toricSpace H)) ^ 2 < q) :
    let d := Module.finrank ℚ (toricSpace H)
    ∃ front : Fin d → (Fin n × Fin n → Fin q),
      ∀ y, let F := growthFiber (toricM H) (fun i => probeForm ζ (front i)) y
        F.Finite ∧ F.ncard ≤ n ^ d := by
  classical
  let d := Module.finrank ℚ (toricSpace H)
  let m := toricM H
  let S := Fin n × Fin n → Fin q
  let p : S → Poly (ToricLive H) := probeForm ζ
  have hp (s : S) : (p s).IsHomogeneous 1 := probeForm_homogeneous s
  have ht : Algebra.trdeg ℂ (presented m) = (d : Cardinal) := toric_trdeg H
  have hm := toric_gen_homogeneous H
  have hfiber (f : Fin d → Poly (ToricLive H)) (hf : ∀ j, (f j).IsHomogeneous 1)
      (hz : separatingZero m f) (y : Fin d → ℂ) :
      (growthFiber m f y).Finite ∧ (growthFiber m f y).ncard ≤ n ^ d :=
    fiber_card_bound m f hf (normal_injective hn.ne' m hm ht.ge f hf hz)
      (normal_finite hn.ne' m hm f hf hz) (toric_filtered_growth H) y
  let good (k : ℕ) := ∃ f : Fin d → Poly (ToricLive H),
    (∀ i, (f i).IsHomogeneous 1) ∧ separatingZero m f ∧
      ∀ i, i.val < k → ∃ s : S, p s = f i
  have hbase : good 0 := by
    obtain ⟨f, hf, hz⟩ := initial_zero_forms hn.ne' m hm ht.le
    exact ⟨f, hf, hz, fun i hi => (Nat.not_lt_zero _ hi).elim⟩
  have hstep (k : ℕ) (hk : k < d) (hg : good k) : good (k + 1) := by
    obtain ⟨f, hf, hz, hprev⟩ := hg
    let j : Fin d := ⟨k, hk⟩
    let y : Fin d → ℂ := fun i => if i = j then 1 else 0
    let F := growthFiber m f y
    obtain ⟨hF, hc⟩ := hfiber f hf hz y
    have hz' (u : ToricLive H → ℂ) (hu : u ∈ F) : u ≠ 0 := by
      intro he
      have heval := hu.2 j
      have hzero : aeval (0 : ToricLive H → ℂ) (f j) = 0 := by
        simpa only [zero_smul, zero_pow (by decide : 1 ≠ 0)] using (hf j).aeval_smul 0 u
      rw [he, hzero] at heval
      simp [y] at heval
    have hpoly (u : ToricLive H → ℂ) (hu : u ∈ hF.toFinset) : probePoly u ≠ 0 := by
      intro he
      have h0 : probePoly (0 : ToricLive H → ℂ) = 0 := by simp [probePoly]
      exact hz' u (hF.mem_toFinset.mp hu) (probePoly_injective (he.trans h0.symm))
    have hkq : (∑ u ∈ hF.toFinset, (probePoly u).totalDegree) < q := by
      have hnpos : 1 ≤ n ^ d := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hn.ne')
      have hm' : n ^ d ≤ (n ^ d) ^ 2 := by
        simpa only [pow_two, mul_one] using Nat.mul_le_mul_left (n ^ d) hnpos
      calc
        _ ≤ ∑ _u ∈ hF.toFinset, n := Finset.sum_le_sum fun u _ => probePoly_totalDegree u
        _ = n * F.ncard := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm, Set.ncard_eq_toFinset_card F hF]
        _ ≤ n * (n ^ d) ^ 2 := Nat.mul_le_mul_left _ (hc.trans hm')
        _ < q := hq
    obtain ⟨s, hs⟩ := grid_simultaneous_avoidance hF.toFinset probePoly hpoly hζ
      (Nat.zero_lt_of_lt hq) hkq
    have havoid : ∃ s, ∀ u ∈ F, aeval u (p s) ≠ 0 := by
      refine ⟨s, fun u hu => ?_⟩
      change aeval u (probeForm ζ s) ≠ 0
      rw [aeval_probeForm]
      exact hs u (hF.mem_toFinset.mpr hu)
    obtain ⟨s', hs'⟩ := replace_front_form hn.ne' m hm f hf hz j p hp havoid
    refine ⟨Function.update f j (p s'), ?_, hs', ?_⟩
    · intro i
      rcases eq_or_ne i j with rfl | he
      · rw [Function.update_self]; exact hp _
      · rw [Function.update_of_ne he]; exact hf _
    · intro i hi
      rcases eq_or_ne i j with rfl | he
      · refine ⟨s', ?_⟩
        rw [Function.update_self]
      · rw [Function.update_of_ne he]
        apply hprev
        have hj : i.val ≠ k := fun e => he (Fin.ext e)
        omega
  have hgood : ∀ k ≤ d, good k := by
    intro k
    induction k with
    | zero => exact fun _ => hbase
    | succ k ih => exact fun hk => hstep k (by omega) (ih (by omega))
  obtain ⟨f, hf, hz, hsel⟩ := hgood d le_rfl
  choose front hfront using fun i : Fin d => hsel i i.isLt
  have he : (fun i => p (front i)) = f := funext hfront
  refine ⟨front, fun y => ?_⟩
  change (growthFiber m (fun i => p (front i)) y).Finite ∧
    (growthFiber m (fun i => p (front i)) y).ncard ≤ n ^ d
  rw [he]
  exact hfiber f hf hz y

end PEqualNP.Outside.L_lib_1092_aux

theorem PEqualNP.Outside.L_lib_1092 :
    ∀ (n q : ℕ) (H : Fin n → Fin n → Bool) (ζ : ℂ), 0 < n → IsPrimitiveRoot ζ q →
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
      n * (n ^ d) ^ 2 < q →
      ∃ (front : Fin d → S) (last : (Fin d → ℂ) → S) (read : (Fin d → ℂ) → ℂ → W),
        ∀ A : Matrix I I ℂ, fits A →
          let y := fun h : Fin d => eval (front h) A
          read y (eval (last y) A) = w A := by
  intro n q H ζ hn hζ I E V d W S fits w eval hq
  obtain ⟨front, hfront⟩ := PEqualNP.Outside.L_lib_1092_aux.phase_front hn H hζ hq
  obtain ⟨last, read, hread⟩ :=
    PEqualNP.Outside.L_lib_1092_aux.determinant_decoder hζ hq front hfront
  exact ⟨front, last, read, hread⟩
