import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_372_aux

open Polynomial Module

abbrev V (n : ℕ) := Fin n → ZMod 2

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def IsQ {W : Type} [AddCommGroup W] [Module (ZMod 2) W] (f : W → Bool) : Prop :=
  ∃ (l : W →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)

def Cert {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n) : Prop :=
  Shape N J ∧ (∀ p ∈ J, IsQ (q p)) ∧ ∀ p ∈ N \ J, ∀ x : ZMod 2 × V n,
    (∀ j : Fin p.length, q (p.take j.val) x = p.get j) →
      (if x.1 = 0 then x.2 = out p else x.2 = T (out p) + b)



section Alg
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n)

lemma al_zmod2_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma al_unit_eq_one {u : (ZMod 2)[X]} (hu : IsUnit u) : u = 1 := by
  obtain ⟨c, hc, rfl⟩ := Polynomial.isUnit_iff.mp hu
  rw [al_zmod2_ne_zero hc.ne_zero, map_one]

lemma al_coprime_of_irred {p g : (ZMod 2)[X]} (hp : Irreducible p) (hg : Irreducible g)
    (hne : p ≠ g) : IsCoprime p g := by
  rw [hp.coprime_iff_not_dvd]
  rintro ⟨r, hr⟩
  rcases hg.isUnit_or_isUnit hr with h | h
  · exact hp.not_isUnit h
  · rw [al_unit_eq_one h, mul_one] at hr
    exact hne hr.symm

lemma al_coprime_of_deg {p g : (ZMod 2)[X]} (hp : Irreducible p) (hg : g ≠ 0)
    (hdeg : g.natDegree < p.natDegree) : IsCoprime p g := by
  rw [hp.coprime_iff_not_dvd]
  intro h
  exact absurd (Polynomial.natDegree_le_of_dvd h hg) (not_le.mpr hdeg)

lemma al_bezout {f g : (ZMod 2)[X]} (h : IsCoprime f g) (x : V n)
    (hf : aeval T.toLinearMap f x = 0) (hg : aeval T.toLinearMap g x = 0) : x = 0 := by
  obtain ⟨a, c, hac⟩ := h
  have := congrArg (fun r => aeval T.toLinearMap r x) hac
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, mul_apply_eq_comp, hf, hg,
    map_zero, add_zero, one_apply_eq_self] at this
  exact this.symm

lemma al_inv_aeval (W : Submodule (ZMod 2) (V n)) (hW : ∀ x ∈ W, T x ∈ W) (g : (ZMod 2)[X]) :
    ∀ x ∈ W, aeval T.toLinearMap g x ∈ W := by
  induction g using Polynomial.induction_on with
  | C a =>
    intro x hx
    simp only [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self]
    exact W.smul_mem a hx
  | add p q hp hq =>
    intro x hx
    simp only [map_add, LinearMap.add_apply]
    exact W.add_mem (hp x hx) (hq x hx)
  | monomial k a ih =>
    intro x hx
    have : aeval T.toLinearMap (C a * X ^ (k + 1)) =
        aeval T.toLinearMap (C a * X ^ k) * T.toLinearMap := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    rw [this, mul_apply_eq_comp]
    exact ih _ (hW x hx)

lemma al_aeval_comm (g : (ZMod 2)[X]) (x : V n) :
    aeval T.toLinearMap g (T x) = T (aeval T.toLinearMap g x) := by
  have h := congrArg (aeval T.toLinearMap) (mul_comm g X)
  simp only [map_mul, aeval_X] at h
  exact LinearMap.congr_fun h x

lemma al_ker_inv (g : (ZMod 2)[X]) (x : V n) (hx : aeval T.toLinearMap g x = 0) :
    aeval T.toLinearMap g (T x) = 0 := by
  rw [al_aeval_comm, hx, map_zero]

def KT (W : Submodule (ZMod 2) (V n)) : Submodule (ZMod 2) (V n) :=
  ⨅ i : ℕ, W.comap (T.toLinearMap ^ i)

lemma mem_KT {W : Submodule (ZMod 2) (V n)} {x : V n} :
    x ∈ KT T W ↔ ∀ i : ℕ, (T.toLinearMap ^ i) x ∈ W := by
  simp [KT, Submodule.mem_iInf]

lemma KT_le (W : Submodule (ZMod 2) (V n)) : KT T W ≤ W := fun x hx => by
  simpa using (mem_KT T).1 hx 0

lemma KT_mono {W W' : Submodule (ZMod 2) (V n)} (h : W ≤ W') : KT T W ≤ KT T W' :=
  fun _ hx => (mem_KT T).2 (fun i => h ((mem_KT T).1 hx i))

lemma al_pow_succ_apply (i : ℕ) (x : V n) :
    (T.toLinearMap ^ (i + 1)) x = (T.toLinearMap ^ i) (T x) := by
  rw [pow_succ, mul_apply_eq_comp]
  rfl

lemma KT_T {W : Submodule (ZMod 2) (V n)} {x : V n} (hx : x ∈ KT T W) : T x ∈ KT T W :=
  (mem_KT T).2 fun i => by
    rw [← al_pow_succ_apply]
    exact (mem_KT T).1 hx (i + 1)

lemma le_KT {W : Submodule (ZMod 2) (V n)} (hW : ∀ x ∈ W, T x ∈ W) : W ≤ KT T W := by
  intro x hx
  rw [mem_KT]
  intro i
  induction i with
  | zero => simpa using hx
  | succ i ih =>
    rw [pow_succ', mul_apply_eq_comp]
    exact hW _ ih

lemma al_monic {p : (ZMod 2)[X]} (hp : Irreducible p) : p.Monic :=
  al_zmod2_ne_zero (leadingCoeff_ne_zero.mpr hp.ne_zero)


theorem alg_preimage {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (pp : (ZMod 2)[X]) (hirr : Irreducible pp)
    (hne : pp ≠ X + 1) (U : Submodule (ZMod 2) (V n)) (hUT : ∀ u ∈ U, T u ∈ U)
    (hUp : ∀ u ∈ U, aeval T.toLinearMap pp u = 0) :
    ∀ u0 ∈ U, ∃ u1 ∈ U, T u1 + u1 = u0 := by
  have hX1 : Irreducible (X + 1 : (ZMod 2)[X]) :=
    Polynomial.irreducible_of_degree_eq_one (by compute_degree!)
  have hcop : IsCoprime pp (X + 1) := al_coprime_of_irred hirr hX1 hne
  let β : U →ₗ[ZMod 2] U :=
    (T.toLinearMap + LinearMap.id).restrict (fun x hx => U.add_mem (hUT x hx) hx)
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h
    have h' : T x + x = 0 := congrArg Subtype.val h
    have : x = 0 := al_bezout T hcop x (hUp x hx) (by simpa using h')
    exact Subtype.ext this
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  intro u0 hu0
  obtain ⟨⟨u1, hu1⟩, h⟩ := hsurj ⟨u0, hu0⟩
  exact ⟨u1, hu1, congrArg Subtype.val h⟩

lemma al_key (pp : (ZMod 2)[X]) (hirr : Irreducible pp) (U : Submodule (ZMod 2) (V n))
    (hUT : ∀ u ∈ U, T u ∈ U) (hUp : ∀ u ∈ U, aeval T.toLinearMap pp u = 0)
    (μ : V n →ₗ[ZMod 2] ZMod 2) (y : V n) (hy : y ∈ U)
    (h0 : ∀ j < pp.natDegree, μ ((T.toLinearMap ^ j) y) = 0) (i : ℕ) :
    μ ((T.toLinearMap ^ i) y) = 0 := by
  have hmon := al_monic hirr
  have hne1 : pp ≠ 1 := fun h => hirr.not_isUnit (h ▸ isUnit_one)
  have hdecomp := Polynomial.modByMonic_add_div (X ^ i : (ZMod 2)[X]) pp
  have e0 : (T.toLinearMap ^ i) = aeval T.toLinearMap (X ^ i : (ZMod 2)[X]) := by simp
  have e1 : (T.toLinearMap ^ i) y = aeval T.toLinearMap ((X ^ i : (ZMod 2)[X]) %ₘ pp) y := by
    rw [e0]
    conv_lhs => rw [← hdecomp]
    rw [map_add, LinearMap.add_apply, map_mul, mul_apply_eq_comp,
      hUp _ (al_inv_aeval T U hUT _ y hy), add_zero]
  rw [e1, aeval_eq_sum_range' (natDegree_modByMonic_lt _ hmon hne1)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro j hj
  rw [h0 j (Finset.mem_range.mp hj), smul_zero]

lemma al_mem_shrink (pp : (ZMod 2)[X]) (hirr : Irreducible pp) (U : Submodule (ZMod 2) (V n))
    (hUT : ∀ u ∈ U, T u ∈ U) (hUp : ∀ u ∈ U, aeval T.toLinearMap pp u = 0)
    (μ : V n →ₗ[ZMod 2] ZMod 2) (y : V n) (hy : y ∈ U)
    (h0 : ∀ j < pp.natDegree, μ ((T.toLinearMap ^ j) y) = 0) :
    y ∈ KT T (U ⊓ LinearMap.ker μ) := by
  rw [mem_KT]
  intro i
  refine ⟨(mem_KT T).1 (le_KT T hUT hy) i, ?_⟩
  exact al_key T pp hirr U hUT hUp μ y hy h0 i

theorem alg_shrink {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (pp : (ZMod 2)[X]) (hirr : Irreducible pp)
    (U : Submodule (ZMod 2) (V n)) (hUT : ∀ u ∈ U, T u ∈ U)
    (hUp : ∀ u ∈ U, aeval T.toLinearMap pp u = 0) (μ : V n →ₗ[ZMod 2] ZMod 2) :
    ∃ U' : Submodule (ZMod 2) (V n), U' ≤ U ∧ (∀ u ∈ U', T u ∈ U') ∧ (∀ u ∈ U', μ u = 0) ∧
      finrank (ZMod 2) U ≤ finrank (ZMod 2) U' + pp.natDegree := by
  refine ⟨KT T (U ⊓ LinearMap.ker μ), (KT_le T _).trans inf_le_left, fun u hu => KT_T T hu,
    fun u hu => ((KT_le T _) hu).2, ?_⟩
  set d := pp.natDegree
  let φ : V n →ₗ[ZMod 2] (Fin d → ZMod 2) := LinearMap.pi (fun i => μ ∘ₗ (T.toLinearMap ^ (i : ℕ)))
  let G := φ.domRestrict U
  have h1 := LinearMap.finrank_range_add_finrank_ker G
  have h2 : finrank (ZMod 2) (LinearMap.range G) ≤ d := by
    calc _ ≤ finrank (ZMod 2) (Fin d → ZMod 2) := Submodule.finrank_le _
      _ = d := Module.finrank_fin_fun _
  have hmem : ∀ y : LinearMap.ker G, ((y : U) : V n) ∈ KT T (U ⊓ LinearMap.ker μ) := by
    intro y
    apply al_mem_shrink T pp hirr U hUT hUp μ _ (y : U).2
    intro j hj
    have hy := y.2
    rw [LinearMap.mem_ker] at hy
    have := congrFun hy ⟨j, hj⟩
    simp only [G, φ, LinearMap.domRestrict_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      Pi.zero_apply] at this
    exact this
  let F : LinearMap.ker G →ₗ[ZMod 2] KT T (U ⊓ LinearMap.ker μ) :=
    LinearMap.codRestrict _ (U.subtype ∘ₗ (LinearMap.ker G).subtype) hmem
  have hFinj : Function.Injective F := by
    intro a c hac
    have := congrArg Subtype.val hac
    simp only [F] at this
    exact Subtype.ext (Subtype.ext this)
  have h3 := LinearMap.finrank_le_finrank_of_injective hFinj
  omega


lemma al_coeff_sum {d : ℕ} (c : Fin d → ZMod 2) (j : Fin d) :
    (∑ i : Fin d, C (c i) * X ^ (i : ℕ)).coeff j = c j := by
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
  simp

lemma al_aeval_sum {d : ℕ} (c : Fin d → ZMod 2) (x : V n) :
    aeval T.toLinearMap (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) x =
      ∑ i : Fin d, c i • (T.toLinearMap ^ (i : ℕ)) x := by
  simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X, LinearMap.sum_apply,
    mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, one_apply_eq_self]

lemma al_gain (pp : (ZMod 2)[X]) (hirr : Irreducible pp) (X0 K : Submodule (ZMod 2) (V n))
    (hKX : K ≤ X0) (hKT : ∀ y ∈ K, T y ∈ K) (hXT : ∀ y ∈ X0, T y ∈ X0) (x1 : V n)
    (hx1 : x1 ∈ X0) (hx1K : x1 ∉ K) (hx1p : aeval T.toLinearMap pp x1 = 0) :
    finrank (ZMod 2) K + pp.natDegree ≤ finrank (ZMod 2) X0 := by
  set d := pp.natDegree with hd
  have hdpos : 0 < d := Irreducible.natDegree_pos hirr
  have hpoly : ∀ g : (ZMod 2)[X], g.degree < d → aeval T.toLinearMap g x1 ∈ K → g = 0 := by
    intro g hg hgK
    by_contra hg0
    have hcop := al_coprime_of_deg hirr hg0 ((Polynomial.natDegree_lt_iff_degree_lt hg0).mpr hg)
    obtain ⟨s, t, hst⟩ := hcop
    have := congrArg (fun r => aeval T.toLinearMap r x1) hst
    simp only [map_add, map_mul, LinearMap.add_apply, mul_apply_eq_comp, hx1p, map_zero, zero_add,
      map_one, one_apply_eq_self] at this
    exact hx1K (this ▸ al_inv_aeval T K hKT t _ hgK)
  let F : ((Fin d → ZMod 2) × K) →ₗ[ZMod 2] V n :=
    LinearMap.coprod (∑ i : Fin d, (LinearMap.proj i).smulRight ((T.toLinearMap ^ (i : ℕ)) x1))
      K.subtype
  have hF : ∀ c y, F (c, y) = (∑ i : Fin d, c i • (T.toLinearMap ^ (i : ℕ)) x1) + y := by
    intro c y
    simp [F]
  have hFinj : Function.Injective F := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨c, y⟩ hcy
    rw [hF] at hcy
    have hsum : aeval T.toLinearMap (∑ i : Fin d, C (c i) * X ^ (i : ℕ)) x1 ∈ K := by
      rw [al_aeval_sum]
      have : ∑ i : Fin d, c i • (T.toLinearMap ^ (i : ℕ)) x1 = -(y : V n) :=
        eq_neg_of_add_eq_zero_left hcy
      rw [this]
      exact K.neg_mem y.2
    have hg := hpoly _ (Polynomial.degree_sum_fin_lt c) hsum
    have hc : c = 0 := by
      funext j
      rw [← al_coeff_sum c j, hg]
      simp
    subst hc
    have hy : (y : V n) = 0 := by simpa using hcy
    simp [Subtype.ext_iff, hy]
  have hrange : LinearMap.range F ≤ X0 := by
    rintro _ ⟨⟨c, y⟩, rfl⟩
    rw [hF]
    refine X0.add_mem (X0.sum_mem fun i _ => X0.smul_mem _ ?_) (hKX y.2)
    exact (mem_KT T).1 (le_KT T hXT hx1) i
  have h1 := LinearMap.finrank_range_of_inj hFinj
  rw [Module.finrank_prod, Module.finrank_fin_fun] at h1
  have h2 := Submodule.finrank_mono hrange
  omega

lemma al_deg_le (pp : (ZMod 2)[X]) (hirr : Irreducible pp) (x : V n) (hx : x ≠ 0)
    (hxp : aeval T.toLinearMap pp x = 0) : pp.natDegree ≤ n := by
  have := al_gain T pp hirr ⊤ ⊥ bot_le (fun y hy => by simp_all) (fun y _ => trivial) x trivial
    (by simpa using hx) hxp
  simpa [finrank_top, Module.finrank_fin_fun] using this

noncomputable def polyS (n : ℕ) : Finset (ZMod 2)[X] :=
  (Finset.univ : Finset (Fin (n + 1) → ZMod 2)).image
    (fun c => ∑ i : Fin (n + 1), C (c i) * X ^ (i : ℕ))

lemma mem_polyS {p : (ZMod 2)[X]} (hp : p.natDegree ≤ n) : p ∈ polyS n := by
  refine Finset.mem_image.mpr ⟨fun i => p.coeff i, Finset.mem_univ _, ?_⟩
  rw [Fin.sum_univ_eq_sum_range (fun i => C (p.coeff i) * X ^ i)]
  conv_rhs => rw [p.as_sum_range' (n + 1) (by omega)]
  simp [C_mul_X_pow_eq_monomial]

lemma al_select (W : Submodule (ZMod 2) (V n)) (S : Finset (ZMod 2)[X]) :
    ∃ lam0 : V n →ₗ[ZMod 2] ZMod 2, ∀ p ∈ S, Irreducible p →
      (∃ x ∈ W, aeval T.toLinearMap p x = 0 ∧ x ≠ 0) →
      ∃ x ∈ W, aeval T.toLinearMap p x = 0 ∧ lam0 x ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert p' S hp' ih =>
    obtain ⟨lam0, hlam0⟩ := ih
    by_cases hgood : Irreducible p' → (∃ x ∈ W, aeval T.toLinearMap p' x = 0 ∧ x ≠ 0) →
        ∃ x ∈ W, aeval T.toLinearMap p' x = 0 ∧ lam0 x ≠ 0
    · refine ⟨lam0, ?_⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hgood
      · exact hlam0 p hp
    · push Not at hgood
      obtain ⟨hirr', ⟨x', hx'W, hx'p, hx'0⟩, hvan⟩ := hgood
      have hcop : IsCoprime p' (∏ p ∈ S.filter Irreducible, p) := by
        apply IsCoprime.prod_right
        intro p hp
        have hp2 := Finset.mem_filter.mp hp
        exact al_coprime_of_irred hirr' hp2.2 (fun h => hp' (h ▸ hp2.1))
      have hx'Q : x' ∉ LinearMap.ker (aeval T.toLinearMap (∏ p ∈ S.filter Irreducible, p)) :=
        fun h => hx'0 (al_bezout T hcop x' hx'p h)
      obtain ⟨f, hf, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx'Q inferInstance
      refine ⟨lam0 + f, ?_⟩
      intro p hp hirr hex
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact ⟨x', hx'W, hx'p, by simp [hvan x' hx'W hx'p, hf]⟩
      · obtain ⟨x, hxW, hxp, hlx⟩ := hlam0 p hp hirr hex
        have hQx : aeval T.toLinearMap (∏ p ∈ S.filter Irreducible, p) x = 0 := by
          obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun p => p) (Finset.mem_filter.mpr ⟨hp, hirr⟩)
          rw [hr, mul_comm, map_mul, mul_apply_eq_comp, hxp, map_zero]
        have hfx : f x = 0 := by
          have : f x ∈ Submodule.map f
              (LinearMap.ker (aeval T.toLinearMap (∏ p ∈ S.filter Irreducible, p))) :=
            Submodule.mem_map_of_mem hQx
          rw [hfmap] at this
          exact (Submodule.mem_bot (ZMod 2)).mp this
        exact ⟨x, hxW, hxp, by simp [hfx, hlx]⟩

lemma al_exists_irred (W : Submodule (ZMod 2) (V n)) (hWT : ∀ x ∈ W, T x ∈ W) (hW : W ≠ ⊥) :
    ∃ p : (ZMod 2)[X], Irreducible p ∧ ∃ x ∈ W, aeval T.toLinearMap p x = 0 ∧ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have key : ∀ g : (ZMod 2)[X], g ≠ 0 → ∀ x ∈ W, aeval T.toLinearMap g x = 0 → x = 0 := by
    intro g
    refine WfDvdMonoid.induction_on_irreducible g ?_ ?_ ?_
    · intro h
      exact absurd rfl h
    · intro u hu _ x _ hx
      obtain ⟨v, hv⟩ := hu.exists_left_inv
      have := congrArg (fun r => aeval T.toLinearMap r x) hv
      simp only [map_mul, mul_apply_eq_comp, hx, map_zero, map_one, one_apply_eq_self] at this
      exact this.symm
    · intro a i ha hi ih _ x hx hix
      rw [map_mul, mul_apply_eq_comp] at hix
      exact ih ha x hx (hcon i hi _ (al_inv_aeval T W hWT a x hx) hix)
  apply hW
  rw [Submodule.eq_bot_iff]
  intro x hx
  exact key _ (LinearMap.charpoly_monic T.toLinearMap).ne_zero x hx
    (by rw [LinearMap.aeval_self_charpoly]; rfl)

lemma al_finrank_hyp (W : Submodule (ZMod 2) (V n)) (f : V n →ₗ[ZMod 2] ZMod 2) (x : V n)
    (hx : x ∈ W) (hfx : f x ≠ 0) :
    finrank (ZMod 2) (W ⊓ LinearMap.ker f : Submodule (ZMod 2) (V n)) + 1 = finrank (ZMod 2) W := by
  have hfx1 : f x = 1 := al_zmod2_ne_zero hfx
  have hsup : W ⊔ LinearMap.ker f = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = f v • x + (v - f v • x) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (W.smul_mem _ hx) ?_
    simp [hfx1]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (LinearMap.ker f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have hr : LinearMap.range f = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • x, by simp [hfx1]⟩
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h2
  rw [hsup, finrank_top, Module.finrank_fin_fun] at h1
  omega


lemma al_cons {k : ℕ} (W : Submodule (ZMod 2) (V n)) (lam0 : V n →ₗ[ZMod 2] ZMod 2)
    (lam' : Fin k → (V n →ₗ[ZMod 2] ZMod 2)) (Bad' : Finset (Fin k))
    (hker : ∀ x ∈ W ⊓ LinearMap.ker lam0, (∀ i, lam' i x = 0) → x = 0)
    (hgood : ∀ j, j ∉ Bad' → ∀ x ∈ W ⊓ LinearMap.ker lam0, (∀ i, i < j → lam' i x = 0) →
      lam' j (T x + x) = 0)
    (B0 : Finset (Fin (k + 1))) (hB0 : (0 : Fin (k + 1)) ∉ B0 → ∀ x ∈ W, lam0 (T x + x) = 0) :
    (∀ x ∈ W, (∀ i, (Fin.cons lam0 lam' : Fin (k + 1) → (V n →ₗ[ZMod 2] ZMod 2)) i x = 0) →
      x = 0) ∧
    ∀ j, j ∉ B0 ∪ Bad'.map (Fin.succEmb k) → ∀ x ∈ W,
      (∀ i, i < j → (Fin.cons lam0 lam' : Fin (k + 1) → (V n →ₗ[ZMod 2] ZMod 2)) i x = 0) →
      (Fin.cons lam0 lam' : Fin (k + 1) → (V n →ₗ[ZMod 2] ZMod 2)) j (T x + x) = 0 := by
  constructor
  · intro x hx h
    apply hker x ⟨hx, by simpa using h 0⟩
    intro i
    simpa using h i.succ
  · intro j hj x hx h
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
    · have h0 : (0 : Fin (k + 1)) ∉ B0 := fun h' => hj (Finset.mem_union_left _ h')
      simpa using hB0 h0 x hx
    · have hj' : j' ∉ Bad' := by
        intro h'
        exact hj (Finset.mem_union_right _ (Finset.mem_map_of_mem _ h'))
      have hx0 : lam0 x = 0 := by simpa using h 0 (Fin.succ_pos j')
      simp only [Fin.cons_succ]
      apply hgood j' hj' x ⟨hx, hx0⟩
      intro i hi
      simpa using h i.succ (Fin.succ_lt_succ_iff.mpr hi)

def Pot (W : Submodule (ZMod 2) (V n)) (m : ℕ) : Prop :=
  ∀ p : (ZMod 2)[X], Irreducible p → p ≠ X + 1 →
    finrank (ZMod 2) (KT T W ⊓ LinearMap.ker (aeval T.toLinearMap p) : Submodule (ZMod 2) (V n)) /
      p.natDegree ≤ m

lemma al_pot_mono {W W' : Submodule (ZMod 2) (V n)} (h : W' ≤ W) {m : ℕ} (hp : Pot T W m) :
    Pot T W' m := by
  intro p hirr hne
  refine le_trans (Nat.div_le_div_right ?_) (hp p hirr hne)
  exact Submodule.finrank_mono (inf_le_inf_right _ (KT_mono T h))

def ChainP (k : ℕ) (W : Submodule (ZMod 2) (V n)) (m : ℕ) : Prop :=
  ∃ lam : Fin k → (V n →ₗ[ZMod 2] ZMod 2), (∀ x ∈ W, (∀ i, lam i x = 0) → x = 0) ∧
    ∃ Bad : Finset (Fin k), Bad.card ≤ m ∧
      ∀ j, j ∉ Bad → ∀ x ∈ W, (∀ i, i < j → lam i x = 0) → lam j (T x + x) = 0

lemma al_step_good {k : ℕ} (W : Submodule (ZMod 2) (V n)) (hW : finrank (ZMod 2) W = k + 1)
    (m : ℕ) (hpot : Pot T W m)
    (hA : ¬ W ≤ W.map (T.toLinearMap + LinearMap.id))
    (ih : ∀ W' : Submodule (ZMod 2) (V n), finrank (ZMod 2) W' = k → ∀ m, Pot T W' m →
      ChainP T k W' m) : ChainP T (k + 1) W m := by
  obtain ⟨w, hwW, hw⟩ := IsConcreteLE.not_le_iff_exists.mp hA
  obtain ⟨f, hf, hfmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  have hfβ : ∀ x ∈ W, f (T x + x) = 0 := by
    intro x hx
    have h1 : T x + x ∈ W.map (T.toLinearMap + LinearMap.id) :=
      ⟨x, hx, by simp⟩
    have h2 : f (T x + x) ∈ Submodule.map f (W.map (T.toLinearMap + LinearMap.id)) :=
      Submodule.mem_map_of_mem h1
    rw [hfmap] at h2
    exact (Submodule.mem_bot (ZMod 2)).mp h2
  have hdim : finrank (ZMod 2) (W ⊓ LinearMap.ker f : Submodule (ZMod 2) (V n)) = k := by
    have := al_finrank_hyp W f w hwW hf
    omega
  obtain ⟨lam', hker', Bad', hcard', hgood'⟩ :=
    ih _ hdim m (al_pot_mono T inf_le_left hpot)
  obtain ⟨h1, h2⟩ := al_cons T W f lam' Bad' hker' hgood' ∅ (fun _ => hfβ)
  refine ⟨Fin.cons f lam', h1, ∅ ∪ Bad'.map (Fin.succEmb k), ?_, h2⟩
  simpa using hcard'

lemma al_inj_of_le (W : Submodule (ZMod 2) (V n))
    (hA : W ≤ W.map (T.toLinearMap + LinearMap.id)) :
    (∀ x ∈ W, T x ∈ W) ∧ ∀ x ∈ W, T x + x = 0 → x = 0 := by
  set β : V n →ₗ[ZMod 2] V n := T.toLinearMap + LinearMap.id with hβ
  have heq : W = W.map β := Submodule.eq_of_le_of_finrank_le hA (Submodule.finrank_map_le β W)
  constructor
  · intro x hx
    have h1 : β x ∈ W := by
      rw [heq]
      exact Submodule.mem_map_of_mem hx
    have h2 : β x = T x + x := by simp [hβ]
    rw [h2] at h1
    have := W.sub_mem h1 hx
    simpa using this
  · intro x hx hx0
    have h1 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict W)
    rw [LinearMap.range_domRestrict, ← heq] at h1
    have h2 : LinearMap.ker (β.domRestrict W) = ⊥ := by
      apply Submodule.finrank_eq_zero.mp
      omega
    have h3 : (⟨x, hx⟩ : W) ∈ LinearMap.ker (β.domRestrict W) := by
      rw [LinearMap.mem_ker]
      simpa [hβ] using hx0
    rw [h2] at h3
    simpa using congrArg Subtype.val ((Submodule.mem_bot (ZMod 2)).mp h3)

lemma al_div_aux {a d b m : ℕ} (hd : 0 < d) (h1 : a + d ≤ b) (h2 : b / d ≤ m + 1) : a / d ≤ m := by
  have h3 : (a + d) / d ≤ b / d := Nat.div_le_div_right h1
  rw [Nat.add_div_right a hd] at h3
  omega

lemma al_step_bad {k : ℕ} (W : Submodule (ZMod 2) (V n)) (hW : finrank (ZMod 2) W = k + 1)
    (m : ℕ) (hpot : Pot T W m)
    (hA : W ≤ W.map (T.toLinearMap + LinearMap.id))
    (ih : ∀ W' : Submodule (ZMod 2) (V n), finrank (ZMod 2) W' = k → ∀ m, Pot T W' m →
      ChainP T k W' m) : ChainP T (k + 1) W m := by
  obtain ⟨hWT, hβinj⟩ := al_inj_of_le T W hA
  have hWbot : W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hW
    omega
  have hKT : KT T W = W := le_antisymm (KT_le T W) (le_KT T hWT)
  obtain ⟨p0, hp0, x1, hx1W, hx1p, hx10⟩ := al_exists_irred T W hWT hWbot
  have hp0ne : p0 ≠ X + 1 := by
    rintro rfl
    apply hx10
    apply hβinj x1 hx1W
    simpa using hx1p
  have hXT : ∀ p : (ZMod 2)[X], ∀ y ∈ (W ⊓ LinearMap.ker (aeval T.toLinearMap p) :
      Submodule (ZMod 2) (V n)), T y ∈ (W ⊓ LinearMap.ker (aeval T.toLinearMap p) :
      Submodule (ZMod 2) (V n)) := by
    intro p y hy
    exact ⟨hWT y hy.1, al_ker_inv T p y hy.2⟩
  have hm1 : 1 ≤ m := by
    have hg := al_gain T p0 hp0 _ ⊥ bot_le (fun y hy => by simp_all) (hXT p0) x1
      ⟨hx1W, hx1p⟩ (by simpa using hx10) hx1p
    rw [finrank_bot, zero_add] at hg
    have hpm := hpot p0 hp0 hp0ne
    rw [hKT] at hpm
    have hdpos : 0 < p0.natDegree := Irreducible.natDegree_pos hp0
    have : 1 ≤ finrank (ZMod 2) (W ⊓ LinearMap.ker (aeval T.toLinearMap p0) :
        Submodule (ZMod 2) (V n)) / p0.natDegree := by
      rw [Nat.le_div_iff_mul_le hdpos]
      omega
    omega
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨lam0, hlam0⟩ := al_select T W (polyS n)
  have hsel : ∀ p : (ZMod 2)[X], Irreducible p →
      (∃ x ∈ W, aeval T.toLinearMap p x = 0 ∧ x ≠ 0) →
      ∃ x ∈ W, aeval T.toLinearMap p x = 0 ∧ lam0 x ≠ 0 := by
    intro p hp hex
    obtain ⟨x, _, hxp, hx0⟩ := hex
    exact hlam0 p (mem_polyS (al_deg_le T p hp x hx0 hxp)) hp ⟨x, by assumption, hxp, hx0⟩
  obtain ⟨x2, hx2W, -, hx2⟩ := hsel p0 hp0 ⟨x1, hx1W, hx1p, hx10⟩
  have hdim : finrank (ZMod 2) (W ⊓ LinearMap.ker lam0 : Submodule (ZMod 2) (V n)) = k := by
    have := al_finrank_hyp W lam0 x2 hx2W hx2
    omega
  have hpot' : Pot T (W ⊓ LinearMap.ker lam0) m' := by
    intro p hp hpne
    by_cases hex : ∃ x ∈ W, aeval T.toLinearMap p x = 0 ∧ x ≠ 0
    · obtain ⟨x3, hx3W, hx3p, hx3⟩ := hsel p hp hex
      have hle : (KT T (W ⊓ LinearMap.ker lam0) ⊓ LinearMap.ker (aeval T.toLinearMap p) :
          Submodule (ZMod 2) (V n)) ≤ W ⊓ LinearMap.ker (aeval T.toLinearMap p) :=
        inf_le_inf_right _ ((KT_le T _).trans inf_le_left)
      have hg := al_gain T p hp _ _ hle
        (fun y hy => ⟨KT_T T hy.1, al_ker_inv T p y hy.2⟩) (hXT p) x3 ⟨hx3W, hx3p⟩
        (fun h => hx3 (((KT_le T _) h.1).2)) hx3p
      have hpm := hpot p hp hpne
      rw [hKT] at hpm
      exact al_div_aux (Irreducible.natDegree_pos hp) hg hpm
    · push Not at hex
      have hbot : (KT T (W ⊓ LinearMap.ker lam0) ⊓ LinearMap.ker (aeval T.toLinearMap p) :
          Submodule (ZMod 2) (V n)) = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        exact hex x (((KT_le T _) hx.1).1) hx.2
      rw [hbot, finrank_bot, Nat.zero_div]
      omega
  obtain ⟨lam', hker', Bad', hcard', hgood'⟩ := ih _ hdim m' hpot'
  obtain ⟨h1, h2⟩ := al_cons T W lam0 lam' Bad' hker' hgood' {0} (fun h => absurd (by simp) h)
  refine ⟨Fin.cons lam0 lam', h1, {0} ∪ Bad'.map (Fin.succEmb k), ?_, h2⟩
  calc ({0} ∪ Bad'.map (Fin.succEmb k)).card ≤ ({0} : Finset (Fin (k + 1))).card +
        (Bad'.map (Fin.succEmb k)).card := Finset.card_union_le _ _
    _ ≤ m' + 1 := by simp; omega

lemma al_chain (k : ℕ) : ∀ W : Submodule (ZMod 2) (V n), finrank (ZMod 2) W = k → ∀ m,
    Pot T W m → ChainP T k W m := by
  induction k with
  | zero =>
    intro W hW m _
    have hb : W = ⊥ := Submodule.finrank_eq_zero.mp hW
    refine ⟨Fin.elim0, fun x hx _ => ?_, ∅, by simp, fun j => Fin.elim0 j⟩
    rw [hb] at hx
    exact (Submodule.mem_bot (ZMod 2)).mp hx
  | succ k ih =>
    intro W hW m hpot
    by_cases hA : W ≤ W.map (T.toLinearMap + LinearMap.id)
    · exact al_step_bad T W hW m hpot hA ih
    · exact al_step_good T W hW m hpot hA ih

theorem alg_main {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (m : ℕ)
    (hm : ∀ p : (ZMod 2)[X], Irreducible p → p ≠ X + 1 →
      finrank (ZMod 2) (LinearMap.ker (aeval T.toLinearMap p)) / p.natDegree ≤ m) :
    ∃ (Φ : V n ≃ₗ[ZMod 2] V n) (Bad : Finset (Fin n)), Bad.card ≤ m ∧
      ∀ j : Fin n, j ∉ Bad → ∀ v : V n, (∀ i : Fin n, i < j → Φ v i = 0) →
        Φ (T v + v) j = 0 := by
  have hpot : Pot T ⊤ m := by
    intro p hp hpne
    refine le_trans (Nat.div_le_div_right ?_) (hm p hp hpne)
    exact Submodule.finrank_mono inf_le_right
  have hdim : finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (V n)) = n := by
    rw [finrank_top, Module.finrank_fin_fun]
  obtain ⟨lam, hker, Bad, hcard, hgood⟩ := al_chain T n ⊤ hdim m hpot
  let Φ0 : V n →ₗ[ZMod 2] V n := LinearMap.pi lam
  have hinj : Function.Injective Φ0 := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    apply hker x trivial
    intro i
    have := congrFun hx i
    simpa [Φ0] using this
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  let Φ := LinearEquiv.ofBijective Φ0 ⟨hinj, hsurj⟩
  have hΦ : ∀ v i, Φ v i = lam i v := by
    intro v i
    rfl
  refine ⟨Φ, Bad, hcard, ?_⟩
  intro j hj v hv
  rw [hΦ]
  exact hgood j hj v trivial (fun i hi => by rw [← hΦ]; exact hv i hi)

end Alg




def Anode {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) (p : List Bool) :
    Finset (ZMod 2 × V n) :=
  Finset.univ.filter (fun w => ∀ j : Fin p.length, q (p.take j.val) w = p.get j)

def Pnode {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (q : List Bool → (ZMod 2 × V n) → Bool)
    (p : List Bool) : Finset (V n) :=
  Finset.univ.filter (fun o => ((0 : ZMod 2), o) ∈ Anode q p ∧ ((1 : ZMod 2), T o + b) ∈ Anode q p)

def Lv (N J : Finset (List Bool)) (p : List Bool) : Finset (List Bool) :=
  (N \ J).filter (fun r => p <+: r)

theorem lw_path_iff {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) (p : List Bool)
    (w : ZMod 2 × V n) :
    (∀ j : Fin p.length, q (p.take j.val) w = p.get j) ↔
      ∀ (j : ℕ) (h : j < p.length), q (p.take j) w = p[j] := by
  constructor
  · intro H j h
    exact H ⟨j, h⟩
  · intro H j
    exact H j.val j.isLt

theorem lw_path_snoc {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) (p : List Bool) (c : Bool)
    (w : ZMod 2 × V n) :
    (∀ (j : ℕ) (h : j < (p ++ [c]).length), q ((p ++ [c]).take j) w = (p ++ [c])[j]) ↔
      (∀ (j : ℕ) (h : j < p.length), q (p.take j) w = p[j]) ∧ q p w = c := by
  constructor
  · intro H
    refine ⟨fun j h => ?_, ?_⟩
    · have h2 : j < (p ++ [c]).length := by simp; omega
      have := H j h2
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left h] at this
      exact this
    · have h2 : p.length < (p ++ [c]).length := by simp
      have := H p.length h2
      simpa using this
  · rintro ⟨H1, H2⟩ j h
    have hj : j < p.length ∨ j = p.length := by simp at h; omega
    rcases hj with hj | hj
    · rw [List.take_append_of_le_length (by omega), List.getElem_append_left hj]
      exact H1 j hj
    · subst hj
      simpa using H2

theorem lw_mem_anode {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) (p : List Bool)
    (w : ZMod 2 × V n) :
    w ∈ Anode q p ↔ ∀ (j : ℕ) (h : j < p.length), q (p.take j) w = p[j] := by
  rw [← lw_path_iff]
  simp [Anode]

theorem lw_anode_child {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) (p : List Bool) (c : Bool) :
    Anode q (p ++ [c]) = (Anode q p).filter (fun w => q p w = c) := by
  ext w
  rw [Finset.mem_filter, lw_mem_anode, lw_mem_anode, lw_path_snoc]

theorem lw_anode_root {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) :
    Anode q [] = Finset.univ := by
  ext w
  simp [lw_mem_anode]

theorem lw_card_univ (n : ℕ) : (Finset.univ : Finset (ZMod 2 × V n)).card = 2 * 2 ^ n := by
  simp [Finset.card_univ, Fintype.card_prod]

theorem lw_card_univ' (n : ℕ) : (Finset.univ : Finset (V n)).card = 2 ^ n := by
  simp [Finset.card_univ]

theorem lw_anode_split {n : ℕ} (q : List Bool → (ZMod 2 × V n) → Bool) (p : List Bool) :
    (Anode q p).card = (Anode q (p ++ [false])).card + (Anode q (p ++ [true])).card := by
  rw [lw_anode_child, lw_anode_child]
  rw [← Finset.card_filter_add_card_filter_not (s := Anode q p) (p := fun w => q p w = false)]
  congr 2
  apply Finset.filter_congr
  intro x _
  simp

theorem lw_lv_root (N J : Finset (List Bool)) : Lv N J [] = N \ J := by
  ext r
  simp [Lv]

theorem lw_lv_leaf (N J : Finset (List Bool)) (r : List Bool) (hr : r ∈ N \ J) :
    1 ≤ (Lv N J r).card := by
  apply Finset.card_pos.mpr
  exact ⟨r, by simp [Lv]; simpa using hr⟩

theorem lw_lv_disj (N J : Finset (List Bool)) (r : List Bool) :
    Disjoint (Lv N J (r ++ [false])) (Lv N J (r ++ [true])) := by
  rw [Finset.disjoint_left]
  intro s h0 h1
  simp only [Lv, Finset.mem_filter] at h0 h1
  have := List.IsPrefix.eq_of_length (List.prefix_of_prefix_length_le h0.2 h1.2 (by simp)) (by simp)
  simp at this

theorem lw_lv_sub (N J : Finset (List Bool)) (r : List Bool) (c : Bool) :
    Lv N J (r ++ [c]) ⊆ Lv N J r := by
  intro s hs
  simp only [Lv, Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, (List.prefix_append r [c]).trans hs.2⟩

theorem lw_lv_child (N J : Finset (List Bool)) (r : List Bool) :
    (Lv N J (r ++ [false])).card + (Lv N J (r ++ [true])).card ≤ (Lv N J r).card := by
  rw [← Finset.card_union_of_disjoint (lw_lv_disj N J r)]
  apply Finset.card_le_card
  exact Finset.union_subset (lw_lv_sub N J r false) (lw_lv_sub N J r true)

def Claim {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (pp : (ZMod 2)[X]) (r : List Bool) : Prop :=
  ∀ (U : Submodule (ZMod 2) (V n)) (k : ℕ), (∀ u ∈ U, T u ∈ U) →
    (∀ u ∈ U, aeval T.toLinearMap pp u = 0) → k * pp.natDegree ≤ finrank (ZMod 2) U →
    (∀ o ∈ Pnode T b q r, ∀ u ∈ U, o + u ∈ Pnode T b q r) →
    2 ^ k * (Anode q r).card ≤ 2 ^ k * (Lv N J r).card + (Pnode T b q r).card

theorem lw_zmod_ne (x : ZMod 2) (h : x ≠ 0) : x = 1 := by
  revert x h
  decide

theorem lw_leaf_pt {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n)
    (hc : Cert T b N J q out) (r : List Bool) (hr : r ∈ N \ J) (w : ZMod 2 × V n)
    (hw : w ∈ Anode q r) : w = (0, out r) ∨ w = (1, T (out r) + b) := by
  have h := hc.2.2 r hr w (by simpa [Anode] using hw)
  obtain ⟨w1, w2⟩ := w
  by_cases h1 : w1 = 0
  · subst h1
    simp at h
    left
    rw [h]
  · have h' : w2 = T (out r) + b := by simpa [h1] using h
    right
    rw [lw_zmod_ne w1 h1, h']

theorem lw_leaf_pnode {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n)
    (hc : Cert T b N J q out) (r : List Bool) (hr : r ∈ N \ J) :
    Pnode T b q r ⊆ {out r} := by
  intro o ho
  simp only [Pnode, Finset.mem_filter] at ho
  rcases lw_leaf_pt T b N J q out hc r hr _ ho.2.1 with h | h
  · simp at h
    simp [h]
  · simp at h

theorem lw_leaf_anode {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n)
    (hc : Cert T b N J q out) (r : List Bool) (hr : r ∈ N \ J) :
    (Anode q r).card ≤ 1 + (Pnode T b q r).card := by
  have hsub : Anode q r ⊆ {(0, out r), (1, T (out r) + b)} := by
    intro w hw
    rcases lw_leaf_pt T b N J q out hc r hr w hw with h | h <;> simp [h]
  by_cases h0 : ((0 : ZMod 2), out r) ∈ Anode q r
  · by_cases h1 : ((1 : ZMod 2), T (out r) + b) ∈ Anode q r
    · have hp : out r ∈ Pnode T b q r := by simp [Pnode, h0, h1]
      have := Finset.card_le_card hsub
      have h2 := Finset.card_le_two (a := ((0 : ZMod 2), out r)) (b := ((1 : ZMod 2), T (out r) + b))
      have h3 := Finset.card_pos.mpr ⟨_, hp⟩
      omega
    · have : Anode q r ⊆ {(0, out r)} := by
        intro w hw
        rcases lw_leaf_pt T b N J q out hc r hr w hw with h | h
        · simp [h]
        · subst h; exact absurd hw h1
      have := Finset.card_le_card this
      simp at this
      omega
  · have : Anode q r ⊆ {(1, T (out r) + b)} := by
      intro w hw
      rcases lw_leaf_pt T b N J q out hc r hr w hw with h | h
      · subst h; exact absurd hw h0
      · simp [h]
    have := Finset.card_le_card this
    simp at this
    omega

theorem lw_leaf_claim {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n)
    (hc : Cert T b N J q out) (pp : (ZMod 2)[X]) (hirr : Irreducible pp)
    (r : List Bool) (hr : r ∈ N \ J) : Claim T b N J q pp r := by
  intro U k _ _ hk hcl
  have hA := lw_leaf_anode T b N J q out hc r hr
  have hL := lw_lv_leaf N J r hr
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    simp only [pow_zero, one_mul]
    omega
  · have hP : Pnode T b q r = ∅ := by
      by_contra hne
      obtain ⟨o, ho⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hU : U = ⊥ := by
        rw [eq_bot_iff]
        intro u hu
        have h1 := lw_leaf_pnode T b N J q out hc r hr ho
        have h2 := lw_leaf_pnode T b N J q out hc r hr (hcl o ho u hu)
        simp at h1 h2
        rw [Submodule.mem_bot]
        rw [h1] at h2
        simpa using h2
      rw [hU, finrank_bot] at hk
      have := hirr.natDegree_pos
      have : 0 < k * pp.natDegree := Nat.mul_pos hpos this
      omega
    rw [hP, Finset.card_empty] at hA ⊢
    have : 2 ^ k * (Anode q r).card ≤ 2 ^ k * (Lv N J r).card :=
      Nat.mul_le_mul_left _ (by omega)
    omega

def Sset {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (q : List Bool → (ZMod 2 × V n) → Bool)
    (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (r : List Bool) : Finset (V n) :=
  (Pnode T b q r).filter (fun o => l (0, o) = l (1, T o + b))

theorem lw_l_zero {n : ℕ} (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (o u : V n) :
    l (0, o + u) = l (0, o) + l (0, u) := by
  rw [← map_add, Prod.mk_add_mk, add_zero]

theorem lw_l_one {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2)
    (o u : V n) : l (1, T (o + u) + b) = l (1, T o + b) + l (0, T u) := by
  rw [← map_add, Prod.mk_add_mk, add_zero, map_add]
  congr 2
  abel

theorem lw_dec_eq (a c b0 : ZMod 2) (h : decide (a = b0) = decide (c = b0)) : a = c := by
  revert a c b0 h
  decide

theorem lw_dec_shift (a b0 : ZMod 2) : decide (a + 0 = b0) = decide (a = b0) := by
  rw [add_zero]

theorem lw_pnode_child_S {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n)
    (q : List Bool → (ZMod 2 × V n) → Bool) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (b0 : ZMod 2)
    (r : List Bool) (hq : q r = fun w => decide (l w = b0)) (c : Bool) :
    Pnode T b q (r ++ [c]) ⊆ Sset T b q l r := by
  intro o ho
  simp only [Pnode, Finset.mem_filter, Finset.mem_univ, true_and, lw_anode_child, hq] at ho
  simp only [Sset, Pnode, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨ho.1.1, ho.2.1⟩, lw_dec_eq _ _ b0 ?_⟩
  rw [ho.1.2, ho.2.2]

theorem lw_pnode_child_disj {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n)
    (q : List Bool → (ZMod 2 × V n) → Bool) (r : List Bool) :
    Disjoint (Pnode T b q (r ++ [false])) (Pnode T b q (r ++ [true])) := by
  rw [Finset.disjoint_left]
  intro o h0 h1
  simp only [Pnode, Finset.mem_filter, Finset.mem_univ, true_and, lw_anode_child] at h0 h1
  rw [h0.1.2] at h1
  exact Bool.false_ne_true h1.1.2

theorem lw_pnode_child_card {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n)
    (q : List Bool → (ZMod 2 × V n) → Bool) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (b0 : ZMod 2)
    (r : List Bool) (hq : q r = fun w => decide (l w = b0)) :
    (Pnode T b q (r ++ [false])).card + (Pnode T b q (r ++ [true])).card ≤
      (Sset T b q l r).card := by
  rw [← Finset.card_union_of_disjoint (lw_pnode_child_disj T b q r)]
  apply Finset.card_le_card
  exact Finset.union_subset (lw_pnode_child_S T b q l b0 r hq false)
    (lw_pnode_child_S T b q l b0 r hq true)

theorem lw_S_le {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n)
    (q : List Bool → (ZMod 2 × V n) → Bool) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2)
    (r : List Bool) : (Sset T b q l r).card ≤ (Pnode T b q r).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem lw_child_closed {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n)
    (q : List Bool → (ZMod 2 × V n) → Bool) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (b0 : ZMod 2)
    (r : List Bool) (hq : q r = fun w => decide (l w = b0)) (U : Submodule (ZMod 2) (V n))
    (hUT : ∀ u ∈ U, T u ∈ U) (hUl : ∀ u ∈ U, l (0, u) = 0)
    (hcl : ∀ o ∈ Pnode T b q r, ∀ u ∈ U, o + u ∈ Pnode T b q r) (c : Bool) :
    ∀ o ∈ Pnode T b q (r ++ [c]), ∀ u ∈ U, o + u ∈ Pnode T b q (r ++ [c]) := by
  intro o ho u hu
  have hsub := lw_pnode_child_S T b q l b0 r hq c ho
  simp only [Sset, Finset.mem_filter] at hsub
  have h2 := hcl o hsub.1 u hu
  simp only [Pnode, Finset.mem_filter, Finset.mem_univ, true_and, lw_anode_child, hq] at ho h2 ⊢
  refine ⟨⟨h2.1, ?_⟩, ⟨h2.2, ?_⟩⟩
  · rw [lw_l_zero, hUl u hu, lw_dec_shift]
    exact ho.1.2
  · rw [lw_l_one, hUl _ (hUT u hu), lw_dec_shift]
    exact ho.2.2

theorem lw_zmod_sum (x y z : ZMod 2) (hxy : x = y) (hz : z ≠ 0) : x + z ≠ y := by
  revert x y z hxy hz
  decide

theorem lw_S_double {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n)
    (q : List Bool → (ZMod 2 × V n) → Bool) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2)
    (r : List Bool) (u1 : V n) (hu1 : l (0, T u1 + u1) ≠ 0)
    (hcl : ∀ o ∈ Pnode T b q r, o + u1 ∈ Pnode T b q r) :
    2 * (Sset T b q l r).card ≤ (Pnode T b q r).card := by
  have hdisj : Disjoint (Sset T b q l r) ((Sset T b q l r).image (fun o => o + u1)) := by
    rw [Finset.disjoint_left]
    intro o ho ho'
    obtain ⟨o', hos, he⟩ := Finset.mem_image.mp ho'
    subst he
    simp only [Sset, Finset.mem_filter] at ho hos
    have hx := ho.2
    rw [lw_l_zero, lw_l_one] at hx
    have e : l (0, o') + l (0, u1) = l (0, o') + l (0, T u1) + l (0, T u1 + u1) := by
      rw [lw_l_zero]
      ring_nf
      have : (2 : ZMod 2) = 0 := rfl
      rw [this]
      ring
    rw [e, hos.2] at hx
    exact lw_zmod_sum _ _ _ rfl hu1 hx
  have hcard : ((Sset T b q l r).image (fun o => o + u1)).card = (Sset T b q l r).card :=
    Finset.card_image_of_injective _ (add_left_injective u1)
  have hsub : Sset T b q l r ∪ (Sset T b q l r).image (fun o => o + u1) ⊆ Pnode T b q r := by
    apply Finset.union_subset (Finset.filter_subset _ _)
    intro x hx
    obtain ⟨o', ho', he⟩ := Finset.mem_image.mp hx
    subst he
    exact hcl o' (Finset.filter_subset _ _ ho')
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hcard] at this
  omega

theorem lw_case1 {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (pp : (ZMod 2)[X])
    (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (b0 : ZMod 2)
    (r : List Bool) (hq : q r = fun w => decide (l w = b0))
    (C0 : Claim T b N J q pp (r ++ [false])) (C1 : Claim T b N J q pp (r ++ [true]))
    (U : Submodule (ZMod 2) (V n)) (k : ℕ) (hUT : ∀ u ∈ U, T u ∈ U)
    (hUp : ∀ u ∈ U, aeval T.toLinearMap pp u = 0) (hk : k * pp.natDegree ≤ finrank (ZMod 2) U)
    (hcl : ∀ o ∈ Pnode T b q r, ∀ u ∈ U, o + u ∈ Pnode T b q r) (hUl : ∀ u ∈ U, l (0, u) = 0) :
    2 ^ k * (Anode q r).card ≤ 2 ^ k * (Lv N J r).card + (Pnode T b q r).card := by
  have h0 := C0 U k hUT hUp hk (lw_child_closed T b q l b0 r hq U hUT hUl hcl false)
  have h1 := C1 U k hUT hUp hk (lw_child_closed T b q l b0 r hq U hUT hUl hcl true)
  have hA := lw_anode_split q r
  have hL := Nat.mul_le_mul_left (2 ^ k) (lw_lv_child N J r)
  have hP := lw_pnode_child_card T b q l b0 r hq
  have hS := lw_S_le T b q l r
  rw [hA, Nat.mul_add]
  rw [Nat.mul_add] at hL
  omega

theorem lw_case2 {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (pp : (ZMod 2)[X]) (hirr : Irreducible pp)
    (hne : pp ≠ X + 1) (l : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2) (b0 : ZMod 2)
    (r : List Bool) (hq : q r = fun w => decide (l w = b0))
    (C0 : Claim T b N J q pp (r ++ [false])) (C1 : Claim T b N J q pp (r ++ [true]))
    (U : Submodule (ZMod 2) (V n)) (k : ℕ) (hUT : ∀ u ∈ U, T u ∈ U)
    (hUp : ∀ u ∈ U, aeval T.toLinearMap pp u = 0)
    (hk : (k + 1) * pp.natDegree ≤ finrank (ZMod 2) U)
    (hcl : ∀ o ∈ Pnode T b q r, ∀ u ∈ U, o + u ∈ Pnode T b q r)
    (u0 : V n) (hu0 : u0 ∈ U) (hl0 : l (0, u0) ≠ 0) :
    2 ^ (k + 1) * (Anode q r).card ≤ 2 ^ (k + 1) * (Lv N J r).card + (Pnode T b q r).card := by
  obtain ⟨u1, hu1, he⟩ := alg_preimage T pp hirr hne U hUT hUp u0 hu0
  have hD := lw_S_double T b q l r u1 (by rw [he]; exact hl0) (fun o ho => hcl o ho u1 hu1)
  obtain ⟨U', hle, hUT', hμ, hfr⟩ :=
    alg_shrink T pp hirr U hUT hUp (l.comp (LinearMap.inr (ZMod 2) (ZMod 2) (V n)))
  have hUl : ∀ u ∈ U', l (0, u) = 0 := fun u hu => by simpa using hμ u hu
  have hUp' : ∀ u ∈ U', aeval T.toLinearMap pp u = 0 := fun u hu => hUp u (hle hu)
  have hcl' : ∀ o ∈ Pnode T b q r, ∀ u ∈ U', o + u ∈ Pnode T b q r :=
    fun o ho u hu => hcl o ho u (hle hu)
  have hk' : k * pp.natDegree ≤ finrank (ZMod 2) U' := by
    rw [Nat.add_mul, one_mul] at hk
    omega
  have h0 := C0 U' k hUT' hUp' hk' (lw_child_closed T b q l b0 r hq U' hUT' hUl hcl' false)
  have h1 := C1 U' k hUT' hUp' hk' (lw_child_closed T b q l b0 r hq U' hUT' hUl hcl' true)
  have hA := lw_anode_split q r
  have hL := Nat.mul_le_mul_left (2 ^ (k + 1)) (lw_lv_child N J r)
  have hP := lw_pnode_child_card T b q l b0 r hq
  rw [hA, Nat.mul_add, pow_succ]
  rw [Nat.mul_add, pow_succ] at hL
  have e0 := Nat.mul_le_mul_right 2 h0
  have e1 := Nat.mul_le_mul_right 2 h1
  rw [Nat.add_mul] at e0 e1
  have r0 : 2 ^ k * 2 * (Anode q (r ++ [false])).card =
      2 ^ k * (Anode q (r ++ [false])).card * 2 := by ring
  have r1 : 2 ^ k * 2 * (Anode q (r ++ [true])).card =
      2 ^ k * (Anode q (r ++ [true])).card * 2 := by ring
  have r2 : 2 ^ k * 2 * (Lv N J (r ++ [false])).card =
      2 ^ k * (Lv N J (r ++ [false])).card * 2 := by ring
  have r3 : 2 ^ k * 2 * (Lv N J (r ++ [true])).card =
      2 ^ k * (Lv N J (r ++ [true])).card * 2 := by ring
  omega

theorem lw_internal {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (pp : (ZMod 2)[X]) (hirr : Irreducible pp)
    (hne : pp ≠ X + 1) (r : List Bool) (hQ : IsQ (q r))
    (C0 : Claim T b N J q pp (r ++ [false])) (C1 : Claim T b N J q pp (r ++ [true])) :
    Claim T b N J q pp r := by
  obtain ⟨l, b0, hq⟩ := hQ
  intro U k hUT hUp hk hcl
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    have := lw_case1 T b N J q pp l b0 r hq C0 C1 ⊥ 0 (by simp) (by simp) (by simp)
      (by intro o ho u hu; rw [Submodule.mem_bot] at hu; rw [hu, add_zero]; exact ho)
      (by intro u hu; rw [Submodule.mem_bot] at hu; rw [hu]; exact map_zero l)
    exact this
  · by_cases hall : ∀ u ∈ U, l (0, u) = 0
    · exact lw_case1 T b N J q pp l b0 r hq C0 C1 U k hUT hUp hk hcl hall
    · obtain ⟨u0, hu0, hl0⟩ : ∃ u0 ∈ U, l (0, u0) ≠ 0 := by
        by_contra hcon
        apply hall
        intro u hu
        by_contra h'
        exact hcon ⟨u, hu, h'⟩
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact lw_case2 T b N J q pp hirr hne l b0 r hq C0 C1 U k' hUT hUp hk hcl u0 hu0 hl0

theorem lw_all_claim {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n)
    (hc : Cert T b N J q out) (pp : (ZMod 2)[X]) (hirr : Irreducible pp) (hne : pp ≠ X + 1) :
    ∀ m : ℕ, ∀ r ∈ N, N.sup List.length + 1 ≤ r.length + m → Claim T b N J q pp r := by
  intro m
  induction m with
  | zero =>
    intro r hr hlen
    have := Finset.le_sup (f := List.length) hr
    omega
  | succ m ih =>
    intro r hr hlen
    by_cases hJ : r ∈ J
    · have hch := hc.1.2.2.2 r hJ
      apply lw_internal T b N J q pp hirr hne r (hc.2.1 r hJ)
      · exact ih (r ++ [false]) hch.1 (by rw [List.length_append, List.length_singleton]; omega)
      · exact ih (r ++ [true]) hch.2 (by rw [List.length_append, List.length_singleton]; omega)
    · exact lw_leaf_claim T b N J q out hc pp hirr r (Finset.mem_sdiff.mpr ⟨hr, hJ⟩)

theorem lw_ker_inv {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (pp : (ZMod 2)[X]) (u : V n)
    (hu : u ∈ LinearMap.ker (aeval T.toLinearMap pp)) :
    T u ∈ LinearMap.ker (aeval T.toLinearMap pp) := by
  rw [LinearMap.mem_ker] at hu ⊢
  have e : aeval T.toLinearMap (pp * X) = aeval T.toLinearMap (X * pp) := by rw [mul_comm]
  rw [map_mul, map_mul, aeval_X] at e
  have := LinearMap.congr_fun e u
  simp only [mul_apply_eq_comp, LinearEquiv.coe_coe] at this
  rw [this, hu, map_zero]

theorem lower_main {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n)
    (hc : Cert T b N J q out) (pp : (ZMod 2)[X]) (hirr : Irreducible pp) (hne : pp ≠ X + 1)
    (k : ℕ) (hk : k * pp.natDegree ≤ finrank (ZMod 2) (LinearMap.ker (aeval T.toLinearMap pp))) :
    2 ^ k * 2 ^ (n + 1) ≤ 2 ^ k * (N \ J).card + 2 ^ n := by
  have C := lw_all_claim T b N J q out hc pp hirr hne (N.sup List.length + 1) [] hc.1.1
    (by simp)
  have hP : Pnode T b q [] = Finset.univ := by
    ext o
    simp [Pnode, lw_anode_root]
  have H := C (LinearMap.ker (aeval T.toLinearMap pp)) k (lw_ker_inv T pp)
    (fun u hu => LinearMap.mem_ker.mp hu) hk (by intro o _ u _; rw [hP]; exact Finset.mem_univ _)
  rw [lw_anode_root, lw_card_univ, lw_lv_root, hP, lw_card_univ'] at H
  rw [pow_succ, mul_comm (2 ^ n) 2]
  exact H



def up_bit (c : Bool) : ZMod 2 := if c then 1 else 0

lemma up_z2 (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

lemma up_dec (c w y : ZMod 2) (β : Bool) (h : decide (c * w + y = 1) = β) :
    y = up_bit β + c * w := by
  revert h; revert c w y β; decide

lemma up_bit_dec (a : ZMod 2) : up_bit (decide (a = 1)) = a := by
  revert a; decide

section defs
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

def up_av (p : List Bool) : Fin n → ZMod 2 := fun i => up_bit (p.getD i false)

def up_xv (p : List Bool) : V n := Φ.symm (up_av p)

def up_lam (j : ℕ) (v : V n) : ZMod 2 := if h : j < n then Φ v ⟨j, h⟩ else 0

def up_cc (p : List Bool) : ZMod 2 := up_lam Φ p.length (T (up_xv Φ p) + up_xv Φ p + b)

def up_lq (p : List Bool) : ZMod 2 × V n →ₗ[ZMod 2] ZMod 2 :=
  if h : p.length < n then
    up_cc T b Φ p • LinearMap.fst _ _ _ +
      ((LinearMap.proj ⟨p.length, h⟩) ∘ₗ Φ.toLinearMap) ∘ₗ LinearMap.snd _ _ _
  else LinearMap.fst _ _ _

def up_q (p : List Bool) (w : ZMod 2 × V n) : Bool := decide (up_lq T b Φ p w = 1)

def up_yv (p : List Bool) : V n := Φ.symm (fun i => up_av p i + up_cc T b Φ (p.take i))

def up_isPair (p : List Bool) : Bool := decide (up_yv T b Φ p = T (up_xv Φ p) + b)

def up_out (p : List Bool) : V n :=
  if p.getD n false then T.symm (up_yv T b Φ p - b) else up_xv Φ p

def up_Ln (k : ℕ) : Finset (List Bool) := (Finset.univ : Finset (Fin k → Bool)).image List.ofFn

def up_NP : Finset (List Bool) := (up_Ln n).filter (fun p => up_isPair T b Φ p = false)

def up_ch (p : List Bool) : Finset (List Bool) := {p ++ [false], p ++ [true]}

def up_N : Finset (List Bool) :=
  (Finset.range (n + 1)).biUnion up_Ln ∪ (up_NP T b Φ).biUnion up_ch

def up_J : Finset (List Bool) := (Finset.range n).biUnion up_Ln ∪ up_NP T b Φ

end defs

lemma up_mem_Ln (k : ℕ) (p : List Bool) : p ∈ up_Ln k ↔ p.length = k := by
  constructor
  · intro h
    simp only [up_Ln, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨f, rfl⟩ := h
    simp
  · intro h
    subst h
    simp only [up_Ln, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨p.get, List.ofFn_get p⟩

lemma up_card_Ln (k : ℕ) : (up_Ln k).card ≤ 2 ^ k := by
  unfold up_Ln
  refine Finset.card_image_le.trans ?_
  simp

section shape
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

lemma up_mem_NP (p : List Bool) :
    p ∈ up_NP T b Φ ↔ p.length = n ∧ up_isPair T b Φ p = false := by
  simp [up_NP, up_mem_Ln]

lemma up_mem_N (p : List Bool) : p ∈ up_N T b Φ ↔
    p.length < n + 1 ∨ ∃ a ∈ up_NP T b Φ, p = a ++ [false] ∨ p = a ++ [true] := by
  simp [up_N, up_mem_Ln, up_ch]

lemma up_mem_J (p : List Bool) : p ∈ up_J T b Φ ↔ p.length < n ∨ p ∈ up_NP T b Φ := by
  simp [up_J, up_mem_Ln]

lemma up_snoc_inj (p a : List Bool) (c d : Bool) (h : p ++ [c] = a ++ [d]) : p = a := by
  have := congrArg List.dropLast h
  simpa using this

lemma up_shape : Shape (up_N T b Φ) (up_J T b Φ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [up_mem_N]; left; simp
  · intro p hp
    rw [up_mem_J] at hp
    rw [up_mem_N]
    rcases hp with hp | hp
    · left; omega
    · left; rw [up_mem_NP] at hp; omega
  · intro p c hp
    rw [up_mem_N] at hp
    rw [up_mem_J]
    rcases hp with hp | ⟨a, ha, h | h⟩
    · left; simp at hp; omega
    · right; rwa [up_snoc_inj p a c false h]
    · right; rwa [up_snoc_inj p a c true h]
  · intro p hp
    rw [up_mem_J] at hp
    rw [up_mem_N, up_mem_N]
    rcases hp with hp | hp
    · constructor <;> (left; simp; omega)
    · exact ⟨Or.inr ⟨p, hp, Or.inl rfl⟩, Or.inr ⟨p, hp, Or.inr rfl⟩⟩

lemma up_leaf (p : List Bool) (hp : p ∈ up_N T b Φ \ up_J T b Φ) :
    (p.length = n ∧ up_isPair T b Φ p = true) ∨
      ∃ a ∈ up_NP T b Φ, p = a ++ [false] ∨ p = a ++ [true] := by
  rw [Finset.mem_sdiff, up_mem_N, up_mem_J, up_mem_NP] at hp
  obtain ⟨h1 | h1, h2⟩ := hp
  · left
    have hl : p.length = n := by omega
    refine ⟨hl, ?_⟩
    cases h : up_isPair T b Φ p
    · exact absurd (Or.inr ⟨hl, h⟩) h2
    · rfl
  · right; exact h1

end shape

section corr
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

lemma up_lq_lt (p : List Bool) (h : p.length < n) (w : ZMod 2 × V n) :
    up_lq T b Φ p w = up_cc T b Φ p * w.1 + Φ w.2 ⟨p.length, h⟩ := by
  simp [up_lq, h]

lemma up_lq_ge (p : List Bool) (h : ¬ p.length < n) (w : ZMod 2 × V n) :
    up_lq T b Φ p w = w.1 := by
  simp [up_lq, h]

lemma up_isQ (p : List Bool) : IsQ (up_q T b Φ p) := ⟨up_lq T b Φ p, 1, rfl⟩

lemma up_coord (p : List Bool) (hlen : n ≤ p.length) (w : ZMod 2 × V n)
    (hpath : ∀ j : Fin p.length, up_q T b Φ (p.take j.val) w = p.get j) (j : Fin n) :
    Φ w.2 j = up_av p j + up_cc T b Φ (p.take j) * w.1 := by
  have hj : j.val < p.length := by omega
  have h : up_q T b Φ (p.take j.val) w = p.get ⟨j.val, hj⟩ := hpath ⟨j.val, hj⟩
  have hl : (p.take j.val).length = j.val := by simp; omega
  unfold up_q at h
  rw [up_lq_lt T b Φ _ (by rw [hl]; exact j.2)] at h
  have h2 := up_dec _ _ _ _ h
  simp only [hl] at h2
  rw [h2]
  congr 2
  simp [List.getD_eq_getElem?_getD, hj]

lemma up_path0 (p : List Bool) (hlen : n ≤ p.length) (w : ZMod 2 × V n)
    (hpath : ∀ j : Fin p.length, up_q T b Φ (p.take j.val) w = p.get j) (h0 : w.1 = 0) :
    w.2 = up_xv Φ p := by
  unfold up_xv
  rw [LinearEquiv.eq_symm_apply]
  funext j
  rw [up_coord T b Φ p hlen w hpath j, h0]
  simp

lemma up_path1 (p : List Bool) (hlen : n ≤ p.length) (w : ZMod 2 × V n)
    (hpath : ∀ j : Fin p.length, up_q T b Φ (p.take j.val) w = p.get j) (h1 : w.1 = 1) :
    w.2 = up_yv T b Φ p := by
  unfold up_yv
  rw [LinearEquiv.eq_symm_apply]
  funext j
  rw [up_coord T b Φ p hlen w hpath j, h1]
  simp

end corr

section corr2
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

lemma up_corr_pair (p : List Bool) (hl : p.length = n) (hpair : up_isPair T b Φ p = true)
    (w : ZMod 2 × V n)
    (hpath : ∀ j : Fin p.length, up_q T b Φ (p.take j.val) w = p.get j) :
    if w.1 = 0 then w.2 = up_out T b Φ p else w.2 = T (up_out T b Φ p) + b := by
  have ho : up_out T b Φ p = up_xv Φ p := by
    simp [up_out, List.getD_eq_getElem?_getD, hl]
  rw [ho]
  rcases up_z2 w.1 with h | h
  · rw [ite_eq_left h]; exact up_path0 T b Φ p hl.ge w hpath h
  · rw [ite_eq_right (by rw [h]; decide)]
    rw [up_path1 T b Φ p hl.ge w hpath h]
    simpa [up_isPair] using hpair

lemma up_corr_ch (a : List Bool) (c : Bool) (hl : a.length = n) (w : ZMod 2 × V n)
    (hpath : ∀ j : Fin (a ++ [c]).length,
      up_q T b Φ ((a ++ [c]).take j.val) w = (a ++ [c]).get j) :
    if w.1 = 0 then w.2 = up_out T b Φ (a ++ [c]) else w.2 = T (up_out T b Φ (a ++ [c])) + b := by
  have hlen : n ≤ (a ++ [c]).length := by simp; omega
  have hq : up_q T b Φ a w = c := by
    have h := hpath ⟨n, by simp; omega⟩
    simpa [← hl] using h
  unfold up_q at hq
  rw [up_lq_ge T b Φ a (by omega)] at hq
  have hg : (a ++ [c]).getD n false = c := by
    simp [List.getD_eq_getElem?_getD, ← hl]
  unfold up_out
  rw [hg]
  cases c
  · have h0 : w.1 = 0 := by
      rcases up_z2 w.1 with h | h
      · exact h
      · simp [h] at hq
    rw [ite_eq_left h0]
    simpa using up_path0 T b Φ _ hlen w hpath h0
  · have h1 : w.1 = 1 := by simpa using hq
    rw [ite_eq_right (by rw [h1]; decide)]
    simpa using up_path1 T b Φ _ hlen w hpath h1

lemma up_corr (p : List Bool) (hp : p ∈ up_N T b Φ \ up_J T b Φ) (w : ZMod 2 × V n)
    (hpath : ∀ j : Fin p.length, up_q T b Φ (p.take j.val) w = p.get j) :
    if w.1 = 0 then w.2 = up_out T b Φ p else w.2 = T (up_out T b Φ p) + b := by
  rcases up_leaf T b Φ p hp with ⟨hl, hpair⟩ | ⟨a, ha, h | h⟩
  · exact up_corr_pair T b Φ p hl hpair w hpath
  · subst h; exact up_corr_ch T b Φ a false ((up_mem_NP T b Φ a).1 ha).1 w hpath
  · subst h; exact up_corr_ch T b Φ a true ((up_mem_NP T b Φ a).1 ha).1 w hpath

end corr2

section count
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

def up_P : Finset (List Bool) := (up_Ln n).filter (fun p => up_isPair T b Φ p = true)

lemma up_leaves_sub : up_N T b Φ \ up_J T b Φ ⊆ up_P T b Φ ∪ (up_NP T b Φ).biUnion up_ch := by
  intro p hp
  rcases up_leaf T b Φ p hp with ⟨hl, hpair⟩ | ⟨a, ha, h⟩
  · apply Finset.mem_union_left
    simp [up_P, up_mem_Ln, hl, hpair]
  · apply Finset.mem_union_right
    rw [Finset.mem_biUnion]
    refine ⟨a, ha, ?_⟩
    rcases h with h | h <;> simp [up_ch, h]

lemma up_leaves_card :
    (up_N T b Φ \ up_J T b Φ).card ≤ (up_P T b Φ).card + 2 * (up_NP T b Φ).card := by
  refine (Finset.card_le_card (up_leaves_sub T b Φ)).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine Nat.add_le_add_left ?_ _
  refine Finset.card_biUnion_le.trans ?_
  have : ∀ a ∈ up_NP T b Φ, (up_ch a).card ≤ 2 := fun a _ => Finset.card_le_two
  refine (Finset.sum_le_sum this).trans ?_
  simp [mul_comm]

lemma up_PNP_card : (up_P T b Φ).card + (up_NP T b Φ).card ≤ 2 ^ n := by
  have h := Finset.card_filter_add_card_filter_not
    (s := up_Ln n) (fun p => up_isPair T b Φ p = true)
  have h2 := up_card_Ln n
  unfold up_P up_NP
  simp only [Bool.not_eq_true] at h
  omega

end count

section px
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

def up_px (x : V n) : List Bool := List.ofFn (fun i : Fin n => decide (Φ x i = 1))

def up_tr (i : ℕ) : V n →ₗ[ZMod 2] V n :=
  Φ.symm.toLinearMap ∘ₗ
    (LinearMap.pi (fun j : Fin n => if j.val < i then LinearMap.proj j else 0)) ∘ₗ Φ.toLinearMap

lemma up_Φ_tr (i : ℕ) (x : V n) (j : Fin n) :
    Φ (up_tr Φ i x) j = if j.val < i then Φ x j else 0 := by
  simp only [up_tr, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, LinearMap.pi_apply]
  split_ifs <;> simp

lemma up_px_len (x : V n) : (up_px Φ x).length = n := by simp [up_px]

lemma up_av_take (x : V n) (i : ℕ) (j : Fin n) :
    up_av ((up_px Φ x).take i) j = if j.val < i then Φ x j else 0 := by
  simp only [up_av, up_px, List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs
  · simp [up_bit_dec]
  · simp [up_bit]

lemma up_av_px (x : V n) : up_av (up_px Φ x) = Φ x := by
  funext j
  have h := up_av_take Φ x n j
  rw [List.take_of_length_le (by rw [up_px_len])] at h
  rw [h, ite_eq_left j.2]

lemma up_xv_px (x : V n) : up_xv Φ (up_px Φ x) = x := by
  simp [up_xv, up_av_px]

lemma up_xv_take (x : V n) (i : ℕ) : up_xv Φ ((up_px Φ x).take i) = up_tr Φ i x := by
  unfold up_xv
  rw [LinearEquiv.symm_apply_eq]
  funext j
  rw [up_av_take, up_Φ_tr]

lemma up_cc_take (x : V n) (i : Fin n) :
    up_cc T b Φ ((up_px Φ x).take i) = Φ (T (up_tr Φ i x) + up_tr Φ i x + b) i := by
  have hl : ((up_px Φ x).take i.val).length = i.val := by
    simp [up_px_len]
  unfold up_cc
  rw [hl, up_xv_take]
  simp [up_lam, i.2]

end px

lemma up_alg (A B C D E : ZMod 2) (h : A + B + (C + D) = 0) (hD : D = 0) :
    C + (B + D + E) = A + E := by
  revert h hD; revert A B C D E; decide

lemma up_alg2 (a : ZMod 2) : a + a = 0 := by
  revert a; decide

section pair
variable {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)

lemma up_pair_of (x : V n)
    (h : ∀ i : Fin n, Φ (T (x + up_tr Φ i x) + (x + up_tr Φ i x)) i = 0) :
    up_isPair T b Φ (up_px Φ x) = true := by
  unfold up_isPair
  rw [decide_eq_true_eq, up_xv_px]
  unfold up_yv
  rw [LinearEquiv.symm_apply_eq]
  funext i
  rw [up_av_px, up_cc_take]
  have hi := h i
  have hD : Φ (up_tr Φ i x) i = 0 := by rw [up_Φ_tr, ite_eq_right (lt_irrefl _)]
  simp only [map_add, Pi.add_apply] at hi ⊢
  exact up_alg _ _ _ _ _ hi hD

lemma up_good (Bad : Finset (Fin n))
    (hgood : ∀ j : Fin n, j ∉ Bad → ∀ v : V n, (∀ i : Fin n, i < j → Φ v i = 0) →
      Φ (T v + v) j = 0)
    (x : V n) (i : Fin n) (hi : i ∉ Bad) :
    Φ (T (x + up_tr Φ i x) + (x + up_tr Φ i x)) i = 0 := by
  apply hgood i hi
  intro k hk
  rw [map_add, Pi.add_apply, up_Φ_tr, ite_eq_left (show k.val < i.val from hk)]
  exact up_alg2 _

def up_Psi (Bad : Finset (Fin n)) : V n →ₗ[ZMod 2] (Bad → ZMod 2) :=
  LinearMap.pi (fun i : Bad => (LinearMap.proj (i : Fin n)) ∘ₗ Φ.toLinearMap ∘ₗ
    (T.toLinearMap + LinearMap.id) ∘ₗ (LinearMap.id + up_tr Φ (i : Fin n)))

lemma up_Psi_apply (Bad : Finset (Fin n)) (x : V n) (i : Bad) :
    up_Psi T Φ Bad x i =
      Φ (T (x + up_tr Φ (i : Fin n) x) + (x + up_tr Φ (i : Fin n) x)) (i : Fin n) := by
  simp [up_Psi]

lemma up_ker_pair (Bad : Finset (Fin n))
    (hgood : ∀ j : Fin n, j ∉ Bad → ∀ v : V n, (∀ i : Fin n, i < j → Φ v i = 0) →
      Φ (T v + v) j = 0)
    (x : V n) (hx : up_Psi T Φ Bad x = 0) : up_px Φ x ∈ up_P T b Φ := by
  unfold up_P
  rw [Finset.mem_filter, up_mem_Ln, up_px_len]
  refine ⟨rfl, up_pair_of T b Φ x ?_⟩
  intro i
  by_cases hi : i ∈ Bad
  · have := congrFun hx ⟨i, hi⟩
    rwa [up_Psi_apply] at this
  · exact up_good T Φ Bad hgood x i hi

lemma up_ker_rank (Bad : Finset (Fin n)) :
    n - Bad.card ≤ finrank (ZMod 2) (LinearMap.ker (up_Psi T Φ Bad)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (up_Psi T Φ Bad)
  have h2 := Submodule.finrank_le (LinearMap.range (up_Psi T Φ Bad))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
  rw [Module.finrank_fin_fun] at h1
  omega

lemma up_P_card (Bad : Finset (Fin n))
    (hgood : ∀ j : Fin n, j ∉ Bad → ∀ v : V n, (∀ i : Fin n, i < j → Φ v i = 0) →
      Φ (T v + v) j = 0) :
    2 ^ (n - Bad.card) ≤ (up_P T b Φ).card := by
  classical
  have hk : 2 ^ (n - Bad.card) ≤ Fintype.card (LinearMap.ker (up_Psi T Φ Bad)) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    exact Nat.pow_le_pow_right (by norm_num) (up_ker_rank T Φ Bad)
  refine hk.trans ?_
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun x => up_px Φ (x : V n)) ?_ ?_
  · intro x _
    exact up_ker_pair T b Φ Bad hgood x (LinearMap.mem_ker.1 x.2)
  · intro x _ y _ hxy
    apply Subtype.ext
    have := congrArg (up_xv Φ) hxy
    simpa [up_xv_px] using this

end pair

theorem upper_main {n : ℕ} (T : V n ≃ₗ[ZMod 2] V n) (b : V n) (Φ : V n ≃ₗ[ZMod 2] V n)
    (Bad : Finset (Fin n)) (m : ℕ) (hBad : Bad.card ≤ m)
    (hgood : ∀ j : Fin n, j ∉ Bad → ∀ v : V n, (∀ i : Fin n, i < j → Φ v i = 0) → Φ (T v + v) j = 0) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × V n) → Bool) (out : List Bool → V n),
      Cert T b N J q out ∧ (N \ J).card + 2 ^ (n - m) ≤ 2 ^ (n + 1) := by
  refine ⟨up_N T b Φ, up_J T b Φ, up_q T b Φ, up_out T b Φ, ⟨up_shape T b Φ,
    fun p _ => up_isQ T b Φ p, fun p hp w hpath => up_corr T b Φ p hp w hpath⟩, ?_⟩
  have h1 := up_leaves_card T b Φ
  have h2 := up_PNP_card T b Φ
  have h3 := up_P_card T b Φ Bad hgood
  have h4 : 2 ^ (n - m) ≤ 2 ^ (n - Bad.card) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega


end PEqualNP.Outside.L_pcx_372_aux

theorem PEqualNP.Outside.L_pcx_372 : (let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ n : ℕ,
    let V := Fin n → ZMod 2
    ∀ (T : V ≃ₗ[ZMod 2] V) (b : V),
      let h := sSup {j : ℕ | ∃ p : Polynomial (ZMod 2),
        Irreducible p ∧ p ≠ Polynomial.X + 1 ∧
        j = Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap p)) / p.natDegree}
      ∀ K : ℕ,
        (∃ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × V) → Bool)
           (out : List Bool → V), cert (queries (ZMod 2 × V))
             (fun z x => if z.1 = 0 then z.2 = x else z.2 = T x + b) N J q out ∧
           (N \ J).card ≤ K) ↔ 2^(n+1) ≤ K + 2^(n-h)) := by
  intro shape queries cert n V0 T b h K
  have hbdd : BddAbove {j : ℕ | ∃ p : Polynomial (ZMod 2),
        Irreducible p ∧ p ≠ Polynomial.X + 1 ∧
        j = Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap p)) / p.natDegree} := by
    refine ⟨n, ?_⟩
    rintro j ⟨p, -, -, rfl⟩
    calc _ ≤ Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap p)) :=
          Nat.div_le_self _ _
      _ ≤ Module.finrank (ZMod 2) (Fin n → ZMod 2) := Submodule.finrank_le _
      _ = n := Module.finrank_fin_fun _
  have hmem : h ∈ {j : ℕ | ∃ p : Polynomial (ZMod 2),
        Irreducible p ∧ p ≠ Polynomial.X + 1 ∧
        j = Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap p)) / p.natDegree} := by
    apply Nat.sSup_mem _ hbdd
    refine ⟨_, Polynomial.X, Polynomial.irreducible_X, ?_, rfl⟩
    intro hX
    have := congrArg (fun r : Polynomial (ZMod 2) => r.coeff 0) hX
    simp at this
  obtain ⟨pp, hirr, hne, hpp⟩ := hmem
  constructor
  · rintro ⟨N, J, q, out, hc, hK⟩
    have hdeg : 0 < pp.natDegree := Irreducible.natDegree_pos hirr
    have hk : h * pp.natDegree ≤
        Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap pp)) := by
      rw [hpp]; exact Nat.div_mul_le_self _ _
    have hhn : h ≤ n := by
      have h1 : Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap pp)) ≤ n := by
        calc _ ≤ Module.finrank (ZMod 2) (Fin n → ZMod 2) := Submodule.finrank_le _
          _ = n := Module.finrank_fin_fun _
      nlinarith
    have := PEqualNP.Outside.L_pcx_372_aux.lower_main T b N J q out hc pp hirr hne h hk
    have h2 : 2 ^ n = 2 ^ h * 2 ^ (n - h) := by rw [← pow_add]; congr 1; omega
    rw [h2] at this
    have h3 : 2 ^ (n + 1) ≤ (N \ J).card + 2 ^ (n - h) := by
      have hpos : 0 < 2 ^ h := by positivity
      have : 2 ^ h * 2 ^ (n + 1) ≤ 2 ^ h * ((N \ J).card + 2 ^ (n - h)) := by
        rw [mul_add]; exact this
      exact Nat.le_of_mul_le_mul_left this hpos
    omega
  · intro hK
    have hm : ∀ p : Polynomial (ZMod 2), Irreducible p → p ≠ Polynomial.X + 1 →
        Module.finrank (ZMod 2) (LinearMap.ker (Polynomial.aeval T.toLinearMap p)) / p.natDegree ≤ h :=
      fun p hp hp2 => le_csSup hbdd ⟨p, hp, hp2, rfl⟩
    obtain ⟨Φ, Bad, hBad, hgood⟩ := PEqualNP.Outside.L_pcx_372_aux.alg_main T h hm
    obtain ⟨N, J, q, out, hc, hcard⟩ := PEqualNP.Outside.L_pcx_372_aux.upper_main T b Φ Bad h hBad hgood
    exact ⟨N, J, q, out, hc, by omega⟩
