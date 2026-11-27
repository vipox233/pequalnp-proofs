import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_859

open Polynomial

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K] [Fintype K]

private lemma fieldCard {d : ℕ} (hdim : Module.finrank (ZMod 2) K = 2 * d) :
    Fintype.card K = (2 ^ d) * (2 ^ d) := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hdim, two_mul, pow_add]

private lemma powerAboveOne {d : ℕ} (hd : 0 < d) : 1 < (2 : ℕ) ^ d := by
  simpa using Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hd

private lemma primitiveSlope {d : ℕ} (hd : 0 < d) (hdim : Module.finrank (ZMod 2) K = 2 * d) :
    ∃ root : K, IsPrimitiveRoot root (2 ^ d + 1) := by
  let q := (2 : ℕ) ^ d
  have hq : 1 < q := powerAboveOne hd
  have hfac : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, Nat.card_eq_fintype_card, fieldCard hdim]
    change q * q - 1 = (q + 1) * (q - 1)
    have hpred : q - 1 + 1 = q := by omega
    have hprod : q * q = (q + 1) * (q - 1) + 1 := by nlinarith
    omega
  obtain ⟨unit, hunit⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Kˣ)
  rw [hfac] at hunit
  have hne : q - 1 ≠ 0 := by omega
  have horder : orderOf (unit ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow_of_dvd hne ⟨q + 1, by rw [hunit, mul_comm]⟩, hunit,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hne)]
  have hprimitive := IsPrimitiveRoot.iff_orderOf.mpr horder
  exact ⟨_, hprimitive.map_of_injective (f := Units.coeHom K) Units.val_injective⟩

private def slopes (q : ℕ) (K : Type) [Field K] : Submonoid K where
  carrier := {root | root ^ (q + 1) = 1}
  one_mem' := one_pow _
  mul_mem' hleft hright := by
    change _ ^ (q + 1) = _ at hleft hright
    change (_ * _) ^ (q + 1) = _
    rw [mul_pow, hleft, hright, one_mul]

private lemma slopesSpan {d : ℕ} (hd : 0 < d) (hdim : Module.finrank (ZMod 2) K = 2 * d)
    {root : K} (hprimitive : IsPrimitiveRoot root (2 ^ d + 1)) :
    Submodule.span (ZMod 2) (slopes (2 ^ d) K : Set K) = ⊤ := by
  let S := slopes (2 ^ d) K
  let E := Algebra.IsAlgebraic.toIntermediateField (Algebra.adjoin (ZMod 2) (S : Set K))
  have hspan : E.toSubalgebra.toSubmodule = Submodule.span (ZMod 2) (S : Set K) := by
    change (Algebra.adjoin (ZMod 2) (S : Set K)).toSubmodule = _
    rw [Algebra.adjoin_eq_span, S.closure_eq]
  let initial : E := ⟨root, Algebra.subset_adjoin hprimitive.pow_eq_one⟩
  letI := Fintype.ofFinite E
  have hcard : Fintype.card E = 2 ^ Module.finrank (ZMod 2) E := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hne : initial ≠ 0 := by
    intro hzero
    have hroot : root = 0 := congrArg Subtype.val hzero
    have := hprimitive.pow_eq_one
    rw [hroot, zero_pow (Nat.succ_ne_zero (2 ^ d))] at this
    exact zero_ne_one this
  have hdiv : 2 ^ d + 1 ∣ Fintype.card E - 1 := by
    apply hprimitive.dvd_of_pow_eq_one
    exact congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one initial hne)
  have hlarge : d < Module.finrank (ZMod 2) E := by
    have hle := Nat.le_of_dvd (by have := Fintype.one_lt_card (α := E); omega : 0 < Fintype.card E - 1) hdiv
    rw [hcard] at hle
    by_contra! hsmall
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hsmall
    omega
  have hdimprod := Module.finrank_mul_finrank (ZMod 2) E K
  rw [hdim] at hdimprod
  have hone : Module.finrank E K = 1 := by
    have hpos : 0 < Module.finrank E K := Module.finrank_pos
    by_contra hne
    have htwo : 2 ≤ Module.finrank E K := by omega
    have := Nat.mul_le_mul_left (Module.finrank (ZMod 2) E) htwo
    omega
  have hfulldim : Module.finrank (ZMod 2) E = Module.finrank (ZMod 2) K := by
    rw [hdim, ← hdimprod, hone, mul_one]
  rw [← hspan]
  exact Submodule.eq_top_of_finrank_eq hfulldim

private lemma augmentedBasis {d : ℕ} (hd : 0 < d) (hdim : Module.finrank (ZMod 2) K = 2 * d) :
    ∃ basis : Module.Basis (Fin (2 * d + 1)) (ZMod 2) (ZMod 2 × K),
      ∀ idx, (basis idx).1 = 1 ∧ (basis idx).2 ^ (2 ^ d + 1) = 1 := by
  obtain ⟨root, hroot⟩ := primitiveSlope hd hdim
  let S := slopes (2 ^ d) K
  let points : Set (ZMod 2 × K) := {pair | pair.1 = 1 ∧ pair.2 ∈ S}
  let W := Submodule.span (ZMod 2) points
  have hpoint {value : K} (hvalue : value ∈ S) : ((1 : ZMod 2), value) ∈ W := by
    exact Submodule.subset_span ⟨rfl, hvalue⟩
  have hbase : ((1 : ZMod 2), (0 : K)) ∈ W := by
    have hsum := W.sum_mem (t := Finset.range (2 ^ d + 1))
      (f := fun idx : ℕ => ((1 : ZMod 2), root ^ idx))
      (fun idx _ => hpoint (by change (root ^ idx) ^ (2 ^ d + 1) = 1
                               rw [← pow_mul, mul_comm idx, pow_mul, hroot.pow_eq_one, one_pow]))
    have hcast : ((2 ^ d + 1 : ℕ) : ZMod 2) = 1 := by
      rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, show ((2 : ℕ) : ZMod 2) = 0 by decide,
        zero_pow hd.ne', zero_add]
    have hgeom := hroot.geom_sum_eq_zero (by have := powerAboveOne hd; omega)
    have heq : (∑ idx ∈ Finset.range (2 ^ d + 1), ((1 : ZMod 2), root ^ idx)) = (1, 0) := by
      apply Prod.ext
      · change AddMonoidHom.fst (ZMod 2) K (∑ idx ∈ Finset.range (2 ^ d + 1), (1, root ^ idx)) = 1
        rw [map_sum]
        change (∑ _ ∈ Finset.range (2 ^ d + 1), (1 : ZMod 2)) = 1
        simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_range] using hcast
      · change AddMonoidHom.snd (ZMod 2) K (∑ idx ∈ Finset.range (2 ^ d + 1), (1, root ^ idx)) = 0
        rw [map_sum]
        exact hgeom
    exact heq ▸ hsum
  let includeSecond : K →ₗ[ZMod 2] (ZMod 2 × K) := LinearMap.inr (ZMod 2) (ZMod 2) K
  have hinclude : Submodule.span (ZMod 2) (S : Set K) ≤ W.comap includeSecond := by
    apply Submodule.span_le.mpr
    intro value hvalue
    change ((0 : ZMod 2), value) ∈ W
    simpa using W.sub_mem (hpoint hvalue) hbase
  rw [slopesSpan hd hdim hroot] at hinclude
  have htop : W = ⊤ := by
    apply top_unique
    intro pair _
    have hleft := W.smul_mem pair.1 hbase
    have hright : ((0 : ZMod 2), pair.2) ∈ W := hinclude (Submodule.mem_top : pair.2 ∈ ⊤)
    simpa using W.add_mem hleft hright
  obtain ⟨vectors, hvectors, hsp, hind⟩ := Submodule.exists_fun_fin_finrank_span_eq (ZMod 2) points
  have hcard : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) points) = 2 * d + 1 := by
    rw [show Submodule.span (ZMod 2) points = ⊤ from htop, finrank_top, Module.finrank_prod,
      Module.finrank_self, hdim, add_comm 1]
  let basis := Module.Basis.mk hind (hsp.trans htop).ge
  refine ⟨basis.reindex (finCongr hcard), fun idx => ?_⟩
  have hvec := hvectors ((finCongr hcard).symm idx)
  change (vectors _).1 = 1 ∧ (vectors _).2 ^ (2 ^ d + 1) = 1 at hvec
  simpa [basis] using hvec

private noncomputable def frob (d : ℕ) : K →ₐ[ZMod 2] K :=
  ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) ^ d).toAlgHom

private lemma frobApply (d : ℕ) (value : K) : frob d value = value ^ (2 ^ d) := by
  simp only [frob, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

private noncomputable def piece (d : ℕ) (slope : K) : K →ₗ[ZMod 2] K :=
  (frob d).toLinearMap + LinearMap.mulLeft (ZMod 2) slope

private lemma pieceApply (d : ℕ) (slope value : K) :
    piece d slope value = value ^ (2 ^ d) + slope * value := by
  simp [piece, frobApply]

private lemma pieceKerBound {d : ℕ} (hd : 0 < d) {slope : K} (hslope : slope ≠ 0) :
    Module.finrank (ZMod 2) (LinearMap.ker (piece d slope)) ≤ d := by
  classical
  let p : K[X] := X ^ (2 ^ d) + C slope * X
  have hp : p.natDegree = 2 ^ d := by
    have hlt : natDegree (C slope * X) < natDegree ((X : K[X]) ^ (2 ^ d)) := by
      simpa [natDegree_C_mul_X _ hslope] using powerAboveOne hd
    simp [p, natDegree_add_eq_left_of_natDegree_lt hlt]
  have hpne : p ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hp
    exact (pow_ne_zero d (by decide : (2 : ℕ) ≠ 0)) hp.symm
  letI := Fintype.ofFinite (LinearMap.ker (piece d slope))
  have hcard : Fintype.card (LinearMap.ker (piece d slope)) ≤ p.roots.toFinset.card := by
    rw [← Fintype.card_coe]
    refine Fintype.card_le_of_injective (fun value => (⟨value.1, ?_⟩ : ↥p.roots.toFinset)) ?_
    · have hzero := LinearMap.mem_ker.mp value.2
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne, Polynomial.IsRoot]
      simpa only [p, eval_add, eval_mul, eval_pow, eval_X, eval_C, ← pieceApply] using hzero
    · intro left right heq
      exact Subtype.ext (congrArg (fun root : ↥p.roots.toFinset => (root : K)) heq)
  have hbound := hcard.trans ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' p))
  rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hp] at hbound
  by_contra! hlt
  exact (Nat.not_lt_of_ge hbound) (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hlt)

private lemma pieceRank {d : ℕ} (hd : 0 < d) (hdim : Module.finrank (ZMod 2) K = 2 * d)
    {slope : K} (hslope : slope ^ (2 ^ d + 1) = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (piece d slope)) = d := by
  let q := (2 : ℕ) ^ d
  have hsne : slope ≠ 0 := by
    intro hzero
    simp [hzero] at hslope
  have htwo : (2 : K) = 0 := by
    haveI := charP_of_injective_algebraMap' (ZMod 2) (A := K) 2
    exact CharP.cast_eq_zero K 2
  have hdouble (value : K) : value + value = 0 := by linear_combination value * htwo
  have hcancel : LinearMap.range (piece d slope) ≤ LinearMap.ker (piece d (slope ^ q)) := by
    rintro _ ⟨value, rfl⟩
    rw [LinearMap.mem_ker, pieceApply, ← frobApply, pieceApply, map_add, map_mul,
      frobApply, frobApply, frobApply, ← pow_mul, ← fieldCard hdim, FiniteField.pow_card]
    change value + slope ^ q * value ^ q + slope ^ q * (value ^ q + slope * value) = 0
    have hone : slope ^ q * slope = 1 := by simpa [pow_succ, q] using hslope
    calc
      _ = (value + value) + (slope ^ q * value ^ q + slope ^ q * value ^ q) := by
        rw [mul_add, ← mul_assoc (slope ^ q) slope value, hone, one_mul]
        ac_rfl
      _ = 0 := by rw [hdouble, hdouble, zero_add]
  have hUpper := (Submodule.finrank_mono hcancel).trans (pieceKerBound hd (pow_ne_zero q hsne))
  have hLower := pieceKerBound hd hsne
  have htotal := (piece d slope).finrank_range_add_finrank_ker
  omega

private lemma sumCoordinates {ι : Type} [Fintype ι] [DecidableEq ι]
    (basis : Module.Basis ι (ZMod 2) (ZMod 2 × K)) (pair : ZMod 2 × K) :
    ∃! members : Finset ι, (∑ idx ∈ members, basis idx) = pair := by
  let coeff := basis.equivFun pair
  have binary (scalar : ZMod 2) : scalar = 0 ∨ scalar = 1 := by
    have hval := scalar.val_lt
    rw [← scalar.natCast_zmod_val]
    rcases (show scalar.val = 0 ∨ scalar.val = 1 by omega) with hzero | hone <;> simp [*]
  let members := Finset.univ.filter fun idx => coeff idx = 1
  refine ⟨members, ?_, ?_⟩
  · change (∑ idx ∈ members, basis idx) = pair
    calc
      _ = ∑ idx, coeff idx • basis idx := by
        change (∑ idx ∈ Finset.univ.filter (fun idx => coeff idx = 1), basis idx) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro idx _
        rcases binary (coeff idx) with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = pair := basis.sum_equivFun pair
  · intro other hother
    ext idx
    have hrepr : (∑ index ∈ other, basis.equivFun (basis index)) idx = coeff idx := by
      rw [← map_sum, hother]
    simp only [Finset.sum_apply, Module.Basis.equivFun_self, Finset.sum_ite_eq'] at hrepr
    simp only [members, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hmem : idx ∈ other
    · rw [if_pos hmem] at hrepr
      simp [hmem, ← hrepr]
    · rw [if_neg hmem] at hrepr
      simp [hmem, ← hrepr]

private lemma evenRepresentations {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (basis : Module.Basis ι (ZMod 2) (ZMod 2 × K)) (hbasis : ∀ idx, (basis idx).1 = 1)
    (target : K) : ∃! members : Finset ι,
      Even members.card ∧ ∀ value : K, ∑ idx ∈ members, piece d (basis idx).2 value = target * value := by
  have sumEven (members : Finset ι) (heven : Even members.card) (value : K) :
      (∑ idx ∈ members, piece d (basis idx).2 value) = (∑ idx ∈ members, (basis idx).2) * value := by
    have hzero : members.card • value ^ ((2 : ℕ) ^ d) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2), heven.natCast_zmod_two, zero_smul]
    simp only [pieceApply, Finset.sum_add_distrib, Finset.sum_const, hzero, zero_add, Finset.sum_mul]
  have sumFirst (members : Finset ι) :
      (∑ idx ∈ members, basis idx).1 = (members.card : ZMod 2) := by
    change AddMonoidHom.fst (ZMod 2) K (∑ idx ∈ members, basis idx) = _
    rw [map_sum]
    simp [hbasis, nsmul_eq_mul]
  have sumSecond (members : Finset ι) :
      (∑ idx ∈ members, basis idx).2 = ∑ idx ∈ members, (basis idx).2 := by
    exact map_sum (AddMonoidHom.snd (ZMod 2) K) _ _
  obtain ⟨members, hmem, hunique⟩ := sumCoordinates basis (0, target)
  have hEven : Even members.card := ZMod.natCast_eq_zero_iff_even.mp (by rw [← sumFirst, hmem])
  refine ⟨members, ⟨hEven, fun value => ?_⟩, fun other hother => ?_⟩
  · rw [sumEven _ hEven, ← sumSecond, hmem]
  · apply hunique other
    apply Prod.ext
    · rw [sumFirst, hother.1.natCast_zmod_two]
    · rw [sumSecond]
      simpa using (sumEven other hother.1 1).symm.trans (hother.2 1)

private lemma minimumPieces {d s : ℕ} (hd : 0 < d) (hdim : Module.finrank (ZMod 2) K = 2 * d)
    (maps : Fin s → (K →ₗ[ZMod 2] K))
    (hsmall : ∀ idx, Module.finrank (ZMod 2) (LinearMap.range (maps idx)) ≤ d)
    (hcover : ∀ z : K, ∃ members : Finset (Fin s), ∀ value : K, ∑ idx ∈ members, maps idx value = z * value) :
    2 * d + 1 ≤ s := by
  let mulMap : K →ₗ[ZMod 2] (K →ₗ[ZMod 2] K) := (Algebra.lmul (ZMod 2) K).toLinearMap
  let W := Submodule.span (ZMod 2) (Set.range maps)
  have hle : LinearMap.range mulMap ≤ W := by
    rintro _ ⟨target, rfl⟩
    obtain ⟨members, hmembers⟩ := hcover target
    have heq : mulMap target = ∑ idx ∈ members, maps idx := by
      ext value
      simpa [mulMap, Algebra.coe_lmul_eq_mul, LinearMap.sum_apply] using (hmembers value).symm
    rw [heq]
    exact W.sum_mem fun idx _ => Submodule.subset_span ⟨idx, rfl⟩
  have hrange : Module.finrank (ZMod 2) (LinearMap.range mulMap) = 2 * d := by
    have hinj : Function.Injective mulMap := Algebra.lmul_injective (R := ZMod 2) (A := K)
    rw [LinearMap.finrank_range_of_inj hinj, hdim]
  have hspan : Module.finrank (ZMod 2) W ≤ s := by
    simpa only [W, Set.finrank, Fintype.card_fin] using (finrank_range_le_card (R := ZMod 2) maps)
  by_contra! hlt
  have heq : LinearMap.range mulMap = W := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have hzero (idx : Fin s) : maps idx = 0 := by
    have hmem : maps idx ∈ W := Submodule.subset_span ⟨idx, rfl⟩
    rw [← heq] at hmem
    obtain ⟨target, htarget⟩ := hmem
    by_cases hne : target = 0
    · simp [← htarget, hne]
    · have hinj : Function.Injective (maps idx) := by
        rw [← htarget]
        intro left right heq
        exact mul_left_cancel₀ hne heq
      have := hsmall idx
      rw [LinearMap.finrank_range_of_inj hinj, hdim] at this
      omega
  obtain ⟨members, hmembers⟩ := hcover 1
  have heval := hmembers 1
  simp [hzero] at heval

end PEqualNP.Outside.L_lib_859

theorem PEqualNP.Outside.L_lib_859 : (let F := ZMod 2
∀ (d : ℕ), 0 < d →
  ∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
    Module.finrank F K = 2*d →
    ∃ (a : Fin (2*d+1) → K) (D : Fin (2*d+1) → (K →ₗ[F] K)),
      (∀ i, (a i)^(2^d+1) = 1) ∧
      (∀ i x, D i x = x^(2^d) + a i*x) ∧
      (∀ i, Module.finrank F (LinearMap.range (D i)) = d) ∧
      (∀ z : K, ∃! S : Finset (Fin (2*d+1)),
        Even S.card ∧ ∀ x : K, ∑ i ∈ S, D i x = z*x) ∧
      (∀ (s : ℕ) (A : Fin s → (K →ₗ[F] K)),
        (∀ i, Module.finrank F (LinearMap.range (A i)) ≤ d) →
        (∀ z : K, ∃ S : Finset (Fin s), ∀ x : K, ∑ i ∈ S, A i x = z*x) →
        2*d+1 ≤ s)) := by
  classical
  dsimp only
  intro d hd K _ _ _ _ hdim
  obtain ⟨basis, hbasis⟩ := PEqualNP.Outside.L_lib_859.augmentedBasis hd hdim
  exact ⟨fun idx => (basis idx).2, fun idx => PEqualNP.Outside.L_lib_859.piece d (basis idx).2,
    fun idx => (hbasis idx).2, fun idx => PEqualNP.Outside.L_lib_859.pieceApply d (basis idx).2,
    fun idx => PEqualNP.Outside.L_lib_859.pieceRank hd hdim (hbasis idx).2,
    PEqualNP.Outside.L_lib_859.evenRepresentations basis (fun idx => (hbasis idx).1),
    fun _ => PEqualNP.Outside.L_lib_859.minimumPieces hd hdim⟩
