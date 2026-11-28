import Mathlib
import PEqualNP.Defs

-- Ported from lean/PEqualNP/Outside/L_meta_26031.lean at c367024cb966e92eee14d1ca63bd92675aeafb41.
-- Retained only the construction and pairing helpers.
-- The circuit rank calculation uses the helper closure from PEqualNP/Outside/L_meta_25647.lean
-- at 14f1d40321543ada6b5b9b937060aad03bb935b7, licensed under Apache-2.0.
-- Adapted by restricting it to private declarations and bridging singleton output taps.

namespace PEqualNP.Outside.L_meta_29944_aux


namespace RankDrop

-- The multiplication-pairing and singular-correction arguments adapt helpers
-- from PEqualNP/Outside/L_meta_26031.lean at c367024cb966e92eee14d1ca63bd92675aeafb41.

open Module

section BitFactor

variable {F E K : Type*} [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

/-- A fixed nonzero output bit on `E` can recover any input bit on `K` after
an `E`-linear map. Use the perfect multiplication pairing on `E` to recover
that map from all the scalar translates of the input bit. -/
private theorem factorBit [FiniteDimensional F E]
    (β : E →ₗ[F] F) (hβ : β ≠ 0) (bit : K →ₗ[F] F) (hb : bit ≠ 0) :
    ∃ L : K →ₗ[E] E, L ≠ 0 ∧ ∀ x, β (L x) = bit x := by
  let b := Module.finBasis F E
  let P : E →ₗ[F] (Fin (finrank F E) → F) :=
    LinearMap.pi fun i => β.comp (LinearMap.mulLeft F (b i))
  have hP : ∀ x i, P x i = β (b i * x) := fun _ _ => rfl
  have inj : Function.Injective P := by
    apply (LinearMap.ker_eq_bot).mp
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hn
    have hz : β.comp (LinearMap.mulLeft F x) = 0 := by
      apply b.ext
      intro i
      have hi := congrFun (LinearMap.mem_ker.mp hx) i
      simpa [hP, mul_comm x (b i)] using hi
    apply hβ
    ext y
    have hy := DFunLike.congr_fun hz (x⁻¹ * y)
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hy
  have dim : finrank F E = finrank F (Fin (finrank F E) → F) := by simp
  let e := LinearEquiv.ofBijective P
    ⟨inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank dim).mp inj⟩
  let Q : K →ₗ[F] (Fin (finrank F E) → F) :=
    LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (algebraMap E K (b i)))
  let l : K →ₗ[F] E := e.symm.toLinearMap.comp Q
  have key (x : K) (a : E) : β (a * l x) = bit (a • x) := by
    let f : E →ₗ[F] F := β.comp (LinearMap.mulLeft F (l x))
    let g : E →ₗ[F] F := bit.comp ((LinearMap.toSpanSingleton E K x).restrictScalars F)
    have hfg : f = g := by
      apply b.ext
      intro i
      have hi := congrFun (e.apply_symm_apply (Q x)) i
      change P (l x) i = Q x i at hi
      change β (l x * b i) = bit (b i • x)
      rw [mul_comm (l x), ← hP, hi]
      rw [Algebra.smul_def]
      rfl
    have h := DFunLike.congr_fun hfg a
    change β (l x * a) = bit (a • x) at h
    simpa only [mul_comm (l x)] using h
  let L : K →ₗ[E] E :=
    { toFun := l
      map_add' := l.map_add
      map_smul' := by
        intro a x
        apply inj
        funext i
        rw [hP, hP, key, smul_smul, ← key]
        simp [mul_assoc] }
  have fac (x : K) : β (L x) = bit x := by
    change β (l x) = bit x
    simpa using key x 1
  refine ⟨L, ?_, fac⟩
  intro h
  apply hb
  ext x
  simpa [h] using (fac x).symm

end BitFactor

section Correction

variable {E K : Type*} [Field E] [Field K] [Algebra E K] {g : ℕ}

private theorem nonzeroInteraction (L : K →ₗ[E] E) (hL : L ≠ 0)
    (d : Fin g → K)
    (hd : Submodule.span E (Set.range fun ij : Fin g × Fin g => d ij.1 * d ij.2) = ⊤)
    (z : K) (hz : z ≠ 0) :
    ∃ i j, L (d i * (z⁻¹ * d j)) ≠ 0 := by
  by_contra! h
  let l := L.comp (LinearMap.mulLeft E z⁻¹)
  have top_le : ⊤ ≤ l.ker := by
    rw [← hd, Submodule.span_le]
    rintro _ ⟨⟨i,j⟩,rfl⟩
    change L (z⁻¹ * (d i * d j)) = 0
    rw [show z⁻¹ * (d i * d j) = d i * (z⁻¹ * d j) by ring]
    exact h i j
  apply hL
  ext x
  have hx := top_le (show z * x ∈ (⊤ : Submodule E K) from trivial)
  change L (z⁻¹ * (z * x)) = 0 at hx
  simpa [← mul_assoc, inv_mul_cancel₀ hz] using hx

private noncomputable def correction (L : K →ₗ[E] E) (d : Fin g → K)
    (S : Finset (Fin g)) (a : Fin g → E) : K →ₗ[E] K :=
  ∑ i ∈ S, (a i • (L.comp (LinearMap.mulLeft E (d i)))).smulRight (d i)

private theorem correction_apply (L : K →ₗ[E] E) (d : Fin g → K)
    (S : Finset (Fin g)) (a : Fin g → E) (x : K) :
    correction L d S a x = ∑ i ∈ S, (a i * L (d i * x)) • d i := by
  simp [correction, smul_eq_mul]

private theorem singularCorrection (L : K →ₗ[E] E) (d : Fin g → K)
    (z : K) (hz : z ≠ 0) (inter : ∃ i j, L (d i * (z⁻¹ * d j)) ≠ 0) :
    ∃ (S : Finset (Fin g)) (a : Fin g → E), S.card ≤ 2 ∧
      ∃ x : K, x ≠ 0 ∧ (LinearMap.mulLeft E z + correction L d S a) x = 0 := by
  classical
  have zz : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  by_cases diag : ∃ i, L (d i * (z⁻¹ * d i)) ≠ 0
  · obtain ⟨i, hi⟩ := diag
    let x := z⁻¹ * d i
    let c := L (d i * x)
    have hc : c ≠ 0 := hi
    have hx : x ≠ 0 := by
      intro h
      exact hc (by simp [c, h])
    have hc' : -c⁻¹ * c = -1 := by rw [neg_mul, inv_mul_cancel₀ hc]
    refine ⟨{i}, fun _ => -c⁻¹, by simp, x, hx, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, correction_apply, Finset.sum_singleton]
    change z * (z⁻¹ * d i) + (-c⁻¹ * c) • d i = 0
    rw [hc', neg_smul, one_smul, ← mul_assoc, zz, one_mul, add_neg_cancel]
  · obtain ⟨i, j, hij⟩ := inter
    have diag0 (l : Fin g) : L (d l * (z⁻¹ * d l)) = 0 := by
      by_contra hl
      exact diag ⟨l, hl⟩
    have hne : i ≠ j := fun h => hij (h ▸ diag0 j)
    have hnmem : i ∉ ({j} : Finset (Fin g)) := by simpa using hne
    let x := z⁻¹ * (d i + d j)
    let c := L (d i * (z⁻¹ * d j))
    have hc : c ≠ 0 := hij
    have hc' : -c⁻¹ * c = -1 := by rw [neg_mul, inv_mul_cancel₀ hc]
    have hi : L (d i * x) = c := by
      rw [show d i * x = d i * (z⁻¹ * d i) + d i * (z⁻¹ * d j) by dsimp [x]; ring,
        map_add, diag0, zero_add]
    have hj : L (d j * x) = c := by
      rw [show d j * x = d i * (z⁻¹ * d j) + d j * (z⁻¹ * d j) by dsimp [x]; ring,
        map_add, diag0, add_zero]
    have hx : x ≠ 0 := by
      intro h
      exact hc (by simpa [h] using hi.symm)
    refine ⟨{i,j}, fun _ => -c⁻¹, by simp [hne], x, hx, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, correction_apply,
      Finset.sum_insert hnmem, Finset.sum_singleton, hi, hj, hc', neg_smul, one_smul]
    change z * (z⁻¹ * (d i + d j)) + (-d i + -d j) = 0
    rw [← mul_assoc, zz, one_mul, ← neg_add_rev, add_comm (d j) (d i), add_neg_cancel]

end Correction

section MatrixRank

variable {F E K : Type*} [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
variable [FiniteDimensional F E] [FiniteDimensional E K]

/-- Sampling a pairing of the form `bit (x * U y)` cannot increase the
dimension of the range of `U`, regardless of the sampling family. -/
private theorem rank_le_range {n : ℕ} (p : Fin n → K) (bit : K →ₗ[F] F)
    (U : K →ₗ[E] K) :
    (Matrix.of fun i j => bit (p i * U (p j))).rank ≤ finrank F U.range := by
  let B : Matrix (Fin n) (Fin n) F := Matrix.of fun i j => bit (p i * U (p j))
  let I : (Fin n → F) →ₗ[F] U.range :=
    Fintype.linearCombination F (fun j => U.rangeRestrict (p j))
  let O : U.range →ₗ[F] (Fin n → F) :=
    (LinearMap.pi fun i => bit.comp (LinearMap.mulLeft F (p i))).comp
      (U.range.subtype.restrictScalars F)
  have eqn : B.mulVecLin = O.comp I := by
    apply (Pi.basisFun F _).ext
    intro j
    rw [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
      LinearMap.comp_apply, Fintype.linearCombination_apply_single, one_smul]
    rfl
  let _ : FiniteDimensional F U.range := FiniteDimensional.trans F E U.range
  change finrank F B.mulVecLin.range ≤ _
  rw [eqn]
  exact (Submodule.finrank_mono (LinearMap.range_comp_le_range I O)).trans O.finrank_range_le

/-- At most two directions suffice to reduce the binary rank by one full
`E`-dimension, using a single `E`-valued coefficient per selected group. -/
private theorem residual {n h m g : ℕ} (hE : finrank F E = h) (hK : finrank E K = m)
    (p : Fin n → K) (β : E →ₗ[F] F) (L : K →ₗ[E] E) (hL : L ≠ 0)
    (d : Fin g → K)
    (hd : Submodule.span E (Set.range fun ij : Fin g × Fin g => d ij.1 * d ij.2) = ⊤)
    (z : K) (hz : z ≠ 0) :
    ∃ (S : Finset (Fin g)) (a : Fin g → E), S.card ≤ 2 ∧
      (Matrix.of fun i j => β (L (z * p i * p j) +
        ∑ l ∈ S, a l * L (d l * p i) * L (d l * p j))).rank ≤ h*m-h := by
  obtain ⟨S, a, hS, x, hx, hxU⟩ :=
    singularCorrection L d z hz (nonzeroInteraction L hL d hd z hz)
  let U := LinearMap.mulLeft E z + correction L d S a
  refine ⟨S, a, hS, ?_⟩
  have entry (x y : K) : L (x * U y) =
      L (z*x*y) + ∑ l ∈ S, a l * L (d l * x) * L (d l * y) := by
    simp only [U, LinearMap.add_apply, LinearMap.mulLeft_apply, correction_apply,
      mul_add, map_add, Finset.mul_sum, map_sum]
    rw [show x * (z * y) = z * x * y by ring]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm x (d l)]
    ring
  simp_rw [← entry]
  refine (rank_le_range p (β.comp (L.restrictScalars F)) U).trans ?_
  have hker : 0 < finrank E U.ker := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨x, LinearMap.mem_ker.mpr hxU⟩, ?_⟩
    exact fun he => hx (congrArg Subtype.val he)
  have hr := U.finrank_range_add_finrank_ker
  have hlt : finrank E U.range ≤ m - 1 := by omega
  rw [← Module.finrank_mul_finrank F E U.range, hE, ← Nat.mul_sub_one]
  exact Nat.mul_le_mul_left h hlt

end MatrixRank

end RankDrop

namespace FiveMasks

private abbrev F := ZMod 2
private abbrev D := GaloisField 2 4

private theorem two_zero : (2 : D) = 0 := CharP.cast_eq_zero D 2

private theorem add_self_zero (x : D) : x + x = 0 := by rw [← two_mul, two_zero, zero_mul]

private theorem root (p : ℕ) [Fact p.Prime] (hp : p ∣ 15) :
    ∃ r : D, r ^ p = 1 ∧ ∀ n : ℕ, r ^ n = 1 → p ∣ n := by
  have hc : Nat.card Dˣ = 15 := by
    rw [Nat.card_units, GaloisField.card 2 4 (by decide)]
    decide
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Dˣ) p (hc.symm ▸ hp)
  refine ⟨u, ?_, ?_⟩
  · have hpow : u ^ p = 1 := hu ▸ pow_orderOf_eq_one u
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using congrArg Units.val hpow
  · intro n hn
    have hn' : u ^ n = 1 := Units.ext (by simpa using hn)
    exact hu ▸ orderOf_dvd_of_pow_eq_one hn'

private theorem pow16 (x : D) : x ^ 16 = x := by
  let : Fintype D := Fintype.ofFinite D
  have hd : Fintype.card D = 16 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 4 (by decide)
  simpa only [hd] using FiniteField.pow_card x

private noncomputable def trace (x : D) : D := x + x^2 + x^4 + x^8

private theorem trace_square (x : D) : trace x ^ 2 = trace x := by
  simp only [trace, add_pow_char _ _ 2, ← pow_mul]
  change x^2 + x^4 + x^8 + x^16 = x + x^2 + x^4 + x^8
  rw [pow16]
  ring

private theorem trace_add (x y : D) : trace (x + y) = trace x + trace y := by
  have h2 := add_pow_char x y 2
  have h4 := add_pow_char_pow x y 2 2
  have h8 := add_pow_char_pow x y 2 3
  change (x+y)^4 = x^4+y^4 at h4
  change (x+y)^8 = x^8+y^8 at h8
  simp only [trace, h2, h4, h8]
  ring

private theorem trace_exists (x : D) : ∃ b : F, algebraMap F D b = trace x := by
  have hh : trace x * (trace x - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, trace_square, sub_self]
  rcases mul_eq_zero.mp hh with h | h
  · exact ⟨0, by simpa using h.symm⟩
  · exact ⟨1, by simpa using (sub_eq_zero.mp h).symm⟩

private noncomputable def bit : D →ₗ[F] F where
  toFun x := (trace_exists x).choose
  map_add' x y := (algebraMap F D).injective (by
    rw [map_add, (trace_exists (x+y)).choose_spec, (trace_exists x).choose_spec,
      (trace_exists y).choose_spec, trace_add])
  map_smul' a x := by
    fin_cases a
    · change (trace_exists (0 • x)).choose = 0 • (trace_exists x).choose
      simp only [zero_smul]
      exact (algebraMap F D).injective (by simp [trace])
    · change (trace_exists (1 • x)).choose = 1 • (trace_exists x).choose
      simp

private theorem bit_coe (x : D) : algebraMap F D (bit x) = trace x :=
  (trace_exists x).choose_spec

private noncomputable def probe (c : D) : D →ₗ[F] F where
  toFun x := bit (c*x)
  map_add' x y := by simp [mul_add]
  map_smul' a x := by
    rw [Algebra.smul_def, mul_left_comm c, ← Algebra.smul_def, map_smul]
    rfl

private theorem trace_deg2 (c x : D) (hc : c^4 = c) :
    trace (c*x) = c*(x+x^4) + (c*(x+x^4))^2 := by
  have hc8 : c^8 = c^2 := by rw [show (8:ℕ) = 4*2 by decide, pow_mul, hc]
  simp only [trace, mul_pow, hc, hc8, add_pow_char _ _ 2, ← pow_mul]
  ring

private theorem factor (s x y : D) (hs : s^2+s+1 = 0) (hs4 : s^4=s) :
    trace (s*x)*trace y + trace x*trace (s^2*y) = trace (x*y^4) + trace (x*y) := by
  have hs42 : (s^2)^4 = s^2 := by rw [← pow_mul, show (2:ℕ)*4 = 4*2 by decide, pow_mul, hs4]
  have hu := trace_deg2 s x hs4
  have hv := trace_deg2 1 y (by simp)
  have hw := trace_deg2 1 x (by simp)
  have hz := trace_deg2 (s^2) y hs42
  rw [show trace y = trace (1*y) by simp, show trace x = trace (1*x) by simp, hu, hv, hw, hz]
  rw [← trace_add, ← mul_add]
  have hy : (y^4+y)^4 = y^4+y := by
    rw [show (y^4+y)^4 = (y^4)^4+y^4 from add_pow_char_pow _ _ 2 2, ← pow_mul]
    rw [show (4:ℕ)*4 = 16 by decide, pow16, add_comm]
  rw [mul_comm x, trace_deg2 _ _ hy]
  simp only [one_mul, mul_pow, ← pow_mul]
  rw [show s^(2*2) = s by exact hs4]
  have hss : s^2+s = 1 := by
    linear_combination hs - two_zero
  rw [show y^4+y = y+y^4 by ac_rfl]
  generalize x+x^4 = u
  generalize y+y^4 = v
  linear_combination (u*v+u^2*v^2)*hss + (s*u*v^2+s^2*u^2*v)*two_zero

private theorem sum_pow (r : D) (hr : r^5 = 1) (hord : ∀ n : ℕ, r^n = 1 → 5 ∣ n)
    (e : ℕ) (he : ¬ 5 ∣ e) : ∑ i : Fin 5, (r^e)^i.val = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  have h5 : (r^e)^5 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hr, one_pow]
  have hh := geom_sum_mul (r^e) 5
  rw [h5, sub_self] at hh
  exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr fun h => he (hord e h))

private theorem reconstruction (r x y : D) (hr : r^5 = 1)
    (hord : ∀ n : ℕ, r^n = 1 → 5 ∣ n) :
    ∑ i : Fin 5, (trace ((r^i.val*x)*(r^i.val*y)^4) + trace ((r^i.val*x)*(r^i.val*y))) * (r^3)^i.val = x*y := by
  have pointwise (i : Fin 5) :
      (trace ((r^i.val*x)*(r^i.val*y)^4) + trace ((r^i.val*x)*(r^i.val*y))) * (r^3)^i.val =
        trace (x*y^4) * (r^3)^i.val + x*y + (x*y)^2*(r^7)^i.val +
          (x*y)^4*(r^11)^i.val + (x*y)^8*(r^19)^i.val := by
    have hxy : (r^i.val*x)*(r^i.val*y)^4 = x*y^4 := by
      calc
        _ = ((r^i.val)^5)*(x*y^4) := by rw [mul_pow]; ring
        _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul, hr, one_pow, one_mul]
    have hxy' : (r^i.val*x)*(r^i.val*y) = (r^2)^i.val*(x*y) := by rw [← pow_mul, Nat.mul_comm, pow_mul]; ring
    rw [hxy, hxy']
    conv_lhs =>
      arg 1
      arg 2
      unfold trace
    have hp (d : ℕ) : ((r^2)^i.val)^d * (r^3)^i.val = (r^(2*d+3))^i.val := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring
    have h3 : (r^2)^i.val * (r^3)^i.val = 1 := by rw [← mul_pow, ← pow_add, hr, one_pow]
    simp only [mul_pow, add_mul]
    calc
      _ = trace (x*y^4) * (r^3)^i.val + (x*y)*((r^2)^i.val * (r^3)^i.val) +
          (x*y)^2*(((r^2)^i.val)^2*(r^3)^i.val) +
          (x*y)^4*(((r^2)^i.val)^4*(r^3)^i.val) +
          (x*y)^8*(((r^2)^i.val)^8*(r^3)^i.val) := by ring
      _ = _ := by rw [h3, mul_one, hp, hp, hp]; simp only [mul_pow]
  simp_rw [pointwise, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_pow r hr hord 3 (by decide), sum_pow r hr hord 7 (by decide),
    sum_pow r hr hord 11 (by decide), sum_pow r hr hord 19 (by decide)]
  simp only [mul_zero, zero_add, add_zero, Fin.sum_univ_succ, Finset.sum_fin_eq_sum_range]
  simp [add_self_zero]

/-- Five mixed rank-two masks realize the quartic field product. -/
private theorem five_masks :
    ∃ a b c d : Fin 5 → D →ₗ[F] F, ∃ w : Fin 5 → D,
      ∀ x y : D, x*y = ∑ i : Fin 5, (a i x*c i y + b i x*d i y) • w i := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨r, hr, hord⟩ := root 5 (by decide)
  obtain ⟨s, hs, hsord⟩ := root 3 (by decide)
  have hs1 : s ≠ 1 := by
    intro h
    have := hsord 1 (by simp [h])
    norm_num at this
  have hs4 : s^4 = s := by
    change s^(3+1) = s
    rw [pow_succ, hs, one_mul]
  have hss : s^2+s+1 = 0 := by
    have h : (s^2+s+1)*(s-1) = 0 := by
      calc
        _ = s^3-1 := by ring
        _ = 0 := by rw [hs, sub_self]
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hs1)
  refine ⟨fun i => probe (s*r^i.val), fun i => probe (r^i.val), fun i => probe (r^i.val),
    fun i => probe (s^2*r^i.val), fun i => (r^3)^i.val, fun x y => ?_⟩
  rw [← reconstruction r x y hr hord]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (bit ((s*r^i.val)*x)*bit (r^i.val*y) + bit (r^i.val*x)*bit ((s^2*r^i.val)*y)) • _
  simp only [Algebra.smul_def, map_add (algebraMap F D), map_mul (algebraMap F D), bit_coe]
  rw [mul_assoc s, mul_assoc (s^2), factor s _ _ hss hs4]

end FiveMasks

open scoped BigOperators

namespace Directions29944

private theorem base_digits_injective {q : ℕ} (hq : 0 < q) (n : ℕ)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < q) (hb : ∀ i, b i < q)
    (h : (∑ i, q ^ i.val * a i) = ∑ i, q ^ i.val * b i) : a = b := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_mul, Fin.val_succ,
      pow_succ', mul_assoc, ← Finset.mul_sum] at h
    have h₀ : a 0 = b 0 := by
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ha 0), Nat.mod_eq_of_lt (hb 0)]
        using congrArg (fun x => x % q) h
    have hh : (∑ i : Fin n, q ^ i.val * a i.succ) = ∑ i : Fin n, q ^ i.val * b i.succ := by
      rw [h₀] at h
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_left_cancel h)
    have ht := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => ha i.succ) (fun i => hb i.succ) hh
    funext i
    exact Fin.cases h₀ (fun j => congrFun ht j) i

private theorem twice_geom_lt {q : ℕ} (hq : 2 < q) (n : ℕ) :
    2 * (∑ i : Fin n, q ^ i.val) < q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.sum_univ_succ, Fin.val_zero, pow_zero, Fin.val_succ, pow_succ',
      ← Finset.mul_sum]
    calc
      2 * (1 + q * ∑ i : Fin n, q ^ i.val) = 2 + q * (2 * ∑ i : Fin n, q ^ i.val) := by ring
      _ < q + q * (2 * ∑ i : Fin n, q ^ i.val) := Nat.add_lt_add_right hq _
      _ = q * (2 * (∑ i : Fin n, q ^ i.val) + 1) := by ring
      _ ≤ q * q ^ n := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt ih)

private def pairExponent {g : ℕ} (s : Sym2 (Fin g)) : Fin g →₀ ℕ :=
  ((Sym2.equivMultiset _ s).val).toFinsupp

private theorem pairExponent_injective (g : ℕ) :
    Function.Injective (pairExponent (g := g)) := by
  intro a b hab
  exact (Sym2.equivMultiset _).injective
    (Subtype.ext (Multiset.toFinsupp.injective hab))

private theorem pairExponent_le {g : ℕ} (s : Sym2 (Fin g)) (i : Fin g) :
    pairExponent s i ≤ 2 := by
  simpa only [pairExponent, Multiset.toFinsupp_apply, (Sym2.equivMultiset _ s).property] using
    Multiset.count_le_card i (Sym2.equivMultiset _ s).val

private theorem pairExponent_sum {g : ℕ} (s : Sym2 (Fin g)) :
    (pairExponent s).sum (fun _ => id) = 2 := by
  rw [pairExponent, Multiset.toFinsupp_sum_eq]
  exact (Sym2.equivMultiset _ s).property

private theorem pairExponent_pair {g : ℕ} (i j : Fin g) :
    pairExponent s(i, j) = Finsupp.single i 1 + Finsupp.single j 1 := by
  change (({i} : Multiset (Fin g)) + {j}).toFinsupp = _
  rw [Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, Multiset.toFinsupp_singleton]

private theorem eval_ne_zero_of_totalDegree_lt {K : Type*} [Field K] [Fintype K]
    {g : ℕ} {P : MvPolynomial (Fin g) K} (hP : P ≠ 0)
    (hdeg : P.totalDegree < Fintype.card K) : ∃ d : Fin g → K, MvPolynomial.eval d P ≠ 0 := by
  classical
  by_contra! H
  have h := MvPolynomial.schwartz_zippel_totalDegree hP (Finset.univ : Finset K)
  have hK : (Fintype.card K : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h' : (1 : ℚ≥0) ≤ P.totalDegree / (Fintype.card K : ℚ≥0) := by
    simpa [Fintype.piFinset_univ, H, Fintype.card_fun, hK] using h
  have h'' : (Fintype.card K : ℚ≥0) ≤ (P.totalDegree : ℚ≥0) := by
    simpa only [one_mul] using (le_div_iff₀ (pos_of_ne_zero hK)).1 h'
  have hle : Fintype.card K ≤ P.totalDegree := by exact_mod_cast h''
  omega

private theorem exists_pair_products_span_of_card
    (E K : Type*) [Field E] [Fintype E] [Field K] [Fintype K]
    [Algebra E K] [FiniteDimensional E K] (hq : 2 < Fintype.card E)
    (m g : ℕ) (hm : m ≤ g * (g + 1) / 2) (hrank : Module.finrank E K = m) :
    ∃ d : Fin g → K,
      Submodule.span E (Set.range fun ij : Fin g × Fin g => d ij.1 * d ij.2) = ⊤ := by
  classical
  let q := Fintype.card E
  have hqK : Fintype.card K = q ^ m := by
    rw [Module.card_eq_pow_finrank (K := E), hrank]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m) (β := Sym2 (Fin g)) (by
    simpa [Sym2.card, Nat.choose_two_right, Nat.mul_comm] using hm)
  let w (j : Fin m) := pairExponent (e j)
  let exponent (σ : Equiv.Perm (Fin m)) := ∑ j, (q ^ (σ j).val) • w j
  -- The row assigned to each pair records its multiplicities in one base-`q` digit.
  have hexp : Function.Injective exponent := by
    intro σ τ h
    have hd (x : Fin g) : (fun i : Fin m => w (σ.symm i) x) = fun i => w (τ.symm i) x := by
      apply base_digits_injective (q := q) (by omega) m
      · exact fun _ => (pairExponent_le _ _).trans_lt hq
      · exact fun _ => (pairExponent_le _ _).trans_lt hq
      · have hx : exponent σ x = exponent τ x := congrArg (fun a : Fin g →₀ ℕ => a x) h
        simp only [exponent, Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul] at hx
        change (∑ j : Fin m, q ^ (σ j).val * w j x) =
          ∑ j : Fin m, q ^ (τ j).val * w j x at hx
        rw [← Equiv.sum_comp σ.symm (fun j => q ^ (σ j).val * w j x),
          ← Equiv.sum_comp τ.symm (fun j => q ^ (τ j).val * w j x)] at hx
        simpa only [Equiv.apply_symm_apply] using hx
    have hsymm : σ.symm = τ.symm := by
      apply Equiv.ext
      intro i
      exact e.injective ((pairExponent_injective g) (Finsupp.ext fun x => congrFun (hd x) i))
    simpa using congrArg Equiv.symm hsymm
  let P : MvPolynomial (Fin g) K :=
    ∑ σ : Equiv.Perm (Fin m), MvPolynomial.monomial (exponent σ) ((σ.sign : ℤ) : K)
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun f : MvPolynomial (Fin g) K => f.coeff (exponent 1)) h
    simp [P, hexp.eq_iff] at hc
  -- The total degree, not just the degree in each variable, is below `|K|`.
  have hdeg : P.totalDegree ≤ 2 * (∑ i : Fin m, q ^ i.val) := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro σ _
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simp only [id_eq, exponent, Finset.sum_apply', Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    change (∑ x : Fin g, ∑ j : Fin m, q ^ (σ j).val * w j x) ≤ _
    rw [Finset.sum_comm]
    have hs (j : Fin m) : (∑ x : Fin g, w j x) = 2 := by
      exact (Finsupp.sum_fintype (w j) (fun _ => id) (fun _ => rfl)).symm.trans
        (pairExponent_sum _)
    simp_rw [← Finset.mul_sum, hs, mul_comm _ 2, ← Finset.mul_sum]
    exact (congrArg (2 * ·) (Equiv.sum_comp σ (fun i => q ^ i.val))).le
  obtain ⟨d, hd⟩ := eval_ne_zero_of_totalDegree_lt hP
    ((hdeg.trans_lt (twice_geom_lt hq m)).trans_eq hqK.symm)
  let v (j : Fin m) := MvPolynomial.eval d (MvPolynomial.monomial (w j) (1 : K))
  let M : Matrix (Fin m) (Fin m) K := Matrix.of fun i j => v j ^ q ^ i.val
  have hdet : M.det ≠ 0 := by
    apply hd.imp
    intro h
    suffices heval : MvPolynomial.eval d P = M.det by rwa [heval]
    rw [Matrix.det_apply']
    simp only [P, map_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [MvPolynomial.monomial_sum_index, map_mul, MvPolynomial.eval_C, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    simp only [Matrix.of_apply, M, ← map_pow, v, MvPolynomial.monomial_pow, one_pow]
  have hvals (s : Sym2 (Fin g)) : MvPolynomial.eval d
      (MvPolynomial.monomial (pairExponent s) (1 : K)) ∈
        Set.range fun ij : Fin g × Fin g => d ij.1 * d ij.2 := by
    refine (Sym2.forall (f := fun s => MvPolynomial.eval d
      (MvPolynomial.monomial (pairExponent s) (1 : K)) ∈
        Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2))).mpr ?_ s
    intro i j
    use (i, j)
    have hmon : MvPolynomial.monomial (pairExponent s(i, j)) (1 : K) =
        MvPolynomial.X i * MvPolynomial.X j := by
      simp only [pairExponent_pair, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul]
    simp [hmon]
  have hLI : LinearIndependent E v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    let a : Fin m → K := fun i => algebraMap E K (c i)
    have hz : M.mulVec a = M.mulVec 0 := by
      rw [Matrix.mulVec_zero]
      funext i
      let f : K →ₐ[E] K := FiniteField.frobeniusAlgHom E K ^ i.val
      have hf := congrArg f hc
      rw [map_sum, map_zero] at hf
      have hf_apply (x : K) : f x = x ^ q ^ i.val := by
        simp only [f, AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, q]
      simp_rw [Algebra.smul_def, map_mul, AlgHom.commutes, hf_apply] at hf
      simpa only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, a, mul_comm, Pi.zero_apply] using hf
    have ha := congrFun (Matrix.mulVec_injective_of_det_ne_zero hdet hz) j
    exact (algebraMap E K).injective (by simpa [a] using ha)
  refine ⟨d, top_unique ?_⟩
  rw [← hLI.span_eq_top_of_card_eq_finrank' (by simpa using hrank.symm)]
  exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact hvals (e j))

/-- The products of a suitable `g` elements of the extension span it over the base field. -/
private theorem exists_pair_products_span (t m g : ℕ) (ht : 0 < t)
    (hm : m ≤ g * (g + 1) / 2) (K : Type*) [Field K] [Fintype K]
    [Algebra (GaloisField 2 (4 * t)) K] [FiniteDimensional (GaloisField 2 (4 * t)) K]
    (hrank : Module.finrank (GaloisField 2 (4 * t)) K = m) :
    ∃ d : Fin g → K,
      Submodule.span (GaloisField 2 (4 * t))
        (Set.range fun ij : Fin g × Fin g => d ij.1 * d ij.2) = ⊤ := by
  let E := GaloisField 2 (4 * t)
  let _ : Fintype E := Fintype.ofFinite E
  have hq : 2 < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (4 * t) (by omega)]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 4) (Nat.pow_le_pow_right (by decide) (by omega))
  exact exists_pair_products_span_of_card E K hq m g hm hrank

end Directions29944


open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

private def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

private theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

private theorem b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private theorem zmod2_two : (2 : ZMod 2) = 0 := rfl

private theorem zmod2_ite_eq (x : ZMod 2) : (if x = 1 then (1 : ZMod 2) else 0) = x := by
  by_cases h : x = 1
  · simp [h]
  · simp only [h, ite_false]
    fin_cases x
    · rfl
    · exact absurd rfl h

private def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

private def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private theorem depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

private theorem wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

private theorem depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

private theorem foldl_append_prefix {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

private theorem wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

private theorem depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_prefix
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

private theorem wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

private theorem depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

private theorem wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

private theorem depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

private theorem oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

private theorem oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

private theorem oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

private theorem anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

private theorem anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → ZMod 2) :
    Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => h i j + h i v + h u j + h u v

private theorem anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [zmod2_add_self]

private theorem anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → ZMod 2) (s : Fin m → ZMod 2) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, zmod2_add_self]

private theorem anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]
  ring

private theorem anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : ZMod 2) (h : Fin n → Fin m → ZMod 2) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

private theorem anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
    (r1 r2 : Fin n → ZMod 2) (s1 s2 : Fin m → ZMod 2) :
    anchor u v (fun i j => (r1 i + s1 j) * (r2 i + s2 j)) =
      Matrix.vecMulVec (fun i => r1 i + r1 u) (fun j => s2 j + s2 v) +
      Matrix.vecMulVec (fun i => r2 i + r2 u) (fun j => s1 j + s1 v) := by
  ext i j
  simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h : ((r1 i + s1 j) * (r2 i + s2 j) + (r1 i + s1 v) * (r2 i + s2 v) +
      (r1 u + s1 j) * (r2 u + s2 j) + (r1 u + s1 v) * (r2 u + s2 v)) +
      ((r1 i + r1 u) * (s2 j + s2 v) + (r2 i + r2 u) * (s1 j + s1 v)) =
      (2 : ZMod 2) * (r1 i * r2 i + r1 u * r2 u + s1 j * s2 j + s1 v * s2 v +
        r1 i * s2 j + r1 i * s2 v + r1 u * s2 j + r1 u * s2 v +
        r2 i * s1 j + r2 i * s1 v + r2 u * s1 j + r2 u * s1 v) := by ring
  rw [zmod2_two, zero_mul] at h
  have hsub : ∀ a b : ZMod 2, a + b = 0 → a = b := by
    intro a b hab
    calc a = a + 0 := (add_zero a).symm
      _ = a + (b + b) := by rw [zmod2_add_self]
      _ = (a + b) + b := by ring
      _ = 0 + b := by rw [hab]
      _ = b := zero_add b
  exact hsub _ _ h


private theorem factor_of_rank_le {n m K : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod 2)) (h : A.rank ≤ K) :
    ∃ (rowVec : Fin K → Fin n → ZMod 2) (colVec : Fin K → Fin m → ZMod 2),
      ∀ i j, A i j = ∑ k : Fin K, rowVec k i * colVec k j := by
  let r := A.rank
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.range A.mulVecLin)
    (rfl : Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) = r)
  have hcol : ∀ j : Fin m, (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec_single]
  let rowVec : Fin K → Fin n → ZMod 2 := fun k i =>
    if hk : k.val < r then (b ⟨k.val, hk⟩).val i else 0
  let colVec : Fin K → Fin m → ZMod 2 := fun k j =>
    if hk : k.val < r then b.repr ⟨fun i => A i j, hcol j⟩ ⟨k.val, hk⟩ else 0
  refine ⟨rowVec, colVec, fun i j => ?_⟩
  have hrepr : ∑ t : Fin r, (b.repr ⟨fun i => A i j, hcol j⟩ t) • (b t) =
      ⟨fun i => A i j, hcol j⟩ := b.sum_repr ⟨fun i => A i j, hcol j⟩
  have heval : A i j = ∑ t : Fin r, (b t).val i * b.repr ⟨fun i => A i j, hcol j⟩ t := by
    have h1 := congrArg (fun (v : LinearMap.range A.mulVecLin) => v.val i) hrepr
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul_of_tower,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun t _ => mul_comm _ _
  rw [heval]
  symm
  have hfilt : ∑ k : Fin K, rowVec k i * colVec k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin K => k.val < r), rowVec k i * colVec k j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hnk
    rw [Finset.mem_filter] at hnk
    have hge : ¬ k.val < r := fun hk => hnk ⟨Finset.mem_univ k, hk⟩
    simp [rowVec, colVec, hge]
  rw [hfilt]
  refine Finset.sum_bij (fun k hk => ⟨k.val, (Finset.mem_filter.mp hk).2⟩) ?_ ?_ ?_ ?_
  · intro _ _
    exact Finset.mem_univ _
  · intro k1 _ k2 _ heq
    exact Fin.ext (Fin.mk.inj heq)
  · intro t _
    refine ⟨⟨t.val, Nat.lt_of_lt_of_le t.isLt h⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩, Fin.ext rfl⟩
  · intro k hk
    have hlt : k.val < r := (Finset.mem_filter.mp hk).2
    simp only [rowVec, colVec, hlt, dite_true]
    rfl


private def Valid (n m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) ⟨gs, 0⟩

private theorem valid_nil (n m : ℕ) : Valid n m [] := by
  exact ⟨by simp, by simp [ReadsBack]⟩

private theorem valid_snoc {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hbound : ∀ a ∈ g.inputs, a < n + m + gs.length) :
    Valid n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hv.1 g' h
    · rw [List.mem_singleton.mp h]
      exact hlen
  · intro j hj a ha
    change j < (gs ++ [g]).length at hj
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at ha
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at ha
      exact hv.2 j hj' a ha
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at ha
      simp only [Nat.sub_self, List.getD_cons_zero] at ha
      exact hbound a ha

private theorem nlGate_or_nil : nlGate ⟨GateOp.or, []⟩ = false := rfl

private theorem nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := rfl

private theorem nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := rfl

private theorem nlGate_and (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := rfl

private def pushFalse (gs : List Gate) : List Gate := gs ++ [⟨GateOp.or, []⟩]

private def pushXor (n m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [n + m + gs.length]⟩]

private def pushAnd (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [a, b]⟩]

private theorem pushFalse_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) :
    let gs' := pushFalse gs
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 = 0 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) = 0) := by
  refine ⟨valid_snoc hv _ (by simp) (by simp), by simp [pushFalse], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushFalse, List.countP_append, nlGate_or_nil]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushFalse
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, nlGate_or_nil]
  · intro i j
    unfold pushFalse
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, GateOp.eval, b2z]

private theorem pushXor_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushXor n m gs a b
    let w := n + m + gs.length + 1
    Valid n m gs' ∧ gs'.length = gs.length + 2 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) +
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  let g2 : Gate := ⟨GateOp.not, [n + m + gs.length]⟩
  have hsplit : pushXor n m gs a b = (gs ++ [g1]) ++ [g2] := by
    simp [pushXor, g1, g2]
  have hv1 : Valid n m (gs ++ [g1]) := valid_snoc hv g1 (by simp [g1]) (by
    intro x hx; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hv2 : Valid n m ((gs ++ [g1]) ++ [g2]) := valid_snoc hv1 g2 (by simp [g2]) (by
    intro x hx; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp)
  refine ⟨hsplit ▸ hv2, by simp [pushXor], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushXor, List.countP_append, nlGate_mod2, nlGate_not]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · rw [hsplit, depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (depthsOf (n + m) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [depthsOf_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_not, Bool.toNat_false, add_zero, Nat.max_zero]
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_mod2, Bool.toNat_false, add_zero, Nat.max_zero]
  · intro i j
    rw [hsplit, wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (wiresOf (oneEach i j) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [wiresOf_length, oneEach_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil]
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

private theorem pushAnd_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushAnd gs a b
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate + 1 ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) + 1 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) *
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  refine ⟨valid_snoc hv _ (by simp) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption), by simp [pushAnd], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushAnd, List.countP_append, nlGate_and]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushAnd
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_and, Bool.toNat_true, Nat.max_zero]
  · intro i j
    unfold pushAnd
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

private theorem build_xor_list {n m : ℕ} (D : ℕ) (ws : List ℕ) (gs : List Gate) (hv : Valid n m gs)
    (hb : ∀ w ∈ ws, w < n + m + gs.length)
    (hd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ D ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum) := by
  induction ws generalizing gs with
  | nil =>
    obtain ⟨hv', hlen', hcnt', hdp', hwp', hdout, hwout⟩ := pushFalse_spec hv
    exact ⟨pushFalse gs, n + m + gs.length, hv', by omega, by omega, hcnt', hdp', hwp',
      by omega, fun i j => by simpa using hwout i j⟩
  | cons w ws ih =>
    have hw_lt : w < n + m + gs.length := hb w List.mem_cons_self
    have hw_d : (depthsOf (n + m) gs).getD w 0 ≤ D := hd w List.mem_cons_self
    obtain ⟨gs1, out1, hv1, hle1, hout1, hcnt1, hdp1, hwp1, hd1, hw1⟩ :=
      ih gs hv (fun a ha => hb a (List.mem_cons_of_mem w ha))
        (fun a ha => hd a (List.mem_cons_of_mem w ha))
    obtain ⟨hv2, hlen2, hcnt2, hdp2, hwp2, hd2, hw2⟩ :=
      pushXor_spec hv1 (by omega : w < n + m + gs1.length) hout1
    refine ⟨pushXor n m gs1 w out1, n + m + gs1.length + 1, hv2, by omega, by omega,
      by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hdp2 k (by omega), hdp1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · rw [hd2, hdp1 w hw_lt]
      exact max_le hw_d hd1
    · intro i j
      rw [hw2 i j, hwp1 i j w hw_lt, hw1 i j]
      simp

private theorem build_row_fn {n m : ℕ} (f : Fin n → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = f i) := by
  let ws : List ℕ := ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map Fin.val
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin n, if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map
          (fun k : Fin n => if k = i then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega), oneEach_getD_left i j k.isLt]
      by_cases hki : k = i
      · subst hki; simp [b2z]
      · have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
        simp [b2z, hki, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin n)),
        ((l.filter (fun k => decide (f k = 1))).map (fun k => if k = i then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if f k = 1 then (if k = i then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hfa : f a = 1 <;> simp [hfa, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    exact zmod2_ite_eq (f i)
  · intro k _ hki
    simp [hki]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem build_col_fn {n m : ℕ} (g : Fin m → ZMod 2) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = g j) := by
  let ws : List ℕ :=
    ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map (fun k => n + k.val)
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin m, if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map
          (fun k : Fin m => if k = j then (1 : ZMod 2) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega),
        oneEach_getD_right i j (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left]
      by_cases hkj : k = j
      · subst hkj; simp [b2z]
      · have hne : k.val ≠ j.val := fun e => hkj (Fin.ext e)
        simp [b2z, hkj, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin m)),
        ((l.filter (fun k => decide (g k = 1))).map (fun k => if k = j then (1 : ZMod 2) else 0)).sum =
        (l.map (fun k => if g k = 1 then (if k = j then (1 : ZMod 2) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hga : g a = 1 <;> simp [hga, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    exact zmod2_ite_eq (g j)
  · intro k _ hkj
    simp [hkj]
  · intro h
    exact absurd (Finset.mem_univ j) h

private theorem build_pair_and {n m : ℕ} (a b : Fin n → ZMod 2) (c d : Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate + 1 ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ 1 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (a i + d j) * (b i + c j)) := by
  obtain ⟨gs1, wa, hv1, hl1, hwa, hc1, hd1, hw1, hda, hfa⟩ := build_row_fn a gs hv
  obtain ⟨gs2, wd, hv2, hl2, hwd, hc2, hd2, hw2, hdd, hfd⟩ := build_col_fn d gs1 hv1
  obtain ⟨hv3, hl3, hc3, hd3, hw3, hdL, hwL⟩ :=
    pushXor_spec hv2 (by omega : wa < n + m + gs2.length) hwd
  set gs3 := pushXor n m gs2 wa wd
  let wL := n + m + gs2.length + 1
  obtain ⟨gs4, wb, hv4, hl4, hwb, hc4, hd4, hw4, hdb, hfb⟩ := build_row_fn b gs3 hv3
  obtain ⟨gs5, wc, hv5, hl5, hwc, hc5, hd5, hw5, hdc, hfc⟩ := build_col_fn c gs4 hv4
  obtain ⟨hv6, hl6, hc6, hd6, hw6, hdR, hwR⟩ :=
    pushXor_spec hv5 (by omega : wb < n + m + gs5.length) hwc
  set gs6 := pushXor n m gs5 wb wc
  let wR := n + m + gs5.length + 1
  obtain ⟨hv7, hl7, hc7, hd7, hw7, hdP, hwP⟩ :=
    pushAnd_spec hv6 (by omega : wL < n + m + gs6.length) (by omega : wR < n + m + gs6.length)
  set gs7 := pushAnd gs6 wL wR
  let out := n + m + gs6.length
  refine ⟨gs7, out, hv7, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hd7 k (by omega), hd6 k (by omega), hd5 k (by omega), hd4 k (by omega),
      hd3 k (by omega), hd2 k (by omega), hd1 k hk]
  · intro i j k hk
    rw [hw7 i j k (by omega), hw6 i j k (by omega), hw5 i j k (by omega), hw4 i j k (by omega),
      hw3 i j k (by omega), hw2 i j k (by omega), hw1 i j k hk]
  · rw [hdP]
    have hL0 : (depthsOf (n + m) gs6).getD wL 0 = 0 := by
      rw [hd6 wL (by omega), hd5 wL (by omega), hd4 wL (by omega), hdL, hd2 wa hwa, hda, hdd]
      simp
    have hR0 : (depthsOf (n + m) gs6).getD wR 0 = 0 := by
      rw [hdR, hd5 wb hwb, hdb, hdc]
      simp
    rw [hL0, hR0]
    simp
  · intro i j
    rw [hwP i j]
    have hLv : b2z ((wiresOf (oneEach i j) gs6).getD wL false) = a i + d j := by
      rw [hw6 i j wL (by omega), hw5 i j wL (by omega), hw4 i j wL (by omega),
        hwL i j, hw2 i j wa hwa, hfa i j, hfd i j]
    have hRv : b2z ((wiresOf (oneEach i j) gs6).getD wR false) = b i + c j := by
      rw [hwR i j, hw5 i j wb hwb, hfb i j, hfc i j]
    rw [hLv, hRv]

private theorem build_many_pairs {n m : ℕ} (t : ℕ)
    (a b : Fin t → Fin n → ZMod 2) (c d : Fin t → Fin m → ZMod 2)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧
      (∀ w ∈ ws, w < n + m + gs'.length) ∧
      (∀ w ∈ ws, (depthsOf (n + m) gs').getD w 0 ≤ 1) ∧
      gs'.countP nlGate = gs.countP nlGate + t ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (∀ (i : Fin n) (j : Fin m), (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs').getD w false))).sum =
        ∑ p : Fin t, (a p i + d p j) * (b p i + c p j)) := by
  induction t generalizing gs with
  | zero =>
    exact ⟨gs, [], hv, le_rfl, by simp, by simp, by simp, fun _ _ => rfl, fun _ _ _ _ => rfl,
      fun _ _ => by simp⟩
  | succ t ih =>
    obtain ⟨gs1, w0, hv1, hl1, hw0, hc1, hd1, hwp1, hdw0, hfv0⟩ :=
      build_pair_and (a 0) (b 0) (c 0) (d 0) gs hv
    obtain ⟨gs2, ws, hv2, hl2, hws, hdws, hc2, hd2, hwp2, hsum⟩ :=
      ih (fun p => a p.succ) (fun p => b p.succ) (fun p => c p.succ) (fun p => d p.succ) gs1 hv1
    refine ⟨gs2, w0 :: ws, hv2, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      · exact hws w hw
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [hd2 w hw0]; exact hdw0
      · exact hdws w hw
    · intro k hk
      rw [hd2 k (by omega), hd1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · intro i j
      rw [List.map_cons, List.sum_cons, hwp2 i j w0 hw0, hfv0 i j, hsum i j, Fin.sum_univ_succ]

private theorem dir_ge {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) (t : ℕ)
    (hr : (anchor u v (fun i j => b2z (G i j))).rank ≤ 2 * t) :
    ∃ C : Circuit,
      ((∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) C ∧ Represents G C) ∧
      (depthsOf (n + m) C.gates).getD C.output 0 ≤ 1 ∧
      C.gates.countP nlGate ≤ t := by
  obtain ⟨rowVec, colVec, hfac⟩ := factor_of_rank_le (anchor u v (fun i j => b2z (G i j))) hr
  let a : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val, by omega⟩
  let b : Fin t → Fin n → ZMod 2 := fun p => rowVec ⟨2 * p.val + 1, by omega⟩
  let c : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val, by omega⟩
  let d : Fin t → Fin m → ZMod 2 := fun p => colVec ⟨2 * p.val + 1, by omega⟩
  let R : Fin n → ZMod 2 := fun i => b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i
  let S : Fin m → ZMod 2 := fun j => b2z (G u j) + ∑ p : Fin t, c p j * d p j
  have hdecomp : ∀ i j, b2z (G i j) = R i + S j + ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) := by
    intro i j
    have hA := hfac i j
    have hpair : ∑ k : Fin (2 * t), rowVec k i * colVec k j =
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      let e : Fin t × Fin 2 ≃ Fin (2 * t) := {
        toFun := fun x => ⟨2 * x.1.val + x.2.val, by omega⟩
        invFun := fun k => (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)
        left_inv := fun ⟨p, q⟩ => by
          ext
          · simp; omega
          · simp; omega
        right_inv := fun k => by
          ext
          simp
          omega
      }
      rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.sum_univ_two]
      rfl
    rw [hpair] at hA
    simp only [anchor] at hA
    have hterm : ∑ p : Fin t, (a p i + d p j) * (b p i + c p j) =
        ∑ p : Fin t, (a p i * b p i + c p j * d p j) +
        ∑ p : Fin t, (a p i * c p j + b p i * d p j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [hterm, ← hA]
    simp only [R, S, Finset.sum_add_distrib]
    have h2 : (b2z (G i v) + b2z (G u v) + ∑ p : Fin t, a p i * b p i) +
        (b2z (G u j) + ∑ p : Fin t, c p j * d p j) +
        ((∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) +
        (b2z (G i j) + b2z (G i v) + b2z (G u j) + b2z (G u v))) =
        b2z (G i j) + (2 : ZMod 2) * (b2z (G i v) + b2z (G u j) + b2z (G u v) +
          ∑ p : Fin t, a p i * b p i + ∑ p : Fin t, c p j * d p j) := by ring
    rw [h2, zmod2_two, zero_mul, add_zero]
  obtain ⟨gs1, wR, hv1, hl1, hwR, hc1, _, _, hdR, hfR⟩ := build_row_fn R [] (valid_nil n m)
  obtain ⟨gs2, wS, hv2, hl2, hwS, hc2, hd2, hw2, hdS, hfS⟩ := build_col_fn S gs1 hv1
  obtain ⟨gs3, ws, hv3, hl3, hws, hdws, hc3, hd3, hw3, hsum3⟩ :=
    build_many_pairs t a b c d gs2 hv2
  obtain ⟨gs4, out, hv4, hl4, hout, hc4, hd4, hw4, hdout, hwout⟩ :=
    build_xor_list 1 (wR :: wS :: ws) gs3 hv3
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · omega
          · exact hws w hw)
      (by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rw [hd3 w (by omega), hd2 w hwR, hdR]; omega
        · rcases List.mem_cons.mp hw with rfl | hw
          · rw [hd3 w hwS, hdS]; omega
          · exact hdws w hw)
  refine ⟨⟨gs4, out⟩, ⟨hv4.1, hv4.2, ?_⟩, hdout, ?_⟩
  · intro i j
    apply b2z_inj
    change b2z ((wiresOf (oneEach i j) gs4).getD out false) = b2z (G i j)
    rw [hwout i j]
    simp only [List.map_cons, List.sum_cons]
    rw [hw3 i j wR (by omega), hw2 i j wR hwR, hfR i j,
      hw3 i j wS hwS, hfS i j, hsum3 i j, hdecomp i j]
    ring
  · change gs4.countP nlGate ≤ t
    simp only [List.countP_nil] at hc1
    omega


private lemma zmod_of_bool_pred (a : ZMod 2) : b2z (decide (a ≠ 0)) = a := by
  fin_cases a
  · change b2z (decide ((0 : ZMod 2) ≠ 0)) = 0
    decide
  · change b2z (decide ((1 : ZMod 2) ≠ 0)) = 1
    decide


private def Fits {n m q : ℕ} (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) : Prop :=
  ∃ (C : Circuit) (tap : Fin q → ℕ), ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
    ∀ j : Fin q, (depthsOf (n+m) C.gates).getD (tap j) 0 ≤ 1 ∧
      Represents (G j) ⟨C.gates,tap j⟩


section Final
open Module

private lemma parity_sum {ι : Type} [DecidableEq ι] (S : Finset ι) (f : ι → Bool) :
    b2z (((S.filter (fun i => f i)).card % 2) == 1) = ∑ i ∈ S, b2z (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [b2z]
  | @insert i S hi ih =>
    by_cases h : f i = true
    · have h' : i ∉ S.filter (fun i => f i = true) := fun hh => hi (Finset.mem_filter.mp hh).1
      simp only [Finset.filter_insert, h, ite_true,Finset.card_insert_of_notMem h', Finset.sum_insert hi]
      rw [←ih]
      let k := (S.filter (fun i => f i = true)).card
      change b2z (((k+1)%2)==1) = 1+b2z ((k%2)==1)
      by_cases e : k%2=0
      · have e' : (k+1)%2=1 := by omega
        rw [e,e']; decide
      · have e' : (k+1)%2=0 := by omega
        have e1 : k%2=1 := by omega
        rw [e1,e']; decide
    · have h' : f i = false := Bool.eq_false_iff.mpr h
      simpa [Finset.filter_insert,h',hi,b2z] using ih

end Final

private theorem mixedBank {n m : ℕ} (q : ℕ)
    (a b : Fin q → Fin n → ZMod 2) (c d : Fin q → Fin m → ZMod 2) :
    ∃ (gs : List Gate) (tap : Fin q → ℕ), Valid n m gs ∧ gs.countP nlGate ≤ q ∧
      ∀ j, tap j < n+m+gs.length ∧ (depthsOf (n+m) gs).getD (tap j) 0 ≤ 1 ∧
        ∀ x y, b2z ((wiresOf (oneEach x y) gs).getD (tap j) false) =
          (a j x + d j y) * (b j x + c j y) := by
  induction q with
  | zero => exact ⟨[],Fin.elim0,valid_nil _ _,by simp,fun j => Fin.elim0 j⟩
  | succ q ih =>
    obtain ⟨gs,tap,v,cnt,works⟩ := ih (fun i => a i.succ) (fun i => b i.succ)
      (fun i => c i.succ) (fun i => d i.succ)
    obtain ⟨gs',w,v',len,wo,num,dep,wire,dw,ww⟩ := build_pair_and (a 0) (b 0) (c 0) (d 0) gs v
    refine ⟨gs', Fin.cases w tap, v', by omega, ?_⟩
    intro j
    refine Fin.cases ⟨wo,dw,ww⟩ (fun j => ?_) j
    obtain ⟨hlt,hd,hw⟩ := works j
    refine ⟨?_,(dep _ hlt).trans_le hd,fun x y => ?_⟩
    · change tap j < n+m+gs'.length
      omega
    · change b2z ((wiresOf (oneEach x y) gs').getD (tap j) false) = _
      rw [wire x y _ hlt,hw x y]

private theorem appendOutputs {n m q : ℕ} (R : Fin q → Fin n → ZMod 2)
    (S : Fin q → Fin m → ZMod 2) (ls : Fin q → List ℕ) (gs : List Gate) (hv : Valid n m gs)
    (hb : ∀ j w, w ∈ ls j → w < n+m+gs.length)
    (hd : ∀ j w, w ∈ ls j → (depthsOf (n+m) gs).getD w 0 ≤ 1) :
    ∃ (gs' : List Gate) (tap : Fin q → ℕ), Valid n m gs' ∧ gs.length ≤ gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n+m+gs.length, (depthsOf (n+m) gs').getD k 0 = (depthsOf (n+m) gs).getD k 0) ∧
      (∀ (x : Fin n) (y : Fin m) k, k < n+m+gs.length →
        (wiresOf (oneEach x y) gs').getD k false = (wiresOf (oneEach x y) gs).getD k false) ∧
      ∀ j, tap j < n+m+gs'.length ∧ (depthsOf (n+m) gs').getD (tap j) 0 ≤ 1 ∧
        ∀ x y, b2z ((wiresOf (oneEach x y) gs').getD (tap j) false) = R j x + S j y +
          ((ls j).map (fun w => b2z ((wiresOf (oneEach x y) gs).getD w false))).sum := by
  induction q generalizing gs with
  | zero => exact ⟨gs,Fin.elim0,hv,le_rfl,rfl,fun _ _ => rfl,fun _ _ _ _ => rfl,fun j => Fin.elim0 j⟩
  | succ q ih =>
    obtain ⟨gs1,wR,v1,l1,bR,c1,d1,e1,hdR,wRval⟩ := build_row_fn (R 0) gs hv
    obtain ⟨gs2,wS,v2,l2,bS,c2,d2,e2,hdS,wSval⟩ := build_col_fn (S 0) gs1 v1
    have hb2 (w) (hw : w ∈ wR :: wS :: ls 0) : w < n+m+gs2.length := by
      rcases List.mem_cons.mp hw with rfl | hw
      · omega
      rcases List.mem_cons.mp hw with rfl | hw
      · exact bS
      · have := hb 0 w hw; omega
    have hd2 (w) (hw : w ∈ wR :: wS :: ls 0) : (depthsOf (n+m) gs2).getD w 0 ≤ 1 := by
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [d2 _ bR,hdR]; omega
      rcases List.mem_cons.mp hw with rfl | hw
      · rw [hdS]; omega
      · have hb0 := hb 0 w hw
        rw [d2 _ (by omega),d1 _ hb0]; exact hd 0 w hw
    obtain ⟨gs3,w,v3,l3,bw,c3,d3,e3,hdw,wval⟩ :=
      build_xor_list 1 (wR :: wS :: ls 0) gs2 v2 hb2 hd2
    have b03 (u) (hu : u < n+m+gs.length) : u < n+m+gs3.length := by omega
    have d03 (u) (hu : u < n+m+gs.length) :
        (depthsOf (n+m) gs3).getD u 0 = (depthsOf (n+m) gs).getD u 0 := by
      rw [d3 _ (by omega),d2 _ (by omega),d1 _ hu]
    have e03 (x : Fin n) (y : Fin m) (u) (hu : u < n+m+gs.length) :
        (wiresOf (oneEach x y) gs3).getD u false = (wiresOf (oneEach x y) gs).getD u false := by
      rw [e3 x y _ (by omega),e2 x y _ (by omega),e1 x y _ hu]
    obtain ⟨gs4,tap,v4,l4,c4,d4,e4,out⟩ := ih (fun j => R j.succ) (fun j => S j.succ)
      (fun j => ls j.succ) gs3 v3 (fun j u hu => b03 u (hb j.succ u hu))
      (fun j u hu => (d03 u (hb j.succ u hu)).trans_le (hd j.succ u hu))
    refine ⟨gs4, Fin.cases w tap, v4, by omega, by omega, ?_, ?_, fun j => ?_⟩
    · intro u hu; rw [d4 _ (b03 _ hu),d03 _ hu]
    · intro x y u hu; rw [e4 x y _ (b03 _ hu),e03 x y _ hu]
    refine Fin.cases ?_ (fun j => ?_) j
    · change w < n+m+gs4.length ∧ (depthsOf (n+m) gs4).getD w 0 ≤ 1 ∧ _
      refine ⟨by omega,(d4 _ bw).trans_le hdw,fun x y => ?_⟩
      change b2z ((wiresOf (oneEach x y) gs4).getD w false) = R 0 x + S 0 y + _
      rw [e4 x y _ bw,wval x y]
      simp only [List.map_cons,List.sum_cons]
      rw [e2 x y wR bR,wRval x y,wSval x y,add_assoc]
      congr 2
      apply congrArg List.sum
      apply List.map_congr_left
      intro u hu
      have hb0 := hb 0 u hu
      rw [e2 x y _ (by omega),e1 x y _ hb0]
    · obtain ⟨bt,dt,vt⟩ := out j
      refine ⟨bt,dt,fun x y => ?_⟩
      change b2z ((wiresOf (oneEach x y) gs4).getD (tap j) false) = R j.succ x + S j.succ y + _
      rw [vt x y]
      congr 2
      apply List.map_congr_left
      intro u hu
      rw [e03 x y _ (hb j.succ u hu)]

private theorem mixedFits {n m q t : ℕ} (G : Fin q → Fin n → Fin m → ZMod 2)
    (a b : Fin t → Fin n → ZMod 2) (c d : Fin t → Fin m → ZMod 2)
    (weights : Fin q → Fin t → ZMod 2)
    (h : ∀ j x y, G j x y = ∑ i, weights j i * (a i x * c i y + b i x * d i y)) :
    Fits (fun j x y => decide (G j x y ≠ 0)) t := by
  classical
  obtain ⟨gs,tap,hv,hcnt,htap⟩ := mixedBank t a b c d
  let R := fun j x => ∑ i, weights j i * (a i x * b i x)
  let S := fun j y => ∑ i, weights j i * (c i y * d i y)
  let active := fun j => Finset.univ.filter (fun i => weights j i ≠ 0)
  let ls := fun j => (active j).toList.map tap
  have member j w (hw : w ∈ ls j) : ∃ i, tap i = w := by
    obtain ⟨i,_,e⟩ := List.mem_map.mp hw
    exact ⟨i,e⟩
  obtain ⟨gs',out,v',_,cnt,_,_,works⟩ := appendOutputs R S ls gs hv
    (fun j w hw => by obtain ⟨i,rfl⟩ := member j w hw; exact (htap i).1)
    (fun j w hw => by obtain ⟨i,rfl⟩ := member j w hw; exact (htap i).2.1)
  refine ⟨⟨gs',0⟩,out,v'.2,v'.1,cnt.trans_le hcnt,fun j => ⟨(works j).2.1,fun x y => ?_⟩⟩
  apply b2z_inj
  change b2z ((wiresOf (oneEach x y) gs').getD (out j) false) = _
  rw [(works j).2.2 x y,zmod_of_bool_pred]
  have weighting : ((ls j).map (fun w => b2z ((wiresOf (oneEach x y) gs).getD w false))).sum =
      ∑ i, weights j i * ((a i x + d i y) * (b i x + c i y)) := by
    simp only [ls,List.map_map,Function.comp_def]
    rw [Finset.toList,Multiset.sum_map_toList]
    change (∑ i ∈ Finset.univ.filter (fun i => weights j i ≠ 0), _) = _
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    rw [(htap i).2.2 x y]
    generalize weights j i = k
    rcases (show k = 0 ∨ k = 1 by fin_cases k <;> first | exact Or.inl rfl | exact Or.inr rfl) with rfl | rfl <;> simp
  rw [weighting,h j x y]
  simp only [R,S,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have cancel (z : ZMod 2) : z + z = 0 := zmod2_add_self z
  have eqn : weights j i * (a i x * b i x) + weights j i * (c i y * d i y) +
      weights j i * ((a i x + d i y) * (b i x + c i y)) =
      (weights j i * (a i x * b i x) + weights j i * (a i x * b i x)) +
      (weights j i * (c i y * d i y) + weights j i * (c i y * d i y)) +
      weights j i * (a i x * c i y + b i x * d i y) := by ring
  rw [eqn,cancel,cancel,zero_add,zero_add]

open scoped BigOperators
open Polynomial

private theorem interpolateProduct {D E : Type*} [Field D] [Field E] [Algebra D E]
    (P : PowerBasis D E) (hp : 0 < P.dim) (v : Fin (2 * P.dim - 1) ↪ D) :
    ∃ (f : Fin (2 * P.dim - 1) → E → D) (w : Fin (2 * P.dim - 1) → E),
      ∀ x y, x * y = ∑ i, (f i x * f i y) • w i := by
  let poly (x : E) : D[X] := ∑ j : Fin P.dim, C (P.basis.repr x j) * X ^ j.val
  have ep (x : E) : aeval P.gen (poly x) = x := by
    simp only [poly, map_sum, map_mul, aeval_C, map_pow, aeval_X]
    simpa only [Algebra.smul_def, P.basis_eq_pow] using P.basis.sum_repr x
  have bd (x : E) : (poly x).natDegree ≤ P.dim - 1 := by
    apply natDegree_sum_le_of_forall_le
    intro j _
    exact (natDegree_C_mul_X_pow_le _ _).trans (by have := j.isLt; omega)
  have ip : Set.InjOn v (↑(Finset.univ : Finset (Fin (2 * P.dim - 1))) : Set _) :=
    v.injective.injOn
  refine ⟨fun i x => (poly x).eval (v i),
    fun i => aeval P.gen (Lagrange.basis Finset.univ v i), fun x y => ?_⟩
  have bxy : (poly x * poly y).degree < ((Finset.univ : Finset (Fin (2 * P.dim - 1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    have hn : (poly x * poly y).natDegree < 2 * P.dim - 1 := by
      have := (natDegree_mul_le (p := poly x) (q := poly y)).trans (Nat.add_le_add (bd x) (bd y))
      omega
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (WithBot.coe_lt_coe.mpr hn)
  have hi := Lagrange.eq_interpolate ip bxy
  have he := congrArg (aeval P.gen) hi
  simpa [Lagrange.interpolate_apply, Algebra.smul_def, ep] using he

private abbrev Small := GaloisField 2 4

private theorem interpolationFamily (t : ℕ) (ht : 0 < t) (ht8 : t ≤ 8) :
    ∃ (f : Fin (2*t-1) → GaloisField 2 (4*t) → Small)
      (reconstruct : Fin (2*t-1) → Small →ₗ[ZMod 2] GaloisField 2 (4*t)),
      ∀ x y, x * y = ∑ i, reconstruct i (f i x * f i y) := by
  let E := GaloisField 2 (4*t)
  have h4t : 4*t ≠ 0 := by omega
  have hd : Module.finrank (ZMod 2) Small ∣ Module.finrank (ZMod 2) E := by
    rw [GaloisField.finrank (p := 2) (by decide : 4 ≠ 0), GaloisField.finrank (p := 2) h4t]
    exact dvd_mul_right _ _
  obtain ⟨emb⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hd
  algebraize [emb.toRingHom]
  let P := Field.powerBasisOfFiniteOfSeparable Small E
  have dim : P.dim = t := by
    have hm := Module.finrank_mul_finrank (ZMod 2) Small E
    rw [GaloisField.finrank (p := 2) (by decide : 4 ≠ 0), GaloisField.finrank (p := 2) h4t,
      PowerBasis.finrank P] at hm
    omega
  let := Fintype.ofFinite Small
  have card : Fintype.card Small = 16 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 4 (by decide)]
    rfl
  have hv : Fintype.card (Fin (2*P.dim-1)) ≤ Fintype.card Small := by
    rw [Fintype.card_fin, card, dim]; omega
  let v := Classical.choice (Function.Embedding.nonempty_of_card_le hv)
  obtain ⟨f,w,hw⟩ := interpolateProduct P (by omega) v
  let e : Fin (2*t-1) ≃ Fin (2*P.dim-1) := finCongr (by omega)
  refine ⟨fun i => f (e i),
    fun i => ((LinearMap.id : Small →ₗ[Small] Small).smulRight (w (e i))).restrictScalars (ZMod 2),
    fun x y => ?_⟩
  change x * y = ∑ i, (f (e i) x * f (e i) y) • w (e i)
  rw [Equiv.sum_comp e (fun i => (f i x * f i y) • w i)]
  exact hw x y



private theorem productCircuits {E D : Type*} [Field E] [Field D] [Algebra (ZMod 2) E]
    [Algebra (ZMod 2) D] {g h n p : ℕ} (e : Fin h → E) (eps : E →ₗ[ZMod 2] ZMod 2)
    (r : Fin g → Fin n → E) (f : Fin p → E → D)
    (recon : Fin p → D →ₗ[ZMod 2] E)
    (interp : ∀ x y, x * y = ∑ i, recon i (f i x * f i y))
    (a b c d : Fin 5 → D → ZMod 2) (w : Fin 5 → D)
    (masks : ∀ x y, x*y = ∑ j, (a j x * c j y + b j x * d j y) • w j)
    (label : Fin (g*h) ≃ Fin g × Fin h) :
    Fits (fun i x y => decide (eps (e (label i).2 * (r (label i).1 x * r (label i).1 y)) ≠ 0))
      (g*(5*p)) := by
  classical
  let prodEquiv : Fin (g*(5*p)) ≃ Fin g × Fin p × Fin 5 :=
    (finProdFinEquiv (m := g) (n := 5*p)).symm.trans
      (Equiv.prodCongr (Equiv.refl _) ((finProdFinEquiv (m := 5) (n := p)).symm.trans (Equiv.prodComm _ _)))
  let present (i : Fin (g*h)) := eps.comp (LinearMap.mulLeft (ZMod 2) (e (label i).2))
  let A (j : Fin (g*(5*p))) (x : Fin n) := a (prodEquiv j).2.2 (f (prodEquiv j).2.1 (r (prodEquiv j).1 x))
  let B (j : Fin (g*(5*p))) (x : Fin n) := b (prodEquiv j).2.2 (f (prodEquiv j).2.1 (r (prodEquiv j).1 x))
  let C (j : Fin (g*(5*p))) (y : Fin n) := c (prodEquiv j).2.2 (f (prodEquiv j).2.1 (r (prodEquiv j).1 y))
  let D' (j : Fin (g*(5*p))) (y : Fin n) := d (prodEquiv j).2.2 (f (prodEquiv j).2.1 (r (prodEquiv j).1 y))
  let W (i : Fin (g*h)) (j : Fin g × Fin p × Fin 5) :=
    if j.1 = (label i).1 then present i (recon j.2.1 (w j.2.2)) else 0
  apply mixedFits _ A B C D' (fun i j => W i (prodEquiv j))
  intro i x y
  change present i (r (label i).1 x * r (label i).1 y) = _
  let P (j : Fin g × Fin p × Fin 5) := W i j *
    (a j.2.2 (f j.2.1 (r j.1 x)) * c j.2.2 (f j.2.1 (r j.1 y)) +
      b j.2.2 (f j.2.1 (r j.1 x)) * d j.2.2 (f j.2.1 (r j.1 y)))
  change present i (r (label i).1 x * r (label i).1 y) = ∑ j, P (prodEquiv j)
  rw [Equiv.sum_comp prodEquiv P,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (label i).1]
  · rw [Fintype.sum_prod_type,interp,map_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [masks,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [P,W,smul_eq_mul,mul_comm]
  · intro j _ hj
    simp [P,W,hj]
  · simp

private theorem selectCoordinates {E : Type*} [Field E] [Algebra (ZMod 2) E] {g h n : ℕ}
    (e : Module.Basis (Fin h) (ZMod 2) E) (eps : E →ₗ[ZMod 2] ZMod 2)
    (r : Fin g → Fin n → E) (label : Fin (g*h) ≃ Fin g × Fin h)
    (A : Finset (Fin g)) (a : Fin g → E) :
    ∃ S : Finset (Fin (g*h)), S.card ≤ A.card*h ∧
      (S.image (fun i => (label i).1)).card ≤ A.card ∧
      ∀ x y, (∑ i ∈ S, eps (e (label i).2 * (r (label i).1 x * r (label i).1 y))) =
        eps (∑ j ∈ A, a j * r j x * r j y) := by
  classical
  let live := (A ×ˢ (Finset.univ : Finset (Fin h))).filter (fun p => e.repr (a p.1) p.2 ≠ 0)
  refine ⟨live.map label.symm.toEmbedding, ?_, ?_, ?_⟩
  · rw [Finset.card_map]
    simpa [live] using (Finset.card_filter_le (A ×ˢ (Finset.univ : Finset (Fin h)))
      (fun p => e.repr (a p.1) p.2 ≠ 0))
  · apply Finset.card_le_card
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hi
    simpa using (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  · intro x y
    rw [Finset.sum_map,map_sum]
    simp only [Equiv.toEmbedding_apply,Equiv.apply_symm_apply]
    simp only [live,Finset.sum_filter,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro j _
    have hr := e.sum_repr (a j)
    have factor := congrArg (fun b : E => eps (b * r j x * r j y)) hr
    rw [Finset.sum_mul, Finset.sum_mul, map_sum] at factor
    rw [← factor]
    apply Finset.sum_congr rfl
    intro u _
    generalize e.repr (a j) u = v
    rcases (show v = 0 ∨ v = 1 by fin_cases v <;> first | exact Or.inl rfl | exact Or.inr rfl) with rfl | rfl <;> simp [mul_assoc]

private theorem fitsOfAnchorRank {n m t : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m)
    (hr : (anchor u v (fun x y => b2z (G x y))).rank ≤ 2*t) : Fits (fun _ : Fin 1 => G) t := by
  obtain ⟨C,⟨ar,rb,rep⟩,dep,cnt⟩ := dir_ge G u v t hr
  exact ⟨C, fun _ => C.output, rb, ar, cnt, fun _ => ⟨dep,rep⟩⟩

end PEqualNP.Outside.L_meta_29944_aux

open PEqualNP.Outside.L_meta_29944_aux

theorem PEqualNP.Outside.L_meta_29944 :
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
  let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    C.gates.foldl (fun (ds : List ℕ) g =>
      ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
      (List.replicate width 0)
  let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
  ∀ (t m g : ℕ), 0 < t → t ≤ 8 → 0 < m → m ≤ g*(g+1)/2 →
    let h := 4*t
    let F := ZMod 2
    let E := GaloisField 2 h
    let k := h*m
    let n := k+1
    ∀ (K : Type) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
        [FiniteDimensional E K] [Fintype K], Module.finrank E K = m →
      ∀ (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
        let point : Fin n → K := Fin.cases 0 basis
        let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
        ∃ (T : Fin (g*h) → Fin n → Fin n → Bool) (label : Fin (g*h) ≃ Fin g × Fin h),
          fits n n (g*h) T (g*(5*(2*t-1))) ∧
          ∀ z : K, z ≠ 0 → ∃ S : Finset (Fin (g*h)), S.card ≤ 2*h ∧
            (S.image (fun i => (label i).1)).card ≤ 2 ∧
            fits n n 1 (fun _ x y => xor (mult z x y)
              (((S.filter (fun i => T i x y)).card % 2) == 1)) ((k-h+1)/2) := by
  classical
  dsimp only
  intro t m g ht ht8 _hm hg K _ _ _ _ _ _ hK basis bit hbit
  let h := 4*t
  let E := GaloisField 2 h
  let k := h*m
  let p : Fin (k+1) → K := Fin.cases 0 basis
  have hp : p 0 = 0 := rfl
  have hE : Module.finrank (ZMod 2) E = h := GaloisField.finrank 2 (by dsimp [h]; omega)
  let e : Module.Basis (Fin h) (ZMod 2) E := (Module.finBasis _ _).reindex (finCongr hE)
  let zeroIndex : Fin h := ⟨0, by dsimp [h]; omega⟩
  let eps := e.coord zeroIndex
  have heps : eps ≠ 0 := by
    intro he
    have hh := DFunLike.congr_fun he (e zeroIndex)
    simp [eps,Module.Basis.coord_apply] at hh
  obtain ⟨L,hL,hfactor⟩ := RankDrop.factorBit eps heps bit hbit
  obtain ⟨d,hd⟩ := Directions29944.exists_pair_products_span t m g ht hg K hK
  obtain ⟨f,recon,interp⟩ := interpolationFamily t ht ht8
  obtain ⟨aa,bb,cc,dd,w,masks⟩ := FiveMasks.five_masks
  let label : Fin (g*h) ≃ Fin g × Fin h := finProdFinEquiv.symm
  let r : Fin g → Fin (k+1) → E := fun j x => L (d j * p x)
  let T (i : Fin (g*h)) (x y : Fin (k+1)) :=
    decide (eps (e (label i).2 * (r (label i).1 x * r (label i).1 y)) ≠ 0)
  refine ⟨T,label,?_,?_⟩
  · change Fits T (g*(5*(2*t-1)))
    exact productCircuits e eps r f recon interp (fun i => aa i) (fun i => bb i)
      (fun i => cc i) (fun i => dd i) w masks label
  · intro z hz
    obtain ⟨A,a,hA,hr⟩ := RankDrop.residual hE hK p eps L hL d hd z hz
    obtain ⟨S,hs,hgroup,hcoeff⟩ := selectCoordinates e eps r label A a
    refine ⟨S,hs.trans (Nat.mul_le_mul_right h hA),hgroup.trans hA,?_⟩
    let G (x y : Fin (k+1)) := xor (decide (bit (z * p x * p y) ≠ 0))
      (((S.filter (fun i => T i x y)).card % 2) == 1)
    change Fits (fun _ : Fin 1 => G) ((k-h+1)/2)
    have entry (x y : Fin (k+1)) : b2z (G x y) =
        eps (L (z * p x * p y) + ∑ j ∈ A, a j * L (d j * p x) * L (d j * p y)) := by
      dsimp only [G]
      rw [b2z_xor,zmod_of_bool_pred,parity_sum,map_add,hfactor]
      simp only [T,zmod_of_bool_pred]
      exact congrArg (bit (z * p x * p y) + ·) (hcoeff x y)
    have row (x : Fin (k+1)) : b2z (G x 0) = 0 := by
      rw [entry]
      simp [hp]
    have col (y : Fin (k+1)) : b2z (G 0 y) = 0 := by
      rw [entry]
      simp [hp]
    apply fitsOfAnchorRank G 0 0
    have heq : anchor 0 0 (fun x y => b2z (G x y)) =
        Matrix.of (fun x y : Fin (k+1) =>
          eps (L (z * p x * p y) + ∑ j ∈ A, a j * L (d j * p x) * L (d j * p y))) := by
      ext x y
      simp only [anchor,row,col,add_zero,Matrix.of_apply]
      exact entry x y
    rw [heq]
    exact hr.trans (by change k-h ≤ 2*((k-h+1)/2); omega)
