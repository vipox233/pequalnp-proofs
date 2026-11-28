import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_370_aux

private lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma gcd_two_pow_sub_one (m s : ℕ) :
    Nat.gcd (2 ^ m - 1) (2 ^ s - 1) = 2 ^ Nat.gcd m s - 1 := by
  induction m, s using Nat.gcd.induction with
  | H0 s => simp
  | H1 m s hm ih =>
    have hpow : 2 ^ s - 1 = (2 ^ (s % m) - 1) + 2 ^ (s % m) * (2 ^ (m * (s / m)) - 1) := by
      have hdiv : s = s % m + m * (s / m) := (Nat.mod_add_div s m).symm
      have h1 : 1 ≤ 2 ^ (s % m) := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ 2 ^ (m * (s / m)) := Nat.one_le_pow _ _ (by omega)
      have h3 : 2 ^ s = 2 ^ (s % m) * 2 ^ (m * (s / m)) := by rw [← pow_add, ← hdiv]
      rw [h3]
      have hprod : 1 ≤ 2 ^ (s % m) * 2 ^ (m * (s / m)) := by nlinarith
      zify [h1, h2, hprod]
      ring
    have hdvd : (2 ^ m - 1) ∣ (2 ^ (m * (s / m)) - 1) := by
      have h1 : (2 ^ m - 1 : ℕ) ∣ ((2 ^ m) ^ (s / m) - 1 ^ (s / m)) :=
        Nat.sub_dvd_pow_sub_pow (2 ^ m) 1 (s / m)
      simpa [pow_mul, one_pow] using h1
    have hgcd_step : Nat.gcd (2 ^ m - 1) (2 ^ s - 1) = Nat.gcd (2 ^ (s % m) - 1) (2 ^ m - 1) := by
      rw [hpow]
      have hmul : (2 ^ m - 1) ∣ 2 ^ (s % m) * (2 ^ (m * (s / m)) - 1) := dvd_mul_of_dvd_right hdvd _
      obtain ⟨c, hc⟩ := hmul
      rw [hc, mul_comm (2 ^ m - 1) c, Nat.gcd_add_mul_right_right, Nat.gcd_comm]
    rw [hgcd_step, ih, ← Nat.gcd_rec]

private lemma coprime_gold (m s : ℕ) (hm : 0 < m) (hodd : Odd (m / Nat.gcd m s)) :
    Nat.Coprime (2 ^ s + 1) (2 ^ m - 1) := by
  set g := Nat.gcd m s
  set d := Nat.gcd (2 ^ s + 1) (2 ^ m - 1)
  have hd1 : d ∣ 2 ^ s + 1 := Nat.gcd_dvd_left _ _
  have hd2 : d ∣ 2 ^ m - 1 := Nat.gcd_dvd_right _ _
  have hd_2s : d ∣ 2 ^ (2 * s) - 1 := by
    have hmul : 2 ^ (2 * s) - 1 = (2 ^ s - 1) * (2 ^ s + 1) := by
      have h1 : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ 2 ^ (2 * s) := Nat.one_le_pow _ _ (by omega)
      have h2s : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [← pow_add]; congr 1; omega
      rw [h2s]
      have hp : 1 ≤ 2 ^ s * 2 ^ s := by nlinarith
      zify [h1, hp]
      ring
    rw [hmul]
    exact dvd_mul_of_dvd_right hd1 _
  have hd_gcd : d ∣ 2 ^ Nat.gcd m (2 * s) - 1 := by
    rw [← gcd_two_pow_sub_one]
    exact Nat.dvd_gcd hd2 hd_2s
  have hgcd2 : Nat.gcd m (2 * s) = g := by
    have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left s hm
    have hm_eq : m = g * (m / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left m s)).symm
    have hs_eq : s = g * (s / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right m s)).symm
    have hcop_ms : Nat.Coprime (m / g) (s / g) := Nat.coprime_div_gcd_div_gcd hg_pos
    have hcop_m2 : Nat.Coprime (m / g) 2 := Nat.coprime_two_right.mpr hodd
    have hcop_all : Nat.Coprime (m / g) (2 * (s / g)) := hcop_m2.mul_right hcop_ms
    calc Nat.gcd m (2 * s)
        = Nat.gcd (g * (m / g)) (g * (2 * (s / g))) := by
            conv_lhs => rw [hm_eq, hs_eq]
            congr 1; ring
      _ = g * Nat.gcd (m / g) (2 * (s / g)) := Nat.gcd_mul_left g _ _
      _ = g * 1 := by rw [hcop_all.gcd_eq_one]
      _ = g := mul_one g
  rw [hgcd2] at hd_gcd
  have hd_s : d ∣ 2 ^ s - 1 := by
    have hs_eq : s = g * (s / g) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right m s)).symm
    have hdvd : (2 ^ g - 1) ∣ (2 ^ (g * (s / g)) - 1) := by
      have h1 := Nat.sub_dvd_pow_sub_pow (2 ^ g) 1 (s / g)
      simpa [pow_mul, one_pow] using h1
    rw [hs_eq]
    exact dvd_trans hd_gcd hdvd
  have hd_2 : d ∣ 2 := by
    have hsub : (2 ^ s + 1) - (2 ^ s - 1) = 2 := by
      have : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by omega)
      omega
    rw [← hsub]
    exact Nat.dvd_sub hd1 hd_s
  have hd_odd : Odd d := by
    have hodd2m : Odd (2 ^ m - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
      refine ⟨2 ^ k - 1, ?_⟩
      rw [pow_succ]
      omega
    exact Odd.of_dvd_nat hodd2m hd2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd_2 with h1 | h2
  · exact h1
  · rw [h2] at hd_odd
    exact absurd hd_odd (by decide)

private lemma gold_injective {F : Type} [Field F] [Fintype F]
    {m s : ℕ} (hm : 0 < m) (hcard : Fintype.card F = 2 ^ m)
    (hodd : Odd (m / Nat.gcd m s)) :
    Function.Injective (fun a : F => a ^ (2 ^ s + 1)) := by
  classical
  intro a b hab
  dsimp only at hab
  by_cases ha : a = 0
  · subst ha
    rw [zero_pow (by positivity)] at hab
    exact (eq_zero_of_pow_eq_zero hab.symm).symm
  · by_cases hb : b = 0
    · subst hb
      rw [zero_pow (by positivity)] at hab
      exact eq_zero_of_pow_eq_zero hab
    · have hcop := coprime_gold m s hm hodd
      have hcards : Fintype.card Fˣ = 2 ^ m - 1 := by
        rw [Fintype.card_units, hcard]
      set ua : Fˣ := Units.mk0 a ha
      set ub : Fˣ := Units.mk0 b hb
      have hpow_u : ua ^ (2 ^ s + 1) = ub ^ (2 ^ s + 1) := by
        ext; exact hab
      have h1 : ua ^ (2 ^ m - 1) = 1 := by
        rw [← hcards]; exact pow_card_eq_one
      have h2 : ub ^ (2 ^ m - 1) = 1 := by
        rw [← hcards]; exact pow_card_eq_one
      have heq_u : ua = ub := by
        have hbez := Nat.gcd_eq_gcd_ab (2 ^ s + 1) (2 ^ m - 1)
        rw [hcop.gcd_eq_one] at hbez
        have hbez' : (1 : ℤ) = (2 ^ s + 1 : ℕ) * Nat.gcdA (2 ^ s + 1) (2 ^ m - 1) +
            (2 ^ m - 1 : ℕ) * Nat.gcdB (2 ^ s + 1) (2 ^ m - 1) := hbez
        calc ua = ua ^ (1 : ℤ) := (zpow_one ua).symm
          _ = ua ^ (((2 ^ s + 1 : ℕ) : ℤ) * Nat.gcdA (2 ^ s + 1) (2 ^ m - 1) +
              ((2 ^ m - 1 : ℕ) : ℤ) * Nat.gcdB (2 ^ s + 1) (2 ^ m - 1)) := by rw [← hbez']
          _ = (ua ^ (2 ^ s + 1)) ^ (Nat.gcdA (2 ^ s + 1) (2 ^ m - 1)) *
              (ua ^ (2 ^ m - 1)) ^ (Nat.gcdB (2 ^ s + 1) (2 ^ m - 1)) := by
              rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
          _ = (ub ^ (2 ^ s + 1)) ^ (Nat.gcdA (2 ^ s + 1) (2 ^ m - 1)) *
              (ub ^ (2 ^ m - 1)) ^ (Nat.gcdB (2 ^ s + 1) (2 ^ m - 1)) := by rw [hpow_u, h1, h2]
          _ = ub ^ (((2 ^ s + 1 : ℕ) : ℤ) * Nat.gcdA (2 ^ s + 1) (2 ^ m - 1) +
              ((2 ^ m - 1 : ℕ) : ℤ) * Nat.gcdB (2 ^ s + 1) (2 ^ m - 1)) := by
              rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
          _ = ub ^ (1 : ℤ) := by rw [← hbez']
          _ = ub := zpow_one ub
      exact congrArg Units.val heq_u

private def chi (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

private lemma chi_add (x y : ZMod 2) : chi (x + y) = chi x * chi y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma chi_zero : chi 0 = 1 := rfl

private lemma chi_abs (x : ZMod 2) : |chi x| = 1 := by
  fin_cases x <;> decide

private lemma chi_le_one (x : ZMod 2) : chi x ≤ 1 := by
  fin_cases x <;> decide

private lemma sum_chi_linear_eq_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (l : V →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0) :
    ∑ x : V, chi (l x) = 0 := by
  have hex : ∃ v : V, l v = 1 := by
    by_contra h
    push Not at h
    apply hl
    ext v
    rcases zmod2_cases (l v) with h0 | h1
    · exact h0
    · exact absurd h1 (h v)
  obtain ⟨v, hv⟩ := hex
  have hshift : ∑ x : V, chi (l x) = ∑ x : V, chi (l (x + v)) :=
    (Equiv.sum_comp (Equiv.addRight v) (fun x => chi (l x))).symm
  have hneg : ∑ x : V, chi (l (x + v)) = - ∑ x : V, chi (l x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_add, hv, chi_add]
    change chi (l x) * (-1) = - chi (l x)
    ring
  omega

private lemma charP_two_of_algebra {F : Type} [Field F] [Algebra (ZMod 2) F] : CharP F 2 := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (algebraMap (ZMod 2) F) n,
      map_eq_zero_iff _ (RingHom.injective (algebraMap (ZMod 2) F)),
      ZMod.natCast_eq_zero_iff]

private lemma add_self_char2 {F : Type} [Field F] [Algebra (ZMod 2) F] (x : F) : x + x = 0 := by
  have : CharP F 2 := charP_two_of_algebra
  exact CharTwo.add_self_eq_zero x

private lemma add_pow_two_pow_char2 {F : Type} [Field F] [Algebra (ZMod 2) F] (s : ℕ) (a b : F) :
    (a + b) ^ (2 ^ s) = a ^ (2 ^ s) + b ^ (2 ^ s) := by
  have hsq : ∀ x y : F, (x + y) ^ 2 = x ^ 2 + y ^ 2 := fun x y => by
    have h2 : x * y + x * y = 0 := add_self_char2 (x * y)
    calc (x + y) ^ 2 = x ^ 2 + (x * y + x * y) + y ^ 2 := by ring
      _ = x ^ 2 + y ^ 2 := by rw [h2, add_zero]
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ, pow_mul, ih, hsq, ← pow_mul, ← pow_mul]

private lemma polar_gold {F : Type} [Field F] [Algebra (ZMod 2) F] (s : ℕ) (a h : F) :
    (a + h) ^ (2 ^ s + 1) + a ^ (2 ^ s + 1) = a ^ (2 ^ s) * h + h ^ (2 ^ s) * a + h ^ (2 ^ s + 1) := by
  rw [pow_succ, pow_succ, pow_succ, add_pow_two_pow_char2]
  have hcancel : a ^ (2 ^ s) * a + a ^ (2 ^ s) * a = 0 := add_self_char2 _
  calc (a ^ (2 ^ s) + h ^ (2 ^ s)) * (a + h) + a ^ (2 ^ s) * a
      = (a ^ (2 ^ s) * a + a ^ (2 ^ s) * a) + (a ^ (2 ^ s) * h + h ^ (2 ^ s) * a + h ^ (2 ^ s) * h) := by ring
    _ = a ^ (2 ^ s) * h + h ^ (2 ^ s) * a + h ^ (2 ^ s) * h := by rw [hcancel, zero_add]

private lemma card_frobenius_ker_le {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s : ℕ} (hm : 0 < m) (hcard : Fintype.card F = 2 ^ m) :
    Nat.card {y : F // y ^ (2 ^ s) + y = 0} ≤ 2 ^ Nat.gcd m s := by
  classical
  have : CharP F 2 := charP_two_of_algebra
  set g := Nat.gcd m s
  have hsub : (Finset.univ.filter fun y : F => y ^ (2 ^ s) + y = 0) ⊆
      (Polynomial.X ^ (2 ^ g) - Polynomial.X : Polynomial F).roots.toFinset := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    have hy_eq : y ^ (2 ^ s) = y := by
      have := congrArg (· + y) hy
      rw [add_assoc, add_self_char2, add_zero, zero_add] at this
      exact this
    have hy_g : y ^ (2 ^ g) = y := by
      by_cases hy0 : y = 0
      · subst hy0
        have hpos : 0 < 2 ^ g := by positivity
        exact zero_pow (by omega)
      · set uy : Fˣ := Units.mk0 y hy0
        have hu1 : uy ^ (2 ^ m - 1) = 1 := by
          have hc : Fintype.card Fˣ = 2 ^ m - 1 := by rw [Fintype.card_units, hcard]
          rw [← hc]; exact pow_card_eq_one
        have hu2 : uy ^ (2 ^ s - 1) = 1 := by
          have h1 : 1 ≤ 2 ^ s := Nat.one_le_pow _ _ (by omega)
          have hmul : uy ^ (2 ^ s - 1) * uy = 1 * uy := by
            rw [← pow_succ, Nat.sub_add_cancel h1, one_mul]
            ext; exact hy_eq
          exact mul_right_cancel hmul
        have hug : uy ^ (2 ^ g - 1) = 1 := by
          have hgcd := gcd_two_pow_sub_one m s
          have hbez := Nat.gcd_eq_gcd_ab (2 ^ m - 1) (2 ^ s - 1)
          rw [hgcd] at hbez
          have h1z : (uy ^ (2 ^ g - 1) : Fˣ) = uy ^ (((2 ^ g - 1 : ℕ) : ℤ)) := (zpow_natCast _ _).symm
          rw [h1z, hbez, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hu1, hu2]
          simp
        have hg1 : 1 ≤ 2 ^ g := Nat.one_le_pow _ _ (by omega)
        have hval : y ^ (2 ^ g - 1) = 1 := congrArg Units.val hug
        calc y ^ (2 ^ g) = y ^ (2 ^ g - 1 + 1) := by rw [Nat.sub_add_cancel hg1]
          _ = y ^ (2 ^ g - 1) * y := pow_succ _ _
          _ = 1 * y := by rw [hval]
          _ = y := one_mul y
    rw [Multiset.mem_toFinset, Polynomial.mem_roots]
    · simp [Polynomial.IsRoot, hy_g]
    · intro hzero
      have hdeg : (Polynomial.X ^ (2 ^ g) - Polynomial.X : Polynomial F).natDegree = 2 ^ g := by
        have hgt : 1 < 2 ^ g := by
          have hgpos : 0 < g := Nat.gcd_pos_of_pos_left s hm
          have : 2 ^ 1 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hgpos
          omega
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
        · simp
        · simp [hgt]
      rw [hzero, Polynomial.natDegree_zero] at hdeg
      have : 0 < 2 ^ g := by positivity
      omega
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  calc (Finset.univ.filter fun y : F => y ^ (2 ^ s) + y = 0).card
      ≤ (Polynomial.X ^ (2 ^ g) - Polynomial.X : Polynomial F).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (Polynomial.X ^ (2 ^ g) - Polynomial.X : Polynomial F).roots.card := Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ (2 ^ g) - Polynomial.X : Polynomial F).natDegree := Polynomial.card_roots' _
    _ ≤ 2 ^ g := by
      have hgt : 1 < 2 ^ g := by
        have hgpos : 0 < g := Nat.gcd_pos_of_pos_left s hm
        have : 2 ^ 1 ≤ 2 ^ g := Nat.pow_le_pow_right (by omega) hgpos
        omega
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · simp
      · simp [hgt]

private lemma finite_linearMap {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Finite (V →ₗ[ZMod 2] ZMod 2) :=
  Finite.of_injective (fun f : V →ₗ[ZMod 2] ZMod 2 => (f : V → ZMod 2)) DFunLike.coe_injective

private lemma dual_natCard_eq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] :
    Nat.card (V →ₗ[ZMod 2] ZMod 2) = Nat.card V := by
  have : Finite (V →ₗ[ZMod 2] ZMod 2) := finite_linearMap
  let : Fintype V := Fintype.ofFinite V
  let : Fintype (V →ₗ[ZMod 2] ZMod 2) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ZMod 2) (V := V →ₗ[ZMod 2] ZMod 2),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := V),
      Subspace.dual_finrank_eq]

private lemma walsh_gold_sq_le {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s : ℕ} (hm : 0 < m) (hcard : Fintype.card F = 2 ^ m)
    (hodd : Odd (m / Nat.gcd m s))
    (α β : F →ₗ[ZMod 2] ZMod 2) (hβ : β ≠ 0) :
    (∑ a : F, chi (α a + β (a ^ (2 ^ s + 1)))) ^ 2 ≤ (2 ^ (m + Nat.gcd m s) : ℤ) := by
  classical
  have : CharP F 2 := charP_two_of_algebra
  set g := Nat.gcd m s
  set f : F → F := fun a => a ^ (2 ^ s + 1)
  have hsq : (∑ a : F, chi (α a + β (f a))) ^ 2 =
      ∑ h : F, chi (α h) * ∑ a : F, chi (β (f (a + h) + f a)) := by
    rw [sq, Finset.sum_mul_sum]
    have hre : ∑ x : F × F, chi (α x.1 + β (f x.1)) * chi (α x.2 + β (f x.2)) =
        ∑ a : F, ∑ h : F, chi (α a + β (f a)) * chi (α (a + h) + β (f (a + h))) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (Equiv.sum_comp (Equiv.addLeft a) (fun b => chi (α a + β (f a)) * chi (α b + β (f b)))).symm
    rw [← Fintype.sum_prod_type']
    change ∑ x : F × F, chi (α x.1 + β (f x.1)) * chi (α x.2 + β (f x.2)) = _
    rw [hre, Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← chi_add, ← chi_add]
    congr 1
    rw [map_add α a h]
    have hα : α a + α a = 0 := by
      rcases zmod2_cases (α a) with h0 | h1
      · rw [h0]; rfl
      · rw [h1]; rfl
    calc α a + β (f a) + (α a + α h + β (f (a + h)))
        = (α a + α a) + α h + (β (f (a + h)) + β (f a)) := by ring
      _ = α h + β (f (a + h) + f a) := by rw [hα, zero_add, ← map_add]
  let T : F →ₗ[ZMod 2] F :=
    { toFun := fun y => y ^ (2 ^ s) + y
      map_add' := fun x y => by rw [add_pow_two_pow_char2]; ring
      map_smul' := fun c y => by
        rcases zmod2_cases c with rfl | rfl
        · simp
        · simp }
  let annT : Submodule (ZMod 2) F :=
    { carrier := {c : F | ∀ y : F, β (c * T y) = 0}
      zero_mem' := fun y => by simp, add_mem' := fun {c1 c2} hc1 hc2 y => by rw [add_mul, map_add, hc1 y, hc2 y, add_zero]
      smul_mem' := fun r {c} hc y => by
        rcases zmod2_cases r with rfl | rfl
        · simp
        · simpa using hc y }
  have hinner : ∀ h : F,
      chi (α h) * ∑ a : F, chi (β (f (a + h) + f a)) ≤
      if f h ∈ annT then (2 ^ m : ℤ) else 0 := by
    intro h
    by_cases hh0 : h = 0
    · subst hh0
      have hf0 : f 0 = 0 := zero_pow (by positivity)
      have hmem : f 0 ∈ annT := by rw [hf0]; exact annT.zero_mem
      simp only [hmem, ↓reduceIte, add_zero, add_self_char2, map_zero, chi_zero,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul, hcard, Nat.cast_pow,
        Nat.cast_ofNat, le_refl]
    · let phi : F →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun y => β (f h * T y)
          map_add' := fun x y => by rw [map_add, mul_add, map_add]
          map_smul' := fun r y => by simp [map_smul] }
      have hscale : ∑ a : F, chi (β (f (a + h) + f a)) =
          chi (β (f h)) * ∑ y : F, chi (phi y) := by
        have hbij : ∑ a : F, chi (β (f (a + h) + f a)) =
            ∑ y : F, chi (β (f (h * y + h) + f (h * y))) :=
          (Equiv.sum_comp (Equiv.mulLeft₀ h hh0) (fun a => chi (β (f (a + h) + f a)))).symm
        rw [hbij, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← chi_add]
        change chi (β (f (h * y + h) + f (h * y))) = chi (β (f h) + β (f h * T y))
        rw [← map_add]
        congr 2
        rw [polar_gold]
        change (h * y) ^ (2 ^ s) * h + h ^ (2 ^ s) * (h * y) + h ^ (2 ^ s + 1) =
            h ^ (2 ^ s + 1) + h ^ (2 ^ s + 1) * (y ^ (2 ^ s) + y)
        rw [mul_pow, pow_succ]
        ring
      rw [hscale]
      by_cases hmem : f h ∈ annT
      · simp only [hmem, ↓reduceIte]
        have hphi0 : ∀ y : F, phi y = 0 := hmem
        have hsum : ∑ y : F, chi (phi y) = (2 ^ m : ℤ) := by
          simp [hphi0, chi_zero, hcard]
        rw [hsum, ← mul_assoc, ← chi_add]
        have hle : chi (α h + β (f h)) ≤ 1 := chi_le_one _
        have hpos : (0 : ℤ) ≤ 2 ^ m := by positivity
        nlinarith
      · simp only [hmem, ↓reduceIte]
        have hphi_ne : phi ≠ 0 := by
          intro h0
          apply hmem
          intro y
          exact congrArg (fun g => g y) h0
        rw [sum_chi_linear_eq_zero phi hphi_ne, mul_zero, mul_zero]
  have hsum_le : (∑ a : F, chi (α a + β (f a))) ^ 2 ≤
      ((Finset.univ.filter fun h : F => f h ∈ annT).card : ℤ) * (2 ^ m : ℤ) := by
    rw [hsq]
    calc ∑ h : F, chi (α h) * ∑ a : F, chi (β (f (a + h) + f a))
        ≤ ∑ h : F, (if f h ∈ annT then (2 ^ m : ℤ) else 0) :=
          Finset.sum_le_sum fun h _ => hinner h
      _ = ((Finset.univ.filter fun h : F => f h ∈ annT).card : ℤ) * (2 ^ m : ℤ) := by
          simp [Finset.sum_ite]
  have hcard_h : (Finset.univ.filter fun h : F => f h ∈ annT).card ≤ Nat.card annT := by
    have hinj := gold_injective hm hcard hodd
    have hsub : (Finset.univ.filter fun h : F => f h ∈ annT).image f ⊆
        (Finset.univ.filter fun c : F => c ∈ annT) := by
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨h, hh, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hh).2⟩
    calc (Finset.univ.filter fun h : F => f h ∈ annT).card
        = ((Finset.univ.filter fun h : F => f h ∈ annT).image f).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.univ.filter fun c : F => c ∈ annT).card := Finset.card_le_card hsub
      _ = Nat.card annT := by rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcard_ann : Nat.card annT ≤ 2 ^ g := by
    let pairMap : F →ₗ[ZMod 2] (F →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun c =>
          { toFun := fun z => β (c * z)
            map_add' := fun x y => by rw [mul_add, map_add]
            map_smul' := fun r x => by simp [map_smul] }
        map_add' := fun c1 c2 => by ext z; simp [add_mul, map_add]
        map_smul' := fun r c => by ext z; simp [map_smul] }
    have hpair_inj : Function.Injective pairMap := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      by_contra hc0
      have hex : ∃ w : F, β w ≠ 0 := by
        by_contra h
        push Not at h
        exact hβ (LinearMap.ext h)
      obtain ⟨w, hw⟩ := hex
      have h0 : pairMap c (c⁻¹ * w) = 0 := by rw [hc]; rfl
      change β (c * (c⁻¹ * w)) = 0 at h0
      rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul] at h0
      exact hw h0
    let restrictMap : annT →ₗ[ZMod 2] ((F ⧸ LinearMap.range T) →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun c => Submodule.liftQ (LinearMap.range T) (pairMap c.1) (by
          rintro z ⟨y, rfl⟩
          exact c.2 y)
        map_add' := fun c1 c2 => by
          ext z
          simp [pairMap, map_add]
        map_smul' := fun r c => by
          ext z
          simp [pairMap, map_smul] }
    have hrest_inj : Function.Injective restrictMap := by
      rw [injective_iff_map_eq_zero]
      intro c hc
      ext
      apply hpair_inj
      ext z
      have h0 := congrArg (fun f => f (Submodule.Quotient.mk z)) hc
      simpa [restrictMap] using h0
    have : Finite ((F ⧸ LinearMap.range T) →ₗ[ZMod 2] ZMod 2) := finite_linearMap
    have hle1 : Nat.card annT ≤ Nat.card ((F ⧸ LinearMap.range T) →ₗ[ZMod 2] ZMod 2) :=
      Nat.card_le_card_of_injective restrictMap hrest_inj
    have hdual_card : Nat.card ((F ⧸ LinearMap.range T) →ₗ[ZMod 2] ZMod 2) =
        Nat.card (F ⧸ LinearMap.range T) := dual_natCard_eq
    have hquot_card : Nat.card (F ⧸ LinearMap.range T) = Nat.card (LinearMap.ker T) := by
      have h1 : Nat.card (LinearMap.range T) * Nat.card (F ⧸ LinearMap.range T) = Nat.card F :=
        (Submodule.card_eq_card_quotient_mul_card (LinearMap.range T)).symm
      have h2 : Nat.card (LinearMap.ker T) * Nat.card (LinearMap.range T) = Nat.card F := by
        have e := T.quotKerEquivRange
        have hq := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker T)
        rw [Nat.card_congr e.toEquiv] at hq
        exact hq.symm
      have hpos : 0 < Nat.card (LinearMap.range T) := Nat.card_pos
      nlinarith
    have hker_card : Nat.card (LinearMap.ker T) ≤ 2 ^ g := by
      let e : LinearMap.ker T ≃ {y : F // y ^ (2 ^ s) + y = 0} := Equiv.refl _
      rw [Nat.card_congr e]
      exact card_frobenius_ker_le hm hcard
    omega
  have hcard_le : ((Finset.univ.filter fun h : F => f h ∈ annT).card : ℤ) ≤ (2 ^ g : ℤ) := by
    exact_mod_cast le_trans hcard_h hcard_ann
  have hpow_eq : (2 ^ g : ℤ) * (2 ^ m : ℤ) = (2 ^ (m + g) : ℤ) := by
    rw [pow_add, mul_comm]
  calc (∑ a : F, chi (α a + β (f a))) ^ 2
      ≤ ((Finset.univ.filter fun h : F => f h ∈ annT).card : ℤ) * (2 ^ m : ℤ) := hsum_le
    _ ≤ (2 ^ g : ℤ) * (2 ^ m : ℤ) := by
        have hpos : (0 : ℤ) ≤ 2 ^ m := by positivity
        nlinarith
    _ = (2 ^ (m + g) : ℤ) := hpow_eq

private lemma exists_annihilator_one {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Fintype F]
    (U : Submodule (ZMod 2) F) {v : F} (hv : v ∉ U) :
    ∃ α : F →ₗ[ZMod 2] ZMod 2, (∀ u ∈ U, α u = 0) ∧ α v = 1 := by
  classical
  let q : F ⧸ U := Submodule.Quotient.mk v
  have hq0 : q ≠ 0 := by
    intro h
    exact hv ((Submodule.Quotient.mk_eq_zero U).mp h)
  let L : Submodule (ZMod 2) (F ⧸ U) := Submodule.span (ZMod 2) {q}
  obtain ⟨K, hK⟩ := Submodule.exists_isCompl L
  let projL : (F ⧸ U) →ₗ[ZMod 2] L := Submodule.projectionOnto L K hK
  have hqL : q ∈ L := Submodule.subset_span (Set.mem_singleton q)
  have hL_basis : ∀ x ∈ L, ∃ c : ZMod 2, c • q = x := by
    intro x hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨c, hc⟩
    exact ⟨c, hc⟩
  let toZ2 : L →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => if x.1 = 0 then 0 else 1
      map_add' := fun x y => by
        obtain ⟨cx, hcx⟩ := hL_basis x.1 x.2
        obtain ⟨cy, hcy⟩ := hL_basis y.1 y.2
        have hxy : (x + y).1 = (cx + cy) • q := by
          change x.1 + y.1 = _; rw [← hcx, ← hcy, add_smul]
        rcases zmod2_cases cx with rfl | rfl <;> rcases zmod2_cases cy with rfl | rfl
        · simp [← hcx, ← hcy, hxy]
        · simp [← hcx, ← hcy, hxy, hq0]
        · simp [← hcx, ← hcy, hxy, hq0]
        · have h11 : (1 : ZMod 2) + 1 = 0 := rfl
          simp [← hcx, ← hcy, hxy, hq0, h11]
      map_smul' := fun r x => by
        obtain ⟨cx, hcx⟩ := hL_basis x.1 x.2
        rcases zmod2_cases r with rfl | rfl <;> rcases zmod2_cases cx with rfl | rfl
        · simp [← hcx]
        · simp [← hcx]
        · simp [← hcx]
        · simp [← hcx, hq0] }
  let α : F →ₗ[ZMod 2] ZMod 2 := toZ2.comp (projL.comp (Submodule.mkQ U))
  refine ⟨α, ?_, ?_⟩
  · intro u hu
    simp only [α, LinearMap.comp_apply, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero U).mpr hu, map_zero]
  · have hproj : projL q = ⟨q, hqL⟩ := Submodule.projectionOnto_apply_left hK ⟨q, hqL⟩
    change toZ2 (projL q) = 1
    rw [hproj]
    simp [toZ2, hq0]

private def annSub {F : Type} [AddCommGroup F] [Module (ZMod 2) F]
    (U : Submodule (ZMod 2) F) : Submodule (ZMod 2) (F →ₗ[ZMod 2] ZMod 2) :=
  { carrier := {α | ∀ u ∈ U, α u = 0}
    zero_mem' := fun _ _ => rfl, add_mem' := fun h1 h2 u hu => by simp [h1 u hu, h2 u hu]
    smul_mem' := fun r {_} hh u hu => by simp [hh u hu] }

private lemma coset_indicator_sum {F : Type} [AddCommGroup F] [Module (ZMod 2) F] [Fintype F]
    (U : Submodule (ZMod 2) F) (x0 a : F) [Fintype (annSub U)] [Decidable (a - x0 ∈ U)] :
    ∑ α : annSub U, chi (α.1 (a - x0)) =
      if a - x0 ∈ U then (Fintype.card (annSub U) : ℤ) else 0 := by
  by_cases hmem : a - x0 ∈ U
  · simp only [hmem, ↓reduceIte]
    have hterm : ∀ α : annSub U, chi (α.1 (a - x0)) = 1 := fun α => by
      rw [α.2 (a - x0) hmem]; rfl
    rw [Finset.sum_congr rfl fun α _ => hterm α]
    simp
  · simp only [hmem, ↓reduceIte]
    obtain ⟨α0, hα0U, hα0v⟩ := exists_annihilator_one U hmem
    let v0 : annSub U := ⟨α0, hα0U⟩
    have hshift : ∑ α : annSub U, chi (α.1 (a - x0)) = ∑ α : annSub U, chi ((α + v0).1 (a - x0)) :=
      (Equiv.sum_comp (Equiv.addRight v0) (fun α : annSub U => chi (α.1 (a - x0)))).symm
    have hneg : ∑ α : annSub U, chi ((α + v0).1 (a - x0)) = - ∑ α : annSub U, chi (α.1 (a - x0)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      change chi (α.1 (a - x0) + α0 (a - x0)) = - chi (α.1 (a - x0))
      rw [hα0v, chi_add]
      change chi (α.1 (a - x0)) * (-1) = - chi (α.1 (a - x0))
      ring
    omega

private lemma graph_corr_coset {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s t : ℕ} (hm : 0 < m) (hcard : Fintype.card F = 2 ^ m)
    (hodd : Odd (m / Nat.gcd m s)) (ht : 2 * t ≤ m)
    (U : Submodule (ZMod 2) F) (hUcard : Nat.card U = 2 ^ (m - t))
    (x0 x1 : F) :
    Nat.card {a : F // a - x0 ∈ U ∧ a ^ (2 ^ s + 1) - x1 ∈ U} ≤
      2 ^ (m - 2 * t) + 2 ^ ((m + Nat.gcd m s) / 2) := by
  classical
  set g := Nat.gcd m s
  set f : F → F := fun a => a ^ (2 ^ s + 1)
  have : Finite (F →ₗ[ZMod 2] ZMod 2) := finite_linearMap
  let : Fintype (annSub U) := Fintype.ofFinite _
  have hann_card : Fintype.card (annSub U) = 2 ^ t := by
    let e : annSub U ≃ₗ[ZMod 2] ((F ⧸ U) →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun α => Submodule.liftQ U α.1 (fun u hu => α.2 u hu)
        invFun := fun ψ => ⟨ψ.comp (Submodule.mkQ U), fun u hu => by
          simp [(Submodule.Quotient.mk_eq_zero U).mpr hu]⟩
        left_inv := fun α => by ext x; rfl
        right_inv := fun ψ => by ext x; rfl
        map_add' := fun α1 α2 => by ext x; rfl
        map_smul' := fun r α => by ext x; rfl }
    have hc1 : Nat.card (annSub U) = Nat.card (F ⧸ U) := by
      rw [Nat.card_congr e.toEquiv, dual_natCard_eq]
    have hmul : Nat.card U * Nat.card (F ⧸ U) = Nat.card F :=
      (Submodule.card_eq_card_quotient_mul_card U).symm
    have hcardF : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hcard]
    rw [hUcard, hcardF] at hmul
    have hpow : 2 ^ (m - t) * 2 ^ t = 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [← Nat.card_eq_fintype_card, hc1]
    have hpos : 0 < 2 ^ (m - t) := by positivity
    nlinarith
  set S := Finset.univ.filter fun a : F => a - x0 ∈ U ∧ f a - x1 ∈ U
  have hfour : ((2 ^ t : ℤ) * (2 ^ t : ℤ)) * (S.card : ℤ) =
      ∑ α : annSub U, ∑ β : annSub U,
        chi (α.1 x0 + β.1 x1) * ∑ a : F, chi (α.1 a + β.1 (f a)) := by
    have h1 : ∀ a : F,
        (∑ α : annSub U, chi (α.1 (a - x0))) * (∑ β : annSub U, chi (β.1 (f a - x1))) =
        if a - x0 ∈ U ∧ f a - x1 ∈ U then (2 ^ t : ℤ) * (2 ^ t : ℤ) else 0 := by
      intro a
      rw [coset_indicator_sum U x0 a, coset_indicator_sum U x1 (f a), hann_card]
      by_cases h1 : a - x0 ∈ U <;> by_cases h2 : f a - x1 ∈ U <;> simp [h1, h2]
    have hsum_lhs : ((2 ^ t : ℤ) * (2 ^ t : ℤ)) * (S.card : ℤ) =
        ∑ a : F, (∑ α : annSub U, chi (α.1 (a - x0))) * (∑ β : annSub U, chi (β.1 (f a - x1))) := by
      rw [Finset.sum_congr rfl fun a _ => h1 a]
      simp [S, Finset.sum_ite, mul_comm]
    rw [hsum_lhs]
    have hexp : ∀ a : F,
        (∑ α : annSub U, chi (α.1 (a - x0))) * (∑ β : annSub U, chi (β.1 (f a - x1))) =
        ∑ α : annSub U, ∑ β : annSub U, chi (α.1 x0 + β.1 x1) * chi (α.1 a + β.1 (f a)) := by
      intro a
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [← chi_add, ← chi_add]
      congr 1
      rw [map_sub, map_sub]
      have hneg : ∀ z : ZMod 2, -z = z := fun z => by
        rcases zmod2_cases z with rfl | rfl <;> rfl
      rw [sub_eq_add_neg, sub_eq_add_neg, hneg, hneg]
      ring
    rw [Finset.sum_congr rfl fun a _ => hexp a]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum]
  have hmg_even : 2 * ((m + g) / 2) = m + g := by
    have hdvd : g ∣ m := Nat.gcd_dvd_left m s
    obtain ⟨k, hk⟩ := hodd
    have hm_eq : m = g * (2 * k + 1) := by
      calc m = g * (m / g) := (Nat.mul_div_cancel' hdvd).symm
        _ = g * (2 * k + 1) := by rw [hk]
    have hsum : m + g = 2 * (g * (k + 1)) := by rw [hm_eq]; ring
    omega
  have hterm_le : ∀ α β : annSub U,
      chi (α.1 x0 + β.1 x1) * ∑ a : F, chi (α.1 a + β.1 (f a)) ≤
        (if α = 0 ∧ β = 0 then (2 ^ m : ℤ) else 0) + (2 ^ ((m + g) / 2) : ℤ) := by
    intro α β
    by_cases hβ0 : β.1 = 0
    · by_cases hα0 : α.1 = 0
      · have hα : α = 0 := Subtype.ext hα0
        have hβ : β = 0 := Subtype.ext hβ0
        simp only [hα, hβ, and_self, ↓reduceIte, ZeroMemClass.coe_zero, LinearMap.zero_apply, add_zero,
          chi_zero, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          hcard, Nat.cast_pow, Nat.cast_ofNat]
        have : (0 : ℤ) ≤ 2 ^ ((m + g) / 2) := by positivity
        omega
      · have hsum0 : ∑ a : F, chi (α.1 a + β.1 (f a)) = 0 := by
          simp only [hβ0, LinearMap.zero_apply, add_zero]
          exact sum_chi_linear_eq_zero α.1 hα0
        rw [hsum0, mul_zero]
        have hpos1 : (0 : ℤ) ≤ if α = 0 ∧ β = 0 then 2 ^ m else 0 := by split_ifs <;> positivity
        have hpos2 : (0 : ℤ) ≤ 2 ^ ((m + g) / 2) := by positivity
        omega
    · have hWsq : (∑ a : F, chi (α.1 a + β.1 (f a))) ^ 2 ≤ ((2 ^ ((m + g) / 2) : ℤ)) ^ 2 := by
        calc (∑ a : F, chi (α.1 a + β.1 (f a))) ^ 2
            ≤ (2 ^ (m + g) : ℤ) := walsh_gold_sq_le hm hcard hodd α.1 β.1 hβ0
          _ = (2 ^ (2 * ((m + g) / 2)) : ℤ) := by rw [hmg_even]
          _ = ((2 ^ ((m + g) / 2) : ℤ)) ^ 2 := by rw [pow_mul']
      have hWabs : |∑ a : F, chi (α.1 a + β.1 (f a))| ≤ (2 ^ ((m + g) / 2) : ℤ) := by
        have hpos : (0 : ℤ) ≤ 2 ^ ((m + g) / 2) := by positivity
        nlinarith [sq_abs (∑ a : F, chi (α.1 a + β.1 (f a)))]
      have hprod : chi (α.1 x0 + β.1 x1) * ∑ a : F, chi (α.1 a + β.1 (f a)) ≤
          (2 ^ ((m + g) / 2) : ℤ) := by
        have h1 : |chi (α.1 x0 + β.1 x1) * ∑ a : F, chi (α.1 a + β.1 (f a))| =
            |∑ a : F, chi (α.1 a + β.1 (f a))| := by
          rw [abs_mul, chi_abs, one_mul]
        exact (le_abs_self _).trans (h1 ▸ hWabs)
      have hpos1 : (0 : ℤ) ≤ if α = 0 ∧ β = 0 then 2 ^ m else 0 := by split_ifs <;> positivity
      omega
  have htotal : ((2 ^ t : ℤ) * (2 ^ t : ℤ)) * (S.card : ℤ) ≤
      (2 ^ m : ℤ) + ((2 ^ t : ℤ) * (2 ^ t : ℤ)) * (2 ^ ((m + g) / 2) : ℤ) := by
    rw [hfour]
    calc ∑ α : annSub U, ∑ β : annSub U, chi (α.1 x0 + β.1 x1) * ∑ a : F, chi (α.1 a + β.1 (f a))
        ≤ ∑ α : annSub U, ∑ β : annSub U,
            ((if α = 0 ∧ β = 0 then (2 ^ m : ℤ) else 0) + (2 ^ ((m + g) / 2) : ℤ)) :=
          Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => hterm_le α β
      _ = (∑ α : annSub U, ∑ β : annSub U, if α = 0 ∧ β = 0 then (2 ^ m : ℤ) else 0) +
          (∑ α : annSub U, ∑ β : annSub U, (2 ^ ((m + g) / 2) : ℤ)) := by
          simp [Finset.sum_add_distrib]
      _ = (2 ^ m : ℤ) + ((2 ^ t : ℤ) * (2 ^ t : ℤ)) * (2 ^ ((m + g) / 2) : ℤ) := by
          have hzero : ∑ α : annSub U, ∑ β : annSub U,
              (if α = 0 ∧ β = 0 then (2 ^ m : ℤ) else 0) = (2 ^ m : ℤ) := by
            rw [Finset.sum_eq_single (0 : annSub U)]
            · simp
            · intro b _ hb; simp [hb]
            · intro h; exact (h (Finset.mem_univ _)).elim
          rw [hzero]
          simp [hann_card, mul_assoc]
  have h2m : (2 ^ m : ℤ) = ((2 ^ t : ℤ) * (2 ^ t : ℤ)) * (2 ^ (m - 2 * t) : ℤ) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [h2m, ← mul_add] at htotal
  have hpos : (0 : ℤ) < (2 ^ t : ℤ) * (2 ^ t : ℤ) := by positivity
  have hle_z : (S.card : ℤ) ≤ (2 ^ (m - 2 * t) : ℤ) + (2 ^ ((m + g) / 2) : ℤ) := by nlinarith
  have hle_n : S.card ≤ 2 ^ (m - 2 * t) + 2 ^ ((m + g) / 2) := by exact_mod_cast hle_z
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hle_n

private lemma pair_count_in_coset {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {m s t : ℕ} (hm : 0 < m) (hcard : Fintype.card F = 2 ^ m)
    (hodd : Odd (m / Nat.gcd m s)) (ht : 2 * t ≤ m)
    (W : Submodule (ZMod 2) (ZMod 2 × F)) (hWcard : Nat.card W = 2 ^ (m + 1 - t))
    (z0 : ZMod 2 × F) :
    Nat.card {a : F // ((0 : ZMod 2), a) - z0 ∈ W ∧ ((1 : ZMod 2), a ^ (2 ^ s + 1)) - z0 ∈ W} ≤
      2 ^ (m - 2 * t) + 2 ^ ((m + Nat.gcd m s) / 2) := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  set S := Finset.univ.filter fun a : F =>
    ((0 : ZMod 2), a) - z0 ∈ W ∧ ((1 : ZMod 2), a ^ (2 ^ s + 1)) - z0 ∈ W
  by_cases hSne : S.Nonempty
  · obtain ⟨a0, ha0⟩ := hSne
    obtain ⟨h0_mem, h1_mem⟩ := (Finset.mem_filter.mp ha0).2
    let x0 : F := a0
    let x1 : F := a0 ^ (2 ^ s + 1)
    let U : Submodule (ZMod 2) F := W.comap (LinearMap.inr (ZMod 2) (ZMod 2) F)
    have hUcard : Nat.card U = 2 ^ (m - t) := by
      let fstW : W →ₗ[ZMod 2] ZMod 2 := (LinearMap.fst (ZMod 2) (ZMod 2) F).comp W.subtype
      have hsurj : Function.Surjective fstW := by
        intro c
        rcases zmod2_cases c with rfl | rfl
        · exact ⟨0, rfl⟩
        · refine ⟨⟨((1 : ZMod 2), x1) - z0 - (((0 : ZMod 2), x0) - z0), W.sub_mem h1_mem h0_mem⟩, ?_⟩
          simp [fstW]
      have hker_eq : Nat.card (LinearMap.ker fstW) = Nat.card U := by
        let e : LinearMap.ker fstW ≃ U :=
          { toFun := fun w => ⟨w.1.1.2, by
              have h1 : w.1.1.1 = 0 := w.2
              have hpair : ((0 : ZMod 2), w.1.1.2) = w.1.1 := Prod.ext h1.symm rfl
              change ((0 : ZMod 2), w.1.1.2) ∈ W
              rw [hpair]; exact w.1.2⟩
            invFun := fun u => ⟨⟨((0 : ZMod 2), u.1), u.2⟩, rfl⟩
            left_inv := fun w => by
              ext
              · exact w.2.symm
              · rfl
            right_inv := fun u => by ext; rfl }
        exact Nat.card_congr e
      have hr : Nat.card (LinearMap.range fstW) = 2 := by
        have htop : LinearMap.range fstW = ⊤ := LinearMap.range_eq_top.mpr hsurj
        have e1 : LinearMap.range fstW ≃ₗ[ZMod 2] ZMod 2 := LinearEquiv.ofTop (LinearMap.range fstW) htop
        rw [Nat.card_congr e1.toEquiv]
        simp
      have hmul : Nat.card (LinearMap.ker fstW) * Nat.card (LinearMap.range fstW) = Nat.card W := by
        have e := fstW.quotKerEquivRange
        have hq := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker fstW)
        rw [Nat.card_congr e.toEquiv] at hq
        exact hq.symm
      rw [hr, hker_eq, hWcard] at hmul
      have hpow : 2 ^ (m - t) * 2 = 2 ^ (m + 1 - t) := by
        rw [← pow_succ]
        congr 1
        omega
      omega
    have hsub : S ⊆ Finset.univ.filter fun a : F => a - x0 ∈ U ∧ a ^ (2 ^ s + 1) - x1 ∈ U := by
      intro a ha
      obtain ⟨ha0', ha1'⟩ := (Finset.mem_filter.mp ha).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · have hdiff := W.sub_mem ha0' h0_mem
        have heq : ((0 : ZMod 2), a - x0) = (((0 : ZMod 2), a) - z0) - (((0 : ZMod 2), x0) - z0) := by
          ext <;> simp
        change ((0 : ZMod 2), a - x0) ∈ W
        rw [heq]; exact hdiff
      · have hdiff := W.sub_mem ha1' h1_mem
        have heq : ((0 : ZMod 2), a ^ (2 ^ s + 1) - x1) =
            (((1 : ZMod 2), a ^ (2 ^ s + 1)) - z0) - (((1 : ZMod 2), x1) - z0) := by
          ext <;> simp
        change ((0 : ZMod 2), a ^ (2 ^ s + 1) - x1) ∈ W
        rw [heq]; exact hdiff
    have hgc := graph_corr_coset hm hcard hodd ht U hUcard x0 x1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hgc
    exact (Finset.card_le_card hsub).trans hgc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hSne, Finset.card_empty]
    exact Nat.zero_le _

private lemma list_prefix_or_diverge : ∀ (p1 p2 : List Bool),
    p1 <+: p2 ∨ p2 <+: p1 ∨ ∃ j : ℕ, ∃ (h1 : j < p1.length) (h2 : j < p2.length),
      p1.take j = p2.take j ∧ p1[j] ≠ p2[j] := by
  intro p1
  induction p1 with
  | nil => intro p2; exact Or.inl List.nil_prefix
  | cons a t1 ih =>
    intro p2
    cases p2 with
    | nil => exact Or.inr (Or.inl List.nil_prefix)
    | cons b t2 =>
      by_cases hab : a = b
      · subst hab
        rcases ih t2 with h1 | h2 | ⟨j, hj1, hj2, htake, hne⟩
        · exact Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h1⟩)
        · exact Or.inr (Or.inl (List.cons_prefix_cons.mpr ⟨rfl, h2⟩))
        · exact Or.inr (Or.inr ⟨j + 1, by simp [hj1], by simp [hj2], by simp [htake], by simpa using hne⟩)
      · exact Or.inr (Or.inr ⟨0, by simp, by simp, rfl, by simpa using hab⟩)

private lemma take_mem_J_of_strict_prefix {N J : Finset (List Bool)}
    (hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    {p : List Bool} (hp : p ∈ N) :
    ∀ k < p.length, p.take k ∈ J := by
  have hdesc : ∀ d k, k + d = p.length → p.take k ∈ N := by
    intro d
    induction d with
    | zero =>
      intro k hd
      have : k = p.length := by omega
      subst this
      simpa using hp
    | succ d ih =>
      intro k hd
      have hklt : k < p.length := by omega
      have hstep : p.take (k + 1) = p.take k ++ [p[k]] := List.take_succ_eq_append_getElem hklt
      have hnext : p.take (k + 1) ∈ N := ih (k + 1) (by omega)
      rw [hstep] at hnext
      exact hshape.2.1 (hshape.2.2.1 _ _ hnext)
  intro k hk
  have hnext : p.take (k + 1) ∈ N := hdesc (p.length - (k + 1)) (k + 1) (by omega)
  rw [List.take_succ_eq_append_getElem hk] at hnext
  exact hshape.2.2.1 _ _ hnext

private theorem main_thm :
    let shape := fun (N J : Finset (List Bool)) =>
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
    let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
      {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
    let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
        (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
      shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
        (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
    ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
        (m s : ℕ), 0 < m → 0 < s → Fintype.card F = 2^m →
      let g := Nat.gcd m s
      Odd (m/g) →
        let t := (m-g)/4
        ∀ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × F) → Bool)
          (out : List Bool → F),
          cert (queries (ZMod 2 × F))
            (fun z a => if z.1 = 0 then z.2 = a else z.2 = a^(2^s+1)) N J q out →
          2^(m+1) ≤ (N \ J).card + 2^(m-t) + 2^(t+(m+g)/2) := by
  classical
  intro shape queries cert F _ _ _ m s hm hs hcard g hodd t N J q out hcert
  obtain ⟨hshape, hq_in, hok⟩ := hcert
  let V := ZMod 2 × F
  have hVcard : Fintype.card V = 2 ^ (m + 1) := by
    simp [V, hcard, pow_succ, mul_comm]
  have hVrank : Module.finrank (ZMod 2) V = m + 1 := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hVcard, ZMod.card] at h1
    exact Nat.pow_right_injective (by omega : 1 < 2) h1.symm
  have hsub_card : ∀ W : Submodule (ZMod 2) V, Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
    intro W
    let : Fintype W := Fintype.ofFinite W
    rw [Nat.card_eq_fintype_card]
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    simpa [ZMod.card] using h1
  let linOf : List Bool → (V →ₗ[ZMod 2] ZMod 2) := fun u =>
    if h : u ∈ J then (hq_in u h).choose else 0
  let rhsOf : List Bool → ZMod 2 := fun u =>
    if h : u ∈ J then (hq_in u h).choose_spec.choose else 0
  have hq_spec : ∀ u ∈ J, ∀ z : V, q u z = decide (linOf u z = rhsOf u) := by
    intro u hu z
    have hspec := (hq_in u hu).choose_spec.choose_spec
    have hlin : linOf u = (hq_in u hu).choose := dite_eq_left hu
    have hrhs : rhsOf u = (hq_in u hu).choose_spec.choose := dite_eq_left hu
    rw [hlin, hrhs]
    exact congrFun hspec z
  let pathSet : List Bool → Finset V := fun p =>
    Finset.univ.filter fun z => ∀ j : Fin p.length, q (p.take j.val) z = p.get j
  let kerSub : List Bool → Submodule (ZMod 2) V := fun p =>
    ⨅ j : Fin p.length, LinearMap.ker (linOf (p.take j.val))
  have hpath_coset : ∀ p ∈ N, ∀ z0 ∈ pathSet p,
      ∀ z : V, z ∈ pathSet p ↔ z - z0 ∈ kerSub p := by
    intro p hp z0 hz0 z
    have hz0' := (Finset.mem_filter.mp hz0).2
    simp only [pathSet, kerSub, Finset.mem_filter, Finset.mem_univ, true_and,
      Submodule.mem_iInf, LinearMap.mem_ker, map_sub]
    constructor
    · intro hz j
      have huJ : p.take j.val ∈ J := take_mem_J_of_strict_prefix hshape hp j.val j.isLt
      have h1 := hz j
      have h2 := hz0' j
      rw [hq_spec _ huJ z] at h1
      rw [hq_spec _ huJ z0] at h2
      have heq : decide (linOf (p.take j.val) z = rhsOf (p.take j.val)) =
          decide (linOf (p.take j.val) z0 = rhsOf (p.take j.val)) := h1.trans h2.symm
      have hval : linOf (p.take j.val) z = linOf (p.take j.val) z0 := by
        rcases zmod2_cases (linOf (p.take j.val) z) with ha | ha <;>
        rcases zmod2_cases (linOf (p.take j.val) z0) with hb | hb <;>
        rcases zmod2_cases (rhsOf (p.take j.val)) with hr | hr <;>
        simp [ha, hb, hr] at heq ⊢
      rw [hval, sub_self]
    · intro hker j
      have huJ : p.take j.val ∈ J := take_mem_J_of_strict_prefix hshape hp j.val j.isLt
      have h0 := hker j
      have hval : linOf (p.take j.val) z = linOf (p.take j.val) z0 := sub_eq_zero.mp h0
      rw [hq_spec _ huJ z, hval, ← hq_spec _ huJ z0]
      exact hz0' j
  have hpath_card : ∀ p ∈ N, ∀ z0 ∈ pathSet p, (pathSet p).card = Nat.card (kerSub p) := by
    intro p hp z0 hz0
    let e : {z : V // z ∈ pathSet p} ≃ kerSub p :=
      { toFun := fun z => ⟨z.1 - z0, (hpath_coset p hp z0 hz0 z.1).mp z.2⟩
        invFun := fun w => ⟨w.1 + z0, (hpath_coset p hp z0 hz0 (w.1 + z0)).mpr (by simp [w.2])⟩
        left_inv := fun z => Subtype.ext (sub_add_cancel z.1 z0)
        right_inv := fun w => Subtype.ext (add_sub_cancel_right w.1 z0) }
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr e
  have hpath_mono : ∀ {p1 p2 : List Bool}, p1 <+: p2 → pathSet p2 ⊆ pathSet p1 := by
    intro p1 p2 hpre z hz
    rcases hpre with ⟨suf, rfl⟩
    have hz' := (Finset.mem_filter.mp hz).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
    have hjlt : j.val < (p1 ++ suf).length := by simp; omega
    have h := hz' ⟨j.val, hjlt⟩
    rw [List.take_append_of_le_length (le_of_lt j.isLt)] at h
    simpa [List.get_eq_getElem, List.getElem_append_left j.isLt] using h
  have hdisj_of_diverge : ∀ {p1 p2 : List Bool}, ¬ (p1 <+: p2) → ¬ (p2 <+: p1) →
      Disjoint (pathSet p1) (pathSet p2) := by
    intro p1 p2 h12 h21
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    rcases list_prefix_or_diverge p1 p2 with h | h | ⟨j, hj1, hj2, htake, hne⟩
    · exact h12 h
    · exact h21 h
    · have h1 := (Finset.mem_filter.mp hz1).2 ⟨j, hj1⟩
      have h2 := (Finset.mem_filter.mp hz2).2 ⟨j, hj2⟩
      rw [htake] at h1
      have heq : p1[j] = p2[j] := by
        have := h1.symm.trans h2
        simpa [List.get_eq_getElem] using this
      exact hne heq
  have hleaves_cover : Finset.univ ⊆ (N \ J).biUnion pathSet := by
    intro z _
    let S_z := N.filter fun p => z ∈ pathSet p
    have hSne : S_z.Nonempty := by
      refine ⟨[], Finset.mem_filter.mpr ⟨hshape.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩⟩⟩
      exact absurd j.isLt (by simp)
    obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image S_z List.length hSne
    obtain ⟨hpN, hzp⟩ := Finset.mem_filter.mp hpS
    have hpNotJ : p ∉ J := by
      intro hpJ
      let b := q p z
      have hpbN : p ++ [b] ∈ N := by
        cases hb : b
        · exact (hshape.2.2.2 p hpJ).1
        · exact (hshape.2.2.2 p hpJ).2
      have hzpb : z ∈ pathSet (p ++ [b]) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
        by_cases hj : j.val < p.length
        · rw [List.take_append_of_le_length (le_of_lt hj)]
          have h := (Finset.mem_filter.mp hzp).2 ⟨j.val, hj⟩
          simpa [List.get_eq_getElem, List.getElem_append_left hj] using h
        · have hj_eq : j.val = p.length := by have := j.isLt; simp at this; omega
          simp only [List.get_eq_getElem, hj_eq, List.take_left, List.getElem_append_right (le_refl _),
            Nat.sub_self, List.getElem_singleton]
          rfl
      have hle := hpmax (p ++ [b]) (Finset.mem_filter.mpr ⟨hpbN, hzpb⟩)
      simp at hle
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hpN, hpNotJ⟩, hzp⟩
  have hleaf_sub_pair : ∀ p ∈ N \ J,
      pathSet p ⊆ ({((0 : ZMod 2), out p), ((1 : ZMod 2), (out p) ^ (2 ^ s + 1))} : Finset V) := by
    intro p hp z hz
    have hokz := hok p hp z (Finset.mem_filter.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases z with ⟨c, y⟩
    rcases zmod2_cases c with rfl | rfl
    · simp only [↓reduceIte] at hokz
      exact Or.inl (Prod.ext rfl hokz)
    · simp only [one_ne_zero, ↓reduceIte] at hokz
      exact Or.inr (Prod.ext rfl hokz)
  let L2 : Finset (List Bool) := (N \ J).filter fun p => (pathSet p).card = 2
  have htotal_leaves : 2 ^ (m + 1) ≤ (N \ J).card + L2.card := by
    have h1 : 2 ^ (m + 1) ≤ ∑ p ∈ N \ J, (pathSet p).card := by
      rw [← hVcard, ← Finset.card_univ]
      exact (Finset.card_le_card hleaves_cover).trans Finset.card_biUnion_le
    have h2 : ∑ p ∈ N \ J, (pathSet p).card ≤ ∑ p ∈ N \ J, (1 + if (pathSet p).card = 2 then 1 else 0) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hle2 : (pathSet p).card ≤ 2 :=
        (Finset.card_le_card (hleaf_sub_pair p hp)).trans Finset.card_le_two
      by_cases hc : (pathSet p).card = 2 <;> simp [hc]; omega
    calc 2 ^ (m + 1) ≤ ∑ p ∈ N \ J, (pathSet p).card := h1
      _ ≤ ∑ p ∈ N \ J, (1 + if (pathSet p).card = 2 then 1 else 0) := h2
      _ = (N \ J).card + L2.card := by
          rw [Finset.sum_add_distrib]
          simp [L2]
  have hker_step : ∀ (p : List Bool) (k : ℕ) (hk : k < p.length),
      Module.finrank (ZMod 2) (kerSub (p.take k)) ≤
        Module.finrank (ZMod 2) (kerSub (p.take (k + 1))) + 1 ∧
      Module.finrank (ZMod 2) (kerSub (p.take (k + 1))) ≤
        Module.finrank (ZMod 2) (kerSub (p.take k)) := by
    intro p k hk
    have hinf : kerSub (p.take (k + 1)) =
        kerSub (p.take k) ⊓ LinearMap.ker (linOf (p.take k)) := by
      ext z
      simp only [kerSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      constructor
      · intro h
        refine ⟨fun j => ?_, ?_⟩
        · have hj1 : j.val < (p.take (k + 1)).length := by
            have := j.isLt; simp at this ⊢; omega
          have hget := h ⟨j.val, hj1⟩
          have htk : (p.take (k + 1)).take j.val = (p.take k).take j.val := by
            rw [List.take_take, List.take_take, Nat.min_eq_left, Nat.min_eq_left]
            · have := j.isLt; simp at this; omega
            · have := j.isLt; simp at this; omega
          rwa [htk] at hget
        · have hk1 : k < (p.take (k + 1)).length := by simp; omega
          have hget := h ⟨k, hk1⟩
          have htk : (p.take (k + 1)).take k = p.take k := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          rwa [htk] at hget
      · rintro ⟨h1, h2⟩ j
        have hjlt : j.val < k + 1 := by have := j.isLt; simp at this; omega
        by_cases hjk : j.val < k
        · have hj' : j.val < (p.take k).length := by simp; omega
          have hget := h1 ⟨j.val, hj'⟩
          have htk : (p.take (k + 1)).take j.val = (p.take k).take j.val := by
            rw [List.take_take, List.take_take, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega)]
          rwa [htk]
        · have hjeq : j.val = k := by omega
          have htk : (p.take (k + 1)).take j.val = p.take k := by
            rw [hjeq, List.take_take, Nat.min_eq_left (by omega)]
          rwa [htk]
    rw [hinf]
    refine ⟨?_, Submodule.finrank_mono inf_le_left⟩
    let restr : kerSub (p.take k) →ₗ[ZMod 2] ZMod 2 := (linOf (p.take k)).domRestrict (kerSub (p.take k))
    have hker_iso : Module.finrank (ZMod 2) (LinearMap.ker restr) =
        Module.finrank (ZMod 2) (kerSub (p.take k) ⊓ LinearMap.ker (linOf (p.take k)) : Submodule (ZMod 2) V) := by
      let e : LinearMap.ker restr ≃ₗ[ZMod 2]
          (kerSub (p.take k) ⊓ LinearMap.ker (linOf (p.take k)) : Submodule (ZMod 2) V) :=
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact e.finrank_eq
    have hrn := LinearMap.finrank_range_add_finrank_ker restr
    have hrange_le : Module.finrank (ZMod 2) (LinearMap.range restr) ≤ 1 := by
      calc Module.finrank (ZMod 2) (LinearMap.range restr)
          ≤ Module.finrank (ZMod 2) (ZMod 2) := Submodule.finrank_le _
        _ = 1 := Module.finrank_self (ZMod 2)
    omega
  have ht_le : 2 * t ≤ m := by omega
  have htarget_ge1 : 1 ≤ m + 1 - t := by omega
  have hfind_anc : ∀ p ∈ L2, ∃ k ≤ p.length,
      Module.finrank (ZMod 2) (kerSub (p.take k)) = m + 1 - t ∧
      ∀ k' < k, Module.finrank (ZMod 2) (kerSub (p.take k')) ≠ m + 1 - t := by
    intro p hpL2
    obtain ⟨hpNJ, hcard2⟩ := Finset.mem_filter.mp hpL2
    have hpN : p ∈ N := (Finset.mem_sdiff.mp hpNJ).1
    have hne : (pathSet p).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨z0, hz0⟩ := hne
    have hrank_end : Module.finrank (ZMod 2) (kerSub (p.take p.length)) = 1 := by
      have hc := hpath_card p hpN z0 hz0
      rw [hcard2, hsub_card] at hc
      have h1 : (2 : ℕ) ^ 1 = 2 ^ Module.finrank (ZMod 2) (kerSub p) := by simpa using hc
      have h2 := Nat.pow_right_injective (by omega : 1 < 2) h1
      rw [List.take_length]
      exact h2.symm
    have hrank_start : Module.finrank (ZMod 2) (kerSub (p.take 0)) = m + 1 := by
      have htop : kerSub [] = ⊤ := by
        ext z; simp [kerSub]
      rw [List.take_zero, htop, finrank_top, hVrank]
    have hex : ∃ k, k ≤ p.length ∧ Module.finrank (ZMod 2) (kerSub (p.take k)) = m + 1 - t := by
      have haux : ∀ k ≤ p.length,
          Module.finrank (ZMod 2) (kerSub (p.take k)) ≤ m + 1 - t →
          ∃ j ≤ k, Module.finrank (ZMod 2) (kerSub (p.take j)) = m + 1 - t := by
        intro k
        induction k with
        | zero =>
          intro _ hle
          exact ⟨0, le_refl 0, by omega⟩
        | succ k ih =>
          intro hkle hle
          by_cases hprev : Module.finrank (ZMod 2) (kerSub (p.take k)) ≤ m + 1 - t
          · obtain ⟨j, hj, hjeq⟩ := ih (by omega) hprev
            exact ⟨j, by omega, hjeq⟩
          · have hst := (hker_step p k (by omega)).1
            exact ⟨k + 1, le_refl _, by omega⟩
      exact haux p.length (le_refl _) (by omega)
    let k0 := Nat.find hex
    obtain ⟨hk0_le, hk0_eq⟩ := Nat.find_spec hex
    refine ⟨k0, hk0_le, hk0_eq, fun k' hk' hEq => ?_⟩
    exact Nat.find_min hex hk' ⟨by omega, hEq⟩
  let ancOf : (p : List Bool) → p ∈ L2 → List Bool := fun p hp => p.take (hfind_anc p hp).choose
  let M : Finset (List Bool) := L2.attach.image fun p => ancOf p.1 p.2
  have hM_memN : ∀ u ∈ M, u ∈ N := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨⟨p, hpL2⟩, _, rfl⟩
    have hpN : p ∈ N := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hpL2).1).1
    have hk_le := (hfind_anc p hpL2).choose_spec.1
    by_cases hlt : (hfind_anc p hpL2).choose < p.length
    · exact hshape.2.1 (take_mem_J_of_strict_prefix hshape hpN _ hlt)
    · have heq : (hfind_anc p hpL2).choose = p.length := by omega
      simpa [ancOf, heq] using hpN
  have hM_rank : ∀ u ∈ M, Module.finrank (ZMod 2) (kerSub u) = m + 1 - t := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨⟨p, hpL2⟩, _, rfl⟩
    exact (hfind_anc p hpL2).choose_spec.2.1
  have hM_min : ∀ u ∈ M, ∀ k' < u.length, Module.finrank (ZMod 2) (kerSub (u.take k')) ≠ m + 1 - t := by
    intro u hu k' hk'
    rcases Finset.mem_image.mp hu with ⟨⟨p, hpL2⟩, _, rfl⟩
    dsimp only at hk' ⊢
    have hk_le := (hfind_anc p hpL2).choose_spec.1
    have hmin := (hfind_anc p hpL2).choose_spec.2.2
    have hlen : (ancOf p hpL2).length = (hfind_anc p hpL2).choose := by
      simp [ancOf, Nat.min_eq_left hk_le]
    have htk : (ancOf p hpL2).take k' = p.take k' := by
      simp only [ancOf, List.take_take]
      rw [Nat.min_eq_left (by omega)]
    rw [htk]
    exact hmin k' (by omega)
  have hM_ne : ∀ u ∈ M, (pathSet u).Nonempty := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨⟨p, hpL2⟩, _, rfl⟩
    have hne : (pathSet p).Nonempty := Finset.card_pos.mp (by rw [(Finset.mem_filter.mp hpL2).2]; omega)
    exact hne.mono (hpath_mono (List.take_prefix _ p))
  have hM_disj : ∀ u1 ∈ M, ∀ u2 ∈ M, u1 ≠ u2 → Disjoint (pathSet u1) (pathSet u2) := by
    intro u1 hu1 u2 hu2 hne
    apply hdisj_of_diverge
    · intro hpre
      have hlt : u1.length < u2.length := by
        rcases hpre with ⟨suf, rfl⟩
        cases suf with
        | nil => exact absurd (List.append_nil u1).symm hne
        | cons _ _ => simp
      have htake : u2.take u1.length = u1 := by
        rcases hpre with ⟨suf, rfl⟩
        exact List.take_left
      exact hM_min u2 hu2 u1.length hlt (htake.symm ▸ hM_rank u1 hu1)
    · intro hpre
      have hlt : u2.length < u1.length := by
        rcases hpre with ⟨suf, rfl⟩
        cases suf with
        | nil => exact absurd (List.append_nil u2) hne
        | cons _ _ => simp
      have htake : u1.take u2.length = u2 := by
        rcases hpre with ⟨suf, rfl⟩
        exact List.take_left
      exact hM_min u1 hu1 u2.length hlt (htake.symm ▸ hM_rank u2 hu2)
  have hM_card : M.card ≤ 2 ^ t := by
    have hdisj' : (M : Set (List Bool)).PairwiseDisjoint pathSet :=
      fun u1 hu1 u2 hu2 hne => hM_disj u1 hu1 u2 hu2 hne
    have hsum : (M.biUnion pathSet).card = ∑ u ∈ M, (pathSet u).card :=
      Finset.card_biUnion hdisj'
    have heach : ∀ u ∈ M, (pathSet u).card = 2 ^ (m + 1 - t) := by
      intro u hu
      obtain ⟨z0, hz0⟩ := hM_ne u hu
      rw [hpath_card u (hM_memN u hu) z0 hz0, hsub_card, hM_rank u hu]
    rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul] at hsum
    have hle : M.card * 2 ^ (m + 1 - t) ≤ 2 ^ (m + 1) := by
      rw [← hsum, ← hVcard, ← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)
    have hpow : 2 ^ t * 2 ^ (m + 1 - t) = 2 ^ (m + 1) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    have hpos : 0 < 2 ^ (m + 1 - t) := by positivity
    nlinarith
  have hfiber_card : ∀ u ∈ M,
      (L2.attach.filter fun p => ancOf p.1 p.2 = u).card ≤
        2 ^ (m - 2 * t) + 2 ^ ((m + g) / 2) := by
    intro u hu
    obtain ⟨z0, hz0⟩ := hM_ne u hu
    have huN := hM_memN u hu
    let F_u := L2.attach.filter fun p => ancOf p.1 p.2 = u
    have hinj_out : Set.InjOn (fun p : {x // x ∈ L2} => out p.1) (F_u : Set {x // x ∈ L2}) := by
      intro p1 _ p2 _ hout
      dsimp only at hout
      apply Subtype.ext
      by_contra hne
      have hp1NJ := (Finset.mem_filter.mp p1.2).1
      have hp2NJ := (Finset.mem_filter.mp p2.2).1
      have hdisj : Disjoint (pathSet p1.1) (pathSet p2.1) := by
        apply hdisj_of_diverge
        · intro hpre
          rcases hpre with ⟨suf, hsuf⟩
          cases suf with
          | nil => exact hne (by simpa using hsuf)
          | cons b rest =>
            have hlt : p1.1.length < p2.1.length := by rw [← hsuf]; simp
            have htk : p2.1.take p1.1.length = p1.1 := by rw [← hsuf]; exact List.take_left
            have hp1J := take_mem_J_of_strict_prefix hshape (Finset.mem_sdiff.mp hp2NJ).1 p1.1.length hlt
            rw [htk] at hp1J
            exact (Finset.mem_sdiff.mp hp1NJ).2 hp1J
        · intro hpre
          rcases hpre with ⟨suf, hsuf⟩
          cases suf with
          | nil => exact hne (by simpa using hsuf.symm)
          | cons b rest =>
            have hlt : p2.1.length < p1.1.length := by rw [← hsuf]; simp
            have htk : p1.1.take p2.1.length = p2.1 := by rw [← hsuf]; exact List.take_left
            have hp2J := take_mem_J_of_strict_prefix hshape (Finset.mem_sdiff.mp hp1NJ).1 p2.1.length hlt
            rw [htk] at hp2J
            exact (Finset.mem_sdiff.mp hp2NJ).2 hp2J
      have hpair1 : pathSet p1.1 = {((0 : ZMod 2), out p1.1), ((1 : ZMod 2), (out p1.1) ^ (2 ^ s + 1))} := by
        apply Finset.eq_of_subset_of_card_le (hleaf_sub_pair p1.1 hp1NJ)
        rw [(Finset.mem_filter.mp p1.2).2]
        exact Finset.card_le_two
      have hpair2 : pathSet p2.1 = {((0 : ZMod 2), out p2.1), ((1 : ZMod 2), (out p2.1) ^ (2 ^ s + 1))} := by
        apply Finset.eq_of_subset_of_card_le (hleaf_sub_pair p2.1 hp2NJ)
        rw [(Finset.mem_filter.mp p2.2).2]
        exact Finset.card_le_two
      have hm1 : ((0 : ZMod 2), out p1.1) ∈ pathSet p1.1 := by rw [hpair1]; simp
      have hm2 : ((0 : ZMod 2), out p1.1) ∈ pathSet p2.1 := by rw [hpair2, hout]; simp
      exact Finset.disjoint_left.mp hdisj hm1 hm2
    have himg_sub : F_u.image (fun p : {x // x ∈ L2} => out p.1) ⊆
        Finset.univ.filter fun a : F =>
          ((0 : ZMod 2), a) - z0 ∈ kerSub u ∧ ((1 : ZMod 2), a ^ (2 ^ s + 1)) - z0 ∈ kerSub u := by
      intro a ha
      rcases Finset.mem_image.mp ha with ⟨p, hpFu, rfl⟩
      have hanc : ancOf p.1 p.2 = u := (Finset.mem_filter.mp hpFu).2
      have hpNJ := (Finset.mem_filter.mp p.2).1
      have hpair : pathSet p.1 = {((0 : ZMod 2), out p.1), ((1 : ZMod 2), (out p.1) ^ (2 ^ s + 1))} := by
        apply Finset.eq_of_subset_of_card_le (hleaf_sub_pair p.1 hpNJ)
        rw [(Finset.mem_filter.mp p.2).2]
        exact Finset.card_le_two
      have hsub_u : pathSet p.1 ⊆ pathSet u := by
        rw [← hanc]; exact hpath_mono (List.take_prefix _ p.1)
      have hm0 : ((0 : ZMod 2), out p.1) ∈ pathSet u := hsub_u (by rw [hpair]; simp)
      have hm1 : ((1 : ZMod 2), (out p.1) ^ (2 ^ s + 1)) ∈ pathSet u := hsub_u (by rw [hpair]; simp)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hpath_coset u huN z0 hz0 _).mp hm0,
        (hpath_coset u huN z0 hz0 _).mp hm1⟩
    have hpc := pair_count_in_coset hm hcard hodd ht_le (kerSub u) (by rw [hsub_card, hM_rank u hu]) z0
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hpc
    calc F_u.card
        = (F_u.image (fun p : {x // x ∈ L2} => out p.1)).card :=
          (Finset.card_image_of_injOn hinj_out).symm
      _ ≤ (Finset.univ.filter fun a : F =>
            ((0 : ZMod 2), a) - z0 ∈ kerSub u ∧ ((1 : ZMod 2), a ^ (2 ^ s + 1)) - z0 ∈ kerSub u).card :=
          Finset.card_le_card himg_sub
      _ ≤ 2 ^ (m - 2 * t) + 2 ^ ((m + g) / 2) := hpc
  have hL2_bound : L2.card ≤ 2 ^ (m - t) + 2 ^ (t + (m + g) / 2) := by
    have hpart : L2.card = ∑ u ∈ M, (L2.attach.filter fun p => ancOf p.1 p.2 = u).card := by
      rw [← Finset.card_attach (s := L2)]
      exact Finset.card_eq_sum_card_fiberwise (fun p _ => Finset.mem_image.mpr ⟨p, Finset.mem_attach _ _, rfl⟩)
    rw [hpart]
    calc ∑ u ∈ M, (L2.attach.filter fun p => ancOf p.1 p.2 = u).card
        ≤ ∑ _u ∈ M, (2 ^ (m - 2 * t) + 2 ^ ((m + g) / 2)) := Finset.sum_le_sum hfiber_card
      _ = M.card * (2 ^ (m - 2 * t) + 2 ^ ((m + g) / 2)) := by simp
      _ ≤ 2 ^ t * (2 ^ (m - 2 * t) + 2 ^ ((m + g) / 2)) := Nat.mul_le_mul_right _ hM_card
      _ = 2 ^ (m - t) + 2 ^ (t + (m + g) / 2) := by
          rw [mul_add, ← pow_add, ← pow_add]
          congr 2
          omega
  omega

end PEqualNP.Outside.L_pcx_370_aux

theorem PEqualNP.Outside.L_pcx_370 : (let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
      (m s : ℕ), 0 < m → 0 < s → Fintype.card F = 2^m →
    let g := Nat.gcd m s
    Odd (m/g) →
      let t := (m-g)/4
      ∀ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × F) → Bool)
        (out : List Bool → F),
        cert (queries (ZMod 2 × F))
          (fun z a => if z.1 = 0 then z.2 = a else z.2 = a^(2^s+1)) N J q out →
        2^(m+1) ≤ (N \ J).card + 2^(m-t) + 2^(t+(m+g)/2)) :=
  PEqualNP.Outside.L_pcx_370_aux.main_thm
