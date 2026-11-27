import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_616

open Finset MvPolynomial

noncomputable section

abbrev Pl (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

def ex {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ := ∑ i ∈ S, Finsupp.single i 1

theorem ex_apply {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : ex S j = if j ∈ S then 1 else 0 := by
  simp [ex, Finset.sum_apply', Finsupp.single_apply]

theorem ex_le_one {n : ℕ} (S : Finset (Fin n)) (j : Fin n) : ex S j ≤ 1 := by
  rw [ex_apply]; split_ifs <;> omega

theorem ex_inj {n : ℕ} {S T : Finset (Fin n)} (h : ex S = ex T) : S = T := by
  ext j
  have := DFunLike.congr_fun h j
  rw [ex_apply, ex_apply] at this
  by_cases h1 : j ∈ S <;> by_cases h2 : j ∈ T <;> simp_all

theorem ex_degree {n : ℕ} (S : Finset (Fin n)) : (ex S).degree = S.card := by
  simp [ex, map_sum, Finsupp.degree_single]

theorem ex_insert {n : ℕ} {S : Finset (Fin n)} {i : Fin n} (h : i ∉ S) :
    ex (insert i S) = Finsupp.single i 1 + ex S := by
  simp [ex, Finset.sum_insert h]

theorem prodX {n : ℕ} (S : Finset (Fin n)) : ∏ i ∈ S, (X i : Pl n) = monomial (ex S) 1 := by
  rw [ex, monomial_sum_one]
  rfl

theorem coeff_ex_monomial {n : ℕ} (U S : Finset (Fin n)) :
    (monomial (ex S) (1 : ZMod 2) : Pl n).coeff (ex U) = if U = S then 1 else 0 := by
  rw [coeff_monomial]
  by_cases h : U = S
  · simp [h]
  · rw [if_neg (fun h' => h (ex_inj h').symm), if_neg h]

theorem single_add_ex_iff {n : ℕ} (i : Fin n) (S U : Finset (Fin n)) :
    Finsupp.single i 1 + ex S = ex U ↔ i ∉ S ∧ U = insert i S := by
  constructor
  · intro h
    have hi : i ∉ S := by
      intro hi
      have := DFunLike.congr_fun h i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
      have h2 := ex_le_one U i
      rw [ex_apply, if_pos hi] at this
      omega
    refine ⟨hi, ?_⟩
    rw [← ex_insert hi] at h
    exact (ex_inj h).symm
  · rintro ⟨hi, rfl⟩
    rw [ex_insert hi]

theorem coeff_X_mul {n : ℕ} (i : Fin n) (S U : Finset (Fin n)) :
    ((X i : Pl n) * monomial (ex S) 1).coeff (ex U) = if i ∉ S ∧ U = insert i S then 1 else 0 := by
  rw [X, monomial_mul_monomial, coeff_monomial, one_mul]
  by_cases h : i ∉ S ∧ U = insert i S
  · rw [if_pos ((single_add_ex_iff i S U).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((single_add_ex_iff i S U).1 h')), if_neg h]

def lin {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) : Pl n := ∑ j, C (g j i) * X j

def cm {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) (ZMod 2) :=
  Matrix.of fun U S => (∏ i ∈ S, lin g i).coeff (ex U)

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem coeff_sq_mul {n : ℕ} (U : Finset (Fin n)) (k : Fin n) (q : Pl n) :
    ((X k) ^ 2 * q).coeff (ex U) = 0 := by
  rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial', if_neg]
  intro h
  have := h k
  simp only [Finsupp.single_eq_same] at this
  have := ex_le_one U k
  omega

theorem coeff_bind {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (U : Finset (Fin n)) (q : Pl n) :
    (bind₁ (lin g) q).coeff (ex U) = ∑ T, cm g U T * q.coeff (ex T) := by
  induction q using MvPolynomial.induction_on' with
  | monomial u a =>
    by_cases hsq : ∃ k, 2 ≤ u k
    · obtain ⟨k, hk⟩ := hsq
      have e : monomial u a = (X k) ^ 2 * monomial (u - Finsupp.single k 2) a := by
        rw [X_pow_eq_monomial, monomial_mul_monomial, one_mul, add_tsub_cancel_of_le]
        intro j
        by_cases hj : j = k
        · subst hj; simpa using hk
        · simp [Finsupp.single_apply, Ne.symm hj]
      have hr : ∀ T : Finset (Fin n), (monomial u a : Pl n).coeff (ex T) = 0 := by
        intro T
        rw [coeff_monomial, if_neg]
        intro h
        have := ex_le_one T k
        rw [h] at hk
        omega
      simp only [hr, mul_zero, Finset.sum_const_zero]
      rw [e, map_mul, map_pow, bind₁_X_right, lin, sum_pow_char, Finset.sum_mul, coeff_sum]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [mul_pow, mul_assoc, mul_left_comm, coeff_sq_mul]
    · push Not at hsq
      have hu : u = ex u.support := by
        ext j
        rw [ex_apply]
        have := hsq j
        by_cases hj : j ∈ u.support
        · rw [if_pos hj]
          have : u j ≠ 0 := Finsupp.mem_support_iff.1 hj
          omega
        · rw [if_neg hj]
          exact Finsupp.notMem_support_iff.1 hj
      rw [hu]
      set T0 := u.support
      have e : monomial (ex T0) a = C a * ∏ i ∈ T0, (X i : Pl n) := by
        rw [prodX, C_mul_monomial, mul_one]
      rw [e, map_mul, bind₁_C_right, map_prod, coeff_C_mul]
      simp only [bind₁_X_right, coeff_C_mul, prodX, coeff_ex_monomial, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [cm, Matrix.of_apply, mul_comm]
  | add p q hp hq =>
    rw [map_add, MvPolynomial.coeff_add, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    rw [MvPolynomial.coeff_add, mul_add]

theorem lin_mul {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) :
    lin (g * h) i = bind₁ (lin g) (lin h i) := by
  simp only [lin, map_sum, map_mul, bind₁_C_right, bind₁_X_right, Matrix.mul_apply, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem cm_mul {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) : cm (g * h) = cm g * cm h := by
  ext U S
  rw [Matrix.mul_apply]
  simp only [cm, Matrix.of_apply]
  simp_rw [lin_mul]
  rw [← map_prod, coeff_bind]
  rfl

theorem lin_one {n : ℕ} (i : Fin n) : lin (1 : Matrix (Fin n) (Fin n) (ZMod 2)) i = X i := by
  simp [lin, Matrix.one_apply, apply_ite C]

theorem cm_one {n : ℕ} : cm (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  ext U S
  simp only [cm, Matrix.of_apply, lin_one, prodX, coeff_ex_monomial, Matrix.one_apply]

theorem cm_homog {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) (U S : Finset (Fin n))
    (h : U.card ≠ S.card) : cm g U S = 0 := by
  simp only [cm, Matrix.of_apply]
  have hl : ∀ i, (lin g i).IsHomogeneous 1 := fun i =>
    IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _)
  have hp := IsHomogeneous.prod S (lin g) (fun _ => 1) (fun i _ => hl i)
  apply hp.coeff_eq_zero
  rw [ex_degree]
  simpa using h

theorem lin_add {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) (i : Fin n) :
    lin (g + h) i = lin g i + lin h i := by
  simp only [lin, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem sign_smul {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : ZMod 2) :
    (Equiv.Perm.sign σ) • x = x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simp
  · rw [Units.neg_smul, one_smul, ZMod.neg_eq_self_mod_two]

theorem top_coeff {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    cm g univ univ = g.det := by
  simp only [cm, Matrix.of_apply, lin]
  rw [Finset.prod_univ_sum (fun _ => univ) (fun i j => C (g j i) * (X j : Pl n)), coeff_sum]
  have hterm : ∀ f : Fin n → Fin n, (∏ i, C (g (f i) i) * (X (f i) : Pl n)) =
      monomial (∑ i, Finsupp.single (f i) 1) (∏ i, g (f i) i) := by
    intro f
    rw [Finset.prod_mul_distrib, ← map_prod,
      show ∏ i, (X (f i) : Pl n) = monomial (∑ i, Finsupp.single (f i) 1) 1 from
        (monomial_sum_one _ _).symm, C_mul_monomial, mul_one]
  simp_rw [hterm, coeff_monomial]
  rw [Fintype.piFinset_univ, ← Finset.sum_filter, Matrix.det_apply]
  simp_rw [sign_smul]
  symm
  refine Finset.sum_bij (fun σ _ => ⇑σ) ?_ ?_ ?_ ?_
  · intro σ _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact Equiv.sum_comp σ (fun j => Finsupp.single j (1 : ℕ))
  · intro a _ b _ h
    exact Equiv.ext (fun x => congrFun h x)
  · intro f hf
    rw [Finset.mem_filter] at hf
    have hs : Function.Surjective f := by
      intro j
      by_contra hne
      push Not at hne
      have := DFunLike.congr_fun hf.2 j
      rw [ex_apply, if_pos (Finset.mem_univ _), Finset.sum_apply'] at this
      simp [Finsupp.single_apply, hne] at this
    exact ⟨Equiv.ofBijective f (Finite.surjective_iff_bijective.1 hs), Finset.mem_univ _, rfl⟩
  · intro σ _
    rfl

theorem trace_id {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    cm (1 + g) univ univ = ∑ S, cm g S S := by
  simp only [cm, Matrix.of_apply]
  rw [show (∏ i, lin (1 + g) i) = ∏ i, (lin g i + X i) from
    Finset.prod_congr rfl (fun i _ => by rw [lin_add, lin_one, add_comm])]
  rw [Finset.prod_add, Finset.powerset_univ, coeff_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [prodX, coeff_mul_monomial', if_pos, mul_one]
  · congr 1
    ext j
    simp only [Finsupp.tsub_apply, ex_apply]
    by_cases h : j ∈ t <;> simp [h]
  · intro j
    simp only [ex_apply]
    by_cases h : j ∈ t <;> simp [h]

theorem cm_empty {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) : cm g ∅ ∅ = 1 := by
  simp [cm, ex]

/- transvections and permutation matrices -/

def tv {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) (ZMod 2) := Matrix.transvection i j 1

theorem tv_sq {n : ℕ} {i j : Fin n} (h : i ≠ j) : tv i j * tv i j = 1 := by
  have := Matrix.transvection_mul_transvection_same i j h (1 : ZMod 2) 1
  rw [show (1 : ZMod 2) + 1 = 0 from rfl, Matrix.transvection_zero] at this
  exact this

theorem lin_tv {n : ℕ} (i j k : Fin n) : lin (tv i j) k = X k + if k = j then X i else 0 := by
  rw [tv, Matrix.transvection, lin_add, lin_one]
  congr 1
  simp only [lin, Matrix.single, Matrix.of_apply]
  by_cases hk : k = j
  · subst hk
    simp [apply_ite C, ite_mul, Finset.sum_ite_eq]
  · simp [hk, Ne.symm hk]

theorem cm_tv {n : ℕ} {i j : Fin n} (hij : i ≠ j) (U S : Finset (Fin n)) :
    cm (tv i j) U S = (if U = S then 1 else 0) +
      (if j ∈ S ∧ i ∉ S ∧ U = insert i (S.erase j) then 1 else 0) := by
  simp only [cm, Matrix.of_apply]
  simp_rw [lin_tv]
  by_cases hj : j ∈ S
  · rw [← Finset.mul_prod_erase S _ hj, if_pos rfl]
    have : ∏ x ∈ S.erase j, (X x + if x = j then X i else 0 : Pl n) = ∏ x ∈ S.erase j, X x :=
      Finset.prod_congr rfl (fun x hx => by rw [if_neg (Finset.ne_of_mem_erase hx), add_zero])
    rw [this, prodX, add_mul, MvPolynomial.coeff_add, coeff_X_mul, coeff_X_mul,
      Finset.insert_erase hj]
    congr 1
    · simp
    · simp [Finset.mem_erase, hij, hj]
  · have : ∏ x ∈ S, (X x + if x = j then X i else 0 : Pl n) = ∏ x ∈ S, X x :=
      Finset.prod_congr rfl (fun x hx => by
        rw [if_neg (show x ≠ j from fun h => hj (h ▸ hx)), add_zero])
    rw [this, prodX, coeff_ex_monomial]
    simp [hj]

def pm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun l k => if l = σ k then 1 else 0

theorem pm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) : pm σ * pm τ = pm (σ * τ) := by
  ext l m
  rw [Matrix.mul_apply]
  simp [pm, Matrix.of_apply, Equiv.Perm.mul_apply]
  by_cases h : l = σ (τ m) <;> simp [h]

theorem pm_one {n : ℕ} : pm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext l m
  simp [pm, Matrix.of_apply, Matrix.one_apply]
  by_cases h : l = m <;> simp [h]

theorem lin_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : Fin n) : lin (pm σ) k = X (σ k) := by
  simp [lin, pm, apply_ite C, ite_mul, Finset.sum_ite_eq']

theorem cm_pm {n : ℕ} (σ : Equiv.Perm (Fin n)) (U S : Finset (Fin n)) :
    cm (pm σ) U S = if U = S.map σ.toEmbedding then 1 else 0 := by
  simp only [cm, Matrix.of_apply, lin_pm]
  rw [show ∏ k ∈ S, (X (σ k) : Pl n) = ∏ l ∈ S.map σ.toEmbedding, X l from
    (Finset.prod_map S σ.toEmbedding (fun l => (X l : Pl n))).symm, prodX, coeff_ex_monomial]

/- the matrices over K -/

abbrev VV (n : ℕ) := Fin n → ZMod 2

def ιK (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K

def hc (K : Type) [Field K] [CharP K 2] {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) K := (cm g).map (ιK K)

theorem hc_apply (K : Type) [Field K] [CharP K 2] {n : ℕ} (g : Matrix (Fin n) (Fin n) (ZMod 2))
    (U S : Finset (Fin n)) : hc K g U S = ιK K (cm g U S) := rfl

theorem hc_mul (K : Type) [Field K] [CharP K 2] {n : ℕ} (g h : Matrix (Fin n) (Fin n) (ZMod 2)) :
    hc K (g * h) = hc K g * hc K h := by
  rw [hc, cm_mul, Matrix.map_mul]
  rfl

theorem hc_one (K : Type) [Field K] [CharP K 2] {n : ℕ} :
    hc K (1 : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  rw [hc, cm_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem two_K (K : Type) [Field K] [CharP K 2] : (2 : K) = 0 := by
  exact_mod_cast CharP.cast_eq_zero K 2

theorem self_add_self (z : VV n) : z + z = 0 := by
  funext j
  exact (by decide : ∀ t : ZMod 2, t + t = 0) (z j)

theorem parity (K : Type) [Field K] [CharP K 2] {n : ℕ} (N : Matrix (Fin n) (Fin n) (ZMod 2))
    (c : Fin n → ZMod 2) :
    ((((univ : Finset (Fin n → ZMod 2)).filter (fun x => N.mulVec x = c)).card : ℕ) : K) =
      ιK K N.det := by
  by_cases hd : N.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
    have hvk : v k = 1 := (zmod2_cases (v k)).resolve_left hk
    have h2 : ∀ x : Fin n → ZMod 2, x + v + v = x := by
      intro x
      rw [add_assoc, self_add_self, add_zero]
    set F := (univ : Finset (Fin n → ZMod 2)).filter (fun x => N.mulVec x = c)
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (fun x => x k = 0)
    have heq : (F.filter (fun x => x k = 0)).card = (F.filter (fun x => ¬ x k = 0)).card := by
      refine Finset.card_nbij' (fun x => x + v) (fun x => x + v) ?_ ?_ ?_ ?_
      · intro x hx
        simp only [F, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hx ⊢
        refine ⟨by rw [Matrix.mulVec_add, hx.1, hv, add_zero], ?_⟩
        rw [Pi.add_apply, hx.2, zero_add]
        exact hk
      · intro x hx
        simp only [F, Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
          Set.mem_setOf_eq] at hx ⊢
        refine ⟨by rw [Matrix.mulVec_add, hx.1, hv, add_zero], ?_⟩
        have : x k = 1 := (zmod2_cases _).resolve_left hx.2
        rw [Pi.add_apply, this, hvk]
        rfl
      · intro x _
        exact h2 x
      · intro x _
        exact h2 x
    rw [hd, map_zero, ← hsplit, heq, ← two_mul, Nat.cast_mul, Nat.cast_ofNat, two_K, zero_mul]
  · have hu : IsUnit N.det := isUnit_iff_ne_zero.2 hd
    have e : (univ : Finset (Fin n → ZMod 2)).filter (fun x => N.mulVec x = c) = {N⁻¹.mulVec c} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      · intro h
        rw [h, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
    have h1 : N.det = 1 := (zmod2_cases _).resolve_left hd
    rw [e, Finset.card_singleton, h1, map_one, Nat.cast_one]

def mat {n : ℕ} (g : VV n ≃ₗ[ZMod 2] VV n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  LinearMap.toMatrix' (g : VV n →ₗ[ZMod 2] VV n)

theorem mat_trans {n : ℕ} (g h : VV n ≃ₗ[ZMod 2] VV n) : mat (h.trans g) = mat g * mat h := by
  rw [mat, LinearEquiv.coe_trans, LinearMap.toMatrix'_comp]
  rfl

theorem det_mat {n : ℕ} (g : VV n ≃ₗ[ZMod 2] VV n) : (mat g).det = 1 := by
  have h : mat g * mat g.symm = 1 := by
    rw [← mat_trans, LinearEquiv.symm_trans_self, mat]
    exact LinearMap.toMatrix'_id
  have : (mat g).det * (mat g.symm).det = 1 := by rw [← Matrix.det_mul, h, Matrix.det_one]
  exact (zmod2_cases _).resolve_left (left_ne_zero_of_mul_eq_one this)

def Alg (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    Submodule K (Matrix (Finset (Fin n)) (Finset (Fin n)) K) :=
  Submodule.span K (Set.range fun g : VV n ≃ₗ[ZMod 2] VV n => hc K (mat g))

theorem mem_of_inv (K : Type) [Field K] [CharP K 2] {n : ℕ} (M M' : Matrix (Fin n) (Fin n) (ZMod 2))
    (h1 : M * M' = 1) (h2 : M' * M = 1) : hc K M ∈ Alg K n := by
  apply Submodule.subset_span
  refine ⟨Matrix.toLin'OfInv h2 h1, ?_⟩
  simp only [mat]
  congr 1
  have : ((Matrix.toLin'OfInv h2 h1 : VV n ≃ₗ[ZMod 2] VV n) : VV n →ₗ[ZMod 2] VV n) =
      Matrix.toLin' M := LinearMap.ext fun x => rfl
  rw [this, LinearMap.toMatrix'_toLin']

theorem one_mem_alg (K : Type) [Field K] [CharP K 2] (n : ℕ) :
    (1 : Matrix (Finset (Fin n)) (Finset (Fin n)) K) ∈ Alg K n := by
  rw [← hc_one K]
  exact mem_of_inv K 1 1 (mul_one 1) (mul_one 1)

theorem alg_mul (K : Type) [Field K] [CharP K 2] {n : ℕ}
    {x y : Matrix (Finset (Fin n)) (Finset (Fin n)) K} (hx : x ∈ Alg K n) (hy : y ∈ Alg K n) :
    x * y ∈ Alg K n := by
  have := Submodule.mul_mem_mul hx hy
  rw [Alg, Submodule.span_mul_span] at this
  refine Submodule.span_le.2 ?_ this
  rintro _ ⟨a, ⟨g, rfl⟩, b, ⟨h, rfl⟩, rfl⟩
  apply Submodule.subset_span
  exact ⟨h.trans g, by simp only; rw [mat_trans, hc_mul]⟩

def Nm (K : Type) [Field K] [CharP K 2] {n : ℕ} (i j : Fin n) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) K := hc K (tv i j) - 1

theorem Nm_mem (K : Type) [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Nm K i j ∈ Alg K n :=
  Submodule.sub_mem _ (mem_of_inv K _ _ (tv_sq h) (tv_sq h)) (one_mem_alg K n)

theorem Nm_apply (K : Type) [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} (h : i ≠ j)
    (U S : Finset (Fin n)) :
    Nm K i j U S = if j ∈ S ∧ i ∉ S ∧ U = insert i (S.erase j) then 1 else 0 := by
  rw [Nm, Matrix.sub_apply, hc_apply, cm_tv h, map_add, Matrix.one_apply]
  by_cases h1 : U = S <;> by_cases h2 : j ∈ S ∧ i ∉ S ∧ U = insert i (S.erase j) <;>
    simp [h1, h2]

theorem NN (K : Type) [Field K] [CharP K 2] {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Nm K j i * Nm K i j =
      Matrix.diagonal (fun S => if j ∈ S ∧ i ∉ S then (1 : K) else 0) := by
  ext U S
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  simp_rw [Nm_apply K hij, Nm_apply K (Ne.symm hij)]
  by_cases hS : j ∈ S ∧ i ∉ S
  · rw [Finset.sum_eq_single (insert i (S.erase j))]
    · have h1 : i ∈ insert i (S.erase j) := Finset.mem_insert_self _ _
      have h2 : j ∉ insert i (S.erase j) := by simp [Ne.symm hij]
      have h3 : (insert i (S.erase j)).erase i = S.erase j :=
        Finset.erase_insert (by simp [hS.2])
      rw [h3, Finset.insert_erase hS.1]
      by_cases hU : U = S
      · subst hU
        simp [h1, h2, hS]
      · simp [h1, h2, hS, hU]
    · intro V _ hV
      simp [hV]
    · simp
  · rw [Finset.sum_eq_zero]
    · by_cases hU : U = S
      · subst hU
        simp [hS]
      · simp [hU]
    · intro V _
      have : ¬ (j ∈ S ∧ i ∉ S ∧ V = insert i (S.erase j)) := fun h => hS ⟨h.1, h.2.1⟩
      rw [if_neg this, mul_zero]

theorem diag_prod (K : Type) [Field K] [CharP K 2] {n : ℕ} (Q : Finset (Fin n × Fin n))
    (hQ : ∀ q ∈ Q, q.1 ≠ q.2) :
    Matrix.diagonal (fun S => ∏ q ∈ Q, if q.1 ∈ S ∧ q.2 ∉ S then (1 : K) else 0) ∈ Alg K n := by
  induction Q using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [Matrix.diagonal_one]
    exact one_mem_alg K n
  | @insert q Q hq ih =>
    have hQ' : ∀ q' ∈ Q, q'.1 ≠ q'.2 := fun q' h => hQ q' (Finset.mem_insert_of_mem h)
    simp_rw [Finset.prod_insert hq]
    rw [← Matrix.diagonal_mul_diagonal]
    refine alg_mul K ?_ (ih hQ')
    rw [← NN K (Ne.symm (hQ q (Finset.mem_insert_self _ _)))]
    exact alg_mul K (Nm_mem K (hQ q (Finset.mem_insert_self _ _)))
      (Nm_mem K (Ne.symm (hQ q (Finset.mem_insert_self _ _))))

theorem diag_unit (K : Type) [Field K] [CharP K 2] {n : ℕ} (S0 : Finset (Fin n))
    (h1 : S0.Nonempty) (h2 : S0ᶜ.Nonempty) :
    Matrix.diagonal (fun S => if S = S0 then (1 : K) else 0) ∈ Alg K n := by
  have e : (fun S => if S = S0 then (1 : K) else 0) =
      fun S => ∏ q ∈ S0 ×ˢ S0ᶜ, if q.1 ∈ S ∧ q.2 ∉ S then (1 : K) else 0 := by
    funext S
    rw [Finset.prod_ite_zero, Finset.prod_const_one]
    by_cases hS : S = S0
    · subst hS
      rw [if_pos rfl, if_pos]
      intro q hq
      rw [Finset.mem_product, Finset.mem_compl] at hq
      exact hq
    · rw [if_neg hS, if_neg]
      intro hall
      apply hS
      ext x
      constructor
      · intro hx
        by_contra hx0
        obtain ⟨j, hj⟩ := h1
        exact (hall (j, x) (Finset.mem_product.2 ⟨hj, Finset.mem_compl.2 hx0⟩)).2 hx
      · intro hx
        obtain ⟨i, hi⟩ := h2
        exact (hall (x, i) (Finset.mem_product.2 ⟨hx, hi⟩)).1
  rw [e]
  refine diag_prod K _ (fun q hq => ?_)
  rw [Finset.mem_product, Finset.mem_compl] at hq
  intro h
  exact hq.2 (h ▸ hq.1)

theorem exists_perm_map {n : ℕ} (S T : Finset (Fin n)) (h : S.card = T.card) :
    ∃ σ : Equiv.Perm (Fin n), S.map σ.toEmbedding = T := by
  have hc : Fintype.card {x // x ∈ S} = Fintype.card {x // x ∈ T} := by
    simp [Fintype.card_coe, h]
  let e : {x // x ∈ S} ≃ {x // x ∈ T} := Fintype.equivOfCardEq hc
  refine ⟨Equiv.extendSubtype e, ?_⟩
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact Equiv.extendSubtype_mem e x hx
  · rw [Finset.card_map, h]

theorem unit_mem (K : Type) [Field K] [CharP K 2] {n : ℕ} (S0 T : Finset (Fin n))
    (h1 : S0.Nonempty) (h2 : S0ᶜ.Nonempty) (h : S0.card = T.card) :
    (Matrix.of fun U S => if U = T ∧ S = S0 then (1 : K) else 0) ∈ Alg K n := by
  obtain ⟨σ, hσ⟩ := exists_perm_map S0 T h
  have hp : hc K (pm σ) ∈ Alg K n :=
    mem_of_inv K (pm σ) (pm σ⁻¹) (by rw [pm_mul, mul_inv_cancel, pm_one])
      (by rw [pm_mul, inv_mul_cancel, pm_one])
  have := alg_mul K hp (diag_unit K S0 h1 h2)
  convert this using 1
  ext U S
  rw [Matrix.mul_diagonal, hc_apply, cm_pm, Matrix.of_apply]
  by_cases hS : S = S0
  · subst hS
    rw [hσ]
    by_cases hU : U = T <;> simp [hU]
  · simp [hS]

/- the index set -/

abbrev pr (n : ℕ) (a : Finset (Fin n) × Finset (Fin n)) : Prop :=
  a.1.card = a.2.card ∧ 0 < a.1.card ∧ a.1.card < n

abbrev Ix (n : ℕ) := {a : Finset (Fin n) × Finset (Fin n) // pr n a}

theorem card_Y (n : ℕ) :
    ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
      (fun a => a.1.card = a.2.card)).card = Nat.choose (2 * n) n := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have h : ∀ S : Finset (Fin n),
      (∑ T : Finset (Fin n), if S.card = T.card then 1 else 0) = n.choose S.card := by
    intro S
    rw [← Finset.card_filter]
    have : (univ : Finset (Finset (Fin n))).filter (fun T => S.card = T.card) =
        Finset.powersetCard S.card univ := by
      ext T
      simp [Finset.mem_powersetCard, eq_comm]
    rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  simp_rw [h]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card, Finset.card_univ, Fintype.card_fin,
    ← Nat.sum_range_choose_sq]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [smul_eq_mul, sq]

theorem card_Ix {n : ℕ} (hn : 0 < n) : Fintype.card (Ix n) = Nat.choose (2 * n) n - 2 := by
  rw [Fintype.card_subtype]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun a => a.1.card = a.2.card))
    (fun a => 0 < a.1.card ∧ a.1.card < n)
  rw [Finset.filter_filter, card_Y] at hsplit
  have e2 : ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter
      (fun a => a.1.card = a.2.card)).filter (fun a => ¬ (0 < a.1.card ∧ a.1.card < n)) =
      {(∅, ∅), (univ, univ)} := by
    ext ⟨S, T⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_and, not_lt]
    constructor
    · rintro ⟨hST, h⟩
      by_cases h0 : S.card = 0
      · left
        have hT : T.card = 0 := hST ▸ h0
        exact ⟨Finset.card_eq_zero.1 h0, Finset.card_eq_zero.1 hT⟩
      · right
        have hle : S.card ≤ n := by simpa using S.card_le_univ
        have hS : S.card = n := le_antisymm hle (h (Nat.pos_of_ne_zero h0))
        have hT : T.card = n := hST ▸ hS
        exact ⟨Finset.eq_univ_of_card S (by simp [hS]), Finset.eq_univ_of_card T (by simp [hT])⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · simp
      · simp
  have hne : ((∅ : Finset (Fin n)), (∅ : Finset (Fin n))) ≠ (univ, univ) := by
    intro h
    have := congrArg (fun a => a.1.card) h
    simp at this
    omega
  rw [e2, Finset.card_pair hne] at hsplit
  have e3 : ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun x => pr n x)).card =
      ((univ : Finset (Finset (Fin n) × Finset (Fin n))).filter (fun a =>
        a.1.card = a.2.card ∧ 0 < a.1.card ∧ a.1.card < n)).card := rfl
  rw [e3]
  omega

theorem split_sum (K : Type) [Field K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (F : Finset (Fin n) → Finset (Fin n) → K)
    (hz : ∀ S T, S.card ≠ T.card → F S T = 0) (h0 : F ∅ ∅ = 1) (h1 : F univ univ = 1) :
    ∑ S, ∑ T, F S T = ∑ a : Ix n, F a.1.1 a.1.2 := by
  rw [← Fintype.sum_prod_type' F, ← Fintype.sum_subtype_add_sum_subtype (pr n) (fun a => F a.1 a.2)]
  have hz2 : ∑ a : {a // ¬ pr n a}, F a.1.1 a.1.2 = 0 := by
    have ha : ¬ pr n (∅, ∅) := by simp [pr]
    have hb : ¬ pr n (univ, univ) := by simp [pr]
    rw [Fintype.sum_eq_add ⟨(∅, ∅), ha⟩ ⟨(univ, univ), hb⟩]
    · simp only
      rw [h0, h1, one_add_one_eq_two, two_K]
    · intro h
      have := congrArg (fun x : {a // ¬ pr n a} => x.1.1.card) h
      simp at this
      omega
    · rintro ⟨⟨S, T⟩, hST⟩ ⟨hna, hnb⟩
      by_cases hc : S.card = T.card
      · exfalso
        simp only [pr, not_and, not_lt] at hST
        by_cases h0' : S.card = 0
        · apply hna
          have hT : T.card = 0 := hc ▸ h0'
          rw [Finset.card_eq_zero] at h0' hT
          subst h0'
          subst hT
          rfl
        · apply hnb
          have hle : S.card ≤ n := by simpa using S.card_le_univ
          have hS : S.card = n := le_antisymm hle (hST hc (Nat.pos_of_ne_zero h0'))
          have hT : T.card = n := hc ▸ hS
          have e1 := Finset.eq_univ_of_card S (by simp [hS])
          have e2 := Finset.eq_univ_of_card T (by simp [hT])
          subst e1
          subst e2
          rfl
      · exact hz S T hc
  rw [hz2, add_zero]

theorem key_iff {n : ℕ} (a b x : VV n) : a + b = x ↔ x + a = b := by
  constructor
  · intro h
    rw [← h, add_comm a b, add_assoc, self_add_self, add_zero]
  · intro h
    rw [← h, add_comm x a, ← add_assoc, self_add_self, zero_add]

theorem fix_formula (K : Type) [Field K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (p r : (VV n ≃ₗ[ZMod 2] VV n) × VV n) :
    ((((univ : Finset (VV n)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x)).card : ℕ) : K) =
      ∑ a : Ix n, hc K (mat p.1) a.1.2 a.1.1 * hc K (mat r.1) a.1.1 a.1.2 := by
  have hfilt : (univ : Finset (VV n)).filter (fun x => r.1 (p.1 x + p.2) + r.2 = x) =
      univ.filter (fun x => (1 + mat r.1 * mat p.1).mulVec x = r.1 p.2 + r.2) := by
    apply Finset.filter_congr
    intro x _
    have hm : (mat r.1 * mat p.1).mulVec x = r.1 (p.1 x) := by
      rw [← Matrix.mulVec_mulVec, mat, mat, LinearMap.toMatrix'_mulVec,
        LinearMap.toMatrix'_mulVec]
      rfl
    rw [Matrix.add_mulVec, Matrix.one_mulVec, hm, map_add, add_assoc]
    exact key_iff _ _ _
  rw [hfilt, parity K, ← top_coeff, trace_id, map_sum]
  have : ∀ S : Finset (Fin n), ιK K (cm (mat r.1 * mat p.1) S S) =
      ∑ T, hc K (mat r.1) S T * hc K (mat p.1) T S := by
    intro S
    rw [cm_mul, Matrix.mul_apply, map_sum]
    simp only [map_mul, hc_apply]
  simp_rw [this]
  rw [split_sum K hn (fun S T => hc K (mat r.1) S T * hc K (mat p.1) T S)]
  · exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  · intro S T h
    rw [hc_apply, cm_homog _ _ _ h, map_zero, zero_mul]
  · rw [hc_apply, hc_apply, cm_empty, cm_empty, map_one, mul_one]
  · rw [hc_apply, hc_apply, top_coeff, top_coeff, det_mat, det_mat, map_one, mul_one]

/- the rank argument -/

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (A : Matrix ι (Fin d) K) (B : Matrix (Fin d) ι K) (h : A * B = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

theorem pad {K : Type} [Field K] {ι : Type} [Fintype ι] {α β : Type} (d : ℕ)
    (hd : Fintype.card ι ≤ d) (a : α → ι → K) (b : β → ι → K) :
    ∃ (A : α → Fin d → K) (B : β → Fin d → K),
      ∀ p q, ∑ σ, a p σ * b q σ = ∑ j : Fin d, A p j * B q j := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin d) (by simpa using hd)
  refine ⟨fun p => Function.extend e (a p) 0, fun q => Function.extend e (b q) 0, fun p q => ?_⟩
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    have hj' : ¬∃ x, e x = j := by simpa [Set.mem_range] using hj
    dsimp only
    rw [Function.extend_apply' _ _ _ hj']
    simp
  · intro σ
    simp [e.injective.extend_apply]

theorem main_iff {K : Type} [Field K] {P : Type} [Fintype P] {ι : Type} [Fintype ι]
    [DecidableEq ι] (d : ℕ) (fx : P → P → K)
    (u w : P → ι → K)
    (hfix : ∀ p r : P, fx p r = ∑ a, u p a * w r a)
    (hu : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0)
    (hw : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * w p β = if β = a then 1 else 0) :
    (∃ (A B : P → Fin d → K), ∀ p r, fx p r = ∑ j : Fin d, A p j * B r j) ↔
      Fintype.card ι ≤ d := by
  constructor
  · rintro ⟨A, B, h⟩
    choose c hc using hu
    choose e he using hw
    have hM : (Matrix.of fun (a : ι) (j : Fin d) => ∑ p, c a p * A p j) *
        (Matrix.of fun (j : Fin d) (β : ι) => ∑ r, e β r * B r j) = 1 := by
      ext a β
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      calc ∑ j, (∑ p, c a p * A p j) * (∑ r, e β r * B r j)
          = ∑ p, ∑ r, c a p * e β r * ∑ j, A p j * B r j := by
            simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => ?_))
            ring
        _ = ∑ p, ∑ r, c a p * e β r * ∑ g, u p g * w r g := by
            simp_rw [← h, hfix]
        _ = ∑ g, (∑ p, c a p * u p g) * (∑ r, e β r * w r g) := by
            simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
            calc ∑ p, ∑ r, ∑ g, c a p * e β r * (u p g * w r g)
                = ∑ p, ∑ g, ∑ r, c a p * e β r * (u p g * w r g) :=
                  Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
              _ = ∑ g, ∑ p, ∑ r, c a p * e β r * (u p g * w r g) := Finset.sum_comm
              _ = _ := by
                  refine Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun p _ =>
                    Finset.sum_congr rfl (fun r _ => ?_)))
                  ring
        _ = if a = β then 1 else 0 := by
            simp_rw [hc, he]
            simp [eq_comm]
    exact rank_bound d _ _ hM
  · intro hd
    obtain ⟨A, B, hAB⟩ := pad (K := K) d hd u w
    exact ⟨A, B, fun p r => by rw [hfix, hAB]⟩

theorem toFun {K : Type} [Field K] {P ι : Type} [Fintype P] [DecidableEq ι] (u : P → ι → K)
    (a : ι) (h : (Pi.single a 1 : ι → K) ∈ Submodule.span K (Set.range u)) :
    ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 h
  refine ⟨c, fun β => ?_⟩
  have := congrFun hc β
  simpa [Finset.sum_apply, Pi.single_apply] using this

theorem transfer {K : Type} [Field K] {P ι : Type} [Fintype P] [DecidableEq ι] (u : P → ι → K)
    (σ : ι ≃ ι) (h : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0) :
    ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p (σ β) = if β = a then 1 else 0 := by
  intro a
  obtain ⟨c, hc⟩ := h (σ a)
  exact ⟨c, fun β => by rw [hc]; simp [σ.injective.eq_iff]⟩

def piM (K : Type) [Field K] (n : ℕ) :
    Matrix (Finset (Fin n)) (Finset (Fin n)) K →ₗ[K] (Ix n → K) where
  toFun M a := M a.1.2 a.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem span_u (K : Type) [Field K] [CharP K 2] {n : ℕ} (a : Ix n) :
    (Pi.single a 1 : Ix n → K) ∈ Submodule.span K (Set.range
      (fun p : (VV n ≃ₗ[ZMod 2] VV n) × VV n => fun b : Ix n => hc K (mat p.1) b.1.2 b.1.1)) := by
  obtain ⟨⟨S0, T⟩, hc0, hpos, hlt⟩ := a
  have h1 : S0.Nonempty := Finset.card_pos.1 hpos
  have h2 : S0ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    simp only at hlt
    omega
  have hE := unit_mem K S0 T h1 h2 hc0
  have hpi : piM K n (Matrix.of fun U S => if U = T ∧ S = S0 then (1 : K) else 0) =
      Pi.single ⟨(S0, T), hc0, hpos, hlt⟩ 1 := by
    funext b
    obtain ⟨⟨S', T'⟩, hb⟩ := b
    show (if T' = T ∧ S' = S0 then (1 : K) else 0) = _
    rw [Pi.single_apply]
    by_cases hS : S' = S0 <;> by_cases hT : T' = T
    · subst hS
      subst hT
      simp
    · simp [hT]
    · simp [hS]
    · simp [hS]
  rw [← hpi]
  have hle : Submodule.map (piM K n) (Alg K n) ≤ Submodule.span K (Set.range
      (fun p : (VV n ≃ₗ[ZMod 2] VV n) × VV n => fun b : Ix n => hc K (mat p.1) b.1.2 b.1.1)) := by
    rw [Alg, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨(g, 0), rfl⟩
  exact hle (Submodule.mem_map_of_mem hE)

def sw (n : ℕ) : Ix n ≃ Ix n where
  toFun a := ⟨(a.1.2, a.1.1), a.2.1.symm, by rw [← a.2.1]; exact a.2.2.1,
    by rw [← a.2.1]; exact a.2.2.2⟩
  invFun a := ⟨(a.1.2, a.1.1), a.2.1.symm, by rw [← a.2.1]; exact a.2.2.1,
    by rw [← a.2.1]; exact a.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- generic fold helpers -/

theorem fold_congr {S : Type} {t : ℕ} (l : List (Fin t)) (g g' : Fin t → S → S)
    (h : ∀ x ∈ l, g x = g' x) (init : S) :
    l.foldl (fun cur st => g st cur) init = l.foldl (fun cur st => g' st cur) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy => h y (by simp [hy])) _

theorem fold_lin {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {t : ℕ}
    (l : List (Fin t)) (f : Fin t → V →ₗ[K] V) :
    ∃ L : V →ₗ[K] V, ∀ v, l.foldl (fun cur st => f st cur) v = L v := by
  induction l with
  | nil => exact ⟨LinearMap.id, fun v => rfl⟩
  | cons x l ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L ∘ₗ f x, fun v => by simp only [List.foldl_cons]; rw [hL]; rfl⟩

theorem mem_take_lt {t i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).take i) : x.val < i := by
  obtain ⟨n, hn, hx⟩ := List.mem_take_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show n < i
  omega

theorem mem_drop_ge {t i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).drop i) : i ≤ x.val := by
  obtain ⟨n, hn, hx⟩ := List.mem_drop_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show i ≤ i + n
  omega

theorem fold_eq {X : Type} (f : ℕ → X → X) (g : ℕ → X) (hs : ∀ t, g (t + 1) = f t (g t))
    (n : ℕ) : (List.finRange n).foldl (fun v i => f i.val v) (g 0) = g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [Fin.coe_castSucc, ih, List.foldl_cons, List.foldl_nil, Fin.val_last, hs]

/- step matrices -/

abbrev Ctl (b : ℕ) := (Fin b → ZMod 2) × ZMod 2

def ev {b : ℕ} (i : Fin (b + 1)) : VV (b + 1) := fun j => if i = j then 1 else 0

def ee (b t : ℕ) : VV (b + 1) := if h : t < b + 1 then ev ⟨t, h⟩ else 0

def Sh (b : ℕ) (lam : Fin (b + 1) → ZMod 2) : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
  Matrix.of fun k l => if k.val < b then (if l.val = k.val + 1 then 1 else 0) else lam l

def Am (b : ℕ) (c : Fin b → ZMod 2) : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
  Sh b (Fin.cons 1 c)

theorem sh_mul {b : ℕ} (lam : Fin (b + 1) → ZMod 2)
    (W : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k j : Fin (b + 1)) :
    (Sh b lam * W) k j =
      if h : k.val < b then W ⟨k.val + 1, by omega⟩ j else ∑ l, lam l * W l j := by
  rw [Matrix.mul_apply]
  simp only [Sh, Matrix.of_apply]
  by_cases h : k.val < b
  · rw [dif_pos h]
    simp only [h, ↓reduceIte, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h'
      exact hl (Fin.ext h')
    · simp
  · rw [dif_neg h]
    simp only [h, ↓reduceIte]

theorem sh_mulVec {b : ℕ} (lam : Fin (b + 1) → ZMod 2) (s : VV (b + 1)) (k : Fin (b + 1)) :
    (Sh b lam).mulVec s k =
      if h : k.val < b then s ⟨k.val + 1, by omega⟩ else ∑ l, lam l * s l := by
  simp only [Matrix.mulVec, dotProduct, Sh, Matrix.of_apply]
  by_cases h : k.val < b
  · rw [dif_pos h]
    simp only [h, ↓reduceIte, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h'
      exact hl (Fin.ext h')
    · simp
  · rw [dif_neg h]
    simp only [h, ↓reduceIte]

def bias (b : ℕ) (e : ZMod 2) : VV (b + 1) := fun k => if k.val < b then 0 else e

def tf (b : ℕ) (C : Ctl b) (s : VV (b + 1)) : VV (b + 1) := (Am b C.1).mulVec s + bias b C.2

theorem tf_lt {b : ℕ} (C : Ctl b) (s : VV (b + 1)) (k : Fin (b + 1)) (h : k.val < b) :
    tf b C s k = s ⟨k.val + 1, by omega⟩ := by
  simp only [tf, Pi.add_apply, Am, sh_mulVec, bias, h, ↓reduceIte, ↓reduceDIte, add_zero]

theorem tf_last {b : ℕ} (C : Ctl b) (s : VV (b + 1)) :
    tf b C s (Fin.last b) = s 0 + C.2 + ∑ j : Fin b, C.1 j * s j.succ := by
  have h : ¬ (Fin.last b).val < b := by simp
  simp only [tf, Pi.add_apply, Am, sh_mulVec, bias, h, ↓reduceIte, ↓reduceDIte]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
  ring

theorem det_am {b : ℕ} (c : Fin b → ZMod 2) : (Am b c).det = 1 := by
  refine (zmod2_cases _).resolve_left ?_
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 : ∀ k : Fin (b + 1), 0 < k.val → v k = 0 := by
    intro k hk
    have := congrFun hv ⟨k.val - 1, by omega⟩
    rw [Am, sh_mulVec, dif_pos (show k.val - 1 < b by omega)] at this
    have e : ∀ y : Fin (b + 1), y.val = k.val → v y = v k := fun y hy => by rw [Fin.ext hy]
    rw [e _ (by simp only; omega)] at this
    exact this
  have h0 : v 0 = 0 := by
    have := congrFun hv (Fin.last b)
    rw [Am, sh_mulVec, dif_neg (by simp), Fin.sum_univ_succ] at this
    simp only [Fin.cons_zero, one_mul, Pi.zero_apply] at this
    rwa [Finset.sum_eq_zero (fun j _ => by rw [h1 j.succ (by simp), mul_zero]), add_zero] at this
  apply hv0
  funext k
  by_cases hk : k.val = 0
  · rw [show k = 0 from Fin.ext hk]
    exact h0
  · exact h1 k (Nat.pos_of_ne_zero hk)

def Lp (b : ℕ) (F : ℕ → Fin b → ZMod 2) : ℕ → Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)
  | 0 => 1
  | t + 1 => Am b (F t) * Lp b F t

theorem det_lp (b : ℕ) (F : ℕ → Fin b → ZMod 2) (t : ℕ) : (Lp b F t).det = 1 := by
  induction t with
  | zero => exact Matrix.det_one
  | succ t ih =>
    show (Am b (F t) * Lp b F t).det = 1
    rw [Matrix.det_mul, det_am, ih, one_mul]

theorem lp_congr (b : ℕ) (F G : ℕ → Fin b → ZMod 2) (p : ℕ) (h : ∀ t < p, F t = G t) :
    Lp b F p = Lp b G p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    show Am b (F p) * Lp b F p = Am b (G p) * Lp b G p
    rw [h p (by omega), ih (fun t ht => h t (by omega))]

theorem lp_add (b : ℕ) (F : ℕ → Fin b → ZMod 2) (p q : ℕ) :
    Lp b F (p + q) = Lp b (fun t => F (p + t)) q * Lp b F p := by
  induction q with
  | zero =>
    show Lp b F p = 1 * Lp b F p
    rw [one_mul]
  | succ q ih =>
    show Am b (F (p + q)) * Lp b F (p + q) = (Am b (F (p + q)) * Lp b (fun t => F (p + t)) q) * Lp b F p
    rw [ih, Matrix.mul_assoc]

/- orbits and the count -/

def orb (b : ℕ) (F : ℕ → Ctl b) (s : VV (b + 1)) : ℕ → VV (b + 1)
  | 0 => s
  | t + 1 => tf b (F t) (orb b F s t)

def cp (b : ℕ) (F : ℕ → Ctl b) : ℕ → VV (b + 1)
  | 0 => 0
  | t + 1 => (Am b (F t).1).mulVec (cp b F t) + bias b (F t).2

theorem orb_eq (b : ℕ) (F : ℕ → Ctl b) (s : VV (b + 1)) (t : ℕ) :
    orb b F s t = (Lp b (fun t => (F t).1) t).mulVec s + cp b F t := by
  induction t with
  | zero =>
    show s = (1 : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)).mulVec s + 0
    rw [Matrix.one_mulVec, add_zero]
  | succ t ih =>
    show tf b (F t) (orb b F s t) = (Am b (F t).1 * Lp b (fun t => (F t).1) t).mulVec s +
      ((Am b (F t).1).mulVec (cp b F t) + bias b (F t).2)
    rw [ih, tf, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

abbrev site (a t : ℕ) : Fin (a + 1) := Fin.ofNat (a + 1) t

theorem site_val (a t : ℕ) : (site a t).val = t % (a + 1) := Fin.val_ofNat _ _

theorem site_eq {a p q : ℕ} (h : p % (a + 1) = q % (a + 1)) : site a p = site a q :=
  Fin.ext (by rw [site_val, site_val, h])

theorem site_fin (a : ℕ) (i : Fin (a + 1)) : site a i.val = i := Fin.ofNat_val_eq_self i

abbrev cst (a b : ℕ) (C : Fin (a + 1) → Ctl b) (x : Fin (a + 1) → ZMod 2) (i : Fin (a + 1)) :
    Prop :=
  x (Fin.ofNat (a + 1) (i.val + (b + 1))) = x i + (C i).2 +
    ∑ j : Fin b, (C i).1 j * x (Fin.ofNat (a + 1) (i.val + 1 + j.val))

def cnt (a b : ℕ) (C : Fin (a + 1) → Ctl b) : ℕ :=
  ((Finset.univ : Finset (Fin (a + 1) → ZMod 2)).filter (fun x =>
    ∀ i : Fin (a + 1), x (Fin.ofNat (a + 1) (i.val + (b + 1))) = x i + (C i).2 +
      ∑ j : Fin b, (C i).1 j * x (Fin.ofNat (a + 1) (i.val + 1 + j.val)))).card

def win (a b : ℕ) (x : Fin (a + 1) → ZMod 2) (t : ℕ) : VV (b + 1) :=
  fun k => x (site a (t + k.val))

theorem win_mod (a b : ℕ) (x : Fin (a + 1) → ZMod 2) (p q : ℕ) (h : p % (a + 1) = q % (a + 1)) :
    win a b x p = win a b x q := by
  funext k
  simp only [win]
  rw [site_eq (a := a) (p := p + k.val) (q := q + k.val)]
  rw [Nat.add_mod, h, ← Nat.add_mod]

theorem win_step (a b : ℕ) (C : Fin (a + 1) → Ctl b) (x : Fin (a + 1) → ZMod 2)
    (i : Fin (a + 1)) :
    cst a b C x i ↔ win a b x (i.val + 1) = tf b (C i) (win a b x i.val) := by
  have hlow : ∀ k : Fin (b + 1), k.val < b →
      win a b x (i.val + 1) k = tf b (C i) (win a b x i.val) k := by
    intro k hk
    rw [tf_lt _ _ _ hk]
    simp only [win]
    rw [show i.val + 1 + k.val = i.val + (k.val + 1) by omega]
  have hl1 : win a b x (i.val + 1) (Fin.last b) = x (Fin.ofNat (a + 1) (i.val + (b + 1))) := by
    simp only [win, Fin.val_last]
    rw [show i.val + 1 + b = i.val + (b + 1) by omega]
  have hl2 : tf b (C i) (win a b x i.val) (Fin.last b) =
      x i + (C i).2 + ∑ j : Fin b, (C i).1 j * x (Fin.ofNat (a + 1) (i.val + 1 + j.val)) := by
    rw [tf_last]
    simp only [win, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    rw [site_fin]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [show i.val + (j.val + 1) = i.val + 1 + j.val by omega]
  constructor
  · intro h
    funext k
    by_cases hk : k.val < b
    · exact hlow k hk
    · rw [show k = Fin.last b from Fin.ext (by simp; omega), hl1, hl2]
      exact h
  · intro h
    have := congrFun h (Fin.last b)
    rw [hl1, hl2] at this
    exact this

def Cn (a b : ℕ) (C : Fin (a + 1) → Ctl b) (t : ℕ) : Ctl b := C (site a t)

theorem sol_step (a b : ℕ) (C : Fin (a + 1) → Ctl b) (x : Fin (a + 1) → ZMod 2)
    (hx : ∀ i, cst a b C x i) (t : ℕ) :
    win a b x (t + 1) = tf b (Cn a b C t) (win a b x t) := by
  have h := (win_step a b C x (site a t)).1 (hx _)
  rw [win_mod a b x (t + 1) ((site a t).val + 1), win_mod a b x t (site a t).val]
  · exact h
  · rw [site_val]
    exact (Nat.mod_mod t (a + 1)).symm
  · rw [site_val]
    exact (Nat.mod_add_mod t (a + 1) 1).symm

theorem orb_win (a b : ℕ) (C : Fin (a + 1) → Ctl b) (x : Fin (a + 1) → ZMod 2)
    (hx : ∀ i, cst a b C x i) (t : ℕ) : orb b (Cn a b C) (win a b x 0) t = win a b x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show tf b (Cn a b C t) (orb b (Cn a b C) (win a b x 0) t) = _
    rw [ih, sol_step a b C x hx]

theorem cn_per (a b : ℕ) (C : Fin (a + 1) → Ctl b) (t : ℕ) :
    Cn a b C (t + (a + 1)) = Cn a b C t := by
  simp only [Cn]
  rw [site_eq (a := a) (Nat.add_mod_right t (a + 1))]

theorem orb_per (a b : ℕ) (C : Fin (a + 1) → Ctl b) (s : VV (b + 1))
    (hs : orb b (Cn a b C) s (a + 1) = s) (t : ℕ) :
    orb b (Cn a b C) s (t + (a + 1)) = orb b (Cn a b C) s t := by
  induction t with
  | zero => rw [Nat.zero_add, hs]; rfl
  | succ t ih =>
    rw [show t + 1 + (a + 1) = (t + (a + 1)) + 1 by omega]
    show tf b (Cn a b C (t + (a + 1))) (orb b (Cn a b C) s (t + (a + 1))) =
      tf b (Cn a b C t) (orb b (Cn a b C) s t)
    rw [ih, cn_per]

theorem orb_shift (b : ℕ) (F : ℕ → Ctl b) (s : VV (b + 1)) (t k : ℕ) (hk : k < b) :
    orb b F s (t + 1) ⟨k, by omega⟩ = orb b F s t ⟨k + 1, by omega⟩ := by
  show tf b (F t) (orb b F s t) ⟨k, by omega⟩ = _
  rw [tf_lt _ _ _ hk]

theorem orb_col (b : ℕ) (F : ℕ → Ctl b) (s : VV (b + 1)) :
    ∀ k (hk : k < b + 1) t, orb b F s t ⟨k, hk⟩ = orb b F s (t + k) 0 := by
  intro k
  induction k with
  | zero =>
    intro hk t
    rfl
  | succ k ih =>
    intro hk t
    rw [← orb_shift b F s t k (by omega), ih (by omega) (t + 1)]
    rw [show t + 1 + k = t + (k + 1) by omega]

theorem z_mod (a b : ℕ) (C : Fin (a + 1) → Ctl b) (s : VV (b + 1))
    (hs : orb b (Cn a b C) s (a + 1) = s) (t : ℕ) :
    orb b (Cn a b C) s t 0 = orb b (Cn a b C) s (t % (a + 1)) 0 := by
  have h : ∀ q r, orb b (Cn a b C) s (r + (a + 1) * q) = orb b (Cn a b C) s r := by
    intro q
    induction q with
    | zero => intro r; rfl
    | succ q ih =>
      intro r
      rw [show r + (a + 1) * (q + 1) = (r + (a + 1) * q) + (a + 1) by ring, orb_per a b C s hs, ih]
  conv_lhs => rw [← Nat.mod_add_div t (a + 1)]
  rw [h]

def psi (a b : ℕ) (C : Fin (a + 1) → Ctl b) (s : VV (b + 1)) : Fin (a + 1) → ZMod 2 :=
  fun i => orb b (Cn a b C) s i.val 0

theorem win_psi (a b : ℕ) (C : Fin (a + 1) → Ctl b) (s : VV (b + 1))
    (hs : orb b (Cn a b C) s (a + 1) = s) (t : ℕ) :
    win a b (psi a b C s) t = orb b (Cn a b C) s t := by
  funext k
  show orb b (Cn a b C) s (site a (t + k.val)).val 0 = _
  rw [site_val, ← z_mod a b C s hs, ← orb_col b _ s k.val k.isLt t]

theorem cnt_eq (a b : ℕ) (C : Fin (a + 1) → Ctl b) :
    cnt a b C = ((Finset.univ : Finset (VV (b + 1))).filter
      (fun s => orb b (Cn a b C) s (a + 1) = s)).card := by
  refine Finset.card_nbij' (fun x => win a b x 0) (fun s => psi a b C s) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hx ⊢
    rw [orb_win a b C x hx]
    exact win_mod a b x _ _ (by simp)
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hs ⊢
    intro i
    refine (win_step a b C (psi a b C s) i).2 ?_
    rw [win_psi a b C s hs, win_psi a b C s hs]
    show tf b (Cn a b C i.val) _ = tf b (C i) _
    rw [Cn, site_fin]
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hx
    funext i
    show orb b (Cn a b C) (win a b x 0) i.val 0 = x i
    rw [orb_win a b C x hx]
    show x (site a (i.val + 0)) = x i
    rw [Nat.add_zero, site_fin]
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hs
    show win a b (psi a b C s) 0 = s
    rw [win_psi a b C s hs]
    rfl

theorem vkey {n : ℕ} (u c s : VV n) : u + c = s ↔ s + u = c := by
  constructor
  · intro h
    rw [← h, add_comm u c, add_assoc, self_add_self, add_zero]
  · intro h
    rw [← h, add_comm s u, ← add_assoc, self_add_self, zero_add]

theorem cnt_K (K : Type) [Field K] [CharP K 2] (a b : ℕ) (C : Fin (a + 1) → Ctl b) :
    ((cnt a b C : ℕ) : K) = ιK K (1 + Lp b (fun t => (Cn a b C t).1) (a + 1)).det := by
  rw [cnt_eq, ← parity K _ (cp b (Cn a b C) (a + 1))]
  have e : (Finset.univ : Finset (VV (b + 1))).filter (fun s => orb b (Cn a b C) s (a + 1) = s) =
      Finset.univ.filter (fun s => (1 + Lp b (fun t => (Cn a b C t).1) (a + 1)).mulVec s =
        cp b (Cn a b C) (a + 1)) := by
    apply Finset.filter_congr
    intro s _
    rw [orb_eq, Matrix.add_mulVec, Matrix.one_mulVec]
    exact vkey _ _ _
  rw [e]

theorem det_expand (K : Type) [Field K] [CharP K 2] {n : ℕ} (hn : 0 < n)
    (X Y : Matrix (Fin n) (Fin n) (ZMod 2)) (hX : X.det = 1) (hY : Y.det = 1) :
    ιK K (1 + X * Y).det = ∑ a : Ix n, hc K X a.1.1 a.1.2 * hc K Y a.1.2 a.1.1 := by
  rw [← top_coeff, trace_id, map_sum]
  have : ∀ S : Finset (Fin n), ιK K (cm (X * Y) S S) = ∑ T, hc K X S T * hc K Y T S := by
    intro S
    rw [cm_mul, Matrix.mul_apply, map_sum]
    simp only [map_mul, hc_apply]
  simp_rw [this]
  rw [split_sum K hn (fun S T => hc K X S T * hc K Y T S)]
  · intro S T h
    rw [hc_apply, cm_homog _ _ _ h, map_zero, zero_mul]
  · rw [hc_apply, hc_apply, cm_empty, cm_empty, map_one, mul_one]
  · rw [hc_apply, hc_apply, top_coeff, top_coeff, hX, hY, map_one, mul_one]

/- the upper bound -/

def st (K : Type) [Field K] [CharP K 2] (b : ℕ) (P : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) :
    Ix (b + 1) → K := fun a => hc K P a.1.1 a.1.2

def exm (K : Type) [Field K] (b : ℕ) (X : Ix (b + 1) → K) (U T : Finset (Fin (b + 1))) : K :=
  if h : pr (b + 1) (U, T) then X ⟨(U, T), h⟩ else 0

def stepL (K : Type) [Field K] [CharP K 2] (b : ℕ) (A : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) :
    (Ix (b + 1) → K) →ₗ[K] (Ix (b + 1) → K) where
  toFun X a := ∑ U, hc K A a.1.1 U * exm K b X U a.1.2
  map_add' X Y := by
    funext a
    simp only [Pi.add_apply, exm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    split_ifs <;> ring
  map_smul' r X := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, exm, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun U _ => ?_)
    split_ifs <;> ring

theorem stepL_st (K : Type) [Field K] [CharP K 2] (b : ℕ)
    (A P : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) :
    stepL K b A (st K b P) = st K b (A * P) := by
  funext a
  show ∑ U, hc K A a.1.1 U * exm K b (st K b P) U a.1.2 = hc K (A * P) a.1.1 a.1.2
  rw [hc_mul, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  simp only [exm, st]
  split_ifs with h
  · rfl
  · by_cases hU : a.1.1.card = U.card
    · exfalso
      apply h
      obtain ⟨h1, h2, h3⟩ := a.2
      refine ⟨?_, ?_, ?_⟩ <;> dsimp only <;> omega
    · rw [mul_zero, hc_apply K A, cm_homog _ _ _ hU, map_zero, zero_mul]

def outL (K : Type) [Field K] (b : ℕ) : (Ix (b + 1) → K) →ₗ[K] K where
  toFun X := ∑ a : Ix (b + 1), X a * (if a.1.2 = a.1.1 then 1 else 0)
  map_add' X Y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

theorem out_st (K : Type) [Field K] [CharP K 2] (b : ℕ)
    (P : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hP : P.det = 1) :
    outL K b (st K b P) = ιK K (1 + P).det := by
  have h := det_expand K (Nat.succ_pos b) P 1 hP Matrix.det_one
  rw [mul_one] at h
  rw [h, hc_one]
  simp only [outL, st, LinearMap.coe_mk, AddHom.coe_mk, Matrix.one_apply]

theorem upper (K : Type) [Field K] [CharP K 2] (a b m : ℕ)
    (hm : Nat.choose (2 * (b + 1)) (b + 1) - 2 ≤ m) :
    ∃ (s : Fin m → K) (step : Fin (a + 1) → Ctl b → (Fin m → K) →ₗ[K] (Fin m → K))
      (out : (Fin m → K) →ₗ[K] K),
      ∀ C : Fin (a + 1) → Ctl b,
        out ((List.finRange (a + 1)).foldl (fun v i => step i (C i) v) s) = (cnt a b C : K) := by
  rw [← card_Ix (Nat.succ_pos b)] at hm
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := Ix (b + 1)) (β := Fin m)
    (by simpa using hm)
  let proj : (Fin m → K) →ₗ[K] (Ix (b + 1) → K) := LinearMap.funLeft K K e
  let inj : (Ix (b + 1) → K) →ₗ[K] (Fin m → K) :=
    { toFun := fun v j => ∑ i, if e i = j then v i else 0
      map_add' := fun v w => by
        funext j
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)
      map_smul' := fun r v => by
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp) }
  have hpi : ∀ v, proj (inj v) = v := by
    intro v
    funext i
    show (∑ i', if e i' = e i then v i' else 0) = v i
    simp only [e.injective.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine ⟨inj (st K b 1), fun i c => inj ∘ₗ stepL K b (Am b c.1) ∘ₗ proj, outL K b ∘ₗ proj,
    fun C => ?_⟩
  have hfold : ∀ (l : List (Fin (a + 1))) (y : Ix (b + 1) → K),
      proj (l.foldl (fun v i => (inj ∘ₗ stepL K b (Am b (C i).1) ∘ₗ proj) v) (inj y)) =
        l.foldl (fun y i => stepL K b (Am b (C i).1) y) y := by
    intro l
    induction l with
    | nil => intro y; exact hpi y
    | cons x l ih =>
      intro y
      simp only [List.foldl_cons, LinearMap.coe_comp, Function.comp_apply, hpi]
      exact ih _
  rw [LinearMap.comp_apply, hfold]
  have hg := fold_eq (fun t y => stepL K b (Am b (Cn a b C t).1) y)
    (fun t => st K b (Lp b (fun t => (Cn a b C t).1) t)) (fun t => (stepL_st K b _ _).symm) (a + 1)
  have e1 : (fun y (i : Fin (a + 1)) => stepL K b (Am b (C i).1) y) =
      fun y i => stepL K b (Am b (Cn a b C i.val).1) y := by
    funext y i
    rw [Cn, site_fin]
  rw [e1]
  rw [show st K b 1 = st K b (Lp b (fun t => (Cn a b C t).1) 0) from rfl]
  rw [hg, out_st K b _ (det_lp _ _ _), cnt_K]

/- every invertible matrix is a product of step matrices -/

def Dsp (b k : ℕ) : Submodule (ZMod 2) (VV (b + 1)) :=
  Submodule.span (ZMod 2) {v | ∃ i, (i + 1 < k ∨ i = b) ∧ v = ee b i}

def valid (b k : ℕ) (v : VV (b + 1)) : Prop := ∃ y ∈ Dsp b k, v = ee b (k - 1) + y

theorem allE {b : ℕ} (X : Submodule (ZMod 2) (VV (b + 1))) (z : ℕ → VV (b + 1))
    (htop : ee b b ∈ X)
    (h : ∀ i, i < b → ee b i ∈ X ∨ (z (i + 1) ∈ X ∧ valid b (i + 1) (z (i + 1)))) :
    ∀ i, ee b i ∈ X := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hib : i < b
    · rcases h i hib with h1 | ⟨h1, y, hy, hz⟩
      · exact h1
      · have hD : Dsp b (i + 1) ≤ X := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨j, hj, rfl⟩
          rcases hj with hj | hj
          · exact ih j (by omega)
          · rw [hj]
            exact htop
        have e : ee b i = z (i + 1) - y := by
          rw [hz, Nat.add_sub_cancel]
          abel
        rw [e]
        exact X.sub_mem h1 (hD hy)
    · by_cases hib' : i = b
      · rw [hib']
        exact htop
      · have e : ee b i = 0 := by
          simp only [ee]
          rw [dif_neg (by omega)]
        rw [e]
        exact X.zero_mem

theorem det_ne_of_span {n : ℕ} (W : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ⊤ ≤ Submodule.span (ZMod 2) (Set.range fun k => W k)) : W.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  apply hv0
  let φ : VV n →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => x ⬝ᵥ v
      map_add' := fun x y => add_dotProduct x y v
      map_smul' := fun r x => smul_dotProduct r x v }
  have hle : Submodule.span (ZMod 2) (Set.range fun k => W k) ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show W k ⬝ᵥ v = 0
    exact congrFun hv k
  funext i
  have := hle (h (Submodule.mem_top (x := Pi.single i 1)))
  rw [LinearMap.mem_ker] at this
  simpa [φ] using this

theorem top_of_ev {b : ℕ} (X : Submodule (ZMod 2) (VV (b + 1))) (h : ∀ i, ee b i ∈ X) :
    ⊤ ≤ X := by
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
  have := h i.val
  simp only [ee, i.isLt, ↓reduceDIte, Fin.eta] at this
  exact this

theorem span_rows {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0)
    (i : ℕ) : ee b i ∈ Submodule.span (ZMod 2) (Set.range fun k => M k) := by
  by_cases hi : i < b + 1
  · have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
    have e : ee b i = ∑ l, M⁻¹ ⟨i, hi⟩ l • M l := by
      funext j
      have := congrFun (congrFun (Matrix.nonsing_inv_mul M hu) ⟨i, hi⟩) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp only [ee, hi, ↓reduceDIte, ev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
    rw [e]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  · have e : ee b i = 0 := by
      simp only [ee]
      rw [dif_neg hi]
    rw [e]
    exact Submodule.zero_mem _

theorem step_exists {b : ℕ} (W W' : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hW : W.det ≠ 0)
    (hW' : W'.det ≠ 0)
    (hsh : ∀ k : Fin (b + 1), (hk : k.val < b) → W' k = W ⟨k.val + 1, by omega⟩) :
    ∃ c, Am b c * W = W' := by
  have hu : IsUnit W.det := isUnit_iff_ne_zero.2 hW
  set lam := Matrix.vecMul (W' (Fin.last b)) W⁻¹ with hlam
  have hl : Matrix.vecMul lam W = W' (Fin.last b) := by
    rw [hlam, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hN : Sh b lam * W = W' := by
    ext k j
    rw [sh_mul]
    split_ifs with hk
    · rw [hsh k hk]
    · have e : k = Fin.last b := Fin.ext (by simp; omega)
      rw [e, ← hl]
      rfl
  have h0 : lam 0 ≠ 0 := by
    intro h0
    have hd : (Sh b lam).det = 0 := by
      refine Matrix.det_eq_zero_of_column_eq_zero 0 (fun k => ?_)
      simp only [Sh, Matrix.of_apply]
      split_ifs with h1 h2
      · simp at h2
      · rfl
      · exact h0
    apply hW'
    rw [← hN, Matrix.det_mul, hd, zero_mul]
  have h1 : lam 0 = 1 := (zmod2_cases _).resolve_left h0
  refine ⟨fun j => lam j.succ, ?_⟩
  have e : (Fin.cons 1 (fun j => lam j.succ) : Fin (b + 1) → ZMod 2) = lam := by
    funext l
    refine Fin.cases ?_ (fun j => ?_) l
    · rw [Fin.cons_zero, h1]
    · rw [Fin.cons_succ]
  rw [Am, e, hN]

def gM (b : ℕ) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (j : ℕ) : VV (b + 1) :=
  if h : j < b + 1 then M ⟨j, h⟩ else 0

def Sk (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ) :
    Set (VV (b + 1)) :=
  {v | (∃ j, k ≤ j ∧ j ≤ b ∧ v = z j) ∨ (∃ j, j < k ∧ v = gM b M j)}

def SS (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ) :
    Set (VV (b + 1)) :=
  {v | (∃ j, k + 1 ≤ j ∧ j ≤ b ∧ v = z j) ∨ (∃ j, j < k ∧ v = gM b M j)}

def Good (b : ℕ) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ) (z : ℕ → VV (b + 1)) :
    Prop :=
  (∀ j, k ≤ j → j ≤ b → valid b j (z j)) ∧
    ∀ k', k ≤ k' → k' ≤ b + 1 → ⊤ ≤ Submodule.span (ZMod 2) (Sk b z M k')

theorem good_base {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    Good b M (b + 1) (fun _ => 0) := by
  refine ⟨fun j h1 h2 => absurd h1 (by omega), fun k' h1 h2 => ?_⟩
  have hk : k' = b + 1 := by omega
  rw [hk]
  refine top_of_ev _ (fun i => ?_)
  refine Submodule.span_mono ?_ (span_rows M hM i)
  rintro _ ⟨k, rfl⟩
  refine Or.inr ⟨k.val, k.isLt, ?_⟩
  simp only [gM, k.isLt, ↓reduceDIte, Fin.eta]

theorem good_step {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ)
    (hk1 : 1 ≤ k) (hkb : k ≤ b) (z : ℕ → VV (b + 1)) (hz : Good b M (k + 1) z) :
    ∃ z', Good b M k z' := by
  obtain ⟨hv, hs⟩ := hz
  have hSk : ⊤ ≤ Submodule.span (ZMod 2) (insert (gM b M k) (SS b z M k)) := by
    refine (hs (k + 1) le_rfl (by omega)).trans (Submodule.span_mono ?_)
    rintro v (⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl ⟨j, hj1, hj2, rfl⟩)
    · by_cases hjk : j = k
      · rw [hjk]
        exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨j, by omega, rfl⟩)
  have hchoose : ∃ x, valid b k x ∧ ⊤ ≤ Submodule.span (ZMod 2) (insert x (SS b z M k)) := by
    by_cases hA : ∃ y ∈ Dsp b k, ee b (k - 1) + y ∉ Submodule.span (ZMod 2) (SS b z M k)
    · obtain ⟨y, hy, hny⟩ := hA
      refine ⟨ee b (k - 1) + y, ⟨y, hy, rfl⟩, ?_⟩
      have hx : ee b (k - 1) + y ∈ Submodule.span (ZMod 2) (insert (gM b M k) (SS b z M k)) :=
        hSk Submodule.mem_top
      have hg := mem_span_insert_exchange hx hny
      refine hSk.trans (Submodule.span_le.2 ?_)
      rintro v (rfl | hv)
      · exact hg
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ hv)
    · push Not at hA
      refine ⟨ee b (k - 1), ⟨0, Submodule.zero_mem _, by rw [add_zero]⟩, ?_⟩
      have h0 : ee b (k - 1) ∈ Submodule.span (ZMod 2) (SS b z M k) := by
        simpa using hA 0 (Submodule.zero_mem _)
      have hD : ∀ i, (i + 1 < k ∨ i = b) → ee b i ∈ Submodule.span (ZMod 2) (SS b z M k) := by
        intro i hi
        have h2 := hA (ee b i) (Submodule.subset_span ⟨i, hi, rfl⟩)
        have e2 : ee b i = (ee b (k - 1) + ee b i) - ee b (k - 1) := by abel
        rw [e2]
        exact Submodule.sub_mem _ h2 h0
      have hall := allE (Submodule.span (ZMod 2) (SS b z M k)) z (hD b (Or.inr rfl)) (by
        intro i hi
        by_cases hik : i + 1 < k
        · exact Or.inl (hD i (Or.inl hik))
        · by_cases hik' : i + 1 = k
          · left
            rw [show i = k - 1 by omega]
            exact h0
          · right
            exact ⟨Submodule.subset_span (Or.inl ⟨i + 1, by omega, by omega, rfl⟩),
              hv (i + 1) (by omega) (by omega)⟩)
      exact (top_of_ev _ hall).trans (Submodule.span_mono (Set.subset_insert _ _))
  obtain ⟨x, hxv, hxs⟩ := hchoose
  refine ⟨Function.update z k x, ?_, ?_⟩
  · intro j hj1 hj2
    by_cases hjk : j = k
    · rw [hjk, Function.update_self]
      exact hxv
    · rw [Function.update_of_ne hjk]
      exact hv j (by omega) hj2
  · intro k' hk' hk'b
    by_cases hkk : k' = k
    · rw [hkk]
      refine hxs.trans (Submodule.span_mono ?_)
      rintro v (rfl | ⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨k, le_rfl, hkb, by rw [Function.update_self]⟩
      · exact Or.inl ⟨j, by omega, hj2, by rw [Function.update_of_ne (by omega)]⟩
      · exact Or.inr ⟨j, hj, rfl⟩
    · refine (hs k' (by omega) hk'b).trans (Submodule.span_mono ?_)
      rintro v (⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨j, hj1, hj2, by rw [Function.update_of_ne (by omega)]⟩
      · exact Or.inr ⟨j, hj, rfl⟩

theorem good_one {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ z, Good b M 1 z := by
  have h : ∀ r, r ≤ b → ∃ z, Good b M (b + 1 - r) z := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨fun _ => 0, good_base M hM⟩
    | succ r ih =>
      intro hr
      obtain ⟨z, hz⟩ := ih (by omega)
      rw [show b + 1 - r = (b - r) + 1 by omega] at hz
      rw [show b + 1 - (r + 1) = b - r by omega]
      exact good_step M (b - r) (by omega) (by omega) z hz
  obtain ⟨z, hz⟩ := h b le_rfl
  rw [show b + 1 - b = 1 by omega] at hz
  exact ⟨z, hz⟩

def seqf (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (t : ℕ) :
    VV (b + 1) :=
  if t < b + 1 then ee b t else if t < 2 * b + 1 then z (t - b) else gM b M (t - (2 * b + 1))

def Wn (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (t : ℕ) :
    Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
  Matrix.of fun k l => seqf b z M (t + k.val) l

theorem surj_exact {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ D : ℕ → Fin b → ZMod 2, Lp b D (2 * b + 1) = M := by
  obtain ⟨z, hv, hs⟩ := good_one M hM
  have hspan : ∀ t, t ≤ 2 * b + 1 →
      ⊤ ≤ Submodule.span (ZMod 2) (Set.range fun k => Wn b z M t k) := by
    intro t ht
    by_cases htb : t ≤ b
    · apply top_of_ev
      apply allE _ z
      · refine Submodule.subset_span ⟨⟨b - t, by omega⟩, ?_⟩
        show seqf b z M (t + (b - t)) = ee b b
        rw [show t + (b - t) = b by omega, seqf, if_pos (by omega)]
      · intro i hi
        by_cases hit : t ≤ i
        · left
          refine Submodule.subset_span ⟨⟨i - t, by omega⟩, ?_⟩
          show seqf b z M (t + (i - t)) = ee b i
          rw [show t + (i - t) = i by omega, seqf, if_pos (by omega)]
        · right
          refine ⟨Submodule.subset_span ⟨⟨i + 1 + b - t, by omega⟩, ?_⟩,
            hv (i + 1) (by omega) (by omega)⟩
          show seqf b z M (t + (i + 1 + b - t)) = z (i + 1)
          rw [seqf, if_neg (by omega), if_pos (by omega)]
          congr 1
          omega
    · have hk := hs (t - b) (by omega) (by omega)
      refine hk.trans (Submodule.span_mono ?_)
      rintro v (⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
      · refine ⟨⟨j - (t - b), by omega⟩, ?_⟩
        show seqf b z M (t + (j - (t - b))) = z j
        rw [seqf, if_neg (by omega), if_pos (by omega)]
        congr 1
        omega
      · refine ⟨⟨j + 2 * b + 1 - t, by omega⟩, ?_⟩
        show seqf b z M (t + (j + 2 * b + 1 - t)) = gM b M j
        rw [seqf, if_neg (by omega), if_neg (by omega)]
        congr 1
        omega
  have hW0 : Wn b z M 0 = 1 := by
    ext k l
    rw [Wn, Matrix.of_apply, seqf, if_pos (by omega), Matrix.one_apply]
    simp only [ee, Nat.zero_add, k.isLt, ↓reduceDIte, Fin.eta, ev]
  have hWL : Wn b z M (2 * b + 1) = M := by
    ext k l
    rw [Wn, Matrix.of_apply, seqf, if_neg (by omega), if_neg (by omega), gM,
      dif_pos (by omega)]
    have e : ∀ y : Fin (b + 1), y.val = k.val → M y l = M k l := fun y hy => by rw [Fin.ext hy]
    exact e _ (by simp only; omega)
  have hshift : ∀ t (k : Fin (b + 1)) (hk : k.val < b),
      Wn b z M (t + 1) k = Wn b z M t ⟨k.val + 1, by omega⟩ := by
    intro t k hk
    funext l
    show seqf b z M (t + 1 + k.val) l = seqf b z M (t + (k.val + 1)) l
    rw [show t + 1 + k.val = t + (k.val + 1) by omega]
  have hex : ∀ t, ∃ c : Fin b → ZMod 2, t < 2 * b + 1 → Am b c * Wn b z M t = Wn b z M (t + 1) := by
    intro t
    by_cases ht : t < 2 * b + 1
    · obtain ⟨c, hc⟩ := step_exists (Wn b z M t) (Wn b z M (t + 1))
        (det_ne_of_span _ (hspan t (by omega))) (det_ne_of_span _ (hspan (t + 1) (by omega)))
        (fun k hk => hshift t k hk)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose D hD using hex
  refine ⟨D, ?_⟩
  have h : ∀ t, t ≤ 2 * b + 1 → Lp b D t = Wn b z M t := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [hW0]
      rfl
    | succ t ih =>
      intro ht
      show Am b (D t) * Lp b D t = _
      rw [ih (by omega), hD t (by omega)]
  rw [h _ le_rfl, hWL]

theorem surj {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0)
    (L : ℕ) (hL : 2 * b + 1 ≤ L) : ∃ D : ℕ → Fin b → ZMod 2, Lp b D L = M := by
  induction L, hL using Nat.le_induction generalizing M with
  | base => exact surj_exact M hM
  | succ L hL ih =>
    have hA : IsUnit (Am b 0).det := by
      rw [det_am]
      exact isUnit_one
    obtain ⟨D, hD⟩ := ih ((Am b 0)⁻¹ * M) (by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, det_am, Ring.inverse_one, one_mul]
      exact hM)
    refine ⟨fun t => if t = L then 0 else D t, ?_⟩
    show Am b (if L = L then 0 else D L) * Lp b (fun t => if t = L then 0 else D t) L = M
    rw [if_pos rfl, lp_congr b _ D L (fun t ht => if_neg (by omega)), hD, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]

theorem span_of_surj (K : Type) [Field K] [CharP K 2] {n : ℕ} {P : Type}
    (X : P → Matrix (Fin n) (Fin n) (ZMod 2))
    (hX : ∀ g : VV n ≃ₗ[ZMod 2] VV n, ∃ p, X p = mat g) (α : Ix n) :
    (Pi.single α 1 : Ix n → K) ∈
      Submodule.span K (Set.range fun p => fun β : Ix n => hc K (X p) β.1.2 β.1.1) := by
  refine Submodule.span_mono ?_ (span_u K α)
  rintro _ ⟨p, rfl⟩
  obtain ⟨q, hq⟩ := hX p.1
  exact ⟨q, by simp only [hq]⟩

/- the lower bound -/

theorem lower (K : Type) [Field K] [CharP K 2] (a b m : ℕ) (hn : 2 * (2 * (b + 1) - 1) ≤ a + 1)
    (s : Fin m → K) (step : Fin (a + 1) → Ctl b → (Fin m → K) →ₗ[K] (Fin m → K))
    (out : (Fin m → K) →ₗ[K] K)
    (hsc : ∀ C : Fin (a + 1) → Ctl b,
        out ((List.finRange (a + 1)).foldl (fun v i => step i (C i) v) s) = (cnt a b C : K)) :
    Nat.choose (2 * (b + 1)) (b + 1) - 2 ≤ m := by
  set i0 := 2 * b + 1 with hi0
  have hn' : 2 * i0 ≤ a + 1 := by omega
  let mix : (Fin (a + 1) → Ctl b) → (Fin (a + 1) → Ctl b) → (Fin (a + 1) → Ctl b) :=
    fun τ σ j => if j.val < i0 then τ j else σ j
  let u : (Fin (a + 1) → Ctl b) → Fin m → K := fun τ =>
    ((List.finRange (a + 1)).take i0).foldl (fun v j => step j (τ j) v) s
  have hL : ∀ σ : Fin (a + 1) → Ctl b, ∃ L : (Fin m → K) →ₗ[K] (Fin m → K), ∀ v,
      ((List.finRange (a + 1)).drop i0).foldl (fun v j => step j (σ j) v) v = L v :=
    fun σ => fold_lin _ (fun j => step j (σ j))
  choose L hL using hL
  have key : ∀ τ σ, out (L σ (u τ)) = (cnt a b (mix τ σ) : K) := by
    intro τ σ
    have e1 : ((List.finRange (a + 1)).take i0).foldl
        (fun v j => step j (mix τ σ j) v) s = u τ :=
      fold_congr _ (fun j => ⇑(step j (mix τ σ j))) (fun j => ⇑(step j (τ j)))
        (fun x hx => by simp only [mix, if_pos (mem_take_lt hx)]) s
    have e2 : ∀ v, ((List.finRange (a + 1)).drop i0).foldl
        (fun v j => step j (mix τ σ j) v) v =
        ((List.finRange (a + 1)).drop i0).foldl (fun v j => step j (σ j) v) v :=
      fun v => fold_congr _ (fun j => ⇑(step j (mix τ σ j))) (fun j => ⇑(step j (σ j)))
        (fun x hx => by simp only [mix, if_neg (not_lt.2 (mem_drop_ge hx))]) v
    rw [← hsc, ← hL σ, ← e1, ← e2, ← List.foldl_append, List.take_append_drop]
  let B : (Fin (a + 1) → Ctl b) → Fin m → K :=
    fun σ j => out (L σ (fun j' => if j = j' then 1 else 0))
  have hfac : ∀ τ σ, (cnt a b (mix τ σ) : K) = ∑ j, u τ j * B σ j := by
    intro τ σ
    rw [← key]
    conv_lhs => rw [pi_eq_sum_univ (u τ)]
    simp only [map_sum, map_smul, smul_eq_mul, B]
  let Lpre : (Fin (a + 1) → Ctl b) → Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
    fun τ => Lp b (fun t => (τ (site a t)).1) i0
  let Lsuf : (Fin (a + 1) → Ctl b) → Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
    fun σ => Lp b (fun t => (σ (site a (i0 + t))).1) (a + 1 - i0)
  have hprod : ∀ τ σ, Lp b (fun t => (Cn a b (mix τ σ) t).1) (a + 1) = Lsuf σ * Lpre τ := by
    intro τ σ
    have h := lp_add b (fun t => (Cn a b (mix τ σ) t).1) i0 (a + 1 - i0)
    rw [show i0 + (a + 1 - i0) = a + 1 by omega] at h
    rw [h]
    congr 1
    · apply lp_congr
      intro t ht
      show (mix τ σ (site a (i0 + t))).1 = (σ (site a (i0 + t))).1
      have hv : ¬ (site a (i0 + t)).val < i0 := by
        rw [site_val, Nat.mod_eq_of_lt (by omega)]
        omega
      simp only [mix, hv, ↓reduceIte]
    · apply lp_congr
      intro t ht
      show (mix τ σ (site a t)).1 = (τ (site a t)).1
      have hv : (site a t).val < i0 := by
        rw [site_val, Nat.mod_eq_of_lt (by omega)]
        exact ht
      simp only [mix, hv, ↓reduceIte]
  have hfix : ∀ τ σ, (cnt a b (mix τ σ) : K) =
      ∑ α : Ix (b + 1), hc K (Lpre τ) α.1.2 α.1.1 * hc K (Lsuf σ) α.1.1 α.1.2 := by
    intro τ σ
    rw [cnt_K, hprod, det_expand K (Nat.succ_pos b) _ _ (det_lp _ _ _) (det_lp _ _ _)]
    exact Finset.sum_congr rfl (fun α _ => mul_comm _ _)
  have hdet : ∀ g : VV (b + 1) ≃ₗ[ZMod 2] VV (b + 1), (mat g).det ≠ 0 := by
    intro g
    rw [det_mat]
    exact one_ne_zero
  have hsurjP : ∀ g : VV (b + 1) ≃ₗ[ZMod 2] VV (b + 1),
      ∃ τ : Fin (a + 1) → Ctl b, Lpre τ = mat g := by
    intro g
    obtain ⟨D, hD⟩ := surj (mat g) (hdet g) i0 (by omega)
    refine ⟨fun j => (D j.val, 0), ?_⟩
    rw [← hD]
    apply lp_congr
    intro t ht
    show D (site a t).val = D t
    rw [site_val, Nat.mod_eq_of_lt (by omega)]
  have hsurjS : ∀ g : VV (b + 1) ≃ₗ[ZMod 2] VV (b + 1),
      ∃ σ : Fin (a + 1) → Ctl b, Lsuf σ = mat g := by
    intro g
    obtain ⟨D, hD⟩ := surj (mat g) (hdet g) (a + 1 - i0) (by omega)
    refine ⟨fun j => (D (j.val - i0), 0), ?_⟩
    rw [← hD]
    apply lp_congr
    intro t ht
    show D ((site a (i0 + t)).val - i0) = D t
    rw [site_val, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]
  have hu : ∀ α : Ix (b + 1), ∃ c : (Fin (a + 1) → Ctl b) → K, ∀ β,
      ∑ p, c p * hc K (Lpre p) β.1.2 β.1.1 = if β = α then 1 else 0 :=
    fun α => toFun _ α (span_of_surj K Lpre hsurjP α)
  have hw : ∀ α : Ix (b + 1), ∃ c : (Fin (a + 1) → Ctl b) → K, ∀ β,
      ∑ p, c p * hc K (Lsuf p) β.1.1 β.1.2 = if β = α then 1 else 0 := by
    intro α
    obtain ⟨c, hc'⟩ := toFun _ (sw (b + 1) α) (span_of_surj K Lsuf hsurjS (sw (b + 1) α))
    refine ⟨c, fun β => ?_⟩
    have h1 := hc' (sw (b + 1) β)
    simp only [(sw (b + 1)).injective.eq_iff] at h1
    exact h1
  have hfin : Fintype.card (Ix (b + 1)) ≤ m :=
    (main_iff (P := Fin (a + 1) → Ctl b) (ι := Ix (b + 1)) m
      (fun τ σ => (cnt a b (mix τ σ) : K))
      (fun p α => hc K (Lpre p) α.1.2 α.1.1) (fun r α => hc K (Lsuf r) α.1.1 α.1.2)
      hfix hu hw).1 ⟨u, B, hfac⟩
  rwa [card_Ix (Nat.succ_pos b)] at hfin

end

end PEqualNP.Outside.L_lib_616

open PEqualNP.Outside.L_lib_616 in
theorem PEqualNP.Outside.L_lib_616 : ∀ (K : Type) [Field K] [CharP K 2] (b a m : ℕ),
  let w := b + 1
  let n := a + 1
  let Control := (Fin b → ZMod 2) × ZMod 2
  let cost := Nat.choose (2 * w) w - 2
  let atSite := fun k => Fin.ofNat (a + 1) k
  let count := fun (C : Fin n → Control) =>
    ((Finset.univ : Finset (Fin n → ZMod 2)).filter (fun x =>
      ∀ i : Fin n, x (atSite (i.val + w)) = x i + (C i).2 +
        ∑ j : Fin b, (C i).1 j * x (atSite (i.val + 1 + j.val)))).card
  let admits :=
    ∃ (s : Fin m → K) (step : Fin n → Control → (Fin m → K) →ₗ[K] (Fin m → K))
      (out : (Fin m → K) →ₗ[K] K),
      ∀ C : Fin n → Control,
        out ((List.finRange n).foldl (fun v i => step i (C i) v) s) = (count C : K)
  (cost ≤ m → admits) ∧ (2 * (2 * w - 1) ≤ n → admits → cost ≤ m) := by
  intro K _ _ b a m
  dsimp only
  exact ⟨fun hm => upper K a b m hm, fun hn h => by
    obtain ⟨s, step, out, hc⟩ := h
    exact lower K a b m hn s step out hc⟩
