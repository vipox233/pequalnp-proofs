import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_708

open Polynomial

/-- The permanent of the square table whose columns in `S` all equal `lam` and whose other
columns are those of `c`. -/
def phi {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A) (S : Finset (Fin n))
    (lam : Fin n → A) : A :=
  ∑ σ : Equiv.Perm (Fin n), (∏ j ∈ S, lam (σ j)) * ∏ j ∈ Sᶜ, c (σ j) j

theorem phi_map {A B : Type} [CommSemiring A] [CommSemiring B] (f : A →+* B) {n : ℕ}
    (c : Fin n → Fin n → A) (S : Finset (Fin n)) (lam : Fin n → A) :
    f (phi c S lam) = phi (fun i j => f (c i j)) S (fun i => f (lam i)) := by
  simp only [phi, map_sum, map_mul, map_prod]

theorem phi_smul {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam : Fin n → A) (s : A) :
    phi c S (fun i => s * lam i) = s ^ S.card * phi c S lam := by
  simp only [phi, Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem phi_pos {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 < c i j) (S : Finset (Fin n))
    (lam : Fin n → ℝ) (hl : ∀ i, 0 < lam i) : 0 < phi c S lam := by
  unfold phi
  exact Finset.sum_pos (fun σ _ => mul_pos (Finset.prod_pos fun j _ => hl _)
    (Finset.prod_pos fun j _ => hc _ _)) Finset.univ_nonempty

theorem phi_univ {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (lam : Fin n → A) : phi c Finset.univ lam = (n.factorial : A) * ∏ i, lam i := by
  unfold phi
  have h : ∀ σ : Equiv.Perm (Fin n),
      (∏ j ∈ (Finset.univ : Finset (Fin n)), lam (σ j)) *
        ∏ j ∈ (Finset.univ : Finset (Fin n))ᶜ, c (σ j) j = ∏ i, lam i := by
    intro σ
    rw [Finset.compl_univ, Finset.prod_empty, mul_one]
    exact Equiv.prod_comp σ lam
  rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]

theorem phi_empty {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (lam : Fin n → A) : phi c ∅ lam = ∑ σ : Equiv.Perm (Fin n), ∏ j, c (σ j) j := by
  unfold phi
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_empty, one_mul, Finset.compl_empty]

/-- The polynomial `z ↦ phi c S (lam + z • u)`. -/
noncomputable def phiPoly {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam u : Fin n → A) : A[X] :=
  phi (fun i j => C (c i j)) S (fun i => C (lam i) + C (u i) * X)

theorem phiPoly_eval {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam u : Fin n → A) (z : A) :
    (phiPoly c S lam u).eval z = phi c S (fun i => lam i + u i * z) := by
  have h := phi_map (Polynomial.evalRingHom z) (fun i j => C (c i j)) S
    (fun i => C (lam i) + C (u i) * X)
  simpa [phiPoly] using h

theorem phiPoly_map {A B : Type} [CommSemiring A] [CommSemiring B] (f : A →+* B) {n : ℕ}
    (c : Fin n → Fin n → A) (S : Finset (Fin n)) (lam u : Fin n → A) :
    (phiPoly c S lam u).map f =
      phiPoly (fun i j => f (c i j)) S (fun i => f (lam i)) (fun i => f (u i)) := by
  have h := phi_map (Polynomial.mapRingHom f) (fun i j => C (c i j)) S
    (fun i => C (lam i) + C (u i) * X)
  simpa [phiPoly] using h

theorem phiPoly_natDegree_le {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam u : Fin n → A) : (phiPoly c S lam u).natDegree ≤ S.card := by
  unfold phiPoly phi
  dsimp only
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine (Polynomial.natDegree_mul_le).trans ?_
  have h1 : (∏ j ∈ S, (C (lam (σ j)) + C (u (σ j)) * X : A[X])).natDegree ≤ S.card := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ j ∈ S, (C (lam (σ j)) + C (u (σ j)) * X : A[X]).natDegree
        ≤ ∑ j ∈ S, 1 := Finset.sum_le_sum fun j _ => by
          rw [Polynomial.natDegree_C_add]
          exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
      _ = S.card := by simp
  have h2 : (∏ j ∈ Sᶜ, (C (c (σ j) j) : A[X])).natDegree = 0 := by
    rw [← map_prod]
    exact Polynomial.natDegree_C _
  omega

theorem phiPoly_derivative_eval_zero {A : Type} [CommRing A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam u : Fin n → A) :
    (derivative (phiPoly c S lam u)).eval 0 =
      ∑ j0 ∈ S, ∑ σ : Equiv.Perm (Fin n),
        u (σ j0) * (∏ j ∈ S.erase j0, lam (σ j)) * ∏ j ∈ Sᶜ, c (σ j) j := by
  have hconst : ∀ σ : Equiv.Perm (Fin n),
      (∏ j ∈ Sᶜ, (C (c (σ j) j) : A[X])) = C (∏ j ∈ Sᶜ, c (σ j) j) :=
    fun σ => (map_prod C _ _).symm
  have h1 : ∀ σ : Equiv.Perm (Fin n),
      (derivative ((∏ j ∈ S, (C (lam (σ j)) + C (u (σ j)) * X)) *
        ∏ j ∈ Sᶜ, (C (c (σ j) j) : A[X]))).eval 0
        = ∑ j0 ∈ S, u (σ j0) * (∏ j ∈ S.erase j0, lam (σ j)) * ∏ j ∈ Sᶜ, c (σ j) j := by
    intro σ
    rw [hconst σ, derivative_mul, derivative_C, mul_zero, add_zero, derivative_prod_finset,
      eval_mul, eval_C, eval_finsetSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j0 _ => ?_
    simp only [eval_mul, eval_prod, eval_add, eval_C, eval_X, mul_zero, add_zero, derivative_add,
      derivative_C, derivative_C_mul, derivative_X, mul_one, zero_add]
    ring
  unfold phiPoly phi
  dsimp only
  rw [derivative_sum, eval_finsetSum, Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_comm]

theorem swap_sum {A : Type} [CommSemiring A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam : Fin n → A) (j0 j1 : Fin n) (h0 : j0 ∈ S) (h1 : j1 ∈ S) :
    (∑ σ : Equiv.Perm (Fin n),
        c (σ j0) j1 * (∏ j ∈ S.erase j0, lam (σ j)) * ∏ j ∈ Sᶜ, c (σ j) j)
      = phi c (S.erase j1) lam := by
  have hR : phi c (S.erase j1) lam =
      ∑ σ : Equiv.Perm (Fin n),
        c (σ j1) j1 * (∏ j ∈ S.erase j1, lam (σ j)) * ∏ j ∈ Sᶜ, c (σ j) j := by
    unfold phi
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hc : (S.erase j1)ᶜ = insert j1 Sᶜ := by
      ext j
      simp only [Finset.mem_compl, Finset.mem_erase, Finset.mem_insert, not_and]
      constructor
      · intro h
        by_cases hj : j = j1
        · exact Or.inl hj
        · exact Or.inr (fun hjS => hj (h hj |> fun h' => absurd hjS h'))
      · rintro (rfl | h) hne
        · exact absurd rfl hne
        · exact h
    rw [hc, Finset.prod_insert (by simpa using h1)]
    ring
  rw [hR]
  refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j0 j1)) _ _ (fun σ => ?_)
  have e1 : (σ * Equiv.swap j0 j1) j1 = σ j0 := by simp
  have e2 : (∏ j ∈ S.erase j1, lam ((σ * Equiv.swap j0 j1) j)) = ∏ j ∈ S.erase j0, lam (σ j) := by
    refine Finset.prod_equiv (Equiv.swap j0 j1) (fun j => ?_) (fun j _ => by simp)
    rcases eq_or_ne j j1 with rfl | hj1
    · simp
    · rcases eq_or_ne j j0 with rfl | hj0
      · simp [hj1, h0, h1, Ne.symm hj1]
      · simp [Equiv.swap_apply_of_ne_of_ne hj0 hj1, hj0, hj1]
  have e3 : (∏ j ∈ Sᶜ, c ((σ * Equiv.swap j0 j1) j) j) = ∏ j ∈ Sᶜ, c (σ j) j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjS : j ∉ S := by simpa using hj
    have hj0 : j ≠ j0 := fun h => hjS (h ▸ h0)
    have hj1 : j ≠ j1 := fun h => hjS (h ▸ h1)
    simp [Equiv.swap_apply_of_ne_of_ne hj0 hj1]
  show c (σ j0) j1 * (∏ j ∈ S.erase j0, lam (σ j)) * ∏ j ∈ Sᶜ, c (σ j) j =
    c ((σ * Equiv.swap j0 j1) j1) j1 * (∏ j ∈ S.erase j1, lam ((σ * Equiv.swap j0 j1) j)) *
      ∏ j ∈ Sᶜ, c ((σ * Equiv.swap j0 j1) j) j
  rw [e1, e2, e3]

theorem phiPoly_derivative {A : Type} [CommRing A] {n : ℕ} (c : Fin n → Fin n → A)
    (S : Finset (Fin n)) (lam : Fin n → A) (j1 : Fin n) (h1 : j1 ∈ S) :
    (derivative (phiPoly c S lam (fun i => c i j1))).eval 0 =
      (S.card : A) * phi c (S.erase j1) lam := by
  rw [phiPoly_derivative_eval_zero,
    Finset.sum_congr rfl (fun j0 hj0 => swap_sum c S lam j0 j1 hj0 h1), Finset.sum_const,
    nsmul_eq_mul]

/-- No zero when every entry of `lam` lies in one open half plane through the origin. -/
theorem stab {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 < c i j) (w : ℂ) :
    ∀ T : Finset (Fin n), ∀ lam : Fin n → ℂ, (∀ i, 0 < (lam i * w).re) →
      phi (fun i j => (c i j : ℂ)) Tᶜ lam ≠ 0 := by
  intro T
  refine Finset.induction_on T ?_ ?_
  · intro lam hl
    rw [Finset.compl_empty, phi_univ]
    refine mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    intro h
    have := hl i
    rw [h, zero_mul] at this
    simp at this
  · intro j1 T' hj1 ih lam hl
    rw [Finset.compl_insert]
    have hj1S : j1 ∈ T'ᶜ := by simpa using hj1
    have hroot : ∀ z : ℂ, 0 ≤ (z * w).re →
        (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam (fun i => (c i j1 : ℂ))).eval z ≠ 0 := by
      intro z hz
      rw [phiPoly_eval]
      refine ih _ (fun i => ?_)
      have h1 : (lam i + (c i j1 : ℂ) * z) * w = lam i * w + (c i j1 : ℂ) * (z * w) := by ring
      rw [h1, Complex.add_re, Complex.re_ofReal_mul]
      have h2 := hl i
      have h3 := mul_nonneg (hc i j1).le hz
      linarith
    have hdeg : 0 < (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam (fun i => (c i j1 : ℂ))).degree := by
      by_contra hnot
      have hnat : (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam (fun i => (c i j1 : ℂ))).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr (not_lt.mp hnot)
      have hPC := Polynomial.eq_C_of_natDegree_eq_zero hnat
      have hagree : ∀ v : ℂ, v ≠ 0 →
          (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ (fun i => (c i j1 : ℂ)) lam).eval v =
            (C ((phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam (fun i => (c i j1 : ℂ))).coeff 0) *
              X ^ (T'ᶜ).card).eval v := by
        intro v hv
        rw [phiPoly_eval, eval_mul, eval_C, eval_pow, eval_X]
        have h2 : (fun i => (c i j1 : ℂ) + lam i * v) =
            fun i => v * (lam i + (c i j1 : ℂ) * v⁻¹) := by
          funext i
          field_simp
          ring
        rw [h2, phi_smul, ← phiPoly_eval]
        conv_lhs => rw [hPC]
        rw [eval_C]
        ring
      have hQeq := Polynomial.eq_of_infinite_eval_eq _ _
        (Set.Infinite.mono (fun v hv => hagree v (by simpa using hv))
          (Set.finite_singleton (0:ℂ)).infinite_compl)
      have hQ0 : (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ (fun i => (c i j1 : ℂ)) lam).eval 0 = 0 := by
        rw [hQeq]
        simp [(Finset.card_pos.mpr ⟨j1, hj1S⟩).ne']
      rw [phiPoly_eval] at hQ0
      have hpos := phi_pos c hc T'ᶜ (fun i => c i j1) (fun i => hc i j1)
      have hcast := phi_map Complex.ofRealHom c T'ᶜ (fun i => c i j1)
      simp only [Complex.ofRealHom_eq_coe] at hcast
      simp only [mul_zero, add_zero] at hQ0
      rw [← hcast] at hQ0
      exact hpos.ne' (by exact_mod_cast hQ0)
    have hder : (derivative (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam
        (fun i => (c i j1 : ℂ)))).eval 0 ≠ 0 := by
      intro h0
      have hne : derivative (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam
          (fun i => (c i j1 : ℂ))) ≠ 0 := by
        intro hd0
        have hC := Polynomial.eq_C_of_derivative_eq_zero hd0
        rw [hC] at hdeg
        exact absurd hdeg (not_lt.mpr Polynomial.degree_C_le)
      have hmem : (0:ℂ) ∈ (derivative (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam
          (fun i => (c i j1 : ℂ)))).rootSet ℂ := by
        rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
        exact ⟨hne, h0⟩
      have hsub := Polynomial.rootSet_derivative_subset_convexHull_rootSet hdeg hmem
      have hconv : Convex ℝ {z : ℂ | (z * w).re < 0} := by
        refine convex_halfSpace_lt ⟨fun a b => ?_, fun r a => ?_⟩ 0
        · simp [add_mul]
        · simp [mul_assoc]
      have hin : (phiPoly (fun i j => (c i j : ℂ)) T'ᶜ lam (fun i => (c i j1 : ℂ))).rootSet ℂ ⊆
          {z : ℂ | (z * w).re < 0} := by
        intro z hz
        rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hz
        by_contra hneg
        exact hroot z (not_lt.mp hneg) hz.2
      have h00 := convexHull_min hin hconv hsub
      simp at h00
    rw [phiPoly_derivative (fun i j => (c i j : ℂ)) T'ᶜ lam j1 hj1S] at hder
    exact right_ne_zero_of_mul hder

/-- Every complex root of the real polynomial `t ↦ phi c S (lam + t • column j1)` is a
negative real. -/
theorem real_roots {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 < c i j) (S : Finset (Fin n))
    (lam : Fin n → ℝ) (hl : ∀ i, 0 < lam i) (j1 : Fin n) (z : ℂ)
    (hz : ((phiPoly c S lam (fun i => c i j1)).map Complex.ofRealHom).eval z = 0) :
    z.im = 0 ∧ z.re < 0 := by
  rw [phiPoly_map, phiPoly_eval] at hz
  simp only [Complex.ofRealHom_eq_coe] at hz
  have key : ∀ w : ℂ, (∀ i, 0 < (((lam i : ℂ) + (c i j1 : ℂ) * z) * w).re) → False := by
    intro w hw
    have h := stab c hc w Sᶜ _ hw
    rw [compl_compl] at h
    exact h hz
  have him : z.im = 0 := by
    rcases lt_trichotomy z.im 0 with h | h | h
    · exfalso
      refine key Complex.I (fun i => ?_)
      have := mul_pos (hc i j1) (neg_pos.mpr h)
      simp
      linarith
    · exact h
    · exfalso
      refine key (-Complex.I) (fun i => ?_)
      have := mul_pos (hc i j1) h
      simp
      linarith
  refine ⟨him, ?_⟩
  by_contra hre
  have hre' : 0 ≤ z.re := not_lt.mp hre
  have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hzr] at hz
  have hcast := phi_map Complex.ofRealHom c S (fun i => lam i + c i j1 * z.re)
  simp only [Complex.ofRealHom_eq_coe, Complex.ofReal_add, Complex.ofReal_mul] at hcast
  rw [← hcast] at hz
  have hpos := phi_pos c hc S (fun i => lam i + c i j1 * z.re)
    (fun i => add_pos_of_pos_of_nonneg (hl i) (mul_nonneg (hc i j1).le hre'))
  exact hpos.ne' (by exact_mod_cast hz)

/-- Two numbers: the weighted comparison of the geometric and the arithmetic mean. -/
theorem amgm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) :
    a ^ m * b ≤ (((m:ℝ) * a + b) / ((m:ℝ) + 1)) ^ (m + 1) := by
  rcases eq_or_lt_of_le ha with ha0 | hapos
  · subst ha0
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [zero_pow hm.ne', zero_mul]
      positivity
  · have hu0 : 0 ≤ ((m:ℝ) * a + b) / ((m:ℝ) + 1) := by positivity
    have hB := one_add_mul_le_pow (show (-2:ℝ) ≤ ((m:ℝ) * a + b) / ((m:ℝ) + 1) / a - 1 by
      have : 0 ≤ ((m:ℝ) * a + b) / ((m:ℝ) + 1) / a := div_nonneg hu0 hapos.le
      linarith) (m + 1)
    calc a ^ m * b = a ^ (m + 1) *
          (1 + ((m + 1 : ℕ) : ℝ) * (((m:ℝ) * a + b) / ((m:ℝ) + 1) / a - 1)) := by
          push_cast
          field_simp
          ring
      _ ≤ a ^ (m + 1) * (1 + (((m:ℝ) * a + b) / ((m:ℝ) + 1) / a - 1)) ^ (m + 1) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (((m:ℝ) * a + b) / ((m:ℝ) + 1)) ^ (m + 1) := by
          rw [← mul_pow]
          congr 1
          field_simp
          ring

theorem amgm_multiset : ∀ (Y : Multiset ℝ), (∀ y ∈ Y, 0 ≤ y) → ∀ d : ℕ, 1 ≤ d →
    Multiset.card Y ≤ d → (Y.map (fun y => 1 + y)).prod ≤ (1 + Y.sum / (d:ℝ)) ^ d := by
  intro Y
  refine Multiset.induction_on Y ?_ ?_
  · intro _ d _ _
    simp
  · intro y Y' ih hnn d hd hcard
    have hy : 0 ≤ y := hnn y (Multiset.mem_cons_self y Y')
    have hnn' : ∀ y' ∈ Y', 0 ≤ y' := fun y' hy' => hnn y' (Multiset.mem_cons_of_mem hy')
    have hs : 0 ≤ Y'.sum := Multiset.sum_nonneg hnn'
    rw [Multiset.card_cons] at hcard
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    rcases Nat.eq_zero_or_pos d' with rfl | hd'
    · have hY' : Y' = 0 := Multiset.card_eq_zero.mp (by omega)
      subst hY'
      simp
    · have hd'R : (0:ℝ) < d' := by exact_mod_cast hd'
      have ih' := ih hnn' d' hd' (by omega)
      have h2 := amgm_two (1 + Y'.sum / (d':ℝ)) (1 + y) (by positivity) (by positivity) d'
      calc (1 + y) * (Y'.map fun y => 1 + y).prod ≤ (1 + y) * (1 + Y'.sum / (d':ℝ)) ^ d' :=
            mul_le_mul_of_nonneg_left ih' (by positivity)
        _ = (1 + Y'.sum / (d':ℝ)) ^ d' * (1 + y) := mul_comm _ _
        _ ≤ (((d':ℝ) * (1 + Y'.sum / (d':ℝ)) + (1 + y)) / ((d':ℝ) + 1)) ^ (d' + 1) := h2
        _ = (1 + (y + Y'.sum) / ((d' + 1 : ℕ) : ℝ)) ^ (d' + 1) := by
            congr 1
            push_cast
            field_simp
            ring

/-- From a bound by the `d`-th power of a line to the slope at zero. -/
theorem cap_step (a S γ : ℝ) (d : ℕ) (ha : 0 ≤ a) (hS : 0 ≤ S) (hγ : 0 ≤ γ) (hd : 1 ≤ d)
    (h : ∀ t : ℝ, 0 < t → γ * t ≤ a * (1 + t * S / (d:ℝ)) ^ d) :
    γ * ((d : ℝ) - 1) ^ (d - 1) ≤ a * S * (d : ℝ) ^ (d - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  have he1 : (((e + 1 : ℕ) : ℝ) - 1) = e := by push_cast; ring
  rw [he1, Nat.add_sub_cancel]
  rcases eq_or_lt_of_le hS with hS0 | hSpos
  · have hγ0 : γ = 0 := by
      by_contra hne
      have hγpos : 0 < γ := lt_of_le_of_ne hγ (Ne.symm hne)
      have h1 := h (a / γ + 1) (by positivity)
      rw [← hS0] at h1
      simp only [mul_zero, zero_div, add_zero, one_pow, mul_one] at h1
      have h2 : γ * (a / γ + 1) = a + γ := by field_simp
      linarith
    rw [hγ0, ← hS0]
    simp
  · rcases Nat.eq_zero_or_pos e with rfl | hepos
    · simp only [pow_zero, mul_one]
      by_contra hlt
      have hpos : 0 < γ - a * S := by linarith [not_le.mp hlt]
      have h1 := h (a / (γ - a * S) + 1) (by positivity)
      simp only [zero_add, Nat.cast_one, div_one, pow_one] at h1
      have h2 : (γ - a * S) * (a / (γ - a * S) + 1) = a + (γ - a * S) := by field_simp
      nlinarith
    · have heR : (0:ℝ) < e := by exact_mod_cast hepos
      have ht : 0 < ((e:ℝ) + 1) / (e * S) := by positivity
      have h1 := h (((e:ℝ) + 1) / (e * S)) ht
      have h3 : (1 + ((e:ℝ) + 1) / (e * S) * S / ((e + 1 : ℕ) : ℝ)) = ((e:ℝ) + 1) / e := by
        push_cast
        field_simp
      rw [h3, div_pow] at h1
      have hκ : 0 < ((e:ℝ) + 1) / ((e:ℝ) ^ (e + 1) * S) := by positivity
      have e1 : γ * (((e:ℝ) + 1) / (e * S)) =
          (γ * (e:ℝ) ^ e) * (((e:ℝ) + 1) / ((e:ℝ) ^ (e + 1) * S)) := by
        field_simp
        ring
      have e2 : a * (((e:ℝ) + 1) ^ (e + 1) / (e:ℝ) ^ (e + 1)) =
          (a * S * ((e:ℝ) + 1) ^ e) * (((e:ℝ) + 1) / ((e:ℝ) ^ (e + 1) * S)) := by
        field_simp
        ring
      rw [e1, e2] at h1
      have h4 := le_of_mul_le_mul_right h1 hκ
      push_cast
      exact h4

theorem roots_prod_eval (m : Multiset ℝ) (hm : ∀ r ∈ m, 0 < r) :
    ((m.map (fun r => (X + C r : ℝ[X]))).prod).eval 0 = m.prod ∧
    (derivative ((m.map (fun r => (X + C r : ℝ[X]))).prod)).eval 0 =
      m.prod * (m.map (fun r => r⁻¹)).sum := by
  revert hm
  refine Multiset.induction_on m ?_ ?_
  · intro _
    simp
  · intro r m' ih hm
    have hr : 0 < r := hm r (Multiset.mem_cons_self r m')
    obtain ⟨ih1, ih2⟩ := ih (fun r' hr' => hm r' (Multiset.mem_cons_of_mem hr'))
    constructor
    · rw [Multiset.map_cons, Multiset.prod_cons, eval_mul, ih1, Multiset.prod_cons]
      simp
    · rw [Multiset.map_cons, Multiset.prod_cons, derivative_mul, eval_add, eval_mul, eval_mul, ih1,
        ih2, Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
      simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_one, eval_add, eval_X,
        eval_C, zero_add, one_mul]
      field_simp

theorem prod_shift (m : Multiset ℝ) (hm : ∀ r ∈ m, 0 < r) (t : ℝ) :
    (m.map (fun r => t + r)).prod =
      m.prod * ((m.map (fun r => t * r⁻¹)).map (fun y => 1 + y)).prod := by
  rw [Multiset.map_map]
  have h5 : m.prod = (m.map (fun r => r)).prod := by rw [Multiset.map_id']
  rw [h5, ← Multiset.prod_map_mul]
  congr 1
  refine Multiset.map_congr rfl (fun r hr => ?_)
  have hrpos := hm r hr
  simp only [Function.comp]
  field_simp
  ring

/-- The slope bound for a product of factors `X + r` with every `r` positive. -/
theorem univ_fac (lc : ℝ) (m : Multiset ℝ) (hm : ∀ r ∈ m, 0 < r) (d : ℕ) (hd : 1 ≤ d)
    (hcard : Multiset.card m ≤ d) (hlc : 0 ≤ lc) (γ : ℝ) (hγ : 0 ≤ γ)
    (hcap : ∀ t : ℝ, 0 < t →
      γ * t ≤ (C lc * (m.map (fun r => (X + C r : ℝ[X]))).prod).eval t) :
    γ * ((d:ℝ) - 1) ^ (d - 1) ≤
      (derivative (C lc * (m.map (fun r => (X + C r : ℝ[X]))).prod)).eval 0 *
        (d:ℝ) ^ (d - 1) := by
  obtain ⟨hev0, hder0⟩ := roots_prod_eval m hm
  have hmprod : 0 < m.prod := Multiset.prod_pos hm
  have hderiv : (derivative (C lc * (m.map (fun r => (X + C r : ℝ[X]))).prod)).eval 0 =
      lc * m.prod * (m.map (fun r => r⁻¹)).sum := by
    rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, hder0]
    ring
  have heval : ∀ t : ℝ, (C lc * (m.map (fun r => (X + C r : ℝ[X]))).prod).eval t =
      lc * (m.map (fun r => t + r)).prod := by
    intro t
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp [Function.comp]
  have hSnn : 0 ≤ (m.map (fun r => r⁻¹)).sum := by
    refine Multiset.sum_nonneg (fun x hx => ?_)
    rw [Multiset.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    exact (inv_pos.mpr (hm r hr)).le
  have hprodnn : 0 ≤ lc * m.prod := mul_nonneg hlc hmprod.le
  have hbound : ∀ t : ℝ, 0 < t →
      γ * t ≤ (lc * m.prod) * (1 + t * (m.map (fun r => r⁻¹)).sum / (d:ℝ)) ^ d := by
    intro t ht
    refine (hcap t ht).trans ?_
    rw [heval t, prod_shift m hm t]
    have h2 := amgm_multiset (m.map (fun r => t * r⁻¹)) (by
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨r, hr, rfl⟩ := hy
        exact mul_nonneg ht.le (inv_pos.mpr (hm r hr)).le) d hd (by
        rw [Multiset.card_map]
        exact hcard)
    rw [Multiset.sum_map_mul_left] at h2
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 hprodnn
  have hfin := cap_step _ _ γ d hprodnn hSnn hγ hd hbound
  rw [hderiv]
  exact hfin

/-- A real polynomial of degree at most `d` whose roots are all negative reals: a lower bound
by a line through the origin on the positive axis bounds the slope at zero. -/
theorem univ_lemma (R : ℝ[X]) (d : ℕ) (hd : 1 ≤ d) (hdeg : R.natDegree ≤ d) (h0 : 0 < R.eval 0)
    (hroots : ∀ z : ℂ, (R.map Complex.ofRealHom).eval z = 0 → z.im = 0 ∧ z.re < 0)
    (γ : ℝ) (hγ : 0 ≤ γ) (hcap : ∀ t : ℝ, 0 < t → γ * t ≤ R.eval t) :
    γ * ((d:ℝ) - 1) ^ (d - 1) ≤ (derivative R).eval 0 * (d:ℝ) ^ (d - 1) := by
  have hR0 : R ≠ 0 := by
    rintro rfl
    simp at h0
  have hP0 : R.map Complex.ofRealHom ≠ 0 :=
    (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hR0
  have hsplit : (R.map Complex.ofRealHom).Splits := IsAlgClosed.splits _
  have hrt : ∀ ρ ∈ (R.map Complex.ofRealHom).roots, ρ.im = 0 ∧ ρ.re < 0 := fun ρ hρ =>
    hroots ρ ((Polynomial.mem_roots hP0).mp hρ)
  have hex : ∃ (lc : ℝ) (m : Multiset ℝ), (∀ r ∈ m, 0 < r) ∧ Multiset.card m ≤ d ∧
      R = C lc * (m.map (fun r => (X + C r : ℝ[X]))).prod := by
    refine ⟨R.leadingCoeff, (R.map Complex.ofRealHom).roots.map (fun ρ => -ρ.re), ?_, ?_, ?_⟩
    · intro r hr
      rw [Multiset.mem_map] at hr
      obtain ⟨ρ, hρ, rfl⟩ := hr
      linarith [(hrt ρ hρ).2]
    · rw [Multiset.card_map]
      exact (Polynomial.card_roots' _).trans (by rw [Polynomial.natDegree_map]; exact hdeg)
    · apply Polynomial.map_injective Complex.ofRealHom Complex.ofReal_injective
      rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_multiset_prod, Multiset.map_map,
        Multiset.map_map]
      conv_lhs => rw [hsplit.eq_prod_roots, Polynomial.leadingCoeff_map]
      congr 2
      refine Multiset.map_congr rfl (fun ρ hρ => ?_)
      have hρ' : ρ = ((ρ.re : ℝ) : ℂ) := Complex.ext rfl (by simp [(hrt ρ hρ).1])
      simp only [Function.comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
        Complex.ofRealHom_eq_coe, Complex.ofReal_neg]
      conv_lhs => rw [hρ']
      simp [sub_eq_add_neg]
  obtain ⟨lc, m, hm, hcard, rfl⟩ := hex
  have hmprod : 0 < m.prod := Multiset.prod_pos hm
  have hlc : 0 ≤ lc := by
    by_contra hneg
    rw [eval_mul, eval_C, (roots_prod_eval m hm).1] at h0
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) hmprod
    linarith
  exact univ_fac lc m hm d hd hcard hlc γ hγ hcap

/-- The first `k` columns. -/
def Sk (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k)

/-- The combination of the first `k` columns of `c` with weights `x`. -/
def lamOf {n : ℕ} (c : Fin n → Fin n → ℝ) (k : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Sk n k, c i j * x j

theorem Sk_full (n : ℕ) : Sk n n = Finset.univ := by
  ext j
  simp [Sk]

theorem Sk_zero (n : ℕ) : Sk n 0 = ∅ := by
  ext j
  simp [Sk]

theorem Sk_card (n k : ℕ) (hk : k ≤ n) : (Sk n k).card = k := by
  unfold Sk
  rw [Fin.card_filter_val_lt]
  omega

theorem mem_Sk_succ (n k : ℕ) (hk : k < n) : (⟨k, hk⟩ : Fin n) ∈ Sk n (k + 1) := by
  simp [Sk]

theorem Sk_succ_erase (n k : ℕ) (hk : k < n) : (Sk n (k + 1)).erase ⟨k, hk⟩ = Sk n k := by
  ext j
  simp only [Sk, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq,
    Fin.ext_iff]
  omega

theorem prod_update_Sk {n : ℕ} (k : ℕ) (hk : k < n) (x : Fin n → ℝ) (t : ℝ) :
    ∏ j ∈ Sk n (k + 1), Function.update x ⟨k, hk⟩ t j = t * ∏ j ∈ Sk n k, x j := by
  rw [← Finset.mul_prod_erase (Sk n (k + 1)) _ (mem_Sk_succ n k hk), Function.update_self,
    Sk_succ_erase]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hne : j ≠ ⟨k, hk⟩ := by
    intro h
    rw [h] at hj
    simp [Sk] at hj
  rw [Function.update_of_ne hne]

theorem lamOf_update {n : ℕ} (c : Fin n → Fin n → ℝ) (k : ℕ) (hk : k < n) (x : Fin n → ℝ)
    (t : ℝ) :
    lamOf c (k + 1) (Function.update x ⟨k, hk⟩ t) = fun i => lamOf c k x i + c i ⟨k, hk⟩ * t := by
  funext i
  unfold lamOf
  rw [← Finset.add_sum_erase (Sk n (k + 1)) _ (mem_Sk_succ n k hk), Function.update_self,
    Sk_succ_erase, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hne : j ≠ ⟨k, hk⟩ := by
    intro h
    rw [h] at hj
    simp [Sk] at hj
  rw [Function.update_of_ne hne]

theorem phi_single {n : ℕ} (c : Fin n → Fin n → ℝ) (j1 : Fin n) (lam : Fin n → ℝ) :
    phi c {j1} (fun i => c i j1) = phi c ∅ lam := by
  unfold phi
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_singleton, Finset.prod_empty, one_mul, Finset.compl_empty,
    Finset.compl_singleton]
  exact Finset.mul_prod_erase Finset.univ (fun j => c (σ j) j) (Finset.mem_univ j1)

theorem Sk_one (n : ℕ) (hn : 0 < n) : Sk n 1 = {⟨0, hn⟩} := by
  ext j
  simp only [Sk, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff]
  omega

/-- The chain of bounds from all `n` columns down to none. -/
theorem cap_chain {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 < c i j) (γ : ℝ) (hγ : 0 ≤ γ)
    (hcap : ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → γ * ∏ j, x j ≤ ∏ i, ∑ j, c i j * x j) :
    ∀ m : ℕ, m ≤ n → ∀ x : Fin n → ℝ, (∀ j, 0 < x j) →
      γ * ((n - m : ℕ) : ℝ) ^ (n - m) * (n.factorial : ℝ) * ∏ j ∈ Sk n (n - m), x j ≤
        (n : ℝ) ^ n * phi c (Sk n (n - m)) (lamOf c (n - m) x) := by
  intro m
  induction m with
  | zero =>
    intro _ x hx
    simp only [Nat.sub_zero]
    rw [Sk_full, phi_univ]
    have h := hcap x hx
    have hl : ∀ i, lamOf c n x i = ∑ j, c i j * x j := by
      intro i
      unfold lamOf
      rw [Sk_full]
    simp only [hl]
    have hnn : 0 ≤ (n:ℝ) ^ n * (n.factorial : ℝ) := by positivity
    calc γ * (n:ℝ) ^ n * (n.factorial:ℝ) * ∏ j, x j
        = (n:ℝ) ^ n * (n.factorial : ℝ) * (γ * ∏ j, x j) := by ring
      _ ≤ (n:ℝ) ^ n * (n.factorial : ℝ) * ∏ i, ∑ j, c i j * x j :=
          mul_le_mul_of_nonneg_left h hnn
      _ = (n:ℝ) ^ n * ((n.factorial : ℝ) * ∏ i, ∑ j, c i j * x j) := by ring
  | succ m ih =>
    intro hm x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, n - (m + 1) = k := ⟨_, rfl⟩
    have hk1 : n - m = k + 1 := by omega
    have hkn : k < n := by omega
    rw [hk]
    rw [hk1] at ih'
    have hN : (0:ℝ) < (n:ℝ) ^ n := pow_pos (by exact_mod_cast (by omega : 0 < n)) n
    have hPi : 0 < ∏ j ∈ Sk n k, x j := Finset.prod_pos fun j _ => hx j
    have hupd : ∀ t : ℝ, 0 < t → ∀ j, 0 < Function.update x ⟨k, hkn⟩ t j := by
      intro t ht j
      rw [Function.update_apply]
      split_ifs
      · exact ht
      · exact hx j
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have h1 := ih' (Function.update x ⟨0, hkn⟩ 1) (hupd 1 one_pos)
      rw [prod_update_Sk 0 hkn x 1, lamOf_update c 0 hkn x 1] at h1
      have hl0 : ∀ i, lamOf c 0 x i = 0 := by
        intro i
        unfold lamOf
        rw [Sk_zero, Finset.sum_empty]
      simp only [hl0, zero_add, mul_one, Sk_zero, Finset.prod_empty, Nat.cast_one, one_pow,
        Sk_one n hkn] at h1
      rw [phi_single c ⟨0, hkn⟩ (lamOf c 0 x)] at h1
      simp only [Sk_zero, Finset.prod_empty, mul_one, Nat.cast_zero, pow_zero]
      exact h1
    · have hlam : ∀ i, 0 < lamOf c k x i := by
        intro i
        unfold lamOf
        refine Finset.sum_pos (fun j _ => mul_pos (hc i j) (hx j)) ⟨⟨0, by omega⟩, ?_⟩
        simp only [Sk, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hkpos
      have hR0 : 0 < (phiPoly c (Sk n (k + 1)) (lamOf c k x) (fun i => c i ⟨k, hkn⟩)).eval 0 := by
        rw [phiPoly_eval]
        refine phi_pos c hc _ _ (fun i => ?_)
        simpa using hlam i
      have hdeg : (phiPoly c (Sk n (k + 1)) (lamOf c k x) (fun i => c i ⟨k, hkn⟩)).natDegree ≤
          k + 1 := (phiPoly_natDegree_le _ _ _ _).trans (by rw [Sk_card n (k + 1) (by omega)])
      have hcap' : ∀ t : ℝ, 0 < t →
          (γ * ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (n.factorial : ℝ) * (∏ j ∈ Sk n k, x j) /
            (n:ℝ) ^ n) * t ≤
            (phiPoly c (Sk n (k + 1)) (lamOf c k x) (fun i => c i ⟨k, hkn⟩)).eval t := by
        intro t ht
        have h1 := ih' (Function.update x ⟨k, hkn⟩ t) (hupd t ht)
        rw [prod_update_Sk k hkn x t, lamOf_update c k hkn x t] at h1
        rw [phiPoly_eval, div_mul_eq_mul_div, div_le_iff₀ hN]
        linarith
      have hγ' : 0 ≤ γ * ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (n.factorial : ℝ) *
          (∏ j ∈ Sk n k, x j) / (n:ℝ) ^ n := by positivity
      have hU := univ_lemma _ (k + 1) (by omega) hdeg hR0
        (fun z hz => real_roots c hc (Sk n (k + 1)) (lamOf c k x) hlam ⟨k, hkn⟩ z hz) _ hγ' hcap'
      rw [phiPoly_derivative c (Sk n (k + 1)) (lamOf c k x) ⟨k, hkn⟩ (mem_Sk_succ n k hkn),
        Sk_card n (k + 1) (by omega), Sk_succ_erase n k hkn, Nat.add_sub_cancel] at hU
      have hQ : (0:ℝ) < ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by positivity
      have he : (((k + 1 : ℕ) : ℝ) - 1) = (k:ℝ) := by
        push_cast
        ring
      rw [he] at hU
      have e1 : γ * ((k + 1 : ℕ) : ℝ) ^ (k + 1) * (n.factorial : ℝ) * (∏ j ∈ Sk n k, x j) /
          (n:ℝ) ^ n * (k:ℝ) ^ k =
          ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
            (γ * (k:ℝ) ^ k * (n.factorial : ℝ) * ∏ j ∈ Sk n k, x j) / (n:ℝ) ^ n := by ring
      have e2 : ((k + 1 : ℕ) : ℝ) * phi c (Sk n k) (lamOf c k x) * ((k + 1 : ℕ) : ℝ) ^ k =
          ((k + 1 : ℕ) : ℝ) ^ (k + 1) * phi c (Sk n k) (lamOf c k x) := by ring
      rw [e1, e2, div_le_iff₀ hN] at hU
      have h' : ((k + 1 : ℕ) : ℝ) ^ (k + 1) *
          (γ * (k:ℝ) ^ k * (n.factorial : ℝ) * ∏ j ∈ Sk n k, x j) ≤
          ((k + 1 : ℕ) : ℝ) ^ (k + 1) * ((n:ℝ) ^ n * phi c (Sk n k) (lamOf c k x)) := by
        linarith
      exact le_of_mul_le_mul_left h' hQ

/-- The permanent bound for a table of positive reals. -/
theorem gurvits_pos {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 < c i j) (γ : ℝ)
    (hγ : 0 ≤ γ)
    (hcap : ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → γ * ∏ j, x j ≤ ∏ i, ∑ j, c i j * x j) :
    γ * (n.factorial : ℝ) ≤ (n:ℝ) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j, c (σ j) j := by
  have h := cap_chain c hc γ hγ hcap n le_rfl (fun _ => 1) (fun _ => one_pos)
  simp only [Nat.sub_self, Sk_zero, Finset.prod_empty, mul_one, pow_zero] at h
  rw [phi_empty] at h
  exact h

/-- The permanent bound for a table of nonnegative reals. -/
theorem gurvits {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 ≤ c i j) (γ : ℝ) (hγ : 0 ≤ γ)
    (hcap : ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → γ * ∏ j, x j ≤ ∏ i, ∑ j, c i j * x j) :
    γ * (n.factorial : ℝ) ≤ (n:ℝ) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j, c (σ j) j := by
  have hstep : ∀ δ : ℝ, 0 < δ → γ * (n.factorial : ℝ) ≤
      (n:ℝ) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j, (c (σ j) j + δ) := by
    intro δ hδ
    refine gurvits_pos (fun i j => c i j + δ) (fun i j => by have := hc i j; linarith) γ hγ
      (fun x hx => ?_)
    refine (hcap x hx).trans ?_
    refine Finset.prod_le_prod₀
      (fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hc i j) (hx j).le) (fun i _ => ?_)
    refine Finset.sum_le_sum fun j _ => ?_
    have h1 := hx j
    nlinarith [hc i j]
  have hcont : Continuous fun δ : ℝ =>
      (n:ℝ) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j, (c (σ j) j + δ) :=
    continuous_const.mul (continuous_finsetSum _ fun σ _ =>
      continuous_finsetProd _ fun j _ => continuous_const.add continuous_id)
  have htend := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Set.Ioi 0), γ * (n.factorial : ℝ) ≤
      (n:ℝ) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j, (c (σ j) j + δ) :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun δ hδ => hstep δ hδ)
  have hfin := ge_of_tendsto htend hev
  simpa using hfin

/-- The squared determinant is at most the product of the squared row lengths. -/
theorem hadamard {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    B.det ^ 2 ≤ ∏ i, ∑ j, (B i j) ^ 2 := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) := ⟨finrank_euclideanSpace_fin⟩
  have h1 : |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det
      (fun i => (WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n)))| ≤
      ∏ i, ‖(WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n))‖ := by
    rw [← ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation).volumeForm_robust'
      (EuclideanSpace.basisFun (Fin n) ℝ)]
    exact Orientation.abs_volumeForm_apply_le _ _
  have h2 : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det
      (fun i => (WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n))) = B.det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
  have h3 : ∀ i, ‖(WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n))‖ ^ 2 = ∑ j, (B i j) ^ 2 := by
    intro i
    rw [EuclideanSpace.real_norm_sq_eq]
  calc B.det ^ 2 = |(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det
        (fun i => (WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n)))| ^ 2 := by
        rw [h2, sq_abs]
    _ ≤ (∏ i, ‖(WithLp.toLp 2 (B i) : EuclideanSpace ℝ (Fin n))‖) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = ∏ i, ∑ j, (B i j) ^ 2 := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun i _ => h3 i

/-- The table with the signs of `s` applied. -/
def sg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if s (i, j) then -A i j else A i j

/-- The squared determinant after signing. -/
noncomputable def Zf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) : ℝ :=
  (Matrix.det (sg A s)) ^ 2

/-- The permanent of the squared entries. -/
def Pf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ j, (A (σ j) j) ^ 2

theorem sg_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) (i j : Fin n) :
    (sg A s i j) ^ 2 = (A i j) ^ 2 := by
  unfold sg
  split_ifs
  · ring
  · rfl

theorem Pf_sg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    Pf (sg A s) = Pf A := by
  unfold Pf
  simp only [sg_sq]

theorem Zf_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    0 ≤ Zf A s := sq_nonneg _

theorem Pf_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ Pf A :=
  Finset.sum_nonneg fun σ _ => Finset.prod_nonneg fun j _ => sq_nonneg _

/-- The squared determinant against the permanent of the squared entries. -/
theorem det_sq_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    B.det ^ 2 * (n.factorial : ℝ) ≤ (n:ℝ) ^ n * Pf B := by
  refine gurvits (fun i j => (B i j) ^ 2) (fun i j => sq_nonneg _) (B.det ^ 2) (sq_nonneg _)
    (fun x hx => ?_)
  have h := hadamard (Matrix.of fun i j => Real.sqrt (x j) * B i j)
  rw [Matrix.det_mul_row, mul_pow, ← Finset.prod_pow] at h
  have h2 : ∀ j, Real.sqrt (x j) ^ 2 = x j := fun j => Real.sq_sqrt (hx j).le
  simp only [h2, Matrix.of_apply, mul_pow] at h
  calc B.det ^ 2 * ∏ j, x j = (∏ j, x j) * B.det ^ 2 := mul_comm _ _
    _ ≤ ∏ i, ∑ j, x j * (B i j) ^ 2 := h
    _ = ∏ i, ∑ j, (B i j) ^ 2 * x j := by
        refine Finset.prod_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem Zf_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    Zf A s * (n.factorial : ℝ) ≤ (n:ℝ) ^ n * Pf A := by
  have h := det_sq_le (sg A s)
  rw [Pf_sg] at h
  exact h

/- The next two results follow the recorded proof of L-lib-459 (the sign averaging identity). -/
theorem sum_prod_signed_ne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (σ τ : Equiv.Perm (Fin n)) (hne : σ ≠ τ) :
    (∑ s : Fin n × Fin n → Bool,
      (∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i)) = 0 := by
  obtain ⟨i0, hi0⟩ : ∃ i0 : Fin n, σ i0 ≠ τ i0 := by
    by_contra h
    exact hne (Equiv.ext fun i => not_not.mp (not_exists.mp h i))
  have hflip_val : ∀ (s : Fin n × Fin n → Bool) (i j : Fin n),
      sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) i j =
        if (i, j) = (σ i0, i0) then -sg A s i j else sg A s i j := by
    intro s i j
    unfold sg
    by_cases hp : (i, j) = (σ i0, i0)
    · simp only [hp, ite_true, Function.update_self]
      cases s (σ i0, i0) <;> simp
    · simp only [hp, ite_false, Function.update_of_ne hp]
  have hprod_σ : ∀ s : Fin n × Fin n → Bool,
      (∏ i : Fin n, sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (σ i) i) =
        -(∏ i : Fin n, sg A s (σ i) i) := by
    intro s
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
    have h0 : sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (σ i0) i0 =
        -sg A s (σ i0) i0 := by
      rw [hflip_val, if_pos rfl]
    have hrest :
        (∏ i ∈ Finset.univ.erase i0,
            sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (σ i) i) =
          ∏ i ∈ Finset.univ.erase i0, sg A s (σ i) i := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hne_i : i ≠ i0 := (Finset.mem_erase.mp hi).1
      have hne_p : (σ i, i) ≠ (σ i0, i0) := by
        intro heq
        exact hne_i (congrArg Prod.snd heq)
      rw [hflip_val, if_neg hne_p]
    rw [h0, hrest, neg_mul]
  have hprod_τ : ∀ s : Fin n × Fin n → Bool,
      (∏ i : Fin n, sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (τ i) i) =
        ∏ i : Fin n, sg A s (τ i) i := by
    intro s
    refine Finset.prod_congr rfl ?_
    intro i _
    have hne_p : (τ i, i) ≠ (σ i0, i0) := by
      intro heq
      have h2 : i = i0 := congrArg Prod.snd heq
      subst h2
      exact hi0 (congrArg Prod.fst heq).symm
    rw [hflip_val, if_neg hne_p]
  have hshift :
      (∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i)) =
      ∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (σ i) i) *
          (∏ i : Fin n, sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (τ i) i) := by
    symm
    refine Fintype.sum_bijective (fun s => Function.update s (σ i0, i0) (!s (σ i0, i0)))
      (Function.Involutive.bijective fun s => ?_) _ _ (fun s => rfl)
    funext q
    by_cases hq : q = (σ i0, i0)
    · subst hq
      simp
    · simp [Function.update_of_ne hq]
  have hneg :
      (∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (σ i) i) *
          (∏ i : Fin n, sg A (Function.update s (σ i0, i0) (!s (σ i0, i0))) (τ i) i)) =
      -(∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [hprod_σ, hprod_τ, neg_mul]
  linarith

/-- The signed squared determinants sum to the permanent of the squared entries. -/
theorem gg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ s : Fin n × Fin n → Bool, Zf A s) = (2 : ℝ) ^ (n * n) * Pf A := by
  have hdet_sq : ∀ s : Fin n × Fin n → Bool,
      Zf A s =
        ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
            ((∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i)) := by
    intro s
    unfold Zf
    rw [sq, Matrix.det_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro τ _
    simp only [Units.smul_def, zsmul_eq_mul]
    ring
  simp_rw [hdet_sq]
  rw [Finset.sum_comm]
  have hswap2 :
      (∑ σ : Equiv.Perm (Fin n), ∑ s : Fin n × Fin n → Bool, ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          ((∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i))) =
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          (∑ s : Fin n × Fin n → Bool,
            (∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i)) := by
    refine Finset.sum_congr rfl ?_
    intro σ _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro τ _
    rw [Finset.mul_sum]
  rw [hswap2]
  have hdiag : ∀ σ : Equiv.Perm (Fin n),
      (∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          (∑ s : Fin n × Fin n → Bool,
            (∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (τ i) i))) =
      (2 : ℝ) ^ (n * n) * (∏ i : Fin n, (A (σ i) i) ^ 2) := by
    intro σ
    rw [Finset.sum_eq_single σ]
    · have hsign2 : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        have h : ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
        exact_mod_cast h
      rw [hsign2, one_mul]
      have hterm : ∀ s : Fin n × Fin n → Bool,
          (∏ i : Fin n, sg A s (σ i) i) * (∏ i : Fin n, sg A s (σ i) i) =
            ∏ i : Fin n, (A (σ i) i) ^ 2 := by
        intro s
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [← sg_sq A s]
        ring
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : Fintype.card (Fin n × Fin n → Bool) = 2 ^ (n * n) := by
        simp [Fintype.card_prod]
      rw [hcard]
      push_cast
      rfl
    · intro τ _ hne
      rw [sum_prod_signed_ne A σ τ hne.symm, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ σ))
  simp_rw [hdiag, ← Finset.mul_sum]
  rfl

theorem exp_le_quad (u : ℝ) (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    Real.exp u ≤ 1 + u + 3 / 4 * u ^ 2 := by
  have h := Real.exp_bound (x := u) (by rw [abs_of_nonneg h0]; exact h1) (n := 3) (by norm_num)
  have h2 := (abs_le.mp h).2
  rw [abs_of_nonneg h0] at h2
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2
  have h3 : u ^ 3 ≤ u ^ 2 := by
    have := mul_le_mul_of_nonneg_right h1 (sq_nonneg u)
    nlinarith
  nlinarith

theorem exp_neg_le_quad (δ : ℝ) (h0 : 0 ≤ δ) : Real.exp (-δ) ≤ 1 - δ + 2 / 3 * δ ^ 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg h0
  have hpos : 0 < 1 + δ + δ ^ 2 / 2 := by positivity
  rw [Real.exp_neg]
  calc (Real.exp δ)⁻¹ ≤ (1 + δ + δ ^ 2 / 2)⁻¹ := inv_anti₀ hpos h1
    _ ≤ 1 - δ + 2 / 3 * δ ^ 2 := by
        rw [inv_le_iff_one_le_mul₀ hpos]
        nlinarith [pow_nonneg h0 2, pow_nonneg h0 3, pow_nonneg h0 4]

theorem sum_prod_fin {S : Type} [Fintype S] [DecidableEq S] (g : S → ℝ) (t : ℕ) :
    ∑ ω : Fin t → S, ∏ h, g (ω h) = (∑ s, g s) ^ t := by
  have h := Finset.prod_univ_sum (fun _ : Fin t => (Finset.univ : Finset S)) (fun _ s => g s)
  rw [Fintype.piFinset_univ] at h
  rw [← h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem exp_shift (c T A B C : ℝ) (hc : 0 ≤ c) (h : c * Real.exp B ≤ T * Real.exp C)
    (hA : A ≤ B - C) : c * Real.exp A ≤ T := by
  have h1 : c * Real.exp A ≤ c * Real.exp (B - C) :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA) hc
  have h2 : c * Real.exp (B - C) = c * Real.exp B / Real.exp C := by
    rw [Real.exp_sub]
    ring
  rw [h2] at h1
  refine h1.trans ?_
  rw [div_le_iff₀ (Real.exp_pos C)]
  exact h

/-- The exponential moment bound for sums of `t` independent uniform draws. -/
theorem moment_bound {S : Type} [Fintype S] [DecidableEq S] (Y : S → ℝ) (hY0 : ∀ s, 0 ≤ Y s)
    (hY1 : ∀ s, Y s ≤ 1) (ν : ℝ) (hν : ∑ s, Y s = ν * (Fintype.card S : ℝ)) (θ a : ℝ) (t : ℕ) :
    ((Finset.univ.filter (fun ω : Fin t → S => θ * a ≤ θ * ∑ h, Y (ω h))).card : ℝ) *
        Real.exp (θ * a) ≤
      (Fintype.card S : ℝ) ^ t * Real.exp ((t:ℝ) * (ν * (Real.exp θ - 1))) := by
  have hpt : ∀ s, Real.exp (θ * Y s) ≤ 1 + Y s * (Real.exp θ - 1) := by
    intro s
    have hc := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ θ) (sub_nonneg.mpr (hY1 s))
      (hY0 s) (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at hc
    rw [mul_comm θ (Y s)]
    linarith
  have hsum : ∑ s, Real.exp (θ * Y s) ≤
      (Fintype.card S : ℝ) * Real.exp (ν * (Real.exp θ - 1)) := by
    calc ∑ s, Real.exp (θ * Y s) ≤ ∑ s, (1 + Y s * (Real.exp θ - 1)) :=
          Finset.sum_le_sum fun s _ => hpt s
      _ = (Fintype.card S : ℝ) * (1 + ν * (Real.exp θ - 1)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hν, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          ring
      _ ≤ (Fintype.card S : ℝ) * Real.exp (ν * (Real.exp θ - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
          linarith [Real.add_one_le_exp (ν * (Real.exp θ - 1))]
  have hmarkov : ((Finset.univ.filter (fun ω : Fin t → S => θ * a ≤ θ * ∑ h, Y (ω h))).card : ℝ) *
      Real.exp (θ * a) ≤ ∑ ω : Fin t → S, Real.exp (θ * ∑ h, Y (ω h)) := by
    calc ((Finset.univ.filter (fun ω : Fin t → S => θ * a ≤ θ * ∑ h, Y (ω h))).card : ℝ) *
          Real.exp (θ * a)
        = ∑ ω ∈ Finset.univ.filter (fun ω : Fin t → S => θ * a ≤ θ * ∑ h, Y (ω h)),
            Real.exp (θ * a) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω : Fin t → S => θ * a ≤ θ * ∑ h, Y (ω h)),
            Real.exp (θ * ∑ h, Y (ω h)) :=
          Finset.sum_le_sum fun ω hω => Real.exp_le_exp.mpr (Finset.mem_filter.mp hω).2
      _ ≤ ∑ ω : Fin t → S, Real.exp (θ * ∑ h, Y (ω h)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hprod : ∑ ω : Fin t → S, Real.exp (θ * ∑ h, Y (ω h)) =
      (∑ s, Real.exp (θ * Y s)) ^ t := by
    rw [← sum_prod_fin]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.mul_sum, Real.exp_sum]
  have hpow : (∑ s, Real.exp (θ * Y s)) ^ t ≤
      (Fintype.card S : ℝ) ^ t * Real.exp ((t:ℝ) * (ν * (Real.exp θ - 1))) := by
    calc (∑ s, Real.exp (θ * Y s)) ^ t
        ≤ ((Fintype.card S : ℝ) * Real.exp (ν * (Real.exp θ - 1))) ^ t :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun s _ => (Real.exp_pos _).le) hsum t
      _ = (Fintype.card S : ℝ) ^ t * Real.exp ((t:ℝ) * (ν * (Real.exp θ - 1))) := by
          rw [mul_pow, ← Real.exp_nat_mul]
  rw [hprod] at hmarkov
  exact hmarkov.trans hpow

theorem tail_upper {S : Type} [Fintype S] [DecidableEq S] (Y : S → ℝ) (hY0 : ∀ s, 0 ≤ Y s)
    (hY1 : ∀ s, Y s ≤ 1) (ν : ℝ) (hν0 : 0 ≤ ν) (hν : ∑ s, Y s = ν * (Fintype.card S : ℝ))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (t : ℕ) :
    ((Finset.univ.filter (fun ω : Fin t → S => (1 + δ) * t * ν ≤ ∑ h, Y (ω h))).card : ℝ) *
        Real.exp (δ ^ 2 * t * ν / 3) ≤ (Fintype.card S : ℝ) ^ t := by
  have hu0 : 0 ≤ 2 * δ / 3 := by positivity
  have hu1 : 2 * δ / 3 ≤ 1 := by linarith
  have hm := moment_bound Y hY0 hY1 ν hν (2 * δ / 3) ((1 + δ) * t * ν) t
  have hsub : (Finset.univ.filter (fun ω : Fin t → S => (1 + δ) * t * ν ≤ ∑ h, Y (ω h))) ⊆
      (Finset.univ.filter (fun ω : Fin t → S =>
        2 * δ / 3 * ((1 + δ) * t * ν) ≤ 2 * δ / 3 * ∑ h, Y (ω h))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, mul_le_mul_of_nonneg_left hω.2 hu0⟩
  have hcard : ((Finset.univ.filter
      (fun ω : Fin t → S => (1 + δ) * t * ν ≤ ∑ h, Y (ω h))).card : ℝ) ≤
      ((Finset.univ.filter (fun ω : Fin t → S =>
        2 * δ / 3 * ((1 + δ) * t * ν) ≤ 2 * δ / 3 * ∑ h, Y (ω h))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hE := exp_le_quad (2 * δ / 3) hu0 hu1
  have htν : 0 ≤ (t:ℝ) * ν := mul_nonneg (Nat.cast_nonneg t) hν0
  refine exp_shift _ _ _ (2 * δ / 3 * ((1 + δ) * t * ν))
    ((t:ℝ) * (ν * (Real.exp (2 * δ / 3) - 1))) (Nat.cast_nonneg _) ?_ ?_
  · exact (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans hm
  · have h5 : Real.exp (2 * δ / 3) - 1 ≤ 2 * δ / 3 + δ ^ 2 / 3 := by nlinarith
    have h6 := mul_le_mul_of_nonneg_left h5 htν
    nlinarith

theorem tail_lower {S : Type} [Fintype S] [DecidableEq S] (Y : S → ℝ) (hY0 : ∀ s, 0 ≤ Y s)
    (hY1 : ∀ s, Y s ≤ 1) (ν : ℝ) (hν0 : 0 ≤ ν) (hν : ∑ s, Y s = ν * (Fintype.card S : ℝ))
    (δ : ℝ) (hδ0 : 0 ≤ δ) (t : ℕ) :
    ((Finset.univ.filter (fun ω : Fin t → S => ∑ h, Y (ω h) ≤ (1 - δ) * t * ν)).card : ℝ) *
        Real.exp (δ ^ 2 * t * ν / 3) ≤ (Fintype.card S : ℝ) ^ t := by
  have hm := moment_bound Y hY0 hY1 ν hν (-δ) ((1 - δ) * t * ν) t
  have hsub : (Finset.univ.filter (fun ω : Fin t → S => ∑ h, Y (ω h) ≤ (1 - δ) * t * ν)) ⊆
      (Finset.univ.filter (fun ω : Fin t → S =>
        -δ * ((1 - δ) * t * ν) ≤ -δ * ∑ h, Y (ω h))) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨hω.1, mul_le_mul_of_nonpos_left hω.2 (neg_nonpos.mpr hδ0)⟩
  have hcard : ((Finset.univ.filter
      (fun ω : Fin t → S => ∑ h, Y (ω h) ≤ (1 - δ) * t * ν)).card : ℝ) ≤
      ((Finset.univ.filter (fun ω : Fin t → S =>
        -δ * ((1 - δ) * t * ν) ≤ -δ * ∑ h, Y (ω h))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hE := exp_neg_le_quad δ hδ0
  have htν : 0 ≤ (t:ℝ) * ν := mul_nonneg (Nat.cast_nonneg t) hν0
  refine exp_shift _ _ _ (-δ * ((1 - δ) * t * ν))
    ((t:ℝ) * (ν * (Real.exp (-δ) - 1))) (Nat.cast_nonneg _) ?_ ?_
  · exact (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le).trans hm
  · have h5 : Real.exp (-δ) - 1 ≤ -δ + 2 / 3 * δ ^ 2 := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 htν
    nlinarith

/-- For one table: few lists of `t` sign patterns miss its permanent by more than `1 ± δ`. -/
theorem bad_count {n : ℕ} (hn : 0 < n) (G : Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (t : ℕ) :
    ((Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
        ¬ ((1 - δ) * t * Pf G ≤ ∑ h, Zf G (ω h) ∧
          ∑ h, Zf G (ω h) ≤ (1 + δ) * t * Pf G))).card : ℝ) *
      Real.exp (δ ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3) ≤
      2 * ((2:ℝ) ^ (n * n)) ^ t := by
  have hnn : (0:ℝ) < (n:ℝ) ^ n := pow_pos (by exact_mod_cast hn) n
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hcardS : (Fintype.card (Fin n × Fin n → Bool) : ℝ) = (2:ℝ) ^ (n * n) := by
    simp [Fintype.card_prod]
  rcases eq_or_lt_of_le (Pf_nonneg G) with hP0 | hPpos
  · have hZ : ∀ s, Zf G s = 0 := by
      intro s
      have h := Zf_le G s
      rw [← hP0, mul_zero] at h
      have h2 := Zf_nonneg G s
      nlinarith
    have hempty : (Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
        ¬ ((1 - δ) * t * Pf G ≤ ∑ h, Zf G (ω h) ∧
          ∑ h, Zf G (ω h) ≤ (1 + δ) * t * Pf G))) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun ω _ => ?_)
      simp [hZ, ← hP0]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    positivity
  · have hden : 0 < (n:ℝ) ^ n * Pf G := mul_pos hnn hPpos
    have hY0 : ∀ s : Fin n × Fin n → Bool,
        0 ≤ Zf G s * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) :=
      fun s => div_nonneg (mul_nonneg (Zf_nonneg G s) hfac.le) hden.le
    have hY1 : ∀ s : Fin n × Fin n → Bool,
        Zf G s * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) ≤ 1 :=
      fun s => (div_le_one hden).mpr (Zf_le G s)
    have hν : ∑ s : Fin n × Fin n → Bool, Zf G s * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) =
        ((n.factorial : ℝ) / (n:ℝ) ^ n) * (Fintype.card (Fin n × Fin n → Bool) : ℝ) := by
      rw [hcardS, ← Finset.sum_div, ← Finset.sum_mul, gg]
      field_simp
    have hsumY : ∀ ω : Fin t → (Fin n × Fin n → Bool),
        ∑ h, Zf G (ω h) * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) =
          (∑ h, Zf G (ω h)) * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) := by
      intro ω
      rw [← Finset.sum_div, ← Finset.sum_mul]
    have hν0 : (0:ℝ) ≤ (n.factorial : ℝ) / (n:ℝ) ^ n := by positivity
    have hup := tail_upper (fun s : Fin n × Fin n → Bool =>
      Zf G s * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G)) hY0 hY1 _ hν0 hν δ hδ0 hδ1 t
    have hlo := tail_lower (fun s : Fin n × Fin n → Bool =>
      Zf G s * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G)) hY0 hY1 _ hν0 hν δ hδ0 t
    have hsub : (Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
        ¬ ((1 - δ) * t * Pf G ≤ ∑ h, Zf G (ω h) ∧
          ∑ h, Zf G (ω h) ≤ (1 + δ) * t * Pf G))) ⊆
        (Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          (1 + δ) * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) ≤
            ∑ h, Zf G (ω h) * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G))) ∪
        (Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          ∑ h, Zf G (ω h) * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) ≤
            (1 - δ) * t * ((n.factorial : ℝ) / (n:ℝ) ^ n))) := by
      intro ω hω
      rw [Finset.mem_filter] at hω
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases h1 : (1 - δ) * t * Pf G ≤ ∑ h, Zf G (ω h)
      · left
        have h2 : ¬ (∑ h, Zf G (ω h) ≤ (1 + δ) * t * Pf G) := fun h2 => hω.2 ⟨h1, h2⟩
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hsumY, le_div_iff₀ hden]
        have h3 := (not_le.mp h2).le
        have e : (1 + δ) * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) * ((n:ℝ) ^ n * Pf G) =
            ((1 + δ) * t * Pf G) * (n.factorial : ℝ) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_right h3 hfac.le
      · right
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hsumY, div_le_iff₀ hden]
        have h3 := (not_le.mp h1).le
        have e : (1 - δ) * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) * ((n:ℝ) ^ n * Pf G) =
            ((1 - δ) * t * Pf G) * (n.factorial : ℝ) := by
          field_simp
        rw [e]
        exact mul_le_mul_of_nonneg_right h3 hfac.le
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcard' : ((Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
        ¬ ((1 - δ) * t * Pf G ≤ ∑ h, Zf G (ω h) ∧
          ∑ h, Zf G (ω h) ≤ (1 + δ) * t * Pf G))).card : ℝ) ≤
        ((Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          (1 + δ) * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) ≤
            ∑ h, Zf G (ω h) * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G))).card : ℝ) +
        ((Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          ∑ h, Zf G (ω h) * (n.factorial : ℝ) / ((n:ℝ) ^ n * Pf G) ≤
            (1 - δ) * t * ((n.factorial : ℝ) / (n:ℝ) ^ n))).card : ℝ) := by
      exact_mod_cast hcard
    rw [hcardS] at hup hlo
    have hmul := mul_le_mul_of_nonneg_right hcard'
      (Real.exp_pos (δ ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3)).le
    refine hmul.trans ((add_mul _ _ _).le.trans ?_)
    linarith

/-- One list of sign patterns is good for every table of a finite family. -/
theorem exists_good {n : ℕ} (hn : 0 < n) {κ : Type} [Fintype κ]
    (Gm : κ → Matrix (Fin n) (Fin n) ℝ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (t : ℕ)
    (hbig : 2 * (Fintype.card κ : ℝ) <
      Real.exp (δ ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3)) :
    ∃ ω : Fin t → (Fin n × Fin n → Bool), ∀ k : κ,
      (1 - δ) * t * Pf (Gm k) ≤ ∑ h, Zf (Gm k) (ω h) ∧
        ∑ h, Zf (Gm k) (ω h) ≤ (1 + δ) * t * Pf (Gm k) := by
  classical
  by_contra hcon
  have hall : ∀ ω : Fin t → (Fin n × Fin n → Bool), ∃ k : κ,
      ¬ ((1 - δ) * t * Pf (Gm k) ≤ ∑ h, Zf (Gm k) (ω h) ∧
        ∑ h, Zf (Gm k) (ω h) ≤ (1 + δ) * t * Pf (Gm k)) := by
    intro ω
    by_contra h
    exact hcon ⟨ω, fun k => not_not.mp (not_exists.mp h k)⟩
  have hcover : (Finset.univ : Finset (Fin t → (Fin n × Fin n → Bool))) ⊆
      Finset.univ.biUnion (fun k : κ =>
        Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          ¬ ((1 - δ) * t * Pf (Gm k) ≤ ∑ h, Zf (Gm k) (ω h) ∧
            ∑ h, Zf (Gm k) (ω h) ≤ (1 + δ) * t * Pf (Gm k)))) := by
    intro ω _
    obtain ⟨k, hk⟩ := hall ω
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
      Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hk⟩⟩
  have h0 := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  rw [Finset.card_univ] at h0
  have h1 : (Fintype.card (Fin t → (Fin n × Fin n → Bool)) : ℝ) ≤
      ∑ k : κ, ((Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          ¬ ((1 - δ) * t * Pf (Gm k) ≤ ∑ h, Zf (Gm k) (ω h) ∧
            ∑ h, Zf (Gm k) (ω h) ≤ (1 + δ) * t * Pf (Gm k)))).card : ℝ) := by
    exact_mod_cast h0
  have hcardΩ : (Fintype.card (Fin t → (Fin n × Fin n → Bool)) : ℝ) = ((2:ℝ) ^ (n * n)) ^ t := by
    simp [Fintype.card_prod]
  have hEpos : 0 < Real.exp (δ ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3) := Real.exp_pos _
  have h2 : (∑ k : κ, ((Finset.univ.filter (fun ω : Fin t → (Fin n × Fin n → Bool) =>
          ¬ ((1 - δ) * t * Pf (Gm k) ≤ ∑ h, Zf (Gm k) (ω h) ∧
            ∑ h, Zf (Gm k) (ω h) ≤ (1 + δ) * t * Pf (Gm k)))).card : ℝ)) *
        Real.exp (δ ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3) ≤
      (Fintype.card κ : ℝ) * (2 * ((2:ℝ) ^ (n * n)) ^ t) := by
    rw [Finset.sum_mul]
    refine (Finset.sum_le_sum fun k _ => bad_count hn (Gm k) δ hδ0 hδ1 t).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h3 := (mul_le_mul_of_nonneg_right h1 hEpos.le).trans h2
  rw [hcardΩ] at h3
  have hpos : (0:ℝ) < ((2:ℝ) ^ (n * n)) ^ t := by positivity
  have h4 : ((2:ℝ) ^ (n * n)) ^ t *
      Real.exp (δ ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3) ≤
      ((2:ℝ) ^ (n * n)) ^ t * (2 * (Fintype.card κ : ℝ)) := by
    linarith
  have h5 := le_of_mul_le_mul_left h4 hpos
  linarith

/-- Rows of length at most one that are close: the determinants are close. -/
theorem det_row_lipschitz {n : ℕ} (B B' : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hB : ∀ i, ∑ j, (B i j) ^ 2 ≤ 1) (hB' : ∀ i, ∑ j, (B' i j) ^ 2 ≤ 1)
    (hd : ∀ i, ∑ j, (B' i j - B i j) ^ 2 ≤ ε ^ 2) :
    |B'.det - B.det| ≤ n * ε := by
  have habs : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := fun a b =>
    abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b], by linarith [le_abs_self a, le_abs_self b]⟩
  have key : ∀ k : ℕ, k ≤ n →
      |(Matrix.of fun (i : Fin n) (j : Fin n) =>
        if (i : ℕ) < k then B' i j else B i j).det - B.det| ≤ k * ε := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : (Matrix.of fun (i : Fin n) (j : Fin n) =>
          if (i : ℕ) < 0 then B' i j else B i j) = B := by
        ext i j
        simp
      rw [h0]
      simp
    | succ k ih =>
      intro hk
      have hkn : k < n := hk
      have ih' := ih (by omega)
      have h1 : (Matrix.of fun (i : Fin n) (j : Fin n) =>
          if (i : ℕ) < k + 1 then B' i j else B i j) =
          (Matrix.of fun (i : Fin n) (j : Fin n) =>
            if (i : ℕ) < k then B' i j else B i j).updateRow ⟨k, hkn⟩
            ((fun j => B' ⟨k, hkn⟩ j - B ⟨k, hkn⟩ j) + fun j => B ⟨k, hkn⟩ j) := by
        ext i j
        rw [Matrix.updateRow_apply]
        by_cases hi : i = ⟨k, hkn⟩
        · subst hi
          simp
        · have hik : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
          by_cases h2 : (i : ℕ) < k
          · have h3 : (i : ℕ) ≤ k := by omega
            simp [hi, h2, h3]
          · have h3 : ¬ (i : ℕ) ≤ k := by omega
            simp [hi, h2, h3]
      have h2 : (Matrix.of fun (i : Fin n) (j : Fin n) =>
            if (i : ℕ) < k then B' i j else B i j).updateRow ⟨k, hkn⟩
            (fun j => B ⟨k, hkn⟩ j) =
          (Matrix.of fun (i : Fin n) (j : Fin n) =>
            if (i : ℕ) < k then B' i j else B i j) := by
        ext i j
        rw [Matrix.updateRow_apply]
        by_cases hi : i = ⟨k, hkn⟩
        · subst hi
          simp
        · simp [hi]
      have hprod : ∏ i, ∑ j, (((Matrix.of fun (i : Fin n) (j : Fin n) =>
            if (i : ℕ) < k then B' i j else B i j).updateRow ⟨k, hkn⟩
            (fun j => B' ⟨k, hkn⟩ j - B ⟨k, hkn⟩ j)) i j) ^ 2 ≤ ε ^ 2 := by
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hkn⟩ : Fin n))]
        have ha : ∑ j, (((Matrix.of fun (i : Fin n) (j : Fin n) =>
            if (i : ℕ) < k then B' i j else B i j).updateRow ⟨k, hkn⟩
            (fun j => B' ⟨k, hkn⟩ j - B ⟨k, hkn⟩ j)) ⟨k, hkn⟩ j) ^ 2 ≤ ε ^ 2 := by
          simp only [Matrix.updateRow_self]
          exact hd ⟨k, hkn⟩
        have hb : ∏ i ∈ Finset.univ.erase (⟨k, hkn⟩ : Fin n), ∑ j,
            (((Matrix.of fun (i : Fin n) (j : Fin n) =>
            if (i : ℕ) < k then B' i j else B i j).updateRow ⟨k, hkn⟩
            (fun j => B' ⟨k, hkn⟩ j - B ⟨k, hkn⟩ j)) i j) ^ 2 ≤ 1 := by
          refine Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
            (fun i hi => ?_)
          have hne : i ≠ ⟨k, hkn⟩ := (Finset.mem_erase.mp hi).1
          simp only [Matrix.updateRow_ne hne, Matrix.of_apply]
          by_cases h3 : (i : ℕ) < k
          · simp only [h3, ite_true]
            exact hB' i
          · simp only [h3, ite_false]
            exact hB i
        calc _ ≤ ε ^ 2 * 1 := mul_le_mul ha hb
              (Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
              (sq_nonneg ε)
          _ = ε ^ 2 := mul_one _
      have hD := abs_le_of_sq_le_sq ((hadamard _).trans hprod) hε
      rw [h1, Matrix.det_updateRow_add, h2]
      have e3 : ∀ a b c : ℝ, a + b - c = a + (b - c) := fun a b c => by ring
      rw [e3]
      refine (habs _ _).trans ?_
      have e4 : ((k + 1 : ℕ) : ℝ) * ε = ε + k * ε := by
        push_cast
        ring
      rw [e4]
      exact add_le_add hD ih'
  have h := key n le_rfl
  have hfull : (Matrix.of fun (i : Fin n) (j : Fin n) =>
      if (i : ℕ) < n then B' i j else B i j) = B' := by
    ext i j
    simp
  rw [hfull] at h
  exact h

theorem Zf_close {n : ℕ} (A G : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ i, ∑ j, (A i j) ^ 2 ≤ 1) (hG : ∀ i, ∑ j, (G i j) ^ 2 ≤ 1)
    (hd : ∀ i, ∑ j, (A i j - G i j) ^ 2 ≤ ε ^ 2) (s : Fin n × Fin n → Bool) :
    |Zf A s - Zf G s| ≤ 2 * n * ε := by
  have hsgA : ∀ i, ∑ j, (sg A s i j) ^ 2 ≤ 1 := fun i => by
    simp only [sg_sq]
    exact hA i
  have hsgG : ∀ i, ∑ j, (sg G s i j) ^ 2 ≤ 1 := fun i => by
    simp only [sg_sq]
    exact hG i
  have hsd : ∀ i, ∑ j, (sg A s i j - sg G s i j) ^ 2 ≤ ε ^ 2 := by
    intro i
    have h1 : ∀ j, (sg A s i j - sg G s i j) ^ 2 = (A i j - G i j) ^ 2 := by
      intro j
      unfold sg
      split_ifs <;> ring
    simp only [h1]
    exact hd i
  have h1 := det_row_lipschitz (sg G s) (sg A s) ε hε hsgG hsgA hsd
  have hdA : |(sg A s).det| ≤ 1 := by
    refine abs_le_of_sq_le_sq ?_ zero_le_one
    have hp : ∏ i, ∑ j, (sg A s i j) ^ 2 ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (fun i _ => hsgA i)
    linarith [hadamard (sg A s)]
  have hdG : |(sg G s).det| ≤ 1 := by
    refine abs_le_of_sq_le_sq ?_ zero_le_one
    have hp : ∏ i, ∑ j, (sg G s i j) ^ 2 ≤ 1 :=
      Finset.prod_le_one₀ (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (fun i _ => hsgG i)
    linarith [hadamard (sg G s)]
  unfold Zf
  have e : (sg A s).det ^ 2 - (sg G s).det ^ 2 =
      ((sg A s).det - (sg G s).det) * ((sg A s).det + (sg G s).det) := by ring
  rw [e, abs_mul]
  have h2 : |(sg A s).det + (sg G s).det| ≤ 2 :=
    abs_le.mpr ⟨by linarith [neg_abs_le (sg A s).det, neg_abs_le (sg G s).det],
      by linarith [le_abs_self (sg A s).det, le_abs_self (sg G s).det]⟩
  have hnε : 0 ≤ (n:ℝ) * ε := mul_nonneg (Nat.cast_nonneg n) hε
  calc |(sg A s).det - (sg G s).det| * |(sg A s).det + (sg G s).det| ≤ ((n:ℝ) * ε) * 2 :=
        mul_le_mul h1 h2 (abs_nonneg _) hnε
    _ = 2 * n * ε := by ring

theorem Pf_close {n : ℕ} (A G : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hA : ∀ i, ∑ j, (A i j) ^ 2 ≤ 1) (hG : ∀ i, ∑ j, (G i j) ^ 2 ≤ 1)
    (hd : ∀ i, ∑ j, (A i j - G i j) ^ 2 ≤ ε ^ 2) :
    |Pf A - Pf G| ≤ 2 * n * ε := by
  have h2pos : (0:ℝ) < (2:ℝ) ^ (n * n) := by positivity
  have h3 : |(∑ s : Fin n × Fin n → Bool, Zf A s) - ∑ s : Fin n × Fin n → Bool, Zf G s| ≤
      (2:ℝ) ^ (n * n) * (2 * n * ε) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun s _ => Zf_close A G ε hε hA hG hd s).trans ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Fin n × Fin n → Bool) : ℝ) = (2:ℝ) ^ (n * n) := by
      simp [Fintype.card_prod]
    rw [hcard]
  rw [gg, gg, ← mul_sub, abs_mul, abs_of_pos h2pos] at h3
  exact le_of_mul_le_mul_left h3 h2pos

/-- Rounding toward zero onto the grid of multiples of `1 / M` in `[-1, 1]`. -/
theorem round_entry (M : ℕ) (hM : 0 < M) (a : ℝ) (ha : a ^ 2 ≤ 1) :
    ∃ k : Fin (2 * M + 1), (((k : ℕ) : ℝ) / M - 1) ^ 2 ≤ a ^ 2 ∧
      (a - (((k : ℕ) : ℝ) / M - 1)) ^ 2 ≤ (1 / (M:ℝ)) ^ 2 := by
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have ha1 : |a| ≤ 1 := abs_le_of_sq_le_sq (by simpa using ha) zero_le_one
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha1
  rcases le_or_gt 0 a with h0 | h0
  · have hfl : ⌊a * M⌋₊ ≤ M := by
      have h1 : a * M ≤ (M:ℝ) := by nlinarith
      exact Nat.floor_le_of_le h1
    have h1 : ((⌊a * M⌋₊ : ℕ) : ℝ) ≤ a * M := Nat.floor_le (by positivity)
    have h2 : a * M < (⌊a * M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    refine ⟨⟨M + ⌊a * M⌋₊, by omega⟩, ?_, ?_⟩
    · have e : (((M + ⌊a * M⌋₊ : ℕ) : ℝ) / M - 1) = (⌊a * M⌋₊ : ℝ) / M := by
        push_cast
        field_simp
        ring
      simp only [e]
      have h3 : (⌊a * M⌋₊ : ℝ) / M ≤ a := by
        rw [div_le_iff₀ hMR]
        exact h1
      exact pow_le_pow_left₀ (by positivity) h3 2
    · have e : (((M + ⌊a * M⌋₊ : ℕ) : ℝ) / M - 1) = (⌊a * M⌋₊ : ℝ) / M := by
        push_cast
        field_simp
        ring
      simp only [e]
      have h3 : (⌊a * M⌋₊ : ℝ) / M ≤ a := by
        rw [div_le_iff₀ hMR]
        exact h1
      have h4 : a - (⌊a * M⌋₊ : ℝ) / M ≤ 1 / (M:ℝ) := by
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hMR]
        linarith
      exact pow_le_pow_left₀ (by linarith) h4 2
  · have hfl : ⌊-a * M⌋₊ ≤ M := by
      have h1 : -a * M ≤ (M:ℝ) := by nlinarith
      exact Nat.floor_le_of_le h1
    have hna : 0 ≤ -a * M := by nlinarith
    have h1 : ((⌊-a * M⌋₊ : ℕ) : ℝ) ≤ -a * M := Nat.floor_le hna
    have h2 : -a * M < (⌊-a * M⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    refine ⟨⟨M - ⌊-a * M⌋₊, by omega⟩, ?_, ?_⟩
    · have e : (((M - ⌊-a * M⌋₊ : ℕ) : ℝ) / M - 1) = -((⌊-a * M⌋₊ : ℝ) / M) := by
        rw [Nat.cast_sub hfl]
        field_simp
        ring
      simp only [e]
      have h3 : (⌊-a * M⌋₊ : ℝ) / M ≤ -a := by
        rw [div_le_iff₀ hMR]
        exact h1
      have h5 : (-((⌊-a * M⌋₊ : ℝ) / M)) ^ 2 = ((⌊-a * M⌋₊ : ℝ) / M) ^ 2 := by ring
      have h6 : a ^ 2 = (-a) ^ 2 := by ring
      rw [h5, h6]
      exact pow_le_pow_left₀ (by positivity) h3 2
    · have e : (((M - ⌊-a * M⌋₊ : ℕ) : ℝ) / M - 1) = -((⌊-a * M⌋₊ : ℝ) / M) := by
        rw [Nat.cast_sub hfl]
        field_simp
        ring
      simp only [e]
      have h3 : (⌊-a * M⌋₊ : ℝ) / M ≤ -a := by
        rw [div_le_iff₀ hMR]
        exact h1
      have h4 : -a - (⌊-a * M⌋₊ : ℝ) / M ≤ 1 / (M:ℝ) := by
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hMR]
        linarith
      have h5 : (a - -((⌊-a * M⌋₊ : ℝ) / M)) ^ 2 = (-a - (⌊-a * M⌋₊ : ℝ) / M) ^ 2 := by ring
      rw [h5]
      exact pow_le_pow_left₀ (by linarith) h4 2

/-- Rows and columns can be scaled so that every row has length one and the permanent of the
squared entries stays above half of the least value a doubly balanced table can have. -/
theorem exists_scaling {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hP : 0 < Pf A) :
    ∃ (A' : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ), 0 < ρ ∧ (∀ i, ∑ j, (A' i j) ^ 2 = 1) ∧
      Pf A' = ρ * Pf A ∧ (∀ s, Zf A' s = ρ * Zf A s) ∧
      (n.factorial : ℝ) ≤ 2 * (n:ℝ) ^ n * Pf A' := by
  have hnn : (0:ℝ) < (n:ℝ) ^ n := pow_pos (by exact_mod_cast hn) n
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hex : ∃ x : Fin n → ℝ, (∀ j, 0 < x j) ∧
      (∏ i, ∑ j, (A i j) ^ 2 * x j) <
        (2 * (n:ℝ) ^ n / (n.factorial : ℝ) * Pf A) * ∏ j, x j := by
    by_contra hcon
    have hall : ∀ x : Fin n → ℝ, (∀ j, 0 < x j) →
        (2 * (n:ℝ) ^ n / (n.factorial : ℝ) * Pf A) * ∏ j, x j ≤
          ∏ i, ∑ j, (A i j) ^ 2 * x j :=
      fun x hx => not_lt.mp (fun hlt => hcon ⟨x, hx, hlt⟩)
    have h := gurvits (fun i j => (A i j) ^ 2) (fun i j => sq_nonneg _) _ (by positivity) hall
    have e : 2 * (n:ℝ) ^ n / (n.factorial : ℝ) * Pf A * (n.factorial : ℝ) =
        2 * ((n:ℝ) ^ n * Pf A) := by
      field_simp
    rw [e] at h
    have hpos : 0 < (n:ℝ) ^ n * Pf A := mul_pos hnn hP
    have h' : 2 * ((n:ℝ) ^ n * Pf A) ≤ (n:ℝ) ^ n * Pf A := h
    linarith
  obtain ⟨x, hx, hlt⟩ := hex
  have hr : ∀ i, 0 < ∑ j, (A i j) ^ 2 * x j := by
    intro i
    by_contra hneg
    have hzero : ∑ j, (A i j) ^ 2 * x j = 0 :=
      le_antisymm (not_lt.mp hneg)
        (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hx j).le)
    have hrow : ∀ j, A i j = 0 := by
      intro j
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (sq_nonneg (A i j)) (hx j).le)).mp hzero j (Finset.mem_univ j)
      rcases mul_eq_zero.mp h1 with h | h
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
      · exact absurd h (hx j).ne'
    have hPz : Pf A = 0 := by
      unfold Pf
      refine Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (Finset.mem_univ (σ.symm i)) ?_
      rw [Equiv.apply_symm_apply, hrow]
      ring
    exact hP.ne' hPz
  have hRpos : 0 < ∏ i, ∑ j, (A i j) ^ 2 * x j := Finset.prod_pos fun i _ => hr i
  have hXpos : 0 < ∏ j, x j := Finset.prod_pos fun j _ => hx j
  have hu2 : ∀ i, (1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j)) ^ 2 = 1 / ∑ j, (A i j) ^ 2 * x j :=
    fun i => by rw [div_pow, one_pow, Real.sq_sqrt (hr i).le]
  have hv2 : ∀ j, (Real.sqrt (x j)) ^ 2 = x j := fun j => Real.sq_sqrt (hx j).le
  have hupos : ∀ i, 0 < 1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j) :=
    fun i => one_div_pos.mpr (Real.sqrt_pos.mpr (hr i))
  have hvpos : ∀ j, 0 < Real.sqrt (x j) := fun j => Real.sqrt_pos.mpr (hx j)
  have hρ : (∏ i, (1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j))) ^ 2 * (∏ j, Real.sqrt (x j)) ^ 2 =
      (∏ j, x j) / ∏ i, ∑ j, (A i j) ^ 2 * x j := by
    rw [← Finset.prod_pow, ← Finset.prod_pow]
    simp only [hu2, hv2]
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    field_simp
  have hPf : Pf (fun i j => 1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j) * (Real.sqrt (x j) * A i j)) =
      ((∏ i, (1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j))) ^ 2 * (∏ j, Real.sqrt (x j)) ^ 2) *
        Pf A := by
    unfold Pf
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : ∀ j, (1 / Real.sqrt (∑ j', (A (σ j) j') ^ 2 * x j') *
        (Real.sqrt (x j) * A (σ j) j)) ^ 2 =
        (1 / Real.sqrt (∑ j', (A (σ j) j') ^ 2 * x j')) ^ 2 *
          ((Real.sqrt (x j)) ^ 2 * (A (σ j) j) ^ 2) := fun j => by ring
    simp only [h1]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow,
      Equiv.prod_comp σ (fun i => 1 / Real.sqrt (∑ j', (A i j') ^ 2 * x j'))]
    ring
  refine ⟨fun i j => 1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j) * (Real.sqrt (x j) * A i j),
    (∏ i, (1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j))) ^ 2 * (∏ j, Real.sqrt (x j)) ^ 2,
    ?_, ?_, hPf, ?_, ?_⟩
  · have h1 : 0 < ∏ i, (1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j)) := Finset.prod_pos fun i _ => hupos i
    have h2 : 0 < ∏ j, Real.sqrt (x j) := Finset.prod_pos fun j _ => hvpos j
    positivity
  · intro i
    have h1 : ∀ j, (1 / Real.sqrt (∑ j', (A i j') ^ 2 * x j') * (Real.sqrt (x j) * A i j)) ^ 2 =
        (1 / ∑ j', (A i j') ^ 2 * x j') * ((A i j) ^ 2 * x j) := by
      intro j
      rw [mul_pow, mul_pow, hu2, hv2]
      ring
    simp only [h1]
    rw [← Finset.mul_sum]
    exact one_div_mul_cancel (hr i).ne'
  · intro s
    unfold Zf
    have hsg : sg (fun i j => 1 / Real.sqrt (∑ j, (A i j) ^ 2 * x j) *
        (Real.sqrt (x j) * A i j)) s =
        Matrix.of (fun i j => 1 / Real.sqrt (∑ j', (A i j') ^ 2 * x j') *
          (Matrix.of (fun i j => Real.sqrt (x j) * sg A s i j)) i j) := by
      ext i j
      simp only [sg, Matrix.of_apply]
      split_ifs <;> ring
    rw [hsg, Matrix.det_mul_column, Matrix.det_mul_row]
    ring
  · rw [hPf, hρ]
    have e2 : (n.factorial : ℝ) * ((2 * (n:ℝ) ^ n / (n.factorial : ℝ) * Pf A) * ∏ j, x j) =
        2 * (n:ℝ) ^ n * Pf A * ∏ j, x j := by
      field_simp
    have h3 := mul_lt_mul_of_pos_left hlt hfac
    rw [e2] at h3
    have e3 : 2 * (n:ℝ) ^ n * ((∏ j, x j) / (∏ i, ∑ j, (A i j) ^ 2 * x j) * Pf A) =
        (2 * (n:ℝ) ^ n * Pf A * ∏ j, x j) / ∏ i, ∑ j, (A i j) ^ 2 * x j := by
      ring
    rw [e3, le_div_iff₀ hRpos]
    exact h3.le

theorem final_ineq (p t P' PG T' TG e : ℝ) (hp : 2 ≤ p) (ht : 0 ≤ t) (he : 0 ≤ e)
    (hT : |T' - TG| ≤ t * e) (hP : |P' - PG| ≤ e)
    (hlo : (1 - 1 / (2 * p)) * t * PG ≤ TG) (hhi : TG ≤ (1 + 1 / (2 * p)) * t * PG)
    (hsmall : (4 * p + 1) * e ≤ P') :
    (p - 1) * t * P' ≤ p * T' ∧ p * T' ≤ (p + 1) * t * P' := by
  have hp0 : 0 < p := by linarith
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  obtain ⟨hP1, hP2⟩ := abs_le.mp hP
  have a1 : p * TG ≤ (p + 1 / 2) * (t * PG) := by
    have h1 := mul_le_mul_of_nonneg_left hhi hp0.le
    have e1 : p * ((1 + 1 / (2 * p)) * t * PG) = (p + 1 / 2) * (t * PG) := by
      field_simp
    linarith
  have a2 : (p - 1 / 2) * (t * PG) ≤ p * TG := by
    have h1 := mul_le_mul_of_nonneg_left hlo hp0.le
    have e1 : p * ((1 - 1 / (2 * p)) * t * PG) = (p - 1 / 2) * (t * PG) := by
      field_simp
    linarith
  have b1 : t * PG ≤ t * P' + t * e := by
    have h1 := mul_le_mul_of_nonneg_left (show PG ≤ P' + e by linarith) ht
    linarith
  have b2 : t * P' - t * e ≤ t * PG := by
    have h1 := mul_le_mul_of_nonneg_left (show P' - e ≤ PG by linarith) ht
    linarith
  have c1 : (p + 1 / 2) * (t * PG) ≤ (p + 1 / 2) * (t * P' + t * e) :=
    mul_le_mul_of_nonneg_left b1 (by linarith)
  have c2 : (p - 1 / 2) * (t * P' - t * e) ≤ (p - 1 / 2) * (t * PG) :=
    mul_le_mul_of_nonneg_left b2 (by linarith)
  have d1 : p * T' ≤ p * TG + p * (t * e) := by
    have h1 := mul_le_mul_of_nonneg_left (show T' ≤ TG + t * e by linarith) hp0.le
    linarith
  have d2 : p * TG - p * (t * e) ≤ p * T' := by
    have h1 := mul_le_mul_of_nonneg_left (show TG - t * e ≤ T' by linarith) hp0.le
    linarith
  have m3 : (4 * p + 1) * (t * e) ≤ t * P' := by
    have h1 := mul_le_mul_of_nonneg_left hsmall ht
    linarith
  have hte : 0 ≤ t * e := mul_nonneg ht he
  constructor
  · nlinarith
  · nlinarith

theorem main_aux (n p : ℕ) (hn : 0 < n) (hp : 2 ≤ p) :
    ∃ (t : ℕ) (s : Fin t → Fin n × Fin n → Bool), 0 < t ∧
      (t : ℝ) ≤ 1 + 12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
        (2 + (n:ℝ) ^ 2 *
          Real.log (2 * ((32 * p * n ^ 2 * (n ^ n / n.factorial + 1) : ℕ) : ℝ) + 1)) ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ,
        ((p:ℝ) - 1) * t * Pf A ≤ (p:ℝ) * ∑ h : Fin t, Zf A (s h) ∧
        (p:ℝ) * ∑ h : Fin t, Zf A (s h) ≤ ((p:ℝ) + 1) * t * Pf A := by
  classical
  have hp0 : 0 < p := by omega
  have hMpos : 0 < 32 * p * n ^ 2 * (n ^ n / n.factorial + 1) :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hp0) (pow_pos hn 2)) (Nat.succ_pos _)
  have hMcast : ((32 * p * n ^ 2 * (n ^ n / n.factorial + 1) : ℕ) : ℝ) =
      32 * (p:ℝ) * (n:ℝ) ^ 2 * (((n ^ n / n.factorial : ℕ) : ℝ) + 1) := by
    push_cast
    ring
  have hq : (n:ℝ) ^ n < (n.factorial : ℝ) * (((n ^ n / n.factorial : ℕ) : ℝ) + 1) := by
    exact_mod_cast Nat.lt_mul_div_succ (n ^ n) (Nat.factorial_pos n)
  generalize hMdef : 32 * p * n ^ 2 * (n ^ n / n.factorial + 1) = M at hMpos hMcast ⊢
  have hMR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
  have hnn : (0:ℝ) < (n:ℝ) ^ n := pow_pos (by exact_mod_cast hn) n
  have hnR : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hfac : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
  have hKpos : 0 < (n:ℝ) ^ n / (n.factorial : ℝ) := div_pos hnn hfac
  have hL0 : 0 ≤ Real.log (2 * (M:ℝ) + 1) := Real.log_nonneg (by linarith)
  have hT0nn : 0 ≤ 12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
      (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) := by positivity
  have htle : (((⌊12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
      (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1))⌋₊ + 1 : ℕ)) : ℝ) ≤
      1 + 12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
        (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) := by
    push_cast
    linarith [Nat.floor_le hT0nn]
  have htgt : 12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
      (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) <
      (((⌊12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
      (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1))⌋₊ + 1 : ℕ)) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  generalize ⌊12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
      (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1))⌋₊ + 1 = t at htle htgt
  have hδ0 : (0:ℝ) ≤ 1 / (2 * (p:ℝ)) := by positivity
  have hδ1 : (1:ℝ) / (2 * (p:ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hcardκ : (Fintype.card (Fin n × Fin n → Fin (2 * M + 1)) : ℝ) =
      (2 * (M:ℝ) + 1) ^ (n * n) := by
    simp [Fintype.card_prod]
  have hbig : 2 * (Fintype.card (Fin n × Fin n → Fin (2 * M + 1)) : ℝ) <
      Real.exp ((1 / (2 * (p:ℝ))) ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3) := by
    rw [hcardκ]
    have hexp1 : Real.exp (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) =
        Real.exp 2 * (2 * (M:ℝ) + 1) ^ (n * n) := by
      rw [Real.exp_add]
      congr 1
      have e1 : (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1) =
          ((n * n : ℕ) : ℝ) * Real.log (2 * (M:ℝ) + 1) := by
        push_cast
        ring
      rw [e1, Real.exp_nat_mul, Real.exp_log (by positivity)]
    have hlt : 2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1) <
        (1 / (2 * (p:ℝ))) ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3 := by
      have e : (1 / (2 * (p:ℝ))) ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3 =
          (t:ℝ) / (12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ))) := by
        field_simp
        ring
      rw [e, lt_div_iff₀ (by positivity)]
      calc (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) *
            (12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)))
          = 12 * (p:ℝ) ^ 2 * ((n:ℝ) ^ n / (n.factorial : ℝ)) *
            (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) := by ring
        _ < (t:ℝ) := htgt
    have h2 : (2:ℝ) < Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
    have hpowpos : (0:ℝ) < (2 * (M:ℝ) + 1) ^ (n * n) := by positivity
    calc 2 * (2 * (M:ℝ) + 1) ^ (n * n) < Real.exp 2 * (2 * (M:ℝ) + 1) ^ (n * n) :=
          mul_lt_mul_of_pos_right h2 hpowpos
      _ = Real.exp (2 + (n:ℝ) ^ 2 * Real.log (2 * (M:ℝ) + 1)) := hexp1.symm
      _ < Real.exp ((1 / (2 * (p:ℝ))) ^ 2 * t * ((n.factorial : ℝ) / (n:ℝ) ^ n) / 3) :=
          Real.exp_lt_exp.mpr hlt
  obtain ⟨ω, hω⟩ := exists_good hn
    (fun (k : Fin n × Fin n → Fin (2 * M + 1)) (i j : Fin n) => ((k (i, j) : ℕ) : ℝ) / M - 1)
    (1 / (2 * (p:ℝ))) hδ0 hδ1 t hbig
  have htpos : 0 < t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    rw [ht0] at htgt
    simp only [Nat.cast_zero] at htgt
    linarith
  refine ⟨t, ω, htpos, htle, ?_⟩
  intro A
  rcases eq_or_lt_of_le (Pf_nonneg A) with hP0 | hPpos
  · have hZ : ∀ s, Zf A s = 0 := by
      intro s
      have h := Zf_le A s
      rw [← hP0, mul_zero] at h
      have h2 := Zf_nonneg A s
      nlinarith
    simp [hZ, ← hP0]
  · obtain ⟨A', ρ, hρ, hrow, hPf, hZf, hbound⟩ := exists_scaling hn A hPpos
    have hentry : ∀ i j, (A' i j) ^ 2 ≤ 1 := by
      intro i j
      calc (A' i j) ^ 2 ≤ ∑ j, (A' i j) ^ 2 :=
            Finset.single_le_sum (fun j _ => sq_nonneg (A' i j)) (Finset.mem_univ j)
        _ = 1 := hrow i
    choose kf hk1 hk2 using fun (q : Fin n × Fin n) =>
      round_entry M hMpos (A' q.1 q.2) (hentry q.1 q.2)
    have hGrow : ∀ i, ∑ j, (((kf (i, j) : ℕ) : ℝ) / M - 1) ^ 2 ≤ 1 := by
      intro i
      calc ∑ j, (((kf (i, j) : ℕ) : ℝ) / M - 1) ^ 2 ≤ ∑ j, (A' i j) ^ 2 :=
            Finset.sum_le_sum fun j _ => hk1 (i, j)
        _ = 1 := hrow i
    have hArow : ∀ i, ∑ j, (A' i j) ^ 2 ≤ 1 := fun i => (hrow i).le
    have hdiff : ∀ i, ∑ j, (A' i j - (((kf (i, j) : ℕ) : ℝ) / M - 1)) ^ 2 ≤
        ((n:ℝ) / M) ^ 2 := by
      intro i
      calc ∑ j, (A' i j - (((kf (i, j) : ℕ) : ℝ) / M - 1)) ^ 2
          ≤ ∑ _j : Fin n, (1 / (M:ℝ)) ^ 2 := Finset.sum_le_sum fun j _ => hk2 (i, j)
        _ = n * (1 / (M:ℝ)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ((n:ℝ) / M) ^ 2 := by
            rw [div_pow, div_pow, one_pow, mul_one_div]
            have h1 : (n:ℝ) ≤ (n:ℝ) ^ 2 := by nlinarith
            exact div_le_div_of_nonneg_right h1 (by positivity)
    have hε : (0:ℝ) ≤ (n:ℝ) / M := by positivity
    have hZc := fun s => Zf_close A'
      (fun (i j : Fin n) => ((kf (i, j) : ℕ) : ℝ) / M - 1) ((n:ℝ) / M) hε hArow hGrow hdiff s
    have hPc := Pf_close A'
      (fun (i j : Fin n) => ((kf (i, j) : ℕ) : ℝ) / M - 1) ((n:ℝ) / M) hε hArow hGrow hdiff
    obtain ⟨hlo, hhi⟩ := hω kf
    have hTc : |(∑ h, Zf A' (ω h)) -
        ∑ h, Zf (fun (i j : Fin n) => ((kf (i, j) : ℕ) : ℝ) / M - 1) (ω h)| ≤
        (t:ℝ) * (2 * n * ((n:ℝ) / M)) := by
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun h _ => hZc (ω h)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsmall : (4 * (p:ℝ) + 1) * (2 * n * ((n:ℝ) / M)) ≤ Pf A' := by
      have e : (4 * (p:ℝ) + 1) * (2 * n * ((n:ℝ) / M)) * (2 * (n:ℝ) ^ n) =
          (4 * (4 * (p:ℝ) + 1) * (n:ℝ) ^ 2 * (n:ℝ) ^ n) / M := by
        field_simp
        ring
      have h1 : (4 * (p:ℝ) + 1) * (2 * n * ((n:ℝ) / M)) * (2 * (n:ℝ) ^ n) ≤ (n.factorial : ℝ) := by
        rw [e, div_le_iff₀ hMR, hMcast]
        have h3 : 32 * (p:ℝ) * (n:ℝ) ^ 2 * (n:ℝ) ^ n ≤
            32 * (p:ℝ) * (n:ℝ) ^ 2 * ((n.factorial : ℝ) * (((n ^ n / n.factorial : ℕ) : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hq.le (by positivity)
        have h4 : 4 * (4 * (p:ℝ) + 1) * ((n:ℝ) ^ 2 * (n:ℝ) ^ n) ≤
            32 * (p:ℝ) * ((n:ℝ) ^ 2 * (n:ℝ) ^ n) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        nlinarith
      have h5 : (4 * (p:ℝ) + 1) * (2 * n * ((n:ℝ) / M)) * (2 * (n:ℝ) ^ n) ≤
          Pf A' * (2 * (n:ℝ) ^ n) := by linarith
      exact le_of_mul_le_mul_right h5 (by positivity)
    obtain ⟨h1, h2⟩ := final_ineq (p:ℝ) t (Pf A')
      (Pf (fun (i j : Fin n) => ((kf (i, j) : ℕ) : ℝ) / M - 1)) (∑ h, Zf A' (ω h))
      (∑ h, Zf (fun (i j : Fin n) => ((kf (i, j) : ℕ) : ℝ) / M - 1) (ω h))
      (2 * n * ((n:ℝ) / M)) hpR (Nat.cast_nonneg t) (by positivity) hTc hPc hlo hhi hsmall
    simp only [hZf] at h1 h2
    rw [← Finset.mul_sum, hPf] at h1 h2
    constructor
    · have h3 : ρ * (((p:ℝ) - 1) * t * Pf A) ≤ ρ * ((p:ℝ) * ∑ h, Zf A (ω h)) := by linarith
      exact le_of_mul_le_mul_left h3 hρ
    · have h3 : ρ * ((p:ℝ) * ∑ h, Zf A (ω h)) ≤ ρ * (((p:ℝ) + 1) * t * Pf A) := by linarith
      exact le_of_mul_le_mul_left h3 hρ

end PEqualNP.Outside.L_lib_708

theorem PEqualNP.Outside.L_lib_708 : ∀ (n p : ℕ), 0 < n → 2 ≤ p →
  let I := Fin n
  let K := (n : ℝ)^n/(n.factorial : ℝ)
  let M : ℕ := 32*p*n^2*(n^n/n.factorial+1)
  ∃ (t : ℕ) (s : Fin t → I × I → Bool), 0 < t ∧
    (t : ℝ) ≤ 1+12*(p : ℝ)^2*K*(2+(n : ℝ)^2*Real.log (2*(M : ℝ)+1)) ∧
    ∀ A : Matrix I I ℝ,
      let P := Matrix.permanent (fun i j => (A i j)^2)
      let total := ∑ h : Fin t, (Matrix.det (fun i j =>
        if s h (i,j) then -A i j else A i j : Matrix I I ℝ))^2
      ((p : ℝ)-1)*t*P ≤ (p : ℝ)*total ∧ (p : ℝ)*total ≤ ((p : ℝ)+1)*t*P := by
  intro n p hn hp I K M
  exact PEqualNP.Outside.L_lib_708.main_aux n p hn hp
