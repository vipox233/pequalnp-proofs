import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_706_aux

open Polynomial

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

def Sk (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k)

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

theorem gurvits_pos {n : ℕ} (c : Fin n → Fin n → ℝ) (hc : ∀ i j, 0 < c i j) (γ : ℝ)
    (hγ : 0 ≤ γ)
    (hcap : ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → γ * ∏ j, x j ≤ ∏ i, ∑ j, c i j * x j) :
    γ * (n.factorial : ℝ) ≤ (n:ℝ) ^ n * ∑ σ : Equiv.Perm (Fin n), ∏ j, c (σ j) j := by
  have h := cap_chain c hc γ hγ hcap n le_rfl (fun _ => 1) (fun _ => one_pos)
  simp only [Nat.sub_self, Sk_zero, Finset.prod_empty, mul_one, pow_zero] at h
  rw [phi_empty] at h
  exact h

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

def sg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if s (i, j) then -A i j else A i j

noncomputable def Zf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : Fin n × Fin n → Bool) : ℝ :=
  (Matrix.det (sg A s)) ^ 2

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

theorem rescale {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hP : 0 < Pf A)
    (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    ∃ (B : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ), 0 < ρ ∧ (∀ i, ∑ j, (B i j)^2 = 1) ∧
      Pf B = ρ * Pf A ∧ (∀ s, Zf B s = ρ * Zf A s) ∧
      ρ = (∏ j, x j) / ∏ i, ∑ j, (A i j)^2 * x j := by
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
    ?_, ?_, hPf, ?_, hρ⟩
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

open Filter Topology

theorem prod_tangent {α : Type*} [DecidableEq α] (v : α → ℝ) (s : Finset α) :
    HasDerivAt (fun t : ℝ => ∏ i ∈ s, (1 + t * v i)) (∑ i ∈ s, v i) 0 := by
  induction s using Finset.induction_on with
  | empty => simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  | @insert i s hi ih =>
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add 1).mul ih
    simpa [hi, Pi.mul_def, Finset.prod_insert, Finset.sum_insert] using h

theorem balance {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (row : ∀ i, ∑ j, (B i j)^2 = 1)
    (cap : ∀ x : Fin n → ℝ, (∀ j, 0 < x j) → ∏ j, x j ≤ ∏ i, ∑ j, (B i j)^2 * x j) :
    ∀ j, ∑ i, (B i j)^2 = 1 := by
  classical
  intro k
  let v := fun i => (B i k)^2
  have hmin : IsLocalMin (fun t : ℝ => (∏ i, (1 + t * v i)) - (1 + t)) 0 := by
    filter_upwards [lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
    let x : Fin n → ℝ := fun j => if j = k then 1+t else 1
    have hx : ∀ j, 0 < x j := by intro j; dsimp [x]; split_ifs <;> linarith
    have hr (i : Fin n) : (∑ j, (B i j)^2 * x j) = 1 + t * v i := by
      calc
        _ = ∑ j, ((B i j)^2 + if j = k then t * v i else 0) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases hj : j = k
          · subst j; simp [x,v]; ring
          · simp [x,hj]
        _ = _ := by simp [Finset.sum_add_distrib,row]
    have h := cap x hx
    simp only [hr] at h
    have hprod : (∏ j, x j) = 1+t := by classical simp [x]
    rw [hprod] at h
    simpa using (sub_nonneg.mpr h)
  have hd := (prod_tangent v Finset.univ).sub ((hasDerivAt_id (0 : ℝ)).const_add 1)
  have d := hmin.hasDerivAt_eq_zero hd
  exact sub_eq_zero.mp d

theorem extremizer {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ha : 0 < Pf A) :
    ∃ (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ), 0 < c ∧
      (∀ i, ∑ j, (B i j)^2 = 1) ∧ (∀ j, ∑ i, (B i j)^2 = 1) ∧
      Pf B = c * Pf A ∧ (n.factorial : ℝ) ≤ (n:ℝ)^n * Pf B ∧
      ∀ s, Zf B s = c * Zf A s := by
  classical
  let Good : Set (Fin n → Fin n → ℝ) := {B | (∀ i, ∑ j, (B i j)^2 = 1) ∧
      ∀ s, Zf B s * Pf A = Zf A s * Pf B}
  have hcP : Continuous (fun B : Fin n → Fin n → ℝ => Pf B) := by
    unfold Pf
    fun_prop
  have hcZ (s : Fin n × Fin n → Bool) : Continuous (fun B : Fin n → Fin n → ℝ => Zf B s) := by
    have entry (B : Fin n → Fin n → ℝ) (i j : Fin n) :
        sg B s i j = (if s (i,j) then (-1 : ℝ) else 1) * B i j := by
      unfold sg
      split <;> simp
    simp only [Zf, Matrix.det_apply', entry]
    fun_prop
  have hclosed : IsClosed Good := by
    have e : Good = (⋂ i, {B : Fin n → Fin n → ℝ | ∑ j, (B i j)^2 = 1}) ∩
        ⋂ s, {B : Fin n → Fin n → ℝ | Zf B s * Pf A = Zf A s * Pf B} := by ext; simp [Good]
    rw [e]
    exact (isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_iInter fun s => isClosed_eq ((hcZ s).mul continuous_const) (continuous_const.mul hcP))
  have hcompact : IsCompact Good := by
    apply (isCompact_Icc (a := fun (_ _ : Fin n) => (-1 : ℝ)) (b := fun _ _ => (1 : ℝ))).of_isClosed_subset hclosed
    intro B hB
    have hbnd (i j : Fin n) : (B i j)^2 ≤ 1 := by
      rw [← hB.1 i]
      exact Finset.single_le_sum (fun k _ => sq_nonneg (B i k)) (Finset.mem_univ j)
    exact ⟨fun i j => by have h := hbnd i j; nlinarith [sq_nonneg (B i j + 1)],
      fun i j => by have h := hbnd i j; nlinarith [sq_nonneg (B i j - 1)]⟩
  obtain ⟨D,r,hr,hrow,hp,hz,_⟩ := rescale A ha (fun _ => 1) (by simp)
  have hd : D ∈ Good := ⟨hrow,fun s => by rw [hz,hp]; ring⟩
  obtain ⟨B,hB,hmax⟩ := hcompact.exists_isMaxOn ⟨D,hd⟩ hcP.continuousOn
  have hpos : 0 < Pf B := lt_of_lt_of_le (hp ▸ mul_pos hr ha : 0 < Pf D) (hmax hd)
  have cap (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) : ∏ j, x j ≤ ∏ i, ∑ j, (B i j)^2 * x j := by
    obtain ⟨T,r',hr',tr,tp,tz,rf⟩ := rescale B hpos x hx
    have ht : T ∈ Good := ⟨tr, fun s => by
      calc Zf T s * Pf A = r' * (Zf B s * Pf A) := by rw [tz]; ring
           _ = _ := by rw [hB.2 s,tp]; ring⟩
    have hle := hmax ht
    change Pf T ≤ Pf B at hle
    rw [tp] at hle
    have hrle : r' ≤ 1 := by nlinarith
    have hden : 0 < ∏ i, ∑ j, (B i j)^2 * x j := by
      apply Finset.prod_pos
      intro i _
      have hrow' := hB.1 i
      obtain ⟨j, hj⟩ : ∃ j, B i j ≠ 0 := by
        by_contra! h
        simp [h] at hrow'
      exact Finset.sum_pos' (fun j _ => mul_nonneg (sq_nonneg _) (hx j).le)
        ⟨j, Finset.mem_univ j, mul_pos (sq_pos_of_ne_zero hj) (hx j)⟩
    rw [rf, div_le_iff₀ hden, one_mul] at hrle
    exact hrle
  refine ⟨B, Pf B / Pf A, div_pos hpos ha, hB.1, balance hB.1 cap, ?_, ?_, ?_⟩
  · field_simp
  · simpa [Pf] using gurvits (fun i j => (B i j)^2) (fun _ _ => sq_nonneg _) 1 zero_le_one
      (by intro x hx; simpa using cap x hx)
  · intro s
    have h := hB.2 s
    field_simp
    linarith

end PEqualNP.Outside.L_lib_706_aux

open PEqualNP.Outside.L_lib_706_aux

theorem PEqualNP.Outside.L_lib_706 : ∀ n : ℕ, 0 < n →
  let I := Fin n
  let S := I × I → Bool
  let P := fun A : Matrix I I ℝ => Matrix.permanent (fun i j => (A i j)^2)
  let Z := fun (A : Matrix I I ℝ) (s : S) =>
    (Matrix.det (fun i j => if s (i,j) then -A i j else A i j : Matrix I I ℝ))^2
  ∀ A : Matrix I I ℝ,
    (∀ s : S, (n.factorial : ℝ) * Z A s ≤ (n : ℝ)^n * P A) ∧
    (0 < P A → ∃ (B : Matrix I I ℝ) (c : ℝ), 0 < c ∧
      (∀ i, (∑ j : I, (B i j)^2) = 1) ∧ (∀ j, (∑ i : I, (B i j)^2) = 1) ∧
      P B = c * P A ∧ (n.factorial : ℝ) ≤ (n : ℝ)^n * P B ∧
      ∀ s : S, Z B s = c * Z A s) := by
  intro n hn I S P Z A
  constructor
  · intro s
    calc (n.factorial : ℝ) * Z A s = Z A s * (n.factorial : ℝ) := mul_comm _ _
         _ ≤ (n : ℝ)^n * P A := Zf_le A s
  · exact extremizer A
