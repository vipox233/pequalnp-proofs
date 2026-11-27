import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_831_aux

open scoped BigOperators

variable {E K : Type} [Field E] [Field K] [Algebra E K]

abbrev Meets {g : ℕ} (u : Fin g → K) (f : Fin g → K →ₗ[E] E) (w : K) (t : ℕ) : Prop :=
  w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
    S.card ≤ t ∧ x ≠ 0 ∧ x = w * ∑ i ∈ S, (a i * f i x) • u i

theorem eval_sum {g : ℕ} (u : Fin g → K) (f : Fin g → K →ₗ[E] E)
    (w : K) (S : Finset (Fin g)) (a : Fin g → E) (x : K) (i : Fin g) :
    f i (w * ∑ j ∈ S, (a j * f j x) • u j) =
      ∑ j ∈ S, (a j * f j x) * f i (w * u j) := by
  simp [Finset.mul_sum, smul_eq_mul]

theorem triangular_exclusion {g : ℕ} (u : Fin g → K) (f : Fin g → K →ₗ[E] E)
    (w : K) (t : ℕ) (h : ∀ i j, i ≤ j → f i (w * u j) = 0) : ¬ Meets u f w t := by
  rintro ⟨_, S, a, x, _, hx, eq⟩
  have hf (i : Fin g) : f i x = 0 := by
    refine Fin.strong_induction_on ?_ i
    intro i ih
    calc
      f i x = ∑ j ∈ S, (a j * f j x) * f i (w * u j) :=
        (congrArg (f i) eq).trans (eval_sum u f w S a x i)
      _ = 0 := Finset.sum_eq_zero fun j _ => by
        by_cases hj : i ≤ j
        · rw [h i j hj, mul_zero]
        · rw [ih j (lt_of_not_ge hj), mul_zero, zero_mul]
  apply hx
  simpa [hf] using eq

abbrev Tri (g : ℕ) := Σ j : Fin g, Fin (j.val + 1)

theorem card_tri (g : ℕ) : Fintype.card (Tri g) = g * (g + 1) / 2 := by
  simp only [Tri, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
  have h (n : ℕ) : (∑ i ∈ Finset.range n, (i+1)) * 2 = n * (n+1) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.add_mul, ih]
      ring
  have hh := h g
  omega

def triMap {g : ℕ} (u : Fin g → K) (f : Fin g → K →ₗ[E] E) : K →ₗ[E] (Tri g → E) :=
  LinearMap.pi fun ij => (f ⟨ij.2.val, by have := ij.2.isLt; have := ij.1.isLt; omega⟩).comp
    (Algebra.lmul E K (u ij.1))

theorem triMap_zero {g : ℕ} (u : Fin g → K) (f : Fin g → K →ₗ[E] E) (w : K)
    (h : triMap u f w = 0) (i j : Fin g) (hij : i ≤ j) : f i (w * u j) = 0 := by
  have hij' : i.val < j.val + 1 := Nat.lt_succ_of_le hij
  have hval := congrFun h (⟨j, ⟨i.val, hij'⟩⟩ : Tri g)
  simpa [triMap, mul_comm] using hval

theorem triangular_card [Fintype E] [Fintype K] [FiniteDimensional E K] {g : ℕ}
    (u : Fin g → K) (f : Fin g → K →ₗ[E] E) (Z : Finset K)
    (hZ : ∀ w ∈ Z, Meets u f w g) :
    Z.card + Fintype.card E ^ (Module.finrank E K - g * (g + 1) / 2) ≤
      Fintype.card E ^ Module.finrank E K := by
  classical
  let T := triMap u f
  let A : Finset K := Finset.univ.filter fun w => T w = 0
  have hcod : Module.finrank E (Tri g → E) = g * (g + 1) / 2 := by
    rw [Module.finrank_fintype_fun_eq_card, card_tri]
  have hrange := (Submodule.finrank_le (LinearMap.range T)).trans_eq hcod
  have hdim := T.finrank_range_add_finrank_ker
  have hd : Module.finrank E K - g * (g+1) / 2 ≤ Module.finrank E (LinearMap.ker T) := by omega
  let e : LinearMap.ker T ≃ {w // w ∈ A} :=
    { toFun := fun w => ⟨w, by exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, LinearMap.mem_ker.mp w.property⟩⟩
      invFun := fun w => ⟨w, LinearMap.mem_ker.mpr (Finset.mem_filter.mp w.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let _ : Fintype (LinearMap.ker T) := Fintype.ofFinite _
  have hA : A.card = Fintype.card E ^ Module.finrank E (LinearMap.ker T) := by
    rw [← Fintype.card_coe, ← Fintype.card_congr e, Module.card_eq_pow_finrank (K := E)]
  have hA' := Nat.pow_le_pow_right (Nat.pos_of_ne_zero (Fintype.card_ne_zero : Fintype.card E ≠ 0)) hd
  rw [← hA] at hA'
  have hdis : Disjoint Z A := Finset.disjoint_left.mpr fun w hw hAw =>
    triangular_exclusion u f w g (triMap_zero u f w (Finset.mem_filter.mp hAw).2) (hZ w hw)
  have huniv := Finset.card_le_univ (s := Z ∪ A)
  rw [Finset.card_union_of_disjoint hdis, Module.card_eq_pow_finrank (K := E)] at huniv
  omega

lemma good_two_of_nonzero_pair
    {g : ℕ} (ell : K →ₗ[E] E) (d : Fin g → K) (w : K)
    (hit : ∃ i j, ell (w * d i * d j) ≠ 0) :
    w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
      S.card ≤ 2 ∧ x ≠ 0 ∧
      x = w * ∑ i ∈ S, (a i * ell (d i * x)) • d i := by
  classical
  obtain ⟨i, j, hij⟩ := hit
  have hw : w ≠ 0 := by
    intro hz
    apply hij
    simp [hz]
  refine ⟨hw, ?_⟩
  by_cases diag : ∃ k, ell (w * d k * d k) ≠ 0
  · obtain ⟨k, hk⟩ := diag
    have hd : d k ≠ 0 := by
      intro hz
      apply hk
      simp [hz]
    refine ⟨{k}, fun _ => (ell (w * d k * d k))⁻¹, w * d k,
      by simp, mul_ne_zero hw hd, ?_⟩
    rw [Finset.sum_singleton, show d k * (w * d k) = w * d k * d k by ring,
      inv_mul_cancel₀ hk, one_smul]
  · push Not at diag
    have hne : i ≠ j := by
      intro h
      subst j
      exact hij (diag i)
    let x := w * (d i + d j)
    have hi : ell (d i * x) = ell (w * d i * d j) := by
      rw [show d i * x = w * d i * d i + w * d i * d j by dsimp [x]; ring,
        map_add, diag i, zero_add]
    have hj : ell (d j * x) = ell (w * d i * d j) := by
      rw [show d j * x = w * d j * d j + w * d i * d j by dsimp [x]; ring,
        map_add, diag j, zero_add]
    have hx : x ≠ 0 := by
      intro hz
      apply hij
      rw [← hi, hz, mul_zero, map_zero]
    refine ⟨{i, j}, fun _ => (ell (w * d i * d j))⁻¹, x,
      by simp [hne], hx, ?_⟩
    rw [Finset.sum_pair hne, hi, hj, inv_mul_cancel₀ hij, one_smul, one_smul]

section

open Module

def pair (ell : K →ₗ[E] E) : K →ₗ[E] Module.Dual E K where
  toFun w := ell.comp (Algebra.lmul E K w)
  map_add' a b := by ext y; change ell ((a+b)*y) = ell (a*y) + ell (b*y); simp [add_mul]
  map_smul' t a := by
    ext y
    change ell ((t • a)*y) = t * ell (a*y)
    rw [smul_mul_assoc, map_smul, smul_eq_mul]

theorem pair_inj (ell : K →ₗ[E] E) (hell : ell ≠ 0) : Function.Injective (pair ell) := by
  rw [← LinearMap.ker_eq_bot]
  apply bot_unique
  intro w hw
  change pair ell w = 0 at hw
  change w = 0
  by_contra hn
  apply hell
  ext z
  have hz : ell (w*(w⁻¹*z)) = 0 := LinearMap.congr_fun hw (w⁻¹*z)
  simpa [← mul_assoc, mul_inv_cancel₀ hn] using hz

variable [FiniteDimensional E K]

theorem pair_surj (ell : K →ₗ[E] E) (hell : ell ≠ 0) : Function.Surjective (pair ell) := by
  have eq : finrank E K = finrank E (Module.Dual E K) :=
    (Subspace.dual_finrank_eq (K := E) (V := K)).symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := pair ell) eq).mp
    (pair_inj ell hell)

variable [Fintype E] [Fintype K]

theorem annihilatorCount (ell : K →ₗ[E] E) (hell : ell ≠ 0) (P : Submodule E K) :
    (@Finset.filter K (fun w => ∃ y ∈ P, ell (w*y) ≠ 0)
      (fun w => Classical.propDecidable (∃ y ∈ P, ell (w*y) ≠ 0)) Finset.univ).card +
      Fintype.card E ^ (finrank E K - finrank E P) = Fintype.card E ^ finrank E K := by
  classical
  let restrict := P.dualRestrict.comp (pair ell)
  have surj : Function.Surjective restrict := (Subspace.dualRestrict_surjective (W := P)).comp (pair_surj ell hell)
  have hdim : finrank E restrict.ker = finrank E K - finrank E P := by
    have h := LinearMap.finrank_range_add_finrank_ker restrict
    rw [LinearMap.range_eq_top.mpr surj, finrank_top, Subspace.dual_finrank_eq] at h
    omega
  have mem (w : K) : w ∈ restrict.ker ↔ ∀ y ∈ P, ell (w*y) = 0 := by
    change restrict w = 0 ↔ _
    rw [LinearMap.ext_iff]
    exact ⟨fun h y hy => h ⟨y,hy⟩, fun h y => h y y.property⟩
  let B := @Finset.filter K (fun w => ¬ ∃ y ∈ P, ell (w*y) ≠ 0)
    (fun w => Classical.propDecidable _) Finset.univ
  have e : ↥B ≃ ↥restrict.ker := Equiv.subtypeEquivProp (funext fun w => propext (by simp [B, mem]))
  have hcard : B.card = Fintype.card E ^ (finrank E K - finrank E P) := by
    rw [← Nat.card_eq_finsetCard, Nat.card_congr e, Module.natCard_eq_pow_finrank (K := E) (V := ↥restrict.ker),
      Nat.card_eq_fintype_card, hdim]
  rw [← hcard, ← Module.card_eq_pow_finrank (K := E) (V := K), ← Finset.card_univ]
  exact @Finset.card_filter_add_card_filter_not K Finset.univ
    (fun w => ∃ y ∈ P, ell (w*y) ≠ 0)
    (fun w => Classical.propDecidable _) (fun w => Classical.propDecidable _)

end

theorem meets_has_pair {g : ℕ} (ell : K →ₗ[E] E) (d : Fin g → K)
    (w : K) (t : ℕ) (h : Meets d (fun i => ell.comp (Algebra.lmul E K (d i))) w t) :
    ∃ i j, ell (w * d i * d j) ≠ 0 := by
  by_contra! hn
  apply triangular_exclusion d (fun i => ell.comp (Algebra.lmul E K (d i))) w t _ h
  intro i j _
  change ell (d i * (w * d j)) = 0
  rw [show d i * (w * d j) = w * d i * d j by ring]
  exact hn i j

lemma pair_hits_span {g : ℕ} (ell : K →ₗ[E] E) (d : Fin g → K) (w : K) :
    let P := Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2))
    (∃ i j, ell (w * d i * d j) ≠ 0) ↔ ∃ y ∈ P, ell (w * y) ≠ 0 := by
  dsimp only
  constructor
  · rintro ⟨i, j, h⟩
    exact ⟨d i * d j, Submodule.subset_span ⟨(i, j), rfl⟩, by simpa [mul_assoc] using h⟩
  · rintro ⟨y, hy, h⟩
    by_contra! hzero
    have hz : Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2)) ≤
        LinearMap.ker (ell.comp (Algebra.lmul E K w)) := by
      refine Submodule.span_le.mpr ?_
      rintro v ⟨⟨i, j⟩, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      change ell (w * (d i * d j)) = 0
      simpa [mul_assoc] using hzero i j
    apply h
    exact LinearMap.mem_ker.mp (hz hy)

theorem symmetric_card [Fintype E] [Fintype K] [FiniteDimensional E K] {g : ℕ}
    (ell : K →ₗ[E] E) (hell : ell ≠ 0) (d : Fin g → K) :
    let P := Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2))
    let good := Meets d (fun i => ell.comp (Algebra.lmul E K (d i)))
    (∀ w : K, (good w g ↔ good w 2) ∧ (good w 2 ↔ ∃ y ∈ P, ell (w*y) ≠ 0)) ∧
      (@Finset.filter K (fun w => good w 2) (fun w => Classical.propDecidable (good w 2))
        Finset.univ).card + Fintype.card E ^ (Module.finrank E K - Module.finrank E P) =
        Fintype.card E ^ Module.finrank E K := by
  intro P good
  have of_pair (w : K) (h : ∃ i j, ell (w * d i * d j) ≠ 0) : good w 2 := by
    exact good_two_of_nonzero_pair ell d w h
  have h2 (w : K) : good w 2 ↔ ∃ y ∈ P, ell (w * y) ≠ 0 :=
    (show good w 2 ↔ ∃ i j, ell (w * d i * d j) ≠ 0 from
      ⟨meets_has_pair ell d w 2, of_pair w⟩).trans (pair_hits_span ell d w)
  constructor
  · intro w
    refine ⟨⟨fun h => of_pair w (meets_has_pair ell d w g h), ?_⟩, h2 w⟩
    rintro ⟨hw, S, a, x, _, hx, heq⟩
    exact ⟨hw, S, a, x, (Finset.card_le_univ S).trans_eq (Fintype.card_fin g), hx, heq⟩
  · have heq : (@Finset.filter K (fun w => good w 2) (fun w => Classical.propDecidable _) Finset.univ) =
        (@Finset.filter K (fun w => ∃ y ∈ P, ell (w*y) ≠ 0) (fun w => Classical.propDecidable _) Finset.univ) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h2 w
    rw [heq]
    exact annihilatorCount ell hell P

end PEqualNP.Outside.L_lib_831_aux

theorem PEqualNP.Outside.L_lib_831 : (∀ (E K : Type) [Field E] [CharP E 2] [Fintype E] [Field K] [Algebra E K]
    [FiniteDimensional E K] [Fintype K], 2 < Fintype.card E →
  ∀ (g : ℕ) (ell : K →ₗ[E] E), ell ≠ 0 →
    let m := Module.finrank E K
    let q := Fintype.card E
    let meet := fun (u : Fin g → K) (f : Fin g → (K →ₗ[E] E)) (w : K) (t : ℕ) =>
      w ≠ 0 ∧ ∃ (S : Finset (Fin g)) (a : Fin g → E) (x : K),
        S.card ≤ t ∧ x ≠ 0 ∧ x = w * ∑ i ∈ S, (a i * f i x) • u i
    (∀ (u : Fin g → K) (f : Fin g → (K →ₗ[E] E)) (Z : Finset K),
      (∀ w ∈ Z, meet u f w g) → Z.card + q^(m-g*(g+1)/2) ≤ q^m) ∧
    ∀ d : Fin g → K,
      let P := Submodule.span E (Set.range (fun ij : Fin g × Fin g => d ij.1 * d ij.2))
      let good := meet d (fun i => ell.comp (Algebra.lmul E K (d i)))
      (∀ w : K, (good w g ↔ good w 2) ∧ (good w 2 ↔ ∃ y ∈ P, ell (w*y) ≠ 0)) ∧
        (@Finset.filter K (fun w => good w 2) (fun w => Classical.propDecidable (good w 2))
          Finset.univ).card + q^(m-Module.finrank E P) = q^m) := by
  intro E K _ _ _ _ _ _ _ _ g ell hell
  dsimp only
  constructor
  · exact PEqualNP.Outside.L_lib_831_aux.triangular_card
  · intro d
    exact PEqualNP.Outside.L_lib_831_aux.symmetric_card ell hell d
