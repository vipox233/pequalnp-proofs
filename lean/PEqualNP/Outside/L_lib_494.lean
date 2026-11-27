import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_494_aux

private lemma monomial_mul_eq_sum {n : ℕ} (a : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) (ZMod 2)) :
    MvPolynomial.monomial a 1 * p =
      p.support.sum (fun b => p.coeff b • MvPolynomial.monomial (a + b) (1 : ZMod 2)) := by
  conv_lhs => rw [p.as_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [MvPolynomial.monomial_mul, one_mul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

private def evalMom {n : ℕ} (y : (Fin n →₀ ℕ) → ZMod 2) :
    MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun p => p.support.sum (fun b => p.coeff b * y b)
    map_add' := fun p q => by
      classical
      have hp : p.support.sum (fun b => p.coeff b * y b) =
          (p.support ∪ q.support).sum (fun b => p.coeff b * y b) := by
        refine Finset.sum_subset Finset.subset_union_left ?_
        intro b _ hbp
        rw [MvPolynomial.notMem_support_iff.mp hbp, zero_mul]
      have hq : q.support.sum (fun b => q.coeff b * y b) =
          (p.support ∪ q.support).sum (fun b => q.coeff b * y b) := by
        refine Finset.sum_subset Finset.subset_union_right ?_
        intro b _ hbq
        rw [MvPolynomial.notMem_support_iff.mp hbq, zero_mul]
      have hpq : (p + q).support.sum (fun b => (p + q).coeff b * y b) =
          (p.support ∪ q.support).sum (fun b => (p + q).coeff b * y b) := by
        refine Finset.sum_subset (MvPolynomial.support_add) ?_
        intro b _ hbpq
        rw [MvPolynomial.notMem_support_iff.mp hbpq, zero_mul]
      rw [hp, hq, hpq, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro b _
      rw [MvPolynomial.coeff_add, add_mul]
    map_smul' := fun c p => by
      classical
      simp only [RingHom.id_apply, smul_eq_mul]
      have hcp : (c • p).support.sum (fun b => (c • p).coeff b * y b) =
          p.support.sum (fun b => (c • p).coeff b * y b) := by
        refine Finset.sum_subset ?_ ?_
        · intro b hb
          rw [MvPolynomial.mem_support_iff] at hb ⊢
          rw [MvPolynomial.coeff_smul, smul_eq_mul] at hb
          exact right_ne_zero_of_mul hb
        · intro b _ hb
          rw [MvPolynomial.notMem_support_iff.mp hb, zero_mul]
      rw [hcp, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro b _
      rw [MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc] }

private lemma evalMom_monomial {n : ℕ} (y : (Fin n →₀ ℕ) → ZMod 2) (a : Fin n →₀ ℕ) :
    evalMom y (MvPolynomial.monomial a 1) = y a := by
  classical
  change (MvPolynomial.monomial a (1 : ZMod 2)).support.sum
    (fun b => (MvPolynomial.monomial a (1 : ZMod 2)).coeff b * y b) = y a
  have hsupp : (MvPolynomial.monomial a (1 : ZMod 2)).support = {a} := by
    ext b
    simp [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, eq_comm]
  rw [hsupp, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl, one_mul]

private lemma evalMom_one {n : ℕ} (y : (Fin n →₀ ℕ) → ZMod 2) :
    evalMom y (1 : MvPolynomial (Fin n) (ZMod 2)) = y 0 := by
  have h1 : (1 : MvPolynomial (Fin n) (ZMod 2)) = MvPolynomial.monomial 0 1 := by
    simp [MvPolynomial.monomial_zero']
  rw [h1, evalMom_monomial]

private lemma map_monomial_mul {n : ℕ} (φ : MvPolynomial (Fin n) (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (a : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) (ZMod 2)) :
    φ (MvPolynomial.monomial a 1 * p) =
      p.support.sum (fun b => p.coeff b * φ (MvPolynomial.monomial (a + b) 1)) := by
  rw [monomial_mul_eq_sum, map_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [map_smul, smul_eq_mul]

private lemma exists_dual_func {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) V) (v : V) (hv : v ∉ W) :
    ∃ φ : V →ₗ[ZMod 2] ZMod 2, φ v = 1 ∧ ∀ w ∈ W, φ w = 0 := by
  let q : V ⧸ W := Submodule.Quotient.mk v
  have hq : q ≠ 0 := by
    intro h0
    exact hv ((Submodule.Quotient.mk_eq_zero W).mp h0)
  let L : Submodule (ZMod 2) (V ⧸ W) := Submodule.span (ZMod 2) {q}
  rcases Submodule.exists_isCompl L with ⟨C, hcompl⟩
  let proj : (V ⧸ W) →ₗ[ZMod 2] L := Submodule.linearProjOfIsCompl L C hcompl
  let coord : L →ₗ[ZMod 2] ZMod 2 := (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (V ⧸ W) q hq).symm.toLinearMap
  let φ : V →ₗ[ZMod 2] ZMod 2 := coord.comp (proj.comp W.mkQ)
  refine ⟨φ, ?_, ?_⟩
  · have hqL : q ∈ L := Submodule.subset_span (Set.mem_singleton q)
    have hproj : proj q = ⟨q, hqL⟩ := Submodule.linearProjOfIsCompl_apply_left hcompl ⟨q, hqL⟩
    change coord (proj q) = 1
    rw [hproj]
    have h1 : (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (V ⧸ W) q hq) (1 : ZMod 2) = ⟨q, hqL⟩ := by
      apply Subtype.ext
      simp [LinearEquiv.toSpanNonzeroSingleton]
    rw [← h1]
    exact (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (V ⧸ W) q hq).symm_apply_apply 1
  · intro w hw
    change coord (proj (Submodule.Quotient.mk w)) = 0
    rw [(Submodule.Quotient.mk_eq_zero W).mpr hw, map_zero, map_zero]

end PEqualNP.Outside.L_lib_494_aux

theorem PEqualNP.Outside.L_lib_494 : (∀ (n m D : ℕ), let P := MvPolynomial (Fin n) (ZMod 2)
  ∀ g : Fin m → P,
    (¬ ∃ q : Fin m → P,
      (∀ j, q j = 0 ∨ (q j).totalDegree + (g j).totalDegree ≤ D) ∧
      (∑ j, q j * g j) = 1) ↔
    ∃ y : (Fin n →₀ ℕ) → ZMod 2, y 0 = 1 ∧
      ∀ (j : Fin m) (a : Fin n →₀ ℕ),
        a.sum (fun _ t => t) + (g j).totalDegree ≤ D →
        (g j).support.sum (fun b => (g j).coeff b * y (a+b)) = 0) := by
  intro n m D P g
  let S : Set P :=
    { p : P | ∃ (j : Fin m) (a : Fin n →₀ ℕ),
      a.sum (fun _ t => t) + (g j).totalDegree ≤ D ∧ p = MvPolynomial.monomial a 1 * g j }
  let W : Submodule (ZMod 2) P := Submodule.span (ZMod 2) S
  have hmem_W : ∀ p : P, p ∈ W ↔
      ∃ q : Fin m → P,
        (∀ j, q j = 0 ∨ (q j).totalDegree + (g j).totalDegree ≤ D) ∧
        (∑ j, q j * g j) = p := by
    intro p
    constructor
    · intro hp
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
      · rintro x ⟨j0, a, hdeg, rfl⟩
        classical
        refine ⟨Function.update 0 j0 (MvPolynomial.monomial a 1), ?_, ?_⟩
        · intro j
          by_cases hj : j = j0
          · subst hj
            right
            simp only [Function.update_self]
            have htd : (MvPolynomial.monomial a (1 : ZMod 2)).totalDegree = a.sum (fun _ t => t) := by
              rw [MvPolynomial.totalDegree_monomial _ (one_ne_zero)]
            omega
          · left
            simp [hj]
        · rw [Finset.sum_eq_single j0]
          · simp
          · intro j _ hne
            simp [hne]
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ j0))
      · refine ⟨0, fun _ => Or.inl rfl, by simp⟩
      · rintro x y _ _ ⟨q1, hq1, rfl⟩ ⟨q2, hq2, rfl⟩
        refine ⟨q1 + q2, ?_, ?_⟩
        · intro j
          rcases hq1 j with h1 | h1
          · rcases hq2 j with h2 | h2
            · left; simp [h1, h2]
            · right; simp [h1, h2]
          · rcases hq2 j with h2 | h2
            · right; simp [h1, h2]
            · right
              have hle := MvPolynomial.totalDegree_add (q1 j) (q2 j)
              change (q1 j + q2 j).totalDegree + (g j).totalDegree ≤ D
              omega
        · rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _
          change (q1 j + q2 j) * g j = q1 j * g j + q2 j * g j
          ring
      · rintro c x _ ⟨q, hq, rfl⟩
        refine ⟨fun j => c • q j, ?_, ?_⟩
        · intro j
          rcases hq j with h0 | hdeg
          · left; simp [h0]
          · right
            have hle := MvPolynomial.totalDegree_smul_le c (q j)
            dsimp only
            omega
        · rw [Finset.smul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [smul_mul_assoc]
    · rintro ⟨q, hq, rfl⟩
      refine Submodule.sum_mem W ?_
      intro j _
      rcases hq j with h0 | hdeg
      · rw [h0, zero_mul]
        exact Submodule.zero_mem W
      · rw [(q j).as_sum, Finset.sum_mul]
        refine Submodule.sum_mem W ?_
        intro a ha
        have hmon : MvPolynomial.monomial a ((q j).coeff a) * g j =
            (q j).coeff a • (MvPolynomial.monomial a 1 * g j) := by
          rw [← smul_mul_assoc, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        rw [hmon]
        refine Submodule.smul_mem W _ (Submodule.subset_span ?_)
        refine ⟨j, a, ?_, rfl⟩
        have ha_le : a.sum (fun _ t => t) ≤ (q j).totalDegree :=
          MvPolynomial.le_totalDegree ha
        omega
  rw [← hmem_W 1]
  constructor
  · intro hnot
    rcases PEqualNP.Outside.L_lib_494_aux.exists_dual_func W 1 hnot with ⟨φ, hφ1, hφW⟩
    refine ⟨fun a => φ (MvPolynomial.monomial a 1), ?_, ?_⟩
    · have h1 : (1 : P) = MvPolynomial.monomial 0 1 := by simp [MvPolynomial.monomial_zero']
      dsimp only
      rw [← h1]
      exact hφ1
    · intro j a hdeg
      have hmem : MvPolynomial.monomial a 1 * g j ∈ W :=
        Submodule.subset_span ⟨j, a, hdeg, rfl⟩
      have h0 := hφW _ hmem
      rw [PEqualNP.Outside.L_lib_494_aux.map_monomial_mul] at h0
      exact h0
  · rintro ⟨y, hy0, hy_ann⟩ h1W
    let φ := PEqualNP.Outside.L_lib_494_aux.evalMom y
    have hφW : ∀ p ∈ W, φ p = 0 := by
      intro p hp
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
      · rintro x ⟨j, a, hdeg, rfl⟩
        rw [PEqualNP.Outside.L_lib_494_aux.map_monomial_mul]
        have hterm : ∀ b ∈ (g j).support,
            (g j).coeff b * φ (MvPolynomial.monomial (a + b) 1) = (g j).coeff b * y (a + b) := by
          intro b _
          rw [PEqualNP.Outside.L_lib_494_aux.evalMom_monomial]
        rw [Finset.sum_congr rfl hterm]
        exact hy_ann j a hdeg
      · exact map_zero φ
      · intro x1 x2 _ _ hx1 hx2
        rw [map_add, hx1, hx2, add_zero]
      · intro c x _ hx
        rw [map_smul, hx, smul_zero]
    have h0 := hφW 1 h1W
    rw [PEqualNP.Outside.L_lib_494_aux.evalMom_one, hy0] at h0
    exact one_ne_zero h0
