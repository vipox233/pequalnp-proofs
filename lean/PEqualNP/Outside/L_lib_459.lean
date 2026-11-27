import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_459_aux

private def signedMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin n × Fin n → Bool) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if s (i, j) then -A i j else A i j

private lemma sum_prod_signed_ne {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (σ τ : Equiv.Perm (Fin n)) (hne : σ ≠ τ) :
    (∑ s : Fin n × Fin n → Bool,
      (∏ i : Fin n, signedMat A s (σ i) i) * (∏ i : Fin n, signedMat A s (τ i) i)) = 0 := by
  have hex : ∃ i0 : Fin n, σ i0 ≠ τ i0 := by
    by_contra h
    push Not at h
    apply hne
    apply Equiv.ext
    intro i
    exact h i
  rcases hex with ⟨i0, hi0⟩
  let p0 : Fin n × Fin n := (σ i0, i0)
  let flip : (Fin n × Fin n → Bool) ≃ (Fin n × Fin n → Bool) :=
    { toFun := fun s => Function.update s p0 (!s p0)
      invFun := fun s => Function.update s p0 (!s p0)
      left_inv := fun s => by
        funext p
        by_cases hp : p = p0
        · subst hp
          simp
        · simp [hp]
      right_inv := fun s => by
        funext p
        by_cases hp : p = p0
        · subst hp
          simp
        · simp [hp] }
  have hflip_val : ∀ (s : Fin n × Fin n → Bool) (i j : Fin n),
      signedMat A (flip s) i j = if (i, j) = p0 then -signedMat A s i j else signedMat A s i j := by
    intro s i j
    unfold signedMat
    dsimp [flip]
    by_cases hp : (i, j) = p0
    · simp only [hp, ↓reduceIte, Function.update_self]
      cases s p0 <;> simp
    · simp only [hp, ↓reduceIte, Function.update_of_ne hp]
  have hprod_σ : ∀ s : Fin n × Fin n → Bool,
      (∏ i : Fin n, signedMat A (flip s) (σ i) i) =
        -(∏ i : Fin n, signedMat A s (σ i) i) := by
    intro s
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
    have h0 : signedMat A (flip s) (σ i0) i0 = -signedMat A s (σ i0) i0 := by
      rw [hflip_val, if_pos rfl]
    have hrest :
        (∏ i ∈ Finset.univ.erase i0, signedMat A (flip s) (σ i) i) =
          ∏ i ∈ Finset.univ.erase i0, signedMat A s (σ i) i := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hne_i : i ≠ i0 := (Finset.mem_erase.mp hi).1
      have hne_p : (σ i, i) ≠ p0 := by
        intro heq
        exact hne_i (congrArg Prod.snd heq)
      rw [hflip_val, if_neg hne_p]
    rw [h0, hrest, neg_mul]
  have hprod_τ : ∀ s : Fin n × Fin n → Bool,
      (∏ i : Fin n, signedMat A (flip s) (τ i) i) =
        ∏ i : Fin n, signedMat A s (τ i) i := by
    intro s
    refine Finset.prod_congr rfl ?_
    intro i _
    have hne_p : (τ i, i) ≠ p0 := by
      intro heq
      have h2 : i = i0 := congrArg Prod.snd heq
      subst h2
      exact hi0 (congrArg Prod.fst heq).symm
    rw [hflip_val, if_neg hne_p]
  have hshift :
      (∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, signedMat A s (σ i) i) * (∏ i : Fin n, signedMat A s (τ i) i)) =
      ∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, signedMat A (flip s) (σ i) i) * (∏ i : Fin n, signedMat A (flip s) (τ i) i) := by
    symm
    refine Fintype.sum_equiv flip _ _ ?_
    intro s
    rfl
  have hneg :
      (∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, signedMat A (flip s) (σ i) i) * (∏ i : Fin n, signedMat A (flip s) (τ i) i)) =
      -(∑ s : Fin n × Fin n → Bool,
        (∏ i : Fin n, signedMat A s (σ i) i) * (∏ i : Fin n, signedMat A s (τ i) i)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro s _
    rw [hprod_σ, hprod_τ, neg_mul]
  linarith

end PEqualNP.Outside.L_lib_459_aux

theorem PEqualNP.Outside.L_lib_459 : (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
  let signed : (Fin n × Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ := fun s =>
    fun i j => if s (i,j) then -A i j else A i j
  let weights : Matrix (Fin n) (Fin n) ℝ := fun row col => A row col ^ 2
  (∑ s : Fin n × Fin n → Bool, (Matrix.det (signed s)) ^ 2) =
    (2 : ℝ)^(n*n) * weights.permanent) := by
  intro n A signed weights
  have hdet_sq : ∀ s : Fin n × Fin n → Bool,
      (Matrix.det (signed s)) ^ 2 =
        ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
            ((∏ i : Fin n, signed s (σ i) i) * (∏ i : Fin n, signed s (τ i) i)) := by
    intro s
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
          ((∏ i : Fin n, signed s (σ i) i) * (∏ i : Fin n, signed s (τ i) i))) =
      ∑ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign τ : ℤ) : ℝ) *
          (∑ s : Fin n × Fin n → Bool,
            (∏ i : Fin n, signed s (σ i) i) * (∏ i : Fin n, signed s (τ i) i)) := by
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
            (∏ i : Fin n, signed s (σ i) i) * (∏ i : Fin n, signed s (τ i) i))) =
      (2 : ℝ) ^ (n * n) * (∏ i : Fin n, weights (σ i) i) := by
    intro σ
    rw [Finset.sum_eq_single σ]
    · have hsign2 : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
        have h : ((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ)) = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
        exact_mod_cast h
      rw [hsign2, one_mul]
      have hterm : ∀ s : Fin n × Fin n → Bool,
          (∏ i : Fin n, signed s (σ i) i) * (∏ i : Fin n, signed s (σ i) i) =
            ∏ i : Fin n, weights (σ i) i := by
        intro s
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl ?_
        intro i _
        simp only [signed, weights]
        split_ifs <;> ring
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : Fintype.card (Fin n × Fin n → Bool) = 2 ^ (n * n) := by
        simp [Fintype.card_fun, Fintype.card_prod]
      rw [hcard]
      push_cast
      rfl
    · intro τ _ hne
      have h0 : (∑ s : Fin n × Fin n → Bool,
          (∏ i : Fin n, signed s (σ i) i) * (∏ i : Fin n, signed s (τ i) i)) = 0 :=
        PEqualNP.Outside.L_lib_459_aux.sum_prod_signed_ne A σ τ hne.symm
      rw [h0, mul_zero]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ σ))
  simp_rw [hdiag, ← Finset.mul_sum]
  rfl
