import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace PEqualNP.Outside.L_lib_804

open Finset Matrix

theorem expansion {I : Type} [Fintype I] [DecidableEq I]
    (M : Matrix I I (ZMod 2)) (A : Finset I) :
    (1 + M.submatrix (Subtype.val : A → I) Subtype.val).det =
      ∑ J ∈ A.powerset, (M.submatrix (Subtype.val : J → I) Subtype.val).det := by
  classical
  let N : Matrix I I (ZMod 2) := Matrix.of (A.piecewise M 0)
  have hn (i j : I) : N i j = if i ∈ A then M i j else 0 := by
    by_cases hi : i ∈ A <;> simp [N, Finset.piecewise, hi]
  have hm : 1 + N = Matrix.of (A.piecewise (Matrix.row (1 + M))
      (Matrix.row (1 : Matrix I I (ZMod 2)))) := by
    ext i j
    by_cases hi : i ∈ A <;> simp [Matrix.add_apply, hn, Finset.piecewise, hi]
  have hd : (1 + N).det = (1 + M.submatrix (Subtype.val : A → I) Subtype.val).det := by
    rw [hm, Matrix.det_piecewise_one_eq_submatrix_det]
    congr 1
    ext i j
    change (1 : Matrix I I (ZMod 2)) i.val j.val + M i.val j.val =
      (1 : Matrix A A (ZMod 2)) i j + M i.val j.val
    congr 1
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne (fun h => hij (Subtype.ext h)), Matrix.one_apply_ne hij]
  rw [← hd, add_comm]
  let D := (Matrix.detRowAlternating : (I → ZMod 2) [⋀^I]→ₗ[ZMod 2] ZMod 2)
  let u : I → I → ZMod 2 := Matrix.row N
  let v : I → I → ZMod 2 := Matrix.row (1 : Matrix I I (ZMod 2))
  change D (u + v) = _
  rw [D.map_add_univ]
  have hminor (J : Finset I) :
      D (J.piecewise u v) = (N.submatrix (Subtype.val : J → I) Subtype.val).det :=
    Matrix.det_piecewise_one_eq_submatrix_det N J
  simp_rw [hminor]
  refine (Finset.sum_subset (s₁ := A.powerset) (fun J _ => Finset.mem_univ J) ?_).symm.trans ?_
  · intro J _ hJ
    have hj : ¬ J ⊆ A := by simpa using hJ
    change ¬ ∀ i ∈ J, i ∈ A at hj
    push Not at hj
    obtain ⟨i, hiJ, hiA⟩ := hj
    exact Matrix.det_eq_zero_of_row_eq_zero ⟨i, hiJ⟩ (fun j => by simp [Matrix.submatrix, hn, hiA])
  · apply Finset.sum_congr rfl
    intro J hJ
    congr 1
    ext i j
    simp [Matrix.submatrix, hn, Finset.mem_powerset.mp hJ i.property]

end PEqualNP.Outside.L_lib_804

theorem PEqualNP.Outside.L_lib_804 : (let F := ZMod 2
∀ (n g : ℕ) (part : Fin n → Fin g) (H : Matrix (Fin n) (Fin n) F),
  let sub := fun (J : Finset (Fin n)) => H.submatrix (fun i : ↥J => i.val) (fun i : ↥J => i.val)
  let active := fun (S : Finset (Fin g)) => Finset.univ.filter (fun i => part i ∈ S)
  let coef := fun (U : Finset (Fin g)) =>
    ∑ J ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.image part = U)),
      (sub J).det
  (∃ S : Finset (Fin g), (1 + sub (active S)).det = 0) ↔
    ∃ U : Finset (Fin g), U.Nonempty ∧ coef U ≠ 0) := by
  classical
  dsimp only
  intro n g part H
  let sub := fun (J : Finset (Fin n)) => H.submatrix (fun i : ↥J => i.val) (fun i : ↥J => i.val)
  let active := fun (S : Finset (Fin g)) => Finset.univ.filter (fun i => part i ∈ S)
  let coef := fun (U : Finset (Fin g)) =>
    ∑ J ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.image part = U)), (sub J).det
  change (∃ S, (1 + sub (active S)).det = 0) ↔ ∃ U, U.Nonempty ∧ coef U ≠ 0
  have hzero : coef ∅ = 1 := by
    have he : ((Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.image part = ∅)) =
        {∅} := by ext J; simp [Finset.image_eq_empty]
    unfold coef
    rw [he, Finset.sum_singleton]
    simp [sub, Matrix.det_isEmpty]
  have hsum (S : Finset (Fin g)) : (1 + sub (active S)).det = ∑ U ∈ S.powerset, coef U := by
    rw [PEqualNP.Outside.L_lib_804.expansion H (active S)]
    have hmap : ∀ J ∈ (active S).powerset, J.image part ∈ S.powerset := by
      intro J hJ
      exact Finset.mem_powerset.mpr (Finset.image_subset_iff.mpr (fun i hi =>
        (Finset.mem_filter.mp (Finset.mem_powerset.mp hJ hi)).2))
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun J => (sub J).det)]
    apply Finset.sum_congr rfl
    intro U hU
    unfold coef
    congr 1
    ext J
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    constructor
    · exact And.right
    · intro hJU
      refine ⟨?_, hJU⟩
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_powerset.mp hU
        (hJU ▸ Finset.mem_image_of_mem part hi)⟩
  have binary (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
    have hlt : a.val < 2 := ZMod.val_lt a
    have hn : a.val ≠ 0 := fun h => ha ((ZMod.val_eq_zero a).mp h)
    apply ZMod.val_injective 2
    have h1 : (1 : ZMod 2).val = 1 := by decide
    omega
  have sumRest (S : Finset (Fin g)) (hS : S.Nonempty)
      (h : ∀ U ∈ S.powerset.erase S, U.Nonempty → coef U = 0) :
      ∑ U ∈ S.powerset.erase S, coef U = 1 := by
    rw [← hzero]
    apply Finset.sum_eq_single ∅
    · intro U hU hn
      exact h U hU (Finset.nonempty_iff_ne_empty.mpr hn)
    · intro hm
      exact (hm (Finset.mem_erase.mpr ⟨hS.ne_empty.symm, Finset.mem_powerset.mpr (Finset.empty_subset _)⟩)).elim
  constructor
  · rintro ⟨S, hS⟩
    by_contra hn
    push Not at hn
    rw [hsum, Finset.sum_eq_single ∅ (fun U _ hU => hn U (Finset.nonempty_iff_ne_empty.mpr hU))
      (fun he => (he (Finset.mem_powerset.mpr (Finset.empty_subset _))).elim), hzero] at hS
    exact one_ne_zero hS
  · intro hex
    by_contra hn
    push Not at hn
    have van : ∀ k : ℕ, ∀ U : Finset (Fin g), U.card = k → U.Nonempty → coef U = 0 := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro U hk hU
        have hdet := binary _ (hn U)
        rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_powerset.mpr (Finset.Subset.refl U))] at hdet
        have hrest := sumRest U hU (fun V hV hne => by
          obtain ⟨hneU, hVU⟩ := Finset.mem_erase.mp hV
          have hlt : V.card < U.card := Finset.card_lt_card
            (ssubset_of_subset_of_ne (Finset.mem_powerset.mp hVU) hneU)
          exact ih V.card (hk ▸ hlt) V rfl hne)
        rw [hrest] at hdet
        exact add_left_cancel (hdet.trans (add_zero (1 : ZMod 2)).symm)
    obtain ⟨U, hU, hne⟩ := hex
    exact hne (van U.card U rfl hU)

