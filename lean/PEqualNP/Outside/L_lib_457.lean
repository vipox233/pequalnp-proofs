import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Basic

namespace PEqualNP.Outside.L_lib_457_aux

open Finset

theorem perm_zero_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    A.permanent = 0 ↔ ∀ σ : Equiv.Perm (Fin n), ∃ i, A (σ i) i = 0 := by
  simp [Matrix.permanent, Finset.sum_eq_zero_iff, Finset.prod_eq_zero_iff]

theorem main {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    A.permanent = 0 ↔
      ∃ R C : Finset (Fin n), n < R.card + C.card ∧ ∀ i ∈ R, ∀ j ∈ C, A i j = 0 := by
  classical
  rw [perm_zero_iff]
  constructor
  · intro h
    by_contra hne
    let t : Fin n → Finset (Fin n) := fun j => univ.filter (fun i => A i j ≠ 0)
    have hall : ∀ s : Finset (Fin n), s.card ≤ (s.biUnion t).card := by
      intro s
      by_contra hlt
      have hlt' := not_le.mp hlt
      apply hne
      refine ⟨(s.biUnion t)ᶜ, s, ?_, ?_⟩
      · rw [card_compl, Fintype.card_fin]
        have := card_le_univ (s.biUnion t)
        rw [Fintype.card_fin] at this
        omega
      · intro i hi j hj
        rw [mem_compl, mem_biUnion] at hi
        by_contra hA
        exact hi ⟨j, hj, mem_filter.mpr ⟨mem_univ _, hA⟩⟩
    obtain ⟨f, hf, hft⟩ := (all_card_le_biUnion_card_iff_exists_injective t).mp hall
    obtain ⟨i, hi⟩ := h (Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf))
    rw [Equiv.ofBijective_apply] at hi
    exact (mem_filter.mp (hft i)).2 hi
  · rintro ⟨R, C, hcard, hz⟩ σ
    by_contra hne
    have hne' : ∀ i, A (σ i) i ≠ 0 := fun i hi => hne ⟨i, hi⟩
    have hmap : ∀ j ∈ C, σ j ∈ Rᶜ := by
      intro j hj
      rw [mem_compl]
      intro hR
      exact hne' j (hz _ hR j hj)
    have h1 := card_le_card_of_injOn σ hmap σ.injective.injOn
    rw [card_compl, Fintype.card_fin] at h1
    have h2 := card_le_univ R
    rw [Fintype.card_fin] at h2
    omega

end PEqualNP.Outside.L_lib_457_aux

theorem PEqualNP.Outside.L_lib_457 : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ),
  A.permanent = 0 ↔
    ∃ R C : Finset (Fin n), n < R.card + C.card ∧ ∀ i ∈ R, ∀ j ∈ C, A i j = 0 := by
  intro n A
  exact PEqualNP.Outside.L_lib_457_aux.main A
