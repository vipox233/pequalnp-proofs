import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_464 : ∀ (n t : ℕ) (w : Fin n → ℕ),
  let W := ∑ i, w i
  let v : Fin n ⊕ Bool → ℕ := Sum.elim w (fun b => if b then W + t else 2 * W - t)
  t ≤ W →
  ((∃ S : Finset (Fin n), (∑ i ∈ S, w i) = t) ↔
   ∃ H : Finset (Fin n ⊕ Bool), (∑ i ∈ H, v i) = ∑ i ∈ Hᶜ, v i) := by
  intro n t w W v ht
  have hsplit : ∀ H : Finset (Fin n ⊕ Bool), ∑ i ∈ H, v i =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ H), w j +
      (if Sum.inr true ∈ H then W + t else 0) + (if Sum.inr false ∈ H then 2 * W - t else 0) := by
    intro H
    have h1 : ∑ i ∈ H, v i = ∑ i : Fin n ⊕ Bool, (if i ∈ H then v i else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1, Fintype.sum_sum_type, Fintype.sum_bool, Finset.sum_filter]
    simp [v]
    ring
  have hW : ∀ S : Finset (Fin n), ∑ j ∈ S, w j + ∑ j ∈ Sᶜ, w j = W := fun S => by
    rw [Finset.sum_add_sum_compl]
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S.image Sum.inl ∪ {Sum.inr false}, ?_⟩
    rw [hsplit, hsplit]
    have e1 : Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ S.image Sum.inl ∪ {Sum.inr false}) = S := by
      ext j; simp
    have e2 : Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ (S.image Sum.inl ∪ {Sum.inr false})ᶜ) = Sᶜ := by
      ext j; simp
    rw [e1, e2]
    have := hW S
    simp
    omega
  · rintro ⟨H, hH⟩
    rw [hsplit, hsplit] at hH
    have e3 : Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ Hᶜ) =
        (Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ H))ᶜ := by
      ext j; simp
    rw [e3] at hH
    have := hW (Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ H))
    set S := Finset.univ.filter (fun j : Fin n => Sum.inl j ∈ H) with hSdef
    by_cases hT : (Sum.inr true : Fin n ⊕ Bool) ∈ H <;> by_cases hF : (Sum.inr false : Fin n ⊕ Bool) ∈ H <;>
      simp only [hT, hF, Finset.mem_compl, not_true_eq_false, not_false_eq_true, ite_true, ite_false] at hH
    · exact ⟨∅, by simp; omega⟩
    · exact ⟨Sᶜ, by omega⟩
    · exact ⟨S, by omega⟩
    · exact ⟨∅, by simp; omega⟩
