import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_462 : ∀ (n m k : ℕ) (A : Fin m → Finset (Fin n)), 0 < n →
  (∀ x, ∃ j, x ∈ A j) →
  ((∃ I : Finset (Fin m), I.card ≤ k ∧ ∀ x, ∃ j ∈ I, x ∈ A j) ↔
   ∃ (I : Finset (Fin m)) (X : Finset (Fin n)), I.card + X.card ≤ k ∧
     (∀ x, x ∈ X ∨ ∃ j ∈ I, x ∈ A j) ∧
     ∀ j, I.Nonempty ∨ ∃ x ∈ X, x ∈ A j) := by
  intro n m k A hn hcov
  constructor
  · rintro ⟨I, hI, hc⟩
    refine ⟨I, ∅, by simpa using hI, fun x => Or.inr (hc x), fun j => Or.inl ?_⟩
    obtain ⟨i, hi, -⟩ := hc ⟨0, hn⟩
    exact ⟨i, hi⟩
  · rintro ⟨I, X, hk, hx, -⟩
    choose pick hpick using hcov
    refine ⟨I ∪ X.image pick, ?_, fun x => ?_⟩
    · calc (I ∪ X.image pick).card ≤ I.card + (X.image pick).card := Finset.card_union_le _ _
        _ ≤ I.card + X.card := by gcongr; exact Finset.card_image_le
        _ ≤ k := hk
    · rcases hx x with h | ⟨j, hj, hxj⟩
      · exact ⟨pick x, Finset.mem_union_right _ (Finset.mem_image.2 ⟨x, h, rfl⟩), hpick x⟩
      · exact ⟨j, Finset.mem_union_left _ hj, hxj⟩
