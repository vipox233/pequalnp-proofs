import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_498 : ∀ (n p q : ℕ) (A : Fin p → Finset (Fin n × Bool))
    (B : Fin q → Finset (Fin n × Bool)) (x : Fin n → Bool),
  let holds := fun C : Finset (Fin n × Bool) => ∃ l ∈ C, x l.1 = l.2
  (∃ t : Bool, (∀ i, holds (A i) ∨ t = true) ∧ (∀ j, holds (B j) ∨ t = false)) ↔
    ∀ i j, holds (A i ∪ B j) := by
  intro n p q A B x holds
  have hu : ∀ C D : Finset (Fin n × Bool), holds (C ∪ D) ↔ holds C ∨ holds D := by
    intro C D
    simp only [holds, Finset.mem_union]
    constructor
    · rintro ⟨l, hl | hl, h⟩
      · exact Or.inl ⟨l, hl, h⟩
      · exact Or.inr ⟨l, hl, h⟩
    · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
      · exact ⟨l, Or.inl hl, h⟩
      · exact ⟨l, Or.inr hl, h⟩
  constructor
  · rintro ⟨t, h1, h2⟩ i j
    rw [hu]
    cases t
    · exact Or.inl ((h1 i).resolve_right (by simp))
    · exact Or.inr ((h2 j).resolve_right (by simp))
  · intro h
    by_cases hA : ∀ i, holds (A i)
    · exact ⟨false, fun i => Or.inl (hA i), fun j => Or.inr rfl⟩
    · push Not at hA
      obtain ⟨i0, hi0⟩ := hA
      refine ⟨true, fun i => Or.inr rfl, fun j => Or.inl ?_⟩
      exact ((hu _ _).1 (h i0 j)).resolve_left hi0
