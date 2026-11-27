import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_476 : ∀ (n m : ℕ) (C : Fin m → Finset (Fin n × Bool)) (A B : Finset (Fin n × Bool)),
  (∃ x : Fin n → Bool,
    (∀ i, ∃ l ∈ C i, x l.1 = l.2) ∧ ∃ l ∈ A ∪ B, x l.1 = l.2) ↔
  ∃ y : Option (Fin n) → Bool,
    (∀ i, ∃ l ∈ C i, y (some l.1) = l.2) ∧
    ((∃ l ∈ A, y (some l.1) = l.2) ∨ y none = true) ∧
    ((∃ l ∈ B, y (some l.1) = l.2) ∨ y none = false) := by
  intro n m C A B
  constructor
  · rintro ⟨x, hC, l, hl, hx⟩
    by_cases ha : ∃ l ∈ A, x l.1 = l.2
    · exact ⟨fun o => o.elim false x, hC, Or.inl ha, Or.inr rfl⟩
    · have hlB : l ∈ B := by
        rcases Finset.mem_union.mp hl with h | h
        · exact absurd ⟨l, h, hx⟩ ha
        · exact h
      exact ⟨fun o => o.elim true x, hC, Or.inr rfl, Or.inl ⟨l, hlB, hx⟩⟩
  · rintro ⟨y, hC, hA, hB⟩
    refine ⟨fun v => y (some v), hC, ?_⟩
    cases h : y none
    · rcases hA with ⟨l, hl, hx⟩ | hA
      · exact ⟨l, Finset.mem_union_left _ hl, hx⟩
      · rw [h] at hA; exact absurd hA (by decide)
    · rcases hB with ⟨l, hl, hx⟩ | hB
      · exact ⟨l, Finset.mem_union_right _ hl, hx⟩
      · rw [h] at hB; exact absurd hB (by decide)
