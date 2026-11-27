import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_465

theorem exu_of_inj {E : Type} [DecidableEq E] {n : ℕ} (M : Finset E) (π : E → Fin n)
    (hc : M.card = n) (hi : Set.InjOn π (M : Set E)) (a : Fin n) :
    ∃! e : E, e ∈ M ∧ π e = a := by
  have himg : M.image π = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hi, hc]; simp
  have : a ∈ M.image π := by rw [himg]; exact Finset.mem_univ a
  obtain ⟨e, he, hea⟩ := Finset.mem_image.1 this
  refine ⟨e, ⟨he, hea⟩, ?_⟩
  rintro e' ⟨he', hea'⟩
  exact hi he' he (hea'.trans hea.symm)

theorem inj_of_exu {E : Type} [DecidableEq E] {n : ℕ} (M : Finset E) (π : E → Fin n)
    (h : ∀ a : Fin n, ∃! e : E, e ∈ M ∧ π e = a) :
    M.card = n ∧ Set.InjOn π (M : Set E) := by
  have hi : Set.InjOn π (M : Set E) := by
    intro e he e' he' hee
    obtain ⟨x, -, hx⟩ := h (π e)
    exact (hx e ⟨he, rfl⟩).trans (hx e' ⟨he', hee.symm⟩).symm
  refine ⟨?_, hi⟩
  have himg : M.image π = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro a
    obtain ⟨e, ⟨he, hea⟩, -⟩ := h a
    exact Finset.mem_image.2 ⟨e, he, hea⟩
  have := Finset.card_image_of_injOn hi
  rw [himg] at this
  simpa using this.symm

end PEqualNP.Outside.L_lib_465

theorem PEqualNP.Outside.L_lib_465 : ∀ (n : ℕ) (T : Finset (Fin n × Fin n × Fin n)),
  (∃ M : Finset (Fin n × Fin n × Fin n), M ⊆ T ∧ M.card = n ∧
    Set.InjOn (fun e : Fin n × Fin n × Fin n => e.1) (M : Set _) ∧
    Set.InjOn (fun e : Fin n × Fin n × Fin n => e.2.1) (M : Set _) ∧ Set.InjOn (fun e : Fin n × Fin n × Fin n => e.2.2) (M : Set _)) ↔
  ∃ M : Finset (Fin n × Fin n × Fin n), M ⊆ T ∧
    ∀ u : Fin 3 × Fin n, ∃! e : Fin n × Fin n × Fin n, e ∈ M ∧
      ((u.1 = 0 ∧ e.1 = u.2) ∨ (u.1 = 1 ∧ e.2.1 = u.2) ∨
       (u.1 = 2 ∧ e.2.2 = u.2)) := by
  intro n T
  constructor
  · rintro ⟨M, hMT, hc, h1, h2, h3⟩
    refine ⟨M, hMT, fun u => ?_⟩
    obtain ⟨a, b⟩ := u
    fin_cases a
    · obtain ⟨e, ⟨he, hea⟩, hu⟩ := PEqualNP.Outside.L_lib_465.exu_of_inj M (fun e => e.1) hc h1 b
      refine ⟨e, ⟨he, Or.inl ⟨rfl, hea⟩⟩, ?_⟩
      rintro e' ⟨he', h'⟩
      apply hu e'
      refine ⟨he', ?_⟩
      rcases h' with ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩
      · exact h'
      · exact absurd h' (by simp)
      · exact absurd h' (by simp)
    · obtain ⟨e, ⟨he, hea⟩, hu⟩ := PEqualNP.Outside.L_lib_465.exu_of_inj M (fun e => e.2.1) hc h2 b
      refine ⟨e, ⟨he, Or.inr (Or.inl ⟨rfl, hea⟩)⟩, ?_⟩
      rintro e' ⟨he', h'⟩
      apply hu e'
      refine ⟨he', ?_⟩
      rcases h' with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩
      · exact absurd h' (by simp)
      · exact h'
      · exact absurd h' (by simp)
    · obtain ⟨e, ⟨he, hea⟩, hu⟩ := PEqualNP.Outside.L_lib_465.exu_of_inj M (fun e => e.2.2) hc h3 b
      refine ⟨e, ⟨he, Or.inr (Or.inr ⟨rfl, hea⟩)⟩, ?_⟩
      rintro e' ⟨he', h'⟩
      apply hu e'
      refine ⟨he', ?_⟩
      rcases h' with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩
      · exact absurd h' (by simp)
      · exact absurd h' (by simp)
      · exact h'
  · rintro ⟨M, hMT, h⟩
    have g1 : ∀ a : Fin n, ∃! e : Fin n × Fin n × Fin n, e ∈ M ∧ e.1 = a := by
      intro a
      obtain ⟨e, ⟨he, hh⟩, hu⟩ := h (0, a)
      refine ⟨e, ⟨he, by rcases hh with ⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> first | exact h' | exact absurd h' (by simp)⟩, ?_⟩
      rintro e' ⟨he', h'⟩
      exact hu e' ⟨he', Or.inl ⟨rfl, h'⟩⟩
    have g2 : ∀ a : Fin n, ∃! e : Fin n × Fin n × Fin n, e ∈ M ∧ e.2.1 = a := by
      intro a
      obtain ⟨e, ⟨he, hh⟩, hu⟩ := h (1, a)
      refine ⟨e, ⟨he, by rcases hh with ⟨h', -⟩ | ⟨-, h'⟩ | ⟨h', -⟩ <;> first | exact h' | exact absurd h' (by simp)⟩, ?_⟩
      rintro e' ⟨he', h'⟩
      exact hu e' ⟨he', Or.inr (Or.inl ⟨rfl, h'⟩)⟩
    have g3 : ∀ a : Fin n, ∃! e : Fin n × Fin n × Fin n, e ∈ M ∧ e.2.2 = a := by
      intro a
      obtain ⟨e, ⟨he, hh⟩, hu⟩ := h (2, a)
      refine ⟨e, ⟨he, by rcases hh with ⟨h', -⟩ | ⟨h', -⟩ | ⟨-, h'⟩ <;> first | exact h' | exact absurd h' (by simp)⟩, ?_⟩
      rintro e' ⟨he', h'⟩
      exact hu e' ⟨he', Or.inr (Or.inr ⟨rfl, h'⟩)⟩
    obtain ⟨hc, h1⟩ := PEqualNP.Outside.L_lib_465.inj_of_exu M (fun e => e.1) g1
    obtain ⟨-, h2⟩ := PEqualNP.Outside.L_lib_465.inj_of_exu M (fun e => e.2.1) g2
    obtain ⟨-, h3⟩ := PEqualNP.Outside.L_lib_465.inj_of_exu M (fun e => e.2.2) g3
    exact ⟨M, hMT, hc, h1, h2, h3⟩
