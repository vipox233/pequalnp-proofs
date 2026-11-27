import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_467 : ∀ (n m : ℕ) (A : Fin m → Finset (Fin (3 * n))), (∀ i, (A i).card = 3) →
  ((∃ S : Finset (Fin m), S.card ≤ n ∧ ∀ x, ∃ i ∈ S, x ∈ A i) ↔
   ∃ S : Finset (Fin m), ∀ x : Fin (3 * n), ∃! i : Fin m, i ∈ S ∧ x ∈ A i) := by
  intro n m A hA
  have hdc : ∀ S : Finset (Fin m), ∑ x : Fin (3 * n), (S.filter (fun i => x ∈ A i)).card = 3 * S.card := by
    intro S
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have : ∀ i ∈ S, ∑ x : Fin (3 * n), (if x ∈ A i then 1 else 0) = 3 := by
      intro i _
      have := hA i
      simpa [Finset.sum_boole] using this
    rw [Finset.sum_congr rfl this]
    simp [mul_comm]
  constructor
  · rintro ⟨S, hS, hcov⟩
    have hge : ∀ x, 1 ≤ (S.filter (fun i => x ∈ A i)).card := fun x => by
      obtain ⟨i, hi, hx⟩ := hcov x
      exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hx⟩⟩
    have hone : ∀ x, (S.filter (fun i => x ∈ A i)).card = 1 := by
      intro x
      by_contra hne
      have hlt : 1 < (S.filter (fun i => x ∈ A i)).card := by have := hge x; omega
      have : ∑ _y : Fin (3 * n), 1 < ∑ y : Fin (3 * n), (S.filter (fun i => y ∈ A i)).card :=
        Finset.sum_lt_sum (fun y _ => hge y) ⟨x, Finset.mem_univ _, hlt⟩
      rw [hdc S] at this
      simp at this
      omega
    refine ⟨S, fun x => ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (hone x)
    have hamem : a ∈ S.filter (fun i => x ∈ A i) := by rw [ha]; simp
    refine ⟨a, ⟨(Finset.mem_filter.1 hamem).1, (Finset.mem_filter.1 hamem).2⟩, ?_⟩
    rintro b ⟨hbS, hbx⟩
    have : b ∈ S.filter (fun i => x ∈ A i) := Finset.mem_filter.2 ⟨hbS, hbx⟩
    rw [ha] at this
    simpa using this
  · rintro ⟨S, hS⟩
    have hone : ∀ x, (S.filter (fun i => x ∈ A i)).card = 1 := by
      intro x
      obtain ⟨a, ⟨haS, hax⟩, huniq⟩ := hS x
      apply Finset.card_eq_one.2
      refine ⟨a, ?_⟩
      ext b
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hb; exact huniq b hb
      · rintro rfl; exact ⟨haS, hax⟩
    have h1 := hdc S
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
    refine ⟨S, by omega, fun x => ?_⟩
    obtain ⟨a, ⟨haS, hax⟩, -⟩ := hS x
    exact ⟨a, haS, hax⟩
