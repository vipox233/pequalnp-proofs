import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_469 : (∀ (n m : ℕ) (P N : Fin m → Finset (Fin n)),
  (∃ x : Fin n → Bool, ∀ i, (∃ v ∈ P i, x v = true) ∨ (∃ v ∈ N i, x v = false)) ↔
    ∃ z : Fin n → ℤ, (∀ v, z v = 0 ∨ z v = 1) ∧
      ∀ i, 1 ≤ (P i).sum z + (N i).sum (fun v => 1 - z v)) := by
  intro n m P N
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun v => if x v = true then 1 else 0, ?_, ?_⟩
    · intro v
      by_cases h : x v = true <;> simp [h]
    · intro i
      have hP : 0 ≤ (P i).sum (fun v => if x v = true then (1 : ℤ) else 0) :=
        Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
      have hN : 0 ≤ (N i).sum (fun v => 1 - if x v = true then (1 : ℤ) else 0) :=
        Finset.sum_nonneg (fun v _ => by split_ifs <;> norm_num)
      rcases hx i with ⟨v, hv, hxv⟩ | ⟨v, hv, hxv⟩
      · have := Finset.single_le_sum
          (f := fun v => if x v = true then (1 : ℤ) else 0)
          (fun v _ => by split_ifs <;> norm_num) hv
        simp only [hxv, if_true] at this
        linarith
      · have := Finset.single_le_sum
          (f := fun v => 1 - if x v = true then (1 : ℤ) else 0)
          (fun v _ => by split_ifs <;> norm_num) hv
        simp only [hxv, Bool.false_eq_true, if_false] at this
        linarith
  · rintro ⟨z, hz, hsum⟩
    refine ⟨fun v => decide (z v = 1), ?_⟩
    intro i
    by_contra hcon
    push_neg at hcon
    obtain ⟨hP, hN⟩ := hcon
    have h1 : (P i).sum z = 0 := Finset.sum_eq_zero (fun v hv => by
      have := hP v hv
      rcases hz v with h | h
      · exact h
      · simp [h] at this)
    have h2 : (N i).sum (fun v => 1 - z v) = 0 := Finset.sum_eq_zero (fun v hv => by
      have := hN v hv
      simp only [ne_eq, decide_eq_false_iff_not, not_not, Bool.not_eq_false,
        decide_eq_true_eq] at this
      rw [this]; norm_num)
    have := hsum i
    rw [h1, h2] at this
    norm_num at this
