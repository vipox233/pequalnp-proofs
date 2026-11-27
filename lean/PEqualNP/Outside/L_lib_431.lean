import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_431 : (∀ (m n r : ℕ) (A : Matrix (Fin m) (Fin r) ℝ) (B : Matrix (Fin r) (Fin n) ℝ),
  (∀ x t, 0 ≤ A x t) → (∀ t y, 0 ≤ B t y) →
  ∃ (rows : Fin r → Finset (Fin m)) (cols : Fin r → Finset (Fin n)),
    ∀ i j, 0 < (A * B) i j ↔ ∃ s, i ∈ rows s ∧ j ∈ cols s) := by
  intro m n r A B hA hB
  set rows : Fin r → Finset (Fin m) :=
    fun t => Finset.univ.filter (fun x => 0 < A x t) with hrows
  set cols : Fin r → Finset (Fin n) :=
    fun t => Finset.univ.filter (fun y => 0 < B t y) with hcols
  refine ⟨rows, cols, ?_⟩
  intro i j
  have hnn : ∀ t : Fin r, 0 ≤ A i t * B t j :=
    fun t => mul_nonneg (hA i t) (hB t j)
  have hmul : (A * B) i j = ∑ t : Fin r, A i t * B t j := Matrix.mul_apply
  constructor
  · intro hij
    rw [hmul] at hij
    have hex : ∃ t, 0 < A i t * B t j := by
      by_contra h
      simp only [not_exists, not_lt] at h
      have hz : ∑ t : Fin r, A i t * B t j = 0 :=
        Finset.sum_eq_zero (fun t _ => le_antisymm (h t) (hnn t))
      exact (lt_self_iff_false (0 : ℝ)).mp (hz ▸ hij)
    obtain ⟨t, ht⟩ := hex
    have hApos : 0 < A i t := by nlinarith [hA i t, hB t j]
    have hBpos : 0 < B t j := by nlinarith [hA i t, hB t j]
    refine ⟨t, ?_, ?_⟩
    · rw [hrows, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hApos⟩
    · rw [hcols, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hBpos⟩
  · intro ⟨s, hi, hj⟩
    have hApos : 0 < A i s := by
      rw [hrows, Finset.mem_filter] at hi
      exact hi.2
    have hBpos : 0 < B s j := by
      rw [hcols, Finset.mem_filter] at hj
      exact hj.2
    have hpos : 0 < A i s * B s j := mul_pos hApos hBpos
    have hle : A i s * B s j ≤ ∑ t : Fin r, A i t * B t j :=
      Finset.single_le_sum (fun t _ => hnn t) (Finset.mem_univ s)
    have : 0 < ∑ t : Fin r, A i t * B t j := lt_of_lt_of_le hpos hle
    exact (hmul ▸ this)
