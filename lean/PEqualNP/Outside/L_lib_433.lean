import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_433 : ∀ (m n d : ℕ) (A : Fin d → Finset (Fin m)) (B : Fin d → Finset (Fin n)),
  let U : Matrix (Fin m) (Fin n) ℚ := fun i j =>
    if ∃ t, i ∈ A t ∧ j ∈ B t then 1 else 0
  U.rank ≤ 2 ^ d - 1 := by
  classical
  intro m n d A B
  dsimp only
  let codes : Finset (Finset (Fin d)) := Finset.univ.erase ∅
  let code (i : Fin m) : Finset (Fin d) := Finset.univ.filter fun t => i ∈ A t
  have mem_code (i : Fin m) (t : Fin d) : t ∈ code i ↔ i ∈ A t := by
    simp [code]
  let L : Matrix (Fin m) codes ℚ := fun i s => if s.val = code i then 1 else 0
  let R : Matrix codes (Fin n) ℚ := fun s j => if ∃ t ∈ s.val, j ∈ B t then 1 else 0
  have factor : L * R = (fun i j => if ∃ t, i ∈ A t ∧ j ∈ B t then 1 else 0) := by
    ext i j
    rw [Matrix.mul_apply]
    by_cases hi : code i = ∅
    · have hs (s : codes) : s.val ≠ code i := by
        rw [hi]
        exact (Finset.mem_erase.mp s.property).1
      have hn : ¬ ∃ t, i ∈ A t ∧ j ∈ B t := by
        rintro ⟨t, ht, _⟩
        have hm := (mem_code i t).2 ht
        simpa [hi] using hm
      simp [L, hs, hn]
    · let s : codes := ⟨code i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩⟩
      rw [Fintype.sum_eq_single s]
      · simp [L, R, s, mem_code]
      · intro a ha
        have hne : a.val ≠ code i := fun h => ha (Subtype.ext h)
        simp [L, hne]
  rw [← factor]
  calc
    (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card codes := Matrix.rank_le_card_width L
    _ = 2 ^ d - 1 := by
      rw [Fintype.card_coe]
      simp [codes, Finset.card_erase_of_mem, Fintype.card_finset]
