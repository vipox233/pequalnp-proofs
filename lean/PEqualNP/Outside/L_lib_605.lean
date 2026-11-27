import Mathlib

namespace PEqualNP.Outside.L_lib_605_aux

theorem part1 (m r : ℕ) (label : Fin m → Fin (m+1) → (Fin r → Bool)) :
    (∀ x : Fin m → (Fin r → Bool), ∃ a, ∀ i, x i ≠ label i a) ↔ ∀ i, Function.Injective (label i) := by
  constructor
  · intro hcov i a a' heq
    by_contra hne
    obtain ⟨k0, hk0⟩ := Fin.exists_succAbove_eq hne
    let σ : Fin m → Fin (m+1) := fun k => a'.succAbove (Equiv.swap i k0 k)
    obtain ⟨v, hv⟩ := hcov (fun k => label k (σ k))
    by_cases hva : v = a'
    · subst hva
      apply hv i
      simp only [σ, Equiv.swap_apply_left, hk0, heq]
    · obtain ⟨k', hk'⟩ := Fin.exists_succAbove_eq hva
      apply hv (Equiv.swap i k0 k')
      simp only [σ, Equiv.swap_apply_self, hk']
  · intro hinj x
    by_contra h
    push_neg at h
    choose f hf using h
    obtain ⟨a, a', hne, hfa⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
    apply hne
    apply hinj (f a)
    rw [← hf a, hfa, hf a']

theorem main (m r : ℕ) (label : Fin m → Fin (m+1) → (Fin r → Bool)) :
    ((∀ x : Fin m → (Fin r → Bool), ∃ a, ∀ i, x i ≠ label i a) ↔ ∀ i, Function.Injective (label i)) ∧
    ((∀ x : Fin m → (Fin r → Bool), ∃ a, ∀ i, x i ≠ label i a) → ∀ b : Fin (m+1), ∃ order : Fin m → Fin (m+1),
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : Fin (m+1)),
        (∀ i, label i (if flags i then b else order i) ≠ label i v) ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j)) := by
  refine ⟨part1 m r label, ?_⟩
  intro hcov b
  have hinj := (part1 m r label).mp hcov
  refine ⟨b.succAbove, Fin.succAbove_right_injective, fun i => Fin.succAbove_ne b i, ?_⟩
  intro flags v
  have hok : (∀ i, label i (if flags i then b else b.succAbove i) ≠ label i v) ↔
      ∀ i, (if flags i then b else b.succAbove i) ≠ v :=
    forall_congr' (fun i => (hinj i).ne_iff)
  rw [hok]
  constructor
  · intro h
    by_cases hall : ∀ j, flags j = false
    · left
      refine ⟨?_, hall⟩
      by_contra hvb
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hvb
      apply h k
      rw [if_neg (by simp [hall k]), hk]
    · right
      push_neg at hall
      obtain ⟨j, hj⟩ := hall
      have hj' : flags j = true := by simpa using hj
      have hvb : v ≠ b := by
        intro hvb
        apply h j
        rw [if_pos hj', hvb]
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hvb
      refine ⟨k, ?_, hk.symm⟩
      by_contra hfk
      apply h k
      rw [if_neg hfk, hk]
  · rintro (⟨rfl, hall⟩ | ⟨j, hj, rfl⟩) i
    · rw [if_neg (by simp [hall i])]
      exact Fin.succAbove_ne v i
    · by_cases hfi : flags i = true
      · rw [if_pos hfi]
        exact (Fin.succAbove_ne b j).symm
      · rw [if_neg hfi]
        intro heq
        have := Fin.succAbove_right_injective heq
        subst this
        exact hfi hj

end PEqualNP.Outside.L_lib_605_aux

theorem PEqualNP.Outside.L_lib_605 : ∀ (m r : Nat),
  let A := Fin (m+1)
  let W := Fin r → Bool
  ∀ label : Fin m → A → W,
    let ok := fun (x : Fin m → W) (a : A) => ∀ i, x i ≠ label i a
    let covers := ∀ x, ∃ a, ok x a
    (covers ↔ ∀ i, Function.Injective (label i)) ∧
    (covers → ∀ b : A, ∃ order : Fin m → A,
      Function.Injective order ∧ (∀ i, order i ≠ b) ∧
      ∀ (flags : Fin m → Bool) (v : A),
        ok (fun pos => label pos (if flags pos then b else order pos)) v ↔
          (v = b ∧ ∀ j, flags j = false) ∨ (∃ j, flags j = true ∧ v = order j)) := by
  intro m r A W label ok covers
  exact PEqualNP.Outside.L_lib_605_aux.main m r label
