import Mathlib

namespace PEqualNP.Outside.L_lib_751_aux

theorem row (f g : Bool → Bool) (dir : Bool)
    (hdir : ∀ (a b : Bool), (a = true → b = true) →
      (if dir then (f b = true → f a = true) else (f a = true → f b = true)))
    (hdirg : ∀ (a b : Bool), (a = true → b = true) →
      ((g a = true → f a = true) ∧ (g b = true → f b = true) ∨
       (f a = true → g a = true) ∧ (f b = true → g b = true)) →
      (if dir then (g b = true → g a = true) else (g a = true → g b = true)))
    {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (hdef : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hS : ∀ i ∈ S, ∃ k ∉ S, (∀ j ∈ J, X i j = X k j) ∧
      ((∀ j ∈ J, A i j = true → A k j = true) ∨ (∀ j ∈ J, A k j = true → A i j = true)))
    (j l : Fin m) (hj : j ∈ J) (hl : l ∈ J) (i : Fin n) (hX : X i j = true → X i l = true) :
    (if dir then (A i l = true → A i j = true) else (A i j = true → A i l = true)) := by
  rw [hdef i j hj, hdef i l hl]
  by_cases hi : i ∈ S
  · rw [if_pos hi, if_pos hi]
    obtain ⟨k, hk, hcopy, hcmp⟩ := hS i hi
    apply hdirg _ _ hX
    rcases hcmp with h | h
    · left
      have h1 := h j hj
      have h2 := h l hl
      rw [hdef i j hj, hdef k j hj, if_pos hi, if_neg hk, ← hcopy j hj] at h1
      rw [hdef i l hl, hdef k l hl, if_pos hi, if_neg hk, ← hcopy l hl] at h2
      exact ⟨h1, h2⟩
    · right
      have h1 := h j hj
      have h2 := h l hl
      rw [hdef i j hj, hdef k j hj, if_pos hi, if_neg hk, ← hcopy j hj] at h1
      rw [hdef i l hl, hdef k l hl, if_pos hi, if_neg hk, ← hcopy l hl] at h2
      exact ⟨h1, h2⟩
  · rw [if_neg hi, if_neg hi]
    exact hdir _ _ hX

theorem main {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (f g : Bool → Bool)
    (hdef : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hS : ∀ i ∈ S, ∃ k ∉ S, (∀ j ∈ J, X i j = X k j) ∧
      ((∀ j ∈ J, A i j = true → A k j = true) ∨ (∀ j ∈ J, A k j = true → A i j = true))) :
    (∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → (∀ i, A i j = true → A i l = true)) ∨
    (∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → (∀ i, A i l = true → A i j = true)) := by
  have key : ∀ dir : Bool,
      (∀ (a b : Bool), (a = true → b = true) →
        (if dir then (f b = true → f a = true) else (f a = true → f b = true))) →
      (∀ (a b : Bool), (a = true → b = true) →
        ((g a = true → f a = true) ∧ (g b = true → f b = true) ∨
         (f a = true → g a = true) ∧ (f b = true → g b = true)) →
        (if dir then (g b = true → g a = true) else (g a = true → g b = true))) →
      ∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → ∀ i,
        (if dir then (A i l = true → A i j = true) else (A i j = true → A i l = true)) :=
    fun dir h1 h2 j hj l hl hX i => row f g dir h1 h2 X A S J hdef hS j l hj hl i (hX i)
  have hf : ∀ b, f b = (if b then f true else f false) := by intro b; cases b <;> rfl
  have hg : ∀ b, g b = (if b then g true else g false) := by intro b; cases b <;> rfl
  rw [funext hf, funext hg] at key
  generalize f true = f1 at key
  generalize f false = f0 at key
  generalize g true = g1 at key
  generalize g false = g0 at key
  cases f1 <;> cases f0 <;> cases g1 <;> cases g0 <;>
  first
  | exact Or.inl (fun j hj l hl hX i => key false (by decide) (by decide) j hj l hl hX i)
  | exact Or.inr (fun j hj l hl hX i => key true (by decide) (by decide) j hj l hl hX i)

end PEqualNP.Outside.L_lib_751_aux

theorem PEqualNP.Outside.L_lib_751 : ∀ (n m : Nat) (X A : Fin n → Fin m → Bool)
    (S : Finset (Fin n)) (J : Finset (Fin m)) (f g : Bool → Bool),
  let rowLE := fun i k : Fin n => ∀ j ∈ J, A i j = true → A k j = true
  let colLE := fun (T : Fin n → Fin m → Bool) (j l : Fin m) =>
    ∀ i, T i j = true → T i l = true
  (∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j))) →
  (∀ i ∈ S, ∃ k ∉ S, (∀ j ∈ J, X i j = X k j) ∧ (rowLE i k ∨ rowLE k i)) →
  (∀ j ∈ J, ∀ l ∈ J, colLE X j l → colLE A j l) ∨
  (∀ j ∈ J, ∀ l ∈ J, colLE X j l → colLE A l j) := by
  intro n m X A S J f g rowLE colLE hdef hS
  exact PEqualNP.Outside.L_lib_751_aux.main X A S J f g hdef hS
