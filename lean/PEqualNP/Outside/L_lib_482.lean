import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_482 : ∀ (n m : ℕ) (L : Fin m → Fin 3 → Fin n × Bool),
  let ev := fun (x : Fin n → Bool) (i : Fin m) (k : Fin 3) => x (L i k).1 == (L i k).2
  let nae := fun (a b c : Bool) => ¬ (a = b ∧ b = c)
  (∃ x : Fin n → Bool, ∀ i, ∃ k, ev x i k = true) ↔
    ∃ (x : Fin n → Bool) (s : Fin m → Bool) (z : Bool), ∀ i,
      nae (ev x i 0) (ev x i 1) (s i) ∧ nae (!(s i)) (ev x i 2) z := by
  intro n m L ev nae
  have flip : ∀ (x : Fin n → Bool) i k, ev (fun v => !x v) i k = !(ev x i k) := by
    intro x i k
    simp only [ev]
    cases hx : x (L i k).1 <;> cases hs : (L i k).2 <;> simp
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, fun i => if ev x i 2 = true then !(ev x i 0) else false, false, fun i => ?_⟩
    obtain ⟨k, hk⟩ := hx i
    have h0 := ev x i 0
    simp only [nae]
    by_cases hc : ev x i 2 = true
    · simp only [hc, ite_true]
      cases ha : ev x i 0 <;> cases hb : ev x i 1 <;> simp
    · have hc' : ev x i 2 = false := by simpa using hc
      simp only [hc]
      have : ev x i 0 = true ∨ ev x i 1 = true := by
        fin_cases k <;> simp_all
      cases ha : ev x i 0 <;> cases hb : ev x i 1 <;> simp_all
  · rintro ⟨x, s, z, h⟩
    cases z
    · refine ⟨x, fun i => ?_⟩
      obtain ⟨h1, h2⟩ := h i
      by_contra hno
      push Not at hno
      have e0 := hno 0; have e1 := hno 1; have e2 := hno 2
      simp only [nae] at h1 h2
      cases hs : s i <;> simp_all
    · refine ⟨fun v => !x v, fun i => ?_⟩
      obtain ⟨h1, h2⟩ := h i
      by_contra hno
      push Not at hno
      have e0 := hno 0; have e1 := hno 1; have e2 := hno 2
      rw [flip] at e0 e1 e2
      simp only [nae] at h1 h2
      cases hs : s i <;> simp_all
