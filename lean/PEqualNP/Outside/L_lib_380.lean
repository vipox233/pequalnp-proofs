import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.ZMod.Basic
import PEqualNP.Defs

-- L-lib-380: in characteristic two p+d and q+e are collisions too, so d lies in H and e in K.
-- A guess (a,b) forces a = b+1 on all d-collisions and a = b on all e-collisions, so a kills H and K
-- while a(q-p) = 1. Conversely Mathlib's dual separation (exists_dual_map_eq_bot_of_notMem) gives f
-- vanishing on H+K with f(q-p) nonzero; take b = f q.

theorem PEqualNP.Outside.L_lib_380 :
    ∀ (n : ℕ) (A : Type) (Y : (Fin n → ZMod 2) → A)
        (d e p q : Fin n → ZMod 2),
      d ≠ 0 → e ≠ 0 → Y p = Y (p + d) → Y q = Y (q + e) →
      let H := Submodule.span (ZMod 2)
        {v : Fin n → ZMod 2 | ∃ x, Y x = Y (x + d) ∧ v = x - p}
      let K := Submodule.span (ZMod 2)
        {v : Fin n → ZMod 2 | ∃ x, Y x = Y (x + e) ∧ v = x - q}
      (∃ (a : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
        a ≠ 0 ∧ a d = 0 ∧ a e = 0 ∧
        (∀ x, a x = b → Y x ≠ Y (x + d)) ∧
        (∀ x, a x = b + 1 → Y x ≠ Y (x + e))) ↔
      q - p ∉ H ⊔ K := by
  intro n A Y d e p q _hd _he hp hq H K
  have two : ∀ t : ZMod 2, t + t = 0 := by decide
  have hH : ∀ x, Y x = Y (x + d) → x - p ∈ H := fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  have hK : ∀ x, Y x = Y (x + e) → x - q ∈ K := fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  have hdH : d ∈ H := by
    have hdd : d + d = 0 := funext fun i => two (d i)
    have h := hH (p + d) (by rw [add_assoc, hdd, add_zero]; exact hp.symm)
    rwa [add_sub_cancel_left] at h
  have heK : e ∈ K := by
    have hee : e + e = 0 := funext fun i => two (e i)
    have h := hK (q + e) (by rw [add_assoc, hee, add_zero]; exact hq.symm)
    rwa [add_sub_cancel_left] at h
  constructor
  · rintro ⟨a, b, -, -, -, h1, h2⟩ hmem
    have ad : ∀ x, Y x = Y (x + d) → a x = b + 1 := by
      intro x hx
      have key : ∀ s t : ZMod 2, s ≠ t → s = t + 1 := by decide
      exact key _ _ (fun hb => h1 x hb hx)
    have ae : ∀ x, Y x = Y (x + e) → a x = b := by
      intro x hx
      have key : ∀ s t : ZMod 2, s ≠ t + 1 → s = t := by decide
      exact key _ _ (fun hb => h2 x hb hx)
    have hHk : H ≤ LinearMap.ker a := by
      refine Submodule.span_le.2 ?_
      rintro v ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, ad x hx, ad p hp, sub_self]
    have hKk : K ≤ LinearMap.ker a := by
      refine Submodule.span_le.2 ?_
      rintro v ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, ae x hx, ae q hq, sub_self]
    have h0 : a (q - p) = 0 := LinearMap.mem_ker.1 (sup_le hHk hKk hmem)
    rw [map_sub, ae q hq, ad p hp] at h0
    have key : ∀ t : ZMod 2, t - (t + 1) ≠ 0 := by decide
    exact key b h0
  · intro hnot
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hz : ∀ v ∈ H ⊔ K, f v = 0 := by
      intro v hv
      have h : f v ∈ (H ⊔ K).map f := Submodule.mem_map_of_mem hv
      rw [hmap] at h
      exact (Submodule.mem_bot _).1 h
    have hqp : f q ≠ f p := by
      intro h; apply hf; rw [map_sub, h, sub_self]
    refine ⟨f, f q, ?_, hz d (Submodule.mem_sup_left hdH), hz e (Submodule.mem_sup_right heK),
      ?_, ?_⟩
    · intro h; apply hf; rw [h]; rfl
    · intro x hx hcol
      have h := hz _ (Submodule.mem_sup_left (hH x hcol))
      rw [map_sub, sub_eq_zero] at h
      exact hqp (hx.symm.trans h)
    · intro x hx hcol
      have h := hz _ (Submodule.mem_sup_right (hK x hcol))
      rw [map_sub, sub_eq_zero, hx] at h
      have key : ∀ t : ZMod 2, t + 1 ≠ t := by decide
      exact key _ h
