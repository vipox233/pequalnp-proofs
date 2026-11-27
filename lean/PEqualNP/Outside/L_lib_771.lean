import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_771

open Polynomial

theorem sv_bound : ∀ (k : ℕ) (P : Polynomial ℝ), P ≠ 0 → P.support.card = k + 1 →
    P.signVariations + 1 ≤ P.support.card := by
  intro k
  induction k with
  | zero =>
    intro P hP hk
    have h0 : P.eraseLead = 0 := by
      have hc : P.eraseLead.support.card = 0 := by rw [card_support_eraseLead, hk]
      rwa [Finset.card_eq_zero, support_eq_empty] at hc
    have hm := eraseLead_add_monomial_natDegree_leadingCoeff P
    rw [h0, zero_add] at hm
    rw [← hm, signVariations_monomial, hm, hk]
  | succ k ih =>
    intro P hP hk
    have hE : P.eraseLead.support.card = k + 1 := by
      rw [card_support_eraseLead, hk]; rfl
    have hE0 : P.eraseLead ≠ 0 := by
      intro h; rw [h] at hE; simp at hE
    have h1 := signVariations_le_eraseLead_succ P
    have h2 := ih P.eraseLead hE0 hE
    omega

end PEqualNP.Outside.L_lib_771

open PEqualNP.Outside.L_lib_771 in
theorem PEqualNP.Outside.L_lib_771 : ∀ (p : Polynomial ℝ), p ≠ 0 →
  (p.roots.toFinset.filter (fun x => 0 < x)).card + 1 ≤ p.support.card := by
  intro p hp
  have hc : 0 < p.support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hp)
  have hs := sv_bound (p.support.card - 1) p hp (by omega)
  have hr := Polynomial.roots_countP_pos_le_signVariations p
  have ht : (p.roots.toFinset.filter (fun x => 0 < x)).card ≤ p.roots.countP (fun x => 0 < x) := by
    rw [← Multiset.toFinset_filter, Multiset.countP_eq_card_filter]
    exact Multiset.toFinset_card_le _
  omega
