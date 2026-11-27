import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_767_aux

theorem sub_one_of_ne : ∀ a b : ZMod 2, a ≠ b → a - b = 1 := by decide

theorem eq_of_add_zero : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

end PEqualNP.Outside.L_lib_767_aux

open PEqualNP.Outside.L_lib_767_aux in
theorem PEqualNP.Outside.L_lib_767 : (∀ (r n : ℕ) (h : Fin n → Fin r → ZMod 2), Function.Injective h → (∀ j, h j ≠ 0) →
  ∀ x y : Fin n → ZMod 2, x ≠ y →
    (Finset.univ.filter (fun j => x j ≠ y j)).card ≤ 2 →
    (∑ j, x j • h j) ≠ (∑ j, y j • h j)) := by
  intro r n h hinj hnz x y hxy hcard heq
  have hdiff : ∑ j, (x j - y j) • h j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  have hsum : ∑ j ∈ Finset.univ.filter (fun j => x j ≠ y j), h j = 0 := by
    rw [← hdiff, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => x j ≠ y j)]
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => ¬ x j ≠ y j), (x j - y j) • h j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      simp [hj]
    rw [h1, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rw [sub_one_of_ne _ _ hj, one_smul]
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hxy
  have hpos : 0 < (Finset.univ.filter (fun j => x j ≠ y j)).card :=
    Finset.card_pos.mpr ⟨j0, by simp [hj0]⟩
  rcases (by omega : (Finset.univ.filter (fun j => x j ≠ y j)).card = 1 ∨
      (Finset.univ.filter (fun j => x j ≠ y j)).card = 2) with h1 | h2
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
    rw [ha, Finset.sum_singleton] at hsum
    exact hnz a hsum
  · obtain ⟨a, b, hab, hS⟩ := Finset.card_eq_two.mp h2
    rw [hS, Finset.sum_pair hab] at hsum
    apply hab
    apply hinj
    funext k
    exact eq_of_add_zero _ _ (by simpa using congrFun hsum k)
