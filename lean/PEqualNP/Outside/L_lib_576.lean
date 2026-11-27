import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_576_aux

open scoped Classical

abbrev Edge (n : ℕ) := Finset (Fin n)
abbrev Matching (n : ℕ) := Finset (Edge n)

def Good {n : ℕ} (m : Matching n) : Prop :=
  m.card = 3 ∧ (∀ e ∈ m, e.card = 2) ∧ ∀ e ∈ m, ∀ f ∈ m, e ≠ f → Disjoint e f

def Rainbow {n : ℕ} (k : ℕ) (ms : Fin k → Matching n) : Prop :=
  ∃ (c : Fin 3 → Fin k) (pick : Fin 3 → Edge n), Function.Injective c ∧
    (∀ j, pick j ∈ ms (c j)) ∧ (∀ i j, i ≠ j → Disjoint (pick i) (pick j))

lemma fin5_other_one (c1 c2 : Fin 5) (h10 : c1 ≠ 0) (h11 : c1 ≠ 1) (h20 : c2 ≠ 0) (h21 : c2 ≠ 1)
    (h12 : c1 ≠ c2) : ∃ c3 : Fin 5, c3 ≠ 0 ∧ c3 ≠ 1 ∧ c3 ≠ c1 ∧ c3 ≠ c2 := by
  fin_cases c1 <;> fin_cases c2 <;> simp_all
  · exact ⟨4, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨4, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨2, by decide⟩

lemma fin5_other_two (c : Fin 5) (h0 : c ≠ 0) (h1 : c ≠ 1) :
    ∃ c1 c2 : Fin 5, c1 ≠ 0 ∧ c1 ≠ 1 ∧ c2 ≠ 0 ∧ c2 ≠ 1 ∧ c1 ≠ c ∧ c2 ≠ c ∧ c1 ≠ c2 := by
  fin_cases c
  · exact absurd rfl h0
  · exact absurd rfl h1
  · exact ⟨3, 4, by decide⟩
  · exact ⟨2, 4, by decide⟩
  · exact ⟨2, 3, by decide⟩

lemma fin5_other_three (i₀ i₁ : Fin 5) (h01 : i₀ ≠ i₁) :
    ∃ c1 c2 c3 : Fin 5,
      c1 ≠ i₀ ∧ c1 ≠ i₁ ∧ c2 ≠ i₀ ∧ c2 ≠ i₁ ∧ c3 ≠ i₀ ∧ c3 ≠ i₁ ∧
      c1 ≠ c2 ∧ c1 ≠ c3 ∧ c2 ≠ c3 := by
  fin_cases i₀ <;> fin_cases i₁
  · exact absurd rfl h01
  · exact ⟨2, 3, 4, by decide⟩
  · exact ⟨1, 3, 4, by decide⟩
  · exact ⟨1, 2, 4, by decide⟩
  · exact ⟨1, 2, 3, by decide⟩
  · exact ⟨2, 3, 4, by decide⟩
  · exact absurd rfl h01
  · exact ⟨0, 3, 4, by decide⟩
  · exact ⟨0, 2, 4, by decide⟩
  · exact ⟨0, 2, 3, by decide⟩
  · exact ⟨1, 3, 4, by decide⟩
  · exact ⟨0, 3, 4, by decide⟩
  · exact absurd rfl h01
  · exact ⟨0, 1, 4, by decide⟩
  · exact ⟨0, 1, 3, by decide⟩
  · exact ⟨1, 2, 4, by decide⟩
  · exact ⟨0, 2, 4, by decide⟩
  · exact ⟨0, 1, 4, by decide⟩
  · exact absurd rfl h01
  · exact ⟨0, 1, 2, by decide⟩
  · exact ⟨1, 2, 3, by decide⟩
  · exact ⟨0, 2, 3, by decide⟩
  · exact ⟨0, 1, 3, by decide⟩
  · exact ⟨0, 1, 2, by decide⟩
  · exact absurd rfl h01

lemma fin5_univ_distinct {i₀ i₁ i₂ i₃ i₄ : Fin 5}
    (huniv : ({i₀, i₁, i₂, i₃, i₄} : Finset (Fin 5)) = Finset.univ) :
    i₀ ≠ i₁ ∧ i₀ ≠ i₂ ∧ i₀ ≠ i₃ ∧ i₀ ≠ i₄ ∧ i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₁ ≠ i₄ ∧
    i₂ ≠ i₃ ∧ i₂ ≠ i₄ ∧ i₃ ≠ i₄ := by
  have hc : ({i₀, i₁, i₂, i₃, i₄} : Finset (Fin 5)).card = 5 := by rw [huniv]; simp
  have hcard_le4 : ∀ a b c d : Fin 5, ({a, b, c, d} : Finset (Fin 5)).card ≤ 4 := by
    intro a b c d
    exact le_trans (Finset.card_insert_le _ _)
      (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _)
        (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (by simp)))))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro rfl; have : ({i₀, i₀, i₂, i₃, i₄} : Finset (Fin 5)) = {i₀, i₂, i₃, i₄} := by ext z; simp
    rw [this] at hc; have := hcard_le4 i₀ i₂ i₃ i₄; omega
  · rintro rfl; have : ({i₀, i₁, i₀, i₃, i₄} : Finset (Fin 5)) = {i₀, i₁, i₃, i₄} := by ext z; simp; tauto
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₃ i₄; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₀, i₄} : Finset (Fin 5)) = {i₀, i₁, i₂, i₄} := by ext z; simp; tauto
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₄; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₃, i₀} : Finset (Fin 5)) = {i₀, i₁, i₂, i₃} := by ext z; simp; tauto
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₃; omega
  · rintro rfl; have : ({i₀, i₁, i₁, i₃, i₄} : Finset (Fin 5)) = {i₀, i₁, i₃, i₄} := by ext z; simp
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₃ i₄; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₁, i₄} : Finset (Fin 5)) = {i₀, i₁, i₂, i₄} := by ext z; simp; tauto
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₄; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₃, i₁} : Finset (Fin 5)) = {i₀, i₁, i₂, i₃} := by ext z; simp; tauto
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₃; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₂, i₄} : Finset (Fin 5)) = {i₀, i₁, i₂, i₄} := by ext z; simp
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₄; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₃, i₂} : Finset (Fin 5)) = {i₀, i₁, i₂, i₃} := by ext z; simp; tauto
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₃; omega
  · rintro rfl; have : ({i₀, i₁, i₂, i₃, i₃} : Finset (Fin 5)) = {i₀, i₁, i₂, i₃} := by ext z; simp
    rw [this] at hc; have := hcard_le4 i₀ i₁ i₂ i₃; omega

lemma of_ho_aux {a b c : Nat} (ha : a = 2) (h : ¬ (a = 2 ∧ 0 < b ∧ 0 < c)) : b = 0 ∨ c = 0 := by
  by_cases hb : b = 0; · exact Or.inl hb
  · by_cases hc : c = 0; · exact Or.inr hc
    · exact absurd ⟨ha, Nat.pos_of_ne_zero hb, Nat.pos_of_ne_zero hc⟩ h

lemma of_hs_aux {a b c : Nat} (h : ¬ (0 < a ∧ 0 < b ∧ 0 < c)) : a = 0 ∨ b = 0 ∨ c = 0 := by
  by_cases ha : a = 0; · exact Or.inl ha
  · by_cases hb : b = 0; · exact Or.inr (Or.inl hb)
    · by_cases hc : c = 0; · exact Or.inr (Or.inr hc)
      · exact absurd ⟨Nat.pos_of_ne_zero ha, Nat.pos_of_ne_zero hb, Nat.pos_of_ne_zero hc⟩ h

lemma sum2_aux {x y : Nat} (hx : x ≤ 2) (hy : y ≤ 2) (hs : x + y = 3) :
    (x = 2 ∧ y = 1) ∨ (x = 1 ∧ y = 2) := by
  omega

lemma sum3_ne111_aux {x y z : Nat} (hx : x ≤ 2) (hy : y ≤ 2) (hz : z ≤ 2)
    (hs : x + y + z = 3) (h0 : x = 0 ∨ y = 0 ∨ z = 0) :
    (x = 2 ∧ y = 1 ∧ z = 0) ∨ (x = 2 ∧ y = 0 ∧ z = 1) ∨
    (x = 1 ∧ y = 2 ∧ z = 0) ∨ (x = 0 ∧ y = 2 ∧ z = 1) ∨
    (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 2) := by
  rcases h0 with rfl | rfl | rfl <;> omega

lemma sum3_le1_aux {x y z : Nat} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 1) (hs : x + y + z = 3) :
    x = 1 ∧ y = 1 ∧ z = 1 := by
  omega

lemma sum3_le2_aux {x y z : Nat} (hx : x ≤ 1) (hy : y ≤ 2) (hz : z ≤ 2)
    (hs : x + y + z = 3) (h0 : x = 0 ∨ y = 0 ∨ z = 0) :
    (x = 1 ∧ y = 2 ∧ z = 0) ∨ (x = 0 ∧ y = 2 ∧ z = 1) ∨
    (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 2) := by
  rcases h0 with rfl | rfl | rfl <;> omega

lemma sum3_le112_aux {x y z : Nat} (hx : x ≤ 1) (hy : y ≤ 1) (hz : z ≤ 2)
    (hs : x + y + z = 3) (h0 : x = 0 ∨ y = 0 ∨ z = 0) :
    (x = 1 ∧ y = 0 ∧ z = 2) ∨ (x = 0 ∧ y = 1 ∧ z = 2) := by
  rcases h0 with rfl | rfl | rfl <;> omega

lemma counts_6_classify (c0 c1 c2 c3 c4 c5 : Fin 3)
    (hsum : c0.val + c1.val + c2.val + c3.val + c4.val + c5.val = 5)
    (hs0 : ¬ (0 < c0.val ∧ 0 < c1.val ∧ 0 < c2.val))
    (hs1 : ¬ (0 < c0.val ∧ 0 < c3.val ∧ 0 < c4.val))
    (hs2 : ¬ (0 < c1.val ∧ 0 < c3.val ∧ 0 < c5.val))
    (hs3 : ¬ (0 < c2.val ∧ 0 < c4.val ∧ 0 < c5.val))
    (ho0a : ¬ (c0.val = 2 ∧ 0 < c3.val ∧ 0 < c2.val))
    (ho0b : ¬ (c0.val = 2 ∧ 0 < c4.val ∧ 0 < c1.val))
    (ho1a : ¬ (c1.val = 2 ∧ 0 < c3.val ∧ 0 < c2.val))
    (ho1b : ¬ (c1.val = 2 ∧ 0 < c5.val ∧ 0 < c0.val))
    (ho2a : ¬ (c2.val = 2 ∧ 0 < c4.val ∧ 0 < c1.val))
    (ho2b : ¬ (c2.val = 2 ∧ 0 < c5.val ∧ 0 < c0.val))
    (ho3a : ¬ (c3.val = 2 ∧ 0 < c1.val ∧ 0 < c4.val))
    (ho3b : ¬ (c3.val = 2 ∧ 0 < c5.val ∧ 0 < c0.val))
    (ho4a : ¬ (c4.val = 2 ∧ 0 < c2.val ∧ 0 < c3.val))
    (ho4b : ¬ (c4.val = 2 ∧ 0 < c5.val ∧ 0 < c0.val))
    (ho5a : ¬ (c5.val = 2 ∧ 0 < c2.val ∧ 0 < c3.val))
    (ho5b : ¬ (c5.val = 2 ∧ 0 < c4.val ∧ 0 < c1.val)) :
    (c0.val = 2 ∧ c5.val = 2 ∧ c3.val = 1) ∨
    (c0.val = 2 ∧ c5.val = 2 ∧ c4.val = 1) ∨
    (c0.val = 2 ∧ c5.val = 2 ∧ c1.val = 1) ∨
    (c0.val = 2 ∧ c5.val = 2 ∧ c2.val = 1) ∨
    (c1.val = 2 ∧ c4.val = 2 ∧ c3.val = 1) ∨
    (c1.val = 2 ∧ c4.val = 2 ∧ c5.val = 1) ∨
    (c1.val = 2 ∧ c4.val = 2 ∧ c0.val = 1) ∨
    (c1.val = 2 ∧ c4.val = 2 ∧ c2.val = 1) ∨
    (c2.val = 2 ∧ c3.val = 2 ∧ c4.val = 1) ∨
    (c2.val = 2 ∧ c3.val = 2 ∧ c5.val = 1) ∨
    (c2.val = 2 ∧ c3.val = 2 ∧ c0.val = 1) ∨
    (c2.val = 2 ∧ c3.val = 2 ∧ c1.val = 1) ∨
    (c0.val = 2 ∧ c3.val = 2 ∧ c1.val = 1) ∨
    (c0.val = 2 ∧ c1.val = 2 ∧ c3.val = 1) ∨
    (c1.val = 2 ∧ c3.val = 2 ∧ c0.val = 1) ∨
    (c0.val = 2 ∧ c4.val = 2 ∧ c2.val = 1) ∨
    (c0.val = 2 ∧ c2.val = 2 ∧ c4.val = 1) ∨
    (c2.val = 2 ∧ c4.val = 2 ∧ c0.val = 1) ∨
    (c1.val = 2 ∧ c5.val = 2 ∧ c2.val = 1) ∨
    (c1.val = 2 ∧ c2.val = 2 ∧ c5.val = 1) ∨
    (c2.val = 2 ∧ c5.val = 2 ∧ c1.val = 1) ∨
    (c3.val = 2 ∧ c5.val = 2 ∧ c4.val = 1) ∨
    (c3.val = 2 ∧ c4.val = 2 ∧ c5.val = 1) ∨
    (c4.val = 2 ∧ c5.val = 2 ∧ c3.val = 1) := by
  have hb0 : c0.val ≤ 2 := Nat.le_of_lt_succ c0.isLt
  have hb1 : c1.val ≤ 2 := Nat.le_of_lt_succ c1.isLt
  have hb2 : c2.val ≤ 2 := Nat.le_of_lt_succ c2.isLt
  have hb3 : c3.val ≤ 2 := Nat.le_of_lt_succ c3.isLt
  have hb4 : c4.val ≤ 2 := Nat.le_of_lt_succ c4.isLt
  have hb5 : c5.val ≤ 2 := Nat.le_of_lt_succ c5.isLt
  by_cases h0 : c0.val = 2
  · rcases of_ho_aux h0 ho0a with h3z | h2z <;> rcases of_ho_aux h0 ho0b with h4z | h1z
    · have h0' : c1.val = 0 ∨ c2.val = 0 := match of_hs_aux hs0 with | Or.inl h => absurd (h0.symm.trans h) (by decide) | Or.inr h => h
      rcases h0' with h1z | h2z
      · rcases sum2_aux hb2 hb5 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h2, h5⟩ | ⟨h2, h5⟩
        · exact absurd ⟨h2, by rw [h5]; decide, by rw [h0]; decide⟩ ho2b
        · simp only [h0, h5, h2, true_and, and_true, true_or, or_true]
      · rcases sum2_aux hb1 hb5 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h1, h5⟩ | ⟨h1, h5⟩
        · exact absurd ⟨h1, by rw [h5]; decide, by rw [h0]; decide⟩ ho1b
        · simp only [h0, h5, h1, true_and, and_true, true_or, or_true]
    · have hs : c2.val + c4.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
      rcases sum3_ne111_aux hb2 hb4 hb5 hs (of_hs_aux hs3) with ⟨h2, h4, _⟩ | ⟨h2, _, h5⟩ | ⟨h2, h4, _⟩ | ⟨_, h4, h5⟩ | ⟨h2, _, h5⟩ | ⟨_, h4, h5⟩
      · simp only [h0, h2, h4, true_and, and_true, true_or, or_true]
      · exact absurd ⟨h2, by rw [h5]; decide, by rw [h0]; decide⟩ ho2b
      · simp only [h0, h4, h2, true_and, and_true, true_or, or_true]
      · exact absurd ⟨h4, by rw [h5]; decide, by rw [h0]; decide⟩ ho4b
      · simp only [h0, h5, h2, true_and, and_true, true_or, or_true]
      · simp only [h0, h5, h4, true_and, and_true, true_or, or_true]
    · have hs : c1.val + c3.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
      rcases sum3_ne111_aux hb1 hb3 hb5 hs (of_hs_aux hs2) with ⟨h1, h3, _⟩ | ⟨h1, _, h5⟩ | ⟨h1, h3, _⟩ | ⟨_, h3, h5⟩ | ⟨h1, _, h5⟩ | ⟨_, h3, h5⟩
      · simp only [h0, h1, h3, true_and, and_true, true_or, or_true]
      · exact absurd ⟨h1, by rw [h5]; decide, by rw [h0]; decide⟩ ho1b
      · simp only [h0, h3, h1, true_and, and_true, true_or, or_true]
      · exact absurd ⟨h3, by rw [h5]; decide, by rw [h0]; decide⟩ ho3b
      · simp only [h0, h5, h1, true_and, and_true, true_or, or_true]
      · simp only [h0, h5, h3, true_and, and_true, true_or, or_true]
    · have h0' : c3.val = 0 ∨ c4.val = 0 := match of_hs_aux hs1 with | Or.inl h => absurd (h0.symm.trans h) (by decide) | Or.inr h => h
      rcases h0' with h3z | h4z
      · rcases sum2_aux hb4 hb5 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h4, h5⟩ | ⟨h4, h5⟩
        · exact absurd ⟨h4, by rw [h5]; decide, by rw [h0]; decide⟩ ho4b
        · simp only [h0, h5, h4, true_and, and_true, true_or, or_true]
      · rcases sum2_aux hb3 hb5 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h3, h5⟩ | ⟨h3, h5⟩
        · exact absurd ⟨h3, by rw [h5]; decide, by rw [h0]; decide⟩ ho3b
        · simp only [h0, h5, h3, true_and, and_true, true_or, or_true]
  · have hb0' : c0.val ≤ 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
    by_cases h1 : c1.val = 2
    · rcases of_ho_aux h1 ho1a with h3z | h2z <;> rcases of_ho_aux h1 ho1b with h5z | h0z
      · have h0' : c0.val = 0 ∨ c2.val = 0 := match of_hs_aux hs0 with | Or.inl h => Or.inl h | Or.inr (Or.inl h) => absurd (h1.symm.trans h) (by decide) | Or.inr (Or.inr h) => Or.inr h
        rcases h0' with h0z | h2z
        · rcases sum2_aux hb2 hb4 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h2, h4⟩ | ⟨h2, h4⟩
          · exact absurd ⟨h2, by rw [h4]; decide, by rw [h1]; decide⟩ ho2a
          · simp only [h1, h4, h2, true_and, and_true, true_or, or_true]
        · have : c0.val = 1 ∧ c4.val = 2 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
          simp only [h1, this.1, this.2, true_and, and_true, true_or, or_true]
      · have hs : c2.val + c4.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
        rcases sum3_ne111_aux hb2 hb4 hb5 hs (of_hs_aux hs3) with ⟨h2, h4, _⟩ | ⟨h2, _, h5⟩ | ⟨h2, h4, _⟩ | ⟨_, h4, h5⟩ | ⟨h2, _, h5⟩ | ⟨_, h4, h5⟩
        · exact absurd ⟨h2, by rw [h4]; decide, by rw [h1]; decide⟩ ho2a
        · simp only [h1, h2, h5, true_and, and_true, true_or, or_true]
        · simp only [h1, h4, h2, true_and, and_true, true_or, or_true]
        · simp only [h1, h4, h5, true_and, and_true, true_or, or_true]
        · simp only [h1, h5, h2, true_and, and_true, true_or, or_true]
        · exact absurd ⟨h5, by rw [h4]; decide, by rw [h1]; decide⟩ ho5b
      · have hs : c0.val + c3.val + c4.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
        rcases sum3_le2_aux hb0' hb3 hb4 hs (of_hs_aux hs1) with ⟨h0', h3, _⟩ | ⟨_, h3, h4⟩ | ⟨h0', _, h4⟩ | ⟨_, h3, h4⟩
        · simp only [h1, h3, h0', true_and, and_true, true_or, or_true]
        · exact absurd ⟨h3, by rw [h1]; decide, by rw [h4]; decide⟩ ho3a
        · simp only [h1, h4, h0', true_and, and_true, true_or, or_true]
        · simp only [h1, h4, h3, true_and, and_true, true_or, or_true]
      · have h0' : c3.val = 0 ∨ c5.val = 0 := match of_hs_aux hs2 with | Or.inl h => absurd (h1.symm.trans h) (by decide) | Or.inr h => h
        rcases h0' with h3z | h5z
        · rcases sum2_aux hb4 hb5 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h4, h5⟩ | ⟨h4, h5⟩
          · simp only [h1, h4, h5, true_and, and_true, true_or, or_true]
          · exact absurd ⟨h5, by rw [h4]; decide, by rw [h1]; decide⟩ ho5b
        · rcases sum2_aux hb3 hb4 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩
          · exact absurd ⟨h3, by rw [h1]; decide, by rw [h4]; decide⟩ ho3a
          · simp only [h1, h4, h3, true_and, and_true, true_or, or_true]
    · have hb1' : c1.val ≤ 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
      by_cases h2 : c2.val = 2
      · rcases of_ho_aux h2 ho2a with h4z | h1z <;> rcases of_ho_aux h2 ho2b with h5z | h0z
        · have hs : c0.val + c1.val + c3.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
          have h0' : c0.val = 0 ∨ c1.val = 0 ∨ c3.val = 0 := match of_hs_aux hs0 with | Or.inl h => Or.inl h | Or.inr (Or.inl h) => Or.inr (Or.inl h) | Or.inr (Or.inr h) => absurd (h2.symm.trans h) (by decide)
          rcases sum3_le112_aux hb0' hb1' hb3 hs h0' with ⟨h0', _, h3⟩ | ⟨_, h1', h3⟩
          · simp only [h2, h3, h0', true_and, and_true, true_or, or_true]
          · simp only [h2, h3, h1', true_and, and_true, true_or, or_true]
        · have hs : c1.val + c3.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
          rcases sum3_le2_aux hb1' hb3 hb5 hs (of_hs_aux hs2) with ⟨h1', h3, _⟩ | ⟨_, h3, h5⟩ | ⟨h1', _, h5⟩ | ⟨_, h3, h5⟩
          · simp only [h2, h3, h1', true_and, and_true, true_or, or_true]
          · simp only [h2, h3, h5, true_and, and_true, true_or, or_true]
          · simp only [h2, h5, h1', true_and, and_true, true_or, or_true]
          · exact absurd ⟨h5, by rw [h2]; decide, by rw [h3]; decide⟩ ho5a
        · have hs : c0.val + c3.val + c4.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
          rcases sum3_le2_aux hb0' hb3 hb4 hs (of_hs_aux hs1) with ⟨h0', h3, _⟩ | ⟨_, h3, h4⟩ | ⟨h0', _, h4⟩ | ⟨_, h3, h4⟩
          · simp only [h2, h3, h0', true_and, and_true, true_or, or_true]
          · simp only [h2, h3, h4, true_and, and_true, true_or, or_true]
          · simp only [h2, h4, h0', true_and, and_true, true_or, or_true]
          · exact absurd ⟨h4, by rw [h2]; decide, by rw [h3]; decide⟩ ho4a
        · have h0' : c4.val = 0 ∨ c5.val = 0 := match of_hs_aux hs3 with | Or.inl h => absurd (h2.symm.trans h) (by decide) | Or.inr h => h
          rcases h0' with h4z | h5z
          · rcases sum2_aux hb3 hb5 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h3, h5⟩ | ⟨h3, h5⟩
            · simp only [h2, h3, h5, true_and, and_true, true_or, or_true]
            · exact absurd ⟨h5, by rw [h2]; decide, by rw [h3]; decide⟩ ho5a
          · rcases sum2_aux hb3 hb4 (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩
            · simp only [h2, h3, h4, true_and, and_true, true_or, or_true]
            · exact absurd ⟨h4, by rw [h2]; decide, by rw [h3]; decide⟩ ho4a
      · have hb2' : c2.val ≤ 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
        by_cases h3 : c3.val = 2
        · rcases of_ho_aux h3 ho3a with h1z | h4z <;> rcases of_ho_aux h3 ho3b with h5z | h0z
          · have hs : c0.val + c2.val + c4.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
            have h0' : c0.val = 0 ∨ c2.val = 0 ∨ c4.val = 0 := match of_hs_aux hs1 with | Or.inl h => Or.inl h | Or.inr (Or.inl h) => absurd (h3.symm.trans h) (by decide) | Or.inr (Or.inr h) => Or.inr (Or.inr h)
            rcases sum3_le112_aux hb0' hb2' hb4 hs h0' with ⟨h0', _, h4⟩ | ⟨_, h2', h4⟩
            · exact absurd ⟨by rw [h0']; decide, by rw [h3]; decide, by rw [h4]; decide⟩ hs1
            · exact absurd ⟨h4, by rw [h2']; decide, by rw [h3]; decide⟩ ho4a
          · have hs : c2.val + c4.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
            rcases sum3_le2_aux hb2' hb4 hb5 hs (of_hs_aux hs3) with ⟨h2', h4, _⟩ | ⟨_, h4, h5⟩ | ⟨h2', _, h5⟩ | ⟨_, h4, h5⟩
            · exact absurd ⟨h4, by rw [h2']; decide, by rw [h3]; decide⟩ ho4a
            · simp only [h3, h4, h5, true_and, and_true, true_or, or_true]
            · exact absurd ⟨h5, by rw [h2']; decide, by rw [h3]; decide⟩ ho5a
            · simp only [h3, h5, h4, true_and, and_true, true_or, or_true]
          · have ⟨h0', h1', h2'⟩ := sum3_le1_aux hb0' hb1' hb2' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
            exact absurd ⟨by rw [h0']; decide, by rw [h1']; decide, by rw [h2']; decide⟩ hs0
          · have hs : c1.val + c2.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
            have h0' : c1.val = 0 ∨ c2.val = 0 ∨ c5.val = 0 := match of_hs_aux hs2 with | Or.inl h => Or.inl h | Or.inr (Or.inl h) => absurd (h3.symm.trans h) (by decide) | Or.inr (Or.inr h) => Or.inr (Or.inr h)
            rcases sum3_le112_aux hb1' hb2' hb5 hs h0' with ⟨h1', _, h5⟩ | ⟨_, h2', h5⟩
            · exact absurd ⟨by rw [h1']; decide, by rw [h3]; decide, by rw [h5]; decide⟩ hs2
            · exact absurd ⟨h5, by rw [h2']; decide, by rw [h3]; decide⟩ ho5a
        · have hb3' : c3.val ≤ 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
          by_cases h4 : c4.val = 2
          · rcases of_ho_aux h4 ho4a with h2z | h3z <;> rcases of_ho_aux h4 ho4b with h5z | h0z
            · have ⟨h0', _, h3'⟩ := sum3_le1_aux hb0' hb1' hb3' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
              exact absurd ⟨by rw [h0']; decide, by rw [h3']; decide, by rw [h4]; decide⟩ hs1
            · have hs : c1.val + c3.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
              rcases sum3_le112_aux hb1' hb3' hb5 hs (of_hs_aux hs2) with ⟨h1', _, h5⟩ | ⟨_, h3', h5⟩
              · exact absurd ⟨h5, by rw [h4]; decide, by rw [h1']; decide⟩ ho5b
              · simp only [h4, h5, h3', true_and, and_true, true_or, or_true]
            · have ⟨h0', h1', h2'⟩ := sum3_le1_aux hb0' hb1' hb2' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
              exact absurd ⟨by rw [h0']; decide, by rw [h1']; decide, by rw [h2']; decide⟩ hs0
            · have hs : c1.val + c2.val + c5.val = 3 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
              have h0' : c1.val = 0 ∨ c2.val = 0 ∨ c5.val = 0 := match of_hs_aux hs3 with | Or.inl h => Or.inr (Or.inl h) | Or.inr (Or.inl h) => absurd (h4.symm.trans h) (by decide) | Or.inr (Or.inr h) => Or.inr (Or.inr h)
              rcases sum3_le112_aux hb1' hb2' hb5 hs h0' with ⟨h1', _, h5⟩ | ⟨_, h2', h5⟩
              · exact absurd ⟨h5, by rw [h4]; decide, by rw [h1']; decide⟩ ho5b
              · exact absurd ⟨by rw [h2']; decide, by rw [h4]; decide, by rw [h5]; decide⟩ hs3
          · have hb4' : c4.val ≤ 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
            by_cases h5 : c5.val = 2
            · rcases of_ho_aux h5 ho5a with h2z | h3z <;> rcases of_ho_aux h5 ho5b with h4z | h1z
              · have ⟨_, h1', h3'⟩ := sum3_le1_aux hb0' hb1' hb3' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
                exact absurd ⟨by rw [h1']; decide, by rw [h3']; decide, by rw [h5]; decide⟩ hs2
              · have ⟨h0', h3', h4'⟩ := sum3_le1_aux hb0' hb3' hb4' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
                exact absurd ⟨by rw [h0']; decide, by rw [h3']; decide, by rw [h4']; decide⟩ hs1
              · have ⟨h0', h1', h2'⟩ := sum3_le1_aux hb0' hb1' hb2' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
                exact absurd ⟨by rw [h0']; decide, by rw [h1']; decide, by rw [h2']; decide⟩ hs0
              · have ⟨_, h2', h4'⟩ := sum3_le1_aux hb0' hb2' hb4' (by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega)
                exact absurd ⟨by rw [h2']; decide, by rw [h4']; decide, by rw [h5]; decide⟩ hs3
            · have hb5' : c5.val ≤ 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
              rcases of_hs_aux hs0 with h0z | h1z | h2z
              · have : c1.val = 1 ∧ c3.val = 1 ∧ c5.val = 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
                exact absurd ⟨by rw [this.1]; decide, by rw [this.2.1]; decide, by rw [this.2.2]; decide⟩ hs2
              · have : c0.val = 1 ∧ c3.val = 1 ∧ c4.val = 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
                exact absurd ⟨by rw [this.1]; decide, by rw [this.2.1]; decide, by rw [this.2.2]; decide⟩ hs1
              · have : c0.val = 1 ∧ c3.val = 1 ∧ c4.val = 1 := by clear hs0 hs1 hs2 hs3 ho0a ho0b ho1a ho1b ho2a ho2b ho3a ho3b ho4a ho4b ho5a ho5b; omega
                exact absurd ⟨by rw [this.1]; decide, by rw [this.2.1]; decide, by rw [this.2.2]; decide⟩ hs1

lemma rainbow_of_three {n k : ℕ} {ms : Fin k → Matching n}
    {c₀ c₁ c₂ : Fin k} {e₀ e₁ e₂ : Edge n}
    (hc01 : c₀ ≠ c₁) (hc02 : c₀ ≠ c₂) (hc12 : c₁ ≠ c₂)
    (he0 : e₀ ∈ ms c₀) (he1 : e₁ ∈ ms c₁) (he2 : e₂ ∈ ms c₂)
    (hd01 : Disjoint e₀ e₁) (hd02 : Disjoint e₀ e₂) (hd12 : Disjoint e₁ e₂) :
    Rainbow k ms := by
  refine ⟨![c₀, c₁, c₂], ![e₀, e₁, e₂], ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro j
    fin_cases j <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Disjoint.symm]

lemma rainbow_of_perm {n k : ℕ} {ms : Fin k → Matching n} (σ : Fin k ≃ Fin k)
    (h : Rainbow k (fun i => ms (σ i))) : Rainbow k ms := by
  rcases h with ⟨c, pick, hinj, hmem, hdisj⟩
  exact ⟨fun j => σ (c j), pick, σ.injective.comp hinj, hmem, hdisj⟩

lemma pair_disjoint_iff {n : ℕ} {a b c d : Fin n} :
    Disjoint ({a, b} : Edge n) {c, d} ↔ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  rw [Finset.disjoint_left]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    refine ⟨fun h1 => h (Or.inl rfl) (Or.inl h1), fun h1 => h (Or.inl rfl) (Or.inr h1),
      fun h1 => h (Or.inr rfl) (Or.inl h1), fun h1 => h (Or.inr rfl) (Or.inr h1)⟩
  · rintro ⟨h1, h2, h3, h4⟩ x (rfl | rfl) (hx | hx) <;> contradiction

lemma pair_comm {n : ℕ} (a b : Fin n) : ({a, b} : Edge n) = {b, a} := by
  ext x; simp [or_comm]

lemma good_eq_of_mem_mem {n : ℕ} {m : Matching n} (hm : Good m) {e f : Edge n}
    {v : Fin n} (he : e ∈ m) (hf : f ∈ m) (hve : v ∈ e) (hvf : v ∈ f) : e = f := by
  by_contra hne
  exact Finset.disjoint_left.mp (hm.2.2 e he f hf hne) hve hvf

lemma good_pair_disj_ne {n : ℕ} {m : Matching n} (hm : Good m) {a b c d : Fin n}
    (h1 : ({a, b} : Edge n) ∈ m) (h2 : ({c, d} : Edge n) ∈ m)
    (hac : a ≠ c) (had : a ≠ d) : b ≠ c ∧ b ≠ d := by
  have hne : ({a, b} : Edge n) ≠ {c, d} := by
    intro heq
    have ha : a ∈ ({c, d} : Edge n) := heq ▸ Finset.mem_insert_self a _
    rcases Finset.mem_insert.mp ha with rfl | h
    · exact hac rfl
    · exact had (Finset.mem_singleton.mp h)
  have hd := pair_disjoint_iff.mp (hm.2.2 _ h1 _ h2 hne)
  exact ⟨hd.2.2.1, hd.2.2.2⟩

lemma card_filter_not_disjoint_le {n : ℕ} {m : Matching n} (hm : Good m) (S : Finset (Fin n)) :
    (m.filter (fun e => ¬ Disjoint e S)).card ≤ S.card := by
  let A := m.filter (fun e => ¬ Disjoint e S)
  have hnpos : 0 < n := by
    by_contra h0
    have hn : n = 0 := by omega
    subst hn
    have hmc : m.card = 3 := hm.1
    have hne : m.Nonempty := Finset.card_pos.mp (by omega)
    rcases hne with ⟨e0, he0⟩
    have hc0 := hm.2.1 e0 he0
    have : e0 = ∅ := by ext x; exact Fin.elim0 x
    rw [this] at hc0; simp at hc0
  let f : Edge n → Fin n := fun e =>
    if h : ∃ v, v ∈ e ∧ v ∈ S then Classical.choose h else ⟨0, hnpos⟩
  have hmaps : Set.MapsTo f (A : Set (Edge n)) (S : Set (Fin n)) := by
    intro e he
    have heA : e ∈ m ∧ ¬ Disjoint e S := Finset.mem_filter.mp he
    have hex : ∃ v, v ∈ e ∧ v ∈ S := Finset.not_disjoint_iff.mp heA.2
    simp only [f, hex, ↓reduceDIte]
    exact (Classical.choose_spec hex).2
  have hinj : Set.InjOn f (A : Set (Edge n)) := by
    intro e₁ he₁ e₂ he₂ hfeq
    have h1 : e₁ ∈ m ∧ ¬ Disjoint e₁ S := Finset.mem_filter.mp he₁
    have h2 : e₂ ∈ m ∧ ¬ Disjoint e₂ S := Finset.mem_filter.mp he₂
    have hex1 : ∃ v, v ∈ e₁ ∧ v ∈ S := Finset.not_disjoint_iff.mp h1.2
    have hex2 : ∃ v, v ∈ e₂ ∧ v ∈ S := Finset.not_disjoint_iff.mp h2.2
    simp only [f, hex1, hex2, ↓reduceDIte] at hfeq
    have hv1 : Classical.choose hex1 ∈ e₁ := (Classical.choose_spec hex1).1
    have hv2 : Classical.choose hex1 ∈ e₂ := hfeq ▸ (Classical.choose_spec hex2).1
    exact good_eq_of_mem_mem hm h1.1 h2.1 hv1 hv2
  exact Finset.card_le_card_of_injOn f hmaps hinj

lemma exists_edge_disjoint_of_card_le_two {n : ℕ} {m : Matching n} (hm : Good m)
    {S : Finset (Fin n)} (hS : S.card ≤ 2) :
    ∃ e ∈ m, Disjoint e S := by
  have hle : (m.filter (fun e => ¬ Disjoint e S)).card ≤ 2 :=
    le_trans (card_filter_not_disjoint_le hm S) hS
  have htot : (m.filter (fun e => Disjoint e S)).card +
      (m.filter (fun e => ¬ Disjoint e S)).card = m.card :=
    Finset.card_filter_add_card_filter_not (s := m) (p := fun e => Disjoint e S)
  have hm3 : m.card = 3 := hm.1
  have hpos : 0 < (m.filter (fun e => Disjoint e S)).card := by omega
  rcases Finset.card_pos.mp hpos with ⟨e, he⟩
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

lemma bip_edge_split {n : ℕ} {s e : Finset (Fin n)} (he : e.card = 2) (hcap : (e ∩ s).card = 1) :
    ∃ a b : Fin n, a ∈ s ∧ b ∉ s ∧ e = {a, b} := by
  rcases Finset.card_eq_one.mp hcap with ⟨a, ha⟩
  have has : a ∈ e ∧ a ∈ s := Finset.mem_inter.mp (ha ▸ Finset.mem_singleton_self a)
  have hdiff : (e.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem has.1, he]
  rcases Finset.card_eq_one.mp hdiff with ⟨b, hb⟩
  have hbe : b ∈ e ∧ b ≠ a := by
    have := Finset.mem_erase.mp (hb ▸ Finset.mem_singleton_self b)
    exact ⟨this.2, this.1⟩
  have hbs : b ∉ s := by
    intro h
    have : b ∈ e ∩ s := Finset.mem_inter.mpr ⟨hbe.1, h⟩
    rw [ha, Finset.mem_singleton] at this
    exact hbe.2 this
  refine ⟨a, b, has.2, hbs, ?_⟩
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · right
      have : x ∈ e.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
      rwa [hb, Finset.mem_singleton] at this
  · rintro (rfl | rfl)
    · exact has.1
    · exact hbe.1

lemma rainbow5_bipartite {n : ℕ} (s : Finset (Fin n)) (b : Fin 5 → Matching n)
    (hgood : ∀ i, Good (b i)) (hbip : ∀ j, ∀ e ∈ b j, (e ∩ s).card = 1) :
    Rainbow 5 b := by
  by_contra hno
  have h0ne : (b 0).Nonempty := Finset.card_pos.mp (by rw [(hgood 0).1]; omega)
  rcases h0ne with ⟨e₀, he₀⟩
  rcases exists_edge_disjoint_of_card_le_two (hgood 1) (le_of_eq ((hgood 0).2.1 e₀ he₀)) with
    ⟨e₁, he₁, hdisj10⟩
  have hdisj01 : Disjoint e₀ e₁ := hdisj10.symm
  rcases bip_edge_split ((hgood 0).2.1 e₀ he₀) (hbip 0 e₀ he₀) with ⟨s₀, t₀, hs₀, ht₀, rfl⟩
  rcases bip_edge_split ((hgood 1).2.1 e₁ he₁) (hbip 1 e₁ he₁) with ⟨s₁, t₁, hs₁, ht₁, rfl⟩
  have hst_disj := pair_disjoint_iff.mp hdisj01
  have hs01 : s₀ ≠ s₁ := hst_disj.1
  have ht01 : t₀ ≠ t₁ := hst_disj.2.2.2
  have hhit : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 → ∀ a c : Fin n, a ∈ s → c ∉ s → ({a, c} : Edge n) ∈ b i →
      (a = s₀ ∨ a = s₁) ∨ (c = t₀ ∨ c = t₁) := by
    intro i hi0 hi1 a c has hcs hac
    by_contra hmiss
    push Not at hmiss
    rcases hmiss with ⟨⟨has0, has1⟩, ⟨hct0, hct1⟩⟩
    have hd0 : Disjoint ({s₀, t₀} : Edge n) {a, c} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm has0, fun h => hcs (h ▸ hs₀), fun h => ht₀ (h ▸ has), Ne.symm hct0⟩
    have hd1 : Disjoint ({s₁, t₁} : Edge n) {a, c} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm has1, fun h => hcs (h ▸ hs₁), fun h => ht₁ (h ▸ has), Ne.symm hct1⟩
    exact hno (rainbow_of_three (by decide) hi0.symm hi1.symm he₀ he₁ hac hdisj01 hd0 hd1)
  have hex_p : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 →
      ∃ a c : Fin n, a ∈ s ∧ c ∉ s ∧ a ≠ s₀ ∧ a ≠ s₁ ∧ (c = t₀ ∨ c = t₁) ∧ ({a, c} : Edge n) ∈ b i := by
    intro i hi0 hi1
    rcases exists_edge_disjoint_of_card_le_two (hgood i)
        (le_trans (Finset.card_insert_le s₀ {s₁}) (by simp)) with ⟨e, hei, hde⟩
    rcases bip_edge_split ((hgood i).2.1 e hei) (hbip i e hei) with ⟨a, c, has, hcs, rfl⟩
    have ha0 : a ≠ s₀ := fun h => Finset.disjoint_left.mp hde (Finset.mem_insert_self a _)
      (by rw [h]; exact Finset.mem_insert_self _ _)
    have ha1 : a ≠ s₁ := fun h => Finset.disjoint_left.mp hde (Finset.mem_insert_self a _)
      (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    rcases hhit i hi0 hi1 a c has hcs hei with (rfl | rfl) | hct
    · exact absurd rfl ha0
    · exact absurd rfl ha1
    · exact ⟨a, c, has, hcs, ha0, ha1, hct, hei⟩
  have hno_swap0 : ∀ i j : Fin 5, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j →
      ∀ c : Fin n, c ∉ s → c ≠ t₀ → c ≠ t₁ → ({s₀, c} : Edge n) ∈ b i →
      ∀ a : Fin n, a ∈ s → a ≠ s₀ → a ≠ s₁ → ({a, t₀} : Edge n) ∈ b j → False := by
    intro i j _ hi1 _ hj1 hij c hcs hct0 hct1 hbi a has has0 has1 hbj
    have hd1 : Disjoint ({s₁, t₁} : Edge n) {s₀, c} := by
      rw [pair_disjoint_iff]
      refine ⟨hs01.symm, fun h => hcs (h ▸ hs₁), fun h => ht₁ (h ▸ hs₀), Ne.symm hct1⟩
    have hd2 : Disjoint ({s₁, t₁} : Edge n) {a, t₀} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm has1, fun h => ht₀ (h ▸ hs₁), fun h => ht₁ (h ▸ has), ht01.symm⟩
    have hd3 : Disjoint ({s₀, c} : Edge n) {a, t₀} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm has0, fun h => ht₀ (h ▸ hs₀), fun h => hcs (h ▸ has), hct0⟩
    exact hno (rainbow_of_three hi1.symm hj1.symm hij he₁ hbi hbj hd1 hd2 hd3)
  have hno_swap1 : ∀ i j : Fin 5, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j →
      ∀ c : Fin n, c ∉ s → c ≠ t₀ → c ≠ t₁ → ({s₁, c} : Edge n) ∈ b i →
      ∀ a : Fin n, a ∈ s → a ≠ s₀ → a ≠ s₁ → ({a, t₁} : Edge n) ∈ b j → False := by
    intro i j hi0 _ hj0 _ hij c hcs hct0 hct1 hbi a has has0 has1 hbj
    have hd1 : Disjoint ({s₀, t₀} : Edge n) {s₁, c} := by
      rw [pair_disjoint_iff]
      refine ⟨hs01, fun h => hcs (h ▸ hs₀), fun h => ht₀ (h ▸ hs₁), Ne.symm hct0⟩
    have hd2 : Disjoint ({s₀, t₀} : Edge n) {a, t₁} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm has0, fun h => ht₁ (h ▸ hs₀), fun h => ht₀ (h ▸ has), ht01⟩
    have hd3 : Disjoint ({s₁, c} : Edge n) {a, t₁} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm has1, fun h => ht₁ (h ▸ hs₁), fun h => hcs (h ▸ has), hct1⟩
    exact hno (rainbow_of_three hi0.symm hj0.symm hij he₀ hbi hbj hd1 hd2 hd3)
  have hfinish : ∀ (sA sB tA tB : Fin n),
      sA ∈ s → sB ∈ s → tA ∉ s → tB ∉ s → sA ≠ sB → tA ≠ tB →
      (∀ i : Fin 5, i ≠ 0 → i ≠ 1 → ∀ a c : Fin n, a ∈ s → c ∉ s → ({a, c} : Edge n) ∈ b i →
        (a = sA ∨ a = sB) ∨ (c = tA ∨ c = tB)) →
      (∀ i j : Fin 5, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j →
        ∀ c : Fin n, c ∉ s → c ≠ tA → c ≠ tB → ({sA, c} : Edge n) ∈ b i →
        ∀ a : Fin n, a ∈ s → a ≠ sA → a ≠ sB → ({a, tA} : Edge n) ∈ b j → False) →
      (∀ i j : Fin 5, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j →
        ∀ c : Fin n, c ∉ s → c ≠ tA → c ≠ tB → ({sB, c} : Edge n) ∈ b i →
        ∀ a : Fin n, a ∈ s → a ≠ sA → a ≠ sB → ({a, tB} : Edge n) ∈ b j → False) →
      (∃ i₁ i₂ : Fin 5, i₁ ≠ 0 ∧ i₁ ≠ 1 ∧ i₂ ≠ 0 ∧ i₂ ≠ 1 ∧ i₁ ≠ i₂ ∧
        (∃ a : Fin n, a ∈ s ∧ a ≠ sA ∧ a ≠ sB ∧ ({a, tA} : Edge n) ∈ b i₁) ∧
        (∃ a : Fin n, a ∈ s ∧ a ≠ sA ∧ a ≠ sB ∧ ({a, tA} : Edge n) ∈ b i₂)) →
      False := by
    intro sA sB tA tB hsA hsB htA htB hsAB htAB hhit' hswA hswB ⟨i₁, i₂, hi10, hi11, hi20, hi21, hi12, hp1, hp2⟩
    have hq_all : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 →
        ∃ c : Fin n, c ∉ s ∧ c ≠ tA ∧ c ≠ tB ∧ ({sB, c} : Edge n) ∈ b i := by
      intro i hi0 hi1
      rcases exists_edge_disjoint_of_card_le_two (hgood i)
          (le_trans (Finset.card_insert_le tA {tB}) (by simp)) with ⟨e, hei, hde⟩
      rcases bip_edge_split ((hgood i).2.1 e hei) (hbip i e hei) with ⟨a, c, has, hcs, rfl⟩
      have hcA : c ≠ tA := fun h => Finset.disjoint_left.mp hde
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self c)) (by rw [h]; exact Finset.mem_insert_self _ _)
      have hcB : c ≠ tB := fun h => Finset.disjoint_left.mp hde
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self c))
        (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rcases hhit' i hi0 hi1 a c has hcs hei with (haA | haB) | (hcA' | hcB')
      · rw [haA] at hei
        by_cases hii1 : i = i₁
        · rcases hp2 with ⟨a2, ha2s, ha2A, ha2B, hb2⟩
          exact False.elim (hswA i i₂ hi0 hi1 hi20 hi21 (hii1 ▸ hi12) c hcs hcA hcB hei a2 ha2s ha2A ha2B hb2)
        · rcases hp1 with ⟨a1, ha1s, ha1A, ha1B, hb1⟩
          exact False.elim (hswA i i₁ hi0 hi1 hi10 hi11 hii1 c hcs hcA hcB hei a1 ha1s ha1A ha1B hb1)
      · rw [haB] at hei
        exact ⟨c, hcs, hcA, hcB, hei⟩
      · exact absurd hcA' hcA
      · exact absurd hcB' hcB
    rcases hq_all 2 (by decide) (by decide) with ⟨c2, hc2s, hc2A, hc2B, hq2⟩
    rcases hq_all 3 (by decide) (by decide) with ⟨c3, hc3s, hc3A, hc3B, hq3⟩
    rcases hq_all 4 (by decide) (by decide) with ⟨c4, hc4s, hc4A, hc4B, hq4⟩
    have hp_all : ∀ j : Fin 5, j ≠ 0 → j ≠ 1 →
        ∃ a : Fin n, a ∈ s ∧ a ≠ sA ∧ a ≠ sB ∧ ({a, tA} : Edge n) ∈ b j := by
      intro j hj0 hj1
      rcases exists_edge_disjoint_of_card_le_two (hgood j)
          (le_trans (Finset.card_insert_le sA {sB}) (by simp)) with ⟨e, hej, hde⟩
      rcases bip_edge_split ((hgood j).2.1 e hej) (hbip j e hej) with ⟨a, c, has, hcs, rfl⟩
      have haA : a ≠ sA := fun h => Finset.disjoint_left.mp hde
        (Finset.mem_insert_self a _) (by rw [h]; exact Finset.mem_insert_self _ _)
      have haB : a ≠ sB := fun h => Finset.disjoint_left.mp hde
        (Finset.mem_insert_self a _) (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      rcases hhit' j hj0 hj1 a c has hcs hej with (haA' | haB') | (hcA' | hcB')
      · exact absurd haA' haA
      · exact absurd haB' haB
      · rw [hcA'] at hej
        exact ⟨a, has, haA, haB, hej⟩
      · rw [hcB'] at hej
        by_cases hj2 : j = 2
        · exact False.elim (hswB 3 j (by decide) (by decide) hj0 hj1 (by omega) c3 hc3s hc3A hc3B hq3 a has haA haB hej)
        · exact False.elim (hswB 2 j (by decide) (by decide) hj0 hj1 (Ne.symm hj2) c2 hc2s hc2A hc2B hq2 a has haA haB hej)
    rcases hp_all 2 (by decide) (by decide) with ⟨a2, ha2s, ha2A, ha2B, hp2'⟩
    rcases hp_all 3 (by decide) (by decide) with ⟨a3, ha3s, ha3A, ha3B, hp3'⟩
    have hne_pq : ({a2, tA} : Edge n) ≠ {sB, c2} := by
      intro h
      have : a2 ∈ ({sB, c2} : Edge n) := h ▸ Finset.mem_insert_self a2 _
      rcases Finset.mem_insert.mp this with h' | h'
      · exact ha2B h'
      · exact hc2s (Finset.mem_singleton.mp h' ▸ ha2s)
    have hrest : ((b 2).erase {a2, tA} |>.erase {sB, c2}).card = 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne_pq.symm, hq2⟩),
        Finset.card_erase_of_mem hp2', (hgood 2).1]
    rcases Finset.card_eq_one.mp hrest with ⟨r, hr⟩
    have hr_mem : r ∈ ((b 2).erase {a2, tA}).erase {sB, c2} := hr ▸ Finset.mem_singleton_self r
    have hr_ne_q : r ≠ {sB, c2} := (Finset.mem_erase.mp hr_mem).1
    have hr_ne_p : r ≠ {a2, tA} := (Finset.mem_erase.mp (Finset.mem_erase.mp hr_mem).2).1
    have hr_b2 : r ∈ b 2 := (Finset.mem_erase.mp (Finset.mem_erase.mp hr_mem).2).2
    rcases bip_edge_split ((hgood 2).2.1 r hr_b2) (hbip 2 r hr_b2) with ⟨ar, cr, hars, hcrs, rfl⟩
    have hd_rp := pair_disjoint_iff.mp ((hgood 2).2.2 _ hr_b2 _ hp2' hr_ne_p)
    have hd_rq := pair_disjoint_iff.mp ((hgood 2).2.2 _ hr_b2 _ hq2 hr_ne_q)
    have harB : ar ≠ sB := hd_rq.1
    have hcrA : cr ≠ tA := hd_rp.2.2.2
    have harA : ar = sA := by
      by_contra hneA
      rcases hhit' 2 (by decide) (by decide) ar cr hars hcrs hr_b2 with (h1 | h2) | (h3 | h4)
      · exact hneA h1
      · exact harB h2
      · exact hcrA h3
      · rw [h4] at hr_b2
        exact hswB 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)
          c3 hc3s hc3A hc3B hq3 ar hars hneA harB hr_b2
    subst ar
    have hcrB : cr = tB := by
      by_contra hneB
      exact hswA 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
        cr hcrs hcrA hneB hr_b2 a3 ha3s ha3A ha3B hp3'
    subst cr
    have hd1 : Disjoint ({sA, tB} : Edge n) {a3, tA} := by
      rw [pair_disjoint_iff]
      refine ⟨Ne.symm ha3A, fun h => htA (h ▸ hsA), fun h => htB (h ▸ ha3s), htAB.symm⟩
    have hd2 : Disjoint ({sA, tB} : Edge n) {sB, c4} := by
      rw [pair_disjoint_iff]
      refine ⟨hsAB, fun h => hc4s (h ▸ hsA), fun h => htB (h ▸ hsB), Ne.symm hc4B⟩
    have hd3 : Disjoint ({a3, tA} : Edge n) {sB, c4} := by
      rw [pair_disjoint_iff]
      refine ⟨ha3B, fun h => hc4s (h ▸ ha3s), fun h => htA (h ▸ hsB), Ne.symm hc4A⟩
    exact hno (rainbow_of_three (by decide) (by decide) (by decide) hr_b2 hp3' hq4 hd1 hd2 hd3)
  rcases hex_p 2 (by decide) (by decide) with ⟨a2, c2, ha2s, _, ha20, ha21, hc2, hp2⟩
  rcases hex_p 3 (by decide) (by decide) with ⟨a3, c3, ha3s, _, ha30, ha31, hc3, hp3⟩
  rcases hex_p 4 (by decide) (by decide) with ⟨a4, c4, ha4s, _, ha40, ha41, hc4, hp4⟩
  have hhit_sw : ∀ i : Fin 5, i ≠ 0 → i ≠ 1 → ∀ a c : Fin n, a ∈ s → c ∉ s → ({a, c} : Edge n) ∈ b i →
      (a = s₁ ∨ a = s₀) ∨ (c = t₁ ∨ c = t₀) := fun i hi0 hi1 a c has hcs hac => by
    rcases hhit i hi0 hi1 a c has hcs hac with (h | h) | (h | h)
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  have hsw1' : ∀ i j : Fin 5, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j →
      ∀ c : Fin n, c ∉ s → c ≠ t₁ → c ≠ t₀ → ({s₁, c} : Edge n) ∈ b i →
      ∀ a : Fin n, a ∈ s → a ≠ s₁ → a ≠ s₀ → ({a, t₁} : Edge n) ∈ b j → False :=
    fun i j hi0 hi1 hj0 hj1 hij c hcs h1 h2 hbi a has ha1 ha2 hbj =>
      hno_swap1 i j hi0 hi1 hj0 hj1 hij c hcs h2 h1 hbi a has ha2 ha1 hbj
  have hsw0' : ∀ i j : Fin 5, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → i ≠ j →
      ∀ c : Fin n, c ∉ s → c ≠ t₁ → c ≠ t₀ → ({s₀, c} : Edge n) ∈ b i →
      ∀ a : Fin n, a ∈ s → a ≠ s₁ → a ≠ s₀ → ({a, t₀} : Edge n) ∈ b j → False :=
    fun i j hi0 hi1 hj0 hj1 hij c hcs h1 h2 hbi a has ha1 ha2 hbj =>
      hno_swap0 i j hi0 hi1 hj0 hj1 hij c hcs h2 h1 hbi a has ha2 ha1 hbj
  rcases hc2 with hc2 | hc2 <;> rcases hc3 with hc3 | hc3 <;> rcases hc4 with hc4 | hc4
  · exact hfinish s₀ s₁ t₀ t₁ hs₀ hs₁ ht₀ ht₁ hs01 ht01 hhit hno_swap0 hno_swap1
      ⟨2, 3, by decide, by decide, by decide, by decide, by decide,
        ⟨a2, ha2s, ha20, ha21, hc2 ▸ hp2⟩, ⟨a3, ha3s, ha30, ha31, hc3 ▸ hp3⟩⟩
  · exact hfinish s₀ s₁ t₀ t₁ hs₀ hs₁ ht₀ ht₁ hs01 ht01 hhit hno_swap0 hno_swap1
      ⟨2, 3, by decide, by decide, by decide, by decide, by decide,
        ⟨a2, ha2s, ha20, ha21, hc2 ▸ hp2⟩, ⟨a3, ha3s, ha30, ha31, hc3 ▸ hp3⟩⟩
  · exact hfinish s₀ s₁ t₀ t₁ hs₀ hs₁ ht₀ ht₁ hs01 ht01 hhit hno_swap0 hno_swap1
      ⟨2, 4, by decide, by decide, by decide, by decide, by decide,
        ⟨a2, ha2s, ha20, ha21, hc2 ▸ hp2⟩, ⟨a4, ha4s, ha40, ha41, hc4 ▸ hp4⟩⟩
  · exact hfinish s₁ s₀ t₁ t₀ hs₁ hs₀ ht₁ ht₀ hs01.symm ht01.symm hhit_sw hsw1' hsw0'
      ⟨3, 4, by decide, by decide, by decide, by decide, by decide,
        ⟨a3, ha3s, ha31, ha30, hc3 ▸ hp3⟩, ⟨a4, ha4s, ha41, ha40, hc4 ▸ hp4⟩⟩
  · exact hfinish s₀ s₁ t₀ t₁ hs₀ hs₁ ht₀ ht₁ hs01 ht01 hhit hno_swap0 hno_swap1
      ⟨3, 4, by decide, by decide, by decide, by decide, by decide,
        ⟨a3, ha3s, ha30, ha31, hc3 ▸ hp3⟩, ⟨a4, ha4s, ha40, ha41, hc4 ▸ hp4⟩⟩
  · exact hfinish s₁ s₀ t₁ t₀ hs₁ hs₀ ht₁ ht₀ hs01.symm ht01.symm hhit_sw hsw1' hsw0'
      ⟨2, 4, by decide, by decide, by decide, by decide, by decide,
        ⟨a2, ha2s, ha21, ha20, hc2 ▸ hp2⟩, ⟨a4, ha4s, ha41, ha40, hc4 ▸ hp4⟩⟩
  · exact hfinish s₁ s₀ t₁ t₀ hs₁ hs₀ ht₁ ht₀ hs01.symm ht01.symm hhit_sw hsw1' hsw0'
      ⟨2, 3, by decide, by decide, by decide, by decide, by decide,
        ⟨a2, ha2s, ha21, ha20, hc2 ▸ hp2⟩, ⟨a3, ha3s, ha31, ha30, hc3 ▸ hp3⟩⟩
  · exact hfinish s₁ s₀ t₁ t₀ hs₁ hs₀ ht₁ ht₀ hs01.symm ht01.symm hhit_sw hsw1' hsw0'
      ⟨2, 3, by decide, by decide, by decide, by decide, by decide,
        ⟨a2, ha2s, ha21, ha20, hc2 ▸ hp2⟩, ⟨a3, ha3s, ha31, ha30, hc3 ▸ hp3⟩⟩

lemma type1_decomp {n : ℕ} {x₀ x₁ x₂ x₃ : Fin n}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    {m : Matching n} (hm : Good m)
    (hhit : ∀ e ∈ m, ¬ Disjoint e ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hint : ({x₀, x₁} : Edge n) ∈ m) :
    ∃ u v : Fin n,
      u ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) ∧
      v ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) ∧
      u ≠ v ∧ ({x₂, u} : Edge n) ∈ m ∧ ({x₃, v} : Edge n) ∈ m := by
  let X : Finset (Fin n) := {x₀, x₁, x₂, x₃}
  have hrem_card : (m.erase {x₀, x₁}).card = 2 := by
    rw [Finset.card_erase_of_mem hint, hm.1]
  rcases Finset.card_eq_two.mp hrem_card with ⟨e₁, e₂, hne12, hrem⟩
  have he1 : e₁ ≠ {x₀, x₁} ∧ e₁ ∈ m := Finset.mem_erase.mp (hrem ▸ Finset.mem_insert_self e₁ _)
  have he2 : e₂ ≠ {x₀, x₁} ∧ e₂ ∈ m := Finset.mem_erase.mp (hrem ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self e₂))
  have hd1 : Disjoint e₁ {x₀, x₁} := hm.2.2 e₁ he1.2 _ hint he1.1
  have hd2 : Disjoint e₂ {x₀, x₁} := hm.2.2 e₂ he2.2 _ hint he2.1
  have hd12 : Disjoint e₁ e₂ := hm.2.2 e₁ he1.2 e₂ he2.2 hne12
  have hhit23 : ∀ e ∈ m, Disjoint e {x₀, x₁} → x₂ ∈ e ∨ x₃ ∈ e := by
    intro e hem hde
    rcases Finset.not_disjoint_iff.mp (hhit e hem) with ⟨w, hwe, hwX⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwX
    rcases hwX with rfl | rfl | rfl | rfl
    · exact absurd (Finset.mem_insert_self _ _) (Finset.disjoint_left.mp hde hwe)
    · exact absurd (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) (Finset.disjoint_left.mp hde hwe)
    · exact Or.inl hwe
    · exact Or.inr hwe
  have hextract : ∀ e ∈ m, Disjoint e {x₀, x₁} → ∀ a b : Fin n, a ∈ e → b ∉ e →
      ({a, b} : Finset (Fin n)) = {x₂, x₃} →
      ∃ u : Fin n, u ∉ X ∧ e = {a, u} := by
    intro e hem hde a b hae hbe hab
    have hcard : (e.erase a).card = 1 := by
      rw [Finset.card_erase_of_mem hae, hm.2.1 e hem]
    rcases Finset.card_eq_one.mp hcard with ⟨u, hu⟩
    have hue : u ∈ e ∧ u ≠ a := by
      have := Finset.mem_erase.mp (hu ▸ Finset.mem_singleton_self u)
      exact ⟨this.2, this.1⟩
    have huX : u ∉ X := by
      intro huX
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at huX
      rcases huX with rfl | rfl | hu2 | hu3
      · exact Finset.disjoint_left.mp hde hue.1 (Finset.mem_insert_self _ _)
      · exact Finset.disjoint_left.mp hde hue.1 (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      · have h2 : x₂ ∈ ({a, b} : Finset (Fin n)) := hab.symm ▸ Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp h2 with h2a | h2b
        · exact hue.2 (hu2.trans h2a)
        · exact hbe ((hu2.trans (Finset.mem_singleton.mp h2b)) ▸ hue.1)
      · have h3 : x₃ ∈ ({a, b} : Finset (Fin n)) := hab.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rcases Finset.mem_insert.mp h3 with h3a | h3b
        · exact hue.2 (hu3.trans h3a)
        · exact hbe ((hu3.trans (Finset.mem_singleton.mp h3b)) ▸ hue.1)
    refine ⟨u, huX, ?_⟩
    ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hw
      by_cases hwa : w = a
      · exact Or.inl hwa
      · right
        have : w ∈ e.erase a := Finset.mem_erase.mpr ⟨hwa, hw⟩
        rwa [hu, Finset.mem_singleton] at this
    · rintro (rfl | rfl)
      · exact hae
      · exact hue.1
  rcases hhit23 e₁ he1.2 hd1 with h12' | h13'
  · have h22' : x₂ ∉ e₂ := Finset.disjoint_left.mp hd12 h12'
    have h23' : x₃ ∈ e₂ := (hhit23 e₂ he2.2 hd2).resolve_left h22'
    have h13_not : x₃ ∉ e₁ := Finset.disjoint_right.mp hd12 h23'
    rcases hextract e₁ he1.2 hd1 x₂ x₃ h12' h13_not rfl with ⟨u, huX, rfl⟩
    rcases hextract e₂ he2.2 hd2 x₃ x₂ h23' h22' (pair_comm x₃ x₂) with ⟨v, hvX, rfl⟩
    exact ⟨u, v, huX, hvX, (pair_disjoint_iff.mp hd12).2.2.2, he1.2, he2.2⟩
  · have h23' : x₃ ∉ e₂ := Finset.disjoint_left.mp hd12 h13'
    have h22' : x₂ ∈ e₂ := (hhit23 e₂ he2.2 hd2).resolve_right h23'
    have h12_not : x₂ ∉ e₁ := Finset.disjoint_right.mp hd12 h22'
    rcases hextract e₂ he2.2 hd2 x₂ x₃ h22' h23' rfl with ⟨u, huX, rfl⟩
    rcases hextract e₁ he1.2 hd1 x₃ x₂ h13' h12_not (pair_comm x₃ x₂) with ⟨v, hvX, rfl⟩
    exact ⟨u, v, huX, hvX, (pair_disjoint_iff.mp hd12).2.2.2.symm, he2.2, he1.2⟩

lemma type0_decomp {n : ℕ} {X : Finset (Fin n)} (hX : X.card = 4)
    {m : Matching n} (hm : Good m) (hhit : ∀ e ∈ m, ¬ Disjoint e X)
    (hnoint : ∀ e ∈ m, ¬ (e ⊆ X)) :
    ∃ miss ∈ X, ∀ x ∈ X, x ≠ miss → ∃ u : Fin n, u ∉ X ∧ ({x, u} : Edge n) ∈ m := by
  have hnpos : 0 < n := by
    by_contra h0
    have hn : n = 0 := by omega
    subst hn
    have : X = ∅ := by ext x; exact Fin.elim0 x
    rw [this] at hX; simp at hX
  have hbip : ∀ e ∈ m, (e ∩ X).card = 1 := by
    intro e hem
    have hpos : 0 < (e ∩ X).card := Finset.card_pos.mpr
      (Finset.not_disjoint_iff.mp (hhit e hem) |> fun ⟨v, hv1, hv2⟩ => ⟨v, Finset.mem_inter.mpr ⟨hv1, hv2⟩⟩)
    have hle : (e ∩ X).card ≤ 2 := le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq (hm.2.1 e hem))
    have hne2 : (e ∩ X).card ≠ 2 := by
      intro h2
      apply hnoint e hem
      have heq : e ∩ X = e := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h2, hm.2.1 e hem])
      intro v hv; rw [← heq] at hv; exact (Finset.mem_inter.mp hv).2
    omega
  let cov : Finset (Fin n) := X.filter (fun x => ∃ u : Fin n, u ∉ X ∧ ({x, u} : Edge n) ∈ m)
  have hcov_card : cov.card = 3 := by
    let g : Edge n → Fin n := fun e =>
      if h : ∃ a b, a ∈ X ∧ b ∉ X ∧ e = {a, b} then Classical.choose h else ⟨0, hnpos⟩
    have hmaps : Set.MapsTo g (m : Set (Edge n)) (cov : Set (Fin n)) := by
      intro e hem
      have hex : ∃ a b, a ∈ X ∧ b ∉ X ∧ e = {a, b} := bip_edge_split (hm.2.1 e hem) (hbip e hem)
      simp only [g, hex, ↓reduceDIte]
      rcases Classical.choose_spec hex with ⟨b, haX, hbX, heq⟩
      exact Finset.mem_filter.mpr ⟨haX, b, hbX, heq ▸ hem⟩
    have hinj : Set.InjOn g (m : Set (Edge n)) := by
      intro e₁ h1 e₂ h2 hgeq
      have hex1 : ∃ a b, a ∈ X ∧ b ∉ X ∧ e₁ = {a, b} := bip_edge_split (hm.2.1 e₁ h1) (hbip e₁ h1)
      have hex2 : ∃ a b, a ∈ X ∧ b ∉ X ∧ e₂ = {a, b} := bip_edge_split (hm.2.1 e₂ h2) (hbip e₂ h2)
      simp only [g, hex1, hex2, ↓reduceDIte] at hgeq
      rcases Classical.choose_spec hex1 with ⟨b1, _, _, he1⟩
      rcases Classical.choose_spec hex2 with ⟨b2, _, _, he2⟩
      generalize Classical.choose hex1 = a1 at hgeq he1
      generalize Classical.choose hex2 = a2 at hgeq he2
      have hmem1 : a1 ∈ e₁ := by rw [he1]; exact Finset.mem_insert_self _ _
      have hmem2 : a1 ∈ e₂ := by rw [hgeq, he2]; exact Finset.mem_insert_self _ _
      exact good_eq_of_mem_mem hm h1 h2 hmem1 hmem2
    have hge : 3 ≤ cov.card := by
      rw [← hm.1]; exact Finset.card_le_card_of_injOn g hmaps hinj
    have hle : cov.card ≤ 3 := by
      let g2 : Fin n → Edge n := fun x =>
        if h : ∃ u, u ∉ X ∧ ({x, u} : Edge n) ∈ m then {x, Classical.choose h} else ∅
      have hmaps2 : Set.MapsTo g2 (cov : Set (Fin n)) (m : Set (Edge n)) := by
        intro x hx
        have hxf := (Finset.mem_filter.mp hx).2
        simp only [g2, hxf, ↓reduceDIte]
        exact (Classical.choose_spec hxf).2
      have hinj2 : Set.InjOn g2 (cov : Set (Fin n)) := by
        intro x₁ hx₁ x₂ hx₂ heq
        have h1 := Finset.mem_filter.mp hx₁
        have h2 := Finset.mem_filter.mp hx₂
        simp only [g2, h1.2, h2.2, ↓reduceDIte] at heq
        have hx1m : x₁ ∈ ({x₂, Classical.choose h2.2} : Edge n) := by rw [← heq]; exact Finset.mem_insert_self _ _
        rcases Finset.mem_insert.mp hx1m with rfl | h'
        · rfl
        · exact absurd (Finset.mem_singleton.mp h' ▸ h1.1) (Classical.choose_spec h2.2).1
      have := Finset.card_le_card_of_injOn g2 hmaps2 hinj2
      rwa [hm.1] at this
    omega
  have hdiff : (X \ cov).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.filter_subset _ _), hX, hcov_card]
  rcases Finset.card_eq_one.mp hdiff with ⟨miss, hmiss⟩
  have hmissX : miss ∈ X := (Finset.mem_sdiff.mp (hmiss ▸ Finset.mem_singleton_self miss)).1
  refine ⟨miss, hmissX, ?_⟩
  intro x hxX hxne
  have hxcov : x ∈ cov := by
    by_contra hnot
    have : x ∈ X \ cov := Finset.mem_sdiff.mpr ⟨hxX, hnot⟩
    rw [hmiss, Finset.mem_singleton] at this
    exact hxne this
  exact (Finset.mem_filter.mp hxcov).2

lemma kill_cross_eq {n : ℕ} {m : Fin 5 → Matching n} (hno : ¬ Rainbow 5 m)
    {x₀ x₁ x₂ x₃ u v : Fin n}
    (_h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (huX : u ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hvX : v ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    {i₀ i₁ i₂ : Fin 5} (h01i : i₀ ≠ i₁) (h02i : i₀ ≠ i₂) (h12i : i₁ ≠ i₂)
    (hm0 : ({x₀, x₁} : Edge n) ∈ m i₀)
    (hm1 : ({x₂, u} : Edge n) ∈ m i₁)
    (hm2 : ({x₃, v} : Edge n) ∈ m i₂) : u = v := by
  by_contra huv
  have hu : u ≠ x₀ ∧ u ≠ x₁ ∧ u ≠ x₂ ∧ u ≠ x₃ := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at huX
    exact ⟨huX.1, huX.2.1, huX.2.2.1, huX.2.2.2⟩
  have hv : v ≠ x₀ ∧ v ≠ x₁ ∧ v ≠ x₂ ∧ v ≠ x₃ := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hvX
    exact ⟨hvX.1, hvX.2.1, hvX.2.2.1, hvX.2.2.2⟩
  have hd01 : Disjoint ({x₀, x₁} : Edge n) {x₂, u} :=
    pair_disjoint_iff.mpr ⟨h02, hu.1.symm, h12, hu.2.1.symm⟩
  have hd02 : Disjoint ({x₀, x₁} : Edge n) {x₃, v} :=
    pair_disjoint_iff.mpr ⟨h03, hv.1.symm, h13, hv.2.1.symm⟩
  have hd12 : Disjoint ({x₂, u} : Edge n) {x₃, v} :=
    pair_disjoint_iff.mpr ⟨h23, hv.2.2.1.symm, hu.2.2.2, huv⟩
  exact hno (rainbow_of_three h01i h02i h12i hm0 hm1 hm2 hd01 hd02 hd12)

lemma kill_three_cross {n : ℕ} {m : Fin 5 → Matching n} (hno : ¬ Rainbow 5 m)
    {x₀ x₁ x₂ u₀ u₁ u₂ : Fin n}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂)
    (hu0 : u₀ ≠ x₀ ∧ u₀ ≠ x₁ ∧ u₀ ≠ x₂)
    (hu1 : u₁ ≠ x₀ ∧ u₁ ≠ x₁ ∧ u₁ ≠ x₂)
    (hu2 : u₂ ≠ x₀ ∧ u₂ ≠ x₁ ∧ u₂ ≠ x₂)
    {i₀ i₁ i₂ : Fin 5} (h01i : i₀ ≠ i₁) (h02i : i₀ ≠ i₂) (h12i : i₁ ≠ i₂)
    (hm0 : ({x₀, u₀} : Edge n) ∈ m i₀)
    (hm1 : ({x₁, u₁} : Edge n) ∈ m i₁)
    (hm2 : ({x₂, u₂} : Edge n) ∈ m i₂) :
    u₀ = u₁ ∨ u₀ = u₂ ∨ u₁ = u₂ := by
  by_contra h
  push Not at h
  rcases h with ⟨h01u, h02u, h12u⟩
  have hd01 : Disjoint ({x₀, u₀} : Edge n) {x₁, u₁} :=
    pair_disjoint_iff.mpr ⟨h01, hu1.1.symm, hu0.2.1, h01u⟩
  have hd02 : Disjoint ({x₀, u₀} : Edge n) {x₂, u₂} :=
    pair_disjoint_iff.mpr ⟨h02, hu2.1.symm, hu0.2.2, h02u⟩
  have hd12 : Disjoint ({x₁, u₁} : Edge n) {x₂, u₂} :=
    pair_disjoint_iff.mpr ⟨h12, hu2.2.1.symm, hu1.2.2, h12u⟩
  exact hno (rainbow_of_three h01i h02i h12i hm0 hm1 hm2 hd01 hd02 hd12)

lemma kill_fork {n : ℕ} {m : Fin 5 → Matching n} (hno : ¬ Rainbow 5 m)
    {x₀ x₁ x₂ x₃ a b c : Fin n}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (haX : a ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hbX : b ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hcX : c ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hab : a ≠ b)
    {i₀ i₁ i₂ i₃ : Fin 5}
    (h02i : i₀ ≠ i₂) (h03i : i₀ ≠ i₃) (h12i : i₁ ≠ i₂) (h13i : i₁ ≠ i₃) (h23i : i₂ ≠ i₃)
    (hm0 : ({x₀, x₁} : Edge n) ∈ m i₀)
    (hm1 : ({x₀, x₂} : Edge n) ∈ m i₁)
    (hm2a : ({x₁, a} : Edge n) ∈ m i₂)
    (hm2b : ({x₂, b} : Edge n) ∈ m i₂)
    (hm3 : ({x₃, c} : Edge n) ∈ m i₃) : False := by
  have hbc : b = c := kill_cross_eq hno h01 h02 h03 h12 h13 h23 hbX hcX h02i h03i h23i hm0 hm2b hm3
  have haX' : a ∉ ({x₀, x₂, x₁, x₃} : Finset (Fin n)) := by
    simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using haX
  have hcX' : c ∉ ({x₀, x₂, x₁, x₃} : Finset (Fin n)) := by
    simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hcX
  have hac : a = c := kill_cross_eq hno h02 h01 h03 h12.symm h23 h13 haX' hcX' h12i h13i h23i hm1 hm2a hm3
  exact hab (hac.trans hbc.symm)

lemma not_three_same_int {n : ℕ} {m : Fin 5 → Matching n} (hgood : ∀ i, Good (m i))
    {x₀ x₁ x₂ x₃ : Fin n}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hhit : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hno : ¬ Rainbow 5 m)
    {i₀ i₁ i₂ : Fin 5} (h01i : i₀ ≠ i₁) (h02i : i₀ ≠ i₂) (h12i : i₁ ≠ i₂)
    (hm0 : ({x₀, x₁} : Edge n) ∈ m i₀)
    (hm1 : ({x₀, x₁} : Edge n) ∈ m i₁)
    (hm2 : ({x₀, x₁} : Edge n) ∈ m i₂) : False := by
  rcases type1_decomp h01 h02 h03 h12 h13 h23 (hgood i₀) (hhit i₀) hm0 with ⟨u₀, v₀, hu0, hv0, huv0, h2u0, h3v0⟩
  rcases type1_decomp h01 h02 h03 h12 h13 h23 (hgood i₁) (hhit i₁) hm1 with ⟨u₁, v₁, hu1, hv1, huv1, h2u1, h3v1⟩
  rcases type1_decomp h01 h02 h03 h12 h13 h23 (hgood i₂) (hhit i₂) hm2 with ⟨u₂, v₂, hu2, hv2, huv2, h2u2, h3v2⟩
  have h1 : u₀ = v₂ := kill_cross_eq hno h01 h02 h03 h12 h13 h23 hu0 hv2 h01i.symm h12i h02i hm1 h2u0 h3v2
  have h2 : u₁ = v₂ := kill_cross_eq hno h01 h02 h03 h12 h13 h23 hu1 hv2 h01i h02i h12i hm0 h2u1 h3v2
  have h3 : u₁ = v₀ := kill_cross_eq hno h01 h02 h03 h12 h13 h23 hu1 hv0 h12i.symm h02i.symm h01i.symm hm2 h2u1 h3v0
  exact huv0 ((h1.trans h2.symm).trans h3)

lemma int_edge_cases {n : ℕ} {x₀ x₁ x₂ x₃ : Fin n} {d : Edge n}
    (hd2 : d.card = 2) (hdsub : d ⊆ ({x₀, x₁, x₂, x₃} : Finset (Fin n))) :
    d = {x₀, x₁} ∨ d = {x₀, x₂} ∨ d = {x₀, x₃} ∨ d = {x₁, x₂} ∨ d = {x₁, x₃} ∨ d = {x₂, x₃} := by
  rcases Finset.card_eq_two.mp hd2 with ⟨a, b, hab, rfl⟩
  have ha : a ∈ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) := hdsub (Finset.mem_insert_self a _)
  have hb : b ∈ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) := hdsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  · exact absurd rfl hab
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl (pair_comm _ _)
  · exact absurd rfl hab
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inl (pair_comm _ _))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (pair_comm _ _))))
  · exact absurd rfl hab
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · exact Or.inr (Or.inr (Or.inl (pair_comm _ _)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (pair_comm _ _)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (pair_comm _ _)))))
  · exact absurd rfl hab

lemma not_mem_X4 {n : ℕ} {x₀ x₁ x₂ x₃ u : Fin n}
    (h : u ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n))) :
    u ≠ x₀ ∧ u ≠ x₁ ∧ u ≠ x₂ ∧ u ≠ x₃ := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

lemma case_all_type1 {n : ℕ} {m : Fin 5 → Matching n} (hgood : ∀ i, Good (m i))
    {x₀ x₁ x₂ x₃ : Fin n}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hhit : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hint : ∀ i : Fin 5, ∃ d ∈ m i, d ⊆ ({x₀, x₁, x₂, x₃} : Finset (Fin n))) :
    Rainbow 5 m := by
  by_contra hno
  let X : Finset (Fin n) := {x₀, x₁, x₂, x₃}
  have hstar : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (i₀ i₁ i₂ : Fin 5), i₀ ≠ i₁ → i₀ ≠ i₂ → i₁ ≠ i₂ →
      ({a, b} : Edge n) ∈ m i₀ → ({a, c} : Edge n) ∈ m i₁ → ({a, d} : Edge n) ∈ m i₂ → False := by
    intro a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ h01i h02i h12i hm0 hm1 hm2
    have hhit' : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({a, b, c, d} : Finset (Fin n)) := by
      rw [hXeq]; exact hhit
    rcases type1_decomp had hab hac hbd.symm hcd.symm hbc (hgood i₂)
        (by intro e he; convert hhit' i₂ e he using 2; ext z; simp [or_comm, or_left_comm]) hm2 with
      ⟨ub, uc, hub, huc, hubc, hmb, hmc⟩
    have hub' : ub ∉ ({a, b, c, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hub
    have huc' : uc ∉ ({a, b, c, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using huc
    have hex3 : ∃ i₃ : Fin 5, i₃ ≠ i₀ ∧ i₃ ≠ i₁ ∧ i₃ ≠ i₂ := by
      rcases fin5_other_three i₀ i₁ h01i with ⟨c1, c2, c3, h10, h11, h20, h21, h30, h31, h12', h13', h23'⟩
      by_cases h : c1 = i₂
      · exact ⟨c2, h20, h21, h ▸ h12'.symm⟩
      · exact ⟨c1, h10, h11, h⟩
    rcases hex3 with ⟨i₃, h30, h31, h32⟩
    rcases hint i₃ with ⟨e3, he3m, he3sub⟩
    rw [← hXeq] at he3sub
    rcases int_edge_cases ((hgood i₃).2.1 e3 he3m) he3sub with
        rfl | rfl | rfl | rfl | rfl | rfl
    · rcases type1_decomp hab hac had hbc hbd hcd (hgood i₃) (hhit' i₃) he3m with
        ⟨_, wd, _, hwd, _, _, hmd⟩
      exact kill_fork hno hab hac had hbc hbd hcd hub' huc' hwd hubc h02i h30.symm h12i h31.symm h32.symm hm0 hm1 hmb hmc hmd
    · rcases type1_decomp hac hab had hbc.symm hcd hbd (hgood i₃)
          (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) he3m with
        ⟨_, wd, _, hwd, _, _, hmd⟩
      have hwd' : wd ∉ ({a, b, c, d} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwd
      exact kill_fork hno hab hac had hbc hbd hcd hub' huc' hwd' hubc h02i h30.symm h12i h31.symm h32.symm hm0 hm1 hmb hmc hmd
    · rcases type1_decomp had hab hac hbd.symm hcd.symm hbc (hgood i₃)
          (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) he3m with
        ⟨wb, _, hwb, _, _, hmb3, _⟩
      have hwb' : wb ∉ ({a, c, d, b} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwb
      rcases type1_decomp hab hac had hbc hbd hcd (hgood i₀) (hhit' i₀) hm0 with
        ⟨vc, vd, hvc, hvd, hvcd, hmc0, hmd0⟩
      have hvc' : vc ∉ ({a, c, d, b} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hvc
      have hvd' : vd ∉ ({a, c, d, b} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hvd
      exact kill_fork hno hac had hab hcd hbc.symm hbd.symm hvc' hvd' hwb' hvcd
        h01i.symm h31.symm h02i.symm h32.symm h30.symm hm1 hm2 hmc0 hmd0 hmb3
    · rcases type1_decomp hbc hab.symm hbd hac.symm hcd had (hgood i₃)
          (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) he3m with
        ⟨_, wd, _, hwd, _, _, hmd⟩
      have hwd' : wd ∉ ({a, b, c, d} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwd
      exact kill_fork hno hab hac had hbc hbd hcd hub' huc' hwd' hubc h02i h30.symm h12i h31.symm h32.symm hm0 hm1 hmb hmc hmd
    · rcases type1_decomp hbd hab.symm hbc had.symm hcd.symm hac (hgood i₃)
          (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) he3m with
        ⟨_, wc, _, hwc, _, _, hmc3⟩
      have hwc' : wc ∉ ({a, b, d, c} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwc
      rcases type1_decomp hac hab had hbc.symm hcd hbd (hgood i₁)
          (by intro e he; convert hhit' i₁ e he using 2; ext z; simp [or_comm, or_left_comm]) hm1 with
        ⟨vb, vd, hvb, hvd, hvbd, hmb1, hmd1⟩
      have hvb' : vb ∉ ({a, b, d, c} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hvb
      have hvd' : vd ∉ ({a, b, d, c} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hvd
      exact kill_fork hno hab had hac hbd hbc hcd.symm hvb' hvd' hwc' hvbd
        h01i h30.symm h12i.symm h32.symm h31.symm hm0 hm2 hmb1 hmd1 hmc3
    · rcases type1_decomp hcd hac.symm hbc.symm had.symm hbd.symm hab (hgood i₃)
          (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) he3m with
        ⟨_, wb, _, hwb, _, _, hmb3⟩
      have hwb' : wb ∉ ({a, c, d, b} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwb
      rcases type1_decomp hab hac had hbc hbd hcd (hgood i₀) (hhit' i₀) hm0 with
        ⟨vc, vd, hvc, hvd, hvcd, hmc0, hmd0⟩
      have hvc' : vc ∉ ({a, c, d, b} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hvc
      have hvd' : vd ∉ ({a, c, d, b} : Finset (Fin n)) := by
        simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hvd
      exact kill_fork hno hac had hab hcd hbc.symm hbd.symm hvc' hvd' hwb' hvcd
        h01i.symm h31.symm h02i.symm h32.symm h30.symm hm1 hm2 hmc0 hmd0 hmb3
  have htri : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (i₀ i₁ i₂ i₃ i₄ : Fin 5),
      ({i₀, i₁, i₂, i₃, i₄} : Finset (Fin 5)) = Finset.univ →
      ({a, b} : Edge n) ∈ m i₀ → ({a, b} : Edge n) ∈ m i₁ →
      ({b, c} : Edge n) ∈ m i₂ → ({b, c} : Edge n) ∈ m i₃ →
      ({a, c} : Edge n) ∈ m i₄ → False := by
    intro a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ i₃ i₄ huniv hm0 hm1 hm2 hm3 hm4
    have hhit' : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({a, b, c, d} : Finset (Fin n)) := by rw [hXeq]; exact hhit
    rcases fin5_univ_distinct huniv with ⟨h01i, h02i, h03i, h04i, h12i, h13i, h14i, h23i, h24i, h34i⟩
    rcases type1_decomp hab hac had hbc hbd hcd (hgood i₀) (hhit' i₀) hm0 with ⟨u0, v0, hu0, hv0, huv0, hmc0, hmd0⟩
    rcases type1_decomp hbc hab.symm hbd hac.symm hcd had (hgood i₃)
        (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_left_comm]) hm3 with
      ⟨u3, _, hu3, _, _, hma3, _⟩
    rcases type1_decomp hac hab had hbc.symm hcd hbd (hgood i₄)
        (by intro e he; convert hhit' i₄ e he using 2; ext z; simp [or_left_comm]) hm4 with
      ⟨_, v4, _, hv4, _, _, hmd4⟩
    have hv4_0 : v4 ∉ ({a, b, c, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv4
    have hu0_v4 : u0 = v4 := kill_cross_eq hno hab hac had hbc hbd hcd hu0 hv4_0 h01i.symm h14i h04i hm1 hmc0 hmd4
    have hv0_bc : v0 ∉ ({b, c, a, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv0
    have hv4_bc : v4 ∉ ({b, c, a, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv4
    have hu3_v0 : u3 = v0 := kill_cross_eq hno hbc hab.symm hbd hac.symm hcd had hu3 hv0_bc h23i h02i.symm h03i.symm hm2 hma3 hmd0
    have hu3_v4 : u3 = v4 := kill_cross_eq hno hbc hab.symm hbd hac.symm hcd had hu3 hv4_bc h23i h24i h34i hm2 hma3 hmd4
    exact huv0 ((hu0_v4.trans hu3_v4.symm).trans hu3_v0)
  have hcyc_opp : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (i₀ i₁ i₂ i₃ : Fin 5), i₀ ≠ i₁ → i₀ ≠ i₂ → i₀ ≠ i₃ → i₁ ≠ i₂ → i₁ ≠ i₃ → i₂ ≠ i₃ →
      ({a, b} : Edge n) ∈ m i₀ → ({a, b} : Edge n) ∈ m i₁ →
      ({b, c} : Edge n) ∈ m i₂ → ({d, a} : Edge n) ∈ m i₃ → False := by
    intro a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ i₃ h01i h02i h03i h12i h13i h23i hm0 hm1 hm2 hm3
    have hhit' : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({a, b, c, d} : Finset (Fin n)) := by rw [hXeq]; exact hhit
    rcases type1_decomp hab hac had hbc hbd hcd (hgood i₀) (hhit' i₀) hm0 with ⟨u0, v0, hu0, hv0, huv0, hmc0, hmd0⟩
    rcases type1_decomp hbc hab.symm hbd hac.symm hcd had (hgood i₂)
        (by intro e he; convert hhit' i₂ e he using 2; ext z; simp [or_left_comm]) hm2 with
      ⟨_, v2, _, hv2, _, _, hmd2⟩
    rcases type1_decomp had.symm hbd.symm hcd.symm hab hac hbc (hgood i₃)
        (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) hm3 with
      ⟨_, v3, _, hv3, _, _, hmc3⟩
    have hv2' : v2 ∉ ({a, b, c, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv2
    have hv3' : v3 ∉ ({a, b, c, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv3
    have h1 : u0 = v2 := kill_cross_eq hno hab hac had hbc hbd hcd hu0 hv2' h01i.symm h12i h02i hm1 hmc0 hmd2
    have h2 : v3 = v0 := kill_cross_eq hno hab hac had hbc hbd hcd hv3' hv0 h13i h01i.symm h03i.symm hm1 hmc3 hmd0
    have h3 : v3 = v2 := kill_cross_eq hno hab hac had hbc hbd hcd hv3' hv2' h03i h02i h23i.symm hm0 hmc3 hmd2
    exact huv0 ((h1.trans h3.symm).trans h2)
  have hcyc_221 : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (i₀ i₁ i₂ i₃ i₄ : Fin 5),
      ({i₀, i₁, i₂, i₃, i₄} : Finset (Fin 5)) = Finset.univ →
      ({a, b} : Edge n) ∈ m i₀ → ({a, b} : Edge n) ∈ m i₁ →
      ({c, d} : Edge n) ∈ m i₂ → ({c, d} : Edge n) ∈ m i₃ →
      ({b, c} : Edge n) ∈ m i₄ → False := by
    intro a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ i₃ i₄ huniv hm0 hm1 hm2 hm3 hm4
    have hhit' : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({a, b, c, d} : Finset (Fin n)) := by rw [hXeq]; exact hhit
    rcases fin5_univ_distinct huniv with ⟨h01i, h02i, h03i, h04i, h12i, h13i, h14i, h23i, h24i, h34i⟩
    rcases type1_decomp hab hac had hbc hbd hcd (hgood i₀) (hhit' i₀) hm0 with ⟨u0, v0, hu0, hv0, huv0, hmc0, hmd0⟩
    rcases type1_decomp hcd hac.symm hbc.symm had.symm hbd.symm hab (hgood i₂)
        (by intro e he; convert hhit' i₂ e he using 2; ext z; simp [or_comm, or_left_comm]) hm2 with
      ⟨u2, v2, hu2, hv2, huv2, hma2, hmb2⟩
    rcases type1_decomp hcd hac.symm hbc.symm had.symm hbd.symm hab (hgood i₃)
        (by intro e he; convert hhit' i₃ e he using 2; ext z; simp [or_comm, or_left_comm]) hm3 with
      ⟨_, v3, _, hv3, _, _, hmb3⟩
    rcases type1_decomp hbc hab.symm hbd hac.symm hcd had (hgood i₄)
        (by intro e he; convert hhit' i₄ e he using 2; ext z; simp [or_left_comm]) hm4 with
      ⟨u4, v4, hu4, hv4, huv4, hma4, hmd4⟩
    have hv4_0 : v4 ∉ ({a, b, c, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv4
    have hu4_cd : u4 ∉ ({c, d, a, b} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hu4
    have hu2_bc : u2 ∉ ({b, c, a, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hu2
    have hv0_bc : v0 ∉ ({b, c, a, d} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv0
    have h_u0_v4 : u0 = v4 := kill_cross_eq hno hab hac had hbc hbd hcd hu0 hv4_0 h01i.symm h14i h04i hm1 hmc0 hmd4
    have h_u4_v3 : u4 = v3 := kill_cross_eq hno hcd hac.symm hbc.symm had.symm hbd.symm hab hu4_cd hv3 h24i h23i h34i.symm hm2 hma4 hmb3
    have h_u2_v0 : u2 = v0 := kill_cross_eq hno hbc hab.symm hbd hac.symm hcd had hu2_bc hv0_bc h24i.symm h04i.symm h02i.symm hm4 hma2 hmd0
    have hu2_cd : u2 ≠ a ∧ u2 ≠ b ∧ u2 ≠ c := by
      have := not_mem_X4 hu2_bc; exact ⟨this.2.2.1, this.1, this.2.1⟩
    have hv3_cd : v3 ≠ a ∧ v3 ≠ b ∧ v3 ≠ c := by
      have := not_mem_X4 (by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv3 : v3 ∉ ({a, b, c, d} : Finset (Fin n)))
      exact ⟨this.1, this.2.1, this.2.2.1⟩
    have hu0_cd : u0 ≠ a ∧ u0 ≠ b ∧ u0 ≠ c := by
      have := not_mem_X4 hu0; exact ⟨this.1, this.2.1, this.2.2.1⟩
    rcases kill_three_cross hno hab hac hbc hu2_cd hv3_cd hu0_cd h23i h02i.symm h03i.symm hma2 hmb3 hmc0 with
      heq | heq | heq
    · have h_u4_v2 : u4 = v2 := kill_cross_eq hno hcd hac.symm hbc.symm had.symm hbd.symm hab hu4_cd hv2 h34i h23i.symm h24i.symm hm3 hma4 hmb2
      exact huv2 ((heq.trans h_u4_v3.symm).trans h_u4_v2)
    · exact huv0 (heq.symm.trans h_u2_v0)
    · exact huv4 (h_u4_v3.trans (heq.trans h_u0_v4))
  let edgeOf : Fin 6 → Edge n := ![{x₀, x₁}, {x₀, x₂}, {x₀, x₃}, {x₁, x₂}, {x₁, x₃}, {x₂, x₃}]
  have hpick : ∀ i : Fin 5, ∃ t : Fin 6, edgeOf t ∈ m i := by
    intro i
    rcases hint i with ⟨d, hdm, hdsub⟩
    rcases int_edge_cases ((hgood i).2.1 d hdm) hdsub with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, hdm⟩
    · exact ⟨1, hdm⟩
    · exact ⟨2, hdm⟩
    · exact ⟨3, hdm⟩
    · exact ⟨4, hdm⟩
    · exact ⟨5, hdm⟩
  choose f hf using hpick
  have hf_mem : ∀ {i : Fin 5} {t : Fin 6}, f i = t → edgeOf t ∈ m i := fun h => h ▸ hf _
  have hle2 : ∀ t : Fin 6, (Finset.univ.filter (fun i : Fin 5 => f i = t)).card ≤ 2 := by
    intro t
    by_contra hgt
    rcases Finset.two_lt_card.mp (by omega : 2 < (Finset.univ.filter (fun i : Fin 5 => f i = t)).card) with
      ⟨i₀, h0, i₁, h1, i₂, h2, h01i, h02i, h12i⟩
    have hf0 := (Finset.mem_filter.mp h0).2
    have hf1 := (Finset.mem_filter.mp h1).2
    have hf2 := (Finset.mem_filter.mp h2).2
    fin_cases t
    · exact not_three_same_int hgood h01 h02 h03 h12 h13 h23 hhit hno h01i h02i h12i
        (hf_mem hf0) (hf_mem hf1) (hf_mem hf2)
    · exact not_three_same_int hgood h02 h01 h03 h12.symm h23 h13
        (fun i e he => by convert hhit i e he using 2; ext z; simp [or_left_comm]) hno h01i h02i h12i
        (hf_mem hf0) (hf_mem hf1) (hf_mem hf2)
    · exact not_three_same_int hgood h03 h01 h02 h13.symm h23.symm h12
        (fun i e he => by convert hhit i e he using 2; ext z; simp [or_comm, or_left_comm]) hno h01i h02i h12i
        (hf_mem hf0) (hf_mem hf1) (hf_mem hf2)
    · exact not_three_same_int hgood h12 h01.symm h13 h02.symm h23 h03
        (fun i e he => by convert hhit i e he using 2; ext z; simp [or_left_comm]) hno h01i h02i h12i
        (hf_mem hf0) (hf_mem hf1) (hf_mem hf2)
    · exact not_three_same_int hgood h13 h01.symm h12 h03.symm h23.symm h02
        (fun i e he => by convert hhit i e he using 2; ext z; simp [or_comm, or_left_comm]) hno h01i h02i h12i
        (hf_mem hf0) (hf_mem hf1) (hf_mem hf2)
    · exact not_three_same_int hgood h23 h02.symm h12.symm h03.symm h13.symm h01
        (fun i e he => by convert hhit i e he using 2; ext z; simp [or_comm, or_left_comm]) hno h01i h02i h12i
        (hf_mem hf0) (hf_mem hf1) (hf_mem hf2)
  let cnt : Fin 6 → ℕ := fun t => (Finset.univ.filter (fun i : Fin 5 => f i = t)).card
  have hsum : cnt 0 + cnt 1 + cnt 2 + cnt 3 + cnt 4 + cnt 5 = 5 := by
    have := Finset.card_eq_sum_card_fiberwise (f := f) (s := (Finset.univ : Finset (Fin 5)))
      (t := (Finset.univ : Finset (Fin 6))) (fun _ _ => Finset.mem_univ _)
    simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_six] at this
    exact this.symm
  have hpos_iff : ∀ t, 0 < cnt t ↔ ∃ i : Fin 5, f i = t := fun t => by
    simp [cnt, Finset.card_pos, Finset.Nonempty]
  have hns0 : ¬ (0 < cnt 0 ∧ 0 < cnt 1 ∧ 0 < cnt 2) := by
    rintro ⟨h0, h1, h2⟩
    rcases (hpos_iff 0).mp h0 with ⟨i₀, hi₀⟩
    rcases (hpos_iff 1).mp h1 with ⟨i₁, hi₁⟩
    rcases (hpos_iff 2).mp h2 with ⟨i₂, hi₂⟩
    exact hstar x₀ x₁ x₂ x₃ h01 h02 h03 h12 h13 h23 rfl i₀ i₁ i₂
      (fun h => by rw [h, hi₁] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₁; exact absurd hi₁ (by decide))
      (hf_mem hi₀) (hf_mem hi₁) (hf_mem hi₂)
  have hns1 : ¬ (0 < cnt 0 ∧ 0 < cnt 3 ∧ 0 < cnt 4) := by
    rintro ⟨h0, h1, h2⟩
    rcases (hpos_iff 0).mp h0 with ⟨i₀, hi₀⟩
    rcases (hpos_iff 3).mp h1 with ⟨i₁, hi₁⟩
    rcases (hpos_iff 4).mp h2 with ⟨i₂, hi₂⟩
    exact hstar x₁ x₀ x₂ x₃ h01.symm h12 h13 h02 h03 h23
      (by ext z; simp [or_left_comm]) i₀ i₁ i₂
      (fun h => by rw [h, hi₁] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₁; exact absurd hi₁ (by decide))
      (by rw [pair_comm]; exact hf_mem hi₀) (hf_mem hi₁) (hf_mem hi₂)
  have hns2 : ¬ (0 < cnt 1 ∧ 0 < cnt 3 ∧ 0 < cnt 5) := by
    rintro ⟨h0, h1, h2⟩
    rcases (hpos_iff 1).mp h0 with ⟨i₀, hi₀⟩
    rcases (hpos_iff 3).mp h1 with ⟨i₁, hi₁⟩
    rcases (hpos_iff 5).mp h2 with ⟨i₂, hi₂⟩
    exact hstar x₂ x₀ x₁ x₃ h02.symm h12.symm h23 h01 h03 h13
      (by ext z; simp [or_left_comm]) i₀ i₁ i₂
      (fun h => by rw [h, hi₁] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₁; exact absurd hi₁ (by decide))
      (by rw [pair_comm]; exact hf_mem hi₀) (by rw [pair_comm]; exact hf_mem hi₁) (hf_mem hi₂)
  have hns3 : ¬ (0 < cnt 2 ∧ 0 < cnt 4 ∧ 0 < cnt 5) := by
    rintro ⟨h0, h1, h2⟩
    rcases (hpos_iff 2).mp h0 with ⟨i₀, hi₀⟩
    rcases (hpos_iff 4).mp h1 with ⟨i₁, hi₁⟩
    rcases (hpos_iff 5).mp h2 with ⟨i₂, hi₂⟩
    exact hstar x₃ x₀ x₁ x₂ h03.symm h13.symm h23.symm h01 h02 h12
      (by ext z; simp [or_comm, or_left_comm]) i₀ i₁ i₂
      (fun h => by rw [h, hi₁] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₀; exact absurd hi₀ (by decide))
      (fun h => by rw [h, hi₂] at hi₁; exact absurd hi₁ (by decide))
      (by rw [pair_comm]; exact hf_mem hi₀) (by rw [pair_comm]; exact hf_mem hi₁) (by rw [pair_comm]; exact hf_mem hi₂)
  have hex2 : ∀ t, cnt t = 2 → ∃ i j : Fin 5, i ≠ j ∧ f i = t ∧ f j = t := by
    intro t ht
    rcases Finset.card_eq_two.mp ht with ⟨i, j, hij, hset⟩
    have hi : i ∈ Finset.univ.filter (fun k : Fin 5 => f k = t) := by rw [hset]; exact Finset.mem_insert_self i _
    have hj : j ∈ Finset.univ.filter (fun k : Fin 5 => f k = t) := by rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    exact ⟨i, j, hij, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  have hkill_opp : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (t0 t1 t2 : Fin 6), edgeOf t0 = {a, b} → edgeOf t1 = {b, c} → edgeOf t2 = {d, a} →
      ¬ (cnt t0 = 2 ∧ 0 < cnt t1 ∧ 0 < cnt t2) := by
    rintro a b c d hab hac had hbc hbd hcd hXeq t0 t1 t2 he0 he1 he2 ⟨hc0, hc1, hc2⟩
    rcases hex2 t0 hc0 with ⟨i₀, i₁, h01i, hf0, hf1⟩
    rcases (hpos_iff t1).mp hc1 with ⟨i₂, hf2⟩
    rcases (hpos_iff t2).mp hc2 with ⟨i₃, hf3⟩
    have ht01 : t0 ≠ t1 := by
      intro h; rw [h, he1] at he0
      have : a ∈ ({b, c} : Edge n) := he0 ▸ Finset.mem_insert_self a _
      simp [hab, hac] at this
    have ht02 : t0 ≠ t2 := by
      intro h; rw [h, he2] at he0
      have : b ∈ ({d, a} : Edge n) := he0 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
      simp [hbd, hab.symm] at this
    have ht12 : t1 ≠ t2 := by
      intro h; rw [h, he2] at he1
      have : b ∈ ({d, a} : Edge n) := he1 ▸ Finset.mem_insert_self b _
      simp [hbd, hab.symm] at this
    exact hcyc_opp a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ i₃ h01i
      (fun h => ht01 (hf0.symm.trans (h ▸ hf2))) (fun h => ht02 (hf0.symm.trans (h ▸ hf3)))
      (fun h => ht01 (hf1.symm.trans (h ▸ hf2))) (fun h => ht02 (hf1.symm.trans (h ▸ hf3)))
      (fun h => ht12 (hf2.symm.trans (h ▸ hf3)))
      (he0 ▸ hf_mem hf0) (he0 ▸ hf_mem hf1) (he1 ▸ hf_mem hf2) (he2 ▸ hf_mem hf3)
  have hkill_221_univ : ∀ t0 t1 t2 : Fin 6, t0 ≠ t1 → t0 ≠ t2 → t1 ≠ t2 →
      cnt t0 = 2 → cnt t1 = 2 → cnt t2 = 1 →
      ∃ i₀ i₁ i₂ i₃ i₄ : Fin 5,
        ({i₀, i₁, i₂, i₃, i₄} : Finset (Fin 5)) = Finset.univ ∧
        f i₀ = t0 ∧ f i₁ = t0 ∧ f i₂ = t1 ∧ f i₃ = t1 ∧ f i₄ = t2 := by
    intro t0 t1 t2 ht01 ht02 ht12 hc0 hc1 hc2
    rcases hex2 t0 hc0 with ⟨i₀, i₁, h01i, hf0, hf1⟩
    rcases hex2 t1 hc1 with ⟨i₂, i₃, h23i, hf2, hf3⟩
    rcases (hpos_iff t2).mp (by omega) with ⟨i₄, hf4⟩
    refine ⟨i₀, i₁, i₂, i₃, i₄, ?_, hf0, hf1, hf2, hf3, hf4⟩
    apply Finset.eq_univ_of_card
    have h02i : i₀ ≠ i₂ := fun h => ht01 (hf0.symm.trans (h ▸ hf2))
    have h03i : i₀ ≠ i₃ := fun h => ht01 (hf0.symm.trans (h ▸ hf3))
    have h04i : i₀ ≠ i₄ := fun h => ht02 (hf0.symm.trans (h ▸ hf4))
    have h12i : i₁ ≠ i₂ := fun h => ht01 (hf1.symm.trans (h ▸ hf2))
    have h13i : i₁ ≠ i₃ := fun h => ht01 (hf1.symm.trans (h ▸ hf3))
    have h14i : i₁ ≠ i₄ := fun h => ht02 (hf1.symm.trans (h ▸ hf4))
    have h24i : i₂ ≠ i₄ := fun h => ht12 (hf2.symm.trans (h ▸ hf4))
    have h34i : i₃ ≠ i₄ := fun h => ht12 (hf3.symm.trans (h ▸ hf4))
    simp [Finset.card_insert_of_notMem, h01i, h02i, h03i, h04i, h12i, h13i, h14i, h23i, h24i, h34i]
  have hkill_221 : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (t0 t1 t2 : Fin 6), t0 ≠ t1 → t0 ≠ t2 → t1 ≠ t2 →
      edgeOf t0 = {a, b} → edgeOf t1 = {c, d} → edgeOf t2 = {b, c} →
      cnt t0 = 2 ∧ cnt t1 = 2 ∧ cnt t2 = 1 → False := by
    rintro a b c d hab hac had hbc hbd hcd hXeq t0 t1 t2 h01t h02t h12t he0 he1 he2 ⟨hc0, hc1, hc2⟩
    rcases hkill_221_univ t0 t1 t2 h01t h02t h12t hc0 hc1 hc2 with ⟨i₀, i₁, i₂, i₃, i₄, hu, hf0, hf1, hf2, hf3, hf4⟩
    exact hcyc_221 a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ i₃ i₄ hu
      (he0 ▸ hf_mem hf0) (he0 ▸ hf_mem hf1) (he1 ▸ hf_mem hf2) (he1 ▸ hf_mem hf3) (he2 ▸ hf_mem hf4)
  have hkill_tri : ∀ (a b c d : Fin n),
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
      ∀ (t0 t1 t2 : Fin 6), t0 ≠ t1 → t0 ≠ t2 → t1 ≠ t2 →
      edgeOf t0 = {a, b} → edgeOf t1 = {b, c} → edgeOf t2 = {a, c} →
      cnt t0 = 2 ∧ cnt t1 = 2 ∧ cnt t2 = 1 → False := by
    rintro a b c d hab hac had hbc hbd hcd hXeq t0 t1 t2 h01t h02t h12t he0 he1 he2 ⟨hc0, hc1, hc2⟩
    rcases hkill_221_univ t0 t1 t2 h01t h02t h12t hc0 hc1 hc2 with ⟨i₀, i₁, i₂, i₃, i₄, hu, hf0, hf1, hf2, hf3, hf4⟩
    exact htri a b c d hab hac had hbc hbd hcd hXeq i₀ i₁ i₂ i₃ i₄ hu
      (he0 ▸ hf_mem hf0) (he0 ▸ hf_mem hf1) (he1 ▸ hf_mem hf2) (he1 ▸ hf_mem hf3) (he2 ▸ hf_mem hf4)
  let c0 : Fin 3 := ⟨cnt 0, Nat.lt_succ_of_le (hle2 0)⟩
  let c1 : Fin 3 := ⟨cnt 1, Nat.lt_succ_of_le (hle2 1)⟩
  let c2 : Fin 3 := ⟨cnt 2, Nat.lt_succ_of_le (hle2 2)⟩
  let c3 : Fin 3 := ⟨cnt 3, Nat.lt_succ_of_le (hle2 3)⟩
  let c4 : Fin 3 := ⟨cnt 4, Nat.lt_succ_of_le (hle2 4)⟩
  let c5 : Fin 3 := ⟨cnt 5, Nat.lt_succ_of_le (hle2 5)⟩
  have hcl := counts_6_classify c0 c1 c2 c3 c4 c5 hsum hns0 hns1 hns2 hns3
    (hkill_opp x₀ x₁ x₂ x₃ h01 h02 h03 h12 h13 h23 rfl 0 3 2 rfl rfl (pair_comm _ _))
    (hkill_opp x₀ x₁ x₃ x₂ h01 h03 h02 h13 h12 h23.symm (by ext z; simp [or_comm, or_left_comm]) 0 4 1 rfl rfl (pair_comm _ _))
    (hkill_opp x₀ x₂ x₁ x₃ h02 h01 h03 h12.symm h23 h13 (by ext z; simp [or_left_comm]) 1 3 2 rfl (pair_comm _ _) (pair_comm _ _))
    (hkill_opp x₀ x₂ x₃ x₁ h02 h03 h01 h23 h12.symm h13.symm (by ext z; simp [or_comm, or_left_comm]) 1 5 0 rfl rfl (pair_comm _ _))
    (hkill_opp x₀ x₃ x₁ x₂ h03 h01 h02 h13.symm h23.symm h12 (by ext z; simp [or_comm, or_left_comm]) 2 4 1 rfl (pair_comm _ _) (pair_comm _ _))
    (hkill_opp x₀ x₃ x₂ x₁ h03 h02 h01 h23.symm h13.symm h12.symm (by ext z; simp [or_comm, or_left_comm]) 2 5 0 rfl (pair_comm _ _) (pair_comm _ _))
    (hkill_opp x₁ x₂ x₀ x₃ h12 h01.symm h13 h02.symm h23 h03 (by ext z; simp [or_left_comm]) 3 1 4 rfl (pair_comm _ _) (pair_comm _ _))
    (hkill_opp x₁ x₂ x₃ x₀ h12 h13 h01.symm h23 h02.symm h03.symm (by ext z; simp [or_comm, or_left_comm]) 3 5 0 rfl rfl rfl)
    (hkill_opp x₁ x₃ x₀ x₂ h13 h01.symm h12 h03.symm h23.symm h02 (by ext z; simp [or_comm, or_left_comm]) 4 2 3 rfl (pair_comm _ _) (pair_comm _ _))
    (hkill_opp x₁ x₃ x₂ x₀ h13 h12 h01.symm h23.symm h03.symm h02.symm (by ext z; simp [or_comm, or_left_comm]) 4 5 0 rfl (pair_comm _ _) rfl)
    (hkill_opp x₂ x₃ x₀ x₁ h23 h02.symm h12.symm h03.symm h13.symm h01 (by ext z; simp [or_comm, or_left_comm]) 5 2 3 rfl (pair_comm _ _) rfl)
    (hkill_opp x₂ x₃ x₁ x₀ h23 h12.symm h02.symm h13.symm h03.symm h01.symm (by ext z; simp [or_comm, or_left_comm]) 5 4 1 rfl (pair_comm _ _) rfl)
  rcases hcl with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hkill_221 x₀ x₁ x₂ x₃ h01 h02 h03 h12 h13 h23 rfl 0 5 3 (by decide) (by decide) (by decide) rfl rfl rfl h
  · exact hkill_221 x₀ x₁ x₃ x₂ h01 h03 h02 h13 h12 h23.symm (by ext z; simp [or_comm, or_left_comm]) 0 5 4 (by decide) (by decide) (by decide) rfl (pair_comm _ _) rfl h
  · exact hkill_221 x₁ x₀ x₂ x₃ h01.symm h12 h13 h02 h03 h23 (by ext z; simp [or_left_comm]) 0 5 1 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_221 x₁ x₀ x₃ x₂ h01.symm h13 h12 h03 h02 h23.symm (by ext z; simp [or_comm, or_left_comm]) 0 5 2 (by decide) (by decide) (by decide) (pair_comm _ _) (pair_comm _ _) rfl h
  · exact hkill_221 x₀ x₂ x₁ x₃ h02 h01 h03 h12.symm h23 h13 (by ext z; simp [or_left_comm]) 1 4 3 (by decide) (by decide) (by decide) rfl rfl (pair_comm _ _) h
  · exact hkill_221 x₀ x₂ x₃ x₁ h02 h03 h01 h23 h12.symm h13.symm (by ext z; simp [or_comm, or_left_comm]) 1 4 5 (by decide) (by decide) (by decide) rfl (pair_comm _ _) rfl h
  · exact hkill_221 x₂ x₀ x₁ x₃ h02.symm h12.symm h23 h01 h03 h13 (by ext z; simp [or_left_comm]) 1 4 0 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_221 x₂ x₀ x₃ x₁ h02.symm h23 h12.symm h03 h01 h13.symm (by ext z; simp [or_comm, or_left_comm]) 1 4 2 (by decide) (by decide) (by decide) (pair_comm _ _) (pair_comm _ _) rfl h
  · exact hkill_221 x₀ x₃ x₁ x₂ h03 h01 h02 h13.symm h23.symm h12 (by ext z; simp [or_comm, or_left_comm]) 2 3 4 (by decide) (by decide) (by decide) rfl rfl (pair_comm _ _) h
  · exact hkill_221 x₀ x₃ x₂ x₁ h03 h02 h01 h23.symm h13.symm h12.symm (by ext z; simp [or_comm, or_left_comm]) 2 3 5 (by decide) (by decide) (by decide) rfl (pair_comm _ _) (pair_comm _ _) h
  · exact hkill_221 x₃ x₀ x₁ x₂ h03.symm h13.symm h23.symm h01 h02 h12 (by ext z; simp [or_comm, or_left_comm]) 2 3 0 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_221 x₃ x₀ x₂ x₁ h03.symm h23.symm h13.symm h02 h01 h12.symm (by ext z; simp [or_comm, or_left_comm]) 2 3 1 (by decide) (by decide) (by decide) (pair_comm _ _) (pair_comm _ _) rfl h
  · exact hkill_tri x₀ x₁ x₂ x₃ h01 h02 h03 h12 h13 h23 rfl 0 3 1 (by decide) (by decide) (by decide) rfl rfl rfl h
  · exact hkill_tri x₁ x₀ x₂ x₃ h01.symm h12 h13 h02 h03 h23 (by ext z; simp [or_left_comm]) 0 1 3 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_tri x₀ x₂ x₁ x₃ h02 h01 h03 h12.symm h23 h13 (by ext z; simp [or_left_comm]) 1 3 0 (by decide) (by decide) (by decide) rfl (pair_comm _ _) rfl h
  · exact hkill_tri x₀ x₁ x₃ x₂ h01 h03 h02 h13 h12 h23.symm (by ext z; simp [or_comm, or_left_comm]) 0 4 2 (by decide) (by decide) (by decide) rfl rfl rfl h
  · exact hkill_tri x₁ x₀ x₃ x₂ h01.symm h13 h12 h03 h02 h23.symm (by ext z; simp [or_comm, or_left_comm]) 0 2 4 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_tri x₀ x₃ x₁ x₂ h03 h01 h02 h13.symm h23.symm h12 (by ext z; simp [or_comm, or_left_comm]) 2 4 0 (by decide) (by decide) (by decide) rfl (pair_comm _ _) rfl h
  · exact hkill_tri x₀ x₂ x₃ x₁ h02 h03 h01 h23 h12.symm h13.symm (by ext z; simp [or_comm, or_left_comm]) 1 5 2 (by decide) (by decide) (by decide) rfl rfl rfl h
  · exact hkill_tri x₂ x₀ x₃ x₁ h02.symm h23 h12.symm h03 h01 h13.symm (by ext z; simp [or_comm, or_left_comm]) 1 2 5 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_tri x₀ x₃ x₂ x₁ h03 h02 h01 h23.symm h13.symm h12.symm (by ext z; simp [or_comm, or_left_comm]) 2 5 1 (by decide) (by decide) (by decide) rfl (pair_comm _ _) rfl h
  · exact hkill_tri x₁ x₂ x₃ x₀ h12 h13 h01.symm h23 h02.symm h03.symm (by ext z; simp [or_comm, or_left_comm]) 3 5 4 (by decide) (by decide) (by decide) rfl rfl rfl h
  · exact hkill_tri x₂ x₁ x₃ x₀ h12.symm h23 h02.symm h13 h01.symm h03.symm (by ext z; simp [or_comm, or_left_comm]) 3 4 5 (by decide) (by decide) (by decide) (pair_comm _ _) rfl rfl h
  · exact hkill_tri x₁ x₃ x₂ x₀ h13 h12 h01.symm h23.symm h03.symm h02.symm (by ext z; simp [or_comm, or_left_comm]) 4 5 3 (by decide) (by decide) (by decide) rfl (pair_comm _ _) rfl h

lemma case2A {n : ℕ} {m : Fin 5 → Matching n} (hgood : ∀ i, Good (m i))
    {x₀ x₁ x₂ x₃ : Fin n}
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h03 : x₀ ≠ x₃)
    (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    (hhit : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hm0 : ({x₀, x₁} : Edge n) ∈ m 0)
    (_hm1_noint : ∀ e ∈ m 1, ¬ (e ⊆ ({x₀, x₁, x₂, x₃} : Finset (Fin n))))
    {y₁ y₂ y₃ : Fin n}
    (hy1X : y₁ ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hy2X : y₂ ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hy3X : y₃ ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))
    (hy12 : y₁ ≠ y₂) (hy13 : y₁ ≠ y₃) (hy23 : y₂ ≠ y₃)
    (hm1_1 : ({x₁, y₁} : Edge n) ∈ m 1)
    (hm1_2 : ({x₂, y₂} : Edge n) ∈ m 1)
    (hm1_3 : ({x₃, y₃} : Edge n) ∈ m 1) :
    Rainbow 5 m := by
  by_contra hno
  let X : Finset (Fin n) := {x₀, x₁, x₂, x₃}
  have hX4 : X.card = 4 := by
    simp [X, Finset.card_insert_of_notMem, h01, h02, h03, h12, h13, h23]
  rcases type1_decomp h01 h02 h03 h12 h13 h23 (hgood 0) (hhit 0) hm0 with ⟨z₂, z₃, hz2X, hz3X, hz23, hm0_2, hm0_3⟩
  have hcross2 : ∀ c : Fin 5, c ≠ 0 → c ≠ 1 → ∀ u : Fin n, u ∉ X → ({x₂, u} : Edge n) ∈ m c → u = y₃ := by
    intro c hc0 hc1 u huX hmc
    exact kill_cross_eq hno h01 h02 h03 h12 h13 h23 huX hy3X hc0.symm (by decide) hc1 hm0 hmc hm1_3
  have hcross3 : ∀ c : Fin 5, c ≠ 0 → c ≠ 1 → ∀ v : Fin n, v ∉ X → ({x₃, v} : Edge n) ∈ m c → v = y₂ := by
    intro c hc0 hc1 v hvX hmc
    exact (kill_cross_eq hno h01 h02 h03 h12 h13 h23 hy2X hvX (by decide) hc0.symm hc1.symm hm0 hm1_2 hmc).symm
  have htwo23 : ∀ (c1 c2 c3 : Fin 5),
      c1 ≠ 0 → c1 ≠ 1 → c2 ≠ 0 → c2 ≠ 1 → c3 ≠ 0 → c3 ≠ 1 →
      c1 ≠ c2 → c1 ≠ c3 → c2 ≠ c3 →
      ({x₂, x₃} : Edge n) ∈ m c1 → ({x₂, x₃} : Edge n) ∈ m c2 → False := by
    intro c1 c2 c3 hc10 hc11 hc20 hc21 hc30 hc31 h12c h13c h23c h23_1 h23_2
    rcases type1_decomp h23 h02.symm h12.symm h03.symm h13.symm h01 (hgood c1)
        (by intro e he; convert hhit c1 e he using 2; ext z; simp [or_comm, or_left_comm]) h23_1 with
      ⟨u1, v1, hu1, hv1, huv1, hm1_0, hm1_1'⟩
    rcases type1_decomp h23 h02.symm h12.symm h03.symm h13.symm h01 (hgood c2)
        (by intro e he; convert hhit c2 e he using 2; ext z; simp [or_comm, or_left_comm]) h23_2 with
      ⟨u2, v2, hu2, hv2, huv2, hm2_0, hm2_1'⟩
    have hu1X : u1 ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hu1
    have hv2X : v2 ∉ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv2
    have hy1' : y₁ ∉ ({x₂, x₃, x₀, x₁} : Finset (Fin n)) := by
      simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy1X
    have hu1_y1' : u1 = y₁ := kill_cross_eq hno h23 h02.symm h12.symm h03.symm h13.symm h01 hu1 hy1' h12c.symm hc21 hc11 h23_2 hm1_0 hm1_1
    have hu2_y1' : u2 = y₁ := kill_cross_eq hno h23 h02.symm h12.symm h03.symm h13.symm h01 hu2 hy1' h12c hc11 hc21 h23_1 hm2_0 hm1_1
    have hv2_ne_y1 : v2 ≠ y₁ := fun h => huv2 (hu2_y1'.trans h.symm)
    have hno_c3_both : ∀ (w2 w3 : Fin n), w2 ∉ X → w3 ∉ X →
        ({x₂, w2} : Edge n) ∈ m c3 → ({x₃, w3} : Edge n) ∈ m c3 → False := by
      intro w2 w3 hw2 hw3 h32 h33
      have hw2_eq : w2 = y₃ := hcross2 c3 hc30 hc31 w2 hw2 h32
      have hw3_eq : w3 = y₂ := hcross3 c3 hc30 hc31 w3 hw3 h33
      subst w2; subst w3
      have hu1_3 : u1 ≠ x₀ ∧ u1 ≠ x₁ ∧ u1 ≠ x₂ := by have := not_mem_X4 hu1X; exact ⟨this.1, this.2.1, this.2.2.1⟩
      have hv2_3 : v2 ≠ x₀ ∧ v2 ≠ x₁ ∧ v2 ≠ x₂ := by have := not_mem_X4 hv2X; exact ⟨this.1, this.2.1, this.2.2.1⟩
      have hy3_3 : y₃ ≠ x₀ ∧ y₃ ≠ x₁ ∧ y₃ ≠ x₂ := by have := not_mem_X4 hy3X; exact ⟨this.1, this.2.1, this.2.2.1⟩
      have hv2_y3 : v2 = y₃ := by
        rcases kill_three_cross hno h01 h02 h12 hu1_3 hv2_3 hy3_3 h12c h13c h23c hm1_0 hm2_1' h32 with h | h | h
        · exact absurd (hu1_y1'.symm.trans h) hv2_ne_y1.symm
        · exact absurd (hu1_y1'.symm.trans h) hy13
        · exact h
      have hu1_3' : u1 ≠ x₀ ∧ u1 ≠ x₁ ∧ u1 ≠ x₃ := by have := not_mem_X4 hu1X; exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hv2_3' : v2 ≠ x₀ ∧ v2 ≠ x₁ ∧ v2 ≠ x₃ := by have := not_mem_X4 hv2X; exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hy2_3' : y₂ ≠ x₀ ∧ y₂ ≠ x₁ ∧ y₂ ≠ x₃ := by have := not_mem_X4 hy2X; exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hv2_y2 : v2 = y₂ := by
        rcases kill_three_cross hno h01 h03 h13 hu1_3' hv2_3' hy2_3' h12c h13c h23c hm1_0 hm2_1' h33 with h | h | h
        · exact absurd (hu1_y1'.symm.trans h) hv2_ne_y1.symm
        · exact absurd (hu1_y1'.symm.trans h) hy12
        · exact h
      exact hy23 (hv2_y2.symm.trans hv2_y3)
    by_cases hint3 : ∃ d ∈ m c3, d ⊆ X
    · rcases hint3 with ⟨d, hdm, hdsub⟩
      rcases int_edge_cases ((hgood c3).2.1 d hdm) hdsub with rfl | rfl | rfl | rfl | rfl | rfl
      · rcases type1_decomp h01 h02 h03 h12 h13 h23 (hgood c3) (hhit c3) hdm with ⟨w2, w3, hw2, hw3, _, h32, h33⟩
        exact hno_c3_both w2 w3 hw2 hw3 h32 h33
      · have hv2_02 : v2 ∉ ({x₀, x₂, x₁, x₃} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv2X
        have hy3_02 : y₃ ∉ ({x₀, x₂, x₁, x₃} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy3X
        have hv2_y3 : v2 = y₃ := kill_cross_eq hno h02 h01 h03 h12.symm h23 h13 hv2_02 hy3_02 h23c.symm hc31 hc21 hdm hm2_1' hm1_3
        have hu1_3 : u1 ≠ x₀ ∧ u1 ≠ x₁ ∧ u1 ≠ x₂ := by have := not_mem_X4 hu1X; exact ⟨this.1, this.2.1, this.2.2.1⟩
        have hv2_3 : v2 ≠ x₀ ∧ v2 ≠ x₁ ∧ v2 ≠ x₂ := by have := not_mem_X4 hv2X; exact ⟨this.1, this.2.1, this.2.2.1⟩
        have hy2_3 : y₂ ≠ x₀ ∧ y₂ ≠ x₁ ∧ y₂ ≠ x₂ := by have := not_mem_X4 hy2X; exact ⟨this.1, this.2.1, this.2.2.1⟩
        rcases kill_three_cross hno h01 h02 h12 hu1_3 hv2_3 hy2_3 h12c hc11 hc21 hm1_0 hm2_1' hm1_2 with h | h | h
        · exact absurd (hu1_y1'.symm.trans h) hv2_ne_y1.symm
        · exact absurd (hu1_y1'.symm.trans h) hy12
        · exact hy23 (h.symm.trans hv2_y3)
      · have hv2_03 : v2 ∉ ({x₀, x₃, x₁, x₂} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv2X
        have hy2_03 : y₂ ∉ ({x₀, x₃, x₁, x₂} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy2X
        have hv2_y2 : v2 = y₂ := kill_cross_eq hno h03 h01 h02 h13.symm h23.symm h12 hv2_03 hy2_03 h23c.symm hc31 hc21 hdm hm2_1' hm1_2
        have hu1_3 : u1 ≠ x₀ ∧ u1 ≠ x₁ ∧ u1 ≠ x₃ := by have := not_mem_X4 hu1X; exact ⟨this.1, this.2.1, this.2.2.2⟩
        have hv2_3 : v2 ≠ x₀ ∧ v2 ≠ x₁ ∧ v2 ≠ x₃ := by have := not_mem_X4 hv2X; exact ⟨this.1, this.2.1, this.2.2.2⟩
        have hy3_3 : y₃ ≠ x₀ ∧ y₃ ≠ x₁ ∧ y₃ ≠ x₃ := by have := not_mem_X4 hy3X; exact ⟨this.1, this.2.1, this.2.2.2⟩
        rcases kill_three_cross hno h01 h03 h13 hu1_3 hv2_3 hy3_3 h12c hc11 hc21 hm1_0 hm2_1' hm1_3 with h | h | h
        · exact absurd (hu1_y1'.symm.trans h) hv2_ne_y1.symm
        · exact absurd (hu1_y1'.symm.trans h) hy13
        · exact hy23 (hv2_y2.symm.trans h)
      · have hu1_12 : u1 ∉ ({x₁, x₂, x₀, x₃} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hu1X
        have hy3_12 : y₃ ∉ ({x₁, x₂, x₀, x₃} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy3X
        have h_u1_y3 : u1 = y₃ := kill_cross_eq hno h12 h01.symm h13 h02.symm h23 h03 hu1_12 hy3_12 h13c.symm hc31 hc11 hdm hm1_0 hm1_3
        exact hy13 (hu1_y1'.symm.trans h_u1_y3)
      · have hu1_13 : u1 ∉ ({x₁, x₃, x₀, x₂} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hu1X
        have hy2_13 : y₂ ∉ ({x₁, x₃, x₀, x₂} : Finset (Fin n)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy2X
        have h_u1_y2 : u1 = y₂ := kill_cross_eq hno h13 h01.symm h12 h03.symm h23.symm h02 hu1_13 hy2_13 h13c.symm hc31 hc11 hdm hm1_0 hm1_2
        exact hy12 (hu1_y1'.symm.trans h_u1_y2)
      · exact not_three_same_int hgood h23 h02.symm h12.symm h03.symm h13.symm h01
          (fun i e he => by convert hhit i e he using 2; ext z; simp [or_comm, or_left_comm])
          hno h12c h13c h23c h23_1 h23_2 hdm
    · push Not at hint3
      rcases type0_decomp hX4 (hgood c3) (hhit c3) hint3 with ⟨miss, hmissX, hcov⟩
      simp only [X, Finset.mem_insert, Finset.mem_singleton] at hmissX
      rcases hmissX with hms | hms | hms | hms
      · rcases hcov x₂ (by simp [X]) (hms ▸ h02.symm) with ⟨w2, hw2, h32⟩
        rcases hcov x₃ (by simp [X]) (hms ▸ h03.symm) with ⟨w3, hw3, h33⟩
        exact hno_c3_both w2 w3 hw2 hw3 h32 h33
      · rcases hcov x₂ (by simp [X]) (hms ▸ h12.symm) with ⟨w2, hw2, h32⟩
        rcases hcov x₃ (by simp [X]) (hms ▸ h13.symm) with ⟨w3, hw3, h33⟩
        exact hno_c3_both w2 w3 hw2 hw3 h32 h33
      · rcases hcov x₀ (by simp [X]) (hms ▸ h02) with ⟨w0, hw0, h30⟩
        rcases hcov x₁ (by simp [X]) (hms ▸ h12) with ⟨w1, hw1, h31⟩
        have hw01 : w0 ≠ w1 := (good_pair_disj_ne (hgood c3) h30 h31 h01 (not_mem_X4 hw1).1.symm).2
        have hw0_cd : w0 ∉ ({x₂, x₃, x₀, x₁} : Finset (Fin n)) := by
          simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw0
        have hw1_cd : w1 ∉ ({x₂, x₃, x₀, x₁} : Finset (Fin n)) := by
          simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw1
        have h_w0_y1 : w0 = y₁ := kill_cross_eq hno h23 h02.symm h12.symm h03.symm h13.symm h01 hw0_cd hy1' h13c hc11 hc31 h23_1 h30 hm1_1
        have h_u1_w1 : u1 = w1 := kill_cross_eq hno h23 h02.symm h12.symm h03.symm h13.symm h01 hu1 hw1_cd h12c.symm h23c h13c h23_2 hm1_0 h31
        exact hw01 (h_w0_y1.trans (hu1_y1'.symm.trans h_u1_w1))
      · rcases hcov x₀ (by simp [X]) (hms ▸ h03) with ⟨w0, hw0, h30⟩
        rcases hcov x₁ (by simp [X]) (hms ▸ h13) with ⟨w1, hw1, h31⟩
        have hw01 : w0 ≠ w1 := (good_pair_disj_ne (hgood c3) h30 h31 h01 (not_mem_X4 hw1).1.symm).2
        have hw0_cd : w0 ∉ ({x₂, x₃, x₀, x₁} : Finset (Fin n)) := by
          simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw0
        have hw1_cd : w1 ∉ ({x₂, x₃, x₀, x₁} : Finset (Fin n)) := by
          simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw1
        have h_w0_y1 : w0 = y₁ := kill_cross_eq hno h23 h02.symm h12.symm h03.symm h13.symm h01 hw0_cd hy1' h13c hc11 hc31 h23_1 h30 hm1_1
        have h_u1_w1 : u1 = w1 := kill_cross_eq hno h23 h02.symm h12.symm h03.symm h13.symm h01 hu1 hw1_cd h12c.symm h23c h13c h23_2 hm1_0 h31
        exact hw01 (h_w0_y1.trans (hu1_y1'.symm.trans h_u1_w1))
  have hno_cross_side : ∀ (xA xB yA yB zA zB : Fin n),
      x₀ ≠ xA → x₀ ≠ xB → x₁ ≠ xA → x₁ ≠ xB → xA ≠ xB →
      ({x₀, x₁, xA, xB} : Finset (Fin n)) = X →
      yA ∉ X → yB ∉ X → y₁ ≠ yA → y₁ ≠ yB → yA ≠ yB →
      zA ∉ X → zB ∉ X → zA ≠ zB →
      ({xA, zA} : Edge n) ∈ m 0 → ({xB, zB} : Edge n) ∈ m 0 →
      ({xA, yA} : Edge n) ∈ m 1 → ({xB, yB} : Edge n) ∈ m 1 →
      (∀ c : Fin 5, c ≠ 0 → c ≠ 1 → ∀ u : Fin n, u ∉ X → ({xA, u} : Edge n) ∉ m c) → False := by
    intro xA xB yA yB zA zB h0A h0B h1A h1B hAB hXeq hyAX hyBX hy1A hy1B hyAB hzAX hzBX hzAB hm0A hm0B hm1A hm1B hnoA
    have hhit' : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rw [hXeq]; exact hhit
    have hcrossB : ∀ c : Fin 5, c ≠ 0 → c ≠ 1 → ∀ v : Fin n, v ∉ X → ({xB, v} : Edge n) ∈ m c → v = yA := by
      intro c hc0 hc1 v hvX hmc
      have hyAX' : yA ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rwa [hXeq]
      have hvX' : v ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rwa [hXeq]
      exact (kill_cross_eq hno h01 h0A h0B h1A h1B hAB hyAX' hvX' (by decide) hc0.symm hc1.symm hm0 hm1A hmc).symm
    have hno_twoAB : ∀ c1 c2 : Fin 5, c1 ≠ 0 → c1 ≠ 1 → c2 ≠ 0 → c2 ≠ 1 → c1 ≠ c2 →
        ({xA, xB} : Edge n) ∈ m c1 → ({xA, xB} : Edge n) ∈ m c2 → False := by
      intro c1 c2 hc10 hc11 hc20 hc21 h12c h1 h2
      rcases fin5_other_one c1 c2 hc10 hc11 hc20 hc21 h12c with ⟨c3, hc30, hc31, h13c, h23c⟩
      have heqAB : ({xA, xB} : Edge n) = {x₂, x₃} := by
        have hA : xA ∈ ({x₂, x₃} : Finset (Fin n)) := by
          have : xA ∈ X := hXeq ▸ (by simp)
          simp only [X, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h | h | h
          · exact absurd h.symm h0A
          · exact absurd h.symm h1A
          · rw [h]; exact Finset.mem_insert_self _ _
          · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        have hB : xB ∈ ({x₂, x₃} : Finset (Fin n)) := by
          have : xB ∈ X := hXeq ▸ (by simp)
          simp only [X, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with h | h | h | h
          · exact absurd h.symm h0B
          · exact absurd h.symm h1B
          · rw [h]; exact Finset.mem_insert_self _ _
          · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rcases Finset.mem_insert.mp hA with hA' | hA' <;> rcases Finset.mem_insert.mp hB with hB' | hB'
        · exact absurd (hA'.trans hB'.symm) hAB
        · rw [hA', Finset.mem_singleton.mp hB']
        · rw [Finset.mem_singleton.mp hA', hB', pair_comm]
        · exact absurd ((Finset.mem_singleton.mp hA').trans (Finset.mem_singleton.mp hB').symm) hAB
      rw [heqAB] at h1 h2
      exact htwo23 c1 c2 c3 hc10 hc11 hc20 hc21 hc30 hc31 h12c h13c.symm h23c.symm h1 h2
    have hclassify : ∀ c : Fin 5, c ≠ 0 → c ≠ 1 →
        ({xA, xB} : Edge n) ∈ m c ∨
        (({x₀, xA} : Edge n) ∈ m c ∧ ({xB, yA} : Edge n) ∈ m c) ∨
        (∃ w0 : Fin n, w0 ∉ X ∧ ({x₀, w0} : Edge n) ∈ m c ∧ ({xB, yA} : Edge n) ∈ m c ∧
          (({x₁, xA} : Edge n) ∈ m c ∨ ∃ w1 : Fin n, w1 ∉ X ∧ w0 ≠ w1 ∧ ({x₁, w1} : Edge n) ∈ m c)) := by
      intro c hc0 hc1
      by_cases hintc : ∃ d ∈ m c, d ⊆ X
      · rcases hintc with ⟨d, hdm, hdsub⟩
        rw [← hXeq] at hdsub
        rcases int_edge_cases ((hgood c).2.1 d hdm) hdsub with rfl | rfl | rfl | rfl | rfl | rfl
        · rcases type1_decomp h01 h0A h0B h1A h1B hAB (hgood c) (hhit' c) hdm with ⟨wA, _, hwA, _, _, hmA, _⟩
          exact False.elim (hnoA c hc0 hc1 wA (by rwa [← hXeq]) hmA)
        · rcases type1_decomp h0A h01 h0B h1A.symm hAB h1B (hgood c)
              (by intro e he; convert hhit' c e he using 2; ext z; simp [or_left_comm]) hdm with
            ⟨_, wB, _, hwB, _, _, hmB⟩
          have hwBX : wB ∉ X := by rw [← hXeq]; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwB
          have hwB_eq : wB = yA := hcrossB c hc0 hc1 wB hwBX hmB
          exact Or.inr (Or.inl ⟨hdm, hwB_eq ▸ hmB⟩)
        · rcases type1_decomp h0B h01 h0A h1B.symm hAB.symm h1A (hgood c)
              (by intro e he; convert hhit' c e he using 2; ext z; simp [or_comm, or_left_comm]) hdm with
            ⟨_, wA, _, hwA, _, _, hmA⟩
          exact False.elim (hnoA c hc0 hc1 wA (by rw [← hXeq]; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwA) hmA)
        · rcases type1_decomp h1A h01.symm h1B h0A.symm hAB h0B (hgood c)
              (by intro e he; convert hhit' c e he using 2; ext z; simp [or_left_comm]) hdm with
            ⟨w0, wB, hw0, hwB, _, hm0c, hmBc⟩
          have hw0X : w0 ∉ X := by rw [← hXeq]; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw0
          have hwBX : wB ∉ X := by rw [← hXeq]; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwB
          have hwB_eq : wB = yA := hcrossB c hc0 hc1 wB hwBX hmBc
          exact Or.inr (Or.inr ⟨w0, hw0X, hm0c, hwB_eq ▸ hmBc, Or.inl hdm⟩)
        · rcases type1_decomp h1B h01.symm h1A h0B.symm hAB.symm h0A (hgood c)
              (by intro e he; convert hhit' c e he using 2; ext z; simp [or_comm, or_left_comm]) hdm with
            ⟨_, wA, _, hwA, _, _, hmA⟩
          exact False.elim (hnoA c hc0 hc1 wA (by rw [← hXeq]; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hwA) hmA)
        · exact Or.inl hdm
      · push Not at hintc
        rcases type0_decomp hX4 (hgood c) (hhit c) hintc with ⟨miss, hmissX, hcov⟩
        rw [← hXeq] at hmissX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmissX
        rcases hmissX with hms | hms | hms | hms
        · rcases hcov xA (hXeq ▸ by simp) (hms ▸ h0A.symm) with ⟨wA, hwA, hmA⟩
          exact False.elim (hnoA c hc0 hc1 wA hwA hmA)
        · rcases hcov xA (hXeq ▸ by simp) (hms ▸ h1A.symm) with ⟨wA, hwA, hmA⟩
          exact False.elim (hnoA c hc0 hc1 wA hwA hmA)
        · rcases hcov x₀ (hXeq ▸ by simp) (hms ▸ h0A) with ⟨w0, hw0, hm0c⟩
          rcases hcov x₁ (hXeq ▸ by simp) (hms ▸ h1A) with ⟨w1, hw1, hm1c⟩
          rcases hcov xB (hXeq ▸ by simp) (hms ▸ hAB.symm) with ⟨wB, hwB, hmBc⟩
          have hwB_eq : wB = yA := hcrossB c hc0 hc1 wB hwB hmBc
          have hw01 : w0 ≠ w1 := (good_pair_disj_ne (hgood c) hm0c hm1c h01 (not_mem_X4 (by rwa [← hXeq] at hw1)).1.symm).2
          exact Or.inr (Or.inr ⟨w0, hw0, hm0c, hwB_eq ▸ hmBc, Or.inr ⟨w1, hw1, hw01, hm1c⟩⟩)
        · rcases hcov xA (hXeq ▸ by simp) (hms ▸ hAB) with ⟨wA, hwA, hmA⟩
          exact False.elim (hnoA c hc0 hc1 wA hwA hmA)
    have hno_0A : ∀ c : Fin 5, c ≠ 0 → c ≠ 1 → ({x₀, xA} : Edge n) ∈ m c → False := by
      intro c hc0 hc1 h0Ac
      rcases fin5_other_two c hc0 hc1 with ⟨c1, c2, hc10, hc11, hc20, hc21, h1c, h2c, h12c⟩
      have hkill_c' : ∀ c' : Fin 5, c' ≠ 0 → c' ≠ 1 → c' ≠ c → ({xB, yA} : Edge n) ∈ m c' → False := by
        intro c' hc'0 hc'1 hcc' hBc'
        have hy1' : y₁ ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rwa [hXeq]
        have hyA' : yA ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rwa [hXeq]
        exact kill_fork hno h01 h0A h0B h1A h1B hAB hy1' hyA' hyA' hy1A (by decide) hc'0.symm hc1 hcc'.symm hc'1.symm hm0 h0Ac hm1_1 hm1A hBc'
      rcases hclassify c1 hc10 hc11 with h1AB | ⟨_, h1B⟩ | ⟨_, _, _, h1B, _⟩
      · rcases hclassify c2 hc20 hc21 with h2AB | ⟨_, h2B⟩ | ⟨_, _, _, h2B, _⟩
        · exact hno_twoAB c1 c2 hc10 hc11 hc20 hc21 h12c h1AB h2AB
        · exact hkill_c' c2 hc20 hc21 h2c h2B
        · exact hkill_c' c2 hc20 hc21 h2c h2B
      · exact hkill_c' c1 hc10 hc11 h1c h1B
      · exact hkill_c' c1 hc10 hc11 h1c h1B
    have hex_two3 : ∃ c1 c2 : Fin 5, c1 ≠ 0 ∧ c1 ≠ 1 ∧ c2 ≠ 0 ∧ c2 ≠ 1 ∧ c1 ≠ c2 ∧
        (∃ w0 : Fin n, w0 ∉ X ∧ ({x₀, w0} : Edge n) ∈ m c1 ∧ ({xB, yA} : Edge n) ∈ m c1 ∧
          (({x₁, xA} : Edge n) ∈ m c1 ∨ ∃ w1 : Fin n, w1 ∉ X ∧ w0 ≠ w1 ∧ ({x₁, w1} : Edge n) ∈ m c1)) ∧
        (∃ w0 : Fin n, w0 ∉ X ∧ ({x₀, w0} : Edge n) ∈ m c2 ∧ ({xB, yA} : Edge n) ∈ m c2 ∧
          (({x₁, xA} : Edge n) ∈ m c2 ∨ ∃ w1 : Fin n, w1 ∉ X ∧ w0 ≠ w1 ∧ ({x₁, w1} : Edge n) ∈ m c2)) := by
      rcases hclassify 2 (by decide) (by decide) with h2AB | ⟨h20A, _⟩ | h2t
      · rcases hclassify 3 (by decide) (by decide) with h3AB | ⟨h30A, _⟩ | h3t
        · exact False.elim (hno_twoAB 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) h2AB h3AB)
        · exact False.elim (hno_0A 3 (by decide) (by decide) h30A)
        · rcases hclassify 4 (by decide) (by decide) with h4AB | ⟨h40A, _⟩ | h4t
          · exact False.elim (hno_twoAB 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) h2AB h4AB)
          · exact False.elim (hno_0A 4 (by decide) (by decide) h40A)
          · exact ⟨3, 4, by decide, by decide, by decide, by decide, by decide, h3t, h4t⟩
      · exact False.elim (hno_0A 2 (by decide) (by decide) h20A)
      · rcases hclassify 3 (by decide) (by decide) with h3AB | ⟨h30A, _⟩ | h3t
        · rcases hclassify 4 (by decide) (by decide) with h4AB | ⟨h40A, _⟩ | h4t
          · exact False.elim (hno_twoAB 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) h3AB h4AB)
          · exact False.elim (hno_0A 4 (by decide) (by decide) h40A)
          · exact ⟨2, 4, by decide, by decide, by decide, by decide, by decide, h2t, h4t⟩
        · exact False.elim (hno_0A 3 (by decide) (by decide) h30A)
        · exact ⟨2, 3, by decide, by decide, by decide, by decide, by decide, h2t, h3t⟩
    rcases hex_two3 with ⟨c1, c2, hc10, hc11, hc20, hc21, h12c, ⟨u0, hu0X, hc1_0, hc1_B, hrest1⟩, ⟨v0, hv0X, hc2_0, hc2_B, hrest2⟩⟩
    have hkill_two_t0 : ∀ (d1 d2 : Fin 5) (a0 a1 b0 b1 : Fin n),
        d1 ≠ 0 → d1 ≠ 1 → d2 ≠ 0 → d2 ≠ 1 → d1 ≠ d2 →
        a0 ∉ X → a1 ∉ X → b0 ∉ X → b1 ∉ X → a0 ≠ a1 → b0 ≠ b1 →
        ({x₀, a0} : Edge n) ∈ m d1 → ({x₁, a1} : Edge n) ∈ m d1 → ({xB, yA} : Edge n) ∈ m d1 →
        ({x₀, b0} : Edge n) ∈ m d2 → ({x₁, b1} : Edge n) ∈ m d2 → ({xB, yA} : Edge n) ∈ m d2 → False := by
      intro d1 d2 a0 a1 b0 b1 _ hd11 _ hd21 hd12 ha0 ha1 hb0 hb1 ha01 _ h10 h11 hm1_B h20 _ hm2_B
      have ha0_yA : a0 ≠ yA := (good_pair_disj_ne (hgood d1) h10 hm1_B h0B (not_mem_X4 (by rwa [← hXeq] at hyAX)).1.symm).2
      have ha1_yA : a1 ≠ yA := (good_pair_disj_ne (hgood d1) h11 hm1_B h1B (not_mem_X4 (by rwa [← hXeq] at hyAX)).2.1.symm).2
      have hb0_yA : b0 ≠ yA := (good_pair_disj_ne (hgood d2) h20 hm2_B h0B (not_mem_X4 (by rwa [← hXeq] at hyAX)).1.symm).2
      have hb0_3 : b0 ≠ x₀ ∧ b0 ≠ x₁ ∧ b0 ≠ xA := by have := not_mem_X4 (by rwa [← hXeq] at hb0); exact ⟨this.1, this.2.1, this.2.2.1⟩
      have ha1_3 : a1 ≠ x₀ ∧ a1 ≠ x₁ ∧ a1 ≠ xA := by have := not_mem_X4 (by rwa [← hXeq] at ha1); exact ⟨this.1, this.2.1, this.2.2.1⟩
      have hyA_3 : yA ≠ x₀ ∧ yA ≠ x₁ ∧ yA ≠ xA := by have := not_mem_X4 (by rwa [← hXeq] at hyAX); exact ⟨this.1, this.2.1, this.2.2.1⟩
      have h_b0_a1 : b0 = a1 := by
        rcases kill_three_cross hno h01 h0A h1A hb0_3 ha1_3 hyA_3 hd12.symm hd21 hd11 h20 h11 hm1A with h | h | h
        · exact h
        · exact absurd h hb0_yA
        · exact absurd h ha1_yA
      have ha0_3B : a0 ≠ x₀ ∧ a0 ≠ x₁ ∧ a0 ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at ha0); exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hy1X' : y₁ ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rw [hXeq]; exact hy1X
      have hy1_3B : y₁ ≠ x₀ ∧ y₁ ≠ x₁ ∧ y₁ ≠ xB := by have := not_mem_X4 hy1X'; exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hyA_3B : yA ≠ x₀ ∧ yA ≠ x₁ ∧ yA ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at hyAX); exact ⟨this.1, this.2.1, this.2.2.2⟩
      have h_a0_y1 : a0 = y₁ := by
        rcases kill_three_cross hno h01 h0B h1B ha0_3B hy1_3B hyA_3B hd11 hd12 hd21.symm h10 hm1_1 hm2_B with h | h | h
        · exact h
        · exact absurd h ha0_yA
        · exact absurd h hy1A
      have hb0_3B : b0 ≠ x₀ ∧ b0 ≠ x₁ ∧ b0 ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at hb0); exact ⟨this.1, this.2.1, this.2.2.2⟩
      have h_b0_y1 : b0 = y₁ := by
        rcases kill_three_cross hno h01 h0B h1B hb0_3B hy1_3B hyA_3B hd21 hd12.symm hd11.symm h20 hm1_1 hm1_B with h | h | h
        · exact h
        · exact absurd h hb0_yA
        · exact absurd h hy1A
      exact ha01 ((h_a0_y1.trans h_b0_y1.symm).trans h_b0_a1)
    have hkill_1A_t0 : ∀ (d1 d2 : Fin 5) (a0 b0 b1 : Fin n),
        d1 ≠ 0 → d1 ≠ 1 → d2 ≠ 0 → d2 ≠ 1 → d1 ≠ d2 →
        a0 ∉ X → b0 ∉ X → b1 ∉ X → b0 ≠ b1 →
        ({x₁, xA} : Edge n) ∈ m d1 → ({x₀, a0} : Edge n) ∈ m d1 → ({xB, yA} : Edge n) ∈ m d1 →
        ({x₀, b0} : Edge n) ∈ m d2 → ({x₁, b1} : Edge n) ∈ m d2 → ({xB, yA} : Edge n) ∈ m d2 → False := by
      intro d1 d2 a0 b0 b1 _ hd11 _ hd21 hd12 _ hb0 _ _ h1_1A _ hm1_B h20 _ hm2_B
      have hb0_yA : b0 ≠ yA := (good_pair_disj_ne (hgood d2) h20 hm2_B h0B (not_mem_X4 (by rwa [← hXeq] at hyAX)).1.symm).2
      have hb0_1A : b0 ∉ ({x₁, xA, x₀, xB} : Finset (Fin n)) := by
        rw [← hXeq] at hb0; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hb0
      have hyB_1A : yB ∉ ({x₁, xA, x₀, xB} : Finset (Fin n)) := by
        rw [← hXeq] at hyBX; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hyBX
      have h_b0_yB : b0 = yB := kill_cross_eq hno h1A h01.symm h1B h0A.symm hAB h0B hb0_1A hyB_1A hd12 hd11 hd21 h1_1A h20 hm1B
      have hb0_3B : b0 ≠ x₀ ∧ b0 ≠ x₁ ∧ b0 ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at hb0); exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hy1X' : y₁ ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rw [hXeq]; exact hy1X
      have hy1_3B : y₁ ≠ x₀ ∧ y₁ ≠ x₁ ∧ y₁ ≠ xB := by have := not_mem_X4 hy1X'; exact ⟨this.1, this.2.1, this.2.2.2⟩
      have hyA_3B : yA ≠ x₀ ∧ yA ≠ x₁ ∧ yA ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at hyAX); exact ⟨this.1, this.2.1, this.2.2.2⟩
      have h_b0_y1 : b0 = y₁ := by
        rcases kill_three_cross hno h01 h0B h1B hb0_3B hy1_3B hyA_3B hd21 hd12.symm hd11.symm h20 hm1_1 hm1_B with h | h | h
        · exact h
        · exact absurd h hb0_yA
        · exact absurd h hy1A
      exact hy1B (h_b0_y1.symm.trans h_b0_yB)
    rcases hrest1 with h1_1A | ⟨u1, hu1X, hu01, hc1_1⟩
    · rcases hrest2 with h2_1A | ⟨v1, hv1X, hv01, hc2_1⟩
      · have hv0_1A : v0 ∉ ({x₁, xA, x₀, xB} : Finset (Fin n)) := by
          rw [← hXeq] at hv0X; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hv0X
        have hyB_1A : yB ∉ ({x₁, xA, x₀, xB} : Finset (Fin n)) := by
          rw [← hXeq] at hyBX; simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hyBX
        have h_v0_yB : v0 = yB := kill_cross_eq hno h1A h01.symm h1B h0A.symm hAB h0B hv0_1A hyB_1A h12c hc11 hc21 h1_1A hc2_0 hm1B
        have hv0_yA : v0 ≠ yA := (good_pair_disj_ne (hgood c2) hc2_0 hc2_B h0B (not_mem_X4 (by rwa [← hXeq] at hyAX)).1.symm).2
        have hv0_3B : v0 ≠ x₀ ∧ v0 ≠ x₁ ∧ v0 ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at hv0X); exact ⟨this.1, this.2.1, this.2.2.2⟩
        have hy1X' : y₁ ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by rw [hXeq]; exact hy1X
        have hy1_3B : y₁ ≠ x₀ ∧ y₁ ≠ x₁ ∧ y₁ ≠ xB := by have := not_mem_X4 hy1X'; exact ⟨this.1, this.2.1, this.2.2.2⟩
        have hyA_3B : yA ≠ x₀ ∧ yA ≠ x₁ ∧ yA ≠ xB := by have := not_mem_X4 (by rwa [← hXeq] at hyAX); exact ⟨this.1, this.2.1, this.2.2.2⟩
        have h_v0_y1 : v0 = y₁ := by
          rcases kill_three_cross hno h01 h0B h1B hv0_3B hy1_3B hyA_3B hc21 h12c.symm hc11.symm hc2_0 hm1_1 hc1_B with h | h | h
          · exact h
          · exact absurd h hv0_yA
          · exact absurd h hy1A
        exact hy1B (h_v0_y1.symm.trans h_v0_yB)
      · exact hkill_1A_t0 c1 c2 u0 v0 v1 hc10 hc11 hc20 hc21 h12c hu0X hv0X hv1X hv01 h1_1A hc1_0 hc1_B hc2_0 hc2_1 hc2_B
    · rcases hrest2 with h2_1A | ⟨v1, hv1X, hv01, hc2_1⟩
      · exact hkill_1A_t0 c2 c1 v0 u0 u1 hc20 hc21 hc10 hc11 h12c.symm hv0X hu0X hu1X hu01 h2_1A hc2_0 hc2_B hc1_0 hc1_1 hc1_B
      · exact hkill_two_t0 c1 c2 u0 u1 v0 v1 hc10 hc11 hc20 hc21 h12c hu0X hu1X hv0X hv1X hu01 hv01 hc1_0 hc1_1 hc1_B hc2_0 hc2_1 hc2_B
  by_cases hex2 : ∃ c : Fin 5, c ≠ 0 ∧ c ≠ 1 ∧ ∃ u : Fin n, u ∉ X ∧ ({x₂, u} : Edge n) ∈ m c
  · by_cases hex3 : ∃ c : Fin 5, c ≠ 0 ∧ c ≠ 1 ∧ ∃ v : Fin n, v ∉ X ∧ ({x₃, v} : Edge n) ∈ m c
    · rcases hex2 with ⟨cA, hcA0, hcA1, uA, huAX, hmA⟩
      rcases hex3 with ⟨cB, hcB0, hcB1, vB, hvBX, hmB⟩
      have huA_eq : uA = y₃ := hcross2 cA hcA0 hcA1 uA huAX hmA
      have hvB_eq : vB = y₂ := hcross3 cB hcB0 hcB1 vB hvBX hmB
      have hABeq : cA = cB := by
        by_contra hne
        have heq := kill_cross_eq hno h01 h02 h03 h12 h13 h23 huAX hvBX hcA0.symm hcB0.symm hne hm0 hmA hmB
        exact hy23 ((hvB_eq.symm.trans heq.symm).trans huA_eq)
      subst cB
      rcases fin5_other_two cA hcA0 hcA1 with ⟨c1, c2, hc10, hc11, hc20, hc21, h1A, h2A, h12c⟩
      have hmust23 : ∀ c : Fin 5, c ≠ 0 → c ≠ 1 → c ≠ cA → ({x₂, x₃} : Edge n) ∈ m c := by
        intro c hc0 hc1 hcne
        have hno2 : ∀ u : Fin n, u ∉ X → ({x₂, u} : Edge n) ∉ m c := by
          intro u huX hmc
          have hu_eq : u = y₃ := hcross2 c hc0 hc1 u huX hmc
          have heq := kill_cross_eq hno h01 h02 h03 h12 h13 h23 huX hvBX hc0.symm hcA0.symm hcne hm0 hmc hmB
          exact hy23 ((hvB_eq.symm.trans heq.symm).trans hu_eq)
        have hno3 : ∀ v : Fin n, v ∉ X → ({x₃, v} : Edge n) ∉ m c := by
          intro v hvX hmc
          have hv_eq : v = y₂ := hcross3 c hc0 hc1 v hvX hmc
          have heq := kill_cross_eq hno h01 h02 h03 h12 h13 h23 huAX hvX hcA0.symm hc0.symm hcne.symm hm0 hmA hmc
          exact hy23 ((hv_eq.symm.trans heq.symm).trans huA_eq)
        by_cases hintc : ∃ d ∈ m c, d ⊆ X
        · rcases hintc with ⟨d, hdm, hdsub⟩
          rcases int_edge_cases ((hgood c).2.1 d hdm) hdsub with rfl | rfl | rfl | rfl | rfl | rfl
          · rcases type1_decomp h01 h02 h03 h12 h13 h23 (hgood c) (hhit c) hdm with ⟨w2, _, hw2, _, _, h2m, _⟩
            exact False.elim (hno2 w2 hw2 h2m)
          · rcases type1_decomp h02 h01 h03 h12.symm h23 h13 (hgood c)
                (by intro e he; convert hhit c e he using 2; ext z; simp [or_left_comm]) hdm with
              ⟨_, w3, _, hw3, _, _, h3m⟩
            exact False.elim (hno3 w3 (by simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw3) h3m)
          · rcases type1_decomp h03 h01 h02 h13.symm h23.symm h12 (hgood c)
                (by intro e he; convert hhit c e he using 2; ext z; simp [or_comm, or_left_comm]) hdm with
              ⟨_, w2, _, hw2, _, _, h2m⟩
            exact False.elim (hno2 w2 (by simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw2) h2m)
          · rcases type1_decomp h12 h01.symm h13 h02.symm h23 h03 (hgood c)
                (by intro e he; convert hhit c e he using 2; ext z; simp [or_left_comm]) hdm with
              ⟨_, w3, _, hw3, _, _, h3m⟩
            exact False.elim (hno3 w3 (by simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw3) h3m)
          · rcases type1_decomp h13 h01.symm h12 h03.symm h23.symm h02 (hgood c)
                (by intro e he; convert hhit c e he using 2; ext z; simp [or_comm, or_left_comm]) hdm with
              ⟨_, w2, _, hw2, _, _, h2m⟩
            exact False.elim (hno2 w2 (by simpa [X, Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw2) h2m)
          · exact hdm
        · push Not at hintc
          rcases type0_decomp hX4 (hgood c) (hhit c) hintc with ⟨miss, hmissX, hcov⟩
          simp only [X, Finset.mem_insert, Finset.mem_singleton] at hmissX
          rcases hmissX with hms | hms | hms | hms
          · rcases hcov x₂ (by simp [X]) (hms ▸ h02.symm) with ⟨w2, hw2, h2m⟩; exact False.elim (hno2 w2 hw2 h2m)
          · rcases hcov x₂ (by simp [X]) (hms ▸ h12.symm) with ⟨w2, hw2, h2m⟩; exact False.elim (hno2 w2 hw2 h2m)
          · rcases hcov x₃ (by simp [X]) (hms ▸ h23.symm) with ⟨w3, hw3, h3m⟩; exact False.elim (hno3 w3 hw3 h3m)
          · rcases hcov x₂ (by simp [X]) (hms ▸ h23) with ⟨w2, hw2, h2m⟩; exact False.elim (hno2 w2 hw2 h2m)
      exact htwo23 c1 c2 cA hc10 hc11 hc20 hc21 hcA0 hcA1 h12c h1A h2A (hmust23 c1 hc10 hc11 h1A) (hmust23 c2 hc20 hc21 h2A)
    · push Not at hex3
      exact hno_cross_side x₃ x₂ y₃ y₂ z₃ z₂ h03 h02 h13 h12 h23.symm
        (by ext z; simp [X, or_comm, or_left_comm]) hy3X hy2X hy13 hy12 hy23.symm hz3X hz2X hz23.symm
        hm0_3 hm0_2 hm1_3 hm1_2 (fun c hc0 hc1 u huX => hex3 c hc0 hc1 u huX)
  · push Not at hex2
    exact hno_cross_side x₂ x₃ y₂ y₃ z₂ z₃ h02 h03 h12 h13 h23 rfl hy2X hy3X hy12 hy13 hy23 hz2X hz3X hz23
      hm0_2 hm0_3 hm1_2 hm1_3 (fun c hc0 hc1 u huX => hex2 c hc0 hc1 u huX)

lemma rainbow5_hitting4 {n : ℕ} {X : Finset (Fin n)} (hX : X.card = 4)
    (m : Fin 5 → Matching n) (hgood : ∀ i, Good (m i))
    (hhit : ∀ i, ∀ e ∈ m i, ¬ Disjoint e X) :
    Rainbow 5 m := by
  by_cases hall0 : ∀ i : Fin 5, ∀ e ∈ m i, ¬ (e ⊆ X)
  · apply rainbow5_bipartite X m hgood
    intro j e he
    have hpos : 0 < (e ∩ X).card := Finset.card_pos.mpr
      (Finset.not_disjoint_iff.mp (hhit j e he) |> fun ⟨v, hv1, hv2⟩ => ⟨v, Finset.mem_inter.mpr ⟨hv1, hv2⟩⟩)
    have hle : (e ∩ X).card ≤ 2 := le_trans (Finset.card_le_card Finset.inter_subset_left) (le_of_eq ((hgood j).2.1 e he))
    have hne2 : (e ∩ X).card ≠ 2 := by
      intro h2
      apply hall0 j e he
      have heq : e ∩ X = e := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [h2, (hgood j).2.1 e he])
      intro v hv; rw [← heq] at hv; exact (Finset.mem_inter.mp hv).2
    omega
  · push Not at hall0
    rcases hall0 with ⟨i₀, d₀, hd₀m, hd₀sub⟩
    rcases Finset.card_eq_two.mp ((hgood i₀).2.1 d₀ hd₀m) with ⟨x₀, x₁, h01, rfl⟩
    have hx0X : x₀ ∈ X := hd₀sub (Finset.mem_insert_self x₀ _)
    have hx1X : x₁ ∈ X := hd₀sub (Finset.mem_insert_of_mem (Finset.mem_singleton_self x₁))
    have hrem : (X \ ({x₀, x₁} : Finset (Fin n))).card = 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hd₀sub, hX, Finset.card_pair h01]
    rcases Finset.card_eq_two.mp hrem with ⟨x₂, x₃, h23, hXrem⟩
    have hx2m := Finset.mem_sdiff.mp (hXrem ▸ Finset.mem_insert_self x₂ _)
    have hx3m := Finset.mem_sdiff.mp (hXrem ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self x₃))
    have h02 : x₀ ≠ x₂ := fun h => hx2m.2 (h ▸ Finset.mem_insert_self _ _)
    have h12 : x₁ ≠ x₂ := fun h => hx2m.2 (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have h03 : x₀ ≠ x₃ := fun h => hx3m.2 (h ▸ Finset.mem_insert_self _ _)
    have h13 : x₁ ≠ x₃ := fun h => hx3m.2 (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hXeq : X = {x₀, x₁, x₂, x₃} := by
      ext v
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hv
        by_cases h01v : v ∈ ({x₀, x₁} : Finset (Fin n))
        · simp only [Finset.mem_insert, Finset.mem_singleton] at h01v
          rcases h01v with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
        · have : v ∈ X \ ({x₀, x₁} : Finset (Fin n)) := Finset.mem_sdiff.mpr ⟨hv, h01v⟩
          rw [hXrem, Finset.mem_insert, Finset.mem_singleton] at this
          rcases this with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr rfl))
      · rintro (rfl | rfl | rfl | rfl)
        · exact hx0X
        · exact hx1X
        · exact hx2m.1
        · exact hx3m.1
    subst X
    by_cases hall1 : ∀ i : Fin 5, ∃ d ∈ m i, d ⊆ ({x₀, x₁, x₂, x₃} : Finset (Fin n))
    · exact case_all_type1 hgood h01 h02 h03 h12 h13 h23 hhit hall1
    · push Not at hall1
      have hcall2A : ∀ (a b c d : Fin n),
          a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
          ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
          ∀ (j₀ j₁ : Fin 5), j₀ ≠ j₁ →
          ({a, b} : Edge n) ∈ m j₀ →
          (∀ e ∈ m j₁, ¬ (e ⊆ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))) →
          (∃ ub uc ud : Fin n,
            ub ∉ ({a, b, c, d} : Finset (Fin n)) ∧ uc ∉ ({a, b, c, d} : Finset (Fin n)) ∧ ud ∉ ({a, b, c, d} : Finset (Fin n)) ∧
            ({b, ub} : Edge n) ∈ m j₁ ∧ ({c, uc} : Edge n) ∈ m j₁ ∧ ({d, ud} : Edge n) ∈ m j₁) →
          Rainbow 5 m := by
        intro a b c d hab hac had hbc hbd hcd hXeq' j₀ j₁ hj01 hmj0 hmj1 ⟨ub, uc, ud, hub, huc, hud, hmb, hmc, hmd⟩
        let σ₁ : Equiv.Perm (Fin 5) := Equiv.swap 0 j₀
        let j₁' : Fin 5 := σ₁.symm j₁
        have hj1'0 : j₁' ≠ 0 := by
          intro h
          have : j₁ = σ₁ 0 := by rw [← h]; simp [j₁']
          rw [Equiv.swap_apply_left] at this
          exact hj01 this.symm
        let τ : Equiv.Perm (Fin 5) := (Equiv.swap 1 j₁').trans σ₁
        have hτ0 : τ 0 = j₀ := by
          change σ₁ (Equiv.swap 1 j₁' 0) = j₀
          rw [Equiv.swap_apply_of_ne_of_ne (by decide) hj1'0.symm, Equiv.swap_apply_left]
        have hτ1 : τ 1 = j₁ := by
          change σ₁ (Equiv.swap 1 j₁' 1) = j₁
          rw [Equiv.swap_apply_left]; simp [j₁']
        apply rainbow_of_perm τ
        have hubc : ub ≠ uc := (good_pair_disj_ne (hgood j₁) hmb hmc hbc (not_mem_X4 huc).2.1.symm).2
        have hubd : ub ≠ ud := (good_pair_disj_ne (hgood j₁) hmb hmd hbd (not_mem_X4 hud).2.1.symm).2
        have hucd : uc ≠ ud := (good_pair_disj_ne (hgood j₁) hmc hmd hcd (not_mem_X4 hud).2.2.1.symm).2
        exact case2A (fun i => hgood (τ i)) hab hac had hbc hbd hcd
          (fun i e he => by rw [hXeq']; exact hhit (τ i) e he)
          (hτ0.symm ▸ hmj0)
          (fun e he => by rw [hXeq']; exact hmj1 e (hτ1 ▸ he))
          hub huc hud hubc hubd hucd (hτ1.symm ▸ hmb) (hτ1.symm ▸ hmc) (hτ1.symm ▸ hmd)
      by_cases h2A_exists : ∃ (j₀ j₁ : Fin 5) (a b c d : Fin n),
          j₀ ≠ j₁ ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
          ({a, b, c, d} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} ∧
          ({a, b} : Edge n) ∈ m j₀ ∧
          (∀ e ∈ m j₁, ¬ (e ⊆ ({x₀, x₁, x₂, x₃} : Finset (Fin n)))) ∧
          (∃ ub uc ud : Fin n,
            ub ∉ ({a, b, c, d} : Finset (Fin n)) ∧ uc ∉ ({a, b, c, d} : Finset (Fin n)) ∧ ud ∉ ({a, b, c, d} : Finset (Fin n)) ∧
            ({b, ub} : Edge n) ∈ m j₁ ∧ ({c, uc} : Edge n) ∈ m j₁ ∧ ({d, ud} : Edge n) ∈ m j₁)
      · rcases h2A_exists with ⟨j₀, j₁, a, b, c, d, hj01, hab, hac, had, hbc, hbd, hcd, hXeq', hmj0, hmj1, hcov⟩
        exact hcall2A a b c d hab hac had hbc hbd hcd hXeq' j₀ j₁ hj01 hmj0 hmj1 hcov
      · rcases hall1 with ⟨i₁, hi₁_noint⟩
        have hi01 : i₀ ≠ i₁ := by
          intro h; subst h; exact hi₁_noint {x₀, x₁} hd₀m hd₀sub
        rcases type0_decomp hX (hgood i₁) (hhit i₁) hi₁_noint with ⟨miss, hmissX, hcov1⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmissX
        have hnot_miss0 : miss ≠ x₀ := by
          intro hm0; apply h2A_exists
          rcases hcov1 x₁ (by simp) (hm0 ▸ h01.symm) with ⟨u1, hu1, hm1⟩
          rcases hcov1 x₂ (by simp) (hm0 ▸ h02.symm) with ⟨u2, hu2, hm2⟩
          rcases hcov1 x₃ (by simp) (hm0 ▸ h03.symm) with ⟨u3, hu3, hm3⟩
          exact ⟨i₀, i₁, x₀, x₁, x₂, x₃, hi01, h01, h02, h03, h12, h13, h23, rfl, hd₀m, hi₁_noint, u1, u2, u3, hu1, hu2, hu3, hm1, hm2, hm3⟩
        have hnot_miss1 : miss ≠ x₁ := by
          intro hm1'; apply h2A_exists
          rcases hcov1 x₀ (by simp) (hm1' ▸ h01) with ⟨u0, hu0, hm0⟩
          rcases hcov1 x₂ (by simp) (hm1' ▸ h12.symm) with ⟨u2, hu2, hm2⟩
          rcases hcov1 x₃ (by simp) (hm1' ▸ h13.symm) with ⟨u3, hu3, hm3⟩
          have hXsw : ({x₁, x₀, x₂, x₃} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} := by ext z; simp [or_left_comm]
          exact ⟨i₀, i₁, x₁, x₀, x₂, x₃, hi01, h01.symm, h12, h13, h02, h03, h23, hXsw, by rw [pair_comm]; exact hd₀m, hi₁_noint,
            u0, u2, u3, by rwa [hXsw], by rwa [hXsw], by rwa [hXsw], hm0, hm2, hm3⟩
        have hcase2B : ∀ (xA xB : Fin n),
            x₀ ≠ xA → x₀ ≠ xB → x₁ ≠ xA → x₁ ≠ xB → xA ≠ xB →
            ({x₀, x₁, xA, xB} : Finset (Fin n)) = {x₀, x₁, x₂, x₃} →
            (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xB →
              ∃ u : Fin n, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m i₁) →
            Rainbow 5 m := by
          intro xA xB h0A h0B h1A h1B hAB hXeq' hcovB
          by_contra hno
          have hhit' : ∀ i, ∀ e ∈ m i, ¬ Disjoint e ({x₀, x₁, xA, xB} : Finset (Fin n)) := by
            rw [hXeq']; exact hhit
          have hX4' : ({x₀, x₁, xA, xB} : Finset (Fin n)).card = 4 := by rw [hXeq']; exact hX
          rcases type1_decomp h01 h0A h0B h1A h1B hAB (hgood i₀) (hhit' i₀) hd₀m with
            ⟨zA, zB, hzA, hzB, hzAB, hm0A, hm0B⟩
          rcases hcovB x₀ (by simp) h0B with ⟨y0, hy0, hm1_0⟩
          rcases hcovB x₁ (by simp) h1B with ⟨y1, hy1, hm1_1⟩
          rcases hcovB xA (by simp) hAB with ⟨yA, hyA, hm1_A⟩
          have hy01 : y0 ≠ y1 := (good_pair_disj_ne (hgood i₁) hm1_0 hm1_1 h01 (not_mem_X4 hy1).1.symm).2
          have hy0A : y0 ≠ yA := (good_pair_disj_ne (hgood i₁) hm1_0 hm1_A h0A (not_mem_X4 hyA).1.symm).2
          have hy1A : y1 ≠ yA := (good_pair_disj_ne (hgood i₁) hm1_1 hm1_A h1A (not_mem_X4 hyA).2.1.symm).2
          have hno_int_B : ∀ j : Fin 5, ∀ u : Fin n, u ∈ ({x₀, x₁, xA} : Finset (Fin n)) → ({xB, u} : Edge n) ∉ m j := by
            intro j u hu hmj
            have hji1 : j ≠ i₁ := by
              intro h; subst h
              exact hi₁_noint {xB, u} hmj (by
                rw [← hXeq']
                intro v hv
                simp only [Finset.mem_insert, Finset.mem_singleton] at hv hu ⊢
                rcases hv with rfl | rfl
                · exact Or.inr (Or.inr (Or.inr rfl))
                · rcases hu with rfl | rfl | rfl <;> simp)
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            apply h2A_exists
            rcases hu with hu0 | hu1 | huA
            · rw [hu0] at hmj
              exact ⟨j, i₁, xB, x₀, x₁, xA, hji1, h0B.symm, h1B.symm, hAB.symm, h01, h0A, h1A,
                by rw [← hXeq']; ext z; simp [or_comm, or_left_comm], hmj, hi₁_noint,
                y0, y1, yA,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy0,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy1,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hyA,
                hm1_0, hm1_1, hm1_A⟩
            · rw [hu1] at hmj
              exact ⟨j, i₁, xB, x₁, x₀, xA, hji1, h1B.symm, h0B.symm, hAB.symm, h01.symm, h1A, h0A,
                by rw [← hXeq']; ext z; simp [or_comm, or_left_comm], hmj, hi₁_noint,
                y1, y0, yA,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy1,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy0,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hyA,
                hm1_1, hm1_0, hm1_A⟩
            · rw [huA] at hmj
              exact ⟨j, i₁, xB, xA, x₀, x₁, hji1, hAB.symm, h0B.symm, h1B.symm, h0A.symm, h1A.symm, h01,
                by rw [← hXeq']; ext z; simp [or_comm, or_left_comm], hmj, hi₁_noint,
                yA, y0, y1,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hyA,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy0,
                by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hy1,
                hm1_A, hm1_0, hm1_1⟩
          have hno_t0_miss01 : ∀ j : Fin 5, (∀ e ∈ m j, ¬ (e ⊆ ({x₀, x₁, xA, xB} : Finset (Fin n)))) →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xB → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j) ∨
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xA → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j) := by
            intro j hj_noint
            have hji0 : i₀ ≠ j := fun h => hj_noint {x₀, x₁} (h ▸ hd₀m) (by intro v hv; simp at hv ⊢; tauto)
            rcases type0_decomp hX4' (hgood j) (hhit' j) hj_noint with ⟨ms, hmsX, hcovj⟩
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmsX
            rcases hmsX with hms | hms | hms | hms
            · exfalso; apply h2A_exists
              rcases hcovj x₁ (by simp) (hms ▸ h01.symm) with ⟨u1, hu1, h1⟩
              rcases hcovj xA (by simp) (hms ▸ h0A.symm) with ⟨uA, huA, hA⟩
              rcases hcovj xB (by simp) (hms ▸ h0B.symm) with ⟨uB, huB, hB⟩
              exact ⟨i₀, j, x₀, x₁, xA, xB, hji0, h01, h0A, h0B, h1A, h1B, hAB, hXeq', hd₀m,
                fun e he => by rw [← hXeq']; exact hj_noint e he, u1, uA, uB, hu1, huA, huB, h1, hA, hB⟩
            · exfalso; apply h2A_exists
              rcases hcovj x₀ (by simp) (hms ▸ h01) with ⟨u0, hu0, h0⟩
              rcases hcovj xA (by simp) (hms ▸ h1A.symm) with ⟨uA, huA, hA⟩
              rcases hcovj xB (by simp) (hms ▸ h1B.symm) with ⟨uB, huB, hB⟩
              have hsw : ({x₁, x₀, xA, xB} : Finset (Fin n)) = {x₀, x₁, xA, xB} := by ext z; simp [or_left_comm]
              exact ⟨i₀, j, x₁, x₀, xA, xB, hji0, h01.symm, h1A, h1B, h0A, h0B, hAB, hsw.trans hXeq',
                by rw [pair_comm]; exact hd₀m, fun e he => by rw [← hXeq']; exact hj_noint e he,
                u0, uA, uB, by rwa [hsw], by rwa [hsw], by rwa [hsw], h0, hA, hB⟩
            · exact Or.inr (hms ▸ hcovj)
            · exact Or.inl (hms ▸ hcovj)
          have hkill_three_missB : ∀ j1 j2 : Fin 5, j1 ≠ i₀ → j1 ≠ i₁ → j2 ≠ i₀ → j2 ≠ i₁ → j1 ≠ j2 →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xB → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j1) →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xB → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j2) →
              False := by
            intro j1 j2 hj10 hj11 hj20 hj21 hj12 hc1 hc2
            have hstep : ∀ (a b c pa pb : Fin n),
                a ≠ b → a ≠ c → b ≠ c → a ≠ xB → b ≠ xB → c ≠ xB →
                ({a, b, c} : Finset (Fin n)) = {x₀, x₁, xA} →
                pa ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) → pb ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) →
                pa ≠ pb → pa ≠ zB → pb ≠ zB →
                ({a, pa} : Edge n) ∈ m i₁ → ({b, pb} : Edge n) ∈ m i₁ → False := by
              intro a b c pa pb hab hac hbc haB hbB hcB habc hpa hpb hpab hpaz hpbz hma hmb
              have haX : a ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by
                have h : a ∈ ({x₀, x₁, xA} : Finset (Fin n)) := habc ▸ Finset.mem_insert_self _ _
                simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
                rcases h with rfl | rfl | rfl <;> simp
              have hbX : b ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by
                have h : b ∈ ({x₀, x₁, xA} : Finset (Fin n)) :=
                  habc ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
                simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
                rcases h with rfl | rfl | rfl <;> simp
              have hcX : c ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)) := by
                have h : c ∈ ({x₀, x₁, xA} : Finset (Fin n)) :=
                  habc ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
                simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
                rcases h with rfl | rfl | rfl <;> simp
              have hnot3 : ∀ {u : Fin n}, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) →
                  u ≠ a ∧ u ≠ b ∧ u ≠ c ∧ u ≠ xB := by
                intro u hu
                have hu0 := not_mem_X4 hu
                have hmem : ∀ v ∈ ({a, b, c} : Finset (Fin n)), u ≠ v := by
                  intro v hv; rw [habc] at hv; simp at hv
                  rcases hv with rfl | rfl | rfl
                  · exact hu0.1
                  · exact hu0.2.1
                  · exact hu0.2.2.1
                exact ⟨hmem a (by simp), hmem b (by simp), hmem c (by simp), hu0.2.2.2⟩
              rcases hc1 a haX haB with ⟨a1, ha1, h1a⟩
              rcases hc1 b hbX hbB with ⟨b1, hb1, h1b⟩
              rcases hc1 c hcX hcB with ⟨c1, hc1m, h1c⟩
              rcases hc2 a haX haB with ⟨a2, ha2, h2a⟩
              rcases hc2 b hbX hbB with ⟨b2, hb2, h2b⟩
              rcases hc2 c hcX hcB with ⟨c2, hc2m, h2c⟩
              have hzB3 := hnot3 hzB; have hpa3 := hnot3 hpa; have hpb3 := hnot3 hpb
              have hc13 := hnot3 hc1m; have hc23 := hnot3 hc2m
              have h_c1_z : c1 = zB := by
                have h1 := kill_three_cross hno haB.symm hcB.symm hac ⟨hzB3.2.2.2, hzB3.1, hzB3.2.2.1⟩ ⟨hpa3.2.2.2, hpa3.1, hpa3.2.2.1⟩ ⟨hc13.2.2.2, hc13.1, hc13.2.2.1⟩ hi01 hj10.symm hj11.symm hm0B hma h1c
                have h2 := kill_three_cross hno hbB.symm hcB.symm hbc ⟨hzB3.2.2.2, hzB3.2.1, hzB3.2.2.1⟩ ⟨hpb3.2.2.2, hpb3.2.1, hpb3.2.2.1⟩ ⟨hc13.2.2.2, hc13.2.1, hc13.2.2.1⟩ hi01 hj10.symm hj11.symm hm0B hmb h1c
                rcases h1 with h | h | h
                · exact absurd h.symm hpaz
                · exact h.symm
                · rcases h2 with h' | h' | h'
                  · exact absurd h'.symm hpbz
                  · exact h'.symm
                  · exact absurd (h.trans h'.symm) hpab
              have h_c2_z : c2 = zB := by
                have h1 := kill_three_cross hno haB.symm hcB.symm hac ⟨hzB3.2.2.2, hzB3.1, hzB3.2.2.1⟩ ⟨hpa3.2.2.2, hpa3.1, hpa3.2.2.1⟩ ⟨hc23.2.2.2, hc23.1, hc23.2.2.1⟩ hi01 hj20.symm hj21.symm hm0B hma h2c
                have h2 := kill_three_cross hno hbB.symm hcB.symm hbc ⟨hzB3.2.2.2, hzB3.2.1, hzB3.2.2.1⟩ ⟨hpb3.2.2.2, hpb3.2.1, hpb3.2.2.1⟩ ⟨hc23.2.2.2, hc23.2.1, hc23.2.2.1⟩ hi01 hj20.symm hj21.symm hm0B hmb h2c
                rcases h1 with h | h | h
                · exact absurd h.symm hpaz
                · exact h.symm
                · rcases h2 with h' | h' | h'
                  · exact absurd h'.symm hpbz
                  · exact h'.symm
                  · exact absurd (h.trans h'.symm) hpab
              have ha1_z : a1 ≠ zB := h_c1_z ▸ (good_pair_disj_ne (hgood j1) h1a h1c hac hc13.1.symm).2
              have hb2_z : b2 ≠ zB := h_c2_z ▸ (good_pair_disj_ne (hgood j2) h2b h2c hbc hc23.2.1.symm).2
              have ha13 := hnot3 ha1; have hb23 := hnot3 hb2
              have h_a1_pb : a1 = pb := by
                rcases kill_three_cross hno hbB.symm haB.symm hab.symm ⟨hzB3.2.2.2, hzB3.2.1, hzB3.1⟩ ⟨hpb3.2.2.2, hpb3.2.1, hpb3.1⟩ ⟨ha13.2.2.2, ha13.2.1, ha13.1⟩ hi01 hj10.symm hj11.symm hm0B hmb h1a with h | h | h
                · exact absurd h.symm hpbz
                · exact absurd h.symm ha1_z
                · exact h.symm
              have h_b2_pa : b2 = pa := by
                rcases kill_three_cross hno haB.symm hbB.symm hab ⟨hzB3.2.2.2, hzB3.1, hzB3.2.1⟩ ⟨hpa3.2.2.2, hpa3.1, hpa3.2.1⟩ ⟨hb23.2.2.2, hb23.1, hb23.2.1⟩ hi01 hj20.symm hj21.symm hm0B hma h2b with h | h | h
                · exact absurd h.symm hpaz
                · exact absurd h.symm hb2_z
                · exact h.symm
              rcases kill_three_cross hno haB.symm hbB.symm hab ⟨hzB3.2.2.2, hzB3.1, hzB3.2.1⟩ ⟨ha13.2.2.2, ha13.1, ha13.2.1⟩ ⟨hb23.2.2.2, hb23.1, hb23.2.1⟩ hj10.symm hj20.symm hj12 hm0B h1a h2b with h | h | h
              · exact ha1_z h.symm
              · exact hb2_z h.symm
              · exact hpab (h_b2_pa.symm.trans (h.symm.trans h_a1_pb))
            by_cases h0z : y0 = zB
            · exact hstep x₁ xA x₀ y1 yA h1A h01.symm h0A.symm h1B hAB h0B (by ext z; simp [or_comm, or_left_comm]) hy1 hyA hy1A (h0z ▸ hy01.symm) (h0z ▸ hy0A.symm) hm1_1 hm1_A
            · by_cases h1z : y1 = zB
              · exact hstep x₀ xA x₁ y0 yA h0A h01 h1A.symm h0B hAB h1B (by ext z; simp [or_comm, or_left_comm]) hy0 hyA hy0A h0z (h1z ▸ hy1A.symm) hm1_0 hm1_A
              · exact hstep x₀ x₁ xA y0 y1 h01 h0A h1A h0B h1B hAB rfl hy0 hy1 hy01 h0z h1z hm1_0 hm1_1
          have hkill_missA_missB : ∀ j1 j2 : Fin 5, j1 ≠ i₀ → j1 ≠ i₁ → j2 ≠ i₀ → j2 ≠ i₁ → j1 ≠ j2 →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xA → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j1) →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xB → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j2) →
              False := by
            intro j1 j2 hj10 hj11 hj20 hj21 hj12 hcA hcB
            rcases hcA xB (by simp) hAB.symm with ⟨cB, hcBX, h1B'⟩
            rcases hcB xA (by simp) hAB with ⟨wA, hwAX, h2A'⟩
            have h_yA_cB : yA = cB := kill_cross_eq hno h01 h0A h0B h1A h1B hAB hyA hcBX hi01 hj10.symm hj11.symm hd₀m hm1_A h1B'
            have h_wA_cB : wA = cB := kill_cross_eq hno h01 h0A h0B h1A h1B hAB hwAX hcBX hj20.symm hj10.symm hj12.symm hd₀m h2A' h1B'
            have h_wA_yA : wA = yA := h_wA_cB.trans h_yA_cB.symm
            have hzB_0A : zB ≠ x₀ ∧ zB ≠ xA ∧ zB ≠ xB := by have := not_mem_X4 hzB; exact ⟨this.1, this.2.2.1, this.2.2.2⟩
            have hy0_0A : y0 ≠ x₀ ∧ y0 ≠ xA ∧ y0 ≠ xB := by have := not_mem_X4 hy0; exact ⟨this.1, this.2.2.1, this.2.2.2⟩
            have hwA_0A : wA ≠ x₀ ∧ wA ≠ xA ∧ wA ≠ xB := by have := not_mem_X4 hwAX; exact ⟨this.1, this.2.2.1, this.2.2.2⟩
            have h_zB_0 : zB = y0 ∨ zB = yA := by
              rcases kill_three_cross hno h0B.symm hAB.symm h0A ⟨hzB_0A.2.2, hzB_0A.1, hzB_0A.2.1⟩ ⟨hy0_0A.2.2, hy0_0A.1, hy0_0A.2.1⟩ ⟨hwA_0A.2.2, hwA_0A.1, hwA_0A.2.1⟩ hi01 hj20.symm hj21.symm hm0B hm1_0 h2A' with h | h | h
              · exact Or.inl h
              · exact Or.inr (h.trans h_wA_yA)
              · exact absurd (h.trans h_wA_yA) hy0A
            have hzB_1A : zB ≠ x₁ ∧ zB ≠ xA ∧ zB ≠ xB := by have := not_mem_X4 hzB; exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
            have hy1_1A : y1 ≠ x₁ ∧ y1 ≠ xA ∧ y1 ≠ xB := by have := not_mem_X4 hy1; exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
            have hwA_1A : wA ≠ x₁ ∧ wA ≠ xA ∧ wA ≠ xB := by have := not_mem_X4 hwAX; exact ⟨this.2.1, this.2.2.1, this.2.2.2⟩
            have h_zB_1 : zB = y1 ∨ zB = yA := by
              rcases kill_three_cross hno h1B.symm hAB.symm h1A ⟨hzB_1A.2.2, hzB_1A.1, hzB_1A.2.1⟩ ⟨hy1_1A.2.2, hy1_1A.1, hy1_1A.2.1⟩ ⟨hwA_1A.2.2, hwA_1A.1, hwA_1A.2.1⟩ hi01 hj20.symm hj21.symm hm0B hm1_1 h2A' with h | h | h
              · exact Or.inl h
              · exact Or.inr (h.trans h_wA_yA)
              · exact absurd (h.trans h_wA_yA) hy1A
            have hzB_eq : zB = yA := by
              rcases h_zB_0 with h0 | h0
              · rcases h_zB_1 with h1 | h1
                · exact absurd (h0.symm.trans h1) hy01
                · exact h1
              · exact h0
            have hzA_ne_cB : zA ≠ cB := fun h => hzAB ((h.trans h_yA_cB.symm).trans hzB_eq.symm)
            have hzA_0B : zA ≠ xA ∧ zA ≠ x₀ ∧ zA ≠ xB := by have := not_mem_X4 hzA; exact ⟨this.2.2.1, this.1, this.2.2.2⟩
            have hy0_0B : y0 ≠ xA ∧ y0 ≠ x₀ ∧ y0 ≠ xB := by have := not_mem_X4 hy0; exact ⟨this.2.2.1, this.1, this.2.2.2⟩
            have hcB_0B : cB ≠ xA ∧ cB ≠ x₀ ∧ cB ≠ xB := by have := not_mem_X4 hcBX; exact ⟨this.2.2.1, this.1, this.2.2.2⟩
            have h_zA_y0 : zA = y0 := by
              rcases kill_three_cross hno h0A.symm hAB h0B hzA_0B hy0_0B hcB_0B hi01 hj10.symm hj11.symm hm0A hm1_0 h1B' with h | h | h
              · exact h
              · exact absurd h hzA_ne_cB
              · exact absurd (h.trans h_yA_cB.symm) hy0A
            have hzA_1B : zA ≠ xA ∧ zA ≠ x₁ ∧ zA ≠ xB := by have := not_mem_X4 hzA; exact ⟨this.2.2.1, this.2.1, this.2.2.2⟩
            have hy1_1B : y1 ≠ xA ∧ y1 ≠ x₁ ∧ y1 ≠ xB := by have := not_mem_X4 hy1; exact ⟨this.2.2.1, this.2.1, this.2.2.2⟩
            have hcB_1B : cB ≠ xA ∧ cB ≠ x₁ ∧ cB ≠ xB := by have := not_mem_X4 hcBX; exact ⟨this.2.2.1, this.2.1, this.2.2.2⟩
            have h_zA_y1 : zA = y1 := by
              rcases kill_three_cross hno h1A.symm hAB h1B hzA_1B hy1_1B hcB_1B hi01 hj10.symm hj11.symm hm0A hm1_1 h1B' with h | h | h
              · exact h
              · exact absurd h hzA_ne_cB
              · exact absurd (h.trans h_yA_cB.symm) hy1A
            exact hy01 (h_zA_y0.symm.trans h_zA_y1)
          have hkill_two_missA : ∀ j1 j2 : Fin 5, j1 ≠ i₀ → j1 ≠ i₁ → j2 ≠ i₀ → j2 ≠ i₁ → j1 ≠ j2 →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xA → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j1) →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xA → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j2) →
              False := by
            intro j1 j2 hj10 hj11 hj20 hj21 hj12 hc1 hc2
            rcases hc1 x₀ (by simp) h0A with ⟨a1, ha1, h10⟩
            rcases hc1 x₁ (by simp) h1A with ⟨b1, hb1, h11⟩
            rcases hc1 xB (by simp) hAB.symm with ⟨c1, hc1X, h1B'⟩
            rcases hc2 x₁ (by simp) h1A with ⟨b2, hb2, h21⟩
            rcases hc2 xB (by simp) hAB.symm with ⟨c2, hc2X, h2B'⟩
            have hc1_yA : c1 = yA := (kill_cross_eq hno h01 h0A h0B h1A h1B hAB hyA hc1X hi01 hj10.symm hj11.symm hd₀m hm1_A h1B').symm
            have hc2_yA : c2 = yA := (kill_cross_eq hno h01 h0A h0B h1A h1B hAB hyA hc2X hi01 hj20.symm hj21.symm hd₀m hm1_A h2B').symm
            have ha1b1 : a1 ≠ b1 := (good_pair_disj_ne (hgood j1) h10 h11 h01 (not_mem_X4 hb1).1.symm).2
            have ha1yA : a1 ≠ yA := hc1_yA ▸ (good_pair_disj_ne (hgood j1) h10 h1B' h0B (not_mem_X4 hc1X).1.symm).2
            have hb1yA : b1 ≠ yA := hc1_yA ▸ (good_pair_disj_ne (hgood j1) h11 h1B' h1B (not_mem_X4 hc1X).2.1.symm).2
            have hb2yA : b2 ≠ yA := hc2_yA ▸ (good_pair_disj_ne (hgood j2) h21 h2B' h1B (not_mem_X4 hc2X).2.1.symm).2
            have h_a1_b2 : a1 = b2 := by
              have t1 := not_mem_X4 ha1; have t2 := not_mem_X4 hb2; have t3 := not_mem_X4 hyA
              rcases kill_three_cross hno h01 h0A h1A ⟨t1.1, t1.2.1, t1.2.2.1⟩ ⟨t2.1, t2.2.1, t2.2.2.1⟩ ⟨t3.1, t3.2.1, t3.2.2.1⟩ hj12 hj11 hj21 h10 h21 hm1_A with h | h | h
              · exact h
              · exact absurd h ha1yA
              · exact absurd h hb2yA
            have h_y0_b1 : y0 = b1 := by
              have t1 := not_mem_X4 hy0; have t2 := not_mem_X4 hb1; have t3 := not_mem_X4 hc2X
              rcases kill_three_cross hno h01 h0B h1B ⟨t1.1, t1.2.1, t1.2.2.2⟩ ⟨t2.1, t2.2.1, t2.2.2.2⟩ ⟨t3.1, t3.2.1, t3.2.2.2⟩ hj11.symm hj21.symm hj12 hm1_0 h11 h2B' with h | h | h
              · exact h
              · exact absurd (h.trans hc2_yA) hy0A
              · exact absurd (h.trans hc2_yA) hb1yA
            have h_y0_b2 : y0 = b2 := by
              have t1 := not_mem_X4 hy0; have t2 := not_mem_X4 hb2; have t3 := not_mem_X4 hc1X
              rcases kill_three_cross hno h01 h0B h1B ⟨t1.1, t1.2.1, t1.2.2.2⟩ ⟨t2.1, t2.2.1, t2.2.2.2⟩ ⟨t3.1, t3.2.1, t3.2.2.2⟩ hj21.symm hj11.symm hj12.symm hm1_0 h21 h1B' with h | h | h
              · exact h
              · exact absurd (h.trans hc1_yA) hy0A
              · exact absurd (h.trans hc1_yA) hb2yA
            exact ha1b1 ((h_a1_b2.trans h_y0_b2.symm).trans h_y0_b1)
          rcases fin5_other_three i₀ i₁ hi01 with ⟨c1, c2, c3, h10', h11', h20', h21', h30', h31', h12', h13', h23'⟩
          have hcl : ∀ j : Fin 5, j ≠ i₀ → j ≠ i₁ →
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xB → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j) ∨
              (∀ x ∈ ({x₀, x₁, xA, xB} : Finset (Fin n)), x ≠ xA → ∃ u, u ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({x, u} : Edge n) ∈ m j) ∨
              (({x₀, x₁} : Edge n) ∈ m j ∧ ∃ w, w ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({xB, w} : Edge n) ∈ m j) ∨
              (({x₀, xA} : Edge n) ∈ m j ∧ ∃ w, w ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({xB, w} : Edge n) ∈ m j) ∨
              (({x₁, xA} : Edge n) ∈ m j ∧ ∃ w, w ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) ∧ ({xB, w} : Edge n) ∈ m j) := by
            intro j _ _
            by_cases hintj : ∃ d ∈ m j, d ⊆ ({x₀, x₁, xA, xB} : Finset (Fin n))
            · rcases hintj with ⟨d, hdm, hdsub⟩
              rcases int_edge_cases ((hgood j).2.1 d hdm) hdsub with rfl | rfl | rfl | rfl | rfl | rfl
              · rcases type1_decomp h01 h0A h0B h1A h1B hAB (hgood j) (hhit' j) hdm with ⟨_, w, _, hw, _, _, hmB⟩
                exact Or.inr (Or.inr (Or.inl ⟨hdm, w, hw, hmB⟩))
              · rcases type1_decomp h0A h01 h0B h1A.symm hAB h1B (hgood j)
                    (by intro e he; convert hhit' j e he using 2; ext z; simp [or_left_comm]) hdm with
                  ⟨_, w, _, hw, _, _, hmB⟩
                exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hdm, w, by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw, hmB⟩)))
              · exact False.elim (hno_int_B j x₀ (by simp) (by rw [pair_comm]; exact hdm))
              · rcases type1_decomp h1A h01.symm h1B h0A.symm hAB h0B (hgood j)
                    (by intro e he; convert hhit' j e he using 2; ext z; simp [or_left_comm]) hdm with
                  ⟨_, w, _, hw, _, _, hmB⟩
                exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hdm, w, by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hw, hmB⟩)))
              · exact False.elim (hno_int_B j x₁ (by simp) (by rw [pair_comm]; exact hdm))
              · exact False.elim (hno_int_B j xA (by simp) (by rw [pair_comm]; exact hdm))
            · push Not at hintj
              rcases hno_t0_miss01 j hintj with hB | hA
              · exact Or.inl hB
              · exact Or.inr (Or.inl hA)
          have hkill_0A_B : ∀ j k : Fin 5, j ≠ i₀ → j ≠ i₁ → k ≠ i₀ → k ≠ i₁ → j ≠ k →
              ({x₀, xA} : Edge n) ∈ m j → ∀ w : Fin n, w ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) → ({xB, w} : Edge n) ∈ m k → False := by
            intro j k _ hj1 hk0 hk1 hjk h0A' w hw hB'
            exact kill_fork hno h01 h0A h0B h1A h1B hAB hy1 hyA hw hy1A hi01 hk0.symm hj1 hjk hk1.symm hd₀m h0A' hm1_1 hm1_A hB'
          have hkill_1A_B : ∀ j k : Fin 5, j ≠ i₀ → j ≠ i₁ → k ≠ i₀ → k ≠ i₁ → j ≠ k →
              ({x₁, xA} : Edge n) ∈ m j → ∀ w : Fin n, w ∉ ({x₀, x₁, xA, xB} : Finset (Fin n)) → ({xB, w} : Edge n) ∈ m k → False := by
            intro j k _ hj1 hk0 hk1 hjk h1A' w hw hB'
            have hsw : ({x₁, x₀, xA, xB} : Finset (Fin n)) = {x₀, x₁, xA, xB} := by ext z; simp [or_left_comm]
            exact kill_fork hno h01.symm h1A h1B h0A h0B hAB (by rwa [hsw]) (by rwa [hsw]) (by rwa [hsw]) hy0A hi01 hk0.symm hj1 hjk hk1.symm
              (by rw [pair_comm]; exact hd₀m) h1A' hm1_0 hm1_A hB'
          rcases hcl c1 h10' h11' with h1B' | h1A' | ⟨h101, w1, hw1, h1Bw⟩ | ⟨h10A, w1, hw1, h1Bw⟩ | ⟨h11A, w1, hw1, h1Bw⟩ <;>
            rcases hcl c2 h20' h21' with h2B' | h2A' | ⟨h201, w2, hw2, h2Bw⟩ | ⟨h20A, w2, hw2, h2Bw⟩ | ⟨h21A, w2, hw2, h2Bw⟩
          · exact hkill_three_missB c1 c2 h10' h11' h20' h21' h12' h1B' h2B'
          · exact hkill_missA_missB c2 c1 h20' h21' h10' h11' h12'.symm h2A' h1B'
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨h301, _, _, _⟩ | ⟨h30A, _, _, _⟩ | ⟨h31A, _, _, _⟩
            · exact hkill_three_missB c1 c3 h10' h11' h30' h31' h13' h1B' h3B'
            · exact hkill_missA_missB c3 c1 h30' h31' h10' h11' h13'.symm h3A' h1B'
            · exact not_three_same_int hgood h01 h0A h0B h1A h1B hAB hhit' hno h20'.symm h30'.symm h23' hd₀m h201 h301
            · exact hkill_0A_B c3 c2 h30' h31' h20' h21' h23'.symm h30A w2 hw2 h2Bw
            · exact hkill_1A_B c3 c2 h30' h31' h20' h21' h23'.symm h31A w2 hw2 h2Bw
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩
            · exact hkill_three_missB c1 c3 h10' h11' h30' h31' h13' h1B' h3B'
            · exact hkill_missA_missB c3 c1 h30' h31' h10' h11' h13'.symm h3A' h1B'
            · exact hkill_0A_B c2 c3 h20' h21' h30' h31' h23' h20A w3 hw3 h3Bw
            · exact hkill_0A_B c2 c3 h20' h21' h30' h31' h23' h20A w3 hw3 h3Bw
            · exact hkill_0A_B c2 c3 h20' h21' h30' h31' h23' h20A w3 hw3 h3Bw
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩
            · exact hkill_three_missB c1 c3 h10' h11' h30' h31' h13' h1B' h3B'
            · exact hkill_missA_missB c3 c1 h30' h31' h10' h11' h13'.symm h3A' h1B'
            · exact hkill_1A_B c2 c3 h20' h21' h30' h31' h23' h21A w3 hw3 h3Bw
            · exact hkill_1A_B c2 c3 h20' h21' h30' h31' h23' h21A w3 hw3 h3Bw
            · exact hkill_1A_B c2 c3 h20' h21' h30' h31' h23' h21A w3 hw3 h3Bw
          · exact hkill_missA_missB c1 c2 h10' h11' h20' h21' h12' h1A' h2B'
          · exact hkill_two_missA c1 c2 h10' h11' h20' h21' h12' h1A' h2A'
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨h301, _, _, _⟩ | ⟨h30A, _, _, _⟩ | ⟨h31A, _, _, _⟩
            · exact hkill_missA_missB c1 c3 h10' h11' h30' h31' h13' h1A' h3B'
            · exact hkill_two_missA c1 c3 h10' h11' h30' h31' h13' h1A' h3A'
            · exact not_three_same_int hgood h01 h0A h0B h1A h1B hAB hhit' hno h20'.symm h30'.symm h23' hd₀m h201 h301
            · exact hkill_0A_B c3 c2 h30' h31' h20' h21' h23'.symm h30A w2 hw2 h2Bw
            · exact hkill_1A_B c3 c2 h30' h31' h20' h21' h23'.symm h31A w2 hw2 h2Bw
          · rcases h1A' xB (by simp) hAB.symm with ⟨w1, hw1, h1Bw⟩
            exact hkill_0A_B c2 c1 h20' h21' h10' h11' h12'.symm h20A w1 hw1 h1Bw
          · rcases h1A' xB (by simp) hAB.symm with ⟨w1, hw1, h1Bw⟩
            exact hkill_1A_B c2 c1 h20' h21' h10' h11' h12'.symm h21A w1 hw1 h1Bw
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨h301, _, _, _⟩ | ⟨h30A, _, _, _⟩ | ⟨h31A, _, _, _⟩
            · exact hkill_three_missB c2 c3 h20' h21' h30' h31' h23' h2B' h3B'
            · exact hkill_missA_missB c3 c2 h30' h31' h20' h21' h23'.symm h3A' h2B'
            · exact not_three_same_int hgood h01 h0A h0B h1A h1B hAB hhit' hno h10'.symm h30'.symm h13' hd₀m h101 h301
            · exact hkill_0A_B c3 c1 h30' h31' h10' h11' h13'.symm h30A w1 hw1 h1Bw
            · exact hkill_1A_B c3 c1 h30' h31' h10' h11' h13'.symm h31A w1 hw1 h1Bw
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨h301, _, _, _⟩ | ⟨h30A, _, _, _⟩ | ⟨h31A, _, _, _⟩
            · exact hkill_missA_missB c2 c3 h20' h21' h30' h31' h23' h2A' h3B'
            · exact hkill_two_missA c2 c3 h20' h21' h30' h31' h23' h2A' h3A'
            · exact not_three_same_int hgood h01 h0A h0B h1A h1B hAB hhit' hno h10'.symm h30'.symm h13' hd₀m h101 h301
            · exact hkill_0A_B c3 c1 h30' h31' h10' h11' h13'.symm h30A w1 hw1 h1Bw
            · exact hkill_1A_B c3 c1 h30' h31' h10' h11' h13'.symm h31A w1 hw1 h1Bw
          · exact not_three_same_int hgood h01 h0A h0B h1A h1B hAB hhit' hno h10'.symm h20'.symm h12' hd₀m h101 h201
          · exact hkill_0A_B c2 c1 h20' h21' h10' h11' h12'.symm h20A w1 hw1 h1Bw
          · exact hkill_1A_B c2 c1 h20' h21' h10' h11' h12'.symm h21A w1 hw1 h1Bw
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩
            · exact hkill_three_missB c2 c3 h20' h21' h30' h31' h23' h2B' h3B'
            · exact hkill_missA_missB c3 c2 h30' h31' h20' h21' h23'.symm h3A' h2B'
            · exact hkill_0A_B c1 c3 h10' h11' h30' h31' h13' h10A w3 hw3 h3Bw
            · exact hkill_0A_B c1 c3 h10' h11' h30' h31' h13' h10A w3 hw3 h3Bw
            · exact hkill_0A_B c1 c3 h10' h11' h30' h31' h13' h10A w3 hw3 h3Bw
          · rcases h2A' xB (by simp) hAB.symm with ⟨w2, hw2, h2Bw⟩
            exact hkill_0A_B c1 c2 h10' h11' h20' h21' h12' h10A w2 hw2 h2Bw
          · exact hkill_0A_B c1 c2 h10' h11' h20' h21' h12' h10A w2 hw2 h2Bw
          · exact hkill_0A_B c1 c2 h10' h11' h20' h21' h12' h10A w2 hw2 h2Bw
          · exact hkill_0A_B c1 c2 h10' h11' h20' h21' h12' h10A w2 hw2 h2Bw
          · rcases hcl c3 h30' h31' with h3B' | h3A' | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩ | ⟨_, w3, hw3, h3Bw⟩
            · exact hkill_three_missB c2 c3 h20' h21' h30' h31' h23' h2B' h3B'
            · exact hkill_missA_missB c3 c2 h30' h31' h20' h21' h23'.symm h3A' h2B'
            · exact hkill_1A_B c1 c3 h10' h11' h30' h31' h13' h11A w3 hw3 h3Bw
            · exact hkill_1A_B c1 c3 h10' h11' h30' h31' h13' h11A w3 hw3 h3Bw
            · exact hkill_1A_B c1 c3 h10' h11' h30' h31' h13' h11A w3 hw3 h3Bw
          · rcases h2A' xB (by simp) hAB.symm with ⟨w2, hw2, h2Bw⟩
            exact hkill_1A_B c1 c2 h10' h11' h20' h21' h12' h11A w2 hw2 h2Bw
          · exact hkill_1A_B c1 c2 h10' h11' h20' h21' h12' h11A w2 hw2 h2Bw
          · exact hkill_1A_B c1 c2 h10' h11' h20' h21' h12' h11A w2 hw2 h2Bw
          · exact hkill_1A_B c1 c2 h10' h11' h20' h21' h12' h11A w2 hw2 h2Bw
        rcases hmissX with hms | hms | hms | hms
        · exact absurd hms hnot_miss0
        · exact absurd hms hnot_miss1
        · exact hcase2B x₃ x₂ h03 h02 h13 h12 h23.symm
            (by ext z; simp [or_comm, or_left_comm])
            (fun x hx hne => by
              have hx' : x ∈ ({x₀, x₁, x₂, x₃} : Finset (Fin n)) := by simpa [or_comm, or_left_comm] using hx
              rcases hcov1 x hx' (hms ▸ hne) with ⟨u, hu, hm⟩
              exact ⟨u, by simpa [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm] using hu, hm⟩)
        · exact hcase2B x₂ x₃ h02 h03 h12 h13 h23 rfl (fun x hx hne => hcov1 x hx (hms ▸ hne))

lemma rainbow7 {n : ℕ} (a : Fin 7 → Matching n) (hgood : ∀ i, Good (a i)) :
    Rainbow 7 a := by
  have h0ne : (a 0).Nonempty := Finset.card_pos.mp (by rw [(hgood 0).1]; omega)
  rcases h0ne with ⟨e₀, he₀⟩
  rcases exists_edge_disjoint_of_card_le_two (hgood 1) (le_of_eq ((hgood 0).2.1 e₀ he₀)) with
    ⟨e₁, he₁, hdisj10⟩
  have hdisj01 : Disjoint e₀ e₁ := hdisj10.symm
  let X : Finset (Fin n) := e₀ ∪ e₁
  have hX4 : X.card = 4 := by
    rw [Finset.card_union_of_disjoint hdisj01, (hgood 0).2.1 e₀ he₀, (hgood 1).2.1 e₁ he₁]
  by_cases hfree : ∃ j : Fin 5, ∃ e ∈ a ⟨j.val + 2, by omega⟩, Disjoint e X
  · rcases hfree with ⟨j, e, he, hde⟩
    have hd0 : Disjoint e₀ e := (Finset.disjoint_union_right.mp hde).1.symm
    have hd1 : Disjoint e₁ e := (Finset.disjoint_union_right.mp hde).2.symm
    exact rainbow_of_three (by decide) (by intro h; have := congrArg Fin.val h; simp at this)
      (by intro h; have := congrArg Fin.val h; simp at this) he₀ he₁ he hdisj01 hd0 hd1
  · push Not at hfree
    let ms : Fin 5 → Matching n := fun j => a ⟨j.val + 2, by omega⟩
    rcases rainbow5_hitting4 hX4 ms (fun j => hgood ⟨j.val + 2, by omega⟩) hfree with
      ⟨c, pick, hinj, hmem, hdisj⟩
    refine ⟨fun k => ⟨(c k).val + 2, by omega⟩, pick, ?_, hmem, hdisj⟩
    intro i j hij
    apply hinj
    apply Fin.ext
    have := congrArg Fin.val hij
    simp at this
    exact this

end PEqualNP.Outside.L_lib_576_aux

theorem PEqualNP.Outside.L_lib_576 : (∀ n : Nat,
  let V := Fin n
  let Edge := Finset V
  let M := Finset Edge
  let good := fun (m : M) => m.card = 3 ∧ (∀ e ∈ m, e.card = 2) ∧
    ∀ e ∈ m, ∀ f ∈ m, e ≠ f → Disjoint e f
  let rainbow := fun (k : Nat) (ms : Fin k → M) =>
    ∃ (c : Fin 3 → Fin k) (pick : Fin 3 → Edge), Function.Injective c ∧
      (∀ j, pick j ∈ ms (c j)) ∧ (∀ i j, i ≠ j → Disjoint (pick i) (pick j))
  (∀ a : Fin 7 → M, (∀ i, good (a i)) → rainbow 7 a) ∧
  (∀ (s : Finset V) (b : Fin 5 → M), (∀ i, good (b i)) →
    (∀ j, ∀ e ∈ b j, (e ∩ s).card = 1) → rainbow 5 b)) := by
  intro n
  exact ⟨PEqualNP.Outside.L_lib_576_aux.rainbow7, PEqualNP.Outside.L_lib_576_aux.rainbow5_bipartite⟩
