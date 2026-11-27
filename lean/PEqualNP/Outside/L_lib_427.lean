import PEqualNP.Defs
import Mathlib.Combinatorics.SetFamily.LYM

namespace PEqualNP.Outside.L_lib_427_aux

open Finset

def code {n d : ℕ} (A : Fin d → Finset (Fin n)) (i : Fin n) : Finset (Fin d) :=
  Finset.univ.filter (fun t => i ∈ A t)

theorem mem_code {n d : ℕ} (A : Fin d → Finset (Fin n)) (i : Fin n) (t : Fin d) :
    t ∈ code A i ↔ i ∈ A t := by
  simp [code]

theorem forward (n d : ℕ) (A B : Fin d → Finset (Fin n))
    (hAB : ∀ i j : Fin n, i ≠ j ↔ ∃ t, i ∈ A t ∧ j ∈ B t) : n ≤ Nat.choose d (d / 2) := by
  have key : ∀ i j : Fin n, code A i ⊆ code A j → i = j := by
    intro i j hsub
    by_contra hne
    obtain ⟨t, hi, hj⟩ := (hAB i j).1 hne
    have h1 : t ∈ code A j := hsub ((mem_code A i t).2 hi)
    rw [mem_code] at h1
    exact (hAB j j).2 ⟨t, h1, hj⟩ rfl
  have hinj : Function.Injective (code A) := by
    intro i j h
    apply key i j
    rw [h]
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (Finset.univ.image (code A))) := by
    intro a ha b hb hab hsub
    rw [Finset.mem_coe, Finset.mem_image] at ha hb
    obtain ⟨i, -, rfl⟩ := ha
    obtain ⟨j, -, rfl⟩ := hb
    exact hab (by rw [key i j hsub])
  have h2 := hanti.sperner
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fin] at h2
  exact h2

theorem backward (n d : ℕ) (hn : n ≤ Nat.choose d (d / 2)) :
    ∃ (A B : Fin d → Finset (Fin n)), ∀ i j : Fin n, i ≠ j ↔ ∃ t, i ∈ A t ∧ j ∈ B t := by
  have hcard : Fintype.card (Finset.powersetCard (d / 2) (Finset.univ : Finset (Fin d))) =
      Nat.choose d (d / 2) := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  let e := Fintype.equivFinOfCardEq hcard
  let g : Fin n → Finset (Fin d) := fun i => (e.symm (Fin.castLE hn i)).1
  have hgcard : ∀ i, (g i).card = d / 2 := by
    intro i
    exact (Finset.mem_powersetCard.1 (e.symm (Fin.castLE hn i)).2).2
  have hginj : ∀ i j, g i = g j → i = j := by
    intro i j hij
    have h1 := Subtype.ext hij
    have h2 := e.symm.injective h1
    apply Fin.ext
    have h3 := congrArg Fin.val h2
    simpa using h3
  refine ⟨fun t => Finset.univ.filter (fun i => t ∈ g i),
    fun t => Finset.univ.filter (fun j => t ∉ g j), ?_⟩
  intro i j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hne
    by_contra hc
    have hsub : g i ⊆ g j := by
      intro t ht
      by_contra hn
      exact hc ⟨t, ht, hn⟩
    have heq : g i = g j := Finset.eq_of_subset_of_card_le hsub (by rw [hgcard, hgcard])
    exact hne (hginj i j heq)
  · rintro ⟨t, hi, hj⟩ hij
    rw [hij] at hi
    exact hj hi

end PEqualNP.Outside.L_lib_427_aux

theorem PEqualNP.Outside.L_lib_427 :
∀ n d : ℕ,
  (∃ (A B : Fin d → Finset (Fin n)),
    ∀ i j : Fin n, i ≠ j ↔ ∃ t, i ∈ A t ∧ j ∈ B t) ↔
  n ≤ Nat.choose d (d / 2) := by
  intro n d
  constructor
  · rintro ⟨A, B, hAB⟩
    exact PEqualNP.Outside.L_lib_427_aux.forward n d A B hAB
  · intro hn
    exact PEqualNP.Outside.L_lib_427_aux.backward n d hn
