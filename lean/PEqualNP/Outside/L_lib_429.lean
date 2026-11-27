import PEqualNP.Defs
import Mathlib.Combinatorics.Hall.Basic

namespace PEqualNP.Outside.L_lib_429_aux

open Finset

def nbr {m n : ℕ} (M : Fin m → Fin n → Bool) (X : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∃ a ∈ X, M a x = true)

theorem konig (m n : ℕ) (M : Fin m → Fin n → Bool) :
    ∃ (R : Finset (Fin m)) (C : Finset (Fin n)) (S : Finset (Fin m × Fin n)),
      (∀ a x, M a x = true → a ∈ R ∨ x ∈ C) ∧
      (∀ e ∈ S, M e.1 e.2 = true) ∧ Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) ∧
      Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) ∧ R.card + C.card ≤ S.card := by
  obtain ⟨X0, -, hX0⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset (Fin m)))
    (fun X => (X.card : ℤ) - ((nbr M X).card : ℤ)) Finset.univ_nonempty
  have hemp := hX0 ∅ (Finset.mem_univ _)
  have hnb0 : (nbr M ∅).card = 0 := by
    rw [Finset.card_eq_zero]
    ext x
    simp [nbr]
  simp only [Finset.card_empty, hnb0, Nat.cast_zero, sub_zero] at hemp
  set d := X0.card - (nbr M X0).card with hd
  let t : Fin m → Finset (Fin n ⊕ Fin d) := fun a =>
    (Finset.univ.filter (fun x => M a x = true)).disjSum Finset.univ
  have hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with hs | hs
    · rw [hs]
      simp
    · obtain ⟨a0, ha0⟩ := hs
      have hsub : (nbr M s).disjSum (Finset.univ : Finset (Fin d)) ⊆ s.biUnion t := by
        intro z hz
        rw [Finset.mem_biUnion]
        rcases z with x | z
        · rw [Finset.inl_mem_disjSum] at hz
          simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and] at hz
          obtain ⟨a, ha, hax⟩ := hz
          refine ⟨a, ha, ?_⟩
          simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hax
        · refine ⟨a0, ha0, ?_⟩
          simp only [t, Finset.inr_mem_disjSum, Finset.mem_univ]
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at h1
      have h2 := hX0 s (Finset.mem_univ _)
      omega
  obtain ⟨f, hfinj, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hfM : ∀ a x, f a = Sum.inl x → M a x = true := by
    intro a x hax
    have h1 := hft a
    rw [hax] at h1
    simp only [t, Finset.inl_mem_disjSum, Finset.mem_filter, Finset.mem_univ, true_and] at h1
    exact h1
  let S : Finset (Fin m × Fin n) := Finset.univ.filter (fun e => f e.1 = Sum.inl e.2)
  have hmemS : ∀ e, e ∈ S ↔ f e.1 = Sum.inl e.2 := by
    intro e
    simp [S]
  have hinj1 : Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) := by
    intro e he e' he' heq
    rw [Finset.mem_coe, hmemS] at he he'
    have h1 : (Sum.inl e.2 : Fin n ⊕ Fin d) = Sum.inl e'.2 := by
      rw [← he, ← he', heq]
    exact Prod.ext heq (Sum.inl_injective h1)
  have hinj2 : Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) := by
    intro e he e' he' heq
    rw [Finset.mem_coe, hmemS] at he he'
    have h1 : f e.1 = f e'.1 := by
      rw [he, he', heq]
    exact Prod.ext (hfinj h1) heq
  let D : Finset (Fin m) := Finset.univ.filter (fun a => ∃ z, f a = Sum.inr z)
  have hD : D.card ≤ d := by
    have h1 : D.image f ⊆ (∅ : Finset (Fin n)).disjSum (Finset.univ : Finset (Fin d)) := by
      intro w hw
      rw [Finset.mem_image] at hw
      obtain ⟨a, ha, rfl⟩ := hw
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      obtain ⟨z, hz⟩ := ha
      rw [hz, Finset.inr_mem_disjSum]
      exact Finset.mem_univ z
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ hfinj, Finset.card_disjSum, Finset.card_empty,
      Finset.card_univ, Fintype.card_fin] at h2
    omega
  have hcov : (Finset.univ : Finset (Fin m)) ⊆ D ∪ S.image Prod.fst := by
    intro a _
    rw [Finset.mem_union]
    rcases hfa : f a with x | z
    · right
      rw [Finset.mem_image]
      exact ⟨(a, x), (hmemS (a, x)).2 hfa, rfl⟩
    · left
      simp only [D, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, hfa⟩
  have hcard1 := Finset.card_le_card hcov
  have hcard2 := Finset.card_union_le D (S.image Prod.fst)
  rw [Finset.card_image_of_injOn hinj1] at hcard2
  rw [Finset.card_univ, Fintype.card_fin] at hcard1
  refine ⟨Finset.univ \ X0, nbr M X0, S, ?_, ?_, hinj1, hinj2, ?_⟩
  · intro a x hax
    by_cases ha : a ∈ X0
    · right
      simp only [nbr, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a, ha, hax⟩
    · left
      simp [ha]
  · intro e he
    exact hfM e.1 e.2 ((hmemS e).1 he)
  · rw [Finset.card_sdiff_of_subset (Finset.subset_univ X0), Finset.card_univ, Fintype.card_fin]
    have hX0le : X0.card ≤ m := by
      have h3 := Finset.card_le_card (Finset.subset_univ X0)
      rw [Finset.card_univ, Fintype.card_fin] at h3
      exact h3
    omega

theorem transfer {m n : ℕ} (M : Fin m → Fin n → Bool) {ι : Type} [Fintype ι] (q : ℕ)
    (hq : Fintype.card ι ≤ q) (rA : ι → Finset (Fin m)) (rB : ι → Finset (Fin n))
    (h : ∀ i j, M i j = true ↔ ∃ s, i ∈ rA s ∧ j ∈ rB s) :
    ∃ (A : Fin q → Finset (Fin m)) (B : Fin q → Finset (Fin n)),
      ∀ i j, M i j = true ↔ ∃ t, i ∈ A t ∧ j ∈ B t := by
  let e := Fintype.equivFin ι
  refine ⟨fun t => if hlt : t.val < Fintype.card ι then rA (e.symm ⟨t.val, hlt⟩) else ∅,
    fun t => if hlt : t.val < Fintype.card ι then rB (e.symm ⟨t.val, hlt⟩) else ∅, ?_⟩
  intro i j
  constructor
  · intro hij
    obtain ⟨s, hi, hj⟩ := (h i j).1 hij
    have hl : (e s).val < Fintype.card ι := (e s).isLt
    refine ⟨⟨(e s).val, by omega⟩, ?_⟩
    simp only [hl, ↓reduceDIte, Fin.eta, Equiv.symm_apply_apply]
    exact ⟨hi, hj⟩
  · rintro ⟨t, hi, hj⟩
    by_cases hlt : t.val < Fintype.card ι
    · simp only [hlt, ↓reduceDIte] at hi hj
      exact (h i j).2 ⟨_, hi, hj⟩
    · simp only [hlt, ↓reduceDIte] at hi
      exact absurd hi (Finset.notMem_empty i)

theorem forward (m n q : ℕ) (M : Fin m → Fin n → Bool)
    (hc4 : ∀ a b x y, M a x = true → M a y = true → M b x = true → M b y = true →
      a = b ∨ x = y)
    (A : Fin q → Finset (Fin m)) (B : Fin q → Finset (Fin n))
    (hAB : ∀ i j, M i j = true ↔ ∃ t, i ∈ A t ∧ j ∈ B t)
    (S : Finset (Fin m × Fin n)) (hS : ∀ e ∈ S, M e.1 e.2 = true)
    (h1 : Set.InjOn Prod.fst (S : Set (Fin m × Fin n)))
    (h2 : Set.InjOn Prod.snd (S : Set (Fin m × Fin n))) : S.card ≤ q := by
  have hch : ∀ e : {e // e ∈ S}, ∃ t, e.1.1 ∈ A t ∧ e.1.2 ∈ B t := by
    intro e
    exact (hAB e.1.1 e.1.2).1 (hS e.1 e.2)
  choose g hg using hch
  have hinj : Function.Injective g := by
    intro e e' heq
    have he1 := hg e
    have he2 := hg e'
    rw [heq] at he1
    have hm1 : M e.1.1 e'.1.2 = true := (hAB e.1.1 e'.1.2).2 ⟨g e', he1.1, he2.2⟩
    have hm2 : M e'.1.1 e.1.2 = true := (hAB e'.1.1 e.1.2).2 ⟨g e', he2.1, he1.2⟩
    apply Subtype.ext
    rcases hc4 e.1.1 e'.1.1 e.1.2 e'.1.2 (hS e.1 e.2) hm1 hm2 (hS e'.1 e'.2) with hh | hh
    · exact h1 (Finset.mem_coe.2 e.2) (Finset.mem_coe.2 e'.2) hh
    · exact h2 (Finset.mem_coe.2 e.2) (Finset.mem_coe.2 e'.2) hh
  have h3 := Fintype.card_le_of_injective g hinj
  rw [Fintype.card_coe, Fintype.card_fin] at h3
  exact h3

theorem backward (m n q : ℕ) (M : Fin m → Fin n → Bool)
    (H : ∀ S : Finset (Fin m × Fin n),
      (∀ e ∈ S, M e.1 e.2 = true) → Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) →
      Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) → S.card ≤ q) :
    ∃ (A : Fin q → Finset (Fin m)) (B : Fin q → Finset (Fin n)),
      ∀ i j, M i j = true ↔ ∃ t, i ∈ A t ∧ j ∈ B t := by
  obtain ⟨R, C, S, hcov, hS, h1, h2, hle⟩ := konig m n M
  have hSq := H S hS h1 h2
  have hcard : Fintype.card ({a // a ∈ R} ⊕ {x // x ∈ C}) ≤ q := by
    rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe]
    omega
  refine transfer M q hcard
    (Sum.elim (fun a => {a.1}) (fun x => Finset.univ.filter (fun i => M i x.1 = true)))
    (Sum.elim (fun a => Finset.univ.filter (fun j => M a.1 j = true)) (fun x => {x.1})) ?_
  intro i j
  constructor
  · intro hij
    rcases hcov i j hij with hi | hj
    · refine ⟨Sum.inl ⟨i, hi⟩, ?_, ?_⟩
      · simp
      · simp [hij]
    · refine ⟨Sum.inr ⟨j, hj⟩, ?_, ?_⟩
      · simp [hij]
      · simp
  · rintro ⟨s, hi, hj⟩
    rcases s with ⟨a, ha⟩ | ⟨x, hx⟩
    · simp only [Sum.elim_inl, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi hj
      rw [hi]
      exact hj
    · simp only [Sum.elim_inr, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
        true_and] at hi hj
      rw [hj]
      exact hi

end PEqualNP.Outside.L_lib_429_aux

theorem PEqualNP.Outside.L_lib_429 :
∀ (m n q : ℕ) (M : Fin m → Fin n → Bool),
  (∀ a b x y, M a x = true → M a y = true → M b x = true → M b y = true →
    a = b ∨ x = y) →
  ((∃ (A : Fin q → Finset (Fin m)) (B : Fin q → Finset (Fin n)),
    ∀ i j, M i j = true ↔ ∃ t, i ∈ A t ∧ j ∈ B t) ↔
    ∀ S : Finset (Fin m × Fin n),
      (∀ e ∈ S, M e.1 e.2 = true) → Set.InjOn Prod.fst (S : Set (Fin m × Fin n)) →
      Set.InjOn Prod.snd (S : Set (Fin m × Fin n)) → S.card ≤ q) := by
  intro m n q M hc4
  constructor
  · rintro ⟨A, B, hAB⟩ S hS h1 h2
    exact PEqualNP.Outside.L_lib_429_aux.forward m n q M hc4 A B hAB S hS h1 h2
  · intro H
    exact PEqualNP.Outside.L_lib_429_aux.backward m n q M H
