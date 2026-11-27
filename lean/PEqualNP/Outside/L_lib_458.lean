import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_458

open Finset Equiv

/-- The product over a permutation as an alternating sum over the forbidden squares it hits. -/
theorem prod_eq {n : ℕ} (F : Finset (Fin n × Fin n)) (σ : Perm (Fin n)) :
    (∏ i, (if (i, σ i) ∈ F then (0 : ℤ) else 1)) =
      ∑ T ∈ F.powerset, if (∀ p ∈ T, σ p.1 = p.2) then (-1 : ℤ) ^ T.card else 0 := by
  have h1 : F.powerset.filter (fun T => ∀ p ∈ T, σ p.1 = p.2) =
      (F.filter (fun p => σ p.1 = p.2)).powerset := by
    ext T
    simp only [mem_filter, mem_powerset, subset_iff]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      exact ⟨h1 hp, h2 p hp⟩
    · intro h
      exact ⟨fun p hp => (h hp).1, fun p hp => (h hp).2⟩
  rw [← sum_filter, h1, sum_powerset_neg_one_pow_card]
  by_cases h : ∃ i, (i, σ i) ∈ F
  · obtain ⟨i, hi⟩ := h
    have hne : F.filter (fun p => σ p.1 = p.2) ≠ ∅ := by
      intro he
      have : (i, σ i) ∈ F.filter (fun p => σ p.1 = p.2) := mem_filter.2 ⟨hi, rfl⟩
      rw [he] at this
      simp at this
    rw [ite_eq_right hne]
    exact prod_eq_zero (mem_univ i) (ite_eq_left hi)
  · push Not at h
    have he : F.filter (fun p => σ p.1 = p.2) = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp hs
      apply h p.1
      rw [hs]
      exact hp
    rw [ite_eq_left he]
    exact prod_eq_one (fun i _ => ite_eq_right (h i))

/-- No permutation passes through two squares of one row or one column. -/
theorem card_bad {n : ℕ} (T : Finset (Fin n × Fin n))
    (hT : ¬ ((T.image Prod.fst).card = T.card ∧ (T.image Prod.snd).card = T.card)) :
    (univ.filter (fun σ : Perm (Fin n) => ∀ p ∈ T, σ p.1 = p.2)).card = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro σ _ hσ
  apply hT
  constructor
  · rw [card_image_iff]
    intro p hp q hq hpq
    have h2 : p.2 = q.2 := by rw [← hσ p hp, ← hσ q hq, hpq]
    exact Prod.ext hpq h2
  · rw [card_image_iff]
    intro p hp q hq hpq
    have h1 : p.1 = q.1 := σ.injective (by rw [hσ p hp, hσ q hq]; exact hpq)
    exact Prod.ext h1 hpq

/-- A placement extends to a permutation. -/
theorem exists_ext {n : ℕ} (T : Finset (Fin n × Fin n))
    (h1 : Set.InjOn Prod.fst (T : Set (Fin n × Fin n)))
    (h2 : Set.InjOn Prod.snd (T : Set (Fin n × Fin n))) :
    ∃ τ : Perm (Fin n), ∀ p ∈ T, τ p.1 = p.2 := by
  let fA : {p // p ∈ T} → {a // a ∈ T.image Prod.fst} :=
    fun p => ⟨p.1.1, mem_image_of_mem _ p.2⟩
  let fB : {p // p ∈ T} → {b // b ∈ T.image Prod.snd} :=
    fun p => ⟨p.1.2, mem_image_of_mem _ p.2⟩
  have hA : Function.Bijective fA := by
    constructor
    · intro p q hpq
      exact Subtype.ext (h1 p.2 q.2 (congrArg Subtype.val hpq))
    · rintro ⟨a, ha⟩
      obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
      exact ⟨⟨p, hp⟩, rfl⟩
  have hB : Function.Bijective fB := by
    constructor
    · intro p q hpq
      exact Subtype.ext (h2 p.2 q.2 (congrArg Subtype.val hpq))
    · rintro ⟨b, hb⟩
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hb
      exact ⟨⟨p, hp⟩, rfl⟩
  let e : {a // a ∈ T.image Prod.fst} ≃ {b // b ∈ T.image Prod.snd} :=
    (Equiv.ofBijective fA hA).symm.trans (Equiv.ofBijective fB hB)
  refine ⟨e.extendSubtype, fun p hp => ?_⟩
  rw [extendSubtype_apply_of_mem e p.1 (mem_image_of_mem _ hp)]
  have : (Equiv.ofBijective fA hA).symm ⟨p.1, mem_image_of_mem _ hp⟩ = ⟨p, hp⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp only [e, Equiv.trans_apply, this]
  rfl

/-- The permutations through a placement: (n - k)! of them. -/
theorem card_good {n : ℕ} (T : Finset (Fin n × Fin n))
    (hT : (T.image Prod.fst).card = T.card ∧ (T.image Prod.snd).card = T.card) :
    (univ.filter (fun σ : Perm (Fin n) => ∀ p ∈ T, σ p.1 = p.2)).card = (n - T.card).factorial := by
  obtain ⟨τ, hτ⟩ := exists_ext T (card_image_iff.1 hT.1) (card_image_iff.1 hT.2)
  set A := T.image Prod.fst with hAdef
  have key : ∀ σ : Perm (Fin n), (∀ p ∈ T, σ p.1 = p.2) ↔
      (∀ a, ¬ (a ∉ A) → (Equiv.mulLeft τ⁻¹ σ) a = a) := by
    intro σ
    constructor
    · intro hσ a ha
      rw [not_not] at ha
      obtain ⟨p, hp, rfl⟩ := mem_image.1 ha
      show τ⁻¹ (σ p.1) = p.1
      rw [Equiv.Perm.inv_eq_iff_eq, hσ p hp, hτ p hp]
    · intro h p hp
      have := h p.1 (not_not.2 (mem_image_of_mem _ hp))
      change τ⁻¹ (σ p.1) = p.1 at this
      rw [Equiv.Perm.inv_eq_iff_eq] at this
      rw [this, hτ p hp]
  have e1 : {σ : Perm (Fin n) // ∀ p ∈ T, σ p.1 = p.2} ≃
      {f : Perm (Fin n) // ∀ a, ¬ (a ∉ A) → f a = a} :=
    Equiv.subtypeEquiv (Equiv.mulLeft τ⁻¹) key
  have e2 := e1.trans (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ A)).symm
  rw [← Fintype.card_subtype, Fintype.card_congr e2, Fintype.card_perm, Fintype.card_subtype,
    filter_not, filter_mem_eq_inter, univ_inter, card_univ_sdiff,
    Fintype.card_fin, hT.1]

end PEqualNP.Outside.L_lib_458

theorem PEqualNP.Outside.L_lib_458 : ∀ (n : ℕ) (forbidden : Finset (Fin n × Fin n)),
  let M : Matrix (Fin n) (Fin n) ℤ := fun i j => if (i,j) ∈ forbidden then 0 else 1
  let placements := forbidden.powerset.filter (fun P : Finset (Fin n × Fin n) =>
    (P.image Prod.fst).card = P.card ∧ (P.image Prod.snd).card = P.card)
  M.permanent = ∑ S ∈ placements, (-1 : ℤ)^S.card * (Nat.factorial (n-S.card) : ℤ) := by
  intro n F M placements
  have hperm : M.permanent = ∑ σ : Equiv.Perm (Fin n), ∏ i, (if (i, σ i) ∈ F then (0 : ℤ) else 1) := by
    rw [Matrix.permanent, ← Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin n)))]
    apply Finset.sum_congr rfl
    intro σ _
    rw [← Equiv.prod_comp σ]
    apply Finset.prod_congr rfl
    intro i _
    simp [M]
  rw [hperm]
  simp only [PEqualNP.Outside.L_lib_458.prod_eq]
  rw [Finset.sum_comm]
  simp only [placements]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  split_ifs with hT
  · rw [PEqualNP.Outside.L_lib_458.card_good T hT]
  · rw [PEqualNP.Outside.L_lib_458.card_bad T hT]
    simp
