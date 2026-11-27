import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_479_aux

open Finset

def sat {n m : ℕ} (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n))
    (X : Finset (Fin n)) : Prop :=
  ∀ i, B i ⊆ X → ∃ v ∈ X, h i = some v

def step {n m : ℕ} (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n))
    (X : Finset (Fin n)) : Finset (Fin n) :=
  X ∪ Finset.univ.filter (fun v => ∃ i, h i = some v ∧ B i ⊆ X)

theorem iter_sub_model {n m : ℕ} (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n))
    (Y : Finset (Fin n)) (hY : sat B h Y) :
    ∀ k : ℕ, ((step B h)^[k]) ∅ ⊆ Y
  | 0 => empty_subset Y
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    have ih := iter_sub_model B h Y hY k
    intro v hv
    rw [step, mem_union] at hv
    rcases hv with hv | hv
    · exact ih hv
    · obtain ⟨i, hi, hBi⟩ := (mem_filter.mp hv).2
      obtain ⟨v', hv'Y, hi'⟩ := hY i (hBi.trans ih)
      have heq : v = v' := Option.some.inj (hi.symm.trans hi')
      rwa [heq]

theorem fixed_or_card {n m : ℕ} (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n)) :
    ∀ k : ℕ, step B h (((step B h)^[k]) ∅) = ((step B h)^[k]) ∅ ∨
      k ≤ (((step B h)^[k]) ∅).card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    rcases fixed_or_card B h k with hfix | hcard
    · left
      rw [Function.iterate_succ_apply', hfix, hfix]
    · by_cases hfix : step B h (((step B h)^[k]) ∅) = ((step B h)^[k]) ∅
      · left
        rw [Function.iterate_succ_apply', hfix, hfix]
      · right
        rw [Function.iterate_succ_apply']
        have hsub : ((step B h)^[k]) ∅ ⊆ step B h (((step B h)^[k]) ∅) := subset_union_left
        have hssub : ((step B h)^[k]) ∅ ⊂ step B h (((step B h)^[k]) ∅) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun e => hfix e.symm⟩
        have hlt : (((step B h)^[k]) ∅).card < (step B h (((step B h)^[k]) ∅)).card :=
          card_lt_card hssub
        omega

theorem step_fixed_n {n m : ℕ} (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n)) :
    step B h (((step B h)^[n]) ∅) = ((step B h)^[n]) ∅ := by
  rcases fixed_or_card B h n with hfix | hcard
  · exact hfix
  · have hsub : ((step B h)^[n]) ∅ ⊆ step B h (((step B h)^[n]) ∅) := subset_union_left
    have hle : (step B h (((step B h)^[n]) ∅)).card ≤ n := by
      have := card_le_univ (step B h (((step B h)^[n]) ∅))
      rwa [Fintype.card_fin] at this
    exact (eq_of_subset_of_card_le hsub (hle.trans hcard)).symm

theorem main (n m : ℕ) (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n)) :
    (∃ X, sat B h X) ↔ (sat B h (((step B h)^[n]) ∅) ∧ ∀ Y, sat B h Y → ((step B h)^[n]) ∅ ⊆ Y) := by
  constructor
  · rintro ⟨X, hX⟩
    refine ⟨?_, fun Y hY => iter_sub_model B h Y hY n⟩
    intro i hBi
    have hLX : ((step B h)^[n]) ∅ ⊆ X := iter_sub_model B h X hX n
    obtain ⟨v, _, hi⟩ := hX i (hBi.trans hLX)
    have hv : v ∈ step B h (((step B h)^[n]) ∅) := by
      rw [step, mem_union]
      right
      exact mem_filter.mpr ⟨mem_univ v, i, hi, hBi⟩
    rw [step_fixed_n] at hv
    exact ⟨v, hv, hi⟩
  · rintro ⟨hL, _⟩
    exact ⟨((step B h)^[n]) ∅, hL⟩

end PEqualNP.Outside.L_lib_479_aux

theorem PEqualNP.Outside.L_lib_479 : ∀ (n m : ℕ) (B : Fin m → Finset (Fin n)) (h : Fin m → Option (Fin n)),
  let sat := fun X : Finset (Fin n) =>
    ∀ i, B i ⊆ X → ∃ v ∈ X, h i = some v
  let step := fun X : Finset (Fin n) =>
    X ∪ Finset.univ.filter (fun v => ∃ i, h i = some v ∧ B i ⊆ X)
  let L := (step^[n]) ∅
  (∃ X, sat X) ↔ (sat L ∧ ∀ Y, sat Y → L ⊆ Y) := by
  intro n m B h
  exact PEqualNP.Outside.L_lib_479_aux.main n m B h
