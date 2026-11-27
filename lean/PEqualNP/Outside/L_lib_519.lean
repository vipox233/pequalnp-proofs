import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_519

variable {α β : Type} [DecidableEq α] [DecidableEq β]

lemma p1 (cols : α → Finset β) (T S : Finset α) (h : S ≠ T) :
    ∃ w ∈ (S \ T) ∪ (T \ S), cols w \ (T.erase w).biUnion cols ⊆
      (S.biUnion cols \ T.biUnion cols) ∪ (T.biUnion cols \ S.biUnion cols) := by
  by_cases hS : ∃ w, w ∈ S ∧ w ∉ T
  · obtain ⟨w, hwS, hwT⟩ := hS
    refine ⟨w, Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hwS, hwT⟩)), ?_⟩
    intro x hx
    rw [Finset.erase_eq_of_notMem hwT] at hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hwS, hx1⟩, hx2⟩))
  · have hST : ∀ w, w ∈ S → w ∈ T := by
      intro w hw
      by_contra hc
      exact hS ⟨w, hw, hc⟩
    have hex : ∃ w, w ∈ T ∧ w ∉ S := by
      by_contra hc
      apply h
      apply Finset.Subset.antisymm hST
      intro w hw
      by_contra hn
      exact hc ⟨w, hw, hn⟩
    obtain ⟨w, hwT, hwS⟩ := hex
    refine ⟨w, Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hwT, hwS⟩)), ?_⟩
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_sdiff.mp hx
    refine Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨w, hwT, hx1⟩, ?_⟩))
    intro hxS
    obtain ⟨v, hvS, hxv⟩ := Finset.mem_biUnion.mp hxS
    have hvw : v ≠ w := by
      intro e
      exact hwS (e ▸ hvS)
    exact hx2 (Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hvw, hST v hvS⟩, hxv⟩)

lemma tog_ne (T : Finset α) (a : α) : (if a ∈ T then T.erase a else insert a T) ≠ T := by
  by_cases ha : a ∈ T
  · rw [if_pos ha]
    intro e
    have : a ∈ T.erase a := by rw [e]; exact ha
    exact (Finset.notMem_erase a T) this
  · rw [if_neg ha]
    intro e
    exact ha (e ▸ Finset.mem_insert_self a T)

lemma tog_err (cols : α → Finset β) (T : Finset α) (a : α) :
    (((if a ∈ T then T.erase a else insert a T).biUnion cols \ T.biUnion cols) ∪
      (T.biUnion cols \ (if a ∈ T then T.erase a else insert a T).biUnion cols)) =
      cols a \ (T.erase a).biUnion cols := by
  by_cases ha : a ∈ T
  · rw [if_pos ha]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with h1 | h1
      · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp h1
        exact absurd (Finset.biUnion_subset_biUnion_of_subset_left cols (Finset.erase_subset a T) h2) h3
      · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp h1
        obtain ⟨v, hvT, hxv⟩ := Finset.mem_biUnion.mp h2
        by_cases hva : v = a
        · exact Finset.mem_sdiff.mpr ⟨hva ▸ hxv, h3⟩
        · exact absurd (Finset.mem_biUnion.mpr ⟨v, Finset.mem_erase.mpr ⟨hva, hvT⟩, hxv⟩) h3
    · intro hx
      obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨a, ha, h2⟩, h3⟩))
  · rw [if_neg ha, Finset.erase_eq_of_notMem ha]
    ext x
    constructor
    · intro hx
      rcases Finset.mem_union.mp hx with h1 | h1
      · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp h1
        obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp h2
        rcases Finset.mem_insert.mp hv with rfl | hvT
        · exact Finset.mem_sdiff.mpr ⟨hxv, h3⟩
        · exact absurd (Finset.mem_biUnion.mpr ⟨v, hvT, hxv⟩) h3
      · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp h1
        exact absurd (Finset.biUnion_subset_biUnion_of_subset_left cols (Finset.subset_insert a T) h2) h3
    · intro hx
      obtain ⟨h2, h3⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨a, Finset.mem_insert_self a T, h2⟩, h3⟩))

lemma p3 (cols : α → Finset β) (T : Finset α) (key : α) :
    (cols key).card ≤ (cols key \ (T.erase key).biUnion cols).card +
      (T.erase key).sum (fun v => (cols key ∩ cols v).card) := by
  have hsub : cols key ⊆ (cols key \ (T.erase key).biUnion cols) ∪
      (T.erase key).biUnion (fun v => cols key ∩ cols v) := by
    intro x hx
    by_cases hc : x ∈ (T.erase key).biUnion cols
    · obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hc
      exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_inter.mpr ⟨hx, hxv⟩⟩))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hx, hc⟩))
  calc (cols key).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left Finset.card_biUnion_le _

lemma p2 [Fintype α] [Nonempty α] (cols : α → Finset β) (T : Finset α) :
    ∃ anchor : α, (if anchor ∈ T then T.erase anchor else insert anchor T) ≠ T ∧
      (((if anchor ∈ T then T.erase anchor else insert anchor T).biUnion cols \ T.biUnion cols) ∪
        (T.biUnion cols \ (if anchor ∈ T then T.erase anchor else insert anchor T).biUnion cols)) =
        cols anchor \ (T.erase anchor).biUnion cols ∧
      ∀ other : Finset α, other ≠ T → (cols anchor \ (T.erase anchor).biUnion cols).card ≤
        ((other.biUnion cols \ T.biUnion cols) ∪ (T.biUnion cols \ other.biUnion cols)).card := by
  obtain ⟨a, -, ha⟩ := Finset.exists_min_image Finset.univ
    (fun w : α => (cols w \ (T.erase w).biUnion cols).card) Finset.univ_nonempty
  refine ⟨a, tog_ne T a, tog_err cols T a, ?_⟩
  intro other ho
  obtain ⟨w, -, hw⟩ := p1 cols T other ho
  exact le_trans (ha w (Finset.mem_univ w)) (Finset.card_le_card hw)

end PEqualNP.Outside.L_lib_519

theorem PEqualNP.Outside.L_lib_519 : ∀ (k c : ℕ) (cols : Fin (2 ^ k) → Finset (Fin c))
    (T : Finset (Fin (2 ^ k))),
  let cover := fun family : Finset (Fin (2 ^ k)) => family.biUnion cols
  let errors := fun proposed : Finset (Fin (2 ^ k)) =>
    (cover proposed \ cover T) ∪ (cover T \ cover proposed)
  let exposed := fun w : Fin (2 ^ k) => cols w \ cover (T.erase w)
  let toggle := fun changed : Fin (2 ^ k) =>
    if changed ∈ T then T.erase changed else insert changed T
  (∀ S : Finset (Fin (2 ^ k)), S ≠ T →
    ∃ w ∈ (S \ T) ∪ (T \ S), exposed w ⊆ errors S) ∧
  (∃ anchor : Fin (2 ^ k),
    toggle anchor ≠ T ∧ errors (toggle anchor) = exposed anchor ∧
    ∀ other : Finset (Fin (2 ^ k)), other ≠ T →
      (exposed anchor).card ≤ (errors other).card) ∧
  (∀ key : Fin (2 ^ k), (cols key).card ≤ (exposed key).card +
    (T.erase key).sum (fun v => (cols key ∩ cols v).card)) := by
  intro k c cols T cover errors exposed toggle
  exact ⟨fun S hS => PEqualNP.Outside.L_lib_519.p1 cols T S hS,
    PEqualNP.Outside.L_lib_519.p2 cols T,
    fun key => PEqualNP.Outside.L_lib_519.p3 cols T key⟩
