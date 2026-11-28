import Mathlib
import PEqualNP.Defs

open Module

namespace PEqualNP.Outside.L_lib_971_aux

variable {K Y : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]

noncomputable def rk {α : Type*} (K : Type*) [Field K] [Module K Y] (v : α → Y) (X : Finset α) : ℕ :=
  finrank K (Submodule.span K (v '' (X : Set α)))

theorem rk_mono {α : Type*} (v : α → Y) {X X' : Finset α} (h : X ⊆ X') :
    rk K v X ≤ rk K v X' :=
  Submodule.finrank_mono (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 h)))

theorem rk_submod {α : Type*} [DecidableEq α] (v : α → Y) (X1 X2 : Finset α) :
    rk K v (X1 ∪ X2) + rk K v (X1 ∩ X2) ≤ rk K v X1 + rk K v X2 := by
  have h1 : Submodule.span K (v '' ((X1 ∪ X2 : Finset α) : Set α)) =
      Submodule.span K (v '' (X1 : Set α)) ⊔ Submodule.span K (v '' (X2 : Set α)) := by
    rw [Finset.coe_union, Set.image_union, Submodule.span_union]
  have h2 : Submodule.span K (v '' ((X1 ∩ X2 : Finset α) : Set α)) ≤
      Submodule.span K (v '' (X1 : Set α)) ⊓ Submodule.span K (v '' (X2 : Set α)) :=
    le_inf (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 Finset.inter_subset_left)))
      (Submodule.span_mono (Set.image_mono (Finset.coe_subset.2 Finset.inter_subset_right)))
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K (v '' (X1 : Set α)))
    (Submodule.span K (v '' (X2 : Set α)))
  have h4 := Submodule.finrank_mono h2
  unfold rk
  rw [h1]
  omega

theorem exch {α β : Type*} [DecidableEq α] [DecidableEq β] (v : α → Y) (E : Finset β) (t : ℕ)
    (f : β → Finset α) (e : β) (he : e ∈ E) (x y : α) (hxy : x ≠ y)
    (H : ∀ J ⊆ E, t ≤ (E \ J).card + rk K v (J.biUnion f)) :
    (∀ J ⊆ E, t ≤ (E \ J).card +
      rk K v (J.biUnion (fun e' => if e' = e then (f e).erase x else f e'))) ∨
    (∀ J ⊆ E, t ≤ (E \ J).card +
      rk K v (J.biUnion (fun e' => if e' = e then (f e).erase y else f e'))) := by
  by_contra hc
  push_neg at hc
  obtain ⟨⟨J1, hJ1, h1⟩, ⟨J2, hJ2, h2⟩⟩ := hc
  have eJ1 : e ∈ J1 := by
    by_contra hn
    have : J1.biUnion (fun e' => if e' = e then (f e).erase x else f e') = J1.biUnion f := by
      apply Finset.biUnion_congr rfl
      intro a ha
      rw [if_neg (fun h : a = e => hn (h ▸ ha))]
    rw [this] at h1
    have := H J1 hJ1
    omega
  have eJ2 : e ∈ J2 := by
    by_contra hn
    have : J2.biUnion (fun e' => if e' = e then (f e).erase y else f e') = J2.biUnion f := by
      apply Finset.biUnion_congr rfl
      intro a ha
      rw [if_neg (fun h : a = e => hn (h ▸ ha))]
    rw [this] at h2
    have := H J2 hJ2
    omega
  set X1 := J1.biUnion (fun e' => if e' = e then (f e).erase x else f e') with hX1
  set X2 := J2.biUnion (fun e' => if e' = e then (f e).erase y else f e') with hX2
  have hU : (J1 ∪ J2).biUnion f ⊆ X1 ∪ X2 := by
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨e', he', ha⟩ := ha
    rw [Finset.mem_union, hX1, hX2, Finset.mem_biUnion, Finset.mem_biUnion]
    by_cases hee : e' = e
    · subst hee
      by_cases hax : a = x
      · right
        refine ⟨e', eJ2, ?_⟩
        rw [if_pos rfl, Finset.mem_erase]
        exact ⟨fun h => hxy (hax ▸ h), ha⟩
      · left
        refine ⟨e', eJ1, ?_⟩
        rw [if_pos rfl, Finset.mem_erase]
        exact ⟨hax, ha⟩
    · rcases Finset.mem_union.1 he' with h | h
      · left
        exact ⟨e', h, by rw [if_neg hee]; exact ha⟩
      · right
        exact ⟨e', h, by rw [if_neg hee]; exact ha⟩
  have hI : ((J1 ∩ J2).erase e).biUnion f ⊆ X1 ∩ X2 := by
    intro a ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨e', he', ha⟩ := ha
    rw [Finset.mem_erase, Finset.mem_inter] at he'
    rw [Finset.mem_inter, hX1, hX2, Finset.mem_biUnion, Finset.mem_biUnion]
    exact ⟨⟨e', he'.2.1, by rw [if_neg he'.1]; exact ha⟩,
      ⟨e', he'.2.2, by rw [if_neg he'.1]; exact ha⟩⟩
  have hUE : J1 ∪ J2 ⊆ E := Finset.union_subset hJ1 hJ2
  have hKE : (J1 ∩ J2).erase e ⊆ E :=
    (Finset.erase_subset _ _).trans (Finset.inter_subset_left.trans hJ1)
  have a1 := H (J1 ∪ J2) hUE
  have a2 := H _ hKE
  have a3 := rk_mono (K := K) v hU
  have a4 := rk_mono (K := K) v hI
  have a5 := rk_submod (K := K) v X1 X2
  have c1 := Finset.card_sdiff_add_card_eq_card hJ1
  have c2 := Finset.card_sdiff_add_card_eq_card hJ2
  have c3 := Finset.card_sdiff_add_card_eq_card hUE
  have c4 := Finset.card_sdiff_add_card_eq_card hKE
  have c5 := Finset.card_union_add_card_inter J1 J2
  have c6 := Finset.card_erase_add_one (Finset.mem_inter.2 ⟨eJ1, eJ2⟩)
  omega

theorem shrink {α β : Type*} [DecidableEq α] [DecidableEq β] (v : α → Y) (E : Finset β)
    (t : ℕ) : ∀ (N : ℕ) (f : β → Finset α), ∑ e ∈ E, (f e).card ≤ N →
    (∀ J ⊆ E, t ≤ (E \ J).card + rk K v (J.biUnion f)) →
    ∃ g : β → Finset α, (∀ e ∈ E, g e ⊆ f e ∧ (g e).card ≤ 1) ∧ t ≤ rk K v (E.biUnion g) := by
  have base : ∀ f : β → Finset α, (∀ e ∈ E, (f e).card ≤ 1) →
      (∀ J ⊆ E, t ≤ (E \ J).card + rk K v (J.biUnion f)) →
      ∃ g : β → Finset α, (∀ e ∈ E, g e ⊆ f e ∧ (g e).card ≤ 1) ∧
        t ≤ rk K v (E.biUnion g) := by
    intro f hall H
    refine ⟨f, fun e he => ⟨subset_refl _, hall e he⟩, ?_⟩
    have := H E (subset_refl _)
    simpa using this
  intro N
  induction N with
  | zero =>
    intro f hs H
    apply base f _ H
    intro e he
    have := (Finset.sum_eq_zero_iff.1 (Nat.le_zero.1 hs)) e he
    omega
  | succ N ih =>
    intro f hs H
    by_cases hall : ∀ e ∈ E, (f e).card ≤ 1
    · exact base f hall H
    push_neg at hall
    obtain ⟨e, he, hlt⟩ := hall
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hlt
    have key : ∀ z ∈ f e, ∀ f' : β → Finset α,
        f' = (fun e' => if e' = e then (f e).erase z else f e') →
        (∀ J ⊆ E, t ≤ (E \ J).card + rk K v (J.biUnion f')) →
        ∃ g : β → Finset α, (∀ e ∈ E, g e ⊆ f e ∧ (g e).card ≤ 1) ∧
          t ≤ rk K v (E.biUnion g) := by
      intro z hz f' hf' H'
      have hsum : ∑ e ∈ E, (f' e).card < ∑ e ∈ E, (f e).card := by
        apply Finset.sum_lt_sum
        · intro i _
          rw [hf']
          dsimp only
          split_ifs with h
          · subst h
            exact Finset.card_le_card (Finset.erase_subset _ _)
          · exact le_rfl
        · refine ⟨e, he, ?_⟩
          rw [hf']
          dsimp only
          rw [if_pos rfl]
          exact Finset.card_erase_lt_of_mem hz
      obtain ⟨g, hg, hgt⟩ := ih f' (by omega) H'
      refine ⟨g, fun i hi => ⟨(hg i hi).1.trans ?_, (hg i hi).2⟩, hgt⟩
      rw [hf']
      dsimp only
      split_ifs with h
      · subst h
        exact Finset.erase_subset _ _
      · exact subset_refl _
    rcases exch v E t f e he x y hxy H with h | h
    · exact key x hx _ rfl h
    · exact key y hy _ rfl h

theorem rank_union_le [DecidableEq Y] (X Z : Finset Y) :
    finrank K (Submodule.span K ((X ∪ Z : Finset Y) : Set Y)) ≤
      X.card + finrank K (Submodule.span K (Z : Set Y)) := by
  rw [Finset.coe_union, Submodule.span_union]
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span K (X : Set Y))
    (Submodule.span K (Z : Set Y))
  have h2 := finrank_span_finset_le_card (R := K) X
  unfold Set.finrank at h2
  omega

theorem rank_le_of_mem (X Z : Finset Y) (h : ∀ x ∈ X, x ∈ Submodule.span K (Z : Set Y)) :
    finrank K (Submodule.span K (X : Set Y)) ≤ finrank K (Submodule.span K (Z : Set Y)) :=
  Submodule.finrank_mono (Submodule.span_le.2 h)

end PEqualNP.Outside.L_lib_971_aux

open PEqualNP.Outside.L_lib_971_aux

theorem PEqualNP.Outside.L_lib_971 : (∀ (k n m : Nat),
  let F := ZMod 2
  let I := Fin k
  let A := Fin n
  let Y := Fin m → F
  ∀ (scope : A → Finset I) (col : A → Y),

  let active := (Finset.univ : Finset A).filter (fun a => col a ≠ 0)
  let left := fun (P : Finset I) (a : A) => scope a \ P
  let good := fun (P : Finset I) => ∀ a ∈ active, (left P a).card ≤ 2
  let pairs := fun (P : Finset I) => (active.image (left P)).filter (fun e => e.card = 2)
  let rank := fun (V : Finset Y) => Module.finrank F (Submodule.span F (V : Set Y))
  let joined := fun (P : Finset I) (J : Finset (Finset I)) =>
    rank ((active.filter (fun a => left P a ∈ J)).image col)
  let worst := fun (P : Finset I) =>
    (Finset.univ : Finset (A → F)).sup (fun w =>
      rank ((pairs P).image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)))

  (∀ (P : Finset I) (z : Nat), good P →
    (worst P ≤ z ↔ ∃ J ⊆ pairs P, ((pairs P) \ J).card + joined P J ≤ z)) ∧
  ∀ (b h : Nat),
    (∃ P : Finset I, good P ∧ worst P ≤ h ∧ P.card + worst P ≤ b) ↔
    (∃ Q : Finset I, good Q ∧ joined Q (pairs Q) ≤ h ∧ Q.card + joined Q (pairs Q) ≤ b)) := by
  intro k n m F I A Y scope col active left good pairs rank joined worst
  have hrank : ∀ S : Finset A, rank (S.image col) = rk F col S := by
    intro S
    show finrank F (Submodule.span F ((S.image col : Finset Y) : Set Y)) = _
    unfold rk
    rw [Finset.coe_image]
  have hbU : ∀ (P : Finset I) (J : Finset (Finset I)),
      J.biUnion (fun e => active.filter (fun a => left P a = e)) =
        active.filter (fun a => left P a ∈ J) := by
    intro P J
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨e, he, ha, rfl⟩
      exact ⟨ha, he⟩
    · rintro ⟨ha, hJ⟩
      exact ⟨_, hJ, ha, rfl⟩
  have easy : ∀ (P : Finset I) (J : Finset (Finset I)), J ⊆ pairs P →
      worst P ≤ ((pairs P) \ J).card + joined P J := by
    intro P J hJ
    apply Finset.sup_le
    intro w _
    have hsplit : (pairs P).image
        (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a) =
        (pairs P \ J).image
          (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a) ∪
        J.image (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a) := by
      rw [← Finset.image_union, Finset.sdiff_union_of_subset hJ]
    show rank _ ≤ _
    rw [hsplit]
    refine (rank_union_le _ _).trans (add_le_add Finset.card_image_le ?_)
    apply rank_le_of_mem
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hx
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    apply Submodule.subset_span
    obtain ⟨haA, hae⟩ := Finset.mem_filter.1 ha
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem col
      (Finset.mem_filter.2 ⟨haA, hae ▸ he⟩))
  have C1 : ∀ (P : Finset I) (z : Nat), good P →
      (worst P ≤ z ↔ ∃ J ⊆ pairs P, ((pairs P) \ J).card + joined P J ≤ z) := by
    intro P z _
    constructor
    · intro hw
      by_contra hne
      push_neg at hne
      have H : ∀ J ⊆ pairs P, z + 1 ≤ (pairs P \ J).card +
          rk F col (J.biUnion (fun e => active.filter (fun a => left P a = e))) := by
        intro J hJ
        have := hne J hJ
        rw [hbU, ← hrank]
        exact this
      obtain ⟨g, hg, ht⟩ := shrink col (pairs P) (z + 1) _
        (fun e => active.filter (fun a => left P a = e)) le_rfl H
      let w : A → F := fun a => if a ∈ (pairs P).biUnion g then 1 else 0
      have h1 : rk F col ((pairs P).biUnion g) ≤ rank ((pairs P).image
          (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)) := by
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro _ ⟨a, ha, rfl⟩
        rw [Finset.mem_coe, Finset.mem_biUnion] at ha
        obtain ⟨e, he, hae⟩ := ha
        rw [Finset.mem_coe, Finset.mem_image]
        refine ⟨e, he, ?_⟩
        have haf := (hg e he).1 hae
        have hw' : ∀ a' ∈ active.filter (fun a => left P a = e),
            w a' • col a' = if a = a' then col a' else 0 := by
          intro a' ha'
          by_cases hh : a = a'
          · subst hh
            rw [if_pos rfl]
            show (if a ∈ (pairs P).biUnion g then (1 : F) else 0) • col a = col a
            rw [if_pos (Finset.mem_biUnion.2 ⟨e, he, hae⟩), one_smul]
          · rw [if_neg hh]
            have hn : a' ∉ (pairs P).biUnion g := by
              intro hm
              obtain ⟨e', he', ha'g⟩ := Finset.mem_biUnion.1 hm
              have q1 := (Finset.mem_filter.1 ((hg e' he').1 ha'g)).2
              have q2 := (Finset.mem_filter.1 ha').2
              have hee : e' = e := q1.symm.trans q2
              subst hee
              exact hh (Finset.card_le_one.1 (hg e' he).2 a hae a' ha'g)
            show (if a' ∈ (pairs P).biUnion g then (1 : F) else 0) • col a' = 0
            rw [if_neg hn, zero_smul]
        rw [Finset.sum_congr rfl hw', Finset.sum_ite_eq, if_pos haf]
      have h2 : rank ((pairs P).image
          (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)) ≤ worst P :=
        Finset.le_sup (f := fun w : A → F => rank ((pairs P).image
          (fun e => ∑ a ∈ active.filter (fun a => left P a = e), w a • col a)))
          (Finset.mem_univ w)
      omega
    · rintro ⟨J, hJ, hle⟩
      exact (easy P J hJ).trans hle
  refine ⟨C1, ?_⟩
  intro b h
  constructor
  · rintro ⟨P, hgood, hwh, hwb⟩
    obtain ⟨J, hJ, hle⟩ := (C1 P (worst P) hgood).1 le_rfl
    have hex : ∀ e ∈ pairs P \ J, ∃ i, i ∈ e := by
      intro e he
      have := (Finset.mem_filter.1 (Finset.mem_sdiff.1 he).1).2
      exact Finset.card_pos.1 (by omega)
    choose c hc using hex
    obtain ⟨Q, hQ⟩ : ∃ Q : Finset I, Q = P ∪ (pairs P \ J).attach.image (fun e => c e.1 e.2) := ⟨_, rfl⟩
    have hleft : ∀ a, left Q a ⊆ left P a := fun a =>
      Finset.sdiff_subset_sdiff (subset_refl _) (hQ ▸ Finset.subset_union_left)
    have hgQ : good Q := fun a ha => (Finset.card_le_card (hleft a)).trans (hgood a ha)
    have hJQ : joined Q (pairs Q) ≤ joined P J := by
      apply rank_le_of_mem
      intro x hx
      apply Submodule.subset_span
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨haA, hap⟩ := Finset.mem_filter.1 ha
      have h2 : (left Q a).card = 2 := (Finset.mem_filter.1 hap).2
      have heq : left Q a = left P a :=
        Finset.eq_of_subset_of_card_le (hleft a) (by have := hgood a haA; omega)
      have hPJ : left P a ∈ J := by
        by_contra hn
        have hmem : left P a ∈ pairs P \ J := Finset.mem_sdiff.2
          ⟨Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ haA, heq ▸ h2⟩, hn⟩
        have hcin : c (left P a) hmem ∈ left Q a := by
          rw [heq]
          exact hc _ hmem
        apply (Finset.mem_sdiff.1 hcin).2
        rw [hQ]
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun e : {x // x ∈ pairs P \ J} => c e.1 e.2) (Finset.mem_attach _ ⟨_, hmem⟩))
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem col (Finset.mem_filter.2 ⟨haA, hPJ⟩))
    have hcard : Q.card ≤ P.card + (pairs P \ J).card := by
      rw [hQ]
      exact (Finset.card_union_le _ _).trans (add_le_add_right (Finset.card_image_le.trans (Finset.card_attach).le) _)
    exact ⟨Q, hgQ, by omega, by omega⟩
  · rintro ⟨Q, hgood, hjh, hjb⟩
    have := easy Q (pairs Q) (subset_refl _)
    rw [Finset.sdiff_self, Finset.card_empty, zero_add] at this
    exact ⟨Q, hgood, by omega, by omega⟩
