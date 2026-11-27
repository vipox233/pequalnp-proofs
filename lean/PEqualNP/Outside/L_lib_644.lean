import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_644

lemma two_mul_le_two_pow : ∀ h : Nat, 1 ≤ h → 2 * h ≤ 2 ^ h
  | 0, hh => by omega
  | 1, _ => by norm_num
  | h + 2, _ => by
    have ih := two_mul_le_two_pow (h + 1) (by omega)
    have hpow : 2 ≤ 2 ^ (h + 1) := by
      have h1 : 1 ≤ h + 1 := by omega
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (h + 1) := Nat.pow_le_pow_right (by norm_num) h1
    calc 2 * (h + 2) = 2 * (h + 1) + 2 := by omega
      _ ≤ 2 ^ (h + 1) + 2 ^ (h + 1) := by omega
      _ = 2 ^ (h + 2) := by ring

lemma exists_balanced_subset {α : Type*} [DecidableEq α] (h : Nat) (hh : 1 ≤ h)
    (w : α → Nat) :
    ∀ G : Finset α, (∀ s ∈ G, 3 * w s ≤ h) → h ≤ 3 * ∑ s ∈ G, w s →
      ∃ A ⊆ G, h ≤ 3 * ∑ s ∈ A, w s ∧ 3 * ∑ s ∈ A, w s < 2 * h := by
  intro G
  induction G using Finset.induction_on with
  | empty =>
    intro _ hge
    simp at hge
    omega
  | @insert a G ha ih =>
    intro hsmall hge
    by_cases hG : h ≤ 3 * ∑ s ∈ G, w s
    · obtain ⟨A, hAG, hlo, hhi⟩ := ih (fun s hs => hsmall s (Finset.mem_insert_of_mem hs)) hG
      exact ⟨A, hAG.trans (Finset.subset_insert a G), hlo, hhi⟩
    · refine ⟨insert a G, Finset.Subset.rfl, hge, ?_⟩
      rw [Finset.sum_insert ha]
      have ha_small := hsmall a (Finset.mem_insert_self a G)
      omega

lemma partition_family {α : Type*} [DecidableEq α] (F : Finset α) (w : α → Nat) (h : Nat)
    (hh : 1 ≤ h) (hw1 : ∀ s ∈ F, 1 ≤ w s) (hwlt : ∀ s ∈ F, w s < h) (hsum : ∑ s ∈ F, w s = h) :
    ∃ A ⊆ F,
      1 ≤ ∑ s ∈ A, w s ∧ 1 ≤ ∑ s ∈ F \ A, w s ∧
      (3 * ∑ s ∈ A, w s ≤ 2 * h ∨ A.card = 1) ∧
      (3 * ∑ s ∈ F \ A, w s ≤ 2 * h ∨ (F \ A).card = 1) := by
  by_cases hbig : ∃ s ∈ F, h < 3 * w s
  · obtain ⟨s, hsF, hsbig⟩ := hbig
    have hsplit : ∑ x ∈ F \ {s}, w x + ∑ x ∈ ({s} : Finset α), w x = ∑ x ∈ F, w x :=
      Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hsF)
    rw [Finset.sum_singleton] at hsplit
    have hlt := hwlt s hsF
    refine ⟨{s}, Finset.singleton_subset_iff.mpr hsF, ?_, by omega, Or.inr (by simp), Or.inl (by omega)⟩
    rw [Finset.sum_singleton]
    exact hw1 s hsF
  · push Not at hbig
    obtain ⟨A, hAF, hlo, hhi⟩ := exists_balanced_subset h hh w F hbig (by omega)
    have hsplit : ∑ x ∈ F \ A, w x + ∑ x ∈ A, w x = ∑ x ∈ F, w x := Finset.sum_sdiff hAF
    refine ⟨A, hAF, by omega, by omega, Or.inl (by omega), Or.inl (by omega)⟩

lemma biUnion_card_le_two_mul {α : Type*} [DecidableEq α] (F : Finset (Finset α)) (h : Nat)
    (hge2 : ∀ s ∈ F, 2 ≤ s.card)
    (hdisj : ∀ s ∈ F, ∀ u ∈ F, s ≠ u → Disjoint s u)
    (hsum : ∑ s ∈ F, (s.card - 1) = h) :
    (F.biUnion id).card ≤ 2 * h := by
  have hpd : (F : Set (Finset α)).PairwiseDisjoint id := by
    intro s hs u hu hne
    exact hdisj s hs u hu hne
  rw [Finset.card_biUnion hpd]
  have hcard_le : F.card ≤ ∑ s ∈ F, (s.card - 1) := by
    calc F.card = ∑ _s ∈ F, 1 := by simp
      _ ≤ ∑ s ∈ F, (s.card - 1) := by
        apply Finset.sum_le_sum
        intro s hs
        have := hge2 s hs
        omega
  have hsum_eq : ∑ s ∈ F, (id s).card = ∑ s ∈ F, (s.card - 1) + F.card := by
    have : ∑ s ∈ F, (id s).card = ∑ s ∈ F, ((s.card - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro s hs
      have := hge2 s hs
      simp only [id_eq]
      omega
    rw [this, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  omega

lemma count_good_colorings {α : Type*} [DecidableEq α]
    (U : Finset α) (F A : Finset (Finset α)) (h : Nat)
    (hAF : A ⊆ F)
    (hsubU : ∀ s ∈ F, s ⊆ U)
    (hge2 : ∀ s ∈ F, 2 ≤ s.card)
    (hdisj : ∀ s ∈ F, ∀ u ∈ F, s ≠ u → Disjoint s u)
    (hsum : ∑ s ∈ F, (s.card - 1) = h) :
    2 ^ U.card ≤
      2 ^ (2 * h) *
        (U.powerset.filter (fun R =>
          (∀ s ∈ A, s ⊆ R) ∧ (∀ s ∈ F \ A, s ⊆ U \ R))).card := by
  let W := F.biUnion id
  let RA := A.biUnion id
  have hWU : W ⊆ U := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨s, hsF, hxs⟩ := hx
    exact hsubU s hsF hxs
  have hRAW : RA ⊆ W := Finset.biUnion_subset_biUnion_of_subset_left id hAF
  have hWcard : W.card ≤ 2 * h := biUnion_card_le_two_mul F h hge2 hdisj hsum
  have hWUcard : W.card ≤ U.card := Finset.card_le_card hWU
  let img := (U \ W).powerset.image (fun X => RA ∪ X)
  have himg_sub : img ⊆ U.powerset.filter (fun R =>
      (∀ s ∈ A, s ⊆ R) ∧ (∀ s ∈ F \ A, s ⊆ U \ R)) := by
    intro R hR
    rw [Finset.mem_image] at hR
    obtain ⟨X, hX, rfl⟩ := hR
    rw [Finset.mem_powerset] at hX
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.union_subset (hRAW.trans hWU) (hX.trans Finset.sdiff_subset), ?_, ?_⟩
    · intro s hs x hxs
      exact Finset.mem_union_left X (Finset.mem_biUnion.mpr ⟨s, hs, hxs⟩)
    · intro s hs x hxs
      rw [Finset.mem_sdiff] at hs
      rw [Finset.mem_sdiff]
      refine ⟨hsubU s hs.1 hxs, ?_⟩
      intro hxR
      rw [Finset.mem_union] at hxR
      rcases hxR with hxRA | hxX
      · rw [Finset.mem_biUnion] at hxRA
        obtain ⟨t, htA, hxt⟩ := hxRA
        have hne : s ≠ t := fun heq => hs.2 (heq ▸ htA)
        exact Finset.disjoint_left.mp (hdisj s hs.1 t (hAF htA) hne) hxs hxt
      · have hxUW := hX hxX
        rw [Finset.mem_sdiff] at hxUW
        exact hxUW.2 (Finset.mem_biUnion.mpr ⟨s, hs.1, hxs⟩)
  have hinj : Set.InjOn (fun X => RA ∪ X) ((U \ W).powerset : Set (Finset α)) := by
    intro X hX Y hY hXY
    dsimp only at hXY
    rw [Finset.mem_coe, Finset.mem_powerset] at hX hY
    ext x
    constructor
    · intro hxX
      have hx_not_RA : x ∉ RA := fun hxRA => (Finset.mem_sdiff.mp (hX hxX)).2 (hRAW hxRA)
      have hxU : x ∈ RA ∪ Y := hXY ▸ Finset.mem_union_right RA hxX
      exact (Finset.mem_union.mp hxU).resolve_left hx_not_RA
    · intro hxY
      have hx_not_RA : x ∉ RA := fun hxRA => (Finset.mem_sdiff.mp (hY hxY)).2 (hRAW hxRA)
      have hxU : x ∈ RA ∪ X := hXY.symm ▸ Finset.mem_union_right RA hxY
      exact (Finset.mem_union.mp hxU).resolve_left hx_not_RA
  have hcard_img : img.card = 2 ^ (U.card - W.card) := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hWU]
  have hcard_le : 2 ^ (U.card - W.card) ≤
      (U.powerset.filter (fun R =>
        (∀ s ∈ A, s ⊆ R) ∧ (∀ s ∈ F \ A, s ⊆ U \ R))).card := by
    rw [← hcard_img]
    exact Finset.card_le_card himg_sub
  calc 2 ^ U.card
      ≤ 2 ^ (2 * h + (U.card - W.card)) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ (2 * h) * 2 ^ (U.card - W.card) := by rw [pow_add]
    _ ≤ 2 ^ (2 * h) *
        (U.powerset.filter (fun R =>
          (∀ s ∈ A, s ⊆ R) ∧ (∀ s ∈ F \ A, s ⊆ U \ R))).card :=
        Nat.mul_le_mul_left _ hcard_le

lemma exists_good_coloring {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset β) (U : Finset α) (fam A : β → Finset (Finset α)) (h : Nat)
    (hScard : 2 ^ (9 * h) ≤ S.card)
    (hAsub : ∀ i ∈ S, A i ⊆ fam i)
    (hfam : ∀ i ∈ S,
      (∀ s ∈ fam i, s ⊆ U) ∧
      (∀ s ∈ fam i, 2 ≤ s.card) ∧
      (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧
      ∑ s ∈ fam i, (s.card - 1) = h) :
    ∃ R ∈ U.powerset,
      2 ^ (7 * h) ≤ (S.filter (fun i =>
        (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card := by
  by_contra hno
  push Not at hno
  have hsum_le : S.card * 2 ^ U.card ≤
      2 ^ (2 * h) * ∑ R ∈ U.powerset,
        (S.filter (fun i =>
          (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card := by
    calc S.card * 2 ^ U.card
        = ∑ _i ∈ S, 2 ^ U.card := by simp
      _ ≤ ∑ i ∈ S, 2 ^ (2 * h) *
            (U.powerset.filter (fun R =>
              (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card := by
          apply Finset.sum_le_sum
          intro i hi
          exact count_good_colorings U (fam i) (A i) h (hAsub i hi)
            (hfam i hi).1 (hfam i hi).2.1 (hfam i hi).2.2.1 (hfam i hi).2.2.2
      _ = 2 ^ (2 * h) * ∑ i ∈ S,
            (U.powerset.filter (fun R =>
              (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card := by
          rw [Finset.mul_sum]
      _ = 2 ^ (2 * h) * ∑ i ∈ S, ∑ R ∈ U.powerset,
            if (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R) then 1 else 0 := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.card_filter]
      _ = 2 ^ (2 * h) * ∑ R ∈ U.powerset, ∑ i ∈ S,
            if (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R) then 1 else 0 := by
          rw [Finset.sum_comm]
      _ = 2 ^ (2 * h) * ∑ R ∈ U.powerset,
            (S.filter (fun i =>
              (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card := by
          congr 1
          apply Finset.sum_congr rfl
          intro R _
          rw [Finset.card_filter]
  have hne : U.powerset.Nonempty := ⟨∅, Finset.empty_mem_powerset U⟩
  have hsum_lt : ∑ R ∈ U.powerset,
      (S.filter (fun i =>
        (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card <
      2 ^ U.card * 2 ^ (7 * h) := by
    calc ∑ R ∈ U.powerset,
          (S.filter (fun i =>
            (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card
        < ∑ _R ∈ U.powerset, 2 ^ (7 * h) := Finset.sum_lt_sum_of_nonempty hne hno
      _ = 2 ^ U.card * 2 ^ (7 * h) := by
          rw [Finset.sum_const, Finset.card_powerset, smul_eq_mul]
  have hpos : 0 < 2 ^ (2 * h) := by positivity
  have hstrict : 2 ^ (2 * h) * ∑ R ∈ U.powerset,
      (S.filter (fun i =>
        (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card <
      2 ^ (9 * h) * 2 ^ U.card := by
    calc 2 ^ (2 * h) * ∑ R ∈ U.powerset,
          (S.filter (fun i =>
            (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))).card
        < 2 ^ (2 * h) * (2 ^ U.card * 2 ^ (7 * h)) := Nat.mul_lt_mul_of_pos_left hsum_lt hpos
      _ = (2 ^ (2 * h) * 2 ^ (7 * h)) * 2 ^ U.card := by ring
      _ = 2 ^ (9 * h) * 2 ^ U.card := by
          rw [← pow_add]
          have : 2 * h + 7 * h = 9 * h := by omega
          rw [this]
  have hSc : 2 ^ (9 * h) * 2 ^ U.card ≤ S.card * 2 ^ U.card :=
    Nat.mul_le_mul_right _ hScard
  omega

lemma exists_common_weight {β : Type*} [DecidableEq β]
    (S' : Finset β) (f : β → Nat) (h : Nat) (hh1 : 1 ≤ h)
    (hS'card : 2 ^ (7 * h) ≤ S'.card)
    (hmaps : ∀ i ∈ S', f i < h) :
    ∃ u ∈ Finset.range h,
      2 * 2 ^ (6 * h) ≤ (S'.filter (fun i => f i = u)).card := by
  by_contra hno
  push Not at hno
  have hmaps' : ∀ i ∈ S', f i ∈ Finset.range h := fun i hi => Finset.mem_range.mpr (hmaps i hi)
  have hfib := Finset.card_eq_sum_card_fiberwise hmaps'
  have hne : (Finset.range h).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hlt : S'.card < h * (2 * 2 ^ (6 * h)) := by
    rw [hfib]
    calc ∑ u ∈ Finset.range h, (S'.filter (fun i => f i = u)).card
        < ∑ _u ∈ Finset.range h, 2 * 2 ^ (6 * h) := Finset.sum_lt_sum_of_nonempty hne hno
      _ = h * (2 * 2 ^ (6 * h)) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2h : 2 * h ≤ 2 ^ h := two_mul_le_two_pow h hh1
  have hbound : h * (2 * 2 ^ (6 * h)) ≤ 2 ^ (7 * h) := by
    calc h * (2 * 2 ^ (6 * h)) = (2 * h) * 2 ^ (6 * h) := by ring
      _ ≤ 2 ^ h * 2 ^ (6 * h) := Nat.mul_le_mul_right _ h2h
      _ = 2 ^ (7 * h) := by
          rw [← pow_add]
          have : h + 6 * h = 7 * h := by omega
          rw [this]
  omega

lemma main_induction (v n : Nat) :
    ∀ h : Nat,
      ∀ (S : Finset (Fin n)) (U : Finset (Fin v)) (fam : Fin n → Finset (Finset (Fin v))),
        2 ^ (9 * h) ≤ S.card →
        (∀ i ∈ S,
          (∀ s ∈ fam i, s ⊆ U) ∧
          (∀ s ∈ fam i, 2 ≤ s.card) ∧
          (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧
          ∑ s ∈ fam i, (s.card - 1) = h) →
        ∃ (I : Finset (Fin n)) (pick : Fin n → Finset (Fin v)),
          I ⊆ S ∧ I.card ≤ h ∧
          (∀ i ∈ I, pick i ∈ fam i ∧ pick i ⊆ U) ∧
          (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (pick i) (pick j)) ∧
          (I.biUnion pick).card = I.card + h := by
  intro h
  induction h using Nat.strong_induction_on with
  | ind h ih =>
    intro S U fam hScard hfam
    by_cases hh0 : h = 0
    · subst hh0
      exact ⟨∅, fun _ => ∅, Finset.empty_subset S, by simp, by simp, by simp, by simp⟩
    have hh1 : 1 ≤ h := by omega
    by_cases hfull : ∃ i ∈ S, ∃ s ∈ fam i, s.card - 1 = h
    · obtain ⟨i, hiS, s, hsfam, hscard⟩ := hfull
      have hsge2 : 2 ≤ s.card := (hfam i hiS).2.1 s hsfam
      have hsU : s ⊆ U := (hfam i hiS).1 s hsfam
      refine ⟨{i}, fun _ => s, Finset.singleton_subset_iff.mpr hiS, by simp [hh1], ?_, ?_, ?_⟩
      · intro j hj
        rw [Finset.mem_singleton] at hj
        subst hj
        exact ⟨hsfam, hsU⟩
      · intro j₁ hj₁ j₂ hj₂ hne
        rw [Finset.mem_singleton] at hj₁ hj₂
        exact absurd (hj₁.trans hj₂.symm) hne
      · simp only [Finset.singleton_biUnion, Finset.card_singleton]
        omega
    · push Not at hfull
      have hlt_all : ∀ i ∈ S, ∀ s ∈ fam i, s.card - 1 < h := by
        intro i hiS s hsfam
        have hle : s.card - 1 ≤ h := by
          rw [← (hfam i hiS).2.2.2]
          exact Finset.single_le_sum (f := fun t : Finset (Fin v) => t.card - 1)
            (fun _ _ => Nat.zero_le _) hsfam
        have hne := hfull i hiS s hsfam
        omega
      have hpart_ex : ∀ i ∈ S, ∃ A ⊆ fam i,
          1 ≤ ∑ s ∈ A, (s.card - 1) ∧
          1 ≤ ∑ s ∈ fam i \ A, (s.card - 1) ∧
          (3 * ∑ s ∈ A, (s.card - 1) ≤ 2 * h ∨ A.card = 1) ∧
          (3 * ∑ s ∈ fam i \ A, (s.card - 1) ≤ 2 * h ∨ (fam i \ A).card = 1) := by
        intro i hiS
        exact partition_family (fam i) (fun s => s.card - 1) h hh1
          (fun s hs => by have := (hfam i hiS).2.1 s hs; omega)
          (hlt_all i hiS)
          (hfam i hiS).2.2.2
      have hA_ex : ∃ A : Fin n → Finset (Finset (Fin v)),
          ∀ i ∈ S, A i ⊆ fam i ∧
            1 ≤ ∑ s ∈ A i, (s.card - 1) ∧
            1 ≤ ∑ s ∈ fam i \ A i, (s.card - 1) ∧
            (3 * ∑ s ∈ A i, (s.card - 1) ≤ 2 * h ∨ (A i).card = 1) ∧
            (3 * ∑ s ∈ fam i \ A i, (s.card - 1) ≤ 2 * h ∨ (fam i \ A i).card = 1) := by
        refine ⟨fun i => if hi : i ∈ S then Classical.choose (hpart_ex i hi) else ∅, ?_⟩
        intro i hi
        dsimp only
        rw [dite_eq_left hi]
        exact Classical.choose_spec (hpart_ex i hi)
      obtain ⟨A, hA⟩ := hA_ex
      obtain ⟨R, hRmem, hS'card⟩ :=
        exists_good_coloring S U fam A h hScard (fun i hi => (hA i hi).1) hfam
      have hRU : R ⊆ U := Finset.mem_powerset.mp hRmem
      set S' := S.filter (fun i =>
        (∀ s ∈ A i, s ⊆ R) ∧ (∀ s ∈ fam i \ A i, s ⊆ U \ R))
      have hS'card' : 2 ^ (7 * h) ≤ S'.card := by convert hS'card
      have hS'sub : S' ⊆ S := Finset.filter_subset _ _
      obtain ⟨u, hurange, hTcard⟩ :=
        exists_common_weight S' (fun i => ∑ s ∈ A i, (s.card - 1)) h hh1 hS'card' (fun i hi => by
          have hiS := hS'sub hi
          have hsplit : ∑ s ∈ fam i \ A i, (s.card - 1) + ∑ s ∈ A i, (s.card - 1) =
              ∑ s ∈ fam i, (s.card - 1) := Finset.sum_sdiff (hA i hiS).1
          have htot := (hfam i hiS).2.2.2
          have hb1 := (hA i hiS).2.2.1
          omega)
      set T := S'.filter (fun i => ∑ s ∈ A i, (s.card - 1) = u)
      have hTsubS' : T ⊆ S' := Finset.filter_subset _ _
      have hTsubS : T ⊆ S := hTsubS'.trans hS'sub
      have hTne : T.Nonempty := Finset.card_pos.mp (by
        have : 0 < 2 * 2 ^ (6 * h) := by positivity
        omega)
      obtain ⟨i₀, hi₀T⟩ := hTne
      have hi₀S : i₀ ∈ S := hTsubS hi₀T
      have hu_eq₀ : ∑ s ∈ A i₀, (s.card - 1) = u := (Finset.mem_filter.mp hi₀T).2
      have hu1 : 1 ≤ u := by
        have := (hA i₀ hi₀S).2.1
        omega
      have hult : u < h := Finset.mem_range.mp hurange
      let b := h - u
      have hb1 : 1 ≤ b := by omega
      have hblt : b < h := by omega
      have hub : u + b = h := by omega
      obtain ⟨T₁, hT₁sub, hT₁card⟩ := Finset.exists_subset_card_eq (by omega : 2 ^ (6 * h) ≤ T.card)
      let T₂ := T \ T₁
      have hT₂sub : T₂ ⊆ T := Finset.sdiff_subset
      have hT₂card : 2 ^ (6 * h) ≤ T₂.card := by
        have hsd : T₂.card = T.card - T₁.card := by
          rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hT₁sub]
        omega
      have hTdisj : Disjoint T₁ T₂ := Finset.disjoint_sdiff
      have hside : ∀ (Tside : Finset (Fin n)) (Uside : Finset (Fin v))
          (Fside : Fin n → Finset (Finset (Fin v))) (w : Nat),
          Tside ⊆ S → 1 ≤ w → w < h → 2 ^ (6 * h) ≤ Tside.card →
          (∀ i ∈ Tside, Fside i ⊆ fam i ∧ (∀ s ∈ Fside i, s ⊆ Uside) ∧
            ∑ s ∈ Fside i, (s.card - 1) = w ∧
            (3 * w ≤ 2 * h ∨ (Fside i).card = 1)) →
          ∃ (Iside : Finset (Fin n)) (pickside : Fin n → Finset (Fin v)),
            Iside ⊆ Tside ∧ Iside.card ≤ w ∧
            (∀ i ∈ Iside, pickside i ∈ fam i ∧ pickside i ⊆ Uside) ∧
            (∀ i ∈ Iside, ∀ j ∈ Iside, i ≠ j → Disjoint (pickside i) (pickside j)) ∧
            (Iside.biUnion pickside).card = Iside.card + w := by
        intro Tside Uside Fside w hTsideS hw1 hwlt hTsideCard hFside
        by_cases hsmall : 3 * w ≤ 2 * h
        · have h9w : 2 ^ (9 * w) ≤ Tside.card := by
            calc 2 ^ (9 * w) ≤ 2 ^ (6 * h) := Nat.pow_le_pow_right (by norm_num) (by omega)
              _ ≤ Tside.card := hTsideCard
          obtain ⟨Iside, pickside, hIT, hIcard, hIp, hIdisj, hIbi⟩ :=
            ih w hwlt Tside Uside Fside h9w (fun i hi =>
              ⟨(hFside i hi).2.1,
               fun s hs => (hfam i (hTsideS hi)).2.1 s ((hFside i hi).1 hs),
               fun s hs t ht hne =>
                 (hfam i (hTsideS hi)).2.2.1 s ((hFside i hi).1 hs) t ((hFside i hi).1 ht) hne,
               (hFside i hi).2.2.1⟩)
          exact ⟨Iside, pickside, hIT, hIcard,
            fun i hi => ⟨(hFside i (hIT hi)).1 (hIp i hi).1, (hIp i hi).2⟩,
            hIdisj, hIbi⟩
        · have hne : Tside.Nonempty := Finset.card_pos.mp (by
            have : 0 < 2 ^ (6 * h) := by positivity
            omega)
          obtain ⟨i1, hi1⟩ := hne
          have hcard1 : (Fside i1).card = 1 := (hFside i1 hi1).2.2.2.resolve_left hsmall
          obtain ⟨s1, hs1eq⟩ := Finset.card_eq_one.mp hcard1
          have hs1mem : s1 ∈ Fside i1 := by rw [hs1eq]; exact Finset.mem_singleton_self s1
          have hs1fam : s1 ∈ fam i1 := (hFside i1 hi1).1 hs1mem
          have hs1U : s1 ⊆ Uside := (hFside i1 hi1).2.1 s1 hs1mem
          have hs1ge2 : 2 ≤ s1.card := (hfam i1 (hTsideS hi1)).2.1 s1 hs1fam
          have hs1sum : s1.card - 1 = w := by
            have := (hFside i1 hi1).2.2.1
            rw [hs1eq, Finset.sum_singleton] at this
            exact this
          refine ⟨{i1}, fun _ => s1, Finset.singleton_subset_iff.mpr hi1, by simp [hw1], ?_, ?_, ?_⟩
          · intro j hj
            rw [Finset.mem_singleton] at hj
            subst hj
            exact ⟨hs1fam, hs1U⟩
          · intro j₁ hj₁ j₂ hj₂ hne
            rw [Finset.mem_singleton] at hj₁ hj₂
            exact absurd (hj₁.trans hj₂.symm) hne
          · simp only [Finset.singleton_biUnion, Finset.card_singleton]
            omega
      obtain ⟨I₁, pick₁, hI₁T, hI₁card, hI₁p, hI₁disj, hI₁bi⟩ :=
        hside T₁ R A u (hT₁sub.trans hTsubS) hu1 hult (by omega) (fun i hi => by
          have hiT := hT₁sub hi
          have hiS' := hTsubS' hiT
          have hiS := hTsubS hiT
          have hgood := (Finset.mem_filter.mp hiS').2
          have husum := (Finset.mem_filter.mp hiT).2
          have hAi := hA i hiS
          refine ⟨hAi.1, hgood.1, husum, ?_⟩
          rw [← husum]
          exact hAi.2.2.2.1)
      obtain ⟨I₂, pick₂, hI₂T, hI₂card, hI₂p, hI₂disj, hI₂bi⟩ :=
        hside T₂ (U \ R) (fun i => fam i \ A i) b (hT₂sub.trans hTsubS) hb1 hblt hT₂card (fun i hi => by
          have hiT := hT₂sub hi
          have hiS' := hTsubS' hiT
          have hiS := hTsubS hiT
          have hgood := (Finset.mem_filter.mp hiS').2
          have husum := (Finset.mem_filter.mp hiT).2
          have hAi := hA i hiS
          have hsplit : ∑ s ∈ fam i \ A i, (s.card - 1) + ∑ s ∈ A i, (s.card - 1) =
              ∑ s ∈ fam i, (s.card - 1) := Finset.sum_sdiff hAi.1
          have htot := (hfam i hiS).2.2.2
          have hbsum : ∑ s ∈ fam i \ A i, (s.card - 1) = b := by omega
          refine ⟨Finset.sdiff_subset, hgood.2, hbsum, ?_⟩
          rw [← hbsum]
          exact hAi.2.2.2.2)
      have hIdisj12 : Disjoint I₁ I₂ := hTdisj.mono hI₁T hI₂T
      have hRBdisj : Disjoint R (U \ R) := Finset.disjoint_sdiff
      let pick : Fin n → Finset (Fin v) := fun i => if i ∈ I₁ then pick₁ i else pick₂ i
      refine ⟨I₁ ∪ I₂, pick,
        Finset.union_subset (hI₁T.trans (hT₁sub.trans hTsubS)) (hI₂T.trans (hT₂sub.trans hTsubS)),
        ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_union_of_disjoint hIdisj12]
        omega
      · intro i hi
        rw [Finset.mem_union] at hi
        rcases hi with hi1 | hi2
        · simp only [pick, ite_eq_left hi1]
          exact ⟨(hI₁p i hi1).1, (hI₁p i hi1).2.trans hRU⟩
        · have hi1 : i ∉ I₁ := Finset.disjoint_right.mp hIdisj12 hi2
          simp only [pick, ite_eq_right hi1]
          exact ⟨(hI₂p i hi2).1, (hI₂p i hi2).2.trans Finset.sdiff_subset⟩
      · intro i hi j hj hne
        rw [Finset.mem_union] at hi hj
        rcases hi with hi1 | hi2 <;> rcases hj with hj1 | hj2
        · simp only [pick, ite_eq_left hi1, ite_eq_left hj1]
          exact hI₁disj i hi1 j hj1 hne
        · have hj1 : j ∉ I₁ := Finset.disjoint_right.mp hIdisj12 hj2
          simp only [pick, ite_eq_left hi1, ite_eq_right hj1]
          exact hRBdisj.mono (hI₁p i hi1).2 (hI₂p j hj2).2
        · have hi1 : i ∉ I₁ := Finset.disjoint_right.mp hIdisj12 hi2
          simp only [pick, ite_eq_right hi1, ite_eq_left hj1]
          exact (hRBdisj.mono (hI₁p j hj1).2 (hI₂p i hi2).2).symm
        · have hi1 : i ∉ I₁ := Finset.disjoint_right.mp hIdisj12 hi2
          have hj1 : j ∉ I₁ := Finset.disjoint_right.mp hIdisj12 hj2
          simp only [pick, ite_eq_right hi1, ite_eq_right hj1]
          exact hI₂disj i hi2 j hj2 hne
      · have hbi1 : I₁.biUnion pick = I₁.biUnion pick₁ := by
          apply Finset.biUnion_congr rfl
          intro i hi
          simp only [pick, ite_eq_left hi]
        have hbi2 : I₂.biUnion pick = I₂.biUnion pick₂ := by
          apply Finset.biUnion_congr rfl
          intro i hi
          have hi1 : i ∉ I₁ := Finset.disjoint_right.mp hIdisj12 hi
          simp only [pick, ite_eq_right hi1]
        have hbi_sub1 : I₁.biUnion pick₁ ⊆ R := by
          rw [Finset.biUnion_subset]
          intro i hi
          exact (hI₁p i hi).2
        have hbi_sub2 : I₂.biUnion pick₂ ⊆ U \ R := by
          rw [Finset.biUnion_subset]
          intro i hi
          exact (hI₂p i hi).2
        have hbi_disj : Disjoint (I₁.biUnion pick₁) (I₂.biUnion pick₂) :=
          hRBdisj.mono hbi_sub1 hbi_sub2
        rw [Finset.union_biUnion, hbi1, hbi2, Finset.card_union_of_disjoint hbi_disj,
          Finset.card_union_of_disjoint hIdisj12, hI₁bi, hI₂bi]
        omega

end PEqualNP.Outside.L_lib_644

theorem PEqualNP.Outside.L_lib_644 : (∀ (v n h : Nat), 2^(9*h) ≤ n →
  let V := Fin v
  ∀ fam : Fin n → Finset (Finset V),
    (∀ i, (∀ s ∈ fam i, 2 ≤ s.card) ∧
      (∀ s ∈ fam i, ∀ u ∈ fam i, s ≠ u → Disjoint s u) ∧
      (fam i).sum (fun s => s.card-1) = h) →
    ∃ (I : Finset (Fin n)) (pick : Fin n → Finset V),
      I.card ≤ h ∧ (∀ i ∈ I, pick i ∈ fam i) ∧
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (pick i) (pick j)) ∧
      (I.biUnion pick).card = I.card + h) := by
  intro v n h hn V fam hfam
  have huniv : 2 ^ (9 * h) ≤ (Finset.univ : Finset (Fin n)).card := by
    simpa using hn
  obtain ⟨I, pick, _, hIcard, hIp, hIdisj, hIbi⟩ :=
    PEqualNP.Outside.L_lib_644.main_induction v n h Finset.univ Finset.univ fam huniv
      (fun i _ => ⟨fun s _ => Finset.subset_univ s, (hfam i).1, (hfam i).2.1, (hfam i).2.2⟩)
  exact ⟨I, pick, hIcard, fun i hi => (hIp i hi).1, hIdisj, hIbi⟩
