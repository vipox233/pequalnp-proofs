import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1139_aux

abbrev syn {m r : Nat} (rows : Fin r → Finset (Fin m)) (x : Finset (Fin m)) : Finset (Fin r) :=
  (Finset.univ : Finset (Fin r)).filter (fun j => ((rows j) ∩ x).card % 2 = 1)

abbrev part {r s : Nat} (owner : Fin r → Fin s) (d : Finset (Fin r)) (i : Fin s) : Finset (Fin r) :=
  d.filter (fun j => owner j = i)

abbrev imageSet {m r : Nat} (rows : Fin r → Finset (Fin m)) : Finset (Finset (Fin r)) :=
  (Finset.univ : Finset (Finset (Fin m))).image (syn rows)

abbrev independent {m r s : Nat} (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s) :
    Finset (Finset (Fin r)) :=
  (imageSet rows).filter (fun d => ∀ i : Fin s, part owner d i ∈ imageSet rows)

abbrev mass {m r : Nat} (rows : Fin r → Finset (Fin m)) (d : Finset (Fin r)) : Nat :=
  ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn rows x = d)).card

theorem card_symmDiff_mod2 {α : Type*} [DecidableEq α] (a b : Finset α) :
    (symmDiff a b).card % 2 = (a.card + b.card) % 2 := by
  have h1 := Finset.card_union_add_card_inter a b
  have h2 : a ∪ b = symmDiff a b ∪ (a ∩ b) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff a b) (a ∩ b) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_symmDiff, Finset.mem_inter] at h1 h2; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1
  omega

theorem inter_symmDiff_right {α : Type*} [DecidableEq α] (c a b : Finset α) :
    c ∩ symmDiff a b = symmDiff (c ∩ a) (c ∩ b) := by
  ext x; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto

theorem filter_symmDiff_eq {α : Type*} [DecidableEq α] (a b : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (symmDiff a b).filter p = symmDiff (a.filter p) (b.filter p) := by
  ext x; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto

theorem syn_empty {m r : Nat} (rows : Fin r → Finset (Fin m)) : syn rows ∅ = ∅ := by
  ext j; simp [syn]

theorem syn_symmDiff {m r : Nat} (rows : Fin r → Finset (Fin m)) (x y : Finset (Fin m)) :
    syn rows (symmDiff x y) = symmDiff (syn rows x) (syn rows y) := by
  ext j
  simp only [syn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff,
    inter_symmDiff_right]
  have h := card_symmDiff_mod2 (rows j ∩ x) (rows j ∩ y)
  omega

theorem empty_mem_imageSet {m r : Nat} (rows : Fin r → Finset (Fin m)) :
    ∅ ∈ imageSet rows := by
  exact Finset.mem_image.mpr ⟨∅, Finset.mem_univ ∅, syn_empty rows⟩

theorem symmDiff_mem_imageSet {m r : Nat} (rows : Fin r → Finset (Fin m))
    {d1 d2 : Finset (Fin r)} (h1 : d1 ∈ imageSet rows) (h2 : d2 ∈ imageSet rows) :
    symmDiff d1 d2 ∈ imageSet rows := by
  obtain ⟨x1, _, rfl⟩ := Finset.mem_image.mp h1
  obtain ⟨x2, _, rfl⟩ := Finset.mem_image.mp h2
  exact Finset.mem_image.mpr ⟨symmDiff x1 x2, Finset.mem_univ _, syn_symmDiff rows x1 x2⟩

theorem part_empty {r s : Nat} (owner : Fin r → Fin s) (i : Fin s) :
    part owner ∅ i = ∅ := by
  simp [part]

theorem part_symmDiff {r s : Nat} (owner : Fin r → Fin s) (d1 d2 : Finset (Fin r)) (i : Fin s) :
    part owner (symmDiff d1 d2) i = symmDiff (part owner d1 i) (part owner d2 i) :=
  filter_symmDiff_eq d1 d2 (fun j => owner j = i)

theorem empty_mem_independent {m r s : Nat} (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s) :
    ∅ ∈ independent rows owner := by
  refine Finset.mem_filter.mpr ⟨empty_mem_imageSet rows, fun i => ?_⟩
  rw [part_empty]
  exact empty_mem_imageSet rows

theorem symmDiff_mem_independent {m r s : Nat} (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s)
    {h1 h2 : Finset (Fin r)} (hh1 : h1 ∈ independent rows owner) (hh2 : h2 ∈ independent rows owner) :
    symmDiff h1 h2 ∈ independent rows owner := by
  obtain ⟨hi1, hp1⟩ := Finset.mem_filter.mp hh1
  obtain ⟨hi2, hp2⟩ := Finset.mem_filter.mp hh2
  refine Finset.mem_filter.mpr ⟨symmDiff_mem_imageSet rows hi1 hi2, fun i => ?_⟩
  rw [part_symmDiff]
  exact symmDiff_mem_imageSet rows (hp1 i) (hp2 i)

theorem union_eq_symmDiff_of_disjoint {α : Type*} [DecidableEq α] {a b : Finset α}
    (hd : Disjoint a b) : a ∪ b = symmDiff a b := by
  ext x
  simp only [Finset.mem_union, Finset.mem_symmDiff]
  constructor
  · rintro (ha | hb)
    · exact Or.inl ⟨ha, Finset.disjoint_left.mp hd ha⟩
    · exact Or.inr ⟨hb, Finset.disjoint_right.mp hd hb⟩
  · rintro (⟨ha, _⟩ | ⟨hb, _⟩)
    · exact Or.inl ha
    · exact Or.inr hb

theorem mem_independent_of_parts {m r s : Nat} (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s)
    (d : Finset (Fin r)) (hp : ∀ i : Fin s, part owner d i ∈ imageSet rows) :
    d ∈ independent rows owner := by
  have hbiU : ∀ S : Finset (Fin s), S.biUnion (fun i => part owner d i) ∈ imageSet rows := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.biUnion_empty]
      exact empty_mem_imageSet rows
    | @insert i S' hiS' ih =>
      rw [Finset.biUnion_insert]
      have hd : Disjoint (part owner d i) (S'.biUnion (fun k => part owner d k)) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        have ho1 : owner j = i := (Finset.mem_filter.mp hj1).2
        obtain ⟨k, hkS', hjk⟩ := Finset.mem_biUnion.mp hj2
        have ho2 : owner j = k := (Finset.mem_filter.mp hjk).2
        exact hiS' (ho1 ▸ ho2.symm ▸ hkS')
      rw [union_eq_symmDiff_of_disjoint hd]
      exact symmDiff_mem_imageSet rows (hp i) ih
  have hd_eq : (Finset.univ : Finset (Fin s)).biUnion (fun i => part owner d i) = d := by
    ext j
    simp only [part, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨_, hjd, _⟩ => hjd, fun hjd => ⟨owner j, hjd, rfl⟩⟩
  have hd_im : d ∈ imageSet rows := hd_eq ▸ hbiU Finset.univ
  exact Finset.mem_filter.mpr ⟨hd_im, hp⟩

theorem mass_eq_const {m r : Nat} (rows : Fin r → Finset (Fin m)) (d : Finset (Fin r))
    (hd : d ∈ imageSet rows) : mass rows d = mass rows ∅ := by
  obtain ⟨x0, _, hsyn0⟩ := Finset.mem_image.mp hd
  refine Finset.card_bij (fun x _ => symmDiff x x0) ?_ ?_ ?_
  · intro x hx
    have hxs : syn rows x = d := (Finset.mem_filter.mp hx).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [syn_symmDiff, hxs, hsyn0, symmDiff_self]; rfl
  · intro x1 _ x2 _ heq
    have h := congrArg (fun t => symmDiff t x0) heq
    simpa [symmDiff_assoc] using h
  · intro y hy
    have hys : syn rows y = ∅ := (Finset.mem_filter.mp hy).2
    refine ⟨symmDiff y x0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, by simp⟩
    rw [syn_symmDiff, hys, hsyn0]; simp

theorem mass_pos_empty {m r : Nat} (rows : Fin r → Finset (Fin m)) : 0 < mass rows ∅ := by
  exact Finset.card_pos.mpr ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ ∅, syn_empty rows⟩⟩

theorem mass_eq_zero_of_not_mem {m r : Nat} (rows : Fin r → Finset (Fin m)) (d : Finset (Fin r))
    (hd : d ∉ imageSet rows) : mass rows d = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact hd (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)

theorem main : ∀ (m r s : Nat), 0 < s →
  ∀ (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s),
  let xs := (Finset.univ : Finset (Finset (Fin m)))
  let parties := (Finset.univ : Finset (Fin s))
  let syn := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin r)).filter (fun j => ((rows j) ∩ x).card % 2 = 1)
  let part := fun (d : Finset (Fin r)) (i : Fin s) => d.filter (fun j => owner j = i)
  let imageSet := xs.image syn
  let independent := imageSet.filter (fun d => ∀ i : Fin s, part d i ∈ imageSet)
  let mass := fun (d : Finset (Fin r)) => (xs.filter (fun x => syn x = d)).card
  ∀ K : Nat,
    let cover := ∃ accept : Fin K → Fin s → Finset (Fin r) → Bool,
      ∀ d : Finset (Fin r), (d ∈ imageSet ↔
        ∃ z : Fin K, ∀ i : Fin s, accept z i (part d i) = true)
    let exactCount := ∃ weight : Fin K → Fin s → Finset (Fin r) → Nat,
      ∀ d : Finset (Fin r), mass d =
        (Finset.univ : Finset (Fin K)).sum
          (fun z => parties.prod (fun i => weight z i (part d i)))
    (cover ↔ imageSet.card ≤ K * independent.card) ∧
      (exactCount ↔ imageSet.card ≤ K * independent.card) := by
  classical
  intro m r s hs rows owner xs0 parties0 syn0 part0 im0 ind0 mass0 K cover0 exact0
  have h1 : cover0 → (imageSet rows).card ≤ K * (independent rows owner).card := by
    rintro ⟨accept, hacc⟩
    let B : Fin K → Finset (Finset (Fin r)) := fun z =>
      (imageSet rows).filter (fun d => ∀ i : Fin s, accept z i (part owner d i) = true)
    have hcov : imageSet rows ⊆ (Finset.univ : Finset (Fin K)).biUnion B := by
      intro d hd
      obtain ⟨z, hz⟩ := (hacc d).mp hd
      exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ z, Finset.mem_filter.mpr ⟨hd, hz⟩⟩
    have hle_sum : (imageSet rows).card ≤
        (Finset.univ : Finset (Fin K)).sum (fun z => (B z).card) :=
      (Finset.card_le_card hcov).trans Finset.card_biUnion_le
    have hB_le : ∀ z : Fin K, (B z).card ≤ (independent rows owner).card := by
      intro z
      by_cases hemp : B z = ∅
      · rw [hemp, Finset.card_empty]; exact Nat.zero_le _
      · obtain ⟨d0, hd0B⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        obtain ⟨hd0im, hd0acc⟩ := Finset.mem_filter.mp hd0B
        have hinj : Set.InjOn (fun d => symmDiff d d0) (B z : Set (Finset (Fin r))) := by
          intro d1 _ d2 _ heq
          have h := congrArg (fun t => symmDiff t d0) heq
          simpa [symmDiff_assoc] using h
        have hmaps : (B z).image (fun d => symmDiff d d0) ⊆ independent rows owner := by
          intro t ht
          obtain ⟨d, hdB, rfl⟩ := Finset.mem_image.mp ht
          obtain ⟨hdim, hdacc⟩ := Finset.mem_filter.mp hdB
          refine mem_independent_of_parts rows owner (symmDiff d d0) (fun i0 => ?_)
          let d' := part owner d i0 ∪ d0.filter (fun j => owner j ≠ i0)
          have hpart_d' : ∀ i : Fin s,
              part owner d' i = if i = i0 then part owner d i0 else part owner d0 i := by
            intro i
            split_ifs with hii0
            · subst hii0
              ext j
              simp only [d', part, Finset.mem_filter, Finset.mem_union]
              constructor
              · rintro ⟨⟨h1, h2⟩ | ⟨_, h2⟩, h3⟩
                · exact ⟨h1, h2⟩
                · exact (h2 h3).elim
              · rintro ⟨h1, h2⟩; exact ⟨Or.inl ⟨h1, h2⟩, h2⟩
            · ext j
              simp only [d', part, Finset.mem_filter, Finset.mem_union]
              constructor
              · rintro ⟨⟨_, h2⟩ | ⟨h1, _⟩, h3⟩
                · exact (hii0 (h3.symm.trans h2)).elim
                · exact ⟨h1, h3⟩
              · rintro ⟨h1, h3⟩; exact ⟨Or.inr ⟨h1, fun h => hii0 (h3.symm.trans h)⟩, h3⟩
          have hd'im : d' ∈ imageSet rows := by
            apply (hacc d').mpr
            refine ⟨z, fun i => ?_⟩
            change accept z i (part owner d' i) = true
            rw [hpart_d' i]
            split_ifs with hii0
            · subst hii0; exact hdacc i
            · exact hd0acc i
          have heq_sd : symmDiff d' d0 = part owner (symmDiff d d0) i0 := by
            ext j
            simp only [d', part, Finset.mem_symmDiff, Finset.mem_union, Finset.mem_filter]
            by_cases ho : owner j = i0 <;> by_cases hjd : j ∈ d <;> by_cases hjd0 : j ∈ d0 <;>
              simp [ho, hjd, hjd0]
          rw [← heq_sd]
          exact symmDiff_mem_imageSet rows hd'im hd0im
        calc (B z).card = ((B z).image (fun d => symmDiff d d0)).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (independent rows owner).card := Finset.card_le_card hmaps
    calc (imageSet rows).card
        ≤ (Finset.univ : Finset (Fin K)).sum (fun z => (B z).card) := hle_sum
      _ ≤ (Finset.univ : Finset (Fin K)).sum (fun _ => (independent rows owner).card) :=
          Finset.sum_le_sum (fun z _ => hB_le z)
      _ = K * (independent rows owner).card := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have h2 : exact0 → cover0 := by
    rintro ⟨weight, hwt⟩
    refine ⟨fun z i u => decide (0 < weight z i u), fun d => ?_⟩
    have hmass_iff : d ∈ imageSet rows ↔ 0 < mass rows d := by
      constructor
      · intro hd; rw [mass_eq_const rows d hd]; exact mass_pos_empty rows
      · intro hpos
        by_contra hnot
        rw [mass_eq_zero_of_not_mem rows d hnot] at hpos
        exact Nat.lt_irrefl 0 hpos
    change d ∈ imageSet rows ↔ ∃ z : Fin K, ∀ i : Fin s, decide (0 < weight z i (part owner d i)) = true
    rw [hmass_iff]
    have hwt' : mass rows d = (Finset.univ : Finset (Fin K)).sum
        (fun z => (Finset.univ : Finset (Fin s)).prod (fun i => weight z i (part owner d i))) := hwt d
    rw [hwt']
    constructor
    · intro hpos
      have hne0 : (Finset.univ : Finset (Fin K)).sum
          (fun z => (Finset.univ : Finset (Fin s)).prod (fun i => weight z i (part owner d i))) ≠ 0 :=
        Nat.ne_of_gt hpos
      obtain ⟨z, _, hz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
      refine ⟨z, fun i => ?_⟩
      simp only [decide_eq_true_eq]
      by_contra h0
      have hw0 : weight z i (part owner d i) = 0 := by omega
      exact hz (Finset.prod_eq_zero (Finset.mem_univ i) hw0)
    · rintro ⟨z, hz⟩
      have hprod_pos : 0 < (Finset.univ : Finset (Fin s)).prod (fun i => weight z i (part owner d i)) := by
        apply Finset.prod_pos
        intro i _
        exact decide_eq_true_eq.mp (hz i)
      exact lt_of_lt_of_le hprod_pos
        (Finset.single_le_sum
          (f := fun z => (Finset.univ : Finset (Fin s)).prod (fun i => weight z i (part owner d i)))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ z))
  have h3 : (imageSet rows).card ≤ K * (independent rows owner).card → exact0 := by
    intro hleK
    let H := independent rows owner
    let G := imageSet rows
    let coset : Finset (Fin r) → Finset (Finset (Fin r)) := fun a => H.image (fun h => symmDiff a h)
    have hcoset_sub : ∀ a ∈ G, coset a ⊆ G := by
      intro a ha d hd
      obtain ⟨h, hhH, rfl⟩ := Finset.mem_image.mp hd
      exact symmDiff_mem_imageSet rows ha (Finset.mem_filter.mp hhH).1
    have hcoset_self : ∀ a, a ∈ coset a := by
      intro a
      exact Finset.mem_image.mpr ⟨∅, empty_mem_independent rows owner, by simp⟩
    have hcoset_card : ∀ a, (coset a).card = H.card := by
      intro a
      apply Finset.card_image_of_injective
      intro h1 h2 heq
      have h := congrArg (fun t => symmDiff a t) heq
      simpa [symmDiff_assoc] using h
    have hcoset_mem_iff : ∀ a d, d ∈ coset a ↔ symmDiff a d ∈ H := by
      intro a d
      constructor
      · intro hd
        obtain ⟨h, hhH, rfl⟩ := Finset.mem_image.mp hd
        simpa [symmDiff_assoc] using hhH
      · intro hsd
        exact Finset.mem_image.mpr ⟨symmDiff a d, hsd, by simp⟩
    have hcoset_eq_or_disj : ∀ a b, coset a = coset b ∨ Disjoint (coset a) (coset b) := by
      intro a b
      by_cases hab : symmDiff a b ∈ H
      · left
        ext d
        rw [hcoset_mem_iff, hcoset_mem_iff]
        constructor
        · intro had
          have heq : symmDiff b d = symmDiff (symmDiff a b) (symmDiff a d) := by
            rw [symmDiff_comm a b, symmDiff_assoc, ← symmDiff_assoc a a d, symmDiff_self, bot_symmDiff]
          rw [heq]
          exact symmDiff_mem_independent rows owner hab had
        · intro hbd
          have heq : symmDiff a d = symmDiff (symmDiff a b) (symmDiff b d) := by
            rw [symmDiff_assoc, ← symmDiff_assoc b b d, symmDiff_self, bot_symmDiff]
          rw [heq]
          exact symmDiff_mem_independent rows owner hab hbd
      · right
        rw [Finset.disjoint_left]
        intro d hda hdb
        have had := (hcoset_mem_iff a d).mp hda
        have hbd := (hcoset_mem_iff b d).mp hdb
        have heq : symmDiff a b = symmDiff (symmDiff a d) (symmDiff b d) := by
          rw [symmDiff_comm b d, symmDiff_assoc, ← symmDiff_assoc d d b, symmDiff_self, bot_symmDiff]
        exact hab (heq ▸ symmDiff_mem_independent rows owner had hbd)
    let Cosets := G.image coset
    have hG_eq : G = Cosets.biUnion id := by
      ext d
      simp only [Cosets, Finset.mem_biUnion, Finset.mem_image, id_eq]
      constructor
      · intro hd; exact ⟨coset d, ⟨d, hd, rfl⟩, hcoset_self d⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, hda⟩; exact hcoset_sub a ha hda
    have hCosets_disj : Set.PairwiseDisjoint (Cosets : Set (Finset (Finset (Fin r)))) id := by
      intro C1 hC1 C2 hC2 hne
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC1
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hC2
      change Disjoint (coset a) (coset b)
      rcases hcoset_eq_or_disj a b with heq | hdisj
      · exact (hne heq).elim
      · exact hdisj
    have hG_card : G.card = Cosets.card * H.card := by
      conv_lhs => rw [hG_eq]
      rw [Finset.card_biUnion hCosets_disj]
      have hall : ∀ C ∈ Cosets, (id C).card = H.card := by
        intro C hC
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hC
        exact hcoset_card a
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul]
    have hH_pos : 0 < H.card := Finset.card_pos.mpr ⟨∅, empty_mem_independent rows owner⟩
    have hCosets_le_K : Cosets.card ≤ K := by
      have hmul : Cosets.card * H.card ≤ K * H.card := hG_card ▸ hleK
      exact Nat.le_of_mul_le_mul_right hmul hH_pos
    let L := Cosets.toList
    have hL_len : L.length = Cosets.card := Finset.length_toList Cosets
    have hL_nd : L.Nodup := Finset.nodup_toList Cosets
    have hL_mem : ∀ C, C ∈ L ↔ C ∈ Cosets := fun C => Finset.mem_toList
    let pickA : Finset (Finset (Fin r)) → Finset (Fin r) := fun C =>
      if h : ∃ a ∈ G, coset a = C then Classical.choose h else ∅
    have hpickA : ∀ C ∈ Cosets, pickA C ∈ G ∧ coset (pickA C) = C := by
      intro C hC
      have hex : ∃ a ∈ G, coset a = C := Finset.mem_image.mp hC
      dsimp only [pickA]
      rw [dite_cond_eq_true (eq_true hex)]
      exact Classical.choose_spec hex
    let i0 : Fin s := ⟨0, hs⟩
    let c0 : Nat := mass rows ∅
    let rep : Fin K → Option (Finset (Fin r)) := fun z =>
      if hz : z.val < L.length then some (pickA L[z.val]) else none
    let weight : Fin K → Fin s → Finset (Fin r) → Nat := fun z i u =>
      match rep z with
      | none => 0
      | some a =>
          if symmDiff (part owner a i) u ∈ G then
            if i = i0 then c0 else 1
          else 0
    have hprod_coset : ∀ (z : Fin K) (d : Finset (Fin r)),
        (Finset.univ : Finset (Fin s)).prod (fun i => weight z i (part owner d i)) =
        match rep z with
        | none => 0
        | some a => if d ∈ coset a then c0 else 0 := by
      intro z d
      cases hrz : rep z with
      | none =>
        refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
        simp [weight, hrz]
      | some a =>
        dsimp only
        by_cases hd : d ∈ coset a
        · simp only [hd, ↓reduceIte]
          have hH : symmDiff a d ∈ H := (hcoset_mem_iff a d).mp hd
          have hparts : ∀ i : Fin s, symmDiff (part owner a i) (part owner d i) ∈ G := by
            intro i
            rw [← part_symmDiff]
            exact (Finset.mem_filter.mp hH).2 i
          rw [Finset.prod_eq_single i0]
          · simp [weight, hrz, hparts i0]
          · intro i _ hne
            simp [weight, hrz, hparts i, hne]
          · intro habs; exact (habs (Finset.mem_univ i0)).elim
        · simp only [hd, ↓reduceIte]
          have hnotH : symmDiff a d ∉ H := fun hh => hd ((hcoset_mem_iff a d).mpr hh)
          have hex_bad : ∃ i : Fin s, symmDiff (part owner a i) (part owner d i) ∉ G := by
            by_contra hall
            push Not at hall
            apply hnotH
            refine mem_independent_of_parts rows owner (symmDiff a d) (fun i => ?_)
            rw [part_symmDiff]
            exact hall i
          obtain ⟨i1, hi1⟩ := hex_bad
          refine Finset.prod_eq_zero (Finset.mem_univ i1) ?_
          simp [weight, hrz, hi1]
    refine ⟨weight, fun d => ?_⟩
    change mass rows d = (Finset.univ : Finset (Fin K)).sum
      (fun z => (Finset.univ : Finset (Fin s)).prod (fun i => weight z i (part owner d i)))
    rw [Finset.sum_congr rfl (fun z _ => hprod_coset z d)]
    by_cases hdG : d ∈ G
    · rw [mass_eq_const rows d hdG]
      have hcd : coset d ∈ L := (hL_mem (coset d)).mpr (Finset.mem_image.mpr ⟨d, hdG, rfl⟩)
      obtain ⟨k, hk, hLk⟩ := List.mem_iff_getElem.mp hcd
      have hkK : k < K := by omega
      let z0 : Fin K := ⟨k, hkK⟩
      have hrz0 : rep z0 = some (pickA L[k]) := by
        dsimp only [rep, z0]; rw [dite_cond_eq_true (eq_true hk)]
      have ha0 : coset (pickA L[k]) = coset d := by
        have hLk_mem : L[k] ∈ Cosets := (hL_mem L[k]).mp (List.getElem_mem hk)
        exact (hpickA L[k] hLk_mem).2.trans hLk
      symm
      rw [Finset.sum_eq_single z0]
      · rw [hrz0]; dsimp only; rw [ha0]; simp [hcoset_self d, c0]
      · intro z _ hzne
        dsimp only [rep]
        split_ifs with hz
        · dsimp only
          have hLz_mem : L[z.val] ∈ Cosets := (hL_mem L[z.val]).mp (List.getElem_mem hz)
          have hcz : coset (pickA L[z.val]) = L[z.val] := (hpickA L[z.val] hLz_mem).2
          have hne_val : z.val ≠ k := fun heq => hzne (Fin.ext heq)
          have hLne : L[z.val] ≠ L[k] := fun heq =>
            hne_val ((List.Nodup.getElem_inj_iff hL_nd).mp heq)
          have hne_cos : coset (pickA L[z.val]) ≠ coset d := by
            rw [hcz, ← hLk]; exact hLne
          have hdisj : Disjoint (coset (pickA L[z.val])) (coset d) := by
            rcases hcoset_eq_or_disj (pickA L[z.val]) d with heq | hdj
            · exact (hne_cos heq).elim
            · exact hdj
          have hnot : d ∉ coset (pickA L[z.val]) := fun hm =>
            Finset.disjoint_left.mp hdisj hm (hcoset_self d)
          simp [hnot]
        · rfl
      · intro habs; exact (habs (Finset.mem_univ z0)).elim
    · rw [mass_eq_zero_of_not_mem rows d hdG]
      symm
      apply Finset.sum_eq_zero
      intro z _
      dsimp only [rep]
      split_ifs with hz
      · dsimp only
        have hLz_mem : L[z.val] ∈ Cosets := (hL_mem L[z.val]).mp (List.getElem_mem hz)
        have haG : pickA L[z.val] ∈ G := (hpickA L[z.val] hLz_mem).1
        have hnot : d ∉ coset (pickA L[z.val]) := fun hm => hdG (hcoset_sub _ haG hm)
        simp [hnot]
      · rfl
  exact ⟨⟨h1, fun h => h2 (h3 h)⟩, ⟨fun h => h1 (h2 h), h3⟩⟩

end PEqualNP.Outside.L_lib_1139_aux

theorem PEqualNP.Outside.L_lib_1139 : ∀ (m r s : Nat), 0 < s →
  ∀ (rows : Fin r → Finset (Fin m)) (owner : Fin r → Fin s),
  let xs := (Finset.univ : Finset (Finset (Fin m)))
  let parties := (Finset.univ : Finset (Fin s))
  let syn := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin r)).filter (fun j => ((rows j) ∩ x).card % 2 = 1)
  let part := fun (d : Finset (Fin r)) (i : Fin s) => d.filter (fun j => owner j = i)
  let imageSet := xs.image syn
  let independent := imageSet.filter (fun d => ∀ i : Fin s, part d i ∈ imageSet)
  let mass := fun (d : Finset (Fin r)) => (xs.filter (fun x => syn x = d)).card
  ∀ K : Nat,
    let cover := ∃ accept : Fin K → Fin s → Finset (Fin r) → Bool,
      ∀ d : Finset (Fin r), (d ∈ imageSet ↔
        ∃ z : Fin K, ∀ i : Fin s, accept z i (part d i) = true)
    let exactCount := ∃ weight : Fin K → Fin s → Finset (Fin r) → Nat,
      ∀ d : Finset (Fin r), mass d =
        (Finset.univ : Finset (Fin K)).sum
          (fun z => parties.prod (fun i => weight z i (part d i)))
    (cover ↔ imageSet.card ≤ K * independent.card) ∧
      (exactCount ↔ imageSet.card ≤ K * independent.card) :=
  PEqualNP.Outside.L_lib_1139_aux.main
