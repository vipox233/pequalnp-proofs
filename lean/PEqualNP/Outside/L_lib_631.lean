import Mathlib

theorem PEqualNP.Outside.L_lib_631 : ∀ (q m h t : Nat), 0 < q →
  let A := Fin (m+h)
  let W := Fin m → Fin q
  ∀ label : Fin m → A → Fin q,
    let live := fun (x : W) =>
      ((Finset.univ : Finset A).filter (fun a => ∀ i, x i ≠ label i a)).card
    let cert := fun (w : W) (I : Finset (Fin m)) (bucket : Fin m → Finset A) =>
      I.card ≤ h-t ∧ (I.biUnion bucket).card = I.card + (h-t) ∧
      (∀ i ∈ I, 2 ≤ (bucket i).card ∧ ∀ a ∈ bucket i, label i a = w i) ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (bucket i) (bucket j)
    (∀ x : W, live x ≤ t → ∃ I bucket, cert x I bucket) ∧
    ∀ (word : W) I bucket, cert word I bucket →
      ∃ y : W, (∀ j ∈ I, y j = word j) ∧ live y ≤ t := by
  classical
  intro q m h t hq
  dsimp only
  intro label
  constructor
  · intro x few
    by_cases hm : m = 0
    · subst m
      have ht : h ≤ t := by simpa using few
      exact ⟨∅,fun _ => ∅,by simp [Nat.sub_eq_zero_of_le ht]⟩
    letI : NeZero m := ⟨hm⟩
    letI : NeZero (m+h) := ⟨by omega⟩
    let dead := Finset.univ.filter (fun a : Fin (m+h) => ∃ i, x i = label i a)
    let owner (a : Fin (m+h)) : Fin m := if hz : ∃ i, x i = label i a then hz.choose else 0
    have owns {a} (ha : a ∈ dead) : x (owner a) = label (owner a) a := by
      have hz := (Finset.mem_filter.mp ha).2
      simpa [owner,hz] using hz.choose_spec
    let first (i : Fin m) : Fin (m+h) := if hz : ∃ a ∈ dead, owner a = i then hz.choose else 0
    have anchor {i} (hi : i ∈ dead.image owner) : first i ∈ dead ∧ owner (first i) = i := by
      have hz := Finset.mem_image.mp hi
      simpa [first,hz] using hz.choose_spec
    let used := Finset.univ.image first
    have usedCount : used.card ≤ m := by simpa [used] using (Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := first))
    let good := Finset.univ.filter (fun a : Fin (m+h) => ∀ i, x i ≠ label i a)
    change good.card ≤ t at few
    have ds : dead = Finset.univ \ good := by
      ext a
      simp [good,dead,not_forall]
    have dc : dead.card = m+h-good.card := by
      rw [ds,Finset.card_sdiff_of_subset (Finset.subset_univ good)]
      simp
    have cap := Finset.card_le_card (Finset.inter_subset_left (s₁ := used) (s₂ := dead))
    have hg : h-t ≤ (dead \ used).card := by
      rw [Finset.card_sdiff]
      omega
    obtain ⟨E,hE,nE⟩ := Finset.exists_subset_card_eq hg
    let I := E.image owner
    have anch {i} (hi : i ∈ I) : first i ∈ dead ∧ owner (first i) = i := by
      apply anchor
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.mp (hE ha)).1
    let T := E ∪ I.image first
    let B := fun i => T.filter (fun a => owner a = i)
    have allT {a} (ha : a ∈ T) : a ∈ dead ∧ owner a ∈ I := by
      rcases Finset.mem_union.mp ha with e|f
      · exact ⟨(Finset.mem_sdiff.mp (hE e)).1,Finset.mem_image_of_mem _ e⟩
      · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp f
        exact ⟨(anch hi).1,(anch hi).2.symm ▸ hi⟩
    have full : I.biUnion B = T := by
      ext a
      constructor
      · intro ha
        obtain ⟨i,_,has⟩ := Finset.mem_biUnion.mp ha
        exact (Finset.mem_filter.mp has).1
      · intro ha
        exact Finset.mem_biUnion.mpr ⟨owner a,(allT ha).2,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
    have dis : Disjoint E (I.image first) := by
      apply Finset.disjoint_left.mpr
      intro a ha hf
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
      exact (Finset.mem_sdiff.mp (hE ha)).2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have count : (I.image first).card = I.card := by
      apply Finset.card_image_iff.mpr
      intro a ha b hb eq
      exact (anch ha).2.symm.trans ((congrArg owner eq).trans (anch hb).2)
    refine ⟨I,B,?_,?_,?_,?_⟩
    · simpa [I,nE] using (Finset.card_image_le (f := owner) (s := E))
    · rw [full,show T.card = _ from Finset.card_union_of_disjoint dis,count,nE,Nat.add_comm]
    · intro i hi
      obtain ⟨a,ha,ea⟩ := Finset.mem_image.mp hi
      have af : first i ∈ I.image first := Finset.mem_image_of_mem first hi
      have ne : a ∉ I.image first := Finset.disjoint_left.mp dis ha
      refine ⟨Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_union_left _ ha,ea⟩,
        first i,Finset.mem_filter.mpr ⟨Finset.mem_union_right _ af,(anch hi).2⟩,?_⟩,?_⟩
      · exact fun eq => ne (eq.symm ▸ af)
      · intro v hv
        obtain ⟨hh,eq⟩ := Finset.mem_filter.mp hv
        simpa [← eq] using (owns (allT hh).1).symm
    · intro i _ j _ ne
      exact Finset.disjoint_left.mpr (fun a ha hb =>
        ne ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2))
  · intro word I B cert
    obtain ⟨size,total,matchB,_⟩ := cert
    let killed := I.biUnion B
    let left := (Finset.univ : Finset (Fin (m+h))) \ killed
    let free := (Finset.univ : Finset (Fin m)) \ I
    have lc : left.card = m+h-killed.card := by simp [left,Finset.card_sdiff_of_subset (Finset.subset_univ killed)]
    have fc : free.card = m-I.card := by simp [free,Finset.card_sdiff_of_subset (Finset.subset_univ I)]
    have ic : I.card ≤ m := by simpa using Finset.card_le_univ I
    change killed.card = _ at total
    have enough : left.card-t ≤ free.card := by omega
    obtain ⟨E,hE,nE⟩ := Finset.exists_subset_card_eq (Nat.sub_le left.card t)
    have fit : Fintype.card ↥E ≤ Fintype.card ↥free := by simpa [nE] using enough
    let emb : ↥E ↪ ↥free := (Fintype.equivFin ↥E).toEmbedding.trans
      ((Fin.castLEEmb fit).trans (Fintype.equivFin ↥free).symm.toEmbedding)
    let site (a : ↥E) : Fin m := (emb a).val
    have inj : Function.Injective site := Subtype.val_injective.comp emb.injective
    let y := Function.extend site (fun a => label (site a) a.val) word
    have kept {i} (hi : i ∈ I) : y i = word i := by
      have miss : i ∉ Set.range site := by
        rintro ⟨a,rfl⟩
        exact (Finset.mem_sdiff.mp (emb a).property).2 hi
      exact Function.extend_apply' _ _ _ miss
    refine ⟨y,fun _ => kept,?_⟩
    have sub : (Finset.univ.filter (fun a => ∀ i, y i ≠ label i a)) ⊆ left \ E := by
      intro a ha
      have ok := (Finset.mem_filter.mp ha).2
      apply Finset.mem_sdiff.mpr
      constructor
      · refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
        intro h
        obtain ⟨i,hi,inB⟩ := Finset.mem_biUnion.mp h
        exact ok i ((kept hi).trans ((matchB i hi).2 a inB).symm)
      · intro he
        let z : ↥E := ⟨a,he⟩
        exact ok (site z) (inj.extend_apply _ _ z)
    have bound := Finset.card_le_card sub
    rw [Finset.card_sdiff_of_subset hE,nE] at bound
    omega
