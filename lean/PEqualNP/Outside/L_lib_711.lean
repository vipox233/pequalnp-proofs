import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_711_aux

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

private lemma zmod2_add_cancel {x y z : ZMod 2} (h : x + z = y + z) : x = y := by
  exact add_right_cancel h

private lemma zmod2_add_eq_iff {x y z : ZMod 2} : x + y = z ↔ x = z + y := by
  constructor
  · intro h; rw [← h, add_assoc, zmod2_add_self, add_zero]
  · intro h; rw [h, add_assoc, zmod2_add_self, add_zero]

private lemma zmod2_swap_add {a b c d : ZMod 2} (h : a + b = c + d) : a + c = b + d := by
  have h1 : a + b + (b + c) = c + d + (b + c) := by rw [h]
  have hL : a + b + (b + c) = a + c := by
    calc a + b + (b + c) = a + (b + b) + c := by ring
      _ = a + 0 + c := by rw [zmod2_add_self]
      _ = a + c := by ring
  have hR : c + d + (b + c) = b + d := by
    calc c + d + (b + c) = (c + c) + (b + d) := by ring
      _ = 0 + (b + d) := by rw [zmod2_add_self]
      _ = b + d := by ring
  rw [hL, hR] at h1
  exact h1

private lemma zmod2_mul_eq_ite (a b : ZMod 2) : a * b = if a = 1 then b else 0 := by
  fin_cases a <;> fin_cases b <;> decide

private lemma prod_add_finset {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α → ZMod 2) :
    ∏ x ∈ s, (a x + b x) =
      ∑ t ∈ s.powerset, (∏ x ∈ s \ t, a x) * (∏ x ∈ t, b x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, ih, Finset.powerset_insert]
    rw [Finset.sum_union]
    · rw [Finset.sum_image]
      · rw [add_mul, Finset.mul_sum, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl
          intro t ht
          have hxt : x ∉ t := fun h => hx (Finset.mem_powerset.mp ht h)
          have hsdiff : insert x s \ t = insert x (s \ t) := by
            ext y
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hy, hyt⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hy, hyt⟩
            · rintro (rfl | ⟨hy, hyt⟩)
              · exact ⟨Or.inl rfl, hxt⟩
              · exact ⟨Or.inr hy, hyt⟩
          rw [hsdiff, Finset.prod_insert (by simp [hx]), mul_assoc]
        · apply Finset.sum_congr rfl
          intro t ht
          have hxt : x ∉ t := fun h => hx (Finset.mem_powerset.mp ht h)
          have hsdiff : insert x s \ insert x t = s \ t := by
            ext y
            simp only [Finset.mem_sdiff, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hy, hnot⟩
              · exact (hnot (Or.inl rfl)).elim
              · exact ⟨hy, fun h => hnot (Or.inr h)⟩
            · rintro ⟨hy, hyt⟩
              refine ⟨Or.inr hy, ?_⟩
              rintro (rfl | h)
              · exact hx hy
              · exact hyt h
          rw [hsdiff, Finset.prod_insert hxt]
          ring
      · intro t1 ht1 t2 ht2 heq
        have h1 : x ∉ t1 := fun h => hx (Finset.mem_powerset.mp ht1 h)
        have h2 : x ∉ t2 := fun h => hx (Finset.mem_powerset.mp ht2 h)
        ext y
        by_cases hy : y = x
        · subst hy; exact iff_of_false h1 h2
        · have := congrArg (fun u => y ∈ u) heq
          simpa [Finset.mem_insert, hy] using this
    · rw [Finset.disjoint_left]
      intro u hu1 hu2
      rcases Finset.mem_image.mp hu2 with ⟨t, _, rfl⟩
      exact hx (Finset.mem_powerset.mp hu1 (Finset.mem_insert_self x t))

private lemma indicator_zero_vec {m : ℕ} (u : Fin m → ZMod 2) :
    (∏ k : Fin m, (1 + u k)) = if u = 0 then 1 else 0 := by
  by_cases hu : u = 0
  · subst hu
    simp
  · rw [if_neg hu]
    have hex : ∃ k : Fin m, u k ≠ 0 := by
      by_contra h
      apply hu
      funext k
      by_contra hk
      exact h ⟨k, hk⟩
    rcases hex with ⟨k, hk⟩
    have hk1 : u k = 1 := (zmod2_cases (u k)).resolve_left hk
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [hk1]
    rfl

private lemma exists_finset_of_weighted_sum {α J : Type*} [DecidableEq J]
    (m : ℕ) (F : Finset α) (g : α → ZMod 2) (M : α → Finset J)
    (hcard : ∀ a ∈ F, (M a).card ≤ m) :
    ∃ T : Finset (Finset J), (∀ mon ∈ T, mon.card ≤ m) ∧
      ∀ (val : J → ZMod 2),
        (∑ mon ∈ T, ∏ j ∈ mon, val j) = ∑ a ∈ F, g a * ∏ j ∈ M a, val j := by
  classical
  let U := F.image M
  let coeff : Finset J → ZMod 2 := fun mon => ∑ a ∈ F with M a = mon, g a
  let T := U.filter (fun mon => coeff mon = 1)
  refine ⟨T, ?_, ?_⟩
  · intro mon hmon
    have hU : mon ∈ U := (Finset.mem_filter.mp hmon).1
    rcases Finset.mem_image.mp hU with ⟨a, ha, rfl⟩
    exact hcard a ha
  · intro val
    have hgroup : (∑ a ∈ F, g a * ∏ j ∈ M a, val j) =
        ∑ mon ∈ U, coeff mon * ∏ j ∈ mon, val j := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := M) (t := U)
        (fun a ha => Finset.mem_image_of_mem M ha)]
      apply Finset.sum_congr rfl
      intro mon _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    rw [hgroup, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro mon _
    rw [zmod2_mul_eq_ite]

private lemma sum_shift_monomial_const (m h : ℕ)
    (mon : Finset (((Fin m → ZMod 2) × (Fin h → ZMod 2)) × (Fin m ⊕ Fin h)))
    (hmon : mon.card ≤ m) :
    ∃ C : ZMod 2, ∀ p : Equiv.Perm ((Fin m → ZMod 2) × (Fin h → ZMod 2)),
      (∑ s : Fin m → ZMod 2,
        ∏ j ∈ mon, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2) = C := by
  classical
  let U := Fin m → ZMod 2
  let H := Fin h → ZMod 2
  let I := U × H
  let J := I × (Fin m ⊕ Fin h)
  let b : U → J → ZMod 2 := fun s j => Sum.elim s (fun _ => 0) j.2
  refine ⟨∑ s : U, ∏ j ∈ mon, b s j, ?_⟩
  intro p
  let a : J → ZMod 2 := fun j => Sum.elim (p j.1).1 (p j.1).2 j.2
  have hfactor : ∀ (s : U) (j : J),
      Sum.elim ((p j.1).1 + s) (p j.1).2 j.2 = a j + b s j := by
    intro s j
    rcases j with ⟨x, k | k⟩
    · rfl
    · simp [a, b]
  calc
    (∑ s : U, ∏ j ∈ mon, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2)
        = ∑ s : U, ∏ j ∈ mon, (a j + b s j) := by
            apply Finset.sum_congr rfl; intro s _
            apply Finset.prod_congr rfl; intro j _; exact hfactor s j
    _ = ∑ s : U, ∑ A ∈ mon.powerset, (∏ j ∈ mon \ A, a j) * (∏ j ∈ A, b s j) := by
            apply Finset.sum_congr rfl; intro s _; exact prod_add_finset mon a (b s)
    _ = ∑ A ∈ mon.powerset, (∏ j ∈ mon \ A, a j) * (∑ s : U, ∏ j ∈ A, b s j) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro A _
            rw [Finset.mul_sum]
    _ = ∑ s : U, ∏ j ∈ mon, b s j := by
            rw [Finset.sum_eq_single mon]
            · simp
            · intro A hA hAne
              have hAsub : A ⊆ mon := Finset.mem_powerset.mp hA
              have hAlt : A.card < m := by
                have hlt : A.card < mon.card :=
                  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, hAne⟩)
                omega
              have hsum0 : (∑ s : U, ∏ j ∈ A, b s j) = 0 := by
                have hexk : ∃ k0 : Fin m, ∀ j ∈ A, j.2 ≠ Sum.inl k0 := by
                  by_contra hall
                  push Not at hall
                  let proj : J → Option (Fin m) := fun j =>
                    Sum.elim some (fun _ => none) j.2
                  have hsub : (Finset.univ : Finset (Fin m)).image some ⊆ A.image proj := by
                    intro y hy
                    rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
                    rcases hall k with ⟨j, hjA, hjk⟩
                    exact Finset.mem_image.mpr ⟨j, hjA, by simp [proj, hjk]⟩
                  have h1 : m ≤ (A.image proj).card := by
                    have h2 := Finset.card_le_card hsub
                    rw [Finset.card_image_of_injective _ (Option.some_injective (Fin m)),
                        Finset.card_fin] at h2
                    exact h2
                  have h3 : (A.image proj).card ≤ A.card := Finset.card_image_le
                  omega
                rcases hexk with ⟨k0, hk0⟩
                let U0 : Finset U := Finset.univ.filter (fun s => s k0 = 0)
                let U1 : Finset U := Finset.univ.filter (fun s => s k0 = 1)
                let flip : U → U := fun s => Function.update s k0 (s k0 + 1)
                have hpart : (Finset.univ : Finset U) = U0 ∪ U1 := by
                  ext s
                  simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, U0, U1]
                  exact ⟨fun _ => zmod2_cases (s k0), fun _ => trivial⟩
                have hdisj : Disjoint U0 U1 := by
                  rw [Finset.disjoint_left]
                  intro s h0 h1
                  have e0 := (Finset.mem_filter.mp h0).2
                  have e1 := (Finset.mem_filter.mp h1).2
                  rw [e0] at e1
                  exact zero_ne_one e1
                have hflip_inv : ∀ s : U, flip (flip s) = s := by
                  intro s
                  funext k
                  by_cases hk : k = k0
                  · subst hk
                    simp [flip, add_assoc, zmod2_add_self]
                  · simp [flip, hk]
                have hval : ∀ s : U, (∏ j ∈ A, b (flip s) j) = ∏ j ∈ A, b s j := by
                  intro s
                  apply Finset.prod_congr rfl
                  intro j hj
                  rcases j with ⟨x, k | k⟩
                  · have hne : k ≠ k0 := fun heq => hk0 (x, Sum.inl k) hj (by rw [heq])
                    simp [b, flip, hne]
                  · simp [b]
                have hbij : (∑ s ∈ U0, ∏ j ∈ A, b s j) = ∑ s ∈ U1, ∏ j ∈ A, b s j := by
                  refine Finset.sum_nbij flip ?_ ?_ ?_ ?_
                  · intro s hs
                    have hs0 : s k0 = 0 := (Finset.mem_filter.mp hs).2
                    simp [U1, flip, hs0]
                  · intro s1 _ s2 _ hEq
                    have := congrArg flip hEq
                    simpa [hflip_inv] using this
                  · intro s hs
                    have hs1 : s k0 = 1 := (Finset.mem_filter.mp hs).2
                    refine ⟨flip s, ?_, hflip_inv s⟩
                    simp [U0, flip, hs1, zmod2_add_self]
                  · intro s _
                    exact (hval s).symm
                rw [hpart, Finset.sum_union hdisj, ← hbij, zmod2_add_self]
              rw [hsum0, mul_zero]
            · intro hnot
              exact (hnot (Finset.mem_powerset.mpr (Finset.Subset.refl mon))).elim

private lemma exists_inj_into {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (S : Finset β) (hcard : Fintype.card α ≤ S.card) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, f a ∈ S := by
  have hle : Fintype.card α ≤ Fintype.card {b // b ∈ S} := by
    rw [Fintype.card_coe]; exact hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  refine ⟨fun a => (e a).1, ?_, fun a => (e a).2⟩
  intro a1 a2 h
  exact e.injective (Subtype.ext h)

private lemma exists_inj_fixing {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (a0 : α) (b0 : β) (S : Finset β) (hb0 : b0 ∉ S)
    (hcard : Fintype.card α ≤ S.card + 1) :
    ∃ f : α → β, Function.Injective f ∧ f a0 = b0 ∧ ∀ a, a ≠ a0 → f a ∈ S := by
  have hcard' : Fintype.card {a : α // a ≠ a0} ≤ S.card := by
    have h1 : Fintype.card {a : α // a ≠ a0} = Fintype.card α - 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  obtain ⟨g, hginj, hgS⟩ := exists_inj_into (α := {a : α // a ≠ a0}) S hcard'
  refine ⟨fun a => if h : a = a0 then b0 else g ⟨a, h⟩, ?_, ?_, ?_⟩
  · intro a1 a2 heq
    by_cases h1 : a1 = a0 <;> by_cases h2 : a2 = a0
    · exact h1.trans h2.symm
    · simp only [dif_pos h1, dif_neg h2] at heq
      exact (hb0 (heq ▸ hgS ⟨a2, h2⟩)).elim
    · simp only [dif_neg h1, dif_pos h2] at heq
      exact (hb0 (heq.symm ▸ hgS ⟨a1, h1⟩)).elim
    · simp only [dif_neg h1, dif_neg h2] at heq
      exact congrArg Subtype.val (hginj heq)
  · simp
  · intro a ha
    simp [ha, hgS]

private lemma two_block_swap {U H I : Type*} [Fintype U] [Fintype H] [Fintype I]
    [DecidableEq U] [DecidableEq H] [DecidableEq I]
    (eUI : U × H ≃ I)
    (s1 s2 : U) (hs12 : s1 ≠ s2)
    (f : (H → I) → ZMod 2) (C0 : ZMod 2)
    (hEq : ∀ p : Equiv.Perm I, (∑ s : U, f (fun t => p.symm (eUI (s, t)))) = C0)
    (v1 v2 w1 w2 : H → I)
    (hv1 : Function.Injective v1) (hv2 : Function.Injective v2)
    (hw1 : Function.Injective w1) (hw2 : Function.Injective w2)
    (hdisjV : ∀ t1 t2, v1 t1 ≠ v2 t2)
    (hdisjW : ∀ t1 t2, w1 t1 ≠ w2 t2)
    (hunion : Finset.univ.image v1 ∪ Finset.univ.image v2 =
              Finset.univ.image w1 ∪ Finset.univ.image w2) :
    f v1 + f v2 = f w1 + f w2 := by
  classical
  let R : Finset I := Finset.univ.image v1 ∪ Finset.univ.image v2
  have hdisjFinV : Disjoint (Finset.univ.image v1) (Finset.univ.image v2) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨t1, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨t2, _, h⟩
    exact hdisjV t1 t2 h.symm
  have hRcard : R.card = 2 * Fintype.card H := by
    rw [Finset.card_union_of_disjoint hdisjFinV,
        Finset.card_image_of_injective _ hv1, Finset.card_image_of_injective _ hv2,
        Finset.card_univ]
    omega
  have hUge2 : 2 ≤ Fintype.card U := by
    have hsub : ({s1, s2} : Finset U) ⊆ Finset.univ := Finset.subset_univ _
    have hc := Finset.card_le_card hsub
    rw [Finset.card_pair hs12, Finset.card_univ] at hc
    exact hc
  let Urem : Finset U := (Finset.univ.erase s1).erase s2
  have hUremCard : Urem.card = Fintype.card U - 2 := by
    have hs2in : s2 ∈ Finset.univ.erase s1 :=
      Finset.mem_erase.mpr ⟨hs12.symm, Finset.mem_univ s2⟩
    rw [Finset.card_erase_of_mem hs2in, Finset.card_erase_of_mem (Finset.mem_univ s1),
        Finset.card_univ]
    omega
  have hcardEq : Fintype.card {p : U × H // p.1 ∈ Urem} = Fintype.card {x : I // x ∉ R} := by
    have hL : Fintype.card {p : U × H // p.1 ∈ Urem} = Urem.card * Fintype.card H := by
      have heq : {p : U × H // p.1 ∈ Urem} ≃ {s : U // s ∈ Urem} × H :=
        { toFun := fun p => (⟨p.1.1, p.2⟩, p.1.2)
          invFun := fun q => ⟨(q.1.1, q.2), q.1.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr heq, Fintype.card_prod, Fintype.card_coe]
    have hRc : Fintype.card {x : I // x ∉ R} = Fintype.card I - R.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    have hIcard : Fintype.card I = Fintype.card U * Fintype.card H := by
      rw [← Fintype.card_congr eUI, Fintype.card_prod]
    rw [hL, hRc, hUremCard, hIcard, hRcard, Nat.sub_mul]
  let rem : {p : U × H // p.1 ∈ Urem} ≃ {x : I // x ∉ R} := Fintype.equivOfCardEq hcardEq
  have mkPerm : ∀ (a1 a2 : H → I),
      Function.Injective a1 → Function.Injective a2 →
      (∀ t1 t2, a1 t1 ≠ a2 t2) →
      Finset.univ.image a1 ∪ Finset.univ.image a2 = R →
      ∃ p : Equiv.Perm I,
        (∀ t, p.symm (eUI (s1, t)) = a1 t) ∧
        (∀ t, p.symm (eUI (s2, t)) = a2 t) ∧
        (∀ s (hs : s ∈ Urem), ∀ t, p.symm (eUI (s, t)) = (rem ⟨(s, t), hs⟩).1) := by
    intro a1 a2 ha1 ha2 hdisjA hAeq
    have hmem1 : ∀ t, a1 t ∈ R := fun t => by
      rw [← hAeq]; exact Finset.mem_union_left _ (Finset.mem_image_of_mem a1 (Finset.mem_univ t))
    have hmem2 : ∀ t, a2 t ∈ R := fun t => by
      rw [← hAeq]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem a2 (Finset.mem_univ t))
    let g : U × H → I := fun q =>
      if h1 : q.1 = s1 then a1 q.2
      else if h2 : q.1 = s2 then a2 q.2
      else (rem ⟨q, Finset.mem_erase.mpr ⟨h2, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ q.1⟩⟩⟩).1
    have hginj : Function.Injective g := by
      intro q1 q2 heq
      by_cases h11 : q1.1 = s1 <;> by_cases h21 : q2.1 = s1
      · simp [g, h11, h21] at heq
        exact Prod.ext (h11.trans h21.symm) (ha1 heq)
      · by_cases h22 : q2.1 = s2
        · simp [g, h11, h22, hs12.symm] at heq
          exact (hdisjA q1.2 q2.2 heq).elim
        · simp [g, h11, h21, h22] at heq
          have hq2 : q2.1 ∈ Urem := Finset.mem_erase.mpr ⟨h22, Finset.mem_erase.mpr ⟨h21, Finset.mem_univ q2.1⟩⟩
          have hnotR := (rem ⟨q2, hq2⟩).2
          exact (hnotR (heq ▸ hmem1 q1.2)).elim
      · by_cases h12 : q1.1 = s2
        · simp [g, h12, h21, hs12.symm] at heq
          exact (hdisjA q2.2 q1.2 heq.symm).elim
        · simp [g, h11, h12, h21] at heq
          have hq1 : q1.1 ∈ Urem := Finset.mem_erase.mpr ⟨h12, Finset.mem_erase.mpr ⟨h11, Finset.mem_univ q1.1⟩⟩
          have hnotR := (rem ⟨q1, hq1⟩).2
          exact (hnotR (heq.symm ▸ hmem1 q2.2)).elim
      · by_cases h12 : q1.1 = s2 <;> by_cases h22 : q2.1 = s2
        · simp [g, h12, h22, hs12.symm] at heq
          exact Prod.ext (h12.trans h22.symm) (ha2 heq)
        · simp [g, h12, h21, h22, hs12.symm] at heq
          have hq2 : q2.1 ∈ Urem := Finset.mem_erase.mpr ⟨h22, Finset.mem_erase.mpr ⟨h21, Finset.mem_univ q2.1⟩⟩
          have hnotR := (rem ⟨q2, hq2⟩).2
          exact (hnotR (heq ▸ hmem2 q1.2)).elim
        · simp [g, h11, h12, h22, hs12.symm] at heq
          have hq1 : q1.1 ∈ Urem := Finset.mem_erase.mpr ⟨h12, Finset.mem_erase.mpr ⟨h11, Finset.mem_univ q1.1⟩⟩
          have hnotR := (rem ⟨q1, hq1⟩).2
          exact (hnotR (heq.symm ▸ hmem2 q2.2)).elim
        · simp [g, h11, h12, h21, h22] at heq
          have := rem.injective (Subtype.ext heq)
          exact congrArg Subtype.val this
    let eG : U × H ≃ I := Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr
      ⟨hginj, by rw [← Fintype.card_congr eUI]⟩)
    let p : Equiv.Perm I := eG.symm.trans eUI
    refine ⟨p, ?_, ?_, ?_⟩
    · intro t
      change eG (eUI.symm (eUI (s1, t))) = a1 t
      rw [eUI.symm_apply_apply]
      simp [eG, g]
    · intro t
      change eG (eUI.symm (eUI (s2, t))) = a2 t
      rw [eUI.symm_apply_apply]
      simp [eG, g, hs12.symm]
    · intro s hs t
      have hs2 : s ≠ s2 := (Finset.mem_erase.mp hs).1
      have hs1 : s ≠ s1 := (Finset.mem_erase.mp (Finset.mem_erase.mp hs).2).1
      change eG (eUI.symm (eUI (s, t))) = _
      rw [eUI.symm_apply_apply]
      simp [eG, g, hs1, hs2]
  obtain ⟨pV, hpV1, hpV2, hpVr⟩ := mkPerm v1 v2 hv1 hv2 hdisjV rfl
  obtain ⟨pW, hpW1, hpW2, hpWr⟩ := mkPerm w1 w2 hw1 hw2 hdisjW hunion.symm
  have hsumSplit : ∀ (G : U → ZMod 2),
      (∑ s : U, G s) = G s1 + G s2 + ∑ s ∈ Urem, G s := by
    intro G
    have hs2in : s2 ∈ Finset.univ.erase s1 :=
      Finset.mem_erase.mpr ⟨hs12.symm, Finset.mem_univ s2⟩
    rw [← Finset.add_sum_erase Finset.univ G (Finset.mem_univ s1)]
    rw [← Finset.add_sum_erase (Finset.univ.erase s1) G hs2in]
    rw [add_assoc]
  have h1 := hEq pV
  have h2 := hEq pW
  rw [hsumSplit] at h1 h2
  have hremEq : (∑ s ∈ Urem, f (fun t => pV.symm (eUI (s, t)))) =
      ∑ s ∈ Urem, f (fun t => pW.symm (eUI (s, t))) := by
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    funext t
    rw [hpVr s hs t, hpWr s hs t]
  have hfv1 : (fun t => pV.symm (eUI (s1, t))) = v1 := funext hpV1
  have hfv2 : (fun t => pV.symm (eUI (s2, t))) = v2 := funext hpV2
  have hfw1 : (fun t => pW.symm (eUI (s1, t))) = w1 := funext hpW1
  have hfw2 : (fun t => pW.symm (eUI (s2, t))) = w2 := funext hpW2
  rw [hfv1, hfv2] at h1
  rw [hfw1, hfw2, ← hremEq] at h2
  exact zmod2_add_cancel (h1.trans h2.symm)

private lemma additive_of_equipartition {U H I : Type*} [Fintype U] [Fintype H] [Fintype I]
    [DecidableEq U] [DecidableEq H] [DecidableEq I]
    (eUI : U × H ≃ I)
    (hU4 : 4 ≤ Fintype.card U)
    (h0 : H)
    (f : (H → I) → ZMod 2) (C0 : ZMod 2)
    (hEq : ∀ p : Equiv.Perm I, (∑ s : U, f (fun t => p.symm (eUI (s, t)))) = C0) :
    ∃ (c : ZMod 2) (z : I → ZMod 2), ∀ v : H → I, Function.Injective v →
      f v = c + ∑ t : H, z (v t) := by
  classical
  have hHpos : 1 ≤ Fintype.card H := Fintype.card_pos_iff.mpr ⟨h0⟩
  have hIcard : Fintype.card I = Fintype.card U * Fintype.card H := by
    rw [← Fintype.card_congr eUI, Fintype.card_prod]
  have hUgt1 : 1 < Fintype.card U := by omega
  obtain ⟨s1, s2, hs12⟩ := Fintype.exists_pair_of_one_lt_card hUgt1
  have hswap := two_block_swap eUI s1 s2 hs12 f C0 hEq
  have hupd_inj : ∀ (v : H → I) (t : H) (b : I),
      Function.Injective v → (∀ s, v s ≠ b) →
      Function.Injective (Function.update v t b) := by
    intro v t b hv hb s1' s2' heq
    by_cases h1 : s1' = t <;> by_cases h2 : s2' = t
    · exact h1.trans h2.symm
    · subst h1
      simp only [Function.update_self, Function.update_of_ne h2] at heq
      exact (hb s2' heq.symm).elim
    · subst h2
      simp only [Function.update_of_ne h1, Function.update_self] at heq
      exact (hb s1' heq).elim
    · simp only [Function.update_of_ne h1, Function.update_of_ne h2] at heq
      exact hv heq
  have hupd_img : ∀ (v : H → I) (t : H) (b : I),
      Function.Injective v →
      Finset.univ.image (Function.update v t b) =
        insert b ((Finset.univ.image v).erase (v t)) := by
    intro v t b hv
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨s, rfl⟩
      by_cases hs : s = t
      · left; simp [hs]
      · right
        rw [Function.update_of_ne hs]
        exact ⟨fun heq => hs (hv heq), s, rfl⟩
    · rintro (rfl | ⟨hne, s, rfl⟩)
      · exact ⟨t, Function.update_self t x v⟩
      · have hst : s ≠ t := fun h => hne (by rw [h])
        exact ⟨s, Function.update_of_ne hst b v⟩
  have hsingle_swap : ∀ (v1 v2 : H → I) (t1 t2 : H),
      Function.Injective v1 → Function.Injective v2 →
      (∀ x y, v1 x ≠ v2 y) →
      f v1 + f (Function.update v1 t1 (v2 t2)) =
        f v2 + f (Function.update v2 t2 (v1 t1)) := by
    intro v1 v2 t1 t2 hv1 hv2 hdisj
    let w1 := Function.update v1 t1 (v2 t2)
    let w2 := Function.update v2 t2 (v1 t1)
    have hw1 : Function.Injective w1 := hupd_inj v1 t1 (v2 t2) hv1 (fun s => hdisj s t2)
    have hw2 : Function.Injective w2 := hupd_inj v2 t2 (v1 t1) hv2 (fun s => (hdisj t1 s).symm)
    have hdisjW : ∀ x y, w1 x ≠ w2 y := by
      intro x y
      by_cases hx : x = t1 <;> by_cases hy : y = t2
      · simp only [w1, w2, hx, hy, Function.update_self]; exact (hdisj t1 t2).symm
      · simp only [w1, w2, hx, Function.update_self, Function.update_of_ne hy]
        exact fun h => hy (hv2 h.symm)
      · simp only [w1, w2, hy, Function.update_of_ne hx, Function.update_self]
        exact fun h => hx (hv1 h)
      · simp only [w1, w2, Function.update_of_ne hx, Function.update_of_ne hy]
        exact hdisj x y
    have hunion : Finset.univ.image v1 ∪ Finset.univ.image v2 =
        Finset.univ.image w1 ∪ Finset.univ.image w2 := by
      rw [hupd_img v1 t1 (v2 t2) hv1, hupd_img v2 t2 (v1 t1) hv2]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
        · by_cases hs : s = t1
          · right; left; exact congrArg v1 hs
          · left; right; exact ⟨fun h => hs (hv1 h), s, rfl⟩
        · by_cases hs : s = t2
          · left; left; exact congrArg v2 hs
          · right; right; exact ⟨fun h => hs (hv2 h), s, rfl⟩
      · rintro ((rfl | ⟨_, s, rfl⟩) | (rfl | ⟨_, s, rfl⟩))
        · right; exact ⟨t2, rfl⟩
        · left; exact ⟨s, rfl⟩
        · left; exact ⟨t1, rfl⟩
        · right; exact ⟨s, rfl⟩
    exact zmod2_swap_add (hswap v1 v2 w1 w2 hv1 hv2 hw1 hw2 hdisj hdisjW hunion)
  have hswap_indep : ∀ (v1 u1 : H → I) (t1 s1' : H) (b : I),
      Function.Injective v1 → Function.Injective u1 →
      v1 t1 = u1 s1' →
      (∀ t, v1 t ≠ b) → (∀ t, u1 t ≠ b) →
      f v1 + f (Function.update v1 t1 b) = f u1 + f (Function.update u1 s1' b) := by
    intro v1 u1 t1 s1' b hv1 hu1 ha hbv hbu
    let bad : Finset I := Finset.univ.image v1 ∪ Finset.univ.image u1 ∪ {b}
    have hbad_le : bad.card ≤ 2 * Fintype.card H := by
      have ha_inter : v1 t1 ∈ Finset.univ.image v1 ∩ Finset.univ.image u1 :=
        Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem v1 (Finset.mem_univ t1),
          ha ▸ Finset.mem_image_of_mem u1 (Finset.mem_univ s1')⟩
      have hinter_pos : 1 ≤ (Finset.univ.image v1 ∩ Finset.univ.image u1).card :=
        Finset.one_le_card.mpr ⟨v1 t1, ha_inter⟩
      have hun : (Finset.univ.image v1 ∪ Finset.univ.image u1).card +
          (Finset.univ.image v1 ∩ Finset.univ.image u1).card =
          (Finset.univ.image v1).card + (Finset.univ.image u1).card :=
        Finset.card_union_add_card_inter _ _
      have hc1 : (Finset.univ.image v1).card = Fintype.card H := by
        rw [Finset.card_image_of_injective _ hv1, Finset.card_univ]
      have hc2 : (Finset.univ.image u1).card = Fintype.card H := by
        rw [Finset.card_image_of_injective _ hu1, Finset.card_univ]
      have h3 : bad.card ≤ (Finset.univ.image v1 ∪ Finset.univ.image u1).card + 1 := by
        calc bad.card ≤ (Finset.univ.image v1 ∪ Finset.univ.image u1).card + ({b} : Finset I).card :=
              Finset.card_union_le _ _
          _ = (Finset.univ.image v1 ∪ Finset.univ.image u1).card + 1 := by simp
      omega
    let Sfree : Finset I := Finset.univ \ bad
    have hSfree : Fintype.card H ≤ Sfree.card + 1 := by
      have hsc : Sfree.card = Fintype.card I - bad.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      have h1 : 4 * Fintype.card H ≤ Fintype.card I := by
        rw [hIcard]; exact Nat.mul_le_mul_right _ hU4
      omega
    have hbnotS : b ∉ Sfree := by
      simp [Sfree, bad]
    obtain ⟨v2, hv2, hv20, hv2S⟩ := exists_inj_fixing h0 b Sfree hbnotS hSfree
    have hdisj1 : ∀ x y, v1 x ≠ v2 y := by
      intro x y
      by_cases hy : y = h0
      · subst hy; rw [hv20]; exact hbv x
      · intro heq
        have hmem := hv2S y hy
        have hnotbad := (Finset.mem_sdiff.mp hmem).2
        apply hnotbad
        rw [← heq]
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_image_of_mem v1 (Finset.mem_univ x)))
    have hdisj2 : ∀ x y, u1 x ≠ v2 y := by
      intro x y
      by_cases hy : y = h0
      · subst hy; rw [hv20]; exact hbu x
      · intro heq
        have hmem := hv2S y hy
        have hnotbad := (Finset.mem_sdiff.mp hmem).2
        apply hnotbad
        rw [← heq]
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image_of_mem u1 (Finset.mem_univ x)))
    have hA := hsingle_swap v1 v2 t1 h0 hv1 hv2 hdisj1
    have hB := hsingle_swap u1 v2 s1' h0 hu1 hv2 hdisj2
    rw [hv20] at hA hB
    rw [ha] at hA
    exact hA.trans hB.symm
  have hex_witness : ∀ a b : I, a ≠ b →
      ∃ w : H → I, Function.Injective w ∧ w h0 = a ∧ ∀ t, w t ≠ b := by
    intro a b hab
    let S : Finset I := (Finset.univ.erase a).erase b
    have hb_in : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
    have hScard : S.card = Fintype.card I - 2 := by
      rw [Finset.card_erase_of_mem hb_in, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ]
      omega
    have h1 : 4 * Fintype.card H ≤ Fintype.card I := by
      rw [hIcard]; exact Nat.mul_le_mul_right _ hU4
    have hle : Fintype.card H ≤ S.card + 1 := by omega
    have hanot : a ∉ S := by simp [S]
    obtain ⟨w, hw, hw0, hwS⟩ := exists_inj_fixing h0 a S hanot hle
    refine ⟨w, hw, hw0, fun t => ?_⟩
    by_cases ht : t = h0
    · subst ht; rw [hw0]; exact hab
    · exact (Finset.mem_erase.mp (hwS t ht)).1
  let delta : I → I → ZMod 2 := fun a b =>
    if h : a = b then 0
    else
      let w := Classical.choose (hex_witness a b h)
      f w + f (Function.update w h0 b)
  have hdelta_eval : ∀ (v : H → I) (t : H) (b : I),
      Function.Injective v → (∀ s, v s ≠ b) →
      f (Function.update v t b) = f v + delta (v t) b := by
    intro v t b hv hb
    have hne : v t ≠ b := hb t
    have hspec := Classical.choose_spec (hex_witness (v t) b hne)
    have h1 : delta (v t) b = f (Classical.choose (hex_witness (v t) b hne)) +
        f (Function.update (Classical.choose (hex_witness (v t) b hne)) h0 b) := by
      simp [delta, hne]
    have heq := hswap_indep v (Classical.choose (hex_witness (v t) b hne)) t h0 b
      hv hspec.1 hspec.2.1.symm hb hspec.2.2
    rw [← h1] at heq
    exact (zmod2_add_eq_iff.mp (by rw [add_comm]; exact heq)).trans (add_comm _ _)
  have hdelta_self : ∀ a : I, delta a a = 0 := fun a => by simp [delta]
  have hdelta_symm : ∀ a b : I, delta a b = delta b a := by
    intro a b
    by_cases hab : a = b
    · subst hab; rfl
    · obtain ⟨w, hw, hw0, hwb⟩ := hex_witness a b hab
      have hw' : Function.Injective (Function.update w h0 b) := hupd_inj w h0 b hw hwb
      have hwa : ∀ s, Function.update w h0 b s ≠ a := by
        intro s
        by_cases hs : s = h0
        · subst hs; simp [Ne.symm hab]
        · rw [Function.update_of_ne hs]; exact fun heq => hs (hw (heq.trans hw0.symm))
      have h1 := hdelta_eval w h0 b hw hwb
      rw [hw0] at h1
      have h2 := hdelta_eval (Function.update w h0 b) h0 a hw' hwa
      have hback : Function.update (Function.update w h0 b) h0 a = w := by
        funext s
        by_cases hs : s = h0
        · subst hs; simp [hw0]
        · simp [hs]
      rw [Function.update_self, hback] at h2
      rw [h1, add_assoc] at h2
      have h3 : delta a b + delta b a = 0 := by
        have h4 : f w + (delta a b + delta b a) = f w + 0 := by rw [add_zero]; exact h2.symm
        exact add_left_cancel h4
      exact (zmod2_add_eq_iff.mp h3).trans (by simp)
  have hdelta_cocycle : ∀ a b d : I, delta a b + delta b d = delta a d := by
    intro a b d
    by_cases hab : a = b
    · subst hab; simp [hdelta_self]
    · by_cases hbd : b = d
      · subst hbd; simp [hdelta_self]
      · by_cases had : a = d
        · subst had; rw [hdelta_symm b a, zmod2_add_self, hdelta_self]
        · let S : Finset I := ((Finset.univ.erase a).erase b).erase d
          have hb_in : b ∈ Finset.univ.erase a :=
            Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
          have hd_in : d ∈ (Finset.univ.erase a).erase b :=
            Finset.mem_erase.mpr ⟨Ne.symm hbd, Finset.mem_erase.mpr ⟨Ne.symm had, Finset.mem_univ d⟩⟩
          have hScard : S.card = Fintype.card I - 3 := by
            rw [Finset.card_erase_of_mem hd_in, Finset.card_erase_of_mem hb_in,
                Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
            omega
          have h1 : 4 * Fintype.card H ≤ Fintype.card I := by
            rw [hIcard]; exact Nat.mul_le_mul_right _ hU4
          have hle : Fintype.card H ≤ S.card + 1 := by omega
          have hanot : a ∉ S := by simp [S]
          obtain ⟨w, hw, hw0, hwS⟩ := exists_inj_fixing h0 a S hanot hle
          have hwb : ∀ s, w s ≠ b := fun s => by
            by_cases hs : s = h0
            · subst hs; rw [hw0]; exact hab
            · exact (Finset.mem_erase.mp (Finset.mem_erase.mp (hwS s hs)).2).1
          have hwd : ∀ s, w s ≠ d := fun s => by
            by_cases hs : s = h0
            · subst hs; rw [hw0]; exact had
            · exact (Finset.mem_erase.mp (hwS s hs)).1
          let w1 := Function.update w h0 b
          have hw1 : Function.Injective w1 := hupd_inj w h0 b hw hwb
          have hw1d : ∀ s, w1 s ≠ d := fun s => by
            by_cases hs : s = h0
            · subst hs; simp [w1, hbd]
            · simp [w1, hs]; exact hwd s
          have e1 := hdelta_eval w h0 b hw hwb
          rw [hw0] at e1
          have e2 := hdelta_eval w1 h0 d hw1 hw1d
          have hupd2 : Function.update w1 h0 d = Function.update w h0 d := by
            funext s; by_cases hs : s = h0 <;> simp [w1, hs]
          rw [hupd2, show w1 h0 = b from Function.update_self h0 b w] at e2
          have e3 := hdelta_eval w h0 d hw hwd
          rw [hw0] at e3
          rw [e1, add_assoc] at e2
          have h4 := e2.symm.trans e3
          exact add_left_cancel h4
  let a0 : I := eUI (s1, h0)
  let z : I → ZMod 2 := fun x => delta a0 x
  have hdelta_z : ∀ a b : I, delta a b = z a + z b := by
    intro a b
    have h := hdelta_cocycle a0 a b
    exact (zmod2_add_eq_iff.mp (by rw [add_comm]; exact h)).trans (add_comm _ _)
  let g : (H → I) → ZMod 2 := fun v => f v + ∑ t : H, z (v t)
  have hg_step : ∀ (v : H → I) (t : H) (b : I),
      Function.Injective v → (∀ s, v s ≠ b) →
      g (Function.update v t b) = g v := by
    intro v t b hv hb
    dsimp only [g]
    rw [hdelta_eval v t b hv hb, hdelta_z (v t) b]
    have hsum_upd : (∑ s : H, z (Function.update v t b s)) =
        (∑ s : H, z (v s)) + z (v t) + z b := by
      rw [← Finset.add_sum_erase Finset.univ (fun s => z (Function.update v t b s)) (Finset.mem_univ t)]
      rw [← Finset.add_sum_erase Finset.univ (fun s => z (v s)) (Finset.mem_univ t)]
      rw [Function.update_self]
      have hrest : (∑ s ∈ Finset.univ.erase t, z (Function.update v t b s)) =
          ∑ s ∈ Finset.univ.erase t, z (v s) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
      rw [hrest]
      calc z b + ∑ s ∈ Finset.univ.erase t, z (v s)
          = (z (v t) + z (v t)) + (z b + ∑ s ∈ Finset.univ.erase t, z (v s)) := by
              rw [zmod2_add_self, zero_add]
        _ = z (v t) + (∑ s ∈ Finset.univ.erase t, z (v s)) + z (v t) + z b := by ring
    rw [hsum_upd]
    calc f v + (z (v t) + z b) + ((∑ s : H, z (v s)) + z (v t) + z b)
        = (f v + ∑ s : H, z (v s)) + (z (v t) + z (v t)) + (z b + z b) := by ring
      _ = (f v + ∑ s : H, z (v s)) + 0 + 0 := by rw [zmod2_add_self, zmod2_add_self]
      _ = f v + ∑ s : H, z (v s) := by ring
  have hg_disj : ∀ v w : H → I,
      Function.Injective v → Function.Injective w → (∀ t1 t2, v t1 ≠ w t2) →
      g v = g w := by
    intro v w hv hw hdisj
    let mix : Finset H → (H → I) := fun S t => if t ∈ S then w t else v t
    have hmix_inj : ∀ S : Finset H, Function.Injective (mix S) := by
      intro S t1 t2 heq
      by_cases h1 : t1 ∈ S <;> by_cases h2 : t2 ∈ S
      · simp [mix, h1, h2] at heq; exact hw heq
      · simp [mix, h1, h2] at heq; exact (hdisj t2 t1 heq.symm).elim
      · simp [mix, h1, h2] at heq; exact (hdisj t1 t2 heq).elim
      · simp [mix, h1, h2] at heq; exact hv heq
    have hind : ∀ S : Finset H, g (mix S) = g v := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        have : mix ∅ = v := by funext t; simp [mix]
        rw [this]
      | @insert t S ht ih =>
        have hupd : mix (insert t S) = Function.update (mix S) t (w t) := by
          funext s
          by_cases hs : s = t
          · subst hs; simp [mix]
          · simp [mix, hs]
        have hnot : ∀ s, mix S s ≠ w t := by
          intro s
          by_cases hs : s ∈ S
          · simp [mix, hs]; exact fun heq => ht (hw heq ▸ hs)
          · simp [mix, hs]; exact hdisj s t
        rw [hupd, hg_step (mix S) t (w t) (hmix_inj S) hnot, ih]
    have huniv : mix Finset.univ = w := by funext t; simp [mix]
    rw [← huniv, hind Finset.univ]
  let v0 : H → I := fun t => eUI (s1, t)
  have hv0 : Function.Injective v0 := fun t1 t2 heq =>
    congrArg Prod.snd (eUI.injective heq)
  refine ⟨g v0, z, ?_⟩
  intro v hv
  have hg_eq : g v = g v0 := by
    let used : Finset I := Finset.univ.image v ∪ Finset.univ.image v0
    have hused : used.card ≤ 2 * Fintype.card H := by
      calc used.card ≤ (Finset.univ.image v).card + (Finset.univ.image v0).card :=
            Finset.card_union_le _ _
        _ ≤ Fintype.card H + Fintype.card H := by
            rw [Finset.card_image_of_injective _ hv, Finset.card_image_of_injective _ hv0,
                Finset.card_univ]
        _ = 2 * Fintype.card H := by omega
    let Sfree : Finset I := Finset.univ \ used
    have hSfree : Fintype.card H ≤ Sfree.card := by
      have hsc : Sfree.card = Fintype.card I - used.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      have h1 : 4 * Fintype.card H ≤ Fintype.card I := by
        rw [hIcard]; exact Nat.mul_le_mul_right _ hU4
      omega
    obtain ⟨u, hu, huS⟩ := exists_inj_into (α := H) Sfree hSfree
    have hdisj1 : ∀ t1 t2, v t1 ≠ u t2 := fun t1 t2 heq => by
      have hnot := (Finset.mem_sdiff.mp (huS t2)).2
      apply hnot
      rw [← heq]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem v (Finset.mem_univ t1))
    have hdisj2 : ∀ t1 t2, v0 t1 ≠ u t2 := fun t1 t2 heq => by
      have hnot := (Finset.mem_sdiff.mp (huS t2)).2
      apply hnot
      rw [← heq]
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem v0 (Finset.mem_univ t1))
    exact (hg_disj v u hv hu hdisj1).trans (hg_disj v0 u hv0 hu hdisj2).symm
  exact zmod2_add_eq_iff.mp hg_eq

end PEqualNP.Outside.L_lib_711_aux

open PEqualNP.Outside.L_lib_711_aux in
theorem PEqualNP.Outside.L_lib_711 : (∀ (m h : Nat), 2 ≤ m →
  let K := ZMod 2
  let U := Fin m → K
  let H := Fin h → K
  let I := U × H
  let J := I × (Fin m ⊕ Fin h)
  let bit := fun (p : Equiv.Perm I) (j : J) =>
    Sum.elim (p j.1).1 (p j.1).2 j.2
  ∀ f : (H → I) → K,
    (∃ T : Finset (Finset J), (∀ mon ∈ T, mon.card ≤ m) ∧
      ∀ p : Equiv.Perm I, (∑ mon ∈ T, ∏ j ∈ mon, bit p j) =
        f (fun t => p.symm (0,t))) ↔
    (∃ (c : K) (z : I → K), ∀ v : H → I, Function.Injective v →
      f v = c + ∑ t : H, z (v t))) := by
  classical
  intro m h hm K U H I J bit f
  constructor
  · rintro ⟨T, hTdeg, hTval⟩
    have hCmon : ∀ mon ∈ T, ∃ C : K, ∀ p : Equiv.Perm I,
        (∑ s : U, ∏ j ∈ mon, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2) = C :=
      fun mon hmon => sum_shift_monomial_const m h mon (hTdeg mon hmon)
    choose Cmon hCmon using hCmon
    let C0 : K := ∑ mon ∈ T.attach, Cmon mon.1 mon.2
    have hEq : ∀ p : Equiv.Perm I, (∑ s : U, f (fun t => p.symm (s, t))) = C0 := by
      intro p
      have hshift : ∀ s : U,
          f (fun t => p.symm (s, t)) =
            ∑ mon ∈ T, ∏ j ∈ mon, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2 := by
        intro s
        let tau : Equiv.Perm I :=
          { toFun := fun x => (x.1 + s, x.2)
            invFun := fun x => (x.1 + s, x.2)
            left_inv := fun ⟨u, t⟩ => Prod.ext (by funext k; change u k + s k + s k = u k; rw [add_assoc, zmod2_add_self, add_zero]) rfl
            right_inv := fun ⟨u, t⟩ => Prod.ext (by funext k; change u k + s k + s k = u k; rw [add_assoc, zmod2_add_self, add_zero]) rfl }
        let ps : Equiv.Perm I := p.trans tau
        have hps_symm : ∀ t : H, ps.symm (0, t) = p.symm (s, t) := by
          intro t
          change p.symm (tau.symm (0, t)) = p.symm (s, t)
          simp [tau]
        have hval := hTval ps
        have hfun : (fun t => ps.symm (0, t)) = fun t => p.symm (s, t) := funext hps_symm
        rw [hfun] at hval
        rw [← hval]
        apply Finset.sum_congr rfl
        intro mon _
        apply Finset.prod_congr rfl
        intro j _
        rfl
      calc
        (∑ s : U, f (fun t => p.symm (s, t)))
            = ∑ s : U, ∑ mon ∈ T, ∏ j ∈ mon, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2 := by
                apply Finset.sum_congr rfl; intro s _; exact hshift s
        _ = ∑ mon ∈ T, ∑ s : U, ∏ j ∈ mon, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2 :=
                Finset.sum_comm
        _ = ∑ mon ∈ T.attach, ∑ s : U, ∏ j ∈ mon.1, Sum.elim ((p j.1).1 + s) (p j.1).2 j.2 :=
                (Finset.sum_attach T _).symm
        _ = C0 := by
                apply Finset.sum_congr rfl
                intro mon _
                exact hCmon mon.1 mon.2 p
    have hU4 : 4 ≤ Fintype.card U := by
      have hc : Fintype.card U = 2 ^ m := by
        simp [U, K, ZMod.card]
      rw [hc]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
    exact additive_of_equipartition (Equiv.refl I) hU4 (0 : H) f C0 hEq
  · rintro ⟨c, z, hfz⟩
    let α := Option (I × Finset (Fin m))
    let g : α → K := fun a => Option.casesOn a c (fun p => z p.1)
    let M : α → Finset J := fun a =>
      Option.casesOn a ∅ (fun p => p.2.image (fun k => (p.1, Sum.inl k)))
    have hcard : ∀ a ∈ (Finset.univ : Finset α), (M a).card ≤ m := by
      intro a _
      cases a with
      | none => simp [M]
      | some p =>
        calc (M (some p)).card ≤ p.2.card := Finset.card_image_le
          _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_card (Finset.subset_univ _)
          _ = m := Finset.card_fin m
    obtain ⟨T, hTdeg, hTsum⟩ := exists_finset_of_weighted_sum m (Finset.univ : Finset α) g M hcard
    refine ⟨T, hTdeg, ?_⟩
    intro p
    rw [hTsum (bit p)]
    have hinj : Function.Injective (fun t : H => p.symm (0, t)) := by
      intro t1 t2 heq
      exact congrArg Prod.snd (p.symm.injective heq)
    rw [hfz _ hinj]
    have hopt : (∑ a : α, g a * ∏ j ∈ M a, bit p j) =
        c + ∑ x : I, z x * ∑ S : Finset (Fin m), ∏ j ∈ S.image (fun k => (x, Sum.inl k)), bit p j := by
      rw [Fintype.sum_option]
      simp only [g, M, Finset.prod_empty, mul_one]
      congr 1
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
    rw [hopt]
    congr 1
    have hterm : ∀ x : I,
        (∑ S : Finset (Fin m), ∏ j ∈ S.image (fun k => (x, Sum.inl k)), bit p j) =
          if (p x).1 = 0 then 1 else 0 := by
      intro x
      rw [← indicator_zero_vec (p x).1]
      have h1 : (∏ k : Fin m, (1 + (p x).1 k)) =
          ∑ S ∈ (Finset.univ : Finset (Fin m)).powerset, ∏ k ∈ S, (p x).1 k := by
        simpa using prod_add_finset (Finset.univ : Finset (Fin m)) (fun _ => 1) (fun k => (p x).1 k)
      rw [h1]
      have hpow : (Finset.univ : Finset (Fin m)).powerset = Finset.univ := by
        ext S; simp
      rw [hpow]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_image]
      · apply Finset.prod_congr rfl; intro k _; rfl
      · intro k1 _ k2 _ heq
        exact Sum.inl.inj (congrArg Prod.snd heq)
    calc
      (∑ x : I, z x * ∑ S : Finset (Fin m), ∏ j ∈ S.image (fun k => (x, Sum.inl k)), bit p j)
          = ∑ x : I, z x * (if (p x).1 = 0 then 1 else 0) := by
              apply Finset.sum_congr rfl; intro x _; rw [hterm x]
      _ = ∑ x : I, if (p x).1 = 0 then z x else 0 := by
              apply Finset.sum_congr rfl; intro x _; split_ifs <;> simp
      _ = ∑ x ∈ Finset.univ.filter (fun x : I => (p x).1 = 0), z x := by
              rw [Finset.sum_filter]
      _ = ∑ t : H, z (p.symm (0, t)) := by
              symm
              refine Finset.sum_nbij (fun t : H => p.symm (0, t)) ?_ ?_ ?_ ?_
              · intro t _
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                rw [p.apply_symm_apply]
              · intro t1 _ t2 _ heq
                exact congrArg Prod.snd (p.symm.injective heq)
              · intro x hx
                have hx0 : (p x).1 = 0 := (Finset.mem_filter.mp hx).2
                refine ⟨(p x).2, Finset.mem_univ _, ?_⟩
                have hpx : (0, (p x).2) = p x := Prod.ext hx0.symm rfl
                dsimp only
                rw [hpx, p.symm_apply_apply]
              · intro _ _; rfl
