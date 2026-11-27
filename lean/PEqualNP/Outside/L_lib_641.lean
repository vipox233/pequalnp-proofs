import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_641_aux

private theorem sum_sq_le_sq_sum {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ) :
    ∑ x ∈ s, f x * f x ≤ (∑ x ∈ s, f x) * (∑ x ∈ s, f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 : (f a + ∑ x ∈ s, f x) * (f a + ∑ x ∈ s, f x) =
        f a * f a + 2 * f a * (∑ x ∈ s, f x) + (∑ x ∈ s, f x) * (∑ x ∈ s, f x) := by ring
    omega

private theorem main_aux (n m : ℕ) (left right : Fin m → Fin n) (fixed : Finset (Fin m)) :
    let words := Finset.univ.filter (fun x : Fin n → Bool => ∀ e ∈ fixed, x (left e) = x (right e))
    let cut := fun y : Fin n → Bool => Finset.univ.filter (fun i => y (left i) ≠ y (right i))
    let profile := fun j : Fin m => words.filter (fun word => word (left j) ≠ word (right j))
    let live := (Finset.univ.image profile).erase ∅
    ∀ r : ℕ, (words.image cut).card ≤ 2 ^ r → 2 * live.card ≤ r * (r + 1) := by
  classical
  intro words cut profile live r hcut
  let relFix : Fin n → Fin n → Prop := fun u v =>
    ∃ e ∈ fixed, (left e = u ∧ right e = v) ∨ (left e = v ∧ right e = u)
  let relAll : Fin n → Fin n → Prop := fun u v =>
    ∃ e : Fin m, (left e = u ∧ right e = v) ∨ (left e = v ∧ right e = u)
  let sFix : Setoid (Fin n) := ⟨Relation.EqvGen relFix, Relation.EqvGen.is_equivalence relFix⟩
  let sAll : Setoid (Fin n) := ⟨Relation.EqvGen relAll, Relation.EqvGen.is_equivalence relAll⟩
  let QFix := Quotient sFix
  let QAll := Quotient sAll
  have hFix_le_All : ∀ u v, sFix.r u v → sAll.r u v := by
    intro u v h
    induction h with
    | rel x y hxy =>
      obtain ⟨e, _, he⟩ := hxy
      exact Relation.EqvGen.rel x y ⟨e, he⟩
    | refl x => exact Relation.EqvGen.refl x
    | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  let proj : QFix → QAll := Quotient.lift (fun u => Quotient.mk sAll u) (fun u v huv =>
    Quotient.sound (hFix_le_All u v huv))
  have hproj_surj : Function.Surjective proj := by
    intro q
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    exact ⟨Quotient.mk sFix u, rfl⟩
  let c1 := Fintype.card QFix
  let c2 := Fintype.card QAll
  have hwords_card : words.card = 2 ^ c1 := by
    let eW : {x // x ∈ words} ≃ (QFix → Bool) :=
      { toFun := fun ⟨x, hx⟩ =>
          Quotient.lift x (fun u v huv => by
            have hxf := (Finset.mem_filter.mp hx).2
            induction huv with
            | rel a b hab =>
              obtain ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hab
              · exact hxf e he
              · exact (hxf e he).symm
            | refl _ => rfl
            | symm _ _ _ ih => exact ih.symm
            | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)
        invFun := fun f =>
          ⟨fun u => f (Quotient.mk sFix u), Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => by
            apply congrArg f
            exact Quotient.sound (show sFix.r (left e) (right e) from
              Relation.EqvGen.rel (left e) (right e) ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)⟩⟩
        left_inv := fun ⟨x, _⟩ => Subtype.ext (funext fun _ => rfl)
        right_inv := fun f => funext fun q => by
          obtain ⟨u, rfl⟩ := Quotient.exists_rep q
          rfl }
    calc words.card = Fintype.card {x // x ∈ words} := (Fintype.card_coe words).symm
      _ = Fintype.card (QFix → Bool) := Fintype.card_congr eW
      _ = 2 ^ c1 := by simp [c1]
  have hfiber : ∀ C ∈ words.image cut, (words.filter (fun y => cut y = C)).card = 2 ^ c2 := by
    intro C hC
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hC
    let F := words.filter (fun y => cut y = cut x0)
    let eF : (QAll → Bool) ≃ {y // y ∈ F} :=
      { toFun := fun f =>
          ⟨fun u => x0 u ^^ f (Quotient.mk sAll u), Finset.mem_filter.mpr ⟨
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun e he => by
              have hxe := (Finset.mem_filter.mp hx0).2 e he
              have hq : Quotient.mk sAll (left e) = Quotient.mk sAll (right e) :=
                Quotient.sound (Relation.EqvGen.rel _ _ ⟨e, Or.inl ⟨rfl, rfl⟩⟩)
              dsimp only; rw [hxe, hq]⟩,
            by
              ext i
              simp only [cut, Finset.mem_filter, Finset.mem_univ, true_and]
              have hq : Quotient.mk sAll (left i) = Quotient.mk sAll (right i) :=
                Quotient.sound (Relation.EqvGen.rel _ _ ⟨i, Or.inl ⟨rfl, rfl⟩⟩)
              rw [hq]
              generalize x0 (left i) = a; generalize x0 (right i) = b; generalize f (Quotient.mk sAll (right i)) = c
              cases a <;> cases b <;> cases c <;> decide⟩⟩
        invFun := fun ⟨y, hy⟩ =>
          Quotient.lift (fun u => x0 u ^^ y u) (fun u v huv => by
            have hcy := (Finset.mem_filter.mp hy).2
            induction huv with
            | rel a b hab =>
              obtain ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hab
              · have hiff : (y (left e) ≠ y (right e)) ↔ (x0 (left e) ≠ x0 (right e)) := by
                  have := congrArg (e ∈ ·) hcy
                  simpa [cut] using this
                generalize y (left e) = a1 at hiff ⊢; generalize y (right e) = a2 at hiff ⊢
                generalize x0 (left e) = b1 at hiff ⊢; generalize x0 (right e) = b2 at hiff ⊢
                cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp_all
              · have hiff : (y (left e) ≠ y (right e)) ↔ (x0 (left e) ≠ x0 (right e)) := by
                  have := congrArg (e ∈ ·) hcy
                  simpa [cut] using this
                generalize y (left e) = a1 at hiff ⊢; generalize y (right e) = a2 at hiff ⊢
                generalize x0 (left e) = b1 at hiff ⊢; generalize x0 (right e) = b2 at hiff ⊢
                cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> simp_all
            | refl _ => rfl
            | symm _ _ _ ih => exact ih.symm
            | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)
        left_inv := fun f => funext fun q => by
          obtain ⟨u, rfl⟩ := Quotient.exists_rep q
          simp only [Quotient.lift_mk]
          generalize x0 u = a; generalize f (Quotient.mk sAll u) = b
          cases a <;> cases b <;> rfl
        right_inv := fun ⟨y, _⟩ => Subtype.ext (funext fun u => by
          simp only [Quotient.lift_mk]
          generalize x0 u = a; generalize y u = b
          cases a <;> cases b <;> rfl) }
    calc F.card = Fintype.card {y // y ∈ F} := (Fintype.card_coe F).symm
      _ = Fintype.card (QAll → Bool) := (Fintype.card_congr eF).symm
      _ = 2 ^ c2 := by simp [c2]
  have hpow_le : 2 ^ c1 ≤ 2 ^ (r + c2) := by
    have hsum := Finset.card_eq_sum_card_fiberwise (f := cut) (s := words) (t := words.image cut)
      (fun x hx => Finset.mem_image_of_mem cut hx)
    rw [hwords_card, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul] at hsum
    rw [hsum, pow_add]
    exact Nat.mul_le_mul_right (2 ^ c2) hcut
  have hc1_le : c1 ≤ r + c2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  let OrdPairs : Finset (QFix × QFix) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ proj p.1 = proj p.2)
  have hlive_bound : 2 * live.card ≤ OrdPairs.card := by
    have hmem_ex : ∀ S ∈ live, ∃ j : Fin m, profile j = S ∧ S ≠ ∅ := by
      intro S hS
      obtain ⟨hne, himg⟩ := Finset.mem_erase.mp hS
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp himg
      exact ⟨j, rfl, hne⟩
    let jOf : {S // S ∈ live} → Fin m := fun S => Classical.choose (hmem_ex S.1 S.2)
    have hjOf_eq : ∀ S : {S // S ∈ live}, profile (jOf S) = S.1 :=
      fun S => (Classical.choose_spec (hmem_ex S.1 S.2)).1
    have hjOf_ne : ∀ S : {S // S ∈ live}, S.1 ≠ ∅ :=
      fun S => (Classical.choose_spec (hmem_ex S.1 S.2)).2
    let pairOf : {S // S ∈ live} → Finset (QFix × QFix) := fun S =>
      {(Quotient.mk sFix (left (jOf S)), Quotient.mk sFix (right (jOf S))),
       (Quotient.mk sFix (right (jOf S)), Quotient.mk sFix (left (jOf S)))}
    have hpair_ne : ∀ S : {S // S ∈ live},
        Quotient.mk sFix (left (jOf S)) ≠ Quotient.mk sFix (right (jOf S)) := by
      intro S heq
      have hne := hjOf_ne S
      rw [← hjOf_eq S] at hne
      obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      obtain ⟨hw_w, hw_ne⟩ := Finset.mem_filter.mp hw
      have hxf := (Finset.mem_filter.mp hw_w).2
      have hw_resp : ∀ a b, sFix.r a b → w a = w b := by
        intro a b hr
        induction hr with
        | rel x y hxy =>
          obtain ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hxy
          · exact hxf e he
          · exact (hxf e he).symm
        | refl _ => rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
      exact hw_ne (hw_resp _ _ (Quotient.exact heq))
    have hpair_card : ∀ S : {S // S ∈ live}, (pairOf S).card = 2 := by
      intro S
      apply Finset.card_pair
      intro heq
      exact hpair_ne S (Prod.mk.inj heq).1
    have hpair_sub : ∀ S : {S // S ∈ live}, pairOf S ⊆ OrdPairs := by
      intro S p hp
      have hproj_eq : proj (Quotient.mk sFix (left (jOf S))) = proj (Quotient.mk sFix (right (jOf S))) :=
        Quotient.sound (Relation.EqvGen.rel _ _ ⟨jOf S, Or.inl ⟨rfl, rfl⟩⟩)
      simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair_ne S, hproj_eq⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpair_ne S).symm, hproj_eq.symm⟩
    have hpair_disj : Set.PairwiseDisjoint (Set.univ : Set {S // S ∈ live}) pairOf := by
      intro S1 _ S2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      have hprof_eq : ∀ u1 v1 u2 v2 : Fin n,
          (Quotient.mk sFix u1 = Quotient.mk sFix u2 ∧ Quotient.mk sFix v1 = Quotient.mk sFix v2) ∨
          (Quotient.mk sFix u1 = Quotient.mk sFix v2 ∧ Quotient.mk sFix v1 = Quotient.mk sFix u2) →
          words.filter (fun w => w u1 ≠ w v1) = words.filter (fun w => w u2 ≠ w v2) := by
        intro u1 v1 u2 v2 hq
        have hw_resp : ∀ w ∈ words, ∀ a b, Quotient.mk sFix a = Quotient.mk sFix b → w a = w b := by
          intro w hw a b hab
          have hxf := (Finset.mem_filter.mp hw).2
          have hr := Quotient.exact hab
          clear hab
          induction hr with
          | rel x y hxy =>
            obtain ⟨e, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hxy
            · exact hxf e he
            · exact (hxf e he).symm
          | refl _ => rfl
          | symm _ _ _ ih => exact ih.symm
          | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
        ext w
        simp only [Finset.mem_filter]
        constructor <;> rintro ⟨hw, hne'⟩ <;> refine ⟨hw, ?_⟩
        · rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [← hw_resp w hw _ _ h1, ← hw_resp w hw _ _ h2]; exact hne'
          · rw [← hw_resp w hw _ _ h2, ← hw_resp w hw _ _ h1]; exact Ne.symm hne'
        · rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [hw_resp w hw _ _ h1, hw_resp w hw _ _ h2]; exact hne'
          · rw [hw_resp w hw _ _ h1, hw_resp w hw _ _ h2]; exact Ne.symm hne'
      simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
      have hq :
          (Quotient.mk sFix (left (jOf S1)) = Quotient.mk sFix (left (jOf S2)) ∧
            Quotient.mk sFix (right (jOf S1)) = Quotient.mk sFix (right (jOf S2))) ∨
          (Quotient.mk sFix (left (jOf S1)) = Quotient.mk sFix (right (jOf S2)) ∧
            Quotient.mk sFix (right (jOf S1)) = Quotient.mk sFix (left (jOf S2))) := by
        rcases hp1 with rfl | rfl <;> rcases hp2 with h2 | h2
        · left; exact Prod.mk.inj h2
        · right; exact Prod.mk.inj h2
        · right; exact ⟨(Prod.mk.inj h2).2, (Prod.mk.inj h2).1⟩
        · left; exact ⟨(Prod.mk.inj h2).2, (Prod.mk.inj h2).1⟩
      have hpeq := hprof_eq _ _ _ _ hq
      have hS12 : S1.1 = S2.1 := by rw [← hjOf_eq S1, ← hjOf_eq S2]; exact hpeq
      exact hne (Subtype.ext hS12)
    calc 2 * live.card = Fintype.card {S // S ∈ live} * 2 := by rw [Fintype.card_coe, mul_comm]
      _ = ∑ S : {S // S ∈ live}, (pairOf S).card := by simp [hpair_card]
      _ = ((Finset.univ : Finset {S // S ∈ live}).biUnion pairOf).card :=
          (Finset.card_biUnion (fun a _ b _ h => hpair_disj (Set.mem_univ a) (Set.mem_univ b) h)).symm
      _ ≤ OrdPairs.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun S _ => hpair_sub S)
  let fib (q : QAll) : Finset QFix := Finset.univ.filter (fun a => proj a = q)
  have hfib_pos : ∀ q : QAll, 1 ≤ (fib q).card := by
    intro q
    obtain ⟨a, ha⟩ := hproj_surj q
    exact Finset.one_le_card.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩
  have hfib_sum : ∑ q : QAll, (fib q).card = c1 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := proj) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)
    simpa [fib, c1] using h.symm
  have hOrd_card : OrdPairs.card = ∑ q : QAll, (fib q).card * ((fib q).card - 1) := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun p : QFix × QFix => proj p.1)
      (s := OrdPairs) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [h]
    refine Finset.sum_congr rfl fun q _ => ?_
    have heq : OrdPairs.filter (fun p => proj p.1 = q) = (fib q).offDiag := by
      ext ⟨a, b⟩
      simp only [OrdPairs, fib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_offDiag]
      constructor
      · rintro ⟨⟨hne, hp⟩, hq⟩
        exact ⟨hq, hp.symm.trans hq, hne⟩
      · rintro ⟨ha, hb, hne⟩
        exact ⟨⟨hne, ha.trans hb.symm⟩, ha⟩
    rw [heq, Finset.offDiag_card]
    have hpos := hfib_pos q
    have : (fib q).card * (fib q).card - (fib q).card = (fib q).card * ((fib q).card - 1) := by
      rw [Nat.mul_sub_left_distrib, mul_one]
    exact this
  let t (q : QAll) : ℕ := (fib q).card - 1
  have ht_sum : ∑ q : QAll, t q = c1 - c2 := by
    have h1 : ∑ q : QAll, (t q + 1) = c1 := by
      rw [← hfib_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have := hfib_pos q
      dsimp only [t]; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
    change (∑ q : QAll, t q) + c2 = c1 at h1
    omega
  have hOrd_t : OrdPairs.card = (∑ q : QAll, t q * t q) + (∑ q : QAll, t q) := by
    rw [hOrd_card, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have hpos := hfib_pos q
    have : (fib q).card = t q + 1 := by dsimp only [t]; omega
    rw [this, Nat.add_sub_cancel]; ring
  have hsq := sum_sq_le_sq_sum (Finset.univ : Finset QAll) t
  have hle_r : ∑ q : QAll, t q ≤ r := by omega
  have hprod : (∑ q : QAll, t q) * (∑ q : QAll, t q) ≤ r * r := Nat.mul_le_mul hle_r hle_r
  have hr_eq : r * (r + 1) = r * r + r := by ring
  omega

end PEqualNP.Outside.L_lib_641_aux

theorem PEqualNP.Outside.L_lib_641 : (∀ (n m : ℕ) (left right : Fin m → Fin n) (fixed : Finset (Fin m)),
  let words := Finset.univ.filter (fun x : Fin n → Bool => ∀ e ∈ fixed, x (left e) = x (right e))
  let cut := fun y : Fin n → Bool => Finset.univ.filter (fun i => y (left i) ≠ y (right i))
  let profile := fun j : Fin m => words.filter (fun word => word (left j) ≠ word (right j))
  let live := (Finset.univ.image profile).erase ∅
  ∀ r : ℕ, (words.image cut).card ≤ 2^r → 2*live.card ≤ r*(r+1)) :=
  PEqualNP.Outside.L_lib_641_aux.main_aux
