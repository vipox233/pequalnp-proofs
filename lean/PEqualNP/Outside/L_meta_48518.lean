import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_48518_aux

theorem lo_alpha {V : Type*} [DecidableEq V] (edge : V → V → Bool) (U : Finset V) (a b : V) (n : ℕ)
    (hab : edge a b = true)
    (hU : ∀ z ⊆ U, (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n) :
    ∀ z ⊆ insert a (insert b U), (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n + 1 := by
  intro z hz hi
  by_cases ha : a ∈ z
  · have hb : b ∉ z := fun hb => by simp [hi a ha b hb] at hab
    have h1 : z.erase a ⊆ U := by
      intro k hk
      rw [Finset.mem_erase] at hk
      have := hz hk.2
      simp only [Finset.mem_insert] at this
      rcases this with h | h | h
      · exact absurd h hk.1
      · exact absurd (h ▸ hk.2) hb
      · exact h
    have := hU _ h1 (fun j hj k hk => hi j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk))
    have := Finset.pred_card_le_card_erase (s := z) (a := a)
    omega
  · have h1 : z.erase b ⊆ U := by
      intro k hk
      rw [Finset.mem_erase] at hk
      have := hz hk.2
      simp only [Finset.mem_insert] at this
      rcases this with h | h | h
      · exact absurd (h ▸ hk.2) ha
      · exact absurd h hk.1
      · exact h
    have := hU _ h1 (fun j hj k hk => hi j (Finset.mem_of_mem_erase hj) k (Finset.mem_of_mem_erase hk))
    have := Finset.pred_card_le_card_erase (s := z) (a := b)
    omega

theorem lo_step {V : Type*} [DecidableEq V] (edge : V → V → Bool) (x : Finset V)
    (f : Finset V → V → Bool)
    (h1 : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true)
    (h2 : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (h3 : ∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true)
    (U : Finset V) (p : Fin 3 → V) (l : ℕ) (hU : U ⊆ x) (hx : ∀ t, p t ∈ x)
    (hn : ∀ t, p t ∉ U) (he : ∀ t, ∀ i ∈ U, edge i (p t) = false)
    (h20 : edge (p 2) (p 0) = false) (hne : p 2 ≠ p 0)
    (hp : Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false) l U) :
    ∃ s t : Fin 3, ((s = 1 ∧ t = 2) ∨ (s = 0 ∧ t = 1)) ∧
      Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false) (l + 2)
        (insert (p s) (insert (p t) U)) := by
  have hsub : ∀ s t : Fin 3, insert (p s) (insert (p t) U) ⊆ x := by
    intro s t k hk
    simp only [Finset.mem_insert] at hk
    rcases hk with h | h | h
    · exact h ▸ hx s
    · exact h ▸ hx t
    · exact hU h
  have hsub1 : ∀ t : Fin 3, insert (p t) U ⊆ x := fun t =>
    (Finset.subset_insert _ _).trans (hsub t t)
  have hf1 : ∀ t, f U (p t) = true := fun t => h1 U hU _ (hx t) ⟨hn t, he t⟩
  by_cases hc : f (insert (p 1) (insert (p 2) U)) (p 0) = false
  · refine ⟨1, 2, Or.inl ⟨rfl, rfl⟩, insert (p 2) U, _, p 0, hx 0,
      ⟨U, insert (p 2) U, p 2, hx 2, hp, Finset.subset_insert _ _, le_rfl, hf1 2,
        h2 _ (hsub1 2) _ (Finset.mem_insert_self _ _)⟩,
      Finset.subset_insert _ _, le_rfl, ?_, hc⟩
    refine h1 _ (hsub1 2) _ (hx 0) ⟨?_, ?_⟩
    · simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hne h.symm, hn 0⟩
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with h | h
      · exact h ▸ h20
      · exact he 0 i h
  · refine ⟨0, 1, Or.inr ⟨rfl, rfl⟩, insert (p 1) U, _, p 0, hx 0,
      ⟨U, insert (p 1) U, p 1, hx 1, hp, Finset.subset_insert _ _, le_rfl, hf1 1,
        h2 _ (hsub1 1) _ (Finset.mem_insert_self _ _)⟩,
      Finset.subset_insert _ _, le_rfl, ?_, h2 _ (hsub 0 1) _ (Finset.mem_insert_self _ _)⟩
    refine h3 _ (insert (p 1) (insert (p 2) U)) ?_ (hsub 1 2) _ (hx 0) (by simpa using hc)
    exact Finset.insert_subset_insert _ (Finset.subset_insert _ _)

theorem lo_chain {V ι : Type*} [DecidableEq V] (edge : V → V → Bool) (x : Finset V)
    (f : Finset V → V → Bool)
    (h1 : ∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true)
    (h2 : ∀ y, y ⊆ x → ∀ j ∈ y, f y j = false)
    (h3 : ∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true)
    (pth : ι → Fin 3 → V)
    (hin : ∀ q, edge (pth q 0) (pth q 1) = true ∧ edge (pth q 1) (pth q 2) = true ∧
      edge (pth q 2) (pth q 0) = false ∧ pth q 2 ≠ pth q 0)
    (L : List ι) : ∀ (U : Finset V) (l n : ℕ), U ⊆ x → (∀ q ∈ L, ∀ t, pth q t ∈ x) →
      L.Pairwise (fun q r => ∀ s t, pth q s ≠ pth r t ∧ edge (pth q s) (pth r t) = false) →
      (∀ q ∈ L, ∀ t, pth q t ∉ U ∧ ∀ i ∈ U, edge i (pth q t) = false) →
      (∀ z ⊆ U, (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n) →
      Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false) l U →
      ∃ Y ⊆ x, Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false) (l + 2 * L.length) Y ∧
        ∀ z ⊆ Y, (∀ j ∈ z, ∀ k ∈ z, edge j k = false) → z.card ≤ n + L.length := by
  induction L with
  | nil => intro U l n hU _ _ _ hn hp; exact ⟨U, hU, hp, hn⟩
  | cons q L ih =>
    intro U l n hU hx hpw hfr hn hp
    rw [List.pairwise_cons] at hpw
    obtain ⟨h01, h12, h20, hne⟩ := hin q
    obtain ⟨s, t, hst, hp'⟩ := lo_step edge x f h1 h2 h3 U (pth q) l hU
      (hx q List.mem_cons_self) (fun t => (hfr q List.mem_cons_self t).1)
      (fun t => (hfr q List.mem_cons_self t).2) h20 hne hp
    have hedge : edge (pth q s) (pth q t) = true := by
      rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h12
      · exact h01
    have hsub : insert (pth q s) (insert (pth q t) U) ⊆ x := by
      intro k hk
      simp only [Finset.mem_insert] at hk
      rcases hk with h | h | h
      · exact h ▸ hx q List.mem_cons_self s
      · exact h ▸ hx q List.mem_cons_self t
      · exact hU h
    have hfr' : ∀ r ∈ L, ∀ t', pth r t' ∉ insert (pth q s) (insert (pth q t) U) ∧
        ∀ i ∈ insert (pth q s) (insert (pth q t) U), edge i (pth r t') = false := by
      intro r hr t'
      have hA := hpw.1 r hr
      have hB := hfr r (List.mem_cons_of_mem _ hr) t'
      refine ⟨?_, ?_⟩
      · simp only [Finset.mem_insert, not_or]
        exact ⟨fun h => (hA s t').1 h.symm, fun h => (hA t t').1 h.symm, hB.1⟩
      · intro i hi
        simp only [Finset.mem_insert] at hi
        rcases hi with h | h | h
        · exact h ▸ (hA s t').2
        · exact h ▸ (hA t t').2
        · exact hB.2 i h
    obtain ⟨Y, hY, hpY, hnY⟩ := ih _ (l + 2) (n + 1) hsub
      (fun r hr => hx r (List.mem_cons_of_mem _ hr)) hpw.2 hfr'
      (lo_alpha edge U _ _ n hedge hn) hp'
    refine ⟨Y, hY, ?_, ?_⟩
    · have : l + 2 * (q :: L).length = l + 2 + 2 * L.length := by
        simp only [List.length_cons]; ring
      rw [this]; exact hpY
    · intro z hz hi
      have := hnY z hz hi
      simp only [List.length_cons]; omega

theorem lo_mem_filter {α : Type*} {p : α → Prop} {inst : DecidablePred p} {s : Finset α}
    {a : α} : a ∈ @Finset.filter α p inst s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p inst s a

theorem lo_card (m d a : ℕ) (w : Fin m → Fin (d+1)) (S : Finset (Fin m)) :
    ((S ×ˢ (Finset.univ : Finset (Fin (a*d)))).filter
      (fun q => q.2.val < a * (w q.1).val)).card = a * S.sum (fun i => (w i).val) := by
  rw [Finset.card_filter, Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  dsimp only
  rw [← Finset.card_filter, Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.mul_le_mul_left _ (Nat.lt_succ_iff.mp (w i).isLt))

theorem lowerT : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m d a : Nat) (g : Fin m → Fin m → Bool),
  (∀ i, g i i = false) → (∀ i j, g i j = g j i) →
  ∀ w : Fin m → Fin (d+1),
    let V := Fin m × (Fin (a*d) × Fin 3)
    let edge := fun (j k : V) =>
      if j.1 = k.1 then decide (j.2.1 = k.2.1 ∧
        (j.2.2.val+1 = k.2.2.val ∨ k.2.2.val+1 = j.2.2.val))
      else g j.1 k.1
    let x := (Finset.univ : Finset V).filter (fun j => j.2.1.val < a * (w j.1).val)
    let score := ((Finset.univ : Finset (Fin m)).powerset.filter
      (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup
      (fun s => s.sum (fun i => (w i).val))
    let alpha := fun (y : Finset V) =>
      (y.powerset.filter (fun z => ∀ j ∈ z, ∀ k ∈ z, edge j k = false)).sup Finset.card
    let admits := fun (e : Nat) =>
      ∃ f : Finset V → V → Bool,
        (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true) ∧
        (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
        (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
        let pack := Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false)
        ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
    (∀ e, admits e → a*score ≤ e)) := by
  intro m d a g hg1 hg2 w V edge x score alpha admits e hadm
  obtain ⟨f, h1, h2, h3, hpack⟩ := hadm
  obtain ⟨S, hS, hSeq⟩ := Finset.exists_mem_eq_sup
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false))
    ⟨∅, by simp⟩ (fun s => s.sum (fun i => (w i).val))
  have hsc : score = S.sum (fun i => (w i).val) := by
    rw [← hSeq]; simp only [score, Finset.powerset_univ]; convert rfl
  have hSi : ∀ i ∈ S, ∀ j ∈ S, g i j = false := (Finset.mem_filter.1 hS).2
  obtain ⟨Y, hY, hpY, hnY⟩ := lo_chain edge x f h1 h2 h3 (fun q t => (q.1, (q.2, t)))
    (fun q => ⟨by simp [edge], by simp [edge], by simp [edge],
      fun h => by simpa using congrArg (fun v : V => v.2.2.val) h⟩)
    ((S ×ˢ (Finset.univ : Finset (Fin (a*d)))).filter
      (fun q => q.2.val < a * (w q.1).val)).toList ∅ 0 0 (Finset.empty_subset _)
    (fun q hq t => by
      rw [Finset.mem_toList, Finset.mem_filter] at hq
      exact lo_mem_filter.2 ⟨Finset.mem_univ _, hq.2⟩)
    ((Finset.nodup_toList _).pairwise_of_forall_ne (fun q hq r hr hne s t => by
      rw [Finset.mem_toList, Finset.mem_filter, Finset.mem_product] at hq hr
      by_cases h : q.1 = r.1
      · have h' : q.2 ≠ r.2 := fun h' => hne (Prod.ext h h')
        refine ⟨fun hh => h' (congrArg (fun v => v.2.1) hh), ?_⟩
        simp [edge, h, h']
      · refine ⟨fun hh => h (Prod.ext_iff.1 hh).1, ?_⟩
        simp [edge, h, hSi _ hq.1.1 _ hr.1.1]))
    (fun _ _ _ => ⟨Finset.notMem_empty _, fun _ hi => absurd hi (Finset.notMem_empty _)⟩)
    (fun z hz _ => by rw [Finset.subset_empty.1 hz]; simp) trivial
  have hb := hpack Y _ hY hpY
  have ha : alpha Y ≤ 0 + _ := Finset.sup_le (fun z hz => by
    rw [lo_mem_filter, Finset.mem_powerset] at hz
    exact hnY z hz.1 hz.2)
  rw [Finset.length_toList, lo_card] at ha hb
  rw [hsc]
  omega

theorem ub_inv (m n : Nat) (g : Fin m → Fin m → Bool) (h1 : ∀ i, g i i = false)
    (h2 : ∀ i j, g i j = g j i) (x : Finset (Fin m × (Fin n × Fin 3)))
    (f : Finset (Fin m × (Fin n × Fin 3)) → Fin m × (Fin n × Fin 3) → Bool)
    (hf : ∀ y j, f y j = true ↔ (j ∉ y ∧ ∀ k ∈ y, g j.1 k.1 = false)) (l : Nat) :
    ∀ y, Nat.rec (motive := fun _ => Finset (Fin m × (Fin n × Fin 3)) → Prop) (fun _ => True)
      (fun _ prev y => ∃ (u v : Finset (Fin m × (Fin n × Fin 3))) (j : Fin m × (Fin n × Fin 3)),
        j ∈ x ∧ prev u ∧ u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false) l y →
    ∃ (Z : Finset (Fin m × (Fin n × Fin 3))) (C : Finset (Fin m)), Z ⊆ y ∧
      (∀ i ∈ C, ∃ k ∈ y, g i k.1 = true) ∧ (∀ j ∈ Z, ∀ k ∈ Z, g j.1 k.1 = false) ∧
      l ≤ Z.card + C.card := by
  induction l with
  | zero => intro y _; exact ⟨∅, ∅, by simp, by simp, by simp, by simp⟩
  | succ l ih =>
    intro y hp
    obtain ⟨u, v, j, _, hp, huv, hvy, hfu, hfv⟩ := hp
    obtain ⟨Z, C, hZ, hC, hI, hl⟩ := ih u hp
    rw [hf] at hfu
    by_cases hjv : j ∈ v
    · refine ⟨insert j Z, C, ?_, ?_, ?_, ?_⟩
      · exact Finset.insert_subset (hvy hjv) (hZ.trans (huv.trans hvy))
      · intro i hi
        obtain ⟨k, hk, hg⟩ := hC i hi
        exact ⟨k, hvy (huv hk), hg⟩
      · intro a ha b hb
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact h1 _
        · exact hfu.2 b (hZ hb)
        · rw [h2]; exact hfu.2 a (hZ ha)
        · exact hI a ha b hb
      · rw [Finset.card_insert_of_notMem (fun h => hfu.1 (hZ h))]; omega
    · have hk : ∃ k ∈ v, g j.1 k.1 = true := by
        by_contra hc
        have : f v j = true := (hf v j).2 ⟨hjv, fun k hk => by simpa using fun h => hc ⟨k, hk, h⟩⟩
        simp [this] at hfv
      refine ⟨Z, insert j.1 C, hZ.trans (huv.trans hvy), ?_, hI, ?_⟩
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · obtain ⟨k, hk, hg⟩ := hk
          exact ⟨k, hvy hk, hg⟩
        · obtain ⟨k, hk, hg⟩ := hC i hi
          exact ⟨k, hvy (huv hk), hg⟩
      · have hn : j.1 ∉ C := by
          intro hc
          obtain ⟨k, hk, hg⟩ := hC _ hc
          rw [hfu.2 k hk] at hg
          exact Bool.false_ne_true hg
        rw [Finset.card_insert_of_notMem hn]; omega

theorem ub_cent (m n : Nat) (c : Fin m → Nat) (Z : Finset (Fin m × (Fin n × Fin 3)))
    (hZ : ∀ j ∈ Z, j.2.1.val < c j.1) :
    (Z.filter (fun j => j.2.2.val = 1)).card ≤ (Z.image Prod.fst).sum c := by
  calc _ ≤ ((Z.image Prod.fst).sigma (fun i => Finset.range (c i))).card := by
        refine Finset.card_le_card_of_injOn (fun j => (⟨j.1, j.2.1.val⟩ : (_ : Fin m) × Nat)) ?_ ?_
        · intro j hj
          rw [Finset.mem_coe, Finset.mem_filter] at hj
          simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_image, Finset.mem_range]
          exact ⟨⟨j, hj.1, rfl⟩, hZ j hj.1⟩
        · intro j hj k hk h
          rw [Finset.mem_coe, Finset.mem_filter] at hj hk
          simp only [Sigma.mk.injEq, heq_eq_eq] at h
          obtain ⟨j1, j2, j3⟩ := j
          obtain ⟨k1, k2, k3⟩ := k
          simp only at h hj hk
          obtain ⟨rfl, h⟩ := h
          have : j2 = k2 := Fin.ext h
          have : j3 = k3 := Fin.ext (by omega)
          subst_vars; rfl
    _ = _ := by simp [Finset.card_sigma]

theorem ub_Z (m n : Nat) (g : Fin m → Fin m → Bool) (c : Fin m → Nat)
    (y Z : Finset (Fin m × (Fin n × Fin 3))) (hy : ∀ j ∈ y, j.2.1.val < c j.1) (hZ : Z ⊆ y)
    (hI : ∀ j ∈ Z, ∀ k ∈ Z, g j.1 k.1 = false) (A S : Nat)
    (hA : ∀ z, z ⊆ y → (∀ j ∈ z, ∀ k ∈ z, j.2.2.val + 1 ≠ k.2.2.val) →
      (∀ j ∈ z, ∀ k ∈ z, g j.1 k.1 = false) → z.card ≤ A)
    (hS : ∀ B : Finset (Fin m), (∀ i ∈ B, ∀ j ∈ B, g i j = false) → B.sum c ≤ S) :
    Z.card ≤ A + S := by
  rw [← Finset.card_filter_add_card_filter_not (s := Z) (fun j => j.2.2.val = 1)]
  have h1 : (Z.filter (fun j => j.2.2.val = 1)).card ≤ S := by
    refine (ub_cent m n c Z (fun j hj => hy j (hZ hj))).trans (hS _ ?_)
    intro i hi i' hi'
    rw [Finset.mem_image] at hi hi'
    obtain ⟨j, hj, rfl⟩ := hi
    obtain ⟨k, hk, rfl⟩ := hi'
    exact hI j hj k hk
  have h2 : (Z.filter (fun j => ¬ j.2.2.val = 1)).card ≤ A := by
    refine hA _ ((Finset.filter_subset _ _).trans hZ) ?_ ?_
    · intro j hj k hk
      rw [Finset.mem_filter] at hj hk
      have := j.2.2.isLt
      have := k.2.2.isLt
      omega
    · intro j hj k hk
      exact hI j (Finset.mem_of_mem_filter _ hj) k (Finset.mem_of_mem_filter _ hk)
  omega

theorem ub_ar (l z c m p q : Nat) (h1 : l ≤ z + c) (h2 : c ≤ m) (h3 : z ≤ p + q) :
    l ≤ p + (q + m) := by
  omega

theorem upperT : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m d a : Nat) (g : Fin m → Fin m → Bool),
  (∀ i, g i i = false) → (∀ i j, g i j = g j i) →
  ∀ w : Fin m → Fin (d+1),
    let V := Fin m × (Fin (a*d) × Fin 3)
    let edge := fun (j k : V) =>
      if j.1 = k.1 then decide (j.2.1 = k.2.1 ∧
        (j.2.2.val+1 = k.2.2.val ∨ k.2.2.val+1 = j.2.2.val))
      else g j.1 k.1
    let x := (Finset.univ : Finset V).filter (fun j => j.2.1.val < a * (w j.1).val)
    let score := ((Finset.univ : Finset (Fin m)).powerset.filter
      (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup
      (fun s => s.sum (fun i => (w i).val))
    let alpha := fun (y : Finset V) =>
      (y.powerset.filter (fun z => ∀ j ∈ z, ∀ k ∈ z, edge j k = false)).sup Finset.card
    let admits := fun (e : Nat) =>
      ∃ f : Finset V → V → Bool,
        (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true) ∧
        (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
        (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
        let pack := Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false)
        ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
    admits (a*score+m)) := by
  intro m d a g h1 h2 w V edge x score alpha admits
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  have hf : ∀ (y : Finset V) (j : V), decide (j ∉ y ∧ ∀ k ∈ y, g j.1 k.1 = false) = true ↔
      (j ∉ y ∧ ∀ k ∈ y, g j.1 k.1 = false) := fun y j => decide_eq_true_iff
  refine ⟨fun y j => decide (j ∉ y ∧ ∀ k ∈ y, g j.1 k.1 = false), ?_, ?_, ?_, ?_⟩
  · intro y _ j _ hj
    rw [hf]
    refine ⟨hj.1, fun k hk => ?_⟩
    by_cases hb : k.1 = j.1
    · rw [hb]; exact h1 _
    · have := hj.2 k hk
      simp only [edge, hb, ite_false] at this
      rw [h2]; exact this
  · intro y _ j hj
    simp [hj]
  · intro u v huv _ j _ h
    rw [hf] at h ⊢
    exact ⟨fun hu => h.1 (huv hu), fun k hk => h.2 k (huv hk)⟩
  · intro pack y l hy hp
    obtain ⟨Z, C, hZ, _, hI, hl⟩ := ub_inv m (a*d) g h1 h2 x _ hf l y hp
    have hC : C.card ≤ m := by
      simpa using Finset.card_le_univ C
    have hZc := ub_Z m (a*d) g (fun i => a * (w i).val) y Z
      (fun j hj => by have := hy hj; rw [Finset.mem_filter] at this; exact this.2) hZ hI
      (alpha y) (a*score) ?_ ?_
    · exact ub_ar _ _ _ _ _ _ hl hC hZc
    · intro z hz hc hg
      apply Finset.le_sup (f := Finset.card)
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hz, fun j hj k hk => ?_⟩
      show (if j.1 = k.1 then _ else _) = false
      split_ifs with hb
      · exact decide_eq_false (fun h => h.2.elim (hc j hj k hk) (hc k hk j hj))
      · exact hg j hj k hk
    · intro B hB
      rw [← Finset.mul_sum]
      apply Nat.mul_le_mul_left
      refine Finset.le_sup (f := fun s : Finset (Fin m) => s.sum (fun i => (w i).val)) ?_
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, hB⟩

theorem thirdT : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m d a : Nat) (g : Fin m → Fin m → Bool),
  (∀ i, g i i = false) → (∀ i j, g i j = g j i) →
  ∀ w : Fin m → Fin (d+1),
    let V := Fin m × (Fin (a*d) × Fin 3)
    let edge := fun (j k : V) =>
      if j.1 = k.1 then decide (j.2.1 = k.2.1 ∧
        (j.2.2.val+1 = k.2.2.val ∨ k.2.2.val+1 = j.2.2.val))
      else g j.1 k.1
    let x := (Finset.univ : Finset V).filter (fun j => j.2.1.val < a * (w j.1).val)
    let score := ((Finset.univ : Finset (Fin m)).powerset.filter
      (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup
      (fun s => s.sum (fun i => (w i).val))
    let alpha := fun (y : Finset V) =>
      (y.powerset.filter (fun z => ∀ j ∈ z, ∀ k ∈ z, edge j k = false)).sup Finset.card
    let admits := fun (e : Nat) =>
      ∃ f : Finset V → V → Bool,
        (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true) ∧
        (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
        (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
        let pack := Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false)
        ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
    (m < a → ∀ k : Nat, (¬ admits (a*(k+1)-1)) ↔ k < score)) := by
  intro m d a g h1 h2 w V edge x score alpha admits hma k
  have L : ∀ e, admits e → a*score ≤ e := lowerT m d a g h1 h2 w
  have U : admits (a*score+m) := upperT m d a g h1 h2 w
  have mono : ∀ e e', e ≤ e' → admits e → admits e' := by
    rintro e e' hle ⟨f, c1, c2, c3, c4⟩
    exact ⟨f, c1, c2, c3, fun y l hy hp => (c4 y l hy hp).trans (by omega)⟩
  constructor
  · intro hn
    by_contra hk
    apply hn
    apply mono _ _ _ U
    have : a * score + a ≤ a * (k + 1) := by
      rw [Nat.mul_succ]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left a (by omega)) a
    omega
  · intro hk ha
    have h := L _ ha
    have : a * (k + 1) ≤ a * score := Nat.mul_le_mul_left a hk
    have : 0 < a := by omega
    have : 0 < a * (k + 1) := Nat.mul_pos this (Nat.succ_pos k)
    omega

end PEqualNP.Outside.L_meta_48518_aux

theorem PEqualNP.Outside.L_meta_48518 : (letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m d a : Nat) (g : Fin m → Fin m → Bool),
  (∀ i, g i i = false) → (∀ i j, g i j = g j i) →
  ∀ w : Fin m → Fin (d+1),
    let V := Fin m × (Fin (a*d) × Fin 3)
    let edge := fun (j k : V) =>
      if j.1 = k.1 then decide (j.2.1 = k.2.1 ∧
        (j.2.2.val+1 = k.2.2.val ∨ k.2.2.val+1 = j.2.2.val))
      else g j.1 k.1
    let x := (Finset.univ : Finset V).filter (fun j => j.2.1.val < a * (w j.1).val)
    let score := ((Finset.univ : Finset (Fin m)).powerset.filter
      (fun s => ∀ i ∈ s, ∀ j ∈ s, g i j = false)).sup
      (fun s => s.sum (fun i => (w i).val))
    let alpha := fun (y : Finset V) =>
      (y.powerset.filter (fun z => ∀ j ∈ z, ∀ k ∈ z, edge j k = false)).sup Finset.card
    let admits := fun (e : Nat) =>
      ∃ f : Finset V → V → Bool,
        (∀ y, y ⊆ x → ∀ j ∈ x, (j ∉ y ∧ ∀ i ∈ y, edge i j = false) → f y j = true) ∧
        (∀ y, y ⊆ x → ∀ j ∈ y, f y j = false) ∧
        (∀ u v, u ⊆ v → v ⊆ x → ∀ j ∈ x, f v j = true → f u j = true) ∧
        let pack := Nat.rec (motive := fun _ => Finset V → Prop) (fun _ => True)
          (fun _ prev y => ∃ (u v : Finset V) (j : V), j ∈ x ∧ prev u ∧
            u ⊆ v ∧ v ⊆ y ∧ f u j = true ∧ f v j = false)
        ∀ y l, y ⊆ x → pack l y → l ≤ alpha y + e
    (∀ e, admits e → a*score ≤ e) ∧ admits (a*score+m) ∧
      (m < a → ∀ k : Nat, (¬ admits (a*(k+1)-1)) ↔ k < score)) := by
  intro m d a g h1 h2 w
  exact ⟨PEqualNP.Outside.L_meta_48518_aux.lowerT m d a g h1 h2 w,
    PEqualNP.Outside.L_meta_48518_aux.upperT m d a g h1 h2 w,
    PEqualNP.Outside.L_meta_48518_aux.thirdT m d a g h1 h2 w⟩
