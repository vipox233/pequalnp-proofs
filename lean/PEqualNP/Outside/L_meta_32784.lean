import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_32784
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
lemma Al.symm {d : Bool} {a b : ℕ} (h : Al R d a b) : Al R d b a := by unfold Al at *; rwa [Nat.and_comm]
def Z0 : ℕ → ℕ := fun _ => 0
lemma al0 (d : Bool) (a b : ℕ) : Al Z0 d a b := by simp [Al, Z0]
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol R m T q' S' := by
  induction h with
  | done h => intro q' S' _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .un (hs h) (ih (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 ha _ ih =>
    intro q' S' hq hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) ha (ih (by omega) (Set.insert_subset_insert hs))
lemma Sol.rel {R' : ℕ → ℕ} {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Sol R' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hR _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) : Sol Z0 m T q S := h.rel fun d a b _ => al0 d a b
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : Sol Z0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (al0 _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol R m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live R m T k t S0 := by
  induction h with
  | @done q S h => exact ⟨0, by omega, 0, {T}, by simpa using h, .stop⟩
  | @un q S a ha _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, by omega, t + 1, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q S d a b ha hb hal _ ih =>
    obtain ⟨k, hk, t, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, insert a (insert b (S1.erase (op d a b))), ?_, .bi hab hal (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k, by omega, t, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
def C (m : ℕ) (S : Set ℕ) : Set ℕ := S ∪ {0, m}
lemma C_mono {m : ℕ} {S S' : Set ℕ} (h : S ⊆ S') : C m S ⊆ C m S' := Set.union_subset_union_left _ h
lemma sub_C (m : ℕ) (S : Set ℕ) : S ⊆ C m S := Set.subset_union_left
def Un (m a : ℕ) (S S' : Finset ℕ) : Prop := ∃ U, S = insert a U ∧ S' = insert (a ^^^ m) U
def Bi (R : ℕ → ℕ) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ Al R d a b
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S') :
    Live R m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') : Bi R d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hal.symm⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live R m T k t S ∧ ∀ q < k, ¬ Sol Z0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 m T q (C m S')) :
    Sol Z0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (al0 _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : Min R m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hl : Live R m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min R m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
  intro k t S ⟨hl, hm⟩
  induction hl with
  | stop => simp
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have ih := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have ih := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    rw [Finset.card_insert_of_notMem hf] at ih; omega
def phi (a n : ℕ) (X : Finset ℕ) : Finset ℕ := insert a (X.erase n)
lemma phi_un {m a n c : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (h1 : c ≠ n) (h2 : c ^^^ m ≠ n) :
    Un m c (phi a n X) (phi a n X') := by
  obtain ⟨U, rfl, rfl⟩ := h
  refine ⟨insert a (U.erase n), ?_, ?_⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi R d b c (phi a n X) (phi a n X') := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  refine ⟨hab, insert a (U.erase n), ?_, ?_, hal⟩ <;> ext x <;> simp [phi] <;> grind
lemma phi_back {m a : ℕ} {X : Finset ℕ} (h : a ^^^ m ∈ X) : Un m a (phi a (a ^^^ m) X) X :=
  ⟨X.erase (a ^^^ m), rfl, by rw [Finset.insert_erase h]⟩
lemma phi_start {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hn : a ^^^ m ∉ S) : phi a (a ^^^ m) S' = S := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn
  simp [phi, hn.2]
lemma un_keep {m c n : ℕ} {X X' : Finset ℕ} (h : Un m c X X') (hn : n ∈ X) (h1 : c ≠ n) : n ∈ X' := by
  obtain ⟨U, rfl, rfl⟩ := h
  simp at hn ⊢; exact Or.inr (hn.resolve_left (Ne.symm h1))
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi R d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma first_move {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min R m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi R d a b S S1 ∧ Live R m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi R d (a ^^^ m) c S1 S2 ∧ Live R m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi R d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live R m T k0 t0 S3) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t S hS hc
  obtain ⟨hl, hm⟩ := hS
  cases hl with
  | stop => simp at hc
  | @bi k t d a b U hab hal hl => exact Or.inl ⟨k, d, a, b, _, rfl, ⟨hab, U, rfl, rfl, hal⟩, hl⟩
  | @un k t a U hl =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf := hu.fresh hl hm
    have hn : a ^^^ m ∉ insert a U := fun h => hf (sub_C _ _ (by simpa using h))
    have hmin := hu.min hl hm
    have hxx : ∀ c : ℕ, c ^^^ m ^^^ m = c := fun c => by simp
    have hc' : 2 ≤ (insert (a ^^^ m) U).card := by
      have h1 := Finset.card_insert_le a U
      rw [Finset.card_insert_of_notMem (fun h => hn (by simp [h]))]; omega
    generalize hS1 : insert (a ^^^ m) U = S1 at *
    have hnS1 : a ^^^ m ∈ S1 := by rw [← hS1]; simp
    have hst := phi_start hu hn
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live R m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
      intro c k2 t2 S2 h2 hl2 hk
      constructor
      · rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        apply hm (k2 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (hl2.sol.mono le_rfl fun x hx => ?_)
        have h3 := hsub hx
        have h4 : x ∈ insert a (insert (a ^^^ m) U) := by rw [hS1]; exact h3
        simp at h4
        rcases h4 with rfl | rfl | h4
        · exact Or.inr (sub_C _ _ (by simp))
        · exact Or.inl rfl
        · exact Or.inr (sub_C _ _ (by simp [h4]))
      · intro e
        exact h2.fresh hl2 (by rw [← hk]; exact hmin.2) (sub_C _ _ (by rw [e]; simpa using hnS1))
    rcases ih k (by omega) t S1 hmin hc' with
      ⟨k0, d, x, y, S2, rfl, hb, hl2⟩ | ⟨k0, t0, c, d, y, S2, S3, rfl, rfl, h1, hb, hl2⟩ |
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hu, n1, h1, hb.symm, hl2⟩)
      have hk2 := un_keep h1 hnS1 n1
      have hg : op d (c ^^^ m) y ≠ a ^^^ m := fun e => hb.fresh hl2 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      refine Or.inr (Or.inl ⟨k0 + 1, t0 + 1, c, d, y, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, rfl, rfl, ?_, phi_bi hb n2 hy hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk2 n2 hy)).live hl2
    · have hb1 := hb.live hl2
      have hb2 := h2.live hb1
      obtain ⟨n1, n2⟩ := dbl h1 hb2 rfl
      have hm2 := h1.min hb2 hmin.2
      have hk2 := un_keep h1 hnS1 n1
      have hm3 := h2.min hb1 hm2.2
      have n3 : c' ≠ a ^^^ m := by
        rintro rfl
        have hsub := h2.sub.2
        rw [hxx] at hsub
        obtain ⟨hcS, hsub1⟩ := h1.sub
        have hcS' : c ∈ insert a U := by
          have : c ∈ insert (a ^^^ m) U := by rw [hS1]; exact hcS
          simp at this ⊢; exact Or.inr (this.resolve_left n1)
        apply hm (k0 + 1 + 1 + 1) (by omega)
        refine .un (a := a) (sub_C _ _ (by simp)) (.un (a := c) (Or.inr (sub_C _ _ (by simpa using hcS'))) (hb1.sol.mono le_rfl fun x hx => ?_))
        have h3 : x = a ∨ x = c ^^^ m ∨ x ∈ S1 := by
          have := hsub hx; simp at this
          rcases this with h | h
          · exact Or.inl h
          · have := hsub1 h; simp at this; exact Or.inr this
        rcases h3 with rfl | rfl | h3
        · exact Or.inr (Or.inr (sub_C _ _ (by simp)))
        · exact Or.inl rfl
        · rw [← hS1] at h3; simp at h3
          rcases h3 with rfl | h3
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (sub_C _ _ (by simp [h3])))
      have n4 : c' ^^^ m ≠ a ^^^ m := fun e => h2.fresh hb1 hm2.2 (sub_C _ _ (by rw [e]; simpa using hk2))
      have hk3 := un_keep h2 hk2 n3
      have hg : op d (c ^^^ m) (c' ^^^ m) ≠ a ^^^ m := fun e => hb.fresh hl2 hm3.2 (sub_C _ _ (by rw [e]; simpa using hk3))
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma and_op (d : Bool) (a b n : ℕ) : op d a b &&& n = op d (a &&& n) (b &&& n) := by
  apply Nat.eq_of_testBit_eq; intro i
  cases d <;> simp [op_bit] <;> grind
lemma and_neg {m n : ℕ} (hn : n &&& m = n) (a : ℕ) : (a ^^^ m) &&& n = (a &&& n) ^^^ n := by
  apply Nat.eq_of_testBit_eq; intro i
  have := congrArg (fun x => x.testBit i) hn
  simp at this ⊢
  grind
abbrev Cst (n x : ℕ) : Prop := x &&& n = 0 ∨ x &&& n = n
def Im (n : ℕ) (S : Finset ℕ) : Set ℕ := (fun x => x &&& n) '' (S : Set ℕ)
lemma Im_mem {n x : ℕ} {S : Finset ℕ} (h : x ∈ S) : x &&& n ∈ C n (Im n S) := Or.inl ⟨x, by simpa using h, rfl⟩
lemma Cst_mem {n x : ℕ} {S : Set ℕ} (h : Cst n x) : x &&& n ∈ C n S := by
  rcases h with h | h <;> simp [C, h]
lemma Cst_neg {m n a : ℕ} (hn : n &&& m = n) : Cst n (a ^^^ m) ↔ Cst n a := by
  unfold Cst; rw [and_neg hn]
  constructor
  · rintro (h | h)
    · right; have := congrArg (· ^^^ n) h; simpa using this
    · left; have := congrArg (· ^^^ n) h; simpa using this
  · rintro (h | h) <;> simp [h]
lemma op_cst {n a b : ℕ} (d : Bool) (ha : Cst n a) :
    op d a b &&& n = 0 ∨ op d a b &&& n = n ∨ op d a b &&& n = b &&& n := by
  rw [and_op]
  rcases ha with h | h <;> rw [h] <;> cases d
  · left; simp [op]
  · right; right; simp [op]
  · right; right; apply Nat.eq_of_testBit_eq; intro i; simp [op]
  · right; left; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_cst2 {n a b : ℕ} (d : Bool) (ha : Cst n a) (hb : Cst n b) : Cst n (op d a b) := by
  rcases op_cst (b := b) d ha with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · unfold Cst at hb ⊢; rw [h]; exact hb
lemma op_cst_mem {n a b : ℕ} {S : Finset ℕ} (d : Bool) (h : Cst n a ∨ Cst n b) (ha : a ∈ S) (hb : b ∈ S) :
    op d a b &&& n ∈ C n (Im n S) := by
  rcases h with h | h
  · rcases op_cst (b := b) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem hb
  · rw [op_comm]
    rcases op_cst (b := a) d h with e | e | e <;> rw [e]
    · simp [C]
    · simp [C]
    · exact Im_mem ha
lemma C_Im_sub {n g : ℕ} {S S' : Finset ℕ} {Q : Set ℕ} (h : S' ⊆ insert g S) (hg : g &&& n ∈ Q)
    (hQ : C n (Im n S) ⊆ Q) : C n (Im n S') ⊆ Q := by
  rintro x (⟨y, hy, rfl⟩ | hx)
  · have := h hy; simp at this
    rcases this with rfl | h'
    · exact hg
    · exact hQ (Im_mem h')
  · exact hQ (Or.inr hx)
section proj
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (al0 _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) :
    Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol Z0 n (T &&& n) q (C n (Im n S'))) : Sol Z0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol Z0 n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q, ?_, hu.kill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q + 1, ?_, hu.im hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min R m T k t S) : 0 ∉ S ∧ m ∉ S := by
  obtain ⟨q, hq, hs⟩ := h.const (n := m) (by simp) (by rwa [hT]) (by rwa [hT])
  have hi : Im m S = (S : Set ℕ) := by
    ext x; constructor
    · rintro ⟨y, hy, rfl⟩; have := hS y hy; simp only; rw [this]; exact hy
    · intro hx; exact ⟨x, hx, hS x hx⟩
  rw [hi, hT] at hs
  have key : ∀ x ∈ S, ¬ Cst m x := by
    intro x hx hc
    have : 0 < (S.filter (Cst m)).card := Finset.card_pos.2 ⟨x, by simp [hx, hc]⟩
    exact h.2 q (by omega) hs
  exact ⟨fun h0 => key 0 h0 (Or.inl (by simp)), fun h1 => key m h1 (Or.inr (by simp))⟩
def sepb (N : ℕ) (d : Bool) (w i : ℕ) : Bool :=
  bif d then xor (w.testBit i) (w.testBit (N + i)) else w.testBit i && !w.testBit (N + i)
def pos' (t : ℕ) : Bool := decide (0 < t)
section cov
variable {N m T i : ℕ} (m1 : m.testBit i = true) (m2 : m.testBit (N + i) = true)
  (t1 : T.testBit i = true) (t2 : T.testBit (N + i) = false)
include t1 t2 m1 m2
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
  induction h with
  | stop => exact ⟨T, by simp, by simp [sepb, pos', t1, t2]⟩
  | @un k t a U _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    have weak : sepb N true w i = true := by
      revert hs; cases pos' t <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨a, by simp, ?_⟩
      revert weak; simp [sepb, pos', m1, m2]
    · exact ⟨w, by simp [hw], by simpa [pos'] using weak⟩
  | @bi k t d a b U _ _ _ ih =>
    obtain ⟨w, hw, hs⟩ := ih
    simp at hw
    rcases hw with rfl | hw
    · by_cases ha : sepb N (pos' t) a i = true
      · exact ⟨a, by simp, ha⟩
      · refine ⟨b, by simp, ?_⟩
        revert hs ha
        unfold sepb; simp only [op_bit]
        cases pos' t <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact ⟨w, by simp [hw], hs⟩
end cov
def Uq (N : ℕ) (e : Bool) (S : Finset ℕ) (a i : ℕ) : Prop :=
  sepb N e a i = true ∧ ∀ c ∈ S, c ≠ a → sepb N e c i = false
lemma sepb_weak {N w i : ℕ} (e : Bool) (h : sepb N e w i = true) : sepb N true w i = true := by
  revert h; cases e <;> simp [sepb] <;> cases w.testBit i <;> cases w.testBit (N + i) <;> simp
section rect
variable {N m T : ℕ}
def Lg (N m T i : ℕ) : Prop := m.testBit i = true ∧ m.testBit (N + i) = true ∧ T.testBit i = true ∧ T.testBit (N + i) = false
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (hi : Lg N m T i)
    (hc : c ∈ insert a (insert b U)) (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl
      rcases hcc with rfl | rfl; exacts [ha hx, hb hx]
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma un_uq {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (ha : a ∉ U)
    (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
  by_cases hcc : c = a
  · rw [ite_eq_left hcc]; subst hcc
    refine ⟨by rw [hn]; exact h.1, fun x hx hne => ?_⟩
    simp at hx
    exact h.2 x (by simp [hx.resolve_left hne]) (fun e => ha (e ▸ hx.resolve_left hne))
  · rw [ite_eq_right hcc]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hcc)
    · exact h.2 x (by simp [hx]) hne
lemma phi_mem {x y g c : ℕ} {U : Finset ℕ} (hc : c ∈ insert x (insert y U)) :
    (if c = x ∨ c = y then g else c) ∈ insert g U := by
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢; tauto
lemma phi_ne {x y g a b : ℕ} {U : Finset ℕ} (hg : g ∉ U) (ha : a ∈ insert x (insert y U)) (hb : b ∈ insert x (insert y U))
    (hab : a ≠ b) (h : ¬ ((a = x ∨ a = y) ∧ (b = x ∨ b = y))) :
    (if a = x ∨ a = y then g else a) ≠ (if b = x ∨ b = y then g else b) := by
  simp only [Finset.mem_insert] at ha hb
  split_ifs with p q q
  · exact absurd ⟨p, q⟩ h
  · rintro rfl; tauto
  · rintro rfl; tauto
  · exact hab
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : Al R d a b) (hl : Live R m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min R m T k t (insert (op d a b) U) := by
  have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live R m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol Z0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min R m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live R m T k 0 S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N false S a i1 → Uq N false S b i2 → Uq N false S a j1 → Uq N false S b j2 → False := by
  generalize ht : 0 = t at hl
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | un => omega
  | @bi k t d x y U hxy hal hl ih =>
    subst ht
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by simpa using hc)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N false (insert x (insert y U)) c i →
        Uq N false (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inr (by simp [pos'])) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4
      have e1 := r1 b hb; have e2 := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have s1 := v1.1; have s3 := v3.1; have s2 := u2.1; have s4 := u4.1
      revert e1 e2 n1 n3 s1 s3 s2 s4
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 (by simpa using hc') rfl ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i j : ℕ} (h1 : Lg N m T i) (h2 : Lg N m T j) :
    ∀ {a : ℕ}, a ∈ S → Uq N true S a i → Uq N true S a j → a.testBit i = a.testBit j := by
  induction hl with
  | stop => intro a ha _ _; simp at ha; subst ha; rw [h1.2.2.1, h2.2.2.1]
  | @un k t x U hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    have := ih hmin.2 hc' (a := if a = x then x ^^^ m else a) (by split_ifs with h <;> simp at ha ⊢; tauto)
      (un_uq h1 hx ha u1) (un_uq h2 hx ha u2)
    split_ifs at this with h
    · subst h; simpa [h1.1, h2.1] using this
    · exact this
  | @bi k t d x y U hxy hal hl ih =>
    intro a ha u1 u2
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have v1 := bi_uq (Or.inl rfl) hl hx hy h1 ha u1
    have v2 := bi_uq (Or.inl rfl) hl hx hy h2 ha u2
    have := ih hmin.2 hc' (phi_mem ha) v1 v2
    split_ifs at this v1 v2 with h
    · obtain ⟨b, hb, hab, hop⟩ : ∃ b ∈ insert x (insert y U), b ≠ a ∧ op d x y = op d a b := by
        rcases h with rfl | rfl
        · exact ⟨y, by simp, Ne.symm hxy, rfl⟩
        · exact ⟨x, by simp, hxy, op_comm _ _ _⟩
      rw [hop] at this v1 v2
      have n1 := u1.2 b hb hab; have n2 := u2.2 b hb hab
      have s1 := v1.1; have s2 := v2.1; have p1 := u1.1; have p2 := u2.1
      revert this n1 n2 s1 s2 p1 p2
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · exact this
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (hc : S.card + t = k + 1) {i1 i2 j1 j2 : ℕ} (h1 : Lg N m T i1) (h2 : Lg N m T i2) (h3 : Lg N m T j1) (h4 : Lg N m T j2) :
    ∀ {a b : ℕ}, a ∈ S → b ∈ S → a ≠ b →
    (∀ w ∈ S, w.testBit i1 = w.testBit i2) → (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) →
    Uq N true S a i1 → Uq N true S b i2 → Uq N true S a j1 → Uq N true S b j2 → False := by
  induction hl with
  | stop => intro a b ha hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t x U hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hg, hc', hmin⟩ := un_tight hl hm (by omega)
    refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (un_uq h1 hx ha u1) (un_uq h2 hx hb u2) (un_uq h3 hx ha u3) (un_uq h4 hx hb u4)
    · split_ifs with h <;> simp at ha ⊢; tauto
    · split_ifs with h <;> simp at hb ⊢; tauto
    · split_ifs with p q q
      · exact absurd (p.trans q.symm) hab
      · intro e; simp at hb; rw [← e] at hb; rcases hb with h | h
        · exact q (by rw [← e, h])
        · exact hg h
      · intro e; simp at ha; rw [e] at ha; rcases ha with h | h
        · exact p (by rw [e, h])
        · exact hg h
      · exact hab
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r1 x (by simp), h1.1, h2.1]
      · exact r1 w (by simp [hw])
    · intro w hw; simp at hw
      rcases hw with rfl | hw
      · simp [r2 x (by simp), h3.2.1, h4.2.1]
      · exact r2 w (by simp [hw])
  | @bi k t d x y U hxy hal hl ih =>
    intro a b ha hb hab r1 r2 u1 u2 u3 u4
    obtain ⟨hx, hy, hg, hc', hmin⟩ := bi_tight hxy hal hl hm (by omega)
    have tr : ∀ {c i}, Lg N m T i → c ∈ insert x (insert y U) → Uq N true (insert x (insert y U)) c i →
        Uq N true (insert (op d x y) U) (if c = x ∨ c = y then op d x y else c) i :=
      fun hi hc h => bi_uq (Or.inl rfl) hl hx hy hi hc h
    by_cases hab' : (a = x ∨ a = y) ∧ (b = x ∨ b = y)
    · have v1 := tr h1 ha u1; have v2 := tr h2 hb u2; have v3 := tr h3 ha u3; have v4 := tr h4 hb u4
      rw [ite_eq_left hab'.1] at v1 v3; rw [ite_eq_left hab'.2] at v2 v4
      have hpol := polar hl hmin.2 hc' h1 h3 (by simp) v1 v3
      have hop : op d x y = op d a b := by
        rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
        · exact absurd rfl hab
        · rfl
        · exact op_comm _ _ _
        · exact absurd rfl hab
      rw [hop] at v1 v2 v3 v4 hpol
      have e1 := r1 a ha; have e2 := r2 a ha; have e1b := r1 b hb; have e2b := r2 b hb
      have n1 := u1.2 b hb (Ne.symm hab); have n3 := u3.2 b hb (Ne.symm hab)
      have n2 := u2.2 a ha hab; have n4 := u4.2 a ha hab
      have s1 := v1.1; have s3 := v3.1; have s2 := v2.1; have s4 := v4.1
      have p1 := u1.1; have p2 := u2.1; have p3 := u3.1; have p4 := u4.1
      revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 p1 p2 p3 p4 hpol
      unfold sepb; simp only [op_bit]
      cases d <;> simp <;> grind
    · refine ih hmin.2 hc' ?_ ?_ ?_ ?_ ?_ (tr h1 ha u1) (tr h2 hb u2) (tr h3 ha u3) (tr h4 hb u4)
      · exact phi_mem ha
      · exact phi_mem hb
      · exact phi_ne hg ha hb hab hab'
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r1 x (by simp), r1 y (by simp)]
        · exact r1 w (by simp [hw])
      · intro w hw; simp at hw
        rcases hw with rfl | hw
        · simp only [op_bit, r2 x (by simp), r2 y (by simp)]
        · exact r2 w (by simp [hw])
end rect
section chrom
variable {N m T : ℕ}
def Ht (N m T : ℕ) (e : Bool) (S : Finset ℕ) (a b : ℕ) : Prop := ∃ i1 i2 j1 j2, Lg N m T i1 ∧ Lg N m T i2 ∧ Lg N m T j1 ∧ Lg N m T j2 ∧
  (∀ w ∈ S, w.testBit i1 = w.testBit i2) ∧ (∀ w ∈ S, w.testBit (N + j1) = w.testBit (N + j2)) ∧
  Uq N e S a i1 ∧ Uq N e S b i2 ∧ Uq N e S a j1 ∧ Uq N e S b j2 ∧ a.testBit i1 = a.testBit j1 ∧ b.testBit i2 = b.testBit j2
lemma Ht.symm {e : Bool} {S : Finset ℕ} {a b : ℕ} (h : Ht N m T e S a b) : Ht N m T e S b a := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  exact ⟨i2, i1, j2, j1, l2, l1, l4, l3, fun w hw => (r1 w hw).symm, fun w hw => (r2 w hw).symm, u2, u1, u4, u3, p2, p1⟩
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hi : Lg N m T i) (hc : c ∈ insert a (insert b U)) (h1 : c = a → a ∉ U) (h2 : c = b → b ∉ U)
    (h : Uq N e (insert a (insert b U)) c i) :
    Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i := by
  obtain ⟨w, hw, hs⟩ := hl.cov hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hs : sepb N e w i = true := by
    rcases he with rfl | rfl
    · exact sepb_weak _ hs
    · exact hs
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc]
    have hcU : c ∉ U := by
      rcases hcc with rfl | rfl; exacts [h1 rfl, h2 rfl]
    have hU : ∀ x ∈ U, sepb N e x i = false := by
      intro x hx
      refine h.2 x (by simp [hx]) ?_
      rintro rfl; exact hcU hx
    simp at hw
    rcases hw with rfl | hw
    · refine ⟨hs, fun x hx hne => ?_⟩
      simp at hx; exact hU x (hx.resolve_left hne)
    · rw [hU w hw] at hs; simp at hs
  · rw [ite_eq_right hcc]
    push Not at hcc
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · have h1 := h.2 a (by simp) (Ne.symm hcc.1)
      have h2 := h.2 b (by simp) (Ne.symm hcc.2)
      revert h1 h2; unfold sepb; simp only [op_bit]
      cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
          cases b.testBit (N + i) <;> simp
    · exact h.2 x (by simp [hx]) hne
lemma pol_op {a b i : ℕ} {d e : Bool} (ha : sepb N e a i = true) (hb : sepb N e b i = false) (ho : sepb N e (op d a b) i = true) :
    (op d a b).testBit i = a.testBit i := by
  revert ha hb ho; unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> cases a.testBit i <;> cases a.testBit (N + i) <;> cases b.testBit i <;>
    cases b.testBit (N + i) <;> simp
lemma pol_phi {a b c i : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (h : Uq N e (insert a (insert b U)) c i)
    (hu : Uq N e (insert (op d a b) U) (if c = a ∨ c = b then op d a b else c) i) :
    (if c = a ∨ c = b then op d a b else c).testBit i = c.testBit i := by
  by_cases hcc : c = a ∨ c = b
  · rw [ite_eq_left hcc] at hu ⊢
    rcases hcc with rfl | rfl
    · exact pol_op h.1 (h.2 b (by simp) (Ne.symm hab)) hu.1
    · rw [op_comm] at hu ⊢
      exact pol_op h.1 (h.2 a (by simp) hab) hu.1
  · rw [ite_eq_right hcc]
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (hc1 : c1 ∈ insert a (insert b U)) (hc2 : c2 ∈ insert a (insert b U))
    (h1 : c1 = a → a ∉ U) (h1' : c1 = b → b ∉ U) (h2 : c2 = a → a ∉ U) (h2' : c2 = b → b ∉ U)
    (h : Ht N m T e (insert a (insert b U)) c1 c2) :
    Ht N m T e (insert (op d a b) U) (if c1 = a ∨ c1 = b then op d a b else c1) (if c2 = a ∨ c2 = b then op d a b else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := bi_uq2 he hl l1 hc1 h1 h1' u1
  have v2 := bi_uq2 he hl l2 hc2 h2 h2' u2
  have v3 := bi_uq2 he hl l3 hc1 h1 h1' u3
  have v4 := bi_uq2 he hl l4 hc2 h2 h2' u4
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, v1, v2, v3, v4, ?_, ?_⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r1 a (by simp), r1 b (by simp)]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp only [op_bit, r2 a (by simp), r2 b (by simp)]
    · exact r2 w (by simp [hw])
  · rw [pol_phi hab u1 v1, pol_phi hab u3 v3, p1]
  · rw [pol_phi hab u2 v2, pol_phi hab u4 v4, p2]
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live R m T k t (insert (op d a b) U))
    (ha : a ∉ U) (hb : b ∉ U) (h : Ht N m T e (insert a (insert b U)) a b) : False := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have v1 := (bi_uq2 he hl l1 (by simp) (fun _ => ha) (fun _ => hb) u1).1
  have v2 := (bi_uq2 he hl l2 (by simp) (fun _ => ha) (fun _ => hb) u2).1
  have v3 := (bi_uq2 he hl l3 (by simp) (fun _ => ha) (fun _ => hb) u3).1
  have v4 := (bi_uq2 he hl l4 (by simp) (fun _ => ha) (fun _ => hb) u4).1
  simp only [true_or, or_true, if_true] at v1 v2 v3 v4
  have e1 := r1 a (by simp); have e2 := r2 a (by simp); have e1b := r1 b (by simp); have e2b := r2 b (by simp)
  have n1 := u1.2 b (by simp) (Ne.symm hab); have n3 := u3.2 b (by simp) (Ne.symm hab)
  have n2 := u2.2 a (by simp) hab; have n4 := u4.2 a (by simp) hab
  have s1 := u1.1; have s2 := u2.1; have s3 := u3.1; have s4 := u4.1
  revert e1 e2 e1b e2b n1 n2 n3 n4 s1 s2 s3 s4 v1 v2 v3 v4 p1 p2
  unfold sepb; simp only [op_bit]
  cases e <;> cases d <;> simp <;> grind
lemma un_uq2 {a c i : ℕ} {U : Finset ℕ} (hi : Lg N m T i) (h1 : c = a → a ∉ U) (hc : c ∈ insert a U) (h : Uq N true (insert a U) c i) :
    Uq N true (insert (a ^^^ m) U) (if c = a then a ^^^ m else c) i := by
  by_cases hca : c = a
  · exact un_uq hi (h1 hca) hc h
  · rw [ite_eq_right hca]
    have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
    refine ⟨h.1, fun x hx hne => ?_⟩
    simp at hx
    rcases hx with rfl | hx
    · rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
    · exact h.2 x (by simp [hx]) hne
lemma ht_un {a c1 c2 : ℕ} {U : Finset ℕ} (hc1 : c1 ∈ insert a U) (hc2 : c2 ∈ insert a U) (h1 : c1 = a → a ∉ U) (h2 : c2 = a → a ∉ U)
    (h : Ht N m T true (insert a U) c1 c2) :
    Ht N m T true (insert (a ^^^ m) U) (if c1 = a then a ^^^ m else c1) (if c2 = a then a ^^^ m else c2) := by
  obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := h
  have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
      (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
    intro c i j m1 m2 p
    split_ifs with h
    · subst h; simp [m1, m2, p]
    · exact p
  refine ⟨i1, i2, j1, j2, l1, l2, l3, l4, ?_, ?_, un_uq2 l1 h1 hc1 u1, un_uq2 l2 h2 hc2 u2, un_uq2 l3 h1 hc1 u3, un_uq2 l4 h2 hc2 u4,
    pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r1 a (by simp), l1.1, l2.1]
    · exact r1 w (by simp [hw])
  · intro w hw; simp at hw
    rcases hw with rfl | hw
    · simp [r2 a (by simp), l3.2.1, l4.2.1]
    · exact r2 w (by simp [hw])
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live R m T k t S) (hm : ∀ q < k, ¬ Sol Z0 m T q (C m (S : Set ℕ)))
    (he : e = true ∨ t = 0) :
    ∃ (x : ℕ) (f : ℕ → ℕ), S.card + t + x = k + 1 ∧ (∀ a ∈ S, f a ≤ x) ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Ht N m T e S a b → f a ≠ f b := by
  induction hl with
  | stop =>
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro a ha b hb hab; simp at ha hb; exact absurd (ha.trans hb.symm) hab
  | @un k t a U hl ih =>
    have he1 : e = true := he.resolve_right (by omega)
    subst he1
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have hmin := hu.min hl hm
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at hx
    have sm : ∀ {i1 i2 : ℕ}, m.testBit i1 = true → m.testBit i2 = true → (∀ w ∈ insert a U, w.testBit i1 = w.testBit i2) →
        ∀ w ∈ insert (a ^^^ m) U, w.testBit i1 = w.testBit i2 := by
      intro i1 i2 m1 m2 r w hw
      simp at hw
      rcases hw with rfl | hw
      · simp [r a (by simp), m1, m2]
      · exact r w (by simp [hw])
    by_cases ha : a ∈ U
    · have eS : insert a U = U := Finset.insert_eq_of_mem ha
      refine ⟨x + 1, fun c => if c = a then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
      · intro c hcS
        rw [eS] at hcS
        by_cases hca : c = a
        · simp [hca]
        · simp only [hca, if_false]
          have := hfx c (by simp [hcS]); omega
      · intro c1 h1 c2 h2 h12 hh
        rw [eS] at h1 h2
        by_cases q1 : c1 = a
        · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
          have := hfx c2 (by simp [h2])
          simp only [q1, q2, if_true, if_false]; omega
        · by_cases q2 : c2 = a
          · have := hfx c1 (by simp [h1])
            simp only [q1, q2, if_true, if_false]; omega
          · simp only [q1, q2, if_false]
            refine hc c1 (by simp [h1]) c2 (by simp [h2]) h12 ?_
            obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
            have tr : ∀ {c i : ℕ}, c ≠ a → Lg N m T i → Uq N true (insert a U) c i → Uq N true (insert (a ^^^ m) U) c i := by
              intro c i hca hi h
              refine ⟨h.1, fun y hy hne => ?_⟩
              simp at hy
              rcases hy with rfl | hy
              · have hn : sepb N true (a ^^^ m) i = sepb N true a i := by simp [sepb, hi.1, hi.2.1]
                rw [hn]; exact h.2 a (by simp) (Ne.symm hca)
              · exact h.2 y (by simp [hy]) hne
            exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, tr q1 l1 u1, tr q2 l2 u2, tr q1 l3 u3, tr q2 l4 u4, p1, p2⟩
    · rw [Finset.card_insert_of_notMem ha]
      have mem : ∀ {c : ℕ}, c ∈ insert a U → (if c = a then a ^^^ m else c) ∈ insert (a ^^^ m) U := by
        intro c hcS; split_ifs with h <;> simp at hcS ⊢; tauto
      refine ⟨x, fun c => f (if c = a then a ^^^ m else c), by omega, fun c hcS => hfx _ (mem hcS), ?_⟩
      intro c1 h1 c2 h2 h12 hh
      refine hc _ (mem h1) _ (mem h2) ?_ ?_
      · split_ifs with p q q
        · exact absurd (p.trans q.symm) h12
        · intro e; simp at h2; rw [← e] at h2; rcases h2 with h | h
          · exact q (by rw [← e, h])
          · exact hf h
        · intro e; simp at h1; rw [e] at h1; rcases h1 with h | h
          · exact p (by rw [e, h])
          · exact hf h
        · exact h12
      · obtain ⟨i1, i2, j1, j2, l1, l2, l3, l4, r1, r2, u1, u2, u3, u4, p1, p2⟩ := hh
        have pp : ∀ {c i j : ℕ}, m.testBit i = true → m.testBit j = true → c.testBit i = c.testBit j →
            (if c = a then a ^^^ m else c).testBit i = (if c = a then a ^^^ m else c).testBit j := by
          intro c i j m1 m2 p
          split_ifs with h
          · subst h; simp [m1, m2, p]
          · exact p
        exact ⟨i1, i2, j1, j2, l1, l2, l3, l4, sm l1.1 l2.1 r1, sm l3.2.1 l4.2.1 r2, un_uq l1 ha h1 u1, un_uq l2 ha h2 u2, un_uq l3 ha h1 u3, un_uq l4 ha h2 u4,
          pp l1.1 l3.1 p1, pp l2.1 l4.1 p2⟩
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hu.fresh hl hm (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have hmin := hu.min hl hm
    have he2 : e = true ∨ e = pos' t := by
      rcases he with h | h
      · exact Or.inl h
      · subst h; cases e <;> simp [pos']
    obtain ⟨x, f, hx, hfx, hc⟩ := ih hmin.2 he
    rw [Finset.card_insert_of_notMem hf] at hx
    have mem : ∀ {c : ℕ}, c ∈ insert a (insert b U) → (if c = a ∨ c = b then op d a b else c) ∈ insert (op d a b) U := fun h => phi_mem h
    by_cases ha : a ∈ U
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = U := by rw [Finset.insert_eq_of_mem hb, Finset.insert_eq_of_mem ha]
        refine ⟨x + 2, fun c => if c = a then x + 2 else if c = b then x + 1 else f c, by rw [eS]; omega, ?_, ?_⟩
        · intro c hcS
          rw [eS] at hcS
          have := hfx c (by simp [hcS])
          dsimp only; split_ifs <;> omega
        · intro c1 h1 c2 h2 h12 hh
          have k1 := h1; have k2 := h2
          rw [eS] at h1 h2
          have f1 := hfx c1 (by simp [h1]); have f2 := hfx c2 (by simp [h2])
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false]; split_ifs <;> omega
            · by_cases q3 : c1 = b
              · have q4 : c2 ≠ b := fun e => h12 (q3.trans e.symm)
                simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
              · by_cases q4 : c2 = b
                · simp only [q1, q2, q3, q4, if_true, if_false]; rw [if_neg (Ne.symm hab)]; omega
                · simp only [q1, q2, q3, q4, if_false]
                  have := ht_bi hab he2 hl k1 k2 (fun e => absurd e q1) (fun e => absurd e q3) (fun e => absurd e q2) (fun e => absurd e q4) hh
                  simp only [q1, q2, q3, q4, or_self, if_false] at this
                  exact hc c1 (by simp [h1]) c2 (by simp [h2]) h12 this
      · have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
        refine ⟨x + 1, fun c => if c = a then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem hb]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = a
          · simp [hca]
          · simp only [hca, if_false, false_or] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = a
          · have q2 : c2 ≠ a := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, false_or] at f2 ⊢; omega
          · by_cases q2 : c2 = a
            · simp only [q1, q2, if_true, if_false, false_or] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun e => absurd e q1) (fun _ => hb) (fun e => absurd e q2) (fun _ => hb) hh
              simp only [q1, q2, if_false, false_or] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
    · by_cases hb : b ∈ U
      · have eS : insert a (insert b U) = insert a U := by rw [Finset.insert_eq_of_mem hb]
        refine ⟨x + 1, fun c => if c = b then x + 1 else f (if c = a ∨ c = b then op d a b else c), ?_, ?_, ?_⟩
        · rw [eS, Finset.card_insert_of_notMem ha]; omega
        · intro c hcS
          have := hfx _ (mem hcS)
          dsimp only; by_cases hca : c = b
          · simp [hca]
          · simp only [hca, if_false, or_false] at this ⊢; omega
        · intro c1 h1 c2 h2 h12 hh
          have f1 := hfx _ (mem h1); have f2 := hfx _ (mem h2)
          by_cases q1 : c1 = b
          · have q2 : c2 ≠ b := fun e => h12 (q1.trans e.symm)
            simp only [q1, q2, if_true, if_false, or_false] at f2 ⊢; omega
          · by_cases q2 : c2 = b
            · simp only [q1, q2, if_true, if_false, or_false] at f1 ⊢; omega
            · have := ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun e => absurd e q1) (fun _ => ha) (fun e => absurd e q2) hh
              simp only [q1, q2, if_false, or_false] at this f1 f2 ⊢
              refine hc _ (by simpa [q1] using mem h1) _ (by simpa [q2] using mem h2) ?_ this
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; tauto
              split_ifs with p q q
              · exact absurd (p.trans q.symm) h12
              · intro e; exact hf (e ▸ h2'.resolve_left q)
              · intro e; exact hf (e ▸ h1'.resolve_left p)
              · exact h12
      · refine ⟨x, fun c => f (if c = a ∨ c = b then op d a b else c), ?_, fun c hcS => hfx _ (mem hcS), ?_⟩
        · rw [Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hb]; omega
        · intro c1 h1 c2 h2 h12 hh
          by_cases hab' : (c1 = a ∨ c1 = b) ∧ (c2 = a ∨ c2 = b)
          · exfalso
            have : Ht N m T e (insert a (insert b U)) a b := by
              rcases hab' with ⟨rfl | rfl, rfl | rfl⟩
              · exact absurd rfl h12
              · exact hh
              · exact hh.symm
              · exact absurd rfl h12
            exact ht_merge hab he2 hl ha hb this
          · exact hc _ (mem h1) _ (mem h2) (phi_ne hf h1 h2 h12 hab')
              (ht_bi hab he2 hl h1 h2 (fun _ => ha) (fun _ => hb) (fun _ => ha) (fun _ => hb) hh)
end chrom
structure W where
  s : Nat
  a : Nat
  b : Nat
  c : Nat
  r : Nat
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 578
def AA : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fff0000)
def HX : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x82208208000 64) 0x4104000400080008) 64) 0x8208420004208400) 64) 0x1041000100020002) 64) 0x1042000880000000)
def HY : Nat := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x2 64) 0x200002008000) 64) 0x800004000020100) 64) 0x10040000200001) 64) 0x80002008000202) 64) 0x80000000000000) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x0)
noncomputable section core
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def sp (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def cov (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (sp d l w.s) ih) v
def twice (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (sp d l w.s) (cov d l t)) ih) v
def hit (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hits (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hit f e))) (m))
def flag (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (sp d l w.s) o) AA
def rect (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flag d l o w :: m)) (true) (hits (flag d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def join (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hits f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hits f c.b)) (hits f c.a)) cs
def bip (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => join ih f cs [f] [] []) (flag false l o w)) v
def anyE (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hits f t)) m
def rmF (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hit f e)) m
def star (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF f t))) false (hits f (rmF f t))) (anyE t)) (hits f t)) m
def flk (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flag false l o w)) v
def mkX (d : Bool) (l o : Nat) (v : List W) : List X :=
  List.rec (motive := fun _ => List X) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩ :: ih) v
def rm (x y : Nat) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h []) (fun w _ ih h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (ih h) (Nat.beq w.s y)) (ih h) (Nat.beq w.s x)) v
def ins (o : W) (v : List W) : (List W → Bool) → Bool :=
  List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [o]) (fun w t ih h => Bool.rec (motive := fun _ => Bool) (ih (fun r => h (w :: r))) (Bool.rec (motive := fun _ => Bool) (h (o :: w :: t)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def child (f : Nat → List W → Bool) (g : Nat) (mk : (List W → Bool) → Bool) (z : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (st z (fun z => mk (f z))) (Nat.beq (Nat.land z g) g)
def put (m s x y : Nat) (v : List W) (h : List W → Bool) : Bool :=
  (st (s) (fun s => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((st (x) (fun x1 => (st (y) (fun y1 => (st (Nat.lor x y) (fun w => ins ⟨s, x1, y1, w, 0⟩ v h))))))) (false) (Nat.beq s m))) (false) (Nat.beq s 0))))
def kids (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc))))) (Nat.ble (Nat.succ n) e))))) (true) ((Bool.rec (motive := fun _ => Bool) (false) ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a c' r h)) z) (oc))) (oa))))
def mid (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kids (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.mul da dc) 0))
def f2 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool := h a c da dc s x y
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : X) : Bool :=
  X.rec (motive := fun _ => Bool) (fun a s q u => X.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : X → Bool) (xs : List X) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : X → X → Bool) (xs : List X) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : X → X → Bool) (xs : List X) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List X) : List X := List.rec (motive := fun _ => List X) [] (fun a _ ih => Bool.rec (motive := fun _ => List X) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : X → X → Bool) (xs : List X) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : X → X → Bool) (xs : List X) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkX d l (wst d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cv (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (cov d l v) l)) b d
def tst (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst d l v) v star)) false (bip l (wst d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rect d l (wst d l v) v [])) (Nat.beq n e)) v.length
def mv (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          node (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (node (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (node (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end core
lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb NN d s i) := by
  cases d <;> simp [sp, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov]
  | cons w v ih =>
    change (Nat.lor (sp d l w.s) (cov d l v)).testBit i = true ↔ _
    simp [no, ih]
lemma twice_bit (d : Bool) (l i : ℕ) (v : List W) (h : (twice d l v).testBit i = false) :
    v.Pairwise (fun w w' => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) := by
  induction v with
  | nil => simp
  | cons w v ih =>
    change (Nat.lor (Nat.land (sp d l w.s) (cov d l v)) (twice d l v)).testBit i = false at h
    simp only [no, nl, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_false_iff] at h
    refine List.pairwise_cons.2 ⟨fun w' hw' ⟨h1, h2⟩ => ?_, ih h.2⟩
    have := (cov_bit d l i v).2 ⟨w', hw', h2⟩
    simp [h1, this] at h
def Rep (v : List W) (S : Finset ℕ) : Prop := (v.map W.s).Nodup ∧ (v.map W.s).toFinset = S
lemma Rep.mem {v : List W} {S : Finset ℕ} (h : Rep v S) {x : ℕ} : x ∈ S ↔ ∃ w ∈ v, w.s = x := by
  rw [← h.2]; simp
lemma Rep.inj {v : List W} {S : Finset ℕ} (h : Rep v S) {w w' : W} (hw : w ∈ v) (hw' : w' ∈ v) (e : w.s = w'.s) : w = w' :=
  List.inj_on_of_nodup_map h.1 hw hw' e
lemma Rep.card {v : List W} {S : Finset ℕ} (h : Rep v S) : S.card = v.length := by
  rw [← h.2, List.toFinset_card_of_nodup h.1, List.length_map]
lemma uq_of {d : Bool} {l i : ℕ} {v : List W} {S : Finset ℕ} (h : Rep v S) {w : W} (hw : w ∈ v)
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq NN d S w.s i := by
  simp only [nl, wst, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
  obtain ⟨⟨hl, hs⟩, ht⟩ := hu
  have ht : (twice d l v).testBit i = false := by simpa [hl] using ht
  refine ⟨hl, hs, fun c hc hne => ?_⟩
  obtain ⟨w', hw', rfl⟩ := h.mem.1 hc
  have hp := twice_bit d l i v ht
  haveI : Std.Symm (fun w w' : W => ¬ ((sp d l w.s).testBit i = true ∧ (sp d l w'.s).testBit i = true)) :=
    ⟨fun a b h h' => h h'.symm⟩
  have := hp.forall hw hw' (fun e => hne (by rw [e]))
  simp only [sp_bit, hl, hs, Bool.true_and, true_and] at this
  simpa using this
def segsX : List (ℕ × ℕ) := [(15, 31), (31, 35), (35, 49), (49, 54), (54, 60), (60, 65), (65, 81), (81, 96), (96, 112), (112, 118), (118, 124), (124, 138), (138, 143), (143, 149), (149, 154), (154, 169), (169, 174), (174, 179), (179, 185), (185, 191), (191, 195), (195, 211), (211, 226), (226, 242), (242, 248), (248, 254), (254, 271), (271, 277), (277, 283), (283, 289), (289, 293), (293, 299)]
def segsY : List (ℕ × ℕ) := [(299, 311), (311, 321), (321, 329), (329, 347), (347, 357), (357, 375), (375, 384), (384, 405), (405, 426), (426, 436), (436, 456), (456, 465), (465, 486), (486, 507), (507, 527), (527, 537), (537, 557), (557, 577)]
def segOk (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok : segsX.all segOk = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok : segsY.all segOk = true := by decide +kernel
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq : HX = bitsOf segsX := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq : HY = bitsOf segsY := by decide +kernel
lemma bitsOf_bit {L : List (ℕ × ℕ)} {h : ℕ} (hh : (bitsOf L).testBit h = true) : ∃ s ∈ L, s.2 = h := by
  induction L with
  | nil => simp [bitsOf] at hh
  | cons s L ih =>
    change (2 ^ s.2 ||| bitsOf L).testBit h = true at hh
    rw [Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true] at hh
    rcases hh with hh | hh
    · exact ⟨s, by simp, by simpa using hh⟩
    · obtain ⟨s', hs', e⟩ := ih hh; exact ⟨s', by simp [hs'], e⟩
lemma carry {u A p h : ℕ} (hp : p < h) (hA : A % 2 ^ h + 2 ^ (p + 1) = 2 ^ h + A % 2 ^ p) (hAh : A.testBit h = false)
    (huh : u.testBit h = false) (hup : u.testBit p = false) (hs : (u + A).testBit h = true) :
    ∃ i, p < i ∧ i < h ∧ u.testBit i = true := by
  by_contra hno
  push Not at hno
  have e1 : u % 2 ^ h = u % 2 ^ p := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_mod_two_pow]
    by_cases h1 : i < p
    · simp [h1, show i < h by omega]
    · by_cases h2 : i < h
      · rcases Nat.lt_or_ge p i with h3 | h3
        · simp [h1, hno i h3 h2]
        · obtain rfl : i = p := by omega
          simp [hup]
      · simp [h1, h2]
  have l1 := Nat.mod_lt u (Nat.two_pow_pos p)
  have l2 := Nat.mod_lt A (Nat.two_pow_pos p)
  have hlt : u % 2 ^ h + A % 2 ^ h < 2 ^ h := by rw [e1]; have := Nat.pow_succ 2 p; omega
  have e2 : (u + A).testBit h = (u / 2 ^ h + A / 2 ^ h).testBit 0 := by
    have : u + A = 2 ^ h * (u / 2 ^ h + A / 2 ^ h) + (u % 2 ^ h + A % 2 ^ h) := by
      have a1 := Nat.div_add_mod u (2 ^ h); have a2 := Nat.div_add_mod A (2 ^ h)
      rw [Nat.mul_add]; omega
    rw [this, Nat.testBit_two_pow_mul_add _ hlt]; simp
  have b1 : (u / 2 ^ h).testBit 0 = false := by rw [← huh, Nat.testBit_div_two_pow]; simp
  have b2 : (A / 2 ^ h).testBit 0 = false := by rw [← hAh, Nat.testBit_div_two_pow]; simp
  rw [e2] at hs
  simp [Nat.testBit_zero] at hs b1 b2
  omega
def Same (L : List (ℕ × ℕ)) (i j : ℕ) : Prop := ∃ s ∈ L, s.1 < i ∧ i < s.2 ∧ s.1 < j ∧ j < s.2
def Good (l s : ℕ) : Prop := (∀ i j, Same segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (NN + i) = s.testBit (NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all segOk = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [HX_eq] at a3; rw [HY_eq] at b3
      obtain ⟨s, hs, rfl⟩ := bitsOf_bit a3
      obtain ⟨s', hs', rfl⟩ := bitsOf_bit b3
      exact ⟨⟨s, hs, a1, a2⟩, ⟨s', hs', b1, b2⟩⟩
lemma hits_false {f : ℕ} {m : List ℕ} (h : ∀ e ∈ m, hit f e = false) : hits f m = false := by
  induction m with
  | nil => rfl
  | cons e m ih =>
    change (Bool.rec (motive := fun _ => Bool) (hits f m) true (hit f e) : Bool) = false
    rw [bR, h e (by simp), ih (fun x hx => h x (by simp [hx]))]; rfl
lemma rect_false {d : Bool} {l o : ℕ} {v : List W} : ∀ {m : List ℕ}, v.Pairwise (fun a b => hit (flag d l o b) (flag d l o a) = false) →
    (∀ w ∈ v, ∀ e ∈ m, hit (flag d l o w) e = false) → rect d l o v m = false := by
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro m hp hm
    change (Bool.rec (motive := fun _ => Bool) (rect d l o v (flag d l o w :: m)) true (hits (flag d l o w) m) : Bool) = false
    rw [List.pairwise_cons] at hp
    rw [bR, hits_false (hm w (by simp)), ih hp.2]; · rfl
    intro w' hw' e he
    simp at he
    rcases he with rfl | he
    · exact hp.1 w' hw'
    · exact hm w' (by simp [hw']) e he
lemma Live.pos {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) : 0 < S.card := by
  cases h with
  | stop => simp
  | un => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
  | bi => exact Finset.card_pos.2 (Finset.insert_nonempty _ _)
def pk (n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range n, f j * 2 ^ (5 * j)
lemma pk_succ (n : ℕ) (f : ℕ → ℕ) : pk (n + 1) f = 2 ^ (5 * n) * f n + pk n f := by
  rw [pk, Finset.sum_range_succ, ← pk]; ring
lemma pk_lt {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, f j < 32) : pk n f < 2 ^ (5 * n) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have := ih (fun j hj => h j (by omega))
    have h2 := h n (by omega)
    rw [pk_succ, show 5 * (n + 1) = 5 * n + 5 by ring, pow_add]
    have : 2 ^ (5 * n) * f n ≤ 2 ^ (5 * n) * 31 := Nat.mul_le_mul_left _ (by omega)
    omega
lemma pk_add (n : ℕ) (f g : ℕ → ℕ) : pk n f + pk n g = pk n (fun j => f j + g j) := by
  simp [pk, ← Finset.sum_add_distrib, add_mul]
lemma pk_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, f j = g j) : pk n f = pk n g :=
  Finset.sum_congr rfl fun j hj => by rw [h j (by simpa using hj)]
lemma pk_sub {n : ℕ} {f g : ℕ → ℕ} (h : ∀ j < n, g j ≤ f j) : pk n f - pk n g = pk n (fun j => f j - g j) := by
  have : pk n (fun j => f j - g j) + pk n g = pk n f := by
    rw [pk_add]; exact pk_congr fun j hj => Nat.sub_add_cancel (h j hj)
  omega
lemma pk_guard {n : ℕ} {f : ℕ → ℕ} (h : ∀ j < n, 16 ≤ f j ∧ f j < 32) :
    pk n f &&& pk n (fun _ => 16) = pk n (fun _ => 16) := by
  induction n with
  | zero => simp [pk]
  | succ n ih =>
    have ih := ih (fun j hj => h j (by omega))
    have h1 : pk n f < 2 ^ (5 * n) := pk_lt fun j hj => (h j (by omega)).2
    have h2 : pk n (fun _ => 16) < 2 ^ (5 * n) := pk_lt fun _ _ => by omega
    have h3 : f n &&& 16 = 16 := by
      obtain ⟨a, b⟩ := h n (by omega)
      generalize f n = x at *
      interval_cases x <;> rfl
    rw [pk_succ, pk_succ]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
    split_ifs with hi
    · rw [← Nat.testBit_and, ih]
    · rw [← Nat.testBit_and, h3]
def isPk (n x : ℕ) : Prop := ∀ i, x.testBit i = true → i % 5 = 0 ∧ i / 5 < n
lemma pk_of {n : ℕ} : ∀ {x : ℕ}, isPk n x → x = pk n (fun j => (x.testBit (5 * j)).toNat) := by
  induction n with
  | zero =>
    intro x h
    simp only [pk, Finset.range_zero, Finset.sum_empty]
    apply Nat.eq_of_testBit_eq; intro i
    by_contra hc
    have := h i (by simpa using hc); omega
  | succ n ih =>
    intro x h
    have hm : isPk n (x % 2 ^ (5 * n)) := by
      intro i hi
      simp only [Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact ⟨(h i hi.2).1, by omega⟩
    have e := ih hm
    have hd : x / 2 ^ (5 * n) = (x.testBit (5 * n)).toNat := by
      apply Nat.eq_of_testBit_eq; intro i
      rw [Nat.testBit_div_two_pow]
      cases i with
      | zero => cases hb : x.testBit (5 * n) <;> simp [hb]
      | succ i =>
        have e1 : x.testBit (i + 1 + 5 * n) = false := by
          by_contra hc
          have := h _ (by simpa using hc); omega
        rw [e1]
        cases x.testBit (5 * n) <;> simp [Nat.testBit_succ]
    rw [pk_succ, ← hd]
    have e2 : pk n (fun j => (x.testBit (5 * j)).toNat) = x % 2 ^ (5 * n) := by
      conv_rhs => rw [e]
      refine pk_congr fun j hj => ?_
      rw [Nat.testBit_mod_two_pow]; simp [show 5 * j < 5 * n by omega]
    rw [e2]; exact (Nat.div_add_mod x _).symm
lemma isPk_and {n x y : ℕ} (hx : isPk n x) : isPk n (x &&& y) := fun i hi => hx i (by simp at hi; exact hi.1)
lemma isPk_or {n x y : ℕ} (hx : isPk n x) (hy : isPk n y) : isPk n (x ||| y) := fun i hi => by
  simp at hi; exact hi.elim (hx i) (hy i)
def fl (w : W) (j : ℕ) : ℕ := (w.c.testBit (5 * j)).toNat
lemma fl_le (w : W) (j : ℕ) : fl w j ≤ 1 := by unfold fl; cases w.c.testBit (5 * j) <;> simp
def cnt (v : List W) (j : ℕ) : ℕ := (v.map (fun w => fl w j)).sum
lemma cnt_cons (w : W) (v : List W) (j : ℕ) : cnt (w :: v) j = fl w j + cnt v j := by simp [cnt]
lemma cnt_perm {v v' : List W} (h : v.Perm v') (j : ℕ) : cnt v j = cnt v' j := (h.map _).sum_eq
structure WOk (P : List ℕ) (w : W) : Prop where
  pa : isPk P.length w.a
  pb : isPk P.length w.b
  ec : w.c = w.a ||| w.b
  ca : ∀ j < P.length, w.a.testBit (5 * j) = true → w.s &&& P.getD j 0 = 0
  cb : ∀ j < P.length, w.b.testBit (5 * j) = true → w.s &&& P.getD j 0 = P.getD j 0
lemma WOk.pc {P : List ℕ} {w : W} (h : WOk P w) : isPk P.length w.c := by rw [h.ec]; exact isPk_or h.pa h.pb
lemma WOk.cst {P : List ℕ} {w : W} (h : WOk P w) {j : ℕ} (hj : j < P.length) (hf : w.c.testBit (5 * j) = true) :
    Cst (P.getD j 0) w.s := by
  rw [h.ec, Nat.testBit_or, Bool.or_eq_true] at hf
  exact hf.elim (fun h1 => Or.inl (h.ca j hj h1)) (fun h1 => Or.inr (h.cb j hj h1))
def Cl (P : List ℕ) (T k : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + b j < k →
  ¬ Sol Z0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
  have hqb : ¬ q + b j < k := fun h => hc j hj q h hs
  have : cnt v j ≤ (S.filter (Cst (P.getD j 0))).card := by
    have e : cnt v j = (v.filter (fun w => w.c.testBit (5 * j))).length := by
      clear hr hw
      induction v with
      | nil => rfl
      | cons w v ih =>
        rw [cnt_cons, ih, List.filter_cons, fl]
        cases w.c.testBit (5 * j) <;> simp; omega
    rw [e, ← List.length_map W.s, ← List.toFinset_card_of_nodup (hr.1.sublist (List.filter_sublist.map _))]
    apply Finset.card_le_card
    intro x hx
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
    obtain ⟨w, ⟨h1, h2⟩, rfl⟩ := hx
    rw [Finset.mem_filter]
    exact ⟨hr.mem.2 ⟨w, h1, rfl⟩, (hw w h1).cst hj h2⟩
  omega
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
lemma rm_eq (x y : ℕ) (v : List W) : ∀ h, rm x y v h = h (v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y))) := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (rm x y v (fun r => h (w :: r)))
      (rm x y v h) (Nat.beq w.s y)) (rm x y v h) (Nat.beq w.s x) : Bool) = _
    rw [bR, bR, ih, ih, List.filter_cons]
    cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> simp
lemma ins_spec (o : W) (v : List W) (hv : ∀ w ∈ v, w.s ≠ o.s) : ∃ r : List W, r.Perm (o :: v) ∧ ∀ h, ins o v h = h r := by
  induction v with
  | nil => exact ⟨[o], List.Perm.refl _, fun h => rfl⟩
  | cons w v ih =>
    obtain ⟨r, hp, hr⟩ := ih fun w' hw' => hv w' (by simp [hw'])
    have e : ∀ h, ins o (w :: v) h = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then false else h (o :: w :: v)) else ins o v (fun r => h (w :: r)) := by
      intro h
      change (Bool.rec (motive := fun _ => Bool) (ins o v (fun r => h (w :: r)))
        (Bool.rec (motive := fun _ => Bool) (h (o :: w :: v)) false (Nat.beq o.s w.s)) (Nat.ble w.s o.s) : Bool) = _
      rw [bR, bR]
    cases hb : Nat.ble w.s o.s with
    | true =>
      refine ⟨o :: w :: v, List.Perm.refl _, fun h => ?_⟩
      have : Nat.beq o.s w.s = false := Bool.eq_false_iff.2 fun h => hv w (by simp) (Nat.eq_of_beq_eq_true h).symm
      rw [e, hb, this]; rfl
    | false =>
      refine ⟨w :: r, (List.Perm.cons w hp).trans (List.Perm.swap _ _ _), fun h => ?_⟩
      rw [e, hb, hr]; rfl
lemma filter_perm {v : List W} (hv : (v.map W.s).Nodup) {a : W} (ha : a ∈ v) :
    (a :: v.filter (fun w => !Nat.beq w.s a.s)).Perm v := by
  induction v with
  | nil => simp at ha
  | cons w v ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hv
    have hne : ∀ x y : ℕ, x ≠ y → Nat.beq x y = false := fun x y h => Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have : v.filter (fun w => !Nat.beq w.s a.s) = v := by
        rw [List.filter_eq_self]
        intro w' hw'
        rw [hne _ _ (hv.1 w' hw')]; rfl
      rw [List.filter_cons, this]; simp
    · rw [List.filter_cons, hne w.s a.s (fun e => hv.1 a ha e.symm)]
      simp only [Bool.not_false, if_true]
      exact (List.Perm.swap _ _ _).trans ((ih hv.2 ha).cons w)
lemma filter2 {v : List W} {x y : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s y)) =
    (v.filter (fun w => !Nat.beq w.s x)).filter (fun w => !Nat.beq w.s y) := by
  rw [List.filter_filter]; congr 1; funext w; cases Nat.beq w.s x <;> cases Nat.beq w.s y <;> rfl
lemma filter1 {v : List W} {x : ℕ} : v.filter (fun w => !(Nat.beq w.s x || Nat.beq w.s x)) = v.filter (fun w => !Nat.beq w.s x) := by
  congr 1; funext w; cases Nat.beq w.s x <;> rfl
inductive Shape (o a c : W) (v : List W) : Bool → Bool → List W → Prop
  | ff {r} : (a :: c :: r).Perm (o :: v) → Shape o a c v false false r
  | tf {r} : (c :: r).Perm (o :: v) → Shape o a c v true false r
  | ft {r} : (a :: r).Perm (o :: v) → Shape o a c v false true r
  | tt {r} : r.Perm (o :: v) → Shape o a c v true true r
lemma Shape.cnt {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) (j : ℕ) :
    cnt r j + (bif ka then 0 else fl a j) + (bif kc then 0 else fl c j) = fl o j + cnt v j := by
  cases h with
  | ff h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tf h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | ft h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
  | tt h => have := cnt_perm h j; simp only [cnt_cons] at this; simp; omega
lemma Shape.mem {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {w : W} (hw : w ∈ r) : w = o ∨ w ∈ v := by
  have : w ∈ o :: v := by
    cases h with
    | ff h => exact h.subset (by simp [hw])
    | tf h => exact h.subset (by simp [hw])
    | ft h => exact h.subset (by simp [hw])
    | tt h => exact h.subset (by simp [hw])
  simpa using this
lemma Shape.len {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) :
    r.length + (bif ka then 0 else 1) + (bif kc then 0 else 1) = v.length + 1 := by
  cases h with
  | ff h => have := h.length_eq; simp at this ⊢; omega
  | tf h => have := h.length_eq; simp at this ⊢; omega
  | ft h => have := h.length_eq; simp at this ⊢; omega
  | tt h => have := h.length_eq; simp at this ⊢; omega
lemma Shape.rep {o a c : W} {v r : List W} {ka kc : Bool} (h : Shape o a c v ka kc r) {S S' : Finset ℕ} (hr : Rep v S)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) (ho : o.s ∉ S)
    (hS : ∀ x, x ∈ S' ↔ x = o.s ∨ (x ∈ S ∧ (x = a.s → ka = true) ∧ (x = c.s → kc = true))) : Rep r S' := by
  have hov : ((o :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ho ?_, hr.1⟩
    rw [← hr.2]; simpa using hm
  have hvS : ∀ x, x ∈ v.map W.s ↔ x ∈ S := fun x => by rw [← hr.2]; simp
  have hm : ∀ x, x ∈ (o :: v).map W.s ↔ x = o.s ∨ x ∈ S := fun x => by simp only [List.map_cons, List.mem_cons, hvS]
  have haS := (hvS a.s).1 (List.mem_map_of_mem ha)
  have hcS := (hvS c.s).1 (List.mem_map_of_mem hc)
  have hao : a.s ≠ o.s := fun e => ho (e ▸ haS)
  have hco : c.s ≠ o.s := fun e => ho (e ▸ hcS)
  cases h with
  | ff h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hn
    refine ⟨hn.2.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n1 : x ≠ a.s := fun e => hn.1.2 (e ▸ h1)
      have n2 : x ≠ c.s := fun e => hn.2.1 (e ▸ h1)
      rcases hx.1 (Or.inr (Or.inr h1)) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n1, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · rcases hx.2 (Or.inl e) with e' | e' | e'
        · exact absurd (e'.symm.trans e) hao
        · exact absurd (e'.symm.trans e) hco
        · exact e'
      · rcases hx.2 (Or.inr e) with e' | e' | e'
        · exact absurd (f1 e') (by simp)
        · exact absurd (f2 e') (by simp)
        · exact e'
  | tf h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ c.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun _ => rfl, fun e => absurd e n2⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hco (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f2 e'
  | ft h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    simp only [List.map_cons, List.nodup_cons] at hn
    refine ⟨hn.2, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx; simp only [List.map_cons, List.mem_cons] at hx
    rw [List.mem_toFinset, hS]
    constructor
    · intro h1
      have n2 : x ≠ a.s := fun e => hn.1 (e ▸ h1)
      rcases hx.1 (Or.inr h1) with e | e
      · exact Or.inl e
      · exact Or.inr ⟨e, fun e => absurd e n2, fun _ => rfl⟩
    · rintro (e | ⟨e, f1, f2⟩)
      · exact (hx.2 (Or.inl e)).resolve_left fun e' => hao (e'.symm.trans e)
      · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  | tt h =>
    have hn := (h.map W.s).nodup_iff.2 hov
    refine ⟨hn, Finset.ext fun x => ?_⟩
    have hx := (h.map W.s).mem_iff (a := x)
    rw [hm] at hx
    rw [List.mem_toFinset, hS, hx]; simp
lemma shape_all {o a c : W} {v r : List W} (ho : ∀ w ∈ v, w.s ≠ o.s) (hp : r.Perm (o :: v)) (hv : (v.map W.s).Nodup)
    (ha : a ∈ v) (hc : c ∈ v) (hac : a.s ≠ c.s) :
    Shape o a c v false false (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s c.s))) ∧
    Shape o a c v true false (r.filter (fun w => !(Nat.beq w.s c.s || Nat.beq w.s c.s))) ∧
    Shape o a c v false true (r.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))) ∧ Shape o a c v true true r := by
  have hnd : (r.map W.s).Nodup := by
    refine (hp.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => ho w hw, hv⟩
  have har : a ∈ r := hp.symm.subset (by simp [ha])
  have hcr : c ∈ r := hp.symm.subset (by simp [hc])
  refine ⟨.ff ?_, .tf ?_, .ft ?_, .tt hp⟩
  · rw [filter2]
    have h1 := filter_perm hnd har
    have h2 : c ∈ r.filter (fun w => !Nat.beq w.s a.s) := by
      rw [List.mem_filter]; refine ⟨hcr, ?_⟩
      rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
    exact ((filter_perm (hnd.sublist (List.filter_sublist.map _)) h2).cons a).trans (h1.trans hp)
  · rw [filter1]; exact (filter_perm hnd hcr).trans hp
  · rw [filter1]; exact (filter_perm hnd har).trans hp
lemma cnt_two {v : List W} {a c : W} (ha : a ∈ v) (hc : c ∈ v) (hv : (v.map W.s).Nodup) (hac : a.s ≠ c.s) (j : ℕ) :
    fl a j + fl c j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  have h2 : c ∈ v.filter (fun w => !Nat.beq w.s a.s) := by
    rw [List.mem_filter]; refine ⟨hc, ?_⟩
    rw [Bool.eq_false_iff.2 fun h => hac (Nat.eq_of_beq_eq_true h).symm]; rfl
  have h3 := cnt_perm (filter_perm (hv.sublist (List.filter_sublist.map _)) h2) j
  simp only [cnt_cons] at h1 h3; omega
lemma cnt_one {v : List W} {a : W} (ha : a ∈ v) (hv : (v.map W.s).Nodup) (j : ℕ) : fl a j ≤ cnt v j := by
  have h1 := cnt_perm (filter_perm hv ha) j
  simp only [cnt_cons] at h1; omega
def opW (d : Bool) (a c : W) : W := bif d then ⟨a.s ||| c.s, a.a &&& c.a, a.b ||| c.b, (a.a &&& c.a) ||| (a.b ||| c.b), 0⟩
  else ⟨a.s &&& c.s, a.a ||| c.a, a.b &&& c.b, (a.a ||| c.a) ||| (a.b &&& c.b), 0⟩
lemma opW_s (d : Bool) (a c : W) : (opW d a c).s = op d a.s c.s := by cases d <;> rfl
lemma opW_ok {P : List ℕ} {a c : W} (d : Bool) (ha : WOk P a) (hc : WOk P c) : WOk P (opW d a c) := by
  cases d
  · refine ⟨isPk_or ha.pa hc.pa, isPk_and ha.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a ||| c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.ca j hj h]; simp [op]
      · rw [hc.ca j hj h]; simp [op]
    · have h : (a.b &&& c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.cb j hj h.1, hc.cb j hj h.2, op_self]
  · refine ⟨isPk_and ha.pa, isPk_or ha.pb hc.pb, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
    · have h : (a.a &&& c.a).testBit (5 * j) = true := h
      rw [Nat.testBit_and, Bool.and_eq_true] at h
      rw [opW_s, and_op, ha.ca j hj h.1, hc.ca j hj h.2, op_self]
    · have h : (a.b ||| c.b).testBit (5 * j) = true := h
      rw [Nat.testBit_or, Bool.or_eq_true] at h
      rw [opW_s, and_op]
      rcases h with h | h
      · rw [ha.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
      · rw [hc.cb j hj h]; apply Nat.eq_of_testBit_eq; intro i; simp [op]
lemma op_good {l x y : ℕ} (d : Bool) (hx : Good l x) (hy : Good l y) : Good l (op d x y) := by
  refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
  · rw [op_bit, op_bit, hx.1 i j h h1 h2, hy.1 i j h h1 h2]
  · rw [op_bit, op_bit, hx.2 i j h h1 h2, hy.2 i j h h1 h2]
lemma fl_and {P : List ℕ} {a c : W} (ha : WOk P a) : a.c &&& c.c = pk P.length (fun j => fl a j * fl c j) := by
  rw [pk_of (isPk_and (y := c.c) ha.pc)]
  refine pk_congr fun j _ => ?_
  rw [Nat.testBit_and]; unfold fl; cases a.c.testBit (5 * j) <;> cases c.c.testBit (5 * j) <;> rfl
lemma fl_pk {P : List ℕ} {a : W} (ha : WOk P a) : a.c = pk P.length (fl a) := pk_of ha.pc
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
    Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hab : a.s ≠ c.s := hb.1
  have hfr := hb.fresh hl hm.2
  have hfS : (opW d' a c).s ∉ S := by rw [opW_s]; exact fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha; have wc := hs.wok c hc
  have wo := opW_ok d' wa wc
  have hrep : Rep r S' := by
    refine hsh.rep hs.rep ha hc hab hfS fun x => ?_
    obtain ⟨_, U, e1, e2, _⟩ := hb
    rw [opW_s] at hfS ⊢
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_, ?_⟩
        · rintro rfl; rw [hka, e2]; simp [h]
        · rintro rfl; rw [hkc, e2]; simp [h]
    · rintro (h | ⟨h, f1, f2⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · have := f2 h; rw [hkc, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hsh.mem hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s]; exact op_good _ (hs.good a ha) (hs.good c hc)
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.im hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill.1]
      have e2 : fl c j = 0 := by simp [fl, hkill.2]
      rw [e1, e2] at hq; simp at hq; omega
  have hmin := hb.min hl hm.2
  have hle' := cnt_le X hrep hwok hcl' hmin hk
  have num : ∀ j < P.length, 1 ≤ 16 + b j - cnt v j + fl a j * fl c j ∧ fl (opW d' a c) j ≤ 1 ∧
      16 ≤ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j ∧ 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j < 32 ∧
      16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j - (bif ka then fl a j else 0) - (bif kc then fl c j else 0) = 16 + b' j - cnt r j := by
    intro j hj
    have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_two ha hc hs.rep.1 hab j; have q4 := hb15 j hj
    have q5 := hsh.cnt j; have q6 := fl_le a j; have q7 := fl_le c j; have q8 := fl_le (opW d' a c) j
    simp only [b'] at q2 ⊢
    generalize fl a j = fa at *; generalize fl c j = fc at *; generalize fl (opW d' a c) j = fo at *
    interval_cases fa <;> interval_cases fc <;> cases ka <;> cases kc <;> simp at q2 q3 q5 ⊢ <;> omega
  have e1 : z + (a.c &&& c.c) - (opW d' a c).c = pk P.length (fun j => 16 + b j - cnt v j + fl a j * fl c j - fl (opW d' a c) j) := by
    rw [hz, fl_and wa, fl_pk wo, pk_add, pk_sub]
    intro j hj; have := num j hj; omega
  refine ⟨⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · rw [e1]
    have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have ec : (bif kc then c.c else 0) = pk P.length (fun j => bif kc then fl c j else 0) := by
      cases kc
      · simp [pk]
      · exact fl_pk wc
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    have le2 : ∀ j, (bif kc then fl c j else 0) ≤ 1 := fun j => by cases kc <;> simp [fl_le]
    rw [ea, ec, pk_sub, pk_sub]
    · exact pk_congr fun j hj => (num j hj).2.2.2.2
    · intro j hj; have := num j hj; have := le1 j; have := le2 j; omega
    · intro j hj; have := num j hj; have := le1 j; omega
  · rw [e1, nl, X.hg, pk_guard]; · simp
    intro j hj; have := num j hj; omega
lemma drop_ok {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S')
    (ha : a ∈ v) (hk : a.s ∉ S')
    (hu : (Nat.land (sp (pos' t) l a.s) (wst (pos' t) l v)).testBit i = true) :
    bif d' then c.s.testBit (NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : X := ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma modeF_false {n e : ℕ} {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {a c : W} {da dc : ℕ} {s x y : ℕ}
    (hf : modeF n e h a c da dc s x y = false) (h0 : ¬ n ≤ e → da = 0 ∧ dc = 0) (h1 : ¬ n + 1 ≤ e → da = 0 ∨ dc = 0) :
    h a c da dc s x y = false := by
  unfold modeF at hf
  cases b1 : Nat.ble n e with
  | false =>
    have := h0 (fun h => by rw [Nat.ble_eq_true_of_le h] at b1; simp at b1)
    rw [b1, this.1, this.2] at hf; rw [this.1, this.2]; exact hf
  | true =>
    cases b2 : Nat.ble (Nat.succ n) e with
    | false =>
      have := h1 (fun h => by rw [Nat.ble_eq_true_of_le h] at b2; simp at b2)
      have h3 : Nat.beq (Nat.mul da dc) 0 = true := by
        change Nat.beq (da * dc) 0 = true
        rcases this with h | h <;> simp [h]
      rw [b1, b2] at hf
      simp only [Bool.cond_true, Bool.cond_false, f1, h3] at hf
      exact hf
    | true => rw [b1, b2] at hf; exact hf
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s NN)
  else Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o)
lemma pair_false {h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pair h (mkx d l o a) (mkx d l o c) = false) (d' : Bool) :
    h a c (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pair, mkx, bR] at hp
  rw [Bool.cond_eq_ite] at hp
  split_ifs at hp with h1
  · cases d'
    · rw [Bool.not_eq_true] at h1; exact h1
    · exact hp
lemma put_eq {m : ℕ} {o : W} {v : List W} (ho : Nat.lor o.a o.b = o.c) (hr : o.r = 0) (h0 : o.s ≠ 0) (h1 : o.s ≠ m) (h : List W → Bool) :
    put m o.s o.a o.b v h = ins o v h := by
  have hb0 : Nat.beq o.s 0 = false := Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h)
  have hb1 : Nat.beq o.s m = false := Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h)
  simp only [put, st_eq, hb0, hb1, ho]
  rw [← hr]
lemma mid_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : mid f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kids (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [mid, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  exact h
lemma kids_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kids ch e n z x y a c oa oc mk = false) :
    (oa = true → oc = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kids, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; subst h1 h2
    revert h; simp only [Bool.cond_true]; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) = false
    cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;> simp
  · intro h1 h2; subst h1; rw [b1 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) = false
    cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;> simp
  · intro h2; rw [b2 h2] at h
    revert h; simp only [Bool.cond_true]
    change _ → ch mk (Nat.sub (Nat.sub z x) y) = false
    cases ch mk (Nat.sub (Nat.sub z x) y) <;> simp
lemma Live.rel {R' : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} (h : Live R m T k t S) (hR : ∀ d a b, Al R d a b → Al R' d a b) : Live R' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hR _ _ _ hal) ih
lemma Bi.rel {R' : ℕ → ℕ} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hR : ∀ d a b, Al R d a b → Al R' d a b) : Bi R' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hR _ _ _ hal⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
    (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
  cases hrect : rect (pos' t) l (wst (pos' t) l r) r [] with
  | false => rfl
  | true =>
      exfalso
      have hs := hm.size
      have hcard := hr.rep.card
      have hpos : 0 < S.card := hm.1.pos
      have htight : S.card + t = k' + 1 := by omega
      rw [rect_false (o := wst (pos' t) l r)] at hrect; · simp at hrect
      · have hnd : r.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hr.rep.1
        refine hnd.imp_of_mem fun {a b} ha hb' hab => ?_
        by_contra hhit
        rw [Bool.not_eq_false] at hhit
        obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec hhit
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (NN + j1) = w.testBit (NN + j2) := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
        have ma := hr.rep.mem.2 ⟨a, ha, rfl⟩
        have mb := hr.rep.mem.2 ⟨b, hb', rfl⟩
        rcases Nat.eq_zero_or_pos t with rfl | htp
        · have hd' : pos' 0 = false := by simp [pos']
          rw [hd'] at u1 u2 u3 u4
          exact rect0 hm.1 hm.2 (by simpa using htight) (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
        · have hd' : pos' t = true := by simp [pos', htp]
          rw [hd'] at u1 u2 u3 u4
          exact rect1 hm.1 hm.2 htight (X.lg _ l1).1 (X.lg _ l2).1 (X.lg _ l3).1 (X.lg _ l4).1
            ma mb hab g1 g2 u1 u2 u3 u4
      · simp
lemma hit_ht {k z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg segY_ok (hu b.s) hs2 y2
  obtain ⟨l1, u1, p1⟩ := uq ha a3
  obtain ⟨l2, u2, p2⟩ := uq hb b3
  obtain ⟨l3, u3, p3⟩ := uq ha c3
  obtain ⟨l4, u4, p4⟩ := uq hb d3
  refine ⟨i1, i2, j1, j2, (X.lg _ l1).1, (X.lg _ l2).1, (X.lg _ l3).1, (X.lg _ l4).1, ?_, ?_, u1, u2, u3, u4, by rw [p1, p3], by rw [p2, p4]⟩
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
  · intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
    exact (hr.good w' hw').2 _ _ ⟨s', hs2, c1, c2, d1, d2⟩ l3 l4
end sound
lemma hits_true {f : ℕ} {m : List ℕ} (h : hits f m = true) : ∃ e ∈ m, hit f e = true := by
  by_contra hc
  push Not at hc
  rw [hits_false fun e he => by simpa using hc e he] at h; simp at h
lemma app_mem {x y : List ℕ} {e : ℕ} : e ∈ app x y ↔ e ∈ x ∨ e ∈ y := by
  induction x with
  | nil => simp [app]
  | cons a x ih =>
    change e ∈ a :: app x y ↔ _
    simp only [List.mem_cons, ih, or_assoc]
def CmOk (F : W → ℕ) (r : List W) (col : ℕ → ℕ) (c : Cm) : Prop := ∃ κ ≤ 1, (∀ e ∈ c.a, ∃ w ∈ r, F w = e ∧ col w.s = κ) ∧
  ∀ e ∈ c.b, ∃ w ∈ r, F w = e ∧ col w.s = 1 - κ
lemma join_false {F : W → ℕ} {r : List W} {col : ℕ → ℕ} {k : List Cm → Bool} {w : W} (hw1 : col w.s ≤ 1)
    (hh : ∀ w' ∈ r, hit (F w) (F w') = true → col w.s ≠ col w'.s)
    (hk : ∀ cs, (∀ c ∈ cs, CmOk F (w :: r) col c) → k cs = false) : ∀ (cs : List Cm) (S O : List ℕ) (Q : List Cm),
    (∀ c ∈ cs, CmOk F r col c) → (∀ c ∈ Q, CmOk F (w :: r) col c) → (∀ e ∈ S, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = col w.s) →
    (∀ e ∈ O, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = 1 - col w.s) → join k (F w) cs S O Q = false := by
  intro cs
  induction cs with
  | nil =>
    intro S O Q _ hQ hS hO
    refine hk _ fun c hc => ?_
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact ⟨col w.s, hw1, hS, hO⟩
    · exact hQ c hc
  | cons c cs ih =>
    intro S O Q hcs hQ hS hO
    have hc := hcs c (by simp)
    have hcs' : ∀ c ∈ cs, CmOk F r col c := fun c' h => hcs c' (by simp [h])
    obtain ⟨κ, hκ, ha, hb⟩ := hc
    have e : join k (F w) (c :: cs) S O Q = bif hits (F w) c.a then (bif hits (F w) c.b then true else join k (F w) cs (app c.b S) (app c.a O) Q)
        else (bif hits (F w) c.b then join k (F w) cs (app c.a S) (app c.b O) Q else join k (F w) cs S O (c :: Q)) := by
      change (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs S O (c :: Q)) (join k (F w) cs (app c.a S) (app c.b O) Q) (hits (F w) c.b))
        (Bool.rec (motive := fun _ => Bool) (join k (F w) cs (app c.b S) (app c.a O) Q) true (hits (F w) c.b)) (hits (F w) c.a) : Bool) = _
      rw [bR, bR, bR]
    rw [e]
    have hA : hits (F w) c.a = true → κ = 1 - col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := ha x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have hB : hits (F w) c.b = true → κ = col w.s := by
      intro h
      obtain ⟨x, hx, hhx⟩ := hits_true h
      obtain ⟨w', hw', e1, e2⟩ := hb x hx
      have := hh w' hw' (by rw [e1]; exact hhx)
      omega
    have up : ∀ {κ' : ℕ} {L : List ℕ}, (∀ e ∈ L, ∃ w' ∈ r, F w' = e ∧ col w'.s = κ') → ∀ e ∈ L, ∃ w' ∈ w :: r, F w' = e ∧ col w'.s = κ' := by
      intro κ' L h e he
      obtain ⟨w', h1, h2⟩ := h e he
      exact ⟨w', by simp [h1], h2⟩
    cases h1 : hits (F w) c.a with
    | true =>
      have k1 := hA h1
      cases h2 : hits (F w) c.b with
      | true => have k2 := hB h2; omega
      | false =>
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
    | false =>
      cases h2 : hits (F w) c.b with
      | true =>
        have k2 := hB h2
        simp only [cond_true, cond_false]
        refine ih _ _ _ hcs' hQ ?_ ?_
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up ha e h; exact ⟨w', q1, q2, by omega⟩
          · exact hS e h
        · intro e he
          rcases app_mem.1 he with h | h
          · obtain ⟨w', q1, q2, q3⟩ := up hb e h; exact ⟨w', q1, q2, by omega⟩
          · exact hO e h
      | false =>
        simp only [cond_false]
        refine ih _ _ _ hcs' ?_ hS hO
        intro c' hc'
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨κ, hκ, up ha, up hb⟩
        · exact hQ c' hc'
lemma bip_aux {l o : ℕ} {col : ℕ → ℕ} : ∀ (v r : List W) (cs : List Cm), (∀ w ∈ v, col w.s ≤ 1) → (∀ c ∈ cs, CmOk (flag false l o) r col c) →
    (∀ w ∈ v, ∀ w' ∈ r, hit (flag false l o w) (flag false l o w') = true → col w.s ≠ col w'.s) →
    v.Pairwise (fun a b => hit (flag false l o b) (flag false l o a) = true → col b.s ≠ col a.s) → bip l o v cs = false := by
  intro v
  induction v with
  | nil => intros; rfl
  | cons w v ih =>
    intro r cs h1 h2 h3 h4
    rw [List.pairwise_cons] at h4
    change join (bip l o v) (flag false l o w) cs [flag false l o w] [] [] = false
    refine join_false (F := flag false l o) (h1 w (by simp)) (h3 w (by simp)) ?_ cs _ _ _ h2 (by simp) ?_ (by simp)
    · intro cs' hcs'
      refine ih (w :: r) cs' (fun x hx => h1 x (by simp [hx])) hcs' ?_ h4.2
      intro x hx w' hw'
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · exact h4.1 x hx
      · exact h3 x (by simp [hx]) w' hw'
    · intro e he
      simp only [List.mem_singleton] at he
      exact ⟨w, by simp, he.symm, rfl⟩
lemma anyE_false : ∀ {m : List ℕ}, m.Pairwise (fun p q => hit p q = false) → anyE m = false := by
  intro m
  induction m with
  | nil => intro _; rfl
  | cons f t ih =>
    intro h
    rw [List.pairwise_cons] at h
    change (Bool.rec (motive := fun _ => Bool) (anyE t) true (hits f t) : Bool) = false
    rw [bR, hits_false h.1, ih h.2]; rfl
lemma rmF_eq (F : W → ℕ) (f : ℕ) (t : List W) : rmF f (t.map F) = (t.eraseP (fun q => hit f (F q))).map F := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    change (Bool.rec (motive := fun _ => List ℕ) (F x :: rmF f (t.map F)) (t.map F) (hit f (F x)) : List ℕ) = _
    rw [List.eraseP_cons]
    cases h : hit f (F x)
    · simp [ih]
    · simp
lemma eraseP_not {α : Type} {p : α → Bool} {a : α} : ∀ {t : List α}, t.Nodup → a ∈ t → p a = true → (∀ x ∈ t, p x = true → x = a) → a ∉ t.eraseP p := by
  intro t
  induction t with
  | nil => intro _ h; simp at h
  | cons x t ih =>
    intro hn ha hp hx
    rw [List.nodup_cons] at hn
    rw [List.eraseP_cons]
    cases h : p x
    · have hax : a ≠ x := fun e => by rw [← e, hp] at h; simp at h
      simp only [Bool.false_eq_true, if_false, List.mem_cons, not_or]
      simp only [List.mem_cons] at ha
      exact ⟨hax, ih hn.2 (ha.resolve_left hax) hp fun y hy => hx y (by simp [hy])⟩
    · have := hx x (by simp) h
      subst this
      simpa using hn.1
lemma star_false {F : W → ℕ} {a : W} : ∀ {v : List W}, v.Nodup → star (v.map F) = false →
    ∃ p q : W, [p, q].Sublist v ∧ hit (F p) (F q) = true ∧ p ≠ a ∧ q ≠ a := by
  intro v hn hst
  by_contra hno
  push Not at hno
  have bad : ∀ p q : W, [p, q].Sublist v → hit (F p) (F q) = true → p = a ∨ q = a := by
    intro p q h1 h2
    by_cases h : p = a
    · exact Or.inl h
    · exact Or.inr (hno p q h1 h2 h)
  clear hno
  have key : star (v.map F) = true := by
    clear hst
    induction v with
    | nil => rfl
    | cons w t ih =>
      rw [List.nodup_cons] at hn
      have bt : ∀ p q : W, [p, q].Sublist t → hit (F p) (F q) = true → p = a ∨ q = a := fun p q h => bad p q (h.cons w)
      have e : star ((w :: t).map F) = bif hits (F w) (t.map F) then (bif anyE (t.map F) then (bif hits (F w) (rmF (F w) (t.map F)) then false else
          (bif anyE (rmF (F w) (t.map F)) then false else true)) else true) else star (t.map F) := by
        change (Bool.rec (motive := fun _ => Bool) (star (t.map F)) (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool)
          (Bool.rec (motive := fun _ => Bool) true false (anyE (rmF (F w) (t.map F)))) false (hits (F w) (rmF (F w) (t.map F)))) (anyE (t.map F))) (hits (F w) (t.map F)) : Bool) = _
        rw [bR, bR, bR, bR]
      rw [e]
      have edge : ∀ u : List W, u.Sublist t → a ∉ u → anyE (u.map F) = false := by
        intro u hu ha
        refine anyE_false ?_
        rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
        intro p q hpq
        by_contra hc
        rw [Bool.not_eq_false] at hc
        have hm : ∀ x ∈ [p, q], x ∈ u := fun x hx => hpq.subset hx
        rcases bt p q (hpq.trans hu) hc with rfl | rfl
        · exact ha (hm p (by simp))
        · exact ha (hm q (by simp))
      cases h1 : hits (F w) (t.map F) with
      | false => rw [cond_false]; exact ih hn.2 bt
      | true =>
        rw [cond_true]
        have part : ∀ q ∈ t, hit (F w) (F q) = true → w = a ∨ q = a := fun q hq h => bad w q ((List.singleton_sublist.2 hq).cons_cons w) h
        by_cases hwa : w = a
        · subst hwa
          rw [edge t (List.Sublist.refl t) hn.1]; rfl
        · have pa : ∀ q ∈ t, hit (F w) (F q) = true → q = a := fun q hq h => (part q hq h).resolve_left hwa
          obtain ⟨x, hx, hhx⟩ := hits_true h1
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          have hqa := pa q hq hhx
          subst hqa
          have hna : q ∉ t.eraseP (fun q => hit (F w) (F q)) := eraseP_not hn.2 hq hhx pa
          rw [rmF_eq, edge _ List.eraseP_sublist hna]
          have : hits (F w) ((t.eraseP (fun q => hit (F w) (F q))).map F) = false := by
            refine hits_false fun e he => ?_
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 he
            by_contra hc
            rw [Bool.not_eq_false] at hc
            have hyt : y ∈ t := List.eraseP_sublist.subset hy
            exact hna (pa y hyt hc ▸ hy)
          rw [this]
          cases anyE (t.map F) <;> rfl
  rw [key] at hst; simp at hst
lemma flk_eq (l o : ℕ) (v : List W) : ∀ k, flk l o v k = k (v.map (flag false l o)) := by
  induction v with
  | nil => intro k; rfl
  | cons w v ih =>
    intro k
    change flk l o v (fun r => k (flag false l o w :: r)) = _
    rw [ih]; rfl
def NK (R : ℕ → ℕ) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live R m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK R m T k' t S := by
  rw [flk_eq] at hst
  have hsz := hm.size
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht NN m T (pos' t) S p q := by
    intro a ha
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 ha
    obtain ⟨p, q, hpq, hh, h1, h2⟩ := star_false (F := flag false l (wst (pos' t) l v)) (a := wa) hs.rep.nodup hst
    have hp : p ∈ v := hpq.subset (by simp)
    have hq : q ∈ v := hpq.subset (by simp)
    have hne : p ≠ q := by
      have := hs.rep.nodup.sublist hpq
      simpa using this
    refine ⟨p.s, q.s, hs.rep.mem.2 ⟨p, hp, rfl⟩, hs.rep.mem.2 ⟨q, hq, rfl⟩, fun e => hne (hs.rep.inj hp hq e), fun e => h1 (hs.rep.inj hp hwa e),
      fun e => h2 (hs.rep.inj hq hwa e), hit_ht X hs hp hq hh⟩
  have he : ∀ t', pos' t = true ∨ t = t' → pos' t = true ∨ t' = 0 := by
    intro t' h
    rcases h with h | h
    · exact Or.inl h
    · subst h
      rcases Nat.eq_zero_or_pos t with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [pos', h])
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi R d a b S S1 → Live R m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
    rintro d a b S1 k0 rfl hb hl U rfl rfl ha hbU
    have hab := hb.1
    have hfS : op d a b ∉ insert a (insert b U) := fun h => hb.fresh hl hm.2 (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by simp [h])
    have eS : insert a (insert b U) = insert b U := Finset.insert_eq_of_mem (by simp [ha])
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS, Finset.card_insert_of_notMem hbU] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have := ht_bi hab (Or.inr rfl) hl hp hq (fun e => absurd e hpa) (fun _ => hbU) (fun e => absurd e hqa) (fun _ => hbU) hh
    have m1 := phi_mem (g := op d a b) hp
    have m2 := phi_mem (g := op d a b) hq
    have hne : (if p = a ∨ p = b then op d a b else p) ≠ (if q = a ∨ q = b then op d a b else q) := by
      simp only [hpa, hqa, false_or]
      have h1' : p = b ∨ p ∈ U := by simp at hp; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; tauto
      split_ifs with r s s
      · exact absurd (r.trans s.symm) hpq
      · intro e; exact hf (e ▸ h2'.resolve_left s)
      · intro e; exact hf (e ▸ h1'.resolve_left r)
      · exact hpq
    have k1 := h3 _ m1 _ m2 hne this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
  constructor
  · intro d a b S1 k0 hk' hb hl
    by_contra hc
    obtain ⟨hab, U, e1, e2, hal⟩ := id hb
    have hfS : op d a b ∉ S := fun h => hb.fresh hl (by rw [← hk']; exact hm.2) (sub_C _ _ (by simpa using h))
    have hf : op d a b ∉ U := fun h => hfS (by rw [e1]; simp [h])
    have hs1 := (hb.min hl (by rw [← hk']; exact hm.2)).size.1
    have hcS1 : S1.card = U.card + 1 := by rw [e2, Finset.card_insert_of_notMem hf]
    by_cases ha : a ∈ U
    · by_cases hbU : b ∈ U
      · have : S = U := by rw [e1, Finset.insert_eq_of_mem hbU, Finset.insert_eq_of_mem ha]
        rw [this] at hx; omega
      · exact kb d a b S1 k0 hk' hb hl U e1 e2 ha hbU
    · by_cases hbU : b ∈ U
      · exact kb d b a S1 k0 hk' hb.symm hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
      · have : S.card = U.card + 2 := by
          rw [e1, Finset.card_insert_of_notMem (by simp [hab, ha]), Finset.card_insert_of_notMem hbU]
        omega
  · rintro a S1 k0 t0 rfl rfl hu hl
    by_contra hc
    obtain ⟨U, rfl, rfl⟩ := id hu
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm.2 (sub_C _ _ (by simp [h]))
    have ha : a ∈ U := by
      by_contra ha
      rw [Finset.card_insert_of_notMem hf, Finset.card_insert_of_notMem ha] at hc; omega
    have eS : insert a U = U := Finset.insert_eq_of_mem ha
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
    rw [Finset.card_insert_of_notMem hf] at h1
    rw [eS] at hx
    obtain ⟨p, q, hp, hq, hpq, hpa, hqa, hh⟩ := av a (by simp)
    have hpos : pos' (t0 + 1) = true := by simp [pos']
    rw [hpos] at hh
    have := ht_un hp hq (fun e => absurd e hpa) (fun e => absurd e hqa) hh
    simp only [hpa, hqa, if_false] at this
    have m1 : p ∈ insert (a ^^^ m) U := by rw [eS] at hp; simp [hp]
    have m2 : q ∈ insert (a ^^^ m) U := by rw [eS] at hq; simp [hq]
    have k1 := h3 _ m1 _ m2 hpq this
    have c1 := h2 _ m1; have c2 := h2 _ m2
    omega
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) := by
  have hsz := hm.size
  have hcard := hs.rep.card
  have e : ∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = bif Nat.beq v.length (k + 1 - t) then (bif rect (pos' t) l (wst (pos' t) l v) v [] then false else F 0) else
      (bif Nat.beq (v.length + 1) (k + 1 - t) then (bif bip l (wst (pos' t) l v) v [] then false else
        (bif flk l (wst (pos' t) l v) v star then F 0 else F 1)) else F 0) := by
    intro F
    change (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flk l (wst (pos' t) l v) v star)) false
        (bip l (wst (pos' t) l v) v [])) (Nat.beq (v.length + 1) (k + 1 - t)))
      (Bool.rec (motive := fun _ => Bool) (F 0) false (rect (pos' t) l (wst (pos' t) l v) v [])) (Nat.beq v.length (k + 1 - t)) : Bool) = _
    rw [bR, bR, bR, bR, bR]
  cases h1 : Nat.beq v.length (k + 1 - t) with
  | true =>
    have h1' := Nat.eq_of_beq_eq_true h1
    have hr := rect_ok X hs hm hk (by omega)
    exact ⟨0, fun F => by rw [e, h1, hr]; rfl, Or.inl rfl⟩
  | false =>
    cases h2 : Nat.beq (v.length + 1) (k + 1 - t) with
    | false => exact ⟨0, fun F => by rw [e, h1, h2]; rfl, Or.inl rfl⟩
    | true =>
      have h2' := Nat.eq_of_beq_eq_true h2
      have hbip : bip l (wst (pos' t) l v) v [] = false := by
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hm.1 hm.2 (by
          rcases Nat.eq_zero_or_pos t with h | h
          · exact Or.inr h
          · exact Or.inl (by simp [pos', h]))
        refine bip_aux (col := f) v [] [] ?_ (by simp) (by simp) ?_
        · intro w hw
          have := q2 w.s (hs.rep.mem.2 ⟨w, hw, rfl⟩); omega
        · have hnd : v.Pairwise (fun a b => a.s ≠ b.s) := List.pairwise_map.1 hs.rep.1
          refine hnd.imp_of_mem fun {a b} ha hb hab hh => ?_
          exact q3 b.s (hs.rep.mem.2 ⟨b, hb, rfl⟩) a.s (hs.rep.mem.2 ⟨a, ha, rfl⟩) (Ne.symm hab) (hit_ht X hs hb ha hh)
      cases h3 : flk l (wst (pos' t) l v) v star with
      | true => exact ⟨0, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inl rfl⟩
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hs hm (by omega) h3⟩⟩
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k z v S) (hl : Live R m T k' t S)
    (h : cv (pos' t) l v b = false) : b = false := by
  have hcov : Nat.beq (cov (pos' t) l v) l = true := by
    rw [Nat.beq_eq]
    apply Nat.eq_of_testBit_eq; intro i
    cases hli : l.testBit i with
    | false =>
      by_contra hc
      obtain ⟨w, _, hw⟩ := (cov_bit _ _ _ _).1 (by simpa using hc)
      rw [sp_bit, hli] at hw; simp at hw
    | true =>
      rw [cov_bit]
      obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
      obtain ⟨w, hw, hs1⟩ := hl.cov m1 m2 t1 t2
      obtain ⟨w', hw', rfl⟩ := hs.rep.mem.1 hw
      exact ⟨w', hw', by rw [sp_bit, hli, hs1]; rfl⟩
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma gate_sound {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hpos := hl.pos
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pair_false hp d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i
      rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by
    rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep hb.symm hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hv2 : 2 ≤ v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := by
      intro x hx; simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rwa [Finset.card_pair hb.1] at h2
  have hpr : Nat.pred v.length + 1 = v.length := by simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l k (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s1).2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kids_false hmid).2.2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).2.2.1 (b0 (fa q1)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hmid := mid_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kids_false hmid).1 (b0 (fa q1)) (b0 (fc q2)))
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k (z - a.c - (bif ka then a.c else 0)) r S' := by
  obtain ⟨b, hb15, hcl, hz⟩ := hs.bud
  have hle := cnt_le X hs.rep hs.wok hcl hm (by omega)
  have hfr := hb.fresh hl hm.2
  have hfS : a.s ^^^ m ∉ S := fun h => hfr (sub_C _ _ (by simpa using h))
  have wa := hs.wok a ha
  have haS : a.s ∈ S := hb.sub.1
  have wo : WOk P (notW m a) := by
    refine ⟨wa.pb, wa.pa, by rw [Nat.or_comm]; exact wa.ec, fun j hj h => ?_, fun j hj h => ?_⟩
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.cb j hj h]; simp
    · change (a.s ^^^ m) &&& _ = _
      rw [and_neg (X.hP j hj).1, wa.ca j hj h]; simp
  have hov : ((notW m a :: v).map W.s).Nodup := by
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => hfS ?_, hs.rep.1⟩
    rw [← hs.rep.2]; simpa [notW] using hm
  have hov2 : ∀ x, x ∈ (notW m a :: v).map W.s ↔ x = a.s ^^^ m ∨ x ∈ S := fun x => by
    rw [← hs.rep.2]; simp [notW]
  have hS' : ∀ x, x ∈ S' ↔ x = a.s ^^^ m ∨ (x ∈ S ∧ (x = a.s → ka = true)) := by
    intro x
    obtain ⟨U, e1, e2⟩ := hb
    rw [e2, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · refine Or.inr ⟨by rw [e1]; simp [h], ?_⟩
        rintro rfl; rw [hka, e2]; simp [h]
    · rintro (h | ⟨h, f1⟩)
      · exact Or.inl h
      · rw [e1] at h; simp only [Finset.mem_insert] at h
        rcases h with h | h
        · have := f1 h; rw [hka, decide_eq_true_eq, e2, Finset.mem_insert] at this; rw [h]; exact this
        · exact Or.inr h
  have hne : a.s ≠ a.s ^^^ m := fun e => hfS (e ▸ haS)
  have hrep : Rep r S' := by
    cases hkk : ka with
    | true =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      refine ⟨hn, Finset.ext fun x => ?_⟩
      rw [List.mem_toFinset, (hsh.map W.s).mem_iff, hov2, hS']; simp
    | false =>
      rw [hkk] at hsh hS'
      have hn := (hsh.map W.s).nodup_iff.2 hov
      simp only [List.map_cons, List.nodup_cons] at hn
      refine ⟨hn.2, Finset.ext fun x => ?_⟩
      have hx := (hsh.map W.s).mem_iff (a := x)
      rw [hov2] at hx; simp only [List.map_cons, List.mem_cons] at hx
      rw [List.mem_toFinset, hS']
      constructor
      · intro h1
        rcases hx.1 (Or.inr h1) with e | e
        · exact Or.inl e
        · exact Or.inr ⟨e, fun e => absurd (e ▸ h1) hn.1⟩
      · rintro (e | ⟨e, f1⟩)
        · exact (hx.2 (Or.inl e)).resolve_left fun e' => hne (e'.symm.trans e)
        · exact (hx.2 (Or.inr e)).resolve_left fun e' => by simpa using f1 e'
  have hmem : ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
    intro w hw
    have : w ∈ notW m a :: v := by
      cases hkk : ka <;> rw [hkk] at hsh
      · exact List.Perm.subset hsh (by simp [hw])
      · exact List.Perm.subset hsh hw
    simpa using this
  have hcnt : ∀ j, cnt r j + (bif ka then 0 else fl a j) = fl a j + cnt v j := by
    intro j
    have ef : fl (notW m a) j = fl a j := rfl
    cases hkk : ka <;> rw [hkk] at hsh
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
    · have := cnt_perm hsh j; simp only [cnt_cons, ef] at this; simp; omega
  have hwok : ∀ w ∈ r, WOk P w := fun w hw => (hmem w hw).elim (fun e => e ▸ wo) (hs.wok w)
  have hgood : ∀ w ∈ r, Good l w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · have hg := hs.good a ha
      refine ⟨fun i j h h1 h2 => ?_, fun i j h h1 h2 => ?_⟩
      · change (a.s ^^^ m).testBit i = (a.s ^^^ m).testBit j
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.1 i j h h1 h2, (X.lg i h1).1.1, (X.lg j h2).1.1]
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  let b' : ℕ → ℕ := fun j => b j - fl a j
  have hcl' : Cl P T k b' S' := by
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol)
      have : fl a j = 1 := by simp [fl, hkill]
      omega
    · refine hcl j hj (q + 1) ?_ (hb.im (X.hP j hj).1 hsol)
      have e1 : fl a j = 0 := by simp [fl, hkill]
      omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    conv_lhs => rw [fl_pk wa]
    rw [pk_sub, pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
    · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st (Nat.sub z w.c) (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) (z - a.c) else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq
  rw [hins] at h
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c - a.c) <;> simp
    exact ⟨_, _, child_sound X (fun h => rfl) hst hmin hk h, hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) (z - a.c) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
lemma scan_false {p : X → Bool} {xs : List X} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (scan p r) true (p a) : Bool) = false at h
    rw [bR] at h
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · revert h; cases p c <;> simp
    · refine ih ?_ c hc
      revert h; cases scan p r <;> simp
lemma pairs_false {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairs h r) true (scan (h a) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · apply scan_false; revert hp; cases scan (h a) r <;> simp
    · apply ih; revert hp; cases pairs h r <;> simp
lemma beq_f {x y : ℕ} (h : x ≠ y) : Nat.beq x y = false := Bool.eq_false_iff.2 fun h' => h (Nat.eq_of_beq_eq_true h')
lemma pairsP_false {h : X → X → Bool} {xs : List X} {q : ℕ} {a c : X} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : X → X → Bool} {xs : List X} {q q' : ℕ} {a c : X} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List X} {a : X} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List X) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : X → X → Bool} {xs : List X} (hp : pairs h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : L_meta_32784.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : X → X → Bool} {xs : List X} (hp : pairsN h xs = false) {a c : X} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
    (hr : a.w.r = 0 ∨ c.w.r = 0) : h a c = false ∨ h c a = false := by
  simp only [pairsN, bR] at hp
  cases h1 : pairs h (fr xs) with
  | true => rw [h1] at hp; simp at hp
  | false =>
    rw [h1, cond_false] at hp
    by_cases hra : a.w.r = 0
    · by_cases hrc : c.w.r = 0
      · exact pairs_any h1 (fr_mem ha hra) (fr_mem hc hrc) hne
      · exact Or.inl (scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc))
    · have hrc := hr.resolve_left hra
      exact Or.inr (scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra))
def Cod (R : ℕ → ℕ) (v : List W) : Prop := ∀ w ∈ v, w.r = 0 ∨ w.r = R w.s
def RR (R : ℕ → ℕ) : Prop := ∀ d a b, R a ≠ 0 → R b ≠ 0 → ¬ Al R d a b
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s => nots (fun q' z v => cv (pos' s) l v (tst (pos' s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos' s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)))) m g (k - s - y) v.length z 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cv (pos s) l v (tst (pos s) l (k - 1 - s) v (fun y =>
        node (F (k - 3) s) (pos s) l m g (k - 2 - s - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s - y) v.length z (q + 1) v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi R d a b S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK R m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live R m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK R m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_32784.X → L_meta_32784.X → Bool) → List L_meta_32784.X → Bool}
    (hs : StOk P T l (k + 1) z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min R m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK R m T k' t S)) → False := by
  intro k' hk hm hy
  obtain ⟨hA, hN⟩ := mv_false F l m g k t z v y h
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with ⟨_, h⟩ | h
    · exact Or.inl h
    · exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw
    rcases hr w hw with h | h
    · exact Or.inl (by rw [h]; rfl)
    · exact hv w h
  rcases first_move k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg L_meta_32784.X.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : a.r = R a.s := (hcod a ha).resolve_left hc'.1
        have h2 : c.r = R c.s := (hcod c hc).resolve_left hc'.2
        have g1 : a.r ≠ 0 := hc'.1
        have g2 : c.r ≠ 0 := hc'.2
        rw [← hax, ← hcy] at hal
        exact hR _ _ _ (by rw [← h1]; exact g1) (by rw [← h2]; exact g2) hal) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X hR ih hs hcod hlen hy k' hk hm hyk
end sound
lemma Live.W {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live R m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol Z0 m T k Q := hl.sol.mono le_rfl hQ
lemma front {m T : ℕ} (hR : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {k t : ℕ} {S : Finset ℕ} (hl : Live Z0 m T k t S)
    (hm : ∀ q < k, ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live R m T k t S ∨ ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ Bi Z0 d a b S S1 ∧ Live Z0 m T k0 t S1 := by
  induction hl with
  | stop => exact Or.inl .stop
  | @un k t a U hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : a ^^^ m ∉ C m (Q ∪ ((insert a U : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : a ^^^ m ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (a ^^^ m) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
    · exact Or.inl (.un h)
    · have nx : x ≠ a ^^^ m := fun e => hx (e ▸ hfR)
      have ny : y ≠ a ^^^ m := fun e => hy (e ▸ hfR)
      have hmV : a ^^^ m ∈ V := by
        have : a ^^^ m ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase (a ^^^ m))) := by
        ext z
        by_cases hz : z = a ^^^ m
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert (a ^^^ m) U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hb0 : Bi Z0 d0 a b (insert a (insert b U)) (insert (op d0 a b) U) := ⟨hab, U, rfl, rfl, hal0⟩
    by_cases hW : R a ≠ 0 ∧ R b ≠ 0
    · exact Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hb0, hl⟩
    have hal : Al R d0 a b := hR _ _ _ (by
      by_contra hc; push Not at hc; exact hW hc)
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfa : op d0 a b ≠ a := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfb : op d0 a b ≠ b := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol Z0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (al0 _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, ⟨hxy, V, e1, rfl, hal'⟩, hl1⟩
    · exact Or.inl (.bi hab hal h)
    · set o := op d0 a b with ho
      have nx : x ≠ o := fun e => hx (e ▸ hfR)
      have ny : y ≠ o := fun e => hy (e ▸ hfR)
      have hmV : o ∈ V := by
        have : o ∈ insert x (insert y V) := by rw [← e1]; simp
        simp at this
        rcases this with h | h | h
        · exact absurd h.symm nx
        · exact absurd h.symm ny
        · exact h
      have eU : U = insert x (insert y (V.erase o)) := by
        ext z
        by_cases hz : z = o
        · subst hz
          simp [hfU, Ne.symm nx, Ne.symm ny]
        · have : z ∈ insert o U ↔ z ∈ insert x (insert y V) := by rw [e1]
          simp only [Finset.mem_insert, hz, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and] at this ⊢
          exact this
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy,
        ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, hal'⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
      · ext z; simp only [Finset.mem_insert]
        constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
      · refine .bi hab hal0 ?_
        have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
          rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
        rw [this]; exact hl1
lemma Min.Z {m T k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) : Min Z0 m T k t S := ⟨h.1.rel fun d a b _ => al0 d a b, h.2⟩
lemma NK.toR {m T k t : ℕ} {S : Finset ℕ} (h : NK Z0 m T k t S) : NK R m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun d a b _ => al0 d a b) (hl.rel fun d a b _ => al0 d a b),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun d a b _ => al0 d a b)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_32784.X → L_meta_32784.X → Bool) → List L_meta_32784.X → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front hR2 hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma or_false' {a b : Bool} (h : (Bool.rec (motive := fun _ => Bool) b true a : Bool) = false) : a = false ∧ b = false := by
  clear X
  cases a <;> simp_all
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hR hR2 ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr => ⟨pairsS, hy1, fun h hp => ?_⟩
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32784.X.s e))
end sound
def rawP : List ℕ := [(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xfffff00000 64) 0x7ffff8) 64) 0x1ffff007) 64) 0xfc00020082080894) 64) 0x104044c045008980) 64) 0x2080f0448009e08a) 64) 0x410113011402260) 64) 0x4f0490808980000) 64) 0x1151409134131114) 64) 0x51144488b6345412) 64) 0x9a118482542693a) 64) 0x260404c451696c04) 64) 0x7708500007c00000) 64) 0xf800000007fff0) 64) 0x1f03c00001f7800) 64) 0x3e00000001fffc) 64) 0xfbc00077fff6cdb), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1ffff001ffff7f0 64) 0x58) 64) 0x28003800500) 64) 0x42001c2004007) 64) 0xa000e00141) 64) 0x20039c00500000) 64) 0x220a812448240222) 64) 0xa020ab0103580204) 64) 0x524220118a808c4c) 64) 0x128eb81218db8bc) 64) 0x1212a00000000000) 64) 0x3fff00000) 64) 0x3c07bff) 64) 0xe0000000fffc0001) 64) 0xe03dfff70000366e), 0x0, (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1ffffe0000000000 64) 0xfffff000000) 64) 0x1ffff7fc0000000) 64) 0x40104101160) 64) 0x20808b008a011600) 64) 0x411e00890f100114) 64) 0x82022c022804587) 64) 0x8800921011600000) 64) 0x4494424294492445) 64) 0x124ad2924484a428) 64) 0x24a448a553450292) 64) 0x4a32b2cbb2020c04) 64) 0x89211001f0000000) 64) 0x3e03fff800000000) 64) 0x7c07800003df0000) 64) 0xf80fffe00000001) 64) 0xef8000077fffb973), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ffff0000000 64) 0x3ff) 64) 0xff800fffff7ffffb) 64) 0xfc00000000000000) 64) 0x20007c8580) 64) 0xfbe42c042c085808) 64) 0x8421e04008438) 64) 0x3ef90b010b021602) 64) 0x3e423c0085800000) 64) 0x80209b8b19000088) 64) 0x20030300181808b1) 64) 0xb8c082c66396331c) 64) 0xff03030220303048) 64) 0x2204201c001f0000) 64) 0x3ef8000000000007) 64) 0x7bdfff8000000) 64) 0xfbe000000000001) 64) 0xefbdfff00000007c), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1ffff 64) 0xc0000000000003ff) 64) 0xffbfe00000000000) 64) 0x0) 64) 0x80208202600) 64) 0x410130013002601c) 64) 0x8200011000200220) 64) 0x10404c004c009800) 64) 0x1001200026000001) 64) 0x8c70c03e08e48f1) 64) 0xc48c1c2460e130c1) 64) 0x3f08f3007c1803e0) 64) 0x8c403c10c403c111) 64) 0xc41c7c0001f7fff) 64) 0x8000000000000007) 64) 0x7df0000000000000) 64) 0xfbefffefffdfffc) 64) 0x180), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7 64) 0xffff00000001ffff) 64) 0xdffffefffff7f800) 64) 0x0) 64) 0x0) 64) 0x1f47df013800) 64) 0x9c009c0138011) 64) 0xf7d085e0087d0bc0) 64) 0x270027004e004) 64) 0x85c00138000001) 64) 0xf0f8100c010070fe) 64) 0x70fe0387f01fe01) 64) 0xc000800780003c00) 64) 0x1003c003003c0060) 64) 0x300607ddf7c00000) 64) 0x7) 64) 0x7df7bdfffbdf7bff) 64) 0xe000000000000000) 64) 0x3e00), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7 64) 0xffff7ffff7fc0000) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x10741041c000) 64) 0x820e000e001c0001) 64) 0x400060000400c00) 64) 0x2083800380070000) 64) 0x20060001c0000001) 64) 0xff001ff001f07f00) 64) 0x7f0003f8001c0fe) 64) 0xf03f8001fc000) 64) 0xe07c001c07c00181) 64) 0xc07807ddf7df7fff) 64) 0xbefbfffbfff7fff0) 64) 0x0) 64) 0x0) 64) 0xc000)]
def xw (e : ℕ × ℕ) : ℕ := op (decide (e.1 < 8)) (rawP.getD (e.1 % 8) 0) (rawP.getD e.2 0)
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := [(8, 1), (0, 1), (8, 3), (0, 3), (8, 4), (0, 4), (8, 5), (0, 5), (9, 4), (1, 4), (9, 5), (1, 5), (12, 5), (4, 5), (12, 6), (4, 6), (13, 7), (5, 7)]
def rawG : List ℕ := rawL six
def FPM : ℕ := 0xffff
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fffffff)
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i x =>
  let w := rawP.getD i 0
  let other := w >>> NN
  bif Z.testBit i then x ||| ((w ||| other) &&& FULL)
  else bif Z.testBit (8+i) then x ||| (FULL ^^^ ((w &&& (other ||| FPM)) &&& FULL))
  else x) 0
def lz (Z : ℕ) : ℕ := Nat.land AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) NN)
def tz (Z : ℕ) : ℕ := Nat.land TG (mz Z)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG : AA &&& TG = AA := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt : TG < 2 ^ NN := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt : AA < 2 ^ NN := by decide +kernel
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg NN (mz Z) (tz Z) i ∧ AA.testBit i = true := by
  have hA : AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< NN).testBit (NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good : rawG.all (fun w => segsX.all (segGood w 0) && segsY.all (segGood w NN)) = true := by decide +kernel
lemma segGood_eq {w o : ℕ} {s : ℕ × ℕ} (h : segGood w o s = true) {i j : ℕ} (h1 : s.1 < i) (h2 : i < s.2) (h3 : s.1 < j) (h4 : j < s.2) :
    w.testBit (o + i) = w.testBit (o + j) := by
  have key : ∀ i, s.1 < i → i < s.2 → w.testBit (o + i) = ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)).testBit (i - s.1 - 1) := by
    intro i h1 h2
    rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, show o + s.1 + 1 + (i - s.1 - 1) = o + i by omega]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega]
  rw [key i h1 h2, key j h3 h4]
  simp only [segGood, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with h | h <;> rw [h]
  · simp
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
    simp [show i - s.1 - 1 < s.2 - s.1 - 1 by omega, show j - s.1 - 1 < s.2 - s.1 - 1 by omega]
lemma wire_good {w : ℕ} (hw : w ∈ rawG) (Z : ℕ) : Good (lz Z) (w &&& mz Z) := by
  have h := List.all_eq_true.1 raw_good w hw
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨fun i j hij h1 h2 => ?_, fun i j hij h1 h2 => ?_⟩ <;> obtain ⟨s, hs, a1, a2, a3, a4⟩ := hij
  · have := segGood_eq (h.1 s hs) a1 a2 a3 a4
    simp only [Nat.zero_add] at this
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.1, (lz_lg Z j h2).1.1]
  · have := segGood_eq (h.2 s hs) a1 a2 a3 a4
    rw [Nat.testBit_and, Nat.testBit_and, this, (lz_lg Z i h1).1.2.1, (lz_lg Z j h2).1.2.1]
noncomputable section
def pL (L : List ℕ) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun d _ ih => Nat.add (Nat.shiftLeft ih 5) d) L
end
lemma pL_cons (d : ℕ) (L : List ℕ) : pL (d :: L) = 2 ^ 5 * pL L + d := by
  change (pL L <<< 5) + d = _; rw [Nat.shiftLeft_eq]; ring
lemma pL_pk (L : List ℕ) : pL L = pk L.length (fun j => L.getD j 0) := by
  induction L with
  | nil => simp [pL, pk]
  | cons d L ih =>
    rw [pL_cons, ih, pk, pk, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, mul_one, List.getD_cons_zero, List.getD_cons_succ]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, pow_add]; ring
lemma pL_bit {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : ∀ i, (pL L).testBit i = true ↔ (i % 5 = 0 ∧ i / 5 < L.length ∧ L.getD (i / 5) 0 = 1) := by
  induction L with
  | nil => intro i; simp [pL]
  | cons d L ih =>
    intro i
    have hd := h d (by simp)
    have ih := ih fun x hx => h x (by simp [hx])
    rw [pL_cons, Nat.testBit_two_pow_mul_add _ (by omega)]
    split_ifs with hi
    · have : i / 5 = 0 := by omega
      rw [this]
      rcases Nat.eq_zero_or_pos i with rfl | hp
      · interval_cases d <;> simp
      · constructor
        · intro hb
          have : d.testBit i = false := Nat.testBit_lt_two_pow (lt_of_le_of_lt hd (Nat.one_lt_two_pow (by omega)))
          rw [this] at hb; simp at hb
        · intro hb; omega
    · rw [ih, show i / 5 = (i - 5) / 5 + 1 by omega]
      simp only [List.length_cons, List.getD_cons_succ]
      constructor
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
      · rintro ⟨a, b, c⟩; exact ⟨by omega, by omega, c⟩
lemma pL_isPk {L : List ℕ} (h : ∀ d ∈ L, d ≤ 1) : isPk L.length (pL L) := fun i hi => by
  have := (pL_bit h i).1 hi; exact ⟨this.1, this.2.1⟩
def bit01 (b : Bool) : ℕ := bif b then 1 else 0
def mkW (P : List ℕ) (s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), 3⟩
lemma mkW_ok (P : List ℕ) (s : ℕ) : WOk P (mkW P s) := by
  have h01 : ∀ f : ℕ → Bool, ∀ d ∈ P.map (fun n => bit01 (f n)), d ≤ 1 := by
    intro f d hd; simp only [List.mem_map] at hd
    obtain ⟨n, _, rfl⟩ := hd; cases f n <;> simp [bit01]
  have bt : ∀ f : ℕ → Bool, ∀ j < P.length, (pL (P.map fun n => bit01 (f n))).testBit (5 * j) = true → f (P.getD j 0) = true := by
    intro f j hj h
    have h := ((pL_bit (h01 f) _).1 h).2.2
    rw [show 5 * j / 5 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj] at h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    simp at h ⊢
    cases hf : f P[j] <;> simp [bit01, hf] at h ⊢
  refine ⟨?_, ?_, rfl, fun j hj h => ?_, fun j hj h => ?_⟩
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) 0); rwa [List.length_map] at this
  · have := pL_isPk (h01 fun n => Nat.beq (Nat.land s n) n); rwa [List.length_map] at this
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) 0) j hj h)
  · exact Nat.eq_of_beq_eq_true (bt (fun n => Nat.beq (Nat.land s n) n) j hj h)
noncomputable section
def addS (o : W) (v : List W) : List W := List.rec (motive := fun _ => List W) [o]
  (fun w t ih => Bool.rec (motive := fun _ => List W) (w :: ih) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s)) v
def avl (P : List ℕ) (m : ℕ) (L : List ℕ) : List W := List.rec (motive := fun _ => List W) []
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySub (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (cov d l t)) l)) true
    (st (Nat.lor c (sp d l w.s)) fun c => ih c fun r => h (w :: r))) v
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 251
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : X → X → Bool) (xs : List X) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
lemma frc_eq (v : List W) : ∀ h, frc v h = h v := by
  induction v with
  | nil => intro h; rfl
  | cons w v ih =>
    intro h
    change st w.s (fun s => st w.a fun a => st w.b fun b => st w.c fun c => frc v fun r => h (⟨s, a, b, c, w.r⟩ :: r)) = _
    simp only [st_eq]; rw [ih]
lemma anySub_false {d : Bool} {l : ℕ} {v : List W} : ∀ {c : ℕ} {h : List W → Bool}, (∀ i, c.testBit i = true → l.testBit i = true) → anySub d l v c h = false →
    ∀ r, r.Sublist v → (∀ i, l.testBit i = true → c.testBit i = true ∨ (cov d l r).testBit i = true) → h r = false := by
  induction v with
  | nil => intro c h _ hh r hr _; rw [List.sublist_nil.1 hr]; exact hh
  | cons w v ih =>
    intro c h hcl hh r hr hcov
    change (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (anySub d l v c h) (Nat.beq (Nat.lor c (cov d l v)) l)) true
      (st (Nat.lor c (sp d l w.s)) fun c => anySub d l v c fun r => h (w :: r)) : Bool) = false at hh
    rw [bR, bR, st_eq] at hh
    cases h1 : anySub d l v (Nat.lor c (sp d l w.s)) (fun r => h (w :: r)) with
    | true => rw [h1] at hh; simp at hh
    | false =>
      rw [h1, Bool.cond_false] at hh
      have hc2 : ∀ i, (cov d l v).testBit i = true → l.testBit i = true := by
        intro i hi
        obtain ⟨w', _, hw'⟩ := (cov_bit _ _ _ _).1 hi
        rw [sp_bit, Bool.and_eq_true] at hw'; exact hw'.1
      cases hr with
      | cons _ hr =>
        have : Nat.beq (Nat.lor c (cov d l v)) l = true := by
          rw [Nat.beq_eq]
          apply Nat.eq_of_testBit_eq; intro i
          rw [no, Nat.testBit_or]
          cases hli : l.testBit i with
          | false =>
            by_contra hc
            rw [Bool.not_eq_false, Bool.or_eq_true] at hc
            rcases hc with h | h
            · rw [hcl i h] at hli; simp at hli
            · rw [hc2 i h] at hli; simp at hli
          | true =>
            rcases hcov i hli with h | h
            · rw [h]; rfl
            · obtain ⟨w', hw', h2⟩ := (cov_bit _ _ _ _).1 h
              rw [(cov_bit d l i v).2 ⟨w', hr.subset hw', h2⟩]; simp
        rw [this, Bool.cond_true] at hh
        exact ih hcl hh r hr hcov
      | cons_cons _ hr =>
        rename_i r'
        refine ih (c := Nat.lor c (sp d l w.s)) ?_ h1 r' hr ?_
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true] at hi
          rcases hi with h | h
          · exact hcl i h
          · rw [sp_bit, Bool.and_eq_true] at h; exact h.1
        · intro i hi
          rw [no, Nat.testBit_or, Bool.or_eq_true]
          rcases hcov i hi with h | h
          · exact Or.inl (Or.inl h)
          · change (Nat.lor (sp d l w.s) (cov d l r')).testBit i = true at h
            rw [no, Nat.testBit_or, Bool.or_eq_true] at h
            rcases h with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
lemma addS_cons (o w : W) (t : List W) : addS o (w :: t) = bif Nat.ble w.s o.s then (bif Nat.beq o.s w.s then w :: t else o :: w :: t) else w :: addS o t := by
  change Bool.rec (motive := fun _ => List W) (w :: addS o t) (Bool.rec (motive := fun _ => List W) (o :: w :: t) (w :: t) (Nat.beq o.s w.s)) (Nat.ble w.s o.s) = _
  cases Nat.ble w.s o.s <;> cases Nat.beq o.s w.s <;> rfl
def Srt (v : List W) : Prop := v.Pairwise (fun a b => b.s < a.s)
lemma addS_spec {o : W} {v : List W} (hv : Srt v) : Srt (addS o v) ∧ (∀ w ∈ addS o v, w = o ∨ w ∈ v) ∧
    (∃ w ∈ addS o v, w.s = o.s) ∧ ∀ w ∈ v, w ∈ addS o v := by
  induction v with
  | nil => exact ⟨List.pairwise_singleton _ _, by simp [addS], ⟨o, by simp [addS], rfl⟩, by simp⟩
  | cons x t ih =>
    have hp := List.pairwise_cons.1 hv
    obtain ⟨i1, i2, i3, i4⟩ := ih hp.2
    rw [addS_cons]
    cases h1 : Nat.ble x.s o.s with
    | true =>
      have hle := Nat.le_of_ble_eq_true h1
      cases h2 : Nat.beq o.s x.s with
      | true => exact ⟨hv, fun w hw => Or.inr hw, ⟨x, by simp, (Nat.eq_of_beq_eq_true h2).symm⟩, fun w hw => hw⟩
      | false =>
        have hne : o.s ≠ x.s := fun e => by rw [e, Nat.beq_refl] at h2; simp at h2
        refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, hv⟩, fun w hw => by simpa using hw, ⟨o, by simp, rfl⟩, fun w hw => by simp at hw ⊢; tauto⟩
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · omega
        · have := hp.1 w hw; omega
    | false =>
      have hlt : o.s < x.s := by
        by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
      refine ⟨List.pairwise_cons.2 ⟨fun w hw => ?_, i1⟩, fun w hw => ?_, ?_, fun w hw => ?_⟩
      · rcases i2 w hw with rfl | h
        · exact hlt
        · exact hp.1 w h
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · rcases i2 w hw with h | h <;> simp [h]
      · obtain ⟨w, hw, e⟩ := i3; exact ⟨w, by simp [hw], e⟩
      · simp only [Bool.cond_false, List.mem_cons] at hw ⊢
        rcases hw with rfl | hw
        · simp
        · exact Or.inr (i4 w hw)
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P (x &&& m) := fun w hw => by
      obtain ⟨x, hx, e⟩ := i2 w hw; exact ⟨x, by simp [hx], e⟩
    rw [e]
    cases h1 : Nat.beq (Nat.land y m) 0 with
    | true =>
      refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact absurd (Nat.eq_of_beq_eq_true h1) h2
      · exact i3 x hx h2 h3
    | false =>
      cases h1' : Nat.beq (Nat.land y m) m with
      | true =>
        refine ⟨i1, old, fun x hx h2 h3 => ?_⟩
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact absurd (Nat.eq_of_beq_eq_true h1') h3
        · exact i3 x hx h2 h3
      | false =>
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma pairsC_false {H : ℕ} {h : X → X → Bool} {xs : List X} (hp : pairsC H h xs = false) :
    xs.Pairwise (fun a b => hb H (a.s + b.s) = true → h a b = false) := by
  induction xs with
  | nil => simp
  | cons a r ih =>
    change (Bool.rec (motive := fun _ => Bool) (pairsC H h r) true
      (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r) : Bool) = false at hp
    rw [bR] at hp
    rw [List.pairwise_cons]
    constructor
    · intro b hbm hi
      have h1 : scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r = false := by
        revert hp
        cases scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r <;> simp
      have h2 := scan_false h1 b hbm
      beta_reduce at h2
      rw [bR] at h2
      have h3 : hb H (Nat.add a.s b.s) = true := hi
      rwa [h3, Bool.cond_true] at h2
    · apply ih; revert hp; cases pairsC H h r <;> simp
def mFull (M : List (ℕ × ℕ)) : Bool := (List.range MM).all (fun r => M.any (fun p => hb p.1 r)) && M.any (fun p => Nat.beq p.2 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  simp only [mFull, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.any_eq_true] at hM
  obtain ⟨hM1, p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine one_sound X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc hne har hcr
    obtain ⟨p, hpM, hpb⟩ := hM1 ((a.s + c.s) % MM) (Nat.mod_lt _ (by decide))
    rw [← hb_mod] at hpb
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : L_meta_32784.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32784.X.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
def pwr (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ := (E.map fun e => Nat.land (xw e) (mz Z)).headD 0
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {E : List (ℕ × ℕ)} {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ E Z) : Im (mz Z') S ⊆ WZ E Z' := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨w, hw, rfl⟩ := hS hy
  exact ⟨w, hw, by simp only [Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]⟩
lemma sumc_eq {P : List ℕ} {v : List W} (hw : ∀ w ∈ v, WOk P w) : sumc v = pk P.length (cnt v) := by
  induction v with
  | nil => simp [sumc, pk, cnt]
  | cons w v ih =>
    change w.c + sumc v = _
    rw [ih fun x hx => hw x (by simp [hx]), fl_pk (hw w (by simp)), pk_add]
    exact pk_congr fun j _ => by rw [cnt_cons]
lemma pk16 (Q : List (ℕ × ℕ)) (K : ℕ) : pL (Q.map fun e => 16 + (K - e.2)) = pk (PZ Q).length (fun j => 16 + (K - (Q.getD j (0, K)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
open Classical in
noncomputable def RZ (E : List (ℕ × ℕ)) (Z : ℕ) : ℕ → ℕ := fun s => if s ∈ WZ E Z then 3 else 0
lemma RZ_set (E : List (ℕ × ℕ)) (Z : ℕ) : {x | RZ E Z x ≠ 0} = WZ E Z := by
  ext x; simp only [RZ, Set.mem_setOf_eq]; split_ifs with h <;> simp [h]
lemma RZ_R (E : List (ℕ × ℕ)) (Z : ℕ) : RR (RZ E Z) := by
  intro d a b ha hb h
  have h3 : ∀ x, RZ E Z x ≠ 0 → RZ E Z x = 3 := by
    intro x hx; unfold RZ at hx ⊢; split_ifs at hx ⊢ with h
    · rfl
    · simp at hx
  unfold Al at h
  rw [h3 a ha, h3 b hb] at h
  cases d <;> simp at h
lemma RZ_R2 (E : List (ℕ × ℕ)) (Z : ℕ) : ∀ d a b, (RZ E Z a = 0 ∨ RZ E Z b = 0) → Al (RZ E Z) d a b := by
  intro d a b h
  unfold Al
  rcases h with h | h <;> rw [h] <;> simp
lemma hasP_ok {p : ℕ} {v : List W} (h : p = 0 ∨ ∃ w ∈ v, w.s = p) : hasP p v = true := by
  unfold hasP
  rw [bR]
  rcases h with rfl | ⟨w, hw, rfl⟩
  · rfl
  · have : (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) = true := by
      induction v with
      | nil => simp at hw
      | cons x v ih =>
        change (Bool.rec (motive := fun _ => Bool) (List.rec (motive := fun _ => Bool) false (fun w' _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w'.s w.s)) v : Bool) true (Nat.beq x.s w.s) : Bool) = true
        rw [bR]
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · rw [Nat.beq_refl]; rfl
        · rw [ih hw]; cases Nat.beq x.s w.s <;> rfl
    rw [this]; cases Nat.beq w.s 0 <;> rfl
lemma rawL_sub {E : List (ℕ × ℕ)} (hE : ∀ e ∈ E, e ∈ six) {w : ℕ} (hw : w ∈ rawL E) : w ∈ rawG := by
  simp only [rawG, rawL, List.mem_append, List.mem_map] at hw ⊢
  rcases hw with h | ⟨e, he, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨e, hE e he, rfl⟩
theorem imp_of_live {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
theorem imp_of {E Q : List (ℕ × ℕ)} {Z L : ℕ} (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : Imp E Z L := by
  intro q hq hsol
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm0 : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk := hm0.size.2
  exact imp_of_live hE hp hL hI (by omega) hS hl (fun q' hq' => Nat.find_min hex (by omega))
    (hb.imp id fun h => h t (by omega))
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def rt3 : List (ℕ × ℕ) := [(86, 7), (4166, 7), (16406, 7)]
def rt2 : List (ℕ × ℕ) := [(7, 6), (13, 8), (14, 6), (21, 7), (22, 7), (28, 7), (37, 7), (38, 6), (44, 7), (52, 7), (69, 7), (70, 7), (76, 7), (84, 8), (100, 7), (133, 7), (134, 6), (140, 7), (148, 7), (164, 6), (196, 7), (262, 4), (268, 6), (276, 4), (292, 6), (324, 4), (388, 6), (532, 4), (548, 4), (580, 4), (644, 4), (772, 4), (2053, 6), (2054, 4), (2068, 4), (2084, 6), (2116, 4), (2180, 6), (2564, 4), (4101, 6), (4102, 8), (4108, 6), (4132, 6), (4164, 8), (4228, 6), (4356, 4), (6148, 4), (8197, 4), (8198, 4), (8204, 4), (8324, 4), (12292, 4), (16389, 6), (16390, 8), (16396, 6), (16404, 8), (16420, 6), (16516, 6), (16644, 4), (18436, 4), (24580, 4), (32773, 4), (32774, 4), (32780, 4), (32804, 4), (36868, 4), (49156, 4)]
def rt1 : List (ℕ × ℕ) := [(5, 10), (6, 9), (12, 10), (20, 10), (36, 10), (68, 10), (132, 10), (260, 7), (516, 5), (2052, 7), (4100, 9), (8196, 5), (16388, 9), (32772, 5)]
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def rt : List (ℕ × ℕ) := rt1 ++ rt2 ++ rt3
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, chk E Q 0 (L - 1) t FF 1 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr fun t ht => ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h t ht⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp86 : okE [] (pr [] 86) (86,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4166 : okE [] (pr [] 4166) (4166,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16406 : okE [] (pr [] 16406) (16406,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma valid3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := by
  apply okAll (T := []) _ (by simp)
  apply List.all_eq_true.mpr
  intro e he
  simp only [rt3,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl
  · exact stamp86
  · exact stamp4166
  · exact stamp16406
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp7 : okE [] (pr rt3 7) (7,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp13 : okE [] (pr rt3 13) (13,8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp14 : okE [] (pr rt3 14) (14,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp21 : okE [] (pr rt3 21) (21,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp22 : okE [] (pr rt3 22) (22,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp28 : okE [] (pr rt3 28) (28,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp37 : okE [] (pr rt3 37) (37,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp38 : okE [] (pr rt3 38) (38,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp44 : okE [] (pr rt3 44) (44,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp52 : okE [] (pr rt3 52) (52,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp69 : okE [] (pr rt3 69) (69,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp70 : okE [] (pr rt3 70) (70,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp76 : okE [] (pr rt3 76) (76,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp84 : okE [] (pr rt3 84) (84,8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp100 : okE [] (pr rt3 100) (100,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp133 : okE [] (pr rt3 133) (133,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp134 : okE [] (pr rt3 134) (134,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp140 : okE [] (pr rt3 140) (140,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp148 : okE [] (pr rt3 148) (148,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp164 : okE [] (pr rt3 164) (164,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp196 : okE [] (pr rt3 196) (196,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp262 : okE [] (pr rt3 262) (262,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp268 : okE [] (pr rt3 268) (268,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp276 : okE [] (pr rt3 276) (276,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp292 : okE [] (pr rt3 292) (292,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp324 : okE [] (pr rt3 324) (324,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp388 : okE [] (pr rt3 388) (388,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp532 : okE [] (pr rt3 532) (532,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp548 : okE [] (pr rt3 548) (548,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp580 : okE [] (pr rt3 580) (580,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp644 : okE [] (pr rt3 644) (644,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp772 : okE [] (pr rt3 772) (772,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2053 : okE [] (pr rt3 2053) (2053,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2054 : okE [] (pr rt3 2054) (2054,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2068 : okE [] (pr rt3 2068) (2068,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2084 : okE [] (pr rt3 2084) (2084,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2116 : okE [] (pr rt3 2116) (2116,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2180 : okE [] (pr rt3 2180) (2180,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2564 : okE [] (pr rt3 2564) (2564,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4101 : okE [] (pr rt3 4101) (4101,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4102 : okE [] (pr rt3 4102) (4102,8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4108 : okE [] (pr rt3 4108) (4108,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4132 : okE [] (pr rt3 4132) (4132,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4164 : okE [] (pr rt3 4164) (4164,8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4228 : okE [] (pr rt3 4228) (4228,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4356 : okE [] (pr rt3 4356) (4356,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp6148 : okE [] (pr rt3 6148) (6148,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp8197 : okE [] (pr rt3 8197) (8197,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp8198 : okE [] (pr rt3 8198) (8198,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp8204 : okE [] (pr rt3 8204) (8204,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp8324 : okE [] (pr rt3 8324) (8324,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp12292 : okE [] (pr rt3 12292) (12292,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16389 : okE [] (pr rt3 16389) (16389,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16390 : okE [] (pr rt3 16390) (16390,8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16396 : okE [] (pr rt3 16396) (16396,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16404 : okE [] (pr rt3 16404) (16404,8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16420 : okE [] (pr rt3 16420) (16420,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16516 : okE [] (pr rt3 16516) (16516,6) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16644 : okE [] (pr rt3 16644) (16644,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp18436 : okE [] (pr rt3 18436) (18436,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp24580 : okE [] (pr rt3 24580) (24580,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp32773 : okE [] (pr rt3 32773) (32773,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp32774 : okE [] (pr rt3 32774) (32774,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp32780 : okE [] (pr rt3 32780) (32780,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp32804 : okE [] (pr rt3 32804) (32804,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp36868 : okE [] (pr rt3 36868) (36868,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp49156 : okE [] (pr rt3 49156) (49156,4) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma valid2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := by
  apply okAll (T := rt3) _ valid3
  apply List.all_eq_true.mpr
  intro e he
  simp only [rt2,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stamp7
  · exact stamp13
  · exact stamp14
  · exact stamp21
  · exact stamp22
  · exact stamp28
  · exact stamp37
  · exact stamp38
  · exact stamp44
  · exact stamp52
  · exact stamp69
  · exact stamp70
  · exact stamp76
  · exact stamp84
  · exact stamp100
  · exact stamp133
  · exact stamp134
  · exact stamp140
  · exact stamp148
  · exact stamp164
  · exact stamp196
  · exact stamp262
  · exact stamp268
  · exact stamp276
  · exact stamp292
  · exact stamp324
  · exact stamp388
  · exact stamp532
  · exact stamp548
  · exact stamp580
  · exact stamp644
  · exact stamp772
  · exact stamp2053
  · exact stamp2054
  · exact stamp2068
  · exact stamp2084
  · exact stamp2116
  · exact stamp2180
  · exact stamp2564
  · exact stamp4101
  · exact stamp4102
  · exact stamp4108
  · exact stamp4132
  · exact stamp4164
  · exact stamp4228
  · exact stamp4356
  · exact stamp6148
  · exact stamp8197
  · exact stamp8198
  · exact stamp8204
  · exact stamp8324
  · exact stamp12292
  · exact stamp16389
  · exact stamp16390
  · exact stamp16396
  · exact stamp16404
  · exact stamp16420
  · exact stamp16516
  · exact stamp16644
  · exact stamp18436
  · exact stamp24580
  · exact stamp32773
  · exact stamp32774
  · exact stamp32780
  · exact stamp32804
  · exact stamp36868
  · exact stamp49156
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp5 : okE [] (pr (rt2 ++ rt3) 5) (5,10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp6 : okE [] (pr (rt2 ++ rt3) 6) (6,9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp12 : okE [] (pr (rt2 ++ rt3) 12) (12,10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp20 : okE [] (pr (rt2 ++ rt3) 20) (20,10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp36 : okE [] (pr (rt2 ++ rt3) 36) (36,10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp68 : okE [] (pr (rt2 ++ rt3) 68) (68,10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp132 : okE [] (pr (rt2 ++ rt3) 132) (132,10) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp260 : okE [] (pr (rt2 ++ rt3) 260) (260,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp516 : okE [] (pr (rt2 ++ rt3) 516) (516,5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp2052 : okE [] (pr (rt2 ++ rt3) 2052) (2052,7) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp4100 : okE [] (pr (rt2 ++ rt3) 4100) (4100,9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp8196 : okE [] (pr (rt2 ++ rt3) 8196) (8196,5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp16388 : okE [] (pr (rt2 ++ rt3) 16388) (16388,9) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem stamp32772 : okE [] (pr (rt2 ++ rt3) 32772) (32772,5) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma valid1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := by
  apply okAll (T := (rt2 ++ rt3)) _ (apI valid2 valid3)
  apply List.all_eq_true.mpr
  intro e he
  simp only [rt1,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact stamp5
  · exact stamp6
  · exact stamp12
  · exact stamp20
  · exact stamp36
  · exact stamp68
  · exact stamp132
  · exact stamp260
  · exact stamp516
  · exact stamp2052
  · exact stamp4100
  · exact stamp8196
  · exact stamp16388
  · exact stamp32772
def remembered := rt1 ++ rt2 ++ rt3
lemma remembered_ok : ∀ e ∈ remembered, Imp [] e.1 e.2 := apI (apI valid1 valid2) valid3
def faceWires : List W := [⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7 64) 0xffff7ffff7fc0000) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x10741041c000) 64) 0x820e000e001c0001) 64) 0x400060000400c00) 64) 0x2083800380070000) 64) 0x20060001c0000001) 64) 0xff001ff001f07f00) 64) 0x7f0003f8001c0fe) 64) 0xf03f8001fc000) 64) 0xe07c001c07c00181) 64) 0xc07807ddf7df7fff) 64) 0xbefbfffbfff7fff0) 64) 0x0) 64) 0x0) 64) 0xc000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x800000001 64) 0x400000000) 64) 0x8000000010000100) 64) 0x42108420000) 64) 0x0) 64) 0x40000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x10842 64) 0x1080000000000000) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x2) 64) 0x0), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x10842 64) 0x1080000800000001) 64) 0x400000000) 64) 0x8000000010000100) 64) 0x42108420000) 64) 0x2) 64) 0x40000000), 0x3⟩, ⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7 64) 0xffff00000001ffff) 64) 0xdffffefffff7f800) 64) 0x0) 64) 0x0) 64) 0x1f47df013800) 64) 0x9c009c0138011) 64) 0xf7d085e0087d0bc0) 64) 0x270027004e004) 64) 0x85c00138000001) 64) 0xf0f8100c010070fe) 64) 0x70fe0387f01fe01) 64) 0xc000800780003c00) 64) 0x1003c003003c0060) 64) 0x300607ddf7c00000) 64) 0x7) 64) 0x7df7bdfffbdf7bff) 64) 0xe000000000000000) 64) 0x3e00), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4200000 64) 0x0) 64) 0x20000000) 64) 0x400000000800008) 64) 0x40000001084) 64) 0x2100000000000000) 64) 0x2000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x80010000 64) 0x4210842108400) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x1000000000000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x84210000 64) 0x4210842108400) 64) 0x20000000) 64) 0x400000000800008) 64) 0x40000001084) 64) 0x2100000000000000) 64) 0x1000000002000000), 0x3⟩, ⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ffff0000000 64) 0x3ff) 64) 0xff800fffff7ffffb) 64) 0xfc00000000000000) 64) 0x20007c8580) 64) 0xfbe42c042c085808) 64) 0x8421e04008438) 64) 0x3ef90b010b021602) 64) 0x3e423c0085800000) 64) 0x80209b8b19000088) 64) 0x20030300181808b1) 64) 0xb8c082c66396331c) 64) 0xff03030220303048) 64) 0x2204201c001f0000) 64) 0x3ef8000000000007) 64) 0x7bdfff8000000) 64) 0xfbe000000000001) 64) 0xefbdfff00000007c), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x80200000 64) 0x2000000) 64) 0x0) 64) 0x1000000002000) 64) 0x200000100000080) 64) 0x8000084200000) 64) 0x8000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000800 64) 0x20) 64) 0x108421084200) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x4000000000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x84200800 64) 0x2000020) 64) 0x108421084200) 64) 0x1000000002000) 64) 0x200000100000080) 64) 0x8000084200000) 64) 0x4000000008000), 0x3⟩, ⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1ffff 64) 0xc0000000000003ff) 64) 0xffbfe00000000000) 64) 0x0) 64) 0x80208202600) 64) 0x410130013002601c) 64) 0x8200011000200220) 64) 0x10404c004c009800) 64) 0x1001200026000001) 64) 0x8c70c03e08e48f1) 64) 0xc48c1c2460e130c1) 64) 0x3f08f3007c1803e0) 64) 0x8c403c10c403c111) 64) 0xc41c7c0001f7fff) 64) 0x8000000000000007) 64) 0x7df0000000000000) 64) 0xfbefffefffdfffc) 64) 0x180), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x40000000) 64) 0x1000000) 64) 0x20000000040000) 64) 0x4000002000001000) 64) 0x8421000000000) 64) 0x100000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000021 64) 0x842000000000000) 64) 0x0) 64) 0x0) 64) 0x0) 64) 0x80000000000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x4000040000021) 64) 0x842000001000000) 64) 0x20000000040000) 64) 0x4000002000001000) 64) 0x8421000000000) 64) 0x80000000100000), 0x3⟩, ⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1ffffe0000000000 64) 0xfffff000000) 64) 0x1ffff7fc0000000) 64) 0x40104101160) 64) 0x20808b008a011600) 64) 0x411e00890f100114) 64) 0x82022c022804587) 64) 0x8800921011600000) 64) 0x4494424294492445) 64) 0x124ad2924484a428) 64) 0x24a448a553450292) 64) 0x4a32b2cbb2020c04) 64) 0x89211001f0000000) 64) 0x3e03fff800000000) 64) 0x7c07800003df0000) 64) 0xf80fffe00000001) 64) 0xef8000077fffb973), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x2 64) 0x100000) 64) 0x800000000080000) 64) 0x0) 64) 0x10000008000004) 64) 0x400080010800) 64) 0x400), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x200000000000 64) 0x100000000010) 64) 0x8421084000000000) 64) 0x0) 64) 0x0) 64) 0x200000000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x2 64) 0x200000100000) 64) 0x800100000080010) 64) 0x8421084000000000) 64) 0x10000008000004) 64) 0x400080010800) 64) 0x200000000400), 0x3⟩, ⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xfffff00000 64) 0x7ffff8) 64) 0x1ffff007) 64) 0xfc00020082080894) 64) 0x104044c045008980) 64) 0x2080f0448009e08a) 64) 0x410113011402260) 64) 0x4f0490808980000) 64) 0x1151409134131114) 64) 0x51144488b6345412) 64) 0x9a118482542693a) 64) 0x260404c451696c04) 64) 0x7708500007c00000) 64) 0xf800000007fff0) 64) 0x1f03c00001f7800) 64) 0x3e00000001fffc) 64) 0xfbc00077fff6cdb), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x80000000000400 64) 0x2000000000200) 64) 0x4000000000) 64) 0x20000) 64) 0x100001000200840) 64) 0x1), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x10000000000 64) 0x8000000000) 64) 0x200000108) 64) 0x4210800000000000) 64) 0x0) 64) 0x800000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x80010000000400 64) 0x2008000000200) 64) 0x4200000108) 64) 0x4210800000020000) 64) 0x100001000200840) 64) 0x800000001), 0x3⟩, ⟨(Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1ffff001ffff7f0 64) 0x58) 64) 0x28003800500) 64) 0x42001c2004007) 64) 0xa000e00141) 64) 0x20039c00500000) 64) 0x220a812448240222) 64) 0xa020ab0103580204) 64) 0x524220118a808c4c) 64) 0x128eb81218db8bc) 64) 0x1212a00000000000) 64) 0x3fff00000) 64) 0x3c07bff) 64) 0xe0000000fffc0001) 64) 0xe03dfff70000366e), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x84200000 64) 0x1000000000008000) 64) 0x40000000004000) 64) 0x80000000000) 64) 0x800000400000) 64) 0x2000020004010040) 64) 0x20), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x10 64) 0x210842000) 64) 0x0) 64) 0x0) 64) 0x10000000000), (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x84200000 64) 0x1000000000008000) 64) 0x40000000004010) 64) 0x80210842000) 64) 0x800000400000) 64) 0x2000020004010040) 64) 0x10000000020), 0x3⟩]
noncomputable def query12 (t H ph : ℕ) : Bool :=
  anySub (pos t) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fff0000) faceWires 0
    (fun r => startv (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fff0000) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7 64) 0xffff7ffff7fdffff) 64) 0xdffffefffff7fbff) 64) 0xffbfefffff7ffffb) 64) 0xfdffff7fdffff7f7) 64) 0xfdffdf77df7dfffe) 64) 0xfbefffefffdfffdd) 64) 0xf7def7ffef7defff) 64) 0xbefbfffbfff7fff7) 64) 0xbef7ffddfffc0001) 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fffffff) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x842108421 64) 0x842108421084210) 64) 0x8421084210842108) 64) 0x4210842108421084) 64) 0x2108421084210842) 64) 0x1084210842108421) 64) 0x842108421084210) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xad6b8c631 64) 0x8c6318b5a96a5b18) 64) 0xc6318c5a96b52d8b) 64) 0x62d8c5b18c6316c5) 64) 0xb16c56d5adab5a56) 64) 0xb5ad6d5ad6b6a5af) 64) 0x3bceb7aca5294a72) 12 t 0 H ph r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma frozen12 (t H ph : ℕ) : chk [] remembered 4 12 t H ph = query12 t H ph := by
  unfold chk query12
  beta_reduce
  rw [frc_eq]
  simp only [st_eq]
  rfl
noncomputable def query13 (t H ph : ℕ) : Bool :=
  anySub (pos t) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fff0000) faceWires 0
    (fun r => startv (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x1 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fff0000) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7 64) 0xffff7ffff7fdffff) 64) 0xdffffefffff7fbff) 64) 0xffbfefffff7ffffb) 64) 0xfdffff7fdffff7f7) 64) 0xfdffdf77df7dfffe) 64) 0xfbefffefffdfffdd) 64) 0xf7def7ffef7defff) 64) 0xbefbfffbfff7fff7) 64) 0xbef7ffddfffc0001) 64) 0xffffdffffdff7fff) 64) 0xf7ffffbffffdfeff) 64) 0xffeffbffffdffffe) 64) 0xff7fffdff7fffdfd) 64) 0xff7ff7ddf7df7fff) 64) 0xbefbfffbfff7fff7) 64) 0x7df7bdfffbdf7bff) 64) 0xefbefffefffdfffd) 64) 0xefbdfff77fffffff) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x842108421 64) 0x842108421084210) 64) 0x8421084210842108) 64) 0x4210842108421084) 64) 0x2108421084210842) 64) 0x1084210842108421) 64) 0x842108421084210) (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0xb5ad9ce73 64) 0x9ce739bdeb7adf39) 64) 0xce739cdeb7bd6f9b) 64) 0xe6f9cdf39ce737cd) 64) 0xf37cdaf6b5ed6ada) 64) 0xd6b5af6b5ad7adf1) 64) 0x4c52d8b4e739ce93) 13 t 0 H ph r)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma frozen13 (t H ph : ℕ) : chk [] remembered 4 13 t H ph = query13 t H ph := by
  unfold chk query13
  beta_reduce
  rw [frc_eq]
  simp only [st_eq]
  rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt0 : query12 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt1 : query12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt2 : query12 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt3 : query12 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt4 : query12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt5 : query12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt6 : query12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt7 : query12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt8 : query12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt9 : query12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt10 : query12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt11 : query12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowAt12 : query12 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma face_low : Imp [] 4 13 := by
  apply imp_of (Or.inl rfl) (by decide) (by norm_num) remembered_ok
  right
  intro t ht
  refine ⟨[(FF,1)],ffull,?_⟩
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  rw [frozen12]
  change query12 t FF 1 = false
  interval_cases t
  · exact lowAt0
  · exact lowAt1
  · exact lowAt2
  · exact lowAt3
  · exact lowAt4
  · exact lowAt5
  · exact lowAt6
  · exact lowAt7
  · exact lowAt8
  · exact lowAt9
  · exact lowAt10
  · exact lowAt11
  · exact lowAt12


lemma pinAt (i z : ℕ) : rawP.getD i 0 &&& mz z ∈ C (mz z) (WZ [] z) := by
  by_cases h : i < rawP.length
  · have mem : rawP.getD i 0 ∈ rawP := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h,Option.getD_some]
      exact List.getElem_mem h
    exact Or.inl ⟨_, by simpa [rawL] using mem, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inr (Or.inl (by simp))

lemma supplied {z L : ℕ} (e : ℕ × ℕ) (lower : Imp [] z L) : Imp [e] z (L-1) := by
  intro k hk tail
  apply lower (k+1) (by omega)
  apply Sol.bi (d := decide (e.1 < 8)) (pinAt (e.1 % 8) z) (pinAt e.2 z) (al0 _ _ _)
  apply tail.mono le_rfl
  intro x hx
  rcases hx with ⟨w,hw,rfl⟩ | hc
  · simp only [rawL,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact Or.inr (Or.inl ⟨w, by simpa [rawL] using hw, rfl⟩)
    · exact Or.inl (and_op _ _ _ _)
  · exact Or.inr (Or.inr hc)

def grade (pool : List (ℕ × ℕ)) (keep : List ℕ) : List (ℕ × ℕ) :=
  pool.map fun a => (a.1, if a.1 ∈ keep then a.2 else a.2-1)
noncomputable def audit (g : ℕ × ℕ) (pool prior : List (ℕ × ℕ)) (keep : List ℕ) : Bool :=
  pool.all fun a => !(keep.contains a.1) || okE [g] (pr prior a.1) a
lemma grade_ok {g : ℕ × ℕ} (hg : g ∈ six) {pool prior : List (ℕ × ℕ)} {keep : List ℕ}
    (hp : ∀ a ∈ pool, Imp [] a.1 a.2) (hr : ∀ a ∈ prior, Imp [g] a.1 a.2)
    (checked : audit g pool prior keep = true) :
    ∀ a ∈ grade pool keep, Imp [g] a.1 a.2 := by
  intro a ha
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ha
  by_cases held : v.1 ∈ keep
  · simp only [if_pos held]
    have h := List.all_eq_true.mp checked v hv
    have inK : keep.contains v.1 = true := by simpa using held
    simp only [inK,Bool.not_true,Bool.false_or] at h
    exact imp_okE (Or.inr ⟨g,hg,rfl,hp v hv⟩) h (fun a m => hr a (List.mem_of_mem_filter m))
  · simp only [if_neg held]
    exact supplied g (hp v hv)

def routeRows (p : List ℕ) (w : ℕ) : ℕ := p.foldr (fun i r => Nat.bit (w.testBit i) r) 0
lemma route_zero (p : List ℕ) : routeRows p 0 = 0 := by
  induction p with
  | nil => rfl
  | cons i p ih => change Nat.bit ((0 : ℕ).testBit i) (routeRows p 0) = 0; simp [ih]
lemma route_and (p : List ℕ) (x y : ℕ) : routeRows p (x &&& y) = routeRows p x &&& routeRows p y := by
  induction p with
  | nil => simp [routeRows]
  | cons i p ih =>
    change Nat.bit ((x &&& y).testBit i) (routeRows p (x &&& y)) = Nat.bit (x.testBit i) (routeRows p x) &&& Nat.bit (y.testBit i) (routeRows p y)
    rw [Nat.testBit_and, ih, Nat.land_bit]
lemma route_or (p : List ℕ) (x y : ℕ) : routeRows p (x ||| y) = routeRows p x ||| routeRows p y := by
  induction p with
  | nil => simp [routeRows]
  | cons i p ih =>
    change Nat.bit ((x ||| y).testBit i) (routeRows p (x ||| y)) = Nat.bit (x.testBit i) (routeRows p x) ||| Nat.bit (y.testBit i) (routeRows p y)
    rw [Nat.testBit_or, ih, Nat.lor_bit]
lemma route_xor (p : List ℕ) (x y : ℕ) : routeRows p (x ^^^ y) = routeRows p x ^^^ routeRows p y := by
  induction p with
  | nil => simp [routeRows]
  | cons i p ih =>
    change Nat.bit ((x ^^^ y).testBit i) (routeRows p (x ^^^ y)) = Nat.bit (x.testBit i) (routeRows p x) ^^^ Nat.bit (y.testBit i) (routeRows p y)
    rw [Nat.testBit_xor, ih, Nat.xor_bit]
lemma route_op (p : List ℕ) (d : Bool) (a b : ℕ) : routeRows p (op d a b) = op d (routeRows p a) (routeRows p b) := by
  cases d <;> simp [op, route_and, route_or]

def Beg (A : ℕ → ℕ → Prop) (R : ℕ → ℕ) (m T k t : ℕ) (S : Finset ℕ) : Prop :=
  Live R m T k t S ∨ ∃ q d a b U, k = q + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ A a b ∧ Bi Z0 d a b S U ∧ Live Z0 m T q t U
def seen (M : List (ℕ × ℕ)) (a b : ℕ) : Bool := M.any fun p => hb p.1 (a + b)

section
variable {R : ℕ → ℕ} {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma chosenOne {A : ℕ → ℕ → Prop} (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (ho : Beg A R m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, A a.s c.s → a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_32784.X → L_meta_32784.X → Bool) → List L_meta_32784.X → Bool,
      node (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
      ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
        h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
        h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases ho with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', admissible, hb, hl1⟩
  · exact mv_sound X hR (look_sound X hR K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨go, hg1, hg2⟩ := h1 wa hwa wb hwb admissible hb.1 (by rw [hcod wa hwa]; exact ha) (by rw [hcod wb hwb]; exact hb')
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      rw [hs.rep.inj ha hwa hax, hs.rep.inj hc hwb hcy]
      exact hg2 h hp) hg1
    have hfr : R (op d wa.s wb.s) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ hf hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := wa.s) (b := wb.s) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (al0 _ _ _) (hs'.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hx'))
      · exact Or.inr (Or.inr hx)
lemma chosenTop (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : ∃ p ∈ M, Nat.beq p.2 1 = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (ho : Beg (fun a b => seen M a b = true) R m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  obtain ⟨p0, hp0, hp1⟩ := hM
  have un : ∀ p ∈ M, 2 ≤ v.length ∧ tst (pos' t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs)))) = false := by
    intro p hp
    have h := h p hp
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq p.2 1)) true
      (node (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v (fun h xs => pairsC p.1 h (fs xs))))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      refine ⟨?_, h⟩
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
  have hmin : Min Z0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  obtain ⟨y, hFy, hyk⟩ := tst_sound X hs hmin hk
  have un2 := fun p hp => (hFy _).symm.trans (un p hp).2
  refine chosenOne X hR hR2 (K := K) (f := look1 l m g K K) (look1_sound X hR hR2 (K := K) K) hs hcod (un p0 hp0).1 hk hl ho hmW hyk ?_ ?_
  · have := (or_false' X (un2 p0 hp0)).2
    rw [bR, hp1, cond_true] at this; exact this
  · intro a ha c hc admissible hne har hcr
    obtain ⟨p, hpM, hpb⟩ := List.any_eq_true.mp admissible
    refine ⟨_, (or_false' X (un2 p hpM)).1, fun h hp => ?_⟩
    have hpw := pairsC_false hp
    have : Std.Symm (fun a b : L_meta_32784.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_32784.X.s e)) hpb
end
theorem chosenImp {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), (∃ p ∈ M, Nat.beq p.2 1 = true) ∧ Beg (fun a b => seen M a b = true) (RZ E Z) (mz Z) (tz Z) k t S ∧ ∀ p ∈ M, chk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hfront, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL E)
  set v := (avl (PZ Q) (mz Z) (rawL E)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL E)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _
  have hcod : ∀ w ∈ v, w.r = RZ E Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ E Z := ⟨x, hx, rfl⟩
    change 3 = RZ E Z (x &&& mz Z)
    rw [RZ, if_pos this]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine chosenTop X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl hfront ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx


def Stable (p : List ℕ) (a : ℕ) : Prop := routeRows p (routeRows p a) = a

lemma stable_xor {p : List ℕ} {a b : ℕ} (ha : Stable p a) (hb : Stable p b) : Stable p (a ^^^ b) := by
  unfold Stable at ha hb ⊢
  simp only [route_xor, ha, hb]

lemma stable_op {p : List ℕ} {a b : ℕ} (d : Bool) (ha : Stable p a) (hb : Stable p b) : Stable p (op d a b) := by
  unfold Stable at ha hb ⊢
  simp only [route_op, ha, hb]

lemma stable_ne {p : List ℕ} {a b : ℕ} (ha : Stable p a) (hb : Stable p b) (hn : a ≠ b) : routeRows p a ≠ routeRows p b := by
  intro e
  exact hn (ha.symm.trans ((congrArg (routeRows p) e).trans hb))

lemma Live.turn {m T k t : ℕ} {S : Finset ℕ} (p : List ℕ) (hm : Stable p m) (hl : Live Z0 m T k t S) :
    (∀ x ∈ S, Stable p x) → Live Z0 (routeRows p m) (routeRows p T) k t (S.image (routeRows p)) := by
  induction hl with
  | stop => intro _; simpa using (Live.stop : Live Z0 (routeRows p m) (routeRows p T) 0 0 _)
  | @un k t a U _ ih =>
    intro hs
    have ha := hs a (by simp)
    have next := ih (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact stable_xor ha hm
      · exact hs _ (Finset.mem_insert_of_mem hx))
    rw [Finset.image_insert] at next ⊢
    rw [route_xor] at next
    exact Live.un next
  | @bi k t d a b U hn _ _ ih =>
    intro hs
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    have next := ih (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact stable_op d ha hb
      · exact hs _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)))
    simp only [Finset.image_insert, route_op] at next ⊢
    exact Live.bi (stable_ne ha hb hn) (al0 _ _ _) next

lemma Bi.turn {a b : ℕ} {d : Bool} {S U : Finset ℕ} (p : List ℕ) (h : Bi Z0 d a b S U)
    (hs : ∀ x ∈ S, Stable p x) :
    Bi Z0 d (routeRows p a) (routeRows p b) (S.image (routeRows p)) (U.image (routeRows p)) := by
  obtain ⟨hn, V, rfl, rfl, _⟩ := h
  exact ⟨stable_ne (hs _ (by simp)) (hs _ (by simp)) hn, V.image (routeRows p),
    by simp, by simp only [Finset.image_insert, route_op], al0 _ _ _⟩

lemma Bi.afterStable {a b : ℕ} {d : Bool} {S U : Finset ℕ} {p : List ℕ}
    (h : Bi Z0 d a b S U) (hs : ∀ x ∈ S, Stable p x) : ∀ x ∈ U, Stable p x := by
  intro x hx
  rcases Finset.mem_insert.mp (h.sub.2.2 hx) with rfl | hx
  · exact stable_op d (hs _ h.sub.1) (hs _ h.sub.2.1)
  · exact hs _ hx

def turn1 : List ℕ := [558, 359, 559, 489, 540, 468, 6, 562, 560, 563, 495, 564, 473, 13, 570, 568, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 489, 489, 489, 489, 31, 540, 540, 540, 540, 540, 31, 468, 468, 468, 468, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 545, 545, 545, 545, 545, 31, 544, 544, 544, 544, 544, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 495, 495, 495, 495, 31, 564, 564, 564, 564, 564, 31, 473, 473, 473, 473, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 497, 497, 497, 497, 31, 476, 476, 476, 476, 31, 567, 567, 567, 567, 567, 31, 566, 566, 566, 566, 566, 31, 519, 519, 519, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 553, 553, 553, 553, 553, 31, 551, 551, 551, 551, 551, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 555, 555, 555, 555, 555, 31, 574, 574, 574, 574, 574, 31, 572, 572, 572, 572, 572, 31, 575, 575, 575, 31, 576, 576, 576, 576, 576, 31, 558, 559, 562, 561, 560, 563, 565, 570, 569, 568, 571, 31, 558, 489, 562, 560, 495, 497, 570, 568, 571, 31, 359, 559, 561, 563, 565, 569, 571, 31, 558, 359, 559, 489, 562, 561, 365, 560, 563, 495, 565, 497, 570, 569, 373, 568, 571, 31, 558, 468, 562, 560, 473, 476, 570, 568, 571, 31, 558, 359, 559, 468, 562, 561, 560, 336, 563, 473, 565, 476, 570, 569, 568, 344, 571, 31, 559, 540, 545, 544, 565, 553, 551, 555, 31, 558, 559, 489, 540, 562, 561, 560, 545, 544, 563, 495, 565, 497, 570, 569, 568, 553, 551, 571, 555, 31, 558, 559, 540, 468, 562, 561, 560, 545, 544, 563, 473, 565, 476, 570, 569, 568, 553, 551, 571, 555, 31, 558, 562, 561, 560, 519, 570, 569, 568, 571, 31, 558, 559, 540, 562, 561, 560, 545, 444, 544, 563, 565, 519, 570, 569, 568, 553, 551, 571, 555, 31, 563, 564, 565, 567, 566, 574, 572, 576, 31, 558, 559, 489, 562, 561, 560, 563, 495, 564, 565, 497, 567, 566, 570, 569, 568, 571, 574, 572, 576, 31, 558, 559, 468, 562, 561, 560, 563, 564, 473, 565, 476, 567, 566, 570, 569, 568, 571, 574, 572, 576, 31, 558, 559, 562, 561, 560, 563, 564, 565, 567, 517, 566, 519, 570, 569, 568, 571, 574, 572, 576, 31, 558, 562, 561, 560, 570, 569, 568, 571, 575, 31, 558, 559, 540, 562, 561, 560, 545, 544, 563, 565, 570, 569, 568, 553, 552, 551, 571, 555, 575, 31, 558, 559, 562, 561, 560, 563, 564, 565, 567, 566, 570, 569, 568, 571, 574, 573, 572, 575, 576, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 934, 952, 898, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 906, 952, 924, 31, 888, 906, 952, 924, 961, 1003, 982, 1033, 1084, 1063, 1104, 1134, 1154, 31, 934, 952, 1003, 1084, 31, 961, 1003, 982, 1033, 1134, 31, 898, 924, 982, 1063, 31, 888, 934, 952, 898, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 888, 906, 952, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 888, 934, 952, 898, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 961, 1003, 982, 1033, 1134, 31, 961, 1003, 982, 1033, 1134, 31, 888, 906, 952, 924, 1003, 982, 1033, 1042, 1084, 1063, 1104, 1134, 1154, 31, 934, 952, 1003, 1084, 31, 1042, 1084, 1063, 1104, 1154, 31, 898, 924, 982, 1063, 31, 888, 906, 952, 924, 961, 1003, 982, 1033, 1042, 1084, 1063, 1104, 1134, 1154, 31, 934, 952, 1003, 1084, 31, 898, 924, 982, 1063, 31, 1042, 1084, 1063, 1104, 1154, 31, 1042, 1084, 1063, 1104, 1154, 31, 1013, 1033, 1104, 31, 888, 934, 952, 898, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 888, 906, 952, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 888, 934, 952, 898, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 961, 1003, 982, 1033, 1134, 31, 961, 1003, 982, 1033, 1134, 31, 888, 934, 906, 952, 898, 924, 1003, 982, 1013, 1033, 1084, 1063, 1104, 1114, 1134, 1154, 31, 961, 1003, 982, 1033, 1134, 31, 1042, 1084, 1063, 1104, 1154, 31, 1042, 1084, 1063, 1104, 1154, 31, 1114, 1134, 1154, 31, 1042, 1084, 1063, 1104, 1154, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 906, 906, 906, 906, 906, 906, 906, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31]
def turn2 : List ℕ := [558, 359, 559, 468, 540, 489, 6, 568, 570, 563, 473, 564, 495, 13, 560, 562, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 468, 468, 468, 468, 31, 540, 540, 540, 540, 540, 31, 489, 489, 489, 489, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 551, 551, 551, 551, 551, 31, 553, 553, 553, 553, 553, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 473, 473, 473, 473, 31, 564, 564, 564, 564, 564, 31, 495, 495, 495, 495, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 476, 476, 476, 476, 31, 497, 497, 497, 497, 31, 572, 572, 572, 572, 572, 31, 574, 574, 574, 574, 574, 31, 575, 575, 575, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 544, 544, 544, 544, 544, 31, 545, 545, 545, 545, 545, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 555, 555, 555, 555, 555, 31, 566, 566, 566, 566, 566, 31, 567, 567, 567, 567, 567, 31, 519, 519, 519, 31, 576, 576, 576, 576, 576, 31, 558, 559, 568, 569, 570, 563, 565, 560, 561, 562, 571, 31, 558, 468, 568, 570, 473, 476, 560, 562, 571, 31, 359, 559, 569, 563, 565, 561, 571, 31, 558, 359, 559, 468, 568, 569, 344, 570, 563, 473, 565, 476, 560, 561, 336, 562, 571, 31, 558, 489, 568, 570, 495, 497, 560, 562, 571, 31, 558, 359, 559, 489, 568, 569, 570, 373, 563, 495, 565, 497, 560, 561, 562, 365, 571, 31, 559, 540, 551, 553, 565, 544, 545, 555, 31, 558, 559, 468, 540, 568, 569, 570, 551, 553, 563, 473, 565, 476, 560, 561, 562, 544, 545, 571, 555, 31, 558, 559, 540, 489, 568, 569, 570, 551, 553, 563, 495, 565, 497, 560, 561, 562, 544, 545, 571, 555, 31, 558, 568, 569, 570, 575, 560, 561, 562, 571, 31, 558, 559, 540, 568, 569, 570, 551, 552, 553, 563, 565, 575, 560, 561, 562, 544, 545, 571, 555, 31, 563, 564, 565, 572, 574, 566, 567, 576, 31, 558, 559, 468, 568, 569, 570, 563, 473, 564, 565, 476, 572, 574, 560, 561, 562, 571, 566, 567, 576, 31, 558, 559, 489, 568, 569, 570, 563, 564, 495, 565, 497, 572, 574, 560, 561, 562, 571, 566, 567, 576, 31, 558, 559, 568, 569, 570, 563, 564, 565, 572, 573, 574, 575, 560, 561, 562, 571, 566, 567, 576, 31, 558, 568, 569, 570, 560, 561, 562, 571, 519, 31, 558, 559, 540, 568, 569, 570, 551, 553, 563, 565, 560, 561, 562, 544, 444, 545, 571, 555, 519, 31, 558, 559, 568, 569, 570, 563, 564, 565, 572, 574, 560, 561, 562, 571, 566, 517, 567, 519, 576, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 898, 924, 934, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 906, 924, 952, 31, 888, 906, 924, 952, 961, 982, 1003, 1134, 1063, 1084, 1154, 1033, 1104, 31, 898, 924, 982, 1063, 31, 961, 982, 1003, 1134, 1033, 31, 934, 952, 1003, 1084, 31, 888, 898, 924, 934, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 888, 906, 924, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 888, 898, 924, 934, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 961, 982, 1003, 1134, 1033, 31, 961, 982, 1003, 1134, 1033, 31, 888, 906, 924, 952, 982, 1003, 1134, 1042, 1063, 1084, 1154, 1033, 1104, 31, 898, 924, 982, 1063, 31, 1042, 1063, 1084, 1154, 1104, 31, 934, 952, 1003, 1084, 31, 888, 906, 924, 952, 961, 982, 1003, 1134, 1042, 1063, 1084, 1154, 1033, 1104, 31, 898, 924, 982, 1063, 31, 934, 952, 1003, 1084, 31, 1042, 1063, 1084, 1154, 1104, 31, 1042, 1063, 1084, 1154, 1104, 31, 1114, 1134, 1154, 31, 888, 898, 924, 934, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 888, 906, 924, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 888, 898, 924, 934, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 961, 982, 1003, 1134, 1033, 31, 961, 982, 1003, 1134, 1033, 31, 888, 898, 906, 924, 934, 952, 982, 1003, 1114, 1134, 1063, 1084, 1154, 1013, 1033, 1104, 31, 961, 982, 1003, 1134, 1033, 31, 1042, 1063, 1084, 1154, 1104, 31, 1042, 1063, 1084, 1154, 1104, 31, 1013, 1033, 1104, 31, 1042, 1063, 1084, 1154, 1104, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 906, 906, 906, 906, 906, 906, 906, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31]
def turn3 : List ℕ := [558, 359, 559, 489, 540, 468, 6, 570, 568, 563, 495, 564, 473, 13, 562, 560, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 489, 489, 489, 489, 31, 540, 540, 540, 540, 540, 31, 468, 468, 468, 468, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 553, 553, 553, 553, 553, 31, 551, 551, 551, 551, 551, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 495, 495, 495, 495, 31, 564, 564, 564, 564, 564, 31, 473, 473, 473, 473, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 497, 497, 497, 497, 31, 476, 476, 476, 476, 31, 574, 574, 574, 574, 574, 31, 572, 572, 572, 572, 572, 31, 575, 575, 575, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 545, 545, 545, 545, 545, 31, 544, 544, 544, 544, 544, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 555, 555, 555, 555, 555, 31, 567, 567, 567, 567, 567, 31, 566, 566, 566, 566, 566, 31, 519, 519, 519, 31, 576, 576, 576, 576, 576, 31, 558, 559, 570, 569, 568, 563, 565, 562, 561, 560, 571, 31, 558, 489, 570, 568, 495, 497, 562, 560, 571, 31, 359, 559, 569, 563, 565, 561, 571, 31, 558, 359, 559, 489, 570, 569, 373, 568, 563, 495, 565, 497, 562, 561, 365, 560, 571, 31, 558, 468, 570, 568, 473, 476, 562, 560, 571, 31, 558, 359, 559, 468, 570, 569, 568, 344, 563, 473, 565, 476, 562, 561, 560, 336, 571, 31, 559, 540, 553, 551, 565, 545, 544, 555, 31, 558, 559, 489, 540, 570, 569, 568, 553, 551, 563, 495, 565, 497, 562, 561, 560, 545, 544, 571, 555, 31, 558, 559, 540, 468, 570, 569, 568, 553, 551, 563, 473, 565, 476, 562, 561, 560, 545, 544, 571, 555, 31, 558, 570, 569, 568, 575, 562, 561, 560, 571, 31, 558, 559, 540, 570, 569, 568, 553, 552, 551, 563, 565, 575, 562, 561, 560, 545, 544, 571, 555, 31, 563, 564, 565, 574, 572, 567, 566, 576, 31, 558, 559, 489, 570, 569, 568, 563, 495, 564, 565, 497, 574, 572, 562, 561, 560, 571, 567, 566, 576, 31, 558, 559, 468, 570, 569, 568, 563, 564, 473, 565, 476, 574, 572, 562, 561, 560, 571, 567, 566, 576, 31, 558, 559, 570, 569, 568, 563, 564, 565, 574, 573, 572, 575, 562, 561, 560, 571, 567, 566, 576, 31, 558, 570, 569, 568, 562, 561, 560, 571, 519, 31, 558, 559, 540, 570, 569, 568, 553, 551, 563, 565, 562, 561, 560, 545, 444, 544, 571, 555, 519, 31, 558, 559, 570, 569, 568, 563, 564, 565, 574, 572, 562, 561, 560, 571, 567, 517, 566, 519, 576, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 934, 952, 898, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 906, 952, 924, 31, 888, 906, 952, 924, 961, 1003, 982, 1134, 1084, 1063, 1154, 1033, 1104, 31, 934, 952, 1003, 1084, 31, 961, 1003, 982, 1134, 1033, 31, 898, 924, 982, 1063, 31, 888, 934, 952, 898, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 888, 906, 952, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 888, 934, 952, 898, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 961, 1003, 982, 1134, 1033, 31, 961, 1003, 982, 1134, 1033, 31, 888, 906, 952, 924, 1003, 982, 1134, 1042, 1084, 1063, 1154, 1033, 1104, 31, 934, 952, 1003, 1084, 31, 1042, 1084, 1063, 1154, 1104, 31, 898, 924, 982, 1063, 31, 888, 906, 952, 924, 961, 1003, 982, 1134, 1042, 1084, 1063, 1154, 1033, 1104, 31, 934, 952, 1003, 1084, 31, 898, 924, 982, 1063, 31, 1042, 1084, 1063, 1154, 1104, 31, 1042, 1084, 1063, 1154, 1104, 31, 1114, 1134, 1154, 31, 888, 934, 952, 898, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 888, 906, 952, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 888, 934, 952, 898, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 961, 1003, 982, 1134, 1033, 31, 961, 1003, 982, 1134, 1033, 31, 888, 934, 906, 952, 898, 924, 1003, 982, 1114, 1134, 1084, 1063, 1154, 1013, 1033, 1104, 31, 961, 1003, 982, 1134, 1033, 31, 1042, 1084, 1063, 1154, 1104, 31, 1042, 1084, 1063, 1154, 1104, 31, 1013, 1033, 1104, 31, 1042, 1084, 1063, 1154, 1104, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 906, 906, 906, 906, 906, 906, 906, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31]
def turn4 : List ℕ := [558, 359, 563, 473, 564, 495, 13, 560, 562, 559, 468, 540, 489, 6, 568, 570, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 473, 473, 473, 473, 31, 564, 564, 564, 564, 564, 31, 495, 495, 495, 495, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 566, 566, 566, 566, 566, 31, 567, 567, 567, 567, 567, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 468, 468, 468, 468, 31, 540, 540, 540, 540, 540, 31, 489, 489, 489, 489, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 476, 476, 476, 476, 31, 497, 497, 497, 497, 31, 544, 544, 544, 544, 544, 31, 545, 545, 545, 545, 545, 31, 519, 519, 519, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 572, 572, 572, 572, 572, 31, 574, 574, 574, 574, 574, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 576, 576, 576, 576, 576, 31, 551, 551, 551, 551, 551, 31, 553, 553, 553, 553, 553, 31, 575, 575, 575, 31, 555, 555, 555, 555, 555, 31, 558, 563, 560, 561, 562, 559, 565, 568, 569, 570, 571, 31, 558, 473, 560, 562, 468, 476, 568, 570, 571, 31, 359, 563, 561, 559, 565, 569, 571, 31, 558, 359, 563, 473, 560, 561, 336, 562, 559, 468, 565, 476, 568, 569, 344, 570, 571, 31, 558, 495, 560, 562, 489, 497, 568, 570, 571, 31, 558, 359, 563, 495, 560, 561, 562, 365, 559, 489, 565, 497, 568, 569, 570, 373, 571, 31, 563, 564, 566, 567, 565, 572, 574, 576, 31, 558, 563, 473, 564, 560, 561, 562, 566, 567, 559, 468, 565, 476, 568, 569, 570, 572, 574, 571, 576, 31, 558, 563, 564, 495, 560, 561, 562, 566, 567, 559, 489, 565, 497, 568, 569, 570, 572, 574, 571, 576, 31, 558, 560, 561, 562, 519, 568, 569, 570, 571, 31, 558, 563, 564, 560, 561, 562, 566, 517, 567, 559, 565, 519, 568, 569, 570, 572, 574, 571, 576, 31, 559, 540, 565, 544, 545, 551, 553, 555, 31, 558, 563, 473, 560, 561, 562, 559, 468, 540, 565, 476, 544, 545, 568, 569, 570, 571, 551, 553, 555, 31, 558, 563, 495, 560, 561, 562, 559, 540, 489, 565, 497, 544, 545, 568, 569, 570, 571, 551, 553, 555, 31, 558, 563, 560, 561, 562, 559, 540, 565, 544, 444, 545, 519, 568, 569, 570, 571, 551, 553, 555, 31, 558, 560, 561, 562, 568, 569, 570, 571, 575, 31, 558, 563, 564, 560, 561, 562, 566, 567, 559, 565, 568, 569, 570, 572, 573, 574, 571, 576, 575, 31, 558, 563, 560, 561, 562, 559, 540, 565, 544, 545, 568, 569, 570, 571, 551, 552, 553, 575, 555, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 898, 924, 934, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 906, 924, 952, 31, 888, 906, 924, 952, 1042, 1063, 1084, 1104, 982, 1003, 1033, 1154, 1134, 31, 898, 924, 1063, 982, 31, 1042, 1063, 1084, 1104, 1154, 31, 934, 952, 1084, 1003, 31, 888, 898, 924, 934, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 888, 906, 924, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 888, 898, 924, 934, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 1042, 1063, 1084, 1104, 1154, 31, 1042, 1063, 1084, 1104, 1154, 31, 888, 906, 924, 952, 1063, 1084, 1104, 961, 982, 1003, 1033, 1154, 1134, 31, 898, 924, 1063, 982, 31, 961, 982, 1003, 1033, 1134, 31, 934, 952, 1084, 1003, 31, 888, 906, 924, 952, 1042, 1063, 1084, 1104, 961, 982, 1003, 1033, 1154, 1134, 31, 898, 924, 1063, 982, 31, 934, 952, 1084, 1003, 31, 961, 982, 1003, 1033, 1134, 31, 961, 982, 1003, 1033, 1134, 31, 1013, 1104, 1033, 31, 888, 898, 924, 934, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 888, 906, 924, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 888, 898, 924, 934, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 1042, 1063, 1084, 1104, 1154, 31, 1042, 1063, 1084, 1104, 1154, 31, 888, 898, 906, 924, 934, 952, 1063, 1084, 1013, 1104, 982, 1003, 1033, 1114, 1154, 1134, 31, 1042, 1063, 1084, 1104, 1154, 31, 961, 982, 1003, 1033, 1134, 31, 961, 982, 1003, 1033, 1134, 31, 1114, 1154, 1134, 31, 961, 982, 1003, 1033, 1134, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 906, 906, 906, 906, 906, 906, 906, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31]
def turn5 : List ℕ := [558, 359, 563, 495, 564, 473, 13, 562, 560, 559, 489, 540, 468, 6, 570, 568, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 495, 495, 495, 495, 31, 564, 564, 564, 564, 564, 31, 473, 473, 473, 473, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 567, 567, 567, 567, 567, 31, 566, 566, 566, 566, 566, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 489, 489, 489, 489, 31, 540, 540, 540, 540, 540, 31, 468, 468, 468, 468, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 497, 497, 497, 497, 31, 476, 476, 476, 476, 31, 545, 545, 545, 545, 545, 31, 544, 544, 544, 544, 544, 31, 519, 519, 519, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 574, 574, 574, 574, 574, 31, 572, 572, 572, 572, 572, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 576, 576, 576, 576, 576, 31, 553, 553, 553, 553, 553, 31, 551, 551, 551, 551, 551, 31, 575, 575, 575, 31, 555, 555, 555, 555, 555, 31, 558, 563, 562, 561, 560, 559, 565, 570, 569, 568, 571, 31, 558, 495, 562, 560, 489, 497, 570, 568, 571, 31, 359, 563, 561, 559, 565, 569, 571, 31, 558, 359, 563, 495, 562, 561, 365, 560, 559, 489, 565, 497, 570, 569, 373, 568, 571, 31, 558, 473, 562, 560, 468, 476, 570, 568, 571, 31, 558, 359, 563, 473, 562, 561, 560, 336, 559, 468, 565, 476, 570, 569, 568, 344, 571, 31, 563, 564, 567, 566, 565, 574, 572, 576, 31, 558, 563, 495, 564, 562, 561, 560, 567, 566, 559, 489, 565, 497, 570, 569, 568, 574, 572, 571, 576, 31, 558, 563, 564, 473, 562, 561, 560, 567, 566, 559, 468, 565, 476, 570, 569, 568, 574, 572, 571, 576, 31, 558, 562, 561, 560, 519, 570, 569, 568, 571, 31, 558, 563, 564, 562, 561, 560, 567, 517, 566, 559, 565, 519, 570, 569, 568, 574, 572, 571, 576, 31, 559, 540, 565, 545, 544, 553, 551, 555, 31, 558, 563, 495, 562, 561, 560, 559, 489, 540, 565, 497, 545, 544, 570, 569, 568, 571, 553, 551, 555, 31, 558, 563, 473, 562, 561, 560, 559, 540, 468, 565, 476, 545, 544, 570, 569, 568, 571, 553, 551, 555, 31, 558, 563, 562, 561, 560, 559, 540, 565, 545, 444, 544, 519, 570, 569, 568, 571, 553, 551, 555, 31, 558, 562, 561, 560, 570, 569, 568, 571, 575, 31, 558, 563, 564, 562, 561, 560, 567, 566, 559, 565, 570, 569, 568, 574, 573, 572, 571, 576, 575, 31, 558, 563, 562, 561, 560, 559, 540, 565, 545, 544, 570, 569, 568, 571, 553, 552, 551, 575, 555, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 934, 952, 898, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 906, 952, 924, 31, 888, 906, 952, 924, 1042, 1084, 1063, 1104, 1003, 982, 1033, 1154, 1134, 31, 934, 952, 1084, 1003, 31, 1042, 1084, 1063, 1104, 1154, 31, 898, 924, 1063, 982, 31, 888, 934, 952, 898, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 888, 906, 952, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 888, 934, 952, 898, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 1042, 1084, 1063, 1104, 1154, 31, 1042, 1084, 1063, 1104, 1154, 31, 888, 906, 952, 924, 1084, 1063, 1104, 961, 1003, 982, 1033, 1154, 1134, 31, 934, 952, 1084, 1003, 31, 961, 1003, 982, 1033, 1134, 31, 898, 924, 1063, 982, 31, 888, 906, 952, 924, 1042, 1084, 1063, 1104, 961, 1003, 982, 1033, 1154, 1134, 31, 934, 952, 1084, 1003, 31, 898, 924, 1063, 982, 31, 961, 1003, 982, 1033, 1134, 31, 961, 1003, 982, 1033, 1134, 31, 1013, 1104, 1033, 31, 888, 934, 952, 898, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 888, 906, 952, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 888, 934, 952, 898, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 1042, 1084, 1063, 1104, 1154, 31, 1042, 1084, 1063, 1104, 1154, 31, 888, 934, 906, 952, 898, 924, 1084, 1063, 1013, 1104, 1003, 982, 1033, 1114, 1154, 1134, 31, 1042, 1084, 1063, 1104, 1154, 31, 961, 1003, 982, 1033, 1134, 31, 961, 1003, 982, 1033, 1134, 31, 1114, 1154, 1134, 31, 961, 1003, 982, 1033, 1134, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 906, 906, 906, 906, 906, 906, 906, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31]
def turn6 : List ℕ := [558, 359, 563, 473, 564, 495, 13, 568, 570, 559, 468, 540, 489, 6, 560, 562, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 473, 473, 473, 473, 31, 564, 564, 564, 564, 564, 31, 495, 495, 495, 495, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 572, 572, 572, 572, 572, 31, 574, 574, 574, 574, 574, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 468, 468, 468, 468, 31, 540, 540, 540, 540, 540, 31, 489, 489, 489, 489, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 476, 476, 476, 476, 31, 497, 497, 497, 497, 31, 551, 551, 551, 551, 551, 31, 553, 553, 553, 553, 553, 31, 575, 575, 575, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 566, 566, 566, 566, 566, 31, 567, 567, 567, 567, 567, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 576, 576, 576, 576, 576, 31, 544, 544, 544, 544, 544, 31, 545, 545, 545, 545, 545, 31, 519, 519, 519, 31, 555, 555, 555, 555, 555, 31, 558, 563, 568, 569, 570, 559, 565, 560, 561, 562, 571, 31, 558, 473, 568, 570, 468, 476, 560, 562, 571, 31, 359, 563, 569, 559, 565, 561, 571, 31, 558, 359, 563, 473, 568, 569, 344, 570, 559, 468, 565, 476, 560, 561, 336, 562, 571, 31, 558, 495, 568, 570, 489, 497, 560, 562, 571, 31, 558, 359, 563, 495, 568, 569, 570, 373, 559, 489, 565, 497, 560, 561, 562, 365, 571, 31, 563, 564, 572, 574, 565, 566, 567, 576, 31, 558, 563, 473, 564, 568, 569, 570, 572, 574, 559, 468, 565, 476, 560, 561, 562, 566, 567, 571, 576, 31, 558, 563, 564, 495, 568, 569, 570, 572, 574, 559, 489, 565, 497, 560, 561, 562, 566, 567, 571, 576, 31, 558, 568, 569, 570, 575, 560, 561, 562, 571, 31, 558, 563, 564, 568, 569, 570, 572, 573, 574, 559, 565, 575, 560, 561, 562, 566, 567, 571, 576, 31, 559, 540, 565, 551, 553, 544, 545, 555, 31, 558, 563, 473, 568, 569, 570, 559, 468, 540, 565, 476, 551, 553, 560, 561, 562, 571, 544, 545, 555, 31, 558, 563, 495, 568, 569, 570, 559, 540, 489, 565, 497, 551, 553, 560, 561, 562, 571, 544, 545, 555, 31, 558, 563, 568, 569, 570, 559, 540, 565, 551, 552, 553, 575, 560, 561, 562, 571, 544, 545, 555, 31, 558, 568, 569, 570, 560, 561, 562, 571, 519, 31, 558, 563, 564, 568, 569, 570, 572, 574, 559, 565, 560, 561, 562, 566, 517, 567, 571, 576, 519, 31, 558, 563, 568, 569, 570, 559, 540, 565, 551, 553, 560, 561, 562, 571, 544, 444, 545, 519, 555, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 898, 924, 934, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 906, 924, 952, 31, 888, 906, 924, 952, 1042, 1063, 1084, 1154, 982, 1003, 1134, 1104, 1033, 31, 898, 924, 1063, 982, 31, 1042, 1063, 1084, 1154, 1104, 31, 934, 952, 1084, 1003, 31, 888, 898, 924, 934, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 888, 906, 924, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 888, 898, 924, 934, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 1042, 1063, 1084, 1154, 1104, 31, 1042, 1063, 1084, 1154, 1104, 31, 888, 906, 924, 952, 1063, 1084, 1154, 961, 982, 1003, 1134, 1104, 1033, 31, 898, 924, 1063, 982, 31, 961, 982, 1003, 1134, 1033, 31, 934, 952, 1084, 1003, 31, 888, 906, 924, 952, 1042, 1063, 1084, 1154, 961, 982, 1003, 1134, 1104, 1033, 31, 898, 924, 1063, 982, 31, 934, 952, 1084, 1003, 31, 961, 982, 1003, 1134, 1033, 31, 961, 982, 1003, 1134, 1033, 31, 1114, 1154, 1134, 31, 888, 898, 924, 934, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 888, 906, 924, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 888, 898, 924, 934, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 1042, 1063, 1084, 1154, 1104, 31, 1042, 1063, 1084, 1154, 1104, 31, 888, 898, 906, 924, 934, 952, 1063, 1084, 1114, 1154, 982, 1003, 1134, 1013, 1104, 1033, 31, 1042, 1063, 1084, 1154, 1104, 31, 961, 982, 1003, 1134, 1033, 31, 961, 982, 1003, 1134, 1033, 31, 1013, 1104, 1033, 31, 961, 982, 1003, 1134, 1033, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 906, 906, 906, 906, 906, 906, 906, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31]
def turn7 : List ℕ := [558, 359, 563, 495, 564, 473, 13, 570, 568, 559, 489, 540, 468, 6, 562, 560, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 558, 31, 359, 359, 359, 31, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 563, 31, 495, 495, 495, 495, 31, 564, 564, 564, 564, 564, 31, 473, 473, 473, 473, 31, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 570, 31, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 569, 31, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 568, 31, 574, 574, 574, 574, 574, 31, 572, 572, 572, 572, 572, 31, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 559, 31, 489, 489, 489, 489, 31, 540, 540, 540, 540, 540, 31, 468, 468, 468, 468, 31, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 565, 31, 497, 497, 497, 497, 31, 476, 476, 476, 476, 31, 553, 553, 553, 553, 553, 31, 551, 551, 551, 551, 551, 31, 575, 575, 575, 31, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 562, 31, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 561, 31, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 560, 31, 567, 567, 567, 567, 567, 31, 566, 566, 566, 566, 566, 31, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 571, 31, 576, 576, 576, 576, 576, 31, 545, 545, 545, 545, 545, 31, 544, 544, 544, 544, 544, 31, 519, 519, 519, 31, 555, 555, 555, 555, 555, 31, 558, 563, 570, 569, 568, 559, 565, 562, 561, 560, 571, 31, 558, 495, 570, 568, 489, 497, 562, 560, 571, 31, 359, 563, 569, 559, 565, 561, 571, 31, 558, 359, 563, 495, 570, 569, 373, 568, 559, 489, 565, 497, 562, 561, 365, 560, 571, 31, 558, 473, 570, 568, 468, 476, 562, 560, 571, 31, 558, 359, 563, 473, 570, 569, 568, 344, 559, 468, 565, 476, 562, 561, 560, 336, 571, 31, 563, 564, 574, 572, 565, 567, 566, 576, 31, 558, 563, 495, 564, 570, 569, 568, 574, 572, 559, 489, 565, 497, 562, 561, 560, 567, 566, 571, 576, 31, 558, 563, 564, 473, 570, 569, 568, 574, 572, 559, 468, 565, 476, 562, 561, 560, 567, 566, 571, 576, 31, 558, 570, 569, 568, 575, 562, 561, 560, 571, 31, 558, 563, 564, 570, 569, 568, 574, 573, 572, 559, 565, 575, 562, 561, 560, 567, 566, 571, 576, 31, 559, 540, 565, 553, 551, 545, 544, 555, 31, 558, 563, 495, 570, 569, 568, 559, 489, 540, 565, 497, 553, 551, 562, 561, 560, 571, 545, 544, 555, 31, 558, 563, 473, 570, 569, 568, 559, 540, 468, 565, 476, 553, 551, 562, 561, 560, 571, 545, 544, 555, 31, 558, 563, 570, 569, 568, 559, 540, 565, 553, 552, 551, 575, 562, 561, 560, 571, 545, 544, 555, 31, 558, 570, 569, 568, 562, 561, 560, 571, 519, 31, 558, 563, 564, 570, 569, 568, 574, 572, 559, 565, 562, 561, 560, 567, 517, 566, 571, 576, 519, 31, 558, 563, 570, 569, 568, 559, 540, 565, 553, 551, 562, 561, 560, 571, 545, 444, 544, 519, 555, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 888, 934, 952, 898, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 906, 952, 924, 31, 888, 906, 952, 924, 1042, 1084, 1063, 1154, 1003, 982, 1134, 1104, 1033, 31, 934, 952, 1084, 1003, 31, 1042, 1084, 1063, 1154, 1104, 31, 898, 924, 1063, 982, 31, 888, 934, 952, 898, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 888, 906, 952, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 888, 934, 952, 898, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 1042, 1084, 1063, 1154, 1104, 31, 1042, 1084, 1063, 1154, 1104, 31, 888, 906, 952, 924, 1084, 1063, 1154, 961, 1003, 982, 1134, 1104, 1033, 31, 934, 952, 1084, 1003, 31, 961, 1003, 982, 1134, 1033, 31, 898, 924, 1063, 982, 31, 888, 906, 952, 924, 1042, 1084, 1063, 1154, 961, 1003, 982, 1134, 1104, 1033, 31, 934, 952, 1084, 1003, 31, 898, 924, 1063, 982, 31, 961, 1003, 982, 1134, 1033, 31, 961, 1003, 982, 1134, 1033, 31, 1114, 1154, 1134, 31, 888, 934, 952, 898, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 888, 906, 952, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 888, 934, 952, 898, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 1042, 1084, 1063, 1154, 1104, 31, 1042, 1084, 1063, 1154, 1104, 31, 888, 934, 906, 952, 898, 924, 1084, 1063, 1114, 1154, 1003, 982, 1134, 1013, 1104, 1033, 31, 1042, 1084, 1063, 1154, 1104, 31, 961, 1003, 982, 1134, 1033, 31, 961, 1003, 982, 1134, 1033, 31, 1013, 1104, 1033, 31, 961, 1003, 982, 1134, 1033, 31, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 888, 31, 934, 934, 934, 934, 934, 934, 934, 934, 934, 31, 906, 906, 906, 906, 906, 906, 906, 31, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 952, 31, 898, 898, 898, 898, 898, 898, 898, 898, 898, 31, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 924, 31, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 1042, 31, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 1084, 31, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 1063, 31, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 1114, 31, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 1154, 31, 961, 961, 961, 961, 961, 961, 961, 961, 31, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 1003, 31, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 982, 31, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 1134, 31, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 1013, 31, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 1104, 31, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 1033, 31]
def moves : List (List ℕ) := [turn1, turn2, turn3, turn4, turn5, turn6, turn7]

def stepWords : List ℕ := rawP.map fun x => x &&& mz 4
lemma stepWords_iff {x : ℕ} : x ∈ stepWords ↔ x ∈ WZ [] 4 := by
  simp only [stepWords, WZ, rawL, List.map_nil, List.append_nil, Set.mem_setOf_eq, List.mem_map]
  exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))

def turnOK (p : List ℕ) : Bool :=
  decide (routeRows p (mz 4) = mz 4 ∧ routeRows p (tz 4) = tz 4) &&
  stepWords.all (fun x => decide (routeRows p (routeRows p x) = x ∧ routeRows p x ∈ stepWords))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn1 : turnOK turn1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn2 : turnOK turn2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn3 : turnOK turn3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn4 : turnOK turn4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn5 : turnOK turn5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn6 : turnOK turn6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validTurn7 : turnOK turn7 = true := by decide +kernel
lemma validTurn {p : List ℕ} (hp : p ∈ moves) : turnOK p = true := by
  simp only [moves,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact validTurn1
  · exact validTurn2
  · exact validTurn3
  · exact validTurn4
  · exact validTurn5
  · exact validTurn6
  · exact validTurn7

lemma motion {p : List ℕ} (hp : p ∈ moves) :
    routeRows p (mz 4) = mz 4 ∧ routeRows p (tz 4) = tz 4 ∧
    ∀ x ∈ WZ [] 4, Stable p x ∧ routeRows p x ∈ WZ [] 4 := by
  have ok := validTurn hp
  simp only [turnOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at ok
  refine ⟨ok.1.1,ok.1.2,?_⟩
  intro x hx
  have h := ok.2 x (stepWords_iff.mpr hx)
  exact ⟨h.1,stepWords_iff.mp h.2⟩

lemma moveSet {p : List ℕ} (hp : p ∈ moves) {x : ℕ} (hx : x ∈ C (mz 4) (WZ [] 4)) :
    Stable p x ∧ routeRows p x ∈ C (mz 4) (WZ [] 4) := by
  obtain ⟨mask,_,words⟩ := motion hp
  rcases hx with hx | hc
  · obtain ⟨h1,h2⟩ := words x hx
    exact ⟨h1, Or.inl h2⟩
  · change x = 0 ∨ x = mz 4 at hc
    rcases hc with e | e
    · rw [e]
      exact ⟨by simp only [Stable,route_zero],Or.inr (by rw [route_zero]; exact Or.inl rfl)⟩
    · rw [e]
      exact ⟨by simp only [Stable,mask],Or.inr (by rw [mask]; exact Or.inr rfl)⟩


def stocked (d : Bool) (a b : ℕ) : Bool :=
  six.any fun e => Nat.beq (op d a b) (xw e &&& mz 4)
def turnStock (d : Bool) (a b : ℕ) : Bool :=
  decide (a = b ∨ a = 0 ∨ b = 0) || stocked d a b ||
    moves.any (fun p => stocked d (routeRows p a) (routeRows p b))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem allChoices : stepWords.all (fun a => stepWords.all (fun b =>
    turnStock false a b && turnStock true a b)) = true := by decide +kernel
lemma rz_iff {w : ℕ} : RZ [] 4 w ≠ 0 ↔ w ∈ WZ [] 4 := by
  classical
  by_cases h : w ∈ WZ [] 4 <;> simp [RZ,h]

def augmented (e : ℕ × ℕ) : List ℕ := (rawL [e]).map fun x => x &&& mz 4
lemma augmented_iff {e : ℕ × ℕ} {x : ℕ} : x ∈ augmented e ↔ x ∈ WZ [e] 4 := by
  simp only [augmented,WZ,Set.mem_setOf_eq,List.mem_map]
  exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))

lemma augMotion {p : List ℕ} {e : ℕ × ℕ} (hp : p ∈ moves)
    (stays : routeRows p (xw e &&& mz 4) = xw e &&& mz 4) {x : ℕ} (hx : x ∈ WZ [e] 4) :
    Stable p x ∧ routeRows p x ∈ WZ [e] 4 := by
  obtain ⟨w,hm,rfl⟩ := hx
  simp only [rawL,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton] at hm
  rcases hm with hm | rfl
  · have old : w &&& mz 4 ∈ WZ [] 4 := ⟨w,by simp [rawL,hm],rfl⟩
    obtain ⟨st,ww⟩ := (motion hp).2.2 _ old
    obtain ⟨v,hv,hs⟩ := ww
    have vmem : v ∈ rawP := by simpa [rawL] using hv
    exact ⟨st, v,by simp [rawL,vmem],hs⟩
  · exact ⟨by simp only [Stable,stays],by rw [stays]; exact ⟨xw e,by simp [rawL],rfl⟩⟩

lemma augSetMotion {p : List ℕ} {e : ℕ × ℕ} (hp : p ∈ moves)
    (stays : routeRows p (xw e &&& mz 4) = xw e &&& mz 4) {x : ℕ} (hx : x ∈ C (mz 4) (WZ [e] 4)) :
    Stable p x ∧ routeRows p x ∈ C (mz 4) (WZ [e] 4) := by
  rcases hx with hx | hx
  · obtain ⟨st,ww⟩ := augMotion hp stays hx
    exact ⟨st,Or.inl ww⟩
  · have mask := (motion hp).1
    change x = 0 ∨ x = mz 4 at hx
    rcases hx with h | h
    · rw [h]
      exact ⟨by simp only [Stable,route_zero],Or.inr (by rw [route_zero]; exact Or.inl rfl)⟩
    · rw [h]
      exact ⟨by simp only [Stable,mask],Or.inr (by rw [mask]; exact Or.inr rfl)⟩

def augPair (e : ℕ × ℕ) (picks : List (ℕ × ℕ)) (a b : ℕ) : Bool :=
  (decide (a = b) || seen picks a b) || moves.any (fun p =>
    Nat.beq (routeRows p (xw e &&& mz 4)) (xw e &&& mz 4) &&
      seen picks (routeRows p a) (routeRows p b))
def allAug (e : ℕ × ℕ) (picks : List (ℕ × ℕ)) : Bool :=
  (augmented e).all fun a => (augmented e).all fun b => augPair e picks a b

lemma augRz {e : ℕ × ℕ} {w : ℕ} : RZ [e] 4 w ≠ 0 ↔ w ∈ WZ [e] 4 := by
  classical
  by_cases h : w ∈ WZ [e] 4 <;> simp [RZ,h]

def wireOf (e : ℕ × ℕ) : ℕ := xw e &&& mz 4
def bank (w : ℕ) : Set ℕ := insert w (C (mz 4) (WZ [] 4))
def ruled (w : ℕ) : Prop := ∀ {k : ℕ} {S : Finset ℕ}, k ≤ 12 → (S : Set ℕ) ⊆ bank w →
  Live Z0 (mz 4) (tz 4) k 1 S → False

lemma bank_single (e : ℕ × ℕ) : C (mz 4) (WZ [e] 4) = bank (wireOf e) := by
  ext x
  constructor
  · rintro (⟨w,hw,rfl⟩ | hc)
    · simp only [rawL,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inr (Or.inl ⟨w,by simpa [rawL] using hw,rfl⟩)
      · exact Or.inl rfl
    · exact Or.inr (Or.inr hc)
  · rintro (rfl | ⟨w,hw,rfl⟩ | hc)
    · exact Or.inl ⟨xw e,by simp [rawL],rfl⟩
    · have h : w ∈ rawP := by simpa [rawL] using hw
      exact Or.inl ⟨w,by simp [rawL,h],rfl⟩
    · exact Or.inr hc

lemma ruled_case (e : ℕ × ℕ) (closed : ∀ {S : Finset ℕ}, (S : Set ℕ) ⊆ C (mz 4) (WZ [e] 4) →
    Live Z0 (mz 4) (tz 4) 12 1 S → False) : ruled (wireOf e) := by
  intro k S hk hS run
  rw [← bank_single] at hS
  by_cases h : k = 12
  · subst k
    exact closed hS run
  · exact supplied e face_low k (by omega) (run.sol.mono le_rfl hS)

lemma ruled_turn {w : ℕ} {p : List ℕ} (hp : p ∈ moves) (hw : Stable p w)
    (known : ruled (routeRows p w)) : ruled w := by
  intro k S hk hS run
  obtain ⟨mask,target,_⟩ := motion hp
  have hs : ∀ x ∈ S, Stable p x := by
    intro x hx
    rcases hS hx with eq | h
    · rw [eq]
      exact hw
    · exact (moveSet hp h).1
  have run' := run.turn p (show Stable p (mz 4) by simp only [Stable,mask]) hs
  rw [mask,target] at run'
  apply known hk _ run'
  intro x hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  rcases hS hv with eq | h
  · exact Or.inl (congrArg (routeRows p) eq)
  · exact Or.inr (moveSet hp h).2

lemma wireStable (e : ℕ × ℕ) {p : List ℕ} (hp : p ∈ moves) : Stable p (wireOf e) := by
  unfold wireOf xw
  rw [and_op]
  exact stable_op _ (moveSet hp (pinAt (e.1 % 8) 4)).1 (moveSet hp (pinAt e.2 4)).1

def inOrbit (f e : ℕ × ℕ) : Bool := Nat.beq (wireOf f) (wireOf e) ||
  moves.any (fun p => Nat.beq (routeRows p (wireOf f)) (wireOf e))
lemma orbitRuled {fs : List (ℕ × ℕ)} {e : ℕ × ℕ} (cert : fs.all (fun f => inOrbit f e) = true)
    (known : ruled (wireOf e)) : ∀ f ∈ fs, ruled (wireOf f) := by
  intro f hf
  have h := List.all_eq_true.mp cert f hf
  simp only [inOrbit,Bool.or_eq_true] at h
  rcases h with eq | moved
  · rwa [Nat.eq_of_beq_eq_true eq]
  · obtain ⟨p,hp,eq⟩ := List.any_eq_true.mp moved
    apply ruled_turn hp (wireStable f hp)
    rwa [Nat.eq_of_beq_eq_true eq]

lemma listRuled {A B : List (ℕ × ℕ)} (ha : ∀ f ∈ A, ruled (wireOf f))
    (hb : ∀ f ∈ B, ruled (wireOf f)) : ∀ f ∈ A ++ B, ruled (wireOf f) := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · exact ha f h
  · exact hb f h

lemma swapBlocked {e : ℕ × ℕ} {S U : Finset ℕ} {d : Bool} {a b w : ℕ}
    (known : ruled w) (out : op d a b = w) (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [e] 4))
    (gate : Bi Z0 d a b S U) (tail : Live Z0 (mz 4) (tz 4) 11 1 U) : False := by
  let l := rawP.getD (e.1 % 8) 0 &&& mz 4
  let r := rawP.getD e.2 0 &&& mz 4
  let pol := decide (e.1 < 8)
  have made : op pol l r = wireOf e := (and_op _ _ _ _).symm
  have hl : l ∈ C (mz 4) (WZ [] 4) := pinAt _ _
  have hr : r ∈ C (mz 4) (WZ [] 4) := pinAt _ _
  have sub : ∀ x ∈ U, x = wireOf e ∨ x ∈ bank w := by
    intro x hx
    rcases Finset.mem_insert.mp (gate.sub.2.2 hx) with rfl | hp
    · exact Or.inr (Or.inl out)
    · have h := hS hp
      rw [bank_single] at h
      exact h.elim Or.inl (fun v => Or.inr (Or.inr v))
  by_cases hn : wireOf e ∈ U
  · by_cases same : l = r
    · have eq : wireOf e = l := made.symm.trans (by rw [← same,op_self])
      apply known (by decide) _ tail
      intro x hx
      rcases sub x hx with h | h
      · rw [h,eq]
        exact Or.inr hl
      · exact h
    · have extended : Live Z0 (mz 4) (tz 4) 12 1 (insert l (insert r (U.erase (wireOf e)))) := by
        apply Live.bi (d := pol) same (al0 _ _ _)
        rw [made,Finset.insert_erase hn]
        exact tail
      apply known (by decide) _ extended
      intro x hx
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_erase] at hx
      rcases hx with rfl | rfl | ⟨hne,hx⟩
      · exact Or.inr hl
      · exact Or.inr hr
      · exact (sub x hx).resolve_left hne
  · apply known (by decide) _ tail
    intro x hx
    exact (sub x hx).resolve_left (fun eq => hn (eq ▸ hx))

def oldOp (prior : List (ℕ × ℕ)) (d : Bool) (a b : ℕ) : Bool :=
  prior.any fun f => Nat.beq (op d a b) (wireOf f)
def orderedPairs (prior : List (ℕ × ℕ)) (e : ℕ × ℕ) (picks : List (ℕ × ℕ)) : Bool :=
  (augmented e).all (fun a => (augmented e).all (fun b =>
    (oldOp prior false a b && oldOp prior true a b) || augPair e picks a b))

def paint (p : ℕ) (w : W) : W := ⟨w.s,w.a,w.b,w.c,if Nat.beq w.s p then 0 else 3⟩
def originalWords (P : List ℕ) (m : ℕ) (A : List ℕ) (p : ℕ) := (avl P m A).map (paint p)
lemma originalSpec (P : List ℕ) (m : ℕ) (A : List ℕ) (p : ℕ) : Srt (originalWords P m A p) ∧
    (∀ w ∈ originalWords P m A p, ∃ x ∈ A, w = paint p (mkW P (x &&& m))) ∧
    ∀ x ∈ A, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ originalWords P m A p, w.s = x &&& m := by
  obtain ⟨order,lift,complete⟩ := avl_spec P m A
  constructor
  · exact List.pairwise_map.mpr order
  constructor
  · intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    obtain ⟨x,hx,rfl⟩ := lift v hv
    exact ⟨x,hx,rfl⟩
  · intro x hx z m'
    obtain ⟨w,hw,eq⟩ := complete x hx z m'
    exact ⟨_,List.mem_map_of_mem hw,eq⟩

lemma paintOk (P : List ℕ) (p x : ℕ) : WOk P (paint p (mkW P x)) := by
  have h := mkW_ok P x
  exact ⟨h.pa,h.pb,h.ec,h.ca,h.cb⟩

lemma rawIn {x Z : ℕ} (E : List (ℕ × ℕ)) (h : x ∈ WZ [] Z) : x ∈ WZ E Z := by
  obtain ⟨w,hw,rfl⟩ := h
  have h : w ∈ rawP := by simpa [rawL] using hw
  exact ⟨w,by simp [rawL,h],rfl⟩
noncomputable def rootChk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (originalWords P m (rawL E) p) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
theorem rootChosen {E Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (fresh : pwr E Z ∉ WZ [] Z) (hE : E = [] ∨ ∃ e ∈ six, E = [e] ∧ Imp [] Z L) (hp : pOk Z Q = true) (hL : L ≤ 15)
    (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (hk : k < L) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ E Z)) (hl : Live Z0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)))
    (hb : (∃ e ∈ Q, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ), (∃ p ∈ M, Nat.beq p.2 1 = true) ∧ Beg (fun a b => seen M a b = true) (RZ [] Z) (mz Z) (tz Z) k t S ∧ ∀ p ∈ M, rootChk E Q Z (L - 1) t p.1 p.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ E Z := by
    intro x hx
    rcases hS hx with h | h
    · exact h
    · simp at h; rcases h with rfl | rfl
      · exact absurd hx h0
      · exact absurd hx h1
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol Z0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  have hpw : pwr E Z = 0 ∨ pwr E Z ∈ S := by
    rcases hE with rfl | ⟨e, he, rfl, hraw⟩
    · exact Or.inl rfl
    · by_contra hc
      push Not at hc
      refine hraw k (by omega) (hl.sol.mono le_rfl ?_)
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      simp only [rawL, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
      · have hx : xw e &&& mz Z ∈ S := by simpa using hx
        exact absurd (show pwr [e] Z ∈ S from hx) hc.2
  obtain ⟨M, hMf, hfront, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := originalSpec (PZ Q) (mz Z) (rawL E) (pwr E Z)
  set v := (originalWords (PZ Q) (mz Z) (rawL E) (pwr E Z)).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (originalWords (PZ Q) (mz Z) (rawL E) (pwr E Z)) := List.filter_sublist
  have hnd : (v.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact (a1.sublist hsub).imp fun h => Nat.ne_of_gt h
  have hrep : Rep v S := by
    refine ⟨hnd, Finset.ext fun x => ?_⟩
    rw [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hv, List.mem_filter] at hw; simpa using hw.2
    · intro hx
      obtain ⟨w, hw, rfl⟩ := hSW hx
      obtain ⟨w', hw', e⟩ := a3 w hw (fun e => h0 (e ▸ hx)) (fun e => h1 (e ▸ hx))
      exact ⟨w', by rw [hv, List.mem_filter]; exact ⟨hw', by simpa [e] using hx⟩, e⟩
  have hwok : ∀ w ∈ v, WOk (PZ Q) w := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact paintOk _ _ _
  have hcod : ∀ w ∈ v, w.r = RZ [] Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    change (if Nat.beq (x &&& mz Z) (pwr E Z) then 0 else 3) = RZ [] Z (x &&& mz Z)
    by_cases same : x &&& mz Z = pwr E Z
    · rw [same]
      simp only [Nat.beq_refl,if_true,RZ,if_neg fresh]
    · have eq : Nat.beq (x &&& mz Z) (pwr E Z) = false := by
        cases h : Nat.beq (x &&& mz Z) (pwr E Z) with
        | false => rfl
        | true => exact (same (Nat.eq_of_beq_eq_true h)).elim
      have raw : x ∈ rawP := by
        rcases hE with rfl | ⟨e,_,rfl,_⟩
        · simpa [rawL] using hx
        · simp only [rawL,List.map_cons,List.map_nil,List.mem_append,List.mem_singleton] at hx
          exact hx.resolve_right (fun h => same (h ▸ rfl))
      have here : x &&& mz Z ∈ WZ [] Z := ⟨x,by simpa [rawL] using raw,rfl⟩
      simp [eq,RZ,here]
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (rawL_sub hE6 hx) Z
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, L - 1)).1 ∧ Q.getD j (0, L - 1) ∈ Q := by
    intro j hj
    rw [hPlen] at hj
    simp [PZ, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
  have X : Ctx (PZ Q) (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (tz Z) := by
    refine ⟨fun i hi => lz_lg Z i hi, fun j hj => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hPget j hj
      have h3 := hproj _ e2
      rw [e1, tz_sub h3.1]; exact h3
    · rw [pL_pk, List.length_map, hPlen]
      refine pk_congr fun j hj => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
  have hcl : Cl (PZ Q) (tz Z) (L - 1) (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos t) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ (L - 1)) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ L - 1 + 1 - t; omega)
  have hhas : hasP (pwr E Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [rootChk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine chosenTop X (RZ_R [] Z) (RZ_R2 [] Z) hMf all hst hcod (by omega) hl hfront ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl (rawIn E hx)
  · exact Or.inl (hSW hx)
  · exact Or.inr hx



def pastGate (prior : List (ℕ × ℕ)) (e : ℕ × ℕ) (d : Bool) (a b : ℕ) : Bool :=
  Nat.beq (op d a b) (wireOf e) || oldOp prior d a b
def rawPairs (prior : List (ℕ × ℕ)) (e : ℕ × ℕ) (picks : List (ℕ × ℕ)) : Bool :=
  stepWords.all (fun a => stepWords.all (fun b =>
    (pastGate prior e false a b && pastGate prior e true a b) || augPair e picks a b))
lemma repeatBlocked {e : ℕ × ℕ} {S U : Finset ℕ} {d : Bool} {a b : ℕ}
    (out : op d a b = wireOf e) (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [e] 4))
    (gate : Bi Z0 d a b S U) (tail : Live Z0 (mz 4) (tz 4) 11 1 U) : False := by
  apply supplied e face_low 11 (by decide)
  apply tail.sol.mono le_rfl
  intro x hx
  rcases Finset.mem_insert.mp (gate.sub.2.2 hx) with rfl | hx
  · rw [out,bank_single]
    exact Or.inl rfl
  · exact hS hx
lemma rootAug {e : ℕ × ℕ} (he : e ∈ six) (hf : pwr [e] 4 ∉ stepWords) {Q picks prior : List (ℕ × ℕ)}
    (earlier : ∀ f ∈ prior, ruled (wireOf f))
    (sane : pOk 4 Q = true) (lower : ∀ a ∈ Q, Imp [e] a.1 a.2)
    (u : ∃ p ∈ picks, Nat.beq p.2 1 = true) (cover : rawPairs prior e picks = true)
    (checked : ∀ p ∈ picks, rootChk [e] Q 4 12 1 p.1 p.2 = false)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [e] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  have low := supplied e face_low
  have applyCase : ∀ {A : Finset ℕ}, (A : Set ℕ) ⊆ C (mz 4) (WZ [e] 4) →
      Live Z0 (mz 4) (tz 4) 12 1 A →
      Beg (fun a b => seen picks a b = true) (RZ [] 4) (mz 4) (tz 4) 12 1 A → False := by
    intro A ha run start
    apply rootChosen (L := 13) (fun h => hf (stepWords_iff.mpr h)) (Or.inr ⟨e,he,rfl,face_low⟩) sane (by norm_num) lower (by omega) ha run low
    exact Or.inr ⟨picks,u,start,checked⟩
  have hm : ∀ q < 12, ¬ Sol Z0 (mz 4) (tz 4) q (C (mz 4) ({x | RZ [] 4 x ≠ 0} ∪ (S : Set ℕ))) := by
    intro q hq proof
    apply low q hq
    apply proof.mono le_rfl
    rintro x ((hx | hx) | hx)
    · exact Or.inl (rawIn [e] (rz_iff.mp hx))
    · exact hS hx
    · exact Or.inr hx
  rcases front (RZ_R2 [] 4) hl hm with direct | ⟨q,d,a,b,U,hq,ha,hb,gate,tail⟩
  · exact applyCase hS hl (Or.inl direct)
  have eq : q = 11 := by omega
  subst q
  have haW := rz_iff.mp ha
  have hbW := rz_iff.mp hb
  have c := List.all_eq_true.mp (List.all_eq_true.mp cover a (stepWords_iff.mpr haW)) b (stepWords_iff.mpr hbW)
  simp only [Bool.or_eq_true,Bool.and_eq_true] at c
  rcases c with before | c
  · have known : pastGate prior e d a b = true := by
      cases d
      · exact before.1
      · exact before.2
    simp only [pastGate,Bool.or_eq_true] at known
    rcases known with same | old
    · exact repeatBlocked (Nat.eq_of_beq_eq_true same) hS gate tail
    · obtain ⟨f,mem,eq⟩ := List.any_eq_true.mp old
      exact swapBlocked (earlier f mem) (Nat.eq_of_beq_eq_true eq) hS gate tail
  · simp only [augPair,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true] at c
    rcases c with (same | keep) | ⟨p,hp,fix,hit⟩
    · exact gate.1 same
    · exact applyCase hS hl (Or.inr ⟨11,d,a,b,U,rfl,ha,hb,keep,gate,tail⟩)
    · have stays := Nat.eq_of_beq_eq_true fix
      obtain ⟨mask,target,_⟩ := motion hp
      have hs : ∀ x ∈ S, Stable p x := fun _ hx => (augSetMotion hp stays (hS hx)).1
      have g' := gate.turn p hs
      have t' := tail.turn p (show Stable p (mz 4) by simp only [Stable,mask]) (gate.afterStable hs)
      rw [mask,target] at t'
      refine applyCase ?_ (g'.live t') ?_
      · intro x hx
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
        exact (augSetMotion hp stays (hS hv)).2
      · exact Or.inr ⟨11,d,_,_,_,rfl,rz_iff.mpr ((motion hp).2.2 a haW).2,
          rz_iff.mpr ((motion hp).2.2 b hbW).2,hit,g',t'⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closedUnary : query13 1 0 1 = false := by decide +kernel
def keep0d3 : List ℕ := [86, 4166, 16406]
def rung0d3 := grade rt3 keep0d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed0d3 : ∀ a ∈ rung0d3, Imp [(8, 1)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep0d2 : List ℕ := [7, 13, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung0d2 := grade rt2 keep0d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed0d2 : ∀ a ∈ rung0d2, Imp [(8, 1)] a.1 a.2 :=
  grade_ok (prior := rung0d3) (by decide) valid2 validSeed0d3 (by decide +kernel)
def keep0d1 : List ℕ := [5, 6, 12, 20, 36, 68, 132, 260, 516, 2052, 4100, 8196, 16388, 32772]
def rung0d1 := grade rt1 keep0d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed0d1 : ∀ a ∈ rung0d1, Imp [(8, 1)] a.1 a.2 :=
  grade_ok (prior := (rung0d2 ++ rung0d3)) (by decide) valid1 (apI validSeed0d2 validSeed0d3) (by decide +kernel)
def cuts0 := rung0d1 ++ rung0d2 ++ rung0d3
lemma marks0 : ∀ a ∈ cuts0, Imp [(8, 1)] a.1 a.2 := apI (apI validSeed0d1 validSeed0d2) validSeed0d3
def keep1d3 : List ℕ := [86, 4166, 16406]
def rung1d3 := grade rt3 keep1d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed1d3 : ∀ a ∈ rung1d3, Imp [(0, 1)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep1d2 : List ℕ := [7, 13, 14, 21, 22, 37, 38, 69, 70, 133, 134, 164, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 8197, 8198, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 32773, 32774]
def rung1d2 := grade rt2 keep1d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed1d2 : ∀ a ∈ rung1d2, Imp [(0, 1)] a.1 a.2 :=
  grade_ok (prior := rung1d3) (by decide) valid2 validSeed1d3 (by decide +kernel)
def keep1d1 : List ℕ := [5, 6, 260, 516, 2052, 4100, 16388]
def rung1d1 := grade rt1 keep1d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed1d1 : ∀ a ∈ rung1d1, Imp [(0, 1)] a.1 a.2 :=
  grade_ok (prior := (rung1d2 ++ rung1d3)) (by decide) valid1 (apI validSeed1d2 validSeed1d3) (by decide +kernel)
def cuts1 := rung1d1 ++ rung1d2 ++ rung1d3
lemma marks1 : ∀ a ∈ cuts1, Imp [(0, 1)] a.1 a.2 := apI (apI validSeed1d1 validSeed1d2) validSeed1d3
def keep2d3 : List ℕ := []
def rung2d3 := grade rt3 keep2d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed2d3 : ∀ a ∈ rung2d3, Imp [(8, 3)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep2d2 : List ℕ := [7, 13, 14, 21, 28, 37, 44, 69, 76, 133, 140, 262, 268, 276, 292, 324, 388, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4108, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16396, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung2d2 := grade rt2 keep2d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed2d2 : ∀ a ∈ rung2d2, Imp [(8, 3)] a.1 a.2 :=
  grade_ok (prior := rung2d3) (by decide) valid2 validSeed2d3 (by decide +kernel)
def keep2d1 : List ℕ := [5, 12, 260, 2052, 8196, 32772]
def rung2d1 := grade rt1 keep2d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed2d1 : ∀ a ∈ rung2d1, Imp [(8, 3)] a.1 a.2 :=
  grade_ok (prior := (rung2d2 ++ rung2d3)) (by decide) valid1 (apI validSeed2d2 validSeed2d3) (by decide +kernel)
def cuts2 := rung2d1 ++ rung2d2 ++ rung2d3
lemma marks2 : ∀ a ∈ cuts2, Imp [(8, 3)] a.1 a.2 := apI (apI validSeed2d1 validSeed2d2) validSeed2d3
def keep3d3 : List ℕ := []
def rung3d3 := grade rt3 keep3d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed3d3 : ∀ a ∈ rung3d3, Imp [(0, 3)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep3d2 : List ℕ := [7, 13, 14, 21, 28, 37, 44, 69, 76, 133, 140, 164, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4108, 4356, 6148, 8197, 8204, 16389, 16396, 16644, 18436, 32773, 32780]
def rung3d2 := grade rt2 keep3d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed3d2 : ∀ a ∈ rung3d2, Imp [(0, 3)] a.1 a.2 :=
  grade_ok (prior := rung3d3) (by decide) valid2 validSeed3d3 (by decide +kernel)
def keep3d1 : List ℕ := [5, 12, 260, 516, 2052]
def rung3d1 := grade rt1 keep3d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed3d1 : ∀ a ∈ rung3d1, Imp [(0, 3)] a.1 a.2 :=
  grade_ok (prior := (rung3d2 ++ rung3d3)) (by decide) valid1 (apI validSeed3d2 validSeed3d3) (by decide +kernel)
def cuts3 := rung3d1 ++ rung3d2 ++ rung3d3
lemma marks3 : ∀ a ∈ cuts3, Imp [(0, 3)] a.1 a.2 := apI (apI validSeed3d1 validSeed3d2) validSeed3d3
def keep4d3 : List ℕ := [86, 4166, 16406]
def rung4d3 := grade rt3 keep4d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed4d3 : ∀ a ∈ rung4d3, Imp [(8, 4)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep4d2 : List ℕ := [7, 13, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung4d2 := grade rt2 keep4d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed4d2 : ∀ a ∈ rung4d2, Imp [(8, 4)] a.1 a.2 :=
  grade_ok (prior := rung4d3) (by decide) valid2 validSeed4d3 (by decide +kernel)
def keep4d1 : List ℕ := [5, 6, 12, 20, 36, 68, 132, 260, 516, 2052, 4100, 8196, 16388, 32772]
def rung4d1 := grade rt1 keep4d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed4d1 : ∀ a ∈ rung4d1, Imp [(8, 4)] a.1 a.2 :=
  grade_ok (prior := (rung4d2 ++ rung4d3)) (by decide) valid1 (apI validSeed4d2 validSeed4d3) (by decide +kernel)
def cuts4 := rung4d1 ++ rung4d2 ++ rung4d3
lemma marks4 : ∀ a ∈ cuts4, Imp [(8, 4)] a.1 a.2 := apI (apI validSeed4d1 validSeed4d2) validSeed4d3
def keep5d3 : List ℕ := [86, 4166, 16406]
def rung5d3 := grade rt3 keep5d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed5d3 : ∀ a ∈ rung5d3, Imp [(0, 4)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep5d2 : List ℕ := [7, 13, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 32773, 32774, 32780, 32804, 36868]
def rung5d2 := grade rt2 keep5d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed5d2 : ∀ a ∈ rung5d2, Imp [(0, 4)] a.1 a.2 :=
  grade_ok (prior := rung5d3) (by decide) valid2 validSeed5d3 (by decide +kernel)
def keep5d1 : List ℕ := [5, 6, 12, 20, 36, 68, 132, 260, 516, 2052, 4100, 8196, 16388, 32772]
def rung5d1 := grade rt1 keep5d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed5d1 : ∀ a ∈ rung5d1, Imp [(0, 4)] a.1 a.2 :=
  grade_ok (prior := (rung5d2 ++ rung5d3)) (by decide) valid1 (apI validSeed5d2 validSeed5d3) (by decide +kernel)
def cuts5 := rung5d1 ++ rung5d2 ++ rung5d3
lemma marks5 : ∀ a ∈ cuts5, Imp [(0, 4)] a.1 a.2 := apI (apI validSeed5d1 validSeed5d2) validSeed5d3
def keep6d3 : List ℕ := []
def rung6d3 := grade rt3 keep6d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed6d3 : ∀ a ∈ rung6d3, Imp [(8, 5)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep6d2 : List ℕ := [7, 13, 21, 28, 37, 38, 44, 52, 69, 76, 84, 100, 133, 164, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4132, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16420, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung6d2 := grade rt2 keep6d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed6d2 : ∀ a ∈ rung6d2, Imp [(8, 5)] a.1 a.2 :=
  grade_ok (prior := rung6d3) (by decide) valid2 validSeed6d3 (by decide +kernel)
def keep6d1 : List ℕ := [5, 12, 20, 36, 68, 260, 516, 2052, 8196, 32772]
def rung6d1 := grade rt1 keep6d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed6d1 : ∀ a ∈ rung6d1, Imp [(8, 5)] a.1 a.2 :=
  grade_ok (prior := (rung6d2 ++ rung6d3)) (by decide) valid1 (apI validSeed6d2 validSeed6d3) (by decide +kernel)
def cuts6 := rung6d1 ++ rung6d2 ++ rung6d3
lemma marks6 : ∀ a ∈ cuts6, Imp [(8, 5)] a.1 a.2 := apI (apI validSeed6d1 validSeed6d2) validSeed6d3
def keep7d3 : List ℕ := []
def rung7d3 := grade rt3 keep7d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed7d3 : ∀ a ∈ rung7d3, Imp [(0, 5)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep7d2 : List ℕ := [7, 13, 21, 28, 37, 38, 44, 52, 69, 76, 100, 133, 140, 164, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2084, 4101, 4132, 4356, 8197, 8198, 8204, 8324, 12292, 16389, 16420, 16644, 24580, 32773, 32804]
def rung7d2 := grade rt2 keep7d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed7d2 : ∀ a ∈ rung7d2, Imp [(0, 5)] a.1 a.2 :=
  grade_ok (prior := rung7d3) (by decide) valid2 validSeed7d3 (by decide +kernel)
def keep7d1 : List ℕ := [5, 12, 36, 260, 516, 8196]
def rung7d1 := grade rt1 keep7d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed7d1 : ∀ a ∈ rung7d1, Imp [(0, 5)] a.1 a.2 :=
  grade_ok (prior := (rung7d2 ++ rung7d3)) (by decide) valid1 (apI validSeed7d2 validSeed7d3) (by decide +kernel)
def cuts7 := rung7d1 ++ rung7d2 ++ rung7d3
lemma marks7 : ∀ a ∈ cuts7, Imp [(0, 5)] a.1 a.2 := apI (apI validSeed7d1 validSeed7d2) validSeed7d3
def keep8d3 : List ℕ := [86, 4166, 16406]
def rung8d3 := grade rt3 keep8d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed8d3 : ∀ a ∈ rung8d3, Imp [(9, 4)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep8d2 : List ℕ := [7, 13, 14, 21, 22, 28, 38, 52, 70, 84, 134, 148, 262, 276, 532, 548, 580, 644, 772, 2054, 2068, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung8d2 := grade rt2 keep8d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed8d2 : ∀ a ∈ rung8d2, Imp [(9, 4)] a.1 a.2 :=
  grade_ok (prior := rung8d3) (by decide) valid2 validSeed8d3 (by decide +kernel)
def keep8d1 : List ℕ := [6, 20, 516, 4100, 8196, 16388, 32772]
def rung8d1 := grade rt1 keep8d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed8d1 : ∀ a ∈ rung8d1, Imp [(9, 4)] a.1 a.2 :=
  grade_ok (prior := (rung8d2 ++ rung8d3)) (by decide) valid1 (apI validSeed8d2 validSeed8d3) (by decide +kernel)
def cuts8 := rung8d1 ++ rung8d2 ++ rung8d3
lemma marks8 : ∀ a ∈ cuts8, Imp [(9, 4)] a.1 a.2 := apI (apI validSeed8d1 validSeed8d2) validSeed8d3
def keep9d3 : List ℕ := [86, 4166, 16406]
def rung9d3 := grade rt3 keep9d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed9d3 : ∀ a ∈ rung9d3, Imp [(1, 4)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep9d2 : List ℕ := [7, 14, 21, 22, 28, 38, 52, 69, 70, 76, 84, 100, 134, 148, 196, 262, 276, 324, 532, 548, 580, 644, 772, 2054, 2068, 2116, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16390, 16404, 32773, 32774, 32780, 32804, 36868]
def rung9d2 := grade rt2 keep9d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed9d2 : ∀ a ∈ rung9d2, Imp [(1, 4)] a.1 a.2 :=
  grade_ok (prior := rung9d3) (by decide) valid2 validSeed9d3 (by decide +kernel)
def keep9d1 : List ℕ := [6, 20, 68, 516, 4100, 8196, 32772]
def rung9d1 := grade rt1 keep9d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed9d1 : ∀ a ∈ rung9d1, Imp [(1, 4)] a.1 a.2 :=
  grade_ok (prior := (rung9d2 ++ rung9d3)) (by decide) valid1 (apI validSeed9d2 validSeed9d3) (by decide +kernel)
def cuts9 := rung9d1 ++ rung9d2 ++ rung9d3
lemma marks9 : ∀ a ∈ cuts9, Imp [(1, 4)] a.1 a.2 := apI (apI validSeed9d1 validSeed9d2) validSeed9d3
def keep10d3 : List ℕ := [86, 4166, 16406]
def rung10d3 := grade rt3 keep10d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed10d3 : ∀ a ∈ rung10d3, Imp [(9, 5)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep10d2 : List ℕ := [7, 13, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung10d2 := grade rt2 keep10d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed10d2 : ∀ a ∈ rung10d2, Imp [(9, 5)] a.1 a.2 :=
  grade_ok (prior := rung10d3) (by decide) valid2 validSeed10d3 (by decide +kernel)
def keep10d1 : List ℕ := [5, 6, 12, 20, 36, 68, 132, 260, 516, 2052, 4100, 8196, 16388, 32772]
def rung10d1 := grade rt1 keep10d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed10d1 : ∀ a ∈ rung10d1, Imp [(9, 5)] a.1 a.2 :=
  grade_ok (prior := (rung10d2 ++ rung10d3)) (by decide) valid1 (apI validSeed10d2 validSeed10d3) (by decide +kernel)
def cuts10 := rung10d1 ++ rung10d2 ++ rung10d3
lemma marks10 : ∀ a ∈ cuts10, Imp [(9, 5)] a.1 a.2 := apI (apI validSeed10d1 validSeed10d2) validSeed10d3
def keep11d3 : List ℕ := [86, 4166, 16406]
def rung11d3 := grade rt3 keep11d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed11d3 : ∀ a ∈ rung11d3, Imp [(1, 5)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep11d2 : List ℕ := [7, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 24580, 32774, 32804]
def rung11d2 := grade rt2 keep11d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed11d2 : ∀ a ∈ rung11d2, Imp [(1, 5)] a.1 a.2 :=
  grade_ok (prior := rung11d3) (by decide) valid2 validSeed11d3 (by decide +kernel)
def keep11d1 : List ℕ := [5, 6, 12, 20, 36, 68, 132, 260, 516, 2052, 4100, 8196, 16388]
def rung11d1 := grade rt1 keep11d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed11d1 : ∀ a ∈ rung11d1, Imp [(1, 5)] a.1 a.2 :=
  grade_ok (prior := (rung11d2 ++ rung11d3)) (by decide) valid1 (apI validSeed11d2 validSeed11d3) (by decide +kernel)
def cuts11 := rung11d1 ++ rung11d2 ++ rung11d3
lemma marks11 : ∀ a ∈ cuts11, Imp [(1, 5)] a.1 a.2 := apI (apI validSeed11d1 validSeed11d2) validSeed11d3
def keep12d3 : List ℕ := [86, 4166, 16406]
def rung12d3 := grade rt3 keep12d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed12d3 : ∀ a ∈ rung12d3, Imp [(12, 5)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep12d2 : List ℕ := [7, 13, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung12d2 := grade rt2 keep12d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed12d2 : ∀ a ∈ rung12d2, Imp [(12, 5)] a.1 a.2 :=
  grade_ok (prior := rung12d3) (by decide) valid2 validSeed12d3 (by decide +kernel)
def keep12d1 : List ℕ := [5, 6, 12, 20, 36, 68, 132, 260, 516, 2052, 4100, 8196, 16388, 32772]
def rung12d1 := grade rt1 keep12d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed12d1 : ∀ a ∈ rung12d1, Imp [(12, 5)] a.1 a.2 :=
  grade_ok (prior := (rung12d2 ++ rung12d3)) (by decide) valid1 (apI validSeed12d2 validSeed12d3) (by decide +kernel)
def cuts12 := rung12d1 ++ rung12d2 ++ rung12d3
lemma marks12 : ∀ a ∈ cuts12, Imp [(12, 5)] a.1 a.2 := apI (apI validSeed12d1 validSeed12d2) validSeed12d3
def keep13d3 : List ℕ := [86, 4166, 16406]
def rung13d3 := grade rt3 keep13d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed13d3 : ∀ a ∈ rung13d3, Imp [(4, 5)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep13d2 : List ℕ := [7, 14, 21, 22, 28, 37, 38, 44, 52, 69, 70, 76, 84, 100, 134, 148, 164, 262, 268, 276, 292, 324, 388, 532, 548, 2053, 2054, 2068, 2084, 2116, 2180, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 24580, 32773, 32774, 32780, 32804, 36868]
def rung13d2 := grade rt2 keep13d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed13d2 : ∀ a ∈ rung13d2, Imp [(4, 5)] a.1 a.2 :=
  grade_ok (prior := rung13d3) (by decide) valid2 validSeed13d3 (by decide +kernel)
def keep13d1 : List ℕ := [5, 6, 12, 20, 36, 68, 260, 2052, 4100, 8196, 16388, 32772]
def rung13d1 := grade rt1 keep13d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed13d1 : ∀ a ∈ rung13d1, Imp [(4, 5)] a.1 a.2 :=
  grade_ok (prior := (rung13d2 ++ rung13d3)) (by decide) valid1 (apI validSeed13d2 validSeed13d3) (by decide +kernel)
def cuts13 := rung13d1 ++ rung13d2 ++ rung13d3
lemma marks13 : ∀ a ∈ cuts13, Imp [(4, 5)] a.1 a.2 := apI (apI validSeed13d1 validSeed13d2) validSeed13d3
def keep14d3 : List ℕ := [86, 4166, 16406]
def rung14d3 := grade rt3 keep14d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed14d3 : ∀ a ∈ rung14d3, Imp [(12, 6)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep14d2 : List ℕ := [21, 22, 28, 52, 69, 70, 76, 84, 100, 148, 196, 276, 324, 532, 548, 580, 644, 772, 2068, 2116, 2564, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 36868, 49156]
def rung14d2 := grade rt2 keep14d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed14d2 : ∀ a ∈ rung14d2, Imp [(12, 6)] a.1 a.2 :=
  grade_ok (prior := rung14d3) (by decide) valid2 validSeed14d3 (by decide +kernel)
def keep14d1 : List ℕ := [20, 68, 516, 4100, 16388]
def rung14d1 := grade rt1 keep14d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed14d1 : ∀ a ∈ rung14d1, Imp [(12, 6)] a.1 a.2 :=
  grade_ok (prior := (rung14d2 ++ rung14d3)) (by decide) valid1 (apI validSeed14d2 validSeed14d3) (by decide +kernel)
def cuts14 := rung14d1 ++ rung14d2 ++ rung14d3
lemma marks14 : ∀ a ∈ cuts14, Imp [(12, 6)] a.1 a.2 := apI (apI validSeed14d1 validSeed14d2) validSeed14d3
def keep15d3 : List ℕ := [86, 4166, 16406]
def rung15d3 := grade rt3 keep15d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed15d3 : ∀ a ∈ rung15d3, Imp [(4, 6)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep15d2 : List ℕ := [7, 14, 21, 22, 28, 38, 52, 69, 70, 76, 84, 100, 134, 148, 196, 262, 276, 324, 532, 580, 2054, 2068, 2116, 4101, 4102, 4108, 4132, 4164, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16389, 16390, 16396, 16404, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung15d2 := grade rt2 keep15d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed15d2 : ∀ a ∈ rung15d2, Imp [(4, 6)] a.1 a.2 :=
  grade_ok (prior := rung15d3) (by decide) valid2 validSeed15d3 (by decide +kernel)
def keep15d1 : List ℕ := [6, 20, 68, 4100, 8196, 16388, 32772]
def rung15d1 := grade rt1 keep15d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed15d1 : ∀ a ∈ rung15d1, Imp [(4, 6)] a.1 a.2 :=
  grade_ok (prior := (rung15d2 ++ rung15d3)) (by decide) valid1 (apI validSeed15d2 validSeed15d3) (by decide +kernel)
def cuts15 := rung15d1 ++ rung15d2 ++ rung15d3
lemma marks15 : ∀ a ∈ cuts15, Imp [(4, 6)] a.1 a.2 := apI (apI validSeed15d1 validSeed15d2) validSeed15d3
def keep16d3 : List ℕ := []
def rung16d3 := grade rt3 keep16d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed16d3 : ∀ a ∈ rung16d3, Imp [(13, 7)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep16d2 : List ℕ := [37, 38, 44, 52, 100, 133, 134, 140, 148, 164, 196, 262, 268, 276, 292, 324, 388, 532, 548, 580, 644, 772, 2053, 2054, 2068, 2084, 2116, 2180, 2564, 4132, 4228, 4356, 6148, 8197, 8198, 8204, 8324, 12292, 16420, 16516, 16644, 18436, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung16d2 := grade rt2 keep16d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed16d2 : ∀ a ∈ rung16d2, Imp [(13, 7)] a.1 a.2 :=
  grade_ok (prior := rung16d3) (by decide) valid2 validSeed16d3 (by decide +kernel)
def keep16d1 : List ℕ := [36, 132, 260, 516, 2052, 8196, 32772]
def rung16d1 := grade rt1 keep16d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed16d1 : ∀ a ∈ rung16d1, Imp [(13, 7)] a.1 a.2 :=
  grade_ok (prior := (rung16d2 ++ rung16d3)) (by decide) valid1 (apI validSeed16d2 validSeed16d3) (by decide +kernel)
def cuts16 := rung16d1 ++ rung16d2 ++ rung16d3
lemma marks16 : ∀ a ∈ cuts16, Imp [(13, 7)] a.1 a.2 := apI (apI validSeed16d1 validSeed16d2) validSeed16d3
def keep17d3 : List ℕ := []
def rung17d3 := grade rt3 keep17d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed17d3 : ∀ a ∈ rung17d3, Imp [(5, 7)] a.1 a.2 :=
  grade_ok (prior := []) (by decide) valid3 (by simp) (by decide +kernel)
def keep17d2 : List ℕ := [37, 38, 44, 52, 100, 133, 134, 140, 148, 164, 196, 292, 388, 548, 644, 2084, 2180, 4132, 4228, 8197, 8198, 8204, 8324, 12292, 16420, 16516, 24580, 32773, 32774, 32780, 32804, 36868, 49156]
def rung17d2 := grade rt2 keep17d2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed17d2 : ∀ a ∈ rung17d2, Imp [(5, 7)] a.1 a.2 :=
  grade_ok (prior := rung17d3) (by decide) valid2 validSeed17d3 (by decide +kernel)
def keep17d1 : List ℕ := [36, 132, 8196, 32772]
def rung17d1 := grade rt1 keep17d1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem validSeed17d1 : ∀ a ∈ rung17d1, Imp [(5, 7)] a.1 a.2 :=
  grade_ok (prior := (rung17d2 ++ rung17d3)) (by decide) valid1 (apI validSeed17d2 validSeed17d3) (by decide +kernel)
def cuts17 := rung17d1 ++ rung17d2 ++ rung17d3
lemma marks17 : ∀ a ∈ cuts17, Imp [(5, 7)] a.1 a.2 := apI (apI validSeed17d1 validSeed17d2) validSeed17d3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed4 : chk [(8, 4)] cuts4 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase4 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(8, 4)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(8, 4), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks4 (by omega) hS hl (supplied (8, 4) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed4
def family4 : List (ℕ × ℕ) := [(8, 4), (8, 6), (11, 4), (11, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid4 : ∀ f ∈ family4, ruled (wireOf f) :=
  orbitRuled (e := (8, 4)) (by decide +kernel) (ruled_case (8, 4) (@endCase4))
def past4 := family4
lemma pastValid4 : ∀ f ∈ past4, ruled (wireOf f) := familyValid4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed5 : chk [(0, 4)] cuts5 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase5 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(0, 4)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(0, 4), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks5 (by omega) hS hl (supplied (0, 4) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed5
def family5 : List (ℕ × ℕ) := [(0, 4), (0, 6), (3, 4), (3, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid5 : ∀ f ∈ family5, ruled (wireOf f) :=
  orbitRuled (e := (0, 4)) (by decide +kernel) (ruled_case (0, 4) (@endCase5))
def past5 := past4 ++ family5
lemma pastValid5 : ∀ f ∈ past5, ruled (wireOf f) := listRuled pastValid4 familyValid5

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed12 : chk [(12, 5)] cuts12 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase12 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(12, 5)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(12, 5), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks12 (by omega) hS hl (supplied (12, 5) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed12
def family12 : List (ℕ × ℕ) := [(12, 5), (12, 7), (13, 6), (14, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid12 : ∀ f ∈ family12, ruled (wireOf f) :=
  orbitRuled (e := (12, 5)) (by decide +kernel) (ruled_case (12, 5) (@endCase12))
def past12 := past5 ++ family12
lemma pastValid12 : ∀ f ∈ past12, ruled (wireOf f) := listRuled pastValid5 familyValid12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed13 : chk [(4, 5)] cuts13 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase13 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(4, 5)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(4, 5), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks13 (by omega) hS hl (supplied (4, 5) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed13
def family13 : List (ℕ × ℕ) := [(4, 5), (4, 7), (5, 6), (6, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid13 : ∀ f ∈ family13, ruled (wireOf f) :=
  orbitRuled (e := (4, 5)) (by decide +kernel) (ruled_case (4, 5) (@endCase13))
def past13 := past12 ++ family13
lemma pastValid13 : ∀ f ∈ past13, ruled (wireOf f) := listRuled pastValid12 familyValid13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed10 : chk [(9, 5)] cuts10 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase10 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(9, 5)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(9, 5), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks10 (by omega) hS hl (supplied (9, 5) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed10
def family10 : List (ℕ × ℕ) := [(9, 5), (9, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid10 : ∀ f ∈ family10, ruled (wireOf f) :=
  orbitRuled (e := (9, 5)) (by decide +kernel) (ruled_case (9, 5) (@endCase10))
def past10 := past13 ++ family10
lemma pastValid10 : ∀ f ∈ past10, ruled (wireOf f) := listRuled pastValid13 familyValid10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed11 : chk [(1, 5)] cuts11 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase11 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(1, 5)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(1, 5), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks11 (by omega) hS hl (supplied (1, 5) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed11
def family11 : List (ℕ × ℕ) := [(1, 5), (1, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid11 : ∀ f ∈ family11, ruled (wireOf f) :=
  orbitRuled (e := (1, 5)) (by decide +kernel) (ruled_case (1, 5) (@endCase11))
def past11 := past10 ++ family11
lemma pastValid11 : ∀ f ∈ past11, ruled (wireOf f) := listRuled pastValid10 familyValid11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed0 : chk [(8, 1)] cuts0 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase0 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(8, 1)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(8, 1), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks0 (by omega) hS hl (supplied (8, 1) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed0
def family0 : List (ℕ × ℕ) := [(8, 1), (9, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid0 : ∀ f ∈ family0, ruled (wireOf f) :=
  orbitRuled (e := (8, 1)) (by decide +kernel) (ruled_case (8, 1) (@endCase0))
def past0 := past11 ++ family0
lemma pastValid0 : ∀ f ∈ past0, ruled (wireOf f) := listRuled pastValid11 familyValid0

def cross1 : List (ℕ × ℕ) := [(0x4000,0), (0x8000,0), (0x80000,0), (0x4000000000000,0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x800000000000 64) 0x0) 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover1 : rawPairs past0 (0, 1) cross1 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n0 : rootChk [(0, 1)] cuts1 4 12 1 0x4000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n1 : rootChk [(0, 1)] cuts1 4 12 1 0x8000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n2 : rootChk [(0, 1)] cuts1 4 12 1 0x80000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n3 : rootChk [(0, 1)] cuts1 4 12 1 0x4000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n4 : rootChk [(0, 1)] cuts1 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n5 : rootChk [(0, 1)] cuts1 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n6 : rootChk [(0, 1)] cuts1 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x800000000000 64) 0x0) 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial1n7 : rootChk [(0, 1)] cuts1 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase1 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(0, 1)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (0, 1)) (picks := cross1) (Q := cuts1) (by decide) (by decide +kernel) pastValid0 (by decide) marks1 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover1 _ hS hl
  intro p hp
  simp only [cross1,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rawTrial1n0
  · exact rawTrial1n1
  · exact rawTrial1n2
  · exact rawTrial1n3
  · exact rawTrial1n4
  · exact rawTrial1n5
  · exact rawTrial1n6
  · exact rawTrial1n7
def family1 : List (ℕ × ℕ) := [(0, 1), (1, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid1 : ∀ f ∈ family1, ruled (wireOf f) :=
  orbitRuled (e := (0, 1)) (by decide +kernel) (ruled_case (0, 1) (@endCase1))
def past1 := past0 ++ family1
lemma pastValid1 : ∀ f ∈ past1, ruled (wireOf f) := listRuled pastValid0 familyValid1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem closed6 : chk [(8, 5)] cuts6 4 12 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase6 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(8, 5)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply imp_of_live (L := 13) (Or.inr ⟨(8, 5), by decide, rfl, face_low⟩) (by decide) (by norm_num) marks6 (by omega) hS hl (supplied (8, 5) face_low)
  refine Or.inr ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  have eq : p = (FF,1) := List.mem_singleton.mp hp
  subst p
  exact closed6
def family6 : List (ℕ × ℕ) := [(8, 5), (8, 7), (11, 5), (11, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid6 : ∀ f ∈ family6, ruled (wireOf f) :=
  orbitRuled (e := (8, 5)) (by decide +kernel) (ruled_case (8, 5) (@endCase6))
def past6 := past1 ++ family6
lemma pastValid6 : ∀ f ∈ past6, ruled (wireOf f) := listRuled pastValid1 familyValid6

def cross7 : List (ℕ × ℕ) := [(0x4000,0), (0x8000,0), (0x80000,0), (0x4000000000000,0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x20000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover7 : rawPairs past6 (0, 5) cross7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n0 : rootChk [(0, 5)] cuts7 4 12 1 0x4000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n1 : rootChk [(0, 5)] cuts7 4 12 1 0x8000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n2 : rootChk [(0, 5)] cuts7 4 12 1 0x80000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n3 : rootChk [(0, 5)] cuts7 4 12 1 0x4000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n4 : rootChk [(0, 5)] cuts7 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n5 : rootChk [(0, 5)] cuts7 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x20000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n6 : rootChk [(0, 5)] cuts7 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial7n7 : rootChk [(0, 5)] cuts7 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase7 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(0, 5)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (0, 5)) (picks := cross7) (Q := cuts7) (by decide) (by decide +kernel) pastValid6 (by decide) marks7 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover7 _ hS hl
  intro p hp
  simp only [cross7,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rawTrial7n0
  · exact rawTrial7n1
  · exact rawTrial7n2
  · exact rawTrial7n3
  · exact rawTrial7n4
  · exact rawTrial7n5
  · exact rawTrial7n6
  · exact rawTrial7n7
def family7 : List (ℕ × ℕ) := [(0, 5), (0, 7), (3, 5), (3, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid7 : ∀ f ∈ family7, ruled (wireOf f) :=
  orbitRuled (e := (0, 5)) (by decide +kernel) (ruled_case (0, 5) (@endCase7))
def past7 := past6 ++ family7
lemma pastValid7 : ∀ f ∈ past7, ruled (wireOf f) := listRuled pastValid6 familyValid7

def cross8 : List (ℕ × ℕ) := [(0x4000,0), (0x4000000000000,0), ((Nat.lor (Nat.shiftLeft 0x400000 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover8 : rawPairs past7 (9, 4) cross8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial8n0 : rootChk [(9, 4)] cuts8 4 12 1 0x4000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial8n1 : rootChk [(9, 4)] cuts8 4 12 1 0x4000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial8n2 : rootChk [(9, 4)] cuts8 4 12 1 (Nat.lor (Nat.shiftLeft 0x400000 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial8n3 : rootChk [(9, 4)] cuts8 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial8n4 : rootChk [(9, 4)] cuts8 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial8n5 : rootChk [(9, 4)] cuts8 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase8 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(9, 4)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (9, 4)) (picks := cross8) (Q := cuts8) (by decide) (by decide +kernel) pastValid7 (by decide) marks8 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover8 _ hS hl
  intro p hp
  simp only [cross8,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact rawTrial8n0
  · exact rawTrial8n1
  · exact rawTrial8n2
  · exact rawTrial8n3
  · exact rawTrial8n4
  · exact rawTrial8n5
def family8 : List (ℕ × ℕ) := [(9, 4), (9, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid8 : ∀ f ∈ family8, ruled (wireOf f) :=
  orbitRuled (e := (9, 4)) (by decide +kernel) (ruled_case (9, 4) (@endCase8))
def past8 := past7 ++ family8
lemma pastValid8 : ∀ f ∈ past8, ruled (wireOf f) := listRuled pastValid7 familyValid8

def cross9 : List (ℕ × ℕ) := [(0x4000000000000,0), ((Nat.lor (Nat.shiftLeft 0x400000 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover9 : rawPairs past8 (1, 4) cross9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial9n0 : rootChk [(1, 4)] cuts9 4 12 1 0x4000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial9n1 : rootChk [(1, 4)] cuts9 4 12 1 (Nat.lor (Nat.shiftLeft 0x400000 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial9n2 : rootChk [(1, 4)] cuts9 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial9n3 : rootChk [(1, 4)] cuts9 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial9n4 : rootChk [(1, 4)] cuts9 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase9 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(1, 4)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (1, 4)) (picks := cross9) (Q := cuts9) (by decide) (by decide +kernel) pastValid8 (by decide) marks9 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover9 _ hS hl
  intro p hp
  simp only [cross9,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact rawTrial9n0
  · exact rawTrial9n1
  · exact rawTrial9n2
  · exact rawTrial9n3
  · exact rawTrial9n4
def family9 : List (ℕ × ℕ) := [(1, 4), (1, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid9 : ∀ f ∈ family9, ruled (wireOf f) :=
  orbitRuled (e := (1, 4)) (by decide +kernel) (ruled_case (1, 4) (@endCase9))
def past9 := past8 ++ family9
lemma pastValid9 : ∀ f ∈ past9, ruled (wireOf f) := listRuled pastValid8 familyValid9

def cross2 : List (ℕ × ℕ) := [(0x4000000000000,0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover2 : rawPairs past9 (8, 3) cross2 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial2n0 : rootChk [(8, 3)] cuts2 4 12 1 0x4000000000000 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial2n1 : rootChk [(8, 3)] cuts2 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial2n2 : rootChk [(8, 3)] cuts2 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial2n3 : rootChk [(8, 3)] cuts2 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase2 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(8, 3)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (8, 3)) (picks := cross2) (Q := cuts2) (by decide) (by decide +kernel) pastValid9 (by decide) marks2 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover2 _ hS hl
  intro p hp
  simp only [cross2,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact rawTrial2n0
  · exact rawTrial2n1
  · exact rawTrial2n2
  · exact rawTrial2n3
def family2 : List (ℕ × ℕ) := [(8, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid2 : ∀ f ∈ family2, ruled (wireOf f) :=
  orbitRuled (e := (8, 3)) (by decide +kernel) (ruled_case (8, 3) (@endCase2))
def past2 := past9 ++ family2
lemma pastValid2 : ∀ f ∈ past2, ruled (wireOf f) := listRuled pastValid9 familyValid2

def cross3 : List (ℕ × ℕ) := [((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover3 : rawPairs past2 (0, 3) cross3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial3n0 : rootChk [(0, 3)] cuts3 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial3n1 : rootChk [(0, 3)] cuts3 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial3n2 : rootChk [(0, 3)] cuts3 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase3 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(0, 3)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (0, 3)) (picks := cross3) (Q := cuts3) (by decide) (by decide +kernel) pastValid2 (by decide) marks3 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover3 _ hS hl
  intro p hp
  simp only [cross3,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact rawTrial3n0
  · exact rawTrial3n1
  · exact rawTrial3n2
def family3 : List (ℕ × ℕ) := [(0, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid3 : ∀ f ∈ family3, ruled (wireOf f) :=
  orbitRuled (e := (0, 3)) (by decide +kernel) (ruled_case (0, 3) (@endCase3))
def past3 := past2 ++ family3
lemma pastValid3 : ∀ f ∈ past3, ruled (wireOf f) := listRuled pastValid2 familyValid3

def cross14 : List (ℕ × ℕ) := [((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover14 : rawPairs past3 (12, 6) cross14 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial14n0 : rootChk [(12, 6)] cuts14 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial14n1 : rootChk [(12, 6)] cuts14 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x4000000000000 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial14n2 : rootChk [(12, 6)] cuts14 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase14 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(12, 6)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (12, 6)) (picks := cross14) (Q := cuts14) (by decide) (by decide +kernel) pastValid3 (by decide) marks14 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover14 _ hS hl
  intro p hp
  simp only [cross14,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact rawTrial14n0
  · exact rawTrial14n1
  · exact rawTrial14n2
def family14 : List (ℕ × ℕ) := [(12, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid14 : ∀ f ∈ family14, ruled (wireOf f) :=
  orbitRuled (e := (12, 6)) (by decide +kernel) (ruled_case (12, 6) (@endCase14))
def past14 := past3 ++ family14
lemma pastValid14 : ∀ f ∈ past14, ruled (wireOf f) := listRuled pastValid3 familyValid14

def cross15 : List (ℕ × ℕ) := [((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover15 : rawPairs past14 (4, 6) cross15 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial15n0 : rootChk [(4, 6)] cuts15 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial15n1 : rootChk [(4, 6)] cuts15 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase15 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(4, 6)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (4, 6)) (picks := cross15) (Q := cuts15) (by decide) (by decide +kernel) pastValid14 (by decide) marks15 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover15 _ hS hl
  intro p hp
  simp only [cross15,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact rawTrial15n0
  · exact rawTrial15n1
def family15 : List (ℕ × ℕ) := [(4, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid15 : ∀ f ∈ family15, ruled (wireOf f) :=
  orbitRuled (e := (4, 6)) (by decide +kernel) (ruled_case (4, 6) (@endCase15))
def past15 := past14 ++ family15
lemma pastValid15 : ∀ f ∈ past15, ruled (wireOf f) := listRuled pastValid14 familyValid15

def cross16 : List (ℕ × ℕ) := [((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0),0), ((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover16 : rawPairs past15 (13, 7) cross16 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial16n0 : rootChk [(13, 7)] cuts16 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x40 64) 0x0) 64) 0x0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial16n1 : rootChk [(13, 7)] cuts16 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase16 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(13, 7)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (13, 7)) (picks := cross16) (Q := cuts16) (by decide) (by decide +kernel) pastValid15 (by decide) marks16 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover16 _ hS hl
  intro p hp
  simp only [cross16,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl
  · exact rawTrial16n0
  · exact rawTrial16n1
def family16 : List (ℕ × ℕ) := [(13, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma familyValid16 : ∀ f ∈ family16, ruled (wireOf f) :=
  orbitRuled (e := (13, 7)) (by decide +kernel) (ruled_case (13, 7) (@endCase16))
def past16 := past15 ++ family16
lemma pastValid16 : ∀ f ∈ past16, ruled (wireOf f) := listRuled pastValid15 familyValid16

def cross17 : List (ℕ × ℕ) := [((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossCover17 : rawPairs past16 (5, 7) cross17 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rawTrial17n0 : rootChk [(5, 7)] cuts17 4 12 1 (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma endCase17 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [(5, 7)] 4))
    (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  apply rootAug (e := (5, 7)) (picks := cross17) (Q := cuts17) (by decide) (by decide +kernel) pastValid16 (by decide) marks17 ⟨((Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft 0x7ff77ffffffeff7 64) 0xfffbfddffeefffbf) 64) 0xffdfff7fffbeefff) 64) 0xfffbdffffff63fff),1), by decide,rfl⟩ crossCover17 _ hS hl
  intro p hp
  simp only [cross17,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl
  · exact rawTrial17n0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma directBlocked {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [] 4))
    (hl : Live Z0 (mz 4) (tz 4) 13 1 S) (hf : Live (RZ [] 4) (mz 4) (tz 4) 13 1 S) : False := by
  refine chosenImp (L := 14) (Or.inl rfl) (by decide) (by norm_num) remembered_ok (by omega) hS hl face_low ?_
  refine Or.inr ⟨[(0,1)], ⟨(0,1),List.mem_singleton.mpr rfl,rfl⟩, Or.inl hf, ?_⟩
  intro p hp
  have eq : p = (0,1) := List.mem_singleton.mp hp
  subst p
  rw [frozen13]
  exact closedUnary

lemma suffixBlocked {e : ℕ × ℕ} {S : Finset ℕ} (he : e ∈ six)
    (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [e] 4)) (hl : Live Z0 (mz 4) (tz 4) 12 1 S) : False := by
  simp only [six,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact endCase0 hS hl
  · exact endCase1 hS hl
  · exact endCase2 hS hl
  · exact endCase3 hS hl
  · exact endCase4 hS hl
  · exact endCase5 hS hl
  · exact endCase6 hS hl
  · exact endCase7 hS hl
  · exact endCase8 hS hl
  · exact endCase9 hS hl
  · exact endCase10 hS hl
  · exact endCase11 hS hl
  · exact endCase12 hS hl
  · exact endCase13 hS hl
  · exact endCase14 hS hl
  · exact endCase15 hS hl
  · exact endCase16 hS hl
  · exact endCase17 hS hl

lemma largerBank {x : ℕ} (e : ℕ × ℕ) (hx : x ∈ C (mz 4) (WZ [] 4)) : x ∈ C (mz 4) (WZ [e] 4) := by
  rcases hx with ⟨w,hw,rfl⟩ | hc
  · have mem : w ∈ rawP := by simpa [rawL] using hw
    exact Or.inl ⟨w, by simp [rawL,mem], rfl⟩
  · exact Or.inr hc

lemma pairBlocked {d : Bool} {a b : ℕ} {S U : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [] 4))
    (h : stocked d a b = true) (gate : Bi Z0 d a b S U) (tail : Live Z0 (mz 4) (tz 4) 12 1 U) : False := by
  obtain ⟨e,he,eq⟩ := List.any_eq_true.mp h
  apply suffixBlocked he _ tail
  intro x hx
  rcases Finset.mem_insert.mp (gate.sub.2.2 hx) with rfl | hx
  · exact Or.inl ⟨xw e,by simp [rawL],Nat.eq_of_beq_eq_true eq⟩
  · exact largerBank e (hS hx)

lemma face_impossible {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 4) (WZ [] 4))
    (hl : Live Z0 (mz 4) (tz 4) 13 1 S) : False := by
  have hm : ∀ q < 13, ¬ Sol Z0 (mz 4) (tz 4) q (C (mz 4) ({x | RZ [] 4 x ≠ 0} ∪ (S : Set ℕ))) := by
    intro q hq proof
    apply face_low q hq
    apply proof.mono le_rfl
    rintro x ((hx | hx) | hx)
    · exact Or.inl (rz_iff.mp hx)
    · exact hS hx
    · exact Or.inr hx
  rcases front (RZ_R2 [] 4) hl hm with direct | ⟨q,d,a,b,U,hq,ha,hb,gate,tail⟩
  · exact directBlocked hS hl direct
  have eq : q = 12 := by omega
  subst q
  have haW := rz_iff.mp ha
  have hbW := rz_iff.mp hb
  have hboth := List.all_eq_true.mp (List.all_eq_true.mp allChoices a (stepWords_iff.mpr haW)) b (stepWords_iff.mpr hbW)
  simp only [Bool.and_eq_true] at hboth
  have had : turnStock d a b = true := by
    cases d
    · exact hboth.1
    · exact hboth.2
  simp only [turnStock,Bool.or_eq_true,decide_eq_true_eq,List.any_eq_true] at had
  rcases had with ((same | za | zb) | direct) | ⟨p,hp,turn⟩
  · exact gate.1 same
  · apply face_low 12 (by omega)
    apply tail.sol.mono le_rfl
    intro x hx
    rcases Finset.mem_insert.mp (gate.sub.2.2 hx) with rfl | hx
    · cases d
      · exact Or.inr (Or.inl (by simp [op,za]))
      · rw [show op true a b = b by simp [op,za]]
        exact Or.inl hbW
    · exact hS hx
  · apply face_low 12 (by omega)
    apply tail.sol.mono le_rfl
    intro x hx
    rcases Finset.mem_insert.mp (gate.sub.2.2 hx) with rfl | hx
    · cases d
      · exact Or.inr (Or.inl (by simp [op,zb]))
      · rw [show op true a b = a by simp [op,zb]]
        exact Or.inl haW
    · exact hS hx
  · exact pairBlocked hS direct gate tail
  · obtain ⟨mask,target,words⟩ := motion hp
    have hs : ∀ x ∈ S, Stable p x := fun _ hx => (moveSet hp (hS hx)).1
    have gate' := gate.turn p hs
    have tail' := tail.turn p (show Stable p (mz 4) by simp only [Stable,mask]) (gate.afterStable hs)
    rw [mask,target] at tail'
    apply pairBlocked _ turn gate' tail'
    intro x hx
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
    exact (moveSet hp (hS hv)).2
inductive Sol2 (m T : ℕ) : ℕ → ℕ → Set ℕ → Prop
  | done {b u : ℕ} {S : Set ℕ} : T ∈ S → Sol2 m T b u S
  | un {b u : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol2 m T b u (insert (a ^^^ m) S) → Sol2 m T b (u + 1) S
  | bi {b u : ℕ} {S : Set ℕ} {d : Bool} {a c : ℕ} : a ∈ S → c ∈ S →
      Sol2 m T b u (insert (op d a c) S) → Sol2 m T (b + 1) u S

lemma Sol2.mono {m T b u : ℕ} {S : Set ℕ} (h : Sol2 m T b u S) :
    ∀ {b' u' : ℕ} {S' : Set ℕ}, b ≤ b' → u ≤ u' → S ⊆ S' → Sol2 m T b' u' S' := by
  induction h with
  | done h => intro b' u' S' _ _ hs; exact .done (hs h)
  | un h _ ih =>
    intro b' u' S' hb hu hs
    obtain ⟨r, rfl⟩ : ∃ r, u' = r + 1 := ⟨u' - 1, by omega⟩
    exact .un (hs h) (ih hb (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 _ ih =>
    intro b' u' S' hb hu hs
    obtain ⟨r, rfl⟩ : ∃ r, b' = r + 1 := ⟨b' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) (ih (by omega) hu (Set.insert_subset_insert hs))

lemma Sol2.live {m T b u : ℕ} {S : Set ℕ} (h : Sol2 m T b u S) :
    ∃ k t, t ≤ u ∧ k ≤ b + t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  induction h with
  | @done b u S h => exact ⟨0, 0, Nat.zero_le _, Nat.zero_le _, {T}, by simpa using h, .stop⟩
  | @un b u S a ha _ ih =>
    obtain ⟨k, t, htu, hkb, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k + 1, t + 1, by omega, by omega, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, t, by omega, hkb, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi b u S d a c ha hc _ ih =>
    obtain ⟨k, t, htu, hkb, S1, hs, hl⟩ := ih
    by_cases hg : op d a c ∈ S1
    · by_cases hac : a = c
      · subst hac; rw [op_self] at hs
        exact ⟨k, t, htu, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, t, htu, by omega, insert a (insert c (S1.erase (op d a c))), ?_, .bi hac (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hc
      · exact (hs h1).resolve_left h2
    · exact ⟨k, t, htu, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def binC : List Gate → ℕ
  | [] => 0
  | g :: gs => (match g.op with | GateOp.not => 0 | _ => 1) + binC gs

def notC : List Gate → ℕ
  | [] => 0
  | g :: gs => (match g.op with | GateOp.not => 1 | _ => 0) + notC gs

lemma binC_add_notC (gs : List Gate) : binC gs + notC gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rcases g with ⟨op, ins⟩
    cases op <;> simp [binC, notC] <;> omega

lemma binC_append (a b : List Gate) : binC (a ++ b) = binC a + binC b := by
  induction a with
  | nil => simp [binC]
  | cons g a ih => simp [binC, ih]; omega

lemma notC_append (a b : List Gate) : notC (a ++ b) = notC a + notC b := by
  induction a with
  | nil => simp [notC]
  | cons g a ih => simp [notC, ih]; omega

lemma notC_pos {gs : List Gate} (h : ∃ g ∈ gs, g.op = GateOp.not) : 1 ≤ notC gs := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨g', hg', hop⟩ := h
    simp only [List.mem_cons] at hg'
    simp only [notC]
    rcases hg' with rfl | hg'
    · rw [hop]; simp
    · have := ih ⟨g', hg', hop⟩; cases hgo : g.op <;> simp [hgo] <;> omega

lemma notC_le_one (gs : List Gate)
    (hu : ∀ i j : Fin gs.length, (gs.get i).op = GateOp.not → (gs.get j).op = GateOp.not → i = j) :
    notC gs ≤ 1 := by
  induction gs with
  | nil => simp [notC]
  | cons g gs ih =>
    simp only [notC]
    cases hg : g.op with
    | not =>
      have hz : notC gs = 0 := by
        have hnone : ∀ x ∈ gs, x.op ≠ GateOp.not := by
          intro x hx hxo
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
          have heq := hu ⟨0, by simp⟩ ⟨k + 1, by simp; omega⟩ hg hxo
          simp at heq
        clear ih hu hg
        induction gs with
        | nil => rfl
        | cons y ys ihy =>
          simp only [notC]
          have hyn := hnone y (by simp)
          cases hy : y.op with
          | not => exact absurd hy hyn
          | _ => simp [ihy (fun z hz => hnone z (by simp [hz]))]
      simp [hz]
    | _ =>
      simp only [Nat.zero_add]
      apply ih
      intro i j hi hj
      have heq := hu ⟨i.val + 1, by simp⟩ ⟨j.val + 1, by simp⟩ hi hj
      exact Fin.ext (by simpa using congrArg Fin.val heq)

section circuit
variable (m : ℕ)
def gv (w : List ℕ) (g : Gate) : ℕ := match g.op, g.inputs with
  | .and, [] => m
  | .and, [i] => w.getD i 0
  | .and, i :: j :: _ => w.getD i 0 &&& w.getD j 0
  | .or, [] => 0
  | .or, [i] => w.getD i 0
  | .or, i :: j :: _ => w.getD i 0 ||| w.getD j 0
  | .not, [] => m
  | .not, i :: _ => w.getD i 0 ^^^ m
  | _, _ => 0
def ex (gs : List Gate) (w : List ℕ) : List ℕ := gs.foldl (fun w g => w ++ [gv m w g]) w
lemma getD_mem {S : Set ℕ} {w : List ℕ} (hw : ∀ x ∈ w, x ∈ S) (h0 : 0 ∈ S) (i : ℕ) : w.getD i 0 ∈ S := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < w.length
  · rw [List.getElem?_eq_getElem h]; exact hw _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none (by omega)]; exact h0
lemma ex_sol2 {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol2 m T (binC gs) (notC gs) S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol2 m T (binC (g :: gs)) (notC (g :: gs)) S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp only [binC]; omega) (by simp only [notC]; omega) subset_rfl
    have go : Sol2 m T (binC gs) (notC gs) (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: t =>
        have hbc : binC (⟨GateOp.and, i :: j :: t⟩ :: gs) = binC gs + 1 := by simp [binC]; omega
        have hnc : notC (⟨GateOp.and, i :: j :: t⟩ :: gs) = notC gs := by simp [notC]
        rw [hbc, hnc]
        exact .bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: t =>
        have hbc : binC (⟨GateOp.or, i :: j :: t⟩ :: gs) = binC gs + 1 := by simp [binC]; omega
        have hnc : notC (⟨GateOp.or, i :: j :: t⟩ :: gs) = notC gs := by simp [notC]
        rw [hbc, hnc]
        exact .bi (d := true) (rd i) (rd j) go
    · match l with
      | [] => exact stay hm
      | i :: t =>
        have hbc : binC (⟨GateOp.not, i :: t⟩ :: gs) = binC gs := by simp [binC]
        have hnc : notC (⟨GateOp.not, i :: t⟩ :: gs) = notC gs + 1 := by simp [notC]; omega
        rw [hbc, hnc]
        exact .un (rd i) go
lemma gv_sub {w : List ℕ} (hw : ∀ x ∈ w, x &&& m = x) (g : Gate) : gv m w g &&& m = gv m w g := by
  have rd : ∀ i, w.getD i 0 &&& m = w.getD i 0 := fun i => getD_mem (S := {x | x &&& m = x}) hw (by simp) i
  unfold gv
  split
  · simp
  · exact rd _
  · rw [Nat.and_assoc, rd]
  · simp
  · exact rd _
  · rw [Nat.and_or_distrib_right, rd, rd]
  · simp
  · rw [and_neg (Nat.and_self m), rd]
  · simp
lemma ex_sub {gs : List Gate} : ∀ {w : List ℕ}, (∀ x ∈ w, x &&& m = x) → ∀ x ∈ ex m gs w, x &&& m = x := by
  induction gs with
  | nil => intro w hw; exact hw
  | cons g gs ih =>
    intro w hw
    refine ih (w := w ++ [gv m w g]) fun x hx => ?_
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hw x hx
    · exact gv_sub m hw g
lemma getD_map (w : List ℕ) (b i : ℕ) : (w.map (fun x => x.testBit b)).getD i false = (w.getD i 0).testBit b := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp
lemma gv_bit {b : ℕ} (hb : m.testBit b = true) (w : List ℕ) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (gv m w g).testBit b = g.op.eval (g.inputs.map fun i => (w.map (fun x => x.testBit b)).getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_map]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [gv, e1, hb]
    | [i], _ => simp [gv, e1]
    | [i, j], _ => simp [gv, e1]
  · match l, hlen with
    | [], _ => simp [gv, e2]
    | [i], _ => simp [gv, e2]
    | [i, j], _ => simp [gv, e2]
  · match l, hlen with
    | [], _ => simp [gv, e3, hb]
    | [i], _ => simp [gv, e3, hb]
    | [i, j], _ => simp [gv, e3, hb]
lemma ex_bit {b : ℕ} (hb : m.testBit b = true) (gs : List Gate) : ∀ (w : List ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (ex m gs w).map (fun x => x.testBit b) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (w.map (fun x => x.testBit b)) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hg
    rw [List.foldl_cons, ← gv_bit m hb w g (hg g List.mem_cons_self)]
    have := ih (w ++ [gv m w g]) (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    rw [List.map_append] at this
    exact this
end circuit

def wiresB (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresB_append (a b : List Gate) (w : List Bool) :
    wiresB (a ++ b) w = wiresB b (wiresB a w) := by
  simp [wiresB, List.foldl_append]

lemma wiresB_length (gs : List Gate) : ∀ w : List Bool, (wiresB gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wiresB]
  | cons g gs ih =>
    intro w
    change (wiresB gs (w ++ [_])).length = _
    rw [ih]; simp; omega

lemma getD_append_lt {α : Type} (L R : List α) (d : α) (i : ℕ) (h : i < L.length) :
    (L ++ R).getD i d = L.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq' {α : Type} (L : List α) (x d : α) : (L ++ [x]).getD L.length d = x := by
  simp

lemma getD_snoc_ne' {α : Type} (L : List α) (x d : α) (i : ℕ) (h : i ≠ L.length) :
    (L ++ [x]).getD i d = L.getD i d := by
  by_cases hi : i < L.length
  · exact getD_append_lt L [x] d i hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

abbrev Stat := Sum Bool ℕ

def statEval (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpGate (m : ℕ) (st : List Stat) (g : Gate) : Option Gate × Stat :=
  match g.op, g.inputs with
  | .and, [] => (none, Sum.inl true)
  | .and, [a] => (none, st.getD a (Sum.inl false))
  | .and, a :: b :: _ =>
    match st.getD a (Sum.inl false), st.getD b (Sum.inl false) with
    | Sum.inl false, _ => (none, Sum.inl false)
    | Sum.inl true, s => (none, s)
    | s, Sum.inl false => (none, Sum.inl false)
    | s, Sum.inl true => (none, s)
    | Sum.inr i, Sum.inr j => (some ⟨GateOp.and, [i, j]⟩, Sum.inr m)
  | .or, [] => (none, Sum.inl false)
  | .or, [a] => (none, st.getD a (Sum.inl false))
  | .or, a :: b :: _ =>
    match st.getD a (Sum.inl false), st.getD b (Sum.inl false) with
    | Sum.inl true, _ => (none, Sum.inl true)
    | Sum.inl false, s => (none, s)
    | s, Sum.inl true => (none, Sum.inl true)
    | s, Sum.inl false => (none, s)
    | Sum.inr i, Sum.inr j => (some ⟨GateOp.or, [i, j]⟩, Sum.inr m)
  | .not, [] => (none, Sum.inl true)
  | .not, a :: _ =>
    match st.getD a (Sum.inl false) with
    | Sum.inl c => (none, Sum.inl (!c))
    | Sum.inr i => (some ⟨GateOp.not, [i]⟩, Sum.inr m)
  | _, _ => (none, Sum.inl false)

def simpRun : List Gate → List Gate → List Stat → List Gate × List Stat
  | [], acc, st => (acc, st)
  | g :: gs, acc, st =>
    let r := simpGate (8 + acc.length) st g
    match r.1 with
    | none => simpRun gs acc (st ++ [r.2])
    | some g' => simpRun gs (acc ++ [g']) (st ++ [r.2])

def st0 : List Stat := [Sum.inr 0, Sum.inr 1, Sum.inl false, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inr 6, Sum.inr 7]

lemma simpGate_props {m : ℕ} {st : List Stat} (hv : ∀ s ∈ st, statValid m s) {g : Gate}
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    (match (simpGate m st g).1 with
      | none => statValid m (simpGate m st g).2
      | some g' => (g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
          g'.op = g.op ∧ statValid (m + 1) (simpGate m st g).2) := by
  have hget : ∀ a, statValid m (st.getD a (Sum.inl false)) := fun a => by
    rw [List.getD_eq_getElem?_getD]
    by_cases ha : a < st.length
    · rw [List.getElem?_eq_getElem ha]; exact hv _ (List.getElem_mem ha)
    · rw [List.getElem?_eq_none (by omega)]; trivial
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [simpGate, statValid]
    | [a], _ => simp [simpGate]; exact hget a
    | [a, b], _ =>
      have ha := hget a; have hb := hget b
      simp only [simpGate]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => cases c <;> simp [statValid] at hb ⊢ <;> exact hb
      | inr i =>
        rw [h1] at ha
        cases h2 : st.getD b (Sum.inl false) with
        | inl c => cases c <;> simp [statValid]; exact ha
        | inr j => simp [statValid]
  · match l, hlen with
    | [], _ => simp [simpGate, statValid]
    | [a], _ => simp [simpGate]; exact hget a
    | [a, b], _ =>
      have ha := hget a; have hb := hget b
      simp only [simpGate]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => cases c <;> simp [statValid] at hb ⊢ <;> exact hb
      | inr i =>
        rw [h1] at ha
        cases h2 : st.getD b (Sum.inl false) with
        | inl c => cases c <;> simp [statValid]; exact ha
        | inr j => simp [statValid]
  · match l, hlen with
    | [], _ => simp [simpGate, statValid]
    | [a], _ =>
      simp only [simpGate]
      cases st.getD a (Sum.inl false) with
      | inl c => simp [statValid]
      | inr i => simp [statValid]
    | [a, b], _ =>
      simp only [simpGate]
      cases st.getD a (Sum.inl false) with
      | inl c => simp [statValid]
      | inr i => simp [statValid]

lemma simpGate_eval {w w' : List Bool} {st : List Stat}
    (hm : w'.length = m)
    (heq : ∀ i, w.getD i false = statEval w' (st.getD i (Sum.inl false)))
    {g : Gate}
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    let val := g.op.eval (g.inputs.map fun i => w.getD i false)
    match (simpGate m st g).1 with
    | none => val = statEval w' (simpGate m st g).2
    | some g' =>
      let w'' := w' ++ [g'.op.eval (g'.inputs.map fun i => w'.getD i false)]
      val = statEval w'' (simpGate m st g).2 := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · match l, hlen with
    | [], _ => simp [simpGate, e1, statEval]
    | [a], _ =>
      have ha := heq a
      simp only [simpGate, e1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      exact ha
    | [a, b], _ =>
      have ha := heq a; have hb := heq b
      simp only [simpGate, e1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c =>
        rw [h1] at ha; dsimp only [statEval] at ha
        cases c <;> simp only [ha, hb, statEval, Bool.false_and, Bool.true_and]
      | inr i =>
        rw [h1] at ha; dsimp only [statEval] at ha
        cases h2 : st.getD b (Sum.inl false) with
        | inl c =>
          rw [h2] at hb; dsimp only [statEval] at hb
          cases c <;> simp only [ha, hb, statEval, Bool.and_false, Bool.and_true]
        | inr j =>
          rw [h2] at hb; dsimp only [statEval] at hb
          dsimp only [statEval]
          rw [← hm, getD_snoc_eq']
          simp only [e1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, ha, hb]
  · match l, hlen with
    | [], _ => simp [simpGate, e2, statEval]
    | [a], _ =>
      have ha := heq a
      simp only [simpGate, e2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      exact ha
    | [a, b], _ =>
      have ha := heq a; have hb := heq b
      simp only [simpGate, e2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c =>
        rw [h1] at ha; dsimp only [statEval] at ha
        cases c <;> simp only [ha, hb, statEval, Bool.false_or, Bool.true_or]
      | inr i =>
        rw [h1] at ha; dsimp only [statEval] at ha
        cases h2 : st.getD b (Sum.inl false) with
        | inl c =>
          rw [h2] at hb; dsimp only [statEval] at hb
          cases c <;> simp only [ha, hb, statEval, Bool.or_false, Bool.or_true]
        | inr j =>
          rw [h2] at hb; dsimp only [statEval] at hb
          dsimp only [statEval]
          rw [← hm, getD_snoc_eq']
          simp only [e2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, ha, hb]
  · match l, hlen with
    | [], _ => simp [simpGate, e3, statEval]
    | [a], _ =>
      have ha := heq a
      simp only [simpGate, e3, List.map_cons, List.map_nil, List.headD]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => rw [h1] at ha; dsimp only [statEval] at ha; simp only [ha, statEval]
      | inr i =>
        rw [h1] at ha; dsimp only [statEval] at ha
        dsimp only [statEval]
        rw [← hm, getD_snoc_eq']
        simp only [e3, List.map_cons, List.map_nil, List.headD, ha]
    | [a, b], _ =>
      have ha := heq a
      simp only [simpGate, e3, List.map_cons, List.map_nil, List.headD]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => rw [h1] at ha; dsimp only [statEval] at ha; simp only [ha, statEval]
      | inr i =>
        rw [h1] at ha; dsimp only [statEval] at ha
        dsimp only [statEval]
        rw [← hm, getD_snoc_eq']
        simp only [e3, List.map_cons, List.map_nil, List.headD, ha]

lemma statEval_snoc {w' : List Bool} {v : Bool} {s : Stat} (hv : statValid w'.length s) :
    statEval (w' ++ [v]) s = statEval w' s := by
  cases s with
  | inl c => rfl
  | inr j => exact getD_append_lt w' [v] false j hv

lemma simpRun_ok (gs : List Gate) : ∀ (acc : List Gate) (st : List Stat),
    (∀ g ∈ acc, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ s ∈ st, statValid (8 + acc.length) s) →
    let res := simpRun gs acc st
    (∀ g ∈ res.1, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
    binC res.1 ≤ binC acc + binC gs ∧
    notC res.1 ≤ notC acc + notC gs ∧
    (∀ s ∈ res.2, statValid (8 + res.1.length) s) ∧
    res.2.length = st.length + gs.length := by
  induction gs with
  | nil =>
    intro acc st ha _ hv
    exact ⟨ha, by simp [simpRun, binC], by simp [simpRun, notC], hv, by simp [simpRun]⟩
  | cons g gs ih =>
    intro acc st ha hgs hv
    have hg := hgs g (by simp)
    have hgs' : ∀ x ∈ gs, x.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ x.inputs.length ≤ 2 :=
      fun x hx => hgs x (List.mem_cons_of_mem _ hx)
    have hp := simpGate_props hv hg
    simp only [simpRun]
    cases hr : (simpGate (8 + acc.length) st g).1 with
    | none =>
      rw [hr] at hp
      have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + acc.length) s := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hv s hs
        · exact hp
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih acc _ ha hgs' hv'
      refine ⟨r1, ?_, ?_, r4, by simp [r5]; omega⟩
      · simp only [binC]; cases g.op <;> omega
      · simp only [notC]; cases g.op <;> omega
    | some g' =>
      rw [hr] at hp
      obtain ⟨hg'ok, hg'op, hs'v⟩ := hp
      have ha' : ∀ x ∈ acc ++ [g'], x.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ x.inputs.length ≤ 2 := by
        intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact ha x hx
        · exact hg'ok
      have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + (acc ++ [g']).length) s := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        have hlen : 8 + (acc ++ [g']).length = 8 + acc.length + 1 := by simp; omega
        rw [hlen]
        rcases hs with hs | rfl
        · have hvs := hv s hs
          cases s with
          | inl _ => trivial
          | inr j => change j < 8 + acc.length at hvs; change j < 8 + acc.length + 1; omega
        · exact hs'v
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih (acc ++ [g']) _ ha' hgs' hv'
      refine ⟨r1, ?_, ?_, r4, by simp [r5]; omega⟩
      · rw [binC_append] at r2; simp only [binC, hg'op] at r2 ⊢; omega
      · rw [notC_append] at r3; simp only [notC, hg'op] at r3 ⊢; omega

lemma simpRun_eval (gs : List Gate) : ∀ (acc : List Gate) (st : List Stat) (w w' : List Bool),
    w'.length = 8 + acc.length →
    w.length = st.length →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ s ∈ st, statValid (8 + acc.length) s) →
    (∀ i, w.getD i false = statEval w' (st.getD i (Sum.inl false))) →
    ∀ i, (wiresB gs w).getD i false =
      statEval (wiresB ((simpRun gs acc st).1.drop acc.length) w') ((simpRun gs acc st).2.getD i (Sum.inl false)) := by
  induction gs with
  | nil =>
    intro acc st w w' _ _ _ _ heq i
    simp only [simpRun, wiresB, List.drop_length, List.foldl_nil]
    exact heq i
  | cons g gs ih =>
    intro acc st w w' hw'len hwlen hgs hv heq
    have hg := hgs g (by simp)
    have hgs' : ∀ x ∈ gs, x.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ x.inputs.length ≤ 2 :=
      fun x hx => hgs x (List.mem_cons_of_mem _ hx)
    have hp := simpGate_props hv hg
    have hev := simpGate_eval hw'len heq hg
    simp only [simpRun]
    cases hr : (simpGate (8 + acc.length) st g).1 with
    | none =>
      rw [hr] at hp hev
      have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + acc.length) s := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · exact hv s hs
        · exact hp
      have heq' : ∀ i, (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD i false =
          statEval w' ((st ++ [(simpGate (8 + acc.length) st g).2]).getD i (Sum.inl false)) := by
        intro i
        by_cases hi : i = w.length
        · subst hi; rw [getD_snoc_eq', hwlen, getD_snoc_eq']; exact hev
        · rw [getD_snoc_ne' _ _ _ _ hi, getD_snoc_ne' _ _ _ _ (hwlen ▸ hi)]; exact heq i
      exact ih acc _ (w ++ [_]) w' hw'len (by simp [hwlen]) hgs' hv' heq'
    | some g' =>
      rw [hr] at hp hev
      obtain ⟨_, _, hs'v⟩ := hp
      have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + (acc ++ [g']).length) s := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        have hlen : 8 + (acc ++ [g']).length = 8 + acc.length + 1 := by simp; omega
        rw [hlen]
        rcases hs with hs | rfl
        · have hvs := hv s hs
          cases s with
          | inl _ => trivial
          | inr j => change j < 8 + acc.length at hvs; change j < 8 + acc.length + 1; omega
        · exact hs'v
      let w'' := w' ++ [g'.op.eval (g'.inputs.map fun j => w'.getD j false)]
      have heq' : ∀ i, (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).getD i false =
          statEval w'' ((st ++ [(simpGate (8 + acc.length) st g).2]).getD i (Sum.inl false)) := by
        intro i
        by_cases hi : i = w.length
        · subst hi; rw [getD_snoc_eq', hwlen, getD_snoc_eq']; exact hev
        · rw [getD_snoc_ne' _ _ _ _ hi, getD_snoc_ne' _ _ _ _ (hwlen ▸ hi), heq i]
          have hvs : statValid w'.length (st.getD i (Sum.inl false)) := by
            rw [hw'len, List.getD_eq_getElem?_getD]
            by_cases hlt : i < st.length
            · rw [List.getElem?_eq_getElem hlt]; exact hv _ (List.getElem_mem hlt)
            · rw [List.getElem?_eq_none (by omega)]; trivial
          exact (statEval_snoc hvs).symm
      have hres := ih (acc ++ [g']) _ (w ++ [_]) w'' (by simp [w'', hw'len]; omega) (by simp [hwlen]) hgs' hv' heq'
      have hpref : ∀ (gs' : List Gate) (acc' : List Gate) (st' : List Stat),
          (simpRun gs' acc' st').1.take acc'.length = acc' := by
        intro gs'
        induction gs' with
        | nil => intro acc' st'; simp [simpRun]
        | cons x xs ihx =>
          intro acc' st'
          simp only [simpRun]
          cases (simpGate (8 + acc'.length) st' x).1 with
          | none => exact ihx acc' _
          | some y =>
            have h1 := ihx (acc' ++ [y]) (st' ++ [(simpGate (8 + acc'.length) st' x).2])
            have h2 := congrArg (List.take acc'.length) h1
            rw [List.take_take, Nat.min_eq_left (by simp), List.take_left] at h2
            exact h2
      have hdrop : (simpRun gs (acc ++ [g']) (st ++ [(simpGate (8 + acc.length) st g).2])).1.drop acc.length =
          g' :: (simpRun gs (acc ++ [g']) (st ++ [(simpGate (8 + acc.length) st g).2])).1.drop (acc ++ [g']).length := by
        set L := (simpRun gs (acc ++ [g']) (st ++ [(simpGate (8 + acc.length) st g).2])).1
        have htk : L.take (acc ++ [g']).length = acc ++ [g'] := hpref gs (acc ++ [g']) _
        have hspl : L = (acc ++ [g']) ++ L.drop (acc ++ [g']).length := by
          conv_lhs => rw [← List.take_append_drop (acc ++ [g']).length L, htk]
        conv_lhs => rw [hspl]
        rw [List.append_assoc, List.drop_left]
        rfl
      intro i
      change (wiresB gs (w ++ [_])).getD i false = _
      rw [hres i, hdrop]
      rfl

lemma simpGate_indep {m : ℕ} {st : List Stat} {w0 w1 : List Bool}
    (hind : ∀ i, match st.getD i (Sum.inl false) with | Sum.inl _ => True | Sum.inr _ => w0.getD i false = w1.getD i false)
    {g : Gate}
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hbin : g.op ≠ GateOp.not → (simpGate m st g).1 ≠ none) :
    match (simpGate m st g).2 with
    | Sum.inl _ => True
    | Sum.inr _ => g.op.eval (g.inputs.map fun i => w0.getD i false) = g.op.eval (g.inputs.map fun i => w1.getD i false) := by
  have e1 : ∀ l, GateOp.and.eval l = l.all id := fun _ => rfl
  have e2 : ∀ l, GateOp.or.eval l = l.any id := fun _ => rfl
  have e3 : ∀ l, GateOp.not.eval l = !(l.headD false) := fun _ => rfl
  obtain ⟨o, l⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen
  rcases hop with rfl | rfl | rfl
  · have hne := hbin (fun h => by cases h)
    match l, hlen with
    | [], _ => simp [simpGate] at hne
    | [a], _ => simp [simpGate] at hne
    | [a, b], _ =>
      have ha := hind a; have hb := hind b
      simp only [simpGate] at hne ⊢
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => rw [h1] at hne; cases c <;> exact absurd rfl hne
      | inr i =>
        rw [h1] at hne ha
        cases h2 : st.getD b (Sum.inl false) with
        | inl c => rw [h2] at hne; cases c <;> exact absurd rfl hne
        | inr j =>
          rw [h2] at hb
          simp only [e1, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          exact congrArg₂ (· && ·) ha hb
  · have hne := hbin (fun h => by cases h)
    match l, hlen with
    | [], _ => simp [simpGate] at hne
    | [a], _ => simp [simpGate] at hne
    | [a, b], _ =>
      have ha := hind a; have hb := hind b
      simp only [simpGate] at hne ⊢
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => rw [h1] at hne; cases c <;> exact absurd rfl hne
      | inr i =>
        rw [h1] at hne ha
        cases h2 : st.getD b (Sum.inl false) with
        | inl c => rw [h2] at hne; cases c <;> exact absurd rfl hne
        | inr j =>
          rw [h2] at hb
          simp only [e2, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
          exact congrArg₂ (· || ·) ha hb
  · match l, hlen with
    | [], _ => simp [simpGate]
    | [a], _ =>
      have ha := hind a
      simp only [simpGate]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => trivial
      | inr i =>
        rw [h1] at ha
        simp only [e3, List.map_cons, List.map_nil, List.headD]
        exact congrArg Bool.not ha
    | [a, b], _ =>
      have ha := hind a
      simp only [simpGate]
      cases h1 : st.getD a (Sum.inl false) with
      | inl c => trivial
      | inr i =>
        rw [h1] at ha
        simp only [e3, List.map_cons, List.map_nil, List.headD]
        exact congrArg Bool.not ha

lemma simpRun_indep (gs : List Gate) : ∀ (acc : List Gate) (st : List Stat) (w0 w1 : List Bool),
    w0.length = st.length →
    w1.length = st.length →
    (∀ g ∈ acc, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ s ∈ st, statValid (8 + acc.length) s) →
    (∀ i, match st.getD i (Sum.inl false) with | Sum.inl _ => True | Sum.inr _ => w0.getD i false = w1.getD i false) →
    binC (simpRun gs acc st).1 = binC acc + binC gs →
    ∀ i, match (simpRun gs acc st).2.getD i (Sum.inl false) with
      | Sum.inl _ => True
      | Sum.inr _ => (wiresB gs w0).getD i false = (wiresB gs w1).getD i false := by
  induction gs with
  | nil =>
    intro acc st w0 w1 _ _ _ _ _ hind _ i
    simpa [simpRun, wiresB] using hind i
  | cons g gs ih =>
    intro acc st w0 w1 h0len h1len ha hgs hv hind hbeq
    have hg := hgs g (by simp)
    have hgs' : ∀ x ∈ gs, x.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ x.inputs.length ≤ 2 :=
      fun x hx => hgs x (List.mem_cons_of_mem _ hx)
    have hp := simpGate_props hv hg
    simp only [simpRun] at hbeq ⊢
    cases hr : (simpGate (8 + acc.length) st g).1 with
    | none =>
      rw [hr] at hp hbeq
      have hnot : g.op = GateOp.not := by
        by_contra hne
        have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + acc.length) s := by
          intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
          rcases hs with hs | rfl; exact hv s hs; exact hp
        have hle := (simpRun_ok gs acc _ ha hgs' hv').2.1
        simp only [binC] at hbeq
        cases hgo : g.op with
        | not => exact hne hgo
        | _ => omega
      have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + acc.length) s := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl; exact hv s hs; exact hp
      have hstep := simpGate_indep (m := 8 + acc.length) hind hg (fun h => absurd hnot h)
      have hind' : ∀ i, match (st ++ [(simpGate (8 + acc.length) st g).2]).getD i (Sum.inl false) with
          | Sum.inl _ => True
          | Sum.inr _ => (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]).getD i false =
                         (w1 ++ [g.op.eval (g.inputs.map fun j => w1.getD j false)]).getD i false := by
        intro i
        by_cases hi : i = st.length
        · subst hi; rw [getD_snoc_eq', ← h0len, getD_snoc_eq', h0len, ← h1len, getD_snoc_eq']; exact hstep
        · rw [getD_snoc_ne' _ _ _ _ hi, getD_snoc_ne' _ _ _ _ (h0len.symm ▸ hi), getD_snoc_ne' _ _ _ _ (h1len.symm ▸ hi)]
          exact hind i
      have hbeq' : binC (simpRun gs acc (st ++ [(simpGate (8 + acc.length) st g).2])).1 = binC acc + binC gs := by
        simp only [binC, hnot, Nat.zero_add] at hbeq; exact hbeq
      exact ih acc _ _ _ (by simp [h0len]) (by simp [h1len]) ha hgs' hv' hind' hbeq'
    | some g' =>
      rw [hr] at hp hbeq
      obtain ⟨hg'ok, hg'op, hs'v⟩ := hp
      have ha' : ∀ x ∈ acc ++ [g'], x.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ x.inputs.length ≤ 2 := by
        intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl; exact ha x hx; exact hg'ok
      have hv' : ∀ s ∈ st ++ [(simpGate (8 + acc.length) st g).2], statValid (8 + (acc ++ [g']).length) s := by
        intro s hs; simp only [List.mem_append, List.mem_singleton] at hs
        have hlen : 8 + (acc ++ [g']).length = 8 + acc.length + 1 := by simp; omega
        rw [hlen]
        rcases hs with hs | rfl
        · have hvs := hv s hs
          cases s with
          | inl _ => trivial
          | inr j => change j < 8 + acc.length at hvs; change j < 8 + acc.length + 1; omega
        · exact hs'v
      have hstep := simpGate_indep (m := 8 + acc.length) hind hg (by rw [hr]; simp)
      have hind' : ∀ i, match (st ++ [(simpGate (8 + acc.length) st g).2]).getD i (Sum.inl false) with
          | Sum.inl _ => True
          | Sum.inr _ => (w0 ++ [g.op.eval (g.inputs.map fun j => w0.getD j false)]).getD i false =
                         (w1 ++ [g.op.eval (g.inputs.map fun j => w1.getD j false)]).getD i false := by
        intro i
        by_cases hi : i = st.length
        · subst hi; rw [getD_snoc_eq', ← h0len, getD_snoc_eq', h0len, ← h1len, getD_snoc_eq']; exact hstep
        · rw [getD_snoc_ne' _ _ _ _ hi, getD_snoc_ne' _ _ _ _ (h0len.symm ▸ hi), getD_snoc_ne' _ _ _ _ (h1len.symm ▸ hi)]
          exact hind i
      have hbeq' : binC (simpRun gs (acc ++ [g']) (st ++ [(simpGate (8 + acc.length) st g).2])).1 = binC (acc ++ [g']) + binC gs := by
        rw [binC_append]; simp only [binC, hg'op] at hbeq ⊢; omega
      exact ih (acc ++ [g']) _ _ _ (by simp [h0len]) (by simp [h1len]) ha' hgs' hv' hind' hbeq'


def f (x : Fin 8 → Bool) : Bool := ((x 0 && x 3) || ((x 1 && x 4) || ((x 0 && x 5) || ((x 1 && x 5) || ((x 3 && x 5) || ((x 1 && x 6) || ((x 2 && x 6) || ((x 4 && x 6) || ((x 0 && x 7) || ((x 1 && x 7) || ((x 2 && x 7) || ((x 3 && x 7) || (x 5 && x 7)))))))))))))
def EF : ℕ := ((rawP.getD 0 0 &&& rawP.getD 3 0) ||| ((rawP.getD 1 0 &&& rawP.getD 4 0) ||| ((rawP.getD 0 0 &&& rawP.getD 5 0) ||| ((rawP.getD 1 0 &&& rawP.getD 5 0) ||| ((rawP.getD 3 0 &&& rawP.getD 5 0) ||| ((rawP.getD 1 0 &&& rawP.getD 6 0) ||| ((rawP.getD 2 0 &&& rawP.getD 6 0) ||| ((rawP.getD 4 0 &&& rawP.getD 6 0) ||| ((rawP.getD 0 0 &&& rawP.getD 7 0) ||| ((rawP.getD 1 0 &&& rawP.getD 7 0) ||| ((rawP.getD 2 0 &&& rawP.getD 7 0) ||| ((rawP.getD 3 0 &&& rawP.getD 7 0) ||| (rawP.getD 5 0 &&& rawP.getD 7 0)))))))))))))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma faceEq : EF &&& mz 4 = tz 4 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma zeroEq : rawP.getD 2 0 &&& mz 4 = 0 := by decide +kernel
theorem bridge_w5 (gs : List Gate) (out : ℕ)
    (hD : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hf : ∀ y : Fin 8 → Bool, y 2 = false → Circuit.eval ⟨gs, out⟩ (List.ofFn y) = f y) :
    Sol2 (mz 4) (tz 4) (binC gs) (notC gs) (C (mz 4) (WZ [] 4)) := by
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 4)
  have hinit_sub : ∀ x ∈ init, x &&& mz 4 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 4) (WZ [] 4) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 4).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 4) gs init).getD out 0 = tz 4 := by
    rw [← faceEq]
    have hsub : ∀ x ∈ ex (mz 4) gs init, x &&& mz 4 = x := ex_sub (mz 4) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 4 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 4).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 4) hk gs init hD, hinit_bits k hk]
      have hr1 : row k 2 = false := by
        have h1 := congrArg (fun x => x.testBit k) zeroEq
        simp only [Nat.testBit_and, hk, Bool.and_true, Nat.zero_testBit] at h1
        exact h1
      have h := hf (row k) hr1
      change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact ex_sol2 (mz 4) gs init (C (mz 4) (WZ [] 4))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩


theorem few_impossible (gates : List Gate) (o : ℕ)
    (hD : ∀ g ∈ gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hb11 : binC gates ≤ 13) (hn1 : notC gates ≤ 1)
    (hf : ∀ x : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x) : False := by
  have hst0v : ∀ s ∈ st0, statValid (8 + ([] : List Gate).length) s := by
    intro s hs
    simp only [st0, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [statValid]
  obtain ⟨hrok, hrbin, hrnot, _, _⟩ := simpRun_ok gates [] st0 (by simp) hD hst0v
  set res := simpRun gates [] st0 with hres_def
  have hev : ∀ y : Fin 8 → Bool, y 2 = false →
      f y = statEval (wiresB res.1 (List.ofFn y)) (res.2.getD o (Sum.inl false)) := by
    intro y hy1
    rw [← hf y]
    have hinit : ∀ i, (List.ofFn y).getD i false = statEval (List.ofFn y) (st0.getD i (Sum.inl false)) := by
      intro i
      match i with
      | 0 => simp [st0, statEval]
      | 1 => simp [st0, statEval]
      | 2 => simp [st0, statEval, hy1]
      | 3 => simp [st0, statEval]
      | 4 => simp [st0, statEval]
      | 5 => simp [st0, statEval]
      | 6 => simp [st0, statEval]
      | 7 => simp [st0, statEval]
      | n + 8 =>
        rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp [st0])]
        rfl
    exact simpRun_eval gates [] st0 (List.ofFn y) (List.ofFn y) (by simp) (by simp [st0]) hD hst0v hinit o
  cases ho : res.2.getD o (Sum.inl false) with
  | inl c =>
    have h0 := hev (fun _ => false) rfl
    have h1 := hev (fun i => decide (i = 4 ∨ i = 6)) rfl
    rw [ho] at h0 h1
    simp [f, statEval] at h0 h1
    rw [h0] at h1
    cases h1
  | inr o' =>
    have hbin10 : binC res.1 ≤ 12 := by
      have hlt : binC res.1 < binC gates := by
        by_contra hge
        have hbeq : binC res.1 = binC [] + binC gates := by simp [binC] at hrbin ⊢; omega
        let y0 : Fin 8 → Bool := fun i => decide (i = 7)
        let y1 : Fin 8 → Bool := fun i => decide (i = 2 ∨ i = 7)
        have hind0 : ∀ i, match st0.getD i (Sum.inl false) with
            | Sum.inl _ => True
            | Sum.inr _ => (List.ofFn y0).getD i false = (List.ofFn y1).getD i false := by
          intro i
          match i with
          | 0 => simp [st0, y0, y1]
          | 1 => simp [st0, y0, y1]
          | 2 => simp [st0, y0, y1]
          | 3 => simp [st0, y0, y1]
          | 4 => simp [st0, y0, y1]
          | 5 => simp [st0, y0, y1]
          | 6 => simp [st0, y0, y1]
          | 7 => simp [st0, y0, y1]
          | n + 8 =>
            rw [List.getD_eq_default _ _ (by simp [st0])]; trivial
        have hind := simpRun_indep gates [] st0 (List.ofFn y0) (List.ofFn y1)
          (by simp [st0]) (by simp [st0]) (by simp) hD hst0v hind0 hbeq o
        rw [← hres_def, ho] at hind
        have hfy0 : (wiresB gates (List.ofFn y0)).getD o false = f y0 := hf y0
        have hfy1 : (wiresB gates (List.ofFn y1)).getD o false = f y1 := hf y1
        rw [hfy0, hfy1] at hind
        simp [f, y0, y1] at hind
      omega
    have hnot1 : notC res.1 ≤ 1 := by simp [notC] at hrnot; omega
    have hfev : ∀ y : Fin 8 → Bool, y 2 = false → Circuit.eval ⟨res.1, o'⟩ (List.ofFn y) = f y := by
      intro y hy1
      have h := hev y hy1
      rw [ho] at h
      exact h.symm
    have hsol := bridge_w5 res.1 o' hrok hfev
    obtain ⟨k, t, htu, hkb, S0, hS0, hl⟩ := hsol.live
    by_cases hk11 : k < 13
    · exact face_low k hk11 (hl.sol.mono le_rfl hS0)
    · have hk : k = 13 := by omega
      have ht : t = 1 := by omega
      subst hk; subst ht
      exact face_impossible hS0 hl


private theorem target_eq_f (x : Fin 8 → Bool) : decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2*i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2*i+1) 0) false = true) = f x :=
  (by decide +kernel : ∀ y : Fin 8 → Bool, decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn y).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2*i) 0) false = true ∧ (List.ofFn y).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2*i+1) 0) false = true) = f y) x

def smallGates : List Gate := [⟨.and, [0, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [15, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [17, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [19, 13]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [21, 18]⟩]
def smallOut : ℕ := 22
private theorem witnessMono : ∀ g ∈ smallGates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [smallGates]
private theorem witnessCorrect (x : Fin 8 → Bool) : Circuit.eval ⟨smallGates, smallOut⟩ (List.ofFn x) = f x :=
  (by decide +kernel : ∀ y : Fin 8 → Bool, Circuit.eval ⟨smallGates, smallOut⟩ (List.ofFn y) = f y) x

private theorem fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩


end PEqualNP.Outside.L_meta_32784

open PEqualNP.Outside.L_meta_32784

theorem PEqualNP.Outside.L_meta_32784 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfit hone hev
  by_cases hnot : ∃ g ∈ gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · have hge : 15 ≤ gates.length := by
      by_contra hlt
      have hcount := binC_add_notC gates
      have hpos := notC_pos hnot
      exact few_impossible gates o (fanInTwo_of (o := o) hfit) (by omega) (notC_le_one gates hone)
        (fun x => (hev x).trans (target_eq_f x))
    exact ⟨smallGates, smallOut, witnessMono, hge, fun x => (witnessCorrect x).trans (target_eq_f x).symm⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨ho, hl⟩ := hfit g hg
    refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim
