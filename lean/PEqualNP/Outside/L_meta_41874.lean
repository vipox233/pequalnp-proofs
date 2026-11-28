import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41874_aux

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
structure XW where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat

structure Inst where
  NN : Nat
  AA : Nat
  HX : Nat
  HY : Nat
  segsX : List (ℕ × ℕ)
  segsY : List (ℕ × ℕ)
  rawP : List ℕ
  TG : ℕ

def segOk (AA : ℕ) (s : ℕ × ℕ) : Bool := decide (s.1 < s.2) && decide (AA % 2 ^ s.2 + 2 ^ (s.1 + 1) = 2 ^ s.2 + AA % 2 ^ s.1) &&
  !AA.testBit s.1 && !AA.testBit s.2
def bitsOf (L : List (ℕ × ℕ)) : ℕ := L.foldr (fun s x => 2 ^ s.2 ||| x) 0
def segGood (w o : ℕ) (s : ℕ × ℕ) : Bool :=
  Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) 0 || Nat.beq ((w >>> (o + s.1 + 1)) % 2 ^ (s.2 - s.1 - 1)) (2 ^ (s.2 - s.1 - 1) - 1)

structure InstOk (I : Inst) : Prop where
  segX_ok : I.segsX.all (segOk I.AA) = true
  segY_ok : I.segsY.all (segOk I.AA) = true
  HX_eq : I.HX = bitsOf I.segsX
  HY_eq : I.HY = bitsOf I.segsY
  AA_TG : I.AA &&& I.TG = I.AA
  TG_lt : I.TG < 2 ^ I.NN
  AA_lt : I.AA < 2 ^ I.NN
  raw_good : I.rawP.all (fun w => I.segsX.all (segGood w 0) && I.segsY.all (segGood w I.NN)) = true
  rawP_len : I.rawP.length = 6


noncomputable section coreC
def st (n : Nat) (f : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) (f 0) (fun m _ => f m) (Nat.succ n)
def spC (NN : Nat) (d : Bool) (l s : Nat) : Nat :=
  Nat.land (Nat.xor s (Nat.land (Nat.shiftRight s NN) l)) (Bool.rec (motive := fun _ => Nat) (Nat.land s l) l d)
def covC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor (spC NN d l w.s) ih) v
def twiceC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w t ih => Nat.lor (Nat.land (spC NN d l w.s) (covC NN d l t)) ih) v
def hitC (HX HY : Nat) (f e : Nat) : Bool := (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (true) (false) (Nat.beq (Nat.land (Nat.land f e) HY) 0))) (false) (Nat.beq (Nat.land (Nat.land f e) HX) 0))
def hitsC (HX HY : Nat) (f : Nat) (m : List Nat) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun e _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (hitC HX HY f e))) (m))
def flagC (NN AA : Nat) (d : Bool) (l o : Nat) (w : W) : Nat := Nat.add (Nat.land (spC NN d l w.s) o) AA
def rectC (NN AA HX HY : Nat) (d : Bool) (l o : Nat) (v : List W) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => false)
    (fun w _ ih m => (Bool.rec (motive := fun _ => Bool) (ih (flagC NN AA d l o w :: m)) (true) (hitsC HX HY (flagC NN AA d l o w) m))) v
def app (x y : List Nat) : List Nat := List.rec (motive := fun _ => List Nat) y (fun e _ ih => e :: ih) x
def joinC (HX HY : Nat) (k : List Cm → Bool) (f : Nat) (cs : List Cm) : List Nat → List Nat → List Cm → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → List Cm → Bool) (fun S O R => k (⟨S, O⟩ :: R))
    (fun c _ ih S O R => Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (ih S O (c :: R)) (ih (app c.a S) (app c.b O) R) (hitsC HX HY f c.b))
      (Bool.rec (motive := fun _ => Bool) (ih (app c.b S) (app c.a O) R) true (hitsC HX HY f c.b)) (hitsC HX HY f c.a)) cs
def bipC (NN AA HX HY : Nat) (l o : Nat) (v : List W) : List Cm → Bool :=
  List.rec (motive := fun _ => List Cm → Bool) (fun _ => false)
    (fun w _ ih cs => (fun f => joinC HX HY ih f cs [f] [] []) (flagC NN AA false l o w)) v
def anyEC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) false (fun f t ih => Bool.rec (motive := fun _ => Bool) ih true (hitsC HX HY f t)) m
def rmFC (HX HY : Nat) (f : Nat) (m : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun e t ih => Bool.rec (motive := fun _ => List Nat) (e :: ih) t (hitC HX HY f e)) m
def starC (HX HY : Nat) (m : List Nat) : Bool := List.rec (motive := fun _ => Bool) true (fun f t ih => Bool.rec (motive := fun _ => Bool) ih
  (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) true false (anyEC HX HY (rmFC HX HY f t))) false (hitsC HX HY f (rmFC HX HY f t))) (anyEC HX HY t)) (hitsC HX HY f t)) m
def flkC (NN AA : Nat) (l o : Nat) (v : List W) : (List Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k []) (fun w _ ih k => (fun f => ih (fun r => k (f :: r))) (flagC NN AA false l o w)) v
def mkXC (NN : Nat) (d : Bool) (l o : Nat) (v : List W) : List XW :=
  List.rec (motive := fun _ => List XW) [] (fun w _ ih => ⟨w, w.s, Nat.shiftRight w.s NN, Nat.land (spC NN d l w.s) o⟩ :: ih) v
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
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def scan (p : XW → Bool) (xs : List XW) : Bool := (List.rec (motive := fun _ => Bool) (false) (fun c _ jh => (Bool.rec (motive := fun _ => Bool) (jh) (true) (p c))) (xs))
def pairs (h : XW → XW → Bool) (xs : List XW) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a r ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) (scan (h a) r))) (xs))
def pairsP (q : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (h a c) (false) (Nat.beq c.s q))) xs) (Nat.beq a.s q))) xs
def pairsQ (q q' : Nat) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  scan (fun a => (Bool.rec (motive := fun _ => Bool) (false) (scan (fun c => (Bool.rec (motive := fun _ => Bool) (false) (h a c) (Nat.beq c.s q'))) xs) (Nat.beq a.s q))) xs
def fr (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) ih (a :: ih) (Nat.beq a.w.r 0)) xs
def fs (xs : List XW) : List XW := List.rec (motive := fun _ => List XW) [] (fun a _ ih => Bool.rec (motive := fun _ => List XW) (a :: ih) ih (Nat.beq a.w.r 0)) xs
def pairsN (h : XW → XW → Bool) (xs : List XW) : Bool :=
  Bool.rec (motive := fun _ => Bool) (scan (fun a => scan (h a) (fs xs)) (fr xs)) true (pairs h (fr xs))
def pairsS (h : XW → XW → Bool) (xs : List XW) : Bool := pairs h (fs xs)
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st (Nat.sub z a.c) (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wstC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twiceC NN d l v)
def nodeC (NN : Nat) (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v))
  (mid f m g e (Nat.pred n) z v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cvC (NN : Nat) (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)) b d
def tstC (NN AA HX HY : Nat) (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flkC NN AA l (wstC NN d l v) v (starC HX HY))) false (bipC NN AA HX HY l (wstC NN d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rectC NN AA HX HY d l (wstC NN d l v) v [])) (Nat.beq n e)) v.length
def mvC (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v v)) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def lookC (NN AA HX HY : Nat) (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end coreC

def bigNat_0 : Nat := ([0, 18442240156254003199, 18158504900851138551, 16933464211838588415, 18158468540270344063, 18374677681430780863, 536739807] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_1 : Nat := ([0, 4503917455548416, 288239172858413064, 70387074476544] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_2 : Nat := ([0, 0, 0, 1513209474796486656, 288275533439207552, 72066392278770752, 537002016] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_3 : Nat := ([12297829382473034410, 4503281799192575, 17870292116834877440, 16884980166377084415, 4159569226461966633, 5654957244412480405, 110913987, 619403873290813440, 11676163710540334404, 434878876264450082, 30923638702356, 962089447427, 4193280] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_4 : Nat := ([14757395258967641292, 18437737097793560575, 288212784419438583, 7650630619567604736, 14433567196928218902, 12832323625198065802, 157587022, 1315369008966402048, 4917970857766195337, 6936160329754030152, 9221333267452527176, 2305286656330039352, 34351349760] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_5 : Nat := ([17361641481138401520, 18442239950095171584, 288221579041570823, 13886638310461394944, 8247082993886701403, 15899649995510436143, 297393044, 2695459721929818112, 6976157360963267265, 40624911656073365, 9221685248444597420, 13835110900526219648, 140668768879103] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_6 : Nat := ([18374966859414961920, 25769148416, 17870283321463537648, 9280018857530086911, 10636535307103334500, 2650693365792899635, 508109977, 5184070314190962688, 13896577591084727425, 12249919936273375513, 9221925079552624888, 16140478920733488128, 576179277326713343] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_7 : Nat := ([18446462603027742720, 18442240130484797440, 57409527, 40039797106671616, 16365824778302521927, 4103276361674653731, 477218590, 8755006025024667648, 9266987197406629644, 14905507908735255009, 3888, 68702696891, 576319980451134464] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_8 : Nat := ([18446744069414584320, 0, 18158504900793729024, 67624344824436223, 279223185218487416, 13906561360151632828, 528611359, 9079265507432988672, 432622649613742080, 17067346811150074366, 4032, 16140539187731365888, 576319980451134975] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_9 : Nat := ([] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_10 : Nat := ([] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def bigNat_11 : Nat := ([18368189366358550664, 18442240156254003199, 18158504900851138551, 16933464211838588415, 18158468540270344063, 18374677681430780863, 536739807] : List Nat).foldr (fun x a => x + 18446744073709551616 * a) 0
def NN0 : Nat := 414
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 77), (77, 80), (80, 83), (83, 97), (97, 99), (99, 102), (102, 116), (116, 131), (131, 146), (146, 148), (148, 151), (151, 154), (154, 157), (157, 171), (171, 186), (186, 201), (201, 203), (203, 205), (205, 209), (209, 212), (212, 215), (215, 218), (218, 222), (222, 226), (226, 238)]
def segsY0 : List (ℕ × ℕ) := [(238, 248), (248, 250), (250, 252), (252, 263), (263, 267), (267, 271), (271, 274), (274, 276), (276, 289), (289, 292), (292, 296), (296, 299), (299, 301), (301, 314), (314, 326), (326, 330), (330, 333), (333, 336), (336, 338), (338, 351), (351, 363), (363, 376), (376, 389), (389, 401), (401, 413)]
def rawP0 : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8]
def TG0 : ℕ := bigNat_11
def I : Inst := ⟨NN0, AA0, HX0, HY0, segsX0, segsY0, rawP0, TG0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segX_ok0 : segsX0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma segY_ok0 : segsY0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HX_eq0 : HX0 = bitsOf segsX0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma HY_eq0 : HY0 = bitsOf segsY0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_TG0 : AA0 &&& TG0 = AA0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma TG_lt0 : TG0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma AA_lt0 : AA0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_good0 : rawP0.all (fun w => segsX0.all (segGood w 0) && segsY0.all (segGood w NN0)) = true := by decide +kernel
lemma IOk : InstOk I := ⟨segX_ok0, segY_ok0, HX_eq0, HY_eq0, AA_TG0, TG_lt0, AA_lt0, raw_good0, rfl⟩

section engine

noncomputable section core
abbrev sp := spC I.NN
abbrev cov := covC I.NN
abbrev twice := twiceC I.NN
abbrev hit := hitC I.HX I.HY
abbrev hits := hitsC I.HX I.HY
abbrev flag := flagC I.NN I.AA
abbrev rect := rectC I.NN I.AA I.HX I.HY
abbrev join := joinC I.HX I.HY
abbrev bip := bipC I.NN I.AA I.HX I.HY
abbrev anyE := anyEC I.HX I.HY
abbrev rmF := rmFC I.HX I.HY
abbrev star := starC I.HX I.HY
abbrev flk := flkC I.NN I.AA
abbrev mkX := mkXC I.NN
abbrev wst := wstC I.NN
abbrev node := nodeC I.NN
abbrev cv := cvC I.NN
abbrev tst := tstC I.NN I.AA I.HX I.HY
abbrev mv := mvC I.NN I.AA I.HX I.HY
abbrev look := lookC I.NN I.AA I.HX I.HY
abbrev look1 := look1C I.NN I.AA I.HX I.HY
end core

lemma bR (c e t : Bool) : (Bool.rec (motive := fun _ => Bool) e t c : Bool) = bif c then t else e := by cases c <;> rfl
lemma st_eq (n : ℕ) (f : ℕ → Bool) : st n f = f n := by cases n <;> rfl
lemma nl (a b : ℕ) : Nat.land a b = a &&& b := rfl
lemma no (a b : ℕ) : Nat.lor a b = a ||| b := rfl
lemma nx (a b : ℕ) : Nat.xor a b = a ^^^ b := rfl
lemma nsr (a b : ℕ) : Nat.shiftRight a b = a >>> b := rfl
lemma sp_bit (d : Bool) (l s i : ℕ) : (sp d l s).testBit i = (l.testBit i && sepb I.NN d s i) := by
  cases d <;> simp [sp, spC, sepb, nl, nx, nsr, Nat.testBit_shiftRight] <;>
    cases l.testBit i <;> cases s.testBit i <;> cases s.testBit (I.NN + i) <;> rfl
lemma cov_bit (d : Bool) (l i : ℕ) (v : List W) : (cov d l v).testBit i = true ↔ ∃ w ∈ v, (sp d l w.s).testBit i = true := by
  induction v with
  | nil => simp [cov, covC]
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
    (hu : (Nat.land (sp d l w.s) (wst d l v)).testBit i = true) : l.testBit i = true ∧ Uq I.NN d S w.s i := by
  simp only [nl, wst, wstC, nx, Nat.testBit_and, Nat.testBit_xor, Bool.and_eq_true, sp_bit] at hu
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

section engine_ok
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
def Good (l s : ℕ) : Prop := (∀ i j, Same I.segsX i j → l.testBit i = true → l.testBit j = true → s.testBit i = s.testBit j) ∧
  (∀ i j, Same I.segsY i j → l.testBit i = true → l.testBit j = true → s.testBit (I.NN + i) = s.testBit (I.NN + j))
lemma flag_seg {L : List (ℕ × ℕ)} (hL : L.all (segOk I.AA) = true) {u : ℕ} (hu : ∀ i, u.testBit i = true → I.AA.testBit i = true)
    {s : ℕ × ℕ} (hs : s ∈ L) (hb : (u + I.AA).testBit s.2 = true) : ∃ i, s.1 < i ∧ i < s.2 ∧ u.testBit i = true := by
  have h := List.all_eq_true.1 hL s hs
  simp only [segOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  refine carry h.1.1.1 h.1.1.2 h.2 ?_ ?_ hb
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.2] at this; simp at this
  · by_contra hc; have := hu _ (by simpa using hc); rw [h.1.2] at this; simp at this
lemma hit_spec {f e : ℕ} (h : hit f e = true) :
    (∃ s ∈ I.segsX, f.testBit s.2 = true ∧ e.testBit s.2 = true) ∧ (∃ s ∈ I.segsY, f.testBit s.2 = true ∧ e.testBit s.2 = true) := by
  have aux : ∀ H, Nat.beq (Nat.land (Nat.land f e) H) 0 = false → ∃ i, f.testBit i = true ∧ e.testBit i = true ∧ H.testBit i = true := by
    intro H hH
    have hne : (f &&& e &&& H) ≠ 0 := fun h0 => by rw [nl, nl, h0] at hH; simp at hH
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
    simp at hi; exact ⟨i, hi.1.1, hi.1.2, hi.2⟩
  simp only [hit, hitC, bR] at h
  cases h1 : Nat.beq (Nat.land (Nat.land f e) I.HX) 0 with
  | true => rw [h1] at h; simp only [cond_true, Bool.false_eq_true] at h
  | false =>
    cases h2 : Nat.beq (Nat.land (Nat.land f e) I.HY) 0 with
    | true => rw [h1, h2] at h; simp only [cond_true, cond_false, Bool.false_eq_true] at h
    | false =>
      obtain ⟨i, a1, a2, a3⟩ := aux _ h1
      obtain ⟨j, b1, b2, b3⟩ := aux _ h2
      rw [IOk.HX_eq] at a3; rw [IOk.HY_eq] at b3
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
  lg : ∀ i, l.testBit i = true → Lg I.NN m T i ∧ I.AA.testBit i = true
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
    bif d' then c.s.testBit (I.NN + i) = false else c.s.testBit i = true := by
  obtain ⟨hli, u1, u2⟩ := uq_of hr ha hu
  obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := X.lg i hli
  obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
  have hac : c.s ≠ a.s := hb.1.symm
  have hsub := hb.sub.2.2 hw
  rw [Finset.mem_insert] at hsub
  have hg : sepb I.NN (pos' t) (op d' a.s c.s) i = true := by
    rcases hsub with rfl | h
    · exact hs
    · have := u2 w h (fun e => hk (e ▸ hw))
      rw [this] at hs; simp at hs
  have hcn := u2 c.s hb.sub.2.1 hac
  revert hg hcn u1
  unfold sepb; simp only [op_bit]
  cases pos' t <;> cases d' <;> cases a.s.testBit i <;> cases a.s.testBit (I.NN + i) <;> cases c.s.testBit i <;>
    cases c.s.testBit (I.NN + i) <;> simp
end sound
def mkx (d : Bool) (l o : ℕ) (w : W) : XW := ⟨w, w.s, Nat.shiftRight w.s I.NN, Nat.land (sp d l w.s) o⟩
lemma mkX_eq (d : Bool) (l o : ℕ) (v : List W) : mkX d l o v = v.map (mkx d l o) := by
  induction v with
  | nil => rfl
  | cons w v ih => change _ :: mkX d l o v = _; rw [ih]; rfl
def modeF (n e : ℕ) : (W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node nodeC modeF
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
def dfc (d d' : Bool) (l o : ℕ) (a c : W) : ℕ := bif d' then Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s I.NN)
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
        have hu : ∀ w, ∀ i, (Nat.land (sp (pos' t) l w) (wst (pos' t) l r)).testBit i = true → I.AA.testBit i = true := by
          intro w i hi
          simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
          exact (X.lg i hi.1.1).2
        obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x1
        obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x2
        obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y1
        obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y2
        obtain ⟨l1, u1⟩ := uq_of hr.rep ha a3
        obtain ⟨l2, u2⟩ := uq_of hr.rep hb' b3
        obtain ⟨l3, u3⟩ := uq_of hr.rep ha c3
        obtain ⟨l4, u4⟩ := uq_of hr.rep hb' d3
        have g1 : ∀ w ∈ S, w.testBit i1 = w.testBit i2 := by
          intro w hw; obtain ⟨w', hw', rfl⟩ := hr.rep.mem.1 hw
          exact (hr.good w' hw').1 _ _ ⟨s, hs1, a1, a2, b1, b2⟩ l1 l2
        have g2 : ∀ w ∈ S, w.testBit (I.NN + j1) = w.testBit (I.NN + j2) := by
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
    (h : hit (flag false l (wst d l r) a) (flag false l (wst d l r) b) = true) : Ht I.NN m T d S a.s b.s := by
  obtain ⟨⟨s, hs1, x1, x2⟩, ⟨s', hs2, y1, y2⟩⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) (wst d l r)).testBit i = true → I.AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  have uq : ∀ {w : W} {i : ℕ}, w ∈ r → (Nat.land (sp false l w.s) (wst d l r)).testBit i = true →
      l.testBit i = true ∧ Uq I.NN d S w.s i ∧ w.s.testBit i = true := by
    intro w i hw hi
    have hi2 := hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi2
    obtain ⟨⟨hl, hs⟩, ho⟩ := hi2
    have hsd : sepb I.NN d w.s i = true := by
      cases d
      · exact hs
      · exact sepb_weak _ hs
    obtain ⟨q1, q2⟩ := uq_of hr.rep hw (d := d) (l := l) (i := i) (by
      simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true]; exact ⟨⟨hl, hsd⟩, ho⟩)
    refine ⟨q1, q2, ?_⟩
    revert hs; simp only [sepb, cond_false]; cases w.s.testBit i <;> simp
  obtain ⟨i1, a1, a2, a3⟩ := flag_seg IOk.segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, b1, b2, b3⟩ := flag_seg IOk.segX_ok (hu b.s) hs1 x2
  obtain ⟨j1, c1, c2, c3⟩ := flag_seg IOk.segY_ok (hu a.s) hs2 y1
  obtain ⟨j2, d1, d2, d3⟩ := flag_seg IOk.segY_ok (hu b.s) hs2 y2
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
  have av : ∀ a : ℕ, a ∈ S → ∃ p q : ℕ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧ p ≠ a ∧ q ≠ a ∧ Ht I.NN m T (pos' t) S p q := by
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := pos' t) hl (hb.min hl hm.2).2 (he t (Or.inr rfl))
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
    obtain ⟨x, f, h1, h2, h3⟩ := chrom (N := I.NN) (e := true) hl (hu.min hl hm.2).2 (Or.inl rfl)
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
        obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := I.NN) (e := pos' t) hm.1 hm.2 (by
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
  simp only [cv, cvC, bR, hcov, cond_true] at h
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
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (I.NN + i) = false else y.s.testBit i = true) →
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
      · change (a.s ^^^ m).testBit (I.NN + i) = (a.s ^^^ m).testBit (I.NN + j)
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
lemma scan_false {p : XW → Bool} {xs : List XW} (h : scan p xs = false) : ∀ c ∈ xs, p c = false := by
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
lemma pairs_false {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) : xs.Pairwise (fun a c => h a c = false) := by
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
lemma pairsP_false {h : XW → XW → Bool} {xs : List XW} {q : ℕ} {a c : XW} (hp : pairsP q h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s ≠ q) : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [beq_f hcq, Bool.cond_false] at h2
lemma pairsQ_false {h : XW → XW → Bool} {xs : List XW} {q q' : ℕ} {a c : XW} (hp : pairsQ q q' h xs = false) (ha : a ∈ xs) (hq : a.s = q)
    (hc : c ∈ xs) (hcq : c.s = q') : h a c = false := by
  have h1 := scan_false hp a ha
  simp only [bR] at h1
  rw [hq, Nat.beq_refl, Bool.cond_true] at h1
  have h2 := scan_false h1 c hc
  beta_reduce at h2
  rwa [hcq, Nat.beq_refl, Bool.cond_true] at h2
lemma pos_eq (t : ℕ) : pos t = pos' t := by cases t <;> simp [pos, pos']
lemma fr_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r = 0) : a ∈ fr xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [h]; simp
    · cases Nat.beq x.w.r 0
      · exact ih ha
      · exact List.mem_cons_of_mem _ (ih ha)
lemma fs_mem {xs : List XW} {a : XW} (ha : a ∈ xs) (h : a.w.r ≠ 0) : a ∈ fs xs := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    change a ∈ Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0)
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [beq_f h]; simp
    · cases Nat.beq x.w.r 0
      · exact List.mem_cons_of_mem _ (ih ha)
      · exact ih ha
lemma pairs_any {h : XW → XW → Bool} {xs : List XW} (hp : pairs h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    h a c = false ∨ h c a = false := by
  have hpw := pairs_false hp
  have : Std.Symm (fun a c : XW => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
  exact (hpw.imp (S := fun a c => h a c = false ∨ h c a = false) fun h => Or.inl h).forall ha hc hne
lemma pairsN_false {h : XW → XW → Bool} {xs : List XW} (hp : pairsN h xs = false) {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c)
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
    {go : (XW → XW → Bool) → List XW → Bool}
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
        have : a.s = c.s := congrArg XW.s e
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
  | zero => intro k t z v S h; simp [look, lookC] at h
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
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (XW → XW → Bool) → List XW → Bool,
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
  | zero => intro k t z v S h; simp [look1, look1C] at h
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e))
end sound

end engine_ok
def xw (e : ℕ × ℕ) : ℕ := I.rawP.getD e.1 0 ||| I.rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := I.rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ I.NN - 1
def kz (Z : ℕ) : ℕ := (List.range 6).foldr (fun i x =>
  let a := I.rawP.getD i 0
  let b := Nat.shiftRight a I.NN
  let z0 := if Z.testBit i then Nat.land (Nat.lor a b) FULL else 0
  let z1 := if Z.testBit (i + 6) then Nat.lor (Nat.land (Nat.xor a FULL) FULL) (Nat.land (Nat.xor b FULL) I.AA) else 0
  Nat.lor x (Nat.lor z0 z1)) 0
def lz (Z : ℕ) : ℕ := Nat.land I.AA (Nat.xor (kz Z) FULL)
def fz (Z : ℕ) : ℕ := Nat.land FPM (Nat.xor (kz Z) FULL)
def mz (Z : ℕ) : ℕ := Nat.lor (Nat.lor (lz Z) (fz Z)) (Nat.shiftLeft (lz Z) I.NN)
def tz (Z : ℕ) : ℕ := Nat.land I.TG (mz Z)

section engine_ok2
lemma lz_lg (Z i : ℕ) (h : (lz Z).testBit i = true) : Lg I.NN (mz Z) (tz Z) i ∧ I.AA.testBit i = true := by
  have hA : I.AA.testBit i = true := by
    simp only [lz, nl, Nat.testBit_and, Bool.and_eq_true] at h; exact h.1
  have hT : I.TG.testBit i = true := by
    have := congrArg (fun x => x.testBit i) IOk.AA_TG
    simp [hA] at this; exact this
  have m1 : (mz Z).testBit i = true := by simp [mz, no, h]
  have m2 : (mz Z).testBit (I.NN + i) = true := by
    simp only [mz, no, Nat.testBit_or, Nat.shiftLeft_eq, Bool.or_eq_true]
    right
    change (lz Z <<< I.NN).testBit (I.NN + i) = true
    rw [Nat.testBit_shiftLeft]; simp [h]
  refine ⟨⟨m1, m2, ?_, ?_⟩, hA⟩
  · simp only [tz, nl, Nat.testBit_and, hT, m1]; rfl
  · simp only [tz, nl, Nat.testBit_and]
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le IOk.TG_lt (Nat.pow_le_pow_right (by omega) (by omega)))]; rfl
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
  have h := List.all_eq_true.1 IOk.raw_good w (by simpa [rawG, rawL, six] using hw)
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
def anySubC (NN : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (covC NN d l t)) l)) true
    (st (Nat.lor c (spC NN d l w.s)) fun c => ih c fun r => h (w :: r))) v
abbrev anySub := anySubC I.NN
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def MM : ℕ := 214
def hb (H x : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def pairsC (H : ℕ) (h : XW → XW → Bool) (xs : List XW) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a r ih => Bool.rec (motive := fun _ => Bool) ih true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (h a x) (hb H (Nat.add a.s x.s))) r)) xs
def topCC (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
abbrev topC := topCC I.NN I.AA I.HX I.HY
def hasP (p : ℕ) (v : List W) : Bool := Bool.rec (motive := fun _ => Bool)
  (List.rec (motive := fun _ => Bool) false (fun w _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq w.s p)) v) true (Nat.beq p 0)
def startvC (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topCC NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
abbrev startv := startvC I.NN I.AA I.HX I.HY
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
lemma pairsC_false {H : ℕ} {h : XW → XW → Bool} {xs : List XW} (hp : pairsC H h xs = false) :
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
    have : Std.Symm (fun a b : XW => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg XW.s e)) hpb
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
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startvC nn aa hx hy l m g B K t p H ph r)))
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
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
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
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  have hE6 : ∀ e ∈ E, e ∈ six := by
    rcases hE with rfl | ⟨e, he, rfl, _⟩
    · simp
    · intro e' he'; simp only [List.mem_singleton] at he'; rw [he']; exact he
  classical
  have hex : ∃ q, Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ E Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hkeq : k = Nat.find hex := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => Nat.find_min hex (by omega) (hs.mono le_rfl hCS)⟩
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
  obtain ⟨M, hMf, hchk⟩ := hb t (by omega)
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
    simp only [startv, startvC, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R E Z) (RZ_R2 E Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine Nat.find_min hex (show q < Nat.find hex by omega) (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx
def FF : ℕ := 2 ^ MM - 1
lemma ffull : mFull [(FF, 1)] = true := by decide +kernel
noncomputable def okT (E Q : List (ℕ × ℕ)) (Z L : ℕ) (ts : List ℕ) : Bool := ts.all (fun t => !chk E Q Z (L - 1) t FF 1)
noncomputable def okE (E Q : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool := pOk e.1 Q && Nat.ble e.2 15 && (Q.any (fun x => Nat.ble e.2 x.2) || okT E Q e.1 e.2 (List.range e.2))
lemma imp_okE {E Q : List (ℕ × ℕ)} {e : ℕ × ℕ} (hE : E = [] ∨ ∃ e' ∈ six, E = [e'] ∧ Imp [] e.1 e.2) (h : okE E Q e = true) (hI : ∀ e' ∈ Q, Imp E e'.1 e'.2) : Imp E e.1 e.2 := by
  simp only [okE, okT, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  refine imp_of hE h.1.1 (Nat.le_of_ble_eq_true h.1.2) hI (h.2.imp (fun ⟨x, hx, hx2⟩ => ⟨x, hx, Nat.le_of_ble_eq_true hx2⟩) fun h t ht =>
    ⟨[(FF, 1)], ffull, fun p hp => ?_⟩)
  simp only [List.mem_singleton] at hp; subst hp; exact h t ht
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
lemma okAll {T U : List (ℕ × ℕ)} (h : U.all (fun e => okE [] (pr T e.1) e) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := fun e he => imp_okE
  (Or.inl rfl) (List.all_eq_true.1 h e he) (fun e' h' => hT e' (List.mem_of_mem_filter h'))
lemma apI {E A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, Imp E e.1 e.2) (hb : ∀ e ∈ B, Imp E e.1 e.2) : ∀ e ∈ A ++ B, Imp E e.1 e.2 := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma imp_ts {E Q : List (ℕ × ℕ)} {L : ℕ} (hE : E = [] ∨ ∃ p ∈ six, E = [p] ∧ Imp [] 0 L) (hp : pOk 0 Q = true) (hL : L ≤ 15) (hI : ∀ e ∈ Q, Imp E e.1 e.2)
    (h : ∀ t < L, ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 (L - 1) t p.1 p.2 = false) : Imp E 0 L :=
  imp_of hE hp hL hI (Or.inr h)
lemma one {E Q : List (ℕ × ℕ)} {K t : ℕ} (h : chk E Q 0 K t FF 1 = false) : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk E Q 0 K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩

end engine_ok2

end engine
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
lemma ex_sol {T : ℕ} (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → Sol Z0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol Z0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol Z0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
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
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (al0 _ _ _) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go
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
theorem fanInTwo_of {gates : List Gate} {o : ℕ}
    (h : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    FanInTwo ⟨gates, o⟩ := by
  intro g hg; obtain ⟨ho, hl⟩ := h g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length t S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg hnot hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have hwm_stay : gv m w g ∈ S → ∀ x ∈ w ++ [gv m w g], x ∈ S := fun h x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact hw x hx; exact h
    have hwm_ins : ∀ x ∈ w ++ [gv m w g], x ∈ insert (gv m w g) S := fun x hx => by
      simp only [List.mem_append, List.mem_singleton] at hx; rcases hx with hx | rfl; exact Or.inr (hw x hx); exact Or.inl rfl
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.and, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have go := ex_sol m gs (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hT
        obtain ⟨k, hk, t, S1, hS1, hl1⟩ := go.live
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) (t + 1) (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨t + 1, by omega, _, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))


section inst_data
def row3g0 : List (ℕ × ℕ) := [(22, 2), (25, 2), (26, 2), (28, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g0ok : row3g0.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g1 : List (ℕ × ℕ) := [(37, 2), (41, 2), (42, 2), (44, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g1ok : row3g1.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g2 : List (ℕ × ℕ) := [(50, 2), (52, 1), (56, 1), (70, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g2ok : row3g2.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g3 : List (ℕ × ℕ) := [(74, 2), (82, 4), (84, 2), (88, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g3ok : row3g3.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g4 : List (ℕ × ℕ) := [(98, 2), (104, 2), (112, 2), (133, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g4ok : row3g4.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g5 : List (ℕ × ℕ) := [(137, 2), (145, 1), (152, 2), (161, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g5ok : row3g5.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g6 : List (ℕ × ℕ) := [(164, 2), (168, 2), (259, 2), (265, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g6ok : row3g6.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g7 : List (ℕ × ℕ) := [(266, 2), (273, 1), (274, 2), (280, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g7ok : row3g7.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g8 : List (ℕ × ℕ) := [(289, 1), (290, 2), (296, 4), (304, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g8ok : row3g8.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g9 : List (ℕ × ℕ) := [(322, 2), (328, 2), (336, 2), (352, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g9ok : row3g9.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g10 : List (ℕ × ℕ) := [(385, 1), (392, 2), (400, 1), (416, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g10ok : row3g10.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g11 : List (ℕ × ℕ) := [(515, 2), (517, 1), (518, 1), (529, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g11ok : row3g11.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g12 : List (ℕ × ℕ) := [(530, 2), (532, 2), (545, 1), (546, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g12ok : row3g12.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g13 : List (ℕ × ℕ) := [(548, 2), (560, 2), (578, 1), (580, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g13ok : row3g13.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g14 : List (ℕ × ℕ) := [(592, 2), (608, 1), (641, 2), (644, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g14ok : row3g14.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g15 : List (ℕ × ℕ) := [(656, 2), (672, 1), (769, 4), (770, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g15ok : row3g15.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g16 : List (ℕ × ℕ) := [(784, 2), (800, 2), (896, 2), (1027, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g16ok : row3g16.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g17 : List (ℕ × ℕ) := [(1029, 1), (1030, 2), (1033, 1), (1034, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g17ok : row3g17.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g18 : List (ℕ × ℕ) := [(1036, 1), (1057, 2), (1058, 1), (1060, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g18ok : row3g18.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g19 : List (ℕ × ℕ) := [(1064, 4), (1090, 2), (1092, 2), (1096, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g19ok : row3g19.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g20 : List (ℕ × ℕ) := [(1120, 1), (1153, 1), (1156, 1), (1160, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g20ok : row3g20.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g21 : List (ℕ × ℕ) := [(1184, 2), (1281, 2), (1282, 2), (1288, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g21ok : row3g21.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g22 : List (ℕ × ℕ) := [(1312, 1), (1537, 2), (1538, 4), (1540, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g22ok : row3g22.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g23 : List (ℕ × ℕ) := [(1568, 2), (1600, 2), (1792, 2), (2051, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g23ok : row3g23.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g24 : List (ℕ × ℕ) := [(2053, 2), (2054, 1), (2057, 1), (2058, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g24ok : row3g24.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g25 : List (ℕ × ℕ) := [(2060, 1), (2065, 1), (2066, 2), (2068, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g25ok : row3g25.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g26 : List (ℕ × ℕ) := [(2072, 4), (2114, 1), (2116, 1), (2120, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g26ok : row3g26.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g27 : List (ℕ × ℕ) := [(2128, 2), (2177, 2), (2180, 2), (2184, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g27ok : row3g27.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g28 : List (ℕ × ℕ) := [(2192, 1), (2305, 2), (2306, 2), (2312, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g28ok : row3g28.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g29 : List (ℕ × ℕ) := [(2320, 1), (2561, 4), (2562, 2), (2564, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g29ok : row3g29.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g30 : List (ℕ × ℕ) := [(2576, 2), (2688, 2), (2816, 2), (3073, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g30ok : row3g30.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g31 : List (ℕ × ℕ) := [(3074, 4), (3076, 4), (3080, 4), (3136, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g31ok : row3g31.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def row3g32 : List (ℕ × ℕ) := [(3200, 2), (3328, 2), (3584, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3g32ok : row3g32.all (fun e => okE [] (pr ([]) e.1) e) = true := by decide +kernel
def rt3 : List (ℕ × ℕ) := row3g0 ++ row3g1 ++ row3g2 ++ row3g3 ++ row3g4 ++ row3g5 ++ row3g6 ++ row3g7 ++ row3g8 ++ row3g9 ++ row3g10 ++ row3g11 ++ row3g12 ++ row3g13 ++ row3g14 ++ row3g15 ++ row3g16 ++ row3g17 ++ row3g18 ++ row3g19 ++ row3g20 ++ row3g21 ++ row3g22 ++ row3g23 ++ row3g24 ++ row3g25 ++ row3g26 ++ row3g27 ++ row3g28 ++ row3g29 ++ row3g30 ++ row3g31 ++ row3g32
lemma r3 : rt3.all (fun e => okE [] (pr ([]) e.1) e) = true := by
  simp only [rt3, List.all_append, Bool.and_true, row3g0ok, row3g1ok, row3g2ok, row3g3ok, row3g4ok, row3g5ok, row3g6ok, row3g7ok, row3g8ok, row3g9ok, row3g10ok, row3g11ok, row3g12ok, row3g13ok, row3g14ok, row3g15ok, row3g16ok, row3g17ok, row3g18ok, row3g19ok, row3g20ok, row3g21ok, row3g22ok, row3g23ok, row3g24ok, row3g25ok, row3g26ok, row3g27ok, row3g28ok, row3g29ok, row3g30ok, row3g31ok, row3g32ok]
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll r3 (by simp)
def row2g0 : List (ℕ × ℕ) := [(3, 3), (5, 2), (6, 2), (9, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g0ok : row2g0.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g1 : List (ℕ × ℕ) := [(10, 3), (12, 1), (17, 2), (18, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g1ok : row2g1.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g2 : List (ℕ × ℕ) := [(20, 3), (24, 5), (33, 3), (34, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g2ok : row2g2.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g3 : List (ℕ × ℕ) := [(36, 3), (40, 5), (48, 3), (66, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g3ok : row2g3.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g4 : List (ℕ × ℕ) := [(68, 2), (72, 3), (80, 5), (96, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g4ok : row2g4.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g5 : List (ℕ × ℕ) := [(129, 4), (132, 2), (136, 3), (144, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g5ok : row2g5.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g6 : List (ℕ × ℕ) := [(160, 3), (257, 5), (258, 6), (264, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g6ok : row2g6.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g7 : List (ℕ × ℕ) := [(272, 5), (288, 5), (320, 3), (384, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g7ok : row2g7.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g8 : List (ℕ × ℕ) := [(513, 5), (514, 5), (516, 4), (528, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g8ok : row2g8.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g9 : List (ℕ × ℕ) := [(544, 4), (576, 2), (640, 3), (768, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g9ok : row2g9.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g10 : List (ℕ × ℕ) := [(1025, 5), (1026, 5), (1028, 5), (1032, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g10ok : row2g10.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g11 : List (ℕ × ℕ) := [(1056, 5), (1088, 3), (1152, 2), (1280, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g11ok : row2g11.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g12 : List (ℕ × ℕ) := [(1536, 5), (2049, 5), (2050, 5), (2052, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g12ok : row2g12.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g13 : List (ℕ × ℕ) := [(2056, 4), (2064, 5), (2112, 2), (2176, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g13ok : row2g13.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def row2g14 : List (ℕ × ℕ) := [(2304, 3), (2560, 5), (3072, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2g14ok : row2g14.all (fun e => okE [] (pr (rt3) e.1) e) = true := by decide +kernel
def rt2 : List (ℕ × ℕ) := row2g0 ++ row2g1 ++ row2g2 ++ row2g3 ++ row2g4 ++ row2g5 ++ row2g6 ++ row2g7 ++ row2g8 ++ row2g9 ++ row2g10 ++ row2g11 ++ row2g12 ++ row2g13 ++ row2g14
lemma r2 : rt2.all (fun e => okE [] (pr (rt3) e.1) e) = true := by
  simp only [rt2, List.all_append, Bool.and_true, row2g0ok, row2g1ok, row2g2ok, row2g3ok, row2g4ok, row2g5ok, row2g6ok, row2g7ok, row2g8ok, row2g9ok, row2g10ok, row2g11ok, row2g12ok, row2g13ok, row2g14ok]
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 (i3)
def row1g0 : List (ℕ × ℕ) := [(1, 7), (2, 8), (4, 6), (8, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g0ok : row1g0.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def row1g1 : List (ℕ × ℕ) := [(16, 8), (32, 8), (64, 6), (128, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g1ok : row1g1.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def row1g2 : List (ℕ × ℕ) := [(256, 8), (512, 9), (1024, 8), (2048, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1g2ok : row1g2.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by decide +kernel
def rt1 : List (ℕ × ℕ) := row1g0 ++ row1g1 ++ row1g2
lemma r1 : rt1.all (fun e => okE [] (pr (rt3 ++ rt2) e.1) e) = true := by
  simp only [rt1, List.all_append, Bool.and_true, row1g0ok, row1g1ok, row1g2ok]
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := okAll r1 (apI i3 i2)
def rt : List (ℕ × ℕ) := (rt3 ++ rt2 ++ rt1).filter (fun e => Nat.ble 4 e.2)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := fun e he => (apI (apI i3 i2) i1) e (List.mem_of_mem_filter he)
def memoCell (width shift : ℕ) : ℕ := Nat.land FF (Nat.shiftLeft (2 ^ width - 1) shift)
noncomputable section memo_data
def memoIter {α : Type} (base : α) (step : α → α) (wrap : Nat → α → α) : Nat → α
  | 0 => base
  | n + 1 => wrap (n + 1) (step (memoIter base step wrap n))

lemma memoIter_eq {α : Type} (base : α) (step : α → α) (wrap : Nat → α → α)
    (hw : ∀ n, wrap n (Nat.rec base (fun _ => step) n) = Nat.rec base (fun _ => step) n) :
    ∀ n, memoIter base step wrap n = Nat.rec base (fun _ => step) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memoIter, ih]
    exact hw (n + 1)

lemma subtypeList_sound {α : Type} {p : α → Prop} (xs : List {x : α // p x}) :
    ∀ x ∈ xs.map Subtype.val, p x := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
  exact a.property

lemma checkedChunks_sound {α : Type} (F : α → Bool)
    (chunks : List {xs : List α // xs.all (fun x => !(F x)) = true}) :
    ∀ x ∈ (chunks.map Subtype.val).flatten, F x = false := by
  intro x hx
  obtain ⟨xs, hxs, hx⟩ := List.mem_flatten.mp hx
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hxs
  have hf := List.all_eq_true.mp a.property x hx
  cases h : F x <;> simp_all


abbrev Runner := Nat → Nat → Nat → List W → Bool
abbrev WireKey := Nat × Nat × Nat × Nat × Nat
abbrev MemoKey := Nat × Nat × Nat × Nat × List WireKey

def packW (v : List W) : List WireKey := v.map (fun w => (w.s,w.a,w.b,w.c,w.r))
def unpackW (v : List WireKey) : List W := v.map (fun (s,a,b,c,r) => ⟨s,a,b,c,r⟩)
lemma unpack_pack (v : List W) : unpackW (packW v) = v := by
  induction v with
  | nil => rfl
  | cons w v ih => cases w; simpa only [packW,unpackW,List.map_cons] using congrArg (List.cons _) ih

def keyRun (run : Nat → Runner) (e : MemoKey) : Bool :=
  run e.1 e.2.1 e.2.2.1 e.2.2.2.1 (unpackW e.2.2.2.2)
def memoWrap (keys : List MemoKey) (fuel : Nat) (run : Runner) : Runner :=
  fun k t z v => if k = 10 then if keys.contains (fuel,k,t,z,packW v) then false else run k t z v else run k t z v
lemma memoWrap_eq (keys : List MemoKey) (run : Nat → Runner)
    (h : ∀ e ∈ keys, keyRun run e = false) (fuel : Nat) : memoWrap keys fuel (run fuel) = run fuel := by
  funext k t z v
  unfold memoWrap
  split_ifs with hk hm
  · have he := h (fuel,k,t,z,packW v) (List.contains_iff_mem.mp hm)
    simpa only [keyRun,unpack_pack] using he.symm
  · rfl
  · rfl

def memoStepC (NN AA HX HY l m g : Nat) (ih : Runner) : Runner := fun k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)

def memoStepS (NN AA HX HY l m g K : Nat) (baseRun : Nat → Runner) (ih : Runner) : Runner := fun k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (baseRun K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)

def memoLookC (NN AA HX HY l m g : Nat) (keys : List MemoKey) : Nat → Runner :=
  memoIter (fun _ _ _ _ => true) (memoStepC NN AA HX HY l m g) (memoWrap keys)
lemma memoLookC_eq (NN AA HX HY l m g : Nat) (keys : List MemoKey)
    (h : ∀ e ∈ keys, keyRun (lookC NN AA HX HY l m g) e = false) :
    memoLookC NN AA HX HY l m g keys = lookC NN AA HX HY l m g := by
  funext fuel
  apply memoIter_eq
  intro n
  exact memoWrap_eq keys (lookC NN AA HX HY l m g) h n

def memoLookS (NN AA HX HY l m g K : Nat) (keysC keysS : List MemoKey) : Nat → Runner :=
  memoIter (fun _ _ _ _ => true)
    (memoStepS NN AA HX HY l m g K (memoLookC NN AA HX HY l m g keysC)) (memoWrap keysS)
lemma memoLookS_eq (NN AA HX HY l m g K : Nat) (keysC keysS : List MemoKey)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoLookS NN AA HX HY l m g K keysC keysS = look1C NN AA HX HY l m g K := by
  unfold memoLookS
  rw [memoLookC_eq NN AA HX HY l m g keysC hC]
  funext fuel
  apply memoIter_eq
  intro n
  exact memoWrap_eq keysS (look1C NN AA HX HY l m g K) hS n
def memoNat (xs : List Nat) : Nat := xs.foldr (fun x a => x + 18446744073709551616 * a) 0
def mn6 : Nat := memoNat [18374966859414961920,25769148416,17870283321463537648,9280018857530086911,10636535307103334500,2650693365792899635,508109977,5184070314190962688,13896577591084727425,12249919936273375513,9221925079552624888,16140478920733488128,576179277326713343]
def mn7 : Nat := memoNat [36028798093755424,68719476802,4611686022722355200,8589934592]
def mn8 : Nat := memoNat [34393325568,2380152403065307136,4398046515332,9223372036854776064]
def mn9 : Nat := mn8 + (memoNat [36028798093755424,68719476802,4611686022722355200,8589934592])
def mn10 : Nat := memoNat [17361641481138401520,18442239950095171584,288221579041570823,13886638310461394944,8247082993886701403,15899649995510436143,297393044,2695459721929818112,6976157360963267265,40624911656073365,9221685248444597420,13835110900526219648,140668768879103]
def mn11 : Nat := 2 ^ 50 + 2 ^ 125 + 2 ^ 155 + 2 ^ 185 + 2 ^ 220
def mn12 : Nat := memoNat [33824,72638701502464,4096,288230376151711744]
def mn13 : Nat := mn12 + (2 ^ 50 + 2 ^ 125 + 2 ^ 155 + 2 ^ 185 + 2 ^ 220)
def mn14 : Nat := memoNat [14757395258967641292,18437737097793560575,288212784419438583,7650630619567604736,14433567196928218902,12832323625198065802,157587022,1315369008966402048,4917970857766195337,6936160329754030152,9221333267452527176,2305286656330039352,34351349760]
def mn15 : Nat := memoNat [1152956689012490241,72057596185413632,4503599631564800,8388608]
def mn16 : Nat := 2 ^ 85 + 2 ^ 245
def mn17 : Nat := mn15 + (2 ^ 85 + 2 ^ 245)
def mn18 : Nat := memoNat [12297829382473034410,4503281799192575,17870292116834877440,16884980166377084415,4159569226461966633,5654957244412480405,110913987,619403873290813440,11676163710540334404,434878876264450082,30923638702356,962089447427,4193280]
def mn19 : Nat := (memoNat [34603009,68719478848,4294967300,8]) * 2 ^ 15
def mn20 : Nat := 1 + 2 ^ 75 + 2 ^ 80 + 2 ^ 240
def mn21 : Nat := mn19 + (1 + 2 ^ 75 + 2 ^ 80 + 2 ^ 240)
def mn22 : Nat := (memoNat [4294967295,15564440312192434176,13505686152975218687,17293897851305213947,9152118993335615489,2270368502436988896,0,17871391631240857568,9295150346450041857,17321281938815,0,18428727475639858912,134184951]) * 2 ^ 32
def mn23 : Nat := memoNat [1049600,70368744177728,137438953600,8796093022208]
def mn24 : Nat := memoNat [37191016243003392,0,4760445543618969600,8456,512]
def mn25 : Nat := mn23 + (memoNat [37191016243003392,0,4760445543618969600,8456,512])
def mn26 : Nat := memoNat [18446462603027742720,18442240130484797440,57409527,40039797106671616,16365824778302521927,4103276361674653731,477218590,8755006025024667648,9266987197406629644,14905507908735255009,3888,68702696891,576319980451134464]
def mn27 : Nat := memoNat [1152921505680588833,2199023321090,4,274877906952]
def mn28 : Nat := memoNat [37190980844126208,0,4539918974976,8192,16]
def mn29 : Nat := mn27 + (memoNat [37190980844126208,0,4539918974976,8192,16])
def mn505 : Nat := memoNat [4165393823095770739,15396935601262669031,2826517241395632714,5680600897694086045,8985]
def mn506 : Nat := mn505 - (memoNat [37191016244052992,70368744177728,4760445681057923200,8796093030664,512])
def mn507 : Nat := mn505 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn508 : Nat := memoNat [4091084427094509107,10710867481562688611,16522104441292798406,14615742540680410012,9512]
def mn509 : Nat := memoNat [4128239090701813299,10636485517729049765,2831157180469164354,5104140136532292253,9512]
def mn510 : Nat := memoNat [1787422848916801073,12944725462423411811,16801327618449820102,14894965718097474460,9512]
def mn511 : Nat := mn509 + (memoNat [17294913284637459487,145206531848191,139611588578508800,558446354053988352])
def mn512 : Nat := mn510 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn513 : Nat := mn511 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn514 : Nat := memoNat [1857228679650363985,10641061753908337895,7289729611811342922,5383363321733985437,9513]
def mn515 : Nat := memoNat [3011311268569663026,13018889720603845863,7438348399652977226,5086125746604356765,9513]
def mn516 : Nat := mn514 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn517 : Nat := mn515 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn518 : Nat := mn514 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn519 : Nat := Nat.xor mn518 ((memoNat [105556439204871,15874199205894,141733920900,335007449864]) * 2 ^ 15)
def mn520 : Nat := mn512 + (memoNat [17329853600579486752,2179232184666177,281337538019328,272404006305784])
def mn521 : Nat := mn513 + (memoNat [18445582989430620162,69341183,140737488486532,562949953675264])
def mn522 : Nat := Nat.xor mn520 ((memoNat [1107303431,70934084034,986012822930200,833223657008]) * 2 ^ 25)
def mn523 : Nat := mn517 + (memoNat [18410680126678238242,2324367583350783,140737488486400,562949953675264])
def mn524 : Nat := mn518 + (memoNat [1152958955646942177,4431031996252094,281337538019196,272404006305784])
def mn525 : Nat := mn519 + (memoNat [18409589411143516161,2251799880927231,140737488486400,562949953675264])
def mn526 : Nat := mn519 + (memoNat [35148971080673,69733228537251774,4362724704124796,18286802523389944])
def mn527 : Nat := mn519 + (memoNat [1115766807714594817,72057596187574272,4503599631564800,18014398517862400])
def mn528 : Nat := memoNat [5282286495215537748,13016785259781729509,16661570752602393162,14903973192246899356,8984]
def mn529 : Nat := mn528 - (memoNat [37191016244052992,70368744177728,4760445681057923200,8796093030664,512])
def mn530 : Nat := memoNat [5279998411550640756,10785179143157099689,16368700308264012238,5392361999790379668,8473]
def mn531 : Nat := mn506 - (memoNat [1152956689047093217,144112993349603326,4503737074712572,9006924393611264])
def mn532 : Nat := Nat.xor mn506 (memoNat [34609376,72495214702823822,137443148548,18032815337635840])
def mn533 : Nat := mn506 - (memoNat [17293823702975184864,4501400742529021,140874927570940,281200099328000])
def mn534 : Nat := mn528 + (memoNat [17293822569102703647,68169720856513,13835058197016084480,8521215115255])
def mn535 : Nat := mn534 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn536 : Nat := mn530 + (memoNat [16140901097749349342,68169720791163,4616326090636263672,17042430230776,496])
def mn537 : Nat := mn531 + (memoNat [33287047104,136339441713276,4755937678954725624,17042430230776,496])
def mn538 : Nat := mn507 - (memoNat [1169304910848,4433231021606848,281474976841600,272678884212744])
def mn539 : Nat := mn507 - (memoNat [16140901097781885887,2177033092140987,140737488355192,553604104847352])
def mn540 : Nat := mn528 - (memoNat [38280597907473408,2305845210451542080,4899916257408585728,288221580595560448])
def mn541 : Nat := mn528 - (memoNat [1125934300169216,2380227174285180926,144119444522668164,9799823984743678208])
def mn542 : Nat := mn534 - (memoNat [1189020671478333473,72055399311675394,9007203558096896,9006924393611256])
def mn543 : Nat := mn541 + (memoNat [17294913284637459487,145206531848191,139611588578508800,558446354053988352])
def mn544 : Nat := mn534 - (memoNat [17329853600579485728,2249600928843777,281479271940096,281200099327992])
def mn545 : Nat := mn543 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn546 : Nat := memoNat [3010150149863919218,10641134321675836713,2529279665712351950,5383372392704914333,8985]
def mn547 : Nat := mn505 - (memoNat [1161084312552480,2377973312891324350,148618787841646460,594466080118800384])
def mn548 : Nat := mn546 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn549 : Nat := mn547 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn550 : Nat := mn505 - (memoNat [1152994141160930273,148546224369176510,9288674240102268,9279603277824000])
def mn551 : Nat := mn505 - (memoNat [36318277041121,74236828303036350,4644337120051068,18568277500624896])
def mn552 : Nat := Nat.xor mn528 (memoNat [1024,492581209243712,141733920768,26388279066624])
def mn553 : Nat := mn552 - (memoNat [37191016277606400,0,4760450083537944576,8456,528])
def mn554 : Nat := memoNat [5281124311424945780,10636703294180076775,16512811231567231430,5680609960075072148,8456]
def mn555 : Nat := mn536 + (memoNat [2343033992205303842,2199023386628,144119727994830856,549755822096,16])
def mn556 : Nat := mn555 - (memoNat [37191016277606400,0,4760450083537944576,8456,528])
def mn557 : Nat := Nat.xor mn554 (memoNat [1056,2752135273251865038,776,576460761161793536,1])
def mn558 : Nat := mn550 + ((memoNat [571474433,68719478817,73014444100,4294967304]) * 2 ^ 16)
def mn559 : Nat := mn558 - (memoNat [37191016277606400,0,4760450083537944576,8456,528])
def mn560 : Nat := mn532 - (memoNat [1048576,0,4539914780672,0,16])
def mn561 : Nat := mn505 - (memoNat [17293823702974135264,4431031998351293,140737488486268,272404006305792])
def mn562 : Nat := mn561 - (memoNat [37191016277606400,0,4760450083537944576,8456,528])
def mn563 : Nat := mn539 - (memoNat [1073741825,65536,4760304806130614272,264,512])
def mn564 : Nat := mn505 + (memoNat [2305843009213628418,13686443528186626048,277078015,532575944704,31])
def mn565 : Nat := mn506 + (memoNat [2305843009213628418,13686443528186626048,277078015,532575944704,31])
def mn566 : Nat := memoNat [6471273116225620565,8405028801676160167,2831165839127558606,14615734294343209893,9528]
def mn567 : Nat := memoNat [6398016983646422581,10710799172188351655,11901134013809240526,14327503918459916692,8504]
def mn568 : Nat := mn529 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn569 : Nat := mn567 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn570 : Nat := Nat.xor mn508 ((memoNat [67109889,15504314818,145298743759000,283467842096]) * 2 ^ 25)
def mn571 : Nat := mn508 - (memoNat [18409589376782695424,2305840878909915007,13835058192586899328,7])
def mn572 : Nat := Nat.xor mn567 (memoNat [1152921576752021505,65602,9395380074956194692,9070970929673,1056])
def mn573 : Nat := mn510 - (memoNat [16104837083103754238,72057594037927807,13835058192716922752,7])
def mn574 : Nat := memoNat [4092174044157857363,12944727663592121573,2970768485445487178,14885958793729020829,9496]
def mn575 : Nat := mn512 - (memoNat [18410714211537680383,2251799813619583,13835058192720985984,7])
def mn576 : Nat := mn574 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn577 : Nat := memoNat [6398089585738991157,8330719339105070179,11910418418708982218,5392371036401586852,9528]
def mn578 : Nat := memoNat [4094428007561283123,10564577319965793379,12189641595866003914,5671594213818651300,9528]
def mn579 : Nat := mn578 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn580 : Nat := mn566 - (memoNat [2307039277930774530,144115190225440704,153122249900031872,8998403178496000])
def mn581 : Nat := memoNat [5318316427214145076,10638741578146227431,2826662377069161038,14309498316035085221,9528]
def mn582 : Nat := mn566 - (memoNat [1128167648559105,4503599698741184,144396525613875072,272678884212736])
def mn583 : Nat := mn566 - (memoNat [1133870351394,16143225503013277632,140599915319167,288784529743937536])
def mn584 : Nat := mn580 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn585 : Nat := Nat.xor mn584 ((memoNat [246291715064833,2267742812174,141733921692,335007449864]) * 2 ^ 15)
def mn586 : Nat := mn520 + (memoNat [1152921504606846977,2130303844352,0,266287972352])
def mn587 : Nat := Nat.xor mn528 (memoNat [1162183790559232,0,14876374735918202880,8193,1536])
def mn588 : Nat := Nat.xor mn529 (memoNat [96,68719476742,5504243169576878080,8589934600,1024])
def mn589 : Nat := mn566 - ((memoNat [34394341377,0,4429185028,8]) * 2 ^ 30)
def mn590 : Nat := mn583 + (memoNat [1099511628834,2322237279571968,140737488486400,562949953683200])
def mn591 : Nat := Nat.xor mn567 ((memoNat [34461652995,0,282304065568796,17592186044424]) * 2 ^ 30)
def mn592 : Nat := mn584 + (memoNat [18410717543358594016,4433162300096445,13835339388525215616,272670294278143])
def mn593 : Nat := mn574 + (memoNat [1227268248603459617,2199023321090,9079833755652,274877923080,32])
def mn594 : Nat := mn593 - (memoNat [36028832453493792,70437463654466,4611686160161308800,8804682957056])
def mn595 : Nat := mn594 + ((memoNat [17592689885695,1030792181759,144115252500365372,270582939768]) * 2 ^ 16)
def mn596 : Nat := mn576 + (memoNat [1227302367857213472,2199023255554,9079837818884,274877923080,32])
def mn597 : Nat := mn596 - (memoNat [36028832453493792,70437463654466,4611686160161308800,8804682957056])
def mn598 : Nat := mn530 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn599 : Nat := mn531 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn600 : Nat := mn565 - (memoNat [1133872481249,4503531046373438,140733193650304,281466387300352])
def mn601 : Nat := mn536 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn602 : Nat := mn601 + ((memoNat [1065151856673,4362930923567100,272678883815428,272678884196352]) * 2 ^ 10)
def mn603 : Nat := mn538 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn604 : Nat := mn546 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn605 : Nat := mn547 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn606 : Nat := mn548 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn607 : Nat := mn549 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn608 : Nat := mn550 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn609 : Nat := mn551 + (memoNat [1152921504606780417,13686441397882781632,142010998651,266287972352,31])
def mn610 : Nat := mn507 + (memoNat [1152921504606780417,13686511766626959296,142010998783,9062380994560,31])
def mn611 : Nat := mn606 + (memoNat [1128167648559105,2310346608912435136,144396663052828672,281474977234944])
def mn612 : Nat := mn608 + (memoNat [37452147391488,76561193801678784,4785074604343296,281474977234944])
def mn613 : Nat := mn564 - (memoNat [1133872448481,2181362488510526,140595754696704,272670294278144])
def mn614 : Nat := mn564 + ((memoNat [1099511627777,2201237782462,131196,266287972600]) * 2 ^ 26)
def mn615 : Nat := mn565 + ((memoNat [1099511627777,2201237782462,131196,266287972600]) * 2 ^ 26)
def mn616 : Nat := memoNat [6470110932469631573,8479333793052077291,2682410857877154386,4815910318189458333,9017]
def mn617 : Nat := mn598 + (memoNat [68157408,2454386956977569858,8800253771912,17870283329727627264])
def mn618 : Nat := mn555 + (memoNat [33554464,18374688676543264706,8804821630851,18428721153976565760,31])
def mn619 : Nat := mn530 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn620 : Nat := memoNat [6507300814840220308,10780677742414570667,7442715526702778834,5392080799691068581,9529]
def mn621 : Nat := mn617 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn622 : Nat := Nat.xor mn571 (memoNat [3224374368,72567767433348,13979173273557009292,1])
def mn623 : Nat := mn598 + (memoNat [17293822569102705631,68169720856637,4909204926799544320,8521215115272,992])
def mn624 : Nat := Nat.xor mn523 ((memoNat [37615567873,15393162788864,144256200442249472,1280]) * 2 ^ 20)
def mn625 : Nat := Nat.xor mn617 (memoNat [1152921712043491329,65602,9683610433391166364,9070970930697,1056])
def mn626 : Nat := Nat.xor mn514 (memoNat [2309326263158834178,70375186628608,144115325519003648,8])
def mn627 : Nat := memoNat [4127076976737013363,10713191915711669481,7438343722165029454,5374356397365531805,9497]
def mn628 : Nat := Nat.xor mn516 (memoNat [3380999330235393,70368811352064,144115325514940416,8])
def mn629 : Nat := mn627 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn630 : Nat := mn590 - (memoNat [38280563548750848,4611686018427388032,4899916394981752960,805306112])
def mn631 : Nat := memoNat [6470147181925451349,6024801627390979241,2687046394604890442,4815910309599531685,9528]
def mn632 : Nat := mn580 - (memoNat [34902898154406912,18374616113074929792,4467570830351532159])
def mn633 : Nat := memoNat [5318316392853359220,6024946833922827433,2826657983183399242,5374356663653520037,9528]
def mn634 : Nat := mn582 - (memoNat [34902863828222976,18444421905218797696,4467570830351532159])
def mn635 : Nat := mn583 - (memoNat [34601920,4683600536367267902,4393885761796,8935141652381565184])
def mn636 : Nat := memoNat [4199136770874002035,6029377863570267371,7145618825947069010,5095133494801224869,9529]
def mn637 : Nat := memoNat [5353219359793301076,8407205830265775339,7294237613788703314,4797895919671596197,9529]
def mn638 : Nat := mn636 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn639 : Nat := mn637 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn640 : Nat := mn620 - (memoNat [2305914511895297025,144044823626647488,9147799312531328,8998403178496000])
def mn641 : Nat := mn620 - (memoNat [1152956689011407873,69735427560507328,4503462192480128,18287077401296896])
def mn642 : Nat := mn516 + (memoNat [1128166574817281,16145404664194598848,281337538019199,272678615777272])
def mn643 : Nat := mn629 + (memoNat [1125934267662337,2251799882960896,140875061526528,562949953683456])
def mn644 : Nat := Nat.xor mn530 ((memoNat [193,15032385536,4611712570343817216,17592186044416]) * 2 ^ 30)
def mn645 : Nat := mn589 + (memoNat [0,2,4160749568,8321499136])
def mn646 : Nat := mn577 + (memoNat [73183496093303872,70506183131206,9367487237815533568,25769803776])
def mn647 : Nat := Nat.xor mn598 (memoNat [39624201115533312,0,14295269642338304000,268451889,1024])
def mn648 : Nat := memoNat [4200262670779828883,8335223140593802411,7289733876718193106,5383355075128349861,9529]
def mn649 : Nat := mn641 + (memoNat [1133871398913,2251799880927232,140737488486400,562949953683456])
def mn650 : Nat := Nat.xor mn637 (memoNat [1248448,224719534030912,137438978944,576469548396445696])
def mn651 : Nat := mn620 - ((memoNat [32801,72057594105036800,144115188080054272]) * 2 ^ 35)
def mn652 : Nat := Nat.xor mn620 (memoNat [1082375,15832967509653568,137439871872,1979120930258944])
def mn653 : Nat := Nat.xor mn639 (memoNat [1084608,224717051002944,137438978944,576469548396445696])
def mn654 : Nat := memoNat [4128167622479562355,12946836520319687851,16508320839237319122,5095124699513492116,8505]
def mn655 : Nat := mn654 + (memoNat [2305877059781459969,139611592607074304,4362862147141632,8725724294283264])
def mn656 : Nat := mn567 + (memoNat [16140901098822041598,136339441713151,148755264445481084,17042430230776,496])
def mn657 : Nat := mn601 + (memoNat [68157408,2454386956977569858,8800253771912,17870283329727627264])
def mn658 : Nat := mn654 + (memoNat [33287047104,136339441713276,4755937678954725624,17042430230776,496])
def mn659 : Nat := mn658 + (memoNat [34016174473216,139611592607139840,8725724282093568,8725724294283264])
def mn660 : Nat := mn616 - (memoNat [73183530486629408,74309462571089988,9367491494128128004,9223363257941623040])
def mn661 : Nat := memoNat [4093265823805294131,10638882311341710503,12040886614615599694,14318514311374451356,9016]
def mn662 : Nat := mn605 - (memoNat [34902966871784448,18374616113074929664,4467570830351532159,512])
def mn663 : Nat := mn661 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn664 : Nat := memoNat [6435206865985522259,8330787575261535465,16661434701066082762,5103586532427444636,9016]
def mn665 : Nat := mn604 + (memoNat [68157408,2454386956977569858,8800253771912,17870283329727627264])
def mn666 : Nat := mn606 + (memoNat [68157408,2454386956977569858,8800253771912,17870283329727627264])
def mn667 : Nat := mn608 + (memoNat [68157408,2454386956977569858,8800253771912,17870283329727627264])
def mn668 : Nat := mn609 + (memoNat [68157408,2454386956977569858,8800253771912,17870283329727627264])
def mn669 : Nat := mn659 + (memoNat [1169304911904,4505798789040128,281474976841728,281474977234952])
def mn670 : Nat := Nat.xor mn557 (memoNat [33587200,75229036544,4428115611648,288230376151711744,16])
def mn671 : Nat := mn663 + (memoNat [36031031475733537,2251868671641600,4611967493404360704,281474977234944])
def mn672 : Nat := Nat.xor mn567 (memoNat [98304,213311765348352,824633734016,288247968337756160])
def mn673 : Nat := Nat.xor mn565 (memoNat [1081376,16140916537585303630,829062909952,864708781039157248])
def mn674 : Nat := mn658 + (memoNat [37190982958055488,4400194125828,4508139542151176,549755822096,16])
def mn675 : Nat := Nat.xor mn654 (memoNat [6327328,213374042374528,824633725696,288247968337756160])
def mn676 : Nat := mn670 + (memoNat [35651584,18374686479667492866,9079833755651,18428729950069587968,31])
def mn677 : Nat := mn613 + (memoNat [69207008,2452135157230993538,8800253771912,17870283329727627264])
def mn678 : Nat := Nat.xor mn655 (memoNat [6294560,213380417716608,824633725696,288247968337756160])
def mn679 : Nat := Nat.xor mn678 (memoNat [3401614196743,15762598899693568,422212465983488,1970324837236736])
def mn680 : Nat := mn505 + (memoNat [64,18302633279381172228,8804951654407,18428730224939106304,31])
def mn681 : Nat := mn506 + (memoNat [64,18302633279381172228,8804951654407,18428730224939106304,31])
def mn682 : Nat := Nat.xor mn558 (memoNat [7200,72552380725529026,26397675094172,54069858693808128,32])
def mn683 : Nat := mn531 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn684 : Nat := mn654 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn685 : Nat := mn573 - (memoNat [2305843008174557122,124,4607182414509244540])
def mn686 : Nat := Nat.xor mn531 (memoNat [196832,4769382442849009678,14709600807922196612,8804682956809,1025])
def mn687 : Nat := mn626 - (memoNat [2305843009247249378,68169720922112,139611588318461952])
def mn688 : Nat := Nat.xor mn654 (memoNat [1152921711909273601,65602,9377365659250066332,9070970930697,1056])
def mn689 : Nat := memoNat [1822324682990997137,15180765011723457769,7577955310873565774,5653579574782596253,9497]
def mn690 : Nat := Nat.xor mn518 (memoNat [108852725940224,14747648,4503737066455040,8])
def mn691 : Nat := mn689 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn692 : Nat := mn632 - (memoNat [1090715568308192,16213028958558486528,139611588448485375])
def mn693 : Nat := memoNat [4165394888179435123,10492374723402767529,2826657983313426762,5095133487016596133,9528]
def mn694 : Nat := mn693 + (memoNat [17294913284637459487,145206531848191,139611588578508800,558446354053988352])
def mn695 : Nat := mn584 - (memoNat [35993579362945025,18444492273897965696,4607182418800017535])
def mn696 : Nat := mn694 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn697 : Nat := memoNat [3048467066047284850,12874778926277563627,7433849202497239634,5077119097088660645,9529]
def mn698 : Nat := mn640 - (memoNat [1090715534722049,70368679168000,139611588448485376])
def mn699 : Nat := mn697 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn700 : Nat := memoNat [3049591832082796209,15178515410865851627,7577823653218835026,5653016899706836133,9529]
def mn701 : Nat := mn524 + (memoNat [32,18374688676547459074,3,274869518336])
def mn702 : Nat := mn691 + (memoNat [35218766462977,2251799882960896,140874931503104,562949953683456])
def mn703 : Nat := Nat.xor mn689 (memoNat [1024,70368756760640,896,54051991621468160])
def mn704 : Nat := mn584 + (memoNat [17257796038751747071,4433228872087487,13835339392815988608,272678875824127])
def mn705 : Nat := mn578 + (memoNat [72092780558550112,206158430278,9227875649367048192,25769803776])
def mn706 : Nat := Nat.xor mn694 (memoNat [3148800,70368756760768,137438953472,54051991621468160])
def mn707 : Nat := mn648 + (memoNat [17293822569069150207,2233785415175763967,130023424,260046848])
def mn708 : Nat := mn636 + ((memoNat [65,211106232729600,422212465074304]) * 2 ^ 45)
def mn709 : Nat := Nat.xor mn697 (memoNat [1048576,12582976,137438954368,54051991621468160])
def mn710 : Nat := Nat.xor mn700 (memoNat [1133872645123,15832967910201408,140874928227200,56022316458704896])
def mn711 : Nat := mn684 + (memoNat [74380898615690241,70368744179776,9520750487188537472,8796093039120,1024])
def mn712 : Nat := Nat.xor mn700 (memoNat [1049600,70368758857792,137438954368,54051991621468160])
def mn713 : Nat := mn533 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn714 : Nat := Nat.xor mn681 (memoNat [8070450532489140225,507077172773915008,824663212800,1706442073309184])
def mn715 : Nat := mn535 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn716 : Nat := mn536 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn717 : Nat := mn658 + (memoNat [17293822569069216831,2233860321682913279,130031616,558446354053988352])
def mn718 : Nat := mn717 + (memoNat [34016174473216,139611592607139840,8725724282093568,8725724294283264])
def mn719 : Nat := mn540 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn720 : Nat := mn605 - (memoNat [35993682440027104,16140900997923864576,4607182418800009343,512])
def mn721 : Nat := mn542 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn722 : Nat := mn543 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn723 : Nat := mn544 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn724 : Nat := mn609 - (memoNat [35993648080322561,18444492273897965568,4607182418800017535,512])
def mn725 : Nat := mn546 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn726 : Nat := mn674 - (2 ^ 10 + 2 ^ 50 + 2 ^ 85 + 2 ^ 86 + 2 ^ 110 + 2 ^ 185 + 2 ^ 245 + 2 ^ 246)
def mn727 : Nat := mn548 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn728 : Nat := mn549 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn729 : Nat := mn550 + (memoNat [34603040,18374688676543264770,8942394802179,18428729950069587968,31])
def mn730 : Nat := mn680 - (memoNat [36318242438145,2181431140943808,4644199676903296,18568552370143232])
def mn731 : Nat := mn717 + (memoNat [35185479385088,144115192372924416,9007199258935296,9007199271518216])
def mn732 : Nat := mn532 - (2 ^ 20 + 2 ^ 85 + 2 ^ 165 + 2 ^ 245)
def mn733 : Nat := mn568 + ((memoNat [34636833,2199023386624,145277407330560,8796093038592]) * 2 ^ 30)
def mn734 : Nat := Nat.xor mn568 ((memoNat [7881299549224967,393216,30073159680]) * 2 ^ 85)
def mn735 : Nat := mn554 + (memoNat [1048608,18374688676541167618,4681925787651,18419722750814846976,47])
def mn736 : Nat := mn555 + (memoNat [34603040,18374688676543264770,8942260584451,18428729950069587968,31])
def mn737 : Nat := Nat.xor mn619 (memoNat [6292480,70368758858112,824633721600,63067986969231360])
def mn738 : Nat := mn557 + (memoNat [69206048,18374688676541167618,13482179559427,18419722750814846976,47])
def mn739 : Nat := mn561 + (memoNat [34603040,18374688676545361922,8942394671107,18428729950069587968,31])
def mn740 : Nat := mn739 - ((memoNat [36028797053600801,0,145277407330304,8796101410816]) * 2 ^ 30)
def mn741 : Nat := mn738 + (memoNat [34878,2303736486735769600,134094848,575897802618175488])
def mn742 : Nat := mn614 + (memoNat [62,4607186958576119808,268181504,575897802886348800])
def mn743 : Nat := mn681 + ((memoNat [35184372089855,2130303842302,124,266287972600]) * 2 ^ 16)
def mn744 : Nat := mn730 + (memoNat [2305878193651776512,139541223867088832,4503462196543360,35738525965484032])
def mn745 : Nat := mn655 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn746 : Nat := mn575 - (memoNat [18446744038277121985,65659,4611545276644196476])
def mn747 : Nat := Nat.xor mn533 (memoNat [65760,5048605619745980430,14727052256478257284,8804682956809,1025])
def mn748 : Nat := Nat.xor mn628 (memoNat [34359739425,72567767498752,144255925698560000])
def mn749 : Nat := mn643 - (memoNat [1133872515073,16145545472684132352,140874793357311,288511850860511232])
def mn750 : Nat := mn690 - (memoNat [16140901030102564863,65535,4362862134951936])
def mn751 : Nat := Nat.xor mn691 (memoNat [1153030356325335043,520165759591124992,8650752,10977524117143552])
def mn752 : Nat := mn519 + (memoNat [1152955519706497025,65302196538900480,4221987215638528,18014398517084152])
def mn753 : Nat := mn702 + ((memoNat [17293892937811231709,4191888205691,128844824696,249108103656]) * 2 ^ 15)
def mn754 : Nat := mn634 - (memoNat [1124800395247584,16143223164334243840,143974450587500543])
def mn755 : Nat := Nat.xor mn635 (memoNat [103079316487,13839717787844950016,940445696,866661455171420160])
def mn756 : Nat := mn584 - (memoNat [36027664189884417,18374686479673723008,4611545280939032703])
def mn757 : Nat := Nat.xor mn696 (memoNat [8070450635394318338,148618790333517824,30277632,10977524117143552])
def mn758 : Nat := mn596 - (memoNat [36031031477864448,4503599834988672,4611967493404491904,786176])
def mn759 : Nat := mn694 + ((memoNat [52777597797375,2130303874045,133143986362,399431958900]) * 2 ^ 16)
def mn760 : Nat := Nat.xor mn698 ((memoNat [1108344833,198656,141733920768]) * 2 ^ 15)
def mn761 : Nat := Nat.xor mn641 (memoNat [67808,2321762219744231424,940470272,866661455171420160])
def mn762 : Nat := mn652 - ((memoNat [1101726220353,6665789380608,141012366262656,768]) * 2 ^ 10)
def mn763 : Nat := mn708 + (memoNat [2305875925910092799,137289421899495424,4222124658655232,8162774340599808])
def mn764 : Nat := mn711 - ((memoNat [1142947843,206158436480,146028888076,24]) * 2 ^ 15)
def mn765 : Nat := Nat.xor mn711 ((memoNat [123145319616003,7902739863745,2147484108,141733921160]) * 2 ^ 16)
def mn766 : Nat := mn519 + (memoNat [1152956653577894913,67483627677616064,4362724704124800,18287077401034744])
def mn767 : Nat := mn519 + (memoNat [3458800798811521091,69810194351327236,4503599631564808,18296423250133000])
def mn768 : Nat := mn745 + (memoNat [37191017283190786,135168,9520745947269693440,562949953430032,1008])
def mn769 : Nat := mn533 + (memoNat [1169305895936,70368744177728,9520891224677023872,8796093022728,1024])
def mn770 : Nat := Nat.xor mn533 (memoNat [104152989696,2251799895474176,10115506975539200000,787977,1024])
def mn771 : Nat := mn594 + (memoNat [1152954524348907552,67554065074028546,4222128949428224,17732932130308608])
def mn772 : Nat := mn613 + ((memoNat [1057,16140901062348373952,133278339199,8589934584]) * 2 ^ 40)
def mn773 : Nat := Nat.xor mn759 (memoNat [3148806,70368744583360,137438953472,1697645953286144])
def mn774 : Nat := mn651 + (memoNat [0,2303591209397911552,134086656,268173312])
def mn775 : Nat := mn638 + ((memoNat [65569,216172782315110400,432345564235960320]) * 2 ^ 35)
def mn776 : Nat := Nat.xor mn763 (memoNat [1048582,405568,137438954368,1697645953286144])
def mn777 : Nat := mn710 + ((memoNat [35184372089855,2130303842304,124,248]) * 2 ^ 15)
def mn778 : Nat := Nat.xor mn711 (memoNat [8070450532483039233,520165759593678848,30277632,10977524117143552])
def mn779 : Nat := mn711 - (memoNat [17293823702941631487,18379260446034032703,140874923376767,8734520363188224])
def mn780 : Nat := mn656 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn781 : Nat := mn716 + (memoNat [1152921504640368639,69805796306581504,4063232,17451448564187136])
def mn782 : Nat := mn658 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn783 : Nat := mn659 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn784 : Nat := mn660 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn785 : Nat := mn664 - (memoNat [1124800395182048,16143223164334243840,143974450587492351])
def mn786 : Nat := mn661 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn787 : Nat := mn609 - (memoNat [36027732907261953,18374686479673722880,4611545280939032703,512])
def mn788 : Nat := mn663 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn789 : Nat := mn664 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn790 : Nat := mn665 + (memoNat [33854,2303666117989494784,134094848,575897802618175488])
def mn791 : Nat := mn739 - (memoNat [1159950407600193,2303736484588488704,148478050348965888,576742227548307456])
def mn792 : Nat := mn727 + (memoNat [1152921504640368639,69805796306581504,4063232,17451448564187136])
def mn793 : Nat := mn614 - (memoNat [1127033777193988,16145475032938979264,144255787991302015,1117103545909248])
def mn794 : Nat := mn729 + (memoNat [1152921504640368639,69805796306581504,4063232,17451448564187136])
def mn795 : Nat := mn739 - (memoNat [35184372088834,200704,4503599627370496,844424930131968])
def mn796 : Nat := mn782 + (memoNat [35185479385089,144115192372989952,9007199258935296,9007199271518216])
def mn797 : Nat := mn539 - (memoNat [1040187393,67584,4760300403650723840,281474976710920,496])
def mn798 : Nat := mn671 + (memoNat [32798,2303666049270018048,134094848,575897802618175488])
def mn799 : Nat := Nat.xor mn569 (memoNat [1,422212465133568,824633721728,299067162755072])
def mn800 : Nat := Nat.xor mn565 (memoNat [1082599,2674493388961870,828928819200,1987977154396160])
def mn801 : Nat := Nat.xor mn652 (memoNat [253573777167745024,448,4787327365967511680,26388279093048,1536])
def mn802 : Nat := mn801 - (memoNat [37191016243003393,67584,4760445543618969600,281474976719112,512])
def mn803 : Nat := mn738 + (memoNat [1152921504640368638,69805796308611072,4063232,26177172842217472])
def mn804 : Nat := mn730 + ((memoNat [2251799813685281,0,4096,786432]) * 2 ^ 35)
def mn805 : Nat := Nat.xor mn684 (memoNat [6297600,422212465131904,824633721600,299067162755072])
def mn806 : Nat := Nat.xor mn681 (memoNat [8070450532489140225,507077172773980544,824663212800,1987917050019840])
def mn807 : Nat := Nat.xor mn505 (memoNat [196608,5057965006318993408,892557151149514752,17643725651968,1025])
def mn808 : Nat := mn807 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn809 : Nat := mn566 + (memoNat [14987979593142501373,136339441647677,4640213942796536,25563645346032,496])
def mn810 : Nat := Nat.xor mn656 (memoNat [1152921714056757249,65602,10260053335542071436,9070970930713,1056])
def mn811 : Nat := mn574 + (memoNat [16140901098822041598,136339441713151,148755264445481084,17042430230776,496])
def mn812 : Nat := mn811 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn813 : Nat := mn577 + (memoNat [16140901098822041598,136339441713151,148755264445481084,17042430230776,496])
def mn814 : Nat := mn578 + (memoNat [16140901098822041598,136339441713151,148755264445481084,17042430230776,496])
def mn815 : Nat := mn511 + (memoNat [37191016244053024,140668768878658,148759662630535428,17583596118272,512])
def mn816 : Nat := mn512 + (memoNat [37191016244053024,140668768878658,148759662630535428,17583596118272,512])
def mn817 : Nat := mn814 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn818 : Nat := mn809 - (memoNat [1154117772251234305,144115190225375230,9007199397347324,9006924393611256])
def mn819 : Nat := mn809 - (memoNat [35183331935264,16213031297239418878,18307132485265264635,306244499523239927])
def mn820 : Nat := mn809 - (memoNat [17294950735678570496,4503599698675709,281475111190524,281200099327992])
def mn821 : Nat := mn819 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn822 : Nat := mn818 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn823 : Nat := mn809 + (memoNat [1089582703576095,4537449261058420738,283586039165882372,269653303094935560])
def mn824 : Nat := mn520 + (memoNat [0,70300024700928,0,8787503087616])
def mn825 : Nat := Nat.xor mn534 (memoNat [1162183790559232,0,4611686049461960704,8192,48])
def mn826 : Nat := Nat.xor mn535 (memoNat [3072,68719476928,142565179392,8589934592,32])
def mn827 : Nat := mn809 - ((memoNat [1125935340322817,0,4398046515328,8192]) * 2 ^ 20)
def mn828 : Nat := mn819 + (memoNat [1152956688978936865,72059861784856576,4499201585053696,18014398517870592])
def mn829 : Nat := Nat.xor mn810 (memoNat [109429994269179904,64,13835058884371021824,8589950977,32])
def mn830 : Nat := mn816 - (memoNat [1152989640001552384,141865591444080640,8725724286156804,8725999172190216])
def mn831 : Nat := mn815 + (memoNat [34359771136,2308094809027379200,4228,9223372036854776064])
def mn832 : Nat := Nat.xor mn811 (memoNat [114883571942949888,68719476800,13835058885021138944,8589950977,32])
def mn833 : Nat := mn816 - (memoNat [1152921538966618112,2253998836940800,4,274877906952])
def mn834 : Nat := mn812 + (memoNat [1227302367823659041,2199023321090,4681791307780,274877923336,32])
def mn835 : Nat := mn816 - (memoNat [1152920405162328065,2198954117120,18446612132314087428,281749854355463])
def mn836 : Nat := Nat.xor mn536 (memoNat [196704,14281407480637423622,4927782417273479300,8804682956824,1025])
def mn837 : Nat := mn808 - (memoNat [35185479384096,144115123653447618,13844065254541099012,9007190681583615])
def mn838 : Nat := mn808 - (memoNat [1169304910880,4503531046307778,13835339530259005444,281466387300351])
def mn839 : Nat := Nat.xor mn539 (memoNat [196832,5057612819000721422,5504243169576902788,8804682956856,1025])
def mn840 : Nat := Nat.xor mn546 (memoNat [196640,13993177104485711886,4909768018763997316,8804682956856,1025])
def mn841 : Nat := Nat.xor mn547 (memoNat [65632,14280984855855497230,5504243169576886404,8804682956856,1025])
def mn842 : Nat := Nat.xor mn548 (memoNat [65568,14272400281382682638,4927219467320057988,8804682956856,1025])
def mn843 : Nat := Nat.xor mn549 (memoNat [65632,14280984855855497230,5504243169576886404,8804682956856,1025])
def mn844 : Nat := Nat.xor mn550 (memoNat [65760,4760375243594268686,5485665821113999492,8804682956856,1025])
def mn845 : Nat := Nat.xor mn551 (memoNat [196832,5057612819000721422,5504243169576902788,8804682956856,1025])
def mn846 : Nat := Nat.xor mn587 (memoNat [33784832,2826009247211323456,4428111311744,9223372096984317952])
def mn847 : Nat := mn842 + (memoNat [1128166575865857,2310346608912435198,281475111190528,281474977234944])
def mn848 : Nat := mn844 + (memoNat [37451074699232,76561193801678846,281474981167104,281474977234944])
def mn849 : Nat := mn845 + (memoNat [1152956687938748385,72057596118370302,4362862143209472,18295873494319104])
def mn850 : Nat := mn807 + (memoNat [68719476736,148478045785686144,8935141660703064320,17870283338049126912])
def mn851 : Nat := mn850 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn852 : Nat := Nat.xor mn616 (memoNat [6917529234000838662,393612,9251264456444084504,18141941859840,1056])
def mn853 : Nat := mn852 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn854 : Nat := mn687 + (memoNat [1190112519811762145,138538465034366,4755942218873700604,17317308145920,512])
def mn855 : Nat := mn627 + (memoNat [16140901097749349342,68169720791163,4616326090636263672,17042430230776,496])
def mn856 : Nat := mn629 + (memoNat [17331013584274064383,70368744112253,4616330630555238652,17317308145920,512])
def mn857 : Nat := mn856 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn858 : Nat := mn820 - (memoNat [37152431331606559,2301409780473722884,287948905603928068,287948901711347712])
def mn859 : Nat := memoNat [4164304205965249075,6024869797111770405,7303372485241154114,4815927352029762461,10024]
def mn860 : Nat := mn818 - (memoNat [34902899227099168,18374684282795851780,4160749571])
def mn861 : Nat := mn859 + (memoNat [17294913284637459487,145206531848191,139611588578508800,558446354053988352])
def mn862 : Nat := mn820 - (memoNat [34902864900915232,18444490074939719684,4160749571])
def mn863 : Nat := mn861 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn864 : Nat := mn636 + (memoNat [16140901097749349342,68169720791163,4616326090636263672,17042430230776,496])
def mn865 : Nat := mn809 + (memoNat [34867748174528480,2108858868758658,9074757651354611844,8628897177822822664])
def mn866 : Nat := mn864 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn867 : Nat := mn865 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn868 : Nat := mn864 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn869 : Nat := Nat.xor mn868 ((memoNat [105554230903809,15874199324678,992137445508,335007449864]) * 2 ^ 15)
def mn870 : Nat := Nat.xor mn642 (memoNat [1152921504606846977,65602,908,9070970929152])
def mn871 : Nat := Nat.xor mn555 (memoNat [8106515614459232263,458766,30790785040388,824633729032,48])
def mn872 : Nat := mn536 + ((memoNat [65,4611683819404132352,8528008,562949953421056]) * 2 ^ 20)
def mn873 : Nat := mn827 + (memoNat [0,64,4467570830351532032,8321499136])
def mn874 : Nat := mn813 + (memoNat [73183495020611616,2336462209218,13835058064006316032,25769803776])
def mn875 : Nat := Nat.xor mn836 (memoNat [39624200042840064,0,144116043202953216,268451840,32])
def mn876 : Nat := memoNat [3047341198353781330,8335359480035450213,11906060104793410374,5383380638773695893,10025]
def mn877 : Nat := mn855 + (memoNat [1227268282963197985,2199023321090,9079833755652,274877923336,32])
def mn878 : Nat := mn865 + (memoNat [17293822568029030431,143076232200189,8188,576460477425516536])
def mn879 : Nat := mn876 + (memoNat [68101068488704,139611592607139840,8725724286156800,8725724294283264])
def mn880 : Nat := mn856 + (memoNat [37189881332498432,0,4539918843904,8192,16])
def mn881 : Nat := mn876 + (memoNat [69234939887615,141863392489963520,8866461774643200,8444249317834752])
def mn882 : Nat := mn688 + (memoNat [33287047104,136339441713276,4755937678954725624,17042430230776,496])
def mn883 : Nat := mn882 + (memoNat [34016174473216,139611592607139840,8725724282093568,8725724294283264])
def mn884 : Nat := Nat.xor mn660 (memoNat [1152921714190974977,65602,9683611000326848644,9070970930745,1056])
def mn885 : Nat := memoNat [2940344388923508274,10638882311341645029,2970909497803352778,14318522832589567141,10008]
def mn886 : Nat := mn841 - (memoNat [34902897146724320,18374684282795851776,8800253771779])
def mn887 : Nat := mn885 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn888 : Nat := Nat.xor mn664 (memoNat [1152921574468222977,65998,10260054160981099404,9070970929721,1056])
def mn889 : Nat := mn852 - (memoNat [1154117772251234305,144115190225375230,9007199397347324,9006924393611256])
def mn890 : Nat := mn852 - (memoNat [17294950735678570496,4503599698675709,281475111190524,281200099327992])
def mn891 : Nat := mn844 + (memoNat [69793217536,2454318787256647746,4467570830351532292,17870283329727627776])
def mn892 : Nat := mn845 + (memoNat [69793217536,2454318787256647746,4467570830351532292,17870283329727627776])
def mn893 : Nat := Nat.xor mn643 ((memoNat [225,2251869005479936,131100,844424931966976]) * 2 ^ 10)
def mn894 : Nat := mn670 + (memoNat [34326183936,0,4616325953197309952,256,496])
def mn895 : Nat := mn887 + (memoNat [36031030403040289,2251868671641600,281479271940096,281474977234944])
def mn896 : Nat := mn810 - (memoNat [16140901064495890430,68171935383551,4092,288229826395897840])
def mn897 : Nat := memoNat [5281124346858392148,8330715005348785447,7591602582211340870,4815927627444523941,9992]
def mn898 : Nat := mn882 + (memoNat [37190982991609920,4400194125828,4539918974984,549755822096,16])
def mn899 : Nat := Nat.xor mn882 (memoNat [6442484832,77034600923148,4104,288230925907525680])
def mn900 : Nat := memoNat [4128202912044763731,13018962217437275497,12198785001011358542,4797913237516588453,9993]
def mn901 : Nat := mn890 + (memoNat [2252899325346848,4611758657128890368,288230376420282368,288230376688582656])
def mn902 : Nat := mn900 + ((memoNat [35184336437247,2061584300030,128849018876,541165879536]) * 2 ^ 15)
def mn903 : Nat := Nat.xor mn902 (memoNat [3539053150209,15762598899300352,985162418880512,1970324837236736])
def mn904 : Nat := mn850 + ((memoNat [33,2181499856156670,136339441844228,272678883942400]) * 2 ^ 11)
def mn905 : Nat := mn808 + (memoNat [68719544320,4616189751194546304,9214364837600043264,18428729692363162112])
def mn906 : Nat := mn717 + (memoNat [37191051676484608,70368744177728,9516383085134741632,8796093030928,1008])
def mn907 : Nat := mn689 + (memoNat [33287047104,136339441713276,4755937678954725624,17042430230776,496])
def mn908 : Nat := mn691 + (memoNat [33287047104,136339441713276,4755937678954725624,17042430230776,496])
def mn909 : Nat := mn818 - (memoNat [16176894679257709598,16140900997923864579,4290772995])
def mn910 : Nat := mn859 + ((memoNat [1065151856673,4362930923567100,272678883815428,272678884196352]) * 2 ^ 10)
def mn911 : Nat := mn694 + (memoNat [33287047104,136339441713276,4755937678954725624,17042430230776,496])
def mn912 : Nat := mn816 - (memoNat [35185479384096,144115123653447618,13844065254541099012,9007190681583615])
def mn913 : Nat := mn911 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn914 : Nat := mn865 + ((memoNat [1065151856673,4362930923567100,272678883815428,272678884196352]) * 2 ^ 10)
def mn915 : Nat := mn868 - (memoNat [16141991779997024287,2198958245887,130023424])
def mn916 : Nat := memoNat [4201422654475456049,12944721059945483623,12194149743595043658,5094587588083078557,10025]
def mn917 : Nat := mn877 + (memoNat [1089581629834239,4465389465851783168,279082439538511872,278660227463380992])
def mn918 : Nat := mn524 + (memoNat [1024,18374756846268315712,127,8796084633600])
def mn919 : Nat := mn524 + (memoNat [1152956690088332321,213305255854274,4503874509472132,26663156973576])
def mn920 : Nat := mn524 + (memoNat [2100224,18374897583756671168,274877907327,26388270678016])
def mn921 : Nat := mn782 + (memoNat [35185445863426,2251799883026432,4503599627501568,562949953683464])
def mn922 : Nat := Nat.xor mn717 (memoNat [32,2199035904002,12,54043470406352896])
def mn923 : Nat := mn573 + (memoNat [17294949603954655263,138536317548545,144256200437923968,17317299757312,512])
def mn924 : Nat := mn814 + (memoNat [2377935788733107234,206158430402,13835058063876292608,25769803776])
def mn925 : Nat := Nat.xor mn911 (memoNat [3221225568,2199035904006,0,54043470406352904])
def mn926 : Nat := mn876 + ((memoNat [1090715534753791,68169720922112,126976]) * 2 ^ 75)
def mn927 : Nat := mn916 + (memoNat [1133871366178,2254000986656768,140737488486400,562949953683456])
def mn928 : Nat := mn927 - (memoNat [1152956690086232097,72059795208734722,4503599631564804,274886295560])
def mn929 : Nat := mn926 + ((memoNat [2196808663009,4499270367375360,281200099065604,281200099327488]) * 2 ^ 10)
def mn930 : Nat := mn908 + (memoNat [1227302367857213473,2199023323138,9079837818884,274877923336,32])
def mn931 : Nat := Nat.xor mn929 (memoNat [1340030025731,15762599180441600,985162418618368,1970324837236736])
def mn932 : Nat := mn907 + (memoNat [34016174473216,139611592607139840,8725724282093568,8725724294283264])
def mn933 : Nat := mn907 + (memoNat [2305878161407049793,141867790536605700,8866461770579976,8444799073648656])
def mn934 : Nat := mn885 + (memoNat [1150740073570928673,70510543112192,18307132485001023488,279223176636923903])
def mn935 : Nat := mn841 - (memoNat [35993612681411552,16140900997923864576,8800383787011])
def mn936 : Nat := memoNat [1787422884316728913,12872810802745480421,3110521086251846346,14876969186643555493,10008]
def mn937 : Nat := mn845 - ((memoNat [36283849114655,2251731094272124,133412552700,532575944952]) * 2 ^ 15)
def mn938 : Nat := mn936 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn939 : Nat := mn845 - (memoNat [35993578321707009,18444492273897965568,8800383795203])
def mn940 : Nat := mn856 - (memoNat [2307039242498310145,213920986532022270,13370061536362492,26458372957798392])
def mn941 : Nat := mn882 + (memoNat [36065083084767264,2201164578820,4539784757256,18419723025701150736,15])
def mn942 : Nat := mn856 - (memoNat [1128132216094720,74309396005322750,4644337250205692,17732648663515128])
def mn943 : Nat := mn850 - (memoNat [1127032704466978,16215212659524573182,18307273222883770363,18577073325211639])
def mn944 : Nat := memoNat [1859478247121213073,15176402149448062313,12333616054766099278,5653315691991414181,10009]
def mn945 : Nat := mn908 + (memoNat [37189883479982144,4398042384388,4539918843912,18419723025701150736,15])
def mn946 : Nat := Nat.xor mn702 (memoNat [33554432,504403160415090688,4194304,9007199279906816])
def mn947 : Nat := Nat.xor mn532 (memoNat [34360786944,14680064,13979318546530959360,63050394783187201,528])
def mn948 : Nat := mn938 + ((memoNat [1152887419814543393,68719480962,8590065672,8589934608]) * 2 ^ 15)
def mn949 : Nat := Nat.xor mn811 (memoNat [0,13194154606592,12,63050944539000880])
def mn950 : Nat := memoNat [4128202842251580019,10564716066732549415,7731214170659830342,5653597158395483045,9992]
def mn951 : Nat := mn855 + (memoNat [1190112487598456865,2199023386628,4539918974984,549755822096,16])
def mn952 : Nat := Nat.xor mn855 (memoNat [6442450976,2199038328844,8,63050944539000880])
def mn953 : Nat := mn900 + ((memoNat [33,68786649088,4,272678883688448]) * 2 ^ 10)
def mn954 : Nat := mn932 + (memoNat [1190112487598456897,4398048673796,4539918974984,549755822096,16])
def mn955 : Nat := Nat.xor mn932 (memoNat [6442451136,13194139598860,8,63050944539000880])
def mn956 : Nat := mn933 - (2 ^ 80 + 2 ^ 245)
def mn957 : Nat := mn807 + (memoNat [2048,4755801343803781248,9223090561878073600,18446181140935475712])
def mn958 : Nat := mn957 - (memoNat [1190112486524715041,2199023321090,4539918974980,274877915144,16])
def mn959 : Nat := mn957 - (memoNat [1133871398913,2251799882958848,140737488486400,281474976972800])
def mn960 : Nat := mn907 + ((memoNat [35185409131517,6390911526910,399431958652,798863917800]) * 2 ^ 15)
def mn961 : Nat := mn820 - (memoNat [36027699655900191,16140900995843424260,4294836227])
def mn962 : Nat := mn910 + (memoNat [34016174473216,139611592607139840,8725724282093568,8725724294283264])
def mn963 : Nat := mn816 - (memoNat [2305912313913310241,74309329429139394,13844065254545162244,9007190681583615])
def mn964 : Nat := mn815 - (memoNat [1169304910880,4503531046307778,13835339530259005444,281466387300351])
def mn965 : Nat := mn816 - (memoNat [1169304910880,4503531046307778,13835339530259005444,281466387300351])
def mn966 : Nat := mn924 + (memoNat [32916629291006,67553998499870720,8584986793607164,8162774340599808])
def mn967 : Nat := mn868 - (memoNat [1124800395214880,2196877805568,134086656])
def mn968 : Nat := mn865 + ((memoNat [1098370777057,4499270369472510,281200098934660,281200099327488]) * 2 ^ 10)
def mn969 : Nat := mn881 + (memoNat [1152919203578052609,2299087609632194562,143692975610527748,275145555976])
def mn970 : Nat := mn916 + (memoNat [34016174473216,139611592607139840,8725724282093568,8725724294283264])
def mn971 : Nat := mn868 + ((memoNat [1098370777057,4499270369472510,281200098934660,281200099327488]) * 2 ^ 10)
def mn972 : Nat := mn877 + (memoNat [1123597804307455,4605001058458923008,287808163820605440,287385951757664256])
def mn973 : Nat := mn519 + (memoNat [35148971048929,67551797398538238,4362724704124924,18295598616150008])
def mn974 : Nat := mn538 + (memoNat [1152922639620112417,2199023321090,149679887351812,274877906952,32])
def mn975 : Nat := Nat.xor mn538 (memoNat [202407936,2251799895474176,26552318689280,786432,32])
def mn976 : Nat := mn923 + (memoNat [68101034934272,139611594685419520,13088586425171968,8725724302409728])
def mn977 : Nat := mn817 + (memoNat [72058694625397793,206158495938,13835058063872229376,25769803776])
def mn978 : Nat := mn911 + (memoNat [68099961192416,139609395666292734,13088586425171968,26739847933984760])
def mn979 : Nat := mn879 + ((memoNat [18445618173802708991,67043327,143974450591690752]) * 2 ^ 35)
def mn980 : Nat := mn970 + (memoNat [1133871398946,2253998906281984,140737488486400,562949953683456])
def mn981 : Nat := Nat.xor mn970 (memoNat [1152921505680588803,208898,12,1689124738170888])
def mn982 : Nat := Nat.xor mn929 ((memoNat [1048577,2267742930944,141733920768,280]) * 2 ^ 15)
def mn983 : Nat := mn932 + (memoNat [1227268282963197985,2199025418242,9079833755652,274877923336,32])
def mn984 : Nat := Nat.xor mn932 (memoNat [222966698861428736,2251799880794112,167976980840448,802816,32])
def mn985 : Nat := mn934 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn986 : Nat := mn888 - (memoNat [1124834754919423,16143154994613256192,134078463])
def mn987 : Nat := mn936 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn988 : Nat := mn845 - (memoNat [36027697541939200,18374686479673657344,8800387858435])
def mn989 : Nat := mn948 + ((memoNat [17293857203684376559,1030792180701,62276960252,261993005172]) * 2 ^ 16)
def mn990 : Nat := mn986 + (memoNat [1124800395215902,145208614187008,143974450721587200,575897802618175488])
def mn991 : Nat := mn856 - (memoNat [1154117772251234305,144115190225375230,9007199397347324,9006924393611256])
def mn992 : Nat := mn889 + ((memoNat [1127033744687105,4571838139068350,285735584403460,272129128406784]) * 2 ^ 10)
def mn993 : Nat := mn951 + ((memoNat [17293857736259796991,996432443357,62277023740,261993005172]) * 2 ^ 16)
def mn994 : Nat := mn902 + (memoNat [36065080937317374,70439678109696,4539784761344,287385951221587968,16])
def mn995 : Nat := mn944 + ((memoNat [17293857753473744895,2130303842365,133143986176,532575944952]) * 2 ^ 15)
def mn996 : Nat := mn957 - (memoNat [36282843529186,72055397164388350,4503599631695868,18577073593384952])
def mn997 : Nat := mn691 + (memoNat [2305878193653940226,144115192372924416,4503737074712576,9007199271518208])
def mn998 : Nat := mn539 - (memoNat [1073741825,67584,0,281474976710664])
def mn999 : Nat := mn957 + (memoNat [1152921538966617088,2253930186670016,13835198792770519044,266288234503])
def mn1000 : Nat := mn960 + (memoNat [2305844178518604833,4507929092882370,13835339530259005448,541166403599])
def mn1001 : Nat := mn812 + (memoNat [2343033990057820162,4398046642176,4539918974980,549755822096,16])
def mn1002 : Nat := Nat.xor mn812 (memoNat [6917529027641081859,13194139731968,12,282024732524592])
def mn1003 : Nat := mn950 + (memoNat [1152921470247075839,69805796308676608,4362862139015168,26177172842217472])
def mn1004 : Nat := mn856 + (memoNat [1152921505680588801,65538,4,274877906952])
def mn1005 : Nat := mn856 - (memoNat [17331013548873089024,2045,4539918974972,281200098811896,16])
def mn1006 : Nat := mn903 + ((memoNat [1,68788682750,4,281200098803712]) * 2 ^ 10)
def mn1007 : Nat := mn908 + (memoNat [37190982991609921,4398046644228,4539918974984,549755822096,16])
def mn1008 : Nat := Nat.xor mn908 (memoNat [6442451136,13194139729932,8,282024732524592])
def mn1009 : Nat := mn933 - (2 ^ 80 + 2 ^ 240)
def mn1010 : Nat := mn614 + (memoNat [72567700324352,18298125286006325244,9280144426401783,17575006191632,1023])
def mn1011 : Nat := mn631 + (memoNat [36318244504576,2305913377957871678,4644607698665728,17583596118280,512])
def mn1012 : Nat := memoNat [4093338425897862707,8258802478258429027,12050171019515341386,5383381429316121516,10040]
def mn1013 : Nat := mn1012 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn1014 : Nat := memoNat [4163144256631425619,5955138769743355111,2538573012876864206,14318523106662184109,10040]
def mn1015 : Nat := memoNat [5317226845550724660,8332966736438863079,2687191800718498510,14021285531532555437,10040]
def mn1016 : Nat := mn1014 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn1017 : Nat := mn1015 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn1018 : Nat := mn1014 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn1019 : Nat := Nat.xor mn1018 ((memoNat [246298356745219,2267742930958,992137446300,335007449864]) * 2 ^ 15)
def mn1020 : Nat := mn589 + ((memoNat [1023,65534]) * 2 ^ 155)
def mn1021 : Nat := Nat.xor mn577 ((memoNat [100664327,2283244879872,140750374174728,274877906960]) * 2 ^ 25)
def mn1022 : Nat := mn784 + (memoNat [37154697999548418,2251799883026432,4755801206503370752,562949953683456])
def mn1023 : Nat := Nat.xor mn660 (memoNat [3145824,83773739761858,30064771072,576460760893358080])
def mn1024 : Nat := Nat.xor mn827 (1 + 2 ^ 60 + 2 ^ 80 + 2 ^ 185 + 2 ^ 195 + 2 ^ 220 + 2 ^ 230)
def mn1025 : Nat := Nat.xor mn813 ((memoNat [100670465,70452965801984,985171008552972,274877906960]) * 2 ^ 25)
def mn1026 : Nat := mn985 + (memoNat [37154731286593537,2251799882960896,140741917536256,562949953683456])
def mn1027 : Nat := mn985 + (memoNat [33285962721,16143152795659341758,13691083604694654975,562941095313407])
def mn1028 : Nat := mn818 + (memoNat [2269850495037210626,4395899158462,13690947398401130500,540897452047,16])
def mn1029 : Nat := Nat.xor mn1012 ((memoNat [65543,144115259010383872,288231338232775552,268435456]) * 2 ^ 35)
def mn1030 : Nat := mn1019 + (memoNat [1133871366145,2251799880927232,140737488482304,562949953683456])
def mn1031 : Nat := memoNat [5281198047456971348,8333111942974907557,16522249851705694926,14597746275246044332,10040]
def mn1032 : Nat := mn1031 + ((memoNat [35185376625665,4611688080011751422,128849019000,541165879536]) * 2 ^ 15)
def mn1033 : Nat := mn1032 - (memoNat [37154698000630816,2305843077933170754,4755801210932432896,8858370048])
def mn1034 : Nat := mn985 + (memoNat [1227302367857213472,2199023255554,9079837814788,274877923336,32])
def mn1035 : Nat := Nat.xor mn1032 (memoNat [7730941231111,2251799883364352,985162419412992,1970324837236736])
def mn1036 : Nat := memoNat [4200298920238729811,5880756805909716265,7294369825762781770,4806920702514066349,10040]
def mn1037 : Nat := mn1036 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn1038 : Nat := mn1036 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn1039 : Nat := Nat.xor mn1038 ((memoNat [246298358844419,6803228268558,992137446300,335007449864]) * 2 ^ 15)
def mn1040 : Nat := mn1038 + (memoNat [2305915645766729730,148618792136675264,9288536801148928,9279878155730944])
def mn1041 : Nat := Nat.xor mn646 ((memoNat [1,2306335593040263168,28672,26388279123968]) * 2 ^ 15)
def mn1042 : Nat := Nat.xor mn1040 (memoNat [1152921512130379777,65998,137438953472,9070970929160])
def mn1043 : Nat := mn962 + (memoNat [1168231170080,4505798789040128,281474976841732,281474977234944])
def mn1044 : Nat := mn1038 + ((memoNat [34603521,1168231139361,4294967300,4294967304]) * 2 ^ 16)
def mn1045 : Nat := mn1040 - (memoNat [2233381978113,2251799885055936,281337538019328,272678884212736])
def mn1046 : Nat := mn815 + (memoNat [1154048504058871809,4395899156480,18442245009701994500,549747433487,16])
def mn1047 : Nat := mn911 + (memoNat [1127000525765664,72061923365093314,13835062590901977096,541165887503,16])
def mn1048 : Nat := mn1012 + (memoNat [2249566430691327,2303663779243554816,287948901443178496,287948901711347712])
def mn1049 : Nat := memoNat [3013565267373016626,10566824717299586279,2966414977875520206,14300508708949619885,10040]
def mn1050 : Nat := Nat.xor mn1018 (memoNat [33653793,16212958727335053312])
def mn1051 : Nat := mn1049 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn1052 : Nat := mn1049 + (memoNat [1124766035511359,2303736484588288000,143974450721595392,575897802618175488])
def mn1053 : Nat := mn584 + (memoNat [17257796038751747039,4503528896788413,13835339525959974784,281466378911743])
def mn1054 : Nat := mn542 + (memoNat [1188985487139799073,2199023321090,4616198560453754884,274877906944,32])
def mn1055 : Nat := mn542 + (memoNat [33553408,18374688607827982272,8938099834883,266279583744,32])
def mn1056 : Nat := Nat.xor mn923 (memoNat [1024,2267742797888,13835058055282163712,283467841545])
def mn1057 : Nat := mn987 + (memoNat [36064015785426945,2251799882960896,140741787516928,562949953683456])
def mn1058 : Nat := Nat.xor mn936 (memoNat [3221226592,68732059718,13835058055282163712,54043204118380545])
def mn1059 : Nat := mn1029 + (memoNat [17332067982638089247,2305843077933168705,4895412799510941696,9118416896])
def mn1060 : Nat := mn1014 + ((memoNat [100663297,139586437120,12884901900,24]) * 2 ^ 25)
def mn1061 : Nat := Nat.xor mn1049 ((memoNat [1161118638670849,12,30786325606400,51539615744]) * 2 ^ 20)
def mn1062 : Nat := mn1059 + ((memoNat [68650270719,2305983611477686142,8787503095800,8787503103984]) * 2 ^ 15)
def mn1063 : Nat := mn786 + (memoNat [74380898615690241,70368744179776,9520750487188537472,8796093039120,1024])
def mn1064 : Nat := mn1063 - (memoNat [1188985487106245665,72057664904890434,4616189622353920000,8598323200])
def mn1065 : Nat := memoNat [3048468131166637682,5880902012441564457,7433981414341290570,5365367056568054701,10040]
def mn1066 : Nat := mn1044 - (memoNat [66592,2305843077939462144,8192,27021597764222976])
def mn1067 : Nat := mn1065 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn1068 : Nat := Nat.xor mn1039 (memoNat [33653793,16212958727335053312,8192])
def mn1069 : Nat := mn1038 + (memoNat [17294913284637459487,145206531848191,139611588578508800,558446354053988352])
def mn1070 : Nat := Nat.xor mn1069 ((memoNat [35185683860483,6803228407822,167503724700,335007449352]) * 2 ^ 15)
def mn1071 : Nat := Nat.xor mn705 (memoNat [8070450532281483271,72057596187523072,29360128,9007199279906816])
def mn1072 : Nat := Nat.xor mn815 (memoNat [1073749024,481036337602,4611686018427387904,60129542144])
def mn1073 : Nat := mn1067 + (memoNat [2267742765057,2310346608912435200,281474976972800,281474977234944])
def mn1074 : Nat := mn1069 + (memoNat [2305913412384751617,146366992186607616,9007199263129600,9007199271518208])
def mn1075 : Nat := mn1048 + (memoNat [2377971008538708033,74309535587567748,9232379244707840000,8725741474676736])
def mn1076 : Nat := mn1075 - (memoNat [1133871398913,2251799882958848,140737488486400,281474976972800])
def mn1077 : Nat := Nat.xor mn1050 ((memoNat [1025,2214592706]) * 2 ^ 25)
def mn1078 : Nat := mn1049 + (memoNat [2305911144608399361,69805798382831616,8725724286156800,8725724294283264])
def mn1079 : Nat := mn1035 + (memoNat [37151330746236928,18442240473941672002,4755378998466977791,8857583616])
def mn1080 : Nat := mn1060 + (memoNat [2305910010737032159,67553927699953664,8584986797670400,8162774340599808])
def mn1081 : Nat := mn1063 - ((memoNat [51380737,1168231107648,6442450950,12]) * 2 ^ 16)
def mn1082 : Nat := Nat.xor mn1063 ((memoNat [246298323189761,68719554946,987842479000,283467842320]) * 2 ^ 15)
def mn1083 : Nat := mn594 + ((memoNat [17592689885695,1031865922527,144115252502462522,270717157492]) * 2 ^ 16)
def mn1084 : Nat := mn593 + (memoNat [1080895759930259392,65302059032706940,9227453415430815616,17732906360242431])
def mn1085 : Nat := mn788 + (memoNat [36029931964104706,2251799883026432,4611826755915874304,562949953683456])
def mn1086 : Nat := Nat.xor mn788 (memoNat [3148838,68719882434,30064771072,1688858450198528])
def mn1087 : Nat := mn816 - ((memoNat [1048577,2251868533164096,4294967296,8]) * 2 ^ 15)
def mn1088 : Nat := mn816 - (memoNat [36029966324925472,4503668485259330,4611967497699196932,8590458880])
def mn1089 : Nat := mn816 + (memoNat [2341872906819077154,4466766118978,4611686022722486276,558345748496])
def mn1090 : Nat := Nat.xor mn816 (memoNat [6917529062000852998,2264994035400704,140737488355332,549756600368])
def mn1091 : Nat := mn987 + (memoNat [2341941075499810818,72057598265792512,8866466069610496,9288674247966720])
def mn1092 : Nat := mn1091 - (memoNat [36029931965154336,2251868602368066,4611826760210841600,8590196736])
def mn1093 : Nat := Nat.xor mn1032 (memoNat [1126999418470400,14680064,144255925698560000,269221888])
def mn1094 : Nat := mn1093 - (memoNat [36029931965154336,2251868602368066,4611826760210841600,8590196736])
def mn1095 : Nat := mn1016 + ((memoNat [103080263681,140806207832064,13194139545600,24576]) * 2 ^ 15)
def mn1096 : Nat := mn1080 + (memoNat [18410715275615797250,135101,13835058050987196416,562941363486719])
def mn1097 : Nat := mn1029 + (memoNat [40529030466765855,6913098066509625410,5187724563097198592,287948910837891072])
def mn1098 : Nat := mn1097 - (memoNat [36029931965154336,2251868602368066,4611826760210841600,8590196736])
def mn1099 : Nat := mn1019 + ((memoNat [68685922305,2305913380172529602,8791798063100,8804682973176]) * 2 ^ 15)
def mn1100 : Nat := mn1063 - (memoNat [17329818416207397919,2251866524022849,4607463898067763200,8725732860100608])
def mn1101 : Nat := mn1065 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn1102 : Nat := Nat.xor mn1039 (memoNat [34359837729,16143152939486152704,8192])
def mn1103 : Nat := mn1067 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn1104 : Nat := mn1040 - (memoNat [2233382011940,2308094877818429376,281337538027520,1117103814344704])
def mn1105 : Nat := mn1069 + (memoNat [1152955589467308031,2082338816,4362862143078400,17451448564187136])
def mn1106 : Nat := mn1039 + (memoNat [1124800395215902,145208614187008,143974450721587200,575897802618175488])
def mn1107 : Nat := mn759 + (memoNat [1133871431681,4503599765850112,140737488617600,281474977234944])
def mn1108 : Nat := mn924 + (memoNat [34084860461055,72057598265720832,8866461770448896,8444249317834752])
def mn1109 : Nat := mn1103 + (memoNat [2267742765057,2310346608912435200,281474976972800,281474977234944])
def mn1110 : Nat := mn1069 + ((memoNat [17592740741633,1168231138367,70866960450,270582939780]) * 2 ^ 16)
def mn1111 : Nat := mn1018 + (memoNat [72059898323599360,78740427926208644,9223657918468194436,8926415953605427456])
def mn1112 : Nat := mn665 + (memoNat [73256132580212736,2145386560,9376776036601036928,18437745670547849744,1023])
def mn1113 : Nat := mn1111 - (memoNat [1152956689012490241,72057596187510784,4503599631564800,9007199263129600])
def mn1114 : Nat := memoNat [3083371098106579538,8263161008784512363,11901561044946594642,4788906312586130861,10041]
def mn1115 : Nat := memoNat [4235199619469495922,6024944632615703915,11761667981391117138,5094869612010042797,10041]
def mn1116 : Nat := mn1114 + (memoNat [1152955555141124095,69805794226206720,4362862143078400,17451448564187136])
def mn1117 : Nat := mn1114 + (memoNat [1124766035511359,2303736484588288000,143974450721595392,575897802618175488])
def mn1118 : Nat := mn707 + (memoNat [1048576,16140901064495857728,137304735871,8795824586752])
def mn1119 : Nat := mn801 - ((memoNat [70369817921535,4329327097852,137438953724,257698038264]) * 2 ^ 15)
def mn1120 : Nat := Nat.xor mn725 ((memoNat [3848290697219,32,12884901952]) * 2 ^ 86)
def mn1121 : Nat := mn926 + ((memoNat [1125934266580993,66571993088,13835058192586899456,255]) * 2 ^ 30)
def mn1122 : Nat := mn856 - (memoNat [1152956653578977280,141863390342414334,8866461770579964,8443974439927800])
def mn1123 : Nat := mn944 - (memoNat [2249532070921248,6913098064427155456,432064089519034368,269934503470301184])
def mn1124 : Nat := mn1059 + ((memoNat [1161117564929025,0,4260607561600,7936]) * 2 ^ 20)
def mn1125 : Nat := mn1111 - (memoNat [34359737312,2179163257569280,4398046511236,8926134461448323328])
def mn1126 : Nat := mn1114 - (memoNat [34359703488,2106524553969664,4398046507140,8628896886041870592])
def mn1127 : Nat := mn1012 + (memoNat [108086394281265216,139586437318,13835058068167065600,25769803776])
def mn1128 : Nat := Nat.xor mn1065 ((memoNat [206158430209,2199023255552,4398046511232,48]) * 2 ^ 50)
def mn1129 : Nat := Nat.xor mn1114 (memoNat [6803228203200,13946619951120384,844424930942976,630785422810152960])
def mn1130 : Nat := Nat.xor mn1111 (memoNat [1133871373537,2760255222450176,140737488515072,875387177571975168])
def mn1131 : Nat := Nat.xor mn1117 ((memoNat [240518168577,2199023269888,4398046511232,48]) * 2 ^ 50)
def mn1132 : Nat := mn1114 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn1133 : Nat := mn1114 + (memoNat [2308164043967299584,4753549408836911104,297096838194790400,8444249854705664])
def mn1134 : Nat := mn1114 + (memoNat [2249532070921248,4607255055217655808,287948901443178496,287948901711347712])
def mn1135 : Nat := Nat.xor mn1134 ((memoNat [35185688052739,2680059664398,167503724700,335007449352]) * 2 ^ 15)
def mn1136 : Nat := Nat.xor mn649 (memoNat [230624,2305929252626759680,939552768,864691130334183424])
def mn1137 : Nat := Nat.xor mn649 (memoNat [198848,2305997360018227200,939548672,639511148965658624])
def mn1138 : Nat := memoNat [5317154243458189908,13018962217435243819,2677907395952978642,4788897517046739869,9017]
def mn1139 : Nat := mn953 + (memoNat [110411858219892768,2201172836352,13619618512896,9007199254765568,48])
def mn1140 : Nat := mn1139 - (memoNat [33824,72638703599616,4096,297237575406452736])
def mn1141 : Nat := mn877 - (memoNat [33824,16140973701049876480,18302628885633699839,288230375883276287])
def mn1142 : Nat := Nat.xor mn865 ((memoNat [240518168577,2199023267840,26388279067392,56]) * 2 ^ 50)
def mn1143 : Nat := Nat.xor mn900 (memoNat [36029896531640320,14680064,4565550366720,63050394783195136,16])
def mn1144 : Nat := mn1078 + (memoNat [2233383027745,2251868671641600,281474976972800,281474977234944])
def mn1145 : Nat := mn1144 - (memoNat [33824,72638703599616,4096,297237575406452736])
def mn1146 : Nat := memoNat [5355507409064905300,8258657411304629545,7587103801814493770,4788906304549843885,10040]
def mn1147 : Nat := mn1139 - (memoNat [17293824835771727872,4503599696578557,281474976972796,281200099327992])
def mn1148 : Nat := Nat.xor mn1132 ((memoNat [3,6597069772800,13194139533696,28]) * 2 ^ 51)
def mn1149 : Nat := mn1133 - (2 ^ 245)
def mn1150 : Nat := mn1111 + (memoNat [2305911110282248192,139611588448354304,8725724286156800,17451448572313600])
def mn1151 : Nat := mn1132 + ((memoNat [35185445831681,2199023257726,137438953600,541165879552]) * 2 ^ 15)
def mn1152 : Nat := mn1111 + (memoNat [2305909976410849279,137359788565395456,8584986797670400,17169973595340800])
def mn1153 : Nat := mn1151 - (memoNat [1133871398913,2251799882958848,140737488486400,281474976972800])
def mn1154 : Nat := mn1131 + (memoNat [1154079187305168897,2371145203672156160,148196575376179200,276037632])
def mn1155 : Nat := mn1117 + (memoNat [2305911110282215425,139611590526699520,8725724286156800,8725724294283264])
def mn1156 : Nat := mn651 + (memoNat [1048576,18444492273893769280,137438822527,8796092760064])
def mn1157 : Nat := mn1156 - ((memoNat [34394341377,70437463656512,4402341482500,8200]) * 2 ^ 15)
def mn1158 : Nat := Nat.xor mn801 (memoNat [1133871366151,15762598698366976,140737489272832,1970324837236736])
def mn1159 : Nat := mn606 + (memoNat [68191264,2452210065753505858,8800253649032,8321236992,1])
def mn1160 : Nat := mn979 + ((memoNat [35433480193,66571993088,13835058192586899456,255]) * 2 ^ 30)
def mn1161 : Nat := mn969 + ((memoNat [33554431,18446741874686291968,4611677222334365439]) * 2 ^ 50)
def mn1162 : Nat := mn994 + (memoNat [33826,16140973703197497344,18302628885633699839,289074800813408255])
def mn1163 : Nat := Nat.xor mn890 (memoNat [34359842848,2676628129841152,140737488379904,576460752304209920])
def mn1164 : Nat := mn1093 + ((memoNat [1161117564929025,0,4260607561600,7936]) * 2 ^ 20)
def mn1165 : Nat := mn1093 + (memoNat [33775864408670208,16138649264612966466,4323314908813721599,8052801536])
def mn1166 : Nat := mn1013 + (memoNat [108086394281297984,137506062534,13835058068167065600,25769803776])
def mn1167 : Nat := mn1166 - ((memoNat [34394341377,70437463656512,4402341482500,8200]) * 2 ^ 15)
def mn1168 : Nat := mn1129 + (memoNat [1152955555141124096,69805794224242688,4362862143078400,8126464])
def mn1169 : Nat := mn1168 - ((memoNat [34394341377,70437463656512,4402341482500,8200]) * 2 ^ 15)
def mn1170 : Nat := mn1155 + (memoNat [1133871398913,2251799883024384,140737488486400,562949953683456])
def mn1171 : Nat := Nat.xor mn1132 (memoNat [1133871470784,2687625378922496,140737488510976,576460752304209920])
def mn1172 : Nat := Nat.xor mn1135 (memoNat [6803228295171,13510801233090560,844424930918400,63331869760421888])
def mn1173 : Nat := mn1148 + (memoNat [33822,72636555915264,4096,296393150476320768])
def mn1174 : Nat := mn1139 + (memoNat [2305877060820664320,69805794226272194,4362724704124804,17442927349071880])
def mn1175 : Nat := mn1133 + (memoNat [1152956689011441664,72057594042056640,4503462192611200,17724127448137728])
def mn1176 : Nat := Nat.xor mn775 (memoNat [32775,15762598765475840,917504,1970324837236736])
def mn1177 : Nat := Nat.xor mn775 (memoNat [3110,15975979116015616,921600,289919226012237824])
def mn1178 : Nat := mn1175 - (memoNat [74382032486006784,0,9520891087237939200,16912,1024])
def mn1179 : Nat := mn970 + (memoNat [1168231170081,4505798789105664,281474976841728,281474977234944])
def mn1180 : Nat := mn1179 - (memoNat [33825,72638701570048,4096,288511851128422400])
def mn1181 : Nat := Nat.xor mn903 (memoNat [36063981425655808,2048,4565554429952,281474976718848,16])
def mn1182 : Nat := Nat.xor mn1095 (memoNat [7696581394439,69679104,985162419404800,1970324837236736])
def mn1183 : Nat := Nat.xor mn1095 (memoNat [7696581495910,72780370817024,985162419417088,289919226012237824])
def mn1184 : Nat := mn1175 - ((memoNat [550292685841,37454329413632,140806207961152,274877776000]) * 2 ^ 26)
def mn1185 : Nat := mn1135 + ((memoNat [1,2176,0,824633720832]) * 2 ^ 15)
def mn1186 : Nat := mn1135 - (memoNat [1057,72638630266880,4096,261490253364199424])
def mn1187 : Nat := mn1133 - (2 ^ 80 + 2 ^ 240)
def mn1188 : Nat := mn1168 + (memoNat [3378833591927841,6919853466158303232,432486302118711296,278941702725828608])
def mn1189 : Nat := mn1131 + (memoNat [3376565849162785,6915349864312211456,432204827141738496,270215978447273984])
def mn1190 : Nat := mn1168 + (memoNat [3377699720528928,6917601666275344384,432345564630224896,278660227748855808])
def mn1191 : Nat := mn1131 + (memoNat [3375431977763872,6913098064429252608,432064089653252096,269934503470301184])
def mn1192 : Nat := mn710 + (memoNat [1016832,18444562642572935232,137438822527,8796092760064])
def mn1193 : Nat := mn711 + (memoNat [2066433,18444633011317180544,274877776127,299067162492928])
def mn1194 : Nat := mn1192 + (memoNat [2099200,140737488355456,274877907200,17592186044416])
def mn1195 : Nat := Nat.xor mn730 (memoNat [229377,15762599178602496,917504,65020719620423680])
def mn1196 : Nat := Nat.xor mn729 ((memoNat [1,68719478848,4,1649267441688]) * 2 ^ 15)
def mn1197 : Nat := Nat.xor mn929 (memoNat [35433512992,2253998904049666,140737488355340,274878693384])
def mn1198 : Nat := mn929 + (memoNat [1152957791745343585,72064193257408518,4503599631695884,824642109464])
def mn1199 : Nat := Nat.xor mn929 (memoNat [41875964128,2267193043976206,140737488355348,824634507320])
def mn1200 : Nat := mn995 + (memoNat [36318277042177,2251799882960896,140737492680704,562949953683456])
def mn1201 : Nat := Nat.xor mn944 ((memoNat [1048577,68719478848,4294967296,1649267441688]) * 2 ^ 15)
def mn1202 : Nat := mn1097 + (memoNat [17329816182824371232,66571993153,4607182423090790400,8581545984])
def mn1203 : Nat := mn1063 + (memoNat [72056496675883073,137371912324,9223231307956224000,281492156317696])
def mn1204 : Nat := mn1097 + (memoNat [17401873779011882080,204010946757,13830554468535500800,25761415168])
def mn1205 : Nat := mn1048 + (memoNat [108086394281266273,206160529606,13835058068167065600,25769803776])
def mn1206 : Nat := mn1205 - (memoNat [1152957822883889153,74309396068304896,4644337120051200,8650752])
def mn1207 : Nat := mn1129 + ((memoNat [32735,71987225360793600,143974450591690752]) * 2 ^ 35)
def mn1208 : Nat := mn1168 + (memoNat [3378833591926785,6919780829671458816,432486302118707200,805568512])
def mn1209 : Nat := mn1207 + (2 ^ 51 + 2 ^ 126 + 2 ^ 156 + 2 ^ 186 + 2 ^ 221)
def mn1210 : Nat := mn1111 + ((memoNat [34290532351,70231305156606,4389456580600,266287980528]) * 2 ^ 15)
def mn1211 : Nat := mn1115 + ((memoNat [18446708991308332031,208838489733119,13052405624700,24312]) * 2 ^ 15)
def mn1212 : Nat := Nat.xor mn711 (memoNat [8070450532482809857,504403160412981248,29360128,9007199279906816])
def mn1213 : Nat := Nat.xor mn711 (memoNat [8070450532482809856,504403160427724800,29360128,54324670530322432])
def mn1214 : Nat := mn730 + (memoNat [1152921504640401408,72057596187443200,4194304,8725724286418944])
def mn1215 : Nat := Nat.xor mn730 (memoNat [8070450532482809859,504403160413116416,29360128,562949978587136])
def mn1216 : Nat := mn519 + (memoNat [37191015170312193,140737488420992,4760445681057923328,17592186052864,512])
def mn1217 : Nat := mn877 + (memoNat [1124766035477503,4609504658222608384,288089638797447168,278378752503447552])
def mn1218 : Nat := Nat.xor mn933 (memoNat [37154696926855168,65536,4565684453376,63331869759905792,16])
def mn1219 : Nat := Nat.xor mn933 (memoNat [37154696926855171,2234368,4565684453376,54606145481875456,16])
def mn1220 : Nat := mn823 + (memoNat [2307005193037807618,4398046642176,4535624007684,549755822096,16])
def mn1221 : Nat := Nat.xor mn1063 ((memoNat [1133630848204807,15393162788864,13194139534208,1544]) * 2 ^ 45)
def mn1222 : Nat := mn1039 + (memoNat [1125899906843679,145208681363456,144115188210073600,567172078340407296])
def mn1223 : Nat := mn1039 + (memoNat [1125899906843678,145208679198720,144115188210073600,557883404108955648])
def mn1224 : Nat := mn1155 + (memoNat [2267742765057,4503599698741248,281474976972800,281474977234944])
def mn1225 : Nat := Nat.xor mn1155 ((memoNat [207618049,412316862528,25769803800,1924145348624]) * 2 ^ 15)
def mn1226 : Nat := mn1133 + (memoNat [1056,72636486844416,4096,278941701920260096])
def mn1227 : Nat := mn1226 - (memoNat [1,2164736,0,9288674231451648])
def mn1228 : Nat := mn777 + (memoNat [2305914511897461761,148689160880719936,9148074190700672,8734520388354048])
def mn1229 : Nat := mn711 + ((memoNat [70369783318527,4329327163390,133143986428,266287972856]) * 2 ^ 15)
def mn1230 : Nat := mn613 + (memoNat [1133940607008,4758053075036405890,149537876353160,8589934592,1])
def mn1231 : Nat := mn739 + ((memoNat [35184372089855,2130303842302,124,541165879544]) * 2 ^ 15)
def mn1232 : Nat := mn929 + (memoNat [1152993008363274273,218426787464546306,13651536378986500,8725999181365256])
def mn1233 : Nat := mn929 + (memoNat [1152991874491875360,216174987581587458,13510798890500100,8444524204392456])
def mn1234 : Nat := mn957 + (memoNat [1152921505680588832,2199023257602,4,281749854617608])
def mn1235 : Nat := mn1200 + ((memoNat [70369816871935,4329327163326,270582939776,266287972856]) * 2 ^ 15)
def mn1236 : Nat := mn596 + ((memoNat [33825,68719480832,4677223714824,274877907456]) * 2 ^ 35)
def mn1237 : Nat := mn1063 + ((memoNat [70370857059327,2130303907838,270582939900,266287972856]) * 2 ^ 15)
def mn1238 : Nat := mn1075 + (memoNat [36028798093755425,68719544386,4611686022722355200,281483566645248])
def mn1239 : Nat := mn1075 + (memoNat [36027664222356512,18444492342546137154,4611545285233868799,8589672448])
def mn1240 : Nat := mn652 + (memoNat [36065116338258944,70368744177792,4616330630421020928,17592186052872,512])
def mn1241 : Nat := mn1240 - (memoNat [1133871398913,2251799882958848,140737488486400,281474976972800])
def mn1242 : Nat := mn775 + (memoNat [37189882373768192,70368811286656,4760305081008521472,17592186052872,512])
def mn1243 : Nat := mn1111 + ((memoNat [70405147592703,74560632256444,4660039520500,532575953384]) * 2 ^ 15)
def mn1244 : Nat := mn711 + (memoNat [37155831873013761,140737488357504,4755942218869506304,17592186052872,512])
def mn1245 : Nat := mn1048 + (memoNat [144115226768347264,4685995687156777224,8813272899848,18446181158115869185])
def mn1246 : Nat := mn1171 + (memoNat [3378833591927840,6919853466160463872,432486302118711296,288230376957280256])
def mn1247 : Nat := Nat.xor mn1245 ((memoNat [246298155424769,15461882333186,966367642500,283467842328]) * 2 ^ 15)
def mn1248 : Nat := mn700 + ((memoNat [52777597273599,3229815502846,133143986364,403726926200]) * 2 ^ 16)
def mn1249 : Nat := mn729 + ((memoNat [52777631876607,3229815502846,137438953660,403726926200]) * 2 ^ 16)
def mn1250 : Nat := mn960 + (memoNat [1227301268345585696,2199023253506,9079837687812,18446462873610764296,31])
def mn1251 : Nat := mn944 + ((memoNat [52777630827519,3229815502846,201863463040,403726926200]) * 2 ^ 16)
def mn1252 : Nat := mn1052 + ((memoNat [52778134143999,2130303875070,201863463100,403726926200]) * 2 ^ 16)
def mn1253 : Nat := mn1205 + (memoNat [2305911144608399359,69805798380664832,8725724286156800,8444249317572608])
def mn1254 : Nat := mn1240 - (memoNat [2267742797826,4503599765917696,281474976972800,562949953945600])
def mn1255 : Nat := mn1226 + ((memoNat [35185342022655,1992864888768,124554051700,824633721064]) * 2 ^ 15)
def mn1256 : Nat := mn1245 - (memoNat [1133871398913,2251799882958848,140737488486400,281474976972800])
def mn1257 : Nat := mn1148 + (memoNat [1123632164113502,2301557323341885440,143833713233113088,873135378024366080])
def mn1258 : Nat := mn650 + (memoNat [2251799814767648,6917601666342584384,288230513993322624,288239173050040320])
def mn1259 : Nat := mn700 + (memoNat [1152922638511800322,74309396066340864,140737492680704,562949962072064])
def mn1260 : Nat := mn680 + (memoNat [1049600,70368746274880,137438953600,9015995347763200])
def mn1261 : Nat := mn729 + ((memoNat [571473921,68719478849,73014444036,141733920776]) * 2 ^ 16)
def mn1262 : Nat := mn815 + (memoNat [1188950370379958273,4688247349531639936,9223380837242773764,17179869696,1])
def mn1263 : Nat := Nat.xor mn929 (memoNat [6804302135328,85570598788466690,5348024558288908,54324945393025032])
def mn1264 : Nat := mn995 + (memoNat [1152994175520702466,6755399646711808,422212473716736,844424930918400])
def mn1265 : Nat := mn944 + (memoNat [1152958956755288065,4503599765848064,281474981167104,9288674231975936])
def mn1266 : Nat := mn593 + ((memoNat [16913,34359740416,2338611857412,137438953728]) * 2 ^ 36)
def mn1267 : Nat := mn1052 + (memoNat [1152957822850334722,2251802028412928,4644337120051200,562949962072064])
def mn1268 : Nat := mn1205 + ((memoNat [68158465,2267742736450,8589934600,8589934608]) * 2 ^ 15)
def mn1269 : Nat := mn1069 + ((memoNat [34603521,1168231106625,4294967300,141733920776]) * 2 ^ 16)
def mn1270 : Nat := mn1155 + (memoNat [3401614163970,6755399579668480,422212465459200,844424930918400])
def mn1271 : Nat := mn1111 + (memoNat [33824,72634404438016,4096,279223176896970752])
def mn1272 : Nat := mn1111 + ((memoNat [34359738369,2199023257600,4398046511232,8]) * 2 ^ 50)
def mn1273 : Nat := mn1134 + ((memoNat [34603009,68719511617,4294967300,141733920776]) * 2 ^ 16)
def mn1274 : Nat := Nat.xor mn1245 ((memoNat [3,0,425201762304]) * 2 ^ 81)
def mn1275 : Nat := mn1245 - ((memoNat [35185411228671,2130303842302,133143986300,266287972600]) * 2 ^ 15)
def mn1276 : Nat := mn711 - ((memoNat [35186484970495,2130303842428,270582939772,807453851896]) * 2 ^ 15)
def mn1277 : Nat := mn907 + (memoNat [74311593950707744,2199021223938,9079829561348,18437737149332733960,31])
def mn1278 : Nat := mn1063 - ((memoNat [35185411229695,4329327097980,133143986300,807453851896]) * 2 ^ 15)
def mn1279 : Nat := Nat.xor mn1207 ((memoNat [121110531,240518207521,15032385550,966367641620]) * 2 ^ 16)
def mn1280 : Nat := mn1245 - (memoNat [1152956689012490241,72057596187379712,4503599631564800,26458647819190272])
def mn1281 : Nat := mn775 + (memoNat [1133871399937,4573968442918912,140737488617472,281474977234944])
def mn1282 : Nat := mn639 + (memoNat [1133871367170,2308165177773789184,140737622704128,562950222118912])
def mn1283 : Nat := mn801 + (memoNat [1125899906875394,2251799883026432,144115188075986944,562949953683456])
def mn1284 : Nat := mn616 + (memoNat [1081376,2269957324864,137438957696,288239172244733952])
def mn1285 : Nat := mn980 + (memoNat [1168231137312,4505798721931264,281474976841728,281474977234944])
def mn1286 : Nat := Nat.xor mn969 (memoNat [5634997196801,9429828541427712,562949954101248,578149602164736000])
def mn1287 : Nat := mn856 + (memoNat [1154047439947202562,2251799883026434,140737622573060,563224831590408])
def mn1288 : Nat := mn852 + (memoNat [1152921505680622593,70439678312450,4100,288230651029618696])
def mn1289 : Nat := mn1095 + (memoNat [2233383027745,2251868604532736,281474976976896,281474977234944])
def mn1290 : Nat := mn1011 + ((memoNat [33555457,72569982025728,140741783453700,274877906952]) * 2 ^ 25)
def mn1291 : Nat := mn1103 + (memoNat [3367254425603,4616189618195470336,422212465463296,844424930918400])
def mn1292 : Nat := mn1011 + ((memoNat [1161118638670849,69208128,4398046515200,274877915136]) * 2 ^ 20)
def mn1293 : Nat := mn1111 - (memoNat [33824,72638699405312,4096,279223176896970752])
def mn1294 : Nat := mn1132 + (memoNat [2267742798881,4576236252760064,281474976976896,288511851128946688])
def mn1295 : Nat := mn1151 + (1 + 2 ^ 50 + 2 ^ 75 + 2 ^ 80 + 2 ^ 125 + 2 ^ 155 + 2 ^ 185 + 2 ^ 220 + 2 ^ 240)
def mn1296 : Nat := mn1151 + (memoNat [1133871367200,2324438450176000,140737488490496,288230376151973888])
def mn1297 : Nat := memoNat [6468985032563836501,6173420415094205739,2538295807106034386,4815919114014045085,9017]
def mn1298 : Nat := mn890 + (memoNat [2267742765025,16145402465171343360,18302910360610668543,281474708799487])
def mn1299 : Nat := mn1011 + (memoNat [34902898186877920,16140900995776380994,4467570834512277503,8321499136])
def mn1300 : Nat := mn1294 - (memoNat [1125899906876448,2305915647915196416,144115188210077696,288230376420147200])
def mn1301 : Nat := mn1151 - ((memoNat [34325135361,70300024702912,4393751547900,8184]) * 2 ^ 15)
def mn1302 : Nat := mn759 + (memoNat [2267743847427,4503599835191360,281474977104128,844424930918656])
def mn1303 : Nat := mn564 + ((memoNat [1025,2308167447661772800,138412032,281475245146112]) * 2 ^ 15)
def mn1304 : Nat := mn789 + (memoNat [1133870349252,2251662513414076,140728898682880,1125882727497984])
def mn1305 : Nat := mn924 + (memoNat [35185479385120,72057598334996482,9011597305446404,9007199271518208])
def mn1306 : Nat := mn1091 + (memoNat [36029931998707745,2251799952164866,285877318320128,281474977234944])
def mn1307 : Nat := mn846 + ((memoNat [34636799,68169725112320,4648602156535680,281474977234432]) * 2 ^ 25)
def mn1308 : Nat := mn1292 - ((memoNat [1161117564929025,0,4260607561600,7936]) * 2 ^ 21)
def mn1309 : Nat := mn1069 + (memoNat [2233858049546713026,76561060659793788,9232660702504943616,9288657068883967])
def mn1310 : Nat := mn1075 - (memoNat [36027732941898784,2251868463956034,4611545285233868800,8589672448])
def mn1311 : Nat := mn997 + (memoNat [37191015170342913,2251799882960896,140874927308800,562949953691648])
def mn1312 : Nat := Nat.xor mn505 (memoNat [37191222436036608,0,5653007260457238528,9992,1552])
def mn1313 : Nat := mn505 + (memoNat [33555456,70368744177728,4402480021632,8796093022208,16])
def mn1314 : Nat := mn507 + (memoNat [33555456,70368744177728,4402480021632,8796093022208,16])
def mn1315 : Nat := mn808 + (memoNat [1152921538966618113,2380154602088628224,4224,9223372311732683016])
def mn1316 : Nat := mn808 + (memoNat [1162183790560256,68719476800,4611686156004884480,8589942784,16])
def mn1317 : Nat := mn855 + (memoNat [2306968910194278402,72057596189673474,4503599761588228,18014673395777544])
def mn1318 : Nat := mn994 + (memoNat [16140902230579511297,4503599698747387,281474976841720,1125350151553008])
def mn1319 : Nat := mn908 + (memoNat [35219839156257,2253998906281986,140737492549636,563224831590408])
def mn1320 : Nat := mn1265 - (memoNat [2147483712,18302633279385366532,18437736874454810631,549739036687])
def mn1321 : Nat := mn957 - (memoNat [37190980844126209,63488,4539918974976,18446462598732849152,15])
def mn1322 : Nat := mn1320 + (memoNat [34050534244352,69805796306712576,4362862143078400,17451448564187136])
def mn1323 : Nat := mn1312 - (memoNat [68652367872,0,9520882282277896192,512,992])
def mn1324 : Nat := mn1314 - (memoNat [16140901064495859646,136339441713275,248,17042430230528])
def mn1325 : Nat := mn565 + ((memoNat [1025,2308167447661772800,138412032,281475245146112]) * 2 ^ 15)
def mn1326 : Nat := Nat.xor mn1304 (memoNat [192,422624781926412,850403524608,17643725651968])
def mn1327 : Nat := mn617 + (memoNat [1125899907957824,2305917917872521280,144115325649035392,576469548664881152])
def mn1328 : Nat := mn1284 - (memoNat [2097152,13835058055282163840,274609471743,17591649173504])
def mn1329 : Nat := mn681 + (memoNat [1049600,70368746274880,137438953600,9015995347763200])
def mn1330 : Nat := mn681 + (memoNat [1190077336511315969,72057596185413632,4755941943995793408,8397064,512])
def mn1331 : Nat := mn745 + (memoNat [1133872448514,2322168627204160,140874927440000,571746046705664])
def mn1332 : Nat := mn730 + (memoNat [2305878193650792449,143974454888761216,4503324757851904,36011204849696768])
def mw2 : WireKey := (mn6,mn7,mn8,mn9,3)
def mw3 : WireKey := (mn10,mn11,mn12,mn13,3)
def mw4 : WireKey := (mn14,mn15,mn16,mn17,3)
def mw5 : WireKey := (mn18,mn19,mn20,mn21,3)
def mw6 : WireKey := (mn22,mn23,mn24,mn25,3)
def mw7 : WireKey := (mn26,mn27,mn28,mn29,3)
def memoOp (d : Bool) (x y : WireKey) : WireKey :=
  let (s,a,b,c,r) := x
  let (ss,aa,bb,cc,rr) := y
  let w := opW d ⟨s,a,b,c,r⟩ ⟨ss,aa,bb,cc,rr⟩
  (w.s,w.a,w.b,w.c,w.r)
def memoNot (x : WireKey) : WireKey :=
  let (s,a,b,c,r) := x
  (s ^^^ mz 0,b,a,c,0)
def mw231 : WireKey := memoNot mw2
def mw219 : WireKey := memoNot mw3
def mw208 : WireKey := memoNot mw4
def mw197 : WireKey := memoNot mw5
def mw252 : WireKey := memoNot mw6
def mw241 : WireKey := memoNot mw7
def mw8 : WireKey := memoOp false mw2 mw3
def mw9 : WireKey := memoOp true mw2 mw3
def mw10 : WireKey := memoOp false mw2 mw4
def mw11 : WireKey := memoOp true mw2 mw4
def mw12 : WireKey := memoOp false mw2 mw5
def mw13 : WireKey := memoOp true mw2 mw5
def mw28 : WireKey := memoOp false mw2 mw6
def mw46 : WireKey := memoOp true mw2 mw6
def mw33 : WireKey := memoOp false mw2 mw7
def mw62 : WireKey := memoOp true mw2 mw7
def mw14 : WireKey := memoOp false mw3 mw4
def mw15 : WireKey := memoOp true mw3 mw4
def mw16 : WireKey := memoOp false mw3 mw5
def mw17 : WireKey := memoOp true mw3 mw5
def mw29 : WireKey := memoOp false mw3 mw6
def mw47 : WireKey := memoOp true mw3 mw6
def mw34 : WireKey := memoOp false mw3 mw7
def mw49 : WireKey := memoOp true mw3 mw7
def mw18 : WireKey := memoOp false mw4 mw5
def mw19 : WireKey := memoOp true mw4 mw5
def mw30 : WireKey := memoOp false mw4 mw6
def mw31 : WireKey := memoOp true mw4 mw6
def mw35 : WireKey := memoOp false mw4 mw7
def mw50 : WireKey := memoOp true mw4 mw7
def mw32 : WireKey := memoOp false mw5 mw6
def mw48 : WireKey := memoOp true mw5 mw6
def mw36 : WireKey := memoOp false mw5 mw7
def mw37 : WireKey := memoOp true mw5 mw7
def mw1 : WireKey := memoOp false mw6 mw7
def mw0 : WireKey := memoOp true mw6 mw7
def mw38 : WireKey := memoOp false mw0 mw2
def mw39 : WireKey := memoOp true mw0 mw2
def mw40 : WireKey := memoOp false mw0 mw3
def mw41 : WireKey := memoOp true mw0 mw3
def mw120 : WireKey := memoOp false mw0 mw31
def mw43 : WireKey := memoOp true mw0 mw31
def mw87 : WireKey := memoOp false mw0 mw37
def mw45 : WireKey := memoOp true mw0 mw37
def mw42 : WireKey := memoOp false mw0 mw4
def mw96 : WireKey := memoOp false mw0 mw46
def mw107 : WireKey := memoOp false mw0 mw47
def mw131 : WireKey := memoOp false mw0 mw48
def mw63 : WireKey := memoOp false mw0 mw49
def mw44 : WireKey := memoOp false mw0 mw5
def mw76 : WireKey := memoOp false mw0 mw50
def mw51 : WireKey := memoOp false mw0 mw62
def mw20 : WireKey := memoOp false mw1 mw2
def mw21 : WireKey := memoOp true mw1 mw2
def mw103 : WireKey := memoOp true mw1 mw28
def mw22 : WireKey := memoOp false mw1 mw29
def mw113 : WireKey := memoOp true mw1 mw29
def mw23 : WireKey := memoOp true mw1 mw3
def mw24 : WireKey := memoOp false mw1 mw30
def mw125 : WireKey := memoOp true mw1 mw30
def mw26 : WireKey := memoOp false mw1 mw32
def mw135 : WireKey := memoOp true mw1 mw32
def mw58 : WireKey := memoOp true mw1 mw33
def mw69 : WireKey := memoOp true mw1 mw34
def mw81 : WireKey := memoOp true mw1 mw35
def mw91 : WireKey := memoOp true mw1 mw36
def mw25 : WireKey := memoOp true mw1 mw4
def mw27 : WireKey := memoOp true mw1 mw5
def mw153 : WireKey := memoOp false mw10 mw12
def mw193 : WireKey := memoOp true mw10 mw12
def mw142 : WireKey := memoOp false mw10 mw14
def mw148 : WireKey := memoOp true mw10 mw14
def mw166 : WireKey := memoOp true mw10 mw18
def mw54 : WireKey := memoOp false mw10 mw28
def mw82 : WireKey := memoOp true mw10 mw28
def mw152 : WireKey := memoOp true mw10 mw3
def mw60 : WireKey := memoOp true mw10 mw30
def mw99 : WireKey := memoOp false mw10 mw33
def mw126 : WireKey := memoOp true mw10 mw33
def mw105 : WireKey := memoOp true mw10 mw35
def mw154 : WireKey := memoOp true mw10 mw5
def mw150 : WireKey := memoOp true mw10 mw6
def mw151 : WireKey := memoOp true mw10 mw7
def mw174 : WireKey := memoOp true mw10 mw8
def mw189 : WireKey := memoOp false mw11 mw13
def mw194 : WireKey := memoOp true mw11 mw13
def mw143 : WireKey := memoOp false mw11 mw15
def mw175 : WireKey := memoOp true mw11 mw15
def mw162 : WireKey := memoOp false mw11 mw19
def mw157 : WireKey := memoOp false mw11 mw3
def mw55 : WireKey := memoOp false mw11 mw31
def mw83 : WireKey := memoOp true mw11 mw31
def mw77 : WireKey := memoOp false mw11 mw46
def mw158 : WireKey := memoOp false mw11 mw5
def mw100 : WireKey := memoOp false mw11 mw50
def mw127 : WireKey := memoOp true mw11 mw50
def mw155 : WireKey := memoOp false mw11 mw6
def mw121 : WireKey := memoOp false mw11 mw62
def mw156 : WireKey := memoOp false mw11 mw7
def mw169 : WireKey := memoOp false mw11 mw9
def mw144 : WireKey := memoOp false mw12 mw16
def mw149 : WireKey := memoOp true mw12 mw16
def mw56 : WireKey := memoOp false mw12 mw28
def mw92 : WireKey := memoOp true mw12 mw28
def mw161 : WireKey := memoOp true mw12 mw3
def mw61 : WireKey := memoOp true mw12 mw32
def mw101 : WireKey := memoOp false mw12 mw33
def mw136 : WireKey := memoOp true mw12 mw33
def mw106 : WireKey := memoOp true mw12 mw36
def mw159 : WireKey := memoOp true mw12 mw6
def mw160 : WireKey := memoOp true mw12 mw7
def mw184 : WireKey := memoOp true mw12 mw8
def mw145 : WireKey := memoOp false mw13 mw17
def mw185 : WireKey := memoOp true mw13 mw17
def mw165 : WireKey := memoOp false mw13 mw3
def mw102 : WireKey := memoOp false mw13 mw37
def mw137 : WireKey := memoOp true mw13 mw37
def mw88 : WireKey := memoOp false mw13 mw46
def mw93 : WireKey := memoOp true mw13 mw46
def mw57 : WireKey := memoOp false mw13 mw48
def mw163 : WireKey := memoOp false mw13 mw6
def mw132 : WireKey := memoOp false mw13 mw62
def mw164 : WireKey := memoOp false mw13 mw7
def mw180 : WireKey := memoOp false mw13 mw9
def mw170 : WireKey := memoOp false mw14 mw16
def mw195 : WireKey := memoOp true mw14 mw16
def mw186 : WireKey := memoOp true mw14 mw18
def mw65 : WireKey := memoOp false mw14 mw29
def mw84 : WireKey := memoOp true mw14 mw29
def mw72 : WireKey := memoOp true mw14 mw30
def mw109 : WireKey := memoOp false mw14 mw34
def mw128 : WireKey := memoOp true mw14 mw34
def mw116 : WireKey := memoOp true mw14 mw35
def mw171 : WireKey := memoOp true mw14 mw5
def mw167 : WireKey := memoOp true mw14 mw6
def mw168 : WireKey := memoOp true mw14 mw7
def mw190 : WireKey := memoOp false mw15 mw17
def mw177 : WireKey := memoOp true mw15 mw17
def mw181 : WireKey := memoOp false mw15 mw19
def mw66 : WireKey := memoOp false mw15 mw31
def mw73 : WireKey := memoOp true mw15 mw31
def mw78 : WireKey := memoOp false mw15 mw47
def mw122 : WireKey := memoOp false mw15 mw49
def mw117 : WireKey := memoOp true mw15 mw49
def mw176 : WireKey := memoOp false mw15 mw5
def mw110 : WireKey := memoOp false mw15 mw50
def mw172 : WireKey := memoOp false mw15 mw6
def mw173 : WireKey := memoOp false mw15 mw7
def mw67 : WireKey := memoOp false mw16 mw29
def mw94 : WireKey := memoOp true mw16 mw29
def mw74 : WireKey := memoOp true mw16 mw32
def mw111 : WireKey := memoOp false mw16 mw34
def mw138 : WireKey := memoOp true mw16 mw34
def mw118 : WireKey := memoOp true mw16 mw36
def mw178 : WireKey := memoOp true mw16 mw6
def mw179 : WireKey := memoOp true mw16 mw7
def mw112 : WireKey := memoOp false mw17 mw37
def mw119 : WireKey := memoOp true mw17 mw37
def mw89 : WireKey := memoOp false mw17 mw47
def mw75 : WireKey := memoOp true mw17 mw47
def mw68 : WireKey := memoOp false mw17 mw48
def mw133 : WireKey := memoOp false mw17 mw49
def mw182 : WireKey := memoOp false mw17 mw6
def mw183 : WireKey := memoOp false mw17 mw7
def mw79 : WireKey := memoOp false mw18 mw30
def mw95 : WireKey := memoOp true mw18 mw30
def mw85 : WireKey := memoOp true mw18 mw32
def mw123 : WireKey := memoOp false mw18 mw35
def mw139 : WireKey := memoOp true mw18 mw35
def mw129 : WireKey := memoOp true mw18 mw36
def mw187 : WireKey := memoOp true mw18 mw6
def mw188 : WireKey := memoOp true mw18 mw7
def mw90 : WireKey := memoOp false mw19 mw31
def mw86 : WireKey := memoOp true mw19 mw31
def mw124 : WireKey := memoOp false mw19 mw37
def mw130 : WireKey := memoOp true mw19 mw37
def mw80 : WireKey := memoOp false mw19 mw48
def mw134 : WireKey := memoOp false mw19 mw50
def mw191 : WireKey := memoOp false mw19 mw6
def mw192 : WireKey := memoOp false mw19 mw7
def mw201 : WireKey := memoOp false mw197 mw2
def mw202 : WireKey := memoOp true mw197 mw2
def mw203 : WireKey := memoOp false mw197 mw3
def mw204 : WireKey := memoOp true mw197 mw3
def mw205 : WireKey := memoOp false mw197 mw4
def mw206 : WireKey := memoOp true mw197 mw4
def mw196 : WireKey := memoOp false mw197 mw6
def mw198 : WireKey := memoOp true mw197 mw6
def mw199 : WireKey := memoOp false mw197 mw7
def mw200 : WireKey := memoOp true mw197 mw7
def mw212 : WireKey := memoOp false mw2 mw208
def mw213 : WireKey := memoOp true mw2 mw208
def mw223 : WireKey := memoOp false mw2 mw219
def mw224 : WireKey := memoOp true mw2 mw219
def mw243 : WireKey := memoOp false mw2 mw241
def mw244 : WireKey := memoOp true mw2 mw241
def mw254 : WireKey := memoOp false mw2 mw252
def mw255 : WireKey := memoOp true mw2 mw252
def mw52 : WireKey := memoOp false mw2 mw29
def mw64 : WireKey := memoOp true mw2 mw29
def mw97 : WireKey := memoOp false mw2 mw34
def mw108 : WireKey := memoOp true mw2 mw34
def mw70 : WireKey := memoOp false mw2 mw47
def mw71 : WireKey := memoOp true mw2 mw47
def mw114 : WireKey := memoOp false mw2 mw49
def mw115 : WireKey := memoOp true mw2 mw49
def mw214 : WireKey := memoOp false mw208 mw3
def mw215 : WireKey := memoOp true mw208 mw3
def mw216 : WireKey := memoOp false mw208 mw5
def mw217 : WireKey := memoOp true mw208 mw5
def mw207 : WireKey := memoOp false mw208 mw6
def mw209 : WireKey := memoOp true mw208 mw6
def mw210 : WireKey := memoOp false mw208 mw7
def mw211 : WireKey := memoOp true mw208 mw7
def mw225 : WireKey := memoOp false mw219 mw4
def mw226 : WireKey := memoOp true mw219 mw4
def mw227 : WireKey := memoOp false mw219 mw5
def mw228 : WireKey := memoOp true mw219 mw5
def mw218 : WireKey := memoOp false mw219 mw6
def mw220 : WireKey := memoOp true mw219 mw6
def mw221 : WireKey := memoOp false mw219 mw7
def mw222 : WireKey := memoOp true mw219 mw7
def mw234 : WireKey := memoOp false mw231 mw3
def mw235 : WireKey := memoOp true mw231 mw3
def mw236 : WireKey := memoOp false mw231 mw4
def mw237 : WireKey := memoOp true mw231 mw4
def mw238 : WireKey := memoOp false mw231 mw5
def mw239 : WireKey := memoOp true mw231 mw5
def mw229 : WireKey := memoOp false mw231 mw6
def mw230 : WireKey := memoOp true mw231 mw6
def mw232 : WireKey := memoOp false mw231 mw7
def mw233 : WireKey := memoOp true mw231 mw7
def mw245 : WireKey := memoOp false mw241 mw3
def mw246 : WireKey := memoOp true mw241 mw3
def mw247 : WireKey := memoOp false mw241 mw4
def mw248 : WireKey := memoOp true mw241 mw4
def mw249 : WireKey := memoOp false mw241 mw5
def mw250 : WireKey := memoOp true mw241 mw5
def mw240 : WireKey := memoOp false mw241 mw6
def mw242 : WireKey := memoOp true mw241 mw6
def mw256 : WireKey := memoOp false mw252 mw3
def mw257 : WireKey := memoOp true mw252 mw3
def mw258 : WireKey := memoOp false mw252 mw4
def mw259 : WireKey := memoOp true mw252 mw4
def mw260 : WireKey := memoOp false mw252 mw5
def mw261 : WireKey := memoOp true mw252 mw5
def mw251 : WireKey := memoOp false mw252 mw7
def mw253 : WireKey := memoOp true mw252 mw7
def mw146 : WireKey := memoOp true mw28 mw29
def mw53 : WireKey := memoOp true mw28 mw3
def mw59 : WireKey := memoOp true mw29 mw8
def mw98 : WireKey := memoOp true mw3 mw33
def mw104 : WireKey := memoOp false mw3 mw62
def mw147 : WireKey := memoOp true mw33 mw34
def mw140 : WireKey := memoOp false mw46 mw47
def mw141 : WireKey := memoOp false mw49 mw62
def originalC : Nat → Runner := lookC I.NN I.AA I.HX I.HY (lz 0) (mz 0) (pL (rt.map (fun _ => 16)))
def originalS : Nat → Runner := look1C I.NN I.AA I.HX I.HY (lz 0) (mz 0) (pL (rt.map (fun _ => 16))) 12
def mcC0 : List MemoKey := [(12,10,1,mn520,[mw6,mw7,mw2,mw20,mw3,mw4,mw5]),(12,10,1,mn521,[mw6,mw21,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn522,[mw6,mw7,mw2,mw3,mw22,mw4,mw5]),(12,10,1,mn523,[mw6,mw23,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn524,[mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(12,10,1,mn525,[mw6,mw25,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn526,[mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(12,10,1,mn527,[mw6,mw27,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC0p : mcC0.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC1 : List MemoKey := [(12,10,1,mn552,[mw6,mw7,mw2,mw38,mw3,mw4,mw5]),(12,10,1,mn553,[mw0,mw6,mw7,mw2,mw38,mw3,mw4,mw5]),(12,10,1,mn554,[mw39,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn555,[mw6,mw7,mw2,mw3,mw40,mw4,mw5]),(12,10,1,mn556,[mw0,mw6,mw7,mw2,mw3,mw40,mw4,mw5]),(12,10,1,mn557,[mw41,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn558,[mw6,mw7,mw2,mw3,mw4,mw42,mw5]),(12,10,1,mn559,[mw0,mw6,mw7,mw2,mw3,mw4,mw42,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC1p : mcC1.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC2 : List MemoKey := [(12,10,1,mn560,[mw43,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn561,[mw6,mw7,mw2,mw3,mw4,mw5,mw44]),(12,10,1,mn562,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw44]),(12,10,1,mn563,[mw45,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn586,[mw6,mw7,mw2,mw20,mw3,mw4,mw5]),(12,10,1,mn587,[mw6,mw51,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn588,[mw6,mw51,mw7,mw2,mw28,mw3,mw4,mw5]),(12,10,1,mn589,[mw6,mw7,mw2,mw3,mw4,mw5,mw52])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC2p : mcC2.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC3 : List MemoKey := [(12,10,1,mn590,[mw6,mw7,mw53,mw2,mw3,mw4,mw5]),(12,10,1,mn591,[mw6,mw7,mw53,mw2,mw28,mw3,mw4,mw5]),(12,10,1,mn592,[mw6,mw7,mw2,mw3,mw4,mw5,mw54]),(12,10,1,mn593,[mw6,mw7,mw55,mw2,mw3,mw4,mw5]),(12,10,1,mn594,[mw6,mw7,mw55,mw2,mw28,mw3,mw4,mw5]),(12,10,1,mn595,[mw6,mw7,mw2,mw3,mw4,mw5,mw56]),(12,10,1,mn596,[mw6,mw7,mw57,mw2,mw3,mw4,mw5]),(12,10,1,mn597,[mw6,mw7,mw57,mw2,mw28,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC3p : mcC3.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC4 : List MemoKey := [(12,10,1,mn610,[mw6,mw7,mw58,mw2,mw3,mw4,mw5]),(12,10,1,mn611,[mw6,mw7,mw2,mw3,mw59,mw4,mw5]),(12,10,1,mn612,[mw6,mw7,mw2,mw3,mw4,mw60,mw5]),(12,10,1,mn613,[mw6,mw7,mw2,mw3,mw4,mw5,mw61]),(12,10,1,mn642,[mw6,mw7,mw2,mw3,mw22,mw4,mw5]),(12,10,1,mn643,[mw6,mw63,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn644,[mw6,mw63,mw7,mw2,mw3,mw29,mw4,mw5]),(12,10,1,mn645,[mw6,mw7,mw2,mw3,mw4,mw5,mw52])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC4p : mcC4.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC5 : List MemoKey := [(12,10,1,mn646,[mw6,mw7,mw64,mw2,mw3,mw4,mw5]),(12,10,1,mn647,[mw6,mw7,mw64,mw2,mw3,mw29,mw4,mw5]),(12,10,1,mn648,[mw6,mw7,mw2,mw3,mw4,mw5,mw65]),(12,10,1,mn649,[mw6,mw7,mw2,mw66,mw3,mw4,mw5]),(12,10,1,mn650,[mw6,mw7,mw2,mw66,mw3,mw29,mw4,mw5]),(12,10,1,mn651,[mw6,mw7,mw2,mw3,mw4,mw5,mw67]),(12,10,1,mn652,[mw6,mw7,mw2,mw68,mw3,mw4,mw5]),(12,10,1,mn653,[mw6,mw7,mw2,mw68,mw3,mw29,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC5p : mcC5.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC6 : List MemoKey := [(12,10,1,mn669,[mw6,mw7,mw69,mw2,mw3,mw4,mw5]),(12,10,1,mn670,[mw41,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn671,[mw6,mw7,mw2,mw70,mw3,mw4,mw5]),(12,10,1,mn672,[mw47,mw6,mw7,mw2,mw70,mw3,mw4,mw5]),(12,10,1,mn673,[mw71,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn674,[mw6,mw7,mw2,mw3,mw4,mw72,mw5]),(12,10,1,mn675,[mw47,mw6,mw7,mw2,mw3,mw4,mw72,mw5]),(12,10,1,mn676,[mw73,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC6p : mcC6.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC7 : List MemoKey := [(12,10,1,mn677,[mw6,mw7,mw2,mw3,mw4,mw5,mw74]),(12,10,1,mn678,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw74]),(12,10,1,mn679,[mw75,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn701,[mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(12,10,1,mn702,[mw6,mw76,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn703,[mw6,mw76,mw7,mw2,mw3,mw4,mw30,mw5]),(12,10,1,mn704,[mw6,mw7,mw2,mw3,mw4,mw5,mw54]),(12,10,1,mn705,[mw6,mw7,mw77,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC7p : mcC7.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC8 : List MemoKey := [(12,10,1,mn706,[mw6,mw7,mw77,mw2,mw3,mw4,mw30,mw5]),(12,10,1,mn707,[mw6,mw7,mw2,mw3,mw4,mw5,mw65]),(12,10,1,mn708,[mw6,mw7,mw2,mw78,mw3,mw4,mw5]),(12,10,1,mn709,[mw6,mw7,mw2,mw78,mw3,mw4,mw30,mw5]),(12,10,1,mn710,[mw6,mw7,mw2,mw3,mw4,mw5,mw79]),(12,10,1,mn711,[mw6,mw7,mw2,mw3,mw80,mw4,mw5]),(12,10,1,mn712,[mw6,mw7,mw2,mw3,mw80,mw4,mw30,mw5]),(12,10,1,mn731,[mw6,mw7,mw81,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC8p : mcC8.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC9 : List MemoKey := [(12,10,1,mn732,[mw43,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn733,[mw6,mw7,mw2,mw82,mw3,mw4,mw5]),(12,10,1,mn734,[mw31,mw6,mw7,mw2,mw82,mw3,mw4,mw5]),(12,10,1,mn735,[mw83,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn736,[mw6,mw7,mw2,mw3,mw84,mw4,mw5]),(12,10,1,mn737,[mw31,mw6,mw7,mw2,mw3,mw84,mw4,mw5]),(12,10,1,mn738,[mw73,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn739,[mw6,mw7,mw2,mw3,mw4,mw5,mw85])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC9p : mcC9.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC10 : List MemoKey := [(12,10,1,mn740,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw85]),(12,10,1,mn741,[mw86,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn766,[mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(12,10,1,mn767,[mw6,mw87,mw2,mw3,mw4,mw5]),(12,10,1,mn768,[mw6,mw87,mw2,mw3,mw4,mw5,mw32]),(12,10,1,mn769,[mw6,mw87,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn770,[mw6,mw87,mw7,mw2,mw3,mw4,mw5,mw32]),(12,10,1,mn771,[mw6,mw7,mw2,mw3,mw4,mw5,mw56])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC10p : mcC10.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC11 : List MemoKey := [(12,10,1,mn772,[mw6,mw7,mw88,mw2,mw3,mw4,mw5]),(12,10,1,mn773,[mw6,mw7,mw88,mw2,mw3,mw4,mw5,mw32]),(12,10,1,mn774,[mw6,mw7,mw2,mw3,mw4,mw5,mw67]),(12,10,1,mn775,[mw6,mw7,mw2,mw89,mw3,mw4,mw5]),(12,10,1,mn776,[mw6,mw7,mw2,mw89,mw3,mw4,mw5,mw32]),(12,10,1,mn777,[mw6,mw7,mw2,mw3,mw4,mw5,mw79]),(12,10,1,mn778,[mw6,mw7,mw2,mw3,mw90,mw4,mw5]),(12,10,1,mn779,[mw6,mw7,mw2,mw3,mw90,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC11p : mcC11.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC12 : List MemoKey := [(12,10,1,mn796,[mw6,mw7,mw91,mw2,mw3,mw4,mw5]),(12,10,1,mn797,[mw45,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn798,[mw6,mw7,mw2,mw92,mw3,mw4,mw5]),(12,10,1,mn799,[mw48,mw6,mw7,mw2,mw92,mw3,mw4,mw5]),(12,10,1,mn800,[mw93,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn801,[mw6,mw7,mw2,mw3,mw94,mw4,mw5]),(12,10,1,mn802,[mw48,mw6,mw7,mw2,mw3,mw94,mw4,mw5]),(12,10,1,mn803,[mw75,mw6,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC12p : mcC12.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC13 : List MemoKey := [(12,10,1,mn804,[mw6,mw7,mw2,mw3,mw4,mw95,mw5]),(12,10,1,mn805,[mw48,mw6,mw7,mw2,mw3,mw4,mw95,mw5]),(12,10,1,mn806,[mw86,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn824,[mw6,mw7,mw2,mw20,mw3,mw4,mw5]),(12,10,1,mn825,[mw96,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn826,[mw96,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn827,[mw6,mw7,mw2,mw3,mw4,mw5,mw97]),(12,10,1,mn828,[mw6,mw7,mw98,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC13p : mcC13.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC14 : List MemoKey := [(12,10,1,mn829,[mw6,mw7,mw98,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn830,[mw6,mw7,mw2,mw3,mw4,mw5,mw99]),(12,10,1,mn831,[mw6,mw7,mw100,mw2,mw3,mw4,mw5]),(12,10,1,mn832,[mw6,mw7,mw100,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn833,[mw6,mw7,mw2,mw3,mw4,mw5,mw101]),(12,10,1,mn834,[mw6,mw7,mw102,mw2,mw3,mw4,mw5]),(12,10,1,mn835,[mw6,mw7,mw102,mw2,mw33,mw3,mw4,mw5]),(12,10,1,mn846,[mw6,mw103,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC14p : mcC14.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC15 : List MemoKey := [(12,10,1,mn847,[mw6,mw7,mw2,mw3,mw104,mw4,mw5]),(12,10,1,mn848,[mw6,mw7,mw2,mw3,mw4,mw105,mw5]),(12,10,1,mn849,[mw6,mw7,mw2,mw3,mw4,mw5,mw106]),(12,10,1,mn870,[mw6,mw7,mw2,mw3,mw22,mw4,mw5]),(12,10,1,mn871,[mw107,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn872,[mw107,mw6,mw7,mw2,mw3,mw34,mw4,mw5]),(12,10,1,mn873,[mw6,mw7,mw2,mw3,mw4,mw5,mw97]),(12,10,1,mn874,[mw6,mw7,mw108,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC15p : mcC15.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC16 : List MemoKey := [(12,10,1,mn875,[mw6,mw7,mw108,mw2,mw3,mw34,mw4,mw5]),(12,10,1,mn876,[mw6,mw7,mw2,mw3,mw4,mw5,mw109]),(12,10,1,mn877,[mw6,mw7,mw2,mw110,mw3,mw4,mw5]),(12,10,1,mn878,[mw6,mw7,mw2,mw110,mw3,mw34,mw4,mw5]),(12,10,1,mn879,[mw6,mw7,mw2,mw3,mw4,mw5,mw111]),(12,10,1,mn880,[mw6,mw7,mw2,mw112,mw3,mw4,mw5]),(12,10,1,mn881,[mw6,mw7,mw2,mw112,mw3,mw34,mw4,mw5]),(12,10,1,mn893,[mw6,mw113,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC16p : mcC16.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC17 : List MemoKey := [(12,10,1,mn894,[mw41,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn895,[mw6,mw7,mw2,mw114,mw3,mw4,mw5]),(12,10,1,mn896,[mw6,mw49,mw7,mw2,mw114,mw3,mw4,mw5]),(12,10,1,mn897,[mw6,mw115,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn898,[mw6,mw7,mw2,mw3,mw4,mw116,mw5]),(12,10,1,mn899,[mw6,mw49,mw7,mw2,mw3,mw4,mw116,mw5]),(12,10,1,mn900,[mw6,mw117,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn901,[mw6,mw7,mw2,mw3,mw4,mw5,mw118])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC17p : mcC17.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC18 : List MemoKey := [(12,10,1,mn902,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw118]),(12,10,1,mn903,[mw6,mw119,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn918,[mw6,mw7,mw2,mw3,mw4,mw24,mw5]),(12,10,1,mn919,[mw120,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn920,[mw120,mw7,mw2,mw3,mw4,mw35,mw5]),(12,10,1,mn921,[mw120,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn922,[mw120,mw6,mw7,mw2,mw3,mw4,mw35,mw5]),(12,10,1,mn923,[mw6,mw7,mw2,mw3,mw4,mw5,mw99])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC18p : mcC18.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC19 : List MemoKey := [(12,10,1,mn924,[mw6,mw7,mw121,mw2,mw3,mw4,mw5]),(12,10,1,mn925,[mw6,mw7,mw121,mw2,mw3,mw4,mw35,mw5]),(12,10,1,mn926,[mw6,mw7,mw2,mw3,mw4,mw5,mw109]),(12,10,1,mn927,[mw6,mw7,mw2,mw122,mw3,mw4,mw5]),(12,10,1,mn928,[mw6,mw7,mw2,mw122,mw3,mw4,mw35,mw5]),(12,10,1,mn929,[mw6,mw7,mw2,mw3,mw4,mw5,mw123]),(12,10,1,mn930,[mw6,mw7,mw2,mw3,mw124,mw4,mw5]),(12,10,1,mn931,[mw6,mw7,mw2,mw3,mw124,mw4,mw35,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC19p : mcC19.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC20 : List MemoKey := [(12,10,1,mn946,[mw6,mw125,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn947,[mw43,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn948,[mw6,mw7,mw2,mw126,mw3,mw4,mw5]),(12,10,1,mn949,[mw6,mw50,mw7,mw2,mw126,mw3,mw4,mw5]),(12,10,1,mn950,[mw6,mw127,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn951,[mw6,mw7,mw2,mw3,mw128,mw4,mw5]),(12,10,1,mn952,[mw6,mw50,mw7,mw2,mw3,mw128,mw4,mw5]),(12,10,1,mn953,[mw6,mw117,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC20p : mcC20.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC21 : List MemoKey := [(12,10,1,mn954,[mw6,mw7,mw2,mw3,mw4,mw5,mw129]),(12,10,1,mn955,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw129]),(12,10,1,mn956,[mw6,mw130,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn973,[mw6,mw7,mw2,mw3,mw4,mw5,mw26]),(12,10,1,mn974,[mw131,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn975,[mw131,mw6,mw7,mw2,mw3,mw4,mw5,mw36]),(12,10,1,mn976,[mw6,mw7,mw2,mw3,mw4,mw5,mw101]),(12,10,1,mn977,[mw6,mw7,mw132,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC21p : mcC21.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC22 : List MemoKey := [(12,10,1,mn978,[mw6,mw7,mw132,mw2,mw3,mw4,mw5,mw36]),(12,10,1,mn979,[mw6,mw7,mw2,mw3,mw4,mw5,mw111]),(12,10,1,mn980,[mw6,mw7,mw2,mw133,mw3,mw4,mw5]),(12,10,1,mn981,[mw6,mw7,mw2,mw133,mw3,mw4,mw5,mw36]),(12,10,1,mn982,[mw6,mw7,mw2,mw3,mw4,mw5,mw123]),(12,10,1,mn983,[mw6,mw7,mw2,mw3,mw134,mw4,mw5]),(12,10,1,mn984,[mw6,mw7,mw2,mw3,mw134,mw4,mw5,mw36]),(12,10,1,mn997,[mw6,mw135,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC22p : mcC22.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC23 : List MemoKey := [(12,10,1,mn998,[mw45,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn999,[mw6,mw7,mw136,mw3,mw4,mw5]),(12,10,1,mn1000,[mw6,mw37,mw7,mw136,mw3,mw4,mw5]),(12,10,1,mn1001,[mw6,mw7,mw2,mw136,mw3,mw4,mw5]),(12,10,1,mn1002,[mw6,mw37,mw7,mw2,mw136,mw3,mw4,mw5]),(12,10,1,mn1003,[mw6,mw137,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1004,[mw6,mw7,mw2,mw3,mw138,mw4,mw5]),(12,10,1,mn1005,[mw6,mw37,mw7,mw2,mw3,mw138,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC23p : mcC23.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC24 : List MemoKey := [(12,10,1,mn1006,[mw6,mw119,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1007,[mw6,mw7,mw2,mw3,mw4,mw139,mw5]),(12,10,1,mn1008,[mw6,mw37,mw7,mw2,mw3,mw4,mw139,mw5]),(12,10,1,mn1009,[mw6,mw130,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1020,[mw6,mw7,mw2,mw3,mw4,mw5,mw52]),(12,10,1,mn1021,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw52]),(12,10,1,mn1022,[mw140,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1023,[mw140,mw6,mw7,mw2,mw3,mw4,mw5,mw8])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC24p : mcC24.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC25 : List MemoKey := [(12,10,1,mn1024,[mw6,mw7,mw2,mw3,mw4,mw5,mw97]),(12,10,1,mn1025,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw97]),(12,10,1,mn1026,[mw6,mw141,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1027,[mw6,mw141,mw7,mw2,mw3,mw4,mw5,mw8]),(12,10,1,mn1028,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn1029,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw142]),(12,10,1,mn1030,[mw6,mw7,mw2,mw3,mw143,mw4,mw5]),(12,10,1,mn1031,[mw6,mw7,mw2,mw3,mw143,mw4,mw5,mw8])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC25p : mcC25.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC26 : List MemoKey := [(12,10,1,mn1032,[mw6,mw7,mw2,mw3,mw4,mw5,mw144]),(12,10,1,mn1033,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw144]),(12,10,1,mn1034,[mw6,mw7,mw2,mw3,mw4,mw145,mw5]),(12,10,1,mn1035,[mw6,mw7,mw2,mw3,mw4,mw145,mw5,mw8]),(12,10,1,mn1040,[mw7,mw146,mw2,mw3,mw4,mw5]),(12,10,1,mn1041,[mw6,mw7,mw146,mw2,mw3,mw4,mw5]),(12,10,1,mn1042,[mw6,mw147,mw2,mw3,mw4,mw5]),(12,10,1,mn1043,[mw6,mw7,mw147,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC26p : mcC26.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC27 : List MemoKey := [(12,10,1,mn1044,[mw6,mw7,mw2,mw3,mw4,mw5,mw148]),(12,10,1,mn1045,[mw6,mw7,mw2,mw3,mw4,mw5,mw149]),(12,10,1,mn1053,[mw6,mw7,mw2,mw3,mw4,mw5,mw54]),(12,10,1,mn1054,[mw150,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1055,[mw150,mw6,mw7,mw2,mw3,mw4,mw5,mw10]),(12,10,1,mn1056,[mw6,mw7,mw2,mw3,mw4,mw5,mw99]),(12,10,1,mn1057,[mw6,mw151,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1058,[mw6,mw151,mw7,mw2,mw3,mw4,mw5,mw10])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC27p : mcC27.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC28 : List MemoKey := [(12,10,1,mn1059,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn1060,[mw6,mw7,mw2,mw152,mw3,mw4,mw5]),(12,10,1,mn1061,[mw6,mw7,mw2,mw152,mw3,mw4,mw5,mw10]),(12,10,1,mn1062,[mw6,mw7,mw2,mw3,mw4,mw5,mw153]),(12,10,1,mn1063,[mw6,mw7,mw2,mw3,mw4,mw154,mw5]),(12,10,1,mn1064,[mw6,mw7,mw2,mw3,mw4,mw154,mw5,mw10]),(12,10,1,mn1071,[mw6,mw7,mw155,mw2,mw3,mw4,mw5]),(12,10,1,mn1072,[mw6,mw7,mw156,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC28p : mcC28.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC29 : List MemoKey := [(12,10,1,mn1073,[mw6,mw7,mw2,mw3,mw4,mw5,mw157]),(12,10,1,mn1074,[mw6,mw7,mw2,mw3,mw4,mw5,mw158]),(12,10,1,mn1083,[mw6,mw7,mw2,mw3,mw4,mw5,mw56]),(12,10,1,mn1084,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw56]),(12,10,1,mn1085,[mw159,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1086,[mw159,mw6,mw7,mw2,mw3,mw4,mw5,mw12]),(12,10,1,mn1087,[mw6,mw7,mw2,mw3,mw4,mw5,mw101]),(12,10,1,mn1088,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw101])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC29p : mcC29.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC30 : List MemoKey := [(12,10,1,mn1089,[mw6,mw160,mw2,mw3,mw4,mw5]),(12,10,1,mn1090,[mw6,mw160,mw2,mw3,mw4,mw5,mw12]),(12,10,1,mn1091,[mw6,mw160,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1092,[mw6,mw160,mw7,mw2,mw3,mw4,mw5,mw12]),(12,10,1,mn1093,[mw6,mw7,mw2,mw3,mw4,mw5,mw144]),(12,10,1,mn1094,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw144]),(12,10,1,mn1095,[mw6,mw7,mw2,mw161,mw3,mw4,mw5]),(12,10,1,mn1096,[mw6,mw7,mw2,mw161,mw3,mw4,mw5,mw12])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC30p : mcC30.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC31 : List MemoKey := [(12,10,1,mn1097,[mw6,mw7,mw2,mw3,mw4,mw5,mw153]),(12,10,1,mn1098,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw153]),(12,10,1,mn1099,[mw6,mw7,mw2,mw3,mw162,mw4,mw5]),(12,10,1,mn1100,[mw6,mw7,mw2,mw3,mw162,mw4,mw5,mw12]),(12,10,1,mn1107,[mw6,mw7,mw163,mw2,mw3,mw4,mw5]),(12,10,1,mn1108,[mw6,mw7,mw164,mw2,mw3,mw4,mw5]),(12,10,1,mn1109,[mw6,mw7,mw2,mw3,mw4,mw5,mw165]),(12,10,1,mn1110,[mw6,mw7,mw2,mw3,mw4,mw5,mw166])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC31p : mcC31.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC32 : List MemoKey := [(12,10,1,mn1118,[mw6,mw7,mw2,mw3,mw4,mw5,mw65]),(12,10,1,mn1119,[mw167,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1120,[mw167,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(12,10,1,mn1121,[mw6,mw7,mw2,mw3,mw4,mw5,mw109]),(12,10,1,mn1122,[mw6,mw168,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1123,[mw6,mw168,mw7,mw2,mw3,mw4,mw5,mw14]),(12,10,1,mn1124,[mw6,mw7,mw2,mw3,mw4,mw5,mw142]),(12,10,1,mn1125,[mw6,mw7,mw169,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC32p : mcC32.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC33 : List MemoKey := [(12,10,1,mn1126,[mw6,mw7,mw169,mw3,mw4,mw5,mw14]),(12,10,1,mn1127,[mw6,mw7,mw169,mw2,mw3,mw4,mw5]),(12,10,1,mn1128,[mw6,mw7,mw169,mw2,mw3,mw4,mw5,mw14]),(12,10,1,mn1129,[mw6,mw7,mw2,mw3,mw4,mw5,mw170]),(12,10,1,mn1130,[mw6,mw7,mw2,mw3,mw4,mw171,mw5]),(12,10,1,mn1131,[mw6,mw7,mw2,mw3,mw4,mw171,mw5,mw14]),(12,10,1,mn1136,[mw6,mw7,mw2,mw172,mw3,mw4,mw5]),(12,10,1,mn1137,[mw6,mw7,mw2,mw15,mw172,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC33p : mcC33.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC34 : List MemoKey := [(12,10,1,mn1138,[mw73,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1139,[mw6,mw2,mw173,mw3,mw4,mw5]),(12,10,1,mn1140,[mw6,mw2,mw15,mw173,mw3,mw4,mw5]),(12,10,1,mn1141,[mw6,mw7,mw2,mw173,mw3,mw4,mw5]),(12,10,1,mn1142,[mw6,mw7,mw2,mw15,mw173,mw3,mw4,mw5]),(12,10,1,mn1143,[mw6,mw117,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1144,[mw6,mw7,mw2,mw3,mw4,mw5,mw174]),(12,10,1,mn1145,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw174])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC34p : mcC34.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC35 : List MemoKey := [(12,10,1,mn1146,[mw6,mw7,mw175,mw2,mw3,mw4,mw5]),(12,10,1,mn1147,[mw6,mw7,mw2,mw3,mw4,mw5,mw176]),(12,10,1,mn1148,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw176]),(12,10,1,mn1149,[mw6,mw7,mw2,mw177,mw3,mw4,mw5]),(12,10,1,mn1156,[mw6,mw7,mw2,mw3,mw4,mw5,mw67]),(12,10,1,mn1157,[mw6,mw7,mw2,mw3,mw4,mw5,mw16,mw67]),(12,10,1,mn1158,[mw178,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1159,[mw178,mw6,mw7,mw2,mw3,mw4,mw5,mw16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC35p : mcC35.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC36 : List MemoKey := [(12,10,1,mn1160,[mw6,mw7,mw2,mw3,mw4,mw5,mw111]),(12,10,1,mn1161,[mw6,mw7,mw2,mw3,mw4,mw5,mw16,mw111]),(12,10,1,mn1162,[mw6,mw179,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1163,[mw6,mw179,mw7,mw2,mw3,mw4,mw5,mw16]),(12,10,1,mn1164,[mw6,mw7,mw2,mw3,mw4,mw5,mw144]),(12,10,1,mn1165,[mw6,mw7,mw2,mw3,mw4,mw5,mw16,mw144]),(12,10,1,mn1166,[mw6,mw7,mw180,mw2,mw3,mw4,mw5]),(12,10,1,mn1167,[mw6,mw7,mw180,mw2,mw3,mw4,mw5,mw16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC36p : mcC36.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC37 : List MemoKey := [(12,10,1,mn1168,[mw6,mw7,mw2,mw3,mw4,mw5,mw170]),(12,10,1,mn1169,[mw6,mw7,mw2,mw3,mw4,mw5,mw16,mw170]),(12,10,1,mn1170,[mw6,mw7,mw2,mw3,mw181,mw4,mw5]),(12,10,1,mn1171,[mw6,mw7,mw2,mw3,mw181,mw4,mw5,mw16]),(12,10,1,mn1174,[mw7,mw2,mw182,mw3,mw4,mw5]),(12,10,1,mn1175,[mw7,mw2,mw17,mw182,mw3,mw4,mw5]),(12,10,1,mn1176,[mw6,mw7,mw2,mw182,mw3,mw4,mw5]),(12,10,1,mn1177,[mw6,mw7,mw2,mw17,mw182,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC37p : mcC37.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC38 : List MemoKey := [(12,10,1,mn1178,[mw75,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1179,[mw6,mw7,mw2,mw183,mw3,mw4,mw5]),(12,10,1,mn1180,[mw6,mw7,mw2,mw17,mw183,mw3,mw4,mw5]),(12,10,1,mn1181,[mw6,mw119,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1182,[mw6,mw7,mw2,mw3,mw4,mw5,mw184]),(12,10,1,mn1183,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw184]),(12,10,1,mn1184,[mw6,mw7,mw185,mw2,mw3,mw4,mw5]),(12,10,1,mn1185,[mw6,mw7,mw2,mw3,mw4,mw5,mw186])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC38p : mcC38.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC39 : List MemoKey := [(12,10,1,mn1186,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw186]),(12,10,1,mn1187,[mw6,mw7,mw2,mw177,mw3,mw4,mw5]),(12,10,1,mn1192,[mw6,mw7,mw2,mw3,mw4,mw5,mw79]),(12,10,1,mn1193,[mw187,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1194,[mw187,mw7,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn1195,[mw187,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1196,[mw187,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn1197,[mw6,mw7,mw2,mw3,mw4,mw5,mw123])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC39p : mcC39.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC40 : List MemoKey := [(12,10,1,mn1198,[mw6,mw188,mw2,mw3,mw4,mw5]),(12,10,1,mn1199,[mw6,mw188,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn1200,[mw6,mw188,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1201,[mw6,mw188,mw7,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn1202,[mw6,mw7,mw2,mw3,mw4,mw5,mw153]),(12,10,1,mn1203,[mw6,mw7,mw189,mw3,mw4,mw5]),(12,10,1,mn1204,[mw6,mw7,mw189,mw3,mw4,mw5,mw18]),(12,10,1,mn1205,[mw6,mw7,mw189,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC40p : mcC40.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC41 : List MemoKey := [(12,10,1,mn1206,[mw6,mw7,mw189,mw2,mw3,mw4,mw5,mw18]),(12,10,1,mn1207,[mw6,mw7,mw2,mw3,mw4,mw5,mw170]),(12,10,1,mn1208,[mw6,mw7,mw2,mw190,mw4,mw5]),(12,10,1,mn1209,[mw6,mw7,mw2,mw190,mw4,mw5,mw18]),(12,10,1,mn1210,[mw6,mw7,mw2,mw190,mw3,mw4,mw5]),(12,10,1,mn1211,[mw6,mw7,mw2,mw190,mw3,mw4,mw5,mw18]),(12,10,1,mn1212,[mw6,mw7,mw2,mw3,mw191,mw4,mw5]),(12,10,1,mn1213,[mw6,mw7,mw2,mw3,mw19,mw191,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC41p : mcC41.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC42 : List MemoKey := [(12,10,1,mn1214,[mw86,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1215,[mw86,mw6,mw7,mw2,mw3,mw19,mw4,mw5]),(12,10,1,mn1216,[mw6,mw7,mw2,mw3,mw192,mw4,mw5]),(12,10,1,mn1217,[mw6,mw7,mw2,mw3,mw19,mw192,mw4,mw5]),(12,10,1,mn1218,[mw6,mw130,mw7,mw2,mw3,mw4,mw5]),(12,10,1,mn1219,[mw6,mw130,mw7,mw2,mw3,mw19,mw4,mw5]),(12,10,1,mn1220,[mw6,mw7,mw2,mw3,mw4,mw5,mw193]),(12,10,1,mn1221,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw193])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC42p : mcC42.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC43 : List MemoKey := [(12,10,1,mn1222,[mw6,mw7,mw194,mw2,mw3,mw4,mw5]),(12,10,1,mn1223,[mw6,mw7,mw194,mw2,mw3,mw19,mw4,mw5]),(12,10,1,mn1224,[mw6,mw7,mw2,mw3,mw4,mw5,mw195]),(12,10,1,mn1225,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw195]),(12,10,1,mn1226,[mw6,mw7,mw2,mw177,mw3,mw4,mw5]),(12,10,1,mn1227,[mw6,mw7,mw2,mw177,mw3,mw19,mw4,mw5]),(12,10,0,mn1228,[mw6,mw7,mw196,mw2,mw3,mw4]),(12,10,0,mn1229,[mw6,mw7,mw197,mw196,mw2,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC43p : mcC43.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC44 : List MemoKey := [(12,10,0,mn1230,[mw198,mw6,mw7,mw2,mw3,mw4]),(12,10,0,mn1231,[mw198,mw6,mw7,mw197,mw2,mw3,mw4]),(12,10,0,mn1232,[mw6,mw7,mw199,mw2,mw3,mw4]),(12,10,0,mn1233,[mw6,mw7,mw197,mw199,mw2,mw3,mw4]),(12,10,0,mn1234,[mw6,mw200,mw7,mw2,mw3,mw4]),(12,10,0,mn1235,[mw6,mw200,mw7,mw197,mw2,mw3,mw4]),(12,10,0,mn1236,[mw6,mw7,mw2,mw201,mw3,mw4]),(12,10,0,mn1237,[mw6,mw7,mw197,mw2,mw201,mw3,mw4])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC44p : mcC44.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC45 : List MemoKey := [(12,10,0,mn1238,[mw6,mw7,mw202,mw2,mw3,mw4]),(12,10,0,mn1239,[mw6,mw7,mw202,mw197,mw2,mw3,mw4]),(12,10,0,mn1240,[mw6,mw7,mw2,mw3,mw203,mw4]),(12,10,0,mn1241,[mw6,mw7,mw197,mw2,mw3,mw203,mw4]),(12,10,0,mn1242,[mw6,mw7,mw204,mw2,mw3,mw4]),(12,10,0,mn1243,[mw6,mw7,mw204,mw197,mw2,mw3,mw4]),(12,10,0,mn1244,[mw6,mw7,mw2,mw3,mw4,mw205]),(12,10,0,mn1245,[mw6,mw7,mw197,mw2,mw3,mw4,mw205])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC45p : mcC45.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC46 : List MemoKey := [(12,10,0,mn1246,[mw6,mw7,mw206,mw2,mw3,mw4]),(12,10,0,mn1247,[mw6,mw7,mw206,mw197,mw2,mw3,mw4]),(12,10,0,mn1229,[mw6,mw7,mw196,mw2,mw3,mw4,mw5]),(12,10,0,mn1248,[mw6,mw7,mw197,mw196,mw2,mw3,mw4,mw5]),(12,10,0,mn1231,[mw198,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1249,[mw198,mw6,mw7,mw197,mw2,mw3,mw4,mw5]),(12,10,0,mn1233,[mw6,mw7,mw199,mw2,mw3,mw4,mw5]),(12,10,0,mn1250,[mw6,mw7,mw197,mw199,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC46p : mcC46.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC47 : List MemoKey := [(12,10,0,mn1235,[mw6,mw200,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1251,[mw6,mw200,mw7,mw197,mw2,mw3,mw4,mw5]),(12,10,0,mn1237,[mw6,mw7,mw2,mw201,mw3,mw4,mw5]),(12,10,0,mn1252,[mw6,mw7,mw197,mw2,mw201,mw3,mw4,mw5]),(12,10,0,mn1239,[mw6,mw7,mw202,mw2,mw3,mw4,mw5]),(12,10,0,mn1253,[mw6,mw7,mw202,mw197,mw2,mw3,mw4,mw5]),(12,10,0,mn1241,[mw6,mw7,mw2,mw3,mw203,mw4,mw5]),(12,10,0,mn1254,[mw6,mw7,mw197,mw2,mw3,mw203,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC47p : mcC47.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC48 : List MemoKey := [(12,10,0,mn1243,[mw6,mw7,mw204,mw2,mw3,mw4,mw5]),(12,10,0,mn1255,[mw6,mw7,mw204,mw197,mw2,mw3,mw4,mw5]),(12,10,0,mn1245,[mw6,mw7,mw2,mw3,mw4,mw205,mw5]),(12,10,0,mn1256,[mw6,mw7,mw197,mw2,mw3,mw4,mw205,mw5]),(12,10,0,mn1247,[mw6,mw7,mw206,mw2,mw3,mw4,mw5]),(12,10,0,mn1257,[mw6,mw7,mw206,mw197,mw2,mw3,mw4,mw5]),(12,10,0,mn1258,[mw6,mw7,mw207,mw2,mw3,mw5]),(12,10,0,mn1259,[mw6,mw7,mw208,mw207,mw2,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC48p : mcC48.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC49 : List MemoKey := [(12,10,0,mn1260,[mw209,mw6,mw7,mw2,mw3,mw5]),(12,10,0,mn1261,[mw209,mw6,mw7,mw208,mw2,mw3,mw5]),(12,10,0,mn1262,[mw6,mw7,mw210,mw2,mw3,mw5]),(12,10,0,mn1263,[mw6,mw7,mw208,mw210,mw2,mw3,mw5]),(12,10,0,mn1264,[mw6,mw211,mw7,mw2,mw3,mw5]),(12,10,0,mn1265,[mw6,mw211,mw7,mw208,mw2,mw3,mw5]),(12,10,0,mn1266,[mw6,mw7,mw2,mw212,mw3,mw5]),(12,10,0,mn1267,[mw6,mw7,mw208,mw2,mw212,mw3,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC49p : mcC49.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC50 : List MemoKey := [(12,10,0,mn1268,[mw6,mw7,mw213,mw2,mw3,mw5]),(12,10,0,mn1269,[mw6,mw7,mw213,mw208,mw2,mw3,mw5]),(12,10,0,mn1270,[mw6,mw7,mw2,mw3,mw214,mw5]),(12,10,0,mn1271,[mw6,mw7,mw208,mw2,mw3,mw214,mw5]),(12,10,0,mn1272,[mw6,mw7,mw215,mw2,mw3,mw5]),(12,10,0,mn1273,[mw6,mw7,mw215,mw208,mw2,mw3,mw5]),(12,10,0,mn1246,[mw6,mw7,mw2,mw3,mw5,mw216]),(12,10,0,mn1274,[mw6,mw7,mw208,mw2,mw3,mw5,mw216])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC50p : mcC50.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC51 : List MemoKey := [(12,10,0,mn1244,[mw6,mw7,mw217,mw2,mw3,mw5]),(12,10,0,mn1275,[mw6,mw7,mw217,mw208,mw2,mw3,mw5]),(12,10,0,mn1259,[mw6,mw7,mw207,mw2,mw3,mw4,mw5]),(12,10,0,mn1276,[mw6,mw7,mw208,mw207,mw2,mw3,mw4,mw5]),(12,10,0,mn1261,[mw209,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1263,[mw6,mw7,mw210,mw2,mw3,mw4,mw5]),(12,10,0,mn1277,[mw6,mw7,mw208,mw210,mw2,mw3,mw4,mw5]),(12,10,0,mn1265,[mw6,mw211,mw7,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC51p : mcC51.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC52 : List MemoKey := [(12,10,0,mn1267,[mw6,mw7,mw2,mw212,mw3,mw4,mw5]),(12,10,0,mn1278,[mw6,mw7,mw208,mw2,mw212,mw3,mw4,mw5]),(12,10,0,mn1269,[mw6,mw7,mw213,mw2,mw3,mw4,mw5]),(12,10,0,mn1271,[mw6,mw7,mw2,mw3,mw214,mw4,mw5]),(12,10,0,mn1279,[mw6,mw7,mw208,mw2,mw3,mw214,mw4,mw5]),(12,10,0,mn1273,[mw6,mw7,mw215,mw2,mw3,mw4,mw5]),(12,10,0,mn1274,[mw6,mw7,mw2,mw3,mw4,mw5,mw216]),(12,10,0,mn1280,[mw6,mw7,mw208,mw2,mw3,mw4,mw5,mw216])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC52p : mcC52.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC53 : List MemoKey := [(12,10,0,mn1275,[mw6,mw7,mw217,mw2,mw3,mw4,mw5]),(12,10,0,mn1281,[mw6,mw7,mw218,mw2,mw4,mw5]),(12,10,0,mn1282,[mw6,mw7,mw219,mw218,mw2,mw4,mw5]),(12,10,0,mn1283,[mw220,mw6,mw7,mw2,mw4,mw5]),(12,10,0,mn1284,[mw220,mw6,mw7,mw219,mw2,mw4,mw5]),(12,10,0,mn1285,[mw6,mw7,mw221,mw2,mw4,mw5]),(12,10,0,mn1286,[mw6,mw7,mw219,mw221,mw2,mw4,mw5]),(12,10,0,mn1287,[mw6,mw222,mw7,mw2,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC53p : mcC53.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC54 : List MemoKey := [(12,10,0,mn1288,[mw6,mw222,mw7,mw219,mw2,mw4,mw5]),(12,10,0,mn1289,[mw6,mw7,mw2,mw223,mw4,mw5]),(12,10,0,mn1290,[mw6,mw7,mw219,mw2,mw223,mw4,mw5]),(12,10,0,mn1291,[mw6,mw7,mw224,mw2,mw4,mw5]),(12,10,0,mn1292,[mw6,mw7,mw224,mw219,mw2,mw4,mw5]),(12,10,0,mn1272,[mw6,mw7,mw2,mw4,mw225,mw5]),(12,10,0,mn1293,[mw6,mw7,mw219,mw2,mw4,mw225,mw5]),(12,10,0,mn1270,[mw6,mw7,mw226,mw2,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC54p : mcC54.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC55 : List MemoKey := [(12,10,0,mn1294,[mw6,mw7,mw226,mw219,mw2,mw4,mw5]),(12,10,0,mn1242,[mw6,mw7,mw2,mw4,mw5,mw227]),(12,10,0,mn1295,[mw6,mw7,mw219,mw2,mw4,mw5,mw227]),(12,10,0,mn1240,[mw6,mw7,mw228,mw2,mw4,mw5]),(12,10,0,mn1296,[mw6,mw7,mw228,mw219,mw2,mw4,mw5]),(12,10,0,mn1282,[mw6,mw7,mw218,mw2,mw3,mw4,mw5]),(12,10,0,mn1284,[mw220,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1297,[mw220,mw6,mw7,mw219,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC55p : mcC55.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC56 : List MemoKey := [(12,10,0,mn1286,[mw6,mw7,mw221,mw2,mw3,mw4,mw5]),(12,10,0,mn1288,[mw6,mw222,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1298,[mw6,mw222,mw7,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1290,[mw6,mw7,mw2,mw223,mw3,mw4,mw5]),(12,10,0,mn1292,[mw6,mw7,mw224,mw2,mw3,mw4,mw5]),(12,10,0,mn1299,[mw6,mw7,mw224,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1293,[mw6,mw7,mw2,mw3,mw4,mw225,mw5]),(12,10,0,mn1294,[mw6,mw7,mw226,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC56p : mcC56.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC57 : List MemoKey := [(12,10,0,mn1300,[mw6,mw7,mw226,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1295,[mw6,mw7,mw2,mw3,mw4,mw5,mw227]),(12,10,0,mn1296,[mw6,mw7,mw228,mw2,mw3,mw4,mw5]),(12,10,0,mn1301,[mw6,mw7,mw228,mw219,mw2,mw3,mw4,mw5]),(12,10,0,mn1302,[mw6,mw7,mw229,mw3,mw4,mw5]),(12,10,0,mn1303,[mw230,mw6,mw7,mw3,mw4,mw5]),(12,10,0,mn1304,[mw230,mw6,mw7,mw231,mw3,mw4,mw5]),(12,10,0,mn1305,[mw6,mw7,mw232,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC57p : mcC57.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC58 : List MemoKey := [(12,10,0,mn1306,[mw6,mw233,mw7,mw3,mw4,mw5]),(12,10,0,mn1307,[mw6,mw233,mw7,mw231,mw3,mw4,mw5]),(12,10,0,mn1291,[mw6,mw7,mw3,mw234,mw4,mw5]),(12,10,0,mn1289,[mw6,mw7,mw235,mw3,mw4,mw5]),(12,10,0,mn1308,[mw6,mw7,mw235,mw231,mw3,mw4,mw5]),(12,10,0,mn1268,[mw6,mw7,mw3,mw4,mw236,mw5]),(12,10,0,mn1266,[mw6,mw7,mw237,mw3,mw4,mw5]),(12,10,0,mn1309,[mw6,mw7,mw237,mw231,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC58p : mcC58.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC59 : List MemoKey := [(12,10,0,mn1238,[mw6,mw7,mw3,mw4,mw5,mw238]),(12,10,0,mn1236,[mw6,mw7,mw239,mw3,mw4,mw5]),(12,10,0,mn1310,[mw6,mw7,mw239,mw231,mw3,mw4,mw5]),(12,10,0,mn1304,[mw230,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1307,[mw6,mw233,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1308,[mw6,mw7,mw2,mw235,mw3,mw4,mw5]),(12,10,0,mn1309,[mw6,mw7,mw2,mw237,mw3,mw4,mw5]),(12,10,0,mn1310,[mw6,mw7,mw2,mw239,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC59p : mcC59.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC60 : List MemoKey := [(12,10,0,mn1311,[mw6,mw2,mw3,mw4,mw5,mw240]),(12,10,0,mn1312,[mw6,mw2,mw3,mw4,mw5,mw241,mw240]),(12,10,0,mn1313,[mw242,mw6,mw2,mw3,mw4,mw5]),(12,10,0,mn1314,[mw242,mw6,mw2,mw3,mw4,mw5,mw241]),(12,10,0,mn1306,[mw6,mw2,mw3,mw4,mw5,mw243]),(12,10,0,mn1315,[mw6,mw2,mw3,mw4,mw5,mw241,mw243]),(12,10,0,mn1305,[mw6,mw244,mw2,mw3,mw4,mw5]),(12,10,0,mn1316,[mw6,mw244,mw2,mw3,mw4,mw5,mw241])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC60p : mcC60.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC61 : List MemoKey := [(12,10,0,mn1287,[mw6,mw2,mw3,mw4,mw5,mw245]),(12,10,0,mn1317,[mw6,mw2,mw3,mw4,mw5,mw241,mw245]),(12,10,0,mn1285,[mw6,mw2,mw246,mw3,mw4,mw5]),(12,10,0,mn1318,[mw6,mw2,mw246,mw3,mw4,mw5,mw241]),(12,10,0,mn1264,[mw6,mw2,mw3,mw4,mw5,mw247]),(12,10,0,mn1319,[mw6,mw2,mw3,mw4,mw5,mw241,mw247]),(12,10,0,mn1262,[mw6,mw2,mw3,mw248,mw4,mw5]),(12,10,0,mn1320,[mw6,mw2,mw3,mw248,mw4,mw5,mw241])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC61p : mcC61.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC62 : List MemoKey := [(12,10,0,mn1234,[mw6,mw2,mw3,mw4,mw5,mw249]),(12,10,0,mn1321,[mw6,mw2,mw3,mw4,mw5,mw241,mw249]),(12,10,0,mn1232,[mw6,mw2,mw3,mw4,mw250,mw5]),(12,10,0,mn1322,[mw6,mw2,mw3,mw4,mw250,mw5,mw241]),(12,10,0,mn1312,[mw6,mw7,mw2,mw3,mw4,mw5,mw240]),(12,10,0,mn1314,[mw242,mw6,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1315,[mw6,mw7,mw2,mw3,mw4,mw5,mw243]),(12,10,0,mn1316,[mw6,mw7,mw244,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC62p : mcC62.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC63 : List MemoKey := [(12,10,0,mn1317,[mw6,mw7,mw2,mw3,mw4,mw5,mw245]),(12,10,0,mn1318,[mw6,mw7,mw2,mw246,mw3,mw4,mw5]),(12,10,0,mn1319,[mw6,mw7,mw2,mw3,mw4,mw5,mw247]),(12,10,0,mn1320,[mw6,mw7,mw2,mw3,mw248,mw4,mw5]),(12,10,0,mn1321,[mw6,mw7,mw2,mw3,mw4,mw5,mw249]),(12,10,0,mn1322,[mw6,mw7,mw2,mw3,mw4,mw250,mw5]),(12,10,0,mn1313,[mw7,mw2,mw3,mw4,mw5,mw251]),(12,10,0,mn1323,[mw7,mw2,mw3,mw4,mw5,mw252,mw251])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC63p : mcC63.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC64 : List MemoKey := [(12,10,0,mn1311,[mw253,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1324,[mw253,mw7,mw2,mw3,mw4,mw5,mw252]),(12,10,0,mn1303,[mw7,mw2,mw3,mw4,mw5,mw254]),(12,10,0,mn1325,[mw7,mw2,mw3,mw4,mw5,mw252,mw254]),(12,10,0,mn1302,[mw7,mw255,mw2,mw3,mw4,mw5]),(12,10,0,mn1326,[mw7,mw255,mw2,mw3,mw4,mw5,mw252]),(12,10,0,mn1283,[mw7,mw2,mw3,mw4,mw5,mw256]),(12,10,0,mn1327,[mw7,mw2,mw3,mw4,mw5,mw252,mw256])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC64p : mcC64.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC65 : List MemoKey := [(12,10,0,mn1281,[mw7,mw2,mw257,mw3,mw4,mw5]),(12,10,0,mn1328,[mw7,mw2,mw257,mw3,mw4,mw5,mw252]),(12,10,0,mn1260,[mw7,mw2,mw3,mw4,mw5,mw258]),(12,10,0,mn1329,[mw7,mw2,mw3,mw4,mw5,mw252,mw258]),(12,10,0,mn1258,[mw7,mw2,mw3,mw259,mw4,mw5]),(12,10,0,mn1330,[mw7,mw2,mw3,mw259,mw4,mw5,mw252]),(12,10,0,mn1230,[mw7,mw2,mw3,mw4,mw5,mw260]),(12,10,0,mn1331,[mw7,mw2,mw3,mw4,mw5,mw252,mw260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC65p : mcC65.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC66 : List MemoKey := [(12,10,0,mn1228,[mw7,mw2,mw3,mw4,mw261,mw5]),(12,10,0,mn1332,[mw7,mw2,mw3,mw4,mw261,mw5,mw252]),(12,10,0,mn1323,[mw6,mw7,mw2,mw3,mw4,mw5,mw251]),(12,10,0,mn1324,[mw6,mw253,mw7,mw2,mw3,mw4,mw5]),(12,10,0,mn1325,[mw6,mw7,mw2,mw3,mw4,mw5,mw254]),(12,10,0,mn1326,[mw6,mw7,mw255,mw2,mw3,mw4,mw5]),(12,10,0,mn1327,[mw6,mw7,mw2,mw3,mw4,mw5,mw256]),(12,10,0,mn1328,[mw6,mw7,mw2,mw257,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC66p : mcC66.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def mcC67 : List MemoKey := [(12,10,0,mn1329,[mw6,mw7,mw2,mw3,mw4,mw5,mw258]),(12,10,0,mn1330,[mw6,mw7,mw2,mw3,mw259,mw4,mw5]),(12,10,0,mn1331,[mw6,mw7,mw2,mw3,mw4,mw5,mw260]),(12,10,0,mn1332,[mw6,mw7,mw2,mw3,mw4,mw261,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcC67p : mcC67.all (fun e => !(keyRun originalC e)) = true := by decide +kernel
def memoChunksC : List {xs : List MemoKey // xs.all (fun e => !(keyRun originalC e)) = true} := [⟨mcC0,mcC0p⟩,⟨mcC1,mcC1p⟩,⟨mcC2,mcC2p⟩,⟨mcC3,mcC3p⟩,⟨mcC4,mcC4p⟩,⟨mcC5,mcC5p⟩,⟨mcC6,mcC6p⟩,⟨mcC7,mcC7p⟩,⟨mcC8,mcC8p⟩,⟨mcC9,mcC9p⟩,⟨mcC10,mcC10p⟩,⟨mcC11,mcC11p⟩,⟨mcC12,mcC12p⟩,⟨mcC13,mcC13p⟩,⟨mcC14,mcC14p⟩,⟨mcC15,mcC15p⟩,⟨mcC16,mcC16p⟩,⟨mcC17,mcC17p⟩,⟨mcC18,mcC18p⟩,⟨mcC19,mcC19p⟩,⟨mcC20,mcC20p⟩,⟨mcC21,mcC21p⟩,⟨mcC22,mcC22p⟩,⟨mcC23,mcC23p⟩,⟨mcC24,mcC24p⟩,⟨mcC25,mcC25p⟩,⟨mcC26,mcC26p⟩,⟨mcC27,mcC27p⟩,⟨mcC28,mcC28p⟩,⟨mcC29,mcC29p⟩,⟨mcC30,mcC30p⟩,⟨mcC31,mcC31p⟩,⟨mcC32,mcC32p⟩,⟨mcC33,mcC33p⟩,⟨mcC34,mcC34p⟩,⟨mcC35,mcC35p⟩,⟨mcC36,mcC36p⟩,⟨mcC37,mcC37p⟩,⟨mcC38,mcC38p⟩,⟨mcC39,mcC39p⟩,⟨mcC40,mcC40p⟩,⟨mcC41,mcC41p⟩,⟨mcC42,mcC42p⟩,⟨mcC43,mcC43p⟩,⟨mcC44,mcC44p⟩,⟨mcC45,mcC45p⟩,⟨mcC46,mcC46p⟩,⟨mcC47,mcC47p⟩,⟨mcC48,mcC48p⟩,⟨mcC49,mcC49p⟩,⟨mcC50,mcC50p⟩,⟨mcC51,mcC51p⟩,⟨mcC52,mcC52p⟩,⟨mcC53,mcC53p⟩,⟨mcC54,mcC54p⟩,⟨mcC55,mcC55p⟩,⟨mcC56,mcC56p⟩,⟨mcC57,mcC57p⟩,⟨mcC58,mcC58p⟩,⟨mcC59,mcC59p⟩,⟨mcC60,mcC60p⟩,⟨mcC61,mcC61p⟩,⟨mcC62,mcC62p⟩,⟨mcC63,mcC63p⟩,⟨mcC64,mcC64p⟩,⟨mcC65,mcC65p⟩,⟨mcC66,mcC66p⟩,⟨mcC67,mcC67p⟩]
def memoKeysC : List MemoKey := (memoChunksC.map Subtype.val).flatten
lemma memoKeysC_sound : ∀ e ∈ memoKeysC, keyRun originalC e = false := checkedChunks_sound (keyRun originalC) memoChunksC
def mcS0 : List MemoKey := [(11,10,1,mn505,[mw0,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn506,[mw0,mw6,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn507,[mw0,mw7,mw1,mw2,mw3,mw4,mw5]),(11,10,1,mn508,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw8]),(11,10,1,mn509,[mw6,mw7,mw1,mw9,mw2,mw3,mw4,mw5]),(11,10,1,mn510,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn511,[mw6,mw7,mw1,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn512,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw12])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS0p : mcS0.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS1 : List MemoKey := [(11,10,1,mn513,[mw6,mw7,mw1,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn514,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn515,[mw6,mw7,mw1,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn516,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn517,[mw6,mw7,mw1,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn518,[mw6,mw7,mw1,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn519,[mw6,mw7,mw1,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn528,[mw0,mw7,mw2,mw28,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS1p : mcS1.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS2 : List MemoKey := [(11,10,1,mn529,[mw0,mw6,mw7,mw2,mw28,mw3,mw4,mw5]),(11,10,1,mn530,[mw0,mw6,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn531,[mw0,mw6,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn532,[mw0,mw31,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn533,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn534,[mw0,mw6,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn535,[mw0,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn536,[mw0,mw6,mw7,mw2,mw3,mw34,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS2p : mcS2.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS3 : List MemoKey := [(11,10,1,mn537,[mw0,mw6,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn538,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn539,[mw0,mw6,mw37,mw2,mw3,mw4,mw5]),(11,10,1,mn540,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw8]),(11,10,1,mn541,[mw0,mw6,mw7,mw9,mw2,mw3,mw4,mw5]),(11,10,1,mn542,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn543,[mw0,mw6,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn544,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw12])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS3p : mcS3.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS4 : List MemoKey := [(11,10,1,mn545,[mw0,mw6,mw7,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn546,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn547,[mw0,mw6,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn548,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn549,[mw0,mw6,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn550,[mw0,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn551,[mw0,mw6,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn564,[mw46,mw7,mw28,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS4p : mcS4.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS5 : List MemoKey := [(11,10,1,mn565,[mw46,mw6,mw7,mw28,mw3,mw4,mw5]),(11,10,1,mn566,[mw7,mw2,mw28,mw3,mw29,mw4,mw5]),(11,10,1,mn567,[mw47,mw6,mw7,mw2,mw28,mw3,mw4,mw5]),(11,10,1,mn568,[mw31,mw6,mw7,mw2,mw28,mw3,mw4,mw5]),(11,10,1,mn569,[mw48,mw6,mw7,mw2,mw28,mw3,mw4,mw5]),(11,10,1,mn570,[mw6,mw7,mw2,mw28,mw33,mw3,mw4,mw5]),(11,10,1,mn571,[mw6,mw7,mw2,mw28,mw3,mw34,mw4,mw5]),(11,10,1,mn572,[mw6,mw49,mw7,mw2,mw28,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS5p : mcS5.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS6 : List MemoKey := [(11,10,1,mn573,[mw6,mw7,mw2,mw28,mw3,mw4,mw35,mw5]),(11,10,1,mn574,[mw6,mw50,mw7,mw2,mw28,mw3,mw4,mw5]),(11,10,1,mn575,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw36]),(11,10,1,mn576,[mw6,mw37,mw7,mw2,mw28,mw3,mw4,mw5]),(11,10,1,mn577,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw8]),(11,10,1,mn578,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw10]),(11,10,1,mn579,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw12]),(11,10,1,mn580,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS6p : mcS6.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS7 : List MemoKey := [(11,10,1,mn581,[mw6,mw7,mw2,mw28,mw15,mw3,mw4,mw5]),(11,10,1,mn582,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw16]),(11,10,1,mn583,[mw6,mw7,mw2,mw28,mw17,mw3,mw4,mw5]),(11,10,1,mn584,[mw6,mw7,mw2,mw28,mw3,mw4,mw5,mw18]),(11,10,1,mn585,[mw6,mw7,mw2,mw28,mw3,mw19,mw4,mw5]),(11,10,1,mn598,[mw46,mw6,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn599,[mw46,mw6,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn600,[mw46,mw6,mw7,mw2,mw3,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS7p : mcS7.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS8 : List MemoKey := [(11,10,1,mn601,[mw46,mw6,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn602,[mw46,mw6,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn603,[mw46,mw6,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn604,[mw46,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn605,[mw46,mw6,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn606,[mw46,mw6,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn607,[mw46,mw6,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn608,[mw46,mw6,mw7,mw2,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS8p : mcS8.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS9 : List MemoKey := [(11,10,1,mn609,[mw46,mw6,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn614,[mw47,mw7,mw2,mw29,mw4,mw5]),(11,10,1,mn615,[mw47,mw6,mw7,mw2,mw29,mw4,mw5]),(11,10,1,mn616,[mw47,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn617,[mw47,mw6,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn618,[mw31,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn619,[mw31,mw6,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn620,[mw7,mw2,mw3,mw29,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS9p : mcS9.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS10 : List MemoKey := [(11,10,1,mn621,[mw48,mw6,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn622,[mw6,mw7,mw2,mw33,mw3,mw29,mw4,mw5]),(11,10,1,mn623,[mw6,mw62,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn624,[mw6,mw7,mw2,mw3,mw29,mw34,mw4,mw5]),(11,10,1,mn625,[mw6,mw49,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn626,[mw6,mw7,mw2,mw3,mw29,mw4,mw35,mw5]),(11,10,1,mn627,[mw6,mw50,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn628,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw36])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS10p : mcS10.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS11 : List MemoKey := [(11,10,1,mn629,[mw6,mw37,mw7,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn630,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw8]),(11,10,1,mn631,[mw6,mw7,mw9,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn632,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw10]),(11,10,1,mn633,[mw6,mw7,mw11,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn634,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw12]),(11,10,1,mn635,[mw6,mw7,mw13,mw2,mw3,mw29,mw4,mw5]),(11,10,1,mn636,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS11p : mcS11.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS12 : List MemoKey := [(11,10,1,mn637,[mw6,mw7,mw2,mw15,mw3,mw29,mw4,mw5]),(11,10,1,mn638,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw16]),(11,10,1,mn639,[mw6,mw7,mw2,mw17,mw3,mw29,mw4,mw5]),(11,10,1,mn640,[mw6,mw7,mw2,mw3,mw29,mw4,mw5,mw18]),(11,10,1,mn641,[mw6,mw7,mw2,mw3,mw29,mw19,mw4,mw5]),(11,10,1,mn654,[mw47,mw6,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn655,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn656,[mw47,mw6,mw7,mw2,mw33,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS12p : mcS12.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS13 : List MemoKey := [(11,10,1,mn657,[mw47,mw6,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn658,[mw47,mw6,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn659,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn660,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw8]),(11,10,1,mn661,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn662,[mw47,mw6,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn663,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw12]),(11,10,1,mn664,[mw47,mw6,mw7,mw13,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS13p : mcS13.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS14 : List MemoKey := [(11,10,1,mn665,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn666,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn667,[mw47,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn668,[mw47,mw6,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn680,[mw31,mw7,mw2,mw3,mw30,mw5]),(11,10,1,mn681,[mw31,mw6,mw7,mw2,mw3,mw30,mw5]),(11,10,1,mn682,[mw31,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn683,[mw31,mw6,mw7,mw2,mw3,mw4,mw30,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS14p : mcS14.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS15 : List MemoKey := [(11,10,1,mn684,[mw48,mw6,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn685,[mw6,mw7,mw2,mw33,mw3,mw4,mw30,mw5]),(11,10,1,mn686,[mw6,mw62,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn687,[mw6,mw7,mw2,mw3,mw34,mw4,mw30,mw5]),(11,10,1,mn688,[mw6,mw49,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn689,[mw6,mw50,mw7,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn690,[mw6,mw7,mw2,mw3,mw4,mw30,mw5,mw36]),(11,10,1,mn691,[mw6,mw37,mw7,mw2,mw3,mw4,mw30,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS15p : mcS15.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS16 : List MemoKey := [(11,10,1,mn692,[mw6,mw7,mw2,mw3,mw4,mw30,mw5,mw8]),(11,10,1,mn693,[mw6,mw7,mw9,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn694,[mw6,mw7,mw11,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn695,[mw6,mw7,mw2,mw3,mw4,mw30,mw5,mw12]),(11,10,1,mn696,[mw6,mw7,mw13,mw2,mw3,mw4,mw30,mw5]),(11,10,1,mn697,[mw6,mw7,mw2,mw15,mw3,mw4,mw30,mw5]),(11,10,1,mn698,[mw6,mw7,mw2,mw3,mw4,mw30,mw5,mw16]),(11,10,1,mn699,[mw6,mw7,mw2,mw17,mw3,mw4,mw30,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS16p : mcS16.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS17 : List MemoKey := [(11,10,1,mn700,[mw6,mw7,mw2,mw3,mw19,mw4,mw30,mw5]),(11,10,1,mn713,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn714,[mw48,mw31,mw7,mw2,mw3,mw4,mw5]),(11,10,1,mn715,[mw31,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn716,[mw31,mw6,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn717,[mw31,mw6,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn718,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn719,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw8])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS17p : mcS17.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS18 : List MemoKey := [(11,10,1,mn720,[mw31,mw6,mw7,mw9,mw2,mw3,mw4,mw5]),(11,10,1,mn721,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn722,[mw31,mw6,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn723,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw12]),(11,10,1,mn724,[mw31,mw6,mw7,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn725,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn726,[mw31,mw6,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn727,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS18p : mcS18.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS19 : List MemoKey := [(11,10,1,mn728,[mw31,mw6,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn729,[mw31,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn730,[mw31,mw6,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn742,[mw48,mw7,mw2,mw3,mw4,mw32]),(11,10,1,mn743,[mw48,mw6,mw7,mw2,mw3,mw4,mw32]),(11,10,1,mn744,[mw48,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn745,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn746,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw32])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS19p : mcS19.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS20 : List MemoKey := [(11,10,1,mn747,[mw6,mw62,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn748,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw32]),(11,10,1,mn749,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn750,[mw6,mw7,mw2,mw3,mw4,mw35,mw5,mw32]),(11,10,1,mn751,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn752,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw36]),(11,10,1,mn753,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn754,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw8])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS20p : mcS20.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS21 : List MemoKey := [(11,10,1,mn755,[mw6,mw7,mw9,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn756,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw10]),(11,10,1,mn757,[mw6,mw7,mw11,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn758,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw12]),(11,10,1,mn759,[mw6,mw7,mw13,mw2,mw3,mw4,mw5,mw32]),(11,10,1,mn760,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw14]),(11,10,1,mn761,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw32]),(11,10,1,mn762,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS21p : mcS21.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS22 : List MemoKey := [(11,10,1,mn763,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw32]),(11,10,1,mn764,[mw6,mw7,mw2,mw3,mw4,mw5,mw32,mw18]),(11,10,1,mn765,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw32]),(11,10,1,mn780,[mw48,mw6,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn781,[mw48,mw6,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn782,[mw48,mw6,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn783,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn784,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw8])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS22p : mcS22.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS23 : List MemoKey := [(11,10,1,mn785,[mw48,mw6,mw7,mw9,mw2,mw3,mw4,mw5]),(11,10,1,mn786,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn787,[mw48,mw6,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn788,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw12]),(11,10,1,mn789,[mw48,mw6,mw7,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn790,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn791,[mw48,mw6,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn792,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS23p : mcS23.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS24 : List MemoKey := [(11,10,1,mn793,[mw48,mw6,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn794,[mw48,mw6,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn795,[mw48,mw6,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn807,[mw6,mw62,mw33,mw3,mw4,mw5]),(11,10,1,mn808,[mw6,mw62,mw7,mw33,mw3,mw4,mw5]),(11,10,1,mn809,[mw6,mw2,mw33,mw3,mw34,mw4,mw5]),(11,10,1,mn810,[mw6,mw49,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn811,[mw6,mw50,mw7,mw2,mw33,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS24p : mcS24.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS25 : List MemoKey := [(11,10,1,mn812,[mw6,mw37,mw7,mw2,mw33,mw3,mw4,mw5]),(11,10,1,mn813,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw8]),(11,10,1,mn814,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw10]),(11,10,1,mn815,[mw6,mw7,mw11,mw33,mw3,mw4,mw5]),(11,10,1,mn816,[mw6,mw7,mw33,mw3,mw4,mw5,mw12]),(11,10,1,mn817,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw12]),(11,10,1,mn818,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw14]),(11,10,1,mn819,[mw6,mw7,mw2,mw33,mw15,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS25p : mcS25.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS26 : List MemoKey := [(11,10,1,mn820,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw16]),(11,10,1,mn821,[mw6,mw7,mw2,mw33,mw17,mw3,mw4,mw5]),(11,10,1,mn822,[mw6,mw7,mw2,mw33,mw3,mw4,mw5,mw18]),(11,10,1,mn823,[mw6,mw7,mw2,mw33,mw3,mw19,mw4,mw5]),(11,10,1,mn836,[mw6,mw62,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn837,[mw6,mw62,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn838,[mw6,mw62,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn839,[mw6,mw62,mw37,mw2,mw3,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS26p : mcS26.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS27 : List MemoKey := [(11,10,1,mn840,[mw6,mw62,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn841,[mw6,mw62,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn842,[mw6,mw62,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn843,[mw6,mw62,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn844,[mw6,mw62,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn845,[mw6,mw62,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn850,[mw6,mw49,mw2,mw34,mw4,mw5]),(11,10,1,mn851,[mw6,mw49,mw7,mw2,mw34,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS27p : mcS27.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS28 : List MemoKey := [(11,10,1,mn852,[mw6,mw49,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn853,[mw6,mw49,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn854,[mw6,mw2,mw3,mw34,mw4,mw35,mw5]),(11,10,1,mn855,[mw6,mw50,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn856,[mw6,mw37,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn857,[mw6,mw37,mw7,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn858,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw8]),(11,10,1,mn859,[mw6,mw7,mw9,mw2,mw3,mw34,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS28p : mcS28.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS29 : List MemoKey := [(11,10,1,mn860,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw10]),(11,10,1,mn861,[mw6,mw7,mw11,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn862,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw12]),(11,10,1,mn863,[mw6,mw7,mw13,mw2,mw3,mw34,mw4,mw5]),(11,10,1,mn864,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw14]),(11,10,1,mn865,[mw6,mw7,mw2,mw15,mw3,mw34,mw4,mw5]),(11,10,1,mn866,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw16]),(11,10,1,mn867,[mw6,mw7,mw2,mw17,mw3,mw34,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS29p : mcS29.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS30 : List MemoKey := [(11,10,1,mn868,[mw6,mw7,mw2,mw3,mw34,mw4,mw5,mw18]),(11,10,1,mn869,[mw6,mw7,mw2,mw3,mw34,mw19,mw4,mw5]),(11,10,1,mn882,[mw6,mw49,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn883,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn884,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw8]),(11,10,1,mn885,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn886,[mw6,mw49,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn887,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw12])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS30p : mcS30.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS31 : List MemoKey := [(11,10,1,mn888,[mw6,mw49,mw7,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn889,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn890,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn891,[mw6,mw49,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn892,[mw6,mw49,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn904,[mw6,mw50,mw2,mw3,mw35,mw5]),(11,10,1,mn905,[mw6,mw50,mw7,mw2,mw3,mw35,mw5]),(11,10,1,mn906,[mw6,mw50,mw2,mw3,mw4,mw35,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS31p : mcS31.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS32 : List MemoKey := [(11,10,1,mn907,[mw6,mw50,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn908,[mw6,mw37,mw7,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn909,[mw6,mw7,mw2,mw3,mw4,mw35,mw5,mw8]),(11,10,1,mn910,[mw6,mw7,mw9,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn911,[mw6,mw7,mw11,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn912,[mw6,mw7,mw2,mw3,mw4,mw35,mw5,mw12]),(11,10,1,mn913,[mw6,mw7,mw13,mw2,mw3,mw4,mw35,mw5]),(11,10,1,mn914,[mw6,mw7,mw2,mw15,mw3,mw4,mw35,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS32p : mcS32.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS33 : List MemoKey := [(11,10,1,mn915,[mw6,mw7,mw2,mw3,mw4,mw35,mw5,mw16]),(11,10,1,mn916,[mw6,mw7,mw2,mw17,mw3,mw4,mw35,mw5]),(11,10,1,mn917,[mw6,mw7,mw2,mw3,mw19,mw4,mw35,mw5]),(11,10,1,mn932,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn933,[mw6,mw50,mw37,mw2,mw3,mw4,mw5]),(11,10,1,mn934,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw8]),(11,10,1,mn935,[mw6,mw50,mw7,mw9,mw2,mw3,mw4,mw5]),(11,10,1,mn936,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw10])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS33p : mcS33.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS34 : List MemoKey := [(11,10,1,mn937,[mw6,mw50,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn938,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw12]),(11,10,1,mn939,[mw6,mw50,mw7,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn940,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn941,[mw6,mw50,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn942,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn943,[mw6,mw50,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn944,[mw6,mw50,mw7,mw2,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS34p : mcS34.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS35 : List MemoKey := [(11,10,1,mn945,[mw6,mw50,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn957,[mw6,mw37,mw2,mw3,mw4,mw36]),(11,10,1,mn958,[mw6,mw37,mw7,mw2,mw3,mw4,mw36]),(11,10,1,mn959,[mw6,mw37,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn960,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn961,[mw6,mw7,mw2,mw3,mw4,mw5,mw36,mw8]),(11,10,1,mn962,[mw6,mw7,mw9,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn963,[mw6,mw7,mw2,mw3,mw4,mw5,mw36,mw10])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS35p : mcS35.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS36 : List MemoKey := [(11,10,1,mn964,[mw6,mw7,mw11,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn965,[mw6,mw7,mw2,mw3,mw4,mw5,mw36,mw12]),(11,10,1,mn966,[mw6,mw7,mw13,mw2,mw3,mw4,mw5,mw36]),(11,10,1,mn967,[mw6,mw7,mw2,mw3,mw4,mw5,mw36,mw14]),(11,10,1,mn968,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw36]),(11,10,1,mn969,[mw6,mw7,mw2,mw3,mw4,mw5,mw36,mw16]),(11,10,1,mn970,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw36]),(11,10,1,mn971,[mw6,mw7,mw2,mw3,mw4,mw5,mw36,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS36p : mcS36.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS37 : List MemoKey := [(11,10,1,mn972,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw36]),(11,10,1,mn985,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw8]),(11,10,1,mn986,[mw6,mw37,mw7,mw9,mw2,mw3,mw4,mw5]),(11,10,1,mn987,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw10]),(11,10,1,mn988,[mw6,mw37,mw7,mw11,mw2,mw3,mw4,mw5]),(11,10,1,mn989,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw12]),(11,10,1,mn990,[mw6,mw37,mw7,mw13,mw2,mw3,mw4,mw5]),(11,10,1,mn991,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS37p : mcS37.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS38 : List MemoKey := [(11,10,1,mn992,[mw6,mw37,mw7,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn993,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn994,[mw6,mw37,mw7,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn995,[mw6,mw37,mw7,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn996,[mw6,mw37,mw7,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn1010,[mw6,mw7,mw9,mw4,mw5,mw8]),(11,10,1,mn1011,[mw6,mw7,mw9,mw3,mw4,mw5,mw8]),(11,10,1,mn1012,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw10])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS38p : mcS38.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS39 : List MemoKey := [(11,10,1,mn1013,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw12]),(11,10,1,mn1014,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw14]),(11,10,1,mn1015,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw8]),(11,10,1,mn1016,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw16]),(11,10,1,mn1017,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw8]),(11,10,1,mn1018,[mw6,mw7,mw2,mw3,mw4,mw5,mw8,mw18]),(11,10,1,mn1019,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw8]),(11,10,1,mn1036,[mw6,mw7,mw9,mw2,mw3,mw4,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS39p : mcS39.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS40 : List MemoKey := [(11,10,1,mn1037,[mw6,mw7,mw9,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn1038,[mw6,mw7,mw9,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn1039,[mw6,mw7,mw9,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn1046,[mw6,mw7,mw11,mw3,mw5,mw10]),(11,10,1,mn1047,[mw6,mw7,mw11,mw3,mw4,mw5,mw10]),(11,10,1,mn1048,[mw6,mw7,mw2,mw3,mw4,mw5,mw10,mw12]),(11,10,1,mn1049,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw10]),(11,10,1,mn1050,[mw6,mw7,mw2,mw3,mw4,mw5,mw10,mw16])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS40p : mcS40.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS41 : List MemoKey := [(11,10,1,mn1051,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw10]),(11,10,1,mn1052,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw10]),(11,10,1,mn1065,[mw6,mw7,mw11,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn1066,[mw6,mw7,mw11,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn1067,[mw6,mw7,mw11,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn1068,[mw6,mw7,mw11,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn1069,[mw6,mw7,mw11,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn1070,[mw6,mw7,mw11,mw2,mw3,mw19,mw4,mw5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS41p : mcS41.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS42 : List MemoKey := [(11,10,1,mn1075,[mw6,mw7,mw13,mw3,mw4,mw12]),(11,10,1,mn1076,[mw6,mw7,mw13,mw3,mw4,mw5,mw12]),(11,10,1,mn1077,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw14]),(11,10,1,mn1078,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw12]),(11,10,1,mn1079,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw16]),(11,10,1,mn1080,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw12]),(11,10,1,mn1081,[mw6,mw7,mw2,mw3,mw4,mw5,mw12,mw18]),(11,10,1,mn1082,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw12])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS42p : mcS42.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS43 : List MemoKey := [(11,10,1,mn1101,[mw6,mw7,mw13,mw2,mw3,mw4,mw5,mw14]),(11,10,1,mn1102,[mw6,mw7,mw13,mw2,mw15,mw3,mw4,mw5]),(11,10,1,mn1103,[mw6,mw7,mw13,mw2,mw3,mw4,mw5,mw16]),(11,10,1,mn1104,[mw6,mw7,mw13,mw2,mw17,mw3,mw4,mw5]),(11,10,1,mn1105,[mw6,mw7,mw13,mw2,mw3,mw4,mw5,mw18]),(11,10,1,mn1106,[mw6,mw7,mw13,mw2,mw3,mw19,mw4,mw5]),(11,10,1,mn1111,[mw6,mw7,mw2,mw15,mw5,mw14]),(11,10,1,mn1112,[mw6,mw7,mw2,mw15,mw3,mw5,mw14])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS43p : mcS43.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS44 : List MemoKey := [(11,10,1,mn1113,[mw6,mw7,mw2,mw15,mw4,mw5,mw14]),(11,10,1,mn1114,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw14]),(11,10,1,mn1115,[mw6,mw7,mw2,mw3,mw4,mw5,mw14,mw16]),(11,10,1,mn1116,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw14]),(11,10,1,mn1117,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw14]),(11,10,1,mn1132,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw16]),(11,10,1,mn1133,[mw6,mw7,mw2,mw15,mw17,mw4,mw5]),(11,10,1,mn1134,[mw6,mw7,mw2,mw15,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS44p : mcS44.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS45 : List MemoKey := [(11,10,1,mn1135,[mw6,mw7,mw2,mw15,mw3,mw19,mw4,mw5]),(11,10,1,mn1150,[mw6,mw7,mw2,mw17,mw4,mw16]),(11,10,1,mn1151,[mw6,mw7,mw2,mw17,mw3,mw4,mw16]),(11,10,1,mn1152,[mw6,mw7,mw2,mw17,mw4,mw5,mw16]),(11,10,1,mn1153,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw16]),(11,10,1,mn1154,[mw6,mw7,mw2,mw3,mw4,mw5,mw16,mw18]),(11,10,1,mn1155,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw16]),(11,10,1,mn1172,[mw6,mw7,mw2,mw17,mw3,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS45p : mcS45.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def mcS46 : List MemoKey := [(11,10,1,mn1173,[mw6,mw7,mw2,mw17,mw3,mw19,mw4,mw5]),(11,10,1,mn1188,[mw6,mw7,mw2,mw3,mw19,mw18]),(11,10,1,mn1189,[mw6,mw7,mw2,mw3,mw19,mw4,mw18]),(11,10,1,mn1190,[mw6,mw7,mw2,mw3,mw19,mw5,mw18]),(11,10,1,mn1191,[mw6,mw7,mw2,mw3,mw19,mw4,mw5,mw18])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def mcS46p : mcS46.all (fun e => !(keyRun originalS e)) = true := by decide +kernel
def memoChunksS : List {xs : List MemoKey // xs.all (fun e => !(keyRun originalS e)) = true} := [⟨mcS0,mcS0p⟩,⟨mcS1,mcS1p⟩,⟨mcS2,mcS2p⟩,⟨mcS3,mcS3p⟩,⟨mcS4,mcS4p⟩,⟨mcS5,mcS5p⟩,⟨mcS6,mcS6p⟩,⟨mcS7,mcS7p⟩,⟨mcS8,mcS8p⟩,⟨mcS9,mcS9p⟩,⟨mcS10,mcS10p⟩,⟨mcS11,mcS11p⟩,⟨mcS12,mcS12p⟩,⟨mcS13,mcS13p⟩,⟨mcS14,mcS14p⟩,⟨mcS15,mcS15p⟩,⟨mcS16,mcS16p⟩,⟨mcS17,mcS17p⟩,⟨mcS18,mcS18p⟩,⟨mcS19,mcS19p⟩,⟨mcS20,mcS20p⟩,⟨mcS21,mcS21p⟩,⟨mcS22,mcS22p⟩,⟨mcS23,mcS23p⟩,⟨mcS24,mcS24p⟩,⟨mcS25,mcS25p⟩,⟨mcS26,mcS26p⟩,⟨mcS27,mcS27p⟩,⟨mcS28,mcS28p⟩,⟨mcS29,mcS29p⟩,⟨mcS30,mcS30p⟩,⟨mcS31,mcS31p⟩,⟨mcS32,mcS32p⟩,⟨mcS33,mcS33p⟩,⟨mcS34,mcS34p⟩,⟨mcS35,mcS35p⟩,⟨mcS36,mcS36p⟩,⟨mcS37,mcS37p⟩,⟨mcS38,mcS38p⟩,⟨mcS39,mcS39p⟩,⟨mcS40,mcS40p⟩,⟨mcS41,mcS41p⟩,⟨mcS42,mcS42p⟩,⟨mcS43,mcS43p⟩,⟨mcS44,mcS44p⟩,⟨mcS45,mcS45p⟩,⟨mcS46,mcS46p⟩]
def memoKeysS : List MemoKey := (memoChunksS.map Subtype.val).flatten
lemma memoKeysS_sound : ∀ e ∈ memoKeysS, keyRun originalS e = false := checkedChunks_sound (keyRun originalS) memoChunksS
end memo_data

noncomputable section memo_bridge
def memoTop (keysC keysS : List MemoKey) (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvC NN AA HX HY (memoLookC NN AA HX HY l m g keysC K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodeC NN (memoLookS NN AA HX HY l m g K keysC keysS K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def memoStart (keysC keysS : List MemoKey) (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => memoTop keysC keysS NN AA HX HY l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
def memoChk (keysC keysS : List MemoKey) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => memoStart keysC keysS nn aa hx hy l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma memoTop_eq (keysC keysS : List MemoKey) (NN AA HX HY l m g K H ph k t z : Nat) (v : List W)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoTop keysC keysS NN AA HX HY l m g K H ph k t z v = topCC NN AA HX HY l m g K H ph k t z v := by
  unfold memoTop topCC
  rw [memoLookC_eq NN AA HX HY l m g keysC hC, memoLookS_eq NN AA HX HY l m g K keysC keysS hC hS]
lemma memoStart_eq (keysC keysS : List MemoKey) (NN AA HX HY l m g B K t p H ph : Nat) (v : List W)
    (hC : ∀ e ∈ keysC, keyRun (lookC NN AA HX HY l m g) e = false)
    (hS : ∀ e ∈ keysS, keyRun (look1C NN AA HX HY l m g K) e = false) :
    memoStart keysC keysS NN AA HX HY l m g B K t p H ph v = startvC NN AA HX HY l m g B K t p H ph v := by
  simp only [memoStart,startvC,memoTop_eq keysC keysS NN AA HX HY l m g K _ _ _ _ _ _ hC hS]
lemma memoChk_eq (H ph : Nat) :
    memoChk memoKeysC memoKeysS [] rt 0 12 1 H ph = chk [] rt 0 12 1 H ph := by
  unfold memoChk chk
  simp only [st_eq]
  simp only [memoStart_eq memoKeysC memoKeysS I.NN I.AA I.HX I.HY (lz 0) (mz 0)
    (pL (rt.map (fun _ => 16))) _ 12 _ _ _ _ _ memoKeysC_sound memoKeysS_sound]
end memo_bridge

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_p : pOk 0 rt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_0 : chk [] rt 0 11 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_1 : chk [] rt 0 11 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_2 : chk [] rt 0 11 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_3 : chk [] rt 0 11 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_4 : chk [] rt 0 11 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_5 : chk [] rt 0 11 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_6 : chk [] rt 0 11 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_7 : chk [] rt 0 11 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_8 : chk [] rt 0 11 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_9 : chk [] rt 0 11 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_10 : chk [] rt 0 11 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def root_11 : chk [] rt 0 11 11 FF 1 = false := by decide +kernel
lemma iroot : Imp [] 0 12 := imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by
  interval_cases t
  · exact one root_0
  · exact one root_1
  · exact one root_2
  · exact one root_3
  · exact one root_4
  · exact one root_5
  · exact one root_6
  · exact one root_7
  · exact one root_8
  · exact one root_9
  · exact one root_10
  · exact one root_11)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_0 : chk [] rt 0 12 1 (0) 1 = false := (memoChk_eq (0) 1).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_1 : chk [] rt 0 12 1 (memoCell 4 0) 0 = false := (memoChk_eq (memoCell 4 0) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_2 : chk [] rt 0 12 1 (memoCell 4 4) 0 = false := (memoChk_eq (memoCell 4 4) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_3 : chk [] rt 0 12 1 (memoCell 4 8) 0 = false := (memoChk_eq (memoCell 4 8) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_4 : chk [] rt 0 12 1 (memoCell 4 12) 0 = false := (memoChk_eq (memoCell 4 12) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_5 : chk [] rt 0 12 1 (memoCell 4 16) 0 = false := (memoChk_eq (memoCell 4 16) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_6 : chk [] rt 0 12 1 (memoCell 4 20) 0 = false := (memoChk_eq (memoCell 4 20) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_7 : chk [] rt 0 12 1 (memoCell 4 24) 0 = false := (memoChk_eq (memoCell 4 24) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_8 : chk [] rt 0 12 1 (memoCell 4 28) 0 = false := (memoChk_eq (memoCell 4 28) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_9 : chk [] rt 0 12 1 (memoCell 4 32) 0 = false := (memoChk_eq (memoCell 4 32) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_10 : chk [] rt 0 12 1 (memoCell 4 36) 0 = false := (memoChk_eq (memoCell 4 36) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_11 : chk [] rt 0 12 1 (memoCell 4 40) 0 = false := (memoChk_eq (memoCell 4 40) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_12 : chk [] rt 0 12 1 (memoCell 4 44) 0 = false := (memoChk_eq (memoCell 4 44) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_13 : chk [] rt 0 12 1 (memoCell 4 48) 0 = false := (memoChk_eq (memoCell 4 48) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_14 : chk [] rt 0 12 1 (memoCell 4 52) 0 = false := (memoChk_eq (memoCell 4 52) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_15 : chk [] rt 0 12 1 (memoCell 4 56) 0 = false := (memoChk_eq (memoCell 4 56) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_16 : chk [] rt 0 12 1 (memoCell 4 60) 0 = false := (memoChk_eq (memoCell 4 60) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_17 : chk [] rt 0 12 1 (memoCell 4 64) 0 = false := (memoChk_eq (memoCell 4 64) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_18 : chk [] rt 0 12 1 (memoCell 4 68) 0 = false := (memoChk_eq (memoCell 4 68) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_19 : chk [] rt 0 12 1 (memoCell 4 72) 0 = false := (memoChk_eq (memoCell 4 72) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_20 : chk [] rt 0 12 1 (memoCell 4 76) 0 = false := (memoChk_eq (memoCell 4 76) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_21 : chk [] rt 0 12 1 (memoCell 4 80) 0 = false := (memoChk_eq (memoCell 4 80) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_22 : chk [] rt 0 12 1 (memoCell 4 84) 0 = false := (memoChk_eq (memoCell 4 84) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_23 : chk [] rt 0 12 1 (memoCell 4 88) 0 = false := (memoChk_eq (memoCell 4 88) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_24 : chk [] rt 0 12 1 (memoCell 4 92) 0 = false := (memoChk_eq (memoCell 4 92) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_25 : chk [] rt 0 12 1 (memoCell 4 96) 0 = false := (memoChk_eq (memoCell 4 96) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_26 : chk [] rt 0 12 1 (memoCell 4 100) 0 = false := (memoChk_eq (memoCell 4 100) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_27 : chk [] rt 0 12 1 (memoCell 4 104) 0 = false := (memoChk_eq (memoCell 4 104) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_28 : chk [] rt 0 12 1 (memoCell 4 108) 0 = false := (memoChk_eq (memoCell 4 108) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_29 : chk [] rt 0 12 1 (memoCell 4 112) 0 = false := (memoChk_eq (memoCell 4 112) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_30 : chk [] rt 0 12 1 (memoCell 4 116) 0 = false := (memoChk_eq (memoCell 4 116) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_31 : chk [] rt 0 12 1 (memoCell 4 120) 0 = false := (memoChk_eq (memoCell 4 120) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_32 : chk [] rt 0 12 1 (memoCell 4 124) 0 = false := (memoChk_eq (memoCell 4 124) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_33 : chk [] rt 0 12 1 (memoCell 4 128) 0 = false := (memoChk_eq (memoCell 4 128) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_34 : chk [] rt 0 12 1 (memoCell 4 132) 0 = false := (memoChk_eq (memoCell 4 132) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_35 : chk [] rt 0 12 1 (memoCell 4 136) 0 = false := (memoChk_eq (memoCell 4 136) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_36 : chk [] rt 0 12 1 (memoCell 4 140) 0 = false := (memoChk_eq (memoCell 4 140) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_37 : chk [] rt 0 12 1 (memoCell 4 144) 0 = false := (memoChk_eq (memoCell 4 144) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_38 : chk [] rt 0 12 1 (memoCell 4 148) 0 = false := (memoChk_eq (memoCell 4 148) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_39 : chk [] rt 0 12 1 (memoCell 4 152) 0 = false := (memoChk_eq (memoCell 4 152) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_40 : chk [] rt 0 12 1 (memoCell 4 156) 0 = false := (memoChk_eq (memoCell 4 156) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_41 : chk [] rt 0 12 1 (memoCell 4 160) 0 = false := (memoChk_eq (memoCell 4 160) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_42 : chk [] rt 0 12 1 (memoCell 4 164) 0 = false := (memoChk_eq (memoCell 4 164) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_43 : chk [] rt 0 12 1 (memoCell 4 168) 0 = false := (memoChk_eq (memoCell 4 168) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_44 : chk [] rt 0 12 1 (memoCell 4 172) 0 = false := (memoChk_eq (memoCell 4 172) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_45 : chk [] rt 0 12 1 (memoCell 4 176) 0 = false := (memoChk_eq (memoCell 4 176) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_46 : chk [] rt 0 12 1 (memoCell 4 180) 0 = false := (memoChk_eq (memoCell 4 180) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_47 : chk [] rt 0 12 1 (memoCell 4 184) 0 = false := (memoChk_eq (memoCell 4 184) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_48 : chk [] rt 0 12 1 (memoCell 4 188) 0 = false := (memoChk_eq (memoCell 4 188) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_49 : chk [] rt 0 12 1 (memoCell 4 192) 0 = false := (memoChk_eq (memoCell 4 192) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_50 : chk [] rt 0 12 1 (memoCell 4 196) 0 = false := (memoChk_eq (memoCell 4 196) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_51 : chk [] rt 0 12 1 (memoCell 4 200) 0 = false := (memoChk_eq (memoCell 4 200) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_52 : chk [] rt 0 12 1 (memoCell 4 204) 0 = false := (memoChk_eq (memoCell 4 204) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_53 : chk [] rt 0 12 1 (memoCell 4 208) 0 = false := (memoChk_eq (memoCell 4 208) 0).symm.trans (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Proof_54 : chk [] rt 0 12 1 (memoCell 4 212) 0 = false := (memoChk_eq (memoCell 4 212) 0).symm.trans (by decide +kernel)
def cacheR1Checked : List {p : ℕ × ℕ // chk [] rt 0 12 1 p.1 p.2 = false} := [⟨((0), 1), cacheR1Proof_0⟩, ⟨((memoCell 4 0), 0), cacheR1Proof_1⟩, ⟨((memoCell 4 4), 0), cacheR1Proof_2⟩, ⟨((memoCell 4 8), 0), cacheR1Proof_3⟩, ⟨((memoCell 4 12), 0), cacheR1Proof_4⟩, ⟨((memoCell 4 16), 0), cacheR1Proof_5⟩, ⟨((memoCell 4 20), 0), cacheR1Proof_6⟩, ⟨((memoCell 4 24), 0), cacheR1Proof_7⟩, ⟨((memoCell 4 28), 0), cacheR1Proof_8⟩, ⟨((memoCell 4 32), 0), cacheR1Proof_9⟩, ⟨((memoCell 4 36), 0), cacheR1Proof_10⟩, ⟨((memoCell 4 40), 0), cacheR1Proof_11⟩, ⟨((memoCell 4 44), 0), cacheR1Proof_12⟩, ⟨((memoCell 4 48), 0), cacheR1Proof_13⟩, ⟨((memoCell 4 52), 0), cacheR1Proof_14⟩, ⟨((memoCell 4 56), 0), cacheR1Proof_15⟩, ⟨((memoCell 4 60), 0), cacheR1Proof_16⟩, ⟨((memoCell 4 64), 0), cacheR1Proof_17⟩, ⟨((memoCell 4 68), 0), cacheR1Proof_18⟩, ⟨((memoCell 4 72), 0), cacheR1Proof_19⟩, ⟨((memoCell 4 76), 0), cacheR1Proof_20⟩, ⟨((memoCell 4 80), 0), cacheR1Proof_21⟩, ⟨((memoCell 4 84), 0), cacheR1Proof_22⟩, ⟨((memoCell 4 88), 0), cacheR1Proof_23⟩, ⟨((memoCell 4 92), 0), cacheR1Proof_24⟩, ⟨((memoCell 4 96), 0), cacheR1Proof_25⟩, ⟨((memoCell 4 100), 0), cacheR1Proof_26⟩, ⟨((memoCell 4 104), 0), cacheR1Proof_27⟩, ⟨((memoCell 4 108), 0), cacheR1Proof_28⟩, ⟨((memoCell 4 112), 0), cacheR1Proof_29⟩, ⟨((memoCell 4 116), 0), cacheR1Proof_30⟩, ⟨((memoCell 4 120), 0), cacheR1Proof_31⟩, ⟨((memoCell 4 124), 0), cacheR1Proof_32⟩, ⟨((memoCell 4 128), 0), cacheR1Proof_33⟩, ⟨((memoCell 4 132), 0), cacheR1Proof_34⟩, ⟨((memoCell 4 136), 0), cacheR1Proof_35⟩, ⟨((memoCell 4 140), 0), cacheR1Proof_36⟩, ⟨((memoCell 4 144), 0), cacheR1Proof_37⟩, ⟨((memoCell 4 148), 0), cacheR1Proof_38⟩, ⟨((memoCell 4 152), 0), cacheR1Proof_39⟩, ⟨((memoCell 4 156), 0), cacheR1Proof_40⟩, ⟨((memoCell 4 160), 0), cacheR1Proof_41⟩, ⟨((memoCell 4 164), 0), cacheR1Proof_42⟩, ⟨((memoCell 4 168), 0), cacheR1Proof_43⟩, ⟨((memoCell 4 172), 0), cacheR1Proof_44⟩, ⟨((memoCell 4 176), 0), cacheR1Proof_45⟩, ⟨((memoCell 4 180), 0), cacheR1Proof_46⟩, ⟨((memoCell 4 184), 0), cacheR1Proof_47⟩, ⟨((memoCell 4 188), 0), cacheR1Proof_48⟩, ⟨((memoCell 4 192), 0), cacheR1Proof_49⟩, ⟨((memoCell 4 196), 0), cacheR1Proof_50⟩, ⟨((memoCell 4 200), 0), cacheR1Proof_51⟩, ⟨((memoCell 4 204), 0), cacheR1Proof_52⟩, ⟨((memoCell 4 208), 0), cacheR1Proof_53⟩, ⟨((memoCell 4 212), 0), cacheR1Proof_54⟩]
def cacheR1Parts : List (ℕ × ℕ) := cacheR1Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR1Full : mFull cacheR1Parts = true := by decide +kernel
def cacheR1One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 1 p.1 p.2 = false := by
  refine ⟨cacheR1Parts, cacheR1Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_0 : chk [] rt 0 12 2 (0) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_1 : chk [] rt 0 12 2 (memoCell 4 0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_2 : chk [] rt 0 12 2 (memoCell 4 4) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_3 : chk [] rt 0 12 2 (memoCell 4 8) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_4 : chk [] rt 0 12 2 (memoCell 4 12) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_5 : chk [] rt 0 12 2 (memoCell 4 16) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_6 : chk [] rt 0 12 2 (memoCell 4 20) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_7 : chk [] rt 0 12 2 (memoCell 4 24) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_8 : chk [] rt 0 12 2 (memoCell 4 28) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_9 : chk [] rt 0 12 2 (memoCell 4 32) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_10 : chk [] rt 0 12 2 (memoCell 4 36) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_11 : chk [] rt 0 12 2 (memoCell 4 40) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_12 : chk [] rt 0 12 2 (memoCell 4 44) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_13 : chk [] rt 0 12 2 (memoCell 4 48) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_14 : chk [] rt 0 12 2 (memoCell 4 52) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_15 : chk [] rt 0 12 2 (memoCell 4 56) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_16 : chk [] rt 0 12 2 (memoCell 4 60) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_17 : chk [] rt 0 12 2 (memoCell 4 64) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_18 : chk [] rt 0 12 2 (memoCell 4 68) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_19 : chk [] rt 0 12 2 (memoCell 4 72) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_20 : chk [] rt 0 12 2 (memoCell 4 76) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_21 : chk [] rt 0 12 2 (memoCell 4 80) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_22 : chk [] rt 0 12 2 (memoCell 4 84) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_23 : chk [] rt 0 12 2 (memoCell 4 88) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_24 : chk [] rt 0 12 2 (memoCell 4 92) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_25 : chk [] rt 0 12 2 (memoCell 4 96) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_26 : chk [] rt 0 12 2 (memoCell 4 100) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_27 : chk [] rt 0 12 2 (memoCell 4 104) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_28 : chk [] rt 0 12 2 (memoCell 4 108) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_29 : chk [] rt 0 12 2 (memoCell 4 112) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_30 : chk [] rt 0 12 2 (memoCell 4 116) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_31 : chk [] rt 0 12 2 (memoCell 4 120) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_32 : chk [] rt 0 12 2 (memoCell 4 124) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_33 : chk [] rt 0 12 2 (memoCell 4 128) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_34 : chk [] rt 0 12 2 (memoCell 4 132) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_35 : chk [] rt 0 12 2 (memoCell 4 136) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_36 : chk [] rt 0 12 2 (memoCell 4 140) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_37 : chk [] rt 0 12 2 (memoCell 4 144) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_38 : chk [] rt 0 12 2 (memoCell 4 148) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_39 : chk [] rt 0 12 2 (memoCell 4 152) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_40 : chk [] rt 0 12 2 (memoCell 4 156) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_41 : chk [] rt 0 12 2 (memoCell 4 160) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_42 : chk [] rt 0 12 2 (memoCell 4 164) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_43 : chk [] rt 0 12 2 (memoCell 4 168) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_44 : chk [] rt 0 12 2 (memoCell 4 172) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_45 : chk [] rt 0 12 2 (memoCell 4 176) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_46 : chk [] rt 0 12 2 (memoCell 4 180) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_47 : chk [] rt 0 12 2 (memoCell 4 184) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_48 : chk [] rt 0 12 2 (memoCell 4 188) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_49 : chk [] rt 0 12 2 (memoCell 4 192) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_50 : chk [] rt 0 12 2 (memoCell 4 196) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_51 : chk [] rt 0 12 2 (memoCell 4 200) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_52 : chk [] rt 0 12 2 (memoCell 4 204) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_53 : chk [] rt 0 12 2 (memoCell 4 208) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Proof_54 : chk [] rt 0 12 2 (memoCell 4 212) 0 = false := by decide +kernel
def cacheR2Checked : List {p : ℕ × ℕ // chk [] rt 0 12 2 p.1 p.2 = false} := [⟨((0), 1), cacheR2Proof_0⟩, ⟨((memoCell 4 0), 0), cacheR2Proof_1⟩, ⟨((memoCell 4 4), 0), cacheR2Proof_2⟩, ⟨((memoCell 4 8), 0), cacheR2Proof_3⟩, ⟨((memoCell 4 12), 0), cacheR2Proof_4⟩, ⟨((memoCell 4 16), 0), cacheR2Proof_5⟩, ⟨((memoCell 4 20), 0), cacheR2Proof_6⟩, ⟨((memoCell 4 24), 0), cacheR2Proof_7⟩, ⟨((memoCell 4 28), 0), cacheR2Proof_8⟩, ⟨((memoCell 4 32), 0), cacheR2Proof_9⟩, ⟨((memoCell 4 36), 0), cacheR2Proof_10⟩, ⟨((memoCell 4 40), 0), cacheR2Proof_11⟩, ⟨((memoCell 4 44), 0), cacheR2Proof_12⟩, ⟨((memoCell 4 48), 0), cacheR2Proof_13⟩, ⟨((memoCell 4 52), 0), cacheR2Proof_14⟩, ⟨((memoCell 4 56), 0), cacheR2Proof_15⟩, ⟨((memoCell 4 60), 0), cacheR2Proof_16⟩, ⟨((memoCell 4 64), 0), cacheR2Proof_17⟩, ⟨((memoCell 4 68), 0), cacheR2Proof_18⟩, ⟨((memoCell 4 72), 0), cacheR2Proof_19⟩, ⟨((memoCell 4 76), 0), cacheR2Proof_20⟩, ⟨((memoCell 4 80), 0), cacheR2Proof_21⟩, ⟨((memoCell 4 84), 0), cacheR2Proof_22⟩, ⟨((memoCell 4 88), 0), cacheR2Proof_23⟩, ⟨((memoCell 4 92), 0), cacheR2Proof_24⟩, ⟨((memoCell 4 96), 0), cacheR2Proof_25⟩, ⟨((memoCell 4 100), 0), cacheR2Proof_26⟩, ⟨((memoCell 4 104), 0), cacheR2Proof_27⟩, ⟨((memoCell 4 108), 0), cacheR2Proof_28⟩, ⟨((memoCell 4 112), 0), cacheR2Proof_29⟩, ⟨((memoCell 4 116), 0), cacheR2Proof_30⟩, ⟨((memoCell 4 120), 0), cacheR2Proof_31⟩, ⟨((memoCell 4 124), 0), cacheR2Proof_32⟩, ⟨((memoCell 4 128), 0), cacheR2Proof_33⟩, ⟨((memoCell 4 132), 0), cacheR2Proof_34⟩, ⟨((memoCell 4 136), 0), cacheR2Proof_35⟩, ⟨((memoCell 4 140), 0), cacheR2Proof_36⟩, ⟨((memoCell 4 144), 0), cacheR2Proof_37⟩, ⟨((memoCell 4 148), 0), cacheR2Proof_38⟩, ⟨((memoCell 4 152), 0), cacheR2Proof_39⟩, ⟨((memoCell 4 156), 0), cacheR2Proof_40⟩, ⟨((memoCell 4 160), 0), cacheR2Proof_41⟩, ⟨((memoCell 4 164), 0), cacheR2Proof_42⟩, ⟨((memoCell 4 168), 0), cacheR2Proof_43⟩, ⟨((memoCell 4 172), 0), cacheR2Proof_44⟩, ⟨((memoCell 4 176), 0), cacheR2Proof_45⟩, ⟨((memoCell 4 180), 0), cacheR2Proof_46⟩, ⟨((memoCell 4 184), 0), cacheR2Proof_47⟩, ⟨((memoCell 4 188), 0), cacheR2Proof_48⟩, ⟨((memoCell 4 192), 0), cacheR2Proof_49⟩, ⟨((memoCell 4 196), 0), cacheR2Proof_50⟩, ⟨((memoCell 4 200), 0), cacheR2Proof_51⟩, ⟨((memoCell 4 204), 0), cacheR2Proof_52⟩, ⟨((memoCell 4 208), 0), cacheR2Proof_53⟩, ⟨((memoCell 4 212), 0), cacheR2Proof_54⟩]
def cacheR2Parts : List (ℕ × ℕ) := cacheR2Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR2Full : mFull cacheR2Parts = true := by decide +kernel
def cacheR2One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 2 p.1 p.2 = false := by
  refine ⟨cacheR2Parts, cacheR2Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_0 : chk [] rt 0 12 3 (0) 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_1 : chk [] rt 0 12 3 (memoCell 7 0) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_2 : chk [] rt 0 12 3 (memoCell 7 7) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_3 : chk [] rt 0 12 3 (memoCell 7 14) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_4 : chk [] rt 0 12 3 (memoCell 7 21) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_5 : chk [] rt 0 12 3 (memoCell 7 28) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_6 : chk [] rt 0 12 3 (memoCell 7 35) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_7 : chk [] rt 0 12 3 (memoCell 7 42) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_8 : chk [] rt 0 12 3 (memoCell 7 49) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_9 : chk [] rt 0 12 3 (memoCell 7 56) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_10 : chk [] rt 0 12 3 (memoCell 7 63) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_11 : chk [] rt 0 12 3 (memoCell 7 70) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_12 : chk [] rt 0 12 3 (memoCell 7 77) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_13 : chk [] rt 0 12 3 (memoCell 7 84) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_14 : chk [] rt 0 12 3 (memoCell 7 91) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_15 : chk [] rt 0 12 3 (memoCell 7 98) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_16 : chk [] rt 0 12 3 (memoCell 7 105) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_17 : chk [] rt 0 12 3 (memoCell 7 112) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_18 : chk [] rt 0 12 3 (memoCell 7 119) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_19 : chk [] rt 0 12 3 (memoCell 7 126) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_20 : chk [] rt 0 12 3 (memoCell 7 133) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_21 : chk [] rt 0 12 3 (memoCell 7 140) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_22 : chk [] rt 0 12 3 (memoCell 7 147) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_23 : chk [] rt 0 12 3 (memoCell 7 154) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_24 : chk [] rt 0 12 3 (memoCell 7 161) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_25 : chk [] rt 0 12 3 (memoCell 7 168) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_26 : chk [] rt 0 12 3 (memoCell 7 175) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_27 : chk [] rt 0 12 3 (memoCell 7 182) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_28 : chk [] rt 0 12 3 (memoCell 7 189) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_29 : chk [] rt 0 12 3 (memoCell 7 196) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_30 : chk [] rt 0 12 3 (memoCell 7 203) 0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Proof_31 : chk [] rt 0 12 3 (memoCell 7 210) 0 = false := by decide +kernel
def cacheR3Checked : List {p : ℕ × ℕ // chk [] rt 0 12 3 p.1 p.2 = false} := [⟨((0), 1), cacheR3Proof_0⟩, ⟨((memoCell 7 0), 0), cacheR3Proof_1⟩, ⟨((memoCell 7 7), 0), cacheR3Proof_2⟩, ⟨((memoCell 7 14), 0), cacheR3Proof_3⟩, ⟨((memoCell 7 21), 0), cacheR3Proof_4⟩, ⟨((memoCell 7 28), 0), cacheR3Proof_5⟩, ⟨((memoCell 7 35), 0), cacheR3Proof_6⟩, ⟨((memoCell 7 42), 0), cacheR3Proof_7⟩, ⟨((memoCell 7 49), 0), cacheR3Proof_8⟩, ⟨((memoCell 7 56), 0), cacheR3Proof_9⟩, ⟨((memoCell 7 63), 0), cacheR3Proof_10⟩, ⟨((memoCell 7 70), 0), cacheR3Proof_11⟩, ⟨((memoCell 7 77), 0), cacheR3Proof_12⟩, ⟨((memoCell 7 84), 0), cacheR3Proof_13⟩, ⟨((memoCell 7 91), 0), cacheR3Proof_14⟩, ⟨((memoCell 7 98), 0), cacheR3Proof_15⟩, ⟨((memoCell 7 105), 0), cacheR3Proof_16⟩, ⟨((memoCell 7 112), 0), cacheR3Proof_17⟩, ⟨((memoCell 7 119), 0), cacheR3Proof_18⟩, ⟨((memoCell 7 126), 0), cacheR3Proof_19⟩, ⟨((memoCell 7 133), 0), cacheR3Proof_20⟩, ⟨((memoCell 7 140), 0), cacheR3Proof_21⟩, ⟨((memoCell 7 147), 0), cacheR3Proof_22⟩, ⟨((memoCell 7 154), 0), cacheR3Proof_23⟩, ⟨((memoCell 7 161), 0), cacheR3Proof_24⟩, ⟨((memoCell 7 168), 0), cacheR3Proof_25⟩, ⟨((memoCell 7 175), 0), cacheR3Proof_26⟩, ⟨((memoCell 7 182), 0), cacheR3Proof_27⟩, ⟨((memoCell 7 189), 0), cacheR3Proof_28⟩, ⟨((memoCell 7 196), 0), cacheR3Proof_29⟩, ⟨((memoCell 7 203), 0), cacheR3Proof_30⟩, ⟨((memoCell 7 210), 0), cacheR3Proof_31⟩]
def cacheR3Parts : List (ℕ × ℕ) := cacheR3Checked.map Subtype.val
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def cacheR3Full : mFull cacheR3Parts = true := by decide +kernel
def cacheR3One : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 3 p.1 p.2 = false := by
  refine ⟨cacheR3Parts, cacheR3Full, ?_⟩
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  exact q.property
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_4 : chk [] rt 0 12 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_5 : chk [] rt 0 12 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_6 : chk [] rt 0 12 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_7 : chk [] rt 0 12 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_8 : chk [] rt 0 12 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_9 : chk [] rt 0 12 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_10 : chk [] rt 0 12 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_11 : chk [] rt 0 12 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def proot_12 : chk [] rt 0 12 12 FF 1 = false := by decide +kernel
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 12 t S) : False := by
  have hmin : ∀ q < 12, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => iroot q hq
  have hm0 : Min Z0 (mz 0) (tz 0) 12 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t < 13 := by have := hm0.size.2; omega
  have hM : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rt 0 12 t p.1 p.2 = false := by
    interval_cases t
    · exact cacheR1One
    · exact cacheR2One
    · exact cacheR3One
    · exact one proot_4
    · exact one proot_5
    · exact one proot_6
    · exact one proot_7
    · exact one proot_8
    · exact one proot_9
    · exact one proot_10
    · exact one proot_11
    · exact one proot_12
  exact imp_of_live (L := 13) (Or.inl rfl) root_p (by norm_num) ir (by omega) hS hl hmin (Or.inr hM)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2 && x 3) || (x 0 && x 2 && x 4) || (x 1 && x 2 && x 4) || (x 1 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 1 && x 2 && x 5) || (x 0 && x 3 && x 5) || (x 2 && x 3 && x 4 && x 5)
def EF : ℕ := (rawP0.getD 0 0 &&& rawP0.getD 1 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 3 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 2 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0 &&& rawP0.getD 5 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 6 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 6 => (rawP0.getD v.val 0).testBit b) = rawP0.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len0]
  · intro i h1 h2
    have : i < rawP0.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 6 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨out, hout⟩
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, List.mem_append_left _ hw, rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by intro k hk; simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]; rw [row_list]
  have hout : (ex (mz 0) gates init).getD o 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) o
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1; rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]; rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn (row k))).getD o false = f (row k) at h
      rw [h]; exact (f_bit k).symm
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot ⟨o, hout⟩
def onWit : List Gate := [⟨.and, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [3, 0]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [1, 16]⟩, ⟨.or, [15, 17]⟩]
theorem onWitBasis : ∀ g ∈ onWit,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem onWitCorrect : ∀ x : Fin 6 → Bool, Circuit.eval ⟨onWit, 18⟩ (List.ofFn x) = f x := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem onTableCorrect : ∀ x : Fin 6 → Bool, f x = Nat.testBit (4276677352 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel
end inst_data
end PEqualNP.Outside.L_meta_41874_aux

open PEqualNP.Outside.L_meta_41874_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_41874 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677352 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677352 * 2 ^ 32 + 3974670472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨⟨gates, o⟩, hC, hsize, hcorrect⟩ := hs
  have hf : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = f x := fun x => (hcorrect x).trans (onTableCorrect x).symm
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 13 ≤ gates.length := by
      by_contra hlt
      by_cases hsmall : gates.length < 12
      · exact iroot gates.length hsmall (bridge ⟨gates, o⟩ hC hf)
      · have heq : gates.length = 12 := by omega
        rcases bridge_not gates o hC hnot hf with hs | ⟨t, ht, S0, hS, hl⟩
        · exact iroot (gates.length - 1) (by omega) hs
        · rw [heq] at hl
          exact iroot_pos ht hS hl
    refine ⟨⟨onWit, 18⟩, ?_, ?_, fun x => (onWitCorrect x).trans (onTableCorrect x)⟩
    · intro g hg
      obtain ⟨ho, hl⟩ := onWitBasis g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ho, hl⟩
    · have hw : (⟨onWit, 18⟩ : Circuit).size = 13 := rfl
      change gates.length ≤ s at hsize
      omega
  · refine ⟨⟨gates, o⟩, ?_, hsize, hcorrect⟩
    intro g hg
    obtain ⟨ho, hl⟩ := hC g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hnot ⟨g, hg, h⟩).elim
