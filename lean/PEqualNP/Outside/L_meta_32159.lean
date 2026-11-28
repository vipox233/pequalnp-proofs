import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32159_aux

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
  rawP_len : I.rawP.length = 8

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
  st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) fun remaining =>
    Bool.rec (motive := fun _ => Bool) false
      (kids (child f g) e n remaining a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v))
      (Nat.beq (Nat.land remaining g) g)
def f0 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Nat.beq (Nat.lor da dc) 0))
def f1 (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) (h a c da dc s x y) (Bool.rec (motive := fun _ => Bool) (Nat.beq dc 0) true (Nat.beq da 0)))
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
  Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)
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
    (fun _ ih k t z v => cvC NN (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1))) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => cvC NN (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeC NN (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1))) fuel
end coreC

def bigNat_0 : Nat := 0xffffeffffeffffef7ffff7ffff7bffff7df7bffff7dffffbbedffffbdf77fffef7b7ddefffb6d6ad5fff5adb56fffad7ffdbffeb6d56abffeb6aafffafffbffedad6b5fff5b5fff7ffdb6db6fffb6dfff0000000000000000
def bigNat_1 : Nat := 0x492952a000a524a90005280024001492a95400149550005000400125294a000a4a0008002492490004920000000000000000000
def bigNat_2 : Nat := 0x1000010000100001080000800008400008208400008200004412000042088000108482210000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0x3ffff07c000000000ffffc0f0f83c00000000000140402000124200a10058000011004800440144014005800840002482802800b020b0c02424804c00000000000000000444a0244a00c4a104225041250821250410821150498ce83e010898411152b60787c1e1128000800000020300000210001bffe000408800000a200020003ffe00c6000004340007ffc30d8600036dffffa7b7179dbe71baf
def bigNat_4 : Nat := 0x1ffffc000000000000000000000000000000000003ffff03e0ffffde00fb80000000400880c00108c40a58206310300000001019045040c440e103000010881490881c20610412440e61882800000000000000000809404094da89400044a0024a10024a08210022a0801130824855701f0114dcf007dc002500060040000018460002c00018000001000000086280002fff8000021084000585fff0001861b6fffb0c000fbc3fe9e6595ce57
def bigNat_5 : Nat := 0x7fffe03e07fffe03ffff7003ffff7800ffffdef6000000000004200bc8480a007a4a03f001f100821401d9205407e007c01f1858160174b6017805e3603600ec6c01e80000000000000000109000890003100208880084802254e001f01548c00aa463800a6453c0019894f7b0000240001021000042c0500002d7ffc000080c10a0000b02afff80000000c2c0b00005b00000001b01b0000360000b8e2fd0cd6e4697f
def bigNat_6 : Nat := 0xffffe00000000007fffef800000003ffff7bee00000000000000000800001289000a40ac00054002a00402c004916d00128012804a090012825800025009434d0001484902b0000000000000000021022110220c022411011537110080911042190cd7c40248040c465bdf720106008040240880c0000000580056fff80000000000601600000b68000000000000d800b5fff0000000001b6c0000036dffffcfa7fed0a0bad0c
def bigNat_7 : Nat := 0x1ffffc000000000000000007fffef8007fffefbffff77d80000000000000000000000004005810b0b5a60087000438021c120025521e00000870087021c1b5ac01160001160458269a488f00011c0000000000000000040204de20410204002102018024218e27c001188e7c8c473bec0806002002018100084008106002c00005adb000000000000000b0016abffe000000000000000dad6000000000000001b6db6fff800000d13f6ca4c6a68f91
def bigNat_8 : Nat := 0xffffe0000007fffefbef0000000000000000000000000000000000000020004a02c0000000140000a00050169a80009000000240024009012528405802405801600000002800005000000000000000000820386003860038863e1c2201c0310fc7df7a00f0110078008100780842401e0210108480e30002d5fff0000000000000000000b6d4000000000000000000000dad6b5fff5b5fff7ffc00000000000000043f7419e9fb1f0e
def bigNat_9 : Nat := 0x1ffffc00000000000ffffeffffef0000000000000000000000000000000000000000000000069a9002300000001180008c0046004d28804e00490138013804e000000026000026009800000013000026000000000000000000fc3c0803c0803c0043fe043fe0781f00208001f00200f8011080f80108003e0042121080f036d68000000000000000000000000b6d56abffeb6aafffafffbffe000000000000000000000000000000000a4cf9b63b5396fa1
def bigNat_10 : Nat := 0x1ffffdffffdffffde00000000000000000000000000000000000000000000000000000000004d2d10bc00213409e0010f002780000000070000001c001c007000000003800003800e00000001c000038000000000000000000ffc00ffc00ffc00f7c0007c00003e00041043e00041f0002201f00021047c0008424010f0036d6ad5fff5adb56fffad7ffdbffe000000000000000000000000000000000000000000000000000000000026863f83919372c7
def bigNat_11 : Nat := 0xffffeffffeffffef7ffff7ffff7bffff7df7bffff7dffffbbedffffbdf77fffef7b7ddefffb6d6ad5fff5adb56fffad7ffdbffeb6d56abffeb6aafffafffbffedad6b5fff5b5fff7ffdb6db6fffb6dfffffffffffffffffff
def NN0 : Nat := 709
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 77), (77, 80), (80, 83), (83, 86), (86, 100), (100, 103), (103, 106), (106, 109), (109, 112), (112, 115), (115, 118), (118, 121), (121, 135), (135, 149), (149, 151), (151, 154), (154, 157), (157, 159), (159, 173), (173, 175), (175, 178), (178, 180), (180, 183), (183, 185), (185, 188), (188, 190), (190, 193), (193, 196), (196, 210), (210, 224), (224, 226), (226, 240), (240, 242), (242, 244), (244, 246), (246, 248), (248, 251), (251, 254), (254, 256), (256, 270), (270, 272), (272, 274), (274, 276), (276, 279), (279, 281), (281, 283), (283, 285), (285, 288), (288, 291), (291, 294), (294, 296), (296, 310), (310, 313), (313, 327), (327, 329), (329, 332), (332, 334), (334, 348), (348, 351), (351, 353), (353, 355), (355, 358), (358, 361), (361, 364), (364, 366), (366, 369), (369, 371), (371, 385), (385, 387), (387, 389), (389, 392), (392, 394), (394, 396), (396, 399), (399, 401), (401, 404), (404, 407), (407, 410)]
def segsY0 : List (ℕ × ℕ) := [(410, 424), (424, 429), (429, 433), (433, 439), (439, 442), (442, 447), (447, 452), (452, 471), (471, 475), (475, 481), (481, 486), (486, 505), (505, 508), (508, 514), (514, 518), (518, 537), (537, 543), (543, 562), (562, 567), (567, 573), (573, 579), (579, 598), (598, 603), (603, 623), (623, 643), (643, 648), (648, 668), (668, 688), (688, 708)]
def rawP0 : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8, bigNat_9, bigNat_10]
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
      have h3 : Bool.rec (motive := fun _ => Bool) (Nat.beq dc 0) true (Nat.beq da 0) = true := by
        rcases this with h | h
        · simp [h]
        · cases Nat.beq da 0 <;> simp [h]
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
  simpa only [cv, cvC, hcov] using h
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
    change cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pos_eq] at h
    have h := cv_ok X hs hm.1 h
    rw [bR] at h
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
    change cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [pos_eq] at h
    have h := cv_ok X hs hl h
    rw [bR] at h
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
def kz (Z : ℕ) : ℕ := (List.range 8).foldr (fun i bad =>
  let a := I.rawP.getD i 0
  let b := Nat.shiftRight a I.NN
  let bad0 := bif Z.testBit i then (a ||| b) &&& FULL else 0
  let bad1 := bif Z.testBit (8+i) then (a &&& b &&& FULL) ^^^ FULL else 0
  bad ||| bad0 ||| bad1) 0
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

def UniqueNot (gs : List Gate) : Prop :=
  ∀ i j : Fin gs.length, (gs.get i).op = .not → (gs.get j).op = .not → i = j

lemma UniqueNot.tail {g : Gate} {gs : List Gate} (h : UniqueNot (g :: gs)) : UniqueNot gs := by
  intro i j hi hj
  let i' : Fin (g :: gs).length := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let j' : Fin (g :: gs).length := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  have he := congrArg Fin.val (h i' j' hi hj)
  apply Fin.ext
  dsimp [i', j'] at he
  omega

lemma UniqueNot.tail_of_head {g : Gate} {gs : List Gate} (h : UniqueNot (g :: gs)) (hg : g.op = .not) :
    ∀ a ∈ gs, a.op ≠ .not := by
  intro a ha hnot
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp ha
  let j : Fin (g :: gs).length := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let z : Fin (g :: gs).length := ⟨0, by simp⟩
  have hj : ((g :: gs).get j).op = .not := by
    change (gs.get i).op = .not
    rw [hi, hnot]
  have he := congrArg Fin.val (h z j hg hj)
  dsimp [z, j] at he
  omega

lemma Live.add_binary {m T k t : ℕ} {S : Set ℕ} {S1 : Finset ℕ} {d : Bool} {a b : ℕ}
    (hl : Live Z0 m T k t S1) (hs : (S1 : Set ℕ) ⊆ insert (op d a b) S) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ k' ≤ k + 1, ∃ S' : Finset ℕ, (S' : Set ℕ) ⊆ S ∧ Live Z0 m T k' t S' := by
  by_cases hg : op d a b ∈ S1
  · by_cases hab : a = b
    · subst hab
      rw [op_self] at hs
      exact ⟨k, by omega, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
    · refine ⟨k + 1, le_rfl, insert a (insert b (S1.erase (op d a b))), ?_,
        .bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
  · exact ⟨k, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩

lemma ex_mono_live {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op = .and ∨ g.op = .or) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    ∃ k ≤ gs.length, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k 0 S0 := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact ⟨0, by simp, _, by simpa [ex] using getD_mem hw h0 i, .stop⟩
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → ∃ k ≤ (g :: gs).length, ∃ S0 : Finset ℕ,
        (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k 0 S0 := by
      intro h
      obtain ⟨k, hk, S0, hS0, hl⟩ := ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT
      exact ⟨k, by simp; omega, S0, hS0, hl⟩
    have go := ih (w ++ [gv m w g]) (insert (gv m w g) S) (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact Or.inr (hw x hx)
        · exact Or.inl rfl) (Or.inr h0) (Or.inr hm) hgs hT
    have hop := hg g List.mem_cons_self
    obtain ⟨o, l⟩ := g
    rcases hop with rfl | rfl
    · match l with
      | [] => exact stay hm
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        obtain ⟨k, hk, S0, hS0, hl⟩ := go
        obtain ⟨k', hk', S', hS', hl'⟩ := Live.add_binary (d := false) hl hS0 (rd i) (rd j)
        exact ⟨k', by simp; omega, S', hS', hl'⟩
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ =>
        obtain ⟨k, hk, S0, hS0, hl⟩ := go
        obtain ⟨k', hk', S', hS', hl'⟩ := Live.add_binary (d := true) hl hS0 (rd i) (rd j)
        exact ⟨k', by simp; omega, S', hS', hl'⟩

lemma ex_sol_not {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ),
    (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    UniqueNot gs → (∃ g ∈ gs, g.op = GateOp.not) →
    (∃ i, (ex m gs w).getD i 0 = T) →
    Sol Z0 m T (gs.length - 1) S ∨ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T gs.length 1 S0 := by
  induction gs with
  | nil => intro _ _ _ _ _ _ _ hnot; simp at hnot
  | cons g gs ih =>
    intro w S hw h0 hm hg huniq hnot hT
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
        rcases ih (w ++ [gv m w ⟨.and, i :: j :: _⟩]) (insert (op false (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs huniq.tail hnot' hT with hs | ⟨S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs huniq.tail hnot' hT with hs | ⟨S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (al0 _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.not, []⟩]) S (hwm_stay hm) h0 hm hgs hT)
      | i :: _ =>
        have hgsMono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or := by
          intro g hg
          have hne := huniq.tail_of_head (by rfl) g hg
          have ho := (hgs g hg).1
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
          rcases ho with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact (hne h).elim
        obtain ⟨k, hk, S1, hS1, hl1⟩ := ex_mono_live m gs
          (w ++ [gv m w ⟨.not, i :: _⟩]) (insert (w.getD i 0 ^^^ m) S)
          hwm_ins (Or.inr h0) (Or.inr hm) hgsMono hT
        by_cases hz : w.getD i 0 ^^^ m ∈ S1
        · have hsub : ((insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m)) : Finset ℕ) : Set ℕ) ⊆ S := by
            intro x hx; simp at hx; rcases hx with rfl | ⟨h1, h2⟩; exact rd i; exact (hS1 h1).resolve_left h2
          have hlu : Live Z0 m T (k + 1) 1 (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨_, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))

lemma scan_eq_any (p : XW → Bool) (xs : List XW) : scan p xs = xs.any p := by
  induction xs with
  | nil => rfl
  | cons w ws ih =>
    change Bool.rec (motive := fun _ => Bool) (scan p ws) true (p w) = _
    rw [ih, bR]
    cases h : p w <;> simp [List.any_cons, h]

lemma pairsC_eq (H : ℕ) (f : XW → XW → Bool) (a : XW) (xs : List XW) :
    pairsC H f (a :: xs) =
      (xs.any (fun x => hb H (a.s + x.s) && f a x) || pairsC H f xs) := by
  have he : (fun x : XW => bif hb H (a.s + x.s) then f a x else false) =
      (fun x : XW => hb H (a.s + x.s) && f a x) := by
    funext x
    cases hb H (a.s + x.s) <;> rfl
  change Bool.rec (motive := fun _ => Bool) (pairsC H f xs) true
    (scan (fun x => Bool.rec (motive := fun _ => Bool) false (f a x) (hb H (a.s + x.s))) xs) = _
  rw [bR, scan_eq_any]
  simp only [bR, he]
  cases xs.any (fun x => hb H (a.s + x.s) && f a x) <;> rfl

def possibleInputPair (H : ℕ) (v : List W) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a rest later =>
      Bool.rec (motive := fun _ => Bool) later true (rest.any fun b => hb H (a.s + b.s))) v

lemma possibleInputPair_cons (H : ℕ) (a : W) (v : List W) :
    possibleInputPair H (a :: v) = ((v.any fun b => hb H (a.s + b.s)) || possibleInputPair H v) := by
  change Bool.rec (motive := fun _ => Bool) (possibleInputPair H v) true
    (v.any fun b => hb H (a.s + b.s)) = _
  cases v.any (fun b => hb H (a.s + b.s)) <;> rfl

lemma mkXC_map (nn : ℕ) (d : Bool) (l o : ℕ) (v : List W) :
    mkXC nn d l o v = v.map (fun w => ⟨w, w.s, Nat.shiftRight w.s nn, Nat.land (spC nn d l w.s) o⟩) := by
  induction v with
  | nil => rfl
  | cons w v ih =>
    change _ :: mkXC nn d l o v = _ :: _
    rw [ih]

lemma fs_eq_filter (xs : List XW) : fs xs = xs.filter (fun x => !Nat.beq x.w.r 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => List XW) (x :: fs xs) (fs xs) (Nat.beq x.w.r 0) = _
    rw [ih]
    cases h : Nat.beq x.w.r 0 <;> simp [h]

lemma fr_eq_filter (xs : List XW) : fr xs = xs.filter (fun x => Nat.beq x.w.r 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Bool.rec (motive := fun _ => List XW) (fr xs) (x :: fr xs) (Nat.beq x.w.r 0) = _
    rw [ih]
    cases h : Nat.beq x.w.r 0 <;> simp [h]

lemma pairImpossible {H nn l o : ℕ} {d : Bool} {v : List W} (f : XW → XW → Bool)
    (h : possibleInputPair H v = false) :
    pairsC H f (fs (mkXC nn d l o v)) = false := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    rw [possibleInputPair_cons, Bool.or_eq_false_iff] at h
    let a' : XW := ⟨a, a.s, Nat.shiftRight a.s nn, Nat.land (spC nn d l a.s) o⟩
    change pairsC H f (Bool.rec (motive := fun _ => List XW)
      (a' :: fs (mkXC nn d l o v)) (fs (mkXC nn d l o v)) (Nat.beq a.r 0)) = _
    cases ha : Nat.beq a.r 0
    · change pairsC H f (a' :: fs (mkXC nn d l o v)) = false
      rw [pairsC_eq, ih h.2, Bool.or_false]
      apply List.any_eq_false.mpr
      intro x hx
      rw [fs_eq_filter, List.mem_filter, mkXC_map, List.mem_map] at hx
      obtain ⟨⟨w, hw, rfl⟩, _⟩ := hx
      intro hit
      simp only [Bool.and_eq_true] at hit
      exact List.any_eq_false.mp h.1 w hw hit.1
    · exact ih h.2

lemma noGenerated {nn l o : ℕ} {d : Bool} {v : List W}
    (h : v.any (fun w => Nat.beq w.r 0) = false) : fr (mkXC nn d l o v) = [] := by
  rw [fr_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro x hx
  rw [mkXC_map, List.mem_map] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  exact List.any_eq_false.mp h w hw

lemma noMoves {v : List W} (h : v.any (fun w => Nat.beq w.r 0) = false)
    (nn aa hx hy l m g k z y : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool) :
    mvC nn aa hx hy F l m g k 0 z v y = false := by
  have hp (f : XW → XW → Bool) : pairsN f (mkXC nn false l (wstC nn false l v) v) = false := by
    rw [pairsN, noGenerated h]; rfl
  have hnode : nodeC nn (F (Nat.sub k 1) 0) false l m g
      (Nat.sub (Nat.sub k 0) y) v.length z v pairsN = false := by
    simp only [nodeC, hp, bR, Bool.cond_self]
  simp only [mvC, show pos 0 = false from rfl, hnode, show ∀ f, prd 0 f = false by intro; rfl, bR]

lemma noNode {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodeC nn f d l m g e n z v (fun h xs => pairsC H h (fs xs)) = false := by
  simp only [nodeC, pairImpossible _ h, bR, Bool.cond_self]

lemma tst_const_false (nn aa hx hy : ℕ) (d : Bool) (l e : ℕ) (v : List W) :
    tstC nn aa hx hy d l e v (fun _ => false) = false := by
  simp only [tstC, bR, Bool.cond_self]

def relevantStart (t H ph : ℕ) (v : List W) : Bool :=
  (Nat.ble v.length 1 || (Nat.beq ph 1 && (pos t || v.any fun w => Nat.beq w.r 0))) ||
    possibleInputPair H v

lemma relevantStart_facts {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false) :
    Nat.ble v.length 1 = false ∧
      (Nat.beq ph 1 = false ∨ (t = 0 ∧ v.any (fun w => Nat.beq w.r 0) = false)) ∧
      possibleInputPair H v = false := by
  simp only [relevantStart, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at h
  refine ⟨h.1.1, h.1.2.imp_right ?_, h.2⟩
  rintro ⟨ht, hv⟩
  exact ⟨by cases t <;> simp [pos] at ht ⊢, hv⟩

lemma inactiveTop {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) :
    topCC nn aa hx hy l m g K H ph k t z v = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topCC, hl, noNode hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMoves hv, Bool.cond_self, tst_const_false]

def guardStart (t H ph : ℕ) (test : List W → Bool) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (test v) (relevantStart t H ph v)

lemma guardStart_eq {t H ph : ℕ} {test : List W → Bool}
    (h : ∀ v, relevantStart t H ph v = false → test v = false) :
    guardStart t H ph test = test := by
  funext v
  unfold guardStart
  cases hv : relevantStart t H ph v
  · exact (h v hv).symm
  · rfl

lemma inactiveStart {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) :
    startvC nn aa hx hy l m g B K t p H ph v = false := by
  simp only [startvC, child, st_eq, inactiveTop h, bR, Bool.cond_self]

noncomputable def searchInputs (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (guardStart t H ph (test nn aa hx hy l m g B p))))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma searchInputs_eq {E Q : List (ℕ × ℕ)} {Z K t H ph : ℕ}
    {test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool}
    (h : ∀ nn aa hx hy l m g B p v, relevantStart t H ph v = false →
      test nn aa hx hy l m g B p v = false) :
    searchInputs E Q Z K t H ph test =
      (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
        frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
          st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
          anySubC nn (pos t) l v 0 (test nn aa hx hy l m g B p)))
        (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z) := by
  simp only [searchInputs, guardStart_eq (h _ _ _ _ _ _ _ _ _)]

noncomputable def chkFast (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p =>
    startvC nn aa hx hy l m g B K t p H ph)

lemma chkFast_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkFast E Q Z K t H ph = chk E Q Z K t H ph := by
  unfold chkFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStart h nn aa hx hy l m g B K p)]
  rfl
set_option maxHeartbeats 0 in
noncomputable def notCandidate (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v : List W) (a : W) : Bool :=
  nots f m g e n z q v [a]

set_option maxHeartbeats 0 in
lemma nots_cons (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v : List W) (a : W) (r : List W) :
    nots f m g e n z q v (a :: r) =
      (notCandidate f m g e n z q v a || nots f m g e n z q v r) := by
  unfold notCandidate
  unfold nots
  dsimp only
  simp only [bR]
  have fact (d x : Bool) : (bif d then true else x) = ((bif d then true else false) || x) := by
    cases d <;> rfl
  exact fact _ _

set_option maxHeartbeats 0 in
lemma nots_true_iff (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) :
    nots f m g e n z q v r = true ↔
      ∃ a ∈ r, notCandidate f m g e n z q v a = true := by
  induction r with
  | nil => simp [nots]
  | cons a r ih =>
    rw [nots_cons, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨b,hb,ht⟩)
      · exact ⟨a, by simp, h⟩
      · exact ⟨b, by simp [hb], ht⟩
    · rintro ⟨b,hb,ht⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Or.inl ht
      · exact Or.inr ⟨b,hb,ht⟩

set_option maxHeartbeats 0 in
lemma nots_some_bin (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W)
    (h : nots f m g e n z q v r = true) :
    ∃ b : Fin 8, nots f m g e n z q v (r.filter fun a => a.s % 8 == b.val) = true := by
  obtain ⟨a,ha,hit⟩ := (nots_true_iff _ _ _ _ _ _ _ _ _).mp h
  refine ⟨⟨a.s % 8, Nat.mod_lt _ (by decide)⟩,
    (nots_true_iff _ _ _ _ _ _ _ _ _).mpr ⟨a, ?_, hit⟩⟩
  simp [ha]

set_option maxHeartbeats 0 in
def picked {X : Type} (F : X → Bool) (G : Fin 8 → X → Bool) : Prop :=
  ∀ x, F x = true → ∃ b, G b x = true

set_option maxHeartbeats 0 in
lemma Bool_pick (base : Bool) (F : Bool) (G : Fin 8 → Bool)
    (h : F = true → ∃ b, G b = true) :
    base || F = true → ∃ b, base || G b = true := by
  cases base
  · simpa using h
  · intro _
    exact ⟨0, rfl⟩

set_option maxHeartbeats 0 in
lemma tst_picked (nn aa hx hy : ℕ) (d : Bool) (l e : ℕ) (v : List W)
    (F : ℕ → Bool) (G : Fin 8 → ℕ → Bool) (hp : picked F G) :
    tstC nn aa hx hy d l e v F = true →
      ∃ b : Fin 8, tstC nn aa hx hy d l e v (G b) = true := by
  simp only [tstC, bR]
  cases h : Nat.beq v.length e
  · simp only [h, Bool.cond_false]
    cases hnext : Nat.beq v.length.succ e
    · simp only [hnext, Bool.cond_false]
      exact hp 0
    · simp only [hnext, Bool.cond_true]
      cases hb : bipC nn aa hx hy l (wstC nn d l v) v []
      · simp only [hb, Bool.cond_false]
        cases hs : flkC nn aa l (wstC nn d l v) v (starC hx hy)
        · simp only [hs, Bool.cond_false]
          exact hp 1
        · simp only [hs, Bool.cond_true]
          exact hp 0
      · simp [hb]
  · simp only [h, Bool.cond_true]
    cases hr : rectC nn aa hx hy d l (wstC nn d l v) v []
    · simp only [hr, Bool.cond_false]
      exact hp 0
    · simp [hr]

set_option maxHeartbeats 0 in
noncomputable def mvPicked (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool)
    (l m g k t z : Nat) (v : List W) (y : Nat) (b : Fin 8) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (v.filter fun a => a.s % 8 == b.val))) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length

set_option maxHeartbeats 0 in
lemma mv_picked (nn aa hx hy : ℕ) (F : ℕ → ℕ → ℕ → List W → Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) :
    mvC nn aa hx hy F l m g k t z v y = true →
      ∃ b : Fin 8, mvPicked nn aa hx hy F l m g k t z v y b = true := by
  simp only [mvC, mvPicked, bR]
  cases hnode : nodeC nn (F (k-1) t) (pos t) l m g (k-t-y) v.length z v pairsN
  · simp only [hnode, Bool.cond_false]
    cases t with
    | zero => simp [prd]
    | succ t =>
      simp only [prd, Nat.rec]
      exact nots_some_bin _ _ _ _ _ _ _ _ _
  · simp only [hnode, Bool.cond_true]
    intro _
    exact ⟨0,by simp⟩

set_option maxHeartbeats 0 in
noncomputable def topPicked (NN AA HX HY l m g K H ph k t z : ℕ) (v : List W) (b : Fin 8) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mvPicked NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y b) (Nat.beq ph 1)) true
      (nodeC NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)

set_option maxHeartbeats 0 in
lemma top_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topCC nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPicked nn aa hx hy l m g K H ph k t z v b = true := by
  simp only [topCC, topPicked, bR]
  cases h : Nat.ble v.length 1
  · simp only [h, Bool.cond_false]
    apply tst_picked
    intro y
    cases hm : nodeC nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hm, Bool.cond_false]
      cases hc : Nat.beq ph 1
      · simp [hc]
      · simp only [hc, Bool.cond_true]
        exact mv_picked _ _ _ _ _ _ _ _ _ _ _ _ _
    · simp only [hm, Bool.cond_true]
      intro _
      exact ⟨0,by simp⟩
  · simp only [h, Bool.cond_true]
    intro _
    exact ⟨0,by simp⟩

set_option maxHeartbeats 0 in
noncomputable def startPicked (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (b : Fin 8) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPicked NN AA HX HY l m g K H ph K t z r b) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

set_option maxHeartbeats 0 in
lemma start_picked (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startvC nn aa hx hy l m g B K t p H ph)
      (fun b v => startPicked nn aa hx hy l m g B K t p H ph v b) := by
  intro v
  simp only [startvC, startPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact top_picked _ _ _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 0 in
lemma anySub_picked (nn : ℕ) (d : Bool) (l : ℕ) (v : List W)
    (F : List W → Bool) (G : Fin 8 → List W → Bool) (hp : picked F G) (bits : ℕ) :
    anySubC nn d l v bits F = true → ∃ b : Fin 8, anySubC nn d l v bits (G b) = true := by
  induction v generalizing F G bits with
  | nil => exact hp []
  | cons a v ih =>
    let inc := Nat.lor bits (spC nn d l a.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l v)) l
    have hu (J : List W → Bool) : anySubC nn d l (a :: v) bits J =
        (bif anySubC nn d l v inc (fun r => J (a :: r)) then true else
          (bif skip then anySubC nn d l v bits J else false)) := by
      change Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l v bits J) skip)
        true (st inc fun c => anySubC nn d l v c (fun r => J (a :: r))) = _
      simp only [st_eq, bR]
    simp only [hu]
    have hs := ih (fun as => F (a :: as)) (fun b as => G b (a :: as))
      (fun as => hp (a :: as)) inc
    cases ht : anySubC nn d l v inc (fun as => F (a :: as))
    · simp only [ht, Bool.cond_false]
      cases hc : skip
      · simp [hc]
      · simp only [hc, Bool.cond_true]
        intro h
        obtain ⟨b,hb⟩ := ih F G hp bits h
        refine ⟨b, ?_⟩
        rw [hb]
        cases anySubC nn d l v inc (fun as => G b (a :: as)) <;> rfl
    · simp only [ht, Bool.cond_true]
      intro _
      obtain ⟨b,hb⟩ := hs ht
      exact ⟨b, by rw [hb]; rfl⟩

set_option maxHeartbeats 0 in
noncomputable def chkPicked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (b : Fin 8) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPicked nn aa hx hy l m g B K t p H ph r b)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

set_option maxHeartbeats 0 in
lemma chk_picked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Fin 8, chkPicked E Q Z K t H ph b = false) : chk E Q Z K t H ph = false := by
  suffices chk E Q Z K t H ph = true → False by
    cases he : chk E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chk, chkPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (start_picked _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h b).symm.trans hb)

section BinaryPartition

noncomputable def pairOne (d : Bool) (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool)
    (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' =>
    bif d then h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)
    else h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s')
      (Nat.lor a.a c.a) (Nat.land a.b c.b)) c) a

def cvOp (b : Fin 8) : Bool := b.val % 2 == 1

lemma pair_picked (h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a c : XW) :
    pair h a c = true → ∃ b : Fin 8, pairOne (cvOp b) h a c = true := by
  have h0 : cvOp 0 = false := rfl
  have h1 : cvOp 1 = true := rfl
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,pairOne,bR]
  intro h'
  cases hon : h w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · rw [hon, Bool.cond_false] at h'
    exact ⟨1, by simpa only [h1, Bool.cond_true] using h'⟩
  · exact ⟨0, by simpa only [h0, Bool.cond_false] using hon⟩

lemma scan_picked (f : XW → Bool) (q : Fin 8 → XW → Bool) (v : List XW)
    (hp : picked f q) :
    scan f v = true → ∃ b, scan (q b) v = true := by
  induction v with
  | nil => simp [scan]
  | cons a v ih =>
    have hu (F : XW → Bool) :
        scan F (a :: v) = (bif F a then true else scan F v) := by
      change Bool.rec (motive := fun _ => Bool) (scan F v) true (F a) = _
      rw [bR]
    simp only [hu]
    cases h : f a
    · simp only [h, Bool.cond_false]
      intro hr
      obtain ⟨b,hb⟩ := ih hr
      exact ⟨b,by rw [hb]; cases q b a <;> rfl⟩
    · intro _
      obtain ⟨b,hb⟩ := hp a h
      exact ⟨b,by rw [hb]; rfl⟩

lemma pairsC_picked (H : ℕ) (a : XW → XW → Bool) (q : Fin 8 → XW → XW → Bool)
    (hp : ∀ x, picked (a x) (fun b => q b x)) (xs : List XW) :
    pairsC H a xs = true → ∃ b, pairsC H (q b) xs = true := by
  induction xs with
  | nil => simp [pairsC]
  | cons x xs ih =>
    have hu (F : XW → XW → Bool) : pairsC H F (x :: xs) =
        (bif scan (fun e => bif hb H (x.s + e.s) then F x e else false) xs
          then true else pairsC H F xs) := by
      change Bool.rec (motive := fun _ => Bool) (pairsC H F xs) true
        (scan (fun e => Bool.rec (motive := fun _ => Bool) false (F x e) (hb H (x.s + e.s))) xs) = _
      simp only [bR]
    have hp' : picked (fun e => bif hb H (x.s + e.s) then a x e else false)
        (fun b e => bif hb H (x.s + e.s) then q b x e else false) := by
      intro e
      cases hc : hb H (x.s + e.s)
      · simp [hc]
      · simpa [hc] using hp x e
    simp only [hu]
    cases hc : scan (fun e => bif hb H (x.s + e.s) then a x e else false) xs
    · simp only [hc, Bool.cond_false]
      intro h
      obtain ⟨b,hb⟩ := ih h
      refine ⟨b, ?_⟩
      rw [hb]
      cases scan (fun e => bif PEqualNP.Outside.L_meta_32159_aux.hb H (x.s + e.s) then q b x e else false) xs <;> rfl
    · intro _
      obtain ⟨b,hb⟩ := scan_picked _ _ xs hp' hc
      exact ⟨b, by rw [hb]; rfl⟩

noncomputable def nodePicked (NN : Nat) (f : Nat → List W → Bool) (d : Bool)
    (l m g e n z : Nat) (v : List W) (H : Nat) (kind : Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool)
    (pairsC H (pairOne kind (f0 h)) (fs xs))
    (Bool.rec (motive := fun _ => Bool) (pairsC H (pairOne kind (f1 h)) (fs xs))
      (pairsC H (pairOne kind (f2 h)) (fs xs)) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v)) (mid f m g e (Nat.pred n) z v)

lemma node_picked (nn : ℕ) (f : ℕ → List W → Bool) (d : Bool)
    (l m g e n z : ℕ) (v : List W) (H : ℕ) :
    nodeC nn f d l m g e n z v (fun h xs => pairsC H h (fs xs)) = true →
      ∃ b : Fin 8, nodePicked nn f d l m g e n z v H (cvOp b) = true := by
  simp only [nodeC, nodePicked, bR]
  cases hn : Nat.ble n e
  · simp only [hn, Bool.cond_false]
    exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _
  · simp only [hn, Bool.cond_true]
    cases hs : Nat.ble n.succ e
    · simp only [hs, Bool.cond_false]
      exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _
    · simp only [hs, Bool.cond_true]
      exact pairsC_picked _ _ _ (fun _ _ => pair_picked _ _ _) _

noncomputable def topPairPicked (NN AA HX HY l m g K H ph k t z : ℕ)
    (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodePicked NN (look1C NN AA HX HY l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v H kind))) true (Nat.ble v.length 1)

lemma topPair_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) :
    topCC nn aa hx hy l m g K H ph k t z v = true →
      ∃ b : Fin 8, topPairPicked nn aa hx hy l m g K H ph k t z v (cvOp b) = true := by
  simp only [topCC, topPairPicked, bR]
  cases ht : Nat.ble v.length 1
  · simp only [ht, Bool.cond_false]
    apply tst_picked
    intro y h
    dsimp only at h ⊢
    cases hx' : nodeC nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))
    · simp only [hx', Bool.cond_false] at h
      refine ⟨0, ?_⟩
      rw [h]
      cases nodePicked nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v H (cvOp 0) <;> rfl
    · obtain ⟨b,hb⟩ := node_picked _ _ _ _ _ _ _ _ _ _ _ hx'
      exact ⟨b, by simp only [hb, Bool.cond_true]⟩
  · simp only [ht, Bool.cond_true]
    exact fun _ => ⟨0,by simp⟩

noncomputable def startPairPicked (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (kind : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPairPicked NN AA HX HY l m g K H ph K t z r kind) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

lemma startPair_picked (nn aa hx hy l m g B K t p H ph : ℕ) :
    picked (startvC nn aa hx hy l m g B K t p H ph)
      (fun b v => startPairPicked nn aa hx hy l m g B K t p H ph v (cvOp b)) := by
  intro v
  simp only [startvC, startPairPicked, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact topPair_picked _ _ _ _ _ _ _ _ _ _ _ _ _ _

noncomputable def chkPairPicked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startPairPicked nn aa hx hy l m g B K t p H ph r kind)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma noNodePicked {v : List W} {H : ℕ} (h : possibleInputPair H v = false)
    (nn : ℕ) (d kind : Bool) (l m g e n z : ℕ) (f : ℕ → List W → Bool) :
    nodePicked nn f d l m g e n z v H kind = false := by
  simp only [nodePicked, pairImpossible _ h, bR, Bool.cond_self]

lemma inactiveTopPicked {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g K k z : ℕ) (kind : Bool) :
    topPairPicked nn aa hx hy l m g K H ph k t z v kind = false := by
  obtain ⟨hl, hm, hp⟩ := relevantStart_facts h
  simp only [topPairPicked, hl, noNodePicked hp, bR]
  rcases hm with hm | ⟨rfl, hv⟩
  · simp only [hm, Bool.cond_false, tst_const_false]
  · simp only [noMoves hv, Bool.cond_self, tst_const_false]

lemma inactiveStartPicked {t H ph : ℕ} {v : List W} (h : relevantStart t H ph v = false)
    (nn aa hx hy l m g B K p : ℕ) (kind : Bool) :
    startPairPicked nn aa hx hy l m g B K t p H ph v kind = false := by
  simp only [startPairPicked, child, st_eq, inactiveTopPicked h, bR, Bool.cond_self]

noncomputable def chkPairFast (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p v =>
    startPairPicked nn aa hx hy l m g B K t p H ph v kind)

lemma chkPairFast_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) :
    chkPairFast E Q Z K t H ph kind = chkPairPicked E Q Z K t H ph kind := by
  unfold chkPairFast
  rw [searchInputs_eq (fun nn aa hx hy l m g B p _ h =>
    inactiveStartPicked h nn aa hx hy l m g B K p kind)]
  rfl

lemma chkPair_picked (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ b : Bool, chkPairPicked E Q Z K t H ph b = false) : chk E Q Z K t H ph = false := by
  suffices chk E Q Z K t H ph = true → False by
    cases he : chk E Q Z K t H ph
    · rfl
    · exact (this he).elim
  intro hex
  simp only [chk, chkPairPicked, frc_eq, st_eq] at h hex
  obtain ⟨b,hb⟩ := anySub_picked _ _ _ _ _ _ (startPair_picked _ _ _ _ _ _ _ _ _ _ _ _ _) _ hex
  exact Bool.noConfusion ((h (cvOp b)).symm.trans hb)

end BinaryPartition

lemma ins_distribute (o : W) (v : List W) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (h : picked f g) : ins o v f = true → ∃ b, ins o v (g b) = true := by
  induction v generalizing f g with
  | nil => exact h [o]
  | cons a r ih =>
    have step (u : List W → Bool) : ins o (a :: r) u =
        (bif Nat.ble a.s o.s then (bif Nat.beq o.s a.s then false else u (o :: a :: r))
          else ins o r (fun ws => u (a :: ws))) := by
      change Bool.rec (motive := fun _ => Bool) (ins o r (fun ws => u (a :: ws)))
        (Bool.rec (motive := fun _ => Bool) (u (o :: a :: r)) false (Nat.beq o.s a.s))
        (Nat.ble a.s o.s) = _
      rw [bR,bR]
    simp only [step]
    cases hle : Nat.ble a.s o.s
    · simp only [hle,Bool.cond_false]
      exact ih (f := fun ws => f (a :: ws)) (g := fun b ws => g b (a :: ws)) (fun ws => h (a :: ws))
    · cases he : Nat.beq o.s a.s
      · simpa only [he,hle,Bool.cond_true,Bool.cond_false] using h (o :: a :: r)
      · simp [he,hle]

lemma put_distribute (m s x y : ℕ) (v : List W) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (h : picked f g) : put m s x y v f = true → ∃ b, put m s x y v (g b) = true := by
  simp only [put,st_eq,bR]
  cases h0 : Nat.beq s 0 <;> cases h1 : Nat.beq s m <;> simp only [h0,h1,Bool.cond_true,Bool.cond_false,Bool.false_eq_true,false_implies]
  exact ins_distribute _ _ h

lemma child_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (free z : ℕ) (mk : (List W → Bool) → Bool) (mk_distribute : ∀ p q, picked p q → mk p = true → ∃ b, mk (q b) = true)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    child f free mk z = true → ∃ b, child (g b) free mk z = true := by
  simp only [child,st_eq,bR]
  cases hb : Nat.beq (z &&& free) free
  · simp [hb]
  · simpa only [hb,Bool.cond_true] using mk_distribute (f z) (fun b => g b z) (h z)

lemma kids_unfold (ch : ((List W → Bool) → Bool) → ℕ → Bool) (e n z x y a c : ℕ)
    (oa oc : Bool) (mk : (List W → Bool) → Bool) :
    kids ch e n z x y a c oa oc mk =
      ((oa && oc && ch (fun f => mk (fun r => rm a c r f)) z) ||
      ((oc && Nat.ble (n+1) e && ch (fun f => mk (fun r => rm c c r f)) (z-x)) ||
      ((oa && Nat.ble (n+1) e && ch (fun f => mk (fun r => rm a a r f)) (z-y)) ||
       (Nat.ble (n+2) e && ch mk (z-x-y))))) := by
  simp only [kids,bR]
  cases oa <;> cases oc <;> cases Nat.ble (n+1) e <;> cases Nat.ble (n+2) e <;> simp <;>
    (try rw [Bool.eq_iff_iff]) <;> (try simp) <;> (try simp only [← Bool.not_eq_true]) <;> tauto

lemma kids_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (free e n z x y a c : ℕ) (oa oc : Bool) (mk : (List W → Bool) → Bool)
    (hm : ∀ p q, picked p q → mk p = true → ∃ b, mk (q b) = true)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    kids (child f free) e n z x y a c oa oc mk = true →
    ∃ b, kids (child (g b) free) e n z x y a c oa oc mk = true := by
  have cm (p q k : ℕ) : child f free (fun f => mk fun r => rm p q r f) k = true →
      ∃ b, child (g b) free (fun f => mk fun r => rm p q r f) k = true := by
    refine child_distribute free k _ ?_ h
    intro u v huv
    simp only [rm_eq]
    exact hm (fun r => u (r.filter _)) (fun b r => v b (r.filter _)) (fun r => huv (r.filter _))
  rw [kids_unfold]
  simp only [Bool.or_eq_true,Bool.and_eq_true]
  rintro (⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩)
  · obtain ⟨b,hb⟩ := cm a c z h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inl ⟨h1,hb⟩
  · obtain ⟨b,hb⟩ := cm c c (z-x) h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inl ⟨h1,hb⟩)
  · obtain ⟨b,hb⟩ := cm a a (z-y) h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inr (Or.inl ⟨h1,hb⟩))
  · obtain ⟨b,hb⟩ := child_distribute free (z-x-y) mk hm h h2
    refine ⟨b, ?_⟩
    simp only [kids_unfold,Bool.or_eq_true,Bool.and_eq_true]
    exact Or.inr (Or.inr (Or.inr ⟨h1,hb⟩))

lemma mid_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (m free e n z : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    mid f m free e n z v a c da dc s x y = true →
      ∃ b, mid (g b) m free e n z v a c da dc s x y = true := by
  simp only [mid,st_eq,bR]
  cases hb : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) free) free
  · simp [hb]
  · simpa only [hb,Bool.cond_true] using
      kids_distribute free e n (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) a.c c.c a.s c.s
        (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)
        (fun _ _ => put_distribute m s x y v) h

lemma pairs_distribute (f : XW → XW → Bool) (g : Fin 8 → XW → XW → Bool)
    (h : ∀ x, picked (f x) (fun b => g b x)) (v : List XW) :
    pairs f v = true → ∃ b, pairs (g b) v = true := by
  induction v with
  | nil => simp [pairs]
  | cons a r ih =>
    have he (u : XW → XW → Bool) : pairs u (a::r) = bif scan (u a) r then true else pairs u r := by
      change Bool.rec (motive := fun _ => Bool) (pairs u r) true (scan (u a) r) = _
      rw [bR]
    simp only [he]
    cases hb : scan (f a) r
    · simp only [hb,Bool.cond_false]
      intro ht
      obtain ⟨b,hb⟩ := ih ht
      exact ⟨b, by rw [hb]; cases scan (g b a) r <;> rfl⟩
    · simp only [hb,Bool.cond_true]
      intro _
      obtain ⟨b,hb⟩ := scan_picked _ _ r (h a) hb
      exact ⟨b,by rw [hb]; rfl⟩

lemma mode_distribute {f : ℕ → List W → Bool} {g : Fin 8 → ℕ → List W → Bool}
    (m free e n z : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ)
    (h : ∀ j, picked (f j) (fun b => g b j)) :
    modeF n e (mid f m free e n.pred z v) a c da dc s x y = true →
      ∃ b, modeF n e (mid (g b) m free e n.pred z v) a c da dc s x y = true := by
  have mid' := mid_distribute m free e n.pred z v a c da dc s x y h
  unfold modeF
  cases hn : Nat.ble n e
  · simp only [hn,Bool.cond_false,f0,bR]
    cases ha : Nat.beq (Nat.lor da dc) 0
    · simp [ha]
    · simpa only [ha,Bool.cond_true] using mid'
  · simp only [hn,Bool.cond_true]
    cases hs : Nat.ble n.succ e
    · simp only [hs,Bool.cond_false,f1,bR]
      cases ha : (bif Nat.beq da 0 then true else Nat.beq dc 0)
      · simp [ha]
      · simpa only [ha,Bool.cond_true] using mid'
    · simpa only [hs,Bool.cond_true,f2] using mid'

lemma pairOne_distribute (d : Bool) {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pairOne d f a c = true → ∃ b, pairOne d (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  cases d <;> simp only [pairOne,Bool.cond_false,Bool.cond_true] <;> exact h _ _ _ _ _ _ _

lemma nodeC_as_mode (NN : ℕ) (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    nodeC NN f d l m g e n z v go = go (pair (modeF n e (mid f m g e n.pred z v))) (mkXC NN d l (wstC NN d l v) v) := by
  unfold nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma pickedNode_as_mode (NN : ℕ) (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (H : ℕ) (kind : Bool) :
    nodePicked NN f d l m g e n z v H kind =
      pairsC H (pairOne kind (modeF n e (mid f m g e n.pred z v))) (fs (mkXC NN d l (wstC NN d l v) v)) := by
  unfold nodePicked modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl

lemma nodePicked_distribute {f : ℕ → List W → Bool} {branches : Fin 8 → ℕ → List W → Bool}
    (NN : ℕ) (d : Bool) (l m g e n z : ℕ) (v : List W) (H : ℕ) (kind : Bool)
    (h : ∀ j, picked (f j) (fun b => branches b j)) :
    nodePicked NN f d l m g e n z v H kind = true →
      ∃ b, nodePicked NN (branches b) d l m g e n z v H kind = true := by
  simp only [pickedNode_as_mode]
  exact pairsC_picked H _ _ (fun x y => pairOne_distribute kind
    (fun _ _ _ _ _ _ _ => mode_distribute m g e n z v _ _ _ _ _ _ _ h) x y) _

lemma look1C_step (nn aa hx hy l m g K fuel k t z : ℕ) (v : List W) :
    look1C nn aa hx hy l m g K fuel.succ k t z v =
      cvC nn (pos t) l v (bif Nat.ble v.length 1 then true else
        tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y)) := by
  change cvC nn (pos t) l v (Bool.rec (motive := fun _ => Bool)
      (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y) true
          (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) = _
  simp only [bR]

def nextPairPred (b : ℕ) (p : XW → XW → Bool) (a c : XW) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (p a c) (Nat.beq (((a.s + c.s) % MM) % 8) b)

lemma nextPairPred_picked (p : XW → XW → Bool) (a : XW) :
    picked (p a) (fun b => nextPairPred b p a) := by
  intro c h
  refine ⟨⟨((a.s + c.s) % MM) % 8, Nat.mod_lt _ (by decide)⟩, ?_⟩
  simpa only [nextPairPred, bR, Nat.beq_refl, Bool.cond_true] using h

def nextPairS (b : ℕ) (p : XW → XW → Bool) (xs : List XW) : Bool :=
  pairsS (nextPairPred b p) xs

def nextPairN (b : ℕ) (p : XW → XW → Bool) (xs : List XW) : Bool :=
  pairsN (nextPairPred b p) xs

lemma nextPairS_picked (p : XW → XW → Bool) (xs : List XW) :
    pairsS p xs = true → ∃ b : Fin 8, nextPairS b p xs = true :=
  pairs_distribute _ _ (nextPairPred_picked p) _

lemma nextPairN_picked (p : XW → XW → Bool) (xs : List XW) :
    pairsN p xs = true → ∃ b : Fin 8, nextPairN b p xs = true := by
  simp only [nextPairN, pairsN, bR]
  cases hs : pairs p (fr xs)
  · simp only [Bool.cond_false]
    intro h
    obtain ⟨b, hb⟩ := scan_picked _ _ _
      (fun a => scan_picked _ _ _ (nextPairPred_picked p a)) h
    refine ⟨b, ?_⟩
    simp only [hb, Bool.cond_self]
  · intro _
    obtain ⟨b, hb⟩ := pairs_distribute _ _ (nextPairPred_picked p) _ hs
    exact ⟨b, by simp only [hb, Bool.cond_true]⟩

noncomputable def mvNext (NN AA HX HY bin : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s => nots (fun q' z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub (Nat.sub k 1) s) v (fun y =>
          nodeC NN (F (Nat.sub k 3) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z (Nat.succ q) v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z 0 v (v.filter fun a => a.s % 8 == bin))) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v (nextPairN bin))) v.length
lemma prdNots_picked (t : ℕ) (f : ℕ → ℕ → ℕ → List W → Bool)
    (m g n z q : ℕ) (e : ℕ → ℕ) (v : List W) :
    prd t (fun s => nots (f s) m g (e s) n z q v v) = true →
    ∃ b : Fin 8, prd t (fun s => nots (f s) m g (e s) n z q v
      (v.filter fun a => a.s % 8 == (b : ℕ))) = true := by
  cases t with
  | zero => simp [prd]
  | succ t => exact nots_some_bin (f t) m g (e t) n z q v v

lemma mvNext_picked (nn aa hx hy l m g k t z : ℕ)
    (F : ℕ → ℕ → ℕ → List W → Bool) (v : List W) (y : ℕ) :
    mvC nn aa hx hy F l m g k t z v y = true →
    ∃ b : Fin 8, mvNext nn aa hx hy b F l m g k t z v y = true := by
  simp only [mvC, mvNext, bR]
  cases hd : nodeC nn (F (Nat.sub k 1) t) (pos t) l m g
      (Nat.sub (Nat.sub k t) y) v.length z v pairsN
  · simp only [Bool.cond_false]
    intro h
    obtain ⟨b, hb⟩ := prdNots_picked t _ m g v.length z 0 _ v h
    exact ⟨b, by simp only [hb, Bool.cond_self]⟩
  · intro _
    rw [nodeC_as_mode] at hd
    obtain ⟨b, hb⟩ := nextPairN_picked _ _ hd
    exact ⟨b, by simp only [nodeC_as_mode, hb, Bool.cond_true]⟩

noncomputable def look1Next (nn aa hx hy l m g K : ℕ) (bin : ℕ) :
    ℕ → ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, _, _ => Nat.beq bin 0
  | fuel + 1, k, t, z, v =>
    cvC nn (pos t) l v (Bool.rec (motive := fun _ => Bool) (tstC nn aa hx hy (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool)
        (mvNext nn aa hx hy bin (lookC nn aa hx hy l m g K) l m g k t z v y) true
        (nodeC nn (look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t)
          (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (nextPairS bin))))
        (Nat.beq bin 0) (Nat.ble v.length 1))

lemma look1Next_picked (nn aa hx hy l m g K fuel k t : ℕ) :
    ∀ z, picked (look1C nn aa hx hy l m g K fuel k t z)
      (fun b => look1Next nn aa hx hy l m g K b fuel k t z) := by
  intro z v
  cases fuel with
  | zero =>
    intro _
    exact ⟨0, rfl⟩
  | succ fuel =>
    rw [look1C_step]
    simp only [look1Next, cvC, bR]
    cases hc : Nat.beq (covC nn (pos t) l v) l
    · simp [hc]
    · simp only [hc, Bool.cond_true]
      cases hv : Nat.ble v.length 1
      · simp only [Bool.cond_false]
        apply tst_picked
        intro y h
        let f := look1C nn aa hx hy l m g K fuel (Nat.sub k 1) t
        let e := Nat.sub (Nat.sub k t) y
        cases hd : nodeC nn f (pos t) l m g e v.length z v pairsS
        · have hm : mvC nn aa hx hy (lookC nn aa hx hy l m g K) l m g k t z v y = true := by
            simpa only [f, e, hd, Bool.cond_false, Bool.or_false] using h
          obtain ⟨b, hb⟩ := mvNext_picked nn aa hx hy l m g k t z _ v y hm
          exact ⟨b, by simp only [hb, Bool.cond_self]⟩
        · rw [nodeC_as_mode] at hd
          obtain ⟨b, hb⟩ := nextPairS_picked _ _ hd
          refine ⟨b, ?_⟩
          simp only [nodeC_as_mode, hb, Bool.cond_true, f, e]
      · exact fun _ => ⟨0, rfl⟩

noncomputable def topPairNext (NN AA HX HY l m g K H ph k t z : ℕ)
    (v : List W) (kind : Bool) (bin : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false
        (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (nodePicked NN (look1Next NN AA HX HY l m g K bin K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y)
        v.length z v H kind))) true (Nat.ble v.length 1)

lemma topPairNext_picked (nn aa hx hy l m g K H ph k t z : ℕ) (v : List W) (kind : Bool) :
    topPairPicked nn aa hx hy l m g K H ph k t z v kind = true →
      ∃ b : Fin 8, topPairNext nn aa hx hy l m g K H ph k t z v kind b = true := by
  simp only [topPairPicked, topPairNext, bR]
  cases ht : Nat.ble v.length 1
  · simp only [ht, Bool.cond_false]
    apply tst_picked
    intro y h
    dsimp only at h ⊢
    cases hx' : nodePicked nn (look1C nn aa hx hy l m g K K (Nat.sub k 1) t) (pos t) l m g
        (Nat.sub (Nat.sub k t) y) v.length z v H kind
    · simp only [hx', Bool.cond_false] at h
      refine ⟨0, ?_⟩
      simp only [h, Bool.cond_self]
    · obtain ⟨b,hb⟩ := nodePicked_distribute nn (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v H kind
        (look1Next_picked nn aa hx hy l m g K K (Nat.sub k 1) t) hx'
      exact ⟨b, by simp only [hb, Bool.cond_true]⟩
  · simp only [ht, Bool.cond_true]
    exact fun _ => ⟨0,by simp⟩

noncomputable def startPairNext (NN AA HX HY l m g B K t p H ph : ℕ) (v : List W) (kind : Bool) (bin : ℕ) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topPairNext NN AA HX HY l m g K H ph K t z r kind bin) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)

lemma startPairNext_picked (nn aa hx hy l m g B K t p H ph : ℕ) (kind : Bool) :
    picked (fun v => startPairPicked nn aa hx hy l m g B K t p H ph v kind)
      (fun b v => startPairNext nn aa hx hy l m g B K t p H ph v kind b) := by
  intro v
  simp only [startPairPicked, startPairNext, child, st_eq, bR]
  cases h : hasP p v
  · simp [h]
  · simp only [h, Bool.cond_true]
    cases hb : Nat.ble v.length (Nat.sub K.succ t)
    · simp [hb]
    · simp only [hb, Bool.cond_true]
      cases hz : Nat.beq (Nat.land (Nat.sub B (sumc v)) g) g
      · simp [hz]
      · simp only [hz, Bool.cond_true]
        exact topPairNext_picked _ _ _ _ _ _ _ _ _ _ _ _ _ v kind

noncomputable def chkPairNext (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool) (bin : ℕ) : Bool :=
  searchInputs E Q Z K t H ph (fun nn aa hx hy l m g B p v =>
    startPairNext nn aa hx hy l m g B K t p H ph v kind bin)

lemma guardStart_picked (t H ph : ℕ) {f : List W → Bool} {g : Fin 8 → List W → Bool}
    (pickedTest : picked f g) :
    picked (guardStart t H ph f) (fun b => guardStart t H ph (g b)) := by
  intro v
  unfold guardStart
  cases h : relevantStart t H ph v
  · simp
  · simpa [h] using pickedTest v

lemma chkPair_next (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) (kind : Bool)
    (checked : ∀ b : Fin 8, chkPairNext E Q Z K t H ph kind b = false) :
    chkPairPicked E Q Z K t H ph kind = false := by
  rw [← chkPairFast_eq]
  refine Bool.eq_false_iff.mpr fun h => ?_
  simp only [chkPairFast, chkPairNext, searchInputs, frc_eq, st_eq] at h checked
  obtain ⟨b, hb⟩ := anySub_picked _ _ _ _ _ _
    (guardStart_picked t H ph (startPairNext_picked _ _ _ _ _ _ _ _ _ _ _ _ _ kind)) _ h
  exact Bool.noConfusion ((checked b).symm.trans hb)

section inst_data
def r5 : List (ℕ × ℕ) := [(31, 1), (47, 1), (55, 1), (59, 2), (61, 1), (62, 2), (79, 1), (87, 4), (91, 2), (93, 2), (94, 4), (103, 1), (107, 1), (109, 1), (110, 1), (115, 2), (117, 1), (118, 4), (121, 1), (122, 2), (124, 1), (143, 1), (151, 1), (155, 1), (157, 2), (158, 2), (167, 1), (171, 2), (173, 4), (174, 2), (179, 1), (181, 1), (182, 2), (185, 2), (186, 2), (188, 2), (199, 1), (205, 2), (206, 1), (211, 1), (213, 2), (214, 4), (217, 1), (218, 1), (220, 2), (229, 1), (230, 1), (233, 1), (236, 1), (242, 1), (244, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk5 : r5.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma i5 : ∀ e ∈ r5, Imp [] e.1 e.2 := okAll (T := []) chk5 (by simp)
def rs5 : List (ℕ × ℕ) := r5
lemma is5 : ∀ e ∈ rs5, Imp [] e.1 e.2 := i5
def r4 : List (ℕ × ℕ) := [(15, 3), (23, 4), (27, 4), (29, 4), (30, 5), (39, 3), (43, 4), (45, 4), (46, 4), (51, 4), (53, 3), (54, 5), (57, 4), (58, 3), (60, 4), (71, 4), (75, 2), (77, 4), (78, 4), (83, 5), (85, 5), (86, 7), (89, 4), (90, 5), (92, 5), (99, 2), (101, 3), (102, 4), (105, 3), (106, 2), (108, 3), (113, 2), (114, 5), (116, 4), (120, 2), (135, 3), (139, 2), (141, 5), (142, 4), (147, 3), (149, 4), (150, 5), (153, 4), (154, 4), (156, 3), (163, 2), (165, 4), (166, 4), (169, 5), (170, 3), (172, 5), (177, 2), (178, 4), (180, 4), (184, 3), (195, 1), (197, 4), (198, 4), (201, 2), (202, 1), (204, 4), (209, 2), (210, 4), (212, 5), (216, 2), (225, 1), (226, 1), (228, 3), (232, 1), (240, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk4 : r4.all (fun e => okE [] (pr rs5 e.1) e) = true := by decide +kernel
lemma i4 : ∀ e ∈ r4, Imp [] e.1 e.2 := okAll (T := rs5) chk4 is5
def rs4 : List (ℕ × ℕ) := r4 ++ rs5
lemma is4 : ∀ e ∈ rs4, Imp [] e.1 e.2 := apI i4 is5
def r3 : List (ℕ × ℕ) := [(7, 6), (11, 5), (13, 7), (14, 7), (19, 7), (21, 7), (22, 8), (25, 7), (26, 6), (28, 6), (35, 5), (37, 6), (38, 7), (41, 7), (42, 5), (44, 7), (49, 5), (50, 6), (52, 7), (56, 5), (67, 5), (69, 7), (70, 7), (73, 5), (74, 5), (76, 7), (81, 6), (82, 8), (84, 8), (88, 6), (97, 4), (98, 5), (100, 6), (104, 4), (112, 5), (131, 4), (133, 7), (134, 7), (137, 6), (138, 5), (140, 6), (145, 5), (146, 7), (148, 6), (152, 5), (161, 5), (162, 5), (164, 7), (168, 6), (176, 5), (193, 4), (194, 4), (196, 7), (200, 4), (208, 5), (224, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk3 : r3.all (fun e => okE [] (pr rs4 e.1) e) = true := by decide +kernel
lemma i3 : ∀ e ∈ r3, Imp [] e.1 e.2 := okAll (T := rs4) chk3 is4
def rs3 : List (ℕ × ℕ) := r3 ++ rs4
lemma is3 : ∀ e ∈ rs3, Imp [] e.1 e.2 := apI i3 is4
def r2 : List (ℕ × ℕ) := [(3, 8), (5, 10), (6, 10), (9, 9), (10, 8), (12, 9), (17, 9), (18, 9), (20, 9), (24, 9), (33, 8), (34, 8), (36, 10), (40, 8), (48, 8), (65, 8), (66, 8), (68, 10), (72, 8), (80, 9), (96, 7), (129, 8), (130, 8), (132, 9), (136, 8), (144, 8), (160, 8), (192, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk2 : r2.all (fun e => okE [] (pr rs3 e.1) e) = true := by decide +kernel
lemma i2 : ∀ e ∈ r2, Imp [] e.1 e.2 := okAll (T := rs3) chk2 is3
def rs2 : List (ℕ × ℕ) := r2 ++ rs3
lemma is2 : ∀ e ∈ rs2, Imp [] e.1 e.2 := apI i2 is3
def r1 : List (ℕ × ℕ) := [(1, 12), (2, 11), (4, 12), (8, 12), (16, 12), (32, 11), (64, 11), (128, 11)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk1 : r1.all (fun e => okE [] (pr rs2 e.1) e) = true := by decide +kernel
lemma i1 : ∀ e ∈ r1, Imp [] e.1 e.2 := okAll (T := rs2) chk1 is2
def rs1 : List (ℕ × ℕ) := r1 ++ rs2
lemma is1 : ∀ e ∈ rs1, Imp [] e.1 e.2 := apI i1 is2
def pin4 : List (ℕ × ℕ) := [(525, 2), (533, 3), (537, 3), (540, 3), (549, 3), (553, 3), (556, 3), (561, 3), (564, 5), (568, 3), (581, 3), (585, 3), (588, 3), (593, 3), (596, 5), (600, 3), (609, 3), (612, 5), (616, 3), (624, 5), (645, 2), (649, 2), (652, 2), (657, 1), (660, 3), (664, 1), (673, 1), (676, 3), (680, 1), (688, 2), (705, 1), (708, 3), (712, 1), (720, 2), (736, 2), (1035, 1), (1043, 3), (1049, 3), (1050, 3), (1059, 1), (1065, 3), (1066, 1), (1073, 1), (1074, 3), (1080, 1), (1091, 2), (1097, 3), (1098, 2), (1105, 3), (1106, 5), (1112, 3), (1121, 2), (1122, 2), (1128, 2), (1136, 2), (1155, 2), (1161, 3), (1162, 2), (1169, 3), (1170, 5), (1176, 3), (1185, 2), (1186, 2), (1192, 2), (1200, 2), (1217, 4), (1218, 4), (1224, 4), (1232, 5), (1248, 3), (2055, 3), (2067, 3), (2069, 3), (2070, 2), (2083, 3), (2085, 5), (2086, 3), (2097, 3), (2098, 3), (2100, 3), (2115, 1), (2117, 3), (2118, 2), (2129, 1), (2130, 2), (2132, 2), (2145, 2), (2146, 1), (2148, 3), (2160, 1), (2179, 3), (2181, 5), (2182, 3), (2193, 3), (2194, 3), (2196, 3), (2209, 5), (2210, 3), (2212, 5), (2224, 3), (2241, 2), (2242, 1), (2244, 3), (2256, 1), (2272, 2), (4103, 5), (4107, 3), (4109, 3), (4110, 5), (4131, 3), (4133, 3), (4134, 5), (4137, 3), (4138, 3), (4140, 3), (4163, 5), (4165, 5), (4166, 7), (4169, 3), (4170, 5), (4172, 5), (4193, 3), (4194, 5), (4196, 5), (4200, 3), (4227, 2), (4229, 3), (4230, 5), (4233, 1), (4234, 2), (4236, 3), (4257, 1), (4258, 2), (4260, 3), (4264, 1), (4289, 2), (4290, 4), (4292, 5), (4296, 2), (4320, 2), (16391, 5), (16395, 3), (16397, 3), (16398, 3), (16403, 5), (16405, 5), (16406, 5), (16409, 3), (16410, 3), (16412, 3), (16419, 3), (16421, 3), (16422, 3), (16425, 2), (16426, 2), (16428, 2), (16433, 3), (16434, 3), (16436, 3), (16440, 2), (16515, 3), (16517, 3), (16518, 3), (16521, 2), (16522, 2), (16524, 2), (16529, 3), (16530, 3), (16532, 3), (16536, 2), (16545, 2), (16546, 2), (16548, 2), (16552, 3), (16560, 2), (32775, 3), (32779, 3), (32781, 5), (32782, 3), (32787, 2), (32789, 3), (32790, 2), (32793, 3), (32794, 2), (32796, 3), (32803, 3), (32805, 5), (32806, 3), (32809, 5), (32810, 3), (32812, 5), (32817, 3), (32818, 2), (32820, 3), (32824, 3), (32835, 2), (32837, 3), (32838, 2), (32841, 3), (32842, 2), (32844, 3), (32849, 2), (32850, 3), (32852, 2), (32856, 2), (32865, 3), (32866, 2), (32868, 3), (32872, 3), (32880, 2), (780, 3), (788, 3), (792, 2), (804, 3), (808, 2), (816, 2), (836, 3), (840, 2), (848, 2), (864, 2), (900, 3), (904, 2), (912, 2), (928, 2), (960, 2), (1290, 2), (1298, 3), (1304, 2), (1314, 2), (1320, 3), (1328, 2), (1346, 2), (1352, 3), (1360, 2), (1376, 3), (1410, 2), (1416, 3), (1424, 2), (1440, 3), (1472, 3), (1545, 3), (1553, 2), (1560, 2), (1569, 2), (1576, 2), (1584, 3), (1601, 2), (1608, 2), (1616, 3), (1632, 3), (1665, 2), (1672, 2), (1680, 3), (1696, 3), (1728, 3), (2565, 3), (2577, 2), (2580, 3), (2593, 2), (2596, 3), (2608, 2), (2625, 2), (2628, 3), (2640, 2), (2656, 2), (2689, 2), (2692, 3), (2704, 2), (2720, 2), (2752, 2), (3075, 2), (3089, 2), (3090, 3), (3105, 3), (3106, 2), (3120, 2), (3137, 3), (3138, 2), (3152, 2), (3168, 3), (3201, 3), (3202, 2), (3216, 2), (3232, 3), (3264, 3), (4358, 3), (4362, 2), (4364, 3), (4386, 2), (4388, 3), (4392, 2), (4418, 2), (4420, 3), (4424, 2), (4448, 2), (4482, 2), (4484, 3), (4488, 2), (4512, 2), (4544, 2), (5123, 3), (5129, 2), (5130, 3), (5153, 2), (5154, 3), (5160, 2), (5185, 3), (5186, 5), (5192, 3), (5216, 3), (5249, 3), (5250, 5), (5256, 3), (5280, 3), (5312, 5), (6147, 2), (6149, 3), (6150, 3), (6177, 2), (6178, 2), (6180, 3), (6209, 2), (6210, 2), (6212, 3), (6240, 2), (6273, 2), (6274, 2), (6276, 3), (6304, 2), (6336, 2), (9219, 2), (9225, 2), (9226, 2), (9233, 3), (9234, 3), (9240, 3), (9281, 2), (9282, 2), (9288, 2), (9296, 3), (9345, 2), (9346, 2), (9352, 2), (9360, 3), (9408, 2), (12291, 2), (12293, 3), (12294, 3), (12297, 2), (12298, 2), (12300, 3), (12353, 2), (12354, 2), (12356, 3), (12360, 2), (12417, 2), (12418, 2), (12420, 3), (12424, 2), (12480, 2), (18435, 3), (18437, 3), (18438, 3), (18449, 3), (18450, 3), (18452, 3), (18465, 3), (18466, 3), (18468, 3), (18480, 3), (18561, 3), (18562, 3), (18564, 3), (18576, 3), (18592, 3), (24579, 3), (24581, 3), (24582, 3), (24585, 3), (24586, 3), (24588, 3), (24593, 3), (24594, 3), (24596, 3), (24600, 3), (24705, 3), (24706, 3), (24708, 3), (24712, 3), (24720, 3), (33285, 3), (33289, 3), (33292, 3), (33297, 3), (33300, 3), (33304, 3), (33313, 3), (33316, 3), (33320, 3), (33328, 3), (33345, 3), (33348, 3), (33352, 3), (33360, 3), (33376, 3), (36867, 3), (36869, 3), (36870, 3), (36873, 3), (36874, 3), (36876, 3), (36897, 3), (36898, 3), (36900, 3), (36904, 3), (36929, 3), (36930, 3), (36932, 3), (36936, 3), (36960, 3), (49155, 3), (49157, 3), (49158, 3), (49161, 3), (49162, 3), (49164, 3), (49169, 3), (49170, 3), (49172, 3), (49176, 3), (49185, 3), (49186, 3), (49188, 3), (49192, 3), (49200, 3), (1800, 3), (1808, 3), (1824, 3), (1856, 3), (1920, 3), (3585, 3), (3600, 3), (3616, 3), (3648, 3), (3712, 3), (5378, 3), (5384, 3), (5408, 3), (5440, 3), (5504, 3), (7169, 3), (7170, 3), (7200, 3), (7232, 3), (7296, 3), (13313, 3), (13314, 3), (13320, 3), (13376, 3), (13440, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4 : pin4.all (fun e => okE [] (pr rs1 e.1) e) = true := by decide +kernel
lemma h4 : ∀ e ∈ pin4, Imp [] e.1 e.2 := okAll (T := rs1) v4 is1
def pv4 : List (ℕ × ℕ) := rs1 ++ pin4
lemma hv4 : ∀ e ∈ pv4, Imp [] e.1 e.2 := apI is1 h4
def pin3 : List (ℕ × ℕ) := [(517, 4), (521, 4), (524, 4), (529, 4), (532, 6), (536, 4), (545, 4), (548, 6), (552, 4), (560, 6), (577, 4), (580, 6), (584, 4), (592, 6), (608, 6), (641, 2), (644, 4), (648, 2), (656, 3), (672, 3), (704, 3), (1027, 3), (1033, 4), (1034, 3), (1041, 4), (1042, 6), (1048, 4), (1057, 3), (1058, 3), (1064, 3), (1072, 3), (1089, 5), (1090, 5), (1096, 5), (1104, 6), (1120, 4), (1153, 5), (1154, 5), (1160, 5), (1168, 6), (1184, 4), (1216, 7), (2051, 4), (2053, 6), (2054, 4), (2065, 4), (2066, 4), (2068, 4), (2081, 6), (2082, 4), (2084, 6), (2096, 4), (2113, 3), (2114, 2), (2116, 4), (2128, 2), (2144, 3), (2177, 6), (2178, 4), (2180, 6), (2192, 4), (2208, 6), (2240, 3), (4099, 6), (4101, 6), (4102, 8), (4105, 4), (4106, 6), (4108, 6), (4129, 4), (4130, 6), (4132, 6), (4136, 4), (4161, 6), (4162, 8), (4164, 8), (4168, 6), (4192, 6), (4225, 3), (4226, 5), (4228, 6), (4232, 3), (4256, 3), (4288, 5), (16387, 6), (16389, 6), (16390, 6), (16393, 4), (16394, 4), (16396, 4), (16401, 6), (16402, 6), (16404, 6), (16408, 4), (16417, 4), (16418, 4), (16420, 4), (16424, 3), (16432, 4), (16513, 4), (16514, 4), (16516, 4), (16520, 3), (16528, 4), (16544, 3), (32771, 4), (32773, 6), (32774, 4), (32777, 6), (32778, 4), (32780, 6), (32785, 4), (32786, 3), (32788, 4), (32792, 4), (32801, 6), (32802, 4), (32804, 6), (32808, 6), (32816, 4), (32833, 4), (32834, 3), (32836, 4), (32840, 4), (32848, 3), (32864, 4), (772, 4), (776, 3), (784, 3), (800, 3), (832, 3), (896, 3), (1282, 3), (1288, 4), (1296, 3), (1312, 4), (1344, 4), (1408, 4), (1537, 3), (1544, 3), (1552, 4), (1568, 4), (1600, 4), (1664, 4), (2561, 3), (2564, 4), (2576, 3), (2592, 3), (2624, 3), (2688, 3), (3073, 4), (3074, 3), (3088, 3), (3104, 4), (3136, 4), (3200, 4), (4354, 3), (4356, 4), (4360, 3), (4384, 3), (4416, 3), (4480, 3), (5121, 4), (5122, 6), (5128, 4), (5152, 4), (5184, 6), (5248, 6), (6145, 3), (6146, 3), (6148, 4), (6176, 3), (6208, 3), (6272, 3), (9217, 3), (9218, 3), (9224, 3), (9232, 4), (9280, 3), (9344, 3), (12289, 3), (12290, 3), (12292, 4), (12296, 3), (12352, 3), (12416, 3), (18433, 4), (18434, 4), (18436, 4), (18448, 4), (18464, 4), (18560, 4), (24577, 4), (24578, 4), (24580, 4), (24584, 4), (24592, 4), (24704, 4), (33281, 4), (33284, 4), (33288, 4), (33296, 4), (33312, 4), (33344, 4), (36865, 4), (36866, 4), (36868, 4), (36872, 4), (36896, 4), (36928, 4), (49153, 4), (49154, 4), (49156, 4), (49160, 4), (49168, 4), (49184, 4), (1792, 4), (3584, 4), (5376, 4), (7168, 4), (13312, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v3 : pin3.all (fun e => okE [] (pr pv4 e.1) e) = true := by decide +kernel
lemma h3 : ∀ e ∈ pin3, Imp [] e.1 e.2 := okAll (T := pv4) v3 hv4
def pv3 : List (ℕ × ℕ) := pv4 ++ pin3
lemma hv3 : ∀ e ∈ pv3, Imp [] e.1 e.2 := apI hv4 h3
def pin2 : List (ℕ × ℕ) := [(513, 5), (516, 7), (520, 5), (528, 7), (544, 7), (576, 7), (640, 4), (1025, 6), (1026, 6), (1032, 6), (1040, 7), (1056, 5), (1088, 8), (1152, 8), (2049, 7), (2050, 5), (2052, 7), (2064, 5), (2080, 7), (2112, 4), (2176, 7), (4097, 7), (4098, 9), (4100, 9), (4104, 7), (4128, 7), (4160, 9), (4224, 6), (16385, 7), (16386, 7), (16388, 7), (16392, 5), (16400, 7), (16416, 5), (16512, 5), (32769, 7), (32770, 5), (32772, 7), (32776, 7), (32784, 5), (32800, 7), (32832, 5), (768, 4), (1280, 5), (1536, 5), (2560, 4), (3072, 5), (4352, 4), (5120, 7), (6144, 4), (9216, 4), (12288, 4), (18432, 5), (24576, 5), (33280, 5), (36864, 5), (49152, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2 : pin2.all (fun e => okE [] (pr pv3 e.1) e) = true := by decide +kernel
lemma h2 : ∀ e ∈ pin2, Imp [] e.1 e.2 := okAll (T := pv3) v2 hv3
def pv2 : List (ℕ × ℕ) := pv3 ++ pin2
lemma hv2 : ∀ e ∈ pv2, Imp [] e.1 e.2 := apI hv3 h2
def pin1 : List (ℕ × ℕ) := [(512, 8), (1024, 9), (2048, 8), (4096, 10), (16384, 8), (32768, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1 : pin1.all (fun e => okE [] (pr pv2 e.1) e) = true := by decide +kernel
lemma h1 : ∀ e ∈ pin1, Imp [] e.1 e.2 := okAll (T := pv2) v1 hv2
def pv1 : List (ℕ × ℕ) := pv2 ++ pin1
lemma hv1 : ∀ e ∈ pv1, Imp [] e.1 e.2 := apI hv2 h1
def rootBounds : List (ℕ × ℕ) := pv1.filter (fun p => p.2 ≥ 5)
lemma rootBounds_sound : ∀ p ∈ rootBounds, Imp [] p.1 p.2 := fun p h => hv1 p (List.mem_of_mem_filter h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma root_p : pOk 0 rootBounds = true := by decide +kernel

private def graph : (Fin 8 → Bool) → Bool := fun x =>
  decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

private def witness : Circuit := ⟨[
   ⟨.or, [5, 0]⟩,
   ⟨.or, [7, 3]⟩,
   ⟨.and, [8, 9]⟩,
   ⟨.and, [1, 4]⟩,
   ⟨.or, [1, 0]⟩,
   ⟨.or, [6, 5]⟩,
   ⟨.and, [12, 13]⟩,
   ⟨.or, [4, 2]⟩,
   ⟨.and, [15, 6]⟩,
   ⟨.or, [3, 2]⟩,
   ⟨.and, [17, 7]⟩,
   ⟨.or, [10, 11]⟩,
   ⟨.or, [19, 14]⟩,
   ⟨.or, [20, 16]⟩,
   ⟨.or, [21, 18]⟩], 22⟩

lemma witness_basis : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

lemma witness_size : witness.gates.length = 15 := rfl

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7)

lemma f_graph (x : Fin 8 → Bool) : f x = graph x := by
  have hx : f x = true ↔ (x 0 = true ∧ x 3 = true) ∨ (x 1 = true ∧ x 4 = true) ∨ (x 0 = true ∧ x 5 = true) ∨ (x 1 = true ∧ x 5 = true) ∨ (x 3 = true ∧ x 5 = true) ∨ (x 0 = true ∧ x 6 = true) ∨ (x 1 = true ∧ x 6 = true) ∨ (x 2 = true ∧ x 6 = true) ∨ (x 4 = true ∧ x 6 = true) ∨ (x 0 = true ∧ x 7 = true) ∨ (x 2 = true ∧ x 7 = true) ∨ (x 3 = true ∧ x 7 = true) ∨ (x 5 = true ∧ x 7 = true) := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  unfold graph
  rw [Bool.eq_iff_iff, hx, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h)
    · exact ⟨0, by decide, by simpa using h⟩
    · exact ⟨1, by decide, by simpa using h⟩
    · exact ⟨2, by decide, by simpa using h⟩
    · exact ⟨3, by decide, by simpa using h⟩
    · exact ⟨4, by decide, by simpa using h⟩
    · exact ⟨5, by decide, by simpa using h⟩
    · exact ⟨6, by decide, by simpa using h⟩
    · exact ⟨7, by decide, by simpa using h⟩
    · exact ⟨8, by decide, by simpa using h⟩
    · exact ⟨9, by decide, by simpa using h⟩
    · exact ⟨10, by decide, by simpa using h⟩
    · exact ⟨11, by decide, by simpa using h⟩
    · exact ⟨12, by decide, by simpa using h⟩
  · rintro ⟨i, hi, h⟩
    have hi' : i < 13 := hi
    interval_cases i <;> simp_all

set_option maxHeartbeats 5000000 in
lemma witness_eval (x : Fin 8 → Bool) : witness.eval (List.ofFn x) = graph x := by
  rw [← f_graph]
  simp only [witness, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  change ((((((x 5 || x 0) && (x 7 || x 3)) || (x 1 && x 4)) || ((x 1 || x 0) && (x 6 || x 5))) || ((x 4 || x 2) && x 6)) || ((x 3 || x 2) && x 7)) = f x
  unfold f
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

def EF : ℕ := (((((((((((((rawP0.getD 0 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 4 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 5 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 1 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 4 0 &&& rawP0.getD 6 0)) ||| (rawP0.getD 0 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 2 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 3 0 &&& rawP0.getD 7 0)) ||| (rawP0.getD 5 0 &&& rawP0.getD 7 0))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len0 : rawP0.length = 8 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 8 => (rawP0.getD v.val 0).testBit b) = rawP0.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len0]
  · intro i h1 h2
    have : i < rawP0.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 8 => (rawP0.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
theorem bridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 8 → Bool, D.eval (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) D.size (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
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
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hu : UniqueNot gates) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol Z0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ [] 0)) ∨
    ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ [] 0) ∧ Live Z0 (mz 0) (tz 0) gates.length 1 S0 := by
  let row : ℕ → Fin 8 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
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
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ [] 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hu hnot ⟨o, hout⟩

def allInputsNeeded (nn : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun w ws rest bits =>
      !Nat.beq (Nat.lor bits (covC nn d l ws)) l &&
        rest (Nat.lor bits (spC nn d l w.s))) v

lemma anySub_allInputs {nn : ℕ} {d : Bool} {l : ℕ} {v : List W} {bits : ℕ}
    (needed : allInputsNeeded nn d l v bits = true) (test : List W → Bool) :
    anySubC nn d l v bits test = test v := by
  induction v generalizing bits test with
  | nil => rfl
  | cons w ws ih =>
    let included := Nat.lor bits (spC nn d l w.s)
    let skip := Nat.beq (Nat.lor bits (covC nn d l ws)) l
    change (!skip && allInputsNeeded nn d l ws included) = true at needed
    simp only [Bool.and_eq_true] at needed
    have mustKeep : skip = false := Bool.eq_false_iff.mpr (fun h => by rw [h] at needed; simp at needed)
    change Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) false (anySubC nn d l ws bits test) skip)
      true (st included (fun c => anySubC nn d l ws c (fun r => test (w :: r)))) = _
    rw [st_eq, ih needed.2, mustKeep]
    cases test (w :: ws) <;> rfl


def rootPreparedWords : List W := [
  ⟨0x1ffffdffffdffffde00000000000000000000000000000000000000000000000000000000004d2d10bc00213409e0010f002780000000070000001c001c007000000003800003800e00000001c000038000000000000000000ffc00ffc00ffc00f7c0007c00003e00041043e00041f0002201f00021047c0008424010f0036d6ad5fff5adb56fffad7ffdbffe000000000000000000000000000000000000000000000000000000000026863f83919372c7, 0x1000000002000000004000000100000000000000008000000000000000001084000000000000000210800008421080000000000000084000000000001080000000000001084010800000021084200000000001084210842108421084200000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 0x4000000108400000000842108420000000000000000000000000000000000000000000001084210800000000000000000000000000000000000000000000000000000000010842000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4000000108400000000842108421000000002000000004000000100000000000000008001084210800000001084000000000000000210800008421080000000000000084010842000001080000000000001084010800000021084200000000001084210842108421084200000000000000000000000000000000000000000084210842000000000000000000000000000800000000, 3⟩,
  ⟨0x1ffffc00000000000ffffeffffef0000000000000000000000000000000000000000000000069a9002300000001180008c0046004d28804e00490138013804e000000026000026009800000013000026000000000000000000fc3c0803c0803c0043fe043fe0781f00208001f00200f8011080f80108003e0042121080f036d68000000000000000000000000b6d56abffeb6aafffafffbffe000000000000000000000000000000000a4cf9b63b5396fa1, 0x800000000000000000100000000000000008000000200000000400000000000000001000210842000000000000000008000004210802108000080200000000001004210842100000000010042108020000010842108001080000000000000000010842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 0x200000100021000000000000001084210840000000000000000000000000000000000000000000042108420000000000000000000000000000000000000000000000000000000108420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000100021000000800000001084210840100000000000000008000000200000000400000000042108421000210842000000000000000008000004210802108000080200000108421004210842100000000010042108020000010842108001080000000000000000010842108421084210000000000000000000000000080000000108421080000000000000000000040000000, 3⟩,
  ⟨0x1ffffc000000000000000007fffef8007fffefbffff77d80000000000000000000000004005810b0b5a60087000438021c120025521e00000870087021c1b5ac01160001160458269a488f00011c0000000000000000040204de20410204002102018024218e27c001188e7c8c473bec0806002002018100084008106002c00005adb000000000000000b0016abffe000000000000000dad6000000000000001b6db6fff800000d13f6ca4c6a68f91, 0x2000000004000000000000000010000000020000000800000000000000042100000000000000000000000000000000400004000040100401000000000108400000000000000000000010842008420004010842108421004000002108400000010002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 0x10000008000080000000000000000000002108421080000000000000000000000008420000000000000001084210842108421084000000000000000000000000000084200000000001084210842108420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000008000080000002000000004000002108421080010000000020000000800008420000000042100001084210842108421084000000000400004000040100401084200000108401084210842108420000010842008420004010842108421004000002108400000010002108400000000842100000000210842100000000200000008000004000002108400000000000100000, 3⟩,
  ⟨0x1ffffc000000000000000000000000000000000003ffff03e0ffffde00fb80000000400880c00108c40a58206310300000001019045040c440e103000010881490881c20610412440e61882800000000000000000809404094da89400044a0024a10024a08210022a0801130824855701f0114dcf007dc002500060040000018460002c00018000001000000086280002fff8000021084000585fff0001861b6fffb0c000fbc3fe9e6595ce57, 0x400000000800000001000000040000000080000000000020000000002008020004000040008021004000000000001000010040000000004200000100420080200840108420000000840000000004010042008420000000800008001004000040008001004010002000401004010040108021000000040000001000000800008001004010000000020, 0x2000400000200000000000000000000000000000000000000000000210842100000000000000000000000000000000000000000000000000000000002108421000000000000000000000000000000000000002108400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x2000400000200000000400000000800000001000000040000000080210842100020000000002008020004000040008021004000000000001000010042108421004200000100420080200840108420000000842108400004010042008420000000800008001004000040008001004010002000401004010040108021000000040000001000000800008001004010000000020, 3⟩,
  ⟨0xffffe0000007fffefbef0000000000000000000000000000000000000020004a02c0000000140000a00050169a80009000000240024009012528405802405801600000002800005000000000000000000820386003860038863e1c2201c0310fc7df7a00f0110078008100780842401e0210108480e30002d5fff0000000000000000000b6d4000000000000000000000dad6b5fff5b5fff7ffc00000000000000043f7419e9fb1f0e, 0x40000000080000000008000000200000000400000010000000001084000000000000000200000108000000200042000000000000002000420000010840000000004200000008001080200002100401080010000000400004210840000000000010840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000040000000080000000008000000200000000400000010000000001084000000000000000200000108000000200042000000000000002000420000010840000000004200000008001080200002100401080010000000400004210840000000000010840000000000000842108421084000000000000004000000100000004210840000000000000002000000, 3⟩,
  ⟨0xffffe00000000007fffef800000003ffff7bee00000000000000000800001289000a40ac00054002a00402c004916d00128012804a090012825800025009434d0001484902b0000000000000000021022110220c022411011537110080911042190cd7c40248040c465bdf720106008040240880c0000000580056fff80000000000601600000b68000000000000d800b5fff0000000001b6c0000036dffffcfa7fed0a0bad0c, 0x100000000200000000400000000000000001000000040000001000210000000000000010000000420000000000000020000200000000000000010802000000000010800000400000000000000001080200840000020000200002000021080000002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 0x800000001004000000000000000000000000000004210842000000000000000000000000000000000000000000000000000000210842100000000000000000000000000000000000000000000000001084200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x800000001004000000100000000200000000400004210842000001000000040000001000210000000000000010000000420000210842100020000200000000000000010802000000000010800000401084200000000001080200840000020000200002000021080000002000021080000800008420000210800008420000010000000400000200002000021080000000008000, 3⟩,
  ⟨0x7fffe03e07fffe03ffff7003ffff7800ffffdef6000000000004200bc8480a007a4a03f001f100821401d9205407e007c01f1858160174b6017805e3603600ec6c01e80000000000000000109000890003100208880084802254e001f01548c00aa463800a6453c0019894f7b0000240001021000042c0500002d7ffc000080c10a0000b02afff80000000c2c0b00005b00000001b01b0000360000b8e2fd0cd6e4697f, 0x8000000010000000020000000800000000000000002000000080200840008400080000800100401080010040100000000000000008021000010042108021084010042008421004200000108421004200802100420080010000100020004200800100020004200040008001080200042008401000000800000020000010000100020004200000000400, 0x40000000084210000000000000000000000000000000000108421084000000008420000000000000000000000000000000000000000008421084210840000000084200000000000000000000000000000010840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x40000000084210000008000000010000000020000000800108421084000002008420080200840008400080000800100401080010040108421084210840008021084210042108021084010042008421004210840108421004200802100420080010000100020004200800100020004200040008001080200042008401000000800000020000010000100020004200000000400, 3⟩,
  ⟨0x3ffff07c000000000ffffc0f0f83c00000000000140402000124200a10058000011004800440144014005800840002482802800b020b0c02424804c00000000000000000444a0244a00c4a104225041250821250410821150498ce83e010898411152b60787c1e1128000800000020300000210001bffe000408800000a200020003ffe00c6000004340007ffc30d8600036dffffa7b7179dbe71baf, 0x20000000040000000080000002000000004000000100000004010800100420000000002000000084000802100000080000800000000000000842008420000000002100020084200000000000080200000108000000000040000400080200000000400080210000100020084000802100421000000002000000080000040000400080210000000001, 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000020000000040000000080000002000000004000000100000004010800100420000000002000000084000802100000080000800000000000000842008420000000002100020084200000000000080200000108000000000040000400080200000000400080210000100020084000802100421000000002000000080000040000400080210000000001, 3⟩]
def rootPreparedMask : ℕ := 0x1ffffdffffdffffdeffffeffffef7fffefbef7fffefbffff77dbffff7beeffffdef6fbbdfff6dad5abffeb5b6adfff5afffb7ffd6daad57ffd6d55fff5fff7ffdb5ad6bffeb6bffefffb6db6dfff6dbffe0000000000000000ffffeffffeffffef7ffff7ffff7bffff7df7bffff7dffffbbedffffbdf77fffef7b7ddefffb6d6ad5fff5adb56fffad7ffdbffeb6d56abffeb6aafffafffbffedad6b5fff5b5fff7ffdb6db6fffb6dfffffffffffffffffff
def rootPreparedSlots : ℕ := 0x42108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
def rootPreparedBudget : ℕ := 0x5ad4b56d9ce739be739cdf37be6f9cdf37bdf15bdeb5bdef9be6f6b66f8c62f7be6f9c6318c6318c6318c6319c6718b5b18c6316c6318c6318be339ce339ce318c6318ce739ce739ce739ce739cdf39ce739ce739ce739ce739ce739ce6f9ce739be717ce738be719c5ef9c6716b62f9cdef9cdf19be6f7c6718bdaf7bdf38bdad6adad7ada96b5ad4b5ab5ad6b6ad2969ce7294a72

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedWords_eq : avl (PZ rootBounds) (mz 0) (rawL []) = rootPreparedWords :=
  Eq.refl rootPreparedWords
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedMask_eq : mz 0 = rootPreparedMask := Eq.refl rootPreparedMask
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedSlots_eq : pL (rootBounds.map fun _ => 16) = rootPreparedSlots := Eq.refl rootPreparedSlots
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedBudget_eq : pL (rootBounds.map fun e => 16 + (14 - e.2)) = rootPreparedBudget :=
  Eq.refl rootPreparedBudget
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedL_eq : lz 0 = I.AA := Eq.refl I.AA
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allRootInputsNeeded (d : Bool) :
    allInputsNeeded I.NN d I.AA rootPreparedWords 0 = true := by
  cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma searchInputs_atRoot (t H ph : ℕ)
    (test : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List W → Bool) :
    searchInputs [] rootBounds 0 14 t H ph test =
      guardStart t H ph (test I.NN I.AA I.HX I.HY I.AA rootPreparedMask
        rootPreparedSlots rootPreparedBudget 0) rootPreparedWords := by
  simp only [searchInputs, frc_eq, st_eq, rootPreparedWords_eq, rootPreparedMask_eq,
    rootPreparedSlots_eq, rootPreparedBudget_eq, rootPreparedL_eq]
  change anySubC I.NN (pos t) I.AA rootPreparedWords 0 _ = _
  rw [anySub_allInputs (allRootInputsNeeded (pos t))]
  rfl




lemma pair_distribute {f : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    {g : Fin 8 → W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool}
    (h : ∀ a c da dc s x y, f a c da dc s x y = true → ∃ b, g b a c da dc s x y = true)
    (a c : XW) : pair f a c = true → ∃ b, pair (g b) a c = true := by
  obtain ⟨w,s,q,u⟩ := a
  obtain ⟨w',s',q',u'⟩ := c
  simp only [pair,bR]
  cases hb : f w w' (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u')
      (Nat.land s s') (Nat.lor w.a w'.a) (Nat.land w.b w'.b)
  · simp only [hb,Bool.cond_false]
    intro hor
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hor
    refine ⟨b, ?_⟩
    rw [hb]
    simp
  · intro _
    obtain ⟨b,hb⟩ := h _ _ _ _ _ _ _ hb
    exact ⟨b,by rw [hb]; rfl⟩



noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootStart_eq (H : ℕ) (kind : Bool) :
    startPairPicked I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots rootPreparedBudget
      14 1 0 H 0 rootPreparedWords kind =
    initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) := by
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 8 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  simp only [startPairPicked, child, st_eq, topPairPicked, bR, haveRequired, len, budget,
    show Nat.ble 8 (Nat.sub 15 1) = true from rfl, show Nat.ble 8 1 = false from rfl,
    Bool.cond_true, Bool.cond_false]
  change (bif initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) then true else false) = _
  cases initialBinary H kind (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots
      14 14 13 1) <;> rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialBinary_of_check (H : ℕ) (kind : Bool)
    (h : chkPairPicked [] rootBounds 0 14 1 H 0 kind = true) :
    initialBinary H kind
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = true := by
  rw [← chkPairFast_eq, chkPairFast, searchInputs_atRoot] at h
  simp only [guardStart, rootStart_eq, bR] at h
  cases hp : relevantStart 1 H 0 rootPreparedWords
  · simp [hp] at h
  · simpa [hp] using h

def wordEquals (a b : W) : Bool :=
  (a.s == b.s) && (a.a == b.a) && (a.b == b.b) && (a.c == b.c) && (a.r == b.r)

lemma wordEquals_spec {a b : W} (h : wordEquals a b = true) : a = b := by
  cases a
  cases b
  simp [wordEquals, Bool.and_eq_true] at h ⊢
  rcases h with ⟨⟨⟨⟨hs, ha⟩, hb⟩, hc⟩, hr⟩
  exact ⟨hs, ha, hb, hc, hr⟩

def frontierMissing (states : List (ℕ × List W)) (z : ℕ) (v : List W) : Bool :=
  !(states.any fun state => (z == state.1) && List.isEqv v state.2 wordEquals)

noncomputable def rootWithGate (i j mask : ℕ) (kind : Bool) : List W :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD i zero
  let b := rootPreparedWords.getD j zero
  let keep := (rootPreparedWords.zipIdx.filter fun e => mask.testBit e.2).map Prod.fst
  addS (opW kind a b) keep

lemma frontierMissing_false {states : List (ℕ × List W)} {z : ℕ} {v : List W}
    (h : frontierMissing states z v = false) : (z, v) ∈ states := by
  simp only [frontierMissing, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨j, w⟩, membership, rfl, he⟩ := h
  have hw : v = w := by
    clear membership
    induction v generalizing w with
    | nil => cases w <;> simp_all [List.isEqv]
    | cons a v ih =>
      cases w with
      | nil => simp [List.isEqv] at he
      | cons b w =>
        simp only [List.isEqv, Bool.and_eq_true] at he
        rw [wordEquals_spec he.1, ih w he.2]
  rwa [hw]

lemma initialBinary_from_frontier (H : ℕ) (kind : Bool) (states : List (ℕ × List W))
    (complete : initialBinary H kind (frontierMissing states) = false)
    (checked : ∀ state ∈ states,
      look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false) :
    chkPairPicked [] rootBounds 0 14 1 H 0 kind = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  have original := initialBinary_of_check H kind h
  unfold initialBinary at original complete
  obtain ⟨_, hit⟩ := nodePicked_distribute
    (branches := fun _ => frontierMissing states)
    I.NN true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind
    (fun z v hit => by
      refine ⟨0, ?_⟩
      cases hm : frontierMissing states z v
      · exact Bool.noConfusion ((checked (z,v) (frontierMissing_false hm)).symm.trans hit)
      · exact hm)
    original
  exact Bool.noConfusion (complete.symm.trans hit)

abbrev SearchState := ℕ × List W

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f true I.AA rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 12 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1 z v))

lemma pureAt_from_frontier (e : ℕ) (state : SearchState) (states : List SearchState)
    (remaining : SearchState → Bool)
    (complete : pureAt e state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, remaining x = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => frontierMissing states)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : frontierMissing states z v
        · exact Bool.noConfusion ((checked _ (frontierMissing_false missed)).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma pureSecond_from_frontier (state : SearchState) (states : List SearchState)
    (complete : pureSecond state (frontierMissing states) = false)
    (checked : ∀ x ∈ states, afterSecond x = false) :
    pureSecond state (fun z v => afterSecond (z,v)) = false :=
  pureAt_from_frontier 12 state states afterSecond complete checked

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (14 : ℕ) = Nat.succ 13 from rfl, look1C_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureSecond state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 13 12 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def secondTransition (state : SearchState) (i j kept : ℕ) (kind : Bool) : SearchState :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := state.2.getD i zero
  let b := state.2.getD j zero
  let word := opW kind a b
  let keptWords := (state.2.zipIdx.filter fun e => kept.testBit e.2).map Prod.fst
  let budget := Nat.sub (Nat.add state.1 (Nat.land a.c b.c)) word.c
  let usedA := if kept.testBit i then a.c else 0
  let usedB := if kept.testBit j then b.c else 0
  (Nat.sub (Nat.sub budget usedA) usedB, addS word keptWords)

noncomputable def firstStates : List SearchState := [
  ⟨0x5293ad2b5b5ad6adef7ad2d4a5a95b52d4a5291ad673aceb7adeb295eb6b5a75adeb79ceb4a5294a5294a52949d2738c675ad6b3ad6739d6b594e94a4e94a56739d6b59ce74a5294a52939ce739c673ad6b39ceb39ce739d6739ce739ce339d6b495272a5293952749ca549d2718ce54a4a54b52b6a5a94adab5a4e94a52d59ca528ca538ca1295292a52739ce749ca54842518c651, rootWithGate 0 1 255 false⟩,
  ⟨0x4e73ad2b5ad6b5adef7aceb39d675aceb39ceb2ad673ad2b7adeb39deb6b5a95adeb7a52b39ce739ce739ce74a569494a95ad6b3ad694a56b5952b5ad2b5ad694a56b59d2939ce739ce73a5294a4a94ad6b4a52b3a5294a5674a5294a5254a56b495693ad6b49d695a4e75a569295275ace75b52b6a5a94adab5a4e94a52d59ce7394e7494e339d292a52739ce749ca548c6518c651, rootWithGate 0 1 255 true⟩,
  ⟨0x4eb1ad2b5ad6f79def7aceb39d676bd2f5ad6919ce319d2b6adeb3a5e96b5ab5a5eb79ce739ce739d294ad6b49d2738c6739ce719ce94a56b59ceb5ad2d6b52b4ad2b49ce739ce74a52b39ce739c6739ce74a52b39d295a5274a4e94a5254a52949d293ad69395295a4e75ada9295296b5296ace95a5a94ada949ca73a52d5a4e5394e7595254a4e92a525294a749ca548ca508c651, rootWithGate 0 2 255 true⟩,
  ⟨0x52b3ad296b56f7aded7b52d4a5695bd6f59d693ad671aceb7ad6b2a5eb6a5a94a5a969d674a5294a56759d6749d2b59c6b59d671ace739d6b594e94a56d4b4e94a52949ce74a5293ace739d6759c6b39ce739ceb39ce94a52739ce73ace359ce7495272a5293952749ca56ad2b38d694b4a94b5276a5292ad2b3a4692952939ca528ca559d252a5292952738ce729c25284a518c611, rootWithGate 0 3 255 false⟩,
  ⟨0x4eb3ad275ad6f7adeb7aceb39d676bd6f5a56b3ad672ad2b7adab3a5eb6ada739d675a56939ce739d695a5695a52b59cab5a5692ad294a56b59d2b4ad6d5b52739ce73a4e939ce74ad2949d695a4ab4a5294a52b49d2739ce94a4e94ad255a52959d693a56b495694a4a76ad6b395695b4e95b5296a5693ad6b4a4a939d2b4a4e7394a759d253a52929d27394e739c6538ca518c631, rootWithGate 0 3 255 true⟩,
  ⟨0x52b3ad2b6b5ad7adef7b4ed4a5a95ad6f5ad6939d673ace77adeb2a56b6b5ab3adeb79d6b39ce94a56b5ad6b49d2759ceb39d6b3ad6739ce7594e94a56d6b5675ace759ceb39ce95ad6b39ce75aceb59d6b39ce739d673ace739ce73ad675aceb495272a5293952749ca549d2b39d696b5296a4a74952529d2b5a4e94a52d59ca528ca539d254a4a5094a739ce749ca5484a118c651, rootWithGate 0 4 255 false⟩,
  ⟨0x4eb3ad2b5ad6b7adef7aceb39d676b56f5ad6b3a5673ad297adeb3a5ab6b5ab4adeb7a56b39ce739d6b5ad6b5a56959ceb4a56b3ad674a52959d2b5ad6d6b5695ad295a52b39ce75ad6b4a5295aceb5a56b39d294a5694ad2939d294ad675ad2b59d272a52b49d695a4e75a56b39d696b5296ace959d673a56b5a4e94a52d5a4a7394e749d254a4e719ce739ce749ca548ca318c651, rootWithGate 0 4 255 true⟩,
  ⟨0x4eb39d2b5ad6f5ad6f7aceb39d676bd6d5ad6b3ad273ace759d673a5eb5b5ab5adab7a56b39ce739d6b5ad6b5a56b49ceb5ad293ad6739ce739d295ad6b6b56b5ad6b5a52b39ce75ad6b4a56b4a4eb5ad2b39ce74a56b5ad6939d275a5275ad6959d673ad6949d6749ce76ada939d675ad296ad2b69d674ada949ce949ceb5a4e7294e759ce54a5272a52539ce5394a548ca5184651, rootWithGate 0 5 255 true⟩,
  ⟨0x4eb3acab5ad6f79d6b5aceb39d676bd6f4ad6b3ad653ad2b7a5eb295674a52b5ade979ce739ce739d2b5a52b59d6b594eb4ad2b2a5693a52b494e94a4e94a4eb5a56949ce739ce74a56939d2b4aca95a5293a4e939ceb4a5273a4e75a5654ad29595692ad6b39d675a4a56a5ab29d676b4e76b4eb69da93a5a95a4a749ced4a4e738ce759d234a5291a52729ce549c6348ca518c251, rootWithGate 0 6 255 true⟩,
  ⟨0x4eb3ad2b5ad6f7adef5aceb39d676bd6f5ad2b3ad673a52b7ade93a5eb6b56b5adeb6a56b39ce739d6b4ad295a56b59ce95ad6b3a52949d6949d2b5a56d6ad6b5ad6b5a52b39ce75a5294a56b5ace94ad6949ce94a56b5ad6949d275ad674a56b59d693ad2b49d2959ce56adab39d296ad275b52b5a5a74a56b59ce73a4eb4a4e7394e559d2549d292a4e739ca7494a338ca518c650, rootWithGate 0 7 255 true⟩,
  ⟨0x5671ad2b5adeb59def7b56d5adeb5aceb39ce919ce319d6b6adeb49de96b5a95a5eb79ce75ad6b5ace739ce749d2738c6739ce719ceb5ad6b59d2d6b4eb5ad293a52b49ce75ad6b39ce739ce739c6739ce75ad6b3a4e749d275ad2b39ce339d2949d6b4b5ab49d6b6ad294a56718ce75ace75ace95a5a94ada949ca73a52d5a52749d2948ce339ce92a525294a749ca54946508c651, rootWithGate 1 2 255 true⟩,
  ⟨0x5693ad296bdad6aded7ad6f5ad6b6b52d49d2d1ad671ad6b7ad6b495eb6a5a74a5a96ace75ad6b5ad2749d274ad2738c6759d671aceb5ad6b5956d4b4e94a4e739d2949ce75ad6b3a4e739ce739c6739ce75ad6b39ce739d275aceb39ce339ce7495ab4a5ad595ab4aca949d2718ce54a4a54b5276a5292ad2b3a4692952939d2949ca938ca1295292952738ce729c252942518c611, rootWithGate 1 3 255 false⟩,
  ⟨0x5673ad275bd6b5adeb7b56f5adab5aceb39ced2ad672ad6b7adab49deb6ada739d675ad295ad6b5ace739ce75ad69494695a5692ad2b5ad6b59d6d5b52b4ad2739ce73a5275ad6b39ce74a52749c693a5295ad6b4a4e739ce95ad2b3a4e349d2959dab4adad59dab5ace95a52928d274aca74b5296a5693ad6b4a4a939d2b4a52949ce9494e329d2929d27394e739c653946518c631, rootWithGate 1 3 255 true⟩,
  ⟨0x5693ad2b6bdeb6adef7acef5adeb6ad2d4a52d19d673ad677adeb4956b6b5a73adeb7aceb39ceb5ad294a5294ada738c6739d6b3ad675ace75956d6b4e94a56739ce759d6739ceb4a5293ace739c6739d6b39d673ace739ce739d6b39ce339ceb495272a52d5a5ab6ad2949d2718ce54a4a54a4a74952529d2b5a4e94a52d59ca949d2938ca1294a5094a739ce749ca54942118c651, rootWithGate 1 4 255 false⟩,
  ⟨0x5673ad2b5bdeb5adef7b52f5adeb5aceb39ced2a5673ad697adeb49dab6b5a94adeb7ad2b4a52b5ace739ce75ada7494a94a56b3ad695ad2959d6d6b52b5ad674a5295a5694a52b39ce74ace74a4a94a56b4a5694ad273a5294a56b3a5254a52b59d693ad6d5a5ab6ad2949d29295275ace75ace959d673a56b5a4e94a52d5a4e949d29394e339ce719ce739ce749ca54946318c651, rootWithGate 1 4 255 true⟩,
  ⟨0x56739d2b5bdeb5ad6f7b56f4adeb5aceb39ced2ad273ace759d6749deb5b5a95adab7ad2b4ad694ace739ce75ada9394a95ad293ad6739ce739d6b6b5295ad694a56b5a5694a56939ce74ad2939ca94ad2b39ce74ad294a5694a56949ce54a56959da94b5ab5a5a95a5295a567295254a4e75ad2b69d674ada949ce949ceb5a52939d29494a339d272a52539ce5394a549465184651, rootWithGate 1 5 255 true⟩,
  ⟨0x5673acab5bdeb59d6b5b56f5a5eb5aceb39ced2ad653ad6b7a5eb295674a5295ade979ce75a5695a4e739ce75a5a948ca94ad2b2a56b4ad2b494e94a4e94a4e949d6949ce74ad2939ce73a4e93a4674a5294ad2939ce939d274ad2949d233a529595ab3b5ad4a5a96ace759d69195255aca55b4eb69da93a5a95a4a749ced4a52949529494e139d291a52729ce549c634946518c251, rootWithGate 1 6 255 true⟩,
  ⟨0x5673ad2b5bdeb5adef5b56f5ade95aceb39ced2ad673a56b7ade949deb6b5695adeb6ad2b5ad2b4a4e739ce75ada9494a75ad6b3a52b5a56949d6d6ad2b5a5694a56b5a5695a52939ce74ad294a4a73ad695a5294ad294a5695a5694a52539d6b59dab4b56d5a56b6a5275a569294e75a4e54b52b5a5a74a56b59ce73a4eb4a52949d27494e3395292a4e739ca7494a33946518c650, rootWithGate 1 7 255 true⟩,
  ⟨0x56b1ad277ad6f79deb7bd6d5adab7bd2f5a56919ce319d6b6adab4a5e96ada739d6759ce75ad6b5ad274a56949d2738c6739ce719ceb5ad6b5a52d5b52d5b4e739ce739ce75ad6b3a4e939ce739c6739ce75ad6b49ce739ce95aceb3a4e349ce75a56b4adab4956b5ace95ad6928d295b4e95ace75a5693ad6939c6729d2b4ad2749ce9595253a4e929d2528ca739c65394a508c631, rootWithGate 2 3 255 true⟩,
  ⟨0x56b1ad2b7adeb79def7bd2d5adeb7b52f5ad6919ce319d696adeb4a5a96b5ab4a5eb79ce74a52b5ad294ad6b49d2738c6739ce719ce95ad295a52d6b52d6b5294ace949ce74a52b4a52b39ce739c6739ce74a5694a5274a4e94a52b3a5254a4e95a5293ad6b49d6b6ad294a569295296b5296a4a749d673a56949ca73a52d5ace749d29495254a4a719ce5294a749ca5494a308c651, rootWithGate 2 4 255 true⟩,
  ⟨0x56b19d2b7adef59d6f7bd6d4adeb7bd2d5ad6919ce319ce759d674a5e95b5ab5a5ab79ce74ad694ad294ad6b49d2738c6739ce719ce739ce73a52b6b52b6b52b4ad2b49ce74a5694a52b39ce739c6739ce739ce74a5295a5294a52949ce54a5275a5694b5a949d695a5295ada7295275ad296a4e959d674ada7394a739ceb5ad2739d29594e54a4e72a523294a5394a5494a5084651, rootWithGate 2 5 255 true⟩,
  ⟨0x56b1acab7adef79d6b5bd6d5a5eb7bd2f4ad6919ce319d6b6a5eb295674a52b5a5e979ce75a5695a4e94a52b49d2738c6739ce719ceb4ad2b494e94a4e94a4eb4a52939ce74ad2939d2939ce739c6739ce74ad2939ce949ce74ace949d233a4e759d6b3b5ab39d696ace75a5a9195276b4e76aca959da93a5a749c6539ced4ad2749529595234a4e91a525194a549c63494a508c251, rootWithGate 2 6 255 true⟩,
  ⟨0x56b1ad2b7adef79def5bd6d5ade97bd2f5ad2919ce319d6b6ade94a5e96b56b5a5eb69ce75ad2b4a5293ad2949d2738c6739ce719ceb5a5694a52d6ad2d6ad2b4ad2b49ce75a52949ce939ce739c6739ce75a5294a5295a5295a5294a52539d295a56b4b56b49d2b6a5275ada9294e96ad275ace94a5a74a569494a52a4eb4ad2749d275952549ce92a4e529467494a3394a508c650, rootWithGate 2 7 255 true⟩,
  ⟨0x56b3ad297bdad7aded7bcef5ad6b7ad6f59d6d39d671ad677ad6b4a56b6a5a93a5a96ad6739ceb5ad6759d676ad2759c6b39d671ace75ace75a56d4b56d4b4e74a4e74ace739ceb3ace759ce759c6b39ce739d6759ce73a4eb39ceb3ace359ce76a5272a52d595ab4aca949d2b38d694b4a94a4a74952529d2b3a469295293aca949ca939d252a4a5094a738ce729c25294a118c611, rootWithGate 3 4 255 false⟩,
  ⟨0x56b3ad277bd6b7adeb7bd2f5adab7b56f5a56d3a5672ad697adab4a5ab6ada739d675ad694a52b5ad695a5696ad6959cab49d692ad295ad295a56d5b56d5b52739ce73ad294a52b4ad295a5275a4ab49d294a5695a52739ceb4a52b3ad255a4e96a5693a56d59dab5ace95a52b395695b4e95ace759d272a52b4a4a939d2b4ace949ce949d253a4e7194e7394e739c65394a318c631, rootWithGate 3 4 255 true⟩,
  ⟨0x56b39d277bd6f5ad6b7bd6f4adab7bd6d5a56d3ad272ace759d674a5eb5ada739d675ad694ad694ad695a5696ad6b49cab5a5272ad2739ce73a56b5b56b5b52739ce73ad294a5694ad295a56949cab4a4e939ce75a52739ceb4a5294a4e55a5276a5a94adab59da94a4e96ad69395674ace95ad2969d273ad6939ca9394e94ad2939ce959ce53a52729d25394e529465394a5184631, rootWithGate 3 5 255 true⟩,
  ⟨0x56b3aca77bd6f79d6b5bd6f5a5ab7bd6f4a56d3ad652ad6b7a5ab295674a52739d6759ce75a5695a52959d296a56b594ab4a5291a52b4ad2b494e94a4e94a4e739ce739ce74ad293a52749d294a46949ce74ad2939ce739ce94ace94a5234a4e769dab3adad49da95aca76a56b295675b4a75b4e969d692a5694a467394eb3ad29494e959d233a52919d27294e539c23394a518c231, rootWithGate 3 6 255 true⟩,
  ⟨0x56b3ad277bd6f7adeb5bd6f5ada97bd6f5a52d3ad672a56b7ada94a5eb6ad6739d675ad695ad2b4a5694a5276ad6b59ca95a5692a4eb5a5694a56d5ad6d5ad2739ce73ad295a5294a4e75a5695a4a93a5275a5295a52739ceb5a5294ad2549d296a5ab4ad6d59d6b5a4e76ad6b395295ace74b5295a5673a52b49ca729ce93ad2949ce759d2539d2929ce7394a739463294a518c630, rootWithGate 3 7 255 true⟩,
  ⟨0x56b39d2b7bdeb5ad6f7bd2f4adeb7b56d5ad6d3a5273ace759d674a5ab5b5ab4adab7ad6b3a5294ad6b5ad6b6ada949ceb4a5293ad6739ce73a56b6b56b6b5695ad295ad6b39d295ad6b5ad294a4eb5a52b39ce75ad694ad2b39d694a5275ad296a5673ad6b5a5a95a5295a56939d675ad296a4e9595253a56949ce949ceb5ace939d2949ce54a4e519ce539ce5394a5494a3184651, rootWithGate 4 5 255 true⟩,
  ⟨0x56b3acab7bdeb79d6b5bd2f5a5eb7b56f4ad6d3a5653ad697a5eb295674a52b4ade979ce749d295a52b5a52b6a5a9594eb3a52b2a5694ace9494e94a4e94a4e95a52749ce73a4e94a5694a4e94aca959d293a52739ce93a4e93a5294a5654ace969d692ad6d4a5a96ace759d6b29d676b4e76aca95956729d695a4a749ced4ace94952949d234a4e709ce729ce549c63494a318c251, rootWithGate 4 6 255 true⟩,
  ⟨0x56b3ad2b7bdeb7adef5bd2f5ade97b56f5ad2d3a5673a5697ade94a5ab6b56b4adeb6ad6b4a4eb4a56b4ad296ada959ce94a56b3a5295a5274a56d6ad6d6ad695ad295ad6b49ce95a5295ad295ace94a56949d275ad694ad2b49d694ad674a52b6a5693ad2d5a56b6a5275a56b39d296ad275ace949d6539d2b59ce73a4eb4ace949d2749d2549ce719ca739ca7494a3394a318c650, rootWithGate 4 7 255 true⟩,
  ⟨0x56b39cab7bdef59d6b5bd6f4a5eb7bd6d4ad6d3ad253ace759d67295674a52b5ada979ce74a5674a52b5a52b6a5ab494eb4ace92a56739ce7394e94a4e94a4eb5a56949ce73a5274a5694a52b3a4a95a4e939ce739ceb4a5293a52759d254ad2769da93b5ab4a5a75a4e76a5a929d655ace76aceb695673a5a749ca7494ab4ad293952959ce34a5271a52529ce339463494a5184251, rootWithGate 5 6 255 true⟩,
  ⟨0x56b39d2b7bdef5ad6f5bd6f4ade97bd6d5ad2d3ad273a4e759d674a5eb5b56b5adab6ad6b4ad293a56b4ad296adab49ce95ad293a52739ce73a56b6ad6b6ad6b5ad6b5ad6b49d275a5295ad6b4a4e94ad2939ce75ad6b5ad6b49d675a5274a5696a5a94b56b5a56959d276ada939d275a5275ad2b59d654a569494e739ca94ad2939d2759ce549d272a4e539ca538ca3394a5184650, rootWithGate 5 7 255 true⟩,
  ⟨0x56b3acab7bdef79d6b5bd6f5a5e97bd6f4ad2d3ad653a56b7a5e9295674a52b5ade969ce75a52949d2b4a4e96a5ab594e94ad2b29d2b4a529394e94a4e94a4eb5a56949ce74a4e749d274a52b4aca74a5274a4e739ceb4a5294a5275a5653a52969dab3b56d4a5696a4e56a5ab29d276ace55b4eb59da739d6959ca539cab3ad294952759d2349d291a4e729ca549461394a518c250, rootWithGate 6 7 255 true⟩,
  ⟨0x56b3aceb7bdef7a5ad6bd6f5ade97bd6f5ad2d3ad673a56b7ade939da95ad6b5adeb6a5295ad2b4a56b4ad296adab59ce95ad6b3a52b5a56949d2b5ad2b5ad2b5ad6b5a5295a5295a5295ad6b5ace94ad695a5294a52b5ad6b5a5695ad674a56b6a5ab4b56d5a56b6a5276adab39d296ad275b52b5a5a74a56b59ce73a4eb4ad2949d2759d2549d292a4e739ca7494a3394a518c650, rootWithGate 6 7 191 true⟩]

def firstCount : ℕ := 35

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def decodeStep (width : ℕ) (parent : ℕ → SearchState) (entry : ℕ) : SearchState :=
  let before := parent (entry % 2 ^ width)
  let left := (entry >>> width) % 16
  let right := (entry >>> (width + 4)) % 16
  let dropLeft := if entry.testBit (width + 8) then 2 ^ left else 0
  let dropRight := if entry.testBit (width + 9) then 2 ^ right else 0
  let kept := 2 ^ before.2.length - 1 - dropLeft - dropRight
  secondTransition before left right kept (entry.testBit (width + 10))


def secondCount : ℕ := 413

def secondCodes : List ℕ := [0x9060c7306318314c18860d820641035c81ac40c6206a90314818840c3206c0832041ae20c710630831441a820c410698830c41b0e048602428119409080464022a01c400, 0x8ec14850a3a85194290814640a2a0560c2ae615630aa98520828c414520a40851c428c214510aa0851042b0e0c870643031d8190a0c7506328321018e80c64062a021501, 0xac8246412aa091504906247312318914c4886248212390918848a420521221090c84902247112308954448a225870e430721438ca1c810e30871443e601d870a43852182, 0x8a4344218210d0c86b0234811a388d58468c23576163a8b1cc58a62c7216290b0c858e22c5116188a0c458422f4016c38921c490c24761242891d448ca25841242095d04, 0x8863c821e390f14870a43c421c210f0c87b023c811e388f61c690e34861a3b0d614690a35751ab28d194690834741a320d150690634731a318d14c688634821a390d1886, 0x90c46762242919d488ca44842232111508906446322299110c890444622229111088864448122c38f21c7b0c3d761e428f1d47cca3c841e3a0f15070a83c831e398f14c7, 0x8c854542ac1955ccaa8654822a3115148aa845787274393a1898ec4e85263a9319498e84c64262a1215098e64c6326299310c98e44c622629121489884484226191361c8, 0x8c66f4136c39921cc90c64763242991d4c8ca65843242195d0c8c86454332199208c8c465523229195d8b8ea5c742e2a17cc4bb0e54872a43151d8a90a54752a3295210a, 0x8e67e633e299f10cfb047c823ec39d21ce90c74763ac29d214eaea74653a421d1d0e8c876543a2a1d20ce8e674633b299d14ce88675823a411d588e8c4758736431b20cd, 0x8ca8e84463a2319118a888544741a31cd18c68c534621a361d090c84854232a12110ce88464422a219cd0b0e7c873ec31f5d8f90a7c753e421f1d0fcc87c543c2a1f20cf, 0x908a664522a2960d4b0e9c874e43271d9390a9c654e42271913ca89c544ec1a75cd3ac69d874a43a521928ec94854a3aa5195290894644a2a2554d2f0e8e87463b231d51, 0x90ec486623b3121588cac58462423159188c8c5765e3aafd0d78ecb4755a32ada1168c8b4545ac3ab2195cecac85573aab1955908ae7456322b1515b0ea4875242a91d54, 0x161dfd0cf4767ac3bb219dceced877243b9619cb0ae485723b37a15b8eadc656ec3b5219acecd4856b3ab5195ab0ecc876642b31d59ccacd8466423361d8]

noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := secondCodes.getD (i / 32) 0
  decodeStep 6 firstAt ((block >>> (17 * (i % 32))) % 131072)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def secondSuccessorsList : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6, 7],
  [0, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43],
  [8, 9, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66],
  [67, 68, 69, 70, 71, 72, 73, 74],
  [10, 11, 44, 45, 67, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105],
  [106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118],
  [12, 46, 75, 76, 106, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148],
  [13, 47, 77, 119, 120, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173],
  [14, 15, 48, 78, 121, 149, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192],
  [16, 17, 49, 79, 122, 123, 150, 151, 174, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214],
  [18, 80, 107, 124, 152, 175, 193, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231],
  [108, 125, 153, 194, 232, 233, 234, 235, 236],
  [19, 81, 109, 126, 154, 176, 195, 215, 232, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253],
  [82, 155, 196, 254, 255, 256, 257, 258],
  [20, 21, 50, 68, 83, 127, 156, 177, 197, 216, 237, 238, 254, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281],
  [22, 23, 51, 69, 84, 110, 128, 178, 198, 217, 239, 259, 260, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299],
  [24, 85, 129, 157, 199, 300, 301, 302, 303, 304, 305, 306, 307, 308],
  [25, 26, 52, 70, 86, 111, 130, 158, 179, 218, 240, 261, 262, 282, 283, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323],
  [27, 87, 112, 131, 159, 180, 200, 219, 241, 263, 284, 309, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334],
  [28, 53, 88, 132, 160, 181, 201, 264, 265, 285, 310, 324, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347],
  [29, 54, 89, 113, 133, 182, 202, 266, 286, 311, 335, 348, 349, 350, 351, 352, 353, 354, 355],
  [30, 55, 90, 134, 161, 203, 220, 267, 287, 300, 312, 336, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365],
  [31, 56, 91, 114, 135, 162, 183, 221, 268, 288, 313, 337, 348, 366, 367, 368, 369, 370, 371],
  [32, 163, 204, 289, 314, 372, 373, 374],
  [1, 33, 57, 92, 93, 136, 164, 184, 205, 222, 242, 269, 270, 290, 301, 315, 325, 338, 339, 349, 356, 366, 372, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384],
  [2, 34, 58, 94, 95, 115, 137, 185, 206, 223, 243, 255, 271, 291, 302, 316, 326, 340, 350, 357, 367, 375, 376, 385, 386, 387, 388, 389, 390, 391],
  [35, 96, 138, 165, 207, 244, 272, 292, 303, 317, 358, 392, 393, 394, 395, 396, 397],
  [3, 36, 59, 97, 98, 116, 139, 166, 186, 224, 245, 246, 256, 273, 293, 304, 318, 327, 341, 351, 359, 368, 377, 378, 385, 386, 398, 399, 400, 401],
  [4, 37, 60, 71, 99, 140, 141, 167, 187, 208, 225, 233, 247, 274, 305, 319, 328, 342, 360, 369, 379, 387, 392, 398, 402, 403, 404, 405, 406],
  [38, 61, 100, 142, 168, 188, 209, 226, 248, 275, 294, 320, 329, 352, 361, 370, 388, 393, 399, 407, 408, 409],
  [5, 39, 62, 72, 101, 143, 144, 169, 189, 210, 227, 234, 249, 276, 277, 295, 306, 330, 343, 353, 362, 380, 389, 394, 400, 402, 403, 410, 411],
  [40, 63, 102, 145, 170, 190, 211, 228, 250, 278, 296, 321, 331, 344, 363, 371, 381, 395, 401, 407, 410, 412],
  [6, 41, 64, 73, 103, 117, 146, 171, 191, 212, 229, 235, 251, 257, 279, 297, 307, 332, 345, 364, 373, 382, 396, 404, 408, 411],
  [42, 65, 104, 147, 172, 192, 213, 230, 252, 280, 298, 308, 322, 333, 346, 354, 365, 383, 390, 397, 405, 409, 412],
  [7, 43, 66, 74, 105, 118, 148, 173, 214, 231, 236, 253, 258, 281, 299, 323, 334, 347, 355, 374, 384, 391, 406]]

def secondSuccessors (i : ℕ) : List ℕ := secondSuccessorsList.getD i []

def thirdCount : ℕ := 1943

def thirdCodes : List ℕ := [0xb0409ac409aa409b3008b2608ae608ac608b2408ae408ac408d2e05b3004b2e04b2c04d2c038ec03b3002cec02b2a02b300192e0192c018ec01b2a01aea01aec008ea008e8008a8008e6008a60088600, 0x8c80baa80b8a80bb040b9040bae40bac40b8c40baa40b8a40bb300ab2a0a92a0aaea0a8ea0aaca0a8ca0ab260a9260ab060aae60a8e60aac60a8c60ab240ab040aae40aac40ab0e0990c0990a098ca09, 0xb2c0caec0c92a0c8ea0c8ca0c9280c8e80c8c80c8a80cb260c9260cb060cae60c8e60cac60c8c60c8a60c8860cb240cb040cae40cb0e0b90e0b90c0b8ec0b90a0b8ea0b8ca0bb080b9080bae80bac80b, 0x8ca0f9080f8c80f8a80fb040fac40faa40f92a0e8ea0e8ca0eb260eae60eac60eb240eb300db2e0dcec0d92a0d8ca0d9280d8c80d8a80db260d9260db060dac60d8c60d8a60d8860db240db040db300c, 0xa8118e6118c6118a61188611ae411ac4118c411aa4118a4118841186411f3010d2e10d2c108ea108ca108e8108c8108a810b0610ae6108e610ac6108c6108a61088610b0e0f90c0fcec0f90a0fcea0f, 0x92c148ec148ea14cca148ca14b2614ae614b301392e1392c138ec13b2a13b2613ae613ac613b301292e1292c128ec12b2612ae612ac612f0e11d0e11d0c118ec11d0a118ea118ca118e8118c8118a811, 0x8e617cc6178a61788617b3016b2e1692c16cea168ca16b2616b0e1590e1590c158ec15b0a1590a15aea158ca15908158e8158c815ca8158a815906158e6158c615ca6158a61588615b301492e14b2c14, 0xa81ad061a8e61a8c61a8a61a8861af30198ec19d2a198ea198ca19b0e1890c1890a188ca1890818ce8188c8188a818ce618b0e1790e17b0c17aec1790a178ea17908178e817cc8178a8170a81790617, 0x90e2192c218ec21b2a2192a21aea218ea21b0e20ea8208ec1f92e1e92c1e8ec1eb301d92c1db301c92e1c92c1c8ec1cb301b92e1b92c1b8ec1bf0e1ad0e1a8ec1a8ea1a8ca1ad081a8e81a8c81a8a81a, 0xaa82db302cb2a2caea2caca2cb242cae42cac42cd2e2790e2792e26b302593025b2e25b2c2590e24d2c2490c248ec2492e2392c238ec23b30229302292c2290c22cec22b2a2292a22b30219302192e21, 0xb0e2fcec2f92a2f8ca2fb282fb082fac82f9262f8c62fb242fb302eb2c2eb0c2eaec2e92a2e8ea2e8ca2eb282eb082eae82eac82e9262e8e62e8c62eb242eae42eb0e2d90c2d90a2d8ca2db082dac82d, 0x90c3590a358ca35f30348ec34b3033b2e3392c33b2633b303292e32b2c3292c328ec32b2632ae632f3031d3031d2e31d2c318ea318ca31b0831ae831ac8318e6318c631b3030d0e30d0c30b302fb2e2f, 0xb303fd2e3e90e3eb303d92e3dd0e3db303c9303cb2e3cb2c3cd2c3b8ec3bb303a92c3acec3ab2a3ab303992e3992c398ec39b2a39aea398ca38b0e3790c37cec3790a37cea378ca37b0e3690a36b0e35, 0x9264b9064b8e64b8c64b8a64b8864bb244bb044bae44be604ad2e48b3047b2e47b2c47f30468ec46b3045b2e45b2445b304492e44b2c4492c448ec44b2444ae4448ea438e8438a8438e2438a24388243, 0x9084cae84cac84c8c84caa84c8a84c9064c8e64c8c64c8a64c8864c9044c8e44c8c44c8a44c8844c8644cb304bb2c4bb0c4baec4bb2a4b92a4bb0a4baea4b8ea4baca4b8ca4b9284b9084b8e84b8c84b, 0xaca4e9264e8e64e8c64eb304db2e4db0e4dcec4db2a4d92a4db0a4daca4d8ca4d9284d9084d8c84d9264d9064d8c64d8a64d8864db244db0e4c90e4c90c4c8ec4cb0a4c90a4caea4caca4c8ca4cb084c, 0xaea51aca51ac651b305092e5092c508ec50b2a50aea50aca50f304fd304fd2e4fd2c4fb0a4faea4f8ea4faca4f8ca4f9084f8e84f8c84f9064f8e64f8c64f8a64f8864fb304ed0e4ed0c4eb2a4eaea4e, 0xcea54aca548ca54b265492654b30539305392e5390e53b2c5392c53b0c538ec53b2a53b0a53aea53eca53aca53cca53b265392653ae6538e653b3052b2852ae852ea452b305192e5192c518ec51b2a51, 0xaea57aca57f3056d305690e5690c568ec56f2a56d2a56b0a56aea568ea56aca568ca56b305592e5592c558ec55b2a55f0a55aea55aca55b305493054b2e54b0e5492c5490c54b2a5492a54b0a54eea54, 0x8ec5bf2a5baea5baca5bb305a92e5ad0e5a92c5ad0c5a8ec5ab2a5af0a5aaea5aaca5ab305992c59b2a59eea59aca59b305892e5892c588ec58b2a58aea58eca58aca58b305792e5792c578ec57b2a57, 0xd0a628ea628ca62d2c618ec61b0e6090c60cec6090a60cea608ca60b0e5f90e5f90a5f8ea5fcca5fb305e92c5ecec5eb2a5eb0e5d90e5d90c5d8ec5d90a5d8ca5db305c92e5c92c5c8ec5cb2a5caea5c, 0x8ea6ce626cb0e6b90c6bb066ba866b9046b8c46ba846baca6a8c86a8c66a8866a8c46a8846a8646a8c26a8826a8626a0626a8426ab3066d2e6590e65b306492e64d0e64b306393063b2e63b2c638ec62, 0xb0477b0e73b0873d08728c872b0e7190871cc871b0671b0e7090c70f0e6fd086f8c86fd066f8c66f8866fb0e6eb0c6e9086ecc86e9066ecc66e8866eb046e9046eb0e6d90c6db086dc866d9046d8c46d, 0x8a878906788e6788a67888678904788e4788a478884780847886478b3077b2e77b0e77b2c77b0c77eec77cec7792a7790a778ca7792877908778c8778a87792677906778c6778a6770a67788677b2477, 0x8ca7a9087a8c87a8a87a9067a8c67a8a67a0a67a8867ab3079d0e79b2c79f0c79aec7992a79928798a879926798a67988679b2479b0e7890e78b0c78aec78b0a7890a78aea78eca78cca78908788e878, 0x8c67caa67cf0e7bd0e7bd0c7b8ec7bf0a7bd0a7baea7baca7b8ca7b8e87b8c87b8a87b8e67b8c67b8a67b8867b8e47b8c47b8a47b8847b0847b8647bf307ad307ad2e7af2c7ad2c7ab0c7aaec7a90a7a, 0xb0a7e8ea7e8ca7eca87e9267e8e67eac67e8c67eb0e7d90c7db0a7d90a7daca7d8ca7de847db307c9307c92e7c90e7cb2c7c92c7cb0c7caec7c8ec7c92a7c8ea7c8ca7cb287cb087caa87c9267c8e67c, 0x90880ce8808c8808a880b268092680b307f92e7fb2c7faec7f92a7f8ea7fcca7f9287f8e87fcc87f8a87fb267f9267fae67f8e67fb307e9307e92e7e90e7eb2c7e92c7eb0c7eaec7e8ec7eb2a7e92a7e, 0x90e82b0c82aec828ec82d2a8290a828ea828ca82d2882908828e8828c8828a882b308192e81b2c81aec8192a81d0a818ea81d0881b308093080b2e80b0e80b2c80b0c8092a8090a80cea808ca8092880, 0xb308593085b2c85b0c8592a85cea858ca85b2885b308492e84b2c84aec8492a848ea84cca84b2884ae884b30839308392e8390e83b2c8392c83b0c83aec838ec8392a838ea838ca83ac883f3082d3082, 0xb308993089b2c89b0c89eec89cec89b2a8992a89b308892e88b2c88aec88b2a8892a88aea888ea8890e87b0c87aec878ec87d2a878ea878ca87b308692e86d0e86b2c86f0c86aec8692a86d0a868ea86, 0x8c8958a895926958c6958a69588695b2495b3091d0c908ec90d2e8fb0e8e90c8ecec8eb0e8d90e8db0c8db308cb2e8cb2c8c90e8bf2c8bd2c8bb0c8baec8b8ec8bb308a92e8ad0e8ab2c8af0c8aaec8a, 0x8a697886978e4978a4970a497884970849786497f3096d3096f2e96b0e96d2c96cec9690a968ca96908968c8968a896906968c6968a6960a69688696b3095b2e95f0e95d0c95cec9592a958ca9592895, 0x8c69ab0e99b0c9990a99cca99e8499b309893098b2e98b0e9892c9890c98cec9892a988ca98b2898b0898aa898926988c698aa698f0e97d0e97f0c97aec97d0a978ea97cca978e8978a8970a8978e697, 0x92c9cb0c9ccec9c92a9c90a9ccca9c8ca9c9289c9089ccc89c8c89c8a89cb269c9269cb309bb2e9b9289bea49bb309a9309ab2e9ab0e9a92c9a90c9acec9ab2a9a92a9ab0a9a8ca9aca89a9269aac69a, 0x92c9f90c9fcec9f92a9f8ca9fac89ff309ed309eb0e9e90c9ecec9ed2a9e90a9e8ca9e0ca9ed289e9089e8c89e8a89eb309db2e9d92c9dcec9d92a9dd0a9d8ca9dd089db309c9309cb2e9cb0e9cb2c9c, 0xb0ea3b0ca3ea8a3b0ea290ca2ceca2d2aa28caa2b30a1b2ea1f0ea192ca1d0ca1ceca192aa1d0aa18caa1b30a0930a0b2ea0b0ea092ca0ceca092aa0ccaa08caa0b28a0b08a0b309f9309fb2e9fb0e9f, 0x8a8ae8c6ae8a6ae886aeb0eaaf2ea9b0ea9b30a8b2ea8f0ea8b0ea790ea7b0ca790ca7b0ea6d2ca690ca6ceca6b30a5b2ea5f0ea592ca5d0ca5ceca5b30a4930a4b2ea4b0ea492ca4ceca4b2aa492aa4, 0xb26b2b30b192eb1d0eb1b2cb1f0cb192ab18eab1ccab1b26b1ae6b1b30b092eb0d0eb092cb0d0cb08ecb0b2ab0ac6b0b30af92eafd0eaf92cafd0caf8ecaff30aed2eaed0eaed2caed0cae8caae8c8ae, 0xb2ab8aeab8d0eb7d0cb78ecb7b30b692cb6d0cb6b30b592eb5d0eb5b30b492eb4d0eb492cb4d0cb48ecb4f30b3d0eb3d0cb38ecb3d2ab38eab38cab3b30b2b2eb2f0eb292cb2d0cb292ab2ceab28cab2, 0xf30c1d30c1d2ec190ec1d2cc190cc18ecc18eac18cac1b08c1aa8c18e6c18c6c1aa6c1d2ebdd0ebd90ebcb30bbb2ebbb2cbbd0ebad2cbad0cba8ecbab30b992cb9d0cb9cecb9b2ab9b30b892eb8d0eb8, 0x8eac5ccac58cac5908c58e8c5cc8c58c8c58a8c5ae6c58e6c5f30c4d2ec4ea4c4f30c3d30c3d2ec390ec3d2cc390cc38ecc3b0ac38eac38cac3ca8c38e6c3ac6c38c6c3f0ec2d0cc2d0ac28cac2e84c2, 0x8cac8ac8c8f30c7d2ec7d2cc78ecc7d0ac78eac78cac7d08c7f30c6d30c6f2ec6b0ec6d2cc690cc690ac6ceac68cac6908c6ce8c68c8c68a8c6f30c5d30c5d2ec590ec5f2cc5d2cc5b0cc58ecc590ac5, 0xd0ecbd2ccbd0ccb8eccbd0acb8eacb8cacbf30cad30cad2cca90ccaceaca8cacaf30c9d30c9d2ec990ec9d2cc98ecc98eac9ccac98cac9b08c9ae8c9f30c8d30c8d2ec890ec8d2cc890cc88ecc88eac8, 0xf30d1d2ed1d0ed1f30d0d30d0f2ed0f2cd0d2cd0f30cfd2ecfd0ecfd2ccfd0ccf8eccff30ced30ced2cce90ccececcef30cdd30cdd2ecd90ecdd2ccd8eccdaeacd8eacdf0eccd0cccea8ccf30cbd2ecb, 0x8caddb0edc90cdccecdc90adcceadc8cadcb0edb90cdb90adb8cadbf30da8ecdab30d9b2ed992cd9b26d9b30d892ed8b2cd892cd88ecd8b26d8ae6d8b0ed790cd790ad78cad7b08d7e86d7f30d390ed2, 0xe62ecd0ceab0ee9b0ce9b0ae990ae98c8e88c6e8886e8b30e4d2ee390ee3b30e292ee2d0ee2b30e1930e1b2ee1b2ce192ce1d2ce08ece0b30df92cdfcecdfb2adfb30de92ede92cde8ecdeb2adeaeade, 0x8caf1f30f08ecf0f2af0b30efb2eef92cefb2aefb26efb0eee90eee90cee8eceeb0aee90aeeaeaee8caeeb08ee908eeae8ee8c8eeca8ee8a8eec86eeb30ed92eedb2ced92ced8ecedb2aedb26edae6ed, 0x92ef8d0ef8b30f7930f7b2ef7b2cf792cf78ecf6d0af68eaf68caf6d2cf58ecf5b0ef490cf4cecf490af4ceaf48caf4b30f392cf3cecf3b2af3b30f292ef292cf28ecf2b2af2aeaf2b0ef190cf190af1, 0xb0b0490b04aeb04909048e904cc904ca9048a904907048e704cc704ca7048a70488704b3103b2f03b2d0392d03ceb03ccb038cb03b2703b30ffb28ffaecfe8eafe8e6fe8a6feb30fad2ef990ef9b30f8, 0xaed08b310792f07b2d0792d078ed07f0f06d0f068ed06aeb068cb06d09068e9068c906ca9068a906d07068e7068c706ca7068a70688706f31058ed05d2b058eb05ccb058cb05b0f0490f04b0d04aed04, 0x92d0fb0d0fced0fb2b0fb0f0e90f0e90d0e8ed0eb0b0e90b0eacb0e8cb0eb310d92f0db2d0daed0db2b0daeb0d8ed0cb310b92f0bd0f0bb2d0bf0d0bb310ab2d0a92d0ab0f0990d09b310892f08b2d08, 0xd071b8e71bcc71b8a71b8871bf311ad2b1aceb1a8cb1ab3116d0d158ed15d2f14b0f1390d13ced13b3112b2f12b2d1290f11f2d11d2d11b0d118ed11b311092f10d0f10b2d10f0d10b310f9310fb2d0f, 0xb2f22b0f2292d22b2b2292b22eeb22ceb22b0f21b0d21ea921b311fb2f1ff0f1f92d1fd0d1fb0f1e90d1eb311db2f1d92d1db311cb2f1c92d1cf0f1bd0f1baed1b8eb1bd091b8e91bcc91b8a91b0a91b, 0x92d2eced2eb2b2eb312d92f2db2b2daeb2d90f2c90d2c8ed2cb0f28f2f27b0f27b3126b2f26f0f26b0f25d2d2590d25b3124b2f24f0f2492d24d0d24b0f2390f2390d238ed23b0b2390b23b312293122, 0xf2b3cd2b3cf313bd313b90f3b8ed3bf2b3bd2b3baeb3b8eb3bf0f3aea93a8ed39f3138d0f38d0d388ed38f3137f31368ed36f31358ed35d2f32b3131b2f31b2d31d2d308ed3090f2f90d2f8ed2fb312e, 0xd2d478ed47b314692d46ced46b2b46b314592f4592d458ed45b2b45aeb45b0f4490d4490b448cb44f3141f3140d0f40f313fd313f90f3e90d3e8ed3ef313dd0f3dd0d3d8ed3df313cd313c90d3cced3c, 0x8ed55b315492d54ced54b2b54b0f5390d53b0b53acb53b315292f52b2d52aed52b2b52aeb528cb51b0f5090d50ced50b0f4f90b4fb314bd2f4a90f4ab314992f49d0f49b314893148b2f48b2d4892d48, 0xd0f67d2d67d0d678ed6790f6690d668ed66b316592d65d0d65ced65b2b65b316492f64d0f64b2b64aeb64b3160d2d5fb0f5e90d5eb0b5eb315d92d5db2b5deeb5db3158d2f57b3156b2f56b2d56d2d55, 0xd2f7cb317bb2f7bb2d7b8ed7ad0b7a8cb7ad2d798ed79b0f7890f7890b78ccb78b317792d77ced77b2b77e87768c974d0f728ed70ced6ff2b6f8ed6ef2b6eaeb6ed2f6ad0f6a90f69b3168b2f68b2d68, 0xf0d93f2f9290f90d0f8ff2d8ed2d8ed2f8ad0f8a90f89b3188b2f88b2d88b3184b0f8390f83b0d8390d83d0b828eb82ccb82d2d81ced81b317d]

noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdCodes.getD (i / 32) 0
  decodeStep 9 secondAt ((block >>> (20 * (i % 32))) % 1048576)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def thirdSuccessorsList : List (List ℕ) := [
  [0, 1, 2, 3, 4, 5, 6],
  [0, 7, 8, 9, 10, 11, 12],
  [1, 7, 13, 14, 15],
  [2, 8, 13, 16, 17],
  [3, 9, 14, 16, 18, 19, 20],
  [4, 10, 17, 18, 21],
  [5, 11, 19, 21],
  [6, 12, 15, 20],
  [22, 23, 24, 25, 26, 27, 28],
  [29, 30, 31, 32, 33, 34, 35],
  [36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53],
  [54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74],
  [22, 36, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96],
  [23, 37, 75, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113],
  [38, 76, 97, 114, 115, 116, 117, 118, 119, 120],
  [121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132],
  [24, 39, 77, 98, 114, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147],
  [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169],
  [78, 99, 133, 148, 170, 171, 172, 173, 174, 175, 176],
  [79, 100, 134, 149, 177, 178, 179, 180, 181, 182, 183, 184],
  [40, 54, 80, 101, 135, 150, 170, 177, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194],
  [25, 29, 41, 55, 81, 102, 115, 121, 136, 151, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213],
  [42, 56, 82, 137, 152, 171, 178, 185, 214, 215, 216, 217, 218, 219],
  [26, 30, 43, 57, 83, 116, 122, 138, 153, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235],
  [44, 58, 84, 103, 139, 154, 236, 237, 238, 239, 240, 241, 242, 243, 244],
  [45, 59, 85, 104, 172, 179, 186, 214, 245, 246, 247, 248, 249],
  [27, 31, 46, 60, 86, 105, 117, 123, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264],
  [87, 106, 140, 155, 195, 220, 250, 265, 266, 267, 268],
  [88, 107, 141, 156, 196, 197, 221, 251, 269, 270, 271, 272],
  [89, 142, 157, 198, 222, 252, 273, 274],
  [158, 199, 223, 236, 253, 275, 276, 277],
  [90, 108, 200, 224, 254, 278],
  [159, 225, 255, 279, 280],
  [0, 47, 48, 61, 62, 91, 109, 118, 124, 143, 160, 187, 188, 201, 202, 215, 226, 237, 245, 256, 279, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290],
  [1, 49, 50, 63, 64, 92, 119, 125, 144, 161, 189, 203, 216, 227, 238, 246, 257, 281, 282, 291, 292, 293, 294, 295, 296, 297],
  [65, 162, 204, 228, 239, 258, 298, 299, 300],
  [2, 51, 52, 66, 67, 93, 110, 120, 126, 180, 205, 229, 240, 247, 259, 283, 284, 291, 292, 301, 302, 303, 304],
  [3, 32, 68, 94, 111, 127, 163, 173, 181, 190, 206, 241, 248, 260, 265, 269, 275, 278, 285, 293, 298, 301, 305, 306, 307, 308],
  [69, 128, 164, 207, 230, 261, 294, 302, 309],
  [4, 33, 70, 95, 129, 145, 165, 174, 182, 191, 192, 208, 209, 217, 231, 242, 266, 270, 273, 276, 286, 295, 299, 303, 305, 310, 311],
  [71, 130, 166, 210, 232, 262, 287, 304, 310],
  [5, 34, 72, 112, 131, 146, 167, 175, 183, 193, 211, 218, 233, 243, 267, 271, 277, 288, 300, 306, 309, 311],
  [73, 132, 168, 212, 234, 244, 263, 289, 296, 307],
  [6, 28, 35, 53, 74, 96, 113, 147, 169, 176, 184, 194, 213, 219, 235, 249, 264, 268, 272, 274, 280, 290, 297, 308],
  [312, 313, 314, 315, 316, 317, 318],
  [319, 320, 321, 322, 323, 324, 325],
  [22, 312, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341],
  [23, 313, 326, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353],
  [354, 355, 356],
  [24, 314, 327, 342, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367],
  [25, 29, 328, 343, 357, 368, 369, 370, 371, 372, 373, 374],
  [26, 30, 329, 358, 368, 375, 376, 377, 378],
  [27, 31, 330, 344, 369, 375, 379, 380],
  [331, 345, 359, 381, 382, 383, 384],
  [332, 360, 385, 386],
  [333, 346, 361, 387, 388, 389, 390, 391, 392],
  [334, 347, 393],
  [315, 319, 335, 348, 362, 394, 395, 396, 397, 398, 399],
  [316, 320, 336, 363, 394, 400, 401, 402, 403],
  [317, 321, 337, 349, 395, 400, 404, 405],
  [32, 322, 338, 350, 370, 379, 381, 387, 393, 396, 401, 404, 406, 407, 408, 409],
  [339, 354, 388, 410, 411, 412],
  [33, 323, 340, 364, 371, 372, 376, 382, 385, 389, 397, 402, 405, 406, 413, 414],
  [351, 355, 390, 410, 413, 415],
  [34, 324, 352, 365, 373, 377, 383, 391, 398, 407, 411, 414],
  [356, 366, 392, 408, 412, 415],
  [28, 35, 318, 325, 341, 353, 367, 374, 378, 380, 384, 386, 399, 403, 409],
  [416, 417, 418, 419, 420, 421],
  [416, 422, 423, 424, 425, 426, 427, 428],
  [417, 422, 429, 430, 431],
  [418, 423, 429, 432, 433],
  [419, 424, 432, 434, 435, 436],
  [420, 425, 426, 434, 437],
  [421, 427, 430, 435, 437],
  [428, 431, 433, 436, 438],
  [36, 312, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462],
  [463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489],
  [37, 313, 439, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507],
  [38, 440, 508, 509, 510, 511, 512, 513, 514, 515, 516],
  [39, 314, 441, 490, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533],
  [442, 463, 491, 517, 534, 535, 536, 537, 538, 539, 540],
  [443, 464, 492, 518, 541, 542, 543, 544, 545, 546, 547, 548],
  [549, 550, 551, 552],
  [40, 41, 54, 55, 416, 444, 465, 493, 508, 519, 541, 549, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570],
  [42, 43, 56, 57, 417, 445, 466, 509, 520, 553, 554, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585],
  [44, 58, 446, 467, 494, 521, 586, 587, 588, 589, 590, 591, 592, 593],
  [45, 46, 59, 60, 418, 447, 468, 495, 510, 555, 556, 571, 572, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605],
  [469, 606, 607, 608, 609, 610, 611, 612],
  [448, 470, 496, 522, 613, 614, 615, 616, 617, 618, 619, 620],
  [449, 471, 523, 621, 622, 623, 624, 625],
  [450, 472, 497, 524, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635],
  [451, 473, 498, 636, 637, 638, 639],
  [47, 61, 452, 474, 499, 525, 542, 557, 573, 594, 606, 640, 641, 642, 643, 644, 645],
  [48, 62, 315, 319, 453, 475, 500, 511, 526, 534, 558, 559, 574, 586, 595, 613, 614, 621, 626, 636, 646, 647, 648, 649, 650, 651],
  [49, 63, 454, 476, 527, 543, 575, 596, 607, 640, 652, 653, 654, 655],
  [50, 64, 316, 320, 455, 477, 512, 528, 535, 550, 560, 576, 587, 597, 615, 622, 627, 637, 656, 657, 658, 659, 660],
  [65, 456, 478, 501, 529, 561, 577, 588, 598, 628, 661, 662, 663, 664, 665, 666],
  [51, 66, 457, 479, 502, 544, 578, 599, 608, 641, 652, 667, 668],
  [52, 67, 317, 321, 458, 480, 503, 513, 536, 551, 562, 579, 589, 600, 616, 623, 629, 638, 669, 670, 671, 672],
  [68, 322, 419, 459, 481, 482, 504, 537, 545, 563, 590, 601, 609, 617, 630, 639, 642, 646, 653, 656, 661, 667, 669, 673, 674, 675, 676],
  [69, 460, 483, 514, 564, 580, 602, 631, 657, 662, 670, 677, 678, 679],
  [70, 323, 420, 461, 484, 485, 530, 538, 546, 565, 566, 581, 591, 610, 618, 624, 632, 643, 647, 654, 658, 663, 668, 671, 673, 680, 681],
  [71, 486, 505, 515, 567, 582, 603, 633, 648, 664, 672, 677, 680, 682],
  [72, 324, 421, 487, 506, 531, 539, 547, 568, 583, 592, 611, 619, 634, 644, 649, 665, 674, 678, 681],
  [73, 488, 516, 532, 569, 584, 593, 604, 635, 650, 659, 666, 675, 679, 682],
  [53, 74, 318, 325, 438, 462, 489, 507, 533, 540, 548, 552, 570, 585, 605, 612, 620, 625, 645, 651, 655, 660, 676],
  [683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694],
  [683, 695, 696, 697, 698, 699, 700, 701],
  [684, 702, 703],
  [685, 695, 702, 704, 705, 706, 707, 708, 709],
  [686, 696, 704, 710, 711, 712, 713, 714, 715, 716, 717, 718],
  [687, 697, 705, 710, 711, 719, 720, 721, 722, 723, 724],
  [688, 698, 706, 712, 719, 725, 726],
  [689, 713, 720, 727, 728, 729, 730],
  [690, 699, 714, 721, 727, 731, 732],
  [691, 715, 722, 728, 731, 733, 734],
  [692, 707, 716, 723, 729, 732, 733],
  [693, 700, 703, 708, 717, 725],
  [694, 701, 709, 718, 724, 726, 730, 734],
  [75, 326, 439, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756],
  [757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778],
  [76, 440, 735, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790],
  [77, 327, 441, 736, 779, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807],
  [808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829],
  [78, 442, 463, 683, 737, 757, 780, 791, 808, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848],
  [684, 738, 758, 792, 809, 849, 850, 851, 852, 853, 854, 855],
  [79, 443, 464, 685, 739, 759, 781, 793, 810, 830, 849, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874],
  [80, 81, 328, 444, 465, 740, 760, 794, 811, 831, 856, 857, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889],
  [82, 83, 329, 445, 466, 686, 812, 832, 858, 875, 876, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906],
  [84, 446, 467, 741, 761, 795, 813, 907, 908, 909, 910, 911, 912, 913, 914],
  [85, 86, 330, 447, 468, 687, 742, 762, 782, 833, 859, 877, 878, 890, 891, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929],
  [87, 469, 688, 743, 763, 783, 796, 814, 834, 860, 879, 892, 915, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942],
  [88, 331, 448, 470, 744, 764, 797, 815, 880, 893, 916, 930, 943, 944, 945, 946, 947, 948, 949, 950, 951],
  [89, 332, 449, 471, 689, 816, 881, 894, 917, 943, 952, 953, 954, 955, 956, 957, 958, 959],
  [333, 450, 472, 745, 765, 798, 817, 835, 895, 907, 918, 960, 961, 962, 963, 964, 965, 966, 967, 968],
  [90, 334, 451, 473, 690, 746, 766, 784, 836, 882, 896, 919, 944, 952, 969, 970, 971, 972, 973, 974, 975],
  [91, 335, 452, 453, 474, 475, 747, 767, 799, 818, 837, 861, 883, 897, 920, 931, 945, 953, 969, 976, 977, 978, 979, 980, 981, 982, 983],
  [92, 336, 454, 455, 476, 477, 691, 819, 838, 862, 884, 898, 908, 921, 932, 946, 954, 960, 970, 976, 977, 984, 985, 986, 987, 988, 989, 990, 991],
  [456, 478, 748, 768, 800, 820, 863, 899, 909, 922, 961, 992, 993, 994, 995, 996, 997],
  [93, 337, 457, 458, 479, 480, 692, 749, 769, 785, 839, 864, 865, 885, 900, 910, 923, 933, 947, 955, 962, 971, 978, 979, 984, 985, 998, 999, 1000, 1001, 1002, 1003],
  [481, 750, 770, 821, 840, 850, 866, 886, 924, 934, 948, 972, 980, 986, 998, 1004, 1005, 1006],
  [94, 338, 459, 482, 751, 771, 786, 801, 822, 841, 851, 867, 911, 925, 935, 963, 973, 987, 992, 999, 1007, 1008, 1009],
  [339, 460, 483, 752, 772, 787, 802, 823, 842, 868, 901, 926, 936, 956, 964, 974, 988, 993, 1000, 1010, 1011, 1012],
  [484, 773, 803, 824, 843, 852, 869, 887, 937, 949, 981, 1001, 1004, 1013],
  [95, 340, 461, 485, 753, 774, 788, 804, 825, 844, 853, 870, 902, 912, 938, 957, 965, 989, 994, 1002, 1014, 1015],
  [486, 754, 775, 789, 826, 845, 871, 903, 927, 939, 966, 975, 995, 1003, 1010, 1014, 1016],
  [487, 693, 755, 776, 805, 827, 846, 854, 872, 888, 904, 913, 940, 950, 967, 982, 996, 1005, 1007, 1011, 1013, 1015],
  [488, 777, 790, 806, 828, 847, 873, 905, 914, 928, 941, 958, 968, 990, 997, 1008, 1012, 1016],
  [96, 341, 462, 489, 694, 756, 778, 807, 829, 848, 855, 874, 889, 906, 929, 942, 951, 959, 983, 991, 1006, 1009],
  [97, 735, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031],
  [98, 342, 490, 736, 1017, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045, 1046, 1047],
  [1048, 1049, 1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057, 1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065, 1066],
  [99, 491, 737, 757, 1018, 1032, 1048, 1067, 1068, 1069, 1070, 1071, 1072, 1073, 1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081],
  [738, 758, 1033, 1049, 1082, 1083, 1084, 1085, 1086],
  [100, 492, 739, 759, 1019, 1034, 1050, 1067, 1082, 1087, 1088, 1089, 1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097, 1098, 1099, 1100, 1101],
  [1051, 1102, 1103, 1104, 1105],
  [101, 102, 343, 493, 740, 760, 1020, 1035, 1052, 1068, 1087, 1088, 1102, 1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113, 1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121, 1122, 1123, 1124],
  [103, 494, 741, 761, 1036, 1053, 1125, 1126, 1127, 1128, 1129, 1130, 1131, 1132],
  [104, 105, 344, 495, 742, 762, 1021, 1069, 1089, 1106, 1107, 1133, 1134, 1135, 1136, 1137, 1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145],
  [106, 743, 763, 1022, 1037, 1054, 1070, 1090, 1108, 1133, 1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153, 1154, 1155],
  [107, 345, 496, 744, 764, 1023, 1038, 1055, 1109, 1110, 1134, 1146, 1156, 1157, 1158, 1159, 1160, 1161, 1162, 1163, 1164, 1165, 1166],
  [346, 497, 745, 765, 1039, 1056, 1071, 1111, 1125, 1135, 1156, 1167, 1168, 1169, 1170, 1171, 1172, 1173, 1174, 1175],
  [108, 347, 498, 746, 766, 1024, 1072, 1112, 1136, 1157, 1176, 1177, 1178, 1179, 1180],
  [1057, 1137, 1181, 1182, 1183],
  [109, 348, 499, 500, 747, 767, 1025, 1040, 1058, 1073, 1091, 1113, 1114, 1126, 1138, 1147, 1158, 1159, 1167, 1176, 1181, 1184, 1185, 1186, 1187, 1188, 1189, 1190, 1191],
  [501, 748, 768, 1041, 1059, 1092, 1115, 1127, 1139, 1168, 1192, 1193, 1194, 1195, 1196, 1197],
  [110, 349, 502, 503, 749, 769, 1026, 1074, 1093, 1094, 1103, 1116, 1128, 1140, 1148, 1160, 1169, 1177, 1184, 1185, 1198, 1199, 1200, 1201],
  [111, 350, 504, 750, 751, 770, 771, 1027, 1042, 1060, 1075, 1083, 1095, 1117, 1129, 1141, 1149, 1161, 1170, 1178, 1186, 1192, 1198, 1202, 1203, 1204, 1205],
  [752, 772, 1028, 1061, 1076, 1096, 1118, 1142, 1150, 1171, 1179, 1193, 1199, 1206, 1207, 1208],
  [753, 773, 774, 1043, 1062, 1077, 1084, 1097, 1119, 1120, 1130, 1151, 1162, 1172, 1187, 1194, 1200, 1202, 1203, 1209, 1210],
  [351, 505, 754, 775, 1029, 1044, 1063, 1078, 1098, 1121, 1143, 1152, 1163, 1173, 1180, 1188, 1195, 1201, 1206, 1209, 1211],
  [112, 352, 506, 755, 776, 1030, 1045, 1064, 1079, 1085, 1099, 1104, 1122, 1131, 1153, 1164, 1174, 1182, 1189, 1196, 1207, 1210],
  [777, 1031, 1046, 1065, 1080, 1100, 1123, 1132, 1144, 1154, 1165, 1175, 1190, 1197, 1204, 1208, 1211],
  [113, 353, 507, 756, 778, 1047, 1066, 1081, 1086, 1101, 1105, 1124, 1145, 1155, 1166, 1183, 1191, 1205],
  [114, 779, 1017, 1212, 1213, 1214, 1215, 1216, 1217, 1218, 1219, 1220, 1221, 1222],
  [780, 1018, 1212, 1223, 1224, 1225, 1226, 1227, 1228],
  [781, 1019, 1213, 1229, 1230, 1231, 1232, 1233, 1234, 1235, 1236],
  [115, 121, 508, 1020, 1214, 1229, 1237, 1238, 1239, 1240, 1241, 1242, 1243, 1244, 1245, 1246],
  [116, 122, 509, 1237, 1247, 1248, 1249, 1250, 1251, 1252, 1253, 1254, 1255],
  [117, 123, 510, 782, 1021, 1238, 1247, 1256, 1257, 1258, 1259, 1260, 1261, 1262],
  [783, 1022, 1215, 1263, 1264, 1265, 1266, 1267, 1268],
  [1023, 1216, 1269, 1270, 1271],
  [1272, 1273, 1274],
  [784, 1024, 1275, 1276, 1277],
  [118, 124, 511, 1025, 1217, 1239, 1248, 1256, 1278, 1279, 1280, 1281, 1282],
  [119, 125, 512, 1240, 1249, 1257, 1278, 1283, 1284, 1285, 1286, 1287],
  [120, 126, 513, 785, 1026, 1230, 1241, 1250, 1258, 1279, 1283, 1288, 1289, 1290, 1291],
  [127, 786, 1027, 1223, 1231, 1259, 1263, 1275, 1284, 1288, 1292, 1293, 1294],
  [128, 354, 514, 787, 1028, 1218, 1224, 1232, 1242, 1251, 1260, 1264, 1272, 1276, 1285, 1289, 1295],
  [129, 788, 1219, 1225, 1233, 1243, 1252, 1265, 1273, 1286, 1290, 1292, 1296, 1297],
  [130, 355, 515, 789, 1029, 1220, 1226, 1234, 1244, 1253, 1261, 1266, 1269, 1277, 1280, 1291, 1296],
  [131, 1030, 1221, 1227, 1235, 1245, 1254, 1267, 1270, 1281, 1293, 1295, 1297],
  [132, 356, 516, 790, 1031, 1222, 1228, 1236, 1246, 1255, 1262, 1268, 1271, 1274, 1282, 1287, 1294],
  [133, 148, 517, 791, 808, 1032, 1048, 1212, 1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305, 1306, 1307, 1308, 1309, 1310, 1311],
  [792, 809, 1033, 1049, 1312, 1313, 1314, 1315, 1316],
  [134, 149, 518, 793, 810, 1034, 1050, 1213, 1298, 1312, 1317, 1318, 1319, 1320, 1321, 1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329, 1330],
  [1051, 1331, 1332, 1333],
  [135, 136, 150, 151, 357, 519, 794, 811, 1035, 1052, 1214, 1299, 1317, 1318, 1331, 1334, 1335, 1336, 1337, 1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345, 1346, 1347, 1348, 1349, 1350, 1351, 1352],
  [137, 138, 152, 153, 358, 520, 812, 1300, 1319, 1334, 1335, 1353, 1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361, 1362, 1363, 1364, 1365],
  [139, 154, 521, 795, 813, 1036, 1053, 1366, 1367, 1368, 1369, 1370, 1371, 1372, 1373],
  [140, 155, 796, 814, 1037, 1054, 1215, 1301, 1320, 1336, 1353, 1374, 1375, 1376, 1377, 1378, 1379, 1380, 1381, 1382, 1383],
  [141, 156, 359, 522, 797, 815, 1038, 1055, 1216, 1337, 1338, 1354, 1374, 1384, 1385, 1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393, 1394],
  [142, 157, 360, 523, 816, 1339, 1355, 1384, 1395, 1396, 1397, 1398, 1399, 1400],
  [158, 361, 524, 798, 817, 1039, 1056, 1302, 1340, 1356, 1366, 1385, 1401, 1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409],
  [159, 1057, 1410, 1411, 1412],
  [143, 160, 362, 525, 526, 799, 818, 1040, 1058, 1217, 1303, 1321, 1341, 1342, 1357, 1367, 1375, 1386, 1387, 1395, 1401, 1410, 1413, 1414, 1415, 1416, 1417, 1418, 1419, 1420],
  [144, 161, 363, 527, 528, 819, 1304, 1322, 1343, 1358, 1368, 1376, 1388, 1396, 1402, 1413, 1414, 1421, 1422, 1423, 1424, 1425],
  [162, 529, 800, 820, 1041, 1059, 1323, 1344, 1359, 1369, 1403, 1426, 1427, 1428, 1429, 1430, 1431],
  [163, 801, 821, 822, 1042, 1060, 1305, 1313, 1324, 1345, 1370, 1377, 1389, 1404, 1415, 1421, 1426, 1432, 1433, 1434, 1435, 1436],
  [164, 802, 823, 1061, 1218, 1306, 1325, 1346, 1360, 1378, 1397, 1405, 1422, 1427, 1437, 1438, 1439],
  [145, 165, 364, 530, 803, 804, 824, 825, 1043, 1062, 1219, 1307, 1314, 1326, 1347, 1348, 1361, 1371, 1379, 1390, 1398, 1406, 1416, 1423, 1428, 1432, 1433, 1440],
  [166, 826, 1044, 1063, 1220, 1308, 1327, 1349, 1362, 1380, 1391, 1407, 1417, 1429, 1437, 1440, 1441],
  [146, 167, 365, 531, 805, 827, 1045, 1064, 1221, 1309, 1315, 1328, 1332, 1350, 1363, 1372, 1381, 1392, 1408, 1411, 1418, 1430, 1434, 1438],
  [168, 366, 532, 806, 828, 1046, 1065, 1222, 1310, 1329, 1351, 1364, 1373, 1382, 1393, 1399, 1409, 1419, 1424, 1431, 1435, 1439, 1441],
  [147, 169, 367, 533, 807, 829, 1047, 1066, 1311, 1316, 1330, 1333, 1352, 1365, 1383, 1394, 1400, 1412, 1420, 1425, 1436],
  [695, 830, 1067, 1298, 1442, 1443, 1444, 1445, 1446, 1447],
  [170, 831, 1068, 1299, 1448, 1449, 1450, 1451, 1452, 1453, 1454],
  [171, 696, 832, 1300, 1448, 1455, 1456, 1457, 1458],
  [172, 697, 833, 1069, 1449, 1455, 1459, 1460],
  [698, 834, 1070, 1301, 1442, 1461, 1462, 1463, 1464],
  [835, 1071, 1302, 1465, 1466, 1467, 1468, 1469, 1470],
  [699, 836, 1072, 1471],
  [534, 837, 1073, 1303, 1472, 1473, 1474, 1475, 1476, 1477],
  [535, 838, 1304, 1472, 1478, 1479, 1480, 1481],
  [536, 839, 1074, 1443, 1473, 1478, 1482, 1483],
  [173, 537, 840, 841, 1075, 1223, 1305, 1444, 1450, 1459, 1461, 1465, 1471, 1474, 1479, 1482, 1484, 1485, 1486, 1487, 1488],
  [842, 1076, 1224, 1306, 1466, 1489, 1490, 1491],
  [174, 538, 843, 844, 1077, 1225, 1307, 1445, 1451, 1452, 1456, 1462, 1467, 1475, 1480, 1483, 1484, 1485, 1492, 1493],
  [845, 1078, 1226, 1308, 1468, 1489, 1492, 1494],
  [175, 539, 700, 846, 1079, 1227, 1309, 1446, 1453, 1457, 1463, 1469, 1476, 1486, 1490, 1493],
  [847, 1080, 1228, 1310, 1470, 1487, 1491, 1494],
  [176, 540, 701, 848, 1081, 1311, 1447, 1454, 1458, 1460, 1464, 1477, 1481, 1488],
  [702, 849, 1082, 1312, 1495, 1496, 1497],
  [850, 851, 1083, 1313, 1495, 1498, 1499, 1500, 1501],
  [852, 853, 1084, 1314, 1496, 1498, 1499, 1502],
  [703, 854, 1085, 1315, 1497, 1500, 1502],
  [855, 1086, 1316, 1501, 1503],
  [177, 856, 1087, 1317, 1504, 1505, 1506, 1507, 1508, 1509, 1510, 1511],
  [541, 857, 1088, 1229, 1318, 1512, 1513, 1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521, 1522, 1523, 1524, 1525, 1526],
  [178, 704, 858, 1319, 1504, 1527, 1528, 1529, 1530, 1531],
  [179, 705, 859, 1089, 1505, 1527, 1532, 1533, 1534],
  [706, 860, 1090, 1320, 1442, 1512, 1535, 1536, 1537, 1538],
  [542, 861, 1091, 1321, 1513, 1514, 1539, 1540, 1541, 1542, 1543, 1544],
  [543, 862, 1322, 1515, 1539, 1545, 1546, 1547, 1548],
  [863, 1092, 1323, 1516, 1549, 1550, 1551, 1552, 1553, 1554],
  [544, 864, 1093, 1517, 1540, 1545, 1555, 1556],
  [180, 707, 865, 1094, 1230, 1443, 1506, 1518, 1528, 1532, 1557, 1558, 1559, 1560],
  [181, 545, 866, 867, 1095, 1231, 1324, 1444, 1495, 1507, 1519, 1533, 1535, 1541, 1546, 1549, 1555, 1557, 1561, 1562, 1563, 1564, 1565],
  [868, 1096, 1232, 1325, 1520, 1550, 1558, 1566, 1567, 1568],
  [182, 546, 869, 870, 1097, 1233, 1326, 1445, 1496, 1508, 1509, 1521, 1522, 1529, 1536, 1542, 1547, 1551, 1556, 1559, 1561, 1562, 1569, 1570],
  [871, 1098, 1234, 1327, 1523, 1552, 1560, 1566, 1569, 1571],
  [183, 547, 708, 872, 1099, 1235, 1328, 1446, 1497, 1510, 1524, 1530, 1537, 1543, 1553, 1563, 1567, 1570],
  [873, 1100, 1236, 1329, 1525, 1554, 1564, 1568, 1571],
  [184, 548, 709, 874, 1101, 1330, 1447, 1503, 1511, 1526, 1531, 1534, 1538, 1544, 1548, 1565],
  [549, 1102, 1331, 1572, 1573, 1574, 1575],
  [550, 1572, 1576, 1577],
  [551, 1103, 1573, 1576],
  [1104, 1332, 1574],
  [552, 1105, 1333, 1575, 1577],
  [185, 553, 875, 1334, 1448, 1504, 1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585],
  [368, 422, 554, 876, 1237, 1335, 1586, 1587, 1588, 1589, 1590, 1591, 1592, 1593, 1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601, 1602, 1603],
  [186, 555, 877, 1106, 1449, 1505, 1578, 1604, 1605, 1606, 1607, 1608, 1609],
  [369, 423, 556, 878, 1107, 1238, 1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617, 1618, 1619, 1620, 1621, 1622, 1623, 1624, 1625],
  [195, 879, 1108, 1336, 1512, 1586, 1610, 1626, 1627, 1628, 1629, 1630],
  [196, 880, 1109, 1337, 1587, 1611, 1631, 1632, 1633, 1634],
  [197, 1110, 1338, 1588, 1612, 1635, 1636],
  [198, 881, 1339, 1589, 1613, 1637, 1638, 1639],
  [199, 1111, 1340, 1590, 1614, 1640, 1641, 1642, 1643, 1644],
  [200, 882, 1112, 1591, 1615, 1645],
  [187, 201, 558, 883, 1113, 1341, 1513, 1579, 1592, 1604, 1616, 1646, 1647, 1648, 1649, 1650, 1651],
  [188, 202, 557, 559, 1114, 1239, 1342, 1514, 1580, 1593, 1605, 1617, 1652, 1653, 1654, 1655, 1656, 1657, 1658, 1659],
  [189, 203, 560, 884, 1240, 1343, 1515, 1572, 1581, 1594, 1606, 1618, 1646, 1652, 1653, 1660, 1661, 1662, 1663, 1664, 1665, 1666],
  [204, 561, 1115, 1344, 1516, 1595, 1619, 1667, 1668, 1669, 1670, 1671],
  [205, 562, 885, 1116, 1241, 1506, 1517, 1518, 1573, 1596, 1607, 1620, 1647, 1654, 1655, 1660, 1672, 1673, 1674, 1675, 1676],
  [190, 206, 370, 424, 563, 886, 1117, 1345, 1450, 1507, 1519, 1608, 1621, 1626, 1631, 1645, 1648, 1661, 1672, 1677, 1678, 1679],
  [207, 564, 1118, 1242, 1346, 1520, 1597, 1622, 1640, 1662, 1667, 1673, 1680, 1681, 1682],
  [191, 208, 371, 425, 565, 887, 1119, 1347, 1451, 1508, 1521, 1582, 1598, 1627, 1632, 1637, 1649, 1663, 1674, 1677, 1683],
  [192, 209, 372, 426, 566, 1120, 1243, 1348, 1452, 1509, 1522, 1583, 1599, 1628, 1638, 1641, 1664, 1668, 1675, 1684, 1685],
  [210, 567, 1121, 1244, 1349, 1523, 1600, 1623, 1642, 1656, 1669, 1676, 1680, 1684, 1686],
  [193, 211, 373, 427, 568, 888, 1122, 1245, 1350, 1453, 1510, 1524, 1574, 1584, 1601, 1629, 1633, 1635, 1643, 1650, 1657, 1670, 1678, 1681, 1683, 1685],
  [212, 569, 1123, 1246, 1351, 1525, 1602, 1624, 1644, 1658, 1665, 1671, 1682, 1686],
  [194, 213, 374, 428, 570, 889, 1124, 1352, 1454, 1511, 1526, 1575, 1585, 1603, 1609, 1625, 1630, 1634, 1636, 1639, 1651, 1659, 1666, 1679],
  [214, 571, 710, 890, 1455, 1527, 1578, 1687, 1688, 1689, 1690],
  [375, 429, 572, 711, 891, 1247, 1691, 1692, 1693, 1694, 1695, 1696, 1697, 1698, 1699, 1700, 1701, 1702, 1703, 1704],
  [220, 712, 892, 1353, 1586, 1691, 1705, 1706, 1707],
  [221, 893, 1354, 1587, 1588, 1692, 1708, 1709, 1710],
  [222, 713, 894, 1355, 1589, 1693, 1711, 1712],
  [223, 895, 1356, 1590, 1694, 1713, 1714, 1715, 1716, 1717],
  [224, 714, 896, 1591, 1695],
  [225, 1696, 1718, 1719, 1720],
  [215, 226, 573, 574, 897, 1248, 1357, 1579, 1580, 1592, 1593, 1687, 1697, 1718, 1721, 1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729],
  [216, 227, 575, 576, 715, 898, 1249, 1358, 1581, 1594, 1688, 1698, 1721, 1722, 1730, 1731, 1732, 1733, 1734, 1735],
  [228, 577, 899, 1359, 1595, 1699, 1736, 1737, 1738, 1739, 1740],
  [229, 578, 579, 716, 900, 1250, 1528, 1596, 1689, 1700, 1723, 1724, 1730, 1731, 1741, 1742, 1743],
  [230, 580, 901, 1251, 1360, 1597, 1701, 1713, 1732, 1736, 1741, 1744, 1745, 1746],
  [217, 231, 376, 581, 902, 1252, 1361, 1456, 1529, 1582, 1583, 1598, 1599, 1705, 1708, 1711, 1714, 1725, 1733, 1737, 1742, 1747, 1748],
  [232, 582, 903, 1253, 1362, 1600, 1702, 1715, 1726, 1738, 1743, 1744, 1747, 1749],
  [218, 233, 377, 430, 583, 717, 904, 1254, 1363, 1457, 1530, 1584, 1601, 1706, 1709, 1716, 1719, 1727, 1739, 1745, 1748],
  [234, 584, 905, 1255, 1364, 1602, 1703, 1717, 1728, 1734, 1740, 1746, 1749],
  [219, 235, 378, 431, 585, 718, 906, 1365, 1458, 1531, 1585, 1603, 1690, 1704, 1707, 1710, 1712, 1720, 1729, 1735],
  [236, 907, 1125, 1366, 1750, 1751, 1752],
  [237, 586, 1126, 1367, 1753, 1754, 1755, 1756],
  [238, 587, 908, 1368, 1753, 1757, 1758, 1759, 1760],
  [239, 588, 909, 1127, 1369, 1761, 1762, 1763],
  [240, 589, 910, 1128, 1754, 1757, 1764, 1765],
  [241, 590, 911, 1129, 1370, 1750, 1758, 1761, 1764, 1766, 1767, 1768],
  [242, 591, 912, 1130, 1371, 1751, 1759, 1762, 1765, 1766, 1769],
  [243, 592, 913, 1131, 1372, 1752, 1755, 1763, 1767, 1769],
  [244, 593, 914, 1132, 1373, 1756, 1760, 1768],
  [250, 719, 915, 1133, 1610, 1691, 1770, 1771],
  [251, 916, 1134, 1611, 1612, 1692, 1772, 1773],
  [252, 720, 917, 1613, 1693, 1774],
  [253, 918, 1135, 1614, 1694, 1775, 1776, 1777, 1778],
  [254, 721, 919, 1136, 1615, 1695, 1779],
  [255, 1137, 1696, 1780, 1781],
  [245, 256, 594, 595, 920, 1138, 1256, 1604, 1605, 1616, 1617, 1687, 1697, 1780, 1782, 1783, 1784, 1785, 1786, 1787, 1788, 1789],
  [246, 257, 596, 597, 722, 921, 1257, 1606, 1618, 1688, 1698, 1782, 1783, 1790, 1791, 1792, 1793, 1794, 1795],
  [258, 598, 922, 1139, 1619, 1699, 1796, 1797, 1798, 1799],
  [247, 259, 599, 600, 723, 923, 1140, 1258, 1532, 1607, 1620, 1689, 1700, 1784, 1785, 1790, 1791, 1800, 1801, 1802],
  [248, 260, 379, 432, 601, 924, 925, 1141, 1259, 1459, 1533, 1608, 1621, 1770, 1772, 1775, 1779, 1786, 1792, 1796, 1800, 1803, 1804],
  [261, 602, 926, 1142, 1260, 1622, 1701, 1776, 1793, 1797, 1801, 1805, 1806],
  [262, 603, 927, 1143, 1261, 1623, 1702, 1777, 1787, 1798, 1802, 1805, 1807],
  [263, 604, 928, 1144, 1262, 1624, 1703, 1778, 1788, 1794, 1799, 1803, 1806, 1807],
  [249, 264, 380, 433, 605, 724, 929, 1145, 1460, 1534, 1609, 1625, 1690, 1704, 1771, 1773, 1774, 1781, 1789, 1795, 1804],
  [930, 1146, 1374, 1808, 1809, 1810, 1811],
  [606, 931, 1147, 1375, 1812, 1813, 1814, 1815, 1816, 1817],
  [607, 932, 1376, 1812, 1818, 1819, 1820, 1821],
  [608, 933, 1148, 1813, 1818, 1822, 1823],
  [265, 609, 934, 935, 1149, 1263, 1377, 1461, 1535, 1626, 1770, 1808, 1814, 1819, 1822, 1824, 1825, 1826, 1827, 1828],
  [936, 1150, 1264, 1378, 1829, 1830, 1831],
  [266, 610, 937, 938, 1151, 1265, 1379, 1462, 1536, 1627, 1628, 1705, 1809, 1815, 1820, 1823, 1824, 1825, 1832, 1833],
  [939, 1152, 1266, 1380, 1829, 1832, 1834],
  [267, 611, 725, 940, 1153, 1267, 1381, 1463, 1537, 1629, 1706, 1810, 1816, 1826, 1830, 1833],
  [941, 1154, 1268, 1382, 1827, 1831, 1834],
  [268, 612, 726, 942, 1155, 1383, 1464, 1538, 1630, 1707, 1771, 1811, 1817, 1821, 1828],
  [943, 1384, 1835, 1836],
  [1156, 1385, 1837, 1838, 1839],
  [944, 1157, 1840],
  [613, 945, 1158, 1386, 1841, 1842, 1843, 1844, 1845, 1846],
  [614, 1159, 1387, 1847, 1848, 1849, 1850],
  [615, 946, 1388, 1841, 1847, 1851, 1852, 1853, 1854],
  [616, 947, 1160, 1842, 1848, 1851, 1855, 1856],
  [269, 381, 617, 948, 1161, 1389, 1631, 1772, 1808, 1840, 1843, 1852, 1855, 1857, 1858, 1859],
  [270, 382, 618, 949, 1162, 1390, 1632, 1708, 1809, 1835, 1844, 1853, 1856, 1857, 1860],
  [1163, 1269, 1391, 1837, 1861],
  [271, 383, 619, 950, 1164, 1270, 1392, 1633, 1635, 1709, 1810, 1838, 1845, 1849, 1858, 1860],
  [1165, 1271, 1393, 1839, 1861],
  [272, 384, 620, 951, 1166, 1394, 1634, 1636, 1710, 1773, 1811, 1836, 1846, 1850, 1854, 1859],
  [727, 952],
  [621, 953, 1395, 1862, 1863, 1864, 1865],
  [622, 728, 954, 1396, 1862, 1866, 1867, 1868],
  [623, 729, 955, 1863, 1866, 1869],
  [956, 1272, 1397, 1870],
  [273, 385, 624, 957, 1273, 1398, 1637, 1638, 1711, 1835, 1864, 1867, 1869],
  [958, 1274, 1399, 1870],
  [274, 386, 625, 730, 959, 1400, 1639, 1712, 1774, 1836, 1865, 1868],
  [626, 1167, 1401, 1871, 1872, 1873, 1874, 1875],
  [627, 960, 1402, 1871, 1876, 1877, 1878, 1879, 1880],
  [628, 961, 1168, 1403, 1881, 1882, 1883],
  [629, 962, 1169, 1872, 1876, 1884, 1885, 1886, 1887],
  [275, 387, 630, 963, 1170, 1404, 1465, 1750, 1775, 1877, 1881, 1884, 1888, 1889, 1890],
  [388, 631, 964, 1171, 1405, 1466, 1640, 1713, 1776, 1878, 1885, 1891],
  [276, 389, 632, 965, 1172, 1406, 1467, 1641, 1714, 1751, 1879, 1882, 1886, 1888, 1892, 1893],
  [390, 633, 966, 1173, 1407, 1468, 1642, 1715, 1777, 1837, 1873, 1887, 1892],
  [277, 391, 634, 967, 1174, 1408, 1469, 1643, 1716, 1752, 1838, 1874, 1883, 1889, 1891, 1893],
  [392, 635, 968, 1175, 1409, 1470, 1644, 1717, 1778, 1839, 1875, 1880, 1890],
  [636, 969, 1176, 1894, 1895, 1896],
  [637, 731, 970, 1894, 1897, 1898],
  [638, 732, 971, 1177, 1895, 1897, 1899],
  [278, 393, 639, 972, 973, 1178, 1275, 1471, 1645, 1779, 1840, 1896, 1898, 1899],
  [974, 1179, 1276, 1900],
  [975, 1180, 1277, 1900],
  [279, 1181, 1410, 1718, 1780, 1901],
  [1182, 1411, 1719, 1901],
  [280, 1183, 1412, 1720, 1781, 1902],
  [281, 640, 976, 1413, 1539, 1652, 1721, 1782, 1812, 1903, 1904, 1905, 1906],
  [7, 282, 394, 977, 1278, 1414, 1472, 1646, 1653, 1722, 1753, 1783, 1841, 1847, 1862, 1871, 1894, 1907, 1908, 1909, 1910],
  [283, 641, 978, 1184, 1540, 1654, 1723, 1784, 1813, 1903, 1911, 1912],
  [8, 284, 395, 979, 1185, 1279, 1473, 1647, 1655, 1724, 1754, 1785, 1842, 1848, 1863, 1872, 1895, 1913, 1914, 1915],
  [9, 285, 396, 642, 646, 980, 1186, 1415, 1474, 1541, 1648, 1786, 1814, 1843, 1896, 1904, 1907, 1911, 1913, 1916, 1917, 1918],
  [10, 286, 397, 643, 647, 981, 1187, 1416, 1475, 1542, 1649, 1725, 1815, 1844, 1864, 1905, 1908, 1912, 1914, 1916, 1919],
  [287, 648, 1188, 1280, 1417, 1656, 1726, 1787, 1873, 1915, 1920],
  [11, 288, 398, 644, 649, 982, 1189, 1281, 1418, 1476, 1543, 1650, 1657, 1727, 1755, 1816, 1845, 1849, 1874, 1901, 1917, 1919],
  [289, 650, 1190, 1282, 1419, 1658, 1728, 1756, 1788, 1875, 1909, 1920],
  [12, 290, 399, 645, 651, 983, 1191, 1420, 1477, 1544, 1651, 1659, 1729, 1789, 1817, 1846, 1850, 1865, 1902, 1906, 1910, 1918],
  [291, 652, 984, 1545, 1730, 1790, 1818, 1903, 1921, 1922],
  [13, 292, 400, 733, 985, 1283, 1478, 1576, 1660, 1731, 1757, 1791, 1851, 1866, 1876, 1897, 1923, 1924, 1925],
  [14, 293, 401, 653, 656, 986, 987, 1284, 1421, 1479, 1546, 1661, 1758, 1792, 1819, 1852, 1877, 1898, 1904, 1907, 1921, 1923, 1926, 1927, 1928, 1929],
  [294, 657, 988, 1285, 1422, 1662, 1732, 1793, 1878, 1924, 1930],
  [295, 402, 654, 658, 989, 1286, 1423, 1480, 1547, 1663, 1664, 1733, 1759, 1820, 1853, 1867, 1879, 1905, 1908, 1922, 1925, 1926, 1927],
  [296, 659, 990, 1287, 1424, 1665, 1734, 1760, 1794, 1880, 1909, 1928, 1930],
  [15, 297, 403, 655, 660, 734, 991, 1425, 1481, 1548, 1577, 1666, 1735, 1795, 1821, 1854, 1868, 1906, 1910, 1929],
  [298, 661, 992, 1192, 1426, 1549, 1761, 1796, 1881, 1931, 1932, 1933],
  [662, 993, 1193, 1427, 1550, 1667, 1736, 1797, 1934],
  [299, 663, 994, 1194, 1428, 1551, 1668, 1737, 1762, 1882, 1931, 1935, 1936],
  [664, 995, 1195, 1429, 1552, 1669, 1738, 1798, 1935],
  [300, 665, 996, 1196, 1430, 1553, 1670, 1739, 1763, 1883, 1932, 1934, 1936],
  [666, 997, 1197, 1431, 1554, 1671, 1740, 1799, 1933],
  [16, 301, 404, 667, 669, 998, 999, 1198, 1288, 1482, 1555, 1557, 1672, 1764, 1800, 1822, 1855, 1884, 1899, 1911, 1913, 1921, 1923, 1937, 1938],
  [302, 670, 1000, 1199, 1289, 1558, 1673, 1741, 1801, 1885, 1924, 1939],
  [17, 303, 405, 668, 671, 1001, 1002, 1200, 1290, 1483, 1556, 1559, 1674, 1675, 1742, 1765, 1823, 1856, 1869, 1886, 1912, 1914, 1922, 1925, 1937, 1938, 1940],
  [304, 672, 1003, 1201, 1291, 1560, 1676, 1743, 1802, 1887, 1915, 1939, 1940],
  [1004, 1202, 1432, 1484, 1498, 1561, 1677, 1824, 1857, 1916, 1926, 1937, 1941],
  [18, 305, 406, 434, 673, 1203, 1292, 1433, 1485, 1499, 1562, 1766, 1825, 1888, 1927, 1931, 1938, 1942],
  [19, 306, 407, 435, 674, 1005, 1007, 1293, 1434, 1486, 1500, 1563, 1678, 1767, 1826, 1858, 1889, 1917, 1932, 1941, 1942],
  [307, 408, 675, 1008, 1204, 1294, 1435, 1487, 1564, 1768, 1803, 1827, 1890, 1928, 1933],
  [20, 308, 409, 436, 676, 1006, 1009, 1205, 1436, 1488, 1501, 1565, 1679, 1804, 1828, 1859, 1918, 1929],
  [410, 677, 1010, 1206, 1437, 1489, 1566, 1680, 1744, 1805, 1829, 1900, 1939],
  [309, 411, 678, 1011, 1207, 1295, 1438, 1490, 1567, 1681, 1745, 1830, 1891, 1934],
  [412, 679, 1012, 1208, 1439, 1491, 1568, 1682, 1746, 1806, 1831, 1870, 1930],
  [310, 413, 680, 1014, 1209, 1296, 1440, 1492, 1569, 1684, 1747, 1832, 1892, 1935, 1940],
  [21, 311, 414, 437, 681, 1013, 1015, 1210, 1297, 1493, 1502, 1570, 1683, 1685, 1748, 1769, 1833, 1860, 1893, 1919, 1936, 1941, 1942],
  [415, 682, 1016, 1211, 1441, 1494, 1571, 1686, 1749, 1807, 1834, 1861, 1920]]

def thirdSuccessors (i : ℕ) : List ℕ := thirdSuccessorsList.getD i []

noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    mvC I.NN I.AA I.HX I.HY
      (lookC I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 12 1 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1 z v))

lemma afterSecond_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 11)
    (mixed : mixedFromSecond state = false)
    (pure : pureAt 11 state (fun z v => afterThird (z,v)) = false) :
    afterSecond state = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 12 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 12 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [afterSecond, frc_eq, st_eq, show (13 : ℕ) = Nat.succ 12 from rfl, look1C_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureAt 11 state
      (look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 12 11 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

def rangeCheck (test : ℕ → Bool) (start count : ℕ) : Bool :=
  (List.range' start count).all test

lemma rangeCheck_append (test : ℕ → Bool) {s a b : ℕ}
    (left : rangeCheck test s a = true) (right : rangeCheck test (s+a) b = true) :
    rangeCheck test s (a+b) = true := by
  unfold rangeCheck at *
  rw [← List.range'_append_1, List.all_append, left, right]
  rfl

lemma rangeCheck_at {test : ℕ → Bool} {n i : ℕ} (checked : rangeCheck test 0 n = true) (hi : i < n) :
    test i = true :=
  List.all_eq_true.mp checked _ (List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hi⟩)

lemma boolOfNeg {b : Bool} (h : (!b) = true) : b = false := by cases b <;> simp_all

noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  let ids := thirdSuccessors i
  (!pureAt 11 state (frontierMissing (ids.map thirdAt))) &&
    ((ids.all fun j => decide (j < thirdCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 11)))

noncomputable def thirdTest (j : ℕ) : Bool := !afterThird (thirdAt j)
noncomputable def secondMixedTest (j : ℕ) : Bool := !mixedFromSecond (secondAt j)

lemma checkedAfterSecond (i : ℕ) (hi : i < secondCount)
    (ready : rangeCheck readyForThird 0 secondCount = true)
    (mixed : rangeCheck secondMixedTest 0 secondCount = true)
    (third : rangeCheck thirdTest 0 thirdCount = true) :
    afterSecond (secondAt i) = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForThird, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterSecond_false (secondAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_from_frontier 11 (secondAt i) ((thirdSuccessors i).map thirdAt) afterThird (boolOfNeg hc) ?_
  intro state membership
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp membership
  have hj' : j < thirdCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact boolOfNeg (rangeCheck_at third hj')


noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  let ids := secondSuccessors i
  (!pureSecond state (frontierMissing (ids.map secondAt))) &&
    ((ids.all fun j => decide (j < secondCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    look1C I.NN I.AA I.HX I.HY I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureSecond_from_frontier (firstAt i) ((secondSuccessors i).map secondAt) (boolOfNeg hc) ?_
  intro state membership
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp membership
  have hj' : j < secondCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact next j hj'


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 3 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 6 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk3 : rangeCheck readyForSecond 9 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk4 : rangeCheck readyForSecond 12 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk5 : rangeCheck readyForSecond 15 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk6 : rangeCheck readyForSecond 18 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk7 : rangeCheck readyForSecond 21 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk8 : rangeCheck readyForSecond 24 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk9 : rangeCheck readyForSecond 27 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk10 : rangeCheck readyForSecond 30 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk11 : rangeCheck readyForSecond 33 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 firstCount = true := by
  exact (@rangeCheck_append readyForSecond 0 18 17
    (@rangeCheck_append readyForSecond 0 9 9
    (@rangeCheck_append readyForSecond 0 3 6
    firstCoverageChunk0 (@rangeCheck_append readyForSecond 3 3 3
    firstCoverageChunk1 firstCoverageChunk2)) (@rangeCheck_append readyForSecond 9 3 6
    firstCoverageChunk3 (@rangeCheck_append readyForSecond 12 3 3
    firstCoverageChunk4 firstCoverageChunk5))) (@rangeCheck_append readyForSecond 18 9 8
    (@rangeCheck_append readyForSecond 18 3 6
    firstCoverageChunk6 (@rangeCheck_append readyForSecond 21 3 3
    firstCoverageChunk7 firstCoverageChunk8)) (@rangeCheck_append readyForSecond 27 3 5
    firstCoverageChunk9 (@rangeCheck_append readyForSecond 30 3 2
    firstCoverageChunk10 firstCoverageChunk11))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 2 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk2 : rangeCheck firstMixedTest 5 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk3 : rangeCheck firstMixedTest 6 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk4 : rangeCheck firstMixedTest 7 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk5 : rangeCheck firstMixedTest 8 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk6 : rangeCheck firstMixedTest 9 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk7 : rangeCheck firstMixedTest 10 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk8 : rangeCheck firstMixedTest 11 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk9 : rangeCheck firstMixedTest 12 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk10 : rangeCheck firstMixedTest 14 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk11 : rangeCheck firstMixedTest 15 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk12 : rangeCheck firstMixedTest 17 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk13 : rangeCheck firstMixedTest 18 6 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk14 : rangeCheck firstMixedTest 24 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk15 : rangeCheck firstMixedTest 25 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk16 : rangeCheck firstMixedTest 27 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk17 : rangeCheck firstMixedTest 28 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk18 : rangeCheck firstMixedTest 29 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk19 : rangeCheck firstMixedTest 30 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk20 : rangeCheck firstMixedTest 31 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk21 : rangeCheck firstMixedTest 32 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk22 : rangeCheck firstMixedTest 33 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 firstCount = true := by
  exact (@rangeCheck_append firstMixedTest 0 15 20
    (@rangeCheck_append firstMixedTest 0 8 7
    (@rangeCheck_append firstMixedTest 0 5 3
    (@rangeCheck_append firstMixedTest 0 2 3
    firstMixedChunk0 firstMixedChunk1) (@rangeCheck_append firstMixedTest 5 1 2
    firstMixedChunk2 (@rangeCheck_append firstMixedTest 6 1 1
    firstMixedChunk3 firstMixedChunk4))) (@rangeCheck_append firstMixedTest 8 3 4
    (@rangeCheck_append firstMixedTest 8 1 2
    firstMixedChunk5 (@rangeCheck_append firstMixedTest 9 1 1
    firstMixedChunk6 firstMixedChunk7)) (@rangeCheck_append firstMixedTest 11 1 3
    firstMixedChunk8 (@rangeCheck_append firstMixedTest 12 2 1
    firstMixedChunk9 firstMixedChunk10)))) (@rangeCheck_append firstMixedTest 15 13 7
    (@rangeCheck_append firstMixedTest 15 9 4
    (@rangeCheck_append firstMixedTest 15 2 7
    firstMixedChunk11 (@rangeCheck_append firstMixedTest 17 1 6
    firstMixedChunk12 firstMixedChunk13)) (@rangeCheck_append firstMixedTest 24 1 3
    firstMixedChunk14 (@rangeCheck_append firstMixedTest 25 2 1
    firstMixedChunk15 firstMixedChunk16))) (@rangeCheck_append firstMixedTest 28 3 4
    (@rangeCheck_append firstMixedTest 28 1 2
    firstMixedChunk17 (@rangeCheck_append firstMixedTest 29 1 1
    firstMixedChunk18 firstMixedChunk19)) (@rangeCheck_append firstMixedTest 31 1 3
    firstMixedChunk20 (@rangeCheck_append firstMixedTest 32 1 2
    firstMixedChunk21 firstMixedChunk22)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 8 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 16 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 24 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 32 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 40 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 48 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 56 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 64 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 72 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 80 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 88 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk12 : rangeCheck readyForThird 96 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk13 : rangeCheck readyForThird 104 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk14 : rangeCheck readyForThird 112 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk15 : rangeCheck readyForThird 120 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk16 : rangeCheck readyForThird 128 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk17 : rangeCheck readyForThird 136 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk18 : rangeCheck readyForThird 144 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk19 : rangeCheck readyForThird 152 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk20 : rangeCheck readyForThird 160 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk21 : rangeCheck readyForThird 168 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk22 : rangeCheck readyForThird 176 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk23 : rangeCheck readyForThird 184 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk24 : rangeCheck readyForThird 192 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk25 : rangeCheck readyForThird 200 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk26 : rangeCheck readyForThird 208 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk27 : rangeCheck readyForThird 216 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk28 : rangeCheck readyForThird 224 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk29 : rangeCheck readyForThird 232 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk30 : rangeCheck readyForThird 240 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk31 : rangeCheck readyForThird 248 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk32 : rangeCheck readyForThird 256 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk33 : rangeCheck readyForThird 264 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk34 : rangeCheck readyForThird 272 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk35 : rangeCheck readyForThird 280 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk36 : rangeCheck readyForThird 288 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk37 : rangeCheck readyForThird 296 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk38 : rangeCheck readyForThird 304 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk39 : rangeCheck readyForThird 312 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk40 : rangeCheck readyForThird 320 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk41 : rangeCheck readyForThird 328 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk42 : rangeCheck readyForThird 336 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk43 : rangeCheck readyForThird 344 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk44 : rangeCheck readyForThird 352 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk45 : rangeCheck readyForThird 360 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk46 : rangeCheck readyForThird 368 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk47 : rangeCheck readyForThird 376 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk48 : rangeCheck readyForThird 384 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk49 : rangeCheck readyForThird 392 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk50 : rangeCheck readyForThird 400 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk51 : rangeCheck readyForThird 408 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 secondCount = true := by
  exact (@rangeCheck_append readyForThird 0 208 205
    (@rangeCheck_append readyForThird 0 104 104
    (@rangeCheck_append readyForThird 0 48 56
    (@rangeCheck_append readyForThird 0 24 24
    (@rangeCheck_append readyForThird 0 8 16
    secondCoverageChunk0 (@rangeCheck_append readyForThird 8 8 8
    secondCoverageChunk1 secondCoverageChunk2)) (@rangeCheck_append readyForThird 24 8 16
    secondCoverageChunk3 (@rangeCheck_append readyForThird 32 8 8
    secondCoverageChunk4 secondCoverageChunk5))) (@rangeCheck_append readyForThird 48 24 32
    (@rangeCheck_append readyForThird 48 8 16
    secondCoverageChunk6 (@rangeCheck_append readyForThird 56 8 8
    secondCoverageChunk7 secondCoverageChunk8)) (@rangeCheck_append readyForThird 72 16 16
    (@rangeCheck_append readyForThird 72 8 8
    secondCoverageChunk9 secondCoverageChunk10) (@rangeCheck_append readyForThird 88 8 8
    secondCoverageChunk11 secondCoverageChunk12)))) (@rangeCheck_append readyForThird 104 48 56
    (@rangeCheck_append readyForThird 104 24 24
    (@rangeCheck_append readyForThird 104 8 16
    secondCoverageChunk13 (@rangeCheck_append readyForThird 112 8 8
    secondCoverageChunk14 secondCoverageChunk15)) (@rangeCheck_append readyForThird 128 8 16
    secondCoverageChunk16 (@rangeCheck_append readyForThird 136 8 8
    secondCoverageChunk17 secondCoverageChunk18))) (@rangeCheck_append readyForThird 152 24 32
    (@rangeCheck_append readyForThird 152 8 16
    secondCoverageChunk19 (@rangeCheck_append readyForThird 160 8 8
    secondCoverageChunk20 secondCoverageChunk21)) (@rangeCheck_append readyForThird 176 16 16
    (@rangeCheck_append readyForThird 176 8 8
    secondCoverageChunk22 secondCoverageChunk23) (@rangeCheck_append readyForThird 192 8 8
    secondCoverageChunk24 secondCoverageChunk25))))) (@rangeCheck_append readyForThird 208 104 101
    (@rangeCheck_append readyForThird 208 48 56
    (@rangeCheck_append readyForThird 208 24 24
    (@rangeCheck_append readyForThird 208 8 16
    secondCoverageChunk26 (@rangeCheck_append readyForThird 216 8 8
    secondCoverageChunk27 secondCoverageChunk28)) (@rangeCheck_append readyForThird 232 8 16
    secondCoverageChunk29 (@rangeCheck_append readyForThird 240 8 8
    secondCoverageChunk30 secondCoverageChunk31))) (@rangeCheck_append readyForThird 256 24 32
    (@rangeCheck_append readyForThird 256 8 16
    secondCoverageChunk32 (@rangeCheck_append readyForThird 264 8 8
    secondCoverageChunk33 secondCoverageChunk34)) (@rangeCheck_append readyForThird 280 16 16
    (@rangeCheck_append readyForThird 280 8 8
    secondCoverageChunk35 secondCoverageChunk36) (@rangeCheck_append readyForThird 296 8 8
    secondCoverageChunk37 secondCoverageChunk38)))) (@rangeCheck_append readyForThird 312 48 53
    (@rangeCheck_append readyForThird 312 24 24
    (@rangeCheck_append readyForThird 312 8 16
    secondCoverageChunk39 (@rangeCheck_append readyForThird 320 8 8
    secondCoverageChunk40 secondCoverageChunk41)) (@rangeCheck_append readyForThird 336 8 16
    secondCoverageChunk42 (@rangeCheck_append readyForThird 344 8 8
    secondCoverageChunk43 secondCoverageChunk44))) (@rangeCheck_append readyForThird 360 24 29
    (@rangeCheck_append readyForThird 360 8 16
    secondCoverageChunk45 (@rangeCheck_append readyForThird 368 8 8
    secondCoverageChunk46 secondCoverageChunk47)) (@rangeCheck_append readyForThird 384 16 13
    (@rangeCheck_append readyForThird 384 8 8
    secondCoverageChunk48 secondCoverageChunk49) (@rangeCheck_append readyForThird 400 8 5
    secondCoverageChunk50 secondCoverageChunk51))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 8 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 16 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 24 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 32 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 40 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 48 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 56 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk8 : rangeCheck secondMixedTest 64 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk9 : rangeCheck secondMixedTest 72 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk10 : rangeCheck secondMixedTest 80 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk11 : rangeCheck secondMixedTest 88 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk12 : rangeCheck secondMixedTest 96 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk13 : rangeCheck secondMixedTest 104 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk14 : rangeCheck secondMixedTest 112 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk15 : rangeCheck secondMixedTest 120 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk16 : rangeCheck secondMixedTest 128 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk17 : rangeCheck secondMixedTest 136 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk18 : rangeCheck secondMixedTest 144 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk19 : rangeCheck secondMixedTest 152 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk20 : rangeCheck secondMixedTest 160 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk21 : rangeCheck secondMixedTest 168 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk22 : rangeCheck secondMixedTest 176 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk23 : rangeCheck secondMixedTest 184 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk24 : rangeCheck secondMixedTest 192 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk25 : rangeCheck secondMixedTest 200 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk26 : rangeCheck secondMixedTest 208 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk27 : rangeCheck secondMixedTest 216 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk28 : rangeCheck secondMixedTest 224 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk29 : rangeCheck secondMixedTest 232 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk30 : rangeCheck secondMixedTest 240 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk31 : rangeCheck secondMixedTest 248 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk32 : rangeCheck secondMixedTest 256 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk33 : rangeCheck secondMixedTest 264 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk34 : rangeCheck secondMixedTest 272 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk35 : rangeCheck secondMixedTest 280 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk36 : rangeCheck secondMixedTest 288 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk37 : rangeCheck secondMixedTest 296 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk38 : rangeCheck secondMixedTest 304 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk39 : rangeCheck secondMixedTest 312 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk40 : rangeCheck secondMixedTest 320 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk41 : rangeCheck secondMixedTest 328 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk42 : rangeCheck secondMixedTest 336 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk43 : rangeCheck secondMixedTest 344 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk44 : rangeCheck secondMixedTest 352 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk45 : rangeCheck secondMixedTest 360 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk46 : rangeCheck secondMixedTest 368 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk47 : rangeCheck secondMixedTest 376 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk48 : rangeCheck secondMixedTest 384 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk49 : rangeCheck secondMixedTest 392 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk50 : rangeCheck secondMixedTest 400 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk51 : rangeCheck secondMixedTest 408 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 secondCount = true := by
  exact (@rangeCheck_append secondMixedTest 0 208 205
    (@rangeCheck_append secondMixedTest 0 104 104
    (@rangeCheck_append secondMixedTest 0 48 56
    (@rangeCheck_append secondMixedTest 0 24 24
    (@rangeCheck_append secondMixedTest 0 8 16
    secondMixedChunk0 (@rangeCheck_append secondMixedTest 8 8 8
    secondMixedChunk1 secondMixedChunk2)) (@rangeCheck_append secondMixedTest 24 8 16
    secondMixedChunk3 (@rangeCheck_append secondMixedTest 32 8 8
    secondMixedChunk4 secondMixedChunk5))) (@rangeCheck_append secondMixedTest 48 24 32
    (@rangeCheck_append secondMixedTest 48 8 16
    secondMixedChunk6 (@rangeCheck_append secondMixedTest 56 8 8
    secondMixedChunk7 secondMixedChunk8)) (@rangeCheck_append secondMixedTest 72 16 16
    (@rangeCheck_append secondMixedTest 72 8 8
    secondMixedChunk9 secondMixedChunk10) (@rangeCheck_append secondMixedTest 88 8 8
    secondMixedChunk11 secondMixedChunk12)))) (@rangeCheck_append secondMixedTest 104 48 56
    (@rangeCheck_append secondMixedTest 104 24 24
    (@rangeCheck_append secondMixedTest 104 8 16
    secondMixedChunk13 (@rangeCheck_append secondMixedTest 112 8 8
    secondMixedChunk14 secondMixedChunk15)) (@rangeCheck_append secondMixedTest 128 8 16
    secondMixedChunk16 (@rangeCheck_append secondMixedTest 136 8 8
    secondMixedChunk17 secondMixedChunk18))) (@rangeCheck_append secondMixedTest 152 24 32
    (@rangeCheck_append secondMixedTest 152 8 16
    secondMixedChunk19 (@rangeCheck_append secondMixedTest 160 8 8
    secondMixedChunk20 secondMixedChunk21)) (@rangeCheck_append secondMixedTest 176 16 16
    (@rangeCheck_append secondMixedTest 176 8 8
    secondMixedChunk22 secondMixedChunk23) (@rangeCheck_append secondMixedTest 192 8 8
    secondMixedChunk24 secondMixedChunk25))))) (@rangeCheck_append secondMixedTest 208 104 101
    (@rangeCheck_append secondMixedTest 208 48 56
    (@rangeCheck_append secondMixedTest 208 24 24
    (@rangeCheck_append secondMixedTest 208 8 16
    secondMixedChunk26 (@rangeCheck_append secondMixedTest 216 8 8
    secondMixedChunk27 secondMixedChunk28)) (@rangeCheck_append secondMixedTest 232 8 16
    secondMixedChunk29 (@rangeCheck_append secondMixedTest 240 8 8
    secondMixedChunk30 secondMixedChunk31))) (@rangeCheck_append secondMixedTest 256 24 32
    (@rangeCheck_append secondMixedTest 256 8 16
    secondMixedChunk32 (@rangeCheck_append secondMixedTest 264 8 8
    secondMixedChunk33 secondMixedChunk34)) (@rangeCheck_append secondMixedTest 280 16 16
    (@rangeCheck_append secondMixedTest 280 8 8
    secondMixedChunk35 secondMixedChunk36) (@rangeCheck_append secondMixedTest 296 8 8
    secondMixedChunk37 secondMixedChunk38)))) (@rangeCheck_append secondMixedTest 312 48 53
    (@rangeCheck_append secondMixedTest 312 24 24
    (@rangeCheck_append secondMixedTest 312 8 16
    secondMixedChunk39 (@rangeCheck_append secondMixedTest 320 8 8
    secondMixedChunk40 secondMixedChunk41)) (@rangeCheck_append secondMixedTest 336 8 16
    secondMixedChunk42 (@rangeCheck_append secondMixedTest 344 8 8
    secondMixedChunk43 secondMixedChunk44))) (@rangeCheck_append secondMixedTest 360 24 29
    (@rangeCheck_append secondMixedTest 360 8 16
    secondMixedChunk45 (@rangeCheck_append secondMixedTest 368 8 8
    secondMixedChunk46 secondMixedChunk47)) (@rangeCheck_append secondMixedTest 384 16 13
    (@rangeCheck_append secondMixedTest 384 8 8
    secondMixedChunk48 secondMixedChunk49) (@rangeCheck_append secondMixedTest 400 8 5
    secondMixedChunk50 secondMixedChunk51))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 30 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 60 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 90 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 120 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 150 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 180 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 210 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 240 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 270 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 300 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 330 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 360 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 390 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 420 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 450 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 480 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk17 : rangeCheck thirdTest 510 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk18 : rangeCheck thirdTest 540 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk19 : rangeCheck thirdTest 570 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk20 : rangeCheck thirdTest 600 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk21 : rangeCheck thirdTest 630 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk22 : rangeCheck thirdTest 660 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk23 : rangeCheck thirdTest 690 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk24 : rangeCheck thirdTest 720 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk25 : rangeCheck thirdTest 750 20 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk26 : rangeCheck thirdTest 770 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk27 : rangeCheck thirdTest 800 25 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk28 : rangeCheck thirdTest 825 19 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk29 : rangeCheck thirdTest 844 26 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk30 : rangeCheck thirdTest 870 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk31 : rangeCheck thirdTest 900 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk32 : rangeCheck thirdTest 930 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk33 : rangeCheck thirdTest 960 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk34 : rangeCheck thirdTest 990 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk35 : rangeCheck thirdTest 1020 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk36 : rangeCheck thirdTest 1050 14 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk37 : rangeCheck thirdTest 1064 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk38 : rangeCheck thirdTest 1077 22 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk39 : rangeCheck thirdTest 1099 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk40 : rangeCheck thirdTest 1129 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk41 : rangeCheck thirdTest 1159 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk42 : rangeCheck thirdTest 1189 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk43 : rangeCheck thirdTest 1219 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk44 : rangeCheck thirdTest 1249 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk45 : rangeCheck thirdTest 1279 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk46 : rangeCheck thirdTest 1309 21 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk47 : rangeCheck thirdTest 1330 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk48 : rangeCheck thirdTest 1360 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk49 : rangeCheck thirdTest 1390 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk50 : rangeCheck thirdTest 1420 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk51 : rangeCheck thirdTest 1450 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk52 : rangeCheck thirdTest 1480 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk53 : rangeCheck thirdTest 1510 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk54 : rangeCheck thirdTest 1540 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk55 : rangeCheck thirdTest 1570 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk56 : rangeCheck thirdTest 1600 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk57 : rangeCheck thirdTest 1630 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk58 : rangeCheck thirdTest 1660 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk59 : rangeCheck thirdTest 1690 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk60 : rangeCheck thirdTest 1720 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk61 : rangeCheck thirdTest 1750 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk62 : rangeCheck thirdTest 1780 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk63 : rangeCheck thirdTest 1810 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk64 : rangeCheck thirdTest 1840 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk65 : rangeCheck thirdTest 1870 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk66 : rangeCheck thirdTest 1900 30 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk67 : rangeCheck thirdTest 1930 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 thirdCount = true := by
  exact (@rangeCheck_append thirdTest 0 990 953
    (@rangeCheck_append thirdTest 0 510 480
    (@rangeCheck_append thirdTest 0 240 270
    (@rangeCheck_append thirdTest 0 120 120
    (@rangeCheck_append thirdTest 0 60 60
    (@rangeCheck_append thirdTest 0 30 30
    thirdTailChunk0 thirdTailChunk1) (@rangeCheck_append thirdTest 60 30 30
    thirdTailChunk2 thirdTailChunk3)) (@rangeCheck_append thirdTest 120 60 60
    (@rangeCheck_append thirdTest 120 30 30
    thirdTailChunk4 thirdTailChunk5) (@rangeCheck_append thirdTest 180 30 30
    thirdTailChunk6 thirdTailChunk7))) (@rangeCheck_append thirdTest 240 120 150
    (@rangeCheck_append thirdTest 240 60 60
    (@rangeCheck_append thirdTest 240 30 30
    thirdTailChunk8 thirdTailChunk9) (@rangeCheck_append thirdTest 300 30 30
    thirdTailChunk10 thirdTailChunk11)) (@rangeCheck_append thirdTest 360 60 90
    (@rangeCheck_append thirdTest 360 30 30
    thirdTailChunk12 thirdTailChunk13) (@rangeCheck_append thirdTest 420 30 60
    thirdTailChunk14 (@rangeCheck_append thirdTest 450 30 30
    thirdTailChunk15 thirdTailChunk16))))) (@rangeCheck_append thirdTest 510 240 240
    (@rangeCheck_append thirdTest 510 120 120
    (@rangeCheck_append thirdTest 510 60 60
    (@rangeCheck_append thirdTest 510 30 30
    thirdTailChunk17 thirdTailChunk18) (@rangeCheck_append thirdTest 570 30 30
    thirdTailChunk19 thirdTailChunk20)) (@rangeCheck_append thirdTest 630 60 60
    (@rangeCheck_append thirdTest 630 30 30
    thirdTailChunk21 thirdTailChunk22) (@rangeCheck_append thirdTest 690 30 30
    thirdTailChunk23 thirdTailChunk24))) (@rangeCheck_append thirdTest 750 94 146
    (@rangeCheck_append thirdTest 750 50 44
    (@rangeCheck_append thirdTest 750 20 30
    thirdTailChunk25 thirdTailChunk26) (@rangeCheck_append thirdTest 800 25 19
    thirdTailChunk27 thirdTailChunk28)) (@rangeCheck_append thirdTest 844 56 90
    (@rangeCheck_append thirdTest 844 26 30
    thirdTailChunk29 thirdTailChunk30) (@rangeCheck_append thirdTest 900 30 60
    thirdTailChunk31 (@rangeCheck_append thirdTest 930 30 30
    thirdTailChunk32 thirdTailChunk33)))))) (@rangeCheck_append thirdTest 990 460 493
    (@rangeCheck_append thirdTest 990 199 261
    (@rangeCheck_append thirdTest 990 87 112
    (@rangeCheck_append thirdTest 990 60 27
    (@rangeCheck_append thirdTest 990 30 30
    thirdTailChunk34 thirdTailChunk35) (@rangeCheck_append thirdTest 1050 14 13
    thirdTailChunk36 thirdTailChunk37)) (@rangeCheck_append thirdTest 1077 52 60
    (@rangeCheck_append thirdTest 1077 22 30
    thirdTailChunk38 thirdTailChunk39) (@rangeCheck_append thirdTest 1129 30 30
    thirdTailChunk40 thirdTailChunk41))) (@rangeCheck_append thirdTest 1189 120 141
    (@rangeCheck_append thirdTest 1189 60 60
    (@rangeCheck_append thirdTest 1189 30 30
    thirdTailChunk42 thirdTailChunk43) (@rangeCheck_append thirdTest 1249 30 30
    thirdTailChunk44 thirdTailChunk45)) (@rangeCheck_append thirdTest 1309 51 90
    (@rangeCheck_append thirdTest 1309 21 30
    thirdTailChunk46 thirdTailChunk47) (@rangeCheck_append thirdTest 1360 30 60
    thirdTailChunk48 (@rangeCheck_append thirdTest 1390 30 30
    thirdTailChunk49 thirdTailChunk50))))) (@rangeCheck_append thirdTest 1450 240 253
    (@rangeCheck_append thirdTest 1450 120 120
    (@rangeCheck_append thirdTest 1450 60 60
    (@rangeCheck_append thirdTest 1450 30 30
    thirdTailChunk51 thirdTailChunk52) (@rangeCheck_append thirdTest 1510 30 30
    thirdTailChunk53 thirdTailChunk54)) (@rangeCheck_append thirdTest 1570 60 60
    (@rangeCheck_append thirdTest 1570 30 30
    thirdTailChunk55 thirdTailChunk56) (@rangeCheck_append thirdTest 1630 30 30
    thirdTailChunk57 thirdTailChunk58))) (@rangeCheck_append thirdTest 1690 120 133
    (@rangeCheck_append thirdTest 1690 60 60
    (@rangeCheck_append thirdTest 1690 30 30
    thirdTailChunk59 thirdTailChunk60) (@rangeCheck_append thirdTest 1750 30 30
    thirdTailChunk61 thirdTailChunk62)) (@rangeCheck_append thirdTest 1810 60 73
    (@rangeCheck_append thirdTest 1810 30 30
    thirdTailChunk63 thirdTailChunk64) (@rangeCheck_append thirdTest 1870 30 43
    thirdTailChunk65 (@rangeCheck_append thirdTest 1900 30 13
    thirdTailChunk66 thirdTailChunk67)))))))

def initialIndices (kind : Bool) : List ℕ := if kind then [1, 2, 4, 6, 7, 8, 9, 10, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34] else [0, 3, 5, 11, 13, 23]

noncomputable def initialStates (kind : Bool) : List SearchState := (initialIndices kind).map firstAt

lemma allInitialIndices (kind : Bool) : (initialIndices kind).all (fun i => decide (i < firstCount)) = true := by
  cases kind <;> decide +kernel

lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) : chkPairPicked [] rootBounds 0 14 1 FF 0 kind = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : chk [] rootBounds 0 14 1 FF 0 = false :=
  chkPair_picked [] rootBounds 0 14 1 FF 0 binaryCertificate


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked0 : chkPicked [] rootBounds 0 14 1 0 1 0 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked1 : chkPicked [] rootBounds 0 14 1 0 1 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked2 : chkPicked [] rootBounds 0 14 1 0 1 2 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked3 : chkPicked [] rootBounds 0 14 1 0 1 3 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked4 : chkPicked [] rootBounds 0 14 1 0 1 4 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked5 : chkPicked [] rootBounds 0 14 1 0 1 5 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked6 : chkPicked [] rootBounds 0 14 1 0 1 6 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked7 : chkPicked [] rootBounds 0 14 1 0 1 7 = false := by decide +kernel

lemma unaryChecked : chk [] rootBounds 0 14 1 0 1 = false := by
  apply chk_picked
  intro b
  fin_cases b
  · exact unaryChecked0
  · exact unaryChecked1
  · exact unaryChecked2
  · exact unaryChecked3
  · exact unaryChecked4
  · exact unaryChecked5
  · exact unaryChecked6
  · exact unaryChecked7


def rootCases : List (ℕ × ℕ) := [(FF, 0), (0, 1)]

lemma rootCases_full : mFull rootCases = true := by decide +kernel

lemma certify_1 : ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] rootBounds 0 14 1 p.1 p.2 = false := by
  refine ⟨rootCases, rootCases_full, ?_⟩
  intro p hp
  simp only [rootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_0 : chk [] rootBounds 0 13 0 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_1 : chk [] rootBounds 0 13 1 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_2 : chk [] rootBounds 0 13 2 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_3 : chk [] rootBounds 0 13 3 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_4 : chk [] rootBounds 0 13 4 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_5 : chk [] rootBounds 0 13 5 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_6 : chk [] rootBounds 0 13 6 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_7 : chk [] rootBounds 0 13 7 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_8 : chk [] rootBounds 0 13 8 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_9 : chk [] rootBounds 0 13 9 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_10 : chk [] rootBounds 0 13 10 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_11 : chk [] rootBounds 0 13 11 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_12 : chk [] rootBounds 0 13 12 FF 1 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma small_13 : chk [] rootBounds 0 13 13 FF 1 = false := by decide +kernel
lemma lower14 : Imp [] 0 14 := imp_ts (Or.inl rfl) root_p (by norm_num) rootBounds_sound (fun t ht => by
  interval_cases t
  · exact one small_0
  · exact one small_1
  · exact one small_2
  · exact one small_3
  · exact one small_4
  · exact one small_5
  · exact one small_6
  · exact one small_7
  · exact one small_8
  · exact one small_9
  · exact one small_10
  · exact one small_11
  · exact one small_12
  · exact one small_13
)

lemma needs15 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 14 1 S) : False := by
  have hmin : ∀ q < 14, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => lower14 q hq
  exact imp_of_live (L := 15) (Or.inl rfl) root_p (by norm_num) rootBounds_sound
    (by norm_num) hS hl hmin (Or.inr certify_1)

lemma onFinal : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gates o hfit hone hev
  by_cases hnot : ∃ g ∈ gates, g.op = GateOp.not
  · have hge : 15 ≤ gates.length := by
      by_contra! hlt
      have hf : ∀ y : Fin 8 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y :=
        fun y => (hev y).trans (f_graph y).symm
      by_cases hsmall : gates.length < 14
      · exact lower14 gates.length hsmall (bridge ⟨gates, o⟩ (fanInTwo_of hfit) hf)
      · have hsize : gates.length = 14 := by omega
        rcases bridge_not gates o (fanInTwo_of hfit) hone hnot hf with hsol | ⟨S, hS, hl⟩
        · exact lower14 (gates.length - 1) (by omega) hsol
        · rw [hsize] at hl
          exact needs15 hS hl
    exact ⟨witness.gates, witness.output, witness_basis, by rw [witness_size]; omega, witness_eval⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    rcases hfit g hg with ⟨h | h | h, hl⟩
    · exact ⟨Or.inl h, hl⟩
    · exact ⟨Or.inr h, hl⟩
    · exact (hnot ⟨g, hg, h⟩).elim

end inst_data
end PEqualNP.Outside.L_meta_32159_aux

theorem PEqualNP.Outside.L_meta_32159 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_32159_aux.onFinal
