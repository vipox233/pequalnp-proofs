import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_35928_aux

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

def bigNat_0 : Nat := 0xfffffdfbfffff7ffffefbffffefbeefffffbef7bffffef7defffffbdf6fbdeffff6bff5ad557feabff55ffaffdffad6b557feaaffd5bff6ffdb555affd6d7feffdad5b5ffbff6dbff0000000000000000
def bigNat_1 : Nat := 0x9400a52aa8015400aa005002005294aa80155002a40090024aaa50029280100252a4a00400924000000000000000000
def bigNat_2 : Nat := 0x100000204000008000010400001041100000410840000108210000042090421000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0xfffffc000000000000000000000000000001fffff03e1f03c000010840000010800848844422046000202208044123108c420000004120a210430008288410c4910c000000000000000002102c080840b41d5160008096082202015821080804e10421245b81f0f81e040b080000040000000044002001ff8003010000200118006000011000010d000ffc21434003ff6dbff6fef15f7d3259bd9
def bigNat_4 : Nat := 0x7ffffc0f81fffff7801f7800000000c000000191014a00c40700c00000001910052801840700008405242038061089080e018c3028000000000000000004215010108540201a8081052810440412a04210926b407c01456d3c00fbc00854000000100000880050002ffc000008000008800140006ffc04442001617fe0018c585ff800618002ae05b98957bc359
def bigNat_5 : Nat := 0x7ffffc07c1fffff01e07ffffde001fffff7bec00000000003c808220d94074a83e01e03c4040880d9401d2907c01e30a0b02d2d81702e340b606c0d8d80e8000000000000000008420020210800406001124b8003e04928c00f00a2a24f000186493df600001080000040c11000a00055ff800000206044000a00015bff0001850580016c000001a05b0000006c000696babab9b9f9aa6
def bigNat_6 : Nat := 0x1fffff7c007ffffdefbc000000000000000000018000280515038001800c0180000a0051500e0003000c1200940e0000600c35a00028050920700000000000000000108484404212108184220412422088514ccbe000c3326f7de20881801008022121000002014000abff0000000000010050000aaffc00000001b005affc00000001ad000000006dbfffb81b43c85103f8c
def bigNat_7 : Nat := 0x7ffffdf001fffff7def00000000000000000000000000000309002a0e0006000300180304800a80e000180006001836aa002800014028252240700e0000c00000000000000000210818808420610600c418638cf8006188f3ef790403800804100e0420104442060000580157fe000000000000002c00557fe0000000000001b550000000000001ad5b5ffbff00000ccfdb29b8db69d11
def bigNat_8 : Nat := 0x1fffff807ffffe00000007ffffdf7dc000000000000000000000000000000000000c520b5a80a80054002a01502a05ad400c8001900064019024aa21b0090d81b000000340680006800000000000000000be00e00207c3800807001043f0fbee000f008000003c02104000f008402088003860005ad40000000000000000002d6b000000000000000001b555affd6d7feffc00000000000000098f5d06f32eb0f0e
def bigNat_9 : Nat := 0x7ffffefffffdf000000000000000000000000000000000000000000000051c000000300018000c00600c012960270004e0023808e0000000c0000600c000000180300003000000000000000000c00f010307fc060ff80fa07c00410081f001042207c00420881f001082410083c06bff00000000000000000000002d6b557feaaffd5bff6ffc00000000000000000000000000000009b3e6d86eb396fa1
def bigNat_10 : Nat := 0x1fffffbf00000000000000000000000000000000000000000000000000000000000860025280c0006000300180300000000800010000400100000001000008010000000200400004000000000000000000fff001fbf80007f000083f80008200fe00020843f80008410fe00021048210fc006bff5ad557feabff55ffaffdff800000000000000000000000000000000000000000000000000009218fe0e639372c7
def bigNat_11 : Nat := 0xfffffdfbfffff7ffffefbffffefbeefffffbef7bffffef7defffffbdf6fbdeffff6bff5ad557feabff55ffaffdffad6b557feaaffd5bff6ffdb555affd6d7feffdad5b5ffbff6dbffffffffffffffffff
def NN0 : Nat := 645
def AA0 : Nat := bigNat_0
def HX0 : Nat := bigNat_1
def HY0 : Nat := bigNat_2
def segsX0 : List (ℕ × ℕ) := [(63, 74), (74, 77), (77, 80), (80, 83), (83, 94), (94, 105), (105, 107), (107, 110), (110, 113), (113, 115), (115, 117), (117, 120), (120, 122), (122, 125), (125, 136), (136, 147), (147, 149), (149, 152), (152, 155), (155, 157), (157, 168), (168, 170), (170, 173), (173, 175), (175, 177), (177, 179), (179, 181), (181, 183), (183, 186), (186, 189), (189, 200), (200, 203), (203, 214), (214, 217), (217, 219), (219, 221), (221, 232), (232, 234), (234, 236), (236, 238), (238, 240), (240, 251), (251, 253), (253, 255), (255, 257), (257, 259), (259, 262), (262, 264), (264, 267), (267, 269), (269, 272), (272, 274), (274, 285), (285, 296), (296, 298), (298, 309), (309, 311), (311, 313), (313, 315), (315, 326), (326, 328), (328, 330), (330, 332), (332, 343), (343, 345), (345, 347), (347, 349), (349, 351), (351, 353), (353, 356), (356, 358), (358, 361), (361, 363), (363, 374), (374, 376), (376, 379)]
def segsY0 : List (ℕ × ℕ) := [(379, 396), (396, 401), (401, 406), (406, 412), (412, 415), (415, 421), (421, 426), (426, 448), (448, 453), (453, 459), (459, 464), (464, 486), (486, 491), (491, 496), (496, 502), (502, 524), (524, 528), (528, 534), (534, 540), (540, 562), (562, 568), (568, 591), (591, 614), (614, 621), (621, 644)]
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
      cases scan (fun e => bif PEqualNP.Outside.L_meta_35928_aux.hb H (x.s + e.s) then q b x e else false) xs <;> rfl
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

noncomputable def demanded (Z : ℕ) : List W :=
  let bank := avl [] (mz Z) (rawL [])
  bank.filter (fun w => !Nat.beq (Nat.land (sp true (lz Z) w.s) (wst true (lz Z) bank)) 0)

lemma demanded_bound {Z L : ℕ} (enough : L < (demanded Z).length) : Imp [] Z L := by
  classical
  intro q hq solution
  let existsSol : ∃ n, Sol Z0 (mz Z) (tz Z) n (C (mz Z) (WZ [] Z)) := ⟨q, solution⟩
  obtain ⟨k, hk, t, S, hS, live⟩ := (Nat.find_spec existsSol).live
  have leSize := le_trans hk (Nat.find_min' existsSol solution)
  have ambient : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have minimal : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨live, fun n hn smaller => Nat.find_min existsSol (lt_of_lt_of_le hn hk) (smaller.mono le_rfl ambient)⟩
  let bank := avl [] (mz Z) (rawL [])
  let all := (bank.map W.s).toFinset
  obtain ⟨sorted, _, hasWire⟩ := avl_spec [] (mz Z) (rawL [])
  have nodup : (bank.map W.s).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact sorted.imp fun h => Nat.ne_of_gt h
  have bankRep : Rep bank all := ⟨nodup, rfl⟩
  have contained : (demanded Z |>.map W.s).toFinset ⊆ S := by
    intro x hx
    obtain ⟨w, hwLat, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    have hwMem : w ∈ bank ∧ (!Nat.beq (Nat.land (sp true (lz Z) w.s) (wst true (lz Z) bank)) 0) = true :=
      List.mem_filter.mp hwLat
    have nonzero : Nat.land (sp true (lz Z) w.s) (wst true (lz Z) bank) ≠ 0 := by
      intro eq; rw [eq] at hwMem; simp at hwMem
    obtain ⟨i,hi⟩ := Nat.exists_testBit_of_ne_zero nonzero
    obtain ⟨hmask, hu⟩ := uq_of bankRep hwMem.1 hi
    obtain ⟨⟨hm1,hm2,ht1,ht2⟩, _⟩ := lz_lg Z i hmask
    obtain ⟨u, hU, sign⟩ := live.cov hm1 hm2 ht1 ht2
    have sign := sepb_weak (pos' t) sign
    have notZero : u ≠ 0 := by rintro rfl; simp [sepb] at sign
    have notFull : u ≠ mz Z := by rintro rfl; simp [sepb, hm1, hm2] at sign
    have hIn : u ∈ all := by
      rcases hS hU with hu | hc
      · obtain ⟨r,hr,rfl⟩ := hu
        obtain ⟨w',hw',same⟩ := hasWire r hr notZero notFull
        exact bankRep.mem.mpr ⟨w',hw',same⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
        exact False.elim (hc.elim notZero notFull)
    have equal : u = w.s := by
      by_contra he
      rw [hu.2 u hIn he] at sign
      simp at sign
    exact equal ▸ hU
  have allNodup : ((demanded Z).map W.s).Nodup :=
    nodup.sublist (List.filter_sublist.map W.s)
  have card := Finset.card_le_card contained
  rw [List.toFinset_card_of_nodup allNodup, List.length_map] at card
  have sz := minimal.size.1
  omega

noncomputable def demandedRow (T : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  (Nat.ble e.2 6 && Nat.ble (e.2 + 1) (demanded e.1).length) || okE [] (pr T e.1) e

lemma demandedAll {T U : List (ℕ × ℕ)} (h : U.all (demandedRow T) = true)
    (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, Imp [] e.1 e.2 := by
  intro e he
  have checked := List.all_eq_true.mp h e he
  simp only [demandedRow, Bool.or_eq_true, Bool.and_eq_true] at checked
  rcases checked with ⟨_, short⟩ | ordinary
  · exact demanded_bound (Nat.le_of_ble_eq_true short)
  · exact imp_okE (Or.inl rfl) ordinary (fun r hr => hT r (List.mem_of_mem_filter hr))

inductive Steps (m T : ℕ) : ℕ → ℕ → Set ℕ → Prop
  | done {S} : T ∈ S → Steps m T 0 0 S
  | un {q u S a} : a ∈ S → Steps m T q u (insert (a ^^^ m) S) → Steps m T (q+1) (u+1) S
  | bi {q u S d a b} : a ∈ S → b ∈ S → Steps m T q u (insert (op d a b) S) → Steps m T (q+1) u S

lemma Steps.widen {m T q u S} (h : Steps m T q u S) :
    ∀ {S'}, S ⊆ S' → Steps m T q u S' := by
  induction h with
  | done h => intro _ hs; exact .done (hs h)
  | un ha _ ih => intro _ hs; exact .un (hs ha) (ih (Set.insert_subset_insert hs))
  | bi ha hb _ ih => intro _ hs; exact .bi (hs ha) (hs hb) (ih (Set.insert_subset_insert hs))

lemma Steps.liveCount {m T q u S} (h : Steps m T q u S) :
    ∃ k t, ∃ S0 : Finset ℕ, k ≤ q ∧ t ≤ u ∧ u + k ≤ q + t ∧
      (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T k t S0 := by
  induction h with
  | @done S h => exact ⟨0, 0, {T}, le_rfl, le_rfl, le_rfl, by simpa using h, .stop⟩
  | @un q u S a ha _ ih =>
    obtain ⟨k,t,S1,hk,ht,hc,hs,hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k+1, t+1, insert a (S1.erase (a ^^^ m)), by omega, by omega, by omega, ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1,h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩
  | @bi q u S d a b ha hb _ ih =>
    obtain ⟨k,t,S1,hk,ht,hc,hs,hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).elim (fun e => e ▸ ha) id,hl⟩
      refine ⟨k+1,t,insert a (insert b (S1.erase (op d a b))),by omega,by omega,by omega,?_,.bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | rfl | ⟨h1,h2⟩
      · exact ha
      · exact hb
      · exact (hs h1).resolve_left h2
    · exact ⟨k,t,S1,by omega,by omega,by omega,fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)),hl⟩

section countProjection
variable {m T n : ℕ} (hn : n &&& m = n)
include hn
lemma Un.stepIm {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S')
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) (q+1) (u+1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.widen (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.stepIm {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S')
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) (q+1) u (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.widen (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.stepKill {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a)
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) q u (C n (Im n S)) :=
  hs.widen (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.stepKill {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Steps n (T &&& n) q u (C n (Im n S'))) : Steps n (T &&& n) q u (C n (Im n S)) :=
  hs.widen (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)

lemma Min.projectCount (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q u, u ≤ t ∧ q + (S.filter (Cst n)).card + t ≤ k + u ∧ Steps n (T &&& n) q u (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop =>
    refine ⟨0, 0, le_rfl, ?_, .done (Im_mem (by simp))⟩
    rw [Finset.filter_eq_empty_iff.2]; · simp
    intro x hx; simp at hx; subst hx
    rintro (h | h); exacts [hT0 h, hT1 h]
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    obtain ⟨q,u,hu',hq,hs⟩ := ih (hu.min hl hm).2
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    by_cases hc : Cst n a
    · refine ⟨q,u,by omega,?_,hu.stepKill hn hc hs⟩
      rw [Finset.filter_insert, ite_eq_left ((Cst_neg hn).2 hc), Finset.card_insert_of_notMem (by simp [hf])] at hq
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · refine ⟨q+1,u+1,by omega,?_,hu.stepIm hn hs⟩
      rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi R d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q,u,hu',hq,hs⟩ := ih (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q,u,hu',?_,hu.stepKill (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q,u,hu',?_,hu.stepKill (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q+1,u,hu',?_,hu.stepIm hs⟩
        rw [ite_eq_right hcb]; omega
end countProjection
lemma minimumInputLive {Z q : ℕ}
    (h0 : tz Z ≠ 0) (h1 : tz Z ≠ mz Z)
    (hs : Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ [] Z))) :
    ∃ k ≤ q, ∃ t, ∃ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] Z ∧
      Live Z0 (mz Z) (tz Z) k t S ∧
      ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) := by
  classical
  have hex : ∃ j, Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) := ⟨q,hs⟩
  obtain ⟨k,hk,t,S,hS,hl⟩ := (Nat.find_spec hex).live
  have heq := le_antisymm hk (Nat.find_min' hex (hl.sol.mono le_rfl hS))
  have lower : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)) :=
    fun j hj => Nat.find_min hex (by omega)
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ [] Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min Z0 (mz Z) (tz Z) k t S :=
    ⟨hl,fun j hj h => lower j hj (h.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w,_,rfl⟩ | h
    · rw [Nat.and_assoc,Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  obtain ⟨hz,ho⟩ := hm.proper hT h0 h1 hbd
  refine ⟨k, hk.trans (Nat.find_min' hex hs),t,S,?_,hl,lower⟩
  intro x hx
  rcases hS hx with h | h
  · exact h
  · simp at h; rcases h with rfl | rfl
    · exact absurd hx hz
    · exact absurd hx ho
namespace BinarySearch
noncomputable section core
def nots (f : Nat → Nat → List W → Bool) (m g e n z q : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st z (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
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
    (fun _ ih k t z v => cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mv ih l m g k t z v y)) true (Nat.ble v.length 1))) fuel
def look1 (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => cv (pos t) l v (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1))) fuel
end core
def Cl (P : List ℕ) (T k t : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ j < P.length, ∀ q u, u ≤ t → q + b j + t < k + u →
    ¬ Steps (P.getD j 0) (T &&& P.getD j 0) q u (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k t z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k t b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k t b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q,u,hu,hq,hs⟩ := hm.projectCount p1 p2 p3
  have hqb : ¬ q + b j + t < k + u := fun h => hc j hj q u hu h hs
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
lemma guard_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hr : StOk P T l k t z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l k t z r S) (hm : Min R m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
  simp only [child, bR, st_eq, guard_ok X hr hm hk, cond_true, hmk] at h
  exact h
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma bi_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi R d' a.s c.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have hcl' : Cl P T k t b' S' := by
    intro j hj q u hu hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q u hu ?_ (hb.stepKill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q+1) u hu ?_ (hb.stepIm hsol)
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
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l k t z r S) (hm : Min R m T k' t S) (hk : k' ≤ k)
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
lemma hit_ht {k t z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k t z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S)
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
lemma tst_sound {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S) (hk : k' ≤ k) :
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
lemma cv_ok {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool} (hs : StOk P T l k t z v S) (hl : Live R m T k' t S)
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
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
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
      r.length = S'.card ∧ StOk P T l k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l (k + 1) (t + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live R m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l k t (z - (bif ka then a.c else 0)) r S' := by
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
  let b' : ℕ → ℕ := b
  have hcl' : Cl P T k t b' S' := by
    intro j hj q u hu hq hsol
    by_cases hkill : a.c.testBit (5*j) = true
    · exact hcl j hj q u (by omega) (by dsimp [b'] at hq; omega)
        (hb.stepKill (X.hP j hj).1 (wa.cst hj hkill) hsol)
    · exact hcl j hj (q+1) (u+1) (by omega) (by dsimp [b'] at hq; omega)
        (hb.stepIm (X.hP j hj).1 hsol)
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    rw [pk_sub]
    · refine pk_congr fun j hj => ?_
      have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
      have q5 := hcnt j; have q6 := fl_le a j
      simp only [b'] at q2 ⊢
      cases ka <;> simp at q5 ⊢ <;> omega
    · intro j hj; have := hle j hj; have := le1 j; omega
end sound
lemma nots_false {f : ℕ → ℕ → List W → Bool} {m g e n z q : ℕ} {v r : List W} (h : nots f m g e n z q v r = false)
    {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) : ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
      (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z q v r) true (Bool.rec (motive := fun _ => Bool)
      (st (Nat.xor w.s m) (fun s => st z (fun z => ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
        Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false
          (child (f s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e)) true
          (Bool.rec (motive := fun _ => Bool) false (child (f s) g (rm w.s w.s v) z) (Nat.ble n e)))))) false (Nat.beq (Nat.succ w.s) q)) : Bool) = false at h
    rw [bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · rw [Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
        (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f (a.s ^^^ m)) g (rm a.s a.s v) z else false) then true else
          (bif Nat.ble (n + 1) e then child (f (a.s ^^^ m)) g (fun h => h v) (z - a.c) else false))) then true
          else nots f m g e n z q v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z q v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {f : ℕ → ℕ → List W → Bool} {e n z q t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l (k + 1) (t + 1) z v S) (hm : Min R m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live R m T k' t S') (ha : a ∈ v) (hq : a.s + 1 ≠ q) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z q v rr = false) : ∃ z' r, f (a.s ^^^ m) z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
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
    have h : child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (fun h => h r0) (z - a.c) <;> simp
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
    have h : child (f (a.s ^^^ m)) g (rm a.s a.s r0) z = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f (a.s ^^^ m)) g (rm a.s a.s r0) z <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_35928_aux.XW → L_meta_35928_aux.XW → Bool) → List L_meta_35928_aux.XW → Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn hSe hb.symm hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound (hR : RR R) {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l k t z v S → Cod R v → ∀ k' ≤ k, ¬ Min R m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
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
        have : a.s = c.s := congrArg L_meta_35928_aux.XW.s e
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
theorem look_sound (hR : RR R) : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l k t z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min R m T k' t S := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hm
    change cv (pos t) l v _ = false at h
    rw [pos_eq] at h
    replace h := cv_ok X hs hm.1 h
    change (Bool.rec (motive := fun _ => Bool) (tst (pos' t) l (k + 1 - t) v (fun y => mv (look l m g fuel) l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at h
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
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_35928_aux.XW → L_meta_35928_aux.XW → Bool) → List L_meta_35928_aux.XW → Bool,
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
theorem look1_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K : ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t z v S h; simp [look1] at h
  | succ fuel ih =>
    intro k t z v S h hs hcod k' hk hl hmW
    change cv (pos t) l v _ = false at h
    rw [pos_eq] at h
    replace h := cv_ok X hs hl h
    change (Bool.rec (motive := fun _ => Bool) (tst (pos' t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (node (look1 l m g K fuel (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_35928_aux.XW.s e))
end sound
noncomputable section
end
noncomputable section
def topC (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (look l m g K) l m g k t z v y) (Nat.beq ph 1)) true
      (node (look1 l m g K K (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startv (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topC l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma topC_sound (hR : RR R) (hR2 : ∀ d a b, (R a = 0 ∨ R b = 0) → Al R d a b) {K k t z : ℕ} {v : List W} {S : Finset ℕ} {M : List (ℕ × ℕ)}
    (hM : mFull M = true) (h : ∀ p ∈ M, topC l m g K p.1 p.2 k t z v = false) (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
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
    have : Std.Symm (fun a b : L_meta_35928_aux.XW => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_35928_aux.XW.s e)) hpb
end sound
noncomputable def chk (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startv l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - t - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
lemma rejectMinimum {Q : List (ℕ × ℕ)} {Z L k t : ℕ} {S : Finset ℕ}
    (hp : pOk Z Q = true) (hL : L ≤ 15) (hk : k < L)
    (hI : ∀ e ∈ Q, ∀ q u, u ≤ t → q < e.2 + u → ¬ Steps (mz e.1) (tz e.1) q u (C (mz e.1) (WZ [] e.1))) (hSW : (S : Set ℕ) ⊆ WZ [] Z)
    (hl : Live Z0 (mz Z) (tz Z) k t S)
    (lower : ∀ j < k, ¬ Sol Z0 (mz Z) (tz Z) j (C (mz Z) (WZ [] Z)))
    (M : List (ℕ × ℕ)) (hMf : mFull M = true)
    (hchk : ∀ p ∈ M, chk [] Q Z (L-1) t p.1 p.2 = false) : False := by
  classical
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0,hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz,nl,Nat.and_assoc,Nat.and_self]
  have hE6 : ∀ e ∈ ([] : List (ℕ × ℕ)), e ∈ six := by simp
  have hm : Min Z0 (mz Z) (tz Z) k t S := ⟨hl,fun j hj hs => lower j hj (hs.mono le_rfl (C_mono hSW))⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := hSW hx
    rw [Nat.and_assoc,Nat.and_self]
  obtain ⟨h0,h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hproj : ∀ e ∈ Q, mz e.1 &&& mz Z = mz e.1 ∧ tz e.1 ≠ 0 ∧ tz e.1 ≠ mz e.1 := by
    intro e he
    obtain ⟨⟨a, b⟩, c⟩ := hp2 e he
    exact ⟨Nat.eq_of_beq_eq_true a, nb b, nb c⟩
  have hno : ∀ e ∈ Q, ∀ q u, u ≤ t → q < e.2 + u →
      ¬ Steps (mz e.1) (tz Z &&& mz e.1) q u (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q u hu hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q u hu hq (hs.widen (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  have hpw : pwr [] Z = 0 ∨ pwr [] Z ∈ S := Or.inl rfl
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) (rawL [])
  set v := (avl (PZ Q) (mz Z) (rawL [])).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) (rawL [])) := List.filter_sublist
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
  have hcod : ∀ w ∈ v, w.r = RZ [] Z w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw)
    have : x &&& mz Z ∈ WZ [] Z := ⟨x, hx, rfl⟩
    change 3 = RZ [] Z (x &&& mz Z)
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
  have hcl : Cl (PZ Q) (tz Z) (L - 1) t (fun j => L - 1 - t - (Q.getD j (0, L - 1 - t)).2) S := by
    intro j hj q u hu hq
    obtain ⟨e1,e2⟩ := hPget j hj
    have memj : j < Q.length := by simpa [PZ] using hj
    have eqj : Q.getD j (0,L-1-t) = Q.getD j (0,L-1) := by
      simp [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem memj]
    change q + (L-1-t-(Q.getD j (0,L-1-t)).2) + t < L-1+u at hq
    rw [eqj] at hq
    rw [e1]
    exact hno _ e2 q u hu (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - t - e.2)) - sumc v) v S := by
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
  have hhas : hasP (pwr [] Z) v = true := hasP_ok (hpw.imp id fun h => hrep.mem.1 h)
  have all : ∀ p ∈ M, topC (lz Z) (mz Z) (pL (Q.map fun _ => 16)) (L - 1) p.1 p.2 (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - t - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startv, bR, hhas, hble, Bool.cond_true] at h3
    exact child_sound X (f := fun z r => topC (lz Z) (mz Z) _ (L - 1) p.1 p.2 (L - 1) t z r) (fun h => rfl) hst hm (by omega) h3
  refine topC_sound X (RZ_R [] Z) (RZ_R2 [] Z) hMf all hst hcod (by omega) hl ?_
  intro q hq hs
  rw [RZ_set] at hs
  refine lower q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

end BinarySearch
lemma Steps.signCount {m T q u S} (h : Steps m T q u S) : u ≤ q := by
  induction h <;> omega

def gradedRow (t : ℕ) (e : ℕ × ℕ) : ℕ × ℕ := (e.1,e.2+1-t)
def HasGrade (t : ℕ) (g : ℕ × ℕ) : Prop :=
  ∀ q u, u ≤ t → q < g.2 + u → ¬ Steps (mz g.1) (tz g.1) q u (C (mz g.1) (WZ [] g.1))

lemma gradeFromFloor {z h t : ℕ} (floor : Imp [] z h) (h0 : tz z ≠ 0) (h1 : tz z ≠ mz z)
    (no : ∀ S : Finset ℕ, (S : Set ℕ) ⊆ WZ [] z → Live Z0 (mz z) (tz z) h t S → False) :
    HasGrade t (gradedRow t (z,h)) := by
  intro q u hu hq steps
  change q < h+1-t+u at hq
  change Steps (mz z) (tz z) q u (C (mz z) (WZ [] z)) at steps
  have huq := steps.signCount
  by_cases cap : t ≤ h+1
  · obtain ⟨k,v,S,hk,hv,count,hS,hl⟩ := steps.liveCount
    have hlow : h ≤ k := by
      by_contra short
      exact floor k (by omega) (hl.sol.mono le_rfl hS)
    have ek : k = h := by omega
    have ev : v = t := by omega
    subst k v
    have hm : Min Z0 (mz z) (tz z) h t S := by
      refine ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl ?_)⟩
      rintro x (hx | hx)
      · exact hS hx
      · exact Or.inr hx
    have hbd : ∀ x ∈ S, x &&& mz z = x := by
      intro x hx
      rcases hS hx with ⟨w,_,rfl⟩ | c
      · rw [Nat.and_assoc,Nat.and_self]
      · simp at c; rcases c with rfl | rfl <;> simp
    obtain ⟨ha,hb⟩ := hm.proper (by simp only [tz,nl,Nat.and_assoc,Nat.and_self]) h0 h1 hbd
    apply no S _ hl
    intro x hx
    rcases hS hx with h | c
    · exact h
    · simp at c; rcases c with rfl | rfl
      · exact absurd hx ha
      · exact absurd hx hb
  · omega

noncomputable def gradeTest (t : ℕ) (before : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  let Q := pr (before.map (gradedRow t)) e.1
  pOk e.1 Q && (e.2+1 ≤ 15) &&
    (e.2 < t || !BinarySearch.chk [] Q e.1 e.2 t FF 1)

lemma checkedGrade {t : ℕ} {before : List (ℕ × ℕ)} {e : ℕ × ℕ}
    (floor : Imp [] e.1 e.2)
    (prior : ∀ x ∈ before, HasGrade t (gradedRow t x))
    (tested : gradeTest t before e = true) : HasGrade t (gradedRow t e) := by
  rcases e with ⟨z,h⟩
  let Q := pr (before.map (gradedRow t)) z
  change pOk z Q && decide (h+1 ≤ 15) && (decide (h < t) || !BinarySearch.chk [] Q z h t FF 1) = true at tested
  simp only [Bool.and_eq_true,decide_eq_true_eq,Bool.or_eq_true,Bool.not_eq_true'] at tested
  obtain ⟨⟨hp,hlim⟩,branch⟩ := tested
  have pn := hp
  simp only [pOk,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at pn
  obtain ⟨⟨p0,p1⟩,_⟩ := pn
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e,Nat.beq_refl] at h; simp at h
  apply gradeFromFloor floor (nb p0) (nb p1)
  intro S sw hl
  have hm : Min Z0 (mz z) (tz z) h t S :=
    ⟨hl,fun j hj hs => floor j hj (hs.mono le_rfl (C_mono sw))⟩
  rcases branch with lt | chk
  · have := hm.size.2; omega
  · refine BinarySearch.rejectMinimum (Q := Q) (L := h+1) hp hlim (by omega) ?_ sw hl floor [(FF,1)] ffull ?_
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := List.mem_map.1 (List.mem_of_mem_filter hx)
      exact prior y hy
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      simpa using chk

lemma addGrades {t : ℕ} {before group : List (ℕ × ℕ)}
    (lower : ∀ e ∈ group, Imp [] e.1 e.2)
    (prior : ∀ e ∈ before, HasGrade t (gradedRow t e))
    (checks : group.all (gradeTest t before) = true) :
    ∀ e ∈ group, HasGrade t (gradedRow t e) :=
  fun e he => checkedGrade (lower e he) prior (List.all_eq_true.1 checks e he)

lemma joinGrades {t : ℕ} {a b : List (ℕ × ℕ)}
    (h1 : ∀ e ∈ a, HasGrade t (gradedRow t e))
    (h2 : ∀ e ∈ b, HasGrade t (gradedRow t e)) :
    ∀ e ∈ a ++ b, HasGrade t (gradedRow t e) :=
  fun e he => (List.mem_append.1 he).elim (h1 e) (h2 e)

lemma gradeWeak {z h t : ℕ} (floor : Imp [] z h) : HasGrade t (z,h-t) := by
  intro q u hu hq st
  change Steps (mz z) (tz z) q u (C (mz z) (WZ [] z)) at st
  change q < h-t+u at hq
  have huq := st.signCount
  obtain ⟨k,v,S,hk,_,_,hS,hl⟩ := st.liveCount
  exact floor k (by omega) (hl.sol.mono le_rfl hS)

section inst_data
def r5 : List (ℕ × ℕ) := [(31, 1), (47, 4), (55, 4), (59, 4), (61, 4), (62, 2), (79, 1), (87, 2), (91, 1), (93, 2), (94, 2), (103, 2), (107, 2), (109, 4), (110, 4), (115, 2), (117, 2), (118, 4), (121, 2), (122, 2), (124, 2), (143, 1), (151, 2), (155, 1), (157, 2), (158, 1), (167, 2), (171, 2), (173, 4), (174, 2), (179, 2), (181, 2), (182, 2), (185, 2), (186, 1), (188, 1), (199, 1), (205, 2), (206, 2), (211, 1), (213, 2), (214, 4), (217, 1), (218, 1), (220, 2), (229, 1), (230, 2), (233, 1), (234, 1), (236, 2), (242, 1), (244, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk5 : r5.all (demandedRow []) = true := by decide +kernel
lemma i5 : ∀ e ∈ r5, Imp [] e.1 e.2 := demandedAll (T := []) chk5 (by simp)
def rs5 : List (ℕ × ℕ) := r5
lemma is5 : ∀ e ∈ rs5, Imp [] e.1 e.2 := i5
def r4 : List (ℕ × ℕ) := [(15, 4), (23, 5), (27, 4), (29, 5), (30, 4), (39, 5), (43, 5), (45, 7), (46, 5), (51, 5), (53, 5), (54, 5), (57, 5), (58, 5), (60, 5), (71, 4), (75, 2), (77, 5), (78, 5), (83, 4), (85, 3), (86, 5), (89, 4), (90, 4), (92, 3), (99, 3), (101, 5), (102, 5), (105, 5), (106, 5), (108, 5), (113, 3), (114, 5), (116, 5), (120, 3), (135, 4), (139, 2), (141, 5), (142, 4), (147, 4), (149, 3), (150, 5), (153, 4), (154, 3), (156, 4), (163, 3), (165, 5), (166, 3), (169, 5), (170, 4), (172, 5), (177, 3), (178, 4), (180, 4), (184, 2), (195, 1), (197, 4), (198, 5), (201, 2), (202, 2), (204, 3), (209, 2), (210, 4), (212, 5), (216, 2), (225, 1), (226, 2), (228, 4), (232, 2), (240, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk4 : r4.all (demandedRow rs5) = true := by decide +kernel
lemma i4 : ∀ e ∈ r4, Imp [] e.1 e.2 := demandedAll (T := rs5) chk4 is5
def rs4 : List (ℕ × ℕ) := r4 ++ rs5
lemma is4 : ∀ e ∈ rs4, Imp [] e.1 e.2 := apI i4 is5
def r3 : List (ℕ × ℕ) := [(7, 7), (11, 5), (13, 8), (14, 7), (19, 7), (21, 6), (22, 7), (25, 7), (26, 7), (28, 6), (35, 6), (37, 8), (38, 6), (41, 8), (42, 7), (44, 8), (49, 6), (50, 7), (52, 7), (56, 6), (67, 5), (69, 6), (70, 7), (73, 6), (74, 6), (76, 6), (81, 5), (82, 7), (84, 6), (88, 5), (97, 6), (98, 6), (100, 7), (104, 6), (112, 6), (131, 5), (133, 6), (134, 6), (137, 6), (138, 5), (140, 6), (145, 5), (146, 7), (148, 6), (152, 5), (161, 6), (162, 5), (164, 6), (168, 6), (176, 5), (193, 4), (194, 5), (196, 6), (200, 3), (208, 5), (224, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk3 : r3.all (demandedRow rs4) = true := by decide +kernel
lemma i3 : ∀ e ∈ r3, Imp [] e.1 e.2 := demandedAll (T := rs4) chk3 is4
def rs3 : List (ℕ × ℕ) := r3 ++ rs4
lemma is3 : ∀ e ∈ rs3, Imp [] e.1 e.2 := apI i3 is4
def r2 : List (ℕ × ℕ) := [(3, 8), (5, 9), (6, 9), (9, 9), (10, 9), (12, 9), (17, 8), (18, 10), (20, 9), (24, 9), (33, 9), (34, 8), (36, 10), (40, 9), (48, 8), (65, 8), (66, 9), (68, 9), (72, 7), (80, 8), (96, 9), (129, 8), (130, 8), (132, 10), (136, 7), (144, 8), (160, 8), (192, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk2 : r2.all (demandedRow rs3) = true := by decide +kernel
lemma i2 : ∀ e ∈ r2, Imp [] e.1 e.2 := demandedAll (T := rs3) chk2 is3
def rs2 : List (ℕ × ℕ) := r2 ++ rs3
lemma is2 : ∀ e ∈ rs2, Imp [] e.1 e.2 := apI i2 is3
def r1 : List (ℕ × ℕ) := []
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma chk1 : r1.all (demandedRow rs2) = true := by decide +kernel
lemma i1 : ∀ e ∈ r1, Imp [] e.1 e.2 := demandedAll (T := rs2) chk1 is2
def rs1 : List (ℕ × ℕ) := r1 ++ rs2
lemma is1 : ∀ e ∈ rs1, Imp [] e.1 e.2 := apI i1 is2
def pin4 : List (ℕ × ℕ) := [(270, 2), (278, 2), (282, 3), (284, 3), (294, 2), (298, 3), (300, 3), (306, 3), (308, 3), (312, 3), (326, 3), (330, 2), (332, 2), (338, 2), (340, 2), (344, 1), (354, 2), (356, 2), (360, 1), (368, 1), (390, 2), (394, 3), (396, 3), (402, 3), (404, 3), (408, 3), (418, 3), (420, 3), (424, 3), (432, 3), (450, 2), (452, 2), (456, 1), (464, 1), (480, 1), (525, 3), (533, 2), (537, 2), (540, 2), (549, 2), (553, 2), (556, 2), (561, 1), (564, 3), (568, 1), (581, 2), (585, 2), (588, 2), (593, 1), (596, 3), (600, 1), (609, 1), (612, 3), (616, 1), (624, 2), (645, 2), (649, 2), (652, 2), (657, 1), (660, 3), (664, 1), (673, 1), (676, 3), (680, 1), (688, 2), (705, 1), (708, 3), (712, 1), (720, 2), (736, 2), (1035, 1), (1043, 3), (1049, 3), (1050, 3), (1059, 1), (1065, 3), (1066, 3), (1073, 1), (1074, 3), (1080, 1), (1091, 2), (1097, 3), (1098, 3), (1105, 3), (1106, 5), (1112, 3), (1121, 2), (1122, 3), (1128, 3), (1136, 2), (1155, 2), (1161, 3), (1162, 3), (1169, 3), (1170, 5), (1176, 3), (1185, 2), (1186, 3), (1192, 3), (1200, 2), (1217, 4), (1218, 5), (1224, 3), (1232, 5), (1248, 4), (2055, 2), (2067, 2), (2069, 2), (2070, 3), (2083, 1), (2085, 3), (2086, 2), (2097, 1), (2098, 2), (2100, 2), (2115, 1), (2117, 3), (2118, 2), (2129, 1), (2130, 2), (2132, 2), (2145, 2), (2146, 1), (2148, 3), (2160, 1), (2179, 1), (2181, 3), (2182, 2), (2193, 1), (2194, 2), (2196, 2), (2209, 2), (2210, 1), (2212, 3), (2224, 1), (2241, 2), (2242, 1), (2244, 3), (2256, 1), (2272, 2), (4103, 3), (4107, 1), (4109, 2), (4110, 2), (4131, 1), (4133, 2), (4134, 2), (4137, 2), (4138, 2), (4140, 3), (4163, 2), (4165, 3), (4166, 3), (4169, 1), (4170, 1), (4172, 2), (4193, 1), (4194, 1), (4196, 2), (4200, 2), (4227, 2), (4229, 3), (4230, 3), (4233, 1), (4234, 1), (4236, 2), (4257, 1), (4258, 1), (4260, 2), (4264, 2), (4289, 2), (4290, 2), (4292, 3), (4296, 1), (4320, 1), (8199, 5), (8203, 5), (8205, 5), (8206, 5), (8211, 5), (8213, 3), (8214, 3), (8217, 5), (8218, 5), (8220, 3), (8259, 3), (8261, 3), (8262, 3), (8265, 3), (8266, 3), (8268, 3), (8273, 3), (8274, 3), (8276, 2), (8280, 3), (8323, 3), (8325, 3), (8326, 3), (8329, 3), (8330, 3), (8332, 3), (8337, 3), (8338, 3), (8340, 2), (8344, 3), (8385, 1), (8386, 1), (8388, 2), (8392, 1), (8400, 2), (16391, 2), (16395, 2), (16397, 2), (16398, 3), (16403, 2), (16405, 2), (16406, 3), (16409, 2), (16410, 3), (16412, 3), (16419, 3), (16421, 3), (16422, 2), (16425, 3), (16426, 2), (16428, 2), (16433, 3), (16434, 2), (16436, 2), (16440, 2), (16515, 2), (16517, 2), (16518, 3), (16521, 2), (16522, 3), (16524, 3), (16529, 2), (16530, 3), (16532, 3), (16536, 3), (16545, 3), (16546, 2), (16548, 2), (16552, 2), (16560, 2), (32775, 2), (32779, 2), (32781, 2), (32782, 2), (32787, 2), (32789, 2), (32790, 2), (32793, 2), (32794, 2), (32796, 2), (32803, 3), (32805, 3), (32806, 3), (32809, 3), (32810, 3), (32812, 3), (32817, 3), (32818, 3), (32820, 3), (32824, 3), (32835, 2), (32837, 2), (32838, 2), (32841, 2), (32842, 2), (32844, 2), (32849, 2), (32850, 2), (32852, 2), (32856, 2), (32865, 3), (32866, 3), (32868, 3), (32872, 3), (32880, 3)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4 : pin4.all (demandedRow rs1) = true := by decide +kernel
lemma h4 : ∀ e ∈ pin4, Imp [] e.1 e.2 := demandedAll (T := rs1) v4 is1
def pv4 : List (ℕ × ℕ) := rs1 ++ pin4
lemma hv4 : ∀ e ∈ pv4, Imp [] e.1 e.2 := apI is1 h4
def pin3 : List (ℕ × ℕ) := [(262, 3), (266, 4), (268, 4), (274, 4), (276, 4), (280, 4), (290, 4), (292, 4), (296, 4), (304, 4), (322, 3), (324, 3), (328, 2), (336, 2), (352, 2), (386, 4), (388, 4), (392, 4), (400, 4), (416, 4), (448, 2), (517, 3), (521, 3), (524, 3), (529, 2), (532, 4), (536, 2), (545, 2), (548, 4), (552, 2), (560, 3), (577, 2), (580, 4), (584, 2), (592, 3), (608, 3), (641, 2), (644, 4), (648, 2), (656, 3), (672, 3), (704, 3), (1027, 3), (1033, 4), (1034, 4), (1041, 4), (1042, 6), (1048, 4), (1057, 3), (1058, 4), (1064, 4), (1072, 3), (1089, 5), (1090, 6), (1096, 4), (1104, 6), (1120, 5), (1153, 5), (1154, 6), (1160, 4), (1168, 6), (1184, 5), (1216, 6), (2051, 2), (2053, 4), (2054, 3), (2065, 2), (2066, 3), (2068, 3), (2081, 3), (2082, 2), (2084, 4), (2096, 2), (2113, 3), (2114, 2), (2116, 4), (2128, 2), (2144, 3), (2177, 3), (2178, 2), (2180, 4), (2192, 2), (2208, 3), (2240, 3), (4099, 3), (4101, 4), (4102, 4), (4105, 2), (4106, 2), (4108, 3), (4129, 2), (4130, 2), (4132, 3), (4136, 3), (4161, 3), (4162, 3), (4164, 4), (4168, 2), (4192, 2), (4225, 3), (4226, 3), (4228, 4), (4232, 2), (4256, 2), (4288, 3), (8195, 6), (8197, 6), (8198, 6), (8201, 6), (8202, 6), (8204, 6), (8209, 6), (8210, 6), (8212, 4), (8216, 6), (8257, 4), (8258, 4), (8260, 4), (8264, 4), (8272, 4), (8321, 4), (8322, 4), (8324, 4), (8328, 4), (8336, 4), (8384, 2), (16387, 3), (16389, 3), (16390, 4), (16393, 3), (16394, 4), (16396, 4), (16401, 3), (16402, 4), (16404, 4), (16408, 4), (16417, 4), (16418, 3), (16420, 3), (16424, 3), (16432, 3), (16513, 3), (16514, 4), (16516, 4), (16520, 4), (16528, 4), (16544, 3), (32771, 3), (32773, 3), (32774, 3), (32777, 3), (32778, 3), (32780, 3), (32785, 3), (32786, 3), (32788, 3), (32792, 3), (32801, 4), (32802, 4), (32804, 4), (32808, 4), (32816, 4), (32833, 3), (32834, 3), (32836, 3), (32840, 3), (32848, 3), (32864, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v3 : pin3.all (demandedRow pv4) = true := by decide +kernel
lemma h3 : ∀ e ∈ pin3, Imp [] e.1 e.2 := demandedAll (T := pv4) v3 hv4
def pv3 : List (ℕ × ℕ) := pv4 ++ pin3
lemma hv3 : ∀ e ∈ pv3, Imp [] e.1 e.2 := apI hv4 h3
def pin2 : List (ℕ × ℕ) := [(258, 5), (260, 5), (264, 5), (272, 5), (288, 5), (320, 3), (384, 5), (513, 3), (516, 5), (520, 3), (528, 4), (544, 4), (576, 4), (640, 4), (1025, 6), (1026, 7), (1032, 5), (1040, 7), (1056, 6), (1088, 7), (1152, 7), (2049, 4), (2050, 3), (2052, 5), (2064, 3), (2080, 4), (2112, 4), (2176, 4), (4097, 4), (4098, 4), (4100, 5), (4104, 3), (4128, 3), (4160, 4), (4224, 4), (8193, 7), (8194, 7), (8196, 7), (8200, 7), (8208, 7), (8256, 5), (8320, 5), (16385, 4), (16386, 5), (16388, 5), (16392, 5), (16400, 5), (16416, 4), (16512, 5), (32769, 4), (32770, 4), (32772, 4), (32776, 4), (32784, 4), (32800, 5), (32832, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2 : pin2.all (demandedRow pv3) = true := by decide +kernel
lemma h2 : ∀ e ∈ pin2, Imp [] e.1 e.2 := demandedAll (T := pv3) v2 hv3
def pv2 : List (ℕ × ℕ) := pv3 ++ pin2
lemma hv2 : ∀ e ∈ pv2, Imp [] e.1 e.2 := apI hv3 h2
def pin1 : List (ℕ × ℕ) := [(256, 6), (512, 5), (1024, 8), (2048, 5), (4096, 5), (8192, 8), (16384, 6), (32768, 5)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1 : pin1.all (demandedRow pv2) = true := by decide +kernel
lemma h1 : ∀ e ∈ pin1, Imp [] e.1 e.2 := demandedAll (T := pv2) v1 hv2
def pv1 : List (ℕ × ℕ) := pv2 ++ pin1
lemma hv1 : ∀ e ∈ pv1, Imp [] e.1 e.2 := apI hv2 h1
def rStrong : List (ℕ × ℕ) := [(1, 11), (2, 11), (4, 12), (8, 11), (16, 11), (32, 11), (128, 11)]

def strongPrior : List (ℕ × ℕ) := pv1.filter (fun e => e.2 ≥ 4)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongRows_check : rStrong.all (demandedRow strongPrior) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongRows_sound : ∀ e ∈ rStrong, Imp [] e.1 e.2 :=
  demandedAll strongRows_check (fun e he => hv1 e (List.mem_of_mem_filter he))

private def graph : (Fin 8 → Bool) → Bool := fun x =>
  decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)

private def witness : Circuit := ⟨[
   ⟨.or, [5, 0]⟩,
   ⟨.and, [3, 8]⟩,
   ⟨.or, [1, 0]⟩,
   ⟨.or, [5, 4]⟩,
   ⟨.and, [10, 11]⟩,
   ⟨.or, [4, 3]⟩,
   ⟨.or, [13, 2]⟩,
   ⟨.or, [14, 1]⟩,
   ⟨.or, [7, 6]⟩,
   ⟨.and, [15, 16]⟩,
   ⟨.or, [6, 0]⟩,
   ⟨.and, [18, 7]⟩,
   ⟨.or, [9, 12]⟩,
   ⟨.or, [20, 17]⟩,
   ⟨.or, [21, 19]⟩], 22⟩

lemma witness_basis : ∀ g ∈ witness.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  simp [witness]

lemma witness_size : witness.gates.length = 15 := rfl

def f (x : Fin 8 → Bool) : Bool := (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

lemma f_graph (x : Fin 8 → Bool) : f x = graph x := by
  have hx : f x = true ↔ (x 0 = true ∧ x 3 = true) ∨ (x 0 = true ∧ x 4 = true) ∨ (x 1 = true ∧ x 4 = true) ∨ (x 0 = true ∧ x 5 = true) ∨ (x 1 = true ∧ x 5 = true) ∨ (x 3 = true ∧ x 5 = true) ∨ (x 1 = true ∧ x 6 = true) ∨ (x 2 = true ∧ x 6 = true) ∨ (x 3 = true ∧ x 6 = true) ∨ (x 4 = true ∧ x 6 = true) ∨ (x 0 = true ∧ x 7 = true) ∨ (x 1 = true ∧ x 7 = true) ∨ (x 2 = true ∧ x 7 = true) ∨ (x 3 = true ∧ x 7 = true) ∨ (x 4 = true ∧ x 7 = true) ∨ (x 6 = true ∧ x 7 = true) := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true, or_assoc]
  unfold graph
  rw [Bool.eq_iff_iff, hx, decide_eq_true_eq]
  constructor
  · rintro (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h)
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
    · exact ⟨13, by decide, by simpa using h⟩
    · exact ⟨14, by decide, by simpa using h⟩
    · exact ⟨15, by decide, by simpa using h⟩
  · rintro ⟨i, hi, h⟩
    have hi' : i < 16 := hi
    interval_cases i <;> simp_all

set_option maxHeartbeats 5000000 in
lemma witness_eval (x : Fin 8 → Bool) : witness.eval (List.ofFn x) = graph x := by
  rw [← f_graph]
  simp only [witness, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.ofFn_succ, List.ofFn_zero, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, List.getD_cons_zero, List.getD_cons_succ, GateOp.eval, List.any_cons,
    List.any_nil, List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
  change ((((x 3 && (x 5 || x 0)) || ((x 1 || x 0) && (x 5 || x 4))) || ((((x 4 || x 3) || x 2) || x 1) && (x 7 || x 6))) || ((x 6 || x 0) && x 7)) = f x
  unfold f
  simp only [Bool.and_or_distrib_left, Bool.and_or_distrib_right, Bool.and_comm,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

def EF : ℕ := (rawP0.getD 0 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 3 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 6 0) ||| (rawP0.getD 2 0 &&& rawP0.getD 6 0) ||| (rawP0.getD 3 0 &&& rawP0.getD 6 0) ||| (rawP0.getD 4 0 &&& rawP0.getD 6 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 7 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 7 0) ||| (rawP0.getD 2 0 &&& rawP0.getD 7 0) ||| (rawP0.getD 3 0 &&& rawP0.getD 7 0) ||| (rawP0.getD 4 0 &&& rawP0.getD 7 0) ||| (rawP0.getD 6 0 &&& rawP0.getD 7 0)
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


def grade5 : List (ℕ × ℕ) := r5
def grade4 : List (ℕ × ℕ) := grade5 ++ r4
def grade3 : List (ℕ × ℕ) := grade4 ++ r3
def grade2 : List (ℕ × ℕ) := grade3 ++ r2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grade5_sound : ∀ e ∈ grade5, HasGrade 1 (gradedRow 1 e) :=
  addGrades (before := []) i5 (by simp) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grade4_sound : ∀ e ∈ grade4, HasGrade 1 (gradedRow 1 e) :=
  joinGrades grade5_sound (addGrades i4 grade5_sound (by decide +kernel))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grade3_sound : ∀ e ∈ grade3, HasGrade 1 (gradedRow 1 e) :=
  joinGrades grade4_sound (addGrades i3 grade4_sound (by decide +kernel))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma grade2_sound : ∀ e ∈ grade2, HasGrade 1 (gradedRow 1 e) :=
  joinGrades grade3_sound (addGrades i2 grade3_sound (by decide +kernel))

lemma gradeRow_one (e : ℕ × ℕ) : gradedRow 1 e = e := by cases e <;> simp [gradedRow]

def pinFloors : List (ℕ × ℕ) := pin4 ++ pin3 ++ pin2 ++ pin1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pinFloors_sound : ∀ e ∈ pinFloors, Imp [] e.1 e.2 := apI (apI (apI h4 h3) h2) h1


def gradePin4 : List (ℕ × ℕ) := grade2 ++ pin4

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradePin4_sound : ∀ e ∈ gradePin4, HasGrade 1 (gradedRow 1 e) :=
  joinGrades grade2_sound (addGrades h4 grade2_sound (by decide +kernel))

def gradePin3 : List (ℕ × ℕ) := gradePin4 ++ pin3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradePin3_sound : ∀ e ∈ gradePin3, HasGrade 1 (gradedRow 1 e) :=
  joinGrades gradePin4_sound (addGrades h3 gradePin4_sound (by decide +kernel))

def gradePin2 : List (ℕ × ℕ) := gradePin3 ++ pin2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradePin2_sound : ∀ e ∈ gradePin2, HasGrade 1 (gradedRow 1 e) :=
  joinGrades gradePin3_sound (addGrades h2 gradePin3_sound (by decide +kernel))

def gradePin1 : List (ℕ × ℕ) := gradePin2 ++ pin1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradePin1_sound : ∀ e ∈ gradePin1, HasGrade 1 (gradedRow 1 e) :=
  joinGrades gradePin2_sound (addGrades h1 gradePin2_sound (by decide +kernel))

def singletonPrior : List (ℕ × ℕ) := gradePin1
lemma singletonPrior_sound : ∀ e ∈ singletonPrior, HasGrade 1 (gradedRow 1 e) := gradePin1_sound

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma strongSingletonGrades : ∀ e ∈ rStrong, HasGrade 1 (gradedRow 1 e) :=
  addGrades (before := singletonPrior) strongRows_sound singletonPrior_sound (by decide +kernel)

def gradeRootBounds : List (ℕ × ℕ) :=
  (rStrong ++ singletonPrior).filter (fun e => e.2 ≥ 5)

lemma gradeRootBounds_sound : ∀ e ∈ gradeRootBounds, HasGrade 1 e := by
  intro e he
  have h := joinGrades strongSingletonGrades singletonPrior_sound e (List.mem_of_mem_filter he)
  simpa only [gradeRow_one] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradeRoot_p : pOk 0 gradeRootBounds = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma zeroFloors : ∀ e ∈ grade2, Imp [] e.1 e.2 := apI (apI (apI i5 i4) i3) i2

def totalRootBounds : List (ℕ × ℕ) :=
  (rStrong ++ (grade2 ++ pinFloors)).filter (fun e => e.2 ≥ 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma totalRootBounds_sound : ∀ e ∈ totalRootBounds, Imp [] e.1 e.2 :=
  fun e h => apI strongRows_sound (apI zeroFloors pinFloors_sound) e (List.mem_of_mem_filter h)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma totalRoot_p : pOk 0 totalRootBounds = true := by decide +kernel

def rootPreparedWords : List W := [
  ⟨0x1fffffbf00000000000000000000000000000000000000000000000000000000000860025280c0006000300180300000000800010000400100000001000008010000000200400004000000000000000000fff001fbf80007f000083f80008200fe00020843f80008410fe00021048210fc006bff5ad557feabff55ffaffdff800000000000000000000000000000000000000000000000000009218fe0e639372c7, 0x40000020000000000100000000010000000000000000002108420000000000000001084010842108400000000000000000000000000108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000040000000, 0x8000000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x8000000000840000020000000000100000000010000000000000000002108420000000000000001084010842108400000000000000000000000000108421084210842108421080000000000000000000000000000000000000000000084210842000000000000000000000000000040000000, 0x3⟩,
  ⟨0x1fffff807ffffe00000007ffffdf7dc000000000000000000000000000000000000c520b5a80a80054002a01502a05ad400c8001900064019024aa21b0090d81b000000340680006800000000000000000be00e00207c3800807001043f0fbee000f008000003c02104000f008402088003860005ad40000000000000000002d6b000000000000000001b555affd6d7feffc00000000000000098f5d06f32eb0f0e, 0x800000000000000000000400000000800000000000000000100001000000000000000000000800000020000000842108000000000000000021084200000000000004210840000000000000842108421084000000000000000210800108421084000042108421084200002000000, 0x20000000000000021084210800000000000000000000421084210840000000000000842108420000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x20000000800000021084210800000400000000800000421084210840100001000000842108420000000800000020000000842108000000000000000021084200000000000004210840000000000000842108421084000000000000000210800108421084000042108421084200002000000, 0x3⟩,
  ⟨0x7ffffefffffdf000000000000000000000000000000000000000000000051c000000300018000c00600c012960270004e0023808e0000000c0000600c000000180300003000000000000000000c00f010307fc060ff80fa07c00410081f001042207c00420881f001082410083c06bff00000000000000000000002d6b557feaaffd5bff6ffc00000000000000000000000000000009b3e6d86eb396fa1, 0x1000000000008000000000000000000000000002000001084200000000001080210000000021084210000000000000000000108400000000000000000004210842108421084210000000000000000000000000084000000108421084210800000000000000000000000, 0x400000000042108400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x400000000042108401000000000008000000000000000000000000002000001084200000000001080210000000021084210000000000000000000108400000000000000000004210842108421084210000000000000000000000000084000000108421084210800000000000000000000000, 0x3⟩,
  ⟨0xfffffc000000000000000000000000000001fffff03e1f03c000010840000010800848844422046000202208044123108c420000004120a210430008288410c4910c000000000000000002102c080840b41d5160008096082202015821080804e10421245b81f0f81e040b080000040000000044002001ff8003010000200118006000011000010d000ffc21434003ff6dbff6fef15f7d3259bd9, 0x800000000004000000000001000200840000020000200042008420000000000000400000010000008000080010042000000000200002000401080000040000400080210000100020084000802100421000010802000001004000800100420084210800000001, 0x10000000000000000000000000000010842108000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x10000000000000000800000000004010842108001000200840000020000200042008420000000000000400000010000008000080010042000000000200002000401080000040000400080210000100020084000802100421000010802000001004000800100420084210800000001, 0x3⟩,
  ⟨0x7ffffdf001fffff7def00000000000000000000000000000309002a0e0006000300180304800a80e000180006001836aa002800014028252240700e0000c00000000000000000210818808420610600c418638cf8006188f3ef790403800804100e0420104442060000580157fe000000000000002c00557fe0000000000001b550000000000001ad5b5ffbff00000ccfdb29b8db69d11, 0x2000000080000000000020000000040000421000000000008000080010842000001004200040000001000000800000421080000000100020000010842000000004000002108400000000842100000000210842100000080000040108000000200042108420000010800100000, 0x1000000000000000000000040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x1000000002000000080000040000020000000040000421000000000008000080010842000001004200040000001000000800000421080000000100020000010842000000004000002108400000000842100000000210842100000080000040108000000200042108420000010800100000, 0x3⟩,
  ⟨0x7ffffc07c1fffff01e07ffffde001fffff7bec00000000003c808220d94074a83e01e03c4040880d9401d2907c01e30a0b02d2d81702e340b606c0d8d80e8000000000000000008420020210800406001124b8003e04928c00f00a2a24f000186493df600001080000040c11000a00055ff800000206044000a00015bff0001850580016c000001a05b0000006c000696babab9b9f9aa6, 0x8000000200042000000000200000100000080010800000000000000000108020000000000100000004000002000020004000840008000080000800100021000010000100020004200040008001080200042008401084200842100400084210840008401080210800000400, 0x4000000000000000000000108421084000000000000000000002108421084210000000001084200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x4000000008000000200042108421084200000100000080010802108421084210000108021084200000100000004000002000020004000840008000080000800100021000010000100020004200040008001080200042008401084200842100400084210840008401080210800000400, 0x3⟩,
  ⟨0x1fffff7c007ffffdefbc000000000000000000018000280515038001800c0180000a0051500e0003000c1200940e0000600c35a00028050920700000000000000000108484404212108184220412422088514ccbe000c3326f7de20881801008022121000002014000abff0000000000010050000aaffc00000001b005affc00000001ad000000006dbfffb81b43c85103f8c, 0x100000004000000000001000000002000400084200000000000000000840108400000000002000000080000040000400004210000000001000010000108400000200002000021080000800008420000210800008420000210002000421000010842100001084010000008000, 0x80000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x80000000100000004000002000001000000002000400084200000000000000000840108400000000002000000080000040000400004210000000001000010000108400000200002000021080000800008420000210800008420000210002000421000010842100001084010000008000, 0x3⟩,
  ⟨0x7ffffc0f81fffff7801f7800000000c000000191014a00c40700c00000001910052801840700008405242038061089080e018c3028000000000000000004215010108540201a8081052810440412a04210926b407c01456d3c00fbc00854000000100000880050002ffc000008000008800140006ffc04442001617fe0018c585ff800618002ae05b98957bc359, 0x400000010000000000080000000008020004010040000400004010802100420084200000008000000200000100001000200802000400004000040008020080000800008001004010002000401004010040108021004000040008020080210002008021004200800000020, 0x200000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0x200000000400000010000000000080200000008020004010040000400004010802100420084200000008000000200000100001000200802000400004000040008020080000800008001004010002000401004010040108021004000040008020080210002008021004200800000020, 0x3⟩]
def rootPreparedMask : ℕ := 0x1fffffbf7ffffefffffdf7ffffdf7ddfffff7def7ffffdefbdfffff7bedf7bdfffed7feb5aaaffd57feabff5ffbff5ad6aaffd55ffab7fedffb6aab5ffadaffdffb5ab6bff7fedb7fe0000000000000000fffffdfbfffff7ffffefbffffefbeefffffbef7bffffef7defffffbdf6fbdeffff6bff5ad557feabff55ffaffdffad6b557feaaffd5bff6ffdb555affd6d7feffdad5b5ffbff6dbffffffffffffffffff
def rootPreparedSlots : ℕ := 0x84210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210842108421084210
def rootPreparedBudget : ℕ := 0xc5eb8c5717c6318c6318b5ad6b6316b5ed8b5f18c6318c5ef7bdef7bdef8bdf18bdf17c6318c6318c6317ad6d3ad695b5295ad275a5293ad294a52b8be317be2f8bdb17c5ef7c5ef6bdf17b62f7bdaf8bdad7adab7adef6b5af6b5716c6318c6318c6318c6318c6318c6318b6318c4a5294652

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedWords_eq : avl (PZ gradeRootBounds) (mz 0) (rawL []) = rootPreparedWords :=
  Eq.refl rootPreparedWords
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedMask_eq : mz 0 = rootPreparedMask := Eq.refl rootPreparedMask
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedSlots_eq : pL (gradeRootBounds.map fun _ => 16) = rootPreparedSlots := Eq.refl rootPreparedSlots
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedBudget_eq : pL (gradeRootBounds.map fun e => 16 + (14 - 1 - e.2)) = rootPreparedBudget :=
  Eq.refl rootPreparedBudget
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootPreparedL_eq : lz 0 = I.AA := Eq.refl I.AA
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradeLook1_step (l m g K fuel k t z : ℕ) (v : List W) :
    BinarySearch.look1 l m g K fuel.succ k t z v =
      cvC I.NN (pos t) l v (bif Nat.ble v.length 1 then true else
        tstC I.NN I.AA I.HX I.HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
          bif nodeC I.NN (BinarySearch.look1 l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS then true
          else BinarySearch.mv (BinarySearch.look l m g K) l m g k t z v y)) := by
  change cvC I.NN (pos t) l v (Bool.rec (motive := fun _ => Bool)
      (tstC I.NN I.AA I.HX I.HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (BinarySearch.mv (BinarySearch.look l m g K) l m g k t z v y) true
          (nodeC I.NN (BinarySearch.look1 l m g K fuel (Nat.sub k 1) t) (pos t)
            l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) = _
  simp only [bR]

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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allRootInputsNeeded :
    allInputsNeeded I.NN true I.AA rootPreparedWords 0 = true := by decide +kernel

noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
lemma initialBinary_of_check
    (h : BinarySearch.chk [] gradeRootBounds 0 14 1 FF 0 = true) :
    ∃ b : Fin 8, initialBinary FF (cvOp b)
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = true := by
  simp only [BinarySearch.chk, frc_eq, st_eq, rootPreparedWords_eq, rootPreparedMask_eq,
    rootPreparedSlots_eq, rootPreparedBudget_eq, rootPreparedL_eq, show pwr [] 0 = 0 from rfl] at h
  change anySubC I.NN true I.AA rootPreparedWords 0 _ = true at h
  rw [anySub_allInputs allRootInputsNeeded] at h
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 8 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  have h8 : Nat.beq 8 14 = false := rfl
  have h9 : Nat.beq 9 14 = false := rfl
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 14 rootPreparedWords F = F 0 := by
    simp only [tstC, len, h8, h9, bR, Bool.cond_false]
  simp only [BinarySearch.startv, BinarySearch.topC, child, st_eq, bR, haveRequired, len, budget,
    show Nat.ble 8 (Nat.sub 15 1) = true from rfl, show Nat.ble 8 1 = false from rfl,
    Bool.cond_true, Bool.cond_false] at h
  change tstC I.NN I.AA I.HX I.HY true I.AA 14 rootPreparedWords _ = true at h
  rw [choose0] at h
  let f := BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
  let z := Nat.sub rootPreparedBudget (sumc rootPreparedWords)
  have ifBool (b : Bool) : (bif b then true else false) = b := by cases b <;> rfl
  change (bif nodeC I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8 z rootPreparedWords
    (fun step xs => pairsC FF step (fs xs)) then true else false) = true at h
  rw [ifBool] at h
  exact node_picked I.NN f true I.AA rootPreparedMask rootPreparedSlots 13 8 z rootPreparedWords FF h


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
      BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false) :
    initialBinary H kind
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = false := by
  refine Bool.eq_false_iff.mpr fun original => ?_
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
    BinarySearch.mv
      (BinarySearch.look I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 13 1 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 13 12 1 z v))

lemma pureAt_of_covered (e : ℕ) (state : SearchState) (remaining : SearchState → Bool)
    (miss : ℕ → List W → Bool)
    (complete : pureAt e state miss = false)
    (covered : ∀ z v, miss z v = false → remaining (z,v) = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => miss)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : miss z v
        · exact Bool.noConfusion ((covered z v missed).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (14 : ℕ) = Nat.succ 13 from rfl, gradeLook1_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 13 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureSecond state
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 13 12 1)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def firstStates : List SearchState := [
  ⟨0xada57bd2f6a56d6b5a9494a5295ad3a5296a56d5adad6b4a5294a5294a739ce94a52b494a5294a539ce948ca7094a33a4a53946128ca519ca5294a749d27294e549ca93a4e73a4e729ceb49d694a4e959ca538ca338ce939ce939cab39ce5294e739ce739ce94a4e739ce738ce74a42118c231, rootWithGate 0 1 255 true⟩,
  ⟨0xada77bd2f6ad6d6b5ab59ce739dad3a5696a56d5b5ad6b4e739ce739ce749ce95a52b49ce739ce739ce9494a7094a53a4a539ca3394a519ca5294a749d2939d2749ca93a4e73a5293a52b49d694a4e95a4e7494e54952939ce939cab39ce739ce74a5294a5294a5294a529495294a42318c231, rootWithGate 0 1 253 true⟩,
  ⟨0xad297bd2f6a5294a52b5a5294a5ad39d696a56d5b5ad6b5294a5294a52549ce949ce94a5294a529294e7394a7094a329c6329ca3394a519ca5294a7394e939d2749ca93a4e73a4e729ce93952739ca74a4e7494e54952939ce939cab394a739ce739ce739ce739d294a529495294a42318c231, rootWithGate 0 2 255 true⟩,
  ⟨0xada97bd2f4a56d6b5ab6a52949dad3a5696a52d4a5294a5293a52749ce749ce75a5294a4e749ce739ce9494a7094653a4a529ca338ca5194a51946549d2939d2549ca73a4a729d293a4eb49d2949ce74a4e7394e348ce9394e729c6929ce7294e54a5293a4e949d293a4e748ce739c2318c230, rootWithGate 0 3 255 true⟩,
  ⟨0xada95bd2f6a56b6b5ab69d294a52d3a5676a56d5b56d6b4e73a5294a527494e959d2b39ce74a52929ca749467094a52a4a5394a339463094a5294a739d2739d27394673a4e73a4e93a529395294a4e959ca5394e549527294a729cab394e739ca739d294a5274a4e739ce74952939c2308c231, rootWithGate 0 4 255 true⟩,
  ⟨0xada97ad2f6a56d5b5ab6a4e94a5a93a5695a56d5b5ab6b4e949ce74a52749ce95a52b49ce939ce939ce9494a5094a539ca539c633946519c63194a749d2929d2739ca929ca73a5273a52949d6739ce959ce748ca349527294e93946939ce529ce54a4e73a52939ce73a52938ce93a423184231, rootWithGate 0 6 255 true⟩,
  ⟨0xada97bd2b6a56d6b56b6a5293a5ad3a56969d695b5ad6ad274a4e93a4e749ca95a4eb39d273a4e7394a7494a708ca53a4a339ca3294a509ca328ca549ce939ce749c6939ce539d2939d2b495693a4a94a4e5494a5394e929ca9294a929ca739ca749d2749d273a52749d27394e749c2318c211, rootWithGate 0 7 255 true⟩,
  ⟨0xbd257bd2f6ad294a529494a5295ad49d296a56d6adad6b4a5294a5294a74a52b39ce9494a5294a539d27494e919ce129c632946128ca519ca5294a749d2939d275a4eb4ad294aca5194a93952739ca749ca538ca338ce939ce939cab39ce739d29294a5294a739ce739ce738ce74a46118c231, rootWithGate 1 2 255 true⟩,
  ⟨0xbda57bd2f4adad6b5a9494a5295ad4a5296a52d4a5294a4a5294a5294a94a5294a529494a5294a54a529594e919ca33a4a529461284a5194a5194655a56939d255a4e94ace93a4e729cab49d2949ce749ca528ca1384a9394e729c692a5272952739ce729ca949ce729ca5384a539c6118c230, rootWithGate 1 3 255 true⟩,
  ⟨0xbda55bd2f6adab6b5a9494a52952d4a5276a56d6ad6d6b4a5294a5294a949d2b49d2b394a5294a53a4e7594a919ce32a4a538c6128c63094a5294a74a56739d2749ca94ad294aca729ce9395294a4e95946328ca338ce7294a729cab39d2739ce9294e739ce74a4a5294a538ce739c6108c231, rootWithGate 1 4 255 true⟩,
  ⟨0xbda57ad2f6adad5b5a9494a5295a94a5295a56d6adab6b4a5294a5294a94a52b4a52b494a5294a54a529594e719ce339ca53942128c6519c63194a75a56929d274a4eb3a4e94ace529ce949d6739ce9594a53846138ce7294e9394693a52529d2739ca529ce939ca529ce7284a73a461184231, rootWithGate 1 6 255 true⟩,
  ⟨0xbda57bd2b6adad6b569494a5295ad4a52969d696adad6aca5294a5294a94a4eb4a4eb394a5294a549ce7594e9194e33a4a33946118ca509ca328ca55a52939ce75a4ab4a5274a4e7294eb495693a4a949ca338c6328ca929ca9294a92a4e739ce9394e5394e73a4e5394e528ca549c6118c211, rootWithGate 1 7 255 true⟩,
  ⟨0xbd297bd2f4b5294a52d5a52949dad49d696a52d4a5294a5293a52749ce75a52949ce74a4e749ce739d2749ce919ca329c6319ca338ca5194a51946549d2b4a5675a4e94ace93a4e729ca9394e7394a53a4e7394e348ce9394e729c6929ce939d2739ce729ca7395293a4e748ce739c6318c230, rootWithGate 2 3 255 true⟩,
  ⟨0xbd295bd2f6b5294a52d59d294a52d49d676a56d6b56d6b4e73a5294a52759d2b494e939ce74a52929ce549ca919ce319c63294a339463094a5294a739d294a56949ca94ad294aca729ce728ce739ca749ca5394e549527294a729cab394e94a4e9294e739ce539ce739ce74952939c6308c231, rootWithGate 2 4 255 true⟩,
  ⟨0xbd297ad2f6b5294a52d5a4e94a5a949d695a56d6b5ab6b4e949ce74a5275a52b49ce949ce939ce939d2749ce719ce32946329c633946519c63194a749d2b3a5694a4eb3a4e94ace529ce739525294a749ce748ca349527294e93946939ce73a52739ca529ce7294e73a52938ce93a463184231, rootWithGate 2 6 255 true⟩,
  ⟨0xbd297bd2b6b5294a52d5a5293a5ad49d6969d696b5ad6ad274a4e93a4e75a4eb49ca939d273a4e7394e549ce9194e329c6129ca3294a509ca328ca549ceb4a5295a4ab4a5274a4e7294e938d2729c673a4e5494a5394e929ca9294a929ca94a4e9394e5394e529d2749d27394e749c6318c211, rootWithGate 2 7 255 true⟩,
  ⟨0xbda95bd2f4b5ab6b5ad69d2949d2d4a5676a52d4a5294a4e72a52749ce959d2959d2939ca549ce73a4e759ca919ca52a4a5294a338c6308ca5194654a5694a56749ca74ace93a4e93a4e9394e949ce749ca5294e348ce728ca519c6929d2939ce739d293a4e749ce729ca548ce72946308c230, rootWithGate 3 4 255 true⟩,
  ⟨0xbda97ad2f4b5ad5b5ad6a4e949da94a5695a52d4a5294a4e939ce549ce95a5295a52949ca7394a74a52959ce719ca539ca529c6338c6519463094655a56b3a5674a4e93a4a93a5273a4e949d27394e749ce738ca148ce728ce7294272a52729d254a4e72a4e9394e72a4e7384a729c63184230, rootWithGate 3 6 255 true⟩,
  ⟨0xbda97bd2b4b5ad6b56d6a52939dad4a56969d294a5294a5273a4e739ca95a4e95a4e939ce539ca549ce759ce9194a53a4a329ca328ca5094a318c635a52b4a5275a4a94a4e739d2939ceb4952939ca73a4e5394a338ca9294a7194671a4e939ce749d2739ce739d2739ce538ca53946318c210, rootWithGate 3 7 255 true⟩,
  ⟨0xbda95bcef6b5ab6b5ad69d294a56d39d2759d2d6b56d6b4e73a5294a52749ce949ce939ce74a52939ce759ca919ce52a4a5394a339463094a5294a74a5694a56949ca94ad294ace93a529395294a4e959ca5394e549527294a729cab39d294a4e939d294a5274a4e739ce74952939c6308c231, rootWithGate 4 5 223 true⟩,
  ⟨0xbda95ad2f6b5ab5b5ad69ce94a5294a5675a56d6b56b6b4a739ce74a52959d2b59d2b394a739ce93a4e759ca719ce529ca5394633942309463194a74a5693a56939ca93a4e94ace73a5273952739ce9594a538ca34952518ca72946939d273a4e739ce73a52739ca529ce738ce929c63084231, rootWithGate 4 6 255 true⟩,
  ⟨0xbda97acef6b5ad5b5ad6a4e94a5ab39d2759d2d6b5ab6b4e949ce74a52749ce949ce939ce939ce939ce759ce719ce539ca539c633946519c63194a75a56b3a5694a4eb3a4e94ad273a52949d6739ce959ce748ca349527294e9394693a5273a5274a4e73a52939ce73a52938ce93a463184231, rootWithGate 5 6 223 true⟩,
  ⟨0xbda97bceb6b5ad6b56d6a5293a5ad39d2759d2b6b5ad6ad274a4e93a4e749ce949ce939d273a4e739ce759ce9194e53a4a339ca3294a509ca328ca55a52b4a5295a4ab4a5274a52939d2b495693a4a94a4e5494a5394e929ca9294a92a4e94a4e949d2749d273a52749d27394e749c6318c211, rootWithGate 5 7 223 true⟩,
  ⟨0xbda97ad2b6b5ad5b56d6a4e93a5a94a56959d696b5ab6ace749ca73a4e95a4eb5a4eb394e729ca749ce759ce7194e539ca339c632946509c6118ca55a52b3a5294a4ab39ce74a52739d294956729ca949ce548c63394e7194a928c672a4e73a4e749ce539d2729ce539d2728ca739c63184211, rootWithGate 6 7 255 true⟩]
def firstCount : ℕ := 24

noncomputable def firstAt (i : ℕ) : SearchState := firstStates.getD i (0, [])

noncomputable def flatGate (code : ℕ) : W × ℕ :=
  let zero : W := ⟨0, 0, 0, 0, 3⟩
  let a := rootPreparedWords.getD (code % 8) zero
  let b := rootPreparedWords.getD ((code >>> 3) % 8) zero
  let gate := opW (code.testBit 6) a b
  (gate, gate.c + (a.c ||| b.c))

noncomputable def flatDecode (depth code : ℕ) : SearchState :=
  let raw := (rootPreparedWords.zipIdx.filter fun e => code.testBit e.2).map Prod.fst
  let gates := (List.range depth).map fun i => flatGate (code >>> (8 + 7 * i))
  (rootPreparedBudget - sumc raw - (gates.foldr (fun e n => e.2 + n) 0),
    gates.foldr (fun e v => addS e.1 v) raw)

def successorCodes (row : ℕ) : List ℕ :=
  (List.range (row % 64)).map fun i => (row >>> (6 + 16 * i)) % 65536

def secondCount : ℕ := 181
def secondCodes : List ℕ := [0xeb2377a48fdd92377dc8fde723f71c8fdf523f7948fdc523f6d48fdf123f3848fcb123f3f48fffb237fac8dfe923ff648dff723ff1c8fff523ff948ffc523fed48fff323f78c8fdc323f6cc8fda323f7c48fee123fac48fe, 0xe563ff158ffb563dfcd8ffc363fe8d8ffe163fb058fefd43ffed0dfeb437fa50ffd9437fdd0ffe743ff1d0fff543ef950fbe543ff150fbc543fed50fbb543ffcd0ffe343ff0d0ffb343ffc50fee143fb050fefd23f7ec8dd, 0xe9c2ff670dff7c3ff9f0bfc7c3ffd70ffe5c2ff170ffb5c3ffcf0ffc3c3fe8f0ffeb837fa60efd9833f9e0ffc783bf960ffc583bed60ffe383fece0ffa383fff58fffb637fad8dfe963ff658dff763df9d8f7c763dfd58ff, 0xd9677fdd9f7f567ff159ffc367f7f51fffb477fad1dfe947ff651dff747ff1d1fff547ef951fbb547efcd1fde347f70d1fdfde1ffef85febe37fdf87fe7e3ffd787fe5e3fed78ffe3e3fecf8ffa3e3fff70bffbc37faf09f, 0xd98b3f9e2ffe58bfff5afffb6b7fadadfe96bff65adff76bdf9daf7c76bded72fbb5cbfed62fbb58bfff797febe77fdf97fe5e7fed79fffdc6ffef1dfd9c77fd71ffc5c7ffae1dfe987bf661cfc787bf961ffb587ffed9df, 0x3f7b7ffbed7fafbdffbcf7fa73bfd9cf7fae3dfe98fbff7a7ffbe97fafadfe7ebfff72bffbcb7faf29fe9caff672dff7cbff1f2ffeb8b7fa62ef]
noncomputable def secondAt (i : ℕ) : SearchState :=
  let block := secondCodes.getD (i / 32) 0
  flatDecode 2 ((block >>> (22 * (i % 32))) % 4194304)

set_option maxRecDepth 100000 in
def secondSuccessorsList : List ℕ := [
  0x1404b20472041c03fa0384034c031802e402a00250023201c001b4016e012e00cc009800480013,
  0x320852081207fa079a0762072e06ea06b60644060005ee05aa0576052604cf,
  0x280dc80d880d700d100cd80ca40c600c1a0be60bb80b620b340ad20aa40a680a3409ea09a40960092c08e80896,
  0x14123211f2119c117a110410d0108c105810240fe00f900f540f160ed00e980e540e2604c80013,
  0x14e41484145c141413f013a8135c132c12dc129c12540e28088d,
  0x1c1884187a182417cc17941758171c16e816ac1670162015e415a6156015180e6c08f605180053,
  0x1c1b7a1b361acc1a941a601a2819d419a41954191418e0092a054c008e,
  0x3c1e9c1e5c1e061de41dac1d741d2e1cfa1ca61c5c1c281bde1b9418e0151c12500eae00d2,
  0x1c20241fec1f821f4a1f1e1ed4191c12a4096e010a,
  0x2221882166213620d42080205e1ede1ba615560eea09b4014c,
  0x622ec22b42252221a21e81be4196c12f409c0018a,
  0x6242023f42392237c231c1c2415940f280a3201ca,
  0x3c271c26dc26862664262c25f825b4257a250e24f6248a247c230020661c5419a015dc13100f520aa40a6e05900217,
  0x2c2852283027ca279e2776248a245a21ca1f30162813600fa20b340ac005e00250,
  0xa2a3029e829922978290228ca289e277a250e24d2235420ba1ca819ec167013a40fe60bb80b4406240295,
  0xa2b282ae42a822a5222021f6e1ce01a281698101a0bf6065802cd,
  0x182bbc2b4a28b4257620f41d1c16d413cc10600c2a068c030c,
  0x1c2c7c2c242bc22a4a27b825941a58171c141010a40c6e06cc,
  0x342d142cd02c8228ec25f423ac1fac1d4c1a94174410d80ca20704034e,
  0x242bf8293027e42634226621241fe41d8c1784147a11100cda077a038e,
  0x3c2c3c2b5229522806264821461de417e4149c11700d3a079c03cd,
  0x102c982ba42aa829ac285c26a023e2219c1e361afa180014f211880d5207f20410,
  0x142cdc2c682af029dc26ec229c201c1e7a1b04187211c80d920832044e,
  0x342d0a2b0a2a3c2706240622fc1e9c1b5c189412280df20854048d]
def secondSuccessors (i : ℕ) : List ℕ := successorCodes (secondSuccessorsList.getD i 0)

def thirdCount : ℕ := 506
def thirdCodes : List ℕ := [0xb54647cfef121fbef890bdd7c48def7e243f7af121fb97891fd6bc48fee3e247e59f123f28f891f9fb848befbc246f75e1227ba70917db3848def5c247f72e122fb17091fde7848fcc3c247e51e123f3ed891bdb2c48def76247b63b123dbd5891fd8ac48feb56247b79b123f30d891f946c48fc, 0xd98a467fdb5237f65a91bfeed48f7c76a47bdac523eff7990fbd7cc8ddf7e643ef2f323f6d7991fbfb8c8bdfbc646eece32377d7191fb8b8c8fdeb8646ef4c323b7661919b8f0c8ede58647edac323f7ed991bbb2cc8ddf76647afab323f715991fbf68c8ddeb4646eeca32377d5191f3ca8c8f9, 0xe9c245e6ce12373df091f9cf848bcc7c247e7ae123f397091798b848fcb5c247e7eb123f3ed891b9d6c48dce96247e6cb12373dd891e9cec48f4c76247a7ab123f395891f98ac48fcb56247a7df7217ff7a90fff7d485febea46ffee522ffef291bfd79489fe9ca45fece5237fae291bfd3148ef, 0xe9ca45eece52377df291fb8f948fdeb8a46ef4c523b7662919bcf148fde58a47efeb523f7eda91bbd6d48dde96a47eecb52377dda91ebced48f5c76a47adae523e6d7291fb6b148f9b58a47efef121f3ef890b9d7c48dcf7e243e73f123f3d7890f9cbc48fcb5e247e7ee122f3ef091b9d78489c, 0xb5c287d5ae143fbcf0a1fd87850feeb8286f74c143bb660a19dcf050fec78287772c143eb960a1fd8b050eac5828775ac143ead60a1fdc7050feb38287f7ef721f7efb90bbd7dc8ddfbce46ef4e722f767391bbd71c8dde98e476fef521f7efa90bbd7d48dde7ea47efee522f7ef291bbd79489d, 0xc786877f2c343eed61a1f7f6cd0dfd96686ffbb343dfd59a1f78acd0fbc36687efef141fbef8a0bdd7c50def7e283f73f143fbd78a0f5cbc50fab5e287d71f143facf8a1fdfb850befbc286f75e1427ba70a17db3850def7c287f73e142fb1f0a1fdeb850fae5c285d72e142fb170a1f58b850fe, 0xe98a877ecc5433f9e2a1ffcb150fbfd6a87dfdb5436fadaa1b7d2d50fbd96a86dfbb543cf9daa1e78ed50f3eb6a86ff4b543ff65aa1bfced50f7c76a87bdae543eed62a1f7fbcd07febe686ffbf341ff979a1f76bcd0fbfdc685ffde3437f671a1bfeb8d0fbc5c687df5c3437fa61a1dfb30d0cf, 0xc782c7372c163fb160b1dd6b058f6a382c7f7ef741ffefba0bfd7dd0dffbce86ff4e742ff673a1bfd71d0dfe98e877fef541efefaa0b7d7d50dbe7ea87dfee542efef2a1b7d79509be9ca85dece5436fdf2a1f78f950fbebca84ff4e542ff672a1bf8f950ffeb8a86df4c543af662a197cf150fb, 0xb5cac7bdac563ced62b1efefcd877b5e6c7becc3633f1e1b1cf6b0d8f7fb46c6feca3637fdd1b1ef8e8d8f7f546c7ddaa363cfcd1b1fb868d8fdfdc2c5f7de1637baf0b13dd3858bed9c2c6f7be163db9f0b16d8f858f6f5c2c7f72e162fb170b1fd6b858f6eb82c6f74c163bb660b19dcf058f6, 0xb54707df1a383f7f7bb0eff7dd857ebeec6bfde7635fa73b16fb39d8d7eb8ec6bf4c7639ff7ab0fff7d585febeac6ff3f563dff72b17ff7958dfebcac4ff4e562ff672b1bfef958f7c7cac7bf5c5637fa62b1dfb3158cfe78ac7bf2c563fff5ab1eff6d58d7eb6ac6bf4b563df65ab1af6b958f3, 0xf54787df2a3c2efcd1e1fb868f0fde9cf057ece7833fae3c19fd79609fe9cb057ece5833f1f2c1dfd7160cfe78b077f2c583bfadac1bfd2d60efd96b067f3b583df1dac1cf6b960fbb5cb07fdac583aed62c1dfb38e0cfc5c7077ecb3833f159c1dfd68e0dfe947077eca3833f1d1c1dfca8e0fb, 0xd9cb84ffbe5c2ff1f2e17fd71709fe98b857ecc5c33f9e2e17fcb170bffd6b85ffdb5c37fadae13fd2d70bfd96b86ffbb5c3df9dae16f8ed70f7b5cb85ddae5c2fed62e1f76b170fffde781ff5f3c27f979e17fd70f09fe987857ecc3c33f961e17ffa8f0bffb4786ff5a3c27fa51e17fb28f0df, 0xfd6bc3ffdb5e17fadaf1bfeed7877e76bc7bdae5e3eff71f07ff78f85ff5c7c3ffdb3e17fdd9f0efeacf87ffd47c3ffda3e17fad1f1bfee8f87ff547c3df2a3e3eed51f1f7c68f8fdfdef81ffdf7c17fafbe13ff79f09fd9cf84ff5c7c27fa63e15ffbd703ffbeb82ff5f5c27f9fae17ff79709f, 0xfdca8ddfde5476faf2a337d3951bbd9ca8edfdb5476f65aa3b7eed51f3c76a8f9fef345f7af9a3bbefcd17de5e68fcdaf347e7f71a37bf78d1ddd9c68eefae347e7ae1a3bbd30d1edd9868e6e3c347b7961a3f36b0d1f9ebefc2ffde7e17fafaf0bfcfd787ffdcbc1ffde5e17faf2f13fef9787f, 0xeb6b94ff4b5caff65ae5bf8ed72f7eb6b16df4b58baf65ac597ced62f3eb6b16ff4b58bbf65ac59fced62f7b5cb17dfee5e4ffaf2f33feed7977fdeb89ffdf5c57f662e39fd79619fe9cb0d7ece5873f65ac39f8ed61e7fbeecabfdf5657f662b39fb30d9cdfbee8affef545efefaa2b7d7d51db, 0x3ef3f4bffbdf23ffbef92ff5f7ca7fae3e53fd31f2afe9cf157ece78b3faf2c53fd3962afd9cb167fef769dfefbb4afd7ddad7fbced6bf4e76adf673b5afd71dad7e98ed73feb5caefedae5b7d6d729be96b95decb5cb6fddae5e78ed72f3]
noncomputable def thirdAt (i : ℕ) : SearchState :=
  let block := thirdCodes.getD (i / 32) 0
  flatDecode 3 ((block >>> (29 * (i % 32))) % 536870912)

set_option maxRecDepth 100000 in
def thirdSuccessorsList : List ℕ := [
  0x22026a023201fa01880150010000e200a4005e000a,
  0xc053204ea0494047a041803dc03a00372033402ee028b,
  0xc07aa0766073a06d006980644063205e205a2054a,
  0xa090a08d2089c0868081407e2056e029e0009,
  0xa0a520a1a09ee09b609620586,
  0x100bf40b940b640b020aec0ab402e40048,
  0x320d1a0ce20c800c480c3205c6,
  0x320e4e0e220dc00daa0d7203220087,
  0x2a0fb20f7a0f040ec60eaa0d6c0a9407c4060000ca,
  0x3a106010000fc60e880c36096003500108,
  0x1811801176112010c810800d820ae80818065c038a,
  0x181276123211c00c6e099c0850069803c80149,
  0x40ee40b3a0183,
  0x2212ba0f220dda09fa06f201c6,
  0x810800ff20f620c940b520a1208ba042a0209,
  0x2010e010340b940444,
  0x3211f6113a104e0e100bca08e6072a0488,
  0x2212b61200116a0f9a0cca0a4a092a077204e2024a,
  0x18125811b20e720d0c078c0506,
  0x2215821542152a14ca1492145e141a13e613b2136e131e12cc,
  0x2a1892184a183217da17a21766172a16f616ba1640162e15cc,
  0x2a1a8a1a461a1a19e219ae1976192218c8,
  0x2a1d8a1d4a1d321cd21c9a1c661c221be81bba1b641b361ae218ee15de12cf,
  0x1a1ec01e9e1e761e0c1de41b361ac0162e1309,
  0x36209e205620001fe61fae1f761f0c1de81bba1b76193a1672134d,
  0x3621962152212e20ee197616a61387,
  0x6222a21f61f221bea16da13c6,
  0xa22ea2292226e20f61e261c2219a6171e1409,
  0x222382237c232e1f5a1c5a19e217521448,
  0x1222661f9e1e521c9a178a1486,
  0x2a22aa21c01fc01eb21cf217ea14c7,
  0x3c230622122116201a1eca1d061a0a18021509,
  0x2234a22d6215e204a1d4a1a5218421548,
  0x2223b621b620aa1daa1aaa18a21587,
  0x426e826882660261825e225b4255a252c24ce24a02470242023cd,
  0x202b082ac02aa82a502a1829dc29a0295a291e28f028a22874281227e427a8276a2711,
  0x202d802d7a2d102cd82c922c5a2c062be82b982b4a,
  0x2f082ed02e922e5a2e022dd82b6023c8,
  0x630aa304a301a2fe42f902f422dea2708,
  0x2831d031983162312a30e82bb02407,
  0x28330432d832a2324e32282746,
  0x34e83488345c341833de339a336427a02449,
  0xe36ec36ac3656363435fc358a3546350e32102f462bd227ce248d,
  0x3437d437ac376e371a3374282c24c7,
  0x3c38e23882385a382a30da2e22285a2508,
  0xc39f4399c396c392e371e33b028b42548,
  0x1a3b823b783b223aca3a923a5a3a2232642f9a2c1e28e2258c,
  0x1a3cb83c743c123be231122e522c5a2908,
  0x3a3d203cda3a2c3906351833da2fe0295825c9,
  0x3de03d883d523bda382c374a355c34182c9c29a0260b,
  0x183eb63e723e123a7c359832902e902cd829c9,
  0x83d4a3a9c3942385437b435c83458314a30082ed02a08264c,
  0x203da03ce23af439a238b437d6362834aa30682a68268b,
  0x323e3a3d343c383b0c39fc38ec364034c432c630ba2d002a8426cd,
  0x363e403df83c423b6c369031802f002d482ac9,
  0x183e9a3c9a3b8e36e8332831e02da02b08,
  0x2e40d440b2404c40043fe03f983f4c3f0c3ec9,
  0xc43f243aa4354433a42c44288424c421841dc41a04150410c,
  0x2a45f245ba4544453c44f444aa446c440c3ede000a,
  0x344686464e462c44240045,
  0x4470c46ea44620084,
  0xc496a492a48d448b2484a481c47c64798474c46ce46344490410c3f1e12c000d0,
  0x3a4aa04a404a1849ec49864798476041583f6e1310010b,
  0x184c404c364be04b884b504b184aec498a481c47dc41a03fb2134d,
  0x184d764d324cd04cbc44d841e613880148,
  0x264dcc4d984ac64644450c42043fda13fa0189,
  0x2a4e8c4e724e104c9849c8424c401e1408,
  0x44f624f1e4ed04b04473a45444292147201c9,
  0x324e084b404a32487446b245ba42f2404a14aa020a,
  0xc4e4c4da04ba04a544894431440aa14c8,
  0x1e4ee64df24cf64bfa4aaa48ea436e40c21509,
  0x224f2a4eb64d004c2a492a45f2438215620249,
  0x44f584d584c4c494c43e21586,
  0x36511c50fa508c505650024fc44f8c3ec8,
  0x3a51a0516023c3,
  0xc523051c44fb02404,
  0x36545c543a53d4538c5356532852ce52a052424fcc3f0e24a0244d,
  0x4552054f4548e52a0527051e051583f5a252c24ca,
  0x4562855d055a055745496532852d650203fa225b4254b,
  0x2e5660554c534c50443fd825c6,
  0x1456fa56a054d4538c40202606,
  0x3a569055ba53cc523a51ba50b240482648,
  0x1456e855dc541c50d440a82686,
  0x2e5644560455365476512e40c426c7,
  0x14593a58f2589c5844580e57d257ba577c572e028a,
  0x385a1e59c659aa597c572a273402c7,
  0x1c5af65aa85a7a576827720306,
  0x145dfa5db25d5c5d045ccc5c905c545c125be45b965b685b10411227e427ae15d0,
  0x45f285ed05ea05e745e165b685b204162287428001620034c,
  0x860105fd85fa05f745e125be45ba85a6a5952579c419e28f028ba165c038f,
  0x20610860fa6098604e57d841da2936169803c9,
  0x2e619461605f545c0c4220296a16c7,
  0x32623a61d860605e505c48425c29a61708,
  0xc62f262a662585f8c5c84429829e21748,
  0x3a61d05fd05e845cc65984583a42d02a1a17ba040a,
  0x1461685edc5d1e59dc585443282a7217d40449,
  0x26626e61ba60845f325d765ab85a3258aa43402a8a182a048c,
  0x3262b2620860c8603a5dba58f243882ad2187204ca,
  0xc62e061145ddc5ad4590c43e02b2a188c0509,
  0x1464f264ae6444640663ce63b8637a63220549,
  0x326584655865182b620585,
  0x1c6644662865fa63282bb205c6,
  0x1467f267ae6744670c66ce66b863462be218c4060a,
  0x2068c868ba6858680e668e639a2c3619180649,
  0x3a6958692865d8650663d22c6e19500688,
  0x326998690c66d82ca21985,
  0x2669d868046704654464102cda19fa06c8,
  0x2669fa697a686e676e647a2d061a260708,
  0x32698868b26784663265b264802d4a1a6a0749,
  0x2068d467dc665464e02daa1a8c0787,
  0x386b5e6b3c6ace6a986a446a3c572c4408,
  0x1c6c446c0c6bd66bba63044f86,
  0x1c6db66d4c6d166cc26cba576a4447,
  0x26e8a6e526e1a6dc26c846a3863424ff4449407ca,
  0x2e6fd66f8e6f766f1e6ed66cd86a4e639257965028080b,
  0x2e708e704a70166b8663ce57fc44dc0848,
  0x1a6dce6a8c50444504,
  0xc70d26e0c6d04643a4545,
  0x1e6eca6e4c6bfc6ac4583a50b245920888,
  0x366f1e6b1c585c50c4,
  0xa700e6f766d786b6e647258b6510a08c8,
  0xc70ce70566f826e846c3264ba58ea45ca0909,
  0x2e70ae6fdc6d9c6c5464d45906,
  0x3c71022dc2,
  0x287160515a2e360944,
  0x20719865122e6e0984,
  0xc71c465502e9a09c4,
  0x28717c713a51882ed20a05,
  0xc71e071b265802f0a0a45,
  0x1e726e72046a0e46102f6c0a86,
  0x26730c72f272986a6a59642f820ac7,
  0x2e720e6a86465a2fe40b05,
  0x32729e727c713c6ac659b4468a30140b48,
  0xc72de6b1e59ea30740b85,
  0x2673386b785a0630900bc5,
  0x38737051ea30c80c04,
  0xa73f073966ba865e231000c46,
  0x38734c6bcc521831620c85,
  0x3073846c046610319a0cc5,
  0xa73dc6c5c666831f20d05,
  0x2c74026c8c46ce322a0d45,
  0xa74a474566ce85a6232400d86,
  0x2c740c6d04471832a20dc5,
  0x2474766d765a8432ce0e05,
  0xa749c6d9c5ae833320e45,
  0x2475ca75a87542750474e85b205258475a33761aca,
  0x1276f67696766e76165b4e528647a41b060e89,
  0x2077ca77b07742770474e45ba852dc47de33ba1b4a,
  0x2e7996794e793678de78a6786e780e66925bd6530a48281b8c,
  0x107a3479ee7802772e721a6dd45c0c5346351833e21bc40ecc,
  0x147af47a9c7a6e7602750c66d05c54538a355c34261c0b,
  0x2c7b8c7b487b26786c74126e04670c5cbc359a1c7a0f0b,
  0x1c7a5e78b077567668755e724a6e445cfa53f2487435c834521cb20f4e,
  0x347ab479f678ca77b6768a759c5d1c54144896362834b21ccc,
  0x87b107a0e792077d276e475ee67725d76546a48ec364034ca1d0d,
  0xc7b547ad679426eb267ba5daa492c368a1d6a0f8a,
  0x2c7bae799467d45dcc494e36ea1d87,
  0x307c567c3c7bc474f45e3454ac49ae370c1dc9,
  0x27ce87cae760275205e6054d849da382c37761e0a,
  0x287cbc7bd676687578736871505e804a023854379e1e400fcc,
  0x27cd67c36768a75a85ee04a6238b437c01ea0100a,
  0x307c5276e475c45f04553a4abc38da1efa1049,
  0x1c7d427d2e780277205f6055584ada3a2c39361f0a,
  0x387e207dd47da6785868185f904b123a6e1f49,
  0x3c7bde78b07772729e6ed05fd055884b4a3a9c39661f88108c,
  0x27d167c3678ca778c72f66f2855e04ba23af439801fe010cc,
  0x147d9c7d707c4e792077e47466730e6f7a684456364bf83b0c39d62036110f,
  0x207dd679566f88688860004c023b5e20401149,
  0x387e2e798a74ae6fe068d84c5a3bb620981189,
  0x207e58691860504c923bee20c6,
  0xa703a697a60b24cf43c12213211c7,
  0x207e7073a0718e704860f64d383c5621761209,
  0xa73ee70a061184d5a3cb621981247,
  0x27d3479d4614c4da03cea21c6,
  0x1c7d507a2e61ae56664dfa3d062207,
  0x287c9c7a7a61fa56b24e083d522247,
  0x27cf47a9456cc4e603daa2286,
  0x207e547af269b2622a4e803dca22c7,
  0x147d887b2669e6625e4ef23e3c2307,
  0x207dcc7b4c71cc70f262a24f363e4223621289,
  0x387e2c7b8c62c44f583ea22386]
def thirdSuccessors (i : ℕ) : List ℕ := successorCodes (thirdSuccessorsList.getD i 0)

noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.mv
      (BinarySearch.look I.AA rootPreparedMask rootPreparedSlots 14)
      I.AA rootPreparedMask rootPreparedSlots 12 1 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 12 11 1 z v))

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
  rw [afterSecond, frc_eq, st_eq, show (13 : ℕ) = Nat.succ 12 from rfl, gradeLook1_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 1) I.AA state.2 (tstC I.NN I.AA I.HX I.HY true I.AA 12 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 1) I.AA state.2 (bif pureAt 11 state
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 12 11 1)
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



def taggedMissing (codes : List ℕ) (atState : ℕ → SearchState) (z : ℕ) (v : List W) : Bool :=
  st (z % 31) fun tag => !(codes.any fun code =>
    (code / 2048 == tag) && !frontierMissing [atState (code % 2048)] z v)

lemma taggedMissing_found {codes : List ℕ} {atState : ℕ → SearchState} {z : ℕ} {v : List W}
    (h : taggedMissing codes atState z v = false) :
    ∃ code ∈ codes, (z,v) = atState (code % 2048) := by
  simp only [taggedMissing, st_eq, Bool.not_eq_false', List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨code, hc, _, hit⟩ := h
  have captured := frontierMissing_false (boolOfNeg hit)
  exact ⟨code, hc, List.mem_singleton.mp captured⟩

noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  let ids := thirdSuccessors i
  (!pureAt 11 state (taggedMissing ids thirdAt)) &&
    ((ids.all fun j => decide (j % 2048 < thirdCount)) &&
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
  refine pureAt_of_covered 11 (secondAt i) afterThird (taggedMissing (thirdSuccessors i) thirdAt) (boolOfNeg hc) ?_
  intro z v found
  obtain ⟨j, hj, eq⟩ := taggedMissing_found found
  rw [eq]
  have hj' : j % 2048 < thirdCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact boolOfNeg (rangeCheck_at third hj')


noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  let ids := secondSuccessors i
  (!pureSecond state (taggedMissing ids secondAt)) &&
    ((ids.all fun j => decide (j % 2048 < secondCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 12 (firstAt i) afterSecond (taggedMissing (secondSuccessors i) secondAt) (boolOfNeg hc) ?_
  intro z v found
  obtain ⟨j, hj, eq⟩ := taggedMissing_found found
  rw [eq]
  have hj' : j % 2048 < secondCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact next _ hj'


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 4 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 8 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk3 : rangeCheck readyForSecond 12 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk4 : rangeCheck readyForSecond 16 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk5 : rangeCheck readyForSecond 20 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 24 = true :=
  (@rangeCheck_append readyForSecond 0 12 12 (@rangeCheck_append readyForSecond 0 4 8 firstCoverageChunk0 (@rangeCheck_append readyForSecond 4 4 4 firstCoverageChunk1 firstCoverageChunk2)) (@rangeCheck_append readyForSecond 12 4 8 firstCoverageChunk3 (@rangeCheck_append readyForSecond 16 4 4 firstCoverageChunk4 firstCoverageChunk5)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk2 : rangeCheck firstMixedTest 3 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk3 : rangeCheck firstMixedTest 5 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk4 : rangeCheck firstMixedTest 7 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk5 : rangeCheck firstMixedTest 11 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk6 : rangeCheck firstMixedTest 14 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk7 : rangeCheck firstMixedTest 18 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk8 : rangeCheck firstMixedTest 21 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 24 = true :=
  (@rangeCheck_append firstMixedTest 0 7 17 (@rangeCheck_append firstMixedTest 0 3 4 (@rangeCheck_append firstMixedTest 0 2 1 firstMixedChunk0 firstMixedChunk1) (@rangeCheck_append firstMixedTest 3 2 2 firstMixedChunk2 firstMixedChunk3)) (@rangeCheck_append firstMixedTest 7 7 10 (@rangeCheck_append firstMixedTest 7 4 3 firstMixedChunk4 firstMixedChunk5) (@rangeCheck_append firstMixedTest 14 4 6 firstMixedChunk6 (@rangeCheck_append firstMixedTest 18 3 3 firstMixedChunk7 firstMixedChunk8))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 12 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 24 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 36 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 48 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 60 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 72 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 84 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 96 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 108 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 120 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 132 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk12 : rangeCheck readyForThird 144 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk13 : rangeCheck readyForThird 156 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk14 : rangeCheck readyForThird 168 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk15 : rangeCheck readyForThird 180 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 181 = true :=
  (@rangeCheck_append readyForThird 0 96 85 (@rangeCheck_append readyForThird 0 48 48 (@rangeCheck_append readyForThird 0 24 24 (@rangeCheck_append readyForThird 0 12 12 secondCoverageChunk0 secondCoverageChunk1) (@rangeCheck_append readyForThird 24 12 12 secondCoverageChunk2 secondCoverageChunk3)) (@rangeCheck_append readyForThird 48 24 24 (@rangeCheck_append readyForThird 48 12 12 secondCoverageChunk4 secondCoverageChunk5) (@rangeCheck_append readyForThird 72 12 12 secondCoverageChunk6 secondCoverageChunk7))) (@rangeCheck_append readyForThird 96 48 37 (@rangeCheck_append readyForThird 96 24 24 (@rangeCheck_append readyForThird 96 12 12 secondCoverageChunk8 secondCoverageChunk9) (@rangeCheck_append readyForThird 120 12 12 secondCoverageChunk10 secondCoverageChunk11)) (@rangeCheck_append readyForThird 144 24 13 (@rangeCheck_append readyForThird 144 12 12 secondCoverageChunk12 secondCoverageChunk13) (@rangeCheck_append readyForThird 168 12 1 secondCoverageChunk14 secondCoverageChunk15))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 12 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 24 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 36 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 48 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 55 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 67 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 79 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk8 : rangeCheck secondMixedTest 91 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk9 : rangeCheck secondMixedTest 102 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk10 : rangeCheck secondMixedTest 114 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk11 : rangeCheck secondMixedTest 126 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk12 : rangeCheck secondMixedTest 138 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk13 : rangeCheck secondMixedTest 150 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk14 : rangeCheck secondMixedTest 162 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk15 : rangeCheck secondMixedTest 174 7 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 181 = true :=
  (@rangeCheck_append secondMixedTest 0 91 90 (@rangeCheck_append secondMixedTest 0 48 43 (@rangeCheck_append secondMixedTest 0 24 24 (@rangeCheck_append secondMixedTest 0 12 12 secondMixedChunk0 secondMixedChunk1) (@rangeCheck_append secondMixedTest 24 12 12 secondMixedChunk2 secondMixedChunk3)) (@rangeCheck_append secondMixedTest 48 19 24 (@rangeCheck_append secondMixedTest 48 7 12 secondMixedChunk4 secondMixedChunk5) (@rangeCheck_append secondMixedTest 67 12 12 secondMixedChunk6 secondMixedChunk7))) (@rangeCheck_append secondMixedTest 91 47 43 (@rangeCheck_append secondMixedTest 91 23 24 (@rangeCheck_append secondMixedTest 91 11 12 secondMixedChunk8 secondMixedChunk9) (@rangeCheck_append secondMixedTest 114 12 12 secondMixedChunk10 secondMixedChunk11)) (@rangeCheck_append secondMixedTest 138 24 19 (@rangeCheck_append secondMixedTest 138 12 12 secondMixedChunk12 secondMixedChunk13) (@rangeCheck_append secondMixedTest 162 12 7 secondMixedChunk14 secondMixedChunk15))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 80 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 91 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 102 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 117 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 133 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 149 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 165 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 177 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 193 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 209 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 225 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 241 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk17 : rangeCheck thirdTest 257 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk18 : rangeCheck thirdTest 273 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk19 : rangeCheck thirdTest 289 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk20 : rangeCheck thirdTest 305 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk21 : rangeCheck thirdTest 321 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk22 : rangeCheck thirdTest 337 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk23 : rangeCheck thirdTest 353 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk24 : rangeCheck thirdTest 369 15 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk25 : rangeCheck thirdTest 384 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk26 : rangeCheck thirdTest 400 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk27 : rangeCheck thirdTest 416 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk28 : rangeCheck thirdTest 432 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk29 : rangeCheck thirdTest 448 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk30 : rangeCheck thirdTest 464 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk31 : rangeCheck thirdTest 480 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk32 : rangeCheck thirdTest 496 10 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 506 = true :=
  (@rangeCheck_append thirdTest 0 241 265 (@rangeCheck_append thirdTest 0 117 124 (@rangeCheck_append thirdTest 0 64 53 (@rangeCheck_append thirdTest 0 32 32 (@rangeCheck_append thirdTest 0 16 16 thirdTailChunk0 thirdTailChunk1) (@rangeCheck_append thirdTest 32 16 16 thirdTailChunk2 thirdTailChunk3)) (@rangeCheck_append thirdTest 64 27 26 (@rangeCheck_append thirdTest 64 16 11 thirdTailChunk4 thirdTailChunk5) (@rangeCheck_append thirdTest 91 11 15 thirdTailChunk6 thirdTailChunk7))) (@rangeCheck_append thirdTest 117 60 64 (@rangeCheck_append thirdTest 117 32 28 (@rangeCheck_append thirdTest 117 16 16 thirdTailChunk8 thirdTailChunk9) (@rangeCheck_append thirdTest 149 16 12 thirdTailChunk10 thirdTailChunk11)) (@rangeCheck_append thirdTest 177 32 32 (@rangeCheck_append thirdTest 177 16 16 thirdTailChunk12 thirdTailChunk13) (@rangeCheck_append thirdTest 209 16 16 thirdTailChunk14 thirdTailChunk15)))) (@rangeCheck_append thirdTest 241 128 137 (@rangeCheck_append thirdTest 241 64 64 (@rangeCheck_append thirdTest 241 32 32 (@rangeCheck_append thirdTest 241 16 16 thirdTailChunk16 thirdTailChunk17) (@rangeCheck_append thirdTest 273 16 16 thirdTailChunk18 thirdTailChunk19)) (@rangeCheck_append thirdTest 305 32 32 (@rangeCheck_append thirdTest 305 16 16 thirdTailChunk20 thirdTailChunk21) (@rangeCheck_append thirdTest 337 16 16 thirdTailChunk22 thirdTailChunk23))) (@rangeCheck_append thirdTest 369 63 74 (@rangeCheck_append thirdTest 369 31 32 (@rangeCheck_append thirdTest 369 15 16 thirdTailChunk24 thirdTailChunk25) (@rangeCheck_append thirdTest 400 16 16 thirdTailChunk26 thirdTailChunk27)) (@rangeCheck_append thirdTest 432 32 42 (@rangeCheck_append thirdTest 432 16 16 thirdTailChunk28 thirdTailChunk29) (@rangeCheck_append thirdTest 464 16 26 thirdTailChunk30 (@rangeCheck_append thirdTest 480 16 10 thirdTailChunk31 thirdTailChunk32))))))

def initialIndices (kind : Bool) : List ℕ := if kind then [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23] else []

noncomputable def initialStates (kind : Bool) : List SearchState := (initialIndices kind).map firstAt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allInitialIndices (kind : Bool) : (initialIndices kind).all (fun i => decide (i < firstCount)) = true := by
  cases kind <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) :
    initialBinary FF kind (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 14 14 13 1) = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : BinarySearch.chk [] gradeRootBounds 0 14 1 FF 0 = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  obtain ⟨b,hb⟩ := initialBinary_of_check h
  exact Bool.noConfusion ((binaryCertificate (cvOp b)).symm.trans hb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked : BinarySearch.chk [] gradeRootBounds 0 14 1 0 1 = false := by decide +kernel

def binaryRootCases : List (ℕ × ℕ) := [(FF,0), (0,1)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma binaryRootFull : mFull binaryRootCases = true := by decide +kernel

lemma binaryRootChecked (p : ℕ × ℕ) (hp : p ∈ binaryRootCases) :
    BinarySearch.chk [] gradeRootBounds 0 14 1 p.1 p.2 = false := by
  simp only [binaryRootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked

namespace Monotone

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma allRootInputsNeeded :
    allInputsNeeded I.NN false I.AA rootPreparedWords 0 = true := by decide +kernel

noncomputable def initialBinary (H : ℕ) (kind : Bool) (f : ℕ → List W → Bool) : Bool :=
  nodePicked I.NN f false I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
lemma initialBinary_of_check
    (h : BinarySearch.chk [] gradeRootBounds 0 13 0 FF 0 = true) :
    ∃ b : Fin 8, initialBinary FF (cvOp b)
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0) = true := by
  simp only [BinarySearch.chk, frc_eq, st_eq, rootPreparedWords_eq, rootPreparedMask_eq,
    rootPreparedSlots_eq, rootPreparedBudget_eq, rootPreparedL_eq, show pwr [] 0 = 0 from rfl] at h
  change anySubC I.NN false I.AA rootPreparedWords 0 _ = true at h
  rw [anySub_allInputs allRootInputsNeeded] at h
  have haveRequired : hasP 0 rootPreparedWords = true := by decide +kernel
  have len : rootPreparedWords.length = 8 := rfl
  have budget : Nat.beq
      (Nat.land (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedSlots) rootPreparedSlots = true := by decide +kernel
  have h8 : Nat.beq 8 14 = false := rfl
  have h9 : Nat.beq 9 14 = false := rfl
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false I.AA 14 rootPreparedWords F = F 0 := by
    simp only [tstC, len, h8, h9, bR, Bool.cond_false]
  simp only [BinarySearch.startv, BinarySearch.topC, child, st_eq, bR, haveRequired, len, budget,
    show Nat.ble 8 (Nat.sub 14 0) = true from rfl, show Nat.ble 8 1 = false from rfl,
    Bool.cond_true, Bool.cond_false] at h
  change tstC I.NN I.AA I.HX I.HY false I.AA 14 rootPreparedWords _ = true at h
  rw [choose0] at h
  let f := BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0
  let z := Nat.sub rootPreparedBudget (sumc rootPreparedWords)
  have ifBool (b : Bool) : (bif b then true else false) = b := by cases b <;> rfl
  change (bif nodeC I.NN f false I.AA rootPreparedMask rootPreparedSlots 13 8 z rootPreparedWords
    (fun step xs => pairsC FF step (fs xs)) then true else false) = true at h
  rw [ifBool] at h
  exact node_picked I.NN f false I.AA rootPreparedMask rootPreparedSlots 13 8 z rootPreparedWords FF h


lemma initialBinary_from_frontier (H : ℕ) (kind : Bool) (states : List (ℕ × List W))
    (complete : initialBinary H kind (frontierMissing states) = false)
    (checked : ∀ state ∈ states,
      BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0 state.1 state.2 = false) :
    initialBinary H kind
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0) = false := by
  refine Bool.eq_false_iff.mpr fun original => ?_
  unfold initialBinary at original complete
  obtain ⟨_, hit⟩ := nodePicked_distribute
    (branches := fun _ => frontierMissing states)
    I.NN false I.AA rootPreparedMask rootPreparedSlots 13 8
    (Nat.sub rootPreparedBudget (sumc rootPreparedWords)) rootPreparedWords H kind
    (fun z v hit => by
      refine ⟨0, ?_⟩
      cases hm : frontierMissing states z v
      · exact Bool.noConfusion ((checked (z,v) (frontierMissing_false hm)).symm.trans hit)
      · exact hm)
    original
  exact Bool.noConfusion (complete.symm.trans hit)

noncomputable def pureAt (e : ℕ) (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  nodeC I.NN f false I.AA rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2 pairsS

noncomputable def pureSecond (state : SearchState) (f : ℕ → List W → Bool) : Bool :=
  pureAt 12 state f

noncomputable def mixedSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.mv
      (BinarySearch.look I.AA rootPreparedMask rootPreparedSlots 13)
      I.AA rootPreparedMask rootPreparedSlots 12 0 z v 0))

noncomputable def afterSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 12 11 0 z v))

lemma pureAt_of_covered (e : ℕ) (state : SearchState) (remaining : SearchState → Bool)
    (miss : ℕ → List W → Bool)
    (complete : pureAt e state miss = false)
    (covered : ∀ z v, miss z v = false → remaining (z,v) = false) :
    pureAt e state (fun z v => remaining (z,v)) = false := by
  refine Bool.eq_false_iff.mpr fun found => ?_
  simp only [pureAt, nodeC_as_mode, pairsS] at found complete
  have hp := pairs_distribute _ _ (fun a c =>
    pair_distribute (fun left right da dc signal x y =>
      mode_distribute rootPreparedMask rootPreparedSlots e state.2.length state.1 state.2
      left right da dc signal x y
      (g := fun _ => miss)
      (fun z v hit => by
        refine ⟨0, ?_⟩
        cases missed : miss z v
        · exact Bool.noConfusion ((covered z v missed).symm.trans hit)
        · exact missed))
    a c) _ found
  obtain ⟨_, hh⟩ := hp
  exact Bool.noConfusion (complete.symm.trans hh)

lemma afterFirst_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 12)
    (mixed : mixedSecond state = false)
    (pure : pureSecond state (fun z v => afterSecond (z,v)) = false) :
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0 state.1 state.2 = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false I.AA 13 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 13 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 13 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [show (13 : ℕ) = Nat.succ 12 from rfl, gradeLook1_step, lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 0) I.AA state.2 (tstC I.NN I.AA I.HX I.HY false I.AA 13 state.2 _) = _
  rw [choose0]
  simp only [afterSecond, frc_eq, st_eq] at pure
  simp only [mixedSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 0) I.AA state.2 (bif pureSecond state
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 12 11 0)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def mixedFromSecond (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.mv
      (BinarySearch.look I.AA rootPreparedMask rootPreparedSlots 13)
      I.AA rootPreparedMask rootPreparedSlots 11 0 z v 0))

noncomputable def afterThird (state : SearchState) : Bool :=
  frc state.2 (fun v => st state.1 (fun z =>
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 11 10 0 z v))

lemma afterSecond_false (state : SearchState)
    (two : 1 < state.2.length) (small : state.2.length < 11)
    (mixed : mixedFromSecond state = false)
    (pure : pureAt 11 state (fun z v => afterThird (z,v)) = false) :
    afterSecond state = false := by
  have lengthOkay : Nat.ble state.2.length 1 = false := by
    cases h : Nat.ble state.2.length 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (Nat.not_le_of_gt two)
  have choose0 (F : ℕ → Bool) : tstC I.NN I.AA I.HX I.HY false I.AA 12 state.2 F = F 0 := by
    have h0 : Nat.beq state.2.length 12 = false := beq_f (by omega)
    have h1 : Nat.beq state.2.length.succ 12 = false := beq_f (by omega)
    simp only [tstC, bR, h0, h1, Bool.cond_false]
  rw [afterSecond, frc_eq, st_eq, show (12 : ℕ) = Nat.succ 11 from rfl, gradeLook1_step,
    lengthOkay, Bool.cond_false]
  change cvC I.NN (pos 0) I.AA state.2 (tstC I.NN I.AA I.HX I.HY false I.AA 12 state.2 _) = _
  rw [choose0]
  simp only [afterThird, frc_eq, st_eq] at pure
  simp only [mixedFromSecond, frc_eq, st_eq] at mixed
  change cvC I.NN (pos 0) I.AA state.2 (bif pureAt 11 state
      (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 11 10 0)
    then true else _) = _
  rw [pure, mixed]
  simp [cvC, bR]

noncomputable def readyForThird (i : ℕ) : Bool :=
  let state := secondAt i
  let ids := thirdSuccessors i
  (!pureAt 11 state (taggedMissing ids thirdAt)) &&
    ((ids.all fun j => decide (j % 2048 < thirdCount)) &&
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
  refine pureAt_of_covered 11 (secondAt i) afterThird (taggedMissing (thirdSuccessors i) thirdAt) (boolOfNeg hc) ?_
  intro z v found
  obtain ⟨j, hj, eq⟩ := taggedMissing_found found
  rw [eq]
  have hj' : j % 2048 < thirdCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact boolOfNeg (rangeCheck_at third hj')


noncomputable def readyForSecond (i : ℕ) : Bool :=
  let state := firstAt i
  let ids := secondSuccessors i
  (!pureSecond state (taggedMissing ids secondAt)) &&
    ((ids.all fun j => decide (j % 2048 < secondCount)) &&
      (decide (1 < state.2.length) && decide (state.2.length < 12)))

noncomputable def firstMixedTest (i : ℕ) : Bool := !mixedSecond (firstAt i)

lemma checkedAfterFirst (i : ℕ) (hi : i < firstCount)
    (ready : rangeCheck readyForSecond 0 firstCount = true)
    (mixed : rangeCheck firstMixedTest 0 firstCount = true)
    (next : ∀ j < secondCount, afterSecond (secondAt j) = false) :
    BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0
      (firstAt i).1 (firstAt i).2 = false := by
  have h := rangeCheck_at ready hi
  simp only [readyForSecond, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hvalid, htwo, hsmall⟩ := h
  refine afterFirst_false (firstAt i) htwo hsmall (boolOfNeg (rangeCheck_at mixed hi)) ?_
  refine pureAt_of_covered 12 (firstAt i) afterSecond (taggedMissing (secondSuccessors i) secondAt) (boolOfNeg hc) ?_
  intro z v found
  obtain ⟨j, hj, eq⟩ := taggedMissing_found found
  rw [eq]
  have hj' : j % 2048 < secondCount := of_decide_eq_true (List.all_eq_true.mp hvalid j hj)
  exact next _ hj'


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk0 : rangeCheck readyForSecond 0 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk1 : rangeCheck readyForSecond 8 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverageChunk2 : rangeCheck readyForSecond 16 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstCoverage_all : rangeCheck readyForSecond 0 24 = true :=
  (@rangeCheck_append readyForSecond 0 8 16 firstCoverageChunk0 (@rangeCheck_append readyForSecond 8 8 8 firstCoverageChunk1 firstCoverageChunk2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk0 : rangeCheck firstMixedTest 0 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk1 : rangeCheck firstMixedTest 8 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixedChunk2 : rangeCheck firstMixedTest 16 8 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma firstMixed_all : rangeCheck firstMixedTest 0 24 = true :=
  (@rangeCheck_append firstMixedTest 0 8 16 firstMixedChunk0 (@rangeCheck_append firstMixedTest 8 8 8 firstMixedChunk1 firstMixedChunk2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk0 : rangeCheck readyForThird 0 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk1 : rangeCheck readyForThird 16 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk2 : rangeCheck readyForThird 32 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk3 : rangeCheck readyForThird 48 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk4 : rangeCheck readyForThird 64 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk5 : rangeCheck readyForThird 80 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk6 : rangeCheck readyForThird 96 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk7 : rangeCheck readyForThird 112 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk8 : rangeCheck readyForThird 128 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk9 : rangeCheck readyForThird 144 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk10 : rangeCheck readyForThird 160 16 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverageChunk11 : rangeCheck readyForThird 176 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondCoverage_all : rangeCheck readyForThird 0 181 = true :=
  (@rangeCheck_append readyForThird 0 96 85 (@rangeCheck_append readyForThird 0 48 48 (@rangeCheck_append readyForThird 0 16 32 secondCoverageChunk0 (@rangeCheck_append readyForThird 16 16 16 secondCoverageChunk1 secondCoverageChunk2)) (@rangeCheck_append readyForThird 48 16 32 secondCoverageChunk3 (@rangeCheck_append readyForThird 64 16 16 secondCoverageChunk4 secondCoverageChunk5))) (@rangeCheck_append readyForThird 96 48 37 (@rangeCheck_append readyForThird 96 16 32 secondCoverageChunk6 (@rangeCheck_append readyForThird 112 16 16 secondCoverageChunk7 secondCoverageChunk8)) (@rangeCheck_append readyForThird 144 16 21 secondCoverageChunk9 (@rangeCheck_append readyForThird 160 16 5 secondCoverageChunk10 secondCoverageChunk11))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk0 : rangeCheck secondMixedTest 0 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk1 : rangeCheck secondMixedTest 24 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk2 : rangeCheck secondMixedTest 48 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk3 : rangeCheck secondMixedTest 72 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk4 : rangeCheck secondMixedTest 96 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk5 : rangeCheck secondMixedTest 120 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk6 : rangeCheck secondMixedTest 144 24 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixedChunk7 : rangeCheck secondMixedTest 168 13 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma secondMixed_all : rangeCheck secondMixedTest 0 181 = true :=
  (@rangeCheck_append secondMixedTest 0 96 85 (@rangeCheck_append secondMixedTest 0 48 48 (@rangeCheck_append secondMixedTest 0 24 24 secondMixedChunk0 secondMixedChunk1) (@rangeCheck_append secondMixedTest 48 24 24 secondMixedChunk2 secondMixedChunk3)) (@rangeCheck_append secondMixedTest 96 48 37 (@rangeCheck_append secondMixedTest 96 24 24 secondMixedChunk4 secondMixedChunk5) (@rangeCheck_append secondMixedTest 144 24 13 secondMixedChunk6 secondMixedChunk7)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk0 : rangeCheck thirdTest 0 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk1 : rangeCheck thirdTest 28 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk2 : rangeCheck thirdTest 56 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk3 : rangeCheck thirdTest 84 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk4 : rangeCheck thirdTest 112 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk5 : rangeCheck thirdTest 140 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk6 : rangeCheck thirdTest 168 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk7 : rangeCheck thirdTest 196 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk8 : rangeCheck thirdTest 224 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk9 : rangeCheck thirdTest 252 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk10 : rangeCheck thirdTest 280 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk11 : rangeCheck thirdTest 308 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk12 : rangeCheck thirdTest 336 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk13 : rangeCheck thirdTest 364 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk14 : rangeCheck thirdTest 392 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk15 : rangeCheck thirdTest 420 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk16 : rangeCheck thirdTest 448 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk17 : rangeCheck thirdTest 476 28 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTailChunk18 : rangeCheck thirdTest 504 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma thirdTail_all : rangeCheck thirdTest 0 506 = true :=
  (@rangeCheck_append thirdTest 0 252 254 (@rangeCheck_append thirdTest 0 112 140 (@rangeCheck_append thirdTest 0 56 56 (@rangeCheck_append thirdTest 0 28 28 thirdTailChunk0 thirdTailChunk1) (@rangeCheck_append thirdTest 56 28 28 thirdTailChunk2 thirdTailChunk3)) (@rangeCheck_append thirdTest 112 56 84 (@rangeCheck_append thirdTest 112 28 28 thirdTailChunk4 thirdTailChunk5) (@rangeCheck_append thirdTest 168 28 56 thirdTailChunk6 (@rangeCheck_append thirdTest 196 28 28 thirdTailChunk7 thirdTailChunk8)))) (@rangeCheck_append thirdTest 252 140 114 (@rangeCheck_append thirdTest 252 56 84 (@rangeCheck_append thirdTest 252 28 28 thirdTailChunk9 thirdTailChunk10) (@rangeCheck_append thirdTest 308 28 56 thirdTailChunk11 (@rangeCheck_append thirdTest 336 28 28 thirdTailChunk12 thirdTailChunk13))) (@rangeCheck_append thirdTest 392 56 58 (@rangeCheck_append thirdTest 392 28 28 thirdTailChunk14 thirdTailChunk15) (@rangeCheck_append thirdTest 448 28 30 thirdTailChunk16 (@rangeCheck_append thirdTest 476 28 2 thirdTailChunk17 thirdTailChunk18)))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initialCoverage (kind : Bool) : initialBinary FF kind (frontierMissing (initialStates kind)) = false := by
  cases kind <;> decide +kernel

lemma binaryCertificate (kind : Bool) :
    initialBinary FF kind (BinarySearch.look1 I.AA rootPreparedMask rootPreparedSlots 13 13 12 0) = false := by
  apply initialBinary_from_frontier FF kind (initialStates kind) (initialCoverage kind)
  intro state membership
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp membership
  have hi' : i < firstCount := of_decide_eq_true (List.all_eq_true.mp (allInitialIndices kind) i hi)
  exact checkedAfterFirst i hi' firstCoverage_all firstMixed_all
    (fun j hj => checkedAfterSecond j hj secondCoverage_all secondMixed_all thirdTail_all)

lemma binaryChecked : BinarySearch.chk [] gradeRootBounds 0 13 0 FF 0 = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  obtain ⟨b,hb⟩ := initialBinary_of_check h
  exact Bool.noConfusion ((binaryCertificate (cvOp b)).symm.trans hb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma unaryChecked : BinarySearch.chk [] gradeRootBounds 0 13 0 0 1 = false := by decide +kernel

lemma rootChecked (p : ℕ × ℕ) (hp : p ∈ binaryRootCases) :
    BinarySearch.chk [] gradeRootBounds 0 13 0 p.1 p.2 = false := by
  simp only [binaryRootCases, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact binaryChecked
  · exact unaryChecked

end Monotone

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x2Pair : Lg I.NN (mz 0) (tz 0) 210 := by
  unfold Lg
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x2Region : mz 4 &&& mz 0 = mz 4 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x2Target : tz 4 ≠ 0 ∧ tz 4 ≠ mz 4 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x2SeparatorsKilled : (rawL []).all (fun w =>
    !(sepb I.NN true (w &&& mz 0) 210) || Nat.beq ((w &&& mz 0) &&& mz 4) 0) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x2SeparatorConstant {x : ℕ} (hin : x ∈ C (mz 0) (WZ [] 0))
    (hsep : sepb I.NN true x 210 = true) : Cst (mz 4) x := by
  rcases hin with h | h
  · obtain ⟨w, hw, rfl⟩ := h
    have hz := List.all_eq_true.mp x2SeparatorsKilled w hw
    simp only [hsep, Bool.not_true, Bool.false_or] at hz
    exact Or.inl (Nat.eq_of_beq_eq_true hz)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl
    · exact Or.inl (by simp)
    · exact Or.inr (by rw [Nat.and_comm, x2Region])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma x2ProjectedInputs {S : Finset ℕ} (hs : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0)) :
    C (mz 4) (Im (mz 4) S) ⊆ C (mz 4) (WZ [] 4) := by
  rintro x (⟨word, hw, rfl⟩ | hx)
  · rcases hs hw with h | h
    · obtain ⟨w, input, rfl⟩ := h
      exact Or.inl ⟨w, input, by
        change (w &&& mz 0) &&& mz 4 = w &&& mz 4
        rw [Nat.and_assoc, Nat.and_comm (mz 0), x2Region]⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl
      · exact Or.inr (by simp)
      · apply Or.inr
        change mz 0 &&& mz 4 ∈ ({0, mz 4} : Set ℕ)
        rw [Nat.and_comm, x2Region]
        exact Set.mem_insert_of_mem _ rfl
  · exact Or.inr hx

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lower13 : Imp [] 0 13 := by
  intro q hq solution
  classical
  let existsSol : ∃ n, Sol Z0 (mz 0) (tz 0) n (C (mz 0) (WZ [] 0)) := ⟨q, solution⟩
  obtain ⟨k, hk, t, S, hS, live⟩ := (Nat.find_spec existsSol).live
  have leSize := le_trans hk (Nat.find_min' existsSol solution)
  have ambient : C (mz 0) (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have minimal : Min Z0 (mz 0) (tz 0) k t S :=
    ⟨live, fun n hn smaller => Nat.find_min existsSol (lt_of_lt_of_le hn hk) (smaller.mono le_rfl ambient)⟩
  obtain ⟨wire, hwire, separated⟩ := live.cov x2Pair.1 x2Pair.2.1 x2Pair.2.2.1 x2Pair.2.2.2
  have constant := x2SeparatorConstant (hS hwire) (sepb_weak (pos' t) separated)
  have killed : 0 < (S.filter (Cst (mz 4))).card :=
    Finset.card_pos.mpr ⟨wire, Finset.mem_filter.mpr ⟨hwire, constant⟩⟩
  obtain ⟨n, leaner, solved⟩ := minimal.const x2Region
    (by rw [tz_sub x2Region]; exact x2Target.1) (by rw [tz_sub x2Region]; exact x2Target.2)
  rw [tz_sub x2Region] at solved
  exact strongRows_sound (4,12) (by decide) n (by omega) (solved.mono le_rfl (x2ProjectedInputs hS))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootInputs {k t : ℕ} {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) k t S)
    (hmin : ∀ q < k, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0))) :
    (S : Set ℕ) ⊆ WZ [] 0 := by
  have hm : Min Z0 (mz 0) (tz 0) k t S :=
    ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl fun _ h => h.elim (fun hs => hS hs) Or.inr)⟩
  have hmasks : ∀ x ∈ S, x &&& mz 0 = x := by
    intro x hx
    rcases hS hx with ⟨x, _, rfl⟩ | e
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at e
      rcases e with rfl | rfl <;> simp
  have ht : tz 0 &&& mz 0 = tz 0 := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  obtain ⟨hzero, hone⟩ := hm.proper ht (by decide +kernel) (by decide +kernel) hmasks
  intro x hx
  rcases hS hx with h | h
  · exact h
  · simp at h
    rcases h with rfl | rfl
    · exact (hzero hx).elim
    · exact (hone hx).elim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma totalPos (t : ℕ) (hpos : 2 ≤ t) (hlt : t < 14) :
    chk [] totalRootBounds 0 13 t FF 1 = false := by
  interval_cases t <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma rootBounds_same : gradeRootBounds = totalRootBounds := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradeZero_sound : ∀ e ∈ gradeRootBounds, HasGrade 0 e := by
  intro e he
  rw [rootBounds_same] at he
  rcases e with ⟨z,k⟩
  simpa using gradeWeak (t := 0) (totalRootBounds_sound (z,k) he)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma gradedThirteenOne : BinarySearch.chk [] gradeRootBounds 0 13 1 FF 1 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lower14 : Imp [] 0 14 := by
  intro q hq solution
  obtain ⟨k, hk, t, S, hS, live⟩ := solution.live
  have ambient : C (mz 0) (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have size : k = 13 := by
    by_contra small
    exact lower13 k (by omega) (live.sol.mono le_rfl hS)
  subst k
  have hm : ∀ u < 13, ¬ Sol Z0 (mz 0) (tz 0) u (C (mz 0) (WZ [] 0)) := fun u hu => lower13 u hu
  have inputs := rootInputs hS live hm
  have minimum : Min Z0 (mz 0) (tz 0) 13 t S :=
    ⟨live, fun u hu smaller => hm u hu (smaller.mono le_rfl ambient)⟩
  have ht := minimum.size.2
  by_cases z : t = 0
  · subst t
    exact BinarySearch.rejectMinimum (L := 14) gradeRoot_p (by decide) (by decide)
      gradeZero_sound inputs live hm binaryRootCases binaryRootFull Monotone.rootChecked
  by_cases u : t = 1
  · subst t
    refine BinarySearch.rejectMinimum (L := 14) gradeRoot_p (by decide) (by decide)
      gradeRootBounds_sound inputs live hm [(FF,1)] ffull ?_
    intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact gradedThirteenOne
  refine imp_of_live (L := 14) (Or.inl rfl) totalRoot_p (by decide) totalRootBounds_sound
    (by decide) hS live hm (Or.inr ?_)
  refine ⟨[(FF,1)], ffull, ?_⟩
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact totalPos t (by omega) (by omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma needs15 {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 14 1 S) : False := by
  have hmin : ∀ q < 14, ¬ Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => lower14 q hq
  have hs' := rootInputs hS hl hmin
  refine BinarySearch.rejectMinimum (L := 15) gradeRoot_p (by decide) (by decide)
    gradeRootBounds_sound hs' hl hmin binaryRootCases binaryRootFull binaryRootChecked


lemma onFinal : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
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
end PEqualNP.Outside.L_meta_35928_aux

theorem PEqualNP.Outside.L_meta_35928 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 1, 5, 3, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_35928_aux.onFinal
