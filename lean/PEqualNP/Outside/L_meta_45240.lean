import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45240
def bigNat_0 : Nat := 0xfffeffff7fff7fffbfffbfff7ffedb7fff7ffebfff57edbf7effd5ff7ffbffdfdfdb6dbfffbfffbfefeafffebfffbfeffffbfffdfefdffff0000000000000000
def bigNat_1 : Nat := 0x800400202024924000400040101500014000401000040002010200000000000000000000
def bigNat_2 : Nat := 0x1000100008000800040004000800124800080014000a8124081002a00000000000000000000000000000000000000000000000000000000000000000000000000
def bigNat_3 : Nat := 0xffff00000000fffc060000000000000fc07e01ff880012209104841209090209420942002438090e084244a09150440848d4000000000000000026ee2b7715bb16dd8af78af71dee4b05ef05ee82f75764b72e1dd43b0000001fc01b0d80003fffbfe00afffebfffbfe00003fffdfefdffffaddddfdf56eeefef
def bigNat_4 : Nat := 0xfffe000000007ffe0000300000fffc7ffe200300fc00200024c12609098442125c121c1284c4494112601384994126209830932800000000000000005b36559b2ecd2b66954b974b2696993a373b361d5b11a98b5662d4c50003ffc01fc361bfff80003fefe2000080003feffff80001fefdffff36eeeaef9b777577
def bigNat_5 : Nat := 0x1fffe000000007fff0000000180fffe00007ffe801800fdff800049624b1212a09024ae24ae240950924924b225092a624ab121f9253000000000000000009d589eae4b564dab279d259c4b38d25f5a5e582f6e42cd1c7cb7816e7ff800001fd86c3fffbfff800fe80000bfff800ffffbfffc00fc0000c7777375e3bbb9ba
def bigNat_6 : Nat := 0x1fffc0000000000007fff7ffefffc00fffefffd0000001b7e000000008f847c23a300db473047304711951f9047c44611f3847cc3fcc23e400000000000000000e19ce0cc706670333e2e3e2e7c5c00639c639cb18c04cdae18cb01967ffbffdfc0006d80000000000feafffe0000000ffffbfffdfe000000f8787c79fc3c3e3c
def bigNat_7 : Nat := 0x1fffdfffefffeffff00000000000000fffefffd7ffeafc00000000000f1c78e3c3fb60078387838781fd5e3e178f87fde3c078f023163c7800000000000000000f1e0f8f07c787e3c3830383070600073e073e0b9f057003000cc01987ffbffdfdfdb0000000000000feafffebfffbfe00000000000000000ff807f81ffc03fc0
def bigNat_8 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb600000000000000000000000000fe07f03fbc36db7fc07fc07fde01fc007f00781fc007f003c183f8000000000000000000fe00ff007f807fc03fc03fc07f80db7c007c003e0000000060f001e07ffbffdfdfdb6dbfffbfffbfe0000000000000000000000000000000ffff8001ffffc000
def bigNat_9 : Nat := 0xfffeffff7fff7fffbfffbfff7ffedb7fff7ffebfff57edbf7effd5ff7ffbffdfdfdb6dbfffbfffbfefeafffebfffbfeffffbfffdfefdffffffffffffffffffff
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
inductive SolB (m T : ℕ) : ℕ → ℕ → Set ℕ → Prop
  | done {q u : ℕ} {S : Set ℕ} : T ∈ S → SolB m T q u S
  | un {q u : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → SolB m T q u (insert (a ^^^ m) S) → SolB m T q (u + 1) S
  | bi {q u : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → SolB m T q u (insert (op d a b) S) → SolB m T (q + 1) u S
lemma SolB.mono {m T q u : ℕ} {S : Set ℕ} (h : SolB m T q u S) :
    ∀ {q' u' : ℕ} {S' : Set ℕ}, q ≤ q' → u ≤ u' → S ⊆ S' → SolB m T q' u' S' := by
  induction h with
  | done h => intro q' u' S' _ _ hs; exact .done (hs h)
  | un h _ ih =>
    intro q' u' S' hq hu hs
    obtain ⟨r, rfl⟩ : ∃ r, u' = r + 1 := ⟨u' - 1, by omega⟩
    exact .un (hs h) (ih hq (by omega) (Set.insert_subset_insert hs))
  | bi h1 h2 _ ih =>
    intro q' u' S' hq hu hs
    obtain ⟨r, rfl⟩ : ∃ r, q' = r + 1 := ⟨q' - 1, by omega⟩
    exact .bi (hs h1) (hs h2) (ih (by omega) hu (Set.insert_subset_insert hs))
lemma SolB.sol {m T q u : ℕ} {S : Set ℕ} (h : SolB m T q u S) : Sol Z0 m T (q + u) S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 _ ih => rw [Nat.add_right_comm]; exact .bi h1 h2 (al0 _ _ _) ih
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
lemma SolB.live {m T q u : ℕ} {S : Set ℕ} (h : SolB m T q u S) :
    ∃ k ≤ q, ∃ t ≤ u, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live Z0 m T (k + t) t S0 := by
  induction h with
  | @done q u S h => exact ⟨0, by omega, 0, by omega, {T}, by simpa using h, .stop⟩
  | @un q u S a ha _ ih =>
    obtain ⟨k, hk, t, ht, S1, hs, hl⟩ := ih
    by_cases hg : a ^^^ m ∈ S1
    · refine ⟨k, hk, t + 1, by omega, insert a (S1.erase (a ^^^ m)), ?_, .un (by rwa [Finset.insert_erase hg])⟩
      intro x hx
      simp at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact ha
      · exact (hs h1).resolve_left h2
    · exact ⟨k, hk, t, by omega, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
  | @bi q u S d a b ha hb _ ih =>
    obtain ⟨k, hk, t, ht, S1, hs, hl⟩ := ih
    by_cases hg : op d a b ∈ S1
    · by_cases hab : a = b
      · subst hab; rw [op_self] at hs
        exact ⟨k, by omega, t, ht, S1, fun x hx => (hs hx).elim (fun e => e ▸ ha) id, hl⟩
      refine ⟨k + 1, by omega, t, ht, insert a (insert b (S1.erase (op d a b))), ?_, ?_⟩
      · intro x hx
        simp at hx
        rcases hx with rfl | rfl | ⟨h1, h2⟩
        · exact ha
        · exact hb
        · exact (hs h1).resolve_left h2
      · rw [Nat.add_right_comm]; exact .bi hab (al0 _ _ _) (by rwa [Finset.insert_erase hg])
    · exact ⟨k, by omega, t, ht, S1, fun x hx => (hs hx).resolve_left (fun e => hg (e ▸ hx)), hl⟩
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
lemma Un.imB {a q u : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : SolB n (T &&& n) q u (C n (Im n S'))) :
    SolB n (T &&& n) q (u + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.imB {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hs : SolB n (T &&& n) q u (C n (Im n S'))) :
    SolB n (T &&& n) (q + 1) u (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (hs.mono le_rfl le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
omit hn in
lemma Bi.killB {a b q u : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi R d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : SolB n (T &&& n) q u (C n (Im n S'))) : SolB n (T &&& n) q u (C n (Im n S)) :=
  hs.mono le_rfl le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.constB (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min R m T k t S) :
    ∃ q, q + t + (S.filter (Cst n)).card ≤ k ∧ SolB n (T &&& n) q t (C n (Im n S)) := by
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
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    refine ⟨q, ?_, hu.imB hn hs⟩
    by_cases hc : Cst n a
    · rw [Finset.filter_insert, ite_eq_left ((Cst_neg hn).2 hc), Finset.card_insert_of_notMem (by simp [hf])] at hq
      rw [Finset.filter_insert, ite_eq_left hc]
      have := Finset.card_insert_le a (U.filter (Cst n)); omega
    · have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
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
    · refine ⟨q, ?_, hu.killB (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.killB (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.imB hs⟩
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
              have h1' : c1 = b ∨ c1 ∈ U := by simp at h1; clear * - h1 q1; tauto
              have h2' : c2 = b ∨ c2 ∈ U := by simp at h2; clear * - h2 q2; tauto
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
              have h1' : c1 = a ∨ c1 ∈ U := by simp at h1; clear * - h1 q1; tauto
              have h2' : c2 = a ∨ c2 ∈ U := by simp at h2; clear * - h2 q2; tauto
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
  deriving DecidableEq
structure X where
  w : W
  s : Nat
  q : Nat
  u : Nat
structure Cm where
  a : List Nat
  b : List Nat
def NN : Nat := 513
def AA : Nat := bigNat_0
def HX : Nat := bigNat_1
def HY : Nat := bigNat_2
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
  (List.rec (motive := fun _ => Bool) (false) (fun a _ ih => (Bool.rec (motive := fun _ => Bool) (ih) (true) ((Bool.rec (motive := fun _ => Bool) ((st (Nat.xor a.s m) (fun s => (st z (fun z => ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v => (Bool.rec (motive := fun _ => Bool) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))) (true) ((Bool.rec (motive := fun _ => Bool) (false) (child (f s) g (rm a.s a.s v) z) (Nat.ble n e)))))))))) (false) (Nat.beq (Nat.succ a.s) q))))) (r))
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wst (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twice d l v)
def uF (l o : Nat) (w : W) : Nat := Nat.land (sp false l w.s) o
def nbL (F : W → Nat) (w : W) (t : List W) : List W :=
  List.rec (motive := fun _ => List W) [] (fun x _ ih => Bool.rec (motive := fun _ => List W) ih (x :: ih) (hit (F w) (F x))) t
def eA (U : W → Nat) (u : Nat) (nb : List W) (el : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) el (fun x _ jh => Nat.lor u (U x) :: jh) nb
def eL (F U : W → Nat) (v : List W) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w t ih => eA U (U w) (nbL F w t) ih) v
def tB (F U : W → Nat) (u : Nat) (x : W) (r : List W) (tl : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) tl (fun y _ jh => Bool.rec (motive := fun _ => List Nat) jh
    (Nat.lor u (Nat.lor (U x) (U y)) :: jh) (hit (F x) (F y))) r
def tA (F U : W → Nat) (u : Nat) (nb : List W) (tl : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) tl (fun x r ih => tB F U u x r ih) nb
def tL (F U : W → Nat) (v : List W) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w t ih => tA F U (U w) (nbL F w t) ih) v
def avoid (q : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun m _ ih => Bool.rec (motive := fun _ => Bool) ih true (Nat.beq (Nat.land m q) 0)) L
def pen (l o : Nat) (v : List W) (a c : W) : Nat :=
  (fun q => Bool.rec (motive := fun _ => Nat) (Bool.rec (motive := fun _ => Nat) 0 1 (avoid q (eL (flag false l o) (uF l o) v))) 2
    (avoid q (tL (flag false l o) (uF l o) v))) (Nat.lor (uF l o a) (uF l o c))
def modeB (n e : Nat) (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : W) (da dc s x y : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) (f0 h a c da dc s x y)
    (Bool.rec (motive := fun _ => Bool) (f1 h a c da dc s x y) (h a c da dc s x y) (Nat.ble (Nat.succ n) e)) (Nat.ble n e)
def hP (f : Nat → List W → Bool) (l m g e n z o : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  st (Nat.sub e (pen l o v a c)) (fun e' => modeB n e' (mid f m g e' (Nat.pred n) z v) a c da dc s x y)
def node (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (X → X → Bool) → List X → Bool) : Bool :=
  (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 (mid f m g e (Nat.pred n) z v))) xs)
    (go (pair (hP f l m g e n z (wst d l v) v)) xs) (Nat.ble n e))
    (mkX d l (wst d l v) v)
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
def segsX : List (ℕ × ℕ) := [(63,81), (81,88), (88,97), (97,114), (114,132), (132,142), (142,158), (158,160), (160,176), (176,178), (178,180), (180,188), (188,198), (198,214), (214,230), (230,233), (233,236), (236,239), (239,242), (242,245), (245,253), (253,261), (261,274), (274,287)]
def segsY : List (ℕ × ℕ) := [(287,297), (297,299), (299,301), (301,312), (312,319), (319,326), (326,329), (329,332), (332,339), (339,341), (341,343), (343,358), (358,360), (360,375), (375,391), (391,394), (394,397), (397,400), (400,415), (415,430), (430,446), (446,463), (463,479), (479,496), (496,512)]
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
def Cl (P : List ℕ) (T k t : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop := ∀ j < P.length, ∀ q, q + t + b j < k →
  ¬ SolB (P.getD j 0) (T &&& P.getD j 0) q t (C (P.getD j 0) (Im (P.getD j 0) S))
structure StOk (P : List ℕ) (T l k t z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k t b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg NN m T i ∧ AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ} (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w)
    (hc : Cl P T k t b S) (hm : Min R m T k' t S) (hk : k' ≤ k) : ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  obtain ⟨q, hq, hs⟩ := hm.constB p1 p2 p3
  have hqb : ¬ q + t + b j < k := fun h => hc j hj q h hs
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
    intro j hj q hq hsol
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
    · refine hcl j hj q ?_ (hb.killB (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
      have : 1 ≤ max (fl a j) (fl c j) := by
        rcases hkill with h | h <;> simp [fl, h]
      have := fl_le a j; have := fl_le c j; omega
    · push Not at hkill
      refine hcl j hj (q + 1) ?_ (hb.imB hsol)
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
lemma modeB_eq (n e : ℕ) (h : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool) (a c : W) (da dc s x y : ℕ) :
    modeB n e h a c da dc s x y = modeF n e h a c da dc s x y := by
  unfold modeB modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma hP_eq (f : ℕ → List W → Bool) (l m g e n z o : ℕ) (v : List W) (a c : W) (da dc s x y : ℕ) :
    hP f l m g e n z o v a c da dc s x y =
      modeF n (e - pen l o v a c) (mid f m g (e - pen l o v a c) (Nat.pred n) z v) a c da dc s x y := by
  unfold hP; rw [st_eq, modeB_eq]; rfl
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (X → X → Bool) → List X → Bool) :
    node f d l m g e n z v go = bif Nat.ble n e then go (pair (hP f l m g e n z (wst d l v) v)) (v.map (mkx d l (wst d l v)))
      else go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node modeF
  cases Nat.ble n e <;> rfl
lemma pair_congr {h h' : W → W → ℕ → ℕ → ℕ → ℕ → ℕ → Bool} {d : Bool} {l o : ℕ} {a c : W}
    (hh : ∀ da dc s x y, h a c da dc s x y = h' a c da dc s x y) :
    pair h (mkx d l o a) (mkx d l o c) = pair h' (mkx d l o a) (mkx d l o c) := by
  simp only [pair, mkx, hh]
lemma avoid_true {q : ℕ} : ∀ {L : List ℕ}, avoid q L = true → ∃ e ∈ L, e &&& q = 0 := by
  intro L
  induction L with
  | nil => intro h; exact Bool.noConfusion h
  | cons e L ih =>
    intro h
    change (Bool.rec (motive := fun _ => Bool) (avoid q L) true (Nat.beq (Nat.land e q) 0) : Bool) = true at h
    rw [bR] at h
    cases h1 : Nat.beq (Nat.land e q) 0 with
    | true => exact ⟨e, by simp, Nat.eq_of_beq_eq_true h1⟩
    | false =>
      rw [h1, cond_false] at h
      obtain ⟨e', he', h'⟩ := ih h
      exact ⟨e', by simp [he'], h'⟩
lemma nbL_cons (F : W → ℕ) (w y : W) (t : List W) : nbL F w (y :: t) =
    bif hit (F w) (F y) then y :: nbL F w t else nbL F w t := by
  show (Bool.rec (motive := fun _ => List W) (nbL F w t) (y :: nbL F w t) (hit (F w) (F y)) : List W) = _
  cases hit (F w) (F y) <;> rfl
lemma nbL_sub (F : W → ℕ) (w : W) : ∀ t : List W, (nbL F w t).Sublist t := by
  intro t
  induction t with
  | nil => exact List.Sublist.slnil
  | cons y t ih =>
    rw [nbL_cons]
    cases hit (F w) (F y)
    · exact ih.cons _
    · exact ih.cons₂ _
lemma nbL_hit {F : W → ℕ} {w x : W} : ∀ {t : List W}, x ∈ nbL F w t → hit (F w) (F x) = true := by
  intro t
  induction t with
  | nil => intro h; exact absurd h (List.not_mem_nil)
  | cons y t ih =>
    intro h
    rw [nbL_cons] at h
    cases h1 : hit (F w) (F y) with
    | false => rw [h1, cond_false] at h; exact ih h
    | true =>
      rw [h1, cond_true] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact h1
      · exact ih h
lemma eA_mem {U : W → ℕ} {u : ℕ} {el : List ℕ} {e : ℕ} : ∀ {nb : List W}, e ∈ eA U u nb el → (∃ x ∈ nb, e = u ||| U x) ∨ e ∈ el := by
  intro nb
  induction nb with
  | nil => intro h; exact Or.inr h
  | cons y nb ih =>
    intro h
    change e ∈ (Nat.lor u (U y)) :: eA U u nb el at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl ⟨y, by simp, rfl⟩
    · rcases ih h with ⟨x, hx, rfl⟩ | h
      · exact Or.inl ⟨x, by simp [hx], rfl⟩
      · exact Or.inr h
lemma eL_mem {F U : W → ℕ} {e : ℕ} : ∀ {v : List W}, e ∈ eL F U v → ∃ w1 w2, [w1, w2].Sublist v ∧
    hit (F w1) (F w2) = true ∧ e = U w1 ||| U w2 := by
  intro v
  induction v with
  | nil => intro h; exact absurd h (List.not_mem_nil)
  | cons w t ih =>
    intro h
    change e ∈ eA U (U w) (nbL F w t) (eL F U t) at h
    rcases eA_mem h with ⟨x, hx, rfl⟩ | h
    · exact ⟨w, x, (List.singleton_sublist.2 ((nbL_sub F w t).subset hx)).cons₂ _, nbL_hit hx, rfl⟩
    · obtain ⟨w1, w2, h1, h2, h3⟩ := ih h
      exact ⟨w1, w2, h1.cons _, h2, h3⟩
lemma tB_cons (F U : W → ℕ) (u : ℕ) (x y : W) (r : List W) (tl : List ℕ) : tB F U u x (y :: r) tl =
    bif hit (F x) (F y) then (u ||| (U x ||| U y)) :: tB F U u x r tl else tB F U u x r tl := by
  show (Bool.rec (motive := fun _ => List ℕ) (tB F U u x r tl) (Nat.lor u (Nat.lor (U x) (U y)) :: tB F U u x r tl)
    (hit (F x) (F y)) : List ℕ) = _
  cases hit (F x) (F y) <;> rfl
lemma tB_mem {F U : W → ℕ} {u : ℕ} {x : W} {tl : List ℕ} {e : ℕ} : ∀ {r : List W}, e ∈ tB F U u x r tl →
    (∃ y ∈ r, hit (F x) (F y) = true ∧ e = u ||| (U x ||| U y)) ∨ e ∈ tl := by
  intro r
  induction r with
  | nil => intro h; exact Or.inr h
  | cons y r ih =>
    intro h
    rw [tB_cons] at h
    cases h1 : hit (F x) (F y) with
    | false =>
      rw [h1, cond_false] at h
      rcases ih h with ⟨y', hy', q⟩ | h
      · exact Or.inl ⟨y', by simp [hy'], q⟩
      · exact Or.inr h
    | true =>
      rw [h1, cond_true] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl ⟨y, by simp, h1, rfl⟩
      · rcases ih h with ⟨y', hy', q⟩ | h
        · exact Or.inl ⟨y', by simp [hy'], q⟩
        · exact Or.inr h
lemma tA_mem {F U : W → ℕ} {u : ℕ} {tl : List ℕ} {e : ℕ} : ∀ {nb : List W}, e ∈ tA F U u nb tl →
    (∃ x y, [x, y].Sublist nb ∧ hit (F x) (F y) = true ∧ e = u ||| (U x ||| U y)) ∨ e ∈ tl := by
  intro nb
  induction nb with
  | nil => intro h; exact Or.inr h
  | cons x r ih =>
    intro h
    change e ∈ tB F U u x r (tA F U u r tl) at h
    rcases tB_mem h with ⟨y, hy, q1, q2⟩ | h
    · exact Or.inl ⟨x, y, (List.singleton_sublist.2 hy).cons₂ _, q1, q2⟩
    · rcases ih h with ⟨x', y', q0, q1, q2⟩ | h
      · exact Or.inl ⟨x', y', q0.cons _, q1, q2⟩
      · exact Or.inr h
lemma tL_mem {F U : W → ℕ} {e : ℕ} : ∀ {v : List W}, e ∈ tL F U v → ∃ w1 w2 w3, [w1, w2, w3].Sublist v ∧
    hit (F w1) (F w2) = true ∧ hit (F w1) (F w3) = true ∧ hit (F w2) (F w3) = true ∧ e = U w1 ||| (U w2 ||| U w3) := by
  intro v
  induction v with
  | nil => intro h; exact absurd h (List.not_mem_nil)
  | cons w t ih =>
    intro h
    change e ∈ tA F U (U w) (nbL F w t) (tL F U t) at h
    rcases tA_mem h with ⟨x, y, q0, q1, q2⟩ | h
    · have hx : x ∈ nbL F w t := q0.subset (by simp)
      have hy : y ∈ nbL F w t := q0.subset (by simp)
      exact ⟨w, x, y, (q0.trans (nbL_sub F w t)).cons₂ _, nbL_hit hx, nbL_hit hy, q1, q2⟩
    · obtain ⟨w1, w2, w3, h1, h2⟩ := ih h
      exact ⟨w1, w2, w3, h1.cons _, h2⟩
lemma pen_eq (l o : ℕ) (v : List W) (a c : W) : pen l o v a c =
    bif avoid (uF l o a ||| uF l o c) (tL (flag false l o) (uF l o) v) then 2
      else bif avoid (uF l o a ||| uF l o c) (eL (flag false l o) (uF l o) v) then 1 else 0 := by
  show (Bool.rec (motive := fun _ => ℕ) (Bool.rec (motive := fun _ => ℕ) 0 1 (avoid (uF l o a ||| uF l o c) (eL (flag false l o) (uF l o) v))) 2
    (avoid (uF l o a ||| uF l o c) (tL (flag false l o) (uF l o) v)) : ℕ) = _
  cases avoid (uF l o a ||| uF l o c) (tL (flag false l o) (uF l o) v) <;>
    cases avoid (uF l o a ||| uF l o c) (eL (flag false l o) (uF l o) v) <;> rfl
lemma uF_avoid {l o e q : ℕ} {w b : W} (h0 : e &&& q = 0) (h1 : ∀ i, (uF l o w).testBit i = true → e.testBit i = true)
    (h2 : ∀ i, (uF l o b).testBit i = true → q.testBit i = true) (hne : uF l o w ≠ 0) : w.s ≠ b.s := by
  intro hs
  have hu : uF l o w = uF l o b := by unfold uF; rw [hs]
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hne
  have h3 := congrArg (fun x => x.testBit i) h0
  simp only [Nat.testBit_and, Nat.zero_testBit] at h3
  rw [h1 i hi, h2 i (hu ▸ hi)] at h3
  exact absurd h3 (by decide)
lemma eN_of {k t n y : ℕ} {Q : Prop} (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ Q)) : n ≤ k - t - y → k - t - y = k - t := by
  rcases hy with rfl | ⟨rfl, h1, _⟩ <;> intro h <;> omega
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
lemma hit_ht {k t z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l k t z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
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
lemma nk_ok {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hm : Min R m T k' t S)
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
      have h1' : p = b ∨ p ∈ U := by simp at hp; clear * - hp hpa; tauto
      have h2' : q = b ∨ q ∈ U := by simp at hq; clear * - hq hqa; tauto
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
  simp only [cv, bR, hcov, cond_true] at h
  cases hp : pos' t <;> rw [hp] at h <;> simpa using h
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
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
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
      · change (a.s ^^^ m).testBit (NN + i) = (a.s ^^^ m).testBit (NN + j)
        rw [Nat.testBit_xor, Nat.testBit_xor, hg.2 i j h h1 h2, (X.lg i h1).1.2.1, (X.lg j h2).1.2.1]
    · exact hs.good w h
  have hcl' : Cl P T k t b S' := fun j hj q hq hsol =>
    hcl j hj q (by omega) (hb.imB (X.hP j hj).1 hsol)
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, b, hb15, hcl', ?_⟩
  have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
    cases ka
    · simp [pk]
    · exact fl_pk wa
  rw [ea, hz, pk_sub]
  · refine pk_congr fun j hj => ?_
    have q2 := hle' j hj; have q5 := hcnt j
    cases ka <;> simp at q5 ⊢ <;> omega
  · intro j hj
    have q1 := hle j hj; have q6 := fl_le a j
    cases ka <;> simp <;> omega
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
  have : Std.Symm (fun a c : L_meta_45240.X => h a c = false ∨ h c a = false) := ⟨fun a b h => h.symm⟩
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
lemma hit_u {o : ℕ} {a b : W} (h : hit (flag false l o a) (flag false l o b) = true) : uF l o a ≠ 0 ∧ uF l o b ≠ 0 := by
  obtain ⟨⟨s, hs1, x1, x2⟩, _⟩ := hit_spec h
  have hu : ∀ w, ∀ i, (Nat.land (sp false l w) o).testBit i = true → AA.testBit i = true := by
    intro w i hi
    simp only [nl, Nat.testBit_and, sp_bit, Bool.and_eq_true] at hi
    exact (X.lg i hi.1.1).2
  obtain ⟨i1, _, _, a3⟩ := flag_seg segX_ok (hu a.s) hs1 x1
  obtain ⟨i2, _, _, b3⟩ := flag_seg segX_ok (hu b.s) hs1 x2
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have e' : Nat.land (sp false l a.s) o = 0 := e
    rw [e'] at a3; simp at a3
  · have e' : Nat.land (sp false l b.s) o = 0 := e
    rw [e'] at b3; simp at b3
lemma pen_card {t k k' z : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k)
    (hb : Bi R d' a.s c.s S S') (hl : Live R m T k' t S') :
    S'.card + t + pen l (wst (pos' t) l v) v a c ≤ k + 1 := by
  have hmin := hb.min hl hm.2
  obtain ⟨x, f, q1, q2, q3⟩ := chrom (N := NN) (e := pos' t) hl hmin.2 (by
    rcases Nat.eq_zero_or_pos t with h | h
    · exact Or.inr h
    · exact Or.inl (by simp [pos', h]))
  suffices hx : pen l (wst (pos' t) l v) v a c ≤ x by omega
  have key : ∀ {w1 w2 : W}, w1 ∈ v → w2 ∈ v → w1.s ≠ w2.s → w1.s ≠ a.s → w1.s ≠ c.s → w2.s ≠ a.s → w2.s ≠ c.s →
      hit (flag false l (wst (pos' t) l v) w1) (flag false l (wst (pos' t) l v) w2) = true →
      f w1.s ≠ f w2.s ∧ f w1.s ≤ x ∧ f w2.s ≤ x := by
    intro w1 w2 h1 h2 h12 h1a h1c h2a h2c hh
    have hH := hit_ht X hs h1 h2 hh
    have m1 := hs.rep.mem.2 ⟨w1, h1, rfl⟩
    have m2 := hs.rep.mem.2 ⟨w2, h2, rfl⟩
    obtain ⟨hab, U, rfl, rfl, hal⟩ := hb
    have hH' := ht_bi hab (Or.inr rfl) hl m1 m2 (fun e => absurd e h1a) (fun e => absurd e h1c) (fun e => absurd e h2a)
      (fun e => absurd e h2c) hH
    rw [if_neg (not_or.2 ⟨h1a, h1c⟩), if_neg (not_or.2 ⟨h2a, h2c⟩)] at hH'
    have n1 : w1.s ∈ insert (op d' a.s c.s) U := Finset.mem_insert_of_mem (by simpa [h1a, h1c] using m1)
    have n2 : w2.s ∈ insert (op d' a.s c.s) U := Finset.mem_insert_of_mem (by simpa [h2a, h2c] using m2)
    exact ⟨q3 _ n1 _ n2 h12 hH', q2 _ n1, q2 _ n2⟩
  have av : ∀ {e : ℕ} {w w' : W}, e &&& (uF l (wst (pos' t) l v) a ||| uF l (wst (pos' t) l v) c) = 0 →
      (∀ i, (uF l (wst (pos' t) l v) w).testBit i = true → e.testBit i = true) →
      (hit (flag false l (wst (pos' t) l v) w) (flag false l (wst (pos' t) l v) w') = true ∨
        hit (flag false l (wst (pos' t) l v) w') (flag false l (wst (pos' t) l v) w) = true) → w.s ≠ a.s ∧ w.s ≠ c.s := by
    intro e w w' h0 h1 hh
    have hne : uF l (wst (pos' t) l v) w ≠ 0 := hh.elim (fun h => (hit_u X h).1) (fun h => (hit_u X h).2)
    exact ⟨uF_avoid h0 h1 (fun i hi => by simp [hi]) hne, uF_avoid h0 h1 (fun i hi => by simp [hi]) hne⟩
  rw [pen_eq]
  cases ht : avoid (uF l (wst (pos' t) l v) a ||| uF l (wst (pos' t) l v) c) (tL (flag false l (wst (pos' t) l v)) (uF l (wst (pos' t) l v)) v) with
  | true =>
    rw [cond_true]
    obtain ⟨e, he, h0⟩ := avoid_true ht
    obtain ⟨w1, w2, w3, hsub, h12, h13, h23, rfl⟩ := tL_mem he
    have hnd := hs.rep.1.sublist (hsub.map W.s)
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true] at hnd
    obtain ⟨a1, c1⟩ := av h0 (fun i hi => by simp [hi]) (Or.inl h12)
    obtain ⟨a2, c2⟩ := av h0 (fun i hi => by simp [hi]) (Or.inr h12)
    obtain ⟨a3, c3⟩ := av h0 (fun i hi => by simp [hi]) (Or.inr h13)
    have m1 : w1 ∈ v := hsub.subset (by simp)
    have m2 : w2 ∈ v := hsub.subset (by simp)
    have m3 : w3 ∈ v := hsub.subset (by simp)
    have k12 := key m1 m2 hnd.1.1 a1 c1 a2 c2 h12
    have k13 := key m1 m3 hnd.1.2 a1 c1 a3 c3 h13
    have k23 := key m2 m3 hnd.2 a2 c2 a3 c3 h23
    omega
  | false =>
    rw [cond_false]
    cases he : avoid (uF l (wst (pos' t) l v) a ||| uF l (wst (pos' t) l v) c) (eL (flag false l (wst (pos' t) l v)) (uF l (wst (pos' t) l v)) v) with
    | false => exact Nat.zero_le _
    | true =>
      rw [cond_true]
      obtain ⟨e, he', h0⟩ := avoid_true he
      obtain ⟨w1, w2, hsub, h12, rfl⟩ := eL_mem he'
      have hnd := hs.rep.1.sublist (hsub.map W.s)
      simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
        List.nodup_nil, and_true, not_false_eq_true] at hnd
      obtain ⟨a1, c1⟩ := av h0 (fun i hi => by simp [hi]) (Or.inl h12)
      obtain ⟨a2, c2⟩ := av h0 (fun i hi => by simp [hi]) (Or.inr h12)
      have k12 := key (hsub.subset (by simp)) (hsub.subset (by simp)) hnd a1 c1 a2 c2 h12
      omega
lemma node_bi {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (L_meta_45240.X → L_meta_45240.X → Bool) → List L_meta_45240.X → Bool}
    (hs : StOk P T l (k + 1) t z v S) (hm : Min R m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (he : n ≤ e → e = k + 1 - t) (hb : Bi R d' x y S S') (hl : Live R m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  have main : (∃ e1, S'.card ≤ e1 ∧ pair (modeF n e1 (mid f m g e1 (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) ∨
      (∃ e1, S'.card ≤ e1 ∧ pair (modeF n e1 (mid f m g e1 (Nat.pred n) z v)) (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false) := by
    cases hne : Nat.ble n e with
    | false =>
      rw [hne, cond_false] at hp
      rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
      · exact Or.inl ⟨e, hSe, h⟩
      · exact Or.inr ⟨e, hSe, h⟩
    | true =>
      rw [hne, cond_true] at hp
      have e0 := he (Nat.le_of_ble_eq_true hne)
      subst hd
      rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
      · refine Or.inl ⟨e - pen l (wst (pos' t) l v) v a c, ?_, ?_⟩
        · have := pen_card X hs hm hk hb hl; omega
        · rw [← pair_congr (hP_eq f l m g e n z (wst (pos' t) l v) v a c)]; exact h
      · refine Or.inr ⟨e - pen l (wst (pos' t) l v) v c a, ?_, ?_⟩
        · have := pen_card X hs hm hk hb.symm hl; omega
        · rw [← pair_congr (hP_eq f l m g e n z (wst (pos' t) l v) v c a)]; exact h
  rcases main with ⟨e1, h1, h⟩ | ⟨e1, h1, h⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn h1 hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hs hm hk hd hn h1 hb.symm hl hc ha h
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
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) (eN_of hy) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem ha) (List.mem_map_of_mem hc) ?_ ?_
      · intro e
        have : a.s = c.s := congrArg L_meta_45240.X.s e
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
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) (eN_of hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
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
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hst2 hm2 (by omega) rfl rfl (NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2) (eN_of hy2) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
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
      · rw [eU]; ext z; simp only [Finset.mem_insert]; clear * - z; tauto
      · ext z; simp only [Finset.mem_insert]; clear * - z; tauto
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
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), f k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live Z0 m T k' t S → (∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live Z0 m T k' t S) (hmW : ∀ q < k', ¬ Sol Z0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK Z0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 → ∃ go : (L_meta_45240.X → L_meta_45240.X → Bool) → List L_meta_45240.X → Bool,
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
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1 hy) (eN_of hy) hb hl1 (fun h xs hp a c ha hc hax hcy hxs => by
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
    look1 l m g K fuel k t z v = false → StOk P T l k t z v S → (∀ w ∈ v, w.r = R w.s) →
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
      exact pairs_any hp (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_45240.X.s e))
end sound
def rawP : List ℕ := [bigNat_3, bigNat_4, bigNat_5, bigNat_6, bigNat_7, bigNat_8]
def xw (e : ℕ × ℕ) : ℕ := rawP.getD e.1 0 ||| rawP.getD e.2 0
def rawL (E : List (ℕ × ℕ)) : List ℕ := rawP ++ E.map xw
def six : List (ℕ × ℕ) := []
def rawG : List ℕ := rawL six
def FPM : ℕ := 2 ^ 64 - 1
def FULL : ℕ := 2 ^ NN - 1
def TG : ℕ := bigNat_9
def pinMasks : List ℕ := [0x26ee2b7715bb7fff8af78af77ffe4b05ef05ee82f757e4bf2effd43b0910489fc21b0d84813fffbfe10afffebfffbfe12253fffdfefdffffaddddfdf56eeefef, 0x5b36559b7fff2b66954bbfff2696993a377ffe3fff11a98b7e62d4c51263ffc49fc361bfff890e3fefe224a089303feffff89311fefdffff36eeeaef9b777577, 0x9d58ffff4b564dab3fffa59c4b38d27fff5e583fff42cd1c7effc16e7ff925891fd86c3fffbfff920fe84924bfff928ffffbfffc90fc9298c7777375e3bbb9ba, 0xfffee0cc706670333fffbfff7ffe007fff7ffeb18c04cdbf18cb01967ffbffdfd1806da3982398238feafffe23e2230ffffbfffdfe611f20f8787c79fc3c3e3c, 0xfffeffff7fff7fffb83038307060007fff7ffebfff57e03000cc01987ffbffdfdfdb003c1c3c1c3c0feafffebfffbfef1e03c78118b1e3c0ff807f81ffc03fc0, 0xfffeffff7fff7fffbfffbfff7ffedb7c007c003e0000000060f001e07ffbffdfdfdb6dbfffbfffbfef00fe003f803c0fe003f801e0c1fc00ffff8001ffffc000, 0x1ffffffffffffe9227fffffffe211fcfffffffffffff89fc8ffe23bfffffffffdbff6fb7ffffb5efb5fffede3fb78fbdfffffb757ddfbdb9552222020a9111010, 0x1ffffffffd132ffffffffe8b4ffffe7ffffc4c9e2a4effe7fa9ffefffffff6cfffb3ddef6d1fffff6bd9dffff7ffff63db35fffffb3e7b66bc911151064888a88, 0x1ffff6151ffffffffd862ffffffff3fa0a5ffffd091bff3ff83487fffdb4ffffff6afb7eda8eda8fffb57ffff6da6fffb6acedaa7ff03ffff38888c8a1c444645, 0x11e63ffffffffffffc1d1c1d183a3ff9c639c637ffffff251ffffffffb83dc1ee3fff927ffffffffff7357037fffffff7063dc19e01ffffff0787838603c3c1c3, 0x10e1f070f838781c3ffffffffffffff8c1f8c1f460fa8ffffffffffff871c38e1e024fffffffffffff0150e0f4383c01fffffffffffffffff007f807e003fc03f, 0x101ff00ff807f803fc03fc03f807f24ffffffffffffffffffffffffff80fc07e021e492401fc01fc01fffffffffffffffffffffffffffffff00007ffe00003fff]
def kz (Z : ℕ) : ℕ := (List.range 12).foldr (fun i x => bif Nat.testBit Z i then Nat.lor x (pinMasks.getD i 0) else x) 0
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
def MM : ℕ := 214
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
    have : Std.Symm (fun a b : L_meta_45240.X => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) :=
      ⟨fun a b h e => (h (by rw [Nat.add_comm]; exact e)).symm⟩
    exact (hpw.imp (S := fun a b => hb p.1 (a.s + b.s) = true → (h a b = false ∨ h b a = false)) fun h e => Or.inl (h e)).forall
      (fs_mem (List.mem_map_of_mem ha) har) (fs_mem (List.mem_map_of_mem hc) hcr) (fun e => hne (congrArg L_meta_45240.X.s e)) hpb
end sound
def WZ (E : List (ℕ × ℕ)) (Z : ℕ) : Set ℕ := {x | ∃ w ∈ rawL E, x = w &&& mz Z}
def Imp (E : List (ℕ × ℕ)) (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol Z0 (mz Z) (tz Z) q (C (mz Z) (WZ E Z))
def ImpB (E : List (ℕ × ℕ)) (Z L t : ℕ) : Prop := ∀ q, q + t < L → ¬ SolB (mz Z) (tz Z) q t (C (mz Z) (WZ E Z))
lemma Imp.toB {E : List (ℕ × ℕ)} {Z L : ℕ} (h : Imp E Z L) (t : ℕ) : ImpB E Z L t := fun q hq hs => h (q + t) hq hs.sol
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
    (hI : ∀ e ∈ Q, ImpB E e.1 e.2 t)
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
  have hno : ∀ e ∈ Q, ∀ q, q + t < e.2 → ¬ SolB (mz e.1) (tz Z &&& mz e.1) q t (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.constB h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
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
  have hcl : Cl (PZ Q) (tz Z) (L - 1) t (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + t + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
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
  have hno : ∀ e ∈ Q, ∀ q, q + t < e.2 → ¬ SolB (mz e.1) (tz Z &&& mz e.1) q t (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact (hI e he).toB t q hq (hs.mono le_rfl le_rfl (C_mono (Im_WZ h3 hSW)))
  have htk := hm.size.2
  rcases hb with ⟨e, he, hle⟩ | hb
  · have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.constB h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
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
  have hcl : Cl (PZ Q) (tz Z) (L - 1) t (fun j => L - 1 - (Q.getD j (0, L - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    have hq' : q + t + (L - 1 - (Q.getD j (0, L - 1)).2) < L - 1 := hq
    rw [e1]; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm (by omega)
  have hst : StOk (PZ Q) (tz Z) (lz Z) (L - 1) t (pL (Q.map fun e => 16 + (L - 1 - e.2)) - sumc v) v S := by
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
def rt3 : List (ℕ × ℕ) := [(1153,4), (98,4), (1281,4), (1537,4), (2561,4), (3073,4), (2562,4), (3074,4), (280,4), (2564,4), (3076,4), (304,4), (2072,4), (3080,4), (560,4), (2576,4)]
def rt2 : List (ℕ × ℕ) := [(129,5), (66,5), (257,5), (513,5), (1025,7), (2049,5), (96,5), (258,6), (514,5), (1026,5), (1152,5), (34,5), (2050,5), (516,5), (264,5), (1028,5), (272,5), (1280,5), (2052,5), (288,5), (24,5), (1032,5), (528,4), (1536,5), (2056,4), (544,5), (2560,7), (48,5), (2064,4), (1056,6), (3072,7)]
def rt1 : List (ℕ × ℕ) := [(1,8), (64,6), (2,8), (128,6), (4,6), (256,8), (8,7), (512,8), (16,6), (1024,9), (32,8), (2048,8)]
def pr (T : List (ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def rt : List (ℕ × ℕ) := rt1 ++ rt2 ++ rt3
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r3 : rt3.all (fun e => okE [] (pr [] e.1) e) = true := by decide +kernel
lemma i3 : ∀ e ∈ rt3, Imp [] e.1 e.2 := okAll (T := []) r3 (by simp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r2 : rt2.all (fun e => okE [] (pr rt3 e.1) e) = true := by decide +kernel
lemma i2 : ∀ e ∈ rt2, Imp [] e.1 e.2 := okAll r2 i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem r1 : rt1.all (fun e => okE [] (pr (rt2 ++ rt3) e.1) e) = true := by decide +kernel
lemma i1 : ∀ e ∈ rt1, Imp [] e.1 e.2 := okAll r1 (apI i2 i3)
lemma ir : ∀ e ∈ rt, Imp [] e.1 e.2 := apI (apI i1 i2) i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_p : pOk 0 rt = true := by decide +kernel

lemma one1 {Q : List (ℕ × ℕ)} {Z K t : ℕ} (h : chk [] Q Z K t FF 1 = false) :
    ∃ M : List (ℕ × ℕ), mFull M = true ∧ ∀ p ∈ M, chk [] Q Z K t p.1 p.2 = false :=
  ⟨[(FF, 1)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩
theorem impB_one {Q : List (ℕ × ℕ)} {Z L : ℕ} (hp : pOk Z Q = true) (hL : L + 1 ≤ 15) (hA : Imp [] Z L)
    (hI : ∀ e ∈ Q, ImpB [] e.1 e.2 1) (hc : chk [] Q Z L 1 FF 1 = false) : ImpB [] Z (L + 1) 1 := by
  intro q hq hs
  obtain ⟨k, hk, t, ht, S, hS, hl⟩ := hs.live
  by_cases hkt : k + t < L
  · exact hA (k + t) hkt (hl.sol.mono le_rfl hS)
  · obtain rfl : t = 1 := by omega
    obtain rfl : L = k + 1 := by omega
    exact imp_of_live (L := k + 1 + 1) (Or.inl rfl) hp hL hI (by omega) hS hl hA (Or.inr (one1 hc))
def up (B T : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  T.map fun e => (e.1, bif B.any (fun x => Nat.beq x.1 e.1 && Nat.beq x.2 e.2) then e.2 + 1 else e.2)
lemma up_imp {B T : List (ℕ × ℕ)} (hB : ∀ e ∈ B, ImpB [] e.1 (e.2 + 1) 1) (hT : ∀ e ∈ T, Imp [] e.1 e.2) :
    ∀ e ∈ up B T, ImpB [] e.1 e.2 1 := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  change ImpB [] x.1 (bif B.any (fun y => Nat.beq y.1 x.1 && Nat.beq y.2 x.2) then x.2 + 1 else x.2) 1
  cases hc : B.any (fun y => Nat.beq y.1 x.1 && Nat.beq y.2 x.2) with
  | false => exact (hT x hx).toB 1
  | true =>
    obtain ⟨y, hy, hxy⟩ := List.any_eq_true.1 hc
    rw [Bool.and_eq_true] at hxy
    obtain rfl : y = x := Prod.ext (Nat.eq_of_beq_eq_true hxy.1) (Nat.eq_of_beq_eq_true hxy.2)
    exact hB y hy
noncomputable def okB (B A T : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  A.any (fun x => Nat.beq x.1 e.1 && Nat.beq x.2 e.2) && pOk e.1 (up B (pr T e.1)) && Nat.ble (e.2 + 1) 15 &&
    !chk [] (up B (pr T e.1)) e.1 e.2 1 FF 1
lemma okAllB {B A T U : List (ℕ × ℕ)} (h : U.all (okB B A T) = true) (hB : ∀ e ∈ B, ImpB [] e.1 (e.2 + 1) 1)
    (hA : ∀ e ∈ A, Imp [] e.1 e.2) (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, ImpB [] e.1 (e.2 + 1) 1 := by
  intro e he
  have h := List.all_eq_true.1 h e he
  simp only [okB, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨⟨⟨⟨x, hx, hx1, hx2⟩, hp⟩, hL⟩, hc⟩ := h
  obtain rfl : x = e := Prod.ext (Nat.eq_of_beq_eq_true hx1) (Nat.eq_of_beq_eq_true hx2)
  exact impB_one hp (Nat.le_of_ble_eq_true hL) (hA x hx) (up_imp hB fun y hy => hT y (List.mem_of_mem_filter hy)) hc
lemma apB {A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, ImpB [] e.1 (e.2 + 1) 1) (hb : ∀ e ∈ B, ImpB [] e.1 (e.2 + 1) 1) :
    ∀ e ∈ A ++ B, ImpB [] e.1 (e.2 + 1) 1 := fun e he => (List.mem_append.1 he).elim (ha e) (hb e)
def rb3 : List (ℕ × ℕ) := [(1153,4), (98,4), (1281,4), (1537,4), (2561,4), (3073,4), (2562,4), (3074,4), (280,4), (2564,4), (3076,4), (304,4), (2072,4), (3080,4), (560,4), (2576,4)]
def rb2 : List (ℕ × ℕ) := [(129,5), (66,5), (257,5), (513,5), (1025,7), (2049,5), (96,5), (258,6), (514,5), (1026,5), (1152,5), (34,5), (2050,5), (516,5), (264,5), (1028,5), (272,5), (1280,5), (2052,5), (288,5), (24,5), (1032,5), (528,4), (1536,5), (2056,4), (544,5), (2560,7), (48,5), (2064,4), (1056,6), (3072,7)]
def rb1 : List (ℕ × ℕ) := [(1,8), (64,6), (2,8), (128,6), (4,6), (256,8), (8,7), (512,8), (16,6), (1024,9), (32,8), (2048,8)]
def rtp : List (ℕ × ℕ) := up (rb1 ++ rb2 ++ rb3) rt
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b3 : rb3.all (okB [] rt3 []) = true := by decide +kernel
lemma j3 : ∀ e ∈ rb3, ImpB [] e.1 (e.2 + 1) 1 := okAllB b3 (by simp) i3 (by simp)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b2 : rb2.all (okB rb3 rt2 rt3) = true := by decide +kernel
lemma j2 : ∀ e ∈ rb2, ImpB [] e.1 (e.2 + 1) 1 := okAllB b2 j3 i2 i3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem b1 : rb1.all (okB (rb2 ++ rb3) rt1 (rt2 ++ rt3)) = true := by decide +kernel
lemma j1 : ∀ e ∈ rb1, ImpB [] e.1 (e.2 + 1) 1 := okAllB b1 (apB j2 j3) i1 (apI i2 i3)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootp_p : pOk 0 rtp = true := by decide +kernel

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
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1) || (x 0 && x 2 && x 3) || (x 1 && x 2 && x 3) || (x 0 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 1 && x 2 && x 5) || (x 1 && x 3 && x 4 && x 5) || (x 2 && x 3 && x 4 && x 5)
def EF : ℕ := (rawP.getD 0 0 &&& rawP.getD 1 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 3 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0) ||| (rawP.getD 0 0 &&& rawP.getD 2 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 2 0 &&& rawP.getD 5 0) ||| (rawP.getD 1 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0) ||| (rawP.getD 2 0 &&& rawP.getD 3 0 &&& rawP.getD 4 0 &&& rawP.getD 5 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
lemma rawP_len : rawP.length = 6 := rfl
lemma row_list (b : ℕ) : List.ofFn (fun v : Fin 6 => (rawP.getD v.val 0).testBit b) = rawP.map (fun x => x.testBit b) := by
  apply List.ext_getElem
  · simp [rawP_len]
  · intro i h1 h2
    have : i < rawP.length := by simpa using h2
    rw [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this]; rfl
lemma f_bit (k : ℕ) : EF.testBit k = f (fun v : Fin 6 => (rawP.getD v.val 0).testBit k) := by
  simp only [f, EF, Nat.testBit_or, Nat.testBit_and]
  rfl
def binary : List Gate → ℕ
  | [] => 0
  | g :: gs => match g.op with
    | .not => binary gs
    | _ => binary gs + 1
def inversions : List Gate → ℕ
  | [] => 0
  | g :: gs => match g.op with
    | .not => inversions gs + 1
    | _ => inversions gs
lemma budgetSum (gs : List Gate) : binary gs + inversions gs = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih => cases g with | mk o ins => cases o <;> simp [binary, inversions] <;> omega
lemma inversionPositive {gs : List Gate} (h : ∃ g ∈ gs, g.op = GateOp.not) : 0 < inversions gs := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨g',mem,eg⟩ := h
    rcases List.mem_cons.1 mem with rfl | tail
    · simp [inversions,eg]
    · have hp := ih ⟨g',tail,eg⟩
      cases g with | mk o ins => cases o <;> simp [inversions] <;> omega
lemma exBudget {T : ℕ} (m : ℕ) (gs : List Gate) : ∀ (w : List ℕ) (S : Set ℕ), (∀ x ∈ w, x ∈ S) → 0 ∈ S → m ∈ S →
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∃ i, (ex m gs w).getD i 0 = T) → SolB m T (binary gs) (inversions gs) S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → SolB m T (binary (g :: gs)) (inversions (g :: gs)) S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by cases g with | mk o ins => cases o <;> simp [binary]) (by cases g with | mk o ins => cases o <;> simp [inversions]) subset_rfl
    have go : SolB m T (binary gs) (inversions gs) (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
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
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) go
    · match l with
      | [] => exact stay hm
      | i :: _ => exact .un (rd i) go

theorem budgetBridge (D : PEqualNP.CircuitLowerBounds.Circuit) (hD : PEqualNP.MetaComplexity.FanInTwo D)
    (hf : ∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y) :
    SolB (mz 0) (tz 0) (binary D.gates) (inversions D.gates) (C (mz 0) (WZ [] 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP.getD v.val 0).testBit k
  let init : List ℕ := rawP.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, _, rfl⟩ := hx
    rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ [] 0) := by
    intro x hx
    simp only [init, List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact Or.inl ⟨w, by simp [rawL, hw], rfl⟩
  have hinit_bits : ∀ k, (mz 0).testBit k = true → init.map (fun x => x.testBit k) = List.ofFn (row k) := by
    intro k hk
    simp only [init, List.map_map, Function.comp_def, Nat.testBit_and, hk, Bool.and_true]
    rw [row_list]
  have hout : (ex (mz 0) gates init).getD out 0 = tz 0 := by
    rw [← EF_ok]
    have hsub : ∀ x ∈ ex (mz 0) gates init, x &&& mz 0 = x := ex_sub (mz 0) hinit_sub
    have hsub' := getD_mem (S := {x | x &&& mz 0 = x}) hsub (by simp) out
    apply Nat.eq_of_testBit_eq; intro k
    have e1 := congrArg (fun x => x.testBit k) hsub'
    simp only [Nat.testBit_and] at e1
    rw [← e1, Nat.testBit_and]
    cases hk : (mz 0).testBit k with
    | false => simp
    | true =>
      simp only [Bool.and_true]
      rw [← getD_map, ex_bit (mz 0) hk gates init hD, hinit_bits k hk]
      have h := hf (row k)
      change (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (List.ofFn (row k))).getD out false = f (row k) at h
      rw [h]
      exact (f_bit k).symm
  exact exBudget (mz 0) gates init (C (mz 0) (WZ [] 0))
    hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl))
    hD ⟨out, hout⟩

structure Snapshot where
  blue : Bool
  fuel : Nat
  gates : Nat
  negs : Nat
  budget : Nat
  wires : List W
  deriving DecidableEq

noncomputable def evalSnap (l m g K : Nat) (s : Snapshot) : Bool :=
  if s.blue then look1 l m g K s.fuel s.gates s.negs s.budget s.wires
  else look l m g s.fuel s.gates s.negs s.budget s.wires

noncomputable def saved (l m g K : Nat) (cache : List Snapshot) (blue : Bool)
    (fuel k t z : Nat) (v : List W) : Bool :=
  let s := Snapshot.mk blue fuel k t z v
  if s ∈ cache then false else evalSnap l m g K s

lemma saved_ok (l m g K : Nat) (cache : List Snapshot)
    (h : ∀ s ∈ cache, evalSnap l m g K s = false) :
    saved l m g K cache = fun blue fuel k t z v => evalSnap l m g K ⟨blue,fuel,k,t,z,v⟩ := by
  funext blue fuel k t z v
  unfold saved
  dsimp only
  split
  · exact (h _ (by assumption)).symm
  · rfl

noncomputable def checkChildren (l m g K : Nat) (cache : List Snapshot) (s : Snapshot) : Bool :=
  let recurse := saved l m g K cache
  match s.fuel with
  | 0 => true
  | j+1 =>
    let k := s.gates
    let t := s.negs
    let z := s.budget
    let v := s.wires
    Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      if s.blue then
        Bool.rec (motive := fun _ => Bool) (mv (recurse false K) l m g k t z v y) true
          (node (recurse true j (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS)
      else mv (recurse false j) l m g k t z v y)) true (Nat.ble v.length 1)

lemma children_ok (l m g K : Nat) (cache : List Snapshot) (s : Snapshot)
    (h : ∀ e ∈ cache, evalSnap l m g K e = false) :
    evalSnap l m g K s = checkChildren l m g K cache s := by
  unfold checkChildren
  rw [saved_ok _ _ _ _ _ h]
  rcases s with ⟨b,j,k,t,z,v⟩
  cases b <;> cases j <;> rfl

noncomputable def checkFront (Q : List (ℕ × ℕ)) (Z K t : Nat) (cache : List Snapshot) : Bool :=
  let l := lz Z
  let m := mz Z
  let P := PZ Q
  let g := pL (Q.map fun _ => 16)
  let B := pL (Q.map fun e => 16 + (K - e.2))
  let p := pwr [] Z
  let recurse := saved l m g K cache
  let top (z : Nat) (v : List W) := Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ K) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv (recurse false K) l m g K t z v y) (Nat.beq 1 1)) true
      (node (recurse true K (Nat.sub K 1) t) (pos t) l m g (Nat.sub (Nat.sub K t) y) v.length z v (fun h xs => pairsC FF h (fs xs))))) true (Nat.ble v.length 1)
  anySub (pos t) l (avl P m (rawL [])) 0 (fun v =>
    Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (child top g (fun h => h v) (Nat.sub B (sumc v))) (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v))

lemma front_eq (Q : List (ℕ × ℕ)) (Z K t : Nat) (cache : List Snapshot)
    (h : ∀ s ∈ cache, evalSnap (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K s = false) :
    chk [] Q Z K t FF 1 = checkFront Q Z K t cache := by
  simp only [chk, frc_eq, st_eq, checkFront]
  rw [saved_ok _ _ _ _ _ h]
  rfl

private def n0 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb600000000000000000000000000fe07f03fbc36db7fc07fc07fde01fc007f00781fc007f003c183f8000000000000000000fe00ff007f807fc03fc03fc07f80db7c007c003e0000000060f001e07ffbffdfdfdb6dbfffbfffbfe0000000000000000000000000000000ffff8001ffffc000
private def n1 : Nat := 0x200040000000000010002008020000000800000000080000040000000004000000000000
private def n2 : Nat := 0x4010802100421080000040100401000000040000001000000002000000080000000000000
private def n3 : Nat := 0x4210842100421080010042108421000000840000001080000042000000084000000000000
private def w0 : W := ⟨n0,n1,n2,n3,0x3⟩
private def n4 : Nat := 0x1fffdfffefffeffff00000000000000fffefffd7ffeafc00000000000f1c78e3c3fb60078387838781fd5e3e178f87fde3c078f023163c7800000000000000000f1e0f8f07c787e3c3830383070600073e073e0b9f057003000cc01987ffbffdfdfdb0000000000000feafffebfffbfe00000000000000000ff807f81ffc03fc0
private def n5 : Nat := 0x4200840008000000000000108000004010000100000000000000000000000010000000000
private def n6 : Nat := 0x10002000401004200842000000080200002008000004200000100000000200000000000
private def n7 : Nat := 0x4210842008401004200842108000084210002108000004200000100000000210000000000
private def w1 : W := ⟨n4,n5,n6,n7,0x3⟩
private def n8 : Nat := 0x1fffc0000000000007fff7ffefffc00fffefffd0000001b7e000000008f847c23a300db473047304711951f9047c44611f3847cc3fcc23e400000000000000000e19ce0cc706670333e2e3e2e7c5c00639c639cb18c04cdae18cb01967ffbffdfc0006d80000000000feafffe0000000ffffbfffdfe000000f8787c79fc3c3e3c
private def n9 : Nat := 0x10800008000000000000000001000210000000400000000000000000000000040000000
private def n10 : Nat := 0x4200000100020084000000000420084000000000020000010000008000000000800000000
private def n11 : Nat := 0x4210800108020084000000000421084210000000420000010000008000000000840000000
private def w2 : W := ⟨n8,n9,n10,n11,0x3⟩
private def n12 : Nat := 0x1fffc00000000000000000000000000fffefffd00000000000000000081840c2023000040304030401195038040c0461030040c02304206000000000000000000e180e0c0706070303820382070400063806380b18004002000c801907ffbffdfc0000000000000000feafffe000000000000000000000000f8007c01fc003e00
private def n13 : Nat := 0x4210840008000000000000108001004210000100400000000000000000000010040000000
private def n14 : Nat := 0x4000000000000080000000000000000000000000000000000000000000
private def n15 : Nat := 0x4210840008000004000000108001084210000100400000000000000000000010040000000
private def w3 : W := ⟨n12,n13,n14,n15,0x0⟩
private def n16 : Nat := 0x1fffe000000007fff0000000180fffe00007ffe801800fdff800049624b1212a09024ae24ae240950924924b225092a624ab121f9253000000000000000009d589eae4b564dab279d259c4b38d25f5a5e582f6e42cd1c7cb7816e7ff800001fd86c3fffbfff800fe80000bfff800ffffbfffc00fc0000c7777375e3bbb9ba
private def n17 : Nat := 0x2100000000000000000000000000040008020000000000000000000000000100000
private def n18 : Nat := 0x40008000000200000000000000000802100400000000800000400000000002000000
private def n19 : Nat := 0x42108000000200000000000000000842108420000000800000400000000002100000
private def w4 : W := ⟨n16,n17,n18,n19,0x3⟩
private def n20 : Nat := 0xfffe000000007ffe0000300000fffc7ffe200300fc00200024c12609098442125c121c1284c4494112601384994126209830932800000000000000005b36559b2ecd2b66954b974b2696993a373b361d5b11a98b5662d4c50003ffc01fc361bfff80003fefe2000080003feffff80001fefdffff36eeeaef9b777577
private def n21 : Nat := 0x420000010000000000000000000000001080210800000020000000000000400
private def n22 : Nat := 0x800000000000000000000000004000000000001000000000008000
private def n23 : Nat := 0x420000010800000000000000000000001084210800000021000000000008400
private def w5 : W := ⟨n20,n21,n22,n23,0x3⟩
private def n24 : Nat := 0xffff00000000fffc060000000000000fc07e01ff880012209104841209090209420942002438090e084244a09150440848d4000000000000000026ee2b7715bb16dd8af78af71dee4b05ef05ee82f75764b72e1dd43b0000001fc01b0d80003fffbfe00afffebfffbfe00003fffdfefdffffaddddfdf56eeefef
private def n25 : Nat := 0x1084200800000000000000000000000000000002108401000000000000001
private def n26 : Nat := 0x10000000000000000000000000000000040000020000000000000020
private def n27 : Nat := 0x1084210800000000000000000000000000000042108421000000000000021
private def w6 : W := ⟨n24,n25,n26,n27,0x3⟩
private def sLowA2 : Snapshot := ⟨true,11,10,0,0x4a5294a7394e739ca749c6539467394e52a52729ca74a4e739d2919d29494a128c654a4a92,[w0,w1,w2,w3,w4,w5,w6]⟩
private def n28 : Nat := 0x1fffe0000000000000000000000fffe00007ffe8000000000000041420a1012a00020282028200950824120b0250828020a00216105000000000000000000914098a048504c2820102010402000534052402960420010008401087ff800001fd80000000000000fe80000bfff80000000000000000000c7007301e3803980
private def n29 : Nat := 0x4200842108000000000000108000004010040108020000000000000000000010000100000
private def n30 : Nat := 0x200000000000000000002000000000000000000000000000000000000
private def n31 : Nat := 0x4200842108000000200000108000004010042108020000000000000000000010000100000
private def w7 : W := ⟨n28,n29,n30,n31,0x0⟩
private def sLowA4 : Snapshot := ⟨true,11,10,0,0x4a5394a5294e93a4e549c65394a959ce729ca5294e54a4e7495291a4e9494a1294e32a4a92,[w0,w1,w2,w4,w7,w5,w6]⟩
private def n32 : Nat := 0x7fff0000000000fffe000000000018000000000009004802020090042004200401101200048004012200488120c0240000000000000000008118808c40464023260c240c48180043184218210c00cd0c188301067ff8000000006c00000000000fe800000000000ffffbfffc00000000c0707071e0383838
private def n33 : Nat := 0x10802108000000000000000001000210040008420000000000000000000000040100000
private def w8 : W := ⟨n32,n33,0x0,n33,0x0⟩
private def sLowA16 : Snapshot := ⟨true,11,10,0,0x4e7294e52952749ce74a4a75a46739d2529ca7394a54a5293952929ce9494a348c632a4a92,[w0,w1,w2,w4,w5,w6,w8]⟩
private def n34 : Nat := 0x1fffefffe00007fff7ffe0001b0fffefffc7ffea01b00fdffa0006de36f1b1ba4d236fe36be368dd4db4936f2378dbb636eb1b9f9b7380000000000000000df7edfbf6fdf6fefb7dfb7df6fbedb7f7f7f7e3f7f53ed9f7ef7d5ef7ffbffc01fdb6dbfffbfffbfefea0000bfffbfeffffbfffdfefdfffff7fffbfffbfffdff
private def n35 : Nat := 0x40008000000200800000000000000802100400004000800000401000000002008000
private def w9 : W := ⟨n34,0x0,n35,n35,0x0⟩
private def sLowA19 : Snapshot := ⟨true,11,10,0,0x5294a4a7394e74a525394a75a4a95a569494e529ca739ca738d292a4a7294a3494e1394692,[w0,w1,w2,w9,w4,w5,w6]⟩
private def n36 : Nat := 0xfffeffff00007ffefffc360000fffc7ffe2fc37efdffa80036e1b70d8d964b1b5e1b5e1bc6c46d791b6e1bc6dde1b770dc38dbfc00000000000000007ffe7fff3fff3fff9fff9fff3ffedb3fff3ffe9fff57edbf7e7fd4ff0003ffdfdfdb6dbfffbfffbfefeafffebfffbfeffffbfffdfefdffffbfffffffdfffffff
private def n37 : Nat := 0x10800000000000000000000000004000040000021000000000008020
private def w10 : W := ⟨n36,0x0,n37,n37,0x0⟩
private def sLowA24 : Snapshot := ⟨true,11,10,0,0x5294a5294a4e739ce7294a75a4a95a5694a5294a52939ca7394a719ce5294a3494e5494651,[w0,w1,w2,w4,w10,w5,w6]⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hLowA2 : evalSnap (lz 0) (mz 0) (pL (rt.map fun _ => 16)) 11 sLowA2 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hLowA4 : evalSnap (lz 0) (mz 0) (pL (rt.map fun _ => 16)) 11 sLowA4 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hLowA16 : evalSnap (lz 0) (mz 0) (pL (rt.map fun _ => 16)) 11 sLowA16 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hLowA19 : evalSnap (lz 0) (mz 0) (pL (rt.map fun _ => 16)) 11 sLowA19 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hLowA24 : evalSnap (lz 0) (mz 0) (pL (rt.map fun _ => 16)) 11 sLowA24 = false := by decide +kernel
private def rootLowA : List Snapshot := [sLowA2,sLowA4,sLowA16,sLowA19,sLowA24]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem chLowA : chk [] rt 0 11 0 FF 1 = false := by
  rw [front_eq _ _ _ _ rootLowA (by
    intro s hs
    simp only [rootLowA, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact hLowA2
    · exact hLowA4
    · exact hLowA16
    · exact hLowA19
    · exact hLowA24)]
  decide +kernel
private def sLowB90 : Snapshot := ⟨true,11,10,1,0x5294a5294a4e739ce7294a75a4a95a5694a5294a52939ca7394a719ce5294a3494e5494651,[w0,w1,w2,w4,w10,w5,w6]⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hLowB90 : evalSnap (lz 0) (mz 0) (pL (rt.map fun _ => 16)) 11 sLowB90 = false := by decide +kernel
private def rootLowB : List Snapshot := [sLowB90]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem chLowB : chk [] rt 0 11 1 FF 1 = false := by
  rw [front_eq _ _ _ _ rootLowB (by
    intro s hs
    simp only [rootLowB, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · exact hLowB90)]
  decide +kernel
private def n38 : Nat := 0xfffe00007fff7ffefffdb60000fffc7ffe201b7efdffabfe2ef1778b8984db17df17df17c4c45d5d17671385dbf176f9dcb8bb7e00000000000000005f3e579f2fcf2be797cf97cf2f9edb3e3f3f3e1f5f11ed8f7e73d4e70003ffc01fc36dbfffbfffbfefe2000080003feffffbfffdfefdffff36ffeaff9b7ff57f
private def n39 : Nat := 0x400000000000000000000000000000000000200000000000000000000000000
private def n40 : Nat := 0x4200840008000000000800108000004010000100000004000000000001000010000008000
private def n41 : Nat := 0x4200840008400000000800108000004010000100000004200000000001000010000008000
private def w11 : W := ⟨n38,n39,n40,n41,0x0⟩
private def sOne14 : Snapshot := ⟨false,12,10,0,0x4a5394a7494a73a4e739465394a959ce72a52729d2939ca5395291a527294a1294e5494692,[w0,w1,w2,w4,w11,w5,w6]⟩
private def n42 : Nat := 0x1fffdfffe0000ffff00000000000000fffe000100008fc00000000000d106883436320068206820681b11a2a068986c5a24068902214344800000000000000000a0c0a860503054182830283050600041c040c0a0a0460030008c01187ff8001fc0180000000000000008fffe3fff80000000000000000000c900150064800a80
private def w12 : W := ⟨n42,n40,n39,n41,0x0⟩
private def sOne15 : Snapshot := ⟨false,12,10,0,0x4a5394a7494a73a4e739465394a959ce72a52729d2939ca5395291a527294a1294e5494692,[w0,w1,w12,w2,w4,w5,w6]⟩
private def n43 : Nat := 0xffff00000000fffc06fffefffd7ffeafdb7efdffabfe13f09f84879209093f097f0943d427fd09ff0fc27ff09ff87c784ffe000000000000000027fe2bff15ff16ff8aff8aff1dfe4b07ff07fe83ff57edbf3e1fd43f0000001fc01b0d80003fffbfefeafffebfffbfeffffbfffdfefdffffadddffff56eeffff
private def n44 : Nat := 0x1080000000000000000000000000000000000002000000000000000000000
private def n45 : Nat := 0x200040000000000010002008020000000800000000080000040000020004000000000020
private def n46 : Nat := 0x200040000001080010002008020000000800000000080000042000020004000000000020
private def w13 : W := ⟨n43,n44,n45,n46,0x0⟩
private def sOne38 : Snapshot := ⟨false,12,10,0,0x4e539ca73a4e7294e729c63494654a569494e94a5293952949ca519ce538c23494e54a4a51,[w0,w1,w2,w4,w5,w13,w6]⟩
private def n47 : Nat := 0x1fffdfffefffe00007fff7ffe0001b000000000000000000000000000ec07603b3824d276c07680769c01d8007600701d800760038183b0000000000000000000d800d4006a00690035003500620090780078003c0000000040e001c07ffbffc01fc0603fff8000000000000000000000000000000000000052220000a9110000
private def w14 : W := ⟨n47,n45,n44,n46,0x0⟩
private def sOne39 : Snapshot := ⟨false,12,10,0,0x4e539ca73a4e7294e729c63494654a569494e94a5293952949ca519ce538c23494e54a4a51,[w0,w1,w14,w2,w4,w5,w6]⟩
private def n48 : Nat := 0x1fffefffeffff00007ffe0001b60000fffc7ffeafc300fdffabfe74f3a79d1db6423adf3adf3acec4e96d3a7b3bce9d73a7389939d3be00000000000000005f765fbb2fdd2fee95db97db27b6db3e773f761f7b53a99b7676d4ed0003ffc01fdb61bfffbfffbfefe20000bfffbfeffff80001fefdffff37efebef9bf7f5f7
private def n49 : Nat := 0x20000000000000000000000000000000000010000000000000000000000000
private def n50 : Nat := 0x10800008000000000800000001000210000000400004000000000001000000040008000
private def n51 : Nat := 0x10800008020000000800000001000210000000400004010000000001000000040008000
private def w15 : W := ⟨n48,n49,n50,n51,0x0⟩
private def sOne43 : Snapshot := ⟨false,12,10,0,0x4e729529394e549ce9394a75a46739d252a5294a4a739ca72952929d27294a348c65494692,[w0,w1,w2,w15,w4,w5,w6]⟩
private def n52 : Nat := 0x1fffc0000000000007fff0000fffc00fffe0001000000187e000000008b045822a2009945204520451111169045844411628458c364c22c400000000000000000a088a044502250112a24282458480041884088a084044424088901127ff8001fc0000c00000000000008fffe000000000003fffc00000000c810141064080a08
private def w16 : W := ⟨n52,n50,n49,n51,0x0⟩
private def sOne44 : Snapshot := ⟨false,12,10,0,0x4e729529394e549ce9394a75a46739d252a5294a4a739ca72952929d27294a348c65494692,[w0,w1,w2,w16,w4,w5,w6]⟩
private def n53 : Nat := 0x1fffefffeffff00000000fffdb6000000007ffeafc07efdffabfe7273939c9cb60939cf39cf39ce40e47d393f39ce4cf393784539c9fe00000000000000003eee3f771fbb1fdd8bf78bf71feedb1def1dee8ef75764b76e3dd47b0000001fdfdb0dbfffbfffbfe00afffebfffbfe00003fffdfefdffffafdfdfdf57efefef
private def n54 : Nat := 0x84000000000000000000000000000000000000008000000000000000000
private def n55 : Nat := 0x10800008000000010000000001000210000000400000000040000020000000040000020
private def n56 : Nat := 0x10800008000084010000000001000210000000400000000040008020000000040000020
private def w17 : W := ⟨n53,n54,n55,n56,0x0⟩
private def sOne46 : Snapshot := ⟨false,12,10,0,0x4e72952939527394a729ca75a46739d252a5294a4a74a52939ca7194e5394a348c654a4a51,[w0,w1,w2,w17,w4,w5,w6]⟩
private def n57 : Nat := 0x1fffc0000000000007fff7ffe000000fffefffd0000001b00000000008d846c232300d2463046304611951b8046c04611b3046c83b8c236000000000000000000c110c088604460223408340860100062106210310800890810c201847ffbffc000006000000000000fe000000000000ffff800000000000050202020a8101010
private def w18 : W := ⟨n57,n55,n54,n56,0x0⟩
private def sOne47 : Snapshot := ⟨false,12,10,0,0x4e72952939527394a729ca75a46739d252a5294a4a74a52939ca7194e5394a348c654a4a51,[w0,w1,w2,w18,w4,w5,w6]⟩
private def n58 : Nat := 0x1fffe000000007fff0000000180fffe0000000080180001ff80004922491212209024a224a22409109208249224092222489121c92410000000000000000084488a2441124489229420944928424548444822244244142895012a7ff8000000180c00003fff80000800003fff80000003fffc00000000c111111060888888
private def n59 : Nat := 0x2100000000000800000000000000040008020004000000000001000000000108000
private def n60 : Nat := 0x800000000000000000000000
private def n61 : Nat := 0x2100000000000800000000000000040008020004000800000001000000000108000
private def w19 : W := ⟨n58,n59,n60,n61,0x0⟩
private def sOne55 : Snapshot := ⟨false,12,10,0,0x5294a4e529ce74a527394a75a4a95a56949ca7394e539ca738d292a4e7294a3494e3294692,[w0,w1,w2,w4,w19,w5,w6]⟩
private def n62 : Nat := 0x1fffc0000fffeffff00007ffefffc360000fffd7ffe2fc37efc002bfeb6d5b6adad964b5b5d5b5d5bd6c56df55b6d5bd6ddd5b76adc32dbee00000000000000007bb675db3eed3b769d6b9f6b36d6993ab73bb69ddb15a9ab566ad4d50003ffdfdfc361bfff80003fefe2fffe80003feffff80001fefdffff3eeeeeef9f777777
private def w20 : W := ⟨n62,n60,n59,n61,0x0⟩
private def sOne56 : Snapshot := ⟨false,12,10,0,0x5294a4e529ce74a527394a75a4a95a56949ca7394e539ca738d292a4e7294a3494e3294692,[w0,w1,w20,w2,w4,w5,w6]⟩
private def n63 : Nat := 0x1fffe000000007fff0000000180fffe00007ffe801800fc00000049424a1212a09024ac24ac240950924124b025092a424aa121f125200000000000000000991094884a444922250825084210905a105a102d0800890850a201447ff800001fc0603fff8000000fe000000000000ffff800000000000042222020a1111010
private def n64 : Nat := 0x2100000000010000000000000000040008020000000040000020000000000100020
private def n65 : Nat := 0x200000000000000000000000000000000000000400000000000000000
private def n66 : Nat := 0x2100000000210000000000000000040008020000000040000420000000000100020
private def w21 : W := ⟨n63,n64,n65,n66,0x0⟩
private def sOne58 : Snapshot := ⟨false,12,10,0,0x5294a4e529d2939ce529ca75a4a95a56949ca7394e54a529494a719ca5394a3494e32a4a51,[w0,w1,w2,w4,w21,w5,w6]⟩
private def n67 : Nat := 0x1fffc0000fffeffff00007ffefffc360000fffd00002fc37e01ffabfeb6b5b5adad164b5b535b535bd6856dbc5b4f5ad6d5b5b55adc0adade000000000000000066ee6b7735bb36dd9af79af73dee4b25ef25ee92f75764b72e5dd4bb0003ffdfc01b0d80003fffbfe00afffebfffbfe00003fffdfefdffffbddddfdf5eeeefef
private def w22 : W := ⟨n67,n65,n64,n66,0x0⟩
private def sOne59 : Snapshot := ⟨false,12,10,0,0x5294a4e529d2939ce529ca75a4a95a56949ca7394e54a529494a719ca5394a3494e32a4a51,[w0,w1,w22,w2,w4,w5,w6]⟩
private def n68 : Nat := 0x1fffdfffefffeffff0000000000000000000000000000000000000000f007803c3c360078007800781e01e0007800781e000780020103c0000000000000000000f000f8007c007e003800380070000070007000380000000000c001807ffbffdfdfdb00000000000000000000000000000000000000000000ff800001ffc00000
private def n69 : Nat := 0x4200840008000000010002108020004010800100000080000040000000004010000000000
private def n70 : Nat := 0x10002000401000000040000000000000000000000000000000000000000000000000000
private def n71 : Nat := 0x4210842008401000010042108020004010800100000080000040000000004010000000000
private def w23 : W := ⟨n68,n69,n70,n71,0x0⟩
private def sOne66 : Snapshot := ⟨true,12,11,1,0x4a5294a5394a729ce729c233946549ce7294e729d29394e749ca71a52948c21294e54a4a92,[w0,w1,w23,w2,w4,w5,w6]⟩
private def n72 : Nat := 0x1fffc0000000000007fff7ffefffc00000000000000000000000000008e047023a000db470047004710011c0047004011c0047003c08238000000000000000000e000e000700070003e003e007c000060006000300000000000c001807ffbffdfc0006d800000000000000000000000000000000000000000f8780001fc3c0000
private def n73 : Nat := 0x210840008000000010002008021000210800000400080000040000000004000040000000
private def n74 : Nat := 0x4000000100020080000000000400000000000000000000000000000000000000000000000
private def n75 : Nat := 0x4210840108020080010002008421000210800000400080000040000000004000040000000
private def w24 : W := ⟨n72,n73,n74,n75,0x0⟩
private def sOne67 : Snapshot := ⟨true,12,11,1,0x4a5294a7294e5394e92a4634942539d25294e94a4a73952939ca729d2948c2348c654a4a92,[w0,w1,w2,w24,w4,w5,w6]⟩
private def sOne68 : Snapshot := ⟨true,12,11,1,0x4a5294a7394e739ca749c6539467394e52a52729ca74a4e739d2919d29494a128c654a4a92,[w0,w1,w2,w3,w4,w5,w6]⟩
private def n76 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb6fffefffd0000001b7e00000000ff87fc3fbf36db7ff07ff07fdf95ff907fc47e1ff387fcc3fdc3fe400000000000000000ff9cffcc7fe67ff33fee3fee7fdcdb7f9c7f9cbf8c04cdae78fb01f67ffbffdfdfdb6dbfffbfffbfefeafffe0000000ffffbfffdfe000000fffffc79fffffe3c
private def n77 : Nat := 0x4210802100421084000040100421084000040000021000010002008000080000800000000
private def w25 : W := ⟨n76,0x0,n77,n77,0x0⟩
private def sOne69 : Snapshot := ⟨true,12,11,1,0x4a5294e529ca5294a93a42539c25394e739ca94a4e529d2929ce52952948463484a54a4a92,[w25,w0,w1,w2,w4,w5,w6]⟩
private def sOne70 : Snapshot := ⟨true,12,11,1,0x4a5394a5294e93a4e549c65394a959ce729ca5294e54a4e7495291a4e9494a1294e32a4a92,[w0,w1,w2,w4,w7,w5,w6]⟩
private def n78 : Nat := 0xfffe0000000000000000000000fffc7ffe2000000000000020c10608098400101810181004c441411060138418010600102083000000000000000000512050902c482a2410001000200000322033201950110000004000800003ffc01fc30000000000000fe2000080003fe0000000000000000036806a819b403540
private def n79 : Nat := 0x4200840008420000010000108000004010000100001080210800000020000010000000400
private def n80 : Nat := 0x800000000000000000000000004000000000000000000000000000
private def n81 : Nat := 0x4200840008420000010800108000004010000100001084210800000020000010000000400
private def w26 : W := ⟨n78,n79,n80,n81,0x0⟩
private def sOne71 : Snapshot := ⟨true,12,11,1,0x4a5394a7494a53a4e729465394a959ce72a52729d29294a528d291a525394a1294e549c292,[w0,w1,w2,w4,w5,w26,w6]⟩
private def n82 : Nat := 0xffff000000000000000000000000000fc0000000000010008004041200080008000802002020080808420400810000004080000000000000000020e028701438161c0830083010600001e001e080f0570030000c00180000001fc01b000000000000000afffebfffbfe00000000000000000ad805f8156c02fc0
private def n83 : Nat := 0x4200840008001084200800108000004010000100000000000002108401000010000000001
private def w27 : W := ⟨n82,n83,0x0,n83,0x0⟩
private def sOne72 : Snapshot := ⟨true,12,11,1,0x4a5394a7494e9294a539465394a959ce72a52729d294a4e749ce5094a7294a1294e54a4a70,[w0,w1,w2,w4,w5,w6,w27]⟩
private def n84 : Nat := 0x1fffdfffe000000007fff7ffefffd80fffefffd7ffe801b7efdff8000cfe67f33b3a0db67be67be6719d59fd967f66719fbe67ef3fdfb3f700000000000000000fddcfeee7b767dbb3fbf3fbe7f7cd27fde7fdcbfee46cdbe7cff81fe7ffbffdfdfd86dbfffbfff800feafffebfff800ffffbfffdfefc0000ff7f7f7dffbfbfbe
private def n85 : Nat := 0x4200040108020084200000000420084000802100420000010800008400000000802000000
private def w28 : W := ⟨n84,0x0,n85,n85,0x0⟩
private def sOne73 : Snapshot := ⟨true,12,11,1,0x4a539ca729525494a54a4a75a425494e7394e529ca54a52928d29294a9494a3484a13a4a92,[w0,w1,w28,w2,w4,w5,w6]⟩
private def n86 : Nat := 0x1fffc0000fffe00007fff7ffefffc30fffefffd7ffe201b7efc002000afc57e2bab84db577c573c5795d55fd157e45795fbc57ee3fcf2bf680000000000000000fbbef5df7eef7b77bf6fbf6f7ede997bbf7bbebddf15edaf5eebd5d77ffbffdfdfc36dbfff80003fefeafffe80003feffffbfffdfefdfffffefefeffff7f7f7f
private def n87 : Nat := 0x4200000100020084000800000420084000000000020004010000008001000000800008000
private def w29 : W := ⟨n86,0x0,n87,n87,0x0⟩
private def sOne74 : Snapshot := ⟨true,12,11,1,0x4a539d2929ce5494a9394a75a425494e73a5294a4e539ca72952929527294a3484a5494692,[w0,w1,w29,w2,w4,w5,w6]⟩
private def n88 : Nat := 0x1fffc00000000ffff7fff7ffefffc06fffefffd00000fdb7e01ff88009fa4fd27a712db4f324f724f53953fb84fce4e53f7a4fdd3fcca7ed40000000000000000e7feebff75ff76ffbeffbeff7dfe4b67ff67feb3ff57edbf3edfd5bf7ffbffdfc01b6d80003fffbfefeafffebfffbfeffffbfffdfefdfffffdfdfffffefeffff
private def n89 : Nat := 0x4200000100020084010000000420084000000000020000010040008020000000800000020
private def w30 : W := ⟨n88,0x0,n89,n89,0x0⟩
private def sOne75 : Snapshot := ⟨true,12,11,1,0x4a539d2929d25394a729ca75a425494e73a5294a4e54a52929ca7194e5394a3484a54a4a51,[w0,w1,w30,w2,w4,w5,w6]⟩
private def n90 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb6fffe00007ffe801800fdff8000ff67fb3fbeb6db7fee7fee7fdf51fe497fb27d1fea67fab3e1fbfd300000000000000000ff58ffae7fd67feb3fdd3fdc7fb8db7f5a7e583f6e42cd1c7cf781ee7ffbffdfdfdb6dbfffbfffbfefe80000bfff800ffffbfffc00fc0000fffff375fffff9ba
private def n91 : Nat := 0x4010842108421080200040100401000000842100401000000802000400080000002000000
private def w31 : W := ⟨n90,0x0,n91,n91,0x0⟩
private def sOne76 : Snapshot := ⟨true,12,11,1,0x4a7294a5294a5295253a42539c273a569494a529ca729d2948ce52a4a948463494e13a4a92,[w31,w0,w1,w2,w4,w5,w6]⟩
private def n92 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb60000000000000fc07e01ff8800fe27f13fbc36db7fc27fc27fde01fc387f0e785fc4a7f153c58bf8d40000000000000000feeeff777fbb7fddbff7bff77feedb7def7deebef75764b76efdd5fb7ffbffdfdfdb6dbfffbfffbfe00afffebfffbfe00003fffdfefdffffffffdfdfffffefef
private def n93 : Nat := 0x4010802100421080010040100401000000040000001000000042000020080000000000020
private def w32 : W := ⟨n92,0x0,n93,n93,0x0⟩
private def sOne77 : Snapshot := ⟨true,12,11,1,0x4a7294e52a4a5294e729c2539c273a56949ca94a52929d2949ca519ce538463494e54a4a51,[w32,w0,w1,w2,w4,w5,w6]⟩
private def n94 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb60000fffc7ffe200300fc002000fec7f63fbdb6db7fdc7fdc7fdec5fd417f607b9fd947f623d9b3fb280000000000000000ff36ff9b7fcd7fe6bfcbbfcb7f96db7e377f363f5b11a98b76f2d5e57ffbffdfdfdb6dbfffbfffbfefe2000080003feffff80001fefdffffffffeaeffffff577
private def n95 : Nat := 0x10000000000000000000000000080000000000000000000000000000
private def n96 : Nat := 0x4010802100421080000840100401000000040000001004000002000001080000000008000
private def n97 : Nat := 0x4010802100421080010840100401000000040000001084000002000001080000000008000
private def w33 : W := ⟨n94,n95,n96,n97,0x0⟩
private def sOne78 : Snapshot := ⟨true,12,11,1,0x4a7294e52a4a5295292942539c273a56949ca94a529294a7394e52a52728463494e5494692,[w33,w0,w1,w2,w4,w5,w6]⟩
private def n98 : Nat := 0x1fffe000000007fff0000000180000000000000000000000000004802401210209024802480240800900024002009000240010181200000000000000000009c009e004b004d80278025804b00d25c005c002e0000000060b001607ff800001fd86c3fffbfff8000000000000000000000000000000000c7770001e3bb8000
private def n99 : Nat := 0x200042100000000010002008020000000840008020080000040000000004000000100000
private def w34 : W := ⟨n98,n99,0x0,n99,0x0⟩
private def sOne79 : Snapshot := ⟨true,12,11,1,0x4e539ca529ce739d272a463494654a569494a7394e539529494a72a4e948c23494e32a4a92,[w0,w1,w2,w4,w34,w5,w6]⟩
private def n100 : Nat := 0xfffe000000007ffe000030000000000000000000000000002401200908044212401200128400480012001004800120008000900000000000000000005a0055002e802b4015401740268099380038001c00000000406000c00003ffc01fc361bfff80003fe000000000000000000000000000000036ee80019b774000
private def n101 : Nat := 0x200040000420000010002008020000000800000001080210840000020004000000000400
private def w35 : W := ⟨n100,n101,0x0,n101,0x0⟩
private def sOne80 : Snapshot := ⟨true,12,11,1,0x4e539ca73a4a539d2929c63494654a569494e94a529294e528ca72a52538c23494e549c292,[w0,w1,w2,w4,w5,w35,w6]⟩
private def n102 : Nat := 0xffff00000000fffc060000000000000000000000000012009004841209090009400942002400090008024000900040004800000000000000000026002b00158016c00ac00ac01d804b040004000200000000201000200000001fc01b0d80003fffbfe0000000000000000000000000000000addd800156eec000
private def n103 : Nat := 0x200040000001084210802008020000000800000000080000042108401004000000000001
private def w36 : W := ⟨n102,n103,0x0,n103,0x0⟩
private def sOne81 : Snapshot := ⟨true,12,11,1,0x4e539ca73a4e7294a529463494654a569494e94a5293952949ca5094a728c23494e54a4a70,[w0,w1,w2,w4,w5,w6,w36]⟩
private def sOne82 : Snapshot := ⟨true,12,11,1,0x4e7294e52952749ce74a4a75a46739d2529ca7394a54a5293952929ce9494a348c632a4a92,[w0,w1,w2,w4,w5,w6,w8]⟩
private def n104 : Nat := 0x7ffe0000000000fffc0000000300000000000480240101004202100210020084090002400200910024009800120000000000000000004114408820442022140a160a24140022142314110800898a104200840003ffc000006180000000000fe200000000000ffff80001fe0000003068686998343434
private def n105 : Nat := 0x10800008420000010000000001000210000000401080210800000020000000040000400
private def w37 : W := ⟨n104,n105,0x0,n105,0x0⟩
private def sOne83 : Snapshot := ⟨true,12,11,1,0x4e729529394a549ce929ca75a46739d252a5294a4a7294e528d2929d25394a348c6549c292,[w0,w1,w2,w4,w5,w6,w37]⟩
private def n106 : Nat := 0xfffc0000000000000000007e00000000020010008000090100010001000004100104000040801040440008400000000000000000208c2044102210110a260a261c4c00018c018c80840444a6080900120000001fc0000d8000000000000afffe000000000003fffdfe000000a8585c59542c2e2c
private def n107 : Nat := 0x10800008001084200800000001000210000000400000000002108401000000040000001
private def w38 : W := ⟨n106,n107,0x0,n107,0x0⟩
private def sOne84 : Snapshot := ⟨true,12,11,1,0x4e72952939527294a5394a75a46739d252a5294a4a74a52939ce5094a7294a348c654a4a70,[w0,w1,w2,w4,w5,w6,w38]⟩
private def sOne85 : Snapshot := ⟨true,12,11,1,0x5294a4a7394e74a525394a75a4a95a569494e529ca739ca738d292a4a7294a3494e1394692,[w0,w1,w2,w9,w4,w5,w6]⟩
private def n108 : Nat := 0x1fffe0000ffff7fff0000fffd86fffe00007ffe8fd87efdff88005b62db1696b2992dae2dee2d4b50b6792dbe2d4b6ee2dbf165f96df40000000000000000bffebfff5fff5fffafffafff5ffedb5fff5ffeafff57edbf7ebfd57f7ff8001fdfdb6dbfffbfffbfefeafffebfffbfeffffbfffdfefdffffeffffffff7ffffff
private def n109 : Nat := 0x40008000000210000000000000000802100400000000840000420000000002000020
private def w39 : W := ⟨n108,0x0,n109,n109,0x0⟩
private def sOne86 : Snapshot := ⟨true,12,11,1,0x5294a4a73952939ce529ca75a4a95a569494e529ca74a52948ca719ca5394a3494e13a4a51,[w0,w1,w2,w39,w4,w5,w6]⟩
private def n110 : Nat := 0x7ffe000000fc00000000400200008000000c000c000040004100200100084002200030012000000000000000001910148a0a440922050905080210901a121a100d4a00890854228044000000001fc0603fff8000000fe000008000000ffff8000000fc00000666626583333132
private def n111 : Nat := 0x2100420000010000000000000000040008021080210800000020000000000100400
private def w40 : W := ⟨n110,n111,0x0,n111,0x0⟩
private def sOne87 : Snapshot := ⟨true,12,11,1,0x5294a4e529ca54a52729ca75a4a95a56949ca7394e5294e528d292a4e5394a3494e329c292,[w0,w1,w2,w4,w5,w6,w40]⟩
private def n112 : Nat := 0x1ff800000200100000000000200020000000008000200000020001000080010000000000000000004480a260112048902950094092842054a044802664244142c15802a0000000000180c00003fff8000080000bfff80000003fffc00fc00008555535542aaa9aa
private def n113 : Nat := 0x2100001084200800000000000000040008020000000002108401000000000100001
private def w41 : W := ⟨n112,n113,0x0,n113,0x0⟩
private def sOne88 : Snapshot := ⟨true,12,11,1,0x5294a4e529d29294a5394a75a4a95a56949ca7394e54a529494e5094a7294a3494e32a4a70,[w0,w1,w2,w4,w5,w6,w41]⟩
private def n114 : Nat := 0x226011304890244804382430486090027012600531120830600d40100000000000301800000003fe002000080003fe000000001fefdffff24cccacf12666567
private def n115 : Nat := 0x421084210800000000000000000000001080210802108421000000000000401
private def w42 : W := ⟨n114,n115,0x0,n115,0x0⟩
private def sOne89 : Snapshot := ⟨true,12,11,1,0x5294a5294a4a5294a5294a75a4a95a5694a5294a529294e528ce5094a5294a3494e549c270,[w0,w1,w2,w4,w5,w6,w42]⟩
private def sOne90 : Snapshot := ⟨true,12,11,1,0x5294a5294a4e739ce7294a75a4a95a5694a5294a52939ca7394a719ce5294a3494e5494651,[w0,w1,w2,w4,w10,w5,w6]⟩
private def sOne190 : Snapshot := ⟨true,11,10,1,0x4a5294a7394a52946528c6539467394e52a52729ca739c65294a7094e5294a128c65494651,[w0,w1,w2,w3,w4,w10,w5,w6]⟩
private def sOne200 : Snapshot := ⟨true,11,10,1,0x4e7294e5294e5394a5294a75a46739d2529ca7394a539ca728ca7194a5294a348c63294651,[w0,w1,w2,w4,w10,w5,w6,w8]⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne14 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne14 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne15 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne15 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne38 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne38 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne39 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne39 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne43 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne43 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne44 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne44 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne46 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne46 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne47 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne47 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne55 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne55 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne56 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne56 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne58 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne58 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne59 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne59 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne66 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne66 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne67 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne67 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne68 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne68 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne69 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne69 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne70 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne70 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne71 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne71 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne72 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne72 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne73 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne73 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne74 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne74 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne75 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne75 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne76 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne76 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne77 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne77 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne78 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne78 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne79 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne79 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne80 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne80 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne81 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne81 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne82 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne82 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne83 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne83 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne84 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne84 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne85 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne85 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne86 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne86 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne87 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne87 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne88 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne88 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne89 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne89 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne190 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne190 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne200 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne200 = false := by decide +kernel
private def cOne90 : List Snapshot := [sOne190,sOne200]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hOne90 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sOne90 = false := by
  rw [children_ok _ _ _ _ cOne90 _ (by
    intro s hs
    simp only [cOne90, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact hOne190
    · exact hOne200)]
  decide +kernel
private def rootOne : List Snapshot := [sOne14,sOne15,sOne38,sOne39,sOne43,sOne44,sOne46,sOne47,sOne55,sOne56,sOne58,sOne59,sOne66,sOne67,sOne68,sOne69,sOne70,sOne71,sOne72,sOne73,sOne74,sOne75,sOne76,sOne77,sOne78,sOne79,sOne80,sOne81,sOne82,sOne83,sOne84,sOne85,sOne86,sOne87,sOne88,sOne89,sOne90]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem chOne : chk [] rtp 0 12 1 FF 1 = false := by
  rw [front_eq _ _ _ _ rootOne (by
    intro s hs
    simp only [rootOne, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hOne14
    · exact hOne15
    · exact hOne38
    · exact hOne39
    · exact hOne43
    · exact hOne44
    · exact hOne46
    · exact hOne47
    · exact hOne55
    · exact hOne56
    · exact hOne58
    · exact hOne59
    · exact hOne66
    · exact hOne67
    · exact hOne68
    · exact hOne69
    · exact hOne70
    · exact hOne71
    · exact hOne72
    · exact hOne73
    · exact hOne74
    · exact hOne75
    · exact hOne76
    · exact hOne77
    · exact hOne78
    · exact hOne79
    · exact hOne80
    · exact hOne81
    · exact hOne82
    · exact hOne83
    · exact hOne84
    · exact hOne85
    · exact hOne86
    · exact hOne87
    · exact hOne88
    · exact hOne89
    · exact hOne90)]
  decide +kernel
private def n116 : Nat := 0xfffefffd7ffeafc0000000000001c00e00038000003800380001d403e100f807c03c000f0030600780000000000000000001e000f00078003c0030003000600003e003e081f0570030000c00180000000000000000000000000feafffebfffbfe0000000000000000000007f8000003fc0
private def n117 : Nat := 0x4210842108421080000040108401004010040100001000000002000000080010000000000
private def n118 : Nat := 0x2000000000000000000000000000000000000000000000000000
private def n119 : Nat := 0x4210842108421080000042108401004010040100001000000002000000080010000000000
private def w43 : W := ⟨n116,n117,n118,n119,0x0⟩
private def sTwo46 : Snapshot := ⟨false,12,10,1,0x4a5294a5294a5294e739c233942739ce729ca729d2929ce749ce51a52948461294e54a4a92,[w0,w1,w2,w4,w5,w6,w43]⟩
private def n120 : Nat := 0x1fffefffeffff00000000000000000000007ffeafc000000000007043821c1cb60038083808380e40e061383839ce0c0383000121c1800000000000000000106018300c180e0c0010001000200010601060087053001000040008000000001fdb00000000000000000000bfffbfe000000000000000000780038003c001c0
private def n121 : Nat := 0x4200840108020084000000108420084010000100020000010000008000000010800000000
private def n122 : Nat := 0x10000000000000000000000000000200000000000000000000000000000000000000000
private def n123 : Nat := 0x4210840108020084000000108420084210000100020000010000008000000010800000000
private def w44 : W := ⟨n120,n121,n122,n123,0x0⟩
private def sTwo51 : Snapshot := ⟨false,12,10,1,0x4a5294a7294e5394a749c6539425494e52a52729ce54a4e729d2919529494a1284a54a4a92,[w0,w1,w2,w44,w4,w5,w6]⟩
private def n124 : Nat := 0x1fffefffeffff000000000001b6000000000000000000000000007003801c1c360038c038c038ce00e0003800380e000380000101c00000000000000000001e001f000f800fc001c001c00380db1c001c000e0000000060300060000000001fdb003fffbfffbfe00000000000000000000000000000000787800003c3c000
private def n125 : Nat := 0x4200040100020084010002008420084000800000020080010040008000004000800000000
private def n126 : Nat := 0x10800000000000000000000001000000000000000000000000000000000000000000000
private def n127 : Nat := 0x4210840100020084010002008421084000800000020080010040008000004000800000000
private def w45 : W := ⟨n124,n125,n126,n127,0x0⟩
private def sTwo55 : Snapshot := ⟨false,12,10,1,0x4a5294a729ce5394a92a46349425394e7394e94a4e53952929ca72952948c23484a54a4a92,[w0,w1,w2,w45,w4,w5,w6]⟩
private def n128 : Nat := 0x1fffc0000000000007fff7ffefffc00fffefffd7ffeafdb7efdffabfe8ff47fa3a380db473f473f4711d51ffd47ff47d1fff47ffbfcfa3ffe0000000000000000e1fee0ff707f703fbe3fbe3f7c7e0063ff63feb1ff57edbf1ecfd59f7ffbffdfc0006d80000000000feafffebfffbfeffffbfffdfefdfffff8787ffffc3c3fff
private def w46 : W := ⟨n128,n126,n125,n127,0x0⟩
private def sTwo56 : Snapshot := ⟨false,12,10,1,0x4a5294a729ce5394a92a46349425394e7394e94a4e53952929ca72952948c23484a54a4a92,[w0,w1,w46,w2,w4,w5,w6]⟩
private def n129 : Nat := 0xfffefffd0000001b7e0000000001800c0003000000300030000194039000c4060033800cc03c4006400000000000000000019c00cc00660033002e002e005c00039c039c818c04cdae180b00160000000000000000000000000feafffe0000000ffffbfffdfe00000000007c7800003e3c
private def n130 : Nat := 0x4010802108421080000040100401000210040000401000000002000000080000040000000
private def n131 : Nat := 0x200000000000000000000000020000000000000000000000000000000000000000000000
private def n132 : Nat := 0x4210802108421080000040100421000210040000401000000002000000080000040000000
private def w47 : W := ⟨n129,n130,n131,n132,0x0⟩
private def sTwo58 : Snapshot := ⟨false,12,10,1,0x4a5294e5294a5294e93a42539c2539d2529ca94a4a729d2939ce529d294846348c654a4a92,[w0,w1,w2,w4,w5,w6,w47]⟩
private def n133 : Nat := 0x1fffdfffefffeffff7fff7ffefffdb6000000007ffeafc000fdffabfefe77f3bfbcb6db7fcf7fcf7fde41fc6d7f3b79dfcc77f33bc1bbf9be0000000000000000fe62ff337f997fccbfd1bfd17fa2db7c637c623e7353201166f4d5e97ffbffdfdfdb6dbfffbfffbfe0000000bfffbfe00000000000fdffffffff8387ffffc1c3
private def w48 : W := ⟨n133,n131,n130,n132,0x0⟩
private def sTwo60 : Snapshot := ⟨false,12,10,1,0x4a5294e5294a5294e93a42539c2539d2529ca94a4a729d2939ce529d294846348c654a4a92,[w48,w0,w1,w2,w4,w5,w6]⟩
private def n134 : Nat := 0x1fffe000000007fff7ffefffdb6fffe00007ffe801b7efdffabfe4f727b9392a0db27ef27ef27c9509e5d27b72509ebf27af9edf93d7e00000000000000009f5e9faf4bd74deba7dfa7df4fbedb5f5f5e5e2f6f42ed9f7eb7d56f7ff800001fd86dbfffbfffbfefe80000bfff800ffffbfffdfefdffffc77ff37fe3bff9bf
private def n135 : Nat := 0x2000000000000000000000000000000008000000000000000000000000000000000
private def n136 : Nat := 0x4200840008000000200000108000004010802100400000000800000400000010002000000
private def n137 : Nat := 0x4200842008000000200000108000004010802108400000000800000400000010002000000
private def w49 : W := ⟨n134,n135,n136,n137,0x0⟩
private def n138 : Nat := 0x7fff7ffefffdb6000000000000001b7efdffabfe0e3071838000db07c707c707c0001c1c07070001c3f070f9cc98387e00000000000000000e1e070f038701c387cf87cf0f9edb0c1f0c1e060f00ed8f7e33d4670000000000006dbfffbfffbfe00000000000000ffffbfffdfefdffff007f807e003fc03f
private def w50 : W := ⟨n138,n6,n5,n7,0x0⟩
private def sTwo61 : Snapshot := ⟨false,12,10,1,0x4a5394a5394e93a4e549c65394a959ce7294e5294a74a4e748d291a4a9494a1294e13a4a92,[w0,w2,w49,w4,w5,w6,w50]⟩
private def sTwo62 : Snapshot := ⟨false,12,10,1,0x4a5394a5394e93a4e549c65394a959ce7294e5294a74a4e748d291a4a9494a1294e13a4a92,[w0,w1,w2,w49,w4,w5,w6]⟩
private def n139 : Nat := 0x1fffc0000fffeffff000000000000000000fffd00002fc00000000000b085842c2d16005810581058168561a058485ad6140585021002c280000000000000000060a06050342832141820182030400020a021a09090150020004800900003ffdfc0030000000000000002fffe00003fe0000000000000000038800c801c400640
private def w51 : W := ⟨n139,n136,n135,n137,0x0⟩
private def sTwo63 : Snapshot := ⟨false,12,10,1,0x4a5394a5394e93a4e549c65394a959ce7294e5294a74a4e748d291a4a9494a1294e13a4a92,[w0,w1,w51,w2,w4,w5,w6]⟩
private def sTwo66 : Snapshot := ⟨false,12,10,1,0x4a5394a7494a73a4e739465394a959ce72a52729d2939ca5395291a527294a1294e5494692,[w0,w2,w4,w11,w5,w6,w50]⟩
private def sTwo67 : Snapshot := ⟨false,12,10,1,0x4a5394a7494a73a4e739465394a959ce72a52729d2939ca5395291a527294a1294e5494692,[w0,w1,w2,w4,w11,w5,w6]⟩
private def sTwo68 : Snapshot := ⟨false,12,10,1,0x4a5394a7494a73a4e739465394a959ce72a52729d2939ca5395291a527294a1294e5494692,[w0,w1,w12,w2,w4,w5,w6]⟩
private def n140 : Nat := 0x1fffdfffe0000ffff7fff0000fffd86fffe000100008fd87e01ff8bfedb36d9b6b632996da36de36d5b11b6bc6d9f6c5b66b6d9db65cb6cd60000000000000000a4c8aa64513254992ab428b459684245c844c8a2a4464434289d013a7ff8001fc0180c00003fff800008fffe3fff80000003fffc00000000c911151064888a88
private def w52 : W := ⟨n140,n22,n21,n23,0x0⟩
private def sTwo69 : Snapshot := ⟨false,12,10,1,0x4a5394a7494a73a4e739465394a959ce72a52729d2939ca5395291a527294a1294e5494692,[w0,w1,w52,w12,w2,w4,w6]⟩
private def n141 : Nat := 0xffff7fff7ffefffdb60000000000000fdb7efdffabfe1e30f1878412db0fc70fc70fc2003c3c0f0f0843c7f0f1f9cc9878fe00000000000000002efe2f7f17bf17df8fff8fff1ffedb0dff0dfe86ff57edbf7e3fd47f0000001fc01b6dbfffbfffbfe00afffebfffbfeffffbfffdfefdffffadffdfff56ffefff
private def n142 : Nat := 0x1004200800000000000000000000000000000000100000000000000000000
private def n143 : Nat := 0x4200840008000000010000108000004010000100000000000040000020000010000000020
private def n144 : Nat := 0x4200840008001004210800108000004010000100000000000040100020000010000000020
private def w53 : W := ⟨n141,n142,n143,n144,0x0⟩
private def sTwo71 : Snapshot := ⟨false,12,10,1,0x4a5394a7494e929ca529465394a959ce72a52729d294a4e749ca709ce5394a1294e54a4a51,[w0,w1,w2,w4,w5,w53,w6]⟩
private def n145 : Nat := 0x1fffdfffefffe000000000000000000fffefffd7ffea0000000000000e1c70e383ba40070387038701dd5c3c170f0779c38070e02316387000000000000000000d100d080684068203000300060000072007200390000000000c001807ffbffc01fc00000000000000fe0000000000000000000000000000052002000a9001000
private def w54 : W := ⟨n145,n143,n142,n144,0x0⟩
private def sTwo72 : Snapshot := ⟨false,12,10,1,0x4a5394a7494e929ca529465394a959ce72a52729d294a4e749ca709ce5394a1294e54a4a51,[w0,w1,w54,w2,w4,w5,w6]⟩
private def n146 : Nat := 0x1fffe0000000000000000000180000000007ffe800000fdff80004062031010a000208e208e200840804920322108086202300139013000000000000000001c401e220b100d88019101900320d21c421c400e6242001064348068000000001fd8003fffbfff8000000000bfff80000000000000fc00000707030403838182
private def n147 : Nat := 0x4200002100020084000000000420084000040008020000010000008000000000800100000
private def n148 : Nat := 0x8000000000000000000000000000000400000000000000000000000000000000
private def n149 : Nat := 0x4200002108020084000000000420084000040008420000010000008000000000800100000
private def w55 : W := ⟨n146,n147,n148,n149,0x0⟩
private def sTwo76 : Snapshot := ⟨false,12,10,1,0x4a539ce529525494a74a4a75a425494e739ca7394a54a52929529294e9494a3484a32a4a92,[w0,w1,w2,w4,w55,w5,w6]⟩
private def n150 : Nat := 0x1fffc0000fffeffff7fff7ffefffc36fffefffd00002fdb7e00002bfebf95fcafaf16db5f715f715fd7957fb45fcd5ed7f795fdcbfcc2fece0000000000000000e3bee1dd74ef7277be6ebe6f7cde0963bd63beb19d15edaf1acb55977ffbffdfc0036d800000003fefeafffe00003feffffbfffdfe01fffff8f8fcfbfc7c7e7d
private def w56 : W := ⟨n150,n148,n147,n149,0x0⟩
private def sTwo77 : Snapshot := ⟨false,12,10,1,0x4a539ce529525494a74a4a75a425494e739ca7394a54a52929529294e9494a3484a32a4a92,[w0,w1,w56,w2,w4,w5,w6]⟩
private def n151 : Nat := 0xfffe000000000000000030000000007ffe200000fc00200020410208088400104c100c108440404110201184084102200030812800000000000000001a2215130e890b4481418141028299182318220c531120014620d441000000001fc3003fff80003fe000000080003fe00000000000fdffff0686828603434143
private def n152 : Nat := 0x4200000100420084010000000420084000000000021080210800008020000000800000400
private def w57 : W := ⟨n151,n152,0x0,n152,0x0⟩
private def sTwo80 : Snapshot := ⟨false,12,10,1,0x4a539d2929ca5494a929ca75a425494e73a5294a4e5294e528d2929525394a3484a549c292,[w0,w1,w2,w4,w5,w57,w6]⟩
private def n153 : Nat := 0x1fffdfffe0000ffff7fff7ffefffd86fffefffd00008fdb7e01ff8bfedfb6fdb7b732db6fb36ff36f5b95bfbc6fdf6e5bf7b6fddbfdcb7ed60000000000000000e5dceaec717674bb3ebe3ebe7d7c4267dc67dcb3ac46cdbe38df01be7ffbffdfc0186d80003fff800feafffe3fff800ffffbfffdfe000000f9797d79fcbcbebc
private def w58 : W := ⟨n153,0x0,n152,n152,0x0⟩
private def sTwo81 : Snapshot := ⟨false,12,10,1,0x4a539d2929ca5494a929ca75a425494e73a5294a4e5294e528d2929525394a3484a549c292,[w0,w1,w58,w2,w4,w5,w6]⟩
private def n154 : Nat := 0xfffe00007ffe801800fdff800001600b00028000002e002e000150024900b205002a600ab0207805300000000000000000015800ae0056002b001d001c003800035a0258016e42cd1c1c07800e0000000000000000000000000fe80000bfff800ffffbfffc00fc000000007374000039ba
private def n155 : Nat := 0x4010802100421080000040100401000000040008021000000002000000080000000100000
private def n156 : Nat := 0x40000000000000000000000000000800000000000000000000000000000000000000
private def n157 : Nat := 0x4010842100421080000040100401000000840008021000000002000000080000000100000
private def w59 : W := ⟨n154,n155,n156,n157,0x0⟩
private def sTwo89 : Snapshot := ⟨false,12,10,1,0x4a7294a529ca5295273a42539c273a569494a7394e529d29494e52a4e948463494e32a4a92,[w0,w1,w2,w4,w5,w6,w59]⟩
private def n158 : Nat := 0xfffc7ffe200300fc00200000c00600018000001c001c0000c4014100600380194006201830032800000000000000000136009b004d0026800b800b00160002370336015b11a98b1602d4050000000000000000000000000fe2000080003feffff80001fefdffff00006aee00003577
private def n159 : Nat := 0x4010802100421080010040100401000000040000001080210802000020080000000000400
private def w60 : W := ⟨n158,n159,0x0,n159,0x0⟩
private def sTwo97 : Snapshot := ⟨false,12,10,1,0x4a7294e52a4a52952929c2539c273a56949ca94a529294e528ce52a52538463494e549c292,[w0,w1,w2,w4,w5,w6,w60]⟩
private def n160 : Nat := 0x1fffe000000007fff0000000180fffefffd7ffeafdb7efdffabfe49f24f9213a09024bf24bf2409d493fd24ff27c93ff24ff93df927fe00000000000000009dfe9eff4b7f4dbfa7bfa5bf4b7ed25fff5ffeafff57edbf7ebfd57f7ff800001fd86c3fffbfff800feafffebfffbfeffffbfffdfefdffffc7777fffe3bbbfff
private def n161 : Nat := 0x2100000000000000000000000000040000000000000000000000000000000000000
private def n162 : Nat := 0x200040008000000210002008020000000802100400080000840000400004000002000000
private def n163 : Nat := 0x200042108000000210002008020000000842100400080000840000400004000002000000
private def w61 : W := ⟨n160,n161,n162,n163,0x0⟩
private def sTwo101 : Snapshot := ⟨false,12,10,1,0x4e539ca5294e739d252a463494654a569494a529ca73952948ca72a4a948c23494e13a4a92,[w0,w1,w2,w61,w4,w5,w6]⟩
private def n164 : Nat := 0x1fffc0000fffeffff00007ffefffc3600000000000000000000000000b605b02dac164b5b405b405bd6016c005b005816c005b002c002d8000000000000000000620061003480324018401a40348009200020001000000000004000800003ffdfc00301800000003fe0000000000000000000000000000000388880001c444000
private def w62 : W := ⟨n164,n162,n161,n163,0x0⟩
private def sTwo102 : Snapshot := ⟨false,12,10,1,0x4e539ca5294e739d252a463494654a569494a529ca73952948ca72a4a948c23494e13a4a92,[w0,w1,w62,w2,w4,w5,w6]⟩
private def n165 : Nat := 0xfffe000000007ffe000030fffefffd7ffeafdb7efdffabfe25f12f890b8442127f123f1285d44bfd12ff17c4bff12ff8bc7897fe00000000000000005bfe55ff2eff2b7f957f977f26fe993bff3bfe9dff57edbf5e6fd4df0003ffc01fc361bfff80003fefeafffebfffbfeffffbfffdfefdffff36eeffff9b777fff
private def n166 : Nat := 0x420000000000000000000000000000001000000000000000000000000000000
private def n167 : Nat := 0x200040000000000010802008020000000800000000084000040000001004000000008000
private def n168 : Nat := 0x200040000420000010802008020000000800000001084000040000001004000000008000
private def w63 : W := ⟨n165,n166,n167,n168,0x0⟩
private def sTwo106 : Snapshot := ⟨false,12,10,1,0x4e539ca73a4a539d2929463494654a569494e94a529294a7394a72a52728c23494e5494692,[w0,w1,w2,w4,w63,w5,w6]⟩
private def n169 : Nat := 0x1fffdfffe0000ffff7fff0000fffd8600000000000000000000000000da06d036b432996d806dc06d5a01b4006d00681b4006d003418368000000000000000000a400aa00510054802a802880590042440044002200000000209001207ff8001fc0180c00003fff8000000000000000000000000000000000c911000064888000
private def w64 : W := ⟨n169,n167,n166,n168,0x0⟩
private def sTwo107 : Snapshot := ⟨false,12,10,1,0x4e539ca73a4a539d2929463494654a569494e94a529294a7394a72a52728c23494e5494692,[w0,w1,w64,w2,w4,w5,w6]⟩
private def n170 : Nat := 0xfffefffd7ffeafdb7efdffabfe01f00f80038000003f003f0001d403fd00ff07c03ff00ff83c7807fe000000000000000001fe00ff007f003f803f803f007e0003ff03fe81ff57edbf1e0fd41f0000000000000000000000000feafffebfffbfeffffbfffdfefdffff00007ffe00003fff
private def w65 : W := ⟨n170,n2,n1,n3,0x0⟩
private def sTwo110 : Snapshot := ⟨false,12,10,1,0x4e539ca73a4e7294e729c63494654a569494e94a5293952949ca519ce538c23494e54a4a51,[w1,w2,w4,w5,w13,w6,w65]⟩
private def sTwo111 : Snapshot := ⟨false,12,10,1,0x4e539ca73a4e7294e729c63494654a569494e94a5293952949ca519ce538c23494e54a4a51,[w0,w1,w2,w4,w5,w13,w6]⟩
private def sTwo112 : Snapshot := ⟨false,12,10,1,0x4e539ca73a4e7294e729c63494654a569494e94a5293952949ca519ce538c23494e54a4a51,[w0,w1,w14,w2,w4,w5,w6]⟩
private def n171 : Nat := 0x1fffefffeffff7fff00000001b6fffe00007ffeafd800fdffabfe7973cb9e1eb6903cef3cef3ccf50f26d3cbb3dcf2e73cbb921f9e5be00000000000000009f7a9fbf4fdf4fefa7dda5dd4bbadb5f7b5e7a2f7f53ed1d7eb7d56f7ff800001fdb6c3fffbfffbfefe80000bfffbfeffffbfffc00fdffffc7f7f3f7e3fbf9fb
private def n172 : Nat := 0x100000000000000000000000000000000020000000000000000000000000000000
private def n173 : Nat := 0x10840008000000200000000001000210802100400000000800000400000000042000000
private def n174 : Nat := 0x10840108000000200000000001000210802100420000000800000400000000042000000
private def w66 : W := ⟨n171,n172,n173,n174,0x0⟩
private def n175 : Nat := 0x1fffefffeffff000000000001b6000000007ffeafc000fdffabfe7073839c1cb60038cf38cf38ce40e06d383b39ce0c7383380139c1be00000000000000001e621f330f990fcc81d181d103a2db1c631c620e735320116634d469000000001fdb003fffbfffbfe0000000bfffbfe00000000000fdffff0787838603c3c1c3
private def w67 : W := ⟨n175,n10,n9,n11,0x0⟩
private def sTwo114 : Snapshot := ⟨false,12,10,1,0x4e7294a72952749ce54a4a75a46739d25294e529ca54a52938d2929ca9494a348c613a4a92,[w0,w1,w66,w67,w4,w5,w6]⟩
private def sTwo115 : Snapshot := ⟨false,12,10,1,0x4e7294a72952749ce54a4a75a46739d25294e529ca54a52938d2929ca9494a348c613a4a92,[w0,w1,w2,w66,w4,w5,w6]⟩
private def n176 : Nat := 0x1fffc00000000000000007ffefffc000000fffd000000037e0000000086843421a1004b431043104310850d9043444210d1843442dc021a400000000000000000608460403020301018221a223444002084218490800400a2004800900003ffdfc0000180000000000002fffe0000000000000001fe00000038080c081c040604
private def w68 : W := ⟨n176,n173,n172,n174,0x0⟩
private def sTwo116 : Snapshot := ⟨false,12,10,1,0x4e7294a72952749ce54a4a75a46739d25294e529ca54a52938d2929ca9494a348c613a4a92,[w0,w1,w2,w68,w4,w5,w6]⟩
private def sTwo119 : Snapshot := ⟨false,12,10,1,0x4e729529394e549ce9394a75a46739d252a5294a4a739ca72952929d27294a348c65494692,[w0,w1,w15,w67,w4,w5,w6]⟩
private def sTwo120 : Snapshot := ⟨false,12,10,1,0x4e729529394e549ce9394a75a46739d252a5294a4a739ca72952929d27294a348c65494692,[w0,w1,w2,w15,w4,w5,w6]⟩
private def sTwo121 : Snapshot := ⟨false,12,10,1,0x4e729529394e549ce9394a75a46739d252a5294a4a739ca72952929d27294a348c65494692,[w0,w1,w2,w16,w4,w5,w6]⟩
private def sTwo124 : Snapshot := ⟨false,12,10,1,0x4e72952939527394a729ca75a46739d252a5294a4a74a52939ca7194e5394a348c654a4a51,[w0,w1,w17,w67,w4,w5,w6]⟩
private def sTwo125 : Snapshot := ⟨false,12,10,1,0x4e72952939527394a729ca75a46739d252a5294a4a74a52939ca7194e5394a348c654a4a51,[w0,w1,w2,w17,w4,w5,w6]⟩
private def sTwo126 : Snapshot := ⟨false,12,10,1,0x4e72952939527394a729ca75a46739d252a5294a4a74a52939ca7194e5394a348c654a4a51,[w0,w1,w2,w18,w4,w5,w6]⟩
private def n177 : Nat := 0x1fffdfffefffe00007fff7ffe0001b0fffefffd7ffea01b00fc0023feedd76ebb3ba4d276fd76bd769dd5dbc576f1779dbb576eabb9f3b72a0000000000000000d910d4886a446922350835086210907a107a103d0800890850e201c47ffbffc01fc0603fff8000000fe000000000000ffff800000000000052222020a9111010
private def w69 : W := ⟨n177,n26,n25,n27,0x0⟩
private def sTwo127 : Snapshot := ⟨false,12,10,1,0x4e72952939527394a729ca75a46739d252a5294a4a74a52939ca7194e5394a348c654a4a51,[w0,w1,w69,w2,w18,w4,w5]⟩
private def n178 : Nat := 0xfffe000000007ffe0000300000fffc000020030000002000248124090904421250121012848449001240128491012400980092080000000000000000422641112489224490429243248609202521261011112083024054810003ffc0000301800000003fe002000000003fe000000001fe01ffff3088888a18444445
private def n179 : Nat := 0x40008420000210000000000000000802100401080210800000420000000002000400
private def w70 : W := ⟨n178,n179,0x0,n179,0x0⟩
private def sTwo130 : Snapshot := ⟨false,12,10,1,0x5294a4a7394a54a52529ca75a4a95a569494e529ca7294e528d292a4a5394a3494e139c292,[w0,w1,w2,w4,w5,w70,w6]⟩
private def n180 : Nat := 0x1fffdfffe0000ffff7fff0000fffd86fffe00017ffe8fd87efdff8bfedb76dbb6b6b2996daf6def6d5b51b6fd6dbf6d5b6ef6dbfb65fb6df60000000000000000bdd8beee5b765dbb2fbd2dbc5b78d25fda5ed8afee46cd3c7cbf817e7ff8001fdfd86c3fffbfff800fe8fffebfff800ffffbfffc00fc0000cf777775e7bbbbba
private def w71 : W := ⟨n180,0x0,n179,n179,0x0⟩
private def sTwo132 : Snapshot := ⟨false,12,10,1,0x5294a4a7394a54a52529ca75a4a95a569494e529ca7294e528d292a4a5394a3494e139c292,[w0,w1,w71,w2,w4,w5,w6]⟩
private def sTwo133 : Snapshot := ⟨false,12,10,1,0x5294a4a7394a54a52529ca75a4a95a569494e529ca7294e528d292a4a5394a3494e139c292,[w0,w1,w71,w52,w2,w4,w6]⟩
private def n181 : Nat := 0xffff00000000fffc060000000000000fc07e0000080012009004841209090009400942002430090c084244809140440048c4000000000000000022a6215114a9125488628a6314c60900a501a680911520a3020854110000001fc00301800000003fe002fffe00003fe000000001fe01ffff28888c8a14444645
private def n182 : Nat := 0x40008001084200800000000000000802100400000000802108401000000002000001
private def w72 : W := ⟨n181,n182,0x0,n182,0x0⟩
private def sTwo134 : Snapshot := ⟨false,12,10,1,0x5294a4a739529294a5394a75a4a95a569494e529ca74a52948ce5094a7294a3494e13a4a70,[w0,w1,w2,w4,w5,w6,w72]⟩
private def n183 : Nat := 0x1fffdfffefffe00007fff7ffe0001b0fffefffd7ffea01b00fdffa3feedf76fbb3ba4d276ff76bf769dd5dbcd76f3779dbb776ebbb9fbb73a0000000000000000dd58deae6b566dab379d359c6b38d27f5a7e583f6e42cd1c7cf781ee7ffbffc01fd86c3fffbfff800fe80000bfff800ffffbfffc00fc0000d7777375ebbbb9ba
private def w73 : W := ⟨n183,0x0,n182,n182,0x0⟩
private def sTwo136 : Snapshot := ⟨false,12,10,1,0x5294a4a739529294a5394a75a4a95a569494e529ca74a52948ce5094a7294a3494e13a4a70,[w0,w1,w73,w2,w4,w5,w6]⟩
private def sTwo139 : Snapshot := ⟨false,12,10,1,0x5294a4e529ce74a527394a75a4a95a56949ca7394e539ca738d292a4e7294a3494e3294692,[w0,w1,w2,w4,w19,w5,w6]⟩
private def sTwo140 : Snapshot := ⟨false,12,10,1,0x5294a4e529ce74a527394a75a4a95a56949ca7394e539ca738d292a4e7294a3494e3294692,[w0,w1,w20,w2,w4,w5,w6]⟩
private def n184 : Nat := 0x1fffc0000fffeffff00007ffefffc360000fffd00002fc37e00002bfeb695b4adad164b5b515b515bd6856db45b4d5ad6d595b54adc02dace000000000000000062a6615134a9325498629a6334c60920a521a690911520a3024854910003ffdfc00301800000003fe002fffe00003fe000000001fe01ffff38888c8a1c444645
private def w74 : W := ⟨n184,n18,n17,n19,0x0⟩
private def sTwo141 : Snapshot := ⟨false,12,10,1,0x5294a4e529ce74a527394a75a4a95a56949ca7394e539ca738d292a4e7294a3494e3294692,[w0,w1,w20,w74,w2,w5,w6]⟩
private def sTwo142 : Snapshot := ⟨false,12,10,1,0x5294a4e529ce74a527394a75a4a95a56949ca7394e539ca738d292a4e7294a3494e3294692,[w0,w1,w52,w2,w4,w19,w6]⟩
private def sTwo144 : Snapshot := ⟨false,12,10,1,0x5294a4e529d2939ce529ca75a4a95a56949ca7394e54a529494a719ca5394a3494e32a4a51,[w0,w1,w2,w4,w21,w5,w6]⟩
private def sTwo145 : Snapshot := ⟨false,12,10,1,0x5294a4e529d2939ce529ca75a4a95a56949ca7394e54a529494a719ca5394a3494e32a4a51,[w0,w1,w22,w2,w4,w5,w6]⟩
private def sTwo146 : Snapshot := ⟨false,12,10,1,0x5294a4e529d2939ce529ca75a4a95a56949ca7394e54a529494a719ca5394a3494e32a4a51,[w0,w1,w22,w74,w2,w5,w6]⟩
private def sTwo147 : Snapshot := ⟨false,12,10,1,0x5294a4e529d2939ce529ca75a4a95a56949ca7394e54a529494a719ca5394a3494e32a4a51,[w0,w1,w69,w2,w4,w21,w5]⟩
private def n185 : Nat := 0xfffe000000007ffe0000300000fffc7ffe200300fc00200024c12609098442125c121c1284c449411260138499412620983093280000000000000000591054882a442922150815082210903a103a101d08008908506200c40003ffc01fc0603fff8000000fe000000000000ffff80000000000001222202089111010
private def n186 : Nat := 0x420000010000000000000000000000001080210840000020000000000000420
private def n187 : Nat := 0x800000000000000000000000000000000000001000000000000000
private def n188 : Nat := 0x420000010800000000000000000000001080210840000021000000000000420
private def w75 : W := ⟨n185,n186,n187,n188,0x0⟩
private def sTwo150 : Snapshot := ⟨false,12,10,1,0x5294a5294a4a539ce7294a75a4a95a5694a5294a529294e528ca719ce5294a3494e549c251,[w0,w1,w2,w4,w5,w75,w6]⟩
private def n189 : Nat := 0x1fffdfffe0000ffff7fff0000fffd86fffe000100008fd87e01ff8bfedb36d9b6b632996da36de36d5b11b6bc6d9f6c5b66b6d9db65cb6cd60000000000000000a6eeab7755bb56ddaaf7aaf75dee4b45ef45eea2f75764b72e9dd53b7ff8001fc01b0d80003fffbfe00afffebfffbfe00003fffdfefdffffeddddfdf76eeefef
private def w76 : W := ⟨n189,n187,n186,n188,0x0⟩
private def sTwo151 : Snapshot := ⟨false,12,10,1,0x5294a5294a4a539ce7294a75a4a95a5694a5294a529294e528ca719ce5294a3494e549c251,[w0,w1,w76,w2,w4,w5,w6]⟩
private def n190 : Nat := 0xffff00000000fffc060000000000000fc07e01ff880012209104841209090209420942002438090e084244a09150440848d4000000000000000024c82a64113214990ab408b419684205c804c882a4464434281d003a0000001fc0180c00003fff800008fffe3fff80000003fffc000000008911151044888a88
private def n191 : Nat := 0x1084200800000000000000000000000004000002108401000000000008001
private def n192 : Nat := 0x10000000000000000000000000000000000000020000000000000000
private def n193 : Nat := 0x1084210800000000000000000000000004000002108421000000000008001
private def w77 : W := ⟨n190,n191,n192,n193,0x0⟩
private def sTwo154 : Snapshot := ⟨false,12,10,1,0x5294a5294a4e7294a5294a75a4a95a5694a5294a52939ca7394e5094a5294a3494e5494670,[w0,w1,w2,w4,w5,w6,w77]⟩
private def n194 : Nat := 0x1fffdfffefffe00007fff7ffe0001b0fffefffd7ffea01b00fc0023feedd76ebb3ba4d276fd76bd769dd5dbc576f1779dbb576eabb9f3b72a0000000000000000db36d59b6ecd6b66b54bb74b6696997a377b363d5b11a98b56e2d5c57ffbffc01fc361bfff80003fefe2000080003feffff80001fefdffff76eeeaefbb777577
private def w78 : W := ⟨n194,n192,n191,n193,0x0⟩
private def sTwo156 : Snapshot := ⟨false,12,10,1,0x5294a5294a4e7294a5294a75a4a95a5694a5294a52939ca7394e5094a5294a3494e5494670,[w0,w1,w78,w2,w4,w5,w6]⟩
private def sTwo158 : Snapshot := ⟨true,12,11,2,0x4a5294a5394a729ce729c233946549ce7294e729d29394e749ca71a52948c21294e54a4a92,[w0,w1,w23,w2,w4,w5,w6]⟩
private def sTwo159 : Snapshot := ⟨true,12,11,2,0x4a5294a7294e5394e92a4634942539d25294e94a4a73952939ca729d2948c2348c654a4a92,[w0,w1,w2,w24,w4,w5,w6]⟩
private def sTwo160 : Snapshot := ⟨true,12,11,2,0x4a5294a7394e739ca749c6539467394e52a52729ca74a4e739d2919d29494a128c654a4a92,[w0,w1,w2,w3,w4,w5,w6]⟩
private def sTwo161 : Snapshot := ⟨true,12,11,2,0x4a5294e529ca5294a93a42539c25394e739ca94a4e529d2929ce52952948463484a54a4a92,[w25,w0,w1,w2,w4,w5,w6]⟩
private def sTwo162 : Snapshot := ⟨true,12,11,2,0x4a5394a5294e93a4e549c65394a959ce729ca5294e54a4e7495291a4e9494a1294e32a4a92,[w0,w1,w2,w4,w7,w5,w6]⟩
private def sTwo163 : Snapshot := ⟨true,12,11,2,0x4a5394a7494a53a4e729465394a959ce72a52729d29294a528d291a525394a1294e549c292,[w0,w1,w2,w4,w5,w26,w6]⟩
private def sTwo164 : Snapshot := ⟨true,12,11,2,0x4a5394a7494e9294a539465394a959ce72a52729d294a4e749ce5094a7294a1294e54a4a70,[w0,w1,w2,w4,w5,w6,w27]⟩
private def sTwo165 : Snapshot := ⟨true,12,11,2,0x4a539ca729525494a54a4a75a425494e7394e529ca54a52928d29294a9494a3484a13a4a92,[w0,w1,w28,w2,w4,w5,w6]⟩
private def sTwo166 : Snapshot := ⟨true,12,11,2,0x4a539d2929ce5494a9394a75a425494e73a5294a4e539ca72952929527294a3484a5494692,[w0,w1,w29,w2,w4,w5,w6]⟩
private def sTwo167 : Snapshot := ⟨true,12,11,2,0x4a539d2929d25394a729ca75a425494e73a5294a4e54a52929ca7194e5394a3484a54a4a51,[w0,w1,w30,w2,w4,w5,w6]⟩
private def sTwo168 : Snapshot := ⟨true,12,11,2,0x4a7294a5294a5295253a42539c273a569494a529ca729d2948ce52a4a948463494e13a4a92,[w31,w0,w1,w2,w4,w5,w6]⟩
private def sTwo169 : Snapshot := ⟨true,12,11,2,0x4a7294e52a4a5294e729c2539c273a56949ca94a52929d2949ca519ce538463494e54a4a51,[w32,w0,w1,w2,w4,w5,w6]⟩
private def sTwo170 : Snapshot := ⟨true,12,11,2,0x4a7294e52a4a5295292942539c273a56949ca94a529294a7394e52a52728463494e5494692,[w33,w0,w1,w2,w4,w5,w6]⟩
private def sTwo171 : Snapshot := ⟨true,12,11,2,0x4e539ca529ce739d272a463494654a569494a7394e539529494a72a4e948c23494e32a4a92,[w0,w1,w2,w4,w34,w5,w6]⟩
private def sTwo172 : Snapshot := ⟨true,12,11,2,0x4e539ca73a4a539d2929c63494654a569494e94a529294e528ca72a52538c23494e549c292,[w0,w1,w2,w4,w5,w35,w6]⟩
private def sTwo173 : Snapshot := ⟨true,12,11,2,0x4e539ca73a4e7294a529463494654a569494e94a5293952949ca5094a728c23494e54a4a70,[w0,w1,w2,w4,w5,w6,w36]⟩
private def sTwo174 : Snapshot := ⟨true,12,11,2,0x4e7294e52952749ce74a4a75a46739d2529ca7394a54a5293952929ce9494a348c632a4a92,[w0,w1,w2,w4,w5,w6,w8]⟩
private def sTwo175 : Snapshot := ⟨true,12,11,2,0x4e729529394a549ce929ca75a46739d252a5294a4a7294e528d2929d25394a348c6549c292,[w0,w1,w2,w4,w5,w6,w37]⟩
private def sTwo176 : Snapshot := ⟨true,12,11,2,0x4e72952939527294a5394a75a46739d252a5294a4a74a52939ce5094a7294a348c654a4a70,[w0,w1,w2,w4,w5,w6,w38]⟩
private def sTwo177 : Snapshot := ⟨true,12,11,2,0x5294a4a7394e74a525394a75a4a95a569494e529ca739ca738d292a4a7294a3494e1394692,[w0,w1,w2,w9,w4,w5,w6]⟩
private def sTwo178 : Snapshot := ⟨true,12,11,2,0x5294a4a73952939ce529ca75a4a95a569494e529ca74a52948ca719ca5394a3494e13a4a51,[w0,w1,w2,w39,w4,w5,w6]⟩
private def sTwo179 : Snapshot := ⟨true,12,11,2,0x5294a4e529ca54a52729ca75a4a95a56949ca7394e5294e528d292a4e5394a3494e329c292,[w0,w1,w2,w4,w5,w6,w40]⟩
private def sTwo180 : Snapshot := ⟨true,12,11,2,0x5294a4e529d29294a5394a75a4a95a56949ca7394e54a529494e5094a7294a3494e32a4a70,[w0,w1,w2,w4,w5,w6,w41]⟩
private def sTwo181 : Snapshot := ⟨true,12,11,2,0x5294a5294a4a5294a5294a75a4a95a5694a5294a529294e528ce5094a5294a3494e549c270,[w0,w1,w2,w4,w5,w6,w42]⟩
private def sTwo182 : Snapshot := ⟨true,12,11,2,0x5294a5294a4e739ce7294a75a4a95a5694a5294a52939ca7394a719ce5294a3494e5494651,[w0,w1,w2,w4,w10,w5,w6]⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo46 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo46 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo51 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo51 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo55 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo55 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo56 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo56 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo58 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo58 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo60 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo60 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo61 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo61 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo62 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo62 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo63 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo63 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo66 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo66 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo67 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo67 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo68 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo68 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo69 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo69 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo71 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo71 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo72 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo72 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo76 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo76 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo77 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo77 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo80 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo80 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo81 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo81 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo89 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo89 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo97 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo97 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo101 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo101 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo102 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo102 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo106 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo106 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo107 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo107 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo110 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo110 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo111 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo111 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo112 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo112 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo114 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo114 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo115 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo115 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo116 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo116 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo119 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo119 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo120 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo120 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo121 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo121 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo124 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo124 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo125 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo125 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo126 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo126 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo127 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo127 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo130 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo130 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo132 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo132 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo133 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo133 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo134 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo134 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo136 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo136 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo139 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo139 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo140 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo140 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo141 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo141 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo142 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo142 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo144 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo144 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo145 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo145 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo146 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo146 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo147 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo147 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo150 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo150 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo151 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo151 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo154 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo154 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo156 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo156 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo158 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo158 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo159 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo159 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo160 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo160 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo161 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo161 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo162 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo162 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo163 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo163 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo164 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo164 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo165 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo165 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo166 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo166 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo167 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo167 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo168 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo168 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo169 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo169 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo170 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo170 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo171 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo171 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo172 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo172 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo173 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo173 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo174 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo174 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo175 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo175 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo176 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo176 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo177 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo177 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo178 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo178 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo179 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo179 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo180 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo180 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo181 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo181 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hTwo182 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sTwo182 = false := by decide +kernel
private def rootTwo : List Snapshot := [sTwo46,sTwo51,sTwo55,sTwo56,sTwo58,sTwo60,sTwo61,sTwo62,sTwo63,sTwo66,sTwo67,sTwo68,sTwo69,sTwo71,sTwo72,sTwo76,sTwo77,sTwo80,sTwo81,sTwo89,sTwo97,sTwo101,sTwo102,sTwo106,sTwo107,sTwo110,sTwo111,sTwo112,sTwo114,sTwo115,sTwo116,sTwo119,sTwo120,sTwo121,sTwo124,sTwo125,sTwo126,sTwo127,sTwo130,sTwo132,sTwo133,sTwo134,sTwo136,sTwo139,sTwo140,sTwo141,sTwo142,sTwo144,sTwo145,sTwo146,sTwo147,sTwo150,sTwo151,sTwo154,sTwo156,sTwo158,sTwo159,sTwo160,sTwo161,sTwo162,sTwo163,sTwo164,sTwo165,sTwo166,sTwo167,sTwo168,sTwo169,sTwo170,sTwo171,sTwo172,sTwo173,sTwo174,sTwo175,sTwo176,sTwo177,sTwo178,sTwo179,sTwo180,sTwo181,sTwo182]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem chTwo : chk [] rtp 0 12 2 FF 1 = false := by
  rw [front_eq _ _ _ _ rootTwo (by
    intro s hs
    simp only [rootTwo, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hTwo46
    · exact hTwo51
    · exact hTwo55
    · exact hTwo56
    · exact hTwo58
    · exact hTwo60
    · exact hTwo61
    · exact hTwo62
    · exact hTwo63
    · exact hTwo66
    · exact hTwo67
    · exact hTwo68
    · exact hTwo69
    · exact hTwo71
    · exact hTwo72
    · exact hTwo76
    · exact hTwo77
    · exact hTwo80
    · exact hTwo81
    · exact hTwo89
    · exact hTwo97
    · exact hTwo101
    · exact hTwo102
    · exact hTwo106
    · exact hTwo107
    · exact hTwo110
    · exact hTwo111
    · exact hTwo112
    · exact hTwo114
    · exact hTwo115
    · exact hTwo116
    · exact hTwo119
    · exact hTwo120
    · exact hTwo121
    · exact hTwo124
    · exact hTwo125
    · exact hTwo126
    · exact hTwo127
    · exact hTwo130
    · exact hTwo132
    · exact hTwo133
    · exact hTwo134
    · exact hTwo136
    · exact hTwo139
    · exact hTwo140
    · exact hTwo141
    · exact hTwo142
    · exact hTwo144
    · exact hTwo145
    · exact hTwo146
    · exact hTwo147
    · exact hTwo150
    · exact hTwo151
    · exact hTwo154
    · exact hTwo156
    · exact hTwo158
    · exact hTwo159
    · exact hTwo160
    · exact hTwo161
    · exact hTwo162
    · exact hTwo163
    · exact hTwo164
    · exact hTwo165
    · exact hTwo166
    · exact hTwo167
    · exact hTwo168
    · exact hTwo169
    · exact hTwo170
    · exact hTwo171
    · exact hTwo172
    · exact hTwo173
    · exact hTwo174
    · exact hTwo175
    · exact hTwo176
    · exact hTwo177
    · exact hTwo178
    · exact hTwo179
    · exact hTwo180
    · exact hTwo181
    · exact hTwo182)]
  decide +kernel
private def sThree201 : Snapshot := ⟨true,12,11,3,0x4a5294a7294e5394e92a4634942539d25294e94a4a73952939ca729d2948c2348c654a4a92,[w0,w1,w2,w24,w4,w5,w6]⟩
private def sThree203 : Snapshot := ⟨true,12,11,3,0x4a5294e529ca5294a93a42539c25394e739ca94a4e529d2929ce52952948463484a54a4a92,[w25,w0,w1,w2,w4,w5,w6]⟩
private def sThree207 : Snapshot := ⟨true,12,11,3,0x4a539ca729525494a54a4a75a425494e7394e529ca54a52928d29294a9494a3484a13a4a92,[w0,w1,w28,w2,w4,w5,w6]⟩
private def sThree208 : Snapshot := ⟨true,12,11,3,0x4a539d2929ce5494a9394a75a425494e73a5294a4e539ca72952929527294a3484a5494692,[w0,w1,w29,w2,w4,w5,w6]⟩
private def sThree209 : Snapshot := ⟨true,12,11,3,0x4a539d2929d25394a729ca75a425494e73a5294a4e54a52929ca7194e5394a3484a54a4a51,[w0,w1,w30,w2,w4,w5,w6]⟩
private def sThree210 : Snapshot := ⟨true,12,11,3,0x4a7294a5294a5295253a42539c273a569494a529ca729d2948ce52a4a948463494e13a4a92,[w31,w0,w1,w2,w4,w5,w6]⟩
private def sThree211 : Snapshot := ⟨true,12,11,3,0x4a7294e52a4a5294e729c2539c273a56949ca94a52929d2949ca519ce538463494e54a4a51,[w32,w0,w1,w2,w4,w5,w6]⟩
private def sThree212 : Snapshot := ⟨true,12,11,3,0x4a7294e52a4a5295292942539c273a56949ca94a529294a7394e52a52728463494e5494692,[w33,w0,w1,w2,w4,w5,w6]⟩
private def sThree213 : Snapshot := ⟨true,12,11,3,0x4e539ca529ce739d272a463494654a569494a7394e539529494a72a4e948c23494e32a4a92,[w0,w1,w2,w4,w34,w5,w6]⟩
private def sThree214 : Snapshot := ⟨true,12,11,3,0x4e539ca73a4a539d2929c63494654a569494e94a529294e528ca72a52538c23494e549c292,[w0,w1,w2,w4,w5,w35,w6]⟩
private def sThree215 : Snapshot := ⟨true,12,11,3,0x4e539ca73a4e7294a529463494654a569494e94a5293952949ca5094a728c23494e54a4a70,[w0,w1,w2,w4,w5,w6,w36]⟩
private def sThree216 : Snapshot := ⟨true,12,11,3,0x4e7294e52952749ce74a4a75a46739d2529ca7394a54a5293952929ce9494a348c632a4a92,[w0,w1,w2,w4,w5,w6,w8]⟩
private def sThree217 : Snapshot := ⟨true,12,11,3,0x4e729529394a549ce929ca75a46739d252a5294a4a7294e528d2929d25394a348c6549c292,[w0,w1,w2,w4,w5,w6,w37]⟩
private def sThree218 : Snapshot := ⟨true,12,11,3,0x4e72952939527294a5394a75a46739d252a5294a4a74a52939ce5094a7294a348c654a4a70,[w0,w1,w2,w4,w5,w6,w38]⟩
private def sThree219 : Snapshot := ⟨true,12,11,3,0x5294a4a7394e74a525394a75a4a95a569494e529ca739ca738d292a4a7294a3494e1394692,[w0,w1,w2,w9,w4,w5,w6]⟩
private def sThree220 : Snapshot := ⟨true,12,11,3,0x5294a4a73952939ce529ca75a4a95a569494e529ca74a52948ca719ca5394a3494e13a4a51,[w0,w1,w2,w39,w4,w5,w6]⟩
private def sThree221 : Snapshot := ⟨true,12,11,3,0x5294a4e529ca54a52729ca75a4a95a56949ca7394e5294e528d292a4e5394a3494e329c292,[w0,w1,w2,w4,w5,w6,w40]⟩
private def sThree222 : Snapshot := ⟨true,12,11,3,0x5294a4e529d29294a5394a75a4a95a56949ca7394e54a529494e5094a7294a3494e32a4a70,[w0,w1,w2,w4,w5,w6,w41]⟩
private def sThree223 : Snapshot := ⟨true,12,11,3,0x5294a5294a4a5294a5294a75a4a95a5694a5294a529294e528ce5094a5294a3494e549c270,[w0,w1,w2,w4,w5,w6,w42]⟩
private def sThree224 : Snapshot := ⟨true,12,11,3,0x5294a5294a4e739ce7294a75a4a95a5694a5294a52939ca7394a719ce5294a3494e5494651,[w0,w1,w2,w4,w10,w5,w6]⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree201 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree201 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree203 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree203 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree207 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree207 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree208 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree208 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree209 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree209 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree210 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree210 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree211 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree211 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree212 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree212 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree213 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree213 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree214 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree214 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree215 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree215 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree216 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree216 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree217 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree217 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree218 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree218 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree219 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree219 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree220 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree220 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree221 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree221 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree222 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree222 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree223 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree223 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem hThree224 : evalSnap (lz 0) (mz 0) (pL (rtp.map fun _ => 16)) 12 sThree224 = false := by decide +kernel
private def rootThree : List Snapshot := [sThree201,sThree203,sThree207,sThree208,sThree209,sThree210,sThree211,sThree212,sThree213,sThree214,sThree215,sThree216,sThree217,sThree218,sThree219,sThree220,sThree221,sThree222,sThree223,sThree224]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem chThree : chk [] rtp 0 12 3 FF 1 = false := by
  rw [front_eq _ _ _ _ rootThree (by
    intro s hs
    simp only [rootThree, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hThree201
    · exact hThree203
    · exact hThree207
    · exact hThree208
    · exact hThree209
    · exact hThree210
    · exact hThree211
    · exact hThree212
    · exact hThree213
    · exact hThree214
    · exact hThree215
    · exact hThree216
    · exact hThree217
    · exact hThree218
    · exact hThree219
    · exact hThree220
    · exact hThree221
    · exact hThree222
    · exact hThree223
    · exact hThree224)]
  decide +kernel
theorem atBudget {u : ℕ} {Q : List (ℕ × ℕ)} {Z L : ℕ} (hp : pOk Z Q = true) (hL : L + 1 ≤ 15) (hA : Imp [] Z L)
    (hI : ∀ e ∈ Q, ImpB [] e.1 e.2 u) (hc : chk [] Q Z L u FF 1 = false) : ImpB [] Z (L + 1) u := by
  intro q hq hs
  obtain ⟨k, hk, t, ht, S, hS, hl⟩ := hs.live
  by_cases hkt : k + t < L
  · exact hA (k + t) hkt (hl.sol.mono le_rfl hS)
  · have htu : t = u := by omega
    subst t
    obtain rfl : L = k + u := by omega
    exact imp_of_live (L := k + u + 1) (Or.inl rfl) hp hL hI (by omega) hS hl hA (Or.inr (one1 hc))
lemma atUp {u : ℕ} {B T : List (ℕ × ℕ)} (hB : ∀ e ∈ B, ImpB [] e.1 (e.2 + 1) u) (hT : ∀ e ∈ T, Imp [] e.1 e.2) :
    ∀ e ∈ up B T, ImpB [] e.1 e.2 u := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  change ImpB [] x.1 (bif B.any (fun y => Nat.beq y.1 x.1 && Nat.beq y.2 x.2) then x.2 + 1 else x.2) u
  cases hc : B.any (fun y => Nat.beq y.1 x.1 && Nat.beq y.2 x.2) with
  | false => exact (hT x hx).toB u
  | true =>
    obtain ⟨y, hy, hxy⟩ := List.any_eq_true.1 hc
    rw [Bool.and_eq_true] at hxy
    obtain rfl : y = x := Prod.ext (Nat.eq_of_beq_eq_true hxy.1) (Nat.eq_of_beq_eq_true hxy.2)
    exact hB y hy
noncomputable def checkAt (u : ℕ) (B A T : List (ℕ × ℕ)) (e : ℕ × ℕ) : Bool :=
  A.any (fun x => Nat.beq x.1 e.1 && Nat.beq x.2 e.2) && pOk e.1 (up B (pr T e.1)) && Nat.ble (e.2 + 1) 15 &&
    !chk [] (up B (pr T e.1)) e.1 e.2 u FF 1
lemma tablesAt {u : ℕ} {B A T U : List (ℕ × ℕ)} (h : U.all (checkAt u B A T) = true) (hB : ∀ e ∈ B, ImpB [] e.1 (e.2 + 1) u)
    (hA : ∀ e ∈ A, Imp [] e.1 e.2) (hT : ∀ e ∈ T, Imp [] e.1 e.2) : ∀ e ∈ U, ImpB [] e.1 (e.2 + 1) u := by
  intro e he
  have h := List.all_eq_true.1 h e he
  simp only [checkAt, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true] at h
  obtain ⟨⟨⟨⟨x, hx, hx1, hx2⟩, hp⟩, hL⟩, hc⟩ := h
  obtain rfl : x = e := Prod.ext (Nat.eq_of_beq_eq_true hx1) (Nat.eq_of_beq_eq_true hx2)
  exact atBudget hp (Nat.le_of_ble_eq_true hL) (hA x hx) (atUp hB fun y hy => hT y (List.mem_of_mem_filter hy)) hc
lemma joinAt {u : ℕ} {A B : List (ℕ × ℕ)} (ha : ∀ e ∈ A, ImpB [] e.1 (e.2 + 1) u) (hb : ∀ e ∈ B, ImpB [] e.1 (e.2 + 1) u) :
    ∀ e ∈ A ++ B, ImpB [] e.1 (e.2 + 1) u := fun e he => (List.mem_append.1 he).elim (ha e) (hb e)
lemma allRaised (u : ℕ)
    (a : rb3.all (checkAt u [] rt3 []) = true)
    (b : rb2.all (checkAt u rb3 rt2 rt3) = true)
    (c : rb1.all (checkAt u (rb2 ++ rb3) rt1 (rt2 ++ rt3)) = true) :
    ∀ e ∈ rtp, ImpB [] e.1 e.2 u := by
  have h3 := tablesAt a (by simp) i3 (by simp)
  have h2 := tablesAt b h3 i2 i3
  have h1 := tablesAt c (joinAt h2 h3) i1 (apI i2 i3)
  exact atUp (joinAt (joinAt h1 h2) h3) ir
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raised2 : ∀ e ∈ rtp, ImpB [] e.1 e.2 2 := allRaised 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raised3 : ∀ e ∈ rtp, ImpB [] e.1 e.2 3 := allRaised 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma lowOther : okT [] rt 0 12 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11] = true := by decide +kernel
lemma rootLower (h0 : chk [] rt 0 11 0 FF 1 = false) (h1 : chk [] rt 0 11 1 FF 1 = false) : Imp [] 0 12 :=
  imp_ts (Or.inl rfl) root_p (by norm_num) ir (fun t ht => by
    have h := lowOther
    simp only [okT, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    interval_cases t
    · exact one h0
    · exact one h1
    · exact one h2
    · exact one h3
    · exact one h4
    · exact one h5
    · exact one h6
    · exact one h7
    · exact one h8
    · exact one h9
    · exact one h10
    · exact one h11)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma upperOther : okT [] rt 0 13 [4, 5, 6, 7, 8, 9, 10, 11, 12] = true := by decide +kernel
lemma highCounts {t : ℕ} (h4 : 4 ≤ t) (h12 : t ≤ 12) : chk [] rt 0 12 t FF 1 = false := by
  have ht : t ∈ ([4,5,6,7,8,9,10,11,12] : List ℕ) := by interval_cases t <;> decide
  have h := List.all_eq_true.1 upperOther t ht
  simpa only [Bool.not_eq_true'] using h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem shortWithNot (low : Imp [] 0 12)
    (oneCount : chk [] rtp 0 12 1 FF 1 = false)
    (twoCount : chk [] rtp 0 12 2 FF 1 = false)
    (threeCount : chk [] rtp 0 12 3 FF 1 = false)
    (D : Circuit) (hD : FanInTwo D) (hf : ∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y)
    (hn : ∃ g ∈ D.gates, g.op = GateOp.not) : 13 ≤ D.size := by
  by_contra! hs
  obtain ⟨k, hk, t, ht, S, hS, hl⟩ := (budgetBridge D hD hf).live
  have hsum := budgetSum D.gates
  have hpos := inversionPositive hn
  have hsize : D.size = D.gates.length := rfl
  have hlower : 12 ≤ k + t := by
    by_contra! h
    exact low _ h (hl.sol.mono le_rfl hS)
  have htotal : k + t = 12 := by omega
  have hmin : ∀ q < k + t, ¬Sol Z0 (mz 0) (tz 0) q (C (mz 0) (WZ [] 0)) := fun q hq => low q (by omega)
  have oneRaised := up_imp (apB (apB j1 j2) j3) ir
  by_cases h1 : t = 1
  · subst t
    exact imp_of_live (L := 13) (.inl rfl) rootp_p (by decide) oneRaised (by omega) hS hl hmin (.inr (one1 oneCount))
  by_cases h2 : t = 2
  · subst t
    exact imp_of_live (L := 13) (.inl rfl) rootp_p (by decide) raised2 (by omega) hS hl hmin (.inr (one1 twoCount))
  by_cases h3 : t = 3
  · subst t
    exact imp_of_live (L := 13) (.inl rfl) rootp_p (by decide) raised3 (by omega) hS hl hmin (.inr (one1 threeCount))
  exact imp_of_live (L := 13) (.inl rfl) root_p (by decide) (fun e he => (ir e he).toB t) (by omega) hS hl hmin
    (.inr (one1 (highCounts (by omega) (by omega))))
def table (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276676840 * 2 ^ 32 + 3936938120)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def witness : Circuit :=
  ⟨[⟨.and,[0,1]⟩, ⟨.or,[0,1]⟩, ⟨.and,[7,2]⟩, ⟨.and,[8,3]⟩, ⟨.or,[9,6]⟩,
    ⟨.and,[3,4]⟩, ⟨.or,[11,8]⟩, ⟨.and,[4,0]⟩, ⟨.or,[13,5]⟩, ⟨.and,[14,12]⟩,
    ⟨.or,[15,10]⟩, ⟨.or,[7,2]⟩, ⟨.and,[17,16]⟩], 18⟩

theorem shape : Monotone2 witness := by
  simp [Monotone2, witness]

theorem size : witness.size = 13 := rfl

theorem evaluation : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = table x := by
  decide +kernel

theorem table_eq : ∀ x : Fin 6 → Bool, table x = f x := by decide +kernel
theorem smallReplacement (h : ∀ D : Circuit, FanInTwo D →
    (∀ y : Fin 6 → Bool, D.eval (List.ofFn y) = f y) →
    (∃ g ∈ D.gates, g.op = GateOp.not) → 13 ≤ D.size) :
    ∀ s : ℕ, HasCircuitSize 6 table s → ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = table x := by
  intro s ⟨D, hv, hs, hf⟩
  by_cases hn : ∃ g ∈ D.gates, g.op = GateOp.not
  · exact ⟨witness,shape, by rw [size]; exact le_trans (h D hv (fun y => (hf y).trans (table_eq y)) hn) hs, evaluation⟩
  · refine ⟨D, fun g hg => ?_,hs,hf⟩
    obtain ⟨hop, len⟩ := hv g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    exact ⟨hop.imp_right (fun hh => hh.resolve_right (fun ne => hn ⟨g,hg,ne⟩)),len⟩
theorem minimalMonotone : ∀ s : ℕ, HasCircuitSize 6 table s → ∃ D : Circuit, Monotone2 D ∧ D.size ≤ s ∧ ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = table x :=
  smallReplacement (shortWithNot (rootLower chLowA chLowB) chOne chTwo chThree)
end PEqualNP.Outside.L_meta_45240

theorem PEqualNP.Outside.L_meta_45240 :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 3936938120) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  PEqualNP.Outside.L_meta_45240.minimalMonotone
