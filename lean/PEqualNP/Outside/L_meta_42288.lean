import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42288_aux

variable {A : Bool → ℕ → ℕ → Prop}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
lemma op_comm (d : Bool) (a b : ℕ) : op d a b = op d b a := by
  cases d <;> simp [op, Nat.and_comm, Nat.or_comm]
lemma op_bit (d : Bool) (a b i : ℕ) : (op d a b).testBit i =
    bif d then a.testBit i || b.testBit i else a.testBit i && b.testBit i := by
  cases d <;> simp [op]
lemma op_self (d : Bool) (a : ℕ) : op d a a = a := by cases d <;> simp [op]
def SymA (A : Bool → ℕ → ℕ → Prop) : Prop := ∀ d a b, A d a b → A d b a
def A0 : Bool → ℕ → ℕ → Prop := fun _ _ _ => True
lemma a0_symm : SymA A0 := fun _ _ _ _ => trivial
lemma a0_all (d : Bool) (a b : ℕ) : A0 d a b := trivial
def gkey (ra rb : ℕ) (d : Bool) : ℕ :=
  (bif Nat.ble ra rb then ra else rb) * 16 + (bif Nat.ble ra rb then rb else ra) * 2 + (bif d then 1 else 0)
lemma gkey_comm (ra rb : ℕ) (d : Bool) : gkey ra rb d = gkey rb ra d := by
  unfold gkey
  by_cases h1 : ra ≤ rb
  · by_cases h2 : rb ≤ ra
    · obtain rfl : ra = rb := by omega
      rfl
    · have b1 : Nat.ble ra rb = true := Nat.ble_eq_true_of_le h1
      have b2 : Nat.ble rb ra = false := Bool.eq_false_iff.2 fun h => h2 (Nat.le_of_ble_eq_true h)
      simp [b1, b2]
  · have h2 : rb ≤ ra := by omega
    have b1 : Nat.ble ra rb = false := Bool.eq_false_iff.2 fun h => h1 (Nat.le_of_ble_eq_true h)
    have b2 : Nat.ble rb ra = true := Nat.ble_eq_true_of_le h2
    simp [b1, b2]
def AR (R : ℕ → ℕ) : Bool → ℕ → ℕ → Prop := fun _ a b => R a = 0 ∨ R b = 0
def AL (R : ℕ → ℕ) (lb : ℕ) : Bool → ℕ → ℕ → Prop := fun d a b => R a = 0 ∨ R b = 0 ∨ lb ≤ gkey (R a) (R b) d
lemma AR.symm (R : ℕ → ℕ) : SymA (AR R) := fun _ _ _ h => Or.symm h
lemma AL.symm (R : ℕ → ℕ) (lb : ℕ) : SymA (AL R lb) := by
  intro d a b h
  rcases h with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · right; right; rwa [gkey_comm]
inductive Sol (A : Bool → ℕ → ℕ → Prop) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol A m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol A m T q (insert (a ^^^ m) S) → Sol A m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → A d a b →
      Sol A m T q (insert (op d a b) S) → Sol A m T (q + 1) S
lemma Sol.mono {m T q : ℕ} {S : Set ℕ} (h : Sol A m T q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → Sol A m T q' S' := by
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
lemma Sol.rel {A' : Bool → ℕ → ℕ → Prop} {m T q : ℕ} {S : Set ℕ} (h : Sol A m T q S)
    (hA : ∀ d a b, A d a b → A' d a b) : Sol A' m T q S := by
  induction h with
  | done h => exact .done h
  | un h _ ih => exact .un h ih
  | bi h1 h2 ha _ ih => exact .bi h1 h2 (hA _ _ _ ha) ih
lemma Sol.to0 {m T q : ℕ} {S : Set ℕ} (h : Sol A m T q S) : Sol A0 m T q S := h.rel fun _ _ _ _ => trivial
inductive Live (A : Bool → ℕ → ℕ → Prop) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live A m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live A m T k t (insert (a ^^^ m) U) →
      Live A m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → A d a b → Live A m T k t (insert (op d a b) U) →
      Live A m T (k + 1) t (insert a (insert b U))
lemma Live.t_le_k {m T k t : ℕ} {S : Finset ℕ} (h : Live A m T k t S) : t ≤ k := by
  induction h with
  | stop => omega
  | un _ ih => omega
  | bi _ _ _ ih => omega
lemma Live.rel {A' : Bool → ℕ → ℕ → Prop} {m T k t : ℕ} {S : Finset ℕ} (h : Live A m T k t S)
    (hA : ∀ d a b, A d a b → A' d a b) : Live A' m T k t S := by
  induction h with
  | stop => exact .stop
  | un _ ih => exact .un ih
  | bi hab hal _ ih => exact .bi hab (hA _ _ _ hal) ih
lemma Live.sol {m T k t : ℕ} {S : Finset ℕ} (h : Live A m T k t S) : Sol A0 m T k (S : Set ℕ) := by
  induction h with
  | stop => exact .done (by simp)
  | @un k t a U _ ih =>
    refine .un (a := a) (by simp) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
  | @bi k t d a b U _ _ _ ih =>
    refine .bi (d := d) (a := a) (b := b) (by simp) (by simp) (a0_all _ _ _) (ih.mono le_rfl ?_)
    intro x hx; simp at hx ⊢; tauto
lemma Sol.live {m T q : ℕ} {S : Set ℕ} (h : Sol A m T q S) :
    ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live A m T k t S0 := by
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
def Bi (A : Bool → ℕ → ℕ → Prop) (d : Bool) (a b : ℕ) (S S' : Finset ℕ) : Prop :=
  a ≠ b ∧ ∃ U, S = insert a (insert b U) ∧ S' = insert (op d a b) U ∧ A d a b
lemma Bi.rel {A' : Bool → ℕ → ℕ → Prop} {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S')
    (hA : ∀ d a b, A d a b → A' d a b) : Bi A' d a b S S' := by
  obtain ⟨hab, U, e1, e2, hal⟩ := h; exact ⟨hab, U, e1, e2, hA _ _ _ hal⟩
lemma Un.live {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live A m T k t S') :
    Live A m T (k + 1) (t + 1) S := by obtain ⟨U, rfl, rfl⟩ := h; exact .un hl
lemma Bi.live {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hl : Live A m T k t S') :
    Live A m T (k + 1) t S := by obtain ⟨hab, U, rfl, rfl, hal⟩ := h; exact .bi hab hal hl
lemma Bi.symm (hA : SymA A) {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') : Bi A d b a S S' := by
  obtain ⟨hab, U, rfl, rfl, hal⟩ := h
  exact ⟨hab.symm, U, Finset.insert_comm _ _ _, by rw [op_comm], hA _ _ _ hal⟩
lemma Un.sub {m a : ℕ} {S S' : Finset ℕ} (h : Un m a S S') : a ∈ S ∧ S' ⊆ insert (a ^^^ m) S := by
  obtain ⟨U, rfl, rfl⟩ := h
  exact ⟨by simp, Finset.insert_subset_insert _ (Finset.subset_insert _ _)⟩
lemma Bi.sub {a b : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') :
    a ∈ S ∧ b ∈ S ∧ S' ⊆ insert (op d a b) S := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  refine ⟨by simp, by simp, Finset.insert_subset_insert _ ?_⟩
  intro x hx; simp [hx]
def Min (A : Bool → ℕ → ℕ → Prop) (m T k t : ℕ) (S : Finset ℕ) : Prop := Live A m T k t S ∧ ∀ q < k, ¬ Sol A0 m T q (C m S)
lemma Un.sol {m T a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol A0 m T q (C m S')) :
    Sol A0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (a := a) (sub_C _ _ (by simpa using ha)) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Bi.sol {m T a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hs : Sol A0 m T q (C m S')) :
    Sol A0 m T (q + 1) (C m S) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (a := a) (b := b) (sub_C _ _ (by simpa using ha)) (sub_C _ _ (by simpa using hb)) (a0_all _ _ _) (hs.mono le_rfl ?_)
  intro x hx
  rcases hx with hx | hx
  · have := hsub hx; simp at this
    rcases this with rfl | h'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl h')
  · exact Or.inr (Or.inr hx)
lemma Un.min {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live A m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol A0 m T q (C m S)) : Min A m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Bi.min {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hl : Live A m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol A0 m T q (C m S)) : Min A m T k t S' :=
  ⟨hl, fun q hq hs => hm (q + 1) (by omega) (h.sol hs)⟩
lemma Un.fresh {m T a k t : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hl : Live A m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol A0 m T q (C m S)) : a ^^^ m ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Bi.fresh {m T a b k t : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hl : Live A m T k t S')
    (hm : ∀ q < k + 1, ¬ Sol A0 m T q (C m S)) : op d a b ∉ C m S := by
  intro hg
  apply hm k (by omega)
  refine hl.sol.mono le_rfl fun x hx => ?_
  have := h.sub.2.2 hx; simp at this
  rcases this with rfl | h'
  · exact hg
  · exact Or.inl h'
lemma Min.size {m T : ℕ} : ∀ {k t : ℕ} {S : Finset ℕ}, Min A m T k t S → S.card + t ≤ k + 1 ∧ t ≤ k := by
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
    have hu : Bi A d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
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
lemma phi_bi {a n b c : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi A d b c X X') (h1 : b ≠ n) (h2 : c ≠ n)
    (h3 : op d b c ≠ n) : Bi A d b c (phi a n X) (phi a n X') := by
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
lemma bi_keep {b c n : ℕ} {d : Bool} {X X' : Finset ℕ} (h : Bi A d b c X X') (hn : n ∈ X) (h1 : b ≠ n)
    (h2 : c ≠ n) : n ∈ X' := by
  obtain ⟨_, U, rfl, rfl, _⟩ := h
  simp at hn ⊢; rcases hn with h | h | h
  · exact absurd h.symm h1
  · exact absurd h.symm h2
  · exact Or.inr h
lemma demorgan {m a b : ℕ} (ha : a &&& m = a) (hb : b &&& m = b) (d : Bool) :
    op d (a ^^^ m) (b ^^^ m) = (op (!d) a b) ^^^ m := by
  apply Nat.eq_of_testBit_eq; intro i
  have ha1 := congrArg (fun x => x.testBit i) ha
  have hb1 := congrArg (fun x => x.testBit i) hb
  simp only [Nat.testBit_and] at ha1 hb1
  revert ha1 hb1
  cases d <;> cases hm : m.testBit i <;> cases ha' : a.testBit i <;> cases hb' : b.testBit i <;> simp [op_bit, hm, ha', hb']
lemma un2_swap {m a c : ℕ} {S S1 S2 : Finset ℕ} (ha : Un m a S S1) (ha_nf : a ^^^ m ∉ S) (hne : c ≠ a ^^^ m) (hc : Un m c S1 S2) :
    ∃ S1', Un m c S S1' ∧ a ≠ c ^^^ m ∧ Un m a S1' S2 := by
  obtain ⟨U1, eS, eS1⟩ := ha
  obtain ⟨U2, eS1', eS2⟩ := hc
  have hnf1 : a ^^^ m ∉ U1 := fun h => ha_nf (by rw [eS]; exact Finset.mem_insert_of_mem h)
  have hmU2 : a ^^^ m ∈ U2 := by
    have : a ^^^ m ∈ insert c U2 := by rw [← eS1', eS1]; simp
    exact (Finset.mem_insert.1 this).resolve_left hne.symm
  set W := U2.erase (a ^^^ m)
  have hU2 : U2 = insert (a ^^^ m) W := (Finset.insert_erase hmU2).symm
  have hU1 : U1 = insert c W := by
    ext x
    by_cases hx : x = a ^^^ m
    · subst hx
      simp [W, hnf1, hne.symm]
    · have : x ∈ insert (a ^^^ m) U1 ↔ x ∈ insert c U2 := by rw [← eS1, eS1']
      simp only [Finset.mem_insert, hx, false_or, Finset.mem_erase, ne_eq, not_false_eq_true, true_and, W] at this ⊢
      exact this
  have hac2 : a ≠ c ^^^ m := fun e => hne (by rw [e]; simp)
  refine ⟨insert (c ^^^ m) (insert a W), ⟨insert a W, ?_, rfl⟩, hac2, ⟨insert (c ^^^ m) W, ?_, ?_⟩⟩
  · rw [eS, hU1, Finset.insert_comm]
  · rw [Finset.insert_comm]
  · rw [eS2, hU2, Finset.insert_comm]
lemma first_move (hA : SymA A) {m T : ℕ} : ∀ (k t : ℕ) (S : Finset ℕ), Min A m T k t S → 2 ≤ S.card →
    (∃ k0 d a b S1, k = k0 + 1 ∧ Bi A d a b S S1 ∧ Live A m T k0 t S1) ∨
    (∃ k0 t0 a d c S1 S2, k = k0 + 2 ∧ t = t0 + 1 ∧ Un m a S S1 ∧ Bi A d (a ^^^ m) c S1 S2 ∧ Live A m T k0 t0 S2) ∨
    (∃ k0 t0 a a' d S1 S2 S3, k = k0 + 3 ∧ t = t0 + 2 ∧ a' < a ∧ Un m a S S1 ∧ a' ≠ a ^^^ m ∧ Un m a' S1 S2 ∧
      Bi A d (a ^^^ m) (a' ^^^ m) S2 S3 ∧ Live A m T k0 t0 S3) := by
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
    have dbl : ∀ {c k2 t2 S2}, Un m c S1 S2 → Live A m T k2 t2 S2 → k = k2 + 1 → c ≠ a ^^^ m ∧ c ^^^ m ≠ a ^^^ m := by
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
      ⟨k0, t0, c, c', d, S2, S3, S4, rfl, rfl, hc'c, h1, hne, h2, hb, hl2⟩
    · by_cases hx : x = a ^^^ m
      · subst hx; exact Or.inr (Or.inl ⟨k0, t, a, d, y, S1, S2, rfl, rfl, hu, hb, hl2⟩)
      by_cases hy : y = a ^^^ m
      · subst hy; exact Or.inr (Or.inl ⟨k0, t, a, d, x, S1, S2, rfl, rfl, hu, hb.symm hA, hl2⟩)
      have hg : op d x y ≠ a ^^^ m := fun e => hb.fresh hl2 hmin.2 (sub_C _ _ (by rw [e]; simpa using hnS1))
      refine Or.inl ⟨k0 + 1, d, x, y, phi a (a ^^^ m) S2, rfl, ?_, ?_⟩
      · rw [← hst]; exact phi_bi hb hx hy hg
      · exact (phi_back (bi_keep hb hnS1 hx hy)).live hl2
    · have hb1 := hb.live hl2
      obtain ⟨n1, n2⟩ := dbl h1 hb1 rfl
      have hm2 := h1.min hb1 hmin.2
      by_cases hy : y = a ^^^ m
      · subst hy
        by_cases hca : c < a
        · exact Or.inr (Or.inr ⟨k0, t0, a, c, d, S1, S2, S3, rfl, rfl, hca, hu, n1, h1, hb.symm hA, hl2⟩)
        · have hac : a < c := Nat.lt_of_le_of_ne (by omega) (fun e => hb.1 (by rw [e]))
          obtain ⟨S1', hu1', hne', hu2'⟩ := un2_swap hu hn n1 h1
          exact Or.inr (Or.inr ⟨k0, t0, c, a, d, S1', S2, S3, rfl, rfl, hac, hu1', hne', hu2', hb, hl2⟩)
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
      refine Or.inr (Or.inr ⟨k0 + 1, t0 + 1, c, c', d, phi a (a ^^^ m) S2, phi a (a ^^^ m) S3, phi a (a ^^^ m) S4, rfl, rfl, hc'c, ?_, hne,
        phi_un h2 n3 n4, phi_bi hb n2 n4 hg, ?_⟩)
      · rw [← hst]; exact phi_un h1 n1 n2
      · exact (phi_back (bi_keep hb hk3 n2 n4)).live hl2
lemma Branch3_no_can0 {m T k0 t0 a a' : ℕ} {d : Bool} {S S1 S2 S3 : Finset ℕ}
    (hm : Min A m T (k0 + 3) (t0 + 2) S) (hS : ∀ x ∈ S, x &&& m = x)
    (hu1 : Un m a S S1) (hne : a' ≠ a ^^^ m) (hu2 : Un m a' S1 S2)
    (hb : Bi A d (a ^^^ m) (a' ^^^ m) S2 S3) (hl3 : Live A m T k0 t0 S3) :
    a ^^^ m ∈ S3 ∨ a' ^^^ m ∈ S3 := by
  by_contra hc
  push Not at hc
  have haS : a ∈ S := hu1.sub.1
  have ha'S : a' ∈ S := by
    have h1 := hu1.sub.2 hu2.sub.1
    rw [Finset.mem_insert] at h1
    exact h1.resolve_left hne
  have hdm : op d (a ^^^ m) (a' ^^^ m) = (op (!d) a a') ^^^ m :=
    demorgan (hS a haS) (hS a' ha'S) d
  apply hm.2 (k0 + 2) (by omega)
  refine .bi (d := !d) (a := a) (b := a') (sub_C _ _ haS) (sub_C _ _ ha'S) (a0_all _ _ _) ?_
  refine .un (a := op (!d) a a') (Or.inl rfl) (hl3.sol.mono le_rfl fun x hx => ?_)
  have h1 := hb.sub.2.2 hx
  rw [Finset.mem_insert] at h1
  rcases h1 with rfl | hx2
  · rw [hdm]; exact Or.inl rfl
  · have h2 := hu2.sub.2 hx2
    rw [Finset.mem_insert] at h2
    rcases h2 with h2 | hx1
    · exact absurd (h2 ▸ hx) hc.2
    · have h3 := hu1.sub.2 hx1
      rw [Finset.mem_insert] at h3
      rcases h3 with h3 | hxS
      · exact absurd (h3 ▸ hx) hc.1
      · exact Or.inr (Or.inr (Or.inl hxS))
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
lemma Un.im {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol A0 n (T &&& n) q (C n (Im n S'))) :
    Sol A0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  refine .un (Im_mem ha) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_neg hn]; exact Or.inl rfl
omit hn in
lemma Bi.im {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hs : Sol A0 n (T &&& n) q (C n (Im n S'))) :
    Sol A0 n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  refine .bi (d := d) (Im_mem ha) (Im_mem hb) (a0_all _ _ _) (hs.mono le_rfl (C_Im_sub hsub ?_ (Set.subset_insert _ _)))
  rw [and_op]; exact Or.inl rfl
lemma Un.kill {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : Sol A0 n (T &&& n) q (C n (Im n S'))) :
    Sol A0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.kill {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : Sol A0 n (T &&& n) q (C n (Im n S'))) : Sol A0 n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
omit hn in
def SolPos (n' T' q : ℕ) (S : Set ℕ) : Prop :=
  ∃ k ≤ q, ∃ t, ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live A0 n' T' k t S0 ∧ (k < q ∨ 1 ≤ t)
omit hn in
lemma SolPos.mono {n' T' q : ℕ} {S : Set ℕ} (h : SolPos n' T' q S) :
    ∀ {q' : ℕ} {S' : Set ℕ}, q ≤ q' → S ⊆ S' → SolPos n' T' q' S' := by
  rintro q' S' hq hs
  obtain ⟨k, hk, t, S0, hS0, hl, hc⟩ := h
  refine ⟨k, by omega, t, S0, hS0.trans hs, hl, ?_⟩
  rcases hc with hlt | ht
  · exact Or.inl (by omega)
  · by_cases hkq : k < q'
    · exact Or.inl hkq
    · exact Or.inr ht
omit hn in
lemma SolPos.of_sol_lt {n' T' q q' : ℕ} {S : Set ℕ} (h : Sol A0 n' T' q S) (hlt : q < q') : SolPos n' T' q' S := by
  obtain ⟨k, hk, t, S0, hS0, hl⟩ := h.live
  exact ⟨k, by omega, t, S0, hS0, hl, Or.inl (by omega)⟩
omit hn in
lemma SolPos.zero_false {n' T' : ℕ} {S : Set ℕ} (h : SolPos n' T' 0 S) : False := by
  obtain ⟨k, hk, t, S0, _, hl, hc⟩ := h
  have htk := hl.t_le_k
  omega
lemma Un.im_pos {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : SolPos n (T &&& n) q (C n (Im n S'))) :
    SolPos n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  obtain ⟨k, hk, t, S0, hS0, hl, hcond⟩ := hs
  have hCS' : C n (Im n S') ⊆ insert ((a ^^^ m) &&& n) (C n (Im n S)) :=
    C_Im_sub hsub (Or.inl rfl) (Set.subset_insert _ _)
  by_cases hmS0 : (a ^^^ m) &&& n ∈ S0
  · refine ⟨k + 1, by omega, t + 1, insert (a &&& n) (S0.erase ((a ^^^ m) &&& n)), ?_, .un (a := a &&& n) ?_, Or.inr (by omega)⟩
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe] at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact Im_mem ha
      · exact (hCS' (hS0 h1)).resolve_left h2
    · rw [← and_neg hn, Finset.insert_erase hmS0]; exact hl
  · refine ⟨k, by omega, t, S0, fun x hx => (hCS' (hS0 hx)).resolve_left (fun e => hmS0 (e ▸ hx)), hl, Or.inl (by omega)⟩
lemma Un.im_sol_to_pos {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hs : Sol A0 n (T &&& n) q (C n (Im n S'))) :
    SolPos n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hsub⟩ := h.sub
  obtain ⟨k, hk, t, S0, hS0, hl⟩ := hs.live
  have hCS' : C n (Im n S') ⊆ insert ((a ^^^ m) &&& n) (C n (Im n S)) :=
    C_Im_sub hsub (Or.inl rfl) (Set.subset_insert _ _)
  by_cases hmS0 : (a ^^^ m) &&& n ∈ S0
  · refine ⟨k + 1, by omega, t + 1, insert (a &&& n) (S0.erase ((a ^^^ m) &&& n)), ?_, .un (a := a &&& n) ?_, Or.inr (by omega)⟩
    · intro x hx
      simp only [Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe] at hx
      rcases hx with rfl | ⟨h1, h2⟩
      · exact Im_mem ha
      · exact (hCS' (hS0 h1)).resolve_left h2
    · rw [← and_neg hn, Finset.insert_erase hmS0]; exact hl
  · refine ⟨k, by omega, t, S0, fun x hx => (hCS' (hS0 hx)).resolve_left (fun e => hmS0 (e ▸ hx)), hl, Or.inl (by omega)⟩
lemma Un.kill_pos {a q : ℕ} {S S' : Finset ℕ} (h : Un m a S S') (hc : Cst n a) (hs : SolPos n (T &&& n) q (C n (Im n S'))) :
    SolPos n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2 (Cst_mem ((Cst_neg hn).2 hc)) subset_rfl)
omit hn in
lemma Bi.im_pos {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hs : SolPos n (T &&& n) q (C n (Im n S'))) :
    SolPos n (T &&& n) (q + 1) (C n (Im n S)) := by
  obtain ⟨ha, hb, hsub⟩ := h.sub
  obtain ⟨k, hk, t, S0, hS0, hl, hcond⟩ := hs
  have hCS' : C n (Im n S') ⊆ insert (op d (a &&& n) (b &&& n)) (C n (Im n S)) :=
    C_Im_sub hsub (by rw [and_op]; exact Or.inl rfl) (Set.subset_insert _ _)
  by_cases hop : op d (a &&& n) (b &&& n) ∈ S0
  · by_cases habn : a &&& n = b &&& n
    · have hmem : op d (a &&& n) (b &&& n) ∈ C n (Im n S) := by rw [← habn, op_self]; exact Im_mem ha
      exact ⟨k, by omega, t, S0, fun x hx => (hCS' (hS0 hx)).elim (fun e => e ▸ hmem) id, hl, Or.inl (by omega)⟩
    · refine ⟨k + 1, by omega, t, insert (a &&& n) (insert (b &&& n) (S0.erase (op d (a &&& n) (b &&& n)))), ?_,
        .bi habn (a0_all _ _ _) (by rwa [Finset.insert_erase hop]), hcond.imp (fun h' => by omega) id⟩
      intro x hx
      simp only [Finset.coe_insert, Finset.coe_erase, Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff, Finset.mem_coe] at hx
      rcases hx with rfl | rfl | ⟨h1, h2⟩
      · exact Im_mem ha
      · exact Im_mem hb
      · exact (hCS' (hS0 h1)).resolve_left h2
  · exact ⟨k, by omega, t, S0, fun x hx => (hCS' (hS0 hx)).resolve_left (fun e => hop (e ▸ hx)), hl, Or.inl (by omega)⟩
omit hn in
lemma Bi.kill_pos {a b q : ℕ} {d : Bool} {S S' : Finset ℕ} (h : Bi A d a b S S') (hc : Cst n a ∨ Cst n b)
    (hs : SolPos n (T &&& n) q (C n (Im n S'))) : SolPos n (T &&& n) q (C n (Im n S)) :=
  hs.mono le_rfl (C_Im_sub h.sub.2.2 (op_cst_mem d hc h.sub.1 h.sub.2.1) subset_rfl)
lemma Min.const (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} {S : Finset ℕ} (h : Min A m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ Sol A0 n (T &&& n) q (C n (Im n S)) := by
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
    have hu : Bi A d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
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
lemma Min.const_pos (hT0 : T &&& n ≠ 0) (hT1 : T &&& n ≠ n) {k t : ℕ} (ht : 1 ≤ t) {S : Finset ℕ} (h : Min A m T k t S) :
    ∃ q, q + (S.filter (Cst n)).card ≤ k ∧ SolPos n (T &&& n) q (C n (Im n S)) := by
  obtain ⟨hl, hm⟩ := h
  induction hl with
  | stop => omega
  | @un k t a U hl ih =>
    have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
    have hmin' := hu.min hl hm
    have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    rcases Nat.eq_zero_or_pos t with rfl | ht'
    · obtain ⟨q, hq, hs⟩ := hmin'.const hn hT0 hT1
      refine ⟨q + 1, ?_, hu.im_sol_to_pos hn hs⟩
      have hcardS : ((insert a U).filter (Cst n)).card ≤ ((insert (a ^^^ m) U).filter (Cst n)).card := by
        by_cases hc : Cst n a
        · have hcm : Cst n (a ^^^ m) := (Cst_neg hn).2 hc
          rw [Finset.filter_insert, if_pos hc, Finset.filter_insert, if_pos hcm]
          conv_rhs => rw [Finset.card_insert_of_notMem (by simp [hf])]
          exact Finset.card_insert_le a (U.filter (Cst n))
        · rw [Finset.filter_insert, ite_eq_right hc]; exact h1
      omega
    · obtain ⟨q, hq, hs⟩ := ih ht' hmin'.2
      by_cases hc : Cst n a
      · refine ⟨q, ?_, hu.kill_pos hn hc hs⟩
        rw [Finset.filter_insert, ite_eq_left hc]
        have := Finset.card_insert_le a (U.filter (Cst n)); omega
      · refine ⟨q + 1, ?_, hu.im_pos hn hs⟩
        rw [Finset.filter_insert, ite_eq_right hc]; omega
  | @bi k t d a b U hab hal hl ih =>
    have hu : Bi A d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
    obtain ⟨q, hq, hs⟩ := ih ht (hu.min hl hm).2
    have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
    have h1 : (U.filter (Cst n)).card ≤ ((insert (op d a b) U).filter (Cst n)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
    have ca := Finset.card_insert_le a (U.filter (Cst n))
    have cb := Finset.card_insert_le b (U.filter (Cst n))
    by_cases hca : Cst n a
    · refine ⟨q, ?_, hu.kill_pos (Or.inl hca) hs⟩
      rw [Finset.filter_insert, ite_eq_left hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · rw [ite_eq_left hcb]
        rw [Finset.filter_insert, ite_eq_left (op_cst2 d hca hcb), Finset.card_insert_of_notMem (by simp [hf])] at hq
        have := Finset.card_insert_le a (insert b (U.filter (Cst n))); omega
      · rw [ite_eq_right hcb]; omega
    · rw [Finset.filter_insert, ite_eq_right hca, Finset.filter_insert]
      by_cases hcb : Cst n b
      · refine ⟨q, ?_, hu.kill_pos (Or.inr hcb) hs⟩
        rw [ite_eq_left hcb]; omega
      · refine ⟨q + 1, ?_, hu.im_pos hs⟩
        rw [ite_eq_right hcb]; omega
end proj
lemma Min.proper {m T k t : ℕ} (hT : T &&& m = T) (hT0 : T ≠ 0) (hT1 : T ≠ m) {S : Finset ℕ} (hS : ∀ x ∈ S, x &&& m = x)
    (h : Min A m T k t S) : 0 ∉ S ∧ m ∉ S := by
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
lemma Live.cov {k t : ℕ} {S : Finset ℕ} (h : Live A m T k t S) : ∃ w ∈ S, sepb N (pos' t) w i = true := by
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
lemma bi_uq {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live A m T k t (insert (op d a b) U))
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
lemma bi_tight {a b k t : ℕ} {d : Bool} {U : Finset ℕ} (hab : a ≠ b) (hal : A d a b) (hl : Live A m T k t (insert (op d a b) U))
    (hm : ∀ q < k + 1, ¬ Sol A0 m T q (C m ((insert a (insert b U) : Finset ℕ) : Set ℕ)))
    (hc : (insert a (insert b U)).card + t = k + 2) :
    a ∉ U ∧ b ∉ U ∧ op d a b ∉ U ∧ (insert (op d a b) U).card + t = k + 1 ∧ Min A m T k t (insert (op d a b) U) := by
  have hu : Bi A d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
  have hf : op d a b ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a (insert b U)
  have h2 := Finset.card_insert_le b U
  have ha : a ∉ insert b U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  have hb : b ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc h1; omega
  exact ⟨fun h => ha (by simp [h]), hb, hf, by omega, hmin⟩
lemma un_tight {a k t : ℕ} {U : Finset ℕ} (hl : Live A m T k t (insert (a ^^^ m) U))
    (hm : ∀ q < k + 1, ¬ Sol A0 m T q (C m ((insert a U : Finset ℕ) : Set ℕ)))
    (hc : (insert a U).card + (t + 1) = k + 2) :
    a ∉ U ∧ a ^^^ m ∉ U ∧ (insert (a ^^^ m) U).card + t = k + 1 ∧ Min A m T k t (insert (a ^^^ m) U) := by
  have hu : Un m a (insert a U) (insert (a ^^^ m) U) := ⟨U, rfl, rfl⟩
  have hf : a ^^^ m ∉ U := fun h => hu.fresh hl hm (sub_C _ _ (by simp [h]))
  have hmin := hu.min hl hm
  have hs := hmin.size.1
  rw [Finset.card_insert_of_notMem hf] at hs ⊢
  have h1 := Finset.card_insert_le a U
  have ha : a ∉ U := fun h => by rw [Finset.insert_eq_of_mem h] at hc; omega
  exact ⟨ha, hf, by omega, hmin⟩
lemma rect0 {k : ℕ} {S : Finset ℕ} (hl : Live A m T k 0 S) (hm : ∀ q < k, ¬ Sol A0 m T q (C m (S : Set ℕ)))
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
lemma polar {k t : ℕ} {S : Finset ℕ} (hl : Live A m T k t S) (hm : ∀ q < k, ¬ Sol A0 m T q (C m (S : Set ℕ)))
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
lemma rect1 {k t : ℕ} {S : Finset ℕ} (hl : Live A m T k t S) (hm : ∀ q < k, ¬ Sol A0 m T q (C m (S : Set ℕ)))
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
lemma bi_uq2 {a b k t c i : ℕ} {d e : Bool} {U : Finset ℕ} (he : e = true ∨ e = pos' t) (hl : Live A m T k t (insert (op d a b) U))
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
lemma ht_bi {a b k t c1 c2 : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live A m T k t (insert (op d a b) U))
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
lemma ht_merge {a b k t : ℕ} {d e : Bool} {U : Finset ℕ} (hab : a ≠ b) (he : e = true ∨ e = pos' t) (hl : Live A m T k t (insert (op d a b) U))
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
lemma chrom {e : Bool} {k t : ℕ} {S : Finset ℕ} (hl : Live A m T k t S) (hm : ∀ q < k, ¬ Sol A0 m T q (C m (S : Set ℕ)))
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
    have hu : Bi A d a b (insert a (insert b U)) (insert (op d a b) U) := ⟨hab, U, rfl, rfl, hal⟩
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
  deriving DecidableEq
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
def modeF (n e : Nat) : (W → W → Nat → Nat → Nat → Nat → Nat → Bool) → W → W → Nat → Nat → Nat → Nat → Nat → Bool :=
  bif Nat.ble n e then (bif Nat.ble (Nat.succ n) e then f2 else f1) else f0
def MM : Nat := 214
def hb (H x : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight H (Nat.mod x MM)) 1) 1
def hashFS (ra rb : Nat) (op ka kc : Bool) : Nat :=
  let le := Nat.ble ra rb
  let lo := bif le then ra else rb
  let hi := bif le then rb else ra
  let klo := bif le then ka else kc
  let khi := bif le then kc else ka
  let tri := bif Nat.ble 2 hi then ((hi - 2) * (hi - 1)) / 2 else 0
  let pid := tri + (lo - 1)
  (pid * 8 + (bif op then 4 else 0) + (bif klo then 2 else 0) + (bif khi then 1 else 0)) % MM
def hashBin (sa sc : Nat) (op ka kc : Bool) : Nat :=
  let le := Nat.ble sa sc
  let klo := bif le then ka else kc
  let khi := bif le then kc else ka
  (((sa % MM + sc % MM) % MM) * 8 + (bif op then 4 else 0) + (bif klo then 2 else 0) + (bif khi then 1 else 0)) % MM
def hashP (sc : Nat) (op ka kc : Bool) : Nat :=
  ((sc % MM) * 8 + (bif op then 4 else 0) + (bif ka then 2 else 0) + (bif kc then 1 else 0)) % MM
def hashNot (sa : Nat) (ka : Bool) : Nat :=
  ((sa % MM) * 2 + (bif ka then 1 else 0)) % MM
def kidsQ (c : ((List W → Bool) → Bool) → Nat → Bool) (e n z x y a c' : Nat) (oa oc : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  (Bool.rec (motive := fun _ => Bool)
    ((Bool.rec (motive := fun _ => Bool) (false) (c mk (Nat.sub (Nat.sub z x) y)) (Nat.ble (Nat.succ (Nat.succ n)) e)))
    (true)
    ((Bool.rec (motive := fun _ => Bool) (false)
      ((Bool.rec (motive := fun _ => Bool)
        ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) (oa)))
        (true)
        ((Bool.rec (motive := fun _ => Bool) (false) (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) (oc)))))
      (Nat.ble (Nat.succ n) e))))
def midQ (f : Nat → List W → Bool) (m g e n z : Nat) (v : List W) (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) (false) ((st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z => kidsQ (child f g) e n z a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0) (put m s x y v)))) (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def kidsH (c : ((List W → Bool) → Bool) → Nat → Bool) (z x y a c' : Nat) (b0 bA bC bAC : Bool) (mk : (List W → Bool) → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false (c mk (Nat.sub (Nat.sub z x) y)) bAC)
        true
        (Bool.rec (motive := fun _ => Bool) false (c (fun h => mk (fun r => rm a a r h)) (Nat.sub z y)) bC))
      true
      (Bool.rec (motive := fun _ => Bool) false (c (fun h => mk (fun r => rm c' c' r h)) (Nat.sub z x)) bA))
    true
    (Bool.rec (motive := fun _ => Bool) false (c (fun h => mk (fun r => rm a c' r h)) z) b0)
def midH (f : Nat → List W → Bool) (kf : Bool → Bool → Bool) (m g e n z : Nat) (v : List W)
    (a c : W) (da dc s x y : Nat) : Bool :=
  (Bool.rec (motive := fun _ => Bool) false
    (st (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) (fun z =>
      let oa := Nat.beq da 0
      let oc := Nat.beq dc 0
      let b0 := oa && oc && kf false false
      let bA := oc && Nat.ble (Nat.succ n) e && kf true false
      let bC := oa && Nat.ble (Nat.succ n) e && kf false true
      let bAC := Nat.ble (Nat.succ (Nat.succ n)) e && kf true true
      Bool.rec (motive := fun _ => Bool) false
        (kidsH (child f g) z a.c c.c a.s c.s b0 bA bC bAC (put m s x y v))
        (b0 || bA || bC || bAC)))
    (Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (Nat.lor x y)) g) g))
def pair (h : W → W → Nat → Nat → Nat → Nat → Nat → Bool) (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u => XW.rec (motive := fun _ => Bool) (fun c s' q' u' => (Bool.rec (motive := fun _ => Bool) (h a c (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b)) (true) (h a c (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b)))) c) a
def pairOH (lb : Nat) (hf : W → W → Bool → Bool → Bool → Bool) (f : Nat → Nat → List W → Bool)
    (m g e n z : Nat) (v : List W) (a c : XW) : Bool :=
  XW.rec (motive := fun _ => Bool) (fun a s q u =>
    XW.rec (motive := fun _ => Bool) (fun c s' q' u' =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) false
          (modeF n e (midH (f (Nat.succ (gkey a.r c.r true))) (hf a c true) m g e (Nat.pred n) z v) a c
            (Nat.land u q') (Nat.land u' q) (Nat.lor s s') (Nat.land a.a c.a) (Nat.lor a.b c.b))
          (Nat.ble lb (gkey a.r c.r true)))
        true
        (Bool.rec (motive := fun _ => Bool) false
          (modeF n e (midH (f (Nat.succ (gkey a.r c.r false))) (hf a c false) m g e (Nat.pred n) z v) a c
            (Nat.xor (Nat.land u s') u) (Nat.xor (Nat.land u' s) u') (Nat.land s s') (Nat.lor a.a c.a) (Nat.land a.b c.b))
          (Nat.ble lb (gkey a.r c.r false)))) c) a
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
def nots (f : Nat → Nat → Nat → List W → Bool) (m g e n z : Nat) (subA : Bool) (q lt : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true
    (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool)
        (st (Nat.xor a.s m) (fun s => st (bif subA then Nat.sub z a.c else z) (fun z =>
          ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v =>
            Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool) false (child (f a.s s) g (fun h => h v) (Nat.sub z a.c)) (Nat.ble (Nat.succ n) e))
              true
              (Bool.rec (motive := fun _ => Bool) false (child (f a.s s) g (rm a.s a.s v) z) (Nat.ble n e))))))
        false (Nat.beq (Nat.succ a.s) q))
      (Nat.beq lt 0 || Nat.ble (Nat.succ a.s) lt))) r)
def notsC (H : Nat) (f : Nat → Nat → Nat → List W → Bool) (m g e n z : Nat) (subA : Bool) (q lt : Nat) (v r : List W) : Bool :=
  (List.rec (motive := fun _ => Bool) false (fun a _ ih => Bool.rec (motive := fun _ => Bool) ih true
    (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool)
        (let bD := Nat.ble n e && hb H (hashNot a.s false)
         let bK := Nat.ble (Nat.succ n) e && hb H (hashNot a.s true)
         Bool.rec (motive := fun _ => Bool) false
           (st (Nat.xor a.s m) (fun s => st (bif subA then Nat.sub z a.c else z) (fun z =>
             ins ⟨s, a.b, a.a, a.c, 0⟩ v (fun v =>
               Bool.rec (motive := fun _ => Bool)
                 (Bool.rec (motive := fun _ => Bool) false (child (f a.s s) g (fun h => h v) (Nat.sub z a.c)) bK)
                 true
                 (Bool.rec (motive := fun _ => Bool) false (child (f a.s s) g (rm a.s a.s v) z) bD)))))
           (bD || bK))
        false (Nat.beq (Nat.succ a.s) q))
      (Nat.beq lt 0 || Nat.ble (Nat.succ a.s) lt))) r)
def pos (t : Nat) : Bool := Nat.rec (motive := fun _ => Bool) false (fun _ _ => true) t
def wstC (NN : Nat) (d : Bool) (l : Nat) (v : List W) : Nat := Nat.xor l (twiceC NN d l v)
def nodeC (NN : Nat) (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  (fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f0 h)) xs)
    (Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e)) (Nat.ble n e))
    (mkXC NN d l (wstC NN d l v) v))
  (mid f m g e (Nat.pred n) z v)
def nodeQC (NN : Nat) (f : Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    ((fun h => (fun xs => Bool.rec (motive := fun _ => Bool) (go (pair (f1 h)) xs) (go (pair (f2 h)) xs) (Nat.ble (Nat.succ n) e))
      (mkXC NN d l (wstC NN d l v) v))
    (midQ f m g e (Nat.pred n) z v))
    (Nat.ble n e)
def nodeOHC (NN lb : Nat) (hf : W → W → Bool → Bool → Bool → Bool) (f : Nat → Nat → List W → Bool) (d : Bool) (l m g e n z : Nat) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) : Bool :=
  go (pairOH lb hf f m g e n z v) (mkXC NN d l (wstC NN d l v) v)
def prd (t : Nat) (h : Nat → Bool) : Bool := Nat.rec (motive := fun _ => Bool) false (fun s _ => h s) t
def cvC (NN : Nat) (d : Bool) (l : Nat) (v : List W) (b : Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false b (Nat.beq (covC NN d l v) l)) b d
def tstC (NN AA HX HY : Nat) (d : Bool) (l e : Nat) (v : List W) (F : Nat → Bool) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) (F 0) (Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) (F 1) (F 0) (flkC NN AA l (wstC NN d l v) v (starC HX HY))) false (bipC NN AA HX HY l (wstC NN d l v) v []))
      (Nat.beq (Nat.succ n) e))
    (Bool.rec (motive := fun _ => Bool) (F 0) false (rectC NN AA HX HY d l (wstC NN d l v) v [])) (Nat.beq n e)) v.length
def mvC (NN AA HX HY : Nat) (F : Nat → Nat → Nat → List W → Bool) (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun a0 q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (prd s (fun s2 => nots (fun _ q' z v => cvC NN (pos s2) l v (tstC NN AA HX HY (pos s2) l (Nat.sub (Nat.sub k 1) s2) v (fun y =>
          nodeQC NN (F (Nat.sub k 3) s2) (pos s2) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s2) y) v.length z v (pairsQ q q'))))
          m g (Nat.sub (Nat.sub (Nat.sub k 1) s2) y) v.length z (pos s2) (Nat.succ q) a0 v v)) true
        (nodeC NN (F (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)))))
      m g (Nat.sub (Nat.sub k s) y) n z (pos s) 0 0 v v)) true
    (nodeC NN (F (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def lookC (NN AA HX HY : Nat) (l m g : Nat) (fuel : Nat) : Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ => true)
    (fun _ ih k t z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y => mvC NN AA HX HY ih l m g k t z v y)) true (Nat.ble v.length 1)) fuel
def look1C (NN AA HX HY : Nat) (l m g K : Nat) (fuel : Nat) : Nat → Nat → Nat → Nat → List W → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → List W → Bool) (fun _ _ _ _ _ => true)
    (fun _ ih k t lb z v => Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
      Bool.rec (motive := fun _ => Bool) (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y) true
        (nodeOHC NN lb (fun _ _ _ _ _ => true) (ih (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)) fuel
end coreC

def bigNat_AA : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3efe) 64) 0xfdff7f6ff6dfeddb) 64) 0xbbbdf7776db6dff7) 64) 0xf7f7f6fdb77df7ef) 64) 0x0
def bigNat_HX : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x8892492008) 64) 0x808090248820810) 64) 0x0
def bigNat_HY : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x4101) 64) 0x200809009201224) 64) 0x4442080000000000) 64) 0x0) 64) 0x0
def bigNat_P0 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3f87f860000001c0) 64) 0xfb801049614020b8) 64) 0x10049805b358000) 64) 0x828) 64) 0x2049772d70c12448) 64) 0x8b85f70061b6c000) 64) 0x7f00601b701f7ef) 64) 0xaaaaaaaaaaaaaaaa
def bigNat_P1 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x7e00) 64) 0x7fb0ff00c1c1e) 64) 0x38182c024793820) 64) 0x4036181601d68000) 64) 0x1452) 64) 0xfcb2194fb61de099) 64) 0x38bc17070d80dff7) 64) 0xf00000fc307c07ef) 64) 0xcccccccccccccccc
def bigNat_P2 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x7f00ff) 64) 0x8030000000e1c01e) 64) 0xf81804020202cb49) 64) 0x984ac12aa8030000) 64) 0x22fe) 64) 0x4ddf2661d246c9d3) 64) 0x913db1700c060007) 64) 0xf7f7f0fd807df00f) 64) 0xf0f0f0f0f0f0f0f0
def bigNat_P3 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f0000ff) 64) 0xbf80000ff601ddc0) 64) 0x2ab0034b988182) 64) 0xeb10003cf2e00000) 64) 0x3e84) 64) 0x91e77b06241f6d03) 64) 0xbb8822776006dff0) 64) 0x7f600007df7e0) 64) 0xff00ff00ff00ff00
def bigNat_P4 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f7f7e00) 64) 0xff6ec0000) 64) 0x33a6900c130203) 64) 0x727c921000800000) 64) 0x3ae6) 64) 0xe504400800978dda) 64) 0x210c4776db00000) 64) 0x7f6fdb7000000) 64) 0xffff0000ffff0000
def bigNat_P5 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f7f7eff) 64) 0xbfb7fb6000000000) 64) 0x3b36db6fe3f3f3) 64) 0x80600020c3040000) 64) 0x3cf8) 64) 0xf9f87c6fc6d80000) 64) 0x202100776db6dff7) 64) 0xf7f0000000000000) 64) 0xffffffff00000000
def bigNat_TG : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3efe) 64) 0xfdff7f6ff6dfeddb) 64) 0xbbbdf7776db6dff7) 64) 0xf7f7f6fdb77df7ef) 64) 0xfeeaece0faeae880
def NN0 : Nat := 271
def AA0 : Nat := bigNat_AA
def HX0 : Nat := bigNat_HX
def HY0 : Nat := bigNat_HY
def segsX0 : List (ℕ × ℕ) := [(63, 68), (68, 75), (75, 81), (81, 87), (87, 91), (91, 94), (94, 97), (97, 104), (104, 107), (107, 115), (115, 123), (123, 131), (131, 141), (141, 144), (144, 147), (147, 150), (150, 153), (153, 156), (156, 159), (159, 163), (163, 167)]
def segsY0 : List (ℕ × ℕ) := [(167, 171), (171, 177), (177, 182), (182, 186), (186, 190), (190, 194), (194, 197), (197, 201), (201, 204), (204, 213), (213, 216), (216, 219), (219, 228), (228, 231), (231, 239), (239, 249), (249, 256), (256, 264), (264, 270)]
def rawP0 : List ℕ := [bigNat_P0, bigNat_P1, bigNat_P2, bigNat_P3, bigNat_P4, bigNat_P5]
def TG0 : ℕ := bigNat_TG
def I : Inst := ⟨NN0, AA0, HX0, HY0, segsX0, segsY0, rawP0, TG0⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem segX_ok0 : segsX0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem segY_ok0 : segsY0.all (segOk AA0) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem HX_eq0 : HX0 = bitsOf segsX0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem HY_eq0 : HY0 = bitsOf segsY0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem AA_TG0 : AA0 &&& TG0 = AA0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem TG_lt0 : TG0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem AA_lt0 : AA0 < 2 ^ NN0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raw_good0 : rawP0.all (fun w => segsX0.all (segGood w 0) && segsY0.all (segGood w NN0)) = true := by decide +kernel
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
abbrev nodeQ := nodeQC I.NN
abbrev nodeOH := nodeOHC I.NN
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
lemma Live.pos {A : Bool → ℕ → ℕ → Prop} {m T k t : ℕ} {S : Finset ℕ} (h : Live A m T k t S) : 0 < S.card := by
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
def Cl (P : List ℕ) (T k t : ℕ) (b : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ j < P.length, ∀ q, q + b j < k →
    (t = 0 → ¬ Sol A0 (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S))) ∧
    (1 ≤ t → ¬ SolPos (P.getD j 0) (T &&& P.getD j 0) q (C (P.getD j 0) (Im (P.getD j 0) S)))
structure StOk (P : List ℕ) (T l m k t z : ℕ) (v : List W) (S : Finset ℕ) : Prop where
  rep : Rep v S
  wok : ∀ w ∈ v, WOk P w
  good : ∀ w ∈ v, Good l w.s
  subm : ∀ w ∈ v, w.s &&& m = w.s
  bud : ∃ b : ℕ → ℕ, (∀ j < P.length, b j ≤ 15) ∧ Cl P T k t b S ∧ z = pk P.length (fun j => 16 + b j - cnt v j)
structure Ctx (P : List ℕ) (l m g T : ℕ) : Prop where
  lg : ∀ i, l.testBit i = true → Lg I.NN m T i ∧ I.AA.testBit i = true
  hP : ∀ j < P.length, P.getD j 0 &&& m = P.getD j 0 ∧ T &&& P.getD j 0 ≠ 0 ∧ T &&& P.getD j 0 ≠ P.getD j 0
  hg : g = pk P.length (fun _ => 16)
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma cnt_le {A : Bool → ℕ → ℕ → Prop} {k k' t : ℕ} {v : List W} {S : Finset ℕ} {b : ℕ → ℕ}
    (hr : Rep v S) (hw : ∀ w ∈ v, WOk P w) (hc : Cl P T k t b S) (hm : Min A m T k' t S) (hk : k' ≤ k) :
    ∀ j < P.length, cnt v j ≤ b j := by
  intro j hj
  obtain ⟨p1, p2, p3⟩ := X.hP j hj
  have hqb : ∃ q, q + (S.filter (Cst (P.getD j 0))).card ≤ k' ∧ (q + b j < k → False) := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · obtain ⟨q, hq, hs⟩ := hm.const p1 p2 p3
      exact ⟨q, hq, fun hlt => (hc j hj q hlt).1 rfl hs⟩
    · obtain ⟨q, hq, hs⟩ := hm.const_pos p1 p2 p3 ht
      exact ⟨q, hq, fun hlt => (hc j hj q hlt).2 ht hs⟩
  obtain ⟨q, hq, hbot⟩ := hqb
  have hle_qb : ¬ q + b j < k := hbot
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
lemma guard_ok {A : Bool → ℕ → ℕ → Prop} {k k' t z : ℕ} {v : List W} {S : Finset ℕ}
    (hr : StOk P T l m k t z v S) (hm : Min A m T k' t S) (hk : k' ≤ k) :
    Nat.beq (Nat.land z g) g = true := by
  obtain ⟨b, hb, hc, hz⟩ := hr.bud
  have hle := cnt_le X hr.rep hr.wok hc hm hk
  rw [nl, hz, X.hg, pk_guard]; · simp
  intro j hj
  have := hb j hj; have := hle j hj; omega
lemma child_sound {A : Bool → ℕ → ℕ → Prop} {f : ℕ → List W → Bool} {z t k k' : ℕ} {r : List W} {S : Finset ℕ}
    {mk : (List W → Bool) → Bool} (hmk : ∀ h, mk h = h r)
    (hr : StOk P T l m k t z r S) (hm : Min A m T k' t S) (hk : k' ≤ k) (h : child f g mk z = false) : f z r = false := by
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
lemma bi_st {A : Bool → ℕ → ℕ → Prop} {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {ka kc : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hb : Bi A d' a.s c.s S S')
    (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v) (hka : ka = decide (a.s ∈ S')) (hkc : kc = decide (c.s ∈ S'))
    (hsh : Shape (opW d' a c) a c v ka kc r) :
    StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have hsubm : ∀ w ∈ r, w.s &&& m = w.s := fun w hw => by
    rcases hsh.mem hw with rfl | h
    · rw [opW_s, and_op, hs.subm a ha, hs.subm c hc]
    · exact hs.subm w h
  let b' : ℕ → ℕ := fun j => b j - max (fl a j) (fl c j)
  have hcl' : Cl P T k t b' S' := by
    intro j hj q hq
    have hl1 := hle j hj
    have h2 := cnt_two ha hc hs.rep.1 hab j
    simp only [b'] at hq
    constructor
    · intro ht hsol
      subst ht
      by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
      · refine (hcl j hj q ?_).1 rfl (hb.kill (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
        have : 1 ≤ max (fl a j) (fl c j) := by rcases hkill with h | h <;> simp [fl, h]
        have := fl_le a j; have := fl_le c j; omega
      · push Not at hkill
        refine (hcl j hj (q + 1) ?_).1 rfl (hb.im hsol)
        have e1 : fl a j = 0 := by simp [fl, hkill.1]
        have e2 : fl c j = 0 := by simp [fl, hkill.2]
        rw [e1, e2] at hq; simp at hq; omega
    · intro ht hsol
      by_cases hkill : a.c.testBit (5 * j) = true ∨ c.c.testBit (5 * j) = true
      · refine (hcl j hj q ?_).2 ht (hb.kill_pos (hkill.imp (wa.cst hj) (wc.cst hj)) hsol)
        have : 1 ≤ max (fl a j) (fl c j) := by rcases hkill with h | h <;> simp [fl, h]
        have := fl_le a j; have := fl_le c j; omega
      · push Not at hkill
        refine (hcl j hj (q + 1) ?_).2 ht (hb.im_pos hsol)
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
  refine ⟨⟨hrep, hwok, hgood, hsubm, b', fun j hj => ?_, hcl', ?_⟩, ?_⟩
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
lemma drop_ok {A : Bool → ℕ → ℕ → Prop} {k' t : ℕ} {v : List W} {S S' : Finset ℕ} {d' : Bool} {a c : W} {i : ℕ} (hr : Rep v S)
    (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S')
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
lemma node_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    node f d l m g e n z v go = go (pair (modeF n e (mid f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold node nodeC modeF
  cases Nat.ble n e <;> cases Nat.ble (Nat.succ n) e <;> rfl
lemma nodeQ_eq (f : ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ) (v : List W) (go : (XW → XW → Bool) → List XW → Bool)
    (hne : n ≤ e) :
    nodeQ f d l m g e n z v go = go (pair (modeF n e (midQ f m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; unfold nodeQ nodeQC modeF
  rw [Nat.ble_eq_true_of_le hne]; simp only [cond_true]
  cases Nat.ble (Nat.succ n) e <;> rfl
lemma nodeOH_eq (lb : ℕ) (hf : W → W → Bool → Bool → Bool → Bool) (f : ℕ → ℕ → List W → Bool) (d : Bool) (l m g e n z : ℕ)
    (v : List W) (go : (XW → XW → Bool) → List XW → Bool) :
    nodeOH lb hf f d l m g e n z v go = go (pairOH lb hf f m g e n z v) (v.map (mkx d l (wst d l v))) := by
  rw [← mkX_eq]; rfl
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
lemma pairOH_false {lb : ℕ} {hf : W → W → Bool → Bool → Bool → Bool} {f : ℕ → ℕ → List W → Bool}
    {m g e n z : ℕ} {v : List W} {d : Bool} {l o : ℕ} {a c : W}
    (hp : pairOH lb hf f m g e n z v (mkx d l o a) (mkx d l o c) = false) (d' : Bool) (hlb : lb ≤ gkey a.r c.r d') :
    modeF n e (midH (f (gkey a.r c.r d' + 1)) (hf a c d') m g e (Nat.pred n) z v) a c
      (dfc d d' l o a c) (dfc d d' l o c a) (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := by
  simp only [pairOH, mkx, bR] at hp
  have hb := Nat.ble_eq_true_of_le hlb
  cases d'
  · rw [hb, Bool.cond_true] at hp
    have hp1 : modeF n e (midH (f (Nat.succ (gkey a.r c.r false))) (hf a c false) m g e (Nat.pred n) z v) a c
        (Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o))
        (Nat.xor (Nat.land (Nat.land (sp d l c.s) o) a.s) (Nat.land (sp d l c.s) o))
        (Nat.land a.s c.s) (Nat.lor a.a c.a) (Nat.land a.b c.b) = false := by
      revert hp
      cases modeF n e (midH (f (Nat.succ (gkey a.r c.r true))) (hf a c true) m g e (Nat.pred n) z v) a c
        (Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s I.NN))
        (Nat.land (Nat.land (sp d l c.s) o) (Nat.shiftRight a.s I.NN))
        (Nat.lor a.s c.s) (Nat.land a.a c.a) (Nat.lor a.b c.b) <;>
      cases modeF n e (midH (f (Nat.succ (gkey a.r c.r false))) (hf a c false) m g e (Nat.pred n) z v) a c
        (Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o))
        (Nat.xor (Nat.land (Nat.land (sp d l c.s) o) a.s) (Nat.land (sp d l c.s) o))
        (Nat.land a.s c.s) (Nat.lor a.a c.a) (Nat.land a.b c.b) <;>
      cases Nat.ble lb (gkey a.r c.r true) <;> simp
    exact hp1
  · rw [hb, Bool.cond_true] at hp
    have hp1 : modeF n e (midH (f (Nat.succ (gkey a.r c.r true))) (hf a c true) m g e (Nat.pred n) z v) a c
        (Nat.land (Nat.land (sp d l a.s) o) (Nat.shiftRight c.s I.NN))
        (Nat.land (Nat.land (sp d l c.s) o) (Nat.shiftRight a.s I.NN))
        (Nat.lor a.s c.s) (Nat.land a.a c.a) (Nat.lor a.b c.b) = false := by
      revert hp; cases modeF n e (midH (f (Nat.succ (gkey a.r c.r false))) (hf a c false) m g e (Nat.pred n) z v) a c
        (Nat.xor (Nat.land (Nat.land (sp d l a.s) o) c.s) (Nat.land (sp d l a.s) o))
        (Nat.xor (Nat.land (Nat.land (sp d l c.s) o) a.s) (Nat.land (sp d l c.s) o))
        (Nat.land a.s c.s) (Nat.lor a.a c.a) (Nat.land a.b c.b) <;> cases Nat.ble lb (gkey a.r c.r false) <;> simp
    exact hp1
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
lemma midQ_false {f : ℕ → List W → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : midQ f m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    kidsQ (child f g) e n (z + (a.c &&& c.c) - (opW d' a c).c) a.c c.c a.s c.s (Nat.beq da 0) (Nat.beq dc 0)
      (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) = false := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [midQ, st_eq, ec] at h
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
lemma kidsQ_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {e n z x y a c : ℕ} {oa oc : Bool} {mk : (List W → Bool) → Bool}
    (h : kidsQ ch e n z x y a c oa oc mk = false) :
    (oc = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (oa = true → n + 1 ≤ e → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (n + 2 ≤ e → ch mk (z - x - y) = false) := by
  simp only [kidsQ, bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_⟩
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
lemma kidsH_false {ch : ((List W → Bool) → Bool) → ℕ → Bool} {z x y a c : ℕ} {b0 bA bC bAC : Bool} {mk : (List W → Bool) → Bool}
    (h : kidsH ch z x y a c b0 bA bC bAC mk = false) :
    (b0 = true → ch (fun h => mk (fun r => rm a c r h)) z = false) ∧
    (bA = true → ch (fun h => mk (fun r => rm c c r h)) (z - x) = false) ∧
    (bC = true → ch (fun h => mk (fun r => rm a a r h)) (z - y) = false) ∧
    (bAC = true → ch mk (z - x - y) = false) := by
  simp only [kidsH, bR] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1; subst h1; revert h; cases ch (fun h => mk (fun r => rm a c r h)) z <;> simp
  · intro h1; subst h1; revert h; cases ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) <;>
      cases (bif b0 then ch (fun h => mk (fun r => rm a c r h)) z else false) <;> simp
  · intro h1; subst h1; revert h; cases ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) <;>
      cases (bif b0 then ch (fun h => mk (fun r => rm a c r h)) z else false) <;>
      cases (bif bA then ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) else false) <;> simp
  · intro h1; subst h1; revert h; cases ch mk (Nat.sub (Nat.sub z x) y) <;>
      cases (bif b0 then ch (fun h => mk (fun r => rm a c r h)) z else false) <;>
      cases (bif bA then ch (fun h => mk (fun r => rm c c r h)) (Nat.sub z x) else false) <;>
      cases (bif bC then ch (fun h => mk (fun r => rm a a r h)) (Nat.sub z y) else false) <;> simp
lemma midH_false {f : ℕ → List W → Bool} {kf : Bool → Bool → Bool} {m g e n z : ℕ} {v : List W} {a c : W} {da dc : ℕ} {d' : Bool}
    (h : midH f kf m g e n z v a c da dc (opW d' a c).s (opW d' a c).a (opW d' a c).b = false)
    (hg : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true) :
    (da = 0 → dc = 0 → kf false false = true → child f g (fun h => put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v (fun r => rm a.s c.s r h)) (z + (a.c &&& c.c) - (opW d' a c).c) = false) ∧
    (dc = 0 → n + 1 ≤ e → kf true false = true → child f g (fun h => put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v (fun r => rm c.s c.s r h)) (z + (a.c &&& c.c) - (opW d' a c).c - a.c) = false) ∧
    (da = 0 → n + 1 ≤ e → kf false true = true → child f g (fun h => put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v (fun r => rm a.s a.s r h)) (z + (a.c &&& c.c) - (opW d' a c).c - c.c) = false) ∧
    (n + 2 ≤ e → kf true true = true → child f g (put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v) (z + (a.c &&& c.c) - (opW d' a c).c - a.c - c.c) = false) := by
  have ec : Nat.lor (opW d' a c).a (opW d' a c).b = (opW d' a c).c := by cases d' <;> rfl
  simp only [midH, st_eq, ec] at h
  have hg' : Nat.beq (Nat.land (Nat.sub (Nat.add z (Nat.land a.c c.c)) (opW d' a c).c) g) g = true := hg
  rw [hg'] at h
  dsimp only at h
  rw [bR] at h
  have b1 : n + 1 ≤ e → Nat.ble (Nat.succ n) e = true := fun h => Nat.ble_eq_true_of_le h
  have b2 : n + 2 ≤ e → Nat.ble (Nat.succ (Nat.succ n)) e = true := fun h => Nat.ble_eq_true_of_le h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro rfl rfl hk; simp only [Nat.beq_refl, hk, Bool.true_and, Bool.true_or, Bool.cond_true] at h
    exact (kidsH_false h).1 (by simp [hk])
  · rintro rfl hle hk; simp only [Nat.beq_refl, b1 hle, hk, Bool.true_and, Bool.or_true, Bool.true_or, Bool.cond_true] at h
    exact (kidsH_false h).2.1 (by simp [b1 hle, hk])
  · rintro rfl hle hk; simp only [Nat.beq_refl, b1 hle, hk, Bool.true_and, Bool.or_true, Bool.true_or, Bool.cond_true] at h
    exact (kidsH_false h).2.2.1 (by simp [b1 hle, hk])
  · intro hle hk; simp only [b2 hle, hk, Bool.true_and, Bool.or_true, Bool.cond_true] at h
    exact (kidsH_false h).2.2.2 (by simp [b2 hle, hk])
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma rect_ok {A : Bool → ℕ → ℕ → Prop} {t k k' z : ℕ} {r : List W} {S : Finset ℕ} (hr : StOk P T l m k t z r S)
    (hm : Min A m T k' t S) (hk : k' ≤ k) (hn : r.length + t = k + 1) : rect (pos' t) l (wst (pos' t) l r) r [] = false := by
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
lemma hit_ht {k t z : ℕ} {r : List W} {S : Finset ℕ} {d : Bool} (hr : StOk P T l m k t z r S) {a b : W} (ha : a ∈ r) (hb : b ∈ r)
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
def NK (A : Bool → ℕ → ℕ → Prop) (m T k' t : ℕ) (S : Finset ℕ) : Prop :=
  (∀ d a b S1 k0, k' = k0 + 1 → Bi A d a b S S1 → Live A m T k0 t S1 → S1.card < S.card) ∧
  ∀ a S1 k0 t0, k' = k0 + 1 → t = t0 + 1 → Un m a S S1 → Live A m T k0 t0 S1 → S1.card ≤ S.card
lemma Rep.nodup {v : List W} {S : Finset ℕ} (h : Rep v S) : v.Nodup := List.Nodup.of_map _ h.1
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nk_ok {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {k k' t z : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l m k t z v S) (hm : Min A m T k' t S)
    (hx : k' ≤ S.card + t) (hst : flk l (wst (pos' t) l v) v star = false) : NK A m T k' t S := by
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
  have kb : ∀ d a b S1 k0, k' = k0 + 1 → Bi A d a b S S1 → Live A m T k0 t S1 → ∀ U, S = insert a (insert b U) → S1 = insert (op d a b) U → a ∈ U → b ∉ U → False := by
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
      · exact kb d b a S1 k0 hk' (hb.symm hA) hl U (by rw [e1, Finset.insert_comm]) (by rw [e2, op_comm]) hbU ha
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
lemma tst_sound {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {k k' t z : ℕ} {v : List W} {S : Finset ℕ}
    (hs : StOk P T l m k t z v S) (hm : Min A m T k' t S) (hk : k' ≤ k) :
    ∃ y, (∀ F : ℕ → Bool, tst (pos' t) l (k + 1 - t) v F = F y) ∧ (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK A m T k' t S)) := by
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
      | false => exact ⟨1, fun F => by rw [e, h1, h2, hbip, h3]; rfl, Or.inr ⟨rfl, by omega, nk_ok X hA hs hm (by omega) h3⟩⟩
lemma cv_ok {A : Bool → ℕ → ℕ → Prop} {t k k' z : ℕ} {v : List W} {S : Finset ℕ} {b : Bool}
    (hs : StOk P T l m k t z v S) (hl : Live A m T k' t S) (h : cv (pos' t) l v b = false) : b = false := by
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
lemma gate_sound {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : pair (modeF n e (mid f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
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
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep (hb.symm hA) hl hc h hi
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
      r.length = S'.card ∧ StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l m k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
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
lemma gateQ_sound {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hq12 : a.s ∈ S' ∨ c.s ∈ S')
    (hp : pair (modeF n e (midQ f m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨_, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
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
      have := hu i; rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i; rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep (hb.symm hA) hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hpr : Nat.pred v.length + 1 = v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hb.1] at h2
    simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exfalso; exact hq12.elim q1 q2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l m k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child f g mk z' = false → ∃ z' r, f z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hmid := midQ_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard
    exact fin hput c3 c4 ((kidsQ_false hmid).2.2 (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := midQ_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kidsQ_false hmid).1 (b0 (fc q2)) (by omega))
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hmid := midQ_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((kidsQ_false hmid).2.1 (b0 (fa q1)) (by omega))
  · exfalso; exact hq12.elim q1 q2
lemma gateQ_sound_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {f : α → ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ}
    {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hq12 : a.s ∈ S' ∨ c.s ∈ S')
    (hp : ∀ q : α, pair (modeF n e (midQ (f q) m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, (∀ q : α, f q z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨_, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp' : ∀ q : α, modeF v.length e (midQ (f q) m g e (Nat.pred v.length) z v) a c
      (dfc (pos' t) d' l (wst (pos' t) l v) a c) (dfc (pos' t) d' l (wst (pos' t) l v) c a)
      (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := fun q => pair_false (hp q) d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp'
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp'
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (I.NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i; rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i; rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep (hb.symm hA) hl hc h hi
  have b0 : ∀ {q : ℕ}, q = 0 → Nat.beq q 0 = true := fun h => by rw [h]; rfl
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hpr : Nat.pred v.length + 1 = v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hb.1] at h2
    simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
      ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
    intro ka kc r h1 h2 h3
    have := (bi_st X hs hm hk hb hl ha hc h1 h2 h3).1
    exact ⟨this.rep.card.symm, this, fun w hw => h3.mem hw⟩
  have hguard : Nat.beq (Nat.land (z + (a.c &&& c.c) - (opW d' a c).c) g) g = true := by
    by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s4).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s2).2
    · exact (bi_st X hs hm hk hb hl ha hc (by simp [q1]) (by simp [q2]) s3).2
    · exfalso; exact hq12.elim q1 q2
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l m k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      (∀ q : α, child (f q) g mk z' = false) → ∃ z' r, (∀ q : α, f q z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, fun q => child_sound X h1 h2 hmin hk (h4 q), h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    exact fin hput c3 c4 fun q => (kidsQ_false (midQ_false (modeF_false (hp' q) (fun h => by omega) (fun h => by omega)) hguard)).2.2 (by omega)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (kidsQ_false (midQ_false (modeF_false (hp' q) (fun h => by omega) (fun h => Or.inr (fc q2))) hguard)).1 (b0 (fc q2)) (by omega)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (kidsQ_false (midQ_false (modeF_false (hp' q) (fun h => by omega) (fun h => Or.inl (fa q1))) hguard)).2.1 (b0 (fa q1)) (by omega)
  · exfalso; exact hq12.elim q1 q2
lemma gate_sound_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {f : α → ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ}
    {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hp : ∀ q : α, pair (modeF n e (mid (f q) m g e (Nat.pred n) z v)) (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, (∀ q : α, f q z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp' : ∀ q : α, modeF v.length e (mid (f q) m g e (Nat.pred v.length) z v) a c
      (dfc (pos' t) d' l (wst (pos' t) l v) a c) (dfc (pos' t) d' l (wst (pos' t) l v) c a)
      (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := fun q => pair_false (hp q) d'
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp'
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp'
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
    rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep (hb.symm hA) hl hc h hi
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
      r.length = S'.card ∧ StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l m k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      (∀ q : α, child (f q) g mk z' = false) → ∃ z' r, (∀ q : α, f q z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, fun q => child_sound X h1 h2 hmin hk (h4 q), h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    exact fin hput c3 c4 fun q => (kids_false (mid_false (modeF_false (hp' q) (fun h => by omega) (fun h => by omega)) hguard)).2.2.2 (by omega)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (kids_false (mid_false (modeF_false (hp' q) (fun h => by omega) (fun h => Or.inr (fc q2))) hguard)).2.1 (b0 (fc q2)) (by omega)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (kids_false (mid_false (modeF_false (hp' q) (fun h => by omega) (fun h => Or.inl (fa q1))) hguard)).2.2.1 (b0 (fa q1)) (by omega)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (kids_false (mid_false (modeF_false (hp' q) (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard)).1 (b0 (fa q1)) (b0 (fc q2))
lemma gateOH_sound {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {lb : ℕ} {hf : W → W → Bool → Bool → Bool → Bool}
    {f : ℕ → ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hlb : lb ≤ gkey a.r c.r d') (hkf : hf a c d' (decide (a.s ∈ S')) (decide (c.s ∈ S')) = true)
    (hp : pairOH lb hf f m g e n z v (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, f (gkey a.r c.r d' + 1) z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp := pairOH_false hp d' hlb
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
      have := hu i; rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i; rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep (hb.symm hA) hl hc h hi
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hpr : Nat.pred v.length + 1 = v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hb.1] at h2
    simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l m k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      child (f (gkey a.r c.r d' + 1)) g mk z' = false → ∃ z' r, f (gkey a.r c.r d' + 1) z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, child_sound X h1 h2 hmin hk h4, h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    have hk' : hf a c d' true true = true := by simpa [q1, q2] using hkf
    exact fin hput c3 c4 ((midH_false (modeF_false hp (fun h => by omega) (fun h => by omega)) hguard).2.2.2 (by omega) hk')
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hk' : hf a c d' true false = true := by simpa [q1, q2] using hkf
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((midH_false (modeF_false hp (fun h => by omega) (fun h => Or.inr (fc q2))) hguard).2.1 (fc q2) (by omega) hk')
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    have hk' : hf a c d' false true = true := by simpa [q1, q2] using hkf
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((midH_false (modeF_false hp (fun h => by omega) (fun h => Or.inl (fa q1))) hguard).2.2.1 (fa q1) (by omega) hk')
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    have hk' : hf a c d' false false = true := by simpa [q1, q2] using hkf
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 ((midH_false (modeF_false hp (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard).1 (fa q1) (fc q2) hk')
lemma gateOH_sound_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {lb : ℕ} {hf : α → W → W → Bool → Bool → Bool → Bool}
    {f : α → ℕ → ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {a c : W} {d' : Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' a.s c.s S S') (hl : Live A m T k' t S') (ha : a ∈ v) (hc : c ∈ v)
    (hlb : lb ≤ gkey a.r c.r d') (hkf : ∀ q : α, hf q a c d' (decide (a.s ∈ S')) (decide (c.s ∈ S')) = true)
    (hp : ∀ q : α, pairOH lb (hf q) (f q) m g e n z v (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) :
    ∃ z' r, (∀ q : α, f q (gkey a.r c.r d' + 1) z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v := by
  subst hd hn
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (opW d' a c).s := fun w hw e => hfr (by
    rw [← opW_s, ← e]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  have ho0 : (opW d' a c).s ≠ 0 := fun e => hfr (by rw [← opW_s, e]; simp [C])
  have ho1 : (opW d' a c).s ≠ m := fun e => hfr (by rw [← opW_s, e]; simp [C])
  obtain ⟨r0, hr0, hins⟩ := ins_spec (opW d' a c) v hosS
  obtain ⟨s1, s2, s3, s4⟩ := shape_all hosS hr0 hs.rep.1 ha hc hb.1
  have hp' : ∀ q : α, modeF v.length e (midH (f q (gkey a.r c.r d' + 1)) (hf q a c d') m g e (Nat.pred v.length) z v) a c
      (dfc (pos' t) d' l (wst (pos' t) l v) a c) (dfc (pos' t) d' l (wst (pos' t) l v) c a)
      (opW d' a c).s (opW d' a c).a (opW d' a c).b = false := fun q => pairOH_false (hp q) d' hlb
  generalize hoa : dfc (pos' t) d' l (wst (pos' t) l v) a c = da at hp'
  generalize hoc : dfc (pos' t) d' l (wst (pos' t) l v) c a = dc at hp'
  have filt : ∀ {x y : W}, (∀ i, (Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v)).testBit i = true → bif d' then y.s.testBit (I.NN + i) = false else y.s.testBit i = true) →
      dfc (pos' t) d' l (wst (pos' t) l v) x y = 0 := by
    intro x y hu
    unfold dfc
    generalize Nat.land (sp (pos' t) l x.s) (wst (pos' t) l v) = u at *
    cases d'
    · simp only [Bool.cond_false, nl, nx] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i; rw [Nat.testBit_xor, Nat.testBit_and]; cases h1 : u.testBit i <;> simp_all
    · simp only [Bool.cond_true, nl, nsr] at hu ⊢
      apply Nat.eq_of_testBit_eq; intro i
      have := hu i; rw [Nat.testBit_and, Nat.testBit_shiftRight]; cases h1 : u.testBit i <;> simp_all
  have fa : a.s ∉ S' → da = 0 := fun h => by rw [← hoa]; exact filt fun i hi => drop_ok X hs.rep hb hl ha h hi
  have fc : c.s ∉ S' → dc = 0 := fun h => by rw [← hoc]; exact filt fun i hi => drop_ok X hs.rep (hb.symm hA) hl hc h hi
  have hput : ∀ h, put m (opW d' a c).s (opW d' a c).a (opW d' a c).b v h = h r0 := fun h => by
    rw [put_eq (by cases d' <;> rfl) (by cases d' <;> rfl) ho0 ho1, hins]
  have hpr : Nat.pred v.length + 1 = v.length := by
    rw [← hs.rep.card]
    have : ({a.s, c.s} : Finset ℕ) ⊆ S := fun x hx => by simp at hx; rcases hx with rfl | rfl; exacts [hb.sub.1, hb.sub.2.1]
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hb.1] at h2
    simp [Nat.pred_eq_sub_one]; omega
  have main : ∀ {ka kc : Bool} {r : List W}, ka = decide (a.s ∈ S') → kc = decide (c.s ∈ S') → Shape (opW d' a c) a c v ka kc r →
      r.length = S'.card ∧ StOk P T l m k t (z + (a.c &&& c.c) - (opW d' a c).c - (bif ka then a.c else 0) - (bif kc then c.c else 0)) r S' ∧
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
  have fin : ∀ {z' : ℕ} {r : List W} {mk : (List W → Bool) → Bool}, (∀ h, mk h = h r) → StOk P T l m k t z' r S' → (∀ w ∈ r, w = opW d' a c ∨ w ∈ v) →
      (∀ q : α, child (f q (gkey a.r c.r d' + 1)) g mk z' = false) → ∃ z' r, (∀ q : α, f q (gkey a.r c.r d' + 1) z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = opW d' a c ∨ w ∈ v :=
    fun {z' r mk} h1 h2 h3 h4 => ⟨z', r, fun q => child_sound X h1 h2 hmin hk (h4 q), h2, h3⟩
  by_cases q1 : a.s ∈ S' <;> by_cases q2 : c.s ∈ S'
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s4
    have hlen := s4.len; simp at hlen
    exact fin hput c3 c4 fun q => (midH_false (modeF_false (hp' q) (fun h => by omega) (fun h => by omega)) hguard).2.2.2 (by omega) (by simpa [q1, q2] using hkf q)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s2
    have hlen := s2.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (midH_false (modeF_false (hp' q) (fun h => by omega) (fun h => Or.inr (fc q2))) hguard).2.1 (fc q2) (by omega) (by simpa [q1, q2] using hkf q)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s3
    have hlen := s3.len; simp only [Bool.cond_true, Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (midH_false (modeF_false (hp' q) (fun h => by omega) (fun h => Or.inl (fa q1))) hguard).2.2.1 (fa q1) (by omega) (by simpa [q1, q2] using hkf q)
  · obtain ⟨c1, c3, c4⟩ := main (by simp [q1]) (by simp [q2]) s1
    have hlen := s1.len; simp only [Bool.cond_false] at hlen
    exact fin (fun h => by rw [hput, rm_eq]) (by simpa using c3) c4 fun q => (midH_false (modeF_false (hp' q) (fun h => ⟨fa q1, fc q2⟩) (fun h => Or.inl (fa q1))) hguard).1 (fa q1) (fc q2) (by simpa [q1, q2] using hkf q)
end sound
def notW (m : ℕ) (a : W) : W := ⟨a.s ^^^ m, a.b, a.a, a.c, 0⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma un_st {A : Bool → ℕ → ℕ → Prop} {k k' t z : ℕ} {v r : List W} {S S' : Finset ℕ} {a : W} {ka : Bool}
    (hs : StOk P T l m (k + 1) (t + 1) z v S) (hm : Min A m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hb : Un m a.s S S')
    (hl : Live A m T k' t S') (ha : a ∈ v) (hka : ka = decide (a.s ∈ S'))
    (hsh : bif ka then r.Perm (notW m a :: v) else (a :: r).Perm (notW m a :: v)) :
    StOk P T l m k t ((bif pos' t then z - a.c else z) - (bif ka then a.c else 0)) r S' := by
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
  have hsubm : ∀ w ∈ r, w.s &&& m = w.s := fun w hw => by
    rcases hmem w hw with rfl | h
    · change (a.s ^^^ m) &&& m = a.s ^^^ m
      rw [and_neg (Nat.and_self m)]
      have := congrArg (· ^^^ m) (hs.subm a ha)
      apply Nat.eq_of_testBit_eq; intro i
      have ha1 := congrArg (fun x => x.testBit i) (hs.subm a ha)
      simp only [Nat.testBit_xor, Nat.testBit_and] at ha1 ⊢
      revert ha1
      cases hm : m.testBit i <;> cases ha' : a.s.testBit i <;> simp
    · exact hs.subm w h
  let b' : ℕ → ℕ := fun j => bif pos' t then b j - fl a j else b j
  have hcl' : Cl P T k t b' S' := by
    intro j hj q hq
    have hl1 := hle j hj
    have h2 := cnt_one ha hs.rep.1 j
    simp only [b'] at hq
    constructor
    · intro ht hsol
      subst ht
      simp only [pos', Nat.lt_irrefl, decide_false, Bool.cond_false] at hq
      by_cases hkill : a.c.testBit (5 * j) = true
      · refine (hcl j hj (q + 1) (by omega)).2 (by omega) ?_
        exact SolPos.of_sol_lt (hb.kill (X.hP j hj).1 (wa.cst hj hkill) hsol) (Nat.lt_succ_self q)
      · exact (hcl j hj (q + 1) (by omega)).2 (by omega) (hb.im_sol_to_pos (X.hP j hj).1 hsol)
    · intro ht hsol
      have hpt : pos' t = true := by simp [pos', show 0 < t by omega]
      simp only [hpt, Bool.cond_true] at hq
      by_cases hkill : a.c.testBit (5 * j) = true
      · refine (hcl j hj q ?_).2 (by omega) (hb.kill_pos (X.hP j hj).1 (wa.cst hj hkill) hsol)
        have : fl a j = 1 := by simp [fl, hkill]
        omega
      · refine (hcl j hj (q + 1) ?_).2 (by omega) (hb.im_pos (X.hP j hj).1 hsol)
        have e1 : fl a j = 0 := by simp [fl, hkill]
        omega
  have hle' := cnt_le X hrep hwok hcl' (hb.min hl hm.2) hk
  refine ⟨hrep, hwok, hgood, hsubm, b', fun j hj => ?_, hcl', ?_⟩
  · have := hb15 j hj; simp only [b']; cases pos' t <;> simp <;> omega
  · have ea : (bif ka then a.c else 0) = pk P.length (fun j => bif ka then fl a j else 0) := by
      cases ka
      · simp [pk]
      · exact fl_pk wa
    have le1 : ∀ j, (bif ka then fl a j else 0) ≤ 1 := fun j => by cases ka <;> simp [fl_le]
    rw [ea, hz]
    cases hpt : pos' t
    · simp only [hpt, Bool.cond_false, b']
      rw [pk_sub]
      · refine pk_congr fun j hj => ?_
        have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
        have q5 := hcnt j; have q6 := fl_le a j
        simp only [b', hpt, Bool.cond_false] at q2
        cases ka <;> simp at q5 ⊢ <;> omega
      · intro j hj; have := hle j hj; have := le1 j; omega
    · simp only [hpt, Bool.cond_true, b']
      conv_lhs => rw [fl_pk wa]
      rw [pk_sub, pk_sub]
      · refine pk_congr fun j hj => ?_
        have q1 := hle j hj; have q2 := hle' j hj; have q3 := cnt_one ha hs.rep.1 j; have q4 := hb15 j hj
        have q5 := hcnt j; have q6 := fl_le a j
        simp only [b', hpt, Bool.cond_true] at q2
        cases ka <;> simp at q5 ⊢ <;> omega
      · intro j hj; have := hle j hj; have := le1 j; have := fl_le a j; omega
      · intro j hj; have := hle j hj; have := fl_le a j; omega
end sound
lemma nots_false {f : ℕ → ℕ → ℕ → List W → Bool} {m g e n z : ℕ} {subA : Bool} {q lt : ℕ} {v r : List W}
    (h : nots f m g e n z subA q lt v r = false) {a : W} (ha : a ∈ r) (hq : a.s + 1 ≠ q) (hlt : lt = 0 ∨ a.s < lt) :
    ins (notW m a) v (fun v =>
      (bif (bif Nat.ble n e then child (f a.s (a.s ^^^ m)) g (rm a.s a.s v) ((bif subA then z - a.c else z)) else false) then true else
      (bif Nat.ble (n + 1) e then child (f a.s (a.s ^^^ m)) g (fun h => h v) ((bif subA then z - a.c else z) - a.c) else false))) = false := by
  induction r with
  | nil => simp at ha
  | cons w r ih =>
    change (Bool.rec (motive := fun _ => Bool) (nots f m g e n z subA q lt v r) true
      (Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool)
          (st (Nat.xor w.s m) (fun s => st (bif subA then Nat.sub z w.c else z) (fun z =>
            ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
              Bool.rec (motive := fun _ => Bool)
                (Bool.rec (motive := fun _ => Bool) false (child (f w.s s) g (fun h => h v) (Nat.sub z w.c)) (Nat.ble (Nat.succ n) e))
                true
                (Bool.rec (motive := fun _ => Bool) false (child (f w.s s) g (rm w.s w.s v) z) (Nat.ble n e))))))
          false (Nat.beq (Nat.succ w.s) q))
        (Nat.beq lt 0 || Nat.ble (Nat.succ w.s) lt)) : Bool) = false at h
    rw [bR, bR, bR] at h
    simp only [st_eq, bR] at h
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · have hltb : (Nat.beq lt 0 || Nat.ble (Nat.succ a.s) lt) = true := by
        rcases hlt with rfl | hlt
        · simp
        · rw [Nat.ble_eq_true_of_le hlt, Bool.or_true]
      rw [hltb, Bool.cond_true, Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h
      cases hh : ins (notW m a) v (fun v =>
        (bif (bif Nat.ble n e then child (f a.s (a.s ^^^ m)) g (rm a.s a.s v) ((bif subA then z - a.c else z)) else false) then true else
        (bif Nat.ble (n + 1) e then child (f a.s (a.s ^^^ m)) g (fun h => h v) ((bif subA then z - a.c else z) - a.c) else false))) with
      | false => rfl
      | true =>
        have h : (bif ins (notW m a) v (fun v =>
          (bif (bif Nat.ble n e then child (f a.s (a.s ^^^ m)) g (rm a.s a.s v) ((bif subA then z - a.c else z)) else false) then true else
          (bif Nat.ble (n + 1) e then child (f a.s (a.s ^^^ m)) g (fun h => h v) ((bif subA then z - a.c else z) - a.c) else false))) then true
          else nots f m g e n z subA q lt v r) = false := h
        rw [hh] at h; simp at h
    · refine ih ?_ ha
      revert h
      cases nots f m g e n z subA q lt v r <;> simp
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma nots_sound {A : Bool → ℕ → ℕ → Prop} {f : ℕ → ℕ → ℕ → List W → Bool} {e n z q lt t k k' : ℕ} {subA : Bool}
    {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l m (k + 1) (t + 1) z v S) (hm : Min A m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hsubA : subA = pos' t) (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live A m T k' t S') (ha : a ∈ v)
    (hq : a.s + 1 ≠ q) (hlt : lt = 0 ∨ a.s < lt) {rr : List W} (har' : a ∈ rr)
    (hp : nots f m g e n z subA q lt v rr = false) :
    ∃ z' r, f a.s (a.s ^^^ m) z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn hsubA
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have h := nots_false hp har' hq hlt
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
    simp only [Bool.cond_true] at hst
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    rw [hb1] at h
    have h : child (f a.s (a.s ^^^ m)) g (fun h => h r0) ((bif pos' t then z - a.c else z) - a.c) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f a.s (a.s ^^^ m)) g (fun h => h r0) ((bif pos' t then z - a.c else z) - a.c) <;> simp
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
    have h : child (f a.s (a.s ^^^ m)) g (rm a.s a.s r0) (bif pos' t then z - a.c else z) = false := by
      revert h; simp only [Bool.cond_true]
      cases child (f a.s (a.s ^^^ m)) g (rm a.s a.s r0) (bif pos' t then z - a.c else z) <;> simp
    exact ⟨_, _, child_sound X (rm_eq _ _ _) hst hmin hk h, hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
lemma nots_sound_all {α : Type} {A : Bool → ℕ → ℕ → Prop} {f : α → ℕ → ℕ → ℕ → List W → Bool}
    {e n z q lt t k k' : ℕ} {subA : Bool} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l m (k + 1) (t + 1) z v S) (hm : Min A m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hsubA : subA = pos' t) (hSe : S'.card ≤ e) (hb : Un m a.s S S') (hl : Live A m T k' t S') (ha : a ∈ v)
    (hq : a.s + 1 ≠ q) (hlt : lt = 0 ∨ a.s < lt) {rr : List W} (har' : a ∈ rr)
    (hp : ∀ u : α, nots (f u) m g e n z subA q lt v rr = false) :
    ∃ z' r, (∀ u : α, f u a.s (a.s ^^^ m) z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn hsubA
  have hmin := hb.min hl hm.2
  have hfr := hb.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have hu : ∀ u : α, ins (notW m a) v (fun v' =>
      (bif (bif Nat.ble v.length e then child (f u a.s (a.s ^^^ m)) g (rm a.s a.s v') ((bif pos' t then z - a.c else z)) else false) then true else
      (bif Nat.ble (v.length + 1) e then child (f u a.s (a.s ^^^ m)) g (fun h => h v') ((bif pos' t then z - a.c else z) - a.c) else false))) = false :=
    fun u => nots_false (hp u) har' hq hlt
  simp only [hins] at hu
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb hl ha (ka := true) (by simp [q1]) hr0
    simp only [Bool.cond_true] at hst
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    have hdk : ∀ u : α, child (f u a.s (a.s ^^^ m)) g (fun h => h r0) ((bif pos' t then z - a.c else z) - a.c) = false := fun u => by
      have h := hu u
      rw [hb1] at h
      revert h; simp only [Bool.cond_true]
      cases child (f u a.s (a.s ^^^ m)) g (fun h => h r0) ((bif pos' t then z - a.c else z) - a.c) <;> simp
    exact ⟨_, _, fun u => child_sound X (fun h => rfl) hst hmin hk (hdk u), hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    have hdd : ∀ u : α, child (f u a.s (a.s ^^^ m)) g (rm a.s a.s r0) (bif pos' t then z - a.c else z) = false := fun u => by
      have h := hu u
      rw [hb1] at h
      revert h; simp only [Bool.cond_true]
      cases child (f u a.s (a.s ^^^ m)) g (rm a.s a.s r0) (bif pos' t then z - a.c else z) <;> simp
    exact ⟨_, _, fun u => child_sound X (rm_eq _ _ _) hst hmin hk (hdd u), hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
end sound
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma notsC_sound_all {α : Type} {A : Bool → ℕ → ℕ → Prop} {Hs : α → ℕ} {f : α → ℕ → ℕ → ℕ → List W → Bool}
    {e n z q lt t k k' : ℕ} {subA : Bool} {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l m (k + 1) (t + 1) z v S) (hm : Min A m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hsubA : subA = pos' t) (hSe : S'.card ≤ e) (hb_u : Un m a.s S S') (hl : Live A m T k' t S') (ha : a ∈ v)
    (hq : a.s + 1 ≠ q) (hlt : lt = 0 ∨ a.s < lt) {rr : List W} (har' : a ∈ rr)
    (hH : ∀ u : α, hb (Hs u) (hashNot a.s (decide (a.s ∈ S'))) = true)
    (hp : ∀ u : α, notsC (Hs u) (f u) m g e n z subA q lt v rr = false) :
    ∃ z' r, (∀ u : α, f u a.s (a.s ^^^ m) z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  subst hn hsubA
  have hmin := hb_u.min hl hm.2
  have hfr := hb_u.fresh hl hm.2
  have hosS : ∀ w ∈ v, w.s ≠ (notW m a).s := fun w hw e => hfr (by
    change a.s ^^^ m ∈ _
    have : w.s = a.s ^^^ m := e
    rw [← this]; exact sub_C _ _ (by simpa using hs.rep.mem.2 ⟨w, hw, rfl⟩))
  obtain ⟨r0, hr0, hins⟩ := ins_spec (notW m a) v hosS
  have hl0 : r0.length = v.length + 1 := by rw [hr0.length_eq]; simp
  have hnd : (r0.map W.s).Nodup := by
    refine (hr0.map W.s).nodup_iff.2 ?_
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and]
    exact ⟨fun w hw => hosS w hw, hs.rep.1⟩
  have har : a ∈ r0 := hr0.symm.subset (by simp [ha])
  have hmem : ∀ w ∈ r0, w = notW m a ∨ w ∈ v := fun w hw => by simpa using hr0.subset hw
  by_cases q1 : a.s ∈ S'
  · have hst := un_st X hs hm hk hb_u hl ha (ka := true) (by simp [q1]) hr0
    simp only [Bool.cond_true] at hst
    have hc := hst.rep.card
    have hb1 : Nat.ble (v.length + 1) e = true := Nat.ble_eq_true_of_le (by omega)
    have hdk : ∀ u : α, child (f u a.s (a.s ^^^ m)) g (fun h => h r0) ((bif pos' t then z - a.c else z) - a.c) = false := by
      intro u
      have hu := hH u
      simp only [q1, decide_true] at hu
      revert har' hp
      induction rr with
      | nil => intro har' _; simp at har'
      | cons w rr ih =>
        intro har' hp
        have h0 := hp u
        change (Bool.rec (motive := fun _ => Bool) (notsC (Hs u) (f u) m g e v.length z (pos' t) q lt v rr) true
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool)
              (let bD := Nat.ble v.length e && hb (Hs u) (hashNot w.s false)
               let bK := Nat.ble (Nat.succ v.length) e && hb (Hs u) (hashNot w.s true)
               Bool.rec (motive := fun _ => Bool) false
                 (st (Nat.xor w.s m) (fun s => st (bif pos' t then Nat.sub z w.c else z) (fun z =>
                   ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
                     Bool.rec (motive := fun _ => Bool)
                       (Bool.rec (motive := fun _ => Bool) false (child (f u w.s s) g (fun h => h v) (Nat.sub z w.c)) bK)
                       true
                       (Bool.rec (motive := fun _ => Bool) false (child (f u w.s s) g (rm w.s w.s v) z) bD)))))
                 (bD || bK))
              false (Nat.beq (Nat.succ w.s) q))
            (Nat.beq lt 0 || Nat.ble (Nat.succ w.s) lt)) : Bool) = false at h0
        rw [bR, bR, bR, bR] at h0
        simp only [List.mem_cons] at har'
        rcases har' with rfl | har'
        · have hltb : (Nat.beq lt 0 || Nat.ble (Nat.succ a.s) lt) = true := by
            rcases hlt with rfl | hlt
            · simp
            · rw [Nat.ble_eq_true_of_le hlt, Bool.or_true]
          rw [hltb, Bool.cond_true, Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h0
          have hK : (Nat.ble (Nat.succ v.length) e && hb (Hs u) (hashNot a.s true)) = true := by
            simp only [Bool.and_eq_true, hb1, hu, and_self]
          rw [hK, Bool.or_true, Bool.cond_true] at h0
          simp only [st_eq, bR, hK, Bool.cond_true] at h0
          have hins' : ∀ h : List W → Bool, ins ⟨Nat.xor a.s m, a.b, a.a, a.c, 0⟩ v h = h r0 := hins
          rw [hins'] at h0
          by_contra hc
          have hc' : child (f u a.s (a.s ^^^ m)) g (fun h => h r0) ((if pos' t = true then z - a.c else z) - a.c) = true := by
            simpa using Bool.eq_true_of_not_eq_false hc
          simp [hc'] at h0
        · refine ih har' fun u' => ?_
          have hu' := hp u'
          change (Bool.rec (motive := fun _ => Bool) (notsC (Hs u') (f u') m g e v.length z (pos' t) q lt v rr) true _) = false at hu'
          rw [bR] at hu'
          revert hu'
          cases notsC (Hs u') (f u') m g e v.length z (pos' t) q lt v rr <;> simp
    exact ⟨_, _, fun u => child_sound X (fun h => rfl) hst hmin hk (hdk u), hst, hmem⟩
  · have hperm : (a :: r0.filter (fun w => !(Nat.beq w.s a.s || Nat.beq w.s a.s))).Perm (notW m a :: v) := by
      rw [filter1]; exact (filter_perm hnd har).trans hr0
    have hst := un_st X hs hm hk hb_u hl ha (ka := false) (by simp [q1]) hperm
    simp only [Bool.cond_false, Nat.sub_zero] at hst
    have hc := hst.rep.card
    have hlen := hperm.length_eq
    simp only [List.length_cons] at hlen
    have hb1 : Nat.ble v.length e = true := Nat.ble_eq_true_of_le (by omega)
    have hdd : ∀ u : α, child (f u a.s (a.s ^^^ m)) g (rm a.s a.s r0) (bif pos' t then z - a.c else z) = false := by
      intro u
      have hu := hH u
      simp only [q1, decide_false] at hu
      revert har' hp
      induction rr with
      | nil => intro har' _; simp at har'
      | cons w rr ih =>
        intro har' hp
        have h0 := hp u
        change (Bool.rec (motive := fun _ => Bool) (notsC (Hs u) (f u) m g e v.length z (pos' t) q lt v rr) true
          (Bool.rec (motive := fun _ => Bool) false
            (Bool.rec (motive := fun _ => Bool)
              (let bD := Nat.ble v.length e && hb (Hs u) (hashNot w.s false)
               let bK := Nat.ble (Nat.succ v.length) e && hb (Hs u) (hashNot w.s true)
               Bool.rec (motive := fun _ => Bool) false
                 (st (Nat.xor w.s m) (fun s => st (bif pos' t then Nat.sub z w.c else z) (fun z =>
                   ins ⟨s, w.b, w.a, w.c, 0⟩ v (fun v =>
                     Bool.rec (motive := fun _ => Bool)
                       (Bool.rec (motive := fun _ => Bool) false (child (f u w.s s) g (fun h => h v) (Nat.sub z w.c)) bK)
                       true
                       (Bool.rec (motive := fun _ => Bool) false (child (f u w.s s) g (rm w.s w.s v) z) bD)))))
                 (bD || bK))
              false (Nat.beq (Nat.succ w.s) q))
            (Nat.beq lt 0 || Nat.ble (Nat.succ w.s) lt)) : Bool) = false at h0
        rw [bR, bR, bR, bR] at h0
        simp only [List.mem_cons] at har'
        rcases har' with rfl | har'
        · have hltb : (Nat.beq lt 0 || Nat.ble (Nat.succ a.s) lt) = true := by
            rcases hlt with rfl | hlt
            · simp
            · rw [Nat.ble_eq_true_of_le hlt, Bool.or_true]
          rw [hltb, Bool.cond_true, Bool.eq_false_iff.2 fun h => hq (Nat.eq_of_beq_eq_true h), Bool.cond_false] at h0
          have hD : (Nat.ble v.length e && hb (Hs u) (hashNot a.s false)) = true := by
            simp only [Bool.and_eq_true, hb1, hu, and_self]
          rw [hD, Bool.true_or, Bool.cond_true] at h0
          simp only [st_eq, bR, hD, Bool.cond_true] at h0
          have hins' : ∀ h : List W → Bool, ins ⟨Nat.xor a.s m, a.b, a.a, a.c, 0⟩ v h = h r0 := hins
          rw [hins'] at h0
          by_contra hc
          have hc' : child (f u a.s (a.s ^^^ m)) g (rm a.s a.s r0) (if pos' t = true then z - a.c else z) = true := by
            simpa using Bool.eq_true_of_not_eq_false hc
          simp [hc'] at h0
        · refine ih har' fun u' => ?_
          have hu' := hp u'
          change (Bool.rec (motive := fun _ => Bool) (notsC (Hs u') (f u') m g e v.length z (pos' t) q lt v rr) true _) = false at hu'
          rw [bR] at hu'
          revert hu'
          cases notsC (Hs u') (f u') m g e v.length z (pos' t) q lt v rr <;> simp
    exact ⟨_, _, fun u => child_sound X (rm_eq _ _ _) hst hmin hk (hdd u), hst, fun w hw => hmem w (List.mem_of_mem_filter hw)⟩
lemma notsC_sound {A : Bool → ℕ → ℕ → Prop} {H : ℕ} {f : ℕ → ℕ → ℕ → List W → Bool} {e n z q lt t k k' : ℕ} {subA : Bool}
    {v : List W} {S S' : Finset ℕ} {a : W}
    (hs : StOk P T l m (k + 1) (t + 1) z v S) (hm : Min A m T (k' + 1) (t + 1) S) (hk : k' ≤ k) (hn : n = v.length)
    (hsubA : subA = pos' t) (hSe : S'.card ≤ e) (hb_u : Un m a.s S S') (hl : Live A m T k' t S') (ha : a ∈ v)
    (hq : a.s + 1 ≠ q) (hlt : lt = 0 ∨ a.s < lt) {rr : List W} (har' : a ∈ rr)
    (hH : hb H (hashNot a.s (decide (a.s ∈ S'))) = true) (hp : notsC H f m g e n z subA q lt v rr = false) :
    ∃ z' r, f a.s (a.s ^^^ m) z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, w = notW m a ∨ w ∈ v := by
  obtain ⟨z', r, hf, hst, hmem⟩ := notsC_sound_all X (α := Unit) (Hs := fun _ => H) (f := fun _ => f) hs hm hk hn hsubA hSe hb_u hl ha hq hlt har'
    (fun _ => hH) (fun _ => hp)
  exact ⟨z', r, hf (), hst, hmem⟩
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
lemma opW_r (d : Bool) (a c : W) : (opW d a c).r = 0 := by cases d <;> rfl
lemma mv_false (F : ℕ → ℕ → ℕ → List W → Bool) (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mv F l m g k t z v y = false) :
    node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false ∧
    ∀ s, t = s + 1 → nots (fun a0 q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
      bif node (F (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q) then true
      else prd s (fun s2 => nots (fun _ q' z v => cv (pos' s2) l v (tst (pos' s2) l (k - 1 - s2) v (fun y =>
        nodeQ (F (k - 3) s2) (pos' s2) l m g (k - 2 - s2 - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s2 - y) v.length z (pos' s2) (q + 1) a0 v v)))) m g (k - s - y) v.length z (pos' s) 0 0 v v = false := by
  change (Bool.rec (motive := fun _ => Bool) (prd t (fun s => nots (fun a0 q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
      (Bool.rec (motive := fun _ => Bool) (prd s (fun s2 => nots (fun _ q' z v => cv (pos s2) l v (tst (pos s2) l (k - 1 - s2) v (fun y =>
        nodeQ (F (k - 3) s2) (pos s2) l m g (k - 2 - s2 - y) v.length z v (pairsQ q q'))))
        m g (k - 1 - s2 - y) v.length z (pos s2) (q + 1) a0 v v)) true
        (node (F (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)) : Bool)))) m g (k - s - y) v.length z (pos s) 0 0 v v)) true
      (node (F (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  simp only [bR, pos_eq] at h
  cases h1 : node (F (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
  | true => rw [h1] at h; simp at h
  | false =>
    rw [h1, Bool.cond_false] at h
    refine ⟨rfl, ?_⟩
    rintro s rfl
    exact h
lemma NK.sizeB {A : Bool → ℕ → ℕ → Prop} {m T k k' t : ℕ} {S S1 : Finset ℕ} {d : Bool} {a b n y : ℕ} (hn : S.card = n) (hm : Min A m T (k' + 1) t S) (hk : k' + 1 ≤ k)
    (hb : Bi A d a b S S1) (hl : Live A m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + t = k ∧ NK A m T (k' + 1) t S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.1 d a b S1 k' rfl hb hl; omega
lemma NK.sizeU {A : Bool → ℕ → ℕ → Prop} {m T k k' t : ℕ} {S S1 : Finset ℕ} {a n y : ℕ} (hn : S.card = n) (hm : Min A m T (k' + 1) (t + 1) S) (hk : k' + 1 ≤ k)
    (hb : Un m a S S1) (hl : Live A m T k' t S1) (hy : y = 0 ∨ (y = 1 ∧ n + (t + 1) = k ∧ NK A m T (k' + 1) (t + 1) S)) : S1.card ≤ k - t - y := by
  have hs := (hb.min hl hm.2).size.1
  rcases hy with rfl | ⟨rfl, h1, h2⟩
  · omega
  · have := h2.2 a S1 k' t rfl rfl hb hl; omega
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma node_bi {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : node f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [node_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hA hs hm hk hd hn hSe hb hl ha hc h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound X hA hs hm hk hd hn hSe (hb.symm hA) hl hc ha h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma nodeQ_bi {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {f : ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hne : n ≤ e) (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S') (hq12 : x ∈ S' ∨ y ∈ S')
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : nodeQ f d l m g e n z v go = false) : ∃ z' r, f z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [nodeQ_eq _ _ _ _ _ _ _ _ _ _ hne] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gateQ_sound X hA hs hm hk hd hn hSe hb hl ha hc hq12 h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gateQ_sound X hA hs hm hk hd hn hSe (hb.symm hA) hl hc ha hq12.symm h
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma nodeOH_bi {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {lb : ℕ} {hf : W → W → Bool → Bool → Bool → Bool} {f : ℕ → ℕ → List W → Bool}
    {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S')
    (hlb : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → lb ≤ gkey a.r c.r d')
    (hkf1 : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → hf a c d' (decide (a.s ∈ S')) (decide (c.s ∈ S')) = true)
    (hkf2 : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → hf c a d' (decide (c.s ∈ S')) (decide (a.s ∈ S')) = true)
    (hgo : ∀ h xs, go h xs = false → ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → xs = v.map (mkx d l (wst d l v)) →
      h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false ∨ h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false)
    (hp : nodeOH lb hf f d l m g e n z v go = false) :
    ∃ a c : W, a ∈ v ∧ c ∈ v ∧ a.s = x ∧ c.s = y ∧
      ∃ z' r, f (gkey a.r c.r d' + 1) z' r = false ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  rw [nodeOH_eq] at hp
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo _ _ hp a c ha hc rfl rfl rfl with h | h
  · obtain ⟨z', r, h1, h2, h3⟩ := gateOH_sound X hA hs hm hk hd hn hSe hb hl ha hc (hlb a c ha hc rfl rfl) (hkf1 a c ha hc rfl rfl) h
    exact ⟨a, c, ha, hc, rfl, rfl, z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gateOH_sound X hA hs hm hk hd hn hSe (hb.symm hA) hl hc ha
      (by rw [gkey_comm]; exact hlb a c ha hc rfl rfl) (hkf2 a c ha hc rfl rfl) h
    rw [gkey_comm] at h1
    exact ⟨a, c, ha, hc, rfl, rfl, z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma nodeOH_bi_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {lb : ℕ} {hf : α → W → W → Bool → Bool → Bool → Bool}
    {f : α → ℕ → ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : α → (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S')
    (hlb : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → lb ≤ gkey a.r c.r d')
    (hkf1 : ∀ q : α, ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → hf q a c d' (decide (a.s ∈ S')) (decide (c.s ∈ S')) = true)
    (hkf2 : ∀ q : α, ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → hf q c a d' (decide (c.s ∈ S')) (decide (a.s ∈ S')) = true)
    (hgo : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
      (∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) ∨
      (∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false))
    (hp : ∀ q : α, nodeOH lb (hf q) (f q) d l m g e n z v (go q) = false) :
    ∃ a c : W, a ∈ v ∧ c ∈ v ∧ a.s = x ∧ c.s = y ∧
      ∃ z' r, (∀ q : α, f q (gkey a.r c.r d' + 1) z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  have hp' : ∀ q : α, go q (pairOH lb (hf q) (f q) m g e n z v) (v.map (mkx d l (wst d l v))) = false := fun q => by
    have hq := hp q; rw [nodeOH_eq] at hq; exact hq
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo a c ha hc rfl rfl with hdir | hdir
  · obtain ⟨z', r, h1, h2, h3⟩ := gateOH_sound_all X hA hs hm hk hd hn hSe hb hl ha hc (hlb a c ha hc rfl rfl) (fun q => hkf1 q a c ha hc rfl rfl) fun q => hdir q _ _ (hp' q) rfl
    exact ⟨a, c, ha, hc, rfl, rfl, z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gateOH_sound_all X hA hs hm hk hd hn hSe (hb.symm hA) hl hc ha
      (by rw [gkey_comm]; exact hlb a c ha hc rfl rfl) (fun q => hkf2 q a c ha hc rfl rfl) fun q => hdir q _ _ (hp' q) rfl
    refine ⟨a, c, ha, hc, rfl, rfl, z', r, ?_, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
    intro q; rw [gkey_comm]; exact h1 q
lemma nodeOH_bi_l_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {lb : ℕ} {hf : α → W → W → Bool → Bool → Bool → Bool}
    {f : α → ℕ → ℕ → List W → Bool} {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : α → (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S')
    (hlb : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → lb ≤ gkey a.r c.r d')
    (hkf1 : ∀ q : α, ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y → hf q a c d' (decide (a.s ∈ S')) (decide (c.s ∈ S')) = true)
    (hgo : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
      ∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false)
    (hp : ∀ q : α, nodeOH lb (hf q) (f q) d l m g e n z v (go q) = false) :
    ∃ a c : W, a ∈ v ∧ c ∈ v ∧ a.s = x ∧ c.s = y ∧
      ∃ z' r, (∀ q : α, f q (gkey a.r c.r d' + 1) z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  have hp' : ∀ q : α, go q (pairOH lb (hf q) (f q) m g e n z v) (v.map (mkx d l (wst d l v))) = false := fun q => by
    have hq := hp q; rw [nodeOH_eq] at hq; exact hq
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  obtain ⟨z', r, h1, h2, h3⟩ := gateOH_sound_all X hA hs hm hk hd hn hSe hb hl ha hc (hlb a c ha hc rfl rfl) (fun q => hkf1 q a c ha hc rfl rfl) fun q => hgo a c ha hc rfl rfl q _ _ (hp' q) rfl
  exact ⟨a, c, ha, hc, rfl, rfl, z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
lemma node_bi_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {f : α → ℕ → List W → Bool}
    {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : α → (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S')
    (hgo : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
      (∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) ∨
      (∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false))
    (hp : ∀ q : α, node (f q) d l m g e n z v (go q) = false) :
    ∃ z' r, (∀ q : α, f q z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  have hp' : ∀ q : α, go q (pair (modeF n e (mid (f q) m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) = false := fun q => by
    have hq := hp q; rw [node_eq] at hq; exact hq
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo a c ha hc rfl rfl with hdir | hdir
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound_all X hA hs hm hk hd hn hSe hb hl ha hc fun q => hdir q _ _ (hp' q) rfl
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gate_sound_all X hA hs hm hk hd hn hSe (hb.symm hA) hl hc ha fun q => hdir q _ _ (hp' q) rfl
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma nodeQ_bi_all {A : Bool → ℕ → ℕ → Prop} (hA : SymA A) {α : Type} {f : α → ℕ → List W → Bool}
    {d : Bool} {e n z t k k' : ℕ} {v : List W} {S S' : Finset ℕ} {x y : ℕ} {d' : Bool}
    {go : α → (XW → XW → Bool) → List XW → Bool}
    (hs : StOk P T l m (k + 1) t z v S) (hm : Min A m T (k' + 1) t S) (hk : k' ≤ k) (hd : d = pos' t) (hn : n = v.length)
    (hne : n ≤ e) (hSe : S'.card ≤ e) (hb : Bi A d' x y S S') (hl : Live A m T k' t S') (hq12 : x ∈ S' ∨ y ∈ S')
    (hgo : ∀ a c : W, a ∈ v → c ∈ v → a.s = x → c.s = y →
      (∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) a) (mkx d l (wst d l v) c) = false) ∨
      (∀ q : α, ∀ h xs, go q h xs = false → xs = v.map (mkx d l (wst d l v)) → h (mkx d l (wst d l v) c) (mkx d l (wst d l v) a) = false))
    (hp : ∀ q : α, nodeQ (f q) d l m g e n z v (go q) = false) :
    ∃ z' r, (∀ q : α, f q z' r = false) ∧ StOk P T l m k t z' r S' ∧ ∀ w ∈ r, (w.s = op d' x y ∧ w.r = 0) ∨ w ∈ v := by
  have hp' : ∀ q : α, go q (pair (modeF n e (midQ (f q) m g e (Nat.pred n) z v))) (v.map (mkx d l (wst d l v))) = false := fun q => by
    have hq := hp q; rw [nodeQ_eq _ _ _ _ _ _ _ _ _ _ hne] at hq; exact hq
  obtain ⟨a, ha, rfl⟩ := hs.rep.mem.1 hb.sub.1
  obtain ⟨c, hc, rfl⟩ := hs.rep.mem.1 hb.sub.2.1
  rcases hgo a c ha hc rfl rfl with hdir | hdir
  · obtain ⟨z', r, h1, h2, h3⟩ := gateQ_sound_all X hA hs hm hk hd hn hSe hb hl ha hc hq12 fun q => hdir q _ _ (hp' q) rfl
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s], by rw [e, opW_r]⟩) id⟩
  · obtain ⟨z', r, h1, h2, h3⟩ := gateQ_sound_all X hA hs hm hk hd hn hSe (hb.symm hA) hl hc ha hq12.symm fun q => hdir q _ _ (hp' q) rfl
    exact ⟨z', r, h1, h2, fun w hw => (h3 w hw).imp (fun e => ⟨by rw [e, opW_s, op_comm], by rw [e, opW_r]⟩) id⟩
lemma mv_sound {R : ℕ → ℕ} {F : ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ), F k t z v = false → StOk P T l m k t z v S → Cod R v → ∀ k' ≤ k, ¬ Min (AR R) m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l m k t z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : mv F l m g k t z v y = false) : ∀ k' ≤ k, Min (AR R) m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK (AR R) m T k' t S)) → False := by
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
  rcases first_move (AR.symm R) k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hb, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hb, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, ha'a, hu, hne, hu', hb, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X (AR.symm R) hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hb hl hy) hb hl (fun h xs hp xa xc hxa hxc hax hcy hxs => by
      subst hxs
      refine pairsN_false hp (List.mem_map_of_mem hxa) (List.mem_map_of_mem hxc) ?_ ?_
      · intro e
        have : xa.s = xc.s := congrArg XW.s e
        exact hb.1 (by rw [← hax, ← hcy, this])
      · by_contra hc'
        push Not at hc'
        change xa.r ≠ 0 ∧ xc.r ≠ 0 at hc'
        obtain ⟨_, U, _, _, hal⟩ := hb
        have h1 : xa.r = R xa.s := (hcod xa hxa).resolve_left hc'.1
        have h2 : xc.r = R xc.s := (hcod xc hxc).resolve_left hc'.2
        rw [← hax, ← hcy] at hal
        exact hal.elim (fun e => hc'.1 (by rw [h1, e])) (fun e => hc'.2 (by rw [h2, e]))) hA
    exact hF _ _ _ _ _ hf hst (codB hcod hmem) k0 (by simpa using hk) (hb.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hb.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN t0 rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 1) hs hm (by omega) rfl rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) (Or.inl rfl) hwa h2
    have hm1 := hu.min hl1 hm.2
    have hf1 := cv_ok X hst1 hl1 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X (AR.symm R) hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    rw [Bool.not_eq_true] at hf2
    obtain ⟨z', r, hf, hst, hmem⟩ := node_bi X (AR.symm R) hst1 hm1 (by omega) rfl rfl (NK.sizeB hst1.rep.card hm1 (by omega) hb hl hy1) hb hl (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsP_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) (fun e => hb.1 (by rw [← hcy, ← e]; rfl)))) hf2
    exact hF _ _ _ _ _ hf hst (codB (codU hcod hmem1) hmem) k0 (by simpa using hk) (hb.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hb.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    have h2 := hN (t0 + 1) rfl
    obtain ⟨z1, r1, hf1, hst1, hmem1⟩ := nots_sound X (k := k + 2) hs hm (by omega) rfl rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) (Or.inl rfl) hwa h2
    have hm1 := hu.min hl2 hm.2
    have hf1 := cv_ok X hst1 hl2 hf1
    obtain ⟨y1, hF1, hy1⟩ := tst_sound X (AR.symm R) hst1 hm1 (by omega)
    have hf1 := (hF1 _).symm.trans hf1
    beta_reduce at hf1
    rw [Bool.cond_eq_ite] at hf1
    split_ifs at hf1 with hf2
    dsimp only [prd] at hf1
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 3 = k by omega, show k + 3 - 2 = k + 1 by omega] at hf1
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    obtain ⟨z2, r2, hf3, hst2, hmem2⟩ := nots_sound X (k := k + 1) hst1 hm1 (by omega) rfl rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1) hu' hl1 hwa' (by omega) (Or.inr ha'a) hwa' hf1
    have hm2 := hu'.min hl1 hm1.2
    have hf3 := cv_ok X hst2 hl1 hf3
    obtain ⟨y2, hF3, hy2⟩ := tst_sound X (AR.symm R) hst2 hm2 (by omega)
    have hf3 := (hF3 _).symm.trans hf3
    beta_reduce at hf3
    have hSsubm : ∀ x ∈ S, x &&& m = x := fun x hx => by
      obtain ⟨wx, hwx, rfl⟩ := hs.rep.mem.1 hx; exact hs.subm wx hwx
    have hq12 := Branch3_no_can0 hm hSsubm hu hne hu' hb hl
    have hS3len := NK.sizeB hst2.rep.card hm2 (by omega) hb hl hy2
    have hS2leS3 : S2.card ≤ S3.card := by
      obtain ⟨_, U, eS2, eS3, _⟩ := id hb
      have hfr3 := hb.fresh hl hm2.2
      have hopU : op d (wa.s ^^^ m) (wa'.s ^^^ m) ∉ U := fun h => hfr3 (sub_C _ _ (by rw [eS2]; simp [h]))
      have hu12 : wa.s ^^^ m ∈ U ∨ wa'.s ^^^ m ∈ U := by
        rcases hq12 with h | h
        · rw [eS3, Finset.mem_insert] at h
          exact Or.inl (h.resolve_left fun e => hfr3 (sub_C _ _ (by rw [eS2, ← e]; simp)))
        · rw [eS3, Finset.mem_insert] at h
          exact Or.inr (h.resolve_left fun e => hfr3 (sub_C _ _ (by rw [eS2, ← e]; simp)))
      rw [eS3, Finset.card_insert_of_notMem hopU, eS2]
      rcases hu12 with h | h
      · rw [Finset.insert_comm, Finset.insert_eq_of_mem h]; exact Finset.card_insert_le _ U
      · rw [Finset.insert_eq_of_mem h]; exact Finset.card_insert_le _ U
    have hne2 : r2.length ≤ k + 1 - t0 - y2 := by
      have := hst2.rep.card; omega
    obtain ⟨z', r, hf, hst, hmem⟩ := nodeQ_bi X (AR.symm R) hst2 hm2 (by omega) rfl rfl hne2 hS3len hb hl hq12 (fun h xs hp a c ha hc hax hcy hxs => by
      subst hxs
      exact Or.inl (pairsQ_false hp (List.mem_map_of_mem ha) hax (List.mem_map_of_mem hc) hcy)) hf3
    exact hF _ _ _ _ _ hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by simpa using hk) (hb.min hl hm2.2)
theorem look_sound {R : ℕ → ℕ} : ∀ (fuel k t z : ℕ) (v : List W) (S : Finset ℕ), look l m g fuel k t z v = false → StOk P T l m k t z v S → Cod R v →
    ∀ k' ≤ k, ¬ Min (AR R) m T k' t S := by
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
      obtain ⟨y, hFy, hyk⟩ := tst_sound X (AR.symm R) hs hm hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      exact mv_sound X ih hs hcod hlen hy k' hk hm hyk
end sound
lemma gkey_inj {ra rb ra' rb' : ℕ} {d d' : Bool} (ha : ra ≤ 6) (hb : rb ≤ 6) (ha' : ra' ≤ 6) (hb' : rb' ≤ 6)
    (he : gkey ra rb d = gkey ra' rb' d') : d = d' ∧ ((ra = ra' ∧ rb = rb') ∨ (ra = rb' ∧ rb = ra')) := by
  unfold gkey at he
  cases d <;> cases d' <;> cases h1 : Nat.ble ra rb <;> cases h2 : Nat.ble ra' rb' <;>
    simp only [h1, h2, Bool.cond_true, Bool.cond_false] at he
  all_goals first
    | (have q1 := Nat.le_of_ble_eq_true h1; have q2 := Nat.le_of_ble_eq_true h2; refine ⟨rfl, Or.inl ⟨by omega, by omega⟩⟩)
    | (have q1 : rb < ra := by by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
       have q2 := Nat.le_of_ble_eq_true h2; refine ⟨rfl, Or.inr ⟨by omega, by omega⟩⟩)
    | (have q1 := Nat.le_of_ble_eq_true h1
       have q2 : rb' < ra' := by by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h2; simp at h2
       refine ⟨rfl, Or.inr ⟨by omega, by omega⟩⟩)
    | (have q1 : rb < ra := by by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h1; simp at h1
       have q2 : rb' < ra' := by by_contra hc; rw [Nat.ble_eq_true_of_le (by omega)] at h2; simp at h2
       refine ⟨rfl, Or.inl ⟨by omega, by omega⟩⟩)
    | omega
def rIdxAux (P : List ℕ) (m s k : ℕ) : ℕ := match P with
  | [] => 0
  | w :: ws => bif Nat.beq (w &&& m) s then k else rIdxAux ws m s (k + 1)
def rIdx (m s : ℕ) : ℕ := rIdxAux I.rawP m s 1
lemma rIdxAux_bound (P : List ℕ) (m s k : ℕ) : rIdxAux P m s k = 0 ∨ (k ≤ rIdxAux P m s k ∧ rIdxAux P m s k < k + P.length) := by
  induction P generalizing k with
  | nil => simp [rIdxAux]
  | cons w ws ih =>
    unfold rIdxAux
    cases Nat.beq (w &&& m) s
    · simp only [Bool.cond_false, List.length_cons]
      rcases ih (k + 1) with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by omega⟩
    · simp only [Bool.cond_true, List.length_cons]; exact Or.inr ⟨le_rfl, by omega⟩
lemma rIdxAux_inj (P : List ℕ) (m : ℕ) : ∀ {s s' k : ℕ}, 1 ≤ k → rIdxAux P m s k ≠ 0 → rIdxAux P m s k = rIdxAux P m s' k → s = s' := by
  induction P with
  | nil => intro s s' k _ h1; simp [rIdxAux] at h1
  | cons w ws ih =>
    intro s s' k hk h1 he
    unfold rIdxAux at h1 he
    cases c1 : Nat.beq (w &&& m) s <;> cases c2 : Nat.beq (w &&& m) s' <;> simp only [c1, c2, Bool.cond_true, Bool.cond_false] at h1 he
    · exact ih (by omega) h1 he
    · rcases rIdxAux_bound ws m s (k + 1) with h0 | ⟨hb, _⟩
      · exact absurd h0 h1
      · omega
    · rcases rIdxAux_bound ws m s' (k + 1) with h0 | ⟨hb, _⟩
      · rw [he] at h1; exact absurd h0 h1
      · omega
    · exact (Nat.eq_of_beq_eq_true c1).symm.trans (Nat.eq_of_beq_eq_true c2)
lemma rIdxAux_pos (P : List ℕ) (m s : ℕ) : ∀ {k : ℕ}, 1 ≤ k → (∃ w ∈ P, w &&& m = s) → rIdxAux P m s k ≠ 0 := by
  induction P with
  | nil => rintro k _ ⟨w, hw, _⟩; simp at hw
  | cons w ws ih =>
    intro k hk ⟨w', hw', he⟩
    unfold rIdxAux
    cases c1 : Nat.beq (w &&& m) s
    · simp only [Bool.cond_false]
      refine ih (by omega) ⟨w', ?_, he⟩
      simp only [List.mem_cons] at hw'
      rcases hw' with rfl | hw'
      · rw [he, Nat.beq_refl] at c1; simp at c1
      · exact hw'
    · simp only [Bool.cond_true]; omega
lemma rIdxAux_mem (P : List ℕ) (m s : ℕ) : ∀ {k : ℕ}, rIdxAux P m s k ≠ 0 → ∃ w ∈ P, w &&& m = s := by
  induction P with
  | nil => intro k h; simp [rIdxAux] at h
  | cons w ws ih =>
    intro k h
    unfold rIdxAux at h
    cases c1 : Nat.beq (w &&& m) s <;> simp only [c1, Bool.cond_true, Bool.cond_false] at h
    · obtain ⟨w', hw', he⟩ := ih h; exact ⟨w', by simp [hw'], he⟩
    · exact ⟨w, by simp, Nat.eq_of_beq_eq_true c1⟩
lemma rIdx_le (m s : ℕ) : rIdx m s ≤ 6 := by
  rcases rIdxAux_bound I.rawP m s 1 with h | ⟨_, h⟩
  · change rIdx m s = 0 at h; omega
  · have hlen := IOk.rawP_len; change rIdx m s < 1 + I.rawP.length at h; omega
lemma rIdx_inj (m x y : ℕ) (hx : rIdx m x ≠ 0) (he : rIdx m x = rIdx m y) : x = y :=
  rIdxAux_inj I.rawP m (by omega) hx he
lemma rIdx_iff (m s : ℕ) : rIdx m s ≠ 0 ↔ ∃ w ∈ I.rawP, w &&& m = s :=
  ⟨rIdxAux_mem I.rawP m s, rIdxAux_pos I.rawP m s (by omega)⟩
lemma Live.W {R : ℕ → ℕ} {m T k t : ℕ} {S : Finset ℕ} {Q : Set ℕ} (hl : Live (AR R) m T k t S) (hQ : (S : Set ℕ) ⊆ Q) : Sol A0 m T k Q := hl.sol.mono le_rfl hQ
lemma Live.to0 {R : ℕ → ℕ} {lb m T k t : ℕ} {S : Finset ℕ} (hl : Live (AL R lb) m T k t S) : Live A0 m T k t S :=
  hl.rel fun _ _ _ _ => trivial
lemma front_ord {R : ℕ → ℕ} (hRle : ∀ x, R x ≤ 6) (hRinj : ∀ x y, R x ≠ 0 → R x = R y → x = y)
    {m T lb k t : ℕ} {S : Finset ℕ} (hl : Live (AL R lb) m T k t S)
    (hm : ∀ q < k, ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) :
    Live (AR R) m T k t S ∨
    ∃ k0 d a b S1, k = k0 + 1 ∧ R a ≠ 0 ∧ R b ≠ 0 ∧ lb ≤ gkey (R a) (R b) d ∧ Bi A0 d a b S S1 ∧
      Live (AL R (gkey (R a) (R b) d + 1)) m T k0 t S1 := by
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
    have hm' : ∀ q < k, ¬ Sol A0 m T q (C m (Q ∪ ((insert (a ^^^ m) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.un (a := a) (Or.inl (Or.inr (by simp))) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, hlb, ⟨hxy, V, e1, rfl, hal⟩, hl1⟩
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
      refine Or.inr ⟨k0 + 1, d, x, y, insert a (insert (op d x y) (V.erase (a ^^^ m))), rfl, hx, hy, hlb,
        ⟨hxy, insert a (V.erase (a ^^^ m)), ?_, ?_, hal⟩, ?_⟩
      · rw [eU]; ext z; simp only [Finset.mem_insert]; tauto
      · ext z; simp only [Finset.mem_insert]; tauto
      · refine .un ?_
        have : insert (a ^^^ m) (insert (op d x y) (V.erase (a ^^^ m))) = insert (op d x y) V := by
          rw [Finset.insert_comm, Finset.insert_erase hmV]
        rw [this]; exact hl1
  | @bi k t d0 a b U hab hal0 hl ih =>
    set Q : Set ℕ := {x | R x ≠ 0} with hQ
    have hfr : op d0 a b ∉ C m (Q ∪ ((insert a (insert b U) : Finset ℕ) : Set ℕ)) := by
      intro hg
      apply hm k (by omega)
      refine hl.sol.mono le_rfl fun x hx => ?_
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
      rcases hx with rfl | hx
      · exact hg
      · exact Or.inl (Or.inr (by simp [hx]))
    have hfU : op d0 a b ∉ U := fun h => hfr (Or.inl (Or.inr (by simp [h])))
    have hfR : R (op d0 a b) = 0 := by
      by_contra h; exact hfr (Or.inl (Or.inl h))
    have hm' : ∀ q < k, ¬ Sol A0 m T q (C m (Q ∪ ((insert (op d0 a b) U : Finset ℕ) : Set ℕ))) := by
      intro q hq hs
      refine hm (q + 1) (by omega) (.bi (d := d0) (a := a) (b := b) (Or.inl (Or.inr (by simp))) (Or.inl (Or.inr (by simp))) (a0_all _ _ _) (hs.mono le_rfl ?_))
      rintro x ((hx | hx) | hx)
      · exact Or.inr (Or.inl (Or.inl hx))
      · simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hx
        rcases hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr (by simp [hx])))
      · exact Or.inr (Or.inr hx)
    rcases ih hm' with h | ⟨k0, d, x, y, S1, rfl, hx, hy, hlb_xy, ⟨hxy, V, e1, rfl, _⟩, hl1⟩
    · by_cases hW : R a ≠ 0 ∧ R b ≠ 0
      · have hlb0 : lb ≤ gkey (R a) (R b) d0 := by
          rcases hal0 with h' | h' | h'
          · exact absurd h' hW.1
          · exact absurd h' hW.2
          · exact h'
        refine Or.inr ⟨k, d0, a, b, _, rfl, hW.1, hW.2, hlb0, ⟨hab, U, rfl, rfl, trivial⟩, ?_⟩
        exact h.rel fun _ _ _ h' => h'.imp id Or.inl
      · have har : AR R d0 a b := by
          by_contra hc; simp only [AR, not_or] at hc; exact hW hc
        exact Or.inl (.bi hab har h)
    · have swap_xy : ∀ (hal_next : AL R (gkey (R x) (R y) d + 1) d0 a b),
          ∃ k1 d1 a1 b1 S1', k0 + 1 + 1 = k1 + 1 ∧ R a1 ≠ 0 ∧ R b1 ≠ 0 ∧ lb ≤ gkey (R a1) (R b1) d1 ∧ Bi A0 d1 a1 b1 (insert a (insert b U)) S1' ∧
            Live (AL R (gkey (R a1) (R b1) d1 + 1)) m T k1 t S1' := by
        intro hal_next
        set o := op d0 a b with ho
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
        refine ⟨k0 + 1, d, x, y, insert a (insert b (insert (op d x y) (V.erase o))), rfl, hx, hy, hlb_xy,
          ⟨hxy, insert a (insert b (V.erase o)), ?_, ?_, trivial⟩, ?_⟩
        · rw [eU]; ext z; simp only [Finset.mem_insert]
          constructor <;> (rintro (h | h | h | h | h) <;> simp only [h, true_or, or_true])
        · ext z; simp only [Finset.mem_insert]
          constructor <;> (rintro (h | h | h | h) <;> simp only [h, true_or, or_true])
        · refine .bi hab hal_next ?_
          have : insert (op d0 a b) (insert (op d x y) (V.erase o)) = insert (op d x y) V := by
            rw [Finset.insert_comm, ← ho, Finset.insert_erase hmV]
          rw [this]; exact hl1
      by_cases hW : R a ≠ 0 ∧ R b ≠ 0
      · have hlb0 : lb ≤ gkey (R a) (R b) d0 := by
          rcases hal0 with h' | h' | h'
          · exact absurd h' hW.1
          · exact absurd h' hW.2
          · exact h'
        rcases Nat.lt_trichotomy (gkey (R a) (R b) d0) (gkey (R x) (R y) d) with hlt | heq | hgt
        · refine Or.inr ⟨k0 + 1, d0, a, b, _, rfl, hW.1, hW.2, hlb0, ⟨hab, U, rfl, rfl, trivial⟩, ?_⟩
          rw [e1]
          refine .bi hxy (Or.inr (Or.inr (Nat.succ_le_of_lt hlt))) ?_
          exact hl1.rel fun _ _ _ h' => h'.imp id (Or.imp id fun h' => by omega)
        · exfalso
          obtain ⟨rfl, ⟨e1', e2'⟩ | ⟨e1', e2'⟩⟩ := gkey_inj (hRle a) (hRle b) (hRle x) (hRle y) heq
          · have e1a : a = x := hRinj a x hW.1 e1'
            have e2b : b = y := hRinj b y hW.2 e2'
            subst e1a e2b
            refine hm' k0 (by omega) (hl1.sol.mono le_rfl fun z hz => ?_)
            simp only [Finset.coe_insert, Set.mem_insert_iff] at hz
            rcases hz with rfl | hz
            · exact Or.inl (Or.inr (by simp))
            · have : z ∈ insert a (insert b V) := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
              rw [← e1] at this; exact Or.inl (Or.inr this)
          · have e1a : a = y := hRinj a y hW.1 e1'
            have e2b : b = x := hRinj b x hW.2 e2'
            subst e1a e2b
            rw [op_comm d0 b a] at hl1
            refine hm' k0 (by omega) (hl1.sol.mono le_rfl fun z hz => ?_)
            simp only [Finset.coe_insert, Set.mem_insert_iff] at hz
            rcases hz with rfl | hz
            · exact Or.inl (Or.inr (by simp))
            · have : z ∈ insert b (insert a V) := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz)
              rw [← e1] at this; exact Or.inl (Or.inr this)
        · exact Or.inr (swap_xy (Or.inr (Or.inr hgt)))
      · have har : AR R d0 a b := by
          by_contra hc; simp only [AR, not_or] at hc; exact hW hc
        exact Or.inr (swap_xy (har.imp id Or.inl))
lemma Min.Z {A : Bool → ℕ → ℕ → Prop} {m T k t : ℕ} {S : Finset ℕ} (h : Min A m T k t S) : Min A0 m T k t S :=
  ⟨h.1.rel fun _ _ _ _ => trivial, h.2⟩
lemma NK.toR {A : Bool → ℕ → ℕ → Prop} {m T k t : ℕ} {S : Finset ℕ} (h : NK A0 m T k t S) : NK A m T k t S :=
  ⟨fun d a b S1 k0 e hb hl => h.1 d a b S1 k0 e (hb.rel fun _ _ _ _ => trivial) (hl.rel fun _ _ _ _ => trivial),
    fun a S1 k0 t0 e e' hu hl => h.2 a S1 k0 t0 e e' hu (hl.rel fun _ _ _ _ => trivial)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma one_sound {R : ℕ → ℕ} (hRle : ∀ x, R x ≤ 6) (hRinj : ∀ x y, R x ≠ 0 → R x = R y → x = y)
    {K lb : ℕ} {f : ℕ → ℕ → ℕ → ℕ → List W → Bool}
    (hF : ∀ (k t lb' z : ℕ) (v : List W) (S : Finset ℕ), f k t lb' z v = false → StOk P T l m k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live (AL R lb') m T k' t S → (∀ q < k', ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l m k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s) (hlen : 2 ≤ v.length)
    {k' : ℕ} (hk : k' ≤ k) (hl : Live (AL R lb) m T k' t S) (hmW : ∀ q < k', ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hy : y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK A0 m T k' t S))
    (h2 : mv (look l m g K) l m g k t z v y = false)
    (h1 : ∀ a ∈ v, ∀ c ∈ v, a.s ≠ c.s → a.r ≠ 0 → c.r ≠ 0 →
      ∃ (hf : W → W → Bool → Bool → Bool → Bool) (go : (XW → XW → Bool) → List XW → Bool),
        (∀ d' ka kc, hf a c d' ka kc = true ∧ hf c a d' kc ka = true) ∧
        nodeOH lb hf (f (k - 1) t) (pos' t) l m g (k - t - y) v.length z v go = false ∧
        ∀ h, go h (v.map (mkx (pos' t) l (wst (pos' t) l v))) = false →
          h (mkx (pos' t) l (wst (pos' t) l v) a) (mkx (pos' t) l (wst (pos' t) l v) c) = false ∨
          h (mkx (pos' t) l (wst (pos' t) l v) c) (mkx (pos' t) l (wst (pos' t) l v) a) = false) : False := by
  have hmin : Min A0 m T k' t S := ⟨hl.to0, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
  have hcard := hs.rep.card
  rcases front_ord hRle hRinj hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hlb, hb, hl1⟩
  · exact mv_sound X (look_sound X K) hs (fun w hw => Or.inr (hcod w hw)) hlen h2 k' hk ⟨hlR, hmin.2⟩ (hy.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, ewa⟩ := hs.rep.mem.1 hb.sub.1
    obtain ⟨wb, hwb, ewb⟩ := hs.rep.mem.1 hb.sub.2.1
    obtain ⟨hf, go, hkf, hg1, hg2⟩ := h1 wa hwa wb hwb (by rw [ewa, ewb]; exact hb.1) (by rw [hcod wa hwa, ewa]; exact ha) (by rw [hcod wb hwb, ewb]; exact hb')
    obtain ⟨a', c', ha', hc', ea', ec', z', r, hfn, hst, hmem⟩ := nodeOH_bi X a0_symm hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1.to0 hy) hb hl1.to0
      (fun w1 w2 hw1 hw2 ew1 ew2 => by
        obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
        obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
        rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact hlb)
      (fun w1 w2 hw1 hw2 ew1 ew2 => by
        obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
        obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
        exact (hkf d _ _).1)
      (fun w1 w2 hw1 hw2 ew1 ew2 => by
        obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
        obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
        exact (hkf d _ _).2)
      (fun h xs hp a' c' ha' hc' e1 e2 hxs => by
        subst hxs
        obtain rfl := hs.rep.inj ha' hwa (e1.trans ewa.symm)
        obtain rfl := hs.rep.inj hc' hwb (e2.trans ewb.symm)
        exact hg2 h hp) hg1
    have hwa' : wa = a' := hs.rep.inj hwa ha' (ewa.trans ea'.symm)
    have hwb' : wb = c' := hs.rep.inj hwb hc' (ewb.trans ec'.symm)
    rw [← hwa', ← hwb', hcod wa hwa, hcod wb hwb, ewa, ewb] at hfn
    have hfr : R (op d a b) = 0 := by
      by_contra hne
      refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
      have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl (Or.inl hne)
      · exact Or.inl (Or.inr hx')
    refine hF _ _ _ _ _ S1 hfn hst ?_ k0 (by simpa using hk) hl1 ?_
    · intro w hw
      rcases hmem w hw with ⟨e1, e2⟩ | h
      · rw [e1, e2, hfr]
      · exact hcod w h
    · intro q hq hs'
      refine hmW (q + 1) (by omega) (.bi (d := d) (a := a) (b := b) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (a0_all _ _ _) (hs'.mono le_rfl ?_))
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
theorem look1_sound {R : ℕ → ℕ} (hRle : ∀ x, R x ≤ 6) (hRinj : ∀ x y, R x ≠ 0 → R x = R y → x = y) {K : ℕ} :
    ∀ (fuel k t lb z : ℕ) (v : List W) (S : Finset ℕ),
    look1 l m g K fuel k t lb z v = false → StOk P T l m k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live (AL R lb) m T k' t S → (∀ q < k', ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro fuel
  induction fuel with
  | zero => intro k t lb z v S h; simp [look1, look1C] at h
  | succ fuel ih =>
    intro k t lb z v S h hs hcod k' hk hl hmW
    change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y => Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g k t z v y) true
        (nodeOH lb (fun _ _ _ _ _ => true) (look1 l m g K fuel (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))) true (Nat.ble v.length 1) : Bool) = false at h
    rw [bR, pos_eq] at h
    cases h0 : Nat.ble v.length 1 with
    | true => rw [h0] at h; simp at h
    | false =>
      rw [h0, cond_false] at h
      have hlen : 2 ≤ v.length := by
        by_contra hc
        rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
      have hmin : Min A0 m T k' t S := ⟨hl.to0, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
      obtain ⟨y, hFy, hyk⟩ := tst_sound X a0_symm hs hmin hk
      have hy := (hFy _).symm.trans h
      beta_reduce at hy
      obtain ⟨hy1, hy2⟩ := or_false' X hy
      refine one_sound X hRle hRinj ih hs hcod hlen hk hl hmW hyk hy2 fun a ha c hc hne har hcr =>
        ⟨fun _ _ _ _ _ => true, pairsS, fun _ _ _ => ⟨rfl, rfl⟩, hy1, fun h hp => ?_⟩
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
  let x1 := bif Nat.testBit Z i then Nat.lor x (Nat.land (Nat.lor (I.rawP.getD i 0) (Nat.shiftRight (I.rawP.getD i 0) I.NN)) FULL) else x
  bif Nat.testBit Z (i + 6) then Nat.lor x1 (Nat.xor (Nat.land (I.rawP.getD i 0) (Nat.lor (Nat.shiftRight (I.rawP.getD i 0) I.NN) FPM)) FULL) else x1) 0
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
def mkW (P : List ℕ) (m s : ℕ) : W := ⟨s, pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0)), pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n)),
  Nat.lor (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) 0))) (pL (P.map fun n => bit01 (Nat.beq (Nat.land s n) n))), rIdx m s⟩
lemma mkW_ok (P : List ℕ) (m s : ℕ) : WOk P (mkW P m s) := by
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
  (fun w _ ih => Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P m (Nat.land w m)) ih) ih (Nat.beq (Nat.land w m) m)) ih (Nat.beq (Nat.land w m) 0)) L
def frc (v : List W) : (List W → Bool) → Bool := List.rec (motive := fun _ => (List W → Bool) → Bool) (fun h => h [])
  (fun w _ ih h => st w.s fun s => st w.a fun a => st w.b fun b => st w.c fun c => ih fun r => h (⟨s, a, b, c, w.r⟩ :: r)) v
def anySubC (NN : ℕ) (d : Bool) (l : ℕ) (v : List W) : ℕ → (List W → Bool) → Bool := List.rec (motive := fun _ => ℕ → (List W → Bool) → Bool) (fun _ h => h [])
  (fun w t ih c h => Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (ih c h) (Nat.beq (Nat.lor c (covC NN d l t)) l)) true
    (st (Nat.lor c (spC NN d l w.s)) fun c => ih c fun r => h (w :: r))) v
abbrev anySub := anySubC I.NN
def sumc (v : List W) : ℕ := List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.add w.c ih) v
def mvHGC (NN AA HX HY : Nat) (F1 F2 : Nat → Nat → Nat → List W → Bool) (H1 H2 : Nat) (f1 f2 : Bool)
    (l m g k t z : Nat) (v : List W) (y : Nat) : Bool :=
  (fun n => Bool.rec (motive := fun _ => Bool)
    (prd t (fun s =>
      let cont := fun a0 q z v => cvC NN (pos s) l v (tstC NN AA HX HY (pos s) l (Nat.sub k s) v (fun y =>
        Bool.rec (motive := fun _ => Bool)
          (prd s (fun s2 =>
            let cont2 := fun _ q' z v => cvC NN (pos s2) l v (tstC NN AA HX HY (pos s2) l (Nat.sub (Nat.sub k 1) s2) v (fun y =>
              nodeQC NN (F2 (Nat.sub k 3) s2) (pos s2) l m g (Nat.sub (Nat.sub (Nat.sub k 2) s2) y) v.length z v (pairsQ q q')))
            bif f2 then notsC H2 cont2 m g (Nat.sub (Nat.sub (Nat.sub k 1) s2) y) v.length z (pos s2) (Nat.succ q) a0 v v
            else nots cont2 m g (Nat.sub (Nat.sub (Nat.sub k 1) s2) y) v.length z (pos s2) (Nat.succ q) a0 v v))
          true
          (bif f2 then nodeOHC NN 0 (fun _ c d ka kc => hb H2 (hashP c.s d ka kc)) (fun _ => F2 (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q)
           else nodeC NN (F2 (Nat.sub k 2) s) (pos s) l m g (Nat.sub (Nat.sub (Nat.sub k 1) s) y) v.length z v (pairsP q))))
      bif f1 then notsC H1 cont m g (Nat.sub (Nat.sub k s) y) n z (pos s) 0 0 v v
      else nots cont m g (Nat.sub (Nat.sub k s) y) n z (pos s) 0 0 v v))
    true
    (bif f1 then nodeOHC NN 0 (fun a c d ka kc => hb H1 (hashBin a.s c.s d ka kc)) (fun _ => F1 (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN
     else nodeC NN (F1 (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) n z v pairsN)) v.length
def look1MC (NN AA HX HY l m g K H k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    mvHGC NN AA HX HY (lookC NN AA HX HY l m g K) (lookC NN AA HX HY l m g K) H 0 true false l m g k t z v y)) true (Nat.ble v.length 1)
def lookMC (NN AA HX HY l m g K Ha Hb k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    mvHGC NN AA HX HY (look1MC NN AA HX HY l m g K Hb) (lookC NN AA HX HY l m g K) Ha Hb true true l m g k t z v y)) true (Nat.ble v.length 1)
def top1CC (NN AA HX HY l m g K H3 k t lb z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (mvHGC NN AA HX HY (lookC NN AA HX HY l m g K) (lookC NN AA HX HY l m g K) H3 0 true false l m g k t z v y)
      true
      (nodeOHC NN lb (fun a c d ka kc => hb H3 (hashFS a.r c.r d ka kc))
        (look1C NN AA HX HY l m g K K (Nat.sub k 1) t)
        (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))) true (Nat.ble v.length 1)
def top1bCC (NN AA HX HY l m g K H2 H3 k t lb z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    nodeOHC NN lb (fun a c d ka kc => hb H2 (hashFS a.r c.r d ka kc))
      (top1CC NN AA HX HY l m g K H3 (Nat.sub k 1) t)
      (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS)) true (Nat.ble v.length 1)
def top2CC (NN AA HX HY l m g K H1 H2 H3 ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tstC NN AA HX HY (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (mvHGC NN AA HX HY (lookMC NN AA HX HY l m g K H2 H3) (look1MC NN AA HX HY l m g K H3) H1 H2 true true l m g k t z v y)
          (nodeOHC NN 0 (fun a c d ka kc => hb H1 (hashFS a.r c.r d ka kc))
            (fun _ => lookMC NN AA HX HY l m g K H2 H3 (Nat.sub k 1) t)
            (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS)
          (Nat.beq ph 3))
        (nodeOHC NN 0 (fun a c d ka kc => hb H1 (hashFS a.r c.r d ka kc))
          (top1bCC NN AA HX HY l m g K H2 H3 (Nat.sub k 1) t)
          (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS)
        (Nat.beq ph 0))
      (Bool.rec (motive := fun _ => Bool)
        (mvC NN AA HX HY (lookC NN AA HX HY l m g K) l m g k t z v y)
        true
        (nodeOHC NN 0 (fun a c d ka kc => hb H1 (hashFS a.r c.r d ka kc))
          (look1C NN AA HX HY l m g K K (Nat.sub k 1) t)
          (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v pairsS))
      (Nat.beq ph 2))) true (Nat.ble v.length 1)
abbrev mvHG := mvHGC I.NN I.AA I.HX I.HY
abbrev look1M := look1MC I.NN I.AA I.HX I.HY
abbrev lookM := lookMC I.NN I.AA I.HX I.HY
abbrev top1C := top1CC I.NN I.AA I.HX I.HY
abbrev top1bC := top1bCC I.NN I.AA I.HX I.HY
abbrev top2C := top2CC I.NN I.AA I.HX I.HY
def startvC (NN AA HX HY l m g B K t H1 H2 H3 ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => top2CC NN AA HX HY l m g K H1 H2 H3 ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))
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
lemma avl_spec (P : List ℕ) (m : ℕ) (L : List ℕ) : Srt (avl P m L) ∧ (∀ w ∈ avl P m L, ∃ x ∈ L, w = mkW P m (x &&& m)) ∧
    ∀ x ∈ L, x &&& m ≠ 0 → x &&& m ≠ m → ∃ w ∈ avl P m L, w.s = x &&& m := by
  induction L with
  | nil => exact ⟨List.Pairwise.nil, by simp [avl], by simp⟩
  | cons y L ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    have e : avl P m (y :: L) = bif Nat.beq (Nat.land y m) 0 then avl P m L else bif Nat.beq (Nat.land y m) m then avl P m L else addS (mkW P m (Nat.land y m)) (avl P m L) := by
      change Bool.rec (motive := fun _ => List W) (Bool.rec (motive := fun _ => List W) (addS (mkW P m (Nat.land y m)) (avl P m L)) (avl P m L) (Nat.beq (Nat.land y m) m)) (avl P m L) (Nat.beq (Nat.land y m) 0) = _
      cases Nat.beq (Nat.land y m) 0 <;> cases Nat.beq (Nat.land y m) m <;> rfl
    have old : ∀ w ∈ avl P m L, ∃ x ∈ y :: L, w = mkW P m (x &&& m) := fun w hw => by
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
        obtain ⟨j1, j2, j3, j4⟩ := addS_spec (o := mkW P m (Nat.land y m)) i1
        refine ⟨j1, fun w hw => ?_, fun x hx h2 h3 => ?_⟩
        · rcases j2 w hw with rfl | h
          · exact ⟨y, by simp, rfl⟩
          · exact old w h
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact j3
          · obtain ⟨w, hw, e⟩ := i3 x hx h2 h3; exact ⟨w, j4 w hw, e⟩
lemma hashFS_symm {ra rb : ℕ} {op ka kc : Bool} (hne : ra ≠ rb) :
    hashFS ra rb op ka kc = hashFS rb ra op kc ka := by
  unfold hashFS
  by_cases h : ra ≤ rb
  · have hlt : ra < rb := Nat.lt_of_le_of_ne h hne
    have b1 : Nat.ble ra rb = true := Nat.ble_eq_true_of_le h
    have b2 : Nat.ble rb ra = false := Bool.eq_false_iff.2 fun e => Nat.not_lt.2 (Nat.le_of_ble_eq_true e) hlt
    simp [b1, b2]
  · have hlt : rb < ra := Nat.lt_of_not_ge h
    have b1 : Nat.ble ra rb = false := Bool.eq_false_iff.2 fun e => h (Nat.le_of_ble_eq_true e)
    have b2 : Nat.ble rb ra = true := Nat.ble_eq_true_of_le (le_of_lt hlt)
    simp [b1, b2]
lemma hashBin_symm {sa sc : ℕ} {op ka kc : Bool} (hne : sa ≠ sc) :
    hashBin sa sc op ka kc = hashBin sc sa op kc ka := by
  unfold hashBin
  by_cases h : sa ≤ sc
  · have hlt : sa < sc := Nat.lt_of_le_of_ne h hne
    have b1 : Nat.ble sa sc = true := Nat.ble_eq_true_of_le h
    have b2 : Nat.ble sc sa = false := Bool.eq_false_iff.2 fun e => Nat.not_lt.2 (Nat.le_of_ble_eq_true e) hlt
    simp [b1, b2, Nat.add_comm]
  · have hlt : sc < sa := Nat.lt_of_not_ge h
    have b1 : Nat.ble sa sc = false := Bool.eq_false_iff.2 fun e => h (Nat.le_of_ble_eq_true e)
    have b2 : Nat.ble sc sa = true := Nat.ble_eq_true_of_le (le_of_lt hlt)
    simp [b1, b2, Nat.add_comm]
lemma hashFS_lt (ra rb : ℕ) (op ka kc : Bool) : hashFS ra rb op ka kc < MM := Nat.mod_lt _ (by decide)
lemma hashBin_lt (sa sc : ℕ) (op ka kc : Bool) : hashBin sa sc op ka kc < MM := Nat.mod_lt _ (by decide)
lemma hashP_lt (sc : ℕ) (op ka kc : Bool) : hashP sc op ka kc < MM := Nat.mod_lt _ (by decide)
lemma hashNot_lt (sa : ℕ) (ka : Bool) : hashNot sa ka < MM := Nat.mod_lt _ (by decide)
def FF : ℕ := 2 ^ MM - 1
def mask1 (M : List (ℕ × ℕ × ℕ × ℕ)) (ph : ℕ) : ℕ :=
  M.foldl (fun acc p => bif (Nat.beq p.2.2.2 2 || Nat.beq p.2.2.2 ph) && Nat.beq p.2.1 FF && Nat.beq p.2.2.1 FF then Nat.lor acc p.1 else acc) 0
def mask2 (M : List (ℕ × ℕ × ℕ × ℕ)) (ph r1 : ℕ) : ℕ :=
  M.foldl (fun acc p => bif (Nat.beq p.2.2.2 2 || Nat.beq p.2.2.2 ph) && hb p.1 r1 && Nat.beq p.2.2.1 FF then Nat.lor acc p.2.1 else acc) 0
def mask3 (M : List (ℕ × ℕ × ℕ × ℕ)) (ph r1 r2 : ℕ) : ℕ :=
  M.foldl (fun acc p => bif (Nat.beq p.2.2.2 2 || Nat.beq p.2.2.2 ph) && hb p.1 r1 && hb p.2.1 r2 then Nat.lor acc p.2.2.1 else acc) 0
def phOk (M : List (ℕ × ℕ × ℕ × ℕ)) (ph : ℕ) : Bool :=
  let m1 := mask1 M ph
  Nat.beq m1 FF || (List.range MM).all (fun r1 => m1.testBit r1 ||
    (let m2 := mask2 M ph r1
     Nat.beq m2 FF || (List.range MM).all (fun r2 => m2.testBit r2 || Nat.beq (mask3 M ph r1 r2) FF)))
def mFull3 (M : List (ℕ × ℕ × ℕ × ℕ)) : Bool :=
  M.any (fun p => Nat.beq p.2.2.2 2 && Nat.beq p.1 FF && Nat.beq p.2.1 FF && Nat.beq p.2.2.1 FF) ||
  (phOk M 0 && phOk M 3 && phOk M 1)
lemma hb_mod (H x : ℕ) : hb H x = hb H (x % MM) := by
  unfold hb
  change Nat.beq ((H >>> (x % MM)) &&& 1) 1 = Nat.beq ((H >>> (x % MM % MM)) &&& 1) 1
  rw [Nat.mod_mod]
lemma hb_testBit (H r : ℕ) (hr : r < MM) : hb H r = H.testBit r := by
  unfold hb
  change Nat.beq ((H >>> (r % MM)) &&& 1) 1 = H.testBit r
  rw [Nat.mod_eq_of_lt hr]
  have h1 : ((H >>> r) &&& 1) = (H.testBit r).toNat := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and, Nat.testBit_shiftRight]
    cases i with
    | zero => cases H.testBit r <;> simp
    | succ i =>
      have : (1 : ℕ).testBit (i + 1) = false := Nat.testBit_lt_two_pow (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ i + 1); omega)
      rw [this, Bool.and_false]
      cases H.testBit r <;> simp [this]
  rw [h1]; cases H.testBit r <;> rfl
lemma hb_FF {r : ℕ} (hr : r < MM) : hb FF r = true := by
  rw [hb_testBit _ _ hr, FF, Nat.testBit_two_pow_sub_one]; simp [hr]
lemma foldl_or_bit {α : Type} (L : List α) (cond : α → Bool) (val : α → ℕ) (r : ℕ) (hr : r < MM) :
    ∀ acc : ℕ, (L.foldl (fun acc p => bif cond p then Nat.lor acc (val p) else acc) acc).testBit r = true →
    acc.testBit r = true ∨ ∃ p ∈ L, cond p = true ∧ hb (val p) r = true := by
  induction L with
  | nil => intro acc h; exact Or.inl h
  | cons p L ih =>
    intro acc h
    simp only [List.foldl_cons] at h
    rcases ih _ h with h1 | ⟨q, hq, h2⟩
    · cases hc : cond p
      · rw [hc, Bool.cond_false] at h1; exact Or.inl h1
      · rw [hc, Bool.cond_true] at h1
        change (acc ||| val p).testBit r = true at h1
        rw [Nat.testBit_or, Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr ⟨p, by simp, hc, by rw [hb_testBit _ _ hr]; exact h1⟩
    · exact Or.inr ⟨q, by simp [hq], h2⟩
lemma mFull3_cov {M : List (ℕ × ℕ × ℕ × ℕ)} (hM : mFull3 M = true) {ph r1 r2 r3 : ℕ} (hph : ph = 0 ∨ ph = 3 ∨ ph = 1)
    (h1 : r1 < MM) (h2 : r2 < MM) (h3 : r3 < MM) :
    ∃ p ∈ M, (p.2.2.2 = 2 ∨ p.2.2.2 = ph) ∧ hb p.1 r1 = true ∧ hb p.2.1 r2 = true ∧ hb p.2.2.1 r3 = true := by
  simp only [mFull3, Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq] at hM
  rcases hM with ⟨p, hp, ⟨⟨⟨hp4, hp1⟩, hp2⟩, hp3⟩⟩ | ⟨⟨h0, h3'⟩, h1'⟩
  · refine ⟨p, hp, Or.inl hp4, ?_, ?_, ?_⟩ <;> simp [hp1, hp2, hp3, hb_FF h1, hb_FF h2, hb_FF h3]
  · have hok : phOk M ph = true := by rcases hph with rfl | rfl | rfl; exacts [h0, h3', h1']
    simp only [phOk, Bool.or_eq_true, Nat.beq_eq, List.all_eq_true, List.mem_range] at hok
    have from_m1 : (mask1 M ph).testBit r1 = true →
        ∃ p ∈ M, (p.2.2.2 = 2 ∨ p.2.2.2 = ph) ∧ hb p.1 r1 = true ∧ hb p.2.1 r2 = true ∧ hb p.2.2.1 r3 = true := by
      intro hb1
      rcases foldl_or_bit M (fun p => (Nat.beq p.2.2.2 2 || Nat.beq p.2.2.2 ph) && Nat.beq p.2.1 FF && Nat.beq p.2.2.1 FF) Prod.fst r1 h1 0 hb1 with hf | ⟨p, hp, hc, hr1⟩
      · simp at hf
      · simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hc
        exact ⟨p, hp, hc.1.1, hr1, by rw [hc.1.2]; exact hb_FF h2, by rw [hc.2]; exact hb_FF h3⟩
    have from_m2 : (mask2 M ph r1).testBit r2 = true →
        ∃ p ∈ M, (p.2.2.2 = 2 ∨ p.2.2.2 = ph) ∧ hb p.1 r1 = true ∧ hb p.2.1 r2 = true ∧ hb p.2.2.1 r3 = true := by
      intro hb2
      rcases foldl_or_bit M (fun p => (Nat.beq p.2.2.2 2 || Nat.beq p.2.2.2 ph) && hb p.1 r1 && Nat.beq p.2.2.1 FF) (fun p => p.2.1) r2 h2 0 hb2 with hf | ⟨p, hp, hc, hr2⟩
      · simp at hf
      · simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hc
        exact ⟨p, hp, hc.1.1, hc.1.2, hr2, by rw [hc.2]; exact hb_FF h3⟩
    have from_m3 : mask3 M ph r1 r2 = FF →
        ∃ p ∈ M, (p.2.2.2 = 2 ∨ p.2.2.2 = ph) ∧ hb p.1 r1 = true ∧ hb p.2.1 r2 = true ∧ hb p.2.2.1 r3 = true := by
      intro hm3
      have hb3 : (mask3 M ph r1 r2).testBit r3 = true := by rw [hm3, FF, Nat.testBit_two_pow_sub_one]; simp [h3]
      rcases foldl_or_bit M (fun p => (Nat.beq p.2.2.2 2 || Nat.beq p.2.2.2 ph) && hb p.1 r1 && hb p.2.1 r2) (fun p => p.2.2.1) r3 h3 0 hb3 with hf | ⟨p, hp, hc, hr3⟩
      · simp at hf
      · simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hc
        exact ⟨p, hp, hc.1.1, hc.1.2, hc.2, hr3⟩
    rcases hok with hff1 | hall1
    · exact from_m1 (by rw [hff1, FF, Nat.testBit_two_pow_sub_one]; simp [h1])
    · rcases hall1 r1 h1 with hr1b | hall2
      · exact from_m1 hr1b
      · rcases hall2 with hff2 | hall2'
        · exact from_m2 (by rw [hff2, FF, Nat.testBit_two_pow_sub_one]; simp [h2])
        · rcases hall2' r2 h2 with hr2b | hm3
          · exact from_m2 hr2b
          · exact from_m3 hm3
lemma list_order {α : Type} {l : List α} {a c : α} (ha : a ∈ l) (hc : c ∈ l) (hne : a ≠ c) :
    (∀ R : α → α → Prop, l.Pairwise R → R a c) ∨ (∀ R : α → α → Prop, l.Pairwise R → R c a) := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    simp only [List.mem_cons] at ha hc
    rcases ha with rfl | ha <;> rcases hc with rfl | hc
    · exact absurd rfl hne
    · exact Or.inl fun R h => (List.pairwise_cons.1 h).1 c hc
    · exact Or.inr fun R h => (List.pairwise_cons.1 h).1 a ha
    · exact (ih ha hc).imp (fun h R hp => h R (List.pairwise_cons.1 hp).2) (fun h R hp => h R (List.pairwise_cons.1 hp).2)
lemma pairs_dir {xs : List XW} {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) :
    (∀ h : XW → XW → Bool, pairs h xs = false → h a c = false) ∨
    (∀ h : XW → XW → Bool, pairs h xs = false → h c a = false) :=
  (list_order ha hc hne).imp (fun ho h hp => ho _ (pairs_false hp)) (fun ho h hp => ho _ (pairs_false hp))
lemma pairsN_dir {xs : List XW} {a c : XW} (ha : a ∈ xs) (hc : c ∈ xs) (hne : a ≠ c) (hr : a.w.r = 0 ∨ c.w.r = 0) :
    (∀ h : XW → XW → Bool, pairsN h xs = false → h a c = false) ∨
    (∀ h : XW → XW → Bool, pairsN h xs = false → h c a = false) := by
  by_cases hra : a.w.r = 0
  · by_cases hrc : c.w.r = 0
    · refine (list_order (fr_mem ha hra) (fr_mem hc hrc) hne).imp (fun ho h hp => ?_) (fun ho h hp => ?_)
      · simp only [pairsN, bR] at hp
        cases h1 : pairs h (fr xs) <;> rw [h1] at hp <;> simp at hp
        exact ho _ (pairs_false h1)
      · simp only [pairsN, bR] at hp
        cases h1 : pairs h (fr xs) <;> rw [h1] at hp <;> simp at hp
        exact ho _ (pairs_false h1)
    · refine Or.inl fun h hp => ?_
      simp only [pairsN, bR] at hp
      cases h1 : pairs h (fr xs) <;> rw [h1] at hp <;> simp at hp
      exact scan_false (scan_false hp a (fr_mem ha hra)) c (fs_mem hc hrc)
  · have hrc := hr.resolve_left hra
    refine Or.inr fun h hp => ?_
    simp only [pairsN, bR] at hp
    cases h1 : pairs h (fr xs) <;> rw [h1] at hp <;> simp at hp
    exact scan_false (scan_false hp c (fr_mem hc hrc)) a (fs_mem ha hra)
lemma mvHGC_false (F1 F2 : ℕ → ℕ → ℕ → List W → Bool) (H1 H2 : ℕ) (f1 f2 : Bool)
    (l m g k t z : ℕ) (v : List W) (y : ℕ) (h : mvHGC I.NN I.AA I.HX I.HY F1 F2 H1 H2 f1 f2 l m g k t z v y = false) :
    (f1 = true → nodeOH 0 (fun a c d ka kc => hb H1 (hashBin a.s c.s d ka kc)) (fun _ => F1 (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false) ∧
    (f1 = false → node (F1 (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN = false) ∧
    ∀ s, t = s + 1 →
      (let cont := fun a0 q z v => cv (pos' s) l v (tst (pos' s) l (k - s) v (fun y =>
        Bool.rec (motive := fun _ => Bool)
          (prd s (fun s2 =>
            let cont2 := fun _ q' z v => cv (pos' s2) l v (tst (pos' s2) l (k - 1 - s2) v (fun y =>
              nodeQ (F2 (k - 3) s2) (pos' s2) l m g (k - 2 - s2 - y) v.length z v (pairsQ q q')))
            bif f2 then notsC H2 cont2 m g (k - 1 - s2 - y) v.length z (pos' s2) (q + 1) a0 v v
            else nots cont2 m g (k - 1 - s2 - y) v.length z (pos' s2) (q + 1) a0 v v))
          true
          (bif f2 then nodeOH 0 (fun _ c d ka kc => hb H2 (hashP c.s d ka kc)) (fun _ => F2 (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q)
           else node (F2 (k - 2) s) (pos' s) l m g (k - 1 - s - y) v.length z v (pairsP q))))
       (f1 = true → notsC H1 cont m g (k - s - y) v.length z (pos' s) 0 0 v v = false) ∧
       (f1 = false → nots cont m g (k - s - y) v.length z (pos' s) 0 0 v v = false)) := by
  change (Bool.rec (motive := fun _ => Bool)
    (prd t (fun s =>
      let cont := fun a0 q z v => cv (pos s) l v (tst (pos s) l (k - s) v (fun y =>
        Bool.rec (motive := fun _ => Bool)
          (prd s (fun s2 =>
            let cont2 := fun _ q' z v => cv (pos s2) l v (tst (pos s2) l (k - 1 - s2) v (fun y =>
              nodeQ (F2 (k - 3) s2) (pos s2) l m g (k - 2 - s2 - y) v.length z v (pairsQ q q')))
            bif f2 then notsC H2 cont2 m g (k - 1 - s2 - y) v.length z (pos s2) (q + 1) a0 v v
            else nots cont2 m g (k - 1 - s2 - y) v.length z (pos s2) (q + 1) a0 v v))
          true
          (bif f2 then nodeOH 0 (fun _ c d ka kc => hb H2 (hashP c.s d ka kc)) (fun _ => F2 (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q)
           else node (F2 (k - 2) s) (pos s) l m g (k - 1 - s - y) v.length z v (pairsP q))))
      bif f1 then notsC H1 cont m g (k - s - y) v.length z (pos s) 0 0 v v
      else nots cont m g (k - s - y) v.length z (pos s) 0 0 v v))
    true
    (bif f1 then nodeOH 0 (fun a c d ka kc => hb H1 (hashBin a.s c.s d ka kc)) (fun _ => F1 (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN
     else node (F1 (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsN) : Bool) = false at h
  rw [bR] at h
  simp only [pos_eq] at h
  cases hf1 : f1 <;> rw [hf1] at h <;> simp only [Bool.cond_false, Bool.cond_true] at h
  · cases h1 : node (F1 (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨fun e => absurd e (by simp), fun _ => rfl, ?_⟩
      rintro s rfl
      exact ⟨fun e => absurd e (by simp), fun _ => h⟩
  · cases h1 : nodeOH 0 (fun a c d ka kc => hb H1 (hashBin a.s c.s d ka kc)) (fun _ => F1 (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsN with
    | true => rw [h1] at h; simp at h
    | false =>
      rw [h1, Bool.cond_false] at h
      refine ⟨fun _ => rfl, fun e => absurd e (by simp), ?_⟩
      rintro s rfl
      exact ⟨fun _ => h, fun e => absurd e (by simp)⟩
section sound
variable {P : List ℕ} {l m g T : ℕ} (X : Ctx P l m g T)
include X
lemma mvHGC_sound_all {R : ℕ → ℕ} {α : Type} {H1 H2 : α → ℕ} {F1 F2 : α → ℕ → ℕ → ℕ → List W → Bool} {f1 f2 : Bool}
    (hF1 : ∀ (r1 : ℕ), r1 < MM → ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ),
      (∀ q : {q : α // f1 = true → hb (H1 q) r1 = true}, F1 q.1 k t z v = false) →
      StOk P T l m k t z v S → Cod R v → ∀ k' ≤ k, ¬ Min (AR R) m T k' t S)
    (hF2 : ∀ (r1 r2 : ℕ), r1 < MM → r2 < MM → ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ),
      (∀ q : {q : α // (f1 = true → hb (H1 q) r1 = true) ∧ (f2 = true → hb (H2 q) r2 = true)}, F2 q.1 k t z v = false) →
      StOk P T l m k t z v S → Cod R v → ∀ k' ≤ k, ¬ Min (AR R) m T k' t S)
    {k t z y : ℕ} {v : List W} {S : Finset ℕ} (hs : StOk P T l m k t z v S) (hcod : Cod R v) (hlen : 2 ≤ v.length)
    (h : ∀ q : α, mvHGC I.NN I.AA I.HX I.HY (F1 q) (F2 q) (H1 q) (H2 q) f1 f2 l m g k t z v y = false) :
    ∀ k' ≤ k, Min (AR R) m T k' t S → (y = 0 ∨ (y = 1 ∧ v.length + t = k ∧ NK (AR R) m T k' t S)) → False := by
  intro k' hk hm hy
  have hcard := hs.rep.card
  have codB : ∀ {v r : List W} {o : ℕ}, Cod R v → (∀ w ∈ r, (w.s = o ∧ w.r = 0) ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw; rcases hr w hw with ⟨_, h⟩ | h; exact Or.inl h; exact hv w h
  have codU : ∀ {v r : List W} {a : W}, Cod R v → (∀ w ∈ r, w = notW m a ∨ w ∈ v) → Cod R r := by
    intro v r o hv hr w hw; rcases hr w hw with h | h; exact Or.inl (by rw [h]; rfl); exact hv w h
  have h0 : ∀ q : α, _ := fun q => mvHGC_false (F1 q) (F2 q) (H1 q) (H2 q) f1 f2 l m g k t z v y (h q)
  rcases first_move (AR.symm R) k' t S hm (by omega) with
    ⟨k0, d, a, b, S1, rfl, hbi, hl⟩ | ⟨k0, t0, a, d, c, S1, S2, rfl, rfl, hu, hbi, hl⟩ |
    ⟨k0, t0, a, a', d, S1, S2, S3, rfl, rfl, ha'a, hu, hne, hu', hbi, hl⟩
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨wa, hwa, ewa⟩ := hs.rep.mem.1 hbi.sub.1
    obtain ⟨wc, hwc, ewc⟩ := hs.rep.mem.1 hbi.sub.2.1
    have hr0 : wa.r = 0 ∨ wc.r = 0 := by
      by_contra hc'
      push Not at hc'
      change wa.r ≠ 0 ∧ wc.r ≠ 0 at hc'
      obtain ⟨_, U, _, _, hal⟩ := id hbi
      have h1 : wa.r = R wa.s := (hcod wa hwa).resolve_left hc'.1
      have h2 : wc.r = R wc.s := (hcod wc hwc).resolve_left hc'.2
      rw [← ewa, ← ewc] at hal
      exact hal.elim (fun e => hc'.1 (by rw [h1, e])) (fun e => hc'.2 (by rw [h2, e]))
    have hdir : ∀ x y : W, x ∈ v → y ∈ v → x.s = a → y.s = b →
        (∀ h xs, pairsN h xs = false → xs = v.map (mkx (pos' t) l (wst (pos' t) l v)) →
          h (mkx (pos' t) l (wst (pos' t) l v) x) (mkx (pos' t) l (wst (pos' t) l v) y) = false) ∨
        (∀ h xs, pairsN h xs = false → xs = v.map (mkx (pos' t) l (wst (pos' t) l v)) →
          h (mkx (pos' t) l (wst (pos' t) l v) y) (mkx (pos' t) l (wst (pos' t) l v) x) = false) := by
      intro x y hx hy ex ey
      obtain rfl := hs.rep.inj hx hwa (ex.trans ewa.symm)
      obtain rfl := hs.rep.inj hy hwc (ey.trans ewc.symm)
      have hne_xw : mkx (pos' t) l (wst (pos' t) l v) x ≠ mkx (pos' t) l (wst (pos' t) l v) y := fun e =>
        hbi.1 (by rw [← ewa, ← ewc]; exact congrArg XW.s e)
      exact (pairsN_dir (List.mem_map_of_mem hx) (List.mem_map_of_mem hy) hne_xw hr0).imp
        (fun f h xs hp hxs => f h (hxs ▸ hp)) (fun f h xs hp hxs => f h (hxs ▸ hp))
    cases hf1 : f1
    · let β := {q : α // f1 = true → hb (H1 q) 0 = true}
      have hp' : ∀ q : β, node (F1 q.1 k t) (pos' t) l m g (k + 1 - t - y) v.length z v pairsN = false := fun q => by
        simpa using (h0 q.1).2.1 hf1
      obtain ⟨z', r, hf, hst, hmem⟩ := node_bi_all X (AR.symm R) (α := β) (f := fun q => F1 q.1 k t) hs hm (by omega) rfl rfl
        (NK.sizeB hcard hm hk hbi hl hy) hbi hl
        (fun x y hx hy ex ey => (hdir x y hx hy ex ey).imp
          (fun f q h xs hp hxs => f h xs hp hxs) (fun f q h xs hp hxs => f h xs hp hxs))
        hp'
      exact hF1 0 (by decide) k t z' r S1 hf hst (codB hcod hmem) k0 (by omega) (hbi.min hl hm.2)
    · let r1 := hashBin wa.s wc.s d (decide (wa.s ∈ S1)) (decide (wc.s ∈ S1))
      let β := {q : α // f1 = true → hb (H1 q) r1 = true}
      have hp' : ∀ q : β, nodeOH 0 (fun a c d ka kc => hb (H1 q.1) (hashBin a.s c.s d ka kc))
          (fun _ => F1 q.1 k t) (pos' t) l m g (k + 1 - t - y) v.length z v pairsN = false := fun q => by
        simpa using (h0 q.1).1 hf1
      obtain ⟨_, _, _, _, _, _, z', r, hf, hst, hmem⟩ := nodeOH_bi_all X (AR.symm R) (α := β)
        (hf := fun q a c d ka kc => hb (H1 q.1) (hashBin a.s c.s d ka kc))
        (f := fun q _ => F1 q.1 k t) hs hm (by omega) rfl rfl (NK.sizeB hcard hm hk hbi hl hy) hbi hl
        (fun _ _ _ _ _ _ => Nat.zero_le _)
        (fun q x y hx hy ex ey => by
          obtain rfl := hs.rep.inj hx hwa (ex.trans ewa.symm)
          obtain rfl := hs.rep.inj hy hwc (ey.trans ewc.symm)
          exact q.2 hf1)
        (fun q x y hx hy ex ey => by
          obtain rfl := hs.rep.inj hx hwa (ex.trans ewa.symm)
          obtain rfl := hs.rep.inj hy hwc (ey.trans ewc.symm)
          rw [hashBin_symm (fun e => hbi.1 (by rw [← ewa, ← ewc, e]))]
          exact q.2 hf1)
        (fun x y hx hy ex ey => (hdir x y hx hy ex ey).imp
          (fun f q h xs hp hxs => f h xs hp hxs) (fun f q h xs hp hxs => f h xs hp hxs))
        hp'
      exact hF1 r1 (hashBin_lt _ _ _ _ _) k t z' r S1 (fun q => hf q) hst (codB hcod hmem) k0 (by omega) (hbi.min hl hm.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
    have hl1 := hbi.live hl
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    let r1 := hashNot wa.s (decide (wa.s ∈ S1))
    let β1 := {q : α // f1 = true → hb (H1 q) r1 = true}
    have hm1 := hu.min hl1 hm.2
    have hmid : ∃ z1 r1' y1, StOk P T l m (k + 1) t0 z1 r1' S1 ∧ (∀ w ∈ r1', w = notW m wa ∨ w ∈ v) ∧
        (y1 = 0 ∨ (y1 = 1 ∧ r1'.length + t0 = k + 1 ∧ NK (AR R) m T (k0 + 1) t0 S1)) ∧
        ∀ q : β1, (bif f2 then nodeOH 0 (fun _ c d ka kc => hb (H2 q.1) (hashP c.s d ka kc)) (fun _ => F2 q.1 k t0)
            (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m))
            else node (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m))) = false := by
      by_cases hf1 : f1 = true
      · obtain ⟨z1, r1', hf1', hst1, hmem1⟩ := notsC_sound_all X hs hm (by omega) rfl rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) (Or.inl rfl) hwa
          (fun q : β1 => q.2 hf1) (fun q : β1 => (h0 q.1).2.2 t0 rfl |>.1 hf1)
        have hf1'' : ∀ q : β1, _ := fun q => cv_ok X hst1 hl1 (hf1' q)
        obtain ⟨y1, hF1', hy1⟩ := tst_sound X (AR.symm R) hst1 hm1 (by omega)
        refine ⟨z1, r1', y1, hst1, hmem1, hy1, fun q => ?_⟩
        have hx := (hF1' _).symm.trans (hf1'' q)
        beta_reduce at hx
        rw [bR, show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega] at hx
        change (bif (bif f2 then _ else _) then true else _) = false at hx
        cases hnd : (bif f2 then nodeOH 0 (fun _ c d ka kc => hb (H2 q.1) (hashP c.s d ka kc)) (fun _ => F2 q.1 k t0)
            (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m))
            else node (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m))) <;>
          rw [hnd] at hx <;> simp at hx <;> rfl
      · have hf1f : f1 = false := Bool.eq_false_iff.2 hf1
        obtain ⟨z1, r1', hf1', hst1, hmem1⟩ := nots_sound_all X (k := k + 1) hs hm (by omega) rfl rfl (NK.sizeU hcard hm hk hu hl1 hy) hu hl1 hwa (by omega) (Or.inl rfl) hwa
          fun q : β1 => (h0 q.1).2.2 t0 rfl |>.2 hf1f
        have hf1'' : ∀ q : β1, _ := fun q => cv_ok X hst1 hl1 (hf1' q)
        obtain ⟨y1, hF1', hy1⟩ := tst_sound X (AR.symm R) hst1 hm1 (by omega)
        refine ⟨z1, r1', y1, hst1, hmem1, hy1, fun q => ?_⟩
        have hx := (hF1' _).symm.trans (hf1'' q)
        beta_reduce at hx
        rw [bR, show k + 2 - 2 = k by omega, show k + 2 - 1 = k + 1 by omega] at hx
        change (bif (bif f2 then _ else _) then true else _) = false at hx
        cases hnd : (bif f2 then nodeOH 0 (fun _ c d ka kc => hb (H2 q.1) (hashP c.s d ka kc)) (fun _ => F2 q.1 k t0)
            (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m))
            else node (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m))) <;>
          rw [hnd] at hx <;> simp at hx <;> rfl
    obtain ⟨z1, r1', y1, hst1, hmem1, hy1, hq1⟩ := hmid
    obtain ⟨wc, hwc, ewc⟩ := hst1.rep.mem.1 hbi.sub.2.1
    let r2 := hashP wc.s d (decide ((wa.s ^^^ m) ∈ S2)) (decide (wc.s ∈ S2))
    let β2 := {q : α // (f1 = true → hb (H1 q) r1 = true) ∧ (f2 = true → hb (H2 q) r2 = true)}
    cases hf2 : f2
    · have hp' : ∀ q : β2, node (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m)) = false := fun q => by
        simpa [hf2] using hq1 ⟨q.1, q.2.1⟩
      obtain ⟨z', r, hf, hst, hmem⟩ := node_bi_all X (AR.symm R) (α := β2) (f := fun q => F2 q.1 k t0) hst1 hm1 (by omega) rfl rfl
        (NK.sizeB hst1.rep.card hm1 (by omega) hbi hl hy1) hbi hl
        (fun a' c' ha' hc' hax hcy => Or.inl fun q h xs hp hxs => by
          subst hxs
          exact pairsP_false hp (List.mem_map_of_mem ha') hax (List.mem_map_of_mem hc') (fun e => hbi.1 (by rw [← hcy, ← e]; rfl)))
        hp'
      exact hF2 r1 r2 (hashNot_lt _ _) (hashP_lt _ _ _ _) k t0 z' r S2 hf hst (codB (codU hcod hmem1) hmem) k0 (by omega) (hbi.min hl hm1.2)
    · have hp' : ∀ q : β2, nodeOH 0 (fun _ c d ka kc => hb (H2 q.1) (hashP c.s d ka kc)) (fun _ => F2 q.1 k t0)
          (pos' t0) l m g (k + 1 - t0 - y1) r1'.length z1 r1' (pairsP (wa.s ^^^ m)) = false := fun q => by
        simpa [hf2] using hq1 ⟨q.1, q.2.1⟩
      obtain ⟨_, _, _, _, _, _, z', r, hf, hst, hmem⟩ := nodeOH_bi_l_all X (AR.symm R) (α := β2)
        (hf := fun q _ c d ka kc => hb (H2 q.1) (hashP c.s d ka kc))
        (f := fun q _ => F2 q.1 k t0) hst1 hm1 (by omega) rfl rfl
        (NK.sizeB hst1.rep.card hm1 (by omega) hbi hl hy1) hbi hl
        (fun _ _ _ _ _ _ => Nat.zero_le _)
        (fun q a' c' ha' hc' hax hcy => by
          obtain rfl := hst1.rep.inj hc' hwc (hcy.trans ewc.symm)
          rw [hax]
          exact q.2.2 hf2)
        (fun a' c' ha' hc' hax hcy q h xs hp hxs => by
          subst hxs
          exact pairsP_false hp (List.mem_map_of_mem ha') hax (List.mem_map_of_mem hc') (fun e => hbi.1 (by rw [← hcy, ← e]; rfl)))
        hp'
      exact hF2 r1 r2 (hashNot_lt _ _) (hashP_lt _ _ _ _) k t0 z' r S2 (fun q => hf q) hst (codB (codU hcod hmem1) hmem) k0 (by omega) (hbi.min hl hm1.2)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
    have hl1 := hbi.live hl
    have hl2 := hu'.live hl1
    obtain ⟨wa, hwa, rfl⟩ := hs.rep.mem.1 hu.sub.1
    let r1 := hashNot wa.s (decide (wa.s ∈ S1))
    let β1 := {q : α // f1 = true → hb (H1 q) r1 = true}
    have hm1 := hu.min hl2 hm.2
    have hmid : ∃ z1 r1' y1, StOk P T l m (k + 2) (t0 + 1) z1 r1' S1 ∧ (∀ w ∈ r1', w = notW m wa ∨ w ∈ v) ∧
        (y1 = 0 ∨ (y1 = 1 ∧ r1'.length + (t0 + 1) = k + 2 ∧ NK (AR R) m T (k0 + 1 + 1) (t0 + 1) S1)) ∧
        ∀ q : β1, (bif f2 then notsC (H2 q.1) (fun _ q' z v => cv (pos' t0) l v (tst (pos' t0) l (k + 2 - t0) v (fun y =>
            nodeQ (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y) v.length z v (pairsQ (wa.s ^^^ m) q'))))
              m g (k + 2 - t0 - y1) r1'.length z1 (pos' t0) ((wa.s ^^^ m) + 1) wa.s r1' r1'
            else nots (fun _ q' z v => cv (pos' t0) l v (tst (pos' t0) l (k + 2 - t0) v (fun y =>
              nodeQ (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y) v.length z v (pairsQ (wa.s ^^^ m) q'))))
              m g (k + 2 - t0 - y1) r1'.length z1 (pos' t0) ((wa.s ^^^ m) + 1) wa.s r1' r1') = false := by
      by_cases hf1 : f1 = true
      · obtain ⟨z1, r1', hf1', hst1, hmem1⟩ := notsC_sound_all X hs hm (by omega) rfl rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) (Or.inl rfl) hwa
          (fun q : β1 => q.2 hf1) (fun q : β1 => (h0 q.1).2.2 (t0 + 1) rfl |>.1 hf1)
        have hf1'' : ∀ q : β1, _ := fun q => cv_ok X hst1 hl2 (hf1' q)
        obtain ⟨y1, hF1', hy1⟩ := tst_sound X (AR.symm R) hst1 hm1 (by omega)
        refine ⟨z1, r1', y1, hst1, hmem1, hy1, fun q => ?_⟩
        have hx := (hF1' _).symm.trans (hf1'' q)
        beta_reduce at hx
        rw [bR] at hx
        change (bif _ then true else prd (t0 + 1) _) = false at hx
        cases hnd : (bif f2 then nodeOH 0 _ _ _ _ _ _ _ _ _ _ _ else node _ _ _ _ _ _ _ _ _ _) <;> rw [hnd] at hx <;> simp at hx
        dsimp only [prd] at hx
        rw [Bool.cond_eq_ite]
        exact hx
      · have hf1f : f1 = false := Bool.eq_false_iff.2 hf1
        obtain ⟨z1, r1', hf1', hst1, hmem1⟩ := nots_sound_all X (k := k + 2) hs hm (by omega) rfl rfl (NK.sizeU hcard hm hk hu hl2 hy) hu hl2 hwa (by omega) (Or.inl rfl) hwa
          fun q : β1 => (h0 q.1).2.2 (t0 + 1) rfl |>.2 hf1f
        have hf1'' : ∀ q : β1, _ := fun q => cv_ok X hst1 hl2 (hf1' q)
        obtain ⟨y1, hF1', hy1⟩ := tst_sound X (AR.symm R) hst1 hm1 (by omega)
        refine ⟨z1, r1', y1, hst1, hmem1, hy1, fun q => ?_⟩
        have hx := (hF1' _).symm.trans (hf1'' q)
        beta_reduce at hx
        rw [bR] at hx
        change (bif _ then true else prd (t0 + 1) _) = false at hx
        cases hnd : (bif f2 then nodeOH 0 _ _ _ _ _ _ _ _ _ _ _ else node _ _ _ _ _ _ _ _ _ _) <;> rw [hnd] at hx <;> simp at hx
        dsimp only [prd] at hx
        rw [Bool.cond_eq_ite]
        exact hx
    obtain ⟨z1, r1', y1, hst1, hmem1, hy1, hq1⟩ := hmid
    obtain ⟨wa', hwa', rfl⟩ := hst1.rep.mem.1 hu'.sub.1
    let r2 := hashNot wa'.s (decide (wa'.s ∈ S2))
    let β2 := {q : α // (f1 = true → hb (H1 q) r1 = true) ∧ (f2 = true → hb (H2 q) r2 = true)}
    have hm2 := hu'.min hl1 hm1.2
    let cont2Fn : β2 → ℕ → ℕ → ℕ → List W → Bool := fun q _ q' z v =>
      cv (pos' t0) l v (tst (pos' t0) l (k + 2 - t0) v (fun y =>
        nodeQ (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y) v.length z v (pairsQ (wa.s ^^^ m) q')))
    have hmid2 : ∃ z2 r2' y2, StOk P T l m (k + 1) t0 z2 r2' S2 ∧ (∀ w ∈ r2', w = notW m wa' ∨ w ∈ r1') ∧
        (y2 = 0 ∨ (y2 = 1 ∧ r2'.length + t0 = k + 1 ∧ NK (AR R) m T (k0 + 1) t0 S2)) ∧
        ∀ q : β2, nodeQ (F2 q.1 k t0) (pos' t0) l m g (k + 1 - t0 - y2) r2'.length z2 r2' (pairsQ (wa.s ^^^ m) (wa'.s ^^^ m)) = false := by
      by_cases hf2 : f2 = true
      · obtain ⟨z2, r2', hf3', hst2, hmem2⟩ := notsC_sound_all X (f := cont2Fn) (q := (wa.s ^^^ m) + 1) (lt := wa.s)
          hst1 hm1 (by omega) rfl rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1)
          hu' hl1 hwa' (by omega) (Or.inr ha'a) hwa' (fun q : β2 => q.2.2 hf2)
          fun q : β2 => by have := hq1 ⟨q.1, q.2.1⟩; simp [hf2] at this; exact this
        have hf3'' : ∀ q : β2, _ := fun q => cv_ok X hst2 hl1 (hf3' q)
        obtain ⟨y2, hF3', hy2⟩ := tst_sound X (AR.symm R) hst2 hm2 (by omega)
        exact ⟨z2, r2', y2, hst2, hmem2, hy2, fun q => by have hx := (hF3' _).symm.trans (hf3'' q); beta_reduce at hx; exact hx⟩
      · have hf2f : f2 = false := Bool.eq_false_iff.2 hf2
        obtain ⟨z2, r2', hf3', hst2, hmem2⟩ := nots_sound_all X (f := cont2Fn) (q := (wa.s ^^^ m) + 1) (lt := wa.s)
          (k := k + 1) hst1 hm1 (by omega) rfl rfl (NK.sizeU hst1.rep.card hm1 (by omega) hu' hl1 hy1)
          hu' hl1 hwa' (by omega) (Or.inr ha'a) hwa'
          fun q : β2 => by have := hq1 ⟨q.1, q.2.1⟩; simp [hf2f] at this; exact this
        have hf3'' : ∀ q : β2, _ := fun q => cv_ok X hst2 hl1 (hf3' q)
        obtain ⟨y2, hF3', hy2⟩ := tst_sound X (AR.symm R) hst2 hm2 (by omega)
        exact ⟨z2, r2', y2, hst2, hmem2, hy2, fun q => by have hx := (hF3' _).symm.trans (hf3'' q); beta_reduce at hx; exact hx⟩
    obtain ⟨z2, r2', y2, hst2, hmem2, hy2, hq2⟩ := hmid2
    have hSsubm : ∀ x ∈ S, x &&& m = x := fun x hx => by
      obtain ⟨wx, hwx, rfl⟩ := hs.rep.mem.1 hx; exact hs.subm wx hwx
    have hq12 := Branch3_no_can0 hm hSsubm hu hne hu' hbi hl
    have hS3len := NK.sizeB hst2.rep.card hm2 (by omega) hbi hl hy2
    have hS2leS3 : S2.card ≤ S3.card := by
      obtain ⟨_, U, eS2, eS3, _⟩ := id hbi
      have hfr3 := hbi.fresh hl hm2.2
      have hopU : op d (wa.s ^^^ m) (wa'.s ^^^ m) ∉ U := fun h => hfr3 (sub_C _ _ (by rw [eS2]; simp [h]))
      have hu12 : wa.s ^^^ m ∈ U ∨ wa'.s ^^^ m ∈ U := by
        rcases hq12 with h | h
        · rw [eS3, Finset.mem_insert] at h
          exact Or.inl (h.resolve_left fun e => hfr3 (sub_C _ _ (by rw [eS2, ← e]; simp)))
        · rw [eS3, Finset.mem_insert] at h
          exact Or.inr (h.resolve_left fun e => hfr3 (sub_C _ _ (by rw [eS2, ← e]; simp)))
      rw [eS3, Finset.card_insert_of_notMem hopU, eS2]
      rcases hu12 with h | h
      · rw [Finset.insert_comm, Finset.insert_eq_of_mem h]; exact Finset.card_insert_le _ U
      · rw [Finset.insert_eq_of_mem h]; exact Finset.card_insert_le _ U
    have hne2 : r2'.length ≤ k + 1 - t0 - y2 := by
      have := hst2.rep.card; omega
    obtain ⟨z', r, hf, hst, hmem⟩ := nodeQ_bi_all X (AR.symm R) (α := β2) (f := fun q => F2 q.1 k t0) hst2 hm2 (by omega) rfl rfl hne2 hS3len hbi hl hq12
      (fun a_w c_w ha_w hc_w hax hcy => Or.inl fun q h xs hp hxs => by
        subst hxs
        exact pairsQ_false hp (List.mem_map_of_mem ha_w) hax (List.mem_map_of_mem hc_w) hcy)
      hq2
    exact hF2 r1 r2 (hashNot_lt _ _) (hashNot_lt _ _) k t0 z' r S3 hf hst (codB (codU (codU hcod hmem1) hmem2) hmem) k0 (by omega) (hbi.min hl hm2.2)

theorem look1MC_sound_all {R : ℕ → ℕ} {α : Type} {H : α → ℕ} {K : ℕ}
    (hcov : ∀ r : ℕ, r < MM → ∃ q : α, hb (H q) r = true) :
    ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ),
    (∀ q : α, look1M l m g K (H q) k t z v = false) → StOk P T l m k t z v S → Cod R v →
      ∀ k' ≤ k, ¬ Min (AR R) m T k' t S := by
  intro k t z v S h hs hcod k' hk hm
  cases h0 : Nat.ble v.length 1 with
  | true =>
    obtain ⟨q0, _⟩ := hcov 0 (by decide)
    have hq := h q0
    change (Bool.rec (motive := fun _ => Bool) _ true (Nat.ble v.length 1) : Bool) = false at hq
    rw [h0] at hq; simp at hq
  | false =>
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    obtain ⟨y, hFy, hyk⟩ := tst_sound X (AR.symm R) hs hm hk
    have hy : ∀ q : α, mvHG (look l m g K) (look l m g K) (H q) 0 true false l m g k t z v y = false := fun q => by
      have hq := h q
      change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
        mvHG (look l m g K) (look l m g K) (H q) 0 true false l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at hq
      rw [bR, pos_eq, h0, Bool.cond_false] at hq
      have hq' := (hFy _).symm.trans hq
      beta_reduce at hq'; exact hq'
    refine mvHGC_sound_all X (R := R) (H1 := H) (H2 := fun _ => 0) (F1 := fun _ => look l m g K) (F2 := fun _ => look l m g K) (f1 := true) (f2 := false)
      (fun r1 hr1 k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 => by
        obtain ⟨q0, hq0⟩ := hcov r1 hr1
        exact look_sound X K k1 t1 z1 v1 S1 (hf ⟨q0, fun _ => hq0⟩) hs1 hc1 k1' hk1)
      (fun r1 _ hr1 _ k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 => by
        obtain ⟨q0, hq0⟩ := hcov r1 hr1
        exact look_sound X K k1 t1 z1 v1 S1 (hf ⟨q0, ⟨fun _ => hq0, fun h => absurd h (by simp)⟩⟩) hs1 hc1 k1' hk1)
      hs hcod hlen hy k' hk hm hyk

theorem lookMC_sound_all {R : ℕ → ℕ} {α : Type} {Ha Hb : α → ℕ} {K : ℕ}
    (hcov : ∀ r1 r2 : ℕ, r1 < MM → r2 < MM → ∃ q : α, hb (Ha q) r1 = true ∧ hb (Hb q) r2 = true) :
    ∀ (k t z : ℕ) (v : List W) (S : Finset ℕ),
    (∀ q : α, lookM l m g K (Ha q) (Hb q) k t z v = false) → StOk P T l m k t z v S → Cod R v →
      ∀ k' ≤ k, ¬ Min (AR R) m T k' t S := by
  intro k t z v S h hs hcod k' hk hm
  cases h0 : Nat.ble v.length 1 with
  | true =>
    obtain ⟨q0, _⟩ := hcov 0 0 (by decide) (by decide)
    have hq := h q0
    change (Bool.rec (motive := fun _ => Bool) _ true (Nat.ble v.length 1) : Bool) = false at hq
    rw [h0] at hq; simp at hq
  | false =>
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    obtain ⟨y, hFy, hyk⟩ := tst_sound X (AR.symm R) hs hm hk
    have hy : ∀ q : α, mvHG (look1M l m g K (Hb q)) (look l m g K) (Ha q) (Hb q) true true l m g k t z v y = false := fun q => by
      have hq := h q
      change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
        mvHG (look1M l m g K (Hb q)) (look l m g K) (Ha q) (Hb q) true true l m g k t z v y)) true (Nat.ble v.length 1) : Bool) = false at hq
      rw [bR, pos_eq, h0, Bool.cond_false] at hq
      have hq' := (hFy _).symm.trans hq
      beta_reduce at hq'; exact hq'
    refine mvHGC_sound_all X (R := R) (H1 := Ha) (H2 := Hb) (F1 := fun q => look1M l m g K (Hb q)) (F2 := fun _ => look l m g K) (f1 := true) (f2 := true)
      (fun r1 hr1 k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 =>
        look1MC_sound_all X (α := {q : α // true = true → hb (Ha q) r1 = true})
          (fun r2 hr2 => by
            obtain ⟨q0, h1, h2⟩ := hcov r1 r2 hr1 hr2
            exact ⟨⟨q0, fun _ => h1⟩, h2⟩)
          k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1)
      (fun r1 r2 hr1 hr2 k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 => by
        obtain ⟨q0, h1, h2⟩ := hcov r1 r2 hr1 hr2
        exact look_sound X K k1 t1 z1 v1 S1 (hf ⟨q0, ⟨fun _ => h1, fun _ => h2⟩⟩) hs1 hc1 k1' hk1)
      hs hcod hlen hy k' hk hm hyk

theorem top1_sound {R : ℕ → ℕ} (hRle : ∀ x, R x ≤ 6) (hRinj : ∀ x y, R x ≠ 0 → R x = R y → x = y)
    {α : Type} {H3 : α → ℕ} {K : ℕ}
    (hcov : ∀ r3 : ℕ, r3 < MM → ∃ q : α, hb (H3 q) r3 = true) :
    ∀ (k t lb z : ℕ) (v : List W) (S : Finset ℕ),
      (∀ q : α, top1C l m g K (H3 q) k t lb z v = false) → StOk P T l m k t z v S → (∀ w ∈ v, w.r = R w.s) →
      ∀ k' ≤ k, Live (AL R lb) m T k' t S → (∀ q < k', ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) → False := by
  intro k t lb z v S h hs hcod k' hk hl hmW
  cases h0 : Nat.ble v.length 1 with
  | true =>
    obtain ⟨q0, _⟩ := hcov 0 (by decide)
    have hq := h q0
    change (Bool.rec (motive := fun _ => Bool) _ true (Nat.ble v.length 1) : Bool) = false at hq
    rw [h0] at hq; simp at hq
  | false =>
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    have hmin : Min A0 m T k' t S := ⟨hl.to0, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
    obtain ⟨y, hFy, hyk⟩ := tst_sound X a0_symm hs hmin hk
    have hy : ∀ q : α,
        nodeOH lb (fun a c d ka kc => hb (H3 q) (hashFS a.r c.r d ka kc)) (look1 l m g K K (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsS = false ∧
        mvHG (look l m g K) (look l m g K) (H3 q) 0 true false l m g k t z v y = false := fun q => by
      have hq := h q
      change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) (mvHG (look l m g K) (look l m g K) (H3 q) 0 true false l m g k t z v y) true
          (nodeOH lb (fun a c d ka kc => hb (H3 q) (hashFS a.r c.r d ka kc)) (look1 l m g K K (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS)))
        true (Nat.ble v.length 1) : Bool) = false at hq
      rw [bR, pos_eq, h0, Bool.cond_false] at hq
      have hq' := (hFy _).symm.trans hq
      beta_reduce at hq'
      obtain ⟨hno, hmv⟩ := or_false' X hq'
      exact ⟨hno, hmv⟩
    have hcard := hs.rep.card
    rcases front_ord hRle hRinj hl hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', hlb, hb, hl1⟩
    · refine mvHGC_sound_all X (R := R) (H1 := H3) (H2 := fun _ => 0) (F1 := fun _ => look l m g K) (F2 := fun _ => look l m g K) (f1 := true) (f2 := false)
        (fun r1 hr1 k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 => by
          obtain ⟨q0, hq0⟩ := hcov r1 hr1
          exact look_sound X K k1 t1 z1 v1 S1 (hf ⟨q0, fun _ => hq0⟩) hs1 hc1 k1' hk1)
        (fun r1 _ hr1 _ k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 => by
          obtain ⟨q0, hq0⟩ := hcov r1 hr1
          exact look_sound X K k1 t1 z1 v1 S1 (hf ⟨q0, ⟨fun _ => hq0, fun h => absurd h (by simp)⟩⟩) hs1 hc1 k1' hk1)
        hs (fun w hw => Or.inr (hcod w hw)) hlen (fun q => (hy q).2) k' hk ⟨hlR, hmin.2⟩ (hyk.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
    · obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      obtain ⟨wa, hwa, ewa⟩ := hs.rep.mem.1 hb.sub.1
      obtain ⟨wb, hwb, ewb⟩ := hs.rep.mem.1 hb.sub.2.1
      let r3 := hashFS (R a) (R b) d (decide (a ∈ S1)) (decide (b ∈ S1))
      obtain ⟨q0, hq0⟩ := hcov r3 (hashFS_lt _ _ _ _ _)
      have hg2 : ∀ h xs, pairsS h xs = false → xs = v.map (mkx (pos' t) l (wst (pos' t) l v)) →
          h (mkx (pos' t) l (wst (pos' t) l v) wa) (mkx (pos' t) l (wst (pos' t) l v) wb) = false ∨
          h (mkx (pos' t) l (wst (pos' t) l v) wb) (mkx (pos' t) l (wst (pos' t) l v) wa) = false := fun h xs hp hxs => by
        subst hxs
        exact pairs_any hp (fs_mem (List.mem_map_of_mem hwa) (by dsimp only [mkx]; rw [hcod wa hwa, ewa]; exact ha))
          (fs_mem (List.mem_map_of_mem hwb) (by dsimp only [mkx]; rw [hcod wb hwb, ewb]; exact hb'))
          (fun e => hb.1 (by rw [← ewa, ← ewb]; exact congrArg XW.s e))
      have hne_R : R a ≠ R b := fun e => hb.1 (hRinj a b ha e)
      obtain ⟨a', c', ha', hc', ea', ec', z', r, hfn, hst, hmem⟩ := nodeOH_bi X a0_symm hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hb hl1.to0 hyk) hb hl1.to0
        (fun w1 w2 hw1 hw2 ew1 ew2 => by
          obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
          obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
          rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact hlb)
        (fun w1 w2 hw1 hw2 ew1 ew2 => by
          obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
          obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
          rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact hq0)
        (fun w1 w2 hw1 hw2 ew1 ew2 => by
          obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
          obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
          rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb, hashFS_symm hne_R.symm]; exact hq0)
        (fun h xs hp a'' c'' ha'' hc'' e1 e2 hxs => by
          obtain rfl := hs.rep.inj ha'' hwa (e1.trans ewa.symm)
          obtain rfl := hs.rep.inj hc'' hwb (e2.trans ewb.symm)
          exact hg2 h xs hp hxs) (hy q0).1
      have hwa' : wa = a' := hs.rep.inj hwa ha' (ewa.trans ea'.symm)
      have hwb' : wb = c' := hs.rep.inj hwb hc' (ewb.trans ec'.symm)
      rw [← hwa', ← hwb', hcod wa hwa, hcod wb hwb, ewa, ewb] at hfn
      have hfr : R (op d a b) = 0 := by
        by_contra hne
        refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
        have hx' := hb.sub.2.2 hx
        simp only [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · exact Or.inl (Or.inl hne)
        · exact Or.inl (Or.inr hx')
      refine look1_sound X hRle hRinj (K := K) _ k t _ z' r S1 hfn hst ?_ k0 (by simpa using hk) hl1 ?_
      · intro w hw
        rcases hmem w hw with ⟨e1, e2⟩ | h'
        · rw [e1, e2, hfr]
        · exact hcod w h'
      · intro q hq hs'
        refine hmW (q + 1) (by omega) (.bi (d := d) (a := a) (b := b) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (a0_all _ _ _) (hs'.mono le_rfl ?_))
        rintro x ((hx | hx) | hx)
        · exact Or.inr (Or.inl (Or.inl hx))
        · have hx' := hb.sub.2.2 hx
          simp only [Finset.mem_insert] at hx'
          rcases hx' with rfl | hx'
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (Or.inr hx'))
        · exact Or.inr (Or.inr hx)

lemma bi_cod_min {R : ℕ → ℕ} {m T k0 : ℕ} {d_op : Bool} {a b : ℕ} {S S1 : Finset ℕ} {v r : List W}
    (hcod : ∀ w ∈ v, w.r = R w.s)
    (hb : Bi A0 d_op a b S S1) (hl1 : Live A0 m T k0 t S1)
    (hmW : ∀ q < k0 + 1, ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ))))
    (hmem : ∀ w ∈ r, (w.s = op d_op a b ∧ w.r = 0) ∨ w ∈ v) :
    (∀ w ∈ r, w.r = R w.s) ∧ ∀ q < k0, ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S1 : Set ℕ))) := by
  clear X
  have hfr : R (op d_op a b) = 0 := by
    by_contra hne
    refine hmW k0 (by omega) (hl1.sol.mono le_rfl fun x hx => ?_)
    have hx' := hb.sub.2.2 hx
    simp only [Finset.mem_insert] at hx'
    rcases hx' with rfl | hx'
    · exact Or.inl (Or.inl hne)
    · exact Or.inl (Or.inr hx')
  refine ⟨fun w hw => ?_, fun q hq hs' => ?_⟩
  · rcases hmem w hw with ⟨e1, e2⟩ | h'
    · rw [e1, e2, hfr]
    · exact hcod w h'
  · refine hmW (q + 1) (by omega) (.bi (d := d_op) (a := a) (b := b) (Or.inl (Or.inr hb.sub.1)) (Or.inl (Or.inr hb.sub.2.1)) (a0_all _ _ _) (hs'.mono le_rfl ?_))
    rintro x ((hx | hx) | hx)
    · exact Or.inr (Or.inl (Or.inl hx))
    · have hx' := hb.sub.2.2 hx
      simp only [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx'
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr hx'))
    · exact Or.inr (Or.inr hx)

lemma top1b_sound {R : ℕ → ℕ} (hRle : ∀ x, R x ≤ 6) (hRinj : ∀ x y, R x ≠ 0 → R x = R y → x = y)
    {α : Type} {H2 H3 : α → ℕ} {K : ℕ}
    (hcov : ∀ r2 r3 : ℕ, r2 < MM → r3 < MM → ∃ q : α, hb (H2 q) r2 = true ∧ hb (H3 q) r3 = true)
    {k k0 t lb z : ℕ} {v : List W} {S S1 : Finset ℕ} {d : Bool} {a b : ℕ}
    (h : ∀ q : α, top1bC l m g K (H2 q) (H3 q) k t lb z v = false)
    (hs : StOk P T l m k t z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    (hk : k0 + 1 ≤ k) (ha : R a ≠ 0) (hb' : R b ≠ 0) (hlb : lb ≤ gkey (R a) (R b) d)
    (hbi : Bi A0 d a b S S1) (hl1 : Live (AL R (gkey (R a) (R b) d + 1)) m T k0 t S1)
    (hmW : ∀ q < k0 + 1, ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  cases h0 : Nat.ble v.length 1 with
  | true =>
    obtain ⟨q0, _⟩ := hcov 0 0 (by decide) (by decide)
    have hq := h q0
    change (Bool.rec (motive := fun _ => Bool) _ true (Nat.ble v.length 1) : Bool) = false at hq
    rw [h0] at hq; simp at hq
  | false =>
    have hmin : Min A0 m T (k0 + 1) t S := ⟨by obtain ⟨hab, U, e1, e2, _⟩ := id hbi; rw [e1]; exact .bi hab trivial (e2 ▸ hl1.to0), fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
    obtain ⟨y, hFy, hyk⟩ := tst_sound X a0_symm hs hmin hk
    have hy : ∀ q : α, nodeOH lb (fun a c d ka kc => hb (H2 q) (hashFS a.r c.r d ka kc))
        (top1C l m g K (H3 q) (k - 1) t) (pos' t) l m g (k - t - y) v.length z v pairsS = false := fun q => by
      have hq := h q
      change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (k + 1 - t) v (fun y =>
        nodeOH lb (fun a c d ka kc => hb (H2 q) (hashFS a.r c.r d ka kc)) (top1C l m g K (H3 q) (k - 1) t) (pos t) l m g (k - t - y) v.length z v pairsS))
        true (Nat.ble v.length 1) : Bool) = false at hq
      rw [bR, pos_eq, h0, Bool.cond_false] at hq
      have hq' := (hFy _).symm.trans hq
      beta_reduce at hq'
      exact hq'
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hcard := hs.rep.card
    obtain ⟨wa, hwa, ewa⟩ := hs.rep.mem.1 hbi.sub.1
    obtain ⟨wb, hwb, ewb⟩ := hs.rep.mem.1 hbi.sub.2.1
    let r2 := hashFS (R a) (R b) d (decide (a ∈ S1)) (decide (b ∈ S1))
    let β := {q : α // hb (H2 q) r2 = true}
    have hne_R : R a ≠ R b := fun e => hbi.1 (hRinj a b ha e)
    obtain ⟨a', c', ha', hc', ea', ec', z', r, hfn, hst, hmem⟩ := nodeOH_bi_all X a0_symm (α := β)
      (hf := fun q a c d ka kc => hb (H2 q.1) (hashFS a.r c.r d ka kc))
      (f := fun q => top1C l m g K (H3 q.1) k t) hs hmin (by omega) rfl rfl (NK.sizeB hcard hmin hk hbi hl1.to0 hyk) hbi hl1.to0
      (fun w1 w2 hw1 hw2 ew1 ew2 => by
        obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
        obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
        rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact hlb)
      (fun q w1 w2 hw1 hw2 ew1 ew2 => by
        obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
        obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
        rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact q.2)
      (fun q w1 w2 hw1 hw2 ew1 ew2 => by
        obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
        obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
        rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb, hashFS_symm hne_R.symm]; exact q.2)
      (fun w1 w2 hw1 hw2 ew1 ew2 => by
        have hne_xw : mkx (pos' t) l (wst (pos' t) l v) w1 ≠ mkx (pos' t) l (wst (pos' t) l v) w2 := fun e =>
          hbi.1 (by rw [← ew1, ← ew2]; exact congrArg XW.s e)
        have hm1 := fs_mem (List.mem_map_of_mem (f := mkx (pos' t) l (wst (pos' t) l v)) hw1) (by change w1.r ≠ 0; rw [hcod w1 hw1, ew1]; exact ha)
        have hm2 := fs_mem (List.mem_map_of_mem (f := mkx (pos' t) l (wst (pos' t) l v)) hw2) (by change w2.r ≠ 0; rw [hcod w2 hw2, ew2]; exact hb')
        exact (pairs_dir hm1 hm2 hne_xw).imp (fun f q h xs hp hxs => by subst hxs; exact f h hp)
          (fun f q h xs hp hxs => by subst hxs; exact f h hp))
      (fun q => hy q.1)
    have hwa' : wa = a' := hs.rep.inj hwa ha' (ewa.trans ea'.symm)
    have hwb' : wb = c' := hs.rep.inj hwb hc' (ewb.trans ec'.symm)
    have hgk : gkey a'.r c'.r d = gkey (R a) (R b) d := by rw [← hwa', ← hwb', hcod wa hwa, hcod wb hwb, ewa, ewb]
    rw [hgk] at hfn
    obtain ⟨hcod', hmW'⟩ := bi_cod_min (t := t) X hcod hbi (hl1.rel fun _ _ _ _ => trivial) hmW hmem
    exact top1_sound X hRle hRinj (α := β) (H3 := fun q => H3 q.1)
      (fun r3 hr3 => by
        obtain ⟨q0, h2, h3⟩ := hcov r2 r3 (hashFS_lt _ _ _ _ _) hr3
        exact ⟨⟨q0, h2⟩, h3⟩)
      k t _ z' r S1 hfn hst hcod' k0 (by simpa using hk) hl1 hmW'

theorem top2_sound {R : ℕ → ℕ} (hRle : ∀ x, R x ≤ 6) (hRinj : ∀ x y, R x ≠ 0 → R x = R y → x = y)
    {M : List (ℕ × ℕ × ℕ × ℕ)} (hM : mFull3 M = true)
    {K t z : ℕ} {v : List W} {S : Finset ℕ}
    (all : ∀ p ∈ M, top2C l m g K p.1 p.2.1 p.2.2.1 p.2.2.2 K t z v = false)
    (hs : StOk P T l m K t z v S) (hcod : ∀ w ∈ v, w.r = R w.s)
    {k' : ℕ} (hk : k' ≤ K) (hl : Live A0 m T k' t S)
    (hmW : ∀ q < k', ¬ Sol A0 m T q (C m ({x | R x ≠ 0} ∪ (S : Set ℕ)))) : False := by
  obtain ⟨p0, hp0, _⟩ := mFull3_cov hM (Or.inl rfl) (by decide : 0 < MM) (by decide : 0 < MM) (by decide : 0 < MM)
  cases h0 : Nat.ble v.length 1 with
  | true =>
    have hq := all p0 hp0
    change (Bool.rec (motive := fun _ => Bool) _ true (Nat.ble v.length 1) : Bool) = false at hq
    rw [h0] at hq; simp at hq
  | false =>
    have hlen : 2 ≤ v.length := by
      by_contra hc
      rw [Nat.ble_eq_true_of_le (by omega)] at h0; simp at h0
    have hl0 : Live (AL R 0) m T k' t S := hl.rel fun _ _ _ _ => Or.inr (Or.inr (Nat.zero_le _))
    have hmin : Min A0 m T k' t S := ⟨hl, fun q hq hs => hmW q hq (hs.mono le_rfl (C_mono Set.subset_union_right))⟩
    obtain ⟨y, hFy, hyk⟩ := tst_sound X a0_symm hs hmin hk
    have case_ph2 : ∀ p ∈ M, p.2.2.2 = 2 →
        nodeOH 0 (fun a c d ka kc => hb p.1 (hashFS a.r c.r d ka kc)) (look1 l m g K K (K - 1) t) (pos' t) l m g (K - t - y) v.length z v pairsS = false ∧
        mv (look l m g K) l m g K t z v y = false := fun p hpM hp2 => by
      have hq := all p hpM
      change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (K + 1 - t) v (fun y =>
        Bool.rec (motive := fun _ => Bool) _ (Bool.rec (motive := fun _ => Bool) (mv (look l m g K) l m g K t z v y) true
          (nodeOH 0 (fun a c d ka kc => hb p.1 (hashFS a.r c.r d ka kc)) (look1 l m g K K (K - 1) t) (pos t) l m g (K - t - y) v.length z v pairsS))
          (Nat.beq p.2.2.2 2))) true (Nat.ble v.length 1) : Bool) = false at hq
      rw [bR, pos_eq, h0, Bool.cond_false] at hq
      have hq' := (hFy _).symm.trans hq
      beta_reduce at hq'
      rw [hp2] at hq'
      obtain ⟨hno, hmv⟩ := or_false' X hq'
      exact ⟨hno, hmv⟩
    have hcard := hs.rep.card
    rcases front_ord hRle hRinj hl0 hmW with hlR | ⟨k0, d, a, b, S1, rfl, ha, hb', _, hbi, hl1⟩
    · by_cases hfast : ∃ p ∈ M, p.2.2.2 = 2
      · obtain ⟨p, hpM, hp2⟩ := hfast
        exact mv_sound X (look_sound X K) hs (fun w hw => Or.inr (hcod w hw)) hlen (case_ph2 p hpM hp2).2 k' hk ⟨hlR, hmin.2⟩
          (hyk.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
      · push Not at hfast
        let α := {p : ℕ × ℕ × ℕ × ℕ // p ∈ M ∧ p.2.2.2 = 1}
        let H1f : α → ℕ := fun q => q.1.1
        let H2f : α → ℕ := fun q => q.1.2.1
        let F1f : α → ℕ → ℕ → ℕ → List W → Bool := fun q => lookM l m g K q.1.2.1 q.1.2.2.1
        let F2f : α → ℕ → ℕ → ℕ → List W → Bool := fun q => look1M l m g K q.1.2.2.1
        have hmv : ∀ q : α, mvHGC I.NN I.AA I.HX I.HY (F1f q) (F2f q) (H1f q) (H2f q) true true l m g K t z v y = false := fun q => by
          have hq := all q.1 q.2.1
          change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (K + 1 - t) v (fun y =>
            Bool.rec (motive := fun _ => Bool)
              (Bool.rec (motive := fun _ => Bool)
                (Bool.rec (motive := fun _ => Bool)
                  (mvHGC I.NN I.AA I.HX I.HY (F1f q) (F2f q) (H1f q) (H2f q) true true l m g K t z v y)
                  _ (Nat.beq q.1.2.2.2 3))
                _ (Nat.beq q.1.2.2.2 0))
              _ (Nat.beq q.1.2.2.2 2))) true (Nat.ble v.length 1) : Bool) = false at hq
          rw [bR, pos_eq, h0, Bool.cond_false] at hq
          have hq' := (hFy _).symm.trans hq
          beta_reduce at hq'
          rw [q.2.2, bR, bR, bR] at hq'
          simp only [show Nat.beq 1 2 = false from rfl, show Nat.beq 1 0 = false from rfl,
            show Nat.beq 1 3 = false from rfl, Bool.cond_false] at hq'
          exact hq'
        refine mvHGC_sound_all X (R := R) (H1 := H1f) (H2 := H2f)
          (F1 := F1f) (F2 := F2f) (f1 := true) (f2 := true)
          (fun r1 hr1 k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 =>
            lookMC_sound_all X (R := R) (α := {q : α // true = true → hb (H1f q) r1 = true})
              (Ha := fun q => q.1.1.2.1) (Hb := fun q => q.1.1.2.2.1) (K := K)
              (fun r2 r3 hr2 hr3 => by
                obtain ⟨p, hpM, hp4, h1, h2, h3⟩ := mFull3_cov hM (Or.inr (Or.inr rfl)) hr1 hr2 hr3
                have hp1 : p.2.2.2 = 1 := hp4.resolve_left (hfast p hpM)
                exact ⟨⟨⟨p, hpM, hp1⟩, fun _ => h1⟩, h2, h3⟩)
              k1 t1 z1 v1 S1 (fun q => hf ⟨q.1, q.2⟩) hs1 hc1 k1' hk1)
          (fun r1 r2 hr1 hr2 k1 t1 z1 v1 S1 hf hs1 hc1 k1' hk1 =>
            look1MC_sound_all X (R := R) (α := {q : α // (true = true → hb (H1f q) r1 = true) ∧ (true = true → hb (H2f q) r2 = true)})
              (H := fun q => q.1.1.2.2.1) (K := K)
              (fun r3 hr3 => by
                obtain ⟨p, hpM, hp4, h1, h2, h3⟩ := mFull3_cov hM (Or.inr (Or.inr rfl)) hr1 hr2 hr3
                have hp1 : p.2.2.2 = 1 := hp4.resolve_left (hfast p hpM)
                exact ⟨⟨⟨p, hpM, hp1⟩, ⟨fun _ => h1, fun _ => h2⟩⟩, h3⟩)
              k1 t1 z1 v1 S1 (fun q => hf ⟨q.1, q.2⟩) hs1 hc1 k1' hk1)
          (k := K) (t := t) (z := z) (y := y) (v := v) (S := S)
          hs (fun w hw => Or.inr (hcod w hw)) hlen hmv k' hk ⟨hlR, hmin.2⟩ (hyk.imp id fun ⟨q1, q2, q3⟩ => ⟨q1, q2, q3.toR⟩)
    · obtain ⟨K, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
      obtain ⟨wa, hwa, ewa⟩ := hs.rep.mem.1 hbi.sub.1
      obtain ⟨wb, hwb, ewb⟩ := hs.rep.mem.1 hbi.sub.2.1
      let r1 := hashFS (R a) (R b) d (decide (a ∈ S1)) (decide (b ∈ S1))
      have hne_R : R a ≠ R b := fun e => hbi.1 (hRinj a b ha e)
      by_cases hfast : ∃ p ∈ M, p.2.2.2 = 2 ∧ hb p.1 r1 = true
      · obtain ⟨p, hpM, hp2, hpr1⟩ := hfast
        obtain ⟨a', c', ha', hc', ea', ec', z', r, hfn, hst, hmem⟩ := nodeOH_bi X a0_symm hs hmin (by omega) rfl rfl
          (NK.sizeB hcard hmin hk hbi hl1.to0 hyk) hbi hl1.to0
          (fun w1 w2 hw1 hw2 ew1 ew2 => by
            obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
            obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
            rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact Nat.zero_le _)
          (fun w1 w2 hw1 hw2 ew1 ew2 => by
            obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
            obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
            rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact hpr1)
          (fun w1 w2 hw1 hw2 ew1 ew2 => by
            obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
            obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
            rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb, hashFS_symm hne_R.symm]; exact hpr1)
          (fun h xs hp a' c' ha' hc' e1 e2 hxs => by
            subst hxs
            obtain rfl := hs.rep.inj ha' hwa (e1.trans ewa.symm)
            obtain rfl := hs.rep.inj hc' hwb (e2.trans ewb.symm)
            exact pairs_any hp (fs_mem (List.mem_map_of_mem ha') (by dsimp only [mkx]; rw [hcod a' ha', e1]; exact ha))
              (fs_mem (List.mem_map_of_mem hc') (by dsimp only [mkx]; rw [hcod c' hc', e2]; exact hb'))
              (fun e => hbi.1 (by rw [← e1, ← e2]; exact congrArg XW.s e)))
          (case_ph2 p hpM hp2).1
        have hwa' : wa = a' := hs.rep.inj hwa ha' (ewa.trans ea'.symm)
        have hwb' : wb = c' := hs.rep.inj hwb hc' (ewb.trans ec'.symm)
        rw [← hwa', ← hwb', hcod wa hwa, hcod wb hwb, ewa, ewb] at hfn
        obtain ⟨hcod', hmW'⟩ := bi_cod_min (t := t) X hcod hbi (hl1.rel fun _ _ _ _ => trivial) hmW hmem
        exact look1_sound X hRle hRinj (K := K + 1) _ K t _ z' r S1 hfn hst hcod' k0 (by simpa using hk) hl1 hmW'
      · push Not at hfast
        obtain ⟨_, hmW'⟩ := bi_cod_min (t := t) X hcod hbi (hl1.rel fun _ _ _ _ => trivial) hmW (fun w hw => Or.inr hw)
        rcases front_ord hRle hRinj hl1 hmW' with hl1R | ⟨k1, d1, a1, b1, S2, rfl, ha1, hb1', hlb1, hb1, hl2⟩
        · let α := {p : ℕ × ℕ × ℕ × ℕ // p ∈ M ∧ p.2.2.2 = 3 ∧ hb p.1 r1 = true}
          have hno : ∀ q : α, nodeOH 0 (fun a c d ka kc => hb q.1.1 (hashFS a.r c.r d ka kc))
              (fun _ => lookM l m g (K + 1) q.1.2.1 q.1.2.2.1 K t) (pos' t) l m g (K + 1 - t - y) v.length z v pairsS = false := fun q => by
            have hq := all q.1 q.2.1
            change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (K + 1 + 1 - t) v (fun y =>
              Bool.rec (motive := fun _ => Bool)
                (Bool.rec (motive := fun _ => Bool)
                  (Bool.rec (motive := fun _ => Bool) _
                    (nodeOH 0 (fun a c d ka kc => hb q.1.1 (hashFS a.r c.r d ka kc)) (fun _ => lookM l m g (K + 1) q.1.2.1 q.1.2.2.1 K t)
                      (pos t) l m g (K + 1 - t - y) v.length z v pairsS)
                    (Nat.beq q.1.2.2.2 3))
                  _ (Nat.beq q.1.2.2.2 0))
                _ (Nat.beq q.1.2.2.2 2))) true (Nat.ble v.length 1) : Bool) = false at hq
            rw [bR, pos_eq, h0, Bool.cond_false] at hq
            have hq' := (hFy _).symm.trans hq
            beta_reduce at hq'
            rw [q.2.2.1, bR, bR, bR] at hq'
            simp only [show Nat.beq 3 2 = false from rfl, show Nat.beq 3 0 = false from rfl,
              show Nat.beq 3 3 = true from rfl, Bool.cond_false, Bool.cond_true] at hq'
            exact hq'
          obtain ⟨_, _, _, _, _, _, z', r, hfn, hst, hmem⟩ := nodeOH_bi_all X a0_symm (α := α)
            (hf := fun q a c d ka kc => hb q.1.1 (hashFS a.r c.r d ka kc))
            (f := fun q _ => lookM l m g (K + 1) q.1.2.1 q.1.2.2.1 K t) hs hmin (by omega) rfl rfl
            (NK.sizeB hcard hmin hk hbi hl1.to0 hyk) hbi hl1.to0
            (fun _ _ _ _ _ _ => Nat.zero_le _)
            (fun q w1 w2 hw1 hw2 ew1 ew2 => by
              obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
              obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
              rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact q.2.2.2)
            (fun q w1 w2 hw1 hw2 ew1 ew2 => by
              obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
              obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
              rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb, hashFS_symm hne_R.symm]; exact q.2.2.2)
            (fun w1 w2 hw1 hw2 ew1 ew2 => by
              have hne_xw : mkx (pos' t) l (wst (pos' t) l v) w1 ≠ mkx (pos' t) l (wst (pos' t) l v) w2 := fun e =>
                hbi.1 (by rw [← ew1, ← ew2]; exact congrArg XW.s e)
              have hm1 := fs_mem (List.mem_map_of_mem (f := mkx (pos' t) l (wst (pos' t) l v)) hw1) (by dsimp only [mkx]; rw [hcod w1 hw1, ew1]; exact ha)
              have hm2 := fs_mem (List.mem_map_of_mem (f := mkx (pos' t) l (wst (pos' t) l v)) hw2) (by dsimp only [mkx]; rw [hcod w2 hw2, ew2]; exact hb')
              exact (pairs_dir hm1 hm2 hne_xw).imp (fun f q h xs hp hxs => by subst hxs; exact f h hp)
                (fun f q h xs hp hxs => by subst hxs; exact f h hp))
            hno
          obtain ⟨hcod1, hmW1⟩ := bi_cod_min (t := t) X hcod hbi (hl1.rel fun _ _ _ _ => trivial) hmW hmem
          have hmin1 : Min (AR R) m T k0 t S1 := ⟨hl1R, fun q hq hs' => hmW1 q hq (hs'.mono le_rfl (C_mono Set.subset_union_right))⟩
          exact lookMC_sound_all X (R := R) (α := α) (Ha := fun q => q.1.2.1) (Hb := fun q => q.1.2.2.1)
            (fun r2 r3 hr2 hr3 => by
              obtain ⟨p, hpM, hp4, h1, h2, h3⟩ := mFull3_cov hM (Or.inr (Or.inl rfl)) (hashFS_lt _ _ _ _ _) hr2 hr3
              have hp3 : p.2.2.2 = 3 := hp4.resolve_left fun h2' => hfast p hpM h2' h1
              exact ⟨⟨p, hpM, hp3, h1⟩, h2, h3⟩)
            K t z' r S1 (fun q => hfn q) hst (fun w hw => Or.inr (hcod1 w hw)) k0 (by omega) hmin1
        · let α := {p : ℕ × ℕ × ℕ × ℕ // p ∈ M ∧ p.2.2.2 = 0 ∧ hb p.1 r1 = true}
          have hno : ∀ q : α, nodeOH 0 (fun a c d ka kc => hb q.1.1 (hashFS a.r c.r d ka kc))
              (top1bC l m g (K + 1) q.1.2.1 q.1.2.2.1 K t) (pos' t) l m g (K + 1 - t - y) v.length z v pairsS = false := fun q => by
            have hq := all q.1 q.2.1
            change (Bool.rec (motive := fun _ => Bool) (tst (pos t) l (K + 1 + 1 - t) v (fun y =>
              Bool.rec (motive := fun _ => Bool)
                (Bool.rec (motive := fun _ => Bool)
                  (Bool.rec (motive := fun _ => Bool) _ _ (Nat.beq q.1.2.2.2 3))
                  (nodeOH 0 (fun a c d ka kc => hb q.1.1 (hashFS a.r c.r d ka kc)) (top1bC l m g (K + 1) q.1.2.1 q.1.2.2.1 K t)
                    (pos t) l m g (K + 1 - t - y) v.length z v pairsS)
                  (Nat.beq q.1.2.2.2 0))
                _ (Nat.beq q.1.2.2.2 2))) true (Nat.ble v.length 1) : Bool) = false at hq
            rw [bR, pos_eq, h0, Bool.cond_false] at hq
            have hq' := (hFy _).symm.trans hq
            beta_reduce at hq'
            rw [q.2.2.1, bR, bR] at hq'
            simp only [show Nat.beq 0 2 = false from rfl, show Nat.beq 0 0 = true from rfl,
              Bool.cond_false, Bool.cond_true] at hq'
            exact hq'
          obtain ⟨a', c', ha', hc', ea', ec', z', r, hfn, hst, hmem⟩ := nodeOH_bi_all X a0_symm (α := α)
            (hf := fun q a c d ka kc => hb q.1.1 (hashFS a.r c.r d ka kc))
            (f := fun q => top1bC l m g (K + 1) q.1.2.1 q.1.2.2.1 K t) hs hmin (by omega) rfl rfl
            (NK.sizeB hcard hmin hk hbi hl1.to0 hyk) hbi hl1.to0
            (fun _ _ _ _ _ _ => Nat.zero_le _)
            (fun q w1 w2 hw1 hw2 ew1 ew2 => by
              obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
              obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
              rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb]; exact q.2.2.2)
            (fun q w1 w2 hw1 hw2 ew1 ew2 => by
              obtain rfl := hs.rep.inj hw1 hwa (ew1.trans ewa.symm)
              obtain rfl := hs.rep.inj hw2 hwb (ew2.trans ewb.symm)
              rw [hcod w1 hw1, hcod w2 hw2, ewa, ewb, hashFS_symm hne_R.symm]; exact q.2.2.2)
            (fun w1 w2 hw1 hw2 ew1 ew2 => by
              have hne_xw : mkx (pos' t) l (wst (pos' t) l v) w1 ≠ mkx (pos' t) l (wst (pos' t) l v) w2 := fun e =>
                hbi.1 (by rw [← ew1, ← ew2]; exact congrArg XW.s e)
              have hm1 := fs_mem (List.mem_map_of_mem (f := mkx (pos' t) l (wst (pos' t) l v)) hw1) (by dsimp only [mkx]; rw [hcod w1 hw1, ew1]; exact ha)
              have hm2 := fs_mem (List.mem_map_of_mem (f := mkx (pos' t) l (wst (pos' t) l v)) hw2) (by dsimp only [mkx]; rw [hcod w2 hw2, ew2]; exact hb')
              exact (pairs_dir hm1 hm2 hne_xw).imp (fun f q h xs hp hxs => by subst hxs; exact f h hp)
                (fun f q h xs hp hxs => by subst hxs; exact f h hp))
            hno
          have hwa' : wa = a' := hs.rep.inj hwa ha' (ewa.trans ea'.symm)
          have hwb' : wb = c' := hs.rep.inj hwb hc' (ewb.trans ec'.symm)
          have hgk : gkey a'.r c'.r d = gkey (R a) (R b) d := by rw [← hwa', ← hwb', hcod wa hwa, hcod wb hwb, ewa, ewb]
          simp only [hgk] at hfn
          obtain ⟨hcod1, hmW1⟩ := bi_cod_min (t := t) X hcod hbi (hl1.rel fun _ _ _ _ => trivial) hmW hmem
          exact top1b_sound X hRle hRinj (α := α) (H2 := fun q => q.1.2.1) (H3 := fun q => q.1.2.2.1)
            (fun r2 r3 hr2 hr3 => by
              obtain ⟨p, hpM, hp4, h1, h2, h3⟩ := mFull3_cov hM (Or.inl rfl) (hashFS_lt _ _ _ _ _) hr2 hr3
              have hp0' : p.2.2.2 = 0 := hp4.resolve_left fun h2' => hfast p hpM h2' h1
              exact ⟨⟨p, hpM, hp0', h1⟩, h2, h3⟩)
            hfn hst hcod1 (by omega) ha1 hb1' hlb1 hb1 hl2 hmW1

end sound
def WZ (Z : ℕ) : Set ℕ := {x | ∃ w ∈ I.rawP, x = w &&& mz Z}
def Imp (Z L : ℕ) : Prop := ∀ q < L, ¬ Sol A0 (mz Z) (tz Z) q (C (mz Z) (WZ Z))
def ImpPos (Z L2 : ℕ) : Prop := ∀ q ≤ L2, ¬ SolPos (mz Z) (tz Z) q (C (mz Z) (WZ Z))
lemma Imp.toPos {Z L : ℕ} (h : Imp Z L) : ImpPos Z (L - 1) := by
  intro q hq hsp
  rcases Nat.eq_zero_or_pos L with rfl | _
  · exact (hsp.mono (by omega) subset_rfl).zero_false
  · obtain ⟨k, hk, _, S0, hS0, hl, _⟩ := hsp
    exact h k (by omega) (hl.sol.mono le_rfl hS0)
lemma ImpPos.mono {Z L1 L2 : ℕ} (h : ImpPos Z L2) (hle : L1 ≤ L2) : ImpPos Z L1 := fun q hq => h q (by omega)
def PZ (Q : List (ℕ × ℕ)) : List ℕ := Q.map (fun e => mz e.1)
def pOk (Z : ℕ) (Q : List (ℕ × ℕ)) : Bool := !Nat.beq (tz Z) 0 && !Nat.beq (tz Z) (mz Z) && Q.all (fun e => Nat.beq (Nat.land (mz e.1) (mz Z)) (mz e.1) &&
  !Nat.beq (tz e.1) 0 && !Nat.beq (tz e.1) (mz e.1))
noncomputable def chk (Q : List (ℕ × ℕ)) (Z K t H1 H2 H3 ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B =>
    frc (avl P m I.rawP) (fun v => st l fun l => st m fun m => st g fun g => st B fun B =>
      st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
      anySubC nn (pos t) l v 0 (fun r => startvC nn aa hx hy l m g B K t H1 H2 H3 ph r)))
    (pL (Q.map fun e => 16 + ((bif pos t then K - 1 else K) - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)
noncomputable def chkCore (l m g B K t H1 H2 H3 ph : ℕ) (v : List W) : Bool :=
  frc v (fun v => st l fun l => st m fun m => st g fun g => st B fun B =>
    st I.NN fun nn => st I.AA fun aa => st I.HX fun hx => st I.HY fun hy =>
    anySubC nn (pos t) l v 0 (fun r => startvC nn aa hx hy l m g B K t H1 H2 H3 ph r))
lemma chk_of_core {Z : ℕ} {Q : List (ℕ × ℕ)} {l m g B K t H1 H2 H3 ph : ℕ} {v : List W}
    (hl : lz Z = l) (hm : mz Z = m) (hg : pL (Q.map fun _ => 16) = g)
    (hB : pL (Q.map fun e => 16 + ((bif pos t then K - 1 else K) - e.2)) = B) (hv : avl (PZ Q) (mz Z) I.rawP = v)
    (hc : chkCore l m g B K t H1 H2 H3 ph v = false) : chk Q Z K t H1 H2 H3 ph = false := by
  subst hl hm hg hB hv; exact hc
lemma chk_of_core0 {Z : ℕ} {Q : List (ℕ × ℕ)} {l m g B K H1 H2 H3 ph : ℕ} {v : List W}
    (hl : lz Z = l) (hm : mz Z = m) (hg : pL (Q.map fun _ => 16) = g)
    (hB : pL (Q.map fun e => 16 + (K - e.2)) = B) (hv : avl (PZ Q) (mz Z) I.rawP = v)
    (hc : chkCore l m g B K 0 H1 H2 H3 ph v = false) : chk Q Z K 0 H1 H2 H3 ph = false :=
  chk_of_core hl hm hg (by simpa [pos] using hB) hv hc
lemma chk_of_core_pos {Z : ℕ} {Q : List (ℕ × ℕ)} {l m g B K t H1 H2 H3 ph : ℕ} {v : List W} (ht : 1 ≤ t)
    (hl : lz Z = l) (hm : mz Z = m) (hg : pL (Q.map fun _ => 16) = g)
    (hB : pL (Q.map fun e => 16 + (K - 1 - e.2)) = B) (hv : avl (PZ Q) (mz Z) I.rawP = v)
    (hc : chkCore l m g B K t H1 H2 H3 ph v = false) : chk Q Z K t H1 H2 H3 ph = false := by
  have hpt : pos t = true := by rw [pos_eq]; simp [pos', show 0 < t by omega]
  exact chk_of_core hl hm hg (by simpa [hpt] using hB) hv hc
lemma tz_sub {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') : tz Z &&& mz Z' = tz Z' := by
  simp only [tz, nl, Nat.and_assoc]; rw [Nat.and_comm (mz Z), h]
lemma Im_WZ {Z Z' : ℕ} (h : mz Z' &&& mz Z = mz Z') {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ WZ Z) : Im (mz Z') S ⊆ WZ Z' := by
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
lemma pk16 (Q : List (ℕ × ℕ)) (dK : ℕ) : pL (Q.map fun e => 16 + (dK - e.2)) = pk (PZ Q).length (fun j => 16 + (dK - (Q.getD j (0, dK)).2)) := by
  rw [pL_pk, PZ, List.length_map, List.length_map]
  refine pk_congr fun j hj => ?_
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl
lemma pos_free_of {Q : List (ℕ × ℕ)} {K : ℕ} (h : Q.any (fun x => Nat.ble K x.2) = true) : ∃ e ∈ Q, K ≤ e.2 := by
  obtain ⟨e, he, hb⟩ := List.any_eq_true.1 h
  exact ⟨e, he, Nat.le_of_ble_eq_true hb⟩
theorem imp_of_live0 {Q : List (ℕ × ℕ)} {Z K k : ℕ} {S : Finset ℕ}
    (hp : pOk Z Q = true) (hK : K ≤ 15) (hI : ∀ e ∈ Q, Imp e.1 e.2)
    (hk : k ≤ K) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ Z)) (hl : Live A0 (mz Z) (tz Z) k 0 S)
    (hmin : ∀ q < k, ¬ Sol A0 (mz Z) (tz Z) q (C (mz Z) (WZ Z)))
    (hb : (∃ e ∈ Q, K < e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q Z K 0 p.1 p.2.1 p.2.2.1 p.2.2.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min A0 (mz Z) (tz Z) k 0 S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ Z := by
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
  have hno : ∀ e ∈ Q, ∀ q < e.2, ¬ Sol A0 (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  by_cases hfree : ∃ e ∈ Q, K < e.2
  · obtain ⟨e, he, hgt⟩ := hfree
    have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2)
    exact hno e he q' (by omega) hs'
  push Not at hfree
  rcases hb with ⟨e, he, hgt⟩ | hb
  · exact absurd hgt (Nat.not_lt.2 (hfree e he))
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) I.rawP
  set v := (avl (PZ Q) (mz Z) I.rawP).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) I.rawP) := List.filter_sublist
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
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _ _
  have hcod : ∀ w ∈ v, w.r = rIdx (mz Z) w.s := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); rfl
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (by simp [rawG, rawL, hx]) Z
  have hsubm : ∀ w ∈ v, w.s &&& mz Z = w.s := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw)
    change (x &&& mz Z) &&& mz Z = x &&& mz Z
    rw [Nat.and_assoc, Nat.and_self]
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K)).1 ∧ Q.getD j (0, K) ∈ Q := by
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
  have hcl : Cl (PZ Q) (tz Z) K 0 (fun j => K - (Q.getD j (0, K)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    constructor
    · intro _; have := hfree _ e2; rw [e1]; dsimp only at hq; exact hno _ e2 q (by omega)
    · intro ht; omega
  have hle := cnt_le X hrep hwok hcl hm hk
  have hst : StOk (PZ Q) (tz Z) (lz Z) (mz Z) K 0 (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, hsubm, _, fun j _ => by omega, hcl, ?_⟩
    rw [sumc_eq hwok, pk16, pk_sub]
    intro j hj; have := hle j hj; omega
  have hcov : ∀ i, (lz Z).testBit i = true → (0 : ℕ).testBit i = true ∨ (cov (pos 0) (lz Z) v).testBit i = true := by
    intro i hli
    right
    rw [cov_bit]
    obtain ⟨⟨m1, m2, t1, t2⟩, _⟩ := lz_lg Z i hli
    obtain ⟨w, hw, hs⟩ := hl.cov m1 m2 t1 t2
    obtain ⟨w', hw', rfl⟩ := hrep.mem.1 hw
    exact ⟨w', hw', by rw [sp_bit, hli, pos_eq, hs]; rfl⟩
  have hsz := hm.size.1
  have hcard := hrep.card
  have hble : Nat.ble v.length (Nat.sub (Nat.succ K) 0) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ K + 1 - 0; simp at hsz; omega)
  have hpos0 : pos 0 = false := rfl
  have all : ∀ p ∈ M, top2C (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K p.1 p.2.1 p.2.2.1 p.2.2.2 K 0 (pL (Q.map fun e => 16 + (K - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq, hpos0, Bool.cond_false] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startvC, hble, cond_true] at h3
    exact child_sound X (f := fun z r => top2C (lz Z) (mz Z) _ K p.1 p.2.1 p.2.2.1 p.2.2.2 K 0 z r) (fun h => rfl) hst hm hk h3
  have hrset : {x | rIdx (mz Z) x ≠ 0} = WZ Z := by
    ext x; rw [Set.mem_setOf_eq, rIdx_iff]; exact ⟨fun ⟨w, hw, he⟩ => ⟨w, hw, he.symm⟩, fun ⟨w, hw, he⟩ => ⟨w, hw, he.symm⟩⟩
  refine top2_sound X (rIdx_le (mz Z)) (rIdx_inj (mz Z)) hMf all hst hcod hk hl ?_
  intro q hq hs
  rw [hrset] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

theorem imp_of_live_pos {Q : List (ℕ × ℕ)} {Z K k t : ℕ} {S : Finset ℕ}
    (hp : pOk Z Q = true) (hK : K ≤ 15) (hI : ∀ e ∈ Q, ImpPos e.1 e.2)
    (ht1 : 1 ≤ t) (hk : k ≤ K) (hS : (S : Set ℕ) ⊆ C (mz Z) (WZ Z)) (hl : Live A0 (mz Z) (tz Z) k t S)
    (hmin : ∀ q < k, ¬ Sol A0 (mz Z) (tz Z) q (C (mz Z) (WZ Z)))
    (hb : (∃ e ∈ Q, K ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q Z K t p.1 p.2.1 p.2.2.1 p.2.2.2 = false) : False := by
  simp only [pOk, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true] at hp
  obtain ⟨⟨hp0, hp1⟩, hp2⟩ := hp
  have nb : ∀ {x y : ℕ}, Nat.beq x y = false → x ≠ y := fun h e => by rw [e, Nat.beq_refl] at h; simp at h
  have hT : tz Z &&& mz Z = tz Z := by simp only [tz, nl, Nat.and_assoc, Nat.and_self]
  classical
  have hCS : C (mz Z) (S : Set ℕ) ⊆ C (mz Z) (WZ Z) := by
    rintro x (hx | hx)
    · exact hS hx
    · exact Or.inr hx
  have hm : Min A0 (mz Z) (tz Z) k t S := ⟨hl, fun q' hq' hs => hmin q' hq' (hs.mono le_rfl hCS)⟩
  have htk := hm.size.2
  have hKpos : 1 ≤ K := by omega
  have hbd : ∀ x ∈ S, x &&& mz Z = x := by
    intro x hx
    rcases hS hx with ⟨w, _, rfl⟩ | h
    · rw [Nat.and_assoc, Nat.and_self]
    · simp at h; rcases h with rfl | rfl <;> simp
  obtain ⟨h0, h1⟩ := hm.proper hT (nb hp0) (nb hp1) hbd
  have hSW : (S : Set ℕ) ⊆ WZ Z := by
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
  have hno : ∀ e ∈ Q, ∀ q ≤ e.2, ¬ SolPos (mz e.1) (tz Z &&& mz e.1) q (C (mz e.1) (Im (mz e.1) S)) := by
    intro e he q hq hs
    have h3 := (hproj e he).1
    rw [tz_sub h3] at hs
    exact hI e he q hq (hs.mono le_rfl (C_mono (Im_WZ h3 hSW)))
  by_cases hfree : ∃ e ∈ Q, K ≤ e.2
  · obtain ⟨e, he, hle⟩ := hfree
    have h3 := hproj e he
    obtain ⟨q', hq', hs'⟩ := hm.const_pos h3.1 (by rw [tz_sub h3.1]; exact h3.2.1) (by rw [tz_sub h3.1]; exact h3.2.2) ht1
    exact hno e he q' (by omega) hs'
  push Not at hfree
  rcases hb with ⟨e, he, hle⟩ | hb
  · exact absurd hle (Nat.not_le.2 (hfree e he))
  obtain ⟨M, hMf, hchk⟩ := hb
  obtain ⟨a1, a2, a3⟩ := avl_spec (PZ Q) (mz Z) I.rawP
  set v := (avl (PZ Q) (mz Z) I.rawP).filter (fun w => decide (w.s ∈ S)) with hv
  have hsub : v.Sublist (avl (PZ Q) (mz Z) I.rawP) := List.filter_sublist
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
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); exact mkW_ok _ _ _
  have hcod : ∀ w ∈ v, w.r = rIdx (mz Z) w.s := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw); rfl
  have hgood : ∀ w ∈ v, Good (lz Z) w.s := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := a2 w (hsub.subset hw); exact wire_good (by simp [rawG, rawL, hx]) Z
  have hsubm : ∀ w ∈ v, w.s &&& mz Z = w.s := by
    intro w hw
    obtain ⟨x, _, rfl⟩ := a2 w (hsub.subset hw)
    change (x &&& mz Z) &&& mz Z = x &&& mz Z
    rw [Nat.and_assoc, Nat.and_self]
  have hPlen : (PZ Q).length = Q.length := by simp [PZ]
  have hPget : ∀ j < (PZ Q).length, (PZ Q).getD j 0 = mz (Q.getD j (0, K - 1)).1 ∧ Q.getD j (0, K - 1) ∈ Q := by
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
  have hcl : Cl (PZ Q) (tz Z) K t (fun j => K - 1 - (Q.getD j (0, K - 1)).2) S := by
    intro j hj q hq
    obtain ⟨e1, e2⟩ := hPget j hj
    constructor
    · intro ht0; omega
    · intro _; have := hfree _ e2; rw [e1]; dsimp only at hq; exact hno _ e2 q (by omega)
  have hle := cnt_le X hrep hwok hcl hm hk
  have hst : StOk (PZ Q) (tz Z) (lz Z) (mz Z) K t (pL (Q.map fun e => 16 + (K - 1 - e.2)) - sumc v) v S := by
    refine ⟨hrep, hwok, hgood, hsubm, _, fun j _ => by omega, hcl, ?_⟩
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
  have hble : Nat.ble v.length (Nat.sub (Nat.succ K) t) = true := Nat.ble_eq_true_of_le (by
    change v.length ≤ K + 1 - t; omega)
  have hpost : pos t = true := by rw [pos_eq]; simp [pos', show 0 < t by omega]
  rw [hpost] at hcov
  have all : ∀ p ∈ M, top2C (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K p.1 p.2.1 p.2.2.1 p.2.2.2 K t (pL (Q.map fun e => 16 + (K - 1 - e.2)) - sumc v) v = false := by
    intro p hpM
    have h2 := hchk p hpM
    simp only [chk, frc_eq, st_eq, hpost, Bool.cond_true] at h2
    have h3 := anySub_false (by simp) h2 v hsub hcov
    simp only [startvC, hble, cond_true] at h3
    exact child_sound X (f := fun z r => top2C (lz Z) (mz Z) _ K p.1 p.2.1 p.2.2.1 p.2.2.2 K t z r) (fun h => rfl) hst hm hk h3
  have hrset : {x | rIdx (mz Z) x ≠ 0} = WZ Z := by
    ext x; rw [Set.mem_setOf_eq, rIdx_iff]; exact ⟨fun ⟨w, hw, he⟩ => ⟨w, hw, he.symm⟩, fun ⟨w, hw, he⟩ => ⟨w, hw, he.symm⟩⟩
  refine top2_sound X (rIdx_le (mz Z)) (rIdx_inj (mz Z)) hMf all hst hcod hk hl ?_
  intro q hq hs
  rw [hrset] at hs
  refine hmin q hq (hs.mono le_rfl ?_)
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · exact Or.inl (hSW hx)
  · exact Or.inr hx

theorem imp_of {Q0 Q1 : List (ℕ × ℕ)} {Z L : ℕ}
    (hp0 : pOk Z Q0 = true) (hp1 : pOk Z Q1 = true) (hL : L ≤ 15)
    (hI0 : ∀ e ∈ Q0, Imp e.1 e.2) (hI1 : ∀ e ∈ Q1, ImpPos e.1 e.2)
    (hb0 : (∃ e ∈ Q0, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q0 Z (L - 1) 0 p.1 p.2.1 p.2.2.1 p.2.2.2 = false)
    (hb1 : ∀ t, 1 ≤ t → t < L → (∃ e ∈ Q1, L - 1 ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q1 Z (L - 1) t p.1 p.2.1 p.2.2.1 p.2.2.2 = false) :
    Imp Z L := by
  intro q hq hsol
  classical
  have hex : ∃ q, Sol A0 (mz Z) (tz Z) q (C (mz Z) (WZ Z)) := ⟨q, hsol⟩
  have hqL : Nat.find hex < L := lt_of_le_of_lt (Nat.find_min' hex hsol) hq
  obtain ⟨k, hk, t, S, hS, hl⟩ := (Nat.find_spec hex).live
  have hkL : k ≤ L - 1 := by omega
  have hmin : ∀ q' < k, ¬ Sol A0 (mz Z) (tz Z) q' (C (mz Z) (WZ Z)) := fun q' hq' hs =>
    Nat.find_min hex (by omega) hs
  have htk := hl.t_le_k
  rcases Nat.eq_zero_or_pos t with rfl | ht1
  · refine imp_of_live0 hp0 (by omega) hI0 hkL hS hl hmin ?_
    rcases hb0 with ⟨e, he, hle⟩ | hM
    · exact Or.inl ⟨e, he, by omega⟩
    · exact Or.inr hM
  · exact imp_of_live_pos hp1 (by omega) hI1 ht1 hkL hS hl hmin (hb1 t ht1 (by omega))

theorem impPos_of {Q1 : List (ℕ × ℕ)} {Z L2 : ℕ}
    (hImp : Imp Z L2) (hp1 : pOk Z Q1 = true) (hL : L2 ≤ 15)
    (hI1 : ∀ e ∈ Q1, ImpPos e.1 e.2)
    (hb1 : ∀ t, 1 ≤ t → t ≤ L2 → (∃ e ∈ Q1, L2 ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q1 Z L2 t p.1 p.2.1 p.2.2.1 p.2.2.2 = false) :
    ImpPos Z L2 := by
  intro q hq hsp
  classical
  have hex : ∃ q, SolPos (mz Z) (tz Z) q (C (mz Z) (WZ Z)) := ⟨q, hsp⟩
  have hqL : Nat.find hex ≤ L2 := le_trans (Nat.find_min' hex hsp) hq
  obtain ⟨k, hk, t, S, hS, hl, hc⟩ := Nat.find_spec hex
  have hkL : k ≤ L2 := by omega
  rcases hc with hlt | ht1
  · exact hImp k (by omega) (hl.sol.mono le_rfl hS)
  · have hmin : ∀ q' < k, ¬ Sol A0 (mz Z) (tz Z) q' (C (mz Z) (WZ Z)) := fun q' hq' hs => hImp q' (by omega) hs
    have htk := hl.t_le_k
    exact imp_of_live_pos hp1 hL hI1 ht1 hkL hS hl hmin (hb1 t ht1 (by omega))

theorem ffull : mFull3 [(FF, FF, FF, 2)] = true := by decide +kernel
lemma one3 {Q : List (ℕ × ℕ)} {Z K t : ℕ} (h : chk Q Z K t FF FF FF 2 = false) :
    ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q Z K t p.1 p.2.1 p.2.2.1 p.2.2.2 = false :=
  ⟨[(FF, FF, FF, 2)], ffull, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact h⟩
def PairOk (e : ℕ × ℕ × ℕ) : Prop := Imp e.1 e.2.1 ∧ ImpPos e.1 e.2.2
def pr (T : List (ℕ × ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ × ℕ) :=
  T.filter (fun e => Nat.beq (Nat.land Z e.1) Z && !Nat.beq Z e.1)
def prImp (T : List (ℕ × ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := (pr T Z).map (fun e => (e.1, e.2.1))
def prPos (T : List (ℕ × ℕ × ℕ)) (Z : ℕ) : List (ℕ × ℕ) := (pr T Z).map (fun e => (e.1, e.2.2))
noncomputable def okImp (T : List (ℕ × ℕ × ℕ)) (Z L : ℕ) : Bool :=
  Nat.beq L 0 ||
    (let Q0 := prImp T Z
     let Q1 := prPos T Z
     pOk Z Q0 && pOk Z Q1 && Nat.ble L 15 &&
       ((Q0.any (fun x => Nat.ble L x.2) || !chk Q0 Z (L - 1) 0 FF FF FF 2) &&
         (List.range L).all (fun t => Nat.beq t 0 || Q1.any (fun x => Nat.ble (L - 1) x.2) || !chk Q1 Z (L - 1) t FF FF FF 2)))
noncomputable def okPos (T : List (ℕ × ℕ × ℕ)) (Z L L2 : ℕ) : Bool :=
  Nat.ble L2 L && (Nat.beq L2 0 || Nat.ble (Nat.succ L2) L ||
    (let Q1 := prPos T Z
     pOk Z Q1 && Nat.ble L2 15 &&
       (List.range (Nat.succ L2)).all (fun t => Nat.beq t 0 || Q1.any (fun x => Nat.ble L2 x.2) || !chk Q1 Z L2 t FF FF FF 2)))
noncomputable def okE3 (T : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : Bool :=
  okImp T e.1 e.2.1 && okPos T e.1 e.2.1 e.2.2
lemma imp_okImp {T : List (ℕ × ℕ × ℕ)} {Z L : ℕ} (h : okImp T Z L = true) (hT : ∀ e ∈ T, PairOk e) : Imp Z L := by
  simp only [okImp, Bool.or_eq_true, Nat.beq_eq] at h
  rcases h with rfl | h
  · intro q hq; omega
  · simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨hp0, hp1⟩, hL⟩, hb0, hall⟩ := h
    have hI0 : ∀ e ∈ prImp T Z, Imp e.1 e.2 := by
      intro e he
      simp only [prImp, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      exact (hT e' (List.mem_of_mem_filter he')).1
    have hI1 : ∀ e ∈ prPos T Z, ImpPos e.1 e.2 := by
      intro e he
      simp only [prPos, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      exact (hT e' (List.mem_of_mem_filter he')).2
    refine imp_of hp0 hp1 (Nat.le_of_ble_eq_true hL) hI0 hI1 ?_ ?_
    · simp only [Bool.or_eq_true, Bool.not_eq_true'] at hb0
      rcases hb0 with hfree | hc0
      · exact Or.inl (pos_free_of hfree)
      · exact Or.inr ⟨[(FF, FF, FF, 2)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hc0⟩
    · intro t ht1 htL
      have ht := List.all_eq_true.1 hall t (List.mem_range.2 htL)
      simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at ht
      rcases ht with (rfl | hfree) | hc
      · omega
      · exact Or.inl (pos_free_of hfree)
      · exact Or.inr ⟨[(FF, FF, FF, 2)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hc⟩
lemma imp_okPos {T : List (ℕ × ℕ × ℕ)} {Z L L2 : ℕ} (hImp : Imp Z L) (h : okPos T Z L L2 = true) (hT : ∀ e ∈ T, PairOk e) : ImpPos Z L2 := by
  simp only [okPos, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
  obtain ⟨hle, hb⟩ := h
  rcases hb with (rfl | hlt) | hrun
  · intro q hq hsp; exact (hsp.mono (by omega) subset_rfl).zero_false
  · exact hImp.toPos.mono (by have := Nat.le_of_ble_eq_true hlt; omega)
  · obtain ⟨⟨hp1, hL2⟩, hall⟩ := hrun
    have hI1 : ∀ e ∈ prPos T Z, ImpPos e.1 e.2 := by
      intro e he
      simp only [prPos, List.mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      exact (hT e' (List.mem_of_mem_filter he')).2
    have hImp2 : Imp Z L2 := fun q hq => hImp q (lt_of_lt_of_le hq (Nat.le_of_ble_eq_true hle))
    refine impPos_of hImp2 hp1 (Nat.le_of_ble_eq_true hL2) hI1 fun t ht1 htL => ?_
    have ht := List.all_eq_true.1 hall t (List.mem_range.2 (Nat.lt_succ_of_le htL))
    simp only [Bool.or_eq_true, Nat.beq_eq, Bool.not_eq_true'] at ht
    rcases ht with (rfl | hfree) | hc
    · omega
    · exact Or.inl (pos_free_of hfree)
    · exact Or.inr ⟨[(FF, FF, FF, 2)], ffull, fun p hp => by simp only [List.mem_singleton] at hp; subst hp; exact hc⟩
lemma imp_okE3 {T : List (ℕ × ℕ × ℕ)} {e : ℕ × ℕ × ℕ} (h : okE3 T e = true) (hT : ∀ e' ∈ T, PairOk e') : PairOk e := by
  simp only [okE3, Bool.and_eq_true] at h
  have hi := imp_okImp h.1 hT
  exact ⟨hi, imp_okPos hi h.2 hT⟩
lemma okAll3 {T U : List (ℕ × ℕ × ℕ)} (h : U.all (fun e => okE3 T e) = true)
    (hT : ∀ e ∈ T, PairOk e) : ∀ e ∈ U, PairOk e := fun e he => imp_okE3 (List.all_eq_true.1 h e he) hT
lemma apI3 {A B : List (ℕ × ℕ × ℕ)} (ha : ∀ e ∈ A, PairOk e) (hb : ∀ e ∈ B, PairOk e) : ∀ e ∈ A ++ B, PairOk e := fun e he =>
  (List.mem_append.1 he).elim (ha e) (hb e)
lemma subI3 {A B : List (ℕ × ℕ × ℕ)} (h : B.all (fun e => A.any (fun a => Nat.beq a.1 e.1 && Nat.beq a.2.1 e.2.1 && Nat.beq a.2.2 e.2.2)) = true)
    (hA : ∀ e ∈ A, PairOk e) : ∀ e ∈ B, PairOk e := by
  intro e he
  have h1 := List.all_eq_true.1 h e he
  obtain ⟨a, ha, h2⟩ := List.any_eq_true.1 h1
  simp only [Bool.and_eq_true, Nat.beq_eq] at h2
  have heq : a = e := Prod.ext h2.1.1 (Prod.ext h2.1.2 h2.2)
  exact heq ▸ hA a ha
lemma subI2_imp {A : List (ℕ × ℕ × ℕ)} {B : List (ℕ × ℕ)} (h : B.all (fun e => A.any (fun a => Nat.beq a.1 e.1 && Nat.beq a.2.1 e.2)) = true)
    (hA : ∀ e ∈ A, PairOk e) : ∀ e ∈ B, Imp e.1 e.2 := by
  intro e he
  obtain ⟨a, ha, h2⟩ := List.any_eq_true.1 (List.all_eq_true.1 h e he)
  simp only [Bool.and_eq_true, Nat.beq_eq] at h2
  have h1 := (hA a ha).1
  rw [h2.1, h2.2] at h1; exact h1
lemma subI2_pos {A : List (ℕ × ℕ × ℕ)} {B : List (ℕ × ℕ)} (h : B.all (fun e => A.any (fun a => Nat.beq a.1 e.1 && Nat.beq a.2.2 e.2)) = true)
    (hA : ∀ e ∈ A, PairOk e) : ∀ e ∈ B, ImpPos e.1 e.2 := by
  intro e he
  obtain ⟨a, ha, h2⟩ := List.any_eq_true.1 (List.all_eq_true.1 h e he)
  simp only [Bool.and_eq_true, Nat.beq_eq] at h2
  have h2' := (hA a ha).2
  rw [h2.1, h2.2] at h2'; exact h2'
lemma imp_ts {Q0 Q1 : List (ℕ × ℕ)} {L : ℕ}
    (hp0 : pOk 0 Q0 = true) (hp1 : pOk 0 Q1 = true) (hL : L ≤ 15)
    (hI0 : ∀ e ∈ Q0, Imp e.1 e.2) (hI1 : ∀ e ∈ Q1, ImpPos e.1 e.2)
    (h0 : (∃ e ∈ Q0, L ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q0 0 (L - 1) 0 p.1 p.2.1 p.2.2.1 p.2.2.2 = false)
    (h1 : ∀ t, 1 ≤ t → t < L → (∃ e ∈ Q1, L - 1 ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk Q1 0 (L - 1) t p.1 p.2.1 p.2.2.1 p.2.2.2 = false) :
    Imp 0 L :=
  imp_of hp0 hp1 hL hI0 hI1 h0 h1

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
    (∃ i, (ex m gs w).getD i 0 = T) → Sol A0 m T gs.length S := by
  induction gs with
  | nil =>
    rintro w S hw h0 _ _ ⟨i, rfl⟩
    exact .done (getD_mem hw h0 i)
  | cons g gs ih =>
    intro w S hw h0 hm hg hT
    have hgs := fun x hx => hg x (List.mem_cons_of_mem _ hx)
    have rd := fun i => getD_mem hw h0 i
    have stay : gv m w g ∈ S → Sol A0 m T (g :: gs).length S := fun h =>
      (ih (w ++ [gv m w g]) S (fun x hx => by
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact hw x hx
        · exact h) h0 hm hgs hT).mono (by simp) subset_rfl
    have go : Sol A0 m T gs.length (insert (gv m w g) S) := ih (w ++ [gv m w g]) _ (fun x hx => by
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
      | i :: j :: _ => exact .bi (d := false) (rd i) (rd j) (a0_all _ _ _) go
    · match l with
      | [] => exact stay h0
      | [i] => exact stay (rd i)
      | i :: j :: _ => exact .bi (d := true) (rd i) (rd j) (a0_all _ _ _) go
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
    Sol A0 m T (gs.length - 1) S ∨ ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ S ∧ Live A0 m T gs.length t S0 := by
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
        · exact Or.inl ((Sol.bi (d := false) (rd i) (rd j) (a0_all _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op false (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op false (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (a0_all _ _ _) (by rwa [Finset.insert_erase hz])⟩
              intro x hx; simp at hx; rcases hx with rfl | rfl | ⟨h1, h2⟩; exact rd i; exact rd j; exact (hS1 h1).resolve_left h2
          · exact Or.inl (hl1.sol.mono le_rfl (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))
    · have hnot' : ∃ g' ∈ gs, g'.op = GateOp.not := by
        rcases hnot with ⟨g', hg', ho⟩; simp only [List.mem_cons] at hg'; rcases hg' with rfl | hg'; simp at ho; exact ⟨g', hg', ho⟩
      match l with
      | [] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, []⟩]) S (hwm_stay h0) h0 hm hgs hT)
      | [i] => exact Or.inl (ex_sol m gs (w ++ [gv m w ⟨.or, [i]⟩]) S (hwm_stay (rd i)) h0 hm hgs hT)
      | i :: j :: _ =>
        rcases ih (w ++ [gv m w ⟨.or, i :: j :: _⟩]) (insert (op true (w.getD i 0) (w.getD j 0)) S) hwm_ins (Or.inr h0) (Or.inr hm) hgs hnot' hT with hs | ⟨t, ht, S1, hS1, hl1⟩
        · exact Or.inl ((Sol.bi (d := true) (rd i) (rd j) (a0_all _ _ _) hs).mono (by cases gs <;> simp at hnot' ⊢) subset_rfl)
        · by_cases hz : op true (w.getD i 0) (w.getD j 0) ∈ S1
          · by_cases hab : w.getD i 0 = w.getD j 0
            · have hsub : (S1 : Set ℕ) ⊆ S := fun x hx => (hS1 hx).elim (fun e => by subst e; rw [hab, op_self]; exact rd j) id
              exact Or.inl (hl1.sol.mono le_rfl hsub)
            · refine Or.inr ⟨t, ht, insert (w.getD i 0) (insert (w.getD j 0) (S1.erase (op true (w.getD i 0) (w.getD j 0)))), ?_, Live.bi hab (a0_all _ _ _) (by rwa [Finset.insert_erase hz])⟩
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
          have hlu : Live A0 m T (k + 1) (t + 1) (insert (w.getD i 0) (S1.erase (w.getD i 0 ^^^ m))) := Live.un (by rwa [Finset.insert_erase hz])
          by_cases hkeq : k = gs.length
          · subst hkeq; exact Or.inr ⟨t + 1, by omega, _, hsub, hlu⟩
          · exact Or.inl (hlu.sol.mono (by simp; omega) hsub)
        · exact Or.inl (hl1.sol.mono (by simp; omega) (fun x hx => (hS1 hx).resolve_left (fun e => hz (e ▸ hx))))

section inst_data
def rtL0_0 : List (ℕ × ℕ × ℕ) := [(1664, 2, 2), (2240, 2, 2), (2624, 2, 2), (2816, 2, 2), (3200, 2, 2), (3328, 2, 2), (3584, 2, 2), (385, 2, 2), (641, 1, 0), (769, 1, 0), (1153, 2, 2), (1281, 1, 0), (1537, 2, 2), (2177, 1, 0), (2305, 2, 2), (2561, 2, 2), (3073, 4, 4), (322, 2, 2), (578, 1, 0), (770, 1, 0), (1282, 1, 0), (1538, 1, 0), (2114, 1, 0), (2306, 2, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL0_0 : rtL0_0.all (fun e => okE3 ([]) e) = true := by decide +kernel
lemma iL0_0 : ∀ e ∈ rtL0_0, PairOk e := okAll3 rL0_0 (by simp)
def rtL0_1 : List (ℕ × ℕ × ℕ) := [(2562, 4, 4), (3074, 2, 2), (259, 1, 0), (515, 1, 0), (1027, 1, 0), (2051, 2, 2), (196, 1, 0), (580, 1, 0), (644, 1, 0), (1156, 2, 2), (1540, 2, 2), (2116, 2, 2), (2180, 2, 2), (2564, 2, 2), (3076, 2, 2), (133, 1, 0), (517, 1, 0), (1029, 2, 2), (2053, 1, 0), (518, 1, 0), (2054, 1, 0), (200, 1, 0), (328, 2, 2), (392, 2, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL0_1 : rtL0_1.all (fun e => okE3 ([]) e) = true := by decide +kernel
lemma iL0_1 : ∀ e ∈ rtL0_1, PairOk e := okAll3 rL0_1 (by simp)
def rtL0_2 : List (ℕ × ℕ × ℕ) := [(1160, 1, 0), (1288, 1, 0), (2120, 1, 0), (2184, 2, 2), (2312, 1, 0), (3080, 2, 2), (137, 2, 2), (265, 2, 2), (1033, 1, 0), (2057, 1, 0), (74, 2, 2), (266, 2, 2), (2058, 2, 2), (140, 1, 0), (2060, 1, 0), (14, 1, 0), (208, 1, 0), (336, 2, 2), (400, 2, 2), (592, 1, 0), (656, 2, 2), (784, 1, 0), (2128, 2, 2), (2192, 1, 0)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL0_2 : rtL0_2.all (fun e => okE3 ([]) e) = true := by decide +kernel
lemma iL0_2 : ∀ e ∈ rtL0_2, PairOk e := okAll3 rL0_2 (by simp)
def rtL0_3 : List (ℕ × ℕ × ℕ) := [(2320, 1, 0), (2576, 2, 2), (145, 4, 4), (273, 2, 2), (529, 2, 2), (2065, 2, 2), (82, 2, 2), (274, 2, 2), (530, 1, 0), (2066, 1, 0), (84, 1, 0), (148, 2, 2), (532, 2, 2), (2068, 1, 0), (21, 2, 2), (88, 2, 2), (152, 2, 2), (280, 4, 4), (2072, 2, 2), (25, 2, 2), (26, 2, 2), (224, 2, 2), (352, 2, 2), (416, 2, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL0_3 : rtL0_3.all (fun e => okE3 ([]) e) = true := by decide +kernel
lemma iL0_3 : ∀ e ∈ rtL0_3, PairOk e := okAll3 rL0_3 (by simp)
def rtL0_4 : List (ℕ × ℕ × ℕ) := [(608, 2, 2), (672, 1, 0), (800, 2, 2), (1184, 1, 0), (1312, 2, 2), (1568, 1, 0), (161, 2, 2), (289, 4, 4), (545, 2, 2), (1057, 2, 2), (98, 2, 2), (290, 4, 4), (546, 4, 4), (1058, 2, 2), (35, 2, 2), (100, 2, 2), (164, 2, 2), (548, 2, 2), (38, 1, 0), (104, 2, 2), (168, 4, 4), (296, 4, 4), (1064, 2, 2), (41, 2, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL0_4 : rtL0_4.all (fun e => okE3 ([]) e) = true := by decide +kernel
lemma iL0_4 : ∀ e ∈ rtL0_4, PairOk e := okAll3 rL0_4 (by simp)
def rtL0_5 : List (ℕ × ℕ × ℕ) := [(42, 1, 0), (44, 1, 0), (112, 4, 4), (176, 4, 4), (304, 4, 4), (560, 4, 4), (49, 2, 2), (50, 2, 2), (52, 2, 2), (56, 2, 2)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL0_5 : rtL0_5.all (fun e => okE3 ([]) e) = true := by decide +kernel
lemma iL0_5 : ∀ e ∈ rtL0_5, PairOk e := okAll3 rL0_5 (by simp)
def rtAcc0 : List (ℕ × ℕ × ℕ) := (((((rtL0_0 ++ rtL0_1) ++ rtL0_2) ++ rtL0_3) ++ rtL0_4) ++ rtL0_5)
lemma irAcc0 : ∀ e ∈ rtAcc0, PairOk e := (apI3 (apI3 (apI3 (apI3 (apI3 iL0_0 iL0_1) iL0_2) iL0_3) iL0_4) iL0_5)
def rtL1_0 : List (ℕ × ℕ × ℕ) := [(320, 3, 3), (384, 3, 3), (1152, 3, 3), (1536, 3, 3), (2112, 3, 3), (2176, 3, 3), (2304, 3, 3), (2560, 5, 5), (3072, 5, 5), (129, 5, 5), (257, 5, 5), (513, 4, 4), (1025, 5, 5), (2049, 5, 5), (66, 3, 3), (258, 5, 5), (2050, 5, 5), (132, 4, 4), (516, 4, 4), (2052, 3, 3), (72, 3, 3), (136, 5, 5), (264, 5, 5), (2056, 4, 4)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL1_0 : rtL1_0.all (fun e => okE3 (rtAcc0) e) = true := by decide +kernel
lemma iL1_0 : ∀ e ∈ rtL1_0, PairOk e := okAll3 rL1_0 irAcc0
def rtL1_1 : List (ℕ × ℕ × ℕ) := [(9, 3, 3), (10, 3, 3), (80, 5, 5), (144, 5, 5), (272, 5, 5), (528, 5, 5), (2064, 4, 4), (17, 5, 5), (18, 3, 3), (20, 3, 3), (24, 5, 5), (96, 5, 5), (160, 5, 5), (288, 7, 7), (544, 5, 5), (1056, 3, 3), (33, 5, 5), (34, 5, 5), (36, 3, 3), (40, 5, 5), (48, 7, 7)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL1_1 : rtL1_1.all (fun e => okE3 (rtAcc0) e) = true := by decide +kernel
lemma iL1_1 : ∀ e ∈ rtL1_1, PairOk e := okAll3 rL1_1 irAcc0
def rtAcc1 : List (ℕ × ℕ × ℕ) := rtAcc0 ++ (rtL1_0 ++ rtL1_1)
lemma irAcc1 : ∀ e ∈ rtAcc1, PairOk e := apI3 irAcc0 (apI3 iL1_0 iL1_1)
def rtL2_0 : List (ℕ × ℕ × ℕ) := [(64, 6, 6), (128, 7, 7), (256, 8, 8), (512, 7, 7), (2048, 8, 8), (1, 8, 8), (2, 7, 7), (8, 7, 7), (16, 9, 9), (32, 8, 8)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rL2_0 : rtL2_0.all (fun e => okE3 (rtAcc1) e) = true := by decide +kernel
lemma iL2_0 : ∀ e ∈ rtL2_0, PairOk e := okAll3 rL2_0 irAcc1
def rtAcc2 : List (ℕ × ℕ × ℕ) := rtAcc1 ++ rtL2_0
lemma irAcc2 : ∀ e ∈ rtAcc2, PairOk e := apI3 irAcc1 iL2_0
def rt : List (ℕ × ℕ × ℕ) := rtAcc2
lemma ir : ∀ e ∈ rt, PairOk e := irAcc2
def rtRoot3 : List (ℕ × ℕ × ℕ) := [(16, 9, 9), (1, 8, 8), (32, 8, 8), (256, 8, 8), (2048, 8, 8), (48, 7, 7), (288, 7, 7), (2, 7, 7), (8, 7, 7), (128, 7, 7), (512, 7, 7), (64, 6, 6)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rtRoot3_sub : rtRoot3.all (fun e => rt.any (fun a => Nat.beq a.1 e.1 && Nat.beq a.2.1 e.2.1 && Nat.beq a.2.2 e.2.2)) = true := by decide +kernel
lemma irRoot3 : ∀ e ∈ rtRoot3, PairOk e := subI3 rtRoot3_sub ir
def rtRootImp : List (ℕ × ℕ) := rtRoot3.map (fun e => (e.1, e.2.1))
def rtRootPos : List (ℕ × ℕ) := rtRoot3.map (fun e => (e.1, e.2.2))
lemma irRootImp : ∀ e ∈ rtRootImp, Imp e.1 e.2 := by
  intro e he; simp only [rtRootImp, List.mem_map] at he; obtain ⟨a, ha, rfl⟩ := he; exact (irRoot3 a ha).1
lemma irRootPos : ∀ e ∈ rtRootPos, ImpPos e.1 e.2 := by
  intro e he; simp only [rtRootPos, List.mem_map] at he; obtain ⟨a, ha, rfl⟩ := he; exact (irRoot3 a ha).2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_p0 : pOk 0 rtRootImp = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem root_p1 : pOk 0 rtRootPos = true := by decide +kernel
def rootL0 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3efe) 64) 0xfdff7f6ff6dfeddb) 64) 0xbbbdf7776db6dff7) 64) 0xf7f7f6fdb77df7ef) 64) 0x0
def rootM0 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f7f7eff) 64) 0xbfb7fb6ff6edddde) 64) 0xfbbbb6db6ffbfbfb) 64) 0xfb7edbbefbf78000) 64) 0x3efe) 64) 0xfdff7f6ff6dfeddb) 64) 0xbbbdf7776db6dff7) 64) 0xf7f7f6fdb77df7ef) 64) 0xffffffffffffffff
def rootG0 : Nat := 0x842108421084210
def rootBr0 : Nat := 0xad294a52939ce72
def rootBr1 : Nat := 0xa4e739ce7294a51
def rootBp : Nat := 0xad294a52939ce72
def rW_0 : W := ⟨Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f7f7eff) 64) 0xbfb7fb6000000000) 64) 0x3b36db6fe3f3f3) 64) 0x80600020c3040000) 64) 0x3cf8) 64) 0xf9f87c6fc6d80000) 64) 0x202100776db6dff7) 64) 0xf7f0000000000000) 64) 0xffffffff00000000, 0x42000400, 0x100000, 0x42100400, 6⟩
def rW_1 : W := ⟨Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f7f7e00) 64) 0xff6ec0000) 64) 0x33a6900c130203) 64) 0x727c921000800000) 64) 0x3ae6) 64) 0xe504400800978dda) 64) 0x210c4776db00000) 64) 0x7f6fdb7000000) 64) 0xffff0000ffff0000, 0x2000001, 0, 0x2000001, 5⟩
def rW_2 : W := ⟨Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x1f0000ff) 64) 0xbf80000ff601ddc0) 64) 0x2ab0034b988182) 64) 0xeb10003cf2e00000) 64) 0x3e84) 64) 0x91e77b06241f6d03) 64) 0xbb8822776006dff0) 64) 0x7f600007df7e0) 64) 0xff00ff00ff00ff00, 0x10000000000, 0x4000000000000, 0x4010000000000, 4⟩
def rW_3 : W := ⟨Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x7f00ff) 64) 0x8030000000e1c01e) 64) 0xf81804020202cb49) 64) 0x984ac12aa8030000) 64) 0x22fe) 64) 0x4ddf2661d246c9d3) 64) 0x913db1700c060007) 64) 0xf7f7f0fd807df00f) 64) 0xf0f0f0f0f0f0f0f0, 0, 0x40008000, 0x40008000, 3⟩
def rW_4 : W := ⟨Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x7e00) 64) 0x7fb0ff00c1c1e) 64) 0x38182c024793820) 64) 0x4036181601d68000) 64) 0x1452) 64) 0xfcb2194fb61de099) 64) 0x38bc17070d80dff7) 64) 0xf00000fc307c07ef) 64) 0xcccccccccccccccc, 0x800000000, 0x200000000000, 0x200800000000, 2⟩
def rW_5 : W := ⟨Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3f87f860000001c0) 64) 0xfb801049614020b8) 64) 0x10049805b358000) 64) 0x828) 64) 0x2049772d70c12448) 64) 0x8b85f70061b6c000) 64) 0x7f00601b701f7ef) 64) 0xaaaaaaaaaaaaaaaa, 0x20, 0x80000000000000, 0x80000000000020, 1⟩
def rootV0 : List W := [rW_0, rW_1, rW_2, rW_3, rW_4, rW_5]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootL0_eq : lz 0 = rootL0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootM0_eq : mz 0 = rootM0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootG0_imp_eq : pL (rtRootImp.map fun _ => 16) = rootG0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootG0_pos_eq : pL (rtRootPos.map fun _ => 16) = rootG0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBr0_eq : pL (rtRootImp.map fun e => 16 + (11 - e.2)) = rootBr0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBr1_eq : pL (rtRootPos.map fun e => 16 + (11 - 1 - e.2)) = rootBr1 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootBp_eq : pL (rtRootPos.map fun e => 16 + (12 - 1 - e.2)) = rootBp := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootV0_imp_eq : avl (PZ rtRootImp) (mz 0) I.rawP = rootV0 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rootV0_pos_eq : avl (PZ rtRootPos) (mz 0) I.rawP = rootV0 := by decide +kernel
def hM_0 : Nat := Nat.lor (Nat.shiftLeft (0x800000) 64) 0x8080008888088888
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_zr_0_0 : chkCore rootL0 rootM0 rootG0 rootBr0 11 0 hM_0 FF FF 0 rootV0 = false := by decide +kernel
def hM_1 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xffffffffffffffff) 64) 0xffffffffff7fffff) 64) 0x7f7fff7777f77777
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_zr_0_1 : chkCore rootL0 rootM0 rootG0 rootBr0 11 0 hM_1 FF FF 0 rootV0 = false := by decide +kernel
def hM_2 : Nat := Nat.lor (Nat.shiftLeft (0x800000808000) 64) 0x8080088888080880
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_zr_0_2 : chkCore rootL0 rootM0 rootG0 rootBr0 11 0 hM_2 FF FF 3 rootV0 = false := by decide +kernel
def hM_3 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xffffffffffffffff) 64) 0xffff7fffff7f7fff) 64) 0x7f7ff77777f7f77f
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_zr_0_3 : chkCore rootL0 rootM0 rootG0 rootBr0 11 0 hM_3 FF FF 3 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_zr_0_4 : chkCore rootL0 rootM0 rootG0 rootBr0 11 0 FF FF FF 1 rootV0 = false := by decide +kernel
def sp_zr_0_Parts : List (ℕ × ℕ × ℕ × ℕ) := [(hM_0, FF, FF, 0), (hM_1, FF, FF, 0), (hM_2, FF, FF, 3), (hM_3, FF, FF, 3), (FF, FF, FF, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_zr_0_Full : mFull3 sp_zr_0_Parts = true := by decide +kernel
lemma sp_zr_0_One : ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk rtRootImp 0 11 0 p.1 p.2.1 p.2.2.1 p.2.2.2 = false := by
  refine ⟨sp_zr_0_Parts, sp_zr_0_Full, ?_⟩
  intro p hp
  simp only [sp_zr_0_Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact chk_of_core0 rootL0_eq rootM0_eq rootG0_imp_eq rootBr0_eq rootV0_imp_eq sp_zr_0_0
  · exact chk_of_core0 rootL0_eq rootM0_eq rootG0_imp_eq rootBr0_eq rootV0_imp_eq sp_zr_0_1
  · exact chk_of_core0 rootL0_eq rootM0_eq rootG0_imp_eq rootBr0_eq rootV0_imp_eq sp_zr_0_2
  · exact chk_of_core0 rootL0_eq rootM0_eq rootG0_imp_eq rootBr0_eq rootV0_imp_eq sp_zr_0_3
  · exact chk_of_core0 rootL0_eq rootM0_eq rootG0_imp_eq rootBr0_eq rootV0_imp_eq sp_zr_0_4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_1 : chkCore rootL0 rootM0 rootG0 rootBr1 11 1 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_2 : chkCore rootL0 rootM0 rootG0 rootBr1 11 2 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_3 : chkCore rootL0 rootM0 rootG0 rootBr1 11 3 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_4 : chkCore rootL0 rootM0 rootG0 rootBr1 11 4 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_5 : chkCore rootL0 rootM0 rootG0 rootBr1 11 5 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_6 : chkCore rootL0 rootM0 rootG0 rootBr1 11 6 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_7 : chkCore rootL0 rootM0 rootG0 rootBr1 11 7 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_8 : chkCore rootL0 rootM0 rootG0 rootBr1 11 8 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_9 : chkCore rootL0 rootM0 rootG0 rootBr1 11 9 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_10 : chkCore rootL0 rootM0 rootG0 rootBr1 11 10 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem zr_11 : chkCore rootL0 rootM0 rootG0 rootBr1 11 11 FF FF FF 2 rootV0 = false := by decide +kernel
lemma iroot : Imp 0 12 := imp_ts root_p0 root_p1 (by norm_num) irRootImp irRootPos (Or.inr sp_zr_0_One) (fun t ht1 htL => by
  interval_cases t
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_1))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_2))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_3))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_4))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_5))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_6))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_7))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_8))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_9))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_10))
  · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBr1_eq rootV0_pos_eq zr_11))
)
def hM_4 : Nat := 0x800000008
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_0 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_4 FF FF 0 rootV0 = false := by decide +kernel
def hM_5 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xffffffffffffffff) 64) 0xff7f77ff7f77f77f) 64) 0x77f7777777f777f7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_1 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_5 FF FF 0 rootV0 = false := by decide +kernel
def hM_6 : Nat := Nat.lor (Nat.shiftLeft (0x80000880) 64) 0x800000088000800
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_2 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_6 FF FF 0 rootV0 = false := by decide +kernel
def hM_7 : Nat := Nat.lor (Nat.shiftLeft (0x80880000880000) 64) 0x8008888000088000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_3 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_7 FF FF 0 rootV0 = false := by decide +kernel
def hM_8 : Nat := Nat.shiftLeft 1 35
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_4 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_8 FF FF 3 rootV0 = false := by decide +kernel
def hM_9 : Nat := Nat.lor (Nat.shiftLeft (0x80000000000000) 64) 0x80000000000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_5 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_9 FF FF 3 rootV0 = false := by decide +kernel
def hM_10 : Nat := Nat.lor (Nat.shiftLeft (0x8000000) 64) 0x80000000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_6 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_10 FF FF 3 rootV0 = false := by decide +kernel
def hM_11 : Nat := Nat.lor (Nat.shiftLeft (0x80000) 64) 0x80
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_7 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_11 FF FF 3 rootV0 = false := by decide +kernel
def hM_12 : Nat := 0x80800
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_8 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_12 FF FF 3 rootV0 = false := by decide +kernel
def hM_13 : Nat := 0x8000000008000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_9 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_13 FF FF 3 rootV0 = false := by decide +kernel
def hM_14 : Nat := Nat.lor (Nat.shiftLeft (0x8000) 64) 0x800000000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_10 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_14 FF FF 3 rootV0 = false := by decide +kernel
def hM_15 : Nat := Nat.lor (Nat.shiftLeft (0x800000) 64) 0x80000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_11 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_15 FF FF 3 rootV0 = false := by decide +kernel
def hM_16 : Nat := 0x8000000008
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_12 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_16 FF FF 3 rootV0 = false := by decide +kernel
def hM_17 : Nat := Nat.lor (Nat.shiftLeft (0x880000000000) 64) 0x808000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_13 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_17 FF FF 3 rootV0 = false := by decide +kernel
def hM_18 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xffffffffffffffff) 64) 0xff7f77fff7777fff) 64) 0x7f7f777777777777
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_14 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_18 FF FF 3 rootV0 = false := by decide +kernel
def hM_19 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x100000000) 64) 0x100000) 64) 0x300
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_15 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_19 FF FF 1 rootV0 = false := by decide +kernel
def hM_20 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xfffffffcffffffff) 64) 0xdfffffffffcfffff) 64) 0xfffffff7fffffcff
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_16 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_20 FF FF 1 rootV0 = false := by decide +kernel
def hM_21 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x200000000) 64) 0x200000) 64) 0x0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_17 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_21 FF FF 1 rootV0 = false := by decide +kernel
def hM_22 : Nat := Nat.lor (Nat.shiftLeft (0x2000000000000000) 64) 0x800000000
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_18 : chkCore rootL0 rootM0 rootG0 rootBp 12 1 hM_22 FF FF 1 rootV0 = false := by decide +kernel
def sp_pr_1_Parts : List (ℕ × ℕ × ℕ × ℕ) := [(hM_4, FF, FF, 0), (hM_5, FF, FF, 0), (hM_6, FF, FF, 0), (hM_7, FF, FF, 0), (hM_8, FF, FF, 3), (hM_9, FF, FF, 3), (hM_10, FF, FF, 3), (hM_11, FF, FF, 3), (hM_12, FF, FF, 3), (hM_13, FF, FF, 3), (hM_14, FF, FF, 3), (hM_15, FF, FF, 3), (hM_16, FF, FF, 3), (hM_17, FF, FF, 3), (hM_18, FF, FF, 3), (hM_19, FF, FF, 1), (hM_20, FF, FF, 1), (hM_21, FF, FF, 1), (hM_22, FF, FF, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_1_Full : mFull3 sp_pr_1_Parts = true := by decide +kernel
lemma sp_pr_1_One : ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk rtRootPos 0 12 1 p.1 p.2.1 p.2.2.1 p.2.2.2 = false := by
  refine ⟨sp_pr_1_Parts, sp_pr_1_Full, ?_⟩
  intro p hp
  simp only [sp_pr_1_Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_0
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_1
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_2
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_3
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_4
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_5
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_6
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_7
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_8
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_9
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_10
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_11
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_12
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_13
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_14
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_15
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_16
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_17
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_1_18
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_0 : chkCore rootL0 rootM0 rootG0 rootBp 12 2 FF FF FF 0 rootV0 = false := by decide +kernel
def hM_23 : Nat := 0x80080800000080
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_1 : chkCore rootL0 rootM0 rootG0 rootBp 12 2 hM_23 FF FF 3 rootV0 = false := by decide +kernel
def hM_24 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xffffffffffffffff) 64) 0xff7f77777777ff77) 64) 0xff7777f7f77f7777
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_2 : chkCore rootL0 rootM0 rootG0 rootBp 12 2 hM_24 FF FF 3 rootV0 = false := by decide +kernel
def hM_25 : Nat := Nat.lor (Nat.shiftLeft (0x80888888880088) 64) 0x8800008808808
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_3 : chkCore rootL0 rootM0 rootG0 rootBp 12 2 hM_25 FF FF 3 rootV0 = false := by decide +kernel
def hM_26 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x2000000200000000) 64) 0x0) 64) 0x800000200
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_4 : chkCore rootL0 rootM0 rootG0 rootBp 12 2 hM_26 FF FF 1 rootV0 = false := by decide +kernel
def hM_27 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xdffffffdffffffff) 64) 0xffffffffffffffff) 64) 0xfffffff7fffffdff
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_5 : chkCore rootL0 rootM0 rootG0 rootBp 12 2 hM_27 FF FF 1 rootV0 = false := by decide +kernel
def sp_pr_2_Parts : List (ℕ × ℕ × ℕ × ℕ) := [(FF, FF, FF, 0), (hM_23, FF, FF, 3), (hM_24, FF, FF, 3), (hM_25, FF, FF, 3), (hM_26, FF, FF, 1), (hM_27, FF, FF, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_2_Full : mFull3 sp_pr_2_Parts = true := by decide +kernel
lemma sp_pr_2_One : ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk rtRootPos 0 12 2 p.1 p.2.1 p.2.2.1 p.2.2.2 = false := by
  refine ⟨sp_pr_2_Parts, sp_pr_2_Full, ?_⟩
  intro p hp
  simp only [sp_pr_2_Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_2_0
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_2_1
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_2_2
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_2_3
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_2_4
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_2_5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_3_0 : chkCore rootL0 rootM0 rootG0 rootBp 12 3 FF FF FF 0 rootV0 = false := by decide +kernel
def hM_28 : Nat := Nat.lor (Nat.shiftLeft (0x8000) 64) 0x8080888888888088
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_3_1 : chkCore rootL0 rootM0 rootG0 rootBp 12 3 hM_28 FF FF 3 rootV0 = false := by decide +kernel
def hM_29 : Nat := Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (Nat.lor (Nat.shiftLeft (0x3fffff) 64) 0xffffffffffffffff) 64) 0xffffffffffff7fff) 64) 0x7f7f777777777f77
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_3_2 : chkCore rootL0 rootM0 rootG0 rootBp 12 3 hM_29 FF FF 3 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_3_3 : chkCore rootL0 rootM0 rootG0 rootBp 12 3 FF FF FF 1 rootV0 = false := by decide +kernel
def sp_pr_3_Parts : List (ℕ × ℕ × ℕ × ℕ) := [(FF, FF, FF, 0), (hM_28, FF, FF, 3), (hM_29, FF, FF, 3), (FF, FF, FF, 1)]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sp_pr_3_Full : mFull3 sp_pr_3_Parts = true := by decide +kernel
lemma sp_pr_3_One : ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk rtRootPos 0 12 3 p.1 p.2.1 p.2.2.1 p.2.2.2 = false := by
  refine ⟨sp_pr_3_Parts, sp_pr_3_Full, ?_⟩
  intro p hp
  simp only [sp_pr_3_Parts, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_3_0
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_3_1
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_3_2
  · exact chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq sp_pr_3_3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_4 : chkCore rootL0 rootM0 rootG0 rootBp 12 4 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_5 : chkCore rootL0 rootM0 rootG0 rootBp 12 5 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_6 : chkCore rootL0 rootM0 rootG0 rootBp 12 6 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_7 : chkCore rootL0 rootM0 rootG0 rootBp 12 7 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_8 : chkCore rootL0 rootM0 rootG0 rootBp 12 8 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_9 : chkCore rootL0 rootM0 rootG0 rootBp 12 9 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_10 : chkCore rootL0 rootM0 rootG0 rootBp 12 10 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_11 : chkCore rootL0 rootM0 rootG0 rootBp 12 11 FF FF FF 2 rootV0 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pr_12 : chkCore rootL0 rootM0 rootG0 rootBp 12 12 FF FF FF 2 rootV0 = false := by decide +kernel
lemma iroot_pos {t : ℕ} {S : Finset ℕ} (ht1 : 1 ≤ t) (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ 0))
    (hl : Live A0 (mz 0) (tz 0) 12 t S) : False := by
  have hmin : ∀ q < 12, ¬ Sol A0 (mz 0) (tz 0) q (C (mz 0) (WZ 0)) := fun q hq => iroot q hq
  have hm0 : Min A0 (mz 0) (tz 0) 12 t S := ⟨hl, fun q hq hs => hmin q hq (hs.mono le_rfl (by rintro x (hx | hx); exact hS hx; exact Or.inr hx))⟩
  have htk : t ≤ 12 := hm0.size.2
  have hM : (∃ e ∈ rtRootPos, 12 ≤ e.2) ∨ ∃ M : List (ℕ × ℕ × ℕ × ℕ), mFull3 M = true ∧ ∀ p ∈ M, chk rtRootPos 0 12 t p.1 p.2.1 p.2.2.1 p.2.2.2 = false := by
    interval_cases t
    · exact Or.inr sp_pr_1_One
    · exact Or.inr sp_pr_2_One
    · exact Or.inr sp_pr_3_One
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_4))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_5))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_6))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_7))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_8))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_9))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_10))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_11))
    · exact Or.inr (one3 (chk_of_core_pos (by omega) rootL0_eq rootM0_eq rootG0_pos_eq rootBp_eq rootV0_pos_eq pr_12))
  exact imp_of_live_pos root_p1 (by norm_num) irRootPos ht1 (le_refl _) hS hl hmin hM
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def f (x : Fin 6 → Bool) : Bool := (x 0 && x 1 && x 2) || (x 0 && x 1 && x 3) || (x 0 && x 2 && x 3) || (x 1 && x 2 && x 3) || (x 0 && x 4) || (x 1 && x 2 && x 4) || (x 2 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 1 && x 2 && x 5) || (x 1 && x 3 && x 5)
def EF : ℕ := (rawP0.getD 0 0 &&& rawP0.getD 1 0 &&& rawP0.getD 2 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 1 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 3 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 2 0 &&& rawP0.getD 3 0 &&& rawP0.getD 4 0) ||| (rawP0.getD 0 0 &&& rawP0.getD 2 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 2 0 &&& rawP0.getD 5 0) ||| (rawP0.getD 1 0 &&& rawP0.getD 3 0 &&& rawP0.getD 5 0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem EF_ok : EF &&& mz 0 = tz 0 := by decide +kernel
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
    Sol A0 (mz 0) (tz 0) D.size (C (mz 0) (WZ 0)) := by
  obtain ⟨gates, out⟩ := D
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ 0) := by
    intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, hw, rfl⟩
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
  exact ex_sol (mz 0) gates init (C (mz 0) (WZ 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD ⟨out, hout⟩
theorem bridge_not (gates : List Gate) (o : ℕ) (hD : FanInTwo ⟨gates, o⟩) (hnot : ∃ g ∈ gates, g.op = GateOp.not)
    (hf : ∀ y : Fin 6 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn y) = f y) :
    Sol A0 (mz 0) (tz 0) (gates.length - 1) (C (mz 0) (WZ 0)) ∨
    ∃ t, 1 ≤ t ∧ ∃ S0 : Finset ℕ, (S0 : Set ℕ) ⊆ C (mz 0) (WZ 0) ∧ Live A0 (mz 0) (tz 0) gates.length t S0 := by
  let row : ℕ → Fin 6 → Bool := fun k v => (rawP0.getD v.val 0).testBit k
  let init : List ℕ := rawP0.map (· &&& mz 0)
  have hinit_sub : ∀ x ∈ init, x &&& mz 0 = x := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, _, rfl⟩ := hx; rw [Nat.and_assoc, Nat.and_self]
  have hinit_mem : ∀ x ∈ init, x ∈ C (mz 0) (WZ 0) := by intro x hx; simp only [init, List.mem_map] at hx; obtain ⟨w, hw, rfl⟩ := hx; exact Or.inl ⟨w, hw, rfl⟩
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
  exact ex_sol_not (mz 0) gates init (C (mz 0) (WZ 0)) hinit_mem (Or.inr (Set.mem_insert _ _)) (Or.inr (Set.mem_insert_of_mem _ rfl)) hD hnot ⟨o, hout⟩
def onWit : List Gate := [⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [8, 4]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [10, 3]⟩, ⟨.and, [11, 2]⟩, ⟨.or, [12, 9]⟩, ⟨.and, [13, 7]⟩, ⟨.and, [10, 1]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [16, 3]⟩, ⟨.or, [17, 14]⟩]
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
theorem onTableCorrect : ∀ x : Fin 6 → Bool, f x = Nat.testBit (4276808928 * 2 ^ 32 + 4209698944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by decide +kernel
end inst_data
end PEqualNP.Outside.L_meta_42288_aux

open PEqualNP.Outside.L_meta_42288_aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_42288 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4209698944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4209698944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
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
