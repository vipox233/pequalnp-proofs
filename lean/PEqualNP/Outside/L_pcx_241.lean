import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_241_aux

open PEqualNP.ProofComplexity

private lemma exists_3cnf_single_list {U : Type} [DecidableEq U] (L : List (U × Bool)) :
    ∃ (q : ℕ) (F : Finset (Clause (U ⊕ Fin q))),
      (∀ C ∈ F, C.card ≤ 3) ∧
      ∀ α : U → Bool,
        (∃ l ∈ L, α l.1 = l.2) ↔
        ∃ a : Fin q → Bool, Satisfies (Sum.elim α a) (↑F : Set (Clause (U ⊕ Fin q))) := by
  let q := L.length + 1
  let cStart : Clause (U ⊕ Fin q) := {(Sum.inr ⟨0, Nat.zero_lt_succ L.length⟩, true)}
  let cEnd : Clause (U ⊕ Fin q) := {(Sum.inr ⟨L.length, Nat.lt_succ_self L.length⟩, false)}
  let stepClause : Fin L.length → Clause (U ⊕ Fin q) := fun i =>
    {(Sum.inr ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩, false),
     (Sum.inl (L.get i).1, (L.get i).2),
     (Sum.inr ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, true)}
  let F : Finset (Clause (U ⊕ Fin q)) :=
    insert cStart (insert cEnd (Finset.univ.image stepClause))
  refine ⟨q, F, ?_, ?_⟩
  · intro C hC
    simp only [F, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hC
    rcases hC with rfl | rfl | ⟨i, rfl⟩
    · simp [cStart]
    · simp [cEnd]
    · exact (Finset.card_insert_le _ _).trans
        (Nat.add_le_add_right ((Finset.card_insert_le _ _).trans (by simp)) 1)
  · intro α
    constructor
    · rintro ⟨l, hl, hα⟩
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hl
      let a : Fin q → Bool := fun j => decide (j.val ≤ i.val)
      refine ⟨a, ?_⟩
      intro C hC
      simp only [Finset.mem_coe, F, Finset.mem_insert, Finset.mem_image, Finset.mem_univ,
        true_and] at hC
      rcases hC with rfl | rfl | ⟨j, rfl⟩
      · refine ⟨(Sum.inr ⟨0, Nat.zero_lt_succ L.length⟩, true), Finset.mem_singleton_self _, ?_⟩
        simp [a]
      · refine ⟨(Sum.inr ⟨L.length, Nat.lt_succ_self L.length⟩, false),
          Finset.mem_singleton_self _, ?_⟩
        simp only [Sum.elim_inr, a, decide_eq_false_iff_not, not_le]
        exact i.isLt
      · by_cases hlt : j.val < i.val
        · refine ⟨(Sum.inr ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, true), ?_, ?_⟩
          · simp [stepClause]
          · simp only [Sum.elim_inr, a, decide_eq_true_eq]
            omega
        · by_cases heq : j.val = i.val
          · refine ⟨(Sum.inl (L.get j).1, (L.get j).2), ?_, ?_⟩
            · simp [stepClause]
            · have hji : j = i := Fin.ext heq
              rw [hji]
              simpa using hα
          · refine ⟨(Sum.inr ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, false), ?_, ?_⟩
            · simp [stepClause]
            · simp only [Sum.elim_inr, a, decide_eq_false_iff_not, not_le]
              omega
    · rintro ⟨a, ha⟩
      by_contra hnone
      have ha0 : a ⟨0, Nat.zero_lt_succ L.length⟩ = true := by
        obtain ⟨lit, hlit, hsat⟩ := ha cStart (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
        rw [Finset.mem_singleton] at hlit
        subst hlit
        simpa using hsat
      have haEnd : a ⟨L.length, Nat.lt_succ_self L.length⟩ = false := by
        obtain ⟨lit, hlit, hsat⟩ := ha cEnd
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        rw [Finset.mem_singleton] at hlit
        subst hlit
        simpa using hsat
      have hind : ∀ (j : ℕ) (hj : j ≤ L.length), a ⟨j, Nat.lt_succ_of_le hj⟩ = true := by
        intro j
        induction j with
        | zero => intro _; exact ha0
        | succ j ih =>
          intro hj
          have hjlt : j < L.length := Nat.lt_of_succ_le hj
          have haj := ih (Nat.le_of_lt hjlt)
          have hmem : stepClause ⟨j, hjlt⟩ ∈ F :=
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
              (Finset.mem_image.2 ⟨⟨j, hjlt⟩, Finset.mem_univ _, rfl⟩))
          obtain ⟨lit, hlit, hsat⟩ := ha _ (Finset.mem_coe.2 hmem)
          simp only [stepClause, Finset.mem_insert, Finset.mem_singleton] at hlit
          rcases hlit with rfl | rfl | rfl
          · simp only [Sum.elim_inr] at hsat
            rw [haj] at hsat
            cases hsat
          · exfalso
            simp only [Sum.elim_inl] at hsat
            exact hnone ⟨L.get ⟨j, hjlt⟩, List.get_mem L ⟨j, hjlt⟩, hsat⟩
          · simpa using hsat
      have hbad := hind L.length (Nat.le_refl _)
      rw [haEnd] at hbad
      cases hbad

private lemma exists_3cnf_of_pred {U : Type} [Fintype U] [DecidableEq U]
    (P : (U → Bool) → Prop) [DecidablePred P] :
    ∃ (q : ℕ) (F : Finset (Clause (U ⊕ Fin q))),
      (∀ C ∈ F, C.card ≤ 3) ∧
      ∀ α : U → Bool,
        P α ↔ ∃ a : Fin q → Bool, Satisfies (Sum.elim α a) (↑F : Set (Clause (U ⊕ Fin q))) := by
  let L : List U := (Finset.univ : Finset U).toList
  have hL : ∀ u : U, u ∈ L := fun u => Finset.mem_toList.2 (Finset.mem_univ u)
  let bad : Finset (U → Bool) := Finset.univ.filter (fun β => ¬ P β)
  let eB : Fin bad.card ≃ {β : U → Bool // β ∈ bad} :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe bad)).symm
  let clauseList : Fin bad.card → List (U × Bool) := fun idx =>
    L.map (fun u => (u, !((eB idx).1 u)))
  have hch : ∀ idx : Fin bad.card,
      ∃ (q : ℕ) (F : Finset (Clause (U ⊕ Fin q))),
        (∀ C ∈ F, C.card ≤ 3) ∧
        ∀ α : U → Bool,
          (∃ l ∈ clauseList idx, α l.1 = l.2) ↔
          ∃ a : Fin q → Bool, Satisfies (Sum.elim α a) (↑F : Set (Clause (U ⊕ Fin q))) :=
    fun idx => exists_3cnf_single_list (clauseList idx)
  choose qs Fs hFcard hFspec using hch
  let σ := (idx : Fin bad.card) × Fin (qs idx)
  let q := Fintype.card σ
  let eQ : σ ≃ Fin q := Fintype.equivFin σ
  let liftLit (idx : Fin bad.card) (lit : (U ⊕ Fin (qs idx)) × Bool) : (U ⊕ Fin q) × Bool :=
    match lit.1 with
    | Sum.inl u => (Sum.inl u, lit.2)
    | Sum.inr j => (Sum.inr (eQ ⟨idx, j⟩), lit.2)
  let liftClause (idx : Fin bad.card) (C : Clause (U ⊕ Fin (qs idx))) : Clause (U ⊕ Fin q) :=
    C.image (liftLit idx)
  let F : Finset (Clause (U ⊕ Fin q)) :=
    (Finset.univ : Finset (Fin bad.card)).biUnion (fun idx => (Fs idx).image (liftClause idx))
  refine ⟨q, F, ?_, ?_⟩
  · intro C hC
    obtain ⟨idx, _, hCi⟩ := Finset.mem_biUnion.1 hC
    obtain ⟨C0, hC0, rfl⟩ := Finset.mem_image.1 hCi
    exact Finset.card_image_le.trans (hFcard idx C0 hC0)
  · intro α
    have hP_iff : P α ↔ ∀ idx : Fin bad.card, ∃ l ∈ clauseList idx, α l.1 = l.2 := by
      constructor
      · intro hP idx
        have hne : α ≠ (eB idx).1 := by
          intro heq
          have hnb : ¬ P (eB idx).1 := (Finset.mem_filter.1 (eB idx).2).2
          exact hnb (heq ▸ hP)
        obtain ⟨u, hu⟩ : ∃ u : U, α u ≠ (eB idx).1 u := by
          by_contra hc
          apply hne
          ext u
          by_contra hnu
          exact hc ⟨u, hnu⟩
        refine ⟨(u, !((eB idx).1 u)), List.mem_map.2 ⟨u, hL u, rfl⟩, ?_⟩
        cases h1 : α u <;> cases h2 : (eB idx).1 u <;> simp_all
      · intro hall
        by_contra hnp
        have hmem : α ∈ bad := Finset.mem_filter.2 ⟨Finset.mem_univ α, hnp⟩
        let idx := eB.symm ⟨α, hmem⟩
        obtain ⟨l, hl, hsat⟩ := hall idx
        obtain ⟨u, _, rfl⟩ := List.mem_map.1 hl
        have heq : (eB idx).1 = α := congrArg Subtype.val (eB.apply_symm_apply ⟨α, hmem⟩)
        rw [heq] at hsat
        cases h1 : α u <;> rw [h1] at hsat <;> cases hsat
    rw [hP_iff]
    constructor
    · intro hall
      have hEx : ∀ idx : Fin bad.card,
          ∃ a : Fin (qs idx) → Bool,
            Satisfies (Sum.elim α a) (↑(Fs idx) : Set (Clause (U ⊕ Fin (qs idx)))) :=
        fun idx => (hFspec idx α).1 (hall idx)
      choose as has using hEx
      refine ⟨fun j => as (eQ.symm j).1 (eQ.symm j).2, ?_⟩
      intro C hC
      rw [Finset.mem_coe] at hC
      obtain ⟨idx, _, hCi⟩ := Finset.mem_biUnion.1 hC
      obtain ⟨C0, hC0, rfl⟩ := Finset.mem_image.1 hCi
      obtain ⟨lit, hlit, hsat⟩ := has idx C0 (Finset.mem_coe.2 hC0)
      refine ⟨liftLit idx lit, Finset.mem_image.2 ⟨lit, hlit, rfl⟩, ?_⟩
      rcases lit with ⟨u | j, b⟩
      · simpa [liftLit] using hsat
      · simp only [liftLit, Sum.elim_inr] at hsat ⊢
        have hrev : eQ.symm (eQ ⟨idx, j⟩) = ⟨idx, j⟩ := eQ.symm_apply_apply ⟨idx, j⟩
        change (fun p : σ => as p.1 p.2) (eQ.symm (eQ ⟨idx, j⟩)) = b
        rw [hrev]
        exact hsat
    · rintro ⟨a, ha⟩ idx
      refine (hFspec idx α).2 ⟨fun j => a (eQ ⟨idx, j⟩), ?_⟩
      intro C0 hC0
      have hmem : liftClause idx C0 ∈ F :=
        Finset.mem_biUnion.2 ⟨idx, Finset.mem_univ _,
          Finset.mem_image.2 ⟨C0, Finset.mem_coe.1 hC0, rfl⟩⟩
      obtain ⟨lit', hlit', hsat⟩ := ha _ (Finset.mem_coe.2 hmem)
      obtain ⟨lit, hlit, rfl⟩ := Finset.mem_image.1 hlit'
      refine ⟨lit, hlit, ?_⟩
      rcases lit with ⟨u | j, b⟩
      · simpa [liftLit] using hsat
      · simpa [liftLit] using hsat

private def reassocLit {A B C : Type} (l : Literal ((A ⊕ B) ⊕ C)) : Literal (A ⊕ (B ⊕ C)) :=
  match l.1 with
  | Sum.inl (Sum.inl a) => (Sum.inl a, l.2)
  | Sum.inl (Sum.inr b) => (Sum.inr (Sum.inl b), l.2)
  | Sum.inr c => (Sum.inr (Sum.inr c), l.2)

private lemma exists_3cnf_assoc {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : (A → Bool) → (B → Bool) → Prop) [DecidablePred (fun α : A ⊕ B → Bool => P (fun a => α (Sum.inl a)) (fun b => α (Sum.inr b)))] :
    ∃ (q : ℕ) (F : Finset (Clause (A ⊕ (B ⊕ Fin q)))),
      (∀ C ∈ F, C.card ≤ 3) ∧
      ∀ (f : A → Bool) (g : B → Bool),
        P f g ↔ ∃ loc : Fin q → Bool,
          Satisfies (Sum.elim f (Sum.elim g loc)) (↑F : Set (Clause (A ⊕ (B ⊕ Fin q)))) := by
  obtain ⟨q, F0, hcard0, hspec0⟩ :=
    exists_3cnf_of_pred (fun α : A ⊕ B → Bool => P (fun a => α (Sum.inl a)) (fun b => α (Sum.inr b)))
  let liftC : Clause ((A ⊕ B) ⊕ Fin q) → Clause (A ⊕ (B ⊕ Fin q)) := fun C => C.image reassocLit
  let F : Finset (Clause (A ⊕ (B ⊕ Fin q))) := F0.image liftC
  refine ⟨q, F, ?_, ?_⟩
  · intro C hC
    obtain ⟨C0, hC0, rfl⟩ := Finset.mem_image.1 hC
    exact Finset.card_image_le.trans (hcard0 C0 hC0)
  · intro f g
    have hpeq : P f g ↔ P (fun a => Sum.elim f g (Sum.inl a)) (fun b => Sum.elim f g (Sum.inr b)) :=
      Iff.rfl
    rw [hpeq, hspec0 (Sum.elim f g)]
    constructor
    · rintro ⟨loc, hloc⟩
      refine ⟨loc, ?_⟩
      intro C hC
      obtain ⟨C0, hC0, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC)
      obtain ⟨lit, hlit, hsat⟩ := hloc C0 (Finset.mem_coe.2 hC0)
      refine ⟨reassocLit lit, Finset.mem_image.2 ⟨lit, hlit, rfl⟩, ?_⟩
      rcases lit with ⟨(a | b) | c, s⟩ <;> simpa [reassocLit] using hsat
    · rintro ⟨loc, hloc⟩
      refine ⟨loc, ?_⟩
      intro C0 hC0
      obtain ⟨lit', hlit', hsat⟩ :=
        hloc (liftC C0) (Finset.mem_coe.2 (Finset.mem_image.2 ⟨C0, Finset.mem_coe.1 hC0, rfl⟩))
      obtain ⟨lit, hlit, rfl⟩ := Finset.mem_image.1 hlit'
      refine ⟨lit, hlit, ?_⟩
      rcases lit with ⟨(a | b) | c, s⟩ <;> simpa [reassocLit] using hsat

private def outDeg {V : Type} [DecidableEq V] (A : Finset (V × V)) (v : V) : ℕ :=
  (A.filter (fun e => e.1 = v)).card

private def inDeg {V : Type} [DecidableEq V] (A : Finset (V × V)) (v : V) : ℕ :=
  (A.filter (fun e => e.2 = v)).card

private def balance {V : Type} [DecidableEq V] (A : Finset (V × V)) (v : V) : ℤ :=
  (outDeg A v : ℤ) - (inDeg A v : ℤ)

private def IsFlow {V : Type} [DecidableEq V] (E : Finset (V × V)) (s t : V) (m : ℕ)
    (A : Finset (V × V)) : Prop :=
  A ⊆ E ∧ balance A s = (m : ℤ) ∧ balance A t = -(m : ℤ) ∧
    ∀ v, v ≠ s → v ≠ t → balance A v = 0

private lemma outDeg_insert {V : Type} [DecidableEq V] {A : Finset (V × V)} {u v : V}
    (h : (u, v) ∉ A) (x : V) :
    outDeg (insert (u, v) A) x = outDeg A x + if x = u then 1 else 0 := by
  unfold outDeg
  rw [Finset.filter_insert]
  by_cases hxu : x = u
  · subst hxu
    simp only [↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hm
    exact h (Finset.mem_filter.1 hm).1
  · have hne : ¬ (u = x) := fun heq => hxu heq.symm
    simp [hxu, hne]

private lemma inDeg_insert {V : Type} [DecidableEq V] {A : Finset (V × V)} {u v : V}
    (h : (u, v) ∉ A) (x : V) :
    inDeg (insert (u, v) A) x = inDeg A x + if x = v then 1 else 0 := by
  unfold inDeg
  rw [Finset.filter_insert]
  by_cases hxv : x = v
  · subst hxv
    simp only [↓reduceIte]
    rw [Finset.card_insert_of_notMem]
    intro hm
    exact h (Finset.mem_filter.1 hm).1
  · have hne : ¬ (v = x) := fun heq => hxv heq.symm
    simp [hxv, hne]

private lemma balance_insert {V : Type} [DecidableEq V] {A : Finset (V × V)} {u v : V}
    (h : (u, v) ∉ A) (x : V) :
    balance (insert (u, v) A) x =
      balance A x + (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
  unfold balance
  rw [outDeg_insert h x, inDeg_insert h x]
  split_ifs <;> omega

private lemma balance_erase {V : Type} [DecidableEq V] {A : Finset (V × V)} {u v : V}
    (h : (u, v) ∈ A) (x : V) :
    balance (A.erase (u, v)) x =
      balance A x - (if x = u then 1 else 0) + (if x = v then 1 else 0) := by
  have hnot : (u, v) ∉ A.erase (u, v) := Finset.notMem_erase (u, v) A
  have hrec := balance_insert hnot x
  rw [Finset.insert_erase h] at hrec
  omega

private lemma sum_outDeg_eq {V : Type} [DecidableEq V] (A : Finset (V × V)) (R : Finset V) :
    ∑ v ∈ R, outDeg A v = (A.filter (fun e => e.1 ∈ R)).card := by
  unfold outDeg
  have hdisj : Set.PairwiseDisjoint (↑R : Set V) (fun v => A.filter (fun e => e.1 = v)) := by
    intro v1 _ v2 _ hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro e he1 he2
    have h1 := (Finset.mem_filter.1 he1).2
    have h2 := (Finset.mem_filter.1 he2).2
    exact hne (h1.symm.trans h2)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv, heA, he1⟩
    exact ⟨heA, he1 ▸ hv⟩
  · rintro ⟨heA, he1⟩
    exact ⟨e.1, he1, heA, rfl⟩

private lemma sum_inDeg_eq {V : Type} [DecidableEq V] (A : Finset (V × V)) (R : Finset V) :
    ∑ v ∈ R, inDeg A v = (A.filter (fun e => e.2 ∈ R)).card := by
  unfold inDeg
  have hdisj : Set.PairwiseDisjoint (↑R : Set V) (fun v => A.filter (fun e => e.2 = v)) := by
    intro v1 _ v2 _ hne
    show Disjoint _ _
    rw [Finset.disjoint_left]
    intro e he1 he2
    have h1 := (Finset.mem_filter.1 he1).2
    have h2 := (Finset.mem_filter.1 he2).2
    exact hne (h1.symm.trans h2)
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨v, hv, heA, he2⟩
    exact ⟨heA, he2 ▸ hv⟩
  · rintro ⟨heA, he2⟩
    exact ⟨e.2, he2, heA, rfl⟩

private lemma filter_split_card {α : Type} [DecidableEq α] (S : Finset α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q] :
    (S.filter P).card =
      (S.filter (fun x => P x ∧ Q x)).card + (S.filter (fun x => P x ∧ ¬ Q x)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.1 hx2).2.2 (Finset.mem_filter.1 hx1).2.2

private lemma sum_balance_eq_cut {V : Type} [DecidableEq V] (A : Finset (V × V)) (R : Finset V) :
    ∑ v ∈ R, balance A v =
      ((A.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)).card : ℤ) -
      ((A.filter (fun e => e.1 ∉ R ∧ e.2 ∈ R)).card : ℤ) := by
  unfold balance
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, sum_outDeg_eq, sum_inDeg_eq]
  have h1 := filter_split_card A (fun e => e.1 ∈ R) (fun e => e.2 ∈ R)
  have h2 := filter_split_card A (fun e => e.2 ∈ R) (fun e => e.1 ∈ R)
  have hsame : A.filter (fun e => e.1 ∈ R ∧ e.2 ∈ R) = A.filter (fun e => e.2 ∈ R ∧ e.1 ∈ R) := by
    ext e; simp [and_comm]
  have hsame2 : A.filter (fun e => e.2 ∈ R ∧ e.1 ∉ R) = A.filter (fun e => e.1 ∉ R ∧ e.2 ∈ R) := by
    ext e; simp [and_comm]
  rw [hsame] at h1
  rw [hsame2] at h2
  omega

private def Walk {V : Type} (adj : V → V → Prop) : List V → Prop
  | [] => True
  | [_] => True
  | u :: v :: rest => adj u v ∧ Walk adj (v :: rest)

private def SimplePath {V : Type} (adj : V → V → Prop) (s t : V) (L : List V) : Prop :=
  L.head? = some s ∧ L.getLast? = some t ∧ Walk adj L ∧ L.Nodup

private lemma walk_of_append_right {V : Type} {adj : V → V → Prop} {pre suf : List V}
    (h : Walk adj (pre ++ suf)) : Walk adj suf := by
  induction pre with
  | nil => exact h
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases suf with
      | nil => trivial
      | cons b bs => exact h.2
    | cons b bs =>
      exact ih h.2

private lemma split_at_mem {V : Type} {x : V} {M : List V} (hx : x ∈ M) :
    ∃ pre suf : List V, M = pre ++ x :: suf := by
  induction M with
  | nil => cases hx
  | cons a rest ih =>
    rcases List.mem_cons.1 hx with rfl | hrest
    · exact ⟨[], rest, rfl⟩
    · obtain ⟨pre, suf, rfl⟩ := ih hrest
      exact ⟨a :: pre, suf, rfl⟩

private lemma shorten_walk {V : Type} {adj : V → V → Prop} :
    ∀ L : List V, ∀ s t : V,
      L.head? = some s → L.getLast? = some t → Walk adj L →
      ∃ M : List V, SimplePath adj s t M ∧ ∀ x ∈ M, x ∈ L
  | [], _, _, hhead, _, _ => by simp at hhead
  | [a], s, t, hhead, hlast, _ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast
    exact ⟨[a], ⟨rfl, rfl, trivial, List.nodup_singleton a⟩, fun _ hx => hx⟩
  | a :: b :: rest, s, t, hhead, hlast, hwalk => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlast' : (b :: rest).getLast? = some t := by
      simpa [List.getLast?_cons_cons] using hlast
    obtain ⟨M, ⟨hMh, hMl, hMw, hMnod⟩, hMsub⟩ := shorten_walk (b :: rest) b t rfl hlast' hwalk.2
    by_cases haM : a ∈ M
    · obtain ⟨pre, suf, hMeq⟩ := split_at_mem haM
      refine ⟨a :: suf, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
      · rw [hMeq] at hMl
        have hgl : (pre ++ a :: suf).getLast? = (a :: suf).getLast? := by
          clear hMl hMw hMnod hMsub hMeq
          induction pre with
          | nil => rfl
          | cons c cs ih =>
            cases hcs : cs ++ a :: suf with
            | nil =>
              have := (List.append_eq_nil_iff.1 hcs).2
              simp at this
            | cons d ds =>
              have : (c :: d :: ds).getLast? = (d :: ds).getLast? := rfl
              rw [List.cons_append, hcs, this, ← hcs]
              exact ih
        rw [← hgl]
        exact hMl
      · rw [hMeq] at hMw
        exact walk_of_append_right hMw
      · rw [hMeq] at hMnod
        exact (List.nodup_append.1 hMnod).2.1
      · intro x hx
        have hxM : x ∈ M := by rw [hMeq]; exact List.mem_append_right pre hx
        exact List.mem_cons_of_mem a (hMsub x hxM)
    · cases M with
      | nil => simp at hMh
      | cons m ms =>
        simp only [List.head?_cons, Option.some.injEq] at hMh
        subst m
        refine ⟨a :: b :: ms, ⟨rfl, ?_, ⟨hwalk.1, hMw⟩, List.nodup_cons.2 ⟨haM, hMnod⟩⟩, ?_⟩
        · simpa [List.getLast?_cons_cons] using hMl
        · intro x hx
          rcases List.mem_cons.1 hx with rfl | hxm
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem a (hMsub x hxm)

private lemma exists_walk_of_reflTransGen {V : Type} {adj : V → V → Prop} {s t : V}
    (h : Relation.ReflTransGen adj s t) :
    ∃ L : List V, L.head? = some s ∧ L.getLast? = some t ∧ Walk adj L := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[t], rfl, rfl, trivial⟩
  | @head a b hab _ ih =>
    obtain ⟨L, hLh, hLl, hLw⟩ := ih
    cases L with
    | nil => simp at hLh
    | cons c cs =>
      simp only [List.head?_cons, Option.some.injEq] at hLh
      subst c
      exact ⟨a :: b :: cs, rfl, by simpa [List.getLast?_cons_cons] using hLl, hab, hLw⟩

private lemma exists_simplePath_of_reflTransGen {V : Type} {adj : V → V → Prop} {s t : V}
    (h : Relation.ReflTransGen adj s t) :
    ∃ L : List V, SimplePath adj s t L := by
  obtain ⟨L, h1, h2, h3⟩ := exists_walk_of_reflTransGen h
  obtain ⟨M, hM, _⟩ := shorten_walk L s t h1 h2 h3
  exact ⟨M, hM⟩

private def ResAdj {V : Type} [DecidableEq V] (E A : Finset (V × V)) (u v : V) : Prop :=
  ((u, v) ∈ E ∧ (u, v) ∉ A) ∨ (v, u) ∈ A

private def augEdge {V : Type} [DecidableEq V] (E : Finset (V × V)) (u v : V)
    (A : Finset (V × V)) : Finset (V × V) :=
  if (u, v) ∈ E then insert (u, v) A else A.erase (v, u)

private def augWalk {V : Type} [DecidableEq V] (E : Finset (V × V)) :
    List V → Finset (V × V) → Finset (V × V)
  | [], A => A
  | [_], A => A
  | u :: v :: rest, A => augWalk E (v :: rest) (augEdge E u v A)

private lemma walk_resAdj_congr {V : Type} [DecidableEq V] {E A A1 : Finset (V × V)} {u : V} :
    ∀ L : List V, u ∉ L →
      (∀ a b, a ≠ u → b ≠ u → ((a, b) ∈ A1 ↔ (a, b) ∈ A)) →
      Walk (ResAdj E A) L → Walk (ResAdj E A1) L
  | [], _, _, _ => trivial
  | [_], _, _, _ => trivial
  | a :: b :: rest, hu, hcongr, ⟨hab, hrest⟩ => by
    have hau : a ≠ u := fun h => hu (h ▸ List.mem_cons_self ..)
    have hbu : b ≠ u := fun h => hu (List.mem_cons_of_mem a (h ▸ List.mem_cons_self ..))
    have hrest_u : u ∉ b :: rest := fun hm => hu (List.mem_cons_of_mem a hm)
    constructor
    · unfold ResAdj at hab ⊢
      rw [hcongr a b hau hbu, hcongr b a hbu hau]
      exact hab
    · exact walk_resAdj_congr (b :: rest) hrest_u hcongr hrest

private lemma augWalk_spec {V : Type} [DecidableEq V] {E : Finset (V × V)}
    (hasym : ∀ e ∈ E, (e.2, e.1) ∉ E) :
    ∀ (L : List V) (s t : V) (A : Finset (V × V)),
      A ⊆ E → SimplePath (ResAdj E A) s t L →
      augWalk E L A ⊆ E ∧
      ∀ x : V, balance (augWalk E L A) x =
        balance A x + (if x = s then 1 else 0) - (if x = t then 1 else 0)
  | [], _, _, _, _, ⟨hhead, _, _, _⟩ => by simp at hhead
  | [a], s, t, A, hAE, ⟨hhead, hlast, _, _⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast
    refine ⟨hAE, fun x => ?_⟩
    simp only [augWalk]
    split_ifs <;> omega
  | u :: v :: rest, s, t, A, hAE, ⟨hhead, hlast, ⟨huv, hrest⟩, hnod⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlast' : (v :: rest).getLast? = some t := by
      simpa [List.getLast?_cons_cons] using hlast
    rcases List.nodup_cons.1 hnod with ⟨hu_not, hnod'⟩
    let A1 := augEdge E u v A
    have hA1_sub : A1 ⊆ E := by
      unfold A1 augEdge
      split_ifs with hE
      · exact Finset.insert_subset hE hAE
      · exact (Finset.erase_subset _ _).trans hAE
    have hA1_bal : ∀ x : V, balance A1 x =
        balance A x + (if x = u then 1 else 0) - (if x = v then 1 else 0) := by
      intro x
      unfold A1 augEdge
      rcases huv with ⟨hE, hnotA⟩ | hvuA
      · simp only [hE, ↓reduceIte]
        exact balance_insert hnotA x
      · have hnotE : (u, v) ∉ E := hasym (v, u) (hAE hvuA)
        simp only [hnotE, ↓reduceIte]
        have he := balance_erase hvuA x
        omega
    have hA1_congr : ∀ a b, a ≠ u → b ≠ u → ((a, b) ∈ A1 ↔ (a, b) ∈ A) := by
      intro a b hau hbu
      unfold A1 augEdge
      split_ifs
      · simp [hau]
      · simp [hbu]
    have hrest1 : Walk (ResAdj E A1) (v :: rest) :=
      walk_resAdj_congr (v :: rest) hu_not hA1_congr hrest
    obtain ⟨hsub, hbal⟩ := augWalk_spec hasym (v :: rest) v t A1 hA1_sub
      ⟨rfl, hlast', hrest1, hnod'⟩
    refine ⟨hsub, fun x => ?_⟩
    change balance (augWalk E (v :: rest) A1) x = _
    rw [hbal x, hA1_bal x]
    split_ifs <;> omega

private lemma exists_flow {V : Type} [Fintype V] [DecidableEq V]
    {E : Finset (V × V)} (hasym : ∀ e ∈ E, (e.2, e.1) ∉ E)
    {s t : V} (hst : s ≠ t) {B : ℕ}
    (hcut : ∀ R : Finset V, s ∈ R → t ∉ R → B ≤ (E.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)).card) :
    ∀ m ≤ B, ∃ A : Finset (V × V), IsFlow E s t m A := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨∅, Finset.empty_subset E, ?_, ?_, ?_⟩ <;> simp [balance, outDeg, inDeg]
  | succ m ih =>
    intro hmB
    obtain ⟨A, hAE, hbalS, hbalT, hbalO⟩ := ih (Nat.le_of_succ_le hmB)
    let R : Finset V := Finset.univ.filter (fun v => Relation.ReflTransGen (ResAdj E A) s v)
    have hsR : s ∈ R := Finset.mem_filter.2 ⟨Finset.mem_univ s, Relation.ReflTransGen.refl⟩
    have htR : t ∈ R := by
      by_contra htNotR
      have hBcut := hcut R hsR htNotR
      have hEsubA : E.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R) ⊆
          A.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R) := by
        intro e he
        rcases Finset.mem_filter.1 he with ⟨heE, he1, he2⟩
        refine Finset.mem_filter.2 ⟨?_, he1, he2⟩
        by_contra heNotA
        have hreach1 : Relation.ReflTransGen (ResAdj E A) s e.1 := (Finset.mem_filter.1 he1).2
        have hreach2 : Relation.ReflTransGen (ResAdj E A) s e.2 :=
          Relation.ReflTransGen.tail hreach1 (Or.inl ⟨heE, heNotA⟩)
        exact he2 (Finset.mem_filter.2 ⟨Finset.mem_univ e.2, hreach2⟩)
      have hback0 : A.filter (fun e => e.1 ∉ R ∧ e.2 ∈ R) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rcases Finset.mem_filter.1 he with ⟨heA, he1, he2⟩
        have hreach2 : Relation.ReflTransGen (ResAdj E A) s e.2 := (Finset.mem_filter.1 he2).2
        have hreach1 : Relation.ReflTransGen (ResAdj E A) s e.1 :=
          Relation.ReflTransGen.tail hreach2 (Or.inr heA)
        exact he1 (Finset.mem_filter.2 ⟨Finset.mem_univ e.1, hreach1⟩)
      have hsum : ∑ v ∈ R, balance A v = (m : ℤ) := by
        rw [Finset.sum_eq_single s]
        · exact hbalS
        · intro v hv hvs
          have hvt : v ≠ t := fun heq => htNotR (heq ▸ hv)
          exact hbalO v hvs hvt
        · intro hsnot; exact absurd hsR hsnot
      have hcutEq := sum_balance_eq_cut A R
      rw [hsum, hback0, Finset.card_empty] at hcutEq
      have hcardLe : (E.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)).card ≤
          (A.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)).card := Finset.card_le_card hEsubA
      omega
    have hreach : Relation.ReflTransGen (ResAdj E A) s t := (Finset.mem_filter.1 htR).2
    obtain ⟨L, hL⟩ := exists_simplePath_of_reflTransGen hreach
    obtain ⟨hsub', hbal'⟩ := augWalk_spec hasym L s t A hAE hL
    refine ⟨augWalk E L A, hsub', ?_, ?_, ?_⟩
    · rw [hbal' s, hbalS]
      simp [hst]
    · rw [hbal' t, hbalT]
      have hts : t ≠ s := hst.symm
      simp only [hts, ↓reduceIte]
      omega
    · intro v hvs hvt
      rw [hbal' v, hbalO v hvs hvt]
      simp [hvs, hvt]

private def walkEdges {V : Type} [DecidableEq V] : List V → Finset (V × V)
  | [] => ∅
  | [_] => ∅
  | u :: v :: rest => insert (u, v) (walkEdges (v :: rest))

private lemma mem_walkEdges_fst {V : Type} [DecidableEq V] :
    ∀ (L : List V) (e : V × V), e ∈ walkEdges L → e.1 ∈ L ∧ e.2 ∈ L
  | [], _, he => by simp [walkEdges] at he
  | [_], _, he => by simp [walkEdges] at he
  | u :: v :: rest, e, he => by
    simp only [walkEdges, Finset.mem_insert] at he
    rcases he with rfl | hrest
    · exact ⟨List.mem_cons_self .., List.mem_cons_of_mem u (List.mem_cons_self ..)⟩
    · obtain ⟨h1, h2⟩ := mem_walkEdges_fst (v :: rest) e hrest
      exact ⟨List.mem_cons_of_mem u h1, List.mem_cons_of_mem u h2⟩

private lemma walkEdges_subset_of_walk {V : Type} [DecidableEq V] {A : Finset (V × V)} :
    ∀ L : List V, Walk (fun u v => (u, v) ∈ A) L → walkEdges L ⊆ A
  | [], _ => Finset.empty_subset A
  | [_], _ => Finset.empty_subset A
  | _ :: v :: rest, ⟨huv, hrest⟩ =>
    Finset.insert_subset huv (walkEdges_subset_of_walk (v :: rest) hrest)

private lemma balance_sdiff_walkEdges {V : Type} [DecidableEq V] :
    ∀ (L : List V) (s t : V) (A : Finset (V × V)),
      SimplePath (fun u v => (u, v) ∈ A) s t L →
      ∀ x : V, balance (A \ walkEdges L) x =
        balance A x - (if x = s then 1 else 0) + (if x = t then 1 else 0)
  | [], _, _, _, ⟨hhead, _, _, _⟩, _ => by simp at hhead
  | [a], s, t, A, ⟨hhead, hlast, _, _⟩, x => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead; subst hlast
    simp only [walkEdges, Finset.sdiff_empty]
    split_ifs <;> omega
  | u :: v :: rest, s, t, A, ⟨hhead, hlast, ⟨huv, hrest⟩, hnod⟩, x => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst u
    have hlast' : (v :: rest).getLast? = some t := by
      simpa [List.getLast?_cons_cons] using hlast
    rcases List.nodup_cons.1 hnod with ⟨hu_not, hnod'⟩
    have hrest_sub : Walk (fun a b => (a, b) ∈ A.erase (s, v)) (v :: rest) := by
      have hgen : ∀ M : List V, s ∉ M → Walk (fun a b => (a, b) ∈ A) M →
          Walk (fun a b => (a, b) ∈ A.erase (s, v)) M := by
        intro M
        induction M with
        | nil => intro _ _; trivial
        | cons a ms ih =>
          cases ms with
          | nil => intro _ _; trivial
          | cons b bs =>
            intro huM ⟨hab, hms⟩
            have hau : a ≠ s := fun h => huM (h ▸ List.mem_cons_self ..)
            refine ⟨Finset.mem_erase.2 ⟨by intro heq; exact hau (congrArg Prod.fst heq), hab⟩,
              ih (fun hm => huM (List.mem_cons_of_mem a hm)) hms⟩
      exact hgen (v :: rest) hu_not hrest
    have hsdiff_eq : A \ walkEdges (s :: v :: rest) = (A.erase (s, v)) \ walkEdges (v :: rest) := by
      ext e
      simp only [walkEdges, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase, not_or]
      tauto
    rw [hsdiff_eq,
      balance_sdiff_walkEdges (v :: rest) v t (A.erase (s, v)) ⟨rfl, hlast', hrest_sub, hnod'⟩ x,
      balance_erase huv x]
    split_ifs <;> omega

private lemma walk_mono {V : Type} {adj1 adj2 : V → V → Prop} (h : ∀ u v, adj1 u v → adj2 u v) :
    ∀ L : List V, Walk adj1 L → Walk adj2 L
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: _ :: _, ⟨h1, h2⟩ => ⟨h _ _ h1, walk_mono h _ h2⟩

private lemma flow_decompose {V : Type} [Fintype V] [DecidableEq V]
    {E : Finset (V × V)} {s t : V} (hst : s ≠ t) :
    ∀ (m : ℕ) (A : Finset (V × V)), IsFlow E s t m A →
      ∃ P : Fin m → List V,
        (∀ b : Fin m, SimplePath (fun u v => (u, v) ∈ E) s t (P b) ∧ walkEdges (P b) ⊆ A) ∧
        (∀ b1 b2 : Fin m, b1 ≠ b2 → Disjoint (walkEdges (P b1)) (walkEdges (P b2))) := by
  classical
  intro m
  induction m with
  | zero =>
    intro _ _
    exact ⟨Fin.elim0, fun b => Fin.elim0 b, fun b => Fin.elim0 b⟩
  | succ m ih =>
    intro A ⟨hAE, hbalS, hbalT, hbalO⟩
    let R : Finset V := Finset.univ.filter (fun v => Relation.ReflTransGen (fun u w => (u, w) ∈ A) s v)
    have hsR : s ∈ R := Finset.mem_filter.2 ⟨Finset.mem_univ s, Relation.ReflTransGen.refl⟩
    have htR : t ∈ R := by
      by_contra htNotR
      have hfwd0 : A.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he
        rcases Finset.mem_filter.1 he with ⟨heA, he1, he2⟩
        have hr1 : Relation.ReflTransGen (fun u w => (u, w) ∈ A) s e.1 := (Finset.mem_filter.1 he1).2
        have hr2 := Relation.ReflTransGen.tail hr1 heA
        exact he2 (Finset.mem_filter.2 ⟨Finset.mem_univ e.2, hr2⟩)
      have hsum : ∑ v ∈ R, balance A v = ((m + 1 : ℕ) : ℤ) := by
        rw [Finset.sum_eq_single s]
        · exact hbalS
        · intro v hv hvs
          exact hbalO v hvs (fun heq => htNotR (heq ▸ hv))
        · intro hns; exact absurd hsR hns
      have hcutEq := sum_balance_eq_cut A R
      rw [hsum, hfwd0, Finset.card_empty] at hcutEq
      omega
    have hreach : Relation.ReflTransGen (fun u w => (u, w) ∈ A) s t := (Finset.mem_filter.1 htR).2
    obtain ⟨L, hL⟩ := exists_simplePath_of_reflTransGen hreach
    have hLsubA : walkEdges L ⊆ A := walkEdges_subset_of_walk L hL.2.2.1
    have hLE : SimplePath (fun u v => (u, v) ∈ E) s t L :=
      ⟨hL.1, hL.2.1, walk_mono (fun _ _ h => hAE h) L hL.2.2.1, hL.2.2.2⟩
    let A' := A \ walkEdges L
    have hA'flow : IsFlow E s t m A' := by
      refine ⟨Finset.sdiff_subset.trans hAE, ?_, ?_, ?_⟩
      · rw [balance_sdiff_walkEdges L s t A hL s, hbalS]
        simp only [hst, ↓reduceIte]
        omega
      · rw [balance_sdiff_walkEdges L s t A hL t, hbalT]
        have hts : t ≠ s := hst.symm
        simp only [hts, ↓reduceIte]
        omega
      · intro v hvs hvt
        rw [balance_sdiff_walkEdges L s t A hL v, hbalO v hvs hvt]
        simp [hvs, hvt]
    obtain ⟨P', hP'spec, hP'disj⟩ := ih A' hA'flow
    refine ⟨Fin.cases L P', ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ ?_ b
      · exact ⟨hLE, hLsubA⟩
      · intro j
        exact ⟨(hP'spec j).1, (hP'spec j).2.trans Finset.sdiff_subset⟩
    · intro b1 b2
      refine Fin.cases ?_ (fun i => ?_) b1
      · refine Fin.cases ?_ (fun j => ?_) b2
        · intro hne; exact absurd rfl hne
        · intro _
          exact Finset.disjoint_of_subset_right (hP'spec j).2 Finset.disjoint_sdiff
      · refine Fin.cases ?_ (fun j => ?_) b2
        · intro _
          exact Finset.disjoint_of_subset_left (hP'spec i).2 Finset.sdiff_disjoint
        · intro hne
          exact hP'disj i j (fun h => hne (congrArg Fin.succ h))

private abbrev Node (p k : ℕ) := Fin p ⊕ (Fin k × Bool)

private def isEdge {p k : ℕ} (view : Fin p → Finset (Fin k)) : Node p k → Node p k → Prop
  | Sum.inl o, Sum.inr (t, false) => t ∈ view o
  | Sum.inr (t1, false), Sum.inr (t2, true) => t1 = t2
  | Sum.inr (t, true), Sum.inl o => t ∈ view o
  | _, _ => False

private def edgeBit {p k : ℕ} (e : Node p k × Node p k) : Option (Fin k) :=
  match e.1, e.2 with
  | Sum.inl _, Sum.inr (t, false) => some t
  | Sum.inr (t, false), Sum.inr (_, true) => some t
  | Sum.inr (t, true), Sum.inl _ => some t
  | _, _ => none

private def ValidHops {p k : ℕ} (view : Fin p → Finset (Fin k))
    (edges : Finset (Node p k × Node p k)) :
    Fin p → Fin p → List (Fin p × Fin k × Fin p) → Prop
  | o1, o2, [] => o1 = o2
  | o1, o2, (a, t, c) :: rest =>
      a = o1 ∧ t ∈ view a ∧ t ∈ view c ∧
      (Sum.inr (t, false), Sum.inr (t, true)) ∈ edges ∧
      ValidHops view edges c o2 rest

private lemma walk_to_hops {p k : ℕ} (view : Fin p → Finset (Fin k)) :
    ∀ (L : List (Node p k)) (o1 o2 : Fin p),
      L.head? = some (Sum.inl o1) → L.getLast? = some (Sum.inl o2) →
      Walk (isEdge view) L →
      ∃ H : List (Fin p × Fin k × Fin p), ValidHops view (walkEdges L) o1 o2 H
  | [], _, _, hhead, _, _ => by simp at hhead
  | [x], o1, o2, hhead, hlast, _ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    rw [hhead] at hlast
    exact ⟨[], Sum.inl.inj hlast⟩
  | [_, _], o1, o2, hhead, hlast, ⟨he, _⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    have hlast' : _ = some (Sum.inl o2) := hlast
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hlast'
    rw [hhead, hlast'] at he
    cases he
  | [u0, u1, u2], o1, o2, hhead, hlast, ⟨he1, he2, _⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    have hlast' : u2 = Sum.inl o2 := by
      simpa [List.getLast?_cons_cons] using hlast
    rw [hhead] at he1
    rw [hlast'] at he2
    cases u1 with
    | inl _ => simp [isEdge] at he1
    | inr tb =>
      rcases tb with ⟨t, b⟩
      cases b
      · simp [isEdge] at he2
      · simp [isEdge] at he1
  | u0 :: u1 :: u2 :: u3 :: rest, o1, o2, hhead, hlast, ⟨he1, he2, he3, hrest⟩ => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases u1 with
    | inl _ => cases he1
    | inr tb1 =>
      rcases tb1 with ⟨t1, b1⟩
      cases b1 with
      | true => cases he1
      | false =>
        have ht1a : t1 ∈ view o1 := he1
        cases u2 with
        | inl _ => cases he2
        | inr tb2 =>
          rcases tb2 with ⟨t2, b2⟩
          cases b2 with
          | false => cases he2
          | true =>
            have ht12 : t1 = t2 := he2
            subst ht12
            cases u3 with
            | inr _ => cases he3
            | inl oMid =>
              have ht1c : t1 ∈ view oMid := he3
              have hlast' : (Sum.inl oMid :: rest).getLast? = some (Sum.inl o2) := by
                simpa [List.getLast?_cons_cons] using hlast
              obtain ⟨H, hH⟩ := walk_to_hops view (Sum.inl oMid :: rest) oMid o2 rfl hlast' hrest
              refine ⟨(o1, t1, oMid) :: H, rfl, ht1a, ht1c, ?_, ?_⟩
              · simp [walkEdges]
              · have hmono : ∀ {e1 e2 : Finset (Node p k × Node p k)}, e1 ⊆ e2 →
                    ∀ a b L, ValidHops view e1 a b L → ValidHops view e2 a b L := by
                  intro e1 e2 hsub a b L
                  induction L generalizing a with
                  | nil => intro h; exact h
                  | cons hd tl ih =>
                    rcases hd with ⟨ha, ht, hc⟩
                    rintro ⟨h1, h2, h3, h4, h5⟩
                    exact ⟨h1, h2, h3, hsub h4, ih hc h5⟩
                refine hmono ?_ oMid o2 H hH
                intro e he
                simp [walkEdges, he]

private def HopRelayOk {p k : ℕ} (o : Fin p) (y : Fin k → Bool) :
    List (Fin p × Fin k × Fin p) → Prop
  | [] => True
  | [_] => True
  | (_, t1, c1) :: (a2, t2, c2) :: rest =>
      (c1 = o → y t1 = y t2) ∧ HopRelayOk o y ((a2, t2, c2) :: rest)

private lemma hopRelayOk_congr {p k : ℕ} {view : Fin p → Finset (Fin k)}
    {edges : Finset (Node p k × Node p k)} {o : Fin p} {y1 y2 : Fin k → Bool}
    (hagree : ∀ t ∈ view o, y1 t = y2 t) :
    ∀ {o1 o2 : Fin p} (H : List (Fin p × Fin k × Fin p)),
      ValidHops view edges o1 o2 H → (HopRelayOk o y1 H ↔ HopRelayOk o y2 H)
  | _, _, [], _ => Iff.rfl
  | _, _, [_], _ => Iff.rfl
  | _, _, (_, t1, c1) :: (a2, t2, c2) :: rest, ⟨_, _, ht1c, _, ha2, ht2a, ht2c, he2, hrest⟩ => by
    have hih := hopRelayOk_congr hagree ((a2, t2, c2) :: rest) ⟨ha2, ht2a, ht2c, he2, hrest⟩
    simp only [HopRelayOk]
    refine and_congr ?_ hih
    constructor <;> intro h hco
    · subst hco
      rw [← hagree t1 ht1c, ← hagree t2 (ha2 ▸ ht2a)]
      exact h rfl
    · subst hco
      rw [hagree t1 ht1c, hagree t2 (ha2 ▸ ht2a)]
      exact h rfl

private lemma hopRelayOk_const {p k : ℕ} (o : Fin p) {y : Fin k → Bool} {val : Bool} :
    ∀ (H : List (Fin p × Fin k × Fin p)),
      (∀ a t c, (a, t, c) ∈ H → y t = val) → HopRelayOk o y H
  | [], _ => trivial
  | [_], _ => trivial
  | (a1, t1, c1) :: (a2, t2, c2) :: rest, hconst => by
    refine ⟨fun _ => ?_, hopRelayOk_const o ((a2, t2, c2) :: rest)
      (fun a t c hm => hconst a t c (List.mem_cons_of_mem _ hm))⟩
    rw [hconst a1 t1 c1 (List.mem_cons_self ..),
      hconst a2 t2 c2 (List.mem_cons_of_mem _ (List.mem_cons_self ..))]

private lemma hopRelayOk_chain {p k : ℕ} {y : Fin k → Bool} :
    ∀ (H : List (Fin p × Fin k × Fin p)) (hne : H ≠ []),
      (∀ o : Fin p, HopRelayOk o y H) →
      y (H.head hne).2.1 = y (H.getLast hne).2.1
  | [], hne, _ => absurd rfl hne
  | [(_, _, _)], _, _ => rfl
  | (_, t1, c1) :: (a2, t2, c2) :: rest, _, hall => by
    have hstep : y t1 = y t2 := (hall c1).1 rfl
    have htail : ∀ o : Fin p, HopRelayOk o y ((a2, t2, c2) :: rest) := fun o => (hall o).2
    have hih := hopRelayOk_chain ((a2, t2, c2) :: rest) (by simp) htail
    simpa using hstep.trans hih

private lemma validHops_head_mem {p k : ℕ} {view : Fin p → Finset (Fin k)}
    {edges : Finset (Node p k × Node p k)} {o1 o2 : Fin p} :
    ∀ (H : List (Fin p × Fin k × Fin p)) (hne : H ≠ []),
      ValidHops view edges o1 o2 H → (H.head hne).2.1 ∈ view o1
  | [], hne, _ => absurd rfl hne
  | (_, _, _) :: _, _, ⟨rfl, ht1, _, _, _⟩ => ht1

private lemma validHops_last_mem {p k : ℕ} {view : Fin p → Finset (Fin k)}
    {edges : Finset (Node p k × Node p k)} :
    ∀ (o1 o2 : Fin p) (H : List (Fin p × Fin k × Fin p)) (hne : H ≠ []),
      ValidHops view edges o1 o2 H → (H.getLast hne).2.1 ∈ view o2
  | _, _, [], hne, _ => absurd rfl hne
  | _, _, [(_, _, _)], _, ⟨_, _, ht2, _, rfl⟩ => ht2
  | _, o2, (_, _, c1) :: hd2 :: rest, _, ⟨_, _, _, _, hrest⟩ => by
    simpa using validHops_last_mem c1 o2 (hd2 :: rest) (by simp) hrest

private lemma validHops_mem_edges {p k : ℕ} {view : Fin p → Finset (Fin k)}
    {edges : Finset (Node p k × Node p k)} :
    ∀ (o1 o2 : Fin p) (H : List (Fin p × Fin k × Fin p)),
      ValidHops view edges o1 o2 H →
      ∀ a t c, (a, t, c) ∈ H → (Sum.inr (t, false), Sum.inr (t, true)) ∈ edges
  | _, _, [], _, _, _, _, hm => by cases hm
  | _, o2, (a1, t1, c1) :: rest, ⟨_, _, _, he, hrest⟩, a, t, c, hm => by
    rcases List.mem_cons.1 hm with hEq | htl
    · rcases Prod.mk.inj hEq with ⟨_, hEq2⟩
      rcases Prod.mk.inj hEq2 with ⟨rfl, _⟩
      exact he
    · exact validHops_mem_edges c1 o2 rest hrest a t c htl

private lemma readers_mem_left_right {n w p : ℕ} {hn : 0 < n} {owner : Fin n → Fin p}
    {left right : Fin p} (hown : ∀ i, owner i = left ∨ owner i = right)
    {z : Fin n} :
    let atSite := fun (i : Fin n) (j : Fin (w + 1)) =>
      (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let readers := fun z : Fin n => Finset.univ.filter (fun o : Fin p =>
      ∃ i : Fin n, owner i = o ∧ ∃ j : Fin (w + 1), atSite i j = z)
    1 < (readers z).card → left ∈ readers z ∧ right ∈ readers z := by
  intro atSite readers hcard
  have hsub : readers z ⊆ {left, right} := by
    intro o ho
    obtain ⟨i, hi, _⟩ := (Finset.mem_filter.1 ho).2
    rcases hown i with hl | hr
    · simp [← hi, hl]
    · simp [← hi, hr]
  constructor
  · by_contra hnotL
    have hsubR : readers z ⊆ {right} := by
      intro o ho
      have hor := hsub ho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hor ⊢
      rcases hor with rfl | rfl
      · exact absurd ho hnotL
      · rfl
    have hc : (readers z).card ≤ 1 := (Finset.card_le_card hsubR).trans (by simp)
    omega
  · by_contra hnotR
    have hsubL : readers z ⊆ {left} := by
      intro o ho
      have hor := hsub ho
      simp only [Finset.mem_insert, Finset.mem_singleton] at hor ⊢
      rcases hor with rfl | rfl
      · rfl
      · exact absurd ho hnotR
    have hc : (readers z).card ≤ 1 := (Finset.card_le_card hsubL).trans (by simp)
    omega

theorem main (n w p : ℕ) (hn : 0 < n) (owner : Fin n → Fin p)
    (left right : Fin p) (hlr : left ≠ right) (hown : ∀ i, owner i = left ∨ owner i = right)
    (k : ℕ) (view : Fin p → Finset (Fin k)) (ternary : Bool) :
    let W := Fin (w + 1) → Bool
    let atSite := fun (i : Fin n) (j : Fin (w + 1)) =>
      (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let readers := fun z : Fin n => Finset.univ.filter (fun o : Fin p =>
      ∃ i : Fin n, owner i = o ∧ ∃ j : Fin (w + 1), atSite i j = z)
    let boundary := Finset.univ.filter (fun site : Fin n => 1 < (readers site).card)
    let V := fun (k q : ℕ) (o : Fin p) (view : Fin p → Finset (Fin k)) =>
      Sum ({i : Fin n // owner i = o} × W) (Sum {t : Fin k // t ∈ view o} (Fin q))
    let represents := fun (k : ℕ) (view : Fin p → Finset (Fin k)) (ternary : Bool) =>
      ∃ (priv : Fin p → ℕ) (F : (o : Fin p) →
          Finset (Clause (V k (priv o) o view))),
        (ternary = true → ∀ o, ∀ C ∈ F o, C.card ≤ 3) ∧
        ∀ tab : Fin n → W → Bool,
          (∃ x : Fin n → Bool, ∀ i, tab i (fun off => x (atSite i off)) = true) ↔
          ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ localBits : Fin (priv o) → Bool,
            Satisfies
              (Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab r.1.val r.2)
                (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y bit.val) localBits))
              (↑(F o) : Set _)
    represents k view ternary ↔ ∀ S : Finset (Fin p), left ∈ S → right ∉ S →
      boundary.card ≤ (Finset.univ.filter (fun bit : Fin k =>
        (∃ inside ∈ S, bit ∈ view inside) ∧
        ∃ outside : Fin p, outside ∉ S ∧ bit ∈ view outside)).card := by
  classical
  intro W atSite readers boundary V represents
  constructor
  · rintro ⟨priv, F, _, hrep⟩ S hLS hRS
    let cutS : Finset (Fin k) := Finset.univ.filter (fun bit : Fin k =>
      (∃ inside ∈ S, bit ∈ view inside) ∧
      ∃ outside : Fin p, outside ∉ S ∧ bit ∈ view outside)
    let wordOf (f : {z : Fin n // z ∈ boundary} → Bool) : Fin n → Bool :=
      fun z => if hz : z ∈ boundary then f ⟨z, hz⟩ else false
    let tabOf (f : {z : Fin n // z ∈ boundary} → Bool) : Fin n → W → Bool :=
      fun i pat => decide (pat = fun off => wordOf f (atSite i off))
    have hex : ∀ f : {z : Fin n // z ∈ boundary} → Bool,
        ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ localBits : Fin (priv o) → Bool,
          Satisfies
            (Sum.elim (fun r : {row : Fin n // owner row = o} × W => tabOf f r.1.val r.2)
              (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y bit.val) localBits))
            (↑(F o) : Set _) := by
      intro f
      exact (hrep (tabOf f)).1 ⟨wordOf f, fun i => by simp [tabOf]⟩
    choose yOf hlocOf using hex
    let proj : ({z : Fin n // z ∈ boundary} → Bool) → ({t : Fin k // t ∈ cutS} → Bool) :=
      fun f t => yOf f t.val
    have hinj : Function.Injective proj := by
      intro f1 f2 hproj
      let tab' : Fin n → W → Bool :=
        fun i pat => if owner i = left then tabOf f1 i pat else tabOf f2 i pat
      let y' : Fin k → Bool :=
        fun t => if ∃ inside ∈ S, t ∈ view inside then yOf f1 t else yOf f2 t
      have hsat' : ∀ o : Fin p, ∃ localBits : Fin (priv o) → Bool,
          Satisfies
            (Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab' r.1.val r.2)
              (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y' bit.val) localBits))
            (↑(F o) : Set _) := by
        intro o
        by_cases hoS : o ∈ S
        · obtain ⟨loc, hloc⟩ := hlocOf f1 o
          refine ⟨loc, ?_⟩
          have heqA :
              Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab' r.1.val r.2)
                (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y' bit.val) loc) =
              Sum.elim (fun r : {row : Fin n // owner row = o} × W => tabOf f1 r.1.val r.2)
                (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => yOf f1 bit.val) loc) := by
            funext v
            rcases v with ⟨⟨i, hi⟩, pat⟩ | (⟨t, ht⟩ | j)
            · simp only [Sum.elim_inl, tab']
              have hoR : o ≠ right := fun h => hRS (h ▸ hoS)
              have hiL : owner i = left := by
                rcases hown i with hl | hr
                · exact hl
                · exact absurd (hi.symm.trans hr) hoR
              simp [hiL]
            · simp only [Sum.elim_inr, Sum.elim_inl, y']
              have hexS : ∃ inside ∈ S, t ∈ view inside := ⟨o, hoS, ht⟩
              simp [hexS]
            · rfl
          rw [heqA]
          exact hloc
        · obtain ⟨loc, hloc⟩ := hlocOf f2 o
          refine ⟨loc, ?_⟩
          have heqA :
              Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab' r.1.val r.2)
                (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y' bit.val) loc) =
              Sum.elim (fun r : {row : Fin n // owner row = o} × W => tabOf f2 r.1.val r.2)
                (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => yOf f2 bit.val) loc) := by
            funext v
            rcases v with ⟨⟨i, hi⟩, pat⟩ | (⟨t, ht⟩ | j)
            · simp only [Sum.elim_inl, tab']
              have hoL : o ≠ left := fun h => hoS (h ▸ hLS)
              have hiNL : owner i ≠ left := fun h => hoL (hi.symm.trans h)
              simp [hiNL]
            · simp only [Sum.elim_inr, Sum.elim_inl, y']
              by_cases hexS : ∃ inside ∈ S, t ∈ view inside
              · simp only [hexS, ↓reduceIte]
                have htC : t ∈ cutS := Finset.mem_filter.2
                  ⟨Finset.mem_univ t, hexS, ⟨o, hoS, ht⟩⟩
                exact congrFun hproj ⟨t, htC⟩
              · simp [hexS]
            · rfl
          rw [heqA]
          exact hloc
      obtain ⟨x, hx⟩ := (hrep tab').2 ⟨y', hsat'⟩
      funext ⟨z, hz⟩
      have hcard : 1 < (readers z).card := (Finset.mem_filter.1 hz).2
      obtain ⟨hLmem, hRmem⟩ := readers_mem_left_right (hn := hn) hown hcard
      obtain ⟨i1, hi1, j1, hj1⟩ := (Finset.mem_filter.1 hLmem).2
      obtain ⟨i2, hi2, j2, hj2⟩ := (Finset.mem_filter.1 hRmem).2
      have h1 := hx i1
      simp only [tab', hi1, ↓reduceIte, tabOf, decide_eq_true_eq] at h1
      have hx1 : x z = f1 ⟨z, hz⟩ := by
        have h1j := congrFun h1 j1
        have hj1' : atSite i1 j1 = z := hj1
        rw [hj1'] at h1j
        simpa [wordOf, hz] using h1j
      have h2 := hx i2
      have hi2NL : owner i2 ≠ left := by rw [hi2]; exact hlr.symm
      simp only [tab', hi2NL, ↓reduceIte, tabOf, decide_eq_true_eq] at h2
      have hx2 : x z = f2 ⟨z, hz⟩ := by
        have h2j := congrFun h2 j2
        have hj2' : atSite i2 j2 = z := hj2
        rw [hj2'] at h2j
        simpa [wordOf, hz] using h2j
      exact hx1.symm.trans hx2
    have hcardLe := Fintype.card_le_of_injective proj hinj
    simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hcardLe
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).1 hcardLe
  · intro hcut
    let B := boundary.card
    let E : Finset (Node p k × Node p k) :=
      Finset.univ.filter (fun e => isEdge view e.1 e.2)
    have hasym : ∀ e ∈ E, (e.2, e.1) ∉ E := by
      intro e he hrev
      have h1 := (Finset.mem_filter.1 he).2
      have h2 := (Finset.mem_filter.1 hrev).2
      rcases e with ⟨u, v⟩
      rcases u with o | ⟨t, b⟩ <;> rcases v with o' | ⟨t', b'⟩
      · cases h1
      · cases b' <;> simp [isEdge] at h1 h2
      · cases b <;> simp [isEdge] at h1 h2
      · cases b <;> cases b' <;> simp [isEdge] at h1 h2
    have hGcut : ∀ R : Finset (Node p k), Sum.inl left ∈ R → Sum.inl right ∉ R →
        B ≤ (E.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)).card := by
      intro R hLR hRR
      let S : Finset (Fin p) := Finset.univ.filter (fun o => Sum.inl o ∈ R)
      have hLS : left ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ left, hLR⟩
      have hRS : right ∉ S := fun h => hRR (Finset.mem_filter.1 h).2
      let cutS : Finset (Fin k) := Finset.univ.filter (fun bit : Fin k =>
        (∃ inside ∈ S, bit ∈ view inside) ∧
        ∃ outside : Fin p, outside ∉ S ∧ bit ∈ view outside)
      have hBcut : B ≤ cutS.card := hcut S hLS hRS
      let C := E.filter (fun e => e.1 ∈ R ∧ e.2 ∉ R)
      have hsubImg : cutS.image some ⊆ C.image edgeBit := by
        intro mt hmt
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hmt
        rcases (Finset.mem_filter.1 ht).2 with ⟨⟨o1, ho1S, ht1⟩, ⟨o2, ho2S, ht2⟩⟩
        have ho1R : Sum.inl o1 ∈ R := (Finset.mem_filter.1 ho1S).2
        have ho2R : Sum.inl o2 ∉ R := fun h => ho2S (Finset.mem_filter.2 ⟨Finset.mem_univ o2, h⟩)
        by_cases hInR : Sum.inr (t, false) ∈ R
        · by_cases hOutR : Sum.inr (t, true) ∈ R
          · refine Finset.mem_image.2 ⟨(Sum.inr (t, true), Sum.inl o2), ?_, rfl⟩
            exact Finset.mem_filter.2
              ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ht2⟩, hOutR, ho2R⟩
          · refine Finset.mem_image.2 ⟨(Sum.inr (t, false), Sum.inr (t, true)), ?_, rfl⟩
            exact Finset.mem_filter.2
              ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, hInR, hOutR⟩
        · refine Finset.mem_image.2 ⟨(Sum.inl o1, Sum.inr (t, false)), ?_, rfl⟩
          exact Finset.mem_filter.2
            ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ht1⟩, ho1R, hInR⟩
      have h1 : cutS.card = (cutS.image some).card :=
        (Finset.card_image_of_injective cutS (Option.some_injective (Fin k))).symm
      have h2 : (cutS.image some).card ≤ (C.image edgeBit).card := Finset.card_le_card hsubImg
      have h3 : (C.image edgeBit).card ≤ C.card := Finset.card_image_le
      exact hBcut.trans (h1 ▸ h2.trans h3)
    have hst : (Sum.inl left : Node p k) ≠ Sum.inl right := fun h => hlr (Sum.inl.inj h)
    obtain ⟨A, hAflow⟩ := exists_flow hasym hst hGcut B (le_refl B)
    obtain ⟨P, hPspec, hPdisj⟩ := flow_decompose hst B A hAflow
    have hHex : ∀ b : Fin B, ∃ H : List (Fin p × Fin k × Fin p),
        ValidHops view (walkEdges (P b)) left right H := by
      intro b
      have hSP := (hPspec b).1
      exact walk_to_hops view (P b) left right hSP.1 hSP.2.1
        (walk_mono (adj1 := fun u v => (u, v) ∈ E) (adj2 := isEdge view)
          (fun _ _ he => (Finset.mem_filter.1 he).2) (P b) hSP.2.2.1)
    choose H hHvalid using hHex
    have hHne : ∀ b : Fin B, H b ≠ [] := by
      intro b hemp
      have hv := hHvalid b
      rw [hemp] at hv
      exact hlr hv
    let firstBit (b : Fin B) : Fin k := (H b).head (hHne b) |>.2.1
    let lastBit (b : Fin B) : Fin k := (H b).getLast (hHne b) |>.2.1
    have hFirstMem : ∀ b : Fin B, firstBit b ∈ view left :=
      fun b => validHops_head_mem (H b) (hHne b) (hHvalid b)
    have hLastMem : ∀ b : Fin B, lastBit b ∈ view right :=
      fun b => validHops_last_mem left right (H b) (hHne b) (hHvalid b)
    have hBitDisj : ∀ b1 b2 : Fin B, ∀ a1 c1 a2 c2 t,
        (a1, t, c1) ∈ H b1 → (a2, t, c2) ∈ H b2 → b1 = b2 := by
      intro b1 b2 a1 c1 a2 c2 t hm1 hm2
      by_contra hne
      have he1 := validHops_mem_edges left right (H b1) (hHvalid b1) a1 t c1 hm1
      have he2 := validHops_mem_edges left right (H b2) (hHvalid b2) a2 t c2 hm2
      exact Finset.disjoint_left.1 (hPdisj b1 b2 hne) he1 he2
    let eB : {z : Fin n // z ∈ boundary} ≃ Fin B :=
      Fintype.equivFinOfCardEq (Fintype.card_coe boundary)
    let zOf (b : Fin B) : Fin n := (eB.symm b).val
    let Pred (o : Fin p) (tabO : {i : Fin n // owner i = o} × W → Bool)
        (yO : {t : Fin k // t ∈ view o} → Bool) : Prop :=
      let yExt : Fin k → Bool := fun t => if h : t ∈ view o then yO ⟨t, h⟩ else false
      (∀ b : Fin B, HopRelayOk o yExt (H b)) ∧
      (o = left → ∃ xL : Fin n → Bool,
        (∀ i : {i : Fin n // owner i = o}, tabO (i, fun off => xL (atSite i.val off)) = true) ∧
        (∀ b : Fin B, yExt (firstBit b) = xL (zOf b))) ∧
      (o = right → ∃ xR : Fin n → Bool,
        (∀ i : {i : Fin n // owner i = o}, tabO (i, fun off => xR (atSite i.val off)) = true) ∧
        (∀ b : Fin B, yExt (lastBit b) = xR (zOf b)))
    have hEnc : ∀ o : Fin p,
        ∃ (q : ℕ) (Fo : Finset (Clause (V k q o view))),
          (∀ C ∈ Fo, C.card ≤ 3) ∧
          ∀ (tabO : {i : Fin n // owner i = o} × W → Bool) (yO : {t : Fin k // t ∈ view o} → Bool),
            Pred o tabO yO ↔ ∃ loc : Fin q → Bool,
              Satisfies (Sum.elim tabO (Sum.elim yO loc)) (↑Fo : Set _) :=
      fun o => exists_3cnf_assoc (Pred o)
    choose priv F hFcard hFspec using hEnc
    refine ⟨priv, F, fun _ o C hC => hFcard o C hC, ?_⟩
    intro tab
    have hsat_iff : ∀ (y : Fin k → Bool) (o : Fin p),
        (∃ loc : Fin (priv o) → Bool,
          Satisfies
            (Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab r.1.val r.2)
              (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y bit.val) loc))
            (↑(F o) : Set _)) ↔
        Pred o (fun r => tab r.1.val r.2) (fun bit => y bit.val) :=
      fun y o => (hFspec o (fun r => tab r.1.val r.2) (fun bit => y bit.val)).symm
    constructor
    · rintro ⟨x, hx⟩
      let y : Fin k → Bool := fun t =>
        if h : ∃ b : Fin B, ∃ a c, (a, t, c) ∈ H b then x (zOf (Classical.choose h)) else false
      have hy_on : ∀ (b : Fin B) (a c : Fin p) (t : Fin k), (a, t, c) ∈ H b → y t = x (zOf b) := by
        intro b a c t hm
        have hex : ∃ b' : Fin B, ∃ a' c', (a', t, c') ∈ H b' := ⟨b, a, c, hm⟩
        simp only [y, hex, ↓reduceDIte]
        obtain ⟨a', c', hm'⟩ := Classical.choose_spec hex
        have hbeq : Classical.choose hex = b := hBitDisj _ _ a' c' a c t hm' hm
        rw [hbeq]
      refine ⟨y, fun o => (hsat_iff y o).2 ?_⟩
      let yExt : Fin k → Bool := fun t => if t ∈ view o then y t else false
      have hagree : ∀ t ∈ view o, yExt t = y t := fun t ht => by simp [yExt, ht]
      refine ⟨?_, ?_, ?_⟩
      · intro b
        exact (hopRelayOk_congr hagree (H b) (hHvalid b)).2
          (hopRelayOk_const o (H b) (fun a t c hm => hy_on b a c t hm))
      · intro hoL
        refine ⟨x, fun i => hx i.val, fun b => ?_⟩
        have hmem : firstBit b ∈ view o := hoL ▸ hFirstMem b
        simp only [hmem, ↓reduceDIte]
        have hhd : (H b).head (hHne b) ∈ H b := List.head_mem (hHne b)
        exact hy_on b ((H b).head (hHne b)).1 ((H b).head (hHne b)).2.2 (firstBit b) hhd
      · intro hoR
        refine ⟨x, fun i => hx i.val, fun b => ?_⟩
        have hmem : lastBit b ∈ view o := hoR ▸ hLastMem b
        simp only [hmem, ↓reduceDIte]
        have hgl : (H b).getLast (hHne b) ∈ H b := List.getLast_mem (hHne b)
        exact hy_on b ((H b).getLast (hHne b)).1 ((H b).getLast (hHne b)).2.2 (lastBit b) hgl
    · rintro ⟨y, hy⟩
      have hPred : ∀ o : Fin p, Pred o (fun r => tab r.1.val r.2) (fun bit => y bit.val) :=
        fun o => (hsat_iff y o).1 (hy o)
      have hRelay : ∀ (b : Fin B) (o : Fin p), HopRelayOk o y (H b) := by
        intro b o
        have hagree : ∀ t ∈ view o, (if t ∈ view o then y t else false) = y t :=
          fun t ht => by simp [ht]
        exact (hopRelayOk_congr hagree (H b) (hHvalid b)).1 ((hPred o).1 b)
      have hChain : ∀ b : Fin B, y (firstBit b) = y (lastBit b) :=
        fun b => hopRelayOk_chain (H b) (hHne b) (hRelay b)
      obtain ⟨xL, hxLtab, hxLbits⟩ := (hPred left).2.1 rfl
      obtain ⟨xR, hxRtab, hxRbits⟩ := (hPred right).2.2 rfl
      have hAgreeBnd : ∀ z ∈ boundary, xL z = xR z := by
        intro z hz
        let b := eB ⟨z, hz⟩
        have hzb : zOf b = z := congrArg Subtype.val (eB.symm_apply_apply ⟨z, hz⟩)
        have hL1 : y (firstBit b) = xL (zOf b) := by
          have h := hxLbits b
          simpa [hFirstMem b] using h
        have hR1 : y (lastBit b) = xR (zOf b) := by
          have h := hxRbits b
          simpa [hLastMem b] using h
        rw [← hzb, ← hL1, ← hR1]
        exact hChain b
      let x : Fin n → Bool := fun z => if left ∈ readers z then xL z else xR z
      refine ⟨x, fun i => ?_⟩
      rcases hown i with hiL | hiR
      · have hwin : (fun off => x (atSite i off)) = (fun off => xL (atSite i off)) := by
          funext off
          have hmem : left ∈ readers (atSite i off) :=
            Finset.mem_filter.2 ⟨Finset.mem_univ left, ⟨i, hiL, ⟨off, rfl⟩⟩⟩
          simp [x, hmem]
        rw [hwin]
        exact hxLtab ⟨i, hiL⟩
      · have hwin : (fun off => x (atSite i off)) = (fun off => xR (atSite i off)) := by
          funext off
          let z := atSite i off
          change (if left ∈ readers z then xL z else xR z) = xR z
          by_cases hLmem : left ∈ readers z
          · have hRmem : right ∈ readers z :=
              Finset.mem_filter.2 ⟨Finset.mem_univ right, ⟨i, hiR, ⟨off, rfl⟩⟩⟩
            have hsub : ({left, right} : Finset (Fin p)) ⊆ readers z := by
              intro o ho
              simp only [Finset.mem_insert, Finset.mem_singleton] at ho
              rcases ho with rfl | rfl
              · exact hLmem
              · exact hRmem
            have hcard : 1 < (readers z).card := by
              have h2 : ({left, right} : Finset (Fin p)).card = 2 := Finset.card_pair hlr
              have hle := Finset.card_le_card hsub
              omega
            have hzBnd : z ∈ boundary := Finset.mem_filter.2 ⟨Finset.mem_univ z, hcard⟩
            simp only [hLmem, ↓reduceIte]
            exact hAgreeBnd z hzBnd
          · simp only [hLmem, ↓reduceIte]
        rw [hwin]
        exact hxRtab ⟨i, hiR⟩

end PEqualNP.Outside.L_pcx_241_aux

theorem PEqualNP.Outside.L_pcx_241 :
∀ (n w p : ℕ) (hn : 0 < n) (owner : Fin n → Fin p),
  let W := Fin (w + 1) → Bool
  let atSite := fun (i : Fin n) (j : Fin (w+1)) =>
    (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let readers := fun z : Fin n => Finset.univ.filter (fun o : Fin p =>
    ∃ i : Fin n, owner i = o ∧ ∃ j : Fin (w+1), atSite i j = z)
  let boundary := Finset.univ.filter (fun site : Fin n => 1 < (readers site).card)
  let V := fun (k q : ℕ) (o : Fin p) (view : Fin p → Finset (Fin k)) =>
    Sum ({i : Fin n // owner i = o} × W) (Sum {t : Fin k // t ∈ view o} (Fin q))
  let represents := fun (k : ℕ) (view : Fin p → Finset (Fin k)) (ternary : Bool) =>
    ∃ (priv : Fin p → ℕ) (F : (o : Fin p) →
        Finset (PEqualNP.ProofComplexity.Clause (V k (priv o) o view))),
      (ternary = true → ∀ o, ∀ C ∈ F o, C.card ≤ 3) ∧
      ∀ tab : Fin n → W → Bool,
        (∃ x : Fin n → Bool, ∀ i, tab i (fun off => x (atSite i off)) = true) ↔
        ∃ y : Fin k → Bool, ∀ o : Fin p, ∃ localBits : Fin (priv o) → Bool,
          PEqualNP.ProofComplexity.Satisfies
            (Sum.elim (fun r : {row : Fin n // owner row = o} × W => tab r.1.val r.2)
              (Sum.elim (fun bit : {t : Fin k // t ∈ view o} => y bit.val) localBits)) (↑(F o) : Set _)
  ∀ (left right : Fin p), left ≠ right → (∀ i, owner i = left ∨ owner i = right) →
    ∀ (k : ℕ) (view : Fin p → Finset (Fin k)) (ternary : Bool),
      represents k view ternary ↔ ∀ S : Finset (Fin p), left ∈ S → right ∉ S →
        boundary.card ≤ (Finset.univ.filter (fun bit : Fin k =>
          (∃ inside ∈ S, bit ∈ view inside) ∧
          ∃ outside : Fin p, outside ∉ S ∧ bit ∈ view outside)).card := by
  intro n w p hn owner W atSite readers boundary V represents left right hlr hown k view ternary
  exact PEqualNP.Outside.L_pcx_241_aux.main n w p hn owner left right hlr hown k view ternary
