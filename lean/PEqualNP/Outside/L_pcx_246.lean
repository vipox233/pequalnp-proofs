import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_246_aux

open PEqualNP.ProofComplexity Finset

theorem exists_3cnf_single_list {U : Type} [DecidableEq U] (L : List (U × Bool)) :
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
      · refine ⟨(Sum.inr ⟨L.length, Nat.lt_succ_self L.length⟩, false), Finset.mem_singleton_self _, ?_⟩
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
        have hs := ha cStart (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
        obtain ⟨lit, hlit, hsat⟩ := hs
        rw [Finset.mem_singleton] at hlit
        subst hlit
        simpa using hsat
      have haEnd : a ⟨L.length, Nat.lt_succ_self L.length⟩ = false := by
        have hs := ha cEnd (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
        obtain ⟨lit, hlit, hsat⟩ := hs
        rw [Finset.mem_singleton] at hlit
        subst hlit
        simpa using hsat
      have hind : ∀ (j : ℕ) (hj : j ≤ L.length), a ⟨j, Nat.lt_succ_of_le hj⟩ = true := by
        intro j
        induction j with
        | zero =>
          intro _
          exact ha0
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

theorem exists_3cnf_of_pred {U : Type} [Fintype U] [DecidableEq U]
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
        Finset.mem_biUnion.2 ⟨idx, Finset.mem_univ _, Finset.mem_image.2 ⟨C0, Finset.mem_coe.1 hC0, rfl⟩⟩
      obtain ⟨lit', hlit', hsat⟩ := ha _ (Finset.mem_coe.2 hmem)
      obtain ⟨lit, hlit, rfl⟩ := Finset.mem_image.1 hlit'
      refine ⟨lit, hlit, ?_⟩
      rcases lit with ⟨u | j, b⟩
      · simpa [liftLit] using hsat
      · simpa [liftLit] using hsat

theorem main (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3)
    (hcov : ∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
      ∃ d : Fin (w + 1), (⟨(r.val + d.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = z)
    (k : Fin 3 → ℕ) (ternary : Bool)
    (code : (Fin n → Bool) → (e : Fin 3) → Fin (k e) → Bool) :
    let Word := Fin n → Bool
    let Pattern := Fin (w + 1) → Bool
    let pos := fun (r : Fin n) (d : Fin (w + 1)) =>
      (⟨(r.val + d.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
    let window := fun (x : Word) (r : Fin n) (d : Fin (w + 1)) => x (pos r d)
    let next := fun e : Fin 3 => e + 1
    let Msg := (e : Fin 3) → Fin (k e) → Bool
    let Table := Fin n → Pattern → Bool
    let pins := fun (word : Word) (row : Fin n) (pat : Pattern) => decide (pat = window word row)
    let V := fun (p : Fin 3) (q : ℕ) =>
      Sum ({r : Fin n // owner r = p} × Pattern)
        (Sum ((e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val)) (Fin q))
    (∃ (priv : Fin 3 → ℕ) (F : (p : Fin 3) → Finset (Clause (V p (priv p)))),
      let accepts := fun (tab : Table) (y : Msg) => ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
        Satisfies
          (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => tab h.1.val h.2)
            (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
              y bit.1.val bit.2) a)) (↑(F p) : Set _)
      (ternary = true → ∀ p, ∀ C ∈ F p, C.card ≤ 3) ∧
      (∀ T : Table, (∃ x : Word, ∀ i, T i (window x i) = true) ↔ ∃ transcript, accepts T transcript) ∧
      ∀ x : Word, accepts (pins x) (code x)) ↔
    ∀ chosen : Fin 3 → Word,
      (∀ e : Fin 3, code (chosen e) e = code (chosen (next e)) e) →
      ∀ party : Fin 3, chosen party = chosen 0 := by
  intro Word Pattern pos window next Msg Table pins V
  constructor
  · rintro ⟨priv, F, htern, hiff, hpins⟩ chosen hagree
    let T : Table := fun r pat => pins (chosen (owner r)) r pat
    let y : Msg := fun e => code (chosen e) e
    have hacc : ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
        Satisfies
          (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => T h.1.val h.2)
            (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
              y bit.1.val bit.2) a)) (↑(F p) : Set _) := by
      intro p
      obtain ⟨a, ha⟩ := hpins (chosen p) p
      refine ⟨a, ?_⟩
      have hass :
          Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => T h.1.val h.2)
            (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
              y bit.1.val bit.2) a) =
          Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => pins (chosen p) h.1.val h.2)
            (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
              code (chosen p) bit.1.val bit.2) a) := by
        funext v
        rcases v with ⟨⟨i, hi⟩, pat⟩ | (⟨⟨e, he⟩, j⟩ | q)
        · simp [T, hi]
        · simp only [Sum.elim_inr, Sum.elim_inl, y]
          rcases he with rfl | rfl
          · rfl
          · exact congrFun (hagree e) j
        · rfl
      rw [hass]
      exact ha
    obtain ⟨x, hx⟩ := (hiff T).2 ⟨y, hacc⟩
    have heqx : ∀ party : Fin 3, chosen party = x := by
      intro party
      funext z
      obtain ⟨r, hr, d, hd⟩ := hcov party z
      have htr := hx r
      simp only [T, pins, hr, decide_eq_true_eq] at htr
      have hfun := congrFun htr d
      dsimp only [window, pos] at hfun
      rw [hd] at hfun
      exact hfun.symm
    intro party
    rw [heqx party, heqx 0]
  · intro huniq
    classical
    let U : Fin 3 → Type := fun p =>
      Sum ({r : Fin n // owner r = p} × Pattern)
        ((e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val))
    let P : (p : Fin 3) → (U p → Bool) → Prop := fun p α =>
      ∃ x : Word,
        (∀ r : {i : Fin n // owner i = p}, α (Sum.inl (r, window x r.val)) = true) ∧
        (∀ bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val),
          α (Sum.inr bit) = code x bit.1.val bit.2)
    have hch : ∀ p : Fin 3, ∃ (q : ℕ) (F : Finset (Clause (U p ⊕ Fin q))),
        (∀ C ∈ F, C.card ≤ 3) ∧
        ∀ α : U p → Bool,
          P p α ↔ ∃ a : Fin q → Bool, Satisfies (Sum.elim α a) (↑F : Set (Clause (U p ⊕ Fin q))) :=
      fun p => exists_3cnf_of_pred (P p)
    choose priv F0 hF0card hF0spec using hch
    let eV : (p : Fin 3) → (U p ⊕ Fin (priv p)) ≃ V p (priv p) := fun p =>
      { toFun := fun v => match v with
          | Sum.inl (Sum.inl h) => Sum.inl h
          | Sum.inl (Sum.inr b) => Sum.inr (Sum.inl b)
          | Sum.inr j => Sum.inr (Sum.inr j)
        invFun := fun v => match v with
          | Sum.inl h => Sum.inl (Sum.inl h)
          | Sum.inr (Sum.inl b) => Sum.inl (Sum.inr b)
          | Sum.inr (Sum.inr j) => Sum.inr j
        left_inv := fun v => by rcases v with (h | b) | j <;> rfl
        right_inv := fun v => by rcases v with h | (b | j) <;> rfl }
    let liftC (p : Fin 3) (C : Clause (U p ⊕ Fin (priv p))) : Clause (V p (priv p)) :=
      C.image (fun lit => (eV p lit.1, lit.2))
    let F : (p : Fin 3) → Finset (Clause (V p (priv p))) := fun p => (F0 p).image (liftC p)
    have hacc_iff : ∀ (T : Table) (y : Msg) (p : Fin 3),
        (∃ a : Fin (priv p) → Bool,
          Satisfies
            (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => T h.1.val h.2)
              (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
                y bit.1.val bit.2) a)) (↑(F p) : Set _)) ↔
        P p (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => T h.1.val h.2)
          (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) => y bit.1.val bit.2)) := by
      intro T y p
      rw [hF0spec p]
      refine exists_congr (fun a => ?_)
      have hcomp : ∀ v : U p ⊕ Fin (priv p),
          Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => T h.1.val h.2)
            (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
              y bit.1.val bit.2) a) (eV p v) =
          Sum.elim (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => T h.1.val h.2)
            (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) => y bit.1.val bit.2))
            a v := by
        intro v
        rcases v with (h | b) | j <;> rfl
      constructor
      · intro hsat C0 hC0
        have hmem : liftC p C0 ∈ F p := Finset.mem_image.2 ⟨C0, Finset.mem_coe.1 hC0, rfl⟩
        obtain ⟨lit', hlit', hl⟩ := hsat _ (Finset.mem_coe.2 hmem)
        obtain ⟨lit, hlit, rfl⟩ := Finset.mem_image.1 hlit'
        refine ⟨lit, hlit, ?_⟩
        simpa [hcomp lit.1] using hl
      · intro hsat C hC
        obtain ⟨C0, hC0, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hC)
        obtain ⟨lit, hlit, hl⟩ := hsat C0 (Finset.mem_coe.2 hC0)
        refine ⟨(eV p lit.1, lit.2), Finset.mem_image.2 ⟨lit, hlit, rfl⟩, ?_⟩
        simpa [hcomp lit.1] using hl
    refine ⟨priv, F, ?_, ?_, ?_⟩
    · intro _ p C hC
      obtain ⟨C0, hC0, rfl⟩ := Finset.mem_image.1 hC
      exact Finset.card_image_le.trans (hF0card p C0 hC0)
    · intro T
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨code x, fun p => (hacc_iff T (code x) p).2 ?_⟩
        exact ⟨x, fun r => hx r.val, fun _ => rfl⟩
      · rintro ⟨y, hy⟩
        have hP : ∀ p : Fin 3,
            ∃ x : Word,
              (∀ r : {i : Fin n // owner i = p}, T r.val (window x r.val) = true) ∧
              (∀ bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val),
                y bit.1.val bit.2 = code x bit.1.val bit.2) :=
          fun p => (hacc_iff T y p).1 (hy p)
        choose chosen hrow hchan using hP
        have hagree : ∀ e : Fin 3, code (chosen e) e = code (chosen (next e)) e := by
          intro e
          funext j
          have h1 := hchan e ⟨⟨e, Or.inl rfl⟩, j⟩
          have h2 := hchan (next e) ⟨⟨e, Or.inr rfl⟩, j⟩
          exact h1.symm.trans h2
        have hall_eq := huniq chosen hagree
        refine ⟨chosen 0, fun i => ?_⟩
        have hri := hrow (owner i) ⟨i, rfl⟩
        rwa [hall_eq (owner i)] at hri
    · intro x p
      refine (hacc_iff (pins x) (code x) p).2 ⟨x, fun r => ?_, fun _ => rfl⟩
      simp [pins]

end PEqualNP.Outside.L_pcx_246_aux

theorem PEqualNP.Outside.L_pcx_246 :
∀ (n w : ℕ) (hn : 0 < n) (owner : Fin n → Fin 3),
  let Word := Fin n → Bool
  let Pattern := Fin (w+1) → Bool
  let pos := fun (r : Fin n) (d : Fin (w+1)) =>
    (⟨(r.val + d.val) % n, Nat.mod_lt _ hn⟩ : Fin n)
  let window := fun (x : Word) (r : Fin n) (d : Fin (w+1)) => x (pos r d)
  (∀ (party : Fin 3) (z : Fin n), ∃ r : Fin n, owner r = party ∧
    ∃ d : Fin (w+1), pos r d = z) →
  ∀ (k : Fin 3 → ℕ) (ternary : Bool),
    let next := fun e : Fin 3 => e + 1
    let Msg := (e : Fin 3) → Fin (k e) → Bool
    let Table := Fin n → Pattern → Bool
    let pins := fun (word : Word) (row : Fin n) (pat : Pattern) => decide (pat = window word row)
    let V := fun (p : Fin 3) (q : ℕ) =>
      Sum ({r : Fin n // owner r = p} × Pattern)
        (Sum ((e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val)) (Fin q))
    ∀ code : Word → Msg,
      (∃ (priv : Fin 3 → ℕ) (F : (p : Fin 3) → Finset (PEqualNP.ProofComplexity.Clause (V p (priv p)))),
        let accepts := fun (tab : Table) (y : Msg) => ∀ p : Fin 3, ∃ a : Fin (priv p) → Bool,
          PEqualNP.ProofComplexity.Satisfies
            (Sum.elim (fun h : {i : Fin n // owner i = p} × Pattern => tab h.1.val h.2)
              (Sum.elim (fun bit : (e : {t : Fin 3 // t = p ∨ next t = p}) × Fin (k e.val) =>
                y bit.1.val bit.2) a)) (↑(F p) : Set _)
        (ternary = true → ∀ p, ∀ C ∈ F p, C.card ≤ 3) ∧
        (∀ T : Table, (∃ x : Word, ∀ i, T i (window x i) = true) ↔ ∃ transcript, accepts T transcript) ∧
        ∀ x : Word, accepts (pins x) (code x)) ↔
      ∀ chosen : Fin 3 → Word,
        (∀ e : Fin 3, code (chosen e) e = code (chosen (next e)) e) →
        ∀ party : Fin 3, chosen party = chosen 0 := by
  intro n w hn owner Word Pattern pos window hcov k ternary next Msg Table pins V code
  exact PEqualNP.Outside.L_pcx_246_aux.main n w hn owner hcov k ternary code
