import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_472_aux.Bridge

open Relation Classical

abbrev Walk (E : ℕ → ℕ → Prop) := Relation.ReflTransGen E

theorem walk_le {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {i j : ℕ} (w : Walk E i j) : j ≤ i := by
  induction w with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (Nat.le_of_lt (dec e)).trans ih

theorem walk_sub {E E' : ℕ → ℕ → Prop} (sub : ∀ {i j}, E i j → E' i j)
    {i j : ℕ} (w : Walk E i j) : Walk E' i j := by
  induction w with
  | refl => exact .refl
  | tail _ e ih => exact .tail ih (sub e)

theorem clash {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    {A : ℕ → Prop} (ac : A c) {x : ℕ}
    (wc : Walk (fun i j => E i j ∧ A j) c x) (wd : Walk E d x) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ A m ∧ Walk E c m ∧ Walk E d m := by
  induction wc with
  | refl =>
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · exact False.elim (ne e)
    · have lt : q < r := (walk_le dec wq).trans_lt (dec rd)
      exact ⟨r, q, c, Or.inl rfl, Or.inr wq, rc, eq, (Ne.symm (ne_of_lt lt)),
        ac, .refl, wd⟩
  | @tail u v wu he ih =>
    have wcu : Walk E c u := walk_sub (fun h => h.1) wu
    have lu : u < r := (walk_le dec wcu).trans_lt (dec rc)
    rcases wd.cases_tail with e | ⟨q, wq, eq⟩
    · subst v
      exact ⟨u, r, d, Or.inr wcu, Or.inl rfl, he.1, rd, ne_of_lt lu, he.2,
        .tail wcu he.1, .refl⟩
    · by_cases hp : u = q
      · subst q
        exact ih wq
      · exact ⟨u, q, v, Or.inr wcu, Or.inr wq, he.1, eq, hp, he.2,
          .tail wcu he.1, wd⟩

def Common (E : ℕ → ℕ → Prop) (c d : ℕ) (u : ℕ) : Prop :=
  Walk E c u ∧ Walk E d u

def Forced {α κ : Type} (bad : α → κ → Prop) (point : κ → α → Prop) (side : α → Bool) (a : α) : Prop :=
  (∃ k, point k a ∧ ∃ b, point k b ∧ side b ≠ side a) ∨
  (∀ k, bad a k → ∀ b, point k b → side b ≠ side a)

theorem criticalSide {α κ : Type} {E : ℕ → ℕ → Prop} {c d : ℕ}
    (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
    (B : α → ℕ → Prop) (side : α → Bool)
    (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
    (branch : ∀ a, B a (if side a then c else d))
    (route : ∀ a i, B a i →
      ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
    {a k} (ha : point k a) :
    Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  obtain ⟨j, hj, w⟩ := route a _ (branch a)
  have eq := (one ha j).1 hj
  simpa [eq] using w

theorem forced_common {α κ : Type} {E : ℕ → ℕ → Prop} {c d : ℕ}
    (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
    (B : α → ℕ → Prop) (side : α → Bool)
    (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
    (branch : ∀ a, B a (if side a then c else d))
    (route : ∀ a i, B a i →
      ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
    (points : ∀ k, ∃ a, point k a)
    {a} (ha : Forced bad point side a) :
    ∃ k, bad a k ∧ Common E c d (leaf k) ∧
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
  have mk : ∀ {k b}, bad a k →
      Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) →
      point k b → side b ≠ side a →
      ∃ k, bad a k ∧ Common E c d (leaf k) ∧
        Walk (fun u v => E u v ∧ B a v) (if side a then c else d) (leaf k) := by
    intro k b bk wa pb hn
    have wb := criticalSide bad point leaf B side one branch route pb
    refine ⟨k, bk, ?_, wa⟩
    have ua := walk_sub (fun h => h.1) wa
    have ub := walk_sub (fun h => h.1) wb
    cases ea : side a <;> cases eb : side b <;> simp_all [Common]
  rcases ha with ⟨k, ka, b, kb, hn⟩ | ha
  · exact mk ((one ka k).2 rfl) (criticalSide bad point leaf B side one branch route ka) kb hn
  · obtain ⟨k, bk, wa⟩ := route a _ (branch a)
    obtain ⟨b, kb⟩ := points k
    exact mk bk wa kb (ha k bk b kb)

theorem entry_exists {α κ : Type} {E : ℕ → ℕ → Prop} (dec : ∀ {i j}, E i j → j < i)
    {r c d : ℕ} (rc : E r c) (rd : E r d) (ne : c ≠ d)
    (bad : α → κ → Prop) (point : κ → α → Prop) (leaf : κ → ℕ)
    (B : α → ℕ → Prop) (side : α → Bool)
    (one : ∀ {a k}, point k a → ∀ j, bad a j ↔ j = k)
    (branch : ∀ a, B a (if side a then c else d))
    (route : ∀ a i, B a i →
      ∃ j, bad a j ∧ Walk (fun u v => E u v ∧ B a v) i (leaf j))
    (points : ∀ k, ∃ a, point k a)
    {a} (ha : Forced bad point side a) :
    ∃ p q m, (p = r ∨ Walk E c p) ∧ (q = r ∨ Walk E d q) ∧
      E p m ∧ E q m ∧ p ≠ q ∧ B a m ∧ Common E c d m := by
  obtain ⟨k, _, ⟨wc, wd⟩, w⟩ := forced_common bad point leaf B side one branch route points ha
  cases h : side a
  · simp [h] at w
    obtain ⟨q, p, m, hq, hp, eq, ep, neq, b, rd', rc'⟩ :=
      clash dec rd rc ne.symm (by simpa [h] using branch a) w wc
    exact ⟨p, q, m, hp, hq, ep, eq, neq.symm, b, rc', rd'⟩
  · simp [h] at w
    exact clash dec rc rd ne (by simpa [h] using branch a) w wd

end PEqualNP.Outside.L_pcx_472_aux.Bridge

namespace PEqualNP.Outside.L_pcx_472_aux.Graph

open PEqualNP.Outside.L_pcx_472_aux.Bridge PEqualNP.ProofComplexity

abbrev ClauseMap (V : Type) := Nat → LinClause V
abbrev Parents := Nat → List Nat

def Rule {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (i : Nat) : Prop :=
    (P i = [] ∧ C i ∈ F) ∨
    (∃ j < i, P i = [j] ∧ (∀ a, LinClauseSat a (C j) → LinClauseSat a (C i))) ∨
    (∃ j < i, ∃ k < i, P i = [j, k] ∧ IsLinResolvent (C j) (C k) (C i))

def Encoded {V : Type} [DecidableEq V] (F : Set (LinClause V))
    (C : ClauseMap V) (P : Parents) (lines : List (LinClause V)) : Prop :=
  (∀ i < lines.length, Rule F C P i) ∧
  (∀ D, D ∈ lines ↔ ∃ i < lines.length, C i = D)

theorem rule_congr {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C D : ClauseMap V} {P Q : Parents} {i : Nat}
    (same : ∀ j ≤ i, D j = C j) (parents : Q i = P i)
    (h : Rule F C P i) : Rule F D Q i := by
  rw [Rule, parents, same i le_rfl]
  rcases h with h | ⟨j, ji, e, weak⟩ | ⟨j, ji, k, ki, e, res⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨j, ji, e, by simpa only [same _ ji.le] using weak⟩)
  · exact Or.inr (Or.inr ⟨j, ji, k, ki, e, by simpa only [same _ ji.le, same _ ki.le] using res⟩)

theorem extend {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents} (enc : Encoded F C P π)
    (D : LinClause V) (q : List Nat)
    (hr : Rule F (Function.update C π.length D) (Function.update P π.length q) π.length) :
    Encoded F (Function.update C π.length D) (Function.update P π.length q) (D :: π) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have ib : i ≤ π.length := Nat.lt_succ_iff.1 (by simpa only [List.length_cons] using hi)
    rcases eq_or_lt_of_le ib with rfl | lt
    · exact hr
    · refine rule_congr (fun j ji => Function.update_of_ne (ne_of_lt (ji.trans_lt lt)) _ _) ?_ (enc.1 i lt)
      exact Function.update_of_ne (ne_of_lt lt) _ _
  · intro A
    simp only [List.mem_cons, List.length_cons]
    constructor
    · intro h
      rcases h with rfl | h
      · exact ⟨π.length, Nat.lt_succ_self _, by simp⟩
      · obtain ⟨i, hi, eq⟩ := (enc.2 _).1 h
        exact ⟨i, by omega, by simpa [Function.update_of_ne (ne_of_lt hi)] using eq⟩
    · rintro ⟨i, hi, eq⟩
      have ib : i ≤ π.length := by omega
      rcases eq_or_lt_of_le ib with rfl | lt
      · exact Or.inl (by simpa using eq.symm)
      · exact Or.inr ((enc.2 _).2 ⟨i, lt, by simpa [Function.update_of_ne (ne_of_lt lt)] using eq⟩)

theorem build_graph {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) : ∃ C P, Encoded F C P π := by
  induction der with
  | nil => exact ⟨fun _ => ∅, fun _ => [], by simp [Encoded]⟩
  | @ax π D _ hD ih =>
    obtain ⟨C, P, enc⟩ := ih
    refine ⟨_, _, extend enc D [] ?_⟩
    exact Or.inl (by simpa using hD)
  | @res π D H R _ d h res ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, di⟩ := (enc.2 _).1 d
    obtain ⟨j, hj, ej⟩ := (enc.2 _).1 h
    refine ⟨_, _, extend enc R [i, j] (Or.inr (Or.inr ⟨i, hi, j, hj, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), Function.update_of_ne (ne_of_lt hj), di, ej] using res
  | @weak π D R _ hD hw ih =>
    obtain ⟨C, P, enc⟩ := ih
    obtain ⟨i, hi, eq⟩ := (enc.2 _).1 hD
    refine ⟨_, _, extend enc R [i] (Or.inr (Or.inl ⟨i, hi, by simp, ?_⟩))⟩
    simpa [Function.update_of_ne (ne_of_lt hi), eq] using hw

def Edge (P : Parents) (i j : Nat) : Prop := j ∈ P i

theorem edge_desc {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i j : Nat} (h : Rule F C P i)
    (e : Edge P i j) : j < i := by
  rcases h with ⟨r, _⟩ | ⟨k, ki, r, _⟩ | ⟨k, ki, m, mi, r, _⟩
  · simp [Edge, r] at e
  · have eq : j = k := by simpa [Edge, r] using e
    simpa [eq] using ki
  · simp only [Edge, r, List.mem_cons, List.mem_nil_iff, or_false] at e
    rcases e with rfl | rfl <;> assumption

def FalseAt {V : Type} (C : ClauseMap V) (a : V → Bool) (i : Nat) : Prop :=
  ¬ LinClauseSat a (C i)

theorem resolve_branch {V : Type} [DecidableEq V] {D H R : LinClause V}
    (a : V → Bool) {f : Finset V}
    (rr : R = D.erase (f, false) ∪ H.erase (f, true))
    (fr : ¬ LinClauseSat a R) :
    if Odd (f.filter (fun x => a x = true)).card
    then ¬ LinClauseSat a D else ¬ LinClauseSat a H := by
  subst R
  by_cases h : Odd (f.filter (fun x => a x = true)).card
  · rw [ite_eq_left h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat
  · rw [ite_eq_right h]
    rintro ⟨q, hq, sat⟩
    apply fr
    refine ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), sat⟩
    rintro rfl
    simp [LinEqSat, h] at sat

theorem follow {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {n : Nat} (rule : ∀ i < n, Rule F C P i) (a : V → Bool)
    {i : Nat} (hi : i < n) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have visit : ∀ j < i, Edge P i j → FalseAt C a j →
        ∃ k, P k = [] ∧ C k ∈ F ∧ FalseAt C a k ∧
          Walk (fun u v => Edge P u v ∧ FalseAt C a v) i k := by
      intro j lt ej fj
      obtain ⟨k, p0, fm, fk, w⟩ := ih j lt (lt.trans hi) fj
      exact ⟨k, p0, fm, fk, Relation.ReflTransGen.head ⟨ej, fj⟩ w⟩
    rcases rule i hi with ⟨p0, hF⟩ | ⟨j, ji, pp, hw⟩ | ⟨j, ji, k, ki, pp, f, h1, h2, rr⟩
    · exact ⟨i, p0, hF, fi, .refl⟩
    · exact visit j ji (by simp [Edge, pp]) (fun h => fi (hw a h))
    · have br := resolve_branch a rr fi
      split at br
      · exact visit j ji (by simp [Edge, pp]) br
      · exact visit k ki (by simp [Edge, pp]) br

theorem first_false {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {π : List (LinClause V)}
    (graph : Encoded F C P π) (empty : ∅ ∈ π)
    (axsat : ∀ D ∈ F, ∃ a, LinClauseSat a D) :
    ∃ r < π.length, (∀ a, FalseAt C a r) ∧
      (∀ j < r, ∃ a, LinClauseSat a (C j)) ∧
      ∃ j < r, ∃ k < r, j ≠ k ∧ P r = [j, k] ∧ ∃ f : Finset V,
          f ≠ ∅ ∧ ∀ a, if Odd (f.filter (fun x => a x = true)).card
            then FalseAt C a j else FalseAt C a k := by
  classical
  have existsFalse : ∃ j, j < π.length ∧ ∀ a, FalseAt C a j := by
    obtain ⟨j, hj, he⟩ := (graph.2 _).1 empty
    exact ⟨j, hj, by simp [FalseAt, he, LinClauseSat]⟩
  let r := Nat.find existsFalse
  obtain ⟨ri, fr⟩ := Nat.find_spec existsFalse
  have prev : ∀ j < r, ∃ a, LinClauseSat a (C j) := by
    intro j hj
    by_contra! h
    exact Nat.find_min existsFalse hj ⟨hj.trans ri, h⟩
  refine ⟨r, ri, fr, prev, ?_⟩
  rcases graph.1 r ri with ⟨_, hF⟩ | ⟨j, jr, _, hw⟩ | ⟨j, jr, k, kr, p, f, df, dk, rr⟩
  · obtain ⟨a, ha⟩ := axsat _ hF
    exact (fr a ha).elim
  · obtain ⟨a, ha⟩ := prev j jr
    exact (fr a (hw a ha)).elim
  · have br : ∀ a, if Odd (f.filter (fun x => a x = true)).card
      then FalseAt C a j else FalseAt C a k := fun a => resolve_branch a rr (fr a)
    have ne : j ≠ k := by
      intro eq
      obtain ⟨a, sat⟩ := prev j jr
      have no := br a
      rw [eq] at no sat
      split at no <;> exact no sat
    have nz : f ≠ ∅ := by
      intro eq
      obtain ⟨a, sat⟩ := prev k kr
      exact (by simpa [eq] using br a : FalseAt C a k) sat
    exact ⟨j, jr, k, kr, ne, p, f, nz, br⟩

open scoped BigOperators

def LocalEdge (P : Parents) (r i j : Nat) : Prop := i ≤ r ∧ Edge P i j

noncomputable def Live (P : Parents) (r : Nat) : Finset Nat := by
  classical
  exact (Finset.range (r + 1)).filter (fun v => Walk (LocalEdge P r) r v)

theorem bounded_edge {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {i j : Nat} (e : LocalEdge P r i j) : j < i := edge_desc (rules i e.1) e.2

theorem live_iff {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    i ∈ Live P r ↔ Walk (LocalEdge P r) r i := by
  classical
  simp only [Live, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact ⟨fun h => h.2, fun w => ⟨walk_le (bounded_edge rules) w, w⟩⟩

theorem live_closed {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r i j : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (hi : i ∈ Live P r) (e : Edge P i j) :
    j ∈ Live P r := by
  have w := (live_iff rules).1 hi
  exact (live_iff rules).2 (.tail w ⟨walk_le (bounded_edge rules) w, e⟩)

def InDegree (P : Parents) (s : Finset Nat) (j : Nat) : Nat :=
  ∑ i ∈ s, (P i).count j

theorem count_edges {P : Parents} {s : Finset Nat}
    (hs : ∀ i ∈ s, ∀ j ∈ P i, j ∈ s) :
    ∑ j ∈ s, InDegree P s j = ∑ i ∈ s, (P i).length := by
  unfold InDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∑ j ∈ s, List.count j (P i)) = ∑ j ∈ (P i).toFinset, List.count j (P i) := by
      symm
      apply Finset.sum_subset
      · intro j hj
        exact hs i hi j (List.mem_toFinset.1 hj)
      · intro j hj hnot
        exact List.count_eq_zero_of_not_mem (fun h => hnot (List.mem_toFinset.2 h))
    _ = (P i).length := by
      simpa only [List.toFinset_coe, Multiset.coe_count, Multiset.coe_card] using
        Multiset.toFinset_sum_count_eq ((P i : List Nat) : Multiset Nat)

theorem inDegree_root {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    InDegree P (Live P r) r = 0 := by
  unfold InDegree
  apply Finset.sum_eq_zero
  intro i hi
  have il := walk_le (bounded_edge rules) ((live_iff rules).1 hi)
  apply List.count_eq_zero_of_not_mem
  intro ei
  exact (Nat.not_lt_of_le il) (edge_desc (rules i il) ei)

theorem inDegree_pos {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r j : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (hj : j ∈ Live P r) (ne : j ≠ r) : 1 ≤ InDegree P (Live P r) j := by
  obtain ⟨i, wi, ei⟩ := ((live_iff rules).1 hj).cases_tail.resolve_left ne
  have im : i ∈ Live P r := (live_iff rules).2 wi
  have h := Finset.single_le_sum (f := fun u => (P u).count j) (fun _ _ => Nat.zero_le _) im
  exact (Nat.succ_le_of_lt (List.count_pos_iff.2 ei.2)).trans h

noncomputable def Surplus (P : Parents) (r : Nat) : Nat :=
  ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1)

theorem surplus_identity {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (∑ i ∈ Live P r, (P i).length) + 1 = (Live P r).card + Surplus P r := by
  have h1 := count_edges (fun i hi j hj => live_closed rules hi hj)
  have root : r ∈ Live P r := (live_iff rules).2 .refl
  have hsum := Finset.sum_erase_add (Live P r) (InDegree P (Live P r)) root
  rw [inDegree_root rules, Nat.add_zero, h1] at hsum
  have hc := Finset.card_erase_of_mem root
  have hp := Finset.card_pos.2 ⟨_, root⟩
  have eq : ∑ j ∈ (Live P r).erase r, InDegree P (Live P r) j =
      ∑ j ∈ (Live P r).erase r, (InDegree P (Live P r) j - 1 + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨ne, hm⟩ := Finset.mem_erase.1 hj
    have lb := inDegree_pos rules hm ne
    omega
  have hone : (∑ _ ∈ (Live P r).erase r, (1 : Nat)) = ((Live P r).erase r).card := by simp
  rw [Finset.sum_add_distrib, hone] at eq
  unfold Surplus
  omega

noncomputable def WithArity (P : Parents) (r n : Nat) : Finset Nat :=
  (Live P r).filter (fun j => (P j).length = n)

theorem length_le_two {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {i : Nat} (h : Rule F C P i) :
    (P i).length ≤ 2 := by
  rcases h with ⟨r, _⟩ | ⟨j, _, r, _⟩ | ⟨j, _, k, _, r, _⟩ <;> simp [r]

theorem arity_sum (P : Parents) (r n k : Nat) :
    (∑ i ∈ Live P r, if (P i).length = n then k else 0) = k * (WithArity P r n).card := by
  rw [← Finset.sum_filter]
  simp [WithArity, Nat.mul_comm]

theorem arity_count {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i) :
    (Live P r).card + 1 =
      2 * (WithArity P r 0).card + (WithArity P r 1).card + Surplus P r := by
  have hk : ∀ i ∈ Live P r, (P i).length ≤ 2 := by
    intro i hi
    exact length_le_two (rules i (walk_le (bounded_edge rules) ((live_iff rules).1 hi)))
  have decomp :
      (Live P r).card = (WithArity P r 0).card + (WithArity P r 1).card + (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (1 : Nat) = ∑ i ∈ Live P r,
        ((if (P i).length = 0 then 1 else 0) + (if (P i).length = 1 then 1 else 0) +
          (if (P i).length = 2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    have countOnes : (∑ _ ∈ Live P r, (1 : Nat)) = (Live P r).card := by simp
    rw [countOnes] at h
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have edges :
      (∑ i ∈ Live P r, (P i).length) = (WithArity P r 1).card + 2 * (WithArity P r 2).card := by
    have h : ∑ i ∈ Live P r, (P i).length = ∑ i ∈ Live P r,
        ((if (P i).length = 1 then 1 else 0) + (if (P i).length = 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := hk i hi
      have := show (P i).length = 0 ∨ (P i).length = 1 ∨ (P i).length = 2 by omega
      rcases this with e | e | e <;> simp [e]
    simpa only [Finset.sum_add_distrib, arity_sum, one_mul] using h
  have hs := surplus_identity rules
  omega

theorem shared_degree {P : Parents} {s : Finset Nat} {p q m : Nat}
    (hp : p ∈ s) (hq : q ∈ s) (ep : Edge P p m) (eq : Edge P q m) (ne : p ≠ q) :
    2 ≤ InDegree P s m := by
  have tm : ({p, q} : Finset Nat) ⊆ s := by
    intro i hi
    rcases (by simpa using hi : i = p ∨ i = q) with rfl | rfl <;> assumption
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u => (P u).count m) tm
    (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert (Finset.notMem_singleton.2 ne), Finset.sum_singleton] at hs
  have lp := List.count_pos_iff.2 ep
  have lq := List.count_pos_iff.2 eq
  unfold InDegree
  omega

theorem no_share_of_zero_surplus {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r z : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (su : Surplus P r = 0) (hz : z ∈ Live P r) (sz : 2 ≤ InDegree P (Live P r) z) : False := by
  have nr := inDegree_root rules
  have zn : z ≠ r := by
    rintro rfl
    omega
  have ze : z ∈ (Live P r).erase r := Finset.mem_erase.2 ⟨zn, hz⟩
  have hh := Finset.single_le_sum (f := fun j => InDegree P (Live P r) j - 1)
    (fun _ _ => Nat.zero_le _) ze
  unfold Surplus at su
  omega

theorem walk_localize {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ≤ r)
    (w : Walk (fun u v => Edge P u v ∧ FalseAt C a v) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j ∧ j ≤ r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have next := (edge_desc (rules _ ih.2) e.1).le.trans ih.2
    exact ⟨.tail ih.1 ⟨⟨ih.2, e.1⟩, next, e.2⟩, next⟩

theorem localized_route {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (a : V → Bool) {i : Nat} (hi : i ≤ r) (fi : FalseAt C a i) :
    ∃ j, P j = [] ∧ C j ∈ F ∧ FalseAt C a j ∧
      Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j := by
  obtain ⟨j, h0, ha, ff, w⟩ := follow (n := r + 1)
    (fun i hi => rules i (Nat.lt_succ_iff.1 hi)) a (Nat.lt_succ_iff.2 hi) fi
  exact ⟨j, h0, ha, ff, (walk_localize rules hi w).1⟩

theorem live_card_le (P : Parents) (r : Nat) : (Live P r).card ≤ r + 1 := by
  classical
  unfold Live
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem unique_leaves {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (ax : κ → LinClause V) (exh : F = Set.range ax)
    (critical : ∀ k, ∃ a : V → Bool, ∀ j, ¬ LinClauseSat a (ax j) ↔ j = k) :
    ∃ leaf : κ → Nat, Function.Injective leaf ∧
      (∀ k, leaf k ∈ WithArity P r 0 ∧ C (leaf k) = ax k) ∧
      Fintype.card κ ≤ (WithArity P r 0).card ∧
      ((WithArity P r 0).card = Fintype.card κ →
        ∀ j ∈ WithArity P r 0, ∃ k, leaf k = j) := by
  classical
  have located : ∀ k, ∃ j, j ∈ WithArity P r 0 ∧ C j = ax k := by
    intro k
    obtain ⟨a, cert⟩ := critical k
    obtain ⟨j, hj, hc, ff, w⟩ := localized_route rules a le_rfl (fr a)
    rw [exh] at hc
    obtain ⟨k', hk'⟩ := hc
    have h : ¬ LinClauseSat a (ax k') := by simpa [FalseAt, hk'] using ff
    have eq := (cert k').1 h
    subst k'
    refine ⟨j, ?_, hk'.symm⟩
    simp only [WithArity, Finset.mem_filter, hj, List.length_nil, and_true]
    exact (live_iff rules).2 (walk_sub (fun e => e.1) w)
  choose leaf spec using located
  have inj : Function.Injective leaf := by
    intro u v h
    obtain ⟨a, cert⟩ := critical u
    have hEq := (spec u).2.symm.trans ((congrArg C h).trans (spec v).2)
    have no := (cert u).2 rfl
    rw [hEq] at no
    exact ((cert v).1 no).symm
  have ss : Finset.univ.image leaf ⊆ WithArity P r 0 := by
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hj
    exact (spec k).1
  have card : (Finset.univ.image leaf).card = Fintype.card κ := by
    rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
  refine ⟨leaf, inj, spec, by simpa [card] using Finset.card_le_card ss, ?_⟩
  intro eq j hj
  have e : Finset.univ.image leaf = WithArity P r 0 :=
    Finset.eq_of_subset_of_card_le ss (by rw [eq, card])
  rw [← e] at hj
  obtain ⟨k, _, e⟩ := Finset.mem_image.1 hj
  exact ⟨k, e⟩

noncomputable def useful {V : Type} (R : LinClause V) : Bool := by
  classical
  exact decide (∃ a, ¬ LinClauseSat a R)

theorem useful_spec {V : Type} (R : LinClause V) :
    useful R = true ↔ ∃ a, ¬ LinClauseSat a R := by
  classical
  simp [useful]

theorem prune_taut {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} (der : IsLinDerivation F π) :
    IsLinDerivation F (π.filter useful) := by
  induction der with
  | nil => exact .nil
  | @ax π D _ hD ih =>
    simp only [List.filter_cons]
    split
    · exact .ax ih hD
    · exact ih
  | @res π D H R _ d h resolvent ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨f, df, hf, rr⟩ := resolvent
      by_cases ud : useful D = true
      · have md := List.mem_filter.2 ⟨d, ud⟩
        by_cases uh : useful H = true
        · exact .res ih md (List.mem_filter.2 ⟨h, uh⟩) ⟨f, df, hf, rr⟩
        · exact .weak ih md (by
            intro a sat
            by_contra no
            have b := resolve_branch a rr no
            split at b
            · exact b sat
            · exact uh ((useful_spec _).2 ⟨a, b⟩))
      · have weak : ∀ a, LinClauseSat a H → LinClauseSat a R := by
          intro a sat
          by_contra no
          have b := resolve_branch a rr no
          split at b
          · exact ud ((useful_spec _).2 ⟨a, b⟩)
          · exact b sat
        obtain ⟨a, ff⟩ := (useful_spec _).1 ur
        have hu : useful H = true := (useful_spec _).2 ⟨a, fun s => ff (weak a s)⟩
        exact .weak ih (List.mem_filter.2 ⟨h, hu⟩) weak
    · rw [ite_eq_right ur]
      exact ih
  | @weak π D R _ hD hw ih =>
    simp only [List.filter_cons]
    by_cases ur : useful R = true
    · rw [ite_eq_left ur]
      obtain ⟨a, no⟩ := (useful_spec _).1 ur
      exact .weak ih (List.mem_filter.2 ⟨hD, (useful_spec _).2 ⟨a, fun h => no (hw a h)⟩⟩) hw
    · rw [ite_eq_right ur]
      exact ih

theorem encoded_useful {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {π : List (LinClause V)} {C : ClauseMap V} {P : Parents}
    (h : Encoded F C P (π.filter useful)) {i : Nat} (hi : i < (π.filter useful).length) :
    ∃ a, FalseAt C a i := by
  have mm := (h.2 _).2 ⟨i, hi, rfl⟩
  exact (useful_spec _).1 (List.mem_filter.1 mm).2

theorem walk_keep_live {V : Type} [DecidableEq V] {F : Set (LinClause V)}
    {C : ClauseMap V} {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    {a : V → Bool} {i j : Nat} (hi : i ∈ Live P r)
    (w : Walk (fun u v => LocalEdge P r u v ∧ (v ≤ r ∧ FalseAt C a v)) i j) :
    Walk (fun u v => LocalEdge P r u v ∧ (v ∈ Live P r ∧ FalseAt C a v)) i j ∧ j ∈ Live P r := by
  induction w with
  | refl => exact ⟨.refl, hi⟩
  | tail _ e ih =>
    have hm := live_closed rules ih.2 e.1.2
    exact ⟨.tail ih.1 ⟨e.1, hm, e.2.2⟩, hm⟩

theorem high_weak_impossible {V κ : Type} [DecidableEq V] [Fintype κ]
    {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule F C P i) (fr : ∀ a, FalseAt C a r)
    (rc : LocalEdge P r r c) (rd : LocalEdge P r r d) (ne : c ≠ d)
    (size : (Live P r).card ≤ 92) (wcount : 3 ≤ (WithArity P r 1).card)
    (labels : Fintype.card κ = 45)
    (ax : κ → LinClause V) (exh : F = Set.range ax) (point : κ → (V → Bool) → Prop)
    (point_exists : ∀ k, ∃ a, point k a)
    (one : ∀ {a k}, point k a → ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k)
    (side : (V → Bool) → Bool)
    (side_choose : ∀ a, FalseAt C a (if side a then c else d))
    (force_exists : ∃ a, Forced (fun a k => ¬ LinClauseSat a (ax k)) point side a) :
    False := by
  have crit : ∀ k, ∃ a : V → Bool, ∀ j, (¬ LinClauseSat a (ax j)) ↔ j = k := by
    intro k
    obtain ⟨a, ha⟩ := point_exists k
    exact ⟨a, one ha⟩
  obtain ⟨leaf, _, atLeaf, lb, covers⟩ := unique_leaves rules fr ax exh crit
  have card := arity_count rules
  have ex : (WithArity P r 0).card = Fintype.card κ := by omega
  have su : Surplus P r = 0 := by omega
  let E := LocalEdge P r
  let B := fun a i => i ∈ Live P r ∧ FalseAt C a i
  let bad := fun a k => ¬ LinClauseSat a (ax k)
  have branch : ∀ a, B a (if side a then c else d) := by
    intro a
    refine ⟨?_, side_choose a⟩
    cases h : side a
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rd))
    · exact (live_iff rules).2 (by simpa [h] using (Relation.ReflTransGen.single rc))
  have route : ∀ a i, B a i →
      ∃ k, bad a k ∧ Walk (fun u v => E u v ∧ B a v) i (leaf k) := by
    intro a i bi
    have ir := walk_le (bounded_edge rules) ((live_iff rules).1 bi.1)
    obtain ⟨j, j0, _, jf, w⟩ := localized_route rules a ir bi.2
    obtain ⟨wm, jm⟩ := walk_keep_live rules bi.1 w
    have jax : j ∈ WithArity P r 0 := by simpa [WithArity, j0] using jm
    obtain ⟨k, hk⟩ := covers ex j jax
    have ceq : C j = ax k := hk ▸ (atLeaf k).2
    exact ⟨k, by simpa [bad, FalseAt, ceq] using jf, hk ▸ wm⟩
  have desc : ∀ {i j}, E i j → j < i := bounded_edge rules
  obtain ⟨a, ha⟩ := force_exists
  obtain ⟨p, q, z, hp, hq, ep, eq, pq, _, _⟩ :=
    entry_exists desc rc rd ne bad point leaf B side one branch route point_exists ha
  have from_left : ∀ {p}, p = r ∨ Walk E c p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rc hp)
  have from_right : ∀ {p}, p = r ∨ Walk E d p → p ∈ Live P r := by
    intro p hp
    rcases hp with rfl | hp
    · exact (live_iff rules).2 .refl
    · exact (live_iff rules).2 (.head rd hp)
  have zl : z ∈ Live P r := live_closed rules (from_left hp) ep.2
  have zd : 2 ≤ InDegree P (Live P r) z := shared_degree (from_left hp) (from_right hq) ep.2 eq.2 pq
  exact no_share_of_zero_surplus rules su zl zd

end PEqualNP.Outside.L_pcx_472_aux.Graph

namespace PEqualNP.Outside.L_pcx_472_aux.Linear

open PEqualNP.ProofComplexity

def smear (s a : Nat) : Nat := a ^^^ (a >>> s)

def parity (a q : Nat) : Bool :=
  (smear 1 (smear 2 (smear 4 (smear 8 (smear 16 (a &&& q)))))).testBit 0

theorem smear_xor (s a b : Nat) :
    smear s (a ^^^ b) = smear s a ^^^ smear s b := by
  simp only [smear, Nat.shiftRight_xor_distrib]
  ac_rfl

theorem parity_left (a b q : Nat) :
    parity (a ^^^ b) q = (parity a q ^^ parity b q) := by
  simp only [parity, Nat.and_xor_distrib_right, smear_xor, Nat.testBit_xor]

theorem parity_right (a b q : Nat) :
    parity q (a ^^^ b) = (parity q a ^^ parity q b) := by
  simp only [parity, Nat.and_xor_distrib_left, smear_xor, Nat.testBit_xor]

theorem parity_comm (a q : Nat) : parity a q = parity q a := by
  simp only [parity, Nat.and_comm]

theorem parity_zero_left (q : Nat) : parity 0 q = false := by
  simp [parity, smear]

abbrev V := Fin 5 × Fin 4

def idx (v : V) : Nat := 4 * v.1.val + v.2.val
def assignment (a : Nat) (v : V) : Bool := a.testBit (idx v)
def formMask (S : Finset V) : Nat := S.fold (· ^^^ ·) 0 (fun v => 2 ^ idx v)

theorem idx_lt (v : V) : idx v < 20 := by
  have h1 := v.1.isLt
  have h2 := v.2.isLt
  unfold idx
  omega

theorem idx_inj : Function.Injective idx := by
  intro v w h
  have hv := v.2.isLt
  have hw := w.2.isLt
  unfold idx at h
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

theorem idx_cover (n : Nat) (h : n < 20) : ∃ v : V, idx v = n := by
  let v : V := (⟨n / 4, by omega⟩, ⟨n % 4, by omega⟩)
  exact ⟨v, by change 4 * (n / 4) + n % 4 = n; omega⟩

theorem mask_insert (S : Finset V) {v : V} (h : v ∉ S) :
    formMask (insert v S) = 2 ^ idx v ^^^ formMask S := by
  simp [formMask, Finset.fold_insert h]

theorem mask_lt (S : Finset V) : formMask S < 1048576 := by
  change formMask S < 2 ^ 20
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert v S h ih =>
    rw [mask_insert S h]
    exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by decide : 1 < 2) (idx_lt v)) ih

theorem bit_mask (S : Finset V) (v : V) :
    (formMask S).testBit (idx v) = decide (v ∈ S) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask]
  | @insert w S h ih =>
    rw [mask_insert S h, Nat.testBit_xor, Nat.testBit_two_pow, ih]
    by_cases hw : v = w
    · subst w
      simp [h]
    · have hidx : idx w ≠ idx v := fun e => hw (idx_inj e.symm)
      simp [hidx, hw]

theorem mask_nz {S : Finset V} (h : S.Nonempty) : formMask S ≠ 0 := by
  obtain ⟨v, hv⟩ := h
  intro hz
  have h' := bit_mask S v
  simp [hz, hv] at h'

theorem parity_unit (a j : Nat) (hj : j < 20) : parity a (2 ^ j) = a.testBit j := by
  have hb : a &&& (2 ^ j) = if a.testBit j then 2 ^ j else 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases h : j = i
    · subst i
      cases ht : a.testBit j <;> simp [ht]
    · cases ht : a.testBit j <;> simp [h]
  have hp : ∀ k : Fin 20, parity (2 ^ k.val) (2 ^ k.val) = true := by decide +kernel
  have hs := hp ⟨j, hj⟩
  unfold parity at hs ⊢
  rw [hb]
  cases ht : a.testBit j
  · simp [smear]
  · simpa only [ht, ite_true, Nat.and_self] using hs

theorem parity_form (a : Nat) (S : Finset V) :
    parity a (formMask S) = decide (Odd (S.filter (fun v => assignment a v = true)).card) := by
  induction S using Finset.induction_on with
  | empty => simp [formMask, parity, smear]
  | @insert v S h ih =>
    rw [mask_insert S h, parity_right, parity_unit _ _ (idx_lt v), ih]
    change (assignment a v ^^ _) = _
    cases hv : assignment a v with
    | false => simp [Finset.filter_insert, hv]
    | true =>
      have hv' : v ∉ S.filter (fun w => assignment a w = true) := by
        intro hh
        exact h (Finset.mem_filter.mp hh).1
      rw [Finset.filter_insert, ite_eq_left hv, Finset.card_insert_of_notMem hv']
      cases hd : decide (Odd (S.filter (fun w => assignment a w = true)).card) with
      | false =>
        have ho : ¬ Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_false hd
        have he : Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]
      | true =>
        have ho : Odd (S.filter (fun w => assignment a w = true)).card := of_decide_eq_true hd
        have he : ¬ Odd ((S.filter (fun w => assignment a w = true)).card + 1) := by
          rw [Nat.odd_iff] at ho ⊢
          omega
        simp [he]

def support (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit (idx v))

def clauseOf (row : Nat × Bool) : Clause V := (support row.1).image (fun v => (v, !row.2))

def linearOf (row : Nat × Bool) : LinClause V := linOfClause (clauseOf row)

theorem singleton_sat (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases hv : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, hv]

theorem linear_iff (a : V → Bool) (C : Clause V) :
    LinClauseSat a (linOfClause C) ↔ ClauseSat a C := by
  simp only [LinClauseSat, linOfClause, Finset.mem_image, ClauseSat]
  constructor
  · rintro ⟨q, ⟨⟨v, s⟩, hs, rfl⟩, hq⟩
    exact ⟨(v, s), hs, (singleton_sat _ _ _).1 hq⟩
  · rintro ⟨⟨v, s⟩, hs, hv⟩
    exact ⟨({v}, s), ⟨(v, s), hs, rfl⟩, (singleton_sat _ _ _).2 hv⟩

def falseOn (a : Nat) (row : Nat × Bool) : Bool :=
  (a &&& row.1) == (if row.2 then row.1 else 0)

theorem false_on_spec (a : Nat) (row : Nat × Bool) (hh : row.1 < 1048576) :
    falseOn a row = true ↔ ¬ LinClauseSat (assignment a) (linearOf row) := by
  unfold falseOn
  rw [beq_iff_eq, linearOf, linear_iff]
  have ht : ClauseSat (assignment a) (clauseOf row) ↔
      ∃ v ∈ support row.1, assignment a v = !row.2 := by
    constructor
    · rintro ⟨l, hl, h⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hl
      exact ⟨v, hv, h⟩
    · rintro ⟨v, hv, h⟩
      exact ⟨(v, !row.2), Finset.mem_image.mpr ⟨v, hv, rfl⟩, h⟩
  rw [ht]
  push Not
  have he : ∀ v : V, assignment a v ≠ !row.2 ↔ assignment a v = row.2 := by
    intro v
    cases h1 : assignment a v <;> cases row.2 <;> simp
  simp only [he]
  constructor
  · intro h v hv
    have hm : row.1.testBit (idx v) = true := (Finset.mem_filter.mp hv).2
    have eq := congrArg (fun k : Nat => k.testBit (idx v)) h
    cases hs : row.2 <;> simpa [Nat.testBit_and, hm, hs, assignment] using eq
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hm : row.1.testBit i = true
    · have hi : i < 20 := by
        by_contra hn
        have hp : 2 ^ 20 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        have hw : row.1 < 2 ^ i := lt_of_lt_of_le hh hp
        simp [Nat.testBit_lt_two_pow hw] at hm
      obtain ⟨v, rfl⟩ := idx_cover i hi
      have hv : v ∈ support row.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
      have hs := h v hv
      cases hr : row.2 <;> simp_all [Nat.testBit_and, assignment]
    · have hn : row.1.testBit i = false := by
        cases ht : row.1.testBit i <;> simp_all
      cases hr : row.2 <;> simp [Nat.testBit_and, hn]

def pigeon (i : Fin 5) : Clause V := Finset.univ.image (fun j : Fin 4 => ((i, j), true))
def collClause (i k : Fin 5) (j : Fin 4) : Clause V := {((i, j), false), ((k, j), false)}

def pigeonMask (i : Fin 5) : Nat := 15 <<< (4 * i.val)
def collMask (i k : Fin 5) (j : Fin 4) : Nat := 2 ^ (4 * i.val + j.val) ||| 2 ^ (4 * k.val + j.val)

theorem pigeonMask_bit : ∀ (i : Fin 5) (v : V),
    (pigeonMask i).testBit (idx v) = decide (v.1 = i) := by decide +kernel

theorem collMask_bit (i k : Fin 5) (j : Fin 4) (v : V) :
    (collMask i k j).testBit (idx v) = decide (v = (i, j) ∨ v = (k, j)) := by
  unfold collMask
  rw [Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
  change (decide (idx (i, j) = idx v) || decide (idx (k, j) = idx v)) = _
  by_cases h1 : v = (i, j)
  · subst h1
    simp
  · by_cases h2 : v = (k, j)
    · subst h2
      simp
    · have hi : idx (i, j) ≠ idx v := fun e => h1 (idx_inj e.symm)
      have hk : idx (k, j) ≠ idx v := fun e => h2 (idx_inj e.symm)
      simp [hi, hk, h1, h2]

theorem clauseOf_pigeonMask (i : Fin 5) : clauseOf (pigeonMask i, false) = pigeon i := by
  ext ⟨v, b⟩
  simp only [clauseOf, support, pigeon, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Bool.not_false, pigeonMask_bit, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact ⟨w.2, by ext <;> simp [hw]⟩
  · rintro ⟨j, heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact ⟨(i, j), rfl, rfl⟩

theorem clauseOf_collMask (i k : Fin 5) (j : Fin 4) :
    clauseOf (collMask i k j, true) = collClause i k j := by
  ext ⟨v, b⟩
  simp only [clauseOf, support, collClause, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Bool.not_true, collMask_bit, decide_eq_true_eq, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨w, hw | hw, heq⟩
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact Or.inl (by simp [hw])
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact Or.inr (by simp [hw])
  · rintro (heq | heq)
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact ⟨(i, j), Or.inl rfl, rfl⟩
    · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact ⟨(k, j), Or.inr rfl, rfl⟩

end PEqualNP.Outside.L_pcx_472_aux.Linear

namespace PEqualNP.Outside.L_pcx_472_aux.Cert

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_472_aux.Bridge PEqualNP.Outside.L_pcx_472_aux.Linear

def axioms : List (Nat × Bool) := [(15, false), (240, false), (3840, false), (61440, false), (983040, false), (17, true), (257, true), (4097, true), (65537, true), (272, true), (4112, true), (65552, true), (4352, true), (65792, true), (69632, true), (34, true), (514, true), (8194, true), (131074, true), (544, true), (8224, true), (131104, true), (8704, true), (131584, true), (139264, true), (68, true), (1028, true), (16388, true), (262148, true), (1088, true), (16448, true), (262208, true), (17408, true), (263168, true), (278528, true), (136, true), (2056, true), (32776, true), (524296, true), (2176, true), (32896, true), (524416, true), (34816, true), (526336, true), (557056, true)]

def axRow (k : Fin 45) : Nat × Bool := axioms.get (k.cast rfl)

def ax (k : Fin 45) : LinClause V := linearOf (axRow k)

def collsTriples : List (Fin 5 × Fin 5 × Fin 4) := [(0, 1, 0), (0, 2, 0), (0, 3, 0), (0, 4, 0), (1, 2, 0), (1, 3, 0), (1, 4, 0), (2, 3, 0), (2, 4, 0), (3, 4, 0), (0, 1, 1), (0, 2, 1), (0, 3, 1), (0, 4, 1), (1, 2, 1), (1, 3, 1), (1, 4, 1), (2, 3, 1), (2, 4, 1), (3, 4, 1), (0, 1, 2), (0, 2, 2), (0, 3, 2), (0, 4, 2), (1, 2, 2), (1, 3, 2), (1, 4, 2), (2, 3, 2), (2, 4, 2), (3, 4, 2), (0, 1, 3), (0, 2, 3), (0, 3, 3), (0, 4, 3), (1, 2, 3), (1, 3, 3), (1, 4, 3), (2, 3, 3), (2, 4, 3), (3, 4, 3)]

theorem all_rows_small : ∀ k : Fin 45, (axRow k).1 < 1048576 := by decide +kernel

theorem pigeon_in_ax : ∀ i : Fin 5, axRow ⟨i.val, by omega⟩ = (pigeonMask i, false) := by decide +kernel

theorem coll_in_ax : ∀ (i k : Fin 5) (j : Fin 4), i ≠ k →
    (List.finRange 45).any (fun r => axRow r == (collMask i k j, true)) = true := by decide +kernel

theorem ax_in_php_check : ∀ r : Fin 45,
    if h : r.val < 5 then
      axRow r == (pigeonMask ⟨r.val, h⟩, false)
    else
      let t := collsTriples.getD (r.val - 5) (0, 0, 0)
      decide (t.1 ≠ t.2.1) && (axRow r == (collMask t.1 t.2.1 t.2.2, true)) := by decide +kernel

theorem formula_range : (fun C => linOfClause C) '' PHP 5 4 = Set.range ax := by
  ext D
  constructor
  · rintro ⟨C, hC, rfl⟩
    rcases hC with ⟨i, rfl⟩ | ⟨i, k, j, hne, rfl⟩
    · refine ⟨⟨i.val, by omega⟩, ?_⟩
      simp only [ax, pigeon_in_ax i, linearOf, clauseOf_pigeonMask, pigeon]
    · obtain ⟨r, _, hr⟩ := List.any_eq_true.mp (coll_in_ax i k j hne)
      refine ⟨r, ?_⟩
      simp only [ax, beq_iff_eq.mp hr, linearOf, clauseOf_collMask, collClause]
  · rintro ⟨r, rfl⟩
    have hc := ax_in_php_check r
    by_cases h : r.val < 5
    · rw [dite_eq_left h] at hc
      have heq := beq_iff_eq.mp hc
      refine ⟨pigeon ⟨r.val, h⟩, Or.inl ⟨⟨r.val, h⟩, rfl⟩, ?_⟩
      simp only [ax, heq, linearOf, clauseOf_pigeonMask]
    · rw [dite_eq_right h] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      set t := collsTriples.getD (r.val - 5) (0, 0, 0)
      refine ⟨collClause t.1 t.2.1 t.2.2, Or.inr ⟨t.1, t.2.1, t.2.2, hc.1, rfl⟩, ?_⟩
      simp only [ax, hc.2, linearOf, clauseOf_collMask]

def ptsList : List (List Nat) := [
  [541200, 295440, 533520, 164880, 272400, 540960, 529440, 99360, 532800, 270720],
  [541185, 540930, 532740, 270600],
  [540705],
  [525345],
  [33825],
  [541201],
  [540961],
  [529441],
  [99361],
  [540946],
  [529426],
  [99346],
  [528706],
  [98626],
  [71746],
  [540962],
  [541202],
  [533522],
  [164882],
  [541217],
  [533537],
  [164897],
  [533057],
  [164417],
  [141377],
  [532804],
  [533524],
  [541204],
  [295444],
  [533569],
  [541249],
  [295489],
  [541729],
  [295969],
  [280609],
  [270728],
  [272408],
  [295448],
  [541208],
  [272513],
  [295553],
  [541313],
  [296993],
  [542753],
  [558113]
]

def pts (k : Fin 45) : List Nat := ptsList.get (k.cast rfl)

def point (k : Fin 45) (a : V → Bool) : Prop :=
  ∃ m ∈ pts k, assignment m = a

theorem pts_nonempty : ∀ k : Fin 45, (pts k).isEmpty = false := by decide +kernel

theorem pts_unique : ∀ k : Fin 45,
    (pts k).all (fun m =>
      (List.finRange 45).all (fun j => falseOn m (axRow j) == (j == k))) = true := by decide +kernel

theorem point_exists (k : Fin 45) : ∃ a : V → Bool, point k a := by
  have hne := pts_nonempty k
  cases hl : pts k with
  | nil => simp [hl] at hne
  | cons m ms => exact ⟨assignment m, m, by simp [hl], rfl⟩

theorem point_only {a : V → Bool} {k : Fin 45} (ha : point k a) (j : Fin 45) :
    (¬ LinClauseSat a (ax j)) ↔ j = k := by
  obtain ⟨m, hm, rfl⟩ := ha
  have hu := List.all_eq_true.mp (pts_unique k) m hm
  have hj := List.all_eq_true.mp hu j (List.mem_finRange j)
  have hspec := false_on_spec m (axRow j) (all_rows_small j)
  have hbeq := beq_iff_eq.mp hj
  unfold ax
  rw [← hspec, hbeq]
  simp

def chosenPairsList : List (Fin 45 × Nat × Nat) := [(0, 541200, 295440), (0, 541200, 533520), (0, 541200, 164880), (0, 541200, 272400), (0, 541200, 540960), (0, 541200, 529440), (0, 541200, 99360), (0, 541200, 532800), (0, 541200, 270720), (1, 541185, 540930), (1, 541185, 532740), (1, 541185, 270600)]

def chosenPairs (a : Fin 12) : Fin 45 × Nat × Nat := chosenPairsList.get (a.cast rfl)

def rawDiff (a : Fin 12) : Nat := (chosenPairs a).2.1 ^^^ (chosenPairs a).2.2

theorem chosen_valid : ∀ a : Fin 12,
    ((pts (chosenPairs a).1).contains (chosenPairs a).2.1 &&
     (pts (chosenPairs a).1).contains (chosenPairs a).2.2) = true := by decide +kernel

def rrefCombosList : List Nat := [2131, 2567, 3072, 339, 279, 384, 91, 15, 10, 96, 6, 1]
def rrefMasksList : List Nat := [589833, 655370, 786444, 589968, 655520, 786624, 592128, 657920, 789504, 626688, 696320, 835584]
def pivColsList : List Nat := [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14]

def rrefCombos (i : Fin 12) : Nat := rrefCombosList.get (i.cast rfl)
def rrefMasks (i : Fin 12) : Nat := rrefMasksList.get (i.cast rfl)
def pivCols (i : Fin 12) : Nat := pivColsList.get (i.cast rfl)

def freeBitMask : Nat := 1017992

def xorCombo (c : Nat) : Nat :=
  (List.finRange 12).foldl (fun acc a => if c.testBit a.val then acc ^^^ rawDiff a else acc) 0

theorem parity_foldl_xor (c M : Nat) (horth : ∀ a : Fin 12, parity (rawDiff a) M = false)
    (l : List (Fin 12)) (acc : Nat) (hacc : parity acc M = false) :
    parity (l.foldl (fun acc a => if c.testBit a.val then acc ^^^ rawDiff a else acc) acc) M = false := by
  induction l generalizing acc with
  | nil => exact hacc
  | cons a t ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · rw [parity_left, hacc, horth a]
      rfl
    · exact hacc

theorem parity_xorCombo (c M : Nat) (horth : ∀ a : Fin 12, parity (rawDiff a) M = false) :
    parity (xorCombo c) M = false :=
  parity_foldl_xor c M horth (List.finRange 12) 0 (parity_zero_left M)

theorem rref_from_combos : ∀ i : Fin 12, xorCombo (rrefCombos i) = rrefMasks i := by decide +kernel

theorem rref_split : ∀ i : Fin 12,
    rrefMasks i = (rrefMasks i &&& freeBitMask) ^^^ 2 ^ pivCols i := by decide +kernel

theorem pivCols_lt : ∀ i : Fin 12, pivCols i < 20 := by decide +kernel

def bit (b : Bool) (k : Nat) : Nat := if b then 2 ^ k else 0

theorem bit_lt (b : Bool) (k n : Nat) (h : k < n) : bit b k < 2 ^ n := by
  cases b
  · simp [bit]
  · simp [bit]
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) h

theorem bit_testBit (b : Bool) (k j : Nat) :
    (bit b k).testBit j = (b && decide (k = j)) := by
  cases b
  · simp [bit]
  · simp [bit, Nat.testBit_two_pow]

def freeIdxVal (M : Nat) : Nat :=
  bit (M.testBit 3) 0 ||| bit (M.testBit 7) 1 ||| bit (M.testBit 11) 2 ||| bit (M.testBit 15) 3 |||
  bit (M.testBit 16) 4 ||| bit (M.testBit 17) 5 ||| bit (M.testBit 18) 6 ||| bit (M.testBit 19) 7

theorem freeIdxVal_lt (M : Nat) : freeIdxVal M < 256 := by
  change freeIdxVal M < 2 ^ 8
  unfold freeIdxVal
  iterate 7 refine Nat.or_lt_two_pow ?_ (bit_lt _ _ 8 (by decide))
  exact bit_lt _ _ 8 (by decide)

theorem freeIdxVal_testBit (M j : Nat) :
    (freeIdxVal M).testBit j =
      ((M.testBit 3 && decide (0 = j)) || (M.testBit 7 && decide (1 = j)) ||
       (M.testBit 11 && decide (2 = j)) || (M.testBit 15 && decide (3 = j)) ||
       (M.testBit 16 && decide (4 = j)) || (M.testBit 17 && decide (5 = j)) ||
       (M.testBit 18 && decide (6 = j)) || (M.testBit 19 && decide (7 = j))) := by
  simp only [freeIdxVal, Nat.testBit_or, bit_testBit]

def freeMaskOf (idx : Nat) : Nat :=
  bit (idx.testBit 0) 3 ||| bit (idx.testBit 1) 7 ||| bit (idx.testBit 2) 11 ||| bit (idx.testBit 3) 15 |||
  bit (idx.testBit 4) 16 ||| bit (idx.testBit 5) 17 ||| bit (idx.testBit 6) 18 ||| bit (idx.testBit 7) 19

theorem freeMaskOf_lt (idx : Nat) : freeMaskOf idx < 2 ^ 20 := by
  unfold freeMaskOf
  iterate 7 refine Nat.or_lt_two_pow ?_ (bit_lt _ _ 20 (by decide))
  exact bit_lt _ _ 20 (by decide)

theorem freeMaskOf_testBit (idx j : Nat) :
    (freeMaskOf idx).testBit j =
      ((idx.testBit 0 && decide (3 = j)) || (idx.testBit 1 && decide (7 = j)) ||
       (idx.testBit 2 && decide (11 = j)) || (idx.testBit 3 && decide (15 = j)) ||
       (idx.testBit 4 && decide (16 = j)) || (idx.testBit 5 && decide (17 = j)) ||
       (idx.testBit 6 && decide (18 = j)) || (idx.testBit 7 && decide (19 = j))) := by
  simp only [freeMaskOf, Nat.testBit_or, bit_testBit]

theorem freeBitMask_testBit : ∀ j : Fin 20,
    freeBitMask.testBit j.val =
      (decide (3 = j.val) || decide (7 = j.val) || decide (11 = j.val) || decide (15 = j.val) ||
       decide (16 = j.val) || decide (17 = j.val) || decide (18 = j.val) || decide (19 = j.val)) := by
  decide +kernel

theorem freeMaskOf_freeIdxVal (M : Nat) :
    freeMaskOf (freeIdxVal M) = M &&& freeBitMask := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : freeMaskOf (freeIdxVal M) < 2 ^ 20 := freeMaskOf_lt _
  have h2 : M &&& freeBitMask < 2 ^ 20 := by
    have ha : M &&& freeBitMask ≤ freeBitMask := Nat.and_le_right
    have hb : freeBitMask < 2 ^ 20 := by decide
    omega
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9
  | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19 =>
    rw [freeMaskOf_testBit, Nat.testBit_and, freeBitMask_testBit ⟨_, by decide⟩]
    simp only [freeIdxVal_testBit]
    simp
  | n + 20 =>
    have hge : 2 ^ 20 ≤ 2 ^ (n + 20) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 hge),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 hge)]

def reconstruct (idx : Nat) : Nat :=
  let mf := freeMaskOf idx
  mf |||
  bit (parity (rrefMasks 0) mf) 0 ||| bit (parity (rrefMasks 1) mf) 1 ||| bit (parity (rrefMasks 2) mf) 2 |||
  bit (parity (rrefMasks 3) mf) 4 ||| bit (parity (rrefMasks 4) mf) 5 ||| bit (parity (rrefMasks 5) mf) 6 |||
  bit (parity (rrefMasks 6) mf) 8 ||| bit (parity (rrefMasks 7) mf) 9 ||| bit (parity (rrefMasks 8) mf) 10 |||
  bit (parity (rrefMasks 9) mf) 12 ||| bit (parity (rrefMasks 10) mf) 13 ||| bit (parity (rrefMasks 11) mf) 14

theorem reconstruct_lt (idx : Nat) : reconstruct idx < 2 ^ 20 := by
  unfold reconstruct
  dsimp only
  iterate 12 refine Nat.or_lt_two_pow ?_ (bit_lt _ _ 20 (by decide))
  exact freeMaskOf_lt idx

theorem reconstruct_testBit (idx j : Nat) :
    (reconstruct idx).testBit j =
      ((freeMaskOf idx).testBit j ||
       (parity (rrefMasks 0) (freeMaskOf idx) && decide (0 = j)) ||
       (parity (rrefMasks 1) (freeMaskOf idx) && decide (1 = j)) ||
       (parity (rrefMasks 2) (freeMaskOf idx) && decide (2 = j)) ||
       (parity (rrefMasks 3) (freeMaskOf idx) && decide (4 = j)) ||
       (parity (rrefMasks 4) (freeMaskOf idx) && decide (5 = j)) ||
       (parity (rrefMasks 5) (freeMaskOf idx) && decide (6 = j)) ||
       (parity (rrefMasks 6) (freeMaskOf idx) && decide (8 = j)) ||
       (parity (rrefMasks 7) (freeMaskOf idx) && decide (9 = j)) ||
       (parity (rrefMasks 8) (freeMaskOf idx) && decide (10 = j)) ||
       (parity (rrefMasks 9) (freeMaskOf idx) && decide (12 = j)) ||
       (parity (rrefMasks 10) (freeMaskOf idx) && decide (13 = j)) ||
       (parity (rrefMasks 11) (freeMaskOf idx) && decide (14 = j))) := by
  simp only [reconstruct, Nat.testBit_or, bit_testBit]

theorem reconstruct_zero : reconstruct 0 = 0 := by decide

theorem rref_bit_eq (M : Nat) (i : Fin 12) (h : parity (rrefMasks i) M = false) :
    M.testBit (pivCols i) = parity (rrefMasks i) (M &&& freeBitMask) := by
  have h1 : parity (rrefMasks i) (M &&& freeBitMask) = parity (rrefMasks i &&& freeBitMask) M := by
    unfold parity
    have hand : rrefMasks i &&& (M &&& freeBitMask) = (rrefMasks i &&& freeBitMask) &&& M := by
      rw [Nat.and_comm M freeBitMask, ← Nat.and_assoc]
    rw [hand]
  rw [rref_split i, parity_left, parity_comm (2 ^ pivCols i) M,
      parity_unit M (pivCols i) (pivCols_lt i)] at h
  rw [h1]
  cases ha : parity (rrefMasks i &&& freeBitMask) M <;> cases hb : M.testBit (pivCols i) <;>
    simp [ha, hb] at h ⊢

theorem reconstruct_eq (M : Nat) (hlt : M < 1048576)
    (horth : ∀ i : Fin 12, parity (rrefMasks i) M = false) :
    M = reconstruct (freeIdxVal M) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : M < 2 ^ 20 := hlt
  have h2 : reconstruct (freeIdxVal M) < 2 ^ 20 := reconstruct_lt _
  match j with
  | 3 | 7 | 11 | 15 | 16 | 17 | 18 | 19 =>
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨_, by decide⟩]
    simp
  | 0 =>
    have hb := rref_bit_eq M 0 (horth 0)
    rw [show pivCols 0 = 0 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨0, by decide⟩, hb]
    simp
  | 1 =>
    have hb := rref_bit_eq M 1 (horth 1)
    rw [show pivCols 1 = 1 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨1, by decide⟩, hb]
    simp
  | 2 =>
    have hb := rref_bit_eq M 2 (horth 2)
    rw [show pivCols 2 = 2 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨2, by decide⟩, hb]
    simp
  | 4 =>
    have hb := rref_bit_eq M 3 (horth 3)
    rw [show pivCols 3 = 4 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨4, by decide⟩, hb]
    simp
  | 5 =>
    have hb := rref_bit_eq M 4 (horth 4)
    rw [show pivCols 4 = 5 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨5, by decide⟩, hb]
    simp
  | 6 =>
    have hb := rref_bit_eq M 5 (horth 5)
    rw [show pivCols 5 = 6 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨6, by decide⟩, hb]
    simp
  | 8 =>
    have hb := rref_bit_eq M 6 (horth 6)
    rw [show pivCols 6 = 8 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨8, by decide⟩, hb]
    simp
  | 9 =>
    have hb := rref_bit_eq M 7 (horth 7)
    rw [show pivCols 7 = 9 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨9, by decide⟩, hb]
    simp
  | 10 =>
    have hb := rref_bit_eq M 8 (horth 8)
    rw [show pivCols 8 = 10 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨10, by decide⟩, hb]
    simp
  | 12 =>
    have hb := rref_bit_eq M 9 (horth 9)
    rw [show pivCols 9 = 12 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨12, by decide⟩, hb]
    simp
  | 13 =>
    have hb := rref_bit_eq M 10 (horth 10)
    rw [show pivCols 10 = 13 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨13, by decide⟩, hb]
    simp
  | 14 =>
    have hb := rref_bit_eq M 11 (horth 11)
    rw [show pivCols 11 = 14 by decide] at hb
    rw [reconstruct_testBit, freeMaskOf_freeIdxVal, Nat.testBit_and, freeBitMask_testBit ⟨14, by decide⟩, hb]
    simp
  | n + 20 =>
    have hge : 2 ^ 20 ≤ 2 ^ (n + 20) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h1 hge),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le h2 hge)]

def wTable : List (List Nat) := [
  [0, 1048575, 1048575, 19, 1048575, 259, 270337, 1048575, 1048575, 4099, 262657, 1048575, 262177, 1048575, 1048575, 65536],
  [0, 2, 32, 34, 512, 514, 544, 69632, 8192, 8194, 8224, 65792, 8704, 65552, 65537, 65536],
  [0, 1, 16, 17, 256, 257, 272, 266240, 4096, 4097, 4112, 262400, 4352, 262160, 262145, 131072],
  [1, 1, 16, 65, 256, 1025, 1040, 266240, 4096, 16385, 16400, 262400, 16640, 262160, 262145, 262144],
  [0, 1, 16, 17, 256, 257, 272, 135168, 4096, 4097, 4112, 131328, 4352, 131088, 131073, 262144],
  [1, 1, 16, 33, 256, 513, 528, 135168, 4096, 8193, 8208, 131328, 8448, 131088, 131073, 131072],
  [2, 2, 32, 33, 512, 513, 528, 135168, 8192, 8193, 8208, 131328, 8448, 131088, 131073, 65536],
  [0, 8, 128, 33, 2048, 513, 528, 69632, 32768, 8193, 8208, 65792, 8448, 65552, 65537, 65536],
  [524288, 131073, 131088, 4352, 131328, 4112, 4097, 4096, 135168, 272, 257, 256, 17, 16, 1, 0],
  [131072, 131073, 131088, 8448, 131328, 8208, 8193, 4096, 135168, 528, 513, 256, 33, 16, 1, 1],
  [65536, 131073, 131088, 8448, 131328, 8208, 8193, 8192, 135168, 528, 513, 512, 33, 32, 2, 2],
  [65536, 65537, 65552, 8448, 65792, 8208, 8193, 16384, 69632, 528, 513, 1024, 33, 64, 4, 0],
  [65536, 262145, 262160, 16640, 262400, 16400, 16385, 16384, 266240, 1040, 1025, 1024, 65, 64, 4, 4],
  [65536, 65537, 65552, 16640, 65792, 16400, 16385, 8192, 69632, 1040, 1025, 512, 65, 32, 2, 0],
  [131072, 131074, 131104, 4352, 131584, 4112, 4097, 4096, 139264, 272, 257, 256, 17, 16, 1, 0],
  [1048575, 65539, 16897, 1048575, 16417, 1048575, 1048575, 4096, 1057, 1048575, 1048575, 256, 1048575, 16, 1, 1048575]
]

def witness (idx : Fin 256) : Nat :=
  (wTable.getD (idx.val / 16) []).getD (idx.val % 16) 0

def checkWitness (idx : Fin 256) : Bool :=
  if idx.val == 0 then true
  else
    let M := reconstruct idx.val
    let w := witness idx
    (List.finRange 45).all (fun k =>
      if falseOn w (axRow k) then
        (pts k).all (fun m => parity m M != parity w M)
      else true)

theorem all_witnesses_valid : ∀ idx : Fin 256, checkWitness idx = true := by decide +kernel

theorem force_exists_all (f : Finset V) (nf : f ≠ ∅) :
    ∃ a : V → Bool, Forced (fun a k => ¬ LinClauseSat a (ax k)) point
      (fun a => decide (Odd (f.filter (fun x => a x = true)).card)) a := by
  let M := formMask f
  have hMlt : M < 1048576 := mask_lt f
  have hMnz : M ≠ 0 := mask_nz (Finset.nonempty_iff_ne_empty.mpr nf)
  by_cases hpair : ∃ a : Fin 12, parity (rawDiff a) M = true
  · obtain ⟨a, ha⟩ := hpair
    have hval := chosen_valid a
    simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hval
    let k := (chosenPairs a).1
    let m0 := (chosenPairs a).2.1
    let m1 := (chosenPairs a).2.2
    have hxor : (parity m0 M ^^ parity m1 M) = true := by
      simpa only [rawDiff, parity_left] using ha
    have hne : parity m1 M ≠ parity m0 M := by
      intro eq
      simp [eq] at hxor
    refine ⟨assignment m0, Or.inl ⟨k, ⟨m0, hval.1, rfl⟩, assignment m1, ⟨m1, hval.2, rfl⟩, ?_⟩⟩
    simpa only [M, parity_form] using hne
  · push Not at hpair
    have horth0 : ∀ a : Fin 12, parity (rawDiff a) M = false := by
      intro a
      cases h : parity (rawDiff a) M
      · rfl
      · exact False.elim (hpair a h)
    have horth : ∀ i : Fin 12, parity (rrefMasks i) M = false := by
      intro i
      rw [← rref_from_combos i]
      exact parity_xorCombo (rrefCombos i) M horth0
    have hrec : M = reconstruct (freeIdxVal M) := reconstruct_eq M hMlt horth
    let idx : Fin 256 := ⟨freeIdxVal M, freeIdxVal_lt M⟩
    have hidx_nz : idx.val ≠ 0 := by
      intro hz
      apply hMnz
      rw [hrec]
      change reconstruct idx.val = 0
      rw [hz]
      exact reconstruct_zero
    let w := witness idx
    have hchk := all_witnesses_valid idx
    have hnzb : (idx.val == 0) = false := beq_false_of_ne hidx_nz
    simp only [checkWitness, hnzb, Bool.false_eq_true, ↓reduceIte] at hchk
    refine ⟨assignment w, Or.inr ?_⟩
    intro k hk b hb
    obtain ⟨m, hm, rfl⟩ := hb
    have hfk : falseOn (witness idx) (axRow k) = true := (false_on_spec w (axRow k) (all_rows_small k)).2 hk
    have hallk := List.all_eq_true.mp hchk k (List.mem_finRange k)
    simp only [hfk, ↓reduceIte] at hallk
    have hne_b := List.all_eq_true.mp hallk m hm
    have hne : parity m (reconstruct idx.val) ≠ parity w (reconstruct idx.val) := bne_iff_ne.mp hne_b
    change parity m (reconstruct (freeIdxVal M)) ≠ parity w (reconstruct (freeIdxVal M)) at hne
    rw [← hrec] at hne
    simpa only [M, parity_form] using hne

end PEqualNP.Outside.L_pcx_472_aux.Cert

namespace PEqualNP.Outside.L_pcx_472_aux.High

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_472_aux.Graph PEqualNP.Outside.L_pcx_472_aux.Linear PEqualNP.Outside.L_pcx_472_aux.Cert

theorem high_impossible {C : ClauseMap V} {P : Parents} {r c d : Nat}
    (rules : ∀ i ≤ r, Rule ((fun D => linOfClause D) '' PHP 5 4) C P i)
    (fr : ∀ a, FalseAt C a r)
    (ec : LocalEdge P r r c) (ed : LocalEdge P r r d) (ne : c ≠ d)
    (size : (Live P r).card ≤ 92) (wcount : 3 ≤ (WithArity P r 1).card)
    (f : Finset V) (nf : f ≠ ∅)
    (br : ∀ a, if Odd (f.filter (fun x => a x = true)).card
      then FalseAt C a c else FalseAt C a d) : False := by
  let side : (V → Bool) → Bool := fun a => decide (Odd (f.filter (fun x => a x = true)).card)
  have side_choose : ∀ a, FalseAt C a (if side a then c else d) := by
    intro a
    have h := br a
    by_cases ho : Odd (f.filter (fun x => a x = true)).card
    · simpa [side, ho] using h
    · simpa [side, ho] using h
  exact high_weak_impossible rules fr ec ed ne size wcount (Fintype.card_fin 45)
    ax formula_range point point_exists point_only side side_choose (force_exists_all f nf)

end PEqualNP.Outside.L_pcx_472_aux.High

namespace PEqualNP.Outside.L_pcx_472_aux.Orientation

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
theorem axis_sat (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a ({v}, s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, Finset.filter_singleton, h]

def lower (a : V → Bool) (S : Finset V) (v : V) : Bool :=
  if v ∈ S then false else a v

theorem filter_lower (a : V → Bool) (S f : Finset V) :
    f.filter (fun x => lower a S x = true) = (f.filter (fun x => a x = true)) \ S := by
  ext x
  by_cases hx : x ∈ S <;> simp [lower, hx]

theorem lower_sat (a : V → Bool) (S : Finset V) (q : LinEq V)
    (heven : ((q.1.filter (fun x => a x = true)) ∩ S).card % 2 = 0) :
    LinEqSat (lower a S) q ↔ LinEqSat a q := by
  unfold LinEqSat
  rw [filter_lower, Nat.odd_iff, Nat.odd_iff]
  have hc := Finset.card_sdiff_add_card_inter (q.1.filter (fun x => a x = true)) S
  have hh : ((q.1.filter (fun x => a x = true)) \ S).card % 2 = 1 ↔
      (q.1.filter (fun x => a x = true)).card % 2 = 1 := by omega
  exact iff_congr hh Iff.rfl

theorem weak_lost_neg_injective {C D : LinClause V} {f : Finset V}
    (shape : ∀ q ∈ D, q.1.card = 1 ∨ q.1 = f)
    (weak : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D)
    {a : V → Bool} (hD : ¬ LinClauseSat a D)
    {v w : V} (hv : ({v}, false) ∈ C) (hw : ({w}, false) ∈ C)
    (hv' : ({v}, false) ∉ D) (hw' : ({w}, false) ∉ D) : v = w := by
  by_contra hne
  have hc : ¬ LinClauseSat a C := fun h => hD (weak _ h)
  have value {x : V} (hx : ({x}, false) ∈ C) : a x = true := by
    cases h : a x
    · exact False.elim (hc ⟨_, hx, (axis_sat _ _ _).2 h⟩)
    · rfl
  have hal : a v = true := value hv
  have har : a w = true := value hw
  have absent {x : V} (hx : a x = true) (hx' : ({x}, false) ∉ D)
      (s : Bool) : ({x}, s) ∉ D := by
    cases s
    · exact hx'
    · intro hm
      exact hD ⟨_, hm, (axis_sat _ _ _).2 hx⟩
  have protect {S : Finset V} (hs : S ⊆ {v, w})
      (hp : ((f.filter (fun x => a x = true)) ∩ S).card % 2 = 0) :
      ¬ LinClauseSat (lower a S) D := by
    rintro ⟨q, hq, h⟩
    apply hD
    refine ⟨q, hq, ?_⟩
    rcases shape q hq with h1 | hf
    · rcases q with ⟨Q, s⟩
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      change Q = {x} at hx
      subst Q
      have hxS : x ∉ S := by
        intro hsx
        have hxv : x = v ∨ x = w := by simpa using hs hsx
        rcases hxv with rfl | rfl
        · exact absent hal hv' s hq
        · exact absent har hw' s hq
      exact (axis_sat _ _ _).2 (by
        simpa [lower, hxS] using (axis_sat _ _ _).1 h)
    · exact (lower_sat a S q (by simpa only [hf] using hp)).1 h
  have relapse {S : Finset V} (hs : S ⊆ {v, w})
      (hp : ((f.filter (fun x => a x = true)) ∩ S).card % 2 = 0)
      (hx : v ∈ S ∨ w ∈ S) : False := by
    apply protect hs hp
    apply weak
    rcases hx with h | h
    · exact ⟨_, hv, (axis_sat _ _ _).2 (by simp [lower, h])⟩
    · exact ⟨_, hw, (axis_sat _ _ _).2 (by simp [lower, h])⟩
  by_cases hvf : v ∈ f
  · by_cases hwf : w ∈ f
    · have hsub : ({v, w} : Finset V) ⊆ f.filter (fun x => a x = true) := by
        intro x hx
        rcases (show x = v ∨ x = w by simpa using hx) with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hvf, hal⟩
        · exact Finset.mem_filter.mpr ⟨hwf, har⟩
      apply relapse (S := {v, w}) (fun _ h => h) _ (Or.inl (by simp))
      rw [Finset.inter_eq_right.mpr hsub]
      simp [hne]
    · apply relapse (S := {w}) (by simp) _ (Or.inr (by simp))
      have he : (f.filter (fun x => a x = true)) ∩ {w} = ∅ := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨h, rfl⟩
        exact hwf (Finset.mem_filter.mp h).1
      simp [he]
  · apply relapse (S := {v}) (by simp) _ (Or.inl (by simp))
    have he : (f.filter (fun x => a x = true)) ∩ {v} = ∅ := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨h, rfl⟩
      exact hvf (Finset.mem_filter.mp h).1
    simp [he]

def neg (v : V) : LinEq V := ({v}, false)

theorem loss_resolvent {C D R : LinClause V} {v : V} {f : Finset V}
    (hR : R = C.erase (f, false) ∪ D.erase (f, true))
    (hn : neg v ∉ R) (hm : neg v ∈ C ∨ neg v ∈ D) : neg v ∈ C ∧ neg v ∉ D ∧ f = {v} := by
  have hbad : neg v ∉ D := by
    intro h
    apply hn
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp [neg], h⟩)
  have hC : neg v ∈ C := hm.resolve_right hbad
  refine ⟨hC, hbad, ?_⟩
  by_contra he
  apply hn
  rw [hR]
  apply Finset.mem_union_left
  exact Finset.mem_erase.mpr ⟨fun h => he ((congrArg Prod.fst h).symm), hC⟩

theorem collision_heads_card {S : Finset (Fin 5 × Fin 4)}
    (cover : ∀ (i j : Fin 5) (h : Fin 4), i ≠ j → (i, h) ∈ S ∨ (j, h) ∈ S) : 16 ≤ S.card := by
  let T := Finset.univ \ S
  have hinj : Set.InjOn Prod.snd (T : Set (Fin 5 × Fin 4)) := by
    rintro ⟨i, h⟩ hi ⟨j, k⟩ hj eq
    change h = k at eq
    subst k
    have hi' : (i, h) ∉ S := (Finset.mem_sdiff.mp hi).2
    have hj' : (j, h) ∉ S := (Finset.mem_sdiff.mp hj).2
    by_cases he : i = j
    · simp [he]
    · exact False.elim ((cover i j h he).elim hi' hj')
  have hT : T.card ≤ 4 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using (Finset.card_le_univ (T.image Prod.snd))
  have hCard : T.card = 20 - S.card := by
    simp [T, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  omega

omit [DecidableEq V] in
theorem no_axis_in_form {a : V → Bool} {D : LinClause V} {v : V}
    (hD : ¬ LinClauseSat a D) (hav : a v = true) (hn : neg v ∉ D)
    {q : LinEq V} (hq : q ∈ D) (hcard : q.1.card = 1) : v ∉ q.1 := by
  intro h
  rcases q with ⟨Q, sign⟩
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  change Q = {x} at hx
  subst Q
  have he : v = x := Finset.mem_singleton.mp h
  subst x
  cases sign
  · exact hn hq
  · exact hD ⟨_, hq, (axis_sat _ _ _).2 hav⟩

theorem keep_axis_free_parity (a : V → Bool) (q : LinEq V) {v : V}
    (hv : v ∉ q.1) : LinEqSat (lower a {v}) q ↔ LinEqSat a q := by
  apply lower_sat
  have h : (q.1.filter (fun x => a x = true)) ∩ {v} = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨hm, rfl⟩
    exact hv (Finset.mem_filter.mp hm).1
  simp [h]

theorem weak_lost_axis_supported {C D : LinClause V}
    (weak : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D)
    {a : V → Bool} (hD : ¬ LinClauseSat a D) {v : V}
    (hin : neg v ∈ C) (hout : neg v ∉ D) :
    ∃ q ∈ D, q.1.card ≠ 1 ∧ v ∈ q.1 := by
  have hav : a v = true := by
    cases h : a v
    · exact False.elim (hD (weak _ ⟨_, hin, (axis_sat _ _ _).2 h⟩))
    · rfl
  by_contra hn
  have hnew : LinClauseSat (lower a {v}) D := by
    exact weak _ ⟨_, hin, (axis_sat _ _ _).2 (by simp [lower])⟩
  obtain ⟨q, hq, hs⟩ := hnew
  have hv : v ∉ q.1 := by
    by_cases hcard : q.1.card = 1
    · exact no_axis_in_form hD hav hout hq hcard
    · exact fun h => hn ⟨q, hq, hcard, h⟩
  exact hD ⟨q, hq, (keep_axis_free_parity a q hv).1 hs⟩

theorem flip_axis_parity (a : V → Bool) (q : LinEq V) {v : V}
    (hv : v ∈ q.1) (hav : a v = true) :
    LinEqSat (lower a {v}) q ↔ ¬ LinEqSat a q := by
  unfold LinEqSat
  rw [filter_lower, Nat.odd_iff, Nat.odd_iff]
  have hs : ({v} : Finset V) ⊆ q.1.filter (fun x => a x = true) := by
    simp [hv, hav]
  have hn := Finset.card_sdiff_add_card_inter (q.1.filter (fun x => a x = true)) {v}
  rw [Finset.inter_eq_right.mpr hs, Finset.card_singleton] at hn
  have hops : ((q.1.filter (fun x => a x = true)) \ {v}).card % 2 = 1 ↔
      ¬ (q.1.filter (fun x => a x = true)).card % 2 = 1 := by omega
  cases h : q.2 <;> simp [hops]

theorem weak_pure_recovers_axis {C D : LinClause V}
    (pure : ∀ q ∈ D, q.1.card = 1)
    (weak : ∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D)
    {a : V → Bool} (hD : ¬ LinClauseSat a D) {q : LinEq V}
    (hq : q ∈ C) {v : V} (hv : v ∈ q.1) (hav : a v = true) : neg v ∈ D := by
  by_contra hn
  have hnq : ¬ LinEqSat a q := fun hs => hD (weak _ ⟨_, hq, hs⟩)
  have news : LinClauseSat (lower a {v}) D :=
    weak _ ⟨_, hq, (flip_axis_parity a q hv hav).2 hnq⟩
  obtain ⟨p, hp, hs⟩ := news
  have hvp : v ∉ p.1 := no_axis_in_form hD hav hn hp (pure p hp)
  exact hD ⟨p, hp, (keep_axis_free_parity a p hvp).1 hs⟩

end PEqualNP.Outside.L_pcx_472_aux.Orientation

namespace PEqualNP.Outside.L_pcx_472_aux.ParShape

variable {X : Type} [DecidableEq X]

abbrev Edge (P : ℕ → List ℕ) (i j : ℕ) : Prop := j ∈ P i
abbrev Reach (P : ℕ → List ℕ) := Relation.ReflTransGen (Edge P)

def Pivot (C : ℕ → Finset (X × Bool)) (P : ℕ → List ℕ) (i : ℕ) : Prop :=
  ∃ j k f, P i = [j, k] ∧ (f, false) ∈ C j ∧ (f, true) ∈ C k ∧
    C i = (C j).erase (f, false) ∪ (C k).erase (f, true)

structure Rules (C : ℕ → Finset (X × Bool)) (P : ℕ → List ℕ)
    (r u v : ℕ) : Prop where
  dec : ∀ {i j}, Edge P i j → j < i
  root : C r = ∅
  clean : ∀ {i}, Reach P r i → ∀ f, (f, false) ∈ C i → (f, true) ∉ C i
  cases : ∀ {i}, Reach P r i →
    (i = u ∨ i = v) ∨ (P i = [] ∧ C i = ∅) ∨
    (∃ j k, P i = [j, k] ∧ C i = C j ∪ C k) ∨ Pivot C P i

def opp (q : X × Bool) : X × Bool := (q.1, !q.2)

theorem all_origins {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v : ℕ}
    (R : Rules C P r u v) (i : ℕ) (hi : Reach P r i) : C i ⊆ C u ∪ C v := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases R.cases hi with (rfl | rfl) | ⟨_, heq⟩ | ⟨j, k, hp, hc⟩ | ⟨j, k, f, hp, _, _, hc⟩
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
    · simp [heq]
    all_goals
      have hj : Edge P i j := by simp [Edge, hp]
      have hk : Edge P i k := by simp [Edge, hp]
      have sj := ih j (R.dec hj) (hi.tail hj)
      have sk := ih k (R.dec hk) (hi.tail hk)
      intro x hx
      rw [hc] at hx
      rcases Finset.mem_union.mp hx with hm | hm
      · apply sj
        first | exact hm | exact Finset.mem_of_mem_erase hm
      · apply sk
        first | exact hm | exact Finset.mem_of_mem_erase hm

def Built (C : ℕ → Finset (X × Bool)) (u v i : ℕ) : Prop :=
  ∃ a b : Bool, (a = true → u ≤ i) ∧ (b = true → v ≤ i) ∧
    C i = (if a then C u else ∅) ∪ (if b then C v else ∅)

theorem before_first {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v t : ℕ}
    (R : Rules C P r u v) (no : ∀ i < t, Reach P r i → ¬ Pivot C P i)
    (i : ℕ) (hi : Reach P r i) (lt : i < t) : Built C u v i := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    rcases R.cases hi with (rfl | rfl) | ⟨hp, hc⟩ | ⟨j, k, hp, hc⟩ | piv
    · exact ⟨true, false, by simp, by simp, by simp⟩
    · exact ⟨false, true, by simp, by simp, by simp⟩
    · exact ⟨false, false, by simp, by simp, by simp [hc]⟩
    · have hj : Edge P i j := by simp [Edge, hp]
      have hk : Edge P i k := by simp [Edge, hp]
      have ji := R.dec hj
      have ki := R.dec hk
      obtain ⟨a, b, ha, hb, hj'⟩ := ih j ji (hi.tail hj) (ji.trans lt)
      obtain ⟨c, d, hc', hd, hk'⟩ := ih k ki (hi.tail hk) (ki.trans lt)
      refine ⟨a || c, b || d, ?_, ?_, ?_⟩
      · intro hab
        rcases (show a = true ∨ c = true by simpa using hab) with h | h
        · exact (ha h).trans ji.le
        · exact (hc' h).trans ki.le
      · intro hbd
        rcases (show b = true ∨ d = true by simpa using hbd) with h | h
        · exact (hb h).trans ji.le
        · exact (hd h).trans ki.le
      · rw [hc, hj', hk']
        cases a <;> cases b <;> cases c <;> cases d <;>
          simp [Finset.union_comm]
    · exact False.elim (no i lt hi piv)

theorem one_step_persist {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i j : ℕ}
    (R : Rules C P r u v) (hi : Reach P r i) (e : Edge P i j)
    (neU : i ≠ u) (neV : i ≠ v) {q : X × Bool} (hq : q ∈ C j)
    (missing : opp q ∉ C u ∪ C v) : q ∈ C i := by
  rcases R.cases hi with (he | he) | ⟨p0, _⟩ | ⟨a, b, eq, hu⟩ | ⟨a, b, f, eq, ha, hb, hu⟩
  · exact (neU he).elim
  · exact (neV he).elim
  · simp [Edge, p0] at e
  · rw [hu]
    rcases (show j = a ∨ j = b by simpa [Edge, eq] using e) with rfl | rfl
    · exact Finset.mem_union_left _ hq
    · exact Finset.mem_union_right _ hq
  · rw [hu]
    have ea : Edge P i a := by simp [Edge, eq]
    have eb : Edge P i b := by simp [Edge, eq]
    rcases (show j = a ∨ j = b by simpa [Edge, eq] using e) with rfl | rfl
    · apply Finset.mem_union_left
      refine Finset.mem_erase.mpr ⟨?_, hq⟩
      intro h
      subst q
      exact missing (all_origins R b (hi.tail eb) (by simpa [opp] using hb))
    · apply Finset.mem_union_right
      refine Finset.mem_erase.mpr ⟨?_, hq⟩
      intro h
      subst q
      exact missing (all_origins R a (hi.tail ea) (by simpa [opp] using ha))

theorem unopposed_persists {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i : ℕ}
    (R : Rules C P r u v) (path : Reach P r i) (hu : u ≤ i) (hv : v ≤ i)
    {q : X × Bool} (hq : q ∈ C i) (miss : opp q ∉ C u ∪ C v) : q ∈ C r := by
  induction path with
  | refl => exact hq
  | @tail a b route e ih =>
    have ua := hu.trans_lt (R.dec e)
    have va := hv.trans_lt (R.dec e)
    exact ih ua.le va.le (one_step_persist R route e (ne_of_gt ua) (ne_of_gt va) hq miss)

theorem no_both_forms {A B : Finset (X × Bool)} {f : X} {q : X × Bool}
    (nA : (f, true) ∉ A) (nB : (f, false) ∉ B)
    (hq : q ∈ A.erase (f, false) ∪ B.erase (f, true)) :
    opp q ∈ A ∪ B → opp q ∈ A.erase (f, false) ∪ B.erase (f, true) := by
  have neg : q ≠ (f, false) := by
    intro h
    subst q
    rcases Finset.mem_union.mp hq with h | h
    · simp at h
    · exact nB (Finset.mem_of_mem_erase h)
  have pos : q ≠ (f, true) := by
    intro h
    subst q
    rcases Finset.mem_union.mp hq with h | h
    · exact nA (Finset.mem_of_mem_erase h)
    · simp at h
  intro ho
  rcases Finset.mem_union.mp ho with hm | hm
  · apply Finset.mem_union_left
    refine Finset.mem_erase.mpr ⟨?_, hm⟩
    intro e
    exact pos (by simpa [opp] using congrArg opp e)
  · apply Finset.mem_union_right
    refine Finset.mem_erase.mpr ⟨?_, hm⟩
    intro e
    exact neg (by simpa [opp] using congrArg opp e)

theorem built_single_source {C : ℕ → Finset (X × Bool)} {u v j : ℕ}
    (build : Built C u v j) {q : X × Bool} (hit : q ∈ C j)
    (avoid : opp q ∉ C j) (other : opp q ∈ C u ∪ C v) :
    (u ≤ j ∧ C j = C u) ∨ (v ≤ j ∧ C j = C v) := by
  obtain ⟨a, b, ha, hb, eq⟩ := build
  cases a <;> cases b
  · simp at eq
    rw [eq] at hit
    simp at hit
  · exact Or.inr ⟨hb rfl, by simpa using eq⟩
  · exact Or.inl ⟨ha rfl, by simpa using eq⟩
  · simp at eq
    exact False.elim (avoid (by rwa [eq]))

theorem single_form_sources {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v : ℕ}
    (R : Rules C P r u v) (existsPivot : ∃ i, Reach P r i ∧ Pivot C P i) :
    ∃ f : X, (C u = {(f, false)} ∧ C v = {(f, true)}) ∨
             (C u = {(f, true)} ∧ C v = {(f, false)}) := by
  classical
  let t := Nat.find existsPivot
  have found : Reach P r t ∧ Pivot C P t := Nat.find_spec existsPivot
  have earlier (i : ℕ) (lt : i < t) (hi : Reach P r i) : ¬ Pivot C P i := by
    intro piv
    exact (Nat.not_le_of_lt lt) (Nat.find_min' existsPivot ⟨hi, piv⟩)
  obtain ⟨j, k, f, hp, hj, hk, ht⟩ := found.2
  have ej : Edge P t j := by simp [Edge, hp]
  have ek : Edge P t k := by simp [Edge, hp]
  have rj := found.1.tail ej
  have rk := found.1.tail ek
  have jlt := R.dec ej
  have klt := R.dec ek
  have nhj := R.clean rj f hj
  have nhk : (f, false) ∉ C k := fun h => R.clean rk f h hk
  have js := built_single_source (before_first R earlier j rj jlt) hj
    (by simpa [opp] using nhj)
    (by simpa [opp] using all_origins R k rk hk)
  have ks := built_single_source (before_first R earlier k rk klt) hk
    (by simpa [opp] using nhk)
    (by simpa [opp] using all_origins R j rj hj)
  have hsource :
      ((u ≤ j ∧ C j = C u) ∧ (v ≤ k ∧ C k = C v)) ∨
      ((v ≤ j ∧ C j = C v) ∧ (u ≤ k ∧ C k = C u)) := by
    rcases js with a | a <;> rcases ks with b | b
    · exfalso
      apply nhj
      rwa [a.2, ← b.2]
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨a, b⟩
    · exfalso
      apply nhj
      rwa [a.2, ← b.2]
  have hEnds : u ≤ t ∧ v ≤ t ∧ C u ∪ C v = C j ∪ C k := by
    rcases hsource with ⟨a, b⟩ | ⟨a, b⟩
    · exact ⟨a.1.trans jlt.le, b.1.trans klt.le, by rw [a.2, b.2]⟩
    · exact ⟨b.1.trans klt.le, a.1.trans jlt.le, by rw [a.2, b.2, Finset.union_comm]⟩
  obtain ⟨hu, hv, he⟩ := hEnds
  have hEmpty : C t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    by_cases hq' : opp q ∈ C u ∪ C v
    · have hq'' : opp q ∈ C t := by
        rw [ht]
        apply no_both_forms nhj nhk (ht ▸ hq)
        simpa only [he] using hq'
      rcases q with ⟨g, b⟩
      cases b
      · exact R.clean found.1 g hq (by simpa [opp] using hq'')
      · exact R.clean found.1 g (by simpa [opp] using hq'') hq
    · have hbad := unopposed_persists R found.1 hu hv hq hq'
      simp [R.root] at hbad
  have ha : (C j).erase (f, false) = ∅ ∧ (C k).erase (f, true) = ∅ :=
    Finset.union_eq_empty.mp (ht.symm.trans hEmpty)
  have hj' : C j = {(f, false)} := by
    rw [← Finset.insert_erase hj, ha.1]
    rfl
  have hk' : C k = {(f, true)} := by
    rw [← Finset.insert_erase hk, ha.2]
    rfl
  refine ⟨f, ?_⟩
  rcases hsource with ⟨a, b⟩ | ⟨a, b⟩
  · exact Or.inl ⟨a.2.symm.trans hj', b.2.symm.trans hk'⟩
  · exact Or.inr ⟨b.2.symm.trans hk', a.2.symm.trans hj'⟩

theorem pass_at {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i j : ℕ}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (hi : Reach P r i) (e : Edge P i j) (neU : i ≠ u) (neV : i ≠ v) :
    C j ⊆ C i := by
  rcases R.cases hi with (he | he) | ⟨p0, _⟩ | ⟨a, b, eq, hu⟩ | piv
  · exact (neU he).elim
  · exact (neV he).elim
  · simp [Edge, p0] at e
  · rw [hu]
    rcases (show j = a ∨ j = b by simpa [Edge, eq] using e) with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  · exact (no i hi piv).elim

theorem pure_after_sources {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ} {r u v i : ℕ}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (hi : Reach P r i) (hu : u ≤ i) (hv : v ≤ i) : C i = ∅ := by
  induction hi with
  | refl => exact R.root
  | @tail a b path0 e ih =>
    have ult := hu.trans_lt (R.dec e)
    have vlt := hv.trans_lt (R.dec e)
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have h := pass_at R no path0 e (ne_of_gt ult) (ne_of_gt vlt) hx
    rw [ih ult.le vlt.le] at h
    simp at h

theorem mark_to_reach {P : ℕ → List ℕ} {E : ℕ → ℕ → Prop} {i j : ℕ}
    (sub : ∀ {a b}, E a b → Edge P a b)
    (path : Relation.ReflTransGen E i j) : Reach P i j := by
  induction path with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail (sub e)

theorem passive_cross_core {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ}
    {E : ℕ → ℕ → Prop} {r u v i : ℕ} {q : X × Bool}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (sub : ∀ {a b}, E a b → Edge P a b)
    (path : Relation.ReflTransGen E r i) (bound : u ≤ i) (hit : q ∈ C i)
    (tail : Relation.ReflTransGen E i u) :
    ∃ j, Relation.ReflTransGen E r v ∧ E v j ∧ Relation.ReflTransGen E j u ∧ q ∈ C j := by
  induction path with
  | refl => simp [R.root] at hit
  | @tail a b path0 e ih =>
    by_cases h : a = v
    · subst a
      exact ⟨b, path0, e, tail, hit⟩
    · have dec := R.dec (sub e)
      have ul := bound.trans_lt dec
      have here := pass_at R no (mark_to_reach sub path0) (sub e) (ne_of_gt ul) h hit
      exact ih ul.le here (.head e tail)

theorem passive_cross {C : ℕ → Finset (X × Bool)} {P : ℕ → List ℕ}
    {E : ℕ → ℕ → Prop} {r u v : ℕ} {q : X × Bool}
    (R : Rules C P r u v) (no : ∀ n, Reach P r n → ¬ Pivot C P n)
    (sub : ∀ {a b}, E a b → Edge P a b)
    (path : Relation.ReflTransGen E r u) (hit : q ∈ C u) :
    ∃ j, Relation.ReflTransGen E r v ∧ E v j ∧ Relation.ReflTransGen E j u ∧ q ∈ C j :=
  passive_cross_core R no sub path (Nat.le_refl _) hit .refl

open PEqualNP.ProofComplexity

variable {V : Type} [DecidableEq V]

def parity (C : LinClause V) : LinClause V := C.filter (fun q => q.1.card ≠ 1)

omit [DecidableEq V] in
theorem parity_mem {C : LinClause V} {q : LinEq V} :
    q ∈ parity C ↔ q ∈ C ∧ q.1.card ≠ 1 := by
  simp [parity]

theorem filtered_res {L H R : LinClause V} {f : Finset V}
    (he : R = L.erase (f, false) ∪ H.erase (f, true)) :
    parity R = (parity L).erase (f, false) ∪ (parity H).erase (f, true) := by
  simp [parity, he, Finset.filter_erase, Finset.filter_union]

theorem filtered_axis_res {L H R : LinClause V} {f : Finset V}
    (he : R = L.erase (f, false) ∪ H.erase (f, true)) (hf : f.card = 1) :
    parity R = parity L ∪ parity H := by
  rw [filtered_res he]
  have hnL : (f, false) ∉ parity L := by simp [parity, hf]
  have hnH : (f, true) ∉ parity H := by simp [parity, hf]
  rw [Finset.erase_eq_of_notMem hnL, Finset.erase_eq_of_notMem hnH]

omit [DecidableEq V] in
theorem parity_clean_of_false {C : LinClause V} {a : V → Bool}
    (ha : ¬ LinClauseSat a C) (f : Finset V) :
    (f, false) ∈ parity C → (f, true) ∉ parity C := by
  intro h0 h1
  have h0 := (parity_mem.mp h0).1
  have h1 := (parity_mem.mp h1).1
  by_cases hd : Odd (f.filter (fun x => a x = true)).card
  · exact ha ⟨_, h1, by simp [LinEqSat, hd]⟩
  · exact ha ⟨_, h0, by simp [LinEqSat, hd]⟩

def clip (P : ℕ → List ℕ) (r i : ℕ) : List ℕ :=
  if i ≤ r then P i else []

theorem edge_clip {P : ℕ → List ℕ} {r i j : ℕ} :
    Edge (clip P r) i j ↔ i ≤ r ∧ j ∈ P i := by
  by_cases hi : i ≤ r <;> simp [Edge, clip, hi]

theorem clip_desc {P : ℕ → List ℕ} {r : ℕ}
    (steps : ∀ i ≤ r, ∀ j ∈ P i, j < i)
    {i j : ℕ} (e : Edge (clip P r) i j) : j < i :=
  steps i (edge_clip.mp e).1 j (edge_clip.mp e).2

theorem clip_le {P : ℕ → List ℕ} {r i : ℕ}
    (steps : ∀ i ≤ r, ∀ j ∈ P i, j < i) (h : Reach (clip P r) r i) : i ≤ r := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ e ih => exact (clip_desc steps e).le.trans ih

theorem mk_rules {C : ℕ → LinClause V} {P : ℕ → List ℕ} {F : Set (LinClause V)}
    {r u v : ℕ}
    (given : ∀ i ≤ r,
      (P i = [] ∧ C i ∈ F) ∨
      (∃ j < i, P i = [j] ∧ (∀ a, LinClauseSat a (C j) → LinClauseSat a (C i))) ∨
      (∃ j < i, ∃ k < i, P i = [j, k] ∧ IsLinResolvent (C j) (C k) (C i)))
    (pure : ∀ D ∈ F, ∀ q ∈ D, q.1.card = 1)
    (empty : C r = ∅) (useful : ∀ i ≤ r, ∃ a, ¬ LinClauseSat a (C i))
    (weak_cover : ∀ i, Reach (clip P r) r i → (P i).length = 1 → i = u ∨ i = v) :
    Rules (fun i => parity (C i)) (clip P r) r u v := by
  have desc : ∀ i ≤ r, ∀ j ∈ P i, j < i := by
    intro i hi j hj
    rcases given i hi with ⟨p0, _⟩ | ⟨k, lt, hp, _⟩ | ⟨k, lt, l, llt, hp, _⟩
    · simp [p0] at hj
    · have eq : j = k := by simpa [hp] using hj
      rwa [eq]
    · rcases (show j = k ∨ j = l by simpa [hp] using hj) with rfl | rfl
      · exact lt
      · exact llt
  refine ⟨clip_desc desc, by simp [parity, empty], ?_, ?_⟩
  · intro i hi f
    obtain ⟨a, ha⟩ := useful i (clip_le desc hi)
    exact parity_clean_of_false ha f
  · intro i hi
    have ir := clip_le desc hi
    have eq : clip P r i = P i := by simp [clip, ir]
    rcases given i ir with ⟨p0, hF⟩ | ⟨j, lt, hp, _⟩ | ⟨j, jlt, k, klt, hp, res⟩
    · right; left
      refine ⟨eq.trans p0, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
      intro q hq
      obtain ⟨hm, hn⟩ := parity_mem.mp hq
      exact hn (pure _ hF q hm)
    · exact Or.inl (weak_cover i hi (by simp [hp]))
    · obtain ⟨f, hL, hR, he⟩ := res
      by_cases h : f.card = 1
      · exact Or.inr (Or.inr (Or.inl ⟨j, k, eq.trans hp, filtered_axis_res he h⟩))
      · exact Or.inr (Or.inr (Or.inr
          ⟨j, k, f, eq.trans hp, parity_mem.mpr ⟨hL, h⟩, parity_mem.mpr ⟨hR, h⟩, filtered_res he⟩))

end PEqualNP.Outside.L_pcx_472_aux.ParShape

namespace PEqualNP.Outside.L_pcx_472_aux.Orientation

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_472_aux.ParShape

variable {V : Type} [DecidableEq V]

def Wide (C : LinClause V) : Prop :=
  ¬ ∃ f : Finset V, ∀ q ∈ C, q.1.card = 1 ∨ q.1 = f

omit [DecidableEq V] in
theorem not_wide_of_empty_parity {C : LinClause V} (empty : parity C = ∅) : ¬ Wide C := by
  intro h
  apply h
  refine ⟨∅, ?_⟩
  intro q hq
  left
  by_contra hn
  have h := parity_mem.mpr ⟨hq, hn⟩
  rw [empty] at h
  simp at h

omit [DecidableEq V] in
theorem not_wide_of_singleton_parity {C : LinClause V} {f : Finset V} {b : Bool}
    (single : parity C = {(f, b)}) : ¬ Wide C := by
  intro h
  apply h
  refine ⟨f, ?_⟩
  intro q hq
  by_cases hn : q.1.card = 1
  · exact Or.inl hn
  · have h := parity_mem.mpr ⟨hq, hn⟩
    rw [single] at h
    exact Or.inr (congrArg Prod.fst (Finset.mem_singleton.mp h))

def ParityRules {V : Type} [DecidableEq V] (C : ℕ → LinClause V) (P : ℕ → List ℕ)
    (r u v : ℕ) : Prop := Rules (fun i => parity (C i)) P r u v

theorem wide_forbids_pivot {C : ℕ → LinClause V} {P : ℕ → List ℕ}
    {r u v i : ℕ} (R : ParityRules C P r u v)
    (location : i = u ∨ i = v) (wide : Wide (C i)) :
    ∀ j, Reach P r j → ¬ Pivot (fun k => parity (C k)) P j := by
  intro j hr hp
  obtain ⟨f, hh⟩ := single_form_sources R ⟨j, hr, hp⟩
  rcases location with rfl | rfl <;> rcases hh with ⟨a, b⟩ | ⟨a, b⟩
  · exact not_wide_of_singleton_parity a wide
  · exact not_wide_of_singleton_parity a wide
  · exact not_wide_of_singleton_parity b wide
  · exact not_wide_of_singleton_parity b wide

theorem wide_source_is_older {C : ℕ → LinClause V} {P : ℕ → List ℕ}
    {r u v i : ℕ} (R : ParityRules C P r u v) (order : u ≤ v)
    (seen : Reach P r i) (location : i = u ∨ i = v) (wide : Wide (C i)) : i = u := by
  rcases location with h | e
  · exact h
  · subst i
    have np := wide_forbids_pivot R (Or.inr rfl) wide
    exact (not_wide_of_empty_parity (pure_after_sources R np seen order (Nat.le_refl _)) wide).elim

omit [DecidableEq V] in
theorem path_false {C : ℕ → LinClause V} {E : ℕ → ℕ → Prop} {a : V → Bool}
    {r i : ℕ} (rootFalse : ¬ LinClauseSat a (C r))
    (edgeFalse : ∀ {j k}, E j k → ¬ LinClauseSat a (C k))
    (path : Relation.ReflTransGen E r i) : ¬ LinClauseSat a (C i) := by
  cases path with
  | refl => exact rootFalse
  | tail _ e => exact edgeFalse e

theorem recover_large_weak {C : ℕ → LinClause V} {P : ℕ → List ℕ} {E : ℕ → ℕ → Prop}
    {r u v j : ℕ} (R : ParityRules C P r u v) (order : u ≤ v)
    (wide : Wide (C u))
    (old_weak : ∀ a : V → Bool, LinClauseSat a (C j) → LinClauseSat a (C u))
    (new_weak : ∀ k, Edge P v k → ∀ a : V → Bool, LinClauseSat a (C k) → LinClauseSat a (C v))
    (sub : ∀ {i k}, E i k → Edge P i k) {a : V → Bool}
    (rootFalse : ¬ LinClauseSat a (C r))
    (edgeFalse : ∀ {i k}, E i k → ¬ LinClauseSat a (C k))
    (walk : Relation.ReflTransGen E r u)
    {x : V} (hneg : neg x ∈ C j) (hgone : neg x ∉ C u) :
    Relation.ReflTransGen E r v ∧ Relation.ReflTransGen E v u ∧ neg x ∈ C v := by
  have fu := path_false rootFalse edgeFalse walk
  have tj : ¬ LinClauseSat a (C j) := fun h => fu (old_weak a h)
  have hx : a x = true := by
    cases h : a x
    · exact False.elim (tj ⟨_, hneg, (axis_sat _ _ _).2 h⟩)
    · rfl
  obtain ⟨q, hq, hn, qx⟩ := weak_lost_axis_supported old_weak fu hneg hgone
  have no := wide_forbids_pivot R (Or.inl rfl) wide
  obtain ⟨k, pathv, ek, suf, hsrc⟩ := passive_cross R no sub walk (parity_mem.mpr ⟨hq, hn⟩)
  have pure : ∀ p ∈ C v, p.1.card = 1 := by
    intro p hp
    have h := pure_after_sources R no (mark_to_reach sub pathv) order (Nat.le_refl _)
    by_contra hn'
    have e := parity_mem.mpr ⟨hp, hn'⟩
    rw [h] at e
    simp at e
  exact ⟨pathv, .head ek suf, weak_pure_recovers_axis pure (new_weak k (sub ek))
    (path_false rootFalse edgeFalse pathv) (parity_mem.mp hsrc).1 qx hx⟩

theorem two_cover_sources {S T : Finset ℕ} {root : ℕ}
    (rootLive : root ∈ T) (inLive : S ⊆ T) (small : S.card ≤ 2) :
    ∃ u v, u ∈ T ∧ v ∈ T ∧ u ≤ v ∧ (S.Nonempty → u ∈ S ∧ v ∈ S) ∧ ∀ i ∈ S, i = u ∨ i = v := by
  by_cases h0 : S = ∅
  · exact ⟨root, root, rootLive, rootLive, Nat.le_refl _, by simp [h0], by simp [h0]⟩
  by_cases h1 : S.card = 1
  · obtain ⟨u, rfl⟩ := Finset.card_eq_one.mp h1
    have live : u ∈ T := inLive (by simp)
    exact ⟨u, u, live, live, Nat.le_refl _, by simp, by simp⟩
  have htwo : 1 < S.card := by
    have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0)
    omega
  obtain ⟨a, ha, b, hb, ne⟩ := Finset.one_lt_card.mp htwo
  have both : ({a, b} : Finset ℕ) ⊆ S := by
    intro x hx
    rcases (show x = a ∨ x = b by simpa using hx) with rfl | rfl
    · exact ha
    · exact hb
  have equal : ({a, b} : Finset ℕ) = S :=
    Finset.eq_of_subset_of_card_le both (by simpa [ne] using small)
  rcases le_total a b with ord | ord
  · refine ⟨a, b, inLive ha, inLive hb, ord, (fun _ => ⟨ha, hb⟩), ?_⟩
    intro x hx
    simpa [← equal] using hx
  · refine ⟨b, a, inLive hb, inLive ha, ord, (fun _ => ⟨hb, ha⟩), ?_⟩
    intro x hx
    have e : x = a ∨ x = b := by simpa [← equal] using hx
    exact e.symm

end PEqualNP.Outside.L_pcx_472_aux.Orientation

namespace PEqualNP.Outside.L_pcx_472_aux.Charge

open PEqualNP.Outside.L_pcx_472_aux.Bridge PEqualNP.Outside.L_pcx_472_aux.Graph PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_472_aux.Orientation (neg loss_resolvent collision_heads_card weak_lost_neg_injective)

variable {V : Type} [DecidableEq V]
variable {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents} {r : Nat}

def NegOnly (D : LinClause V) : Prop := ∀ q ∈ D, q.2 = false

def FirstUse (i j : Nat) : Prop :=
  Edge P i j ∧ P j = [] ∧ NegOnly (C j)

theorem unique_firstUse {i j k : Nat} (rule : Rule F C P i)
    (h : FirstUse (P := P) (C := C) i j) (g : FirstUse (P := P) (C := C) i k) : j = k := by
  rcases h with ⟨hj, _, hn⟩
  rcases g with ⟨hk, _, gn⟩
  rcases rule with ⟨p0, _⟩ | ⟨l, _, pl, _⟩ | ⟨l, _, m, _, pm, f, _, mf, _⟩
  · simp [Edge, p0] at hj
  · simp only [Edge, pl, List.mem_singleton] at hj hk
    exact hj.trans hk.symm
  · simp only [Edge, pm, List.mem_cons, List.not_mem_nil, or_false] at hj hk
    rcases hj with rfl | rfl
    · rcases hk with rfl | rfl
      · rfl
      · have no := gn (f, true) mf
        contradiction
    · have no := hn (f, true) mf
      contradiction

def Loss (i j : Nat) (v : V) : Prop :=
  Edge P i j ∧ P j ≠ [] ∧ neg v ∉ C i ∧ neg v ∈ C j

theorem loss_rule {i j : Nat} {v : V} (rule : Rule F C P i)
    (h : Loss (P := P) (C := C) i j v) :
    (P i = [j] ∧ ∀ a, LinClauseSat a (C j) → LinClauseSat a (C i)) ∨
    (∃ k, P i = [j, k] ∧ (({v}, true) : LinEq V) ∈ C k ∧
      C i = (C j).erase (neg v) ∪ (C k).erase ({v}, true)) := by
  obtain ⟨he, _, hi, hj⟩ := h
  rcases rule with ⟨p0, _⟩ | ⟨l, _, pl, hw⟩ | ⟨l, _, k, _, pr, f, _, hfk, rr⟩
  · simp [Edge, p0] at he
  · have eq : j = l := by simpa [Edge, pl] using he
    subst l
    exact Or.inl ⟨pl, hw⟩
  · have mem : neg v ∈ C l ∨ neg v ∈ C k := by
      simp only [Edge, pr, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> tauto
    obtain ⟨_, nk, mv⟩ := loss_resolvent rr hi mem
    have eq : j = l := by
      simp only [Edge, pr, List.mem_cons, List.not_mem_nil, or_false] at he
      exact he.resolve_right (fun e => nk (e ▸ hj))
    subst l
    subst f
    exact Or.inr ⟨k, pr, hfk, rr⟩

theorem loss_not_firstUse {i j k : Nat} {v : V} (rule : Rule F C P i)
    (h : Loss (P := P) (C := C) i j v) :
    ¬ FirstUse (P := P) (C := C) i k := by
  rintro ⟨ek, k0, kn⟩
  have j0 := h.2.1
  rcases loss_rule rule h with ⟨pl, _⟩ | ⟨m, pl, hm, _⟩
  · have eq : k = j := by simpa [Edge, pl] using ek
    exact j0 (eq ▸ k0)
  · simp only [Edge, pl, List.mem_cons, List.not_mem_nil, or_false] at ek
    rcases ek with rfl | rfl
    · exact j0 k0
    · have no := kn _ hm
      contradiction

theorem binary_loss_unique {i j k : Nat} {v w : V} (rule : Rule F C P i)
    (two : (P i).length = 2) (h : Loss (P := P) (C := C) i j v)
    (g : Loss (P := P) (C := C) i k w) : v = w := by
  rcases loss_rule rule h with ⟨e, _⟩ | ⟨a, e, _, rv⟩
  · simp [e] at two
  rcases loss_rule rule g with ⟨f, _⟩ | ⟨b, f, _, _⟩
  · simp [f] at two
  have same : j = k := (List.cons.inj (e.symm.trans f)).1
  subst k
  have has := g.2.2.2
  by_contra ne
  apply g.2.2.1
  rw [rv]
  refine Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, has⟩)
  intro he
  apply ne
  simpa [neg] using (congrArg Prod.fst he).symm

theorem first_loss {E : Nat → Nat → Prop} {i j : Nat} {v : V}
    (w : Walk E i j) (h0 : neg v ∉ C i) (h1 : neg v ∈ C j) :
    ∃ p q, Walk (fun u v' => E u v' ∧ neg v ∉ C v') i p ∧
       E p q ∧ Walk E q j ∧ neg v ∉ C p ∧ neg v ∈ C q := by
  induction w using Relation.ReflTransGen.head_induction_on with
  | refl => exact (h0 h1).elim
  | @head i x e w ih =>
    by_cases hx : neg v ∈ C x
    · exact ⟨i, x, .refl, e, w, h0, hx⟩
    · obtain ⟨p, q, pr, ep, suf, np, yq⟩ := ih hx
      exact ⟨p, q, .head ⟨e, hx⟩ pr, ep, suf, np, yq⟩

abbrev Grid := Fin 5 × Fin 4
abbrev Collision := {t : Fin 5 × Fin 5 × Fin 4 // t.1 < t.2.1}

def first (k : Collision) : Grid := (k.val.1, k.val.2.2)
def second (k : Collision) : Grid := (k.val.2.1, k.val.2.2)
def collision (k : Collision) : LinClause Grid := {neg (first k), neg (second k)}

theorem nCollision : Fintype.card Collision = 40 := by decide +kernel

theorem neg_inj {x y : Grid} (h : neg x = neg y) : x = y := by
  exact Finset.singleton_inj.1 (congrArg Prod.fst h)

theorem collision_injective : Function.Injective collision := by
  intro k l h
  have h1 : neg (first k) ∈ collision l := h ▸ Finset.mem_insert_self _ _
  have h2 : neg (second k) ∈ collision l := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [collision, Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with e1 | e1
  · have hf : first k = first l := neg_inj e1
    rcases h2 with e2 | e2
    · have hs : second k = first l := neg_inj e2
      have hfk : first k = second k := hf.trans hs.symm
      exact False.elim ((ne_of_lt k.2) (congrArg Prod.fst hfk))
    · have hs : second k = second l := neg_inj e2
      rcases Prod.mk.inj hf with ⟨c1, c3⟩
      rcases Prod.mk.inj hs with ⟨c2, _⟩
      exact Subtype.ext (Prod.ext c1 (Prod.ext c2 c3))
  · have hf : first k = second l := neg_inj e1
    rcases h2 with e2 | e2
    · have hs : second k = first l := neg_inj e2
      have h1lt : k.val.1 < k.val.2.1 := k.2
      have h2lt : l.val.1 < l.val.2.1 := l.2
      have e1' : k.val.1 = l.val.2.1 := congrArg Prod.fst hf
      have e2' : k.val.2.1 = l.val.1 := congrArg Prod.fst hs
      omega
    · have hs : second k = second l := neg_inj e2
      have hfk : first k = second k := hf.trans hs.symm
      exact False.elim ((ne_of_lt k.2) (congrArg Prod.fst hfk))

theorem collision_negative (k : Collision) : NegOnly (collision k) := by
  intro a ha
  simp only [collision, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;> rfl

theorem heads_large (endpoint : Collision → Grid)
    (each : ∀ k, endpoint k = first k ∨ endpoint k = second k) :
    16 ≤ (Finset.univ.image endpoint).card := by
  apply collision_heads_card
  intro i j h ne
  rcases lt_or_gt_of_ne ne with ij | ji
  · let k : Collision := ⟨(i, j, h), ij⟩
    have hm : endpoint k ∈ (Finset.univ.image endpoint : Finset Grid) := Finset.mem_image.2 ⟨_, by simp, rfl⟩
    rcases each k with eq | eq
    · simpa [k, eq, first] using Or.inl (b := (j, h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm
    · simpa [k, eq, second] using Or.inr (a := (i, h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm
  · let k : Collision := ⟨(j, i, h), ji⟩
    have hm : endpoint k ∈ (Finset.univ.image endpoint : Finset Grid) := Finset.mem_image.2 ⟨_, by simp, rfl⟩
    rcases each k with eq | eq
    · simpa [k, eq, first] using Or.inr (a := (i, h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm
    · simpa [k, eq, second] using Or.inl (b := (j, h) ∈ (Finset.univ.image endpoint : Finset Grid)) hm

theorem collision_charges {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (axes : 45 ≤ (WithArity P r 0).card)
    (good : Nat → Nat → Grid → Prop)
    (is_loss : ∀ i j v, good i j v → Loss (C := C) (P := P) i j v)
    (one_loss : ∀ i j k v w, i ∈ Live P r → good i j v → good i k w → v = w)
    (witnesses : ∀ k : Collision, ∃ i j, i ∈ Live P r ∧ Edge P i j ∧ P j = [] ∧ C j = collision k ∧
        ∃ v l t, (v = first k ∨ v = second k) ∧ l ∈ Live P r ∧ good l t v) :
    101 ≤ (Live P r).card := by
  classical
  choose i j hi eij j0 cj kk using witnesses
  choose endpoint loss target endp loss_live loss_good using kk
  have firstuse (k : Collision) : FirstUse (C := C) (P := P) (i k) (j k) :=
    ⟨eij k, j0 k, cj k ▸ collision_negative k⟩
  have rule_live : ∀ u ∈ Live P r, Rule F C P u := by
    intro u hu
    exact rules _ (walk_le (bounded_edge rules) ((live_iff rules).1 hu))
  have ii : Function.Injective i := by
    intro k l eq
    have same := unique_firstUse (rule_live (i k) (hi k)) (firstuse k) (eq ▸ firstuse l)
    have e := (cj k).symm.trans ((congrArg C same).trans (cj l))
    exact collision_injective e
  let I := Finset.univ.image i
  have ic : I.card = 40 := by simp [I, Finset.card_image_of_injective _ ii, nCollision]
  let S := Finset.univ.image endpoint
  have sc : 16 ≤ S.card := heads_large endpoint endp
  have all : ∀ v ∈ S, ∃ l t, l ∈ Live P r ∧ good l t v := by
    intro v hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hv
    exact ⟨loss k, target k, loss_live k, loss_good k⟩
  choose ll tt hl ht using all
  let L := S.attach.image (fun v => ll v.val v.property)
  have lc : L.card = S.card := by
    rw [Finset.card_image_of_injective, Finset.card_attach]
    intro a b ee
    apply Subtype.ext
    change ll a.val a.property = ll b.val b.property at ee
    have hb := ht b.val b.property
    rw [← ee] at hb
    exact one_loss _ _ _ _ _ (hl a.val a.property) (ht a.val a.property) hb
  let A := WithArity P r 0
  have Asub : A ⊆ Live P r := Finset.filter_subset _ _
  have Isub : I ⊆ Live P r := by
    intro u hu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hu
    exact hi k
  have Lsub : L ⊆ Live P r := by
    intro u hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hu
    exact hl v.val v.property
  have AI : Disjoint A I := by
    apply Finset.disjoint_left.2
    intro u au iu
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 iu
    have p0 := (Finset.mem_filter.1 au).2
    simp at p0
    have ee := eij k
    simp [Edge, p0] at ee
  have AL : Disjoint A L := by
    apply Finset.disjoint_left.2
    intro u au lu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 lu
    have p0 := (Finset.mem_filter.1 au).2
    simp at p0
    have ee := (is_loss _ _ _ (ht v.val v.property)).1
    simp [Edge, p0] at ee
  have IL : Disjoint I L := by
    apply Finset.disjoint_left.2
    intro u iu lu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 lu
    obtain ⟨k, _, e⟩ := Finset.mem_image.1 iu
    exact loss_not_firstUse (rule_live _ (hl v.val v.property))
      (is_loss _ _ _ (ht v.val v.property)) (e ▸ firstuse k)
  have hist : A ∪ I ∪ L ⊆ Live P r :=
    Finset.union_subset (Finset.union_subset Asub Isub) Lsub
  have bound := Finset.card_le_card hist
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.2 ⟨AL, IL⟩),
    Finset.card_union_of_disjoint AI, ic, lc] at bound
  change 45 ≤ A.card at axes
  omega

def SmallForms (D : LinClause V) : Prop :=
  ∃ q : Finset V, ∀ e ∈ D, e.1.card = 1 ∨ e.1 = q

def GoodLoss (i j : Nat) (v : V) : Prop :=
  Loss (C := C) (P := P) i j v ∧ (∃ a, FalseAt C a i) ∧
    ((P i).length = 2 ∨ SmallForms (C i))

theorem good_unique {i j k : Nat} {v w : V} (rule : Rule F C P i)
    (h : GoodLoss (C := C) (P := P) i j v)
    (g : GoodLoss (C := C) (P := P) i k w) : v = w := by
  obtain ⟨hl, ⟨a, ff⟩, two | ⟨q, shape⟩⟩ := h
  · exact binary_loss_unique rule two hl g.1
  · rcases loss_rule rule hl with ⟨vj, weak⟩ | ⟨l, vv, _, _⟩
    · have eq : k = j := by simpa [Edge, vj] using g.1.1
      subst k
      exact weak_lost_neg_injective shape weak ff hl.2.2.2 g.1.2.2.2 hl.2.2.1 g.1.2.2.1
    · exact binary_loss_unique rule (by simp [vv]) hl g.1

theorem collision_residue {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {i j : Nat} {k : Collision} (rule : Rule F C P i)
    (he : Edge P i j) (cj : C j = collision k) (two : (P i).length = 2) :
    neg (first k) ∈ C i ∨ neg (second k) ∈ C i := by
  rcases rule with ⟨p0, _⟩ | ⟨l, _, p1, _⟩ | ⟨l, _, m, _, pm, f, fl, fm, rr⟩
  · simp [p0] at two
  · simp [p1] at two
  · simp only [Edge, pm, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · have first_ne_second : first k ≠ second k := fun eq => (ne_of_lt k.property) (congrArg Prod.fst eq)
      rw [cj] at fl rr
      have opts : (f, false) = neg (first k) ∨ (f, false) = neg (second k) := by
        simpa only [collision, Finset.mem_insert, Finset.mem_singleton] using fl
      rcases opts with ho | ho
      · right
        rw [rr]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun eq => first_ne_second
          ((Finset.singleton_inj.1 (congrArg Prod.fst (eq.trans ho))).symm), by simp [collision]⟩)
      · left
        rw [rr]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨fun eq => first_ne_second
          (Finset.singleton_inj.1 (congrArg Prod.fst (eq.trans ho))), by simp [collision]⟩)
    · have zz := collision_negative k (f, true) (cj ▸ fm)
      contradiction

def Mark (C : ClauseMap V) (P : Parents) (r : Nat) (a : V → Bool) (i j : Nat) : Prop :=
  LocalEdge P r i j ∧ FalseAt C a j

omit [DecidableEq V] in
theorem rootRawAbsent {v : V} (h : ∀ a, FalseAt C a r) : neg v ∉ C r := by
  intro hm
  apply h (fun _ => false)
  exact ⟨_, hm, by simp [neg, LinEqSat]⟩

omit [DecidableEq V] in
theorem false_on_mark {a : V → Bool} {i j : Nat}
    (w : Walk (Mark C P r a) i j) (h : FalseAt C a i) : FalseAt C a j := by
  rcases w.cases_tail with rfl | ⟨k, _, hk⟩
  · exact h
  · exact hk.2

omit [DecidableEq V] in
theorem has_child_from_path {a : V → Bool} {i j k : Nat}
    (w : Walk (Mark C P r a) i j) (out : Edge P j k) : P i ≠ [] := by
  rcases w.cases_head with rfl | ⟨l, hl, _⟩
  · intro he
    simp [Edge, he] at out
  · intro he
    have ho := hl.1.2
    simp [Edge, he] at ho

def Recover (C : ClauseMap V) (P : Parents) (r : Nat) : Prop :=
  ∀ (a : V → Bool) i j v, P i = [j] → ¬ SmallForms (C i) →
    neg v ∈ C j → neg v ∉ C i →
    ∀ Q : Nat → Nat → Prop, (∀ {u z}, Q u z → Mark C P r a u z) →
      Walk Q r i → ∃ t, Walk Q r t ∧ Walk Q t i ∧ neg v ∈ C t

theorem charge_path {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (fr : ∀ a, FalseAt C a r) (rootInternal : P r ≠ []) (recover : Recover C P r)
    (k : Collision) (crit : ∃ a, ∀ D ∈ F, ¬ LinClauseSat a D → D = collision k) :
    ∃ i j, i ∈ Live P r ∧ Edge P i j ∧ P j = [] ∧ C j = collision k ∧
      ∃ v l t, (v = first k ∨ v = second k) ∧ l ∈ Live P r ∧
        GoodLoss (C := C) (P := P) l t v := by
  classical
  obtain ⟨a, ua⟩ := crit
  obtain ⟨j, j0, jf, af, wj⟩ := localized_route rules a le_rfl (fr a)
  have cj : C j = collision k := ua _ jf af
  obtain ⟨i, wi0, ei0⟩ := wj.cases_tail.resolve_left (fun e => rootInternal (e ▸ j0))
  have wi : Walk (Mark C P r a) r i :=
    walk_sub (fun e => ⟨e.1, e.2.2⟩) wi0
  have ir : i ≤ r := ei0.1.1
  have eij : Edge P i j := ei0.1.2
  have fi := false_on_mark wi (fr a)
  have il := (live_iff rules).2 (walk_sub (fun e => e.1) wi)
  refine ⟨i, j, il, eij, j0, cj, ?_⟩
  have pay : ∃ v t, (v = first k ∨ v = second k) ∧ neg v ∈ C t ∧
      Walk (Mark C P r a) r t ∧ Walk (Mark C P r a) t i := by
    by_cases has : neg (first k) ∈ C i ∨ neg (second k) ∈ C i
    · rcases has with h | h
      · exact ⟨first k, i, Or.inl rfl, h, wi, .refl⟩
      · exact ⟨second k, i, Or.inr rfl, h, wi, .refl⟩
    push Not at has
    have possible : ∀ u, P i = [u] → u = j := by
      intro u pu
      exact (by simpa [Edge, pu] using eij : j = u).symm
    have ic := rules i ir
    rcases ic with ⟨p0, _⟩ | ⟨u, _, pu, wu⟩ | ⟨u, _, z, _, e, _⟩
    · simp [Edge, p0] at eij
    · have ji := possible u pu
      subst u
      have fv : neg (first k) ∈ C j := by simp [cj, collision]
      have sv : neg (second k) ∈ C j := by simp [cj, collision]
      have nonsmall : ¬ SmallForms (C i) := by
        rintro ⟨q, sq⟩
        have hh := weak_lost_neg_injective sq wu fi fv sv has.1 has.2
        exact (ne_of_lt k.property) (congrArg Prod.fst hh)
      obtain ⟨t, wt, ws, ht⟩ := recover a i j (first k) pu nonsmall fv has.1 _ (fun e => e) wi
      exact ⟨first k, t, Or.inl rfl, ht, wt, ws⟩
    · exact False.elim ((collision_residue (rules i ir) eij cj (by simp [e])).elim has.1 has.2)
  obtain ⟨v, t, hv, tv, wt, ti⟩ := pay
  have nr := rootRawAbsent (v := v) fr
  obtain ⟨l, u, pre, edge, suffix, nv, pv⟩ := first_loss (C := C) wt nr tv
  have marked : Walk (Mark C P r a) r l := walk_sub (fun e => e.1) pre
  have fl := false_on_mark marked (fr a)
  have ll := (live_iff rules).2 (walk_sub (fun e => e.1) marked)
  have hinternal := has_child_from_path (suffix.trans ti) eij
  have loss : Loss (C := C) (P := P) l u v := ⟨edge.1.2, hinternal, nv, pv⟩
  have shape : (P l).length = 2 ∨ SmallForms (C l) := by
    rcases loss_rule (rules l edge.1.1) loss with ⟨pu, _⟩ | ⟨x, pe, _, _⟩
    · right
      by_contra h
      obtain ⟨z, wz, _, nz⟩ := recover a l u v pu h pv nv _ (fun e => e.1) pre
      rcases wz.cases_tail with e | ⟨z0, _, e⟩
      · exact nr (e ▸ nz)
      · exact e.2 nz
    · left
      simp [pe]
  exact ⟨v, l, u, hv, ll, loss, ⟨a, fl⟩, shape⟩

theorem low_bound_of_recover {F : Set (LinClause Grid)} {C : ClauseMap Grid}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (fr : ∀ a, FalseAt C a r) (rootInternal : P r ≠ [])
    (axes : 45 ≤ (WithArity P r 0).card) (recover : Recover C P r)
    (crits : ∀ k : Collision, ∃ a, ∀ D ∈ F, ¬ LinClauseSat a D → D = collision k) :
    101 ≤ (Live P r).card := by
  apply collision_charges rules axes (GoodLoss (C := C) (P := P)) (fun _ _ _ h => h.1)
  · intro i j k v w il h g
    have ir := walk_le (bounded_edge rules) ((live_iff rules).1 il)
    exact good_unique (rules i ir) h g
  · exact fun k => charge_path rules fr rootInternal recover k (crits k)

end PEqualNP.Outside.L_pcx_472_aux.Charge

namespace PEqualNP.Outside.L_pcx_472_aux.Low

open PEqualNP.Outside.L_pcx_472_aux.Graph PEqualNP.Outside.L_pcx_472_aux.Charge PEqualNP.Outside.L_pcx_472_aux.Linear PEqualNP.Outside.L_pcx_472_aux.Cert PEqualNP.ProofComplexity

theorem linearOf_collMask_eq (k : Collision) :
    linearOf (collMask k.val.1 k.val.2.1 k.val.2.2, true) = collision k := by
  simp only [linearOf, clauseOf_collMask, collClause, linOfClause, collision, first, second,
    PEqualNP.Outside.L_pcx_472_aux.Orientation.neg]
  ext x
  simp

theorem collision_crit (k : Collision) :
    ∃ a, ∀ D ∈ (linOfClause '' PHP 5 4), ¬ LinClauseSat a D → D = collision k := by
  obtain ⟨label, _, hbeq⟩ := List.any_eq_true.mp (coll_in_ax k.val.1 k.val.2.1 k.val.2.2 (ne_of_lt k.2))
  have same : ax label = collision k := by
    simp only [ax, beq_iff_eq.mp hbeq, linearOf_collMask_eq]
  obtain ⟨a, ha⟩ := point_exists label
  refine ⟨a, ?_⟩
  intro D hd nh
  rw [formula_range] at hd
  obtain ⟨j, rfl⟩ := hd
  have e := (point_only ha j).1 nh
  exact e ▸ same

theorem low_impossible {C : ClauseMap Grid} {P : Parents} {r : Nat}
    (rules : ∀ i ≤ r, Rule (linOfClause '' PHP 5 4) C P i)
    (fr : ∀ a, FalseAt C a r) (rootInternal : P r ≠ [])
    (size : (Live P r).card ≤ 92) (recover : Recover C P r) : False := by
  have crit : ∀ k : Fin 45, ∃ a : Grid → Bool, ∀ j,
      (¬ LinClauseSat a (ax j)) ↔ j = k := by
    intro k
    obtain ⟨a, ha⟩ := point_exists k
    exact ⟨a, point_only ha⟩
  obtain ⟨_, _, _, lower, _⟩ := unique_leaves rules fr ax formula_range crit
  rw [Fintype.card_fin] at lower
  have lb := low_bound_of_recover rules fr rootInternal lower recover collision_crit
  omega

end PEqualNP.Outside.L_pcx_472_aux.Low

namespace PEqualNP.Outside.L_pcx_472_aux.Strip

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_472_aux.Graph

variable {V : Type} [DecidableEq V]

def strip (D : LinClause V) : LinClause V := D.filter (fun q => q.1 ≠ ∅)

omit [DecidableEq V] in
theorem no_false_empty {D : LinClause V} (live : ∃ a, ¬ LinClauseSat a D) :
    (∅, false) ∉ D := by
  intro hm
  obtain ⟨a, ha⟩ := live
  exact ha ⟨_, hm, by simp [LinEqSat]⟩

theorem strip_sat {D : LinClause V} (live : ∃ a, ¬ LinClauseSat a D) (a : V → Bool) :
    LinClauseSat a (strip D) ↔ LinClauseSat a D := by
  constructor
  · rintro ⟨q, hq, hs⟩
    exact ⟨q, (Finset.mem_filter.1 hq).1, hs⟩
  · rintro ⟨⟨f, b⟩, hq, hs⟩
    have hn : f ≠ ∅ := by
      rintro rfl
      cases b
      · exact no_false_empty live hq
      · simp [LinEqSat] at hs
    exact ⟨_, Finset.mem_filter.2 ⟨hq, hn⟩, hs⟩

theorem nonempty_equation_sat (q : LinEq V) (hn : q.1 ≠ ∅) :
    ∃ a : V → Bool, LinEqSat a q := by
  rcases q with ⟨f, b⟩
  cases b
  · exact ⟨fun _ => false, by simp [LinEqSat]⟩
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hn
    let a := fun j : V => decide (j = v)
    have fe : f.filter (fun j => a j = true) = {v} := by
      ext j
      simp only [a, Finset.mem_filter, decide_eq_true_eq, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h.symm ▸ hv, h⟩⟩
    exact ⟨a, by simp [LinEqSat, fe]⟩

theorem strip_false {D : LinClause V} (h : ∀ a, ¬ LinClauseSat a D) : strip D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.2
  intro q hq
  obtain ⟨hm, hn⟩ := Finset.mem_filter.1 hq
  obtain ⟨a, ha⟩ := nonempty_equation_sat q hn
  exact h a ⟨q, hm, ha⟩

theorem strip_ax {D : LinClause V} (axes : ∀ q ∈ D, q.1.card = 1) : strip D = D := by
  refine Finset.filter_true_of_mem ?_
  intro q hq he
  have eq := axes q hq
  simp [he] at eq

theorem strip_rules {F : Set (LinClause V)} {C : ClauseMap V}
    {P : Parents} {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (useful : ∀ i ≤ r, ∃ a, FalseAt C a i)
    (pure : ∀ D ∈ F, ∀ q ∈ D, q.1.card = 1) :
    ∀ i ≤ r, Rule F (fun i => strip (C i)) P i := by
  intro i hi
  rcases rules i hi with ⟨p0, f⟩ | ⟨j, ji, p1, hw⟩ | ⟨j, ji, k, ki, p2, g, hj, hk, hr⟩
  · exact Or.inl ⟨p0, by simpa only [strip_ax (pure _ f)] using f⟩
  · refine Or.inr (Or.inl ⟨j, ji, p1, fun a ha => ?_⟩)
    have hs := strip_sat (useful j (ji.le.trans hi)) a
    exact (strip_sat (useful i hi) a).2 (hw a (hs.1 ha))
  · have nz : g ≠ ∅ := by
      rintro rfl
      exact no_false_empty (useful j (ji.le.trans hi)) hj
    refine Or.inr (Or.inr ⟨j, ji, k, ki, p2, g, Finset.mem_filter.2 ⟨hj, nz⟩,
      Finset.mem_filter.2 ⟨hk, nz⟩, ?_⟩)
    simp [strip, hr, Finset.filter_erase, Finset.filter_union]

theorem php_pure {D : LinClause (Fin 5 × Fin 4)}
    (h : D ∈ (linOfClause '' PHP 5 4)) : ∀ q ∈ D, q.1.card = 1 := by
  obtain ⟨C, _, rfl⟩ := h
  intro q hq
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.1 hq
  simp

end PEqualNP.Outside.L_pcx_472_aux.Strip

namespace PEqualNP.Outside.L_pcx_472_aux.Recovery

open PEqualNP.Outside.L_pcx_472_aux.Graph PEqualNP.Outside.L_pcx_472_aux.Bridge PEqualNP.Outside.L_pcx_472_aux.Charge PEqualNP.ProofComplexity
open PEqualNP.Outside.L_pcx_472_aux.Orientation

variable {V : Type} [DecidableEq V]

theorem weaken_edge {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents}
    {i j : Nat} (rule : Rule F C P i)
    (hw : (P i).length = 1) (he : Edge P i j) :
    ∀ a, LinClauseSat a (C j) → LinClauseSat a (C i) := by
  rcases rule with ⟨p0, _⟩ | ⟨k, _, p1, wk⟩ | ⟨k, _, l, _, p2, _⟩
  · simp [p0] at hw
  · have eq : j = k := by simpa [Edge, p1] using he
    exact eq.symm ▸ wk
  · simp [p2] at hw

theorem recover_of_few {F : Set (LinClause V)} {C : ClauseMap V} {P : Parents}
    {r : Nat} (rules : ∀ i ≤ r, Rule F C P i)
    (pure : ∀ D ∈ F, ∀ q ∈ D, q.1.card = 1)
    (root : C r = ∅) (live : ∀ i ≤ r, ∃ a, FalseAt C a i)
    (few : (WithArity P r 1).card ≤ 2) : Recover C P r := by
  have rt : r ∈ Live P r := (live_iff rules).2 .refl
  obtain ⟨u, v, _, hv, order, real, cover⟩ :=
    two_cover_sources rt (Finset.filter_subset _ _) few
  have weak_cover : ∀ i, PEqualNP.Outside.L_pcx_472_aux.ParShape.Reach (PEqualNP.Outside.L_pcx_472_aux.ParShape.clip P r) r i →
      (P i).length = 1 → i = u ∨ i = v := by
    intro i w h
    have wr := walk_sub (fun e => PEqualNP.Outside.L_pcx_472_aux.ParShape.edge_clip.mp e) w
    exact cover i (Finset.mem_filter.2 ⟨(live_iff rules).2 wr, h⟩)
  have R : ParityRules C (PEqualNP.Outside.L_pcx_472_aux.ParShape.clip P r) r u v :=
    PEqualNP.Outside.L_pcx_472_aux.ParShape.mk_rules rules pure root live weak_cover
  intro a i j x pj wide hn hg Q sub path
  have sub_clip : ∀ {h k}, Q h k → PEqualNP.Outside.L_pcx_472_aux.ParShape.Edge (PEqualNP.Outside.L_pcx_472_aux.ParShape.clip P r) h k :=
    fun e => PEqualNP.Outside.L_pcx_472_aux.ParShape.edge_clip.mpr (sub e).1
  have rpath : PEqualNP.Outside.L_pcx_472_aux.ParShape.Reach (PEqualNP.Outside.L_pcx_472_aux.ParShape.clip P r) r i := walk_sub sub_clip path
  have lm : i ∈ Live P r := (live_iff rules).2 (walk_sub (fun h => (sub h).1) path)
  have one : (P i).length = 1 := by simp [pj]
  have im : i ∈ WithArity P r 1 := Finset.mem_filter.2 ⟨lm, one⟩
  have loc := cover i im
  have iu := wide_source_is_older R order rpath loc wide
  have vweak := (Finset.mem_filter.1 (real ⟨i, im⟩).2).2
  have wi : i ≤ r := walk_le (bounded_edge rules) ((live_iff rules).1 lm)
  have wv : v ≤ r := walk_le (bounded_edge rules) ((live_iff rules).1 hv)
  have old := weaken_edge (rules i wi) one (j := j) (by simp [Edge, pj])
  have newer : ∀ k, PEqualNP.Outside.L_pcx_472_aux.ParShape.Edge (PEqualNP.Outside.L_pcx_472_aux.ParShape.clip P r) v k →
      ∀ a, LinClauseSat a (C k) → LinClauseSat a (C v) := by
    intro k ek
    exact weaken_edge (rules v wv) vweak (PEqualNP.Outside.L_pcx_472_aux.ParShape.edge_clip.mp ek).2
  subst i
  have rf : FalseAt C a r := by simp [FalseAt, root, LinClauseSat]
  obtain ⟨pr, post, ax⟩ := recover_large_weak R order wide old newer sub_clip
    rf (fun e => (sub e).2) path hn hg
  exact ⟨v, pr, post, ax⟩

end PEqualNP.Outside.L_pcx_472_aux.Recovery

namespace PEqualNP.Outside.L_pcx_472_aux.Main

open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_472_aux.Graph PEqualNP.Outside.L_pcx_472_aux.Strip PEqualNP.Outside.L_pcx_472_aux.Charge
open PEqualNP.Outside.L_pcx_472_aux.Orientation (axis_sat)

theorem php_ax_sat (D : LinClause Grid) (h : D ∈ (linOfClause '' PHP 5 4)) :
    ∃ a : Grid → Bool, LinClauseSat a D := by
  obtain ⟨C, hC, rfl⟩ := h
  rcases hC with ⟨i, rfl⟩ | ⟨i, j, h, hne, rfl⟩
  · refine ⟨fun _ => true, ({(i, (0 : Fin 4))}, true), ?_, (axis_sat _ _ _).2 rfl⟩
    exact Finset.mem_image.2 ⟨((i, (0 : Fin 4)), true), by simp, rfl⟩
  · refine ⟨fun _ => false, ({(i, h)}, false), ?_, (axis_sat _ _ _).2 rfl⟩
    exact Finset.mem_image.2 ⟨((i, h), false), by simp, rfl⟩

theorem verify
    (π : List (LinClause Grid)) (refute : IsLinRefutation (PHP 5 4) π)
    (small : π.length ≤ 92) : False := by
  classical
  let π' := π.filter useful
  have hempty : ∅ ∈ π' := List.mem_filter.2
    ⟨refute.2, (useful_spec _).2 ⟨fun _ => false, by simp [LinClauseSat]⟩⟩
  obtain ⟨C, P, graph⟩ := build_graph (prune_taut refute.1)
  obtain ⟨r, lr, fr, _, c, _, d, _, ne, introP, f, nf, br⟩ :=
    first_false graph hempty php_ax_sat
  have size : (Live P r).card ≤ 92 := by
    have hs : π'.length ≤ π.length := List.length_filter_le _ _
    exact (live_card_le P r).trans ((Nat.succ_le_of_lt lr).trans (hs.trans small))
  have rules : ∀ i ≤ r, Rule (linOfClause '' PHP 5 4) C P i :=
    fun i h => graph.1 i (h.trans_lt lr)
  by_cases high : 3 ≤ (WithArity P r 1).card
  · have ec : LocalEdge P r r c := ⟨le_rfl, by simp [Edge, introP]⟩
    have ed : LocalEdge P r r d := ⟨le_rfl, by simp [Edge, introP]⟩
    exact PEqualNP.Outside.L_pcx_472_aux.High.high_impossible rules fr ec ed ne
      size high f nf br
  · let C' := fun i => strip (C i)
    have pu : ∀ D ∈ (linOfClause '' PHP 5 4), ∀ q ∈ D, q.1.card = 1 :=
      fun _ h => php_pure h
    have live : ∀ i ≤ r, ∃ a, FalseAt C a i :=
      fun i h => encoded_useful graph (h.trans_lt lr)
    have root : C' r = ∅ := strip_false fr
    have ss : ∀ i ≤ r, Rule (linOfClause '' PHP 5 4) C' P i :=
      strip_rules rules live pu
    have sf : ∀ a, FalseAt C' a r := by simp [FalseAt, root, LinClauseSat]
    have sl : ∀ i ≤ r, ∃ a, FalseAt C' a i := by
      intro i hi
      obtain ⟨a, ha⟩ := live i hi
      exact ⟨a, fun h => ha ((strip_sat (live i hi) a).1 h)⟩
    have recover := PEqualNP.Outside.L_pcx_472_aux.Recovery.recover_of_few ss pu root sl (by omega)
    exact PEqualNP.Outside.L_pcx_472_aux.Low.low_impossible ss sf (by simp [introP]) size recover

end PEqualNP.Outside.L_pcx_472_aux.Main

theorem PEqualNP.Outside.L_pcx_472 : (¬ (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 92)) := by
  rintro ⟨π, refute, small⟩
  exact PEqualNP.Outside.L_pcx_472_aux.Main.verify π refute small
