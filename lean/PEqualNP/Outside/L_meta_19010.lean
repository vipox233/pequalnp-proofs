import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19010_aux

def x1List : List ℕ :=
  [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
   103293914128, 26322415680, 344922804352, 414195942664, 581968119809,
   1065151898146]

def x1Set : Finset ℕ := x1List.toFinset
def x2Val : ℕ := 1099511562240
def x3Val : ℕ := 1099511627775
def b40 : ℕ := 1099511627776
def b41 : ℕ := 2199023255552
def b401 : ℕ := 3298534883328
def lim42 : ℕ := 4398046511104

def vVal (v : Fin 11) : ℕ := x1List.getD v.val 0

def edgesArr : Array (Fin 11 × Fin 11) :=
  #[(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
    (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

def edgeEnds (e : Fin 16) : Fin 11 × Fin 11 :=
  edgesArr[e.val]!

def adj (u v : Fin 11) : Bool :=
  (List.finRange 16).any fun e =>
    let p := edgeEnds e
    (p.1 == u && p.2 == v) || (p.1 == v && p.2 == u)

def findEdge (u v : Fin 11) : Fin 16 :=
  match (List.finRange 16).find? (fun e =>
      let p := edgeEnds e
      (p.1 == u && p.2 == v) || (p.1 == v && p.2 == u)) with
  | some e => e
  | none => 0

private lemma h_bit_edge : ∀ (v : Fin 11) (e : Fin 16),
    (vVal v).testBit e.val = decide (v = (edgeEnds e).1 ∨ v = (edgeEnds e).2) := by
  decide +kernel

private lemma h_nonedge_bad : ∀ (u v : Fin 11), adj u v = false →
    ∃ m : Fin 40, 16 ≤ m.val ∧ (vVal u).testBit m.val = true ∧ (vVal v).testBit m.val = true := by
  decide +kernel

private lemma h_c4_free : ∀ (u₁ u₂ v₁ v₂ : Fin 11),
    u₁ ≠ u₂ → v₁ ≠ v₂ → adj u₁ v₁ = true → adj u₁ v₂ = true →
    adj u₂ v₁ = true → adj u₂ v₂ = false := by
  decide +kernel

private lemma h_adj_irrefl : ∀ (v : Fin 11), adj v v = false := by
  decide +kernel

private lemma h_adj_symm : ∀ (u v : Fin 11), adj u v = adj v u := by
  decide +kernel

private lemma h_findEdge_spec : ∀ (u v : Fin 11), adj u v = true →
    ((edgeEnds (findEdge u v)).1 = u ∧ (edgeEnds (findEdge u v)).2 = v) ∨
    ((edgeEnds (findEdge u v)).1 = v ∧ (edgeEnds (findEdge u v)).2 = u) := by
  decide +kernel

private lemma h_findEdge_comm : ∀ (u v : Fin 11), findEdge u v = findEdge v u := by
  decide +kernel

private lemma h_findEdge_of_ends : ∀ (e : Fin 16),
    findEdge (edgeEnds e).1 (edgeEnds e).2 = e := by
  decide +kernel

private lemma h_edgeEnds_adj : ∀ (e : Fin 16),
    adj (edgeEnds e).1 (edgeEnds e).2 = true := by
  decide +kernel

private lemma h_vVal_le : ∀ (v : Fin 11), vVal v ≤ x3Val := by
  decide +kernel

private lemma h_vVal_inj : ∀ (u v : Fin 11), vVal u = vVal v → u = v := by
  decide +kernel

private lemma h_x1Set_iff : ∀ w, w ∈ x1Set ↔ ∃ v : Fin 11, vVal v = w := by
  intro w
  simp only [x1Set, x1List, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
  · rintro ⟨v, rfl⟩
    fin_cases v <;> simp [vVal, x1List]

private lemma h_x2_bit : ∀ m : Fin 40, x2Val.testBit m.val = decide (16 ≤ m.val) := by
  decide +kernel

private lemma h_x3_bit : ∀ m : Fin 40, x3Val.testBit m.val = true := by
  decide +kernel

private lemma h_b40_bit : ∀ m < 42, b40.testBit m = decide (m = 40) := by
  intro m hm
  interval_cases m <;> decide

private lemma h_b41_bit : ∀ m < 42, b41.testBit m = decide (m = 41) := by
  intro m hm
  interval_cases m <;> decide

private lemma h_le_x3_iff (w : ℕ) (hw : w < lim42) :
    w ≤ x3Val ↔ w.testBit 40 = false ∧ w.testBit 41 = false := by
  have hx3 : x3Val = 2 ^ 40 - 1 := by decide
  have hlim : lim42 = 2 ^ 42 := by decide
  rw [hx3]
  constructor
  · intro hle
    have hlt : w < 2 ^ 40 := by omega
    exact ⟨Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)⟩
  · rintro ⟨h40, h41⟩
    by_contra hgt
    have hge : 2 ^ 40 ≤ w := by omega
    have hq : w / 2 ^ 40 < 4 := by
      have : w < 2 ^ 42 := by rw [← hlim]; exact hw
      omega
    have hqpos : 1 ≤ w / 2 ^ 40 := by omega
    have hb40 : w.testBit 40 = ((w / 2 ^ 40) % 2 == 1) := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]; simp [Nat.and_one_is_mod]
    have hb41 : w.testBit 41 = ((w / 2 ^ 41) % 2 == 1) := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]; simp [Nat.and_one_is_mod]
    have hdiv41 : w / 2 ^ 41 = (w / 2 ^ 40) / 2 := by
      rw [Nat.div_div_eq_div_mul]; rfl
    rw [hdiv41] at hb41
    have hcases : w / 2 ^ 40 = 1 ∨ w / 2 ^ 40 = 2 ∨ w / 2 ^ 40 = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · rw [h1] at hb40; simp [h40] at hb40
    · rw [h2] at hb41; simp [h41] at hb41
    · rw [h3] at hb40; simp [h40] at hb40

/-! ### Generic Graph Component Lower Bound -/

def stepRel {α : Type*} (es : List (α × α)) (u v : α) : Prop :=
  (u, v) ∈ es ∨ (v, u) ∈ es

def conn {α : Type*} (es : List (α × α)) (u v : α) : Prop :=
  Relation.ReflTransGen (stepRel es) u v

lemma conn_refl {α : Type*} (es : List (α × α)) (u : α) : conn es u u :=
  Relation.ReflTransGen.refl

lemma conn_trans {α : Type*} {es : List (α × α)} {u v w : α}
    (h1 : conn es u v) (h2 : conn es v w) : conn es u w :=
  Relation.ReflTransGen.trans h1 h2

lemma conn_symm {α : Type*} {es : List (α × α)} {u v : α} (h : conn es u v) : conn es v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    have hrev : stepRel es _ _ := hstep.symm
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hrev) ih

lemma conn_edge {α : Type*} {es : List (α × α)} {u v : α} (h : (u, v) ∈ es) : conn es u v :=
  Relation.ReflTransGen.single (Or.inl h)

lemma conn_mono {α : Type*} {es₁ es₂ : List (α × α)} (hsub : ∀ p ∈ es₁, p ∈ es₂)
    {u v : α} (h : conn es₁ u v) : conn es₂ u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    apply Relation.ReflTransGen.tail ih
    rcases hstep with h1 | h1
    · exact Or.inl (hsub _ h1)
    · exact Or.inr (hsub _ h1)

lemma conn_cons_split {α : Type*} {a b : α} {rest : List (α × α)} {u v : α}
    (h : conn ((a, b) :: rest) u v) :
    conn rest u v ∨ (conn rest u a ∧ conn rest b v) ∨ (conn rest u b ∧ conn rest a v) := by
  induction h with
  | refl => exact Or.inl Relation.ReflTransGen.refl
  | @tail y z _ hstep ih =>
    have hstep' : (y = a ∧ z = b) ∨ (y = b ∧ z = a) ∨ stepRel rest y z := by
      rcases hstep with hm | hm
      · simp only [List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hrest
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (Or.inr (Or.inl hrest))
      · simp only [List.mem_cons, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩ | hrest
        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr hrest))
    rcases hstep' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hrest
    · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.refl⟩)
      · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.refl⟩)
      · exact Or.inl h1
    · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.refl⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.refl⟩)
    · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (Relation.ReflTransGen.tail h1 hrest)
      · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.tail h2 hrest⟩)
      · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.tail h2 hrest⟩)

lemma cover_by_conn {α : Type*} [Fintype α] [DecidableEq α] :
    ∀ (es : List (α × α)) (R : Finset α),
      (∀ x : α, ∃ r ∈ R, conn es x r) →
      Fintype.card α ≤ R.card + es.length := by
  intro es
  induction es with
  | nil =>
    intro R hR
    have huniv : Finset.univ ⊆ R := by
      intro x _
      obtain ⟨r, hr, hconn⟩ := hR x
      have hxeq : x = r := by
        cases hconn with
        | refl => rfl
        | tail _ hs => rcases hs with h | h <;> simp at h
      exact hxeq ▸ hr
    have hcard := Finset.card_le_card huniv
    simpa using hcard
  | cons ab rest ih =>
    rcases ab with ⟨a, b⟩
    intro R hR
    by_cases ha : ∃ r ∈ R, conn rest a r
    · obtain ⟨ra, hra, hca⟩ := ha
      have hR' : ∀ x : α, ∃ r ∈ insert b R, conn rest x r := by
        intro x
        obtain ⟨r, hr, hcx⟩ := hR x
        rcases conn_cons_split hcx with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact ⟨r, Finset.mem_insert_of_mem hr, h1⟩
        · exact ⟨ra, Finset.mem_insert_of_mem hra, conn_trans h1 hca⟩
        · exact ⟨b, Finset.mem_insert_self _ _, h1⟩
      have h1 := ih (insert b R) hR'
      have h2 := Finset.card_insert_le b R
      simp only [List.length_cons]
      omega
    · have hb : ∃ r ∈ R, conn rest b r := by
        obtain ⟨r, hr, hcb⟩ := hR b
        rcases conn_cons_split hcb with h1 | ⟨_, h2⟩ | ⟨_, h2⟩
        · exact ⟨r, hr, h1⟩
        · exact ⟨r, hr, h2⟩
        · exact absurd ⟨r, hr, h2⟩ ha
      obtain ⟨rb, hrb, hcb⟩ := hb
      have hR' : ∀ x : α, ∃ r ∈ insert a R, conn rest x r := by
        intro x
        obtain ⟨r, hr, hcx⟩ := hR x
        rcases conn_cons_split hcx with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact ⟨r, Finset.mem_insert_of_mem hr, h1⟩
        · exact ⟨a, Finset.mem_insert_self _ _, h1⟩
        · exact ⟨rb, Finset.mem_insert_of_mem hrb, conn_trans h1 hcb⟩
      have h1 := ih (insert a R) hR'
      have h2 := Finset.card_insert_le a R
      simp only [List.length_cons]
      omega

lemma list_filter_partition_len {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    (l.filter (fun x => decide (p x))).length + (l.filter (fun x => decide (¬ p x))).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split_ifs with h1 h2 h2
    · exfalso; exact (of_decide_eq_true h2) (of_decide_eq_true h1)
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega
    · exfalso; exact h2 (decide_eq_true (fun hp => h1 (decide_eq_true hp)))

def optFindList (o : Option ℕ) (f : ℕ → Fin 16 → Bool) : List (Fin 16) :=
  match o with
  | none => []
  | some p => match (List.finRange 16).find? (f p) with
              | none => []
              | some e => [e]

lemma optFindList_len (o : Option ℕ) (f : ℕ → Fin 16 → Bool) :
    (optFindList o f).length ≤ (if o.isSome then 1 else 0) := by
  cases o with
  | none => simp [optFindList]
  | some p =>
    simp only [optFindList, Option.isSome_some, ↓reduceIte]
    cases (List.finRange 16).find? (f p) <;> simp

lemma mem_optFindList {o : Option ℕ} {f : ℕ → Fin 16 → Bool} {p : ℕ} {r : Fin 16}
    (ho : o = some p) (hr : (List.finRange 16).find? (f p) = some r) :
    r ∈ optFindList o f := by
  subst ho
  simp [optFindList, hr]

/-! ### Bitwise helpers -/

lemma or_le_right_lt {a b : ℕ} (hne : a ||| b ≠ b) : b < a ||| b := by
  have hle : b ≤ a ||| b := Nat.right_le_or
  omega

lemma or_le_left_lt {a b : ℕ} (hne : a ||| b ≠ a) : a < a ||| b := by
  have hle : a ≤ a ||| b := Nat.left_le_or
  omega

lemma bitwise_sub_trans {a b c : ℕ} (h1 : a ||| b = b) (h2 : b ||| c = c) : a ||| c = c := by
  calc a ||| c = a ||| (b ||| c) := by rw [h2]
    _ = (a ||| b) ||| c := by rw [Nat.or_assoc]
    _ = b ||| c := by rw [h1]
    _ = c := h2

lemma testBit_of_or_eq {a b : ℕ} (h : a ||| b = b) (i : ℕ) (ha : a.testBit i = true) :
    b.testBit i = true := by
  rw [← h, Nat.testBit_or, ha, Bool.true_or]

lemma and_x2_eq_zero_of_or {a b c : ℕ}
    (ha : a &&& c &&& x2Val = 0) (hb : b &&& c &&& x2Val = 0) :
    (a ||| b) &&& c &&& x2Val = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 := congrArg (fun n => n.testBit i) ha
  have h2 := congrArg (fun n => n.testBit i) hb
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 h2 ⊢
  cases ha' : a.testBit i <;> cases hb' : b.testBit i <;>
    cases hc' : c.testBit i <;> cases hx2 : x2Val.testBit i <;> simp_all

lemma and_x2_eq_zero_of_le {a b c : ℕ} (hle : a ||| b = b) (hb : b &&& c &&& x2Val = 0) :
    a &&& c &&& x2Val = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 := congrArg (fun n => n.testBit i) hb
  simp only [Nat.testBit_and, Nat.zero_testBit] at h1 ⊢
  cases ha : a.testBit i
  · simp
  · have hb' := testBit_of_or_eq hle i ha
    rw [hb'] at h1
    simpa using h1

/-! ### Pure OR-DAG representation -/

structure PureDag where
  P : Finset ℕ
  hx1 : x1Set ⊆ P
  hbound : ∀ w ∈ P, w ≤ x3Val
  hbuild : ∀ w ∈ P \ x1Set, ∃ a ∈ P, ∃ b ∈ P, a < w ∧ b < w ∧ w = a ||| b

def addPureOr (D : PureDag) (u v : ℕ) (hu : u ∈ D.P) (hv : v ∈ D.P) : PureDag where
  P := insert (u ||| v) D.P
  hx1 := D.hx1.trans (Finset.subset_insert _ _)
  hbound := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · have h1 := D.hbound u hu
      have h2 := D.hbound v hv
      have hx3 : x3Val = 2 ^ 40 - 1 := by decide
      rw [hx3] at h1 h2 ⊢
      have hlt : (u ||| v) < 2 ^ 40 := Nat.or_lt_two_pow (by omega) (by omega)
      omega
    · exact D.hbound w hw'
  hbuild := by
    intro w hw
    obtain ⟨hwP, hwx1⟩ := Finset.mem_sdiff.mp hw
    by_cases hmem : w ∈ D.P
    · obtain ⟨a, ha, b, hb, haw, hbw, heq⟩ := D.hbuild w (Finset.mem_sdiff.mpr ⟨hmem, hwx1⟩)
      exact ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, haw, hbw, heq⟩
    · have hwuv : w = u ||| v := (Finset.mem_insert.mp hwP).resolve_right hmem
      subst hwuv
      have hnu : u ||| v ≠ u := fun h => hmem (h.symm ▸ hu)
      have hnv : u ||| v ≠ v := fun h => hmem (h.symm ▸ hv)
      exact ⟨u, Finset.mem_insert_of_mem hu, v, Finset.mem_insert_of_mem hv,
        or_le_left_lt hnu, or_le_right_lt hnv, rfl⟩

lemma addPureOr_card_sdiff_le (D : PureDag) (u v : ℕ) (hu : u ∈ D.P) (hv : v ∈ D.P) :
    ((addPureOr D u v hu hv).P \ x1Set).card ≤ (D.P \ x1Set).card + 1 := by
  have hsub : (addPureOr D u v hu hv).P \ x1Set ⊆ insert (u ||| v) (D.P \ x1Set) := by
    intro w hw
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_insert.mp h1 with rfl | h1'
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨h1', h2⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

lemma addPureList (D : PureDag) : ∀ (ps : List ℕ), ps ≠ [] → (∀ p ∈ ps, p ∈ D.P) →
    ∃ (D' : PureDag) (u : ℕ),
      D.P ⊆ D'.P ∧
      u ∈ D'.P ∧
      (D'.P \ x1Set).card + 1 ≤ (D.P \ x1Set).card + ps.length ∧
      (∀ i, u.testBit i = true ↔ ∃ p ∈ ps, p.testBit i = true) := by
  intro ps
  induction ps generalizing D with
  | nil => intro h; exact (h rfl).elim
  | cons p rest ih =>
    intro _ hmem
    cases rest with
    | nil =>
      refine ⟨D, p, Finset.Subset.rfl, hmem p (by simp), by simp, ?_⟩
      intro i; simp
    | cons q tail =>
      have hne : (q :: tail) ≠ [] := List.cons_ne_nil _ _
      obtain ⟨D1, u1, hsub1, hu1, hcard1, hbit1⟩ :=
        ih D hne (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
      have hp1 : p ∈ D1.P := hsub1 (hmem p (by simp))
      let D2 := addPureOr D1 p u1 hp1 hu1
      refine ⟨D2, p ||| u1, hsub1.trans (Finset.subset_insert _ _),
        Finset.mem_insert_self _ _, ?_, ?_⟩
      · have hstep := addPureOr_card_sdiff_le D1 p u1 hp1 hu1
        simp only [D2, List.length_cons] at hcard1 ⊢
        omega
      · intro i
        simp only [Nat.testBit_or, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp, hbit1]

/-! ### Step 1: Eliminate all dirty OR gates -/

/-- A clean pair `(u, p)` where `u ∈ P ∪ Dd`, `p ∈ P`, and `u &&& p &&& x2Val = 0`. -/
def isCleanPair (P Dd : Finset ℕ) (pair : ℕ × ℕ) : Prop :=
  (pair.1 ∈ P ∨ pair.1 ∈ Dd) ∧ pair.2 ∈ P ∧ pair.1 &&& pair.2 &&& x2Val = 0

def coversAllEdges (M : List (ℕ × ℕ)) : Prop :=
  ∀ e : Fin 16, ∃ pair ∈ M, (pair.1 &&& pair.2).testBit e.val = true

lemma elim_dirty_or :
    ∀ (kd : ℕ) (d0 e0 : ℕ) (D : PureDag) (Dd : Finset ℕ) (M : List (ℕ × ℕ)),
      (Dd \ {d0, e0}).card = kd →
      (∀ w ∈ Dd \ {d0, e0}, ∃ a ∈ D.P ∪ Dd, ∃ b ∈ D.P ∪ Dd, a < w ∧ b < w ∧ w = a ||| b) →
      (∀ pair ∈ M, isCleanPair D.P Dd pair) →
      coversAllEdges M →
      ∃ (D' : PureDag) (M' : List (ℕ × ℕ)),
        D.P ⊆ D'.P ∧
        (∀ pair ∈ M', isCleanPair D'.P {d0, e0} pair) ∧
        coversAllEdges M' ∧
        M'.length + (D'.P \ x1Set).card ≤ M.length + (D.P \ x1Set).card + kd := by
  intro kd
  induction kd with
  | zero =>
    intro d0 e0 D Dd M hkd _ hM hcov
    have hsub : Dd ⊆ {d0, e0} := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hkd)
    refine ⟨D, M, Finset.Subset.rfl, ?_, hcov, by omega⟩
    intro pair hp
    obtain ⟨h1, h2, h3⟩ := hM pair hp
    exact ⟨h1.imp id (fun h => hsub h), h2, h3⟩
  | succ kd ih =>
    intro d0 e0 D Dd M hkd hbuild hM hcov
    have hne : (Dd \ {d0, e0}).Nonempty := Finset.card_pos.mp (by omega)
    let wmax := (Dd \ {d0, e0}).max' hne
    have hwmax_mem : wmax ∈ Dd \ {d0, e0} := Finset.max'_mem _ hne
    have hwmax_Dd : wmax ∈ Dd := (Finset.mem_sdiff.mp hwmax_mem).1
    have hwmax_not_base : wmax ∉ ({d0, e0} : Finset ℕ) := (Finset.mem_sdiff.mp hwmax_mem).2
    let Dd' := Dd.erase wmax
    have hkd' : (Dd' \ {d0, e0}).card = kd := by
      have heq : Dd' \ {d0, e0} = (Dd \ {d0, e0}).erase wmax := by
        ext x; simp [Dd', Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [heq, Finset.card_erase_of_mem hwmax_mem, hkd]; omega
    have hbuild' : ∀ w ∈ Dd' \ {d0, e0},
        ∃ a ∈ D.P ∪ Dd', ∃ b ∈ D.P ∪ Dd', a < w ∧ b < w ∧ w = a ||| b := by
      intro w hw
      have hw_orig : w ∈ Dd \ {d0, e0} := by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hw
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase h1, h2⟩
      have hw_le : w ≤ wmax := Finset.le_max' _ w hw_orig
      obtain ⟨a, ha, b, hb, haw, hbw, heq⟩ := hbuild w hw_orig
      have ha' : a ∈ D.P ∪ Dd' := by
        rcases Finset.mem_union.mp ha with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by omega, h⟩)
      have hb' : b ∈ D.P ∪ Dd' := by
        rcases Finset.mem_union.mp hb with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by omega, h⟩)
      exact ⟨a, ha', b, hb', haw, hbw, heq⟩
    obtain ⟨a, ha, b, hb, haw, hbw, hwab⟩ := hbuild wmax hwmax_mem
    have ha' : a ∈ D.P ∪ Dd' := by
      rcases Finset.mem_union.mp ha with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by omega, h⟩)
    have hb' : b ∈ D.P ∪ Dd' := by
      rcases Finset.mem_union.mp hb with h | h
      · exact Finset.mem_union_left _ h
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by omega, h⟩)
    let hit := M.filter (fun pair => decide (pair.1 = wmax))
    let rest := M.filter (fun pair => decide (pair.1 ≠ wmax))
    have hlen_split : hit.length + rest.length = M.length :=
      list_filter_partition_len (fun pair : ℕ × ℕ => pair.1 = wmax) M
    by_cases hhit : hit = []
    · have hM' : ∀ pair ∈ rest, isCleanPair D.P Dd' pair := by
        intro pair hp
        have hpM : pair ∈ M := (List.mem_filter.mp hp).1
        have hpne : pair.1 ≠ wmax := by simpa using (List.mem_filter.mp hp).2
        obtain ⟨h1, h2, h3⟩ := hM pair hpM
        refine ⟨?_, h2, h3⟩
        rcases h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Finset.mem_erase.mpr ⟨hpne, h⟩)
      have hcov' : coversAllEdges rest := by
        intro e
        obtain ⟨pair, hpM, hbit⟩ := hcov e
        have hpne : pair.1 ≠ wmax := by
          intro heq
          have : pair ∈ hit := List.mem_filter.mpr ⟨hpM, by simp [heq]⟩
          rw [hhit] at this; simp at this
        exact ⟨pair, List.mem_filter.mpr ⟨hpM, by simp [hpne]⟩, hbit⟩
      obtain ⟨D', M', hsub, hclean', hcov'', hcost⟩ := ih d0 e0 D Dd' rest hkd' hbuild' hM' hcov'
      exact ⟨D', M', hsub, hclean', hcov'', by omega⟩
    · let ps := hit.map Prod.snd
      have hps_ne : ps ≠ [] := by simp [ps, hhit]
      have hps_mem : ∀ p ∈ ps, p ∈ D.P := by
        intro p hp
        obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hp
        exact (hM pair (List.mem_filter.mp hpair).1).2.1
      obtain ⟨D1, pU, hsub1, hpU, hcard1, hbitU⟩ := addPureList D ps hps_ne hps_mem
      have hwmax_pU_clean : wmax &&& pU &&& x2Val = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_and, Nat.zero_testBit]
        cases hw1 : wmax.testBit i
        · simp
        · cases hp1 : pU.testBit i
          · simp
          · cases hx2 : x2Val.testBit i
            · simp
            · exfalso
              obtain ⟨p, hpps, hpi⟩ := (hbitU i).mp hp1
              obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hpps
              have hpairM : pair ∈ M := (List.mem_filter.mp hpair).1
              have hpair1 : pair.1 = wmax := by simpa using (List.mem_filter.mp hpair).2
              have hcl := (hM pair hpairM).2.2
              have hb := congrArg (fun n => n.testBit i) hcl
              rw [hpair1] at hb
              simp [Nat.testBit_and, hw1, hpi, hx2] at hb
      have ha_clean : a &&& pU &&& x2Val = 0 := by
        apply and_x2_eq_zero_of_le _ hwmax_pU_clean
        rw [hwab, ← Nat.or_assoc, Nat.or_self]
      have hb_clean : b &&& pU &&& x2Val = 0 := by
        apply and_x2_eq_zero_of_le _ hwmax_pU_clean
        rw [hwab, Nat.or_comm a b, ← Nat.or_assoc, Nat.or_self]
      let M1 := (a, pU) :: (b, pU) :: rest
      have hM1 : ∀ pair ∈ M1, isCleanPair D1.P Dd' pair := by
        intro pair hp
        simp only [M1, List.mem_cons] at hp
        rcases hp with rfl | rfl | hp
        · exact ⟨(Finset.mem_union.mp ha').imp (fun h => hsub1 h) id, hpU, ha_clean⟩
        · exact ⟨(Finset.mem_union.mp hb').imp (fun h => hsub1 h) id, hpU, hb_clean⟩
        · have hpM : pair ∈ M := (List.mem_filter.mp hp).1
          have hpne : pair.1 ≠ wmax := by simpa using (List.mem_filter.mp hp).2
          obtain ⟨h1, h2, h3⟩ := hM pair hpM
          exact ⟨h1.imp (fun h => hsub1 h) (fun h => Finset.mem_erase.mpr ⟨hpne, h⟩), hsub1 h2, h3⟩
      have hcov1 : coversAllEdges M1 := by
        intro e
        obtain ⟨pair, hpM, hbit⟩ := hcov e
        by_cases h1 : pair.1 = wmax
        · have hpair_hit : pair ∈ hit := List.mem_filter.mpr ⟨hpM, by simp [h1]⟩
          have hp_ps : pair.2 ∈ ps := List.mem_map.mpr ⟨pair, hpair_hit, rfl⟩
          simp only [Nat.testBit_and, Bool.and_eq_true] at hbit
          rw [h1, hwab, Nat.testBit_or, Bool.or_eq_true] at hbit
          have hpU_e : pU.testBit e.val = true := (hbitU e.val).mpr ⟨pair.2, hp_ps, hbit.2⟩
          rcases hbit.1 with hae | hbe
          · refine ⟨(a, pU), by simp [M1], ?_⟩
            simp [Nat.testBit_and, hae, hpU_e]
          · refine ⟨(b, pU), by simp [M1], ?_⟩
            simp [Nat.testBit_and, hbe, hpU_e]
        · exact ⟨pair, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_filter.mpr ⟨hpM, by simp [h1]⟩)), hbit⟩
      have hbuild1 : ∀ w ∈ Dd' \ {d0, e0},
          ∃ a1 ∈ D1.P ∪ Dd', ∃ b1 ∈ D1.P ∪ Dd', a1 < w ∧ b1 < w ∧ w = a1 ||| b1 := by
        intro w hw
        obtain ⟨a1, ha1, b1, hb1, h1, h2, h3⟩ := hbuild' w hw
        exact ⟨a1, (Finset.mem_union.mp ha1).elim (fun h => Finset.mem_union_left _ (hsub1 h))
          (fun h => Finset.mem_union_right _ h),
          b1, (Finset.mem_union.mp hb1).elim (fun h => Finset.mem_union_left _ (hsub1 h))
          (fun h => Finset.mem_union_right _ h), h1, h2, h3⟩
      obtain ⟨D', M', hsub2, hclean', hcov'', hcost⟩ := ih d0 e0 D1 Dd' M1 hkd' hbuild1 hM1 hcov1
      have hps_len : ps.length = hit.length := List.length_map _
      have hM1_len : M1.length = 2 + rest.length := by simp [M1]; omega
      refine ⟨D', M', hsub1.trans hsub2, hclean', hcov'', ?_⟩
      omega

/-! ### Step 1b: Merge all d0-pairs into at most 1 and all e0-pairs into at most 1 -/

lemma merge_single_dirty (d0 : ℕ) (D : PureDag) (Other : Finset ℕ) (M : List (ℕ × ℕ))
    (hM : ∀ pair ∈ M, isCleanPair D.P (insert d0 Other) pair)
    (hcov : coversAllEdges M) :
    ∃ (D' : PureDag) (Mpure : List (ℕ × ℕ)) (pOpt : Option ℕ),
      D.P ⊆ D'.P ∧
      (∀ pair ∈ Mpure, isCleanPair D'.P Other pair) ∧
      (∀ p, pOpt = some p → p ∈ D'.P ∧ d0 &&& p &&& x2Val = 0) ∧
      (∀ e : Fin 16,
        (∃ pair ∈ Mpure, (pair.1 &&& pair.2).testBit e.val = true) ∨
        (∃ p, pOpt = some p ∧ (d0 &&& p).testBit e.val = true)) ∧
      Mpure.length + (if pOpt.isSome then 1 else 0) + (D'.P \ x1Set).card ≤
        M.length + (D.P \ x1Set).card := by
  let hit := M.filter (fun pair => decide (pair.1 = d0))
  let rest := M.filter (fun pair => decide (pair.1 ≠ d0))
  have hlen_split : hit.length + rest.length = M.length :=
    list_filter_partition_len (fun pair : ℕ × ℕ => pair.1 = d0) M
  by_cases hhit : hit = []
  · refine ⟨D, rest, none, Finset.Subset.rfl, ?_, by simp, ?_, by simp; omega⟩
    · intro pair hp
      have hpM := (List.mem_filter.mp hp).1
      have hpne : pair.1 ≠ d0 := by simpa using (List.mem_filter.mp hp).2
      obtain ⟨h1, h2, h3⟩ := hM pair hpM
      exact ⟨h1.imp id (fun h => (Finset.mem_insert.mp h).resolve_left hpne), h2, h3⟩
    · intro e
      obtain ⟨pair, hpM, hbit⟩ := hcov e
      have hpne : pair.1 ≠ d0 := by
        intro heq
        have : pair ∈ hit := List.mem_filter.mpr ⟨hpM, by simp [heq]⟩
        rw [hhit] at this; simp at this
      exact Or.inl ⟨pair, List.mem_filter.mpr ⟨hpM, by simp [hpne]⟩, hbit⟩
  · let ps := hit.map Prod.snd
    have hps_ne : ps ≠ [] := by simp [ps, hhit]
    have hps_mem : ∀ p ∈ ps, p ∈ D.P := by
      intro p hp
      obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hp
      exact (hM pair (List.mem_filter.mp hpair).1).2.1
    obtain ⟨D1, pU, hsub1, hpU, hcard1, hbitU⟩ := addPureList D ps hps_ne hps_mem
    have hd0_clean : d0 &&& pU &&& x2Val = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_and, Nat.zero_testBit]
      cases hd1 : d0.testBit i
      · simp
      · cases hp1 : pU.testBit i
        · simp
        · cases hx2 : x2Val.testBit i
          · simp
          · exfalso
            obtain ⟨p, hpps, hpi⟩ := (hbitU i).mp hp1
            obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hpps
            have hpairM := (List.mem_filter.mp hpair).1
            have hpair1 : pair.1 = d0 := by simpa using (List.mem_filter.mp hpair).2
            have hcl := (hM pair hpairM).2.2
            have hb := congrArg (fun n => n.testBit i) hcl
            rw [hpair1] at hb
            simp [Nat.testBit_and, hd1, hpi, hx2] at hb
    refine ⟨D1, rest, some pU, hsub1, ?_, ?_, ?_, ?_⟩
    · intro pair hp
      have hpM := (List.mem_filter.mp hp).1
      have hpne : pair.1 ≠ d0 := by simpa using (List.mem_filter.mp hp).2
      obtain ⟨h1, h2, h3⟩ := hM pair hpM
      exact ⟨h1.imp (fun h => hsub1 h) (fun h => (Finset.mem_insert.mp h).resolve_left hpne),
        hsub1 h2, h3⟩
    · intro p hp
      cases hp
      exact ⟨hpU, hd0_clean⟩
    · intro e
      obtain ⟨pair, hpM, hbit⟩ := hcov e
      by_cases h1 : pair.1 = d0
      · have hpair_hit : pair ∈ hit := List.mem_filter.mpr ⟨hpM, by simp [h1]⟩
        have hp_ps : pair.2 ∈ ps := List.mem_map.mpr ⟨pair, hpair_hit, rfl⟩
        simp only [Nat.testBit_and, Bool.and_eq_true] at hbit
        have hpU_e : pU.testBit e.val = true := (hbitU e.val).mpr ⟨pair.2, hp_ps, hbit.2⟩
        right
        refine ⟨pU, rfl, ?_⟩
        simp [Nat.testBit_and, h1 ▸ hbit.1, hpU_e]
      · left
        exact ⟨pair, List.mem_filter.mpr ⟨hpM, by simp [h1]⟩, hbit⟩
    · have hps_len : ps.length = hit.length := List.length_map _
      simp only [Option.isSome_some, ↓reduceIte]
      omega

/-! ### Step 2: Pure OR-DAG seed sets, cones, LAM/R split, and Clean Triple Theorem -/

section PureDagTheory

variable (D : PureDag)

noncomputable def dagChildren (w : ℕ) : ℕ × ℕ :=
  if h : w ∈ D.P \ x1Set then
    let a := Classical.choose (D.hbuild w h)
    let ha := Classical.choose_spec (D.hbuild w h)
    let b := Classical.choose ha.2
    (a, b)
  else (0, 0)

lemma dagChildren_spec {w : ℕ} (hw : w ∈ D.P \ x1Set) :
    (dagChildren D w).1 ∈ D.P ∧ (dagChildren D w).2 ∈ D.P ∧
    (dagChildren D w).1 < w ∧ (dagChildren D w).2 < w ∧
    w = (dagChildren D w).1 ||| (dagChildren D w).2 := by
  unfold dagChildren
  rw [dif_pos hw]
  set a := Classical.choose (D.hbuild w hw)
  have ha := Classical.choose_spec (D.hbuild w hw)
  set b := Classical.choose ha.2
  have hb := Classical.choose_spec ha.2
  exact ⟨ha.1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2⟩

noncomputable def seedSet : ℕ → Finset (Fin 11)
  | w =>
    if h1 : w ∈ x1Set then
      {Classical.choose ((h_x1Set_iff w).mp h1)}
    else if h2 : w ∈ D.P \ x1Set then
      have _ : (dagChildren D w).1 < w := (dagChildren_spec D h2).2.2.1
      have _ : (dagChildren D w).2 < w := (dagChildren_spec D h2).2.2.2.1
      seedSet (dagChildren D w).1 ∪ seedSet (dagChildren D w).2
    else ∅
termination_by w => w

noncomputable def dagCone : ℕ → Finset ℕ
  | w =>
    if h2 : w ∈ D.P \ x1Set then
      have _ : (dagChildren D w).1 < w := (dagChildren_spec D h2).2.2.1
      have _ : (dagChildren D w).2 < w := (dagChildren_spec D h2).2.2.2.1
      insert w (dagCone (dagChildren D w).1 ∪ dagCone (dagChildren D w).2)
    else ∅
termination_by w => w

lemma seedSet_x1 {w : ℕ} (hw : w ∈ x1Set) :
    ∃ v : Fin 11, vVal v = w ∧ seedSet D w = {v} := by
  rw [seedSet, dif_pos hw]
  exact ⟨Classical.choose ((h_x1Set_iff w).mp hw),
    Classical.choose_spec ((h_x1Set_iff w).mp hw), rfl⟩

lemma seedSet_step {w : ℕ} (hw : w ∈ D.P \ x1Set) :
    seedSet D w = seedSet D (dagChildren D w).1 ∪ seedSet D (dagChildren D w).2 := by
  have hnx1 : w ∉ x1Set := (Finset.mem_sdiff.mp hw).2
  rw [seedSet, dif_neg hnx1, dif_pos hw]

lemma dagCone_x1 {w : ℕ} (hw : w ∉ D.P \ x1Set) : dagCone D w = ∅ := by
  rw [dagCone, dif_neg hw]

lemma dagCone_step {w : ℕ} (hw : w ∈ D.P \ x1Set) :
    dagCone D w = insert w (dagCone D (dagChildren D w).1 ∪ dagCone D (dagChildren D w).2) := by
  rw [dagCone, dif_pos hw]

lemma seedSet_nonempty : ∀ w ∈ D.P, (seedSet D w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hx1 : w ∈ x1Set
    · obtain ⟨v, _, heq⟩ := seedSet_x1 D hx1
      rw [heq]; exact Finset.singleton_nonempty v
    · have hsd : w ∈ D.P \ x1Set := Finset.mem_sdiff.mpr ⟨hw, hx1⟩
      have hs := dagChildren_spec D hsd
      rw [seedSet_step D hsd]
      exact (ih _ hs.2.2.1 hs.1).mono Finset.subset_union_left

lemma seedSet_testBit : ∀ w ∈ D.P, ∀ i,
    w.testBit i = true ↔ ∃ v ∈ seedSet D w, (vVal v).testBit i = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw i
    by_cases hx1 : w ∈ x1Set
    · obtain ⟨v, hv, heq⟩ := seedSet_x1 D hx1
      rw [heq, ← hv]; simp
    · have hsd : w ∈ D.P \ x1Set := Finset.mem_sdiff.mpr ⟨hw, hx1⟩
      have hs := dagChildren_spec D hsd
      rw [seedSet_step D hsd]
      conv_lhs => rw [hs.2.2.2.2]
      rw [Nat.testBit_or, Bool.or_eq_true, ih _ hs.2.2.1 hs.1 i, ih _ hs.2.2.2.1 hs.2.1 i]
      simp only [Finset.mem_union]
      constructor
      · rintro (⟨v, hv, hb⟩ | ⟨v, hv, hb⟩)
        · exact ⟨v, Or.inl hv, hb⟩
        · exact ⟨v, Or.inr hv, hb⟩
      · rintro ⟨v, hv | hv, hb⟩
        · exact Or.inl ⟨v, hv, hb⟩
        · exact Or.inr ⟨v, hv, hb⟩

lemma seedSet_card_ge_two {w : ℕ} (hw : w ∈ D.P \ x1Set) : 2 ≤ (seedSet D w).card := by
  have hwP := (Finset.mem_sdiff.mp hw).1
  have hnx1 := (Finset.mem_sdiff.mp hw).2
  have hpos : 1 ≤ (seedSet D w).card := Finset.card_pos.mpr (seedSet_nonempty D w hwP)
  by_contra hlt
  have h1 : (seedSet D w).card = 1 := by omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
  have hweq : w = vVal v := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [seedSet_testBit D w hwP i, hv]
    simp
  exact hnx1 (hweq ▸ (h_x1Set_iff (vVal v)).mpr ⟨v, rfl⟩)

lemma dagCone_sub : ∀ w, dagCone D w ⊆ D.P \ x1Set := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hsd : w ∈ D.P \ x1Set
    · have hs := dagChildren_spec D hsd
      rw [dagCone_step D hsd]
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact hsd
      · rcases Finset.mem_union.mp hu' with h | h
        · exact ih _ hs.2.2.1 h
        · exact ih _ hs.2.2.2.1 h
    · rw [dagCone_x1 D hsd]; exact Finset.empty_subset _

lemma dagCone_seedSet_sub : ∀ w, ∀ u ∈ dagCone D w, seedSet D u ⊆ seedSet D w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    by_cases hsd : w ∈ D.P \ x1Set
    · have hs := dagChildren_spec D hsd
      rw [dagCone_step D hsd] at hu
      rcases Finset.mem_insert.mp hu with rfl | hu'
      · exact Finset.Subset.rfl
      · rw [seedSet_step D hsd]
        rcases Finset.mem_union.mp hu' with h | h
        · exact (ih _ hs.2.2.1 u h).trans Finset.subset_union_left
        · exact (ih _ hs.2.2.2.1 u h).trans Finset.subset_union_right
    · rw [dagCone_x1 D hsd] at hu; simp at hu

noncomputable def lamSet : Finset ℕ :=
  (D.P \ x1Set).filter (fun w => ∃ v : Fin 11, ∀ u ∈ seedSet D w, adj v u = true)

noncomputable def restSet : Finset ℕ := (D.P \ x1Set) \ lamSet D

lemma lam_rest_card : (lamSet D).card + (restSet D).card = (D.P \ x1Set).card := by
  have hsub : lamSet D ⊆ D.P \ x1Set := Finset.filter_subset _ _
  have := Finset.card_sdiff_add_card_eq_card hsub
  simpa [restSet, Nat.add_comm] using this

noncomputable def lamCenter (w : ℕ) : Fin 11 :=
  if h : ∃ v : Fin 11, ∀ u ∈ seedSet D w, adj v u = true then
    Classical.choose h
  else 0

lemma lamCenter_spec {w : ℕ} (hw : w ∈ lamSet D) :
    ∀ u ∈ seedSet D w, adj (lamCenter D w) u = true := by
  have hex : ∃ v : Fin 11, ∀ u ∈ seedSet D w, adj v u = true :=
    (Finset.mem_filter.mp hw).2
  unfold lamCenter
  rw [dif_pos hex]
  exact Classical.choose_spec hex

lemma lamCenter_unique {w : ℕ} (hw : w ∈ D.P \ x1Set) {v₁ v₂ : Fin 11}
    (h1 : ∀ u ∈ seedSet D w, adj v₁ u = true)
    (h2 : ∀ u ∈ seedSet D w, adj v₂ u = true) : v₁ = v₂ := by
  by_contra hne
  have hcard := seedSet_card_ge_two D hw
  obtain ⟨u₁, hu₁, u₂, hu₂, hu12⟩ := Finset.one_lt_card.mp (by omega : 1 < (seedSet D w).card)
  have hbad := h_c4_free v₁ v₂ u₁ u₂ hne hu12 (h1 u₁ hu₁) (h1 u₂ hu₂) (h2 u₁ hu₁)
  rw [h2 u₂ hu₂] at hbad
  contradiction

noncomputable def lamEdge (w : ℕ) : Fin 16 × Fin 16 :=
  if hw : w ∈ lamSet D then
    have hsd : w ∈ D.P \ x1Set := (Finset.mem_filter.mp hw).1
    have hs := dagChildren_spec D hsd
    let v := lamCenter D w
    let u₁ := Classical.choose (seedSet_nonempty D _ hs.1)
    let u₂ := Classical.choose (seedSet_nonempty D _ hs.2.1)
    (findEdge v u₁, findEdge v u₂)
  else (0, 0)

noncomputable def lamEdgeList : List (Fin 16 × Fin 16) :=
  (lamSet D).toList.map (lamEdge D)

lemma lamEdgeList_len : (lamEdgeList D).length = (lamSet D).card := by
  simp [lamEdgeList]

lemma lam_connected : ∀ w ∈ D.P, ∀ v : Fin 11,
    (∀ u ∈ seedSet D w, adj v u = true) →
    ∀ u₁ ∈ seedSet D w, ∀ u₂ ∈ seedSet D w,
      conn (lamEdgeList D) (findEdge v u₁) (findEdge v u₂) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw v hv u₁ hu₁ u₂ hu₂
    by_cases hx1 : w ∈ x1Set
    · obtain ⟨x, _, heq⟩ := seedSet_x1 D hx1
      rw [heq] at hu₁ hu₂
      rw [Finset.mem_singleton.mp hu₁, Finset.mem_singleton.mp hu₂]
      exact conn_refl _ _
    · have hsd : w ∈ D.P \ x1Set := Finset.mem_sdiff.mpr ⟨hw, hx1⟩
      have hlam : w ∈ lamSet D := Finset.mem_filter.mpr ⟨hsd, ⟨v, hv⟩⟩
      have hcv : lamCenter D w = v := lamCenter_unique D hsd (lamCenter_spec D hlam) hv
      have hs := dagChildren_spec D hsd
      have hstep := seedSet_step D hsd
      have hva : ∀ u ∈ seedSet D (dagChildren D w).1, adj v u = true :=
        fun u hu => hv u (hstep ▸ Finset.mem_union_left _ hu)
      have hvb : ∀ u ∈ seedSet D (dagChildren D w).2, adj v u = true :=
        fun u hu => hv u (hstep ▸ Finset.mem_union_right _ hu)
      let ua := Classical.choose (seedSet_nonempty D _ hs.1)
      have hua : ua ∈ seedSet D (dagChildren D w).1 :=
        Classical.choose_spec (seedSet_nonempty D _ hs.1)
      let ub := Classical.choose (seedSet_nonempty D _ hs.2.1)
      have hub : ub ∈ seedSet D (dagChildren D w).2 :=
        Classical.choose_spec (seedSet_nonempty D _ hs.2.1)
      have hedge_mem : (findEdge v ua, findEdge v ub) ∈ lamEdgeList D := by
        have h1 : lamEdge D w = (findEdge v ua, findEdge v ub) := by
          unfold lamEdge
          rw [dif_pos hlam, hcv]
        rw [← h1]
        exact List.mem_map.mpr ⟨w, Finset.mem_toList.mpr hlam, rfl⟩
      have hab : conn (lamEdgeList D) (findEdge v ua) (findEdge v ub) :=
        conn_edge hedge_mem
      rw [hstep] at hu₁ hu₂
      rcases Finset.mem_union.mp hu₁ with h1 | h1 <;> rcases Finset.mem_union.mp hu₂ with h2 | h2
      · exact ih _ hs.2.2.1 hs.1 v hva u₁ h1 u₂ h2
      · exact conn_trans (ih _ hs.2.2.1 hs.1 v hva u₁ h1 ua hua)
          (conn_trans hab (ih _ hs.2.2.2.1 hs.2.1 v hvb ub hub u₂ h2))
      · exact conn_trans (ih _ hs.2.2.2.1 hs.2.1 v hvb u₁ h1 ub hub)
          (conn_trans (conn_symm hab) (ih _ hs.2.2.1 hs.1 v hva ua hua u₂ h2))
      · exact ih _ hs.2.2.2.1 hs.2.1 v hvb u₁ h1 u₂ h2

/-! ### Key Lemma: Every wire in `X1 ∪ lamSet` hits at most ONE `conn (lamEdgeList D)`-class of `Star(a)` -/

lemma base_hits_single_class (a : Fin 11) {w : ℕ} (hw : w ∈ D.P) (hnotR : w ∉ restSet D)
    {u₁ u₂ : Fin 11}
    (hu₁ : u₁ ∈ seedSet D w) (ha₁ : adj a u₁ = true)
    (hu₂ : u₂ ∈ seedSet D w) (ha₂ : adj a u₂ = true) :
    conn (lamEdgeList D) (findEdge a u₁) (findEdge a u₂) := by
  by_cases h12 : u₁ = u₂
  · subst h12; exact conn_refl _ _
  · by_cases hx1 : w ∈ x1Set
    · obtain ⟨v, _, heq⟩ := seedSet_x1 D hx1
      rw [heq] at hu₁ hu₂
      have := (Finset.mem_singleton.mp hu₁).trans (Finset.mem_singleton.mp hu₂).symm
      exact (h12 this).elim
    · have hsd : w ∈ D.P \ x1Set := Finset.mem_sdiff.mpr ⟨hw, hx1⟩
      have hlam : w ∈ lamSet D := by
        by_contra hnl
        exact hnotR (Finset.mem_sdiff.mpr ⟨hsd, hnl⟩)
      have hc := lamCenter_spec D hlam
      have hca : lamCenter D w = a := by
        by_contra hne
        have hbad := h_c4_free (lamCenter D w) a u₁ u₂ hne h12 (hc u₁ hu₁) (hc u₂ hu₂) ha₁
        rw [ha₂] at hbad; contradiction
      rw [hca] at hc
      exact lam_connected D w hw a hc u₁ hu₁ u₂ hu₂

/-! ### Key Lemma: `|Cone(B) ∩ restSet|` merges all `Star(a)`-edges of `S(B) ∩ N(a)` into ONE component! -/

noncomputable def coneGateEdge (a : Fin 11) (w : ℕ) : Option (Fin 16 × Fin 16) :=
  if h : w ∈ D.P \ x1Set then
    let ch := dagChildren D w
    if h1 : ∃ u ∈ seedSet D ch.1, adj a u = true then
      if h2 : ∃ u ∈ seedSet D ch.2, adj a u = true then
        some (findEdge a (Classical.choose h1), findEdge a (Classical.choose h2))
      else none
    else none
  else none

noncomputable def coneRestEdges (a : Fin 11) (B : ℕ) : List (Fin 16 × Fin 16) :=
  ((dagCone D B ∩ restSet D).toList.filterMap (coneGateEdge D a))

lemma coneRestEdges_len_le (a : Fin 11) (B : ℕ) :
    (coneRestEdges D a B).length ≤ (dagCone D B ∩ restSet D).card := by
  unfold coneRestEdges
  calc ((dagCone D B ∩ restSet D).toList.filterMap (coneGateEdge D a)).length
      ≤ (dagCone D B ∩ restSet D).toList.length := List.length_filterMap_le _ _
    _ = (dagCone D B ∩ restSet D).card := Finset.length_toList _

lemma coneRestEdges_connect (a : Fin 11) :
    ∀ B ∈ D.P, ∀ u₁ ∈ seedSet D B, adj a u₁ = true →
      ∀ u₂ ∈ seedSet D B, adj a u₂ = true →
      conn (lamEdgeList D ++ coneRestEdges D a B) (findEdge a u₁) (findEdge a u₂) := by
  intro B
  induction B using Nat.strong_induction_on with
  | ind B ih =>
    intro hB u₁ hu₁ ha₁ u₂ hu₂ ha₂
    by_cases hnotR : B ∉ restSet D
    · exact conn_mono (fun p hp => List.mem_append_left _ hp)
        (base_hits_single_class D a hB hnotR hu₁ ha₁ hu₂ ha₂)
    · push_neg at hnotR
      have hsd : B ∈ D.P \ x1Set := (Finset.mem_sdiff.mp hnotR).1
      have hs := dagChildren_spec D hsd
      have hstep := seedSet_step D hsd
      have hcone := dagCone_step D hsd
      have hsubL : ∀ p ∈ lamEdgeList D ++ coneRestEdges D a (dagChildren D B).1,
          p ∈ lamEdgeList D ++ coneRestEdges D a B := by
        intro p hp
        rcases List.mem_append.mp hp with h | h
        · exact List.mem_append_left _ h
        · apply List.mem_append_right
          obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.mp h
          refine List.mem_filterMap.mpr ⟨w, ?_, hwe⟩
          rw [Finset.mem_toList] at hw ⊢
          obtain ⟨hc1, hr1⟩ := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr ⟨hcone ▸ Finset.mem_insert_of_mem (Finset.mem_union_left _ hc1), hr1⟩
      have hsubR : ∀ p ∈ lamEdgeList D ++ coneRestEdges D a (dagChildren D B).2,
          p ∈ lamEdgeList D ++ coneRestEdges D a B := by
        intro p hp
        rcases List.mem_append.mp hp with h | h
        · exact List.mem_append_left _ h
        · apply List.mem_append_right
          obtain ⟨w, hw, hwe⟩ := List.mem_filterMap.mp h
          refine List.mem_filterMap.mpr ⟨w, ?_, hwe⟩
          rw [Finset.mem_toList] at hw ⊢
          obtain ⟨hc2, hr2⟩ := Finset.mem_inter.mp hw
          exact Finset.mem_inter.mpr ⟨hcone ▸ Finset.mem_insert_of_mem (Finset.mem_union_right _ hc2), hr2⟩
      rw [hstep] at hu₁ hu₂
      rcases Finset.mem_union.mp hu₁ with h1 | h1 <;> rcases Finset.mem_union.mp hu₂ with h2 | h2
      · exact conn_mono hsubL (ih _ hs.2.2.1 hs.1 u₁ h1 ha₁ u₂ h2 ha₂)
      · have hex1 : ∃ u ∈ seedSet D (dagChildren D B).1, adj a u = true := ⟨u₁, h1, ha₁⟩
        have hex2 : ∃ u ∈ seedSet D (dagChildren D B).2, adj a u = true := ⟨u₂, h2, ha₂⟩
        let r₁ := Classical.choose hex1
        have hr₁ := Classical.choose_spec hex1
        let r₂ := Classical.choose hex2
        have hr₂ := Classical.choose_spec hex2
        have hB_in : B ∈ dagCone D B ∩ restSet D :=
          Finset.mem_inter.mpr ⟨hcone ▸ Finset.mem_insert_self _ _, hnotR⟩
        have hge : coneGateEdge D a B = some (findEdge a r₁, findEdge a r₂) := by
          unfold coneGateEdge
          rw [dif_pos hsd, dif_pos hex1, dif_pos hex2]
        have hbridge : (findEdge a r₁, findEdge a r₂) ∈ lamEdgeList D ++ coneRestEdges D a B := by
          apply List.mem_append_right
          exact List.mem_filterMap.mpr ⟨B, Finset.mem_toList.mpr hB_in, hge⟩
        exact conn_trans (conn_mono hsubL (ih _ hs.2.2.1 hs.1 u₁ h1 ha₁ r₁ hr₁.1 hr₁.2))
          (conn_trans (conn_edge hbridge)
            (conn_mono hsubR (ih _ hs.2.2.2.1 hs.2.1 r₂ hr₂.1 hr₂.2 u₂ h2 ha₂)))
      · have hex1 : ∃ u ∈ seedSet D (dagChildren D B).1, adj a u = true := ⟨u₂, h2, ha₂⟩
        have hex2 : ∃ u ∈ seedSet D (dagChildren D B).2, adj a u = true := ⟨u₁, h1, ha₁⟩
        let r₁ := Classical.choose hex1
        have hr₁ := Classical.choose_spec hex1
        let r₂ := Classical.choose hex2
        have hr₂ := Classical.choose_spec hex2
        have hB_in : B ∈ dagCone D B ∩ restSet D :=
          Finset.mem_inter.mpr ⟨hcone ▸ Finset.mem_insert_self _ _, hnotR⟩
        have hge : coneGateEdge D a B = some (findEdge a r₁, findEdge a r₂) := by
          unfold coneGateEdge
          rw [dif_pos hsd, dif_pos hex1, dif_pos hex2]
        have hbridge : (findEdge a r₁, findEdge a r₂) ∈ lamEdgeList D ++ coneRestEdges D a B := by
          apply List.mem_append_right
          exact List.mem_filterMap.mpr ⟨B, Finset.mem_toList.mpr hB_in, hge⟩
        exact conn_trans (conn_mono hsubR (ih _ hs.2.2.2.1 hs.2.1 u₁ h1 ha₁ r₂ hr₂.1 hr₂.2))
          (conn_trans (conn_symm (conn_edge hbridge))
            (conn_mono hsubL (ih _ hs.2.2.1 hs.1 r₁ hr₁.1 hr₁.2 u₂ h2 ha₂)))
      · exact conn_mono hsubR (ih _ hs.2.2.2.1 hs.2.1 u₁ h1 ha₁ u₂ h2 ha₂)

lemma cones_rest_disjoint (a : Fin 11) (B C : ℕ)
    (hsub : ∀ u ∈ seedSet D B ∩ seedSet D C, adj a u = true) :
    Disjoint (dagCone D B ∩ restSet D) (dagCone D C ∩ restSet D) := by
  rw [Finset.disjoint_left]
  intro w hwB hwC
  obtain ⟨hwCB, hwR⟩ := Finset.mem_inter.mp hwB
  obtain ⟨hwCC, _⟩ := Finset.mem_inter.mp hwC
  have hsd : w ∈ D.P \ x1Set := (Finset.mem_sdiff.mp hwR).1
  have hnotLam : w ∉ lamSet D := (Finset.mem_sdiff.mp hwR).2
  apply hnotLam
  refine Finset.mem_filter.mpr ⟨hsd, ⟨a, ?_⟩⟩
  intro u hu
  exact hsub u (Finset.mem_inter.mpr
    ⟨dagCone_seedSet_sub D B w hwCB hu, dagCone_seedSet_sub D C w hwCC hu⟩)

lemma cone_rest_card_half (a : Fin 11) (B C : ℕ)
    (hsub : ∀ u ∈ seedSet D B ∩ seedSet D C, adj a u = true) :
    2 * min (dagCone D B ∩ restSet D).card (dagCone D C ∩ restSet D).card ≤ (restSet D).card := by
  have hdisj := cones_rest_disjoint D a B C hsub
  have hun : (dagCone D B ∩ restSet D) ∪ (dagCone D C ∩ restSet D) ⊆ restSet D :=
    Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
  have h1 := Finset.card_le_card hun
  rw [Finset.card_union_of_disjoint hdisj] at h1
  omega

/-! ### Clean Triple Classification & Connection -/

lemma clean_triple_adj {A B C : ℕ} (hA : A ∈ D.P) (hB : B ∈ D.P) (hC : C ∈ D.P)
    (hcl : A &&& B &&& C &&& x2Val = 0)
    {u v : Fin 11} (huB : u ∈ seedSet D B) (huC : u ∈ seedSet D C) (hvA : v ∈ seedSet D A) :
    adj u v = true := by
  by_contra hfalse
  have hf : adj u v = false := by cases h : adj u v <;> simp_all
  obtain ⟨m, hm16, hmu, hmv⟩ := h_nonedge_bad u v hf
  have hAbit : A.testBit m.val = true := (seedSet_testBit D A hA m.val).mpr ⟨v, hvA, hmv⟩
  have hBbit : B.testBit m.val = true := (seedSet_testBit D B hB m.val).mpr ⟨u, huB, hmu⟩
  have hCbit : C.testBit m.val = true := (seedSet_testBit D C hC m.val).mpr ⟨u, huC, hmu⟩
  have hx2bit : x2Val.testBit m.val = true := by rw [h_x2_bit m]; simp [hm16]
  have h0 := congrArg (fun n => n.testBit m.val) hcl
  simp [Nat.testBit_and, hAbit, hBbit, hCbit, hx2bit] at h0

lemma edge_in_triple_decomp {A B C : ℕ} (hA : A ∈ D.P) (hB : B ∈ D.P) (hC : C ∈ D.P)
    (hcl : A &&& B &&& C &&& x2Val = 0)
    {e : Fin 16} (he : (A &&& B &&& C).testBit e.val = true) :
    let u := (edgeEnds e).1
    let v := (edgeEnds e).2
    (u ∈ seedSet D B ∩ seedSet D C ∧ v ∈ seedSet D A) ∨
    (v ∈ seedSet D B ∩ seedSet D C ∧ u ∈ seedSet D A) ∨
    (u ∈ seedSet D A ∩ seedSet D C ∧ v ∈ seedSet D B) ∨
    (v ∈ seedSet D A ∩ seedSet D C ∧ u ∈ seedSet D B) ∨
    (u ∈ seedSet D A ∩ seedSet D B ∧ v ∈ seedSet D C) ∨
    (v ∈ seedSet D A ∩ seedSet D B ∧ u ∈ seedSet D C) := by
  have hdisj : ∀ w, ¬ (w ∈ seedSet D A ∧ w ∈ seedSet D B ∧ w ∈ seedSet D C) := by
    rintro w ⟨h1, h2, h3⟩
    have hbad := clean_triple_adj D hA hB hC hcl h2 h3 h1
    rw [h_adj_irrefl] at hbad; contradiction
  simp only [Nat.testBit_and, Bool.and_eq_true] at he
  obtain ⟨⟨heA, heB⟩, heC⟩ := he
  obtain ⟨a, ha, hae⟩ := (seedSet_testBit D A hA e.val).mp heA
  obtain ⟨b, hb, hbe⟩ := (seedSet_testBit D B hB e.val).mp heB
  obtain ⟨c, hc, hce⟩ := (seedSet_testBit D C hC e.val).mp heC
  rw [h_bit_edge] at hae hbe hce
  simp only [decide_eq_true_eq] at hae hbe hce
  rcases hae with rfl | rfl <;> rcases hbe with hbe | hbe <;> rcases hce with hce | hce
  · exact (hdisj _ ⟨ha, hbe ▸ hb, hce ▸ hc⟩).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨ha, hbe ▸ hb⟩, hce ▸ hc⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨ha, hce ▸ hc⟩, hbe ▸ hb⟩))
  · exact Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨hbe ▸ hb, hce ▸ hc⟩, ha⟩)
  · exact Or.inl ⟨Finset.mem_inter.mpr ⟨hbe ▸ hb, hce ▸ hc⟩, ha⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨ha, hce ▸ hc⟩, hbe ▸ hb⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Finset.mem_inter.mpr ⟨ha, hbe ▸ hb⟩, hce ▸ hc⟩))))
  · exact (hdisj _ ⟨ha, hbe ▸ hb, hce ▸ hc⟩).elim

/-- For ANY clean triple `(A, B, C)` in `D.P`:
    there exists a list `extra` of edges of length `≤ (restSet D).card / 2`
    such that ALL edges of `A &&& B &&& C` are connected in `lamEdgeList D ++ extra`! -/
lemma clean_triple_connected {A B C : ℕ} (hA : A ∈ D.P) (hB : B ∈ D.P) (hC : C ∈ D.P)
    (hcl : A &&& B &&& C &&& x2Val = 0) :
    ∃ extra : List (Fin 16 × Fin 16),
      2 * extra.length ≤ (restSet D).card ∧
      ∀ e₁ e₂ : Fin 16,
        (A &&& B &&& C).testBit e₁.val = true →
        (A &&& B &&& C).testBit e₂.val = true →
        conn (lamEdgeList D ++ extra) e₁ e₂ := by
  let X := seedSet D B ∩ seedSet D C
  let Y := seedSet D A ∩ seedSet D C
  let Z := seedSet D A ∩ seedSet D B
  have hXA : ∀ x ∈ X, ∀ a ∈ seedSet D A, adj x a = true := by
    intro x hx a ha
    exact clean_triple_adj D hA hB hC hcl (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2 ha
  have hYB : ∀ y ∈ Y, ∀ b ∈ seedSet D B, adj y b = true := by
    intro y hy b hb
    have hcl' : B &&& A &&& C &&& x2Val = 0 := by
      simpa [Nat.and_comm, Nat.and_assoc] using hcl
    exact clean_triple_adj D hB hA hC hcl' (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2 hb
  have hZC : ∀ z ∈ Z, ∀ c ∈ seedSet D C, adj z c = true := by
    intro z hz c hc
    have hcl' : C &&& A &&& B &&& x2Val = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      have h0 := congrArg (fun n => n.testBit i) hcl
      simp only [Nat.testBit_and, Nat.zero_testBit] at h0 ⊢
      cases hAi : A.testBit i <;> cases hBi : B.testBit i <;> cases hCi : C.testBit i <;>
        cases hx2i : x2Val.testBit i <;> simp_all
    exact clean_triple_adj D hC hA hB hcl' (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2 hc
  have hdisj : ∀ v, ¬ (v ∈ seedSet D A ∧ v ∈ seedSet D B ∧ v ∈ seedSet D C) := by
    rintro v ⟨h1, h2, h3⟩
    have hbad := hXA v (Finset.mem_inter.mpr ⟨h2, h3⟩) v h1
    rw [h_adj_irrefl] at hbad; contradiction
  -- Helper: if `e` has endpoint `p` in `X` and other in `S(A)`, then `e = findEdge p q`
  have edge_eq_find : ∀ (e : Fin 16) (p q : Fin 11),
      ((edgeEnds e).1 = p ∧ (edgeEnds e).2 = q) ∨ ((edgeEnds e).1 = q ∧ (edgeEnds e).2 = p) →
      e = findEdge p q := by
    intro e p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, h_findEdge_of_ends]
    · rw [h_findEdge_comm, ← h1, ← h2, h_findEdge_of_ends]
  -- Case split on whether one of X, Y, Z has card ≥ 2!
  by_cases hX2 : 2 ≤ X.card
  · -- |X| ≥ 2 implies |S(A)| = 1 (since S(A) is nonempty and C4-free!)
    have hA1 : (seedSet D A).card = 1 := by
      have hpos : 1 ≤ (seedSet D A).card := Finset.card_pos.mpr (seedSet_nonempty D A hA)
      by_contra hne
      obtain ⟨a₁, ha₁, a₂, ha₂, ha12⟩ := Finset.one_lt_card.mp (by omega : 1 < (seedSet D A).card)
      obtain ⟨x₁, hx₁, x₂, hx₂, hx12⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
      have hbad := h_c4_free x₁ x₂ a₁ a₂ hx12 ha12 (hXA x₁ hx₁ a₁ ha₁) (hXA x₁ hx₁ a₂ ha₂) (hXA x₂ hx₂ a₁ ha₁)
      rw [hXA x₂ hx₂ a₂ ha₂] at hbad; contradiction
    obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hA1
    have ha_in : a ∈ seedSet D A := ha_eq ▸ Finset.mem_singleton_self a
    -- Check if a ∈ S(B) or a ∈ S(C)
    by_cases haB : a ∈ seedSet D B
    · -- Then Z = {a}, so S(C) ⊆ N(a), and EVERY edge of A&B&C is (a, c) for c ∈ S(C)!
      have hCsub : ∀ c ∈ seedSet D C, adj a c = true :=
        fun c hc => hZC a (Finset.mem_inter.mpr ⟨ha_in, haB⟩) c hc
      refine ⟨[], by simp, ?_⟩
      intro e₁ e₂ he₁ he₂
      have extract_c : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
          ∃ c ∈ seedSet D C, e = findEdge a c := by
        intro e he
        have hYempty : Y = ∅ := by
          ext v; simp only [Y, Finset.mem_inter, ha_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
          rintro rfl hvC
          exact hdisj _ ⟨ha_in, haB, hvC⟩
        have hd := edge_in_triple_decomp D hA hB hC hcl he
        simp only [← ha_eq] at hd
        rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hv : (edgeEnds e).2 = a := Finset.mem_singleton.mp (ha_eq ▸ h2)
          exact ⟨(edgeEnds e).1, (Finset.mem_inter.mp h1).2, edge_eq_find e a _ (Or.inr ⟨rfl, hv⟩)⟩
        · have hu : (edgeEnds e).1 = a := Finset.mem_singleton.mp (ha_eq ▸ h2)
          exact ⟨(edgeEnds e).2, (Finset.mem_inter.mp h1).2, edge_eq_find e a _ (Or.inl ⟨hu, rfl⟩)⟩
        · change (edgeEnds e).1 ∈ Y at h1; rw [hYempty] at h1; simp at h1
        · change (edgeEnds e).2 ∈ Y at h1; rw [hYempty] at h1; simp at h1
        · have hu : (edgeEnds e).1 = a := Finset.mem_singleton.mp (ha_eq ▸ (Finset.mem_inter.mp h1).1)
          exact ⟨(edgeEnds e).2, h2, edge_eq_find e a _ (Or.inl ⟨hu, rfl⟩)⟩
        · have hv : (edgeEnds e).2 = a := Finset.mem_singleton.mp (ha_eq ▸ (Finset.mem_inter.mp h1).1)
          exact ⟨(edgeEnds e).1, h2, edge_eq_find e a _ (Or.inr ⟨rfl, hv⟩)⟩
      obtain ⟨c₁, hc₁, rfl⟩ := extract_c e₁ he₁
      obtain ⟨c₂, hc₂, rfl⟩ := extract_c e₂ he₂
      simpa using lam_connected D C hC a hCsub c₁ hc₁ c₂ hc₂
    · by_cases haC : a ∈ seedSet D C
      · -- Symmetric: Y = {a}, S(B) ⊆ N(a)!
        have hBsub : ∀ b ∈ seedSet D B, adj a b = true :=
          fun b hb => hYB a (Finset.mem_inter.mpr ⟨ha_in, haC⟩) b hb
        refine ⟨[], by simp, ?_⟩
        intro e₁ e₂ he₁ he₂
        have extract_b : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
            ∃ b ∈ seedSet D B, e = findEdge a b := by
          intro e he
          have hZempty : Z = ∅ := by
            ext v; simp only [Z, Finset.mem_inter, ha_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl hvB; exact haB hvB
          have hd := edge_in_triple_decomp D hA hB hC hcl he
          rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
          · have hv : (edgeEnds e).2 = a := Finset.mem_singleton.mp (ha_eq ▸ h2)
            exact ⟨(edgeEnds e).1, (Finset.mem_inter.mp h1).1, edge_eq_find e a _ (Or.inr ⟨rfl, hv⟩)⟩
          · have hu : (edgeEnds e).1 = a := Finset.mem_singleton.mp (ha_eq ▸ h2)
            exact ⟨(edgeEnds e).2, (Finset.mem_inter.mp h1).1, edge_eq_find e a _ (Or.inl ⟨hu, rfl⟩)⟩
          · have hu : (edgeEnds e).1 = a := Finset.mem_singleton.mp (ha_eq ▸ (Finset.mem_inter.mp h1).1)
            exact ⟨(edgeEnds e).2, h2, edge_eq_find e a _ (Or.inl ⟨hu, rfl⟩)⟩
          · have hv : (edgeEnds e).2 = a := Finset.mem_singleton.mp (ha_eq ▸ (Finset.mem_inter.mp h1).1)
            exact ⟨(edgeEnds e).1, h2, edge_eq_find e a _ (Or.inr ⟨rfl, hv⟩)⟩
          · change (edgeEnds e).1 ∈ Z at h1; rw [hZempty] at h1; simp at h1
          · change (edgeEnds e).2 ∈ Z at h1; rw [hZempty] at h1; simp at h1
        obtain ⟨b₁, hb₁, rfl⟩ := extract_b e₁ he₁
        obtain ⟨b₂, hb₂, rfl⟩ := extract_b e₂ he₂
        simpa using lam_connected D B hB a hBsub b₁ hb₁ b₂ hb₂
      · -- TYPE IV!! Y = ∅, Z = ∅, S(B) ∩ S(C) ⊆ N(a)!
        -- Pick the smaller of coneRestEdges D a B and coneRestEdges D a C!
        have hBC_sub : ∀ u ∈ seedSet D B ∩ seedSet D C, adj a u = true := by
          intro u hu
          rw [h_adj_symm]; exact hXA u hu a ha_in
        have hhalf := cone_rest_card_half D a B C hBC_sub
        have hYempty : Y = ∅ := by
          ext v; simp only [Y, Finset.mem_inter, ha_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
          rintro rfl hvC; exact haC hvC
        have hZempty : Z = ∅ := by
          ext v; simp only [Z, Finset.mem_inter, ha_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
          rintro rfl hvB; exact haB hvB
        have extract_x : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
            ∃ u ∈ seedSet D B ∩ seedSet D C, e = findEdge a u := by
          intro e he
          have hd := edge_in_triple_decomp D hA hB hC hcl he
          rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
          · have hv : (edgeEnds e).2 = a := Finset.mem_singleton.mp (ha_eq ▸ h2)
            exact ⟨(edgeEnds e).1, h1, edge_eq_find e a _ (Or.inr ⟨rfl, hv⟩)⟩
          · have hu : (edgeEnds e).1 = a := Finset.mem_singleton.mp (ha_eq ▸ h2)
            exact ⟨(edgeEnds e).2, h1, edge_eq_find e a _ (Or.inl ⟨hu, rfl⟩)⟩
          · change (edgeEnds e).1 ∈ Y at h1; rw [hYempty] at h1; simp at h1
          · change (edgeEnds e).2 ∈ Y at h1; rw [hYempty] at h1; simp at h1
          · change (edgeEnds e).1 ∈ Z at h1; rw [hZempty] at h1; simp at h1
          · change (edgeEnds e).2 ∈ Z at h1; rw [hZempty] at h1; simp at h1
        by_cases hcmp : (dagCone D B ∩ restSet D).card ≤ (dagCone D C ∩ restSet D).card
        · refine ⟨coneRestEdges D a B, ?_, ?_⟩
          · have hlen := coneRestEdges_len_le D a B
            have hmin : min (dagCone D B ∩ restSet D).card (dagCone D C ∩ restSet D).card =
                (dagCone D B ∩ restSet D).card := Nat.min_eq_left hcmp
            omega
          · intro e₁ e₂ he₁ he₂
            obtain ⟨u₁, hu₁, rfl⟩ := extract_x e₁ he₁
            obtain ⟨u₂, hu₂, rfl⟩ := extract_x e₂ he₂
            exact coneRestEdges_connect D a B hB u₁ (Finset.mem_inter.mp hu₁).1 (hBC_sub u₁ hu₁)
              u₂ (Finset.mem_inter.mp hu₂).1 (hBC_sub u₂ hu₂)
        · refine ⟨coneRestEdges D a C, ?_, ?_⟩
          · have hlen := coneRestEdges_len_le D a C
            have hmin : min (dagCone D B ∩ restSet D).card (dagCone D C ∩ restSet D).card =
                (dagCone D C ∩ restSet D).card := Nat.min_eq_right (by omega)
            omega
          · intro e₁ e₂ he₁ he₂
            obtain ⟨u₁, hu₁, rfl⟩ := extract_x e₁ he₁
            obtain ⟨u₂, hu₂, rfl⟩ := extract_x e₂ he₂
            exact coneRestEdges_connect D a C hC u₁ (Finset.mem_inter.mp hu₁).2 (hBC_sub u₁ hu₁)
              u₂ (Finset.mem_inter.mp hu₂).2 (hBC_sub u₂ hu₂)
  · by_cases hY2 : 2 ≤ Y.card
    · -- Symmetric to X: rotate (A, B, C) -> (B, A, C)
      have hB1 : (seedSet D B).card = 1 := by
        have hpos : 1 ≤ (seedSet D B).card := Finset.card_pos.mpr (seedSet_nonempty D B hB)
        by_contra hne
        obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.one_lt_card.mp (by omega : 1 < (seedSet D B).card)
        obtain ⟨y₁, hy₁, y₂, hy₂, hy12⟩ := Finset.one_lt_card.mp (by omega : 1 < Y.card)
        have hbad := h_c4_free y₁ y₂ b₁ b₂ hy12 hb12 (hYB y₁ hy₁ b₁ hb₁) (hYB y₁ hy₁ b₂ hb₂) (hYB y₂ hy₂ b₁ hb₁)
        rw [hYB y₂ hy₂ b₂ hb₂] at hbad; contradiction
      obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hB1
      have hb_in : b ∈ seedSet D B := hb_eq ▸ Finset.mem_singleton_self b
      by_cases hbA : b ∈ seedSet D A
      · have hCsub : ∀ c ∈ seedSet D C, adj b c = true :=
          fun c hc => hZC b (Finset.mem_inter.mpr ⟨hbA, hb_in⟩) c hc
        refine ⟨[], by simp, ?_⟩
        intro e₁ e₂ he₁ he₂
        have extract_c : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
            ∃ c ∈ seedSet D C, e = findEdge b c := by
          intro e he
          have hXempty : X = ∅ := by
            ext v; simp only [X, Finset.mem_inter, hb_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl hvC; exact hdisj _ ⟨hbA, hb_in, hvC⟩
          have hd := edge_in_triple_decomp D hA hB hC hcl he
          rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · change (edgeEnds e).1 ∈ X at h1; rw [hXempty] at h1; simp at h1
          · change (edgeEnds e).2 ∈ X at h1; rw [hXempty] at h1; simp at h1
          · have hv : (edgeEnds e).2 = b := Finset.mem_singleton.mp (hb_eq ▸ h2)
            exact ⟨(edgeEnds e).1, (Finset.mem_inter.mp h1).2, edge_eq_find e b _ (Or.inr ⟨rfl, hv⟩)⟩
          · have hu : (edgeEnds e).1 = b := Finset.mem_singleton.mp (hb_eq ▸ h2)
            exact ⟨(edgeEnds e).2, (Finset.mem_inter.mp h1).2, edge_eq_find e b _ (Or.inl ⟨hu, rfl⟩)⟩
          · have hu : (edgeEnds e).1 = b := Finset.mem_singleton.mp (hb_eq ▸ (Finset.mem_inter.mp h1).2)
            exact ⟨(edgeEnds e).2, h2, edge_eq_find e b _ (Or.inl ⟨hu, rfl⟩)⟩
          · have hv : (edgeEnds e).2 = b := Finset.mem_singleton.mp (hb_eq ▸ (Finset.mem_inter.mp h1).2)
            exact ⟨(edgeEnds e).1, h2, edge_eq_find e b _ (Or.inr ⟨rfl, hv⟩)⟩
        obtain ⟨c₁, hc₁, rfl⟩ := extract_c e₁ he₁
        obtain ⟨c₂, hc₂, rfl⟩ := extract_c e₂ he₂
        simpa using lam_connected D C hC b hCsub c₁ hc₁ c₂ hc₂
      · by_cases hbC : b ∈ seedSet D C
        · have hAsub : ∀ a ∈ seedSet D A, adj b a = true :=
            fun a ha => hXA b (Finset.mem_inter.mpr ⟨hb_in, hbC⟩) a ha
          refine ⟨[], by simp, ?_⟩
          intro e₁ e₂ he₁ he₂
          have extract_a : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
              ∃ a ∈ seedSet D A, e = findEdge b a := by
            intro e he
            have hZempty : Z = ∅ := by
              ext v; simp only [Z, Finset.mem_inter, hb_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
              rintro hvA rfl; exact hbA hvA
            have hd := edge_in_triple_decomp D hA hB hC hcl he
            rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
            · have hu : (edgeEnds e).1 = b := Finset.mem_singleton.mp (hb_eq ▸ (Finset.mem_inter.mp h1).1)
              exact ⟨(edgeEnds e).2, h2, edge_eq_find e b _ (Or.inl ⟨hu, rfl⟩)⟩
            · have hv : (edgeEnds e).2 = b := Finset.mem_singleton.mp (hb_eq ▸ (Finset.mem_inter.mp h1).1)
              exact ⟨(edgeEnds e).1, h2, edge_eq_find e b _ (Or.inr ⟨rfl, hv⟩)⟩
            · have hv : (edgeEnds e).2 = b := Finset.mem_singleton.mp (hb_eq ▸ h2)
              exact ⟨(edgeEnds e).1, (Finset.mem_inter.mp h1).1, edge_eq_find e b _ (Or.inr ⟨rfl, hv⟩)⟩
            · have hu : (edgeEnds e).1 = b := Finset.mem_singleton.mp (hb_eq ▸ h2)
              exact ⟨(edgeEnds e).2, (Finset.mem_inter.mp h1).1, edge_eq_find e b _ (Or.inl ⟨hu, rfl⟩)⟩
            · change (edgeEnds e).1 ∈ Z at h1; rw [hZempty] at h1; simp at h1
            · change (edgeEnds e).2 ∈ Z at h1; rw [hZempty] at h1; simp at h1
          obtain ⟨a₁, ha₁, rfl⟩ := extract_a e₁ he₁
          obtain ⟨a₂, ha₂, rfl⟩ := extract_a e₂ he₂
          simpa using lam_connected D A hA b hAsub a₁ ha₁ a₂ ha₂
        · have hAC_sub : ∀ u ∈ seedSet D A ∩ seedSet D C, adj b u = true := by
            intro u hu; rw [h_adj_symm]; exact hYB u hu b hb_in
          have hhalf := cone_rest_card_half D b A C hAC_sub
          have hXempty : X = ∅ := by
            ext v; simp only [X, Finset.mem_inter, hb_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro rfl hvC; exact hbC hvC
          have hZempty : Z = ∅ := by
            ext v; simp only [Z, Finset.mem_inter, hb_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
            rintro hvA rfl; exact hbA hvA
          have extract_y : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
              ∃ u ∈ seedSet D A ∩ seedSet D C, e = findEdge b u := by
            intro e he
            have hd := edge_in_triple_decomp D hA hB hC hcl he
            rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
            · change (edgeEnds e).1 ∈ X at h1; rw [hXempty] at h1; simp at h1
            · change (edgeEnds e).2 ∈ X at h1; rw [hXempty] at h1; simp at h1
            · have hv : (edgeEnds e).2 = b := Finset.mem_singleton.mp (hb_eq ▸ h2)
              exact ⟨(edgeEnds e).1, h1, edge_eq_find e b _ (Or.inr ⟨rfl, hv⟩)⟩
            · have hu : (edgeEnds e).1 = b := Finset.mem_singleton.mp (hb_eq ▸ h2)
              exact ⟨(edgeEnds e).2, h1, edge_eq_find e b _ (Or.inl ⟨hu, rfl⟩)⟩
            · change (edgeEnds e).1 ∈ Z at h1; rw [hZempty] at h1; simp at h1
            · change (edgeEnds e).2 ∈ Z at h1; rw [hZempty] at h1; simp at h1
          by_cases hcmp : (dagCone D A ∩ restSet D).card ≤ (dagCone D C ∩ restSet D).card
          · refine ⟨coneRestEdges D b A, ?_, ?_⟩
            · have hlen := coneRestEdges_len_le D b A
              have hmin : min (dagCone D A ∩ restSet D).card (dagCone D C ∩ restSet D).card =
                  (dagCone D A ∩ restSet D).card := Nat.min_eq_left hcmp
              omega
            · intro e₁ e₂ he₁ he₂
              obtain ⟨u₁, hu₁, rfl⟩ := extract_y e₁ he₁
              obtain ⟨u₂, hu₂, rfl⟩ := extract_y e₂ he₂
              exact coneRestEdges_connect D b A hA u₁ (Finset.mem_inter.mp hu₁).1 (hAC_sub u₁ hu₁)
                u₂ (Finset.mem_inter.mp hu₂).1 (hAC_sub u₂ hu₂)
          · refine ⟨coneRestEdges D b C, ?_, ?_⟩
            · have hlen := coneRestEdges_len_le D b C
              have hmin : min (dagCone D A ∩ restSet D).card (dagCone D C ∩ restSet D).card =
                  (dagCone D C ∩ restSet D).card := Nat.min_eq_right (by omega)
              omega
            · intro e₁ e₂ he₁ he₂
              obtain ⟨u₁, hu₁, rfl⟩ := extract_y e₁ he₁
              obtain ⟨u₂, hu₂, rfl⟩ := extract_y e₂ he₂
              exact coneRestEdges_connect D b C hC u₁ (Finset.mem_inter.mp hu₁).2 (hAC_sub u₁ hu₁)
                u₂ (Finset.mem_inter.mp hu₂).2 (hAC_sub u₂ hu₂)
    · by_cases hZ2 : 2 ≤ Z.card
      · -- Symmetric to X: |Z| ≥ 2 implies |S(C)| = 1
        have hC1 : (seedSet D C).card = 1 := by
          have hpos : 1 ≤ (seedSet D C).card := Finset.card_pos.mpr (seedSet_nonempty D C hC)
          by_contra hne
          obtain ⟨c₁, hc₁, c₂, hc₂, hc12⟩ := Finset.one_lt_card.mp (by omega : 1 < (seedSet D C).card)
          obtain ⟨z₁, hz₁, z₂, hz₂, hz12⟩ := Finset.one_lt_card.mp (by omega : 1 < Z.card)
          have hbad := h_c4_free z₁ z₂ c₁ c₂ hz12 hc12 (hZC z₁ hz₁ c₁ hc₁) (hZC z₁ hz₁ c₂ hc₂) (hZC z₂ hz₂ c₁ hc₁)
          rw [hZC z₂ hz₂ c₂ hc₂] at hbad; contradiction
        obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hC1
        have hc_in : c ∈ seedSet D C := hc_eq ▸ Finset.mem_singleton_self c
        by_cases hcA : c ∈ seedSet D A
        · have hBsub : ∀ b ∈ seedSet D B, adj c b = true :=
            fun b hb => hYB c (Finset.mem_inter.mpr ⟨hcA, hc_in⟩) b hb
          refine ⟨[], by simp, ?_⟩
          intro e₁ e₂ he₁ he₂
          have extract_b : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
              ∃ b ∈ seedSet D B, e = findEdge c b := by
            intro e he
            have hXempty : X = ∅ := by
              ext v; simp only [X, Finset.mem_inter, hc_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
              rintro hvB rfl; exact hdisj _ ⟨hcA, hvB, hc_in⟩
            have hd := edge_in_triple_decomp D hA hB hC hcl he
            rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · change (edgeEnds e).1 ∈ X at h1; rw [hXempty] at h1; simp at h1
            · change (edgeEnds e).2 ∈ X at h1; rw [hXempty] at h1; simp at h1
            · have hu : (edgeEnds e).1 = c := Finset.mem_singleton.mp (hc_eq ▸ (Finset.mem_inter.mp h1).2)
              exact ⟨(edgeEnds e).2, h2, edge_eq_find e c _ (Or.inl ⟨hu, rfl⟩)⟩
            · have hv : (edgeEnds e).2 = c := Finset.mem_singleton.mp (hc_eq ▸ (Finset.mem_inter.mp h1).2)
              exact ⟨(edgeEnds e).1, h2, edge_eq_find e c _ (Or.inr ⟨rfl, hv⟩)⟩
            · have hv : (edgeEnds e).2 = c := Finset.mem_singleton.mp (hc_eq ▸ h2)
              exact ⟨(edgeEnds e).1, (Finset.mem_inter.mp h1).2, edge_eq_find e c _ (Or.inr ⟨rfl, hv⟩)⟩
            · have hu : (edgeEnds e).1 = c := Finset.mem_singleton.mp (hc_eq ▸ h2)
              exact ⟨(edgeEnds e).2, (Finset.mem_inter.mp h1).2, edge_eq_find e c _ (Or.inl ⟨hu, rfl⟩)⟩
          obtain ⟨b₁, hb₁, rfl⟩ := extract_b e₁ he₁
          obtain ⟨b₂, hb₂, rfl⟩ := extract_b e₂ he₂
          simpa using lam_connected D B hB c hBsub b₁ hb₁ b₂ hb₂
        · by_cases hcB : c ∈ seedSet D B
          · have hAsub : ∀ a ∈ seedSet D A, adj c a = true :=
              fun a ha => hXA c (Finset.mem_inter.mpr ⟨hcB, hc_in⟩) a ha
            refine ⟨[], by simp, ?_⟩
            intro e₁ e₂ he₁ he₂
            have extract_a : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
                ∃ a ∈ seedSet D A, e = findEdge c a := by
              intro e he
              have hYempty : Y = ∅ := by
                ext v; simp only [Y, Finset.mem_inter, hc_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
                rintro hvA rfl; exact hcA hvA
              have hd := edge_in_triple_decomp D hA hB hC hcl he
              rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have hu : (edgeEnds e).1 = c := Finset.mem_singleton.mp (hc_eq ▸ (Finset.mem_inter.mp h1).2)
                exact ⟨(edgeEnds e).2, h2, edge_eq_find e c _ (Or.inl ⟨hu, rfl⟩)⟩
              · have hv : (edgeEnds e).2 = c := Finset.mem_singleton.mp (hc_eq ▸ (Finset.mem_inter.mp h1).2)
                exact ⟨(edgeEnds e).1, h2, edge_eq_find e c _ (Or.inr ⟨rfl, hv⟩)⟩
              · change (edgeEnds e).1 ∈ Y at h1; rw [hYempty] at h1; simp at h1
              · change (edgeEnds e).2 ∈ Y at h1; rw [hYempty] at h1; simp at h1
              · have hv : (edgeEnds e).2 = c := Finset.mem_singleton.mp (hc_eq ▸ h2)
                exact ⟨(edgeEnds e).1, (Finset.mem_inter.mp h1).1, edge_eq_find e c _ (Or.inr ⟨rfl, hv⟩)⟩
              · have hu : (edgeEnds e).1 = c := Finset.mem_singleton.mp (hc_eq ▸ h2)
                exact ⟨(edgeEnds e).2, (Finset.mem_inter.mp h1).1, edge_eq_find e c _ (Or.inl ⟨hu, rfl⟩)⟩
            obtain ⟨a₁, ha₁, rfl⟩ := extract_a e₁ he₁
            obtain ⟨a₂, ha₂, rfl⟩ := extract_a e₂ he₂
            simpa using lam_connected D A hA c hAsub a₁ ha₁ a₂ ha₂
          · have hAB_sub : ∀ u ∈ seedSet D A ∩ seedSet D B, adj c u = true := by
              intro u hu; rw [h_adj_symm]; exact hZC u hu c hc_in
            have hhalf := cone_rest_card_half D c A B hAB_sub
            have hXempty : X = ∅ := by
              ext v; simp only [X, Finset.mem_inter, hc_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
              rintro hvB rfl; exact hcB hvB
            have hYempty : Y = ∅ := by
              ext v; simp only [Y, Finset.mem_inter, hc_eq, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
              rintro hvA rfl; exact hcA hvA
            have extract_z : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
                ∃ u ∈ seedSet D A ∩ seedSet D B, e = findEdge c u := by
              intro e he
              have hd := edge_in_triple_decomp D hA hB hC hcl he
              rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
              · change (edgeEnds e).1 ∈ X at h1; rw [hXempty] at h1; simp at h1
              · change (edgeEnds e).2 ∈ X at h1; rw [hXempty] at h1; simp at h1
              · change (edgeEnds e).1 ∈ Y at h1; rw [hYempty] at h1; simp at h1
              · change (edgeEnds e).2 ∈ Y at h1; rw [hYempty] at h1; simp at h1
              · have hv : (edgeEnds e).2 = c := Finset.mem_singleton.mp (hc_eq ▸ h2)
                exact ⟨(edgeEnds e).1, h1, edge_eq_find e c _ (Or.inr ⟨rfl, hv⟩)⟩
              · have hu : (edgeEnds e).1 = c := Finset.mem_singleton.mp (hc_eq ▸ h2)
                exact ⟨(edgeEnds e).2, h1, edge_eq_find e c _ (Or.inl ⟨hu, rfl⟩)⟩
            by_cases hcmp : (dagCone D A ∩ restSet D).card ≤ (dagCone D B ∩ restSet D).card
            · refine ⟨coneRestEdges D c A, ?_, ?_⟩
              · have hlen := coneRestEdges_len_le D c A
                have hmin : min (dagCone D A ∩ restSet D).card (dagCone D B ∩ restSet D).card =
                    (dagCone D A ∩ restSet D).card := Nat.min_eq_left hcmp
                omega
              · intro e₁ e₂ he₁ he₂
                obtain ⟨u₁, hu₁, rfl⟩ := extract_z e₁ he₁
                obtain ⟨u₂, hu₂, rfl⟩ := extract_z e₂ he₂
                exact coneRestEdges_connect D c A hA u₁ (Finset.mem_inter.mp hu₁).1 (hAB_sub u₁ hu₁)
                  u₂ (Finset.mem_inter.mp hu₂).1 (hAB_sub u₂ hu₂)
            · refine ⟨coneRestEdges D c B, ?_, ?_⟩
              · have hlen := coneRestEdges_len_le D c B
                have hmin : min (dagCone D A ∩ restSet D).card (dagCone D B ∩ restSet D).card =
                    (dagCone D B ∩ restSet D).card := Nat.min_eq_right (by omega)
                omega
              · intro e₁ e₂ he₁ he₂
                obtain ⟨u₁, hu₁, rfl⟩ := extract_z e₁ he₁
                obtain ⟨u₂, hu₂, rfl⟩ := extract_z e₂ he₂
                exact coneRestEdges_connect D c B hB u₁ (Finset.mem_inter.mp hu₁).2 (hAB_sub u₁ hu₁)
                  u₂ (Finset.mem_inter.mp hu₂).2 (hAB_sub u₂ hu₂)
      · -- TYPES I, II, III: |X| ≤ 1, |Y| ≤ 1, |Z| ≤ 1 -> ZERO extra edges needed!!
        refine ⟨[], by simp, ?_⟩
        intro e₁ e₂ he₁ he₂
        -- Each edge belongs to star(x) for x ∈ X, star(y) for y ∈ Y, or star(z) for z ∈ Z.
        -- Since |X|, |Y|, |Z| ≤ 1, any two edges from the SAME set are connected by `lam_connected`,
        -- and any two nonempty sets among X, Y, Z share the edge between their unique elements!
        have star_conn : ∀ e : Fin 16, (A &&& B &&& C).testBit e.val = true →
            (∃ x ∈ X, ∃ a ∈ seedSet D A, e = findEdge x a) ∨
            (∃ y ∈ Y, ∃ b ∈ seedSet D B, e = findEdge y b) ∨
            (∃ z ∈ Z, ∃ c ∈ seedSet D C, e = findEdge z c) := by
          intro e he
          rcases edge_in_triple_decomp D hA hB hC hcl he with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨(edgeEnds e).1, h1, (edgeEnds e).2, h2, edge_eq_find e _ _ (Or.inl ⟨rfl, rfl⟩)⟩
          · exact Or.inl ⟨(edgeEnds e).2, h1, (edgeEnds e).1, h2, edge_eq_find e _ _ (Or.inr ⟨rfl, rfl⟩)⟩
          · exact Or.inr (Or.inl ⟨(edgeEnds e).1, h1, (edgeEnds e).2, h2, edge_eq_find e _ _ (Or.inl ⟨rfl, rfl⟩)⟩)
          · exact Or.inr (Or.inl ⟨(edgeEnds e).2, h1, (edgeEnds e).1, h2, edge_eq_find e _ _ (Or.inr ⟨rfl, rfl⟩)⟩)
          · exact Or.inr (Or.inr ⟨(edgeEnds e).1, h1, (edgeEnds e).2, h2, edge_eq_find e _ _ (Or.inl ⟨rfl, rfl⟩)⟩)
          · exact Or.inr (Or.inr ⟨(edgeEnds e).2, h1, (edgeEnds e).1, h2, edge_eq_find e _ _ (Or.inr ⟨rfl, rfl⟩)⟩)
        have hXuniq : ∀ x₁ ∈ X, ∀ x₂ ∈ X, x₁ = x₂ := fun x₁ h1 x₂ h2 =>
          Finset.card_le_one.mp (by omega : X.card ≤ 1) x₁ h1 x₂ h2
        have hYuniq : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, y₁ = y₂ := fun y₁ h1 y₂ h2 =>
          Finset.card_le_one.mp (by omega : Y.card ≤ 1) y₁ h1 y₂ h2
        have hZuniq : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ = z₂ := fun z₁ h1 z₂ h2 =>
          Finset.card_le_one.mp (by omega : Z.card ≤ 1) z₁ h1 z₂ h2
        simp only [List.append_nil]
        rcases star_conn e₁ he₁ with ⟨x₁, hx₁, a₁, ha₁, rfl⟩ | ⟨y₁, hy₁, b₁, hb₁, rfl⟩ | ⟨z₁, hz₁, c₁, hc₁, rfl⟩ <;>
        rcases star_conn e₂ he₂ with ⟨x₂, hx₂, a₂, ha₂, rfl⟩ | ⟨y₂, hy₂, b₂, hb₂, rfl⟩ | ⟨z₂, hz₂, c₂, hc₂, rfl⟩
        · rw [hXuniq x₁ hx₁ x₂ hx₂]
          exact lam_connected D A hA x₂ (hXA x₂ hx₂) a₁ ha₁ a₂ ha₂
        · have hyA : y₂ ∈ seedSet D A := (Finset.mem_inter.mp hy₂).1
          have hxB : x₁ ∈ seedSet D B := (Finset.mem_inter.mp hx₁).1
          exact conn_trans (lam_connected D A hA x₁ (hXA x₁ hx₁) a₁ ha₁ y₂ hyA)
            (by rw [h_findEdge_comm x₁ y₂]; exact lam_connected D B hB y₂ (hYB y₂ hy₂) x₁ hxB b₂ hb₂)
        · have hzA : z₂ ∈ seedSet D A := (Finset.mem_inter.mp hz₂).1
          have hxC : x₁ ∈ seedSet D C := (Finset.mem_inter.mp hx₁).2
          exact conn_trans (lam_connected D A hA x₁ (hXA x₁ hx₁) a₁ ha₁ z₂ hzA)
            (by rw [h_findEdge_comm x₁ z₂]; exact lam_connected D C hC z₂ (hZC z₂ hz₂) x₁ hxC c₂ hc₂)
        · have hyA : y₁ ∈ seedSet D A := (Finset.mem_inter.mp hy₁).1
          have hxB : x₂ ∈ seedSet D B := (Finset.mem_inter.mp hx₂).1
          exact conn_trans (lam_connected D B hB y₁ (hYB y₁ hy₁) b₁ hb₁ x₂ hxB)
            (by rw [h_findEdge_comm y₁ x₂]; exact lam_connected D A hA x₂ (hXA x₂ hx₂) y₁ hyA a₂ ha₂)
        · rw [hYuniq y₁ hy₁ y₂ hy₂]
          exact lam_connected D B hB y₂ (hYB y₂ hy₂) b₁ hb₁ b₂ hb₂
        · have hzB : z₂ ∈ seedSet D B := (Finset.mem_inter.mp hz₂).2
          have hyC : y₁ ∈ seedSet D C := (Finset.mem_inter.mp hy₁).2
          exact conn_trans (lam_connected D B hB y₁ (hYB y₁ hy₁) b₁ hb₁ z₂ hzB)
            (by rw [h_findEdge_comm y₁ z₂]; exact lam_connected D C hC z₂ (hZC z₂ hz₂) y₁ hyC c₂ hc₂)
        · have hzA : z₁ ∈ seedSet D A := (Finset.mem_inter.mp hz₁).1
          have hxC : x₂ ∈ seedSet D C := (Finset.mem_inter.mp hx₂).2
          exact conn_trans (lam_connected D C hC z₁ (hZC z₁ hz₁) c₁ hc₁ x₂ hxC)
            (by rw [h_findEdge_comm z₁ x₂]; exact lam_connected D A hA x₂ (hXA x₂ hx₂) z₁ hzA a₂ ha₂)
        · have hzB : z₁ ∈ seedSet D B := (Finset.mem_inter.mp hz₁).2
          have hyC : y₂ ∈ seedSet D C := (Finset.mem_inter.mp hy₂).2
          exact conn_trans (lam_connected D C hC z₁ (hZC z₁ hz₁) c₁ hc₁ y₂ hyC)
            (by rw [h_findEdge_comm z₁ y₂]; exact lam_connected D B hB y₂ (hYB y₂ hy₂) z₁ hzB b₂ hb₂)
        · rw [hZuniq z₁ hz₁ z₂ hz₂]
          exact lam_connected D C hC z₂ (hZC z₂ hz₂) c₁ hc₁ c₂ hc₂

/-- For ANY clean pure-pure pair `(A, B)` in `D.P`: ZERO extra edges needed! -/
lemma clean_pair_connected {A B : ℕ} (hA : A ∈ D.P) (hB : B ∈ D.P)
    (hcl : A &&& B &&& x2Val = 0) :
    ∀ e₁ e₂ : Fin 16,
      (A &&& B).testBit e₁.val = true →
      (A &&& B).testBit e₂.val = true →
      conn (lamEdgeList D) e₁ e₂ := by
  have hAB_adj : ∀ a ∈ seedSet D A, ∀ b ∈ seedSet D B, adj a b = true := by
    intro a ha b hb
    have hcl3 : A &&& B &&& B &&& x2Val = 0 := by simpa [Nat.and_assoc, Nat.and_self] using hcl
    rw [h_adj_symm]
    exact clean_triple_adj D hA hB hB hcl3 hb hb ha
  have hcase : (seedSet D A).card = 1 ∨ (seedSet D B).card = 1 := by
    by_contra h
    push_neg at h
    have h1 : 1 ≤ (seedSet D A).card := Finset.card_pos.mpr (seedSet_nonempty D A hA)
    have h2 : 1 ≤ (seedSet D B).card := Finset.card_pos.mpr (seedSet_nonempty D B hB)
    obtain ⟨a₁, ha₁, a₂, ha₂, ha12⟩ := Finset.one_lt_card.mp (by omega : 1 < (seedSet D A).card)
    obtain ⟨b₁, hb₁, b₂, hb₂, hb12⟩ := Finset.one_lt_card.mp (by omega : 1 < (seedSet D B).card)
    have hbad := h_c4_free a₁ a₂ b₁ b₂ ha12 hb12 (hAB_adj a₁ ha₁ b₁ hb₁) (hAB_adj a₁ ha₁ b₂ hb₂) (hAB_adj a₂ ha₂ b₁ hb₁)
    rw [hAB_adj a₂ ha₂ b₂ hb₂] at hbad; contradiction
  have edge_eq_find : ∀ (e : Fin 16) (p q : Fin 11),
      ((edgeEnds e).1 = p ∧ (edgeEnds e).2 = q) ∨ ((edgeEnds e).1 = q ∧ (edgeEnds e).2 = p) →
      e = findEdge p q := by
    intro e p q h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2, h_findEdge_of_ends]
    · rw [h_findEdge_comm, ← h1, ← h2, h_findEdge_of_ends]
  rcases hcase with hA1 | hB1
  · obtain ⟨a, ha_eq⟩ := Finset.card_eq_one.mp hA1
    have ha_in : a ∈ seedSet D A := ha_eq ▸ Finset.mem_singleton_self a
    have hBsub : ∀ b ∈ seedSet D B, adj a b = true := fun b hb => hAB_adj a ha_in b hb
    have hdisj : a ∉ seedSet D B := fun h => by have := hBsub a h; rw [h_adj_irrefl] at this; contradiction
    have extract : ∀ e : Fin 16, (A &&& B).testBit e.val = true → ∃ b ∈ seedSet D B, e = findEdge a b := by
      intro e he
      simp only [Nat.testBit_and, Bool.and_eq_true] at he
      obtain ⟨u, hu, hue⟩ := (seedSet_testBit D A hA e.val).mp he.1
      obtain ⟨v, hv, hve⟩ := (seedSet_testBit D B hB e.val).mp he.2
      have hua : u = a := Finset.mem_singleton.mp (ha_eq ▸ hu)
      rw [hua] at hue
      rw [h_bit_edge] at hue hve
      simp only [decide_eq_true_eq] at hue hve
      rcases hue with h1 | h1 <;> rcases hve with h2 | h2
      · exfalso; exact hdisj ((h1.trans h2.symm) ▸ hv)
      · exact ⟨v, hv, edge_eq_find e a v (Or.inl ⟨h1.symm, h2.symm⟩)⟩
      · exact ⟨v, hv, edge_eq_find e a v (Or.inr ⟨h2.symm, h1.symm⟩)⟩
      · exfalso; exact hdisj ((h1.trans h2.symm) ▸ hv)
    intro e₁ e₂ he₁ he₂
    obtain ⟨b₁, hb₁, rfl⟩ := extract e₁ he₁
    obtain ⟨b₂, hb₂, rfl⟩ := extract e₂ he₂
    exact lam_connected D B hB a hBsub b₁ hb₁ b₂ hb₂
  · obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.mp hB1
    have hb_in : b ∈ seedSet D B := hb_eq ▸ Finset.mem_singleton_self b
    have hAsub : ∀ a ∈ seedSet D A, adj b a = true := fun a ha => by
      rw [h_adj_symm]; exact hAB_adj a ha b hb_in
    have hdisj : b ∉ seedSet D A := fun h => by have := hAsub b h; rw [h_adj_irrefl] at this; contradiction
    have extract : ∀ e : Fin 16, (A &&& B).testBit e.val = true → ∃ a ∈ seedSet D A, e = findEdge b a := by
      intro e he
      simp only [Nat.testBit_and, Bool.and_eq_true] at he
      obtain ⟨u, hu, hue⟩ := (seedSet_testBit D A hA e.val).mp he.1
      obtain ⟨v, hv, hve⟩ := (seedSet_testBit D B hB e.val).mp he.2
      have hvb : v = b := Finset.mem_singleton.mp (hb_eq ▸ hv)
      rw [hvb] at hve
      rw [h_bit_edge] at hue hve
      simp only [decide_eq_true_eq] at hue hve
      rcases hue with h1 | h1 <;> rcases hve with h2 | h2
      · exfalso; exact hdisj ((h2.trans h1.symm) ▸ hu)
      · exact ⟨u, hu, edge_eq_find e b u (Or.inr ⟨h1.symm, h2.symm⟩)⟩
      · exact ⟨u, hu, edge_eq_find e b u (Or.inl ⟨h2.symm, h1.symm⟩)⟩
      · exfalso; exact hdisj ((h2.trans h1.symm) ▸ hu)
    intro e₁ e₂ he₁ he₂
    obtain ⟨a₁, ha₁, rfl⟩ := extract e₁ he₁
    obtain ⟨a₂, ha₂, rfl⟩ := extract e₂ he₂
    exact lam_connected D A hA b hAsub a₁ ha₁ a₂ ha₂

end PureDagTheory

/-! ### Putting Everything Together: `16 ≤ x7.card + (x6 \ x8).card` -/

lemma main_edge_bound
    (x4 x5 : ℕ) (x6 x7 : Finset ℕ)
    (hx4 : x4 ∈ Finset.image₂ (· &&& ·) {w ∈ x6 | w ≤ x3Val} {w ∈ x6 | w ≤ x3Val})
    (hx5 : x5 ∈ Finset.image₂ (· &&& ·) {w ∈ x6 | w ≤ x3Val} {w ∈ x6 | w ≤ x3Val})
    (hx4_dirty : x4 &&& x2Val ≠ 0)
    (hx5_dirty : x5 &&& x2Val ≠ 0)
    (hx45_ov : x4 &&& x5 &&& x2Val ≠ 0)
    (hbuild : ∀ w ∈ x6 \ insert (x4 ||| b40) (insert (x5 ||| b41) x1Set),
      ∃ a ∈ x6, ∃ b ∈ x6, a < w ∧ b < w ∧ w = a ||| b)
    (hseeds : ∀ w ∈ x6, w < lim42 ∧ w ≠ 0 ∧ ∀ r < 42, w.testBit r = true →
      ∃ a ∈ x6 ∩ insert (x4 ||| b40) (insert (x5 ||| b41) x1Set), a ||| w = w ∧ a.testBit r = true)
    (hcov : ∀ r ∈ insert 40 (Finset.range 16), ∃ b ∈ x7, b.testBit r = true)
    (hB : ∀ b ∈ x7,
      b ∈ Finset.image₂ (fun u v => u &&& v &&& x3Val |||
            if (u ||| v) &&& b401 = b401 then b40 else 0) x6 x6 ∧
      b &&& x2Val = 0) :
    16 ≤ x7.card + (x6 \ insert (x4 ||| b40) (insert (x5 ||| b41) x1Set)).card := by
  let x8 := insert (x4 ||| b40) (insert (x5 ||| b41) x1Set)
  let x9 := {w ∈ x6 | w ≤ x3Val}
  let d0 := x4 ||| b40
  let e0 := x5 ||| b41
  obtain ⟨s1, hs1, s2, hs2, hx4_eq⟩ := Finset.mem_image₂.mp hx4
  obtain ⟨t1, ht1, t2, ht2, hx5_eq⟩ := Finset.mem_image₂.mp hx5
  have hs1_le : s1 ≤ x3Val := (Finset.mem_filter.mp hs1).2
  have hs2_le : s2 ≤ x3Val := (Finset.mem_filter.mp hs2).2
  have ht1_le : t1 ≤ x3Val := (Finset.mem_filter.mp ht1).2
  have ht2_le : t2 ≤ x3Val := (Finset.mem_filter.mp ht2).2
  have hx4_le : x4 ≤ x3Val := by
    rw [← hx4_eq]; exact Nat.and_le_left.trans hs1_le
  have hx5_le : x5 ≤ x3Val := by
    rw [← hx5_eq]; exact Nat.and_le_left.trans ht1_le
  have hd0_gt : ¬ d0 ≤ x3Val := by
    have hx3 : x3Val = 2 ^ 40 - 1 := by decide
    have hb : b40 = 2 ^ 40 := by decide
    have hle : b40 ≤ d0 := Nat.right_le_or
    omega
  have he0_gt : ¬ e0 ≤ x3Val := by
    have hx3 : x3Val = 2 ^ 40 - 1 := by decide
    have hb : b41 = 2 ^ 41 := by decide
    have hle : b41 ≤ e0 := Nat.right_le_or
    omega
  -- Every dirty wire w ∈ x6 \ x9 contains x4 or x5 bitwise!
  have hdirty_sub : ∀ w ∈ x6, ¬ w ≤ x3Val → x4 ||| w = w ∨ x5 ||| w = w := by
    intro w hw hgt
    have hlt := (hseeds w hw).1
    have h401 : w.testBit 40 = true ∨ w.testBit 41 = true := by
      have hiff := h_le_x3_iff w hlt
      cases h40 : w.testBit 40 <;> cases h41 : w.testBit 41
      · exfalso; exact hgt (hiff.mpr ⟨h40, h41⟩)
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    rcases h401 with h40 | h41
    · obtain ⟨a, ha, haw, ha40⟩ := (hseeds w hw).2.2 40 (by omega) h40
      have ha8 := (Finset.mem_inter.mp ha).2
      simp only [Finset.mem_insert] at ha8
      rcases ha8 with rfl | rfl | hax1
      · left
        have hsub : x4 ||| (x4 ||| b40) = x4 ||| b40 := by rw [← Nat.or_assoc, Nat.or_self]
        exact bitwise_sub_trans hsub haw
      · exfalso
        have hx3lim : x3Val < lim42 := by decide
        have hx5_40 : x5.testBit 40 = false := (h_le_x3_iff x5 (by omega)).mp hx5_le |>.1
        have hb41_40 : b41.testBit 40 = false := by decide
        rw [Nat.testBit_or, hx5_40, hb41_40] at ha40; simp at ha40
      · exfalso
        obtain ⟨v, rfl⟩ := (h_x1Set_iff a).mp hax1
        have hx3lim : x3Val < lim42 := by decide
        have hv_40 : (vVal v).testBit 40 = false :=
          (h_le_x3_iff (vVal v) (Nat.lt_of_le_of_lt (h_vVal_le v) hx3lim)).mp (h_vVal_le v) |>.1
        rw [hv_40] at ha40; simp at ha40
    · obtain ⟨a, ha, haw, ha41⟩ := (hseeds w hw).2.2 41 (by omega) h41
      have ha8 := (Finset.mem_inter.mp ha).2
      simp only [Finset.mem_insert] at ha8
      rcases ha8 with rfl | rfl | hax1
      · exfalso
        have hx3lim : x3Val < lim42 := by decide
        have hx4_41 : x4.testBit 41 = false := (h_le_x3_iff x4 (by omega)).mp hx4_le |>.2
        have hb40_41 : b40.testBit 41 = false := by decide
        rw [Nat.testBit_or, hx4_41, hb40_41] at ha41; simp at ha41
      · right
        have hsub : x5 ||| (x5 ||| b41) = x5 ||| b41 := by rw [← Nat.or_assoc, Nat.or_self]
        exact bitwise_sub_trans hsub haw
      · exfalso
        obtain ⟨v, rfl⟩ := (h_x1Set_iff a).mp hax1
        have hx3lim : x3Val < lim42 := by decide
        have hv_41 : (vVal v).testBit 41 = false :=
          (h_le_x3_iff (vVal v) (Nat.lt_of_le_of_lt (h_vVal_le v) hx3lim)).mp (h_vVal_le v) |>.2
        rw [hv_41] at ha41; simp at ha41
  -- Two dirty wires NEVER intersect cleanly!
  have hdirty_dirty : ∀ u ∈ x6, ∀ v ∈ x6, ¬ u ≤ x3Val → ¬ v ≤ x3Val → u &&& v &&& x2Val ≠ 0 := by
    intro u hu v hv hgu hgv hzero
    have hbit_zero : ∀ a b : ℕ, a ||| u = u → b ||| v = v → a &&& b &&& x2Val = 0 := by
      intro a b hau hbv
      apply Nat.eq_of_testBit_eq; intro i
      have hz := congrArg (fun n => n.testBit i) hzero
      simp only [Nat.testBit_and, Nat.zero_testBit] at hz ⊢
      cases ha : a.testBit i <;> cases hb : b.testBit i <;> cases hx2 : x2Val.testBit i
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · have hu' := testBit_of_or_eq hau i ha
        have hv' := testBit_of_or_eq hbv i hb
        rw [hu', hv', hx2] at hz; simp at hz
    rcases hdirty_sub u hu hgu with hu4 | hu5 <;> rcases hdirty_sub v hv hgv with hv4 | hv5
    · exact hx4_dirty (by simpa [Nat.and_self] using hbit_zero x4 x4 hu4 hv4)
    · exact hx45_ov (hbit_zero x4 x5 hu4 hv5)
    · exact hx45_ov (by simpa [Nat.and_comm x4 x5] using hbit_zero x5 x4 hu5 hv4)
    · exact hx5_dirty (by simpa [Nat.and_self] using hbit_zero x5 x5 hu5 hv5)
  -- Build initial PureDag D0 = x9 ∪ x1Set, and Dd0 = x6 \ x9
  let D0 : PureDag := {
    P := x9 ∪ x1Set
    hx1 := Finset.subset_union_right
    hbound := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact (Finset.mem_filter.mp h).2
      · obtain ⟨v, rfl⟩ := (h_x1Set_iff w).mp h; exact h_vVal_le v
    hbuild := by
      intro w hw
      obtain ⟨hwP, hnx1⟩ := Finset.mem_sdiff.mp hw
      have hw9 : w ∈ x9 := (Finset.mem_union.mp hwP).resolve_right hnx1
      have hw6 : w ∈ x6 := (Finset.mem_filter.mp hw9).1
      have hwle : w ≤ x3Val := (Finset.mem_filter.mp hw9).2
      have hnx8 : w ∉ x8 := by
        intro hx
        simp only [x8, Finset.mem_insert] at hx
        rcases hx with rfl | rfl | h
        · exact hd0_gt hwle
        · exact he0_gt hwle
        · exact hnx1 h
      obtain ⟨a, ha, b, hb, haw, hbw, hwab⟩ := hbuild w (Finset.mem_sdiff.mpr ⟨hw6, hnx8⟩)
      exact ⟨a, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, by omega⟩),
        b, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, by omega⟩), haw, hbw, hwab⟩
  }
  let Dd0 : Finset ℕ := x6 \ x9
  -- Partition (x6 \ x8).card = (D0.P \ x1Set).card + (Dd0 \ {d0, e0}).card
  have hpart_card : (D0.P \ x1Set).card + (Dd0 \ {d0, e0}).card = (x6 \ x8).card := by
    have hdisj : Disjoint (D0.P \ x1Set) (Dd0 \ {d0, e0}) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      have hwle := D0.hbound w (Finset.mem_sdiff.mp h1).1
      have hw9 : w ∉ x9 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).2
      have hw6 : w ∈ x6 := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp h2).1).1
      exact hw9 (Finset.mem_filter.mpr ⟨hw6, hwle⟩)
    have hun : (D0.P \ x1Set) ∪ (Dd0 \ {d0, e0}) = x6 \ x8 := by
      ext w
      simp only [Finset.mem_union, Finset.mem_sdiff, D0, Dd0, x9, x8, Finset.mem_filter,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (⟨hw9 | hwx1, hnx1⟩ | ⟨⟨hw6, hnotle⟩, hne⟩)
        · refine ⟨hw9.1, ?_⟩
          rintro (rfl | rfl | h)
          · exact hd0_gt hw9.2
          · exact he0_gt hw9.2
          · exact hnx1 h
        · exact (hnx1 hwx1).elim
        · refine ⟨hw6, ?_⟩
          rintro (rfl | rfl | h)
          · exact hne (Or.inl rfl)
          · exact hne (Or.inr rfl)
          · obtain ⟨v, rfl⟩ := (h_x1Set_iff w).mp h
            exact hnotle ⟨hw6, h_vVal_le v⟩
      · rintro ⟨hw6, hnx8⟩
        by_cases hle : w ≤ x3Val
        · left
          exact ⟨Or.inl ⟨hw6, hle⟩, fun h => hnx8 (Or.inr (Or.inr h))⟩
        · right
          refine ⟨⟨hw6, fun h => hle h.2⟩, ?_⟩
          rintro (rfl | rfl)
          · exact hnx8 (Or.inl rfl)
          · exact hnx8 (Or.inr (Or.inl rfl))
    rw [← Finset.card_union_of_disjoint hdisj, hun]
  -- Every b ∈ x7 yields a clean pair (u, p) with u ∈ D0.P ∪ Dd0, p ∈ D0.P
  have hpair_ex : ∀ b ∈ x7, ∃ pair : ℕ × ℕ,
      isCleanPair D0.P Dd0 pair ∧ ∀ e : Fin 16, b.testBit e.val = (pair.1 &&& pair.2).testBit e.val := by
    intro b hb
    obtain ⟨hb11, hbcl⟩ := hB b hb
    obtain ⟨u, hu6, v, hv6, hb_eq⟩ := Finset.mem_image₂.mp hb11
    have huv_cl : u &&& v &&& x2Val = 0 := by
      apply Nat.eq_of_testBit_eq; intro i
      have hz := congrArg (fun n => n.testBit i) hbcl
      rw [← hb_eq] at hz
      simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at hz ⊢
      by_cases hi : i < 40
      · have hx3i : x3Val.testBit i = true := h_x3_bit ⟨i, hi⟩
        cases hu : u.testBit i <;> cases hv : v.testBit i <;> cases hx2 : x2Val.testBit i <;>
          simp_all
      · have hx2i : x2Val.testBit i = false := by
          have hlt40 : x2Val < 2 ^ 40 := by decide
          have hpow : 2 ^ 40 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
          exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt40 hpow)
        simp [hx2i]
    have hbit_eq : ∀ e : Fin 16, b.testBit e.val = (u &&& v).testBit e.val := by
      intro e
      rw [← hb_eq, Nat.testBit_or, Nat.testBit_and, h_x3_bit ⟨e.val, by omega⟩, Bool.and_true]
      have htag : (if (u ||| v) &&& b401 = b401 then b40 else 0).testBit e.val = false := by
        split_ifs
        · rw [h_b40_bit e.val (by omega)]; simp; omega
        · simp
      rw [htag, Bool.or_false]
    by_cases hvle : v ≤ x3Val
    · refine ⟨(u, v), ⟨?_, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv6, hvle⟩), huv_cl⟩, hbit_eq⟩
      by_cases hule : u ≤ x3Val
      · exact Or.inl (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu6, hule⟩))
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hu6, fun h => hule (Finset.mem_filter.mp h).2⟩)
    · have hule : u ≤ x3Val := by
        by_contra hgu
        exact hdirty_dirty u hu6 v hv6 hgu hvle huv_cl
      refine ⟨(v, u), ⟨Or.inr (Finset.mem_sdiff.mpr ⟨hv6, fun h => hvle (Finset.mem_filter.mp h).2⟩),
        Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu6, hule⟩),
        by simpa [Nat.and_comm u v] using huv_cl⟩, ?_⟩
      intro e; rw [hbit_eq e, Nat.and_comm]
  let M0 : List (ℕ × ℕ) := x7.attach.toList.map (fun ⟨b, hb⟩ => Classical.choose (hpair_ex b hb))
  have hM0_len : M0.length = x7.card := by simp [M0]
  have hM0_clean : ∀ pair ∈ M0, isCleanPair D0.P Dd0 pair := by
    intro pair hp
    obtain ⟨⟨b, hb⟩, _, rfl⟩ := List.mem_map.mp hp
    exact (Classical.choose_spec (hpair_ex b hb)).1
  have hM0_cov : coversAllEdges M0 := by
    intro e
    obtain ⟨b, hb, hbe⟩ := hcov e.val (Finset.mem_insert_of_mem (Finset.mem_range.mpr e.isLt))
    refine ⟨Classical.choose (hpair_ex b hb), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨⟨b, hb⟩, Finset.mem_toList.mpr (Finset.mem_attach _ _), rfl⟩
    · rw [← (Classical.choose_spec (hpair_ex b hb)).2 e]; exact hbe
  have hDd0_build : ∀ w ∈ Dd0 \ {d0, e0},
      ∃ a ∈ D0.P ∪ Dd0, ∃ b ∈ D0.P ∪ Dd0, a < w ∧ b < w ∧ w = a ||| b := by
    intro w hw
    obtain ⟨hwDd, hwne⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hw6, hnot9⟩ := Finset.mem_sdiff.mp hwDd
    have hnx8 : w ∉ x8 := by
      intro hx
      simp only [x8, Finset.mem_insert] at hx
      rcases hx with rfl | rfl | h
      · exact hwne (by simp [d0])
      · exact hwne (by simp [e0])
      · obtain ⟨v, rfl⟩ := (h_x1Set_iff w).mp h
        exact hnot9 (Finset.mem_filter.mpr ⟨hw6, h_vVal_le v⟩)
    obtain ⟨a, ha, b, hb, haw, hbw, hwab⟩ := hbuild w (Finset.mem_sdiff.mpr ⟨hw6, hnx8⟩)
    have hmem : ∀ z ∈ x6, z ∈ D0.P ∪ Dd0 := by
      intro z hz
      by_cases hz9 : z ∈ x9
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hz9)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hz9⟩)
    exact ⟨a, hmem a ha, b, hmem b hb, haw, hbw, hwab⟩
  -- Run Step 1: Eliminate all dirty OR gates!
  obtain ⟨D1, M1, hsub01, hM1_clean, hM1_cov, hcost1⟩ :=
    elim_dirty_or (Dd0 \ {d0, e0}).card d0 e0 D0 Dd0 M0 rfl hDd0_build hM0_clean hM0_cov
  -- Run Step 1b: Merge all d0-pairs into at most 1 (pD), then all e0-pairs into at most 1 (pE)!
  obtain ⟨D2, M2, pD, hsub12, hM2_clean, hpD_spec, hcov2, hcost2⟩ :=
    merge_single_dirty d0 D1 {e0} M1 hM1_clean hM1_cov
  -- Now merge e0-pairs in M2 (keeping pD untouched!)
  -- Wait: use merge_single_dirty directly on M2 by restricting to edges covered by M2, or simpler:
  -- do the exact same 2-line filter on M2 for e0!
  have hM2_clean' : ∀ pair ∈ M2, isCleanPair D2.P (insert e0 ∅) pair := by
    simpa using hM2_clean
  let hitE := M2.filter (fun pair => decide (pair.1 = e0))
  let Mpure := M2.filter (fun pair => decide (pair.1 ≠ e0))
  have hlen2 : hitE.length + Mpure.length = M2.length :=
    list_filter_partition_len (fun pair : ℕ × ℕ => pair.1 = e0) M2
  -- Produce D3, pE : Option ℕ!
  have hstepE : ∃ (D3 : PureDag) (pE : Option ℕ),
      D2.P ⊆ D3.P ∧
      (∀ p, pE = some p → p ∈ D3.P ∧ e0 &&& p &&& x2Val = 0) ∧
      (∀ e : Fin 16,
        (∃ pair ∈ Mpure, (pair.1 &&& pair.2).testBit e.val = true) ∨
        (∃ p, pD = some p ∧ (d0 &&& p).testBit e.val = true) ∨
        (∃ p, pE = some p ∧ (e0 &&& p).testBit e.val = true)) ∧
      Mpure.length + (if pE.isSome then 1 else 0) + (D3.P \ x1Set).card ≤
        M2.length + (D2.P \ x1Set).card := by
    by_cases hhit : hitE = []
    · refine ⟨D2, none, Finset.Subset.rfl, by simp, ?_, by simp; omega⟩
      intro e
      rcases hcov2 e with ⟨pair, hp2, hbit⟩ | ⟨p, hp, hbit⟩
      · have hpne : pair.1 ≠ e0 := by
          intro heq
          have : pair ∈ hitE := List.mem_filter.mpr ⟨hp2, by simp [heq]⟩
          rw [hhit] at this; simp at this
        exact Or.inl ⟨pair, List.mem_filter.mpr ⟨hp2, by simp [hpne]⟩, hbit⟩
      · exact Or.inr (Or.inl ⟨p, hp, hbit⟩)
    · let ps := hitE.map Prod.snd
      have hps_ne : ps ≠ [] := by simp [ps, hhit]
      have hps_mem : ∀ p ∈ ps, p ∈ D2.P := by
        intro p hp
        obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hp
        exact (hM2_clean' pair (List.mem_filter.mp hpair).1).2.1
      obtain ⟨D3, pU, hsub23, hpU, hcard3, hbitU⟩ := addPureList D2 ps hps_ne hps_mem
      have he0_clean : e0 &&& pU &&& x2Val = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.testBit_and, Nat.zero_testBit]
        cases he1 : e0.testBit i
        · simp
        · cases hp1 : pU.testBit i
          · simp
          · cases hx2 : x2Val.testBit i
            · simp
            · exfalso
              obtain ⟨p, hpps, hpi⟩ := (hbitU i).mp hp1
              obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hpps
              have hpairM := (List.mem_filter.mp hpair).1
              have hpair1 : pair.1 = e0 := by simpa using (List.mem_filter.mp hpair).2
              have hcl := (hM2_clean' pair hpairM).2.2
              have hb := congrArg (fun n => n.testBit i) hcl
              rw [hpair1] at hb; simp [Nat.testBit_and, he1, hpi, hx2] at hb
      refine ⟨D3, some pU, hsub23, ?_, ?_, ?_⟩
      · intro p hp; cases hp; exact ⟨hpU, he0_clean⟩
      · intro e
        rcases hcov2 e with ⟨pair, hp2, hbit⟩ | ⟨p, hp, hbit⟩
        · by_cases h1 : pair.1 = e0
          · have hpair_hit : pair ∈ hitE := List.mem_filter.mpr ⟨hp2, by simp [h1]⟩
            have hp_ps : pair.2 ∈ ps := List.mem_map.mpr ⟨pair, hpair_hit, rfl⟩
            simp only [Nat.testBit_and, Bool.and_eq_true] at hbit
            have hpU_e : pU.testBit e.val = true := (hbitU e.val).mpr ⟨pair.2, hp_ps, hbit.2⟩
            exact Or.inr (Or.inr ⟨pU, rfl, by simp [Nat.testBit_and, h1 ▸ hbit.1, hpU_e]⟩)
          · exact Or.inl ⟨pair, List.mem_filter.mpr ⟨hp2, by simp [h1]⟩, hbit⟩
        · exact Or.inr (Or.inl ⟨p, hp, hbit⟩)
      · have hps_len : ps.length = hitE.length := List.length_map _
        simp only [Option.isSome_some, ↓reduceIte]
        omega
  obtain ⟨D3, pE, hsub23, hpE_spec, hcov3, hcost3⟩ := hstepE
  -- Now D3 is a PureDag containing s1, s2, t1, t2, every pair in Mpure, pD (if some), pE (if some)!
  have hsub03 : D0.P ⊆ D3.P := hsub01.trans (hsub12.trans hsub23)
  have hs1_3 : s1 ∈ D3.P := hsub03 (Finset.mem_union_left _ hs1)
  have hs2_3 : s2 ∈ D3.P := hsub03 (Finset.mem_union_left _ hs2)
  have ht1_3 : t1 ∈ D3.P := hsub03 (Finset.mem_union_left _ ht1)
  have ht2_3 : t2 ∈ D3.P := hsub03 (Finset.mem_union_left _ ht2)
  -- Strip b40/b41 from d0 &&& p and e0 &&& p:
  have hd0_and_x2 : ∀ p, d0 &&& p &&& x2Val = 0 → s1 &&& s2 &&& p &&& x2Val = 0 := by
    intro p h
    rw [hx4_eq]
    apply and_x2_eq_zero_of_le _ h
    rw [← Nat.or_assoc, Nat.or_self]
  have he0_and_x2 : ∀ p, e0 &&& p &&& x2Val = 0 → t1 &&& t2 &&& p &&& x2Val = 0 := by
    intro p h
    rw [hx5_eq]
    apply and_x2_eq_zero_of_le _ h
    rw [← Nat.or_assoc, Nat.or_self]
  have hd0_bit_e : ∀ p (e : Fin 16), (d0 &&& p).testBit e.val = (s1 &&& s2 &&& p).testBit e.val := by
    intro p e
    rw [hx4_eq]
    simp only [d0, Nat.testBit_and, Nat.testBit_or]
    have hb : b40.testBit e.val = false := by rw [h_b40_bit e.val (by omega)]; simp; omega
    simp [hb]
  have he0_bit_e : ∀ p (e : Fin 16), (e0 &&& p).testBit e.val = (t1 &&& t2 &&& p).testBit e.val := by
    intro p e
    rw [hx5_eq]
    simp only [e0, Nat.testBit_and, Nat.testBit_or]
    have hb : b41.testBit e.val = false := by rw [h_b41_bit e.val (by omega)]; simp; omega
    simp [hb]
  -- Extract extraD (length ≤ |restSet|/2) for pD, and extraE (length ≤ |restSet|/2) for pE!
  have hexD : ∃ extraD : List (Fin 16 × Fin 16),
      2 * extraD.length ≤ (restSet D3).card ∧
      ∀ p, pD = some p → ∀ e₁ e₂ : Fin 16,
        (d0 &&& p).testBit e₁.val = true → (d0 &&& p).testBit e₂.val = true →
        conn (lamEdgeList D3 ++ extraD) e₁ e₂ := by
    cases hpD_eq : pD with
    | none => exact ⟨[], by simp, by simp⟩
    | some p =>
      obtain ⟨hp2, hcl2⟩ := hpD_spec p hpD_eq
      obtain ⟨ex, hlen, hcon⟩ := clean_triple_connected D3 hs1_3 hs2_3 (hsub23 hp2) (hd0_and_x2 p hcl2)
      refine ⟨ex, hlen, ?_⟩
      intro p' hp' e₁ e₂ he₁ he₂
      cases hp'
      rw [hd0_bit_e] at he₁ he₂
      exact hcon e₁ e₂ he₁ he₂
  have hexE : ∃ extraE : List (Fin 16 × Fin 16),
      2 * extraE.length ≤ (restSet D3).card ∧
      ∀ p, pE = some p → ∀ e₁ e₂ : Fin 16,
        (e0 &&& p).testBit e₁.val = true → (e0 &&& p).testBit e₂.val = true →
        conn (lamEdgeList D3 ++ extraE) e₁ e₂ := by
    cases hpE_eq : pE with
    | none => exact ⟨[], by simp, by simp⟩
    | some p =>
      obtain ⟨hp3, hcl3⟩ := hpE_spec p hpE_eq
      obtain ⟨ex, hlen, hcon⟩ := clean_triple_connected D3 ht1_3 ht2_3 hp3 (he0_and_x2 p hcl3)
      refine ⟨ex, hlen, ?_⟩
      intro p' hp' e₁ e₂ he₁ he₂
      cases hp'
      rw [he0_bit_e] at he₁ he₂
      exact hcon e₁ e₂ he₁ he₂
  obtain ⟨extraD, hlenD, hconD⟩ := hexD
  obtain ⟨extraE, hlenE, hconE⟩ := hexE
  let esAll : List (Fin 16 × Fin 16) := lamEdgeList D3 ++ extraD ++ extraE
  have hesAll_len : esAll.length ≤ (D3.P \ x1Set).card := by
    have hlr := lam_rest_card D3
    have hlam := lamEdgeList_len D3
    simp only [esAll, List.length_append]
    omega
  -- Pick one representative edge for each nonempty pair in Mpure, plus one for pD, one for pE!
  let repList : List (Fin 16) :=
    (Mpure.filterMap fun pair => (List.finRange 16).find? fun e => (pair.1 &&& pair.2).testBit e.val) ++
    optFindList pD (fun p e => (d0 &&& p).testBit e.val) ++
    optFindList pE (fun p e => (e0 &&& p).testBit e.val)
  have hrep_len : repList.length ≤ Mpure.length + (if pD.isSome then 1 else 0) + (if pE.isSome then 1 else 0) := by
    have h1 : (Mpure.filterMap fun pair => (List.finRange 16).find? fun e =>
        (pair.1 &&& pair.2).testBit e.val).length ≤ Mpure.length := List.length_filterMap_le _ _
    have h2 := optFindList_len pD (fun p e => (d0 &&& p).testBit e.val)
    have h3 := optFindList_len pE (fun p e => (e0 &&& p).testBit e.val)
    simp only [repList, List.length_append]
    omega
  let R : Finset (Fin 16) := repList.toFinset
  have hR_card : R.card ≤ repList.length := List.toFinset_card_le repList
  have hR_cov : ∀ e : Fin 16, ∃ r ∈ R, conn esAll e r := by
    intro e
    rcases hcov3 e with ⟨pair, hpm, hbit⟩ | ⟨p, hpD, hbit⟩ | ⟨p, hpE, hbit⟩
    · have hfind_ne : ((List.finRange 16).find? fun r => (pair.1 &&& pair.2).testBit r.val).isSome = true := by
        rw [List.find?_isSome]
        exact ⟨e, List.mem_finRange e, hbit⟩
      obtain ⟨r, hr_eq⟩ := Option.isSome_iff_exists.mp hfind_ne
      have hr_bit : (pair.1 &&& pair.2).testBit r.val = true :=
        @List.find?_some (Fin 16) (fun r => (pair.1 &&& pair.2).testBit r.val) _ _ hr_eq
      have hr_in : r ∈ R := by
        apply List.mem_toFinset.mpr
        apply List.mem_append_left
        apply List.mem_append_left
        exact List.mem_filterMap.mpr ⟨pair, hpm, hr_eq⟩
      have hpair_clean := hM2_clean' pair (List.mem_filter.mp hpm).1
      have hne_e0 : pair.1 ≠ e0 := by simpa using (List.mem_filter.mp hpm).2
      have hp1 : pair.1 ∈ D3.P := by
        rcases hpair_clean.1 with h | h
        · exact hsub23 h
        · simp only [Finset.mem_insert, Finset.notMem_empty, or_false] at h
          exact (hne_e0 h).elim
      have hp2 : pair.2 ∈ D3.P := hsub23 hpair_clean.2.1
      have hcon := clean_pair_connected D3 hp1 hp2 hpair_clean.2.2 e r hbit hr_bit
      exact ⟨r, hr_in, conn_mono (fun q hq => List.mem_append_left _ (List.mem_append_left _ hq)) hcon⟩
    · have hfind_ne : ((List.finRange 16).find? fun r => (d0 &&& p).testBit r.val).isSome = true := by
        rw [List.find?_isSome]; exact ⟨e, List.mem_finRange e, hbit⟩
      obtain ⟨r, hr_eq⟩ := Option.isSome_iff_exists.mp hfind_ne
      have hr_bit : (d0 &&& p).testBit r.val = true :=
        @List.find?_some (Fin 16) (fun r => (d0 &&& p).testBit r.val) _ _ hr_eq
      have hr_in : r ∈ R := by
        apply List.mem_toFinset.mpr
        apply List.mem_append_left
        apply List.mem_append_right
        exact mem_optFindList hpD hr_eq
      have hcon := hconD p hpD e r hbit hr_bit
      exact ⟨r, hr_in, conn_mono (fun q hq => List.mem_append_left _ hq) hcon⟩
    · have hfind_ne : ((List.finRange 16).find? fun r => (e0 &&& p).testBit r.val).isSome = true := by
        rw [List.find?_isSome]; exact ⟨e, List.mem_finRange e, hbit⟩
      obtain ⟨r, hr_eq⟩ := Option.isSome_iff_exists.mp hfind_ne
      have hr_bit : (e0 &&& p).testBit r.val = true :=
        @List.find?_some (Fin 16) (fun r => (e0 &&& p).testBit r.val) _ _ hr_eq
      have hr_in : r ∈ R := by
        apply List.mem_toFinset.mpr
        apply List.mem_append_right
        exact mem_optFindList hpE hr_eq
      have hcon := hconE p hpE e r hbit hr_bit
      have hsubE : ∀ q ∈ lamEdgeList D3 ++ extraE, q ∈ esAll := by
        intro q hq
        rcases List.mem_append.mp hq with h | h
        · exact List.mem_append_left _ (List.mem_append_left _ h)
        · exact List.mem_append_right _ h
      exact ⟨r, hr_in, conn_mono hsubE hcon⟩
  have h16 := cover_by_conn esAll R hR_cov
  simp only [Fintype.card_fin] at h16
  change 16 ≤ x7.card + (x6 \ x8).card
  omega


/-! ### Section 11: Five-Top Lower Bound (`5 ≤ x7.card`) -/

def starList : List ℕ := [3, 12, 48, 192, 772, 3088, 12352, 20608, 34056, 51201, 8738]
def adjList : List ℕ := [1536, 272, 1056, 192, 1282, 772, 1160, 584, 562, 417, 85]

def dirEdgeList : List (Fin 11 × Fin 11) :=
  [(0, 9), (9, 0), (0, 10), (10, 0), (1, 4), (4, 1), (1, 8), (8, 1), (2, 5), (5, 2), (2, 10), (10, 2), (3, 6), (6, 3), (3, 7), (7, 3), (4, 8), (8, 4), (4, 10), (10, 4), (5, 8), (8, 5), (5, 9), (9, 5), (6, 7), (7, 6), (6, 10), (10, 6), (7, 9), (9, 7), (8, 9), (9, 8)]

def triList : List (Fin 11 × Fin 11 × Fin 11) :=
  [(1, 4, 8), (1, 8, 4), (3, 6, 7), (3, 7, 6), (4, 1, 8), (4, 8, 1), (5, 8, 9), (5, 9, 8), (6, 3, 7), (6, 7, 3), (7, 3, 6), (7, 6, 3), (8, 1, 4), (8, 4, 1), (8, 5, 9), (8, 9, 5), (9, 5, 8), (9, 8, 5)]

private lemma h_starList_len : starList.length = 11 := by decide
private lemma h_adjList_len : adjList.length = 11 := by decide

private lemma h_starList_bit : ∀ (v : Fin 11) (e : Fin 16),
    (starList.getD v.val 0).testBit e.val = (vVal v).testBit e.val := by
  decide +kernel

private lemma h_starList_lt : ∀ v : Fin 11, starList.getD v.val 0 < 65536 := by
  decide +kernel

private lemma h_adjList_bit : ∀ (u v : Fin 11),
    (adjList.getD u.val 0).testBit v.val = adj u v := by
  decide +kernel

private lemma h_dirEdge_mem : ∀ u v : Fin 11, adj u v = true → (u, v) ∈ dirEdgeList := by
  decide +kernel

private lemma h_tri_mem : ∀ z x y : Fin 11,
    adj z x = true → adj z y = true → adj x y = true → (z, x, y) ∈ triList := by
  decide +kernel

private lemma h_2047_bit : ∀ v : Fin 11, (2047 : ℕ).testBit v.val = true := by
  decide +kernel

private lemma h_65535_bit : ∀ e : Fin 16, (65535 : ℕ).testBit e.val = true := by
  decide +kernel

lemma testBit_zero_eq (m : ℕ) : m.testBit 0 = (m % 2 == 1) := by
  rw [Nat.testBit, Nat.shiftRight_zero, Nat.and_comm, Nat.and_one_is_mod]
  cases h : m % 2 with
  | zero => rfl
  | succ k =>
    have hk : k = 0 := by omega
    subst hk; rfl

lemma testBit_div2 (m k : ℕ) : (m / 2).testBit k = m.testBit (k + 1) := by
  rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    Nat.pow_succ', ← Nat.div_div_eq_div_mul]

lemma testBit_one_shl (k i : ℕ) : (1 <<< k).testBit i = decide (k = i) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hki : k ≤ i
  · by_cases heq : k = i
    · subst heq; simp
    · have hgt : 1 ≤ i - k := by omega
      have h1 : (1 : ℕ).testBit (i - k) = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ 1 ≤ 2 ^ (i - k) := Nat.pow_le_pow_right (by omega) hgt
        omega
      simp [hki, heq, h1]
  · have hne : k ≠ i := by omega
    simp [hki, hne]

def subMask (a b : ℕ) : Bool := (a &&& b) == a

lemma subMask_iff {a b : ℕ} :
    subMask a b = true ↔ ∀ i, a.testBit i = true → b.testBit i = true := by
  simp only [subMask, beq_iff_eq]
  constructor
  · intro h i ha
    have hi := congrArg (fun n => n.testBit i) h
    rw [Nat.testBit_and, ha, Bool.true_and] at hi
    exact hi
  · intro h
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_and]
    cases ha : a.testBit i
    · simp
    · simp [h i ha]

lemma subMask_trans {a b c : ℕ} (h1 : subMask a b = true) (h2 : subMask b c = true) :
    subMask a c = true :=
  subMask_iff.mpr fun i ha => subMask_iff.mp h2 i (subMask_iff.mp h1 i ha)

def edgeOfMaskGo : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: ss, m =>
    if m == 0 then 0
    else (if m % 2 == 1 then s else 0) ||| edgeOfMaskGo ss (m / 2)

def edgeOfMask (m : ℕ) : ℕ := edgeOfMaskGo starList m

lemma edgeOfMaskGo_testBit : ∀ (ss : List ℕ) (m i : ℕ),
    (edgeOfMaskGo ss m).testBit i = true ↔
      ∃ k < ss.length, m.testBit k = true ∧ (ss.getD k 0).testBit i = true := by
  intro ss
  induction ss with
  | nil => intro m i; simp [edgeOfMaskGo]
  | cons s ss ih =>
    intro m i
    simp only [edgeOfMaskGo]
    by_cases hm : m = 0
    · subst hm; simp
    · have hm' : (m == 0) = false := beq_false_of_ne hm
      rw [hm']; simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_or, Bool.or_eq_true]
      constructor
      · rintro (h0 | hrest)
        · by_cases hodd : m % 2 = 1
          · refine ⟨0, Nat.zero_lt_succ _, ?_, ?_⟩
            · rw [testBit_zero_eq]; simp [hodd]
            · simp only [hodd, beq_self_eq_true, ↓reduceIte] at h0; simpa using h0
          · have : (m % 2 == 1) = false := beq_false_of_ne hodd
            simp [this] at h0
        · obtain ⟨k, hk, hmk, hsk⟩ := (ih (m / 2) i).mp hrest
          refine ⟨k + 1, Nat.succ_lt_succ hk, ?_, ?_⟩
          · rw [← testBit_div2]; exact hmk
          · simpa using hsk
      · rintro ⟨k, hk, hmk, hsk⟩
        cases k with
        | zero =>
          left
          rw [testBit_zero_eq] at hmk
          simp only [hmk, ↓reduceIte]
          simpa using hsk
        | succ k' =>
          right
          rw [ih]
          refine ⟨k', Nat.lt_of_succ_lt_succ hk, ?_, ?_⟩
          · rw [testBit_div2]; exact hmk
          · simpa using hsk

lemma edgeOfMask_testBit (m : ℕ) (e : Fin 16) :
    (edgeOfMask m).testBit e.val = true ↔
      ∃ v : Fin 11, m.testBit v.val = true ∧ (vVal v).testBit e.val = true := by
  rw [edgeOfMask, edgeOfMaskGo_testBit, h_starList_len]
  constructor
  · rintro ⟨k, hk, hmk, hsk⟩
    refine ⟨⟨k, hk⟩, hmk, ?_⟩
    rw [← h_starList_bit ⟨k, hk⟩ e]; exact hsk
  · rintro ⟨v, hmv, hvv⟩
    refine ⟨v.val, v.isLt, hmv, ?_⟩
    rw [h_starList_bit v e]; exact hvv

lemma edgeOfMask_testBit_ge (m : ℕ) {i : ℕ} (hi : 16 ≤ i) :
    (edgeOfMask m).testBit i = false := by
  by_contra h
  have ht : (edgeOfMask m).testBit i = true := by cases h' : (edgeOfMask m).testBit i <;> simp_all
  obtain ⟨k, hk, _, hsk⟩ := (edgeOfMaskGo_testBit starList m i).mp ht
  rw [h_starList_len] at hk
  have hlt := h_starList_lt ⟨k, hk⟩
  have hpow : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
  have hf : (starList.getD k 0).testBit i = false :=
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : starList.getD k 0 < 2 ^ 16) hpow)
  rw [List.getD_eq_getElem?_getD] at hf
  simp [hf] at hsk

def pureMaskNat (m : ℕ) : ℕ := edgeOfMaskGo x1List m

private lemma h_x1List_len : x1List.length = 11 := by decide

lemma pureMaskNat_testBit (m i : ℕ) :
    (pureMaskNat m).testBit i = true ↔
      ∃ v : Fin 11, m.testBit v.val = true ∧ (vVal v).testBit i = true := by
  rw [pureMaskNat, edgeOfMaskGo_testBit, h_x1List_len]
  constructor
  · rintro ⟨k, hk, hmk, hsk⟩; exact ⟨⟨k, hk⟩, hmk, hsk⟩
  · rintro ⟨v, hmv, hvv⟩; exact ⟨v.val, v.isLt, hmv, hvv⟩

def maskOfList : List (Fin 11) → ℕ
  | [] => 0
  | v :: vs => (1 <<< v.val) ||| maskOfList vs

lemma maskOfList_testBit (l : List (Fin 11)) (i : ℕ) :
    (maskOfList l).testBit i = true ↔ ∃ v ∈ l, v.val = i := by
  induction l with
  | nil => simp [maskOfList]
  | cons v vs ih =>
    simp only [maskOfList, Nat.testBit_or, Bool.or_eq_true, testBit_one_shl, decide_eq_true_eq,
      ih, List.mem_cons]
    constructor
    · rintro (h | ⟨w, hw, rfl⟩)
      · exact ⟨v, Or.inl rfl, h⟩
      · exact ⟨w, Or.inr hw, rfl⟩
    · rintro ⟨w, rfl | hw, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨w, hw, rfl⟩

def finsetMask (S : Finset (Fin 11)) : ℕ :=
  maskOfList ((List.finRange 11).filter (fun v => decide (v ∈ S)))

lemma finsetMask_testBit (S : Finset (Fin 11)) (i : ℕ) :
    (finsetMask S).testBit i = true ↔ ∃ v : Fin 11, v ∈ S ∧ v.val = i := by
  rw [finsetMask, maskOfList_testBit]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, of_decide_eq_true (List.mem_filter.mp hv).2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, List.mem_filter.mpr ⟨List.mem_finRange v, decide_eq_true hv⟩, rfl⟩

lemma finsetMask_testBit_fin (S : Finset (Fin 11)) (v : Fin 11) :
    (finsetMask S).testBit v.val = decide (v ∈ S) := by
  cases h : (finsetMask S).testBit v.val
  · symm; rw [decide_eq_false_iff_not]
    intro hv
    have := (finsetMask_testBit S v.val).mpr ⟨v, hv, rfl⟩
    simp [h] at this
  · symm; rw [decide_eq_true_eq]
    obtain ⟨w, hw, hvw⟩ := (finsetMask_testBit S v.val).mp h
    have : w = v := Fin.ext hvw
    subst this; exact hw

lemma finsetMask_sub_2047 (S : Finset (Fin 11)) : subMask (finsetMask S) 2047 = true := by
  rw [subMask_iff]; intro i hi
  obtain ⟨v, _, rfl⟩ := (finsetMask_testBit S i).mp hi
  exact h_2047_bit v

def cvNatGo : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | v :: vs, d, idx =>
    (if (v &&& d &&& x2Val) == 0 then 1 <<< idx else 0) ||| cvNatGo vs d (idx + 1)

def cvNat (d : ℕ) : ℕ := cvNatGo x1List d 0

lemma cvNatGo_testBit : ∀ (vs : List ℕ) (d idx i : ℕ),
    (cvNatGo vs d idx).testBit i = true ↔
      ∃ k < vs.length, idx + k = i ∧ (vs.getD k 0 &&& d &&& x2Val) = 0 := by
  intro vs
  induction vs with
  | nil => intro d idx i; simp [cvNatGo]
  | cons v vs ih =>
    intro d idx i
    simp only [cvNatGo, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (h0 | ⟨k, hk, hki, hzk⟩)
      · by_cases hz : (v &&& d &&& x2Val) = 0
        · simp only [hz, beq_self_eq_true, ↓reduceIte, testBit_one_shl, decide_eq_true_eq] at h0
          exact ⟨0, Nat.zero_lt_succ _, by omega, by simpa using hz⟩
        · have : ((v &&& d &&& x2Val) == 0) = false := beq_false_of_ne hz
          simp [this] at h0
      · exact ⟨k + 1, Nat.succ_lt_succ hk, by omega, by simpa using hzk⟩
    · rintro ⟨k, hk, hki, hzk⟩
      cases k with
      | zero =>
        left
        have hz : (v &&& d &&& x2Val) = 0 := by simpa using hzk
        simp only [hz, beq_self_eq_true, ↓reduceIte, testBit_one_shl, decide_eq_true_eq]
        omega
      | succ k' =>
        right
        exact ⟨k', Nat.lt_of_succ_lt_succ hk, by omega, by simpa using hzk⟩

lemma cvNat_testBit (d i : ℕ) :
    (cvNat d).testBit i = true ↔ ∃ v : Fin 11, v.val = i ∧ (vVal v &&& d &&& x2Val) = 0 := by
  rw [cvNat, cvNatGo_testBit, h_x1List_len]
  constructor
  · rintro ⟨k, hk, hki, hz⟩; exact ⟨⟨k, hk⟩, by simpa using hki, hz⟩
  · rintro ⟨v, rfl, hz⟩; exact ⟨v.val, v.isLt, by simp, hz⟩

lemma cvNat_testBit_fin (d : ℕ) (v : Fin 11) :
    (cvNat d).testBit v.val = true ↔ (vVal v &&& d &&& x2Val) = 0 := by
  rw [cvNat_testBit]
  constructor
  · rintro ⟨w, hvw, hz⟩; have : w = v := Fin.ext hvw; subst this; exact hz
  · intro hz; exact ⟨v, rfl, hz⟩

def hasTwoBits (m : ℕ) : Bool := (m != 0) && ((m &&& (m - 1)) != 0)

lemma hasTwoBits_of_two {m u v : ℕ} (hne : u ≠ v)
    (hu : m.testBit u = true) (hv : m.testBit v = true) : hasTwoBits m = true := by
  wlog huv : u < v generalizing u v
  · exact this hne.symm hv hu (by omega)
  have hm0 : m ≠ 0 := by intro h; subst h; simp at hv
  have hr_pos : 1 ≤ m % 2 ^ v := by
    have hdiv : (m % 2 ^ v).testBit u = true := by
      rw [Nat.testBit_mod_two_pow]
      simp [huv, hu]
    by_contra h0
    have hz : m % 2 ^ v = 0 := by omega
    rw [hz] at hdiv; simp at hdiv
  have hdiv_eq : (m - 1) / 2 ^ v = m / 2 ^ v := by
    have hmod := Nat.div_add_mod m (2 ^ v)
    have hlt : m % 2 ^ v < 2 ^ v := Nat.mod_lt m (Nat.two_pow_pos v)
    have h1 : m - 1 = 2 ^ v * (m / 2 ^ v) + (m % 2 ^ v - 1) := by omega
    rw [h1, Nat.mul_add_div (Nat.two_pow_pos v)]
    have h2 : (m % 2 ^ v - 1) / 2 ^ v = 0 := Nat.div_eq_of_lt (by omega)
    omega
  have hm1_v : (m - 1).testBit v = true := by
    have : (m - 1).testBit v = m.testBit v := by
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, hdiv_eq]
    rw [this, hv]
  have hand_ne : m &&& (m - 1) ≠ 0 := by
    intro hz
    have := congrArg (fun n => n.testBit v) hz
    rw [Nat.testBit_and, hv, hm1_v] at this; simp at this
  simp only [hasTwoBits, Bool.and_eq_true, bne_iff_ne]
  exact ⟨hm0, hand_ne⟩

def nbList (v : Fin 11) : List (Fin 11) := (List.finRange 11).filter (fun w => adj v w)

private lemma h_nbList_len : ∀ v : Fin 11, (nbList v).length ≤ 4 := by decide +kernel

def pickBits : List (Fin 11) → ℕ → ℕ
  | [], _ => 0
  | v :: rest, k => (if k % 2 == 1 then 1 <<< v.val else 0) ||| pickBits rest (k / 2)

lemma exists_pickBits_go (S : Finset (Fin 11)) : ∀ (l : List (Fin 11)),
    l.Nodup → (∀ v ∈ S, v ∈ l) →
    ∃ k < 2 ^ l.length, ∀ i, (pickBits l k).testBit i = true ↔ ∃ v : Fin 11, v ∈ S ∧ v.val = i := by
  intro l
  induction l generalizing S with
  | nil =>
    intro _ hsub
    refine ⟨0, by decide, fun i => ?_⟩
    simp only [pickBits, Nat.zero_testBit, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro v hv; exact (List.not_mem_nil (hsub v hv)).elim
  | cons a rest ih =>
    intro hnd hsub
    have ha_not : a ∉ rest := (List.nodup_cons.mp hnd).1
    have hnd_rest : rest.Nodup := (List.nodup_cons.mp hnd).2
    let S' := S.erase a
    have hsub' : ∀ v ∈ S', v ∈ rest := by
      intro v hv
      have hne : v ≠ a := (Finset.mem_erase.mp hv).1
      rcases List.mem_cons.mp (hsub v (Finset.mem_erase.mp hv).2) with rfl | h
      · exact (hne rfl).elim
      · exact h
    obtain ⟨k', hk', hbit'⟩ := ih S' hnd_rest hsub'
    let b : ℕ := if a ∈ S then 1 else 0
    let k : ℕ := b + 2 * k'
    have hb_le : b ≤ 1 := by dsimp only [b]; split_ifs <;> omega
    have hk_lt : k < 2 ^ (a :: rest).length := by
      dsimp only [k]; simp only [List.length_cons, Nat.pow_succ]; omega
    have hk_mod : k % 2 = b := by
      dsimp only [k, b]; split_ifs <;> omega
    have hk_div : k / 2 = k' := by
      dsimp only [k, b]; split_ifs <;> omega
    refine ⟨k, hk_lt, fun i => ?_⟩
    simp only [pickBits, hk_mod, hk_div, Nat.testBit_or, Bool.or_eq_true, hbit']
    constructor
    · rintro (h0 | ⟨v, hv, rfl⟩)
      · by_cases haS : a ∈ S
        · simp only [b, haS, ↓reduceIte, beq_self_eq_true, testBit_one_shl, decide_eq_true_eq] at h0
          exact ⟨a, haS, h0⟩
        · simp [b, haS] at h0
      · exact ⟨v, (Finset.mem_erase.mp hv).2, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      by_cases hva : v = a
      · subst hva; left
        simp [b, hv, testBit_one_shl]
      · right
        exact ⟨v, Finset.mem_erase.mpr ⟨hva, hv⟩, rfl⟩

lemma exists_pickBits (x : Fin 11) (S : Finset (Fin 11)) (hsub : ∀ v ∈ S, adj x v = true) :
    ∃ k : Fin 16, finsetMask S = pickBits (nbList x) k.val := by
  have hnd : (nbList x).Nodup := (List.nodup_finRange 11).filter _
  have hmem : ∀ v ∈ S, v ∈ nbList x := fun v hv =>
    List.mem_filter.mpr ⟨List.mem_finRange v, hsub v hv⟩
  obtain ⟨k, hk_lt, hbit⟩ := exists_pickBits_go S (nbList x) hnd hmem
  have hpow : 2 ^ (nbList x).length ≤ 16 := by
    have := h_nbList_len x
    exact Nat.pow_le_pow_right (by omega) this
  refine ⟨⟨k, Nat.lt_of_lt_of_le hk_lt hpow⟩, ?_⟩
  apply Nat.eq_of_testBit_eq; intro i
  cases h1 : (finsetMask S).testBit i
  · symm; by_contra h2
    have ht : (pickBits (nbList x) k).testBit i = true := by
      cases h' : (pickBits (nbList x) k).testBit i <;> simp_all
    have := (finsetMask_testBit S i).mpr ((hbit i).mp ht)
    simp [h1] at this
  · symm; exact (hbit i).mpr ((finsetMask_testBit S i).mp h1)

def coarseArr : Array (ℕ × ℕ) := #[
  (58899, 2047), (58892, 2047), (9776, 2047), (58048, 2047), (59140, 2047),
  (52240, 2047), (62016, 2047), (61568, 2047), (50952, 2047), (52225, 2047),
  (8738, 2047), (59939, 1953), (8755, 1141), (52273, 1957), (34572, 1842),
  (8998, 1367), (36120, 788), (36120, 562), (28864, 1736), (12898, 1245),
  (55425, 1001), (52489, 947), (36120, 304), (51203, 853), (3120, 501),
  (8754, 1796), (806, 1584), (8994, 1586), (1596, 1328), (33295, 1808),
  (3344, 1314), (52481, 1955), (34072, 1312), (12386, 1632), (12834, 1640),
  (24801, 1760), (8258, 1728), (22657, 1924), (55297, 1932), (18560, 964),
  (34057, 1792), (35072, 1798)]

def coarseList : List (ℕ × ℕ) := coarseArr.toList

def domByCoarse (ec cv : ℕ) : Bool :=
  coarseList.any (fun m => subMask ec m.1 && subMask cv m.2)

lemma domByCoarse_spec {ec cv : ℕ} (h : domByCoarse ec cv = true) :
    ∃ idx < 42,
      subMask ec (coarseArr.getD idx (0, 0)).1 = true ∧
      subMask cv (coarseArr.getD idx (0, 0)).2 = true := by
  rw [domByCoarse, List.any_eq_true] at h
  obtain ⟨m, hm, hsub⟩ := h
  rw [Bool.and_eq_true] at hsub
  obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hm
  have hlen : coarseList.length = 42 := by decide
  have hsz : idx < coarseArr.size := by simpa [coarseList] using hidx
  have hget : coarseArr.getD idx (0, 0) = coarseList[idx]'hidx := by
    simp [Array.getD, hsz, coarseList]
  exact ⟨idx, by omega, hget.symm ▸ hsub.1, hget.symm ▸ hsub.2⟩

private lemma h_dom_S :
    (List.finRange 11).all (fun v => domByCoarse (starList.getD v.val 0) 2047) = true := by
  decide +kernel

private lemma h_dom_Z1 :
    dirEdgeList.all (fun p =>
      (List.finRange 16).all (fun kA =>
        let mA := pickBits (nbList p.2) kA.val
        if mA.testBit p.1.val then
          let d := pureMaskNat mA &&& (vVal p.1 ||| vVal p.2)
          let cv := cvNat d
          domByCoarse (d &&& edgeOfMask cv) cv
        else true)) = true := by
  decide +kernel

private lemma h_dom_Z2 :
    triList.all (fun t =>
      (List.finRange 16).all (fun kA =>
        let mA := pickBits (nbList t.2.1) kA.val
        if mA.testBit t.1.val && mA.testBit t.2.2.val then
          (List.finRange 16).all (fun kB =>
            let mB := pickBits (nbList t.2.2) kB.val
            if mB.testBit t.1.val && mB.testBit t.2.1.val && ((mA &&& mB) == (1 <<< t.1.val)) then
              let d := pureMaskNat mA &&& pureMaskNat mB
              let cv := cvNat d
              domByCoarse (d &&& edgeOfMask cv) cv
            else true)
        else true)) = true := by
  decide +kernel

private lemma h_dom_XY :
    dirEdgeList.all (fun p =>
      (List.finRange 16).all (fun kA =>
        let mA := pickBits (nbList p.1) kA.val
        if mA.testBit p.2.val then
          (List.finRange 16).all (fun kB =>
            let mB := pickBits (nbList p.2) kB.val
            if mB.testBit p.1.val && ((mA &&& mB) == 0) then
              let d := pureMaskNat mA &&& pureMaskNat mB
              if (d &&& x2Val) != 0 then
                let cv := cvNat d
                domByCoarse (d &&& edgeOfMask cv) cv
              else true
            else true)
        else true)) = true := by
  decide +kernel

lemma dirty_dominated_by_coarse (D : PureDag) (s1 s2 : ℕ)
    (hs1 : s1 ∈ D.P) (hs2 : s2 ∈ D.P) (hdirty : (s1 &&& s2) &&& x2Val ≠ 0) :
    let d := s1 &&& s2
    let cv := cvNat d
    ∃ idx < 42,
      subMask (d &&& edgeOfMask cv) (coarseArr.getD idx (0, 0)).1 = true ∧
      subMask cv (coarseArr.getD idx (0, 0)).2 = true := by
  intro d cv
  let SA := seedSet D s1
  let SB := seedSet D s2
  let CV : Finset (Fin 11) := Finset.univ.filter (fun v : Fin 11 => (vVal v &&& d &&& x2Val) = 0)
  have hs1_eq : s1 = pureMaskNat (finsetMask SA) := by
    apply Nat.eq_of_testBit_eq; intro i
    cases h : s1.testBit i
    · symm; by_contra h2
      have ht : (pureMaskNat (finsetMask SA)).testBit i = true := by
        cases h' : (pureMaskNat (finsetMask SA)).testBit i <;> simp_all
      obtain ⟨v, hmv, hvv⟩ := (pureMaskNat_testBit _ _).mp ht
      rw [finsetMask_testBit_fin, decide_eq_true_eq] at hmv
      have := (seedSet_testBit D s1 hs1 i).mpr ⟨v, hmv, hvv⟩
      simp [h] at this
    · symm; rw [pureMaskNat_testBit]
      obtain ⟨v, hv, hvv⟩ := (seedSet_testBit D s1 hs1 i).mp h
      exact ⟨v, by rw [finsetMask_testBit_fin, decide_eq_true hv], hvv⟩
  have hs2_eq : s2 = pureMaskNat (finsetMask SB) := by
    apply Nat.eq_of_testBit_eq; intro i
    cases h : s2.testBit i
    · symm; by_contra h2
      have ht : (pureMaskNat (finsetMask SB)).testBit i = true := by
        cases h' : (pureMaskNat (finsetMask SB)).testBit i <;> simp_all
      obtain ⟨v, hmv, hvv⟩ := (pureMaskNat_testBit _ _).mp ht
      rw [finsetMask_testBit_fin, decide_eq_true_eq] at hmv
      have := (seedSet_testBit D s2 hs2 i).mpr ⟨v, hmv, hvv⟩
      simp [h] at this
    · symm; rw [pureMaskNat_testBit]
      obtain ⟨v, hv, hvv⟩ := (seedSet_testBit D s2 hs2 i).mp h
      exact ⟨v, by rw [finsetMask_testBit_fin, decide_eq_true hv], hvv⟩
  have hcv_eq : cv = finsetMask CV := by
    apply Nat.eq_of_testBit_eq; intro i
    cases h : cv.testBit i
    · symm; by_contra h2
      have ht : (finsetMask CV).testBit i = true := by
        cases h' : (finsetMask CV).testBit i <;> simp_all
      obtain ⟨v, hv, rfl⟩ := (finsetMask_testBit CV i).mp ht
      have hz := (Finset.mem_filter.mp hv).2
      have := (cvNat_testBit_fin d v).mpr hz
      simp [cv, h] at this
    · symm; rw [finsetMask_testBit]
      obtain ⟨v, rfl, hz⟩ := (cvNat_testBit d i).mp h
      exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hz⟩, rfl⟩
  -- Helper: any vertex in SA ∩ SB cannot be in CV!
  have hdisj_inter : ∀ z : Fin 11, z ∈ SA → z ∈ SB → z ∉ CV := by
    intro z hzA hzB hzCV
    have hz := (Finset.mem_filter.mp hzCV).2
    obtain ⟨m, hm16, hzm, _⟩ := h_nonedge_bad z z (h_adj_irrefl z)
    have h1 : s1.testBit m.val = true := (seedSet_testBit D s1 hs1 m.val).mpr ⟨z, hzA, hzm⟩
    have h2 : s2.testBit m.val = true := (seedSet_testBit D s2 hs2 m.val).mpr ⟨z, hzB, hzm⟩
    have hx2 : x2Val.testBit m.val = true := by rw [h_x2_bit m]; simp [hm16]
    have h0 := congrArg (fun n => n.testBit m.val) hz
    simp only [d, Nat.testBit_and, Nat.zero_testBit, hzm, h1, h2, hx2] at h0
    simp at h0
  -- Helper: if u ∈ SA and v ∈ SB ∩ CV (or u ∈ SB and v ∈ SA ∩ CV, or u ∈ CV and v ∈ SA ∩ SB), then adj u v = true!
  have hadj_A_BCV : ∀ u v : Fin 11, u ∈ SA → v ∈ SB → v ∈ CV → adj u v = true := by
    intro u v hu hvB hvCV
    by_contra hna
    have hfalse : adj u v = false := by cases h' : adj u v <;> simp_all
    obtain ⟨m, hm16, hum, hvm⟩ := h_nonedge_bad u v hfalse
    have hz := (Finset.mem_filter.mp hvCV).2
    have h1 : s1.testBit m.val = true := (seedSet_testBit D s1 hs1 m.val).mpr ⟨u, hu, hum⟩
    have h2 : s2.testBit m.val = true := (seedSet_testBit D s2 hs2 m.val).mpr ⟨v, hvB, hvm⟩
    have hx2 : x2Val.testBit m.val = true := by rw [h_x2_bit m]; simp [hm16]
    have h0 := congrArg (fun n => n.testBit m.val) hz
    simp only [d, Nat.testBit_and, Nat.zero_testBit, hvm, h1, h2, hx2] at h0
    simp at h0
  have hadj_B_ACV : ∀ u v : Fin 11, u ∈ SB → v ∈ SA → v ∈ CV → adj u v = true := by
    intro u v hu hvA hvCV
    by_contra hna
    have hfalse : adj u v = false := by cases h' : adj u v <;> simp_all
    obtain ⟨m, hm16, hum, hvm⟩ := h_nonedge_bad u v hfalse
    have hz := (Finset.mem_filter.mp hvCV).2
    have h1 : s1.testBit m.val = true := (seedSet_testBit D s1 hs1 m.val).mpr ⟨v, hvA, hvm⟩
    have h2 : s2.testBit m.val = true := (seedSet_testBit D s2 hs2 m.val).mpr ⟨u, hu, hum⟩
    have hx2 : x2Val.testBit m.val = true := by rw [h_x2_bit m]; simp [hm16]
    have h0 := congrArg (fun n => n.testBit m.val) hz
    simp only [d, Nat.testBit_and, Nat.zero_testBit, hvm, h1, h2, hx2] at h0
    simp at h0
  have hadj_CV_AB : ∀ u v : Fin 11, u ∈ CV → v ∈ SA → v ∈ SB → adj u v = true := by
    intro u v hu hvA hvB
    by_contra hna
    have hfalse : adj u v = false := by cases h' : adj u v <;> simp_all
    obtain ⟨m, hm16, hum, hvm⟩ := h_nonedge_bad u v hfalse
    have hz := (Finset.mem_filter.mp hu).2
    have h1 : s1.testBit m.val = true := (seedSet_testBit D s1 hs1 m.val).mpr ⟨v, hvA, hvm⟩
    have h2 : s2.testBit m.val = true := (seedSet_testBit D s2 hs2 m.val).mpr ⟨v, hvB, hvm⟩
    have hx2 : x2Val.testBit m.val = true := by rw [h_x2_bit m]; simp [hm16]
    have h0 := congrArg (fun n => n.testBit m.val) hz
    simp only [d, Nat.testBit_and, Nat.zero_testBit, hum, h1, h2, hx2] at h0
    simp at h0
  -- Helper: single-star domination closes immediately via h_dom_S!
  have hstar_close : ∀ v : Fin 11, subMask (d &&& edgeOfMask cv) (starList.getD v.val 0) = true →
      ∃ idx < 42, subMask (d &&& edgeOfMask cv) (coarseArr.getD idx (0, 0)).1 = true ∧
        subMask cv (coarseArr.getD idx (0, 0)).2 = true := by
    intro v hsub
    have hdS := List.all_eq_true.mp h_dom_S v (List.mem_finRange v)
    obtain ⟨idx, hidx, h1, h2⟩ := domByCoarse_spec hdS
    refine ⟨idx, hidx, subMask_trans hsub h1, subMask_trans ?_ h2⟩
    rw [hcv_eq]; exact finsetMask_sub_2047 CV
  -- Helper: every edge bit i of (d &&& edgeOfMask cv) has i < 16 and endpoints hitting SA, SB, CV!
  have hedge_info : ∀ i, (d &&& edgeOfMask cv).testBit i = true →
      ∃ e : Fin 16, e.val = i ∧
        ((edgeEnds e).1 ∈ SA ∨ (edgeEnds e).2 ∈ SA) ∧
        ((edgeEnds e).1 ∈ SB ∨ (edgeEnds e).2 ∈ SB) ∧
        ((edgeEnds e).1 ∈ CV ∨ (edgeEnds e).2 ∈ CV) := by
    intro i hi
    rw [Nat.testBit_and, Bool.and_eq_true] at hi
    have hi16 : i < 16 := by
      by_contra hge
      have := edgeOfMask_testBit_ge cv (by omega : 16 ≤ i)
      simp [this] at hi
    let e : Fin 16 := ⟨i, hi16⟩
    have h1 : s1.testBit e.val = true := by
      have := hi.1; rw [Nat.testBit_and, Bool.and_eq_true] at this; exact this.1
    have h2 : s2.testBit e.val = true := by
      have := hi.1; rw [Nat.testBit_and, Bool.and_eq_true] at this; exact this.2
    obtain ⟨v1, hv1A, hv1e⟩ := (seedSet_testBit D s1 hs1 e.val).mp h1
    obtain ⟨v2, hv2B, hv2e⟩ := (seedSet_testBit D s2 hs2 e.val).mp h2
    obtain ⟨v3, hv3cv, hv3e⟩ := (edgeOfMask_testBit cv e).mp hi.2
    rw [hcv_eq, finsetMask_testBit_fin, decide_eq_true_eq] at hv3cv
    rw [h_bit_edge v1 e, decide_eq_true_eq] at hv1e
    rw [h_bit_edge v2 e, decide_eq_true_eq] at hv2e
    rw [h_bit_edge v3 e, decide_eq_true_eq] at hv3e
    refine ⟨e, rfl, ?_, ?_, ?_⟩
    · rcases hv1e with rfl | rfl <;> [exact Or.inl hv1A; exact Or.inr hv1A]
    · rcases hv2e with rfl | rfl <;> [exact Or.inl hv2B; exact Or.inr hv2B]
    · rcases hv3e with rfl | rfl <;> [exact Or.inl hv3cv; exact Or.inr hv3cv]
  -- Helper: if every edge in d &&& edgeOfMask cv has an endpoint in a single vertex v, done!
  have hstar_of_hit : ∀ v : Fin 11,
      (∀ e : Fin 16, (d &&& edgeOfMask cv).testBit e.val = true →
        (edgeEnds e).1 = v ∨ (edgeEnds e).2 = v) →
      ∃ idx < 42, subMask (d &&& edgeOfMask cv) (coarseArr.getD idx (0, 0)).1 = true ∧
        subMask cv (coarseArr.getD idx (0, 0)).2 = true := by
    intro v hhit
    apply hstar_close v
    rw [subMask_iff]; intro i hi
    obtain ⟨e, rfl, _, _, _⟩ := hedge_info i hi
    rw [h_starList_bit v e, h_bit_edge v e, decide_eq_true_eq]
    rcases hhit e hi with h | h <;> [exact Or.inl h.symm; exact Or.inr h.symm]
  -- Case 0: SA.card ≤ 1 ∨ SB.card ≤ 1 ∨ CV.card ≤ 1
  by_cases hsmall : SA.card ≤ 1 ∨ SB.card ≤ 1 ∨ CV.card ≤ 1
  · rcases hsmall with hA1 | hB1 | hC1
    · rcases Finset.card_le_one_iff_subset_singleton.mp hA1 with ⟨v, hv⟩
      exact hstar_of_hit v fun e he => by
        obtain ⟨e', heq, hA, _, _⟩ := hedge_info e.val he
        have : e' = e := Fin.ext heq; subst this
        rcases hA with h | h
        · exact Or.inl (Finset.mem_singleton.mp (hv h))
        · exact Or.inr (Finset.mem_singleton.mp (hv h))
    · rcases Finset.card_le_one_iff_subset_singleton.mp hB1 with ⟨v, hv⟩
      exact hstar_of_hit v fun e he => by
        obtain ⟨e', heq, _, hB, _⟩ := hedge_info e.val he
        have : e' = e := Fin.ext heq; subst this
        rcases hB with h | h
        · exact Or.inl (Finset.mem_singleton.mp (hv h))
        · exact Or.inr (Finset.mem_singleton.mp (hv h))
    · rcases Finset.card_le_one_iff_subset_singleton.mp hC1 with ⟨v, hv⟩
      exact hstar_of_hit v fun e he => by
        obtain ⟨e', heq, _, _, hC⟩ := hedge_info e.val he
        have : e' = e := Fin.ext heq; subst this
        rcases hC with h | h
        · exact Or.inl (Finset.mem_singleton.mp (hv h))
        · exact Or.inr (Finset.mem_singleton.mp (hv h))
  -- Now 2 ≤ SA.card, 2 ≤ SB.card, 2 ≤ CV.card!
  have hAge2 : 2 ≤ SA.card := by omega
  have hBge2 : 2 ≤ SB.card := by omega
  have hCge2 : 2 ≤ CV.card := by omega
  let Z := SA ∩ SB
  let Y := SA ∩ CV
  let X := SB ∩ CV
  -- All three pairwise intersections have card ≤ 1 by C4-freeness!
  have hZ1 : Z.card ≤ 1 := by
    by_contra hgt
    obtain ⟨z1, hz1, z2, hz2, hneZ⟩ := Finset.one_lt_card.mp (by omega : 1 < Z.card)
    obtain ⟨c1, hc1, c2, hc2, hneC⟩ := Finset.one_lt_card.mp (by omega : 1 < CV.card)
    have h11 := hadj_CV_AB c1 z1 hc1 (Finset.mem_inter.mp hz1).1 (Finset.mem_inter.mp hz1).2
    have h12 := hadj_CV_AB c1 z2 hc1 (Finset.mem_inter.mp hz2).1 (Finset.mem_inter.mp hz2).2
    have h21 := hadj_CV_AB c2 z1 hc2 (Finset.mem_inter.mp hz1).1 (Finset.mem_inter.mp hz1).2
    have h22 := hadj_CV_AB c2 z2 hc2 (Finset.mem_inter.mp hz2).1 (Finset.mem_inter.mp hz2).2
    have := h_c4_free c1 c2 z1 z2 hneC hneZ h11 h12 h21
    simp [h22] at this
  have hY1 : Y.card ≤ 1 := by
    by_contra hgt
    obtain ⟨y1, hy1, y2, hy2, hneY⟩ := Finset.one_lt_card.mp (by omega : 1 < Y.card)
    obtain ⟨b1, hb1, b2, hb2, hneB⟩ := Finset.one_lt_card.mp (by omega : 1 < SB.card)
    have h11 := hadj_B_ACV b1 y1 hb1 (Finset.mem_inter.mp hy1).1 (Finset.mem_inter.mp hy1).2
    have h12 := hadj_B_ACV b1 y2 hb1 (Finset.mem_inter.mp hy2).1 (Finset.mem_inter.mp hy2).2
    have h21 := hadj_B_ACV b2 y1 hb2 (Finset.mem_inter.mp hy1).1 (Finset.mem_inter.mp hy1).2
    have h22 := hadj_B_ACV b2 y2 hb2 (Finset.mem_inter.mp hy2).1 (Finset.mem_inter.mp hy2).2
    have := h_c4_free b1 b2 y1 y2 hneB hneY h11 h12 h21
    simp [h22] at this
  have hX1 : X.card ≤ 1 := by
    by_contra hgt
    obtain ⟨x1, hx1, x2, hx2, hneX⟩ := Finset.one_lt_card.mp (by omega : 1 < X.card)
    obtain ⟨a1, ha1, a2, ha2, hneA⟩ := Finset.one_lt_card.mp (by omega : 1 < SA.card)
    have h11 := hadj_A_BCV a1 x1 ha1 (Finset.mem_inter.mp hx1).1 (Finset.mem_inter.mp hx1).2
    have h12 := hadj_A_BCV a1 x2 ha1 (Finset.mem_inter.mp hx2).1 (Finset.mem_inter.mp hx2).2
    have h21 := hadj_A_BCV a2 x1 ha2 (Finset.mem_inter.mp hx1).1 (Finset.mem_inter.mp hx1).2
    have h22 := hadj_A_BCV a2 x2 ha2 (Finset.mem_inter.mp hx2).1 (Finset.mem_inter.mp hx2).2
    have := h_c4_free a1 a2 x1 x2 hneA hneX h11 h12 h21
    simp [h22] at this
  -- Every edge in d &&& edgeOfMask cv has an endpoint in X ∪ Y ∪ Z!
  have hedge_XYZ : ∀ e : Fin 16, (d &&& edgeOfMask cv).testBit e.val = true →
      (edgeEnds e).1 ∈ X ∨ (edgeEnds e).1 ∈ Y ∨ (edgeEnds e).1 ∈ Z ∨
      (edgeEnds e).2 ∈ X ∨ (edgeEnds e).2 ∈ Y ∨ (edgeEnds e).2 ∈ Z := by
    intro e he
    obtain ⟨e', heq, hA, hB, hC⟩ := hedge_info e.val he
    have : e' = e := Fin.ext heq; subst this
    rcases hA with h1 | h2 <;> rcases hB with h3 | h4 <;> rcases hC with h5 | h6
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_inter.mpr ⟨h1, h3⟩)))
    · exact Or.inr (Or.inr (Or.inl (Finset.mem_inter.mpr ⟨h1, h3⟩)))
    · exact Or.inr (Or.inl (Finset.mem_inter.mpr ⟨h1, h5⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_inter.mpr ⟨h4, h6⟩))))
    · exact Or.inl (Finset.mem_inter.mpr ⟨h3, h5⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Finset.mem_inter.mpr ⟨h2, h6⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_inter.mpr ⟨h2, h4⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Finset.mem_inter.mpr ⟨h2, h4⟩)))))
  -- Case split on Z = ∅ vs Z = {z}!
  by_cases hZe : Z = ∅
  · by_cases hXe : X = ∅
    · by_cases hYe : Y = ∅
      · exact hstar_of_hit 0 fun e he => by
          rcases hedge_XYZ e he with h | h | h | h | h | h <;> simp [hXe, hYe, hZe] at h
      · obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
        have hYeq : Y = {y} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hy, fun w hw => Finset.card_le_one.mp hY1 w hw y hy⟩
        exact hstar_of_hit y fun e he => by
          rcases hedge_XYZ e he with h | h | h | h | h | h <;>
            simp [hXe, hZe, hYeq] at h
          · exact Or.inl h
          · exact Or.inr h
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hXe
      have hXeq : X = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hx, fun w hw => Finset.card_le_one.mp hX1 w hw x hx⟩
      by_cases hYe : Y = ∅
      · exact hstar_of_hit x fun e he => by
          rcases hedge_XYZ e he with h | h | h | h | h | h <;>
            simp [hYe, hZe, hXeq] at h
          · exact Or.inl h
          · exact Or.inr h
      · -- Type XY! Z = ∅, X = {x}, Y = {y}!
        obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
        have hxB : x ∈ SB := (Finset.mem_inter.mp hx).1
        have hxCV : x ∈ CV := (Finset.mem_inter.mp hx).2
        have hyA : y ∈ SA := (Finset.mem_inter.mp hy).1
        have hyCV : y ∈ CV := (Finset.mem_inter.mp hy).2
        have hxy : adj x y = true := by
          rw [h_adj_symm]; exact hadj_A_BCV y x hyA hxB hxCV
        have hSA_nb : ∀ a ∈ SA, adj x a = true := fun a ha => by
          rw [h_adj_symm]; exact hadj_A_BCV a x ha hxB hxCV
        have hSB_nb : ∀ b ∈ SB, adj y b = true := fun b hb => by
          rw [h_adj_symm]; exact hadj_B_ACV b y hb hyA hyCV
        obtain ⟨kA, hkA⟩ := exists_pickBits x SA hSA_nb
        obtain ⟨kB, hkB⟩ := exists_pickBits y SB hSB_nb
        have hmem_de : (x, y) ∈ dirEdgeList := h_dirEdge_mem x y hxy
        have hdom := List.all_eq_true.mp h_dom_XY (x, y) hmem_de
        have hdom1 := List.all_eq_true.mp hdom kA (List.mem_finRange kA)
        have hmA_y : (pickBits (nbList x) kA.val).testBit y.val = true := by
          rw [← hkA, finsetMask_testBit_fin, decide_eq_true hyA]
        simp only [hmA_y, ↓reduceIte] at hdom1
        have hdom2 := List.all_eq_true.mp hdom1 kB (List.mem_finRange kB)
        have hmB_x : (pickBits (nbList y) kB.val).testBit x.val = true := by
          rw [← hkB, finsetMask_testBit_fin, decide_eq_true hxB]
        have hmAB0 : (pickBits (nbList x) kA.val &&& pickBits (nbList y) kB.val) = 0 := by
          rw [← hkA, ← hkB]
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and, Nat.zero_testBit]
          cases h1 : (finsetMask SA).testBit i
          · simp
          · obtain ⟨v, hvA, rfl⟩ := (finsetMask_testBit SA i).mp h1
            have hvnotB : v ∉ SB := fun hvB => by
              have : v ∈ Z := Finset.mem_inter.mpr ⟨hvA, hvB⟩
              simp [hZe] at this
            rw [finsetMask_testBit_fin, decide_eq_false hvnotB]; simp
        have hd_eq : pureMaskNat (pickBits (nbList x) kA.val) &&&
            pureMaskNat (pickBits (nbList y) kB.val) = d := by
          rw [← hkA, ← hkB, ← hs1_eq, ← hs2_eq]
        simp only [hmB_x, hmAB0, beq_self_eq_true, Bool.and_self, ↓reduceIte, hd_eq] at hdom2
        have hne0 : ((d &&& x2Val) != 0) = true := bne_iff_ne.mpr hdirty
        simp only [hne0, ↓reduceIte] at hdom2
        exact domByCoarse_spec hdom2
  · -- Z = {z}!
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hZe
    have hZeq : Z = {z} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hz, fun w hw => Finset.card_le_one.mp hZ1 w hw z hz⟩
    have hzA : z ∈ SA := (Finset.mem_inter.mp hz).1
    have hzB : z ∈ SB := (Finset.mem_inter.mp hz).2
    by_cases hXe : X = ∅
    · by_cases hYe : Y = ∅
      · exact hstar_of_hit z fun e he => by
          rcases hedge_XYZ e he with h | h | h | h | h | h <;>
            simp [hXe, hYe, hZeq] at h
          · exact Or.inl h
          · exact Or.inr h
      · -- Type Z1 (symmetric: Z={z}, Y={y}, X=∅)! Swap SA and SB!
        obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
        have hYeq : Y = {y} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hy, fun w hw => Finset.card_le_one.mp hY1 w hw y hy⟩
        have hyA : y ∈ SA := (Finset.mem_inter.mp hy).1
        have hyCV : y ∈ CV := (Finset.mem_inter.mp hy).2
        have hzy : adj z y = true := by
          rw [h_adj_symm]; exact hadj_CV_AB y z hyCV hzA hzB
        have hSB_nb : ∀ b ∈ SB, adj y b = true := fun b hb => by
          rw [h_adj_symm]; exact hadj_B_ACV b y hb hyA hyCV
        obtain ⟨kB, hkB⟩ := exists_pickBits y SB hSB_nb
        have hdom := List.all_eq_true.mp h_dom_Z1 (z, y) (h_dirEdge_mem z y hzy)
        have hdom1 := List.all_eq_true.mp hdom kB (List.mem_finRange kB)
        have hmB_z : (pickBits (nbList y) kB.val).testBit z.val = true := by
          rw [← hkB, finsetMask_testBit_fin, decide_eq_true hzB]
        simp only [hmB_z, ↓reduceIte] at hdom1
        obtain ⟨idx, hidx, h1, h2⟩ := domByCoarse_spec hdom1
        let d' := pureMaskNat (pickBits (nbList y) kB.val) &&& (vVal z ||| vVal y)
        let cv' := cvNat d'
        have hd'_eq : d' = s2 &&& (vVal z ||| vVal y) := by
          dsimp only [d']; rw [← hkB, ← hs2_eq]
        -- Monotonicity: cv ⊆ cv' because (vVal z ||| vVal y) ⊆ s1!
        have hsub_cv : subMask cv cv' = true := by
          rw [subMask_iff]; intro i hi
          obtain ⟨v, rfl, hzv⟩ := (cvNat_testBit d i).mp hi
          rw [cvNat_testBit_fin]
          apply Nat.eq_of_testBit_eq; intro bit
          have h0 := congrArg (fun n => n.testBit bit) hzv
          rw [hd'_eq]
          simp only [d, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h0 ⊢
          cases hvbit : (vVal v).testBit bit <;> cases hs2bit : s2.testBit bit <;>
            cases hx2bit : x2Val.testBit bit
          · simp
          · simp
          · simp
          · simp
          · simp
          · simp
          · simp
          · simp only [hvbit, hs2bit, hx2bit, Bool.true_and, Bool.and_true] at h0 ⊢
            cases hzb : (vVal z).testBit bit <;> cases hyb : (vVal y).testBit bit
            · simp
            · have : s1.testBit bit = true := (seedSet_testBit D s1 hs1 bit).mpr ⟨y, hyA, hyb⟩
              simp [this] at h0
            · have : s1.testBit bit = true := (seedSet_testBit D s1 hs1 bit).mpr ⟨z, hzA, hzb⟩
              simp [this] at h0
            · have : s1.testBit bit = true := (seedSet_testBit D s1 hs1 bit).mpr ⟨z, hzA, hzb⟩
              simp [this] at h0
        -- Edge inclusion: d &&& edgeOfMask cv ⊆ d' &&& edgeOfMask cv'
        have hsub_ec : subMask (d &&& edgeOfMask cv) (d' &&& edgeOfMask cv') = true := by
          rw [subMask_iff]; intro i hi
          obtain ⟨e, rfl, _, _, _⟩ := hedge_info i hi
          rw [Nat.testBit_and, Bool.and_eq_true] at hi
          have he_hit : (edgeEnds e).1 = z ∨ (edgeEnds e).1 = y ∨
              (edgeEnds e).2 = z ∨ (edgeEnds e).2 = y := by
            rcases hedge_XYZ e (by rw [Nat.testBit_and, Bool.and_eq_true]; exact hi) with
              h | h | h | h | h | h <;> simp [hXe, hYeq, hZeq] at h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr h))
            · exact Or.inr (Or.inr (Or.inl h))
          rw [Nat.testBit_and, Bool.and_eq_true]
          constructor
          · rw [hd'_eq, Nat.testBit_and, Bool.and_eq_true]
            refine ⟨(Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi.1).2, ?_⟩
            rw [Nat.testBit_or, Bool.or_eq_true, h_bit_edge z e, h_bit_edge y e]
            rcases he_hit with h | h | h | h <;> simp [h]
          · obtain ⟨v, hmv, hvv⟩ := (edgeOfMask_testBit cv e).mp hi.2
            exact (edgeOfMask_testBit cv' e).mpr ⟨v, subMask_iff.mp hsub_cv v.val hmv, hvv⟩
        exact ⟨idx, hidx, subMask_trans hsub_ec h1, subMask_trans hsub_cv h2⟩
    · obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hXe
      have hXeq : X = {x} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hx, fun w hw => Finset.card_le_one.mp hX1 w hw x hx⟩
      have hxB : x ∈ SB := (Finset.mem_inter.mp hx).1
      have hxCV : x ∈ CV := (Finset.mem_inter.mp hx).2
      have hzx : adj z x = true := by
        rw [h_adj_symm]; exact hadj_CV_AB x z hxCV hzA hzB
      have hSA_nb : ∀ a ∈ SA, adj x a = true := fun a ha => by
        rw [h_adj_symm]; exact hadj_A_BCV a x ha hxB hxCV
      by_cases hYe : Y = ∅
      · -- Type Z1 (Z={z}, X={x}, Y=∅)!
        obtain ⟨kA, hkA⟩ := exists_pickBits x SA hSA_nb
        have hdom := List.all_eq_true.mp h_dom_Z1 (z, x) (h_dirEdge_mem z x hzx)
        have hdom1 := List.all_eq_true.mp hdom kA (List.mem_finRange kA)
        have hmA_z : (pickBits (nbList x) kA.val).testBit z.val = true := by
          rw [← hkA, finsetMask_testBit_fin, decide_eq_true hzA]
        simp only [hmA_z, ↓reduceIte] at hdom1
        obtain ⟨idx, hidx, h1, h2⟩ := domByCoarse_spec hdom1
        let d' := pureMaskNat (pickBits (nbList x) kA.val) &&& (vVal z ||| vVal x)
        let cv' := cvNat d'
        have hd'_eq : d' = s1 &&& (vVal z ||| vVal x) := by
          dsimp only [d']; rw [← hkA, ← hs1_eq]
        have hsub_cv : subMask cv cv' = true := by
          rw [subMask_iff]; intro i hi
          obtain ⟨v, rfl, hzv⟩ := (cvNat_testBit d i).mp hi
          rw [cvNat_testBit_fin]
          apply Nat.eq_of_testBit_eq; intro bit
          have h0 := congrArg (fun n => n.testBit bit) hzv
          rw [hd'_eq]
          simp only [d, Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h0 ⊢
          cases hvbit : (vVal v).testBit bit <;> cases hs1bit : s1.testBit bit <;>
            cases hx2bit : x2Val.testBit bit
          · simp
          · simp
          · simp
          · simp
          · simp
          · simp
          · simp
          · simp only [hvbit, hs1bit, hx2bit, Bool.true_and, Bool.and_true] at h0 ⊢
            cases hzb : (vVal z).testBit bit <;> cases hxb : (vVal x).testBit bit
            · simp
            · have : s2.testBit bit = true := (seedSet_testBit D s2 hs2 bit).mpr ⟨x, hxB, hxb⟩
              simp [this] at h0
            · have : s2.testBit bit = true := (seedSet_testBit D s2 hs2 bit).mpr ⟨z, hzB, hzb⟩
              simp [this] at h0
            · have : s2.testBit bit = true := (seedSet_testBit D s2 hs2 bit).mpr ⟨z, hzB, hzb⟩
              simp [this] at h0
        have hsub_ec : subMask (d &&& edgeOfMask cv) (d' &&& edgeOfMask cv') = true := by
          rw [subMask_iff]; intro i hi
          obtain ⟨e, rfl, _, _, _⟩ := hedge_info i hi
          rw [Nat.testBit_and, Bool.and_eq_true] at hi
          have he_hit : (edgeEnds e).1 = z ∨ (edgeEnds e).1 = x ∨
              (edgeEnds e).2 = z ∨ (edgeEnds e).2 = x := by
            rcases hedge_XYZ e (by rw [Nat.testBit_and, Bool.and_eq_true]; exact hi) with
              h | h | h | h | h | h <;> simp [hYe, hXeq, hZeq] at h
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact Or.inr (Or.inr (Or.inr h))
            · exact Or.inr (Or.inr (Or.inl h))
          rw [Nat.testBit_and, Bool.and_eq_true]
          constructor
          · rw [hd'_eq, Nat.testBit_and, Bool.and_eq_true]
            refine ⟨(Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi.1).1, ?_⟩
            rw [Nat.testBit_or, Bool.or_eq_true, h_bit_edge z e, h_bit_edge x e]
            rcases he_hit with h | h | h | h <;> simp [h]
          · obtain ⟨v, hmv, hvv⟩ := (edgeOfMask_testBit cv e).mp hi.2
            exact (edgeOfMask_testBit cv' e).mpr ⟨v, subMask_iff.mp hsub_cv v.val hmv, hvv⟩
        exact ⟨idx, hidx, subMask_trans hsub_ec h1, subMask_trans hsub_cv h2⟩
      · -- Type Z2 (Z={z}, X={x}, Y={y} — a triangle!)
        obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hYe
        have hyA : y ∈ SA := (Finset.mem_inter.mp hy).1
        have hyCV : y ∈ CV := (Finset.mem_inter.mp hy).2
        have hzy : adj z y = true := by
          rw [h_adj_symm]; exact hadj_CV_AB y z hyCV hzA hzB
        have hxy : adj x y = true := by
          rw [h_adj_symm]; exact hadj_A_BCV y x hyA hxB hxCV
        have hSB_nb : ∀ b ∈ SB, adj y b = true := fun b hb => by
          rw [h_adj_symm]; exact hadj_B_ACV b y hb hyA hyCV
        obtain ⟨kA, hkA⟩ := exists_pickBits x SA hSA_nb
        obtain ⟨kB, hkB⟩ := exists_pickBits y SB hSB_nb
        have hdom := List.all_eq_true.mp h_dom_Z2 (z, x, y) (h_tri_mem z x y hzx hzy hxy)
        have hdom1 := List.all_eq_true.mp hdom kA (List.mem_finRange kA)
        have hmA_z : (pickBits (nbList x) kA.val).testBit z.val = true := by
          rw [← hkA, finsetMask_testBit_fin, decide_eq_true hzA]
        have hmA_y : (pickBits (nbList x) kA.val).testBit y.val = true := by
          rw [← hkA, finsetMask_testBit_fin, decide_eq_true hyA]
        simp only [hmA_z, hmA_y, Bool.and_self, ↓reduceIte] at hdom1
        have hdom2 := List.all_eq_true.mp hdom1 kB (List.mem_finRange kB)
        have hmB_z : (pickBits (nbList y) kB.val).testBit z.val = true := by
          rw [← hkB, finsetMask_testBit_fin, decide_eq_true hzB]
        have hmB_x : (pickBits (nbList y) kB.val).testBit x.val = true := by
          rw [← hkB, finsetMask_testBit_fin, decide_eq_true hxB]
        have hmABz : (pickBits (nbList x) kA.val &&& pickBits (nbList y) kB.val) = (1 <<< z.val) := by
          rw [← hkA, ← hkB]
          apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.testBit_and, testBit_one_shl]
          cases h1 : (finsetMask SA).testBit i
          · simp only [Bool.false_and]
            symm; rw [decide_eq_false_iff_not]; intro hzi; subst hzi
            rw [finsetMask_testBit_fin, decide_eq_true hzA] at h1; simp at h1
          · obtain ⟨v, hvA, rfl⟩ := (finsetMask_testBit SA i).mp h1
            by_cases hvz : v = z
            · subst hvz; rw [finsetMask_testBit_fin, decide_eq_true hzB]; simp
            · have hvnotB : v ∉ SB := fun hvB => by
                have hvZ : v ∈ Z := Finset.mem_inter.mpr ⟨hvA, hvB⟩
                rw [hZeq, Finset.mem_singleton] at hvZ; exact hvz hvZ
              rw [finsetMask_testBit_fin, decide_eq_false hvnotB]
              have hne : z.val ≠ v.val := fun h => hvz (Fin.ext h.symm)
              simp [hne]
        have hd_eq : pureMaskNat (pickBits (nbList x) kA.val) &&&
            pureMaskNat (pickBits (nbList y) kB.val) = d := by
          rw [← hkA, ← hkB, ← hs1_eq, ← hs2_eq]
        simp only [hmB_z, hmB_x, hmABz, beq_self_eq_true, Bool.and_self, ↓reduceIte, hd_eq] at hdom2
        exact domByCoarse_spec hdom2

/-! ### Compact LP Dual Certificate Verification for `m ≤ 4` -/

def topMasksLoop (ed c : ℕ) : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | _, [] => []
  | st :: sts, ad :: ads =>
    let P := ad &&& c
    let rest := topMasksLoop ed c sts ads
    if hasTwoBits P then
      let eP := edgeOfMask P
      ((ed &&& eP) ||| (st &&& eP)) :: rest
    else rest

lemma mem_topMasksLoop_of_idx (ed c : ℕ) :
    ∀ (sts ads : List ℕ) (k : ℕ), k < sts.length → k < ads.length →
      hasTwoBits (ads.getD k 0 &&& c) = true →
      let P := ads.getD k 0 &&& c
      let eP := edgeOfMask P
      ((ed &&& eP) ||| (sts.getD k 0 &&& eP)) ∈ topMasksLoop ed c sts ads := by
  intro sts
  induction sts with
  | nil => intro ads k hk; simp at hk
  | cons st sts ih =>
    intro ads k hk1 hk2 h2
    cases ads with
    | nil => simp at hk2
    | cons ad ads =>
      simp only [topMasksLoop]
      cases k with
      | zero =>
        simp only [List.getD_cons_zero] at h2 ⊢
        simp [h2]
      | succ k' =>
        simp only [List.getD_cons_succ] at h2 ⊢
        have hm := ih ads k' (Nat.lt_of_succ_lt_succ hk1) (Nat.lt_of_succ_lt_succ hk2) h2
        split_ifs
        · exact List.mem_cons_of_mem _ hm
        · exact hm

def rawTopMasks (md me : ℕ × ℕ) : List ℕ :=
  let cd := md.2; let ce := me.2; let cde := cd &&& ce
  let ed := md.1; let ee := me.1
  starList ++
  [ed &&& edgeOfMask cd, ee &&& edgeOfMask ce, (ed ||| ee) &&& edgeOfMask cde] ++
  topMasksLoop ed cd starList adjList ++
  topMasksLoop ee ce starList adjList ++
  topMasksLoop (ed ||| ee) cde starList adjList

inductive WTree where
  | leaf (w : List ℕ)
  | node (l r : WTree)

def wtreeGet : WTree → ℕ → List ℕ
  | .leaf w, _ => w
  | .node l r, n => if n % 2 == 0 then wtreeGet l (n / 2) else wtreeGet r (n / 2)

def weightTree : WTree := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf [0,0,1,1,0,2,1,1,1,0,0,2,1,0,0,0]) (.leaf [0,1,0,2,1,0,1,1,0,0,0,1,0,0,0,0])) (.node (.leaf [4,0,29,0,17,10,23,24,0,0,4,17,13,2,6,0]) (.leaf [10,2,2,2,0,5,13,7,4,2,0,0,4,2,7,1]))) (.node (.node (.leaf [3,1,2,0,3,1,2,2,0,0,0,1,2,0,0,0]) (.leaf [1,0,1,1,1,1,0,0,2,0,0,1,3,0,1,1])) (.node (.leaf [2,5,4,5,3,1,0,11,1,0,1,2,0,0,0,0]) (.leaf [1,1,4,2,3,1,4,2,2,0,1,1,2,0,0,1])))) (.node (.node (.node (.leaf [0,0,0,0,0,2,1,1,2,0,0,0,1,0,0,0]) (.leaf [0,0,0,2,2,0,1,1,0,0,0,0,1,0,0,0])) (.node (.leaf [3,1,4,2,4,1,3,0,2,0,2,0,3,0,0,0]) (.leaf [4,8,3,1,3,5,0,11,1,2,1,2,0,0,4,2]))) (.node (.node (.leaf [2,7,6,6,1,1,2,10,5,0,0,9,0,0,0,0]) (.leaf [2,1,2,2,1,1,3,3,3,0,0,2,2,1,1,1])) (.leaf [9,3,4,3,1,2,3,9,5,1,1,0,3,5,0,0])))) (.node (.node (.node (.node (.leaf [0,0,1,1,0,2,0,0,1,0,0,2,2,0,0,0]) (.leaf [5,11,9,10,12,3,13,4,5,4,1,1,1,0,1,1])) (.node (.leaf [1,6,7,1,2,0,6,2,1,0,0,1,2,0,0,4]) (.leaf [6,6,15,14,27,14,11,20,20,2,11,11,4,11,26,5]))) (.node (.node (.leaf [2,5,4,1,3,1,0,11,5,0,1,2,0,0,0,0]) (.leaf [1,0,1,1,0,0,0,0,1,0,0,1,2,0,0,0])) (.node (.leaf [7,2,5,6,1,2,5,6,3,3,1,1,4,3,0,0]) (.leaf [0,0,1,1,1,1,1,1,1,0,0,1,0,0,1,0])))) (.node (.node (.node (.leaf [0,0,1,0,0,1,0,0,1,0,0,2,2,0,0,0]) (.leaf [1,11,4,6,4,2,0,0,9,0,1,1,16,4,0,2])) (.node (.leaf [1,1,0,2,1,1,0,2,0,0,0,1,0,0,0,0]) (.leaf [3,8,23,7,5,5,18,11,5,2,12,3,10,2,1,6]))) (.node (.node (.leaf [0,4,0,4,1,1,3,3,0,0,0,1,2,0,0,0]) (.leaf [0,7,5,6,3,1,6,4,3,4,1,2,6,0,0,1])) (.leaf [0,21,15,11,4,0,0,0,5,5,3,4,22,0,0,1]))))) (.node (.node (.node (.node (.node (.leaf [1,0,0,9,2,2,6,6,0,0,0,7,4,0,0,0]) (.leaf [2,0,1,1,2,0,2,0,1,0,0,0,0,0,0,0])) (.node (.leaf [1,3,5,2,4,2,0,13,6,1,0,7,0,0,2,0]) (.leaf [4,7,5,1,10,8,13,6,1,0,3,3,2,4,10,1]))) (.node (.node (.leaf [0,3,0,1,3,1,2,2,3,0,0,0,2,0,0,0]) (.leaf [1,1,4,2,2,1,3,3,1,0,2,1,2,0,1,1])) (.node (.leaf [8,3,10,1,1,7,6,5,0,0,1,1,5,1,0,0]) (.leaf [0,3,1,1,0,0,2,2,2,1,0,2,2,0,0,1])))) (.node (.node (.node (.leaf [0,0,2,0,0,2,1,1,0,0,0,2,1,0,0,0]) (.leaf [1,2,6,4,6,2,0,8,3,1,0,0,0,0,1,0])) (.node (.leaf [4,10,13,7,12,7,1,9,7,0,5,2,4,0,0,0]) (.leaf [0,3,2,2,1,1,2,4,3,0,0,2,2,2,0,1]))) (.node (.node (.leaf [0,2,0,1,0,0,1,1,0,0,1,0,1,0,0,0]) (.leaf [3,1,7,8,3,1,3,12,5,1,1,3,2,9,1,1])) (.leaf [2,1,2,1,1,5,0,7,3,0,1,0,0,0,0,0])))) (.node (.node (.node (.node (.leaf [0,0,3,0,0,2,2,1,0,0,0,1,1,0,0,0]) (.leaf [3,5,4,0,3,1,3,5,0,0,0,4,3,2,0,0])) (.node (.leaf [4,3,4,3,5,2,2,3,3,0,2,1,0,1,0,0]) (.leaf [6,6,11,12,15,6,8,22,1,1,2,6,7,15,1,2]))) (.node (.node (.leaf [2,7,1,0,7,4,8,4,11,0,0,2,4,0,0,0]) (.leaf [1,1,4,2,3,1,2,4,2,0,2,0,2,1,0,0])) (.leaf [1,2,6,4,1,3,0,0,3,1,1,2,8,3,0,0]))) (.node (.node (.node (.leaf [0,0,0,2,0,1,1,0,0,0,0,2,1,0,0,0]) (.leaf [1,3,5,7,6,0,0,0,3,0,2,1,7,1,1,0])) (.node (.leaf [19,2,14,14,23,2,15,12,1,0,0,2,14,0,0,0]) (.leaf [3,6,7,10,8,1,6,7,2,3,2,10,8,1,2,5]))) (.node (.node (.leaf [2,13,8,3,0,0,8,5,3,0,0,9,6,0,4,0]) (.leaf [2,2,2,2,8,3,0,0,1,2,1,3,10,4,3,2])) (.leaf [1,1,2,0,1,1,0,2,0,0,0,1,0,0,0,0])))))) (.node (.node (.node (.node (.node (.node (.leaf [0,0,1,1,0,0,1,1,1,0,0,1,1,0,0,0]) (.leaf [4,11,19,13,17,32,3,43,24,0,10,21,3,0,0,0])) (.node (.leaf [6,17,17,0,0,8,25,19,0,0,0,32,14,2,11,0]) (.leaf [3,2,2,1,5,2,0,7,2,2,3,3,0,0,5,1]))) (.node (.node (.leaf [1,1,0,0,1,1,0,2,2,0,0,1,0,0,0,0]) (.leaf [1,1,2,2,4,0,4,2,3,0,1,1,1,0,3,0])) (.node (.leaf [13,2,7,6,1,10,1,13,7,0,1,0,0,0,0,0]) (.leaf [12,12,14,10,2,2,8,22,12,0,0,2,7,15,1,2])))) (.node (.node (.node (.leaf [0,0,1,1,0,2,0,2,1,0,0,2,0,0,0,0]) (.leaf [1,1,4,7,9,1,2,9,4,1,0,0,2,8,0,0])) (.node (.leaf [0,1,0,2,1,0,1,0,0,0,0,1,1,0,0,0]) (.leaf [5,3,4,3,3,3,6,6,1,1,2,1,1,4,4,2]))) (.node (.node (.leaf [3,12,12,1,2,0,7,8,0,0,1,8,7,0,0,0]) (.leaf [1,2,5,2,1,1,2,3,1,2,3,4,3,0,1,2])) (.leaf [1,1,1,1,0,0,1,3,2,0,0,0,1,2,0,0])))) (.node (.node (.node (.node (.leaf [0,0,6,3,2,6,5,5,2,1,1,1,3,1,1,1]) (.leaf [2,0,2,0,2,0,1,1,0,0,0,0,1,0,0,0])) (.node (.leaf [1,1,0,2,1,1,0,0,0,0,0,1,2,0,0,0]) (.leaf [1,1,3,1,2,1,2,2,1,0,0,1,0,0,0,2]))) (.node (.node (.leaf [1,11,1,4,0,0,8,6,1,0,0,4,6,0,0,1]) (.leaf [1,2,9,3,8,1,6,4,3,0,3,1,5,0,0,3])) (.leaf [0,2,4,3,0,3,0,0,2,1,1,1,5,2,1,0]))) (.node (.node (.node (.leaf [0,0,1,1,0,1,0,2,1,0,0,1,0,0,0,0]) (.leaf [1,1,2,9,9,1,4,7,2,8,0,0,4,1,0,0])) (.node (.leaf [0,2,0,2,2,0,1,1,0,0,0,0,1,0,0,0]) (.leaf [6,3,2,6,1,1,4,8,3,1,0,2,2,6,2,2]))) (.node (.node (.leaf [1,2,2,2,0,1,2,2,1,0,0,1,1,0,1,1]) (.leaf [4,4,1,2,2,1,0,0,1,1,2,3,8,4,4,1])) (.leaf [0,2,1,1,0,0,0,2,1,0,0,0,0,0,0,0]))))) (.node (.node (.node (.node (.node (.leaf [0,0,0,0,1,0,2,3,4,0,0,4,2,0,0,0]) (.leaf [2,6,3,2,1,2,7,1,4,0,0,5,0,0,0,0])) (.node (.leaf [1,4,4,2,2,0,3,3,2,0,0,1,3,0,0,0]) (.leaf [1,2,0,6,6,5,2,2,0,0,3,3,1,2,1,3]))) (.node (.node (.leaf [1,13,0,5,3,1,10,8,0,0,5,2,8,0,0,1]) (.leaf [0,6,8,3,5,2,9,11,5,1,1,0,9,2,0,0])) (.node (.leaf [4,0,0,0,1,1,2,3,4,0,0,0,2,0,0,0]) (.leaf [8,32,14,19,10,5,17,32,23,0,1,8,16,12,0,1])))) (.node (.node (.node (.leaf [0,1,4,3,1,6,4,4,3,0,0,4,3,0,0,0]) (.leaf [1,1,3,2,3,1,0,4,2,0,0,0,0,0,0,0])) (.node (.leaf [3,8,12,6,10,19,2,13,15,0,7,13,13,0,0,0]) (.leaf [11,30,26,20,3,7,11,14,10,10,1,17,25,0,1,15]))) (.node (.node (.leaf [1,23,0,16,5,0,18,12,0,0,0,2,12,0,0,2]) (.leaf [0,1,2,1,3,0,1,3,2,0,0,1,1,2,0,0])) (.leaf [6,1,5,3,2,1,4,4,3,0,0,0,4,0,0,0])))) (.node (.node (.node (.node (.leaf [1,1,0,0,1,10,8,6,10,0,1,0,5,0,0,1]) (.leaf [1,4,8,0,5,3,5,3,0,0,0,1,2,1,0,0])) (.node (.leaf [0,2,1,1,2,0,0,1,1,0,0,0,1,0,0,0]) (.leaf [25,0,19,2,19,0,29,21,2,0,2,2,21,0,7,2]))) (.node (.node (.leaf [1,3,1,3,0,0,2,2,0,0,0,3,2,0,0,0]) (.leaf [13,7,8,21,7,7,0,0,4,4,4,12,38,7,12,7])) (.leaf [11,1,5,9,2,1,2,12,3,1,1,0,3,10,0,0]))) (.node (.node (.node (.leaf [1,3,1,0,0,0,2,2,3,0,0,3,2,0,0,0]) (.leaf [5,0,6,7,3,2,10,0,4,0,1,3,0,2,0,2])) (.node (.leaf [1,1,2,0,2,0,2,2,0,0,0,1,2,0,0,0]) (.leaf [7,4,3,8,0,0,6,5,3,0,0,3,5,0,1,0]))) (.node (.node (.leaf [2,15,14,15,3,3,0,0,11,0,0,2,24,0,2,0]) (.leaf [0,17,2,4,35,4,22,28,9,2,2,0,22,4,0,0])) (.leaf [6,1,4,4,6,0,3,5,2,0,1,1,0,0,0,0]))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf [0,0,0,0,0,2,1,1,2,0,0,2,1,0,0,0]) (.leaf [4,8,5,3,1,3,1,10,6,0,0,8,0,0,0,0])) (.node (.leaf [1,1,1,1,0,0,3,1,2,0,0,0,1,0,2,0]) (.leaf [1,1,1,0,2,0,0,0,0,1,1,1,2,1,2,0]))) (.node (.node (.leaf [6,2,0,1,0,6,4,4,5,0,1,0,4,0,0,0]) (.leaf [1,0,1,0,1,1,0,3,1,0,0,1,0,0,0,1])) (.node (.leaf [0,0,1,0,0,1,1,1,0,0,0,2,1,0,0,0]) (.leaf [3,2,2,1,3,1,3,5,3,0,0,4,1,4,1,0])))) (.node (.node (.node (.leaf [0,0,0,4,1,4,3,2,0,0,0,0,2,0,0,0]) (.leaf [0,1,2,2,2,1,2,2,1,1,0,1,1,1,0,0])) (.node (.leaf [0,1,0,0,1,0,1,0,2,0,0,1,1,0,0,0]) (.leaf [1,4,1,1,6,2,3,5,2,0,1,1,3,2,0,1]))) (.node (.node (.leaf [2,17,10,9,1,0,17,1,8,0,0,15,1,0,0,0]) (.leaf [1,4,8,7,4,4,10,5,6,0,0,1,4,1,5,1])) (.leaf [2,2,2,2,0,0,4,8,5,1,2,1,2,6,0,0])))) (.node (.node (.node (.node (.leaf [0,0,0,2,0,2,1,1,0,0,0,2,1,0,0,0]) (.leaf [0,4,5,1,4,1,3,3,0,0,0,1,2,1,0,0])) (.node (.leaf [1,6,5,3,2,0,4,4,3,0,0,1,4,0,0,0]) (.leaf [15,7,20,10,23,3,4,4,7,2,2,4,7,3,0,10]))) (.node (.node (.leaf [0,6,1,2,0,0,4,3,1,0,2,2,3,1,0,0]) (.leaf [1,1,7,2,6,3,6,5,4,0,5,1,5,1,2,0])) (.leaf [17,2,1,16,2,11,9,10,1,1,0,1,8,2,0,0]))) (.node (.node (.node (.leaf [1,1,4,2,0,3,0,0,1,0,0,2,4,0,1,0]) (.leaf [0,1,2,1,3,1,1,3,2,0,0,0,1,2,0,0])) (.node (.leaf [1,1,0,2,1,1,2,0,0,0,0,1,0,0,0,0]) (.leaf [6,19,33,15,6,6,24,26,11,3,22,6,23,3,0,0]))) (.node (.node (.leaf [0,4,0,3,1,0,3,2,0,0,0,1,2,0,0,0]) (.leaf [3,2,2,4,6,2,2,4,1,0,0,2,1,1,2,1])) (.leaf [0,0,1,2,1,0,1,1,0,2,0,0,2,0,0,0]))))) (.node (.node (.node (.node (.node (.leaf [0,0,2,2,1,1,0,4,1,0,0,2,0,0,0,0]) (.leaf [1,4,3,5,3,0,8,0,2,3,1,3,0,0,0,0])) (.node (.leaf [0,1,1,0,1,0,0,2,1,0,0,1,0,0,0,0]) (.leaf [2,2,0,0,8,3,2,3,8,3,4,3,1,2,2,3]))) (.node (.node (.leaf [2,0,1,0,2,0,1,1,1,0,0,0,1,0,0,0]) (.leaf [1,0,1,1,1,1,1,1,1,0,0,0,1,0,0,0])) (.node (.leaf [3,0,0,3,1,0,2,2,0,0,0,0,2,0,0,0]) (.leaf [3,5,4,2,2,3,8,4,5,1,0,2,1,3,2,5])))) (.node (.node (.node (.leaf [0,0,5,2,3,0,4,4,2,0,1,0,4,0,0,0]) (.leaf [6,6,26,19,25,6,0,0,13,3,2,2,34,6,0,3])) (.node (.leaf [2,4,3,2,0,1,1,0,3,0,0,4,5,0,0,0]) (.leaf [2,2,4,4,1,7,7,7,7,1,3,4,4,4,4,1]))) (.node (.node (.leaf [0,10,0,0,2,2,7,8,10,0,0,1,5,0,0,1]) (.leaf [15,17,17,19,7,1,12,37,21,3,2,8,9,27,4,3])) (.leaf [9,1,4,8,2,1,4,8,1,7,0,0,3,1,0,0])))) (.node (.node (.node (.node (.leaf [1,0,6,1,3,0,5,3,1,0,1,1,3,0,0,0]) (.leaf [0,2,2,0,1,0,1,1,0,0,0,1,1,0,0,0])) (.node (.leaf [1,1,2,0,1,1,0,0,0,0,0,1,2,0,0,0]) (.leaf [0,0,1,1,1,3,3,3,1,1,1,1,2,3,3,1]))) (.node (.node (.leaf [1,5,3,3,0,0,1,0,3,0,0,4,5,0,0,0]) (.leaf [3,6,17,12,6,3,17,13,9,4,1,3,9,4,7,7])) (.leaf [3,3,7,5,1,5,0,11,3,2,2,3,0,0,0,1]))) (.node (.node (.node (.leaf [0,0,0,0,0,1,1,0,2,0,0,2,1,0,0,0]) (.leaf [5,15,20,27,24,2,0,0,11,2,7,5,28,0,5,1])) (.node (.leaf [1,12,0,0,4,1,10,10,5,1,5,2,9,0,0,1]) (.leaf [3,4,7,10,9,4,10,9,2,2,2,3,2,6,2,5]))) (.node (.node (.leaf [1,1,0,3,1,0,2,2,0,0,0,1,2,0,0,0]) (.leaf [1,1,1,1,3,2,0,5,0,1,0,2,0,0,1,1])) (.leaf [0,2,1,1,2,0,0,2,1,0,0,0,0,0,0,0])))))) (.node (.node (.node (.node (.node (.node (.leaf [0,1,3,2,3,1,2,4,1,0,0,0,2,0,0,0]) (.leaf [2,3,5,0,3,2,4,1,0,0,0,2,0,0,0,0])) (.node (.leaf [0,1,1,0,1,0,0,0,1,0,0,1,2,0,0,0]) (.leaf [3,7,5,8,11,1,6,7,1,5,3,6,8,0,2,8]))) (.node (.node (.leaf [1,1,0,0,1,1,2,0,2,0,0,1,0,0,0,0]) (.leaf [1,0,3,1,3,0,1,2,1,0,0,1,2,0,0,2])) (.node (.leaf [14,3,10,10,0,14,16,2,8,2,0,2,0,0,0,0]) (.leaf [19,14,17,18,4,2,12,35,20,7,1,14,7,14,7,8])))) (.node (.node (.node (.leaf [0,0,1,1,0,2,2,0,1,0,0,2,0,0,0,0]) (.leaf [1,1,4,3,4,1,0,0,2,1,0,0,6,1,1,0])) (.node (.leaf [14,2,11,9,13,6,8,0,8,0,3,4,2,1,0,0]) (.leaf [9,5,2,2,2,6,8,7,5,0,2,1,4,3,4,1]))) (.node (.node (.leaf [0,11,0,0,2,2,7,6,8,0,3,1,5,0,0,1]) (.leaf [1,3,5,5,2,1,0,11,1,1,2,3,0,0,1,1])) (.leaf [6,3,6,5,5,18,0,0,11,1,5,2,25,3,0,2])))) (.node (.node (.node (.node (.leaf [0,1,5,3,1,5,7,0,2,0,0,1,0,0,0,0]) (.leaf [1,7,13,1,6,0,4,11,0,0,1,6,4,7,0,0])) (.node (.leaf [3,1,2,2,0,3,0,1,2,0,0,0,3,0,0,0]) (.leaf [5,7,15,14,12,7,10,12,3,11,11,4,2,2,4,1]))) (.node (.node (.leaf [1,3,1,0,2,0,1,2,3,0,0,2,2,0,0,0]) (.leaf [0,1,2,2,0,1,3,1,2,0,0,0,1,0,0,0])) (.leaf [10,10,24,18,3,18,0,33,8,8,4,6,0,0,6,3]))) (.node (.node (.node (.leaf [1,1,2,2,0,2,0,0,1,0,0,1,3,0,0,0]) (.leaf [6,1,11,8,8,2,10,9,3,1,5,5,5,1,5,3])) (.node (.leaf [11,1,4,9,11,1,5,9,0,1,0,3,5,1,0,0]) (.leaf [2,4,5,12,16,5,12,12,6,4,7,7,3,12,12,2]))) (.node (.node (.leaf [1,3,4,2,2,0,3,3,2,0,0,2,3,0,0,0]) (.leaf [13,23,7,7,7,7,0,31,5,7,7,17,0,0,17,3])) (.leaf [2,22,0,22,3,2,8,8,0,0,4,0,17,1,0,0]))))) (.node (.node (.node (.node (.node (.leaf [0,1,0,6,1,0,3,4,0,0,0,5,3,0,0,0]) (.leaf [1,3,5,3,4,8,6,5,6,0,3,4,1,0,0,0])) (.node (.leaf [0,2,2,1,0,0,1,1,1,0,0,2,2,0,0,1]) (.leaf [0,8,2,5,3,0,1,8,5,0,1,0,1,1,0,0]))) (.node (.node (.leaf [1,4,3,1,3,0,0,0,3,0,1,2,7,0,0,0]) (.leaf [9,1,0,10,0,1,8,7,0,0,0,1,6,0,2,1])) (.node (.leaf [22,4,0,0,9,4,25,23,31,4,2,2,23,1,0,0]) (.leaf [5,3,5,4,4,7,11,9,6,2,2,4,2,7,9,1])))) (.node (.node (.node (.leaf [0,0,1,0,0,1,0,2,1,0,0,2,0,0,0,0]) (.leaf [1,8,3,2,3,1,0,0,5,0,1,0,8,2,2,1])) (.node (.leaf [3,1,0,3,0,3,2,2,0,0,1,0,2,0,0,0]) (.leaf [15,20,22,4,14,5,25,25,10,2,2,14,18,5,6,14]))) (.node (.node (.leaf [0,2,0,0,0,0,1,1,2,0,0,0,1,0,0,0]) (.leaf [7,1,6,23,7,1,14,15,4,20,1,7,13,1,1,1])) (.leaf [0,0,5,9,2,3,4,3,2,7,0,1,7,1,0,0])))) (.node (.node (.node (.node (.leaf [1,1,0,8,1,8,7,5,0,0,1,0,4,0,0,1]) (.leaf [0,0,0,0,2,0,1,1,2,0,0,0,1,0,0,0])) (.node (.leaf [5,0,3,3,4,0,2,0,2,0,1,1,3,1,0,0]) (.leaf [14,18,13,3,13,14,0,0,4,4,3,4,32,11,14,4]))) (.node (.node (.leaf [2,2,3,1,2,0,2,2,1,0,0,0,2,0,0,0]) (.leaf [6,4,2,8,4,4,0,15,2,2,2,5,0,0,5,3])) (.leaf [4,1,4,2,2,1,3,3,2,0,0,0,3,0,0,0]))) (.node (.node (.node (.leaf [1,1,0,0,1,1,0,0,2,0,0,1,2,0,0,0]) (.leaf [3,0,0,4,0,2,2,4,0,0,0,1,1,0,1,1])) (.node (.leaf [0,2,1,2,1,0,0,0,0,0,0,1,3,0,0,0]) (.leaf [0,1,1,2,2,1,3,1,1,0,1,1,1,0,2,0]))) (.node (.node (.leaf [1,1,2,1,0,0,0,3,1,0,0,1,0,0,0,0]) (.leaf [4,2,2,1,6,2,0,0,2,2,1,3,10,2,4,3])) (.leaf [1,3,0,0,2,0,3,4,6,0,1,2,0,0,0,0]))))))))

inductive CoverCert where
  | wt (idx : ℕ)
  | br (e : ℕ) (subs : List ℕ)

def certRows : Array (Array CoverCert) := #[
  #[.wt 0, .wt 1, .br 2 [6,4,6,4,6,7,6,7], .wt 8, .wt 9, .br 2 [14,15,16,17,16,17,16,17], .wt 18, .wt 19, .wt 20, .br 2 [14,15,16,17,16,17,16,17], .br 2 [6,4,6,4,6,7,6,7], .br 2 [6,4,6,4], .wt 0, .br 2 [6,4,6,4], .wt 20, .wt 9, .wt 20, .wt 20, .wt 8, .wt 18, .wt 19, .wt 20, .wt 20, .wt 22, .br 12 [5,11,5,11], .br 2 [6,4,6,4], .wt 9, .wt 9, .br 6 [24,23,24,23], .wt 1, .br 6 [25,26,27,26], .br 6 [25,26,27,26], .wt 20, .wt 18, .wt 18, .br 2 [29,28,29,28], .wt 0, .wt 19, .wt 19, .wt 19, .wt 20, .wt 20],
  #[.wt 1, .wt 30, .wt 31, .wt 32, .wt 33, .wt 34, .wt 35, .wt 32, .wt 36, .wt 37, .wt 37, .wt 1, .br 6 [39,40,39,40], .wt 32, .wt 32, .br 0 [17,9,17,30], .wt 33, .wt 31, .wt 34, .wt 35, .br 4 [41,1,42,1], .wt 33, .wt 36, .wt 33, .wt 37, .wt 37, .wt 37, .wt 30, .wt 1, .wt 33, .wt 36, .wt 32, .wt 37, .wt 37, .wt 43, .wt 1, .wt 44, .wt 36, .wt 32, .wt 32, .wt 33],
  #[.wt 30, .wt 45, .wt 46, .wt 47, .wt 48, .wt 49, .wt 50, .br 2 [51,52,53,54,55,56,55,57], .br 2 [6,4,6,7,6,7,6,7], .br 2 [6,4,6,7], .wt 58, .wt 59, .wt 60, .wt 46, .wt 50, .wt 47, .wt 45, .wt 48, .wt 49, .wt 50, .wt 50, .br 6 [62,5,62,63], .wt 46, .wt 46, .wt 46, .wt 46, .wt 30, .br 6 [67,68,67,69], .wt 47, .wt 70, .wt 47, .wt 48, .wt 48, .wt 71, .wt 47, .wt 72, .wt 73, .wt 47, .wt 47, .wt 47],
  #[.wt 8, .wt 74, .wt 75, .wt 76, .wt 76, .wt 77, .wt 78, .wt 79, .wt 80, .wt 8, .br 2 [81,82,81,82], .wt 77, .wt 74, .wt 77, .wt 75, .wt 8, .wt 83, .wt 84, .wt 77, .wt 77, .wt 78, .wt 75, .wt 79, .wt 79, .wt 79, .wt 85, .wt 86, .wt 75, .wt 78, .wt 75, .wt 79, .wt 79, .wt 78, .wt 8, .wt 78, .wt 78, .wt 75, .wt 77, .wt 75],
  #[.wt 9, .wt 87, .wt 88, .wt 89, .wt 32, .wt 90, .wt 91, .wt 92, .wt 9, .br 6 [95,96,95,96], .wt 32, .wt 9, .wt 87, .wt 87, .wt 74, .wt 88, .wt 89, .wt 90, .wt 87, .wt 90, .wt 46, .wt 46, .wt 9, .wt 9, .br 0 [97,46,97,46], .br 4 [20,9,20,9], .wt 87, .wt 90, .wt 32, .wt 91, .wt 91, .wt 90, .wt 9, .wt 90, .wt 90, .wt 32, .wt 32, .wt 87],
  #[.wt 33, .wt 98, .wt 99, .wt 100, .br 2 [14,15,16,17,16,17,16,17], .br 2 [102,101,102,101,102,87,102,101], .br 2 [103,101,103,101], .br 2 [14,15,16,17], .wt 104, .wt 33, .wt 105, .wt 87, .wt 33, .wt 75, .wt 98, .wt 99, .wt 100, .wt 33, .br 6 [106,107,108,109], .wt 33, .wt 47, .wt 110, .wt 111, .wt 112, .br 6 [115,116,115,116], .wt 33, .wt 100, .wt 33, .wt 117, .wt 118, .br 2 [55,123,55,123], .wt 33, .wt 99, .wt 99, .wt 33, .wt 47, .wt 33],
  #[.wt 18, .wt 76, .wt 124, .wt 125, .wt 126, .wt 126, .wt 18, .br 2 [127,128,127,128], .wt 124, .wt 88, .wt 124, .wt 98, .wt 18, .wt 18, .wt 125, .wt 124, .wt 124, .wt 125, .wt 98, .wt 126, .wt 126, .wt 126, .wt 129, .wt 130, .wt 98, .wt 125, .wt 98, .wt 18, .wt 18, .wt 125, .wt 18, .wt 125, .wt 125, .wt 76, .wt 124, .wt 98],
  #[.wt 19, .wt 131, .wt 125, .wt 132, .wt 132, .wt 19, .wt 133, .wt 131, .wt 89, .wt 131, .wt 99, .wt 19, .wt 83, .wt 19, .wt 131, .wt 131, .wt 125, .wt 99, .wt 132, .wt 132, .wt 80, .wt 134, .wt 135, .wt 99, .wt 136, .wt 99, .wt 132, .wt 80, .wt 125, .wt 19, .wt 19, .wt 19, .wt 19, .wt 125, .wt 99],
  #[.wt 20, .wt 137, .wt 138, .wt 138, .wt 20, .wt 139, .wt 20, .wt 32, .wt 20, .wt 20, .wt 77, .wt 124, .wt 131, .wt 20, .wt 20, .wt 137, .wt 50, .wt 138, .wt 138, .wt 138, .wt 140, .wt 20, .wt 50, .wt 100, .wt 20, .wt 138, .wt 138, .wt 141, .wt 20, .wt 142, .wt 137, .wt 32, .wt 20, .wt 20],
  #[.wt 36, .br 2 [143,144,143,144,143,90,143,90], .br 2 [143,144,143,144], .br 2 [14,15,16,17], .wt 145, .wt 36, .wt 90, .wt 137, .wt 137, .wt 78, .wt 125, .wt 125, .wt 90, .wt 137, .wt 36, .br 12 [122,11,122,19], .br 2 [143,17,143,17], .wt 146, .br 6 [147,148,149,150], .br 6 [151,122,152,122], .wt 153, .wt 137, .wt 36, .wt 137, .wt 154, .br 2 [143,144,143,144], .wt 78, .wt 125, .wt 36, .wt 36, .wt 36, .wt 36, .wt 90],
  #[.wt 37, .wt 37, .wt 155, .br 2 [6,4,6,7], .wt 37, .wt 91, .wt 138, .wt 138, .wt 79, .wt 126, .wt 132, .wt 138, .wt 138, .br 6 [156,5,157,110], .br 12 [5,158,98,158], .wt 37, .wt 37, .wt 37, .br 6 [160,161,160,129], .wt 162, .wt 138, .wt 138, .wt 138, .wt 37, .wt 37, .wt 163, .wt 37, .br 2 [143,144,143,90], .br 2 [143,128,143,90], .wt 37, .wt 138, .wt 138],
  #[.wt 37, .wt 164, .br 2 [6,4], .wt 138, .wt 92, .wt 138, .wt 47, .wt 132, .wt 126, .wt 132, .wt 138, .wt 138, .wt 47, .wt 165, .wt 37, .wt 37, .wt 37, .br 6 [168,63], .wt 169, .wt 111, .wt 138, .wt 138, .wt 37, .wt 37, .wt 170, .wt 37, .br 2 [143,144], .wt 172, .wt 47, .wt 138, .wt 92],
  #[.wt 0, .wt 173, .br 6 [174,175], .wt 9, .wt 20, .wt 20, .wt 18, .wt 18, .wt 19, .wt 20, .wt 20, .wt 22, .wt 173, .wt 58, .wt 9, .wt 9, .wt 176, .wt 1, .wt 58, .wt 177, .wt 20, .wt 18, .wt 18, .wt 178, .wt 8, .wt 19, .wt 19, .wt 19, .wt 20, .wt 20],
  #[.wt 59, .wt 139, .br 6 [95,179], .wt 139, .wt 104, .wt 133, .br 2 [127,128], .wt 133, .wt 139, .wt 139, .wt 146, .wt 59, .br 2 [6,4], .wt 180, .br 6 [168,5], .wt 181, .wt 182, .wt 59, .wt 139, .wt 139, .wt 183, .br 2 [6,4], .wt 184, .wt 59, .wt 133, .wt 133, .wt 133, .wt 139, .wt 139],
  #[.wt 20, .wt 32, .wt 32, .wt 33, .wt 77, .wt 185, .wt 131, .wt 90, .wt 33, .wt 36, .wt 33, .wt 37, .wt 37, .wt 37, .wt 60, .wt 20, .wt 33, .wt 36, .wt 20, .wt 37, .wt 37, .wt 90, .wt 20, .wt 36, .wt 36, .wt 32, .wt 20, .wt 33],
  #[.wt 9, .br 6 [186,187], .wt 32, .wt 88, .wt 88, .wt 89, .br 6 [188,189], .wt 32, .wt 90, .wt 46, .wt 46, .wt 9, .wt 9, .br 6 [191,161], .br 6 [193,194], .wt 105, .wt 90, .wt 32, .wt 91, .wt 91, .wt 195, .wt 32, .wt 90, .wt 90, .wt 32, .wt 32, .wt 87],
  #[.wt 20, .wt 20, .wt 77, .wt 124, .wt 131, .wt 20, .wt 20, .wt 137, .wt 50, .wt 50, .wt 138, .wt 138, .wt 60, .wt 196, .wt 50, .wt 100, .wt 20, .wt 138, .wt 138, .wt 141, .wt 20, .wt 137, .wt 137, .wt 32, .wt 20, .wt 20],
  #[.wt 20, .wt 75, .wt 98, .wt 99, .wt 20, .wt 20, .wt 47, .wt 33, .wt 47, .wt 110, .wt 111, .wt 112, .wt 196, .wt 33, .wt 100, .wt 20, .wt 117, .wt 47, .wt 141, .wt 20, .wt 99, .wt 47, .wt 32, .wt 20, .wt 20],
  #[.wt 8, .wt 83, .wt 84, .wt 131, .wt 77, .wt 78, .wt 75, .wt 79, .wt 79, .wt 79, .wt 85, .wt 86, .wt 75, .wt 78, .wt 75, .wt 18, .wt 79, .wt 78, .wt 8, .wt 19, .wt 78, .wt 75, .wt 77, .wt 75],
  #[.wt 18, .br 2 [197,198], .wt 124, .wt 124, .wt 125, .wt 98, .wt 126, .wt 126, .wt 126, .br 0 [23,199,23], .wt 200, .wt 98, .wt 125, .wt 98, .wt 18, .wt 18, .wt 201, .wt 18, .wt 202, .wt 125, .wt 76, .wt 124, .wt 98],
  #[.wt 19, .wt 131, .wt 131, .wt 125, .wt 99, .wt 132, .wt 132, .wt 132, .wt 134, .wt 135, .wt 99, .wt 136, .wt 99, .wt 203, .wt 132, .wt 125, .wt 84, .wt 19, .wt 19, .wt 19, .wt 125, .wt 136],
  #[.wt 20, .wt 20, .wt 137, .wt 50, .wt 50, .wt 204, .wt 138, .br 6 [207,208], .wt 209, .wt 50, .wt 90, .wt 20, .wt 138, .wt 138, .wt 90, .wt 20, .wt 142, .wt 137, .wt 131, .wt 20, .wt 20],
  #[.wt 20, .wt 137, .wt 33, .wt 50, .wt 210, .wt 138, .wt 211, .wt 20, .wt 33, .wt 100, .wt 20, .wt 138, .wt 138, .wt 141, .wt 20, .wt 137, .wt 137, .wt 32, .wt 20, .wt 20],
  #[.wt 22, .wt 59, .wt 47, .wt 146, .wt 165, .wt 212, .wt 153, .wt 47, .wt 90, .wt 47, .wt 154, .wt 47, .wt 78, .wt 125, .wt 36, .wt 22, .wt 22, .wt 36, .wt 22],
  #[.wt 33, .wt 46, .wt 46, .wt 46, .wt 112, .wt 213, .wt 33, .wt 70, .wt 33, .wt 117, .wt 47, .wt 214, .wt 33, .wt 72, .wt 47, .wt 47, .wt 47, .wt 47],
  #[.wt 37, .wt 37, .wt 37, .wt 215, .wt 162, .wt 47, .wt 138, .wt 47, .wt 37, .wt 37, .wt 71, .wt 37, .wt 216, .wt 217, .wt 37, .wt 138, .wt 111],
  #[.wt 9, .wt 9, .wt 218, .wt 219, .wt 110, .wt 138, .wt 110, .wt 37, .wt 37, .wt 220, .wt 9, .wt 221, .wt 146, .wt 37, .wt 138, .wt 92],
  #[.wt 9, .wt 222, .wt 223, .wt 111, .wt 111, .wt 111, .wt 37, .wt 37, .wt 163, .wt 9, .wt 224, .wt 165, .wt 37, .wt 138, .wt 92],
  #[.wt 30, .wt 225, .wt 60, .wt 226, .wt 60, .wt 227, .wt 222, .wt 228, .wt 129, .wt 229, .wt 230, .wt 112, .wt 140, .wt 112],
  #[.wt 1, .wt 231, .wt 153, .wt 20, .wt 232, .wt 162, .br 8 [43,90,141,141], .wt 1, .wt 135, .wt 22, .wt 22, .wt 20, .wt 20],
  #[.wt 33, .wt 47, .wt 33, .wt 117, .wt 47, .wt 141, .wt 33, .wt 72, .wt 47, .wt 33, .wt 47, .wt 33],
  #[.wt 36, .wt 47, .wt 138, .wt 47, .wt 78, .wt 47, .wt 90, .wt 78, .wt 78, .wt 36, .wt 47],
  #[.wt 20, .wt 138, .wt 47, .wt 141, .wt 20, .wt 99, .wt 47, .wt 32, .wt 20, .wt 20],
  #[.wt 18, .wt 18, .wt 163, .wt 18, .wt 154, .wt 154, .wt 37, .wt 138, .wt 117],
  #[.wt 18, .wt 163, .wt 18, .wt 202, .wt 47, .wt 37, .wt 47, .wt 47],
  #[.wt 43, .wt 163, .wt 78, .wt 78, .wt 78, .wt 78, .wt 90],
  #[.wt 0, .wt 19, .wt 19, .wt 33, .wt 20, .wt 20],
  #[.wt 19, .wt 19, .wt 19, .wt 36, .wt 90],
  #[.wt 19, .wt 19, .wt 36, .wt 22],
  #[.wt 19, .wt 32, .wt 22],
  #[.wt 20, .wt 20],
  #[.wt 20]
]

def weightOfMask : List ℕ → ℕ → ℕ
  | [], _ => 0
  | w0 :: ws, m =>
    if m == 0 then 0
    else (if m % 2 == 1 then w0 else 0) + weightOfMask ws (m / 2)

lemma weightOfMask_mono : ∀ (w : List ℕ) (m1 m2 : ℕ),
    (∀ i, m1.testBit i = true → m2.testBit i = true) →
    weightOfMask w m1 ≤ weightOfMask w m2 := by
  intro w
  induction w with
  | nil => intro m1 m2 _; simp [weightOfMask]
  | cons w0 ws ih =>
    intro m1 m2 hsub
    simp only [weightOfMask]
    by_cases hm1 : m1 = 0
    · subst hm1; simp
    · have hm1' : (m1 == 0) = false := beq_false_of_ne hm1
      have hm2 : m2 ≠ 0 := by
        intro h2; subst h2
        have ⟨i, hi⟩ : ∃ i, m1.testBit i = true := by
          by_contra hall
          push_neg at hall
          apply hm1
          apply Nat.eq_of_testBit_eq; intro i
          cases h' : m1.testBit i
          · simp
          · exact (hall i h').elim
        have := hsub i hi; simp at this
      have hm2' : (m2 == 0) = false := beq_false_of_ne hm2
      rw [hm1', hm2']; simp only [Bool.false_eq_true, ↓reduceIte]
      have hrec : weightOfMask ws (m1 / 2) ≤ weightOfMask ws (m2 / 2) :=
        ih (m1 / 2) (m2 / 2) fun i hi => by
          rw [testBit_div2] at hi ⊢; exact hsub (i + 1) hi
      have hhead : (if m1 % 2 == 1 then w0 else 0) ≤ (if m2 % 2 == 1 then w0 else 0) := by
        by_cases ho1 : m1 % 2 = 1
        · have hbit : m1.testBit 0 = true := by rw [testBit_zero_eq]; simp [ho1]
          have hbit2 := hsub 0 hbit
          rw [testBit_zero_eq] at hbit2
          simp [ho1, hbit2]
        · have : (m1 % 2 == 1) = false := beq_false_of_ne ho1
          simp [this]
      omega

lemma weightOfMask_or_le : ∀ (w : List ℕ) (m1 m2 : ℕ),
    weightOfMask w (m1 ||| m2) ≤ weightOfMask w m1 + weightOfMask w m2 := by
  intro w
  induction w with
  | nil => intro m1 m2; simp [weightOfMask]
  | cons w0 ws ih =>
    intro m1 m2
    by_cases hm1 : m1 = 0
    · subst hm1; simp [weightOfMask]
    · by_cases hm2 : m2 = 0
      · subst hm2; simp [weightOfMask]
      · have hor : m1 ||| m2 ≠ 0 := by
          intro h
          have : m1 ≤ m1 ||| m2 := Nat.left_le_or
          omega
        simp only [weightOfMask, beq_false_of_ne hm1, beq_false_of_ne hm2, beq_false_of_ne hor,
          Bool.false_eq_true, ↓reduceIte]
        have hdiv : (m1 ||| m2) / 2 = (m1 / 2) ||| (m2 / 2) := by
          apply Nat.eq_of_testBit_eq; intro k
          rw [testBit_div2, Nat.testBit_or, Nat.testBit_or, testBit_div2, testBit_div2]
        rw [hdiv]
        have hrec := ih (m1 / 2) (m2 / 2)
        have h0 : (if (m1 ||| m2) % 2 == 1 then w0 else 0) ≤
            (if m1 % 2 == 1 then w0 else 0) + (if m2 % 2 == 1 then w0 else 0) := by
          have hb := Nat.testBit_or m1 m2 0
          rw [testBit_zero_eq, testBit_zero_eq, testBit_zero_eq] at hb
          cases h1 : (m1 % 2 == 1) <;> cases h2 : (m2 % 2 == 1) <;> simp_all
        omega

def checkWeight (rem k : ℕ) (ms : List ℕ) (w : List ℕ) : Bool :=
  let tot := weightOfMask w rem
  if tot == 0 then false
  else
    let bound := (tot - 1) / k
    ms.all (fun m => decide (weightOfMask w (m &&& rem) ≤ bound))

lemma list_or_foldl_weight (w : List ℕ) (rem bound : ℕ) :
    ∀ (S : List ℕ), (∀ s ∈ S, weightOfMask w (s &&& rem) ≤ bound) →
      weightOfMask w (S.foldl (· ||| ·) 0 &&& rem) ≤ S.length * bound := by
  have hgen : ∀ (S : List ℕ) (acc : ℕ), (∀ s ∈ S, weightOfMask w (s &&& rem) ≤ bound) →
      weightOfMask w (S.foldl (· ||| ·) acc &&& rem) ≤
        weightOfMask w (acc &&& rem) + S.length * bound := by
    intro S
    induction S with
    | nil => intro acc _; simp
    | cons s rest ih =>
      intro acc hS
      simp only [List.foldl_cons, List.length_cons]
      have h1 := ih (acc ||| s) (fun x hx => hS x (List.mem_cons_of_mem s hx))
      have h2 : (acc ||| s) &&& rem = (acc &&& rem) ||| (s &&& rem) := by
        apply Nat.eq_of_testBit_eq; intro i
        simp only [Nat.testBit_and, Nat.testBit_or]
        cases acc.testBit i <;> cases s.testBit i <;> cases rem.testBit i <;> rfl
      rw [h2] at h1
      have h3 := weightOfMask_or_le w (acc &&& rem) (s &&& rem)
      have h4 := hS s (List.mem_cons_self ..)
      have hmul : (rest.length + 1) * bound = rest.length * bound + bound := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
  intro S hS
  have h := hgen S 0 hS
  simp only [Nat.zero_and, weightOfMask] at h
  have hz : weightOfMask w 0 = 0 := by cases w <;> simp [weightOfMask]
  rw [hz] at h; omega

lemma checkWeight_sound (rem k : ℕ) (hk : 1 ≤ k) (ms : List ℕ) (w : List ℕ)
    (hchk : checkWeight rem k ms w = true)
    (S : List ℕ) (hlen : S.length ≤ k)
    (hdom : ∀ s ∈ S, ∃ m ∈ ms, subMask s m = true)
    (hcov : ∀ e : Fin 16, rem.testBit e.val = true → ∃ s ∈ S, s.testBit e.val = true)
    (hrem_lt : ∀ i, 16 ≤ i → rem.testBit i = false) : False := by
  simp only [checkWeight] at hchk
  by_cases htot : weightOfMask w rem = 0
  · simp [htot] at hchk
  · have htot' : (weightOfMask w rem == 0) = false := beq_false_of_ne htot
    rw [htot'] at hchk; simp only [Bool.false_eq_true, ↓reduceIte] at hchk
    have hall := List.all_eq_true.mp hchk
    let bound := (weightOfMask w rem - 1) / k
    have hS_le : ∀ s ∈ S, weightOfMask w (s &&& rem) ≤ bound := by
      intro s hs
      obtain ⟨m, hm, hsub⟩ := hdom s hs
      have hm_le : weightOfMask w (m &&& rem) ≤ bound := of_decide_eq_true (hall m hm)
      have hmono : weightOfMask w (s &&& rem) ≤ weightOfMask w (m &&& rem) := by
        apply weightOfMask_mono; intro i hi
        rw [Nat.testBit_and, Bool.and_eq_true] at hi ⊢
        exact ⟨subMask_iff.mp hsub i hi.1, hi.2⟩
      exact hmono.trans hm_le
    have hfold := list_or_foldl_weight w rem bound S hS_le
    have hrem_sub : ∀ i, rem.testBit i = true → (S.foldl (· ||| ·) 0 &&& rem).testBit i = true := by
      intro i hi
      have hi16 : i < 16 := by
        by_contra hge
        have := hrem_lt i (by omega); simp [this] at hi
      obtain ⟨s, hs, hsi⟩ := hcov ⟨i, hi16⟩ hi
      rw [Nat.testBit_and, Bool.and_eq_true]
      refine ⟨?_, hi⟩
      have hfold_or : ∀ (l : List ℕ) (acc : ℕ),
          (acc.testBit i = true ∨ ∃ x ∈ l, x.testBit i = true) →
          (l.foldl (· ||| ·) acc).testBit i = true := by
        intro l
        induction l with
        | nil => rintro acc (h | ⟨x, hx, _⟩); exact h; simp at hx
        | cons x xs ih =>
          intro acc h
          simp only [List.foldl_cons]
          apply ih
          rcases h with h | ⟨y, hy, hyi⟩
          · left; rw [Nat.testBit_or, h]; simp
          · rcases List.mem_cons.mp hy with rfl | hy'
            · left; rw [Nat.testBit_or, hyi]; simp
            · exact Or.inr ⟨y, hy', hyi⟩
      exact hfold_or S 0 (Or.inr ⟨s, hs, hsi⟩)
    have hwt_le : weightOfMask w rem ≤ S.length * bound :=
      (weightOfMask_mono w rem _ hrem_sub).trans hfold
    have hmul_le : S.length * bound ≤ k * bound := Nat.mul_le_mul_right bound hlen
    have hdiv_le : k * bound ≤ weightOfMask w rem - 1 := Nat.mul_div_le (weightOfMask w rem - 1) k
    omega

def checkBrGo (e : ℕ) (ms : List ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | m :: rest, subs =>
    if m.testBit e then
      match subs with
      | [] => false
      | widx :: srest =>
        checkWeight (65535 ^^^ (m &&& 65535)) 3 ms (wtreeGet weightTree widx) &&
        checkBrGo e ms rest srest
    else checkBrGo e ms rest subs
  | [], _ :: _ => false

lemma checkBrGo_mem (e : ℕ) (ms : List ℕ) :
    ∀ (rest subs : List ℕ), checkBrGo e ms rest subs = true →
      ∀ m ∈ rest, m.testBit e = true →
        ∃ widx, checkWeight (65535 ^^^ (m &&& 65535)) 3 ms (wtreeGet weightTree widx) = true := by
  intro rest
  induction rest with
  | nil => intro subs _ m hm; simp at hm
  | cons a rest ih =>
    intro subs hchk m hm hme
    simp only [checkBrGo] at hchk
    by_cases hae : a.testBit e = true
    · simp only [hae, ↓reduceIte] at hchk
      cases subs with
      | nil => simp at hchk
      | cons widx srest =>
        rw [Bool.and_eq_true] at hchk
        rcases List.mem_cons.mp hm with rfl | hm'
        · exact ⟨widx, hchk.1⟩
        · exact ih srest hchk.2 m hm' hme
    · have hae' : a.testBit e = false := by cases h' : a.testBit e <;> simp_all
      simp only [hae', Bool.false_eq_true, ↓reduceIte] at hchk
      rcases List.mem_cons.mp hm with rfl | hm'
      · simp [hae'] at hme
      · exact ih subs hchk m hm' hme

def checkCert (ms : List ℕ) : CoverCert → Bool
  | .wt idx => checkWeight 65535 4 ms (wtreeGet weightTree idx)
  | .br e subs => decide (e < 16) && checkBrGo e ms ms subs

lemma checkCert_sound (ms : List ℕ) (c : CoverCert) (hchk : checkCert ms c = true)
    (S : List ℕ) (hlen : S.length ≤ 4)
    (hdom : ∀ s ∈ S, ∃ m ∈ ms, subMask s m = true)
    (hcov : ∀ e : Fin 16, ∃ s ∈ S, s.testBit e.val = true) : False := by
  cases c with
  | wt idx =>
    apply checkWeight_sound 65535 4 (by omega) ms (wtreeGet weightTree idx) hchk S hlen hdom
    · intro e _; exact hcov e
    · intro i hi
      apply Nat.testBit_lt_two_pow
      have : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
      omega
  | br e subs =>
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨he16, hbr⟩ := hchk
    obtain ⟨s0, hs0, hs0e⟩ := hcov ⟨e, he16⟩
    obtain ⟨m0, hm0, hsub0⟩ := hdom s0 hs0
    have hm0e : m0.testBit e = true := subMask_iff.mp hsub0 e hs0e
    obtain ⟨widx, hwt⟩ := checkBrGo_mem e ms ms subs hbr m0 hm0 hm0e
    let rem := 65535 ^^^ (m0 &&& 65535)
    let S' := S.erase s0
    have hlen' : S'.length ≤ 3 := by
      have hmem_len : S'.length = S.length - 1 := List.length_erase_of_mem hs0
      have hpos : 1 ≤ S.length := by
        cases S with | nil => simp at hs0 | cons _ _ => simp
      omega
    have hdom' : ∀ s ∈ S', ∃ m ∈ ms, subMask s m = true :=
      fun s hs => hdom s (List.mem_of_mem_erase hs)
    have hcov' : ∀ f : Fin 16, rem.testBit f.val = true → ∃ s ∈ S', s.testBit f.val = true := by
      intro f hf
      have hm0f : m0.testBit f.val = false := by
        dsimp only [rem] at hf
        rw [Nat.testBit_xor, Nat.testBit_and, h_65535_bit f, Bool.and_true] at hf
        cases hm : m0.testBit f.val <;> simp [hm] at hf ⊢
      have hs0f : s0.testBit f.val = false := by
        by_contra h
        have ht : s0.testBit f.val = true := by cases h' : s0.testBit f.val <;> simp_all
        have := subMask_iff.mp hsub0 f.val ht
        simp [hm0f] at this
      obtain ⟨s, hs, hsf⟩ := hcov f
      have hne : s ≠ s0 := by intro heq; subst heq; simp [hs0f] at hsf
      exact ⟨s, (List.mem_erase_of_ne hne).mpr hs, hsf⟩
    have hrem_lt : ∀ i, 16 ≤ i → rem.testBit i = false := by
      intro i hi
      dsimp only [rem]
      have hpow : 2 ^ 16 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
      have h65 : (65535 : ℕ).testBit i = false := Nat.testBit_lt_two_pow (by omega)
      rw [Nat.testBit_xor, Nat.testBit_and, h65]; simp
    exact checkWeight_sound rem 3 (by omega) ms (wtreeGet weightTree widx) hwt S' hlen' hdom' hcov' hrem_lt

def checkPair (i j : ℕ) : Bool :=
  let md := coarseArr.getD i (0, 0)
  let me := coarseArr.getD j (0, 0)
  let row := certRows.getD i #[]
  let c := row.getD (j - i) (.wt 0)
  checkCert (rawTopMasks md me) c

def checkRowGo (i : ℕ) : ℕ → Bool
  | 0 => true
  | d + 1 => checkPair i (i + d) && checkRowGo i d

def checkRow (i : ℕ) : Bool := checkRowGo i (42 - i)

lemma checkRowGo_spec (i : ℕ) : ∀ (n : ℕ), checkRowGo i n = true →
    ∀ d < n, checkPair i (i + d) = true := by
  intro n
  induction n with
  | zero => intro _ d hd; omega
  | succ n ih =>
    intro h d hd
    simp only [checkRowGo, Bool.and_eq_true] at h
    by_cases hdn : d = n
    · subst hdn; exact h.1
    · exact ih h.2 d (by omega)

private lemma h_rows_0 : (List.range 6).all (fun k => checkRow k) = true := by decide +kernel
private lemma h_rows_1 : (List.range 6).all (fun k => checkRow (6 + k)) = true := by decide +kernel
private lemma h_rows_2 : (List.range 6).all (fun k => checkRow (12 + k)) = true := by decide +kernel
private lemma h_rows_3 : (List.range 6).all (fun k => checkRow (18 + k)) = true := by decide +kernel
private lemma h_rows_4 : (List.range 6).all (fun k => checkRow (24 + k)) = true := by decide +kernel
private lemma h_rows_5 : (List.range 6).all (fun k => checkRow (30 + k)) = true := by decide +kernel
private lemma h_rows_6 : (List.range 6).all (fun k => checkRow (36 + k)) = true := by decide +kernel

lemma all_pairs_checked (i j : ℕ) (hi : i < 42) (hj : j < 42) (hle : i ≤ j) :
    checkPair i j = true := by
  have hrow : checkRow i = true := by
    by_cases h0 : i < 6
    · exact List.all_eq_true.mp h_rows_0 i (List.mem_range.mpr h0)
    · by_cases h1 : i < 12
      · have := List.all_eq_true.mp h_rows_1 (i - 6) (List.mem_range.mpr (by omega))
        simpa [show 6 + (i - 6) = i by omega] using this
      · by_cases h2 : i < 18
        · have := List.all_eq_true.mp h_rows_2 (i - 12) (List.mem_range.mpr (by omega))
          simpa [show 12 + (i - 12) = i by omega] using this
        · by_cases h3 : i < 24
          · have := List.all_eq_true.mp h_rows_3 (i - 18) (List.mem_range.mpr (by omega))
            simpa [show 18 + (i - 18) = i by omega] using this
          · by_cases h4 : i < 30
            · have := List.all_eq_true.mp h_rows_4 (i - 24) (List.mem_range.mpr (by omega))
              simpa [show 24 + (i - 24) = i by omega] using this
            · by_cases h5 : i < 36
              · have := List.all_eq_true.mp h_rows_5 (i - 30) (List.mem_range.mpr (by omega))
                simpa [show 30 + (i - 30) = i by omega] using this
              · have := List.all_eq_true.mp h_rows_6 (i - 36) (List.mem_range.mpr (by omega))
                simpa [show 36 + (i - 36) = i by omega] using this
  have hspec := checkRowGo_spec i (42 - i) hrow (j - i) (by omega)
  simpa [show i + (j - i) = j by omega] using hspec

lemma five_top_bound
    (x4 x5 : ℕ) (x6 x7 : Finset ℕ)
    (hx4 : x4 ∈ Finset.image₂ (· &&& ·) {w ∈ x6 | w ≤ x3Val} {w ∈ x6 | w ≤ x3Val})
    (hx5 : x5 ∈ Finset.image₂ (· &&& ·) {w ∈ x6 | w ≤ x3Val} {w ∈ x6 | w ≤ x3Val})
    (hx4_dirty : x4 &&& x2Val ≠ 0)
    (hx5_dirty : x5 &&& x2Val ≠ 0)
    (hx45_ov : x4 &&& x5 &&& x2Val ≠ 0)
    (hbuild : ∀ w ∈ x6 \ insert (x4 ||| b40) (insert (x5 ||| b41) x1Set),
      ∃ a ∈ x6, ∃ b ∈ x6, a < w ∧ b < w ∧ w = a ||| b)
    (hseeds : ∀ w ∈ x6, w < lim42 ∧ w ≠ 0 ∧ ∀ r < 42, w.testBit r = true →
      ∃ a ∈ x6 ∩ insert (x4 ||| b40) (insert (x5 ||| b41) x1Set), a ||| w = w ∧ a.testBit r = true)
    (hcov : ∀ r ∈ insert 40 (Finset.range 16), ∃ b ∈ x7, b.testBit r = true)
    (hB : ∀ b ∈ x7,
      b ∈ Finset.image₂ (fun u v => u &&& v &&& x3Val |||
            if (u ||| v) &&& b401 = b401 then b40 else 0) x6 x6 ∧
      b &&& x2Val = 0) :
    5 ≤ x7.card := by
  let x8 := insert (x4 ||| b40) (insert (x5 ||| b41) x1Set)
  let x9 := {w ∈ x6 | w ≤ x3Val}
  let d0 := x4 ||| b40
  let e0 := x5 ||| b41
  obtain ⟨s1, hs1, s2, hs2, hx4_eq⟩ := Finset.mem_image₂.mp hx4
  obtain ⟨t1, ht1, t2, ht2, hx5_eq⟩ := Finset.mem_image₂.mp hx5
  have hs1_le : s1 ≤ x3Val := (Finset.mem_filter.mp hs1).2
  have ht1_le : t1 ≤ x3Val := (Finset.mem_filter.mp ht1).2
  have hx4_le : x4 ≤ x3Val := by rw [← hx4_eq]; exact Nat.and_le_left.trans hs1_le
  have hx5_le : x5 ≤ x3Val := by rw [← hx5_eq]; exact Nat.and_le_left.trans ht1_le
  have hd0_gt : ¬ d0 ≤ x3Val := by
    have hx3 : x3Val = 2 ^ 40 - 1 := by decide
    have hb : b40 = 2 ^ 40 := by decide
    have hle : b40 ≤ d0 := Nat.right_le_or
    omega
  have he0_gt : ¬ e0 ≤ x3Val := by
    have hx3 : x3Val = 2 ^ 40 - 1 := by decide
    have hb : b41 = 2 ^ 41 := by decide
    have hle : b41 ≤ e0 := Nat.right_le_or
    omega
  have hdirty_sub : ∀ w ∈ x6, ¬ w ≤ x3Val → x4 ||| w = w ∨ x5 ||| w = w := by
    intro w hw hgt
    have hlt := (hseeds w hw).1
    have h401 : w.testBit 40 = true ∨ w.testBit 41 = true := by
      have hiff := h_le_x3_iff w hlt
      cases h40 : w.testBit 40 <;> cases h41 : w.testBit 41
      · exfalso; exact hgt (hiff.mpr ⟨h40, h41⟩)
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inl rfl
    rcases h401 with h40 | h41
    · obtain ⟨a, ha, haw, ha40⟩ := (hseeds w hw).2.2 40 (by omega) h40
      have ha8 := (Finset.mem_inter.mp ha).2
      simp only [x8, Finset.mem_insert] at ha8
      rcases ha8 with rfl | rfl | hax1
      · left; exact bitwise_sub_trans (by rw [← Nat.or_assoc, Nat.or_self]) haw
      · exfalso
        have hx3lim : x3Val < lim42 := by decide
        have hx5_40 : x5.testBit 40 = false := (h_le_x3_iff x5 (by omega)).mp hx5_le |>.1
        have hb41_40 : b41.testBit 40 = false := by decide
        rw [Nat.testBit_or, hx5_40, hb41_40] at ha40; simp at ha40
      · exfalso
        obtain ⟨v, rfl⟩ := (h_x1Set_iff a).mp hax1
        have hx3lim : x3Val < lim42 := by decide
        have hv_40 : (vVal v).testBit 40 = false :=
          (h_le_x3_iff (vVal v) (Nat.lt_of_le_of_lt (h_vVal_le v) hx3lim)).mp (h_vVal_le v) |>.1
        rw [hv_40] at ha40; simp at ha40
    · obtain ⟨a, ha, haw, ha41⟩ := (hseeds w hw).2.2 41 (by omega) h41
      have ha8 := (Finset.mem_inter.mp ha).2
      simp only [x8, Finset.mem_insert] at ha8
      rcases ha8 with rfl | rfl | hax1
      · exfalso
        have hx3lim : x3Val < lim42 := by decide
        have hx4_41 : x4.testBit 41 = false := (h_le_x3_iff x4 (by omega)).mp hx4_le |>.2
        have hb40_41 : b40.testBit 41 = false := by decide
        rw [Nat.testBit_or, hx4_41, hb40_41] at ha41; simp at ha41
      · right; exact bitwise_sub_trans (by rw [← Nat.or_assoc, Nat.or_self]) haw
      · exfalso
        obtain ⟨v, rfl⟩ := (h_x1Set_iff a).mp hax1
        have hx3lim : x3Val < lim42 := by decide
        have hv_41 : (vVal v).testBit 41 = false :=
          (h_le_x3_iff (vVal v) (Nat.lt_of_le_of_lt (h_vVal_le v) hx3lim)).mp (h_vVal_le v) |>.2
        rw [hv_41] at ha41; simp at ha41
  have hdirty_dirty : ∀ u ∈ x6, ∀ v ∈ x6, ¬ u ≤ x3Val → ¬ v ≤ x3Val → u &&& v &&& x2Val ≠ 0 := by
    intro u hu v hv hgu hgv hzero
    have hbit_zero : ∀ a b : ℕ, a ||| u = u → b ||| v = v → a &&& b &&& x2Val = 0 := by
      intro a b hau hbv
      apply Nat.eq_of_testBit_eq; intro i
      have hz := congrArg (fun n => n.testBit i) hzero
      simp only [Nat.testBit_and, Nat.zero_testBit] at hz ⊢
      cases ha : a.testBit i <;> cases hb : b.testBit i <;> cases hx2 : x2Val.testBit i
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · simp
      · have hu' := testBit_of_or_eq hau i ha
        have hv' := testBit_of_or_eq hbv i hb
        rw [hu', hv', hx2] at hz; simp at hz
    rcases hdirty_sub u hu hgu with hu4 | hu5 <;> rcases hdirty_sub v hv hgv with hv4 | hv5
    · exact hx4_dirty (by simpa [Nat.and_self] using hbit_zero x4 x4 hu4 hv4)
    · exact hx45_ov (hbit_zero x4 x5 hu4 hv5)
    · exact hx45_ov (by simpa [Nat.and_comm x4 x5] using hbit_zero x5 x4 hu5 hv4)
    · exact hx5_dirty (by simpa [Nat.and_self] using hbit_zero x5 x5 hu5 hv5)
  let D0 : PureDag := {
    P := x9 ∪ x1Set
    hx1 := Finset.subset_union_right
    hbound := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact (Finset.mem_filter.mp h).2
      · obtain ⟨v, rfl⟩ := (h_x1Set_iff w).mp h; exact h_vVal_le v
    hbuild := by
      intro w hw
      obtain ⟨hwP, hnx1⟩ := Finset.mem_sdiff.mp hw
      have hw9 : w ∈ x9 := (Finset.mem_union.mp hwP).resolve_right hnx1
      have hw6 : w ∈ x6 := (Finset.mem_filter.mp hw9).1
      have hwle : w ≤ x3Val := (Finset.mem_filter.mp hw9).2
      have hnx8 : w ∉ x8 := by
        intro hx
        simp only [x8, Finset.mem_insert] at hx
        rcases hx with rfl | rfl | h
        · exact hd0_gt hwle
        · exact he0_gt hwle
        · exact hnx1 h
      obtain ⟨a, ha, b, hb, haw, hbw, hwab⟩ := hbuild w (Finset.mem_sdiff.mpr ⟨hw6, hnx8⟩)
      exact ⟨a, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha, by omega⟩),
        b, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, by omega⟩), haw, hbw, hwab⟩
  }
  have hs1D : s1 ∈ D0.P := Finset.mem_union_left _ hs1
  have hs2D : s2 ∈ D0.P := Finset.mem_union_left _ hs2
  have ht1D : t1 ∈ D0.P := Finset.mem_union_left _ ht1
  have ht2D : t2 ∈ D0.P := Finset.mem_union_left _ ht2
  obtain ⟨i4, hi4, h4ec, h4cv⟩ := dirty_dominated_by_coarse D0 s1 s2 hs1D hs2D (hx4_eq.symm ▸ hx4_dirty)
  obtain ⟨i5, hi5, h5ec, h5cv⟩ := dirty_dominated_by_coarse D0 t1 t2 ht1D ht2D (hx5_eq.symm ▸ hx5_dirty)
  rw [hx4_eq] at h4ec h4cv
  rw [hx5_eq] at h5ec h5cv
  -- Helper: given ordered (id, ie) with id ≤ ie and corresponding (dx, ex) ∈ {(x4, x5), (x5, x4)},
  -- every b ∈ x7 has (b &&& 65535) dominated by some mask in rawTopMasks (coarseArr[id]) (coarseArr[ie])!
  have hclose : ∀ (id ie : ℕ), id < 42 → ie < 42 → id ≤ ie →
      ∀ (dx ex : ℕ),
        (∀ a ∈ x8, a = dx ||| b40 ∨ a = dx ||| b41 ∨ a = ex ||| b40 ∨ a = ex ||| b41 ∨ a ∈ x1Set) →
        subMask (dx &&& edgeOfMask (cvNat dx)) (coarseArr.getD id (0, 0)).1 = true →
        subMask (cvNat dx) (coarseArr.getD id (0, 0)).2 = true →
        subMask (ex &&& edgeOfMask (cvNat ex)) (coarseArr.getD ie (0, 0)).1 = true →
        subMask (cvNat ex) (coarseArr.getD ie (0, 0)).2 = true →
        5 ≤ x7.card := by
    intro id ie hid hie hle dx ex hx8_cls hdec hdcv heec hecv
    by_contra hlt5
    have hcard4 : x7.card ≤ 4 := by omega
    let md := coarseArr.getD id (0, 0)
    let me := coarseArr.getD ie (0, 0)
    let ms := rawTopMasks md me
    let S := x7.toList.map (fun b => b &&& 65535)
    have hS_len : S.length ≤ 4 := by
      simp only [S, List.length_map, Finset.length_toList]; exact hcard4
    have hS_cov : ∀ e : Fin 16, ∃ s ∈ S, s.testBit e.val = true := by
      intro e
      obtain ⟨b, hb, hbe⟩ := hcov e.val (Finset.mem_insert_of_mem (Finset.mem_range.mpr e.isLt))
      refine ⟨b &&& 65535, List.mem_map.mpr ⟨b, Finset.mem_toList.mpr hb, rfl⟩, ?_⟩
      rw [Nat.testBit_and, hbe, h_65535_bit e]; rfl
    have hS_dom : ∀ s ∈ S, ∃ m ∈ ms, subMask s m = true := by
      intro s hs
      obtain ⟨b, hb_l, rfl⟩ := List.mem_map.mp hs
      have hb : b ∈ x7 := Finset.mem_toList.mp hb_l
      obtain ⟨hb11, hbcl⟩ := hB b hb
      obtain ⟨u0, hu0, v0, hv0, hb_eq⟩ := Finset.mem_image₂.mp hb11
      have huv0_cl : u0 &&& v0 &&& x2Val = 0 := by
        apply Nat.eq_of_testBit_eq; intro i
        have hz := congrArg (fun n => n.testBit i) hbcl
        rw [← hb_eq] at hz
        simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at hz ⊢
        by_cases hi : i < 40
        · have hx3i : x3Val.testBit i = true := h_x3_bit ⟨i, hi⟩
          cases hu : u0.testBit i <;> cases hv : v0.testBit i <;> cases hx2 : x2Val.testBit i <;>
            simp [hu, hv, hx2, hx3i] at hz ⊢
        · have hx2i : x2Val.testBit i = false := by
            have hlt40 : x2Val < 2 ^ 40 := by decide
            exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt40 (Nat.pow_le_pow_right (by omega) (by omega)))
          simp [hx2i]
      have hbit_eq : ∀ e : Fin 16, (b &&& 65535).testBit e.val = (u0 &&& v0).testBit e.val := by
        intro e
        rw [Nat.testBit_and, h_65535_bit e, Bool.and_true, ← hb_eq, Nat.testBit_or, Nat.testBit_and,
          h_x3_bit ⟨e.val, by omega⟩, Bool.and_true]
        have htag : (if (u0 ||| v0) &&& b401 = b401 then b40 else 0).testBit e.val = false := by
          split_ifs
          · rw [h_b40_bit e.val (by omega)]; simp; omega
          · simp
        rw [htag, Bool.or_false]
      -- At least one of u0, v0 is pure (≤ x3Val)!
      have hpure_one : (u0 ≤ x3Val) ∨ (v0 ≤ x3Val) := by
        by_contra hboth; push_neg at hboth
        exact hdirty_dirty u0 hu0 v0 hv0 (by omega) (by omega) huv0_cl
      -- Pick (u, p) with u ∈ x6, p ∈ D0.P, u &&& p &&& x2Val = 0, and same 16-bit mask as b &&& 65535!
      have hex_up : ∃ u ∈ x6, ∃ p ∈ D0.P, u &&& p &&& x2Val = 0 ∧
          ∀ e : Fin 16, (b &&& 65535).testBit e.val = (u &&& p).testBit e.val := by
        rcases hpure_one with hu_le | hv_le
        · refine ⟨v0, hv0, u0, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu0, hu_le⟩), ?_, ?_⟩
          · rw [Nat.and_comm v0 u0]; exact huv0_cl
          · intro e; rw [hbit_eq e, Nat.and_comm]
        · exact ⟨u0, hu0, v0, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hv0, hv_le⟩), huv0_cl, hbit_eq⟩
      obtain ⟨u, hu6, p, hpD, hup_cl, hup_bit⟩ := hex_up
      have hge16 : ∀ i, 16 ≤ i → (b &&& 65535).testBit i = false := by
        intro i hi
        rw [Nat.testBit_and]
        have : (65535 : ℕ).testBit i = false :=
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 65535 < 2 ^ 16) (Nat.pow_le_pow_right (by omega) hi))
        simp [this]
      let SP := seedSet D0 p
      -- Helper: any single star v is in ms!
      have hstar_in : ∀ v : Fin 11, starList.getD v.val 0 ∈ ms := fun v => by
        apply List.mem_append_left; apply List.mem_append_left
        apply List.mem_append_left; apply List.mem_append_left
        have hlt : v.val < starList.length := by rw [h_starList_len]; exact v.isLt
        rw [List.getD_eq_getElem _ _ hlt]
        exact List.getElem_mem hlt
      -- Case 1: SP.card ≤ 1
      by_cases hP1 : SP.card ≤ 1
      · rcases Finset.card_le_one_iff_subset_singleton.mp hP1 with ⟨v, hv⟩
        refine ⟨starList.getD v.val 0, hstar_in v, ?_⟩
        rw [subMask_iff]; intro i hi
        have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
        let e : Fin 16 := ⟨i, hi16⟩
        rw [hup_bit e, Nat.testBit_and, Bool.and_eq_true] at hi
        obtain ⟨w, hwP, hwe⟩ := (seedSet_testBit D0 p hpD e.val).mp hi.2
        have hwv : w = v := Finset.mem_singleton.mp (hv hwP)
        subst hwv
        rw [h_starList_bit w e]; exact hwe
      -- Case 2: 2 ≤ SP.card!
      have hPge2 : 2 ≤ SP.card := by omega
      -- Collect pure seeds of u: SQ = {q : Fin 11 | vVal q ||| u = u}
      let SQ : Finset (Fin 11) := Finset.univ.filter (fun q : Fin 11 => vVal q ||| u = u)
      -- For every q ∈ SQ and w ∈ SP, adj q w = true!
      have hSQ_adj : ∀ q ∈ SQ, ∀ w ∈ SP, adj q w = true := by
        intro q hq w hw
        have hqu : vVal q ||| u = u := (Finset.mem_filter.mp hq).2
        by_contra hna
        have hf : adj q w = false := by
          cases h' : adj q w
          · rfl
          · exact (hna h').elim
        obtain ⟨m, hm16, hqm, hwm⟩ := h_nonedge_bad q w hf
        have hum : u.testBit m.val = true := testBit_of_or_eq hqu m.val hqm
        have hpm : p.testBit m.val = true := (seedSet_testBit D0 p hpD m.val).mpr ⟨w, hw, hwm⟩
        have hx2m : x2Val.testBit m.val = true := by rw [h_x2_bit m]; simp [hm16]
        have h0 := congrArg (fun n => n.testBit m.val) hup_cl
        simp only [Nat.testBit_and, Nat.zero_testBit, hum, hpm, hx2m] at h0; simp at h0
      -- Therefore SQ.card ≤ 1 by C4-freeness!
      have hSQ1 : SQ.card ≤ 1 := by
        by_contra hgt
        obtain ⟨q1, hq1, q2, hq2, hneQ⟩ := Finset.one_lt_card.mp (by omega : 1 < SQ.card)
        obtain ⟨w1, hw1, w2, hw2, hneW⟩ := Finset.one_lt_card.mp (by omega : 1 < SP.card)
        have := h_c4_free q1 q2 w1 w2 hneQ hneW
          (hSQ_adj q1 hq1 w1 hw1) (hSQ_adj q1 hq1 w2 hw2) (hSQ_adj q2 hq2 w1 hw1)
        simp [hSQ_adj q2 hq2 w2 hw2] at this
      -- Check if dx ||| u = u (hasD) and ex ||| u = u (hasE)!
      have h_dx_cv : dx ||| u = u → ∀ w ∈ SP, (cvNat dx).testBit w.val = true := by
        intro hdu w hw
        rw [cvNat_testBit_fin]
        apply Nat.eq_of_testBit_eq; intro bit
        have h0 := congrArg (fun n => n.testBit bit) hup_cl
        simp only [Nat.testBit_and, Nat.zero_testBit] at h0 ⊢
        cases hwb : (vVal w).testBit bit <;> cases hdb : dx.testBit bit <;> cases hx2b : x2Val.testBit bit
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · have hu' := testBit_of_or_eq hdu bit hdb
          have hp' := (seedSet_testBit D0 p hpD bit).mpr ⟨w, hw, hwb⟩
          rw [hu', hp', hx2b] at h0; simp at h0
      have h_ex_cv : ex ||| u = u → ∀ w ∈ SP, (cvNat ex).testBit w.val = true := by
        intro heu w hw
        rw [cvNat_testBit_fin]
        apply Nat.eq_of_testBit_eq; intro bit
        have h0 := congrArg (fun n => n.testBit bit) hup_cl
        simp only [Nat.testBit_and, Nat.zero_testBit] at h0 ⊢
        cases hwb : (vVal w).testBit bit <;> cases heb : ex.testBit bit <;> cases hx2b : x2Val.testBit bit
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · simp
        · have hu' := testBit_of_or_eq heu bit heb
          have hp' := (seedSet_testBit D0 p hpD bit).mpr ⟨w, hw, hwb⟩
          rw [hu', hp', hx2b] at h0; simp at h0
      -- For every edge e with (u &&& p).testBit e.val = true, u.testBit e.val comes from dx, ex, or some q ∈ SQ!
      have hu_edge_src : ∀ e : Fin 16, (u &&& p).testBit e.val = true →
          (dx ||| u = u ∧ dx.testBit e.val = true) ∨
          (ex ||| u = u ∧ ex.testBit e.val = true) ∨
          (∃ q ∈ SQ, (vVal q).testBit e.val = true) := by
        intro e he
        rw [Nat.testBit_and, Bool.and_eq_true] at he
        obtain ⟨a, ha, hau, hae⟩ := (hseeds u hu6).2.2 e.val (by omega) he.1
        have ha8 : a ∈ x8 := (Finset.mem_inter.mp ha).2
        have hne_b40 : b40.testBit e.val = false := by rw [h_b40_bit e.val (by omega)]; simp; omega
        have hne_b41 : b41.testBit e.val = false := by rw [h_b41_bit e.val (by omega)]; simp; omega
        rcases hx8_cls a ha8 with rfl | rfl | rfl | rfl | hax1
        · left
          refine ⟨bitwise_sub_trans (by rw [← Nat.or_assoc, Nat.or_self]) hau, ?_⟩
          rw [Nat.testBit_or, hne_b40, Bool.or_false] at hae; exact hae
        · left
          refine ⟨bitwise_sub_trans (by rw [← Nat.or_assoc, Nat.or_self]) hau, ?_⟩
          rw [Nat.testBit_or, hne_b41, Bool.or_false] at hae; exact hae
        · right; left
          refine ⟨bitwise_sub_trans (by rw [← Nat.or_assoc, Nat.or_self]) hau, ?_⟩
          rw [Nat.testBit_or, hne_b40, Bool.or_false] at hae; exact hae
        · right; left
          refine ⟨bitwise_sub_trans (by rw [← Nat.or_assoc, Nat.or_self]) hau, ?_⟩
          rw [Nat.testBit_or, hne_b41, Bool.or_false] at hae; exact hae
        · right; right
          obtain ⟨q, rfl⟩ := (h_x1Set_iff a).mp hax1
          exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hau⟩, hae⟩
      -- Helper: if w ∈ SP and (dx ||| u = u), then (u &&& p).testBit e.val = true with dx.testBit e.val = true implies md.1.testBit e.val = true!
      have hdx_in_md1 : dx ||| u = u → ∀ e : Fin 16, dx.testBit e.val = true → p.testBit e.val = true →
          md.1.testBit e.val = true := by
        intro hdu e hde hpe
        obtain ⟨w, hwP, hwe⟩ := (seedSet_testBit D0 p hpD e.val).mp hpe
        have hwcv := h_dx_cv hdu w hwP
        have h1 : (dx &&& edgeOfMask (cvNat dx)).testBit e.val = true := by
          rw [Nat.testBit_and, Bool.and_eq_true]
          exact ⟨hde, (edgeOfMask_testBit (cvNat dx) e).mpr ⟨w, hwcv, hwe⟩⟩
        exact subMask_iff.mp hdec e.val h1
      have hex_in_me1 : ex ||| u = u → ∀ e : Fin 16, ex.testBit e.val = true → p.testBit e.val = true →
          me.1.testBit e.val = true := by
        intro heu e hee hpe
        obtain ⟨w, hwP, hwe⟩ := (seedSet_testBit D0 p hpD e.val).mp hpe
        have hwcv := h_ex_cv heu w hwP
        have h1 : (ex &&& edgeOfMask (cvNat ex)).testBit e.val = true := by
          rw [Nat.testBit_and, Bool.and_eq_true]
          exact ⟨hee, (edgeOfMask_testBit (cvNat ex) e).mpr ⟨w, hwcv, hwe⟩⟩
        exact subMask_iff.mp heec e.val h1
      -- Helper: for any mask P with ∀ w ∈ SP, P.testBit w.val = true, every edge bit of p is in edgeOfMask P!
      have hp_in_eP : ∀ P : ℕ, (∀ w ∈ SP, P.testBit w.val = true) →
          ∀ e : Fin 16, p.testBit e.val = true → (edgeOfMask P).testBit e.val = true := by
        intro P hP e hpe
        obtain ⟨w, hwP, hwe⟩ := (seedSet_testBit D0 p hpD e.val).mp hpe
        exact (edgeOfMask_testBit P e).mpr ⟨w, hP w hwP, hwe⟩
      -- Case split on SQ = ∅ vs SQ = {q} and (dx ||| u = u, ex ||| u = u)!
      by_cases hSQe : SQ = ∅
      · by_cases hdu : dx ||| u = u
        · by_cases heu : ex ||| u = u
          · -- q0[2]: (md.1 ||| me.1) &&& edgeOfMask (md.2 &&& me.2)
            refine ⟨(md.1 ||| me.1) &&& edgeOfMask (md.2 &&& me.2), ?_, ?_⟩
            · apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              apply List.mem_append_right; simp
            · rw [subMask_iff]; intro i hi
              have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
              let e : Fin 16 := ⟨i, hi16⟩
              rw [hup_bit e] at hi
              have hpe : p.testBit e.val = true := (Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi).2
              rw [Nat.testBit_and, Nat.testBit_or, Bool.and_eq_true, Bool.or_eq_true]
              refine ⟨?_, hp_in_eP (md.2 &&& me.2) (fun w hw => by
                rw [Nat.testBit_and, subMask_iff.mp hdcv w.val (h_dx_cv hdu w hw),
                  subMask_iff.mp hecv w.val (h_ex_cv heu w hw)]; rfl) e hpe⟩
              rcases hu_edge_src e hi with ⟨_, hde⟩ | ⟨_, hee⟩ | ⟨q, hq, _⟩
              · exact Or.inl (hdx_in_md1 hdu e hde hpe)
              · exact Or.inr (hex_in_me1 heu e hee hpe)
              · simp [hSQe] at hq
          · -- q0[0]: md.1 &&& edgeOfMask md.2
            refine ⟨md.1 &&& edgeOfMask md.2, ?_, ?_⟩
            · apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              apply List.mem_append_right; simp
            · rw [subMask_iff]; intro i hi
              have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
              let e : Fin 16 := ⟨i, hi16⟩
              rw [hup_bit e] at hi
              have hpe : p.testBit e.val = true := (Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi).2
              rw [Nat.testBit_and, Bool.and_eq_true]
              refine ⟨?_, hp_in_eP md.2 (fun w hw => subMask_iff.mp hdcv w.val (h_dx_cv hdu w hw)) e hpe⟩
              rcases hu_edge_src e hi with ⟨_, hde⟩ | ⟨h', _⟩ | ⟨q, hq, _⟩
              · exact hdx_in_md1 hdu e hde hpe
              · exact (heu h').elim
              · simp [hSQe] at hq
        · by_cases heu : ex ||| u = u
          · -- q0[1]: me.1 &&& edgeOfMask me.2
            refine ⟨me.1 &&& edgeOfMask me.2, ?_, ?_⟩
            · apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              apply List.mem_append_right; simp
            · rw [subMask_iff]; intro i hi
              have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
              let e : Fin 16 := ⟨i, hi16⟩
              rw [hup_bit e] at hi
              have hpe : p.testBit e.val = true := (Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi).2
              rw [Nat.testBit_and, Bool.and_eq_true]
              refine ⟨?_, hp_in_eP me.2 (fun w hw => subMask_iff.mp hecv w.val (h_ex_cv heu w hw)) e hpe⟩
              rcases hu_edge_src e hi with ⟨h', _⟩ | ⟨_, hee⟩ | ⟨q, hq, _⟩
              · exact (hdu h').elim
              · exact hex_in_me1 heu e hee hpe
              · simp [hSQe] at hq
          · -- Neither dx, ex, nor SQ: b &&& 65535 = 0 ≤ star 0!
            refine ⟨starList.getD 0 0, hstar_in 0, ?_⟩
            rw [subMask_iff]; intro i hi
            have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
            let e : Fin 16 := ⟨i, hi16⟩
            rw [hup_bit e] at hi
            rcases hu_edge_src e hi with ⟨h', _⟩ | ⟨h', _⟩ | ⟨q, hq, _⟩
            · exact (hdu h').elim
            · exact (heu h').elim
            · simp [hSQe] at hq
      · -- SQ = {q}!
        obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hSQe
        have hSQeq : SQ = {q} := Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hq, fun w hw => Finset.card_le_one.mp hSQ1 w hw q hq⟩
        obtain ⟨w1, hw1, w2, hw2, hneW⟩ := Finset.one_lt_card.mp (by omega : 1 < SP.card)
        have hq_adj_bit : ∀ w ∈ SP, (adjList.getD q.val 0).testBit w.val = true := fun w hw => by
          rw [h_adjList_bit q w]; exact hSQ_adj q hq w hw
        by_cases hdu : dx ||| u = u
        · by_cases heu : ex ||| u = u
          · -- qde at q
            let P := adjList.getD q.val 0 &&& (md.2 &&& me.2)
            have hP_sub : ∀ w ∈ SP, P.testBit w.val = true := fun w hw => by
              dsimp only [P]
              rw [Nat.testBit_and, Nat.testBit_and, hq_adj_bit w hw,
                subMask_iff.mp hdcv w.val (h_dx_cv hdu w hw),
                subMask_iff.mp hecv w.val (h_ex_cv heu w hw)]; rfl
            have h2b : hasTwoBits P = true :=
              hasTwoBits_of_two (fun h => hneW (Fin.ext h)) (hP_sub w1 hw1) (hP_sub w2 hw2)
            refine ⟨((md.1 ||| me.1) &&& edgeOfMask P) ||| (starList.getD q.val 0 &&& edgeOfMask P), ?_, ?_⟩
            · apply List.mem_append_right
              exact mem_topMasksLoop_of_idx (md.1 ||| me.1) (md.2 &&& me.2) starList adjList q.val
                (by rw [h_starList_len]; exact q.isLt) (by rw [h_adjList_len]; exact q.isLt) h2b
            · rw [subMask_iff]; intro i hi
              have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
              let e : Fin 16 := ⟨i, hi16⟩
              rw [hup_bit e] at hi
              have hpe : p.testBit e.val = true := (Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi).2
              have heP := hp_in_eP P hP_sub e hpe
              rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Nat.testBit_or, Bool.or_eq_true,
                Bool.and_eq_true, Bool.and_eq_true, Bool.or_eq_true]
              rcases hu_edge_src e hi with ⟨_, hde⟩ | ⟨_, hee⟩ | ⟨q', hq', hq'e⟩
              · exact Or.inl ⟨Or.inl (hdx_in_md1 hdu e hde hpe), heP⟩
              · exact Or.inl ⟨Or.inr (hex_in_me1 heu e hee hpe), heP⟩
              · rw [hSQeq, Finset.mem_singleton] at hq'; subst hq'
                exact Or.inr ⟨by rw [h_starList_bit q' e]; exact hq'e, heP⟩
          · -- qd at q
            let P := adjList.getD q.val 0 &&& md.2
            have hP_sub : ∀ w ∈ SP, P.testBit w.val = true := fun w hw => by
              dsimp only [P]
              rw [Nat.testBit_and, hq_adj_bit w hw, subMask_iff.mp hdcv w.val (h_dx_cv hdu w hw)]; rfl
            have h2b : hasTwoBits P = true :=
              hasTwoBits_of_two (fun h => hneW (Fin.ext h)) (hP_sub w1 hw1) (hP_sub w2 hw2)
            refine ⟨(md.1 &&& edgeOfMask P) ||| (starList.getD q.val 0 &&& edgeOfMask P), ?_, ?_⟩
            · apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
              exact mem_topMasksLoop_of_idx md.1 md.2 starList adjList q.val
                (by rw [h_starList_len]; exact q.isLt) (by rw [h_adjList_len]; exact q.isLt) h2b
            · rw [subMask_iff]; intro i hi
              have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
              let e : Fin 16 := ⟨i, hi16⟩
              rw [hup_bit e] at hi
              have hpe : p.testBit e.val = true := (Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi).2
              have heP := hp_in_eP P hP_sub e hpe
              rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Bool.or_eq_true,
                Bool.and_eq_true, Bool.and_eq_true]
              rcases hu_edge_src e hi with ⟨_, hde⟩ | ⟨h', _⟩ | ⟨q', hq', hq'e⟩
              · exact Or.inl ⟨hdx_in_md1 hdu e hde hpe, heP⟩
              · exact (heu h').elim
              · rw [hSQeq, Finset.mem_singleton] at hq'; subst hq'
                exact Or.inr ⟨by rw [h_starList_bit q' e]; exact hq'e, heP⟩
        · by_cases heu : ex ||| u = u
          · -- qe at q
            let P := adjList.getD q.val 0 &&& me.2
            have hP_sub : ∀ w ∈ SP, P.testBit w.val = true := fun w hw => by
              dsimp only [P]
              rw [Nat.testBit_and, hq_adj_bit w hw, subMask_iff.mp hecv w.val (h_ex_cv heu w hw)]; rfl
            have h2b : hasTwoBits P = true :=
              hasTwoBits_of_two (fun h => hneW (Fin.ext h)) (hP_sub w1 hw1) (hP_sub w2 hw2)
            refine ⟨(me.1 &&& edgeOfMask P) ||| (starList.getD q.val 0 &&& edgeOfMask P), ?_, ?_⟩
            · apply List.mem_append_left; apply List.mem_append_right
              exact mem_topMasksLoop_of_idx me.1 me.2 starList adjList q.val
                (by rw [h_starList_len]; exact q.isLt) (by rw [h_adjList_len]; exact q.isLt) h2b
            · rw [subMask_iff]; intro i hi
              have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
              let e : Fin 16 := ⟨i, hi16⟩
              rw [hup_bit e] at hi
              have hpe : p.testBit e.val = true := (Nat.testBit_and .. ▸ Bool.and_eq_true .. |>.mp hi).2
              have heP := hp_in_eP P hP_sub e hpe
              rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, Bool.or_eq_true,
                Bool.and_eq_true, Bool.and_eq_true]
              rcases hu_edge_src e hi with ⟨h', _⟩ | ⟨_, hee⟩ | ⟨q', hq', hq'e⟩
              · exact (hdu h').elim
              · exact Or.inl ⟨hex_in_me1 heu e hee hpe, heP⟩
              · rw [hSQeq, Finset.mem_singleton] at hq'; subst hq'
                exact Or.inr ⟨by rw [h_starList_bit q' e]; exact hq'e, heP⟩
          · -- pure star at q!
            refine ⟨starList.getD q.val 0, hstar_in q, ?_⟩
            rw [subMask_iff]; intro i hi
            have hi16 : i < 16 := by by_contra hge; have := hge16 i (by omega); simp [this] at hi
            let e : Fin 16 := ⟨i, hi16⟩
            rw [hup_bit e] at hi
            rcases hu_edge_src e hi with ⟨h', _⟩ | ⟨h', _⟩ | ⟨q', hq', hq'e⟩
            · exact (hdu h').elim
            · exact (heu h').elim
            · rw [hSQeq, Finset.mem_singleton] at hq'; subst hq'
              rw [h_starList_bit q' e]; exact hq'e
    have hchk := all_pairs_checked id ie hid hie hle
    exact checkCert_sound ms ((certRows.getD id #[]).getD (ie - id) (.wt 0)) hchk S hS_len hS_dom hS_cov
  by_cases hord : i4 ≤ i5
  · exact hclose i4 i5 hi4 hi5 hord x4 x5 (fun a ha => by
      simp only [x8, Finset.mem_insert] at ha
      rcases ha with rfl | rfl | h
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) h4ec h4cv h5ec h5cv
  · exact hclose i5 i4 hi5 hi4 (by omega) x5 x4 (fun a ha => by
      simp only [x8, Finset.mem_insert] at ha
      rcases ha with rfl | rfl | h
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))) h5ec h5cv h4ec h4cv

end PEqualNP.Outside.L_meta_19010_aux

theorem PEqualNP.Outside.L_meta_19010 : have x1 : Finset ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset; have x2 : ℕ := (1099511562240 : ℕ); have x3 : ℕ := (1099511627775 : ℕ); ∀ (x4 x5 : ℕ) (x6 x7 : Finset ℕ),   have x8 : Finset ℕ := Insert.insert (x4 ||| (1099511627776 : ℕ)) (Insert.insert (x5 ||| (2199023255552 : ℕ)) x1);   have x9 : Finset ℕ := {x9 ∈ x6 | x9 ≤ x3};   have x10 : Finset ℕ := Finset.image₂ (fun (x10 x11 : ℕ) => x10 &&& x11) x9 x9;   have x11 : Finset ℕ := Finset.image₂ (fun (x11 x12 : ℕ) => x11 &&& x12 &&& x3 ||| if (x11 ||| x12) &&& (3298534883328 : ℕ) = (3298534883328 : ℕ) then (1099511627776 : ℕ) else (0 : ℕ)) x6 x6;   x4 ∈ x10 → x5 ∈ x10 → x4 &&& x2 ≠ (0 : ℕ) → x5 &&& x2 ≠ (0 : ℕ) → x4 &&& x5 &&& x2 ≠ (0 : ℕ) → (∃ x17 ∈ x1, (x4 ||| x5) &&& x17 &&& x2 = (0 : ℕ)) → (∃ x18 ∈ x6 \ x8, x18 &&& (3298534883328 : ℕ) = (3298534883328 : ℕ)) → (∀ x19 ∈ x6 \ x8, ∃ x21 ∈ x6, ∃ x22 ∈ x6, x21 < x19 ∧ x22 < x19 ∧ x19 = x21 ||| x22) → (∀ x20 ∈ x6, x20 < (4398046511104 : ℕ) ∧ x20 ≠ (0 : ℕ) ∧ ∀ x22 < (42 : ℕ), x20.testBit x22 = Bool.true → ∃ x25 ∈ x6 ∩ x8, x25 ||| x20 = x20 ∧ x25.testBit x22 = Bool.true) → (1 : ℕ) ≤ (x6 \ x8).card → (x6 \ x8).card + (2 : ℕ) * x7.card ≤ (20 : ℕ) → x7.card ≤ (6 : ℕ) → (∀ x24 ∈ Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)), ∃ x26 ∈ x7, x26.testBit x24 = Bool.true) → (∀ x25 ∈ x7, x25 ∈ x11 ∧ x25 &&& x2 = (0 : ℕ) ∧ ∀ x27 ∈ x11, x27 &&& x2 = (0 : ℕ) → x25 ||| x27 = x27 → x27 = x25) → (∀ x26 ∈ x7, ∃ x28 < (41 : ℕ), x26.testBit x28 = Bool.true ∧ ∀ x29 ∈ x7, x29.testBit x28 = Bool.true → x29 = x26) → False := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 hx4 hx5 hx4d hx5d hx45 _ _ hbuild hseeds _ hsum _ hcov hB _
  have h16 : 16 ≤ x7.card + (x6 \ x8).card :=
    PEqualNP.Outside.L_meta_19010_aux.main_edge_bound x4 x5 x6 x7 hx4 hx5 hx4d hx5d hx45
      hbuild hseeds hcov (fun b hb => ⟨(hB b hb).1, (hB b hb).2.1⟩)
  have h5 : 5 ≤ x7.card :=
    PEqualNP.Outside.L_meta_19010_aux.five_top_bound x4 x5 x6 x7 hx4 hx5 hx4d hx5d hx45
      hbuild hseeds hcov (fun b hb => ⟨(hB b hb).1, (hB b hb).2.1⟩)
  omega
