import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19012_aux

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

end PEqualNP.Outside.L_meta_19012_aux

theorem PEqualNP.Outside.L_meta_19012 :
    have x1 : Finset ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].toFinset; have x2 : ℕ := (1099511562240 : ℕ); have x3 : ℕ := (1099511627775 : ℕ); ∀ (x4 x5 : ℕ) (x6 x7 : Finset ℕ),   have x8 : Finset ℕ := Insert.insert (x4 ||| (1099511627776 : ℕ)) (Insert.insert (x5 ||| (2199023255552 : ℕ)) x1);   have x9 : Finset ℕ := {x9 ∈ x6 | x9 ≤ x3};   have x10 : Finset ℕ := Finset.image₂ (fun (x10 x11 : ℕ) => x10 &&& x11) x9 x9;   have x11 : Finset ℕ := Finset.image₂ (fun (x11 x12 : ℕ) => x11 &&& x12 &&& x3 ||| if (x11 ||| x12) &&& (3298534883328 : ℕ) = (3298534883328 : ℕ) then (1099511627776 : ℕ) else (0 : ℕ)) x6 x6;   x4 ∈ x10 → x5 ∈ x10 → x4 &&& x2 ≠ (0 : ℕ) → x5 &&& x2 ≠ (0 : ℕ) → x4 &&& x5 &&& x2 ≠ (0 : ℕ) → (∃ x17 ∈ x1, (x4 ||| x5) &&& x17 &&& x2 = (0 : ℕ)) → (∃ x18 ∈ x6 \ x8, x18 &&& (3298534883328 : ℕ) = (3298534883328 : ℕ)) → (∀ x19 ∈ x6 \ x8, ∃ x21 ∈ x6, ∃ x22 ∈ x6, x21 < x19 ∧ x22 < x19 ∧ x19 = x21 ||| x22) → (∀ x20 ∈ x6, x20 < (4398046511104 : ℕ) ∧ x20 ≠ (0 : ℕ) ∧ ∀ x22 < (42 : ℕ), x20.testBit x22 = Bool.true → ∃ x25 ∈ x6 ∩ x8, x25 ||| x20 = x20 ∧ x25.testBit x22 = Bool.true) → (1 : ℕ) ≤ (x6 \ x8).card → (x6 \ x8).card + (2 : ℕ) * x7.card ≤ (20 : ℕ) → (7 : ℕ) ≤ x7.card → x7.card ≤ (9 : ℕ) → (∀ x25 ∈ Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)), ∃ x27 ∈ x7, x27.testBit x25 = Bool.true) → (∀ x26 ∈ x7, x26 ∈ x11 ∧ x26 &&& x2 = (0 : ℕ) ∧ ∀ x28 ∈ x11, x28 &&& x2 = (0 : ℕ) → x26 ||| x28 = x28 → x28 = x26) → (∀ x27 ∈ x7, ∃ x29 < (41 : ℕ), x27.testBit x29 = Bool.true ∧ ∀ x30 ∈ x7, x30.testBit x29 = Bool.true → x30 = x27) → False := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 hx4 hx5 hx4d hx5d hx45 _ _ hbuild hseeds _ hsum hge7 _ hcov hB _
  have h16 : 16 ≤ x7.card + (x6 \ x8).card :=
    PEqualNP.Outside.L_meta_19012_aux.main_edge_bound x4 x5 x6 x7 hx4 hx5 hx4d hx5d hx45
      hbuild hseeds hcov (fun b hb => ⟨(hB b hb).1, (hB b hb).2.1⟩)
  omega
