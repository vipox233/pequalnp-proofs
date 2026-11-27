import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_359_aux

open Classical

def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def queries (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Set (V → Bool) :=
  {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}

def cert {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) : Prop :=
  shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
    (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)

abbrev Vec (k : ℕ) := Fin k → ZMod 2

def IsMatching (k : ℕ) (v : Vec k → Vec k) : Prop :=
  ∀ x, v (v x) = x ∧ v x ≠ x

def HasTree (k : ℕ) (v : Vec k → Vec k) : Prop :=
  ∃ (N J : Finset (List Bool)) (q : List Bool → Vec k → Bool) (out : List Bool → Finset (Vec k)),
    cert (queries (Vec k)) (fun x a => a = {x, v x}) N J q out ∧ 2 * (N \ J).card = 2 ^ k

def Good (k : ℕ) (v : Vec k → Vec k) : Prop :=
  IsMatching k v ∧ HasTree k v

noncomputable def count (k : ℕ) : ℕ :=
  Nat.card {v : Vec k → Vec k // Good k v}

noncomputable def gauss (k d : ℕ) : ℕ :=
  Nat.card {A : Submodule (ZMod 2) (Vec k) // Module.finrank (ZMod 2) A = d}

lemma card_vec (k : ℕ) : Fintype.card (Vec k) = 2 ^ k := by
  simp [Vec, ZMod.card]

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

lemma zmod2_eq_of_decide_eq {a c b : ZMod 2} (h : decide (a = b) = decide (c = b)) : a = c := by
  have hiff : (a = b) ↔ (c = b) := by
    have := congrArg (· = true) h
    simpa [decide_eq_true_eq] using this
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases c with rfl | rfl <;>
    rcases zmod2_cases b with rfl | rfl <;> simp_all

inductive PTree (V O : Type) where
  | leaf : O → PTree V O
  | node : (V → Bool) → PTree V O → PTree V O → PTree V O

namespace PTree

def eval {V O : Type} : PTree V O → V → O
  | leaf o, _ => o
  | node f l r, x => if f x = false then l.eval x else r.eval x

def evalPath {V O : Type} : PTree V O → V → List Bool
  | leaf _, _ => []
  | node f l r, x => if f x = false then false :: l.evalPath x else true :: r.evalPath x

def leafPaths {V O : Type} : PTree V O → Finset (List Bool)
  | leaf _ => {[]}
  | node _ l r => l.leafPaths.image (false :: ·) ∪ r.leafPaths.image (true :: ·)

def leafCount {V O : Type} : PTree V O → ℕ
  | leaf _ => 1
  | node _ l r => l.leafCount + r.leafCount

def queriesOk {V O : Type} (qs : Set (V → Bool)) : PTree V O → Prop
  | leaf _ => True
  | node f l r => f ∈ qs ∧ l.queriesOk qs ∧ r.queriesOk qs

def nodes {V O : Type} : PTree V O → Finset (List Bool)
  | leaf _ => {[]}
  | node _ l r => insert [] (l.nodes.image (false :: ·) ∪ r.nodes.image (true :: ·))

def internals {V O : Type} : PTree V O → Finset (List Bool)
  | leaf _ => ∅
  | node _ l r => insert [] (l.internals.image (false :: ·) ∪ r.internals.image (true :: ·))

def queryAt {V O : Type} : PTree V O → List Bool → V → Bool
  | leaf _, _, _ => false
  | node f _ _, [], x => f x
  | node _ l _, false :: p, x => l.queryAt p x
  | node _ _ r, true :: p, x => r.queryAt p x

def outAt {V O : Type} [Inhabited O] : PTree V O → List Bool → O
  | leaf o, _ => o
  | node _ _ _, [] => default
  | node _ l _, false :: p => l.outAt p
  | node _ _ r, true :: p => r.outAt p

lemma leafPaths_card {V O : Type} (t : PTree V O) : t.leafPaths.card = t.leafCount := by
  induction t with
  | leaf o => simp [leafPaths, leafCount]
  | node f l r ihl ihr =>
    simp only [leafPaths, leafCount]
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2),
      Finset.card_image_of_injective _ (fun _ _ h => List.cons.inj h |>.2), ihl, ihr]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rcases Finset.mem_image.mp hp1 with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hp2 with ⟨b, _, h⟩
    cases h

lemma leafCount_pos {V O : Type} (t : PTree V O) : 0 < t.leafCount := by
  induction t with
  | leaf _ => simp [leafCount]
  | node _ l r ihl ihr => simp [leafCount]; omega

lemma leafPaths_nonempty {V O : Type} (t : PTree V O) : t.leafPaths.Nonempty := by
  rw [← Finset.card_pos, leafPaths_card]
  exact leafCount_pos t

lemma evalPath_mem_leafPaths {V O : Type} (t : PTree V O) (x : V) :
    t.evalPath x ∈ t.leafPaths := by
  induction t with
  | leaf o => simp [evalPath, leafPaths]
  | node f l r ihl ihr =>
    simp only [evalPath, leafPaths]
    split_ifs
    · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ihl)
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ihr)

lemma eval_eq_of_evalPath_eq {V O : Type} (t : PTree V O) {x y : V}
    (h : t.evalPath x = t.evalPath y) : t.eval x = t.eval y := by
  induction t with
  | leaf o => rfl
  | node f l r ihl ihr =>
    simp only [evalPath, eval] at h ⊢
    by_cases hx : f x = false <;> by_cases hy : f y = false <;> simp_all

lemma nil_mem_nodes {V O : Type} (t : PTree V O) : [] ∈ t.nodes := by
  cases t <;> simp [nodes]

lemma internals_subset_nodes {V O : Type} (t : PTree V O) : t.internals ⊆ t.nodes := by
  induction t with
  | leaf _ => simp [internals, nodes]
  | node f l r ihl ihr =>
    intro p hp
    simp only [internals, nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, ihl hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, ihr hq, rfl⟩)

lemma to_shape {V O : Type} (t : PTree V O) : shape t.nodes t.internals := by
  refine ⟨nil_mem_nodes t, internals_subset_nodes t, ?_, ?_⟩
  · induction t with
    | leaf _ =>
      intro p b h
      simp only [nodes, Finset.mem_singleton] at h
      exact absurd h (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil b []))
    | node f l r ihl ihr =>
      intro p b h
      simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at h
      rcases h with h0 | ⟨q, hq, hqeq⟩ | ⟨q, hq, hqeq⟩
      · exact absurd h0 (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil b []))
      · cases p with
        | nil => simp [internals]
        | cons c p' =>
          simp only [List.cons_append, List.cons.injEq] at hqeq
          rcases hqeq with ⟨rfl, rfl⟩
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (ihl p' b hq)))
      · cases p with
        | nil => simp [internals]
        | cons c p' =>
          simp only [List.cons_append, List.cons.injEq] at hqeq
          rcases hqeq with ⟨rfl, rfl⟩
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (ihr p' b hq)))
  · induction t with
    | leaf _ => intro p hp; simp [internals] at hp
    | node f l r ihl ihr =>
      intro p hp
      simp only [internals, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · constructor
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (nil_mem_nodes l)))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (nil_mem_nodes r)))
      · obtain ⟨h0, h1⟩ := ihl q hq
        constructor
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h0))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h1))
      · obtain ⟨h0, h1⟩ := ihr q hq
        constructor
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h0))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h1))

lemma nodes_sdiff_internals {V O : Type} (t : PTree V O) :
    t.nodes \ t.internals = t.leafPaths := by
  induction t with
  | leaf _ => simp [nodes, internals, leafPaths]
  | node f l r ihl ihr =>
    ext p
    simp only [Finset.mem_sdiff, nodes, internals, leafPaths, Finset.mem_insert,
      Finset.mem_union, Finset.mem_image]
    cases p with
    | nil => simp
    | cons b p' =>
      cases b
      · simp only [reduceCtorEq, List.cons.injEq, true_and, false_and, false_or, exists_eq_right,
          and_false, exists_false, or_false]
        rw [← Finset.mem_sdiff, ihl]
      · simp only [reduceCtorEq, List.cons.injEq, true_and, false_and, false_or, exists_eq_right,
          and_false, exists_false]
        rw [← Finset.mem_sdiff, ihr]

lemma to_queriesOk {V O : Type} {qs : Set (V → Bool)} (t : PTree V O) (ht : t.queriesOk qs) :
    ∀ p ∈ t.internals, t.queryAt p ∈ qs := by
  induction t with
  | leaf _ => intro p hp; simp [internals] at hp
  | node f l r ihl ihr =>
    rcases ht with ⟨hf, hl, hr⟩
    intro p hp
    simp only [internals, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact hf
    · exact ihl hl q hq
    · exact ihr hr q hq

lemma to_outAt_eq_eval {V O : Type} [Inhabited O] (t : PTree V O) :
    ∀ p ∈ t.nodes \ t.internals, ∀ x : V,
      (∀ j : Fin p.length, t.queryAt (p.take j.val) x = p.get j) →
      t.outAt p = t.eval x := by
  induction t with
  | leaf o =>
    intro p _ x _
    rfl
  | node f l r ihl ihr =>
    intro p hp x hreach
    rw [nodes_sdiff_internals] at hp
    simp only [leafPaths, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have h0 := hreach ⟨0, by simp⟩
      simp only [List.take_zero, queryAt, List.get_eq_getElem, List.getElem_cons_zero] at h0
      simp only [outAt, eval, h0, ↓reduceIte]
      apply ihl q (by rwa [nodes_sdiff_internals]) x
      intro j
      have hj := hreach ⟨j.val + 1, by simp [j.isLt]⟩
      simpa [List.take_succ_cons, queryAt] using hj
    · have h0 := hreach ⟨0, by simp⟩
      simp only [List.take_zero, queryAt, List.get_eq_getElem, List.getElem_cons_zero] at h0
      simp only [outAt, eval, h0, reduceCtorEq, ↓reduceIte]
      apply ihr q (by rwa [nodes_sdiff_internals]) x
      intro j
      have hj := hreach ⟨j.val + 1, by simp [j.isLt]⟩
      simpa [List.take_succ_cons, queryAt] using hj

lemma to_cert {V O : Type} [Inhabited O] {qs : Set (V → Bool)} {ok : V → O → Prop}
    (t : PTree V O) (hq : t.queriesOk qs) (hok : ∀ x, ok x (t.eval x)) :
    cert qs ok t.nodes t.internals t.queryAt t.outAt ∧ (t.nodes \ t.internals).card = t.leafCount := by
  refine ⟨⟨to_shape t, to_queriesOk t hq, ?_⟩, ?_⟩
  · intro p hp x hreach
    rw [to_outAt_eq_eval t p hp x hreach]
    exact hok x
  · rw [nodes_sdiff_internals, leafPaths_card]

end PTree

lemma shape_append_mem {N J : Finset (List Bool)} (hsh : shape N J) :
    ∀ (p q : List Bool), p ++ q ∈ N → p ∈ N := by
  intro p q
  induction q using List.reverseRecOn with
  | nil => intro h; simpa using h
  | append_singleton q b ih =>
    intro h
    rw [← List.append_assoc] at h
    exact ih (hsh.2.1 (hsh.2.2.1 (p ++ q) b h))

lemma shape_take_mem {N J : Finset (List Bool)} (hsh : shape N J) {p : List Bool} (hp : p ∈ N)
    (k : ℕ) : p.take k ∈ N := by
  apply shape_append_mem hsh (p.take k) (p.drop k)
  simpa using hp

lemma shape_length_lt_card {N J : Finset (List Bool)} (hsh : shape N J) {p : List Bool}
    (hp : p ∈ N) : p.length < N.card := by
  have hsub : (Finset.range (p.length + 1)).image (fun k => p.take k) ⊆ N := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨k, _, rfl⟩
    exact shape_take_mem hsh hp k
  have hinj : Set.InjOn (fun k => p.take k) (Finset.range (p.length + 1) : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have hlen := congrArg List.length hab
    simp only [List.length_take] at hlen
    omega
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hle
  omega

noncomputable def ofCert {V O : Type} (N J : Finset (List Bool))
    (q : List Bool → V → Bool) (out : List Bool → O)
    (hsh : shape N J) (p : List Bool) (_hp : p ∈ N) : PTree V O :=
  if hJ : p ∈ J then
    have h0 : p ++ [false] ∈ N := (hsh.2.2.2 p hJ).1
    have h1 : p ++ [true] ∈ N := (hsh.2.2.2 p hJ).2
    have hlt0 : N.card - (p ++ [false]).length < N.card - p.length := by
      have := shape_length_lt_card hsh h0; simp at this ⊢; omega
    have hlt1 : N.card - (p ++ [true]).length < N.card - p.length := by
      have := shape_length_lt_card hsh h1; simp at this ⊢; omega
    PTree.node (q p) (ofCert N J q out hsh (p ++ [false]) h0)
                     (ofCert N J q out hsh (p ++ [true]) h1)
  else
    PTree.leaf (out p)
termination_by N.card - p.length

lemma ofCert_queriesOk {V O : Type} {qs : Set (V → Bool)}
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O)
    (hsh : shape N J) (hq : ∀ r ∈ J, q r ∈ qs) :
    ∀ (m : ℕ) (p : List Bool) (_hp : p ∈ N), N.card - p.length = m →
      (ofCert N J q out hsh p _hp).queriesOk qs := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hp hm
    unfold ofCert
    split_ifs with hJ
    · have h0 : p ++ [false] ∈ N := (hsh.2.2.2 p hJ).1
      have h1 : p ++ [true] ∈ N := (hsh.2.2.2 p hJ).2
      have hlt0 : N.card - (p ++ [false]).length < m := by
        have := shape_length_lt_card hsh h0; simp at this ⊢; omega
      have hlt1 : N.card - (p ++ [true]).length < m := by
        have := shape_length_lt_card hsh h1; simp at this ⊢; omega
      exact ⟨hq p hJ, ih _ hlt0 _ h0 rfl, ih _ hlt1 _ h1 rfl⟩
    · trivial

lemma ofCert_leafCount {V O : Type}
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O)
    (hsh : shape N J) :
    ∀ (m : ℕ) (p : List Bool) (hp : p ∈ N), N.card - p.length = m →
      (ofCert N J q out hsh p hp).leafCount = ((N \ J).filter (fun r => p <+: r)).card := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hp hm
    unfold ofCert
    split_ifs with hJ
    · have h0 : p ++ [false] ∈ N := (hsh.2.2.2 p hJ).1
      have h1 : p ++ [true] ∈ N := (hsh.2.2.2 p hJ).2
      have hlt0 : N.card - (p ++ [false]).length < m := by
        have := shape_length_lt_card hsh h0; simp at this ⊢; omega
      have hlt1 : N.card - (p ++ [true]).length < m := by
        have := shape_length_lt_card hsh h1; simp at this ⊢; omega
      simp only [PTree.leafCount]
      rw [ih _ hlt0 _ h0 rfl, ih _ hlt1 _ h1 rfl]
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext r
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro (⟨hr, hp0⟩ | ⟨hr, hp1⟩)
          · exact ⟨hr, (List.prefix_append p [false]).trans hp0⟩
          · exact ⟨hr, (List.prefix_append p [true]).trans hp1⟩
        · rintro ⟨⟨hrN, hrJ⟩, ⟨t, rfl⟩⟩
          cases t with
          | nil =>
            simp only [List.append_nil] at hrJ
            exact absurd hJ hrJ
          | cons b t' =>
            cases b
            · left; exact ⟨⟨hrN, hrJ⟩, ⟨t', by simp⟩⟩
            · right; exact ⟨⟨hrN, hrJ⟩, ⟨t', by simp⟩⟩
      · rw [Finset.disjoint_left]
        intro r hr0 hr1
        simp only [Finset.mem_filter] at hr0 hr1
        rcases hr0.2 with ⟨t0, ht0⟩
        rcases hr1.2 with ⟨t1, ht1⟩
        have heq := ht0.trans ht1.symm
        simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append,
          List.nil_append, List.cons.injEq] at heq
        exact Bool.false_ne_true heq.1
    · simp only [PTree.leafCount]
      have hset : (N \ J).filter (fun r => p <+: r) = {p} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hrN, hrJ⟩, ⟨t, rfl⟩⟩
          cases t with
          | nil => simp
          | cons b t' =>
            exfalso
            have hmem : p ++ [b] ∈ N := by
              apply shape_append_mem hsh (p ++ [b]) t'
              simpa [List.append_assoc] using hrN
            exact hJ (hsh.2.2.1 p b hmem)
        · rintro rfl
          exact ⟨⟨hp, hJ⟩, List.prefix_refl _⟩
      rw [hset, Finset.card_singleton]

lemma ofCert_eval {V O : Type}
    (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O)
    (hsh : shape N J) (x : V) :
    ∀ (m : ℕ) (p : List Bool) (hp : p ∈ N), N.card - p.length = m →
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) →
      ∃ r ∈ N \ J, (∀ j : Fin r.length, q (r.take j.val) x = r.get j) ∧
        (ofCert N J q out hsh p hp).eval x = out r := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hp hm hreach
    unfold ofCert
    split_ifs with hJ
    · have h0 : p ++ [false] ∈ N := (hsh.2.2.2 p hJ).1
      have h1 : p ++ [true] ∈ N := (hsh.2.2.2 p hJ).2
      have hlt0 : N.card - (p ++ [false]).length < m := by
        have := shape_length_lt_card hsh h0; simp at this ⊢; omega
      have hlt1 : N.card - (p ++ [true]).length < m := by
        have := shape_length_lt_card hsh h1; simp at this ⊢; omega
      simp only [PTree.eval]
      by_cases hqpx : q p x = false
      · simp only [hqpx, ↓reduceIte]
        apply ih _ hlt0 (p ++ [false]) h0 rfl
        intro j
        by_cases hj : j.val < p.length
        · have htake : (p ++ [false]).take j.val = p.take j.val := by
            rw [List.take_append_of_le_length (le_of_lt hj)]
          rw [htake]
          have hget : (p ++ [false]).get j = p.get ⟨j.val, hj⟩ := by
            simp [List.getElem_append_left hj]
          rw [hget]
          exact hreach ⟨j.val, hj⟩
        · have hjeq : j.val = p.length := by
            have := j.isLt; simp at this; omega
          have htake : (p ++ [false]).take j.val = p := by
            rw [hjeq, List.take_left]
          have hget : (p ++ [false]).get j = false := by
            simp [List.get_eq_getElem, hjeq]
          rw [htake, hget, hqpx]
      · have hqpx' : q p x = true := by
          cases h : q p x <;> simp_all
        simp only [hqpx', reduceCtorEq, ↓reduceIte]
        apply ih _ hlt1 (p ++ [true]) h1 rfl
        intro j
        by_cases hj : j.val < p.length
        · have htake : (p ++ [true]).take j.val = p.take j.val := by
            rw [List.take_append_of_le_length (le_of_lt hj)]
          rw [htake]
          have hget : (p ++ [true]).get j = p.get ⟨j.val, hj⟩ := by
            simp [List.getElem_append_left hj]
          rw [hget]
          exact hreach ⟨j.val, hj⟩
        · have hjeq : j.val = p.length := by
            have := j.isLt; simp at this; omega
          have htake : (p ++ [true]).take j.val = p := by
            rw [hjeq, List.take_left]
          have hget : (p ++ [true]).get j = true := by
            simp [List.get_eq_getElem, hjeq]
          rw [htake, hget, hqpx']
    · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hreach, rfl⟩

lemma hasTree_iff_ptree (k : ℕ) (v : Vec k → Vec k) :
    HasTree k v ↔
      ∃ t : PTree (Vec k) (Finset (Vec k)),
        t.queriesOk (queries (Vec k)) ∧
        (∀ x, t.eval x = {x, v x}) ∧
        2 * t.leafCount = 2 ^ k := by
  constructor
  · rintro ⟨N, J, q, out, ⟨hsh, hq, hok⟩, hcard⟩
    refine ⟨ofCert N J q out hsh [] hsh.1, ?_, ?_, ?_⟩
    · exact ofCert_queriesOk N J q out hsh hq _ [] hsh.1 rfl
    · intro x
      obtain ⟨r, hr, hreach, hev⟩ := ofCert_eval N J q out hsh x _ [] hsh.1 rfl (fun j => Fin.elim0 j)
      rw [hev]
      exact hok r hr x hreach
    · have hlc := ofCert_leafCount N J q out hsh _ [] hsh.1 rfl
      have hfilt : (N \ J).filter (fun r => [] <+: r) = N \ J := by
        ext r; simp
      rw [hfilt] at hlc
      rw [hlc, hcard]
  · rintro ⟨t, hq, hev, hcnt⟩
    obtain ⟨hc, hcard⟩ := t.to_cert (ok := fun x a => a = {x, v x}) hq hev
    exact ⟨t.nodes, t.internals, t.queryAt, t.outAt, hc, by rw [hcard, hcnt]⟩

lemma fiber_card_le_two {k : ℕ} {v : Vec k → Vec k} {t : PTree (Vec k) (Finset (Vec k))}
    (hev : ∀ x, t.eval x = {x, v x}) (p : List Bool) :
    (Finset.univ.filter (fun x : Vec k => t.evalPath x = p)).card ≤ 2 := by
  by_cases hne : (Finset.univ.filter (fun x : Vec k => t.evalPath x = p)).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hxp : t.evalPath x = p := (Finset.mem_filter.mp hx).2
    have hsub : Finset.univ.filter (fun y : Vec k => t.evalPath y = p) ⊆ {x, v x} := by
      intro y hy
      have hyp : t.evalPath y = p := (Finset.mem_filter.mp hy).2
      have hteq : t.eval y = t.eval x := t.eval_eq_of_evalPath_eq (hyp.trans hxp.symm)
      rw [hev y, hev x] at hteq
      have hyin : y ∈ ({y, v y} : Finset (Vec k)) := by simp
      rwa [hteq] at hyin
    exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

lemma fiber_card_eq_two {k : ℕ} {v : Vec k → Vec k} {t : PTree (Vec k) (Finset (Vec k))}
    (hev : ∀ x, t.eval x = {x, v x}) (hcnt : 2 * t.leafCount = 2 ^ k)
    {p : List Bool} (hp : p ∈ t.leafPaths) :
    (Finset.univ.filter (fun x : Vec k => t.evalPath x = p)).card = 2 := by
  have hsum : ∑ r ∈ t.leafPaths, (Finset.univ.filter (fun x : Vec k => t.evalPath x = r)).card =
      ∑ _r ∈ t.leafPaths, 2 := by
    have hpart : ∑ r ∈ t.leafPaths, (Finset.univ.filter (fun x : Vec k => t.evalPath x = r)).card =
        (Finset.univ : Finset (Vec k)).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext x
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        exact ⟨t.evalPath x, t.evalPath_mem_leafPaths x, rfl⟩
      · intro r1 _ r2 _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
    rw [hpart, Finset.card_univ, card_vec, Finset.sum_const, t.leafPaths_card, smul_eq_mul,
      mul_comm, hcnt]
  have hall := (Finset.sum_eq_sum_iff_of_le (fun r _ => fiber_card_le_two hev r)).mp hsum
  exact hall p hp

lemma evalPath_v {k : ℕ} {v : Vec k → Vec k} {t : PTree (Vec k) (Finset (Vec k))}
    (hm : IsMatching k v) (hev : ∀ x, t.eval x = {x, v x}) (hcnt : 2 * t.leafCount = 2 ^ k)
    (x : Vec k) : t.evalPath (v x) = t.evalPath x := by
  let p := t.evalPath x
  have hp : p ∈ t.leafPaths := t.evalPath_mem_leafPaths x
  have hcard := fiber_card_eq_two hev hcnt hp
  have hsub : Finset.univ.filter (fun y : Vec k => t.evalPath y = p) ⊆ {x, v x} := by
    intro y hy
    have hyp : t.evalPath y = p := (Finset.mem_filter.mp hy).2
    have hteq : t.eval y = t.eval x := t.eval_eq_of_evalPath_eq hyp
    rw [hev y, hev x] at hteq
    have hyin : y ∈ ({y, v y} : Finset (Vec k)) := by simp
    rwa [hteq] at hyin
  have hpair : ({x, v x} : Finset (Vec k)).card = 2 := by
    rw [Finset.card_pair (hm x).2.symm]
  have heq : Finset.univ.filter (fun y : Vec k => t.evalPath y = p) = {x, v x} :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hpair])
  have hvin : v x ∈ Finset.univ.filter (fun y : Vec k => t.evalPath y = p) := by
    rw [heq]; simp
  exact (Finset.mem_filter.mp hvin).2

def dot {k : ℕ} (a x : Vec k) : ZMod 2 := ∑ i : Fin k, a i * x i

lemma dot_comm {k : ℕ} (a x : Vec k) : dot a x = dot x a := by
  simp only [dot, mul_comm]

def dotL {k : ℕ} (a : Vec k) : Vec k →ₗ[ZMod 2] ZMod 2 where
  toFun x := dot a x
  map_add' x y := by simp [dot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)

@[simp] lemma dotL_apply {k : ℕ} (a x : Vec k) : dotL a x = dot a x := rfl

def dotEquiv (k : ℕ) : Vec k ≃ₗ[ZMod 2] (Vec k →ₗ[ZMod 2] ZMod 2) where
  toFun := dotL
  map_add' a b := by
    apply LinearMap.ext; intro x
    simp [dotL_apply, dot, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply LinearMap.ext; intro x
    simp only [dotL_apply, dot, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => by ring)
  invFun l := fun i => l (Pi.single i 1)
  left_inv a := by
    ext i
    simp [dotL_apply, dot, Pi.single_apply]
  right_inv l := by
    apply LinearMap.ext; intro x
    simp only [dotL_apply, dot]
    have hx : x = ∑ i : Fin k, x i • Pi.single i (1 : ZMod 2) := by
      ext j
      simp [Pi.single_apply]
    conv_rhs => rw [hx]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, smul_eq_mul, mul_comm]

def invSub {k : ℕ} (v : Vec k → Vec k) : Submodule (ZMod 2) (Vec k) :=
  { carrier := {a | ∀ x, dot a (v x) = dot a x}, add_mem' := fun {a b} ha hb x => by
      change ∑ i, (a i + b i) * v x i = ∑ i, (a i + b i) * x i
      simp only [add_mul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) (ha x) (hb x),
    zero_mem' := fun x => by simp [dot],
    smul_mem' := fun c {a} ha x => by
      change ∑ i, (c * a i) * v x i = ∑ i, (c * a i) * x i
      simp only [mul_assoc, ← Finset.mul_sum]
      exact congrArg (c * ·) (ha x) }

lemma invSub_ne_bot {n : ℕ} (hn : 2 ≤ n) {v : Vec n → Vec n} (hg : Good n v) :
    invSub v ≠ ⊥ := by
  obtain ⟨hm, ht⟩ := hg
  obtain ⟨t, hq, hev, hcnt⟩ := (hasTree_iff_ptree n v).mp ht
  cases t with
  | leaf o =>
    simp only [PTree.leafCount] at hcnt
    have h4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
    omega
  | node f l r =>
    obtain ⟨⟨lin, b, rfl⟩, _, _⟩ := hq
    let a : Vec n := (dotEquiv n).symm lin
    have hlin : dotL a = lin := (dotEquiv n).apply_symm_apply lin
    have ha_ne : a ≠ 0 := by
      intro ha0
      have hlin0 : lin = 0 := by rw [← hlin, ha0]; ext x; simp [dotL, dot]
      by_cases hb : (0 : ZMod 2) = b
      · obtain ⟨p0, hp0⟩ := l.leafPaths_nonempty
        have hmem : false :: p0 ∈ (PTree.node (fun x => decide (lin x = b)) l r).leafPaths :=
          Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp0)
        have hcard := fiber_card_eq_two hev hcnt hmem
        have hne : (Finset.univ.filter (fun x => (PTree.node (fun x => decide (lin x = b)) l r).evalPath x = false :: p0)).Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨x, hx⟩ := hne
        have hpx := (Finset.mem_filter.mp hx).2
        simp only [PTree.evalPath, hlin0, LinearMap.zero_apply, hb, decide_true,
          reduceCtorEq, ↓reduceIte, List.cons.injEq] at hpx
        exact hpx.1
      · obtain ⟨p0, hp0⟩ := r.leafPaths_nonempty
        have hmem : true :: p0 ∈ (PTree.node (fun x => decide (lin x = b)) l r).leafPaths :=
          Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp0)
        have hcard := fiber_card_eq_two hev hcnt hmem
        have hne : (Finset.univ.filter (fun x => (PTree.node (fun x => decide (lin x = b)) l r).evalPath x = true :: p0)).Nonempty :=
          Finset.card_pos.mp (by omega)
        obtain ⟨x, hx⟩ := hne
        have hpx := (Finset.mem_filter.mp hx).2
        simp only [PTree.evalPath, hlin0, LinearMap.zero_apply, decide_eq_false hb,
          ↓reduceIte, List.cons.injEq, reduceCtorEq] at hpx
        exact hpx.1
    have ha_mem : a ∈ invSub v := by
      intro x
      have hp := evalPath_v hm hev hcnt x
      simp only [PTree.evalPath] at hp
      have hdec : decide (lin (v x) = b) = decide (lin x = b) := by
        by_cases h1 : decide (lin (v x) = b) = false <;>
          by_cases h2 : decide (lin x = b) = false <;> simp_all
      have heq := zmod2_eq_of_decide_eq hdec
      have h1 : dot a (v x) = lin (v x) := by rw [← hlin]; rfl
      have h2 : dot a x = lin x := by rw [← hlin]; rfl
      rw [h1, h2, heq]
    intro hbot
    rw [hbot, Submodule.mem_bot] at ha_mem
    exact ha_ne ha_mem

noncomputable def prune {V V' O O' : Type}
    (g : V' → V) (hOut : O → O') :
    PTree V O → Finset V → Option (PTree V' O')
  | PTree.leaf o, S =>
      if S.Nonempty then some (PTree.leaf (hOut o)) else none
  | PTree.node f l r, S =>
      let S0 := S.filter (fun x => f x = false)
      let S1 := S.filter (fun x => f x = true)
      match prune g hOut l S0, prune g hOut r S1 with
      | none, none => none
      | some tl, none => some tl
      | none, some tr => some tr
      | some tl, some tr => some (PTree.node (fun y => f (g y)) tl tr)

lemma prune_isSome_iff {V V' O O' : Type} (g : V' → V) (hOut : O → O')
    (t : PTree V O) (S : Finset V) :
    (prune g hOut t S).isSome ↔ S.Nonempty := by
  induction t generalizing S with
  | leaf o =>
    simp only [prune]
    split_ifs with h <;> simp [h]
  | node f l r ihl ihr =>
    simp only [prune]
    set S0 := S.filter (fun x => f x = false)
    set S1 := S.filter (fun x => f x = true)
    have h0 := ihl S0
    have h1 := ihr S1
    cases hl : prune g hOut l S0 <;> cases hr : prune g hOut r S1 <;>
      simp only [hl, hr, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
        false_iff, true_iff] at h0 h1 ⊢
    · intro hne
      obtain ⟨x, hx⟩ := hne
      cases hfx : f x
      · exact h0 ⟨x, Finset.mem_filter.mpr ⟨hx, hfx⟩⟩
      · exact h1 ⟨x, Finset.mem_filter.mpr ⟨hx, hfx⟩⟩
    · obtain ⟨x, hx⟩ := h1
      exact ⟨x, (Finset.mem_filter.mp hx).1⟩
    · obtain ⟨x, hx⟩ := h0
      exact ⟨x, (Finset.mem_filter.mp hx).1⟩
    · obtain ⟨x, hx⟩ := h0
      exact ⟨x, (Finset.mem_filter.mp hx).1⟩

lemma prune_queriesOk {V V' O O' : Type} {qs : Set (V → Bool)} {qs' : Set (V' → Bool)}
    (g : V' → V) (hOut : O → O') (hg : ∀ f ∈ qs, (fun y => f (g y)) ∈ qs')
    (t : PTree V O) (ht : t.queriesOk qs) (S : Finset V) {t' : PTree V' O'}
    (hp : prune g hOut t S = some t') :
    t'.queriesOk qs' := by
  induction t generalizing S t' with
  | leaf o =>
    simp only [prune] at hp
    split_ifs at hp with h
    · cases hp; trivial
  | node f l r ihl ihr =>
    rcases ht with ⟨hf, hl, hr⟩
    simp only [prune] at hp
    cases hpl : prune g hOut l (S.filter (fun x => f x = false)) <;>
      cases hpr : prune g hOut r (S.filter (fun x => f x = true)) <;>
      rw [hpl, hpr] at hp
    · cases hp
    · cases hp; exact ihr hr _ hpr
    · cases hp; exact ihl hl _ hpl
    · cases hp; exact ⟨hg f hf, ihl hl _ hpl, ihr hr _ hpr⟩

lemma prune_eval {V V' O O' : Type} (g : V' → V) (hOut : O → O')
    (t : PTree V O) (S : Finset V) {t' : PTree V' O'}
    (hp : prune g hOut t S = some t') {y : V'} (hy : g y ∈ S) :
    t'.eval y = hOut (t.eval (g y)) := by
  induction t generalizing S t' with
  | leaf o =>
    simp only [prune] at hp
    split_ifs at hp with h
    · cases hp; rfl
  | node f l r ihl ihr =>
    simp only [prune] at hp
    set S0 := S.filter (fun x => f x = false)
    set S1 := S.filter (fun x => f x = true)
    cases hfx : f (g y)
    · have hy0 : g y ∈ S0 := Finset.mem_filter.mpr ⟨hy, hfx⟩
      have h0some : (prune g hOut l S0).isSome := (prune_isSome_iff g hOut l S0).mpr ⟨g y, hy0⟩
      obtain ⟨tl, htl⟩ := Option.isSome_iff_exists.mp h0some
      rw [htl] at hp
      cases htr : prune g hOut r S1 <;> rw [htr] at hp <;> cases hp
      · simp only [PTree.eval, hfx, ↓reduceIte]
        exact ihl S0 htl hy0
      · simp only [PTree.eval, hfx, ↓reduceIte]
        exact ihl S0 htl hy0
    · have hy1 : g y ∈ S1 := Finset.mem_filter.mpr ⟨hy, hfx⟩
      have h1some : (prune g hOut r S1).isSome := (prune_isSome_iff g hOut r S1).mpr ⟨g y, hy1⟩
      obtain ⟨tr, htr⟩ := Option.isSome_iff_exists.mp h1some
      rw [htr] at hp
      cases htl : prune g hOut l S0 <;> rw [htl] at hp <;> cases hp
      · simp only [PTree.eval, hfx, reduceCtorEq, ↓reduceIte]
        exact ihr S1 htr hy1
      · simp only [PTree.eval, hfx, reduceCtorEq, ↓reduceIte]
        exact ihr S1 htr hy1

lemma prune_leafCount {V V' O O' : Type} (g : V' → V) (hOut : O → O')
    (t : PTree V O) (S : Finset V) {t' : PTree V' O'}
    (hp : prune g hOut t S = some t') :
    t'.leafCount = (S.image t.evalPath).card := by
  induction t generalizing S t' with
  | leaf o =>
    simp only [prune] at hp
    split_ifs at hp with h
    · cases hp
      have himg : S.image (PTree.leaf o).evalPath = {[]} := by
        ext p
        simp only [Finset.mem_image, PTree.evalPath, Finset.mem_singleton]
        constructor
        · rintro ⟨_, _, rfl⟩; rfl
        · rintro rfl; obtain ⟨x, hx⟩ := h; exact ⟨x, hx, rfl⟩
      rw [himg]
      simp [PTree.leafCount]
  | node f l r ihl ihr =>
    simp only [prune] at hp
    set S0 := S.filter (fun x => f x = false)
    set S1 := S.filter (fun x => f x = true)
    have hsplit : (S.image (PTree.node f l r).evalPath).card =
        (S0.image l.evalPath).card + (S1.image r.evalPath).card := by
      have hunion : S.image (PTree.node f l r).evalPath =
          (S0.image l.evalPath).image (false :: ·) ∪ (S1.image r.evalPath).image (true :: ·) := by
        ext p
        simp only [Finset.mem_image, Finset.mem_union, PTree.evalPath, S0, S1, Finset.mem_filter]
        constructor
        · rintro ⟨x, hx, rfl⟩
          cases hfx : f x
          · left; exact ⟨l.evalPath x, ⟨x, ⟨hx, hfx⟩, rfl⟩, by simp⟩
          · right; exact ⟨r.evalPath x, ⟨x, ⟨hx, hfx⟩, rfl⟩, by simp⟩
        · rintro (⟨q, ⟨x, ⟨hx, hfx⟩, rfl⟩, rfl⟩ | ⟨q, ⟨x, ⟨hx, hfx⟩, rfl⟩, rfl⟩)
          · exact ⟨x, hx, by simp [hfx]⟩
          · exact ⟨x, hx, by simp [hfx]⟩
      rw [hunion, Finset.card_union_of_disjoint,
        Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2),
        Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases Finset.mem_image.mp hp1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hp2 with ⟨_, _, h⟩
      cases h
    rw [hsplit]
    cases htl : prune g hOut l S0 <;> cases htr : prune g hOut r S1 <;> rw [htl, htr] at hp
    · cases hp
    · cases hp
      have h0e : S0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp (by
        intro hne; have := (prune_isSome_iff g hOut l S0).mpr hne; simp [htl] at this)
      rw [h0e, Finset.image_empty, Finset.card_empty, zero_add]
      exact ihr S1 htr
    · cases hp
      have h1e : S1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp (by
        intro hne; have := (prune_isSome_iff g hOut r S1).mpr hne; simp [htr] at this)
      rw [h1e, Finset.image_empty, Finset.card_empty, add_zero]
      exact ihl S0 htl
    · cases hp
      simp only [PTree.leafCount]
      rw [ihl S0 htl, ihr S1 htr]

def mapTree {V V' O O' : Type} (g : V' → V) (hOut : O → O') :
    PTree V O → PTree V' O'
  | PTree.leaf o => PTree.leaf (hOut o)
  | PTree.node f l r => PTree.node (fun y => f (g y)) (mapTree g hOut l) (mapTree g hOut r)

lemma mapTree_eval {V V' O O' : Type} (g : V' → V) (hOut : O → O')
    (t : PTree V O) (y : V') :
    (mapTree g hOut t).eval y = hOut (t.eval (g y)) := by
  induction t with
  | leaf o => rfl
  | node f l r ihl ihr =>
    simp only [mapTree, PTree.eval]
    split_ifs <;> [exact ihl; exact ihr]

lemma mapTree_leafCount {V V' O O' : Type} (g : V' → V) (hOut : O → O')
    (t : PTree V O) :
    (mapTree g hOut t).leafCount = t.leafCount := by
  induction t with
  | leaf o => rfl
  | node f l r ihl ihr => simp [mapTree, PTree.leafCount, ihl, ihr]

lemma mapTree_queriesOk {V V' O O' : Type} {qs : Set (V → Bool)} {qs' : Set (V' → Bool)}
    (g : V' → V) (hOut : O → O') (hg : ∀ f ∈ qs, (fun y => f (g y)) ∈ qs')
    (t : PTree V O) (ht : t.queriesOk qs) :
    (mapTree g hOut t).queriesOk qs' := by
  induction t with
  | leaf o => trivial
  | node f l r ihl ihr => exact ⟨hg f ht.1, ihl ht.2.1, ihr ht.2.2⟩

def stackTree {V O : Type} (q : ℕ → V → Bool) :
    (d : ℕ) → ((Fin d → ZMod 2) → PTree V O) → PTree V O
  | 0, F => F Fin.elim0
  | d + 1, F =>
      PTree.node (q d)
        (stackTree q d (fun c => F (Fin.snoc c 0)))
        (stackTree q d (fun c => F (Fin.snoc c 1)))

lemma stackTree_queriesOk {V O : Type} {qs : Set (V → Bool)} (q : ℕ → V → Bool) :
    ∀ (d : ℕ) (F : (Fin d → ZMod 2) → PTree V O),
      (∀ i < d, q i ∈ qs) →
      (∀ c, (F c).queriesOk qs) →
      (stackTree q d F).queriesOk qs
  | 0, F, _, hF => hF Fin.elim0
  | d + 1, F, hq, hF => by
    refine ⟨hq d (Nat.lt_succ_self d), ?_, ?_⟩
    · exact stackTree_queriesOk q d _ (fun i hi => hq i (Nat.lt_succ_of_lt hi)) (fun c => hF _)
    · exact stackTree_queriesOk q d _ (fun i hi => hq i (Nat.lt_succ_of_lt hi)) (fun c => hF _)

lemma stackTree_leafCount {V O : Type} (q : ℕ → V → Bool) :
    ∀ (d : ℕ) (F : (Fin d → ZMod 2) → PTree V O),
      (stackTree q d F).leafCount = ∑ c : Fin d → ZMod 2, (F c).leafCount
  | 0, F => by
    simp only [stackTree]
    rw [Finset.sum_eq_single Fin.elim0]
    · intro c _ hc
      exact absurd (Subsingleton.elim c Fin.elim0) hc
    · intro h
      exact absurd (Finset.mem_univ _) h
  | d + 1, F => by
    simp only [stackTree, PTree.leafCount]
    rw [stackTree_leafCount q d, stackTree_leafCount q d]
    let e : (Fin d → ZMod 2) ⊕ (Fin d → ZMod 2) ≃ (Fin (d + 1) → ZMod 2) :=
      { toFun := Sum.elim (fun c => Fin.snoc c 0) (fun c => Fin.snoc c 1)
        invFun := fun c => if c (Fin.last d) = 0 then Sum.inl (Fin.init c) else Sum.inr (Fin.init c)
        left_inv := by
          rintro (c | c) <;> simp [Fin.snoc_last, Fin.init_snoc]
        right_inv := by
          intro c
          rcases zmod2_cases (c (Fin.last d)) with h0 | h1
          · simp only [h0, ↓reduceIte, Sum.elim_inl]
            rw [← h0, Fin.snoc_init_self]
          · simp only [h1, one_ne_zero, ↓reduceIte, Sum.elim_inr]
            rw [← h1, Fin.snoc_init_self] }
    rw [← Fintype.sum_equiv e (fun s => (F (e s)).leafCount) (fun c => (F c).leafCount) (fun _ => rfl)]
    rw [Fintype.sum_sum_type]
    rfl

lemma stackTree_eval {V O : Type} (q : ℕ → V → Bool) :
    ∀ (d : ℕ) (F : (Fin d → ZMod 2) → PTree V O) (x : V) (c : Fin d → ZMod 2),
      (∀ i : Fin d, q i.val x = decide (c i = 1)) →
      (stackTree q d F).eval x = (F c).eval x
  | 0, F, x, c, _ => by
    have : c = Fin.elim0 := Subsingleton.elim _ _
    subst this; rfl
  | d + 1, F, x, c, hc => by
    simp only [stackTree, PTree.eval]
    have hlast := hc (Fin.last d)
    simp only [Fin.val_last] at hlast
    rcases zmod2_cases (c (Fin.last d)) with h0 | h1
    · have hqf : q d x = false := by rw [hlast, h0]; decide
      simp only [hqf, ↓reduceIte]
      rw [stackTree_eval q d _ x (Fin.init c)]
      · have hsn : Fin.snoc (Fin.init c) (0 : ZMod 2) = c := by rw [← h0, Fin.snoc_init_self]
        rw [hsn]
      · intro i
        exact hc i.castSucc
    · have hqt : q d x = true := by rw [hlast, h1]; decide
      simp only [hqt, reduceCtorEq, ↓reduceIte]
      rw [stackTree_eval q d _ x (Fin.init c)]
      · have hsn : Fin.snoc (Fin.init c) (1 : ZMod 2) = c := by rw [← h1, Fin.snoc_init_self]
        rw [hsn]
      · intro i
        exact hc i.castSucc

lemma finrank_le_dim {n : ℕ} (A : Submodule (ZMod 2) (Vec n)) :
    Module.finrank (ZMod 2) A ≤ n := by
  calc Module.finrank (ZMod 2) A ≤ Module.finrank (ZMod 2) (Vec n) := Submodule.finrank_le A
  _ = n := Module.finrank_fin_fun (ZMod 2)

lemma exists_split_equiv {n d : ℕ} (A : Submodule (ZMod 2) (Vec n))
    (hA : Module.finrank (ZMod 2) A = d) :
    ∃ (e : Fin d → Vec n) (T : Vec n ≃ₗ[ZMod 2] Vec d × Vec (n - d)),
      (∀ j, e j ∈ A) ∧
      (∀ x j, (T x).1 j = dot (e j) x) ∧
      (∀ v : Vec n → Vec n, A ≤ invSub v ↔ ∀ x, (T (v x)).1 = (T x).1) := by
  have hd : d ≤ n := hA ▸ finrank_le_dim A
  obtain ⟨B, hAB⟩ := Submodule.exists_isCompl A
  have hB : Module.finrank (ZMod 2) B = n - d := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hAB.codisjoint.eq_top, hAB.disjoint.eq_bot, finrank_top, finrank_bot,
      Module.finrank_fin_fun, hA, add_zero] at hsum
    omega
  let bA : Module.Basis (Fin d) (ZMod 2) A := (Module.finBasis (ZMod 2) A).reindex (finCongr hA)
  let bB : Module.Basis (Fin (n - d)) (ZMod 2) B := (Module.finBasis (ZMod 2) B).reindex (finCongr hB)
  let e : Fin d → Vec n := fun j => (bA j).val
  let f : Fin (n - d) → Vec n := fun k => (bB k).val
  let M : Vec n →ₗ[ZMod 2] Vec d × Vec (n - d) :=
    LinearMap.prod (LinearMap.pi fun j => dotL (e j)) (LinearMap.pi fun k => dotL (f k))
  have hMinj : Function.Injective M := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h1 : ∀ j, dot (e j) x = 0 := fun j => by
      have := congrFun (congrArg Prod.fst hx) j
      simpa [M, dotL_apply] using this
    have h2 : ∀ k, dot (f k) x = 0 := fun k => by
      have := congrFun (congrArg Prod.snd hx) k
      simpa [M, dotL_apply] using this
    have hAker : A ≤ LinearMap.ker (dotL x) := by
      intro a ha
      have hrepr : (⟨a, ha⟩ : A) = ∑ j, bA.repr ⟨a, ha⟩ j • bA j := (bA.sum_repr ⟨a, ha⟩).symm
      have haeq : a = ∑ j, bA.repr ⟨a, ha⟩ j • e j :=
        calc a = A.subtype ⟨a, ha⟩ := rfl
        _ = A.subtype (∑ j, bA.repr ⟨a, ha⟩ j • bA j) := congrArg A.subtype hrepr
        _ = ∑ j, bA.repr ⟨a, ha⟩ j • e j := by simp only [map_sum, map_smul]; rfl
      rw [LinearMap.mem_ker, haeq, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul, smul_eq_mul, dotL_apply, dot_comm, h1 j, mul_zero]
    have hBker : B ≤ LinearMap.ker (dotL x) := by
      intro b hb
      have hrepr : (⟨b, hb⟩ : B) = ∑ k, bB.repr ⟨b, hb⟩ k • bB k := (bB.sum_repr ⟨b, hb⟩).symm
      have hbeq : b = ∑ k, bB.repr ⟨b, hb⟩ k • f k :=
        calc b = B.subtype ⟨b, hb⟩ := rfl
        _ = B.subtype (∑ k, bB.repr ⟨b, hb⟩ k • bB k) := congrArg B.subtype hrepr
        _ = ∑ k, bB.repr ⟨b, hb⟩ k • f k := by simp only [map_sum, map_smul]; rfl
      rw [LinearMap.mem_ker, hbeq, map_sum]
      apply Finset.sum_eq_zero
      intro k _
      rw [map_smul, smul_eq_mul, dotL_apply, dot_comm, h2 k, mul_zero]
    have htop : (⊤ : Submodule (ZMod 2) (Vec n)) ≤ LinearMap.ker (dotL x) := by
      rw [← hAB.codisjoint.eq_top]
      exact sup_le hAker hBker
    ext i
    have hi : Pi.single i (1 : ZMod 2) ∈ LinearMap.ker (dotL x) := htop trivial
    rw [LinearMap.mem_ker] at hi
    simpa [dotL_apply, dot, Pi.single_apply] using hi
  have hcard : Fintype.card (Vec n) = Fintype.card (Vec d × Vec (n - d)) := by
    rw [Fintype.card_prod, card_vec, card_vec, card_vec, ← pow_add, Nat.add_sub_of_le hd]
  have hMbij : Function.Bijective M :=
    (Fintype.bijective_iff_injective_and_card M).mpr ⟨hMinj, hcard⟩
  let T : Vec n ≃ₗ[ZMod 2] Vec d × Vec (n - d) := LinearEquiv.ofBijective M hMbij
  refine ⟨e, T, fun j => (bA j).2, fun x j => rfl, ?_⟩
  intro v
  constructor
  · intro hv x
    ext j
    exact hv (bA j).2 x
  · intro hv a ha x
    have hrepr : (⟨a, ha⟩ : A) = ∑ j, bA.repr ⟨a, ha⟩ j • bA j := (bA.sum_repr ⟨a, ha⟩).symm
    have haeq : a = ∑ j, bA.repr ⟨a, ha⟩ j • e j :=
      calc a = A.subtype ⟨a, ha⟩ := rfl
      _ = A.subtype (∑ j, bA.repr ⟨a, ha⟩ j • bA j) := congrArg A.subtype hrepr
      _ = ∑ j, bA.repr ⟨a, ha⟩ j • e j := by simp only [map_sum, map_smul]; rfl
    have hdot : ∀ u : Vec n, dot a u = ∑ j, bA.repr ⟨a, ha⟩ j * dot (e j) u := by
      intro u
      conv_lhs => rw [dot_comm, haeq]
      change dotL u (∑ j, bA.repr ⟨a, ha⟩ j • e j) = _
      rw [map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul, smul_eq_mul, dotL_apply, dot_comm]
    rw [hdot (v x), hdot x]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hj := congrFun (hv x) j
    change dot (e j) (v x) = dot (e j) x at hj
    rw [hj]

lemma card_good_respecting {n d : ℕ} (A : Submodule (ZMod 2) (Vec n))
    (hA : Module.finrank (ZMod 2) A = d) :
    Nat.card {v : Vec n → Vec n // Good n v ∧ A ≤ invSub v} = (count (n - d)) ^ (2 ^ d) := by
  obtain ⟨e, T, _, hT1, hTinv⟩ := exists_split_equiv A hA
  let embed (c : Vec d) (y : Vec (n - d)) : Vec n := T.symm (c, y)
  have hT_embed : ∀ c y, T (embed c y) = (c, y) := fun c y => T.apply_symm_apply (c, y)
  have hembed_inj : ∀ c, Function.Injective (embed c) := by
    intro c y1 y2 h
    have := congrArg T h
    rw [hT_embed, hT_embed] at this
    exact (Prod.mk.inj this).2
  have hGood_equiv :
      {v : Vec n → Vec n // Good n v ∧ A ≤ invSub v} ≃
        (Vec d → {u : Vec (n - d) → Vec (n - d) // Good (n - d) u}) :=
    { toFun := fun ⟨v, ⟨hmv, htv⟩, hAv⟩ c =>
        let u : Vec (n - d) → Vec (n - d) := fun y => (T (v (embed c y))).2
        have hv1 : ∀ x, (T (v x)).1 = (T x).1 := (hTinv v).mp hAv
        have hvu : ∀ y, v (embed c y) = embed c (u y) := by
          intro y
          apply T.injective
          rw [hT_embed]
          exact Prod.ext (by rw [hv1, hT_embed]) rfl
        have hmu : IsMatching (n - d) u := by
          intro y
          constructor
          · apply hembed_inj c
            rw [← hvu, ← hvu, (hmv _).1]
          · intro heq
            have h1 := hvu y
            rw [heq] at h1
            exact (hmv (embed c y)).2 h1
        have htu : HasTree (n - d) u := by
          rw [hasTree_iff_ptree] at htv ⊢
          obtain ⟨t, hqt, hevt, hcntt⟩ := htv
          let S : Finset (Vec n) := Finset.univ.image (embed c)
          have hSne : S.Nonempty := ⟨embed c 0, Finset.mem_image_of_mem _ (Finset.mem_univ 0)⟩
          have hsome := (prune_isSome_iff (embed c) (fun B => Finset.univ.filter (fun y => embed c y ∈ B)) t S).mpr hSne
          obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp hsome
          refine ⟨t', ?_, ?_, ?_⟩
          · apply prune_queriesOk (embed c) _ _ t hqt S ht'
            rintro f ⟨l, b, rfl⟩
            let l' : Vec (n - d) →ₗ[ZMod 2] ZMod 2 :=
              l.comp (T.symm.toLinearMap.comp (LinearMap.inr (ZMod 2) (Vec d) (Vec (n - d))))
            refine ⟨l', b - l (T.symm (c, 0)), ?_⟩
            ext y
            have heq_y : embed c y = T.symm (c, 0) + T.symm (0, y) := by
              change T.symm (c, y) = T.symm (c, 0) + T.symm (0, y)
              rw [← map_add]
              simp
            have hl : l (embed c y) = l (T.symm (c, 0)) + l' y := by
              rw [heq_y, map_add]
              rfl
            have hiff : (l (embed c y) = b) ↔ (l' y = b - l (T.symm (c, 0))) := by
              rw [hl]
              constructor <;> intro h
              · rw [← h]; ring
              · rw [h]; ring
            simp [hiff]
          · intro y
            have hyS : embed c y ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ y)
            rw [prune_eval (embed c) _ t S ht' hyS, hevt (embed c y), hvu y]
            ext z
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
              Finset.mem_singleton]
            exact ⟨fun h => h.imp (fun h1 => hembed_inj c h1) (fun h2 => hembed_inj c h2),
                   fun h => h.imp (congrArg (embed c)) (congrArg (embed c))⟩
          · rw [prune_leafCount (embed c) _ t S ht']
            have hScard : S.card = 2 ^ (n - d) := by
              rw [Finset.card_image_of_injective _ (hembed_inj c), Finset.card_univ, card_vec]
            have hfib : ∀ p ∈ S.image t.evalPath,
                (S.filter (fun x => t.evalPath x = p)).card = 2 := by
              intro p hp
              obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
              obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hxS
              have hsub : S.filter (fun z => t.evalPath z = t.evalPath (embed c y)) =
                  {embed c y, v (embed c y)} := by
                ext z
                simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
                constructor
                · rintro ⟨_, hzp⟩
                  have he := t.eval_eq_of_evalPath_eq hzp
                  rw [hevt z, hevt (embed c y)] at he
                  have hzin : z ∈ ({z, v z} : Finset (Vec n)) := by simp
                  rw [he] at hzin
                  simpa using hzin
                · rintro (rfl | rfl)
                  · exact ⟨Finset.mem_image_of_mem _ (Finset.mem_univ y), rfl⟩
                  · exact ⟨by rw [hvu y]; exact Finset.mem_image_of_mem _ (Finset.mem_univ (u y)),
                           evalPath_v hmv hevt hcntt (embed c y)⟩
              rw [hsub, Finset.card_pair (hmv (embed c y)).2.symm]
            have hsum : ∑ p ∈ S.image t.evalPath, (S.filter (fun x => t.evalPath x = p)).card = S.card := by
              rw [← Finset.card_biUnion]
              · congr 1
                ext x
                simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
                constructor
                · rintro ⟨_, _, hx, _⟩; exact hx
                · intro hx; exact ⟨t.evalPath x, ⟨x, hx, rfl⟩, hx, rfl⟩
              · intro p1 _ p2 _ hne
                dsimp only [Function.onFun]
                rw [Finset.disjoint_left]
                intro x hx1 hx2
                exact hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
            rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm] at hsum
            rw [hsum, hScard]
        ⟨u, hmu, htu⟩
      invFun := fun F =>
        let v : Vec n → Vec n := fun x => embed (T x).1 ((F (T x).1).val (T x).2)
        have hTv : ∀ x, T (v x) = ((T x).1, (F (T x).1).val (T x).2) := fun x => hT_embed _ _
        have hmv : IsMatching n v := by
          intro x
          have hFc := (F (T x).1).2.1
          constructor
          · apply T.injective
            rw [hTv, hTv, (hFc (T x).2).1]
          · intro heq
            have h2 := congrArg (fun z => (T z).2) heq
            rw [hTv] at h2
            exact (hFc (T x).2).2 h2
        have hAv : A ≤ invSub v := (hTinv v).mpr (fun x => by rw [hTv])
        have htv : HasTree n v := by
          rw [hasTree_iff_ptree]
          have htree : ∀ c : Vec d, ∃ tc : PTree (Vec (n - d)) (Finset (Vec (n - d))),
              tc.queriesOk (queries (Vec (n - d))) ∧
              (∀ y, tc.eval y = {y, (F c).val y}) ∧
              2 * tc.leafCount = 2 ^ (n - d) :=
            fun c => (hasTree_iff_ptree (n - d) (F c).val).mp (F c).2.2
          let tc : Vec d → PTree (Vec (n - d)) (Finset (Vec (n - d))) := fun c => Classical.choose (htree c)
          have htc : ∀ c, (tc c).queriesOk (queries (Vec (n - d))) ∧
              (∀ y, (tc c).eval y = {y, (F c).val y}) ∧
              2 * (tc c).leafCount = 2 ^ (n - d) := fun c => Classical.choose_spec (htree c)
          let π2 : Vec n →ₗ[ZMod 2] Vec (n - d) :=
            (LinearMap.snd (ZMod 2) (Vec d) (Vec (n - d))).comp T.toLinearMap
          let lifted : Vec d → PTree (Vec n) (Finset (Vec n)) :=
            fun c => mapTree π2 (fun B => B.image (embed c)) (tc c)
          let qCoord : ℕ → Vec n → Bool :=
            fun i x => if hi : i < d then decide (dot (e ⟨i, hi⟩) x = 1) else false
          let bigT : PTree (Vec n) (Finset (Vec n)) := stackTree qCoord d lifted
          refine ⟨bigT, ?_, ?_, ?_⟩
          · apply stackTree_queriesOk
            · intro i hi
              refine ⟨dotL (e ⟨i, hi⟩), 1, ?_⟩
              ext x
              simp only [qCoord, hi, ↓reduceDIte, dotL_apply]
              exact decide_eq_decide.mpr Iff.rfl
            · intro c
              apply mapTree_queriesOk π2 _ _ (tc c) (htc c).1
              rintro f ⟨l, b, rfl⟩
              exact ⟨l.comp π2, b, rfl⟩
          · intro x
            rw [stackTree_eval qCoord d lifted x (T x).1]
            · simp only [lifted, mapTree_eval, (htc (T x).1).2.1]
              have hpx : π2 x = (T x).2 := rfl
              rw [hpx, Finset.image_insert, Finset.image_singleton]
              have hxemb : embed (T x).1 (T x).2 = x := by
                change T.symm ((T x).1, (T x).2) = x
                simp
              rw [hxemb]
            · intro i
              simp [qCoord, i.isLt, hT1 x i]
          · rw [stackTree_leafCount, Finset.mul_sum]
            have hterm : ∀ c : Vec d, 2 * (lifted c).leafCount = 2 ^ (n - d) := by
              intro c
              simp only [lifted, mapTree_leafCount]
              exact (htc c).2.2
            rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_const, Finset.card_univ,
              card_vec, smul_eq_mul, ← pow_add, Nat.add_sub_of_le (hA ▸ finrank_le_dim A)]
        ⟨v, ⟨hmv, htv⟩, hAv⟩
      left_inv := by
        rintro ⟨v, ⟨hmv, htv⟩, hAv⟩
        apply Subtype.ext
        funext x
        have hv1 : ∀ z, (T (v z)).1 = (T z).1 := (hTinv v).mp hAv
        change embed (T x).1 (T (v (embed (T x).1 (T x).2))).2 = v x
        have hxemb : embed (T x).1 (T x).2 = x := by
          change T.symm ((T x).1, (T x).2) = x; simp
        rw [hxemb]
        apply T.injective
        rw [hT_embed]
        exact Prod.ext (hv1 x).symm rfl
      right_inv := by
        intro F
        funext c
        apply Subtype.ext
        funext z
        change (T (embed (T (embed c z)).1 ((F (T (embed c z)).1).val (T (embed c z)).2))).2 =
          (F c).val z
        rw [hT_embed, hT_embed] }
  rw [Nat.card_congr hGood_equiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Vec d), card_vec]
  rfl

noncomputable instance fintypeSubmodule (n : ℕ) : Fintype (Submodule (ZMod 2) (Vec n)) :=
  Fintype.ofFinite _

noncomputable instance fintypeLinearMap {n : ℕ} (B : Submodule (ZMod 2) (Vec n)) :
    Fintype (B →ₗ[ZMod 2] ZMod 2) :=
  @Fintype.ofFinite _ (Finite.of_injective DFunLike.coe DFunLike.coe_injective)

lemma card_linearMap_zmod2 {n : ℕ} (B : Submodule (ZMod 2) (Vec n)) :
    Fintype.card (B →ₗ[ZMod 2] ZMod 2) = 2 ^ (Module.finrank (ZMod 2) B) := by
  let b := Module.finBasis (ZMod 2) B
  let e1 : (B →ₗ[ZMod 2] ZMod 2) ≃ (Vec (Module.finrank (ZMod 2) B) →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun f => f.comp b.equivFun.symm.toLinearMap
      invFun := fun g => g.comp b.equivFun.toLinearMap
      left_inv := fun f => by
        apply LinearMap.ext; intro x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      right_inv := fun g => by
        apply LinearMap.ext; intro x
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }
  rw [Fintype.card_congr (e1.trans (dotEquiv _).toEquiv.symm), card_vec]

lemma choose_succ_two (m : ℕ) : Nat.choose (m + 1) 2 = Nat.choose m 2 + m := by
  simp [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]

lemma sum_subspaces_eq_zero {n : ℕ} (W : Submodule (ZMod 2) (Vec n)) (hW : W ≠ ⊥) :
    ∑ A ∈ Finset.univ.filter (fun A : Submodule (ZMod 2) (Vec n) => A ≤ W),
      (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2) = 0 := by
  have hex : ∃ u ∈ W, u ≠ 0 := by
    by_contra h
    push Not at h
    exact hW ((Submodule.eq_bot_iff W).mpr h)
  obtain ⟨u, huW, hu0⟩ := hex
  have hex_i : ∃ i : Fin n, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨i0, hi0⟩ := hex_i
  have hui0 : u i0 = 1 := zmod2_eq_one_of_ne_zero hi0
  let π : Vec n →ₗ[ZMod 2] Vec n :=
    LinearMap.id + (LinearMap.proj i0).smulRight u
  have hπ_apply : ∀ x, π x = x + x i0 • u := fun _ => rfl
  have hπu : π u = 0 := by
    ext j
    simp [hπ_apply, hui0, zmod2_add_self]
  have hπi0 : ∀ x, (π x) i0 = 0 := by
    intro x
    simp [hπ_apply, hui0, zmod2_add_self]
  have hπW : ∀ x ∈ W, π x ∈ W := fun x hx =>
    W.add_mem hx (W.smul_mem (x i0) huW)
  let H : Submodule (ZMod 2) (Vec n) := W ⊓ LinearMap.ker (LinearMap.proj i0)
  have hπ_mem_H : ∀ x ∈ W, π x ∈ H := fun x hx =>
    ⟨hπW x hx, by simp [LinearMap.mem_ker, hπi0 x]⟩
  have hπ_on_H : ∀ x ∈ H, π x = x := by
    intro x hx
    have hx0 : x i0 = 0 := hx.2
    simp [hπ_apply, hx0]
  have hπ_eq_zero : ∀ x, π x = 0 → x = 0 ∨ x = u := by
    intro x hx
    rcases zmod2_cases (x i0) with h0 | h1
    · left
      simpa [hπ_apply, h0] using hx
    · right
      ext j
      have hj := congrFun hx j
      simp only [hπ_apply, h1, one_smul, Pi.add_apply, Pi.zero_apply] at hj
      have := congrArg (· + u j) hj
      simpa [add_assoc, zmod2_add_self] using this
  let F : Finset (Submodule (ZMod 2) (Vec n)) := Finset.univ.filter (· ≤ W)
  let G : Finset (Submodule (ZMod 2) (Vec n)) := Finset.univ.filter (· ≤ H)
  have hmaps : ∀ A ∈ F, A.map π ∈ G := by
    intro A hA
    rw [Finset.mem_filter] at hA ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact hπ_mem_H a (hA.2 ha)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_eq_zero
  intro B hB
  have hBH : B ≤ H := (Finset.mem_filter.mp hB).2
  have hBW : B ≤ W := hBH.trans inf_le_left
  let FB := F.filter (fun A => A.map π = B)
  rw [← Finset.sum_filter_add_sum_filter_not FB (fun A => u ∈ A)]
  let Atop : Submodule (ZMod 2) (Vec n) := B ⊔ Submodule.span (ZMod 2) {u}
  have hIn_eq : FB.filter (fun A => u ∈ A) = {Atop} := by
    ext A
    simp only [FB, F, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hAW, hAmap⟩, huA⟩
      apply le_antisymm
      · intro a ha
        have hpa : π a ∈ B := hAmap ▸ ⟨a, ha, rfl⟩
        have hdec : a = π a + a i0 • u := by
          ext j
          simp only [hπ_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          rw [add_assoc, zmod2_add_self, add_zero]
        rw [hdec]
        exact Submodule.add_mem _ (Submodule.mem_sup_left hpa)
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))))
      · refine sup_le ?_ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huA))
        intro b hb
        rw [← hAmap] at hb
        rcases hb with ⟨a, ha, rfl⟩
        exact A.add_mem ha (A.smul_mem _ huA)
    · rintro rfl
      refine ⟨⟨sup_le hBW (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huW)), ?_⟩,
              Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u))⟩
      rw [Submodule.map_sup]
      have hBmap : B.map π = B := by
        ext x
        simp only [Submodule.mem_map]
        exact ⟨by rintro ⟨b, hb, rfl⟩; rwa [hπ_on_H b (hBH hb)],
               fun hx => ⟨x, hx, hπ_on_H x (hBH hx)⟩⟩
      have humap : (Submodule.span (ZMod 2) {u}).map π = ⊥ := by
        rw [Submodule.map_span, Set.image_singleton, hπu, Submodule.span_singleton_eq_bot]
      rw [hBmap, humap, sup_bot_eq]
  have hAtop_dim : Module.finrank (ZMod 2) Atop = Module.finrank (ZMod 2) B + 1 := by
    have hinf : B ⊓ Submodule.span (ZMod 2) {u} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxB, hxu⟩ := hx
      rw [SetLike.mem_coe, Submodule.mem_span_singleton] at hxu
      obtain ⟨c, rfl⟩ := hxu
      have hx0 : (c • u) i0 = 0 := (hBH hxB).2
      simp only [Pi.smul_apply, smul_eq_mul, hui0, mul_one] at hx0
      simp [hx0]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq B (Submodule.span (ZMod 2) {u})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hu0] at hsum
    exact hsum
  let mkEquiv : ∀ (A : Submodule (ZMod 2) (Vec n)), A.map π = B → u ∉ A → (A ≃ₗ[ZMod 2] B) :=
    fun A hAmap huA =>
      let φ : A →ₗ[ZMod 2] B :=
        (π.comp A.subtype).codRestrict B (fun a => hAmap ▸ ⟨a.1, a.2, rfl⟩)
      have hφbij : Function.Bijective φ := by
        constructor
        · intro a1 a2 heq
          have h0 : π (a1.1 - a2.1) = 0 := by
            rw [map_sub, sub_eq_zero]
            exact congrArg Subtype.val heq
          rcases hπ_eq_zero _ h0 with h | h
          · exact Subtype.ext (sub_eq_zero.mp h)
          · exact absurd (h ▸ A.sub_mem a1.2 a2.2) huA
        · intro b
          have hb : b.1 ∈ A.map π := hAmap.symm ▸ b.2
          rcases hb with ⟨a, ha, hab⟩
          exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
      LinearEquiv.ofBijective φ hφbij
  have hOut_dim : ∀ A ∈ FB.filter (fun A => u ∉ A),
      Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) B := by
    intro A hA
    simp only [FB, F, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    exact (mkEquiv A hA.1.2 hA.2).finrank_eq
  have hOut_card : (FB.filter (fun A => u ∉ A)).card = 2 ^ (Module.finrank (ZMod 2) B) := by
    let eOut : {A : Submodule (ZMod 2) (Vec n) // A ∈ FB.filter (fun A => u ∉ A)} ≃
        (B →ₗ[ZMod 2] ZMod 2) :=
      { toFun := fun ⟨A, hA⟩ =>
          have hA' : A ≤ W ∧ A.map π = B ∧ u ∉ A := by
            simp only [FB, F, Finset.mem_filter, Finset.mem_univ, true_and] at hA
            exact ⟨hA.1.1, hA.1.2, hA.2⟩
          (LinearMap.proj i0).comp (A.subtype.comp (mkEquiv A hA'.2.1 hA'.2.2).symm.toLinearMap)
        invFun := fun f =>
          let gf : B →ₗ[ZMod 2] Vec n := B.subtype + f.smulRight u
          let Af : Submodule (ZMod 2) (Vec n) := LinearMap.range gf
          have hAfW : Af ≤ W := by
            rintro _ ⟨b, rfl⟩
            exact W.add_mem (hBW b.2) (W.smul_mem _ huW)
          have hAfmap : Af.map π = B := by
            ext x
            simp only [Submodule.mem_map, Af, LinearMap.mem_range, gf]
            constructor
            · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
              have h1 : π (b.1 + f b • u) = b.1 := by
                rw [map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H b.1 (hBH b.2)]
              simp [h1]
            · intro hx
              refine ⟨x + f ⟨x, hx⟩ • u, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
              rw [map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H x (hBH hx)]
          have huAf : u ∉ Af := by
            rintro ⟨b, hb⟩
            have h1 := congrArg π hb
            simp only [gf, LinearMap.add_apply, Submodule.coe_subtype, LinearMap.smulRight_apply,
              map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H b.1 (hBH b.2)] at h1
            have hb0 : b = 0 := Subtype.ext h1
            subst hb0
            simp only [gf, map_zero] at hb
            exact hu0 hb.symm
          ⟨Af, by simp [FB, F, hAfW, hAfmap, huAf]⟩
        left_inv := by
          rintro ⟨A, hA⟩
          apply Subtype.ext
          have hA' : A ≤ W ∧ A.map π = B ∧ u ∉ A := by
            simp only [FB, F, Finset.mem_filter, Finset.mem_univ, true_and] at hA
            exact ⟨hA.1.1, hA.1.2, hA.2⟩
          let eA : A ≃ₗ[ZMod 2] B := mkEquiv A hA'.2.1 hA'.2.2
          ext x
          simp only [LinearMap.mem_range, LinearMap.add_apply, Submodule.coe_subtype,
            LinearMap.smulRight_apply, LinearMap.comp_apply, LinearMap.proj_apply]
          constructor
          · rintro ⟨b, rfl⟩
            let ha : A := eA.symm b
            have hπa : π ha.1 = b.1 := by
              have := eA.apply_symm_apply b
              exact congrArg Subtype.val this
            have hxeq : b.1 + ha.1 i0 • u = ha.1 := by
              rw [← hπa]
              ext j
              simp only [hπ_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              rw [add_assoc, zmod2_add_self, add_zero]
            change b.1 + ha.1 i0 • u ∈ A
            rw [hxeq]
            exact ha.2
          · intro hxA
            let b : B := ⟨π x, hA'.2.1 ▸ ⟨x, hxA, rfl⟩⟩
            refine ⟨b, ?_⟩
            have hsym : (eA.symm b).1 = x := by
              have h1 : eA ⟨x, hxA⟩ = b := Subtype.ext rfl
              have h2 := congrArg eA.symm h1
              simpa using congrArg Subtype.val h2.symm
            change b.1 + (eA.symm b).1 i0 • u = x
            rw [hsym]
            ext j
            simp only [b, hπ_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            rw [add_assoc, zmod2_add_self, add_zero]
        right_inv := by
          intro f
          apply LinearMap.ext; intro b
          let gf : B →ₗ[ZMod 2] Vec n := B.subtype + f.smulRight u
          let Af : Submodule (ZMod 2) (Vec n) := LinearMap.range gf
          have hAfmap : Af.map π = B := by
            ext x
            simp only [Submodule.mem_map, Af, LinearMap.mem_range, gf]
            constructor
            · rintro ⟨_, ⟨b', rfl⟩, rfl⟩
              have h1 : π (b'.1 + f b' • u) = b'.1 := by
                rw [map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H b'.1 (hBH b'.2)]
              simp [h1]
            · intro hx
              refine ⟨x + f ⟨x, hx⟩ • u, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
              rw [map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H x (hBH hx)]
          have huAf : u ∉ Af := by
            rintro ⟨b', hb'⟩
            have h1 := congrArg π hb'
            simp only [gf, LinearMap.add_apply, Submodule.coe_subtype, LinearMap.smulRight_apply,
              map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H b'.1 (hBH b'.2)] at h1
            have hb0 : b' = 0 := Subtype.ext h1
            subst hb0
            simp only [gf, map_zero] at hb'
            exact hu0 hb'.symm
          let eAf : Af ≃ₗ[ZMod 2] B := mkEquiv Af hAfmap huAf
          have hmem : gf b ∈ Af := ⟨b, rfl⟩
          have hπg : π (gf b) = b.1 := by
            simp only [gf, LinearMap.add_apply, Submodule.coe_subtype, LinearMap.smulRight_apply,
              map_add, map_smul, hπu, smul_zero, add_zero, hπ_on_H b.1 (hBH b.2)]
          have hsym : (eAf.symm b).1 = gf b := by
            have h1 : eAf ⟨gf b, hmem⟩ = b := Subtype.ext hπg
            have h2 := congrArg eAf.symm h1
            simpa using congrArg Subtype.val h2.symm
          change (eAf.symm b).1 i0 = f b
          rw [hsym]
          have hb0 : b.1 i0 = 0 := (hBH b.2).2
          simp [gf, hb0, hui0] }
    rw [← Fintype.card_coe, Fintype.card_congr eOut, card_linearMap_zmod2]
  rw [hIn_eq, Finset.sum_singleton, hAtop_dim]
  rw [Finset.sum_congr rfl (fun A hA => by rw [hOut_dim A hA])]
  rw [Finset.sum_const, hOut_card, nsmul_eq_mul]
  set m := Module.finrank (ZMod 2) B
  rw [choose_succ_two, pow_add, pow_succ]
  push_cast
  ring

lemma count_zero : count 0 = 0 := by
  simp only [count]
  have hemp : IsEmpty {v : Vec 0 → Vec 0 // Good 0 v} := by
    refine ⟨fun ⟨v, hm, _⟩ => ?_⟩
    exact (hm 0).2 (Subsingleton.elim _ _)
  rw [Nat.card_eq_fintype_card]
  exact @Fintype.card_eq_zero _ _ hemp

lemma count_one : count 1 = 1 := by
  simp only [count]
  let v0 : Vec 1 → Vec 1 := fun x i => x i + 1
  have hv0 : Good 1 v0 := by
    refine ⟨?_, ?_⟩
    · intro x
      constructor
      · ext i; simp [v0, add_assoc, zmod2_add_self]
      · intro h
        have := congrFun h 0
        simp [v0] at this
    · rw [hasTree_iff_ptree]
      refine ⟨PTree.leaf Finset.univ, trivial, ?_, by simp [PTree.leafCount]⟩
      intro x
      ext y
      simp only [PTree.eval, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases zmod2_cases (x 0) with hx0 | hx0 <;> rcases zmod2_cases (y 0) with hy0 | hy0
      · left; ext i; have hi : i = 0 := Subsingleton.elim i 0; subst hi; rw [hy0, hx0]
      · right; ext i; have hi : i = 0 := Subsingleton.elim i 0; subst hi; simp [v0, hx0, hy0]
      · right; ext i; have hi : i = 0 := Subsingleton.elim i 0; subst hi; simp [v0, hx0, hy0]; decide
      · left; ext i; have hi : i = 0 := Subsingleton.elim i 0; subst hi; rw [hy0, hx0]
  have huniq : Unique {v : Vec 1 → Vec 1 // Good 1 v} :=
    { default := ⟨v0, hv0⟩
      uniq := fun ⟨v, hm, _⟩ => by
        apply Subtype.ext
        ext x i
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        have hne : v x 0 ≠ x 0 := by
          intro h
          apply (hm x).2
          ext j; have hj : j = 0 := Subsingleton.elim j 0; subst hj; exact h
        rcases zmod2_cases (x 0) with hx0 | hx0 <;> rcases zmod2_cases (v x 0) with hvx0 | hvx0
        · exact absurd (hvx0.trans hx0.symm) hne
        · simp [v0, hx0, hvx0]
        · simp [v0, hx0, hvx0]; decide
        · exact absurd (hvx0.trans hx0.symm) hne }
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_unique

lemma gauss_zero (n : ℕ) : gauss n 0 = 1 := by
  simp only [gauss]
  have huniq : Unique {A : Submodule (ZMod 2) (Vec n) // Module.finrank (ZMod 2) A = 0} :=
    { default := ⟨⊥, finrank_bot (ZMod 2) (Vec n)⟩
      uniq := fun ⟨A, hA⟩ => Subtype.ext (Submodule.finrank_eq_zero.mp hA) }
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_unique

lemma main_recurrence (n : ℕ) (hn : 2 ≤ n) :
    (count n : ℤ) = (Finset.Icc 1 n).sum (fun d =>
      (-1 : ℤ) ^ (d + 1) * 2 ^ (Nat.choose d 2) * (gauss n d : ℤ) * (count (n - d) : ℤ) ^ (2 ^ d)) := by
  let Vgood : Finset (Vec n → Vec n) := Finset.univ.filter (Good n)
  have hzero :
      ∑ v ∈ Vgood,
        ∑ A ∈ Finset.univ.filter (fun A : Submodule (ZMod 2) (Vec n) => A ≤ invSub v),
          (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact sum_subspaces_eq_zero (invSub v) (invSub_ne_bot hn (Finset.mem_filter.mp hv).2)
  have hswap :
      ∑ v ∈ Vgood,
        ∑ A ∈ Finset.univ.filter (fun A : Submodule (ZMod 2) (Vec n) => A ≤ invSub v),
          (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2) =
      ∑ A : Submodule (ZMod 2) (Vec n),
        (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2) *
          ((Vgood.filter (fun v => A ≤ invSub v)).card : ℤ) := by
    trans (∑ v ∈ Vgood, ∑ A : Submodule (ZMod 2) (Vec n),
      if A ≤ invSub v then
        (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2)
      else 0)
    · refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.sum_filter]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun A _ => ?_)
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hfib_card : ∀ A : Submodule (ZMod 2) (Vec n),
      (Vgood.filter (fun v => A ≤ invSub v)).card =
        (count (n - Module.finrank (ZMod 2) A)) ^ (2 ^ (Module.finrank (ZMod 2) A)) := by
    intro A
    have heq : (Vgood.filter (fun v => A ≤ invSub v)).card =
        Nat.card {v : Vec n → Vec n // Good n v ∧ A ≤ invSub v} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext v
      simp [Vgood]
    rw [heq]
    exact card_good_respecting A rfl
  have hgroup :
      ∑ A : Submodule (ZMod 2) (Vec n),
        (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2) *
          ((Vgood.filter (fun v => A ≤ invSub v)).card : ℤ) =
      ∑ d ∈ Finset.Icc 0 n,
        (-1 : ℤ) ^ d * 2 ^ (Nat.choose d 2) * (gauss n d : ℤ) * (count (n - d) : ℤ) ^ (2 ^ d) := by
    have hmaps : ∀ A ∈ (Finset.univ : Finset (Submodule (ZMod 2) (Vec n))),
        Module.finrank (ZMod 2) A ∈ Finset.Icc 0 n :=
      fun A _ => Finset.mem_Icc.mpr ⟨Nat.zero_le _, finrank_le_dim A⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have hconst : ∀ (A : Submodule (ZMod 2) (Vec n)),
        A ∈ (Finset.univ : Finset (Submodule (ZMod 2) (Vec n))).filter
          (fun S : Submodule (ZMod 2) (Vec n) => Module.finrank (ZMod 2) S = d) →
        (-1 : ℤ) ^ (Module.finrank (ZMod 2) A) * 2 ^ (Nat.choose (Module.finrank (ZMod 2) A) 2) *
          ((Vgood.filter (fun v => A ≤ invSub v)).card : ℤ) =
        (-1 : ℤ) ^ d * 2 ^ (Nat.choose d 2) * (count (n - d) : ℤ) ^ (2 ^ d) := by
      intro A hA
      have hd : Module.finrank (ZMod 2) A = d := (Finset.mem_filter.mp hA).2
      rw [hfib_card A, hd]
      push_cast
      rfl
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    have hgc : ((Finset.univ : Finset (Submodule (ZMod 2) (Vec n))).filter
        (fun A : Submodule (ZMod 2) (Vec n) => Module.finrank (ZMod 2) A = d)).card = gauss n d := by
      rw [gauss, Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hgc]
    ring
  have htotal :
      ∑ d ∈ Finset.Icc 0 n,
        (-1 : ℤ) ^ d * 2 ^ (Nat.choose d 2) * (gauss n d : ℤ) * (count (n - d) : ℤ) ^ (2 ^ d) = 0 := by
    rw [← hgroup, ← hswap, hzero]
  have hsplit : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext d
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hsplit, Finset.sum_insert (by simp)] at htotal
  simp only [pow_zero, Nat.choose_zero_succ, one_mul, gauss_zero,
    Nat.cast_one, mul_one, Nat.sub_zero, pow_one] at htotal
  have hneg :
      (Finset.Icc 1 n).sum (fun d =>
        (-1 : ℤ) ^ d * 2 ^ (Nat.choose d 2) * (gauss n d : ℤ) * (count (n - d) : ℤ) ^ (2 ^ d)) =
      - (Finset.Icc 1 n).sum (fun d =>
        (-1 : ℤ) ^ (d + 1) * 2 ^ (Nat.choose d 2) * (gauss n d : ℤ) * (count (n - d) : ℤ) ^ (2 ^ d)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [pow_succ]
    ring
  rw [hneg] at htotal
  linarith

end PEqualNP.Outside.L_pcx_359_aux

theorem PEqualNP.Outside.L_pcx_359 : (let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  let count := fun k : ℕ =>
    let X := Fin k → ZMod 2
    Nat.card {v : X → X //
      (∀ x, v (v x) = x ∧ v x ≠ x) ∧
      ∃ (N J : Finset (List Bool)) (q : List Bool → X → Bool) (out : List Bool → Finset X),
        cert (queries X) (fun x a => a = {x, v x}) N J q out ∧ 2*(N \ J).card = 2^k}
  let gauss := fun (k d : ℕ) => Nat.card
    {A : Submodule (ZMod 2) (Fin k → ZMod 2) // Module.finrank (ZMod 2) A = d}
  count 0 = 0 ∧ count 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n →
    (count n : ℤ) = (Finset.Icc 1 n).sum (fun d =>
      (-1 : ℤ)^(d+1) * 2^(Nat.choose d 2) * (gauss n d : ℤ) * (count (n-d) : ℤ)^(2^d))) := by
  exact ⟨PEqualNP.Outside.L_pcx_359_aux.count_zero,
         PEqualNP.Outside.L_pcx_359_aux.count_one,
         PEqualNP.Outside.L_pcx_359_aux.main_recurrence⟩
