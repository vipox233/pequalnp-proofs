import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fintype.EquivFin
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_511_aux

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Lit (n : ℕ) := Fin n × Bool
abbrev Fml (n : ℕ) := Finset (Lit n × Lit n)

def sat {n : ℕ} (C : Fml n) (w : Word n) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
def count {n : ℕ} (C : Fml n) : ℕ :=
  (Finset.univ.filter (fun w => sat C w = true)).card

def hull {n : ℕ} {pool : Finset (Word n)} (label : ↥pool → Bool) (z : Word n) : Prop :=
  ∀ i j : Fin n, ∃ q : ↥pool, label q = true ∧ q.val i = z i ∧ q.val j = z j

noncomputable def decode {n : ℕ} {pool : Finset (Word n)} (label : ↥pool → Bool) : Bool := by
  classical
  exact decide (2^n < 2*(Finset.univ.filter (hull label)).card)

def correct {n s : ℕ} {pool : Finset (Word n)} (classify : (↥pool → Bool) → Bool) : Prop :=
  ∀ A : Fml n, let v := classify (fun q => sat A q.val)
    (2*count A ≤ 2^n → v = false) ∧
      (2^n*(2^(s-1)+1) ≤ 2^s*count A → v = true)

theorem hull_sound {n : ℕ} {pool : Finset (Word n)} (A : Fml n) (z : Word n)
    (h : hull (pool:=pool) (fun q => sat A q.val) z) : sat A z = true := by
  unfold sat
  rw [decide_eq_true_eq]
  intro c hc
  obtain ⟨q,hq,h₁,h₂⟩ := h c.1.1 c.2.1
  have satq : ∀ k ∈ A, q.val k.1.1 ≠ k.1.2 ∨ q.val k.2.1 ≠ k.2.2 := by
    simpa only [sat,decide_eq_true_eq] using hq
  simpa only [h₁,h₂] using satq c hc

theorem decode_false {n : ℕ} {pool : Finset (Word n)} (A : Fml n) (h : 2*count A ≤ 2^n) :
    decode (pool:=pool) (fun q => sat A q.val) = false := by
  classical
  unfold decode
  rw [decide_eq_false_iff_not]
  apply Nat.not_lt_of_ge
  refine (Nat.mul_le_mul_left 2 ?_).trans h
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hull_sound A w (Finset.mem_filter.mp hw).2⟩

theorem indistinguishable {n s : ℕ} {pool : Finset (Word n)} (A B : Fml n)
    (low : 2*count A ≤ 2^n) (high : 2^n*(2^(s-1)+1) ≤ 2^s*count B)
    (same : ∀ q ∈ pool, sat A q = sat B q) :
    ¬ ∃ f, correct (s:=s) (pool:=pool) f := by
  rintro ⟨f,hf⟩
  have hl := (hf A).1 low
  have hh := (hf B).2 high
  have eq : (fun q : ↥pool => sat A q.val) = (fun q : ↥pool => sat B q.val) := by
    funext q
    exact same q.val q.property
  rw [eq,hh] at hl
  contradiction


def cube {n : ℕ} (S : Finset (Fin n)) (pat : Word n) : Finset (Word n) :=
  Finset.univ.filter fun w => ∀ i ∈ S, w i = pat i

def cubeEquiv {n : ℕ} (S : Finset (Fin n)) (pat : Word n) :
    (↥(cube S pat)) ≃ ({i : Fin n // i ∉ S} → Bool) where
  toFun x i := x.val i.val
  invFun f := ⟨fun j => if hj : j ∈ S then pat j else f ⟨j,hj⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j hj => by simp [hj]⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases hj : j ∈ S
    · simp only [dif_pos hj]
      exact ((Finset.mem_filter.mp x.property).2 j hj).symm
    · simp [hj]
  right_inv f := by
    funext i
    simp [i.property]

theorem cube_card {n : ℕ} (S : Finset (Fin n)) (pat : Word n) :
    (cube S pat).card = 2^(n-S.card) := by
  classical
  have hc : Fintype.card {i : Fin n // i ∉ S} = n-S.card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_subtype_compl (fun i : Fin n => i ∈ S)
  have e := Fintype.card_congr (cubeEquiv S pat)
  simpa [hc,Fintype.card_fun] using e


def covers {n s : ℕ} (pool : Finset (Word n)) : Prop :=
  ∀ S : Finset (Fin n), S.card ≤ s → ∀ pat : Word n,
    ∃ x ∈ pool, ∀ bit ∈ S, x bit = pat bit

def unit {n : ℕ} (i : Fin n) (b : Bool) : Fml n := {((i,b),(i,b))}
def star {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (pat : Word n) : Fml n :=
  (S.erase i).image fun j => ((i,pat i),(j,!pat j))
def easy {n : ℕ} (i : Fin n) (pat : Word n) : Finset (Word n) :=
  cube {i} (fun j => !pat j)

theorem bad_iff_not_bit (a b : Bool) : (a ≠ b) ↔ a = !b := by
  cases a <;> cases b <;> decide
theorem not_bad_iff_bit (a b : Bool) : (a ≠ !b) ↔ a = b := by
  cases a <;> cases b <;> decide

theorem mem_easy {n : ℕ} (i : Fin n) (pat w : Word n) :
    w ∈ easy i pat ↔ w i ≠ pat i := by
  simp [easy,cube,bad_iff_not_bit]

theorem unit_sat {n : ℕ} (i : Fin n) (pat w : Word n) :
    sat (unit i (pat i)) w = true ↔ w ∈ easy i pat := by
  rw [mem_easy]
  simp [sat,unit]

theorem star_sat {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (pat w : Word n) :
    sat (star S i pat) w = true ↔ w ∈ easy i pat ∪ cube S pat := by
  classical
  rw [sat, decide_eq_true_eq, Finset.mem_union, mem_easy]
  constructor
  · intro h
    by_cases hw : w i = pat i
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro j hj
      by_cases e : j = i
      · simpa [e] using hw
      have hclause := h ((i,pat i),(j,!pat j))
        (Finset.mem_image.mpr ⟨j,Finset.mem_erase.mpr ⟨e,hj⟩,rfl⟩)
      exact (not_bad_iff_bit _ _).mp (hclause.resolve_left (not_not_intro hw))
    · exact Or.inl hw
  · intro h q hq
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
    rcases h with he | hc
    · exact Or.inl he
    · exact Or.inr ((not_bad_iff_bit _ _).mpr
        ((Finset.mem_filter.mp hc).2 j (Finset.mem_of_mem_erase hj)))

theorem easy_card {n : ℕ} (i : Fin n) (pat : Word n) :
    (easy i pat).card = 2^(n-1) := by simp [easy,cube_card]

theorem unit_count {n : ℕ} (i : Fin n) (pat : Word n) :
    count (unit i (pat i)) = 2^(n-1) := by
  rw [←easy_card i pat]
  unfold count
  apply congrArg Finset.card
  ext w
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,unit_sat]

theorem star_count {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (pat : Word n) :
    count (star S i pat) = 2^(n-1)+2^(n-S.card) := by
  have hset : Finset.univ.filter (fun w => sat (star S i pat) w = true) = easy i pat ∪ cube S pat := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,star_sat]
  have hd : Disjoint (easy i pat) (cube S pat) := by
    apply Finset.disjoint_left.mpr
    intro w he hc
    exact (mem_easy i pat w).mp he ((Finset.mem_filter.mp hc).2 i hi)
  unfold count
  rw [hset,Finset.card_union_of_disjoint hd,easy_card,cube_card]

theorem missed_no_classifier {n s : ℕ} {pool : Finset (Word n)}
    (hs : 1 ≤ s) (hsn : s ≤ n) (S : Finset (Fin n)) (hS : S.card ≤ s)
    (i : Fin n) (hi : i ∈ S) (pat : Word n) (missed : ∀ w ∈ pool, w ∉ cube S pat) :
    ¬ ∃ f, correct (s:=s) (pool:=pool) f := by
  have npos : 1 ≤ n := hs.trans hsn
  have eqn : 2*2^(n-1) = (2:ℕ)^n := by
    rw [Nat.mul_comm,←pow_succ,Nat.sub_add_cancel npos]
  have eqs : 2*2^(s-1) = (2:ℕ)^s := by
    rw [Nat.mul_comm,←pow_succ,Nat.sub_add_cancel hs]
  apply indistinguishable (unit i (pat i)) (star S i pat)
  · rw [unit_count i pat,eqn]
  · rw [star_count S i hi pat]
    have hmass : (2:ℕ)^n ≤ 2^s*2^(n-S.card) := by
      calc
        (2:ℕ)^n = 2^s*2^(n-s) := by
          rw [←pow_add]
          congr 1
          omega
        _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    calc
      (2:ℕ)^n*(2^(s-1)+1) = 2^n*2^(s-1)+2^n := by ring
      _ ≤ 2^s*2^(n-1)+2^s*2^(n-S.card) := by
        apply Nat.add_le_add _ hmass
        rw [←eqn,←eqs]
        ring_nf
        exact le_rfl
      _ = _ := by ring
  · intro w hw
    have e : (sat (unit i (pat i)) w = true) ↔ (sat (star S i pat) w = true) := by
      rw [unit_sat,star_sat,Finset.mem_union]
      simp [missed w hw]
    cases hl : sat (unit i (pat i)) w <;> cases hr : sat (star S i pat) w <;>
      simp_all

theorem classifier_implies_covers {n s : ℕ} {pool : Finset (Word n)} (hs : 1 ≤ s) (hsn : s ≤ n)
    (h : ∃ f, correct (s:=s) (pool:=pool) f) : covers (s:=s) pool := by
  classical
  intro S hS pat
  by_contra no
  have missed : ∀ w ∈ pool, w ∉ cube S pat := by
    intro w hw hc
    exact no ⟨w,hw,(Finset.mem_filter.mp hc).2⟩
  rcases S.eq_empty_or_nonempty with e | ⟨i,hi⟩
  · let i : Fin n := ⟨0,by omega⟩
    have hm : ∀ w ∈ pool, w ∉ cube {i} pat := by
      intro w hw _
      apply missed w hw
      simp [e,cube]
    exact missed_no_classifier hs hsn {i} (by simpa using hs) i (by simp) pat hm h
  · exact missed_no_classifier hs hsn S hS i hi pat missed h


theorem pair_at {V : Type*} [DecidableEq V] {S : Finset V} (hc : S.card=2) {i : V} (hi : i∈S) :
    ∃ j, j≠i ∧ S={i,j} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl
  · exact ⟨b,Ne.symm hab,rfl⟩
  · exact ⟨a,hab,Finset.pair_comm _ _⟩

theorem edges_intersect_star_or_triangle {V : Type*} [DecidableEq V] (G : Finset (Finset V))
    (he : G.Nonempty) (hc : ∀ e ∈ G, e.card=2)
    (hx : ∀ e ∈ G, ∀ f ∈ G, ¬Disjoint e f) :
    (∃ i, ∀ e ∈ G, i ∈ e) ∨
      (∃ i j k : V, i ≠ j ∧ k ≠ i ∧ k ≠ j ∧
        ({i,j} : Finset V) ∈ G ∧ ({j,k} : Finset V) ∈ G ∧ ({i,k} : Finset V) ∈ G) := by
  classical
  obtain ⟨e,he⟩ := he
  obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (hc e he)
  by_cases hi : ∀ f ∈ G, i ∈ f
  · exact Or.inl ⟨i,hi⟩
  by_cases hj : ∀ f ∈ G, j ∈ f
  · exact Or.inl ⟨j,hj⟩
  push_neg at hi hj
  obtain ⟨f,hf,hif⟩ := hi
  obtain ⟨t,ht,hjt⟩ := hj
  have hjf : j∈f := by
    obtain ⟨v, hv, hvf⟩ := Finset.not_disjoint_iff.mp (hx _ he _ hf)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact False.elim (hif hvf)
    · exact hvf
  obtain ⟨k,hkj,rfl⟩ := pair_at (hc f hf) hjf
  have hki : k≠i := by
    rintro rfl
    exact hif (by simp)
  have hit : i∈t := by
    obtain ⟨v,hv,hvt⟩ := Finset.not_disjoint_iff.mp (hx _ he _ ht)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact hvt
    · exact False.elim (hjt hvt)
  have hkt : k∈t := by
    obtain ⟨v,hv,hvt⟩ := Finset.not_disjoint_iff.mp (hx _ hf _ ht)
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact False.elim (hjt hvt)
    · exact hvt
  have subt : ({i,k} : Finset V) ⊆ t := by
    intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl
    · exact hit
    · exact hkt
  have et : ({i,k} : Finset V) = t :=
    Finset.eq_of_subset_of_card_le subt (by rw [hc t ht]; simp [Ne.symm hki])
  exact Or.inr ⟨i,j,k,hij,hki,hkj,he,hf,et.symm ▸ ht⟩


abbrev Clause (n : ℕ) := Lit n × Lit n

def ends {n : ℕ} (c : Clause n) : Finset (Lit n) := {c.1,c.2}
def support {n : ℕ} (c : Clause n) : Finset (Fin n) := {c.1.1,c.2.1}
abbrev proper {n : ℕ} (c : Clause n) : Prop := c.1.1 ≠ c.2.1

def bad {n : ℕ} (c : Clause n) : Finset (Word n) :=
  Finset.univ.filter fun w => w c.1.1 = c.1.2 ∧ w c.2.1 = c.2.2
def solutions {n : ℕ} (A : Fml n) : Finset (Word n) :=
  Finset.univ.filter fun w => sat A w = true

theorem popcount (n : ℕ) : (Finset.univ : Finset (Word n)).card = 2^n := by
  simp [Word,Fintype.card_fun]

theorem pow_split (n k : ℕ) (hk : k ≤ n) : (2:ℕ)^n = 2^k * 2^(n-k) := by
  rw [←pow_add]
  congr 1
  omega

theorem cube_inter {n : ℕ} (S T : Finset (Fin n)) (w : Word n) :
    cube S w ∩ cube T w = cube (S∪T) w := by
  ext u
  simp only [cube, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ⟨a,b⟩ i hi
    rcases Finset.mem_union.mp hi with h|h
    · exact a i h
    · exact b i h
  · intro h
    exact ⟨fun i hi => h i (Finset.mem_union_left _ hi),fun i hi => h i (Finset.mem_union_right _ hi)⟩

theorem bad_uses_end {n : ℕ} {c : Clause n} {w : Word n}
    (hw : w∈bad c) {l : Lit n} (hl : l∈ends c) : w l.1 = l.2 := by
  have h := (Finset.mem_filter.mp hw).2
  simp only [ends, Finset.mem_insert,Finset.mem_singleton] at hl
  rcases hl with rfl|rfl
  · exact h.1
  · exact h.2

theorem bad_as_cube {n : ℕ} (c : Clause n) (b : Word n)
    (h1 : b c.1.1 = c.1.2) (h2 : b c.2.1 = c.2.2) : bad c = cube (support c) b := by
  ext w
  simp [bad,cube,support,h1,h2]

theorem bad_proper_card {n : ℕ} (c : Clause n) (hp : proper c) :
    (bad c).card = 2^(n-2) := by
  let b : Word n := fun i => if i=c.1.1 then c.1.2 else c.2.2
  have hn : c.1.1 ≠ c.2.1 := hp
  rw [bad_as_cube c b (by simp [b]) (by simp [b,Ne.symm hn]),cube_card]
  simp [support,hn]

theorem bad_disjoint_solutions {n : ℕ} {A : Fml n} {c : Clause n} (hc : c∈A) :
    Disjoint (solutions A) (bad c) := by
  apply Finset.disjoint_left.mpr
  intro w hw hbad
  have ha : sat A w = true := (Finset.mem_filter.mp hw).2
  rw [sat,decide_eq_true_eq] at ha
  obtain ⟨e1,e2⟩ := (Finset.mem_filter.mp hbad).2
  exact (ha c hc).elim (fun h => h e1) (fun h => h e2)

theorem forbidden_mass {n : ℕ} (A : Fml n) (B : Finset (Word n))
    (hd : Disjoint (solutions A) B) (size : 2^n ≤ 2*B.card) : 2*count A ≤ 2^n := by
  have h := Finset.card_le_card (Finset.subset_univ ((solutions A) ∪ B))
  rw [Finset.card_union_of_disjoint hd,popcount] at h
  change (count A)+B.card ≤ 2^n at h
  omega

theorem compatible_ends {n : ℕ} (hn : 2 ≤ n) {A : Fml n} (hd : 2^n < 2*count A)
    {c d : Clause n} (hc : c∈A) (hD : d∈A) (hc' : proper c) (hd' : proper d)
    {i : Fin n} {b v : Bool} (hb : (i,b)∈ends c) (hv : (i,v)∈ends d) : b=v := by
  by_contra no
  have dis : Disjoint (bad c) (bad d) := by
    apply Finset.disjoint_left.mpr
    intro w w1 w2
    exact no ((bad_uses_end w1 hb).symm.trans (bad_uses_end w2 hv))
  have hu : Disjoint (solutions A) (bad c ∪ bad d) := by
    exact Finset.disjoint_union_right.mpr ⟨bad_disjoint_solutions hc,bad_disjoint_solutions hD⟩
  have hcard : 2^n ≤ 2*(bad c ∪ bad d).card := by
    rw [Finset.card_union_of_disjoint dis,bad_proper_card c hc',bad_proper_card d hd',pow_split n 2 hn]
    omega
  exact (Nat.not_lt_of_ge (forbidden_mass A _ hu hcard)) hd

theorem improper_taut {n : ℕ} (hn : 1 ≤ n) {A : Fml n} (hd : 2^n < 2*count A)
    {c : Clause n} (hc : c∈A) (h : ¬proper c) : (bad c : Finset (Word n)) = ∅ := by
  have e : c.1.1=c.2.1 := not_ne_iff.mp h
  by_cases b : c.1.2=c.2.2
  · let pat : Word n := fun _ => c.1.2
    have shape : (bad c).card = 2^(n-1) := by
      rw [bad_as_cube c pat rfl b,cube_card]
      simp [support,e]
    have sz : 2^n ≤ 2*(bad c).card := by
      rw [shape,pow_split n 1 hn]
      exact le_rfl
    exact False.elim ((Nat.not_lt_of_ge (forbidden_mass A _ (bad_disjoint_solutions hc) sz)) hd)
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨x,y⟩ := (Finset.mem_filter.mp hw).2
    exact b (x.symm.trans (e ▸ y))


def occurs {n : ℕ} (A : Fml n) (i : Fin n) (v : Bool) : Prop :=
  ∃ c ∈ A, proper c ∧ (i,v) ∈ ends c

noncomputable def polarity {n : ℕ} (A : Fml n) : Word n := by
  classical
  exact fun i => if h : ∃ b, occurs A i b then h.choose else false

theorem polarity_correct {n : ℕ} (hn : 2 ≤ n) {A : Fml n} (high : 2^n < 2*count A)
    {i : Fin n} {v : Bool} (hv : occurs A i v) : polarity A i = v := by
  classical
  have h : ∃ b, occurs A i b := ⟨v,hv⟩
  unfold polarity
  rw [dif_pos h]
  obtain ⟨c,hc,hc',ec⟩ := h.choose_spec
  obtain ⟨d,hd,hd',ed⟩ := hv
  exact compatible_ends hn high hc hd hc' hd' ec ed

def edges {n : ℕ} (A : Fml n) : Finset (Finset (Fin n)) :=
  (A.filter proper).image support

def graphSol {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n))) : Finset (Word n) :=
  Finset.univ.filter fun w => ∀ e ∈ G, w ∉ cube e col

theorem graph_arity {n : ℕ} (A : Fml n) : ∀ e ∈ edges A, e.card=2 := by
  intro e he
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
  have hn : c.1.1 ≠ c.2.1 := (Finset.mem_filter.mp hc).2
  simp [support,hn]

theorem proper_bad_eq_graph_cube {n : ℕ} (hn : 2 ≤ n) {A : Fml n} (high : 2^n < 2*count A)
    {c : Clause n} (hc : c∈A) (hp : proper c) :
    bad c = cube (support c) (polarity A) := by
  apply bad_as_cube
  · exact polarity_correct hn high ⟨c,hc,hp,by simp [ends]⟩
  · exact polarity_correct hn high ⟨c,hc,hp,by simp [ends]⟩

theorem sat_iff_avoid {n : ℕ} (A : Fml n) (w : Word n) :
    sat A w = true ↔ ∀ c ∈ A, w ∉ bad c := by
  classical
  rw [sat,decide_eq_true_eq]
  constructor
  · intro h c hc hbad
    obtain ⟨a,b⟩ := (Finset.mem_filter.mp hbad).2
    exact (h c hc).elim (fun u=>u a) (fun u=>u b)
  · intro h c hc
    by_cases e : w c.1.1 = c.1.2
    · right
      intro f
      exact h c hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,f⟩)
    · exact Or.inl e

theorem normalize_graph {n : ℕ} (hn : 2 ≤ n) (A : Fml n) (high : 2^n < 2*count A) :
    solutions A = graphSol (polarity A) (edges A) := by
  classical
  ext w
  simp only [solutions,graphSol,Finset.mem_filter,Finset.mem_univ,true_and,sat_iff_avoid]
  constructor
  · intro h e he
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hc,hp⟩ := Finset.mem_filter.mp hc
    rw [←proper_bad_eq_graph_cube hn high hc hp]
    exact h c hc
  · intro h c hc
    by_cases hp : proper c
    · rw [proper_bad_eq_graph_cube hn high hc hp]
      exact h (support c) (Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr ⟨hc,hp⟩,rfl⟩)
    · rw [improper_taut (by omega) high hc hp]
      simp


theorem g_off {n : ℕ} {col : Word n} {G : Finset (Finset (Fin n))} {e : Finset (Fin n)}
    (he : e∈G) : Disjoint (graphSol col G) (cube e col) := by
  apply Finset.disjoint_left.mpr
  intro w hw heq
  exact (Finset.mem_filter.mp hw).2 e he heq

theorem g_forbidden {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n))) (B : Finset (Word n))
    (hd : Disjoint (graphSol col G) B) (hs : 2^n ≤ 2*B.card) :
    2*(graphSol col G).card ≤ 2^n := by
  have h := Finset.card_le_card (Finset.subset_univ (graphSol col G ∪ B))
  rw [Finset.card_union_of_disjoint hd,popcount] at h
  omega

theorem size_four {n : ℕ} {A B : Finset (Fin n)} (ha : A.card=2) (hb : B.card=2)
    (dis : Disjoint A B) : (A∪B).card=4 ∧ 4≤n := by
  have h : (A∪B).card=4 := by rw [Finset.card_union_of_disjoint dis,ha,hb]
  refine ⟨h,?_⟩
  have hc := Finset.card_le_card (Finset.subset_univ (A∪B))
  simpa only [h,Finset.card_univ,Fintype.card_fin] using hc

theorem two_bad_mass {n : ℕ} (col : Word n) {A B : Finset (Fin n)}
    (ha : A.card=2) (hb : B.card=2) (dis : Disjoint A B) :
    (cube A col ∪ cube B col).card=7*2^(n-4) := by
  obtain ⟨hcard,hn⟩ := size_four ha hb dis
  have eqpow : (2:ℕ)^(n-2) = 4*2^(n-4) := by
    rw [pow_split (n-2) 2 (by omega)]
    congr 2 <;> omega
  have mass := Finset.card_union_add_card_inter (cube A col) (cube B col)
  rw [cube_inter, cube_card, cube_card, cube_card, ha,hb,hcard,eqpow] at mass
  omega

theorem only_two_when_disjoint {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n)))
    (size : ∀ e ∈ G, e.card=2) (high : 2^n < 2*(graphSol col G).card)
    (A B : Finset (Fin n)) (ha : A∈G) (hb : B∈G) (dis : Disjoint A B) :
    G = {A,B} := by
  have na := size A ha
  have nb := size B hb
  obtain ⟨_,hn⟩ := size_four na nb dis
  apply Finset.Subset.antisymm
  · intro C hc
    by_contra no
    have eA : A≠C := fun e => no (by simp [←e])
    have eB : B≠C := fun e => no (by simp [←e])
    have needA : ¬ A ⊆ C := by
      intro sub
      exact eA (Finset.eq_of_subset_of_card_le sub (by rw [na,size C hc]))
    have needB : ¬ B ⊆ C := by
      intro sub
      exact eB (Finset.eq_of_subset_of_card_le sub (by rw [nb,size C hc]))
    obtain ⟨a,ma,naC⟩ := Finset.not_subset.mp needA
    obtain ⟨b,mb,nbC⟩ := Finset.not_subset.mp needB
    let S := insert a (insert b C)
    let pat : Word n := fun x => if x=a ∨ x=b then !col x else col x
    let V := cube S pat
    have sc : S.card≤4 := by
      have h1 := Finset.card_insert_le a (insert b C)
      have h2 := Finset.card_insert_le b C
      change (insert a (insert b C)).card ≤ 4
      have h3 := size C hc
      omega
    have sub : V ⊆ cube C col := by
      intro w hw
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro x hx
      have xna : x≠a := fun e => naC (e ▸ hx)
      have xnb : x≠b := fun e => nbC (e ▸ hx)
      have h := (Finset.mem_filter.mp hw).2 x (show x∈S from by simp [S,hx])
      simpa [pat,xna,xnb] using h
    have da : Disjoint (cube A col) V := by
      apply Finset.disjoint_left.mpr
      intro w hA hV
      have t := (Finset.mem_filter.mp hA).2 a ma
      have u := (Finset.mem_filter.mp hV).2 a (show a∈S from by simp [S])
      simpa [pat,t] using u
    have db : Disjoint (cube B col) V := by
      apply Finset.disjoint_left.mpr
      intro w hB hV
      have t := (Finset.mem_filter.mp hB).2 b mb
      have u := (Finset.mem_filter.mp hV).2 b (show b∈S from by simp [S])
      simpa [pat,t] using u
    let all := (cube A col ∪ cube B col) ∪ V
    have allDis : Disjoint (graphSol col G) all := by
      exact Finset.disjoint_union_right.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨g_off ha,g_off hb⟩,(g_off (col:=col) hc).mono_right sub⟩
    have hv : (2:ℕ)^(n-4) ≤ V.card := by
      unfold V
      rw [cube_card]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    have hm : 2^n ≤ 2*all.card := by
      unfold all
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨da,db⟩),
        two_bad_mass col na nb dis,pow_split n 4 hn]
      omega
    exact (Nat.not_lt_of_ge (g_forbidden col G all allDis hm)) high
  · intro C hc
    simp only [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl
    · exact ha
    · exact hb

theorem flipped_value (x y : Bool) (h : x ≠ y) : (!x)=y := by
  cases x <;> cases y <;> simp_all

theorem triangle_at_most_half {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n)))
    (i j k : Fin n) (hij : ({i,j} : Finset (Fin n))∈G)
    (hjk : ({j,k} : Finset (Fin n))∈G) (hik : ({i,k} : Finset (Fin n))∈G) :
    2*(graphSol col G).card ≤ 2^n := by
  classical
  let f : Word n → Word n := fun w a => !w a
  have map : Set.MapsTo f (↑(graphSol col G)) (↑(Finset.univ \ graphSol col G : Finset (Word n))) := by
    intro w hw
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro badFlip
    have good := (Finset.mem_filter.mp hw).2
    have inv := (Finset.mem_filter.mp badFlip).2
    have avoid {a b : Fin n} (h : ({a,b} : Finset (Fin n))∈G)
        (ha : w a = col a) (hb : w b = col b) : False :=
      good _ h (by simp [cube,ha,hb])
    have hit {a b : Fin n} (h : ({a,b} : Finset (Fin n))∈G)
        (ha : w a ≠ col a) (hb : w b ≠ col b) : False := by
      apply inv _ h
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl
      · exact flipped_value _ _ ha
      · exact flipped_value _ _ hb
    by_cases ci : w i = col i
    · exact hit hjk (avoid hij ci) (avoid hik ci)
    by_cases cj : w j = col j
    · exact hit hik ci (avoid hjk cj)
    · exact hit hij ci cj
  have inj : Set.InjOn f (↑(graphSol col G)) := by
    intro u _ v _ eq
    funext a
    have e := congrFun eq a
    change (!(u a)) = (!(v a)) at e
    simpa using congrArg (fun b : Bool => !b) e
  have bound := Finset.card_le_card_of_injOn f map inj
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),popcount] at bound
  have hn := Finset.card_le_card (Finset.subset_univ (graphSol col G))
  rw [popcount] at hn
  omega


def vertices {n : ℕ} (G : Finset (Finset (Fin n))) : Finset (Fin n) := G.biUnion id
def starPat {n : ℕ} (i : Fin n) (col : Word n) : Word n :=
  fun j => if j=i then col j else !col j

theorem easy_mem_graph {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n))) (i : Fin n)
    (center : ∀ e∈G,i∈e) (w : Word n) (he : w∈easy i col) : w∈graphSol col G := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,fun e he' hw => ?_⟩
  exact (mem_easy _ _ _).mp he ((Finset.mem_filter.mp hw).2 i (center e he'))

theorem star_graph_set {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n))) (i : Fin n)
    (size : ∀ e∈G,e.card=2) (center : ∀ e∈G,i∈e) :
    graphSol col G = easy i col ∪ cube (vertices G) (starPat i col) := by
  ext w
  rw [Finset.mem_union]
  constructor
  · intro hw
    by_cases hi : w i=col i
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro j hj
      by_cases hji : j=i
      · simpa [starPat,hji] using hi
      obtain ⟨e,he,mj⟩ := Finset.mem_biUnion.mp hj
      obtain ⟨k,hki,rfl⟩ := pair_at (size e he) (center e he)
      have jk : j=k := by
        simpa [id,hji] using mj
      subst j
      have hk : w k ≠ col k := by
        intro eq
        exact (Finset.mem_filter.mp hw).2 _ he (by simp [cube,hi,eq])
      simpa [starPat,hki] using (bad_iff_not_bit _ _).mp hk
    · exact Or.inl ((mem_easy _ _ _).mpr hi)
  · rintro (he | hh)
    · exact easy_mem_graph col G i center w he
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro e he hw
      obtain ⟨k,hki,rfl⟩ := pair_at (size e he) (center e he)
      have km : k∈vertices G := Finset.mem_biUnion.mpr ⟨{i,k},he,by simp⟩
      have hk := (Finset.mem_filter.mp hh).2 k km
      have badk := (Finset.mem_filter.mp hw).2 k (by simp)
      simp [starPat,hki,badk] at hk

theorem star_graph_card {n : ℕ} (col : Word n) (G : Finset (Finset (Fin n))) (i : Fin n)
    (Gpos : G.Nonempty) (size : ∀ e∈G,e.card=2) (center : ∀ e∈G,i∈e) :
    (graphSol col G).card=2^(n-1)+2^(n-(vertices G).card) := by
  have iv : i∈vertices G := by
    obtain ⟨e,he⟩ := Gpos
    exact Finset.mem_biUnion.mpr ⟨e,he,center e he⟩
  have dis : Disjoint (easy i col) (cube (vertices G) (starPat i col)) := by
    apply Finset.disjoint_left.mpr
    intro w he hv
    have h := (Finset.mem_filter.mp hv).2 i iv
    exact (mem_easy _ _ _).mp he (by simpa [starPat] using h)
  rw [star_graph_set col G i size center,Finset.card_union_of_disjoint dis,easy_card,cube_card]

theorem gap_implies_high {n s N : ℕ} (hs : 1≤s)
    (hgap : (2:ℕ)^n*(2^(s-1)+1) ≤ 2^s*N) : 2^n < 2*N := by
  have eqs : 2*2^(s-1) = (2:ℕ)^s := by
    rw [Nat.mul_comm,←pow_succ,Nat.sub_add_cancel hs]
  by_contra nope
  have hlow : 2*N ≤ 2^n := by omega
  have hbase : (2:ℕ)^s*N ≤ 2^n*2^(s-1) := by
    rw [←eqs]
    calc
      2*2^(s-1)*N = (2*N)*2^(s-1) := by ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ hlow
  have hp : 0 < (2:ℕ)^n := Nat.pow_pos (by decide)
  rw [Nat.mul_add,Nat.mul_one] at hgap
  omega

theorem star_support_bound {n s : ℕ} (hs : 1≤s) (hsn : s≤n)
    (col : Word n) (G : Finset (Finset (Fin n))) (i : Fin n)
    (Gpos : G.Nonempty) (size : ∀ e∈G,e.card=2) (center : ∀ e∈G,i∈e)
    (gap : (2:ℕ)^n*(2^(s-1)+1) ≤ 2^s*(graphSol col G).card) :
    (vertices G).card ≤ s := by
  have eqn : 2*2^(n-1) = (2:ℕ)^n := by
    rw [Nat.mul_comm,←pow_succ,Nat.sub_add_cancel (hs.trans hsn)]
  have eqs : 2*2^(s-1) = (2:ℕ)^s := by
    rw [Nat.mul_comm,←pow_succ,Nat.sub_add_cancel hs]
  have eqbas : (2:ℕ)^n*2^(s-1) = 2^s*2^(n-1) := by
    rw [←eqn,←eqs]
    ac_rfl
  rw [star_graph_card col G i Gpos size center, Nat.mul_add, Nat.mul_one, Nat.mul_add, eqbas] at gap
  have tail : (2:ℕ)^n ≤ 2^s*2^(n-(vertices G).card) := by omega
  rw [pow_split n s hsn] at tail
  have hcomp := Nat.le_of_mul_le_mul_left tail (Nat.pow_pos (by decide))
  have cap := Finset.card_le_card (Finset.subset_univ (vertices G))
  rw [Finset.card_univ,Fintype.card_fin] at cap
  by_contra no
  have small := Nat.pow_lt_pow_right (a:=2) (by decide)
    (show n-(vertices G).card < n-s from by omega)
  omega


abbrev Gap (n s N : ℕ) : Prop := (2:ℕ)^n*(2^(s-1)+1) ≤ 2^s*N

theorem two_graph_card {n : ℕ} (b : Word n) {E F : Finset (Fin n)}
    (hE : E.card=2) (hF : F.card=2) (dis : Disjoint E F) :
    (graphSol b {E,F}).card = 9*2^(n-4) := by
  have sets : graphSol b {E,F} = Finset.univ \ (cube E b ∪ cube F b) := by
    ext w
    simp [graphSol,not_or]
  obtain ⟨_,hn⟩ := size_four hE hF dis
  rw [sets,Finset.card_sdiff_of_subset (Finset.subset_univ _),popcount,
    two_bad_mass b hE hF dis,pow_split n 4 hn]
  omega

theorem disjoint_gap_s {n s : ℕ} (hs : 3≤s) (b : Word n) {E F : Finset (Fin n)}
    (hE : E.card=2) (hF : F.card=2) (dis : Disjoint E F)
    (gap : Gap n s (graphSol b {E,F}).card) : 4≤s := by
  by_contra no
  have he : s=3 := by omega
  obtain ⟨_,hn⟩ := size_four hE hF dis
  have hp : 0 < (2:ℕ)^(n-4) := Nat.pow_pos (by decide)
  unfold Gap at gap
  rw [two_graph_card b hE hF dis,he,pow_split n 4 hn] at gap
  norm_num at gap
  omega

theorem sat_from_graph {n : ℕ} {A : Fml n} {b : Word n} {G : Finset (Finset (Fin n))}
    (eq : solutions A = graphSol b G) {w : Word n} (hg : w∈graphSol b G) :
    sat A w=true :=
  (Finset.mem_filter.mp (show w∈solutions A from eq.symm ▸ hg)).2

theorem graph_from_sat {n : ℕ} {A : Fml n} {b : Word n} {G : Finset (Finset (Fin n))}
    (eq : solutions A = graphSol b G) {w : Word n} (hg : sat A w=true) :
    w∈graphSol b G := eq ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hg⟩ : w∈solutions A)

theorem covered_pair {n s : ℕ} {pool : Finset (Word n)} {A : Fml n}
    (hc : covers (s:=s) pool) (z : Word n) (T : Finset (Fin n)) (ht : T.card≤s)
    (i j : Fin n) (hi : i∈T) (hj : j∈T) (ok : ∀ w∈cube T z, sat A w=true) :
    ∃ q : ↥pool, sat A q.val = true ∧ q.val i = z i ∧ q.val j = z j := by
  obtain ⟨w,wp,hw⟩ := hc T ht z
  exact ⟨⟨w,wp⟩,ok w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩),hw i hi,hw j hj⟩

theorem decoder_true_by_mass {n : ℕ} {pool : Finset (Word n)} (A : Fml n) (B : Finset (Word n))
    (sub : ∀ w∈B, hull (pool:=pool) (fun q=>sat A q.val) w)
    (big : 2^n < 2*B.card) : decode (pool:=pool) (fun q=>sat A q.val)=true := by
  classical
  unfold decode
  rw [decide_eq_true_eq]
  apply big.trans_le (Nat.mul_le_mul_left 2 (Finset.card_le_card ?_))
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sub w hw⟩

theorem empty_decode_true {n s : ℕ} {pool : Finset (Word n)} {A : Fml n} {b : Word n}
    (hs : 2≤s) (hc : covers (s:=s) pool) (eq : solutions A = graphSol b ∅) :
    decode (pool:=pool) (fun q=>sat A q.val) = true := by
  apply decoder_true_by_mass A Finset.univ
  · intro z _ i j
    exact covered_pair hc z {i,j} (by
      have h:=Finset.card_insert_le i ({j}:Finset (Fin n))
      rw [Finset.card_singleton] at h
      exact h.trans hs) i j (by simp) (by simp)
      (fun w _ => sat_from_graph eq (by simp [graphSol]))
  · rw [popcount]
    have h : 0 < (2:ℕ)^n := Nat.pow_pos (by decide)
    omega

theorem absent_bit {n : ℕ} {E : Finset (Fin n)} {b z : Word n} (h : z∉cube E b) :
    ∃ j∈E,z j ≠ b j := by
  classical
  by_contra no
  apply h
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro j hj
  by_contra not'
  exact no ⟨j,hj,not'⟩

theorem disjoint_decode_true {n s : ℕ} {pool : Finset (Word n)} {A : Fml n} {b : Word n}
    {E F : Finset (Fin n)} (hs : 4≤s) (hc : covers (s:=s) pool)
    (eq : solutions A = graphSol b {E,F})
    (hi : 2^n < 2*(graphSol b {E,F}).card) :
    decode (pool:=pool) (fun q=>sat A q.val)=true := by
  apply decoder_true_by_mass A (graphSol b {E,F}) _ hi
  intro z hz i j
  have hG := (Finset.mem_filter.mp hz).2
  obtain ⟨a,ha,hza⟩ := absent_bit (hG E (by simp))
  obtain ⟨c,hc',hzc⟩ := absent_bit (hG F (by simp))
  let T : Finset (Fin n) := {i,j,a,c}
  have hcard : T.card≤s := by
    have h1 := Finset.card_insert_le i ({j,a,c}:Finset (Fin n))
    have h2 := Finset.card_insert_le j ({a,c}:Finset (Fin n))
    have h3 := Finset.card_insert_le a ({c}:Finset (Fin n))
    rw [Finset.card_singleton] at h3
    change ({i,j,a,c}:Finset (Fin n)).card≤s
    omega
  apply covered_pair hc z T hcard i j (by simp [T]) (by simp [T])
  intro w hw
  have wx := (Finset.mem_filter.mp hw).2
  apply sat_from_graph eq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro H hH hbad
  simp only [Finset.mem_insert,Finset.mem_singleton] at hH
  rcases hH with rfl|rfl
  · exact hza ((wx a (by simp [T])).symm.trans ((Finset.mem_filter.mp hbad).2 a ha))
  · exact hzc ((wx c (by simp [T])).symm.trans ((Finset.mem_filter.mp hbad).2 c hc'))

theorem star_decode_true {n s : ℕ} {pool : Finset (Word n)} {A : Fml n} {b : Word n}
    {G : Finset (Finset (Fin n))} (hs : 3≤s) (hsn : s≤n) (hc : covers (s:=s) pool)
    (eq : solutions A = graphSol b G) (Gpos : G.Nonempty)
    (size : ∀ e∈G,e.card=2) (m : Fin n) (center : ∀ e∈G,m∈e)
    (gap : Gap n s (graphSol b G).card) :
    decode (pool:=pool) (fun q=>sat A q.val)=true := by
  have hsize := star_support_bound (by omega : 1≤s) hsn b G m Gpos size center gap
  have easyHull {z : Word n} (hz : z∈easy m b) :
      hull (pool:=pool) (fun q=>sat A q.val) z := by
    intro i j
    let T : Finset (Fin n) := {i,j,m}
    have hf : T.card≤s := by
      have h1 := Finset.card_insert_le i ({j,m}:Finset (Fin n))
      have h2 := Finset.card_insert_le j ({m}:Finset (Fin n))
      rw [Finset.card_singleton] at h2
      change ({i,j,m}:Finset (Fin n)).card≤s
      omega
    apply covered_pair hc z T hf i j (by simp [T]) (by simp [T])
    intro w hw
    apply sat_from_graph eq
    apply easy_mem_graph b G m center
    apply (mem_easy m b w).mpr
    rw [(Finset.mem_filter.mp hw).2 m (by simp [T])]
    exact (mem_easy m b z).mp hz
  obtain ⟨x,xp,xv⟩ := hc (vertices G) hsize (starPat m b)
  have xc : x∈cube (vertices G) (starPat m b) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,xv⟩
  have xs : sat A x=true := sat_from_graph eq (by
    rw [star_graph_set b G m size center]
    exact Finset.mem_union_right _ xc)
  have xh : hull (pool:=pool) (fun q=>sat A q.val) x := fun _ _=>⟨⟨x,xp⟩,xs,rfl,rfl⟩
  have mi : m∈vertices G := by
    obtain ⟨e,he⟩ := Gpos
    exact Finset.mem_biUnion.mpr ⟨e,he,center e he⟩
  have xno : x∉easy m b := by
    intro e
    exact (mem_easy _ _ _).mp e (by simpa [starPat] using xv m mi)
  apply decoder_true_by_mass A (insert x (easy m b))
  · intro w hw
    rw [Finset.mem_insert] at hw
    rcases hw with rfl|h
    · exact xh
    · exact easyHull h
  · rw [Finset.card_insert_of_notMem xno,easy_card,pow_split n 1 (by omega)]
    omega

theorem decode_gap {n s : ℕ} {pool : Finset (Word n)} (hs : 3≤s) (hsn : s≤n)
    (hcover : covers (s:=s) pool) (A : Fml n) (gap : Gap n s (count A)) :
    decode (pool:=pool) (fun q=>sat A q.val)=true := by
  classical
  have hi := gap_implies_high (show 1≤s from by omega) gap
  let b := polarity A
  let G := edges A
  have eq : solutions A = graphSol b G := normalize_graph (by omega) A hi
  have eqCard : count A = (graphSol b G).card := congrArg Finset.card eq
  have sizes : ∀ e∈G, e.card=2 := graph_arity A
  rw [eqCard] at hi gap
  rcases G.eq_empty_or_nonempty with no | Gpos
  · rw [no] at eq
    exact empty_decode_true (by omega : 2≤s) hcover eq
  by_cases one : ∀ e∈G, ∀ f∈G, ¬Disjoint e f
  · rcases edges_intersect_star_or_triangle G Gpos sizes one with ⟨m,hm⟩ | ⟨i,j,k,_,_,_,e,f,g⟩
    · exact star_decode_true hs hsn hcover eq Gpos sizes m hm gap
    · exact False.elim ((Nat.not_lt_of_ge (triangle_at_most_half b G i j k e f g)) hi)
  push_neg at one
  obtain ⟨e,he,f,hf,hdis⟩ := one
  have res := only_two_when_disjoint b G sizes hi e f he hf hdis
  rw [res] at hi eq gap
  exact disjoint_decode_true (disjoint_gap_s hs b (sizes e he) (sizes f hf) hdis gap) hcover eq hi


def Target : Prop :=
  ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let count := fun (G : F) => (Finset.univ.filter (fun u => sat G u = true)).card
  let Q := 2 ^ n
  ∀ pool : Finset W,
    let correct := fun (classify : (↥pool → Bool) → Bool) => ∀ A : F,
      let value := classify (fun q => sat A q.val)
      (2 * count A ≤ Q → value = false) ∧
      (Q * (2 ^ (s - 1) + 1) ≤ 2 ^ s * count A → value = true)
    let covers := ∀ S : Finset (Fin n), S.card ≤ s → ∀ pat : W,
      ∃ x ∈ pool, ∀ bit ∈ S, x bit = pat bit
    let decoder := fun (label : ↥pool → Bool) =>
      let hull := fun z : W => ∀ i j : Fin n, ∃ v : ↥pool,
        label v = true ∧ v.val i = z i ∧ v.val j = z j
      decide (Q < 2 * (Finset.univ.filter hull).card)
    ((∃ classify, correct classify) ↔ covers) ∧ (covers → correct decoder)


theorem decoder_correct {n s : ℕ} {pool : Finset (Word n)} (hs : 3≤s) (hsn : s≤n)
    (hc : covers (s:=s) pool) : correct (s:=s) (pool:=pool) decode := by
  intro A
  exact ⟨decode_false A, decode_gap hs hsn hc A⟩

theorem decode_agrees {n : ℕ} {pool : Finset (Word n)} (label : ↥pool → Bool)
    (d : DecidablePred (hull label)) :
    decode label =
      decide (2^n < 2*((@Finset.filter (Word n) (hull label) d Finset.univ)).card) := by
  classical
  unfold decode
  have h :
      @Finset.filter (Word n) (hull label) (fun z => Classical.propDecidable (hull label z)) Finset.univ =
      @Finset.filter (Word n) (hull label) d Finset.univ := by
    ext w
    simp only [Finset.mem_filter]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [h]

theorem solveTarget : Target := by
  unfold Target
  intro n s hs hsn
  dsimp only
  intro pool
  refine ⟨?_,?_⟩
  · constructor
    · exact classifier_implies_covers (by omega : 1≤s) hsn
    · intro hc
      exact ⟨decode, decoder_correct hs hsn hc⟩
  · intro hc A
    have good := decoder_correct (pool:=pool) hs hsn hc A
    let label : ↥pool → Bool := fun q => sat A q.val
    let d : DecidablePred (hull label) := fun z =>
      inferInstanceAs (Decidable (∀ i j : Fin n, ∃ v : ↥pool,
        label v = true ∧ v.val i = z i ∧ v.val j = z j))
    have he := decode_agrees label d
    constructor
    · intro low
      exact he.symm.trans (good.1 low)
    · intro high
      exact he.symm.trans (good.2 high)

end PEqualNP.Outside.L_lib_511_aux

theorem PEqualNP.Outside.L_lib_511 :
  ∀ (n s : ℕ), 3 ≤ s → s ≤ n →
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let count := fun (G : F) => (Finset.univ.filter (fun u => sat G u = true)).card
  let Q := 2 ^ n
  ∀ pool : Finset W,
    let correct := fun (classify : (↥pool → Bool) → Bool) => ∀ A : F,
      let value := classify (fun q => sat A q.val)
      (2 * count A ≤ Q → value = false) ∧
      (Q * (2 ^ (s - 1) + 1) ≤ 2 ^ s * count A → value = true)
    let covers := ∀ S : Finset (Fin n), S.card ≤ s → ∀ pat : W,
      ∃ x ∈ pool, ∀ bit ∈ S, x bit = pat bit
    let decoder := fun (label : ↥pool → Bool) =>
      let hull := fun z : W => ∀ i j : Fin n, ∃ v : ↥pool,
        label v = true ∧ v.val i = z i ∧ v.val j = z j
      decide (Q < 2 * (Finset.univ.filter hull).card)
    ((∃ classify, correct classify) ↔ covers) ∧ (covers → correct decoder) := PEqualNP.Outside.L_lib_511_aux.solveTarget

