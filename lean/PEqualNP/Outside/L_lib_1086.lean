import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1086_aux

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Clause (n : ℕ) := (Fin n × Bool) × (Fin n × Bool)

def Sat {n : ℕ} (A : Finset (Clause n)) (x : Word n) : Prop :=
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2

def Free {n : ℕ} (B S : Finset (Word n)) : Prop :=
  Disjoint B S ∧ ∀ D : Finset (Word n), D ⊆ S → ∃ A : Finset (Clause n),
    ∀ x : Word n, Sat A x ↔ x ∈ B ∨ x ∈ D

def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

def middle {n : ℕ} (a b c : Word n) : Word n := fun i => maj (a i) (b i) (c i)

theorem maj_clause : ∀ a b c d e f p q : Bool,
    (a ≠ p ∨ d ≠ q) → (b ≠ p ∨ e ≠ q) → (c ≠ p ∨ f ≠ q) →
    maj a b c ≠ p ∨ maj d e f ≠ q := by decide

theorem sat_closed {n : ℕ} {A : Finset (Clause n)} {a b c : Word n}
    (ha : Sat A a) (hb : Sat A b) (hc : Sat A c) : Sat A (middle a b c) := by
  intro k hk
  exact maj_clause _ _ _ _ _ _ _ _ (ha k hk) (hb k hk) (hc k hk)

def Closed {α : Type*} (op : α → α → α → α) (X : Finset α) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, op a b c ∈ X

theorem freely_closed {n : ℕ} {B S D : Finset (Word n)}
    (h : Free B S) (hD : D ⊆ S) : Closed middle (B ∪ D) := by
  obtain ⟨A,ha⟩ := h.2 D hD
  intro a h₁ b h₂ c h₃
  apply Finset.mem_union.mpr
  exact (ha _).mp (sat_closed ((ha a).mpr (Finset.mem_union.mp h₁))
    ((ha b).mpr (Finset.mem_union.mp h₂)) ((ha c).mpr (Finset.mem_union.mp h₃)))

theorem sat_of_separation {n : ℕ} (X : Finset (Word n))
    (sep : ∀ x : Word n, x ∉ X → ∃ i j : Fin n,
      ∀ y ∈ X, y i ≠ x i ∨ y j ≠ x j) :
    ∃ A : Finset (Clause n), ∀ x, Sat A x ↔ x ∈ X := by
  classical
  let A := (Finset.univ : Finset (Clause n)).filter
    (fun c => ∀ y ∈ X, y c.1.1 ≠ c.1.2 ∨ y c.2.1 ≠ c.2.2)
  refine ⟨A, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    by_contra hn
    obtain ⟨i,j,hij⟩ := sep x hn
    have hc : ((i,x i),(j,x j)) ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
    simpa using hx _ hc
  · intro hx c hc
    exact (Finset.mem_filter.mp hc).2 x hx

def word {n : ℕ} (s : Finset (Fin n)) : Word n := fun i => decide (i ∈ s)

theorem word_inj {n : ℕ} : Function.Injective (@word n) := by
  intro a b h
  ext i
  simpa [word] using congrFun h i

def supp {n : ℕ} (x : Word n) : Finset (Fin n) := Finset.univ.filter (fun i => x i = true)

@[simp] theorem mem_supp {n : ℕ} {x : Word n} {i : Fin n} : i ∈ supp x ↔ x i = true := by
  simp [supp]

@[simp] theorem word_supp {n : ℕ} (x : Word n) : word (supp x) = x := by
  funext i
  simp [word]

@[simp] theorem supp_word {n : ℕ} (s : Finset (Fin n)) : supp (word s) = s := by
  ext i
  simp [word]

def orient {n : ℕ} (r x : Word n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ r i)

@[simp] theorem mem_orient {n : ℕ} {r x : Word n} {i : Fin n} : i ∈ orient r x ↔ x i ≠ r i := by
  simp [orient]

@[simp] theorem orient_self {n : ℕ} (r : Word n) : orient r r = ∅ := by simp [orient]

theorem orient_inj {n : ℕ} (r : Word n) : Function.Injective (orient r) := by
  intro x y h
  funext i
  have t : (x i ≠ r i) ↔ (y i ≠ r i) := by
    simpa only [mem_orient] using (Finset.ext_iff.mp h i)
  cases h₁ : x i <;> cases h₂ : y i <;> cases h₃ : r i <;> simp_all

def med {α : Type*} [DecidableEq α] (a b c : Finset α) : Finset α :=
  (a ∩ b) ∪ (a ∩ c) ∪ (b ∩ c)

theorem orient_middle {n : ℕ} (r a b c : Word n) :
    orient r (middle a b c) = med (orient r a) (orient r b) (orient r c) := by
  ext i
  simp only [med, Finset.mem_union, Finset.mem_inter, mem_orient, middle]
  cases a i <;> cases b i <;> cases c i <;> cases r i <;> decide

theorem oriented_closed {n : ℕ} (r : Word n) {X : Finset (Word n)} (h : Closed middle X) :
    Closed med (X.image (orient r)) := by
  intro a ha b hb c hc
  obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
  rw [← orient_middle]
  exact Finset.mem_image_of_mem _ (h _ ha' _ hb' _ hc')

end PEqualNP.Outside.L_lib_1086_aux

namespace PEqualNP.Outside.L_lib_1086_aux

variable {α : Type*} [DecidableEq α]
abbrev Fam (α : Type*) := Finset (Finset α)

def Cov (X : Fam α) (a x : Finset α) : Prop :=
  a ∈ X ∧ a ⊂ x ∧ ∀ u ∈ X, a ⊆ u → u ⊂ x → u = a

def Principal (X : Fam α) (x : Finset α) : Prop :=
  ∃ i ∈ x, ∀ a ∈ X, a ⊂ x → i ∉ a

def Extreme (X : Fam α) (s : Finset α) : Prop :=
  ∀ a ∈ X, ∀ b ∈ X, ∀ c ∈ X, a ≠ s → b ≠ s → c ≠ s → med a b c ≠ s

theorem med_root (a b : Finset α) : med a b ∅ = a ∩ b := by simp [med]

theorem med_under {a b x : Finset α} (ha : a ⊆ x) (hb : b ⊆ x) :
    med a b x = a ∪ b := by
  ext i
  simp only [med, Finset.mem_union, Finset.mem_inter]
  constructor
  · tauto
  · rintro (h|h)
    · exact Or.inl (Or.inr ⟨h,ha h⟩)
    · exact Or.inr ⟨h,hb h⟩

theorem extends_to_cov {X : Fam α} {a x : Finset α} (ha : a ∈ X) (hle : a ⊂ x) :
    ∃ u, Cov X u x ∧ a ⊆ u := by
  classical
  let C := X.filter (fun p => a ⊆ p ∧ p ⊂ x)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨ha, Finset.Subset.rfl, hle⟩
  obtain ⟨u,hu,hmax⟩ := Finset.exists_max_image C Finset.card ⟨a,haC⟩
  obtain ⟨huX,hau,hux⟩ := Finset.mem_filter.mp hu
  refine ⟨u,⟨huX,hux,?_⟩,hau⟩
  intro v hv huv hvx
  have hvC : v ∈ C := Finset.mem_filter.mpr ⟨hv, hau.trans huv, hvx⟩
  exact (Finset.eq_of_subset_of_card_le huv (hmax v hvC)).symm

theorem two_covers {X : Fam α} (root : ∅ ∈ X) {x : Finset α} (hx : x ≠ ∅)
    (hp : ¬ Principal X x) : ∃ a b, Cov X a x ∧ Cov X b x ∧ a ≠ b := by
  classical
  have he : ∅ ⊂ x := Finset.empty_ssubset.mpr (Finset.nonempty_iff_ne_empty.mpr hx)
  obtain ⟨a,ha,_⟩ := extends_to_cov root he
  obtain ⟨i,hix,hia⟩ : ∃ i ∈ x, i ∉ a := by
    by_contra! hn
    exact ha.2.1.not_ge hn
  have hi : ∃ t ∈ X, t ⊂ x ∧ i ∈ t := by
    by_contra! hn
    exact hp ⟨i,hix,fun t ht htx hit => hn t ht htx hit⟩
  obtain ⟨t,ht,htx,hit⟩ := hi
  obtain ⟨b,hb,htb⟩ := extends_to_cov ht htx
  exact ⟨a,b,ha,hb,fun hab => hia (hab ▸ htb hit)⟩

theorem cover_union {X : Fam α} (closed : Closed med X) {x a b : Finset α}
    (hx : x ∈ X) (ha : Cov X a x) (hb : Cov X b x) (hne : a ≠ b) : a ∪ b = x := by
  classical
  have au : a ⊆ a ∪ b := Finset.subset_union_left
  have bu : b ⊆ a ∪ b := Finset.subset_union_right
  have ux : a ∪ b ⊆ x := Finset.union_subset ha.2.1.le hb.2.1.le
  have huX := closed _ ha.1 _ hb.1 _ hx
  rw [med_under ha.2.1.le hb.2.1.le] at huX
  by_contra hn
  have strict : a ∪ b ⊂ x := lt_of_le_of_ne ux hn
  exact hne ((ha.2.2 _ huX au strict).symm.trans (hb.2.2 _ huX bu strict))

theorem maximal_of_two {X : Fam α} (closed : Closed med X) {x a b : Finset α}
    (hx : x ∈ X) (he : Extreme X x) (ha : Cov X a x) (hb : Cov X b x) (hne : a ≠ b) :
    ∀ z ∈ X, x ⊆ z → z = x := by
  intro z hz hle
  by_contra hzx
  apply he a ha.1 b hb.1 z hz ha.2.1.ne hb.2.1.ne hzx
  rw [med_under (ha.2.1.le.trans hle) (hb.2.1.le.trans hle), cover_union closed hx ha hb hne]

theorem at_most_two {X : Fam α} (closed : Closed med X) {x a b c : Finset α}
    (hx : x ∈ X) (he : Extreme X x) (ha : Cov X a x) (hb : Cov X b x) (hc : Cov X c x)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : False := by
  have pab := cover_union closed hx ha hb hab
  have pac := cover_union closed hx ha hc hac
  have pbc := cover_union closed hx hb hc hbc
  apply he a ha.1 b hb.1 c hc.1 ha.2.1.ne hb.2.1.ne hc.2.1.ne
  ext i
  have hab' := Finset.ext_iff.mp pab i
  have hac' := Finset.ext_iff.mp pac i
  have hbc' := Finset.ext_iff.mp pbc i
  simp only [med, Finset.mem_union, Finset.mem_inter] at *
  tauto

theorem cover_nonempty {X : Fam α} {x a b : Finset α} (ha : Cov X a x) (hb : Cov X b x)
    (hne : a ≠ b) : a ≠ ∅ := by
  intro h
  subst a
  exact hne (ha.2.2 b hb.1 (Finset.empty_subset _) hb.2.1).symm

theorem single_upper {X : Fam α} (closed : Closed med X) (root : ∅ ∈ X) {p a b : Finset α}
    (hp : p ≠ ∅) (he : Extreme X p) (ha : Cov X p a) (hb : Cov X p b)
    (haX : a ∈ X) (hbX : b ∈ X) : a = b := by
  classical
  have hpab : p ⊆ a ∩ b := Finset.subset_inter ha.2.1.le hb.2.1.le
  have hX : a ∩ b ∈ X := by simpa only [med_root] using closed a haX b hbX ∅ root
  by_contra hne
  have h₁ : a ∩ b ≠ a := by
    intro h
    have hab : a ⊆ b := h ▸ Finset.inter_subset_right
    exact ha.2.1.ne (hb.2.2 a haX ha.2.1.le (lt_of_le_of_ne hab hne)).symm
  have h₀ := ha.2.2 (a ∩ b) hX hpab (lt_of_le_of_ne Finset.inter_subset_left h₁)
  exact he a haX b hbX ∅ root ha.2.1.ne' hb.2.1.ne' hp.symm ((med_root a b).trans h₀)

theorem same_private_coordinate {X : Fam α} (closed : Closed med X) (root : ∅ ∈ X)
    {a b : Finset α} {i : α} (ha : a ∈ X) (hb : b ∈ X) (hia : i ∈ a) (hib : i ∈ b)
    (pa : ∀ x ∈ X, x ⊂ a → i ∉ x) (pb : ∀ x ∈ X, x ⊂ b → i ∉ x) : a = b := by
  have hm : a ∩ b ∈ X := by simpa only [med_root] using closed a ha b hb ∅ root
  have hi : i ∈ a ∩ b := Finset.mem_inter.mpr ⟨hia,hib⟩
  have ea : a ∩ b = a := by
    by_contra hn
    exact pa _ hm (lt_of_le_of_ne Finset.inter_subset_left hn) hi
  have eb : a ∩ b = b := by
    by_contra hn
    exact pb _ hm (lt_of_le_of_ne Finset.inter_subset_right hn) hi
  exact ea.symm.trans eb

end PEqualNP.Outside.L_lib_1086_aux

namespace PEqualNP.Outside.L_lib_1086_aux

open Classical

variable {α : Type*} [DecidableEq α]

def pairGraph (X S B : Fam α) : SimpleGraph B where
  Adj a b := a.val ≠ b.val ∧ ∃ x ∈ S, Cov X a.val x ∧ Cov X b.val x
  symm := ⟨fun a b h => by
    obtain ⟨hne,x,hx,ha,hb⟩ := h
    exact ⟨hne.symm,x,hx,hb,ha⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem median_pairs (a b c : Finset α) : med (a ∪ b) (a ∪ c) (b ∪ c) = a ∪ b ∪ c := by
  ext i
  simp only [med, Finset.mem_union, Finset.mem_inter]
  tauto

theorem pairGraph_triangleFree {X S B : Fam α} (hs : S ⊆ X) (closed : Closed med X)
    (xt : ∀ x ∈ S, Extreme X x) : (pairGraph X S B).CliqueFree 3 := by
  classical
  intro f hf
  have large : 2 < f.card := by rw [hf.card_eq]; decide
  obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp large
  obtain ⟨dab,x,hx,ax,bx⟩ := hf.isClique ha hb ab
  obtain ⟨dac,y,hy,ay,cy⟩ := hf.isClique ha hc ac
  obtain ⟨dbc,z,hz,bz,cz⟩ := hf.isClique hb hc bc
  have Xeq := cover_union closed (hs hx) ax bx dab
  have Yeq := cover_union closed (hs hy) ay cy dac
  have Zeq := cover_union closed (hs hz) bz cz dbc
  have hm := closed x (hs hx) y (hs hy) z (hs hz)
  rw [← Xeq, ← Yeq, ← Zeq, median_pairs] at hm
  have x_le : x ⊆ a.val ∪ b.val ∪ c.val := by rw [← Xeq]; exact Finset.subset_union_left
  have y_le : y ⊆ a.val ∪ b.val ∪ c.val := by
    rw [← Yeq]; exact Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right
  have hmx := maximal_of_two closed (hs hx) (xt x hx) ax bx dab _ hm x_le
  have hmy := maximal_of_two closed (hs hy) (xt y hy) ay cy dac _ hm y_le
  have hxy : y = x := hmy.symm.trans hmx
  rw [hxy] at cy
  exact at_most_two closed (hs hx) (xt x hx) ax bx cy dab dac dbc

theorem principal_card [Fintype α] {X : Fam α} (root : ∅ ∈ X) (closed : Closed med X) :
    (X.filter (Principal X)).card ≤ Fintype.card α := by
  classical
  let P := X.filter (Principal X)
  have hh (x : P) : ∃ i ∈ x.val, ∀ a ∈ X, a ⊂ x.val → i ∉ a := (Finset.mem_filter.mp x.prop).2
  let key (x : P) : α := Classical.choose (hh x)
  have spec (x : P) := Classical.choose_spec (hh x)
  have inj : Function.Injective key := by
    intro a b eq
    apply Subtype.ext
    apply same_private_coordinate closed root (Finset.mem_filter.mp a.prop).1 (Finset.mem_filter.mp b.prop).1
      (spec a).1 _ (spec a).2
    · intro x hx hlt
      change key a ∉ x
      rw [eq]
      exact (spec b).2 x hx hlt
    · change key a ∈ b.val
      rw [eq]
      exact (spec b).1
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective key inj

def BothFixed (X B : Fam α) (x : Finset α) : Prop :=
  ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ Cov X a x ∧ Cov X b x

theorem fixed_card {X S B : Fam α} (hs : S ⊆ X) (closed : Closed med X)
    (xt : ∀ x ∈ S, Extreme X x) :
    (S.filter (BothFixed X B)).card ≤ B.card * B.card / 4 := by
  classical
  let V := S.filter (BothFixed X B)
  let G := pairGraph X S B
  have choice (s : V) : ∃ a b : B, G.Adj a b ∧ a.val ∪ b.val = s.val := by
    obtain ⟨hx,a,ha,b,hb,hab,ac,bc⟩ := Finset.mem_filter.mp s.prop
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,⟨hab,s.val,hx,ac,bc⟩,cover_union closed (hs hx) ac bc hab⟩
  choose a b adj unions using choice
  let edge (s : V) : G.edgeFinset :=
    ⟨s(a s, b s), SimpleGraph.mem_edgeFinset.mpr (show G.Adj (a s) (b s) from adj s)⟩
  have inj : Function.Injective edge := by
    intro x y eq
    have heq : s(a x,b x) = s(a y,b y) := congrArg Subtype.val eq
    apply Subtype.ext
    rw [← unions x, ← unions y]
    rcases Sym2.eq_iff.mp heq with hw | hw
    · rw [hw.1,hw.2]
    · rw [hw.1,hw.2,Finset.union_comm]
  have one := Finset.card_le_card_of_injective inj
  have cf : G.CliqueFree (2+1) := pairGraph_triangleFree hs closed xt
  have two := cf.card_edgeFinset_le
  rw [SimpleGraph.turanNumber_two, Fintype.card_coe, pow_two] at two
  exact one.trans two

def HasSwitchPred (X S : Fam α) (x : Finset α) : Prop :=
  ∃ p ∈ S, p ≠ ∅ ∧ Principal X p ∧ Cov X p x

theorem switchPred_card {X S : Fam α} (hs : S ⊆ X) (root : ∅ ∈ X) (closed : Closed med X)
    (xt : ∀ x ∈ S, Extreme X x) :
    (S.filter (HasSwitchPred X S)).card ≤ (X.filter (Principal X)).card := by
  classical
  let P := X.filter (Principal X)
  let T := S.filter (HasSwitchPred X S)
  have next (x : T) : ∃ p : P, p.val ∈ S ∧ p.val ≠ ∅ ∧ Cov X p.val x.val := by
    obtain ⟨_,p,hp,ne,pri,cov⟩ := Finset.mem_filter.mp x.prop
    exact ⟨⟨p,Finset.mem_filter.mpr ⟨hs hp,pri⟩⟩,hp,ne,cov⟩
  choose f spec using next
  apply Finset.card_le_card_of_injective (f := f)
  intro a b eq
  apply Subtype.ext
  have hb := (spec b).2.2
  rw [← eq] at hb
  exact single_upper closed root (spec a).2.1 (xt _ (spec a).1) (spec a).2.2 hb
    (hs (Finset.mem_filter.mp a.prop).1) (hs (Finset.mem_filter.mp b.prop).1)

theorem anchored_upper [Fintype α] {B S : Fam α} (root : ∅ ∈ B ∪ S)
    (closed : Closed med (B ∪ S)) (xt : ∀ x ∈ S, Extreme (B ∪ S) x) :
    S.card ≤ 2 * Fintype.card α + 1 + B.card * B.card / 4 := by
  classical
  let X := B ∪ S
  let P := X.filter (Principal X)
  let T := S.filter (HasSwitchPred X S)
  let G := S.filter (BothFixed X B)
  have hs : S ⊆ X := Finset.subset_union_right
  have cover : S ⊆ insert ∅ ((P ∪ T) ∪ G) := by
    intro x hx
    by_cases empty : x = ∅
    · exact Finset.mem_insert.mpr (Or.inl empty)
    apply Finset.mem_insert_of_mem
    by_cases pri : Principal X x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs hx,pri⟩))
    obtain ⟨a,b,ha,hb,hab⟩ := two_covers root empty pri
    have side {a b : Finset α} (aS : a ∈ S) (ca : Cov X a x) (cb : Cov X b x) (ab : a ≠ b) :
        x ∈ T := by
      have ane := cover_nonempty ca cb ab
      have ap : Principal X a := by
        by_contra hn
        obtain ⟨c,d,hc,hd,hcd⟩ := two_covers root ane hn
        exact ca.2.1.ne' (maximal_of_two closed (hs aS) (xt a aS) hc hd hcd x (hs hx) ca.2.1.le)
      exact Finset.mem_filter.mpr ⟨hx,a,aS,ane,ap,ca⟩
    by_cases aS : a ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (side aS ha hb hab))
    by_cases bS : b ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (side bS hb ha hab.symm))
    have aB : a ∈ B := (Finset.mem_union.mp ha.1).resolve_right aS
    have bB : b ∈ B := (Finset.mem_union.mp hb.1).resolve_right bS
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,a,aB,b,bB,hab,ha,hb⟩)
  have pcard : P.card ≤ Fintype.card α := principal_card root closed
  have tcard : T.card ≤ P.card := switchPred_card hs root closed xt
  have gcard : G.card ≤ B.card*B.card/4 := fixed_card hs closed xt
  have ub := Finset.card_le_card cover
  have i := Finset.card_insert_le (∅ : Finset α) ((P ∪ T) ∪ G)
  have u := Finset.card_union_le (P ∪ T) G
  have v := Finset.card_union_le P T
  omega

end PEqualNP.Outside.L_lib_1086_aux

namespace PEqualNP.Outside.L_lib_1086_aux

theorem extreme_image {n : ℕ} {B S : Finset (Word n)} (h : Free B S)
    (r x : Word n) (hx : x ∈ S) : Extreme ((B ∪ S).image (orient r)) (orient r x) := by
  classical
  intro a ha b hb c hc ax bx cx eq
  obtain ⟨a',ha',rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b',hb',rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
  have keep (y : Word n) (hy : y ∈ B ∪ S) (hne : orient r y ≠ orient r x) : y ∈ B ∪ S.erase x := by
    rcases Finset.mem_union.mp hy with hB|hS
    · exact Finset.mem_union_left _ hB
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun e => hne (e ▸ rfl), hS⟩)
  have closed := freely_closed h (Finset.erase_subset x S)
  have prod := closed _ (keep _ ha' ax) _ (keep _ hb' bx) _ (keep _ hc' cx)
  rw [← orient_middle] at eq
  rw [orient_inj r eq] at prod
  rcases Finset.mem_union.mp prod with hB|he
  · exact Finset.disjoint_left.mp h.1 hB hx
  · exact (Finset.mem_erase.mp he).1 rfl

theorem upper {n : ℕ} (B S : Finset (Word n)) (h : Free B S) :
    S.card ≤ 2*n+1+B.card*B.card/4 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨r,hr⟩ := hs
    let T := B.image (orient r)
    let U := S.image (orient r)
    have hu : r ∈ B ∪ S := Finset.mem_union_right _ hr
    have img : T ∪ U = (B ∪ S).image (orient r) := by rw [Finset.image_union]
    have root : ∅ ∈ T ∪ U := by
      rw [img, ← orient_self r]
      exact Finset.mem_image_of_mem _ hu
    have clo : Closed med (T ∪ U) := by
      rw [img]
      exact oriented_closed r (freely_closed h (Finset.Subset.rfl (s := S)))
    have xt : ∀ x ∈ U, Extreme (T ∪ U) x := by
      intro x hx
      obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
      rw [img]
      exact extreme_image h r x' hx'
    have bound := anchored_upper root clo xt
    simpa only [T,U,Finset.card_image_of_injective _ (orient_inj r),Fintype.card_fin] using bound
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

end PEqualNP.Outside.L_lib_1086_aux

namespace PEqualNP.Outside.L_lib_1086_aux

abbrev Points (n : ℕ) := Finset (Finset (Fin n))

def singles {α : Type*} [DecidableEq α] (A : Finset α) : Finset (Finset α) :=
  A.image (fun i => {i})

def pairs {α : Type*} [DecidableEq α] (A B : Finset α) : Finset (Finset α) :=
  (A ×ˢ B).image (fun p => {p.1, p.2})

theorem mem_singles {α : Type*} [DecidableEq α] {A : Finset α} {s : Finset α} :
    s ∈ singles A ↔ ∃ i ∈ A, s = {i} := by
  simp only [singles, Finset.mem_image]
  grind

theorem mem_pairs {α : Type*} [DecidableEq α] {A B : Finset α} {s : Finset α} :
    s ∈ pairs A B ↔ ∃ i ∈ A, ∃ j ∈ B, s = {i,j} := by
  simp only [pairs, Finset.mem_image, Finset.mem_product, Prod.exists]
  grind

def baseSet {α : Type*} [DecidableEq α] (L R : Finset α) : Finset (Finset α) :=
  insert ∅ (singles (L ∪ R))

def switchSet {α : Type*} [DecidableEq α] (L R E : Finset α) (p : α) : Finset (Finset α) :=
  (singles E ∪ pairs L R) ∪ pairs E {p}

def Thin {α : Type*} (color : α → Bool) (s : Finset α) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, color i = color j → i = j

theorem thin_pair {α : Type*} [DecidableEq α] {col : α → Bool} {i j : α} (h : col i ≠ col j) :
    Thin col {i,j} := by
  intro u hu v hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> grind

theorem thin_determines_pair {α : Type*} [DecidableEq α] {col : α → Bool} {s : Finset α}
    (h : Thin col s) {i j : α} (hi : i ∈ s) (hj : j ∈ s) (ne : i ≠ j) : s = {i,j} := by
  have neq : col i ≠ col j := fun eq => ne (h i hi j hj eq)
  ext k
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hk
    have w : col k = col i ∨ col k = col j := by
      cases h₁ : col k <;> cases h₂ : col i <;> cases h₃ : col j <;> simp_all
    exact w.imp (h k hk i hi) (h k hk j hj)
  · rintro (rfl|rfl) <;> assumption

theorem base_or_switch {α : Type*} [DecidableEq α] {L R E : Finset α} {p : α} {s : Finset α}
    (h : s ∈ baseSet L R ∪ switchSet L R E p) :
    s = ∅ ∨ (∃ i ∈ L ∪ R, s = {i}) ∨ (∃ i ∈ E, s = {i}) ∨
       (∃ i ∈ L, ∃ j ∈ R, s = {i,j}) ∨ (∃ i ∈ E, s = {i,p}) := by
  simp only [baseSet, switchSet, Finset.mem_union, Finset.mem_insert, mem_singles, mem_pairs,
    Finset.mem_singleton, exists_eq_left] at h
  simp only [Finset.mem_union]
  rcases h with (a|b)|((c|d)|e)
  · exact Or.inl a
  · exact Or.inr (Or.inl b)
  · exact Or.inr (Or.inr (Or.inl c))
  · exact Or.inr (Or.inr (Or.inr (Or.inl d)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr e)))

theorem shape_thin {α : Type*} [DecidableEq α] {L R E : Finset α} {p : α}
    (lr : Disjoint L R) (er : Disjoint E R) (hp : p ∈ R) {s : Finset α}
    (h : s ∈ baseSet L R ∪ switchSet L R E p) : Thin (fun i => decide (i ∈ R)) s := by
  rcases base_or_switch h with rfl|⟨i,_,rfl⟩|⟨i,_,rfl⟩|⟨i,hi,j,hj,rfl⟩|⟨i,hi,rfl⟩
  · simp [Thin]
  · simp [Thin]
  · simp [Thin]
  · exact thin_pair (by simp [hj,Finset.disjoint_left.mp lr hi])
  · exact thin_pair (by simp [hp,Finset.disjoint_left.mp er hi])

theorem shape_at_extra {α : Type*} [DecidableEq α] {L R E : Finset α} {p i : α}
    (hi : i ∉ L ∪ R) {s : Finset α}
    (h : s ∈ baseSet L R ∪ switchSet L R E p) (his : i ∈ s) (hps : p ∉ s) : s = {i} := by
  rcases base_or_switch h with rfl|⟨j,hj,rfl⟩|⟨j,_,rfl⟩|⟨a,ha,b,hb,rfl⟩|⟨a,_,rfl⟩
  · simp at his
  · rw [Finset.mem_singleton.mp his]
  · rw [Finset.mem_singleton.mp his]
  · simp only [Finset.mem_insert, Finset.mem_singleton] at his
    rcases his with rfl|rfl
    · exact False.elim (hi (Finset.mem_union_left _ ha))
    · exact False.elim (hi (Finset.mem_union_right _ hb))
  · simp at hps

def PairApprox {α : Type*} (Z : Finset (Finset α)) (t : Finset α) : Prop :=
  ∀ i j : α, ∃ s ∈ Z, (i ∈ s ↔ i ∈ t) ∧ (j ∈ s ↔ j ∈ t)

theorem recovered {α : Type*} [DecidableEq α] {L R E : Finset α} {p : α}
    (lr : Disjoint L R) (ex : Disjoint E (L ∪ R)) (hp : p ∈ R)
    {D : Finset (Finset α)} (hD : D ⊆ switchSet L R E p) {t : Finset α}
    (approx : PairApprox (baseSet L R ∪ D) t) : t ∈ baseSet L R ∪ D := by
  classical
  let col (i : α) : Bool := decide (i ∈ R)
  have er : Disjoint E R := ex.mono_right Finset.subset_union_right
  have incl : baseSet L R ∪ D ⊆ baseSet L R ∪ switchSet L R E p := Finset.union_subset_union Finset.Subset.rfl hD
  have inThin (s) (hs : s ∈ baseSet L R ∪ D) : Thin col s := shape_thin lr er hp (incl hs)
  have ht : Thin col t := by
    intro i hi j hj
    obtain ⟨s,hs,a,b⟩ := approx i j
    exact inThin s hs i (a.mpr hi) j (b.mpr hj)
  by_cases two : ∃ i ∈ t, ∃ j ∈ t, i ≠ j
  · obtain ⟨i,hi,j,hj,hij⟩ := two
    obtain ⟨s,hs,a,b⟩ := approx i j
    have ts := thin_determines_pair ht hi hj hij
    have ss := thin_determines_pair (inThin s hs) (a.mpr hi) (b.mpr hj) hij
    exact (ts.trans ss.symm) ▸ hs
  · by_cases empty : t = ∅
    · subst t
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have singleton : t = {i} := by
      ext j
      simp only [Finset.mem_singleton]
      exact ⟨fun hj => by_contra fun neq => two ⟨j,hj,i,hi,neq⟩, fun eq => eq ▸ hi⟩
    by_cases active : i ∈ L ∪ R
    · rw [singleton]
      exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (mem_singles.mpr ⟨i,active,rfl⟩))
    have ip : i ≠ p := fun eq => active (eq ▸ Finset.mem_union_right _ hp)
    obtain ⟨s,hs,a,b⟩ := approx i p
    have hpt : p ∉ t := by simp [singleton,Ne.symm ip]
    have ss := shape_at_extra active (incl hs) (a.mpr hi) (fun w => hpt (b.mp w))
    exact (singleton.trans ss.symm) ▸ hs

end PEqualNP.Outside.L_lib_1086_aux

namespace PEqualNP.Outside.L_lib_1086_aux

variable {α : Type*} [DecidableEq α]

theorem singles_card (A : Finset α) : (singles A).card = A.card := by
  apply Finset.card_image_of_injective
  intro i j h
  simpa using h

theorem pair_size {A B : Finset α} (dis : Disjoint A B) {s : Finset α}
    (hs : s ∈ pairs A B) : s.card = 2 := by
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_pairs.mp hs
  have ne : a ≠ b := fun q => Finset.disjoint_left.mp dis ha (q ▸ hb)
  simp [ne]

theorem pairs_card {A B : Finset α} (dis : Disjoint A B) :
    (pairs A B).card = A.card * B.card := by
  classical
  unfold pairs
  rw [Finset.card_image_of_injOn, Finset.card_product]
  intro a ha b hb eq
  obtain ⟨ha₁,ha₂⟩ := Finset.mem_product.mp ha
  obtain ⟨hb₁,hb₂⟩ := Finset.mem_product.mp hb
  change ({a.1,a.2} : Finset α) = {b.1,b.2} at eq
  have first : a.1 ∈ ({b.1,b.2} : Finset α) := eq ▸ Finset.mem_insert_self _ _
  have second : a.2 ∈ ({b.1,b.2} : Finset α) := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  simp only [Finset.mem_insert, Finset.mem_singleton] at first second
  apply Prod.ext
  · exact first.resolve_right (fun e => Finset.disjoint_left.mp dis ha₁ (e ▸ hb₂))
  · exact second.resolve_left (fun e => Finset.disjoint_left.mp dis hb₁ (e ▸ ha₂))

theorem base_card {L R : Finset α} (lr : Disjoint L R) :
    (baseSet L R).card = L.card + R.card + 1 := by
  have no : (∅ : Finset α) ∉ singles (L ∪ R) := by
    intro h
    obtain ⟨i,_,eq⟩ := mem_singles.mp h
    simpa using congrArg Finset.card eq
  rw [baseSet, Finset.card_insert_of_notMem no, singles_card, Finset.card_union_of_disjoint lr]

theorem switch_sizes {L R E : Finset α} {p : α} (lr : Disjoint L R)
    (ex : Disjoint E (L ∪ R)) (hp : p ∈ R) :
    Disjoint (baseSet L R) (switchSet L R E p) ∧
      (switchSet L R E p).card = L.card * R.card + 2 * E.card := by
  classical
  have pe : Disjoint E {p} := by
    rw [Finset.disjoint_singleton_right]
    exact fun hep => Finset.disjoint_left.mp ex hep (Finset.mem_union_right _ hp)
  have size₁ {s : Finset α} (hs : s ∈ singles E) : s.card = 1 := by
    obtain ⟨i,_,rfl⟩ := mem_singles.mp hs
    simp
  have sl : Disjoint (singles E) (pairs L R) := by
    rw [Finset.disjoint_left]
    intro s h₁ h₂
    have := size₁ h₁
    have := pair_size lr h₂
    omega
  have sp : Disjoint (singles E) (pairs E {p}) := by
    rw [Finset.disjoint_left]
    intro s h₁ h₂
    have := size₁ h₁
    have := pair_size pe h₂
    omega
  have lp : Disjoint (pairs L R) (pairs E {p}) := by
    rw [Finset.disjoint_left]
    intro s h₁ h₂
    obtain ⟨l,hl,r,hr,rfl⟩ := mem_pairs.mp h₁
    obtain ⟨e,he,q,hq,eq⟩ := mem_pairs.mp h₂
    obtain rfl := Finset.mem_singleton.mp hq
    have m : e ∈ ({l,r} : Finset α) := eq ▸ Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp m with e₁|e₂
    · exact Finset.disjoint_left.mp ex he (Finset.mem_union_left _ (e₁ ▸ hl))
    · exact Finset.disjoint_left.mp ex he (Finset.mem_union_right _ ((Finset.mem_singleton.mp e₂) ▸ hr))
  constructor
  · rw [Finset.disjoint_left]
    intro s hB hS
    have small : s.card ≤ 1 := by
      rcases Finset.mem_insert.mp hB with rfl|w
      · simp
      · obtain ⟨i,_,rfl⟩ := mem_singles.mp w; simp
    rcases Finset.mem_union.mp hS with both|pair
    · rcases Finset.mem_union.mp both with one|pair
      · obtain ⟨i,hi,rfl⟩ := mem_singles.mp one
        rcases Finset.mem_insert.mp hB with ill|hh
        · simpa using congrArg Finset.card ill
        · obtain ⟨j,hj,eq⟩ := mem_singles.mp hh
          have h : i = j := by simpa using eq
          exact Finset.disjoint_left.mp ex hi (h ▸ hj)
      · have := pair_size lr pair; omega
    · have := pair_size pe pair; omega
  · have mix := Finset.disjoint_union_left.mpr ⟨sp,lp⟩
    rw [switchSet,Finset.card_union_of_disjoint mix,Finset.card_union_of_disjoint sl,
      singles_card,pairs_card lr,pairs_card pe,Finset.card_singleton,Nat.mul_one]
    omega

theorem balanced (m : ℕ) : (m/2) * (m - m/2) = m*m/4 := by
  let k := m/2
  change k*(m-k)=m*m/4
  have alt : m=2*k ∨ m=2*k+1 := by dsimp [k]; omega
  rcases alt with e|e
  · have h : m-k=k := by omega
    rw [h,e]
    have g : 2*k*(2*k) = 4*(k*k) := by ring
    rw [g]
    omega
  · have h : m-k=k+1 := by omega
    rw [h,e]
    have g : (2*k+1)*(2*k+1) = 4*(k*(k+1))+1 := by ring
    rw [g]
    omega

end PEqualNP.Outside.L_lib_1086_aux

namespace PEqualNP.Outside.L_lib_1086_aux

theorem realizable {n : ℕ} (Z : Points n) (recover : ∀ t, PairApprox Z t → t ∈ Z) :
    ∃ A : Finset (Clause n), ∀ x : Word n, Sat A x ↔ x ∈ Z.image word := by
  classical
  apply sat_of_separation
  intro x hx
  by_contra! no
  have approx : PairApprox Z (supp x) := by
    intro i j
    obtain ⟨y,hy,hi,hj⟩ := no i j
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hy
    refine ⟨s,hs,?_,?_⟩
    · have hh := congrArg (fun b : Bool => b = true) hi
      simpa [word] using hh
    · have hh := congrArg (fun b : Bool => b = true) hj
      simpa [word] using hh
  have img := Finset.mem_image_of_mem word (recover (supp x) approx)
  exact hx (by simpa using img)

theorem word_free {n : ℕ} {L R E : Finset (Fin n)} {p : Fin n}
    (lr : Disjoint L R) (ex : Disjoint E (L ∪ R)) (hp : p ∈ R) :
    Free ((baseSet L R).image word) ((switchSet L R E p).image word) := by
  classical
  have dis := (switch_sizes lr ex hp).1
  constructor
  · rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,eq⟩ := Finset.mem_image.mp hy
    exact (Finset.disjoint_left.mp dis ha) ((word_inj eq) ▸ hb)
  · intro D hD
    let T := (switchSet L R E p).filter (fun t => word t ∈ D)
    have sub : T ⊆ switchSet L R E p := Finset.filter_subset _ _
    have image : T.image word = D := by
      ext x
      constructor
      · intro h
        obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hy).2
      · intro h
        obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (hD h)
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hs,h⟩)
    obtain ⟨A,ha⟩ := realizable (baseSet L R ∪ T) (fun _ => recovered lr ex hp sub)
    refine ⟨A,fun x => ?_⟩
    simpa only [Finset.image_union,Finset.mem_union,image] using ha x

theorem lower (n m : ℕ) (pos : 1 ≤ m) (le : m ≤ n) :
    ∃ B S : Finset (Word n), Free B S ∧ B.card = m+1 ∧ S.card = m*m/4+2*(n-m) := by
  classical
  let V := (Finset.univ : Finset (Fin n))
  have vc : V.card = n := by simp [V]
  obtain ⟨active,hactive,ac⟩ := Finset.exists_subset_card_eq (show m ≤ V.card by omega)
  obtain ⟨L,hL,lc⟩ := Finset.exists_subset_card_eq (show m/2 ≤ active.card by omega)
  let R := active \ L
  let E := V \ active
  have rc : R.card = m-m/2 := by
    change (active \ L).card = _
    rw [Finset.card_sdiff_of_subset hL,ac,lc]
  have ec : E.card = n-m := by
    change (V \ active).card = _
    rw [Finset.card_sdiff_of_subset hactive,vc,ac]
  have union : L ∪ R = active := by
    ext i
    simp only [R,Finset.mem_union,Finset.mem_sdiff]
    by_cases h : i ∈ L <;> simp [h]
    exact hL h
  have lr : Disjoint L R := Finset.disjoint_sdiff
  have ex : Disjoint E (L ∪ R) := by rw [union]; exact Finset.sdiff_disjoint
  have rne : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p,hp⟩ := rne
  refine ⟨(baseSet L R).image word,(switchSet L R E p).image word,word_free lr ex hp,?_,?_⟩
  · rw [Finset.card_image_of_injective _ word_inj,base_card lr,lc,rc]
    omega
  · rw [Finset.card_image_of_injective _ word_inj,(switch_sizes lr ex hp).2,lc,rc,ec,balanced]

end PEqualNP.Outside.L_lib_1086_aux

theorem PEqualNP.Outside.L_lib_1086 : (let W := fun n : ℕ => Fin n → Bool
let F := fun n : ℕ => Finset ((Fin n × Bool) × (Fin n × Bool))
let sat := fun (n : ℕ) (A : F n) (x : W n) =>
  ∀ c ∈ A, x c.1.1 ≠ c.1.2 ∨ x c.2.1 ≠ c.2.2
let free := fun (n : ℕ) (B S : Finset (W n)) =>
  Disjoint B S ∧ ∀ D : Finset (W n), D ⊆ S → ∃ A : F n,
    ∀ x : W n, (sat n A x ↔ (x ∈ B ∨ x ∈ D))
∀ n : ℕ,
  (∀ B S : Finset (W n), free n B S →
    S.card ≤ 2 * n + 1 + B.card * B.card / 4) ∧
  ∀ m : ℕ, 1 ≤ m → m ≤ n →
    ∃ B S : Finset (W n), free n B S ∧ B.card = m + 1 ∧
      S.card = m * m / 4 + 2 * (n - m)) := by
  dsimp only
  intro n
  exact ⟨PEqualNP.Outside.L_lib_1086_aux.upper, PEqualNP.Outside.L_lib_1086_aux.lower n⟩
