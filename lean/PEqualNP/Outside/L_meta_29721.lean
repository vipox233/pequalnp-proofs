import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29721
/- The circuit normalization and the reachability lemmas adapt Niklas Hummel’s
   L-meta-27805 (PR #43535). The read-once tree and table classification are new. -/

namespace TightOneHot

inductive Tree where
  | wire (id : ℕ)
  | both (left right : Tree)
  | either (left right : Tree)

namespace Tree

def support : Tree → Finset ℕ
  | .wire id => {id}
  | .both a b | .either a b => a.support ∪ b.support

def readOnce : Tree → Prop
  | .wire _ => True
  | .both a b | .either a b => a.readOnce ∧ b.readOnce ∧ Disjoint a.support b.support

def holds : Tree → Finset ℕ → Prop
  | .wire id, x => id ∈ x
  | .both a b, x => a.holds x ∧ b.holds x
  | .either a b, x => a.holds x ∨ b.holds x

lemma holds_empty (t : Tree) : ¬ t.holds ∅ := by
  induction t with
  | wire id => simp [holds]
  | both a b ha hb => simp [holds, ha, hb]
  | either a b ha hb => simp [holds, ha, hb]

lemma holds_mono (t : Tree) {x y : Finset ℕ} (h : x ⊆ y) : t.holds x → t.holds y := by
  induction t with
  | wire id => exact fun hx => h hx
  | both a b ha hb => exact fun hx => ⟨ha hx.1, hb hx.2⟩
  | either a b ha hb => exact fun hx => hx.elim (Or.inl ∘ ha) (Or.inr ∘ hb)

lemma holds_congr (t : Tree) {x y : Finset ℕ}
    (h : ∀ i ∈ t.support, i ∈ x ↔ i ∈ y) : t.holds x ↔ t.holds y := by
  induction t with
  | wire id => exact h id (by simp [support])
  | both a b ha hb =>
    exact and_congr (ha (fun i hi => h i (Finset.mem_union_left _ hi)))
      (hb (fun i hi => h i (Finset.mem_union_right _ hi)))
  | either a b ha hb =>
    exact or_congr (ha (fun i hi => h i (Finset.mem_union_left _ hi)))
      (hb (fun i hi => h i (Finset.mem_union_right _ hi)))

lemma insert_unused (t : Tree) (i : ℕ) (x : Finset ℕ) (hi : i ∉ t.support) :
    t.holds (insert i x) ↔ t.holds x := by
  apply holds_congr
  intro j hj
  simp only [Finset.mem_insert]
  exact ⟨fun h => h.elim (fun e => (hi (e ▸ hj)).elim) id, Or.inr⟩

lemma singleton_in_support (t : Tree) {i : ℕ} (h : t.holds {i}) : i ∈ t.support := by
  by_contra hi
  exact t.holds_empty ((t.insert_unused i ∅ hi).mp h)

lemma pair_uses_both (t : Tree) {i j : ℕ} (h : t.holds {i,j})
    (hi : ¬ t.holds {i}) (hj : ¬ t.holds {j}) :
    i ∈ t.support ∧ j ∈ t.support := by
  constructor
  · by_contra miss
    exact hj ((t.insert_unused i {j} miss).mp h)
  · by_contra miss
    rw [Finset.pair_comm] at h
    exact hi ((t.insert_unused j {i} miss).mp h)

lemma pair_has_input (t : Tree) {i j : ℕ} (h : t.holds {i,j}) :
    i ∈ t.support ∨ j ∈ t.support := by
  by_contra! hm
  exact hm.2 (t.singleton_in_support ((t.insert_unused i {j} hm.1).mp h))

lemma both_pair (a b : Tree) {i j : ℕ} (sep : Disjoint a.support b.support)
    (ha : a.holds {i,j}) (hb : b.holds {i,j}) :
    (a.holds {i} ∧ b.holds {j}) ∨ (a.holds {j} ∧ b.holds {i}) := by
  rcases a.pair_has_input ha with hi | hj
  · have hbi := (Finset.disjoint_left.mp sep) hi
    have hbj : j ∈ b.support := (b.pair_has_input hb).resolve_left hbi
    have haj := (Finset.disjoint_right.mp sep) hbj
    rw [Finset.pair_comm] at ha
    exact Or.inl ⟨(a.insert_unused j {i} haj).mp ha, (b.insert_unused i {j} hbi).mp hb⟩
  · have hbj := (Finset.disjoint_left.mp sep) hj
    have hbi : i ∈ b.support := (b.pair_has_input hb).resolve_right hbj
    have hai := (Finset.disjoint_right.mp sep) hbi
    rw [Finset.pair_comm] at hb
    exact Or.inr ⟨(a.insert_unused i {j} hai).mp ha, (b.insert_unused j {i} hbj).mp hb⟩

lemma meet_exchange (a b : Tree) {i j k : ℕ} (sep : Disjoint a.support b.support)
    (hij : a.holds {i,j} ∧ b.holds {i,j})
    (hik : a.holds {i,k} ∧ b.holds {i,k}) (s : Finset ℕ) :
    (a.holds (insert j s) ∧ b.holds (insert j s)) ↔
      (a.holds (insert k s) ∧ b.holds (insert k s)) := by
  rcases both_pair a b sep hij.1 hij.2 with ⟨ai,bj⟩ | ⟨aj,bi⟩ <;>
    rcases both_pair a b sep hik.1 hik.2 with ⟨ai',bk⟩ | ⟨ak,bi'⟩
  · have ajn := (Finset.disjoint_right.mp sep) (b.singleton_in_support bj)
    have akn := (Finset.disjoint_right.mp sep) (b.singleton_in_support bk)
    have bj' : b.holds (insert j s) := b.holds_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) bj
    have bk' : b.holds (insert k s) := b.holds_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) bk
    simp only [bj', bk', and_true, a.insert_unused _ s ajn, a.insert_unused _ s akn]
  · exact ((Finset.disjoint_left.mp sep) (a.singleton_in_support ai)
      (b.singleton_in_support bi')).elim
  · exact ((Finset.disjoint_left.mp sep) (a.singleton_in_support ai')
      (b.singleton_in_support bi)).elim
  · have bjn := (Finset.disjoint_left.mp sep) (a.singleton_in_support aj)
    have bkn := (Finset.disjoint_left.mp sep) (a.singleton_in_support ak)
    have aj' : a.holds (insert j s) := a.holds_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) aj
    have ak' : a.holds (insert k s) := a.holds_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) ak
    simp only [aj', ak', true_and, b.insert_unused _ s bjn, b.insert_unused _ s bkn]

/-- With a common partner, the two accepted pairs have interchangeable other inputs. -/
lemma exchange (t : Tree) {i j k : ℕ} (ht : t.readOnce)
    (hij : t.holds {i,j}) (hik : t.holds {i,k})
    (hi : ¬ t.holds {i}) (hj : ¬ t.holds {j}) (hk : ¬ t.holds {k}) (s : Finset ℕ) :
    t.holds (insert j s) ↔ t.holds (insert k s) := by
  induction t with
  | wire id =>
    change id ∈ ({i,j} : Finset ℕ) at hij
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with e | e
    · subst id
      exact (hi (by simp [holds])).elim
    · subst id
      exact (hj (by simp [holds])).elim
  | both a b ha hb =>
    exact meet_exchange a b ht.2.2 hij hik s
  | either a b ha hb =>
    have nai : ¬ a.holds {i} := hi ∘ Or.inl
    have nbi : ¬ b.holds {i} := hi ∘ Or.inr
    have naj : ¬ a.holds {j} := hj ∘ Or.inl
    have nbj : ¬ b.holds {j} := hj ∘ Or.inr
    have nak : ¬ a.holds {k} := hk ∘ Or.inl
    have nbk : ¬ b.holds {k} := hk ∘ Or.inr
    rcases hij with aij | bij <;> rcases hik with aik | bik
    · have aj := (a.pair_uses_both aij nai naj).2
      have ak := (a.pair_uses_both aik nai nak).2
      exact or_congr (ha ht.1 aij aik nai naj nak)
        ((b.insert_unused _ s ((Finset.disjoint_left.mp ht.2.2) aj)).trans
          (b.insert_unused _ s ((Finset.disjoint_left.mp ht.2.2) ak)).symm)
    · exact ((Finset.disjoint_left.mp ht.2.2) (a.pair_uses_both aij nai naj).1
        (b.pair_uses_both bik nbi nbk).1).elim
    · exact ((Finset.disjoint_left.mp ht.2.2) (a.pair_uses_both aik nai nak).1
        (b.pair_uses_both bij nbi nbj).1).elim
    · have bj := (b.pair_uses_both bij nbi nbj).2
      have bk := (b.pair_uses_both bik nbi nbk).2
      exact or_congr
        ((a.insert_unused _ s ((Finset.disjoint_right.mp ht.2.2) bj)).trans
          (a.insert_unused _ s ((Finset.disjoint_right.mp ht.2.2) bk)).symm)
        (hb ht.2.1 bij bik nbi nbj nbk)

lemma rectangle (t : Tree) {a b c d : ℕ} (ht : t.readOnce)
    (hab : t.holds {a,b}) (hac : t.holds {a,c}) (hdb : t.holds {d,b})
    (ha : ¬ t.holds {a}) (hb : ¬ t.holds {b}) (hc : ¬ t.holds {c}) :
    t.holds {d,c} := by
  simpa only [Finset.pair_comm d] using
    (t.exchange ht hab hac ha hb hc {d}).mp (by simpa only [Finset.pair_comm d] using hdb)

end Tree
end TightOneHot

namespace TightOneHot.Tree

structure PairSplit (t : Tree) (i j : ℕ) where
  left : Tree
  right : Tree
  rest : List Tree
  leftTrue : left.holds {i}
  rightTrue : right.holds {j}
  leftSub : left.support ⊆ t.support
  rightSub : right.support ⊆ t.support
  separate : Disjoint left.support right.support
  restSub : ∀ b ∈ rest, b.support ⊆ t.support
  separateRestLeft : ∀ b ∈ rest, Disjoint left.support b.support
  separateRestRight : ∀ b ∈ rest, Disjoint right.support b.support
  evaluate : ∀ S, t.holds S ↔
    (left.holds S ∧ right.holds S) ∨ ∃ b ∈ rest, b.holds S

lemma pairSplit (t : Tree) (ro : t.readOnce) {i j : ℕ}
    (pair : t.holds {i,j}) (hi : ¬ t.holds {i}) (hj : ¬ t.holds {j}) :
    Nonempty (PairSplit t i j) := by
  induction t with
  | wire k =>
    change k ∈ ({i,j} : Finset ℕ) at pair
    simp only [Finset.mem_insert, Finset.mem_singleton] at pair
    rcases pair with e | e
    · subst k
      exact (hi (by simp [holds])).elim
    · subst k
      exact (hj (by simp [holds])).elim
  | both a b ha hb =>
    rcases both_pair a b ro.2.2 pair.1 pair.2 with ⟨ai,bj⟩ | ⟨aj,bi⟩
    · refine ⟨⟨a,b,[],ai,bj,Finset.subset_union_left,Finset.subset_union_right,
        ro.2.2, ?_, ?_, ?_, ?_⟩⟩ <;> simp [holds]
    · refine ⟨⟨b,a,[],bi,aj,Finset.subset_union_right,Finset.subset_union_left,
        ro.2.2.symm, ?_, ?_, ?_, ?_⟩⟩ <;> simp [holds, and_comm]
  | either a b ha hb =>
    rcases pair with h | h
    · obtain ⟨d⟩ := ha ro.1 h (hi ∘ Or.inl) (hj ∘ Or.inl)
      refine ⟨⟨d.left,d.right,b :: d.rest,d.leftTrue,d.rightTrue,
        d.leftSub.trans Finset.subset_union_left, d.rightSub.trans Finset.subset_union_left,
        d.separate,?_,?_,?_,?_⟩⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Finset.subset_union_right
        · exact (d.restSub t ht).trans Finset.subset_union_left
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Disjoint.mono_left d.leftSub ro.2.2
        · exact d.separateRestLeft t ht
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Disjoint.mono_left d.rightSub ro.2.2
        · exact d.separateRestRight t ht
      · intro S
        simp only [holds, d.evaluate, List.mem_cons, exists_eq_or_imp, or_left_comm, or_comm]
    · obtain ⟨d⟩ := hb ro.2.1 h (hi ∘ Or.inr) (hj ∘ Or.inr)
      refine ⟨⟨d.left,d.right,a :: d.rest,d.leftTrue,d.rightTrue,
        d.leftSub.trans Finset.subset_union_right, d.rightSub.trans Finset.subset_union_right,
        d.separate,?_,?_,?_,?_⟩⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Finset.subset_union_left
        · exact (d.restSub t ht).trans Finset.subset_union_right
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Disjoint.mono_left d.leftSub ro.2.2.symm
        · exact d.separateRestLeft t ht
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Disjoint.mono_left d.rightSub ro.2.2.symm
        · exact d.separateRestRight t ht
      · intro S
        simp only [holds, d.evaluate, List.mem_cons, exists_eq_or_imp, or_left_comm]

end TightOneHot.Tree

namespace TightOneHot.Tree

lemma holds_insert (t : Tree) {i : ℕ} (h : t.holds {i}) (s : Finset ℕ) :
    t.holds (insert i s) :=
  t.holds_mono (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)) h

lemma PairSplit.accept_left {t : Tree} {p q : ℕ} (d : PairSplit t p q) {s : Finset ℕ}
    (h : d.left.holds s) : t.holds (insert q s) :=
  (d.evaluate _).mpr (.inl ⟨d.left.holds_mono (Finset.subset_insert _ _) h,
    d.right.holds_insert d.rightTrue s⟩)

lemma PairSplit.accept_right {t : Tree} {p q : ℕ} (d : PairSplit t p q) {s : Finset ℕ}
    (h : d.right.holds s) : t.holds (insert p s) :=
  (d.evaluate _).mpr (.inl ⟨d.left.holds_insert d.leftTrue s,
    d.right.holds_mono (Finset.subset_insert _ _) h⟩)

lemma left_on_neighbor {t : Tree} {p q l w a : ℕ} (d : PairSplit t p q)
    (hlw : t.holds {l,w}) (hw : ¬ t.holds {w})
    (hlq : ¬ t.holds {l,q}) (hla : ¬ t.holds {l,a})
    (h : t.holds (insert q {l,a})) :
    l ∉ d.left.support ∧ l ∉ d.right.support ∧ d.left.holds {a} := by
  have qRight := d.right.singleton_in_support d.rightTrue
  have qNotLeft := Finset.disjoint_right.mp d.separate qRight
  have hleft : d.left.holds {l,a} := by
    rcases (d.evaluate _).mp h with hprod | ⟨b, hb, hval⟩
    · exact (d.left.insert_unused q {l,a} qNotLeft).mp hprod.1
    · have qNotRest := Finset.disjoint_left.mp (d.separateRestRight b hb) qRight
      exact (hla ((d.evaluate _).mpr (.inr ⟨b, hb, (b.insert_unused q {l,a} qNotRest).mp hval⟩))).elim
  have hlProd (side : l ∈ d.left.support ∨ l ∈ d.right.support) :
      d.left.holds {l,w} ∧ d.right.holds {l,w} := by
    rcases (d.evaluate _).mp hlw with hprod | ⟨b, hb, hval⟩
    · exact hprod
    · have lNotRest : l ∉ b.support := side.elim
        (fun h => Finset.disjoint_left.mp (d.separateRestLeft b hb) h)
        (fun h => Finset.disjoint_left.mp (d.separateRestRight b hb) h)
      exact (hw ((d.evaluate _).mpr (.inr ⟨b, hb, (b.insert_unused l {w} lNotRest).mp hval⟩))).elim
  have lNotLeft : l ∉ d.left.support := by
    intro hlLeft
    have hprod := hlProd (.inl hlLeft)
    have wRight := d.right.singleton_in_support
      ((d.right.insert_unused l {w} (Finset.disjoint_left.mp d.separate hlLeft)).mp hprod.2)
    have hlLeftValue : d.left.holds {l} := by
      rw [Finset.pair_comm] at hprod
      exact (d.left.insert_unused w {l} (Finset.disjoint_right.mp d.separate wRight)).mp hprod.1
    exact hlq (by rw [Finset.pair_comm]; exact d.accept_left hlLeftValue)
  have lNotRight : l ∉ d.right.support := by
    intro hlRight
    have hprod := hlProd (.inr hlRight)
    have wLeft := d.left.singleton_in_support ((d.left.insert_unused l {w} lNotLeft).mp hprod.1)
    have hlRightValue : d.right.holds {l} := by
      rw [Finset.pair_comm] at hprod
      exact (d.right.insert_unused w {l} (Finset.disjoint_left.mp d.separate wLeft)).mp hprod.2
    have haLeft := (d.left.insert_unused l {a} lNotLeft).mp hleft
    exact hla ((d.evaluate _).mpr (.inl ⟨by
      rw [Finset.pair_comm]
      exact d.left.holds_insert haLeft _, d.right.holds_insert hlRightValue _⟩))
  exact ⟨lNotLeft, lNotRight, (d.left.insert_unused l {a} lNotLeft).mp hleft⟩

lemma neighbor_only_high_partner {t : Tree} {p q l a z : ℕ} (d : PairSplit t p q)
    (lNotRight : l ∉ d.right.support) (aLeft : d.left.holds {a})
    (hlz : ¬ t.holds {l,z}) (hpz : ¬ t.holds {p,z}) :
    ¬ t.holds (insert a {l,z}) := by
  intro h
  have aInLeft := d.left.singleton_in_support aLeft
  rcases (d.evaluate _).mp h with hprod | ⟨b, hb, hval⟩
  · have rightValue := (d.right.insert_unused l {z} lNotRight).mp
        ((d.right.insert_unused a _ (Finset.disjoint_left.mp d.separate aInLeft)).mp hprod.2)
    exact hpz (d.accept_right rightValue)
  · have aNotRest := Finset.disjoint_left.mp (d.separateRestLeft b hb) aInLeft
    exact hlz ((d.evaluate _).mpr (.inr ⟨b, hb, (b.insert_unused a _ aNotRest).mp hval⟩))

lemma left_exchange {t : Tree} {p q a b : ℕ} (d : PairSplit t p q)
    (ha : d.left.holds {a}) (hb : d.left.holds {b}) (s : Finset ℕ) :
    t.holds (insert a s) ↔ t.holds (insert b s) := by
  rw [d.evaluate, d.evaluate]
  have aLeft := d.left.singleton_in_support ha
  have bLeft := d.left.singleton_in_support hb
  apply or_congr
  · simp only [d.left.holds_insert ha s, d.left.holds_insert hb s, true_and,
      d.right.insert_unused _ _ (Finset.disjoint_left.mp d.separate aLeft),
      d.right.insert_unused _ _ (Finset.disjoint_left.mp d.separate bLeft)]
  · apply exists_congr
    intro v
    apply and_congr_right
    intro hv
    exact (v.insert_unused _ _ (Finset.disjoint_left.mp (d.separateRestLeft v hv) aLeft)).trans
      (v.insert_unused _ _ (Finset.disjoint_left.mp (d.separateRestLeft v hv) bLeft)).symm

end TightOneHot.Tree

namespace TightOneHot.Tree

inductive Fixed where
  | constant (b : Bool)
  | tree (t : Tree)

def Fixed.support : Fixed → Finset ℕ
  | .constant _ => ∅
  | .tree t => t.support

def Fixed.readOnce : Fixed → Prop
  | .constant _ => True
  | .tree t => t.readOnce

def Fixed.holds : Fixed → Finset ℕ → Prop
  | .constant b, _ => b = true
  | .tree t, s => t.holds s

def Fixed.both : Fixed → Fixed → Fixed
  | .constant false, _ | _, .constant false => .constant false
  | .constant true, b => b
  | a, .constant true => a
  | .tree a, .tree b => .tree (Tree.both a b)

def Fixed.either : Fixed → Fixed → Fixed
  | .constant true, _ | _, .constant true => .constant true
  | .constant false, b => b
  | a, .constant false => a
  | .tree a, .tree b => .tree (Tree.either a b)

lemma Fixed.both_holds (a b : Fixed) (s : Finset ℕ) :
    (a.both b).holds s ↔ a.holds s ∧ b.holds s := by
  cases a <;> cases b <;> try rename_i u v
  · cases u <;> cases v <;> simp [both, holds]
  · cases u <;> simp [both, holds]
  · cases v <;> simp [both, holds]
  · rfl

lemma Fixed.either_holds (a b : Fixed) (s : Finset ℕ) :
    (a.either b).holds s ↔ a.holds s ∨ b.holds s := by
  cases a <;> cases b <;> try rename_i u v
  · cases u <;> cases v <;> simp [either, holds]
  · cases u <;> simp [either, holds]
  · cases v <;> simp [either, holds]
  · rfl

lemma Fixed.both_support (a b : Fixed) :
    (a.both b).support ⊆ a.support ∪ b.support := by
  cases a <;> cases b <;> try rename_i u v
  · cases u <;> cases v <;> simp [both, support]
  · cases u <;> simp [both, support]
  · cases v <;> simp [both, support]
  · apply Finset.Subset.rfl

lemma Fixed.either_support (a b : Fixed) :
    (a.either b).support ⊆ a.support ∪ b.support := by
  cases a <;> cases b <;> try rename_i u v
  · cases u <;> cases v <;> simp [either, support]
  · cases u <;> simp [either, support]
  · cases v <;> simp [either, support]
  · apply Finset.Subset.rfl

lemma Fixed.both_readOnce (a b : Fixed) (ha : a.readOnce) (hb : b.readOnce)
    (hd : Disjoint a.support b.support) : (a.both b).readOnce := by
  cases a <;> cases b <;> try rename_i u v
  · cases u <;> cases v <;> trivial
  · cases u
    · trivial
    · exact hb
  · cases v
    · trivial
    · exact ha
  · exact ⟨ha,hb,hd⟩

lemma Fixed.either_readOnce (a b : Fixed) (ha : a.readOnce) (hb : b.readOnce)
    (hd : Disjoint a.support b.support) : (a.either b).readOnce := by
  cases a <;> cases b <;> try rename_i u v
  · cases u <;> cases v <;> trivial
  · cases u
    · exact hb
    · trivial
  · cases v
    · exact ha
    · trivial
  · exact ⟨ha,hb,hd⟩

def pin (i : ℕ) (v : Bool) : Tree → Fixed
  | .wire w => if w = i then .constant v else .tree (.wire w)
  | .both a b => (a.pin i v).both (b.pin i v)
  | .either a b => (a.pin i v).either (b.pin i v)

lemma pin_support (t : Tree) (i : ℕ) (v : Bool) : (t.pin i v).support ⊆ t.support := by
  induction t with
  | wire w =>
    by_cases h : w = i <;> simp [pin, h, Fixed.support]
  | both a b ha hb =>
    exact ((a.pin i v).both_support (b.pin i v)).trans (Finset.union_subset_union ha hb)
  | either a b ha hb =>
    exact ((a.pin i v).either_support (b.pin i v)).trans (Finset.union_subset_union ha hb)

lemma pin_readOnce (t : Tree) (h : t.readOnce) (i : ℕ) (v : Bool) :
    (t.pin i v).readOnce := by
  induction t with
  | wire w =>
    by_cases he : w = i <;> simp [pin, he, Fixed.readOnce, readOnce]
  | both a b ha hb =>
    exact (a.pin i v).both_readOnce _ (ha h.1) (hb h.2.1)
      (Disjoint.mono (a.pin_support i v) (b.pin_support i v) h.2.2)
  | either a b ha hb =>
    exact (a.pin i v).either_readOnce _ (ha h.1) (hb h.2.1)
      (Disjoint.mono (a.pin_support i v) (b.pin_support i v) h.2.2)

lemma pin_true_holds (t : Tree) (i : ℕ) (s : Finset ℕ) :
    (t.pin i true).holds s ↔ t.holds (insert i s) := by
  induction t with
  | wire w => by_cases h : w = i <;> simp [pin, h, holds, Fixed.holds]
  | both a b ha hb => exact ((a.pin i true).both_holds _ _).trans (and_congr ha hb)
  | either a b ha hb => exact ((a.pin i true).either_holds _ _).trans (or_congr ha hb)

lemma low_exchange (t : Tree) (ht : t.readOnce) {l a b c : ℕ}
    (hl : ¬ t.holds {l})
    (ha : ¬ t.holds {l,a}) (hb : ¬ t.holds {l,b}) (hc : ¬ t.holds {l,c})
    (hab : t.holds (insert l {a,b})) (hac : t.holds (insert l {a,c})) (s : Finset ℕ) :
    t.holds (insert l (insert b s)) ↔ t.holds (insert l (insert c s)) := by
  have pinned := t.pin_true_holds l
  have read := t.pin_readOnce ht l true
  cases eq : t.pin l true with
  | constant v =>
    rw [eq] at pinned
    have val := (pinned _).mpr hab
    exact (hl ((pinned ∅).mp val)).elim
  | tree u =>
    rw [eq] at pinned read
    exact (pinned _).symm.trans ((u.exchange read
      ((pinned _).mpr hab) ((pinned _).mpr hac)
      (ha ∘ (pinned _).mp) (hb ∘ (pinned _).mp) (hc ∘ (pinned _).mp) s).trans (pinned _))

end TightOneHot.Tree

namespace TightOneHot
open TightOneHot.Tree

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

structure Table (ι κ : Type) [DecidableEq ι] [DecidableEq κ] where
  f : ι → κ → Prop
  tree : Tree
  p : ℕ
  l : ℕ
  R : ι → ℕ
  C : κ → ℕ
  r : ι
  u : ι
  c : κ
  v : κ
  ro : tree.readOnce
  rAbsent : R r ∉ tree.support
  uAbsent : R u ∉ tree.support
  cAbsent : C c ∉ tree.support
  vAbsent : C v ∉ tree.support
  highEmpty : ¬ tree.holds {p}
  lowEmpty : ¬ tree.holds {l}
  repr : ∀ i j, f i j ↔ tree.holds (insert (if i = u ∨ j = v then p else l) {R i,C j})
  rows : Function.Injective f
  cols : Function.Injective (fun j i => f i j)
  noFullRow : ∀ i, ∃ j, ¬ f i j
  noFullCol : ∀ j, ∃ i, ¬ f i j
  ru : r ≠ u
  cv : c ≠ v
  diffLow : ∃ i, f i c ∧ ¬ f i v
  diffHigh : ∃ i, f i v ∧ ¬ f i c
  diffLowCol : ∃ j, f r j ∧ ¬ f u j
  diffHighCol : ∃ j, f u j ∧ ¬ f r j

namespace Table

variable (a : Table ι κ)

def flip : Table κ ι where
  f j i := a.f i j
  tree := a.tree
  p := a.p
  l := a.l
  R := a.C
  C := a.R
  r := a.c
  u := a.v
  c := a.r
  v := a.u
  ro := a.ro
  rAbsent := a.cAbsent
  uAbsent := a.vAbsent
  cAbsent := a.rAbsent
  vAbsent := a.uAbsent
  highEmpty := a.highEmpty
  lowEmpty := a.lowEmpty
  repr j i := by simpa only [or_comm, Finset.pair_comm] using a.repr i j
  rows := a.cols
  cols := a.rows
  noFullRow := a.noFullCol
  noFullCol := a.noFullRow
  ru := a.cv
  cv := a.ru
  diffLow := a.diffLowCol
  diffHigh := a.diffHighCol
  diffLowCol := a.diffLow
  diffHighCol := a.diffHigh

lemma cValue (i : ι) :
    a.f i a.c ↔ a.tree.holds {if i = a.u then a.p else a.l, a.R i} := by
  rw [a.repr]
  simp only [a.cv, or_false]
  rw [Finset.pair_comm (a.R i), Finset.insert_comm]
  exact a.tree.insert_unused _ _ a.cAbsent

lemma vValue (i : ι) :
    a.f i a.v ↔ a.tree.holds {a.p, a.R i} := by
  rw [a.repr]
  simp only [or_true, ite_true]
  rw [Finset.pair_comm (a.R i), Finset.insert_comm]
  exact a.tree.insert_unused _ _ a.vAbsent

lemma ordinary (i : ι) (j : κ) (hi : i ≠ a.u) (hj : j ≠ a.v) :
    a.f i j ↔ a.tree.holds (insert a.l {a.R i,a.C j}) := by
  simpa [hi,hj] using a.repr i j

lemma notRowSingle (i : ι) : ¬ a.tree.holds {a.R i} := by
  intro h
  obtain ⟨j, hj⟩ := a.noFullRow i
  exact hj ((a.repr i j).mpr (a.tree.holds_mono (by simp) h))

lemma notColSingle (j : κ) : ¬ a.tree.holds {a.C j} :=
  a.flip.notRowSingle j

lemma controlsFalse : ¬ a.f a.r a.c ∧ ¬ a.f a.r a.v ∧
    ¬ a.f a.u a.c ∧ ¬ a.f a.u a.v := by
  rw [a.cValue a.r, a.vValue a.r, a.cValue a.u, a.vValue a.u]
  simp only [a.ru, ite_false, ite_true]
  have absent (q w : ℕ) (hw : w ∉ a.tree.support) : ¬ a.tree.holds {q} → ¬ a.tree.holds {q,w} := by
    rw [Finset.pair_comm]
    exact fun h => h ∘ (a.tree.insert_unused w {q} hw).mp
  exact ⟨absent _ _ a.rAbsent a.lowEmpty, absent _ _ a.rAbsent a.highEmpty,
    absent _ _ a.uAbsent a.highEmpty, absent _ _ a.uAbsent a.highEmpty⟩

lemma equate_rows (i k : ι) (hi : i ≠ a.u) (hk : k ≠ a.u)
    (h : ∀ S, a.tree.holds (insert (a.R i) S) ↔ a.tree.holds (insert (a.R k) S)) :
    i = k := by
  apply a.rows
  funext j
  apply propext
  rw [a.repr, a.repr]
  simp only [hi, hk, false_or]
  rw [Finset.insert_comm _ (a.R i), Finset.insert_comm _ (a.R k)]
  exact h _

lemma low_row (x : ι) (hx : a.f x a.c) (hxHigh : ¬ a.f x a.v) :
    x ≠ a.r ∧ x ≠ a.u ∧ a.tree.holds {a.l,a.R x} ∧ ¬ a.tree.holds {a.p,a.R x} ∧
    (∀ i, a.f i a.c ↔ i = x) ∧ (∀ j, a.f x j ↔ j ≠ a.v) := by
  have xr : x ≠ a.r := fun e => a.controlsFalse.1 (e ▸ hx)
  have xu : x ≠ a.u := fun e => a.controlsFalse.2.2.1 (e ▸ hx)
  have low : a.tree.holds {a.l,a.R x} := by simpa [a.cValue, xu] using hx
  have high : ¬ a.tree.holds {a.p,a.R x} := fun h => hxHigh ((a.vValue x).mpr h)
  refine ⟨xr,xu,low,high, ?_,?_⟩
  · intro i
    constructor
    · intro hi
      have iu : i ≠ a.u := fun e => a.controlsFalse.2.2.1 (e ▸ hi)
      have il : a.tree.holds {a.l,a.R i} := by simpa [a.cValue, iu] using hi
      exact a.equate_rows i x iu xu
        (a.tree.exchange a.ro il low a.lowEmpty (a.notRowSingle i) (a.notRowSingle x))
    · rintro rfl
      exact hx
  · intro j
    constructor
    · exact fun h e => hxHigh (e ▸ h)
    · intro jv
      exact (a.ordinary x j xu jv).mpr (a.tree.holds_mono (by simp) low)

lemma high_row (x : ι) (hx : a.f x a.v) (hxLow : ¬ a.f x a.c) :
    x ≠ a.r ∧ x ≠ a.u ∧ a.tree.holds {a.p,a.R x} ∧ ¬ a.tree.holds {a.l,a.R x} ∧
    (∀ i, a.f i a.v ↔ i = x) := by
  have xr : x ≠ a.r := fun e => a.controlsFalse.2.1 (e ▸ hx)
  have xu : x ≠ a.u := fun e => a.controlsFalse.2.2.2 (e ▸ hx)
  have high := (a.vValue x).mp hx
  have low : ¬ a.tree.holds {a.l,a.R x} := by simpa [a.cValue, xu] using hxLow
  refine ⟨xr,xu,high,low,?_⟩
  intro i
  constructor
  · intro hi
    have iu : i ≠ a.u := fun e => a.controlsFalse.2.2.2 (e ▸ hi)
    exact a.equate_rows i x iu xu (a.tree.exchange a.ro ((a.vValue i).mp hi)
      high a.highEmpty (a.notRowSingle i) (a.notRowSingle x))
  · rintro rfl
    exact hx

structure Core where
  lo : ι
  hi : ι
  loCol : κ
  hiCol : κ
  loWitness : a.f lo a.c ∧ ¬ a.f lo a.v
  hiWitness : a.f hi a.v ∧ ¬ a.f hi a.c
  loColWitness : a.f a.r loCol ∧ ¬ a.f a.u loCol
  hiColWitness : a.f a.u hiCol ∧ ¬ a.f a.r hiCol

def Core.flip (d : a.Core) : a.flip.Core :=
  ⟨d.loCol,d.hiCol,d.lo,d.hi,d.loColWitness,d.hiColWitness,d.loWitness,d.hiWitness⟩

variable {a : Table ι κ} (d : a.Core)

def Core.low (d : a.Core) := a.low_row d.lo d.loWitness.1 d.loWitness.2
def Core.high (d : a.Core) := a.high_row d.hi d.hiWitness.1 d.hiWitness.2

def Core.rowRest (d : a.Core) (i : ι) : Prop :=
  i ≠ a.r ∧ i ≠ a.u ∧ i ≠ d.lo

def Core.colRest (d : a.Core) (j : κ) : Prop :=
  j ≠ a.c ∧ j ≠ a.v ∧ j ≠ d.loCol

lemma Core.lowFalse {i : ι} (hi : d.rowRest i) : ¬ a.tree.holds {a.l,a.R i} := by
  intro h
  have value : a.f i a.c := (a.cValue i).mpr (by simpa [hi.2.1] using h)
  exact hi.2.2 ((d.low.2.2.2.2.1 i).mp value)

lemma Core.highFalse {i : ι} (hi : i ≠ d.hi) : ¬ a.tree.holds {a.p,a.R i} :=
  fun h => hi ((d.high.2.2.2.2 i).mp ((a.vValue i).mpr h))

lemma Core.hiRest : d.rowRest d.hi :=
  ⟨d.high.1,d.high.2.1,fun e => d.hiWitness.2 (e ▸ d.loWitness.1)⟩

lemma Core.diagonal : ¬ a.f d.hi d.hiCol := by
  intro h
  have value := (a.ordinary d.hi d.hiCol d.hiRest.2.1 d.flip.hiRest.2.1).mp h
  have exchange := a.tree.exchange a.ro d.high.2.2.1 d.flip.high.2.2.1
    a.highEmpty (a.notRowSingle d.hi) (a.notColSingle d.hiCol) {a.l,a.R d.hi}
  apply d.high.2.2.2.1
  have other : a.tree.holds (insert (a.C d.hiCol) {a.l,a.R d.hi}) := by
    rw [Finset.insert_comm, Finset.pair_comm (a.C d.hiCol)]
    exact value
  have same := exchange.mpr other
  rw [Finset.insert_comm] at same
  have collapsed : ({a.l,a.R d.hi,a.R d.hi} : Finset ℕ) = {a.l,a.R d.hi} := by
    ext w; simp [or_assoc]
  rw [collapsed] at same
  exact same

lemma Core.lowRowsEq {i k : ι} (hi : d.rowRest i) (hk : d.rowRest k)
    (high : a.f i a.v ↔ a.f k a.v)
    (low : ∀ j, d.colRest j → (a.f i j ↔ a.f k j)) : i = k := by
  apply a.rows
  funext j
  apply propext
  by_cases jc : j = a.c
  · subst j
    exact (d.low.2.2.2.2.1 i).trans ((iff_of_false hi.2.2 hk.2.2).trans (d.low.2.2.2.2.1 k).symm)
  by_cases jv : j = a.v
  · subst j
    exact high
  by_cases jl : j = d.loCol
  · subst j
    change a.flip.f d.loCol i ↔ a.flip.f d.loCol k
    exact iff_of_true ((d.flip.low.2.2.2.2.2 i).mpr hi.2.1) ((d.flip.low.2.2.2.2.2 k).mpr hk.2.1)
  exact low j ⟨jc,jv,jl⟩

lemma Core.uniqueRows (j : κ) (hj : d.colRest j) (i k : ι)
    (hi : d.rowRest i) (hk : d.rowRest k) (hij : a.f i j) (hkj : a.f k j) : i = k := by
  have acceptI := (a.ordinary i j hi.2.1 hj.2.1).mp hij
  have acceptK := (a.ordinary k j hk.2.1 hj.2.1).mp hkj
  have sameHigh (i k : ι) (hi : d.rowRest i) (hk : d.rowRest k)
      (ai : a.tree.holds (insert a.l {a.R i,a.C j}))
      (ak : a.tree.holds (insert a.l {a.R k,a.C j}))
      (hh : a.f i a.v ↔ a.f k a.v) : i = k := by
    apply d.lowRowsEq hi hk hh
    intro s hs
    have exch := a.tree.low_exchange a.ro a.lowEmpty
      (d.flip.lowFalse hj) (d.lowFalse hi) (d.lowFalse hk)
      (by rwa [Finset.pair_comm]) (by rwa [Finset.pair_comm]) {a.C s}
    exact (a.ordinary i s hi.2.1 hs.2.1).trans
      (exch.trans (a.ordinary k s hk.2.1 hs.2.1).symm)
  have special (k : ι) (hk : d.rowRest k) (hn : k ≠ d.hi)
      (aHi : a.f d.hi j) (ak : a.f k j) : False := by
    obtain ⟨split⟩ := a.tree.pairSplit a.ro d.high.2.2.1 a.highEmpty (a.notRowSingle d.hi)
    have hp := (a.ordinary d.hi j d.hiRest.2.1 hj.2.1).mp aHi
    have hp' : a.tree.holds (insert (a.R d.hi) {a.l,a.C j}) := by
      rwa [Finset.insert_comm]
    obtain ⟨_,hRight,hLeft⟩ := left_on_neighbor split d.low.2.2.1 (a.notRowSingle d.lo)
      d.high.2.2.2.1 (d.flip.lowFalse hj) hp'
    have invalid := neighbor_only_high_partner split hRight hLeft
      (d.lowFalse hk) (d.highFalse hn)
    apply invalid
    have val := (a.ordinary k j hk.2.1 hj.2.1).mp ak
    change a.tree.holds (insert (a.C j) {a.l,a.R k})
    rw [Finset.insert_comm, Finset.pair_comm (a.C j)]
    exact val
  by_cases e1 : i = d.hi
  · subst i
    by_cases e2 : k = d.hi
    · exact e2.symm
    · exact (special k hk e2 hij hkj).elim
  by_cases e2 : k = d.hi
  · subst k
    exact (special i hi e1 hkj hij).elim
  exact sameHigh i k hi hk acceptI acceptK
    (iff_of_false (fun h => e1 ((d.high.2.2.2.2 i).mp h))
      (fun h => e2 ((d.high.2.2.2.2 k).mp h)))

lemma Core.existsCol (i : ι) (hi : d.rowRest i) (hn : i ≠ d.hi) :
    ∃ j, d.colRest j ∧ a.f i j := by
  by_contra! absent
  apply hi.1 (a.rows (funext fun j => propext (show a.f i j ↔ a.f a.r j from by
    by_cases jc : j = a.c
    · subst j
      exact iff_of_false (fun h => hi.2.2 ((d.low.2.2.2.2.1 i).mp h)) a.controlsFalse.1
    by_cases jv : j = a.v
    · subst j
      exact iff_of_false (fun h => hn ((d.high.2.2.2.2 i).mp h)) a.controlsFalse.2.1
    by_cases jl : j = d.loCol
    · subst j
      change a.flip.f d.loCol i ↔ a.flip.f d.loCol a.r
      exact iff_of_true ((d.flip.low.2.2.2.2.2 i).mpr hi.2.1)
        ((d.flip.low.2.2.2.2.2 a.r).mpr a.ru)
    · exact iff_of_false (absent j ⟨jc,jv,jl⟩)
        (fun h => jl ((d.flip.low.2.2.2.2.1 j).mp h)))))

end Table
end TightOneHot

namespace Base.CircuitFacts
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool := x ++ [compute x g]

theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, step, ih]; omega

theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega

theorem getD_ge (W : List Bool) (i : ℕ) (h : W.length ≤ i) : W.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem pre (gs : List Gate) : ∀ (x : List Bool) (w : ℕ), w < x.length →
    (gs.foldl step x).getD w false = x.getD w false := by
  induction gs with
  | nil => intro x w _; rfl
  | cons g gs ih =>
    intro x w h
    rw [List.foldl_cons, ih _ _ (by simp [step]; omega), step, snoc, ite_eq_left h]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl step w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (step (gs.foldl step w) g).getD i false = (gs.foldl step w).getD i false := by
      intro i hi
      simp only [step, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (step (gs.foldl step w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl step w).getD i false) := by
        simp only [step, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen, compute, List.getD_eq_getElem?_getD]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

theorem gate_formula (C : Circuit) {N j : ℕ} (x : List Bool)
    (hx : x.length = N) (hj : j < C.gates.length) :
    (C.gates.foldl step x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        if i < N + j then (C.gates.foldl step x).getD i false else false) := by
  have h := foldl_char C.gates x j hj
  rw [hx] at h
  exact h

def before (C : Circuit) (N j w : ℕ) : Prop := w ∈ (gateAt C j).inputs ∧ w < N + j

def closed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Prop :=
  (∀ j ∈ L, j < C.gates.length) ∧
    ∀ j ∈ L, ∀ i, before C N j (N + i) → i ∈ L

theorem minimal_closed (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) :
    ∃ L : Finset ℕ, r ∈ L ∧ closed N C L ∧
      ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N + i) := by
  classical
  let A := Finset.range C.gates.length
  have hc : closed N C A := by
    refine ⟨fun j hj => Finset.mem_range.mp hj, ?_⟩
    intro j hj i hi
    have hlt := Finset.mem_range.mp hj
    have hs := hi.2
    exact Finset.mem_range.mpr (by omega)
  let candidates := A.powerset.filter fun L => r ∈ L ∧ closed N C L
  have hA : A ∈ candidates := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _), Finset.mem_range.mpr hr, hc⟩
  obtain ⟨L, hL, hmin⟩ := candidates.exists_min_image Finset.card ⟨A, hA⟩
  obtain ⟨hsub, hrL, hclose⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hrL, hclose, ?_⟩
  intro i hi hir
  by_contra hn
  have hs : L.erase i ∈ candidates := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.mem_erase.mpr ⟨Ne.symm hir, hrL⟩, ?_⟩
    · exact (Finset.erase_subset _ _).trans (Finset.mem_powerset.mp hsub)
    · constructor
      · intro j hj
        exact hclose.1 j (Finset.mem_of_mem_erase hj)
      · intro j hj k hkj
        have hj' := Finset.mem_of_mem_erase hj
        refine Finset.mem_erase.mpr ⟨?_, hclose.2 j hj' k hkj⟩
        rintro rfl
        exact hn ⟨j, hj', hkj⟩
  have h := hmin _ hs
  have hpos := Finset.card_pos.mpr ⟨i, hi⟩
  rw [Finset.card_erase_of_mem hi] at h
  omega

def inputSlots (N : ℕ) (C : Circuit) (j : ℕ) : Finset (ℕ × ℕ) :=
  ((gateAt C j).inputs.toFinset.filter (· < N + j)).image (Prod.mk j)

def slots (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (ℕ × ℕ) :=
  L.biUnion (inputSlots N C)

theorem mem_slot {N : ℕ} {C : Circuit} {L : Finset ℕ} {j w : ℕ} :
    (j,w) ∈ slots N C L ↔ j ∈ L ∧ before C N j w := by
  constructor
  · intro h
    obtain ⟨j', hj', hh⟩ := Finset.mem_biUnion.mp h
    obtain ⟨w', hw', he⟩ := Finset.mem_image.mp hh
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl,rfl⟩ := he
    have ⟨hi,hl⟩ := Finset.mem_filter.mp hw'
    exact ⟨hj', List.mem_toFinset.mp hi, hl⟩
  · rintro ⟨hj, hw, hl⟩
    exact Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw,hl⟩,rfl⟩⟩

def used (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (slots N C L).image Prod.snd

theorem mem_used {N : ℕ} {C : Circuit} {L : Finset ℕ} {w : ℕ} :
    w ∈ used N C L ↔ ∃ j ∈ L, before C N j w := by
  constructor
  · intro h
    obtain ⟨⟨j,i⟩, hslot, e⟩ := Finset.mem_image.mp h
    change i = w at e
    subst i
    exact ⟨j,(mem_slot.mp hslot).1,(mem_slot.mp hslot).2⟩
  · rintro ⟨j,hj,hw⟩
    exact Finset.mem_image.mpr ⟨(j,w),mem_slot.mpr ⟨hj,hw⟩,rfl⟩

theorem closed_values {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) :
    ∀ j ∈ L, (C.gates.foldl step x).getD (N + j) false =
      (C.gates.foldl step y).getD (N + j) false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    rw [gate_formula C x hx (hL.1 j hj), gate_formula C y hy (hL.1 j hj)]
    congr 1
    apply List.map_congr_left
    intro w hw
    split_ifs with hb <;> try rfl
    by_cases hi : w < N
    · rw [pre _ _ _ (by omega : w < x.length), pre _ _ _ (by omega : w < y.length)]
      exact he w (mem_used.mpr ⟨j,hj,hw,hb⟩)
    · let i := w - N
      have e : N + i = w := by dsimp [i]; omega
      have hil : i < j := by omega
      rw [← e] at hw hb ⊢
      exact ih i hil (hL.2 j hj i ⟨hw,hb⟩)

theorem inputSlots_card (N : ℕ) (C : Circuit) (j : ℕ) :
    (inputSlots N C j).card = ((gateAt C j).inputs.toFinset.filter (· < N + j)).card :=
  Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)

theorem root_bounds {n m : ℕ} {A : Fin n → Fin m → Bool}
    (hn : 2 ≤ n)
    (hrow : ∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false)
    (hcol : ∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false)
    (C : Circuit) (hG : Represents A C) :
    n + m ≤ C.output ∧ C.output < n + m + C.gates.length := by
  have raw (u : Fin n) (v : Fin m) (hi : C.output < n + m) :
      C.eval (oneEach u v) = (oneEach u v).getD C.output false := by
    exact pre _ _ _ (by simpa [oneEach] using hi)
  constructor
  · by_contra! h
    by_cases hin : C.output < n
    · let a : Fin n := ⟨C.output, hin⟩
      obtain ⟨b, hne, _, _⟩ := hrow a
      obtain ⟨_, _, v, ht, _⟩ := hrow b
      have he := (hG b v).trans ht
      rw [raw _ _ h, each_value, decide_eq_true_eq] at he
      rcases he with he | he
      · exact hne (Fin.ext he.symm)
      · omega
    · let v : Fin m := ⟨C.output - n, by omega⟩
      have ev : n + v.val = C.output := by dsimp [v]; omega
      obtain ⟨w, hne, _, _⟩ := hcol v
      obtain ⟨_, _, a, ht, _⟩ := hcol w
      have he := (hG a w).trans ht
      rw [raw _ _ h, each_value, decide_eq_true_eq] at he
      rcases he with he | he
      · have := a.isLt; omega
      · exact hne (Fin.ext (by omega))
  · by_contra! h
    let a : Fin n := ⟨0, by omega⟩
    obtain ⟨_, _, v, ht, _⟩ := hrow a
    have he := (hG a v).trans ht
    change (C.gates.foldl step (oneEach a v)).getD C.output false = true at he
    rw [getD_ge _ _ (by rw [len]; simpa [oneEach] using h)] at he
    contradiction

def comparable {ι κ : Type} (A : ι → κ → Bool) (a b : ι) : Prop :=
  (∀ j, A a j = true → A b j = true) ∨ (∀ j, A b j = true → A a j = true)

end Base.CircuitFacts

namespace Base.CircuitFacts
namespace Network

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

def trimGate (g : Gate) : Gate :=
  match g.op with
  | .not => ⟨.not, g.inputs.take 1⟩
  | _ => g

def trim (C : Circuit) : Circuit :=
  ⟨C.gates.map trimGate, C.output⟩

theorem trimGate_eval (g : Gate) (x : List Bool) :
    compute x (trimGate g) = compute x g := by
  cases g with
  | mk op inp =>
    cases op <;> try rfl
    cases inp <;> rfl

theorem trim_eval (C : Circuit) (x : List Bool) :
    (trim C).eval x = C.eval x := by
  have h (gs : List Gate) (v : List Bool) :
      (gs.map trimGate).foldl step v = gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, ih, step, trimGate_eval]
  change ((C.gates.map trimGate).foldl step x).getD C.output false = _
  rw [h]
  rfl

theorem trim_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (trim C) := by
  intro g hg
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨ha', hs⟩ := h a ha
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

theorem trim_unary (C : Circuit) :
    ∀ g ∈ (trim C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg he
  change g ∈ C.gates.map trimGate at hg
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hg
  rcases a with ⟨o, l⟩
  cases o <;> simp_all [trimGate]

def edgeTo (N : ℕ) (C : Circuit) (L : Finset ℕ) (w v : ℕ) : Prop :=
  ∃ j ∈ L, v = N + j ∧ before C N j w

abbrev reaches (N : ℕ) (C : Circuit) (L : Finset ℕ) :=
  Relation.ReflTransGen (edgeTo N C L)

theorem edgeIncreases {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (h : edgeTo N C L w v) : w < v := by
  obtain ⟨j, _, rfl, _, h⟩ := h
  exact h

theorem reachIncreases {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (h : reaches N C L w v) : w ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (edgeIncreases e))

def value (N : ℕ) (C : Circuit) (x : ℕ → Bool) (override : ℕ → Option Bool)
    (w : ℕ) : Bool :=
  match override w with
  | some b => b
  | none =>
    if w < N then x w
    else if w - N < C.gates.length then
      let g := gateAt C (w - N)
      g.op.eval (g.inputs.map fun u => if h : u < w then value N C x override u else false)
    else false
termination_by w

def relay (f : ℕ) (b : Bool) (w : ℕ) : Option Bool :=
  if w = f then some b else none

theorem val_raw {N : ℕ} {C : Circuit} {x : ℕ → Bool} {O : ℕ → Option Bool}
    {w : ℕ} (hw : w < N) (ho : O w = none) :
    value N C x O w = x w := by
  rw [value, ho, if_pos hw]

theorem val_gate {N : ℕ} {C : Circuit} {x : ℕ → Bool} {O : ℕ → Option Bool}
    {j : ℕ} (hj : j < C.gates.length) (ho : O (N+j) = none) :
    value N C x O (N+j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun u =>
        if u < N+j then value N C x O u else false) := by
  rw [value, ho, if_neg (by omega : ¬ N+j < N)]
  simp only [Nat.add_sub_cancel_left, if_pos hj]
  rfl

theorem val_relay (N : ℕ) (C : Circuit) (x : ℕ → Bool) (f : ℕ) (b : Bool) :
    value N C x (relay f b) f = b := by
  rw [value]
  simp [relay]

theorem val_fold (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) (w : ℕ) :
    value N C (fun i => x.getD i false) (fun _ => none) w =
      (C.gates.foldl step x).getD w false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < N
    · rw [val_raw hw rfl, pre _ _ _ (by omega)]
    · by_cases hreal : w - N < C.gates.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w-N, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [val_gate hj rfl, gate_formula C x hx hj]
        congr 1
        apply List.map_congr_left
        intro u _
        split_ifs with h
        · exact ih u h
        · rfl
      · rw [value, if_neg hw, if_neg hreal, getD_ge]
        rw [len, hx]
        omega

theorem val_original (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) :
    value N C (fun i => x.getD i false) (fun _ => none) C.output = C.eval x :=
  val_fold N C x hx C.output

def live (N : ℕ) (L : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ ∃ j ∈ L, w = N+j

theorem prev_live {N : ℕ} {C : Circuit} {L : Finset ℕ} (closedL : closed N C L)
    {j u : ℕ} (hj : j ∈ L) (hb : before C N j u) : live N L u := by
  by_cases hu : u < N
  · exact .inl hu
  · have eq : u = N + (u-N) := by omega
    right
    refine ⟨u-N, closedL.2 j hj _ ?_, eq⟩
    rwa [← eq]

theorem path_head {N : ℕ} {C : Circuit} {L : Finset ℕ} {w v : ℕ}
    (p : reaches N C L w v) (neq : w ≠ v) :
    ∃ z, edgeTo N C L w z ∧ reaches N C L z v := by
  induction p with
  | refl => exact (neq rfl).elim
  | @tail b c p e ih =>
    by_cases h : w = b
    · subst b
      exact ⟨c,e,.refl⟩
    · obtain ⟨z,hz,hp⟩ := ih h
      exact ⟨z,hz,hp.tail e⟩

theorem every_gate_reaches_root {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (cl : closed N C L) {r : ℕ}
    (next : ∀ j ∈ L, j ≠ r → ∃ k ∈ L, before C N k (N+j))
    (j : ℕ) (hj : j ∈ L) : reaches N C L (N+j) (N+r) := by
  by_cases e : j = r
  · subst j
    exact .refl
  · obtain ⟨k, hk, hb⟩ := next j hj e
    have hlt := hb.2
    have hkvalid := cl.1 k hk
    exact .head ⟨k, hk, rfl, hb⟩ (every_gate_reaches_root cl next k hk)
termination_by C.gates.length - j
decreasing_by omega

theorem value_agree {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (w : ℕ) (hw : live N L w) (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (raw : ∀ u < N, reaches N C L u w → x u = y u)
    (hOverride : ∀ u, reaches N C L u w → O u = P u) :
    value N C x O w = value N C y P w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have he := hOverride w (.refl)
    cases hO : O w with
    | some b =>
      have hP : P w = some b := he.symm.trans hO
      rw [value, hO]
      symm
      rw [value, hP]
    | none =>
      have hP : P w = none := he.symm.trans hO
      rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw hO, val_raw hw hP, raw w hw .refl]
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j, hj, rfl, hu, h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          · intro v hv p
            exact raw v hv (p.tail E)
          · intro v p
            exact hOverride v (p.tail E)
        · rfl

theorem replace_signal {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (x : ℕ → Bool) (f w : ℕ) (hw : live N L w) :
    value N C x (fun _ => none) w =
      value N C x (relay f (value N C x (fun _ => none) f)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h : w = f
    · subst w
      exact (val_relay N C x f _).symm
    · have ho : relay f (value N C x (fun _ => none) f) w = none := by simp [relay,h]
      rcases hw with hraw | ⟨j,hj,rfl⟩
      · rw [val_raw hraw ho, val_raw hraw rfl]
      · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) rfl]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · exact ih u hlt (prev_live cl hj ⟨hu,hlt⟩)
        · rfl

theorem gate_order (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (u v : ℕ → Bool) (h : ∀ i ∈ g.inputs, u i = true → v i = true) :
    g.op.eval (g.inputs.map u) = true → g.op.eval (g.inputs.map v) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hm b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact h i hi (hm _ ⟨i,hi,rfl⟩)
  · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨i,hi,rfl⟩, hb⟩
    exact ⟨v i, ⟨i,hi,rfl⟩, h i hi hb⟩

theorem value_mono {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (w : ℕ) (hw : live N L w) (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (raw : ∀ u < N, reaches N C L u w → x u = true → y u = true)
    (hOverride : ∀ u, reaches N C L u w → (O u = none ∧ P u = none) ∨
      ∃ b c, O u = some b ∧ P u = some c ∧ (b = true → c = true))
    (gates : ∀ j ∈ L, reaches N C L (N+j) w → O (N+j) = none →
      (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) :
    value N C x O w = true → value N C y P w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hOverride w .refl with ⟨hO,hP⟩ | ⟨b,c,hO,hP,hle⟩
    · rcases hw with hw | ⟨j,hj,rfl⟩
      · rw [val_raw hw hO, val_raw hw hP]
        exact raw w hw .refl
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        apply gate_order _ (gates j hj .refl hO)
        intro u hu
        split_ifs with h
        · let E : edgeTo N C L u (N+j) := ⟨j,hj,rfl,hu,h⟩
          apply ih u h (prev_live cl hj ⟨hu,h⟩)
          · intro v hv p
            exact raw v hv (p.tail E)
          · intro v p
            exact hOverride v (p.tail E)
          · intro k hk p
            exact gates k hk (p.tail E)
        · exact id
    · have hx : value N C x O w = b := by rw [value,hO]
      have hy : value N C y P w = c := by rw [value,hP]
      simpa only [hx,hy] using hle

end Network
end Base.CircuitFacts
namespace Base.CircuitFacts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def rawUsed (N : ℕ) (C : Circuit) (L : Finset ℕ) : Finset ℕ :=
  (used N C L).filter (· < N)

def missingRows (n m : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => u.val ∉ used (n+m) C L

def missingCols (n m : ℕ) (C : Circuit) (L : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun v => n + v.val ∉ used (n+m) C L

noncomputable def activeNot (C : Circuit) (L : Finset ℕ) : Finset ℕ := by
  classical
  exact L.filter fun j => (gateAt C j).op = .not

theorem closed_eval_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hL : closed N C L) (hr : r ∈ L) (ho : C.output = N+r)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (he : ∀ i ∈ used N C L, x.getD i false = y.getD i false) : C.eval x = C.eval y := by
  change (C.gates.foldl step x).getD C.output false = (C.gates.foldl step y).getD C.output false
  rw [ho]
  exact closed_values hL x y hx hy he r hr

theorem missing_rows_le {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hi : Function.Injective A) (hA : Represents A C) (hL : closed (n+m) C L)
    (hr : r ∈ L) (ho : C.output = n+m+r) : (missingRows n m C L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hui := (Finset.mem_filter.mp hu).2
  have hvi := (Finset.mem_filter.mp hv).2
  apply hi
  funext j
  rw [← hA u j, ← hA v j]
  apply closed_eval_eq hL hr ho _ _ (by simp [oneEach]) (by simp [oneEach])
  intro w hw
  rw [each_value, each_value]
  have hu' : w ≠ u.val := fun h => hui (h ▸ hw)
  have hv' : w ≠ v.val := fun h => hvi (h ▸ hw)
  simp [hu',hv']

theorem missing_cols_le {n m : ℕ} {A : Fin n → Fin m → Bool} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hi : Function.Injective (fun j i => A i j)) (hA : Represents A C) (hL : closed (n+m) C L)
    (hr : r ∈ L) (ho : C.output = n+m+r) : (missingCols n m C L).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  have hui := (Finset.mem_filter.mp hu).2
  have hvi := (Finset.mem_filter.mp hv).2
  apply hi
  funext i
  change A i u = A i v
  rw [← hA i u, ← hA i v]
  apply closed_eval_eq hL hr ho _ _ (by simp [oneEach]) (by simp [oneEach])
  intro w hw
  rw [each_value, each_value]
  have hu' : w ≠ n+u.val := fun h => hui (h ▸ hw)
  have hv' : w ≠ n+v.val := fun h => hvi (h ▸ hw)
  simp [hu',hv']

theorem input_partition (n m : ℕ) (C : Circuit) (L : Finset ℕ) :
    (rawUsed (n+m) C L).card + (missingRows n m C L).card + (missingCols n m C L).card = n+m := by
  let R := rawUsed (n+m) C L
  let A := (missingRows n m C L).image Fin.val
  let B := (missingCols n m C L).image (fun f => n+f.val)
  have hA (w : ℕ) : w ∈ A ↔ w < n ∧ w ∉ used (n+m) C L := by
    constructor
    · intro h
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp h
      exact ⟨u.isLt, (Finset.mem_filter.mp hu).2⟩
    · rintro ⟨h,hn⟩
      exact Finset.mem_image.mpr ⟨⟨w,h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩,rfl⟩
  have hB (w : ℕ) : w ∈ B ↔ n ≤ w ∧ w < n+m ∧ w ∉ used (n+m) C L := by
    constructor
    · intro h
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp h
      exact ⟨by omega, by have := v.isLt; omega, (Finset.mem_filter.mp hv).2⟩
    · rintro ⟨h,hm,hn⟩
      let v : Fin m := ⟨w - n, by omega⟩
      have he : n + v.val = w := by dsimp [v]; omega
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [he]⟩,he⟩
  have hR (w : ℕ) : w ∈ R ↔ w ∈ used (n+m) C L ∧ w < n+m := Finset.mem_filter
  have hRA : Disjoint R A := Finset.disjoint_left.mpr fun w h1 h2 => ((hA w).1 h2).2 ((hR w).1 h1).1
  have hAB : Disjoint (R ∪ A) B := by
    apply Finset.disjoint_left.mpr
    intro w h1 h2
    rcases Finset.mem_union.mp h1 with h1 | h1
    · exact ((hB w).1 h2).2.2 ((hR w).1 h1).1
    · have := ((hA w).1 h1).1
      have := ((hB w).1 h2).1
      omega
  have hp : R ∪ A ∪ B = Finset.range (n+m) := by
    ext w
    simp only [Finset.mem_union, Finset.mem_range, hR, hA, hB]
    by_cases h : w ∈ used (n+m) C L
    · simp [h]
    · simp [h]; omega
  have hcA : A.card = (missingRows n m C L).card := Finset.card_image_of_injective _ Fin.val_injective
  have hcB : B.card = (missingCols n m C L).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))
  rw [← hcA, ← hcB, ← Finset.card_union_of_disjoint hRA, ← Finset.card_union_of_disjoint hAB, hp, Finset.card_range]

theorem slots_count_low {N : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C N j (N+i)) :
    (rawUsed N C L).card + (L.card-1) ≤ (used N C L).card := by
  let I := (L.erase r).image (N + ·)
  have hdis : Disjoint (rawUsed N C L) I := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw'
    have := (Finset.mem_filter.mp hw).2
    omega
  have hsub : rawUsed N C L ∪ I ⊆ used N C L := by
    intro w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact (Finset.mem_filter.mp h).1
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hn,hm⟩ := Finset.mem_erase.mp hi
      exact mem_used.mpr (huse i hm hn)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injective _ (fun a b h => by omega),
    Finset.card_erase_of_mem hr] at hc
  exact hc

theorem slots_count_high {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) :
    (slots N C L).card + (activeNot C L).card ≤ 2*L.card := by
  classical
  have hmem (j : ℕ) (hj : j ∈ L) : gateAt C j ∈ C.gates := by
    have hb := hL.1 j hj
    rw [gateAt, List.getD_eq_getElem _ _ hb]
    exact List.getElem_mem _
  have hw (j : ℕ) : (inputSlots N C j).card ≤ (gateAt C j).inputs.length := by
    unfold inputSlots
    exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (List.toFinset_card_le _))
  have hpoint (j : ℕ) (hj : j ∈ L) :
      (inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0) ≤ 2 := by
    have hm := hmem j hj
    by_cases h : (gateAt C j).op = .not
    · have k := (hw j).trans (hNot _ hm h)
      simp [h]
      omega
    · simpa [h] using (hw j).trans (hC _ hm).2
  have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N C)
  have hn : (activeNot C L).card = ∑ j ∈ L, if (gateAt C j).op = .not then 1 else 0 := by
    unfold activeNot
    rw [Finset.card_filter]
  change (slots N C L).card ≤ ∑ j ∈ L, (inputSlots N C j).card at hslots
  have hsum : (∑ j ∈ L, ((inputSlots N C j).card + (if (gateAt C j).op = .not then 1 else 0))) ≤
      ∑ _j ∈ L, (2 : ℕ) := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, ← hn] at hsum
  calc
    _ ≤ (∑ j ∈ L, (inputSlots N C j).card) + (activeNot C L).card := Nat.add_le_add_right hslots _
    _ ≤ ∑ _j ∈ L, (2 : ℕ) := hsum
    _ = _ := by simp [Nat.mul_comm]

theorem unique_reader_of_inj {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hinj : Set.InjOn Prod.snd (slots N C L : Set (ℕ × ℕ)))
    {j k w : ℕ} (hj : j ∈ L) (hk : k ∈ L) (he : before C N j w) (hf : before C N k w) : j = k := by
  exact congrArg Prod.fst (hinj (mem_slot.mpr ⟨hj,he⟩) (mem_slot.mpr ⟨hk,hf⟩) rfl)

theorem no_not_if_full {n m : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (hL : closed (n+m) C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i))
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (hsmall : C.size ≤ n+m-1) (hrows : (missingRows n m C L).card = 0)
    (hcols : (missingCols n m C L).card = 0) :
    (activeNot C L).card = 0 ∧ L.card = C.size ∧ C.size = n+m-1 := by
  have hn := input_partition n m C L
  have hl := slots_count_low hr huse
  have hh := slots_count_high hL hC hNot
  have hm := Finset.card_image_le (s := slots (n+m) C L) (f := Prod.snd)
  change (used (n+m) C L).card ≤ (slots (n+m) C L).card at hm
  have hLf : L ⊆ Finset.range C.size := fun _ hj => Finset.mem_range.mpr (hL.1 _ hj)
  have hLc : L.card ≤ C.size := by simpa using Finset.card_le_card hLf
  have hpos := Finset.card_pos.mpr ⟨r,hr⟩
  omega

theorem collision_counts {n m : ℕ} {C : Circuit} {L : Finset ℕ} {r : ℕ}
    (hr : r ∈ L) (hL : closed (n+m) C L)
    (huse : ∀ i ∈ L, i ≠ r → ∃ j ∈ L, before C (n+m) j (n+m+i))
    (hC : FanInTwo C) (hNot : ∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1)
    (hsmall : C.size ≤ n+m-1)
    (hrows : (missingRows n m C L).card ≤ 1) (hcols : (missingCols n m C L).card ≤ 1)
    (hnpos : 0 < (activeNot C L).card)
    (hcollision : ¬ Set.InjOn Prod.snd (slots (n+m) C L : Set (ℕ × ℕ))) :
    (missingRows n m C L).card = 1 ∧ (missingCols n m C L).card = 1 ∧
    (activeNot C L).card = 1 ∧ L.card = C.size ∧ C.size = n+m-1 ∧
    (slots (n+m) C L).card = (used (n+m) C L).card+1 := by
  have hn := input_partition n m C L
  have hl := slots_count_low hr huse
  have hh := slots_count_high hL hC hNot
  have hm := Finset.card_image_le (s := slots (n+m) C L) (f := Prod.snd)
  change (used (n+m) C L).card ≤ (slots (n+m) C L).card at hm
  have hne : (used (n+m) C L).card ≠ (slots (n+m) C L).card := fun e =>
    hcollision (Finset.injOn_of_card_image_eq e)
  have hLf : L ⊆ Finset.range C.size := fun _ hj => Finset.mem_range.mpr (hL.1 _ hj)
  have hLc : L.card ≤ C.size := by simpa using Finset.card_le_card hLf
  have hpos := Finset.card_pos.mpr ⟨r,hr⟩
  omega

theorem collision_exists {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (h : ¬ Set.InjOn Prod.snd (slots N C L : Set (ℕ × ℕ))) :
    ∃ j k w : ℕ, j ∈ L ∧ k ∈ L ∧ j ≠ k ∧ before C N j w ∧ before C N k w := by
  classical
  unfold Set.InjOn at h
  push Not at h
  obtain ⟨⟨j,v⟩, hj, ⟨k,w⟩, hk, e, hn⟩ := h
  change v = w at e
  subst v
  exact ⟨j,k,w,(mem_slot.mp hj).1,(mem_slot.mp hk).1,
    fun h => hn (Prod.ext h rfl),(mem_slot.mp hj).2,(mem_slot.mp hk).2⟩

theorem unique_collision {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hc : (slots N C L).card = (used N C L).card + 1)
    {j k w : ℕ} (hj : j ∈ L) (hk : k ∈ L) (hne : j ≠ k)
    (he : before C N j w) (hf : before C N k w) :
    ∀ {a b v : ℕ}, a ∈ L → b ∈ L → a ≠ b → before C N a v → before C N b v →
      v = w ∧ ((a=j ∧ b=k) ∨ (a=k ∧ b=j)) := by
  let S := slots N C L
  have hjs : (j,w) ∈ S := mem_slot.mpr ⟨hj,he⟩
  have hks : (k,w) ∈ S := mem_slot.mpr ⟨hk,hf⟩
  have hks' : (k,w) ∈ S.erase (j,w) := Finset.mem_erase.mpr
    ⟨fun h => hne (congrArg Prod.fst h).symm, hks⟩
  have him : (S.erase (j,w)).image Prod.snd = S.image Prod.snd := by
    apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.erase_subset _ _))
    intro y hy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hy
    by_cases e : p = (j,w)
    · subst p
      exact Finset.mem_image.mpr ⟨(k,w),hks',rfl⟩
    · exact Finset.mem_image.mpr ⟨p,Finset.mem_erase.mpr ⟨e,hp⟩,rfl⟩
  have hinj : Set.InjOn Prod.snd (S.erase (j,w) : Set (ℕ × ℕ)) := by
    apply Finset.injOn_of_card_image_eq
    rw [him, Finset.card_erase_of_mem hjs]
    change (used N C L).card = (slots N C L).card-1
    omega
  intro a b v ha hb hab hav hbv
  have has : (a,v) ∈ S := mem_slot.mpr ⟨ha,hav⟩
  have hbs : (b,v) ∈ S := mem_slot.mpr ⟨hb,hbv⟩
  by_cases ea : (a,v) = (j,w)
  · obtain ⟨rfl,rfl⟩ := Prod.mk.inj ea
    have hb' : (b,v) ∈ S.erase (a,v) := Finset.mem_erase.mpr ⟨fun h => hab (congrArg Prod.fst h).symm,hbs⟩
    have q := congrArg Prod.fst (hinj hb' hks' rfl)
    exact ⟨rfl,Or.inl ⟨rfl,q⟩⟩
  · have ha' := Finset.mem_erase.mpr ⟨ea,has⟩
    by_cases eb : (b,v) = (j,w)
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eb
      have q := congrArg Prod.fst (hinj ha' hks' rfl)
      exact ⟨rfl,Or.inr ⟨q,rfl⟩⟩
    · have hb' := Finset.mem_erase.mpr ⟨eb,hbs⟩
      exact (hab (congrArg Prod.fst (hinj ha' hb' rfl))).elim

end Base.CircuitFacts
namespace Base.CircuitFacts

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover

theorem activeNot_mem {C : Circuit} {L : Finset ℕ} {j : ℕ} :
    j ∈ activeNot C L ↔ j ∈ L ∧ (gateAt C j).op = .not := by
  classical
  unfold activeNot
  exact Finset.mem_filter

theorem no_active_not_elim {C : Circuit} {L : Finset ℕ}
    (hno : (activeNot C L).card = 0) {j : ℕ} (hj : j ∈ L) : (gateAt C j).op ≠ .not := by
  intro he
  have hmem := Finset.card_pos.mpr ⟨j, activeNot_mem.mpr ⟨hj,he⟩⟩
  omega

end Base.CircuitFacts
namespace Base.CircuitFacts.Unate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Network

abbrev arc := edgeTo
abbrev Path := reaches

def Live (N : ℕ) (L : Finset ℕ) (w : ℕ) : Prop :=
  w < N ∨ ∃ j ∈ L, w = N + j

def Model (N : ℕ) (C : Circuit) (L : Finset ℕ) (skip : Option ℕ) (val : ℕ → Bool) : Prop :=
  ∀ j ∈ L, skip ≠ some (N + j) → val (N + j) =
    (gateAt C j).op.eval ((gateAt C j).inputs.map fun u => if u < N + j then val u else false)

def Changes (N i : ℕ) (skip : Option ℕ) (x y : ℕ → Bool) : Prop :=
  (∀ w < N, w ≠ i → x w = y w) ∧
    (∀ w, skip = some w → x w = y w) ∧
    (x i = true → y i = true)

def Sign (N : ℕ) (C : Circuit) (L : Finset ℕ) (skip : Option ℕ)
    (i w : ℕ) (positive : Bool) : Prop :=
  ∀ x y : ℕ → Bool, Model N C L skip x → Model N C L skip y → Changes N i skip x y →
    if positive then x w = true → y w = true else y w = true → x w = true

theorem value_is_model {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (x : ℕ → Bool) :
    Model N C L none (value N C x (fun _ => none)) := by
  intro j hj _
  exact val_gate (hL.1 j hj) rfl

theorem arc_lt {N : ℕ} {C : Circuit} {L : Finset ℕ} {x y : ℕ} :
    arc N C L x y → x < y := by
  rintro ⟨j, _, rfl, _, h⟩
  exact h

theorem path_mono {P : ℕ → ℕ → Prop} (hp : ∀ a b, P a b → a < b)
    {u v : ℕ} (h : Relation.ReflTransGen P u v) : u ≤ v := by
  induction h with
  | refl => exact le_rfl
  | tail _ he ih => exact ih.trans (hp _ _ he).le

theorem last_eq_deterministic {P : ℕ → ℕ → Prop} (hmono : ∀ a b, P a b → a < b)
    (unique : ∀ a b c, P a b → P a c → b = c)
    {s u v w : ℕ}
    (hu : Relation.ReflTransGen P s u) (hv : Relation.ReflTransGen P s v)
    (huw : P u w) (hvw : P v w) : u = v := by
  revert hv
  induction hu using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hv
    rcases hv.cases_head with hv | ⟨a, ha, hv⟩
    · exact hv
    · have h := unique _ _ _ ha huw
      subst a
      have := path_mono hmono hv
      have := hmono _ _ hvw
      omega
  | @head s a ha _ ih =>
    intro hv
    rcases hv.cases_head with rfl | ⟨b, hb, hv⟩
    · have h := unique _ _ _ ha hvw
      subst a
      have := hmono _ _ huw
      have := path_mono hmono (show Relation.ReflTransGen P w u from ‹Relation.ReflTransGen P w u›)
      omega
    · have h := unique _ _ _ ha hb
      subst b
      exact ih hv

theorem last_eq {N : ℕ} {C : Circuit} {L : Finset ℕ} {s u v w : ℕ}
    (unique : ∀ a b c, Path N C L s a → arc N C L a b → arc N C L a c → b = c)
    (hu : Path N C L s u) (hv : Path N C L s v) (huw : arc N C L u w) (hvw : arc N C L v w) :
    u = v := by
  let P := fun a b => Path N C L s a ∧ arc N C L a b
  have establish {u} (h : Path N C L s u) : Relation.ReflTransGen P s u := by
    induction h with
    | refl => exact .refl
    | tail h hc ih => exact .tail ih ⟨h, hc⟩
  exact last_eq_deterministic (fun _ _ h => arc_lt h.2)
    (fun _ _ _ h₁ h₂ => unique _ _ _ h₁.1 h₁.2 h₂.2)
    (establish hu) (establish hv) ⟨hu, huw⟩ ⟨hv, hvw⟩

theorem parent_live {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {j u : ℕ} (hj : j ∈ L) (hu : before C N j u) : Live N L u := by
  by_cases h : u < N
  · exact Or.inl h
  · have eq : u = N + (u - N) := by omega
    refine Or.inr ⟨u - N, hL.2 j hj _ ?_, eq⟩
    simpa only [← eq] using hu

theorem unchanged {N : ℕ} {C : Circuit} {L : Finset ℕ} (hL : closed N C L)
    {skip : Option ℕ} {i : ℕ} {x y : ℕ → Bool}
    (hx : Model N C L skip x) (hy : Model N C L skip y) (hc : Changes N i skip x y)
    {w : ℕ} (live : Live N L w) (away : ¬ Path N C L i w) : x w = y w := by
  revert live away
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro live away
    rcases live with low | ⟨j, hj, rfl⟩
    · exact hc.1 _ low (fun h => away (h ▸ Relation.ReflTransGen.refl))
    by_cases cut : skip = some (N + j)
    · exact hc.2.1 _ cut
    rw [hx j hj cut, hy j hj cut]
    congr 1
    apply List.map_congr_left
    intro u hu
    split_ifs with hlt
    · have e : arc N C L u (N + j) := ⟨j, hj, rfl, hu, hlt⟩
      exact ih u hlt (parent_live hL hj ⟨hu,hlt⟩) (fun hp => away (.tail hp e))
    · rfl

private theorem eval_positive (g : Gate) (op : g.op = .and ∨ g.op = .or)
    {x y : ℕ → Bool} (h : ∀ w ∈ g.inputs, x w = true → y w = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases op with op | op
  · simp only [op, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id]
    exact fun hx w hw => h w hw (hx w hw)
  · simp only [op, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    rintro ⟨w, hw, hx⟩
    exact ⟨w, hw, h w hw hx⟩

private theorem eval_negative (g : Gate) (op : g.op = .not)
    {x y : ℕ → Bool} (h : ∀ w ∈ g.inputs, x w = true → y w = true) :
    g.op.eval (g.inputs.map y) = true → g.op.eval (g.inputs.map x) = true := by
  rw [op]
  rcases eq : g.inputs with _ | ⟨w, ws⟩
  · simp [GateOp.eval]
  · have hxy := h w (by simp [eq])
    simp only [GateOp.eval, List.map_cons, List.headD_cons]
    intro hy
    cases hxx : x w
    · rfl
    · rw [hxy hxx] at hy
      cases hy

theorem fixed_polarity {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {skip : Option ℕ} {i : ℕ}
    (unique : ∀ a b c, Path N C L i a → arc N C L a b → arc N C L a c → b = c)
    {w : ℕ} (live : Live N L w) : ∃ positive : Bool, Sign N C L skip i w positive := by
  classical
  revert live
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro live
    by_cases away : ¬ Path N C L i w
    · exact ⟨true, fun x y hx hy hxy => by
        simp only [ite_true, unchanged hL hx hy hxy live away, imp_self]⟩
    rcases live with low | ⟨j, hj, rfl⟩
    · refine ⟨true, fun x y hx hy hxy => ?_⟩
      simp only [ite_true]
      by_cases h : w = i
      · simpa only [h] using hxy.2.2
      · rw [hxy.1 w low h]
        exact id
    by_cases cut : skip = some (N + j)
    · exact ⟨true, fun x y hx hy hxy => by simp only [ite_true, hxy.2.1 _ cut, imp_self]⟩
    by_cases has : ∃ u, before C N j u ∧ Path N C L i u
    · obtain ⟨u, hu, hpu⟩ := has
      obtain ⟨s, hs⟩ := ih u hu.2 (parent_live hL hj hu)
      have eq {v : ℕ} (hv : before C N j v) (hpv : Path N C L i v) : v = u :=
        last_eq unique hpv hpu ⟨j, hj, rfl, hv⟩ ⟨j, hj, rfl, hu⟩
      have mem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ (hL.1 j hj)]
        exact List.getElem_mem _
      have hop := (hC _ mem).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      let Tx (x : ℕ → Bool) v := if v < N + j then x v else false
      have directions (x y : ℕ → Bool) (hx : Model N C L skip x) (hy : Model N C L skip y)
          (hc : Changes N i skip x y) :
          (if s then ∀ v ∈ (gateAt C j).inputs, Tx x v = true → Tx y v = true
           else ∀ v ∈ (gateAt C j).inputs, Tx y v = true → Tx x v = true) := by
        have uniform := hs x y hx hy hc
        have equal (v : ℕ) (hv : before C N j v) (hv' : ¬ Path N C L i v) :
            x v = y v := unchanged hL hx hy hc (parent_live hL hj hv) hv'
        cases se : s <;> simp only [se, ite_true] at uniform ⊢
        · intro v hv
          unfold Tx
          split_ifs with hlt
          · by_cases p : Path N C L i v
            · rw [eq ⟨hv,hlt⟩ p]
              exact uniform
            · rw [equal v ⟨hv,hlt⟩ p]
              exact id
          · exact id
        · intro v hv
          unfold Tx
          split_ifs with hlt
          · by_cases p : Path N C L i v
            · rw [eq ⟨hv,hlt⟩ p]
              exact uniform
            · rw [equal v ⟨hv,hlt⟩ p]
              exact id
          · exact id
      rcases hop with ha | ho | hn
      · refine ⟨s, fun x y hx hy hc => ?_⟩
        rw [hx j hj cut, hy j hj cut]
        have hm := directions x y hx hy hc
        cases s
        · exact eval_positive _ (Or.inl ha) hm
        · exact eval_positive _ (Or.inl ha) hm
      · refine ⟨s, fun x y hx hy hc => ?_⟩
        rw [hx j hj cut, hy j hj cut]
        have hm := directions x y hx hy hc
        cases s
        · exact eval_positive _ (Or.inr ho) hm
        · exact eval_positive _ (Or.inr ho) hm
      · refine ⟨!s, fun x y hx hy hc => ?_⟩
        rw [hx j hj cut, hy j hj cut]
        have hm := directions x y hx hy hc
        cases s
        · exact eval_negative _ hn hm
        · exact eval_negative _ hn hm
    · refine ⟨true, fun x y hx hy hc => ?_⟩
      simp only [ite_true]
      have e : x (N + j) = y (N + j) := by
        rw [hx j hj cut, hy j hj cut]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · exact unchanged hL hx hy hc (parent_live hL hj ⟨hu,hlt⟩) (fun p => has ⟨_, ⟨hu,hlt⟩, p⟩)
        · rfl
      rw [e]
      exact id

theorem outside_fork_unate {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {fork skip : Option ℕ} {i : ℕ}
    (unique : ∀ a j k, fork ≠ some a → j ∈ L → k ∈ L →
      before C N j a → before C N k a → j = k)
    (away : ∀ f, fork = some f → ¬ Path N C L i f)
    {w : ℕ} (live : Live N L w) :
    ∃ positive : Bool, Sign N C L skip i w positive := by
  apply fixed_polarity hL hC _ live
  rintro a _ _ path ⟨j, hj, rfl, hb⟩ ⟨k, hk, rfl, hc⟩
  rw [unique a j k (fun h => away a h path) hj hk hb hc]

theorem value_changes {N i : ℕ} (hi : i < N) (C : Circuit) {x y : ℕ → Bool}
    (h : Changes N i none x y) :
    Changes N i none (value N C x (fun _ => none)) (value N C y (fun _ => none)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w hw hn
    rw [val_raw hw rfl, val_raw hw rfl]
    exact h.1 w hw hn
  · intro w e
    cases e
  · rw [val_raw hi rfl, val_raw hi rfl]
    exact h.2.2

theorem original_unate {N : ℕ} {C : Circuit} {L : Finset ℕ}
    (hL : closed N C L) (hC : FanInTwo C) {fork : Option ℕ} {i : ℕ} (hi : i < N)
    (unique : ∀ a j k, fork ≠ some a → j ∈ L → k ∈ L →
      before C N j a → before C N k a → j = k)
    (away : ∀ f, fork = some f → ¬ Path N C L i f)
    {w : ℕ} (live : Live N L w) :
    ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes N i none x y →
      if pos then value N C x (fun _ => none) w = true → value N C y (fun _ => none) w = true
      else value N C y (fun _ => none) w = true → value N C x (fun _ => none) w = true := by
  obtain ⟨s, hs⟩ := outside_fork_unate (skip := none) hL hC unique away live
  exact ⟨s, fun x y h =>
    hs _ _ (value_is_model hL x) (value_is_model hL y) (value_changes hi C h)⟩

theorem not_path_unused {N : ℕ} {C : Circuit} {L : Finset ℕ} {i w : ℕ}
    (unused : i ∉ used N C L) (ne : i ≠ w) : ¬ Path N C L i w := by
  intro path
  rcases path.cases_head with e | ⟨a, ⟨j, hj, _, h⟩, _⟩
  · exact ne e
  · exact unused (mem_used.mpr ⟨j,hj,h⟩)

theorem change_insert_input {N i t : ℕ} (ne : i ≠ t) :
    Changes N i none (fun k => decide (k = t)) (fun k => decide (k = i ∨ k = t)) := by
  refine ⟨?_,?_,?_⟩
  · intro k _ hk
    simp [hk]
  · intro w e
    cases e
  · simp [Ne.symm ne]

theorem omitted_row_comparable {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} {L : Finset ℕ} (rep : PEqualNP.Represents.Represents A C)
    (hL : closed (n+m) C L) (live : Live (n+m) L C.output)
    {i₀ i : Fin n} (omitted : ¬ Path (n+m) C L i₀.val C.output)
    (polarity : ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes (n+m) i.val none x y →
      if pos then value (n+m) C x (fun _ => none) C.output = true →
                   value (n+m) C y (fun _ => none) C.output = true
      else value (n+m) C y (fun _ => none) C.output = true →
           value (n+m) C x (fun _ => none) C.output = true) :
    (∀ j, A i₀ j = true → A i j = true) ∨ (∀ j, A i j = true → A i₀ j = true) := by
  have vi := i.isLt
  have vi₀ := i₀.isLt
  let bare (j : Fin m) (k : ℕ) : Bool := decide (k = n + j.val)
  let row (a : Fin n) (j : Fin m) (k : ℕ) : Bool := decide (k = a.val ∨ k = n + j.val)
  have rowEval (a : Fin n) (j : Fin m) :
      value (n+m) C (row a j) (fun _ => none) C.output = A a j := by
    let x := PEqualNP.Represents.oneEach a j
    have e : (fun k => x.getD k false) = row a j := funext (each_value a j)
    rw [← e, val_original (n+m) C x (by simp [x, PEqualNP.Represents.oneEach])]
    exact rep a j
  have bareEval (j : Fin m) :
      value (n+m) C (bare j) (fun _ => none) C.output = A i₀ j := by
    rw [← rowEval i₀ j]
    exact unchanged hL (value_is_model hL _) (value_is_model hL _)
      (value_changes (by omega) C (change_insert_input (by omega))) live omitted
  obtain ⟨sign, hs⟩ := polarity
  have relate (j : Fin m) := hs (bare j) (row i j) (change_insert_input (by omega))
  cases sign
  · right
    intro j
    rw [← rowEval i j, ← bareEval j]
    exact relate j
  · left
    intro j
    rw [← bareEval j, ← rowEval i j]
    exact relate j

theorem omitted_col_comparable {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} {L : Finset ℕ} (rep : PEqualNP.Represents.Represents A C)
    (hL : closed (n+m) C L) (live : Live (n+m) L C.output)
    {j₀ j : Fin m} (omitted : ¬ Path (n+m) C L (n+j₀.val) C.output)
    (polarity : ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes (n+m) (n+j.val) none x y →
      if pos then value (n+m) C x (fun _ => none) C.output = true →
                   value (n+m) C y (fun _ => none) C.output = true
      else value (n+m) C y (fun _ => none) C.output = true →
           value (n+m) C x (fun _ => none) C.output = true) :
    (∀ i, A i j₀ = true → A i j = true) ∨ (∀ i, A i j = true → A i j₀ = true) := by
  have vj := j.isLt
  have vj₀ := j₀.isLt
  let bare (i : Fin n) (k : ℕ) : Bool := decide (k = i.val)
  let col (i : Fin n) (a : Fin m) (k : ℕ) : Bool := decide (k = n + a.val ∨ k = i.val)
  have colEval (i : Fin n) (a : Fin m) :
      value (n+m) C (col i a) (fun _ => none) C.output = A i a := by
    let x := PEqualNP.Represents.oneEach i a
    have e : (fun k => x.getD k false) = col i a := by
      funext k
      rw [each_value]
      simp only [col, or_comm]
    rw [← e, val_original (n+m) C x (by simp [x, PEqualNP.Represents.oneEach])]
    exact rep i a
  have bareEval (i : Fin n) :
      value (n+m) C (bare i) (fun _ => none) C.output = A i j₀ := by
    have vi := i.isLt
    rw [← colEval i j₀]
    exact unchanged hL (value_is_model hL _) (value_is_model hL _)
      (value_changes (by omega) C (change_insert_input (by omega))) live omitted
  obtain ⟨sign, hs⟩ := polarity
  have relate (i : Fin n) := hs (bare i) (col i j) (change_insert_input (by have := i.isLt; omega))
  cases sign
  · right
    intro i
    rw [← colEval i j, ← bareEval i]
    exact relate i
  · left
    intro i
    rw [← bareEval i, ← colEval i j]
    exact relate i

end Base.CircuitFacts.Unate

namespace Base.ConeFacts

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

def RG (n : ℕ) (gs : List Gate) (i j : ℕ) : Prop :=
  j < gs.length ∧ i < j ∧ n + i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs

theorem tg_last {α : Type} {R : α → α → Prop} {a b : α} (h : Relation.TransGen R a b) :
    ∃ c, R c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

theorem cones_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, coneStep, List.length_append,
      List.length_cons, List.length_nil]; omega

theorem RG_snoc (n : ℕ) (gs : List Gate) (g : Gate) (a b : ℕ) (hb : b < gs.length) :
    RG n (gs ++ [g]) a b ↔ RG n gs a b := by
  unfold RG
  have : (gs ++ [g]).getD b ⟨GateOp.or, []⟩ = gs.getD b ⟨GateOp.or, []⟩ := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hb]
  rw [this]
  simp only [List.length_append, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨_, h2, h3⟩; exact ⟨hb, h2, h3⟩
  · rintro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩

theorem tg_snoc (n : ℕ) (gs : List Gate) (g : Gate) (i j : ℕ) (hj : j < gs.length) :
    Relation.TransGen (RG n (gs ++ [g])) i j ↔ Relation.TransGen (RG n gs) i j := by
  constructor
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ hj).mp h)
    | @tail b c _ hbc ih =>
      have hb : b < gs.length := by have := hbc.2.1; omega
      exact Relation.TransGen.tail (ih hb) ((RG_snoc n gs g _ _ hj).mp hbc)
  · intro h
    induction h with
    | single h => exact Relation.TransGen.single ((RG_snoc n gs g _ _ h.1).mpr h)
    | tail _ hbc ih => exact Relation.TransGen.tail (ih (lt_trans hbc.2.1 hbc.1)) ((RG_snoc n gs g _ _ hbc.1).mpr hbc)

theorem cone_list (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔ Relation.TransGen (RG n gs) i j := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i j
    simp only [List.foldl_nil, List.getD_nil, List.not_mem_nil, false_iff]
    intro h
    obtain ⟨c, hc⟩ := tg_last h
    exact absurd hc.1 (by simp)
  | append_singleton gs g ih =>
    intro i j
    have hL := cones_length n gs []
    simp only [List.length_nil, Nat.zero_add] at hL
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    set cs := gs.foldl (coneStep n) [] with hcs
    rcases Nat.lt_trichotomy j gs.length with h1 | h1 | h1
    · rw [tg_snoc n gs g i j h1, ← ih i j]
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · subst h1
      have hget : (coneStep n cs g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
            (fun w => (w - n) :: cs.getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hL]
      rw [hget, hL]
      have hRL : ∀ c, RG n (gs ++ [g]) c gs.length ↔ c < gs.length ∧ n + c ∈ g.inputs := by
        intro c
        unfold RG
        have : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
          simp [List.getD_eq_getElem?_getD]
        rw [this]
        simp
      simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · rintro ⟨w, ⟨hw, hw1, hw2⟩, hi | hi⟩
        · apply Relation.TransGen.single
          rw [hRL]
          refine ⟨by omega, ?_⟩
          have : n + i = w := by omega
          rw [this]; exact hw
        · have h2 := (ih i (w - n)).mp hi
          rw [← tg_snoc n gs g i (w - n) (by omega)] at h2
          refine Relation.TransGen.tail h2 ((hRL _).mpr ⟨by omega, ?_⟩)
          have : n + (w - n) = w := by omega
          rw [this]; exact hw
      · intro h
        cases h with
        | single h =>
          obtain ⟨hc, hm⟩ := (hRL i).mp h
          exact ⟨n + i, ⟨hm, by omega, by omega⟩, Or.inl (by omega)⟩
        | @tail c _ hic hc =>
          obtain ⟨hc1, hm⟩ := (hRL c).mp hc
          refine ⟨n + c, ⟨hm, by omega, by omega⟩, Or.inr ?_⟩
          have : n + c - n = c := by omega
          rw [this, ih]
          exact (tg_snoc n gs g i c hc1).mp hic
    · have hnil : (coneStep n cs g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [hnil]
      simp only [List.not_mem_nil, false_iff]
      intro h
      obtain ⟨c, hc⟩ := tg_last h
      have := hc.1
      simp at this
      omega

def RR (n : ℕ) (C : Circuit) (i j : ℕ) : Prop :=
  j < C.gates.length ∧ i < j ∧ n + i ∈ (gateAt C j).inputs

theorem cone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ Relation.TransGen (RR n C) i j := by
  unfold InCone cones
  rw [cone_list n C.gates i j]
  rfl

end Base.ConeFacts

namespace Base
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open Base.CircuitFacts
open Base.CircuitFacts.Network
open Base.CircuitFacts.Unate (Changes Path)

theorem witnesses {ι κ : Type} (A : ι → κ → Bool)
    (h : ∀ i, ∃ k, ¬ comparable A i k) (i : ι) :
    ∃ k, k ≠ i ∧ ∃ j, A i j = true ∧ A k j = false := by
  obtain ⟨k, hn⟩ := h i
  refine ⟨k, fun e => hn (e ▸ Or.inl (fun _ h => h)), ?_⟩
  by_contra! hz
  apply hn
  left
  intro j hj
  cases he : A k j
  · exact False.elim (hz j hj he)
  · rfl

theorem trimmedWires (C : Circuit) (x : List Bool) :
    (Network.trim C).wires x = C.wires x := by
  have h (gs : List Gate) (v : List Bool) :
      (gs.map trimGate).foldl step v = gs.foldl step v := by
    induction gs generalizing v with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, ih, step, trimGate_eval]
  exact h C.gates x

theorem trimGateAt (C : Circuit) (j : ℕ) (hj : j < C.size) :
    gateAt (Network.trim C) j = trimGate (gateAt C j) := by
  have ht : j < (Network.trim C).gates.length := by simpa [Network.trim, Circuit.size] using hj
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ ht]
  exact List.getElem_map _

theorem fullSlots [DecidableEq GateOp] {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    (fan : FanInTwo D) (unary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1)
    (sat : (slots N D L).card + (activeNot D L).card = 2 * L.card) :
    ∀ j ∈ L, (gateAt D j).inputs.length = (if (gateAt D j).op = .not then 1 else 2) ∧
      (gateAt D j).inputs.Nodup ∧ ∀ w ∈ (gateAt D j).inputs, w < N + j := by
  classical
  let cost (j : ℕ) := (inputSlots N D j).card + (if (gateAt D j).op = .not then 1 else 0)
  have bound (j) (hj : j ∈ L) :
      (gateAt D j).inputs.length ≤ (if (gateAt D j).op = .not then 1 else 2) := by
    have mem : gateAt D j ∈ D.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ (cl.1 j hj)]
      exact List.getElem_mem _
    split_ifs with h
    · exact unary _ mem h
    · exact (fan _ mem).2
  have count (j : ℕ) : (inputSlots N D j).card ≤ (gateAt D j).inputs.length := by
    rw [inputSlots_card]
    exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
  have costLe (j) (hj : j ∈ L) : cost j ≤ 2 := by
    have hh := bound j hj
    have hc := count j
    by_cases h : (gateAt D j).op = .not <;> simp [cost, h] at * <;> omega
  have sumLo : 2 * L.card ≤ ∑ j ∈ L, cost j := by
    have hslots := Finset.card_biUnion_le (s := L) (t := inputSlots N D)
    change (slots N D L).card ≤ _ at hslots
    have hn : (activeNot D L).card = ∑ j ∈ L, if (gateAt D j).op = .not then 1 else 0 := by
      unfold activeNot
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : (gateAt D a).op = .not <;> simp [h]
    simpa only [cost, Finset.sum_add_distrib, ← hn, ← sat] using
      Nat.add_le_add_right hslots (activeNot D L).card
  intro j hj
  have splitSum := Finset.sum_erase_add L cost hj
  have eraseBound : ∑ k ∈ L.erase j, cost k ≤ (L.erase j).card * 2 := by
    simpa using Finset.sum_le_sum (s := L.erase j)
      (fun k hk => costLe k (Finset.mem_of_mem_erase hk))
  rw [Finset.card_erase_of_mem hj] at eraseBound
  have pos := Finset.card_pos.mpr ⟨j,hj⟩
  have eqCost : cost j = 2 := by have := costLe j hj; omega
  have filled : (inputSlots N D j).card =
      (if (gateAt D j).op = .not then 1 else 2) := by
    change (inputSlots N D j).card + (if (gateAt D j).op = .not then 1 else 0) = 2 at eqCost
    by_cases h : (gateAt D j).op = .not <;> simp [h] at eqCost ⊢ <;> omega
  have len := Nat.le_antisymm (bound j hj) (filled ▸ count j)
  have equality := filled.trans len.symm
  let S := (gateAt D j).inputs.toFinset
  rw [inputSlots_card] at equality
  change (S.filter (· < N + j)).card = (gateAt D j).inputs.length at equality
  have lo := Finset.card_le_card (Finset.filter_subset (· < N + j) S)
  have hi := List.toFinset_card_le (gateAt D j).inputs
  change S.card ≤ _ at hi
  have all : S.filter (· < N + j) = S :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have nodup : (gateAt D j).inputs.Nodup := by
    exact Multiset.toFinset_card_eq_card_iff_nodup (m := ((gateAt D j).inputs : Multiset ℕ)) |>.mp (by
      change S.card = (gateAt D j).inputs.length
      omega)
  refine ⟨len, nodup, ?_⟩
  intro w hw
  have hmem : w ∈ S := List.mem_toFinset.mpr hw
  rw [← all] at hmem
  exact (Finset.mem_filter.mp hmem).2

theorem used_has_reader {N : ℕ} {D : Circuit} {L : Finset ℕ} (back : ReadsBack N D)
    (valid : ∀ j ∈ L, j < D.size) (w : ℕ) :
    w ∈ used N D L ↔ ∃ j ∈ L, w ∈ (gateAt D j).inputs := by
  rw [mem_used]
  exact ⟨fun ⟨j,hj,hm,_⟩ => ⟨j,hj,hm⟩, fun ⟨j,hj,hm⟩ => ⟨j,hj,hm,back j (valid j hj) w hm⟩⟩

theorem reads_card (D : Circuit) (L : Finset ℕ) (w : ℕ)
    (nodup : ∀ j ∈ L, (gateAt D j).inputs.Nodup) :
    readsIn D L w = (L.filter fun j => w ∈ (gateAt D j).inputs).card := by
  rw [readsIn, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : w ∈ (gateAt D j).inputs
  · simp only [h, ite_true]
    have lo := List.count_pos_iff.mpr h
    have hi := List.nodup_iff_count_le_one.mp (nodup j hj) w
    omega
  · simpa [h] using List.count_eq_zero.mpr h

theorem gateReach {N : ℕ} {D : Circuit} {L : Finset ℕ}
    (full : L = Finset.range D.size) (a b : ℕ) :
    reaches N D L (N+a) (N+b) ↔ a = b ∨ PEqualNP.EdgeOwnership.InCone N D a b := by
  rw [Base.ConeFacts.cone_iff]
  have arc {i j : ℕ} : edgeTo N D L (N+i) (N+j) ↔ Base.ConeFacts.RR N D i j := by
    constructor
    · rintro ⟨k,hk,e,hm,lt⟩
      have he : j = k := by omega
      subst k
      exact ⟨Finset.mem_range.mp (full ▸ hk), by omega, hm⟩
    · rintro ⟨hj,hij,hm⟩
      exact ⟨j,full.symm ▸ Finset.mem_range.mpr hj,rfl,hm,by omega⟩
  constructor
  · intro p
    have lift {v : ℕ} (p : reaches N D L (N+a) v) :
        ∃ j, v = N+j ∧ (a = j ∨ Relation.TransGen (Base.ConeFacts.RR N D) a j) := by
      induction p with
      | refl => exact ⟨a,rfl,Or.inl rfl⟩
      | tail _ he ih =>
        obtain ⟨i,rfl,hi⟩ := ih
        obtain ⟨j,hj,rfl,hm,lt⟩ := he
        have edge := arc.mp ⟨j,hj,rfl,hm,lt⟩
        exact ⟨j,rfl,hi.elim (fun e => Or.inr (.single (e ▸ edge))) (fun p => Or.inr (.tail p edge))⟩
    obtain ⟨j,e,hj⟩ := lift p
    have eq : b = j := by omega
    exact eq ▸ hj
  · rintro (rfl | p)
    · exact .refl
    · induction p with
      | single he => exact .single (arc.mpr he)
      | tail _ he ih => exact .tail ih (arc.mpr he)

theorem sameCut {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    (stop : ℕ) (noLeak : ∀ a b, a ≠ stop → edgeTo N D L a b → reaches N D L a stop →
      reaches N D L b stop)
    (b : Bool) (x y : ℕ → Bool)
    (raw : ∀ u < N, ¬ reaches N D L u stop → x u = y u)
    (w : ℕ) (hw : live N L w) (out : w = stop ∨ ¬ reaches N D L w stop) :
    value N D x (relay stop b) w = value N D y (relay stop b) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases out with rfl | out
    · rw [val_relay, val_relay]
    have ne : w ≠ stop := fun e => out (e ▸ .refl)
    have ho : relay stop b w = none := by simp [relay, ne]
    rcases hw with hw | ⟨j,hj,rfl⟩
    · rw [val_raw hw ho, val_raw hw ho, raw w hw out]
    · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) ho]
      congr 1
      apply List.map_congr_left
      intro u hu
      split_ifs with h
      · apply ih u h (prev_live cl hj ⟨hu,h⟩)
        by_cases ef : u = stop
        · exact .inl ef
        · exact .inr (fun p => out (noLeak u _ ef ⟨j,hj,rfl,hu,h⟩ p))
      · rfl

theorem orderCut {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    {t w : ℕ} (hw : live N L w)
    (ops : ∀ j ∈ L, j ≠ t → (gateAt D j).op = .and ∨ (gateAt D j).op = .or)
    {x y : ℕ → Bool} {b c : Bool}
    (raw : ∀ u < N, x u = true → y u = true) (hbc : b = true → c = true) :
    value N D x (relay (N+t) b) w = true → value N D y (relay (N+t) c) w = true := by
  apply value_mono cl w hw _ _ _ _ (fun u hu _ => raw u hu)
  · intro u _
    by_cases eq : u = N + t
    · exact Or.inr ⟨b,c,by simp [relay,eq],by simp [relay,eq],hbc⟩
    · exact Or.inl ⟨by simp [relay,eq],by simp [relay,eq]⟩
  · intro j hj _ hnone
    apply ops j hj
    rintro rfl
    simp [relay] at hnone

theorem unateWithClosedNot {N : ℕ} {D : Circuit} {L : Finset ℕ} (cl : closed N D L)
    {t u w i : ℕ} (ht : t ∈ L) (hu : before D N t u) (htail : (gateAt D t).inputs = [u])
    (hnot : (gateAt D t).op = .not) (hw : live N L w) (htw : N + t ≤ w)
    (ops : ∀ j ∈ L, j ≠ t → (gateAt D j).op = .and ∨ (gateAt D j).op = .or)
    (noLeak : ∀ a b, a ≠ N+t → edgeTo N D L a b → reaches N D L a (N+t) →
      reaches N D L b (N+t)) :
    ∃ pos : Bool, ∀ x y : ℕ → Bool, Changes N i none x y →
      if pos then value N D x (fun _ => none) w = true → value N D y (fun _ => none) w = true
      else value N D y (fun _ => none) w = true → value N D x (fun _ => none) w = true := by
  classical
  let V (x : ℕ → Bool) := value N D x (fun _ => none)
  have act (x : ℕ → Bool) : V x (N+t) = ! V x u := by
    dsimp only [V]
    rw [val_gate (cl.1 t ht) rfl, hnot, htail]
    simp [GateOp.eval, hu.2]
  have orient (x y : ℕ → Bool) (h : Changes N i none x y) :
      ∀ a < N, x a = true → y a = true := by
    intro a ha
    by_cases e : a = i
    · subst a
      exact h.2.2
    · rw [h.1 a ha e]
      exact id
  by_cases reach : reaches N D L i (N+t)
  · refine ⟨false, fun x y h => ?_⟩
    change V y w = true → V x w = true
    have up : V x u = true → V y u = true := by
      apply value_mono cl u (prev_live cl ht hu) _ _ _ _ (fun a ha _ => orient x y h a ha)
        (fun _ _ => Or.inl ⟨rfl,rfl⟩)
      intro j hj p _
      have hlt := reachIncreases p
      have huLt := hu.2
      exact ops j hj (by omega)
    have down : V y (N+t) = true → V x (N+t) = true := by
      rw [act, act]
      cases hx : V x u <;> cases hy : V y u <;> simp_all
    have eq : value N D y (relay (N+t) (V y (N+t))) w =
        value N D x (relay (N+t) (V y (N+t))) w := by
      refine sameCut cl (N+t) noLeak (V y (N+t)) y x ?_ w hw ?_
      · intro a ha away
        exact (h.1 a ha (fun e => away (e ▸ reach))).symm
      · by_cases e : w = N+t
        · exact Or.inl e
        · exact Or.inr (fun p => e (by have := reachIncreases p; omega))
    dsimp only [V] at eq ⊢
    rw [replace_signal cl y (N+t) w hw, replace_signal cl x (N+t) w hw, eq]
    exact orderCut cl hw ops (fun _ _ => id) down
  · refine ⟨true, fun x y h => ?_⟩
    change V x w = true → V y w = true
    have eq : V x (N+t) = V y (N+t) := by
      apply value_agree cl (N+t) (Or.inr ⟨t,ht,rfl⟩)
      · intro a ha p
        exact h.1 a ha (fun e => reach (e ▸ p))
      · intro a _
        rfl
    dsimp only [V] at eq ⊢
    rw [replace_signal cl x (N+t) w hw, replace_signal cl y (N+t) w hw, eq]
    exact orderCut cl hw ops (orient x y h) id

theorem trimReads {C : Circuit} {t : ℕ} (ht : t < C.size)
    (only : ∀ j < C.size, (gateAt (Network.trim C) j).op = .not ↔ j = t)
    (w : ℕ) :
    readsIn C (Finset.range C.size) w =
      readsIn (Network.trim C) (Finset.range (Network.trim C).size) w +
        ((gateAt C t).inputs.drop 1).count w := by
  have sizes : (Network.trim C).size = C.size := by simp [Network.trim, Circuit.size]
  rw [sizes, readsIn, readsIn]
  let tailCount := ((gateAt C t).inputs.drop 1).count w
  have takeCount (j : ℕ) (hj : j ∈ Finset.range C.size) :
      (gateAt C j).inputs.count w =
        (gateAt (Network.trim C) j).inputs.count w + if j = t then tailCount else 0 := by
    have hj' := Finset.mem_range.mp hj
    have op : (trimGate (gateAt C j)).op = (gateAt C j).op := by
      cases h : (gateAt C j).op <;> simp [trimGate,h]
    have only' : (gateAt C j).op = .not ↔ j = t := by
      simpa only [trimGateAt C j hj', op] using only j hj'
    rw [trimGateAt C j hj']
    by_cases e : j = t
    · have h := only'.mpr e
      subst j
      simp only [trimGate,h,tailCount]
      nth_rw 1 [← List.take_append_drop 1 (gateAt C t).inputs]
      exact List.count_append
    · have ne := fun h => e (only'.mp h)
      cases h : (gateAt C j).op <;> simp_all [trimGate]
  calc
    _ = ∑ j ∈ Finset.range C.size,
        ((gateAt (Network.trim C) j).inputs.count w + if j = t then tailCount else 0) :=
      Finset.sum_congr rfl takeCount
    _ = _ := by rw [Finset.sum_add_distrib]; simp [ht, tailCount]

end Base

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open Base.CircuitFacts
open Base.CircuitFacts.Network
open Base.CircuitFacts.Unate (Changes Path)
open Base

theorem struct_29755 : (∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  C.size ≤ n + m - 1 →
  (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
  letI : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  let N := n+m
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map (fun g =>
    if g.op = PEqualNP.CircuitLowerBounds.GateOp.not then ⟨g.op,g.inputs.take 1⟩ else g), C.output⟩
  let atGate := PEqualNP.MetaComplexity.NestedCover.gateAt D
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size)
  (∀ xs : List Bool, D.wires xs = C.wires xs) ∧
  C.size = N-1 ∧ D.output+1 = N+D.size ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N D ∧
  (∀ g ∈ D.gates, ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) ∧
  ∃ (r : Fin n) (c : Fin m) (f t : Fin D.size), f < t ∧
    (∀ j : Fin D.size, (atGate j.val).op = PEqualNP.CircuitLowerBounds.GateOp.not ↔ j = t) ∧
    (∀ i : Fin n, reads i.val = if i = r then 0 else 1) ∧
    (∀ j : Fin m, reads (n+j.val) = if j = c then 0 else 1) ∧
    (∀ j : Fin D.size, reads (N+j.val) =
      if j = f then 2 else if j.val+1 = D.size then 0 else 1) ∧
    PEqualNP.EdgeOwnership.InCone N D f.val t.val ∧
    PEqualNP.MetaComplexity.NestedCover.readsIn D (insert t.val (((PEqualNP.EdgeOwnership.cones N D).getD t.val []).toFinset)) (N+f.val) = 1 ∧
    ∀ w : Nat, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w =
      reads w + (((PEqualNP.MetaComplexity.NestedCover.gateAt C t.val).inputs.drop 1).count w)) := by
  classical
  intro n m A hn hm
  dsimp only
  intro hi hj ri ci C fan rep small hnC
  let N := n+m
  let D := Network.trim C
  letI : DecidableEq GateOp := gateOpDecEq
  have dEq : D = ⟨C.gates.map (fun g =>
      if g.op = GateOp.not then ⟨g.op,g.inputs.take 1⟩ else g), C.output⟩ := by
    have emap : trimGate = (fun g : Gate =>
        if g.op = GateOp.not then ⟨g.op,g.inputs.take 1⟩ else g) := by
      funext g
      cases g with
      | mk op inp => cases op <;> simp [trimGate]
    change Circuit.mk (C.gates.map trimGate) C.output = _
    rw [emap]
  let goal (E : Circuit) : Prop :=
    let reads := readsIn E (Finset.range E.size)
    (∀ xs : List Bool, E.wires xs = C.wires xs) ∧
    C.size = N-1 ∧ E.output+1 = N+E.size ∧ ReadsBack N E ∧
    (∀ g ∈ E.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧
    ∃ (r : Fin n) (c : Fin m) (f t : Fin E.size), f < t ∧
      (∀ j : Fin E.size, (gateAt E j.val).op = .not ↔ j = t) ∧
      (∀ i : Fin n, reads i.val = if i = r then 0 else 1) ∧
      (∀ j : Fin m, reads (n+j.val) = if j = c then 0 else 1) ∧
      (∀ j : Fin E.size, reads (N+j.val) =
        if j = f then 2 else if j.val+1 = E.size then 0 else 1) ∧
      PEqualNP.EdgeOwnership.InCone N E f.val t.val ∧
      readsIn E (insert t.val (((PEqualNP.EdgeOwnership.cones N E).getD t.val []).toFinset)) (N+f.val) = 1 ∧
      ∀ w : Nat, readsIn C (Finset.range C.size) w =
        reads w + (((gateAt C t.val).inputs.drop 1).count w)
  change goal _
  rw [← dEq]
  dsimp only [goal]
  have sizeD : D.size = C.size := by simp [D, Network.trim, Circuit.size]
  have dfan : FanInTwo D := trim_fan C fan
  have dunary : ∀ g ∈ D.gates, g.op = .not → g.inputs.length ≤ 1 := trim_unary C
  have drep : Represents A D := fun i j => (trim_eval C (oneEach i j)).trans (rep i j)
  have dsmall : D.size ≤ N - 1 := sizeD.trans_le small
  have dnot : ∃ g ∈ D.gates, g.op = GateOp.not := by
    obtain ⟨g,hg,hnot⟩ := hnC
    refine ⟨trimGate g, List.mem_map.mpr ⟨g,hg,rfl⟩, ?_⟩
    simp [trimGate,hnot]
  obtain ⟨outlo,outhi⟩ := root_bounds (by omega) (witnesses A ri)
    (witnesses (fun j i => A i j) ci) D drep
  let o := D.output - N
  have outEq : D.output = N+o := by dsimp [o,N]; omega
  have oLt : o < D.size := by dsimp [o,N,Circuit.size]; omega
  obtain ⟨L,ho,closedL,next⟩ := minimal_closed N D o oLt
  have liveOut : Network.live N L D.output := Or.inr ⟨o,ho,outEq⟩
  have nout : N ≤ D.output := outlo
  have rowLe := missing_rows_le hi drep closedL ho outEq
  have colLe := missing_cols_le hj drep closedL ho outEq
  have gmem (k : ℕ) (hk : k < D.size) : gateAt D k ∈ D.gates := by
    rw [gateAt,List.getD_eq_getElem _ _ hk]
    exact List.getElem_mem _
  have ops (k : ℕ) (hk : k ∈ L) (ne : (gateAt D k).op ≠ .not) :
      (gateAt D k).op = .and ∨ (gateAt D k).op = .or := by
    have h := (dfan _ (gmem k (closedL.1 k hk))).1
    simpa [Set.mem_insert_iff, ne] using h
  have needed (polarity : ∀ i < N, ∃ pos : Bool, ∀ x y : ℕ → Bool,
      Changes N i none x y →
      if pos then value N D x (fun _ => none) D.output = true →
                    value N D y (fun _ => none) D.output = true
      else value N D y (fun _ => none) D.output = true →
           value N D x (fun _ => none) D.output = true) :
      (missingRows n m D L).card = 0 ∧ (missingCols n m D L).card = 0 := by
    constructor
    · by_contra hne
      obtain ⟨r,hr⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      have unused := (Finset.mem_filter.mp hr).2
      have out := Unate.not_path_unused (w := D.output) unused (by
        have := r.isLt
        dsimp [N] at nout
        omega)
      obtain ⟨k,hk⟩ := ri r
      exact hk (Unate.omitted_row_comparable drep closedL liveOut out
        (polarity k.val (by have := k.isLt; dsimp [N]; omega)))
    · by_contra hne
      obtain ⟨c,hc⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      have unused := (Finset.mem_filter.mp hc).2
      have out := Unate.not_path_unused (w := D.output) unused (by
        have := c.isLt
        dsimp [N] at nout
        omega)
      obtain ⟨k,hk⟩ := ci c
      exact hk (Unate.omitted_col_comparable drep closedL liveOut out
        (polarity (n+k.val) (by have := k.isLt; dsimp [N]; omega)))
  have anyFullHasNot (full : L = Finset.range D.size) : 0 < (activeNot D L).card := by
    obtain ⟨g,hg,hnot⟩ := dnot
    obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hg
    refine Finset.card_pos.mpr ⟨k, activeNot_mem.mpr ⟨full.symm ▸ Finset.mem_range.mpr hk, ?_⟩⟩
    rw [gateAt,List.getD_eq_getElem _ _ hk,he,hnot]
  have activePos : 0 < (activeNot D L).card := by
    by_contra! hno
    have zero : (activeNot D L).card = 0 := by omega
    obtain ⟨r0,c0⟩ := needed (by
      intro i _
      refine ⟨true, fun x y changeXY => ?_⟩
      simp only [ite_true]
      apply value_mono closedL _ liveOut _ _ _ _ _ (fun _ _ => Or.inl ⟨rfl,rfl⟩)
        (fun j h _ _ => ops j h (no_active_not_elim zero h))
      intro w hw _
      by_cases e : w = i
      · subst w
        exact changeXY.2.2
      · rw [changeXY.1 w hw e]
        exact id)
    obtain ⟨_,sz,_⟩ := no_not_if_full ho closedL next dfan dunary dsmall r0 c0
    have full : L = Finset.range D.size :=
      Finset.eq_of_subset_of_card_le (fun k hk => Finset.mem_range.mpr (closedL.1 k hk))
        (by simp [sz])
    exact (Nat.not_lt_of_ge hno) (anyFullHasNot full)
  have collision : ¬ Set.InjOn Prod.snd (slots N D L : Set (ℕ × ℕ)) := by
    intro injective
    obtain ⟨r0,c0⟩ := needed (by
      intro i hilt
      exact Unate.original_unate (fork := none) closedL dfan hilt
        (fun _ _ _ _ hp hq h1 h2 => unique_reader_of_inj injective hp hq h1 h2)
        (fun _ h => by cases h) liveOut)
    have h0 := (no_not_if_full ho closedL next dfan dunary dsmall r0 c0).1
    omega
  obtain ⟨row1,col1,not1,lSize,tight,slots1⟩ :=
    collision_counts ho closedL next dfan dunary dsmall rowLe colLe activePos collision
  have full : L = Finset.range D.size :=
    Finset.eq_of_subset_of_card_le (fun k hk => Finset.mem_range.mpr (closedL.1 k hk))
      (by simp [lSize])
  have arity := fullSlots closedL dfan dunary (by
    have hpar : (rawUsed N D L).card + (missingRows n m D L).card +
        (missingCols n m D L).card = N := input_partition n m D L
    have hlo : (rawUsed N D L).card + (L.card-1) ≤ (used N D L).card :=
      slots_count_low ho next
    have hhi : (slots N D L).card + (activeNot D L).card ≤ 2*L.card :=
      slots_count_high closedL dfan dunary
    have hs : (slots N D L).card = (used N D L).card+1 := slots1
    have lc : L.card = N-1 := lSize.trans tight
    have hp := Finset.card_pos.mpr ⟨o,ho⟩
    omega)
  have back : ReadsBack N D :=
    fun k hk => (arity k (full.symm ▸ Finset.mem_range.mpr hk)).2.2
  obtain ⟨j,k,f,hjL,hkL,hjk,hjf,hkf⟩ := collision_exists collision
  have forkOnly (a p q : ℕ) (ha : a ≠ f) (hp : p ∈ L) (hq : q ∈ L)
      (h1 : before D N p a) (h2 : before D N q a) : p = q := by
    by_contra hne
    exact ha (unique_collision slots1 hjL hkL hjk hjf hkf hp hq hne h1 h2).1
  obtain ⟨t,htEq⟩ := Finset.card_eq_one.mp not1
  have htL : t ∈ L := (activeNot_mem.mp (htEq.symm ▸ Finset.mem_singleton_self t)).1
  have only (j : ℕ) (hj : j ∈ L) : (gateAt D j).op = .not ↔ j = t := by
    have eq := activeNot_mem (C := D) (L := L) (j := j)
    rw [htEq,Finset.mem_singleton] at eq
    exact ⟨fun h => eq.mpr ⟨hj,h⟩, fun h => (eq.mp h).2⟩
  have htNot := (only t htL).mpr rfl
  obtain ⟨u,huList⟩ := List.length_eq_one_iff.mp (by simpa [htNot] using (arity t htL).1)
  have huMem : u ∈ (gateAt D t).inputs := by simp [huList]
  have hu : before D N t u := ⟨huMem,(arity t htL).2.2 u huMem⟩
  obtain ⟨r,hrEq⟩ := Finset.card_eq_one.mp row1
  obtain ⟨c,hcEq⟩ := Finset.card_eq_one.mp col1
  have rowUnused (i : Fin n) : i.val ∉ used N D L ↔ i = r := by
    change i.val ∉ used (n+m) D L ↔ i = r
    rw [← Finset.mem_singleton, ← hrEq]
    simp [missingRows]
  have colUnused (i : Fin m) : n+i.val ∉ used N D L ↔ i = c := by
    change n+i.val ∉ used (n+m) D L ↔ i = c
    rw [← Finset.mem_singleton, ← hcEq]
    simp [missingCols]
  have badRow : ¬ Path N D L r.val D.output := Unate.not_path_unused ((rowUnused r).mpr rfl)
    (by have := r.isLt; dsimp [N] at nout; omega)
  have badCol : ¬ Path N D L (n+c.val) D.output := Unate.not_path_unused ((colUnused c).mpr rfl)
    (by have := c.isLt; dsimp [N] at nout; omega)
  obtain ⟨i,hiBad⟩ := ri r
  obtain ⟨v,hvBad⟩ := ci c
  have signsAway (a : ℕ) (ha : a < N) (away : ¬ Path N D L a f) :=
    Unate.original_unate (fork := some f) closedL dfan ha
      (fun a p q hs => forkOnly a p q (fun h => hs (congrArg some h.symm)))
      (fun g h => by have e := Option.some.inj h; simpa only [← e] using away) liveOut
  have rowFork : Path N D L i.val f := by
    by_contra p
    exact hiBad (Unate.omitted_row_comparable drep closedL liveOut badRow
      (signsAway i.val (by have := i.isLt; dsimp [N]; omega) p))
  have colFork : Path N D L (n+v.val) f := by
    by_contra p
    exact hvBad (Unate.omitted_col_comparable drep closedL liveOut badCol
      (signsAway (n+v.val) (by have := v.isLt; dsimp [N]; omega) p))
  have rawEnd {a : ℕ} (p : Path N D L a f) (hf : f < N) : a = f := by
    rcases p.cases_tail with he | ⟨b,_,⟨g,_,he,_⟩⟩
    · exact he.symm
    · omega
  have fge : N ≤ f := by
    by_contra! hf
    have h1 := rawEnd rowFork hf
    have h2 := rawEnd colFork hf
    have := i.isLt
    omega
  let fidx := f-N
  have feq : f = N+fidx := by dsimp [fidx]; omega
  have fLt : fidx < D.size := by
    have hb := hjf.2
    have hL : j < D.size := closedL.1 j hjL
    omega
  have allReach (a : ℕ) (ha : a ∈ L) :
      reaches N D L (N+a) D.output := outEq.symm ▸ every_gate_reaches_root closedL next a ha
  have tLe := reachIncreases (allReach t htL)
  have lastLt : D.size - 1 < D.size := by have := oLt; omega
  have outLast : D.output + 1 = N+D.size := by
    have hlast := reachIncreases (allReach (D.size-1) (full.symm ▸ Finset.mem_range.mpr lastLt))
    omega
  have atMostOne (w : ℕ) (hne : w ≠ f) :
      readsIn D L w = if w ∈ used N D L then 1 else 0 := by
    let S := L.filter fun q => w ∈ (gateAt D q).inputs
    have read := reads_card D L w (fun q hq => (arity q hq).2.1)
    change readsIn D L w = S.card at read
    rw [read]
    have s1 : S.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨haL,haW⟩ := Finset.mem_filter.mp ha
      obtain ⟨hbL,hbW⟩ := Finset.mem_filter.mp hb
      exact forkOnly w a b hne haL hbL ⟨haW,back a (closedL.1 a haL) w haW⟩
        ⟨hbW,back b (closedL.1 b hbL) w hbW⟩
    have pos : 0 < S.card ↔ w ∈ used N D L := by
      rw [Finset.card_pos, used_has_reader back closedL.1]
      exact ⟨fun ⟨q,hq⟩ => ⟨q,Finset.mem_filter.mp hq⟩,
        fun ⟨q,hq⟩ => ⟨q,Finset.mem_filter.mpr hq⟩⟩
    by_cases h : w ∈ used N D L
    · rw [ite_eq_left h]
      exact Nat.le_antisymm s1 (pos.mpr h)
    · rw [ite_eq_right h]
      exact Nat.eq_zero_of_not_pos (mt pos.mp h)
  have forkReaders : L.filter (fun q => f ∈ (gateAt D q).inputs) = {j,k} := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨ha,hw⟩
      by_cases p : a = j
      · exact Or.inl p
      · exact Or.inr ((unique_collision slots1 hjL hkL hjk hjf hkf ha hjL p
          ⟨hw,back a (closedL.1 a ha) f hw⟩ hjf).2.resolve_left
            (fun h => p h.1)).1
    · rintro (rfl | rfl)
      · exact ⟨hjL,hjf.1⟩
      · exact ⟨hkL,hkf.1⟩
  have forkRead : readsIn D L f = 2 := by
    rw [reads_card D L f (fun q hq => (arity q hq).2.1),forkReaders]
    simp [hjk]
  let Q := insert t (((PEqualNP.EdgeOwnership.cones N D).getD t []).toFinset)
  have inQ (a : ℕ) : a ∈ Q ↔ reaches N D L (N+a) (N+t) := by
    rw [gateReach full]
    simp [Q, PEqualNP.EdgeOwnership.InCone]
  have qSub : Q ⊆ L := by
    intro a ha
    have hle := reachIncreases ((inQ a).mp ha)
    have ht := closedL.1 t htL
    exact full.symm ▸ Finset.mem_range.mpr (by change t < D.size at ht; omega)
  have oneToNot : readsIn D Q f = 1 := by
    by_contra hread
    let T := Q.filter fun a => f ∈ (gateAt D a).inputs
    have n1 : T.card ≠ 1 := by
      rw [reads_card D Q f (fun a ha => (arity a (qSub ha)).2.1)] at hread
      exact hread
    have sub : T ⊆ ({j,k} : Finset ℕ) := by
      intro a ha
      rw [← forkReaders]
      obtain ⟨ha,hm⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨qSub ha,hm⟩
    have noLeak : ∀ a b, a ≠ N+t → edgeTo N D L a b → reaches N D L a (N+t) →
        reaches N D L b (N+t) := by
      intro a b ne ab p
      by_cases e : a = f
      · subst a
        obtain ⟨w,fw,wp⟩ := Network.path_head p ne
        obtain ⟨s,hs,rfl,hsw⟩ := fw
        have hsT : s ∈ T := Finset.mem_filter.mpr ⟨(inQ s).mpr wp,hsw.1⟩
        have hpos := Finset.card_pos.mpr ⟨s,hsT⟩
        have htwo : ({j,k} : Finset ℕ).card = 2 := by simp [hjk]
        have hbd := Finset.card_le_card sub
        have all := Finset.eq_of_subset_of_card_le sub (by omega)
        obtain ⟨d,hd,rfl,hdw⟩ := ab
        have hdT : d ∈ T := by
          rw [all,← forkReaders]
          exact Finset.mem_filter.mpr ⟨hd,hdw.1⟩
        exact (inQ d).mp (Finset.mem_filter.mp hdT).1
      · obtain ⟨w,aw,wp⟩ := Network.path_head p ne
        obtain ⟨j',hj',rfl,h1⟩ := aw
        obtain ⟨k',hk',rfl,h2⟩ := ab
        rwa [forkOnly a k' j' e hk' hj' h2 h1]
    exact hiBad (Unate.omitted_row_comparable drep closedL liveOut badRow
      (unateWithClosedNot closedL htL hu huList htNot liveOut tLe
        (fun a ha ne => ops a ha (fun h => ne ((only a ha).mp h))) noLeak))
  have fToNot : fidx < t ∧ PEqualNP.EdgeOwnership.InCone N D fidx t := by
    have one := reads_card D Q f (fun a ha => (arity a (qSub ha)).2.1)
    rw [oneToNot] at one
    have pos : 0 < (Q.filter fun a => f ∈ (gateAt D a).inputs).card := by omega
    obtain ⟨a,ha⟩ := Finset.card_pos.mp pos
    obtain ⟨haQ,haF⟩ := Finset.mem_filter.mp ha
    have ba := back a (closedL.1 a (qSub haQ)) f haF
    have path := Relation.ReflTransGen.head
      (show edgeTo N D L f (N+a) from ⟨a,qSub haQ,rfl,haF,ba⟩) ((inQ a).mp haQ)
    rw [feq] at path
    have lt : fidx < t := by
      have le := reachIncreases ((inQ a).mp haQ)
      omega
    exact ⟨lt, ((gateReach full fidx t).mp path).resolve_left (Nat.ne_of_lt lt)⟩
  have otherRead (a : ℕ) (ha : a < D.size) (hne : N+a ≠ f) :
      readsIn D L (N+a) = if a+1 = D.size then 0 else 1 := by
    rw [atMostOne _ hne]
    by_cases last : a+1 = D.size
    · have h0 : N+a ∉ used N D L := by
        intro hm
        obtain ⟨b,hb,hbefore⟩ := mem_used.mp hm
        have hbl := closedL.1 b hb
        have hlt := hbefore.2
        change b < D.size at hbl
        omega
      simp [last,h0]
    · have hao : a ≠ o := fun e => by omega
      obtain ⟨b,hb,hbefore⟩ := next a (full.symm ▸ Finset.mem_range.mpr ha) hao
      simp [last, mem_used.mpr ⟨b,hb,hbefore⟩]
  have opShape : ∀ g ∈ D.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1) := by
    intro g hg
    obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hg
    have ga : gateAt D a = g := by rw [gateAt,List.getD_eq_getElem _ _ ha,he]
    have hL : a ∈ L := full.symm ▸ Finset.mem_range.mpr ha
    rw [← ga]
    by_cases e : (gateAt D a).op = .not
    · exact Or.inr ⟨e,by simpa [e] using (arity a hL).1⟩
    · exact Or.inl ⟨ops a hL e,by simpa [e] using (arity a hL).1⟩
  let ff : Fin D.size := ⟨fidx,fLt⟩
  let tt : Fin D.size := ⟨t,closedL.1 _ htL⟩
  refine ⟨trimmedWires C, by omega, outLast, back, opShape, r,c,ff,tt,fToNot.1,?_,?_,?_,?_,fToNot.2,?_,?_⟩
  · intro a
    rw [only a.val (full.symm ▸ Finset.mem_range.mpr a.isLt)]
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  · intro a
    rw [← full,atMostOne _ (by have := a.isLt; dsimp [N] at fge; omega)]
    by_cases h : a = r
    · subst a
      simp [(rowUnused r).mpr rfl]
    · have : a.val ∈ used N D L := by simpa only [not_not] using mt (rowUnused a).mp h
      simp [h,this]
  · intro a
    rw [← full,atMostOne _ (by have := a.isLt; dsimp [N] at fge; omega)]
    by_cases h : a = c
    · subst a
      simp [(colUnused c).mpr rfl]
    · have : n+a.val ∈ used N D L := by simpa only [not_not] using mt (colUnused a).mp h
      simp [h,this]
  · intro a
    rw [← full]
    by_cases e : a = ff
    · subst a
      change readsIn D L (N+fidx) = _
      simp [← feq,forkRead]
    · have neq : N+a.val ≠ f := fun h => e (Fin.ext (by change a.val = fidx; omega))
      simpa [e] using otherRead a.val a.isLt neq
  · change readsIn D Q (N+fidx) = 1
    rwa [← feq]
  · intro w
    have htb : t < C.size := sizeD ▸ (show t < D.size from closedL.1 t htL)
    exact trimReads htb
      (fun a ha => only a (full.symm ▸ Finset.mem_range.mpr (sizeD.symm ▸ ha))) w

namespace Proof

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover
open Base.CircuitFacts Base.CircuitFacts.Network Base

def override2 (w1 : ℕ) (b1 : Bool) (w2 : ℕ) (b2 : Bool) (w : ℕ) : Option Bool :=
  if w = w1 then some b1 else if w = w2 then some b2 else none

theorem val_override2_left (N : ℕ) (C : Circuit) (x : ℕ → Bool)
    (w1 : ℕ) (b1 : Bool) (w2 : ℕ) (b2 : Bool) :
    value N C x (override2 w1 b1 w2 b2) w1 = b1 := by
  rw [value]
  simp [override2]

theorem val_override2_right (N : ℕ) (C : Circuit) (x : ℕ → Bool)
    (w1 : ℕ) (b1 : Bool) (w2 : ℕ) (b2 : Bool) (hne : w2 ≠ w1) :
    value N C x (override2 w1 b1 w2 b2) w2 = b2 := by
  rw [value]
  simp [override2, hne]

theorem override2_none_ne {w1 w2 u : ℕ} {b1 b2 : Bool}
    (h : override2 w1 b1 w2 b2 u = none) : u ≠ w1 ∧ u ≠ w2 := by
  by_cases h1 : u = w1
  · unfold override2 at h; rw [ite_eq_left h1] at h; cases h
  · by_cases h2 : u = w2
    · unfold override2 at h; rw [ite_eq_right h1, ite_eq_left h2] at h; cases h
    · exact ⟨h1, h2⟩

theorem replace_signal2 {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (x : ℕ → Bool) (w1 w2 : ℕ) (hne : w2 ≠ w1) (w : ℕ) (hw : live N L w) :
    value N C x (fun _ => none) w =
      value N C x (override2 w1 (value N C x (fun _ => none) w1)
                             w2 (value N C x (fun _ => none) w2)) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w = w1
    · subst h1
      exact (val_override2_left N C x w _ w2 _).symm
    · by_cases h2 : w = w2
      · subst h2
        exact (val_override2_right N C x w1 _ w _ hne).symm
      · have ho : override2 w1 (value N C x (fun _ => none) w1)
            w2 (value N C x (fun _ => none) w2) w = none := by
          simp [override2, h1, h2]
        rcases hw with hraw | ⟨j, hj, rfl⟩
        · rw [val_raw hraw ho, val_raw hraw rfl]
        · rw [val_gate (cl.1 j hj) ho, val_gate (cl.1 j hj) rfl]
          congr 1
          apply List.map_congr_left
          intro u hu
          split_ifs with hlt
          · exact ih u hlt (prev_live cl hj ⟨hu, hlt⟩)
          · rfl

def unblockedStep (N : ℕ) (C : Circuit) (L : Finset ℕ) (stop : ℕ → Prop) (a b : ℕ) : Prop :=
  ¬ stop b ∧ edgeTo N C L a b

abbrev unblocked (N : ℕ) (C : Circuit) (L : Finset ℕ) (stop : ℕ → Prop) :=
  Relation.ReflTransGen (unblockedStep N C L stop)

theorem unblocked_to_reaches {N : ℕ} {C : Circuit} {L : Finset ℕ} {stop : ℕ → Prop}
    {a b : ℕ} (h : unblocked N C L stop a b) : reaches N C L a b := by
  induction h with
  | refl => exact .refl
  | tail _ e ih => exact ih.tail e.2

theorem value_agree_stop {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (stop : ℕ → Prop) (w : ℕ) (hw : live N L w)
    (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (hstop : ∀ u, O u = none → ¬ stop u)
    (hOeq : ∀ u, unblocked N C L stop u w → O u = P u)
    (hraw : ∀ u < N, unblocked N C L stop u w → O u = none → x u = y u) :
    value N C x O w = value N C y P w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have he := hOeq w .refl
    cases hO : O w with
    | some b =>
      have hP : P w = some b := he.symm.trans hO
      rw [value, hO]
      symm
      rw [value, hP]
    | none =>
      have hP : P w = none := he.symm.trans hO
      have hns : ¬ stop w := hstop w hO
      rcases hw with hw | ⟨j, hj, rfl⟩
      · rw [val_raw hw hO, val_raw hw hP, hraw w hw .refl hO]
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · have stepE : unblockedStep N C L stop u (N + j) := ⟨hns, j, hj, rfl, hu, hlt⟩
          exact ih u hlt (prev_live cl hj ⟨hu, hlt⟩)
            (fun v hv => hOeq v (hv.tail stepE))
            (fun v hv hp => hraw v hv (hp.tail stepE))
        · rfl

theorem value_mono_stop {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (stop : ℕ → Prop) (w : ℕ) (hw : live N L w)
    (x y : ℕ → Bool) (O P : ℕ → Option Bool)
    (hstop : ∀ u, O u = none → ¬ stop u)
    (hraw : ∀ u < N, unblocked N C L stop u w → O u = none → x u = true → y u = true)
    (hOv : ∀ u, unblocked N C L stop u w →
      (O u = none ∧ P u = none) ∨
      ∃ b c, O u = some b ∧ P u = some c ∧ (b = true → c = true))
    (hgates : ∀ j ∈ L, unblocked N C L stop (N + j) w → O (N + j) = none →
      (gateAt C j).op = .and ∨ (gateAt C j).op = .or) :
    value N C x O w = true → value N C y P w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hOv w .refl with ⟨hO, hP⟩ | ⟨b, c, hO, hP, hbc⟩
    · have hns : ¬ stop w := hstop w hO
      rcases hw with hw | ⟨j, hj, rfl⟩
      · rw [val_raw hw hO, val_raw hw hP]
        exact hraw w hw .refl hO
      · rw [val_gate (cl.1 j hj) hO, val_gate (cl.1 j hj) hP]
        apply gate_order _ (hgates j hj .refl hO)
        intro u hu
        split_ifs with hlt
        · have stepE : unblockedStep N C L stop u (N + j) := ⟨hns, j, hj, rfl, hu, hlt⟩
          exact ih u hlt (prev_live cl hj ⟨hu, hlt⟩)
            (fun v hv hp => hraw v hv (hp.tail stepE))
            (fun v hv => hOv v (hv.tail stepE))
            (fun k hk hp => hgates k hk (hp.tail stepE))
        · exact id
    · have hx : value N C x O w = b := by rw [value, hO]
      have hy : value N C y P w = c := by rw [value, hP]
      simpa only [hx, hy] using hbc

theorem value_false_stop {N : ℕ} {C : Circuit} {L : Finset ℕ} (cl : closed N C L)
    (stop : ℕ → Prop) (w : ℕ) (hw : live N L w)
    (x : ℕ → Bool) (O : ℕ → Option Bool)
    (hstop : ∀ u, O u = none → ¬ stop u)
    (hraw : ∀ u < N, unblocked N C L stop u w → O u = none → x u = false)
    (hOv : ∀ u, unblocked N C L stop u w → O u = none ∨ O u = some false)
    (hgates : ∀ j ∈ L, unblocked N C L stop (N + j) w → O (N + j) = none →
      ((gateAt C j).op = .and ∨ (gateAt C j).op = .or) ∧ (gateAt C j).inputs.length = 2) :
    value N C x O w = false := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases hOv w .refl with hO | hO
    · have hns : ¬ stop w := hstop w hO
      rcases hw with hw | ⟨j, hj, rfl⟩
      · rw [val_raw hw hO]
        exact hraw w hw .refl hO
      · rw [val_gate (cl.1 j hj) hO]
        obtain ⟨hop, hlen⟩ := hgates j hj .refl hO
        have hall : ∀ u ∈ (gateAt C j).inputs,
            (if u < N + j then value N C x O u else false) = false := by
          intro u hu
          split_ifs with hlt
          · have stepE : unblockedStep N C L stop u (N + j) := ⟨hns, j, hj, rfl, hu, hlt⟩
            exact ih u hlt (prev_live cl hj ⟨hu, hlt⟩)
              (fun v hv hp => hraw v hv (hp.tail stepE))
              (fun v hv => hOv v (hv.tail stepE))
              (fun k hk hp => hgates k hk (hp.tail stepE))
          · rfl
        rcases hlist : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, t⟩⟩
        · simp [hlist] at hlen
        · simp [hlist] at hlen
        · cases t with
          | nil =>
            have ha := hall a (by simp [hlist])
            have hb := hall b (by simp [hlist])
            rcases hop with hop | hop <;>
              simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                List.any_cons, List.any_nil, id_eq, ha, hb] <;> rfl
          | cons _ _ => simp [hlist] at hlen
    · rw [value, hO]

def ind2 {n m : ℕ} (i : Fin n) (j : Fin m) (w : ℕ) : Bool :=
  decide (w = i.val ∨ w = n + j.val)

def sing (k : ℕ) (w : ℕ) : Bool := decide (w = k)

def zeroX (_ : ℕ) : Bool := false

theorem eval_ind2 {n m : ℕ} {A : Fin n → Fin m → Bool} {D : Circuit}
    (hRep : Represents A D) (i : Fin n) (j : Fin m) :
    value (n + m) D (ind2 i j) (fun _ => none) D.output = A i j := by
  have hlen : (oneEach i j).length = n + m := by simp [oneEach]
  have heq : (fun w => (oneEach i j).getD w false) = ind2 i j := by
    funext w
    exact each_value i j w
  have h := val_original (n + m) D (oneEach i j) hlen
  rw [heq] at h
  exact h.trans (hRep i j)

theorem closed_range (N : ℕ) (D : Circuit) (back : ReadsBack N D) :
    closed N D (Finset.range D.size) := by
  refine ⟨fun j hj => Finset.mem_range.mp hj, ?_⟩
  intro j hj u hu
  have hj' : j < D.gates.length := Finset.mem_range.mp hj
  have hlt := back j hj' (N + u) hu.1
  exact Finset.mem_range.mpr (by change u < D.gates.length; omega)

theorem nodup_of_struct {n m : ℕ} {D : Circuit} {r : Fin n} {c : Fin m} {f t : Fin D.size}
    (hback : ReadsBack (n + m) D)
    (hopShape : ∀ g ∈ D.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1))
    (hReadsRow : ∀ i : Fin n, readsIn D (Finset.range D.size) i.val = if i = r then 0 else 1)
    (hReadsCol : ∀ j : Fin m, readsIn D (Finset.range D.size) (n + j.val) = if j = c then 0 else 1)
    (hReadsGate : ∀ j : Fin D.size, readsIn D (Finset.range D.size) (n + m + j.val) =
      if j = f then 2 else if j.val + 1 = D.size then 0 else 1)
    (hQreads : readsIn D (insert t.val (((PEqualNP.EdgeOwnership.cones (n + m) D).getD t.val []).toFinset)) (n + m + f.val) = 1)
    (j : ℕ) (hj : j < D.size) :
    (gateAt D j).inputs.Nodup := by
  set N := n + m
  set L := Finset.range D.size
  set Q := insert t.val (((PEqualNP.EdgeOwnership.cones N D).getD t.val []).toFinset)
  have hjL : j ∈ L := Finset.mem_range.mpr hj
  have hgmem : gateAt D j ∈ D.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases hopShape _ hgmem with ⟨_, hlen⟩ | ⟨_, hlen⟩
  · rcases hl : (gateAt D j).inputs with _ | ⟨a, _ | ⟨b, tl⟩⟩
    · simp [hl] at hlen
    · simp [hl] at hlen
    · cases tl with
      | cons _ _ => simp [hl] at hlen
      | nil =>
        rw [List.nodup_cons, List.mem_singleton]
        refine ⟨?_, List.nodup_singleton b⟩
        intro hab
        subst hab
        have hcnt : (gateAt D j).inputs.count a = 2 := by simp [hl]
        have hge2 : 2 ≤ readsIn D L a := by
          unfold readsIn
          have := Finset.single_le_sum (f := fun k => (gateAt D k).inputs.count a)
            (fun _ _ => Nat.zero_le _) hjL
          omega
        have halt : a < N + j := hback j hj a (by simp [hl])
        have ha_eq : a = N + f.val := by
          by_cases ha1 : a < n
          · have hr := hReadsRow ⟨a, ha1⟩
            dsimp only at hr
            split_ifs at hr <;> omega
          · by_cases ha2 : a < N
            · have hc := hReadsCol ⟨a - n, by omega⟩
              have he : n + (a - n) = a := by omega
              rw [he] at hc
              split_ifs at hc <;> omega
            · have ha3 : a - N < D.size := by omega
              have hg := hReadsGate ⟨a - N, ha3⟩
              have he : N + (a - N) = a := by omega
              rw [he] at hg
              split_ifs at hg with hgf
              · have : a - N = f.val := congrArg Fin.val hgf
                omega
              · omega
              · omega
        subst ha_eq
        have hQsub : Q ⊆ L := by
          intro x hx
          have hxr : reaches N D L (N + x) (N + t.val) := by
            rw [gateReach (rfl : L = Finset.range D.size)]
            simp only [Q, Finset.mem_insert, List.mem_toFinset] at hx
            exact hx
          have hle := reachIncreases hxr
          have htlt := t.isLt
          exact Finset.mem_range.mpr (by omega)
        have hsplit : readsIn D L (N + f.val) = readsIn D Q (N + f.val) + readsIn D (L \ Q) (N + f.val) := by
          unfold readsIn
          rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hQsub]
        have htot : readsIn D L (N + f.val) = 2 := by simpa using hReadsGate f
        by_cases hjQ : j ∈ Q
        · have hleQ := Finset.single_le_sum (f := fun k => (gateAt D k).inputs.count (N + f.val))
            (fun _ _ => Nat.zero_le _) hjQ
          change (gateAt D j).inputs.count (N + f.val) ≤ readsIn D Q (N + f.val) at hleQ
          omega
        · have hjout : j ∈ L \ Q := Finset.mem_sdiff.mpr ⟨hjL, hjQ⟩
          have hleO := Finset.single_le_sum (f := fun k => (gateAt D k).inputs.count (N + f.val))
            (fun _ _ => Nat.zero_le _) hjout
          change (gateAt D j).inputs.count (N + f.val) ≤ readsIn D (L \ Q) (N + f.val) at hleO
          omega
  · rcases hl : (gateAt D j).inputs with _ | ⟨a, tl⟩
    · simp [hl] at hlen
    · cases tl with
      | nil => exact List.nodup_singleton a
      | cons _ _ => simp [hl] at hlen

set_option maxHeartbeats 2000000 in
theorem part12
    (n m : ℕ) (A : Fin n → Fin m → Bool) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hRowInj : Function.Injective A) (hColInj : Function.Injective (fun j i => A i j))
    (hRowIncomp : ∀ i, ∃ k, ¬ ((∀ j, A i j = true → A k j = true) ∨ (∀ j, A k j = true → A i j = true)))
    (hColIncomp : ∀ j, ∃ l, ¬ ((∀ i, A i j = true → A i l = true) ∨ (∀ i, A i l = true → A i j = true)))
    (C : Circuit) (hF : FanInTwo C) (hRep : Represents A C) (hSize : C.size ≤ n + m - 1)
    (hHasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    letI : DecidableEq GateOp := gateOpDecEq
    let N := n + m
    let D : Circuit := ⟨C.gates.map (fun g =>
      if g.op = GateOp.not then ⟨g.op, g.inputs.take 1⟩ else g), C.output⟩
    ∃ (r u : Fin n) (c v : Fin m) (f t : Fin D.size),
      r ≠ u ∧ c ≠ v ∧ f < t ∧
      D.size = N - 1 ∧ D.output + 1 = N + D.size ∧ ReadsBack N D ∧ Represents A D ∧ FanInTwo D ∧
      (∀ j : Fin D.size, (gateAt D j.val).op = GateOp.not ↔ j = t) ∧
      (∀ g ∈ D.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
      (∀ j < D.size, (gateAt D j).inputs.Nodup) ∧
      (∀ i : Fin n, readsIn D (Finset.range D.size) i.val = if i = r then 0 else 1) ∧
      (∀ j : Fin m, readsIn D (Finset.range D.size) (n + j.val) = if j = c then 0 else 1) ∧
      (∀ j : Fin D.size, readsIn D (Finset.range D.size) (N + j.val) =
        if j = f then 2 else if j.val + 1 = D.size then 0 else 1) ∧
      (gateAt D f.val).op = .or ∧
      ((gateAt D f.val).inputs = [u.val, n + v.val] ∨ (gateAt D f.val).inputs = [n + v.val, u.val]) ∧
      (gateAt D t.val) = ⟨.not, [N + f.val]⟩ ∧
      ¬ ((∀ j, A r j = true → A u j = true) ∨ (∀ j, A u j = true → A r j = true)) ∧
      ¬ ((∀ i, A i c = true → A i v = true) ∨ (∀ i, A i v = true → A i c = true)) ∧
      value N D zeroX (override2 (N + f.val) true (N + t.val) false) D.output = false ∧
      value N D zeroX (override2 (N + f.val) false (N + t.val) true) D.output = false := by
  classical
  let _ : DecidableEq GateOp := gateOpDecEq
  dsimp only
  set N := n + m
  set D : Circuit := ⟨C.gates.map (fun g =>
    if g.op = GateOp.not then ⟨g.op, g.inputs.take 1⟩ else g), C.output⟩
  have hS := struct_29755 n m A hn hm hRowInj hColInj hRowIncomp hColIncomp C hF hRep hSize hHasNot
  dsimp only at hS
  change (∀ xs : List Bool, D.wires xs = C.wires xs) ∧
    C.size = N - 1 ∧ D.output + 1 = N + D.size ∧ ReadsBack N D ∧
    (∀ g ∈ D.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
    ∃ (r : Fin n) (c : Fin m) (f t : Fin D.size), f < t ∧
      (∀ j : Fin D.size, (gateAt D j.val).op = .not ↔ j = t) ∧
      (∀ i : Fin n, readsIn D (Finset.range D.size) i.val = if i = r then 0 else 1) ∧
      (∀ j : Fin m, readsIn D (Finset.range D.size) (n + j.val) = if j = c then 0 else 1) ∧
      (∀ j : Fin D.size, readsIn D (Finset.range D.size) (N + j.val) =
        if j = f then 2 else if j.val + 1 = D.size then 0 else 1) ∧
      PEqualNP.EdgeOwnership.InCone N D f.val t.val ∧
      readsIn D (insert t.val (((PEqualNP.EdgeOwnership.cones N D).getD t.val []).toFinset)) (N + f.val) = 1 ∧
      ∀ w : ℕ, readsIn C (Finset.range C.size) w =
        readsIn D (Finset.range D.size) w + (((gateAt C t.val).inputs.drop 1).count w) at hS
  obtain ⟨hwires, hCsize, hout, hback, hopShape, r, c, f, t, hft, hNotOnly, hReadsRow, hReadsCol, hReadsGate, hInCone, hQreads, _⟩ := hS
  have hDsize : D.size = N - 1 := by
    have : D.size = C.size := by simp [D, Circuit.size]
    omega
  have hDrep : Represents A D := by
    intro i j
    simp only [Circuit.eval, hwires]
    exact hRep i j
  have hDfan : FanInTwo D := by
    intro g hg
    rcases hopShape g hg with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
    · refine ⟨?_, by omega⟩
      rcases hop with h | h <;> simp [h]
    · exact ⟨by simp [hop], by omega⟩
  set L := Finset.range D.size
  have clL : closed N D L := closed_range N D hback
  have hnodup : ∀ j < D.size, (gateAt D j).inputs.Nodup :=
    nodup_of_struct hback hopShape hReadsRow hReadsCol hReadsGate hQreads
  have hreads_card : ∀ (S : Finset ℕ), S ⊆ L → ∀ w,
      readsIn D S w = (S.filter fun j => w ∈ (gateAt D j).inputs).card := by
    intro S hS w
    exact reads_card D S w (fun j hj => hnodup j (Finset.mem_range.mp (hS hj)))
  have hreads_eq_zero : ∀ w, readsIn D L w = 0 → ∀ j ∈ L, w ∉ (gateAt D j).inputs := by
    intro w h0 j hj hmem
    rw [hreads_card L (Finset.Subset.refl L) w, Finset.card_eq_zero] at h0
    exact Finset.notMem_empty j (h0 ▸ Finset.mem_filter.mpr ⟨hj, hmem⟩)
  have hreads_le_one : ∀ w, w ≠ N + f.val → readsIn D L w ≤ 1 := by
    intro w hne
    by_cases h1 : w < n
    · have h := hReadsRow ⟨w, h1⟩; dsimp only at h; split_ifs at h <;> omega
    · by_cases h2 : w < N
      · have h := hReadsCol ⟨w - n, by omega⟩
        have he : n + (w - n) = w := by omega
        rw [he] at h; split_ifs at h <;> omega
      · by_cases h3 : w < N + D.size
        · have h := hReadsGate ⟨w - N, by omega⟩
          have he : N + (w - N) = w := by omega
          rw [he] at h
          have hne' : (⟨w - N, by omega⟩ : Fin D.size) ≠ f := fun e => hne (by
            have := congrArg Fin.val e; dsimp only at this; omega)
          simp only [hne', ite_false] at h
          split_ifs at h <;> omega
        · have h0 : readsIn D L w = 0 := by
            rw [hreads_card L (Finset.Subset.refl L) w, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro j hj hmem
            have := hback j (Finset.mem_range.mp hj) w hmem
            have := Finset.mem_range.mp hj
            omega
          omega
  have huniq : ∀ w, w ≠ N + f.val → ∀ j1 ∈ L, ∀ j2 ∈ L,
      w ∈ (gateAt D j1).inputs → w ∈ (gateAt D j2).inputs → j1 = j2 := by
    intro w hne j1 hj1 j2 hj2 hm1 hm2
    have hle := hreads_le_one w hne
    rw [hreads_card L (Finset.Subset.refl L) w] at hle
    exact Finset.card_le_one.mp hle j1 (Finset.mem_filter.mpr ⟨hj1, hm1⟩) j2 (Finset.mem_filter.mpr ⟨hj2, hm2⟩)
  set Q : Finset ℕ := insert t.val (((PEqualNP.EdgeOwnership.cones N D).getD t.val []).toFinset)
  set Fset : Finset ℕ := insert f.val (((PEqualNP.EdgeOwnership.cones N D).getD f.val []).toFinset)
  have hmemQ : ∀ a, a ∈ Q ↔ reaches N D L (N + a) (N + t.val) := by
    intro a
    rw [gateReach (rfl : L = Finset.range D.size)]
    simp only [Q, Finset.mem_insert, List.mem_toFinset, PEqualNP.EdgeOwnership.InCone]
  have hmemF : ∀ a, a ∈ Fset ↔ reaches N D L (N + a) (N + f.val) := by
    intro a
    rw [gateReach (rfl : L = Finset.range D.size)]
    simp only [Fset, Finset.mem_insert, List.mem_toFinset, PEqualNP.EdgeOwnership.InCone]
  have hQsub : Q ⊆ L := by
    intro a ha
    have hle := reachIncreases ((hmemQ a).mp ha)
    have htlt := t.isLt
    exact Finset.mem_range.mpr (by omega)
  have hFsub : Fset ⊆ L := by
    intro a ha
    have hle := reachIncreases ((hmemF a).mp ha)
    have hflt := f.isLt
    exact Finset.mem_range.mpr (by omega)
  have hfReachT : reaches N D L (N + f.val) (N + t.val) :=
    (gateReach (rfl : L = Finset.range D.size) f.val t.val).mpr (Or.inr hInCone)
  have hFsubQ : Fset ⊆ Q := by
    intro a ha
    exact (hmemQ a).mpr (((hmemF a).mp ha).trans hfReachT)
  have htNotF : t.val ∉ Fset := by
    intro htF
    have hle := reachIncreases ((hmemF t.val).mp htF)
    have : f.val < t.val := hft
    omega
  have hQclosed : ∀ j ∈ Q, ∀ a, N + a ∈ (gateAt D j).inputs → a ∈ Q := by
    intro j hj a ha
    have hjL := hQsub hj
    have hlt := hback j (Finset.mem_range.mp hjL) (N + a) ha
    exact (hmemQ a).mpr (Relation.ReflTransGen.head ⟨j, hjL, rfl, ha, hlt⟩ ((hmemQ j).mp hj))
  have hFclosed : ∀ j ∈ Fset, ∀ a, N + a ∈ (gateAt D j).inputs → a ∈ Fset := by
    intro j hj a ha
    have hjL := hFsub hj
    have hlt := hback j (Finset.mem_range.mp hjL) (N + a) ha
    exact (hmemF a).mpr (Relation.ReflTransGen.head ⟨j, hjL, rfl, ha, hlt⟩ ((hmemF j).mp hj))
  have hnoEscapeQ : ∀ a ∈ Q, a ≠ f.val → a ≠ t.val → ∀ j ∈ L,
      N + a ∈ (gateAt D j).inputs → j ∈ Q := by
    intro a ha haf hat j hj hmem
    have hreach := (hmemQ a).mp ha
    have hne : N + a ≠ N + t.val := by omega
    obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, hkz⟩ := path_head hreach hne
    have hkQ : k ∈ Q := (hmemQ k).mpr hkz
    have heq : j = k := huniq (N + a) (by omega) j hj k hkL hmem hkm
    exact heq ▸ hkQ
  have hnoEscapeF : ∀ a ∈ Fset, a ≠ f.val → ∀ j ∈ L,
      N + a ∈ (gateAt D j).inputs → j ∈ Fset := by
    intro a ha haf j hj hmem
    have hreach := (hmemF a).mp ha
    have hne : N + a ≠ N + f.val := by omega
    obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, hkz⟩ := path_head hreach hne
    have hkF : k ∈ Fset := (hmemF k).mpr hkz
    have heq : j = k := huniq (N + a) (by omega) j hj k hkL hmem hkm
    exact heq ▸ hkF
  have hnot_gate_and_or : ∀ j ∈ L, j ≠ t.val →
      ((gateAt D j).op = .and ∨ (gateAt D j).op = .or) ∧ (gateAt D j).inputs.length = 2 := by
    intro j hj hjt
    have hjlt := Finset.mem_range.mp hj
    have hgmem : gateAt D j ∈ D.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
    have hne : (gateAt D j).op ≠ .not := fun h => hjt (congrArg Fin.val ((hNotOnly ⟨j, hjlt⟩).mp h))
    rcases hopShape _ hgmem with h | ⟨h, _⟩
    · exact h
    · exact (hne h).elim
  have htOp : (gateAt D t.val).op = .not := (hNotOnly t).mpr rfl
  have htLen : (gateAt D t.val).inputs.length = 1 := by
    have hgmem : gateAt D t.val ∈ D.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ t.isLt]; exact List.getElem_mem t.isLt
    rcases hopShape _ hgmem with ⟨h, _⟩ | ⟨_, hlen⟩
    · rcases h with h | h <;> rw [htOp] at h <;> cases h
    · exact hlen
  obtain ⟨ut, hutList⟩ := List.length_eq_one_iff.mp htLen
  have hutMem : ut ∈ (gateAt D t.val).inputs := by simp [hutList]
  have hutLt : ut < N + t.val := hback t.val t.isLt ut hutMem
  have hutLive : live N L ut := prev_live clL (Finset.mem_range.mpr t.isLt) ⟨hutMem, hutLt⟩
  have houtEq : D.output = N + (D.size - 1) := by omega
  have houtLive : live N L D.output := Or.inr ⟨D.size - 1, Finset.mem_range.mpr (by omega), houtEq⟩
  have hfLive : live N L (N + f.val) := Or.inr ⟨f.val, Finset.mem_range.mpr f.isLt, rfl⟩
  have htLive : live N L (N + t.val) := Or.inr ⟨t.val, Finset.mem_range.mpr t.isLt, rfl⟩
  have hQreads1 : ∀ j1 ∈ Q, ∀ j2 ∈ Q,
      N + f.val ∈ (gateAt D j1).inputs → N + f.val ∈ (gateAt D j2).inputs → j1 = j2 := by
    intro j1 hj1 j2 hj2 hm1 hm2
    have h1 := hQreads
    rw [hreads_card Q hQsub (N + f.val)] at h1
    exact Finset.card_le_one.mp (le_of_eq h1) j1 (Finset.mem_filter.mpr ⟨hj1, hm1⟩) j2 (Finset.mem_filter.mpr ⟨hj2, hm2⟩)
  let W (x : ℕ → Bool) : Bool := value N D x (fun _ => none) (N + f.val)
  let Psi (b : Bool) (x : ℕ → Bool) : Bool := value N D x (relay (N + f.val) b) ut
  let Phi (b1 b2 : Bool) (x : ℕ → Bool) : Bool :=
    value N D x (override2 (N + f.val) b1 (N + t.val) b2) D.output
  have hT_eq : ∀ x, value N D x (fun _ => none) (N + t.val) = ! Psi (W x) x := by
    intro x
    have h1 : value N D x (fun _ => none) (N + t.val) = ! value N D x (fun _ => none) ut := by
      rw [val_gate t.isLt rfl, htOp, hutList]
      simp [GateOp.eval, hutLt]
    rw [h1]
    congr 1
    exact replace_signal clL x (N + f.val) ut hutLive
  have hEval : ∀ x, value N D x (fun _ => none) D.output = Phi (W x) (! Psi (W x) x) x := by
    intro x
    have hftne : N + t.val ≠ N + f.val := by have : f.val < t.val := hft; omega
    have h := replace_signal2 clL x (N + f.val) (N + t.val) hftne D.output houtLive
    rw [hT_eq x] at h
    exact h
  have hEvalA : ∀ (i : Fin n) (j : Fin m),
      A i j = Phi (W (ind2 i j)) (! Psi (W (ind2 i j)) (ind2 i j)) (ind2 i j) := by
    intro i j
    rw [← eval_ind2 hDrep i j, hEval]
  have hrNoReach : ∀ w, N ≤ w → ¬ reaches N D L r.val w := by
    intro w hw hr
    obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, _⟩ := path_head hr (by have := r.isLt; omega)
    exact hreads_eq_zero r.val (by simpa using hReadsRow r) k hkL hkm
  have hcNoReach : ∀ w, N ≤ w → ¬ reaches N D L (n + c.val) w := by
    intro w hw hr
    obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, _⟩ := path_head hr (by have := c.isLt; omega)
    exact hreads_eq_zero (n + c.val) (by simpa using hReadsCol c) k hkL hkm
  have hUnb_F_reach : ∀ w, unblocked N D L (fun z => z = N + f.val) w ut →
      reaches N D L w (N + t.val) ∧ (w ≠ N + f.val → ¬ reaches N D L w (N + f.val)) := by
    intro w hw
    have hnotf : w ≠ N + f.val → ¬ reaches N D L w (N + f.val) := by
      induction hw using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro hne hrf
        obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, hkz⟩ := path_head hrf hne
        have hkF : k ∈ Fset := (hmemF k).mpr hkz
        have hkt : t.val = k := huniq ut hne t.val (Finset.mem_range.mpr t.isLt) k hkL hutMem hkm
        exact htNotF (hkt ▸ hkF)
      | @head a b step _ ih =>
        intro hne hrf
        obtain ⟨hnb, j, hjL, rfl, hjm, _⟩ := step
        obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, hkz⟩ := path_head hrf hne
        have hjk : j = k := huniq a hne j hjL k hkL hjm hkm
        exact ih hnb (hjk ▸ hkz)
    have hr1 : reaches N D L w ut := unblocked_to_reaches hw
    have hr2 : reaches N D L w (N + t.val) :=
      hr1.tail ⟨t.val, Finset.mem_range.mpr t.isLt, rfl, hutMem, hutLt⟩
    exact ⟨hr2, hnotf⟩
  have hUnb_Phi_reach : ∀ w, unblocked N D L (fun z => z = N + f.val ∨ z = N + t.val) w D.output →
      w ≠ N + f.val → w ≠ N + t.val → ¬ reaches N D L w (N + t.val) := by
    intro w hw
    induction hw using Relation.ReflTransGen.head_induction_on with
    | refl =>
      intro _ hnt hrt
      have hle := reachIncreases hrt
      have htlt := t.isLt
      have htEq : N + t.val = D.output := by omega
      exact hnt htEq.symm
    | @head a b step _ ih =>
      intro hnf hnt hrt
      obtain ⟨hnb, j, hjL, rfl, hjm, _⟩ := step
      have hnb1 : N + j ≠ N + f.val := fun h => hnb (Or.inl h)
      have hnb2 : N + j ≠ N + t.val := fun h => hnb (Or.inr h)
      obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, hkz⟩ := path_head hrt hnt
      have hjk : j = k := huniq a hnf j hjL k hkL hjm hkm
      exact ih hnb1 hnb2 (hjk ▸ hkz)
  have hW_agree : ∀ x y, (∀ w < N, reaches N D L w (N + f.val) → x w = y w) → W x = W y := by
    intro x y hxy
    exact value_agree clL (N + f.val) hfLive x y (fun _ => none) (fun _ => none) hxy (fun _ _ => rfl)
  have hW_mono : ∀ x y, (∀ w < N, reaches N D L w (N + f.val) → x w = true → y w = true) →
      W x = true → W y = true := by
    intro x y hxy
    refine value_mono clL (N + f.val) hfLive x y (fun _ => none) (fun _ => none) hxy
      (fun _ _ => Or.inl ⟨rfl, rfl⟩) ?_
    intro j hj hr _
    have hjt : j ≠ t.val := fun e => htNotF (e ▸ (hmemF j).mpr hr)
    exact (hnot_gate_and_or j hj hjt).1
  have hW_zero : W zeroX = false := by
    refine value_false_stop clL (fun _ => False) (N + f.val) hfLive zeroX (fun _ => none)
      (fun _ _ => id) (fun _ _ _ _ => rfl) (fun _ _ => Or.inl rfl) ?_
    intro j hj hu _
    have hr := unblocked_to_reaches hu
    have hjt : j ≠ t.val := fun e => htNotF (e ▸ (hmemF j).mpr hr)
    exact hnot_gate_and_or j hj hjt
  have hPsi_agree : ∀ b x y,
      (∀ w < N, reaches N D L w (N + t.val) → ¬ reaches N D L w (N + f.val) → x w = y w) →
      Psi b x = Psi b y := by
    intro b x y hxy
    refine value_agree_stop clL (fun z => z = N + f.val) ut hutLive x y (relay (N + f.val) b) (relay (N + f.val) b)
      (fun u hu e => by simp [relay, e] at hu) (fun _ _ => rfl) ?_
    intro w hw hu _
    have ⟨h1, h2⟩ := hUnb_F_reach w hu
    exact hxy w hw h1 (h2 (by omega))
  have hPsi_mono : ∀ b1 b2 x y, (b1 = true → b2 = true) →
      (∀ w < N, reaches N D L w (N + t.val) → ¬ reaches N D L w (N + f.val) → x w = true → y w = true) →
      Psi b1 x = true → Psi b2 y = true := by
    intro b1 b2 x y hb hxy
    refine value_mono_stop clL (fun z => z = N + f.val) ut hutLive x y (relay (N + f.val) b1) (relay (N + f.val) b2)
      (fun u hu e => by simp [relay, e] at hu) ?_ ?_ ?_
    · intro w hw hu _
      have ⟨h1, h2⟩ := hUnb_F_reach w hu
      exact hxy w hw h1 (h2 (by omega))
    · intro w _
      by_cases hwf : w = N + f.val
      · exact Or.inr ⟨b1, b2, by simp [relay, hwf], by simp [relay, hwf], hb⟩
      · exact Or.inl ⟨by simp [relay, hwf], by simp [relay, hwf]⟩
    · intro j hj hu _
      have hr := reachIncreases (unblocked_to_reaches hu)
      exact (hnot_gate_and_or j hj (by omega)).1
  have hPsi_zero : Psi false zeroX = false := by
    refine value_false_stop clL (fun z => z = N + f.val) ut hutLive zeroX (relay (N + f.val) false)
      (fun u hu e => by simp [relay, e] at hu) (fun _ _ _ _ => rfl) ?_ ?_
    · intro u _
      by_cases huf : u = N + f.val
      · exact Or.inr (by simp [relay, huf])
      · exact Or.inl (by simp [relay, huf])
    · intro j hj hu _
      have hr := reachIncreases (unblocked_to_reaches hu)
      exact hnot_gate_and_or j hj (by omega)
  have hftne_all : N + t.val ≠ N + f.val := by have : f.val < t.val := hft; omega
  have hPhi_agree : ∀ b1 b2 x y,
      (∀ w < N, w ≠ r.val → w ≠ n + c.val → ¬ reaches N D L w (N + t.val) → x w = y w) →
      Phi b1 b2 x = Phi b1 b2 y := by
    intro b1 b2 x y hxy
    refine value_agree_stop clL (fun z => z = N + f.val ∨ z = N + t.val) D.output houtLive
      x y (override2 (N + f.val) b1 (N + t.val) b2) (override2 (N + f.val) b1 (N + t.val) b2)
      (fun u hu h => by have ⟨h1, h2⟩ := override2_none_ne hu; exact h.elim h1 h2) (fun _ _ => rfl) ?_
    intro w hw hu _
    have hnr : w ≠ r.val := fun e => hrNoReach D.output (by omega) (e ▸ unblocked_to_reaches hu)
    have hnc : w ≠ n + c.val := fun e => hcNoReach D.output (by omega) (e ▸ unblocked_to_reaches hu)
    exact hxy w hw hnr hnc (hUnb_Phi_reach w hu (by omega) (by omega))
  have hPhi_mono : ∀ b1 b2 c1 c2 x y,
      (b1 = true → c1 = true) → (b2 = true → c2 = true) →
      (∀ w < N, w ≠ r.val → w ≠ n + c.val → ¬ reaches N D L w (N + t.val) → x w = true → y w = true) →
      Phi b1 b2 x = true → Phi c1 c2 y = true := by
    intro b1 b2 c1 c2 x y h1 h2 hxy
    refine value_mono_stop clL (fun z => z = N + f.val ∨ z = N + t.val) D.output houtLive
      x y (override2 (N + f.val) b1 (N + t.val) b2) (override2 (N + f.val) c1 (N + t.val) c2)
      (fun u hu h => by have ⟨h1, h2⟩ := override2_none_ne hu; exact h.elim h1 h2) ?_ ?_ ?_
    · intro w hw hu _
      have hnr : w ≠ r.val := fun e => hrNoReach D.output (by omega) (e ▸ unblocked_to_reaches hu)
      have hnc : w ≠ n + c.val := fun e => hcNoReach D.output (by omega) (e ▸ unblocked_to_reaches hu)
      exact hxy w hw hnr hnc (hUnb_Phi_reach w hu (by omega) (by omega))
    · intro w _
      by_cases hwf : w = N + f.val
      · exact Or.inr ⟨b1, c1, by simp [override2, hwf], by simp [override2, hwf], h1⟩
      · by_cases hwt : w = N + t.val
        · exact Or.inr ⟨b2, c2, by unfold override2; rw [ite_eq_right hwf, ite_eq_left hwt],
            by unfold override2; rw [ite_eq_right hwf, ite_eq_left hwt], h2⟩
        · exact Or.inl ⟨by unfold override2; rw [ite_eq_right hwf, ite_eq_right hwt],
            by unfold override2; rw [ite_eq_right hwf, ite_eq_right hwt]⟩
    · intro j hj _ hnone
      have hjt : j ≠ t.val := fun e => (override2_none_ne hnone).2 (by omega)
      exact (hnot_gate_and_or j hj hjt).1
  have hPhi_zero : Phi false false zeroX = false := by
    refine value_false_stop clL (fun z => z = N + f.val ∨ z = N + t.val) D.output houtLive
      zeroX (override2 (N + f.val) false (N + t.val) false)
      (fun u hu h => by have ⟨h1, h2⟩ := override2_none_ne hu; exact h.elim h1 h2)
      (fun _ _ _ _ => rfl) ?_ ?_
    · intro u _
      by_cases h1 : u = N + f.val
      · exact Or.inr (by simp [override2, h1])
      · by_cases h2 : u = N + t.val
        · exact Or.inr (by unfold override2; rw [ite_eq_right h1, ite_eq_left h2])
        · exact Or.inl (by unfold override2; rw [ite_eq_right h1, ite_eq_right h2])
    · intro j hj _ hnone
      have hjt : j ≠ t.val := fun e => (override2_none_ne hnone).2 (by omega)
      exact hnot_gate_and_or j hj hjt
  have hRowReach_F : ∀ i : Fin n,
      ¬ ((∀ j, A r j = true → A i j = true) ∨ (∀ j, A i j = true → A r j = true)) →
      reaches N D L i.val (N + f.val) := by
    intro i hi
    by_contra hnf
    by_cases hnt : reaches N D L i.val (N + t.val)
    · apply hi; right; intro j hij
      rw [hEvalA i j] at hij; rw [hEvalA r j]
      have hWeq : W (ind2 i j) = W (ind2 r j) := hW_agree _ _ (fun w _ hrw => by
        have h1 : w ≠ i.val := fun e => hnf (e ▸ hrw)
        have h2 : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
        simp [ind2, h1, h2])
      have hPsiLe : Psi (W (ind2 r j)) (ind2 r j) = true → Psi (W (ind2 i j)) (ind2 i j) = true := by
        rw [hWeq]
        exact hPsi_mono _ _ _ _ id (fun w _ hrw _ h1 => by
          have hwr : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrw)
          simp only [ind2, decide_eq_true_eq] at h1 ⊢
          rcases h1 with h1 | h1
          · exact (hwr h1).elim
          · exact Or.inr h1)
      have hNotLe : (! Psi (W (ind2 i j)) (ind2 i j)) = true → (! Psi (W (ind2 r j)) (ind2 r j)) = true := by
        intro h
        rw [Bool.not_eq_true'] at h ⊢
        exact Bool.eq_false_iff.mpr (fun ht => by have := hPsiLe ht; rw [this] at h; cases h)
      exact hPhi_mono _ _ _ _ (ind2 i j) (ind2 r j) (fun h => hWeq ▸ h) hNotLe (fun w _ hnr _ hwn h1 => by
        have hwi : w ≠ i.val := fun e => hwn (e ▸ hnt)
        simp only [ind2, decide_eq_true_eq] at h1 ⊢
        rcases h1 with h1 | h1
        · exact (hwi h1).elim
        · exact Or.inr h1) hij
    · apply hi; left; intro j hrj
      rw [hEvalA r j] at hrj; rw [hEvalA i j]
      have hWeq : W (ind2 r j) = W (ind2 i j) := hW_agree _ _ (fun w _ hrw => by
        have h1 : w ≠ i.val := fun e => hnf (e ▸ hrw)
        have h2 : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
        simp [ind2, h1, h2])
      have hPsieq : Psi (W (ind2 r j)) (ind2 r j) = Psi (W (ind2 i j)) (ind2 i j) := by
        rw [hWeq]
        exact hPsi_agree _ _ _ (fun w _ hrw _ => by
          have h1 : w ≠ i.val := fun e => hnt (e ▸ hrw)
          have h2 : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrw)
          simp [ind2, h1, h2])
      rw [hPsieq, hWeq] at hrj
      exact hPhi_mono _ _ _ _ _ _ id id (fun w _ hnr _ _ h1 => by
        simp only [ind2, decide_eq_true_eq] at h1 ⊢
        rcases h1 with h1 | h1
        · exact (hnr h1).elim
        · exact Or.inr h1) hrj
  have hColReach_F : ∀ j : Fin m,
      ¬ ((∀ i, A i c = true → A i j = true) ∨ (∀ i, A i j = true → A i c = true)) →
      reaches N D L (n + j.val) (N + f.val) := by
    intro j hj
    by_contra hnf
    by_cases hnt : reaches N D L (n + j.val) (N + t.val)
    · apply hj; right; intro i hij
      rw [hEvalA i j] at hij; rw [hEvalA i c]
      have hWeq : W (ind2 i j) = W (ind2 i c) := hW_agree _ _ (fun w _ hrw => by
        have h1 : w ≠ n + j.val := fun e => hnf (e ▸ hrw)
        have h2 : w ≠ n + c.val := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hrw)
        simp [ind2, h1, h2])
      have hPsiLe : Psi (W (ind2 i c)) (ind2 i c) = true → Psi (W (ind2 i j)) (ind2 i j) = true := by
        rw [hWeq]
        exact hPsi_mono _ _ _ _ id (fun w _ hrw _ h1 => by
          have hwc : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrw)
          simp only [ind2, decide_eq_true_eq] at h1 ⊢
          rcases h1 with h1 | h1
          · exact Or.inl h1
          · exact (hwc h1).elim)
      have hNotLe : (! Psi (W (ind2 i j)) (ind2 i j)) = true → (! Psi (W (ind2 i c)) (ind2 i c)) = true := by
        intro h
        rw [Bool.not_eq_true'] at h ⊢
        exact Bool.eq_false_iff.mpr (fun ht => by have := hPsiLe ht; rw [this] at h; cases h)
      exact hPhi_mono _ _ _ _ (ind2 i j) (ind2 i c) (fun h => hWeq ▸ h) hNotLe (fun w _ _ hnc hwn h1 => by
        have hwj : w ≠ n + j.val := fun e => hwn (e ▸ hnt)
        simp only [ind2, decide_eq_true_eq] at h1 ⊢
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact (hwj h1).elim) hij
    · apply hj; left; intro i hic
      rw [hEvalA i c] at hic; rw [hEvalA i j]
      have hWeq : W (ind2 i c) = W (ind2 i j) := hW_agree _ _ (fun w _ hrw => by
        have h1 : w ≠ n + j.val := fun e => hnf (e ▸ hrw)
        have h2 : w ≠ n + c.val := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hrw)
        simp [ind2, h1, h2])
      have hPsieq : Psi (W (ind2 i c)) (ind2 i c) = Psi (W (ind2 i j)) (ind2 i j) := by
        rw [hWeq]
        exact hPsi_agree _ _ _ (fun w _ hrw _ => by
          have h1 : w ≠ n + j.val := fun e => hnt (e ▸ hrw)
          have h2 : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrw)
          simp [ind2, h1, h2])
      rw [hPsieq, hWeq] at hic
      exact hPhi_mono _ _ _ _ _ _ id id (fun w _ _ hnc _ h1 => by
        simp only [ind2, decide_eq_true_eq] at h1 ⊢
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact (hnc h1).elim) hic
  obtain ⟨u, huIncomp⟩ := hRowIncomp r
  obtain ⟨v, hvIncomp⟩ := hColIncomp c
  have huReachF : reaches N D L u.val (N + f.val) := hRowReach_F u huIncomp
  have hvReachF : reaches N D L (n + v.val) (N + f.val) := hColReach_F v hvIncomp
  have hru : r ≠ u := fun e => hrNoReach (N + f.val) (by omega) (e ▸ huReachF)
  have hcv : c ≠ v := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hvReachF)
  have hWu : W (sing u.val) = true := by
    by_contra hWuf
    have hWuf' : W (sing u.val) = false := Bool.eq_false_iff.mpr hWuf
    let b0 := Phi false true zeroX
    let b1 := Phi true (! Psi true zeroX) zeroX
    have hCase : ∀ j : Fin m, A u j = A r j ∨ (A r j = b0 ∧ A u j = b1) := by
      intro j
      by_cases hjF : reaches N D L (n + j.val) (N + f.val)
      · have hjT : reaches N D L (n + j.val) (N + t.val) := hjF.trans hfReachT
        have huT : reaches N D L u.val (N + t.val) := huReachF.trans hfReachT
        have hPsi_u : ∀ b, Psi b (ind2 u j) = Psi b zeroX := fun b =>
          hPsi_agree b _ _ (fun w _ _ hnf => by
            have h1 : w ≠ u.val := fun e => hnf (e ▸ huReachF)
            have h2 : w ≠ n + j.val := fun e => hnf (e ▸ hjF)
            simp [ind2, zeroX, h1, h2])
        have hPsi_r : ∀ b, Psi b (ind2 r j) = Psi b zeroX := fun b =>
          hPsi_agree b _ _ (fun w _ hrw hnf => by
            have h1 : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrw)
            have h2 : w ≠ n + j.val := fun e => hnf (e ▸ hjF)
            simp [ind2, zeroX, h1, h2])
        have hPhi_u : ∀ c1 c2, Phi c1 c2 (ind2 u j) = Phi c1 c2 zeroX := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ _ _ hnt => by
            have h1 : w ≠ u.val := fun e => hnt (e ▸ huT)
            have h2 : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
            simp [ind2, zeroX, h1, h2])
        have hPhi_r : ∀ c1 c2, Phi c1 c2 (ind2 r j) = Phi c1 c2 zeroX := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ hnr _ hnt => by
            have h2 : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
            simp [ind2, zeroX, hnr, h2])
        by_cases hWj : W (ind2 r j) = true
        · left
          have hWuj : W (ind2 u j) = true := hW_mono _ _ (fun w _ hrw h1 => by
            have hwr : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
            simp only [ind2, decide_eq_true_eq] at h1 ⊢
            rcases h1 with h1 | h1
            · exact (hwr h1).elim
            · exact Or.inr h1) hWj
          rw [hEvalA u j, hEvalA r j, hWuj, hWj, hPsi_u, hPsi_r, hPhi_u, hPhi_r]
        · have hWjf : W (ind2 r j) = false := Bool.eq_false_iff.mpr hWj
          cases hWuj : W (ind2 u j)
          · left
            rw [hEvalA u j, hEvalA r j, hWuj, hWjf, hPsi_u, hPsi_r, hPhi_u, hPhi_r]
          · right
            rw [hEvalA u j, hEvalA r j, hWuj, hWjf, hPsi_u, hPsi_r, hPsi_zero, hPhi_u, hPhi_r]
            exact ⟨rfl, rfl⟩
      · left
        have hWuj : W (ind2 u j) = false := by
          rw [← hWuf']
          exact hW_agree _ _ (fun w _ hrw => by
            have h2 : w ≠ n + j.val := fun e => hjF (e ▸ hrw)
            simp [ind2, sing, h2])
        have hWrj : W (ind2 r j) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have h1 : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
            have h2 : w ≠ n + j.val := fun e => hjF (e ▸ hrw)
            simp [ind2, zeroX, h1, h2])
        have hPsieq : Psi false (ind2 u j) = Psi false (ind2 r j) :=
          hPsi_agree false _ _ (fun w _ hrw hnf => by
            have h1 : w ≠ u.val := fun e => hnf (e ▸ huReachF)
            have h2 : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrw)
            simp [ind2, h1, h2])
        have huT : reaches N D L u.val (N + t.val) := huReachF.trans hfReachT
        have hPhieq : ∀ c1 c2, Phi c1 c2 (ind2 u j) = Phi c1 c2 (ind2 r j) := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ hnr _ hnt => by
            have h1 : w ≠ u.val := fun e => hnt (e ▸ huT)
            simp [ind2, h1, hnr])
        rw [hEvalA u j, hEvalA r j, hWuj, hWrj, hPsieq, hPhieq]
    cases hb0 : b0
    · apply huIncomp; left; intro j hrj
      rcases hCase j with heq | ⟨hr0, _⟩
      · exact heq.trans hrj
      · rw [hb0] at hr0; rw [hr0] at hrj; cases hrj
    · apply huIncomp; right; intro j huj
      rcases hCase j with heq | ⟨hr0, _⟩
      · exact heq.symm.trans huj
      · exact hr0.trans hb0
  have hWv : W (sing (n + v.val)) = true := by
    by_contra hWvf
    have hWvf' : W (sing (n + v.val)) = false := Bool.eq_false_iff.mpr hWvf
    let b0 := Phi false true zeroX
    let b1 := Phi true (! Psi true zeroX) zeroX
    have hCase : ∀ i : Fin n, A i v = A i c ∨ (A i c = b0 ∧ A i v = b1) := by
      intro i
      by_cases hiF : reaches N D L i.val (N + f.val)
      · have hiT : reaches N D L i.val (N + t.val) := hiF.trans hfReachT
        have hvT : reaches N D L (n + v.val) (N + t.val) := hvReachF.trans hfReachT
        have hPsi_v : ∀ b, Psi b (ind2 i v) = Psi b zeroX := fun b =>
          hPsi_agree b _ _ (fun w _ _ hnf => by
            have h1 : w ≠ i.val := fun e => hnf (e ▸ hiF)
            have h2 : w ≠ n + v.val := fun e => hnf (e ▸ hvReachF)
            simp [ind2, zeroX, h1, h2])
        have hPsi_c : ∀ b, Psi b (ind2 i c) = Psi b zeroX := fun b =>
          hPsi_agree b _ _ (fun w _ hrw hnf => by
            have h1 : w ≠ i.val := fun e => hnf (e ▸ hiF)
            have h2 : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrw)
            simp [ind2, zeroX, h1, h2])
        have hPhi_v : ∀ c1 c2, Phi c1 c2 (ind2 i v) = Phi c1 c2 zeroX := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ _ _ hnt => by
            have h1 : w ≠ i.val := fun e => hnt (e ▸ hiT)
            have h2 : w ≠ n + v.val := fun e => hnt (e ▸ hvT)
            simp [ind2, zeroX, h1, h2])
        have hPhi_c : ∀ c1 c2, Phi c1 c2 (ind2 i c) = Phi c1 c2 zeroX := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ _ hnc hnt => by
            have h1 : w ≠ i.val := fun e => hnt (e ▸ hiT)
            simp [ind2, zeroX, h1, hnc])
        by_cases hWi : W (ind2 i c) = true
        · left
          have hWiv : W (ind2 i v) = true := hW_mono _ _ (fun w _ hrw h1 => by
            have hwc : w ≠ n + c.val := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hrw)
            simp only [ind2, decide_eq_true_eq] at h1 ⊢
            rcases h1 with h1 | h1
            · exact Or.inl h1
            · exact (hwc h1).elim) hWi
          rw [hEvalA i v, hEvalA i c, hWiv, hWi, hPsi_v, hPsi_c, hPhi_v, hPhi_c]
        · have hWif : W (ind2 i c) = false := Bool.eq_false_iff.mpr hWi
          cases hWiv : W (ind2 i v)
          · left
            rw [hEvalA i v, hEvalA i c, hWiv, hWif, hPsi_v, hPsi_c, hPhi_v, hPhi_c]
          · right
            rw [hEvalA i v, hEvalA i c, hWiv, hWif, hPsi_v, hPsi_c, hPsi_zero, hPhi_v, hPhi_c]
            exact ⟨rfl, rfl⟩
      · left
        have hWiv : W (ind2 i v) = false := by
          rw [← hWvf']
          exact hW_agree _ _ (fun w _ hrw => by
            have h1 : w ≠ i.val := fun e => hiF (e ▸ hrw)
            simp [ind2, sing, h1])
        have hWic : W (ind2 i c) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have h1 : w ≠ i.val := fun e => hiF (e ▸ hrw)
            have h2 : w ≠ n + c.val := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hrw)
            simp [ind2, zeroX, h1, h2])
        have hPsieq : Psi false (ind2 i v) = Psi false (ind2 i c) :=
          hPsi_agree false _ _ (fun w _ hrw hnf => by
            have h1 : w ≠ n + v.val := fun e => hnf (e ▸ hvReachF)
            have h2 : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrw)
            simp [ind2, h1, h2])
        have hvT : reaches N D L (n + v.val) (N + t.val) := hvReachF.trans hfReachT
        have hPhieq : ∀ c1 c2, Phi c1 c2 (ind2 i v) = Phi c1 c2 (ind2 i c) := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ _ hnc hnt => by
            have h2 : w ≠ n + v.val := fun e => hnt (e ▸ hvT)
            simp [ind2, h2, hnc])
        rw [hEvalA i v, hEvalA i c, hWiv, hWic, hPsieq, hPhieq]
    cases hb0 : b0
    · apply hvIncomp; left; intro i hic
      rcases hCase i with heq | ⟨hc0, _⟩
      · exact heq.trans hic
      · rw [hb0] at hc0; rw [hc0] at hic; cases hic
    · apply hvIncomp; right; intro i hiv
      rcases hCase i with heq | ⟨hc0, _⟩
      · exact heq.symm.trans hiv
      · exact hc0.trans hb0
  have hW_of_u : ∀ j : Fin m, W (ind2 u j) = true := fun j =>
    hW_mono _ _ (fun w _ _ h => by simp only [sing, ind2, decide_eq_true_eq] at h ⊢; exact Or.inl h) hWu
  have hW_of_v : ∀ i : Fin n, W (ind2 i v) = true := fun i =>
    hW_mono _ _ (fun w _ _ h => by simp only [sing, ind2, decide_eq_true_eq] at h ⊢; exact Or.inr h) hWv
  have hPhi_10 : Phi true false zeroX = false := by
    by_contra h10
    have h10' : Phi true false zeroX = true := Bool.eq_true_of_not_eq_false h10
    obtain ⟨k, hk⟩ := hRowIncomp u
    apply hk; right; intro j _
    rw [hEvalA u j, hW_of_u j]
    exact hPhi_mono true false true (! Psi true (ind2 u j)) zeroX (ind2 u j)
      id (fun h => by cases h) (fun _ _ _ _ _ h => by simp [zeroX] at h) h10'
  have hPhi_01 : Phi false true zeroX = false := by
    by_contra h01
    have h01' : Phi false true zeroX = true := Bool.eq_true_of_not_eq_false h01
    apply huIncomp; right; intro j huj
    by_contra hrjf
    have hrj : A r j = false := Bool.eq_false_iff.mpr hrjf
    have hPsi_r_true : Psi (W (ind2 r j)) (ind2 r j) = true := by
      by_contra hpf
      have hpf' : Psi (W (ind2 r j)) (ind2 r j) = false := Bool.eq_false_iff.mpr hpf
      have ht : A r j = true := by
        rw [hEvalA r j, hpf']
        exact hPhi_mono false true (W (ind2 r j)) true zeroX (ind2 r j)
          (fun h => by cases h) id (fun _ _ _ _ _ h => by simp [zeroX] at h) h01'
      rw [hrj] at ht; cases ht
    have hjT : reaches N D L (n + j.val) (N + t.val) := by
      by_contra hnjT
      have hnjF : ¬ reaches N D L (n + j.val) (N + f.val) := fun h => hnjT (h.trans hfReachT)
      have hWrj : W (ind2 r j) = false := by
        rw [← hW_zero]
        exact hW_agree _ _ (fun w _ hrw => by
          have h1 : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
          have h2 : w ≠ n + j.val := fun e => hnjF (e ▸ hrw)
          simp [ind2, zeroX, h1, h2])
      have hPsir : Psi false (ind2 r j) = false :=
        (hPsi_agree false _ _ (fun w _ hrw _ => by
          have h1 : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrw)
          have h2 : w ≠ n + j.val := fun e => hnjT (e ▸ hrw)
          simp [ind2, zeroX, h1, h2])).trans hPsi_zero
      rw [hWrj, hPsir] at hPsi_r_true; cases hPsi_r_true
    have hPsi_u_true : Psi true (ind2 u j) = true := by
      refine hPsi_mono (W (ind2 r j)) true (ind2 r j) (ind2 u j) (fun _ => rfl) ?_ hPsi_r_true
      intro w _ hrw _ h1
      have hwr : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrw)
      simp only [ind2, decide_eq_true_eq] at h1 ⊢
      rcases h1 with h1 | h1
      · exact (hwr h1).elim
      · exact Or.inr h1
    have huT : reaches N D L u.val (N + t.val) := huReachF.trans hfReachT
    have hAuj_f : A u j = false := by
      rw [hEvalA u j, hW_of_u j, hPsi_u_true]
      simp only [Bool.not_true]
      exact (hPhi_agree true false _ _ (fun w _ _ _ hnt => by
        have h1 : w ≠ u.val := fun e => hnt (e ▸ huT)
        have h2 : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
        simp [ind2, zeroX, h1, h2])).trans hPhi_10
    rw [hAuj_f] at huj; cases huj
  have hPsi_10 : Psi true zeroX = true := by
    by_contra hp10
    have hp10' : Psi true zeroX = false := Bool.eq_false_iff.mpr hp10
    apply huIncomp; left; intro j hrj
    by_cases hjT : reaches N D L (n + j.val) (N + t.val) ∧ ¬ reaches N D L (n + j.val) (N + f.val)
    · have hWrj : W (ind2 r j) = false := by
        rw [← hW_zero]
        exact hW_agree _ _ (fun w _ hrw => by
          have h1 : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
          have h2 : w ≠ n + j.val := fun e => hjT.2 (e ▸ hrw)
          simp [ind2, zeroX, h1, h2])
      have hArj_f : A r j = false := by
        rw [hEvalA r j, hWrj]
        by_contra htr
        have htr' : Phi false (! Psi false (ind2 r j)) (ind2 r j) = true := Bool.eq_true_of_not_eq_false htr
        have h1 : Phi false true zeroX = true :=
          hPhi_mono false (! Psi false (ind2 r j)) false true (ind2 r j) zeroX
            id (fun _ => rfl) (fun w _ hnr _ hnt h => by
              have h2 : w ≠ n + j.val := fun e => hnt (e ▸ hjT.1)
              simp only [ind2, decide_eq_true_eq] at h
              rcases h with h | h
              · exact (hnr h).elim
              · exact (h2 h).elim) htr'
        rw [hPhi_01] at h1; cases h1
      rw [hArj_f] at hrj; cases hrj
    · have hPsir : Psi (W (ind2 r j)) (ind2 r j) = false := by
        by_contra htr
        have htr' : Psi (W (ind2 r j)) (ind2 r j) = true := Bool.eq_true_of_not_eq_false htr
        have h1 : Psi true zeroX = true :=
          hPsi_mono (W (ind2 r j)) true (ind2 r j) zeroX (fun _ => rfl) (fun w _ hrt hnf h => by
            have h1 : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrt)
            have h2 : w ≠ n + j.val := fun e => hjT ⟨e ▸ hrt, e ▸ hnf⟩
            simp only [ind2, decide_eq_true_eq] at h
            rcases h with h | h
            · exact (h1 h).elim
            · exact (h2 h).elim) htr'
        rw [hp10'] at h1; cases h1
      have hPsiu : Psi (W (ind2 u j)) (ind2 u j) = false := by
        by_contra htr
        have htr' : Psi (W (ind2 u j)) (ind2 u j) = true := Bool.eq_true_of_not_eq_false htr
        have h1 : Psi true zeroX = true :=
          hPsi_mono (W (ind2 u j)) true (ind2 u j) zeroX (fun _ => rfl) (fun w _ hrt hnf h => by
            have h1 : w ≠ u.val := fun e => hnf (e ▸ huReachF)
            have h2 : w ≠ n + j.val := fun e => hjT ⟨e ▸ hrt, e ▸ hnf⟩
            simp only [ind2, decide_eq_true_eq] at h
            rcases h with h | h
            · exact (h1 h).elim
            · exact (h2 h).elim) htr'
        rw [hp10'] at h1; cases h1
      rw [hEvalA r j, hPsir] at hrj
      rw [hEvalA u j, hPsiu, hW_of_u j]
      exact hPhi_mono (W (ind2 r j)) true true true (ind2 r j) (ind2 u j)
        (fun _ => rfl) id (fun w _ hnr _ _ h => by
          simp only [ind2, decide_eq_true_eq] at h ⊢
          rcases h with h | h
          · exact (hnr h).elim
          · exact Or.inr h) hrj
  have hZeroCorner : ∀ b : Bool, Phi b (! Psi b zeroX) zeroX = false := by
    intro b
    cases b
    · rw [hPsi_zero]; exact hPhi_01
    · rw [hPsi_10]; exact hPhi_10
  have hOnlyRowF : ∀ x : Fin n, reaches N D L x.val (N + f.val) → x = u := by
    intro x hxF
    by_contra hxu
    have hxr : x ≠ r := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hxF)
    have hxT : reaches N D L x.val (N + t.val) := hxF.trans hfReachT
    have huT : reaches N D L u.val (N + t.val) := huReachF.trans hfReachT
    cases hWx : W (sing x.val)
    · apply hxr
      apply hRowInj
      funext j
      by_cases hjF : reaches N D L (n + j.val) (N + f.val)
      · have hjT : reaches N D L (n + j.val) (N + t.val) := hjF.trans hfReachT
        have h1 : A x j = false := by
          rw [hEvalA x j]
          have hp : Psi (W (ind2 x j)) (ind2 x j) = Psi (W (ind2 x j)) zeroX :=
            hPsi_agree _ _ _ (fun w _ _ hnf => by
              have ha : w ≠ x.val := fun e => hnf (e ▸ hxF)
              have hb : w ≠ n + j.val := fun e => hnf (e ▸ hjF)
              simp [ind2, zeroX, ha, hb])
          have hph : Phi (W (ind2 x j)) (! Psi (W (ind2 x j)) zeroX) (ind2 x j) =
              Phi (W (ind2 x j)) (! Psi (W (ind2 x j)) zeroX) zeroX :=
            hPhi_agree _ _ _ _ (fun w _ _ _ hnt => by
              have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
              have hb : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
              simp [ind2, zeroX, ha, hb])
          rw [hp, hph]; exact hZeroCorner _
        have h2 : A r j = false := by
          rw [hEvalA r j]
          have hp : Psi (W (ind2 r j)) (ind2 r j) = Psi (W (ind2 r j)) zeroX :=
            hPsi_agree _ _ _ (fun w _ hrt hnf => by
              have ha : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrt)
              have hb : w ≠ n + j.val := fun e => hnf (e ▸ hjF)
              simp [ind2, zeroX, ha, hb])
          have hph : Phi (W (ind2 r j)) (! Psi (W (ind2 r j)) zeroX) (ind2 r j) =
              Phi (W (ind2 r j)) (! Psi (W (ind2 r j)) zeroX) zeroX :=
            hPhi_agree _ _ _ _ (fun w _ hnr _ hnt => by
              have hb : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
              simp [ind2, zeroX, hnr, hb])
          rw [hp, hph]; exact hZeroCorner _
        rw [h1, h2]
      · have hWxj : W (ind2 x j) = false := by
          rw [← hWx]
          exact hW_agree _ _ (fun w _ hrw => by
            have hb : w ≠ n + j.val := fun e => hjF (e ▸ hrw)
            simp [ind2, sing, hb])
        have hWrj : W (ind2 r j) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
            have hb : w ≠ n + j.val := fun e => hjF (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        have hPsieq : Psi false (ind2 x j) = Psi false (ind2 r j) :=
          hPsi_agree false _ _ (fun w _ hrt hnf => by
            have ha : w ≠ x.val := fun e => hnf (e ▸ hxF)
            have hb : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrt)
            simp [ind2, ha, hb])
        have hPhieq : ∀ c1 c2, Phi c1 c2 (ind2 x j) = Phi c1 c2 (ind2 r j) := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ hnr _ hnt => by
            have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
            simp [ind2, ha, hnr])
        rw [hEvalA x j, hEvalA r j, hWxj, hWrj, hPsieq, hPhieq]
    · apply hxu
      apply hRowInj
      funext j
      have hWxj : W (ind2 x j) = true :=
        hW_mono _ _ (fun w _ _ h => by simp only [sing, ind2, decide_eq_true_eq] at h ⊢; exact Or.inl h) hWx
      have hPsieq : Psi true (ind2 x j) = Psi true (ind2 u j) :=
        hPsi_agree true _ _ (fun w _ _ hnf => by
          have ha : w ≠ x.val := fun e => hnf (e ▸ hxF)
          have hb : w ≠ u.val := fun e => hnf (e ▸ huReachF)
          simp [ind2, ha, hb])
      have hPhieq : ∀ c1 c2, Phi c1 c2 (ind2 x j) = Phi c1 c2 (ind2 u j) := fun c1 c2 =>
        hPhi_agree c1 c2 _ _ (fun w _ _ _ hnt => by
          have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
          have hb : w ≠ u.val := fun e => hnt (e ▸ huT)
          simp [ind2, ha, hb])
      rw [hEvalA x j, hEvalA u j, hWxj, hW_of_u j, hPsieq, hPhieq]
  have hOnlyColF : ∀ y : Fin m, reaches N D L (n + y.val) (N + f.val) → y = v := by
    intro y hyF
    by_contra hyv
    have hyc : y ≠ c := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hyF)
    have hyT : reaches N D L (n + y.val) (N + t.val) := hyF.trans hfReachT
    have hvT : reaches N D L (n + v.val) (N + t.val) := hvReachF.trans hfReachT
    cases hWy : W (sing (n + y.val))
    · apply hyc
      apply hColInj
      funext i
      dsimp only
      by_cases hiF : reaches N D L i.val (N + f.val)
      · have hiT : reaches N D L i.val (N + t.val) := hiF.trans hfReachT
        have h1 : A i y = false := by
          rw [hEvalA i y]
          have hp : Psi (W (ind2 i y)) (ind2 i y) = Psi (W (ind2 i y)) zeroX :=
            hPsi_agree _ _ _ (fun w _ _ hnf => by
              have ha : w ≠ i.val := fun e => hnf (e ▸ hiF)
              have hb : w ≠ n + y.val := fun e => hnf (e ▸ hyF)
              simp [ind2, zeroX, ha, hb])
          have hph : Phi (W (ind2 i y)) (! Psi (W (ind2 i y)) zeroX) (ind2 i y) =
              Phi (W (ind2 i y)) (! Psi (W (ind2 i y)) zeroX) zeroX :=
            hPhi_agree _ _ _ _ (fun w _ _ _ hnt => by
              have ha : w ≠ i.val := fun e => hnt (e ▸ hiT)
              have hb : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
              simp [ind2, zeroX, ha, hb])
          rw [hp, hph]; exact hZeroCorner _
        have h2 : A i c = false := by
          rw [hEvalA i c]
          have hp : Psi (W (ind2 i c)) (ind2 i c) = Psi (W (ind2 i c)) zeroX :=
            hPsi_agree _ _ _ (fun w _ hrt hnf => by
              have ha : w ≠ i.val := fun e => hnf (e ▸ hiF)
              have hb : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrt)
              simp [ind2, zeroX, ha, hb])
          have hph : Phi (W (ind2 i c)) (! Psi (W (ind2 i c)) zeroX) (ind2 i c) =
              Phi (W (ind2 i c)) (! Psi (W (ind2 i c)) zeroX) zeroX :=
            hPhi_agree _ _ _ _ (fun w _ _ hnc hnt => by
              have ha : w ≠ i.val := fun e => hnt (e ▸ hiT)
              simp [ind2, zeroX, ha, hnc])
          rw [hp, hph]; exact hZeroCorner _
        rw [h1, h2]
      · have hWiy : W (ind2 i y) = false := by
          rw [← hWy]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ i.val := fun e => hiF (e ▸ hrw)
            simp [ind2, sing, ha])
        have hWic : W (ind2 i c) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ i.val := fun e => hiF (e ▸ hrw)
            have hb : w ≠ n + c.val := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        have hPsieq : Psi false (ind2 i y) = Psi false (ind2 i c) :=
          hPsi_agree false _ _ (fun w _ hrt hnf => by
            have ha : w ≠ n + y.val := fun e => hnf (e ▸ hyF)
            have hb : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrt)
            simp [ind2, ha, hb])
        have hPhieq : ∀ c1 c2, Phi c1 c2 (ind2 i y) = Phi c1 c2 (ind2 i c) := fun c1 c2 =>
          hPhi_agree c1 c2 _ _ (fun w _ _ hnc hnt => by
            have ha : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
            simp [ind2, ha, hnc])
        rw [hEvalA i y, hEvalA i c, hWiy, hWic, hPsieq, hPhieq]
    · apply hyv
      apply hColInj
      funext i
      dsimp only
      have hWiy : W (ind2 i y) = true :=
        hW_mono _ _ (fun w _ _ h => by simp only [sing, ind2, decide_eq_true_eq] at h ⊢; exact Or.inr h) hWy
      have hPsieq : Psi true (ind2 i y) = Psi true (ind2 i v) :=
        hPsi_agree true _ _ (fun w _ _ hnf => by
          have ha : w ≠ n + y.val := fun e => hnf (e ▸ hyF)
          have hb : w ≠ n + v.val := fun e => hnf (e ▸ hvReachF)
          simp [ind2, ha, hb])
      have hPhieq : ∀ c1 c2, Phi c1 c2 (ind2 i y) = Phi c1 c2 (ind2 i v) := fun c1 c2 =>
        hPhi_agree c1 c2 _ _ (fun w _ _ _ hnt => by
          have ha : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
          have hb : w ≠ n + v.val := fun e => hnt (e ▸ hvT)
          simp [ind2, ha, hb])
      rw [hEvalA i y, hEvalA i v, hWiy, hW_of_v i, hPsieq, hPhieq]
  have hInF_eq : (Finset.range N).filter (fun w => reaches N D L w (N + f.val)) = {u.val, n + v.val} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hw, hrw⟩
      by_cases h1 : w < n
      · left; exact congrArg Fin.val (hOnlyRowF ⟨w, h1⟩ hrw)
      · right
        have h2 : w - n < m := by omega
        have he : n + (w - n) = w := by omega
        have := congrArg Fin.val (hOnlyColF ⟨w - n, h2⟩ (he.symm ▸ hrw))
        dsimp only at this; omega
    · rintro (rfl | rfl)
      · exact ⟨by have := u.isLt; omega, huReachF⟩
      · exact ⟨by have := v.isLt; omega, hvReachF⟩
  have hFset_eq : Fset = {f.val} := by
    have hWiresF : ∀ j ∈ Fset, ∀ w ∈ (gateAt D j).inputs,
        w ∈ ({u.val, n + v.val} : Finset ℕ) ∪ (Fset.erase f.val).image (N + ·) := by
      intro j hj w hw
      have hjL := hFsub hj
      have hlt := hback j (Finset.mem_range.mp hjL) w hw
      have hrw : reaches N D L w (N + f.val) :=
        Relation.ReflTransGen.head ⟨j, hjL, rfl, hw, hlt⟩ ((hmemF j).mp hj)
      by_cases hwn : w < N
      · rw [Finset.mem_union, ← hInF_eq]
        exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hrw⟩)
      · rw [Finset.mem_union]
        right
        refine Finset.mem_image.mpr ⟨w - N, Finset.mem_erase.mpr ⟨?_, ?_⟩, by omega⟩
        · have hjle := reachIncreases ((hmemF j).mp hj)
          omega
        · exact (hmemF (w - N)).mpr (by rwa [show N + (w - N) = w by omega])
    let S_F : Finset ℕ := ({u.val, n + v.val} : Finset ℕ) ∪ (Fset.erase f.val).image (N + ·)
    have hsum1 : ∑ j ∈ Fset, (gateAt D j).inputs.length = 2 * Fset.card := by
      calc ∑ j ∈ Fset, (gateAt D j).inputs.length
          = ∑ _j ∈ Fset, 2 := Finset.sum_congr rfl (fun j hj =>
              (hnot_gate_and_or j (hFsub hj) (fun e => htNotF (e ▸ hj))).2)
        _ = Fset.card * 2 := by simp
        _ = 2 * Fset.card := Nat.mul_comm _ _
    have hsum2 : ∑ j ∈ Fset, (gateAt D j).inputs.length = ∑ w ∈ S_F, readsIn D Fset w := by
      unfold readsIn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hsub : (gateAt D j).inputs.toFinset ⊆ S_F := fun w hw => hWiresF j hj w (List.mem_toFinset.mp hw)
      have hnd := hnodup j (Finset.mem_range.mp (hFsub hj))
      have h1 : ∑ w ∈ S_F, (gateAt D j).inputs.count w = ∑ w ∈ (gateAt D j).inputs.toFinset, (gateAt D j).inputs.count w := by
        symm
        refine Finset.sum_subset hsub ?_
        intro w _ hwn
        exact List.count_eq_zero.mpr (fun hm => hwn (List.mem_toFinset.mpr hm))
      rw [h1]
      have h2 : ∑ w ∈ (gateAt D j).inputs.toFinset, (gateAt D j).inputs.count w = (gateAt D j).inputs.toFinset.card := by
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro w hw
        have hm := List.mem_toFinset.mp hw
        have hpos := List.count_pos_iff.mpr hm
        have hle := List.nodup_iff_count_le_one.mp hnd w
        omega
      rw [h2, List.toFinset_card_of_nodup hnd]
    have hsum3 : ∑ w ∈ S_F, readsIn D Fset w ≤ S_F.card := by
      calc ∑ w ∈ S_F, readsIn D Fset w
          ≤ ∑ _w ∈ S_F, 1 := Finset.sum_le_sum (fun w hw => by
            have hne : w ≠ N + f.val := by
              simp only [S_F, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image, Finset.mem_erase] at hw
              rcases hw with (rfl | rfl) | ⟨a, ⟨haf, _⟩, rfl⟩
              · have := u.isLt; omega
              · have := v.isLt; omega
              · omega
            have hle1 : readsIn D Fset w ≤ readsIn D L w :=
              Finset.sum_le_sum_of_subset_of_nonneg hFsub (fun _ _ _ => Nat.zero_le _)
            exact hle1.trans (hreads_le_one w hne))
        _ = S_F.card := by simp
    have hScard : S_F.card ≤ 2 + (Fset.card - 1) := by
      have h1 : S_F.card ≤ ({u.val, n + v.val} : Finset ℕ).card + ((Fset.erase f.val).image (N + ·)).card :=
        Finset.card_union_le _ _
      have h2 : ({u.val, n + v.val} : Finset ℕ).card ≤ 2 := Finset.card_le_two
      have h3 : ((Fset.erase f.val).image (N + ·)).card ≤ (Fset.erase f.val).card := Finset.card_image_le
      have hfF : f.val ∈ Fset := Finset.mem_insert_self _ _
      have h4 : (Fset.erase f.val).card = Fset.card - 1 := Finset.card_erase_of_mem hfF
      omega
    have hfF : f.val ∈ Fset := Finset.mem_insert_self _ _
    have hFpos : 1 ≤ Fset.card := Finset.card_pos.mpr ⟨f.val, hfF⟩
    have hF1 : Fset.card = 1 := by omega
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hfF, fun x hx =>
      Finset.card_le_one.mp (le_of_eq hF1) x hx f.val hfF⟩
  have hfInputs : (gateAt D f.val).inputs = [u.val, n + v.val] ∨
      (gateAt D f.val).inputs = [n + v.val, u.val] := by
    have hlen := (hnot_gate_and_or f.val (Finset.mem_range.mpr f.isLt) (by have : f.val < t.val := hft; omega)).2
    have hnd := hnodup f.val f.isLt
    have hmem : ∀ w ∈ (gateAt D f.val).inputs, w = u.val ∨ w = n + v.val := by
      intro w hw
      have hlt := hback f.val f.isLt w hw
      have hrw : reaches N D L w (N + f.val) :=
        Relation.ReflTransGen.single ⟨f.val, Finset.mem_range.mpr f.isLt, rfl, hw, hlt⟩
      by_cases hwn : w < N
      · have h1 : w ∈ ({u.val, n + v.val} : Finset ℕ) := by
          rw [← hInF_eq]
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hrw⟩
        simpa using h1
      · have h2 : w - N ∈ Fset := (hmemF (w - N)).mpr (by rwa [show N + (w - N) = w by omega])
        rw [hFset_eq, Finset.mem_singleton] at h2
        omega
    rcases hl : (gateAt D f.val).inputs with _ | ⟨a, _ | ⟨b, tl⟩⟩
    · simp [hl] at hlen
    · simp [hl] at hlen
    · cases tl with
      | cons _ _ => simp [hl] at hlen
      | nil =>
        have hab : a ≠ b := by rw [hl, List.nodup_cons] at hnd; simpa using hnd.1
        rcases hmem a (by simp [hl]) with rfl | rfl <;>
        rcases hmem b (by simp [hl]) with rfl | rfl
        · exact (hab rfl).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hab rfl).elim
  have hfOp : (gateAt D f.val).op = .or := by
    have hop := (hnot_gate_and_or f.val (Finset.mem_range.mpr f.isLt) (by have : f.val < t.val := hft; omega)).1
    rcases hop with hand | hor
    · exfalso
      have h1 := hWu
      dsimp only [W] at h1
      rw [val_gate f.isLt rfl, hand] at h1
      have huv : u.val ≠ n + v.val := by have := u.isLt; omega
      have hult : u.val < N + f.val := by have := u.isLt; omega
      have hvlt : n + v.val < N + f.val := by have := v.isLt; omega
      have hu_raw : value N D (sing u.val) (fun _ => none) u.val = true := by
        rw [val_raw (by have := u.isLt; omega) rfl]; simp [sing]
      have hv_raw : value N D (sing u.val) (fun _ => none) (n + v.val) = false := by
        rw [val_raw (by have := v.isLt; omega) rfl]; simp [sing, huv.symm]
      rcases hfInputs with h | h <;> rw [h] at h1
      · simp [GateOp.eval, hult, hvlt, hu_raw, hv_raw] at h1
      · simp [GateOp.eval, hult, hvlt, hu_raw, hv_raw] at h1
    · exact hor
  have hNoHidRow : ∀ x : Fin n, reaches N D L x.val (N + t.val) → ¬ reaches N D L x.val (N + f.val) → False := by
    intro x hxT hxnF
    have hxr : x ≠ r := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hxT)
    have hxu : x ≠ u := fun e => hxnF (e ▸ huReachF)
    cases hpx : Psi false (sing x.val)
    · apply hxr
      apply hRowInj
      funext j
      by_cases hjv : j = v
      · subst j
        have hW1 : W (ind2 x v) = true := hW_of_v x
        have hW2 : W (ind2 r v) = true := hW_of_v r
        have hP1 : Psi true (ind2 x v) = true := hPsi_mono true true zeroX _ id (fun _ _ _ _ h => by simp [zeroX] at h) hPsi_10
        have hP2 : Psi true (ind2 r v) = true := hPsi_mono true true zeroX _ id (fun _ _ _ _ h => by simp [zeroX] at h) hPsi_10
        have hvT : reaches N D L (n + v.val) (N + t.val) := hvReachF.trans hfReachT
        have hPh : Phi true false (ind2 x v) = Phi true false (ind2 r v) :=
          hPhi_agree true false _ _ (fun w _ hnr _ hnt => by
            have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
            simp [ind2, ha, hnr])
        rw [hEvalA x v, hEvalA r v, hW1, hW2, hP1, hP2, Bool.not_true, hPh]
      · have hjnf : ¬ reaches N D L (n + j.val) (N + f.val) := fun h => hjv (hOnlyColF j h)
        have hWx : W (ind2 x j) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ x.val := fun e => hxnF (e ▸ hrw)
            have hb : w ≠ n + j.val := fun e => hjnf (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        have hWr : W (ind2 r j) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ r.val := fun e => hrNoReach (N + f.val) (by omega) (e ▸ hrw)
            have hb : w ≠ n + j.val := fun e => hjnf (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        by_cases hjT : reaches N D L (n + j.val) (N + t.val)
        · have h1 : A x j = false := by
            rw [hEvalA x j, hWx]
            by_contra htr
            have htr' := Bool.eq_true_of_not_eq_false htr
            have h01 := hPhi_mono false (! Psi false (ind2 x j)) false true (ind2 x j) zeroX
              id (fun _ => rfl) (fun w _ _ _ hnt h => by
                have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
                have hb : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
                simp only [ind2, decide_eq_true_eq] at h
                rcases h with h | h
                · exact (ha h).elim
                · exact (hb h).elim) htr'
            rw [hPhi_01] at h01; cases h01
          have h2 : A r j = false := by
            rw [hEvalA r j, hWr]
            by_contra htr
            have htr' := Bool.eq_true_of_not_eq_false htr
            have h01 := hPhi_mono false (! Psi false (ind2 r j)) false true (ind2 r j) zeroX
              id (fun _ => rfl) (fun w _ hnr _ hnt h => by
                have hb : w ≠ n + j.val := fun e => hnt (e ▸ hjT)
                simp only [ind2, decide_eq_true_eq] at h
                rcases h with h | h
                · exact (hnr h).elim
                · exact (hb h).elim) htr'
            rw [hPhi_01] at h01; cases h01
          rw [h1, h2]
        · have hP1 : Psi false (ind2 x j) = false :=
            (hPsi_agree false _ _ (fun w _ hrt _ => by
              have hb : w ≠ n + j.val := fun e => hjT (e ▸ hrt)
              simp [ind2, sing, hb])).trans hpx
          have hP2 : Psi false (ind2 r j) = false :=
            (hPsi_agree false _ _ (fun w _ hrt _ => by
              have ha : w ≠ r.val := fun e => hrNoReach (N + t.val) (by omega) (e ▸ hrt)
              have hb : w ≠ n + j.val := fun e => hjT (e ▸ hrt)
              simp [ind2, zeroX, ha, hb])).trans hPsi_zero
          have hPh : Phi false true (ind2 x j) = Phi false true (ind2 r j) :=
            hPhi_agree false true _ _ (fun w _ hnr _ hnt => by
              have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
              simp [ind2, ha, hnr])
          rw [hEvalA x j, hEvalA r j, hWx, hWr, hP1, hP2]
          exact hPh
    · obtain ⟨k, hk⟩ := hRowIncomp x
      apply hk; left; intro j hxj
      have hP1 : Psi (W (ind2 x j)) (ind2 x j) = true :=
        hPsi_mono false (W (ind2 x j)) (sing x.val) (ind2 x j) (fun h => by cases h)
          (fun w _ _ _ h => by simp only [sing, ind2, decide_eq_true_eq] at h ⊢; exact Or.inl h) hpx
      by_cases hjv : j = v
      · subst j
        rw [hEvalA x v, hP1, hW_of_v x] at hxj
        simp only [Bool.not_true] at hxj
        have hvT : reaches N D L (n + v.val) (N + t.val) := hvReachF.trans hfReachT
        have hph := hPhi_agree true false (ind2 x v) zeroX (fun w _ _ _ hnt => by
          have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
          have hb : w ≠ n + v.val := fun e => hnt (e ▸ hvT)
          simp [ind2, zeroX, ha, hb])
        rw [hph, hPhi_10] at hxj; cases hxj
      · have hjnf : ¬ reaches N D L (n + j.val) (N + f.val) := fun h => hjv (hOnlyColF j h)
        have hWx : W (ind2 x j) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ x.val := fun e => hxnF (e ▸ hrw)
            have hb : w ≠ n + j.val := fun e => hjnf (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        rw [hEvalA x j, hP1, hWx] at hxj
        simp only [Bool.not_true] at hxj
        rw [hEvalA k j]
        exact hPhi_mono false false (W (ind2 k j)) (! Psi (W (ind2 k j)) (ind2 k j)) (ind2 x j) (ind2 k j)
          (fun h => by cases h) (fun h => by cases h) (fun w _ _ _ hnt h => by
            have ha : w ≠ x.val := fun e => hnt (e ▸ hxT)
            simp only [ind2, decide_eq_true_eq] at h ⊢
            rcases h with h | h
            · exact (ha h).elim
            · exact Or.inr h) hxj
  have hNoHidCol : ∀ y : Fin m, reaches N D L (n + y.val) (N + t.val) → ¬ reaches N D L (n + y.val) (N + f.val) → False := by
    intro y hyT hynF
    have hyc : y ≠ c := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hyT)
    have hyv : y ≠ v := fun e => hynF (e ▸ hvReachF)
    cases hpy : Psi false (sing (n + y.val))
    · apply hyc
      apply hColInj
      funext i
      dsimp only
      by_cases hiu : i = u
      · subst i
        have hW1 : W (ind2 u y) = true := hW_of_u y
        have hW2 : W (ind2 u c) = true := hW_of_u c
        have hP1 : Psi true (ind2 u y) = true := hPsi_mono true true zeroX _ id (fun _ _ _ _ h => by simp [zeroX] at h) hPsi_10
        have hP2 : Psi true (ind2 u c) = true := hPsi_mono true true zeroX _ id (fun _ _ _ _ h => by simp [zeroX] at h) hPsi_10
        have huT : reaches N D L u.val (N + t.val) := huReachF.trans hfReachT
        have hPh : Phi true false (ind2 u y) = Phi true false (ind2 u c) :=
          hPhi_agree true false _ _ (fun w _ _ hnc hnt => by
            have ha : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
            simp [ind2, ha, hnc])
        rw [hEvalA u y, hEvalA u c, hW1, hW2, hP1, hP2]
        exact hPh
      · have hinf : ¬ reaches N D L i.val (N + f.val) := fun h => hiu (hOnlyRowF i h)
        have hWy : W (ind2 i y) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ i.val := fun e => hinf (e ▸ hrw)
            have hb : w ≠ n + y.val := fun e => hynF (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        have hWc : W (ind2 i c) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ i.val := fun e => hinf (e ▸ hrw)
            have hb : w ≠ n + c.val := fun e => hcNoReach (N + f.val) (by omega) (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        by_cases hiT : reaches N D L i.val (N + t.val)
        · have h1 : A i y = false := by
            rw [hEvalA i y, hWy]
            by_contra htr
            have htr' := Bool.eq_true_of_not_eq_false htr
            have h01 := hPhi_mono false (! Psi false (ind2 i y)) false true (ind2 i y) zeroX
              id (fun _ => rfl) (fun w _ _ _ hnt h => by
                have ha : w ≠ i.val := fun e => hnt (e ▸ hiT)
                have hb : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
                simp only [ind2, decide_eq_true_eq] at h
                rcases h with h | h
                · exact (ha h).elim
                · exact (hb h).elim) htr'
            rw [hPhi_01] at h01; cases h01
          have h2 : A i c = false := by
            rw [hEvalA i c, hWc]
            by_contra htr
            have htr' := Bool.eq_true_of_not_eq_false htr
            have h01 := hPhi_mono false (! Psi false (ind2 i c)) false true (ind2 i c) zeroX
              id (fun _ => rfl) (fun w _ _ hnc hnt h => by
                have ha : w ≠ i.val := fun e => hnt (e ▸ hiT)
                simp only [ind2, decide_eq_true_eq] at h
                rcases h with h | h
                · exact (ha h).elim
                · exact (hnc h).elim) htr'
            rw [hPhi_01] at h01; cases h01
          rw [h1, h2]
        · have hP1 : Psi false (ind2 i y) = false :=
            (hPsi_agree false _ _ (fun w _ hrt _ => by
              have ha : w ≠ i.val := fun e => hiT (e ▸ hrt)
              simp [ind2, sing, ha])).trans hpy
          have hP2 : Psi false (ind2 i c) = false :=
            (hPsi_agree false _ _ (fun w _ hrt _ => by
              have ha : w ≠ i.val := fun e => hiT (e ▸ hrt)
              have hb : w ≠ n + c.val := fun e => hcNoReach (N + t.val) (by omega) (e ▸ hrt)
              simp [ind2, zeroX, ha, hb])).trans hPsi_zero
          have hPh : Phi false true (ind2 i y) = Phi false true (ind2 i c) :=
            hPhi_agree false true _ _ (fun w _ _ hnc hnt => by
              have ha : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
              simp [ind2, ha, hnc])
          rw [hEvalA i y, hEvalA i c, hWy, hWc, hP1, hP2]
          exact hPh
    · obtain ⟨l, hl⟩ := hColIncomp y
      apply hl; left; intro i hiy
      have hP1 : Psi (W (ind2 i y)) (ind2 i y) = true :=
        hPsi_mono false (W (ind2 i y)) (sing (n + y.val)) (ind2 i y) (fun h => by cases h)
          (fun w _ _ _ h => by simp only [sing, ind2, decide_eq_true_eq] at h ⊢; exact Or.inr h) hpy
      by_cases hiu : i = u
      · subst i
        rw [hEvalA u y, hP1, hW_of_u y] at hiy
        simp only [Bool.not_true] at hiy
        have huT : reaches N D L u.val (N + t.val) := huReachF.trans hfReachT
        have hph := hPhi_agree true false (ind2 u y) zeroX (fun w _ _ _ hnt => by
          have ha : w ≠ u.val := fun e => hnt (e ▸ huT)
          have hb : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
          simp [ind2, zeroX, ha, hb])
        rw [hph, hPhi_10] at hiy; cases hiy
      · have hinf : ¬ reaches N D L i.val (N + f.val) := fun h => hiu (hOnlyRowF i h)
        have hWy : W (ind2 i y) = false := by
          rw [← hW_zero]
          exact hW_agree _ _ (fun w _ hrw => by
            have ha : w ≠ i.val := fun e => hinf (e ▸ hrw)
            have hb : w ≠ n + y.val := fun e => hynF (e ▸ hrw)
            simp [ind2, zeroX, ha, hb])
        rw [hEvalA i y, hP1, hWy] at hiy
        simp only [Bool.not_true] at hiy
        rw [hEvalA i l]
        exact hPhi_mono false false (W (ind2 i l)) (! Psi (W (ind2 i l)) (ind2 i l)) (ind2 i y) (ind2 i l)
          (fun h => by cases h) (fun h => by cases h) (fun w _ _ _ hnt h => by
            have hb : w ≠ n + y.val := fun e => hnt (e ▸ hyT)
            simp only [ind2, decide_eq_true_eq] at h ⊢
            rcases h with h | h
            · exact Or.inl h
            · exact (hb h).elim) hiy
  have hNoHid : ∀ w < N, reaches N D L w (N + t.val) → reaches N D L w (N + f.val) := by
    intro w hw hwt
    by_contra hwnf
    by_cases h1 : w < n
    · exact hNoHidRow ⟨w, h1⟩ hwt hwnf
    · have h2 : w - n < m := by omega
      have he : n + (w - n) = w := by omega
      exact hNoHidCol ⟨w - n, h2⟩ (he.symm ▸ hwt) (he.symm ▸ hwnf)
  let Tset : Finset ℕ := Q \ Fset
  have htTset : t.val ∈ Tset := Finset.mem_sdiff.mpr ⟨Finset.mem_insert_self _ _, htNotF⟩
  have hTset_eq : Tset = {t.val} := by
    have hTsubQ : Tset ⊆ Q := Finset.sdiff_subset
    have hTsubL : Tset ⊆ L := hTsubQ.trans hQsub
    have hWiresT : ∀ j ∈ Tset, ∀ w ∈ (gateAt D j).inputs,
        w ∈ insert (N + f.val) ((Tset.erase t.val).image (N + ·)) := by
      intro j hj w hw
      have hjQ := hTsubQ hj
      have hjL := hQsub hjQ
      have hjNotF : j ∉ Fset := (Finset.mem_sdiff.mp hj).2
      have hlt := hback j (Finset.mem_range.mp hjL) w hw
      have hrw : reaches N D L w (N + t.val) :=
        Relation.ReflTransGen.head ⟨j, hjL, rfl, hw, hlt⟩ ((hmemQ j).mp hjQ)
      by_cases hwn : w < N
      · exfalso
        have hrf := hNoHid w hwn hrw
        obtain ⟨z, ⟨k, hkL, rfl, hkm, _⟩, hkz⟩ := path_head hrf (by omega)
        have hjk : j = k := huniq w (by omega) j hjL k hkL hw hkm
        exact hjNotF (hjk ▸ (hmemF k).mpr hkz)
      · have haQ : w - N ∈ Q := hQclosed j hjQ (w - N) (by rwa [show N + (w - N) = w by omega])
        by_cases haF : w - N ∈ Fset
        · rw [hFset_eq, Finset.mem_singleton] at haF
          exact Finset.mem_insert.mpr (Or.inl (by omega))
        · have hat : w - N ≠ t.val := by
            have hjle := reachIncreases ((hmemQ j).mp hjQ)
            omega
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
            ⟨w - N, Finset.mem_erase.mpr ⟨hat, Finset.mem_sdiff.mpr ⟨haQ, haF⟩⟩, by omega⟩))
    let S_T : Finset ℕ := insert (N + f.val) ((Tset.erase t.val).image (N + ·))
    have hsum1 : ∑ j ∈ Tset, (gateAt D j).inputs.length = 2 * (Tset.card - 1) + 1 := by
      rw [← Finset.add_sum_erase Tset (fun j => (gateAt D j).inputs.length) htTset, htLen]
      have hrest : ∑ j ∈ Tset.erase t.val, (gateAt D j).inputs.length = 2 * (Tset.erase t.val).card := by
        calc ∑ j ∈ Tset.erase t.val, (gateAt D j).inputs.length
            = ∑ _j ∈ Tset.erase t.val, 2 := Finset.sum_congr rfl (fun j hj =>
                (hnot_gate_and_or j (hTsubL (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)).2)
          _ = (Tset.erase t.val).card * 2 := by simp
          _ = 2 * (Tset.erase t.val).card := Nat.mul_comm _ _
      rw [hrest, Finset.card_erase_of_mem htTset]
      omega
    have hsum2 : ∑ j ∈ Tset, (gateAt D j).inputs.length = ∑ w ∈ S_T, readsIn D Tset w := by
      unfold readsIn
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      have hsub : (gateAt D j).inputs.toFinset ⊆ S_T := fun w hw => hWiresT j hj w (List.mem_toFinset.mp hw)
      have hnd := hnodup j (Finset.mem_range.mp (hTsubL hj))
      have h1 : ∑ w ∈ S_T, (gateAt D j).inputs.count w = ∑ w ∈ (gateAt D j).inputs.toFinset, (gateAt D j).inputs.count w := by
        symm
        refine Finset.sum_subset hsub ?_
        intro w _ hwn
        exact List.count_eq_zero.mpr (fun hm => hwn (List.mem_toFinset.mpr hm))
      rw [h1]
      have h2 : ∑ w ∈ (gateAt D j).inputs.toFinset, (gateAt D j).inputs.count w = (gateAt D j).inputs.toFinset.card := by
        rw [Finset.card_eq_sum_ones]
        apply Finset.sum_congr rfl
        intro w hw
        have hm := List.mem_toFinset.mp hw
        have hpos := List.count_pos_iff.mpr hm
        have hle := List.nodup_iff_count_le_one.mp hnd w
        omega
      rw [h2, List.toFinset_card_of_nodup hnd]
    have hsum3 : ∑ w ∈ S_T, readsIn D Tset w ≤ S_T.card := by
      calc ∑ w ∈ S_T, readsIn D Tset w
          ≤ ∑ _w ∈ S_T, 1 := Finset.sum_le_sum (fun w hw => by
            by_cases hwf : w = N + f.val
            · subst hwf
              have hleQ : readsIn D Tset (N + f.val) ≤ readsIn D Q (N + f.val) :=
                Finset.sum_le_sum_of_subset_of_nonneg hTsubQ (fun _ _ _ => Nat.zero_le _)
              omega
            · have hleL : readsIn D Tset w ≤ readsIn D L w :=
                Finset.sum_le_sum_of_subset_of_nonneg hTsubL (fun _ _ _ => Nat.zero_le _)
              exact hleL.trans (hreads_le_one w hwf))
        _ = S_T.card := by simp
    have hScard : S_T.card ≤ 1 + (Tset.card - 1) := by
      have h1 : S_T.card ≤ ((Tset.erase t.val).image (N + ·)).card + 1 :=
        Finset.card_insert_le _ _
      have h2 : ((Tset.erase t.val).image (N + ·)).card ≤ (Tset.erase t.val).card := Finset.card_image_le
      have h3 : (Tset.erase t.val).card = Tset.card - 1 := Finset.card_erase_of_mem htTset
      omega
    have hTpos : 1 ≤ Tset.card := Finset.card_pos.mpr ⟨t.val, htTset⟩
    have hT1 : Tset.card = 1 := by omega
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨htTset, fun x hx =>
      Finset.card_le_one.mp (le_of_eq hT1) x hx t.val htTset⟩
  have hutEq : ut = N + f.val := by
    have hQeq : Q = {f.val, t.val} := by
      ext x
      by_cases hxF : x ∈ Fset
      · rw [hFset_eq, Finset.mem_singleton] at hxF
        subst hxF
        simp [hFsubQ (Finset.mem_insert_self _ _)]
      · constructor
        · intro hxQ
          have hxT : x ∈ Tset := Finset.mem_sdiff.mpr ⟨hxQ, hxF⟩
          rw [hTset_eq, Finset.mem_singleton] at hxT
          simp [hxT]
        · intro hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hFsubQ (Finset.mem_insert_self _ _)
          · exact Finset.mem_insert_self _ _
    have h1 := hQreads
    rw [hreads_card Q hQsub (N + f.val)] at h1
    have hpos : 0 < (Q.filter fun j => N + f.val ∈ (gateAt D j).inputs).card := by omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
    obtain ⟨hjQ, hjm⟩ := Finset.mem_filter.mp hj
    rw [hQeq, Finset.mem_insert, Finset.mem_singleton] at hjQ
    rcases hjQ with rfl | rfl
    · have := hback f.val f.isLt (N + f.val) hjm; omega
    · rw [hutList, List.mem_singleton] at hjm; exact hjm.symm
  have htGate : gateAt D t.val = ⟨.not, [N + f.val]⟩ := by
    cases h : gateAt D t.val with
    | mk op inp =>
      rw [h] at htOp hutList
      dsimp only at htOp hutList
      subst htOp; rw [hutList, hutEq]
  exact ⟨r, u, c, v, f, t, hru, hcv, hft, hDsize, hout, hback, hDrep, hDfan,
    hNotOnly, hopShape, hnodup, hReadsRow, hReadsCol, hReadsGate,
    hfOp, hfInputs, htGate, huIncomp, hvIncomp, hPhi_10, hPhi_01⟩

def chainOrs (acc nextIdx : ℕ) : List ℕ → List Gate
  | [] => []
  | w :: ws => ⟨.or, [acc, w]⟩ :: chainOrs nextIdx (nextIdx + 1) ws

theorem chainOrs_length (acc nextIdx : ℕ) (ws : List ℕ) :
    (chainOrs acc nextIdx ws).length = ws.length := by
  induction ws generalizing acc nextIdx with
  | nil => rfl
  | cons _ _ ih => simp [chainOrs, ih]

theorem chainOrs_mem (acc nextIdx : ℕ) (ws : List ℕ) :
    ∀ g ∈ chainOrs acc nextIdx ws, g.op = .or ∧ g.inputs.length = 2 := by
  induction ws generalizing acc nextIdx with
  | nil => intro _ h; cases h
  | cons w ws ih =>
    intro g hg
    simp only [chainOrs, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact ⟨rfl, rfl⟩
    · exact ih nextIdx (nextIdx + 1) g hg

theorem chainOrs_readsBack (acc nextIdx : ℕ) (ws : List ℕ)
    (hacc : acc < nextIdx) (hws : ∀ w ∈ ws, w < nextIdx) :
    ∀ k (hk : k < (chainOrs acc nextIdx ws).length),
      ∀ w ∈ (chainOrs acc nextIdx ws)[k].inputs, w < nextIdx + k := by
  induction ws generalizing acc nextIdx with
  | nil => intro k hk; simp [chainOrs] at hk
  | cons u ws ih =>
    intro k hk w hw
    cases k with
    | zero =>
      simp only [chainOrs, List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · omega
      · have := hws w (List.mem_cons_self ..); omega
    | succ k =>
      simp only [chainOrs, List.getElem_cons_succ] at hw
      have hk' : k < (chainOrs nextIdx (nextIdx + 1) ws).length := by
        simp only [chainOrs, List.length_cons] at hk; omega
      have h := ih nextIdx (nextIdx + 1) (by omega)
        (fun z hz => by have := hws z (List.mem_cons_of_mem _ hz); omega) k hk' w hw
      omega

theorem chainOrs_fold (acc nextIdx : ℕ) (ws : List ℕ) (pref : List Bool)
    (hlen : pref.length = nextIdx) (hacc : acc < nextIdx) (hws : ∀ w ∈ ws, w < nextIdx) :
    ((chainOrs acc nextIdx ws).foldl step pref).getD
        (if ws.length = 0 then acc else nextIdx + ws.length - 1) false =
      (pref.getD acc false || ws.any (fun w => pref.getD w false)) := by
  induction ws generalizing acc nextIdx pref with
  | nil => simp [chainOrs]
  | cons u ws ih =>
    simp only [chainOrs, List.foldl_cons]
    let pref1 := step pref ⟨.or, [acc, u]⟩
    have hlen1 : pref1.length = nextIdx + 1 := by simp [pref1, step, hlen]
    have hacc1 : pref1.getD nextIdx false = (pref.getD acc false || pref.getD u false) := by
      simp only [pref1, step, snoc, hlen, lt_irrefl, ite_false, ite_true, compute, GateOp.eval,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have hlt1 : ∀ z, z < nextIdx → pref1.getD z false = pref.getD z false := by
      intro z hz
      simp only [pref1, step, snoc, hlen, hz, ite_true]
    have hidx : (if (u :: ws).length = 0 then acc else nextIdx + (u :: ws).length - 1) =
        (if ws.length = 0 then nextIdx else (nextIdx + 1) + ws.length - 1) := by
      cases ws <;> simp <;> omega
    rw [hidx]
    have hrec := ih nextIdx (nextIdx + 1) pref1 hlen1 (by omega)
      (fun z hz => by have := hws z (List.mem_cons_of_mem _ hz); omega)
    rw [hrec, hacc1]
    have hany : ws.any (fun w => pref1.getD w false) = ws.any (fun w => pref.getD w false) := by
      have hws' : ∀ z ∈ ws, z < nextIdx := fun z hz => hws z (List.mem_cons_of_mem _ hz)
      clear hrec hidx hacc1 hlen1 hws ih
      induction ws with
      | nil => rfl
      | cons a tl ih2 =>
        simp only [List.any_cons]
        rw [hlt1 a (hws' a (List.mem_cons_self ..)), ih2 (fun z hz => hws' z (List.mem_cons_of_mem _ hz))]
    rw [hany]
    simp [Bool.or_assoc]

theorem sort_idxOf_lt {S : Finset ℕ} {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) :
    (S.sort (· ≤ ·)).idxOf a < (S.sort (· ≤ ·)).idxOf b := by
  set l := S.sort (· ≤ ·)
  have hal : a ∈ l := (Finset.mem_sort (· ≤ ·)).mpr ha
  have hbl : b ∈ l := (Finset.mem_sort (· ≤ ·)).mpr hb
  have hpw : l.Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hia : l.idxOf a < l.length := List.idxOf_lt_length_of_mem hal
  have hib : l.idxOf b < l.length := List.idxOf_lt_length_of_mem hbl
  by_contra hge
  have hle : l.idxOf b ≤ l.idxOf a := Nat.le_of_not_lt hge
  rcases eq_or_lt_of_le hle with heq | hlt
  · have : b = a := by
      have h1 := List.getElem_idxOf hia
      have h2 := List.getElem_idxOf hib
      rw [← h2, ← h1]
      congr 1
    omega
  · have hba : l[l.idxOf b] ≤ l[l.idxOf a] :=
      (List.pairwise_iff_getElem.mp hpw) (l.idxOf b) (l.idxOf a) hib hia hlt
    rw [List.getElem_idxOf hib, List.getElem_idxOf hia] at hba
    omega

theorem nodup_idxOf_getElem {l : List ℕ} (hnd : l.Nodup) (k : ℕ) (hk : k < l.length) :
    l.idxOf l[k] = k := by
  have hlt : l.idxOf l[k] < l.length := List.idxOf_lt_length_of_mem (List.getElem_mem hk)
  exact (List.Nodup.getElem_inj_iff hnd).mp (List.getElem_idxOf hlt)

set_option maxHeartbeats 4000000 in
theorem readOnceCut
    (n m : ℕ) (A : Fin n → Fin m → Bool) (hn : 3 ≤ n) (hm : 3 ≤ m)
    (D : Circuit) (r u : Fin n) (c v : Fin m) (f t : Fin D.size)
    (hru : r ≠ u) (hcv : c ≠ v) (hft : f < t)
    (hDsize : D.size = n + m - 1) (hout : D.output + 1 = n + m + D.size)
    (hback : ReadsBack (n + m) D) (hDrep : Represents A D) (hDfan : FanInTwo D)
    (hNotOnly : ∀ j : Fin D.size, (gateAt D j.val).op = .not ↔ j = t)
    (hopShape : ∀ g ∈ D.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (hnodup : ∀ j < D.size, (gateAt D j).inputs.Nodup)
    (hReadsRow : ∀ i : Fin n, readsIn D (Finset.range D.size) i.val = if i = r then 0 else 1)
    (hReadsCol : ∀ j : Fin m, readsIn D (Finset.range D.size) (n + j.val) = if j = c then 0 else 1)
    (hReadsGate : ∀ j : Fin D.size, readsIn D (Finset.range D.size) (n + m + j.val) =
      if j = f then 2 else if j.val + 1 = D.size then 0 else 1)
    (hfOp : (gateAt D f.val).op = .or)
    (hfInputs : (gateAt D f.val).inputs = [u.val, n + v.val] ∨ (gateAt D f.val).inputs = [n + v.val, u.val])
    (htGate : gateAt D t.val = ⟨.not, [n + m + f.val]⟩)
    (huIncomp : ¬ ((∀ j, A r j = true → A u j = true) ∨ (∀ j, A u j = true → A r j = true)))
    (hvIncomp : ¬ ((∀ i, A i c = true → A i v = true) ∨ (∀ i, A i v = true → A i c = true)))
    (hPhi_10 : value (n + m) D zeroX (override2 (n + m + f.val) true (n + m + t.val) false) D.output = false)
    (hPhi_01 : value (n + m) D zeroX (override2 (n + m + f.val) false (n + m + t.val) true) D.output = false) :

    ∃ (tree : TightOneHot.Tree) (p l : ℕ),
      tree.readOnce ∧
      r.val ∉ tree.support ∧ u.val ∉ tree.support ∧
      n + c.val ∉ tree.support ∧ n + v.val ∉ tree.support ∧
      ¬ tree.holds {p} ∧ ¬ tree.holds {l} ∧
      (∀ i : Fin n, i.val ≠ p ∧ i.val ≠ l) ∧
      (∀ j : Fin m, n + j.val ≠ p ∧ n + j.val ≠ l) ∧
      ∀ i j, A i j = true ↔ tree.holds (insert (if i = u ∨ j = v then p else l)
        ({i.val, n + j.val} : Finset ℕ)) := by
  classical
  set N := n + m
  set L := Finset.range D.size
  set U := (L.erase f.val).erase t.val
  have clL : closed N D L := closed_range N D hback
  have hUsubL : U ⊆ L := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hUgate : ∀ g ∈ U, g < D.size ∧ g ≠ f.val ∧ g ≠ t.val ∧
      ((gateAt D g).op = .and ∨ (gateAt D g).op = .or) ∧
      (gateAt D g).inputs.length = 2 ∧ (gateAt D g).inputs.Nodup := by
    intro g hg
    have hgt : g ≠ t.val := Finset.ne_of_mem_erase hg
    have hg1 : g ∈ L.erase f.val := Finset.mem_of_mem_erase hg
    have hgf : g ≠ f.val := Finset.ne_of_mem_erase hg1
    have hgL : g ∈ L := Finset.mem_of_mem_erase hg1
    have hglt : g < D.size := Finset.mem_range.mp hgL
    have hgmem : gateAt D g ∈ D.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hglt]; exact List.getElem_mem hglt
    have hne : (gateAt D g).op ≠ .not := fun h => hgt (congrArg Fin.val ((hNotOnly ⟨g, hglt⟩).mp h))
    rcases hopShape _ hgmem with ⟨hop, hlen⟩ | ⟨hop, _⟩
    · exact ⟨hglt, hgf, hgt, hop, hlen, hnodup g hglt⟩
    · exact (hne hop).elim
  have hreads_card : ∀ (S : Finset ℕ), S ⊆ L → ∀ w,
      readsIn D S w = (S.filter fun j => w ∈ (gateAt D j).inputs).card := fun S hS w =>
    reads_card D S w (fun j hj => hnodup j (Finset.mem_range.mp (hS hj)))
  have hreadsU_le_one : ∀ w, readsIn D U w ≤ 1 := by
    intro w
    by_cases hwf : w = N + f.val
    · subst hwf
      have hfL : f.val ∈ L := Finset.mem_range.mpr f.isLt
      have htL : t.val ∈ L.erase f.val := Finset.mem_erase.mpr ⟨by have : f.val < t.val := hft; omega, Finset.mem_range.mpr t.isLt⟩
      have htot : readsIn D L (N + f.val) = 2 := by simpa using hReadsGate f
      have h1 : readsIn D L (N + f.val) = (gateAt D f.val).inputs.count (N + f.val) + readsIn D (L.erase f.val) (N + f.val) :=
        (Finset.add_sum_erase L _ hfL).symm
      have h2 : readsIn D (L.erase f.val) (N + f.val) = (gateAt D t.val).inputs.count (N + f.val) + readsIn D U (N + f.val) :=
        (Finset.add_sum_erase (L.erase f.val) _ htL).symm
      have hct : (gateAt D t.val).inputs.count (N + f.val) = 1 := by simp [htGate]
      have hcf : (gateAt D f.val).inputs.count (N + f.val) = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        have := hback f.val f.isLt (N + f.val) hm; omega
      omega
    · have hle : readsIn D U w ≤ readsIn D L w :=
        Finset.sum_le_sum_of_subset_of_nonneg hUsubL (fun _ _ _ => Nat.zero_le _)
      have hle1 : readsIn D L w ≤ 1 := by
        by_cases h1 : w < n
        · have h := hReadsRow ⟨w, h1⟩; dsimp only at h; split_ifs at h <;> omega
        · by_cases h2 : w < N
          · have h := hReadsCol ⟨w - n, by omega⟩
            have he : n + (w - n) = w := by omega
            rw [he] at h; split_ifs at h <;> omega
          · by_cases h3 : w < N + D.size
            · have h := hReadsGate ⟨w - N, by omega⟩
              have he : N + (w - N) = w := by omega
              rw [he] at h
              have hne' : (⟨w - N, by omega⟩ : Fin D.size) ≠ f := fun e => hwf (by
                have := congrArg Fin.val e; dsimp only at this; omega)
              split_ifs at h <;> first | exact (hne' ‹_›).elim | omega
            · have h0 : readsIn D L w = 0 := by
                rw [hreads_card L (Finset.Subset.refl L) w, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                intro j hj hmem
                have := hback j (Finset.mem_range.mp hj) w hmem
                have := Finset.mem_range.mp hj
                omega
              omega
      omega
  have huniqU : ∀ w, ∀ j1 ∈ U, ∀ j2 ∈ U,
      w ∈ (gateAt D j1).inputs → w ∈ (gateAt D j2).inputs → j1 = j2 := by
    intro w j1 hj1 j2 hj2 hm1 hm2
    have hle := hreadsU_le_one w
    rw [hreads_card U hUsubL w] at hle
    exact Finset.card_le_one.mp hle j1 (Finset.mem_filter.mpr ⟨hj1, hm1⟩) j2 (Finset.mem_filter.mpr ⟨hj2, hm2⟩)
  let reachU := reaches N D U
  let orStepU (a b : ℕ) : Prop :=
    ∃ g ∈ U, b = N + g ∧ (gateAt D g).op = .or ∧ before D N g a
  let orReachU := Relation.ReflTransGen orStepU
  have hor_to_reachU : ∀ {a b}, orReachU a b → reachU a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | tail _ e ih =>
      obtain ⟨g, hg, rfl, _, hb⟩ := e
      exact ih.tail ⟨g, hg, rfl, hb⟩
  have hreachU_disjoint : ∀ g ∈ U, ∀ a ∈ (gateAt D g).inputs, ∀ b ∈ (gateAt D g).inputs,
      a ≠ b → ∀ w, reachU w a → reachU w b → False := by
    intro g hg a ha b hb hab w hwa hwb
    induction hwa using Relation.ReflTransGen.head_induction_on with
    | refl =>
      obtain ⟨z, ⟨k, hkU, rfl, hkm, _⟩, hkz⟩ := path_head hwb hab
      have hle := reachIncreases hkz
      have hblt := hback g (hUgate g hg).1 b hb
      have hgk : g = k := huniqU a g hg k hkU ha hkm
      omega
    | @head x y step _ ih =>
      by_cases hxb : x = b
      · subst hxb
        obtain ⟨k, hkU, rfl, hkm, _⟩ := step
        have hle := reachIncreases (‹reachU (N + k) a›)
        have halt := hback g (hUgate g hg).1 a ha
        have hgk : g = k := huniqU x g hg k hkU hb hkm
        omega
      · obtain ⟨j, hjU, rfl, hjm, _⟩ := step
        obtain ⟨z, ⟨k, hkU, rfl, hkm, _⟩, hkz⟩ := path_head hwb hxb
        have hjk : j = k := huniqU x j hjU k hkU hjm hkm
        exact ih (hjk ▸ hkz)
  have hreachU_linear : ∀ x y z, reachU x y → reachU x z → reachU y z ∨ reachU z y := by
    intro x y z hxy hxz
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl => exact Or.inl hxz
    | @head a b step _ ih =>
      by_cases haz : a = z
      · subst haz
        exact Or.inr (Relation.ReflTransGen.head step ‹reachU b y›)
      · obtain ⟨j, hjU, rfl, hjm, _⟩ := step
        obtain ⟨w, ⟨k, hkU, rfl, hkm, _⟩, hkw⟩ := path_head hxz haz
        have hjk : j = k := huniqU a j hjU k hkU hjm hkm
        exact ih (hjk ▸ hkw)
  have horReachU_ops : ∀ {x y h}, orReachU x y → reachU x (N + h) → reachU (N + h) y →
      N + h ≠ x → (gateAt D h).op = .or := by
    intro x y h hxy hxh hhy hne
    induction hxy using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have h1 := reachIncreases hxh
      have h2 := reachIncreases hhy
      exact (hne (by omega)).elim
    | @head a b step hby ih =>
      obtain ⟨k, hkU, rfl, hkor, hkm, _⟩ := step
      obtain ⟨z, ⟨j, hjU, rfl, hjm, _⟩, hjh⟩ := path_head hxh (Ne.symm hne)
      have hkj : k = j := huniqU a k hkU j hjU hkm hjm
      subst hkj
      by_cases hhk : h = k
      · exact hhk ▸ hkor
      · exact ih hjh (by omega)
  let valU (S : Finset ℕ) (w : ℕ) : Bool :=
    value N D (fun i => decide (i ∈ S))
      (override2 (N + f.val) (decide (N + f.val ∈ S)) (N + t.val) (decide (N + t.val ∈ S))) w
  have hvalU_leaf : ∀ S w, (w < N ∨ w = N + f.val ∨ w = N + t.val) → valU S w = decide (w ∈ S) := by
    intro S w hw
    rcases hw with hw | rfl | rfl
    · dsimp only [valU]
      have h1 : w ≠ N + f.val := by omega
      have h2 : w ≠ N + t.val := by omega
      rw [val_raw hw (by simp [override2, h1, h2])]
    · exact val_override2_left N D _ _ _ _ _
    · exact val_override2_right N D _ _ _ _ _ (by have : f.val < t.val := hft; omega)
  have hvalU_gate : ∀ S g, g ∈ U →
      valU S (N + g) = (gateAt D g).op.eval ((gateAt D g).inputs.map (valU S)) := by
    intro S g hg
    obtain ⟨hglt, hgf, hgt, _, _, _⟩ := hUgate g hg
    dsimp only [valU]
    rw [val_gate hglt (by simp [override2, hgf, hgt])]
    congr 1
    apply List.map_congr_left
    intro u hu
    rw [ite_eq_left (hback g hglt u hu)]
  have hval_eval_ind2 : ∀ (i : Fin n) (j : Fin m),
      A i j = valU (({i.val, n + j.val} : Finset ℕ) ∪
        if decide (i = u ∨ j = v) then {N + f.val} else {N + t.val}) D.output := by
    intro i j
    have hwf_val : value N D (ind2 i j) (fun _ => none) (N + f.val) = decide (i = u ∨ j = v) := by
      rw [val_gate f.isLt rfl, hfOp]
      have hult : u.val < N + f.val := by have := u.isLt; omega
      have hvlt : n + v.val < N + f.val := by have := v.isLt; omega
      have h1 : value N D (ind2 i j) (fun _ => none) u.val = decide (i = u) := by
        rw [val_raw (by have := u.isLt; omega : u.val < N) rfl]
        simp only [ind2, decide_eq_decide]
        constructor
        · rintro (h | h)
          · exact Fin.ext h.symm
          · have := u.isLt; omega
        · intro h; left; exact congrArg Fin.val h.symm
      have h2 : value N D (ind2 i j) (fun _ => none) (n + v.val) = decide (j = v) := by
        rw [val_raw (by have := v.isLt; omega : n + v.val < N) rfl]
        simp only [ind2, decide_eq_decide]
        constructor
        · rintro (h | h)
          · have := i.isLt; omega
          · exact Fin.ext (by omega)
        · intro h; right; exact congrArg (n + Fin.val ·) h.symm
      rcases hfInputs with h | h <;> rw [h]
      · simp only [GateOp.eval, List.map_cons, List.map_nil, hult, hvlt, ite_true, h1, h2,
          List.any_cons, List.any_nil, id_eq, Bool.or_false, ← Bool.decide_or]
      · simp only [GateOp.eval, List.map_cons, List.map_nil, hult, hvlt, ite_true, h1, h2,
          List.any_cons, List.any_nil, id_eq, Bool.or_false]
        rw [Bool.or_comm, ← Bool.decide_or]
    have hwt_val : value N D (ind2 i j) (fun _ => none) (N + t.val) = ! decide (i = u ∨ j = v) := by
      rw [val_gate t.isLt rfl, htGate]
      have hlt : N + f.val < N + t.val := by have : f.val < t.val := hft; omega
      simp [GateOp.eval, hlt, hwf_val]
    have hftne : N + t.val ≠ N + f.val := by have : f.val < t.val := hft; omega
    have houtLive : live N L D.output := Or.inr ⟨D.size - 1, Finset.mem_range.mpr (by omega), by omega⟩
    rw [← eval_ind2 hDrep i j, replace_signal2 clL (ind2 i j) (N + f.val) (N + t.val) hftne D.output houtLive,
      hwf_val, hwt_val]
    dsimp only [valU]
    have hf_mem : decide (N + f.val ∈ (({i.val, n + j.val} : Finset ℕ) ∪
        if decide (i = u ∨ j = v) then {N + f.val} else {N + t.val})) = decide (i = u ∨ j = v) := by
      have hi_lt : i.val < N := by have := i.isLt; omega
      have hj_lt : n + j.val < N := by have := j.isLt; omega
      cases hb : decide (i = u ∨ j = v)
      · simp only [Bool.false_eq_true, ite_false, decide_eq_false_iff_not, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨⟨by omega, by omega⟩, hftne.symm⟩
      · simp
    have ht_mem : decide (N + t.val ∈ (({i.val, n + j.val} : Finset ℕ) ∪
        if decide (i = u ∨ j = v) then {N + f.val} else {N + t.val})) = ! decide (i = u ∨ j = v) := by
      have hi_lt : i.val < N := by have := i.isLt; omega
      have hj_lt : n + j.val < N := by have := j.isLt; omega
      cases hb : decide (i = u ∨ j = v)
      · simp
      · simp only [ite_true, Bool.not_true, decide_eq_false_iff_not, Finset.mem_union,
          Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨⟨by omega, by omega⟩, hftne⟩
    rw [hf_mem, ht_mem]
    refine value_agree clL D.output houtLive _ _ _ _ ?_ (fun _ _ => rfl)
    intro w hw _
    simp only [ind2, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, decide_eq_decide]
    cases decide (i = u ∨ j = v)
    · simp only [Bool.false_eq_true, ite_false, Finset.mem_singleton]
      exact ⟨Or.inl, fun h => h.resolve_right (by omega)⟩
    · simp only [ite_true, Finset.mem_singleton]
      exact ⟨Or.inl, fun h => h.resolve_right (by omega)⟩
  have hNoReach_rcuv : ∀ w, (w = r.val ∨ w = n + c.val ∨ w = u.val ∨ w = n + v.val) →
      ∀ g ∈ U, w ∉ (gateAt D g).inputs := by
    intro w hw g hg hm
    have hgL : g ∈ L := hUsubL hg
    have hgf : g ≠ f.val := (hUgate g hg).2.1
    rcases hw with rfl | rfl | rfl | rfl
    · have h0 : readsIn D L r.val = 0 := by simpa using hReadsRow r
      rw [hreads_card L (Finset.Subset.refl L) r.val, Finset.card_eq_zero] at h0
      exact Finset.notMem_empty g (h0 ▸ Finset.mem_filter.mpr ⟨hgL, hm⟩)
    · have h0 : readsIn D L (n + c.val) = 0 := by simpa using hReadsCol c
      rw [hreads_card L (Finset.Subset.refl L) (n + c.val), Finset.card_eq_zero] at h0
      exact Finset.notMem_empty g (h0 ▸ Finset.mem_filter.mpr ⟨hgL, hm⟩)
    · have h1 : readsIn D L u.val = 1 := by simpa [hru.symm] using hReadsRow u
      rw [hreads_card L (Finset.Subset.refl L) u.val] at h1
      have hfu : u.val ∈ (gateAt D f.val).inputs := by rcases hfInputs with h | h <;> simp [h]
      exact hgf (Finset.card_le_one.mp (le_of_eq h1) g (Finset.mem_filter.mpr ⟨hgL, hm⟩)
        f.val (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f.isLt, hfu⟩))
    · have h1 : readsIn D L (n + v.val) = 1 := by simpa [hcv.symm] using hReadsCol v
      rw [hreads_card L (Finset.Subset.refl L) (n + v.val)] at h1
      have hfv : n + v.val ∈ (gateAt D f.val).inputs := by rcases hfInputs with h | h <;> simp [h]
      exact hgf (Finset.card_le_one.mp (le_of_eq h1) g (Finset.mem_filter.mpr ⟨hgL, hm⟩)
        f.val (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr f.isLt, hfv⟩))
  have hNotReachU_out : ∀ w, (w = r.val ∨ w = n + c.val ∨ w = u.val ∨ w = n + v.val) → ¬ reachU w D.output := by
    intro w hw hr
    have hwlt : w < N := by
      rcases hw with rfl | rfl | rfl | rfl
      · have := r.isLt; omega
      · have := c.isLt; omega
      · have := u.isLt; omega
      · have := v.isLt; omega
    obtain ⟨z, ⟨g, hgU, rfl, hgm, _⟩, _⟩ := path_head hr (by omega)
    exact hNoReach_rcuv w hw g hgU hgm
  have hvalU_10 : valU {N + f.val} D.output = false := by
    rw [← hPhi_10]
    have hftne : N + t.val ≠ N + f.val := by have : f.val < t.val := hft; omega
    dsimp only [valU]
    simp only [Finset.mem_singleton, decide_true, hftne, decide_false]
    refine value_agree clL D.output (Or.inr ⟨D.size - 1, Finset.mem_range.mpr (by omega), by omega⟩) _ _ _ _ ?_ (fun _ _ => rfl)
    intro w hw _
    simp only [zeroX, Finset.mem_singleton, decide_eq_false_iff_not]
    omega
  have hvalU_01 : valU {N + t.val} D.output = false := by
    rw [← hPhi_01]
    have hftne : N + f.val ≠ N + t.val := by have : f.val < t.val := hft; omega
    dsimp only [valU]
    simp only [Finset.mem_singleton, decide_true, hftne, decide_false]
    refine value_agree clL D.output (Or.inr ⟨D.size - 1, Finset.mem_range.mpr (by omega), by omega⟩) _ _ _ _ ?_ (fun _ _ => rfl)
    intro w hw _
    simp only [zeroX, Finset.mem_singleton, decide_eq_false_iff_not]
    omega

  have build : ∀ w < N + D.size, ∃ tree : TightOneHot.Tree,
      tree.readOnce ∧ (∀ x ∈ tree.support, reachU x w) ∧
      ∀ S, tree.holds S ↔ valU S w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      by_cases leaf : w < N ∨ w = N + f.val ∨ w = N + t.val
      · refine ⟨.wire w, trivial, ?_, ?_⟩
        · intro z hz
          have : z = w := Finset.mem_singleton.mp hz
          subst z
          exact Relation.ReflTransGen.refl
        · intro S
          rw [hvalU_leaf S w leaf, decide_eq_true_eq]
          rfl
      have wEq : w = N + (w - N) := by
        have := (not_or.mp leaf).1
        omega
      have gU : w - N ∈ U := by
        simp only [U, L, Finset.mem_erase, Finset.mem_range]
        have hf := (not_or.mp (not_or.mp leaf).2).1
        have ht := (not_or.mp (not_or.mp leaf).2).2
        exact ⟨by omega, by omega, by omega⟩
      obtain ⟨a, b, inputs⟩ : ∃ a b, (gateAt D (w - N)).inputs = [a,b] := by
        have len := (hUgate _ gU).2.2.2.2.1
        cases hs : (gateAt D (w - N)).inputs with
        | nil => simp [hs] at len
        | cons a as =>
          cases ht : as with
          | nil => simp [hs, ht] at len
          | cons b bs =>
            have empty : bs = [] := by
              simp only [hs, ht, List.length_cons] at len
              exact List.length_eq_zero_iff.mp (by omega)
            exact ⟨a,b,by simp [empty]⟩
      have ha : a ∈ (gateAt D (w - N)).inputs := by simp [inputs]
      have hb : b ∈ (gateAt D (w - N)).inputs := by simp [inputs]
      have ab : a ≠ b := by
        simpa [inputs] using (hUgate _ gU).2.2.2.2.2
      have aLt : a < w := by have h := hback _ (hUgate _ gU).1 _ ha; omega
      have bLt : b < w := by have h := hback _ (hUgate _ gU).1 _ hb; omega
      obtain ⟨ta, ra, sa, va⟩ := ih a aLt (by omega)
      obtain ⟨tb, rb, sb, vb⟩ := ih b bLt (by omega)
      have sep : Disjoint ta.support tb.support :=
        Finset.disjoint_left.mpr (fun z za zb =>
          hreachU_disjoint _ gU _ ha _ hb ab z (sa z za) (sb z zb))
      have hr : ∀ z ∈ ta.support ∪ tb.support, reachU z w := by
        intro z hz
        rcases Finset.mem_union.mp hz with za | zb
        · exact (sa z za).tail ⟨w - N, gU, wEq, ha, by omega⟩
        · exact (sb z zb).tail ⟨w - N, gU, wEq, hb, by omega⟩
      have val (S : Finset ℕ) : valU S w =
          (gateAt D (w - N)).op.eval [valU S a, valU S b] := by
        conv_lhs => rw [show w = N + (w - N) from wEq]
        simpa only [inputs, List.map_cons, List.map_nil] using hvalU_gate S (w - N) gU
      rcases (hUgate _ gU).2.2.2.1 with hop | hop
      · refine ⟨.both ta tb, ⟨ra,rb,sep⟩, hr, fun S => ?_⟩
        rw [val, hop]
        simpa [TightOneHot.Tree.holds, GateOp.eval, Bool.and_eq_true] using and_congr (va S) (vb S)
      · refine ⟨.either ta tb, ⟨ra,rb,sep⟩, hr, fun S => ?_⟩
        rw [val, hop]
        simpa [TightOneHot.Tree.holds, GateOp.eval, Bool.or_eq_true] using or_congr (va S) (vb S)
  obtain ⟨tree, ro, hs, hv⟩ := build D.output (by omega)
  refine ⟨tree, N + f.val, N + t.val, ro,
    fun h => hNotReachU_out _ (.inl rfl) (hs _ h),
    fun h => hNotReachU_out _ (.inr (.inr (.inl rfl))) (hs _ h),
    fun h => hNotReachU_out _ (.inr (.inl rfl)) (hs _ h),
    fun h => hNotReachU_out _ (.inr (.inr (.inr rfl))) (hs _ h),
    fun h => by simpa [hvalU_10] using (hv _).mp h,
    fun h => by simpa [hvalU_01] using (hv _).mp h,
    fun i => ⟨by have := i.isLt; omega, by have := i.isLt; omega⟩,
    fun j => ⟨by have := j.isLt; omega, by have := j.isLt; omega⟩, ?_⟩
  intro i j
  rw [hval_eval_ind2, hv]
  congr 2
  by_cases h : i = u ∨ j = v
  · simp [h, Finset.union_singleton]
  · simp [h, Finset.union_singleton]

end Proof

end PEqualNP.Outside.L_meta_29721

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_29721

theorem PEqualNP.Outside.L_meta_29721 :
∀ (n m : Nat) (A : Fin n → Fin m → Bool), 3 ≤ n → 3 ≤ m →
  let rowLE := fun i k : Fin n => ∀ j, A i j = true → A k j = true
  let colLE := fun j l : Fin m => ∀ i, A i j = true → A i l = true
  let rc := fun i k : Fin n => rowLE i k ∨ rowLE k i
  let cc := fun j l : Fin m => colLE j l ∨ colLE l j
  Function.Injective A → Function.Injective (fun j i => A i j) →
  (∀ i, ∃ k, ¬ rc i k) → (∀ j, ∃ l, ¬ cc j l) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C →
  C.size ≤ n + m - 1 →
  (∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not) →
  ∃ (x : Fin 4 ↪ Fin n) (y : Fin 4 ↪ Fin m),
  let R := fun i : Fin n => i ≠ x 0 ∧ i ≠ x 1 ∧ i ≠ x 2
  let T := fun j : Fin m => j ≠ y 0 ∧ j ≠ y 1 ∧ j ≠ y 2
  (∀ j, A (x 0) j = decide (j = y 2) ∧ A (x 1) j = decide (j = y 3) ∧
    A (x 2) j = decide (j ≠ y 1)) ∧
  (∀ i, A i (y 0) = decide (i = x 2) ∧ A i (y 1) = decide (i = x 3) ∧
    A i (y 2) = decide (i ≠ x 1)) ∧ A (x 3) (y 3) = false ∧
  (∀ i j l, R i → T j → T l → A i j = true → A i l = true → j = l) ∧
  (∀ j i k, T j → R i → R k → A i j = true → A k j = true → i = k) ∧
  (∀ i, R i → i ≠ x 3 → ∃ j, T j ∧ A i j = true) ∧
  (∀ j, T j → j ≠ y 3 → ∃ i, R i ∧ A i j = true) := by
  classical
  intro n m A hn hm
  dsimp only
  intro rowInj colInj rowIncomp colIncomp C fan rep size containsNot
  obtain ⟨r,u,c,v,f,t,ru,cv,ft,dsize,out,back,drep,dfan,onlyNot,shape,nodup,
    readsRow,readsCol,readsGate,op,inputs,notGate,rowPair,colPair,railHigh,railLow⟩ :=
    Proof.part12 n m A hn hm rowInj colInj rowIncomp colIncomp C fan rep size containsNot
  obtain ⟨tree,p,l,ro,rAbsent,uAbsent,cAbsent,vAbsent,emptyHigh,emptyLow,_,_,trace⟩ :=
    Proof.readOnceCut n m A hn hm _ r u c v f t ru cv ft dsize out back drep dfan
      onlyNot shape nodup readsRow readsCol readsGate op inputs notGate rowPair colPair railHigh railLow
  let table : TightOneHot.Table (Fin n) (Fin m) :=
    { f := fun i j => A i j = true
      tree := tree
      p := p
      l := l
      R := Fin.val
      C := fun j => n + j.val
      r := r
      u := u
      c := c
      v := v
      ro := ro
      rAbsent := rAbsent
      uAbsent := uAbsent
      cAbsent := cAbsent
      vAbsent := vAbsent
      highEmpty := emptyHigh
      lowEmpty := emptyLow
      repr := trace
      rows := by
        intro i k e
        apply rowInj
        funext j
        exact Bool.eq_iff_iff.mpr (Iff.of_eq (congrFun e j))
      cols := by
        intro j l e
        apply colInj
        funext i
        exact Bool.eq_iff_iff.mpr (Iff.of_eq (congrFun e i))
      noFullRow := by
        intro i
        by_contra! full
        obtain ⟨k,hk⟩ := rowIncomp i
        exact hk (.inr (fun j _ => full j))
      noFullCol := by
        intro j
        by_contra! full
        obtain ⟨k,hk⟩ := colIncomp j
        exact hk (.inr (fun i _ => full i))
      ru := ru
      cv := cv
      diffLow := by
        have h := (not_or.mp colPair).1
        push Not at h
        exact h
      diffHigh := by
        have h := (not_or.mp colPair).2
        push Not at h
        exact h
      diffLowCol := by
        have h := (not_or.mp rowPair).1
        push Not at h
        exact h
      diffHighCol := by
        have h := (not_or.mp rowPair).2
        push Not at h
        exact h }
  obtain ⟨x2, lrow⟩ := table.diffLow
  obtain ⟨x3, hrow⟩ := table.diffHigh
  obtain ⟨y2, lcol⟩ := table.diffLowCol
  obtain ⟨y3, hcol⟩ := table.diffHighCol
  let d : table.Core := ⟨x2,x3,y2,y3,lrow,hrow,lcol,hcol⟩
  have embed {α : Type} (a b c e : α) (ab : a ≠ b) (ac : c ≠ a)
      (bc : c ≠ b) (ae : e ≠ a) (be : e ≠ b) (ce : e ≠ c) :
      ∃ x : Fin 4 ↪ α, x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = e := by
    refine ⟨⟨![a,b,c,e], ?_⟩, rfl,rfl,rfl,rfl⟩
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | exfalso
    all_goals
      first
      | exact ab h
      | exact ab h.symm
      | exact ac h
      | exact ac h.symm
      | exact bc h
      | exact bc h.symm
      | exact ae h
      | exact ae h.symm
      | exact be h
      | exact be h.symm
      | exact ce h
      | exact ce h.symm
  obtain ⟨x, x0, x1, x2eq, x3eq⟩ := embed r u x2 x3 ru d.low.1 d.low.2.1
    d.hiRest.1 d.hiRest.2.1 d.hiRest.2.2
  obtain ⟨y, y0, y1, y2eq, y3eq⟩ := embed c v y2 y3 cv d.flip.low.1 d.flip.low.2.1
    d.flip.hiRest.1 d.flip.hiRest.2.1 d.flip.hiRest.2.2
  refine ⟨x,y, ?_⟩
  rw [x0,x1,x2eq,x3eq,y0,y1,y2eq,y3eq]
  refine ⟨?_, ?_, Bool.eq_false_iff.mpr d.diagonal, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨Bool.eq_iff_iff.mpr ((d.flip.low.2.2.2.2.1 j).trans (Iff.of_eq decide_eq_true_eq.symm)),
      Bool.eq_iff_iff.mpr ((d.flip.high.2.2.2.2 j).trans (Iff.of_eq decide_eq_true_eq.symm)),
      Bool.eq_iff_iff.mpr ((d.low.2.2.2.2.2 j).trans (Iff.of_eq decide_eq_true_eq.symm))⟩
  · intro i
    exact ⟨Bool.eq_iff_iff.mpr ((d.low.2.2.2.2.1 i).trans (Iff.of_eq decide_eq_true_eq.symm)),
      Bool.eq_iff_iff.mpr ((d.high.2.2.2.2 i).trans (Iff.of_eq decide_eq_true_eq.symm)),
      Bool.eq_iff_iff.mpr ((d.flip.low.2.2.2.2.2 i).trans (Iff.of_eq decide_eq_true_eq.symm))⟩
  · intro i j l hi hj hl hij hil
    exact d.flip.uniqueRows i hi j l hj hl hij hil
  · intro j i k hj hi hk hij hkj
    exact d.uniqueRows j hj i k hi hk hij hkj
  · exact d.existsCol
  · exact d.flip.existsCol
