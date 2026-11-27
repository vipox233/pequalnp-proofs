import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_806_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

inductive Tree where
  | leaf (i : ℕ)
  | node (isAnd : Bool) (l r : Tree)
  deriving DecidableEq

def Tree.eval : Tree → (ℕ → Bool) → Bool
  | .leaf i, x => x i
  | .node b l r, x => if b then l.eval x && r.eval x else l.eval x || r.eval x

def Tree.nodes : Tree → ℕ
  | .leaf _ => 0
  | .node _ l r => l.nodes + r.nodes + 1

def Tree.occ (i : ℕ) : Tree → ℕ
  | .leaf j => if i = j then 1 else 0
  | .node _ l r => l.occ i + r.occ i

def Tree.bound (n : ℕ) : Tree → Prop
  | .leaf i => i < n
  | .node _ l r => l.bound n ∧ r.bound n

def Tree.subst (t : Tree) (i : ℕ) (p : Tree) : Tree := match t with
  | .leaf j => if j = i then p else .leaf j
  | .node b l r => .node b (l.subst i p) (r.subst i p)

theorem subst_eval (t p : Tree) (i : ℕ) (x : ℕ → Bool) :
    (t.subst i p).eval x = t.eval (fun j => if j = i then p.eval x else x j) := by
  induction t with
  | leaf j => by_cases h : j = i <;> simp [Tree.subst, Tree.eval, h]
  | node b l r hl hr => simp [Tree.subst, Tree.eval, hl, hr]

theorem subst_nodes (t p : Tree) (i : ℕ) :
    (t.subst i p).nodes = t.nodes + t.occ i * p.nodes := by
  induction t with
  | leaf j =>
    by_cases h : j = i
    · simp [Tree.subst, Tree.nodes, Tree.occ, h]
    · simp [Tree.subst, Tree.nodes, Tree.occ, h, Ne.symm h]
  | node b l r hl hr => simp only [Tree.subst, Tree.nodes, Tree.occ, hl, hr, Nat.add_mul]; omega

theorem subst_occ (t p : Tree) (i j : ℕ) :
    (t.subst i p).occ j = (if j = i then 0 else t.occ j) + t.occ i * p.occ j := by
  induction t with
  | leaf k =>
    by_cases h : k = i <;> by_cases h' : j = i <;>
      simp_all [Tree.subst, Tree.occ, eq_comm]
  | node b l r hl hr =>
    simp only [Tree.subst, Tree.occ, hl, hr]
    split_ifs <;> simp_all [Nat.add_mul] <;> omega

theorem occ_zero_of_bound (t : Tree) {n i : ℕ} (h : t.bound n) (hi : n ≤ i) :
    t.occ i = 0 := by
  induction t with
  | leaf j => simp only [Tree.bound] at h; simp [Tree.occ, show i ≠ j by omega]
  | node b l r hl hr => simp only [Tree.bound] at h; simp [Tree.occ, hl h.1, hr h.2]

theorem subst_bound (t p : Tree) (i n : ℕ) (ht : t.bound (n+1)) (hp : p.bound n)
    (hi : i = n) : (t.subst i p).bound n := by
  subst i
  induction t with
  | leaf j =>
    simp only [Tree.bound] at ht
    by_cases h : j = n
    · simpa [Tree.subst, h] using hp
    · simpa [Tree.subst, h, Tree.bound] using (show j < n by omega)
  | node b l r hl hr => exact ⟨hl ht.1, hr ht.2⟩

theorem eval_zero (t : Tree) : t.eval (fun _ => false) = false := by
  induction t with
  | leaf i => rfl
  | node b l r hl hr => simp [Tree.eval, hl, hr]

theorem eval_support (t : Tree) (x : ℕ → Bool) (h : t.eval x = true) :
    ∃ i, 0 < t.occ i ∧ x i = true := by
  induction t with
  | leaf j => exact ⟨j, by simp [Tree.occ], h⟩
  | node b l r hl hr =>
    cases b <;> simp only [Tree.eval, Bool.false_eq_true, ite_false, ite_true,
      Bool.and_eq_true, Bool.or_eq_true] at h
    · rcases h with h | h
      · obtain ⟨i, hi, hx⟩ := hl h; exact ⟨i, by simp only [Tree.occ]; omega, hx⟩
      · obtain ⟨i, hi, hx⟩ := hr h; exact ⟨i, by simp only [Tree.occ]; omega, hx⟩
    · obtain ⟨i, hi, hx⟩ := hl h.1
      exact ⟨i, by simp only [Tree.occ]; omega, hx⟩

theorem singleton_occ (t : Tree) (a : ℕ)
    (h : t.eval (fun i => decide (i = a)) = true) : 0 < t.occ a := by
  obtain ⟨i, hi, hx⟩ := eval_support t _ h
  have : i = a := of_decide_eq_true hx
  simpa [this] using hi

def Tree.parts : Tree → List Tree
  | .node false l r => l.parts ++ r.parts
  | t => [t]

theorem parts_eval (t : Tree) (x : ℕ → Bool) :
    (t.parts.map (fun p => p.eval x)).any id = t.eval x := by
  induction t with
  | leaf j => simp [Tree.parts, Tree.eval]
  | node b l r hl hr => cases b <;> simp [Tree.parts, Tree.eval, hl, hr]

theorem parts_weight (t : Tree) :
    (t.parts.map (fun p => p.nodes+1)).sum = t.nodes+1 := by
  induction t with
  | leaf j => simp [Tree.parts]
  | node b l r hl hr => cases b <;> simp [Tree.parts, Tree.nodes, hl, hr] <;> omega

theorem parts_occ (t : Tree) (i : ℕ) : (t.parts.map (fun p => p.occ i)).sum = t.occ i := by
  induction t with
  | leaf j => simp [Tree.parts]
  | node b l r hl hr => cases b <;> simp [Tree.parts, Tree.occ, hl, hr]

theorem singleton_part (t : Tree) (a : ℕ) (ho : t.occ a ≤ 1)
    (h : t.eval (fun i => decide (i = a)) = true) : Tree.leaf a ∈ t.parts := by
  induction t with
  | leaf j =>
    have : j = a := of_decide_eq_true h
    simp [Tree.parts, this]
  | node b l r hl hr =>
    have hol : l.occ a ≤ 1 := by simp only [Tree.occ] at ho; omega
    have hor : r.occ a ≤ 1 := by simp only [Tree.occ] at ho; omega
    cases b <;> simp only [Tree.eval, Bool.false_eq_true, ite_false, ite_true,
      Bool.and_eq_true, Bool.or_eq_true] at h
    · rcases h with h | h
      · exact List.mem_append_left _ (hl hol h)
      · exact List.mem_append_right _ (hr hor h)
    · have ha := singleton_occ l a h.1
      have hb := singleton_occ r a h.2
      simp only [Tree.occ] at ho
      omega

def Tree.orFold (t : Tree) (ts : List Tree) : Tree := ts.foldl (.node false) t

theorem orFold_weight (ts : List Tree) (t : Tree) :
    (t.orFold ts).nodes+1 = t.nodes+1 + (ts.map (fun p => p.nodes+1)).sum := by
  induction ts generalizing t with
  | nil => simp [Tree.orFold]
  | cons p ts ih =>
    simp only [Tree.orFold, List.foldl_cons]
    rw [show (ts.foldl (Tree.node false) (Tree.node false t p)).nodes+1 = _ from ih _]
    simp [Tree.nodes, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem orFold_occ (ts : List Tree) (t : Tree) (i : ℕ) :
    (t.orFold ts).occ i = t.occ i + (ts.map (fun p => p.occ i)).sum := by
  induction ts generalizing t with
  | nil => simp [Tree.orFold]
  | cons p ts ih =>
    simp only [Tree.orFold, List.foldl_cons]
    rw [show (ts.foldl (Tree.node false) (Tree.node false t p)).occ i = _ from ih _]
    simp [Tree.occ, Nat.add_assoc]

theorem orFold_eval (ts : List Tree) (t : Tree) (x : ℕ → Bool) :
    (t.orFold ts).eval x = (t.eval x || (ts.map (fun p => p.eval x)).any id) := by
  induction ts generalizing t with
  | nil => simp [Tree.orFold]
  | cons p ts ih =>
    simp only [Tree.orFold, List.foldl_cons]
    rw [show (ts.foldl (Tree.node false) (Tree.node false t p)).eval x = _ from ih _]
    simp [Tree.eval, Bool.or_assoc]

def Same (t u : Tree) : Prop :=
  u.nodes = t.nodes ∧ (∀ i, u.occ i = t.occ i) ∧ ∀ x, u.eval x = t.eval x

theorem same_refl (t : Tree) : Same t t := ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem same_node (b : Bool) {l l' r r' : Tree} (hl : Same l l') (hr : Same r r') :
    Same (.node b l r) (.node b l' r') := by
  refine ⟨by simp [Tree.nodes, hl.1, hr.1], ?_, ?_⟩
  · intro i; simp [Tree.occ, hl.2.1 i, hr.2.1 i]
  · intro x; simp [Tree.eval, hl.2.2 x, hr.2.2 x]

def Tree.hasOr (a b : ℕ) : Tree → Prop
  | .leaf _ => False
  | .node op l r => (op = false ∧ l = .leaf a ∧ r = .leaf b) ∨ l.hasOr a b ∨ r.hasOr a b

theorem hasOr_fold {t : Tree} (ts : List Tree) {a b : ℕ} (h : t.hasOr a b) :
    (t.orFold ts).hasOr a b := by
  induction ts generalizing t with
  | nil => exact h
  | cons p ts ih => exact ih (Or.inr (Or.inl h))

theorem expose_singletons (t : Tree) (a b : ℕ) (hab : a ≠ b)
    (hoa : t.occ a ≤ 1) (hob : t.occ b ≤ 1)
    (ha : t.eval (fun i => decide (i = a)) = true)
    (hb : t.eval (fun i => decide (i = b)) = true) :
    ∃ u, Same t u ∧ u.hasOr a b := by
  classical
  have hma := singleton_part t a hoa ha
  have hmb := singleton_part t b hob hb
  have hne : Tree.leaf b ≠ Tree.leaf a := by simpa using Ne.symm hab
  have hmb' : Tree.leaf b ∈ t.parts.erase (.leaf a) :=
    (List.mem_erase_of_ne hne).mpr hmb
  let rest := (t.parts.erase (.leaf a)).erase (.leaf b)
  have hp : t.parts.Perm (.leaf a :: .leaf b :: rest) :=
    (List.perm_cons_erase hma).trans ((List.perm_cons_erase hmb').cons _)
  let u := (Tree.node false (.leaf a) (.leaf b)).orFold rest
  refine ⟨u, ⟨?_, ?_, ?_⟩, hasOr_fold rest (Or.inl ⟨rfl,rfl,rfl⟩)⟩
  · have hw := (hp.map (fun p => p.nodes+1)).sum_eq
    rw [parts_weight] at hw
    have hu := orFold_weight rest (Tree.node false (.leaf a) (.leaf b))
    simp only [List.map_cons, List.sum_cons, Tree.nodes] at hw hu
    change u.nodes = t.nodes
    dsimp [u] at *
    omega
  · intro i
    have hw := (hp.map (fun p => p.occ i)).sum_eq
    rw [parts_occ] at hw
    simp only [List.map_cons, List.sum_cons] at hw
    simpa [u, orFold_occ, Tree.occ, Nat.add_assoc] using hw.symm
  · intro x
    have hw := (hp.map (fun p => p.eval x)).any_eq (f := id)
    rw [parts_eval] at hw
    simp only [List.map_cons, List.any_cons, id_eq] at hw
    simpa [u, orFold_eval, Tree.eval, Bool.or_assoc] using hw.symm

theorem eval_agree (t : Tree) (x y : ℕ → Bool)
    (h : ∀ i, 0 < t.occ i → x i = y i) : t.eval x = t.eval y := by
  induction t with
  | leaf j => exact h j (by simp [Tree.occ])
  | node b l r hl hr =>
    have hL : l.eval x = l.eval y := hl (fun i hi => h i (by simp only [Tree.occ]; omega))
    have hR : r.eval x = r.eval y := hr (fun i hi => h i (by simp only [Tree.occ]; omega))
    simp [Tree.eval, hL, hR]

def pair (a b : ℕ) : ℕ → Bool := fun i => decide (i = a ∨ i = b)
def single (a : ℕ) : ℕ → Bool := fun i => decide (i = a)

theorem pair_absent (t : Tree) (a b : ℕ) (h : t.occ a = 0) :
    t.eval (pair a b) = t.eval (single b) := by
  apply eval_agree
  intro i hi
  have hia : i ≠ a := by intro e; subst i; omega
  simp [pair, single, hia]

theorem pair_uses (t : Tree) (a b : ℕ) (h : t.eval (pair a b) = true)
    (hb : t.eval (single b) = false) : 0 < t.occ a := by
  by_contra hn
  have hz : t.occ a = 0 := by omega
  rw [pair_absent t a b hz, hb] at h
  contradiction

theorem expose_pairs (t : Tree) (a b c : ℕ) (hbc : b ≠ c)
    (hro : ∀ i, t.occ i ≤ 1)
    (ha : t.eval (single a) = false) (hb : t.eval (single b) = false)
    (hc : t.eval (single c) = false)
    (hab : t.eval (pair a b) = true) (hac : t.eval (pair a c) = true) :
    ∃ u, Same t u ∧ u.hasOr b c := by
  induction t with
  | leaf j =>
    simp only [Tree.eval, single, decide_eq_false_iff_not] at ha hb
    simp only [Tree.eval, pair, decide_eq_true_eq] at hab
    tauto
  | node op l r hl hr =>
    have hrol : ∀ i, l.occ i ≤ 1 := by
      intro i; have := hro i; simp only [Tree.occ] at this; omega
    have hror : ∀ i, r.occ i ≤ 1 := by
      intro i; have := hro i; simp only [Tree.occ] at this; omega
    cases op
    · simp only [Tree.eval, Bool.false_eq_true, ite_false, Bool.or_eq_false_iff,
        Bool.or_eq_true] at ha hb hc hab hac
      by_cases hal : l.occ a = 0
      · have hlb : l.eval (pair a b) = false := (pair_absent l a b hal).trans hb.1
        have hlc : l.eval (pair a c) = false := (pair_absent l a c hal).trans hc.1
        have hrb : r.eval (pair a b) = true := hab.resolve_left (by simp [hlb])
        have hrc : r.eval (pair a c) = true := hac.resolve_left (by simp [hlc])
        obtain ⟨u, hu, hU⟩ := hr hror ha.2 hb.2 hc.2 hrb hrc
        exact ⟨.node false l u, same_node false (same_refl l) hu, Or.inr (Or.inr hU)⟩
      · have har : r.occ a = 0 := by have := hro a; simp only [Tree.occ] at this; omega
        have hrb : r.eval (pair a b) = false := (pair_absent r a b har).trans hb.2
        have hrc : r.eval (pair a c) = false := (pair_absent r a c har).trans hc.2
        have hlb : l.eval (pair a b) = true := hab.resolve_right (by simp [hrb])
        have hlc : l.eval (pair a c) = true := hac.resolve_right (by simp [hrc])
        obtain ⟨u, hu, hU⟩ := hl hrol ha.1 hb.1 hc.1 hlb hlc
        exact ⟨.node false u r, same_node false hu (same_refl r), Or.inr (Or.inl hU)⟩
    · simp only [Tree.eval, ite_true, Bool.and_eq_true] at hab hac
      by_cases hal : l.occ a = 0
      · have hbl : l.eval (single b) = true := (pair_absent l a b hal).symm.trans hab.1
        have hcl : l.eval (single c) = true := (pair_absent l a c hal).symm.trans hac.1
        obtain ⟨u, hu, hU⟩ := expose_singletons l b c hbc (hrol b) (hrol c) hbl hcl
        exact ⟨.node true u r, same_node true hu (same_refl r), Or.inr (Or.inl hU)⟩
      · have har : r.occ a = 0 := by have := hro a; simp only [Tree.occ] at this; omega
        have hbr : r.eval (single b) = true := (pair_absent r a b har).symm.trans hab.2
        have hcr : r.eval (single c) = true := (pair_absent r a c har).symm.trans hac.2
        obtain ⟨u, hu, hU⟩ := expose_singletons r b c hbc (hror b) (hror c) hbr hcr
        exact ⟨.node true l u, same_node true (same_refl l) hu, Or.inr (Or.inr hU)⟩

def Tree.begins (a b : ℕ) : Tree → Prop
  | .leaf _ => False
  | .node op l r => (op = false ∧ l = .leaf a ∧ r = .leaf b) ∨ l.begins a b

theorem orient (t : Tree) (a b : ℕ) (h : t.hasOr a b) :
    ∃ u, Same t u ∧ u.begins a b := by
  induction t with
  | leaf i => exact False.elim h
  | node op l r hl hr =>
    rcases h with h | h | h
    · exact ⟨.node op l r, same_refl _, Or.inl h⟩
    · obtain ⟨u, hu, hU⟩ := hl h
      exact ⟨.node op u r, same_node op hu (same_refl r), Or.inr hU⟩
    · obtain ⟨u, hu, hU⟩ := hr h
      refine ⟨.node op u l, ⟨?_, ?_, ?_⟩, Or.inr hU⟩
      · simp [Tree.nodes, hu.1, Nat.add_comm]
      · intro i; simp [Tree.occ, hu.2.1 i, Nat.add_comm]
      · intro x; simp [Tree.eval, hu.2.2 x, Bool.and_comm, Bool.or_comm]

theorem bound_iff (t : Tree) (n : ℕ) : t.bound n ↔ ∀ i, n ≤ i → t.occ i = 0 := by
  refine ⟨fun h i hi => occ_zero_of_bound t h hi, ?_⟩
  induction t with
  | leaf j =>
    intro h
    change j < n
    by_contra hn
    have := h j (by omega)
    simp [Tree.occ] at this
  | node b l r hl hr =>
    intro h
    refine ⟨hl (fun i hi => ?_), hr (fun i hi => ?_)⟩
    all_goals have := h i hi; simp only [Tree.occ] at this; omega

theorem same_bound {t u : Tree} (h : Same t u) {n : ℕ} (ht : t.bound n) : u.bound n := by
  rw [bound_iff] at ht ⊢
  intro i hi
  rw [h.2.1 i]
  exact ht i hi

def reads (gs : List Gate) (i : ℕ) : ℕ := (gs.map (fun g => g.inputs.count i)).sum

@[simp] theorem reads_nil (i : ℕ) : reads [] i = 0 := rfl

@[simp] theorem reads_append (gs hs : List Gate) (i : ℕ) :
    reads (gs ++ hs) i = reads gs i + reads hs i := by simp [reads]

@[simp] theorem reads_one (g : Gate) (i : ℕ) : reads [g] i = g.inputs.count i := by simp [reads]

def op (b : Bool) : GateOp := if b then .and else .or

def Tree.emit (t : Tree) (base : ℕ) : Circuit := match t with
  | .leaf i => ⟨[], i⟩
  | .node b l r =>
    let L := l.emit base
    let R := r.emit (base + l.nodes)
    ⟨L.gates ++ R.gates ++ [⟨op b, [L.output, R.output]⟩], base+l.nodes+r.nodes⟩

theorem emit_size (t : Tree) (base : ℕ) : (t.emit base).size = t.nodes := by
  induction t generalizing base with
  | leaf i => rfl
  | node b l r hl hr =>
    have hL := hl base
    have hR := hr (base+l.nodes)
    simp only [Circuit.size] at hL hR
    simp [Tree.emit, Circuit.size, Tree.nodes, hL, hR, Nat.add_assoc]

theorem emit_count (t : Tree) (base i : ℕ) :
    reads (t.emit base).gates i + (if i = (t.emit base).output then 1 else 0) =
      t.occ i + (if base ≤ i ∧ i < base+t.nodes then 1 else 0) := by
  induction t generalizing base with
  | leaf j =>
    by_cases hij : i = j <;>
      simp [Tree.emit, Tree.occ, Tree.nodes, hij, show ¬(base ≤ i ∧ i < base) by omega]
  | node b l r hl hr =>
    have hL := hl base
    have hR := hr (base+l.nodes)
    have partition :
        (if base ≤ i ∧ i < base+l.nodes then 1 else 0) +
        (if base+l.nodes ≤ i ∧ i < base+l.nodes+r.nodes then 1 else 0) +
        (if i = base+l.nodes+r.nodes then 1 else 0) =
        (if base ≤ i ∧ i < base+(l.nodes+r.nodes+1) then 1 else 0) := by
      split_ifs <;> omega
    simp only [Tree.emit, reads_append, reads_one, List.count_cons, List.count_nil,
      Circuit.output, Tree.occ, Tree.nodes]
    simp only [beq_iff_eq, eq_comm (a := i), Nat.add_zero, Nat.add_assoc] at *
    omega

theorem bound_mono {t : Tree} {n m : ℕ} (h : t.bound n) (hnm : n ≤ m) : t.bound m := by
  rw [bound_iff] at h ⊢
  exact fun i hi => h i (hnm.trans hi)

def Back (base : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < base+j

theorem back_append {base : ℕ} {gs hs : List Gate} (hg : Back base gs)
    (hh : Back (base+gs.length) hs) : Back base (gs++hs) := by
  intro j hj i hi
  by_cases hjg : j < gs.length
  · rw [List.getElem_append_left hjg] at hi
    exact hg j hjg i hi
  · have hjh : j-gs.length < hs.length := by simp only [List.length_append] at hj; omega
    rw [List.getElem_append_right (by omega)] at hi
    have h := hh (j-gs.length) hjh i hi
    omega

theorem back_one {base : ℕ} {g : Gate} (h : ∀ i ∈ g.inputs, i < base) : Back base [g] := by
  intro j hj i hi
  have : j = 0 := by simp only [List.length_singleton] at hj; omega
  subst j
  exact h i hi

theorem emit_output (t : Tree) (base : ℕ) (h : t.bound base) :
    (t.emit base).output < base+t.nodes := by
  cases t with
  | leaf i => exact h
  | node b l r => simp only [Tree.emit, Tree.nodes]; omega

theorem emit_back (t : Tree) (base : ℕ) (h : t.bound base) : Back base (t.emit base).gates := by
  induction t generalizing base with
  | leaf i => intro j hj; simp [Tree.emit] at hj
  | node b l r hl hr =>
    have hL := hl base h.1
    have hR := hr (base+l.nodes) (bound_mono h.2 (by omega))
    have hLb := emit_output l base h.1
    have hRb := emit_output r (base+l.nodes) (bound_mono h.2 (by omega))
    have hsL : (l.emit base).gates.length = l.nodes := emit_size l base
    have hsR : (r.emit (base+l.nodes)).gates.length = r.nodes := emit_size r (base+l.nodes)
    apply back_append (back_append hL (by simpa [hsL] using hR))
    apply back_one
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    simp only [List.length_append, hsL, hsR]
    rcases hi with rfl | rfl <;> omega

theorem emit_shape (t : Tree) (base : ℕ) :
    ∀ g ∈ (t.emit base).gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
  induction t generalizing base with
  | leaf i => simp [Tree.emit]
  | node b l r hl hr =>
    intro g hg
    simp only [Tree.emit, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact hl base g hg
    · exact hr (base+l.nodes) g hg
    · cases b <;> simp [op]

theorem emit_terminal (t : Tree) (base : ℕ) (h : t.bound base) :
    (t.emit base).output+1 = base+(t.emit base).size ∨
      ((t.emit base).size = 0 ∧ (t.emit base).output < base) := by
  cases t with
  | leaf i => exact Or.inr ⟨rfl,h⟩
  | node b l r => left; rw [emit_size]; simp only [Tree.emit, Tree.nodes]; omega

theorem reads_eq (C : Circuit) (i : ℕ) :
    reads C.gates i = readsIn C (Finset.range C.size) i := by
  unfold reads readsIn Circuit.size gateAt
  rw [Finset.sum_range, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    have hj : j < C.gates.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ hj]

theorem emit_reads (t : Tree) (base : ℕ) (h : t.bound base) (hro : ∀ i, t.occ i ≤ 1) :
    (∀ i < base, reads (t.emit base).gates i ≤ 1) ∧
    ∀ j < (t.emit base).size, reads (t.emit base).gates (base+j) =
      if j+1 = (t.emit base).size then 0 else 1 := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have hc := emit_count t base i
    have hr := hro i
    simp only [show ¬(base ≤ i ∧ i < base+t.nodes) by omega, ite_false] at hc
    omega
  · intro j hj
    rw [emit_size] at hj ⊢
    have hc := emit_count t base (base+j)
    have hz := occ_zero_of_bound t h (show base ≤ base+j by omega)
    have ht := emit_terminal t base h
    rw [emit_size] at ht
    have ht' : (t.emit base).output+1 = base+t.nodes := by rcases ht with ht | ht <;> omega
    have heq : (base+j = (t.emit base).output) ↔ j+1 = t.nodes := by omega
    have hi : base ≤ base+j ∧ base+j < base+t.nodes := by omega
    simp only [hz, if_pos hi, Nat.zero_add, heq] at hc
    by_cases hjlast : j+1 = t.nodes
    · have he : base+j = (t.emit base).output := heq.mpr hjlast
      simp [hjlast, he] at hc ⊢
      omega
    · have he : base+j ≠ (t.emit base).output := fun e => hjlast (heq.mp e)
      simp [hjlast, he] at hc ⊢
      omega

theorem head_append {gs hs : List Gate} {g : Gate} (h : gs[0]? = some g) :
    (gs++hs)[0]? = some g := by cases gs <;> simpa using h

theorem emit_first (t : Tree) (base a b : ℕ) (h : t.begins a b) :
    (t.emit base).gates[0]? = some ⟨.or,[a,b]⟩ := by
  induction t generalizing base with
  | leaf i => exact False.elim h
  | node op l r hl hr =>
    rcases h with ⟨rfl,rfl,rfl⟩ | h
    · rfl
    · exact head_append (head_append (hl base h))

def run (gs : List Gate) (p : List Bool) := (⟨gs,0⟩ : Circuit).wires p

theorem run_append (a b : List Gate) (p : List Bool) :
    run (a++b) p = run b (run a p) := by simp [run,Circuit.wires,List.foldl_append]

theorem run_ext (gs : List Gate) (p : List Bool) :
    ∃ tail, run gs p = p ++ tail ∧ tail.length = gs.length := by
  induction gs generalizing p with
  | nil => exact ⟨[],by simp [run,Circuit.wires],rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map (fun i => p.getD i false))
    obtain ⟨t,eq,lt⟩ := ih (p++[v])
    exact ⟨v::t, by simpa [run,Circuit.wires,v] using eq, by simp [lt]⟩

theorem run_length (gs : List Gate) (p : List Bool) :
    (run gs p).length = p.length+gs.length := by
  obtain ⟨_,e,h⟩ := run_ext gs p
  simp [e,h]

theorem run_keep (gs : List Gate) (p : List Bool) (i : ℕ) (hi : i < p.length) :
    (run gs p).getD i false = p.getD i false := by
  obtain ⟨t,eq,_⟩ := run_ext gs p
  simp [eq,List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem run_terminal (gs : List Gate) (p : List Bool) (g : Gate) :
    (run (gs++[g]) p).getD (p.length+gs.length) false =
      g.op.eval (g.inputs.map (fun i => (run gs p).getD i false)) := by
  rw [run_append, ← run_length]
  simp [run,Circuit.wires,List.getD_eq_getElem?_getD]

theorem eval_run_keep (t : Tree) (gs : List Gate) (p : List Bool) (h : t.bound p.length) :
    t.eval (fun i => (run gs p).getD i false) = t.eval (fun i => p.getD i false) := by
  apply eval_agree
  intro i hi
  apply run_keep
  by_contra hn
  have hz := occ_zero_of_bound t h (show p.length ≤ i by omega)
  omega

theorem emit_eval (t : Tree) (p : List Bool) (h : t.bound p.length) :
    (run (t.emit p.length).gates p).getD (t.emit p.length).output false =
      t.eval (fun i => p.getD i false) := by
  induction t generalizing p with
  | leaf i => rfl
  | node b l r hl hr =>
    let L := l.emit p.length
    let R := r.emit (p.length+l.nodes)
    have lenL : L.gates.length = l.nodes := emit_size l p.length
    have lenR : R.gates.length = r.nodes := emit_size r (p.length+l.nodes)
    have runLen : (run L.gates p).length = p.length+l.nodes := by simp [run_length, lenL]
    have hLv := hl p h.1
    have hRv := hr (run L.gates p) (by rw [runLen]; exact bound_mono h.2 (by omega))
    rw [runLen] at hRv
    change (run L.gates p).getD L.output false = _ at hLv
    change (run R.gates (run L.gates p)).getD R.output false = _ at hRv
    have keepL : (run R.gates (run L.gates p)).getD L.output false =
        (run L.gates p).getD L.output false := by
      apply run_keep
      rw [runLen]
      exact emit_output l p.length h.1
    have outLen : p.length+l.nodes+r.nodes = p.length+(L.gates++R.gates).length := by
      simp [lenL,lenR,Nat.add_assoc]
    change (run ((L.gates++R.gates)++[⟨op b,[L.output,R.output]⟩]) p).getD
      (p.length+l.nodes+r.nodes) false = _
    rw [outLen,run_terminal,run_append]
    cases b
    all_goals
      simp only [op,Bool.false_eq_true,ite_false,ite_true,GateOp.eval,List.map_cons,List.map_nil,
        List.all_cons,List.all_nil,List.any_cons,List.any_nil,id_eq,Bool.and_true,Bool.or_false,Tree.eval]
      rw [keepL,hLv,hRv,eval_run_keep r L.gates p h.2]

def Shape (g : Gate) : Prop := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

theorem shape_decomp {g : Gate} (h : Shape g) : ∃ b a c, g = ⟨op b,[a,c]⟩ := by
  rcases g with ⟨o,ins⟩
  obtain ⟨ho,hlen⟩ := h
  rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d,rest⟩⟩⟩ <;> simp at hlen
  rcases ho with rfl | rfl
  · exact ⟨true,a,c,rfl⟩
  · exact ⟨false,a,c,rfl⟩

def gateTree (g : Gate) : Tree :=
  .node (match g.op with | .and => true | _ => false)
    (.leaf (g.inputs.getD 0 0)) (.leaf (g.inputs.getD 1 0))

theorem gateTree_formula (b : Bool) (a c : ℕ) :
    gateTree ⟨op b,[a,c]⟩ = .node b (.leaf a) (.leaf c) := by cases b <;> simp [gateTree,op]

theorem gateTree_nodes (g : Gate) : (gateTree g).nodes = 1 := rfl

theorem gateTree_occ (g : Gate) (h : Shape g) (i : ℕ) :
    (gateTree g).occ i = g.inputs.count i := by
  obtain ⟨b,a,c,rfl⟩ := shape_decomp h
  rw [gateTree_formula]
  simp only [Tree.occ,List.count_cons,List.count_nil]
  simp only [beq_iff_eq]
  split_ifs <;> omega

theorem gateTree_bound (g : Gate) (h : Shape g) (n : ℕ) (hb : ∀ i ∈ g.inputs, i < n) :
    (gateTree g).bound n := by
  obtain ⟨b,a,c,rfl⟩ := shape_decomp h
  exact (by simpa [gateTree_formula,Tree.bound] using And.intro (hb a (by simp)) (hb c (by simp)))

theorem gateTree_eval (g : Gate) (h : Shape g) (w : List Bool) :
    (gateTree g).eval (fun i => w.getD i false) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  obtain ⟨b,a,c,rfl⟩ := shape_decomp h
  rw [gateTree_formula]
  cases b <;> simp [Tree.eval,op,GateOp.eval]

def expandRev (n : ℕ) : List Gate → Tree → Tree
  | [],t => t
  | g::gs,t => expandRev n gs (t.subst (n+gs.length) (gateTree g))

def expand (n : ℕ) (gs : List Gate) (t : Tree) := expandRev n gs.reverse t

theorem expand_snoc (n : ℕ) (gs : List Gate) (g : Gate) (t : Tree) :
    expand n (gs++[g]) t = expand n gs (t.subst (n+gs.length) (gateTree g)) := by
  simp [expand,expandRev]

theorem getD_snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l++[b]).getD i false = if i = l.length then b else l.getD i false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | rfl | h
  · simp [List.getElem?_append_left h,ne_of_lt h]
  · simp
  · have h2 : l.length+1 ≤ i := by omega
    simp [List.getElem?_eq_none h.le,
      List.getElem?_eq_none (by simpa using h2 : (l++[b]).length ≤ i),ne_of_gt h]

theorem expand_eval (n : ℕ) (gs : List Gate) (t : Tree) (p : List Bool) (hp : p.length = n)
    (hg : ∀ g ∈ gs, Shape g) :
    (expand n gs t).eval (fun i => p.getD i false) =
      t.eval (fun i => (run gs p).getD i false) := by
  induction gs using List.reverseRecOn generalizing t with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [expand_snoc,ih _ (fun v hv => hg v (by simp [hv])),subst_eval]
    have len := run_length gs p
    rw [hp] at len
    rw [gateTree_eval g (hg g (by simp))]
    congr 1
    funext i
    rw [run_append]
    change _ = ((run gs p)++[g.op.eval (g.inputs.map (fun i => (run gs p).getD i false))]).getD i false
    rw [getD_snoc,len]

theorem back_prefix {n : ℕ} {gs hs : List Gate} (h : Back n (gs++hs)) : Back n gs := by
  intro j hj i hi
  have hja : j < (gs++hs).length := by simp; omega
  apply h j hja i
  simpa [List.getElem_append_left hj] using hi

theorem reads_zero {n : ℕ} {gs : List Gate} (hb : Back n gs) (i : ℕ) (hi : n+gs.length ≤ i) :
    reads gs i = 0 := by
  unfold reads
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,hj,hjg⟩ := List.getElem_of_mem hg
  apply List.count_eq_zero.mpr
  intro hm
  have := hb j hj i (by simpa [hjg] using hm)
  omega

theorem expand_tree (n : ℕ) (gs : List Gate) (t : Tree)
    (hg : ∀ g ∈ gs, Shape g) (hb : Back n gs) (ht : t.bound (n+gs.length))
    (hinternal : ∀ j < gs.length, t.occ (n+j)+reads gs (n+j) = 1)
    (hinput : ∀ i < n, t.occ i+reads gs i ≤ 1) :
    (expand n gs t).bound n ∧ (expand n gs t).nodes = t.nodes+gs.length ∧
      ∀ i, (expand n gs t).occ i ≤ 1 := by
  induction gs using List.reverseRecOn generalizing t with
  | nil =>
    refine ⟨ht, by simp [expand,expandRev], ?_⟩
    intro i
    by_cases hi : i < n
    · simpa [expand,expandRev] using hinput i hi
    · have hz := occ_zero_of_bound t ht (show n+[].length ≤ i by simpa using Nat.le_of_not_gt hi)
      simpa [expand,expandRev,hz]
  | append_singleton gs g ih =>
    have hg' : ∀ v ∈ gs, Shape v := fun v hv => hg v (by simp [hv])
    have hgg : Shape g := hg g (by simp)
    have hb' : Back n gs := back_prefix hb
    have hlast : ∀ i ∈ g.inputs, i < n+gs.length := by
      intro i hi
      apply hb gs.length (by simp) i
      simpa using hi
    have hgc : g.inputs.count (n+gs.length) = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      have := hlast _ hm
      omega
    have hone : t.occ (n+gs.length) = 1 := by
      have hh := hinternal gs.length (by simp)
      simpa only [reads_append,reads_one,reads_zero hb' (n+gs.length) (by omega),hgc,
        Nat.add_zero] using hh
    let u := t.subst (n+gs.length) (gateTree g)
    have hu : u.bound (n+gs.length) := by
      apply subst_bound t (gateTree g) (n+gs.length) (n+gs.length)
      · simpa [List.length_append,Nat.add_assoc] using ht
      · exact gateTree_bound g hgg _ hlast
      · rfl
    have huc : ∀ j < gs.length, u.occ (n+j)+reads gs (n+j) = 1 := by
      intro j hj
      have hold := hinternal j (by simp; omega)
      rw [reads_append,reads_one] at hold
      change (t.subst _ _).occ _+_ = _
      rw [subst_occ,if_neg (by omega),hone,gateTree_occ g hgg,Nat.one_mul]
      omega
    have hui : ∀ i < n, u.occ i+reads gs i ≤ 1 := by
      intro i hi
      have hold := hinput i hi
      rw [reads_append,reads_one] at hold
      change (t.subst _ _).occ _+_ ≤ _
      rw [subst_occ,if_neg (by omega),hone,gateTree_occ g hgg,Nat.one_mul]
      omega
    have hun : u.nodes = t.nodes+1 := by simp [u,subst_nodes,hone,gateTree_nodes]
    obtain ⟨hbound,hsize,honce⟩ := ih u hg' hb' hu huc hui
    rw [expand_snoc]
    refine ⟨hbound, ?_, honce⟩
    change (expand n gs u).nodes = _
    rw [hsize,hun]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

def IsTree (n : ℕ) (C : Circuit) : Prop :=
  (∀ g ∈ C.gates, Shape g) ∧ ReadsBack n C ∧
  (C.output+1 = n+C.size ∨ (C.size = 0 ∧ C.output < n)) ∧
  (∀ i < n, readsIn C (Finset.range C.size) i ≤ 1) ∧
  (∀ j < C.size, readsIn C (Finset.range C.size) (n+j) = if j+1 = C.size then 0 else 1)

theorem back_iff (n : ℕ) (C : Circuit) : Back n C.gates ↔ ReadsBack n C := by
  constructor
  · intro h j hj i hi
    rw [gateAt,List.getD_eq_getElem _ _ hj] at hi
    exact h j hj i hi
  · intro h j hj i hi
    apply h j hj i
    rwa [gateAt,List.getD_eq_getElem _ _ hj]

theorem emit_tree (t : Tree) (n : ℕ) (hb : t.bound n) (hro : ∀ i, t.occ i ≤ 1) :
    IsTree n (t.emit n) := by
  obtain ⟨hr,hg⟩ := emit_reads t n hb hro
  refine ⟨emit_shape t n,(back_iff n _).mp (emit_back t n hb),emit_terminal t n hb,?_,?_⟩
  · intro i hi; rw [← reads_eq]; exact hr i hi
  · intro j hj; rw [← reads_eq]; exact hg j hj

theorem recover (n : ℕ) (C : Circuit) (h : IsTree n C) :
    ∃ t : Tree, t.bound n ∧ t.nodes = C.size ∧ (∀ i, t.occ i ≤ 1) ∧
      ∀ p : List Bool, p.length = n → t.eval (fun i => p.getD i false) = C.eval p := by
  obtain ⟨hshape,hback,hterm,hinput,hgate⟩ := h
  have hb := (back_iff n C).mpr hback
  have hout : C.output < n+C.size := by rcases hterm with h | ⟨hs,ho⟩ <;> omega
  have ht : (Tree.leaf C.output).bound (n+C.gates.length) := hout
  have hint : ∀ j < C.gates.length,
      (Tree.leaf C.output).occ (n+j)+reads C.gates (n+j) = 1 := by
    intro j hj
    change j < C.size at hj
    have hr := hgate j hj
    rw [← reads_eq] at hr
    have hlast : C.output+1 = n+C.size := by rcases hterm with h | ⟨hs,ho⟩ <;> omega
    simp only [Tree.occ,hr]
    split_ifs <;> omega
  have hin : ∀ i < n, (Tree.leaf C.output).occ i+reads C.gates i ≤ 1 := by
    intro i hi
    by_cases hs : C.size = 0
    · have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hs
      simp [Tree.occ,hnil]
      split_ifs <;> omega
    · have ho : i ≠ C.output := by rcases hterm with h | h <;> omega
      have hr := hinput i hi
      rw [← reads_eq] at hr
      simpa [Tree.occ,ho] using hr
  let t := expand n C.gates (.leaf C.output)
  obtain ⟨hbound,hnodes,honce⟩ := expand_tree n C.gates (.leaf C.output) hshape hb ht hint hin
  refine ⟨t,hbound,?_,honce,?_⟩
  · simpa [Tree.nodes,Circuit.size] using hnodes
  · intro p hp
    exact expand_eval n C.gates (.leaf C.output) p hp hshape

def value {n : ℕ} (C : Circuit) (s : Finset (Fin n)) : Bool :=
  C.eval (List.ofFn (fun z : Fin n => decide (z ∈ s)))

theorem getD_ofFn (n : ℕ) (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i,h⟩ else false := by
  by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi]

theorem input_single {n : ℕ} (a : Fin n) :
    (fun i => (List.ofFn (fun z : Fin n => decide (z ∈ ({a} : Finset (Fin n))))).getD i false) =
      single a.val := by
  funext i
  rw [getD_ofFn]
  by_cases hi : i < n
  · simp [hi,Fin.ext_iff,single]
  · have hia : i ≠ a.val := by have := a.isLt; omega
    simp [hi,single,hia]

theorem input_pair {n : ℕ} (a b : Fin n) :
    (fun i => (List.ofFn (fun z : Fin n => decide (z ∈ ({a,b} : Finset (Fin n))))).getD i false) =
      pair a.val b.val := by
  funext i
  rw [getD_ofFn]
  by_cases hi : i < n
  · simp [hi,Fin.ext_iff,pair]
  · have hia : i ≠ a.val := by have := a.isLt; omega
    have hib : i ≠ b.val := by have := b.isLt; omega
    simp [hi,pair,hia,hib]

theorem main (N : ℕ) (F : Circuit) (x : Fin 3 ↪ Fin N)
    (hF : IsTree N F) (_hz : value F (∅ : Finset (Fin N)) = false)
    (hs : ∀ i : Fin 3, value F {x i} = false)
    (h01 : value F {x 0,x 1} = true) (h02 : value F {x 0,x 2} = true) :
    ∃ G : Circuit, IsTree N G ∧ G.size = F.size ∧
      G.gates[0]? = some ⟨.or,[(x 1).val,(x 2).val]⟩ ∧
      ∀ s : Finset (Fin N), value G s = value F s := by
  obtain ⟨t,hb,hn,hr,he⟩ := recover N F hF
  have hsingle (i : Fin 3) : t.eval (single (x i).val) = false := by
    have h := he (List.ofFn (fun z : Fin N => decide (z ∈ ({x i} : Finset (Fin N))))) (by simp)
    rw [input_single] at h
    exact h.trans (hs i)
  have hpair01 : t.eval (pair (x 0).val (x 1).val) = true := by
    have h := he (List.ofFn (fun z : Fin N => decide (z ∈ ({x 0,x 1} : Finset (Fin N))))) (by simp)
    rw [input_pair] at h
    exact h.trans h01
  have hpair02 : t.eval (pair (x 0).val (x 2).val) = true := by
    have h := he (List.ofFn (fun z : Fin N => decide (z ∈ ({x 0,x 2} : Finset (Fin N))))) (by simp)
    rw [input_pair] at h
    exact h.trans h02
  have hbc : (x 1).val ≠ (x 2).val := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (x.injective (Fin.ext h))
  obtain ⟨u,hu,hOr⟩ := expose_pairs t (x 0).val (x 1).val (x 2).val hbc hr
    (hsingle 0) (hsingle 1) (hsingle 2) hpair01 hpair02
  obtain ⟨v,hv,hfirst⟩ := orient u (x 1).val (x 2).val hOr
  have hvb : v.bound N := same_bound hv (same_bound hu hb)
  have hvr : ∀ i, v.occ i ≤ 1 := by intro i; rw [hv.2.1 i,hu.2.1 i]; exact hr i
  refine ⟨v.emit N,emit_tree v N hvb hvr,?_,emit_first v N _ _ hfirst,?_⟩
  · rw [emit_size,hv.1,hu.1,hn]
  · intro s
    let p := List.ofFn (fun z : Fin N => decide (z ∈ s))
    have hp : p.length = N := by simp [p]
    have hev := emit_eval v p (by simpa [hp] using hvb)
    rw [hp] at hev
    exact hev.trans ((hv.2.2 _).trans ((hu.2.2 _).trans (he p hp)))

end PEqualNP.Outside.L_lib_806_aux

theorem PEqualNP.Outside.L_lib_806 : (∀ (N : Nat) (F : PEqualNP.CircuitLowerBounds.Circuit) (x : Fin 3 ↪ Fin N),
  let tree := fun D : PEqualNP.CircuitLowerBounds.Circuit =>
    (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack N D ∧
    (D.output + 1 = N + D.size ∨ (D.size = 0 ∧ D.output < N)) ∧
    (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) i ≤ 1) ∧
    (∀ j < D.size, PEqualNP.MetaComplexity.NestedCover.readsIn D (Finset.range D.size) (N+j) =
      if j+1 = D.size then 0 else 1)
  let val := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (s : Finset (Fin N)) =>
    D.eval (List.ofFn (fun z : Fin N => decide (z ∈ s)))
  tree F → val F ∅ = false → (∀ i : Fin 3, val F {x i} = false) →
  val F {x 0,x 1} = true → val F {x 0,x 2} = true →
  ∃ G : PEqualNP.CircuitLowerBounds.Circuit, tree G ∧ G.size = F.size ∧
    G.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [(x 1).val,(x 2).val]⟩ ∧
    ∀ s : Finset (Fin N), val G s = val F s) := by
  exact PEqualNP.Outside.L_lib_806_aux.main
