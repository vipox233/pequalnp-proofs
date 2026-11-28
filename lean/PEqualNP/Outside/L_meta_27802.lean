import PEqualNP.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

namespace PEqualNP.Outside.L_meta_27802_aux

open PEqualNP.CircuitLowerBounds

-- Lower bound (the transposition and partition argument of the desk's sketch).

-- Part A. The affine form of a wire on one-hot inputs: a constant and a linear part over ZMod 2.

abbrev Rep (n : ℕ) := Bool × (Fin n → ZMod 2)

def rzero (n : ℕ) : Rep n := (false, 0)

def rval {n : ℕ} (r : Rep n) (i : Fin n) : Bool := xor r.1 (decide (r.2 i = 1))

def grep {n : ℕ} (op : GateOp) : List ℕ → List (Rep n) → Rep n
  | [], _ => (op.eval [], 0)
  | [u], L =>
    (xor (op.eval [false]) (xor (op.eval [true]) (op.eval [false]) && (L.getD u (rzero n)).1),
      if xor (op.eval [true]) (op.eval [false]) then (L.getD u (rzero n)).2 else 0)
  | [u, w], L =>
    (xor (xor (op.eval [false, false])
        (xor (op.eval [true, false]) (op.eval [false, false]) && (L.getD u (rzero n)).1))
        (xor (op.eval [false, true]) (op.eval [false, false]) && (L.getD w (rzero n)).1),
      (if xor (op.eval [true, false]) (op.eval [false, false]) then (L.getD u (rzero n)).2 else 0) +
      (if xor (op.eval [false, true]) (op.eval [false, false]) then (L.getD w (rzero n)).2 else 0))
  | _ :: _ :: _ :: _, _ => rzero n

lemma eval_one (op : GateOp) (x : Bool) :
    op.eval [x] = xor (op.eval [false]) (xor (op.eval [true]) (op.eval [false]) && x) := by
  have H : ∀ a c y : Bool, cond y c a = xor a (xor c a && y) := by decide
  cases x
  · exact H (op.eval [false]) (op.eval [true]) false
  · exact H (op.eval [false]) (op.eval [true]) true

lemma eval_two (op : GateOp)
    (h : (op.eval [false, false] ^^ op.eval [false, true] ^^ op.eval [true, false] ^^
      op.eval [true, true]) = false) (x y : Bool) :
    op.eval [x, y] = xor (xor (op.eval [false, false])
        (xor (op.eval [true, false]) (op.eval [false, false]) && x))
        (xor (op.eval [false, true]) (op.eval [false, false]) && y) := by
  have H : ∀ a b c d : Bool, (a ^^ b ^^ c ^^ d) = false → ∀ x y : Bool,
      cond x (cond y d c) (cond y b a) = xor (xor a (xor c a && x)) (xor b a && y) := by decide
  have K := H _ _ _ _ h
  cases x <;> cases y
  · exact K false false
  · exact K false true
  · exact K true false
  · exact K true true

lemma key1 {n : ℕ} (c0 c1 r1 : Bool) (f : Fin n → ZMod 2) (i : Fin n) :
    xor (xor c0 (c1 && r1)) (decide ((if c1 = true then f else 0) i = 1)) =
      xor c0 (c1 && xor r1 (decide (f i = 1))) := by
  have H : ∀ (c0 c1 r1 : Bool) (z : ZMod 2),
      xor (xor c0 (c1 && r1)) (decide ((if c1 = true then z else 0) = 1)) =
      xor c0 (c1 && xor r1 (decide (z = 1))) := by decide
  have e : (if c1 = true then f else 0) i = if c1 = true then f i else 0 := by
    split_ifs <;> rfl
  rw [e]
  exact H c0 c1 r1 (f i)

lemma key2 {n : ℕ} (c0 c1 c2 r1 q1 : Bool) (f g : Fin n → ZMod 2) (i : Fin n) :
    xor (xor (xor c0 (c1 && r1)) (c2 && q1))
      (decide (((if c1 = true then f else 0) + (if c2 = true then g else 0)) i = 1)) =
    xor (xor c0 (c1 && xor r1 (decide (f i = 1)))) (c2 && xor q1 (decide (g i = 1))) := by
  have H : ∀ (c0 c1 c2 r1 q1 : Bool) (z w : ZMod 2),
      xor (xor (xor c0 (c1 && r1)) (c2 && q1))
        (decide ((if c1 = true then z else 0) + (if c2 = true then w else 0) = 1)) =
      xor (xor c0 (c1 && xor r1 (decide (z = 1)))) (c2 && xor q1 (decide (w = 1))) := by
    decide
  have e : ((if c1 = true then f else 0) + (if c2 = true then g else 0)) i =
      (if c1 = true then f i else 0) + (if c2 = true then g i else 0) := by
    split_ifs <;> rfl
  rw [e]
  exact H c0 c1 c2 r1 q1 (f i) (g i)

-- An affine gate with at most two inputs maps affine forms to an affine form.
lemma rval_grep {n : ℕ} (op : GateOp) (ins : List ℕ) (L : List (Rep n)) (i : Fin n)
    (hlen : ins.length ≤ 2)
    (haff : ins.length = 2 → (op.eval [false, false] ^^ op.eval [false, true] ^^
          op.eval [true, false] ^^ op.eval [true, true]) = false) :
    rval (grep op ins L) i = op.eval (ins.map fun u => rval (L.getD u (rzero n)) i) := by
  match ins, hlen, haff with
  | [], _, _ =>
    show xor (op.eval []) (decide ((0 : Fin n → ZMod 2) i = 1)) = op.eval []
    simp
  | [u], _, _ =>
    show xor (xor (op.eval [false])
        (xor (op.eval [true]) (op.eval [false]) && (L.getD u (rzero n)).1))
        (decide ((if xor (op.eval [true]) (op.eval [false]) = true then
          (L.getD u (rzero n)).2 else 0) i = 1)) =
      op.eval [xor (L.getD u (rzero n)).1 (decide ((L.getD u (rzero n)).2 i = 1))]
    rw [key1]
    exact (eval_one op _).symm
  | [u, w], _, haff =>
    show xor (xor (xor (op.eval [false, false])
        (xor (op.eval [true, false]) (op.eval [false, false]) && (L.getD u (rzero n)).1))
        (xor (op.eval [false, true]) (op.eval [false, false]) && (L.getD w (rzero n)).1))
        (decide (((if xor (op.eval [true, false]) (op.eval [false, false]) = true then
          (L.getD u (rzero n)).2 else 0) +
          (if xor (op.eval [false, true]) (op.eval [false, false]) = true then
          (L.getD w (rzero n)).2 else 0)) i = 1)) =
      op.eval [xor (L.getD u (rzero n)).1 (decide ((L.getD u (rzero n)).2 i = 1)),
        xor (L.getD w (rzero n)).1 (decide ((L.getD w (rzero n)).2 i = 1))]
    rw [key2]
    exact (eval_two op (haff rfl) _ _).symm
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

def wl (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def rinit (n : ℕ) : List (Rep n) := List.ofFn (fun h : Fin n => ((false, Pi.single h 1) : Rep n))

def rl {n : ℕ} (gs : List Gate) : List (Rep n) :=
  gs.foldl (fun L g => L ++ [grep g.op g.inputs L]) (rinit n)

lemma wl_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wl (gs ++ [g]) x = wl gs x ++ [g.op.eval (g.inputs.map fun i => (wl gs x).getD i false)] := by
  simp [wl, List.foldl_append]

lemma rl_snoc {n : ℕ} (gs : List Gate) (g : Gate) :
    (rl (gs ++ [g]) : List (Rep n)) = rl gs ++ [grep g.op g.inputs (rl gs)] := by
  simp [rl, List.foldl_append]

lemma wl_length (gs : List Gate) (x : List Bool) : (wl gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wl]
  | append_singleton gs g ih =>
    rw [wl_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

lemma rl_length {n : ℕ} (gs : List Gate) : (rl gs : List (Rep n)).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [rl, rinit]
  | append_singleton gs g ih =>
    rw [rl_snoc]
    simp only [List.length_append, List.length_singleton, ih]
    omega

def Affine2 (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
    (g.op.eval [false, false] ^^ g.op.eval [false, true] ^^
      g.op.eval [true, false] ^^ g.op.eval [true, true]) = false)

-- Fact (a): on the one-hot input e_i every wire is c + a(i) for its affine form (c, a).
lemma wires_rep {n : ℕ} (i : Fin n) (gs : List Gate) : (∀ g ∈ gs, Affine2 g) → ∀ v : ℕ,
    (wl gs (List.ofFn (fun h : Fin n => decide (h = i)))).getD v false =
      rval ((rl gs : List (Rep n)).getD v (rzero n)) i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ v
    simp only [wl, rl, List.foldl_nil]
    by_cases hv : v < n
    · have h1 : v < (List.ofFn (fun h : Fin n => decide (h = i))).length := by simpa using hv
      have h2 : v < (rinit n).length := by simpa [rinit] using hv
      rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
      simp only [rinit, List.getElem_ofFn, rval, Pi.single_apply]
      by_cases h : (⟨v, hv⟩ : Fin n) = i
      · simp [h]
      · have h' : i ≠ ⟨v, hv⟩ := fun e => h e.symm
        simp [h, h']
    · have h1 : (List.ofFn (fun h : Fin n => decide (h = i))).length ≤ v := by simp; omega
      have h2 : (rinit n).length ≤ v := by simp [rinit]; omega
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
      simp [rzero, rval]
  | append_singleton gs g ih =>
    intro hg v
    have hg' : ∀ g' ∈ gs, Affine2 g' := fun g' h' => hg g' (List.mem_append_left _ h')
    have hgg : Affine2 g := hg g (by simp)
    have hwlen : (wl gs (List.ofFn (fun h : Fin n => decide (h = i)))).length = n + gs.length := by
      rw [wl_length]; simp
    have hrlen : (rl gs : List (Rep n)).length = n + gs.length := rl_length gs
    rw [wl_snoc, rl_snoc]
    rcases lt_trichotomy v (n + gs.length) with h | h | h
    · have h1 : v < (wl gs (List.ofFn (fun h : Fin n => decide (h = i)))).length := by omega
      have h2 : v < (rl gs : List (Rep n)).length := by omega
      rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h2]
      exact ih hg' v
    · subst h
      have h1 : (wl gs (List.ofFn (fun h : Fin n => decide (h = i)))).length ≤ n + gs.length := by
        omega
      have h2 : (rl gs : List (Rep n)).length ≤ n + gs.length := by omega
      rw [List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
      rw [hwlen, hrlen, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [rval_grep g.op g.inputs (rl gs) i hgg.1 hgg.2]
      congr 1
      apply List.map_congr_left
      intro u _
      exact ih hg' u
    · have h1 : (wl gs (List.ofFn (fun h : Fin n => decide (h = i))) ++
          [g.op.eval (g.inputs.map fun u =>
            (wl gs (List.ofFn (fun h : Fin n => decide (h = i)))).getD u false)]).length ≤ v := by
        simp only [List.length_append, List.length_singleton]; omega
      have h2 : ((rl gs : List (Rep n)) ++ [grep g.op g.inputs (rl gs)]).length ≤ v := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
      simp [rzero, rval]

-- Part B. The transposed pass: masks over Fin k pushed back from the outputs to the inputs,
-- with a block partition of Fin k (the desk's partition argument).

abbrev Mask (k : ℕ) := Fin k → ZMod 2

def unitM {k : ℕ} (j : Fin k) : Mask k := Pi.single j 1

def bsum {k : ℕ} (blk : Fin k → Fin k) (m : Mask k) (β : Fin k) : ZMod 2 :=
  ∑ a, if blk a = β then m a else 0

-- a mask meets at most one block oddly
def OneOdd {k : ℕ} (blk : Fin k → Fin k) (m : Mask k) : Prop :=
  ∀ β γ, bsum blk m β = 1 → bsum blk m γ = 1 → β = γ

def par {k : ℕ} (m : Mask k) : ZMod 2 := ∑ a, m a

def relab {k : ℕ} (blk : Fin k → Fin k) (β γ : Fin k) : Fin k → Fin k :=
  fun a => if blk a = γ then β else blk a

lemma z2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

lemma z2add : ∀ x y : ZMod 2, x + y = 1 → x = 1 ∨ y = 1 := by decide

lemma bsum_add {k : ℕ} (blk : Fin k → Fin k) (x y : Mask k) (β : Fin k) :
    bsum blk (x + y) β = bsum blk x β + bsum blk y β := by
  unfold bsum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma bsum_unit {k : ℕ} (blk : Fin k → Fin k) (j β : Fin k) :
    bsum blk (unitM j) β = if blk j = β then 1 else 0 := by
  unfold bsum unitM
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma good_zero {k : ℕ} (blk : Fin k → Fin k) : OneOdd blk 0 := by
  intro β γ h _
  simp [bsum] at h

lemma good_unit {k : ℕ} (blk : Fin k → Fin k) (j : Fin k) : OneOdd blk (unitM j) := by
  intro β γ hβ hγ
  rw [bsum_unit] at hβ hγ
  by_cases h1 : blk j = β
  · by_cases h2 : blk j = γ
    · exact h1.symm.trans h2
    · rw [if_neg h2] at hγ
      exact absurd hγ zero_ne_one
  · rw [if_neg h1] at hβ
    exact absurd hβ zero_ne_one

lemma par_eq {k : ℕ} (blk : Fin k → Fin k) (m : Mask k) : par m = ∑ β, bsum blk m β := by
  unfold par bsum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_ite_eq]
  simp

lemma par_add {k : ℕ} (x y : Mask k) : par (x + y) = par x + par y := by
  unfold par
  rw [← Finset.sum_add_distrib]
  rfl

lemma par_unit {k : ℕ} (j : Fin k) : par (unitM j) = 1 := by
  unfold par unitM
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ j) h

lemma bsum_relab_left {k : ℕ} (blk : Fin k → Fin k) (m : Mask k) {β γ : Fin k} (hne : β ≠ γ) :
    bsum (relab blk β γ) m β = bsum blk m β + bsum blk m γ := by
  unfold bsum relab
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : blk a = γ
  · have h' : blk a ≠ β := by rw [h]; exact fun e => hne e.symm
    simp [h, h', hne.symm]
  · simp [h]

lemma bsum_relab_right {k : ℕ} (blk : Fin k → Fin k) (m : Mask k) {β γ : Fin k} (hne : β ≠ γ) :
    bsum (relab blk β γ) m γ = 0 := by
  unfold bsum relab
  apply Finset.sum_eq_zero
  intro a _
  by_cases h : blk a = γ
  · simp [h, hne]
  · simp [h]

lemma bsum_relab_other {k : ℕ} (blk : Fin k → Fin k) (m : Mask k) {β γ δ : Fin k}
    (hδβ : δ ≠ β) (hδγ : δ ≠ γ) : bsum (relab blk β γ) m δ = bsum blk m δ := by
  unfold bsum relab
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : blk a = γ
  · simp [h, Ne.symm hδβ, Ne.symm hδγ]
  · simp [h]

lemma relab_odd {k : ℕ} (blk : Fin k → Fin k) (x : Mask k) {β γ : Fin k} (hne : β ≠ γ) (δ : Fin k)
    (h : bsum (relab blk β γ) x δ = 1) : ∃ ε, bsum blk x ε = 1 ∧ (if ε = γ then β else ε) = δ := by
  by_cases hδγ : δ = γ
  · rw [hδγ, bsum_relab_right blk x hne] at h
    exact absurd h zero_ne_one
  · by_cases hδβ : δ = β
    · rw [hδβ, bsum_relab_left blk x hne] at h
      rw [hδβ]
      rcases z2add _ _ h with h' | h'
      · exact ⟨β, h', by simp⟩
      · exact ⟨γ, h', by simp⟩
    · rw [bsum_relab_other blk x hδβ hδγ] at h
      exact ⟨δ, h, by simp [hδγ]⟩

lemma good_relab {k : ℕ} (blk : Fin k → Fin k) (x : Mask k) {β γ : Fin k} (hne : β ≠ γ)
    (hx : OneOdd blk x) : OneOdd (relab blk β γ) x := by
  intro δ1 δ2 h1 h2
  obtain ⟨ε1, e1, f1⟩ := relab_odd blk x hne δ1 h1
  obtain ⟨ε2, e2, f2⟩ := relab_odd blk x hne δ2 h2
  have h := hx _ _ e1 e2
  subst h
  exact f1.symm.trans f2

lemma no_three {k : ℕ} (blk : Fin k → Fin k) (x y : Mask k) (hx : OneOdd blk x) (hy : OneOdd blk y)
    (β γ δ : Fin k) (h1 : bsum blk (x + y) β = 1) (h2 : bsum blk (x + y) γ = 1)
    (h3 : bsum blk (x + y) δ = 1) (hβγ : β ≠ γ) (hβδ : β ≠ δ) (hγδ : γ ≠ δ) : False := by
  rw [bsum_add] at h1 h2 h3
  rcases z2add _ _ h1 with a1 | a1 <;> rcases z2add _ _ h2 with a2 | a2 <;>
    rcases z2add _ _ h3 with a3 | a3
  all_goals first
    | exact hβγ (hx _ _ a1 a2)
    | exact hβγ (hy _ _ a1 a2)
    | exact hβδ (hx _ _ a1 a3)
    | exact hβδ (hy _ _ a1 a3)
    | exact hγδ (hx _ _ a2 a3)
    | exact hγδ (hy _ _ a2 a3)

lemma good_merge {k : ℕ} (blk : Fin k → Fin k) (x y : Mask k) (hx : OneOdd blk x) (hy : OneOdd blk y)
    {β γ : Fin k} (hne : β ≠ γ) (hβ : bsum blk (x + y) β = 1) (hγ : bsum blk (x + y) γ = 1) :
    OneOdd (relab blk β γ) (x + y) := by
  intro δ1 δ2 h1 _
  exfalso
  by_cases hδγ : δ1 = γ
  · rw [hδγ, bsum_relab_right blk _ hne] at h1
    exact zero_ne_one h1
  · by_cases hδβ : δ1 = β
    · rw [hδβ, bsum_relab_left blk _ hne, hβ, hγ] at h1
      exact absurd h1 (by decide)
    · rw [bsum_relab_other blk _ hδβ hδγ] at h1
      exact no_three blk x y hx hy β γ δ1 hβ hγ h1 hne (Ne.symm hδβ) (Ne.symm hδγ)

lemma par_merge {k : ℕ} (blk : Fin k → Fin k) (x y : Mask k) (hx : OneOdd blk x) (hy : OneOdd blk y)
    {β γ : Fin k} (hne : β ≠ γ) (hβ : bsum blk (x + y) β = 1) (hγ : bsum blk (x + y) γ = 1) :
    par (x + y) = 0 := by
  rw [par_eq blk, Fintype.sum_eq_add β γ hne]
  · rw [hβ, hγ]
    decide
  · intro δ hδ
    rcases z2 (bsum blk (x + y) δ) with h | h
    · exact h
    · exact (no_three blk x y hx hy β γ δ hβ hγ h hne (Ne.symm hδ.1) (Ne.symm hδ.2)).elim

lemma card_relab {k : ℕ} (blk : Fin k → Fin k) (β γ : Fin k) :
    (Finset.univ.image blk).card ≤ (Finset.univ.image (relab blk β γ)).card + 1 := by
  have hsub : Finset.univ.image blk ⊆ insert γ (Finset.univ.image (relab blk β γ)) := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases h : blk a = γ
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simp [relab, h]⟩
  calc (Finset.univ.image blk).card ≤ (insert γ (Finset.univ.image (relab blk β γ))).card :=
        Finset.card_le_card hsub
    _ ≤ _ := Finset.card_insert_le _ _

-- the potentials
def zc {k : ℕ} (L : ℕ) (p : ℕ → Mask k) : ℕ := ((Finset.range L).filter (fun v => p v ≠ 0)).card

def f1 {k : ℕ} (A : Finset (Mask k)) : Finset (Mask k) := A.filter (fun m => par m = 0 ∧ m ≠ 0)

def f2 {k : ℕ} (A : Finset (Mask k)) : Finset (Mask k) :=
  A.filter (fun m => par m = 1 ∧ m ∉ Finset.univ.image unitM)

def phi1 {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (A : Finset (Mask k)) : ℕ := zc L p + (f1 A).card

def phi2 {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (A : Finset (Mask k)) (mg : ℕ) : ℕ :=
  zc L p + (f2 A).card + mg

def SInv {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (blk : Fin k → Fin k) (A : Finset (Mask k)) (mg : ℕ) :
    Prop :=
  (∀ v < L, OneOdd blk (p v)) ∧ (∀ v < L, p v = 0 ∨ p v ∈ A) ∧ (∀ j, unitM j ∈ A) ∧
    k ≤ (Finset.univ.image blk).card + mg

lemma f1_insert {k : ℕ} (r : Mask k) (A : Finset (Mask k)) :
    (f1 (insert r A)).card ≤ (f1 A).card + 1 := by
  unfold f1
  rw [Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

lemma f2_insert {k : ℕ} (r : Mask k) (A : Finset (Mask k)) :
    (f2 (insert r A)).card ≤ (f2 A).card + 1 := by
  unfold f2
  rw [Finset.filter_insert]
  split_ifs
  · exact Finset.card_insert_le _ _
  · omega

lemma f2_insert_even {k : ℕ} (r : Mask k) (A : Finset (Mask k)) (h : par r = 0) :
    (f2 (insert r A)).card = (f2 A).card := by
  unfold f2
  rw [Finset.filter_insert, if_neg]
  rw [h]
  intro h'
  exact zero_ne_one h'.1

lemma zc_update_le {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (u : ℕ) (x : Mask k) :
    zc L (Function.update p u x) ≤ zc L p + 1 := by
  unfold zc
  calc ((Finset.range L).filter (fun v => Function.update p u x v ≠ 0)).card
      ≤ (insert u ((Finset.range L).filter (fun v => p v ≠ 0))).card := by
        apply Finset.card_le_card
        intro v hv
        simp only [Finset.mem_filter, Finset.mem_range] at hv
        by_cases h : v = u
        · rw [h]
          exact Finset.mem_insert_self _ _
        · apply Finset.mem_insert_of_mem
          simp only [Finset.mem_filter, Finset.mem_range]
          rw [Function.update_of_ne h] at hv
          exact hv
    _ ≤ _ := Finset.card_insert_le _ _

lemma zc_update_le' {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (u : ℕ) (x : Mask k) (hu : p u ≠ 0) :
    zc L (Function.update p u x) ≤ zc L p := by
  unfold zc
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_range] at hv ⊢
  by_cases h : v = u
  · subst h
    exact ⟨hv.1, hu⟩
  · rw [Function.update_of_ne h] at hv
    exact hv

lemma zc_update_out {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (u : ℕ) (x : Mask k) (hu : L ≤ u) :
    zc L (Function.update p u x) = zc L p := by
  unfold zc
  congr 1
  apply Finset.filter_congr
  intro v hv
  rw [Finset.mem_range] at hv
  have hvu : v ≠ u := by omega
  rw [Function.update_of_ne hvu]

lemma zc_succ {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (h : p L ≠ 0) : zc (L + 1) p = zc L p + 1 := by
  unfold zc
  rw [Finset.range_add_one, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem]
  simp

lemma zc_le_succ {k : ℕ} (L : ℕ) (p : ℕ → Mask k) : zc L p ≤ zc (L + 1) p := by
  unfold zc
  apply Finset.card_le_card
  intro v
  simp only [Finset.mem_filter, Finset.mem_range]
  intro h
  exact ⟨by omega, h.2⟩

-- one event of the transposed circuit: the mask m is added at node u
lemma event {k : ℕ} (L : ℕ) (p : ℕ → Mask k) (blk : Fin k → Fin k) (A : Finset (Mask k)) (mg : ℕ)
    (h : SInv L p blk A mg) (m : Mask k) (hm : OneOdd blk m) (hmA : m = 0 ∨ m ∈ A) (u : ℕ) :
    ∃ blk' A' mg', SInv L (Function.update p u (p u + m)) blk' A' mg' ∧
      (∀ x, OneOdd blk x → OneOdd blk' x) ∧ A ⊆ A' ∧
      phi1 L (Function.update p u (p u + m)) A' ≤ phi1 L p A + 1 ∧
      phi2 L (Function.update p u (p u + m)) A' mg' ≤ phi2 L p A mg + 1 := by
  obtain ⟨hG, hA, hU, hK⟩ := h
  by_cases hu : u < L
  · by_cases h0 : p u = 0
    · have hz := zc_update_le L p u (p u + m)
      refine ⟨blk, A, mg, ⟨?_, ?_, hU, hK⟩, fun x hx => hx, Finset.Subset.refl _, ?_, ?_⟩
      · intro v hv
        by_cases hvu : v = u
        · rw [hvu, Function.update_self, h0, zero_add]
          exact hm
        · rw [Function.update_of_ne hvu]
          exact hG v hv
      · intro v hv
        by_cases hvu : v = u
        · rw [hvu, Function.update_self, h0, zero_add]
          exact hmA
        · rw [Function.update_of_ne hvu]
          exact hA v hv
      · unfold phi1
        omega
      · unfold phi2
        omega
    · have hz := zc_update_le' L p u (p u + m) h0
      have hGu := hG u hu
      have hAm : ∀ v < L, Function.update p u (p u + m) v = 0 ∨
          Function.update p u (p u + m) v ∈ insert (p u + m) A := by
        intro v hv
        by_cases hvu : v = u
        · rw [hvu, Function.update_self]
          exact Or.inr (Finset.mem_insert_self _ _)
        · rw [Function.update_of_ne hvu]
          rcases hA v hv with h' | h'
          · exact Or.inl h'
          · exact Or.inr (Finset.mem_insert_of_mem h')
      have hUm : ∀ j, unitM j ∈ insert (p u + m) A := fun j => Finset.mem_insert_of_mem (hU j)
      have q1 := f1_insert (p u + m) A
      by_cases hr : OneOdd blk (p u + m)
      · have q2 := f2_insert (p u + m) A
        refine ⟨blk, insert (p u + m) A, mg, ⟨?_, hAm, hUm, hK⟩, fun x hx => hx,
          Finset.subset_insert _ _, ?_, ?_⟩
        · intro v hv
          by_cases hvu : v = u
          · rw [hvu, Function.update_self]
            exact hr
          · rw [Function.update_of_ne hvu]
            exact hG v hv
        · unfold phi1
          omega
        · unfold phi2
          omega
      · unfold OneOdd at hr
        push_neg at hr
        obtain ⟨β, γ, hβ, hγ, hne⟩ := hr
        have hpar := par_merge blk (p u) m hGu hm hne hβ hγ
        have q2 := f2_insert_even (p u + m) A hpar
        have hc := card_relab blk β γ
        refine ⟨relab blk β γ, insert (p u + m) A, mg + 1, ⟨?_, hAm, hUm, ?_⟩,
          fun x hx => good_relab blk x hne hx, Finset.subset_insert _ _, ?_, ?_⟩
        · intro v hv
          by_cases hvu : v = u
          · rw [hvu, Function.update_self]
            exact good_merge blk (p u) m hGu hm hne hβ hγ
          · rw [Function.update_of_ne hvu]
            exact good_relab blk _ hne (hG v hv)
        · omega
        · unfold phi1
          omega
        · unfold phi2
          omega
  · have hz := zc_update_out L p u (p u + m) (by omega)
    refine ⟨blk, A, mg, ⟨?_, ?_, hU, hK⟩, fun x hx => hx, Finset.Subset.refl _, ?_, ?_⟩
    · intro v hv
      rw [Function.update_of_ne (show v ≠ u by omega)]
      exact hG v hv
    · intro v hv
      rw [Function.update_of_ne (show v ≠ u by omega)]
      exact hA v hv
    · unfold phi1
      omega
    · unfold phi2
      omega

def upd {k : ℕ} (l : List (ℕ × Mask k)) (p : ℕ → Mask k) : ℕ → Mask k :=
  l.foldl (fun q e => Function.update q e.1 (q e.1 + e.2)) p

lemma events {k : ℕ} (L : ℕ) (l : List (ℕ × Mask k)) :
    ∀ (p : ℕ → Mask k) (blk : Fin k → Fin k) (A : Finset (Mask k)) (mg : ℕ), SInv L p blk A mg →
    (∀ e ∈ l, OneOdd blk e.2 ∧ (e.2 = 0 ∨ e.2 ∈ A)) →
    ∃ blk' A' mg', SInv L (upd l p) blk' A' mg' ∧
      phi1 L (upd l p) A' ≤ phi1 L p A + l.length ∧
      phi2 L (upd l p) A' mg' ≤ phi2 L p A mg + l.length := by
  induction l with
  | nil =>
    intro p blk A mg h _
    exact ⟨blk, A, mg, h, by simp [upd], by simp [upd]⟩
  | cons e l ih =>
    intro p blk A mg h hl
    obtain ⟨hg, hmA⟩ := hl e (by simp)
    obtain ⟨blk1, A1, mg1, h1, hgood, hsub, q1, q2⟩ := event L p blk A mg h e.2 hg hmA e.1
    have hl' : ∀ e' ∈ l, OneOdd blk1 e'.2 ∧ (e'.2 = 0 ∨ e'.2 ∈ A1) := by
      intro e' he'
      obtain ⟨g', a'⟩ := hl e' (List.mem_cons_of_mem _ he')
      exact ⟨hgood _ g', a'.imp id (fun h => hsub h)⟩
    obtain ⟨blk2, A2, mg2, h2, r1, r2⟩ := ih _ blk1 A1 mg1 h1 hl'
    have eq : upd (e :: l) p = upd l (Function.update p e.1 (p e.1 + e.2)) := rfl
    refine ⟨blk2, A2, mg2, ?_, ?_, ?_⟩
    · rw [eq]
      exact h2
    · rw [eq, List.length_cons]
      omega
    · rw [eq, List.length_cons]
      omega

lemma bil_update {k n : ℕ} (L : ℕ) (a : ℕ → Fin n → ZMod 2) (ha : ∀ u, L ≤ u → a u = 0)
    (i : Fin n) (j : Fin k) (p : ℕ → Mask k) (u : ℕ) (m : Mask k) :
    ∑ v ∈ Finset.range L, (Function.update p u (p u + m)) v j * a v i =
      ∑ v ∈ Finset.range L, p v j * a v i + m j * a u i := by
  have e : ∀ v, (Function.update p u (p u + m)) v j * a v i =
      p v j * a v i + (if v = u then m j * a u i else 0) := by
    intro v
    by_cases hv : v = u
    · subst hv
      simp [add_mul]
    · simp [Function.update_of_ne hv, hv]
  rw [Finset.sum_congr rfl (fun v _ => e v), Finset.sum_add_distrib, Finset.sum_ite_eq']
  by_cases hu : u < L
  · simp [hu]
  · simp [hu, ha u (by omega)]

lemma bil_fold {k n : ℕ} (L : ℕ) (a : ℕ → Fin n → ZMod 2) (ha : ∀ u, L ≤ u → a u = 0)
    (i : Fin n) (j : Fin k) (l : List (ℕ × Mask k)) : ∀ (p : ℕ → Mask k),
    ∑ v ∈ Finset.range L, (upd l p) v j * a v i =
      ∑ v ∈ Finset.range L, p v j * a v i + (l.map (fun e => e.2 j * a e.1 i)).sum := by
  induction l with
  | nil => intro p; simp [upd]
  | cons e l ih =>
    intro p
    have eq : upd (e :: l) p = upd l (Function.update p e.1 (p e.1 + e.2)) := rfl
    rw [eq, ih, bil_update L a ha i j p e.1 e.2, List.map_cons, List.sum_cons]
    ring

-- the nodes a gate pushes its mask to: its live linear inputs
def gnodes (op : GateOp) : List ℕ → List ℕ
  | [] => []
  | [u] => if xor (op.eval [true]) (op.eval [false]) then [u] else []
  | [u, w] => (if xor (op.eval [true, false]) (op.eval [false, false]) then [u] else []) ++
      (if xor (op.eval [false, true]) (op.eval [false, false]) then [w] else [])
  | _ :: _ :: _ :: _ => []

lemma gnodes_len (g : Gate) :
    (gnodes g.op g.inputs).length ≤ 1 + [g].countP (fun g => decide (g.inputs.length = 2)) := by
  obtain ⟨op, ins⟩ := g
  match ins with
  | [] => simp [gnodes]
  | [u] =>
    simp only [gnodes]
    split_ifs <;> simp
  | [u, w] =>
    simp only [gnodes]
    split_ifs <;> simp
  | _ :: _ :: _ :: _ => simp [gnodes]

lemma gnodes_sum {k n : ℕ} (op : GateOp) (ins : List ℕ) (L : List (Rep n)) (m : Mask k)
    (i : Fin n) (j : Fin k) :
    (((gnodes op ins).map (fun u => (u, m))).map
      (fun e => e.2 j * (L.getD e.1 (rzero n)).2 i)).sum = m j * (grep op ins L).2 i := by
  match ins with
  | [] => simp [gnodes, grep]
  | [u] =>
    simp only [gnodes, grep]
    split_ifs <;> simp
  | [u, w] =>
    simp only [gnodes, grep]
    split_ifs <;> simp [mul_add]
  | _ :: _ :: _ :: _ => simp [gnodes, grep, rzero]

lemma rl_getD_lt {n : ℕ} (gs : List Gate) (g : Gate) (v : ℕ) (hv : v < n + gs.length) :
    (rl (gs ++ [g]) : List (Rep n)).getD v (rzero n) = (rl gs : List (Rep n)).getD v (rzero n) := by
  rw [rl_snoc]
  exact List.getD_append _ _ _ _ (by rw [rl_length]; exact hv)

lemma rl_getD_top {n : ℕ} (gs : List Gate) (g : Gate) :
    (rl (gs ++ [g]) : List (Rep n)).getD (n + gs.length) (rzero n) = grep g.op g.inputs (rl gs) := by
  have h1 : (rl gs : List (Rep n)).length ≤ n + gs.length := by rw [rl_length]
  rw [rl_snoc, List.getD_append_right _ _ _ _ h1]
  have h2 : n + gs.length - (rl gs : List (Rep n)).length = 0 := by rw [rl_length]; omega
  simp only [h2, List.getD_cons_zero]

lemma rl_getD_out {n : ℕ} (gs : List Gate) (u : ℕ) (hu : n + gs.length ≤ u) :
    ((rl gs : List (Rep n)).getD u (rzero n)).2 = 0 := by
  rw [List.getD_eq_default _ _ (by rw [rl_length]; exact hu)]
  rfl

lemma gate_step {k n : ℕ} (col : Fin n → Mask k) (gs : List Gate) (g : Gate)
    (p : ℕ → Mask k) (blk : Fin k → Fin k) (A : Finset (Mask k)) (mg : ℕ)
    (hS : SInv (n + gs.length + 1) p blk A mg)
    (hB : ∀ i j, ∑ v ∈ Finset.range (n + gs.length + 1),
      p v j * ((rl (gs ++ [g]) : List (Rep n)).getD v (rzero n)).2 i = col i j) :
    ∃ p' blk' A' mg', SInv (n + gs.length) p' blk' A' mg' ∧
      (∀ i j, ∑ v ∈ Finset.range (n + gs.length),
        p' v j * ((rl gs : List (Rep n)).getD v (rzero n)).2 i = col i j) ∧
      phi1 (n + gs.length) p' A' ≤ phi1 (n + gs.length + 1) p A +
        [g].countP (fun g => decide (g.inputs.length = 2)) ∧
      phi2 (n + gs.length) p' A' mg' ≤ phi2 (n + gs.length + 1) p A mg +
        [g].countP (fun g => decide (g.inputs.length = 2)) := by
  obtain ⟨hG, hA, hU, hK⟩ := hS
  have hS' : SInv (n + gs.length) p blk A mg :=
    ⟨fun v hv => hG v (by omega), fun v hv => hA v (by omega), hU, hK⟩
  have hsplit : ∀ i j, ∑ v ∈ Finset.range (n + gs.length + 1),
      p v j * ((rl (gs ++ [g]) : List (Rep n)).getD v (rzero n)).2 i =
      ∑ v ∈ Finset.range (n + gs.length), p v j * ((rl gs : List (Rep n)).getD v (rzero n)).2 i +
        p (n + gs.length) j * (grep g.op g.inputs (rl gs)).2 i := by
    intro i j
    rw [Finset.sum_range_succ, rl_getD_top]
    congr 1
    apply Finset.sum_congr rfl
    intro v hv
    rw [rl_getD_lt gs g v (Finset.mem_range.mp hv)]
  have hzc := zc_le_succ (n + gs.length) p
  by_cases hm : p (n + gs.length) = 0
  · refine ⟨p, blk, A, mg, hS', ?_, ?_, ?_⟩
    · intro i j
      rw [← hB i j, hsplit, hm]
      simp
    · unfold phi1
      omega
    · unfold phi2
      omega
  · have hmG : OneOdd blk (p (n + gs.length)) := hG _ (by omega)
    have hmA : p (n + gs.length) ∈ A := (hA _ (by omega)).resolve_left hm
    have hE : ∀ e ∈ (gnodes g.op g.inputs).map (fun u => (u, p (n + gs.length))),
        OneOdd blk e.2 ∧ (e.2 = 0 ∨ e.2 ∈ A) := by
      intro e he
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp he
      exact ⟨hmG, Or.inr hmA⟩
    obtain ⟨blk', A', mg', h1, q1, q2⟩ := events (n + gs.length)
      ((gnodes g.op g.inputs).map (fun u => (u, p (n + gs.length)))) p blk A mg hS' hE
    have hlen := gnodes_len g
    have hz := zc_succ (n + gs.length) p hm
    rw [List.length_map] at q1 q2
    refine ⟨_, blk', A', mg', h1, ?_, ?_, ?_⟩
    · intro i j
      rw [bil_fold (n + gs.length) _ (rl_getD_out gs) i j, ← hB i j, hsplit, gnodes_sum]
    · unfold phi1 at q1 ⊢
      omega
    · unfold phi2 at q2 ⊢
      omega

lemma descent {k n : ℕ} (col : Fin n → Mask k) (gs : List Gate) :
    ∀ (p : ℕ → Mask k) (blk : Fin k → Fin k) (A : Finset (Mask k)) (mg : ℕ),
    SInv (n + gs.length) p blk A mg →
    (∀ i j, ∑ v ∈ Finset.range (n + gs.length),
      p v j * ((rl gs : List (Rep n)).getD v (rzero n)).2 i = col i j) →
    ∃ p' blk' A' mg', SInv n p' blk' A' mg' ∧
      (∀ i j, ∑ v ∈ Finset.range n,
        p' v j * ((rl [] : List (Rep n)).getD v (rzero n)).2 i = col i j) ∧
      phi1 n p' A' ≤ phi1 (n + gs.length) p A + gs.countP (fun g => decide (g.inputs.length = 2)) ∧
      phi2 n p' A' mg' ≤ phi2 (n + gs.length) p A mg +
        gs.countP (fun g => decide (g.inputs.length = 2)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro p blk A mg hS hB
    exact ⟨p, blk, A, mg, by simpa using hS, by simpa using hB, by simp, by simp⟩
  | append_singleton gs g ih =>
    intro p blk A mg hS hB
    have e : n + (gs ++ [g]).length = n + gs.length + 1 := by simp; omega
    rw [e] at hS hB
    obtain ⟨p1, blk1, A1, mg1, h1, b1, r1, s1⟩ := gate_step col gs g p blk A mg hS hB
    obtain ⟨p2, blk2, A2, mg2, h2, b2, r2, s2⟩ := ih p1 blk1 A1 mg1 h1 b1
    refine ⟨p2, blk2, A2, mg2, h2, b2, ?_, ?_⟩
    · rw [e, List.countP_append]
      omega
    · rw [e, List.countP_append]
      omega

lemma bil_base {k n : ℕ} (p : ℕ → Mask k) (col : Fin n → Mask k)
    (h : ∀ i j, ∑ v ∈ Finset.range n,
      p v j * ((rl [] : List (Rep n)).getD v (rzero n)).2 i = col i j) (i : Fin n) :
    p i = col i := by
  funext j
  rw [← h i j, Finset.sum_eq_single (i : ℕ)]
  · have h1 : (i : ℕ) < (rinit n).length := by simp [rinit]
    simp only [rl, List.foldl_nil]
    rw [List.getD_eq_getElem _ _ h1]
    simp [rinit]
  · intro v hv hvi
    have hv' : v < n := Finset.mem_range.mp hv
    have h1 : v < (rinit n).length := by simp [rinit]; exact hv'
    simp only [rl, List.foldl_nil]
    rw [List.getD_eq_getElem _ _ h1]
    simp only [rinit, List.getElem_ofFn]
    have hne : i ≠ ⟨v, hv'⟩ := fun e => hvi (by rw [e])
    simp [Pi.single_apply, hne]
  · intro hi
    exact absurd (Finset.mem_range.mpr i.isLt) hi

lemma blocks_le_two {k n : ℕ} (col : Fin n → Mask k)
    (hfam : ∀ m : Mask k, (∃ i, col i = m) ↔ par m = 1)
    (blk : Fin k → Fin k) (hG : ∀ i, OneOdd blk (col i)) : (Finset.univ.image blk).card ≤ 2 := by
  by_contra hc
  push_neg at hc
  obtain ⟨β1, h1, β2, h2, β3, h3, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
  obtain ⟨a1, _, e1⟩ := Finset.mem_image.mp h1
  obtain ⟨a2, _, e2⟩ := Finset.mem_image.mp h2
  obtain ⟨a3, _, e3⟩ := Finset.mem_image.mp h3
  have hpar : par (unitM a1 + unitM a2 + unitM a3) = 1 := by
    rw [par_add, par_add, par_unit, par_unit, par_unit]
    decide
  obtain ⟨i, hi⟩ := (hfam _).mpr hpar
  have g := hG i
  rw [hi] at g
  have n21 : ¬ blk a2 = β1 := by rw [e2]; exact Ne.symm h12
  have n31 : ¬ blk a3 = β1 := by rw [e3]; exact Ne.symm h13
  have n12 : ¬ blk a1 = β2 := by rw [e1]; exact h12
  have n32 : ¬ blk a3 = β2 := by rw [e3]; exact Ne.symm h23
  have b1 : bsum blk (unitM a1 + unitM a2 + unitM a3) β1 = 1 := by
    rw [bsum_add, bsum_add, bsum_unit, bsum_unit, bsum_unit, if_pos e1, if_neg n21, if_neg n31]
    decide
  have b2 : bsum blk (unitM a1 + unitM a2 + unitM a3) β2 = 1 := by
    rw [bsum_add, bsum_add, bsum_unit, bsum_unit, bsum_unit, if_neg n12, if_pos e2, if_neg n32]
    decide
  exact h12 (g _ _ b1 b2)

lemma lower_core {k n : ℕ} (col : Fin n → Mask k) (hinj : Function.Injective col) (b : ZMod 2)
    (hfam : ∀ m : Mask k, (∃ i, col i = m) ↔ par m = b)
    (p : ℕ → Mask k) (blk : Fin k → Fin k) (A : Finset (Mask k)) (mg : ℕ)
    (hS : SInv n p blk A mg) (hp : ∀ i : Fin n, p i = col i) (c : ℕ)
    (h1 : phi1 n p A ≤ k + c) (h2 : phi2 n p A mg ≤ k + c) : 2 * n ≤ c + k + 2 := by
  obtain ⟨hG, hA, hU, hK⟩ := hS
  have hzc : (Finset.univ.filter (fun i : Fin n => ¬ col i = 0)).card ≤ zc n p := by
    unfold zc
    calc (Finset.univ.filter (fun i : Fin n => ¬ col i = 0)).card
        = ((Finset.univ.filter (fun i : Fin n => ¬ col i = 0)).map Fin.valEmbedding).card :=
          (Finset.card_map _).symm
      _ ≤ _ := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
            Fin.valEmbedding_apply] at hv
          obtain ⟨i, hi, rfl⟩ := hv
          simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨i.isLt, by rw [hp i]; exact hi⟩
  have hcolA : ∀ i, ¬ col i = 0 → col i ∈ A := by
    intro i hi
    rcases hA i i.isLt with h | h
    · rw [hp i] at h
      exact absurd h hi
    · rw [hp i] at h
      exact h
  have hparc : ∀ i, par (col i) = b := fun i => (hfam (col i)).mp ⟨i, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i : Fin n => col i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  rcases z2 b with hb | hb
  · -- even masks: every nonzero column is a new even mask
    have hT1 : (Finset.univ.filter (fun i : Fin n => col i = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hinj (hx.trans hy.symm)
    have hf1 : (Finset.univ.filter (fun i : Fin n => ¬ col i = 0)).card ≤ (f1 A).card := by
      rw [← Finset.card_image_of_injective _ hinj]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      unfold f1
      simp only [Finset.mem_filter]
      exact ⟨hcolA i hi, by rw [hparc i, hb], hi⟩
    unfold phi1 at h1
    omega
  · -- odd masks: nonunit odd columns, plus at least k - 2 merges
    have hall : (Finset.univ.filter (fun i : Fin n => ¬ col i = 0)).card = n := by
      rw [Finset.filter_true_of_mem]
      · simp
      · intro i _ h
        have := hparc i
        rw [h, hb] at this
        simp [par] at this
    have hS1 : (Finset.univ.filter (fun i : Fin n => col i ∈ Finset.univ.image unitM)).card ≤ k := by
      rw [← Finset.card_image_of_injective _ hinj]
      calc _ ≤ (Finset.univ.image (unitM : Fin k → Mask k)).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
            exact hi
        _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    have hsplit2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun i : Fin n => col i ∈ Finset.univ.image unitM)
    rw [Finset.card_univ, Fintype.card_fin] at hsplit2
    have hf2 : (Finset.univ.filter (fun i : Fin n => ¬ col i ∈ Finset.univ.image unitM)).card ≤
        (f2 A).card := by
      rw [← Finset.card_image_of_injective _ hinj]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have hne : ¬ col i = 0 := by
        intro h
        have := hparc i
        rw [h, hb] at this
        simp [par] at this
      unfold f2
      simp only [Finset.mem_filter]
      exact ⟨hcolA i hne, by rw [hparc i, hb], hi⟩
    have hb2 := blocks_le_two col (fun m => by rw [hfam m, hb]) blk
      (fun i => by rw [← hp i]; exact hG i i.isLt)
    unfold phi2 at h2
    omega

theorem lower_abstract {k n : ℕ} (gs : List Gate) (col : Fin n → Mask k)
    (hinj : Function.Injective col) (b : ZMod 2) (hfam : ∀ m : Mask k, (∃ i, col i = m) ↔ par m = b)
    (w : Fin k → ℕ) (hw : ∀ i j, ((rl gs : List (Rep n)).getD (w j) (rzero n)).2 i = col i j) :
    2 * n ≤ gs.countP (fun g => decide (g.inputs.length = 2)) + k + 2 := by
  have hS0 : SInv (n + gs.length) (fun _ => (0 : Mask k)) id (Finset.univ.image unitM) 0 := by
    refine ⟨fun v _ => good_zero id, fun v _ => Or.inl rfl,
      fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j), ?_⟩
    rw [Finset.image_id]
    simp
  have hE0 : ∀ e ∈ (List.finRange k).map (fun j => (w j, (unitM j : Mask k))),
      OneOdd id e.2 ∧ (e.2 = 0 ∨ e.2 ∈ Finset.univ.image unitM) := by
    intro e he
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    exact ⟨good_unit id j, Or.inr (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩
  obtain ⟨blk1, A1, mg1, h1, r1, s1⟩ := events (n + gs.length) _ (fun _ => (0 : Mask k)) id _ 0
    hS0 hE0
  have hf10 : (f1 (Finset.univ.image (unitM : Fin k → Mask k))).card = 0 := by
    rw [Finset.card_eq_zero]
    unfold f1
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    rw [par_unit]
    intro h
    exact one_ne_zero h.1
  have hf20 : (f2 (Finset.univ.image (unitM : Fin k → Mask k))).card = 0 := by
    rw [Finset.card_eq_zero]
    unfold f2
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx h
    exact h.2 hx
  have hz0 : zc (n + gs.length) (fun _ => (0 : Mask k)) = 0 := by
    simp [zc]
  have hB1 : ∀ i j, ∑ v ∈ Finset.range (n + gs.length),
      (upd ((List.finRange k).map (fun j => (w j, (unitM j : Mask k)))) (fun _ => 0)) v j *
        ((rl gs : List (Rep n)).getD v (rzero n)).2 i = col i j := by
    intro i j
    rw [bil_fold (n + gs.length) _ (rl_getD_out gs) i j, List.map_map]
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]
    rw [← Fin.sum_univ_def]
    rw [Finset.sum_eq_single j]
    · show unitM j j * ((rl gs : List (Rep n)).getD (w j) (rzero n)).2 i = col i j
      rw [hw]
      simp [unitM]
    · intro b _ hb
      simp [unitM, Pi.single_apply, Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  obtain ⟨p2, blk2, A2, mg2, h2, b2, r2, s2⟩ := descent col gs _ blk1 A1 mg1 h1 hB1
  have hp := bil_base p2 col b2
  rw [List.length_map, List.length_finRange] at r1 s1
  unfold phi1 at r1
  unfold phi2 at s1
  apply lower_core col hinj b hfam p2 blk2 A2 mg2 h2 hp
  · unfold phi1 at r2 ⊢
    omega
  · unfold phi2 at s2 ⊢
    omega

-- Part C. From the circuit to the masks: read each output through its constant.

def tauN {k : ℕ} (cst : Fin k → Bool) (m : Mask k) : Finset (Fin k) :=
  Finset.univ.filter (fun j => xor (cst j) (decide (m j = 1)) = true)

lemma tau_mem {k : ℕ} (cst : Fin k → Bool) (m : Mask k) (j : Fin k) :
    j ∈ tauN cst m ↔ xor (cst j) (decide (m j = 1)) = true := by
  simp [tauN]

lemma zkey1 : ∀ (c : Bool) (x y : ZMod 2),
    (xor c (decide (x = 1)) = true ↔ xor c (decide (y = 1)) = true) → x = y := by decide

lemma zkey2 : ∀ (c : Bool) (z : ZMod 2),
    (if xor c (decide (z = 1)) = true then (1 : ZMod 2) else 0) = (if c = true then 1 else 0) + z := by
  decide

lemma zkey3 : ∀ (b : Bool) (γ x : ZMod 2),
    (decide (γ + x = 1) = b) ↔ x = (if b = true then 1 else 0) + γ := by decide

lemma tau_inj {k : ℕ} (cst : Fin k → Bool) (m m' : Mask k) (h : tauN cst m = tauN cst m') :
    m = m' := by
  funext j
  have hj : j ∈ tauN cst m ↔ j ∈ tauN cst m' := by rw [h]
  rw [tau_mem, tau_mem] at hj
  exact zkey1 (cst j) (m j) (m' j) hj

lemma tau_card {k : ℕ} (cst : Fin k → Bool) (m : Mask k) :
    ((tauN cst m).card : ZMod 2) = (∑ j, if cst j = true then (1 : ZMod 2) else 0) + par m := by
  unfold tauN par
  rw [Finset.natCast_card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact zkey2 (cst j) (m j)

-- The lower bound for one circuit.
theorem lower_bound (k n : ℕ) (b : Bool) (F : Fin n → Finset (Fin k))
    (hF : Function.Injective F)
    (hfam : ∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) (s : ℕ)
    (C : Circuit)
    (hC1 : ∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
      (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
        g.op.eval [true,false] ^^ g.op.eval [true,true]) = false))
    (hC2 : C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ s)
    (hC3 : ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
      (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) :
    2 * n ≤ s + k + 2 := by
  choose w hw using hC3
  have hrep : ∀ j i, rval ((rl C.gates : List (Rep n)).getD (w j) (rzero n)) i =
      decide (j ∈ F i) := by
    intro j i
    rw [← wires_rep i C.gates hC1 (w j)]
    exact hw j i
  have htau : ∀ i, tauN (fun j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).1)
      (fun j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).2 i) = F i := by
    intro i
    ext j
    rw [tau_mem]
    have h := hrep j i
    change xor ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).1
      (decide (((rl C.gates : List (Rep n)).getD (w j) (rzero n)).2 i = 1)) = decide (j ∈ F i) at h
    rw [h]
    simp
  have hinj : Function.Injective
      (fun i j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).2 i : Fin n → Mask k) := by
    intro i i' h
    apply hF
    rw [← htau i, ← htau i']
    exact congrArg _ h
  have hfam' : ∀ m : Mask k,
      (∃ i, (fun i j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).2 i : Fin n → Mask k) i
        = m) ↔
      par m = (if b = true then 1 else 0) + ∑ j, if ((rl C.gates : List (Rep n)).getD (w j)
        (rzero n)).1 = true then (1 : ZMod 2) else 0 := by
    intro m
    have e1 : (∃ i, (fun i j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).2 i :
        Fin n → Mask k) i = m) ↔
        (∃ i, F i = tauN (fun j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).1) m) := by
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, by rw [← htau i]; exact congrArg _ hi⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, tau_inj (fun j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).1) _ _
          ((htau i).trans hi)⟩
    rw [e1, hfam]
    have e2 : Odd (tauN (fun j => ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).1) m).card ↔
        (∑ j, if ((rl C.gates : List (Rep n)).getD (w j) (rzero n)).1 = true then (1 : ZMod 2)
          else 0) + par m = 1 := by
      rw [← ZMod.natCast_eq_one_iff_odd, tau_card]
    rw [decide_eq_decide.mpr e2]
    exact zkey3 b _ _
  have := lower_abstract C.gates _ hinj _ hfam' w (fun i j => rfl)
  omega

-- The lower-bound direction of the posted statement, word for word.
theorem lower_dir : ∀ (k n : ℕ), 2 ≤ k → ∀ (b : Bool) (F : Fin n → Finset (Fin k)),
  Function.Injective F → (∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) →
  ∀ s : ℕ,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
        (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
          g.op.eval [true,false] ^^ g.op.eval [true,true]) = false)) ∧
      C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ s ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) →
    2*n ≤ s + k + 2 := by
  intro k n _ b F hF hfam s hC
  obtain ⟨C, hC1, hC2, hC3⟩ := hC
  exact lower_bound k n b F hF hfam s C hC1 hC2 hC3


-- Upper bound (the even centred family) and the glue iff_of_lower.

-- Wire values on one-hot inputs, read in ZMod 2.
def bz : Bool → ZMod 2
  | true => 1
  | false => 0

theorem bz_xor (p q : Bool) : bz (p ^^ q) = bz p + bz q := by
  cases p <;> cases q <;> decide

theorem bz_not (p : Bool) : bz (!p) = bz p + 1 := by
  cases p <;> decide

theorem bz_inj {p q : Bool} (h : bz p = bz q) : p = q := by
  revert h
  cases p <;> cases q <;> decide

theorem natcast_bz (c : ℕ) : ((c : ℕ) : ZMod 2) = bz (decide (Odd c)) := by
  induction c with
  | zero =>
    have h0 : ¬ Odd 0 := by decide
    rw [Nat.cast_zero, decide_eq_false h0]
    decide
  | succ c ih =>
    rw [Nat.cast_succ, ih]
    by_cases h : Odd c
    · have h' : ¬ Odd (c + 1) := by rw [Nat.odd_add_one]; exact not_not.2 h
      rw [decide_eq_true h, decide_eq_false h']
      decide
    · have h' : Odd (c + 1) := by rw [Nat.odd_add_one]; exact h
      rw [decide_eq_false h, decide_eq_true h']
      decide

-- Gates allowed by the statement, and the count of binary gates.
def Good (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
    (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
      g.op.eval [true,false] ^^ g.op.eval [true,true]) = false)

def cost (gs : List Gate) : ℕ := gs.countP (fun g => decide (g.inputs.length = 2))

theorem good_nil : Good [] := by
  intro g hg
  simp at hg

theorem good_append {a b : List Gate} (ha : Good a) (hb : Good b) : Good (a ++ b) := by
  intro g hg
  rcases List.mem_append.1 hg with h | h
  · exact ha g h
  · exact hb g h

theorem cost_append (a b : List Gate) : cost (a ++ b) = cost a + cost b := by
  simp [cost, List.countP_append]

-- Wires of a gate list.
theorem wires_nil (x : List Bool) : (Circuit.mk [] 0).wires x = x := rfl

theorem wires_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    (Circuit.mk (g :: gs) 0).wires x =
      (Circuit.mk gs 0).wires (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) := rfl

theorem wires_append (gs gs' : List Gate) (x : List Bool) :
    (Circuit.mk (gs ++ gs') 0).wires x =
      (Circuit.mk gs' 0).wires ((Circuit.mk gs 0).wires x) := by
  simp only [Circuit.wires, List.foldl_append]

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (gs ++ [g]) 0).wires x = (Circuit.mk gs 0).wires x ++
      [g.op.eval (g.inputs.map fun i => ((Circuit.mk gs 0).wires x).getD i false)] := by
  rw [wires_append]
  rfl

theorem wires_length (gs : List Gate) : ∀ (x : List Bool),
    ((Circuit.mk gs 0).wires x).length = x.length + gs.length := by
  induction gs with
  | nil => intro x; rfl
  | cons g gs ih =>
    intro x
    rw [wires_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem wires_ext (gs : List Gate) : ∀ (x : List Bool),
    ∃ t, (Circuit.mk gs 0).wires x = x ++ t := by
  induction gs with
  | nil => intro x; exact ⟨[], by rw [wires_nil, List.append_nil]⟩
  | cons g gs ih =>
    intro x
    obtain ⟨t, ht⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => x.getD i false) :: t, ?_⟩
    rw [wires_cons, ht]
    simp

theorem getD_app (l t : List Bool) (w : ℕ) (h : w < l.length) :
    (l ++ t).getD w false = l.getD w false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_len (l : List Bool) (v : Bool) (w : ℕ) (h : l.length = w) :
    (l ++ [v]).getD w false = v := by
  subst h
  rw [List.getD_eq_getElem?_getD, List.getElem?_concat_length, Option.getD_some]

theorem getD_len2 (l : List Bool) (v1 v2 : Bool) (w : ℕ) (h : l.length + 1 = w) :
    ((l ++ [v1]) ++ [v2]).getD w false = v2 := by
  apply getD_len
  rw [List.length_append, List.length_singleton]
  exact h

theorem not_eval (p : Bool) : GateOp.eval GateOp.not [p] = !p := rfl

theorem mod2_not (p q : Bool) :
    GateOp.eval GateOp.not [GateOp.eval (GateOp.mod 2) [p, q]] = (p ^^ q) := by
  cases p <;> cases q <;> decide

theorem mod2_affine : (GateOp.eval (GateOp.mod 2) [false,false] ^^ GateOp.eval (GateOp.mod 2) [false,true] ^^
    GateOp.eval (GateOp.mod 2) [true,false] ^^ GateOp.eval (GateOp.mod 2) [true,true]) = false := by
  decide

-- A wire carrying v on every one-hot input.
def Avail (n : ℕ) (gs : List Gate) (v : Fin n → ZMod 2) : Prop :=
  ∃ w, w < n + gs.length ∧ ∀ i : Fin n,
    bz (((Circuit.mk gs 0).wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false) = v i

theorem avail_congr {n : ℕ} {gs : List Gate} {v v' : Fin n → ZMod 2} (h : Avail n gs v)
    (e : ∀ i, v i = v' i) : Avail n gs v' := by
  obtain ⟨w, hw, hv⟩ := h
  exact ⟨w, hw, fun i => (hv i).trans (e i)⟩

theorem avail_mono {n : ℕ} {gs : List Gate} {v : Fin n → ZMod 2} (h : Avail n gs v)
    (gs' : List Gate) : Avail n (gs ++ gs') v := by
  obtain ⟨w, hw, hv⟩ := h
  refine ⟨w, ?_, fun i => ?_⟩
  · rw [List.length_append]
    omega
  · obtain ⟨t, ht⟩ := wires_ext gs'
      ((Circuit.mk gs 0).wires (List.ofFn (fun h : Fin n => decide (h = i))))
    rw [wires_append, ht, getD_app]
    · exact hv i
    · rw [wires_length, List.length_ofFn]
      exact hw

theorem avail_input {n : ℕ} (gs : List Gate) (i0 : Fin n) :
    Avail n gs (fun i => if i = i0 then 1 else 0) := by
  have hi0 := i0.isLt
  refine ⟨i0.val, by omega, fun i => ?_⟩
  show bz _ = if i = i0 then 1 else 0
  obtain ⟨t, ht⟩ := wires_ext gs (List.ofFn (fun h : Fin n => decide (h = i)))
  rw [ht, getD_app _ _ _ (by rw [List.length_ofFn]; exact hi0)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hi0]
  by_cases hi : i = i0
  · subst hi
    simp [bz]
  · simp [bz, hi, Ne.symm hi]

def xg (a b c : ℕ) : List Gate := [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [c]⟩]

theorem good_xg (a b c : ℕ) : Good (xg a b c) := by
  intro g hg
  simp [xg] at hg
  rcases hg with rfl | rfl
  · exact ⟨by simp, fun _ => mod2_affine⟩
  · exact ⟨by simp, fun h => by simp at h⟩

theorem cost_xg (a b c : ℕ) : cost (xg a b c) = 1 := by
  simp [cost, xg]

theorem wires_xg {n : ℕ} (gs : List Gate) (a b : ℕ) (x : List Bool) (hx : x.length = n) :
    ((Circuit.mk (gs ++ xg a b (n + gs.length)) 0).wires x).getD (n + gs.length + 1) false =
      (((Circuit.mk gs 0).wires x).getD a false ^^ ((Circuit.mk gs 0).wires x).getD b false) := by
  have e : gs ++ xg a b (n + gs.length) =
      (gs ++ [⟨GateOp.mod 2, [a, b]⟩]) ++ [⟨GateOp.not, [n + gs.length]⟩] := by
    simp [xg]
  have hW : ((Circuit.mk gs 0).wires x).length = n + gs.length := by
    rw [wires_length, hx]
  rw [e, wires_snoc, wires_snoc]
  generalize (Circuit.mk gs 0).wires x = W at hW ⊢
  have h2 : W.length + 1 = n + gs.length + 1 := by omega
  rw [getD_len2 _ _ _ _ h2]
  simp only [List.map_cons, List.map_nil]
  rw [getD_len _ _ _ hW]
  exact mod2_not _ _

theorem avail_xor {n : ℕ} {gs : List Gate} {u v : Fin n → ZMod 2} (hu : Avail n gs u)
    (hv : Avail n gs v) :
    ∃ ext, Good ext ∧ cost ext ≤ 1 ∧ Avail n (gs ++ ext) (fun i => u i + v i) := by
  obtain ⟨a, ha, hu⟩ := hu
  obtain ⟨b, hb, hv⟩ := hv
  refine ⟨xg a b (n + gs.length), good_xg _ _ _, by rw [cost_xg], n + gs.length + 1, ?_,
    fun i => ?_⟩
  · simp only [xg, List.length_append, List.length_cons, List.length_nil]
    omega
  · show bz _ = u i + v i
    rw [wires_xg gs a b (List.ofFn (fun h : Fin n => decide (h = i))) List.length_ofFn,
      bz_xor, hu i, hv i]

theorem avail_not {n : ℕ} {gs : List Gate} {v : Fin n → ZMod 2} (hv : Avail n gs v) :
    ∃ ext, Good ext ∧ cost ext ≤ 0 ∧ Avail n (gs ++ ext) (fun i => v i + 1) := by
  obtain ⟨a, ha, hv⟩ := hv
  refine ⟨[⟨GateOp.not, [a]⟩], ?_, ?_, n + gs.length, ?_, fun i => ?_⟩
  · intro g hg
    rw [List.mem_singleton] at hg
    subst hg
    exact ⟨by simp, fun h => by simp at h⟩
  · simp [cost]
  · simp only [List.length_append, List.length_singleton]
    omega
  · show bz _ = v i + 1
    have hW : ((Circuit.mk gs 0).wires (List.ofFn (fun h : Fin n => decide (h = i)))).length =
        n + gs.length := by
      rw [wires_length, List.length_ofFn]
    rw [wires_snoc, getD_len _ _ _ hW]
    simp only [List.map_cons, List.map_nil]
    rw [not_eval, bz_not, hv i]

theorem avail_shift {n : ℕ} {gs : List Gate} {v : Fin n → ZMod 2} (b : Bool) (hv : Avail n gs v) :
    ∃ ext, Good ext ∧ cost ext ≤ 0 ∧ Avail n (gs ++ ext) (fun i => v i + bz b) := by
  cases b
  · refine ⟨[], good_nil, by simp [cost], ?_⟩
    rw [List.append_nil]
    exact avail_congr hv (fun i => by simp [bz])
  · obtain ⟨e, g, c, h⟩ := avail_not hv
    exact ⟨e, g, c, avail_congr h (fun i => by simp [bz])⟩

-- Several targets, one binary gate each.
theorem avail_many {n : ℕ} {β : Type} [DecidableEq β] (u : β → Fin n → ZMod 2) (gs : List Gate)
    (L : Finset β) :
    (∀ x ∈ L, ∀ e : List Gate, ∃ ext, Good ext ∧ cost ext ≤ 1 ∧ Avail n (gs ++ e ++ ext) (u x)) →
    ∃ ext, Good ext ∧ cost ext ≤ L.card ∧ ∀ x ∈ L, Avail n (gs ++ ext) (u x) := by
  refine Finset.induction_on L ?_ ?_
  · intro _
    exact ⟨[], good_nil, by simp [cost], fun x hx => by simp at hx⟩
  · intro a L' ha ih H
    obtain ⟨e1, g1, c1, h1⟩ := ih (fun x hx => H x (Finset.mem_insert_of_mem hx))
    obtain ⟨e2, g2, c2, h2⟩ := H a (Finset.mem_insert_self a L') e1
    refine ⟨e1 ++ e2, good_append g1 g2, ?_, ?_⟩
    · rw [cost_append, Finset.card_insert_of_notMem ha]
      omega
    · intro x hx
      rw [← List.append_assoc]
      rcases Finset.mem_insert.1 hx with h | h
      · rw [h]
        exact h2
      · exact avail_mono (h1 x h) e2

-- The XOR of a nonempty family of available wires.
theorem avail_sum {n : ℕ} {β : Type} [DecidableEq β] (u : β → Fin n → ZMod 2) (L : Finset β) :
    ∀ gs : List Gate, L.Nonempty → (∀ x ∈ L, Avail n gs (u x)) →
    ∃ ext, Good ext ∧ cost ext ≤ L.card - 1 ∧
      Avail n (gs ++ ext) (fun i => L.sum (fun x => u x i)) := by
  refine Finset.induction_on L ?_ ?_
  · intro gs h
    exact absurd h Finset.not_nonempty_empty
  · intro a L' ha ih gs _ hav
    by_cases hL' : L'.Nonempty
    · obtain ⟨e1, g1, c1, h1⟩ := ih gs hL' (fun x hx => hav x (Finset.mem_insert_of_mem hx))
      obtain ⟨e2, g2, c2, h2⟩ :=
        avail_xor (avail_mono (hav a (Finset.mem_insert_self a L')) e1) h1
      refine ⟨e1 ++ e2, good_append g1 g2, ?_, ?_⟩
      · rw [cost_append, Finset.card_insert_of_notMem ha]
        have := hL'.card_pos
        omega
      · rw [← List.append_assoc]
        exact avail_congr h2 (fun i => (Finset.sum_insert (f := fun x => u x i) ha).symm)
    · rw [Finset.not_nonempty_iff_eq_empty] at hL'
      subst hL'
      refine ⟨[], good_nil, by simp [cost], ?_⟩
      rw [List.append_nil]
      exact avail_congr (hav a (Finset.mem_insert_self a ∅)) (fun i => by simp)

-- Splitting a powerset sum at a new element.
theorem sum_split_a {k : ℕ} (a : Fin k) (J' : Finset (Fin k)) (ha : a ∉ J')
    (f : Finset (Fin k) → ZMod 2) :
    (insert a J').powerset.sum (fun R => if a ∈ R then f R else 0) =
      J'.powerset.sum (fun R => f (insert a R)) := by
  rw [Finset.sum_powerset_insert ha]
  have h0 : J'.powerset.sum (fun R => if a ∈ R then f R else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro R hR
    have : a ∉ R := fun h => ha (Finset.mem_powerset.1 hR h)
    simp [this]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro R _
  simp

theorem sum_split_j {k : ℕ} (a j : Fin k) (J' : Finset (Fin k)) (ha : a ∉ J') (hja : j ≠ a)
    (f : Finset (Fin k) → ZMod 2) :
    (insert a J').powerset.sum (fun R => if j ∈ R then f R else 0) =
      J'.powerset.sum (fun R => if j ∈ R then f R + f (insert a R) else 0) := by
  rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R _
  by_cases hjR : j ∈ R
  · simp [hjR]
  · simp [hjR, hja]

-- All subsets of J: each coordinate j gets the XOR of the inputs whose mask holds j.
theorem lemA {n k : ℕ} (J : Finset (Fin k)) :
    ∀ (z : Finset (Fin k) → Fin n → ZMod 2) (gs : List Gate),
    (∀ R ⊆ J, R.Nonempty → Avail n gs (z R)) →
    ∃ ext, Good ext ∧ cost ext ≤ 2 * (2 ^ J.card - 1 - J.card) ∧
      ∀ j ∈ J, Avail n (gs ++ ext)
        (fun i => J.powerset.sum (fun R => if j ∈ R then z R i else 0)) := by
  refine Finset.induction_on J ?_ ?_
  · intro z gs _
    exact ⟨[], good_nil, by simp [cost], fun j hj => by simp at hj⟩
  · intro a J' ha ih z gs hz
    obtain ⟨e1, g1, c1, h1⟩ := avail_many (fun R => fun i => z R i + z (insert a R) i) gs
      (J'.powerset.erase ∅) (by
        intro R hR e
        have hR' := Finset.mem_erase.1 hR
        have hsub : R ⊆ J' := Finset.mem_powerset.1 hR'.2
        have hne : R.Nonempty := Finset.nonempty_iff_ne_empty.2 hR'.1
        exact avail_xor
          (avail_mono (hz R (Finset.Subset.trans hsub (Finset.subset_insert a J')) hne) e)
          (avail_mono (hz (insert a R) (Finset.insert_subset_insert a hsub)
            (Finset.insert_nonempty a R)) e))
    obtain ⟨e2, g2, c2, h2⟩ := avail_sum (fun R => z (insert a R)) J'.powerset (gs ++ e1)
      ⟨∅, Finset.empty_mem_powerset J'⟩
      (fun R hR => avail_mono (hz (insert a R)
        (Finset.insert_subset_insert a (Finset.mem_powerset.1 hR))
        (Finset.insert_nonempty a R)) e1)
    obtain ⟨e3, g3, c3, h3⟩ := ih (fun R => fun i => z R i + z (insert a R) i) (gs ++ e1 ++ e2)
      (by
        intro R hR hne
        exact avail_mono (h1 R (Finset.mem_erase.2
          ⟨Finset.nonempty_iff_ne_empty.1 hne, Finset.mem_powerset.2 hR⟩)) e2)
    refine ⟨e1 ++ e2 ++ e3, good_append (good_append g1 g2) g3, ?_, ?_⟩
    · rw [cost_append, cost_append, Finset.card_insert_of_notMem ha]
      rw [Finset.card_erase_of_mem (Finset.empty_mem_powerset J'), Finset.card_powerset] at c1
      rw [Finset.card_powerset] at c2
      have hp : J'.card < 2 ^ J'.card := Nat.lt_two_pow_self
      rw [pow_succ]
      omega
    · intro j hj
      have hassoc : gs ++ (e1 ++ e2 ++ e3) = gs ++ e1 ++ e2 ++ e3 := by
        simp only [List.append_assoc]
      rw [hassoc]
      by_cases hja : j = a
      · rw [hja]
        exact avail_congr (avail_mono h2 e3)
          (fun i => (sum_split_a a J' ha (fun R => z R i)).symm)
      · have hj' : j ∈ J' := by
          rcases Finset.mem_insert.1 hj with h | h
          · exact absurd h hja
          · exact h
        exact avail_congr (h3 j hj')
          (fun i => (sum_split_j a j J' ha hja (fun R => z R i)).symm)

-- The even centred names: a subset R of the other coordinates, with o added to fix the parity.
def cen {k : ℕ} (o : Fin k) (b : Bool) (R : Finset (Fin k)) : Finset (Fin k) :=
  if decide (Odd R.card) = b then R else insert o R

theorem cen_erase {k : ℕ} (o : Fin k) (b : Bool) (R : Finset (Fin k)) (hR : o ∉ R) :
    (cen o b R).erase o = R := by
  unfold cen
  split_ifs
  · exact Finset.erase_eq_of_notMem hR
  · exact Finset.erase_insert hR

theorem cen_parity {k : ℕ} (o : Fin k) (b : Bool) (R : Finset (Fin k)) (hR : o ∉ R) :
    decide (Odd (cen o b R).card) = b := by
  unfold cen
  split_ifs with h
  · exact h
  · rw [Finset.card_insert_of_notMem hR]
    revert h
    by_cases hc : Odd R.card
    · have h' : ¬ Odd (R.card + 1) := by rw [Nat.odd_add_one]; exact not_not.2 hc
      rw [decide_eq_true hc, decide_eq_false h']
      cases b <;> decide
    · have h' : Odd (R.card + 1) := by rw [Nat.odd_add_one]; exact hc
      rw [decide_eq_false hc, decide_eq_true h']
      cases b <;> decide

theorem cen_eq_iff {k : ℕ} (o : Fin k) (b : Bool) (S R : Finset (Fin k))
    (hS : decide (Odd S.card) = b) (hR : o ∉ R) :
    S = cen o b R ↔ R = S.erase o := by
  constructor
  · intro h
    rw [h, cen_erase o b R hR]
  · intro h
    subst h
    unfold cen
    by_cases ho : o ∈ S
    · have hc : (S.erase o).card + 1 = S.card := Finset.card_erase_add_one ho
      have hne : ¬ (decide (Odd (S.erase o).card) = b) := by
        rw [← hS, ← hc]
        by_cases h' : Odd (S.erase o).card
        · have h'' : ¬ Odd ((S.erase o).card + 1) := by
            rw [Nat.odd_add_one]; exact not_not.2 h'
          rw [decide_eq_true h', decide_eq_false h'']
          decide
        · have h'' : Odd ((S.erase o).card + 1) := by
            rw [Nat.odd_add_one]; exact h'
          rw [decide_eq_false h', decide_eq_true h'']
          decide
      rw [if_neg hne, Finset.insert_erase ho]
    · rw [Finset.erase_eq_of_notMem ho, if_pos hS]

def zf {n k : ℕ} (F : Fin n → Finset (Fin k)) (o : Fin k) (b : Bool) (R : Finset (Fin k))
    (i : Fin n) : ZMod 2 :=
  if F i = cen o b R then 1 else 0

theorem key6 {k n : ℕ} (o : Fin k) (b : Bool) (F : Fin n → Finset (Fin k))
    (hpar : ∀ i, decide (Odd (F i).card) = b) (j : Fin k) (hj : j ≠ o) (i : Fin n) :
    (Finset.univ.erase o).powerset.sum (fun R => if j ∈ R then zf F o b R i else 0) =
      if j ∈ F i then 1 else 0 := by
  have hR0 : (F i).erase o ∈ (Finset.univ.erase o).powerset :=
    Finset.mem_powerset.2 (Finset.erase_subset_erase o (Finset.subset_univ _))
  rw [Finset.sum_eq_single_of_mem ((F i).erase o) hR0]
  · have hc : F i = cen o b ((F i).erase o) :=
      (cen_eq_iff o b (F i) ((F i).erase o) (hpar i) (Finset.notMem_erase o _)).2 rfl
    show (if j ∈ (F i).erase o then (if F i = cen o b ((F i).erase o) then (1 : ZMod 2) else 0)
      else 0) = if j ∈ F i then 1 else 0
    rw [if_pos hc]
    by_cases hjF : j ∈ F i
    · rw [if_pos (Finset.mem_erase.2 ⟨hj, hjF⟩), if_pos hjF]
    · rw [if_neg (fun h => hjF (Finset.mem_of_mem_erase h)), if_neg hjF]
  · intro R hR hne
    have hRo : o ∉ R := fun h => Finset.notMem_erase o _ (Finset.mem_powerset.1 hR h)
    have hc : ¬ F i = cen o b R := fun h => hne ((cen_eq_iff o b (F i) R (hpar i) hRo).1 h)
    show (if j ∈ R then (if F i = cen o b R then (1 : ZMod 2) else 0) else 0) = 0
    rw [if_neg hc, ite_self]

theorem last_bit {k : ℕ} (o : Fin k) (b : Bool) (S : Finset (Fin k))
    (hS : decide (Odd S.card) = b) :
    (Finset.univ.erase o).sum (fun j => if j ∈ S then (1 : ZMod 2) else 0) + bz b =
      if o ∈ S then 1 else 0 := by
  have hf : (Finset.univ.erase o).filter (fun j => j ∈ S) = S.erase o := by
    ext x
    simp [Finset.mem_filter, Finset.mem_erase]
  rw [Finset.sum_boole, hf, natcast_bz, ← hS]
  by_cases ho : o ∈ S
  · rw [if_pos ho, ← Finset.card_erase_add_one ho]
    generalize (S.erase o).card = c
    by_cases h : Odd c
    · have h' : ¬ Odd (c + 1) := by rw [Nat.odd_add_one]; exact not_not.2 h
      rw [decide_eq_true h, decide_eq_false h']
      decide
    · have h' : Odd (c + 1) := by rw [Nat.odd_add_one]; exact h
      rw [decide_eq_false h, decide_eq_true h']
      decide
  · rw [if_neg ho, Finset.erase_eq_of_notMem ho]
    generalize decide (Odd S.card) = x
    cases x <;> decide

theorem build (k n : ℕ) (o : Fin k) (b : Bool) (F : Fin n → Finset (Fin k))
    (hF : Function.Injective F)
    (hS : ∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b)
    (hJ : (Finset.univ.erase o).Nonempty) :
    ∃ gs, Good gs ∧
      cost gs ≤ 2 * (2 ^ (Finset.univ.erase o).card - 1 - (Finset.univ.erase o).card) +
        ((Finset.univ.erase o).card - 1) ∧
      ∀ j : Fin k, Avail n gs (fun i => if j ∈ F i then 1 else 0) := by
  have hRo : ∀ R ∈ (Finset.univ.erase o).powerset, o ∉ R :=
    fun R hR h => Finset.notMem_erase o _ (Finset.mem_powerset.1 hR h)
  have hpar : ∀ i, decide (Odd (F i).card) = b := fun i => (hS (F i)).1 ⟨i, rfl⟩
  have hex : ∀ R ∈ (Finset.univ.erase o).powerset, ∃ i0, F i0 = cen o b R :=
    fun R hR => (hS _).2 (cen_parity o b R (hRo R hR))
  have hz : ∀ R ⊆ Finset.univ.erase o, R.Nonempty → Avail n [] (zf F o b R) := by
    intro R hR _
    obtain ⟨i0, hi0⟩ := hex R (Finset.mem_powerset.2 hR)
    refine avail_congr (avail_input [] i0) (fun i => ?_)
    show (if i = i0 then (1 : ZMod 2) else 0) = if F i = cen o b R then 1 else 0
    rw [← hi0]
    by_cases h : i = i0
    · rw [if_pos h, if_pos (congrArg F h)]
    · rw [if_neg h, if_neg (fun h' => h (hF h'))]
  obtain ⟨e1, g1, c1, h1⟩ := lemA (Finset.univ.erase o) (zf F o b) [] hz
  have h1' : ∀ j ∈ Finset.univ.erase o, Avail n e1 (fun i => if j ∈ F i then 1 else 0) := by
    intro j hj
    have h := h1 j hj
    rw [List.nil_append] at h
    exact avail_congr h (fun i => key6 o b F hpar j (Finset.mem_erase.1 hj).1 i)
  obtain ⟨e2, g2, c2, h2⟩ := avail_sum (fun j i => if j ∈ F i then (1 : ZMod 2) else 0)
    (Finset.univ.erase o) e1 hJ h1'
  obtain ⟨e3, g3, c3, h3⟩ := avail_shift b h2
  refine ⟨e1 ++ e2 ++ e3, good_append (good_append g1 g2) g3, ?_, ?_⟩
  · rw [cost_append, cost_append]
    omega
  · intro j
    by_cases hj : j = o
    · rw [hj]
      exact avail_congr h3 (fun i => last_bit o b (F i) (hpar i))
    · have hj' : j ∈ Finset.univ.erase o := Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩
      have h := avail_mono (h1' j hj') (e2 ++ e3)
      rw [← List.append_assoc] at h
      exact h

theorem pow_le_n (k n : ℕ) (o : Fin k) (b : Bool) (F : Fin n → Finset (Fin k))
    (hS : ∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) :
    2 ^ (Finset.univ.erase o).card ≤ n := by
  have hRo : ∀ R ∈ (Finset.univ.erase o).powerset, o ∉ R :=
    fun R hR h => Finset.notMem_erase o _ (Finset.mem_powerset.1 hR h)
  have hex : ∀ R ∈ (Finset.univ.erase o).powerset, ∃ i0, F i0 = cen o b R :=
    fun R hR => (hS _).2 (cen_parity o b R (hRo R hR))
  obtain ⟨i₀, -⟩ := hex ∅ (Finset.empty_mem_powerset _)
  have : Nonempty (Fin n) := ⟨i₀⟩
  have h : (Finset.univ.erase o).powerset.card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card_of_injOn (fun R => Function.invFun F (cen o b R))
      (by
        intro R _
        exact Finset.mem_coe.2 (Finset.mem_univ _))
      (by
        intro R1 hR1 R2 hR2 heq
        have m1 : R1 ∈ (Finset.univ.erase o).powerset := Finset.mem_coe.1 hR1
        have m2 : R2 ∈ (Finset.univ.erase o).powerset := Finset.mem_coe.1 hR2
        have e1 := Function.invFun_eq (hex R1 m1)
        have e2 := Function.invFun_eq (hex R2 m2)
        have heq' : Function.invFun F (cen o b R1) = Function.invFun F (cen o b R2) := heq
        have hc : cen o b R1 = cen o b R2 := by
          have h3 := congrArg F heq'
          rw [e1, e2] at h3
          exact h3
        rw [← cen_erase o b R1 (hRo R1 m1), ← cen_erase o b R2 (hRo R2 m2), hc])
  rw [Finset.card_powerset, Finset.card_fin] at h
  exact h

theorem avail_out {n : ℕ} {gs : List Gate} {P : Fin n → Prop} [DecidablePred P]
    (h : Avail n gs (fun i => if P i then 1 else 0)) :
    ∃ w : ℕ, ∀ i : Fin n,
      ((Circuit.mk gs 0).wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false =
        decide (P i) := by
  obtain ⟨w, _, hv⟩ := h
  refine ⟨w, fun i => bz_inj ?_⟩
  rw [hv i]
  by_cases hp : P i
  · simp [bz, hp]
  · simp [bz, hp]

theorem upper_bound : ∀ (k n : ℕ), 2 ≤ k → ∀ (b : Bool) (F : Fin n → Finset (Fin k)),
    Function.Injective F → (∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) →
    ∀ s : ℕ, 2*n ≤ s + k + 2 →
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
        (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
          g.op.eval [true,false] ^^ g.op.eval [true,true]) = false)) ∧
      C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ s ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false =
          decide (j ∈ F i)) := by
  intro k n hk b F hF hS s hs
  have hk0 : 0 < k := by omega
  have hk1 : 1 < k := by omega
  have hJ : (Finset.univ.erase (⟨0, hk0⟩ : Fin k)).Nonempty :=
    ⟨⟨1, hk1⟩, Finset.mem_erase.2 ⟨fun h => by simp [Fin.ext_iff] at h, Finset.mem_univ _⟩⟩
  obtain ⟨gs, hg, hc, hav⟩ := build k n ⟨0, hk0⟩ b F hF hS hJ
  have hp := pow_le_n k n ⟨0, hk0⟩ b F hS
  have hcard : (Finset.univ.erase (⟨0, hk0⟩ : Fin k)).card = k - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
  rw [hcard] at hc hp
  have hlt : k - 1 < 2 ^ (k - 1) := Nat.lt_two_pow_self
  refine ⟨⟨gs, 0⟩, hg, ?_, fun j => avail_out (hav j)⟩
  show cost gs ≤ s
  omega

-- The posted statement from a lower bound in the same shape.
theorem iff_of_lower (hlow : ∀ (k n : ℕ), 2 ≤ k → ∀ (b : Bool) (F : Fin n → Finset (Fin k)),
    Function.Injective F → (∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) →
    ∀ s : ℕ,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
        (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
          g.op.eval [true,false] ^^ g.op.eval [true,true]) = false)) ∧
      C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ s ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) →
    2*n ≤ s + k + 2) :
    ∀ (k n : ℕ), 2 ≤ k → ∀ (b : Bool) (F : Fin n → Finset (Fin k)),
  Function.Injective F → (∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) →
  ∀ s : ℕ,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
        (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
          g.op.eval [true,false] ^^ g.op.eval [true,true]) = false)) ∧
      C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ s ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) ↔
    2*n ≤ s + k + 2 :=
  fun k n hk b F hF hS s => ⟨hlow k n hk b F hF hS s, upper_bound k n hk b F hF hS s⟩


end PEqualNP.Outside.L_meta_27802_aux

theorem PEqualNP.Outside.L_meta_27802 : ∀ (k n : ℕ), 2 ≤ k → ∀ (b : Bool) (F : Fin n → Finset (Fin k)),
  Function.Injective F → (∀ S : Finset (Fin k), (∃ i, F i = S) ↔ decide (Odd S.card) = b) →
  ∀ s : ℕ,
    (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧ (g.inputs.length = 2 →
        (g.op.eval [false,false] ^^ g.op.eval [false,true] ^^
          g.op.eval [true,false] ^^ g.op.eval [true,true]) = false)) ∧
      C.gates.countP (fun g => decide (g.inputs.length = 2)) ≤ s ∧
      ∀ j : Fin k, ∃ w : ℕ, ∀ i : Fin n,
        (C.wires (List.ofFn (fun h : Fin n => decide (h = i)))).getD w false = decide (j ∈ F i)) ↔
    2*n ≤ s + k + 2 :=
  PEqualNP.Outside.L_meta_27802_aux.iff_of_lower PEqualNP.Outside.L_meta_27802_aux.lower_dir
